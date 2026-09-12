//! Threaded, networked habi_core node. Thin I/O wrapper: all actual
//! protocol/safety logic lives in shared_state.rs and
//! peer_protocol.rs (fully unit-tested there, without sockets). This
//! binary only does socket read/write and thread spawning, calling
//! straight into those already-proven functions.
//!
//! Usage:
//!   habi_node <node_id> <peer_listen_addr> <admin_listen_addr> \
//!             <peers_file> [state_file]
//!
//! peers_file format, one per line: NODE_ID|HOST:PORT
//! (the peer-listener address of every node in the network,
//! including this one -- this node's own entry is ignored).

use habi_core::conversion_day_coordinator::{compute_conversion_day, PeerSnapshot};
use habi_core::peer_protocol::{apply_link_up_reply, apply_propagate_reply, handle_incoming_peer_message};
use habi_core::persistence::{load_node_state, save_node_state};
use habi_core::shared_state::{NodeShared, SharedState};
use habi_core::wire::{AdminMessage, AdminReply, PeerMessage};
use std::collections::HashMap;
use std::env;
use std::fs;
use std::io::{BufRead, BufReader, Write};
use std::net::{TcpListener, TcpStream};
use std::path::PathBuf;
use std::sync::{Arc, Mutex};
use std::thread;

type PeerAddrs = Arc<Mutex<HashMap<String, String>>>;

fn parse_peers_file(path: &str, self_id: &str) -> HashMap<String, String> {
    let mut map = HashMap::new();
    let content = fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("cannot read peers file {path}: {e}"));
    for line in content.lines() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        let mut parts = line.splitn(2, '|');
        let id = parts.next().unwrap_or("").trim();
        let addr = parts.next().unwrap_or("").trim();
        if id.is_empty() || addr.is_empty() {
            eprintln!("[warn] skipping malformed peers file line: {line:?}");
            continue;
        }
        if id == self_id {
            continue;
        }
        map.insert(id.to_string(), addr.to_string());
    }
    map
}

fn read_one_line(stream: &TcpStream) -> std::io::Result<String> {
    let mut reader = BufReader::new(stream);
    let mut line = String::new();
    reader.read_line(&mut line)?;
    Ok(line)
}

fn write_line(mut stream: &TcpStream, s: &str) -> std::io::Result<()> {
    stream.write_all(s.as_bytes())?;
    stream.write_all(b"\n")?;
    stream.flush()
}

/// Connect to a peer, send one message, read exactly one reply line.
fn exchange_with_peer(addr: &str, msg: &PeerMessage) -> Result<PeerMessage, String> {
    let stream = TcpStream::connect(addr).map_err(|e| format!("connect to {addr} failed: {e}"))?;
    write_line(&stream, &msg.encode()).map_err(|e| format!("send to {addr} failed: {e}"))?;
    let line = read_one_line(&stream).map_err(|e| format!("read from {addr} failed: {e}"))?;
    if line.trim().is_empty() {
        return Err(format!("peer {addr} closed connection without replying"));
    }
    PeerMessage::decode(&line).map_err(|e| format!("bad reply from {addr}: {e}"))
}

/// Connect to a peer, send one message, do not wait for a reply.
fn send_to_peer_no_reply(addr: &str, msg: &PeerMessage) -> Result<(), String> {
    let stream = TcpStream::connect(addr).map_err(|e| format!("connect to {addr} failed: {e}"))?;
    write_line(&stream, &msg.encode()).map_err(|e| format!("send to {addr} failed: {e}"))
}

fn persist(shared: &SharedState, state_path: &Option<PathBuf>) {
    if let Some(path) = state_path {
        let guard = shared.lock().unwrap();
        if let Err(e) = save_node_state(&guard.node, path) {
            eprintln!("[warn] failed to persist state to {path:?}: {e}");
        }
    }
}

fn handle_peer_connection(stream: TcpStream, shared: SharedState) {
    let line = match read_one_line(&stream) {
        Ok(l) if !l.trim().is_empty() => l,
        Ok(_) => return, // empty line / connection closed immediately
        Err(e) => {
            eprintln!("[warn] peer connection read error: {e}");
            return;
        }
    };
    let msg = match PeerMessage::decode(&line) {
        Ok(m) => m,
        Err(e) => {
            eprintln!("[warn] malformed peer message: {e}");
            return;
        }
    };
    match handle_incoming_peer_message(&shared, msg) {
        Ok(Some(reply)) => {
            if let Err(e) = write_line(&stream, &reply.encode()) {
                eprintln!("[warn] failed to write peer reply: {e}");
            }
        }
        Ok(None) => {} // no reply expected (LinkDown, SpentNotify)
        Err(e) => {
            eprintln!("[warn] error handling peer message: {e}");
        }
    }
}

fn run_peer_listener(bind_addr: String, shared: SharedState) {
    let listener = TcpListener::bind(&bind_addr)
        .unwrap_or_else(|e| panic!("cannot bind peer listener on {bind_addr}: {e}"));
    println!("[peer] listening on {bind_addr}");
    for incoming in listener.incoming() {
        match incoming {
            Ok(stream) => {
                let shared = Arc::clone(&shared);
                thread::spawn(move || handle_peer_connection(stream, shared));
            }
            Err(e) => eprintln!("[warn] peer accept error: {e}"),
        }
    }
}

fn handle_admin_command(
    shared: &SharedState,
    peers: &PeerAddrs,
    state_path: &Option<PathBuf>,
    msg: AdminMessage,
) -> AdminReply {
    match msg {
        AdminMessage::LinkUp { peer } => {
            let addr = match peers.lock().unwrap().get(&peer).cloned() {
                Some(a) => a,
                None => return AdminReply::Error { detail: format!("unknown peer {peer}") },
            };

            let (self_id, own_ledger, own_spent) = {
                let g = shared.lock().unwrap();
                (g.node.node_id.clone(), g.ledger_sorted(), g.spent_sorted())
            };
            let hello = PeerMessage::LinkUpHello {
                from: self_id,
                ledger: own_ledger,
                spent: own_spent,
            };

            match exchange_with_peer(&addr, &hello) {
                Ok(ack @ PeerMessage::LinkUpAck { .. }) => {
                    match apply_link_up_reply(shared, ack) {
                        Ok(()) => {
                            persist(shared, state_path);
                            AdminReply::Ok
                        }
                        Err(e) => AdminReply::Error { detail: e.to_string() },
                    }
                }
                Ok(other) => AdminReply::Error {
                    detail: format!("unexpected reply from {peer}: {other:?}"),
                },
                Err(e) => AdminReply::Error { detail: e },
            }
        }

        AdminMessage::LinkDown { peer } => {
            let addr = match peers.lock().unwrap().get(&peer).cloned() {
                Some(a) => a,
                None => return AdminReply::Error { detail: format!("unknown peer {peer}") },
            };
            let self_id = shared.lock().unwrap().node.node_id.clone();
            let notify = PeerMessage::LinkDown { from: self_id };
            if let Err(e) = send_to_peer_no_reply(&addr, &notify) {
                return AdminReply::Error { detail: e };
            }
            shared.lock().unwrap().apply_link_down(&peer);
            persist(shared, state_path);
            AdminReply::Ok
        }

        AdminMessage::Propagate { peer } => {
            let addr = match peers.lock().unwrap().get(&peer).cloned() {
                Some(a) => a,
                None => return AdminReply::Error { detail: format!("unknown peer {peer}") },
            };
            let self_id = {
                let g = shared.lock().unwrap();
                // FIX: mirror network.rs::propagate's network[src][dst]
                // precondition on the requester's side too, not just
                // the peer handler's side -- fail fast locally instead
                // of making a doomed network round trip.
                if !g.is_linked(&peer) {
                    return AdminReply::Error {
                        detail: format!("no link to {peer}, cannot propagate"),
                    };
                }
                g.node.node_id.clone()
            };
            let req = PeerMessage::PropagateRequest { from: self_id };
            match exchange_with_peer(&addr, &req) {
                Ok(reply @ PeerMessage::PropagateReply { .. }) => {
                    match apply_propagate_reply(shared, reply) {
                        Ok(()) => {
                            persist(shared, state_path);
                            AdminReply::Ok
                        }
                        Err(e) => AdminReply::Error { detail: e.to_string() },
                    }
                }
                Ok(other) => AdminReply::Error {
                    detail: format!("unexpected reply from {peer}: {other:?}"),
                },
                Err(e) => AdminReply::Error { detail: e },
            }
        }

        AdminMessage::SpendAt { bearer } => {
            let (self_id, connected) = {
                let mut g = shared.lock().unwrap();
                if let Err(e) = g.local_spend(&bearer) {
                    return AdminReply::Error { detail: e.to_string() };
                }
                (g.node.node_id.clone(), g.connected_peers())
            };
            persist(shared, state_path);

            // Broadcast to every currently-connected peer, mirroring
            // network.rs::spend_at's connected_to(nn) broadcast.
            // Best-effort: a peer that's unreachable right now will
            // simply learn of the spend later via LinkUp/Propagate,
            // same as the centralized model's direct-link-only design.
            let peer_addrs = peers.lock().unwrap();
            for peer_id in &connected {
                if let Some(addr) = peer_addrs.get(peer_id) {
                    let notify = PeerMessage::SpentNotify {
                        from: self_id.clone(),
                        bearer: bearer.clone(),
                    };
                    if let Err(e) = send_to_peer_no_reply(addr, &notify) {
                        eprintln!("[warn] failed to notify {peer_id} of spend: {e}");
                    }
                }
            }
            AdminReply::Ok
        }

        AdminMessage::ConversionDay => {
            // 1. Gather our own snapshot plus every reachable peer's,
            //    via StatusRequest -- bypasses the pairwise-link
            //    requirement, matching conversion_day.rs's
            //    "designated reconciliation authority" model.
            // FIX: the original version called shared.lock().unwrap()
            // three times within one statement (building the
            // PeerSnapshot inline). Rust keeps every temporary --
            // including each MutexGuard -- alive until the END of the
            // enclosing statement, not the end of each sub-expression,
            // so all three guards were held simultaneously against a
            // non-reentrant Mutex: a genuine self-deadlock, silent
            // (no panic, no output), reproduced and confirmed via a
            // real hung `conversion-day` admin call. Fix: take the
            // lock exactly once, in its own scope, extract everything
            // needed, then let the guard drop before building the
            // PeerSnapshot.
            let (self_id, self_ledger, self_spent) = {
                let g = shared.lock().unwrap();
                (g.node.node_id.clone(), g.node.ledger.clone(), g.node.spent.clone())
            };
            let mut snapshots = vec![PeerSnapshot {
                node_id: self_id.clone(),
                ledger: self_ledger,
                spent: self_spent,
            }];

            let peer_addrs: Vec<(String, String)> = {
                let g = peers.lock().unwrap();
                g.iter().map(|(k, v)| (k.clone(), v.clone())).collect()
            };

            let self_req = PeerMessage::StatusRequest { from: self_id.clone() };
            for (peer_id, addr) in &peer_addrs {
                match exchange_with_peer(addr, &self_req) {
                    Ok(PeerMessage::StatusReply { ledger, spent, .. }) => {
                        snapshots.push(PeerSnapshot {
                            node_id: peer_id.clone(),
                            ledger: ledger.into_iter().collect(),
                            spent: spent.into_iter().collect(),
                        });
                    }
                    Ok(other) => {
                        eprintln!("[warn] unexpected reply from {peer_id} during ConversionDay: {other:?}");
                    }
                    Err(e) => {
                        // Best-effort, matching conversion_day.rs's
                        // "participants defaults to all reachable" --
                        // an unreachable peer is simply excluded from
                        // this round, not a hard failure.
                        eprintln!("[warn] {peer_id} unreachable during ConversionDay: {e}");
                    }
                }
            }

            // 2. Compute the burn set, or detect a real conflict.
            let burn_set = match compute_conversion_day(&snapshots) {
                Ok(set) => set,
                Err(conflict) => {
                    return AdminReply::Error { detail: conflict.to_string() };
                }
            };

            // 3. Apply the burn locally, then broadcast SpentNotify
            //    to every peer that responded (best-effort, same
            //    reachability caveat as step 1).
            {
                let mut g = shared.lock().unwrap();
                for b in &burn_set {
                    g.apply_spent_notify(b);
                }
            }
            persist(shared, state_path);

            for (peer_id, addr) in &peer_addrs {
                for b in &burn_set {
                    let notify = PeerMessage::SpentNotify {
                        from: self_id.clone(),
                        bearer: b.clone(),
                    };
                    if let Err(e) = send_to_peer_no_reply(addr, &notify) {
                        eprintln!("[warn] failed to broadcast burn of {b} to {peer_id}: {e}");
                    }
                }
            }

            AdminReply::Ok
        }

        AdminMessage::Status => {
            let g = shared.lock().unwrap();
            AdminReply::StatusReport {
                node_id: g.node.node_id.clone(),
                ledger: g.ledger_sorted(),
                spent: g.spent_sorted(),
                links: g.connected_peers(),
            }
        }

        // TEST/BOOTSTRAP ONLY -- see AdminMessage::Seed doc comment
        // in wire.rs. No provenance check, no broadcast to peers:
        // this is purely local ledger insertion for smoke-testing,
        // not a real economic action.
        AdminMessage::Seed { bearer } => {
            let node_id = {
                let mut g = shared.lock().unwrap();
                g.node.ledger.insert(bearer.clone());
                g.node.node_id.clone()
            };
            eprintln!(
                "[WARN] {node_id}: ADMIN_SEED invoked for bearer {bearer:?} -- \
                 test/bootstrap-only operation, no provenance check, not a real \
                 economic action. See README.md."
            );
            persist(shared, state_path);
            AdminReply::Ok
        }
    }
}

fn handle_admin_connection(
    stream: TcpStream,
    shared: SharedState,
    peers: PeerAddrs,
    state_path: Option<PathBuf>,
) {
    let line = match read_one_line(&stream) {
        Ok(l) if !l.trim().is_empty() => l,
        Ok(_) => return,
        Err(e) => {
            eprintln!("[warn] admin connection read error: {e}");
            return;
        }
    };
    let reply = match AdminMessage::decode(&line) {
        Ok(msg) => handle_admin_command(&shared, &peers, &state_path, msg),
        Err(e) => AdminReply::Error { detail: e.to_string() },
    };
    if let Err(e) = write_line(&stream, &reply.encode()) {
        eprintln!("[warn] failed to write admin reply: {e}");
    }
}

fn run_admin_listener(
    bind_addr: String,
    shared: SharedState,
    peers: PeerAddrs,
    state_path: Option<PathBuf>,
) {
    let listener = TcpListener::bind(&bind_addr)
        .unwrap_or_else(|e| panic!("cannot bind admin listener on {bind_addr}: {e}"));
    println!("[admin] listening on {bind_addr}");
    for incoming in listener.incoming() {
        match incoming {
            Ok(stream) => {
                let shared = Arc::clone(&shared);
                let peers = Arc::clone(&peers);
                let state_path = state_path.clone();
                thread::spawn(move || handle_admin_connection(stream, shared, peers, state_path));
            }
            Err(e) => eprintln!("[warn] admin accept error: {e}"),
        }
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 5 {
        eprintln!(
            "usage: {} <node_id> <peer_listen_addr> <admin_listen_addr> <peers_file> [state_file]",
            args[0]
        );
        std::process::exit(1);
    }
    let node_id = args[1].clone();
    let peer_listen_addr = args[2].clone();
    let admin_listen_addr = args[3].clone();
    let peers_file = args[4].clone();
    let state_path: Option<PathBuf> = args.get(5).map(PathBuf::from);

    let peer_map = parse_peers_file(&peers_file, &node_id);
    println!("[init] {node_id}: loaded {} peer(s) from {peers_file}", peer_map.len());
    let peers: PeerAddrs = Arc::new(Mutex::new(peer_map));

    let shared: SharedState = match &state_path {
        Some(path) => match load_node_state(path) {
            Ok(Some(node)) => {
                println!("[init] {node_id}: restored state from {path:?}");
                Arc::new(Mutex::new(NodeShared { node, links: HashMap::new() }))
            }
            Ok(None) => {
                println!("[init] {node_id}: no existing state file, starting fresh");
                NodeShared::new_shared(&node_id)
            }
            Err(e) => {
                eprintln!("[warn] {node_id}: failed to load state from {path:?}: {e}, starting fresh");
                NodeShared::new_shared(&node_id)
            }
        },
        None => NodeShared::new_shared(&node_id),
    };

    let peer_shared = Arc::clone(&shared);
    let peer_addr = peer_listen_addr.clone();
    let peer_thread = thread::spawn(move || run_peer_listener(peer_addr, peer_shared));

    let admin_shared = Arc::clone(&shared);
    let admin_peers = Arc::clone(&peers);
    let admin_state_path = state_path.clone();
    let admin_thread = thread::spawn(move || {
        run_admin_listener(admin_listen_addr, admin_shared, admin_peers, admin_state_path)
    });

    peer_thread.join().expect("peer listener thread panicked");
    admin_thread.join().expect("admin listener thread panicked");
}
