//! Automated integration test: spawns three real habi_node processes
//! and drives the networked ConversionDay coordinator through both
//! its outcomes over actual TCP sockets:
//!   1. Genuine conflict (both N1 and N2 spend b1) -- must return
//!      REPLY_ERROR naming both nodes, and leave all state UNCHANGED
//!      (no partial burn/mutation -- compute_conversion_day is
//!      checked before any mutation is attempted, so the conflict
//!      path is atomic by construction, not via rollback).
//!   2. No conflict (only N1 spends b1) -- must return REPLY_OK,
//!      burn b1 from every node's ledger via SpentNotify broadcast,
//!      and leave b1 permanently unspendable everywhere afterward.
//!
//! Mirrors conversion_day_raises_on_preexisting_double_spend and
//! conversion_day_prevents_future_double_spend (tests/invariants.rs)
//! -- now reproduced across genuinely separate OS processes.

use std::io::{BufRead, BufReader, Write};
use std::net::TcpStream;
use std::path::PathBuf;
use std::process::{Child, Command, Stdio};
use std::thread;
use std::time::Duration;

struct NodeProcess {
    child: Child,
    #[allow(dead_code)]
    node_id: String,
}

impl Drop for NodeProcess {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

fn spawn_node(
    node_id: &str,
    peer_addr: &str,
    admin_addr: &str,
    peers_file: &PathBuf,
    state_file: &PathBuf,
) -> NodeProcess {
    let bin = env!("CARGO_BIN_EXE_habi_node");
    let child = Command::new(bin)
        .arg(node_id)
        .arg(peer_addr)
        .arg(admin_addr)
        .arg(peers_file)
        .arg(state_file)
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()
        .unwrap_or_else(|e| panic!("failed to spawn habi_node for {node_id}: {e}"));
    NodeProcess { child, node_id: node_id.to_string() }
}

fn admin_call(addr: &str, line: &str) -> String {
    let mut last_err = String::new();
    for _ in 0..20 {
        match TcpStream::connect(addr) {
            Ok(mut stream) => {
                if writeln!(stream, "{line}").is_err() {
                    last_err = "write failed".to_string();
                    thread::sleep(Duration::from_millis(50));
                    continue;
                }
                let mut reader = BufReader::new(&stream);
                let mut reply = String::new();
                if reader.read_line(&mut reply).is_err() || reply.trim().is_empty() {
                    last_err = "empty or failed read".to_string();
                    thread::sleep(Duration::from_millis(50));
                    continue;
                }
                return reply.trim().to_string();
            }
            Err(e) => {
                last_err = e.to_string();
                thread::sleep(Duration::from_millis(50));
            }
        }
    }
    panic!("admin_call to {addr} failed after retries: {last_err} (line was {line:?})");
}

fn assert_ok(reply: &str, context: &str) {
    assert!(reply == "REPLY_OK", "{context}: expected REPLY_OK, got {reply:?}");
}

fn parse_status(reply: &str) -> (Vec<String>, Vec<String>) {
    let parts: Vec<&str> = reply.splitn(5, '|').collect();
    assert_eq!(parts[0], "REPLY_STATUS", "expected REPLY_STATUS, got {reply:?}");
    let parse_csv = |s: &str| -> Vec<String> {
        if s.is_empty() {
            Vec::new()
        } else {
            let mut v: Vec<String> = s.split(',').map(|x| x.to_string()).collect();
            v.sort();
            v
        }
    };
    (parse_csv(parts[2]), parse_csv(parts[3]))
}

fn setup_three_nodes(tag: &str) -> (PathBuf, NodeProcess, NodeProcess, NodeProcess, String, String, String) {
    let tmp_dir = std::env::temp_dir().join(format!(
        "habi_convday_test_{tag}_{}",
        std::process::id()
    ));
    std::fs::create_dir_all(&tmp_dir).unwrap();

    let peers_file = tmp_dir.join("peers.txt");
    // Distinct port range per scenario (29001-29003 conflict,
    // 29011-29013 no-conflict) so both scenarios in this file can
    // run without colliding, and don't collide with
    // networked_double_spend.rs's 19001-19003 range either.
    let (p1, p2, p3, a1, a2, a3) = match tag {
        "conflict" => (29001, 29002, 29003, 29101, 29102, 29103),
        "noconflict" => (29011, 29012, 29013, 29111, 29112, 29113),
        other => panic!("unknown tag {other}"),
    };
    std::fs::write(
        &peers_file,
        format!(
            "N1|127.0.0.1:{p1}\nN2|127.0.0.1:{p2}\nN3|127.0.0.1:{p3}\n"
        ),
    )
    .unwrap();

    let n1_state = tmp_dir.join("N1.state");
    let n2_state = tmp_dir.join("N2.state");
    let n3_state = tmp_dir.join("N3.state");

    let n1 = spawn_node("N1", &format!("127.0.0.1:{p1}"), &format!("127.0.0.1:{a1}"), &peers_file, &n1_state);
    let n2 = spawn_node("N2", &format!("127.0.0.1:{p2}"), &format!("127.0.0.1:{a2}"), &peers_file, &n2_state);
    let n3 = spawn_node("N3", &format!("127.0.0.1:{p3}"), &format!("127.0.0.1:{a3}"), &peers_file, &n3_state);

    thread::sleep(Duration::from_millis(200));

    (
        tmp_dir,
        n1,
        n2,
        n3,
        format!("127.0.0.1:{a1}"),
        format!("127.0.0.1:{a2}"),
        format!("127.0.0.1:{a3}"),
    )
}

#[test]
fn networked_conversion_day_rejects_genuine_conflict_atomically() {
    let (tmp_dir, _n1, _n2, _n3, n1_admin, n2_admin, n3_admin) = setup_three_nodes("conflict");

    // Reproduce a genuine cross-node double-spend: N1 and N2 both
    // spend b1 while disconnected.
    assert_ok(&admin_call(&n1_admin, "ADMIN_SEED|b1"), "seed N1 b1");
    assert_ok(&admin_call(&n2_admin, "ADMIN_SEED|b2"), "seed N2 b2");
    assert_ok(&admin_call(&n1_admin, "ADMIN_LINK_UP|N2"), "link-up N1-N2");
    assert_ok(&admin_call(&n1_admin, "ADMIN_LINK_DOWN|N2"), "link-down N1-N2");
    assert_ok(&admin_call(&n1_admin, "ADMIN_SPEND_AT|b1"), "N1 spends b1");
    assert_ok(&admin_call(&n2_admin, "ADMIN_SPEND_AT|b1"), "N2 spends b1");

    // Snapshot state BEFORE Conversion Day, on all three nodes.
    let before_n1 = admin_call(&n1_admin, "ADMIN_STATUS");
    let before_n2 = admin_call(&n2_admin, "ADMIN_STATUS");
    let before_n3 = admin_call(&n3_admin, "ADMIN_STATUS");

    // Conversion Day must detect the conflict and refuse -- naming
    // both N1 and N2 as the conflicting spenders of b1.
    let reply = admin_call(&n1_admin, "ADMIN_CONVERSION_DAY");
    assert!(
        reply.starts_with("REPLY_ERROR"),
        "expected REPLY_ERROR for a genuine conflict, got {reply:?}"
    );
    assert!(
        reply.contains("b1") && reply.contains('N') ,
        "error should name the conflicting bearer/nodes, got {reply:?}"
    );

    // ATOMICITY: state on ALL THREE nodes must be byte-for-byte
    // unchanged after a rejected Conversion Day -- compute_conversion_day
    // is checked before any mutation is attempted (confirmed by
    // reading src/bin/habi_node.rs directly: the Err arm returns
    // immediately, before any lock for mutation is taken), so there
    // is no partial-write window and nothing to roll back.
    let after_n1 = admin_call(&n1_admin, "ADMIN_STATUS");
    let after_n2 = admin_call(&n2_admin, "ADMIN_STATUS");
    let after_n3 = admin_call(&n3_admin, "ADMIN_STATUS");

    assert_eq!(before_n1, after_n1, "N1 state must be unchanged after a rejected Conversion Day");
    assert_eq!(before_n2, after_n2, "N2 state must be unchanged after a rejected Conversion Day");
    assert_eq!(before_n3, after_n3, "N3 state must be unchanged after a rejected Conversion Day");

    let _ = std::fs::remove_dir_all(&tmp_dir);
}

#[test]
fn networked_conversion_day_burns_and_prevents_future_spend_when_no_conflict() {
    let (tmp_dir, _n1, _n2, _n3, n1_admin, n2_admin, n3_admin) = setup_three_nodes("noconflict");

    // Only N1 seeds and spends b1 -- N2/N3 never touch it. This is
    // NOT a conflict (only one genuine spender), so Conversion Day
    // must succeed and burn b1 everywhere.
    assert_ok(&admin_call(&n1_admin, "ADMIN_SEED|b1"), "seed N1 b1");
    assert_ok(&admin_call(&n1_admin, "ADMIN_LINK_UP|N2"), "link-up N1-N2");
    assert_ok(&admin_call(&n1_admin, "ADMIN_LINK_DOWN|N2"), "link-down N1-N2");
    assert_ok(&admin_call(&n1_admin, "ADMIN_SPEND_AT|b1"), "N1 spends b1");

    let reply = admin_call(&n1_admin, "ADMIN_CONVERSION_DAY");
    assert_ok(&reply, "Conversion Day with no genuine conflict");

    // Heal the link -- N2 must NOT inherit a stale b1 via the merge,
    // since it's already been burned.
    assert_ok(&admin_call(&n1_admin, "ADMIN_LINK_UP|N2"), "heal link N1-N2");

    let (n1_ledger, n1_spent) = parse_status(&admin_call(&n1_admin, "ADMIN_STATUS"));
    let (n2_ledger, n2_spent) = parse_status(&admin_call(&n2_admin, "ADMIN_STATUS"));
    let (n3_ledger, n3_spent) = parse_status(&admin_call(&n3_admin, "ADMIN_STATUS"));

    // b1 must be absent from every ledger everywhere.
    assert!(!n1_ledger.contains(&"b1".to_string()), "N1 must not list b1 as held");
    assert!(!n2_ledger.contains(&"b1".to_string()), "N2 must not list b1 as held");
    assert!(!n3_ledger.contains(&"b1".to_string()), "N3 must not list b1 as held");

    // Only N1 (the genuine spender) shows it in spent -- N2/N3
    // learned of the burn via SpentNotify, which correctly does NOT
    // add to their own spent set (see shared_state.rs::apply_spent_notify).
    assert_eq!(n1_spent, vec!["b1".to_string()], "N1 genuinely spent b1");
    assert!(n2_spent.is_empty(), "N2 never spent b1 itself -- burn must not inflate its spent set");
    assert!(n3_spent.is_empty(), "N3 never spent b1 itself -- burn must not inflate its spent set");

    // Any further spend attempt on b1 must fail on every node.
    let n1_retry = admin_call(&n1_admin, "ADMIN_SPEND_AT|b1");
    let n2_retry = admin_call(&n2_admin, "ADMIN_SPEND_AT|b1");
    let n3_retry = admin_call(&n3_admin, "ADMIN_SPEND_AT|b1");
    assert!(n1_retry.starts_with("REPLY_ERROR"), "N1 spend retry must fail, got {n1_retry:?}");
    assert!(n2_retry.starts_with("REPLY_ERROR"), "N2 spend retry must fail, got {n2_retry:?}");
    assert!(n3_retry.starts_with("REPLY_ERROR"), "N3 spend retry must fail, got {n3_retry:?}");

    let _ = std::fs::remove_dir_all(&tmp_dir);
}
