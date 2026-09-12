//! Automated integration test: spawns three real habi_node processes,
//! drives them through the exact Result 1 double-spend scenario over
//! actual TCP sockets (not in-process function calls), and asserts
//! the same double-spend shape already proven by
//! no_double_spend_violated_reproduces_result1 (tests/invariants.rs),
//! DIL_CRDT.tla's Result 1, and habi_safety.v's
//! naive_reconnect_breaks_safety -- now reproduced across genuinely
//! separate OS processes.
//!
//! Run with: cargo test --test networked_double_spend
//! (runs alongside the rest of `cargo test` by default too)

use std::io::{BufRead, BufReader, Write};
use std::net::TcpStream;
use std::path::PathBuf;
use std::process::{Child, Command, Stdio};
use std::thread;
use std::time::Duration;

/// Wraps a spawned habi_node child process. Killed automatically on
/// drop (including when a test panics mid-assertion, since Drop runs
/// during unwinding) -- this is what prevents orphaned background
/// processes from a failed test run.
struct NodeProcess {
    child: Child,
    #[allow(dead_code)] // kept for debug visibility (e.g. in a debugger or future eprintln)
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
    NodeProcess {
        child,
        node_id: node_id.to_string(),
    }
}

/// Sends one AdminMessage-encoded line to addr, returns the raw reply
/// line. Retries the connection briefly, since the listener thread
/// may not have bound yet immediately after process spawn.
fn admin_call(addr: &str, line: &str) -> String {
    let mut last_err = String::new();
    for attempt in 0..20 {
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
        let _ = attempt;
    }
    panic!("admin_call to {addr} failed after retries: {last_err} (line was {line:?})");
}

fn assert_ok(reply: &str, context: &str) {
    assert!(
        reply == "REPLY_OK",
        "{context}: expected REPLY_OK, got {reply:?}"
    );
}

/// Parses a REPLY_STATUS line into (ledger, spent) sorted Vec<String>
/// pairs, for assertion convenience. Minimal parsing here (not using
/// the crate's own AdminReply::decode) is deliberate -- this keeps
/// the integration test's assertions independent of the exact same
/// parser under test, so a bug in AdminReply::decode itself wouldn't
/// silently mask a wire-format regression.
fn parse_status(reply: &str) -> (Vec<String>, Vec<String>) {
    // REPLY_STATUS|node_id|ledger_csv|spent_csv|links_csv
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

#[test]
fn networked_double_spend_reproduces_result1_over_real_tcp() {
    let tmp_dir = std::env::temp_dir().join(format!(
        "habi_networked_test_{}",
        std::process::id()
    ));
    std::fs::create_dir_all(&tmp_dir).unwrap();

    let peers_file = tmp_dir.join("peers.txt");
    std::fs::write(
        &peers_file,
        "N1|127.0.0.1:19001\nN2|127.0.0.1:19002\nN3|127.0.0.1:19003\n",
    )
    .unwrap();

    let n1_state = tmp_dir.join("N1.state");
    let n2_state = tmp_dir.join("N2.state");
    let n3_state = tmp_dir.join("N3.state");

    // Distinct port range from the manual smoketest (9001-9103) so
    // this test can run even if smoketest processes are still up.
    let _n1 = spawn_node("N1", "127.0.0.1:19001", "127.0.0.1:19101", &peers_file, &n1_state);
    let _n2 = spawn_node("N2", "127.0.0.1:19002", "127.0.0.1:19102", &peers_file, &n2_state);
    let _n3 = spawn_node("N3", "127.0.0.1:19003", "127.0.0.1:19103", &peers_file, &n3_state);

    // Give all three listeners a moment to bind before the first
    // admin_call's retry loop starts (retries handle stragglers too).
    thread::sleep(Duration::from_millis(200));

    let n1_admin = "127.0.0.1:19101";
    let n2_admin = "127.0.0.1:19102";

    // Seed initial holdings: N1:{b1}, N2:{b2} -- matches
    // make_init_network() in tests/invariants.rs exactly.
    assert_ok(&admin_call(n1_admin, "ADMIN_SEED|b1"), "seed N1 b1");
    assert_ok(&admin_call(n2_admin, "ADMIN_SEED|b2"), "seed N2 b2");

    // LinkUp N1-N2, verify the merge produced ["b1","b2"] on both sides.
    assert_ok(&admin_call(n1_admin, "ADMIN_LINK_UP|N2"), "link-up N1-N2");

    let (n1_ledger_after_merge, _) = parse_status(&admin_call(n1_admin, "ADMIN_STATUS"));
    assert_eq!(
        n1_ledger_after_merge,
        vec!["b1".to_string(), "b2".to_string()],
        "N1 must hold both bearers after LinkUp merge"
    );
    let (n2_ledger_after_merge, _) = parse_status(&admin_call(n2_admin, "ADMIN_STATUS"));
    assert_eq!(
        n2_ledger_after_merge,
        vec!["b1".to_string(), "b2".to_string()],
        "N2 must hold both bearers after LinkUp merge (symmetric)"
    );

    // LinkDown, then spend b1 on BOTH sides while disconnected -- the
    // exact double-spend shape from Result 1.
    assert_ok(&admin_call(n1_admin, "ADMIN_LINK_DOWN|N2"), "link-down N1-N2");

    assert_ok(&admin_call(n1_admin, "ADMIN_SPEND_AT|b1"), "N1 spends b1");
    assert_ok(&admin_call(n2_admin, "ADMIN_SPEND_AT|b1"), "N2 spends b1");

    let (n1_final_ledger, n1_final_spent) = parse_status(&admin_call(n1_admin, "ADMIN_STATUS"));
    let (n2_final_ledger, n2_final_spent) = parse_status(&admin_call(n2_admin, "ADMIN_STATUS"));

    assert_eq!(
        n1_final_spent,
        vec!["b1".to_string()],
        "N1 must show b1 as spent"
    );
    assert_eq!(
        n2_final_spent,
        vec!["b1".to_string()],
        "N2 must show b1 as spent -- this IS the double-spend: both \
         nodes genuinely spent b1 independently while disconnected, \
         matching no_double_spend_violated_reproduces_result1"
    );
    assert!(
        !n1_final_ledger.contains(&"b1".to_string()),
        "N1 must not still list b1 as held after spending it"
    );
    assert!(
        !n2_final_ledger.contains(&"b1".to_string()),
        "N2 must not still list b1 as held after spending it"
    );

    let _ = std::fs::remove_dir_all(&tmp_dir);
}
