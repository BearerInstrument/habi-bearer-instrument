//! cargo test
//!
//! Tests the two invariants from DIL_CRDT_PerLink_Symmetric.tla against
//! the Rust model, plus the Conversion Day barrier's safety guarantee.

use habi_core::conversion_day::{check_post_barrier_safety, run_conversion_day};
use habi_core::network::Network;

fn make_init_network() -> Network {
    let mut net = Network::new(&["N1", "N2", "N3"]);
    net.nodes.get_mut("N1").unwrap().ledger.insert("b1".into());
    net.nodes.get_mut("N2").unwrap().ledger.insert("b2".into());
    net
}

#[test]
fn fresh_network_satisfies_both_invariants() {
    let net = make_init_network();
    assert!(net.no_double_spend_across_nodes().is_empty());
    assert!(net.pairwise_synced_no_double_spend().is_empty());
}

#[test]
fn no_double_spend_violated_reproduces_result1() {
    let mut net = make_init_network();
    net.link_down("N1", "N2").unwrap();
    net.link_up("N1", "N2").unwrap();
    net.link_down("N1", "N2").unwrap();
    net.spend_at("N1", "b1").unwrap();
    net.spend_at("N2", "b1").unwrap();

    let violations = net.no_double_spend_across_nodes();
    assert_eq!(
        violations,
        vec![("b1".to_string(), vec!["N1".to_string(), "N2".to_string()])]
    );
}

/// Reproduces the addendum's Result 2 trace (Section 3, States 1-7)
/// exactly:
///   - N1 merges with N2 (both end up holding b1,b2), then splits off
///   - N2 spends b1 while isolated from N1 -- N1 never hears about it
///   - N1 (still holding b1,b2, unaware of the spend) later merges with
///     N3, so N3 inherits the stale belief that b1 is still good
///   - N2 stays linked to N3 throughout, so once N3 holds b1 the
///     PairwiseSyncedNoDoubleSpend invariant is violated on the N2-N3
///     edge: N2 has spent b1, but its direct neighbor N3 still lists
///     b1 as valid.
#[test]
fn pairwise_synced_violated_reproduces_result2() {
    let mut net = make_init_network();
    net.link_down("N1", "N2").unwrap();
    net.link_down("N1", "N3").unwrap(); // N1 isolated; N2-N3 stays up throughout
    net.link_up("N1", "N2").unwrap(); // merge: N1, N2 both -> {b1, b2}
    net.link_down("N1", "N2").unwrap();
    net.spend_at("N2", "b1").unwrap(); // N2 spends b1; N1 (isolated) never hears it
    net.link_up("N1", "N3").unwrap(); // N1's stale {b1,b2} merges into N3

    let violations = net.pairwise_synced_no_double_spend();
    assert!(
        !violations.is_empty(),
        "expected a pairwise-sync violation like Result 2"
    );
    assert!(violations.iter().any(|(n1, n2, b)| {
        b == "b1" && ((n1 == "N2" && n2 == "N3") || (n1 == "N3" && n2 == "N2"))
    }));
}

#[test]
fn conversion_day_prevents_future_double_spend() {
    let mut net = make_init_network();
    net.link_down("N1", "N2").unwrap();
    net.link_up("N1", "N2").unwrap();
    net.link_down("N1", "N2").unwrap();
    net.spend_at("N1", "b1").unwrap();

    run_conversion_day(&mut net, None).unwrap();
    assert!(check_post_barrier_safety(&net, None));

    assert!(
        net.spend_at("N2", "b1").is_err(),
        "N2 should not have been able to spend b1"
    );
}

#[test]
fn conversion_day_raises_on_preexisting_double_spend() {
    let mut net = make_init_network();
    net.link_down("N1", "N2").unwrap();
    net.link_up("N1", "N2").unwrap();
    net.link_down("N1", "N2").unwrap();
    net.spend_at("N1", "b1").unwrap();
    net.spend_at("N2", "b1").unwrap();

    let err = run_conversion_day(&mut net, None).unwrap_err();
    assert_eq!(
        err.violations[0],
        ("b1".to_string(), vec!["N1".to_string(), "N2".to_string()])
    );
}

#[test]
fn propagate_only_violates_pairwise_sync_result3() {
    let mut net = make_init_network(); // N1:{b1}, N2:{b2}, N3:{}, fully linked
    net.propagate("N2", "N1").unwrap();      // N1 pulls b2 from N2
    net.link_down("N1", "N2").unwrap();      // N1-N2 drops; N1-N3, N2-N3 stay up
    net.spend_at("N1", "b2").unwrap();       // N1 spends b2 (N3 had none, no visible change)
    net.propagate("N2", "N3").unwrap();      // N3 gets b2 from N2 — but N1 (linked to N3) already spent it

    let violations = net.pairwise_synced_no_double_spend();
    assert!(!violations.is_empty(), "expected a pairwise-sync violation via Propagate alone");
}

#[test]
fn conversion_day_closes_propagate_only_gap() {
    let mut net = make_init_network();
    net.propagate("N2", "N1").unwrap();
    net.link_down("N1", "N2").unwrap();
    net.spend_at("N1", "b2").unwrap();
    net.propagate("N2", "N3").unwrap();

    // Precondition: the vulnerability from Result 3 is present before the barrier
    assert!(!net.pairwise_synced_no_double_spend().is_empty());

    // Conversion Day should reconcile it without raising, since only N1 has
    // actually spent b2 -- this is staleness, not a genuine double-spend.
    run_conversion_day(&mut net, None).unwrap();
    assert!(check_post_barrier_safety(&net, None));
}
