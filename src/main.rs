//! Reproduces the Result 1 counterexample trace (addendum Section 2,
//! States 1-6, 1260 states / 346 distinct), confirms
//! NoDoubleSpendAcrossNodes is violated exactly as TLC found, then
//! shows a Conversion Day barrier closing the gap.
//!
//! Run: cargo run --bin demo_scenarios

use habi_core::conversion_day::{check_post_barrier_safety, run_conversion_day};
use habi_core::network::Network;

fn scenario_result1_without_barrier() {
    println!("{}", "=".repeat(70));
    println!("SCENARIO 1: Result 1 counterexample, reproduced (no barrier)");
    println!("{}", "=".repeat(70));

    let mut net = Network::new(&["N1", "N2", "N3"]);
    net.nodes.get_mut("N1").unwrap().ledger.insert("b1".into());
    net.nodes.get_mut("N2").unwrap().ledger.insert("b2".into());

    // State 2: <LinkDown> N1-N2
    net.link_down("N1", "N2").unwrap();
    // State 3: <LinkUp> N1-N2 back up -> merge -> both hold {b1, b2}
    net.link_up("N1", "N2").unwrap();
    // State 4: <LinkDown> N1-N2 down again, isolating the pair from N3
    net.link_down("N1", "N2").unwrap();
    // State 5: <SpendAt> N1 spends b1 -- only broadcasts to CURRENT
    // direct neighbors. N1 is isolated, so nobody else learns yet.
    net.spend_at("N1", "b1").unwrap();
    // N2 still independently holds b1 from the earlier merge, and was
    // never told it was spent. State 6: <SpendAt> N2 spends b1 too.
    net.spend_at("N2", "b1").unwrap();

    net.print_state("Final state");
    let violations = net.no_double_spend_across_nodes();
    println!("\nNoDoubleSpendAcrossNodes violations: {:?}", violations);
    assert!(
        !violations.is_empty(),
        "expected the same violation TLC found"
    );
    println!("CONFIRMED: same double-spend shape as the addendum's Result 1 trace.");
}

fn scenario_result1_with_barrier() {
    println!("\n{}", "=".repeat(70));
    println!("SCENARIO 2: Same setup, but Conversion Day barrier intervenes");
    println!("{}", "=".repeat(70));

    let mut net = Network::new(&["N1", "N2", "N3"]);
    net.nodes.get_mut("N1").unwrap().ledger.insert("b1".into());
    net.nodes.get_mut("N2").unwrap().ledger.insert("b2".into());

    net.link_down("N1", "N2").unwrap();
    net.link_up("N1", "N2").unwrap();
    net.link_down("N1", "N2").unwrap();
    net.spend_at("N1", "b1").unwrap();

    println!("\n>> Conversion Day barrier fires (coordinator reconciles all nodes) <<");
    run_conversion_day(&mut net, None).expect("barrier should not find a conflict here");
    net.print_state("State immediately after Conversion Day");

    // N2's ledger no longer contains b1 (it was globally spent), so
    // this spend now correctly fails instead of silently double-spending.
    match net.spend_at("N2", "b1") {
        Ok(()) => println!("UNEXPECTED: N2 was able to spend b1 after the barrier"),
        Err(e) => println!("\nN2 attempted to spend b1 and was correctly rejected: {e}"),
    }

    let ok = check_post_barrier_safety(&net, None);
    println!("\ncheck_post_barrier_safety(): {ok}");
    assert!(ok, "barrier should have closed the gap");
    println!("CONFIRMED: Conversion Day closes exactly the gap Result 1/2 describe.");
}

fn scenario_barrier_after_real_double_spend() {
    println!("\n{}", "=".repeat(70));
    println!("SCENARIO 3: Barrier correctly detects a real pre-existing double-spend");
    println!("{}", "=".repeat(70));

    let mut net = Network::new(&["N1", "N2", "N3"]);
    net.nodes.get_mut("N1").unwrap().ledger.insert("b1".into());
    net.nodes.get_mut("N2").unwrap().ledger.insert("b2".into());

    net.link_down("N1", "N2").unwrap();
    net.link_up("N1", "N2").unwrap();
    net.link_down("N1", "N2").unwrap();
    net.spend_at("N1", "b1").unwrap();
    net.spend_at("N2", "b1").unwrap(); // both nodes have now genuinely spent b1

    match run_conversion_day(&mut net, None) {
        Ok(()) => println!("UNEXPECTED: barrier did not detect the double-spend"),
        Err(e) => {
            println!("\nConversion Day correctly detected an unresolvable conflict: {e}");
            println!("(This is what has to be escalated out-of-band -- the barrier");
            println!(" prevents FUTURE double-spends, it cannot undo one that");
            println!(" already completed before the barrier ran.)");
        }
    }
}

fn main() {
    scenario_result1_without_barrier();
    scenario_result1_with_barrier();
    scenario_barrier_after_real_double_spend();
    println!("\n{}", "=".repeat(70));
    println!("All scenarios completed.");
    println!("{}", "=".repeat(70));
}
