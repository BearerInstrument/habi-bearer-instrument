//! Conversion Day settlement barrier.
//!
//! Implements Month 9 path (a) from the addendum's Section 4:
//!   "Introduce a coordinating settlement mechanism ... and re-verify
//!    PairwiseSyncedNoDoubleSpend or an equivalent global property
//!    against the extended design."
//!
//! Deliberately NOT path (b) (liveness/eventual reframing) — this
//! barrier is checked as a state-by-state SAFETY property: either
//! global consistency holds immediately after the barrier fires, or
//! it returns an error.
//!
//! Design: a periodic/triggered global reconciliation event. Unlike
//! LinkUp (pairwise, direct-link-only), Conversion Day requires the
//! *coordinator* to have gathered spent/ledger state from every node
//! scheduled to participate — the "designated reconciliation
//! authority" option named in Section 4(a), chosen over version
//! vectors for this first prototype because it's simplest to model.

use crate::network::{LogEntry, Network};
use std::collections::{HashMap, HashSet};
use std::fmt;

/// Raised if Conversion Day itself discovers a bearer spent by more
/// than one node. This should never happen if every node observes
/// Conversion Day reliably; see module docs re: what the barrier does
/// and does not guarantee.
#[derive(Debug)]
pub struct DoubleSpendDetected {
    pub violations: Vec<(String, Vec<String>)>,
}

impl fmt::Display for DoubleSpendDetected {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "double-spend detected during reconciliation: {:?}",
            self.violations
        )
    }
}
impl std::error::Error for DoubleSpendDetected {}

/// Perform one global reconciliation event.
///
/// 1. Gather every participating node's `spent` set (this is the
///    coordinating step that per-link gossip alone cannot do — it
///    requires the barrier to see all nodes at once, not pairwise).
/// 2. If any bearer was spent by more than one node, that is a
///    genuine double-spend that already happened; Conversion Day
///    cannot un-spend it, so it's returned as an error for
///    out-of-band handling (this prototype does not attempt
///    automatic resolution).
/// 3. Otherwise, remove every spent bearer from every participating
///    node's ledger — closing exactly the gap the addendum's Result 2
///    describes, and (per Month 9 follow-up) the Result 3 gap too: this
///    barrier doesn't care HOW a node ended up holding a stale bearer
///    (a direct spend it missed, or a Propagate from a neighbor who
///    hadn't heard of the spend yet) -- it only checks the true global
///    spent set, so both failure shapes are closed the same way. See
///    `conversion_day_closes_propagate_only_gap` in tests/invariants.rs.
///
/// `participants` defaults to all nodes in the network when `None`.
/// Nodes NOT in `participants` (e.g. still disconnected / EMCON at
/// barrier time) are left untouched — this prototype makes no
/// liveness claim about when they'll eventually reconcile; it only
/// guarantees that whichever nodes DID participate end this call in a
/// mutually consistent state.
/// Rust implementation of the reconcile-on-reconnect step proved safe in
/// habi_safety.v as `SStep_SafeReconnect` (Section 6/7, Month 9 Coq proof).
/// A bare reconnect with no reconciliation is UNSAFE after an offline
/// double-spend -- see `naive_reconnect_breaks_safety` in habi_safety.v,
/// which replays this system's Result 1 trace as a machine-checked
/// counterexample. This function is what closes that gap; the corresponding
/// safety theorem is `safe_step_preserves_invariant`.
pub fn run_conversion_day(
    net: &mut Network,
    participants: Option<&HashSet<String>>,
) -> Result<(), DoubleSpendDetected> {
    let all_ids: HashSet<String> = net.nodes.keys().cloned().collect();
    let participants: HashSet<String> = participants.cloned().unwrap_or(all_ids);

    let mut spent_by: HashMap<String, HashSet<String>> = HashMap::new();
    for nid in &participants {
        if let Some(node) = net.nodes.get(nid) {
            for b in &node.spent {
                spent_by.entry(b.clone()).or_default().insert(nid.clone());
            }
        }
    }

    let mut violations: Vec<(String, Vec<String>)> = spent_by
        .iter()
        .filter(|(_, ns)| ns.len() > 1)
        .map(|(b, ns)| {
            let mut v: Vec<String> = ns.iter().cloned().collect();
            v.sort();
            (b.clone(), v)
        })
        .collect();
    violations.sort();

    if !violations.is_empty() {
        return Err(DoubleSpendDetected { violations });
    }

    let globally_spent: HashSet<String> = spent_by.keys().cloned().collect();
    for nid in &participants {
        if let Some(node) = net.nodes.get_mut(nid) {
            for b in &globally_spent {
                node.ledger.remove(b);
            }
        }
    }

    let mut cleared: Vec<&String> = globally_spent.iter().collect();
    cleared.sort();
    let mut sorted_participants: Vec<&String> = participants.iter().collect();
    sorted_participants.sort();

    net.log.push(LogEntry {
        action: "ConversionDay".to_string(),
        detail: format!(
            "participants={:?}, cleared={:?}",
            sorted_participants, cleared
        ),
    });

    Ok(())
}

/// Safety check to run immediately after run_conversion_day(), matching
/// the addendum's Month 9 plan: re-verify a global-consistency
/// invariant against the extended design, as a safety property (not
/// liveness).
///
/// Returns true if, restricted to `participants`, no bearer remains
/// double-held (i.e. Result 1/Result 2/Result 3's failure modes are
/// closed for the reconciled set).
/// Formally corresponds to `SStep_SafeReconnect` / `safe_step_preserves_invariant`
/// in habi_safety.v (Month 9 Coq proof, Topic 55-24-02). That proof shows a bare
/// network reconnect is unsafe after an offline double-spend (see
/// `naive_reconnect_breaks_safety`, built from this file's own Result 1 trace);
/// this function is the safety check that must hold post-barrier, matching the
/// conclusion of `safe_step_preserves_invariant` for arbitrary node/bearer counts.
pub fn check_post_barrier_safety(net: &Network, participants: Option<&HashSet<String>>) -> bool {
    let all_ids: HashSet<String> = net.nodes.keys().cloned().collect();
    let participants: HashSet<String> = participants.cloned().unwrap_or(all_ids);

    let global_spent: HashSet<String> = participants
        .iter()
        .filter_map(|n| net.nodes.get(n))
        .flat_map(|node| node.spent.iter().cloned())
        .collect();

    for n in &participants {
        if let Some(node) = net.nodes.get(n) {
            if node.ledger.iter().any(|b| global_spent.contains(b)) {
                return false;
            }
        }
    }
    true
}
