//! Pure, socket-free Conversion Day coordination logic for the
//! distributed habi_node binary. Mirrors conversion_day.rs's
//! run_conversion_day() exactly, but operates on gathered
//! PeerSnapshot data instead of a centralized &mut Network -- the
//! habi_node binary is responsible for gathering these snapshots
//! over the network (via StatusRequest/StatusReply) and applying
//! the resulting burn set back out (via SpentNotify broadcast), but
//! all the actual conflict-detection/merge logic lives here,
//! unit-testable without any sockets.

use std::collections::{HashMap, HashSet};
use std::fmt;

#[derive(Debug, Clone)]
pub struct PeerSnapshot {
    pub node_id: String,
    pub ledger: HashSet<String>,
    pub spent: HashSet<String>,
}

/// Mirrors conversion_day.rs's DoubleSpendDetected: raised if more
/// than one node genuinely spent the same bearer. Conversion Day
/// cannot un-spend it -- this is returned for out-of-band handling,
/// same as the centralized version.
#[derive(Debug)]
pub struct ConversionDayConflict {
    pub violations: Vec<(String, Vec<String>)>,
}

impl fmt::Display for ConversionDayConflict {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "double-spend detected during distributed reconciliation: {:?}",
            self.violations
        )
    }
}
impl std::error::Error for ConversionDayConflict {}

/// Mirrors conversion_day.rs::run_conversion_day's logic exactly:
/// 1. Gather spent-by-bearer across all snapshots.
/// 2. If any bearer was spent by more than one node, that's a real
///    conflict -- return it as an error, do not attempt resolution.
/// 3. Otherwise return the full set of globally-spent bearers, which
///    the caller must then burn from every node's ledger (via
///    SpentNotify broadcast in the networked version).
pub fn compute_conversion_day(
    snapshots: &[PeerSnapshot],
) -> Result<HashSet<String>, ConversionDayConflict> {
    let mut spent_by: HashMap<String, HashSet<String>> = HashMap::new();
    for snap in snapshots {
        for b in &snap.spent {
            spent_by
                .entry(b.clone())
                .or_default()
                .insert(snap.node_id.clone());
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
        return Err(ConversionDayConflict { violations });
    }

    Ok(spent_by.keys().cloned().collect())
}

/// Mirrors conversion_day.rs::check_post_barrier_safety: true if, for
/// the given snapshots, no bearer remains held by a node that also
/// appears (anywhere in the set) as having spent it.
pub fn check_post_conversion_day_safety(snapshots: &[PeerSnapshot]) -> bool {
    let global_spent: HashSet<String> = snapshots
        .iter()
        .flat_map(|s| s.spent.iter().cloned())
        .collect();

    for snap in snapshots {
        if snap.ledger.iter().any(|b| global_spent.contains(b)) {
            return false;
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;

    fn set(items: &[&str]) -> HashSet<String> {
        items.iter().map(|s| s.to_string()).collect()
    }

    #[test]
    fn no_conflict_returns_the_globally_spent_set() {
        let snapshots = vec![
            PeerSnapshot {
                node_id: "N1".into(),
                ledger: set(&["b2"]),
                spent: set(&["b1"]),
            },
            PeerSnapshot {
                node_id: "N2".into(),
                ledger: set(&["b2"]),
                spent: set(&[]),
            },
            PeerSnapshot {
                node_id: "N3".into(),
                ledger: set(&[]),
                spent: set(&[]),
            },
        ];
        let result = compute_conversion_day(&snapshots).unwrap();
        assert_eq!(result, set(&["b1"]));
    }

    #[test]
    fn genuine_double_spend_is_detected_as_a_conflict() {
        // Mirrors Result 1 exactly: both N1 and N2 spent b1 independently.
        let snapshots = vec![
            PeerSnapshot {
                node_id: "N1".into(),
                ledger: set(&["b2"]),
                spent: set(&["b1"]),
            },
            PeerSnapshot {
                node_id: "N2".into(),
                ledger: set(&["b2"]),
                spent: set(&["b1"]),
            },
        ];
        let err = compute_conversion_day(&snapshots).unwrap_err();
        assert_eq!(err.violations, vec![("b1".to_string(), vec!["N1".to_string(), "N2".to_string()])]);
    }

    #[test]
    fn post_conversion_day_safety_holds_after_correct_burn() {
        // Simulates the state AFTER a successful (no-conflict) burn:
        // b1 removed from every ledger, spent sets untouched.
        let snapshots = vec![
            PeerSnapshot {
                node_id: "N1".into(),
                ledger: set(&[]), // b1 already burned here
                spent: set(&["b1"]),
            },
            PeerSnapshot {
                node_id: "N2".into(),
                ledger: set(&[]), // b1 burned here too
                spent: set(&[]),
            },
        ];
        assert!(check_post_conversion_day_safety(&snapshots));
    }

    #[test]
    fn post_conversion_day_safety_fails_if_burn_was_incomplete() {
        let snapshots = vec![
            PeerSnapshot {
                node_id: "N1".into(),
                ledger: set(&[]),
                spent: set(&["b1"]),
            },
            PeerSnapshot {
                node_id: "N2".into(),
                ledger: set(&["b1"]), // still holds it -- burn didn't reach N2
                spent: set(&[]),
            },
        ];
        assert!(!check_post_conversion_day_safety(&snapshots));
    }
}
