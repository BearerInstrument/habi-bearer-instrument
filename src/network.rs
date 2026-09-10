//! Mirrors the `Next` relation in DIL_CRDT_PerLink_Symmetric.tla:
//!
//!   Next ==
//!     (\E n, m \in Nodes : LinkDown(n, m))
//!     \/ (\E n, m \in Nodes : LinkUp(n, m))
//!     \/ (\E src, dst \in Nodes : Propagate(src, dst))
//!     \/ (\E nn \in Nodes, bb \in Bearers : SpendAt(nn, bb))
//!
//! Connectivity is symmetric and direct-link-only, matching the spec's
//! SCOPE NOTE: a node only learns of / broadcasts to nodes it is
//! directly linked to.

use crate::node::Node;
use std::collections::{HashMap, HashSet};
use std::fmt;

#[derive(Debug)]
pub struct NetworkError(pub String);

impl fmt::Display for NetworkError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}
impl std::error::Error for NetworkError {}

#[derive(Debug, Clone)]
pub struct LogEntry {
    pub action: String,
    pub detail: String,
}

pub struct Network {
    pub nodes: HashMap<String, Node>,
    /// Symmetric adjacency: links[a][b] == links[b][a] is maintained by
    /// construction (link_down/link_up always flip both directions).
    pub links: HashMap<String, HashMap<String, bool>>,
    /// Audit trail, mirrors the shape of a TLC counterexample trace.
    pub log: Vec<LogEntry>,
}

impl Network {
    pub fn new(node_ids: &[&str]) -> Self {
        let mut nodes = HashMap::new();
        for &id in node_ids {
            nodes.insert(id.to_string(), Node::new(id));
        }
        let mut links: HashMap<String, HashMap<String, bool>> = HashMap::new();
        for &a in node_ids {
            let mut row = HashMap::new();
            for &b in node_ids {
                row.insert(b.to_string(), a != b);
            }
            links.insert(a.to_string(), row);
        }
        Network {
            nodes,
            links,
            log: Vec::new(),
        }
    }

    pub fn connected_to(&self, n: &str) -> HashSet<String> {
        match self.links.get(n) {
            Some(row) => row
                .iter()
                .filter(|(m, &up)| m.as_str() != n && up)
                .map(|(m, _)| m.clone())
                .collect(),
            None => HashSet::new(),
        }
    }

    fn is_linked(&self, n: &str, m: &str) -> Result<bool, NetworkError> {
        self.links
            .get(n)
            .and_then(|row| row.get(m))
            .copied()
            .ok_or_else(|| NetworkError(format!("unknown node pair {n}-{m}")))
    }

    fn record(&mut self, action: &str, detail: String) {
        self.log.push(LogEntry {
            action: action.to_string(),
            detail,
        });
    }

    // ---- TLA+ actions ---------------------------------------------------

    /// LinkDown(n, m): tear down a link symmetrically.
    pub fn link_down(&mut self, n: &str, m: &str) -> Result<(), NetworkError> {
        if n == m {
            return Err(NetworkError("cannot link a node to itself".into()));
        }
        if !self.is_linked(n, m)? {
            return Err(NetworkError(format!("link {n}-{m} already down")));
        }
        self.links.get_mut(n).unwrap().insert(m.to_string(), false);
        self.links.get_mut(m).unwrap().insert(n.to_string(), false);
        self.record("LinkDown", format!("{n}-{m}"));
        Ok(())
    }

    /// LinkUp(n, m): bring a link up and merge ledgers.
    ///
    /// FIX carried over from the .tla FIX comment: merging burns anything
    /// either side already knows was spent, but NEVER rewrites `spent`
    /// itself. `spent` only grows via an actual SpendAt call by that
    /// node — inheriting "spent" through a link merge would conflate
    /// knowledge-of-a-spend with an independent spend event.
    pub fn link_up(&mut self, n: &str, m: &str) -> Result<(), NetworkError> {
        if n == m {
            return Err(NetworkError("cannot link a node to itself".into()));
        }
        if self.is_linked(n, m)? {
            return Err(NetworkError(format!("link {n}-{m} already up")));
        }
        if !self.nodes.contains_key(n) || !self.nodes.contains_key(m) {
            return Err(NetworkError(format!("unknown node {n} or {m}")));
        }

        let merged: HashSet<String> = {
            let known_spent: HashSet<String> = self.nodes[n]
                .spent
                .union(&self.nodes[m].spent)
                .cloned()
                .collect();
            self.nodes[n]
                .ledger
                .union(&self.nodes[m].ledger)
                .filter(|b| !known_spent.contains(*b))
                .cloned()
                .collect()
        };

        self.nodes.get_mut(n).unwrap().ledger = merged.clone();
        self.nodes.get_mut(m).unwrap().ledger = merged;

        self.links.get_mut(n).unwrap().insert(m.to_string(), true);
        self.links.get_mut(m).unwrap().insert(n.to_string(), true);
        self.record("LinkUp", format!("{n}-{m}"));
        Ok(())
    }

    /// Propagate(src, dst): direct-link-only propagation of UNSPENT
    /// holdings. dst only receives what src currently holds and dst
    /// hasn't already spent or already got.
    ///
    /// Result 3 (addendum follow-up, Month 9): deliverability here only
    /// checks dst's OWN spent/ledger sets, never dst's other current
    /// neighbors. So a bearer already spent by one neighbor of dst can
    /// still be freshly delivered to dst by a DIFFERENT neighbor who
    /// hasn't heard of the spend yet -- violating PairwiseSyncedNoDoubleSpend
    /// on the live dst-spender edge, with no LinkUp/merge step involved at
    /// all. See `propagate_only_violates_pairwise_sync_result3` in
    /// tests/invariants.rs for the reproducing trace (confirmed against
    /// TLC on DIL_CRDT_PerLink_Symmetric.tla's PASS.cfg).
    pub fn propagate(&mut self, src: &str, dst: &str) -> Result<(), NetworkError> {
        if !self.is_linked(src, dst)? {
            return Err(NetworkError(format!(
                "no link {src}-{dst}, cannot propagate"
            )));
        }

        let deliverable: HashSet<String> = {
            let node_src = &self.nodes[src];
            let node_dst = &self.nodes[dst];
            node_src
                .ledger
                .iter()
                .filter(|b| !node_dst.spent.contains(*b) && !node_dst.ledger.contains(*b))
                .cloned()
                .collect()
        };
        if deliverable.is_empty() {
            return Err(NetworkError(format!(
                "nothing deliverable from {src} to {dst}"
            )));
        }

        self.nodes
            .get_mut(dst)
            .unwrap()
            .ledger
            .extend(deliverable.iter().cloned());

        let mut delivered: Vec<&String> = deliverable.iter().collect();
        delivered.sort();
        self.record("Propagate", format!("{src}->{dst}: {:?}", delivered));
        Ok(())
    }

    /// SpendAt(nn, bb): broadcasts the revocation to CURRENT DIRECT
    /// NEIGHBORS ONLY — not globally. A node not directly linked at the
    /// moment of the spend does not learn about it until a later
    /// Propagate/LinkUp event reaches it. This is the root cause the
    /// addendum's Result 1/Result 2/Result 3 findings are about.
    pub fn spend_at(&mut self, nn: &str, bb: &str) -> Result<(), NetworkError> {
        let holds = self
            .nodes
            .get(nn)
            .map(|node| node.ledger.contains(bb))
            .unwrap_or(false);
        if !holds {
            return Err(NetworkError(format!(
                "{nn} does not hold {bb}, cannot spend"
            )));
        }

        self.nodes.get_mut(nn).unwrap().spent.insert(bb.to_string());

        let mut targets = self.connected_to(nn);
        targets.insert(nn.to_string());
        for m in &targets {
            if let Some(node) = self.nodes.get_mut(m) {
                node.ledger.remove(bb);
            }
        }
        self.record("SpendAt", format!("{nn}: {bb}"));
        Ok(())
    }

    // ---- invariants (mirror the two TLA+ invariants) --------------------

    /// NoDoubleSpendAcrossNodes ==
    ///   \A bbb \in Bearers : Cardinality({nnn : bbb \in spent[nnn]}) <= 1
    ///
    /// Returns (bearer, spenders) for each violation; empty == holds.
    pub fn no_double_spend_across_nodes(&self) -> Vec<(String, Vec<String>)> {
        let mut all_bearers: HashSet<String> = HashSet::new();
        for node in self.nodes.values() {
            all_bearers.extend(node.ledger.iter().cloned());
            all_bearers.extend(node.spent.iter().cloned());
        }

        let mut violations: Vec<(String, Vec<String>)> = all_bearers
            .iter()
            .filter_map(|b| {
                let mut spenders: Vec<String> = self
                    .nodes
                    .iter()
                    .filter(|(_, node)| node.spent.contains(b))
                    .map(|(id, _)| id.clone())
                    .collect();
                if spenders.len() > 1 {
                    spenders.sort();
                    Some((b.clone(), spenders))
                } else {
                    None
                }
            })
            .collect();
        violations.sort();
        violations
    }

    /// PairwiseSyncedNoDoubleSpend ==
    ///   \A n1, n2 : network[n1][n2] =>
    ///     \A b : (b in spent[n1] \/ b in spent[n2]) =>
    ///             (b notin ledgers[n1] /\ b notin ledgers[n2])
    ///
    /// Returns (n1, n2, bearer) for each violation; empty == holds.
    pub fn pairwise_synced_no_double_spend(&self) -> Vec<(String, String, String)> {
        let mut violations = Vec::new();
        let mut ids: Vec<&String> = self.nodes.keys().collect();
        ids.sort();

        for &n1 in &ids {
            for &n2 in &ids {
                if n1 == n2 {
                    continue;
                }
                let linked = *self
                    .links
                    .get(n1)
                    .and_then(|row| row.get(n2))
                    .unwrap_or(&false);
                if !linked {
                    continue;
                }
                let node1 = &self.nodes[n1];
                let node2 = &self.nodes[n2];
                let mut spent_union: Vec<&String> = node1.spent.union(&node2.spent).collect();
                spent_union.sort();
                for b in spent_union {
                    if node1.ledger.contains(b) || node2.ledger.contains(b) {
                        violations.push((n1.clone(), n2.clone(), b.clone()));
                    }
                }
            }
        }
        violations
    }

    pub fn print_state(&self, label: &str) {
        println!("\n-- {label} --");
        let mut ids: Vec<&String> = self.nodes.keys().collect();
        ids.sort();
        for id in ids {
            let node = &self.nodes[id];
            let mut ledger: Vec<&String> = node.ledger.iter().collect();
            ledger.sort();
            let mut spent: Vec<&String> = node.spent.iter().collect();
            spent.sort();
            println!("  Node({id}, ledger={:?}, spent={:?})", ledger, spent);
        }
    }
}
