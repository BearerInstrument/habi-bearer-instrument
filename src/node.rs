//! Mirrors TypeOK / Init from DIL_CRDT_PerLink_Symmetric.tla:
//!   ledgers \in [Nodes -> SUBSET Bearers]
//!   spent   \in [Nodes -> SUBSET Bearers]

use std::collections::HashSet;

#[derive(Debug, Clone)]
pub struct Node {
    pub node_id: String,
    /// Bearers this node currently holds.
    pub ledger: HashSet<String>,
    /// Bearers this node has spent.
    pub spent: HashSet<String>,
}

impl Node {
    pub fn new(node_id: &str) -> Self {
        Node {
            node_id: node_id.to_string(),
            ledger: HashSet::new(),
            spent: HashSet::new(),
        }
    }

    pub fn holds(&self, bearer: &str) -> bool {
        self.ledger.contains(bearer)
    }
}
