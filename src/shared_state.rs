//! Thread-safe per-node state for the distributed habi_node binary.
//!
//! This module holds ONE node's view of the world (its own ledger,
//! spent set, and per-peer link status) and exposes pure functions
//! for the state transitions a distributed node needs. Unlike
//! network.rs's centralized Network (which has direct access to
//! every node's Node struct), a real node only ever has its own
//! state plus whatever a peer sends it over the wire -- so these
//! functions take peer data as plain arguments rather than reaching
//! into a shared Network.
//!
//! IMPORTANT semantic note on Propagate: network.rs's centralized
//! propagate(src, dst) computes
//!   deliverable = (ledger[src] \ spent[dst]) \ ledger[dst]
//! which needs BOTH sides' state. A distributed source node cannot
//! compute this alone (it doesn't have dst's spent set). So here,
//! PropagateReply carries the source's FULL raw ledger (unfiltered),
//! and the REQUESTER computes the filter locally via
//! compute_propagate_deliverable, using its own spent+ledger plus
//! the received raw ledger. This mirrors how LinkUp already works
//! (both sides exchange raw state, each computes the same merge
//! independently) and needs no change to PropagateRequest's wire shape.

use crate::node::Node;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::sync::{Arc, Mutex};

#[derive(Debug)]
pub struct StateError(pub String);

impl fmt::Display for StateError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}
impl std::error::Error for StateError {}

/// One node's local, mutable view: its own Node data plus per-peer
/// link status (true == link up). Does NOT know about peers it has
/// no link entry for yet -- is_linked defaults to false for unknown
/// peer ids, matching network.rs's is_linked error-on-unknown-pair
/// behavior loosely (here, simply "not linked" rather than an error,
/// since a distributed node may legitimately not have heard of a
/// peer yet).
pub struct NodeShared {
    pub node: Node,
    pub links: HashMap<String, bool>,
}

pub type SharedState = Arc<Mutex<NodeShared>>;

impl NodeShared {
    pub fn new(node_id: &str) -> Self {
        NodeShared {
            node: Node::new(node_id),
            links: HashMap::new(),
        }
    }

    pub fn new_shared(node_id: &str) -> SharedState {
        Arc::new(Mutex::new(Self::new(node_id)))
    }

    pub fn is_linked(&self, peer: &str) -> bool {
        *self.links.get(peer).unwrap_or(&false)
    }

    pub fn set_link(&mut self, peer: &str, up: bool) {
        self.links.insert(peer.to_string(), up);
    }

    pub fn connected_peers(&self) -> Vec<String> {
        let mut peers: Vec<String> = self
            .links
            .iter()
            .filter(|(_, &up)| up)
            .map(|(id, _)| id.clone())
            .collect();
        peers.sort();
        peers
    }

    /// LinkUp merge: mirrors network.rs::link_up's
    ///   merged = (ledger[n] u ledger[m]) \ (spent[n] u spent[m])
    /// computed here from this node's own state plus a peer's raw
    /// ledger/spent (received via LinkUpHello/LinkUpAck). Pure --
    /// does not mutate self or set the link.
    pub fn compute_link_up_merge(
        &self,
        peer_ledger: &HashSet<String>,
        peer_spent: &HashSet<String>,
    ) -> HashSet<String> {
        let known_spent: HashSet<String> =
            self.node.spent.union(peer_spent).cloned().collect();
        self.node
            .ledger
            .union(peer_ledger)
            .filter(|b| !known_spent.contains(*b))
            .cloned()
            .collect()
    }

    /// Applies a precomputed LinkUp merge: sets this node's ledger to
    /// `merged` and marks the link to `peer` up. spent is unchanged
    /// (spent only ever grows via local_spend, never via a merge --
    /// same invariant network.rs's FIX comment documents).
    pub fn apply_link_up(&mut self, peer: &str, merged: HashSet<String>) {
        self.node.ledger = merged;
        self.set_link(peer, true);
    }

    pub fn apply_link_down(&mut self, peer: &str) {
        self.set_link(peer, false);
    }

    /// Mirrors network.rs::propagate's deliverable filter, computed
    /// from this node's own spent+ledger against a peer's RAW
    /// (unfiltered) ledger, per the module-level note above.
    pub fn compute_propagate_deliverable(&self, peer_ledger: &HashSet<String>) -> HashSet<String> {
        peer_ledger
            .iter()
            .filter(|b| !self.node.spent.contains(*b) && !self.node.ledger.contains(*b))
            .cloned()
            .collect()
    }

    pub fn apply_propagate_deliverable(&mut self, deliverable: HashSet<String>) {
        self.node.ledger.extend(deliverable);
    }

    /// A peer notified us it spent `bearer` -- mirrors the remote-node
    /// side effect of network.rs::spend_at's broadcast loop: remove
    /// the bearer from OUR ledger if we currently hold it. Does not
    /// touch our own spent set (we didn't spend it, our peer did).
    pub fn apply_spent_notify(&mut self, bearer: &str) {
        self.node.ledger.remove(bearer);
    }

    /// Local spend: mirrors network.rs::spend_at's spender-side
    /// effect only (marks spent, removes from own ledger). Does NOT
    /// broadcast -- the caller (networking layer) is responsible for
    /// sending SpentNotify to every currently-connected peer after
    /// this returns Ok, mirroring network.rs's
    /// `targets = connected_to(nn) u {nn}` (the "u {nn}" self-removal
    /// is exactly this function's ledger.remove).
    pub fn local_spend(&mut self, bearer: &str) -> Result<(), StateError> {
        if !self.node.ledger.contains(bearer) {
            return Err(StateError(format!(
                "{} does not hold {bearer}, cannot spend",
                self.node.node_id
            )));
        }
        self.node.spent.insert(bearer.to_string());
        self.node.ledger.remove(bearer);
        Ok(())
    }

    pub fn ledger_sorted(&self) -> Vec<String> {
        let mut v: Vec<String> = self.node.ledger.iter().cloned().collect();
        v.sort();
        v
    }

    pub fn spent_sorted(&self) -> Vec<String> {
        let mut v: Vec<String> = self.node.spent.iter().cloned().collect();
        v.sort();
        v
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn set(items: &[&str]) -> HashSet<String> {
        items.iter().map(|s| s.to_string()).collect()
    }

    #[test]
    fn link_up_merge_matches_network_rs_semantics() {
        // Mirrors network.rs's own link_up test shape: N1 holds b1,
        // peer (standing in for N2) holds b2, neither has spent
        // anything -- merge should yield both bearers on our side.
        let mut n1 = NodeShared::new("N1");
        n1.node.ledger.insert("b1".to_string());

        let peer_ledger = set(&["b2"]);
        let peer_spent = set(&[]);
        let merged = n1.compute_link_up_merge(&peer_ledger, &peer_spent);
        assert_eq!(merged, set(&["b1", "b2"]));

        n1.apply_link_up("N2", merged);
        assert_eq!(n1.node.ledger, set(&["b1", "b2"]));
        assert!(n1.is_linked("N2"));
    }

    #[test]
    fn link_up_merge_excludes_bearers_either_side_already_spent() {
        // Mirrors network.rs's FIX comment: a bearer already spent by
        // EITHER side must not reappear in the merged ledger, even if
        // it's still sitting in the other side's (stale) ledger.
        let mut n1 = NodeShared::new("N1");
        n1.node.ledger.insert("b1".to_string());
        n1.node.spent.insert("b1".to_string()); // N1 already spent b1

        // Peer's ledger is stale -- still shows b1 as valid.
        let peer_ledger = set(&["b1", "b2"]);
        let peer_spent = set(&[]);
        let merged = n1.compute_link_up_merge(&peer_ledger, &peer_spent);

        assert_eq!(merged, set(&["b2"]), "b1 must be burned, not merged back in");
    }

    #[test]
    fn link_up_merge_never_writes_to_spent() {
        let mut n1 = NodeShared::new("N1");
        n1.node.ledger.insert("b1".to_string());
        let before_spent = n1.node.spent.clone();

        let merged = n1.compute_link_up_merge(&set(&["b2"]), &set(&["b2"]));
        n1.apply_link_up("N2", merged);

        assert_eq!(n1.node.spent, before_spent, "spent must only grow via local_spend");
    }

    #[test]
    fn propagate_deliverable_excludes_own_spent_and_own_ledger() {
        let mut n1 = NodeShared::new("N1");
        n1.node.spent.insert("b1".to_string()); // already spent, must not re-receive
        n1.node.ledger.insert("b3".to_string()); // already held, must not duplicate

        let peer_ledger = set(&["b1", "b2", "b3"]);
        let deliverable = n1.compute_propagate_deliverable(&peer_ledger);

        assert_eq!(deliverable, set(&["b2"]));
    }

    #[test]
    fn apply_propagate_deliverable_extends_ledger() {
        let mut n1 = NodeShared::new("N1");
        n1.apply_propagate_deliverable(set(&["b1", "b2"]));
        assert_eq!(n1.node.ledger, set(&["b1", "b2"]));
    }

    #[test]
    fn local_spend_rejects_bearer_not_held() {
        let mut n1 = NodeShared::new("N1");
        let result = n1.local_spend("b1");
        assert!(result.is_err());
    }

    #[test]
    fn local_spend_marks_spent_and_removes_from_own_ledger() {
        let mut n1 = NodeShared::new("N1");
        n1.node.ledger.insert("b1".to_string());
        n1.local_spend("b1").unwrap();

        assert!(n1.node.spent.contains("b1"));
        assert!(!n1.node.ledger.contains("b1"));
    }

    #[test]
    fn apply_spent_notify_removes_but_does_not_mark_spent() {
        // A peer told us THEY spent b1 -- we should stop holding it,
        // but WE did not spend it, so our own spent set is untouched.
        let mut n1 = NodeShared::new("N1");
        n1.node.ledger.insert("b1".to_string());
        n1.apply_spent_notify("b1");

        assert!(!n1.node.ledger.contains("b1"));
        assert!(!n1.node.spent.contains("b1"));
    }

    #[test]
    fn connected_peers_only_lists_links_currently_up() {
        let mut n1 = NodeShared::new("N1");
        n1.set_link("N2", true);
        n1.set_link("N3", false);
        assert_eq!(n1.connected_peers(), vec!["N2".to_string()]);
    }

    #[test]
    fn unknown_peer_defaults_to_not_linked() {
        let n1 = NodeShared::new("N1");
        assert!(!n1.is_linked("N2"));
    }

    #[test]
    fn shared_state_is_usable_across_threads() {
        use std::thread;
        let shared = NodeShared::new_shared("N1");
        {
            let mut guard = shared.lock().unwrap();
            guard.node.ledger.insert("b1".to_string());
        }
        let shared_clone = Arc::clone(&shared);
        let handle = thread::spawn(move || {
            let mut guard = shared_clone.lock().unwrap();
            guard.local_spend("b1").unwrap();
        });
        handle.join().unwrap();

        let guard = shared.lock().unwrap();
        assert!(guard.node.spent.contains("b1"));
    }
}
