//! Pure, socket-free message dispatch logic for the distributed
//! habi_node binary. Every function here takes an already-parsed
//! PeerMessage and a SharedState, and returns an already-typed
//! reply (or None) -- no TcpStream, no I/O. The habi_node binary is
//! a thin wrapper that does socket read/write and calls straight
//! into these functions, so all the actual protocol logic is
//! unit-testable without real networking.

use crate::shared_state::{SharedState, StateError};
use crate::wire::PeerMessage;
use std::collections::HashSet;

fn to_set(items: Vec<String>) -> HashSet<String> {
    items.into_iter().collect()
}

/// Handles a message that arrived UNSOLICITED on our peer listener
/// (i.e. someone else initiated this connection to us). Returns the
/// reply to write back, if the protocol calls for one.
pub fn handle_incoming_peer_message(
    shared: &SharedState,
    msg: PeerMessage,
) -> Result<Option<PeerMessage>, StateError> {
    let mut guard = shared.lock().unwrap();
    match msg {
        PeerMessage::LinkUpHello { from, ledger, spent } => {
            let peer_ledger = to_set(ledger);
            let peer_spent = to_set(spent);
            // Capture OUR original state before applying the merge --
            // the peer needs these exact pre-merge values (not our
            // post-merge ledger) to compute the identical merge on
            // their side from the same two input sets.
            let own_ledger = guard.ledger_sorted();
            let own_spent = guard.spent_sorted();

            let merged = guard.compute_link_up_merge(&peer_ledger, &peer_spent);
            guard.apply_link_up(&from, merged);

            let self_id = guard.node.node_id.clone();
            Ok(Some(PeerMessage::LinkUpAck {
                from: self_id,
                ledger: own_ledger,
                spent: own_spent,
            }))
        }
        PeerMessage::LinkDown { from } => {
            guard.apply_link_down(&from);
            Ok(None)
        }
        PeerMessage::PropagateRequest { from } => {
            // FIX: network.rs::propagate requires network[src][dst] = TRUE
            // as a precondition. The original version replied
            // unconditionally regardless of link state -- this closes
            // that gap by rejecting a propagate request from a peer
            // we don't currently have an active link to.
            if !guard.is_linked(&from) {
                return Err(StateError(format!(
                    "no link to {from}, cannot propagate"
                )));
            }
            let self_id = guard.node.node_id.clone();
            let bearers = guard.ledger_sorted();
            Ok(Some(PeerMessage::PropagateReply {
                from: self_id,
                bearers,
            }))
        }
        PeerMessage::SpentNotify { from: _, bearer } => {
            guard.apply_spent_notify(&bearer);
            Ok(None)
        }
        PeerMessage::StatusRequest { from: _ } => {
            let self_id = guard.node.node_id.clone();
            let ledger = guard.ledger_sorted();
            let spent = guard.spent_sorted();
            Ok(Some(PeerMessage::StatusReply {
                from: self_id,
                ledger,
                spent,
            }))
        }
        PeerMessage::LinkUpAck { .. }
        | PeerMessage::PropagateReply { .. }
        | PeerMessage::StatusReply { .. } => {
            Err(StateError(
                "LinkUpAck/PropagateReply/StatusReply must only arrive as a \
                 direct reply on a connection we initiated, not as an \
                 unsolicited incoming message"
                    .to_string(),
            ))
        }
    }
}

/// Applies a LinkUpAck we received in reply to a LinkUpHello we sent.
/// Computes the same merge formula the peer already applied on their
/// side, from the same two original input sets, so both sides
/// converge on an identical merged ledger.
pub fn apply_link_up_reply(shared: &SharedState, reply: PeerMessage) -> Result<(), StateError> {
    match reply {
        PeerMessage::LinkUpAck { from, ledger, spent } => {
            let peer_ledger = to_set(ledger);
            let peer_spent = to_set(spent);
            let mut guard = shared.lock().unwrap();
            let merged = guard.compute_link_up_merge(&peer_ledger, &peer_spent);
            guard.apply_link_up(&from, merged);
            Ok(())
        }
        other => Err(StateError(format!(
            "expected LinkUpAck, got {other:?}"
        ))),
    }
}

/// Applies a PropagateReply we received in reply to a
/// PropagateRequest we sent. Filters the peer's raw ledger against
/// our own spent+ledger locally, since only we have the data needed
/// to compute the correct deliverable set.
pub fn apply_propagate_reply(shared: &SharedState, reply: PeerMessage) -> Result<(), StateError> {
    match reply {
        PeerMessage::PropagateReply { bearers, .. } => {
            let peer_ledger = to_set(bearers);
            let mut guard = shared.lock().unwrap();
            let deliverable = guard.compute_propagate_deliverable(&peer_ledger);
            guard.apply_propagate_deliverable(deliverable);
            Ok(())
        }
        other => Err(StateError(format!(
            "expected PropagateReply, got {other:?}"
        ))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::shared_state::NodeShared;

    fn set(items: &[&str]) -> Vec<String> {
        items.iter().map(|s| s.to_string()).collect()
    }

    #[test]
    fn link_up_hello_computes_merge_and_replies_with_own_original_state() {
        let shared = NodeShared::new_shared("N1");
        {
            let mut g = shared.lock().unwrap();
            g.node.ledger.insert("b1".to_string());
        }

        let hello = PeerMessage::LinkUpHello {
            from: "N2".to_string(),
            ledger: set(&["b2"]),
            spent: set(&[]),
        };
        let reply = handle_incoming_peer_message(&shared, hello).unwrap().unwrap();

        match reply {
            PeerMessage::LinkUpAck { from, ledger, spent } => {
                assert_eq!(from, "N1");
                assert_eq!(ledger, set(&["b1"]), "must reply with ORIGINAL pre-merge ledger");
                assert_eq!(spent, Vec::<String>::new());
            }
            other => panic!("expected LinkUpAck, got {other:?}"),
        }

        let g = shared.lock().unwrap();
        assert_eq!(g.node.ledger, ["b1", "b2"].iter().map(|s| s.to_string()).collect());
        assert!(g.is_linked("N2"));
    }

    #[test]
    fn two_nodes_converge_on_identical_merge_via_hello_and_ack_roundtrip() {
        // Simulates the full LinkUp handshake between two NodeShared
        // instances without any sockets: N1 sends Hello, N2's handler
        // produces an Ack, N1 applies that Ack. Both must end up with
        // the same ledger.
        let n1 = NodeShared::new_shared("N1");
        {
            let mut g = n1.lock().unwrap();
            g.node.ledger.insert("b1".to_string());
        }
        let n2 = NodeShared::new_shared("N2");
        {
            let mut g = n2.lock().unwrap();
            g.node.ledger.insert("b2".to_string());
        }

        let n1_original_ledger = n1.lock().unwrap().ledger_sorted();
        let n1_original_spent = n1.lock().unwrap().spent_sorted();
        let hello = PeerMessage::LinkUpHello {
            from: "N1".to_string(),
            ledger: n1_original_ledger,
            spent: n1_original_spent,
        };

        let ack = handle_incoming_peer_message(&n2, hello).unwrap().unwrap();
        apply_link_up_reply(&n1, ack).unwrap();

        let n1_final = n1.lock().unwrap().ledger_sorted();
        let n2_final = n2.lock().unwrap().ledger_sorted();
        assert_eq!(n1_final, n2_final, "both sides must converge on the same merged ledger");
        assert_eq!(n1_final, vec!["b1".to_string(), "b2".to_string()]);
    }

    #[test]
    fn link_up_excludes_already_spent_bearer_across_the_full_handshake() {
        // Same convergence test, but N1 already spent b1 and N2's
        // ledger is stale (still shows b1). The FIX semantics must
        // survive the full round trip, not just the isolated
        // compute_link_up_merge call already covered in shared_state.
        let n1 = NodeShared::new_shared("N1");
        {
            let mut g = n1.lock().unwrap();
            g.node.ledger.insert("b1".to_string());
            g.local_spend("b1").unwrap(); // b1 now spent, removed from N1's own ledger
        }
        let n2 = NodeShared::new_shared("N2");
        {
            let mut g = n2.lock().unwrap();
            g.node.ledger.insert("b1".to_string()); // stale -- doesn't know b1 was spent
            g.node.ledger.insert("b2".to_string());
        }

        let n1_original_ledger = n1.lock().unwrap().ledger_sorted();
        let n1_original_spent = n1.lock().unwrap().spent_sorted();
        let hello = PeerMessage::LinkUpHello {
            from: "N1".to_string(),
            ledger: n1_original_ledger,
            spent: n1_original_spent,
        };

        let ack = handle_incoming_peer_message(&n2, hello).unwrap().unwrap();
        apply_link_up_reply(&n1, ack).unwrap();

        let n1_final = n1.lock().unwrap().ledger_sorted();
        let n2_final = n2.lock().unwrap().ledger_sorted();
        assert_eq!(n1_final, n2_final);
        assert_eq!(n1_final, vec!["b2".to_string()], "b1 must be burned on both sides, not merged back in");
    }

    #[test]
    fn propagate_request_replies_with_full_raw_ledger_unfiltered() {
        let src = NodeShared::new_shared("N2");
        {
            let mut g = src.lock().unwrap();
            g.node.ledger.insert("b1".to_string());
            g.node.ledger.insert("b2".to_string());
            // Required precondition since the link-check fix: mirrors
            // network.rs::propagate's network[src][dst] = TRUE guard.
            g.set_link("N1", true);
        }
        let req = PeerMessage::PropagateRequest { from: "N1".to_string() };
        let reply = handle_incoming_peer_message(&src, req).unwrap().unwrap();

        match reply {
            PeerMessage::PropagateReply { from, bearers } => {
                assert_eq!(from, "N2");
                let mut sorted = bearers;
                sorted.sort();
                assert_eq!(sorted, vec!["b1".to_string(), "b2".to_string()],
                    "reply must carry the FULL raw ledger, unfiltered -- requester filters locally");
            }
            other => panic!("expected PropagateReply, got {other:?}"),
        }
    }

    #[test]
    fn propagate_reply_is_filtered_locally_by_requester_not_by_source() {
        let dst = NodeShared::new_shared("N1");
        {
            let mut g = dst.lock().unwrap();
            g.node.spent.insert("b1".to_string()); // already spent -- must not re-receive
            g.node.ledger.insert("b3".to_string()); // already held -- must not duplicate
        }

        let reply = PeerMessage::PropagateReply {
            from: "N2".to_string(),
            bearers: set(&["b1", "b2", "b3"]), // source's raw, unfiltered ledger
        };
        apply_propagate_reply(&dst, reply).unwrap();

        let g = dst.lock().unwrap();
        assert_eq!(g.node.ledger, ["b2", "b3"].iter().map(|s| s.to_string()).collect());
    }

    #[test]
    fn propagate_request_rejected_when_not_linked() {
        // FIX regression test: mirrors network.rs::propagate's
        // network[src][dst] = TRUE precondition. No link set up here.
        let src = NodeShared::new_shared("N2");
        {
            let mut g = src.lock().unwrap();
            g.node.ledger.insert("b1".to_string());
        }
        let req = PeerMessage::PropagateRequest { from: "N1".to_string() };
        let result = handle_incoming_peer_message(&src, req);
        assert!(result.is_err(), "propagate from an unlinked peer must be rejected");
    }

    #[test]
    fn link_down_updates_local_link_state_no_reply() {
        let n1 = NodeShared::new_shared("N1");
        {
            let mut g = n1.lock().unwrap();
            g.set_link("N2", true);
        }
        let msg = PeerMessage::LinkDown { from: "N2".to_string() };
        let reply = handle_incoming_peer_message(&n1, msg).unwrap();
        assert!(reply.is_none());
        assert!(!n1.lock().unwrap().is_linked("N2"));
    }

    #[test]
    fn spent_notify_removes_bearer_no_reply_and_does_not_mark_spent() {
        let n1 = NodeShared::new_shared("N1");
        {
            let mut g = n1.lock().unwrap();
            g.node.ledger.insert("b1".to_string());
        }
        let msg = PeerMessage::SpentNotify {
            from: "N2".to_string(),
            bearer: "b1".to_string(),
        };
        let reply = handle_incoming_peer_message(&n1, msg).unwrap();
        assert!(reply.is_none());

        let g = n1.lock().unwrap();
        assert!(!g.node.ledger.contains("b1"));
        assert!(!g.node.spent.contains("b1"), "receiving side did not spend it, only the sender did");
    }

    #[test]
    fn unsolicited_ack_or_reply_is_rejected() {
        let n1 = NodeShared::new_shared("N1");
        let bad_ack = PeerMessage::LinkUpAck {
            from: "N2".to_string(),
            ledger: vec![],
            spent: vec![],
        };
        assert!(handle_incoming_peer_message(&n1, bad_ack).is_err());

        let bad_reply = PeerMessage::PropagateReply {
            from: "N2".to_string(),
            bearers: vec![],
        };
        assert!(handle_incoming_peer_message(&n1, bad_reply).is_err());

        let bad_status_reply = PeerMessage::StatusReply {
            from: "N2".to_string(),
            ledger: vec![],
            spent: vec![],
        };
        assert!(handle_incoming_peer_message(&n1, bad_status_reply).is_err());
    }

    #[test]
    fn status_request_replies_with_own_ledger_and_spent() {
        let n1 = NodeShared::new_shared("N1");
        {
            let mut g = n1.lock().unwrap();
            g.node.ledger.insert("b1".to_string());
            g.node.spent.insert("b2".to_string());
        }
        let req = PeerMessage::StatusRequest { from: "coordinator".to_string() };
        let reply = handle_incoming_peer_message(&n1, req).unwrap().unwrap();
        match reply {
            PeerMessage::StatusReply { from, ledger, spent } => {
                assert_eq!(from, "N1");
                assert_eq!(ledger, vec!["b1".to_string()]);
                assert_eq!(spent, vec!["b2".to_string()]);
            }
            other => panic!("expected StatusReply, got {other:?}"),
        }
    }

    #[test]
    fn apply_link_up_reply_rejects_wrong_message_type() {
        let n1 = NodeShared::new_shared("N1");
        let wrong = PeerMessage::LinkDown { from: "N2".to_string() };
        assert!(apply_link_up_reply(&n1, wrong).is_err());
    }

    #[test]
    fn apply_propagate_reply_rejects_wrong_message_type() {
        let n1 = NodeShared::new_shared("N1");
        let wrong = PeerMessage::LinkDown { from: "N2".to_string() };
        assert!(apply_propagate_reply(&n1, wrong).is_err());
    }
}
