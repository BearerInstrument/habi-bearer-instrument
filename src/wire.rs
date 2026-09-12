//! Hand-rolled wire protocol for node-to-node and admin communication.
//!
//! std-only, matching the crate's existing zero-external-dependency
//! design (see Cargo.toml). Messages are single-line, pipe-delimited
//! text, newline-terminated.
//!
//! LinkUpHello/LinkUpAck carry the sender's full ledger+spent sets --
//! unlike the centralized network.rs::link_up (which has direct
//! access to both sides' Node structs), a distributed node must
//! actually receive its peer's state before it can compute the same
//! symmetric merge: merged = (ledgers[n] u ledgers[m]) \ (spent[n] u spent[m]).
//! Both sides compute this independently from the same two input
//! sets, so they converge on an identical result without either side
//! trusting the other's computation -- only the other's raw data.

use std::fmt;

#[derive(Debug)]
pub struct WireError(pub String);

impl fmt::Display for WireError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}
impl std::error::Error for WireError {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PeerMessage {
    LinkUpHello {
        from: String,
        ledger: Vec<String>,
        spent: Vec<String>,
    },
    LinkUpAck {
        from: String,
        ledger: Vec<String>,
        spent: Vec<String>,
    },
    LinkDown {
        from: String,
    },
    PropagateRequest {
        from: String,
    },
    PropagateReply {
        from: String,
        bearers: Vec<String>,
    },
    SpentNotify {
        from: String,
        bearer: String,
    },
    /// Used by a Conversion Day coordinator to gather a node's raw
    /// state directly, bypassing the pairwise-link requirement that
    /// gates LinkUp/Propagate -- mirrors conversion_day.rs's
    /// centralized model, which has direct access to every node's
    /// state regardless of link topology (the "designated
    /// reconciliation authority", not pairwise gossip).
    StatusRequest {
        from: String,
    },
    StatusReply {
        from: String,
        ledger: Vec<String>,
        spent: Vec<String>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AdminMessage {
    LinkUp { peer: String },
    LinkDown { peer: String },
    Propagate { peer: String },
    SpendAt { bearer: String },
    Status,
    /// TEST/BOOTSTRAP ONLY: directly inserts a bearer into this
    /// node's ledger with no provenance check. Real bearer issuance
    /// is out of scope for this stage -- this exists solely so a
    /// distributed deployment can be smoke-tested end-to-end without
    /// a real issuance/mint mechanism yet existing. Never intended
    /// as a production operation.
    Seed { bearer: String },
    /// Triggers this node to act as Conversion Day coordinator:
    /// gathers StatusReply from every peer in its peers file (plus
    /// its own local state), runs compute_conversion_day, and on
    /// success broadcasts SpentNotify for every globally-spent
    /// bearer to every node (itself included). Mirrors
    /// conversion_day.rs::run_conversion_day's semantics exactly,
    /// over the network.
    ConversionDay,
}

/// Reply sent back to an admin client after processing an AdminMessage.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AdminReply {
    Ok,
    Error { detail: String },
    StatusReport {
        node_id: String,
        ledger: Vec<String>,
        spent: Vec<String>,
        links: Vec<String>,
    },
}

fn escape(s: &str) -> String {
    s.replace('\\', "\\\\").replace('|', "\\|").replace(',', "\\,")
}

fn unescape(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let mut chars = s.chars();
    while let Some(c) = chars.next() {
        if c == '\\' {
            match chars.next() {
                Some('\\') => out.push('\\'),
                Some('|') => out.push('|'),
                Some(',') => out.push(','),
                Some(other) => {
                    out.push('\\');
                    out.push(other);
                }
                None => out.push('\\'),
            }
        } else {
            out.push(c);
        }
    }
    out
}

// Splits on top-level, unescaped '|' only. Returns each field's RAW
// text (still escaped) -- callers that need a plain scalar value
// (from/bearer/peer names) must call unescape() themselves; callers
// that need a list (ledger/spent/bearers/links) must call
// decode_list() themselves, which does its own comma-aware unescape.
// Un-escaping here (at the '|' layer) before those callers get a
// chance to interpret escaped commas would destroy the very
// escaping decode_list depends on -- that was the original bug.
fn split_fields(line: &str) -> Vec<String> {
    let mut fields = Vec::new();
    let mut current = String::new();
    let mut chars = line.chars().peekable();
    while let Some(c) = chars.next() {
        if c == '\\' {
            current.push(c);
            if let Some(&next) = chars.peek() {
                current.push(next);
                chars.next();
            }
        } else if c == '|' {
            fields.push(current.clone());
            current.clear();
        } else {
            current.push(c);
        }
    }
    fields.push(current);
    fields
}

fn encode_list(items: &[String]) -> String {
    items.iter().map(|s| escape(s)).collect::<Vec<_>>().join(",")
}

fn decode_list(s: &str) -> Vec<String> {
    if s.is_empty() {
        Vec::new()
    } else {
        let mut items = Vec::new();
        let mut current = String::new();
        let mut chars = s.chars().peekable();
        while let Some(c) = chars.next() {
            if c == '\\' {
                current.push(c);
                if let Some(&next) = chars.peek() {
                    current.push(next);
                    chars.next();
                }
            } else if c == ',' {
                items.push(unescape(&current));
                current.clear();
            } else {
                current.push(c);
            }
        }
        items.push(unescape(&current));
        items
    }
}

impl PeerMessage {
    pub fn encode(&self) -> String {
        match self {
            PeerMessage::LinkUpHello { from, ledger, spent } => format!(
                "LINK_UP_HELLO|{}|{}|{}",
                escape(from),
                encode_list(ledger),
                encode_list(spent)
            ),
            PeerMessage::LinkUpAck { from, ledger, spent } => format!(
                "LINK_UP_ACK|{}|{}|{}",
                escape(from),
                encode_list(ledger),
                encode_list(spent)
            ),
            PeerMessage::LinkDown { from } => format!("LINK_DOWN|{}", escape(from)),
            PeerMessage::PropagateRequest { from } => {
                format!("PROPAGATE_REQUEST|{}", escape(from))
            }
            PeerMessage::PropagateReply { from, bearers } => {
                format!("PROPAGATE_REPLY|{}|{}", escape(from), encode_list(bearers))
            }
            PeerMessage::SpentNotify { from, bearer } => {
                format!("SPENT_NOTIFY|{}|{}", escape(from), escape(bearer))
            }
            PeerMessage::StatusRequest { from } => {
                format!("STATUS_REQUEST|{}", escape(from))
            }
            PeerMessage::StatusReply { from, ledger, spent } => format!(
                "STATUS_REPLY|{}|{}|{}",
                escape(from),
                encode_list(ledger),
                encode_list(spent)
            ),
        }
    }

    pub fn decode(line: &str) -> Result<Self, WireError> {
        let fields = split_fields(line.trim_end_matches('\n'));
        match fields.first().map(|s| s.as_str()) {
            Some("LINK_UP_HELLO") if fields.len() == 4 => Ok(PeerMessage::LinkUpHello {
                from: unescape(&fields[1]),
                ledger: decode_list(&fields[2]),
                spent: decode_list(&fields[3]),
            }),
            Some("LINK_UP_ACK") if fields.len() == 4 => Ok(PeerMessage::LinkUpAck {
                from: unescape(&fields[1]),
                ledger: decode_list(&fields[2]),
                spent: decode_list(&fields[3]),
            }),
            Some("LINK_DOWN") if fields.len() == 2 => Ok(PeerMessage::LinkDown {
                from: unescape(&fields[1]),
            }),
            Some("PROPAGATE_REQUEST") if fields.len() == 2 => {
                Ok(PeerMessage::PropagateRequest { from: unescape(&fields[1]) })
            }
            Some("PROPAGATE_REPLY") if fields.len() == 3 => Ok(PeerMessage::PropagateReply {
                from: unescape(&fields[1]),
                bearers: decode_list(&fields[2]),
            }),
            Some("SPENT_NOTIFY") if fields.len() == 3 => Ok(PeerMessage::SpentNotify {
                from: unescape(&fields[1]),
                bearer: unescape(&fields[2]),
            }),
            Some("STATUS_REQUEST") if fields.len() == 2 => Ok(PeerMessage::StatusRequest {
                from: unescape(&fields[1]),
            }),
            Some("STATUS_REPLY") if fields.len() == 4 => Ok(PeerMessage::StatusReply {
                from: unescape(&fields[1]),
                ledger: decode_list(&fields[2]),
                spent: decode_list(&fields[3]),
            }),
            _ => Err(WireError(format!("unrecognized or malformed message: {line:?}"))),
        }
    }
}

impl AdminMessage {
    pub fn encode(&self) -> String {
        match self {
            AdminMessage::LinkUp { peer } => format!("ADMIN_LINK_UP|{}", escape(peer)),
            AdminMessage::LinkDown { peer } => format!("ADMIN_LINK_DOWN|{}", escape(peer)),
            AdminMessage::Propagate { peer } => format!("ADMIN_PROPAGATE|{}", escape(peer)),
            AdminMessage::SpendAt { bearer } => format!("ADMIN_SPEND_AT|{}", escape(bearer)),
            AdminMessage::Status => "ADMIN_STATUS".to_string(),
            AdminMessage::Seed { bearer } => format!("ADMIN_SEED|{}", escape(bearer)),
            AdminMessage::ConversionDay => "ADMIN_CONVERSION_DAY".to_string(),
        }
    }

    pub fn decode(line: &str) -> Result<Self, WireError> {
        let fields = split_fields(line.trim_end_matches('\n'));
        match fields.first().map(|s| s.as_str()) {
            Some("ADMIN_LINK_UP") if fields.len() == 2 => {
                Ok(AdminMessage::LinkUp { peer: unescape(&fields[1]) })
            }
            Some("ADMIN_LINK_DOWN") if fields.len() == 2 => {
                Ok(AdminMessage::LinkDown { peer: unescape(&fields[1]) })
            }
            Some("ADMIN_PROPAGATE") if fields.len() == 2 => {
                Ok(AdminMessage::Propagate { peer: unescape(&fields[1]) })
            }
            Some("ADMIN_SPEND_AT") if fields.len() == 2 => {
                Ok(AdminMessage::SpendAt { bearer: unescape(&fields[1]) })
            }
            Some("ADMIN_STATUS") if fields.len() == 1 => Ok(AdminMessage::Status),
            Some("ADMIN_SEED") if fields.len() == 2 => {
                Ok(AdminMessage::Seed { bearer: unescape(&fields[1]) })
            }
            Some("ADMIN_CONVERSION_DAY") if fields.len() == 1 => Ok(AdminMessage::ConversionDay),
            _ => Err(WireError(format!("unrecognized or malformed admin message: {line:?}"))),
        }
    }
}

impl AdminReply {
    pub fn encode(&self) -> String {
        match self {
            AdminReply::Ok => "REPLY_OK".to_string(),
            AdminReply::Error { detail } => format!("REPLY_ERROR|{}", escape(detail)),
            AdminReply::StatusReport { node_id, ledger, spent, links } => format!(
                "REPLY_STATUS|{}|{}|{}|{}",
                escape(node_id),
                encode_list(ledger),
                encode_list(spent),
                encode_list(links)
            ),
        }
    }

    pub fn decode(line: &str) -> Result<Self, WireError> {
        let fields = split_fields(line.trim_end_matches('\n'));
        match fields.first().map(|s| s.as_str()) {
            Some("REPLY_OK") if fields.len() == 1 => Ok(AdminReply::Ok),
            Some("REPLY_ERROR") if fields.len() == 2 => {
                Ok(AdminReply::Error { detail: unescape(&fields[1]) })
            }
            Some("REPLY_STATUS") if fields.len() == 5 => Ok(AdminReply::StatusReport {
                node_id: unescape(&fields[1]),
                ledger: decode_list(&fields[2]),
                spent: decode_list(&fields[3]),
                links: decode_list(&fields[4]),
            }),
            _ => Err(WireError(format!("unrecognized or malformed reply: {line:?}"))),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn peer_message_roundtrip() {
        let msgs = vec![
            PeerMessage::LinkUpHello {
                from: "N1".into(),
                ledger: vec!["b1".into(), "b2".into()],
                spent: vec![],
            },
            PeerMessage::LinkUpAck {
                from: "N2".into(),
                ledger: vec![],
                spent: vec!["b1".into()],
            },
            PeerMessage::LinkDown { from: "N3".into() },
            PeerMessage::PropagateRequest { from: "N1".into() },
            PeerMessage::PropagateReply {
                from: "N1".into(),
                bearers: vec!["b1".into(), "b2".into()],
            },
            PeerMessage::PropagateReply { from: "N1".into(), bearers: vec![] },
            PeerMessage::SpentNotify { from: "N1".into(), bearer: "b1".into() },
            PeerMessage::StatusRequest { from: "N1".into() },
            PeerMessage::StatusReply {
                from: "N1".into(),
                ledger: vec!["b1".into()],
                spent: vec![],
            },
        ];
        for m in msgs {
            let encoded = m.encode();
            let decoded = PeerMessage::decode(&encoded).unwrap();
            assert_eq!(m, decoded, "roundtrip failed for {encoded:?}");
        }
    }

    #[test]
    fn admin_message_roundtrip() {
        let msgs = vec![
            AdminMessage::LinkUp { peer: "N2".into() },
            AdminMessage::LinkDown { peer: "N2".into() },
            AdminMessage::Propagate { peer: "N2".into() },
            AdminMessage::SpendAt { bearer: "b1".into() },
            AdminMessage::Status,
            AdminMessage::Seed { bearer: "b1".into() },
            AdminMessage::ConversionDay,
        ];
        for m in msgs {
            let encoded = m.encode();
            let decoded = AdminMessage::decode(&encoded).unwrap();
            assert_eq!(m, decoded, "roundtrip failed for {encoded:?}");
        }
    }

    #[test]
    fn admin_reply_roundtrip() {
        let msgs = vec![
            AdminReply::Ok,
            AdminReply::Error { detail: "no link N2-N3".into() },
            AdminReply::StatusReport {
                node_id: "N1".into(),
                ledger: vec!["b1".into()],
                spent: vec![],
                links: vec!["N2".into(), "N3".into()],
            },
        ];
        for m in msgs {
            let encoded = m.encode();
            let decoded = AdminReply::decode(&encoded).unwrap();
            assert_eq!(m, decoded, "roundtrip failed for {encoded:?}");
        }
    }

    #[test]
    fn escaping_handles_pipe_backslash_and_comma_in_bearer_names() {
        let m = PeerMessage::LinkUpHello {
            from: "N1".into(),
            ledger: vec!["weird|bearer\\name,with,commas".into(), "b2".into()],
            spent: vec![],
        };
        let encoded = m.encode();
        let decoded = PeerMessage::decode(&encoded).unwrap();
        assert_eq!(m, decoded);
    }

    #[test]
    fn decode_rejects_malformed_input() {
        assert!(PeerMessage::decode("NOT_A_REAL_MESSAGE").is_err());
        assert!(PeerMessage::decode("LINK_UP_HELLO").is_err());
        assert!(AdminMessage::decode("").is_err());
        assert!(AdminReply::decode("GARBAGE").is_err());
    }

    #[test]
    fn empty_ledger_and_spent_roundtrip_as_empty_not_single_blank_item() {
        let m = PeerMessage::LinkUpHello {
            from: "N1".into(),
            ledger: vec![],
            spent: vec![],
        };
        let encoded = m.encode();
        let decoded = PeerMessage::decode(&encoded).unwrap();
        if let PeerMessage::LinkUpHello { ledger, spent, .. } = decoded {
            assert_eq!(ledger, Vec::<String>::new());
            assert_eq!(spent, Vec::<String>::new());
        } else {
            panic!("wrong variant decoded");
        }
    }
}
