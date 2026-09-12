//! Node-state persistence: save/load a Node's ledger and spent sets
//! to/from a plain text file, so state survives a process restart.
//!
//! std-only. Uses write-to-temp-then-rename so a crash mid-write
//! never leaves a corrupted state file -- the rename is atomic on
//! the same filesystem, so readers always see either the old
//! complete file or the new complete file, never a partial one.

use crate::node::Node;
use std::collections::HashSet;
use std::fmt;
use std::fs;
use std::io::{BufRead, BufReader, Write};
use std::path::Path;

#[derive(Debug)]
pub struct PersistenceError(pub String);

impl fmt::Display for PersistenceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}
impl std::error::Error for PersistenceError {}

impl From<std::io::Error> for PersistenceError {
    fn from(e: std::io::Error) -> Self {
        PersistenceError(format!("io error: {e}"))
    }
}

/// Save a node's ledger/spent state to `path`, atomically.
pub fn save_node_state(node: &Node, path: &Path) -> Result<(), PersistenceError> {
    let tmp_path = path.with_extension("tmp");
    {
        let mut f = fs::File::create(&tmp_path)?;
        writeln!(f, "NODE_ID|{}", node.node_id)?;
        let mut ledger: Vec<&String> = node.ledger.iter().collect();
        ledger.sort();
        for b in ledger {
            writeln!(f, "LEDGER|{b}")?;
        }
        let mut spent: Vec<&String> = node.spent.iter().collect();
        spent.sort();
        for b in spent {
            writeln!(f, "SPENT|{b}")?;
        }
        f.sync_all()?;
    }
    fs::rename(&tmp_path, path)?;
    Ok(())
}

/// Load a node's ledger/spent state from `path`. Returns Ok(None) if
/// the file does not exist yet (fresh node, nothing to restore).
pub fn load_node_state(path: &Path) -> Result<Option<Node>, PersistenceError> {
    if !path.exists() {
        return Ok(None);
    }
    let f = fs::File::open(path)?;
    let reader = BufReader::new(f);

    let mut node_id: Option<String> = None;
    let mut ledger: HashSet<String> = HashSet::new();
    let mut spent: HashSet<String> = HashSet::new();

    for line in reader.lines() {
        let line = line?;
        if line.is_empty() {
            continue;
        }
        let mut parts = line.splitn(2, '|');
        let tag = parts.next().unwrap_or("");
        let value = parts.next().unwrap_or("");
        match tag {
            "NODE_ID" => node_id = Some(value.to_string()),
            "LEDGER" => {
                ledger.insert(value.to_string());
            }
            "SPENT" => {
                spent.insert(value.to_string());
            }
            other => {
                return Err(PersistenceError(format!(
                    "unrecognized line tag {other:?} in {path:?}"
                )))
            }
        }
    }

    let node_id = node_id.ok_or_else(|| {
        PersistenceError(format!("state file {path:?} missing NODE_ID line"))
    })?;

    Ok(Some(Node {
        node_id,
        ledger,
        spent,
    }))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::env;

    fn temp_path(name: &str) -> std::path::PathBuf {
        let mut p = env::temp_dir();
        p.push(format!("habi_persistence_test_{name}_{}.state", std::process::id()));
        p
    }

    #[test]
    fn save_then_load_roundtrips_exactly() {
        let path = temp_path("roundtrip");
        let mut node = Node::new("N1");
        node.ledger.insert("b1".into());
        node.ledger.insert("b2".into());
        node.spent.insert("b1".into());

        save_node_state(&node, &path).unwrap();
        let loaded = load_node_state(&path).unwrap().unwrap();

        assert_eq!(loaded.node_id, node.node_id);
        assert_eq!(loaded.ledger, node.ledger);
        assert_eq!(loaded.spent, node.spent);

        fs::remove_file(&path).ok();
    }

    #[test]
    fn load_missing_file_returns_none() {
        let path = temp_path("missing");
        fs::remove_file(&path).ok();
        let result = load_node_state(&path).unwrap();
        assert!(result.is_none());
    }

    #[test]
    fn save_never_leaves_a_partial_file_on_the_target_path() {
        // The rename-based approach means the target path only ever
        // exists as a complete file. Confirm the .tmp intermediate
        // does not linger after a successful save.
        let path = temp_path("no_partial");
        let tmp_path = path.with_extension("tmp");
        fs::remove_file(&path).ok();
        fs::remove_file(&tmp_path).ok();

        let node = Node::new("N2");
        save_node_state(&node, &path).unwrap();

        assert!(path.exists());
        assert!(!tmp_path.exists());

        fs::remove_file(&path).ok();
    }
}
