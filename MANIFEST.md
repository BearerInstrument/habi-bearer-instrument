# habi_core — Verified Items Manifest (2026-09-11/12 distributed hardening pass)

## 46 automated tests — `cargo test`, all passing

- 36 unit tests (wire encoding, persistence, shared_state merge/spend
  logic, peer_protocol dispatch, conversion_day_coordinator)
- 7 invariant-reproduction tests (`tests/invariants.rs`) — Result 1,
  Result 2, Result 3, and Conversion Day behavior against the
  centralized `Network` model
- 1 networked double-spend integration test
  (`tests/networked_double_spend.rs`) — spawns 3 real `habi_node`
  processes, reproduces Result 1 over genuine TCP sockets
- 2 networked Conversion Day integration tests
  (`tests/networked_conversion_day.rs`):
  - `networked_conversion_day_rejects_genuine_conflict_atomically` —
    confirms the coordinator refuses a genuine cross-node double
    spend and leaves every node's state byte-for-byte unchanged
    (verified atomic by construction: `compute_conversion_day` is
    checked before any mutation is attempted — the Err arm returns
    before any state-mutating lock is taken, so there is no partial
    write to roll back from)
  - `networked_conversion_day_burns_and_prevents_future_spend_when_no_conflict` —
    confirms a genuine no-conflict burn removes the bearer from
    every node's ledger, correctly leaves `spent` untouched on
    nodes that never spent it themselves, and makes the bearer
    permanently unspendable on all three nodes afterward

Reproduce with: `cargo build && cargo test`
Logs: `stage2d_seed_build.log`, `stage2d_seed_test.log`,
`stage2d_smoke.log`, `stage5_full_test.log` (46 PASS)

## +1 separately-verified Coq evidence artifact

`Coq-evidence-2026-09-19.tar.gz` (+ `.sha256`) — the CURRENT
`habi_safety.v`/`habi_safety.vo` pair, containing all 13
theorems/lemmas presently in the proof (10 original, plus 3 added
2026-09-18 for the per-link settlement quorum fix):

- `naive_reconnect_breaks_safety`
- `run_conversion_day_exe_preserves_safety`
- `naive_reconnect_not_safe`
- `safe_reconnect_implies_invariant`
- `reconnect_must_forbid_naive_double_spend`
- `network_N1N2_down_at_N1N2`
- `network_all_true_N1N2`
- `naive_reconnect_link_not_safe`
- `safe_reconnect_link_implies_invariant`
- `reconnect_link_must_forbid_naive_double_spend`
- `full_quorum_check_is_honest`
- `singleton_participant_check_not_honest`
- `quorum_burn_implies_invariant`

The original 10 prove the reconnect-safety result under both the
global-connectivity model (`SyncedNoDoubleSpend3`) and the per-link
model (`PairwiseSyncedNoDoubleSpend3`). The 3 added 2026-09-18 prove
the per-link settlement quorum fix directly: `full_quorum_check_is_honest`
(a full-quorum conflict check can never silently miss a real conflict),
`singleton_participant_check_not_honest` (a concrete counterexample
confirming the original partial-quorum design was genuinely unsafe),
and `quorum_burn_implies_invariant` (a full-quorum burn yields
`PairwiseSyncedNoDoubleSpend3`). This is NOT a `cargo test`
result — it is a compiled Coq proof (`.vo`), verified here via:

1. SHA-256 checksum match against the accompanying `.sha256` file
2. A fresh `coqc habi_safety.v` recompile from the archived `.v`
   source, confirmed to compile with zero errors (done both at
   archive-creation time and again independently after re-extracting
   from the finished archive)

Supersedes the earlier `Coq-evidence-2026-09-09.tar.gz` (3
theorems, an earlier independently-valid checkpoint) — removed from
this package to avoid shipping stale evidence alongside the current,
more complete proof.

## Total: 47 independently verified items

46 test-suite passes + 1 compile-verified proof artifact. The two
categories are checked by different mechanisms (`cargo test`
pass/fail vs. `coqc` compile success + checksum) and should not be
read as 47 uniform test results.
