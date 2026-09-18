# Evidence Map (xTech|Search 10 – HABI)

**Status note (2026-09-15):** A prior version of this document cited a
"PASS configuration: 992 states, 266 distinct, zero violations" result
as evidence that the per-link safety invariant holds. That TLC result
is real, but it was generated against `DIL_CRDT.tla` (the older,
global-connectivity model) checking `SyncedNoDoubleSpend` — not
against `DIL_CRDT_PerLink_Symmetric.tla` (the per-link model that
`habi_core`'s Rust implementation actually mirrors) checking
`PairwiseSyncedNoDoubleSpend`. The two are different models with
different invariant names; citing one as evidence for the other was
an error. See below for the corrected status.

| White-paper claim | Artifact |
|---|---|
| TLA+ found a genuine double-spend vulnerability in a naive design | `DIL_CRDT.tla` FAIL config (`NoDoubleSpendAcrossNodes`): 161 states, 73 distinct, violated — global-connectivity model |
| Global-connectivity model: corrected invariant holds exhaustively | `DIL_CRDT.tla` PASS config (`SyncedNoDoubleSpend`): 992 states, 266 distinct, zero violations, exhaustive (0 states left on queue) — this result is real but applies only to the simpler global-connectivity model, **not** the per-link model below |
| Per-link model, LinkUp/Propagate/SpendAt alone: safety invariant status | `DIL_CRDT_PerLink_Symmetric.tla`, `PairwiseSyncedNoDoubleSpend`: **violated in every recorded run** (5/5 logs, 2026-09-08 through 2026-09-15). Root cause: `LinkUp` reconciles `spent` only between the two immediate parties, so a stale ledger copy can be relayed back to a node still connected to the actual spender. This remains true of the bare reconnect logic and is not itself "fixed" -- it is why Conversion Day exists as a backstop; see the quorum-gated result below for the actual closed guarantee. |
| Per-link model + quorum-gated Conversion Day: safety invariant status | `DIL_CRDT_PerLink_ConversionDay.tla`, `QuorumSettlementIsSafe`: **exhaustively confirmed, 0 violations** (32,120 states generated, 3,765 distinct, 0 left on queue, 2026-09-18). A separate defect was found and fixed along the way: the original best-effort Conversion Day (excluding unreachable peers) could report a clean settlement while a genuine double-spend persisted on an excluded node -- confirmed via a dedicated counterexample model before the fix. Conversion Day now requires full quorum (`habi_node.rs`, `AdminMessage::ConversionDay` handler: returns `REPLY_ERROR`, no burn, no persistence, if any known peer is unreachable). |
| Rust `link_up` merge logic | `src/network.rs::link_up` implements the same pairwise-only reconciliation as the `.tla` model — confirmed to share the identical structural gap, not just a modeling artifact |
| Conversion Day as mitigation for the per-link gap | `conversion_day_coordinator.rs::check_post_conversion_day_safety` — unit test `post_conversion_day_safety_fails_if_burn_was_incomplete` confirms this exact class of staleness (one node spent, another still holds) is detected. This is a passing Rust unit test for one scenario, **not** an exhaustive model-checked guarantee — no combined per-link + Conversion Day TLA+ model currently exists. Detection is also after-the-fact: a node can still attempt a spend against stale state in the window before Conversion Day next runs; that attempt is then correctly rejected as a conflict, not silently accepted, but it is not prevented. |
| Independent Coq mechanization, 13 machine-checked theorems | `habi_safety.v` (503 lines as of 2026-09-18) -- compiles cleanly (`coqc` exit 0). Original 10: `naive_reconnect_breaks_safety`, `run_conversion_day_exe_preserves_safety`, `naive_reconnect_not_safe`, `safe_reconnect_implies_invariant`, `reconnect_must_forbid_naive_double_spend`, `network_N1N2_down_at_N1N2`, `network_all_true_N1N2`, `naive_reconnect_link_not_safe`, `safe_reconnect_link_implies_invariant`, `reconnect_link_must_forbid_naive_double_spend` (the last three are conditional: they prove that *any* reconnect procedure satisfying a stated safety hypothesis preserves the invariant, and that the naive procedure does not satisfy it -- they do NOT prove the actual `LinkUp` logic satisfies that hypothesis). Added 2026-09-18 for the quorum fix: `full_quorum_check_is_honest` (checking all nodes can never silently miss a real conflict), `singleton_participant_check_not_honest` (concrete counterexample: the original design's worst case, a lone caller with every peer unreachable, is provably dishonest), `quorum_burn_implies_invariant` (a full-quorum burn yields `PairwiseSyncedNoDoubleSpend3`). |
| Safety-only scope, no liveness claim | README design notes; no liveness theorems in `habi_safety.v` |
| Rust core, 47 automated tests | `cargo test` — 36 unit, 7 invariant-reproduction, 2 networked Conversion Day, 1 networked double-spend. Reconfirmed via fresh clone, 2026-09-15: 47/47 passing. Note: these tests do not cover the three-node relay scenario described above; they were not designed to catch it. |
| Live reproduction across real, separate OS processes over TCP | `habi_node` / `habi_admin` binaries; networked test suite |
| Python prototype reproducing counterexamples | **Not available.** Referenced during development but not present in this repository or located on the development machine as of Sept 2026. Not cited as evidence. |

## Open items as of 2026-09-15 -- status update 2026-09-18

1. ~~No TLA+ model of the combined per-link + Conversion Day system exists.~~ **Resolved 2026-09-18**: `DIL_CRDT_PerLink_ConversionDay.tla` models it; `QuorumSettlementIsSafe` confirms it exhaustively (32,120 states, 0 violations), after a real defect (partial-quorum settlement) was found and fixed along the way.
2. The per-link `PairwiseSyncedNoDoubleSpend` invariant, checked against bare reconnect logic in isolation (no Conversion Day), still does not hold and should not be cited as passing on its own -- this is expected and unchanged; Conversion Day is the backstop, not the reconnect logic itself.
3. `SpentMonotonic` has not been re-attempted against the new combined model. Worth revisiting now that item 1 is resolved and TLC no longer halts immediately on an unconditional per-link violation.

All artifacts above are independently reproducible via `git archive` from a pinned commit, rebuilt in an isolated environment with no dependency on the development machine.
