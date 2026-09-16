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
| Per-link model (matches shipped Rust code): safety invariant status | `DIL_CRDT_PerLink_Symmetric.tla`, `PairwiseSyncedNoDoubleSpend`: **currently violated in every recorded run** (5/5 logs, 2026-09-08 through 2026-09-15). Root cause: `LinkUp` reconciles `spent` only between the two immediate parties, so a stale ledger copy can be relayed back to a node still connected to the actual spender. This is not resolved. |
| Rust `link_up` merge logic | `src/network.rs::link_up` implements the same pairwise-only reconciliation as the `.tla` model — confirmed to share the identical structural gap, not just a modeling artifact |
| Conversion Day as mitigation for the per-link gap | `conversion_day_coordinator.rs::check_post_conversion_day_safety` — unit test `post_conversion_day_safety_fails_if_burn_was_incomplete` confirms this exact class of staleness (one node spent, another still holds) is detected. This is a passing Rust unit test for one scenario, **not** an exhaustive model-checked guarantee — no combined per-link + Conversion Day TLA+ model currently exists. Detection is also after-the-fact: a node can still attempt a spend against stale state in the window before Conversion Day next runs; that attempt is then correctly rejected as a conflict, not silently accepted, but it is not prevented. |
| Independent Coq mechanization, 10 machine-checked theorems | `habi_safety.v` (406 lines) — re-verified 2026-09-15, byte-identical to the copy in the NRL-submitted evidence tarball (SHA256 match), compiles cleanly (`coqc` exit 0). Real theorem/lemma list: `naive_reconnect_breaks_safety`, `run_conversion_day_exe_preserves_safety`, `naive_reconnect_not_safe`, `safe_reconnect_implies_invariant`, `reconnect_must_forbid_naive_double_spend`, `network_N1N2_down_at_N1N2`, `network_all_true_N1N2`, `naive_reconnect_link_not_safe`, `safe_reconnect_link_implies_invariant`, `reconnect_link_must_forbid_naive_double_spend`. The per-link theorems (last three) are conditional: they prove that *any* reconnect procedure satisfying a stated safety hypothesis preserves the invariant, and that the naive procedure does not satisfy it. They do NOT prove the system's actual `LinkUp` logic satisfies that hypothesis -- consistent with, not contradicted by, the TLC violation documented above. |
| Safety-only scope, no liveness claim | README design notes; no liveness theorems in `habi_safety.v` |
| Rust core, 46 automated tests | `cargo test` — 36 unit, 7 invariant-reproduction, 2 networked Conversion Day, 1 networked double-spend. Reconfirmed via fresh clone, 2026-09-15: 46/46 passing. Note: these tests do not cover the three-node relay scenario described above; they were not designed to catch it. |
| Live reproduction across real, separate OS processes over TCP | `habi_node` / `habi_admin` binaries; networked test suite |
| Python prototype reproducing counterexamples | **Not available.** Referenced during development but not present in this repository or located on the development machine as of Sept 2026. Not cited as evidence. |

## Open items as of 2026-09-15

1. No TLA+ model of the combined per-link + Conversion Day system exists. Building one is the only way to make an exhaustive safety claim for the actual mitigation strategy.
2. The per-link `PairwiseSyncedNoDoubleSpend` invariant, in isolation, does not hold and should not be cited as passing anywhere.
3. `SpentMonotonic` (added 2026-09-15) has not been meaningfully checked — TLC halts on the pre-existing `PairwiseSyncedNoDoubleSpend` violation before it can explore enough of the state space to confirm or refute it.

All artifacts above are independently reproducible via `git archive` from a pinned commit, rebuilt in an isolated environment with no dependency on the development machine.
