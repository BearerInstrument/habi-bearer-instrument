# Evidence Map (xTech|Search 10 – HABI)

| White-paper claim | Artifact |
|---|---|
| TLA+ found a genuine double-spend vulnerability in the naive disconnect/reconnect design | FAIL configuration: 161 states explored, 73 distinct — counterexample trace |
| Corrected synchronization invariant holds exhaustively | PASS configuration: 992 states explored, 266 distinct, zero violations |
| Independent Coq mechanization, 10 machine-checked theorems | `habi_safety.v` (406 lines) — theorem names follow `naive_reconnect_*`, `safe_reconnect_*`, `reconnect_*_double_spend` patterns; compiles cleanly (`coqc` exit 0) |
| Safety-only scope, no liveness claim | README design notes; no liveness theorems in `habi_safety.v` |
| Rust core, 46 automated tests | `cargo test` — 36 unit, 7 invariant-reproduction, 2 networked Conversion Day, 1 networked double-spend |
| Live reproduction across real, separate OS processes over TCP | `habi_node` / `habi_admin` binaries; networked test suite |
| Conversion Day reconciliation barrier | `conversion_day_coordinator.rs` |
| Python prototype reproducing counterexamples | **Not available.** Referenced during development but not present in this repository or located on the development machine as of Sept 2026. Not cited as evidence. |

All artifacts above are independently reproducible via `git archive` from a pinned commit, rebuilt in an isolated environment with no dependency on the development machine.
