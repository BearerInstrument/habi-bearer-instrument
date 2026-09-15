# habi_core

## What This Is / What This Is Not

**This is:** A safety-focused formal verification project for a disconnection-tolerant bearer-instrument ledger. It includes a TLA+ model that found a genuine double-spend vulnerability in a naive disconnect/reconnect design, an independent Coq mechanization of the corrected safety invariant (10 machine-checked theorems), and a Rust implementation validated by 46 automated tests, including live reproduction across three separate networked processes over real TCP. This repository is submitted as supporting technical evidence for the HABI white paper under Army xTech|Search 10 and reflects prior work submitted under NRL Long-Range BAA N00173-24-S-BA01, Topic 55-24-02.

**This is not:** A production-ready or hardened system. No liveness claim is made about disconnected nodes ("stragglers") — Conversion Day is a safety result, not a liveness guarantee. The `seed` mechanism is bootstrap-only and does not model real-world issuance. This is a transliteration of the TLA+-verified design into Rust, not an independent re-verification of the Rust code itself.

Rust port of `DIL_CRDT_PerLink_Symmetric.tla`, matching the prototype-core
language commitment in the whitepaper (Section 2d, Section 4 — Month 6
deliverable: Rust for memory safety on embedded naval hardware).

This Rust implementation was originally developed alongside a Python
transliteration of the same `.tla` spec, used during development to
cross-check invariants and demo scenarios. That Python version is not
present in this repository and could not be located on the development
machine as of September 2026 — it should not be cited as available
evidence until it is recovered and independently re-verified.

| File | Mirrors |
|---|---|
| `src/node.rs` | `TypeOK` / `Init` — a node's `ledger`/`spent` sets |
| `src/network.rs` | `Next` — `link_down`, `link_up`, `propagate`, `spend_at`, plus both invariants (`no_double_spend_across_nodes`, `pairwise_synced_no_double_spend`) |
| `src/conversion_day.rs` | Month 9 path **(a)** from Section 4: a coordinating settlement barrier, checked as a **safety** result (`Result<(), DoubleSpendDetected>`), not reframed as liveness |
| `src/main.rs` | Demo binary reproducing the Result 1 counterexample, then the barrier closing it, then the barrier correctly rejecting a real pre-existing double-spend |
| `tests/invariants.rs` | Reproduces both Result 1 and Result 2 counterexample traces exactly, plus barrier behavior |

Zero external crates — std only — so `cargo build`/`cargo test` need no
network access, which matters if the embedded target build environment
is offline/air-gapped.

## Build & run

```bash
cargo build
cargo run --bin demo_scenarios
cargo test
```

## Status: compiled, tested, and deployed

All of the above is compiler-verified and passing (`cargo build` +
`cargo test`, 46 tests: 36 unit, 7 invariant-reproduction, 2 networked Conversion Day integration tests,
1 networked double-spend integration test) as of the distributed hardening pass
described below. It has also been run as three genuinely separate OS
processes communicating over real TCP sockets, not just in-process.

## Design notes carried over from the Python version

- `run_conversion_day` picks "designated reconciliation authority" as
  the concrete mechanism (over version vectors) purely because it's
  simplest to prototype first.
- The barrier's safety guarantee: reconciled nodes end the call
  mutually consistent, or the call returns `Err(DoubleSpendDetected)`
  for out-of-band handling if a genuine conflict already happened
  before the barrier could run. No liveness claim is made about
  stragglers that didn't participate in a given barrier — that's
  Section 4 path (b), explicitly deferred per the addendum's
  recommendation.
- This is a transliteration, not a re-verification. The `.tla` model
  checking is still the thing that counts as the Month 9 formal
  result; this crate is for engineering exploration and, eventually,
  the actual deployable core.


## Distributed deployment (`habi_node` / `habi_admin`)

Beyond the single-process demo/test suite above, `habi_core` also
includes a real networked deployment: each node runs as its own OS
process (`src/bin/habi_node.rs`), communicating with peer nodes and
an admin client over plain TCP with a hand-rolled, pipe-delimited
wire protocol (`src/wire.rs`) — no external dependencies, matching
the crate's zero-crate philosophy.

| File | Purpose |
|---|---|
| `src/wire.rs` | `PeerMessage`/`AdminMessage`/`AdminReply` wire encoding |
| `src/shared_state.rs` | Thread-safe (`Arc<Mutex<>>`) per-node state + pure merge/spend logic, unit-tested without sockets |
| `src/peer_protocol.rs` | Pure peer-message dispatch logic (LinkUp/Propagate/SpendAt/Status), unit-tested without sockets |
| `src/conversion_day_coordinator.rs` | Pure distributed Conversion Day logic (gather → detect conflict or burn), unit-tested without sockets |
| `src/persistence.rs` | Atomic (write-temp-then-rename) node state save/load, survives process restart and abrupt `SIGKILL` |
| `src/bin/habi_node.rs` | The threaded node server itself — thin I/O wrapper over the above, one thread per connection |
| `src/bin/habi_admin.rs` | Minimal CLI client for driving a running node's admin listener |
| `tests/networked_double_spend.rs` | Spawns three real `habi_node` processes, reproduces Result 1 over actual TCP, kills them via `Drop` even on test panic |

### Running a 3-node deployment

```bash
cat > peers.txt <<'PEERS'
N1|127.0.0.1:9001
N2|127.0.0.1:9002
N3|127.0.0.1:9003
PEERS

./target/debug/habi_node N1 127.0.0.1:9001 127.0.0.1:9101 peers.txt N1.state &
./target/debug/habi_node N2 127.0.0.1:9002 127.0.0.1:9102 peers.txt N2.state &
./target/debug/habi_node N3 127.0.0.1:9003 127.0.0.1:9103 peers.txt N3.state &

./target/debug/habi_admin 127.0.0.1:9101 status
./target/debug/habi_admin 127.0.0.1:9101 link-up N2
./target/debug/habi_admin 127.0.0.1:9101 spend b1
./target/debug/habi_admin 127.0.0.1:9101 conversion-day
```

### Admin commands

- `link-up <peer>` / `link-down <peer>` — bring a link to a named peer up/down
- `propagate <peer>` — pull unspent holdings from a linked peer (requires an active link, same precondition as `network.rs::propagate`)
- `spend <bearer>` — locally spend a held bearer, broadcasts `SpentNotify` to currently-connected peers
- `status` — report this node's ledger, spent set, and active links
- `conversion-day` — act as coordinator: gather every peer's raw state via `StatusRequest`, detect a genuine cross-node conflict (if any bearer was spent by more than one node, refuses and reports it — mirrors `conversion_day.rs`'s `DoubleSpendDetected`) or, if none, burn every globally-spent bearer from every node's ledger via `SpentNotify` broadcast (mirrors `run_conversion_day`)
- `seed <bearer>` — **test/bootstrap only, see warning below**

### ⚠️ `seed` is a test/bootstrap operation, not real issuance

There is currently no real bearer-issuance/minting mechanism, centralized
or distributed. `seed` directly inserts a bearer into a node's ledger
with **no provenance check whatsoever** — it exists solely so a
distributed deployment can be smoke-tested and integration-tested
end-to-end without a real issuance system yet existing. It is not gated
behind `#[cfg(test)]` because it must work in the actual running
`habi_node` binary during manual and integration testing, not only in
`cargo test`'s unit-test build — `#[cfg(test)]` only applies within a
crate's own test compilation, and `habi_node` is a separate binary
target reached over real TCP. Every invocation logs a runtime warning
to the node's own log output for this reason. **A real issuance
mechanism is a prerequisite for any production use of this system and
does not yet exist.**

### Known distributed-vs-centralized semantic notes

- **`SpentNotify` after a burn does not add to `spent`.** After
  `conversion-day` burns a bearer from a node that never actually
  spent it, that node's `spent` set is correctly left untouched —
  only `ledger` is affected. `spent` records who genuinely initiated
  a spend; inflating it via a burn notification would corrupt the
  very provenance tracking `conversion-day`'s conflict detection
  depends on. A node recovering from a burn shows the bearer as
  unspendable (absent from `ledger`), not as something it spent.
- **`Propagate` requires an active link**, matching
  `network.rs::propagate`'s `network[src][dst] = TRUE` precondition
  — added after an initial version incorrectly replied to a
  propagate request regardless of link state.
