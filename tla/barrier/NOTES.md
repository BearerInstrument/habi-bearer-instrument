
## 2026-09-09: bb notin barrier guard — tried and reverted
Added a global `bb \notin barrier` precondition to SpendAt to try to
close the Result 1/2 gap directly in TLA+. Reverted after review of
Appendix 2: this guard is neither of the two mechanisms the reference
prototypes actually implement (peer-barrier check in SpendAt, or
ledger-burn-on-reconnect in LinkUp) — it's a third, more conservative,
unvalidated mechanism. habi_core/conversion_day.rs and habi_safety.v
implement ledger-burn-on-reconnect only. The peer-barrier check exists
separately in /root/habi_prototype/{go,rust}, outside this tree, and
is not currently modeled here. Diff of the reverted patch is preserved
in DIL_CRDT_Barrier.tla.bak for reference.
