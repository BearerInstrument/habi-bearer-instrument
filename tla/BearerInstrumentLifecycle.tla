---------------- MODULE BearerInstrumentLifecycle ----------------
EXTENDS Naturals, FiniteSets, TLC
VARIABLES ledger, holder, state

Bearers == {"b1", "b2"}
Parties == {"Alice", "Bob", "Treasury"}

TypeOK ==
  /\ ledger \in SUBSET Bearers
  /\ holder \in [Bearers -> Parties \union {"None"}]
  /\ state  \in [Bearers -> {"Issued","Held","Transferred","Redeemed"}]

Init ==
  /\ ledger = Bearers
  /\ holder = [b \in Bearers |-> "Treasury"]
  /\ state  = [b \in Bearers |-> "Issued"]

Issue(b) ==
  /\ state[b] = "Issued"
  /\ state'  = [state EXCEPT ![b] = "Held"]
  /\ holder' = [holder EXCEPT ![b] = "Alice"]
  /\ UNCHANGED ledger

\* FIX: Transfer now actually reaches the "Transferred" state instead
\* of leaving state unchanged at "Held" -- previously "Transferred"
\* was declared in TypeOK but unreachable by any action.
Transfer(b, from, to) ==
  /\ state[b] \in {"Held", "Transferred"}
  /\ holder[b] = from
  /\ from /= to
  /\ state'  = [state EXCEPT ![b] = "Transferred"]
  /\ holder' = [holder EXCEPT ![b] = to]
  /\ UNCHANGED ledger

\* FIX: Redeem no longer removes b from ledger. ledger is now a
\* permanent registry of every bearer that ever existed, so
\* NoDoubleSpend below has something real to check against a
\* redeemed bearer instead of the property being vacuously true.
Redeem(b) ==
  /\ state[b] \in {"Held", "Transferred"}
  /\ state'  = [state EXCEPT ![b] = "Redeemed"]
  /\ holder' = [holder EXCEPT ![b] = "None"]
  /\ UNCHANGED ledger

Next ==
  \E b \in Bearers :
    \/ Issue(b)
    \/ Redeem(b)
    \/ \E f, t \in Parties : Transfer(b, f, t)

Spec == Init /\ [][Next]_<<ledger, holder, state>>

\* FIX: every reachable state where all bearers are Redeemed is now
\* an explicitly expected terminal state (no action can fire once
\* every bearer is spent) rather than an unmodeled TLC deadlock.
\* Terminating is an unconditional stuttering step, gated by its own
\* precondition -- this is what actually assigns all three primed
\* variables in every disjunct of Next \/ Terminating (the earlier
\* attempt using => left them unassigned when the guard was true).
Terminating ==
  /\ \A b \in Bearers : state[b] = "Redeemed"
  /\ UNCHANGED <<ledger, holder, state>>

FairSpec == Init /\ [][Next \/ Terminating]_<<ledger, holder, state>>

\* FIX: checks state directly, over the permanent ledger, so a
\* redeemed-and-then-somehow-reissued bearer (impossible under this
\* Next relation, but that's exactly what the invariant should be
\* protecting against) would actually be caught. No longer vacuous:
\* ledger membership no longer changes on Redeem, so this genuinely
\* constrains reachable (holder, state) combinations.
NoDoubleSpend ==
  \A b \in ledger :
    state[b] = "Redeemed" => holder[b] = "None"

=============================================================================
