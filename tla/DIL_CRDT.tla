---------------- MODULE DIL_CRDT ----------------
EXTENDS Naturals, FiniteSets, TLC
VARIABLES ledgers, spent, networkUp

Nodes == {"N1","N2","N3"}
Bearers == {"b1","b2"}

TypeOK ==
  /\ ledgers \in [Nodes -> SUBSET Bearers]
  /\ spent \in [Nodes -> SUBSET Bearers]
  /\ networkUp \in BOOLEAN

Init ==
  /\ ledgers = [a \in Nodes |->
                  IF a = "N1" THEN {"b1"}
                  ELSE IF a = "N2" THEN {"b2"}
                  ELSE {}]
  /\ spent = [a \in Nodes |-> {}]
  /\ networkUp = TRUE

IntersectAll(SS) == { xx \in UNION SS : \A TT \in SS : xx \in TT }

Disconnect == networkUp' = FALSE /\ UNCHANGED <<ledgers, spent>>

\* FIX 1: spent is NEVER rewritten here. It stays a permanent record of
\* who actually initiated each spend -- that's what makes
\* NoDoubleSpendAcrossNodes meaningful. Reconnect only uses spent to
\* decide what to BURN from ledgers; it does not corrupt spent itself.
Reconnect ==
  /\ networkUp = FALSE
  /\ networkUp' = TRUE
  /\ LET allSpent == UNION {spent[vv] : vv \in Nodes} IN
       ledgers' = [uu \in Nodes |-> ledgers[uu] \ allSpent]
  /\ UNCHANGED spent

\* FIX 2: while CONNECTED, a spend is immediately visible/burned
\* everywhere (models "connected = consistent" -- the real
\* inconsistency window only exists during a partition). While
\* DISCONNECTED, only the local node's ledger changes -- this is the
\* actual fork risk the invariant is meant to catch.
SpendAt(nn, bb) ==
  /\ bb \in ledgers[nn]
  /\ spent' = [mm \in Nodes |-> IF mm=nn THEN spent[mm] \union {bb} ELSE spent[mm]]
  /\ IF networkUp
       THEN ledgers' = [mm \in Nodes |-> ledgers[mm] \ {bb}]
       ELSE ledgers' = [mm \in Nodes |-> IF mm=nn THEN ledgers[mm] \ {bb} ELSE ledgers[mm]]
  /\ UNCHANGED networkUp

Replicate ==
  /\ networkUp = TRUE
  /\ ledgers' = [pp \in Nodes |-> (UNION {ledgers[qq] : qq \in Nodes}) \ spent[pp]]
  /\ UNCHANGED <<spent, networkUp>>

\* ResolveBurn kept for parity with Reconnect's burn logic while still
\* connected (e.g. a late-arriving spend record from a slow peer).
ResolveBurn ==
  /\ networkUp = TRUE
  /\ LET allSpent == UNION {spent[qq] : qq \in Nodes} IN
       ledgers' = [pp \in Nodes |-> ledgers[pp] \ allSpent]
  /\ UNCHANGED <<spent, networkUp>>

Next == Disconnect \/ Reconnect \/ Replicate \/ ResolveBurn \/ \E nn \in Nodes, bb \in Bearers : SpendAt(nn,bb)
Spec == Init /\ [][Next]_<<ledgers, spent, networkUp>>

\* Detects TRUE double-spend: two DIFFERENT nodes each independently
\* initiated a spend of the same bearer. Should violate only via a
\* trace that goes through Disconnect first.
NoDoubleSpendAcrossNodes == \A bbb \in Bearers : Cardinality({nnn \in Nodes : bbb \in spent[nnn]}) <= 1

SyncedNoDoubleSpend ==
  networkUp =>
    \A ccc \in Bearers :
      (\E ddd \in Nodes : ccc \in spent[ddd]) => (\A eee \in Nodes : ccc \notin ledgers[eee])
=============================================================================
