---------------------------- MODULE DIL_CRDT_PerLink_ConversionDay ----------------------------
EXTENDS Naturals, FiniteSets, Sequences

VARIABLES ledgers, spent, network, justSettled

Nodes   == {"N1","N2","N3"}
Bearers == {"b1","b2"}

TypeOK ==
  /\ ledgers \in [Nodes -> SUBSET Bearers]
  /\ spent   \in [Nodes -> SUBSET Bearers]
  /\ network \in [Nodes -> [Nodes -> BOOLEAN]]
  /\ justSettled \in BOOLEAN

Init ==
  /\ ledgers = [n \in Nodes |-> IF n = "N1" THEN {"b1"}
                                 ELSE IF n = "N2" THEN {"b2"}
                                 ELSE {}]
  /\ spent   = [n \in Nodes |-> {}]
  /\ network = [a \in Nodes |-> [b \in Nodes |-> a /= b]]
  /\ justSettled = FALSE

FullyConnected ==
  \A a, b \in Nodes : a = b \/ network[a][b] = TRUE

LinkDown(n, m) ==
  /\ n /= m
  /\ network[n][m] = TRUE
  /\ network' = [network EXCEPT ![n][m] = FALSE, ![m][n] = FALSE]
  /\ justSettled' = FALSE
  /\ UNCHANGED <<ledgers, spent>>

LinkUp(n, m) ==
  /\ n /= m
  /\ network[n][m] = FALSE
  /\ LET merged == (ledgers[n] \union ledgers[m]) \ (spent[n] \union spent[m])
     IN
       /\ network' = [network EXCEPT ![n][m] = TRUE, ![m][n] = TRUE]
       /\ ledgers' = [ledgers EXCEPT ![n] = merged, ![m] = merged]
  /\ justSettled' = FALSE
  /\ UNCHANGED spent

Propagate(src, dst) ==
  /\ network[src][dst] = TRUE
  /\ LET deliverable == (ledgers[src] \ spent[dst]) \ ledgers[dst]
     IN
       /\ deliverable /= {}
       /\ ledgers' = [ledgers EXCEPT ![dst] = ledgers[dst] \union deliverable]
  /\ justSettled' = FALSE
  /\ UNCHANGED <<spent, network>>

SpendAt(nn, bb) ==
  /\ bb \in ledgers[nn]
  /\ spent' = [spent EXCEPT ![nn] = spent[nn] \union {bb}]
  /\ ledgers' = [mm \in Nodes |->
                   IF mm = nn \/ network[nn][mm] = TRUE
                   THEN ledgers[mm] \ {bb}
                   ELSE ledgers[mm]]
  /\ justSettled' = FALSE
  /\ UNCHANGED network

\* Quorum-gated Conversion Day: refuses to run at all -- no burn, no
\* decision -- unless every known node is currently reachable. This
\* is the fix for the partial-participation gap: an unreachable node
\* can no longer be silently excluded from a settlement round.
ConversionDay ==
  /\ FullyConnected
  /\ LET spentBy(b)  == {n \in Nodes : b \in spent[n]}
         conflicted  == {b \in Bearers : Cardinality(spentBy(b)) > 1}
     IN
       IF conflicted /= {}
       THEN /\ justSettled' = FALSE
            /\ UNCHANGED <<ledgers, spent, network>>
       ELSE LET toBurn == {b \in Bearers : spentBy(b) /= {}}
            IN /\ ledgers' = [n \in Nodes |-> ledgers[n] \ toBurn]
               /\ justSettled' = TRUE
               /\ UNCHANGED <<spent, network>>

Next ==
  \/ \E n, m \in Nodes : LinkDown(n, m)
  \/ \E n, m \in Nodes : LinkUp(n, m)
  \/ \E src, dst \in Nodes : Propagate(src, dst)
  \/ \E nn \in Nodes, bb \in Bearers : SpendAt(nn, bb)
  \/ ConversionDay

Spec == Init /\ [][Next]_<<ledgers, spent, network, justSettled>>

NoDoubleSpendAcrossNodes ==
  \A b \in Bearers : Cardinality({n \in Nodes : b \in spent[n]}) <= 1

QuorumSettlementIsSafe ==
  justSettled => NoDoubleSpendAcrossNodes

=============================================================================
