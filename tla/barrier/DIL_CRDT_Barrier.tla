---------------- MODULE DIL_CRDT_Barrier ----------------
EXTENDS Naturals, FiniteSets, TLC

VARIABLES ledgers, spent, network, barrier

Nodes   == {"N1","N2","N3"}
Bearers == {"b1","b2"}

TypeOK ==
  /\ ledgers  \in [Nodes -> SUBSET Bearers]
  /\ spent    \in [Nodes -> SUBSET Bearers]
  /\ network  \in [Nodes -> [Nodes -> BOOLEAN]]
  /\ barrier  \in SUBSET Bearers

Init ==
  /\ ledgers = [a \in Nodes |->
                  IF a = "N1" THEN {"b1"}
                  ELSE IF a = "N2" THEN {"b2"}
                  ELSE {}]
  /\ spent   = [a \in Nodes |-> {}]
  /\ network = [a \in Nodes |-> [b \in Nodes |-> a /= b]]
  /\ barrier = {}

ConnectedTo(n) == {m \in Nodes : m /= n /\ network[n][m] = TRUE}

FullyConnected ==
  \A a, b \in Nodes : a = b \/ network[a][b] = TRUE

PartiallyIsolated(n) ==
  \E m \in Nodes : m /= n /\ network[n][m] = FALSE

LinkDown(n, m) ==
  /\ n /= m
  /\ network[n][m] = TRUE
  /\ network' = [network EXCEPT ![n][m] = FALSE, ![m][n] = FALSE]
  /\ UNCHANGED <<ledgers, spent, barrier>>

LinkUp(n, m) ==
  /\ n /= m
  /\ network[n][m] = FALSE
  /\ LET knownSpent == spent[n] \union spent[m]
         merged     == ((ledgers[n] \union ledgers[m]) \ knownSpent) \ barrier
     IN
       /\ network' = [network EXCEPT ![n][m] = TRUE, ![m][n] = TRUE]
       /\ ledgers' = [ledgers EXCEPT ![n] = merged, ![m] = merged]
  /\ UNCHANGED <<spent, barrier>>

Propagate(src, dst) ==
  /\ network[src][dst] = TRUE
  /\ LET deliverable == ((ledgers[src] \ spent[dst]) \ ledgers[dst]) \ barrier
     IN
       /\ deliverable /= {}
       /\ ledgers' = [ledgers EXCEPT ![dst] = ledgers[dst] \union deliverable]
  /\ UNCHANGED <<spent, network, barrier>>

SpendAt(nn, bb) ==
  /\ bb \in ledgers[nn]
  /\ spent'   = [spent EXCEPT ![nn] = spent[nn] \union {bb}]
  /\ ledgers' = [mm \in Nodes |->
                   IF mm = nn \/ mm \in ConnectedTo(nn)
                   THEN ledgers[mm] \ {bb}
                   ELSE ledgers[mm]]
  /\ barrier' = IF PartiallyIsolated(nn)
                THEN barrier \union {bb}
                ELSE barrier
  /\ UNCHANGED network

ClearBarrier ==
  /\ FullyConnected
  /\ \A b \in barrier : \A n \in Nodes : b \notin ledgers[n]
  /\ barrier' = {}
  /\ UNCHANGED <<ledgers, spent, network>>

Next ==
  \/ \E n, m \in Nodes : LinkDown(n, m)
  \/ \E n, m \in Nodes : LinkUp(n, m)
  \/ \E src, dst \in Nodes : Propagate(src, dst)
  \/ \E nn \in Nodes, bb \in Bearers : SpendAt(nn, bb)
  \/ ClearBarrier

Spec == Init /\ [][Next]_<<ledgers, spent, network, barrier>>

NoDoubleSpendAcrossNodes ==
  \A b \in Bearers :
    Cardinality({n \in Nodes : b \in spent[n]}) <= 1

PairwiseSyncedNoDoubleSpend ==
  \A n1, n2 \in Nodes :
    network[n1][n2] = TRUE =>
      \A b \in Bearers :
        ((b \in spent[n1]) \/ (b \in spent[n2])) =>
          (b \notin ledgers[n1] /\ b \notin ledgers[n2])

BarrierConsistent ==
  FullyConnected /\ barrier = {} =>
    \A b \in Bearers :
      (\E n \in Nodes : b \in spent[n]) =>
        (\A m \in Nodes : b \notin ledgers[m])

=============================================================================
