---------------- MODULE DIL_CRDT_PerLink_Symmetric ----------------
EXTENDS Naturals, FiniteSets, TLC
VARIABLES ledgers, spent, network

Nodes == {"N1","N2","N3"}
Bearers == {"b1","b2"}

TypeOK ==
  /\ ledgers \in [Nodes -> SUBSET Bearers]
  /\ spent \in [Nodes -> SUBSET Bearers]
  /\ network \in [Nodes -> [Nodes -> BOOLEAN]]

Init ==
  /\ ledgers = [a \in Nodes |->
                  IF a = "N1" THEN {"b1"}
                  ELSE IF a = "N2" THEN {"b2"}
                  ELSE {}]
  /\ spent = [a \in Nodes |-> {}]
  /\ network = [a \in Nodes |-> [b \in Nodes |-> a /= b]]

ConnectedTo(n) == {m \in Nodes : m /= n /\ network[n][m] = TRUE}

LinkDown(n, m) ==
  /\ n /= m
  /\ network[n][m] = TRUE
  /\ network' = [network EXCEPT ![n][m] = FALSE, ![m][n] = FALSE]
  /\ UNCHANGED <<ledgers, spent>>

\* FIX: LinkUp burns anything either side already knows was spent, but
\* NEVER rewrites spent itself. spent must only grow via an actual SpendAt
\* call by that node -- inheriting "spent" through a link merge conflates
\* knowledge-of-a-spend with an independent spend event, which produces
\* false NoDoubleSpendAcrossNodes violations (a single real spend getting
\* miscounted as two).
LinkUp(n, m) ==
  /\ n /= m
  /\ network[n][m] = FALSE
  /\ LET knownSpent == spent[n] \union spent[m]
         merged == (ledgers[n] \union ledgers[m]) \ knownSpent
     IN
       /\ network' = [network EXCEPT ![n][m] = TRUE, ![m][n] = TRUE]
       /\ ledgers' = [ledgers EXCEPT ![n] = merged, ![m] = merged]
  /\ UNCHANGED spent

\* Direct-link-only propagation of UNSPENT holdings. dst only receives what
\* src currently holds and dst hasn't already spent or already got.
Propagate(src, dst) ==
  /\ network[src][dst] = TRUE
  /\ LET deliverable == (ledgers[src] \ spent[dst]) \ ledgers[dst] IN
       /\ deliverable /= {}
       /\ ledgers' = [ledgers EXCEPT ![dst] = ledgers[dst] \union deliverable]
  /\ UNCHANGED <<spent, network>>

SpendAt(nn, bb) ==
  /\ bb \in ledgers[nn]
  /\ spent' = [spent EXCEPT ![nn] = spent[nn] \union {bb}]
  /\ ledgers' = [mm \in Nodes |->
                   IF mm = nn \/ mm \in ConnectedTo(nn)
                   THEN ledgers[mm] \ {bb}
                   ELSE ledgers[mm]]
  /\ UNCHANGED network

Next ==
  (\E n, m \in Nodes : LinkDown(n, m))
  \/ (\E n, m \in Nodes : LinkUp(n, m))
  \/ (\E src, dst \in Nodes : Propagate(src, dst))
  \/ (\E nn \in Nodes, bb \in Bearers : SpendAt(nn, bb))

Spec == Init /\ [][Next]_<<ledgers, spent, network>>

\* GLOBAL vulnerability check. EXPECTED TO VIOLATE -- and, as an
\* additional documented finding beyond the original 3-node model: even
\* WITHOUT a global spent-tracking overwrite bug, a node's local belief
\* about a bearer's validity can go stale the instant it disconnects, and
\* nothing in a purely direct-link, no-global-broadcast gossip design
\* stops it from propagating that staleness onward before it learns
\* otherwise. This is a structural property of pairwise-gossip CRDTs, not
\* a bug in this model -- and motivates the settlement-barrier /
\* "Conversion Day" design already proposed in the whitepaper (Section 3)
\* as the actual mitigation, rather than a purely local reconciliation
\* protocol.
NoDoubleSpendAcrossNodes ==
  \A bbb \in Bearers : Cardinality({nnn \in Nodes : bbb \in spent[nnn]}) <= 1

\* LOCAL (per-edge) safety check.
PairwiseSyncedNoDoubleSpend ==
  \A n1, n2 \in Nodes :
    network[n1][n2] = TRUE =>
      \A b \in Bearers :
        ((b \in spent[n1]) \/ (b \in spent[n2])) => (b \notin ledgers[n1] /\ b \notin ledgers[n2])

\* ACTION PROPERTY (not an invariant): spent[n] only ever grows. This
\* is true by construction today -- every action either leaves spent
\* UNCHANGED (LinkDown, LinkUp, Propagate) or unions into it (SpendAt)
\* -- but that fact currently depends on reading all four actions by
\* eye. Asserting it explicitly means TLC catches any future action
\* that accidentally removes a bearer from spent[n], which would
\* silently undermine both NoDoubleSpendAcrossNodes and
\* PairwiseSyncedNoDoubleSpend, since both are defined entirely in
\* terms of set membership in spent.
SpentMonotonic ==
  [][\A n \in Nodes : spent[n] \subseteq spent'[n]]_<<ledgers, spent, network>>
=============================================================================
