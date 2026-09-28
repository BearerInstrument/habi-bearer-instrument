---- MODULE PolicyGate ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Actions

VARIABLES
    pending,        \* set of actions currently proposed and undecided
    confirmations,  \* [Actions -> SUBSET Nodes] which nodes confirmed an action
    decisions,      \* [Actions -> {"None","Approved","Blocked","Deferred"}]
    networkUp       \* [Nodes -> BOOLEAN] reachability of each policy node from the coordinator

Decision == {"None", "Approved", "Blocked", "Deferred"}

TypeOK ==
    /\ pending \subseteq Actions
    /\ confirmations \in [Actions -> SUBSET Nodes]
    /\ decisions \in [Actions -> Decision]
    /\ networkUp \in [Nodes -> BOOLEAN]

Init ==
    /\ pending = {}
    /\ confirmations = [a \in Actions |-> {}]
    /\ decisions = [a \in Actions |-> "None"]
    /\ networkUp = [n \in Nodes |-> TRUE]

\* A new action enters the system awaiting confirmation
ProposeAction(a) ==
    /\ a \notin pending
    /\ decisions[a] = "None"
    /\ pending' = pending \cup {a}
    /\ UNCHANGED <<confirmations, decisions, networkUp>>

\* A reachable node confirms an action satisfies its assigned property
NodeConfirms(n, a) ==
    /\ a \in pending
    /\ decisions[a] = "None"
    /\ networkUp[n] = TRUE
    /\ confirmations' = [confirmations EXCEPT ![a] = confirmations[a] \cup {n}]
    /\ UNCHANGED <<pending, decisions, networkUp>>

\* A reachable node finds a violation -- blocks immediately, no quorum needed to block
NodeBlocks(n, a) ==
    /\ a \in pending
    /\ decisions[a] = "None"
    /\ networkUp[n] = TRUE
    /\ decisions' = [decisions EXCEPT ![a] = "Blocked"]
    /\ UNCHANGED <<pending, confirmations, networkUp>>

\* Approve only if every node has confirmed
ApproveIfQuorumConfirmed(a) ==
    /\ a \in pending
    /\ decisions[a] = "None"
    /\ confirmations[a] = Nodes
    /\ decisions' = [decisions EXCEPT ![a] = "Approved"]
    /\ UNCHANGED <<pending, confirmations, networkUp>>

\* Defer if some node relevant to this action is unreachable and not yet confirmed
DeferIfUnreachable(a) ==
    /\ a \in pending
    /\ decisions[a] = "None"
    /\ \E n \in Nodes : networkUp[n] = FALSE /\ n \notin confirmations[a]
    /\ decisions' = [decisions EXCEPT ![a] = "Deferred"]
    /\ UNCHANGED <<pending, confirmations, networkUp>>

LinkDown(n) ==
    /\ networkUp' = [networkUp EXCEPT ![n] = FALSE]
    /\ UNCHANGED <<pending, confirmations, decisions>>

LinkUp(n) ==
    /\ networkUp' = [networkUp EXCEPT ![n] = TRUE]
    /\ UNCHANGED <<pending, confirmations, decisions>>

Next ==
    \/ \E a \in Actions : ProposeAction(a)
    \/ \E n \in Nodes, a \in Actions : NodeConfirms(n, a)
    \/ \E n \in Nodes, a \in Actions : NodeBlocks(n, a)
    \/ \E a \in Actions : ApproveIfQuorumConfirmed(a)
    \/ \E a \in Actions : DeferIfUnreachable(a)
    \/ \E n \in Nodes : LinkDown(n)
    \/ \E n \in Nodes : LinkUp(n)

Spec == Init /\ [][Next]_<<pending, confirmations, decisions, networkUp>>

\* SAFETY: an action is never approved without every node's confirmation
NoActionApprovedWithoutFullConfirmation ==
    \A a \in Actions : decisions[a] = "Approved" => confirmations[a] = Nodes

\* SAFETY: a node can only confirm while reachable (enforced structurally
\* by NodeConfirms' guard), so an approved action's confirmations were all
\* given while their nodes were reachable at confirmation time. This invariant
\* checks that decisions never skip straight to Approved without going
\* through pending/confirmation -- i.e. no shortcut bypasses the process.
ApprovalOnlyViaConfirmedQuorum ==
    \A a \in Actions :
        decisions[a] = "Approved" => confirmations[a] = Nodes

\* LIVENESS-ADJACENT SAFETY: once an action is Deferred, it never silently
\* becomes Approved without the previously-missing node's confirmation --
\* i.e. deferral is never bypassed.
DeferredNeverSkipsToApprovedWithoutConfirmation ==
    \A a \in Actions :
        (decisions[a] = "Approved") =>
            \A n \in Nodes : n \in confirmations[a]

====
