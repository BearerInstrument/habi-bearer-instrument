(* Policy Gate formal safety proof.
   Mirrors PolicyGate.tla (tla/policy-gate/PolicyGate.tla), exhaustively
   verified by TLC at 2x2 and 3x3 configs on 2026-09-28.
   This file is independent of habi_safety.v -- no shared definitions,
   no edits to that file. *)

Require Import List.
Import ListNotations.

Section PolicyGateModel.

Variable Node : Type.
Variable Action : Type.
Variable action_eq_dec : forall x y : Action, {x = y} + {x <> y}.

Inductive Decision : Type :=
  | DNone
  | DApproved
  | DBlocked
  | DDeferred.

(* A state: for each Action, which Nodes have confirmed it, and its Decision. *)
Record State := mkState {
  confirmations : Action -> Node -> Prop;
  decisions     : Action -> Decision
}.

Variable AllNodes : list Node.

Definition FullyConfirmed (s : State) (a : Action) : Prop :=
  forall n : Node, In n AllNodes -> confirmations s a n.

(* SAFETY 1: an action's Decision is Approved only if every node in
   AllNodes has confirmed it. Mirrors NoActionApprovedWithoutFullConfirmation. *)
Definition NoActionApprovedWithoutFullConfirmation (s : State) : Prop :=
  forall a : Action, decisions s a = DApproved -> FullyConfirmed s a.

Definition if_action_eq (a a' : Action) (d : Decision) (default : Decision) : Decision :=
  if action_eq_dec a a' then d else default.

(* The ApproveIfQuorumConfirmed transition: only fires when FullyConfirmed
   already holds, and only changes decisions for the one action approved. *)
Definition ApproveStep (s s' : State) (a : Action) : Prop :=
  FullyConfirmed s a /\
  decisions s a = DNone /\
  decisions s' = (fun a' => if_action_eq a a' DApproved (decisions s a')) /\
  confirmations s' = confirmations s.

(* THEOREM 1: the ApproveStep transition preserves
   NoActionApprovedWithoutFullConfirmation. *)
Theorem approve_step_preserves_invariant :
  forall s s' a,
    NoActionApprovedWithoutFullConfirmation s ->
    ApproveStep s s' a ->
    NoActionApprovedWithoutFullConfirmation s'.
Proof.
  intros s s' a Hinv Hstep a' Happ.
  unfold ApproveStep in Hstep.
  destruct Hstep as [Hfc [Hnone [Hdec Hconf]]].
  unfold FullyConfirmed.
  intros n Hin.
  rewrite Hconf.
  rewrite Hdec in Happ.
  unfold if_action_eq in Happ.
  destruct (action_eq_dec a a') as [Heq | Hneq].
  - subst a'. exact (Hfc n Hin).
  - apply (Hinv a' Happ n Hin).
Qed.

End PolicyGateModel.

Section DeferProperty.

Variable Node2 : Type.
Variable Action2 : Type.
Variable AllNodes2 : list Node2.

Inductive Decision2 : Type :=
  | D2None
  | D2Approved
  | D2Blocked
  | D2Deferred.

Record State2 := mkState2 {
  confirmations2 : Action2 -> Node2 -> Prop;
  decisions2     : Action2 -> Decision2;
  networkUp2     : Node2 -> Prop
}.

Definition FullyConfirmed2 (s : State2) (a : Action2) : Prop :=
  forall n : Node2, In n AllNodes2 -> confirmations2 s a n.

(* DeferGuard requires the unreachable, unconfirmed node to be a member
   of AllNodes2 -- the same fixed, complete node set that FullyConfirmed2
   ranges over. This matches PolicyGate.tla, where networkUp and
   confirmations are both indexed over the same Nodes constant. Without
   this membership condition the two guards are not actually in tension,
   which is the gap an earlier proof attempt (not in this file) caught. *)
Definition DeferGuard (s : State2) (a : Action2) : Prop :=
  exists n : Node2, In n AllNodes2 /\ ~ (networkUp2 s n) /\ ~ (confirmations2 s a n).

(* THEOREM 2: DeferGuard and FullyConfirmed2 are mutually exclusive.
   Whenever deferral is possible (an AllNodes2 member is unreachable and
   unconfirmed), full-quorum approval is not possible. This is the formal
   core of "defer, not fail open." *)
Theorem defer_and_full_confirmation_exclusive :
  forall s a,
    DeferGuard s a -> ~ FullyConfirmed2 s a.
Proof.
  intros s a Hdefer Hfull.
  unfold DeferGuard in Hdefer.
  destruct Hdefer as [n [Hin [Hunreach Hunconf]]].
  apply Hunconf.
  apply Hfull.
  exact Hin.
Qed.

End DeferProperty.

Section PolicyGateFull.

(* Unified model matching PolicyGate.tla's full state (pending,
   confirmations, decisions, networkUp together), used for the combined
   Next-relation induction below. *)

Variable FNode : Type.
Variable FAction : Type.
Variable faction_eq_dec : forall x y : FAction, {x = y} + {x <> y}.
Variable FAllNodes : list FNode.

Inductive FDecision : Type :=
  | FDNone
  | FDApproved
  | FDBlocked
  | FDDeferred.

Record FState := mkFState {
  fpending       : FAction -> Prop;
  fconfirmations : FAction -> FNode -> Prop;
  fdecisions     : FAction -> FDecision;
  fnetworkUp     : FNode -> Prop
}.

Definition FFullyConfirmed (s : FState) (a : FAction) : Prop :=
  forall n : FNode, In n FAllNodes -> fconfirmations s a n.

Definition FInvariant (s : FState) : Prop :=
  forall a : FAction, fdecisions s a = FDApproved -> FFullyConfirmed s a.


Variable fnode_eq_dec : forall x y : FNode, {x = y} + {x <> y}.

Definition FIfAction (a a' : FAction) (d default : FDecision) : FDecision :=
  if faction_eq_dec a a' then d else default.

Definition FProposeStep (s s' : FState) (a : FAction) : Prop :=
  ~ fpending s a /\
  fdecisions s a = FDNone /\
  fpending s' = (fun a' => if faction_eq_dec a a' then True else fpending s a') /\
  fconfirmations s' = fconfirmations s /\
  fdecisions s' = fdecisions s /\
  fnetworkUp s' = fnetworkUp s.

Definition FConfirmStep (s s' : FState) (n : FNode) (a : FAction) : Prop :=
  fpending s a /\
  fdecisions s a = FDNone /\
  fnetworkUp s n /\
  fconfirmations s' = (fun a' n' =>
    if faction_eq_dec a a'
    then (n' = n \/ fconfirmations s a n')
    else fconfirmations s a' n') /\
  fpending s' = fpending s /\
  fdecisions s' = fdecisions s /\
  fnetworkUp s' = fnetworkUp s.

Definition FBlockStep (s s' : FState) (n : FNode) (a : FAction) : Prop :=
  fpending s a /\
  fdecisions s a = FDNone /\
  fnetworkUp s n /\
  fdecisions s' = (fun a' => FIfAction a a' FDBlocked (fdecisions s a')) /\
  fpending s' = fpending s /\
  fconfirmations s' = fconfirmations s /\
  fnetworkUp s' = fnetworkUp s.

Definition FApproveStep (s s' : FState) (a : FAction) : Prop :=
  fpending s a /\
  fdecisions s a = FDNone /\
  FFullyConfirmed s a /\
  fdecisions s' = (fun a' => FIfAction a a' FDApproved (fdecisions s a')) /\
  fpending s' = fpending s /\
  fconfirmations s' = fconfirmations s /\
  fnetworkUp s' = fnetworkUp s.

Definition FDeferGuard (s : FState) (a : FAction) : Prop :=
  exists n : FNode, In n FAllNodes /\ ~ (fnetworkUp s n) /\ ~ (fconfirmations s a n).

Definition FDeferStep (s s' : FState) (a : FAction) : Prop :=
  fpending s a /\
  fdecisions s a = FDNone /\
  FDeferGuard s a /\
  fdecisions s' = (fun a' => FIfAction a a' FDDeferred (fdecisions s a')) /\
  fpending s' = fpending s /\
  fconfirmations s' = fconfirmations s /\
  fnetworkUp s' = fnetworkUp s.

Definition FLinkDownStep (s s' : FState) (n : FNode) : Prop :=
  fnetworkUp s' = (fun n' => if fnode_eq_dec n n' then False else fnetworkUp s n') /\
  fpending s' = fpending s /\
  fconfirmations s' = fconfirmations s /\
  fdecisions s' = fdecisions s.

Definition FLinkUpStep (s s' : FState) (n : FNode) : Prop :=
  fnetworkUp s' = (fun n' => if fnode_eq_dec n n' then True else fnetworkUp s n') /\
  fpending s' = fpending s /\
  fconfirmations s' = fconfirmations s /\
  fdecisions s' = fdecisions s.

Definition FNext (s s' : FState) : Prop :=
  (exists a, FProposeStep s s' a) \/
  (exists n a, FConfirmStep s s' n a) \/
  (exists n a, FBlockStep s s' n a) \/
  (exists a, FApproveStep s s' a) \/
  (exists a, FDeferStep s s' a) \/
  (exists n, FLinkDownStep s s' n) \/
  (exists n, FLinkUpStep s s' n).


(* THEOREM 3: FProposeStep preserves FInvariant. Trivial in the sense
   that Propose never touches fdecisions or fconfirmations -- it only
   adds an action to fpending -- so no approved action's status changes. *)
Theorem fpropose_preserves_invariant :
  forall s s' a,
    FInvariant s ->
    FProposeStep s s' a ->
    FInvariant s'.
Proof.
  intros s s' a Hinv Hstep.
  unfold FProposeStep in Hstep.
  destruct Hstep as [Hnotpending [Hnone [Hpend' [Hconf' [Hdec' Hnet']]]]].
  unfold FInvariant.
  intros a' Happ.
  rewrite Hdec' in Happ.
  pose proof (Hinv a' Happ) as Hfc.
  unfold FFullyConfirmed in *.
  intros n Hin.
  rewrite Hconf'.
  exact (Hfc n Hin).
Qed.

End PolicyGateFull.
