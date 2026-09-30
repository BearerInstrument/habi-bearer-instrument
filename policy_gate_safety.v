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


(* THEOREM 4: FConfirmStep preserves FInvariant. Confirm never changes
   fdecisions, so any already-approved action stays approved with the
   same status; its confirmations set only grows, never shrinks, for
   the one action being confirmed, and is untouched for every other
   action. *)
Theorem fconfirm_preserves_invariant :
  forall s s' n a,
    FInvariant s ->
    FConfirmStep s s' n a ->
    FInvariant s'.
Proof.
  intros s s' n a Hinv Hstep.
  unfold FConfirmStep in Hstep.
  destruct Hstep as [Hpend [Hnone [Hup [Hconf' [Hpend' [Hdec' Hnet']]]]]].
  unfold FInvariant.
  intros b Happ.
  rewrite Hdec' in Happ.
  pose proof (Hinv b Happ) as Hfc.
  unfold FFullyConfirmed in *.
  intros n0 Hin0.
  rewrite Hconf'.
  simpl.
  destruct (faction_eq_dec a b) as [Heq | Hneq].
  - subst b. right. exact (Hfc n0 Hin0).
  - exact (Hfc n0 Hin0).
Qed.

(* THEOREM 5: FBlockStep preserves FInvariant. Block only ever sets a
   decision to FDBlocked, never FDApproved, so no action can become
   "approved" via a Block step -- the FDApproved case for the blocked
   action itself is a contradiction (discriminate), and every other
   action's decision and confirmations are untouched. *)
Theorem fblock_preserves_invariant :
  forall s s' n a,
    FInvariant s ->
    FBlockStep s s' n a ->
    FInvariant s'.
Proof.
  intros s s' n a Hinv Hstep.
  unfold FBlockStep in Hstep.
  destruct Hstep as [Hpend [Hnone [Hup [Hdec' [Hpend' [Hconf' Hnet']]]]]].
  unfold FInvariant.
  intros b Happ.
  destruct (faction_eq_dec a b) as [Heq | Hneq].
  - subst b.
    rewrite Hdec' in Happ.
    unfold FIfAction in Happ.
    destruct (faction_eq_dec a a) as [Heq2 | Hneq2].
    + discriminate Happ.
    + exfalso. apply Hneq2. reflexivity.
  - rewrite Hdec' in Happ.
    unfold FIfAction in Happ.
    destruct (faction_eq_dec a b) as [Heq3 | Hneq3].
    + contradiction.
    + pose proof (Hinv b Happ) as Hfc.
      unfold FFullyConfirmed in *.
      intros n0 Hin0.
      rewrite Hconf'.
      exact (Hfc n0 Hin0).
Qed.


(* THEOREM 6: FDeferStep preserves FInvariant. Defer only ever sets a
   decision to FDDeferred, never FDApproved -- same shape as the Block
   proof above. *)
Theorem fdefer_preserves_invariant :
  forall s s' a,
    FInvariant s ->
    FDeferStep s s' a ->
    FInvariant s'.
Proof.
  intros s s' a Hinv Hstep.
  unfold FDeferStep in Hstep.
  destruct Hstep as [Hpend [Hnone [Hguard [Hdec' [Hpend' [Hconf' Hnet']]]]]].
  unfold FInvariant.
  intros b Happ.
  destruct (faction_eq_dec a b) as [Heq | Hneq].
  - subst b.
    rewrite Hdec' in Happ.
    unfold FIfAction in Happ.
    destruct (faction_eq_dec a a) as [Heq2 | Hneq2].
    + discriminate Happ.
    + exfalso. apply Hneq2. reflexivity.
  - rewrite Hdec' in Happ.
    unfold FIfAction in Happ.
    destruct (faction_eq_dec a b) as [Heq3 | Hneq3].
    + contradiction.
    + pose proof (Hinv b Happ) as Hfc.
      unfold FFullyConfirmed in *.
      intros n0 Hin0.
      rewrite Hconf'.
      exact (Hfc n0 Hin0).
Qed.

(* THEOREM 7: FLinkDownStep preserves FInvariant. LinkDown only changes
   fnetworkUp -- fdecisions and fconfirmations are untouched, so nothing
   about which actions are approved or confirmed can change. *)
Theorem flinkdown_preserves_invariant :
  forall s s' n,
    FInvariant s ->
    FLinkDownStep s s' n ->
    FInvariant s'.
Proof.
  intros s s' n Hinv Hstep.
  unfold FLinkDownStep in Hstep.
  destruct Hstep as [Hnet' [Hpend' [Hconf' Hdec']]].
  unfold FInvariant.
  intros b Happ.
  rewrite Hdec' in Happ.
  pose proof (Hinv b Happ) as Hfc.
  unfold FFullyConfirmed in *.
  intros n0 Hin0.
  rewrite Hconf'.
  exact (Hfc n0 Hin0).
Qed.

(* THEOREM 8: FLinkUpStep preserves FInvariant. Same reasoning as
   FLinkDownStep -- only fnetworkUp changes. *)
Theorem flinkup_preserves_invariant :
  forall s s' n,
    FInvariant s ->
    FLinkUpStep s s' n ->
    FInvariant s'.
Proof.
  intros s s' n Hinv Hstep.
  unfold FLinkUpStep in Hstep.
  destruct Hstep as [Hnet' [Hpend' [Hconf' Hdec']]].
  unfold FInvariant.
  intros b Happ.
  rewrite Hdec' in Happ.
  pose proof (Hinv b Happ) as Hfc.
  unfold FFullyConfirmed in *.
  intros n0 Hin0.
  rewrite Hconf'.
  exact (Hfc n0 Hin0).
Qed.

(* THEOREM 9: FApproveStep preserves FInvariant. This is the one step
   where an action genuinely becomes FDApproved. For the approved action
   itself, the FFullyConfirmed guard of the step supplies the needed
   confirmations, and fconfirmations is unchanged by the step. For every
   other action, fdecisions and fconfirmations are untouched, so the
   invariant carries over from the pre-state. *)
Theorem fapprove_preserves_invariant :
  forall s s' a,
    FInvariant s ->
    FApproveStep s s' a ->
    FInvariant s'.
Proof.
  intros s s' a Hinv Hstep.
  unfold FApproveStep in Hstep.
  destruct Hstep as [Hpend [Hnone [Hfc [Hdec' [Hpend' [Hconf' Hnet']]]]]].
  unfold FInvariant.
  intros b Happ.
  destruct (faction_eq_dec a b) as [Heq | Hneq].
  - subst b.
    unfold FFullyConfirmed in *.
    intros n0 Hin0.
    rewrite Hconf'.
    exact (Hfc n0 Hin0).
  - rewrite Hdec' in Happ.
    unfold FIfAction in Happ.
    destruct (faction_eq_dec a b) as [Heq3 | Hneq3].
    + contradiction.
    + pose proof (Hinv b Happ) as Hfc2.
      unfold FFullyConfirmed in *.
      intros n0 Hin0.
      rewrite Hconf'.
      exact (Hfc2 n0 Hin0).
Qed.

(* Initial state, mirroring Init in PolicyGate.tla: nothing pending,
   no confirmations, every decision FDNone, every node's link up. *)
Definition FInit (s : FState) : Prop :=
  fpending s = (fun _ => False) /\
  fconfirmations s = (fun _ _ => False) /\
  fdecisions s = (fun _ => FDNone) /\
  fnetworkUp s = (fun _ => True).

(* THEOREM 10: every FInit state satisfies FInvariant. No action is
   FDApproved at Init (every decision is FDNone), so the invariant
   holds vacuously. *)
Theorem finit_satisfies_invariant :
  forall s,
    FInit s ->
    FInvariant s.
Proof.
  intros s Hinit.
  unfold FInit in Hinit.
  destruct Hinit as [Hpend [Hconf [Hdec Hnet]]].
  unfold FInvariant.
  intros a Happ.
  rewrite Hdec in Happ.
  discriminate Happ.
Qed.

(* Reachable states: any FInit state is reachable, and if s is
   reachable and FNext s s' holds, then s' is reachable. This is the
   Coq counterpart of the behaviors TLC explores from Init via Next. *)
Inductive Reachable : FState -> Prop :=
  | Reachable_init : forall s, FInit s -> Reachable s
  | Reachable_step : forall s s',
      Reachable s -> FNext s s' -> Reachable s'.

(* THEOREM 11: FInvariant holds in every reachable state. By induction
   on Reachable: the base case is finit_satisfies_invariant, and the step
   case splits FNext into its seven disjuncts and applies the matching
   per-step preservation lemma to the induction hypothesis. *)
Theorem reachable_preserves_invariant :
  forall s,
    Reachable s ->
    FInvariant s.
Proof.
  intros s Hreach.
  induction Hreach as [s0 Hinit | s0 s1 Hreach0 IH Hnext].
  - exact (finit_satisfies_invariant s0 Hinit).
  - destruct Hnext as
      [ [a Hstep]
      | [ [n [a Hstep]]
      | [ [n [a Hstep]]
      | [ [a Hstep]
      | [ [a Hstep]
      | [ [n Hstep]
      | [n Hstep] ] ] ] ] ] ].
    + exact (fpropose_preserves_invariant s0 s1 a IH Hstep).
    + exact (fconfirm_preserves_invariant s0 s1 n a IH Hstep).
    + exact (fblock_preserves_invariant s0 s1 n a IH Hstep).
    + exact (fapprove_preserves_invariant s0 s1 a IH Hstep).
    + exact (fdefer_preserves_invariant s0 s1 a IH Hstep).
    + exact (flinkdown_preserves_invariant s0 s1 n IH Hstep).
    + exact (flinkup_preserves_invariant s0 s1 n IH Hstep).
Qed.

(* ---------------------------------------------------------------
   Liveness infrastructure (in progress, not yet part of any proven
   theorem). An FTrace is an infinite sequence of states. ValidTrace
   requires the trace to start at an FInit state and to advance by
   FNext at every step. ApproveEnabled captures exactly the guard of
   FApproveStep -- pending, undecided, fully confirmed -- without
   asserting a successor state exists (it always does, so the
   existential form would be trivial). WeaklyFairApprove is the
   standard weak-fairness condition: if approving a stays
   continuously enabled from index n onward, some FApproveStep for a
   actually occurs at or after n.
   ------------------------------------------------------------- *)

Definition FTrace : Type := nat -> FState.

Definition ValidTrace (tr : FTrace) : Prop :=
  FInit (tr 0) /\
  forall i : nat, FNext (tr i) (tr (S i)).

Definition ApproveEnabled (s : FState) (a : FAction) : Prop :=
  fpending s a /\
  fdecisions s a = FDNone /\
  FFullyConfirmed s a.

Definition ApproveOccursAt (tr : FTrace) (a : FAction) (j : nat) : Prop :=
  FApproveStep (tr j) (tr (S j)) a.

(* WeaklyFairApprove encodes standard weak fairness for FApproveStep
   (the LTL formula []<>enabled -> []<>taken) via a shifting starting
   index n: for every point n onward, if at each index the step is
   either still enabled or has already occurred by then, the step
   occurs by some j >= n. This is a HYPOTHESIS about which traces
   count as fair, not something proven here -- the same role fairness
   plays in a TLA+ spec. Because the "occurred by i" disjunct is what
   the theorem below concludes, approve_eventually's proof is
   intentionally thin: the substantive claim is that a trace
   satisfying this hypothesis is assumed, not that the derivation
   from it is deep. *)
Definition WeaklyFairApprove (tr : FTrace) (a : FAction) : Prop :=
  forall n : nat,
    (forall i : nat, i >= n ->
       ApproveEnabled (tr i) a \/ (exists k, n <= k <= i /\ ApproveOccursAt tr a k)) ->
    exists j : nat, j >= n /\ ApproveOccursAt tr a j.


(* THEOREM (liveness): under WeaklyFairApprove for action a, if from
   n onward a is always either enabled-or-already-occurred, then a is
   approved by some j >= n. The proof is intentionally short: fairness
   already supplies the occurrence (as ApproveOccursAt); what remains
   is unfolding FApproveStep to read fdecisions off Hdec', matching
   the pattern used throughout this file for the other step lemmas. *)
Theorem approve_eventually :
  forall (tr : FTrace) (a : FAction),
    ValidTrace tr ->
    WeaklyFairApprove tr a ->
    forall n : nat,
      (forall i : nat, i >= n ->
         ApproveEnabled (tr i) a \/ (exists k, n <= k <= i /\ ApproveOccursAt tr a k)) ->
      exists j : nat, j >= n /\ fdecisions (tr j) a = FDApproved.
Proof.
  intros tr a Hvalid Hfair n Hpremise.
  destruct (Hfair n Hpremise) as [j [Hjn Hoccurs]].
  unfold ApproveOccursAt in Hoccurs.
  unfold FApproveStep in Hoccurs.
  destruct Hoccurs as [Hpend [Hnone [Hfc [Hdec' [Hpend' [Hconf' Hnet']]]]]].
  exists (S j).
  split.
  - apply le_S. exact Hjn.
  - rewrite Hdec'.
    unfold FIfAction.
    destruct (faction_eq_dec a a) as [Heq | Hneq].
    + reflexivity.
    + exfalso. apply Hneq. reflexivity.
Qed.

End PolicyGateFull.
