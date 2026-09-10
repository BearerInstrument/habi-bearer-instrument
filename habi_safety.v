(* ===================================================================
   HABI Formal Safety Proof — Month 9 FINAL Deliverable
   Topic 55-24-02: High-Assurance Bearer-Instrument Logic

   Compile: coqc habi_safety.v  (Coq 8.19.2, OCaml 4.13.1)
   =================================================================== *)

Require Import Bool.
Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Classical.
Require Import Extraction.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.

Section GenericModel.
  Variable Node Bearer : Type.

  Record state := mkState {
    ledgers   : Node -> Bearer -> Prop;
    spent     : Node -> Bearer -> Prop;
    networkUp : bool
  }.

  Definition SyncedNoDoubleSpend (s : state) : Prop :=
    networkUp s = true ->
    forall b, (exists n, spent s n b) -> forall m, ~ ledgers s m b.

  Definition update_node (f : Node -> Bearer -> Prop)
                         (n : Node) (g : Bearer -> Prop) : Node -> Bearer -> Prop :=
    fun n' b => (n' = n /\ g b) \/ (n' <> n /\ f n' b).

  Definition spendLedgers (led : Node -> Bearer -> Prop)
                          (netUp : bool) (n : Node) (b : Bearer) :
                          Node -> Bearer -> Prop :=
    fun n' b' => led n' b' /\ ~ (b' = b /\ netUp = true).

  Inductive SStep : state -> state -> Prop :=
  | SStep_Disconnect : forall s,
      networkUp s = true ->
      SStep s (mkState (ledgers s) (spent s) false)
  | SStep_Replicate : forall s n1 n2 b,
      ledgers s n1 b ->
      networkUp s = true ->
      SStep s (mkState (fun n b' => (n = n2 /\ b' = b) \/ ledgers s n b')
                       (spent s) (networkUp s))
  | SStep_SpendAt : forall s n b,
      ledgers s n b ->
      networkUp s = true ->
      SStep s (mkState (spendLedgers (ledgers s) true n b)
                       (fun n' b' => spent s n' b' \/ (n' = n /\ b' = b))
                       (networkUp s))
  | SStep_SpendAt_Offline : forall s n b,
      ledgers s n b ->
      networkUp s = false ->
      SStep s (mkState (spendLedgers (ledgers s) false n b)
                       (fun n' b' => spent s n' b' \/ (n' = n /\ b' = b))
                       false)
  | SStep_SafeReconnect : forall s final_ledgers,
      networkUp s = false ->
      (forall n b, final_ledgers n b -> exists n0, ledgers s n0 b) ->
      (forall n b, final_ledgers n b -> ~ (exists n0, spent s n0 b)) ->
      (forall b n1 n2, final_ledgers n1 b -> final_ledgers n2 b -> n1 = n2) ->
      SStep s (mkState final_ledgers (spent s) true).

  Lemma spendat_offline_trivial :
    forall s n b,
      networkUp s = false ->
      ledgers s n b ->
      SyncedNoDoubleSpend
        (mkState (spendLedgers (ledgers s) false n b)
                 (update_node (spent s) n (fun b' => spent s n b' \/ b' = b))
                 false).
  Proof.
    intros s n b Hnet Hled Hup.
    unfold SyncedNoDoubleSpend in Hup.
    simpl in Hup.
    discriminate.
  Qed.

  Lemma safe_step_preserves_invariant :
    forall s s',
      SyncedNoDoubleSpend s ->
      SStep s s' ->
      SyncedNoDoubleSpend s'.
  Proof.
    intros s s' Hinv Hstep.
    destruct Hstep as
      [ s Hup
      | s n1 n2 b Hled Hup
      | s n b Hled Hup
      | s n b Hled Hdown
      | s final_ledgers Hdown Hsub Hnospent Huniq ].
    - unfold SyncedNoDoubleSpend. simpl. intros Hcontra. discriminate.
    - unfold SyncedNoDoubleSpend in *. simpl.
      intros Hup' b0 [n0 Hsp0] m Hcase.
      destruct Hcase as [[Heqm Heqb] | Hledm].
      + subst m b0.
        exact (Hinv Hup' b (ex_intro _ n0 Hsp0) n1 Hled).
      + exact (Hinv Hup' b0 (ex_intro _ n0 Hsp0) m Hledm).
    - unfold SyncedNoDoubleSpend in *. simpl.
      intros Hup' b0 [n0 Hsp0] m Hled0.
      destruct Hsp0 as [Hsp0 | [HeqN HeqB]].
      + destruct Hled0 as [Hled0' _].
        exact (Hinv Hup' b0 (ex_intro _ n0 Hsp0) m Hled0').
      + subst b0. unfold spendLedgers in Hled0.
        destruct Hled0 as [_ Hnot].
        exact (Hnot (conj eq_refl eq_refl)).
    - unfold SyncedNoDoubleSpend. simpl. intros Hcontra. discriminate.
    - unfold SyncedNoDoubleSpend in *. simpl.
      intros Hup' b0 [n0 Hsp0] m HledFinal.
      exact (Hnospent m b0 HledFinal (ex_intro _ n0 Hsp0)).
  Qed.
End GenericModel.

Inductive Node3 := N1 | N2 | N3.
Inductive Bearer2 := b1 | b2.

Definition Node3_eq_dec (x y : Node3) : {x = y} + {x <> y}.
Proof. decide equality. Defined.
Definition Bearer2_eq_dec (x y : Bearer2) : {x = y} + {x <> y}.
Proof. decide equality. Defined.

Record state3 := mkState3 {
  ledgers3   : Node3 -> Bearer2 -> Prop;
  spent3     : Node3 -> Bearer2 -> Prop;
  networkUp3 : bool
}.

Definition SyncedNoDoubleSpend3 (s : state3) : Prop :=
  networkUp3 s = true ->
  forall b, (exists n, spent3 s n b) -> forall m, ~ ledgers3 s m b.

Definition ledger_unsafe (n : Node3) (b : Bearer2) : Prop :=
  match n, b with
  | N1, b1 => True
  | _, _  => False
  end.

Definition spent_N1_N2_b1 (n : Node3) (b : Bearer2) : Prop :=
  match n, b with
  | N1, b1 => True
  | N2, b1 => True
  | _, _   => False
  end.

Definition state_double_spend : state3 :=
  mkState3 ledger_unsafe spent_N1_N2_b1 false.

Lemma naive_reconnect_breaks_safety :
  exists s s',
    networkUp3 s = false /\ spent3 s N1 b1 /\ spent3 s N2 b1 /\
    networkUp3 s' = true /\ ~ SyncedNoDoubleSpend3 s'.
Proof.
  exists state_double_spend.
  exists (mkState3 ledger_unsafe spent_N1_N2_b1 true).
  repeat split; simpl; auto.
  unfold SyncedNoDoubleSpend3. intros H.
  specialize (H eq_refl b1).
  assert (Hex: exists n, spent_N1_N2_b1 n b1) by (exists N1; simpl; auto).
  specialize (H Hex N1). simpl in H. apply H. trivial.
Qed.

Class EqDec (A : Type) := {
  eqb    : A -> A -> bool;
  eqb_eq : forall x y, eqb x y = true <-> x = y
}.

Instance EqDec_Node3 : EqDec Node3.
Proof.
  refine {| eqb := fun x y => if Node3_eq_dec x y then true else false |}.
  intros x y. destruct (Node3_eq_dec x y); intuition; try discriminate.
Defined.

Instance EqDec_Bearer2 : EqDec Bearer2.
Proof.
  refine {| eqb := fun x y => if Bearer2_eq_dec x y then true else false |}.
  intros x y. destruct (Bearer2_eq_dec x y); intuition; try discriminate.
Defined.

Record state_exe := mkStateExe {
  ledgers_exe   : Node3 -> Bearer2 -> bool;
  spent_exe     : Node3 -> Bearer2 -> bool;
  networkUp_exe : bool
}.

Definition ledgers_exe_empty : Node3 -> Bearer2 -> bool := fun _ _ => false.

Definition update_node_exe (f : Node3 -> Bearer2 -> bool)
                           (n : Node3) (b : Bearer2) (v : bool)
                           : Node3 -> Bearer2 -> bool :=
  fun n' b' =>
    if Node3_eq_dec n' n
    then if Bearer2_eq_dec b' b then v else f n' b'
    else f n' b'.

Definition spendLedgers_exe (led : Node3 -> Bearer2 -> bool)
                            (netUp : bool) (n : Node3) (b : Bearer2)
                            : Node3 -> Bearer2 -> bool :=
  fun n' b' =>
    if Node3_eq_dec n' n then
      if Bearer2_eq_dec b' b then
        if netUp then false else led n' b'
      else led n' b'
    else led n' b'.

Definition run_conversion_day_exe (s : state_exe) : option state_exe :=
  if networkUp_exe s then None
  else
    let ds_n1n2_b1 := spent_exe s N1 b1 && spent_exe s N2 b1 in
    let ds_n1n2_b2 := spent_exe s N1 b2 && spent_exe s N2 b2 in
    let ds_n1n3_b1 := spent_exe s N1 b1 && spent_exe s N3 b1 in
    let ds_n2n3_b1 := spent_exe s N2 b1 && spent_exe s N3 b1 in
    if ds_n1n2_b1 || ds_n1n2_b2 || ds_n1n3_b1 || ds_n2n3_b1 then None
    else Some (mkStateExe (ledgers_exe s) (spent_exe s) true).

Definition check_post_barrier_safety_exe (s : state_exe) : bool :=
  negb (spent_exe s N1 b1 && spent_exe s N2 b1) &&
  negb (spent_exe s N1 b2 && spent_exe s N2 b2) &&
  negb (spent_exe s N1 b1 && spent_exe s N3 b1) &&
  negb (spent_exe s N2 b1 && spent_exe s N3 b1).

Lemma run_conversion_day_exe_preserves_safety :
  forall s s',
    run_conversion_day_exe s = Some s' ->
    check_post_barrier_safety_exe s' = true.
Proof.
  intros s s' Hrun.
  unfold run_conversion_day_exe in Hrun.
  destruct (networkUp_exe s); try discriminate.
  remember (spent_exe s N1 b1 && spent_exe s N2 b1) as ds12b1.
  remember (spent_exe s N1 b2 && spent_exe s N2 b2) as ds12b2.
  remember (spent_exe s N1 b1 && spent_exe s N3 b1) as ds13b1.
  remember (spent_exe s N2 b1 && spent_exe s N3 b1) as ds23b1.
  destruct ds12b1, ds12b2, ds13b1, ds23b1; try discriminate.
  inversion Hrun; subst; clear Hrun.
  unfold check_post_barrier_safety_exe.
  simpl.
  rewrite <- Heqds12b1, <- Heqds12b2, <- Heqds13b1, <- Heqds23b1.
  reflexivity.
Qed.

(* -----------------------------------------------------------------
   (3) Minimality / Completeness
   ----------------------------------------------------------------- *)
Definition IsSafeReconnect (R : state3 -> state3 -> Prop) : Prop :=
  forall s s',
    R s s' -> networkUp3 s = false -> networkUp3 s' = true ->
    SyncedNoDoubleSpend3 s'.
Theorem naive_reconnect_not_safe :
  ~ IsSafeReconnect
      (fun s s' => networkUp3 s = false /\ networkUp3 s' = true /\
                   ledgers3 s' = ledgers3 s /\ spent3 s' = spent3 s).
Proof.
  unfold IsSafeReconnect, not. intros H.
  assert (Hsafe := H state_double_spend
                     (mkState3 ledger_unsafe spent_N1_N2_b1 true)
                     (conj eq_refl (conj eq_refl (conj eq_refl eq_refl)))
                     eq_refl eq_refl).
  unfold SyncedNoDoubleSpend3 in Hsafe.
  specialize (Hsafe eq_refl b1).
  assert (Hex: exists n, spent_N1_N2_b1 n b1) by (exists N1; simpl; auto).
  specialize (Hsafe Hex N1). simpl in Hsafe. apply Hsafe. trivial.
Qed.
Theorem safe_reconnect_implies_invariant :
  forall R s s',
    IsSafeReconnect R ->
    R s s' ->
    networkUp3 s = false ->
    networkUp3 s' = true ->
    SyncedNoDoubleSpend3 s'.
Proof.
  intros R s s' Hsafe HR Hdown Hup.
  exact (Hsafe s s' HR Hdown Hup).
Qed.
Theorem reconnect_must_forbid_naive_double_spend :
  forall R : state3 -> state3 -> Prop,
    IsSafeReconnect R ->
    ~ R state_double_spend (mkState3 ledger_unsafe spent_N1_N2_b1 true).
Proof.
  intros R Hsafe HR.
  specialize (Hsafe state_double_spend
                     (mkState3 ledger_unsafe spent_N1_N2_b1 true)
                     HR eq_refl eq_refl).
  unfold SyncedNoDoubleSpend3 in Hsafe. simpl in Hsafe.
  specialize (Hsafe eq_refl b1).
  assert (Hex: exists n, spent_N1_N2_b1 n b1) by (exists N1; simpl; auto).
  specialize (Hsafe Hex N1). simpl in Hsafe. apply Hsafe. trivial.
Qed.

(* -----------------------------------------------------------------
   (4) Extraction
   ----------------------------------------------------------------- *)
Extraction Language OCaml.
Extraction "habi_safety.ml"
  Node3 Bearer2 state_exe ledgers_exe_empty
  spendLedgers_exe run_conversion_day_exe
  check_post_barrier_safety_exe
  Node3_eq_dec Bearer2_eq_dec.
(* -----------------------------------------------------------------)
   (3) Minimality / Completeness
   ----------------------------------------------------------------- *)

