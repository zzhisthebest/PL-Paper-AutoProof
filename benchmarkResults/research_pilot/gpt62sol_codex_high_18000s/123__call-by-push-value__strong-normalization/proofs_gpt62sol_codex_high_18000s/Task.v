Require Import CBPV.SyntacticTyping CBPV.AbstractReductionSystems CBPV.StrongReduction.

Set Implicit Arguments.

Require Import Logic List.

Require Import Classes.Morphisms.

Import List Notations.

From Stdlib Require Import Arith.PeanoNat Logic.Eqdep_dec.

(* All substitution equations below use pointwise equality of environments. *)
Local Ltac cbpv_syntax_ind :=
  apply mutind_val_comp; intros; cbn [ren_value ren_comp subst_value subst_comp];
  f_equal; eauto.

Local Ltac cbpv_lift_simpl :=
  cbv beta iota zeta delta
    [upRen_value_value up_ren up_value_value scons funcomp shift bound var_zero
     ren_value subst_value];
  first [reflexivity | assumption |
    match goal with
    | H : forall i, _ = _ |- _ => solve [rewrite H; reflexivity]
    end].

Local Ltac cbpv_lift :=
  intros [i|]; first [cbpv_lift_simpl | destruct i as [i|]; cbpv_lift_simpl].

Lemma cbpv_ren_compose :
  forall n,
  (forall (v : value n) m k (r : fin n -> fin m) (q : fin m -> fin k)
      (p : fin n -> fin k), (forall i, q (r i) = p i) ->
      ren_value q (ren_value r v) = ren_value p v) /\
  (forall (c : comp n) m k (r : fin n -> fin m) (q : fin m -> fin k)
      (p : fin n -> fin k), (forall i, q (r i) = p i) ->
      ren_comp q (ren_comp r c) = ren_comp p c).
Proof.
  cbpv_syntax_ind;
    match goal with
    | H : forall m k r q p, _ -> _ = _ |- _ = _ => apply H
    end;
    cbpv_lift.
Qed.

Lemma cbpv_subst_ren :
  forall n,
  (forall (v : value n) m k (r : fin n -> fin m) (s : fin m -> value k)
      (t : fin n -> value k), (forall i, s (r i) = t i) ->
      subst_value s (ren_value r v) = subst_value t v) /\
  (forall (c : comp n) m k (r : fin n -> fin m) (s : fin m -> value k)
      (t : fin n -> value k), (forall i, s (r i) = t i) ->
      subst_comp s (ren_comp r c) = subst_comp t c).
Proof.
  cbpv_syntax_ind;
    match goal with
    | H : forall m k r s t, _ -> _ = _ |- _ = _ => apply H
    end;
    cbpv_lift.
Qed.

Lemma cbpv_ren_lift n m k (r : fin m -> fin k)
    (s : fin n -> value m) (t : fin n -> value k) :
  (forall i, ren_value r (s i) = t i) ->
  forall i, ren_value (upRen_value_value r) (up_value_value s i) =
      up_value_value t i.
Proof.
  intros H [i|]; [|reflexivity].
  cbv beta iota zeta delta [up_value_value scons funcomp].
  rewrite <- H.
  rewrite (proj1 (cbpv_ren_compose _) (s i) _ _ shift (upRen_value_value r)
    (fun j => shift (r j))) by reflexivity.
  symmetry. apply (proj1 (cbpv_ren_compose _)). reflexivity.
Qed.

Lemma cbpv_ren_subst :
  forall n,
  (forall (v : value n) m k (s : fin n -> value m) (r : fin m -> fin k)
      (t : fin n -> value k), (forall i, ren_value r (s i) = t i) ->
      ren_value r (subst_value s v) = subst_value t v) /\
  (forall (c : comp n) m k (s : fin n -> value m) (r : fin m -> fin k)
      (t : fin n -> value k), (forall i, ren_value r (s i) = t i) ->
      ren_comp r (subst_comp s c) = subst_comp t c).
Proof.
  cbpv_syntax_ind;
    match goal with
    | H : forall m k s r t, _ -> _ = _ |- _ = _ => apply H
    end; repeat apply cbpv_ren_lift; auto.
Qed.

Lemma cbpv_subst_lift n m k (s : fin n -> value m)
    (t : fin m -> value k) (p : fin n -> value k) :
  (forall i, subst_value t (s i) = p i) ->
  forall i, subst_value (up_value_value t) (up_value_value s i) =
      up_value_value p i.
Proof.
  intros H [i|]; [|reflexivity].
  change (subst_value (up_value_value t) (ren_value shift (s i)) =
    ren_value shift (p i)).
  rewrite <- H.
  rewrite (proj1 (cbpv_subst_ren _) (s i) _ _ shift (up_value_value t)
    (fun j => ren_value shift (t j))) by reflexivity.
  symmetry. apply (proj1 (cbpv_ren_subst _)). reflexivity.
Qed.

Lemma cbpv_subst_compose :
  forall n,
  (forall (v : value n) m k (s : fin n -> value m) (t : fin m -> value k)
      (p : fin n -> value k), (forall i, subst_value t (s i) = p i) ->
      subst_value t (subst_value s v) = subst_value p v) /\
  (forall (c : comp n) m k (s : fin n -> value m) (t : fin m -> value k)
      (p : fin n -> value k), (forall i, subst_value t (s i) = p i) ->
      subst_comp t (subst_comp s c) = subst_comp p c).
Proof.
  cbpv_syntax_ind;
    match goal with
    | H : forall m k s t p, _ -> _ = _ |- _ = _ => apply H
    end; repeat apply cbpv_subst_lift; auto.
Qed.

Lemma cbpv_subst_variables :
  forall n,
  (forall (v : value n) m (s : fin n -> value m) (r : fin n -> fin m),
      (forall i, s i = var_value (r i)) -> subst_value s v = ren_value r v) /\
  (forall (c : comp n) m (s : fin n -> value m) (r : fin n -> fin m),
      (forall i, s i = var_value (r i)) -> subst_comp s c = ren_comp r c).
Proof.
  cbpv_syntax_ind;
    match goal with
    | H : forall m s r, _ -> _ = _ |- _ = _ => apply H
    end; cbpv_lift.
Qed.

Lemma cbpv_ren_id :
  forall n,
  (forall (v : value n) (r : fin n -> fin n),
      (forall i, r i = i) -> ren_value r v = v) /\
  (forall (c : comp n) (r : fin n -> fin n),
      (forall i, r i = i) -> ren_comp r c = c).
Proof.
  cbpv_syntax_ind;
    match goal with
    | H : forall r, _ -> _ = _ |- _ = _ => apply H
    end;
    cbpv_lift.
Qed.

Lemma cbpv_subst_id n (c : comp n) :
  subst_comp (@var_value n) c = c.
Proof.
  rewrite (proj2 (cbpv_subst_variables _) c _ (@var_value n) (@idren n))
    by reflexivity.
  apply (proj2 (cbpv_ren_id _)). reflexivity.
Qed.

Definition cbpv_open1 n (c : comp (S n)) (v : value n) :=
  subst_comp (v .: @var_value n) c.

Definition cbpv_open2 n (c : comp (S (S n))) (v w : value n) :=
  subst_comp (w .: (v .: @var_value n)) c.

Lemma cbpv_subst_shift n (v w : value n) :
  subst_value (w .: @var_value n) (ren_value shift v) = v.
Proof.
  rewrite (proj1 (cbpv_subst_ren _) v _ _ shift (w .: @var_value n)
    (@var_value n)) by reflexivity.
  rewrite (proj1 (cbpv_subst_variables _) v _ (@var_value n) (@idren n))
    by reflexivity.
  apply (proj1 (cbpv_ren_id _)). reflexivity.
Qed.

Lemma cbpv_open1_lift n m (c : comp (S n)) (s : fin n -> value m) v :
  cbpv_open1 (subst_comp (up_value_value s) c) v = subst_comp (v .: s) c.
Proof.
  unfold cbpv_open1. apply (proj2 (cbpv_subst_compose _)).
  intros [i|]; [apply cbpv_subst_shift | reflexivity].
Qed.

Lemma cbpv_open2_lift n m (c : comp (S (S n))) (s : fin n -> value m) v w :
  cbpv_open2 (subst_comp (up_value_value (up_value_value s)) c) v w =
    subst_comp (w .: (v .: s)) c.
Proof.
  unfold cbpv_open2. apply (proj2 (cbpv_subst_compose _)).
  intros [ [i|] | ]; try reflexivity.
  change (subst_value (w .: (v .: @var_value m))
    (ren_value shift (ren_value shift (s i))) = s i).
  rewrite (proj1 (cbpv_subst_ren _) (ren_value shift (s i)) _ _
    shift (w .: (v .: @var_value m)) (v .: @var_value m)) by reflexivity.
  apply cbpv_subst_shift.
Qed.

Lemma cbpv_subst_open1 n m (c : comp (S n)) (s : fin n -> value m) v :
  subst_comp s (cbpv_open1 c v) =
    cbpv_open1 (subst_comp (up_value_value s) c) (subst_value s v).
Proof.
  rewrite cbpv_open1_lift. unfold cbpv_open1.
  apply (proj2 (cbpv_subst_compose _)). intros [i|]; reflexivity.
Qed.

Lemma cbpv_subst_open2 n m (c : comp (S (S n))) (s : fin n -> value m) v w :
  subst_comp s (cbpv_open2 c v w) =
    cbpv_open2 (subst_comp (up_value_value (up_value_value s)) c)
      (subst_value s v) (subst_value s w).
Proof.
  rewrite cbpv_open2_lift. unfold cbpv_open2.
  apply (proj2 (cbpv_subst_compose _)). intros [ [i|] | ]; reflexivity.
Qed.

Lemma cbpv_primitive_subst n (c d : comp n) :
  c ≽ d -> forall m (s : fin n -> value m), subst_comp s c ≽ subst_comp s d.
Proof.
  destruct 1 as [c | c d v E | b c c1 c2 E | c d v E |
    v b c c1 c2 E | v w c d E]; subst; intros m s;
    cbn [subst_comp subst_value]; try (destruct b; cbn [subst_comp subst_value]);
    constructor; try reflexivity;
    first [symmetry; apply cbpv_subst_open1 | symmetry; apply cbpv_subst_open2].
Qed.

Lemma cbpv_step_subst : forall n,
  (forall (c d : comp n), c ↪ d ->
    forall m (s : fin n -> value m), subst_comp s c ↪ subst_comp s d) /\
  (forall (v w : value n), v ↪ᵥ w ->
    forall m (s : fin n -> value m), subst_value s v ↪ᵥ subst_value s w).
Proof.
  apply mutind_sstep; intros; cbn [subst_comp subst_value];
    constructor; eauto using cbpv_primitive_subst.
Qed.

Lemma cbpv_step_ren_comp n (c d : comp n) :
  c ↪ d -> forall m (r : fin n -> fin m), ren_comp r c ↪ ren_comp r d.
Proof.
  intros H m r.
  rewrite <- (proj2 (cbpv_subst_variables _) c _ (fun i => var_value (r i)) r),
          <- (proj2 (cbpv_subst_variables _) d _ (fun i => var_value (r i)) r)
    by reflexivity.
  now apply (proj1 (cbpv_step_subst n)).
Qed.

Lemma cbpv_step_ren_value n (v w : value n) :
  v ↪ᵥ w -> forall m (r : fin n -> fin m), ren_value r v ↪ᵥ ren_value r w.
Proof.
  intros H m r.
  rewrite <- (proj1 (cbpv_subst_variables _) v _ (fun i => var_value (r i)) r),
          <- (proj1 (cbpv_subst_variables _) w _ (fun i => var_value (r i)) r)
    by reflexivity.
  now apply (proj2 (cbpv_step_subst n)).
Qed.

(* A term is locally reducible when it is strongly normalizing and every
   introduction it can reach satisfies the observations for its type. *)
Definition cbpv_at {X} (R : X -> X -> Prop) (O : X -> Prop) (x : X) :=
  SN R x /\ forall y, star R x y -> O y.

Definition cbpv_every_value (O : forall n, value n -> Prop) n (v : value n) :=
  forall m (r : fin n -> fin m), cbpv_at sstep_value (O m) (ren_value r v).

Definition cbpv_every_comp (O : forall n, comp n -> Prop) n (c : comp n) :=
  forall m (r : fin n -> fin m), cbpv_at sstep (O m) (ren_comp r c).

Fixpoint cbpv_value_obs (A : valtype) n (v : value n) {struct A} : Prop :=
  match A, v with
  | U B, thunk c => cbpv_every_comp (@cbpv_comp_obs B) c
  | Sigma A1 A2, inj b w =>
      if b then cbpv_every_value (@cbpv_value_obs A1) w
      else cbpv_every_value (@cbpv_value_obs A2) w
  | cross A1 A2, pair v1 v2 =>
      cbpv_every_value (@cbpv_value_obs A1) v1 /\
      cbpv_every_value (@cbpv_value_obs A2) v2
  | _, _ => True
  end
with cbpv_comp_obs (B : comptype) n (c : comp n) {struct B} : Prop :=
  match B, c with
  | F A, ret v => cbpv_every_value (@cbpv_value_obs A) v
  | Pi B1 B2, tuple c1 c2 =>
      cbpv_every_comp (@cbpv_comp_obs B1) c1 /\
      cbpv_every_comp (@cbpv_comp_obs B2) c2
  | arrow A C, lambda body =>
      forall v, cbpv_every_value (@cbpv_value_obs A) v ->
        cbpv_every_comp (@cbpv_comp_obs C) (cbpv_open1 body v)
  | _, _ => True
  end.

Definition cbpv_RV A {n} (v : value n) :=
  cbpv_every_value (@cbpv_value_obs A) v.
Definition cbpv_RC B {n} (c : comp n) :=
  cbpv_every_comp (@cbpv_comp_obs B) c.

Local Notation RV := cbpv_RV.
Local Notation RC := cbpv_RC.
Local Notation "'LV' A v" :=
  (cbpv_at sstep_value (@cbpv_value_obs A _) v)
  (at level 10, A at level 0, v at level 0).
Local Notation "'LC' B c" :=
  (cbpv_at sstep (@cbpv_comp_obs B _) c)
  (at level 10, B at level 0, c at level 0).

Lemma cbpv_at_intro {X} (R : X -> X -> Prop) (O : X -> Prop) x :
  O x -> (forall y, R x y -> cbpv_at R O y) -> cbpv_at R O x.
Proof.
  intros H Hstep. split.
  - constructor. intros y Hy. exact (proj1 (Hstep y Hy)).
  - intros y Hy. destruct Hy as [x | x z y Hz Hy].
    + exact H.
    + exact (proj2 (Hstep z Hz) y Hy).
Qed.

Lemma cbpv_at_step {X} (R : X -> X -> Prop) (O : X -> Prop) x y :
  cbpv_at R O x -> R x y -> cbpv_at R O y.
Proof.
  intros [Hsn Hobs] Hstep. split.
  - destruct Hsn. now apply H.
  - intros z Hz. apply Hobs. now eapply starStep; eauto.
Qed.

Lemma cbpv_value_local A n (v : value n) : RV A v -> LV A v.
Proof.
  intro H. specialize (H n (@idren n)).
  now rewrite (proj1 (cbpv_ren_id n) v (@idren n)) in H.
Qed.

Lemma cbpv_comp_local B n (c : comp n) : RC B c -> LC B c.
Proof.
  intro H. specialize (H n (@idren n)).
  now rewrite (proj2 (cbpv_ren_id n) c (@idren n)) in H.
Qed.

Lemma cbpv_value_ren A n (v : value n) m (r : fin n -> fin m) :
  RV A v -> RV A (ren_value r v).
Proof.
  intros H k q.
  rewrite (proj1 (cbpv_ren_compose n) v m k r q (fun i => q (r i)))
    by reflexivity.
  apply H.
Qed.

Lemma cbpv_comp_ren B n (c : comp n) m (r : fin n -> fin m) :
  RC B c -> RC B (ren_comp r c).
Proof.
  intros H k q.
  rewrite (proj2 (cbpv_ren_compose n) c m k r q (fun i => q (r i)))
    by reflexivity.
  apply H.
Qed.

Lemma cbpv_value_step A n (v w : value n) :
  RV A v -> v ↪ᵥ w -> RV A w.
Proof.
  intros H Hstep m r. eapply cbpv_at_step.
  - apply H.
  - now apply cbpv_step_ren_value.
Qed.

Lemma cbpv_comp_step B n (c d : comp n) :
  RC B c -> c ↪ d -> RC B d.
Proof.
  intros H Hstep m r. eapply cbpv_at_step.
  - apply H.
  - now apply cbpv_step_ren_comp.
Qed.

Lemma cbpv_value_sn A n (v : value n) : RV A v -> SN sstep_value v.
Proof. intro H. exact (proj1 (cbpv_value_local H)). Qed.

Lemma cbpv_comp_sn B n (c : comp n) : RC B c -> SN sstep c.
Proof. intro H. exact (proj1 (cbpv_comp_local H)). Qed.

Lemma cbpv_value_head A n (v : value n) : RV A v -> cbpv_value_obs A v.
Proof. intro H. exact (proj2 (cbpv_value_local H) v (starRefl _ v)). Qed.

Lemma cbpv_comp_head B n (c : comp n) : RC B c -> cbpv_comp_obs B c.
Proof. intro H. exact (proj2 (cbpv_comp_local H) c (starRefl _ c)). Qed.

(* The indices of values and computations are natural numbers, so
   inversion can use decidable equality to recover their arguments. *)
Local Ltac cbpv_invert H :=
  inversion H; subst; clear H;
  repeat match goal with
  | E : existT _ _ _ = existT _ _ _ |- _ =>
      apply (inj_pair2_eq_dec Nat.eq_dec) in E; subst
  end.

Local Ltac cbpv_invert_step H :=
  cbpv_invert H;
  try match goal with Hred : _ ≽ _ |- _ => cbpv_invert Hred end.

Lemma cbpv_var A n (i : fin n) : RV A (var_value i).
Proof.
  intros m r. apply cbpv_at_intro.
  - destruct A; exact I.
  - intros w H. cbpv_invert H.
Qed.

Lemma cbpv_unit n : RV one (@u n).
Proof.
  intros m r. apply cbpv_at_intro.
  - exact I.
  - intros w H. cbpv_invert H.
Qed.

Lemma cbpv_cunit n : RC cone (@cu n).
Proof.
  intros m r. apply cbpv_at_intro.
  - exact I.
  - intros d H. cbpv_invert_step H.
Qed.

Lemma cbpv_local_pair A B n (v w : value n) :
  RV A v -> RV B w -> LV (cross A B) (pair v w).
Proof.
  intros Hv Hw.
  induction (cbpv_value_sn Hv) as [v _ IHv] in Hv, w, Hw |- *.
  induction (cbpv_value_sn Hw) as [w _ IHw] in Hw |- *.
  apply cbpv_at_intro.
  - exact (conj Hv Hw).
  - intros z H. cbpv_invert H; eauto using cbpv_value_step.
Qed.

Lemma cbpv_pair A B n (v w : value n) :
  RV A v -> RV B w -> RV (cross A B) (pair v w).
Proof.
  intros Hv Hw m r. apply cbpv_local_pair; now apply cbpv_value_ren.
Qed.

Lemma cbpv_local_inj A B n (b : bool) (v : value n) :
  RV (if b then A else B) v -> LV (Sigma A B) (inj b v).
Proof.
  intro Hv. induction (cbpv_value_sn Hv) as [v _ IH] in Hv |- *.
  apply cbpv_at_intro.
  - destruct b; exact Hv.
  - intros w H. cbpv_invert H. eauto using cbpv_value_step.
Qed.

Lemma cbpv_inj A B n (b : bool) (v : value n) :
  RV (if b then A else B) v -> RV (Sigma A B) (inj b v).
Proof.
  intros Hv m r. apply cbpv_local_inj. now apply cbpv_value_ren.
Qed.

Lemma cbpv_local_thunk B n (c : comp n) :
  RC B c -> LV (U B) (thunk c).
Proof.
  intro Hc. induction (cbpv_comp_sn Hc) as [c _ IH] in Hc |- *.
  apply cbpv_at_intro.
  - exact Hc.
  - intros w H. cbpv_invert H. eauto using cbpv_comp_step.
Qed.

Lemma cbpv_thunk B n (c : comp n) : RC B c -> RV (U B) (thunk c).
Proof.
  intros Hc m r. apply cbpv_local_thunk. now apply cbpv_comp_ren.
Qed.

Lemma cbpv_local_ret A n (v : value n) :
  RV A v -> LC (F A) (ret v).
Proof.
  intro Hv. induction (cbpv_value_sn Hv) as [v _ IH] in Hv |- *.
  apply cbpv_at_intro.
  - exact Hv.
  - intros d H. cbpv_invert_step H. eauto using cbpv_value_step.
Qed.

Lemma cbpv_ret A n (v : value n) : RV A v -> RC (F A) (ret v).
Proof.
  intros Hv m r. apply cbpv_local_ret. now apply cbpv_value_ren.
Qed.

Lemma cbpv_local_tuple B1 B2 n (c d : comp n) :
  RC B1 c -> RC B2 d -> LC (Pi B1 B2) (tuple c d).
Proof.
  intros Hc Hd.
  induction (cbpv_comp_sn Hc) as [c _ IHc] in Hc, d, Hd |- *.
  induction (cbpv_comp_sn Hd) as [d _ IHd] in Hd |- *.
  apply cbpv_at_intro.
  - exact (conj Hc Hd).
  - intros e H. cbpv_invert_step H; eauto using cbpv_comp_step.
Qed.

Lemma cbpv_tuple B1 B2 n (c d : comp n) :
  RC B1 c -> RC B2 d -> RC (Pi B1 B2) (tuple c d).
Proof.
  intros Hc Hd m r. apply cbpv_local_tuple; now apply cbpv_comp_ren.
Qed.

(* Binder bodies must also be reducible after replacing their bound variables. *)
Definition cbpv_body A B n (c : comp (S n)) :=
  forall v, RV A v -> RC B (cbpv_open1 c v).

Definition cbpv_body2 A D B n (c : comp (S (S n))) :=
  forall v w, RV A v -> RV D w -> RC B (cbpv_open2 c v w).

Lemma cbpv_body_step A B n (c d : comp (S n)) :
  cbpv_body A B c -> c ↪ d -> cbpv_body A B d.
Proof.
  intros H Hcd v Hv. eapply cbpv_comp_step.
  - apply H, Hv.
  - now apply (proj1 (cbpv_step_subst _)).
Qed.

Lemma cbpv_body2_step A D B n (c d : comp (S (S n))) :
  cbpv_body2 A D B c -> c ↪ d -> cbpv_body2 A D B d.
Proof.
  intros H Hcd v w Hv Hw. eapply cbpv_comp_step.
  - now apply H.
  - now apply (proj1 (cbpv_step_subst _)).
Qed.

Lemma cbpv_local_lambda A B n (c : comp (S n)) :
  SN sstep c -> cbpv_body A B c -> LC (arrow A B) (lambda c).
Proof.
  induction 1 as [c _ IH]. intro Hbody.
  apply cbpv_at_intro.
  - exact Hbody.
  - intros d H. cbpv_invert_step H. eauto using cbpv_body_step.
Qed.

Definition cbpv_binder A B n (c : comp (S n)) :=
  forall m (r : fin n -> fin m), cbpv_body A B (ren_comp (upRen_value_value r) c).

Definition cbpv_binder2 A D B n (c : comp (S (S n))) :=
  forall m (r : fin n -> fin m),
    cbpv_body2 A D B (ren_comp (upRen_value_value (upRen_value_value r)) c).

Lemma cbpv_lambda A B n (c : comp (S n)) :
  RC B c -> cbpv_binder A B c -> RC (arrow A B) (lambda c).
Proof.
  intros Hc Hbody m r. apply cbpv_local_lambda.
  - exact (proj1 (Hc _ (upRen_value_value r))).
  - apply Hbody.
Qed.

(* Eliminations use induction on the strong normalization of their
   subterms. The head redex is justified by the observation on its scrutinee. *)
Lemma cbpv_local_force B n (v : value n) : RV (U B) v -> LC B (force v).
Proof.
  intro Hv. induction (cbpv_value_sn Hv) as [v _ IH] in Hv |- *.
  apply cbpv_at_intro.
  - destruct B; exact I.
  - intros d H. cbpv_invert_step H.
    + eauto using cbpv_value_step.
    + apply cbpv_comp_local. exact (cbpv_value_head Hv).
Qed.

Lemma cbpv_force B n (v : value n) : RV (U B) v -> RC B (force v).
Proof.
  intros Hv m r. apply cbpv_local_force. now apply cbpv_value_ren.
Qed.

Lemma cbpv_local_app A B n (c : comp n) (v : value n) :
  RC (arrow A B) c -> RV A v -> LC B (Syntax.app c v).
Proof.
  intros Hc Hv.
  induction (cbpv_comp_sn Hc) as [c _ IHc] in Hc, v, Hv |- *.
  induction (cbpv_value_sn Hv) as [v _ IHv] in Hv |- *.
  apply cbpv_at_intro.
  - destruct B; exact I.
  - intros d H. cbpv_invert_step H.
    + eauto using cbpv_comp_step.
    + eauto using cbpv_value_step.
    + apply cbpv_comp_local.
      exact (cbpv_comp_head Hc v Hv).
Qed.

Lemma cbpv_app A B n (c : comp n) (v : value n) :
  RC (arrow A B) c -> RV A v -> RC B (Syntax.app c v).
Proof.
  intros Hc Hv m r. eapply cbpv_local_app.
  - now apply cbpv_comp_ren.
  - now apply cbpv_value_ren.
Qed.

Lemma cbpv_local_proj B1 B2 n (b : bool) (c : comp n) :
  RC (Pi B1 B2) c -> LC (if b then B1 else B2) (proj b c).
Proof.
  intro Hc. induction (cbpv_comp_sn Hc) as [c _ IH] in Hc |- *.
  apply cbpv_at_intro.
  - destruct b; [destruct B1 | destruct B2]; exact I.
  - intros d H. cbpv_invert_step H.
    + eauto using cbpv_comp_step.
    + apply cbpv_comp_local. destruct (cbpv_comp_head Hc) as [H1 H2].
      destruct b; assumption.
Qed.

Lemma cbpv_proj B1 B2 n (b : bool) (c : comp n) :
  RC (Pi B1 B2) c -> RC (if b then B1 else B2) (proj b c).
Proof.
  intros Hc m r. apply cbpv_local_proj. now apply cbpv_comp_ren.
Qed.

Lemma cbpv_local_letin A B n (c : comp n) (d : comp (S n)) :
  RC (F A) c -> SN sstep d -> cbpv_body A B d -> LC B (letin c d).
Proof.
  intros Hc Hd Hbody.
  induction (cbpv_comp_sn Hc) as [c _ IHc] in Hc, d, Hd, Hbody |- *.
  induction Hd as [d Hnext IHd] in Hbody |- *.
  apply cbpv_at_intro.
  - destruct B; exact I.
  - intros e H. cbpv_invert_step H.
    + eauto using cbpv_comp_step, SNC.
    + eauto using cbpv_body_step.
    + apply cbpv_comp_local. apply Hbody. exact (cbpv_comp_head Hc).
Qed.

Lemma cbpv_letin A B n (c : comp n) (d : comp (S n)) :
  RC (F A) c -> RC B d -> cbpv_binder A B d -> RC B (letin c d).
Proof.
  intros Hc Hd Hbody m r. eapply cbpv_local_letin.
  - now apply cbpv_comp_ren.
  - exact (proj1 (Hd _ (upRen_value_value r))).
  - apply Hbody.
Qed.

Lemma cbpv_local_caseZ B n (v : value n) :
  RV zero v -> LC B (caseZ v).
Proof.
  intro Hv. induction (cbpv_value_sn Hv) as [v _ IH] in Hv |- *.
  apply cbpv_at_intro.
  - destruct B; exact I.
  - intros d H. cbpv_invert_step H. eauto using cbpv_value_step.
Qed.

Lemma cbpv_caseZ B n (v : value n) : RV zero v -> RC B (caseZ v).
Proof.
  intros Hv m r. apply cbpv_local_caseZ. now apply cbpv_value_ren.
Qed.

Lemma cbpv_local_caseS A D B n (v : value n) (c d : comp (S n)) :
  RV (Sigma A D) v -> SN sstep c -> SN sstep d ->
  cbpv_body A B c -> cbpv_body D B d -> LC B (caseS v c d).
Proof.
  intros Hv Hc Hd Hleft Hright.
  induction (cbpv_value_sn Hv) as [v _ IHv] in Hv, c, d, Hc, Hd, Hleft, Hright |- *.
  induction Hc as [c Hnextc IHc] in d, Hd, Hleft, Hright |- *.
  induction Hd as [d Hnextd IHd] in Hright |- *.
  apply cbpv_at_intro.
  - destruct B; exact I.
  - intros e H. cbpv_invert_step H.
    + eauto using cbpv_value_step, SNC.
    + eauto using cbpv_body_step, SNC.
    + eauto using cbpv_body_step.
    + apply cbpv_comp_local. pose proof (cbpv_value_head Hv) as Harg.
      destruct b; [apply Hleft | apply Hright]; exact Harg.
Qed.

Lemma cbpv_caseS A D B n (v : value n) (c d : comp (S n)) :
  RV (Sigma A D) v -> RC B c -> RC B d ->
  cbpv_binder A B c -> cbpv_binder D B d -> RC B (caseS v c d).
Proof.
  intros Hv Hc Hd Hleft Hright m r. eapply cbpv_local_caseS.
  - now apply cbpv_value_ren.
  - exact (proj1 (Hc _ (upRen_value_value r))).
  - exact (proj1 (Hd _ (upRen_value_value r))).
  - apply Hleft.
  - apply Hright.
Qed.

Lemma cbpv_local_caseP A D B n (v : value n) (c : comp (S (S n))) :
  RV (cross A D) v -> SN sstep c ->
  cbpv_body2 A D B c -> LC B (caseP v c).
Proof.
  intros Hv Hc Hbody.
  induction (cbpv_value_sn Hv) as [v _ IHv] in Hv, c, Hc, Hbody |- *.
  induction Hc as [c Hnext IHc] in Hbody |- *.
  apply cbpv_at_intro.
  - destruct B; exact I.
  - intros d H. cbpv_invert_step H.
    + eauto using cbpv_value_step, SNC.
    + eauto using cbpv_body2_step.
    + apply cbpv_comp_local.
      destruct (cbpv_value_head Hv) as [H1 H2]. now apply Hbody.
Qed.

Lemma cbpv_caseP A D B n (v : value n) (c : comp (S (S n))) :
  RV (cross A D) v -> RC B c ->
  cbpv_binder2 A D B c -> RC B (caseP v c).
Proof.
  intros Hv Hc Hbody m r. eapply cbpv_local_caseP.
  - now apply cbpv_value_ren.
  - exact (proj1 (Hc _ (upRen_value_value (upRen_value_value r)))).
  - apply Hbody.
Qed.

Definition cbpv_environment n m (Gamma : ctx n) (s : fin n -> value m) :=
  forall i, RV (Gamma i) (s i).

Lemma cbpv_environment_cons n m (Gamma : ctx n) (s : fin n -> value m) A v :
  cbpv_environment Gamma s -> RV A v ->
  cbpv_environment (A .: Gamma) (v .: s).
Proof. intros Hs Hv [i|]; [apply Hs | exact Hv]. Qed.

Lemma cbpv_environment_ren n m k (Gamma : ctx n) (s : fin n -> value m)
    (r : fin m -> fin k) :
  cbpv_environment Gamma s ->
  cbpv_environment Gamma (fun i => ren_value r (s i)).
Proof. intros Hs i. apply cbpv_value_ren, Hs. Qed.

Lemma cbpv_environment_lift n m (Gamma : ctx n) (s : fin n -> value m) A :
  cbpv_environment Gamma s ->
  cbpv_environment (A .: Gamma) (up_value_value s).
Proof.
  intro Hs. apply cbpv_environment_cons.
  - now apply cbpv_environment_ren.
  - apply cbpv_var.
Qed.

Definition cbpv_value_instances n (Gamma : ctx n) (v : value n) A :=
  forall m (s : fin n -> value m), cbpv_environment Gamma s ->
    RV A (subst_value s v).

Definition cbpv_comp_instances n (Gamma : ctx n) (c : comp n) B :=
  forall m (s : fin n -> value m), cbpv_environment Gamma s ->
    RC B (subst_comp s c).

Lemma cbpv_instance_binder A B n (Gamma : ctx n) (c : comp (S n)) :
  cbpv_comp_instances (A .: Gamma) c B ->
  forall m (s : fin n -> value m), cbpv_environment Gamma s ->
    cbpv_binder A B (subst_comp (up_value_value s) c).
Proof.
  intros Hc m s Hs k r v Hv.
  rewrite (proj2 (cbpv_ren_subst _) c _ _
    (up_value_value s) (upRen_value_value r)
    (up_value_value (fun i => ren_value r (s i))))
    by (apply cbpv_ren_lift; reflexivity).
  rewrite cbpv_open1_lift.
  apply Hc, cbpv_environment_cons; [now apply cbpv_environment_ren | exact Hv].
Qed.

Lemma cbpv_instance_binder2 A D B n (Gamma : ctx n) (c : comp (S (S n))) :
  cbpv_comp_instances (D .: (A .: Gamma)) c B ->
  forall m (s : fin n -> value m), cbpv_environment Gamma s ->
    cbpv_binder2 A D B (subst_comp (up_value_value (up_value_value s)) c).
Proof.
  intros Hc m s Hs k r v w Hv Hw.
  rewrite (proj2 (cbpv_ren_subst _) c _ _
    (up_value_value (up_value_value s)) (upRen_value_value (upRen_value_value r))
    (up_value_value (up_value_value (fun i => ren_value r (s i)))))
    by (do 2 apply cbpv_ren_lift; reflexivity).
  rewrite cbpv_open2_lift.
  apply Hc, cbpv_environment_cons; [|exact Hw].
  apply cbpv_environment_cons; [now apply cbpv_environment_ren | exact Hv].
Qed.

(* The fundamental lemma uses a reducible substitution for the free variables. *)
Lemma cbpv_fundamental : forall n (Gamma : ctx n),
  (forall v A, Gamma ⊩ v : A -> cbpv_value_instances Gamma v A) /\
  (forall c B, Gamma ⊢ c : B -> cbpv_comp_instances Gamma c B).
Proof.
  apply (@mutind_value_computation_typing
    (@cbpv_value_instances) (@cbpv_comp_instances));
    unfold cbpv_value_instances, cbpv_comp_instances;
    intros; cbn [subst_value subst_comp].
  - auto.
  - apply cbpv_unit.
  - apply cbpv_pair; auto.
  - apply cbpv_inj; auto.
  - apply cbpv_thunk; auto.
  - apply cbpv_cunit.
  - eapply cbpv_lambda.
    + eauto using cbpv_environment_lift.
    + eauto using cbpv_instance_binder.
  - eapply cbpv_letin.
    + eauto.
    + eauto using cbpv_environment_lift.
    + eauto using cbpv_instance_binder.
  - apply cbpv_ret; auto.
  - eauto using cbpv_app.
  - apply cbpv_tuple; auto.
  - eauto using cbpv_proj.
  - apply cbpv_force; auto.
  - apply cbpv_caseZ; auto.
  - eapply cbpv_caseS.
    + eauto.
    + eauto using cbpv_environment_lift.
    + eauto using cbpv_environment_lift.
    + eauto using cbpv_instance_binder.
    + eauto using cbpv_instance_binder.
  - eapply cbpv_caseP.
    + eauto.
    + eauto using cbpv_environment_lift.
    + eauto using cbpv_instance_binder2.
Qed.

Theorem strong_normalisation_cbpv n (Gamma: ctx n) P B:
  Gamma ⊢ P : B -> SN sstep P.
Proof.
  intro HP.
  apply (cbpv_comp_sn (B := B)).
  rewrite <- (cbpv_subst_id P).
  apply (proj2 (cbpv_fundamental Gamma) _ _ HP).
  intro i. apply cbpv_var.
Qed.
