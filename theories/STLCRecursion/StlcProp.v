Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
From AutoProof.STLCRecursion Require Import Syntax.

Import ListNotations.

Module STLCRecProp.
Import STLCRec.

Lemma lc_at_weaken : forall k j t,
  lc_at k t ->
  k <= j ->
  lc_at j t.
Proof.
  intros k j t H.
  generalize dependent j.
  induction H; intros j Hle; eauto using lc_at.
  - apply lc_bvar. lia.
  - apply lc_abs. apply IHlc_at. lia.
Qed.

Lemma term_lc_at : forall k t,
  locally_closed t ->
  lc_at k t.
Proof.
  unfold locally_closed. intros. eapply lc_at_weaken; eauto. lia.
Qed.

Lemma numeric_value_lc : forall n,
  numeric_value n -> locally_closed n.
Proof.
  intros n H. induction H; constructor; assumption.
Qed.

Lemma value_regular : forall v,
  value v -> locally_closed v.
Proof.
  intros v H. destruct H.
  - assumption.
  - apply lc_true.
  - apply lc_false.
  - apply numeric_value_lc. assumption.
Qed.

Lemma numeral_numeric : forall n, numeric_value (numeral n).
Proof.
  induction n; simpl; constructor; assumption.
Qed.

Lemma numeric_numeral : forall t,
  numeric_value t -> exists n : nat, t = numeral n.
Proof.
  intros t H. induction H.
  - exists 0. reflexivity.
  - destruct IHnumeric_value as [m ->]. exists (S m). reflexivity.
Qed.

Lemma open_rec_preserves_lc_at : forall t k u,
  lc_at (S k) t ->
  locally_closed u ->
  lc_at k (open_rec k u t).
Proof.
  induction t; intros k u Hlc Hu; simpl in *; inversion Hlc; subst; eauto using lc_at.
  - destruct (Nat.eqb k n) eqn:Heq.
    + apply term_lc_at. exact Hu.
    + apply Nat.eqb_neq in Heq. apply lc_bvar. lia.
Qed.

Lemma open_preserves_term : forall t u,
  lc_at 1 t ->
  locally_closed u ->
  locally_closed (open t u).
Proof.
  unfold open, locally_closed. intros.
  apply open_rec_preserves_lc_at; assumption.
Qed.

Lemma lc_at_open_inv : forall t k u,
  lc_at k (open_rec k u t) ->
  lc_at (S k) t.
Proof.
  induction t; intros k u Hlc; simpl in *.
  - destruct (Nat.eqb k n) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst. apply lc_bvar. lia.
    + inversion Hlc; subst. apply lc_bvar. lia.
  - apply lc_fvar.
  - inversion Hlc; subst. eauto using lc_at.
  - inversion Hlc; subst. apply lc_abs. apply (IHt (S k) u). assumption.
  - apply lc_true.
  - apply lc_false.
  - apply lc_zero.
  - inversion Hlc; subst. eauto using lc_at.
  - inversion Hlc; subst. eauto using lc_at.
Qed.

Lemma typing_regular : forall Gamma t T,
  <{ Gamma |-- t \in T }> ->
  locally_closed t.
Proof.
  intros Gamma t T Ht.
  induction Ht.
  - unfold locally_closed. apply lc_fvar.
  - unfold locally_closed. apply lc_abs.
    pose (x := fresh L).
    assert (Hfresh : ~ In x L) by (unfold x; apply fresh_notin).
    specialize (H0 x Hfresh).
    apply lc_at_open_inv with (u := tm_fvar x).
    exact H0.
  - unfold locally_closed. apply lc_app; assumption.
  - unfold locally_closed. apply lc_true.
  - unfold locally_closed. apply lc_false.
  - apply lc_zero.
  - apply lc_succ. assumption.
  - apply lc_rec; assumption.
Qed.

Lemma canonical_forms_fun : forall t T1 T2,
  <{ empty |-- t \in T1 -> T2 }> ->
  value t ->
  exists body, t = tm_abs T1 body.
Proof.
  intros t T1 T2 HT HV.
  inversion HV; subst.
  - inversion HT; subst. eauto.
  - inversion HT.
  - inversion HT.
  - inversion H; subst; inversion HT.
Qed.

Lemma canonical_forms_nat : forall t,
  <{ empty |-- t \in Nat }> ->
  value t -> numeric_value t.
Proof.
  intros t HT HV. inversion HV; subst; try assumption; inversion HT.
Qed.

Lemma numeric_no_step : forall n,
  numeric_value n -> forall t, ~ (n --> t).
Proof.
  intros n Hn. induction Hn; intros u Hs; inversion Hs; subst.
  eapply IHHn. eassumption.
Qed.

Lemma value_no_step : forall v,
  value v -> forall t, ~ (v --> t).
Proof.
  intros v Hv t Hs. destruct Hv; try solve [inversion Hs].
  eapply numeric_no_step; eauto.
Qed.

Lemma step_deterministic : forall t t1 t2,
  t --> t1 -> t --> t2 -> t1 = t2.
Proof.
  intros t t1 t2 Hs1. revert t2.
  induction Hs1; intros u Hs2; inversion Hs2; subst;
    try reflexivity;
    try solve [exfalso; eapply value_no_step; eauto];
    try solve [exfalso; eapply numeric_no_step; eauto];
    try solve [f_equal; eauto].
  all: try match goal with H : tm_abs _ _ --> _ |- _ => inversion H end.
  all: try match goal with H : tm_zero --> _ |- _ => inversion H end.
  all: try solve [match goal with
    | HV : value ?v, HS : ?v --> ?u |- _ =>
        exfalso; exact (value_no_step v HV u HS)
    end].
  all: try solve [match goal with
    | HN : numeric_value ?n, HS : tm_succ ?n --> ?u |- _ =>
        exfalso; exact (numeric_no_step (tm_succ n) (nv_succ n HN) u HS)
    end].
Qed.

Theorem progress : forall t T,
  <{ empty |-- t \in T }> ->
  value t \/ exists t', t --> t'.
Proof.
  intros t T Ht. remember empty as Gamma.
  induction Ht; subst Gamma.
  - discriminate H.
  - left. apply v_abs. apply typing_regular with
      (Gamma := empty) (T := Ty_Arrow T1 T2).
    apply T_Abs with (L := L). exact H.
  - right.
    destruct (IHHt1 eq_refl) as [Hv1 | [u Hs1]].
    + destruct (IHHt2 eq_refl) as [Hv2 | [u Hs2]].
      * destruct (canonical_forms_fun _ _ _ Ht1 Hv1) as [body ->].
        exists (open body t2). apply ST_AppAbs.
        -- apply value_regular. exact Hv1.
        -- exact Hv2.
      * exists (tm_app t1 u). apply ST_App2; assumption.
    + exists (tm_app u t2). apply ST_App1.
      * exact Hs1.
      * eapply typing_regular. exact Ht2.
  - left. apply v_true.
  - left. apply v_false.
  - left. apply v_nat. apply nv_zero.
  - destruct (IHHt eq_refl) as [Hv | [u Hs]].
    + left. apply v_nat. apply nv_succ.
      eapply canonical_forms_nat; eauto.
    + right. exists (tm_succ u). apply ST_Succ. exact Hs.
  - right.
    destruct (IHHt1 eq_refl) as [Hvn | [n' Hsn]].
    + pose proof (canonical_forms_nat _ Ht1 Hvn) as Hnum.
      destruct (IHHt2 eq_refl) as [Hvb | [b' Hsb]].
      * destruct (IHHt3 eq_refl) as [Hvs | [s' Hss]].
        -- inversion Hnum; subst.
           ++ exists b. apply ST_RecZero; assumption.
           ++ eexists. apply ST_RecSucc; eassumption.
        -- exists (tm_natrec n b s'). apply ST_RecStep; assumption.
      * exists (tm_natrec n b' s). apply ST_RecBase; try assumption.
        eapply typing_regular. exact Ht3.
    + exists (tm_natrec n' b s). apply ST_RecArg; try assumption;
        eapply typing_regular; eassumption.
Qed.

End STLCRecProp.
