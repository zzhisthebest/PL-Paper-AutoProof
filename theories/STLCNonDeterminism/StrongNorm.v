Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
From AutoProof Require Import Smallstep.
From AutoProof.STLCNonDeterminism Require Import Syntax.
From AutoProof.STLCNonDeterminism Require Import StlcProp.
From AutoProof.STLCNonDeterminism Require Import WeakNorm.

Import ListNotations.

Module STLCNDStrongNorm.
Import STLCND.
Import STLCNDProp.
Import STLCNDWeakNorm.

(** strongly_normalizing t 表示：不存在从 t 出发的无限归约路径。
*)
Inductive strongly_normalizing : tm -> Prop :=
    (* SN_intro 同时包含基础情况和递归情况：对于已经不能继续归约的程序，
    例如 true，条件 forall t', true --> t' -> strongly_normalizing t'
    自动成立，因为根本不存在满足 true --> t' 的 t'。  *)
  | SN_intro : forall t,
      (forall t', t --> t' -> strongly_normalizing t') ->
      strongly_normalizing t.

Lemma sn_step : forall t t',
  strongly_normalizing t ->
  t --> t' ->
  strongly_normalizing t'.
Proof.
  intros t t' Hsn Hstep.
  inversion Hsn as [t0 Hnext].
  apply Hnext. exact Hstep.
Qed.

Lemma step_preserves_lc : forall t t',
  t --> t' ->
  locally_closed t ->
  locally_closed t'.
Proof.
  intros t t' Hstep Hlc.
  induction Hstep.
  - apply open_preserves_term.
    + unfold locally_closed in H. inversion H. assumption.
    + apply value_regular. exact H0.
  - inversion Hlc; subst. apply lc_app.
    + apply IHHstep. assumption.
    + assumption.
  - inversion Hlc; subst. apply lc_app.
    + apply value_regular. exact H.
    + apply IHHstep. assumption.
  - assumption.
  - assumption.
Qed.

Lemma value_no_step : forall v,
  value v ->
  forall t, ~ (v --> t).
Proof.
  intros v Hv t Hstep.
  inversion Hv; subst; inversion Hstep.
Qed.

Lemma value_multi_eq : forall v t,
  value v ->
  v -->* t ->
  t = v.
Proof.
  intros v t Hv Hmulti.
  inversion Hmulti; subst.
  - reflexivity.
  - exfalso. eapply value_no_step; eauto.
Qed.

Lemma value_sn : forall v,
  value v ->
  strongly_normalizing v.
Proof.
  intros v Hv.
  apply SN_intro. intros t Hstep.
  exfalso. eapply value_no_step; eauto.
Qed.

(**
  strong_value_relation T v：v 是类型 T 下的 reducible value。
  strong_expression_relation T t：t 的每条归约路径都终止，而且最终得到的
  每个 value 都满足 strong_value_relation T。
*)
Fixpoint strong_value_relation (T : ty) (v : tm) : Prop :=
  value v /\
  match T with
  | Ty_Bool =>
      v = tm_true \/ v = tm_false
  | Ty_Arrow T1 T2 =>
      exists body,
        v = tm_abs T1 body /\
        forall arg,
          strong_value_relation T1 arg ->
          locally_closed (open body arg) /\
          strongly_normalizing (open body arg) /\
          forall result,
            open body arg -->* result ->
            value result ->
            strong_value_relation T2 result
  end.

Definition strong_expression_relation (T : ty) (t : tm) : Prop :=
  locally_closed t /\
  strongly_normalizing t /\
  forall v,
    t -->* v ->
    value v ->
    strong_value_relation T v.

Lemma strong_value_relation_value : forall T v,
  strong_value_relation T v -> value v.
Proof.
  intros T v H. destruct T; simpl in H; tauto.
Qed.

Lemma strong_value_relation_lc : forall T v,
  strong_value_relation T v -> locally_closed v.
Proof.
  intros T v H.
  apply value_regular.
  eapply strong_value_relation_value. exact H.
Qed.

Lemma strong_value_is_expression : forall T v,
  strong_value_relation T v ->
  strong_expression_relation T v.
Proof.
  intros T v Hv.
  split.
  - eapply strong_value_relation_lc. exact Hv.
  - split.
    + apply value_sn. eapply strong_value_relation_value. exact Hv.
    + intros v' Hmulti Hvalue.
      assert (v' = v).
      {
        eapply value_multi_eq.
        - eapply strong_value_relation_value. exact Hv.
        - exact Hmulti.
      }
      subst v'. exact Hv.
Qed.

Lemma strong_expression_step : forall T t t',
  strong_expression_relation T t ->
  t --> t' ->
  strong_expression_relation T t'.
Proof.
  intros T t t' [Hlc [Hsn Hall]] Hstep.
  split.
  - eapply step_preserves_lc; eauto.
  - split.
    + eapply sn_step; eauto.
    + intros v Hmulti Hv.
      apply Hall with (v := v); auto.
      eapply multi_step; eauto.
Qed.

Lemma strong_expression_of_reducts : forall T t,
  locally_closed t ->
  ~ value t ->
  (forall t', t --> t' -> strong_expression_relation T t') ->
  strong_expression_relation T t.
Proof.
  intros T t Hlc Hnotvalue Hnext.
  split. exact Hlc.
  split.
  - apply SN_intro. intros t' Hstep.
    destruct (Hnext t' Hstep) as [_ [Hsn _]]. exact Hsn.
  - intros v Hmulti Hv.
    inversion Hmulti; subst.
    + contradiction.
    + destruct (Hnext y H) as [_ [_ Hall]].
      eapply Hall; eauto.
Qed.

Lemma strong_expression_app : forall T1 T2 t1 t2,
  strong_expression_relation (Ty_Arrow T1 T2) t1 ->
  strong_expression_relation T1 t2 ->
  strong_expression_relation T2 (tm_app t1 t2).
Proof.
  intros T1 T2 t1 t2 HE1 HE2.
  destruct HE1 as [Hlc1 [Hsn1 Hall1]].
  revert T1 T2 Hlc1 Hall1 t2 HE2.
  induction Hsn1 as [t1 Hnext1 IH1].
  intros T1 T2 Hlc1 Hall1 t2 HE2.
  destruct HE2 as [Hlc2 [Hsn2 Hall2]].
  revert Hlc2 Hall2.
  induction Hsn2 as [t2 Hnext2 IH2].
  intros Hlc2 Hall2.
  apply strong_expression_of_reducts.
  - apply lc_app; assumption.
  - intro Hvalue. inversion Hvalue.
  - intros u Hstep.
    inversion Hstep; subst.
    + assert (Hrefl1 : tm_abs T t -->* tm_abs T t) by apply multi_refl.
      assert (Hrefl2 : t2 -->* t2) by apply multi_refl.
      pose proof
        (Hall1 (tm_abs T t) Hrefl1 (v_abs T t H1)) as HVfun.
      pose proof (Hall2 t2 Hrefl2 H3) as HVarg.
      simpl in HVfun.
      destruct HVfun as [_ [body [Heq Hbody]]].
      injection Heq as HeqT Heqbody.
      subst T. subst body.
      exact (Hbody t2 HVarg).
    + apply (IH1 t1' H1 T1 T2).
      * eapply step_preserves_lc; eauto.
      * intros v Hmulti Hv.
        apply Hall1 with (v := v); auto.
        eapply multi_step; eauto.
      * split. exact Hlc2.
        split.
        -- apply SN_intro. exact Hnext2.
        -- exact Hall2.
    + apply (IH2 t2' H3).
      * eapply step_preserves_lc; eauto.
      * intros v Hmulti Hv.
        apply Hall2 with (v := v); auto.
        eapply multi_step; eauto.
Qed.

Lemma strong_expression_choice : forall T t1 t2,
  strong_expression_relation T t1 ->
  strong_expression_relation T t2 ->
  strong_expression_relation T (tm_choice t1 t2).
Proof.
  intros T t1 t2 HE1 HE2.
  destruct HE1 as [Hlc1 [Hsn1 Hall1]].
  destruct HE2 as [Hlc2 [Hsn2 Hall2]].
  apply strong_expression_of_reducts.
  - apply lc_choice; assumption.
  - intro Hvalue. inversion Hvalue.
  - intros u Hstep. inversion Hstep; subst.
    + exact (conj Hlc1 (conj Hsn1 Hall1)).
    + exact (conj Hlc2 (conj Hsn2 Hall2)).
Qed.

Definition strong_related_substitution
    (Gamma : context) (rho : term_substitution) : Prop :=
  forall x T,
    Gamma x = Some T ->
    strong_value_relation T (rho x).

Lemma strong_related_update : forall Gamma rho x T v,
  strong_related_substitution Gamma rho ->
  strong_value_relation T v ->
  strong_related_substitution
    (update Gamma x T) (subst_update rho x v).
Proof.
  unfold strong_related_substitution, subst_update, update.
  intros Gamma rho x T v Hrel HV y U Hy.
  destruct (Nat.eqb x y) eqn:Heq.
  - apply Nat.eqb_eq in Heq. subst y.
    injection Hy as ->. exact HV.
  - apply Hrel. exact Hy.
Qed.

Lemma strong_empty_related :
  strong_related_substitution empty id_substitution.
Proof.
  unfold strong_related_substitution, empty.
  intros. discriminate H.
Qed.

(**
  Fundamental theorem for strong normalization：类型正确的程序在把自由变量
  替换成对应类型的 reducible value 后，满足 strong expression relation。
*)
Theorem strong_fundamental : forall Gamma t T,
  <{ Gamma |-- t \in T }> ->
  forall rho,
    proper_substitution rho ->
    strong_related_substitution Gamma rho ->
    strong_expression_relation T (msubst rho t).
Proof.
  intros Gamma t T Htyping.
  induction Htyping; intros rho Hproper Hrel.
  - simpl. apply strong_value_is_expression.
    apply Hrel with (x := x). exact H.
  - assert (Habs_lc : locally_closed (msubst rho (tm_abs T1 t1))).
    {
      apply msubst_preserves_term.
      - exact Hproper.
      - apply typing_regular with
          (Gamma := Gamma) (T := Ty_Arrow T1 T2).
        apply T_Abs with (L := L). exact H.
    }
    apply strong_value_is_expression.
    simpl. split.
    + apply v_abs. exact Habs_lc.
    + exists (msubst rho t1). split.
      * reflexivity.
      * intros arg HVarg.
        pose (x := fresh (L ++ free_vars t1)).
        assert (HxL : ~ In x L).
        {
          intro Hin. unfold x in Hin.
          apply (fresh_notin (L ++ free_vars t1)).
          apply in_or_app. left. exact Hin.
        }
        assert (Hxfv : ~ In x (free_vars t1)).
        {
          intro Hin. unfold x in Hin.
          apply (fresh_notin (L ++ free_vars t1)).
          apply in_or_app. right. exact Hin.
        }
        specialize (H0 x HxL (subst_update rho x arg)).
        assert (Harg_lc : locally_closed arg).
        {
          eapply strong_value_relation_lc. exact HVarg.
        }
        specialize (H0 (proper_update rho x arg Hproper Harg_lc)).
        specialize
          (H0 (strong_related_update Gamma rho x T1 arg Hrel HVarg)).
        rewrite
          (msubst_open_update t1 rho x arg Hxfv Hproper Harg_lc) in H0.
        exact H0.
  - apply strong_expression_app with (T1 := T1).
    + apply IHHtyping1; assumption.
    + apply IHHtyping2; assumption.
  - apply strong_value_is_expression.
    simpl. split.
    + apply v_true.
    + left. reflexivity.
  - apply strong_value_is_expression.
    simpl. split.
    + apply v_false.
    + right. reflexivity.
  - apply strong_expression_choice.
    + apply IHHtyping1; assumption.
    + apply IHHtyping2; assumption.
Qed.

(** Strong normalization：每个闭合且类型正确的程序，其所有归约路径都终止。 *)
Theorem strong_normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Htyping.
  pose proof
    (strong_fundamental empty t T Htyping id_substitution
      id_substitution_proper strong_empty_related) as Hrel.
  rewrite msubst_id in Hrel.
  destruct Hrel as [_ [Hsn _]]. exact Hsn.
Qed.

End STLCNDStrongNorm.
