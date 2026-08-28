(** Fundamental theorem of relational parametricity for System F. *)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
From AutoProof.SystemF Require Import Syntax.
From AutoProof.SystemF Require Import Infrastructure.
From AutoProof.SystemF Require Import Typing.
From AutoProof.SystemF Require Import LogicalRelation.

Module SystemFParametricity.
Import ListNotations.
Import SystemF.
Import SystemFInfrastructure.
Import SystemFTyping.
Import SystemFLogicalRelation.

(* 显然 *)
Lemma relation_update_eq : forall rho X a,
  (relation_update rho X a) X = Some a.
Proof.
  intros. unfold relation_update. rewrite Nat.eqb_refl. reflexivity.
Qed.
(* 显然 *)
Lemma relation_update_neq : forall rho X Y a,
  X <> Y -> relation_update rho X a Y = rho Y.
Proof.
  intros rho X Y a Hneq. unfold relation_update.
  rewrite (proj2 (Nat.eqb_neq X Y)) by assumption. reflexivity.
Qed.
(* related_type_substitutions Delta theta1 theta2 rho 表示：
  对于 Delta 中的每个类型变量 X，rho 都保存了一个 assignment，其左右类型分别等于 theta1
  X 和 theta2 X，并同时保存了这两个类型之间的合格关系。 *)
Definition related_type_substitutions
    (Delta : ty_context) (theta1 theta2 : type_substitution)
    (rho : relation_env) : Prop :=
  forall X : atom,
    In X Delta ->
    exists a : relation_assignment,
      rho X = Some a /\
      a.(assignment_left) = theta1 X /\
      a.(assignment_right) = theta2 X.
(* related_substitutions rho Gamma gamma1 gamma2 表示：
  对于 Gamma 中每个类型为 T 的程序自由变量 x，左边替换进去的 gamma1 x 与右边替换进去的 gamma2 x，
  必须在 rho 对类型变量的解释下满足类型 T 的 value_relation。 *)
Definition related_substitutions
    (rho : relation_env) (Gamma : context)
    (gamma1 gamma2 : term_substitution) : Prop :=
  forall x T,
    lookup_context x Gamma = Some T ->
    value_relation [] rho T (gamma1 x) (gamma2 x).

Lemma left_type_empty_agrees : forall T k rho theta,
  lc_ty_at k T ->
  (forall X, In X (fv_ty T) ->
    exists a, rho X = Some a /\ a.(assignment_left) = theta X) ->
  left_type_rec k [] rho T = instantiate_ty theta T.
Proof.
  induction T; intros k rho theta Hlc Hagree; simpl in *.
  - inversion Hlc; subst.
    rewrite (proj2 (Nat.ltb_lt n k)) by assumption. reflexivity.
  - destruct (Hagree a) as [b [Hlookup Heq]]; auto.
    rewrite Hlookup, Heq. reflexivity.
  - inversion Hlc; subst. f_equal.
    + apply IHT1; [assumption |]. intros X Hin. apply Hagree.
      apply in_app_iff. auto.
    + apply IHT2; [assumption |]. intros X Hin. apply Hagree.
      apply in_app_iff. auto.
  - inversion Hlc; subst. f_equal.
    apply IHT; [assumption | exact Hagree].
Qed.

Lemma right_type_empty_agrees : forall T k rho theta,
  lc_ty_at k T ->
  (forall X, In X (fv_ty T) ->
    exists a, rho X = Some a /\ a.(assignment_right) = theta X) ->
  right_type_rec k [] rho T = instantiate_ty theta T.
Proof.
  induction T; intros k rho theta Hlc Hagree; simpl in *.
  - inversion Hlc; subst.
    rewrite (proj2 (Nat.ltb_lt n k)) by assumption. reflexivity.
  - destruct (Hagree a) as [b [Hlookup Heq]]; auto.
    rewrite Hlookup, Heq. reflexivity.
  - inversion Hlc; subst. f_equal.
    + apply IHT1; [assumption |]. intros X Hin. apply Hagree.
      apply in_app_iff. auto.
    + apply IHT2; [assumption |]. intros X Hin. apply Hagree.
      apply in_app_iff. auto.
  - inversion Hlc; subst. f_equal.
    apply IHT; [assumption | exact Hagree].
Qed.

Lemma left_type_related : forall Delta theta1 theta2 rho T,
  related_type_substitutions Delta theta1 theta2 rho ->
  wf_ty Delta T ->
  left_type [] rho T = instantiate_ty theta1 T.
Proof.
  intros Delta theta1 theta2 rho T Hrel Hwf.
  unfold left_type. apply left_type_empty_agrees.
  - apply wf_ty_lc with Delta. exact Hwf.
  - intros X Hin. destruct (Hrel X) as [a [Hlookup [Hleft Hright]]].
    + eapply wf_ty_fv; eauto.
    + exists a. auto.
Qed.

Lemma right_type_related : forall Delta theta1 theta2 rho T,
  related_type_substitutions Delta theta1 theta2 rho ->
  wf_ty Delta T ->
  right_type [] rho T = instantiate_ty theta2 T.
Proof.
  intros Delta theta1 theta2 rho T Hrel Hwf.
  unfold right_type. apply right_type_empty_agrees.
  - apply wf_ty_lc with Delta. exact Hwf.
  - intros X Hin. destruct (Hrel X) as [a [Hlookup [Hleft Hright]]].
    + eapply wf_ty_fv; eauto.
    + exists a. auto.
Qed.

Lemma related_types_left_wf : forall Delta theta1 theta2 rho,
  related_type_substitutions Delta theta1 theta2 rho ->
  type_substitution_wf Delta [] theta1.
Proof.
  intros Delta theta1 theta2 rho Hrel X Hin.
  destruct (Hrel X Hin) as [a [Hlookup [Hleft Hright]]].
  rewrite <- Hleft. pose proof a.(assignment_is_candidate) as Ha.
  exact (proj1 Ha).
Qed.

Lemma related_types_right_wf : forall Delta theta1 theta2 rho,
  related_type_substitutions Delta theta1 theta2 rho ->
  type_substitution_wf Delta [] theta2.
Proof.
  intros Delta theta1 theta2 rho Hrel X Hin.
  destruct (Hrel X Hin) as [a [Hlookup [Hleft Hright]]].
  rewrite <- Hright. pose proof a.(assignment_is_candidate) as Ha.
  exact (proj1 (proj2 Ha)).
Qed.

Lemma related_terms_left_typed : forall Delta Gamma theta1 theta2 rho gamma1 gamma2,
  context_wf Delta Gamma ->
  related_type_substitutions Delta theta1 theta2 rho ->
  related_substitutions rho Gamma gamma1 gamma2 ->
  term_substitution_typed Gamma [] empty theta1 gamma1.
Proof.
  intros Delta Gamma theta1 theta2 rho gamma1 gamma2 Hctx Htypes Hterms.
  intros x T Hlookup. pose proof (Hterms x T Hlookup) as HR.
  pose proof (value_relation_typing _ _ _ _ _ HR) as [Ht1 Ht2].
  rewrite (left_type_related Delta theta1 theta2 rho T Htypes) in Ht1.
  - exact Ht1.
  - eapply Hctx; eauto.
Qed.

Lemma related_terms_right_typed : forall Delta Gamma theta1 theta2 rho gamma1 gamma2,
  context_wf Delta Gamma ->
  related_type_substitutions Delta theta1 theta2 rho ->
  related_substitutions rho Gamma gamma1 gamma2 ->
  term_substitution_typed Gamma [] empty theta2 gamma2.
Proof.
  intros Delta Gamma theta1 theta2 rho gamma1 gamma2 Hctx Htypes Hterms.
  intros x T Hlookup. pose proof (Hterms x T Hlookup) as HR.
  pose proof (value_relation_typing _ _ _ _ _ HR) as [Ht1 Ht2].
  rewrite (right_type_related Delta theta1 theta2 rho T Htypes) in Ht2.
  - exact Ht2.
  - eapply Hctx; eauto.
Qed.

Lemma related_substitutions_update : forall rho Gamma gamma1 gamma2 x T v1 v2,
  related_substitutions rho Gamma gamma1 gamma2 ->
  value_relation [] rho T v1 v2 ->
  related_substitutions rho <{ x |-> $(T); Gamma }>
    (term_subst_update gamma1 x v1)
    (term_subst_update gamma2 x v2).
Proof.
  intros rho Gamma gamma1 gamma2 x T v1 v2 Hgamma Hv y U Hlookup.
  unfold update in Hlookup. simpl in Hlookup.
  unfold term_subst_update.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst y. rewrite Nat.eqb_refl.
    inversion Hlookup. subst U. exact Hv.
  - apply Nat.eqb_neq in E.
    rewrite (proj2 (Nat.eqb_neq x y)) by congruence.
    apply Hgamma. exact Hlookup.
Qed.

Lemma related_type_substitutions_update :
  forall Delta theta1 theta2 rho X a,
  related_type_substitutions Delta theta1 theta2 rho ->
  related_type_substitutions (X :: Delta)
    (type_subst_update theta1 X a.(assignment_left))
    (type_subst_update theta2 X a.(assignment_right))
    (relation_update rho X a).
Proof.
  intros Delta theta1 theta2 rho X a Htheta Y Hin.
  destruct (Nat.eq_dec X Y) as [E | Hneq].
  - subst Y. exists a. repeat split.
    + apply relation_update_eq.
    + unfold type_subst_update. rewrite Nat.eqb_refl. reflexivity.
    + unfold type_subst_update. rewrite Nat.eqb_refl. reflexivity.
  - destruct Hin as [E | Hin]; [contradiction |].
    destruct (Htheta Y Hin) as [b [Hlookup [Hleft Hright]]].
    exists b. repeat split.
    + rewrite relation_update_neq by exact Hneq. exact Hlookup.
    + unfold type_subst_update.
      rewrite (proj2 (Nat.eqb_neq X Y)) by assumption. exact Hleft.
    + unfold type_subst_update.
      rewrite (proj2 (Nat.eqb_neq X Y)) by assumption. exact Hright.
Qed.

Lemma left_type_rho_update_irrelevant : forall T k eta rho X a,
  ~ In X (fv_ty T) ->
  left_type_rec k eta (relation_update rho X a) T =
  left_type_rec k eta rho T.
Proof.
  induction T; intros k eta rho X b Hfresh; simpl in *.
  - reflexivity.
  - assert (Hneq : X <> a).
    { intro E. subst X. apply Hfresh. simpl. auto. }
    rewrite relation_update_neq by exact Hneq. reflexivity.
  - rewrite in_app_iff in Hfresh. f_equal; [apply IHT1 | apply IHT2]; tauto.
  - f_equal. apply IHT. exact Hfresh.
Qed.

Lemma right_type_rho_update_irrelevant : forall T k eta rho X a,
  ~ In X (fv_ty T) ->
  right_type_rec k eta (relation_update rho X a) T =
  right_type_rec k eta rho T.
Proof.
  induction T; intros k eta rho X b Hfresh; simpl in *.
  - reflexivity.
  - assert (Hneq : X <> a) by (intro; subst; apply Hfresh; auto).
    rewrite relation_update_neq by exact Hneq. reflexivity.
  - rewrite in_app_iff in Hfresh. f_equal; [apply IHT1 | apply IHT2]; tauto.
  - f_equal. apply IHT. exact Hfresh.
Qed.

Lemma value_relation_rho_update_irrelevant : forall T eta rho X a,
  ~ In X (fv_ty T) ->
  forall v1 v2,
    value_relation eta (relation_update rho X a) T v1 v2 <->
    value_relation eta rho T v1 v2.
Proof.
  induction T; intros eta rho X b Hfresh v1 v2; simpl in *.
  all: unfold left_type, right_type in *.
  - rewrite left_type_rho_update_irrelevant by exact Hfresh.
    rewrite right_type_rho_update_irrelevant by exact Hfresh.
    reflexivity.
  - assert (Hneq : X <> a) by (intro; subst; apply Hfresh; auto).
    rewrite relation_update_neq by exact Hneq.
    rewrite left_type_rho_update_irrelevant by exact Hfresh.
    rewrite right_type_rho_update_irrelevant by exact Hfresh.
    reflexivity.
  - rewrite in_app_iff in Hfresh.
    assert (H1 : ~ In X (fv_ty T1)) by intuition.
    assert (H2 : ~ In X (fv_ty T2)) by intuition.
    assert (Hwhole : ~ In X (fv_ty (Ty_Arrow T1 T2))).
    { simpl. rewrite in_app_iff. exact Hfresh. }
    rewrite (left_type_rho_update_irrelevant (Ty_Arrow T1 T2)
      0 eta rho X b Hwhole).
    rewrite (right_type_rho_update_irrelevant (Ty_Arrow T1 T2)
      0 eta rho X b Hwhole).
    rewrite (left_type_rho_update_irrelevant T1 0 eta rho X b H1).
    rewrite (right_type_rho_update_irrelevant T1 0 eta rho X b H1).
    rewrite (left_type_rho_update_irrelevant T2 0 eta rho X b H2).
    rewrite (right_type_rho_update_irrelevant T2 0 eta rho X b H2).
    specialize (IHT1 eta rho X b H1).
    specialize (IHT2 eta rho X b H2).
    split.
    + intros [Hv1 [Hv2 [Ht1 [Ht2 [body1 [body2 [E1 [E2 Hmap]]]]]]]].
      split; [exact Hv1 |]. split; [exact Hv2 |].
      split; [exact Ht1 |]. split; [exact Ht2 |].
      exists body1, body2. split; [exact E1 |]. split; [exact E2 |].
      intros arg1 arg2 Harg.
      unfold expression_lifting in *.
      destruct (Hmap arg1 arg2 (proj2 (IHT1 arg1 arg2) Harg)) as
        [Ha1 [Ha2 [w1 [w2 [Hs1 [Hs2 HR]]]]]].
      repeat split; try assumption. exists w1, w2. repeat split; try assumption.
      apply IHT2. exact HR.
    + intros [Hv1 [Hv2 [Ht1 [Ht2 [body1 [body2 [E1 [E2 Hmap]]]]]]]].
      split; [exact Hv1 |]. split; [exact Hv2 |].
      split; [exact Ht1 |]. split; [exact Ht2 |].
      exists body1, body2. split; [exact E1 |]. split; [exact E2 |].
      intros arg1 arg2 Harg.
      unfold expression_lifting in *.
      destruct (Hmap arg1 arg2 (proj1 (IHT1 arg1 arg2) Harg)) as
        [Ha1 [Ha2 [w1 [w2 [Hs1 [Hs2 HR]]]]]].
      repeat split; try assumption. exists w1, w2. repeat split; try assumption.
      apply IHT2. exact HR.
  - rewrite left_type_rho_update_irrelevant by exact Hfresh.
    rewrite right_type_rho_update_irrelevant by exact Hfresh.
    split.
    + intros [Hv1 [Hv2 [Ht1 [Ht2 [body1 [body2 [E1 [E2 Hmap]]]]]]]].
      split; [exact Hv1 |]. split; [exact Hv2 |].
      split; [exact Ht1 |]. split; [exact Ht2 |].
      exists body1, body2. split; [exact E1 |]. split; [exact E2 |].
      intros c.
      unfold expression_lifting in *.
      destruct (Hmap c) as [Ha1 [Ha2 [w1 [w2 [Hs1 [Hs2 HR]]]]]].
      repeat split.
      * rewrite left_type_rho_update_irrelevant in Ha1 by exact Hfresh. exact Ha1.
      * rewrite right_type_rho_update_irrelevant in Ha2 by exact Hfresh. exact Ha2.
      * exists w1, w2. repeat split; try assumption.
        apply (proj1 (IHT (c :: eta) rho X b Hfresh w1 w2)). exact HR.
    + intros [Hv1 [Hv2 [Ht1 [Ht2 [body1 [body2 [E1 [E2 Hmap]]]]]]]].
      split; [exact Hv1 |]. split; [exact Hv2 |].
      split; [exact Ht1 |]. split; [exact Ht2 |].
      exists body1, body2. split; [exact E1 |]. split; [exact E2 |].
      intros c.
      unfold expression_lifting in *.
      destruct (Hmap c) as [Ha1 [Ha2 [w1 [w2 [Hs1 [Hs2 HR]]]]]].
      repeat split.
      * rewrite left_type_rho_update_irrelevant by exact Hfresh. exact Ha1.
      * rewrite right_type_rho_update_irrelevant by exact Hfresh. exact Ha2.
      * exists w1, w2. repeat split; try assumption.
        apply (proj2 (IHT (c :: eta) rho X b Hfresh w1 w2)). exact HR.
Qed.

Lemma nth_error_snoc_last : forall (A : Type) (xs : list A) x,
  nth_error (xs ++ [x]) (length xs) = Some x.
Proof.
  intros A xs. induction xs; intros x; simpl; auto.
Qed.

Lemma nth_error_snoc_lt : forall (A : Type) (xs : list A) x i,
  i < length xs -> nth_error (xs ++ [x]) i = nth_error xs i.
Proof.
  intros A xs. induction xs as [|a xs IH]; intros x [|i] Hi; simpl in *.
  - lia.
  - lia.
  - reflexivity.
  - apply IH. lia.
Qed.

Lemma left_type_rec_open_relation : forall T j k eta rho X a,
  length eta = k ->
  lc_ty_at (S (j + k)) T ->
  ~ In X (fv_ty T) ->
  left_type_rec j (eta ++ [a]) rho T =
  left_type_rec j eta (relation_update rho X a)
    (open_ty_rec (j + k) (Ty_FVar X) T).
Proof.
  induction T; intros j k eta rho X b Hlen Hlc Hfresh; simpl in *.
  - assert (Hlt : n < S (j + k)) by (inversion Hlc; assumption).
    destruct (Nat.lt_trichotomy n j) as [Hnj | [E | Hjn]].
    + rewrite (proj2 (Nat.ltb_lt n j)) by exact Hnj.
      rewrite (proj2 (Nat.eqb_neq (j + k) n)) by lia.
      simpl. rewrite (proj2 (Nat.ltb_lt n j)) by exact Hnj. reflexivity.
    + subst n.
      rewrite Nat.ltb_irrefl.
      destruct k.
      * simpl in Hlen. apply length_zero_iff_nil in Hlen. subst eta. simpl.
        replace (j - j) with 0 by lia.
        replace (j + 0) with j by lia.
        cbn [left_type_rec]. rewrite Nat.eqb_refl.
        cbn [left_type_rec]. unfold relation_update.
        rewrite Nat.eqb_refl. reflexivity.
      * rewrite (proj2 (Nat.eqb_neq (j + S k) j)) by lia.
        simpl. rewrite Nat.ltb_irrefl.
        replace (j - j) with 0 by lia.
        rewrite nth_error_snoc_lt; [reflexivity | lia].
    + rewrite (proj2 (Nat.ltb_ge n j)) by lia.
      destruct (Nat.eq_dec n (j + k)) as [E | Hneq].
      * subst n. replace (j + k - j) with k by lia.
        rewrite <- Hlen. rewrite nth_error_snoc_last.
        rewrite Nat.eqb_refl. cbn [left_type_rec].
        unfold relation_update. rewrite Nat.eqb_refl. reflexivity.
      * assert (Hnlt : n < j + k) by lia.
        rewrite (proj2 (Nat.eqb_neq (j + k) n)) by congruence.
        simpl. rewrite (proj2 (Nat.ltb_ge n j)) by lia.
        assert (Hidx : n - j < length eta) by lia.
        rewrite nth_error_snoc_lt by exact Hidx. reflexivity.
  - assert (Hneq : X <> a) by (intro; subst; apply Hfresh; auto).
    rewrite relation_update_neq by exact Hneq. reflexivity.
  - assert (Hlc1 : lc_ty_at (S (j + k)) T1) by (inversion Hlc; assumption).
    assert (Hlc2 : lc_ty_at (S (j + k)) T2) by (inversion Hlc; assumption).
    rewrite in_app_iff in Hfresh. f_equal.
    + eapply IHT1; eauto; intuition.
    + eapply IHT2; eauto; intuition.
  - assert (Hlcbody : lc_ty_at (S (S (j + k))) T)
      by (inversion Hlc; assumption).
    f_equal.
    pose proof (IHT (S j) k eta rho X b Hlen) as IH.
    replace (S j + k) with (S (j + k)) in IH by lia.
    apply IH; assumption.
Qed.

Lemma right_type_rec_open_relation : forall T j k eta rho X a,
  length eta = k ->
  lc_ty_at (S (j + k)) T ->
  ~ In X (fv_ty T) ->
  right_type_rec j (eta ++ [a]) rho T =
  right_type_rec j eta (relation_update rho X a)
    (open_ty_rec (j + k) (Ty_FVar X) T).
Proof.
  induction T; intros j k eta rho X b Hlen Hlc Hfresh; simpl in *.
  - assert (Hlt : n < S (j + k)) by (inversion Hlc; assumption).
    destruct (Nat.lt_trichotomy n j) as [Hnj | [E | Hjn]].
    + rewrite (proj2 (Nat.ltb_lt n j)) by exact Hnj.
      rewrite (proj2 (Nat.eqb_neq (j + k) n)) by lia.
      simpl. rewrite (proj2 (Nat.ltb_lt n j)) by exact Hnj. reflexivity.
    + subst n.
      rewrite Nat.ltb_irrefl.
      destruct k.
      * simpl in Hlen. apply length_zero_iff_nil in Hlen. subst eta. simpl.
        replace (j - j) with 0 by lia.
        replace (j + 0) with j by lia.
        cbn [right_type_rec]. rewrite Nat.eqb_refl.
        cbn [right_type_rec]. unfold relation_update.
        rewrite Nat.eqb_refl. reflexivity.
      * rewrite (proj2 (Nat.eqb_neq (j + S k) j)) by lia.
        simpl. rewrite Nat.ltb_irrefl.
        replace (j - j) with 0 by lia.
        rewrite nth_error_snoc_lt; [reflexivity | lia].
    + rewrite (proj2 (Nat.ltb_ge n j)) by lia.
      destruct (Nat.eq_dec n (j + k)) as [E | Hneq].
      * subst n. replace (j + k - j) with k by lia.
        rewrite <- Hlen. rewrite nth_error_snoc_last.
        rewrite Nat.eqb_refl. cbn [right_type_rec].
        unfold relation_update. rewrite Nat.eqb_refl. reflexivity.
      * assert (Hnlt : n < j + k) by lia.
        rewrite (proj2 (Nat.eqb_neq (j + k) n)) by congruence.
        simpl. rewrite (proj2 (Nat.ltb_ge n j)) by lia.
        assert (Hidx : n - j < length eta) by lia.
        rewrite nth_error_snoc_lt by exact Hidx. reflexivity.
  - assert (Hneq : X <> a) by (intro; subst; apply Hfresh; auto).
    rewrite relation_update_neq by exact Hneq. reflexivity.
  - assert (Hlc1 : lc_ty_at (S (j + k)) T1) by (inversion Hlc; assumption).
    assert (Hlc2 : lc_ty_at (S (j + k)) T2) by (inversion Hlc; assumption).
    rewrite in_app_iff in Hfresh. f_equal.
    + eapply IHT1; eauto; intuition.
    + eapply IHT2; eauto; intuition.
  - assert (Hlcbody : lc_ty_at (S (S (j + k))) T)
      by (inversion Hlc; assumption).
    f_equal.
    pose proof (IHT (S j) k eta rho X b Hlen) as IH.
    replace (S j + k) with (S (j + k)) in IH by lia.
    apply IH; assumption.
Qed.

Lemma left_type_open_relation : forall T k eta rho X a,
  length eta = k -> lc_ty_at (S k) T -> ~ In X (fv_ty T) ->
  left_type (eta ++ [a]) rho T =
  left_type eta (relation_update rho X a)
    (open_ty_rec k (Ty_FVar X) T).
Proof.
  intros. unfold left_type.
  pose proof (left_type_rec_open_relation T 0 k eta rho X a H H0 H1) as Heq.
  simpl in Heq. exact Heq.
Qed.

Lemma right_type_open_relation : forall T k eta rho X a,
  length eta = k -> lc_ty_at (S k) T -> ~ In X (fv_ty T) ->
  right_type (eta ++ [a]) rho T =
  right_type eta (relation_update rho X a)
    (open_ty_rec k (Ty_FVar X) T).
Proof.
  intros. unfold right_type.
  pose proof (right_type_rec_open_relation T 0 k eta rho X a H H0 H1) as Heq.
  simpl in Heq. exact Heq.
Qed.

Lemma expression_lifting_change : forall A1 A2 B1 B2 R S t1 t2,
  A1 = B1 -> A2 = B2 ->
  (forall v1 v2, R v1 v2 <-> S v1 v2) ->
  expression_lifting A1 A2 R t1 t2 <->
  expression_lifting B1 B2 S t1 t2.
Proof.
  intros A1 A2 B1 B2 R S t1 t2 E1 E2 HRS. subst B1. subst B2.
  apply expression_lifting_equiv. exact HRS.
Qed.

Lemma value_relation_open_relation : forall T k eta rho X a,
  length eta = k ->
  lc_ty_at (S k) T ->
  ~ In X (fv_ty T) ->
  forall v1 v2,
    value_relation (eta ++ [a]) rho T v1 v2 <->
    value_relation eta (relation_update rho X a)
      (open_ty_rec k (Ty_FVar X) T) v1 v2.
Proof.
  induction T; intros k eta rho X b Hlen Hlc Hfresh v1 v2.
  - assert (HL := left_type_open_relation (Ty_BVar n) k eta rho X b
      Hlen Hlc Hfresh).
    assert (HR := right_type_open_relation (Ty_BVar n) k eta rho X b
      Hlen Hlc Hfresh).
    cbn [value_relation]. rewrite HL, HR.
    assert (Hlt : n < S k) by (inversion Hlc; assumption).
    destruct (Nat.eq_dec n k) as [E | Hneq].
    + subst n.
      rewrite <- Hlen. rewrite nth_error_snoc_last.
      assert (Hopen : open_ty_rec (length eta) (Ty_FVar X)
        (Ty_BVar (length eta)) = Ty_FVar X).
      { simpl. rewrite Nat.eqb_refl. reflexivity. }
      rewrite Hopen. cbn [value_relation]. rewrite relation_update_eq. reflexivity.
    + assert (Hnk : n < k) by lia.
      assert (Hopen : open_ty_rec k (Ty_FVar X) (Ty_BVar n) = Ty_BVar n).
      { simpl. rewrite (proj2 (Nat.eqb_neq k n)) by congruence. reflexivity. }
      rewrite Hopen. cbn [value_relation].
      rewrite nth_error_snoc_lt by (rewrite Hlen; exact Hnk).
      reflexivity.
  - assert (Hneq : X <> a).
    { intro E. subst X. apply Hfresh. simpl. auto. }
    assert (HL := left_type_open_relation (Ty_FVar a) k eta rho X b
      Hlen Hlc Hfresh).
    assert (HR := right_type_open_relation (Ty_FVar a) k eta rho X b
      Hlen Hlc Hfresh).
    cbn [value_relation]. rewrite HL, HR.
    assert (Hopen : open_ty_rec k (Ty_FVar X) (Ty_FVar a) = Ty_FVar a)
      by reflexivity.
    rewrite Hopen. cbn [value_relation]. unfold relation_update.
    rewrite (proj2 (Nat.eqb_neq X a)) by exact Hneq. reflexivity.
  - assert (Hlc1 : lc_ty_at (S k) T1) by (inversion Hlc; assumption).
    assert (Hlc2 : lc_ty_at (S k) T2) by (inversion Hlc; assumption).
    assert (Hfresh1 : ~ In X (fv_ty T1)).
    { intro Hin. apply Hfresh. simpl. apply in_app_iff. auto. }
    assert (Hfresh2 : ~ In X (fv_ty T2)).
    { intro Hin. apply Hfresh. simpl. apply in_app_iff. auto. }
    assert (HL := left_type_open_relation (Ty_Arrow T1 T2) k eta rho X b
      Hlen Hlc Hfresh).
    assert (HR := right_type_open_relation (Ty_Arrow T1 T2) k eta rho X b
      Hlen Hlc Hfresh).
    cbn [value_relation]. rewrite HL, HR.
    assert (HL1 := left_type_open_relation T1 k eta rho X b
      Hlen Hlc1 Hfresh1).
    assert (HR1 := right_type_open_relation T1 k eta rho X b
      Hlen Hlc1 Hfresh1).
    assert (HL2 := left_type_open_relation T2 k eta rho X b
      Hlen Hlc2 Hfresh2).
    assert (HR2 := right_type_open_relation T2 k eta rho X b
      Hlen Hlc2 Hfresh2).
    specialize (IHT1 k eta rho X b Hlen Hlc1 Hfresh1).
    specialize (IHT2 k eta rho X b Hlen Hlc2 Hfresh2).
    split.
    + intros [Hv1 [Hv2 [Ht1 [Ht2 [body1 [body2 [E1 [E2 Hmap]]]]]]]].
      split; [exact Hv1 |]. split; [exact Hv2 |].
      split; [exact Ht1 |]. split; [exact Ht2 |].
      exists body1, body2. split.
      * rewrite <- HL1. exact E1.
      * split.
        -- rewrite <- HR1. exact E2.
        -- intros arg1 arg2 Harg.
           pose proof (Hmap arg1 arg2 (proj2 (IHT1 arg1 arg2) Harg)) as Hout.
           apply (proj1 (expression_lifting_change _ _ _ _ _ _ _ _
             HL2 HR2 IHT2)). exact Hout.
    + intros [Hv1 [Hv2 [Ht1 [Ht2 [body1 [body2 [E1 [E2 Hmap]]]]]]]].
      split; [exact Hv1 |]. split; [exact Hv2 |].
      split; [exact Ht1 |]. split; [exact Ht2 |].
      exists body1, body2. split.
      * rewrite HL1. exact E1.
      * split.
        -- rewrite HR1. exact E2.
        -- intros arg1 arg2 Harg.
           pose proof (Hmap arg1 arg2 (proj1 (IHT1 arg1 arg2) Harg)) as Hout.
           apply (proj2 (expression_lifting_change _ _ _ _ _ _ _ _
             HL2 HR2 IHT2)). exact Hout.
  - assert (Hbodylc : lc_ty_at (S (S k)) T) by (inversion Hlc; assumption).
    assert (HL := left_type_open_relation (Ty_All T) k eta rho X b
      Hlen Hlc Hfresh).
    assert (HR := right_type_open_relation (Ty_All T) k eta rho X b
      Hlen Hlc Hfresh).
    cbn [value_relation]. rewrite HL, HR.
    split.
    + intros [Hv1 [Hv2 [Ht1 [Ht2 [body1 [body2 [E1 [E2 Hmap]]]]]]]].
      split; [exact Hv1 |]. split; [exact Hv2 |].
      split; [exact Ht1 |]. split; [exact Ht2 |].
      exists body1, body2. split; [exact E1 |]. split; [exact E2 |].
      intros c.
      assert (Hlen' : length (c :: eta) = S k) by (simpl; lia).
      specialize (IHT (S k) (c :: eta) rho X b Hlen' Hbodylc Hfresh).
      pose proof (Hmap c) as Hout.
      assert (HLbody := left_type_open_relation T (S k) (c :: eta)
        rho X b Hlen' Hbodylc Hfresh).
      assert (HRbody := right_type_open_relation T (S k) (c :: eta)
        rho X b Hlen' Hbodylc Hfresh).
      apply (proj1 (expression_lifting_change _ _ _ _ _ _ _ _
        HLbody HRbody IHT)). exact Hout.
    + intros [Hv1 [Hv2 [Ht1 [Ht2 [body1 [body2 [E1 [E2 Hmap]]]]]]]].
      split; [exact Hv1 |]. split; [exact Hv2 |].
      split; [exact Ht1 |]. split; [exact Ht2 |].
      exists body1, body2. split; [exact E1 |]. split; [exact E2 |].
      intros c.
      assert (Hlen' : length (c :: eta) = S k) by (simpl; lia).
      specialize (IHT (S k) (c :: eta) rho X b Hlen' Hbodylc Hfresh).
      pose proof (Hmap c) as Hout.
      assert (HLbody := left_type_open_relation T (S k) (c :: eta)
        rho X b Hlen' Hbodylc Hfresh).
      assert (HRbody := right_type_open_relation T (S k) (c :: eta)
        rho X b Hlen' Hbodylc Hfresh).
      apply (proj2 (expression_lifting_change _ _ _ _ _ _ _ _
        HLbody HRbody IHT)). exact Hout.
Qed.

Lemma left_type_rec_env_equiv_gen : forall T j k eta1 eta2 rho,
  lc_ty_at (j + k) T ->
  (forall i, i < k -> nth_error eta1 i = nth_error eta2 i) ->
  left_type_rec j eta1 rho T = left_type_rec j eta2 rho T.
Proof.
  induction T; intros j k eta1 eta2 rho Hlc Hagree; simpl.
  - assert (Hlt : n < j + k) by (inversion Hlc; assumption).
    destruct (n <? j) eqn:Hnj.
    + reflexivity.
    + apply Nat.ltb_ge in Hnj.
      assert (Hidx : n - j < k) by lia.
      rewrite (Hagree (n - j) Hidx). reflexivity.
  - reflexivity.
  - assert (Hlc1 : lc_ty_at (j + k) T1) by (inversion Hlc; assumption).
    assert (Hlc2 : lc_ty_at (j + k) T2) by (inversion Hlc; assumption).
    f_equal; [eapply IHT1 | eapply IHT2]; eauto.
  - assert (Hbody : lc_ty_at (S (j + k)) T) by (inversion Hlc; assumption).
    f_equal. pose proof (IHT (S j) k eta1 eta2 rho) as IH.
    replace (S j + k) with (S (j + k)) in IH by lia.
    apply IH; assumption.
Qed.

Lemma right_type_rec_env_equiv_gen : forall T j k eta1 eta2 rho,
  lc_ty_at (j + k) T ->
  (forall i, i < k -> nth_error eta1 i = nth_error eta2 i) ->
  right_type_rec j eta1 rho T = right_type_rec j eta2 rho T.
Proof.
  induction T; intros j k eta1 eta2 rho Hlc Hagree; simpl.
  - assert (Hlt : n < j + k) by (inversion Hlc; assumption).
    destruct (n <? j) eqn:Hnj.
    + reflexivity.
    + apply Nat.ltb_ge in Hnj.
      assert (Hidx : n - j < k) by lia.
      rewrite (Hagree (n - j) Hidx). reflexivity.
  - reflexivity.
  - assert (Hlc1 : lc_ty_at (j + k) T1) by (inversion Hlc; assumption).
    assert (Hlc2 : lc_ty_at (j + k) T2) by (inversion Hlc; assumption).
    f_equal; [eapply IHT1 | eapply IHT2]; eauto.
  - assert (Hbody : lc_ty_at (S (j + k)) T) by (inversion Hlc; assumption).
    f_equal. pose proof (IHT (S j) k eta1 eta2 rho) as IH.
    replace (S j + k) with (S (j + k)) in IH by lia.
    apply IH; assumption.
Qed.

Lemma left_type_rec_env_equiv : forall T k eta1 eta2 rho,
  lc_ty_at k T ->
  (forall i, i < k -> nth_error eta1 i = nth_error eta2 i) ->
  left_type_rec 0 eta1 rho T = left_type_rec 0 eta2 rho T.
Proof.
  intros. apply left_type_rec_env_equiv_gen with (k := k).
  - simpl. exact H.
  - exact H0.
Qed.

Lemma right_type_rec_env_equiv : forall T k eta1 eta2 rho,
  lc_ty_at k T ->
  (forall i, i < k -> nth_error eta1 i = nth_error eta2 i) ->
  right_type_rec 0 eta1 rho T = right_type_rec 0 eta2 rho T.
Proof.
  intros. apply right_type_rec_env_equiv_gen with (k := k).
  - simpl. exact H.
  - exact H0.
Qed.

Lemma value_relation_env_equiv : forall T k eta1 eta2 rho,
  lc_ty_at k T ->
  (forall i, i < k -> nth_error eta1 i = nth_error eta2 i) ->
  forall v1 v2,
    value_relation eta1 rho T v1 v2 <->
    value_relation eta2 rho T v1 v2.
Proof.
  induction T; intros k eta1 eta2 rho Hlc Hagree v1 v2.
  - assert (HL := left_type_rec_env_equiv (Ty_BVar n) k eta1 eta2 rho
      Hlc Hagree).
    assert (HR := right_type_rec_env_equiv (Ty_BVar n) k eta1 eta2 rho
      Hlc Hagree).
    cbn [value_relation]. unfold left_type, right_type. rewrite HL, HR.
    assert (Hlt : n < k) by (inversion Hlc; assumption).
    rewrite (Hagree n Hlt). reflexivity.
  - reflexivity.
  - assert (Hlc1 : lc_ty_at k T1) by (inversion Hlc; assumption).
    assert (Hlc2 : lc_ty_at k T2) by (inversion Hlc; assumption).
    assert (HL := left_type_rec_env_equiv (Ty_Arrow T1 T2)
      k eta1 eta2 rho Hlc Hagree).
    assert (HR := right_type_rec_env_equiv (Ty_Arrow T1 T2)
      k eta1 eta2 rho Hlc Hagree).
    cbn [value_relation]. unfold left_type, right_type. rewrite HL, HR.
    assert (HL1 := left_type_rec_env_equiv T1 k eta1 eta2 rho Hlc1 Hagree).
    assert (HR1 := right_type_rec_env_equiv T1 k eta1 eta2 rho Hlc1 Hagree).
    assert (HL2 := left_type_rec_env_equiv T2 k eta1 eta2 rho Hlc2 Hagree).
    assert (HR2 := right_type_rec_env_equiv T2 k eta1 eta2 rho Hlc2 Hagree).
    specialize (IHT1 k eta1 eta2 rho Hlc1 Hagree).
    specialize (IHT2 k eta1 eta2 rho Hlc2 Hagree).
    split.
    + intros [Hv1 [Hv2 [Ht1 [Ht2 [body1 [body2 [E1 [E2 Hmap]]]]]]]].
      split; [exact Hv1 |]. split; [exact Hv2 |].
      split; [exact Ht1 |]. split; [exact Ht2 |].
      exists body1, body2. split.
      * rewrite <- HL1. exact E1.
      * split.
        -- rewrite <- HR1. exact E2.
        -- intros arg1 arg2 Harg.
           pose proof (Hmap arg1 arg2 (proj2 (IHT1 arg1 arg2) Harg)) as Hout.
           apply (proj1 (expression_lifting_change _ _ _ _ _ _ _ _
             HL2 HR2 IHT2)). exact Hout.
    + intros [Hv1 [Hv2 [Ht1 [Ht2 [body1 [body2 [E1 [E2 Hmap]]]]]]]].
      split; [exact Hv1 |]. split; [exact Hv2 |].
      split; [exact Ht1 |]. split; [exact Ht2 |].
      exists body1, body2. split.
      * rewrite HL1. exact E1.
      * split.
        -- rewrite HR1. exact E2.
        -- intros arg1 arg2 Harg.
           pose proof (Hmap arg1 arg2 (proj1 (IHT1 arg1 arg2) Harg)) as Hout.
           apply (proj2 (expression_lifting_change _ _ _ _ _ _ _ _
             HL2 HR2 IHT2)). exact Hout.
  - assert (Hbodylc : lc_ty_at (S k) T) by (inversion Hlc; assumption).
    assert (HL := left_type_rec_env_equiv (Ty_All T)
      k eta1 eta2 rho Hlc Hagree).
    assert (HR := right_type_rec_env_equiv (Ty_All T)
      k eta1 eta2 rho Hlc Hagree).
    cbn [value_relation]. unfold left_type, right_type. rewrite HL, HR.
    split.
    + intros [Hv1 [Hv2 [Ht1 [Ht2 [body1 [body2 [E1 [E2 Hmap]]]]]]]].
      split; [exact Hv1 |]. split; [exact Hv2 |].
      split; [exact Ht1 |]. split; [exact Ht2 |].
      exists body1, body2. split; [exact E1 |]. split; [exact E2 |].
      intros a.
      assert (Hagree' : forall i, i < S k ->
        nth_error (a :: eta1) i = nth_error (a :: eta2) i).
      { intros [|i] Hi; simpl; [reflexivity | apply Hagree; lia]. }
      specialize (IHT (S k) (a :: eta1) (a :: eta2) rho
        Hbodylc Hagree').
      assert (HLbody := left_type_rec_env_equiv T (S k)
        (a :: eta1) (a :: eta2) rho Hbodylc Hagree').
      assert (HRbody := right_type_rec_env_equiv T (S k)
        (a :: eta1) (a :: eta2) rho Hbodylc Hagree').
      apply (proj1 (expression_lifting_change _ _ _ _ _ _ _ _
        HLbody HRbody IHT)). apply Hmap.
    + intros [Hv1 [Hv2 [Ht1 [Ht2 [body1 [body2 [E1 [E2 Hmap]]]]]]]].
      split; [exact Hv1 |]. split; [exact Hv2 |].
      split; [exact Ht1 |]. split; [exact Ht2 |].
      exists body1, body2. split; [exact E1 |]. split; [exact E2 |].
      intros a.
      assert (Hagree' : forall i, i < S k ->
        nth_error (a :: eta1) i = nth_error (a :: eta2) i).
      { intros [|i] Hi; simpl; [reflexivity | apply Hagree; lia]. }
      specialize (IHT (S k) (a :: eta1) (a :: eta2) rho
        Hbodylc Hagree').
      assert (HLbody := left_type_rec_env_equiv T (S k)
        (a :: eta1) (a :: eta2) rho Hbodylc Hagree').
      assert (HRbody := right_type_rec_env_equiv T (S k)
        (a :: eta1) (a :: eta2) rho Hbodylc Hagree').
      apply (proj2 (expression_lifting_change _ _ _ _ _ _ _ _
        HLbody HRbody IHT)). apply Hmap.
Qed.

Lemma value_relation_closed_env : forall T rho eta1 eta2,
  locally_closed_ty T -> forall v1 v2,
  value_relation eta1 rho T v1 v2 <-> value_relation eta2 rho T v1 v2.
Proof.
  intros T rho eta1 eta2 Hlc v1 v2.
  apply value_relation_env_equiv with (k := 0); [exact Hlc | lia].
Qed.

Lemma left_type_rec_depth_irrelevant : forall T k,
  lc_ty_at k T -> forall j eta rho,
  left_type_rec (k + j) eta rho T = left_type_rec k [] rho T.
Proof.
  intros T k Hlc. induction Hlc; intros j eta rho; simpl.
  - rewrite (proj2 (Nat.ltb_lt i (k + j))) by lia.
    rewrite (proj2 (Nat.ltb_lt i k)) by assumption. reflexivity.
  - reflexivity.
  - rewrite IHHlc1, IHHlc2. reflexivity.
  - f_equal. replace (S k + j) with (S (k + j)) by lia.
    apply IHHlc.
Qed.

Lemma right_type_rec_depth_irrelevant : forall T k,
  lc_ty_at k T -> forall j eta rho,
  right_type_rec (k + j) eta rho T = right_type_rec k [] rho T.
Proof.
  intros T k Hlc. induction Hlc; intros j eta rho; simpl.
  - rewrite (proj2 (Nat.ltb_lt i (k + j))) by lia.
    rewrite (proj2 (Nat.ltb_lt i k)) by assumption. reflexivity.
  - reflexivity.
  - rewrite IHHlc1, IHHlc2. reflexivity.
  - f_equal. replace (S k + j) with (S (k + j)) by lia.
    apply IHHlc.
Qed.

Lemma left_type_rec_open_type : forall T j k eta rho U a,
  length eta = k -> lc_ty_at (S (j + k)) T -> locally_closed_ty U ->
  a.(assignment_left) = left_type [] rho U ->
  left_type_rec j (eta ++ [a]) rho T =
  left_type_rec j eta rho (open_ty_rec (j + k) U T).
Proof.
  induction T; intros j k eta rho U b Hlen Hlc HU Hb; simpl in *.
  - assert (Hlt : n < S (j + k)) by (inversion Hlc; assumption).
    destruct (Nat.lt_trichotomy n j) as [Hnj | [E | Hjn]].
    + rewrite (proj2 (Nat.ltb_lt n j)) by exact Hnj.
      rewrite (proj2 (Nat.eqb_neq (j + k) n)) by lia.
      simpl. rewrite (proj2 (Nat.ltb_lt n j)) by exact Hnj. reflexivity.
    + subst n. rewrite Nat.ltb_irrefl. destruct k.
      * simpl in Hlen. apply length_zero_iff_nil in Hlen. subst eta. simpl.
        replace (j - j) with 0 by lia. replace (j + 0) with j by lia.
        cbn [left_type_rec]. rewrite Nat.eqb_refl.
        cbn. rewrite Hb.
        pose proof (left_type_rec_depth_irrelevant U 0 HU j [] rho) as Heq.
        simpl in Heq. symmetry. exact Heq.
      * rewrite (proj2 (Nat.eqb_neq (j + S k) j)) by lia.
        simpl. rewrite Nat.ltb_irrefl. replace (j - j) with 0 by lia.
        rewrite nth_error_snoc_lt; [reflexivity | lia].
    + rewrite (proj2 (Nat.ltb_ge n j)) by lia.
      destruct (Nat.eq_dec n (j + k)) as [E | Hneq].
      * subst n. replace (j + k - j) with k by lia.
        rewrite <- Hlen. rewrite nth_error_snoc_last. rewrite Nat.eqb_refl.
        rewrite Hb.
        pose proof (left_type_rec_depth_irrelevant U 0 HU j eta rho) as Heq.
        simpl in Heq. symmetry. exact Heq.
      * assert (Hnlt : n < j + k) by lia.
        rewrite (proj2 (Nat.eqb_neq (j + k) n)) by congruence.
        simpl. rewrite (proj2 (Nat.ltb_ge n j)) by lia.
        assert (Hidx : n - j < length eta) by lia.
        rewrite nth_error_snoc_lt by exact Hidx. reflexivity.
  - reflexivity.
  - assert (Hlc1 : lc_ty_at (S (j + k)) T1) by (inversion Hlc; assumption).
    assert (Hlc2 : lc_ty_at (S (j + k)) T2) by (inversion Hlc; assumption).
    f_equal; [eapply IHT1 | eapply IHT2]; eauto.
  - assert (Hbody : lc_ty_at (S (S (j + k))) T) by (inversion Hlc; assumption).
    f_equal. pose proof (IHT (S j) k eta rho U b Hlen) as IH.
    replace (S j + k) with (S (j + k)) in IH by lia.
    apply IH; assumption.
Qed.

Lemma right_type_rec_open_type : forall T j k eta rho U a,
  length eta = k -> lc_ty_at (S (j + k)) T -> locally_closed_ty U ->
  a.(assignment_right) = right_type [] rho U ->
  right_type_rec j (eta ++ [a]) rho T =
  right_type_rec j eta rho (open_ty_rec (j + k) U T).
Proof.
  induction T; intros j k eta rho U b Hlen Hlc HU Hb; simpl in *.
  - assert (Hlt : n < S (j + k)) by (inversion Hlc; assumption).
    destruct (Nat.lt_trichotomy n j) as [Hnj | [E | Hjn]].
    + rewrite (proj2 (Nat.ltb_lt n j)) by exact Hnj.
      rewrite (proj2 (Nat.eqb_neq (j + k) n)) by lia.
      simpl. rewrite (proj2 (Nat.ltb_lt n j)) by exact Hnj. reflexivity.
    + subst n. rewrite Nat.ltb_irrefl. destruct k.
      * simpl in Hlen. apply length_zero_iff_nil in Hlen. subst eta. simpl.
        replace (j - j) with 0 by lia. replace (j + 0) with j by lia.
        cbn [right_type_rec]. rewrite Nat.eqb_refl. cbn. rewrite Hb.
        pose proof (right_type_rec_depth_irrelevant U 0 HU j [] rho) as Heq.
        simpl in Heq. symmetry. exact Heq.
      * rewrite (proj2 (Nat.eqb_neq (j + S k) j)) by lia.
        simpl. rewrite Nat.ltb_irrefl. replace (j - j) with 0 by lia.
        rewrite nth_error_snoc_lt; [reflexivity | lia].
    + rewrite (proj2 (Nat.ltb_ge n j)) by lia.
      destruct (Nat.eq_dec n (j + k)) as [E | Hneq].
      * subst n. replace (j + k - j) with k by lia.
        rewrite <- Hlen. rewrite nth_error_snoc_last. rewrite Nat.eqb_refl.
        rewrite Hb.
        pose proof (right_type_rec_depth_irrelevant U 0 HU j eta rho) as Heq.
        simpl in Heq. symmetry. exact Heq.
      * assert (Hnlt : n < j + k) by lia.
        rewrite (proj2 (Nat.eqb_neq (j + k) n)) by congruence.
        simpl. rewrite (proj2 (Nat.ltb_ge n j)) by lia.
        assert (Hidx : n - j < length eta) by lia.
        rewrite nth_error_snoc_lt by exact Hidx. reflexivity.
  - reflexivity.
  - assert (Hlc1 : lc_ty_at (S (j + k)) T1) by (inversion Hlc; assumption).
    assert (Hlc2 : lc_ty_at (S (j + k)) T2) by (inversion Hlc; assumption).
    f_equal; [eapply IHT1 | eapply IHT2]; eauto.
  - assert (Hbody : lc_ty_at (S (S (j + k))) T) by (inversion Hlc; assumption).
    f_equal. pose proof (IHT (S j) k eta rho U b Hlen) as IH.
    replace (S j + k) with (S (j + k)) in IH by lia.
    apply IH; assumption.
Qed.

Lemma left_type_open_type : forall T k eta rho U a,
  length eta = k -> lc_ty_at (S k) T -> locally_closed_ty U ->
  a.(assignment_left) = left_type [] rho U ->
  left_type (eta ++ [a]) rho T = left_type eta rho (open_ty_rec k U T).
Proof.
  intros. unfold left_type.
  pose proof (left_type_rec_open_type T 0 k eta rho U a H H0 H1 H2) as Heq.
  simpl in Heq. exact Heq.
Qed.

Lemma right_type_open_type : forall T k eta rho U a,
  length eta = k -> lc_ty_at (S k) T -> locally_closed_ty U ->
  a.(assignment_right) = right_type [] rho U ->
  right_type (eta ++ [a]) rho T = right_type eta rho (open_ty_rec k U T).
Proof.
  intros. unfold right_type.
  pose proof (right_type_rec_open_type T 0 k eta rho U a H H0 H1 H2) as Heq.
  simpl in Heq. exact Heq.
Qed.

Lemma value_relation_open_type : forall T k eta rho U a,
  length eta = k -> lc_ty_at (S k) T -> locally_closed_ty U ->
  a.(assignment_left) = left_type [] rho U ->
  a.(assignment_right) = right_type [] rho U ->
  a.(assignment_relation) = value_relation [] rho U ->
  forall v1 v2,
    value_relation (eta ++ [a]) rho T v1 v2 <->
    value_relation eta rho (open_ty_rec k U T) v1 v2.
Proof.
  induction T; intros k eta rho U b Hlen Hlc HU HbL HbR HbRel v1 v2.
  - assert (HL := left_type_open_type (Ty_BVar n) k eta rho U b
      Hlen Hlc HU HbL).
    assert (HR := right_type_open_type (Ty_BVar n) k eta rho U b
      Hlen Hlc HU HbR).
    cbn [value_relation]. rewrite HL, HR.
    assert (Hlt : n < S k) by (inversion Hlc; assumption).
    destruct (Nat.eq_dec n k) as [E | Hneq].
    + subst n. rewrite <- Hlen. rewrite nth_error_snoc_last.
      assert (Hopen : open_ty_rec (length eta) U (Ty_BVar (length eta)) = U).
      { simpl. rewrite Nat.eqb_refl. reflexivity. }
      rewrite Hopen. rewrite HbRel.
      pose proof (value_relation_closed_env U rho [] eta HU v1 v2) as Heq.
      split.
      * intros [Hv1 [Hv2 [Ht1 [Ht2 HR0]]]]. apply Heq. exact HR0.
      * intros HReta.
        pose proof (proj2 Heq HReta) as HR0.
        pose proof (value_relation_values _ _ _ _ _ HReta) as [Hv1 Hv2].
        pose proof (value_relation_typing _ _ _ _ _ HReta) as [Ht1 Ht2].
        repeat split; assumption.
    + assert (Hnk : n < k) by lia.
      assert (Hopen : open_ty_rec k U (Ty_BVar n) = Ty_BVar n).
      { simpl. rewrite (proj2 (Nat.eqb_neq k n)) by congruence. reflexivity. }
      rewrite Hopen. cbn [value_relation].
      rewrite nth_error_snoc_lt by (rewrite Hlen; exact Hnk). reflexivity.
  - assert (HL := left_type_open_type (Ty_FVar a) k eta rho U b
      Hlen Hlc HU HbL).
    assert (HR := right_type_open_type (Ty_FVar a) k eta rho U b
      Hlen Hlc HU HbR).
    cbn [value_relation]. rewrite HL, HR. reflexivity.
  - assert (Hlc1 : lc_ty_at (S k) T1) by (inversion Hlc; assumption).
    assert (Hlc2 : lc_ty_at (S k) T2) by (inversion Hlc; assumption).
    assert (HL := left_type_open_type (Ty_Arrow T1 T2) k eta rho U b
      Hlen Hlc HU HbL).
    assert (HR := right_type_open_type (Ty_Arrow T1 T2) k eta rho U b
      Hlen Hlc HU HbR).
    cbn [value_relation]. rewrite HL, HR.
    assert (HL1 := left_type_open_type T1 k eta rho U b
      Hlen Hlc1 HU HbL).
    assert (HR1 := right_type_open_type T1 k eta rho U b
      Hlen Hlc1 HU HbR).
    assert (HL2 := left_type_open_type T2 k eta rho U b
      Hlen Hlc2 HU HbL).
    assert (HR2 := right_type_open_type T2 k eta rho U b
      Hlen Hlc2 HU HbR).
    specialize (IHT1 k eta rho U b Hlen Hlc1 HU HbL HbR HbRel).
    specialize (IHT2 k eta rho U b Hlen Hlc2 HU HbL HbR HbRel).
    split.
    + intros [Hv1 [Hv2 [Ht1 [Ht2 [body1 [body2 [E1 [E2 Hmap]]]]]]]].
      split; [exact Hv1 |]. split; [exact Hv2 |].
      split; [exact Ht1 |]. split; [exact Ht2 |].
      exists body1, body2. split.
      * rewrite <- HL1. exact E1.
      * split.
        -- rewrite <- HR1. exact E2.
        -- intros arg1 arg2 Harg.
           pose proof (Hmap arg1 arg2 (proj2 (IHT1 arg1 arg2) Harg)) as Hout.
           apply (proj1 (expression_lifting_change _ _ _ _ _ _ _ _
             HL2 HR2 IHT2)). exact Hout.
    + intros [Hv1 [Hv2 [Ht1 [Ht2 [body1 [body2 [E1 [E2 Hmap]]]]]]]].
      split; [exact Hv1 |]. split; [exact Hv2 |].
      split; [exact Ht1 |]. split; [exact Ht2 |].
      exists body1, body2. split.
      * rewrite HL1. exact E1.
      * split.
        -- rewrite HR1. exact E2.
        -- intros arg1 arg2 Harg.
           pose proof (Hmap arg1 arg2 (proj1 (IHT1 arg1 arg2) Harg)) as Hout.
           apply (proj2 (expression_lifting_change _ _ _ _ _ _ _ _
             HL2 HR2 IHT2)). exact Hout.
  - assert (Hbodylc : lc_ty_at (S (S k)) T) by (inversion Hlc; assumption).
    assert (HL := left_type_open_type (Ty_All T) k eta rho U b
      Hlen Hlc HU HbL).
    assert (HR := right_type_open_type (Ty_All T) k eta rho U b
      Hlen Hlc HU HbR).
    cbn [value_relation]. rewrite HL, HR.
    split.
    + intros [Hv1 [Hv2 [Ht1 [Ht2 [body1 [body2 [E1 [E2 Hmap]]]]]]]].
      split; [exact Hv1 |]. split; [exact Hv2 |].
      split; [exact Ht1 |]. split; [exact Ht2 |].
      exists body1, body2. split; [exact E1 |]. split; [exact E2 |].
      intros c.
      assert (Hlen' : length (c :: eta) = S k) by (simpl; lia).
      specialize (IHT (S k) (c :: eta) rho U b Hlen' Hbodylc HU
        HbL HbR HbRel).
      assert (HLbody := left_type_open_type T (S k) (c :: eta)
        rho U b Hlen' Hbodylc HU HbL).
      assert (HRbody := right_type_open_type T (S k) (c :: eta)
        rho U b Hlen' Hbodylc HU HbR).
      apply (proj1 (expression_lifting_change _ _ _ _ _ _ _ _
        HLbody HRbody IHT)). apply Hmap.
    + intros [Hv1 [Hv2 [Ht1 [Ht2 [body1 [body2 [E1 [E2 Hmap]]]]]]]].
      split; [exact Hv1 |]. split; [exact Hv2 |].
      split; [exact Ht1 |]. split; [exact Ht2 |].
      exists body1, body2. split; [exact E1 |]. split; [exact E2 |].
      intros c.
      assert (Hlen' : length (c :: eta) = S k) by (simpl; lia).
      specialize (IHT (S k) (c :: eta) rho U b Hlen' Hbodylc HU
        HbL HbR HbRel).
      assert (HLbody := left_type_open_type T (S k) (c :: eta)
        rho U b Hlen' Hbodylc HU HbL).
      assert (HRbody := right_type_open_type T (S k) (c :: eta)
        rho U b Hlen' Hbodylc HU HbR).
      apply (proj2 (expression_lifting_change _ _ _ _ _ _ _ _
        HLbody HRbody IHT)). apply Hmap.
Qed.

Lemma lookup_context_ftv : forall Gamma x T X,
  lookup_context x Gamma = Some T ->
  In X (fv_ty T) -> In X (ftv_context Gamma).
Proof.
  induction Gamma as [|[y U] Gamma IH]; intros x T X Hlookup Hin; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + inversion Hlookup; subst. apply in_or_app. left. exact Hin.
    + apply in_or_app. right. eapply IH; eauto.
Qed.

Lemma related_substitutions_relation_update :
  forall rho Gamma gamma1 gamma2 X a,
  related_substitutions rho Gamma gamma1 gamma2 ->
  ~ In X (ftv_context Gamma) ->
  related_substitutions (relation_update rho X a) Gamma gamma1 gamma2.
Proof.
  intros rho Gamma gamma1 gamma2 X a Hgamma Hfresh x T Hlookup.
  assert (Hnotin : ~ In X (fv_ty T)).
  { intro Hin. apply Hfresh. eapply lookup_context_ftv; eauto. }
  apply (proj2 (value_relation_rho_update_irrelevant T [] rho X a
    Hnotin (gamma1 x) (gamma2 x))).
  apply Hgamma. exact Hlookup.
Qed.

(*只要给 t 的自由类型变量和自由程序变量提供两组相关的替换，
  替换后得到的两个完整程序就会在类型 T 下相关。
  它其实就是：
  > 相关输入产生相关输出。 *)
Definition semantically_typed
    (Delta : ty_context) (Gamma : context) (t : tm) (T : ty) : Prop :=
  forall (theta1 theta2 : type_substitution)
         (rho : relation_env)
         (gamma1 gamma2 : term_substitution),
    type_substitution_closed theta1 ->
    type_substitution_closed theta2 ->
    term_substitution_closed gamma1 ->
    term_substitution_closed gamma2 ->
    related_type_substitutions Delta theta1 theta2 rho ->
    related_substitutions rho Gamma gamma1 gamma2 ->
    expression_relation [] rho T
      (instantiate theta1 gamma1 t)
      (instantiate theta2 gamma2 t).

Lemma instantiated_typing_left : forall Delta Gamma t T,
  has_type Delta Gamma t T -> context_wf Delta Gamma ->
  forall theta1 theta2 rho gamma1 gamma2,
  type_substitution_closed theta1 -> term_substitution_closed gamma1 ->
  related_type_substitutions Delta theta1 theta2 rho ->
  related_substitutions rho Gamma gamma1 gamma2 ->
  has_type [] empty (instantiate theta1 gamma1 t) (left_type [] rho T).
Proof.
  intros Delta Gamma t T Hty Hctx theta1 theta2 rho gamma1 gamma2
    Htheta1 Hgamma1 Htypes Hterms.
  rewrite left_type_related with (Delta := Delta) (theta1 := theta1)
    (theta2 := theta2); [|exact Htypes|].
  - eapply has_type_instantiate; eauto.
    + apply related_types_left_wf with (theta2 := theta2) (rho := rho).
      exact Htypes.
    + eapply related_terms_left_typed; eauto.
  - eapply typing_type_wf; eauto.
Qed.

Lemma instantiated_typing_right : forall Delta Gamma t T,
  has_type Delta Gamma t T -> context_wf Delta Gamma ->
  forall theta1 theta2 rho gamma1 gamma2,
  type_substitution_closed theta2 -> term_substitution_closed gamma2 ->
  related_type_substitutions Delta theta1 theta2 rho ->
  related_substitutions rho Gamma gamma1 gamma2 ->
  has_type [] empty (instantiate theta2 gamma2 t) (right_type [] rho T).
Proof.
  intros Delta Gamma t T Hty Hctx theta1 theta2 rho gamma1 gamma2
    Htheta2 Hgamma2 Htypes Hterms.
  rewrite right_type_related with (Delta := Delta) (theta1 := theta1)
    (theta2 := theta2); [|exact Htypes|].
  - eapply has_type_instantiate; eauto.
    + apply related_types_right_wf with (theta1 := theta1) (rho := rho).
      exact Htypes.
    + eapply related_terms_right_typed; eauto.
  - eapply typing_type_wf; eauto.
Qed.
(* fundamental定理 *)
Theorem fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  context_wf Delta Gamma ->
  semantically_typed Delta Gamma t T.
Proof.
  intros Delta Gamma t T Hty.
  induction Hty as
      [Delta Gamma x T Hlookup Hwf
      | L Delta Gamma T1 body T2 Hwf Hbody IHbody
      | Delta Gamma t1 t2 T1 T2 Ht1 IHt1 Ht2 IHt2
      | L Delta Gamma body T Hbody IHbody
      | Delta Gamma t T U Ht IHt HU];
    intros Hctx;
    unfold semantically_typed in *;
    intros theta1 theta2 rho gamma1 gamma2
      Htheta1 Htheta2 Hgamma1 Hgamma2 Htypes Hterms.
  - pose proof (Hterms x T Hlookup) as HR.
    apply expression_relation_of_values. exact HR.
  - assert (Hwhole : has_type Delta Gamma (tm_abs T1 body)
      (Ty_Arrow T1 T2)).
    { eapply T_Abs; eauto. }
    pose proof (instantiated_typing_left _ _ _ _ Hwhole Hctx
      theta1 theta2 rho gamma1 gamma2 Htheta1 Hgamma1 Htypes Hterms) as HTleft.
    pose proof (instantiated_typing_right _ _ _ _ Hwhole Hctx
      theta1 theta2 rho gamma1 gamma2 Htheta2 Hgamma2 Htypes Hterms) as HTright.
    assert (Hvleft : value (instantiate theta1 gamma1 (tm_abs T1 body))).
    { simpl. apply v_abs. eapply typing_lc; eauto. }
    assert (Hvright : value (instantiate theta2 gamma2 (tm_abs T1 body))).
    { simpl. apply v_abs. eapply typing_lc; eauto. }
    apply expression_relation_of_values.
    cbn [value_relation].
    split; [exact Hvleft |]. split; [exact Hvright |].
    split; [exact HTleft |]. split; [exact HTright |].
    exists (instantiate theta1 gamma1 body), (instantiate theta2 gamma2 body).
    assert (HL1 := left_type_related Delta theta1 theta2 rho T1 Htypes Hwf).
    assert (HR1 := right_type_related Delta theta1 theta2 rho T1 Htypes Hwf).
    split.
    + simpl. rewrite HL1. reflexivity.
    + split.
      * simpl. rewrite HR1. reflexivity.
      * intros arg1 arg2 Harg.
        pose proof (value_relation_values _ _ _ _ _ Harg) as [Harg1 Harg2].
        set (x := fresh (L ++ fv_tm body)).
        assert (Hxall : ~ In x (L ++ fv_tm body)).
        { subst x. apply fresh_notin. }
        rewrite in_app_iff in Hxall.
        assert (HxL : ~ In x L) by intuition.
        assert (Hxbody : ~ In x (fv_tm body)) by intuition.
        pose proof (IHbody x HxL
          (context_wf_update Delta Gamma x T1 Hctx Hwf)
          theta1 theta2 rho
          (term_subst_update gamma1 x arg1)
          (term_subst_update gamma2 x arg2)) as IH.
        specialize (IH Htheta1 Htheta2).
        specialize (IH
          (term_subst_update_closed gamma1 x arg1 Hgamma1
            (value_lc _ Harg1))
          (term_subst_update_closed gamma2 x arg2 Hgamma2
            (value_lc _ Harg2))).
        specialize (IH Htypes
          (related_substitutions_update rho Gamma gamma1 gamma2 x T1
            arg1 arg2 Hterms Harg)).
        rewrite (instantiate_open_tm body theta1 gamma1 x arg1
          Hxbody Htheta1 Hgamma1 (value_lc _ Harg1)) in IH.
        rewrite (instantiate_open_tm body theta2 gamma2 x arg2
          Hxbody Htheta2 Hgamma2 (value_lc _ Harg2)) in IH.
        exact IH.
  - cbn [instantiate].
    eapply expression_relation_app.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
  - assert (Hwhole : has_type Delta Gamma (tm_tabs body) (Ty_All T)).
    { eapply T_TAbs; eauto. }
    pose proof (instantiated_typing_left _ _ _ _ Hwhole Hctx
      theta1 theta2 rho gamma1 gamma2 Htheta1 Hgamma1 Htypes Hterms) as HTleft.
    pose proof (instantiated_typing_right _ _ _ _ Hwhole Hctx
      theta1 theta2 rho gamma1 gamma2 Htheta2 Hgamma2 Htypes Hterms) as HTright.
    assert (Hvleft : value (instantiate theta1 gamma1 (tm_tabs body))).
    { simpl. apply v_tabs. eapply typing_lc; eauto. }
    assert (Hvright : value (instantiate theta2 gamma2 (tm_tabs body))).
    { simpl. apply v_tabs. eapply typing_lc; eauto. }
    apply expression_relation_of_values.
    cbn [value_relation].
    split; [exact Hvleft |]. split; [exact Hvright |].
    split; [exact HTleft |]. split; [exact HTright |].
    exists (instantiate theta1 gamma1 body), (instantiate theta2 gamma2 body).
    split; [reflexivity |]. split; [reflexivity |].
    intros a.
    pose proof a.(assignment_is_candidate) as Hcandidate.
    destruct Hcandidate as [Hwf1 [Hwf2 HRa]].
    set (X := fresh
      (L ++ fv_ty T ++ ftv_tm body ++ Delta ++ ftv_context Gamma)).
    assert (HXall :
      ~ In X (L ++ fv_ty T ++ ftv_tm body ++ Delta ++ ftv_context Gamma)).
    { subst X. apply fresh_notin. }
    repeat rewrite in_app_iff in HXall.
    assert (HXL : ~ In X L) by intuition.
    assert (HXT : ~ In X (fv_ty T)) by intuition.
    assert (HXbody : ~ In X (ftv_tm body)) by intuition.
    assert (HXDelta : ~ In X Delta) by intuition.
    assert (HXGamma : ~ In X (ftv_context Gamma)) by intuition.
    assert (Hctx' : context_wf (X :: Delta) Gamma).
    { eapply context_wf_weaken_type; [exact Hctx |].
      unfold ty_context_included. simpl. auto. }
    pose proof (Hbody X HXL) as Hopened.
    pose proof (typing_type_lc _ _ _ _ Hopened) as HopenTlc.
    assert (HTlc : lc_ty_at 1 T).
    { apply (lc_ty_at_open_inv T 0 X). exact HopenTlc. }
    pose proof (IHbody X HXL Hctx'
      (type_subst_update theta1 X a.(assignment_left))
      (type_subst_update theta2 X a.(assignment_right))
      (relation_update rho X a) gamma1 gamma2) as IH.
    specialize (IH
      (type_subst_update_closed theta1 X a.(assignment_left)
        Htheta1 (wf_ty_lc _ _ Hwf1))
      (type_subst_update_closed theta2 X a.(assignment_right)
        Htheta2 (wf_ty_lc _ _ Hwf2)) Hgamma1 Hgamma2).
    specialize (IH
      (related_type_substitutions_update Delta theta1 theta2 rho X a Htypes)
      (related_substitutions_relation_update rho Gamma gamma1 gamma2
        X a Hterms HXGamma)).
    rewrite (instantiate_open_ty body theta1 gamma1 X a.(assignment_left)
      HXbody Htheta1 Hgamma1 (wf_ty_lc _ _ Hwf1)) in IH.
    rewrite (instantiate_open_ty body theta2 gamma2 X a.(assignment_right)
      HXbody Htheta2 Hgamma2 (wf_ty_lc _ _ Hwf2)) in IH.
    assert (HL := left_type_open_relation T 0 [] rho X a
      eq_refl HTlc HXT).
    assert (HR := right_type_open_relation T 0 [] rho X a
      eq_refl HTlc HXT).
    assert (HVR := value_relation_open_relation T 0 [] rho X a
      eq_refl HTlc HXT).
    apply (proj2 (expression_lifting_change _ _ _ _ _ _ _ _
      HL HR HVR)). exact IH.
  - cbn [instantiate].
    pose proof (IHt Hctx theta1 theta2 rho gamma1 gamma2
      Htheta1 Htheta2 Hgamma1 Hgamma2 Htypes Hterms) as Hall.
    assert (HUlc : locally_closed_ty U) by (eapply wf_ty_lc; eauto).
    assert (HLU := left_type_related Delta theta1 theta2 rho U Htypes HU).
    assert (HRU := right_type_related Delta theta1 theta2 rho U Htypes HU).
    assert (Hcandidate : relation_candidate
      (left_type [] rho U) (right_type [] rho U)
      (value_relation [] rho U)).
    { split.
      - rewrite HLU. eapply wf_ty_instantiate; eauto.
        apply related_types_left_wf with (theta2 := theta2) (rho := rho).
        exact Htypes.
      - split.
        + rewrite HRU. eapply wf_ty_instantiate; eauto.
          apply related_types_right_wf with (theta1 := theta1) (rho := rho).
          exact Htypes.
        + intros v1 v2 HRv.
          pose proof (value_relation_values _ _ _ _ _ HRv) as [Hv1 Hv2].
          pose proof (value_relation_typing _ _ _ _ _ HRv) as [Ht1 Ht2].
          repeat split; assumption. }
    set (a := {| assignment_left := left_type [] rho U;
                 assignment_right := right_type [] rho U;
                 assignment_relation := value_relation [] rho U;
                 assignment_is_candidate := Hcandidate |}).
    pose proof (expression_relation_tapp [] rho T
      (instantiate theta1 gamma1 t) (instantiate theta2 gamma2 t) a Hall)
      as Htapp.
    assert (HTlc : lc_ty_at 1 T).
    { pose proof (typing_type_lc _ _ _ _ Ht) as Halllc.
      inversion Halllc; assumption. }
    assert (HLa : a.(assignment_left) = left_type [] rho U) by reflexivity.
    assert (HRa' : a.(assignment_right) = right_type [] rho U) by reflexivity.
    assert (HRel : a.(assignment_relation) = value_relation [] rho U)
      by reflexivity.
    assert (HL := left_type_open_type T 0 [] rho U a
      eq_refl HTlc HUlc HLa).
    assert (HR := right_type_open_type T 0 [] rho U a
      eq_refl HTlc HUlc HRa').
    assert (HVR := value_relation_open_type T 0 [] rho U a
      eq_refl HTlc HUlc HLa HRa' HRel).
    change (expression_relation [a] rho T
      (tm_tapp (instantiate theta1 gamma1 t) (left_type [] rho U))
      (tm_tapp (instantiate theta2 gamma2 t) (right_type [] rho U))) in Htapp.
    rewrite HLU, HRU in Htapp.
    apply (proj1 (expression_lifting_change _ _ _ _ _ _ _ _
      HL HR HVR)). exact Htapp.
Qed.

Definition empty_relation_env : relation_env := fun _ => None.

(*  *)
Lemma semantically_typed_empty : forall t T,
  semantically_typed [] empty t T ->
  expression_relation [] empty_relation_env T t t.
Proof.
  intros.
  unfold semantically_typed in H.
  specialize (H
    identity_type_substitution identity_type_substitution
    empty_relation_env
    identity_term_substitution identity_term_substitution
    identity_type_substitution_closed identity_type_substitution_closed
    identity_term_substitution_closed identity_term_substitution_closed).
  repeat rewrite instantiate_identity in H.
  apply H;clear H.
  - unfold related_type_substitutions.
    intros.
    inversion H.
  - unfold related_substitutions.
    intros.
    inversion H.
    
Qed.

(* fundamental 的直接推论。 *)
(* 这也是参数定理，但是比起下面那个不直观。 *)
Theorem parametricity : forall t T,
  has_type [] empty t T ->
  expression_relation [] empty_relation_env T t t.
Proof.
  intros.
  apply semantically_typed_empty.
  apply fundamental.
  - assumption.
  - 
    (* 显然 *)
    unfold context_wf.
    intros.
    (* H0不成立 *)
    discriminate H0.
Qed.
(*对于同一个多态程序 t: Ty_All T，任取两个实例化类型以及它们之间的合格候选关系 R，
  分别用这两个类型实例化 t，得到的两个程序必然按照类型主体 T 保持关系 R。
  这体现了参数性。*)
Lemma parametricity_tapp : forall t T a,
has_type [] empty t (Ty_All T) ->
expression_relation [a] empty_relation_env T
  (tm_tapp t a.(assignment_left))
  (tm_tapp t a.(assignment_right)).
Proof.
  intros.
  apply expression_relation_tapp.
  apply parametricity.
  assumption.
Qed.
End SystemFParametricity.
