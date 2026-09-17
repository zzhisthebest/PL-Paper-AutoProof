From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
From AutoProof.SystemFRefinementIf Require Import Syntax Infrastructure.
Import ListNotations.
Module SystemFRefinementIfLogicalRelation.
Import SystemFRefinementIf SystemFRefinementIfInfrastructure.

Definition relation := tm -> Prop.
Record value_candidate := {
  candidate_relation : relation;
  candidate_values : forall v, candidate_relation v -> value v
}.
Definition relation_env := atom -> option value_candidate.
Definition relation_update (rho : relation_env) (X : atom) (a : value_candidate) :=
  fun Y => if Nat.eqb X Y then Some a else rho Y.

Definition expression_lifting (R : relation) (t : tm) : Prop :=
  locally_closed_tm t /\ strongly_normalizing t /\
  forall v, t -->* v -> value v -> R v.

Fixpoint value_relation (eta : list value_candidate) (rho : relation_env)
    (T : ty) (v : tm) : Prop :=
  match T with
  | Ty_BVar i =>
      match nth_error eta i with Some a => a.(candidate_relation) v | None => False end
  | Ty_FVar X =>
      match rho X with Some a => a.(candidate_relation) v | None => False end
  | Ty_Arrow T1 T2 =>
      value v /\ exists U body, v = tm_abs U body /\
      forall arg, value_relation eta rho T1 arg ->
        expression_lifting (value_relation eta rho T2) (open_tm body arg)
  | Ty_All T =>
      value v /\ exists body, v = tm_tabs body /\
      forall (U : ty) (a : value_candidate), locally_closed_ty U ->
        expression_lifting (value_relation (a :: eta) rho T) (open_tm_ty body U)
  | Ty_Bool => value v /\ (v = tm_true \/ v = tm_false)
  end.

Definition expression_relation eta rho T t :=
  expression_lifting (value_relation eta rho T) t.

Lemma value_relation_value : forall eta rho T v,
  value_relation eta rho T v -> value v.
Proof.
  intros eta rho T v H. destruct T; simpl in H; try exact (proj1 H).
  - destruct (nth_error eta n) as [a|]; try contradiction. exact (candidate_values a v H).
  - destruct (rho a) as [b|]; try contradiction. exact (candidate_values b v H).
Qed.

Definition interpreted_candidate eta rho T : value_candidate :=
  {| candidate_relation := value_relation eta rho T;
     candidate_values := value_relation_value eta rho T |}.

Lemma expression_lifting_equiv : forall R S,
  (forall v, R v <-> S v) ->
  forall t, expression_lifting R t <-> expression_lifting S t.
Proof.
  unfold expression_lifting. firstorder.
Qed.

Lemma value_arrow_equiv : forall eta1 eta2 rho1 rho2 A1 A2 B1 B2,
  (forall v, value_relation eta1 rho1 A1 v <-> value_relation eta2 rho2 A2 v) ->
  (forall v, value_relation eta1 rho1 B1 v <-> value_relation eta2 rho2 B2 v) ->
  forall v, value_relation eta1 rho1 (Ty_Arrow A1 B1) v <->
            value_relation eta2 rho2 (Ty_Arrow A2 B2) v.
Proof.
  intros eta1 eta2 rho1 rho2 A1 A2 B1 B2 HA HB v. cbn [value_relation].
  split; intros [Hv [U [body [Heq Hmap]]]]; split; [exact Hv| |exact Hv|];
    exists U, body; split; [exact Heq| |exact Heq|]; intros arg Harg.
  - apply (proj1 (expression_lifting_equiv _ _ HB _)).
    apply Hmap. apply (proj2 (HA arg)). exact Harg.
  - apply (proj2 (expression_lifting_equiv _ _ HB _)).
    apply Hmap. apply (proj1 (HA arg)). exact Harg.
Qed.

Lemma value_all_equiv : forall eta1 eta2 rho1 rho2 T1 T2,
  (forall a v, value_relation (a :: eta1) rho1 T1 v <->
               value_relation (a :: eta2) rho2 T2 v) ->
  forall v, value_relation eta1 rho1 (Ty_All T1) v <->
            value_relation eta2 rho2 (Ty_All T2) v.
Proof.
  intros eta1 eta2 rho1 rho2 T1 T2 H v. cbn [value_relation].
  split; intros [Hv [body [Heq Hmap]]]; split; [exact Hv| |exact Hv|];
    exists body; split; [exact Heq| |exact Heq|]; intros U a HU.
  - apply (proj1 (expression_lifting_equiv _ _ (H a) _)). apply Hmap. exact HU.
  - apply (proj2 (expression_lifting_equiv _ _ (H a) _)). apply Hmap. exact HU.
Qed.

Lemma value_relation_env_equiv : forall T k eta1 eta2 rho,
  lc_ty_at k T ->
  (forall i, i < k -> nth_error eta1 i = nth_error eta2 i) ->
  forall v, value_relation eta1 rho T v <-> value_relation eta2 rho T v.
Proof.
  induction T; intros k eta1 eta2 rho Hlc Henv v.
  - cbn [value_relation]. rewrite Henv; [reflexivity|inversion Hlc; assumption].
  - reflexivity.
  - apply value_arrow_equiv; intros u; eapply IHT1 || eapply IHT2;
      try (inversion Hlc; eassumption); exact Henv.
  - apply value_all_equiv. intros a u.
    apply (IHT (S k)); [inversion Hlc; assumption|].
    intros i Hi. destruct i; simpl; [reflexivity|apply Henv; lia].
  - reflexivity.
Qed.

Lemma value_relation_closed_env : forall T eta1 eta2 rho,
  locally_closed_ty T ->
  forall v, value_relation eta1 rho T v <-> value_relation eta2 rho T v.
Proof.
  intros T eta1 eta2 rho Hlc. apply (value_relation_env_equiv T 0); auto.
  intros i Hi. lia.
Qed.

Lemma value_relation_rho_update_irrelevant : forall T eta rho X a,
  ~ In X (fv_ty T) ->
  forall v, value_relation eta (relation_update rho X a) T v <->
            value_relation eta rho T v.
Proof.
  induction T; intros eta rho X b Hfresh v; simpl in Hfresh.
  - reflexivity.
  - cbn [value_relation]. unfold relation_update.
    destruct (Nat.eqb X a) eqn:E; [apply Nat.eqb_eq in E; subst; tauto|reflexivity].
  - rewrite in_app_iff in Hfresh. apply value_arrow_equiv.
    + apply IHT1. tauto.
    + apply IHT2. tauto.
  - apply value_all_equiv. intros a u. apply IHT. exact Hfresh.
  - reflexivity.
Qed.

Lemma nth_error_snoc_last : forall (A : Type) (xs : list A) x,
  nth_error (xs ++ [x]) (length xs) = Some x.
Proof.
  intros A xs x. induction xs; simpl; auto.
Qed.

Lemma value_relation_open_relation : forall T k eta rho X a,
  length eta = k -> lc_ty_at (S k) T -> ~ In X (fv_ty T) ->
  forall v, value_relation (eta ++ [a]) rho T v <->
    value_relation eta (relation_update rho X a) (open_ty_rec k (Ty_FVar X) T) v.
Proof.
  induction T; intros k eta rho X b Hlen Hlc Hfresh v.
  - assert (Hlt : n < S k) by (inversion Hlc; assumption).
    cbn [open_ty_rec]. destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n.
      cbn [value_relation]. rewrite <- Hlen, nth_error_snoc_last.
      unfold relation_update. rewrite Nat.eqb_refl. reflexivity.
    + cbn [value_relation]. rewrite nth_error_app1.
      * reflexivity.
      * apply Nat.eqb_neq in E. lia.
  - cbn [open_ty_rec value_relation]. unfold relation_update.
    destruct (Nat.eqb X a) eqn:E; [apply Nat.eqb_eq in E; subst; simpl in Hfresh; tauto|reflexivity].
  - cbn [open_ty_rec]. apply value_arrow_equiv.
    + apply IHT1 with (k := k); try assumption.
      * inversion Hlc; assumption.
      * simpl in Hfresh. rewrite in_app_iff in Hfresh. tauto.
    + apply IHT2 with (k := k); try assumption.
      * inversion Hlc; assumption.
      * simpl in Hfresh. rewrite in_app_iff in Hfresh. tauto.
  - cbn [open_ty_rec]. apply value_all_equiv. intros a u.
    apply (IHT (S k) (a :: eta)); simpl; try congruence; try assumption.
    inversion Hlc; assumption.
  - reflexivity.
Qed.

Lemma value_relation_open_type : forall T k eta rho U,
  length eta = k -> lc_ty_at (S k) T -> locally_closed_ty U ->
  forall v,
    value_relation (eta ++ [interpreted_candidate [] rho U]) rho T v <->
    value_relation eta rho (open_ty_rec k U T) v.
Proof.
  induction T; intros k eta rho U Hlen Hlc HU v.
  - assert (Hlt : n < S k) by (inversion Hlc; assumption).
    cbn [open_ty_rec]. destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n.
      cbn [value_relation]. rewrite <- Hlen, nth_error_snoc_last.
      cbn [interpreted_candidate candidate_relation].
      apply value_relation_closed_env. exact HU.
    + cbn [value_relation]. rewrite nth_error_app1.
      * reflexivity.
      * apply Nat.eqb_neq in E. lia.
  - reflexivity.
  - cbn [open_ty_rec]. apply value_arrow_equiv.
    + apply IHT1 with (k := k); try assumption. inversion Hlc; assumption.
    + apply IHT2 with (k := k); try assumption. inversion Hlc; assumption.
  - cbn [open_ty_rec]. apply value_all_equiv. intros a u.
    apply (IHT (S k) (a :: eta)); simpl; try congruence; try assumption.
    inversion Hlc; assumption.
  - reflexivity.
Qed.

End SystemFRefinementIfLogicalRelation.
