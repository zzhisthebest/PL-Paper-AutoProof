From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
From AutoProof.SystemFIf Require Import Syntax Infrastructure Norm.
From AutoProof.SystemFIf Require Import RelationalEvaluation.
Import ListNotations.

Module SystemFBinaryLogicalRelation.
Import SystemF SystemFInfrastructure SystemFNorm SystemFRelationalEvaluation.

Definition binary_relation := tm -> tm -> Prop.

Record binary_candidate := {
  candidate_relation : binary_relation;
  candidate_values : forall v1 v2, candidate_relation v1 v2 -> value v1 /\ value v2
}.

Definition binary_env := atom -> option binary_candidate.
Definition relation_update (rho : binary_env) (X : atom) (a : binary_candidate) :=
  fun Y => if Nat.eqb X Y then Some a else rho Y.

Definition results_match (R : binary_relation) (t1 t2 : tm) : Prop :=
  exists v1 v2,
    evaluates t1 v1 /\ evaluates t2 v2 /\ R v1 v2.

Definition expression_lifting (R : binary_relation) (t1 t2 : tm) : Prop :=
  locally_closed_tm t1 /\ locally_closed_tm t2 /\ results_match R t1 t2.

Fixpoint value_relation (eta : list binary_candidate) (rho : binary_env)
    (T : ty) (v1 v2 : tm) : Prop :=
  match T with
  | Ty_BVar i =>
      match nth_error eta i with Some a => a.(candidate_relation) v1 v2 | None => False end
  | Ty_FVar X =>
      match rho X with Some a => a.(candidate_relation) v1 v2 | None => False end
  | Ty_Arrow T1 T2 =>
      value v1 /\ value v2 /\
      exists U1 body1 U2 body2,
        v1 = tm_abs U1 body1 /\ v2 = tm_abs U2 body2 /\
        forall arg1 arg2, value_relation eta rho T1 arg1 arg2 ->
          expression_lifting (value_relation eta rho T2)
            (open_tm body1 arg1) (open_tm body2 arg2)
  | Ty_All T =>
      value v1 /\ value v2 /\
      exists body1 body2,
        v1 = tm_tabs body1 /\ v2 = tm_tabs body2 /\
        forall (U1 U2 : ty) (a : binary_candidate),
          locally_closed_ty U1 -> locally_closed_ty U2 ->
          expression_lifting (value_relation (a :: eta) rho T)
            (open_tm_ty body1 U1) (open_tm_ty body2 U2)
  | Ty_Bool => (v1 = tm_true /\ v2 = tm_true) \/ (v1 = tm_false /\ v2 = tm_false)
  end.

Definition expression_relation eta rho T t1 t2 :=
  expression_lifting (value_relation eta rho T) t1 t2.

Lemma value_relation_values : forall eta rho T v1 v2,
  value_relation eta rho T v1 v2 -> value v1 /\ value v2.
Proof.
  intros eta rho T v1 v2 H. destruct T; simpl in H.
  - destruct (nth_error eta n) as [a|]; try contradiction.
    exact (candidate_values a v1 v2 H).
  - destruct (rho a) as [b|]; try contradiction.
    exact (candidate_values b v1 v2 H).
  - tauto.
  - tauto.
  - destruct H as [[-> ->]|[-> ->]]; split; constructor.
Qed.

Definition interpreted_candidate eta rho T : binary_candidate :=
  {| candidate_relation := value_relation eta rho T;
     candidate_values := value_relation_values eta rho T |}.

Lemma expression_lifting_equiv : forall R S,
  (forall v1 v2, R v1 v2 <-> S v1 v2) ->
  forall t1 t2, expression_lifting R t1 t2 <-> expression_lifting S t1 t2.
Proof.
  intros R S H t1 t2. unfold expression_lifting, results_match.
  split; intros [H1 [H2 [v1 [v2 [E1 [E2 HR]]]]]].
  - split; [exact H1|]. split; [exact H2|].
    exists v1, v2. repeat split; try assumption. apply H. exact HR.
  - split; [exact H1|]. split; [exact H2|].
    exists v1, v2. repeat split; try assumption. apply H. exact HR.
Qed.

Lemma value_arrow_equiv : forall eta1 eta2 rho1 rho2 A1 A2 B1 B2,
  (forall v w, value_relation eta1 rho1 A1 v w <-> value_relation eta2 rho2 A2 v w) ->
  (forall v w, value_relation eta1 rho1 B1 v w <-> value_relation eta2 rho2 B2 v w) ->
  forall v w, value_relation eta1 rho1 (Ty_Arrow A1 B1) v w <->
              value_relation eta2 rho2 (Ty_Arrow A2 B2) v w.
Proof.
  intros eta1 eta2 rho1 rho2 A1 A2 B1 B2 HA HB v w.
  cbn [value_relation]. split;
    intros [Hv [Hw [U [b [V [c [Ev [Ew Hmap]]]]]]]];
    split; [exact Hv| |exact Hv|]; split; [exact Hw| |exact Hw|];
    exists U, b, V, c; split; [exact Ev| |exact Ev|];
    split; [exact Ew| |exact Ew|]; intros a1 a2 Harg.
  - apply (proj1 (expression_lifting_equiv _ _ HB _ _)).
    apply Hmap. apply (proj2 (HA a1 a2)). exact Harg.
  - apply (proj2 (expression_lifting_equiv _ _ HB _ _)).
    apply Hmap. apply (proj1 (HA a1 a2)). exact Harg.
Qed.

Lemma value_all_equiv : forall eta1 eta2 rho1 rho2 T1 T2,
  (forall a v w, value_relation (a :: eta1) rho1 T1 v w <->
                 value_relation (a :: eta2) rho2 T2 v w) ->
  forall v w, value_relation eta1 rho1 (Ty_All T1) v w <->
              value_relation eta2 rho2 (Ty_All T2) v w.
Proof.
  intros eta1 eta2 rho1 rho2 T1 T2 H v w.
  cbn [value_relation]. split;
    intros [Hv [Hw [b [c [Ev [Ew Hmap]]]]]];
    split; [exact Hv| |exact Hv|]; split; [exact Hw| |exact Hw|];
    exists b, c; split; [exact Ev| |exact Ev|];
    split; [exact Ew| |exact Ew|]; intros U V a HU HV.
  - apply (proj1 (expression_lifting_equiv _ _ (H a) _ _)). apply Hmap; assumption.
  - apply (proj2 (expression_lifting_equiv _ _ (H a) _ _)). apply Hmap; assumption.
Qed.

Lemma value_relation_env_equiv : forall T k eta1 eta2 rho,
  lc_ty_at k T ->
  (forall i, i < k -> nth_error eta1 i = nth_error eta2 i) ->
  forall v w, value_relation eta1 rho T v w <-> value_relation eta2 rho T v w.
Proof.
  induction T; intros k eta1 eta2 rho Hlc Henv v w.
  - cbn [value_relation]. rewrite Henv; [reflexivity|inversion Hlc; assumption].
  - reflexivity.
  - apply value_arrow_equiv; intros u z; eapply IHT1 || eapply IHT2;
      try (inversion Hlc; eassumption); exact Henv.
  - apply value_all_equiv. intros a u z.
    apply (IHT (S k)); [inversion Hlc; assumption|].
    intros i Hi. destruct i; simpl; [reflexivity|apply Henv; lia].
  - reflexivity.
Qed.

Lemma value_relation_closed_env : forall T eta1 eta2 rho,
  locally_closed_ty T ->
  forall v w, value_relation eta1 rho T v w <-> value_relation eta2 rho T v w.
Proof.
  intros T eta1 eta2 rho Hlc. apply (value_relation_env_equiv T 0); auto.
  intros i Hi. lia.
Qed.

Lemma value_relation_rho_update_irrelevant : forall T eta rho X a,
  ~ In X (fv_ty T) ->
  forall v w, value_relation eta (relation_update rho X a) T v w <->
            value_relation eta rho T v w.
Proof.
  induction T; intros eta rho X b Hfresh v w; simpl in Hfresh.
  - reflexivity.
  - cbn [value_relation]. unfold relation_update.
    destruct (Nat.eqb X a) eqn:E; [apply Nat.eqb_eq in E; subst; tauto|reflexivity].
  - rewrite in_app_iff in Hfresh. apply value_arrow_equiv.
    + apply IHT1. tauto.
    + apply IHT2. tauto.
  - apply value_all_equiv. intros a u z. apply IHT. exact Hfresh.
  - reflexivity.
Qed.

Lemma nth_error_snoc_last : forall (A : Type) (xs : list A) x,
  nth_error (xs ++ [x]) (length xs) = Some x.
Proof.
  intros A xs x. induction xs; simpl; auto.
Qed.

Lemma value_relation_open_relation : forall T k eta rho X a,
  length eta = k -> lc_ty_at (S k) T -> ~ In X (fv_ty T) ->
  forall v w, value_relation (eta ++ [a]) rho T v w <->
    value_relation eta (relation_update rho X a) (open_ty_rec k (Ty_FVar X) T) v w.
Proof.
  induction T; intros k eta rho X b Hlen Hlc Hfresh v w.
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
  - cbn [open_ty_rec]. apply value_all_equiv. intros a u z.
    apply (IHT (S k) (a :: eta)); simpl; try congruence; try assumption.
    inversion Hlc; assumption.
  - reflexivity.
Qed.

Lemma value_relation_open_type : forall T k eta rho U,
  length eta = k -> lc_ty_at (S k) T -> locally_closed_ty U ->
  forall v w,
    value_relation (eta ++ [interpreted_candidate [] rho U]) rho T v w <->
    value_relation eta rho (open_ty_rec k U T) v w.
Proof.
  induction T; intros k eta rho U Hlen Hlc HU v w.
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
  - cbn [open_ty_rec]. apply value_all_equiv. intros a u z.
    apply (IHT (S k) (a :: eta)); simpl; try congruence; try assumption.
    inversion Hlc; assumption.
  - reflexivity.
Qed.

Lemma value_is_expression : forall eta rho T v w,
  value_relation eta rho T v w -> expression_relation eta rho T v w.
Proof.
  intros eta rho T v w HR.
  destruct (value_relation_values _ _ _ _ _ HR) as [Hv Hw].
  split. apply value_regular; assumption.
  split. apply value_regular; assumption.
  exists v, w. repeat split; eauto using EvalValue.
Qed.

Lemma expression_app : forall eta rho A B f1 f2 t1 t2,
  expression_relation eta rho (Ty_Arrow A B) f1 f2 ->
  expression_relation eta rho A t1 t2 ->
  expression_relation eta rho B (tm_app f1 t1) (tm_app f2 t2).
Proof.
  intros eta rho A B f1 f2 t1 t2
    [Hf1 [Hf2 [vf1 [vf2 [Ef1 [Ef2 HRf]]]]]]
    [Ht1 [Ht2 [va1 [va2 [Ea1 [Ea2 HRa]]]]]].
  split. apply lc_tm_app; assumption.
  split. apply lc_tm_app; assumption.
  destruct HRf as [_ [_ [U1 [body1 [U2 [body2 [E1 [E2 Hmap]]]]]]]].
  subst vf1 vf2.
  destruct (Hmap va1 va2 HRa) as [_ [_ [v1 [v2 [Ebody1 [Ebody2 HR]]]]]].
  exists v1, v2. repeat split; eauto using EvalApp.
Qed.

Lemma expression_tapp : forall eta rho T t1 t2 U1 U2 a,
  expression_relation eta rho (Ty_All T) t1 t2 ->
  locally_closed_ty U1 -> locally_closed_ty U2 ->
  expression_relation (a :: eta) rho T (tm_tapp t1 U1) (tm_tapp t2 U2).
Proof.
  intros eta rho T t1 t2 U1 U2 a
    [H1 [H2 [v1 [v2 [E1 [E2 HR]]]]]] HU1 HU2.
  split. apply lc_tm_tapp; assumption.
  split. apply lc_tm_tapp; assumption.
  destruct HR as [_ [_ [body1 [body2 [Ev1 [Ev2 Hmap]]]]]].
  subst v1 v2.
  destruct (Hmap U1 U2 a HU1 HU2) as [_ [_ [w1 [w2 [Ebody1 [Ebody2 HR]]]]]].
  exists w1, w2. repeat split; eauto using EvalTApp.
Qed.

Lemma expression_if : forall eta rho T c1 c2 t1 t2 u1 u2,
  expression_relation eta rho Ty_Bool c1 c2 ->
  expression_relation eta rho T t1 t2 ->
  expression_relation eta rho T u1 u2 ->
  expression_relation eta rho T (tm_if c1 t1 u1) (tm_if c2 t2 u2).
Proof.
  intros eta rho T c1 c2 t1 t2 u1 u2
    [Hc1 [Hc2 [vc1 [vc2 [Ec1 [Ec2 HRc]]]]]]
    [Ht1 [Ht2 [vt1 [vt2 [Et1 [Et2 HRt]]]]]]
    [Hu1 [Hu2 [vu1 [vu2 [Eu1 [Eu2 HRu]]]]]].
  split. apply lc_tm_if; assumption.
  split. apply lc_tm_if; assumption.
  cbn [value_relation] in HRc.
  destruct HRc as [[-> ->]|[-> ->]].
  - exists vt1, vt2. repeat split; eauto using EvalIfTrue.
  - exists vu1, vu2. repeat split; eauto using EvalIfFalse.
Qed.

Definition related_substitutions (rho : binary_env) (Gamma : context)
    (gamma1 gamma2 : term_substitution) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    value_relation [] rho T (gamma1 x) (gamma2 x).

Lemma related_substitutions_update : forall rho Gamma gamma1 gamma2 x T v1 v2,
  related_substitutions rho Gamma gamma1 gamma2 -> value_relation [] rho T v1 v2 ->
  related_substitutions rho (update Gamma x T)
    (term_subst_update gamma1 x v1) (term_subst_update gamma2 x v2).
Proof.
  intros rho Gamma gamma1 gamma2 x T v1 v2 Hrel HV y U Hy.
  unfold update, term_subst_update in *. simpl in Hy.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst y. rewrite Nat.eqb_refl.
    injection Hy as ->. exact HV.
  - assert (E' : Nat.eqb x y = false) by
      (apply Nat.eqb_neq; apply Nat.eqb_neq in E; congruence).
    rewrite E'. apply Hrel. exact Hy.
Qed.

Lemma related_substitutions_relation_update : forall rho Gamma gamma1 gamma2 X a,
  related_substitutions rho Gamma gamma1 gamma2 -> ~ In X (ftv_context Gamma) ->
  related_substitutions (relation_update rho X a) Gamma gamma1 gamma2.
Proof.
  intros rho Gamma gamma1 gamma2 X a Hrel Hfresh x T Hlookup.
  assert (Hnot : ~ In X (fv_ty T)).
  { intros Hin. apply Hfresh. eapply lookup_context_ftv; eauto. }
  apply (proj2 (value_relation_rho_update_irrelevant T [] rho X a Hnot _ _)).
  apply Hrel. exact Hlookup.
Qed.

Theorem binary_fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall theta1 theta2 rho gamma1 gamma2,
    type_substitution_closed theta1 -> type_substitution_closed theta2 ->
    term_substitution_closed gamma1 -> term_substitution_closed gamma2 ->
    related_substitutions rho Gamma gamma1 gamma2 ->
    expression_relation [] rho T
      (instantiate theta1 gamma1 t) (instantiate theta2 gamma2 t).
Proof.
  intros Delta Gamma t T Hty.
  induction Hty as
      [Delta Gamma x T Hlookup Hwf
      | L Delta Gamma T1 body T2 Hwf Hbody IHbody
      | Delta Gamma t1 t2 T1 T2 Ht1 IHt1 Ht2 IHt2
      | L Delta Gamma body T Hbody IHbody
      | Delta Gamma t T U Ht IHt HU
      | Delta Gamma | Delta Gamma
      | Delta Gamma t1 t2 t3 T Ht1 IHt1 Ht2 IHt2 Ht3 IHt3];
    intros theta1 theta2 rho gamma1 gamma2 Htheta1 Htheta2 Hgamma1 Hgamma2 Hterms.
  - apply value_is_expression. apply Hterms. exact Hlookup.
  - assert (Hwhole : has_type Delta Gamma (tm_abs T1 body) (Ty_Arrow T1 T2)).
    { eapply T_Abs; eauto. }
    assert (Hlc1 : locally_closed_tm (instantiate theta1 gamma1 (tm_abs T1 body))).
    { apply instantiate_closed; try assumption. eapply typing_lc; eauto. }
    assert (Hlc2 : locally_closed_tm (instantiate theta2 gamma2 (tm_abs T1 body))).
    { apply instantiate_closed; try assumption. eapply typing_lc; eauto. }
    apply value_is_expression. cbn [value_relation instantiate].
    split. apply v_abs. exact Hlc1.
    split. apply v_abs. exact Hlc2.
    exists (instantiate_ty theta1 T1), (instantiate theta1 gamma1 body),
      (instantiate_ty theta2 T1), (instantiate theta2 gamma2 body).
    split. reflexivity. split. reflexivity. intros arg1 arg2 Harg.
    destruct (value_relation_values _ _ _ _ _ Harg) as [Hv1 Hv2].
    pose proof (value_regular _ Hv1) as Ha1.
    pose proof (value_regular _ Hv2) as Ha2.
    set (x := fresh (L ++ fv_tm body)).
    assert (Hxall : ~ In x (L ++ fv_tm body)) by (subst x; apply fresh_notin).
    rewrite in_app_iff in Hxall.
    assert (HxL : ~ In x L) by tauto.
    assert (Hxb : ~ In x (fv_tm body)) by tauto.
    pose proof (IHbody x HxL theta1 theta2 rho
      (term_subst_update gamma1 x arg1) (term_subst_update gamma2 x arg2)
      Htheta1 Htheta2
      (term_subst_update_closed _ _ _ Hgamma1 Ha1)
      (term_subst_update_closed _ _ _ Hgamma2 Ha2)
      (related_substitutions_update _ _ _ _ _ _ _ _ Hterms Harg)) as IH.
    rewrite (instantiate_open_tm body theta1 gamma1 x arg1 Hxb Htheta1 Hgamma1 Ha1),
      (instantiate_open_tm body theta2 gamma2 x arg2 Hxb Htheta2 Hgamma2 Ha2) in IH.
    exact IH.
  - apply expression_app with (A := T1); [apply IHt1|apply IHt2]; assumption.
  - assert (Hwhole : has_type Delta Gamma (tm_tabs body) (Ty_All T)).
    { eapply T_TAbs; eauto. }
    assert (Hlc1 : locally_closed_tm (instantiate theta1 gamma1 (tm_tabs body))).
    { apply instantiate_closed; try assumption. eapply typing_lc; eauto. }
    assert (Hlc2 : locally_closed_tm (instantiate theta2 gamma2 (tm_tabs body))).
    { apply instantiate_closed; try assumption. eapply typing_lc; eauto. }
    apply value_is_expression. cbn [value_relation instantiate].
    split. apply v_tabs. exact Hlc1.
    split. apply v_tabs. exact Hlc2.
    exists (instantiate theta1 gamma1 body), (instantiate theta2 gamma2 body).
    split. reflexivity. split. reflexivity. intros U1 U2 a HU1 HU2.
    set (X := fresh (L ++ fv_ty T ++ ftv_tm body ++ ftv_context Gamma)).
    assert (HXall : ~ In X (L ++ fv_ty T ++ ftv_tm body ++ ftv_context Gamma))
      by (subst X; apply fresh_notin).
    repeat rewrite in_app_iff in HXall.
    assert (HXL : ~ In X L) by tauto.
    assert (HXT : ~ In X (fv_ty T)) by tauto.
    assert (HXb : ~ In X (ftv_tm body)) by tauto.
    assert (HXG : ~ In X (ftv_context Gamma)) by tauto.
    pose proof (IHbody X HXL
      (type_subst_update theta1 X U1) (type_subst_update theta2 X U2)
      (relation_update rho X a) gamma1 gamma2
      (type_subst_update_closed _ _ _ Htheta1 HU1)
      (type_subst_update_closed _ _ _ Htheta2 HU2) Hgamma1 Hgamma2
      (related_substitutions_relation_update _ _ _ _ _ _ Hterms HXG)) as IH.
    rewrite (instantiate_open_ty body theta1 gamma1 X U1 HXb Htheta1 Hgamma1 HU1),
      (instantiate_open_ty body theta2 gamma2 X U2 HXb Htheta2 Hgamma2 HU2) in IH.
    assert (HTlc : lc_ty_at 1 T).
    { pose proof (typing_type_lc _ _ _ _ Hwhole) as HH. inversion HH; assumption. }
    apply (proj2 (expression_lifting_equiv _ _
      (value_relation_open_relation T 0 [] rho X a eq_refl HTlc HXT) _ _)). exact IH.
  - cbn [instantiate].
    pose proof (IHt theta1 theta2 rho gamma1 gamma2
      Htheta1 Htheta2 Hgamma1 Hgamma2 Hterms) as HE.
    assert (HUlc : locally_closed_ty U) by (eapply wf_ty_lc; eauto).
    assert (HU1 : locally_closed_ty (instantiate_ty theta1 U)).
    { apply instantiate_ty_closed; assumption. }
    assert (HU2 : locally_closed_ty (instantiate_ty theta2 U)).
    { apply instantiate_ty_closed; assumption. }
    pose proof (expression_tapp [] rho T _ _ _ _
      (interpreted_candidate [] rho U) HE HU1 HU2) as Hout.
    assert (HTlc : lc_ty_at 1 T).
    { pose proof (typing_type_lc _ _ _ _ Ht) as HH. inversion HH; assumption. }
    apply (proj1 (expression_lifting_equiv _ _
      (value_relation_open_type T 0 [] rho U eq_refl HTlc HUlc) _ _)). exact Hout.
  - apply value_is_expression. left. split; reflexivity.
  - apply value_is_expression. right. split; reflexivity.
  - apply expression_if; [apply IHt1|apply IHt2|apply IHt3]; assumption.
Qed.

End SystemFBinaryLogicalRelation.
