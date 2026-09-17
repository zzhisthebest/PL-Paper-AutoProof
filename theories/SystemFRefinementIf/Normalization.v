From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
From AutoProof.SystemFRefinementIf Require Import Syntax Infrastructure CoreTyping LogicalRelation.
Import ListNotations.
Module SystemFRefinementIfNormalization.
Import SystemFRefinementIf SystemFRefinementIfInfrastructure SystemFRefinementIfCoreTyping SystemFRefinementIfLogicalRelation.

Lemma value_regular : forall v, value v -> locally_closed_tm v.
Proof. intros v H. destruct H; try assumption; constructor. Qed.

Lemma value_no_step : forall v, value v -> forall t, ~ (v --> t).
Proof. intros v Hv t Hs. destruct Hv; inversion Hs. Qed.

Lemma step_preserves_lc : forall t u,
  t --> u -> locally_closed_tm t -> locally_closed_tm u.
Proof.
  intros t u Hstep. induction Hstep; intros Hlc; unfold locally_closed_tm in *;
    inversion Hlc; subst; eauto 10 using lc_tm_at, value_regular.
  - eapply open_tm_preserves_lc_at.
    + inversion H; eassumption.
    + apply value_regular. exact H0.
  - eapply open_tm_ty_preserves_lc_at.
    + inversion H; eassumption.
    + exact H0.
Qed.

Lemma sn_step : forall t t',
  strongly_normalizing t ->
  t --> t' ->
  strongly_normalizing t'.
Proof.
  intros t t' Hsn Hstep.
  inversion Hsn as [t0 Hnext].
  apply Hnext. exact Hstep.
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

Section Compatibility.
Variable eta : list value_candidate.
Variable rho : relation_env.
Local Notation strong_value_relation := (value_relation eta rho).
Local Notation strong_expression_relation := (expression_relation eta rho).

Lemma strong_value_relation_value : forall T v,
  strong_value_relation T v -> value v.
Proof. intros T v H. eapply value_relation_value. exact H. Qed.
Lemma strong_value_relation_lc : forall T v,
  strong_value_relation T v -> locally_closed_tm v.
Proof. intros T v H. apply value_regular. eapply strong_value_relation_value. exact H. Qed.
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
  locally_closed_tm t ->
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

Lemma strong_expression_intro : forall T t,
  locally_closed_tm t ->
  (value t -> strong_value_relation T t) ->
  (forall u, t --> u -> strong_expression_relation T u) ->
  strong_expression_relation T t.
Proof.
  intros T t Hlc HV Hnext. split. exact Hlc.
  split.
  - apply SN_intro. intros u Hstep.
    destruct (Hnext u Hstep) as [_ [Hsn _]]. exact Hsn.
  - intros v Hsteps Hv. inversion Hsteps; subst.
    + apply HV. exact Hv.
    + destruct (Hnext y H) as [_ [_ Hall]]. eapply Hall; eauto.
Qed.

Lemma strong_expression_app : forall T1 T2 t1 t2,
  strong_expression_relation (Ty_Arrow T1 T2) t1 ->
  strong_expression_relation T1 t2 ->
  strong_expression_relation T2 (tm_app t1 t2).
Proof.
  intros T1 T2 t1 t2 [Hlc1 [Hsn1 Hall1]] HE2.
  revert T1 T2 Hlc1 Hall1 t2 HE2.
  induction Hsn1 as [t1 Hnext1 IH1]. intros T1 T2 Hlc1 Hall1 t2 [Hlc2 [Hsn2 Hall2]].
  revert Hlc2 Hall2. induction Hsn2 as [t2 Hnext2 IH2]. intros Hlc2 Hall2.
  apply strong_expression_of_reducts.
  - apply lc_tm_app; assumption.
  - intros Hv. inversion Hv; subst.
  - intros u Hstep. inversion Hstep; subst.
    + pose proof (Hall1 (tm_abs T t) (multi_refl _) (v_abs T t H1)) as HVfun.
      pose proof (Hall2 t2 (multi_refl _) H3) as HVarg.
      destruct HVfun as [_ [U [body [Heq Hmap]]]].
      injection Heq as E1 E2. subst U body. apply Hmap. exact HVarg.
    + apply (IH1 t1' H1 T1 T2).
      * eapply step_preserves_lc; eauto.
      * intros v Hm Hv. apply (Hall1 v); auto. eapply multi_step; eauto.
      * split. exact Hlc2. split. apply SN_intro. exact Hnext2. exact Hall2.
    + apply (IH2 t2' H3).
      * eapply step_preserves_lc; eauto.
      * intros v Hm Hv. apply (Hall2 v); auto. eapply multi_step; eauto.
Qed.

Lemma strong_expression_if : forall T t1 t2 t3,
  strong_expression_relation Ty_Bool t1 ->
  strong_expression_relation T t2 ->
  strong_expression_relation T t3 ->
  strong_expression_relation T (tm_if t1 t2 t3).
Proof.
  intros T t1 t2 t3 [Hlc [Hsn Hall]] H2 H3.
  revert Hlc Hall. induction Hsn as [t1 Hnext IH]. intros Hlc Hall.
  apply strong_expression_of_reducts.
  - apply lc_tm_if.
    + exact Hlc.
    + exact (proj1 H2).
    + exact (proj1 H3).
  - intro Hv. inversion Hv; subst.
  - intros u Hstep. inversion Hstep; subst.
    + exact H2.
    + exact H3.
    + apply (IH t1' H4).
      * eapply step_preserves_lc; eauto.
      * intros v Hsteps Hv. apply Hall with (v := v); auto.
        eapply multi_step; eauto.
Qed.

End Compatibility.

Lemma strong_expression_tapp : forall eta rho T t U a,
  expression_relation eta rho (Ty_All T) t -> locally_closed_ty U ->
  expression_relation (a :: eta) rho T (tm_tapp t U).
Proof.
  intros eta rho T t U a [Hlc [Hsn Hall]] HU.
  revert Hlc Hall. induction Hsn as [t Hnext IH]. intros Hlc Hall.
  apply (strong_expression_of_reducts (a :: eta) rho T).
  - apply lc_tm_tapp; assumption.
  - intros Hv. inversion Hv; subst.
  - intros u Hstep. inversion Hstep; subst.
    + match goal with H : locally_closed_tm (tm_tabs ?b) |- _ =>
        pose proof (Hall _ (multi_refl _) (v_tabs b H)) as HV end.
      destruct HV as [_ [body [Heq Hmap]]]. injection Heq as ->.
      apply Hmap. exact HU.
    + eapply IH.
      * eassumption.
      * eapply step_preserves_lc; eauto.
      * intros v Hm Hv. apply (Hall v); auto. eapply multi_step; eauto.
Qed.

Definition related_substitution (rho : relation_env) (Gamma : context)
    (gamma : term_substitution) : Prop :=
  forall x T, lookup_context x Gamma = Some T -> value_relation [] rho T (gamma x).

Lemma related_substitution_update : forall rho Gamma gamma x T v,
  related_substitution rho Gamma gamma -> value_relation [] rho T v ->
  related_substitution rho (update Gamma x T) (term_subst_update gamma x v).
Proof.
  intros rho Gamma gamma x T v Hrel HV y U Hy.
  unfold update, term_subst_update in *. simpl in Hy.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst y. rewrite Nat.eqb_refl.
    injection Hy as ->. exact HV.
  - assert (E' : Nat.eqb x y = false) by (apply Nat.eqb_neq; apply Nat.eqb_neq in E; congruence).
    rewrite E'. apply Hrel. exact Hy.
Qed.

Lemma lookup_context_ftv : forall Gamma x T X,
  lookup_context x Gamma = Some T -> In X (fv_ty T) -> In X (ftv_context Gamma).
Proof.
  induction Gamma as [|[y U] Gamma IH]; intros x T X Hlookup Hin; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y).
    + injection Hlookup as ->. apply in_or_app. left. exact Hin.
    + apply in_or_app. right. eapply IH; eauto.
Qed.

Lemma related_substitution_relation_update : forall rho Gamma gamma X a,
  related_substitution rho Gamma gamma -> ~ In X (ftv_context Gamma) ->
  related_substitution (relation_update rho X a) Gamma gamma.
Proof.
  intros rho Gamma gamma X a Hrel Hfresh x T Hlookup.
  assert (Hnot : ~ In X (fv_ty T)).
  { intros Hin. apply Hfresh. eapply lookup_context_ftv; eauto. }
  apply (proj2 (value_relation_rho_update_irrelevant T [] rho X a Hnot (gamma x))).
  apply Hrel. exact Hlookup.
Qed.

Theorem fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall theta rho gamma,
    type_substitution_closed theta -> term_substitution_closed gamma ->
    related_substitution rho Gamma gamma ->
    expression_relation [] rho T (instantiate theta gamma t).
Proof.
  intros Delta Gamma t T Hty.
  induction Hty as
      [Delta Gamma x T Hlookup Hwf
      | L Delta Gamma T1 body T2 Hwf Hbody IHbody
      | Delta Gamma t1 t2 T1 T2 Ht1 IHt1 Ht2 IHt2
      | L Delta Gamma body T Hbody IHbody
      | Delta Gamma t T U Ht IHt HU
      | Delta Gamma | Delta Gamma
      | Delta Gamma t1 t2 t3 T Ht1 IHt1 Ht2 IHt2 Ht3 IHt3
];
    intros theta rho gamma Htheta Hgamma Hterms.
  - apply strong_value_is_expression. apply Hterms. exact Hlookup.
  - assert (Hwhole : has_type Delta Gamma (tm_abs T1 body) (Ty_Arrow T1 T2)).
    { eapply T_Abs; eauto. }
    assert (Hvlc : locally_closed_tm (instantiate theta gamma (tm_abs T1 body))).
    { apply instantiate_closed; try assumption. eapply typing_lc; eauto. }
    apply strong_value_is_expression. cbn [value_relation instantiate].
    split. apply v_abs. exact Hvlc.
    exists (instantiate_ty theta T1), (instantiate theta gamma body).
    split. reflexivity. intros arg Harg.
    assert (Harglc : locally_closed_tm arg).
    { apply value_regular. eapply value_relation_value. exact Harg. }
    set (x := fresh (L ++ fv_tm body)).
    assert (Hxall : ~ In x (L ++ fv_tm body)) by (subst x; apply fresh_notin).
    rewrite in_app_iff in Hxall.
    assert (HxL : ~ In x L) by tauto.
    assert (Hxbody : ~ In x (fv_tm body)) by tauto.
    pose proof (IHbody x HxL theta rho (term_subst_update gamma x arg)
      Htheta (term_subst_update_closed gamma x arg Hgamma Harglc)
      (related_substitution_update rho Gamma gamma x T1 arg Hterms Harg)) as IH.
    rewrite (instantiate_open_tm body theta gamma x arg Hxbody Htheta Hgamma Harglc) in IH.
    exact IH.
  - apply strong_expression_app with (T1 := T1); [apply IHt1|apply IHt2]; assumption.
  - assert (Hwhole : has_type Delta Gamma (tm_tabs body) (Ty_All T)).
    { eapply T_TAbs; eauto. }
    assert (Hvlc : locally_closed_tm (instantiate theta gamma (tm_tabs body))).
    { apply instantiate_closed; try assumption. eapply typing_lc; eauto. }
    apply strong_value_is_expression. cbn [value_relation instantiate].
    split. apply v_tabs. exact Hvlc.
    exists (instantiate theta gamma body). split. reflexivity.
    intros U a HU.
    set (X := fresh (L ++ fv_ty T ++ ftv_tm body ++ ftv_context Gamma)).
    assert (HXall : ~ In X (L ++ fv_ty T ++ ftv_tm body ++ ftv_context Gamma))
      by (subst X; apply fresh_notin).
    repeat rewrite in_app_iff in HXall.
    assert (HXL : ~ In X L) by tauto.
    assert (HXT : ~ In X (fv_ty T)) by tauto.
    assert (HXbody : ~ In X (ftv_tm body)) by tauto.
    assert (HXGamma : ~ In X (ftv_context Gamma)) by tauto.
    pose proof (IHbody X HXL (type_subst_update theta X U)
      (relation_update rho X a) gamma
      (type_subst_update_closed theta X U Htheta HU) Hgamma
      (related_substitution_relation_update rho Gamma gamma X a Hterms HXGamma)) as IH.
    rewrite (instantiate_open_ty body theta gamma X U HXbody Htheta Hgamma HU) in IH.
    assert (HTlc : lc_ty_at 1 T).
    { pose proof (typing_type_lc _ _ _ _ Hwhole) as HH. inversion HH; assumption. }
    apply (proj2 (expression_lifting_equiv _ _
      (value_relation_open_relation T 0 [] rho X a eq_refl HTlc HXT) _)).
    exact IH.
  - cbn [instantiate].
    pose proof (IHt theta rho gamma Htheta Hgamma Hterms) as HE.
    assert (HUlc : locally_closed_ty U) by (eapply wf_ty_lc; eauto).
    assert (HUinst : locally_closed_ty (instantiate_ty theta U)).
    { apply instantiate_ty_closed; assumption. }
    pose proof (strong_expression_tapp [] rho T _ (instantiate_ty theta U)
      (interpreted_candidate [] rho U) HE HUinst) as Hout.
    assert (HTlc : lc_ty_at 1 T).
    { pose proof (typing_type_lc _ _ _ _ Ht) as HH. inversion HH; assumption. }
    apply (proj1 (expression_lifting_equiv _ _
      (value_relation_open_type T 0 [] rho U eq_refl HTlc HUlc) _)). exact Hout.
  - apply strong_value_is_expression. split. apply v_true. left. reflexivity.
  - apply strong_value_is_expression. split. apply v_false. right. reflexivity.
  - apply strong_expression_if; [apply IHt1|apply IHt2|apply IHt3]; assumption.
Qed.

(** Operational type-safety lemmas used only to turn strong normalization into
    termination at a value. *)
Lemma canonical_arrow : forall v T1 T2,
  value v ->
  has_type [] empty v (Ty_Arrow T1 T2) ->
  exists U body, v = tm_abs U body.
Proof.
  intros v T1 T2 Hv Hty.
  inversion Hv; subst.
  - exists T, t. reflexivity.
  - inversion Hty.
  - inversion Hty.
  - inversion Hty.
Qed.

Lemma canonical_all : forall v T,
  value v ->
  has_type [] empty v (Ty_All T) ->
  exists body, v = tm_tabs body.
Proof.
  intros v T Hv Hty.
  inversion Hv; subst.
  - inversion Hty.
  - exists t. reflexivity.
  - inversion Hty.
  - inversion Hty.
Qed.

Lemma canonical_bool : forall v,
  value v ->
  has_type [] empty v Ty_Bool ->
  v = tm_true \/ v = tm_false.
Proof.
  intros v Hv Hty. inversion Hv; subst.
  - inversion Hty.
  - inversion Hty.
  - left. reflexivity.
  - right. reflexivity.
Qed.

Lemma term_beta_typing : forall L T1 body T2 v,
  wf_ty [] T1 ->
  (forall x, ~ In x L ->
    has_type [] (update empty x T1)
      (open_tm body (tm_fvar x)) T2) ->
  has_type [] empty v T1 ->
  has_type [] empty (open_tm body v) T2.
Proof.
  intros L T1 body T2 v HT1 Hbody Hv.
  set (x := fresh (L ++ fv_tm body)).
  assert (Hx : ~ In x (L ++ fv_tm body)).
  { subst x. apply fresh_notin. }
  rewrite in_app_iff in Hx.
  assert (HxL : ~ In x L) by intuition.
  assert (Hxfv : ~ In x (fv_tm body)) by intuition.
  pose proof (Hbody x HxL) as Hopened.
  set (gamma := term_subst_update identity_term_substitution x v).
  assert (Hctx : context_wf [] (update empty x T1)).
  { intros y U Hlookup. unfold update, empty in Hlookup. simpl in Hlookup.
    destruct (Nat.eqb y x) eqn:E; try discriminate.
    inversion Hlookup; subst. exact HT1. }
  assert (Htheta_wf :
    type_substitution_wf [] [] identity_type_substitution).
  { intros X Hin. contradiction. }
  assert (Hgamma_typed : term_substitution_typed
      (update empty x T1) [] empty identity_type_substitution gamma).
  { intros y U Hlookup. unfold update, empty in Hlookup. simpl in Hlookup.
    destruct (Nat.eqb y x) eqn:E; try discriminate.
    apply Nat.eqb_eq in E. subst y. inversion Hlookup; subst U.
    unfold gamma, term_subst_update. rewrite Nat.eqb_refl.
    rewrite instantiate_ty_identity. exact Hv. }
  pose proof (has_type_instantiate _ _ _ _ Hopened Hctx
    [] empty identity_type_substitution gamma
    identity_type_substitution_closed
    (term_subst_update_closed identity_term_substitution x v
      identity_term_substitution_closed (typing_lc _ _ _ _ Hv))
    Htheta_wf Hgamma_typed) as Hinst.
  unfold gamma in Hinst.
  rewrite (instantiate_open_tm body identity_type_substitution
      identity_term_substitution x v Hxfv
      identity_type_substitution_closed identity_term_substitution_closed
      (typing_lc _ _ _ _ Hv)) in Hinst.
  rewrite instantiate_identity, instantiate_ty_identity in Hinst.
  exact Hinst.
Qed.

Lemma type_beta_typing : forall L body T U,
  (forall X, ~ In X L ->
    has_type [X] empty
      (open_tm_ty body (Ty_FVar X))
      (open_ty T (Ty_FVar X))) ->
  wf_ty [] U ->
  has_type [] empty (open_tm_ty body U) (open_ty T U).
Proof.
  intros L body T U Hbody HU.
  set (X := fresh (L ++ ftv_tm body ++ fv_ty T)).
  assert (HX : ~ In X (L ++ ftv_tm body ++ fv_ty T)).
  { subst X. apply fresh_notin. }
  repeat rewrite in_app_iff in HX.
  assert (HXL : ~ In X L) by intuition.
  assert (HXbody : ~ In X (ftv_tm body)) by intuition.
  assert (HXT : ~ In X (fv_ty T)) by intuition.
  pose proof (Hbody X HXL) as Hopened.
  set (theta := type_subst_update identity_type_substitution X U).
  assert (Htheta_closed : type_substitution_closed theta).
  { unfold theta. apply type_subst_update_closed.
    - exact identity_type_substitution_closed.
    - exact (wf_ty_lc [] U HU). }
  assert (Htheta_wf : type_substitution_wf [X] [] theta).
  { intros Y Hin. simpl in Hin. destruct Hin as [E | Hin]; [|contradiction].
    subst Y. unfold theta, type_subst_update. rewrite Nat.eqb_refl. exact HU. }
  assert (Hctx : context_wf [X] empty).
  { intros y V Hlookup. discriminate. }
  assert (Hgamma_typed : term_substitution_typed
      empty [] empty theta identity_term_substitution).
  { intros y V Hlookup. discriminate. }
  pose proof (has_type_instantiate _ _ _ _ Hopened Hctx
    [] empty theta identity_term_substitution
    Htheta_closed identity_term_substitution_closed
    Htheta_wf Hgamma_typed) as Hinst.
  unfold theta in Hinst.
  rewrite (instantiate_open_ty body identity_type_substitution
      identity_term_substitution X U HXbody
      identity_type_substitution_closed identity_term_substitution_closed
      (wf_ty_lc [] U HU)) in Hinst.
  rewrite (instantiate_ty_open_local T identity_type_substitution X U HXT) in Hinst.
  - rewrite instantiate_identity, instantiate_ty_identity in Hinst. exact Hinst.
  - intros Y Hin. apply lc_ty_fvar.
  - exact (wf_ty_lc [] U HU).
Qed.

Theorem core_progress : forall t T,
  has_type [] empty t T ->
  value t \/ exists t', t --> t'.
Proof.
  intros t T Hty.
  remember (@nil atom) as Delta eqn:EDelta.
  remember empty as Gamma eqn:EGamma.
  induction Hty; subst.
  - discriminate H.
  - left. apply v_abs. eapply typing_lc. eapply T_Abs; eauto.
  - right.
    destruct IHHty1 as [Hv1 | [t1' Hs1]]; try reflexivity.
    + destruct IHHty2 as [Hv2 | [t2' Hs2]]; try reflexivity.
      * destruct (canonical_arrow _ _ _ Hv1 Hty1) as [U [body E]].
        subst t1. exists (open_tm body t2). apply ST_AppAbs.
        -- eapply typing_lc. exact Hty1.
        -- exact Hv2.
      * exists (tm_app t1 t2'). apply ST_App2; assumption.
    + exists (tm_app t1' t2). apply ST_App1.
      * exact Hs1.
      * eapply typing_lc. exact Hty2.
  - left. apply v_tabs. eapply typing_lc. eapply T_TAbs; eauto.
  - right.
    destruct IHHty as [Hv | [t' Hs]]; try reflexivity.
    + destruct (canonical_all _ _ Hv Hty) as [body E]. subst t.
      exists (open_tm_ty body U). apply ST_TAppTabs.
      * eapply typing_lc. exact Hty.
      * eapply wf_ty_lc. eassumption.
    + exists (tm_tapp t' U). apply ST_TApp.
      * exact Hs.
      * eapply wf_ty_lc. eassumption.
  - left. apply v_true.
  - left. apply v_false.
  - right. destruct IHHty1 as [Hv | [t1' Hstep]]; try reflexivity.
    + destruct (canonical_bool _ Hv Hty1) as [-> | ->].
      * exists t2. apply ST_IfTrue; eapply typing_lc; eauto.
      * exists t3. apply ST_IfFalse; eapply typing_lc; eauto.
    + exists (tm_if t1' t2 t3). apply ST_If.
      * exact Hstep.
      * eapply typing_lc. exact Hty2.
      * eapply typing_lc. exact Hty3.
Qed.

Theorem core_preservation : forall t t' T,
  has_type [] empty t T ->
  t --> t' ->
  has_type [] empty t' T.
Proof.
  intros t t' T Hty Hstep.
  remember (@nil atom) as Delta eqn:EDelta.
  remember empty as Gamma eqn:EGamma.
  generalize dependent t'.
  induction Hty; intros t' Hstep; subst; inversion Hstep; subst.
  - inversion Hty1; subst. eapply term_beta_typing; eauto.
  - eapply T_App; eauto.
  - eapply T_App; eauto.
  - inversion Hty; subst. eapply type_beta_typing; eauto.
  - eapply T_TApp; eauto.
  - exact Hty2.
  - exact Hty3.
  - eapply T_If; eauto.
Qed.

Definition empty_relation_env : relation_env := fun _ => None.

Theorem strong_normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  intros t T HT.
  assert (Hempty : related_substitution empty_relation_env empty identity_term_substitution).
  { intros x U Hlookup. discriminate Hlookup. }
  pose proof (fundamental [] empty t T HT identity_type_substitution empty_relation_env
    identity_term_substitution identity_type_substitution_closed
    identity_term_substitution_closed Hempty) as Hrel.
  rewrite instantiate_identity in Hrel.
  exact (proj1 (proj2 Hrel)).
Qed.

Definition halts (t : tm) : Prop :=
  exists v, t -->* v /\ value v.

Lemma typed_strong_normalization_implies_halts : forall t,
  strongly_normalizing t ->
  forall T, has_type [] empty t T -> halts t.
Proof.
  intros t Hsn. induction Hsn as [t Hnext IH]. intros T Htyped.
  destruct (core_progress t T Htyped) as [Hv | [t' Hstep]].
  - exists t. split; [apply multi_refl | exact Hv].
  - pose proof (core_preservation t t' T Htyped Hstep) as Htyped'.
    destruct (IH t' Hstep T Htyped') as [v [Hsteps Hv]].
    exists v. split; [eapply multi_step; eauto | exact Hv].
Qed.

Theorem weak_normalization : forall t T,
  has_type [] empty t T -> halts t.
Proof.
  intros t T Htyped.
  eapply typed_strong_normalization_implies_halts.
  - apply strong_normalization with (T := T). exact Htyped.
  - exact Htyped.
Qed.

End SystemFRefinementIfNormalization.
