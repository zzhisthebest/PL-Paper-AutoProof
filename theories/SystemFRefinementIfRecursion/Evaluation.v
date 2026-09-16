From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
From AutoProof.SystemFRefinementIfRecursion Require Import
  Syntax Infrastructure CoreTyping.
Module SystemFRefinementIfRecursionEvaluation.
Import ListNotations SystemFRefinementIfRecursion SystemFRefinementIfRecursionInfrastructure
  SystemFRefinementIfRecursionCoreTyping.

Inductive multi : tm -> tm -> Prop :=
  | multi_refl : forall t, multi t t
  | multi_step : forall t1 t2 t3,
      t1 --> t2 -> multi t2 t3 -> multi t1 t3.
Notation "t '-->*' u" := (multi t u) (at level 40).

Definition halts (t : tm) : Prop :=
  exists v, multi t v /\ value v.

Lemma open_tm_preserves_lc_at : forall t K k u,
  lc_tm_at K (S k) t -> locally_closed_tm u ->
  lc_tm_at K k (open_tm_rec k u t).
Proof.
  induction t; intros K k u Hlc Hu; simpl; inversion Hlc; subst;
    eauto 8 using lc_tm_at.
  destruct (Nat.eqb k n) eqn:E.
  - eapply lc_tm_at_monotone; [exact Hu|lia|lia].
  - apply Nat.eqb_neq in E. apply lc_tm_bvar. lia.
Qed.

Lemma open_tm_ty_preserves_lc_at : forall t K k U,
  lc_tm_at (S K) k t -> locally_closed_ty U ->
  lc_tm_at K k (open_tm_ty_rec K U t).
Proof.
  induction t; intros K k U Hlc HU; simpl; inversion Hlc; subst;
    eauto 8 using lc_tm_at.
  - apply lc_tm_abs.
    + apply lc_ty_at_open; [assumption|].
      eapply lc_ty_at_monotone; [exact HU|lia].
    + eapply IHt; eauto.
  - apply lc_tm_tapp.
    + eapply IHt; eauto.
    + apply lc_ty_at_open; [assumption|].
      eapply lc_ty_at_monotone; [exact HU|lia].
  - apply lc_tm_fix.
    + apply lc_ty_at_open; [assumption |]. eapply lc_ty_at_monotone; [exact HU | lia].
    + apply lc_ty_at_open; [assumption |]. eapply lc_ty_at_monotone; [exact HU | lia].
    + eapply IHt1; eauto.
    + eapply IHt2; eauto.
Qed.

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
  - unfold open_fix_body, open_tm.
    eapply open_tm_preserves_lc_at.
    + eapply open_tm_preserves_lc_at.
      * inversion H; eassumption.
      * exact H.
    + apply value_regular. exact H0.
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


Lemma fix_beta_typing : forall A B metric body arg,
  has_type [] empty (tm_fix A B metric body) (Ty_Arrow A B) ->
  has_type [] empty arg A ->
  has_type [] empty (open_fix_body body (tm_fix A B metric body) arg) B.
Proof.
  intros A B metric body arg Hfix Harg.
  inversion Hfix as [ | | | | | | | | L D G A' B' m b HA HB Hmetric Hbody | | | | ]; subst.
  set (f := fresh (L ++ fv_tm body)).
  set (x := fresh (f :: L ++ fv_tm body)).
  assert (Hf : ~ In f (L ++ fv_tm body)) by (apply fresh_notin).
  assert (Hx : ~ In x (f :: L ++ fv_tm body)) by (apply fresh_notin).
  simpl in Hx. repeat rewrite in_app_iff in Hf, Hx.
  assert (HfL : ~ In f L) by tauto.
  assert (HxL : ~ In x (f :: L)) by (simpl; tauto).
  pose proof (Hbody f x HfL HxL) as Ho.
  set (gamma := term_subst_update
    (term_subst_update identity_term_substitution x arg) f (tm_fix A B metric body)).
  assert (Hctx : context_wf [] (update (update empty x A) f (Ty_Arrow A B))).
  { apply context_wf_update.
    - apply context_wf_update; [intros y T E; discriminate | assumption].
    - apply WF_Arrow; assumption. }
  assert (Hgamma : term_substitution_closed gamma).
  { unfold gamma. apply term_subst_update_closed.
    - apply term_subst_update_closed; [apply identity_term_substitution_closed |].
      eapply typing_lc; eauto.
    - eapply typing_lc; eauto. }
  assert (Hgt : term_substitution_typed
    (update (update empty x A) f (Ty_Arrow A B))
    [] empty identity_type_substitution gamma).
  { intros y T Hy. simpl in Hy. unfold gamma, term_subst_update.
    destruct (Nat.eqb y f) eqn:Ef.
    - apply Nat.eqb_eq in Ef. subst y. rewrite Nat.eqb_refl.
      inversion Hy; subst T. rewrite instantiate_ty_identity. assumption.
    - apply Nat.eqb_neq in Ef. rewrite (proj2 (Nat.eqb_neq f y)) by congruence.
      destruct (Nat.eqb y x) eqn:Ex; [| discriminate].
      apply Nat.eqb_eq in Ex. subst y. rewrite Nat.eqb_refl.
      inversion Hy; subst T. rewrite instantiate_ty_identity. assumption. }
  assert (Htw : type_substitution_wf [] [] identity_type_substitution).
  { intros X HX. contradiction. }
  pose proof (has_type_instantiate _ _ _ _ Ho Hctx [] empty
    identity_type_substitution gamma identity_type_substitution_closed
    Hgamma Htw Hgt) as Hinst.
  unfold gamma in Hinst.
  rewrite instantiate_open_fix_body in Hinst;
    try tauto; try apply identity_type_substitution_closed;
    try apply identity_term_substitution_closed;
    try solve [eapply typing_lc; eauto].
  rewrite instantiate_identity, instantiate_ty_identity in Hinst. exact Hinst.
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
  - inversion Hty1; subst. eapply fix_beta_typing; eauto.
  - inversion Hty; subst. eapply type_beta_typing; eauto.
  - eapply T_TApp; eauto.
  - apply T_Div; eauto.
  - apply T_Div; eauto.
  - apply T_Int.
  - apply T_Arith; eauto.
  - apply T_Arith; eauto.
  - apply T_Int.
  - apply T_IfZero; eauto.
  - assumption.
  - assumption.
  - eapply T_If; eauto.
  - assumption.
  - assumption.
Qed.

Lemma multi_preservation : forall t t' T,
  has_type [] empty t T ->
  multi t t' ->
  has_type [] empty t' T.
Proof.
  intros t t' T Hty Hmulti. induction Hmulti.
  - exact Hty.
  - apply IHHmulti. eapply core_preservation; eauto.
Qed.

Lemma step_deterministic : forall t u,
  t --> u -> forall v, t --> v -> u = v.
Proof.
  intros t u H. induction H; intros z Hz; inversion Hz; subst;
    try reflexivity;
    try solve [match goal with Hs : step (tm_abs _ _) _ |- _ => inversion Hs end];
    try solve [match goal with Hs : step (tm_tabs _) _ |- _ => inversion Hs end];
    try solve [match goal with Hs : step (tm_int _) _ |- _ => inversion Hs end];
    try solve [match goal with Hs : step (tm_fix _ _ _ _) _ |- _ => inversion Hs end];
    try solve [match goal with Hs : step tm_true _ |- _ => inversion Hs end];
    try solve [match goal with Hs : step tm_false _ |- _ => inversion Hs end];
    try congruence;
    try solve [exfalso; eapply value_no_step; eauto using value];
    try solve [exfalso; match goal with Hv : value ?v, Hs : step ?v _ |- _ => exact (value_no_step v Hv _ Hs) end];
    f_equal; eauto.
Qed.

Lemma multi_trans : forall t u v,
  multi t u -> multi u v -> multi t v.
Proof. intros t u v H. induction H; eauto using multi. Qed.

Lemma halts_value : forall v, value v -> halts v.
Proof. intros v Hv. exists v. split; [constructor|assumption]. Qed.

Lemma halts_step : forall t u, t --> u -> halts t -> halts u.
Proof.
  intros t u Hstep [v [Hsteps Hv]].
  inversion Hsteps; subst.
  - exfalso. eapply value_no_step; eauto.
  - assert (u = t2) by (eapply step_deterministic; eauto).
    subst. exists v. auto.
Qed.

Lemma halts_multi : forall t u, multi t u -> halts t -> halts u.
Proof.
  intros t u H. induction H; intros HH; auto.
  apply IHmulti. eapply halts_step; eauto.
Qed.
Lemma multi_value_unique : forall t v,
  multi t v -> value v ->
  forall w, multi t w -> value w -> v = w.
Proof.
  intros t v H. induction H; intros Hv w Hw Hvw.
  - symmetry. eapply value_multi_eq; eauto.
  - inversion Hw; subst.
    + exfalso. eapply value_no_step; eauto.
    + match goal with Hs : t1 --> ?u |- _ =>
        assert (t2 = u) by (eapply step_deterministic; eauto); subst u
      end.
      eapply IHmulti; eauto.
Qed.

End SystemFRefinementIfRecursionEvaluation.
