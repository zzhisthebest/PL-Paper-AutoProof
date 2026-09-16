From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
From AutoProof.SystemFRefinementIfRecursion Require Import Syntax.
From AutoProof.SystemFRefinementIfRecursion Require Import Infrastructure.

Module SystemFRefinementIfRecursionCoreTyping.
Import ListNotations.
Import SystemFRefinementIfRecursion.
Import SystemFRefinementIfRecursionInfrastructure.

Definition ty_context_included (Delta Delta' : ty_context) : Prop :=
  forall X, In X Delta -> In X Delta'.

Definition context_included (Gamma Gamma' : context) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    lookup_context x Gamma' = Some T.

Lemma wf_ty_weaken : forall Delta T,
  wf_ty Delta T ->
  forall Delta', ty_context_included Delta Delta' -> wf_ty Delta' T.
Proof.
  intros Delta T Hwf. induction Hwf; intros Delta' Hinc.
  - apply WF_Var. apply Hinc. assumption.
  - apply WF_Arrow; auto.
  - apply WF_All with L. intros X Hfresh.
    apply H0. exact Hfresh.
    unfold ty_context_included in *. simpl. intros Y [E | Hin].
    + left. exact E.
    + right. apply Hinc. exact Hin.
  - apply WF_Int.
  - apply WF_Bool.
Qed.

Lemma has_type_weaken_context : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall Gamma', context_included Gamma Gamma' ->
  has_type Delta Gamma' t T.
Proof.
  intros Delta Gamma t T Hty. induction Hty; intros Gamma' Hinc.
  - apply T_Var; [apply Hinc; assumption | assumption].
  - apply T_Abs with L; [assumption |]. intros x Hfresh.
    apply H1. exact Hfresh.
    unfold context_included in *. intros y U Hlookup.
    unfold update in *. simpl in *.
    destruct (Nat.eqb y x); [exact Hlookup |].
    apply Hinc. exact Hlookup.
  - apply T_App with T1; auto.
  - apply T_TAbs with L. intros X Hfresh. apply H0; assumption.
  - eapply T_TApp; eauto.
  - apply T_Int.
  - apply T_Div; auto.
  - apply T_Arith; auto.
  - apply T_Fix with L; try assumption.
    + intros x Hx. apply H2; [assumption |].
      intros y U Hy. simpl in *. destruct (Nat.eqb y x); auto.
    + intros f x Hf Hx. apply H4; try assumption.
      intros y U Hy. simpl in *. destruct (Nat.eqb y f); [assumption |].
      destruct (Nat.eqb y x); auto.
  - apply T_IfZero; auto.
  - apply T_True.
  - apply T_False.
  - eapply T_If; eauto.
Qed.

Lemma has_type_weaken_type : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall Delta', ty_context_included Delta Delta' ->
  has_type Delta' Gamma t T.
Proof.
  intros Delta Gamma t T Hty. induction Hty; intros Delta' Hinc.
  - apply T_Var; [assumption | eapply wf_ty_weaken; eauto].
  - apply T_Abs with L.
    + eapply wf_ty_weaken; eauto.
    + intros x Hfresh. apply H1; assumption.
  - apply T_App with T1; auto.
  - apply T_TAbs with L. intros X Hfresh.
    apply H0. exact Hfresh.
    unfold ty_context_included in *. simpl. intros Y [E | Hin].
    + left. exact E.
    + right. apply Hinc. exact Hin.
  - eapply T_TApp; eauto. eapply wf_ty_weaken; eauto.
  - apply T_Int.
  - apply T_Div; auto.
  - apply T_Arith; auto.
  - apply T_Fix with L.
    + eapply wf_ty_weaken; eauto.
    + eapply wf_ty_weaken; eauto.
    + intros x Hx. apply H2; assumption.
    + intros f x Hf Hx. apply H4; assumption.
  - apply T_IfZero; auto.
  - apply T_True.
  - apply T_False.
  - eapply T_If; eauto.
Qed.

Definition type_substitution_wf
    (Delta Delta' : ty_context) (theta : type_substitution) : Prop :=
  forall X, In X Delta -> wf_ty Delta' (theta X).

Lemma fv_ty_open_rec_preserves : forall T k U X,
  In X (fv_ty T) -> In X (fv_ty (open_ty_rec k U T)).
Proof.
  induction T; intros k U X Hin; simpl in *.
  - contradiction.
  - exact Hin.
  - apply in_app_iff in Hin. apply in_app_iff.
    destruct Hin as [Hin | Hin].
    + left. apply IHT1. exact Hin.
    + right. apply IHT2. exact Hin.
  - apply IHT. exact Hin.
  - contradiction.
  - contradiction.
Qed.

Lemma wf_ty_fv : forall Delta T,
  wf_ty Delta T -> forall X, In X (fv_ty T) -> In X Delta.
Proof.
  intros Delta T Hwf. induction Hwf; intros Y Hin; simpl in *.
  - destruct Hin as [E | Hin].
    + subst. assumption.
    + contradiction.
  - apply in_app_iff in Hin. destruct Hin; auto.
  - set (X := fresh (L ++ fv_ty T)).
    assert (HX : ~ In X (L ++ fv_ty T)).
    { subst X. apply fresh_notin. }
    rewrite in_app_iff in HX.
    assert (HXL : ~ In X L) by intuition.
    assert (HXfv : ~ In X (fv_ty T)) by intuition.
    pose proof (H0 X HXL Y) as IH.
    assert (Hopen : In Y (fv_ty (open_ty T (Ty_FVar X)))).
    { unfold open_ty. apply fv_ty_open_rec_preserves. exact Hin. }
    specialize (IH Hopen). simpl in IH.
    destruct IH as [E | HinDelta].
    + subst Y. contradiction.
    + exact HinDelta.
  - contradiction.
  - contradiction.
Qed.

Lemma instantiate_ty_open_rec_local : forall T k theta X U,
  ~ In X (fv_ty T) ->
  (forall Y, In Y (fv_ty T) -> locally_closed_ty (theta Y)) ->
  locally_closed_ty U ->
  instantiate_ty (type_subst_update theta X U)
    (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k U (instantiate_ty theta T).
Proof.
  induction T; intros k theta X U Hfresh Htheta HU; simpl in *.
  - destruct (Nat.eqb k n); simpl.
    + unfold type_subst_update. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - assert (X <> a) by (intro; subst; apply Hfresh; auto).
    unfold type_subst_update.
    rewrite (proj2 (Nat.eqb_neq X a)) by assumption.
    symmetry. apply open_ty_rec_lc_at.
    eapply lc_ty_at_monotone.
    + apply Htheta. auto.
    + lia.
  - rewrite in_app_iff in Hfresh.
    assert (Hfresh1 : ~ In X (fv_ty T1)) by intuition.
    assert (Hfresh2 : ~ In X (fv_ty T2)) by intuition.
    rewrite (IHT1 k theta X U Hfresh1),
      (IHT2 k theta X U Hfresh2); try assumption.
    + reflexivity.
    + intros Y Hin. apply Htheta. apply in_app_iff. auto.
    + intros Y Hin. apply Htheta. apply in_app_iff. auto.
  - rewrite IHT; try assumption. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma instantiate_ty_open_local : forall T theta X U,
  ~ In X (fv_ty T) ->
  (forall Y, In Y (fv_ty T) -> locally_closed_ty (theta Y)) ->
  locally_closed_ty U ->
  instantiate_ty (type_subst_update theta X U)
    (open_ty T (Ty_FVar X)) =
  open_ty (instantiate_ty theta T) U.
Proof.
  intros. unfold open_ty. apply instantiate_ty_open_rec_local; assumption.
Qed.

Lemma wf_ty_instantiate : forall Delta T,
  wf_ty Delta T ->
  forall Delta' theta,
    type_substitution_wf Delta Delta' theta ->
    wf_ty Delta' (instantiate_ty theta T).
Proof.
  intros Delta T Hwf. induction Hwf; intros Delta' theta Htheta; simpl.
  - apply Htheta. assumption.
  - apply WF_Arrow; auto.
  - apply WF_All with (L ++ Delta ++ Delta' ++ fv_ty T).
    intros X Hfresh.
    repeat rewrite in_app_iff in Hfresh.
    assert (HXL : ~ In X L) by intuition.
    assert (HXDelta : ~ In X Delta) by intuition.
    assert (HXDelta' : ~ In X Delta') by intuition.
    assert (HXT : ~ In X (fv_ty T)) by intuition.
    pose proof (H0 X HXL (X :: Delta')
      (type_subst_update theta X (Ty_FVar X))) as IH.
    assert (Hsub : type_substitution_wf (X :: Delta) (X :: Delta')
      (type_subst_update theta X (Ty_FVar X))).
    { unfold type_substitution_wf in *. intros Y [E | Hin].
      - subst Y. unfold type_subst_update. rewrite Nat.eqb_refl.
        apply WF_Var. simpl. auto.
      - assert (Hneq : X <> Y).
        { intro E. subst. contradiction. }
        unfold type_subst_update.
        rewrite (proj2 (Nat.eqb_neq X Y)) by assumption.
        eapply wf_ty_weaken.
        + apply Htheta. exact Hin.
        + unfold ty_context_included. simpl. auto. }
    assert (Hopen :
      instantiate_ty (type_subst_update theta X (Ty_FVar X))
        (open_ty T (Ty_FVar X)) =
      open_ty (instantiate_ty theta T) (Ty_FVar X)).
    { apply instantiate_ty_open_local.
      - exact HXT.
      - intros Y Hin. apply wf_ty_lc with Delta'. apply Htheta.
        assert (Hwhole : wf_ty Delta (Ty_All T)).
        { apply WF_All with L. exact H. }
        eapply wf_ty_fv; [exact Hwhole |]. simpl. exact Hin.
      - apply lc_ty_fvar. }
    rewrite <- Hopen. exact (IH Hsub).
  - apply WF_Int.
  - apply WF_Bool.
Qed.

(* Gamma中每个自由程序变量对应的类型T,T里的所有自由类型变量都出现在Delta里。 *)
Definition context_wf (Delta : ty_context) (Gamma : context) : Prop :=
  forall x T, lookup_context x Gamma = Some T -> wf_ty Delta T.

Definition term_substitution_typed
    (Gamma : context) (Delta' : ty_context) (Gamma' : context)
    (theta : type_substitution) (gamma : term_substitution) : Prop :=
  forall x T,
    lookup_context x Gamma = Some T ->
    has_type Delta' Gamma' (gamma x) (instantiate_ty theta T).

Lemma notin_dom_lookup_none : forall x Gamma,
  ~ In x (dom_context Gamma) -> lookup_context x Gamma = None.
Proof.
  intros x Gamma. induction Gamma as [|[y T] Gamma IH]; intros Hfresh; simpl in *.
  - reflexivity.
  - assert (Hxy : x <> y) by intuition.
    rewrite (proj2 (Nat.eqb_neq x y)) by assumption.
    apply IH. intuition.
Qed.

Lemma context_included_update_fresh : forall Gamma x T,
  ~ In x (dom_context Gamma) ->
  context_included Gamma (update Gamma x T).
Proof.
  intros Gamma x T Hfresh y U Hlookup. unfold update. simpl.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst y.
    rewrite notin_dom_lookup_none in Hlookup by assumption. discriminate.
  - exact Hlookup.
Qed.

Lemma context_wf_update : forall Delta Gamma x T,
  context_wf Delta Gamma -> wf_ty Delta T ->
  context_wf Delta (update Gamma x T).
Proof.
  intros Delta Gamma x T Hctx HT y U Hlookup.
  unfold update in Hlookup. simpl in Hlookup.
  destruct (Nat.eqb y x) eqn:E.
  - inversion Hlookup; subst. exact HT.
  - apply Hctx with y. exact Hlookup.
Qed.

Lemma context_wf_weaken_type : forall Delta Gamma,
  context_wf Delta Gamma ->
  forall Delta', ty_context_included Delta Delta' ->
  context_wf Delta' Gamma.
Proof.
  intros Delta Gamma Hctx Delta' Hinc x T Hlookup.
  eapply wf_ty_weaken; [eapply Hctx; eauto | exact Hinc].
Qed.

Lemma instantiate_ty_update_irrelevant : forall T theta X U,
  ~ In X (fv_ty T) ->
  instantiate_ty (type_subst_update theta X U) T = instantiate_ty theta T.
Proof.
  induction T; intros theta X U Hfresh; simpl in *.
  - reflexivity.
  - unfold type_subst_update.
    assert (Hneq : X <> a) by (intro; subst; apply Hfresh; auto).
    rewrite (proj2 (Nat.eqb_neq X a)) by assumption. reflexivity.
  - rewrite in_app_iff in Hfresh.
    rewrite IHT1, IHT2; tauto.
  - f_equal. apply IHT. assumption.
  - reflexivity.
  - reflexivity.
Qed.

Lemma instantiate_ty_open_rec_commute : forall T k U theta,
  type_substitution_closed theta ->
  instantiate_ty theta (open_ty_rec k U T) =
  open_ty_rec k (instantiate_ty theta U) (instantiate_ty theta T).
Proof.
  induction T; intros k U theta Htheta; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. apply open_ty_rec_lc_at.
    eapply lc_ty_at_monotone; [apply Htheta | lia].
  - rewrite IHT1, IHT2; try assumption. reflexivity.
  - rewrite IHT; try assumption. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma instantiate_ty_open_commute : forall T U theta,
  type_substitution_closed theta ->
  instantiate_ty theta (open_ty T U) =
  open_ty (instantiate_ty theta T) (instantiate_ty theta U).
Proof.
  intros. unfold open_ty. apply instantiate_ty_open_rec_commute. assumption.
Qed.

Lemma term_substitution_typed_update : forall Gamma Delta' Gamma' theta gamma x T,
  term_substitution_typed Gamma Delta' Gamma' theta gamma ->
  ~ In x (dom_context Gamma') ->
  wf_ty Delta' (instantiate_ty theta T) ->
  term_substitution_typed (update Gamma x T) Delta'
    (update Gamma' x (instantiate_ty theta T)) theta
    (term_subst_update gamma x (tm_fvar x)).
Proof.
  intros Gamma Delta' Gamma' theta gamma x T Hgamma Hfresh Hwf y U Hlookup.
  simpl in Hlookup. unfold term_subst_update.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst y. rewrite Nat.eqb_refl.
    inversion Hlookup; subst U. apply T_Var; [apply lookup_context_update_eq | assumption].
  - apply Nat.eqb_neq in E. rewrite (proj2 (Nat.eqb_neq x y)) by congruence.
    eapply has_type_weaken_context; [eapply Hgamma; eauto |].
    apply context_included_update_fresh. assumption.
Qed.

Lemma has_type_instantiate : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  context_wf Delta Gamma ->
  forall Delta' Gamma' theta gamma,
    type_substitution_closed theta ->
    term_substitution_closed gamma ->
    type_substitution_wf Delta Delta' theta ->
    term_substitution_typed Gamma Delta' Gamma' theta gamma ->
    has_type Delta' Gamma'
      (instantiate theta gamma t) (instantiate_ty theta T).
Proof.
  intros Delta Gamma t T Hty. induction Hty as
      [Delta Gamma x T Hlookup Hwf
      | L Delta Gamma T1 body T2 Hwf Hbody IHbody
      | Delta Gamma t1 t2 T1 T2 Ht1 IHt1 Ht2 IHt2
      | L Delta Gamma body T Hbody IHbody
      | Delta Gamma t T U Ht IHt HU
      | Delta Gamma n
      | Delta Gamma t1 t2 Ht1 IHt1 Ht2 IHt2
      | Delta Gamma op t1 t2 Ht1 IHt1 Ht2 IHt2
      | L Delta Gamma A B metric body HA HB Hmetric IHmetric Hbody IHbody
      | Delta Gamma t t0 t1 T Ht IHt Ht0 IHt0 Ht1 IHt1
      | Delta Gamma | Delta Gamma
      | Delta Gamma t1 t2 t3 T Ht1 IHt1 Ht2 IHt2 Ht3 IHt3];
    intros Hctx Delta' Gamma' theta gamma Htheta Hgamma Htheta_wf Hgamma_ty;
    simpl.
  - eapply Hgamma_ty. exact Hlookup.
  - apply T_Abs with (L ++ fv_tm body ++ dom_context Gamma').
    + eapply wf_ty_instantiate; eauto.
    + intros x Hfresh. repeat rewrite in_app_iff in Hfresh.
      assert (HxL : ~ In x L) by intuition.
      assert (Hxbody : ~ In x (fv_tm body)) by intuition.
      assert (HxGamma' : ~ In x (dom_context Gamma')) by intuition.
      pose proof (IHbody x HxL
        (context_wf_update Delta Gamma x T1 Hctx Hwf)
        Delta' (update Gamma' x (instantiate_ty theta T1)) theta
        (term_subst_update gamma x (tm_fvar x))) as IH.
      rewrite <- (instantiate_open_tm body theta gamma x (tm_fvar x));
        try assumption; try apply lc_tm_fvar.
      apply IH; try assumption.
      * apply term_subst_update_closed; [assumption | apply lc_tm_fvar].
      * unfold term_substitution_typed. intros y U Hlookup'.
        unfold update in Hlookup'. simpl in Hlookup'.
        unfold term_subst_update.
        destruct (Nat.eqb y x) eqn:E.
        -- apply Nat.eqb_eq in E. subst y. rewrite Nat.eqb_refl.
           inversion Hlookup'; subst U.
           apply T_Var.
           ++ unfold update. simpl. rewrite Nat.eqb_refl. reflexivity.
           ++ eapply wf_ty_instantiate; eauto.
        -- apply Nat.eqb_neq in E.
           rewrite (proj2 (Nat.eqb_neq x y)) by congruence.
           eapply has_type_weaken_context.
           ++ eapply Hgamma_ty. exact Hlookup'.
           ++ apply context_included_update_fresh. exact HxGamma'.
  - eapply T_App.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
  - apply T_TAbs with
      (L ++ Delta ++ Delta' ++ ftv_tm body ++ fv_ty T).
    intros X Hfresh. repeat rewrite in_app_iff in Hfresh.
    assert (HXL : ~ In X L) by intuition.
    assert (HXDelta : ~ In X Delta) by intuition.
    assert (HXDelta' : ~ In X Delta') by intuition.
    assert (HXbody : ~ In X (ftv_tm body)) by intuition.
    assert (HXT : ~ In X (fv_ty T)) by intuition.
    set (theta' := type_subst_update theta X (Ty_FVar X)).
    assert (Hctx' : context_wf (X :: Delta) Gamma).
    { eapply context_wf_weaken_type; [exact Hctx |].
      unfold ty_context_included. simpl. auto. }
    assert (Htheta_wf' : type_substitution_wf
      (X :: Delta) (X :: Delta') theta').
    { unfold theta', type_substitution_wf, type_subst_update.
      intros Y [E | Hin].
      - subst Y. rewrite Nat.eqb_refl. apply WF_Var. simpl. auto.
      - assert (Hneq : X <> Y) by (intro; subst; contradiction).
        rewrite (proj2 (Nat.eqb_neq X Y)) by assumption.
        eapply wf_ty_weaken.
        + apply Htheta_wf. exact Hin.
        + unfold ty_context_included. simpl. auto. }
    assert (Hgamma_ty' : term_substitution_typed
      Gamma (X :: Delta') Gamma' theta' gamma).
    { unfold term_substitution_typed in *. intros x U Hlookup.
      assert (HwfU : wf_ty Delta U) by (eapply Hctx; eauto).
      assert (HXU : ~ In X (fv_ty U)).
      { intro Hin. apply HXDelta. eapply wf_ty_fv; eauto. }
      unfold theta'.
      rewrite instantiate_ty_update_irrelevant by exact HXU.
      eapply has_type_weaken_type.
      - eapply Hgamma_ty. exact Hlookup.
      - unfold ty_context_included. simpl. auto. }
    pose proof (IHbody X HXL Hctx' (X :: Delta') Gamma'
      theta' gamma) as IH.
    rewrite <- (instantiate_open_ty body theta gamma X (Ty_FVar X));
      try assumption; try apply lc_ty_fvar.
    rewrite <- (instantiate_ty_open T theta X (Ty_FVar X));
      try assumption; try apply lc_ty_fvar.
    assert (Htheta' : type_substitution_closed theta').
    { unfold theta'. apply type_subst_update_closed; auto. apply lc_ty_fvar. }
    exact (IH Htheta' Hgamma Htheta_wf' Hgamma_ty').
  - rewrite instantiate_ty_open_commute by exact Htheta.
    eapply T_TApp.
    + apply IHt; assumption.
    + eapply wf_ty_instantiate; eauto.
  - apply T_Int.
  - apply T_Div; [apply IHt1 | apply IHt2]; assumption.
  - apply T_Arith; [apply IHt1 | apply IHt2]; assumption.
  - apply T_Fix with (L ++ fv_tm metric ++ fv_tm body ++ dom_context Gamma').
    + eapply wf_ty_instantiate; eauto.
    + eapply wf_ty_instantiate; eauto.
    + intros x Hx. repeat rewrite in_app_iff in Hx.
      rewrite <- (instantiate_open_tm metric theta gamma x (tm_fvar x));
        try assumption; try apply lc_tm_fvar; try tauto.
      apply IHmetric.
      * tauto.
      * apply context_wf_update; assumption.
      * assumption.
      * apply term_subst_update_closed; [assumption | constructor].
      * assumption.
      * apply term_substitution_typed_update; try assumption; try tauto.
        eapply wf_ty_instantiate; eauto.
    + intros f x Hf Hx. simpl in Hx.
      repeat rewrite in_app_iff in Hf, Hx.
      rewrite <- (instantiate_open_fix_body body theta gamma f x (tm_fvar f) (tm_fvar x));
        try assumption; try constructor; try tauto.
      apply IHbody.
      * tauto.
      * simpl. tauto.
      * apply context_wf_update.
        -- apply context_wf_update; assumption.
        -- apply WF_Arrow; assumption.
      * assumption.
      * apply term_subst_update_closed; [| constructor].
        apply term_subst_update_closed; [assumption | constructor].
      * assumption.
      * change (term_substitution_typed (update (update Gamma x A) f (Ty_Arrow A B))
          Delta' (update (update Gamma' x (instantiate_ty theta A))
            f (instantiate_ty theta (Ty_Arrow A B))) theta
          (term_subst_update (term_subst_update gamma x (tm_fvar x)) f (tm_fvar f))).
        apply term_substitution_typed_update.
        -- apply term_substitution_typed_update; try assumption; try tauto.
           eapply wf_ty_instantiate; eauto.
        -- simpl. intuition congruence.
        -- simpl. apply WF_Arrow; eapply wf_ty_instantiate; eauto.
  - apply T_IfZero; [apply IHt | apply IHt0 | apply IHt1]; assumption.
  - apply T_True.
  - apply T_False.
  - eapply T_If; [apply IHt1 | apply IHt2 | apply IHt3]; assumption.
Qed.

Lemma wf_ty_open_all : forall Delta T U,
  wf_ty Delta (Ty_All T) -> wf_ty Delta U -> wf_ty Delta (open_ty T U).
Proof.
  intros Delta T U Hall HU.
  inversion Hall as [| |L Delta0 body Hbody| |]; subst.
  set (X := fresh (L ++ Delta ++ fv_ty T)).
  assert (HX : ~ In X (L ++ Delta ++ fv_ty T)).
  { subst X. apply fresh_notin. }
  repeat rewrite in_app_iff in HX.
  assert (HXL : ~ In X L) by intuition.
  assert (HXDelta : ~ In X Delta) by intuition.
  assert (HXT : ~ In X (fv_ty T)) by intuition.
  pose proof (Hbody X HXL) as Hopened.
  set (theta := type_subst_update identity_type_substitution X U).
  assert (Htheta_closed : type_substitution_closed theta).
  { unfold theta. apply type_subst_update_closed.
    - apply identity_type_substitution_closed.
    - apply wf_ty_lc with Delta. exact HU. }
  assert (Htheta_wf : type_substitution_wf (X :: Delta) Delta theta).
  { unfold theta, type_substitution_wf, type_subst_update,
      identity_type_substitution.
    intros Y [E | Hin].
    - subst Y. rewrite Nat.eqb_refl. exact HU.
    - assert (Hneq : X <> Y) by (intro; subst; contradiction).
      rewrite (proj2 (Nat.eqb_neq X Y)) by assumption.
      apply WF_Var. exact Hin. }
  pose proof (wf_ty_instantiate _ _ Hopened Delta theta Htheta_wf) as Hinst.
  assert (Hopen : instantiate_ty theta (open_ty T (Ty_FVar X)) = open_ty T U).
  { unfold theta.
    rewrite instantiate_ty_open_local.
    - rewrite instantiate_ty_identity. reflexivity.
    - exact HXT.
    - intros Y Hin. apply lc_ty_fvar.
    - apply wf_ty_lc with Delta. exact HU. }
  rewrite Hopen in Hinst. exact Hinst.
Qed.

Lemma typing_type_wf : forall Delta Gamma t T,
  has_type Delta Gamma t T -> wf_ty Delta T.
Proof.
  intros Delta Gamma t T Hty. induction Hty.
  - exact H0.
  - apply WF_Arrow; [exact H |].
    set (x := fresh L). apply H1 with x. subst x. apply fresh_notin.
  - inversion IHHty1. assumption.
  - apply WF_All with L. intros X Hfresh. apply H0. exact Hfresh.
  - eapply wf_ty_open_all; eauto.
  - apply WF_Int.
  - apply WF_Int.
  - apply WF_Int.
  - apply WF_Arrow; assumption.
  - assumption.
  - apply WF_Bool.
  - apply WF_Bool.
  - exact IHHty2.
Qed.

Lemma fv_tm_open_preserves : forall t k u x,
  In x (fv_tm t) -> In x (fv_tm (open_tm_rec k u t)).
Proof.
  induction t; intros k u x Hin; simpl in *; try contradiction; try assumption;
    try solve [eauto];
    repeat rewrite in_app_iff in *; intuition eauto.
Qed.

Lemma fv_tm_open_type : forall t k U,
  fv_tm (open_tm_ty_rec k U t) = fv_tm t.
Proof.
  induction t; intros; simpl; rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3; reflexivity.
Qed.

Lemma typing_fv_bound : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall x, lookup_context x Gamma = None -> ~ In x (fv_tm t).
Proof.
  intros Delta Gamma t T Hty.
  induction Hty as
    [Delta Gamma y T Hlookup Hwf
    |L Delta Gamma A body B HA Hbody IHbody
    |Delta Gamma t1 t2 A B Ht1 IHt1 Ht2 IHt2
    |L Delta Gamma body T Hbody IHbody
    |Delta Gamma t T U Ht IHt HU
    |Delta Gamma n
    |Delta Gamma t1 t2 Ht1 IHt1 Ht2 IHt2
      | Delta Gamma op t1 t2 Ht1 IHt1 Ht2 IHt2
    |L Delta Gamma A B metric body HA HB Hmetric IHmetric Hbody IHbody
    |Delta Gamma t t0 t1 T Ht IHt Ht0 IHt0 Ht1 IHt1
      | Delta Gamma | Delta Gamma
      | Delta Gamma t1 t2 t3 T Ht1 IHt1 Ht2 IHt2 Ht3 IHt3];
    intros x Hnone Hin; simpl in Hin.
  - destruct Hin as [E | []]. subst. congruence.
  - set (y := fresh (x :: L)).
    assert (Hy : ~ In y (x :: L)) by apply fresh_notin. simpl in Hy.
    apply (IHbody y ltac:(tauto) x).
    + simpl. rewrite (proj2 (Nat.eqb_neq x y)) by intuition congruence. exact Hnone.
    + apply fv_tm_open_preserves. exact Hin.
  - apply in_app_iff in Hin. destruct Hin; [eapply IHt1 | eapply IHt2]; eauto.
  - apply (IHbody (fresh L) (fresh_notin L) x Hnone).
    unfold open_tm_ty. rewrite fv_tm_open_type. exact Hin.
  - eapply IHt; eauto.
  - contradiction.
  - apply in_app_iff in Hin. destruct Hin; [eapply IHt1 | eapply IHt2]; eauto.
  - apply in_app_iff in Hin. destruct Hin; [eapply IHt1 | eapply IHt2]; eauto.
  - set (f := fresh (x :: L)).
    set (y := fresh (f :: x :: L)).
    assert (Hf : ~ In f (x :: L)) by apply fresh_notin.
    assert (Hy : ~ In y (f :: x :: L)) by apply fresh_notin.
    simpl in Hf, Hy.
    apply in_app_iff in Hin. destruct Hin as [Hin | Hin].
    + apply (IHmetric y ltac:(tauto) x).
      * simpl. rewrite (proj2 (Nat.eqb_neq x y)) by intuition congruence. exact Hnone.
      * apply fv_tm_open_preserves. exact Hin.
    + apply (IHbody f y ltac:(tauto) ltac:(simpl; tauto) x).
      * simpl. rewrite (proj2 (Nat.eqb_neq x f)) by intuition congruence.
        rewrite (proj2 (Nat.eqb_neq x y)) by intuition congruence. exact Hnone.
      * unfold open_fix_body, open_tm.
        apply fv_tm_open_preserves. apply fv_tm_open_preserves. exact Hin.
  - repeat rewrite in_app_iff in Hin.
    destruct Hin as [Hin | [Hin | Hin]]; [eapply IHt | eapply IHt0 | eapply IHt1]; eauto.
  - contradiction.
  - contradiction.
  - repeat rewrite in_app_iff in Hin. destruct Hin as [Hin | [Hin | Hin]]; [eapply IHt1 |eapply IHt2 |eapply IHt3]; eauto.
Qed.

Lemma closed_typing_no_free_terms : forall Delta t T,
  has_type Delta empty t T -> fv_tm t = [].
Proof.
  intros Delta t T Htyped.
  destruct (fv_tm t) as [| x xs] eqn:E; [reflexivity |].
  exfalso. apply (typing_fv_bound _ _ _ _ Htyped x eq_refl).
  rewrite E. simpl. auto.
Qed.

Lemma instantiate_no_free_terms : forall t gamma,
  fv_tm t = [] ->
  instantiate identity_type_substitution gamma t = t.
Proof.
  induction t; intros gamma Hfv; simpl in *; try discriminate;
    repeat match goal with H : _ ++ _ = [] |- _ => apply app_eq_nil in H as [? ?] end;
    rewrite ?instantiate_ty_identity; f_equal; eauto.
Qed.

End SystemFRefinementIfRecursionCoreTyping.
