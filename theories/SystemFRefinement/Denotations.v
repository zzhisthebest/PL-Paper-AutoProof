From Stdlib Require Import Arith.PeanoNat Lists.List Lia Program.Wf.
From Equations Require Import Equations.
From AutoProof.SystemFRefinement Require Import
  Syntax Infrastructure CoreTyping RefinementTyping Evaluation.

Module SystemFRefinementDenotations.
Import ListNotations.
Import SystemFRefinement.
Import SystemFRefinementInfrastructure.
Import SystemFRefinementCoreTyping.
Import SystemFRefinementTyping.
Import SystemFRefinementEvaluation.

Fixpoint fv_pred (p : qualifier) : list atom :=
  match p with
  | Pred_True | Pred_False => []
  | Pred_Eq t1 t2 | Pred_Lt t1 t2 | Pred_Le t1 t2 => fv_tm t1 ++ fv_tm t2
  | Pred_And p1 p2 | Pred_Or p1 p2 => fv_pred p1 ++ fv_pred p2
  | Pred_Not p => fv_pred p
  end.

Definition fv_qualifier := fv_pred.

Fixpoint fv_rty (R : rty) : list atom :=
  match R with
  | R_Refine _ ps => fv_qualifier ps
  | R_Func R1 R2 | R_Exists R1 R2 => fv_rty R1 ++ fv_rty R2
  | R_Poly R1 => fv_rty R1
  end.

Fixpoint ftv_pred (p : qualifier) : list atom :=
  match p with
  | Pred_True | Pred_False => []
  | Pred_Eq t1 t2 | Pred_Lt t1 t2 | Pred_Le t1 t2 => ftv_tm t1 ++ ftv_tm t2
  | Pred_And p1 p2 | Pred_Or p1 p2 => ftv_pred p1 ++ ftv_pred p2
  | Pred_Not p => ftv_pred p
  end.

Definition ftv_qualifier := ftv_pred.

Fixpoint ftv_rty (R : rty) : list atom :=
  match R with
  | R_Refine T ps => fv_ty T ++ ftv_qualifier ps
  | R_Func R1 R2 | R_Exists R1 R2 => ftv_rty R1 ++ ftv_rty R2
  | R_Poly R1 => ftv_rty R1
  end.

Fixpoint fv_rcontext (RGamma : rcontext) : list atom :=
  match RGamma with
  | [] => []
  | (_, R) :: RGamma' => fv_rty R ++ fv_rcontext RGamma'
  end.

Fixpoint ftv_rcontext (RGamma : rcontext) : list atom :=
  match RGamma with
  | [] => []
  | (_, R) :: RGamma' => ftv_rty R ++ ftv_rcontext RGamma'
  end.

Fixpoint instantiate_pred
    (theta : type_substitution) (gamma : term_substitution)
    (p : qualifier) : qualifier :=
  match p with
  | Pred_True => Pred_True
  | Pred_False => Pred_False
  | Pred_Eq t1 t2 =>
      Pred_Eq (instantiate theta gamma t1) (instantiate theta gamma t2)
  | Pred_Lt t1 t2 => Pred_Lt (instantiate theta gamma t1) (instantiate theta gamma t2)
  | Pred_Le t1 t2 => Pred_Le (instantiate theta gamma t1) (instantiate theta gamma t2)
  | Pred_And p1 p2 => Pred_And (instantiate_pred theta gamma p1) (instantiate_pred theta gamma p2)
  | Pred_Not p => Pred_Not (instantiate_pred theta gamma p)
  | Pred_Or p1 p2 =>
      Pred_Or (instantiate_pred theta gamma p1)
        (instantiate_pred theta gamma p2)
  end.

Definition instantiate_qualifier := instantiate_pred.

Fixpoint instantiate_rty
    (theta : type_substitution) (gamma : term_substitution)
    (R : rty) : rty :=
  match R with
  | R_Refine T ps =>
      R_Refine (instantiate_ty theta T) (instantiate_qualifier theta gamma ps)
  | R_Func R1 R2 =>
      R_Func (instantiate_rty theta gamma R1)
        (instantiate_rty theta gamma R2)
  | R_Exists R1 R2 =>
      R_Exists (instantiate_rty theta gamma R1)
        (instantiate_rty theta gamma R2)
  | R_Poly R1 => R_Poly (instantiate_rty theta gamma R1)
  end.

(* 定义refinement type 语法大小*)
Fixpoint rty_size (R : rty) : nat :=
  match R with
  | R_Refine _ _ => 1
  | R_Func R1 R2 => S (rty_size R1 + rty_size R2)
  | R_Exists R1 R2 => S (rty_size R1 + rty_size R2)
  | R_Poly R1 => S (rty_size R1)
  end.

Lemma rty_size_open_tm_rec : forall R k u,
  rty_size (open_rty_tm_rec k u R) = rty_size R.
Proof.
  induction R; intros; simpl; rewrite ?IHR1, ?IHR2, ?IHR; reflexivity.
Qed.

Lemma rty_size_open_tm : forall R u,
  rty_size (open_rty_tm R u) = rty_size R.
Proof.
  intros. apply rty_size_open_tm_rec.
Qed.

Lemma rty_size_open_ty_rec : forall R k U,
  rty_size (open_rty_ty_rec k U R) = rty_size R.
Proof.
  induction R; intros; simpl; rewrite ?IHR1, ?IHR2, ?IHR; reflexivity.
Qed.

Lemma rty_size_open_ty : forall R U,
  rty_size (open_rty_ty R U) = rty_size R.
Proof.
  intros. apply rty_size_open_ty_rec.
Qed.

Lemma erase_instantiate_rty : forall theta gamma R,
  erase (instantiate_rty theta gamma R) = instantiate_ty theta (erase R).
Proof.
  induction R; intros; simpl; rewrite ?IHR1, ?IHR2, ?IHR; reflexivity.
Qed.

Lemma instantiate_pred_open_tm_rec : forall p k theta gamma x u,
  ~ In x (fv_pred p) ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  instantiate_pred theta (term_subst_update gamma x u)
    (open_pred_tm_rec k (tm_fvar x) p) =
  open_pred_tm_rec k u (instantiate_pred theta gamma p).
Proof.
  induction p; intros; simpl in *; try reflexivity;
    try solve [rewrite in_app_iff in H; rewrite !instantiate_open_tm_rec; intuition];
    try solve [rewrite in_app_iff in H; rewrite IHp1, IHp2; intuition].
  f_equal. apply IHp; assumption.
Qed.

Lemma instantiate_qualifier_open_tm_rec : forall ps k theta gamma x u,
  ~ In x (fv_qualifier ps) ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  instantiate_qualifier theta (term_subst_update gamma x u)
    (open_qualifier_tm_rec k (tm_fvar x) ps) =
  open_qualifier_tm_rec k u (instantiate_qualifier theta gamma ps).
Proof.
  exact instantiate_pred_open_tm_rec.
Qed.

Lemma instantiate_rty_open_tm_rec : forall R k theta gamma x u,
  ~ In x (fv_rty R) ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  instantiate_rty theta (term_subst_update gamma x u)
    (open_rty_tm_rec k (tm_fvar x) R) =
  open_rty_tm_rec k u (instantiate_rty theta gamma R).
Proof.
  induction R; intros; simpl in *.
  - f_equal. apply instantiate_qualifier_open_tm_rec; assumption.
  - rewrite in_app_iff in H.
    rewrite IHR1, IHR2; intuition.
  - rewrite in_app_iff in H.
    rewrite IHR1, IHR2; intuition.
  - f_equal. apply IHR; assumption.
Qed.

Lemma instantiate_rty_open_tm : forall R theta gamma x u,
  ~ In x (fv_rty R) ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  instantiate_rty theta (term_subst_update gamma x u)
    (open_rty_tm R (tm_fvar x)) =
  open_rty_tm (instantiate_rty theta gamma R) u.
Proof.
  intros. unfold open_rty_tm.
  apply instantiate_rty_open_tm_rec; assumption.
Qed.

Lemma instantiate_pred_open_ty_rec : forall p k theta gamma X U,
  ~ In X (ftv_pred p) ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_ty U ->
  instantiate_pred (type_subst_update theta X U) gamma
    (open_pred_ty_rec k (Ty_FVar X) p) =
  open_pred_ty_rec k U (instantiate_pred theta gamma p).
Proof.
  induction p; intros; simpl in *; try reflexivity;
    try solve [rewrite in_app_iff in H; rewrite !instantiate_open_ty_rec; intuition];
    try solve [rewrite in_app_iff in H; rewrite IHp1, IHp2; intuition].
  f_equal. apply IHp; assumption.
Qed.

Lemma instantiate_qualifier_open_ty_rec : forall ps k theta gamma X U,
  ~ In X (ftv_qualifier ps) ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_ty U ->
  instantiate_qualifier (type_subst_update theta X U) gamma
    (open_qualifier_ty_rec k (Ty_FVar X) ps) =
  open_qualifier_ty_rec k U (instantiate_qualifier theta gamma ps).
Proof.
  exact instantiate_pred_open_ty_rec.
Qed.

Lemma instantiate_rty_open_ty_rec : forall R k theta gamma X U,
  ~ In X (ftv_rty R) ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_ty U ->
  instantiate_rty (type_subst_update theta X U) gamma
    (open_rty_ty_rec k (Ty_FVar X) R) =
  open_rty_ty_rec k U (instantiate_rty theta gamma R).
Proof.
  induction R; intros; simpl in *.
  - rewrite in_app_iff in H.
    f_equal.
    + apply instantiate_ty_open_rec; intuition.
    + apply instantiate_qualifier_open_ty_rec; intuition.
  - rewrite in_app_iff in H.
    rewrite IHR1, IHR2; intuition.
  - rewrite in_app_iff in H.
    rewrite IHR1, IHR2; intuition.
  - f_equal. apply IHR; assumption.
Qed.

Lemma instantiate_rty_open_ty : forall R theta gamma X U,
  ~ In X (ftv_rty R) ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_ty U ->
  instantiate_rty (type_subst_update theta X U) gamma
    (open_rty_ty R (Ty_FVar X)) =
  open_rty_ty (instantiate_rty theta gamma R) U.
Proof.
  intros. unfold open_rty_ty.
  apply instantiate_rty_open_ty_rec; assumption.
Qed.

Lemma instantiate_term_update_irrelevant : forall t theta gamma x u,
  ~ In x (fv_tm t) ->
  instantiate theta (term_subst_update gamma x u) t =
  instantiate theta gamma t.
Proof.
  induction t; intros; simpl in *; try reflexivity.
  - unfold term_subst_update.
    rewrite (proj2 (Nat.eqb_neq x a)); [reflexivity | intuition].
  - f_equal. apply IHt. exact H.
  - rewrite in_app_iff in H. f_equal; [apply IHt1 | apply IHt2]; intuition.
  - f_equal. apply IHt. exact H.
  - f_equal. apply IHt. exact H.
  - rewrite in_app_iff in H. f_equal; [apply IHt1 | apply IHt2]; intuition.
  - rewrite in_app_iff in H. f_equal; [apply IHt1 | apply IHt2]; intuition.
Qed.

Lemma instantiate_rty_term_update_irrelevant : forall R theta gamma x u,
  ~ In x (fv_rty R) ->
  instantiate_rty theta (term_subst_update gamma x u) R =
  instantiate_rty theta gamma R.
Proof.
  induction R as [T ps | R1 IHR1 R2 IHR2 | R1 IHR1 R2 IHR2 | R IHR];
    intros; simpl in *.
  - f_equal. induction ps; simpl in *; try reflexivity;
      try solve [rewrite in_app_iff in H; f_equal; apply instantiate_term_update_irrelevant; intuition];
      try solve [rewrite in_app_iff in H; f_equal; [apply IHps1|apply IHps2]; intuition].
    f_equal. apply IHps. exact H.
  - rewrite in_app_iff in H. f_equal; [apply IHR1|apply IHR2]; intuition.
  - rewrite in_app_iff in H. f_equal; [apply IHR1|apply IHR2]; intuition.
  - f_equal. apply IHR. exact H.
Qed.

Lemma instantiate_term_type_update_irrelevant : forall t theta gamma X U,
  ~ In X (ftv_tm t) ->
  instantiate (type_subst_update theta X U) gamma t =
  instantiate theta gamma t.
Proof.
  induction t; intros; simpl in *; try reflexivity.
  - rewrite in_app_iff in H. f_equal.
    + apply instantiate_ty_update_irrelevant. tauto.
    + apply IHt. tauto.
  - rewrite in_app_iff in H. f_equal; [apply IHt1 | apply IHt2]; tauto.
  - f_equal. apply IHt. exact H.
  - rewrite in_app_iff in H. f_equal.
    + apply IHt. tauto.
    + apply instantiate_ty_update_irrelevant. tauto.
  - rewrite in_app_iff in H. f_equal; [apply IHt1 | apply IHt2]; intuition.
  - rewrite in_app_iff in H. f_equal; [apply IHt1 | apply IHt2]; intuition.
Qed.

Lemma instantiate_rty_type_update_irrelevant : forall R theta gamma X U,
  ~ In X (ftv_rty R) ->
  instantiate_rty (type_subst_update theta X U) gamma R =
  instantiate_rty theta gamma R.
Proof.
  induction R as [T ps | R1 IHR1 R2 IHR2 | R1 IHR1 R2 IHR2 | R IHR];
    intros; simpl in *.
  - rewrite in_app_iff in H. f_equal.
    + apply instantiate_ty_update_irrelevant. intuition.
    + assert (HF : ~ In X (ftv_pred ps)) by intuition.
      clear H. rename HF into H.
      induction ps; simpl in *; try reflexivity;
        try solve [rewrite in_app_iff in H; f_equal; apply instantiate_term_type_update_irrelevant; intuition];
        try solve [rewrite in_app_iff in H; f_equal; [apply IHps1|apply IHps2]; intuition].
      f_equal. apply IHps. exact H.
  - rewrite in_app_iff in H. f_equal; [apply IHR1|apply IHR2]; intuition.
  - rewrite in_app_iff in H. f_equal; [apply IHR1|apply IHR2]; intuition.
  - f_equal. apply IHR. exact H.
Qed.

Lemma instantiate_open_tm_rec_commute : forall t k u theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  instantiate theta gamma (open_tm_rec k u t) =
  open_tm_rec k (instantiate theta gamma u) (instantiate theta gamma t).
Proof.
  induction t; intros; simpl; try reflexivity.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. apply open_tm_rec_lc_at with (K := 0).
    eapply lc_tm_at_monotone; [apply H0 | lia | lia].
  - f_equal. apply IHt; assumption.
  - f_equal; [apply IHt1 | apply IHt2]; assumption.
  - f_equal. apply IHt; assumption.
  - f_equal. apply IHt; assumption.
  - f_equal; [apply IHt1 | apply IHt2]; assumption.
  - f_equal; [apply IHt1 | apply IHt2]; assumption.
Qed.

Lemma instantiate_open_tm_commute : forall t u theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  instantiate theta gamma (open_tm t u) =
  open_tm (instantiate theta gamma t) (instantiate theta gamma u).
Proof.
  intros. unfold open_tm. apply instantiate_open_tm_rec_commute; assumption.
Qed.

Lemma instantiate_pred_open_tm_commute : forall p k u theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  instantiate_pred theta gamma (open_pred_tm_rec k u p) =
  open_pred_tm_rec k (instantiate theta gamma u)
    (instantiate_pred theta gamma p).
Proof.
  induction p; intros; simpl; try reflexivity;
    try solve [rewrite !instantiate_open_tm_rec_commute; try assumption; reflexivity];
    try solve [rewrite IHp1, IHp2; try assumption; reflexivity].
  f_equal. apply IHp; assumption.
Qed.

Lemma instantiate_qualifier_open_tm_commute : forall ps k u theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  instantiate_qualifier theta gamma (open_qualifier_tm_rec k u ps) =
  open_qualifier_tm_rec k (instantiate theta gamma u)
    (instantiate_qualifier theta gamma ps).
Proof.
  exact instantiate_pred_open_tm_commute.
Qed.

Lemma instantiate_rty_open_tm_commute : forall R k u theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  instantiate_rty theta gamma (open_rty_tm_rec k u R) =
  open_rty_tm_rec k (instantiate theta gamma u)
    (instantiate_rty theta gamma R).
Proof.
  induction R; intros; simpl.
  - f_equal. apply instantiate_qualifier_open_tm_commute; assumption.
  - rewrite IHR1, IHR2; try assumption. reflexivity.
  - rewrite IHR1, IHR2; try assumption. reflexivity.
  - rewrite IHR; try assumption. reflexivity.
Qed.

Lemma instantiate_rty_open_tm_commute_top : forall R u theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  instantiate_rty theta gamma (open_rty_tm R u) =
  open_rty_tm (instantiate_rty theta gamma R) (instantiate theta gamma u).
Proof.
  intros. unfold open_rty_tm. apply instantiate_rty_open_tm_commute; assumption.
Qed.

Lemma instantiate_open_ty_tm_rec_commute : forall t k U theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_ty U ->
  instantiate theta gamma (open_tm_ty_rec k U t) =
  open_tm_ty_rec k (instantiate_ty theta U) (instantiate theta gamma t).
Proof.
  induction t; intros; simpl; try reflexivity.
  - symmetry. apply open_tm_ty_rec_lc_at with (k := 0).
    eapply lc_tm_at_monotone; [apply H0 | lia | lia].
  - f_equal.
    + apply instantiate_ty_open_rec_commute. exact H.
    + apply IHt; assumption.
  - f_equal; [apply IHt1 | apply IHt2]; assumption.
  - f_equal. apply IHt; assumption.
  - f_equal.
    + apply IHt; assumption.
    + apply instantiate_ty_open_rec_commute. exact H.
  - f_equal; [apply IHt1 | apply IHt2]; assumption.
  - f_equal; [apply IHt1 | apply IHt2]; assumption.
Qed.

Lemma instantiate_open_ty_tm_commute : forall t U theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_ty U ->
  instantiate theta gamma (open_tm_ty t U) =
  open_tm_ty (instantiate theta gamma t) (instantiate_ty theta U).
Proof.
  intros. unfold open_tm_ty.
  apply instantiate_open_ty_tm_rec_commute; assumption.
Qed.

Lemma instantiate_pred_open_ty_commute : forall p k U theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_ty U ->
  instantiate_pred theta gamma (open_pred_ty_rec k U p) =
  open_pred_ty_rec k (instantiate_ty theta U)
    (instantiate_pred theta gamma p).
Proof.
  induction p; intros; simpl; try reflexivity;
    try solve [rewrite !instantiate_open_ty_tm_rec_commute; try assumption; reflexivity];
    try solve [rewrite IHp1, IHp2; try assumption; reflexivity].
  f_equal. apply IHp; assumption.
Qed.

Lemma instantiate_qualifier_open_ty_commute : forall ps k U theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_ty U ->
  instantiate_qualifier theta gamma (open_qualifier_ty_rec k U ps) =
  open_qualifier_ty_rec k (instantiate_ty theta U)
    (instantiate_qualifier theta gamma ps).
Proof.
  exact instantiate_pred_open_ty_commute.
Qed.

Lemma instantiate_rty_open_ty_commute : forall R k U theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_ty U ->
  instantiate_rty theta gamma (open_rty_ty_rec k U R) =
  open_rty_ty_rec k (instantiate_ty theta U)
    (instantiate_rty theta gamma R).
Proof.
  induction R; intros; simpl.
  - rewrite instantiate_ty_open_rec_commute,
      instantiate_qualifier_open_ty_commute; try assumption. reflexivity.
  - rewrite IHR1, IHR2; try assumption. reflexivity.
  - rewrite IHR1, IHR2; try assumption. reflexivity.
  - rewrite IHR; try assumption. reflexivity.
Qed.

Lemma instantiate_rty_open_ty_commute_top : forall R U theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_ty U ->
  instantiate_rty theta gamma (open_rty_ty R U) =
  open_rty_ty (instantiate_rty theta gamma R) (instantiate_ty theta U).
Proof.
  intros. unfold open_rty_ty. apply instantiate_rty_open_ty_commute; assumption.
Qed.

Lemma instantiate_value : forall v theta gamma,
  value v ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  value (instantiate theta gamma v).
Proof.
  intros v theta gamma Hv Htheta Hgamma. inversion Hv; subst; simpl.
  - apply v_abs.
    change (locally_closed_tm (instantiate theta gamma (tm_abs T t))).
    apply instantiate_closed; assumption.
  - apply v_tabs.
    change (locally_closed_tm (instantiate theta gamma (tm_tabs t))).
    apply instantiate_closed; assumption.
  - apply v_int.
Qed.

Lemma instantiate_step : forall t t' theta gamma,
  t --> t' ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  instantiate theta gamma t --> instantiate theta gamma t'.
Proof.
  intros t t' theta gamma Hstep Htheta Hgamma. induction Hstep; simpl.
  - rewrite instantiate_open_tm_commute; try assumption.
    + apply ST_AppAbs.
      * change (locally_closed_tm (instantiate theta gamma (tm_abs T t))).
        apply instantiate_closed; assumption.
      * apply instantiate_value; assumption.
    + apply value_regular. exact H0.
  - apply ST_App1.
    + apply IHHstep.
    + apply instantiate_closed; assumption.
  - apply ST_App2.
    + apply instantiate_value; assumption.
    + apply IHHstep.
  - rewrite instantiate_open_ty_tm_commute; try assumption.
    + apply ST_TAppTabs.
      * change (locally_closed_tm (instantiate theta gamma (tm_tabs t))).
        apply instantiate_closed; assumption.
      * apply instantiate_ty_closed; assumption.
  - apply ST_TApp.
    + apply IHHstep.
    + apply instantiate_ty_closed; assumption.
  - apply ST_Div1; [assumption|apply instantiate_closed; assumption].
  - apply ST_Div2; [apply instantiate_value; assumption|assumption].
  - apply ST_DivInt. assumption.
  - apply ST_Arith1; [assumption|apply instantiate_closed; assumption].
  - apply ST_Arith2; [apply instantiate_value; assumption|assumption].
  - apply ST_ArithInt.
Qed.

Lemma instantiate_predicate_multistep : forall t t' theta gamma,
  predicate_multistep t t' ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  predicate_multistep (instantiate theta gamma t)
    (instantiate theta gamma t').
Proof.
  intros t t' theta gamma Hmulti Htheta Hgamma. induction Hmulti.
  - apply PMS_Refl.
  - eapply PMS_Step.
    + eapply instantiate_step; eauto.
    + exact IHHmulti.
Qed.

Lemma instantiate_ty_no_free : forall T theta,
  fv_ty T = [] -> instantiate_ty theta T = T.
Proof.
  induction T; intros; simpl in *; try discriminate; try reflexivity.
  - apply app_eq_nil in H as [H1 H2]. rewrite IHT1, IHT2; auto.
  - rewrite IHT; auto.
Qed.

Lemma instantiate_no_free : forall t theta gamma,
  fv_tm t = [] -> ftv_tm t = [] -> instantiate theta gamma t = t.
Proof.
  induction t; intros; simpl in *; try discriminate; try reflexivity;
    repeat match goal with H : _ ++ _ = [] |- _ => apply app_eq_nil in H as [? ?] end;
    f_equal; eauto using instantiate_ty_no_free.
Qed.

Lemma instantiate_pred_closed : forall p theta gamma,
  predicate_closed p -> instantiate_pred theta gamma p = p.
Proof.
  induction p; intros; simpl in *; try reflexivity;
    try solve [decompose [and] H; f_equal; apply instantiate_no_free; assumption];
    try solve [destruct H; f_equal; auto].
  f_equal. apply IHp. assumption.
Qed.

Lemma instantiate_qualifier_holds : forall ps theta gamma,
  predicate_closed ps ->
  qualifier_holds ps ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  qualifier_holds (instantiate_qualifier theta gamma ps).
Proof.
  intros ps theta gamma Hclosed Hholds Htheta Hgamma.
  unfold instantiate_qualifier. rewrite instantiate_pred_closed by assumption.
  exact Hholds.
Qed.

Lemma instantiate_pred_open_rec_commute : forall p k u theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  instantiate_pred theta gamma (open_pred_tm_rec k u p) =
  open_pred_tm_rec k (instantiate theta gamma u)
    (instantiate_pred theta gamma p).
Proof.
  induction p; intros; simpl; try reflexivity;
    try solve [rewrite !instantiate_open_tm_rec_commute; try assumption; reflexivity];
    try solve [rewrite IHp1, IHp2; try assumption; reflexivity].
  f_equal. apply IHp; assumption.
Qed.

Lemma instantiate_qualifier_open_commute : forall ps u theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  instantiate_qualifier theta gamma (open_qualifier_tm ps u) =
  open_qualifier_tm (instantiate_qualifier theta gamma ps)
    (instantiate theta gamma u).
Proof.
  intros. apply instantiate_pred_open_rec_commute; assumption.
Qed.

(** [denotes R v] means that the value [v] semantically belongs to the
    refinement type [R]. *)
(* 值上的logical relation *)
Equations denotes (R : rty) (v : tm) : Prop by wf (rty_size R) lt :=
  denotes (R_Refine T ps) v :=
      (* 显然 *)
      value v /\
      has_type [] empty v T /\
      qualifier_holds (open_qualifier_tm ps v);
  denotes (R_Func R1 R2) v :=
      (* 一个函数属于 R1 -> R2，当它把每个满足 R1 的输入，都计算成满足相应 R2 的输出。 *)
      value v /\
      has_type [] empty v (erase (R_Func R1 R2)) /\
      forall arg,
        denotes R1 arg ->
        locally_closed_tm (tm_app v arg) /\
        halts (tm_app v arg) /\
        forall result,
          multi (tm_app v arg) result ->
          value result ->
          denotes (open_rty_tm R2 arg) result;
  denotes (R_Exists R1 R2) v :=
      value v /\
      has_type [] empty v (erase (R_Exists R1 R2)) /\
      exists witness,
        denotes R1 witness /\
        denotes (open_rty_tm R2 witness) v;
  denotes (R_Poly R1) v :=
      value v /\
      has_type [] empty v (erase (R_Poly R1)) /\
      forall U,
        wf_ty [] U ->
        locally_closed_tm (tm_tapp v U) /\
        halts (tm_tapp v U) /\
        forall result,
          multi (tm_tapp v U) result ->
          value result ->
          denotes (open_rty_ty R1 U) result.
Next Obligation.
  simpl. lia.
Qed.
Next Obligation.
  rewrite rty_size_open_tm. simpl. lia.
Qed.
Next Obligation.
  simpl. lia.
Qed.
Next Obligation.
  rewrite rty_size_open_tm. simpl. lia.
Qed.
Next Obligation.
  rewrite rty_size_open_ty. simpl. lia.
Qed.

(** [evals_denotes R t] means that every value reachable from [t] belongs to
    [R].  The halting component rules out stuck computations. *)
(* 程序上的logical relation *)
Definition evals_denotes (R : rty) (t : tm) : Prop :=
  locally_closed_tm t /\
  halts t /\
  forall v,
    multi t v ->
    value v ->
    denotes R v.

Lemma denotes_refine_iff : forall T ps v,
  denotes (R_Refine T ps) v <->
  value v /\ has_type [] empty v T /\
  qualifier_holds (open_qualifier_tm ps v).
Proof.
  intros. simp denotes. reflexivity.
Qed.

Lemma denotes_func_iff : forall R1 R2 v,
  denotes (R_Func R1 R2) v <->
  value v /\ has_type [] empty v (erase (R_Func R1 R2)) /\
  forall arg,
    denotes R1 arg ->
    locally_closed_tm (tm_app v arg) /\
    halts (tm_app v arg) /\
    forall result,
      multi (tm_app v arg) result ->
      value result ->
      denotes (open_rty_tm R2 arg) result.
Proof.
  intros. simp denotes. reflexivity.
Qed.

Lemma denotes_exists_iff : forall R1 R2 v,
  denotes (R_Exists R1 R2) v <->
  value v /\ has_type [] empty v (erase (R_Exists R1 R2)) /\
  exists witness,
    denotes R1 witness /\ denotes (open_rty_tm R2 witness) v.
Proof.
  intros. simp denotes. reflexivity.
Qed.

Lemma denotes_poly_iff : forall R v,
  denotes (R_Poly R) v <->
  value v /\ has_type [] empty v (erase (R_Poly R)) /\
  forall U,
    wf_ty [] U ->
    locally_closed_tm (tm_tapp v U) /\
    halts (tm_tapp v U) /\
    forall result,
      multi (tm_tapp v U) result ->
      value result ->
      denotes (open_rty_ty R U) result.
Proof.
  intros. simp denotes. reflexivity.
Qed.

Lemma denotes_value : forall R v,
  denotes R v -> value v.
Proof.
  intros R v H.
  destruct R; cbn [denotes] in H; exact (proj1 H).
Qed.

Lemma denotes_refinement_predicates : forall T ps v,
  denotes (R_Refine T ps) v ->
  qualifier_holds (open_qualifier_tm ps v).
Proof.
  intros T ps v H.
  cbn [denotes] in H.
  exact (proj2 (proj2 H)).
Qed.

Lemma instantiate_pred_identity : forall p,
  instantiate_pred identity_type_substitution identity_term_substitution p = p.
Proof.
  induction p; simpl; rewrite ?instantiate_identity, ?IHp1, ?IHp2, ?IHp; reflexivity.
Qed.

Lemma instantiate_qualifier_identity : forall ps,
  instantiate_qualifier identity_type_substitution identity_term_substitution ps = ps.
Proof.
  exact instantiate_pred_identity.
Qed.

Lemma instantiate_rty_identity : forall R,
  instantiate_rty identity_type_substitution identity_term_substitution R = R.
Proof.
  induction R; simpl.
  - rewrite instantiate_ty_identity, instantiate_qualifier_identity. reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR. reflexivity.
Qed.

End SystemFRefinementDenotations.
