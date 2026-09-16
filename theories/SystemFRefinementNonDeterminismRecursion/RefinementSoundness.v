From Stdlib Require Import Arith.PeanoNat Arith.Wf_nat Lists.List Lia ZArith.ZArith.
From AutoProof.SystemFRefinementNonDeterminismRecursion Require Import
  Syntax Infrastructure CoreTyping RefinementTyping Evaluation Denotations Termination.

Module SystemFRefinementNonDeterminismRecursionSoundness.
Import ListNotations.
Import SystemFRefinementNonDeterminismRecursion.
Import SystemFRefinementNonDeterminismRecursionInfrastructure.
Import SystemFRefinementNonDeterminismRecursionCoreTyping.
Import SystemFRefinementNonDeterminismRecursionTyping.
Import SystemFRefinementNonDeterminismRecursionEvaluation.
Import SystemFRefinementNonDeterminismRecursionDenotations.
Import SystemFRefinementNonDeterminismRecursionTermination.

(* related_substitution theta gamma RGamma
表示：
类型替换 theta 和程序替换 gamma 满足 RGamma 中记录的全部要求。 *)
Record related_substitution
    (theta : type_substitution) (gamma : term_substitution)
    (RGamma : rcontext) : Prop := {
  substitution_values : forall x, value (gamma x);
  substitution_lookup : forall x R,
    lookup_rcontext x RGamma = Some R ->
    denotes (instantiate_rty theta gamma R) (gamma x)
}.
Arguments substitution_values {theta gamma RGamma} _ _.
Arguments substitution_lookup {theta gamma RGamma} _ _ _ _.
Coercion substitution_lookup : related_substitution >-> Funclass.

Lemma denotes_typing : forall R v,
  denotes R v -> has_type [] empty v (erase R).
Proof.
  intros R v H. destruct R; cbn [denotes] in H; exact (proj1 (proj2 H)).
Qed.

Lemma evals_denotes_of_denotes : forall R v,
  denotes R v -> evals_denotes R v.
Proof.
  intros R v Hden. split.
  - apply value_regular. eapply denotes_value. exact Hden.
  - split.
    + apply must_terminate_value. eapply denotes_value. exact Hden.
    + intros result Hsteps Hvalue.
      assert (Hv : value v) by (eapply denotes_value; exact Hden).
      assert (result = v).
      { exact (value_multi_eq v result Hv Hsteps). }
      subst result. exact Hden.
Qed.

Lemma evals_denotes_from_value : forall R v,
  value v -> evals_denotes R v -> denotes R v.
Proof.
  intros R v Hv [_ [_ Hall]].
  apply (Hall v (multi_refl v) Hv).
Qed.

Lemma core_multi_preservation : forall t v T,
  has_type [] empty t T ->
  multi t v ->
  has_type [] empty v T.
Proof.
  intros t v T Htyped Hsteps. induction Hsteps.
  - exact Htyped.
  - apply IHHsteps. eapply core_preservation; eauto.
Qed.

Lemma lookup_erase_context_inv : forall RGamma x T,
  lookup_context x (erase_context RGamma) = Some T ->
  exists R,
    lookup_rcontext x RGamma = Some R /\ erase R = T.
Proof.
  induction RGamma as [|[y R] RGamma IH]; intros x T Hlookup; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + inversion Hlookup; subst. exists R. split; reflexivity.
    + destruct (IH x T Hlookup) as [S [HS HE]].
      exists S. split; assumption.
Qed.

Lemma related_substitution_typed : forall theta gamma RGamma,
  related_substitution theta gamma RGamma ->
  term_substitution_typed (erase_context RGamma) [] empty theta gamma.
Proof.
  intros theta gamma RGamma Hrel x T Hlookup.
  destruct (lookup_erase_context_inv RGamma x T Hlookup)
    as [R [HR Herase]].
  pose proof (denotes_typing _ _ (Hrel x R HR)) as Htyped.
  rewrite erase_instantiate_rty in Htyped.
  rewrite Herase in Htyped. exact Htyped.
Qed.

Lemma lookup_rcontext_fv : forall RGamma y R x,
  lookup_rcontext y RGamma = Some R ->
  In x (fv_rty R) ->
  In x (fv_rcontext RGamma).
Proof.
  induction RGamma as [|[z S] RGamma IH]; intros y R x Hlookup Hin; simpl in *.
  - discriminate.
  - destruct (Nat.eqb y z) eqn:E.
    + inversion Hlookup; subst. apply in_or_app. left. exact Hin.
    + apply in_or_app. right. eapply IH; eauto.
Qed.

Lemma lookup_rcontext_ftv : forall RGamma y R X,
  lookup_rcontext y RGamma = Some R ->
  In X (ftv_rty R) ->
  In X (ftv_rcontext RGamma).
Proof.
  induction RGamma as [|[z S] RGamma IH]; intros y R X Hlookup Hin; simpl in *.
  - discriminate.
  - destruct (Nat.eqb y z) eqn:E.
    + inversion Hlookup; subst. apply in_or_app. left. exact Hin.
    + apply in_or_app. right. eapply IH; eauto.
Qed.

Lemma related_substitution_update : forall theta gamma RGamma x R v,
  related_substitution theta gamma RGamma ->
  denotes (instantiate_rty theta gamma R) v ->
  ~ In x (fv_rty R) ->
  ~ In x (fv_rcontext RGamma) ->
  related_substitution theta (term_subst_update gamma x v)
    (update_rcontext RGamma x R).
Proof.
  intros theta gamma RGamma x R v Hrel Hden HfreshR HfreshGamma.
  constructor.
  { intro y. unfold term_subst_update. destruct (Nat.eqb x y).
    - eapply denotes_value; exact Hden.
    - exact (substitution_values Hrel y). }
  intros y S Hlookup. simpl in Hlookup.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst y. inversion Hlookup; subst S.
    rewrite instantiate_rty_term_update_irrelevant by exact HfreshR.
    unfold term_subst_update. rewrite Nat.eqb_refl.
    exact Hden.
  - apply Nat.eqb_neq in E.
    assert (HlookupS : lookup_rcontext y RGamma = Some S) by exact Hlookup.
    assert (HfreshS : ~ In x (fv_rty S)).
    { intro Hin. apply HfreshGamma. eapply lookup_rcontext_fv; eauto. }
    rewrite instantiate_rty_term_update_irrelevant by exact HfreshS.
    unfold term_subst_update.
    rewrite (proj2 (Nat.eqb_neq x y)) by congruence.
    exact (Hrel y S HlookupS).
Qed.

Lemma related_substitution_type_update : forall theta gamma RGamma X U,
  related_substitution theta gamma RGamma ->
  ~ In X (ftv_rcontext RGamma) ->
  related_substitution (type_subst_update theta X U) gamma RGamma.
Proof.
  intros theta gamma RGamma X U Hrel Hfresh.
  constructor; [exact (substitution_values Hrel) |].
  intros x R Hlookup.
  rewrite instantiate_rty_type_update_irrelevant.
  - exact (Hrel x R Hlookup).
  - intro Hin. apply Hfresh. eapply lookup_rcontext_ftv; eauto.
Qed.

Lemma entails_sound : forall Delta RGamma ps qs,
  entails Delta RGamma ps qs ->
  forall theta gamma,
    type_substitution_closed theta ->
    term_substitution_closed gamma ->
    related_substitution theta gamma RGamma ->
    qualifier_holds (instantiate_qualifier theta gamma ps) ->
    qualifier_holds (instantiate_qualifier theta gamma qs).
Proof.
  intros Delta RGamma ps qs Hentails. induction Hentails;
    intros theta gamma Htheta Hgamma Hrel Hholds;
    cbn [instantiate_qualifier instantiate_pred qualifier_holds predicate_holds interpret_qualifier] in *;
    repeat match goal with
    | IH : forall theta gamma, type_substitution_closed theta ->
        term_substitution_closed gamma -> related_substitution theta gamma _ -> _ |- _ =>
        specialize (IH theta gamma Htheta Hgamma Hrel)
    end; try tauto.
  - pose proof (Hrel x (R_Refine T p) H) as Hd.
  apply denotes_refine_iff in Hd. destruct Hd as [Hv [Ht Hp]].
  unfold open_qualifier_tm, open_qualifier_tm_rec.
  unfold qualifier_holds, instantiate_qualifier.
  rewrite (instantiate_pred_open_tm_commute p 0 (tm_fvar x) theta gamma
    Htheta Hgamma (lc_tm_fvar 0 0 x)).
  exact Hp.
  - apply H.
    + exact (substitution_values Hrel).
    + intros x T q0 Hlookup.
      pose proof (Hrel x (R_Refine T q0) Hlookup) as Hd.
      apply denotes_refine_iff in Hd. destruct Hd as [_ [_ Hp]].
      change (qualifier_holds (instantiate_qualifier theta gamma (open_qualifier_tm q0 (tm_fvar x)))).
      rewrite instantiate_qualifier_open_commute.
      * exact Hp.
      * exact Htheta.
      * exact Hgamma.
      * apply lc_tm_fvar.
    + exact Hholds.
Qed.

Scheme has_rtype_mut_ind := Induction for has_rtype Sort Prop
with subtype_mut_ind := Induction for subtype Sort Prop.

Combined Scheme refinement_typing_mutind
  from has_rtype_mut_ind, subtype_mut_ind.

Lemma multi_app_left : forall t1 t1' t2,
  multi t1 t1' -> locally_closed_tm t2 ->
  multi (tm_app t1 t2) (tm_app t1' t2).
Proof.
  intros t1 t1' t2 Hsteps Hlc. induction Hsteps.
  - apply multi_refl.
  - eapply multi_step.
    + apply ST_App1; eauto.
    + exact IHHsteps.
Qed.

Lemma multi_app_right : forall v1 t2 t2',
  value v1 -> multi t2 t2' ->
  multi (tm_app v1 t2) (tm_app v1 t2').
Proof.
  intros v1 t2 t2' Hv Hsteps. induction Hsteps.
  - apply multi_refl.
  - eapply multi_step.
    + apply ST_App2; eauto.
    + exact IHHsteps.
Qed.

Lemma multi_tapp : forall t t' U,
  multi t t' -> locally_closed_ty U ->
  multi (tm_tapp t U) (tm_tapp t' U).
Proof.
  intros t t' U Hsteps HU. induction Hsteps.
  - apply multi_refl.
  - eapply multi_step.
    + apply ST_TApp; eauto.
    + exact IHHsteps.
Qed.

Lemma multi_trans : forall t1 t2 t3,
  multi t1 t2 -> multi t2 t3 -> multi t1 t3.
Proof.
  intros t1 t2 t3 H12 H23. induction H12.
  - exact H23.
  - eapply multi_step; eauto.
Qed.

Lemma evals_denotes_intro : forall R t,
  locally_closed_tm t ->
  (value t \/ exists u, t --> u) ->
  (value t -> denotes R t) ->
  (forall u, t --> u -> evals_denotes R u) ->
  evals_denotes R t.
Proof.
  intros R t Hlc Hp Hv Hnext. split; [assumption |]. split.
  - constructor; [assumption |].
    intros u Hs. exact (proj1 (proj2 (Hnext u Hs))).
  - intros v Hm Hvalue. inversion Hm; subst.
    + apply Hv; assumption.
    + match goal with
      | Hs : t --> ?u, Hrest : multi ?u v |- _ =>
          exact (proj2 (proj2 (Hnext u Hs)) v Hrest Hvalue)
      end.
Qed.

Lemma evals_denotes_map : forall R S t,
  (forall v, denotes R v -> denotes S v) ->
  evals_denotes R t -> evals_denotes S t.
Proof.
  intros R S t Hmap [Hlc [Htotal Hall]].
  split; [assumption |]. split; [assumption |].
  intros v Hm Hv. apply Hmap. apply Hall; assumption.
Qed.

Lemma evals_denotes_reduct : forall R t u,
  evals_denotes R t -> t --> u -> evals_denotes R u.
Proof.
  intros R t u [Hlc [Htotal Hall]] Hs. split.
  - eapply step_preserves_lc; eauto.
  - split; [eapply must_terminate_step; eauto |].
    intros v Hm Hv. apply Hall; [eapply multi_step; eauto |assumption].
Qed.

Lemma evals_denotes_single : forall R t u,
  locally_closed_tm t ->
  t --> u ->
  (forall w, t --> w -> w = u) ->
  evals_denotes R u ->
  evals_denotes R t.
Proof.
  intros R t u Hlc Hs Hunique Hu. apply evals_denotes_intro.
  - exact Hlc.
  - right. eauto.
  - intros Hv. exfalso. eapply value_no_step; eauto.
  - intros w Hw. rewrite (Hunique w Hw). exact Hu.
Qed.

Lemma evals_denotes_bind : forall S R t (E : tm -> tm),
  evals_denotes S t ->
  (forall u, locally_closed_tm u -> locally_closed_tm (E u)) ->
  (forall u, ~ value (E u)) ->
  (forall u u', u --> u' -> E u --> E u') ->
  (forall u w, ~ value u -> E u --> w ->
    exists u', u --> u' /\ w = E u') ->
  (forall v, multi t v -> value v -> denotes S v -> evals_denotes R (E v)) ->
  evals_denotes R (E t).
Proof.
  intros S R t E [Hlc [Htotal Hall]] HElc HEnval HEstep HEinv.
  revert Hlc Hall.
  induction Htotal as [t Hp Hnext IH]; intros Hlc Hall Hcont.
  destruct Hp as [Hv | [u Hs]].
  - apply Hcont; [constructor |assumption |apply Hall; [constructor |assumption]].
  - apply evals_denotes_intro.
    + apply HElc; assumption.
    + right. exists (E u). apply HEstep; assumption.
    + intros Hv. exfalso. exact (HEnval t Hv).
    + intros w Hw.
      assert (Hnv : ~ value t) by (intro Hv; eapply value_no_step; eauto).
      destruct (HEinv t w Hnv Hw) as [u' [Hs' ->]].
      apply (IH u' Hs').
      * eapply step_preserves_lc; eauto.
      * intros v Hm Hv. apply Hall; [eapply multi_step; eauto |assumption].
      * intros v Hm Hv Hd. apply Hcont; [eapply multi_step; eauto |assumption |assumption].
Qed.

Lemma evals_denotes_app_exists : forall R1 R2 t1 t2,
  evals_denotes (R_Func R1 R2) t1 ->
  evals_denotes R1 t2 ->
  evals_denotes (R_Exists R1 R2) (tm_app t1 t2).
Proof.
  intros R1 R2 t1 t2 Hfun Harg.
  eapply evals_denotes_bind with (S := R_Func R1 R2) (E := fun u => tm_app u t2).
  - exact Hfun.
  - intros; apply lc_tm_app; [assumption |exact (proj1 Harg)].
  - intros u Hv; inversion Hv.
  - intros; apply ST_App1; [assumption |exact (proj1 Harg)].
  - intros u w Hnv Hs. inversion Hs; subst.
    + exfalso. apply Hnv. constructor; assumption.
    + eauto.
    + contradiction.
    + exfalso. apply Hnv. constructor; assumption.
  - intros f Htf Hvf Hdf.
    eapply evals_denotes_bind with (S := R1) (E := fun u => tm_app f u).
    + exact Harg.
    + intros; apply lc_tm_app; [apply value_regular; assumption |assumption].
    + intros u Hv; inversion Hv.
    + intros; apply ST_App2; assumption.
    + intros u w Hnv Hs. inversion Hs; subst.
      * contradiction.
      * exfalso. eapply value_no_step; eauto.
      * eauto.
      * contradiction.
    + intros arg Hta Hva Hda.
      apply denotes_func_iff in Hdf. destruct Hdf as [_ [_ Happ]].
      eapply evals_denotes_map; [|exact (Happ arg Hda)].
      intros result Hd. apply denotes_exists_iff.
      split; [eapply denotes_value; eauto |]. split.
      * pose proof (denotes_typing _ _ Hd) as Ht.
        rewrite erase_open_rty_tm in Ht. exact Ht.
      * exists arg. auto.
Qed.

Lemma evals_denotes_tapp : forall R t U,
  evals_denotes (R_Poly R) t -> wf_ty [] U ->
  evals_denotes (open_rty_ty R U) (tm_tapp t U).
Proof.
  intros R t U Ht HU.
  eapply evals_denotes_bind with (S := R_Poly R) (E := fun u => tm_tapp u U).
  - exact Ht.
  - intros; apply lc_tm_tapp; [assumption |eapply wf_ty_lc; eauto].
  - intros u Hv; inversion Hv.
  - intros; apply ST_TApp; [assumption |eapply wf_ty_lc; eauto].
  - intros u w Hnv Hs. inversion Hs; subst.
    + exfalso. apply Hnv. constructor; assumption.
    + eauto.
  - intros v Hm Hv Hd. apply denotes_poly_iff in Hd.
    destruct Hd as [_ [_ Happ]]. apply Happ; assumption.
Qed.

Lemma evals_denotes_choice : forall R t1 t2,
  evals_denotes R t1 -> evals_denotes R t2 ->
  evals_denotes R (tm_choice t1 t2).
Proof.
  intros R t1 t2 H1 H2. apply evals_denotes_intro.
  - apply lc_tm_choice; [exact (proj1 H1) |exact (proj1 H2)].
  - right. exists t1. apply ST_ChoiceLeft; [exact (proj1 H1) |exact (proj1 H2)].
  - intros Hv. inversion Hv.
  - intros u Hs. inversion Hs; subst; assumption.
Qed.

Lemma multi_div_left : forall t1 t1' t2,
  multi t1 t1' -> locally_closed_tm t2 ->
  multi (tm_div t1 t2) (tm_div t1' t2).
Proof.
  intros t1 t1' t2 H Hlc. induction H; eauto using multi, step.
Qed.

Lemma multi_div_right : forall v t2 t2',
  value v -> multi t2 t2' ->
  multi (tm_div v t2) (tm_div v t2').
Proof.
  intros v t2 t2' Hv H. induction H; eauto using multi, step.
Qed.

Lemma value_int_canonical : forall v,
  value v -> has_type [] empty v Ty_Int -> exists n, v = tm_int n.
Proof.
  intros v Hv Ht. inversion Hv; subst; inversion Ht; eauto.
Qed.

Lemma evals_denotes_div : forall t1 t2,
  evals_denotes (R_Refine Ty_Int Pred_True) t1 ->
  evals_denotes (R_Refine Ty_Int (Pred_Ne (tm_bvar 0) (tm_int 0%Z))) t2 ->
  evals_denotes (R_Refine Ty_Int (Pred_Eq (tm_bvar 0) (tm_div t1 t2))) (tm_div t1 t2).
Proof.
  intros t1 t2 H1 H2.
  eapply evals_denotes_bind with
    (S := R_Refine Ty_Int Pred_True) (E := fun u => tm_div u t2).
  - exact H1.
  - intros; apply lc_tm_div; [assumption |exact (proj1 H2)].
  - intros u Hv; inversion Hv.
  - intros; apply ST_Div1; [assumption |exact (proj1 H2)].
  - intros u w Hnv Hs. inversion Hs; subst; eauto;
      exfalso; apply Hnv; first [assumption |constructor].
  - intros v1 Hm1 Hv1 Hd1. apply denotes_refine_iff in Hd1.
    destruct Hd1 as [_ [Ht1 _]].
    destruct (value_int_canonical _ Hv1 Ht1) as [n ->].
    eapply evals_denotes_bind with
      (S := R_Refine Ty_Int (Pred_Ne (tm_bvar 0) (tm_int 0%Z)))
      (E := fun u => tm_div (tm_int n) u).
    + exact H2.
    + intros; apply lc_tm_div; [constructor |assumption].
    + intros u Hv; inversion Hv.
    + intros; apply ST_Div2; [constructor |assumption].
    + intros u w Hnv Hs. inversion Hs; subst; eauto;
        try match goal with Hs : step (tm_int _) _ |- _ => inversion Hs end;
        exfalso; apply Hnv; first [assumption |constructor].
    + intros v2 Hm2 Hv2 Hd2. apply denotes_refine_iff in Hd2.
      destruct Hd2 as [_ [Ht2 Hnz]].
      destruct (value_int_canonical _ Hv2 Ht2) as [m ->].
      assert (Em : m <> 0%Z).
      { intro E. subst m. apply Hnz.
        exists (tm_int 0%Z). repeat split; constructor. }
      eapply evals_denotes_single with (u := tm_int (Z.div n m)).
      * repeat constructor.
      * apply ST_DivInt; assumption.
      * intros w Hs. inversion Hs; subst; try reflexivity;
          match goal with Hs : step (tm_int _) _ |- _ => inversion Hs end.
      * apply evals_denotes_of_denotes. apply denotes_refine_iff.
        split; [constructor |]. split; [constructor |].
        unfold open_qualifier_tm, open_qualifier_tm_rec. simpl.
        rewrite (open_tm_rec_lc_at t1 0 0 (tm_int (Z.div n m)) (proj1 H1)),
          (open_tm_rec_lc_at t2 0 0 (tm_int (Z.div n m)) (proj1 H2)).
        exists (tm_int (Z.div n m)). split; [constructor |]. split; [|constructor].
        assert (Hm : multi (tm_div t1 t2) (tm_int (Z.div n m))).
        { eapply multi_trans; [apply multi_div_left; [exact Hm1 |exact (proj1 H2)] |].
          eapply multi_trans; [apply multi_div_right; eauto using value |].
          eapply multi_step; [apply ST_DivInt; assumption |constructor]. }
        induction Hm; eauto using predicate_multistep.
Qed.



Lemma multi_arith_left : forall op t1 t1' t2,
  multi t1 t1' -> locally_closed_tm t2 ->
  multi (tm_arith op t1 t2) (tm_arith op t1' t2).
Proof. intros op t1 t1' t2 H Hlc. induction H; eauto using multi, step. Qed.

Lemma multi_arith_right : forall op v t2 t2',
  value v -> multi t2 t2' ->
  multi (tm_arith op v t2) (tm_arith op v t2').
Proof. intros op v t2 t2' Hv H. induction H; eauto using multi, step. Qed.

Lemma evals_denotes_arith : forall op t1 t2,
  evals_denotes (R_Refine Ty_Int Pred_True) t1 ->
  evals_denotes (R_Refine Ty_Int Pred_True) t2 ->
  evals_denotes (R_Refine Ty_Int
    (Pred_Eq (tm_bvar 0) (tm_arith op t1 t2))) (tm_arith op t1 t2).
Proof.
  intros op t1 t2 H1 H2.
  eapply evals_denotes_bind with
    (S := R_Refine Ty_Int Pred_True) (E := fun u => tm_arith op u t2).
  - exact H1.
  - intros; apply lc_tm_arith; [assumption |exact (proj1 H2)].
  - intros u Hv; inversion Hv.
  - intros; apply ST_Arith1; [assumption |exact (proj1 H2)].
  - intros u w Hnv Hs. inversion Hs; subst; eauto;
      exfalso; apply Hnv; first [assumption |constructor].
  - intros v1 Hm1 Hv1 Hd1. apply denotes_refine_iff in Hd1.
    destruct Hd1 as [_ [Ht1 _]].
    destruct (value_int_canonical _ Hv1 Ht1) as [n ->].
    eapply evals_denotes_bind with
      (S := R_Refine Ty_Int Pred_True) (E := fun u => tm_arith op (tm_int n) u).
    + exact H2.
    + intros; apply lc_tm_arith; [constructor |assumption].
    + intros u Hv; inversion Hv.
    + intros; apply ST_Arith2; [constructor |assumption].
    + intros u w Hnv Hs. inversion Hs; subst; eauto;
        try match goal with Hs : step (tm_int _) _ |- _ => inversion Hs end;
        exfalso; apply Hnv; first [assumption |constructor].
    + intros v2 Hm2 Hv2 Hd2. apply denotes_refine_iff in Hd2.
      destruct Hd2 as [_ [Ht2 _]].
      destruct (value_int_canonical _ Hv2 Ht2) as [m ->].
      set (result := eval_integer_operator op n m).
      eapply evals_denotes_single with (u := tm_int result).
      * repeat constructor.
      * apply ST_ArithInt.
      * intros w Hs. inversion Hs; subst; try reflexivity;
          match goal with Hs : step (tm_int _) _ |- _ => inversion Hs end.
      * apply evals_denotes_of_denotes. apply denotes_refine_iff.
        split; [constructor |]. split; [constructor |].
        unfold open_qualifier_tm, open_qualifier_tm_rec. simpl.
        rewrite (open_tm_rec_lc_at t1 0 0 (tm_int result) (proj1 H1)),
          (open_tm_rec_lc_at t2 0 0 (tm_int result) (proj1 H2)).
        exists (tm_int result). split; [constructor |]. split; [|constructor].
        assert (Hm : multi (tm_arith op t1 t2) (tm_int result)).
        { eapply multi_trans; [apply multi_arith_left; [exact Hm1 |exact (proj1 H2)] |].
          eapply multi_trans; [apply multi_arith_right; eauto using value |].
          eapply multi_step; [apply ST_ArithInt |constructor]. }
        induction Hm; eauto using predicate_multistep.
Qed.



Lemma instantiated_refinement_typing_erases : forall Delta RGamma t R theta gamma,
  has_rtype Delta RGamma t R ->
  context_wf Delta (erase_context RGamma) ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  type_substitution_wf Delta [] theta ->
  related_substitution theta gamma RGamma ->
  has_type [] empty (instantiate theta gamma t)
    (erase (instantiate_rty theta gamma R)).
Proof.
  intros Delta RGamma t R theta gamma Htyped Hctx Htheta Hgamma
    HthetaWf Hrelated.
  pose proof (refinement_typing_erases _ _ _ _ Htyped) as Herased.
  pose proof (has_type_instantiate Delta (erase_context RGamma) t (erase R)
    Herased Hctx [] empty theta gamma Htheta Hgamma HthetaWf
    (related_substitution_typed theta gamma RGamma Hrelated)) as Hinst.
  rewrite erase_instantiate_rty. exact Hinst.
Qed.

(*
typing_semantics Delta RGamma t R
表示：
> 在类型变量环境 Delta 和程序变量环境 RGamma 下，程序 t 在语义上具有 refinement type R。
 *)
(* Semantic substitutions map program variables to values. *)

Definition typing_semantics
    (Delta : ty_context) (RGamma : rcontext) (t : tm) (R : rty) : Prop :=
  context_wf Delta (erase_context RGamma) ->
  forall theta gamma,
    type_substitution_closed theta ->
    term_substitution_closed gamma ->
    type_substitution_wf Delta [] theta ->
    related_substitution theta gamma RGamma ->
    evals_denotes (instantiate_rty theta gamma R)
      (instantiate theta gamma t).

Definition subtype_semantics
    (Delta : ty_context) (RGamma : rcontext) (R S : rty) : Prop :=
  wf_ty Delta (erase S) ->
  context_wf Delta (erase_context RGamma) ->
  forall theta gamma,
    type_substitution_closed theta ->
    term_substitution_closed gamma ->
    type_substitution_wf Delta [] theta ->
    related_substitution theta gamma RGamma ->
    forall v,
      denotes (instantiate_rty theta gamma R) v ->
      denotes (instantiate_rty theta gamma S) v.

Lemma predicate_multi_to_multi : forall t u,
  predicate_multistep t u -> multi t u.
Proof. intros t u H. induction H; eauto using multi. Qed.


Lemma nonnegative_metric_result : forall t,
  qualifier_holds (Pred_Ge t (tm_int 0%Z)) ->
  exists n : Z, predicate_multistep t (tm_int n) /\ (0 <= n)%Z.
Proof.
  intros t [z [n [Hz [Hn Hle]]]].
  assert (z = 0%Z).
  { pose proof (value_multi_eq _ _ (v_int 0) (predicate_multi_to_multi _ _ Hz)). congruence. }
  subst z. exists n. auto.
Qed.

Lemma measured_argument_metric : forall A p metric arg,
  denotes (measured_input A p metric) arg ->
  exists n : Z, predicate_multistep (open_tm metric arg) (tm_int n) /\ (0 <= n)%Z.
Proof.
  intros A p metric arg Hd.
  apply denotes_refine_iff in Hd. destruct Hd as [_ [_ [_ Hmetric]]].
  apply nonnegative_metric_result. exact Hmetric.
Qed.

Lemma smaller_argument_metric : forall A p metric current next n,
  locally_closed_tm current ->
  predicate_multistep current (tm_int n) ->
  denotes (smaller_input A p metric current) next ->
  denotes (measured_input A p metric) next /\
  exists m : Z,
    predicate_multistep (open_tm metric next) (tm_int m) /\
    (0 <= m)%Z /\ (m < n)%Z.
Proof.
  intros A p metric current next n Hlc Hcurrent Hd.
  apply denotes_refine_iff in Hd. destruct Hd as [Hv [Ht [Hp [Hge Hlt]]]].
  change (qualifier_holds
    (Pred_Lt (open_tm metric next) (open_tm_rec 0 next current))) in Hlt.
  rewrite (open_tm_rec_lc_at current 0 0 next Hlc) in Hlt.
  split.
  - apply denotes_refine_iff. repeat split; assumption.
  - destruct (nonnegative_metric_result _ Hge) as [m [Hm Hnonneg]].
    destruct Hlt as [a [b [Ha [Hb [Hab Hall]]]]].
    exists m. repeat split; try assumption. exact (Hall m n Hm Hcurrent).
Qed.


Lemma recursive_function_denotes : forall A B p metric body R2,
  has_type [] empty (tm_fix A B metric body) (Ty_Arrow A (erase R2)) ->
  (forall arg,
    denotes (measured_input A p metric) arg ->
    denotes (R_Func (smaller_input A p metric (open_tm metric arg)) R2)
      (tm_fix A B metric body) ->
    evals_denotes (open_rty_tm R2 arg)
      (open_fix_body body (tm_fix A B metric body) arg)) ->
  denotes (R_Func (measured_input A p metric) R2) (tm_fix A B metric body).
Proof.
  intros A B p metric body R2 Htyped Hbody.
  assert (Hfixlc : locally_closed_tm (tm_fix A B metric body)).
  { eapply typing_lc; eauto. }
  assert (Hmetriclc : lc_tm_at 0 1 metric).
  { inversion Hfixlc; assumption. }
  assert (Hfixv : value (tm_fix A B metric body)) by (constructor; assumption).
  assert (Hrun : forall n : Z, forall arg,
    denotes (measured_input A p metric) arg ->
    predicate_multistep (open_tm metric arg) (tm_int n) ->
    evals_denotes (open_rty_tm R2 arg) (tm_app (tm_fix A B metric body) arg)).
  { intro n. induction n as [n IH] using
      (well_founded_induction integer_decreases_wf).
    intros arg Harg Hmetric.
    assert (Hargv : value arg) by (eapply denotes_value; eauto).
    assert (Harglc : locally_closed_tm arg) by (apply value_regular; assumption).
    eapply evals_denotes_single.
    - apply lc_tm_app; assumption.
    - apply ST_AppFix; assumption.
    - intros w Hs. inversion Hs; subst; try reflexivity.
      + exfalso. eapply value_no_step; [exact Hfixv | exact H1].
      + exfalso. eapply value_no_step; [exact Hargv | eassumption].
    - apply Hbody; [assumption |].
      apply denotes_func_iff. split; [assumption |]. split; [exact Htyped |].
      intros next Hnext.
      assert (Hcurrentlc : locally_closed_tm (open_tm metric arg)).
      { apply open_tm_preserves_lc_at; assumption. }
      destruct (smaller_argument_metric _ _ _ _ _ _ Hcurrentlc Hmetric Hnext)
        as [Hnextbase [m [Hm [Hnonneg Hlt]]]].
      apply (IH m).
      + split; assumption.
      + exact Hnextbase.
      + exact Hm. }
  apply denotes_func_iff. split; [assumption |]. split; [exact Htyped |].
  intros arg Harg.
  destruct (measured_argument_metric _ _ _ _ Harg) as [m [Hm Hnonneg]].
  apply (Hrun m); assumption.
Qed.

Lemma instantiate_pred_update_irrelevant : forall p theta gamma x u,
  ~ In x (fv_pred p) ->
  instantiate_pred theta (term_subst_update gamma x u) p =
  instantiate_pred theta gamma p.
Proof.
  induction p; intros; simpl in *; try reflexivity;
    try solve [rewrite in_app_iff in H; f_equal;
      apply instantiate_term_update_irrelevant; intuition];
    try solve [rewrite in_app_iff in H; f_equal; [apply IHp1 | apply IHp2]; intuition].
  f_equal. apply IHp. assumption.
Qed.

Lemma instantiate_smaller_input : forall A p metric theta gamma x arg,
  ~ In x (fv_pred p) -> ~ In x (fv_tm metric) ->
  type_substitution_closed theta -> term_substitution_closed gamma ->
  locally_closed_tm arg ->
  instantiate_rty theta (term_subst_update gamma x arg)
    (smaller_input A p metric (open_tm metric (tm_fvar x))) =
  smaller_input (instantiate_ty theta A) (instantiate_pred theta gamma p)
    (instantiate theta gamma metric) (open_tm (instantiate theta gamma metric) arg).
Proof.
  intros A p metric theta gamma x arg Hp Hmetric Htheta Hgamma Harg.
  unfold smaller_input. cbn [instantiate_rty instantiate_qualifier instantiate_pred Pred_Ge].
  rewrite instantiate_pred_update_irrelevant by assumption.
  rewrite (instantiate_term_update_irrelevant metric theta gamma x arg Hmetric).
  rewrite instantiate_open_tm by assumption. reflexivity.
Qed.

Lemma fresh_open_pred : forall p k x y,
  x <> y -> ~ In x (fv_pred p) ->
  ~ In x (fv_pred (open_pred_tm_rec k (tm_fvar y) p)).
Proof.
  induction p; intros k x y Hneq Hfresh; simpl in *; try tauto;
    repeat rewrite in_app_iff in *;
    try solve [intro Hin; destruct Hin; apply fv_open_tm_rec in H;
      simpl in H; intuition];
    try solve [intuition eauto].
Qed.

Lemma fresh_open_rty : forall R k x y,
  x <> y -> ~ In x (fv_rty R) ->
  ~ In x (fv_rty (open_rty_tm_rec k (tm_fvar y) R)).
Proof.
  induction R; intros k x y Hneq Hfresh; simpl in *.
  - apply fresh_open_pred; assumption.
  - rewrite in_app_iff in *. intuition eauto.
  - rewrite in_app_iff in *. intuition eauto.
  - eauto.
Qed.

Lemma related_substitution_strengthen : forall theta gamma RGamma x T p q,
  related_substitution theta gamma RGamma ->
  lookup_rcontext x RGamma = Some (R_Refine T p) ->
  qualifier_holds (open_qualifier_tm (instantiate_qualifier theta gamma q) (gamma x)) ->
  related_substitution theta gamma (update_rcontext RGamma x (R_Refine T q)).
Proof.
  intros theta gamma RGamma x T p q Hrel Hx Hq.
  constructor; [exact (substitution_values Hrel) |].
  intros y R Hy. simpl in Hy. destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst y. inversion Hy; subst R.
    pose proof (Hrel x (R_Refine T p) Hx) as Hd.
    apply denotes_refine_iff in Hd. destruct Hd as [Hv [Ht Hp]].
    apply denotes_refine_iff. auto.
  - apply Hrel. exact Hy.
Qed.

Theorem fundamental_and_subtyping :
  (forall Delta RGamma t R (H : has_rtype Delta RGamma t R),
    typing_semantics Delta RGamma t R) /\
  (forall Delta RGamma R S (H : subtype Delta RGamma R S),
    subtype_semantics Delta RGamma R S).
Proof.
  apply refinement_typing_mutind;
    unfold typing_semantics, subtype_semantics.
  - intros Delta RGamma x R Hlookup Hwf Hctx theta gamma Htheta Hgamma
      HthetaWf Hrelated. simpl.
    apply evals_denotes_of_denotes. exact (Hrelated x R Hlookup).
  - intros L Delta RGamma R1 body R2 Hwf Hbody IHbody Hctx
      theta gamma Htheta Hgamma HthetaWf Hrelated.
    assert (Hwhole : has_rtype Delta RGamma
      (tm_abs (erase R1) body) (R_Func R1 R2)).
    { apply RT_Abs with L; assumption. }
    pose proof (instantiated_refinement_typing_erases _ _ _ _ _ _ Hwhole
      Hctx Htheta Hgamma HthetaWf Hrelated) as Htyped.
    assert (Hvalue : value (instantiate theta gamma (tm_abs (erase R1) body))).
    { apply v_abs. eapply typing_lc. exact Htyped. }
    apply evals_denotes_of_denotes.
    apply (proj2 (denotes_func_iff _ _ _)).
    split; [exact Hvalue |]. split; [exact Htyped |].
    intros arg Harg.
    assert (Harglc : locally_closed_tm arg).
    { apply value_regular. eapply denotes_value. exact Harg. }
    set (x := fresh (L ++ fv_tm body ++ fv_rty R1 ++ fv_rty R2 ++
      fv_rcontext RGamma)).
    assert (Hxall : ~ In x (L ++ fv_tm body ++ fv_rty R1 ++ fv_rty R2 ++
      fv_rcontext RGamma)) by (subst x; apply fresh_notin).
    repeat rewrite in_app_iff in Hxall.
    assert (Hctx' : context_wf Delta
      (erase_context (update_rcontext RGamma x R1))).
    { simpl. apply context_wf_update; [exact Hctx |].
      eapply wf_rty_erases. exact Hwf. }
    pose proof (IHbody x ltac:(tauto) Hctx' theta
      (term_subst_update gamma x arg) Htheta
      (term_subst_update_closed gamma x arg Hgamma Harglc) HthetaWf
      (related_substitution_update theta gamma RGamma x R1 arg Hrelated Harg
        ltac:(tauto) ltac:(tauto))) as Hresult.
    rewrite (instantiate_open_tm body theta gamma x arg) in Hresult;
      try tauto.
    rewrite (instantiate_rty_open_tm R2 theta gamma x arg) in Hresult;
      try tauto.
    apply evals_denotes_intro.
    + apply lc_tm_app.
      * apply value_regular. exact Hvalue.
      * exact Harglc.
    + right. eexists. apply ST_AppAbs.
      * exact (value_regular _ Hvalue).
      * eapply denotes_value. exact Harg.
    + intros HappValue. inversion HappValue.
    + intros u Hstep. inversion Hstep; subst.
      * exact Hresult.
      * match goal with Hs : tm_abs _ _ --> _ |- _ => inversion Hs end.
      * exfalso. eapply value_no_step.
        -- eapply denotes_value. exact Harg.
        -- eassumption.
  - intros Delta RGamma t1 t2 R1 R2 Ht1 IHt1 Ht2 IHt2 Hctx
      theta gamma Htheta Hgamma HthetaWf Hrelated.
    pose proof (IHt1 Hctx theta gamma Htheta Hgamma HthetaWf Hrelated) as Hfun.
    pose proof (IHt2 Hctx theta gamma Htheta Hgamma HthetaWf Hrelated) as Harg.
    eapply evals_denotes_app_exists; eauto.
  - intros L Delta RGamma body R Hbody IHbody Hctx theta gamma
      Htheta Hgamma HthetaWf Hrelated.
    assert (Hwhole : has_rtype Delta RGamma (tm_tabs body) (R_Poly R)).
    { apply RT_TAbs with L. exact Hbody. }
    pose proof (instantiated_refinement_typing_erases _ _ _ _ _ _ Hwhole
      Hctx Htheta Hgamma HthetaWf Hrelated) as Htyped.
    assert (Hvalue : value (instantiate theta gamma (tm_tabs body))).
    { apply v_tabs. eapply typing_lc. exact Htyped. }
    apply evals_denotes_of_denotes.
    apply (proj2 (denotes_poly_iff _ _)).
    split; [exact Hvalue |]. split; [exact Htyped |].
    intros U HU.
    set (X := fresh (L ++ ftv_tm body ++ ftv_rty R ++ ftv_rcontext RGamma)).
    assert (HXall : ~ In X
      (L ++ ftv_tm body ++ ftv_rty R ++ ftv_rcontext RGamma))
      by (subst X; apply fresh_notin).
    repeat rewrite in_app_iff in HXall.
    assert (Hctx' : context_wf (X :: Delta) (erase_context RGamma)).
    { eapply context_wf_weaken_type; [exact Hctx |].
      unfold ty_context_included. simpl. auto. }
    assert (Htheta' : type_substitution_closed
      (type_subst_update theta X U)).
    { apply type_subst_update_closed; [exact Htheta |].
      eapply wf_ty_lc. exact HU. }
    assert (HthetaWf' : type_substitution_wf (X :: Delta) []
      (type_subst_update theta X U)).
    { intros Y HY. simpl in HY. destruct HY as [HY | HY].
      - subst Y. unfold type_subst_update. rewrite Nat.eqb_refl. exact HU.
      - unfold type_subst_update.
        destruct (Nat.eqb X Y) eqn:E.
        + exact HU.
        + apply HthetaWf. exact HY. }
    pose proof (IHbody X ltac:(tauto) Hctx'
      (type_subst_update theta X U) gamma Htheta' Hgamma HthetaWf'
      (related_substitution_type_update theta gamma RGamma X U Hrelated
        ltac:(tauto))) as Hresult.
    rewrite (instantiate_open_ty body theta gamma X U) in Hresult;
      try tauto; try (eapply wf_ty_lc; exact HU).
    rewrite (instantiate_rty_open_ty R theta gamma X U) in Hresult;
      try tauto; try (eapply wf_ty_lc; exact HU).
    apply evals_denotes_intro.
    + apply lc_tm_tapp.
      * apply value_regular. exact Hvalue.
      * eapply wf_ty_lc. exact HU.
    + right. eexists. apply ST_TAppTabs.
      * exact (value_regular _ Hvalue).
      * eapply wf_ty_lc. exact HU.
    + intros HtappValue. inversion HtappValue.
    + intros u Hstep. inversion Hstep; subst.
      * exact Hresult.
      * match goal with Hs : tm_tabs _ --> _ |- _ => inversion Hs end.
  - intros Delta RGamma t R U Ht IHt HU Hctx theta gamma Htheta Hgamma
      HthetaWf Hrelated.
    pose proof (IHt Hctx theta gamma Htheta Hgamma HthetaWf Hrelated) as Hpoly.
    assert (HUinst : wf_ty [] (instantiate_ty theta U)).
    { eapply wf_ty_instantiate; eauto. }
    pose proof (evals_denotes_tapp _ _ _ Hpoly HUinst) as Hresult.
    assert (Heq :
      instantiate_rty theta gamma (open_rty_ty R U) =
      open_rty_ty (instantiate_rty theta gamma R) (instantiate_ty theta U)).
    { apply instantiate_rty_open_ty_commute_top; try assumption.
      eapply wf_ty_lc. exact HU. }
    rewrite Heq. exact Hresult.
  - intros Delta RGamma n Hctx theta gamma Htheta Hgamma HthetaWf Hrelated.
    apply evals_denotes_of_denotes. apply denotes_refine_iff.
    split; [constructor|]. split; [constructor|].
    exists (tm_int n). repeat split; constructor.
  - intros Delta RGamma t1 t2 Ht1 IHt1 Ht2 IHt2 Hctx theta gamma
      Htheta Hgamma HthetaWf Hrelated.
    apply evals_denotes_div.
    + exact (IHt1 Hctx theta gamma Htheta Hgamma HthetaWf Hrelated).
    + exact (IHt2 Hctx theta gamma Htheta Hgamma HthetaWf Hrelated).
  - intros Delta RGamma op t1 t2 Ht1 IHt1 Ht2 IHt2 Hctx theta gamma
      Htheta Hgamma HthetaWf Hrelated.
    apply evals_denotes_arith.
    + exact (IHt1 Hctx theta gamma Htheta Hgamma HthetaWf Hrelated).
    + exact (IHt2 Hctx theta gamma Htheta Hgamma HthetaWf Hrelated).
  - intros Delta RGamma t1 t2 R Ht1 IHt1 Ht2 IHt2 Hctx theta gamma
      Htheta Hgamma HthetaWf Hrelated.
    apply evals_denotes_choice.
    + exact (IHt1 Hctx theta gamma Htheta Hgamma HthetaWf Hrelated).
    + exact (IHt2 Hctx theta gamma Htheta Hgamma HthetaWf Hrelated).
  - intros Delta RGamma v T ps Htyped Hv Hwf Hclosed Hpred Hctx theta gamma
      Htheta Hgamma HthetaWf Hrelated.
    assert (Hinst_value : value (instantiate theta gamma v)).
    { eapply instantiate_value; eauto. }
    apply evals_denotes_of_denotes.
    apply (proj2 (denotes_refine_iff _ _ _)).
    split; [exact Hinst_value |]. split.
    + eapply has_type_instantiate; eauto.
      exact (related_substitution_typed theta gamma RGamma Hrelated).
    + pose proof (instantiate_qualifier_holds _ theta gamma Hclosed Hpred Htheta Hgamma)
        as Hpred'.
      assert (Heq : instantiate_qualifier theta gamma (open_qualifier_tm ps v) =
        open_qualifier_tm (instantiate_qualifier theta gamma ps)
          (instantiate theta gamma v)).
      { apply instantiate_qualifier_open_commute; try assumption.
        apply value_regular. exact Hv. }
      rewrite Heq in Hpred'.
      exact Hpred'.
  - intros L Delta RGamma A p metric body R2 Hwf Hmetric Hbody IHbody Hctx
      theta gamma Htheta Hgamma HthetaWf Hrelated.
    assert (Hwhole : has_rtype Delta RGamma (tm_fix A (erase R2) metric body)
      (R_Func (measured_input A p metric) R2)).
    { apply RT_Fix with L; assumption. }
    pose proof (instantiated_refinement_typing_erases _ _ _ _ _ _ Hwhole
      Hctx Htheta Hgamma HthetaWf Hrelated) as Htyped.
    set (vf := instantiate theta gamma (tm_fix A (erase R2) metric body)).
    assert (Hvflc : locally_closed_tm vf) by (eapply typing_lc; exact Htyped).
    assert (HAv : wf_ty Delta A).
    { pose proof (wf_rty_erases _ _ _ Hwf) as H. inversion H; assumption. }
    assert (HBv : wf_ty Delta (erase R2)).
    { pose proof (wf_rty_erases _ _ _ Hwf) as H. inversion H; assumption. }
    apply evals_denotes_of_denotes.
    apply (recursive_function_denotes (instantiate_ty theta A)
      (instantiate_ty theta (erase R2)) (instantiate_pred theta gamma p)
      (instantiate theta gamma metric) (instantiate theta gamma body)
      (instantiate_rty theta gamma R2)).
    + exact Htyped.
    + intros arg Harg Hrec.
      assert (Harglc : locally_closed_tm arg) by
        (apply value_regular; eapply denotes_value; exact Harg).
      set (all := L ++ fv_tm body ++ fv_tm metric ++ fv_pred p ++
        fv_rty R2 ++ fv_rcontext RGamma).
      set (x := fresh all).
      set (f := fresh (x :: all)).
      assert (Hxall : ~ In x all) by apply fresh_notin.
      assert (Hfall : ~ In f (x :: all)) by apply fresh_notin.
      unfold all in Hxall, Hfall. simpl in Hfall.
      repeat rewrite in_app_iff in Hxall, Hfall.
      assert (Hfx : f <> x) by intuition congruence.
      assert (Hfreshopen : ~ In f (fv_tm (open_tm metric (tm_fvar x)))).
      { intro Hin. apply fv_open_tm_rec in Hin. simpl in Hin. intuition congruence. }
      set (Rin := measured_input A p metric).
      set (Rrec := R_Func (smaller_input A p metric (open_tm metric (tm_fvar x))) R2).
      assert (Hfreshrec : ~ In f (fv_rty Rrec)).
      { unfold Rrec, smaller_input. simpl.
        repeat rewrite in_app_iff. simpl. tauto. }
      assert (Hfreshctx : ~ In f (fv_rcontext (update_rcontext RGamma x Rin))).
      { unfold Rin, measured_input. simpl. repeat rewrite in_app_iff. simpl. tauto. }
      assert (Hrelx : related_substitution theta (term_subst_update gamma x arg)
        (update_rcontext RGamma x Rin)).
      { apply related_substitution_update; try assumption.
        - unfold Rin, measured_input. simpl. repeat rewrite in_app_iff. simpl. tauto.
        - tauto. }
      assert (Hrecx : denotes
        (instantiate_rty theta (term_subst_update gamma x arg) Rrec) vf).
      { unfold Rrec. cbn [instantiate_rty].
        rewrite instantiate_smaller_input; try tauto.
        rewrite instantiate_rty_term_update_irrelevant by tauto.
        exact Hrec. }
      assert (Hrelxf : related_substitution theta
        (term_subst_update (term_subst_update gamma x arg) f vf)
        (update_rcontext (update_rcontext RGamma x Rin) f Rrec)).
      { apply related_substitution_update; assumption. }
      assert (Hctxxf : context_wf Delta
        (erase_context (update_rcontext (update_rcontext RGamma x Rin) f Rrec))).
      { simpl. apply context_wf_update.
        - apply context_wf_update; assumption.
        - apply WF_Arrow; assumption. }
      pose proof (IHbody f x ltac:(tauto) ltac:(simpl; intuition congruence)
        Hctxxf theta (term_subst_update (term_subst_update gamma x arg) f vf)
        Htheta
        (term_subst_update_closed _ f vf
          (term_subst_update_closed gamma x arg Hgamma Harglc) Hvflc)
        HthetaWf Hrelxf) as Hresult.
      rewrite instantiate_open_fix_body in Hresult; try tauto.
      rewrite (instantiate_rty_term_update_irrelevant
        (open_rty_tm R2 (tm_fvar x)) theta (term_subst_update gamma x arg) f vf) in Hresult.
      * rewrite instantiate_rty_open_tm in Hresult; try tauto.
      * apply fresh_open_rty; tauto.
  - intros Delta RGamma x p t0 t1 R Hlookup Ht0 IHt0 Ht1 IHt1 Hctx
      theta gamma Htheta Hgamma HthetaWf Hrelated.
    assert (Hwhole : has_rtype Delta RGamma (tm_ifzero (tm_fvar x) t0 t1) R).
    { eapply RT_IfZero; eauto. }
    pose proof (instantiated_refinement_typing_erases _ _ _ _ _ _ Hwhole
      Hctx Htheta Hgamma HthetaWf Hrelated) as Htyped.
    pose proof (typing_lc _ _ _ _ Htyped) as Hlc.
    pose proof (Hrelated x (R_Refine Ty_Int p) Hlookup) as Hd.
    apply denotes_refine_iff in Hd. destruct Hd as [Hv [Ht Hp]].
    destruct (value_int_canonical _ Hv Ht) as [n Hn].
    assert (Hctx' : forall q, context_wf Delta
      (erase_context (update_rcontext RGamma x (R_Refine Ty_Int q)))).
    { intro q. simpl. apply context_wf_update; [assumption | constructor]. }
    simpl in Hlc |- *. rewrite Hn in Hlc |- *.
    inversion Hlc; subst.
    destruct (Z.eq_dec n 0) as [En | En].
    + subst n. eapply evals_denotes_single; [exact Hlc | apply ST_IfZero; assumption | |].
      * intros w Hs. inversion Hs; subst; try reflexivity; try congruence;
          match goal with Hs : step (tm_int _) _ |- _ => inversion Hs end.
      *
      apply IHt0; try assumption; [apply Hctx' |].
      eapply related_substitution_strengthen; [exact Hrelated | exact Hlookup |].
      change (qualifier_holds (open_qualifier_tm (instantiate_qualifier theta gamma p) (gamma x)) /\
        qualifier_holds (Pred_Eq (gamma x) (tm_int 0%Z))).
      split; [exact Hp |]. rewrite Hn. exists (tm_int 0%Z). repeat split; constructor.
    + eapply evals_denotes_single; [exact Hlc | apply ST_IfNonzero; assumption | |].
      * intros w Hs. inversion Hs; subst; try reflexivity; try congruence;
          match goal with Hs : step (tm_int _) _ |- _ => inversion Hs end.
      *
      apply IHt1; try assumption; [apply Hctx' |].
      eapply related_substitution_strengthen; [exact Hrelated | exact Hlookup |].
      change (qualifier_holds (open_qualifier_tm (instantiate_qualifier theta gamma p) (gamma x)) /\
        ~ qualifier_holds (Pred_Eq (gamma x) (tm_int 0%Z))).
      split; [exact Hp |]. rewrite Hn.
      intros [v [Hnv [H0v Hvv]]].
      pose proof (value_multi_eq _ _ (v_int n) (predicate_multi_to_multi _ _ Hnv)) as E1.
      pose proof (value_multi_eq _ _ (v_int 0) (predicate_multi_to_multi _ _ H0v)) as E2.
      congruence.
  - intros Delta RGamma t R S Ht IHt Hwf Hsub IHsub Hctx theta gamma
      Htheta Hgamma HthetaWf Hrelated.
    pose proof (IHt Hctx theta gamma Htheta Hgamma HthetaWf Hrelated) as Hresult.
    eapply evals_denotes_map; [|exact Hresult].
    intros v Hden.
    apply (IHsub (wf_rty_erases _ _ _ Hwf) Hctx theta gamma Htheta Hgamma
      HthetaWf Hrelated v Hden).
  - intros Delta RGamma R Hwf Hctx theta gamma Htheta Hgamma HthetaWf
      Hrelated v Hden. exact Hden.
  - intros L Delta RGamma T ps qs Hentails Hwf Hctx theta gamma Htheta
      Hgamma HthetaWf Hrelated v Hden.
    apply (proj1 (denotes_refine_iff _ _ _)) in Hden.
    destruct Hden as [Hv [Htyped Hps]].
    set (x := fresh (L ++ fv_qualifier ps ++ fv_qualifier qs ++ fv_rcontext RGamma)).
    assert (Hxall : ~ In x (L ++ fv_qualifier ps ++ fv_qualifier qs ++ fv_rcontext RGamma))
      by (subst x; apply fresh_notin).
    repeat rewrite in_app_iff in Hxall.
    pose proof (entails_sound _ _ _ _ (Hentails x ltac:(tauto)) theta
      (term_subst_update gamma x v)) as Hsound.
    assert (Hvlc : locally_closed_tm v) by (apply value_regular; exact Hv).
    assert (Hgamma' : term_substitution_closed (term_subst_update gamma x v)).
    { apply term_subst_update_closed; assumption. }
    assert (Hps_eq :
      instantiate_qualifier theta (term_subst_update gamma x v)
        (open_qualifier_tm ps (tm_fvar x)) =
      open_qualifier_tm (instantiate_qualifier theta gamma ps) v).
    { unfold open_qualifier_tm. apply instantiate_qualifier_open_tm_rec; tauto. }
    assert (Hqs_eq :
      instantiate_qualifier theta (term_subst_update gamma x v)
        (open_qualifier_tm qs (tm_fvar x)) =
      open_qualifier_tm (instantiate_qualifier theta gamma qs) v).
    { unfold open_qualifier_tm. apply instantiate_qualifier_open_tm_rec; tauto. }
    apply (proj2 (denotes_refine_iff _ _ _)).
    split; [exact Hv |]. split; [exact Htyped |].
    rewrite <- Hqs_eq. apply Hsound; try assumption.
    + apply related_substitution_update; try assumption.
      * apply denotes_refine_iff. split; [exact Hv|]. split; [exact Htyped|exact I].
      * simpl. tauto.
      * tauto.
    + rewrite Hps_eq. exact Hps.
  - intros L Delta RGamma R1 R2 S1 S2 Hdomain IHdomain Hcodomain IHcodomain
      Hwf Hctx theta gamma Htheta Hgamma HthetaWf Hrelated v Hden.
    apply (proj1 (denotes_func_iff _ _ _)) in Hden.
    destruct Hden as [Hv [Htyped Hmap]].
    assert (HwfS1 : wf_ty Delta (erase S1)).
    { simpl in Hwf. inversion Hwf. assumption. }
    assert (HwfS2 : wf_ty Delta (erase S2)).
    { simpl in Hwf. inversion Hwf. assumption. }
    apply (proj2 (denotes_func_iff _ _ _)).
    split; [exact Hv |]. split.
    + pose proof (subtype_erases _ _ _ _
        (S_Func L Delta RGamma R1 R2 S1 S2 Hdomain Hcodomain)) as Herase.
      simpl in Htyped |- *.
      rewrite !erase_instantiate_rty in Htyped |- *.
      simpl in Herase. injection Herase as E1 E2.
      rewrite <- E1, <- E2. exact Htyped.
    + intros arg HargS1.
      assert (HwfR1 : wf_ty Delta (erase R1)).
      { pose proof (subtype_erases _ _ _ _ Hdomain) as E.
        rewrite <- E. exact HwfS1. }
      pose proof (IHdomain HwfR1 Hctx theta gamma Htheta Hgamma HthetaWf
        Hrelated arg HargS1) as HargR1.
      pose proof (Hmap arg HargR1) as Hresult.
      set (x := fresh (L ++ fv_rty R1 ++ fv_rty R2 ++ fv_rty S1 ++
        fv_rty S2 ++ fv_rcontext RGamma)).
      assert (Hxall : ~ In x
        (L ++ fv_rty R1 ++ fv_rty R2 ++ fv_rty S1 ++ fv_rty S2 ++
          fv_rcontext RGamma)) by (subst x; apply fresh_notin).
      repeat rewrite in_app_iff in Hxall.
      assert (Harglc : locally_closed_tm arg).
      { apply value_regular. eapply denotes_value. exact HargS1. }
      assert (Hctx' : context_wf Delta
        (erase_context (update_rcontext RGamma x S1))).
      { simpl. apply context_wf_update; assumption. }
      assert (HwfOpenS2 : wf_ty Delta
        (erase (open_rty_tm S2 (tm_fvar x)))).
      { rewrite erase_open_rty_tm. exact HwfS2. }
      assert (HR2eq :
        instantiate_rty theta (term_subst_update gamma x arg)
          (open_rty_tm R2 (tm_fvar x)) =
        open_rty_tm (instantiate_rty theta gamma R2) arg).
      { apply instantiate_rty_open_tm; tauto. }
      assert (HS2eq :
        instantiate_rty theta (term_subst_update gamma x arg)
          (open_rty_tm S2 (tm_fvar x)) =
        open_rty_tm (instantiate_rty theta gamma S2) arg).
      { apply instantiate_rty_open_tm; tauto. }
      eapply evals_denotes_map; [|exact Hresult].
      intros result Hresult_denotes.
      pose proof (IHcodomain x ltac:(tauto) HwfOpenS2 Hctx' theta
        (term_subst_update gamma x arg) Htheta
        (term_subst_update_closed gamma x arg Hgamma Harglc) HthetaWf
        (related_substitution_update theta gamma RGamma x S1 arg Hrelated
          HargS1 ltac:(tauto) ltac:(tauto)) result) as Hconvert.
      rewrite HR2eq, HS2eq in Hconvert.
      apply Hconvert. exact Hresult_denotes.
  - intros Delta RGamma witness R1 R2 S Hwitness Htyping IHtyping Hsub IHsub
      Hwf Hctx theta gamma Htheta Hgamma HthetaWf Hrelated v HdenS.
    pose proof (IHtyping Hctx theta gamma Htheta Hgamma HthetaWf Hrelated)
      as Hwit_eval.
    assert (Hwit_value : value (instantiate theta gamma witness)).
    { eapply instantiate_value; eauto. }
    pose proof (evals_denotes_from_value _ _ Hwit_value Hwit_eval) as Hwit_den.
    assert (HwfOpen : wf_ty Delta (erase (open_rty_tm R2 witness))).
    { rewrite erase_open_rty_tm. simpl in Hwf. exact Hwf. }
    pose proof (IHsub HwfOpen Hctx theta gamma Htheta Hgamma HthetaWf Hrelated
      v HdenS) as Hbody_den.
    assert (Hopen_eq :
      instantiate_rty theta gamma (open_rty_tm R2 witness) =
      open_rty_tm (instantiate_rty theta gamma R2)
        (instantiate theta gamma witness)).
    { apply instantiate_rty_open_tm_commute_top; try assumption.
      apply value_regular. exact Hwitness. }
    rewrite Hopen_eq in Hbody_den.
    apply (proj2 (denotes_exists_iff _ _ _)).
    split.
    + eapply denotes_value. exact HdenS.
    + split.
      * pose proof (denotes_typing _ _ HdenS) as Htyped.
        pose proof (subtype_erases _ _ _ _
          (S_Witness Delta RGamma witness R1 R2 S Hwitness Htyping Hsub))
          as Herase.
        change (has_type [] empty v
          (erase (instantiate_rty theta gamma (R_Exists R1 R2)))).
        rewrite erase_instantiate_rty.
        rewrite <- Herase.
        rewrite erase_instantiate_rty in Htyped. exact Htyped.
      * exists (instantiate theta gamma witness). split; assumption.
  - intros L Delta RGamma R1 R2 S HwfR1 HlcS Hsub IHsub HwfS Hctx
      theta gamma Htheta Hgamma HthetaWf Hrelated v Hden.
    apply (proj1 (denotes_exists_iff _ _ _)) in Hden.
    destruct Hden as [Hv [Htyped [witness [Hwitness Hbody]]]].
    set (x := fresh (L ++ fv_rty R1 ++ fv_rty R2 ++ fv_rty S ++
      fv_rcontext RGamma)).
    assert (Hxall : ~ In x
      (L ++ fv_rty R1 ++ fv_rty R2 ++ fv_rty S ++ fv_rcontext RGamma))
      by (subst x; apply fresh_notin).
    repeat rewrite in_app_iff in Hxall.
    assert (Hwitness_lc : locally_closed_tm witness).
    { apply value_regular. eapply denotes_value. exact Hwitness. }
    assert (Hctx' : context_wf Delta
      (erase_context (update_rcontext RGamma x R1))).
    { simpl. apply context_wf_update; [exact Hctx |].
      eapply wf_rty_erases. exact HwfR1. }
    assert (HwfS' : wf_ty Delta (erase S)) by exact HwfS.
    pose proof (IHsub x ltac:(tauto) HwfS' Hctx' theta
      (term_subst_update gamma x witness) Htheta
      (term_subst_update_closed gamma x witness Hgamma Hwitness_lc) HthetaWf
      (related_substitution_update theta gamma RGamma x R1 witness Hrelated
        Hwitness ltac:(tauto) ltac:(tauto)) v) as Hconvert.
    assert (Hsource_eq :
      instantiate_rty theta (term_subst_update gamma x witness)
        (open_rty_tm R2 (tm_fvar x)) =
      open_rty_tm (instantiate_rty theta gamma R2) witness).
    { apply instantiate_rty_open_tm; tauto. }
    rewrite Hsource_eq in Hconvert.
    assert (Htarget_eq :
      instantiate_rty theta (term_subst_update gamma x witness) S =
      instantiate_rty theta gamma S).
    { apply instantiate_rty_term_update_irrelevant. tauto. }
    rewrite Htarget_eq in Hconvert. apply Hconvert. exact Hbody.
  - intros L Delta RGamma R S Hsub IHsub Hwf Hctx theta gamma Htheta Hgamma
      HthetaWf Hrelated v Hden.
    apply (proj1 (denotes_poly_iff _ _)) in Hden.
    destruct Hden as [Hv [Htyped Hmap]].
    apply (proj2 (denotes_poly_iff _ _)).
    split; [exact Hv |]. split.
    + pose proof (subtype_erases _ _ _ _
        (S_Poly L Delta RGamma R S Hsub)) as Herase.
      simpl in Htyped |- *.
      rewrite !erase_instantiate_rty in Htyped |- *.
      simpl in Herase. injection Herase as E.
      rewrite <- E. exact Htyped.
    + intros U HU.
      pose proof (Hmap U HU) as Hresult.
      set (X := fresh (L ++ ftv_rty R ++ ftv_rty S ++ ftv_rcontext RGamma)).
      assert (HXall : ~ In X
        (L ++ ftv_rty R ++ ftv_rty S ++ ftv_rcontext RGamma))
        by (subst X; apply fresh_notin).
      repeat rewrite in_app_iff in HXall.
      assert (Hctx' : context_wf (X :: Delta) (erase_context RGamma)).
      { eapply context_wf_weaken_type; [exact Hctx |].
        unfold ty_context_included. simpl. auto. }
      assert (Htheta' : type_substitution_closed
        (type_subst_update theta X U)).
      { apply type_subst_update_closed; [exact Htheta |].
        eapply wf_ty_lc. exact HU. }
      assert (HthetaWf' : type_substitution_wf (X :: Delta) []
        (type_subst_update theta X U)).
      { intros Y HY. simpl in HY. destruct HY as [HY | HY].
        - subst Y. unfold type_subst_update. rewrite Nat.eqb_refl. exact HU.
        - unfold type_subst_update. destruct (Nat.eqb X Y); auto. }
      assert (HwfOpenS : wf_ty (X :: Delta)
        (erase (open_rty_ty S (Ty_FVar X)))).
      { rewrite erase_open_rty_ty.
        apply wf_ty_open_all.
        - eapply wf_ty_weaken; [exact Hwf |].
          unfold ty_context_included. simpl. auto.
        - apply WF_Var. simpl. auto. }
      assert (HR_eq :
        instantiate_rty (type_subst_update theta X U) gamma
          (open_rty_ty R (Ty_FVar X)) =
        open_rty_ty (instantiate_rty theta gamma R) U).
      { apply instantiate_rty_open_ty; try tauto.
        eapply wf_ty_lc. exact HU. }
      assert (HS_eq :
        instantiate_rty (type_subst_update theta X U) gamma
          (open_rty_ty S (Ty_FVar X)) =
        open_rty_ty (instantiate_rty theta gamma S) U).
      { apply instantiate_rty_open_ty; try tauto.
        eapply wf_ty_lc. exact HU. }
      eapply evals_denotes_map; [|exact Hresult].
      intros result Hresult_denotes.
      pose proof (IHsub X ltac:(tauto) HwfOpenS Hctx'
        (type_subst_update theta X U) gamma Htheta' Hgamma HthetaWf'
        (related_substitution_type_update theta gamma RGamma X U Hrelated
          ltac:(tauto)) result) as Hconvert.
      rewrite HR_eq, HS_eq in Hconvert.
      apply Hconvert. exact Hresult_denotes.
  - intros Delta RGamma R S U HRS IHRS HSU IHSU HwfU Hctx theta gamma
      Htheta Hgamma HthetaWf Hrelated v HdenR.
    assert (HwfS : wf_ty Delta (erase S)).
    { pose proof (subtype_erases _ _ _ _ HSU) as E.
      rewrite E. exact HwfU. }
    apply (IHSU HwfU Hctx theta gamma Htheta Hgamma HthetaWf Hrelated v).
    apply (IHRS HwfS Hctx theta gamma Htheta Hgamma HthetaWf Hrelated v).
    exact HdenR.
Qed.

Theorem fundamental : forall Delta RGamma t R,
  has_rtype Delta RGamma t R ->
  typing_semantics Delta RGamma t R.
Proof.
  intros Delta RGamma t R Htyping.
  exact ((proj1 fundamental_and_subtyping) Delta RGamma t R Htyping).
Qed.

Theorem subtyping_sound : forall Delta RGamma R S,
  subtype Delta RGamma R S ->
  subtype_semantics Delta RGamma R S.
Proof.
  intros Delta RGamma R S Hsub.
  exact ((proj2 fundamental_and_subtyping) Delta RGamma R S Hsub).
Qed.

Definition default_value_substitution : term_substitution := fun _ => tm_int 0%Z.

Theorem refinement_termination : forall t R,
  has_rtype [] empty_rcontext t R -> must_terminate t.
Proof.
  intros t R Htyped.
  assert (Hctx : context_wf [] (erase_context empty_rcontext)).
  { intros x T Hlookup. discriminate. }
  assert (Hgamma : term_substitution_closed default_value_substitution).
  { intro x. constructor. }
  assert (Htheta : type_substitution_wf [] [] identity_type_substitution).
  { intros X Hin. contradiction. }
  assert (Hrelated : related_substitution identity_type_substitution
    default_value_substitution empty_rcontext).
  { constructor.
    - intro x. constructor.
    - intros x S Hlookup. discriminate. }
  pose proof (fundamental _ _ _ _ Htyped Hctx
    identity_type_substitution default_value_substitution
    identity_type_substitution_closed Hgamma Htheta Hrelated) as Hsemantic.
  destruct Hsemantic as [_ [Hhalts _]].
  rewrite instantiate_no_free_terms in Hhalts.
  - exact Hhalts.
  - apply closed_typing_no_free_terms with ([] : ty_context) (erase R).
    exact (refinement_typing_erases [] empty_rcontext t R Htyped).
Qed.

End SystemFRefinementNonDeterminismRecursionSoundness.
