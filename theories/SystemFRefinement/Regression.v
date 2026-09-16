From Stdlib Require Import Arith.PeanoNat Lists.List ZArith.BinInt Lia.
From AutoProof.SystemFRefinement Require Import Syntax RefinementTyping Evaluation Safety.
Module SystemFRefinementRegression.
Import ListNotations SystemFRefinement SystemFRefinementTyping
  SystemFRefinementEvaluation SystemFRefinementSafety.

Example six_div_two : step (tm_div (tm_int 6%Z) (tm_int 2%Z)) (tm_int 3%Z).
Proof. apply ST_DivInt. discriminate. Qed.

Example negative_quotient :
  step (tm_div (tm_int (-7)%Z) (tm_int 3%Z)) (tm_int (-3)%Z).
Proof. apply ST_DivInt. discriminate. Qed.

Example zero_divisor_no_step : forall t,
  ~ step (tm_div (tm_int 6%Z) (tm_int 0%Z)) t.
Proof.
  intros t H. inversion H; subst;
    try match goal with Hs : step (tm_int _) _ |- _ => inversion Hs end;
    congruence.
Qed.

Example division_not_value : ~ value (tm_div (tm_int 6%Z) (tm_int 0%Z)).
Proof. intro H; inversion H. Qed.

Example erased_typing_allows_zero :
  has_type [] empty (tm_div (tm_int 6%Z) (tm_int 0%Z)) Ty_Int.
Proof. apply T_Div; apply T_Int. Qed.

Lemma integer_multistep : forall n t,
  predicate_multistep (tm_int n) t -> t = tm_int n.
Proof.
  intros n t H. inversion H; subst; try reflexivity.
  match goal with Hs : step (tm_int _) _ |- _ => inversion Hs end.
Qed.

Example six_div_two_refined :
  has_rtype [] empty_rcontext (tm_div (tm_int 6%Z) (tm_int 2%Z))
    (R_Refine Ty_Int Pred_True).
Proof.
  apply RT_Div.
  - apply RT_RefineValue.
    + apply T_Int.
    + apply v_int.
    + apply RWF_Refine with (L := []).
      * apply WF_Int.
      * intros. apply PWF_True.
    + exact I.
    + exact I.
  - apply RT_RefineValue.
    + apply T_Int.
    + apply v_int.
    + apply RWF_Refine with (L := []).
      * apply WF_Int.
      * intros x Hx. unfold qualifier_wf, open_qualifier_tm,
          open_qualifier_tm_rec, Pred_Ne. simpl.
        apply PWF_Not. apply PWF_Eq with Ty_Int.
        -- apply T_Var; [simpl; rewrite Nat.eqb_refl; reflexivity | apply WF_Int].
        -- apply T_Int.
    + simpl. repeat split; try reflexivity; apply lc_tm_int.
    + intros [v [H2 [H0 Hv]]].
      pose proof (integer_multistep _ _ H2).
      pose proof (integer_multistep _ _ H0). congruence.
Qed.

Example zero_fails_nonzero_qualifier :
  ~ qualifier_holds
      (open_qualifier_tm (Pred_Ne (tm_bvar 0) (tm_int 0%Z)) (tm_int 0%Z)).
Proof.
  intro H. apply H. exists (tm_int 0%Z).
  repeat split; constructor.
Qed.

Example open_division_body :
  open_tm (tm_div (tm_int 6%Z) (tm_bvar 0)) (tm_int 2%Z) =
  tm_div (tm_int 6%Z) (tm_int 2%Z).
Proof. reflexivity. Qed.

Example zero_divisor_not_refinement_typed : forall R,
  ~ has_rtype [] empty_rcontext (tm_div (tm_int 6%Z) (tm_int 0%Z)) R.
Proof.
  intros R Htyped.
  destruct (never_stuck _ _ R Htyped (multi_refl _)) as [Hv|[u Hu]].
  - exact (division_not_value Hv).
  - exact (zero_divisor_no_step u Hu).
Qed.

Example any_division_typable : forall (n m : Z),
  m <> 0%Z ->
  has_rtype [] empty_rcontext (tm_div (tm_int n) (tm_int m))
    (R_Refine Ty_Int Pred_True).
Proof.
  intros n m Hnz. apply RT_Div.
  - apply RT_RefineValue.
    + constructor.
    + constructor.
    + apply RWF_Refine with []; [constructor|intros; constructor].
    + exact I.
    + exact I.
  - apply RT_RefineValue.
    + constructor.
    + constructor.
    + apply RWF_Refine with []; [constructor|].
      intros x Hx. apply PWF_Not. apply PWF_Eq with Ty_Int.
      * apply T_Var; [simpl; rewrite Nat.eqb_refl; reflexivity|constructor].
      * constructor.
    + simpl. repeat split; try reflexivity; constructor.
    + intros [v [Hm [Hz Hv]]].
      pose proof (integer_multistep _ _ Hm).
      pose proof (integer_multistep _ _ Hz). congruence.
Qed.

Example division_function_typable :
  has_rtype [] empty_rcontext (tm_abs Ty_Int (tm_div (tm_int 6%Z) (tm_bvar 0)))
    (R_Func (R_Refine Ty_Int (Pred_Ne (tm_bvar 0) (tm_int 0%Z)))
      (R_Refine Ty_Int Pred_True)).
Proof.
  apply (RT_Abs [] [] empty_rcontext
    (R_Refine Ty_Int (Pred_Ne (tm_bvar 0) (tm_int 0%Z)))
    (tm_div (tm_int 6%Z) (tm_bvar 0)) (R_Refine Ty_Int Pred_True)).
  - apply RWF_Refine with []; [constructor|].
    intros x Hx. apply PWF_Not. apply PWF_Eq with Ty_Int.
    + apply T_Var; [simpl; rewrite Nat.eqb_refl; reflexivity|constructor].
    + constructor.
  - intros x Hx. apply RT_Div.
    + apply RT_RefineValue.
      * constructor.
      * constructor.
      * apply RWF_Refine with []; [constructor|intros; constructor].
      * exact I.
      * exact I.
    + apply RT_Var.
      * simpl. rewrite Nat.eqb_refl. reflexivity.
      * apply RWF_Refine with []; [constructor|].
        intros y Hy. apply PWF_Not. apply PWF_Eq with Ty_Int.
        -- apply T_Var; [simpl; rewrite Nat.eqb_refl; reflexivity|constructor].
        -- constructor.
Qed.

Example addition_result :
  tm_arith Int_Add (tm_int 7%Z) (tm_int 5%Z) --> tm_int 12%Z.
Proof. apply ST_ArithInt. Qed.

Example subtraction_can_be_negative :
  tm_arith Int_Sub (tm_int 3%Z) (tm_int 8%Z) --> tm_int (-5)%Z.
Proof. apply ST_ArithInt. Qed.

Example multiplication_result :
  tm_arith Int_Mul (tm_int (-3)%Z) (tm_int 4%Z) --> tm_int (-12)%Z.
Proof. apply ST_ArithInt. Qed.

Example arithmetic_accepts_zero : forall op n,
  tm_arith op (tm_int n) (tm_int 0%Z) -->
    tm_int (eval_integer_operator op n 0%Z).
Proof. intros. apply ST_ArithInt. Qed.

Example nested_arithmetic :
  multi (tm_arith Int_Mul
           (tm_arith Int_Sub (tm_int 7%Z) (tm_int 2%Z))
           (tm_int 3%Z)) (tm_int 15%Z).
Proof.
  eapply multi_step.
  - apply ST_Arith1; [apply ST_ArithInt | constructor].
  - apply multi_step with (t2 := tm_int 15%Z).
    + apply ST_ArithInt.
    + apply multi_refl.
Qed.

Example arithmetic_refinement_typed : forall op n m,
  has_rtype [] empty_rcontext (tm_arith op (tm_int n) (tm_int m))
    (R_Refine Ty_Int
      (Pred_Eq (tm_bvar 0) (tm_arith op (tm_int n) (tm_int m)))).
Proof.
  intros. apply RT_Arith; apply RT_RefineValue.
  - apply T_Int.
  - apply v_int.
  - apply RWF_Refine with []; [constructor | intros; constructor].
  - exact I.
  - exact I.
  - apply T_Int.
  - apply v_int.
  - apply RWF_Refine with []; [constructor | intros; constructor].
  - exact I.
  - exact I.
Qed.

Example arithmetic_qualifier :
  qualifier_holds (Pred_Lt
    (tm_arith Int_Sub (tm_int 3%Z) (tm_int 8%Z)) (tm_int 0%Z)).
Proof.
  exists (-5)%Z, 0%Z. split.
  - eapply PMS_Step; [apply ST_ArithInt | constructor].
  - split; [constructor | lia].
Qed.

End SystemFRefinementRegression.
