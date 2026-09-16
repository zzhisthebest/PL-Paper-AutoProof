From Stdlib Require Import Lists.List ZArith.BinInt.
From AutoProof.SystemFRefinementIf Require Import
  Syntax RefinementTyping Evaluation Safety.

Module SystemFRefinementIfRegression.
Import ListNotations SystemFRefinementIf SystemFRefinementIfTyping
  SystemFRefinementIfEvaluation SystemFRefinementIfSafety.

Example selected_branch_only :
  tm_if tm_true (tm_int 7%Z) (tm_div (tm_int 1%Z) (tm_int 0%Z))
    --> tm_int 7%Z.
Proof. apply ST_IfTrue; repeat constructor. Qed.

Lemma literal_any_int : forall n,
  has_rtype [] empty_rcontext (tm_int n) (R_Refine Ty_Int Pred_True).
Proof.
  intros. apply RT_RefineValue.
  - constructor.
  - constructor.
  - apply RWF_Refine with []; [constructor | intros; constructor].
  - exact I.
  - exact I.
Qed.

Example conditional_typed :
  has_rtype [] empty_rcontext
    (tm_if tm_true (tm_int 7%Z) (tm_int 8%Z))
    (R_Refine Ty_Int Pred_True).
Proof. apply RT_If; [apply RT_True | apply literal_any_int | apply literal_any_int]. Qed.

Example zero_divisor_not_typed : forall R,
  ~ has_rtype [] empty_rcontext (tm_div (tm_int 1%Z) (tm_int 0%Z)) R.
Proof.
  intros R H.
  destruct (never_stuck _ _ R H (multi_refl _)) as [Hv | [u Hs]].
  - inversion Hv.
  - inversion Hs; subst;
      try match goal with Hstep : step (tm_int _) _ |- _ => inversion Hstep end.
    contradiction.
Qed.

Print Assumptions conditional_typed.
Print Assumptions never_stuck.
End SystemFRefinementIfRegression.
