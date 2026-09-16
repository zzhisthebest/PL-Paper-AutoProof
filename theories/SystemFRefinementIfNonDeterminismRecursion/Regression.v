From Stdlib Require Import Lists.List ZArith.BinInt Lia.
From AutoProof.SystemFRefinementIfNonDeterminismRecursion Require Import
  Syntax RefinementTyping Evaluation RefinementSoundness Safety.

Module SystemFRefinementIfNonDeterminismRecursionRegression.
Import ListNotations SystemFRefinementIfNonDeterminismRecursion
  SystemFRefinementIfNonDeterminismRecursionTyping SystemFRefinementIfNonDeterminismRecursionEvaluation
  SystemFRefinementIfNonDeterminismRecursionSafety SystemFRefinementIfNonDeterminismRecursionSoundness.

Lemma integer_any : forall n,
  has_rtype [] empty_rcontext (tm_int n) (R_Refine Ty_Int Pred_True).
Proof.
  intros. apply RT_RefineValue.
  - constructor.
  - constructor.
  - apply RWF_Refine with []; [constructor |intros; constructor].
  - exact I.
  - exact I.
Qed.

Example choice_typed :
  has_rtype [] empty_rcontext (tm_choice (tm_int 2%Z) (tm_int 3%Z))
    (R_Refine Ty_Int Pred_True).
Proof. apply RT_Choice; apply integer_any. Qed.

Example choice_left :
  tm_choice (tm_int 2%Z) (tm_int 3%Z) --> tm_int 2%Z.
Proof. apply ST_ChoiceLeft; constructor. Qed.

Example choice_right :
  tm_choice (tm_int 2%Z) (tm_int 3%Z) --> tm_int 3%Z.
Proof. apply ST_ChoiceRight; constructor. Qed.

Example risky_division_has_a_good_path :
  multi (tm_div (tm_int 6%Z) (tm_choice (tm_int 0%Z) (tm_int 1%Z))) (tm_int 6%Z).
Proof.
  eapply multi_step.
  - apply ST_Div2; [constructor |apply ST_ChoiceRight; constructor].
  - eapply multi_step; [apply ST_DivInt; discriminate |constructor].
Qed.

Example risky_division_not_typed : forall R,
  ~ has_rtype [] empty_rcontext
    (tm_div (tm_int 6%Z) (tm_choice (tm_int 0%Z) (tm_int 1%Z))) R.
Proof.
  intros R Htyped.
  assert (Hs : multi
    (tm_div (tm_int 6%Z) (tm_choice (tm_int 0%Z) (tm_int 1%Z)))
    (tm_div (tm_int 6%Z) (tm_int 0%Z))).
  { eapply multi_step.
    - apply ST_Div2; [constructor |apply ST_ChoiceLeft; constructor].
    - constructor. }
  destruct (never_stuck _ _ R Htyped Hs) as [Hv |[u Hu]].
  - inversion Hv.
  - inversion Hu; subst;
      try match goal with Hs : step (tm_int _) _ |- _ => inversion Hs end.
    contradiction.
Qed.


Example nondeterministic_metric_not_less_than_itself :
  ~ qualifier_holds
    (Pred_Lt (tm_choice (tm_int 0%Z) (tm_int 1%Z))
             (tm_choice (tm_int 0%Z) (tm_int 1%Z))).
Proof.
  intros [n [m [Hn [Hm [Hlt Hall]]]]].
  assert (Hzero : predicate_multistep
    (tm_choice (tm_int 0%Z) (tm_int 1%Z)) (tm_int 0%Z)).
  { eapply PMS_Step; [apply ST_ChoiceLeft; constructor | constructor]. }
  pose proof (Hall 0%Z 0%Z Hzero Hzero). lia.
Qed.

Example boolean_choice_safe :
  forall t', multi (tm_if tm_true
    (tm_choice (tm_int 2%Z) (tm_int 3%Z)) (tm_int 4%Z)) t' ->
    value t' \/ exists u, t' --> u.
Proof.
  intros t' Hsteps. eapply never_stuck; [|exact Hsteps].
  eapply RT_If; [apply RT_True |apply RT_Choice; apply integer_any |apply integer_any].
Qed.

Print Assumptions never_stuck.
End SystemFRefinementIfNonDeterminismRecursionRegression.
