From Stdlib Require Import Lists.List.
From AutoProof.SystemFRefinementNonDeterminismRecursion Require Import
  Syntax RefinementTyping Evaluation RefinementSoundness.
Module SystemFRefinementNonDeterminismRecursionSafety.
Import ListNotations SystemFRefinementNonDeterminismRecursion
  SystemFRefinementNonDeterminismRecursionTyping
  SystemFRefinementNonDeterminismRecursionEvaluation
  SystemFRefinementNonDeterminismRecursionSoundness.
Theorem never_stuck : forall t t' R,
  has_rtype [] empty_rcontext t R ->
  multi t t' ->
  value t' \/ exists u, t' --> u.
Proof.
  intros t t' R Htyped Hsteps.
  apply must_terminate_progress.
  eapply must_terminate_multi; [exact Hsteps |].
  exact (refinement_termination t R Htyped).
Qed.
Print Assumptions never_stuck.
End SystemFRefinementNonDeterminismRecursionSafety.
