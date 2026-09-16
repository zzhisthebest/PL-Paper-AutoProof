From Stdlib Require Import Lists.List.
From AutoProof.SystemFRefinementNonDeterminism Require Import
  Syntax RefinementTyping Evaluation Denotations RefinementSoundness.

Module SystemFRefinementNonDeterminismSafety.
Import ListNotations SystemFRefinementNonDeterminism
  SystemFRefinementNonDeterminismTyping SystemFRefinementNonDeterminismEvaluation
  SystemFRefinementNonDeterminismDenotations SystemFRefinementNonDeterminismSoundness.

Theorem never_stuck : forall (t t' : tm) (R : rty),
  has_rtype [] empty_rcontext t R ->
  multi t t' ->
  value t' \/ exists u, t' --> u.
Proof.
  intros t t' R Htyped Hsteps.
  pose proof (denotational_soundness t R Htyped) as [_ [Htotal _]].
  apply must_terminate_progress.
  eapply must_terminate_multi; eauto.
Qed.

Print Assumptions never_stuck.
End SystemFRefinementNonDeterminismSafety.
