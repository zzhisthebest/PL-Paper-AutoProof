From Stdlib Require Import Lists.List.
From AutoProof.SystemFRefinementRecursion Require Import
  Syntax RefinementTyping Evaluation RefinementSoundness.

Module SystemFRefinementRecursionSafety.
Import ListNotations SystemFRefinementRecursion SystemFRefinementRecursionTyping
  SystemFRefinementRecursionEvaluation SystemFRefinementRecursionSoundness.

Theorem never_stuck : forall t t' R,
  has_rtype [] empty_rcontext t R ->
  multi t t' ->
  value t' \/ exists u, t' --> u.
Proof.
  intros t t' R Htyped Hsteps.
  pose proof (refinement_termination t R Htyped) as Hhalts.
  pose proof (halts_multi t t' Hsteps Hhalts) as Hremaining.
  destruct Hremaining as [v [Htv Hv]].
  inversion Htv; subst.
  - left. exact Hv.
  - right. eexists. eassumption.
Qed.

Print Assumptions never_stuck.

End SystemFRefinementRecursionSafety.
