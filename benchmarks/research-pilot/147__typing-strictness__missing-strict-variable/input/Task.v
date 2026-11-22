From strictness.cbpv Require Import strict_semtyping.

Theorem strict_explosion : forall n (γ : attrs n) (Γ : context n) (ρ : env n) i,
  ρ_not_ok γ ρ Γ n i ltac:(auto) ->
  (forall V A, VWt γ Γ V A -> EvalValFail ρ V) /\
  (forall M A, CWt γ Γ M (CF A) -> EvalCompFail ρ M).
