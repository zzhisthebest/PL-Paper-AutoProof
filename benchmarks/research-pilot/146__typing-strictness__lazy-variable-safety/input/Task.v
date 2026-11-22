From strictness.cbpv Require Import lazy_semtyping.

Theorem lazy_soundness : forall n (γ : attrs n) (Γ : context n) (ρ : env n),
  ρ_ok γ ρ Γ n γ ->
  forall i, γ i = Lazy ->
  (forall V A, VWt γ Γ V A ->
    exists W, EvalVal γ (ρ <- Absent @ i) V W) /\
  (forall M B, CWt γ Γ M B ->
    exists T, EvalComp γ (ρ <- Absent @ i) M T).
