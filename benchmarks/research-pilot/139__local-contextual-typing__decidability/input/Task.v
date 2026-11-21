Require Import Syntax Algo.

Theorem dec_sub : forall Δ A p B,
  {Ω | sub Δ A p B Ω} + {~ exists Ω, sub Δ A p B Ω}.

Theorem dec_ty : forall Γ Σ e,
  {A | ty Γ Σ e A} + {~ exists A, ty Γ Σ e A}.
