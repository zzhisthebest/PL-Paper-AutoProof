From Stdlib Require Import Utf8.
Require Import Common.Types Source.Typing Source.CPS.
Require Import Target.ContextualEquivalence.

Theorem coherence {V : Set} (Γ : env V) e T :
  ∀ (D₁ D₂ : Γ ⊢ e ∷ T), ctx_equiv Γ C⟦ D₁ ⟧ C⟦ D₂ ⟧ T.
