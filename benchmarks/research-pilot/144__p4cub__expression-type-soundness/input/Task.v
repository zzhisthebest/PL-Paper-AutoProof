Require Import Coq.micromega.Lia.

From Poulet4.P4cub.Semantics.Dynamic Require Import BigStep.Value.Typing BigStep.Semantics.

Require Import Poulet4.P4cub.Semantics.Static.Typing Poulet4.Utils.ForallMap.

Section BigStepTheorems.

Section ExpPreservation.

Theorem exp_big_step_preservation : forall ϵ e v Δ Γ τ,
        ⟨ ϵ, e ⟩ ⇓ v ->
        Forall2 type_val ϵ Γ ->
        `⟨ Δ, Γ ⟩ ⊢ e ∈ τ ->
        ⊢ᵥ v ∈ τ.

End ExpPreservation.

Section ExpProgress.

Theorem exp_big_step_progress : forall Δ Γ e τ ϵ,
        Forall2 type_val ϵ Γ ->
        `⟨ Δ, Γ ⟩ ⊢ e ∈ τ ->
        exists v, ⟨ ϵ, e ⟩ ⇓ v.

End ExpProgress.

End BigStepTheorems.
