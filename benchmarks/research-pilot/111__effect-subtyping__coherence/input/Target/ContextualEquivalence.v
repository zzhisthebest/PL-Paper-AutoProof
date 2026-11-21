From Stdlib Require Import Utf8.
Require Import Common.Types.
Require Import Target.Syntax Target.Typing.
Require Import Target.Reduction.

Definition obs (e₁ e₂ : exp0) : Prop :=
  stops e₁ → stops e₂.
Notation "A ~ B" := (obs A B) (at level 70).

Definition ctx_equiv {V : Set}
    (Γ : env V) (e₁ e₂ : exp V) (T : typ_eff) :=
  ∀ (C : ctx V) ρ, C ∷[ Γ ⊢ T ]↝ (ρ)ε → plug C e₁ ~ plug C e₂.
