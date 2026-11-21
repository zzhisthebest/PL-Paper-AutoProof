From Stdlib Require Import Utf8.
Require Import Common.Metatheory Common.Types.
Require Import Source.Syntax.

Reserved Notation "A ≺: B" (at level 45).

Inductive sub : typ_eff → typ_eff → Set :=
| S_Refl  : ∀ T, T ≺: T
| S_Trans : ∀ T₁ T₂ T₃,
    T₂ ≺: T₃ → T₁ ≺: T₂ → T₁ ≺: T₃
| S_Arrow : ∀ τ₁ τ₂ T₁ T₂,
    (τ₂)ε ≺: (τ₁)ε → T₁ ≺: T₂ → (τ₁ ↦ T₁)ε ≺: (τ₂ ↦ T₂)ε
| S_Lift  : ∀ τ T₁ T₂,
    T₁ ≺: T₂ → (τ)ε ≺: τ ![ T₁ ] T₂
| S_Cons  : ∀ τ₁ τ₂ T₁ T₂ T₁' T₂',
    (τ₁)ε ≺: (τ₂)ε → T₂ ≺: T₁ → T₁' ≺: T₂' → τ₁ ![ T₁ ] T₁' ≺: τ₂ ![ T₂ ] T₂'
where "A ≺: B" := (sub A B).

Reserved Notation "G ⊢ e ∷ T" (at level 45).

Inductive typing {V : Set} (Γ : env V) : exp V → typ_eff → Set :=
| T_Var   : ∀ x,
    Γ ⊢ exp_var x ∷ (Γ x)ε
| T_Const : ∀ m,
    Γ ⊢ exp_const m ∷ (ℕ)ε
| T_Abs   : ∀ e τ T,
    Γ / τ ⊢ e ∷ T →
    Γ ⊢ exp_abs e ∷ (τ ↦ T)ε
| T_PApp  : ∀ e₁ e₂ τ T,
    Γ ⊢ e₁ ∷ (τ ↦ T)ε →
    Γ ⊢ e₂ ∷ (τ)ε →
    Γ ⊢ exp_app e₁ e₂ ∷ T
| T_App   : ∀ e₁ e₂ τ₁ τ₂ U₁ U₂ U₃ U₄,
    Γ ⊢ e₁ ∷ (τ₂ ↦ τ₁ ![ U₄ ] U₃) ![ U₂ ] U₁ →
    Γ ⊢ e₂ ∷ τ₂ ![ U₃ ] U₂ →
    Γ ⊢ exp_app e₁ e₂ ∷ τ₁ ![ U₄ ] U₁
| T_Sft   : ∀ e τ T U,
    Γ / τ ↦ T ⊢ e ∷ U →
    Γ ⊢ exp_shift0 e ∷ τ ![ T ] U
| T_Rst   : ∀ e τ T,
    Γ ⊢ e ∷ τ ![ (τ)ε ] T →
    Γ ⊢ exp_reset0 e ∷ T
| T_PDol  : ∀ e₁ e₂ τ T U,
    Γ ⊢ e₁ ∷ (τ ↦ T)ε →
    Γ ⊢ e₂ ∷ τ ![ T ] U →
    Γ ⊢ exp_dollar e₁ e₂ ∷ U
| T_Dol   : ∀ e₁ e₂ τ τ' T U₁ U₂ U₃,
    Γ ⊢ e₁ ∷ (τ ↦ T) ![ U₂ ] U₁ →
    Γ ⊢ e₂ ∷ τ ![ T ] τ' ![ U₃ ] U₂ →
    Γ ⊢ exp_dollar e₁ e₂ ∷ τ' ![ U₃ ] U₁
| T_Fix   : ∀ e τ T,
    Γ / τ ↦ T / τ ⊢ e ∷ T →
    Γ ⊢ exp_fix e ∷ (τ ↦ T)ε
| T_PSucc : ∀ e,
    Γ ⊢ e ∷ (ℕ)ε →
    Γ ⊢ exp_succ e ∷ (ℕ)ε
| T_Succ  : ∀ e T U,
    Γ ⊢ e ∷ ℕ ![ T ] U →
    Γ ⊢ exp_succ e ∷ ℕ ![ T ] U
| T_PCase : ∀ e e₁ e₂ T,
    Γ ⊢ e ∷ (ℕ)ε →
    Γ ⊢ e₁ ∷ T →
    Γ / ℕ ⊢ e₂ ∷ T →
    Γ ⊢ exp_case e e₁ e₂ ∷ T
| T_Case  : ∀ e e₁ e₂ τ U₁ U₂ U₃,
    Γ ⊢ e ∷ ℕ ![ U₂ ] U₁ →
    Γ ⊢ e₁ ∷ τ ![ U₃ ] U₂ →
    Γ / ℕ ⊢ e₂ ∷ τ ![ U₃ ] U₂ →
    Γ ⊢ exp_case e e₁ e₂ ∷ τ ![ U₃ ] U₁
| T_Sub   : ∀ e T U,
    Γ ⊢ e ∷ T →
    T ≺: U →
    Γ ⊢ e ∷ U
where "G ⊢ e ∷ T" := (@typing _ G e T).

Arguments T_Var   [V] [Γ] _.
Arguments T_Const [V] [Γ] _.
Arguments T_Abs   [V] [Γ] [e] [τ] [T] _.
Arguments T_PApp  [V] [Γ] [e₁] [e₂] [τ] [T] _ _.
Arguments T_App   [V] [Γ] [e₁] [e₂] [τ₁] [τ₂] [U₁] [U₂] [U₃] [U₄] _ _.
Arguments T_Sft   [V] [Γ] [e] [τ] [T] [U] _.
Arguments T_Rst   [V] [Γ] [e] [τ] [T] _.
Arguments T_PDol  [V] [Γ] [e₁] [e₂] [τ] [T] [U] _ _.
Arguments T_Dol   [V] [Γ] [e₁] [e₂] [τ] [τ'] [T] [U₁] [U₂] [U₃] _ _.
Arguments T_Fix   [V] [Γ] [e] [τ] [T] _.
Arguments T_PSucc [V] [Γ] [e] _.
Arguments T_Succ  [V] [Γ] [e] [T] [U] _.
Arguments T_PCase [V] [Γ] [e] [e₁] [e₂] [T] _ _ _.
Arguments T_Case  [V] [Γ] [e] [e₁] [e₂] [τ] [U₁] [U₂] [U₃] _ _ _.
Arguments T_Sub   [V] [Γ] [e] [T] [U] _ _.
