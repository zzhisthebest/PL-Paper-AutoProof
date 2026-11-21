From Stdlib Require Import Utf8.
Require Import Common.Types Target.Syntax.

Reserved Notation "c ⊩ A ≺: B" (at level 45).

Inductive sub : crc → typ_eff → typ_eff → Prop :=
| sub_refl  : ∀ T, crc_id ⊩ T ≺: T
| sub_trans : ∀ S T U c₁ c₂,
    c₁ ⊩ S ≺: U →
    c₂ ⊩ T ≺: S →
    crc_comp c₁ c₂ ⊩ T ≺: U
| sub_arrow : ∀ τ₁ τ₂ T₁ T₂ c₁ c₂,
    c₁ ⊩ (τ₂)ε ≺: (τ₁)ε → c₂ ⊩ T₁ ≺: T₂ →
    crc_arrow c₁ c₂ ⊩ (τ₁ ↦ T₁)ε ≺: (τ₂ ↦ T₂)ε
| sub_lift  : ∀ τ T U c,
    c ⊩ T ≺: U →
    crc_lift c ⊩ (τ)ε ≺: τ ![ T ] U
| sub_cons  : ∀ τ₁ τ₂ T₁ T₂ U₁ U₂ c c₁ c₂,
    c ⊩ (τ₁)ε ≺: (τ₂)ε →
    c₁ ⊩ T₂ ≺: T₁ →
    c₂ ⊩ U₁ ≺: U₂ →
    crc_cons c c₁ c₂ ⊩ τ₁ ![ T₁ ] U₁ ≺: τ₂ ![ T₂ ] U₂
where "c ⊩ A ≺: B" := (sub c A B).

Reserved Notation "G ⊩ e ∷ T" (at level 45).

Inductive typing {V : Set} (Γ : env V) : exp V → typ_eff → Prop :=
| T_Var   : ∀ x, Γ ⊩ exp_var x ∷ (Γ x)ε
| T_Const : ∀ m, Γ ⊩ exp_const m ∷ (ℕ)ε
| T_Abs   : ∀ e τ T,
    Γ / τ ⊩ e ∷ T →
    Γ ⊩ exp_abs e ∷ (τ ↦ T)ε
| T_App   : ∀ e₁ e₂ τ T,
    Γ ⊩ e₁ ∷ (τ ↦ T)ε →
    Γ ⊩ e₂ ∷ (τ)ε →
    Γ ⊩ exp_app e₁ e₂ ∷ T
| T_KAbs  : ∀ e τ T U,
    Γ / τ ↦ T ⊩ e ∷ U →
    Γ ⊩ exp_abs e ∷ τ ![ T ] U
| T_KApp  : ∀ e k τ T U,
    open_value k →
    Γ ⊩ e ∷ τ ![ T ] U →
    Γ ⊩ k ∷ (τ ↦ T)ε →
    Γ ⊩ exp_app e k ∷ U
| T_CApp  : ∀ c e T U,
    c ⊩ T ≺: U →
    Γ ⊩ e ∷ T →
    Γ ⊩ exp_capp c e ∷ U
| T_Fix   : ∀ e τ T,
    Γ / τ ↦ T / τ ⊩ e ∷ T →
    Γ ⊩ exp_fix e ∷ (τ ↦ T)ε
| T_Succ  : ∀ e,
    Γ ⊩ e ∷ (ℕ)ε → Γ ⊩ exp_succ e ∷ (ℕ)ε
| T_Case  : ∀ e₁ e₂ e₃ T,
    Γ ⊩ e₁ ∷ (ℕ)ε →
    Γ ⊩ e₂ ∷ T →
    Γ / ℕ ⊩ e₃ ∷ T →
    Γ ⊩ exp_case e₁ e₂ e₃ ∷ T
where "G ⊩ e ∷ T" := (@typing _ G e T).

Reserved Notation "⊩ᵥ v ∷ T" (at level 45).


Reserved Notation "C ∷[ G ⊢ A ]↝ B" (at level 45).

Inductive ctx_typing (T₀ : typ_eff) : ∀ V : Set, ctx V → env V → typ_eff → Prop :=
| CT_Hole  : ctx_hole ∷[ empty_env ⊢ T₀ ]↝ T₀
| CT_Abs   : ∀ (V : Set) (C : ctx V) Γ τ T,
  C ∷[ Γ ⊢ (τ ↦ T)ε ]↝ T₀ →
  ctx_abs C ∷[ Γ / τ ⊢ T ]↝ T₀
| CT_App1  : ∀ (V : Set) (C : ctx V) Γ e τ T,
  C ∷[ Γ ⊢ T ]↝ T₀ →
  Γ ⊩ e ∷ (τ)ε →
  ctx_app1 C e ∷[ Γ ⊢ (τ ↦ T)ε ]↝ T₀
| CT_App2  : ∀ (V : Set) (C : ctx V) Γ e τ T,
  Γ ⊩ e ∷ (τ ↦ T)ε →
  C ∷[ Γ ⊢ T ]↝ T₀ →
  ctx_app2 e C ∷[ Γ ⊢ (τ)ε ]↝ T₀
| CT_KAbs  : ∀ (V : Set) (C : ctx V) Γ τ T U,
  C ∷[ Γ ⊢ τ ![ T ] U ]↝ T₀ →
  ctx_abs C ∷[ Γ / τ ↦ T ⊢ U ]↝ T₀
| CT_KApp : ∀ (V : Set) (C : ctx V) Γ k τ T U,
  open_value k →
  C ∷[ Γ ⊢ U ]↝ T₀ →
  Γ ⊩ k ∷ (τ ↦ T)ε →
  ctx_app1 C k ∷[ Γ ⊢ τ ![ T ] U ]↝ T₀
| CT_CApp : ∀ (V : Set) (C : ctx V) Γ c T U,
  c ⊩ T ≺: U →
  C ∷[ Γ ⊢ U ]↝ T₀ →
  ctx_capp c C ∷[ Γ ⊢ T ]↝ T₀
| CT_Fix : ∀ (V : Set) (C : ctx V) Γ τ T,
  C ∷[ Γ ⊢ (τ ↦ T)ε ]↝ T₀ →
  ctx_fix C ∷[ Γ / τ ↦ T / τ ⊢ T ]↝ T₀
| CT_Succ : ∀ (V : Set) (C : ctx V) Γ,
  C ∷[ Γ ⊢ (ℕ)ε ]↝ T₀ →
  ctx_succ C ∷[ Γ ⊢ (ℕ)ε ]↝ T₀
| CT_Case : ∀ (V : Set) (C : ctx V) Γ e₁ e₂ T,
  C ∷[ Γ ⊢ T ]↝ T₀ →
  Γ ⊩ e₁ ∷ T →
  Γ / ℕ ⊩ e₂ ∷ T →
  ctx_case C e₁ e₂ ∷[ Γ ⊢ (ℕ)ε ]↝ T₀
| CT_Case1 : ∀ (V : Set) (C : ctx V) Γ e e₂ T,
  Γ ⊩ e ∷ (ℕ)ε →
  C ∷[ Γ ⊢ T ]↝ T₀ →
  Γ / ℕ ⊩ e₂ ∷ T →
  ctx_case1 e C e₂ ∷[ Γ ⊢ T ]↝ T₀
| CT_Case2 : ∀ (V : Set) (C : ctx V) Γ e e₁ T,
  Γ ⊩ e ∷ (ℕ)ε →
  Γ ⊩ e₁ ∷ T →
  C ∷[ Γ ⊢ T ]↝ T₀ →
  ctx_case2 e e₁ C ∷[ Γ / ℕ ⊢ T ]↝ T₀
where "C ∷[ G ⊢ A ]↝ B" := (ctx_typing B _ C G A).
