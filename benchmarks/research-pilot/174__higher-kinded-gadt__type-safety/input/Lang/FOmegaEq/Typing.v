Require Import Utf8.

Require Import Coq.Lists.List.

Require Import Lang.FOmegaEq.Types Lang.FOmegaEq.Kinds Lang.FOmegaEq.Syntax.

Require Import Binding.Lib Binding.Set.

Require Import Binding.Env.

Import Binding.Intrinsic (Ctx, dom, extC, Build_Ctx, mtC).

Reserved Notation "Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ" (at level 70, Ψ, Γ, e at level 60).

Reserved Notation "Δ ∣ Ψ ∣ Γ ⊢ᵥ v : τ" (at level 70, Ψ, Γ, v at level 60).

Inductive typing_expr {V : Set} (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> (typ ⋆ Δ)) :
  expr V -> typ ⋆ Δ -> Prop :=
| T_val {τ v} :
  Δ ∣ Ψ ∣ Γ ⊢ᵥ v : τ -> Δ ∣ Ψ ∣ Γ ⊢ₑ v : τ
| T_bind  {τ₁ τ₂ e₁ e₂} :
  Δ ∣ Ψ ∣ Γ ⊢ₑ e₁ : τ₁ -> Δ ∣ Ψ ∣ Γ ▹ τ₁ ⊢ₑ e₂ : τ₂ -> Δ ∣ Ψ ∣ Γ ⊢ₑ e₁ >>= e₂ : τ₂
| T_congE {τ τ' e} : Ψ ⊩ τ ≃ τ' -> Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ -> Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ'
| T_app  τ₁ τ₂ v₁ v₂ :
  Δ ∣ Ψ ∣ Γ ⊢ᵥ v₁ : τ₁ →ᵗ τ₂ -> Δ ∣ Ψ ∣ Γ ⊢ᵥ v₂ : τ₁ -> Δ ∣ Ψ ∣ Γ ⊢ₑ v₁ v₂ : τ₂
| T_tapp {κ τ σ v} :
  Δ ∣ Ψ ∣ Γ ⊢ᵥ v : ∀ᵗ κ , τ -> Δ ∣ Ψ ∣ Γ ⊢ₑ e_tapp v : subst τ σ
| T_projL {τ₁ τ₂ v} :
  Δ ∣ Ψ ∣ Γ ⊢ᵥ v : τ₁ × τ₂ -> Δ ∣ Ψ ∣ Γ ⊢ₑ e_proj L v : τ₁
| T_projR {τ₁ τ₂ v} :
  Δ ∣ Ψ ∣ Γ ⊢ᵥ v : τ₁ × τ₂ -> Δ ∣ Ψ ∣ Γ ⊢ₑ e_proj R v : τ₂
| T_abort {τ : typ ⋆ Δ} {v} :
  Δ ∣ Ψ ∣ Γ ⊢ᵥ v : ⊥ -> Δ ∣ Ψ ∣ Γ ⊢ₑ e_abort v : τ
| T_case {τ₁ τ₂ : typ ⋆ Δ} {τ} {v e₁ e₂} :
  Δ ∣ Ψ ∣ Γ ▹ τ₁ ⊢ₑ e₁ : τ -> Δ ∣ Ψ ∣ Γ ▹ τ₂ ⊢ₑ e₂ : τ ->
  Δ ∣ Ψ ∣ Γ ⊢ᵥ v : τ₁ + τ₂ -> Δ ∣ Ψ ∣ Γ ⊢ₑ e_case v e₁ e₂ : τ
| T_unpack {κ} {τ τ'} {v e} :
  Δ ∣ Ψ ∣ Γ ⊢ᵥ v : ∃ᵗ κ , τ ->
  extC κ Δ ∣ map shift Ψ ∣ shift • Γ ▹ τ ⊢ₑ e : shift τ' ->
  Δ ∣ Ψ ∣ Γ ⊢ₑ e_unpack v e : τ'
| T_unroll κ τ σ₁ σ₂ (HF : rel_app κ (rec_type Δ κ τ) (subst τ (rec_type Δ κ τ)) ⋆ σ₁ σ₂) v :
  Δ ∣ Ψ ∣ Γ ⊢ᵥ v : σ₁ -> Δ ∣ Ψ ∣ Γ ⊢ₑ e_unroll v : σ₂
| T_cabort {τ : typ ⋆ Δ} {ψ}  :
  Ψ ⊩ ψ -> ⊮ ψ -> Δ ∣ Ψ ∣ Γ ⊢ₑ e_cabort : τ
| T_capp {φ τ} {v} :
  Ψ ⊩ φ -> Δ ∣ Ψ ∣ Γ ⊢ᵥ v : φ →ᶜ τ -> Δ ∣ Ψ ∣ Γ ⊢ₑ e_capp v : τ
| T_lwith {φ τ} {σ : typ ⋆ Δ} {v e} :
  Δ ∣ Ψ ∣ Γ ⊢ᵥ v : φ ×ᶜ σ -> Δ ∣ φ :: Ψ ∣ Γ ▹ σ ⊢ₑ e : τ ->
  Δ ∣ Ψ ∣ Γ ⊢ₑ e_lwith v e : τ
where "Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ" := (typing_expr Δ Ψ%typ Γ%typ e%syn τ%typ)
with typing_val {V : Set} (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> (typ ⋆ Δ)) : value V -> typ ⋆ Δ -> Prop :=
| T_var {x τ} (EQ : Γ x = τ) : Δ ∣ Ψ ∣ Γ ⊢ᵥ v_var x : τ
| T_congV {v τ τ'} : Ψ ⊩ τ ≃ τ' -> Δ ∣ Ψ ∣ Γ ⊢ᵥ v : τ -> Δ ∣ Ψ ∣ Γ ⊢ᵥ v : τ'
| T_unit : Δ ∣ Ψ ∣ Γ ⊢ᵥ ⟨⟩ : ⊤
| T_lam {τ₁ τ₂ e} :
  Δ ∣ Ψ ∣ Γ ▹ τ₁ ⊢ₑ e : τ₂ -> Δ ∣ Ψ ∣ Γ ⊢ᵥ ƛ e : τ₁ →ᵗ τ₂
| T_pair {τ₁ τ₂ v₁ v₂} :
  Δ ∣ Ψ ∣ Γ ⊢ᵥ v₁ : τ₁ -> Δ ∣ Ψ ∣ Γ ⊢ᵥ v₂ : τ₂ -> Δ ∣ Ψ ∣ Γ ⊢ᵥ ⟨v₁, v₂⟩ : τ₁ × τ₂
| T_injl {τ₁ τ₂ v} :
  Δ ∣ Ψ ∣ Γ ⊢ᵥ v : τ₁ -> Δ ∣ Ψ ∣ Γ ⊢ᵥ v_inj L v : τ₁ + τ₂
| T_injr {τ₁ τ₂ v} :
  Δ ∣ Ψ ∣ Γ ⊢ᵥ v : τ₂ -> Δ ∣ Ψ ∣ Γ ⊢ᵥ v_inj R v : τ₁ + τ₂
| T_tlam {κ τ e} :
  extC κ Δ ∣ map shift Ψ ∣ compose shift Γ ⊢ₑ e : τ -> Δ ∣ Ψ ∣ Γ ⊢ᵥ Λ e : ∀ᵗ κ, τ
| T_pack κ {τ : typ ⋆ (extC κ Δ)} {τ' : typ κ Δ} {v} :
  Δ ∣ Ψ ∣ Γ ⊢ᵥ v : subst τ τ' -> Δ ∣ Ψ ∣ Γ ⊢ᵥ v_pack v : ∃ᵗ κ, τ
| T_roll κ τ σ₁ σ₂ (HF : rel_app κ (rec_type Δ κ τ) (subst τ (rec_type Δ κ τ)) ⋆ σ₁ σ₂) v :
  Δ ∣ Ψ ∣ Γ ⊢ᵥ v : σ₂ -> Δ ∣ Ψ ∣ Γ ⊢ᵥ v_roll v : σ₁
| T_lamC {φ τ} {e} :
  Δ ∣ φ :: Ψ ∣ Γ ⊢ₑ e : τ -> Δ ∣ Ψ ∣ Γ ⊢ᵥ ƛᶜ e : φ →ᶜ τ
| T_withC {φ τ} {v} :
  Δ ∣ Ψ ∣ Γ ⊢ᵥ v : τ -> Ψ ⊩ φ -> Δ ∣ Ψ ∣ Γ ⊢ᵥ ⟨v⟩ᶜ : φ ×ᶜ τ
| T_rec {τ₁ τ₂ : typ ⋆ Δ} {e : expr (inc (inc V))} :
  Δ ∣ Ψ ∣ Γ ▹ (τ₁ →ᵗ τ₂) ▹ τ₁ ⊢ₑ e : τ₂ -> Δ ∣ Ψ ∣ Γ ⊢ᵥ (v_fix e) : τ₁ →ᵗ τ₂
where "Δ ∣ Ψ ∣ Γ ⊢ᵥ v : τ" := (typing_val Δ Ψ%typ Γ%typ v%syn τ%typ).

Section ExampleClosedVoid.

Definition ntarr : typ ⋆ (extC (⋆ ⇒ ⋆) (extC ⋆ mtC)) :=
    (0ᵛ (t_var _ (VS VZ : dom (extC _ (extC _ _))) eq_refl) →ᵗ ⊥)%typ.

Definition eqA : constr (extC (⋆ ⇒ ⋆) (extC ⋆ mtC)) :=
    (tc_all ⋆ 0ᵛ ≃ t_var _ (VS VZ : dom (extC _ (extC _ _))) eq_refl)%typ.

Arguments ntarr : simpl never.

Arguments eqA : simpl never.

Definition tloop : typ ⋆ (extC ⋆ mtC) :=
    (∃ᵗ ⋆ ⇒ ⋆, eqA ×ᶜ ntarr)%typ.

Definition ltl := (∀ᵗ ⋆, tloop)%typ.

Definition foo : value ∅ :=
    v_lam (e_unpack (v_var VZ)
             (e_lwith (v_var VZ)
                (e_app (v_var VZ) (v_pack (v_withC (v_var VZ)))))).

Definition nt : expr ∅ := e_app foo (v_pack (v_withC foo)).

Definition δε {Δ : Ctx kind} : Intrinsic.Arr mtC Δ := {| Intrinsic.apply_arr (x : dom mtC) := match x with end;
                                                          Intrinsic.arr_hom (x : dom mtC) := match x with end |}.

End ExampleClosedVoid.
