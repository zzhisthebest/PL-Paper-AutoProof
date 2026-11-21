Require Import Utf8.

Require Import Binding.Lib Binding.Set.

Require Import Trans.DeepHandle_to_Shift0.

Import T.

Existing Instance S.SetPureCore_typ.

Definition compose {A B C} (f : B → C) (g : A → B) (x : A) := f (g x).

Definition sshift {A : Set} : inc A [→] inc (inc (inc A)) :=
  {| apply_arr :=
       λ x, match x with
            | VZ   => VZ
            | VS x => VS (VS (VS x))
            end
  |}.

Definition hndl_typ {A : Set} (σ₁ σ₂ : typ (inc A)) : typ (inc (inc (inc A))) :=
  ((fmap sshift σ₁) →[ε] (fmap sshift σ₂ →[#(VS VZ)] #(VS (VS VZ)))
   →[#(VS VZ)] #(VS (VS VZ)))%tp.

Definition eff_typ {A : Set} (σ₁ σ₂ : typ (inc A)) : typ (inc (inc A)) :=
  (([∀] T, hndl_typ σ₁ σ₂) →[#VZ] #(VS VZ))%tp.

Definition tr_kind κ :=
  match κ with
  | S.T => T
  | S.E => E
  end.

Fixpoint tr_typ {A : Set} (τ : S.typ A) : T.typ A :=
  match τ with
  | S.t_var x       => #x
  | S.t_arr τ₁ ρ τ₂ => tr_typ τ₁ →[tr_typ ρ] tr_typ τ₂
  | S.t_all κ τ     => [∀] tr_kind κ, tr_typ τ
  | S.r_pure         => ε
  | S.r_cons σ₁ σ₂ ρ => [eff_typ (tr_typ σ₁) (tr_typ σ₂) / #VZ] tr_typ ρ
  end%tp.

Definition tr_sub {A B : Set} (γ : @Sub S.typ _ A B) : @Sub T.typ _ A B :=
  {| apply_sub := λ x, tr_typ (γ x) |}.

Require Import Top.Env.

Theorem tr_type_pres {A V : Set} (Δ : S.tenv A) (Γ : S.env V A) e τ ρ
        (HWF : S.wf_env Δ Γ)
        (HT : S.types Δ Γ e τ ρ) :
  tr_kind ∘ Δ ∣ tr_typ ∘ Γ ⊢ tr_expr e :: tr_typ τ / tr_typ ρ.

Theorem preservation {V : Set} (e e' : S.expr V) :
  S.red e e' → tr_expr e →ᵢ⁺ tr_expr e'.
