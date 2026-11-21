Require Import Utf8.

Require Import Binding.Lib Binding.Set.

Require Export Lang.DeepHandle.Types.

Require Import RelationClasses Env.

Definition env V A := V → typ A.

Definition tenv (A : Set) := A → kind.

Reserved Notation " Δ ⊢ τ :: κ " (at level 70, τ at level 30, no associativity).

Reserved Notation " Δ ⊢ τ ⇝ τ' " (at level 70, τ, τ' at level 30, no associativity).

Reserved Notation " Δ ⊢ τ ≲ τ' :: κ " (at level 70, τ, τ' at level 30, no associativity).

Reserved Notation " Δ ∣ Γ ⊢ e :: τ / ρ " (at level 70, Γ, e at level 40, τ at level 30, no associativity).

Section WellFormedness.

Local Open Scope tp_scope.

Inductive kinds (A : Set) (Δ : tenv A) : typ A → kind → Prop :=
  | k_var (x : A) : Δ ⊢ # x :: Δ x
  | k_arr τ₁ τ₂ ρ
          (HKτ₁ : Δ ⊢ τ₁ :: T)
          (HKτ₂ : Δ ⊢ τ₂ :: T)
          (HKρ  : Δ ⊢ ρ  :: E) :
      Δ ⊢ τ₁ →[ρ] τ₂ :: T
  | k_all κ τ
          (HK : Δ ▹ κ ⊢ τ :: T) :
      Δ ⊢ [∀] κ, τ :: T
  | k_pure : Δ ⊢ ε :: E
  | k_cons τ₁ τ₂ ρ
           (HKτ₁ : Δ ▹ T ⊢ τ₁ :: T)
           (HKτ₂ : Δ ▹ T ⊢ τ₂ :: T)
           (HKρ  : Δ ⊢ ρ :: E) :
      Δ ⊢ [τ₁ ⇒ τ₂] ρ :: E
  where " Δ ⊢ τ :: κ " := (kinds _ Δ τ κ).

Definition wf_env {A V : Set} (Δ : tenv A) (Γ : env V A) :=
    ∀ x, Δ ⊢ Γ x :: T.

Definition wf_subst {A B : Set} (Δ₁ : tenv A) (Δ₂ : tenv B) (η : A [⇒] B) :=
    ∀ x, Δ₂ ⊢ η x :: Δ₁ x.

Section Properties.

End Properties.

End WellFormedness.

Notation " Δ ⊢ τ :: κ " := (kinds _ Δ τ κ).

Section Instantiation.

Local Open Scope tp_scope.

Inductive inst_typ {A : Set} (Δ : tenv A) : typ A → typ A → Prop :=
  | inst_id  τ : Δ ⊢ τ ⇝ τ
  | inst_all κ τ₁ τ₂ σ
             (HK  : Δ ⊢ σ :: κ)
             (HGS : Δ ⊢ subst (Inc:=inc) τ₁ σ ⇝ τ₂) :
      Δ ⊢ [∀] κ, τ₁ ⇝ τ₂
  where " Δ ⊢ τ ⇝ τ' " := (@inst_typ _ Δ τ τ').

End Instantiation.

Notation " Δ ⊢ τ ⇝ τ' " := (@inst_typ _ Δ τ τ').

Section Subtyping.

Local Open Scope tp_scope.

Inductive subtyp (A : Set) (Δ : tenv A) : kind → typ A → typ A  → Prop :=
  | st_var (x : A) :
      Δ ⊢ #x ≲ #x :: Δ x
  | st_arr {σ₁ σ₂ τ₁ τ₂ ρ₁ ρ₂}
           (HST₁ : Δ ⊢ σ₂ ≲ σ₁ :: T)
           (HST₂ : Δ ⊢ τ₁ ≲ τ₂ :: T)
           (HSE  : Δ ⊢ ρ₁ ≲ ρ₂ :: E) :
      Δ ⊢ σ₁ →[ρ₁] τ₁ ≲ σ₂ →[ρ₂] τ₂ :: T
  | st_all {κ τ₁ τ₂}
           (HST : Δ ▹ κ ⊢ τ₁ ≲ τ₂ :: T) :
      Δ ⊢ [∀] κ, τ₁ ≲ [∀] κ, τ₂ :: T
  | st_pure {ρ} (HWF : Δ ⊢ ρ :: E) :
      Δ ⊢ ε ≲ ρ :: E
  | st_cons σ₁ σ₂ {ρ₁ ρ₂}
            (HSE : Δ ⊢ ρ₁ ≲ ρ₂ :: E) :
      Δ ⊢ [σ₁ ⇒ σ₂] ρ₁ ≲ [σ₁ ⇒ σ₂] ρ₂ :: E
  where " Δ ⊢ τ₁ ≲ τ₂ :: κ " := (subtyp _ Δ κ τ₁ τ₂).

Section Properties.

End Properties.

End Subtyping.

Notation " Δ ⊢ τ ≲ τ' :: κ " := (subtyp _ Δ κ τ τ').

Require Export Lang.DeepHandle.Syntax.

Section Typing.

Local Open Scope tp_scope.

Local Open Scope exp_scope.

Inductive types {A V : Set} (Δ : tenv A) (Γ : env V A) : expr V → typ A → typ A → Prop :=
  | types_var x :
      Δ ∣ Γ ⊢ # x :: Γ x / ε
  | types_lam e τ₁ τ₂ ρ
              (HK : Δ ⊢ τ₁ :: T)
              (HT : Δ ∣ Γ ▹ τ₁ ⊢ e :: τ₂ / ρ) :
      Δ ∣ Γ ⊢ [λ] e :: τ₁ →[ρ] τ₂ / ε
  | types_app e₁ e₂ σ τ ρ
              (HT1 : Δ ∣ Γ ⊢ e₁ :: σ →[ρ] τ / ρ)
              (HT2 : Δ ∣ Γ ⊢ e₂ :: σ / ρ) :
      Δ ∣ Γ ⊢ e₁ @ e₂ :: τ / ρ
  | types_all e κ τ
              (HT : Δ ▹ κ ∣ shift (Inc:=inc) Γ ⊢ e :: τ / ε) :
      Δ ∣ Γ ⊢ e :: [∀] κ, τ / ε
  | types_ins e σ κ τ ρ
              (HK : Δ ⊢ σ :: κ)
              (HT : Δ ∣ Γ ⊢ e :: [∀] κ, τ / ρ) :
      Δ ∣ Γ ⊢ e :: subst (Inc:=inc) τ σ / ρ
  | types_do (v : value V) τ σ₁ σ₂
             (HK  : Δ ⊢ τ :: T)
             (HK₁ : Δ ▹ T ⊢ σ₁ :: T)
             (HK₂ : Δ ▹ T ⊢ σ₂ :: T)
             (HTE : Δ ∣ Γ ⊢ v :: subst (Inc:=inc) σ₁ τ / ε) :
      Δ ∣ Γ ⊢ e_do v :: subst (Inc:=inc) σ₂ τ / [σ₁ ⇒ σ₂] ε
  | types_lift e τ σ₁ σ₂ ρ
               (HK₁ : Δ ▹ T ⊢ σ₁ :: T)
               (HK₂ : Δ ▹ T ⊢ σ₂ :: T)
               (HT  : Δ ∣ Γ ⊢ e :: τ / ρ) :
      Δ ∣ Γ ⊢ e⇑ :: τ / [σ₁ ⇒ σ₂] ρ
  | types_handle e h r τ₁ τ₂ σ₁ σ₂ ρ
                 (HT : Δ ∣ Γ ⊢ e :: τ₁ / [σ₁ ⇒ σ₂] ρ)
                 (HR : Δ ∣ Γ ▹ τ₁ ⊢ r :: τ₂ / ρ)
                 (HH : Δ ▹ T ∣ shift (Inc:=inc) Γ ▹ σ₁ ▹ σ₂ →[shift (Inc:=inc) ρ] shift (Inc:=inc) τ₂ ⊢ h :: shift (Inc:=inc) τ₂ / shift (Inc:=inc) ρ) :
      Δ ∣ Γ ⊢ e_handle_ret e h r :: τ₂ / ρ
  | types_subt e τ₁ τ₂ ρ₁ ρ₂
               (HSE : Δ ⊢ ρ₁ ≲ ρ₂ :: E)
               (HST : Δ ⊢ τ₁ ≲ τ₂ :: T)
               (HT  : Δ ∣ Γ ⊢ e :: τ₁ / ρ₁) :
      Δ ∣ Γ ⊢ e :: τ₂ / ρ₂

  where  " Δ ∣ Γ ⊢ e :: τ / ρ " := (@types _ _ Δ Γ e τ ρ).

End Typing.

Notation " Δ ∣ Γ ⊢ e :: τ / ρ " := (@types _ _ Δ Γ e τ ρ).

Section TypingProperties.

Local Open Scope tp_scope.

Local Open Scope exp_scope.

Definition types_subst {A U V : Set} Δ (Γ₁ : env U A) (Γ₂ : env V A) (γ : @Sub value _ U V) :=
    ∀ x, Δ ∣ Γ₂ ⊢ γ x :: Γ₁ x / r_pure.

Definition xtypes {A V : Set} Δ (Γ : env V A) E τ₁ τ₂ ρ₁ ρ₂ :=
    ∀ (U : Set) Γ' (δ : V [→] U) e (HEq : Γ ≃ Γ' ∘ δ)
      (HT : Δ ∣ Γ' ⊢ e :: τ₁ / ρ₁),
      Δ ∣ Γ' ⊢ fmap δ E [e] :: τ₂ / ρ₂.

End TypingProperties.
