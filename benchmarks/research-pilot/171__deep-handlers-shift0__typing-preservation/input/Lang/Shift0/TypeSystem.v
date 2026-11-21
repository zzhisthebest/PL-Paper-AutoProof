Require Import Utf8.

Require Import Binding.Lib Binding.Set.

Require Export Lang.Shift0.Types.

Require Import RelationClasses Env.

Definition env V A := V → typ A.

Definition tenv (A : Set) := A → kind.

Reserved Notation " Δ ⊢ τ :: κ " (at level 70, τ at level 30, no associativity).

Reserved Notation " Δ ⊢ τ ⇝ τ' " (at level 70, τ, τ' at level 30, no associativity).

Reserved Notation " Δ ⊢ τ ≲ τ' :: κ " (at level 70, τ, τ' at level 30, no associativity).

Reserved Notation " Δ ∣ Γ ⊢ e :: τ / ρ " (at level 70, Γ, e at level 40, τ at level 30, no associativity).

Section WellFormedness.

Local Open Scope typ_scope.

Inductive kinds {A} (Δ : tenv A) : typ A → kind → Prop :=
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
  | k_cons τ ρ ρ'
           (HKτ : Δ ▹ T ▹ E ⊢ τ :: T)
           (HKρ : Δ ▹ T ▹ E ⊢ ρ :: E)
           (HKρ' : Δ ⊢ ρ' :: E) :
      Δ ⊢ [ τ / ρ ] ρ' :: E
  where " Δ ⊢ τ :: κ " := (@kinds _ Δ τ κ).

Definition wf_env {A V : Set} (Δ : tenv A) (Γ : env V A) :=
    ∀ x, Δ ⊢ Γ x :: T.

Definition wf_subst {A B : Set} (Δ₁ : tenv A) (Δ₂ : tenv B) (η : A [⇒] B) :=
    ∀ x, Δ₂ ⊢ η x :: Δ₁ x.

End WellFormedness.

Notation " Δ ⊢ τ :: κ " := (@kinds _ Δ τ κ).

Section Instantiation.

Local Open Scope typ_scope.

Inductive inst_typ {A : Set} (Δ : tenv A) : typ A → typ A → Prop :=
  | inst_id  τ : Δ ⊢ τ ⇝ τ
  | inst_all κ τ₁ τ₂ σ
             (HK  : Δ ⊢ σ :: κ)
             (HGS : Δ ⊢ subst (Inc:=inc) τ₁ σ ⇝ τ₂) :
      (Δ ⊢ [∀] κ, τ₁ ⇝ τ₂)%tp
  where " Δ ⊢ τ ⇝ τ' " := (@inst_typ _ Δ τ τ').

End Instantiation.

Notation " Δ ⊢ τ ⇝ τ' " := (@inst_typ _ Δ τ τ').

Section Subtyping.

Local Open Scope typ_scope.

Inductive subtyp A (Δ : tenv A) : kind → typ A → typ A  → Prop :=
  | st_var x :
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
  | st_cons τ ρ {ρ₁ ρ₂}
            (HSE : Δ ⊢ ρ₁ ≲ ρ₂ :: E) :
      Δ ⊢ [τ / ρ] ρ₁ ≲ [τ / ρ] ρ₂ :: E

  where " Δ ⊢ τ₁ ≲ τ₂ :: κ " := (subtyp _ Δ κ τ₁ τ₂).

End Subtyping.

Notation " Δ ⊢ τ ≲ τ' :: κ " := (subtyp _ Δ κ τ τ').

Require Export Lang.Shift0.Syntax.

Section Typing.

Local Open Scope exp_scope.

Local Open Scope typ_scope.

Inductive types (A V : Set) (Δ : tenv A) (Γ : env V A) : expr V → typ A → typ A → Prop :=
  | types_var x :
      Δ ∣ Γ ⊢ (#x)%exp :: Γ x / ε
  | types_lam e τ₁ τ₂ ρ
              (HK : Δ ⊢ τ₁ :: T)
              (HT : Δ ∣ Γ ▹ τ₁ ⊢ e :: τ₂ / ρ) :
      Δ ∣ Γ ⊢ [λ] e :: τ₁ →[ ρ ] τ₂ / ε
  | types_app e₁ e₂ σ τ ρ
              (HT1 : Δ ∣ Γ ⊢ e₁ :: t_arr σ ρ τ / ρ)
              (HT2 : Δ ∣ Γ ⊢ e₂ :: σ / ρ) :
      Δ ∣ Γ ⊢ e₁ @ e₂ :: τ / ρ
  | types_all e κ τ
              (HT : Δ ▹ κ ∣ shift (Inc:=inc) Γ ⊢ e :: τ / r_pure) :
      Δ ∣ Γ ⊢ e :: [∀] κ, τ / ε
  | types_ins e σ κ τ ρ
              (HK : Δ ⊢ σ :: κ)
              (HT : Δ ∣ Γ ⊢ e :: [∀] κ, τ / ρ) :
      Δ ∣ Γ ⊢ e :: subst (Inc:=inc) τ σ / ρ
  | types_rst e r σ τ τ' ρ ρ'
              (HKτ : Δ ⊢ τ' :: T)
              (HKρ : Δ ⊢ ρ' :: E)
              (HTE : Δ ∣ Γ ⊢ e :: τ / [σ / ρ] subst (Inc:=inc) (subst (Inc:=inc) ρ (shift (Inc:=inc) ρ')) τ')
              (HTR : Δ ∣ Γ ▹ τ ⊢ r :: subst (Inc:=inc) (subst (Inc:=inc) σ (shift (Inc:=inc) ρ')) τ' / subst (Inc:=inc) (subst (Inc:=inc) ρ (shift (Inc:=inc) ρ')) τ') :
      Δ ∣ Γ ⊢ ⟨e ∣ r⟩%exp :: subst (Inc:=inc) (subst (Inc:=inc) σ (shift (Inc:=inc) ρ')) τ' / subst (Inc:=inc) (subst (Inc:=inc) ρ (shift (Inc:=inc) ρ')) τ'
  | types_lift e σ τ ρ ρ'
               (HKσ : Δ ▹ T ▹ E ⊢ σ :: T)
               (HKρ : Δ ▹ T ▹ E ⊢ ρ :: E)
               (HT  : Δ ∣ Γ ⊢ e :: τ / ρ') :
      Δ ∣ Γ ⊢ e⇑ :: τ / [σ / ρ] ρ'
  | types_sft0 e σ τ ρ ρ'
               (HKτ : Δ ⊢ τ :: T)
               (HKρ : Δ ⊢ ρ' :: E)
               (HKσ : Δ ▹ T ▹ E ⊢ σ :: T)
               (HST : Δ ▹ T ▹ E ⊢ shift (Inc:=inc) (shift (Inc:=inc) ρ') ≲ ρ :: E)
               (HT  : Δ ▹ T ▹ E ∣ shift (Inc:=inc) (shift (Inc:=inc) Γ) ▹ shift (Inc:=inc) (shift (Inc:=inc) τ) →[ ρ ] σ ⊢ e :: σ / shift (Inc:=inc) (shift (Inc:=inc) ρ')) :
      Δ ∣ Γ ⊢ e_sft0 e :: τ / [σ / ρ] ρ'
  | types_subt e τ₁ τ₂ ρ₁ ρ₂
               (HSR : Δ ⊢ ρ₁ ≲ ρ₂ :: E)
               (HST : Δ ⊢ τ₁ ≲ τ₂ :: T)
               (HT  : Δ ∣ Γ ⊢ e :: τ₁ / ρ₁) :
      Δ ∣ Γ ⊢ e :: τ₂ / ρ₂

  where  " Δ ∣ Γ ⊢ e :: τ / ρ " := (types _ _ Δ Γ e τ ρ).

End Typing.

Notation " Δ ∣ Γ ⊢ e :: τ / ρ " := (types _ _ Δ Γ e τ ρ).

Section TypingProperties.

Local Open Scope typ_scope.

Local Open Scope exp_scope.

Definition types_subst {A U V : Set} Δ (Γ₁ : env U A) (Γ₂ : env V A) (γ : @Sub value _ U V) :=
    ∀ x, Δ ∣ Γ₂ ⊢ γ x :: Γ₁ x / r_pure.

Definition xtypes {A V : Set} Δ (Γ : env V A) E τ₁ τ₂ ρ₁ ρ₂ :=
    ∀ (U : Set) Γ' (δ : V [→] U) e (HEq : Γ ≃ Γ' ∘ δ)
      (HT : Δ ∣ Γ' ⊢ e :: τ₁ / ρ₁),
      Δ ∣ Γ' ⊢ xplug (fmap δ E) e :: τ₂ / ρ₂.

End TypingProperties.
