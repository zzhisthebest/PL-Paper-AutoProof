Require Import Utf8.

Require Import Binding.Lib Binding.Intrinsic Binding.Auto.

Require Import FOmegaEq.Kinds.

Inductive type {Δ : Ctx kind} : kind → Type :=
| t_var κ (x : dom Δ) (EQ : Δ x = κ) : type κ
| t_lam {κₐ κᵣ} (τ : @type (Δ ▹ κₐ) κᵣ) : type (κₐ ⇒ κᵣ)
| t_app {κₐ κᵣ} (σ : type (κₐ ⇒ κᵣ)) (τ : type κₐ) : type κᵣ
| t_ctor {κ} (c : tctor κ) : type κ
| t_carr  (ψ : constr) (τ : type ⋆) : type ⋆
| t_cprod (ψ : constr) (τ : type ⋆) : type ⋆
with constr {Δ : Ctx kind} : Type :=
| c_eq (κ : kind) (τ₁ τ₂ : type κ) : constr.

Arguments type Δ : clear implicits.

Arguments constr Δ : clear implicits.

Require Import Basics.

Definition typ := flip type.

Declare Scope typ_scope.

Delimit Scope typ_scope with typ.

Coercion t_ctor : tctor >-> type.

Coercion t_app : type >-> Funclass.

Definition rec_type (Δ : Ctx kind) (κ : kind) (τ : typ κ (extC κ Δ)) : typ κ Δ
  := (tc_rec κ) (t_lam τ).

Definition t_arr {Δ} (τ₁ τ₂ : typ ⋆ Δ) : typ ⋆ Δ :=
  tc_arr τ₁ τ₂.

Definition t_prod {Δ} (τ₁ τ₂ : typ ⋆ Δ) : typ ⋆ Δ :=
  tc_prod τ₁ τ₂.

Definition t_sum {Δ} (τ₁ τ₂ : typ ⋆ Δ) : typ ⋆ Δ :=
  tc_sum τ₁ τ₂.

Definition t_all {Δ} κ (τ : typ ⋆ (extC κ Δ)) :=
  (tc_all κ) (t_lam τ).

Definition t_xist {Δ} κ (τ : typ ⋆ (extC κ Δ)) :=
  (tc_xist κ) (t_lam τ).

Notation "'ƛ' τ" := (t_lam τ : typ _ _) (at level 60) : typ_scope.

Notation "σ →ᵗ τ" := (t_arr σ τ) (at level 55, right associativity) : typ_scope.

Notation "τ₁ + τ₂" := (t_sum τ₁ τ₂) (at level 50, left associativity) : typ_scope.

Notation "τ₁ × τ₂" := (t_prod τ₁ τ₂) (at level 40, left associativity) : typ_scope.

Notation "χ →ᶜ τ" := (t_carr χ τ) (at level 55, right associativity) : typ_scope.

Notation "χ ×ᶜ τ" := (t_cprod χ τ) (at level 40, left associativity) : typ_scope.

Notation "τ₁ ≃ τ₂" := (c_eq _ τ₁ τ₂) (at level 65, no associativity) : typ_scope.

Notation "∀ᵗ κ , τ" := (t_all κ τ) (at level 60) : typ_scope.

Notation "∃ᵗ κ , τ" := (t_xist κ τ) (at level 60) : typ_scope.

Notation "⊥" := tc_void : typ_scope.

Notation "'⊤'" := tc_unit : typ_scope.

Notation "'0ᵛ'" := (t_var _ (VZ : dom (_ ▹ _)) eq_refl).

Local Open Scope bind_scope.

Local Open Scope typ_scope.

Fixpoint tmap {κ} {Δ₁ Δ₂ : Ctx kind} (δ : Δ₁ [→] Δ₂) (τ : typ κ Δ₁) : typ κ Δ₂ :=
  match τ with
  | t_var κ x EQ => t_var κ (δ x) (eq_trans (arr_hom δ x) EQ)
  | t_lam τ => ƛ tmap (δ ↑) τ
  | t_app σ τ => (tmap δ σ) (tmap δ τ)
  | t_ctor c  => c
  | φ →ᶜ τ => cmap δ φ →ᶜ tmap δ τ
  | φ ×ᶜ τ => cmap δ φ ×ᶜ tmap δ τ
  end
with cmap {Δ₁ Δ₂ : Ctx kind} (δ : Δ₁ [→] Δ₂) (φ : constr Δ₁) : constr Δ₂ :=
  match φ with
  | c_eq κ τ₁ τ₂ => c_eq κ (tmap δ τ₁) (tmap δ τ₂)
  end.

#[export] Instance IPC_typ : IntPureCore (λ κ, typ κ) := @t_var.

#[export] Instance FMap_typ {κ} : FunctorCore (typ κ) := @tmap κ.

#[export] Instance FMap_constr : FunctorCore constr := @cmap.

Fixpoint tbind {κ} {Δ₁ Δ₂ : Ctx kind} (ρ : Δ₁ [⇒] Δ₂) (τ : typ κ Δ₁) : typ κ Δ₂ :=
  match τ with
  | t_var κ x EQ  => ρ κ x EQ
  | t_lam τ     => ƛ (tbind (ρ ↑) τ)
  | t_app σ τ   => (tbind ρ σ) (tbind ρ τ)
  | t_ctor c    => c
  | t_carr  φ τ => cbind ρ φ →ᶜ tbind ρ τ
  | t_cprod φ τ => cbind ρ φ ×ᶜ tbind ρ τ
  end
with cbind {Δ₁ Δ₂ : Ctx kind} (ρ : Δ₁ [⇒] Δ₂) (φ : constr Δ₁) : constr Δ₂ :=
  match φ with
  | c_eq κ τ₁ τ₂ => c_eq κ (tbind ρ τ₁) (tbind ρ τ₂)
  end.

#[export] Instance BindT {κ} : BindCore (typ κ) := @tbind κ.

#[export] Instance BindC : BindCore constr := @cbind.

Inductive rel_app {Δ : Ctx kind} (κ₁ : kind) (σ₁ σ₂ : typ κ₁ Δ) : ∀ κ₂, typ κ₂ Δ → typ κ₂ Δ → Prop :=
| rel_app_refl : rel_app κ₁ σ₁ σ₂ κ₁ σ₁ σ₂
| rel_app_app {κₐ κᵣ} (τ₁ τ₂ : typ (κₐ ⇒ κᵣ) Δ) (τ : typ κₐ Δ)
    (HF : rel_app κ₁ σ₁ σ₂ (κₐ ⇒ κᵣ) τ₁ τ₂) :
  rel_app κ₁ σ₁ σ₂ κᵣ (τ₁ τ) (τ₂ τ).

Require Import List.

Inductive tctd {Δ : Ctx kind} {κ} : typ κ Δ → ∀ {κ'}, tctor κ' → Prop :=
| inj_ctor c : tctd (t_ctor c) c
| inj_app {κₐ κ'} (σ : typ (κₐ ⇒ κ) Δ) τ (c : tctor κ') (HI : tctd σ c) : tctd (σ τ) c.

Inductive cdiscr : ∀ {κ}, tctor κ → tctor κ → Prop :=
| cd_unit_void : cdiscr tc_unit tc_void
| cd_void_unit : cdiscr tc_void tc_unit
| cd_all_xist κ : cdiscr (tc_all κ)  (tc_xist κ)
| cd_xist_all κ : cdiscr (tc_xist κ) (tc_all κ)
| cd_all_rec    : cdiscr (tc_all ⋆)  (tc_rec ⋆)
| cd_rec_all    : cdiscr (tc_rec ⋆)  (tc_all ⋆)
| cd_xist_rec   : cdiscr (tc_xist ⋆) (tc_rec ⋆)
| cd_rec_xist   : cdiscr (tc_rec ⋆)  (tc_xist ⋆)
| cd_arr_sum  : cdiscr tc_arr  tc_sum
| cd_sum_arr  : cdiscr tc_sum  tc_arr
| cd_arr_prod : cdiscr tc_arr  tc_prod
| cd_prod_arr : cdiscr tc_prod tc_arr
| cd_prod_sum : cdiscr tc_prod tc_sum
| cd_sum_prod : cdiscr tc_sum  tc_prod.

Definition cdiscrK {κ₁ κ₂} : tctor κ₁ → tctor κ₂ → Prop :=
  match kindEqDec.eq_dec κ₁ κ₂ with
  | left EQ =>
      eq_rect κ₁ (λ κ : kindEqDec.U, tctor κ₁ → tctor κ → Prop) cdiscr κ₂ EQ
  | right NEQ => λ _ _, True
  end.

Inductive tdiscr {Δ : Ctx kind} : constr Δ → Prop :=
| td_ctd {κ κ₁ κ₂ τ₁ τ₂} {c₁ : tctor κ₁} {c₂ : tctor κ₂}
         (HI₁ : tctd τ₁ c₁)
         (HI₂ : tctd τ₂ c₂)
         (HD : cdiscrK c₁ c₂) :
  tdiscr (c_eq κ τ₁ τ₂)
| td_carr_ctd {ψ τ σ κ} {c : tctor κ}
              (HI : tctd σ c) :
  tdiscr (c_eq ⋆ (t_carr ψ τ) σ)
| td_ctd_carr {ψ τ σ κ} {c : tctor κ}
              (HI : tctd σ c) :
  tdiscr (c_eq ⋆ σ (t_carr ψ τ))
| td_cprod_ctd {ψ τ σ κ} {c : tctor κ}
               (HI : tctd σ c) :
  tdiscr (c_eq ⋆ (t_cprod ψ τ) σ)
| td_ctd_cprod {ψ τ σ κ} {c : tctor κ}
               (HI : tctd σ c) :
  tdiscr (c_eq ⋆ σ (t_cprod ψ τ))
| td_carr_cprod {ψ₁ ψ₂ τ₁ τ₂} :
    tdiscr (c_eq ⋆ (t_carr ψ₁ τ₁) (t_cprod ψ₂ τ₂))
| td_cprod_carr {ψ₁ ψ₂ τ₁ τ₂} :
    tdiscr (c_eq ⋆ (t_cprod ψ₂ τ₂) (t_carr ψ₁ τ₁)).

Notation "⊮ ψ" := (tdiscr ψ%typ) (at level 70).

Arguments tdiscr {Δ} ψ%typ.

Reserved Notation "Ψ ⊩ ψ" (at level 70, no associativity).

Inductive tproves_i {Δ : Ctx kind} {Ψ : list (constr Δ)} : constr Δ → Prop :=
| tpi_ax ψ (HIn : In ψ Ψ) : Ψ ⊩ ψ
| tpi_var {κ x EQ₁ EQ₂} : Ψ ⊩ t_var κ x EQ₁ ≃ t_var κ x EQ₂
| tpi_lam {κₐ κᵣ} {τ₁ τ₂ : typ κᵣ (Δ ▹ κₐ)} (HP : map shift Ψ ⊩ τ₁ ≃ τ₂) :
    Ψ ⊩ ƛ τ₁ ≃ ƛ τ₂
| tpi_app {κₐ κᵣ} {σ₁ σ₂ : typ (κₐ ⇒ κᵣ) Δ} {τ₁ τ₂}
          (HP₁ : Ψ ⊩ σ₁ ≃ σ₂)
          (HP₂ : Ψ ⊩ τ₁ ≃ τ₂) :
    Ψ ⊩ σ₁ τ₁ ≃ σ₂ τ₂
| tpi_ctor {κ} (c : tctor κ) : Ψ ⊩ c ≃ c
| tpi_carr {ψ τ₁ τ₂} (HP : Ψ ⊩ τ₁ ≃ τ₂) :
    Ψ ⊩ ψ →ᶜ τ₁ ≃ ψ →ᶜ τ₂
| tpi_cprod {ψ τ₁ τ₂} (HP : Ψ ⊩ τ₁ ≃ τ₂) :
    Ψ ⊩ ψ ×ᶜ τ₁ ≃ ψ ×ᶜ τ₂
| tpi_symm {κ} {τ₁ τ₂ : typ κ Δ} (HP : Ψ ⊩ τ₁ ≃ τ₂) :
    Ψ ⊩ τ₂ ≃ τ₁
| tpi_trans {κ} {τ₁ τ₂ τ₃ : typ κ Δ}
            (HP₁ : Ψ ⊩ τ₁ ≃ τ₂)
            (HP₂ : Ψ ⊩ τ₂ ≃ τ₃) :
    Ψ ⊩ τ₁ ≃ τ₃
| tpi_eta {κₐ κᵣ} (τ : typ (κₐ ⇒ κᵣ) Δ) :
    Ψ ⊩ τ ≃ ƛ shift τ 0ᵛ
| tpi_beta {κₐ κᵣ} (σ : typ κₐ Δ) (τ : typ κᵣ (Δ ▹ κₐ)) :
    Ψ ⊩ (ƛ τ) σ ≃ subst τ σ
| tpi_appInjR {κₐ κᵣ κ} {σ₁ σ₂ : typ (κₐ ⇒ κᵣ) Δ} {c : tctor κ} {τ₁ τ₂ : typ κₐ Δ}
              (HI₁ : tctd σ₁ c)
              (HI₂ : tctd σ₂ c)
              (HP : Ψ ⊩ σ₁ τ₁ ≃ σ₂ τ₂) :
    Ψ ⊩ τ₁ ≃ τ₂
| tpi_appInjL {κₐ κᵣ κ} {σ₁ σ₂ : typ (κₐ ⇒ κᵣ) Δ} {c : tctor κ} {τ₁ τ₂ : typ κₐ Δ}
              (HI₁ : tctd σ₁ c)
              (HI₂ : tctd σ₂ c)
              (HP : Ψ ⊩ σ₁ τ₁ ≃ σ₂ τ₂) :
    Ψ ⊩ σ₁ ≃ σ₂
| tpi_carrInjR {ψ₁ ψ₂ τ₁ τ₂}
                (HP : Ψ ⊩ ψ₁ →ᶜ τ₁ ≃ ψ₂ →ᶜ τ₂) :
    Ψ ⊩ (c_eq ⋆ τ₁ τ₂)
| tpi_cprodInjR {ψ₁ ψ₂ τ₁ τ₂}
                (HP : Ψ ⊩ ψ₁ ×ᶜ τ₁ ≃ ψ₂ ×ᶜ τ₂) :
    Ψ ⊩ τ₁ ≃ τ₂
| tpi_cprodInjL {ψ₁ ψ₂ τ₁ τ₂}
    (HP : Ψ ⊩ ψ₁ ×ᶜ τ₁ ≃ ψ₂ ×ᶜ τ₂) :
    Ψ ⊩ ψ₁ -> Ψ ⊩ ψ₂
| tpi_carrInjL {ψ₁ ψ₂ τ₁ τ₂}
    (HP : Ψ ⊩ ψ₁ →ᶜ τ₁ ≃ ψ₂ →ᶜ τ₂) :
  Ψ ⊩ ψ₁ -> Ψ ⊩ ψ₂
where "Ψ ⊩ ψ" := (@tproves_i _ Ψ%typ ψ%typ).

Arguments tproves_i {Δ} Ψ%typ φ%typ.

Require Import RelationClasses.

Class Separable {A : Type} (R : A → A → Prop) :=
  sep : ∀ {x y} z, R x y → R x z ∨ R z y.

Definition tequiv {Δ κ} Ψ (τ₁ τ₂ : typ κ Δ) := tproves_i Ψ (c_eq κ τ₁ τ₂).

Arguments tequiv {_ _} _ _ _ /.
