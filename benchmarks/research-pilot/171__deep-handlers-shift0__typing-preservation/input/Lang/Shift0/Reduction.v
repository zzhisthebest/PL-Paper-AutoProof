Require Import Utf8.

Require Import Binding.Lib.

Require Import Lang.Shift0.Syntax.

Reserved Notation "e ↦ e'" (at level 70, no associativity).

Reserved Notation "e '–→' e'" (at level 70, no associativity).

Reserved Notation "e '→ᵢ' e'" (at level 70, no associativity).

Local Open Scope exp_scope.

Inductive contr {V : Set} : expr V → expr V → Prop :=
| contr_beta : ∀ (e : expr (inc V)) (v : value V),
    ([λ] e) @ v ↦ subst (Inc:=inc) e v
| contr_sft0_rst : ∀ (E : ectx V) (e : expr (inc V)),
    xfree 0 E →
    ⟨ E [e_sft0 e] ⟩ ↦ subst (Inc:=inc) e ([λ] ⟨shift (Inc:=inc) E [#VZ]⟩)
| contr_sft0_rst_ret : ∀ (E : ectx V) (e : expr (inc V)) (e' : expr (inc V)),
    xfree 0 E →
    ⟨ E [e_sft0 e] ∣ e' ⟩ ↦ subst (Inc:=inc) e ([λ] ⟨shift (Inc:=inc) E [#VZ] ∣ fmap (liftA (G:=inc) (mk_shift (Inc:=inc))) e'⟩)
| contr_rst : ∀ (v : value V),
    ⟨v⟩ ↦ v
| contr_rst_ret : ∀ (v : value V) (e : expr (inc V)),
    ⟨v ∣ e⟩ ↦ subst (Inc:=inc) e v
| contr_lift : ∀ (v : value V),
    v⇑ ↦ v
where "e ↦ e'" := (contr e e').

Inductive red {V : Set} : expr V → expr V → Prop :=
| red_contr : ∀ e₁ e₂,
    e₁ ↦ e₂ →
    e₁ –→ e₂
| red_app1 : ∀ e₁ e₂ e,
    e₁ –→ e₂ →
    e₁ @ e –→ e₂ @ e
| red_app2 : ∀ (v : value V) e₁ e₂,
    e₁ –→ e₂ →
    v @ e₁ –→ v @ e₂
| red_rst : ∀ e₁ e₂,
    e₁ –→ e₂ →
    ⟨e₁⟩ –→ ⟨e₂⟩
| red_rst_ret : ∀ e₁ e₂ e,
    e₁ –→ e₂ →
    ⟨e₁ ∣ e⟩ –→ ⟨e₂ ∣ e⟩
| red_lift : ∀ e₁ e₂,
    e₁ –→ e₂ →
    e₁⇑ –→ e₂⇑
where "e –→ e'" := (red e e').

Inductive redi {V : Set} : expr V → expr V → Prop :=
| redi_contr (e₁ e₂ : expr V) (HC : e₁ ↦ e₂) :
    e₁ →ᵢ e₂
| redi_appL (e₁ e₂ e : expr V) (HR : e₁ →ᵢ e₂) :
    e₁ @ e →ᵢ e₂ @ e
| redi_appR (e₁ e₂ e : expr V) (HR : e₁ →ᵢ e₂) :
    e @ e₁ →ᵢ e @ e₂
| redi_lam (e₁ e₂ : expr (inc V)) (HR : e₁ →ᵢ e₂) :
    [λ] e₁ →ᵢ [λ] e₂
| redi_rst (e₁ e₂ : expr V) (HR : e₁ →ᵢ e₂) :
    ⟨e₁⟩ →ᵢ ⟨e₂⟩
| redi_rst_retL (e₁ e₂ : expr V) r (HR : e₁ →ᵢ e₂) :
    ⟨e₁ ∣ r⟩ →ᵢ ⟨e₂ ∣ r⟩
| redi_rst_retR (e : expr V) r₁ r₂ (HR : r₁ →ᵢ r₂) :
    ⟨e ∣ r₁⟩ →ᵢ ⟨e ∣ r₂⟩
| redi_lift (e₁ e₂ : expr V) (HR : e₁ →ᵢ e₂) :
    e₁⇑ →ᵢ e₂⇑
| redi_sft0 (e₁ e₂ : expr (inc V)) (HR : e₁ →ᵢ e₂) :
    e_sft0 e₁ →ᵢ e_sft0 e₂

where "e₁ →ᵢ e₂" := (@redi _ e₁ e₂).

Require Import Relations RelationClasses.

Notation red_rtc := (@clos_refl_trans_1n _ red).

Inductive red_tc {V : Set} (e₁ e₂ : expr V) : Prop :=
| red_tc_step : ∀ e, red e₁ e → red_rtc e e₂ → red_tc e₁ e₂
.

Notation "e –→⁺ e'" := (red_tc e e') (at level 70, no associativity).

Notation "e –→* e'" := (red_rtc e e') (at level 70, no associativity).

Notation "e →ᵢ* e'" := (@clos_refl_trans_1n _ redi e e') (at level 70, no associativity).

Reserved Notation "e →ᵢ⁺ e'" (at level 70, no associativity).

Inductive redi_tc {V : Set} (e₁ e₃ : expr V) : Prop :=
| redi_tc_step e₂ (HR : e₁ →ᵢ e₂) (HRC : e₂ →ᵢ* e₃) :
    e₁ →ᵢ⁺ e₃
where "e →ᵢ⁺ e'" := (redi_tc e e').
