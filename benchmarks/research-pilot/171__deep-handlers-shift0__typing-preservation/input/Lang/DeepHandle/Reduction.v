Require Import Utf8.

Require Import Binding.Lib.

Require Import Lang.DeepHandle.Syntax.

Reserved Notation "e ↦ e'" (at level 70, no associativity).

Reserved Notation "e '–→' e'" (at level 70, no associativity).

Local Open Scope exp_scope.

Inductive contr {V : Set} : expr V → expr V → Prop :=
| contr_beta : ∀ (e : expr (inc V)) (v : value V),
    ([λ] e) @ v ↦ subst (Inc:=inc) e v
| contr_do_handle : ∀ (E : ectx V) (v : value V) (h : expr (inc (inc V))),
    xfree 0 E →
    e_handle (xplug E (e_do v)) h ↦
             subst (Inc:=inc) (subst (Inc:=inc) h (shift (Inc:=inc) ([λ] e_handle (shift (Inc:=inc) E [# VZ]) (fmap (liftA (G:=inc) (liftA (G:=inc) (mk_shift (Inc:=inc)))) h)))) v
| contr_do_handle_ret : ∀ (E : ectx V) (v vr : value V) (h : expr (inc (inc V))) r,
    vr = [λ] e_handle_ret (shift (Inc:=inc) E [#VZ]) (fmap (liftA (G:=inc) (liftA (G:=inc) (mk_shift (Inc:=inc)))) h) (fmap (liftA (G:=inc) (mk_shift (Inc:=inc))) r) →
    xfree 0 E →
    e_handle_ret (E [e_do v]) h r ↦ subst (Inc:=inc) (subst (Inc:=inc) h (shift (Inc:=inc) vr)) v
| contr_handle : ∀ (v : value V) h,
    e_handle v h ↦ v
| contr_handle_ret : ∀ (v : value V) h (r : expr (inc V)),
    e_handle_ret v h r ↦ subst (Inc:=inc) r v
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
| red_handle : ∀ e₁ e₂ h,
    e₁ –→ e₂ →
    e_handle e₁ h –→ e_handle e₂ h
| red_handle_ret : ∀ e₁ e₂ h r,
    e₁ –→ e₂ →
    e_handle_ret e₁ h r –→ e_handle_ret e₂ h r
| red_lift : ∀ e₁ e₂, e₁ –→ e₂ →
    e₁⇑ –→ e₂⇑
where "e –→ e'" := (red e e').

Require Import Relations.

Notation red_rtc := (@clos_refl_trans_1n _ red).

Inductive red_tc {V : Set} (e₁ e₂ : expr V) : Prop :=
| red_tc_step : ∀ e, red e₁ e → red_rtc e e₂ → red_tc e₁ e₂
.

Notation "e –→⁺ e'" := (red_tc e e') (at level 70, no associativity).

Notation "e –→* e'" := (red_rtc e e') (at level 70, no associativity).
