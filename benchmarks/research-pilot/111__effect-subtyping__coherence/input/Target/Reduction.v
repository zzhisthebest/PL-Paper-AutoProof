From Stdlib Require Import Utf8.
Require Import Common.Metatheory Target.Syntax.

Inductive beta_step : exp0 → exp0 → Prop :=
| Beta_abs    : ∀ e v r,
    value v →
    r = subst e v →
    beta_step (exp_app (exp_abs e) v) r
| Beta_lift   : ∀ c v k,
    value v →
    value k →
    beta_step (exp_app (exp_capp (crc_lift c) v) k)
      (exp_capp c (exp_app k v))
| Beta_fix    : ∀ e v r,
    value v →
    r = subst (subst e (weaken v)) (exp_fix e) →
    beta_step (exp_app (exp_fix e) v) r
| Beta_succ   : ∀ m,
    beta_step (exp_succ (exp_const m)) (exp_const (S m))
| Beta_case_Z : ∀ e₁ e₂,
    beta_step (exp_case (exp_const 0) e₁ e₂) e₁
| Beta_case_S : ∀ m e₁ e₂ r,
    r = subst e₂ (exp_const m) →
    beta_step (exp_case (exp_const (S m)) e₁ e₂) r
.

Inductive iota_step : exp0 → exp0 → Prop :=
| Iota_id    : ∀ v,
    value v →
    iota_step (exp_capp crc_id v) v
| Iota_comp  : ∀ c₁ c₂ v,
    value v →
    iota_step (exp_capp (crc_comp c₁ c₂) v)
      (exp_capp c₁ (exp_capp c₂ v))
| Iota_arrow : ∀ c₁ c₂ f v,
    value f →
    value v →
    iota_step (exp_app (exp_capp (crc_arrow c₁ c₂) f) v)
      (exp_capp c₂ (exp_app f (exp_capp c₁ v)))
| Iota_cons : ∀ c c₁ c₂ v k,
    value v →
    value k →
    iota_step (exp_app (exp_capp (crc_cons c c₁ c₂) v) k)
      (exp_capp c₂ (exp_app v (exp_capp (crc_arrow c c₁) k)))
.

Section ContextCl.

Variable R : exp0 → exp0 → Prop.

Inductive ctx_cl : exp0 → exp0 → Prop :=
| CC_hole  : ∀ e₁ e₂, R e₁ e₂ → ctx_cl e₁ e₂
| CC_app1  : ∀ e₁ e₂ e,
    ctx_cl e₁ e₂ → ctx_cl (exp_app e₁ e) (exp_app e₂ e)
| CC_app2  : ∀ v e₁ e₂,
    value v →
    ctx_cl e₁ e₂ → ctx_cl (exp_app v e₁) (exp_app v e₂)
| CC_capp  : ∀ c e₁ e₂,
    ctx_cl e₁ e₂ → ctx_cl (exp_capp c e₁) (exp_capp c e₂)
| CC_succ  : ∀ e₁ e₂,
    ctx_cl e₁ e₂ → ctx_cl (exp_succ e₁) (exp_succ e₂)
| CC_case  : ∀ e₁ e₂ f₁ f₂,
    ctx_cl e₁ e₂ → ctx_cl (exp_case e₁ f₁ f₂) (exp_case e₂ f₁ f₂)
.

End ContextCl.

Definition beta : exp0 → exp0 → Prop :=
  ctx_cl beta_step.
Definition iota : exp0 → exp0 → Prop :=
  ctx_cl iota_step.


Inductive stops (e : exp0) : Prop :=
| StopsValue : value e → stops e
| StopsBeta  : ∀ e', beta e e' → stops e' → stops e
| StopsIota  : ∀ e', iota e e' → stops e' → stops e
.
