Require Import Utf8.

Require Import Lang.Syntax.

Require Import List.

Inductive handler {Eff V : Set} (he : expr Eff (inc (inc V))) :
    list (expr Eff (inc (inc V))) → Op → Prop :=
| H_0 : ∀ h, handler he (he :: h) 0
| H_S : ∀ e h op, handler he h op → handler he (e :: h) (S op)
.

Inductive red {Eff : Set} :
    expr0 Eff → expr0 Eff → Prop :=
| red_beta : ∀ (e : expr1 Eff) (v : value0 Eff),
    red (e_app (v_lam e) v) (esubst e v)
| red_ebeta : ∀ (e : expr0 Eff),
    red (e_eapp (v_elam e)) e
| red_lift_val : ∀ l (v : value0 Eff),
    red (e_lift l v) v
| red_handle_val : ∀ l (v : value0 Eff) h (re : expr1 Eff),
    red (e_handle l v h re) (esubst re v)
| red_handle_op : ∀ l E op (v : value0 Eff) h re (he : expr2 Eff),
    rfree l 0 E →
    handler he h op →
    red (e_handle l (rplug E (e_app (v_op l op) v)) h re)
        (ebisubst he v (v_lam (e_handle l
          (rplug (rshift E) (v_var VZ))
          (map eshift2 h)
          (eshift1 re))))
| red_app1 : ∀ e e' e₂,
    red e e' →
    red (e_app e e₂) (e_app e' e₂)
| red_app2 : ∀ (v : value0 Eff) e e',
    red e e' →
    red (e_app v e) (e_app v e')
| red_eapp : ∀ e e',
    red e e' →
    red (e_eapp e) (e_eapp e')
| red_lift : ∀ l e e',
    red e e' →
    red (e_lift l e) (e_lift l e')
| red_handle : ∀ l e e' re h,
    red e e' →
    red (e_handle l e re h) (e_handle l e' re h)
.

Require Import Relation_Operators.

Notation red_rtc := (@clos_refl_trans_1n _ red).

Inductive red_n {Eff : Set} : nat → expr0 Eff → expr0 Eff → Prop :=
| red_n_0 : ∀ e, red_n 0 e e
| red_n_S : ∀ n e₁ e₂ e₃,
    red e₁ e₂ →
    red_n n e₂ e₃ →
    red_n (S n) e₁ e₃
.

Definition irred {Eff : Set} (e : expr0 Eff) : Prop :=
  ∀ e', red e e' → False.
