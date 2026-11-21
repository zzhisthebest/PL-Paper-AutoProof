Require Import Utf8.

Require Import List.

Class DecEffectEq (Eff : Set) : Set :=
  { dec_effect_eq : ∀ l₁ l₂ : Eff, {l₁ = l₂} + {l₁ ≠ l₂}
  }.

Inductive inc (V : Set) : Set :=
| VZ : inc V
| VS : V → inc V
.

Arguments VZ {V}.

Arguments VS {V}.

Definition extend {A : Set} {B : Type} (f : A → B) (x : B) : inc A → B :=
  λ y, match y with
       | VZ   => x
       | VS z => f z
       end.

Notation "f ',+' x" := (@extend _ _ f x) (at level 45, left associativity).

Inductive effect (Eff EV : Set) : Set :=
| ef_var  : EV → effect Eff EV
| ef_nil  : effect Eff EV
| ef_cons : Eff → effect Eff EV → effect Eff EV
.

Arguments ef_var  {Eff} {EV}.

Arguments ef_nil  {Eff} {EV}.

Arguments ef_cons {Eff} {EV}.

Inductive typ (Eff EV : Set) : Set :=
| t_unit    : typ Eff EV
| t_arrow   : typ Eff EV → effect Eff EV → typ Eff EV → typ Eff EV
| t_forallE : typ Eff (inc EV) → typ Eff EV
.

Arguments t_unit    {Eff} {EV}.

Arguments t_arrow   {Eff} {EV}.

Arguments t_forallE {Eff} {EV}.

Notation typ0 Eff := (typ Eff Empty_set).

Definition Op : Set := nat.

Inductive expr (Eff V : Set) : Set :=
| e_value  : value Eff V → expr Eff V
| e_app    : expr Eff V → expr Eff V → expr Eff V
| e_eapp   : expr Eff V → expr Eff V
| e_lift   : Eff → expr Eff V → expr Eff V
| e_handle :
    Eff → expr Eff V → list (expr Eff (inc (inc V))) → expr Eff (inc V) →
    expr Eff V
with value (Eff V : Set) : Set :=
| v_var  : V → value Eff V
| v_unit : value Eff V
| v_lam  : expr Eff (inc V) → value Eff V
| v_elam : expr Eff V → value Eff V
| v_op   : Eff → Op → value Eff V
.

Arguments e_value  {Eff} {V}.

Arguments e_app    {Eff} {V}.

Arguments e_eapp   {Eff} {V}.

Arguments e_lift   {Eff} {V}.

Arguments e_handle {Eff} {V}.

Arguments v_var  {Eff} {V}.

Arguments v_unit {Eff} {V}.

Arguments v_lam  {Eff} {V}.

Arguments v_elam {Eff} {V}.

Arguments v_op   {Eff} {V}.

Coercion e_value : value >-> expr.

Notation expr0  Eff := (expr  Eff Empty_set).

Notation expr1  Eff := (expr  Eff (inc Empty_set)).

Notation expr2  Eff := (expr  Eff (inc (inc Empty_set))).

Notation value0 Eff := (value Eff Empty_set).

Inductive ectx (Eff V : Set) : Set :=
| x_hole   : ectx Eff V
| x_app1   : ectx Eff V → expr Eff V → ectx Eff V
| x_app2   : value Eff V → ectx Eff V → ectx Eff V
| x_eapp   : ectx Eff V → ectx Eff V
| x_lift   : Eff → ectx Eff V → ectx Eff V
| x_handle :
    Eff → ectx Eff V → list (expr Eff (inc (inc V))) → expr Eff (inc V) →
    ectx Eff V
.

Arguments x_hole   {Eff} {V}.

Arguments x_app1   {Eff} {V}.

Arguments x_app2   {Eff} {V}.

Arguments x_eapp   {Eff} {V}.

Arguments x_lift   {Eff} {V}.

Arguments x_handle {Eff} {V}.

Notation ectx0 Eff := (ectx Eff Empty_set).

Fixpoint plug {Eff V : Set} (E : ectx Eff V) (e : expr Eff V) : expr Eff V :=
  match E with
  | x_hole            => e
  | x_app1 E e'       => plug E (e_app e e')
  | x_app2 v E        => plug E (e_app v e)
  | x_eapp E          => plug E (e_eapp e)
  | x_lift   l E      => plug E (e_lift   l e)
  | x_handle l E h re => plug E (e_handle l e h re)
  end.

Inductive rctx (Eff V : Set) : Set :=
| r_hole   : rctx Eff V
| r_app1   : rctx Eff V → expr Eff V → rctx Eff V
| r_app2   : value Eff V → rctx Eff V → rctx Eff V
| r_eapp   : rctx Eff V → rctx Eff V
| r_lift   : Eff → rctx Eff V → rctx Eff V
| r_handle :
    Eff → rctx Eff V → list (expr Eff (inc (inc V))) → expr Eff (inc V) →
    rctx Eff V
.

Arguments r_hole   {Eff} {V}.

Arguments r_app1   {Eff} {V}.

Arguments r_app2   {Eff} {V}.

Arguments r_eapp   {Eff} {V}.

Arguments r_lift   {Eff} {V}.

Arguments r_handle {Eff} {V}.

Notation rctx0 Eff := (rctx Eff Empty_set).

Fixpoint rplug {Eff V : Set} (E : rctx Eff V) (e : expr Eff V) : expr Eff V :=
  match E with
  | r_hole            => e
  | r_app1 E e'       => e_app (rplug E e) e'
  | r_app2 v E        => e_app v (rplug E e)
  | r_eapp E          => e_eapp (rplug E e)
  | r_lift   l E      => e_lift   l (rplug E e)
  | r_handle l E h re => e_handle l (rplug E e) h re
  end.

Fixpoint rcomp {Eff V : Set} (E E' : rctx Eff V) : rctx Eff V :=
  match E with
  | r_hole            => E'
  | r_app1 E e        => r_app1 (rcomp E E') e
  | r_app2 v E        => r_app2 v (rcomp E E')
  | r_eapp E          => r_eapp (rcomp E E')
  | r_lift   l E      => r_lift   l (rcomp E E')
  | r_handle l E h re => r_handle l (rcomp E E') h re
  end.

Fixpoint xcompr {Eff V : Set} (E₀ : ectx Eff V) (E : rctx Eff V) : ectx Eff V :=
  match E with
  | r_hole            => E₀
  | r_app1 E e        => xcompr (x_app1 E₀ e) E
  | r_app2 v E        => xcompr (x_app2 v E₀) E
  | r_eapp E          => xcompr (x_eapp E₀) E
  | r_lift   l E      => xcompr (x_lift   l E₀) E
  | r_handle l E h re => xcompr (x_handle l E₀ h re) E
  end.

Inductive rfree_g {Eff V : Set} (m : nat) (l : Eff) : nat → rctx Eff V → Prop :=
| RF_hole : rfree_g m l m r_hole
| RF_app1 : ∀ n E e,
    rfree_g m l n E →
    rfree_g m l n (r_app1 E e)
| RF_app2 : ∀ n v E,
    rfree_g m l n E →
    rfree_g m l n (r_app2 v E)
| RF_eapp : ∀ n E,
    rfree_g m l n E →
    rfree_g m l n (r_eapp E)
| RF_lift_e : ∀ n E,
    rfree_g m l n E →
    rfree_g m l (S n) (r_lift l E)
| RF_lift_n : ∀ n l' E,
    l' ≠ l →
    rfree_g m l n E →
    rfree_g m l n (r_lift l' E)
| RF_handle_e : ∀ n E re h,
    rfree_g m l (S n) E →
    rfree_g m l n (r_handle l E re h)
| RF_handle_n : ∀ n l' E h re,
    l' ≠ l →
    rfree_g m l n E →
    rfree_g m l n (r_handle l' E h re)
.

Notation rfree := (rfree_g 0).

Definition rfree_m {Eff V : Set} ρ (E : rctx Eff V) : Prop :=
  ∀ l, match ρ l with
       | None   => True
       | Some n => rfree l n E
       end.

Definition inc_map {A B : Set} (f : A → B) (m : inc A) : inc B :=
  match m with
  | VZ   => VZ
  | VS x => VS (f x)
  end.

Fixpoint fmap {Eff A B : Set} (f : A → B) (ε : effect Eff A) : effect Eff B :=
  match ε with
  | ef_var μ    => ef_var (f μ)
  | ef_nil      => ef_nil
  | ef_cons l ε => ef_cons l (fmap f ε)
  end.

Fixpoint tmap {Eff A B : Set} (f : A → B) (τ : typ Eff A) : typ Eff B :=
  match τ with
  | t_unit          => t_unit
  | t_arrow τ₁ ε τ₂ => t_arrow (tmap f τ₁) (fmap f ε) (tmap f τ₂)
  | t_forallE τ     => t_forallE (tmap (inc_map f) τ)
  end.

Fixpoint emap {Eff A B : Set} (f : A → B) (e : expr Eff A) : expr Eff B :=
  match e with
  | e_value v     => vmap f v
  | e_app e₁ e₂   => e_app (emap f e₁) (emap f e₂)
  | e_eapp e      => e_eapp (emap f e)
  | e_lift   l e  => e_lift l (emap f e)
  | e_handle l e h re =>
    e_handle l (emap f e)
      (map (emap (inc_map (inc_map f))) h) (emap (inc_map f) re)
  end
with vmap {Eff A B : Set} (f : A → B) (v : value Eff A) : value Eff B :=
  match v with
  | v_var x   => v_var (f x)
  | v_unit    => v_unit
  | v_lam e   => v_lam (emap (inc_map f) e)
  | v_elam e  => v_elam (emap f e)
  | v_op l op => v_op l op
  end.

Fixpoint rmap {Eff A B : Set} (f : A → B) (E : rctx Eff A) : rctx Eff B :=
  match E with
  | r_hole       => r_hole
  | r_app1 E e   => r_app1 (rmap f E) (emap f e)
  | r_app2 v E   => r_app2 (vmap f v) (rmap f E)
  | r_eapp E     => r_eapp (rmap f E)
  | r_lift   l E => r_lift l (rmap f E)
  | r_handle l E h re =>
    r_handle l (rmap f E)
      (map (emap (inc_map (inc_map f))) h) (emap (inc_map f) re)
  end.

Definition of_empty {V : Set} (x : Empty_set) : V :=
  match x with
  end.

Notation topen := (tmap of_empty).

Notation fshift  := (fmap (@VS _)).

Notation tshift  := (tmap (@VS _)).

Notation vshift  := (vmap (@VS _)).

Notation eshift1 := (emap (inc_map (@VS _))).

Notation eshift2 := (emap (inc_map (inc_map (@VS _)))).

Notation rshift  := (rmap (@VS _)).

Definition flift {Eff A B : Set} (f : A → effect Eff B) :
    inc A → effect Eff (inc B) :=
  λ x, match x with
       | VZ   => ef_var VZ
       | VS y => fshift (f y)
       end.

Definition lift {Eff A B : Set} (f : A → value Eff B) :
    inc A → value Eff (inc B) :=
  λ x, match x with
       | VZ   => v_var VZ
       | VS y => vshift (f y)
       end.

Fixpoint fbind {Eff A B : Set} (f : A → effect Eff B) (ε : effect Eff A) :
    effect Eff B :=
  match ε with
  | ef_var μ    => f μ
  | ef_nil      => ef_nil
  | ef_cons l ε => ef_cons l (fbind f ε)
  end.

Fixpoint tbind {Eff A B : Set} (f : A → effect Eff B) (τ : typ Eff A) :
    typ Eff B :=
  match τ with
  | t_unit          => t_unit
  | t_arrow τ₁ ε τ₂ => t_arrow (tbind f τ₁) (fbind f ε) (tbind f τ₂)
  | t_forallE τ     => t_forallE (tbind (flift f) τ)
  end.

Fixpoint ebind {Eff A B : Set} (f : A → value Eff B) (e : expr Eff A) :
    expr Eff B :=
  match e with
  | e_value v         => vbind f v
  | e_app e₁ e₂       => e_app (ebind f e₁) (ebind f e₂)
  | e_eapp e          => e_eapp (ebind f e)
  | e_lift   l e      => e_lift l (ebind f e)
  | e_handle l e h re =>
    e_handle l (ebind f e) (map (ebind (lift (lift f))) h) (ebind (lift f) re)
  end
with vbind {Eff A B : Set} (f : A → value Eff B) (v : value Eff A) :
    value Eff B :=
  match v with
  | v_var x   => f x
  | v_unit    => v_unit
  | v_lam e   => v_lam (ebind (lift f) e)
  | v_elam e  => v_elam (ebind f e)
  | v_op l op => v_op l op
  end.

Fixpoint rbind {Eff A B : Set} (f : A → value Eff B) (E : rctx Eff A)
    : rctx Eff B :=
  match E with
  | r_hole            => r_hole
  | r_app1 E e        => r_app1 (rbind f E) (ebind f e)
  | r_app2 v E        => r_app2 (vbind f v) (rbind f E)
  | r_eapp E          => r_eapp (rbind f E)
  | r_lift   l E      => r_lift l (rbind f E)
  | r_handle l E h re =>
    r_handle l (rbind f E) (map (ebind (lift (lift f))) h) (ebind (lift f) re)
  end.

Definition fsubst_func {Eff EV : Set} (ε : effect Eff EV) (x : inc EV) :
    effect Eff EV :=
  match x with
  | VZ   => ε
  | VS y => ef_var y
  end.

Definition subst_func {Eff V : Set} (v : value Eff V) (x : inc V) :
    value Eff V :=
  match x with
  | VZ   => v
  | VS y => v_var y
  end.

Definition bisubst_func {Eff V : Set} (v1 v2 : value Eff V) (x : inc (inc V)) :
    value Eff V :=
  match x with
  | VZ        => v2
  | VS VZ     => v1
  | VS (VS y) => v_var y
  end.

Notation fsubst ε' ε := (fbind (fsubst_func ε) ε').

Notation tsubst τ  ε := (tbind (fsubst_func ε) τ).

Notation esubst  e v := (ebind (subst_func v) e).

Notation esubst1 e v := (ebind (lift (subst_func v)) e).

Notation esubst2 e v := (ebind (lift (lift (subst_func v))) e).

Notation ebisubst e v1 v2 := (ebind (bisubst_func v1 v2) e).

Notation vsubst v₀ v := (vbind (subst_func v) v₀).

Notation vbisubst v v1 v2 := (vbind (bisubst_func v1 v2) v).

Notation rsubst E v := (rbind (subst_func v) E).
