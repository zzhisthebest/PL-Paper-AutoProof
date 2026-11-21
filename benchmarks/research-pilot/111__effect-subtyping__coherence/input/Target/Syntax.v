From Stdlib Require Import Utf8.
Require Import Common.Metatheory.

Inductive crc : Set :=
| crc_id    : crc
| crc_comp  : crc → crc → crc
| crc_arrow : crc → crc → crc
| crc_lift  : crc → crc
| crc_cons  : crc → crc → crc → crc
.

Inductive exp (V : Set) : Set :=
| exp_var   : V → exp V
| exp_const : nat → exp V
| exp_abs   : exp (inc V) → exp V
| exp_app   : exp V → exp V → exp V
| exp_capp  : crc → exp V → exp V
| exp_fix   : exp (inc (inc V)) → exp V
| exp_succ  : exp V → exp V
| exp_case  : exp V → exp V → exp (inc V) → exp V
.

Arguments exp_var   [V] _.
Arguments exp_const [V] _.
Arguments exp_abs   [V] _.
Arguments exp_app   [V] _ _.
Arguments exp_capp  [V] _ _.
Arguments exp_fix   [V] _.
Arguments exp_succ  [V] _.
Arguments exp_case  [V] _ _ _.

Definition exp0 : Set := exp empty.
Definition exp1 : Set := exp (inc empty).
Definition exp2 : Set := exp (inc (inc empty)).

Inductive ctx : Set → Type :=
| ctx_hole  : ctx empty
| ctx_abs   : ∀ V, ctx V → ctx (inc V)
| ctx_app1  : ∀ V, ctx V → exp V → ctx V
| ctx_app2  : ∀ V, exp V → ctx V → ctx V
| ctx_capp  : ∀ V, crc → ctx V → ctx V
| ctx_fix   : ∀ V, ctx V → ctx (inc (inc V))
| ctx_succ  : ∀ V, ctx V → ctx V
| ctx_case  : ∀ V, ctx V → exp V → exp (inc V) → ctx V
| ctx_case1 : ∀ V, exp V → ctx V → exp (inc V) → ctx V
| ctx_case2 : ∀ V, exp V → exp V → ctx V → ctx (inc V)
.

Arguments ctx_abs   [V] _.
Arguments ctx_app1  [V] _ _.
Arguments ctx_app2  [V] _ _.
Arguments ctx_capp  [V] _ _.
Arguments ctx_fix   [V] _.
Arguments ctx_succ  [V] _.
Arguments ctx_case  [V] _ _ _.
Arguments ctx_case1 [V] _ _ _.
Arguments ctx_case2 [V] _ _ _.


Inductive value : exp0 → Prop :=
| Val_const      : ∀ m, value (exp_const m)
| Val_abs        : ∀ e, value (exp_abs e)
| Val_capp_arrow : ∀ c₁ c₂ v,
    value v →
    value (exp_capp (crc_arrow c₁ c₂) v)
| Val_capp_lift  : ∀ c v,
    value v →
    value (exp_capp (crc_lift c) v)
| Val_capp_cons  : ∀ c c₁ c₂ v,
    value v →
    value (exp_capp (crc_cons c c₁ c₂) v)
| Val_fix        : ∀ e, value (exp_fix e)
.


Inductive open_value {V : Set} : exp V → Prop :=
| OVal_var   : ∀ x, open_value (exp_var x)
| OVal_const : ∀ m, open_value (exp_const m)
| OVal_abs   : ∀ e, open_value (exp_abs e)
| OVal_capp_arrow : ∀ c₁ c₂ v,
    open_value v →
    open_value (exp_capp (crc_arrow c₁ c₂) v)
| OVal_capp_lift  : ∀ c v,
    open_value v →
    open_value (exp_capp (crc_lift c) v)
| OVal_capp_cons  : ∀ c c₁ c₂ v,
    open_value v →
    open_value (exp_capp (crc_cons c c₁ c₂) v)
| OVal_fix        : ∀ e, open_value (exp_fix e)
.


Fixpoint map {V W : Set} (f : V → W) (e : exp V) : exp W :=
  match e with
  | exp_var  x       => exp_var (f x)
  | exp_const m      => exp_const m
  | exp_abs  e       => exp_abs (map (inc_map f) e)
  | exp_app  e₁ e₂   => exp_app (map f e₁) (map f e₂)
  | exp_capp c  e    => exp_capp c (map f e)
  | exp_fix  e       => exp_fix (map (inc_map (inc_map f)) e)
  | exp_succ e       => exp_succ (map f e)
  | exp_case e e₁ e₂ => exp_case (map f e) (map f e₁) (map (inc_map f) e₂)
  end.

Notation weaken e := (map (@VS _) e).
Notation weaken1 e := (map (inc_map (@VS _)) e).

Definition lift {V W : Set} (f : V → exp W) (x : inc V) : exp (inc W) :=
  match x with
  | VZ   => exp_var VZ
  | VS y => map (@VS _) (f y)
  end.

Fixpoint bind {V W : Set} (f : V → exp W) (e : exp V) : exp W :=
  match e with
  | exp_var  x       => f x
  | exp_const m      => exp_const m
  | exp_abs  e       => exp_abs (bind (lift f) e)
  | exp_app  e₁ e₂   => exp_app (bind f e₁) (bind f e₂)
  | exp_capp c  e    => exp_capp c (bind f e)
  | exp_fix  e       => exp_fix (bind (lift (lift f)) e)
  | exp_succ e       => exp_succ (bind f e)
  | exp_case e e₁ e₂ => exp_case (bind f e) (bind f e₁) (bind (lift f) e₂)
  end.

Definition subst_func {V : Set} (e : exp V) (x : inc V) : exp V :=
  match x with
  | VZ   => e
  | VS y => exp_var y
  end.

Notation subst e₁ e₂ := (bind (subst_func e₂) e₁).

Fixpoint plug {V : Set} (C : ctx V) : exp V → exp0 :=
  match C in ctx V with
  | ctx_hole            => fun e => e
  | ctx_abs    C       => fun e => plug C (exp_abs e)
  | ctx_app1   C e₂    => fun e => plug C (exp_app e e₂)
  | ctx_app2   e₁ C    => fun e => plug C (exp_app e₁ e)
  | ctx_capp   c  C    => fun e => plug C (exp_capp c e)
  | ctx_fix    C       => fun e => plug C (exp_fix e)
  | ctx_succ   C       => fun e => plug C (exp_succ e)
  | ctx_case   C e₁ e₂ => fun e => plug C (exp_case e e₁ e₂)
  | ctx_case1  e₀ C e₂ => fun e => plug C (exp_case e₀ e e₂)
  | ctx_case2  e₀ e₁ C => fun e => plug C (exp_case e₀ e₁ e)
  end.
