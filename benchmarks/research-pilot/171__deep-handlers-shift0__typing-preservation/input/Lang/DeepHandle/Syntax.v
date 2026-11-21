Require Import Utf8.

Require Export Binding.Inc.

Require Import Binding.Lib Binding.Set.

Inductive expr (V : Set) : Set :=
| e_value      : value V → expr V
| e_app        : expr V → expr V → expr V
| e_do         : value V → expr V
| e_handle     : expr V → expr (inc (inc V)) → expr V
| e_handle_ret : expr V → expr (inc (inc V)) → expr (inc V) → expr V
| e_lift    : expr V → expr V
with value (V : Set) : Set :=
| v_var : V → value V
| v_lam : expr (inc V) → value V
.

Arguments e_value      {V}.

Arguments e_app        {V}.

Arguments e_do         {V}.

Arguments e_handle     {V}.

Arguments e_handle_ret {V}.

Arguments e_lift       {V}.

Arguments v_var {V}.

Arguments v_lam {V}.

Notation " # v "     := (v_var v) (at level 5, no associativity) : exp_scope.

Notation " [λ] e "   := (v_lam e) (at level 40, no associativity) : exp_scope.

Notation " e₁ @ e₂ " := (e_app e₁ e₂) (at level 20, left associativity) : exp_scope.

Notation " e ⇑ "   := (e_lift e) (at level 5, no associativity) : exp_scope.

Delimit Scope exp_scope with exp.

Coercion e_value : value >-> expr.

Instance SetPureCore_value : SetPureCore value :=
  { set_pure := @v_var }.

Arguments SetPureCore_value {A} /.

Inductive ectx (V : Set) : Set :=
| x_hole       : ectx (V : Set)
| x_app1       : ectx V → expr V → ectx V
| x_app2       : value V → ectx V → ectx V
| x_handle     : ectx V → expr (inc (inc V)) → ectx V
| x_handle_ret : ectx V → expr (inc (inc V)) → expr (inc V) → ectx V
| x_lift    : ectx V → ectx V
.

Arguments x_hole       {V}.

Arguments x_app1       {V}.

Arguments x_app2       {V}.

Arguments x_handle     {V}.

Arguments x_handle_ret {V}.

Arguments x_lift       {V}.

Reserved Notation " E [ e ] " (at level 15, no associativity).

Fixpoint xplug {V : Set} (E : ectx V) (e : expr V) : expr V :=
  match E with
  | x_hole             => e
  | x_app1       E e'  => E [e] @ e'
  | x_app2       v E   => v @ E [e]
  | x_handle     E h   => e_handle (E [e]) h
  | x_handle_ret E h r => e_handle_ret (E [e]) h r
  | x_lift       E     => (E [e])⇑
  end%exp
where " E [ e ] " := (xplug E e) : exp_scope.

Inductive xfree {V : Set} : nat → ectx V → Prop :=
| XF_hole       : xfree 0 x_hole
| XF_app1       : ∀ n E e,   xfree n E → xfree n (x_app1 E e)
| XF_app2       : ∀ n v E,   xfree n E → xfree n (x_app2 v E)
| XF_handle     : ∀ n E e,   xfree (S n) E → xfree n (x_handle E e)
| XF_handle_ret : ∀ n E e r, xfree (S n) E → xfree n (x_handle_ret E e r)
| XF_lift       : ∀ n E,     xfree n E → xfree (S n) (x_lift E)
.

Inductive mctx (V : Set) : Set :=
| m_hole       : mctx V
| m_app1       : mctx V → expr V → mctx V
| m_app2       : value V → mctx V → mctx V
| m_handle     : mctx V → expr (inc (inc V)) → mctx V
| m_handle_ret : mctx V → expr (inc (inc V)) → expr (inc V) → mctx V
| m_lift       : mctx V → mctx V
.

Arguments m_hole       {V}.

Arguments m_app1       {V}.

Arguments m_app2       {V}.

Arguments m_handle     {V}.

Arguments m_handle_ret {V}.

Arguments m_lift       {V}.

Fixpoint mplug {V : Set} (F : mctx V) (e : expr V) : expr V :=
  match F with
  | m_hole             => e
  | m_app1       F e'  => mplug F (e @ e')
  | m_app2 v     F     => mplug F (v @ e)
  | m_handle     F h   => mplug F (e_handle e h)
  | m_handle_ret F h r => mplug F (e_handle_ret e h r)
  | m_lift       F     => mplug F (e⇑)
  end%exp.

Fixpoint emap {A B : Set} (f : A [→] B) (e : expr A) : expr B :=
  match e with
  | e_value      v     => vmap f v
  | e₁ @ e₂            => emap f e₁ @ emap f e₂
  | e_do         v     => e_do     (vmap f v)
  | e_handle     e h   => e_handle (emap f e) (emap (liftA (G:=inc) (liftA (G:=inc) f)) h)
  | e_handle_ret e h r =>
    e_handle_ret (emap f e) (emap (liftA (G:=inc) (liftA (G:=inc) f)) h) (emap (liftA (G:=inc) f) r)
  | e⇑                 => (emap f e)⇑
  end%exp
with vmap {A B : Set} (f : A [→] B) (v : value A) : value B :=
  match v with
  | # x => # (f x)
  | [λ] e => [λ] emap (liftA (G:=inc) f) e
  end%exp.

Instance IsMapCore_emap : IsMapCore (@emap) := {}.

Instance IsMapCore_vmap : IsMapCore (@vmap) := {}.

Fixpoint xmap {A B : Set} (f : A [→] B) (E : ectx A) : ectx B :=
  match E with
  | x_hole        => x_hole
  | x_app1    E e => x_app1    (xmap f E) (fmap f e)
  | x_app2    v E => x_app2    (fmap f v) (xmap f E)
  | x_handle  E h => x_handle  (xmap f E) (fmap (liftA (G:=inc) (liftA (G:=inc) f)) h)
  | x_handle_ret E h r =>
    x_handle_ret (xmap f E) (fmap (liftA (G:=inc) (liftA (G:=inc) f)) h) (fmap (liftA (G:=inc) f) r)
  | x_lift    E   => x_lift    (xmap f E)
  end.

Instance IsMapCore_xmap : IsMapCore (@xmap) := {}.

Fixpoint mmap {A B : Set} (f : A [→] B) (F : mctx A) : mctx B :=
  match F with
  | m_hole        => m_hole
  | m_app1    F e => m_app1    (mmap f F) (fmap f e)
  | m_app2    v F => m_app2    (fmap f v) (mmap f F)
  | m_handle  F h => m_handle  (mmap f F) (fmap (liftA (G:=inc) (liftA (G:=inc) f)) h)
  | m_handle_ret F h r =>
    m_handle_ret (mmap f F) (fmap (liftA (G:=inc) (liftA (G:=inc) f)) h) (fmap (liftA (G:=inc) f) r)
  | m_lift    F   => m_lift    (mmap f F)
  end.

Instance IsMapCore_mmap : IsMapCore (@mmap) := {}.

Fixpoint ebind {A B : Set} (f : A [⇒] B) (e : expr A) : expr B :=
  match e with
  | e_value      v     => vbind f v
  | e₁ @ e₂            => ebind f e₁ @ ebind f e₂
  | e_do         v     => e_do     (vbind f v)
  | e_handle     e h   => e_handle (ebind f e) (ebind (liftS (G:=inc) (liftS (G:=inc) f)) h)
  | e_handle_ret e h r =>
    e_handle_ret (ebind f e) (ebind (liftS (G:=inc) (liftS (G:=inc) f)) h) (ebind (liftS (G:=inc) f) r)
  | e⇑                 => (ebind f e)⇑
  end%exp
with vbind {A B : Set} (f : A [⇒] B) (v : value A) : value B :=
  match v with
  | # x => f x
  | [λ] e => [λ] (ebind (liftS (G:=inc) f) e)
  end%exp.

Instance IsBindCore_ebind : IsBindCore (@ebind) := {}.

Instance IsBindCore_vbind : IsBindCore (@vbind) := {}.

Fixpoint xbind {A B : Set} (f : A [⇒] B) (E : ectx A) : ectx B :=
  match E with
  | x_hole        => x_hole
  | x_app1    E e => x_app1    (xbind f E) (bind  f e)
  | x_app2    v E => x_app2    (bind  f v) (xbind f E)
  | x_handle  E h => x_handle  (xbind f E) (bind (liftS (G:=inc) (liftS (G:=inc) f)) h)
  | x_handle_ret E h r =>
    x_handle_ret (xbind f E) (bind (liftS (G:=inc) (liftS (G:=inc) f)) h) (bind (liftS (G:=inc) f) r)
  | x_lift    E   => x_lift    (xbind f E)
  end.

Instance IsBindCore_xbind : IsBindCore (@xbind) := {}.

Fixpoint mbind {A B : Set} (f : A [⇒] B) (F : mctx A) : mctx B :=
  match F with
  | m_hole        => m_hole
  | m_app1    F e => m_app1    (mbind f F) (bind  f e)
  | m_app2    v F => m_app2    (bind  f v) (mbind f F)
  | m_handle  F h => m_handle  (mbind f F) (bind (liftS (G:=inc) (liftS (G:=inc) f)) h)
  | m_handle_ret F h r =>
    m_handle_ret (mbind f F) (bind (liftS (G:=inc) (liftS (G:=inc) f)) h) (bind (liftS (G:=inc) f) r)
  | m_lift    F   => m_lift    (mbind f F)
  end.

Instance IsBindCore_mbind : IsBindCore (@mbind) := {}.
