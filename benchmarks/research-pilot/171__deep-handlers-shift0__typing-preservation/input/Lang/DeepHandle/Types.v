Require Import Utf8.

Require Import Binding.Lib Binding.Set.

Inductive kind := T | E.

Inductive typ (A : Set) : Set :=
| t_var  : A → typ A
| t_arr  : typ A → typ A → typ A → typ A
| t_all  : kind → typ (inc A) → typ A
| r_pure : typ A
| r_cons : typ (inc A) → typ (inc A) → typ A → typ A
.

Arguments t_var  {A}.

Arguments t_arr  {A}.

Arguments t_all  {A}.

Arguments r_pure {A}.

Arguments r_cons {A}.

Notation " # v "           := (t_var v) (at level 5, no associativity) : tp_scope.

Notation " τ₁ →[ ρ ] τ₂ "  := (t_arr τ₁ ρ τ₂) (at level 30, right associativity) : tp_scope.

Notation " [∀] κ , τ "     := (t_all κ τ) (at level 30, no associativity) : tp_scope.

Notation "'ε'"             := (r_pure) : tp_scope.

Notation " [ τ₁ ⇒ τ₂ ] ρ " := (r_cons τ₁ τ₂ ρ) (at level 30, τ₁ at level 50, τ₂ at level 50, right associativity) : tp_scope.

Delimit Scope tp_scope with tp.

Instance SetPureCore_typ : SetPureCore typ :=
  { set_pure := @t_var}.

Arguments SetPureCore_typ {A} /.

Fixpoint tmap {A B : Set} (f : A [→] B) (τ : typ A) : typ B :=
  match τ with
  | # x         => #(f x)
  | τ₁ →[ρ] τ₂  => tmap f τ₁ →[tmap f ρ] tmap f τ₂
  | [∀] κ, τ    => [∀] κ, tmap (liftA (G:=inc) f) τ
  | ε           => ε
  | [τ₁ ⇒ τ₂] ρ => [tmap (liftA (G:=inc) f) τ₁ ⇒ tmap (liftA (G:=inc) f) τ₂] tmap f ρ
  end%tp.

Instance IsMapCore_tmap : IsMapCore (@tmap) := {}.

Fixpoint tbind {A B : Set} (f : A [⇒] B) (τ : typ A) : typ B :=
  match τ with
  | #x          => f x
  | τ₁ →[ρ] τ₂  => tbind f τ₁ →[tbind f ρ] tbind f τ₂
  | [∀] κ, τ    => [∀] κ, tbind (liftS (G:=inc) f) τ
  | ε           => r_pure
  | [τ₁ ⇒ τ₂] ρ => [tbind (liftS (G:=inc) f) τ₁ ⇒ tbind (liftS (G:=inc) f) τ₂] tbind f ρ
  end%tp.

Instance IsBindCore_tbind : IsBindCore (@tbind) := {}.

Section Meta.

End Meta.
