Require Import Utf8.

Require Import Binding.Lib Binding.Set.

Inductive kind := T | E.

Inductive typ (A : Set) : Set :=
| t_var  : A → typ A
| t_arr  : typ A → typ A → typ A → typ A
| t_all  : kind → typ (inc A) → typ A
| r_pure : typ A
| r_cons : typ (inc (inc A)) → typ (inc (inc A)) → typ A → typ A
.

Arguments t_var {A}.

Arguments t_arr {A}.

Arguments t_all {A}.

Arguments r_pure {A}.

Arguments r_cons {A}.

Notation " # v "           := (t_var v) (at level 5, no associativity) : typ_scope.

Notation " τ₁ →[ ρ ] τ₂ "  := (t_arr τ₁ ρ τ₂) (at level 30, right associativity) : typ_scope.

Notation " [∀] κ , τ "     := (t_all κ τ) (at level 30, no associativity) : typ_scope.

Notation "'ε'"             := (r_pure) : typ_scope.

Notation " [ τ / ρ ] ρ' "  := (r_cons τ ρ ρ') (at level 30, τ at level 30, ρ at level 50, right associativity) : typ_scope.

Delimit Scope typ_scope with tp.

Section Instances.

Local Open Scope typ_scope.

Global Instance SetPureCore_typ : SetPureCore typ :=
    { set_pure := @t_var }.

Fixpoint tmap {A B : Set} (f : A [→] B) (τ : typ A) : typ B :=
    match τ with
    | # x        => # (f x)
    | τ₁ →[ρ] τ₂ => tmap f τ₁ →[tmap f ρ] tmap f τ₂
    | [∀] κ, τ   => [∀] κ, tmap (liftA (G:=inc) f) τ
    | ε          => ε
    | [τ / ρ] ρ' => [ tmap (liftA (G:=inc) (liftA (G:=inc) f)) τ / tmap (liftA (G:=inc) (liftA (G:=inc) f)) ρ] tmap f ρ'
    end.

Global Instance IsMapCore_tmap : IsMapCore (@tmap) := {}.

Fixpoint tbind {A B : Set} (f : A [⇒] B) (τ : typ A) : typ B :=
    match τ with
    | # x        => f x
    | τ₁ →[ρ] τ₂ => tbind f τ₁ →[tbind f ρ] tbind f τ₂
    | [∀] κ, τ   => [∀] κ, tbind (liftS (G:=inc) f) τ
    | ε          => ε
    | [τ / ρ] ρ' => [tbind (liftS (G:=inc) (liftS (G:=inc) f)) τ / tbind (liftS (G:=inc) (liftS (G:=inc) f)) ρ] tbind f ρ'
    end.

Global Instance IsBindCore_tbind : IsBindCore (@tbind) := {}.

End Instances.

Arguments SetPureCore_typ {A} /.

Section Meta.

End Meta.
