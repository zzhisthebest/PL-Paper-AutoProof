Require Import Utf8.

Require Import Binding.Core.

Require Import Binding.Inc.

Require Import Binding.Properties.

Require Import Morphisms.

Class SetPureCore (F : Set → Type) : Type :=
  set_pure : ∀ A : Set, A → F A.

Arguments set_pure {F _ A}.

Record Arr (A B : Set) : Type :=
  { apply_arr : A → B
  }.

Notation " A '[→]' B " := (Arr A B) (at level 100, no associativity) : type_scope.

Arguments apply_arr {A B}.

Coercion apply_arr : Arr >-> Funclass.

Record Sub {F : Set → Type} {FP : SetPureCore F} (A B : Set) : Type :=
  { apply_sub : A → F B
  }.

Notation " A '[⇒]' B " := (Sub A B) (at level 100, no associativity) : type_scope.

Arguments apply_sub {F FP A B}.

Coercion apply_sub : Sub >-> Funclass.

Instance ArrEqC : EqIndCore Arr :=
  λ A B f g, ∀ x, f x = g x.

Instance SubEqC {F} {FP : SetPureCore F} : EqIndCore Sub :=
  λ A B f g, ∀ x, f x = g x.

Global Instance ArrowCore_Set : ArrowCore Arr :=
  { arrow_id   := λ _,         {| apply_arr := λ x, x       |}
  ; arrow_comp := λ _ _ _ f g, {| apply_arr := λ x, f (g x) |}
  }.

Class SetPure (F : Set → Type) {FP : SetPureCore F}
    {MapF : FunctorCore F}
    {BndF : BindCore F} : Prop :=
  { fmap_set_pure : ∀ (A B : Set) (f : Arr A B) (x : A),
      fmap f (set_pure x) = set_pure (f x)
  ; bind_set_pure : ∀ (A B : Set) (f : Sub A B) (x : A),
      bind f (set_pure x) = f x
  }.

Section SetInstances.

Context {F : Set → Type} {FP : SetPureCore F}.

Context {MapF : FunctorCore (Arr := Arr) F}.

Context {BndF : BindCore (Sub := Sub) F}.

Context {SPF : SetPure F}.

Global Instance SubstArrCore_Set : ArrowCore Sub :=
    { arrow_id A := {| apply_sub := set_pure |};
      arrow_comp A B C f g := {| apply_sub := λ x, bind f (g x) |} }.

Global Instance SubstCore_Set : SubstCore Arr Sub :=
    λ A B f, {| apply_sub := λ x, set_pure (f x) |}.

Definition incFun (A B : Set) (f : Arr A B) : inc A → inc B := inc_map f.

Global Instance IncMap : FunctorCore inc := incFun.

Global Instance ALiftableCore_inc : LiftableCore Arr inc :=
    { lift A B f := {| apply_arr := fmap f |} }.

Global Instance ShiftableCore_inc : ShiftableCore Arr inc :=
    λ A, {| apply_arr := VS |}.

Global Instance SLiftableCore_inc : LiftableCore Sub inc :=
    { lift A B f :=
        {| apply_sub := λ x,
                        match x with
                        | VZ   => set_pure VZ
                        | VS y => shift (f y)
                        end
        |}
    }.

Global Instance SubstitutableCore_inc : SubstitutableCore Sub F inc :=
    λ A v,
    {| apply_sub := λ x,
                    match x with
                    | VZ => v
                    | VS y => set_pure y
                    end
    |}.

End SetInstances.

Arguments set_pure {F _ A} /.
