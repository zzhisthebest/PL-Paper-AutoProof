Require Import Utf8.

Require Import Binding.Core.

Require Import Binding.Inc.

Class SetPureCore (F : Set → Type) : Type :=
  set_pure : ∀ A : Set, A → F A.

Arguments set_pure {F _ A}.

Record Arr (A B : Set) : Type :=
  { apply_arr : A → B
  }.

Arguments apply_arr {A B}.

Coercion apply_arr : Arr >-> Funclass.

Record Sub {F : Set → Type} {FP : SetPureCore F} (A B : Set) : Type :=
  { apply_sub : A → F B
  }.

Arguments apply_sub {F FP A B}.

Coercion apply_sub : Sub >-> Funclass.

Notation "A '[→]' B" := (Arr A B) (at level 99) : type_scope.

Notation "A '[⇒]' B" := (Sub A B) (at level 99) : type_scope.

Class SetPure (F : Set → Type) {FP : SetPureCore F}
    {map  : ∀ A B : Set, (A [→] B) → F A → F B}
    {MapF : IsMapCore map}
    {bnd  : ∀ A B : Set, (A [⇒] B) → F A → F B}
    {BndF : IsBindCore bnd} : Prop :=
  { fmap_set_pure : ∀ (A B : Set) (f : A [→] B) (x : A),
      fmap f (set_pure x) = set_pure (f x)
  ; bind_set_pure : ∀ (A B : Set) (f : A [⇒] B) (x : A),
      bind f (set_pure x) = f x
  }.

Section SetInstances.

Context {F : Set → Type} {FP : SetPureCore F}.

Context {map : ∀ A B : Set, (A [→] B) → F A → F B} {MapF : IsMapCore map}.

Context {bnd : ∀ A B : Set, (A [⇒] B) → F A → F B} {BndF : IsBindCore bnd}.

Context {SPF : SetPure F}.

Global Instance ArrowCore_Set : ArrowCore Arr :=
  { arrow_id   := λ _,         {| apply_arr := λ x, x       |}
  ; arrow_comp := λ _ _ _ f g, {| apply_arr := λ x, f (g x) |}
  ; arrow_eq   := λ _ _   f g, ∀ x, f x = g x
  }.

Global Instance PreSubstCore_Set : PreSubstCore Sub :=
  { subst_pure := λ _, {| apply_sub := set_pure |}
  ; subst_eq   := λ _ _ f g, ∀ x, f x = g x
  }.

Global Instance SubstCore_Set : SubstCore Arr Sub :=
  { arrow_subst_comp := λ (A B C : Set) (f : B [→] C) (g : A [⇒] B),
      {| apply_sub := λ x, fmap f (g x) |}
  ; subst_comp := λ (A B C : Set) (f : B [⇒] C) (g : A [⇒] B),
      {| apply_sub := λ x, bind f (g x) |}
  }.

Context {MF : FMap map} {BF : Bind bnd}.

Context {MBF : BindMap map bnd}.

Global Instance ALiftableCore_inc : ALiftableCore Arr inc :=
  { liftA := λ _ _ f, {| apply_arr := inc_map f |} }.

Global Instance SLiftableCore_inc : SLiftableCore Sub inc :=
  { liftS := λ A B (f : A [⇒] B),
      {| apply_sub := λ x,
           match x with
           | VZ   => set_pure VZ
           | VS y => fmap {| apply_arr := VS |} (f y)
           end
      |}
  }.

Global Instance ShiftableCore_inc : ShiftableCore Arr inc :=
  λ A, {| apply_arr := VS |}.

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
