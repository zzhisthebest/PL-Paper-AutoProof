Require Import Utf8.

Require Import Binding.Lib Binding.Set.

Require Import SetoidClass.

Definition eq_ext {A B} (f g : A → B) := ∀ x, f x = g x.

Definition Equivalence_eq_ext {A B} : Equivalence (@eq_ext A B) :=
 {| Equivalence_Reflexive := fun f x => eq_refl;
    Equivalence_Symmetric := fun f g H x => eq_sym (H x);
    Equivalence_Transitive := fun f g h H1 H2 x => eq_trans (H1 x) (H2 x) |}.

Instance Setoid_equiv {A B} : Setoid (A → B) := Build_Setoid Equivalence_eq_ext.

Definition empty_env {A} : ∅ → A := λ x, match x with end.

Definition extend {V A : Set} (Γ : V → A) (τ : A) : inc V → A :=
  λ x, match x with VZ => τ | VS x => Γ x end.

Definition compose {A B C} (f : B → C) (g : A → B) (x : A) := f (g x).

Notation "f ∘ g" := (compose f g) (at level 40, left associativity).

Notation "f ▹ v" := (extend f v) (at level 40, v at next level, left associativity).

Notation "□" := empty_env.

Notation "x ≃ y" := (equiv x y) (at level 70, no associativity).

Arguments compose {A B C} f g x /.

Section Definitions.

Context {T : Set → Type} {PureT : SetPureCore T}
          {tmap : ∀ A B : Set, A [→] B → T A → T B}
          {tbind : ∀ A B : Set, A [⇒] B → T A → T B}
          {MapT : IsMapCore tmap} {BindT : IsBindCore tbind}.

Definition envmap {V A B : Set} (f : A [→] B) (Γ : V → T A) x :=
    fmap f (Γ x).

Definition envbind {V A B : Set} (f : A [⇒] B) (Γ : V → T A) x :=
    bind f (Γ x).

Global Instance IsMapCore_env V : IsMapCore (@envmap V) := {}.

Global Instance IsBindCore_env V : IsBindCore (@envbind V) := {}.

Global Arguments envmap {V A B} f Γ x /.

Global Arguments envbind {V A B} f Γ x /.

End Definitions.
