Require Import Utf8.

Require Import Binding.Lib.

Require Import SetoidClass Morphisms.

Definition eq_ext {A B} (f g : A → B) := ∀ x, f x = g x.

Instance Setoid_equiv {A B} : Setoid (A → B) :=
  Build_Setoid (equiv := @eq_ext A B) ltac:(split; unfold eq_ext; congruence).

Definition empty_env {A} : ∀ (x : ∅), A := λ x, match x with end.

Definition extend {V : Set} {A} (Γ : V → A) (τ : A) : inc V → A :=
  λ x, match x with VZ => τ | VS x => Γ x end.

Definition compose {A B C} (f : B → C) (g : A → B) (x : A) := f (g x).

Notation "f • g" := (compose f g) (at level 40, left associativity).

Notation "f ▹ v" := (extend f v) (at level 40, v at next level, left associativity).

Notation "□" := empty_env.

Notation "x ≡ y" := (equiv x y) (at level 70, no associativity).

Arguments compose {A B C} f g x /.

Require Import Binding.Set.

Import ArrowNotations.
