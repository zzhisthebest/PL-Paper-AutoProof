Set Implicit Arguments.

Require Import Coq.Program.Basics.

From TLC Require Import LibAxioms.

Definition ignore_second {A B C : Type} (f : A -> C) (x : A) (n : B) := f x.

Definition compose12 {A B C D : Type} (g : B -> D -> C) (f : A -> D -> B) (x : A) (n : D) :=
  g (f x n) n.

Notation " g ∘∘ f "
  := (compose12 g f) (at level 40, left associativity) : program_scope.

Open Scope program_scope.

Definition dec_apply {A B : Type} dec (f : A -> B) g x :=
  match dec x with
  | true => f x
  | false => g x
  end.
