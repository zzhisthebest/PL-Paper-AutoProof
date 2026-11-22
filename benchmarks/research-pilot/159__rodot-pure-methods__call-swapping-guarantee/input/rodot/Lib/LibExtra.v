Set Implicit Arguments.

Require Import Coq.Bool.Bool.

Require Export Coq.Program.Basics.

From TLC Require Export LibVar LibLN LibEnv.

Require Export LibNatExtra LibVarExtra LibSetExtra LibEnvExtra LibListExtra LibListReorder LibFreshExtra.

Open Scope program_scope.

Section Program.

Definition dec_apply {A B : Type} dec (f : A -> B) g x :=
    match dec x with
    | true => f x
    | false => g x
    end.

Definition ignore_second {A B C : Type} (f : A -> C) (x : A) (n : B) := f x.

Definition compose12 {A B C D : Type} (g : B -> D -> C) (f : A -> D -> B) (x : A) (n : D) :=
    g (f x n) n.

Notation " g ∘∘ f " := (compose12 g f) (at level 40, left associativity).

End Program.

Notation " g ∘∘ f "
  := (compose12 g f) (at level 40, left associativity) : program_scope.

Module Nat := PeanoNat.Nat.

Notation "xs ~** vs" := (singles (List.rev xs) (List.rev vs))
  (at level 27, left associativity) : env_scope.
