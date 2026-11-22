Require Export Poulet4.Monads.Monad.

From Coq Require Import Lists.List Program.Basics.

Require Import VST.zlist.Zlist.

Import ListNotations.

Open Scope monad.

Open Scope list_scope.

Definition option_bind (A B: Type) (c: option A) (f: A -> option B) : option B :=
  match c with
  | Some a => f a
  | None => None
  end.

Global Instance option_monad_inst : Monad option :=
  { mret := @Some;
    mbind := option_bind;
  }.

Definition option_fail {A : Type} : option A := None.

Fixpoint reduce_option {A : Type} (acts: list (option A)) (f : A -> A -> A) (base: A) : option A :=
  match acts with
  | nil => Some base
  | None :: _ => None
  | Some x :: xs => reduce_option xs f (f x base)
  end.

Definition guard (b : bool) : option unit := if b then Some tt else None.
