Require Import Coq.Arith.Arith.

Require Import Coq.NArith.NArith.

Require Import Coq.Sorting.Permutation.

Require Import Coq.Strings.Ascii.

Require Import Coq.Strings.String.

Require Import Coq.Lists.List.

Require Import Coq.micromega.Lia.

Import ListNotations.

Definition ascii_leb (c1 c2: ascii) := N.leb (N_of_ascii c1) (N_of_ascii c2).

Fixpoint string_leb (s1 s2: string) :=
  match s1, s2 with
  | EmptyString, EmptyString => true
  | String c1 s1, String c2 s2 =>
    if (c1 =? c2)%char then string_leb s1 s2 else ascii_leb c1 c2
  | EmptyString, String _ _ => true
  | String _ _, EmptyString => false
  end.

Local Open Scope string_scope.

Definition findi {A: Type} (f: A -> bool) (l: list A): option (nat * A) :=
  let fix iter (al: list A) (index: nat): option (nat * A) :=
      match al with
      | [] => None
      | a :: rest => if f a then Some (index, a) else iter rest (S index)
      end in
  iter l O.

Inductive Forall_fold {A B} (P : A -> B -> A -> Prop) : A -> list B -> A -> Prop :=
  | Forall_fold_nil : forall a,
      Forall_fold P a [] a
  | Forall_fold_cons : forall a b a' bs a'',
      P a b a' ->
      Forall_fold P a' bs a'' ->
      Forall_fold P a (b :: bs) a''.

Inductive Forall2_fold {A B C} (P : A -> B -> C -> A -> Prop) : A -> list B -> list C -> A -> Prop :=
  | Forall2_fold_nil : forall a,
      Forall2_fold P a [] [] a
  | Forall2_fold_cons : forall a b c a' bs cs a'',
      P a b c a' ->
      Forall2_fold P a' bs cs a'' ->
      Forall2_fold P a (b :: bs) (c :: cs) a''.
