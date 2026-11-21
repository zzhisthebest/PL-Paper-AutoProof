From mathcomp Require Import ssreflect.seq all_ssreflect.

Require Import List String Coq.Arith.PeanoNat Relations ZArith Datatypes Setoid Morphisms Coq.Logic.Decidable Coq.Program.Basics Coq.Init.Datatypes.

Import ListNotations.

Open Scope list_scope.

From Paco Require Import paco.

Import ListNotations.

From SST Require Import src.header src.sim src.expr src.process src.local src.global src.balanced src.typecheck src.part src.gttreeh src.step.

Inductive isMerge : ltt -> list (option ltt) -> Prop :=
  | matm : forall t, isMerge t (Some t :: nil)
  | mconsn : forall t xs, isMerge t xs -> isMerge t (None :: xs)
  | mconss : forall t xs, isMerge t xs -> isMerge t (Some t :: xs).
