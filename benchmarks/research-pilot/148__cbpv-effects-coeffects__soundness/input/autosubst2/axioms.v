Require Import Coq.Logic.FunctionalExtensionality.

Require Import Program.Tactics.

Require Export List.

Definition funcomp {X Y Z} (g : Y -> Z) (f : X -> Y)  :=
  fun x => g (f x).

Notation "'list_map'" := map.

Definition cod X A:  Type :=  X -> A.
