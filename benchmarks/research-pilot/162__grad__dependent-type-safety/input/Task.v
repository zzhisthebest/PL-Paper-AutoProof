Require Import ssreflect.

Require Import Coq.Classes.EquivDec.

Require Import Metalib.Metatheory.

Require Import Coq.Structures.Orders.

Require Import Stdlib.Init.Sumbool.

Require Import Coq.Program.Equality.

Require Import Coq.Classes.RelationClasses.

Require Import dqtt_ott.

Require Export beta.

Theorem preservation: forall D G a A, Typing D G a A -> forall a', Step a a' -> Typing D G a' A.

Theorem progress : forall a A,
  Typing nil nil a A -> value a \/ exists a', Step a a'.
