Require Import Program.Equality.

Require Import Metalib.Metatheory.

Require Import Language Infra.

Notation "v |- e ->* e'" := ((star exp (step v)) e e') (at level 68).

Theorem gen_type_safety : forall G e m A,
  has_type G e m A -> forall v e',
  value v ->
  has_type top v inf G ->
  v |- e ->* e' ->
  value e' \/
  (exists e'', step v e' e'').
