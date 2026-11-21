Require Import syntax_ott.

Require Import Program.Equality.

Require Import Metalib.Metatheory.

Require Import Lia.

Require Import Relation_Operators.

Require Import Operators_Properties.

Theorem TypCast_soundness: forall D A B c,
  TypCast D nil A B c ->
  eqe2 D nil A B.

Theorem TypCast_completeness: forall D A B,
  eqe2 D nil A B ->
  exists c, TypCast D nil A B c.
