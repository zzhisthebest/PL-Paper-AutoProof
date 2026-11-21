Require Import erasure.

Require Import Program.Equality.

Require Import Metalib.Metatheory.

Require Import Lia.

Require Import Relation_Operators.

Require Import Operators_Properties.

Definition terminate (e:exp) : Prop :=
  exists v, value v /\ e ==>* v.

Definition diverge (e:exp) : Prop :=
  ~ (exists v, value v /\ e ==>* v).

Theorem behavior_equiv: forall e t e',
  EquiTypingC nil e t e' ->
  (terminate e <-> terminate e') /\
  (diverge e <-> diverge e').
