Require Import syntax_ott.

Require Import Program.Equality.

Require Import Metalib.Metatheory.

Require Export LibTactics.

Require Import Lia.

Require Export equiRec.

Theorem preservation: forall e T,
  Typing nil e T -> forall e',
  Reduction e e' -> Typing nil e' T.

Require Import Program.Equality.

Require Import Metalib.Metatheory.

Require Export LibTactics.

Require Export subtyping.

Theorem progress: forall e t, Typing nil e t -> (value e) \/ exists e', Reduction e e'.
