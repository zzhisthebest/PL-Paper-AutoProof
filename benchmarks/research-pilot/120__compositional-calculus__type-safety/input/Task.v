Require Import Infrastructure.

Require Import Coq.Program.Equality.

Require Import List.

Import ListNotations.

Require Import Arith Lia.

Theorem type_safety : forall e e' A,
    Typing nil nil e Inf A ->
    e ->* e' ->
    value e' \/ exists e'', step e' e''.
