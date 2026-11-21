Require Import Rules.

Set Implicit Arguments.

Require Import Metalib.Metatheory.

Require Import Program.Equality.

Theorem preservation : forall e e' T,
    typing nil e T ->
    step e e' ->
    typing nil e' T.
