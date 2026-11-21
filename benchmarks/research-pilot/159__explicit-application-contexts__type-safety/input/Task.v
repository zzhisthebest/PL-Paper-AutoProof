Set Implicit Arguments.

From TLC Require Import LibReflect.

From TLC Require Import LibList LibLN.

Require Import DeclDef.

Theorem typing_preservation : forall E S e T e',
    typing E S e T ->
    red e e' ->
    typing E S e' T.

Theorem typing_progress : forall e T nil,
    typing empty nil e T ->
    value e \/ exists e', red e e'.
