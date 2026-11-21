Require Import Metalib.Metatheory.

Require Import syntax_ott syntaxb_ott rules_inf rulesb_inf Infrastructure_b ttyping.

Require Import List.

Import ListNotations.

From Stdlib Require Import Arith Lia.

Require Import Strings.String.

From Stdlib Require Import Lia.

Theorem soundness_mul: forall e t e' A,
  ttyping nil e Inf A t->
  step e (e_exp e') ->
  exists t', t ->* (t_term t') /\ ttyping nil e' Inf A t' .
