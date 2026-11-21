Require Import Nbe.Syntax.Def Nbe.Utils.Notations.

Set Implicit Arguments.

Require Import Nbe.Domain.Def.

Require Import Nbe.Domain.Eval.

Require Import Nbe.Domain.Rb.

Inductive Nbe (A:Tm) (Gamma:Cxt) (t:Tm) : Tm -> Prop :=
| Nbe_intro: forall DA d denv v,
  EvalCxt Gamma denv ->
  EvalTm A denv DA ->
  EvalTm t denv d ->
  RbNf (length Gamma) (Ddown DA d) v ->
  Nbe A Gamma t v
.
