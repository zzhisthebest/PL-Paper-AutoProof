From Stdlib Require Import Utf8.
Require Import Common.Metatheory.

Inductive exp (V : Set) : Set :=
| exp_var    : V → exp V
| exp_const  : nat → exp V
| exp_abs    : exp (inc V) → exp V
| exp_app    : exp V → exp V → exp V
| exp_shift0 : exp (inc V) → exp V
| exp_reset0 : exp V → exp V
| exp_dollar : exp V → exp V → exp V
| exp_fix    : exp (inc (inc V)) → exp V
| exp_succ   : exp V → exp V
| exp_case   : exp V → exp V → exp (inc V) → exp V
.

Arguments exp_var    [V] _.
Arguments exp_const  [V] _.
Arguments exp_abs    [V] _.
Arguments exp_app    [V] _ _.
Arguments exp_shift0 [V] _.
Arguments exp_reset0 [V] _.
Arguments exp_dollar [V] _ _.
Arguments exp_fix    [V] _.
Arguments exp_succ   [V] _.
Arguments exp_case   [V] _ _ _.
