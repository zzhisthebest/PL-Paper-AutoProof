From Declarative Require Import Language.

Theorem transitivity : forall Γ e1 e2 e3 A B,
  usub Γ e1 e2 A ->
  usub Γ e2 e3 B ->
  usub Γ e1 e3 A.
