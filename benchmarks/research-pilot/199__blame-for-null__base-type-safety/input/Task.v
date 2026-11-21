From Stdlib Require Import Bool.
Require Import Definitions.

Theorem preservation : forall G t r T,
  typing G t T ->
  step t r ->
  (exists p, r = r_blame p) \/
  (exists u, r = r_term u /\ typing G u T).

Theorem progress : forall t T,
  typing nil t T ->
  (exists u, step t u) \/ Is_true (is_val_of_trm t).
