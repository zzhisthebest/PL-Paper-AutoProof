Set Implicit Arguments.

From TLC Require Import LibLN.

Require Import Main_ott.

Notation "t ^^ u" := (open_trm_wrt_trm t u) (at level 67).

Notation "t ^ x" := (open_trm_wrt_trm t (trm_var_f x)).

Notation "t --> t'" := (reduct t t') (at level 67).
