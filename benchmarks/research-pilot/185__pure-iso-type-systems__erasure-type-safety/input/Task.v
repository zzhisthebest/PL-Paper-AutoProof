From TLC Require Import LibLN.

Set Implicit Arguments.

Require Import LamI_Full_ott.

Implicit Types x : var.

Definition era := erasure.

Definition cera := map erasure.

Theorem subject_reduction_result : forall E t t' T,
  typing E t T ->
  C.beta (era t) (era t') ->
  C.typing (cera E) (era t') (era T).

Theorem progress_result : forall t T,
  typing empty t T ->
  C.value (era t)
  \/ exists t', C.reduct (era t) t'.
