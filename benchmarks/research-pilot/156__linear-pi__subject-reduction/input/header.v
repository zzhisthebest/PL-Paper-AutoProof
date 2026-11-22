Require Export compat.

Require Import Bool List Lia PeanoNat.

Notation name  := nat.

Definition nat_pair_eq_dec : forall n m : name * name, {n = m} + {n <> m} :=
  ltac:(decide equality; decide equality; decide equality).

Opaque nat_pair_eq_dec.
