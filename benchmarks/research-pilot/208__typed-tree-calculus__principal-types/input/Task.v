Require Import String Arith Lia Bool List Nat.

Require Import terms types subtypes derive.

Open Scope string_scope.

Open Scope nat_scope.

Set Default Proof Using "Type".

Theorem programs_have_types: forall p gamma, program p -> derive gamma p (program_type p).

Theorem programs_have_principal_types:
  forall p, program p ->
            forall gamma ty, derive gamma p ty -> subtype (program_type p) ty.
