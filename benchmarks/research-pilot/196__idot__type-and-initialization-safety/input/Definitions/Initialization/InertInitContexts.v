Set Implicit Arguments.

Require Import LibExtra AbstractSyntax.

Definition inert_inits Delta :=
  forall x init, binds x init Delta ->
            init = free \/ init = committed.
