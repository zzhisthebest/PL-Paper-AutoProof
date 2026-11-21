Set Implicit Arguments.

Require Import LibExtra AbstractSyntax.

Require Import Effects.

Implicit Types (Delta : init_ctx) (Sigma : heap) (ℰ : eff_ctx).

Notation well_pointed Delta ℰ x :=
  ((binds x committed Delta) \/ (x \in dom ℰ /\ binds x free Delta)).
