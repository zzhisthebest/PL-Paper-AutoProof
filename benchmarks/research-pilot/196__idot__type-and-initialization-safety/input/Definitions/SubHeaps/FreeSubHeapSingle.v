Set Implicit Arguments.

Require Import LibExtra AbstractSyntax.

Require Import Effects.

Require Import FreeItems.

Definition free_sub_heap (ℰ : eff_ctx) (Sigma : heap) (Delta : init_ctx) :=
  forall x effs,

    binds x effs ℰ ->
    (forall y a, (y,a) \in (from_list effs) -> y = x) /\

    exists itm, binds x itm Sigma /\

                free_heap_item Delta ℰ x itm.
