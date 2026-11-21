Set Implicit Arguments.

Require Import LibExtra AbstractSyntax.

Require Import Effects HeapEffects.

Require Import HeapDefsPointsTo WellPointed.

Definition free_heap_defs (Delta : init_ctx) (ℰ : eff_ctx)
           (y : var) (hds : heap_defs) :=

  binds y free Delta /\

  binds y (heap_defs_effs y hds)  ℰ /\

  forall x, (x \in heap_defs_points_to hds) ->
       well_pointed Delta ℰ x.

Inductive free_heap_item : init_ctx -> eff_ctx -> var -> item -> Prop :=

| free_heap_obj : forall Delta ℰ y T hds,
    free_heap_defs Delta ℰ y hds ->
    free_heap_item Delta ℰ y (item_obj T hds).
