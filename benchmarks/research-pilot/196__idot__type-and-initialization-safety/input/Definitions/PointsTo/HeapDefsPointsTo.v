Set Implicit Arguments.

Require Import LibExtra AbstractSyntax.

Require Import Effects.

Fixpoint heap_defs_points_to (hds : heap_defs) :=
  match hds with
  | nil => \{}
  | (heap_def_typ _ _) :: ds => heap_defs_points_to ds
  | (heap_def_trm l (Some x)) :: ds => \{ x} \u heap_defs_points_to ds
  | (heap_def_trm l None) :: ds => heap_defs_points_to ds
  end%list.
