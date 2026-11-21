Set Implicit Arguments.

Require Import LibExtra AbstractSyntax.

Require Import Effects.

Fixpoint heap_defs_effs (x : var) (hds : heap_defs) : effects :=
  match hds with
  | nil                             => nil
  | (heap_def_typ _ _)        :: ds => heap_defs_effs x ds
  | (heap_def_trm l (Some _)) :: ds => heap_defs_effs x ds
  | (heap_def_trm l None)     :: ds => (x,l) :: (heap_defs_effs x ds)
  end%list.
