Set Implicit Arguments.

Require Import LibExtra AbstractSyntax.

Inductive defs_update : heap_defs -> trm_label -> var -> heap_defs -> Prop :=

| defs_update_var : forall hds a o x,
    defs_update (cons (heap_def_trm a o) hds)
                a x
                (cons (heap_def_trm a (Some x)) hds)
| defs_update_push : forall hds d a x hds',
    defs_update hds a x hds' ->
    defs_update (cons d hds) a x (cons d hds').

Definition heap_update (Sigma : heap) (x : var) (a : trm_label) (y : var) (Sigma' : heap) :=
  exists T hds hds' Sigma1 Sigma2,
    (Sigma = Sigma1 & x ~ (item_obj T hds) & Sigma2) /\
    (x # Sigma2) /\
    (defs_update hds a y hds') /\
    (Sigma' = Sigma1 & x ~ (item_obj T hds') & Sigma2).
