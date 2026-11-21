Set Implicit Arguments.

From TLC Require Import LibList.

From TLC Require Import LibLN.

Require Import DeclDef.

Require Import FDef.

Require Import FInfra.

Require Import DeclInfra.

Inductive d2fgen : denv -> dtyp -> ftrm -> dtyp -> ftrm -> Prop :=
  | d2fgen_empty : forall E t s,
      dokt E ->
      dtype t ->
      fterm s ->
      (dfv_tt t) \- (dfv_tt_env E) = \{} ->
      d2fgen E t s t s
  | d2fgen_step : forall x E t t2 s s2,
      x \in (dfv_tt (t fopen_tt_var x) \- dfv_tt_env E) ->
      x \notin dfv_tt t ->
      x \notin ffv_te s ->
      d2fgen E (dtyp_all t)
                 (ftrm_tabs s)
                 t2 s2 ->
      d2fgen E (t fopen_tt_var x) (s fopen_te_var x) t2 s2.
