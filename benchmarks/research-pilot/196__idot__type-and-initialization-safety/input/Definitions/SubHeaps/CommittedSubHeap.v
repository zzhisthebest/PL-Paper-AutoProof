Set Implicit Arguments.

Require Import LibExtra AbstractSyntax.

Require Import Typing Initialization InitTyping InitWeakening GeneralTyping.

Inductive committed_heap_def : init_ctx -> heap_def -> Prop :=

| committed_heap_def_typ : forall Delta A T,
    committed_heap_def Delta (heap_def_typ A T)

| committed_heap_def_trm : forall Delta a x,
    binds x committed Delta ->
    committed_heap_def Delta (heap_def_trm a (Some x)).

Inductive committed_heap_defs : init_ctx -> heap_defs -> Prop :=
| committed_heap_defs_nil : forall Delta,
    committed_heap_defs Delta nil

| committed_heap_defs_cons : forall Delta hd hds,
    committed_heap_defs Delta hds ->
    committed_heap_def Delta hd ->
    committed_heap_defs Delta (cons hd hds).

Inductive committed_heap_item :
  ctx -> init_ctx -> item -> Prop :=

| committed_heap_lit : forall Gamma Delta l,
    Gamma ⸴ Delta ⊢c l ->
    committed_heap_item Gamma Delta (item_lit l)

| committed_heap_obj : forall Gamma Delta T hds,
    committed_heap_defs Delta hds ->
    committed_heap_item Gamma Delta (item_obj T hds).

Definition well_committed_heap (Gamma : ctx) (Delta : init_ctx) (Sigma : heap) :=
  dom Gamma = dom Delta /\
  dom Delta = dom Sigma /\
  forall x itm,
    binds x committed Delta ->
    binds x itm Sigma ->
    committed_heap_item Gamma Delta itm.

Definition more_committed Delta Delta' :=
  (forall x, binds x committed Delta -> binds x committed Delta').
