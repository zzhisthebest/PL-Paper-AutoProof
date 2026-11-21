From Paco Require Import paco.

From live_mpst.STBase Require Import src.expr src.header src.local src.global src.projection src.part src.balanced src.merge src.gttreeh src.step.

From live_mpst.STLive Require Import src.lcontext src.wfltt src.assoc src.ltth src.path_props.

Require Import List String Coq.Arith.PeanoNat Morphisms Relations Setoid.

Require Import Coq.Program.Equality.

Require Import Coq.Init.Logic Lia.

Import ListNotations.

Section gttstepH_ind_ref.

Variable P : gtth -> nat -> nat -> nat -> gtth  -> Prop.

End gttstepH_ind_ref.

Theorem liveness : forall gamma g,
wfgC g -> projectableA g -> tctx_wf gamma ->
 assoc gamma g ->
liveCtx gamma.
