From Paco Require Import paco.

From live_mpst.STBase Require Import src.expr src.header src.local.

From live_mpst.STLive Require Import src.lcontext.

Require Import List String Coq.Arith.PeanoNat Morphisms Relations Setoid.

Require Import Coq.Program.Equality.

Import ListNotations.

Variant wfltt (R: ltt -> Prop) : ltt -> Prop :=
    | wfltt_end : wfltt R ltt_end
    | wfltt_send: forall p xs, SList xs -> Forall
    (fun u=> u= None \/ exists s g, u= Some (s,g)
        /\ R g) xs -> wfltt R (ltt_send p xs)
    | wfltt_recv: forall p xs, SList xs -> Forall (fun u=> u= None \/ exists s g, u= Some (s,g)
        /\ R g) xs -> wfltt R (ltt_recv p xs).

Definition wflttC := paco1 wfltt bot1.

Definition tctx_wf (g:tctx):= forall p l,
(M.find p g = Some l -> wflttC l).
