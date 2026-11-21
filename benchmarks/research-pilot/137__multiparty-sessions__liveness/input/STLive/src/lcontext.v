From Paco Require Import paco.

From live_mpst.STBase Require Import src.expr src.header src.local.

Require Import List Coq.Arith.PeanoNat Morphisms Relations Setoid.

Require Import Coq.Program.Equality.

Import ListNotations.

Notation opt_lbl := nat.

Inductive label: Type :=
  | lrecv: part -> part -> option sort -> opt_lbl -> label
  | lsend: part -> part -> option sort -> opt_lbl -> label
  | lcomm: part -> part -> opt_lbl -> label.

Definition ispSubjl r l :=
  match l with
  | lsend p q _ _ => p=r
  | lrecv p q _ _=> p=r
  | lcomm p q _ => p=r \/ q=r
  end.

From MMaps Require Import MMaps.

Module M := MMaps.RBT.Make(Nat).

Module MF := MMaps.Facts.Properties Nat M.

Definition tctx: Type := M.t ltt.

Definition both {A:Type} (z: nat) (o:option A) (o':option A) :=
 match o,o' with
   | Some _, None   => o
   | None, Some _   => o'
   | _,_            => None
 end.

Definition disj_merge {A:Type} (g1 g2:M.t A) (H:MF.Disjoint g1 g2)  :=
  M.merge both g1 g2.

Inductive tctxR: tctx -> label -> tctx -> Prop :=
  | Rsend: forall p q xs n s T,
            p <> q ->
            onth n xs = Some (s, T) ->
            tctxR (M.add p (ltt_send q xs) M.empty) (lsend p q (Some s) n) (M.add p T M.empty)
  | Rrecv: forall p q xs n s T,
            p <> q ->
            onth n xs = Some (s, T) ->
            tctxR (M.add p (ltt_recv q xs) M.empty) (lrecv p q (Some s) n) (M.add p T M.empty)
  | Rcomm: forall p q g1 g1' g2 g2' s s' n (H1: MF.Disjoint g1 g2) (H2: MF.Disjoint g1' g2'),
            p <> q ->
            tctxR g1 (lsend p q (Some s) n) g1'  ->
            tctxR g2 (lrecv q p (Some s') n) g2' ->
            subsort s s' ->
            tctxR (disj_merge g1 g2 H1) (lcomm p q n) (disj_merge g1' g2' H2)
  | RvarI: forall g l g' p T,
            tctxR g l g' ->
            M.mem p g = false ->
            tctxR (M.add p T g) l (M.add p T g')
  | Rstruct: forall g1 g1' g2 g2' l,
    tctxR g1' l g2' ->
    M.Equal g1 g1' ->
    M.Equal g2 g2' ->
    tctxR g1 l g2.

Definition tctxRE l c := exists c', tctxR c l c'.

Definition tctxRF l c c' := tctxR c l c'.

Definition m_update (p:nat) (t:ltt) (g:tctx) := M.add p t (M.remove p g).
