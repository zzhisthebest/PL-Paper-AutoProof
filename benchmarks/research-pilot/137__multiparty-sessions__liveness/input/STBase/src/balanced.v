From mathcomp Require Import all_ssreflect.

Require Import List String Coq.Arith.PeanoNat Relations ZArith Datatypes Setoid Morphisms Coq.Logic.Decidable Coq.Program.Basics Coq.Init.Datatypes.

Import ListNotations.

Open Scope list_scope.

From Paco Require Import paco.

Import ListNotations.

From live_mpst.STBase Require Import src.header src.sim src.expr src.local src.global src.part src.gttreeh.

Inductive gnode : Type :=
  | gnode_end : gnode
  | gnode_pq : part -> part -> gnode
  | gnode_s  : sort -> gnode.

Inductive gttmap : gtt -> list fin -> option fin -> gnode -> Prop :=
  | gmap_end : gttmap gtt_end nil None gnode_end
  | gmap_pq  : forall p q xs, gttmap (gtt_send p q xs) nil None (gnode_pq p q)
  | gmap_con : forall n lis xs p q st gk s gn, onth n xs = Some (st, gk) -> gttmap gk lis s gn -> gttmap (gtt_send p q xs) (n :: lis) s gn
  | gmap_st  : forall n xs p q st gk, onth n xs = Some (st, gk) -> gttmap (gtt_send p q xs) nil (Some n) (gnode_s st).

Inductive lnode : Type :=
  | lnode_end  : lnode
  | lnode_send : part -> lnode
  | lnode_recv : part -> lnode
  | lnode_s    : sort -> lnode.

Inductive lttmap : ltt -> list fin -> option fin -> lnode -> Prop :=
  | lmap_end  : lttmap ltt_end nil None lnode_end
  | lmap_send : forall p xs, lttmap (ltt_send p xs) nil None (lnode_send p)
  | lmap_recv : forall p xs, lttmap (ltt_recv p xs) nil None (lnode_recv p)
  | lmap_cons : forall n lis xs p st gk s gn, onth n xs = Some (st, gk) -> lttmap gk lis s gn -> lttmap (ltt_send p xs) (n :: lis) s gn
  | lmap_conr : forall n lis xs p st gk s gn, onth n xs = Some (st, gk) -> lttmap gk lis s gn -> lttmap (ltt_recv p xs) (n :: lis) s gn
  | lmap_sts  : forall n xs p st gk, onth n xs = Some(st, gk) -> lttmap (ltt_send p xs) nil (Some n) (lnode_s st)
  | lmap_str  : forall n xs p st gk, onth n xs = Some(st, gk) -> lttmap (ltt_recv p xs) nil (Some n) (lnode_s st).

Fixpoint isoList (R: ltt -> ltt -> Prop) (l1 l2: list (option(sort*ltt))): Prop :=
  match (l1,l2) with
    | (Datatypes.None::xs, Datatypes.None::ys)               => isoList R xs ys
    | (Datatypes.Some (s,t)::xs, Datatypes.Some (s',t')::ys) => s = s' /\ R t t' /\ isoList R xs ys
    | (nil, nil)                                             => True
    | (_, _)                                                 => False
  end.

Inductive lttIso (R: ltt -> ltt -> Prop): ltt -> ltt -> Prop :=
  | i_end : lttIso R ltt_end ltt_end
  | i_recv: forall p xs ys, isoList R xs ys -> lttIso R (ltt_recv p xs) (ltt_recv p ys)
  | i_send: forall p xs ys, isoList R xs ys -> lttIso R (ltt_send p xs) (ltt_send p ys).

Definition lttIsoC L L' := paco2 lttIso bot2 L L'.

Inductive isMergeCtx : list (option gtt) -> list (option (list (option gtt))) -> Prop :=
  | cmatm : forall t, isMergeCtx t (Some t :: nil)
  | cmconsn : forall t xs, isMergeCtx t xs -> isMergeCtx t (None :: xs)
  | cmconss : forall t t' t'' xs,
      Forall3S (fun u v w =>
        (u = None /\ v = None /\ w = None) \/
        (exists t, u = None /\ v = Some t /\ w = Some t) \/
        (exists t, u = Some t /\ v = None /\ w = Some t) \/
        (exists t, u = Some t /\ v = Some t /\ w = Some t)
      ) t t' t'' ->
      isMergeCtx t xs -> isMergeCtx t'' (Some t' :: xs).

Inductive usedCtx : (list (option gtt)) -> gtth -> Prop :=
  | used_hol : forall n G, usedCtx (extendLis n (Some G)) (gtth_hol n)
  | used_con : forall ctxG ctxGLis p q ys, isMergeCtx ctxG ctxGLis ->
        List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists ctxGi s g, u = Some ctxGi /\ v = Some (s, g) /\ usedCtx ctxGi g)) ctxGLis ys -> usedCtx ctxG (gtth_send p q ys).

Definition balancedG (G : gtt) := forall w w' p q gn,
  gttmap G w None gn -> (gttmap G (w ++ w') None (gnode_pq p q) \/ gttmap G (w ++ w') None (gnode_pq q p)) ->
  (exists k, forall w', (gttmap G (w ++ w') None (gnode_end) \/ (List.length w' = k /\ exists tc, gttmap G (w ++ w') None tc)) ->
                        exists w2 w0, w' = w2 ++ w0 /\ exists r,
                        gttmap G (w ++ w2) None (gnode_pq p r) \/ gttmap G (w ++ w2) None (gnode_pq r p)).

Definition wfgC G := exists G', gttTC G' G /\ wfG G' /\ (forall n, exists m, guardG n m G') /\ balancedG G.

Definition wfgCw G := exists G', gttTC G' G /\ wfG G' /\ (forall n, exists m, guardG n m G').

Definition wfC T := exists T', lttTC T' T /\ wfL T' /\ (forall n, exists m, guardL n m T').
