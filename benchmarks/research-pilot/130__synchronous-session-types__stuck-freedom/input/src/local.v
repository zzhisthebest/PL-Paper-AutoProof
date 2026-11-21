From mathcomp Require Import ssreflect.seq all_ssreflect.

Require Import List String Coq.Arith.PeanoNat Relations ZArith Datatypes Setoid Morphisms Coq.Logic.Decidable Coq.Program.Basics Coq.Init.Datatypes.

Import ListNotations.

Open Scope list_scope.

From Paco Require Import paco.

Import ListNotations.

From SST Require Import src.header src.sim src.expr.

Section ltt.

CoInductive ltt: Type :=
  | ltt_end : ltt
  | ltt_recv: part -> list (option(sort*ltt)) -> ltt
  | ltt_send: part -> list (option(sort*ltt)) -> ltt.

Definition ltt_id (s: ltt): ltt :=
  match s with
    | ltt_end      => ltt_end
    | ltt_recv p l => ltt_recv p l
    | ltt_send p l => ltt_send p l
  end.

Inductive local  : Type :=
  | l_var : fin -> local
  | l_end : local
  | l_send : part -> list (option (sort * local)) -> local
  | l_recv : part -> list (option (sort * local)) -> local
  | l_rec : local -> local .

Section local_ind_ref.

Variable P : local -> Prop.

End local_ind_ref.

Fixpoint incr_freeL (fv m : fin) (T : local) :=
  match T with
    | l_var n        => l_var (if fv <= n then (n + m) else n)
    | l_end          => l_end
    | l_send p lis => l_send p (List.map (fun u =>
          match u with
            | Some (s, g) => Some (s, incr_freeL fv m g)
            | None        => None
          end) lis)
    | l_recv p lis => l_recv p (List.map (fun u =>
          match u with
            | Some (s, g) => Some (s, incr_freeL fv m g)
            | None        => None
          end) lis)
    | l_rec g        => l_rec (incr_freeL (S fv) m g)
  end.

Inductive subst_local : fin -> fin -> local -> local -> local -> Prop :=
  | subl_var_is   : forall G t m,                            subst_local t m G (l_var t) (incr_freeL 0 m G)
  | subl_var_notz : forall G t m, t <> 0 ->                  subst_local t m G (l_var 0) (l_var 0)
  | subl_var_not1 : forall G t t' m, t <> S t' -> t <= t' -> subst_local t m G (l_var (S t')) (l_var (t'))
  | subl_var_not2 : forall G t t' m, t <> S t' -> t' < t  -> subst_local t m G (l_var (S t')) (l_var (S t'))
  | subl_end      : forall G t m,                            subst_local t m G l_end l_end
  | subl_send     : forall G t m p xs ys, List.Forall2 (fun u v =>
                           (u = None /\ v = None) \/
                           (exists s g g', u = Some(s, g) /\ v = Some(s, g') /\ subst_local t m G g g')
                                                  ) xs ys -> subst_local t m G (l_send p xs) (l_send p ys)
  | subl_recv     : forall G t m p xs ys, List.Forall2 (fun u v =>
                           (u = None /\ v = None) \/
                           (exists s g g', u = Some(s, g) /\ v = Some(s, g') /\ subst_local t m G g g')
                                                  ) xs ys -> subst_local t m G (l_recv p xs) (l_recv p ys)
  | subl_rec      : forall G t m P Q, subst_local (S t) (S m) G P Q -> subst_local t m G (l_rec P) (l_rec Q).

Inductive betaL : relation local :=
  | lttS : forall G G', subst_local 0 0 (l_rec G) G G' -> betaL (l_rec G) G'.

Inductive lttT (R : local -> ltt -> Prop) : local -> ltt -> Prop :=
  | lttT_end  : lttT R l_end ltt_end
  | lttT_send : forall p xs ys, List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g g', u = Some(s, g) /\ v = Some(s, g') /\ R g g')) xs ys -> lttT R (l_send p xs) (ltt_send p ys)
  | lttT_recv : forall p xs ys, List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g g', u = Some(s, g) /\ v = Some(s, g') /\ R g g')) xs ys -> lttT R (l_recv p xs) (ltt_recv p ys)
  | lttT_rec  : forall G Q G', subst_local 0 0 (l_rec G) G Q -> lttT R Q G' -> lttT R (l_rec G) G'.

Definition lttTC G G' := paco2 lttT bot2 G G'.

Inductive wfL : local -> Prop :=
  | wfl_var : forall n, wfL (l_var n)
  | wfl_end : wfL l_end
  | wfl_send : forall p lis, SList lis -> List.Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ wfL g)) lis -> wfL (l_send p lis)
  | wfl_recv : forall p lis, SList lis -> List.Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ wfL g)) lis -> wfL (l_recv p lis)
  | wfl_rec  : forall g, wfL g -> wfL (l_rec g).

Inductive guardL : fin -> fin -> local -> Prop :=
  | gl_nil  : forall m T, guardL 0 m T
  | gl_end  : forall n m, guardL n m l_end
  | gl_send : forall n m p lis, List.Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ guardL n m g)) lis -> guardL (S n) m (l_send p lis)
  | gl_recv : forall n m p lis, List.Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ guardL n m g)) lis -> guardL (S n) m (l_recv p lis)
  | gl_rec  : forall n m g Q, subst_local 0 0 (l_rec g) g Q -> guardL n m Q -> guardL n (S m) (l_rec g).

Fixpoint wfrec (R1: sort -> sort -> Prop) (R2: ltt -> ltt -> Prop) (l1 l2: list (option(sort*ltt))): Prop :=
  match (l1,l2) with
    | (Datatypes.None::xs, Datatypes.None::ys)               => wfrec R1 R2 xs ys
    | (Datatypes.Some (s',t')::xs, Datatypes.Some (s,t)::ys) => R1 s' s /\ R2 t t' /\ wfrec R1 R2 xs ys
    | (Datatypes.None::xs, Datatypes.Some(s,t)::ys)          => wfrec R1 R2 xs ys
    | (nil, _)                                               => True
    | _                                                      => False
  end.

Fixpoint wfsend (R1: sort -> sort -> Prop) (R2: ltt -> ltt -> Prop) (l1 l2: list (option(sort*ltt))): Prop :=
  match (l1,l2) with
    | (Datatypes.None::xs, Datatypes.None::ys)               => wfsend R1 R2 xs ys
    | (Datatypes.Some (s,t)::xs, Datatypes.Some (s',t')::ys) => R1 s s' /\ R2 t t' /\ wfsend R1 R2 xs ys
    | (Datatypes.None::xs, Datatypes.Some(s',t')::ys)        => wfsend R1 R2 xs ys
    | (nil, _)                                               => True
    | _                                                      => False
  end.

Inductive subtype (R: ltt -> ltt -> Prop): ltt -> ltt -> Prop :=
  | sub_end: subtype R ltt_end ltt_end
  | sub_in : forall p xs ys,
                    wfrec subsort R ys xs ->
                    subtype R (ltt_recv p xs) (ltt_recv p ys)
  | sub_out : forall p xs ys,
                     wfsend subsort R xs ys ->
                     subtype R (ltt_send p xs) (ltt_send p ys).

Definition subtypeC l1 l2 := paco2 subtype bot2 l1 l2.

End ltt.
