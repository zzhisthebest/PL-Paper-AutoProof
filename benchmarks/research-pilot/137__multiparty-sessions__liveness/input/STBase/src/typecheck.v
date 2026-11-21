From mathcomp Require Import all_ssreflect.

Require Import List String Coq.Arith.PeanoNat Relations ZArith Datatypes Setoid Morphisms Coq.Logic.Decidable Coq.Program.Basics Coq.Init.Datatypes.

Import ListNotations.

Open Scope list_scope.

From Paco Require Import paco.

Import ListNotations.

From live_mpst.STBase Require Import src.header src.sim src.expr src.process src.local src.global src.balanced.

Definition ctxS := list (option sort).

Definition ctxT := list (option ltt).

Inductive typ_expr: ctxS -> expr -> sort -> Prop :=
  | sc_var : forall c s t, Some t = onth s c -> typ_expr c (e_var s) t
  | sc_vali: forall c i, typ_expr c (e_val (vint i)) sint
  | sc_valn: forall c i, typ_expr c (e_val (vnat i)) snat
  | sc_valb: forall c b, typ_expr c (e_val (vbool b)) sbool
  | sc_succ: forall c e, typ_expr c e snat ->
                         typ_expr c (e_succ e) snat
  | sc_neg : forall c e, typ_expr c e sint ->
                         typ_expr c (e_neg e) sint
  | sc_sub : forall c e s s', typ_expr c e s ->
                                 subsort s s' ->
                                 typ_expr c e s'
  | sc_not : forall c e, typ_expr c e sbool ->
                         typ_expr c (e_not e) sbool
  | sc_gt  : forall c e1 e2, typ_expr c e1 sint ->
                             typ_expr c e2 sint ->
                             typ_expr c (e_gt e1 e2) sbool
  | sc_plus: forall c e1 e2, typ_expr c e1 sint ->
                             typ_expr c e2 sint ->
                             typ_expr c (e_plus e1 e2) sint
  | sc_det  : forall c e1 e2 s, typ_expr c e1 s -> typ_expr c e2 s -> typ_expr c (e_det e1 e2) s.

Inductive typ_proc: ctxS -> ctxT -> process -> ltt -> Prop :=
  | tc_inact: forall cs ct,     typ_proc cs ct (p_inact) (ltt_end)
  | tc_var  : forall cs ct s t, Some t = onth s ct -> wfC t ->
                                typ_proc cs ct (p_var s) t
  | tc_mu   : forall cs ct p t,       typ_proc cs (Some t :: ct) p t ->
                                      typ_proc cs ct (p_rec p) t
  | tc_ite  : forall cs ct e p1 p2 T, typ_expr cs e sbool ->
                                      typ_proc cs ct p1 T ->
                                      typ_proc cs ct p2 T ->
                                      typ_proc cs ct (p_ite e p1 p2) T
  | tc_sub  : forall cs ct p t t',    typ_proc cs ct p t ->
                                      subtypeC t t' -> wfC t' ->
                                      typ_proc cs ct p t'
  | tc_recv : forall cs ct p STT P,
                     length P = length STT -> SList P ->
                     Forall2 (fun u v => (u = None /\ v = None) \/
                     (exists p s t, u = Some p /\ v = Some (s, t) /\ typ_proc (Some s :: cs) ct p t)) P STT ->
                     typ_proc cs ct (p_recv p P) (ltt_recv p STT)
  | tc_send : forall cs ct p l e P S T, typ_expr cs e S ->
                                        typ_proc cs ct P T ->
                                        typ_proc cs ct (p_send p l e P) (ltt_send p (extendLis l (Some (S,T)))).

Section typ_proc_ind_ref.

Variable P : ctxS -> ctxT -> process -> ltt -> Prop.

End typ_proc_ind_ref.

Fixpoint RemoveT (n : fin) (Gt : ctxT) : ctxT :=
  match Gt with
    | x::xs =>
      match n with
        | S m => x :: RemoveT m xs
        | 0   => None :: xs
      end
    | [] => []
  end.

Fixpoint extendT (n : fin) (T : ltt) (Gt : ctxT) : ctxT :=
  match Gt with
    | x::xs =>
      match n with
        | S m => x :: extendT m T xs
        | 0   => Some T :: xs
      end
    | [] =>
      match n with
        | S m => None :: extendT m T []
        | 0   => [Some T]
      end
  end.
