From Paco Require Import paco.

From live_mpst.STBase Require Import src.expr src.header src.local src.global src.projection src.part src.balanced src.merge src.gttreeh src.step.

From live_mpst.STLive Require Import src.lcontext src.assoc src.wfltt.

Require Import List String Ring Coq.Arith.PeanoNat Morphisms Relations Setoid.

Require Import Coq.Program.Equality.

Require Import Coq.Init.Logic.

Require Import Lia Arith.

Inductive ltth :=
    | ltth_send : part -> list (option (sort*ltth)) -> ltth
    | ltth_recv : part -> list (option (sort*ltth)) -> ltth
    | ltth_hol :  nat -> ltth.

Section ltth_ind.

Variable P : ltth -> Prop.

End ltth_ind.

Definition max_option_list (xs: list (option nat)) : nat :=
    list_max (map (fun u=> match u with
        | None => 0
        | Some x => x end
    ) xs).

Inductive wfgtth : gtth -> Prop :=
    | wfg_hol : forall n, wfgtth (gtth_hol n)
    | wfg_hsend : forall p q xs, SList xs ->
    Forall (fun u=> u=None \/ exists s g, u= Some (s,g) /\ wfgtth g) xs->
        wfgtth (gtth_send p q xs).

Inductive wfltth : ltth -> Prop :=
    | wfgl_hol : forall n, wfltth (ltth_hol n)
    | wfgl_hsend : forall p xs, SList xs ->
    Forall (fun u=> u=None \/ exists s g, u= Some (s,g) /\ wfltth g) xs->
        wfltth (ltth_send p xs)
    | wfgl_hrecv : forall p xs, SList xs ->
    Forall (fun u=> u=None \/ exists s g, u= Some (s,g) /\ wfltth g) xs->
        wfltth (ltth_recv p xs)
    .

Inductive used_in_ltth : nat -> ltth -> Prop :=
    | used_hol : forall n, used_in_ltth n (ltth_hol n)
    | used_send : forall n xs p k s ll, onth k xs = Some (s, ll) -> used_in_ltth n ll ->
    used_in_ltth n (ltth_send p xs)
    | used_recv : forall n xs p k s ll, onth k xs = Some (s, ll) -> used_in_ltth n ll ->
    used_in_ltth n (ltth_recv p xs).

Definition fills_holes (ls :list (option ltth)) (l : ltth) :=
    forall n, used_in_ltth n l -> exists s, onth n ls = Some s.

Inductive typ_ltth : ltth -> list (option ltt) -> ltt -> Prop :=
    | typ_ltth_hol : forall n ll xs,
    onth n xs = Some ll -> typ_ltth (ltth_hol n) xs ll
    | typ_ltth_send :
    forall xs ys p ls,
    Forall2
    (fun u v=> (u=None /\ v= None)
    \/ exists s lt ltr, u=Some (s,lt) /\ v= Some (s, ltr) /\ typ_ltth lt ls ltr) xs ys ->
    typ_ltth (ltth_send p xs) ls (ltt_send p ys)
    | typ_ltth_recv :
    forall xs ys p ls,
    Forall2
    (fun u v=> (u=None /\ v= None)
    \/ exists s lt ltr, u=Some (s,lt) /\ v= Some (s, ltr) /\ typ_ltth lt ls ltr) xs ys ->
    typ_ltth (ltth_recv p xs) ls (ltt_recv p ys).

Inductive ishlParts : part -> ltth -> Prop :=
    | hal_send: forall p xs, ishlParts p (ltth_send p xs)
    | hal_rec: forall p xs, ishlParts p (ltth_recv p xs)
    | hal_sendr : forall p r n lis s g,  p <> r -> onth n lis= Some (s,g) ->
    ishlParts r g -> ishlParts r (ltth_send p lis)
    | hal_recvr : forall p r n lis s g,  p <> r -> onth n lis= Some (s,g) ->
    ishlParts r g -> ishlParts r (ltth_recv p lis).

Definition typ_p_send_ltth (ls:list (option ltt)) (ctx: ltth) (p:part) (t:ltt) :=
    typ_ltth ctx ls t /\  (ishlParts p ctx -> False) /\

    (forall n, used_in_ltth n ctx -> exists xs, onth n ls=Some (ltt_send p xs)).

Definition typ_p_recv_ltth (ls:list (option ltt)) (ctx: ltth) (p:part) (t:ltt) :=
    typ_ltth ctx ls t /\  (ishlParts p ctx -> False) /\
    (forall n, used_in_ltth n ctx -> exists xs, onth n ls=Some (ltt_recv p xs)).

Fixpoint gtth_height (gh : gtth) : nat :=
    match gh with
    | gtth_hol n => 0
    | gtth_send p q xs =>
    list_max (map (fun u=> match u with
        | None => 0
        | Some (s,x) => gtth_height x end
        ) xs)+1 end
.

Section gtth_ind_by_height.

Variable P : gtth -> Prop.

End gtth_ind_by_height.
