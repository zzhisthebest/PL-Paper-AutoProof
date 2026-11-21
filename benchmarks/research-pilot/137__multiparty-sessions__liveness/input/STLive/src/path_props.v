From Paco Require Import paco.

From live_mpst.STBase Require Import src.expr src.header src.local src.projection src.step src.global.

From live_mpst.STLive Require Import src.lcontext src.assoc.

Require Import List String Coq.Arith.PeanoNat Morphisms Relations.

Require Import Coq.Program.Equality.

Import ListNotations.

CoInductive coseq (A: Type): Type :=
  | conil : coseq A
  | cocons: A -> coseq A -> coseq A.

Arguments conil {_}.

Arguments cocons {_} _ _.

Definition coseq_id {A: Type} (c: coseq A): coseq A :=
  match c with
    | conil       => conil
    | cocons x xs => cocons x xs
  end.

Notation local_path := (coseq (tctx*(option label))) (only parsing).

Variant valid_pathGI {A:Type} (V: A  ->  label -> A -> Prop)
(R: coseq (A * option label) ->  Prop)
:
coseq (A * option label) -> Prop :=
  | nil_validGI: valid_pathGI V R conil
  | cons_nill_validGI: forall x, valid_pathGI V R (cocons (x, None) conil)
  | cons_cons_validGI: forall x y l l' xs,
  R (cocons (x,l') xs) ->
    V y l x ->
    valid_pathGI V R (cocons (y,Some l) (cocons (x,l') xs)).

Definition valid_path_GC {A:Type} (V: A-> label -> A-> Prop) := paco1 (valid_pathGI V) bot1.

Definition local_path_vcriteria := (fun x1 l  x2  =>
  match (x1,l,x2) with
    | ((g1,lcomm p q ell),g2) => tctxR g1 (lcomm p q ell) g2
    | _ => False
  end
).

Definition local_valid_pathC := valid_path_GC local_path_vcriteria.

Inductive eventually {A: Type} (F: coseq A -> Prop): coseq A -> Prop :=
  | evh: forall xs, F xs -> eventually F xs
  | evc: forall x xs, eventually F xs -> eventually F (cocons x xs).

Inductive alwaysG {A: Type} (F: coseq A -> Prop) (R: coseq A -> Prop): coseq A -> Prop :=
  | alwn: F conil -> alwaysG F R conil
  | alwc: forall x xs, F (cocons x xs) -> R xs -> alwaysG F R (cocons x xs).

Inductive until {A:Type} (F: coseq A -> Prop) (G: coseq A -> Prop) : coseq A -> Prop:=
  | untilh : forall xs, G xs -> until F G xs
  | untilc: forall x xs, F (cocons x xs) -> until F G xs -> until F G (cocons x xs).

Inductive weak_untilI {A:Type}  (F: coseq A -> Prop) (G: coseq A -> Prop) (R:coseq A -> Prop): coseq A -> Prop:=
  | wuntilh : forall xs, G xs -> weak_untilI F G R xs
  | wuntilc: forall x xs, F (cocons x xs) -> R xs -> weak_untilI F G R (cocons x xs)
  | wuntiln : F conil -> weak_untilI F G R conil.

Definition weak_untilC {A:Type} (F: coseq A -> Prop) G := paco1 (weak_untilI F G) bot1.

Definition alwaysCG {A:Type} (F: coseq A -> Prop) := paco1 (alwaysG F) bot1.

Definition next {A:Type} P (xs:coseq A) := match xs with
            | conil => False
            | cocons x xs => P xs end.

Definition to_path_prop {A:Type} (P:A -> Prop) (on_conil : Prop): (coseq (A*option label)-> Prop) :=
    fun u=> match u with
            | conil => on_conil
            | cocons (g,_) _ => P g
    end.

Definition headComm (p q: part) (pt: local_path): Prop :=
  match pt with
    | cocons (g, Some (lcomm a b n)) xs =>
    p=a /\ q=b
    | _                          => False
  end.

Definition fair_path_local_inner (pt: local_path): Prop :=
  forall p q n, to_path_prop (tctxRE (lcomm p q n)) False pt ->  eventually (headComm p q) pt.

Definition fair_path := alwaysCG fair_path_local_inner.

Definition live_path_inner (pt: local_path) : Prop := forall p q s n,
(to_path_prop (tctxRE (lsend p q (Some s) n)) False pt -> eventually (headComm p q) pt) /\
(to_path_prop (tctxRE (lrecv p q (Some s) n)) False pt -> eventually (headComm q p) pt).

Definition live_path := alwaysCG live_path_inner.

Definition weak_safety (c: tctx ) :=
forall p q s s'  k k', tctxRE (lsend p q (Some s) k) c -> tctxRE (lrecv q p (Some s') k') c ->
                               tctxRE (lcomm p q k) c.

Inductive safe (R: tctx -> Prop): tctx -> Prop :=
  | safety_red :  forall c, weak_safety c -> (forall p q c' k,
    tctxR c (lcomm p q k) c' -> exists c'', M.Equal c' c'' /\ R c'')
    ->  safe R c.

Definition safeC c := paco1 safe bot1 c.

Definition tctxRcomm (g: tctx) (g':tctx) := exists p q ell, tctxR g (lcomm p q ell) g'.

Definition tctxRtc := clos_refl_trans tctx tctxRcomm.

Definition all_fair_live (g:tctx) := forall l xs,
  local_valid_pathC (cocons (g, l) xs) -> fair_path (cocons (g, l) xs) ->
  live_path (cocons (g, l) xs).

Definition liveCtx (g: tctx) := forall g',
  tctxRtc g g' -> all_fair_live g'.

Notation global_path := (coseq (gtt*option label)) (only parsing).

Section global_path.

Definition global_path_vcriteria :  gtt -> label -> gtt -> Prop := fun x1 l x2 =>
    match (x1,l,x2) with
        | (g1,lcomm p q ell,g2) => gttstepC g1 g2 p q ell
        | _ =>False
    end.

Definition global_valid_pathC := valid_path_GC global_path_vcriteria.

Definition global_comm_enabled p q n g := exists g', gttstepC g g' p q n.

Definition headComm_global (p q: part) (pt: global_path): Prop :=
  match pt with
    | cocons (g, Some (lcomm a b n)) xs =>
     p=a /\ q=b
    | _                          => False
  end.

Definition fair_path_inner_global (pt: global_path): Prop :=
  forall p q n,
  to_path_prop (global_comm_enabled p q n) False pt ->
  eventually (headComm_global p q) pt.

Definition fair_path_global := alwaysCG fair_path_inner_global.

Definition global_label_enabled l g:= match l with
    | lsend p q (Some s) n => exists xs g',
        projectionC g p  (ltt_send q xs) /\ onth n xs=Some (s,g')
    | lrecv p q (Some s) n => exists xs g',
        projectionC g p  (ltt_recv q xs) /\ onth n xs=Some (s,g')
    | lcomm p q n => exists g', gttstepC g g' p q n
    | _ => False end.

Definition live_path_inner_global (pt: global_path) : Prop := forall p q s n,
(to_path_prop (global_label_enabled (lsend p q (Some s) n)) False pt ->
eventually (headComm_global p q) pt) /\
(to_path_prop (global_label_enabled (lrecv p q (Some s) n)) False pt ->
eventually (headComm_global q p) pt).

Definition live_path_global := alwaysCG live_path_inner_global.

Definition all_fair_live_global (g:gtt) := forall l xs,
  global_valid_pathC (cocons (g, l) xs) -> fair_path_global (cocons (g, l) xs) ->
  live_path_global (cocons (g, l) xs).

Definition live_type_global (g: gtt) := forall g',
  gttstepRtc g g' -> all_fair_live_global g'.

End global_path.
