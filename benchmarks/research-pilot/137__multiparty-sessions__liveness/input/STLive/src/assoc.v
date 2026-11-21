From Paco Require Import paco.

From live_mpst.STBase Require Import src.expr src.header src.local src.global src.projection src.part src.balanced src.merge src.gttreeh.

From live_mpst.STLive Require Import src.lcontext src.wfltt.

Require Import List String Coq.Arith.PeanoNat Morphisms Relations Setoid.

Require Import Coq.Program.Equality.

Import ListNotations.

Definition issubProj (t:ltt) (g:gtt) (p:part) :=
    exists tg, projectionC g p tg /\ subtypeC t tg.

Definition assoc (g: tctx) (gt:gtt) :=
    forall p, (isgPartsC p gt -> exists Tp, M.find p g=Some Tp /\
        issubProj Tp gt p) /\
         (~ isgPartsC p gt -> forall Tpx, M.find p g = Some Tpx -> Tpx=ltt_end).

Section subproj_inversion.

Definition send_cond (xs:list (option (sort*ltt))) (ys:list (option (sort*gtt))) (p:part) :=
    Forall2R (fun x y => x=None
        \/ (exists s elx s' ely, y=Some (s',ely)/\ x=Some (s,elx) /\
        subsort s s' /\
        issubProj elx ely p)) xs ys.

Definition subproj_cont_cond (t:ltt) (ys:list(option(sort*gtt))) (p:part) :=
    Forall (fun y=> (y=None)\/
    (exists s' Gy, y=Some (s', Gy) /\issubProj t Gy p)) ys.

Definition recv_cond (xs:list (option (sort*ltt))) (ys:list (option (sort*gtt))) (p:part) :=
    Forall2R (fun y x => y=None
        \/ (exists s elx s' ely, y=Some (s',ely)/\ x=Some (s,elx) /\
        subsort s' s /\
        issubProj elx ely p)) ys xs.

End subproj_inversion.

Definition typ_p_gtth  (gs:list (option gtt)) (ctx:gtth) p G:=
    typ_gtth gs ctx G /\
    (ishParts p ctx -> False) /\
    Forall
    (fun u : option gtt =>
    u = None \/
    (exists (q : opt_lbl) (lsg : list (option (sort * gtt))),
    u = Some (gtt_send p q lsg) \/
    u = Some (gtt_send q p lsg) \/ u = Some gtt_end)) gs.

Section Forall2_forall.

Variables (A B: Type).

Variable P : option A -> option B -> Prop.

End Forall2_forall.
