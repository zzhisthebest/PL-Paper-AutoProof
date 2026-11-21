Require Export Metalib.Metatheory.

Require Import Definitions.

Require Import Infrastructure.

From Stdlib Require Import Lia.

Inductive tpre : typ -> typ -> Prop :=
| tp_tvar : forall x,
    tpre (t_fvar x) (t_fvar x)
| tp_i :
    tpre t_int t_int
| tp_all : forall L A B,
    (forall x, x \notin L ->
            tpre (A open_tt_var x) (B open_tt_var x)) ->
    tpre (t_all A) (t_all B)
| tp_dyn : forall (A:typ),
    type A ->
    tpre A t_dyn
| tp_abs : forall (A B C D:typ),
    tpre A C ->
    tpre B D ->
    tpre (t_arrow A B) (t_arrow C D)
| tp_unit :
    tpre t_unit t_unit
| tp_ref : forall A B,
    tpre A B ->
    tpre (t_ref A) (t_ref B)
.

Inductive epre : exp -> exp -> Prop :=
 | ep_var : forall (x:var),
    epre (e_fvar x) (e_fvar x)
 | ep_i i:
    epre (e_lit i) (e_lit i)
 | ep_unit :
    epre e_unit e_unit
 | ep_abs : forall (e1 e2:exp) (L:vars) A1 A2 B1 B2,
     ( forall x , x \notin  L  ->
      epre  ( open_ee e1 (e_fvar x) )   ( open_ee e2 (e_fvar x) )  )  ->
      tpre A1 A2 ->
      tpre B1 B2 ->
     epre (e_abs A1 e1 B1) (e_abs A2 e2 B2)
 | ep_tabs : forall (e1 e2:exp) (L:vars) A1 A2,
      (forall x , x \notin  L  ->
      epre  ( open_te e1 (t_fvar x) )   ( open_te e2 (t_fvar x) )  )  ->
      (forall X, X \notin L ->
      tpre (A1 open_tt_var X) (A2 open_tt_var X) ) ->
     epre (e_tabs e1 A1) (e_tabs e2 A2)
 | ep_app : forall (e1 e2 e1' e2':exp) ,
     epre e1 e1' ->
     epre e2 e2' ->
     epre (e_app e1 e2) (e_app e1' e2')
 | ep_tapp : forall (e1 e2:exp) A B,
     tpre A B ->
     epre e1 e2 ->
     epre (e_tapp e1 A) (e_tapp e2 B)
 | ep_anno : forall (e1 e2:exp) A B,
     tpre A B ->
     epre e1 e2 ->
     epre (e_anno e1 A) (e_anno e2 B)
 | ep_loc i:
     epre (e_loc i) (e_loc i)
 | ep_ref : forall (e1 e2:exp),
     epre e1 e2 ->
     epre (e_ref e1) (e_ref e2)
 | ep_get : forall (e1 e2:exp),
     epre e1 e2 ->
     epre (e_get e1) (e_get e2)
 | ep_set : forall (e1 e2 e1' e2':exp) ,
     epre e1 e1' ->
     epre e2 e2' ->
     epre (e_set e1 e2) (e_set e1' e2')
.

Inductive mpre : sto -> sto -> Prop :=
 | mp_nil :
    mpre nil nil
 | mp_cons: forall v1 m1 v2 m2,
    epre v1 v2 ->
    mpre m1 m2 ->
    mpre (v1::m1) (v2::m2).

Inductive ppre : phi -> phi -> Prop :=
 | pp_nil :
    ppre nil nil
 | pp_cons: forall t1 m1 t2 m2,
    tpre t1 t2 ->
    ppre m1 m2 ->
    ppre (t1::m1) (t2::m2).

Inductive cpre : env -> env -> Prop :=
  | cp_nil:
      cpre nil nil
  | cp_cons: forall E F x A1 A2,
      tpre A1 A2 ->
      cpre E F ->
      cpre ([(x ,bind_typ A1)] ++ E) ([(x, bind_typ A2)] ++ F)
  | cp_cons2: forall E F x,
      cpre E F ->
      cpre (x ~tvar ++ E) (x ~tvar ++ F)
.

Theorem SGG_both: forall E1 E2 e1 e2 dir T P mu,
   P |== mu ->
   cpre E1 E2 ->
   epre e1 e2 ->
   typing E1 P e1 dir T ->
   exists T', typing E2 P e2 dir T' /\  tpre T T'.

Theorem dynamic_guarantee_dir: forall e1 e2 P1 P2 mu1 mu1' mu2 e1' dir T1 T2,
 P1 |== mu1 ->
 P2 |== mu2 ->
 mpre mu1 mu2 ->
 epre e1 e2 ->
 typing nil P1 e1 dir T1 ->
 typing nil P2 e2 dir T2 ->
 step ( e1, mu1) ((r_e e1'),mu1') ->
 exists e2' mu2', step (e2,mu2) ((r_e e2'),mu2') /\
 epre e1' e2' /\ mpre mu1' mu2'.
