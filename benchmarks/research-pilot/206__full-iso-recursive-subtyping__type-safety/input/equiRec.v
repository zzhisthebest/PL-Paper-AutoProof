Require Import Program.Equality.

Require Import Metalib.Metatheory.

Require Export LibTactics.

Require Import Lia.

Require Export erasure.

Inductive eqe : tctx -> actx -> typ -> typ -> Prop :=
 | e_assump : forall (D:tctx) (H:actx) (A B:typ),
      In ( A ,  B )  H  ->
     WFT D A ->
     WFT D B ->
     eqe D H A B
 | e_refl : forall (D:tctx) (H:actx) (A:typ),
     WFT D A ->
     eqe D H A A
 | e_trans : forall (D:tctx) (H:actx) (A C B:typ),
     eqe D H A B ->
     eqe D H B C ->
     eqe D H A C
 | e_fld : forall (D:tctx) (H:actx) (A:typ),
     WFT D (t_mu A) ->
     eqe D H (t_mu A)  (open_typ_wrt_typ  A (t_mu A) )
 | e_unfld : forall (D:tctx) (H:actx) (A:typ),
     WFT D (t_mu A) ->
     eqe D H  (open_typ_wrt_typ  A (t_mu A) )  (t_mu A)
 | e_arrfix : forall (D:tctx) (H:actx) (A1 A2 B1 B2:typ),
     eqe D  (cons ( (t_arrow A1 A2) ,  (t_arrow B1 B2) )  H )  A1 B1 ->
     eqe D  (cons ( (t_arrow A1 A2) ,  (t_arrow B1 B2) )  H )  A2 B2 ->
     eqe D H (t_arrow A1 A2) (t_arrow B1 B2).

Notation unfold_mu t :=
    (open_typ_wrt_typ t (t_mu t)).

Definition cctx_sem (cl : actx) (Rel: typ -> typ -> Prop) : Type :=
  Forall (fun l => match l with ( A, B) => Rel A B end) cl.

Definition reverse_E (E: cctx) :=
  map (fun v => match v with (A, B) =>  (B, A) end) E.

Definition reverse_A (E: actx) :=
  List.map (fun v => match v with (A, B) =>  (B, A) end) E.

Inductive eq_env: list (typ * typ) -> list (typ * typ) -> Prop :=
| eq_env_nil: eq_env nil nil
| eq_env_cons_same: forall t1 t2 E1 E2,
    eq_env E1 E2 ->
    eq_env ((t1,t2)::E1) ((t1,t2)::E2)
| eq_env_cons_rev: forall t1 t2 E1 E2,
    eq_env E1 E2 ->
    eq_env ((t1,t2)::E1) ((t2,t1)::E2)
.

Definition to_assump (E: cctx) :=
  List.map (fun cx_v => match cx_v with (_, v) => v end) E.
