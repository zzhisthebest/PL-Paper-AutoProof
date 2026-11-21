Require Import Coq.Logic.FunctionalExtensionality.

Require Import Coq.Program.Equality.

Require Export Metalib.Metatheory.

Require Export Metalib.LibLNgen.

Require Export syntax_ott.

Scheme typ_ind' := Induction for typ Sort Prop.

Definition typ_mutind :=
  fun H1 H2 H3 H4 H5 H6 =>
  typ_ind' H1 H2 H3 H4 H5 H6.

Scheme typ_rec' := Induction for typ Sort Set.

Definition typ_mutrec :=
  fun H1 H2 H3 H4 H5 H6 =>
  typ_rec' H1 H2 H3 H4 H5 H6.

Scheme co_ind' := Induction for co Sort Prop.

Definition co_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 =>
  co_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13.

Scheme co_rec' := Induction for co Sort Set.

Definition co_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 =>
  co_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13.

Scheme exp_ind' := Induction for exp Sort Prop.

Definition exp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 =>
  exp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.

Scheme exp_rec' := Induction for exp Sort Set.

Definition exp_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 =>
  exp_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.

Fixpoint close_exp_wrt_exp_rec (n1 : nat) (x1 : var) (e1 : exp) {struct e1} : exp :=
  match e1 with
    | trm_var_f x2 => if (x1 == x2) then (trm_var_b n1) else (trm_var_f x2)
    | trm_var_b n2 => if (lt_ge_dec n2 n1) then (trm_var_b n2) else (trm_var_b (S n2))
    | trm_unit => trm_unit
    | trm_lit i1 => trm_lit i1
    | trm_abs e2 => trm_abs (close_exp_wrt_exp_rec (S n1) x1 e2)
    | trm_app e2 e3 => trm_app (close_exp_wrt_exp_rec n1 x1 e2) (close_exp_wrt_exp_rec n1 x1 e3)
    | trm_pair e2 e3 => trm_pair (close_exp_wrt_exp_rec n1 x1 e2) (close_exp_wrt_exp_rec n1 x1 e3)
    | trm_rcd l1 e2 => trm_rcd l1 (close_exp_wrt_exp_rec n1 x1 e2)
    | trm_proj e2 l1 => trm_proj (close_exp_wrt_exp_rec n1 x1 e2) l1
    | trm_capp c1 e2 => trm_capp c1 (close_exp_wrt_exp_rec n1 x1 e2)
  end.

Definition close_exp_wrt_exp x1 e1 := close_exp_wrt_exp_rec 0 x1 e1.

Fixpoint size_typ (T1 : typ) {struct T1} : nat :=
  match T1 with
    | a_nat => 1
    | a_unit => 1
    | a_arrow T2 T3 => 1 + (size_typ T2) + (size_typ T3)
    | a_prod T2 T3 => 1 + (size_typ T2) + (size_typ T3)
    | a_rcd l1 T2 => 1 + (size_typ T2)
  end.

Fixpoint size_co (c1 : co) {struct c1} : nat :=
  match c1 with
    | co_id => 1
    | co_trans c2 c3 => 1 + (size_co c2) + (size_co c3)
    | co_top => 1
    | co_arr c2 c3 => 1 + (size_co c2) + (size_co c3)
    | co_pair c2 c3 => 1 + (size_co c2) + (size_co c3)
    | co_proj1 => 1
    | co_proj2 => 1
    | co_distArr => 1
    | co_distRcd l1 => 1
    | co_rcd l1 c2 => 1 + (size_co c2)
    | co_topArr => 1
    | co_topRcd l1 => 1
  end.

Fixpoint size_exp (e1 : exp) {struct e1} : nat :=
  match e1 with
    | trm_var_f x1 => 1
    | trm_var_b n1 => 1
    | trm_unit => 1
    | trm_lit i1 => 1
    | trm_abs e2 => 1 + (size_exp e2)
    | trm_app e2 e3 => 1 + (size_exp e2) + (size_exp e3)
    | trm_pair e2 e3 => 1 + (size_exp e2) + (size_exp e3)
    | trm_rcd l1 e2 => 1 + (size_exp e2)
    | trm_proj e2 l1 => 1 + (size_exp e2)
    | trm_capp c1 e2 => 1 + (size_co c1) + (size_exp e2)
  end.

Inductive degree_exp_wrt_exp : nat -> exp -> Prop :=
  | degree_wrt_exp_trm_var_f : forall n1 x1,
    degree_exp_wrt_exp n1 (trm_var_f x1)
  | degree_wrt_exp_trm_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_exp_wrt_exp n1 (trm_var_b n2)
  | degree_wrt_exp_trm_unit : forall n1,
    degree_exp_wrt_exp n1 (trm_unit)
  | degree_wrt_exp_trm_lit : forall n1 i1,
    degree_exp_wrt_exp n1 (trm_lit i1)
  | degree_wrt_exp_trm_abs : forall n1 e1,
    degree_exp_wrt_exp (S n1) e1 ->
    degree_exp_wrt_exp n1 (trm_abs e1)
  | degree_wrt_exp_trm_app : forall n1 e1 e2,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 e2 ->
    degree_exp_wrt_exp n1 (trm_app e1 e2)
  | degree_wrt_exp_trm_pair : forall n1 e1 e2,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 e2 ->
    degree_exp_wrt_exp n1 (trm_pair e1 e2)
  | degree_wrt_exp_trm_rcd : forall n1 l1 e1,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 (trm_rcd l1 e1)
  | degree_wrt_exp_trm_proj : forall n1 e1 l1,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 (trm_proj e1 l1)
  | degree_wrt_exp_trm_capp : forall n1 c1 e1,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 (trm_capp c1 e1).

Scheme degree_exp_wrt_exp_ind' := Induction for degree_exp_wrt_exp Sort Prop.

Definition degree_exp_wrt_exp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 =>
  degree_exp_wrt_exp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.

Inductive lc_set_exp : exp -> Set :=
  | lc_set_trm_var_f : forall x1,
    lc_set_exp (trm_var_f x1)
  | lc_set_trm_unit :
    lc_set_exp (trm_unit)
  | lc_set_trm_lit : forall i1,
    lc_set_exp (trm_lit i1)
  | lc_set_trm_abs : forall e1,
    (forall x1 : var, lc_set_exp (open_exp_wrt_exp e1 (trm_var_f x1))) ->
    lc_set_exp (trm_abs e1)
  | lc_set_trm_app : forall e1 e2,
    lc_set_exp e1 ->
    lc_set_exp e2 ->
    lc_set_exp (trm_app e1 e2)
  | lc_set_trm_pair : forall e1 e2,
    lc_set_exp e1 ->
    lc_set_exp e2 ->
    lc_set_exp (trm_pair e1 e2)
  | lc_set_trm_rcd : forall l1 e1,
    lc_set_exp e1 ->
    lc_set_exp (trm_rcd l1 e1)
  | lc_set_trm_proj : forall e1 l1,
    lc_set_exp e1 ->
    lc_set_exp (trm_proj e1 l1)
  | lc_set_trm_capp : forall c1 e1,
    lc_set_exp e1 ->
    lc_set_exp (trm_capp c1 e1).

Scheme lc_exp_ind' := Induction for lc_exp Sort Prop.

Definition lc_exp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  lc_exp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.

Scheme lc_set_exp_ind' := Induction for lc_set_exp Sort Prop.

Definition lc_set_exp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  lc_set_exp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.

Scheme lc_set_exp_rec' := Induction for lc_set_exp Sort Set.

Definition lc_set_exp_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  lc_set_exp_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.

Definition body_exp_wrt_exp e1 := forall x1, lc_exp (open_exp_wrt_exp e1 (trm_var_f x1)).
