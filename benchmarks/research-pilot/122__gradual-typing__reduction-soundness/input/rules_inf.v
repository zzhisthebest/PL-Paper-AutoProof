Require Import Coq.Arith.Wf_nat.

Require Import Coq.Program.Equality.

Require Export Metalib.Metatheory.

Require Export Metalib.LibLNgen.

Require Export syntax_ott.

Require Export syntaxb_ott.

Scheme typ_ind' := Induction for typ Sort Prop.

Definition typ_mutind :=
  fun H1 H2 H3 H4 H5 =>
  typ_ind' H1 H2 H3 H4 H5.

Scheme typ_rec' := Induction for typ Sort Set.

Definition typ_mutrec :=
  fun H1 H2 H3 H4 H5 =>
  typ_rec' H1 H2 H3 H4 H5.

Scheme exp_ind' := Induction for exp Sort Prop.

Definition exp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  exp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.

Scheme exp_rec' := Induction for exp Sort Set.

Definition exp_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  exp_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.

Fixpoint close_exp_wrt_exp_rec (n1 : nat) (x1 : var) (e1 : exp) {struct e1} : exp :=
  match e1 with
    | e_var_f x2 => if (x1 == x2) then (e_var_b n1) else (e_var_f x2)
    | e_var_b n2 => if (lt_ge_dec n2 n1) then (e_var_b n2) else (e_var_b (S n2))
    | e_lit i1 => e_lit i1
    | e_abs A1 e2 B1 => e_abs A1 (close_exp_wrt_exp_rec (S n1) x1 e2) B1
    | e_app e2 e3 => e_app (close_exp_wrt_exp_rec n1 x1 e2) (close_exp_wrt_exp_rec n1 x1 e3)
    | e_anno e2 A1 => e_anno (close_exp_wrt_exp_rec n1 x1 e2) A1
    | e_add => e_add
    | e_addl i1 => e_addl i1
  end.

Definition close_exp_wrt_exp x1 e1 := close_exp_wrt_exp_rec 0 x1 e1.

Fixpoint size_typ (A1 : typ) {struct A1} : nat :=
  match A1 with
    | t_int => 1
    | t_arrow A2 B1 => 1 + (size_typ A2) + (size_typ B1)
    | t_dyn => 1
  end.

Fixpoint size_exp (e1 : exp) {struct e1} : nat :=
  match e1 with
    | e_var_f x1 => 1
    | e_var_b n1 => 1
    | e_lit i1 => 1
    | e_abs A1 e2 B1 => 1 + (size_typ A1) + (size_exp e2) + (size_typ B1)
    | e_app e2 e3 => 1 + (size_exp e2) + (size_exp e3)
    | e_anno e2 A1 => 1 + (size_exp e2) + (size_typ A1)
    | e_add => 1
    | e_addl i1 => 1
  end.

Inductive degree_exp_wrt_exp : nat -> exp -> Prop :=
  | degree_wrt_exp_e_var_f : forall n1 x1,
    degree_exp_wrt_exp n1 (e_var_f x1)
  | degree_wrt_exp_e_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_exp_wrt_exp n1 (e_var_b n2)
  | degree_wrt_exp_e_lit : forall n1 i1,
    degree_exp_wrt_exp n1 (e_lit i1)
  | degree_wrt_exp_e_abs : forall n1 A1 e1 B1,
    degree_exp_wrt_exp (S n1) e1 ->
    degree_exp_wrt_exp n1 (e_abs A1 e1 B1)
  | degree_wrt_exp_e_app : forall n1 e1 e2,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 e2 ->
    degree_exp_wrt_exp n1 (e_app e1 e2)
  | degree_wrt_exp_e_anno : forall n1 e1 A1,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 (e_anno e1 A1)
  | degree_wrt_exp_e_add : forall n1,
    degree_exp_wrt_exp n1 (e_add)
  | degree_wrt_exp_e_addl : forall n1 i1,
    degree_exp_wrt_exp n1 (e_addl i1).

Scheme degree_exp_wrt_exp_ind' := Induction for degree_exp_wrt_exp Sort Prop.

Definition degree_exp_wrt_exp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  degree_exp_wrt_exp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.

Inductive lc_set_exp : exp -> Set :=
  | lc_set_e_var_f : forall x1,
    lc_set_exp (e_var_f x1)
  | lc_set_e_lit : forall i1,
    lc_set_exp (e_lit i1)
  | lc_set_e_abs : forall A1 e1 B1,
    (forall x1 : var, lc_set_exp (open_exp_wrt_exp e1 (e_var_f x1))) ->
    lc_set_exp (e_abs A1 e1 B1)
  | lc_set_e_app : forall e1 e2,
    lc_set_exp e1 ->
    lc_set_exp e2 ->
    lc_set_exp (e_app e1 e2)
  | lc_set_e_anno : forall e1 A1,
    lc_set_exp e1 ->
    lc_set_exp (e_anno e1 A1)
  | lc_set_e_add :
    lc_set_exp (e_add)
  | lc_set_e_addl : forall i1,
    lc_set_exp (e_addl i1).

Scheme lc_exp_ind' := Induction for lc_exp Sort Prop.

Definition lc_exp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 =>
  lc_exp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9.

Scheme lc_set_exp_ind' := Induction for lc_set_exp Sort Prop.

Definition lc_set_exp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 =>
  lc_set_exp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9.

Scheme lc_set_exp_rec' := Induction for lc_set_exp Sort Set.

Definition lc_set_exp_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 =>
  lc_set_exp_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9.

Definition body_exp_wrt_exp e1 := forall x1, lc_exp (open_exp_wrt_exp e1 (e_var_f x1)).
