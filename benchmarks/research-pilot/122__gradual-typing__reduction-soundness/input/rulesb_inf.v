Require Import Coq.Arith.Wf_nat.

Require Import Coq.Program.Equality.

Require Export Metalib.Metatheory.

Require Export Metalib.LibLNgen.

Require Export syntaxb_ott.

Scheme typ_ind' := Induction for typ Sort Prop.

Definition typ_mutind :=
  fun H1 H2 H3 H4 H5 =>
  typ_ind' H1 H2 H3 H4 H5.

Scheme typ_rec' := Induction for typ Sort Set.

Definition typ_mutrec :=
  fun H1 H2 H3 H4 H5 =>
  typ_rec' H1 H2 H3 H4 H5.

Scheme term_ind' := Induction for term Sort Prop.

Definition term_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  term_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.

Scheme term_rec' := Induction for term Sort Set.

Definition term_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  term_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.

Fixpoint close_term_wrt_term_rec (n1 : nat) (x1 : var) (t1 : term) {struct t1} : term :=
  match t1 with
    | trm_var_f x2 => if (x1 == x2) then (trm_var_b n1) else (trm_var_f x2)
    | trm_var_b n2 => if (lt_ge_dec n2 n1) then (trm_var_b n2) else (trm_var_b (S n2))
    | trm_lit i1 => trm_lit i1
    | trm_abs A1 t2 => trm_abs A1 (close_term_wrt_term_rec (S n1) x1 t2)
    | trm_app t2 t3 => trm_app (close_term_wrt_term_rec n1 x1 t2) (close_term_wrt_term_rec n1 x1 t3)
    | trm_cast t2 A1 B1 => trm_cast (close_term_wrt_term_rec n1 x1 t2) A1 B1
    | trm_add => trm_add
    | trm_addl i1 => trm_addl i1
  end.

Definition close_term_wrt_term x1 t1 := close_term_wrt_term_rec 0 x1 t1.

Fixpoint size_typ (A1 : typ) {struct A1} : nat :=
  match A1 with
    | t_int => 1
    | t_arrow A2 B1 => 1 + (size_typ A2) + (size_typ B1)
    | t_dyn => 1
  end.

Fixpoint size_term (t1 : term) {struct t1} : nat :=
  match t1 with
    | trm_var_f x1 => 1
    | trm_var_b n1 => 1
    | trm_lit i1 => 1
    | trm_abs A1 t2 => 1 + (size_typ A1) + (size_term t2)
    | trm_app t2 t3 => 1 + (size_term t2) + (size_term t3)
    | trm_cast t2 A1 B1 => 1 + (size_term t2) + (size_typ A1) + (size_typ B1)
    | trm_add => 1
    | trm_addl i1 => 1
  end.

Inductive degree_term_wrt_term : nat -> term -> Prop :=
  | degree_wrt_term_trm_var_f : forall n1 x1,
    degree_term_wrt_term n1 (trm_var_f x1)
  | degree_wrt_term_trm_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_term_wrt_term n1 (trm_var_b n2)
  | degree_wrt_term_trm_lit : forall n1 i1,
    degree_term_wrt_term n1 (trm_lit i1)
  | degree_wrt_term_trm_abs : forall n1 A1 t1,
    degree_term_wrt_term (S n1) t1 ->
    degree_term_wrt_term n1 (trm_abs A1 t1)
  | degree_wrt_term_trm_app : forall n1 t1 t2,
    degree_term_wrt_term n1 t1 ->
    degree_term_wrt_term n1 t2 ->
    degree_term_wrt_term n1 (trm_app t1 t2)
  | degree_wrt_term_trm_cast : forall n1 t1 A1 B1,
    degree_term_wrt_term n1 t1 ->
    degree_term_wrt_term n1 (trm_cast t1 A1 B1)
  | degree_wrt_term_trm_add : forall n1,
    degree_term_wrt_term n1 (trm_add)
  | degree_wrt_term_trm_addl : forall n1 i1,
    degree_term_wrt_term n1 (trm_addl i1).

Scheme degree_term_wrt_term_ind' := Induction for degree_term_wrt_term Sort Prop.

Definition degree_term_wrt_term_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  degree_term_wrt_term_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.

Inductive lc_set_term : term -> Set :=
  | lc_set_trm_var_f : forall x1,
    lc_set_term (trm_var_f x1)
  | lc_set_trm_lit : forall i1,
    lc_set_term (trm_lit i1)
  | lc_set_trm_abs : forall A1 t1,
    (forall x1 : var, lc_set_term (open_term_wrt_term t1 (trm_var_f x1))) ->
    lc_set_term (trm_abs A1 t1)
  | lc_set_trm_app : forall t1 t2,
    lc_set_term t1 ->
    lc_set_term t2 ->
    lc_set_term (trm_app t1 t2)
  | lc_set_trm_cast : forall t1 A1 B1,
    lc_set_term t1 ->
    lc_set_term (trm_cast t1 A1 B1)
  | lc_set_trm_add :
    lc_set_term (trm_add)
  | lc_set_trm_addl : forall i1,
    lc_set_term (trm_addl i1).

Scheme lc_term_ind' := Induction for lc_term Sort Prop.

Definition lc_term_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 =>
  lc_term_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9.

Scheme lc_set_term_ind' := Induction for lc_set_term Sort Prop.

Definition lc_set_term_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 =>
  lc_set_term_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9.

Scheme lc_set_term_rec' := Induction for lc_set_term Sort Set.

Definition lc_set_term_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 =>
  lc_set_term_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9.

Definition body_term_wrt_term t1 := forall x1, lc_term (open_term_wrt_term t1 (trm_var_f x1)).
