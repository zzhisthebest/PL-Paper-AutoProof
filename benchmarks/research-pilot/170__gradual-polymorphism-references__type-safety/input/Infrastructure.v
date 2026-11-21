Require Export Metalib.Metatheory.

Require Import Definitions.

Require Export Metalib.LibLNgen.

Require Import String.

Fixpoint fv_tt (T : typ) {struct T} : atoms :=
  match T with
  | t_int       => {}
  | t_dyn     => {}
  | t_unit     => {}
  | t_bvar J      => {}
  | t_fvar X      => {{ X }}
  | t_arrow T1 T2 => (fv_tt T1) `union` (fv_tt T2)
  | t_all T1      => (fv_tt T1)
  | t_ref T1      => (fv_tt T1)
  end.

Fixpoint fv_te (e : exp) {struct e} : atoms :=
match e with
| e_bvar i       => {}
| e_fvar x       => {}
| e_lit i        => {}
| e_unit        => {}
| e_loc l        => {}
| e_abs A e1 B   => (fv_tt A) `union` (fv_te e1) `union` (fv_tt B)
| e_app e1 e2    => (fv_te e1) `union` (fv_te e2)
| e_anno e A     => (fv_te e) `union` (fv_tt A)
| e_tabs e A     => (fv_te e) `union` (fv_tt A)
| e_tapp e A     => (fv_te e) `union` (fv_tt A)
| e_ref e     => (fv_te e)
| e_get e     => (fv_te e)
| e_set e1 e2    => (fv_te e1) `union` (fv_te e2)
end.

Fixpoint fv_ee (e : exp) {struct e} : atoms :=
match e with
| e_bvar i       => {}
| e_fvar x       => {{ x }}
| e_lit i        => {}
| e_unit        => {}
| e_loc l        => {}
| e_abs A e1 B   => (fv_ee e1)
| e_app e1 e2    => (fv_ee e1) `union` (fv_ee e2)
| e_anno e A     => (fv_ee e)
| e_tabs e A     => (fv_ee e)
| e_tapp e A     => (fv_ee e)
| e_ref e     => (fv_ee e)
| e_get e     => (fv_ee e)
| e_set e1 e2    => (fv_ee e1) `union` (fv_ee e2)
end.

Fixpoint subst_tt (Z : var) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | t_int         => t_int
  | t_dyn         => t_dyn
  | t_unit         => t_unit
  | t_bvar J      => t_bvar J
  | t_fvar X      => if X == Z then U else (t_fvar X)
  | t_arrow T1 T2 => t_arrow (subst_tt Z U T1) (subst_tt Z U T2)
  | t_all T1      => t_all (subst_tt Z U T1)
  | t_ref T1      => t_ref (subst_tt Z U T1)
  end.

Fixpoint subst_te (z : var) (u : typ) (e : exp) {struct e} : exp :=
  match e with
  | e_bvar i       => e_bvar i
  | e_fvar x       => e_fvar x
  | e_lit i        => e_lit i
  | e_unit         => e_unit
  | e_loc l        => e_loc l
  | e_abs A e1 B   => e_abs (subst_tt z u A) (subst_te z u e1) (subst_tt z u B)
  | e_app e1 e2    => e_app (subst_te z u e1) (subst_te z u e2)
  | e_anno e A     => e_anno (subst_te z u e) (subst_tt z u A)
  | e_tabs e A     => e_tabs (subst_te z u e) (subst_tt z u A)
  | e_tapp e A     => e_tapp (subst_te z u e) (subst_tt z u A)
  | e_ref t1    => e_ref (subst_te z u t1)
  | e_get t1    => e_get (subst_te z u t1)
  | e_set t1 t2 => e_set (subst_te z u t1) (subst_te z u t2)
  end.

Fixpoint subst_ee (z : var) (u : exp) (e : exp) {struct e} : exp :=
  match e with
  | e_bvar i       => e_bvar i
  | e_fvar x       => if x == z then u else (e_fvar x)
  | e_lit i        => e_lit i
  | e_unit         => e_unit
  | e_loc l        => e_loc l
  | e_abs A e1 B   => e_abs A (subst_ee z u e1) B
  | e_app e1 e2    => e_app (subst_ee z u e1) (subst_ee z u e2)
  | e_anno e A     => e_anno (subst_ee z u e) A
  | e_tabs e A     => e_tabs (subst_ee z u e) A
  | e_tapp e A     => e_tapp (subst_ee z u e) A
  | e_ref t1    => e_ref (subst_ee z u t1)
  | e_get t1    => e_get (subst_ee z u t1)
  | e_set t1 t2 => e_set (subst_ee z u t1) (subst_ee z u t2)
  end.

Definition subst_tb (Z : var) (P : typ) (b : binding) : binding :=
  match b with
  | bind_tvar => bind_tvar
  | bind_typ T => bind_typ (subst_tt Z P T)
  end.

Fixpoint size_typ (A1 : typ) {struct A1} : nat :=
match A1 with
  | t_fvar X1 => 1
  | t_bvar n1 => 1
  | t_int => 1
  | t_dyn => 1
  | t_unit => 1
  | t_all A => 1 + (size_typ A)
  | t_arrow A2 B1 => 1 + (size_typ A2) + (size_typ B1)
  | t_ref A => 1 + (size_typ A)
end.

Fixpoint size_exp (e1 : exp) {struct e1} : nat :=
match e1 with
  | e_fvar x1 => 1
  | e_bvar n1 => 1
  | e_lit i1 => 1
  | e_unit => 1
  | e_abs A1 e2 B1 => 1 + (size_typ A1) + (size_exp e2) + (size_typ B1)
  | e_app e2 e3 => 1 + (size_exp e2) + (size_exp e3)
  | e_anno e2 A1 => 1 + (size_exp e2) + (size_typ A1)
  | e_tabs e2 B1 => 1 + (size_exp e2) + (size_typ B1)
  | e_tapp e2 A1 => 1 + (size_exp e2) + (size_typ A1)
  | e_loc l => 1
  | e_ref e => 1 + (size_exp e)
  | e_get e => 1 + (size_exp e)
  | e_set e2 e3 => 1 + (size_exp e2) + (size_exp e3)
end.

Fixpoint fv_tt_env (E : env) {struct E} : atoms :=
  match E with
  | nil                      => {}
  | cons (x, bind_typ t) E' => fv_tt t `union` fv_tt_env E'
  | cons (x, bind_tvar) E'  => fv_tt_env E'
  end.

Scheme typ_ind' := Induction for typ Sort Prop.

Definition typ_mutind :=
fun H1 H2 H3 H4 H5 H6 H7 =>
typ_ind' H1 H2 H3 H4 H5 H6 H7.

Scheme exp_ind' := Induction for exp Sort Prop.

Definition exp_mutind :=
fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 =>
exp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12.

Definition irred e mu mu': Prop := forall b, ~(step (e, mu) (b, mu')).

Notation "[ z ~> u ] e" := (subst_ee z u e) (at level 0).

Notation "t ^^ u"       := (open_ee t u) (at level 67).

Notation "e ^ x"        := (open_ee e (e_fvar x)).

Notation "v |-> A v'" := (TypedReduce v A v') (at level 68).

Notation "e ~-> r" := (step e r) (at level 68).
