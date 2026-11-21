Require Import Coq.Program.Equality.

Require Export Metalib.Metatheory.

Require Export Metalib.LibLNgen.

Require Export Syntax_ott.

Scheme ty_ind' := Induction for ty Sort Prop.

Definition ty_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 =>
  ty_ind' H1 H2 H3 H4 H5 H6 H7 H8.

Scheme ty_rec' := Induction for ty Sort Set.

Definition ty_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 =>
  ty_rec' H1 H2 H3 H4 H5 H6 H7 H8.

Scheme co_ind' := Induction for co Sort Prop.

Definition co_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 =>
  co_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14.

Scheme co_rec' := Induction for co Sort Set.

Definition co_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 =>
  co_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14.

Scheme exp_ind' := Induction for exp Sort Prop.

Definition exp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 =>
  exp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.

Scheme exp_rec' := Induction for exp Sort Set.

Definition exp_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 =>
  exp_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.

Fixpoint close_ty_wrt_ty_rec (n1 : nat) (X1 : typvar) (T1 : ty) {struct T1} : ty :=
  match T1 with
    | ty_nat => ty_nat
    | ty_unit => ty_unit
    | ty_var_f X2 => if (X1 == X2) then (ty_var_b n1) else (ty_var_f X2)
    | ty_var_b n2 => if (lt_ge_dec n2 n1) then (ty_var_b n2) else (ty_var_b (S n2))
    | ty_arrow T2 T3 => ty_arrow (close_ty_wrt_ty_rec n1 X1 T2) (close_ty_wrt_ty_rec n1 X1 T3)
    | ty_prod T2 T3 => ty_prod (close_ty_wrt_ty_rec n1 X1 T2) (close_ty_wrt_ty_rec n1 X1 T3)
    | ty_all T2 => ty_all (close_ty_wrt_ty_rec (S n1) X1 T2)
  end.

Definition close_ty_wrt_ty X1 T1 := close_ty_wrt_ty_rec 0 X1 T1.

Fixpoint close_exp_wrt_ty_rec (n1 : nat) (X1 : typvar) (e1 : exp) {struct e1} : exp :=
  match e1 with
    | exp_var_f x1 => exp_var_f x1
    | exp_var_b n2 => exp_var_b n2
    | exp_unit => exp_unit
    | exp_lit i1 => exp_lit i1
    | exp_abs e2 => exp_abs (close_exp_wrt_ty_rec n1 X1 e2)
    | exp_app e2 e3 => exp_app (close_exp_wrt_ty_rec n1 X1 e2) (close_exp_wrt_ty_rec n1 X1 e3)
    | exp_pair e2 e3 => exp_pair (close_exp_wrt_ty_rec n1 X1 e2) (close_exp_wrt_ty_rec n1 X1 e3)
    | exp_capp c1 e2 => exp_capp c1 (close_exp_wrt_ty_rec n1 X1 e2)
    | exp_tabs e2 => exp_tabs (close_exp_wrt_ty_rec (S n1) X1 e2)
    | exp_tapp e2 T1 => exp_tapp (close_exp_wrt_ty_rec n1 X1 e2) (close_ty_wrt_ty_rec n1 X1 T1)
  end.

Fixpoint close_exp_wrt_exp_rec (n1 : nat) (x1 : expvar) (e1 : exp) {struct e1} : exp :=
  match e1 with
    | exp_var_f x2 => if (x1 == x2) then (exp_var_b n1) else (exp_var_f x2)
    | exp_var_b n2 => if (lt_ge_dec n2 n1) then (exp_var_b n2) else (exp_var_b (S n2))
    | exp_unit => exp_unit
    | exp_lit i1 => exp_lit i1
    | exp_abs e2 => exp_abs (close_exp_wrt_exp_rec (S n1) x1 e2)
    | exp_app e2 e3 => exp_app (close_exp_wrt_exp_rec n1 x1 e2) (close_exp_wrt_exp_rec n1 x1 e3)
    | exp_pair e2 e3 => exp_pair (close_exp_wrt_exp_rec n1 x1 e2) (close_exp_wrt_exp_rec n1 x1 e3)
    | exp_capp c1 e2 => exp_capp c1 (close_exp_wrt_exp_rec n1 x1 e2)
    | exp_tabs e2 => exp_tabs (close_exp_wrt_exp_rec n1 x1 e2)
    | exp_tapp e2 T1 => exp_tapp (close_exp_wrt_exp_rec n1 x1 e2) T1
  end.

Definition close_exp_wrt_ty X1 e1 := close_exp_wrt_ty_rec 0 X1 e1.

Definition close_exp_wrt_exp x1 e1 := close_exp_wrt_exp_rec 0 x1 e1.

Fixpoint size_ty (T1 : ty) {struct T1} : nat :=
  match T1 with
    | ty_nat => 1
    | ty_unit => 1
    | ty_var_f X1 => 1
    | ty_var_b n1 => 1
    | ty_arrow T2 T3 => 1 + (size_ty T2) + (size_ty T3)
    | ty_prod T2 T3 => 1 + (size_ty T2) + (size_ty T3)
    | ty_all T2 => 1 + (size_ty T2)
  end.

Fixpoint size_co (c1 : co) {struct c1} : nat :=
  match c1 with
    | co_id => 1
    | co_trans c2 c3 => 1 + (size_co c2) + (size_co c3)
    | co_top => 1
    | co_bot => 1
    | co_arr c2 c3 => 1 + (size_co c2) + (size_co c3)
    | co_pair c2 c3 => 1 + (size_co c2) + (size_co c3)
    | co_proj1 => 1
    | co_proj2 => 1
    | co_forall c2 => 1 + (size_co c2)
    | co_distArr => 1
    | co_topArr => 1
    | co_topAll => 1
    | co_distPoly => 1
  end.

Fixpoint size_exp (e1 : exp) {struct e1} : nat :=
  match e1 with
    | exp_var_f x1 => 1
    | exp_var_b n1 => 1
    | exp_unit => 1
    | exp_lit i1 => 1
    | exp_abs e2 => 1 + (size_exp e2)
    | exp_app e2 e3 => 1 + (size_exp e2) + (size_exp e3)
    | exp_pair e2 e3 => 1 + (size_exp e2) + (size_exp e3)
    | exp_capp c1 e2 => 1 + (size_co c1) + (size_exp e2)
    | exp_tabs e2 => 1 + (size_exp e2)
    | exp_tapp e2 T1 => 1 + (size_exp e2) + (size_ty T1)
  end.

Inductive degree_ty_wrt_ty : nat -> ty -> Prop :=
  | degree_wrt_ty_ty_nat : forall n1,
    degree_ty_wrt_ty n1 (ty_nat)
  | degree_wrt_ty_ty_unit : forall n1,
    degree_ty_wrt_ty n1 (ty_unit)
  | degree_wrt_ty_ty_var_f : forall n1 X1,
    degree_ty_wrt_ty n1 (ty_var_f X1)
  | degree_wrt_ty_ty_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_ty_wrt_ty n1 (ty_var_b n2)
  | degree_wrt_ty_ty_arrow : forall n1 T1 T2,
    degree_ty_wrt_ty n1 T1 ->
    degree_ty_wrt_ty n1 T2 ->
    degree_ty_wrt_ty n1 (ty_arrow T1 T2)
  | degree_wrt_ty_ty_prod : forall n1 T1 T2,
    degree_ty_wrt_ty n1 T1 ->
    degree_ty_wrt_ty n1 T2 ->
    degree_ty_wrt_ty n1 (ty_prod T1 T2)
  | degree_wrt_ty_ty_all : forall n1 T1,
    degree_ty_wrt_ty (S n1) T1 ->
    degree_ty_wrt_ty n1 (ty_all T1).

Scheme degree_ty_wrt_ty_ind' := Induction for degree_ty_wrt_ty Sort Prop.

Definition degree_ty_wrt_ty_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 =>
  degree_ty_wrt_ty_ind' H1 H2 H3 H4 H5 H6 H7 H8.

Inductive degree_exp_wrt_ty : nat -> exp -> Prop :=
  | degree_wrt_ty_exp_var_f : forall n1 x1,
    degree_exp_wrt_ty n1 (exp_var_f x1)
  | degree_wrt_ty_exp_var_b : forall n1 n2,
    degree_exp_wrt_ty n1 (exp_var_b n2)
  | degree_wrt_ty_exp_unit : forall n1,
    degree_exp_wrt_ty n1 (exp_unit)
  | degree_wrt_ty_exp_lit : forall n1 i1,
    degree_exp_wrt_ty n1 (exp_lit i1)
  | degree_wrt_ty_exp_abs : forall n1 e1,
    degree_exp_wrt_ty n1 e1 ->
    degree_exp_wrt_ty n1 (exp_abs e1)
  | degree_wrt_ty_exp_app : forall n1 e1 e2,
    degree_exp_wrt_ty n1 e1 ->
    degree_exp_wrt_ty n1 e2 ->
    degree_exp_wrt_ty n1 (exp_app e1 e2)
  | degree_wrt_ty_exp_pair : forall n1 e1 e2,
    degree_exp_wrt_ty n1 e1 ->
    degree_exp_wrt_ty n1 e2 ->
    degree_exp_wrt_ty n1 (exp_pair e1 e2)
  | degree_wrt_ty_exp_capp : forall n1 c1 e1,
    degree_exp_wrt_ty n1 e1 ->
    degree_exp_wrt_ty n1 (exp_capp c1 e1)
  | degree_wrt_ty_exp_tabs : forall n1 e1,
    degree_exp_wrt_ty (S n1) e1 ->
    degree_exp_wrt_ty n1 (exp_tabs e1)
  | degree_wrt_ty_exp_tapp : forall n1 e1 T1,
    degree_exp_wrt_ty n1 e1 ->
    degree_ty_wrt_ty n1 T1 ->
    degree_exp_wrt_ty n1 (exp_tapp e1 T1).

Inductive degree_exp_wrt_exp : nat -> exp -> Prop :=
  | degree_wrt_exp_exp_var_f : forall n1 x1,
    degree_exp_wrt_exp n1 (exp_var_f x1)
  | degree_wrt_exp_exp_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_exp_wrt_exp n1 (exp_var_b n2)
  | degree_wrt_exp_exp_unit : forall n1,
    degree_exp_wrt_exp n1 (exp_unit)
  | degree_wrt_exp_exp_lit : forall n1 i1,
    degree_exp_wrt_exp n1 (exp_lit i1)
  | degree_wrt_exp_exp_abs : forall n1 e1,
    degree_exp_wrt_exp (S n1) e1 ->
    degree_exp_wrt_exp n1 (exp_abs e1)
  | degree_wrt_exp_exp_app : forall n1 e1 e2,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 e2 ->
    degree_exp_wrt_exp n1 (exp_app e1 e2)
  | degree_wrt_exp_exp_pair : forall n1 e1 e2,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 e2 ->
    degree_exp_wrt_exp n1 (exp_pair e1 e2)
  | degree_wrt_exp_exp_capp : forall n1 c1 e1,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 (exp_capp c1 e1)
  | degree_wrt_exp_exp_tabs : forall n1 e1,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 (exp_tabs e1)
  | degree_wrt_exp_exp_tapp : forall n1 e1 T1,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 (exp_tapp e1 T1).

Scheme degree_exp_wrt_ty_ind' := Induction for degree_exp_wrt_ty Sort Prop.

Definition degree_exp_wrt_ty_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 =>
  degree_exp_wrt_ty_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.

Scheme degree_exp_wrt_exp_ind' := Induction for degree_exp_wrt_exp Sort Prop.

Definition degree_exp_wrt_exp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 =>
  degree_exp_wrt_exp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.

Inductive lc_set_ty : ty -> Set :=
  | lc_set_ty_nat :
    lc_set_ty (ty_nat)
  | lc_set_ty_unit :
    lc_set_ty (ty_unit)
  | lc_set_ty_var_f : forall X1,
    lc_set_ty (ty_var_f X1)
  | lc_set_ty_arrow : forall T1 T2,
    lc_set_ty T1 ->
    lc_set_ty T2 ->
    lc_set_ty (ty_arrow T1 T2)
  | lc_set_ty_prod : forall T1 T2,
    lc_set_ty T1 ->
    lc_set_ty T2 ->
    lc_set_ty (ty_prod T1 T2)
  | lc_set_ty_all : forall T1,
    (forall X1 : typvar, lc_set_ty (open_ty_wrt_ty T1 (ty_var_f X1))) ->
    lc_set_ty (ty_all T1).

Scheme lc_ty_ind' := Induction for lc_ty Sort Prop.

Definition lc_ty_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 =>
  lc_ty_ind' H1 H2 H3 H4 H5 H6 H7.

Scheme lc_set_ty_ind' := Induction for lc_set_ty Sort Prop.

Definition lc_set_ty_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 =>
  lc_set_ty_ind' H1 H2 H3 H4 H5 H6 H7.

Scheme lc_set_ty_rec' := Induction for lc_set_ty Sort Set.

Definition lc_set_ty_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 =>
  lc_set_ty_rec' H1 H2 H3 H4 H5 H6 H7.

Inductive lc_set_exp : exp -> Set :=
  | lc_set_exp_var_f : forall x1,
    lc_set_exp (exp_var_f x1)
  | lc_set_exp_unit :
    lc_set_exp (exp_unit)
  | lc_set_exp_lit : forall i1,
    lc_set_exp (exp_lit i1)
  | lc_set_exp_abs : forall e1,
    (forall x1 : expvar, lc_set_exp (open_exp_wrt_exp e1 (exp_var_f x1))) ->
    lc_set_exp (exp_abs e1)
  | lc_set_exp_app : forall e1 e2,
    lc_set_exp e1 ->
    lc_set_exp e2 ->
    lc_set_exp (exp_app e1 e2)
  | lc_set_exp_pair : forall e1 e2,
    lc_set_exp e1 ->
    lc_set_exp e2 ->
    lc_set_exp (exp_pair e1 e2)
  | lc_set_exp_capp : forall c1 e1,
    lc_set_exp e1 ->
    lc_set_exp (exp_capp c1 e1)
  | lc_set_exp_tabs : forall e1,
    (forall X1 : typvar, lc_set_exp (open_exp_wrt_ty e1 (ty_var_f X1))) ->
    lc_set_exp (exp_tabs e1)
  | lc_set_exp_tapp : forall e1 T1,
    lc_set_exp e1 ->
    lc_set_ty T1 ->
    lc_set_exp (exp_tapp e1 T1).

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

Definition body_ty_wrt_ty T1 := forall X1, lc_ty (open_ty_wrt_ty T1 (ty_var_f X1)).

Definition body_exp_wrt_ty e1 := forall X1, lc_exp (open_exp_wrt_ty e1 (ty_var_f X1)).

Definition body_exp_wrt_exp e1 := forall x1, lc_exp (open_exp_wrt_exp e1 (exp_var_f x1)).
