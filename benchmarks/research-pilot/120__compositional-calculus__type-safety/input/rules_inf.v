Require Import Coq.Arith.Wf_nat.

Require Import Coq.Program.Equality.

Require Export Metalib.Metatheory.

Require Export Metalib.LibLNgen.

Require Export syntax_ott.

Scheme typ_ind' := Induction for typ Sort Prop.

Definition typ_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  typ_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.

Scheme typ_rec' := Induction for typ Sort Set.

Definition typ_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  typ_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.

Scheme exp_ind' := Induction for exp Sort Prop.

Definition exp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 =>
  exp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14.

Scheme exp_rec' := Induction for exp Sort Set.

Definition exp_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 =>
  exp_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14.

Fixpoint close_typ_wrt_typ_rec (n1 : nat) (X1 : typevar) (A1 : typ) {struct A1} : typ :=
  match A1 with
    | t_tvar_f X2 => if (X1 == X2) then (t_tvar_b n1) else (t_tvar_f X2)
    | t_tvar_b n2 => if (lt_ge_dec n2 n1) then (t_tvar_b n2) else (t_tvar_b (S n2))
    | t_int => t_int
    | t_top => t_top
    | t_bot => t_bot
    | t_forall A2 B1 => t_forall (close_typ_wrt_typ_rec n1 X1 A2) (close_typ_wrt_typ_rec (S n1) X1 B1)
    | t_arrow A2 B1 => t_arrow (close_typ_wrt_typ_rec n1 X1 A2) (close_typ_wrt_typ_rec n1 X1 B1)
    | t_and A2 B1 => t_and (close_typ_wrt_typ_rec n1 X1 A2) (close_typ_wrt_typ_rec n1 X1 B1)
    | t_rcd l1 A2 => t_rcd l1 (close_typ_wrt_typ_rec n1 X1 A2)
  end.

Definition close_typ_wrt_typ X1 A1 := close_typ_wrt_typ_rec 0 X1 A1.

Fixpoint close_exp_wrt_typ_rec (n1 : nat) (X1 : typevar) (e1 : exp) {struct e1} : exp :=
  match e1 with
    | e_var_f x1 => e_var_f x1
    | e_var_b n2 => e_var_b n2
    | e_top => e_top
    | e_lit i1 => e_lit i1
    | e_abs A1 e2 => e_abs (close_typ_wrt_typ_rec n1 X1 A1) (close_exp_wrt_typ_rec n1 X1 e2)
    | e_fixpoint A1 e2 => e_fixpoint (close_typ_wrt_typ_rec n1 X1 A1) (close_exp_wrt_typ_rec n1 X1 e2)
    | e_app e2 e3 => e_app (close_exp_wrt_typ_rec n1 X1 e2) (close_exp_wrt_typ_rec n1 X1 e3)
    | e_merge e2 e3 => e_merge (close_exp_wrt_typ_rec n1 X1 e2) (close_exp_wrt_typ_rec n1 X1 e3)
    | e_anno e2 A1 => e_anno (close_exp_wrt_typ_rec n1 X1 e2) (close_typ_wrt_typ_rec n1 X1 A1)
    | e_rcd l1 e2 => e_rcd l1 (close_exp_wrt_typ_rec n1 X1 e2)
    | e_proj e2 l1 => e_proj (close_exp_wrt_typ_rec n1 X1 e2) l1
    | e_tabs e2 => e_tabs (close_exp_wrt_typ_rec (S n1) X1 e2)
    | e_tapp e2 A1 => e_tapp (close_exp_wrt_typ_rec n1 X1 e2) (close_typ_wrt_typ_rec n1 X1 A1)
  end.

Fixpoint close_exp_wrt_exp_rec (n1 : nat) (x1 : termvar) (e1 : exp) {struct e1} : exp :=
  match e1 with
    | e_var_f x2 => if (x1 == x2) then (e_var_b n1) else (e_var_f x2)
    | e_var_b n2 => if (lt_ge_dec n2 n1) then (e_var_b n2) else (e_var_b (S n2))
    | e_top => e_top
    | e_lit i1 => e_lit i1
    | e_abs A1 e2 => e_abs A1 (close_exp_wrt_exp_rec (S n1) x1 e2)
    | e_fixpoint A1 e2 => e_fixpoint A1 (close_exp_wrt_exp_rec (S n1) x1 e2)
    | e_app e2 e3 => e_app (close_exp_wrt_exp_rec n1 x1 e2) (close_exp_wrt_exp_rec n1 x1 e3)
    | e_merge e2 e3 => e_merge (close_exp_wrt_exp_rec n1 x1 e2) (close_exp_wrt_exp_rec n1 x1 e3)
    | e_anno e2 A1 => e_anno (close_exp_wrt_exp_rec n1 x1 e2) A1
    | e_rcd l1 e2 => e_rcd l1 (close_exp_wrt_exp_rec n1 x1 e2)
    | e_proj e2 l1 => e_proj (close_exp_wrt_exp_rec n1 x1 e2) l1
    | e_tabs e2 => e_tabs (close_exp_wrt_exp_rec n1 x1 e2)
    | e_tapp e2 A1 => e_tapp (close_exp_wrt_exp_rec n1 x1 e2) A1
  end.

Definition close_exp_wrt_typ X1 e1 := close_exp_wrt_typ_rec 0 X1 e1.

Definition close_exp_wrt_exp x1 e1 := close_exp_wrt_exp_rec 0 x1 e1.

Fixpoint size_typ (A1 : typ) {struct A1} : nat :=
  match A1 with
    | t_tvar_f X1 => 1
    | t_tvar_b n1 => 1
    | t_int => 1
    | t_top => 1
    | t_bot => 1
    | t_forall A2 B1 => 1 + (size_typ A2) + (size_typ B1)
    | t_arrow A2 B1 => 1 + (size_typ A2) + (size_typ B1)
    | t_and A2 B1 => 1 + (size_typ A2) + (size_typ B1)
    | t_rcd l1 A2 => 1 + (size_typ A2)
  end.

Fixpoint size_exp (e1 : exp) {struct e1} : nat :=
  match e1 with
    | e_var_f x1 => 1
    | e_var_b n1 => 1
    | e_top => 1
    | e_lit i1 => 1
    | e_abs A1 e2 => 1 + (size_typ A1) + (size_exp e2)
    | e_fixpoint A1 e2 => 1 + (size_typ A1) + (size_exp e2)
    | e_app e2 e3 => 1 + (size_exp e2) + (size_exp e3)
    | e_merge e2 e3 => 1 + (size_exp e2) + (size_exp e3)
    | e_anno e2 A1 => 1 + (size_exp e2) + (size_typ A1)
    | e_rcd l1 e2 => 1 + (size_exp e2)
    | e_proj e2 l1 => 1 + (size_exp e2)
    | e_tabs e2 => 1 + (size_exp e2)
    | e_tapp e2 A1 => 1 + (size_exp e2) + (size_typ A1)
  end.

Inductive degree_typ_wrt_typ : nat -> typ -> Prop :=
  | degree_wrt_typ_t_tvar_f : forall n1 X1,
    degree_typ_wrt_typ n1 (t_tvar_f X1)
  | degree_wrt_typ_t_tvar_b : forall n1 n2,
    lt n2 n1 ->
    degree_typ_wrt_typ n1 (t_tvar_b n2)
  | degree_wrt_typ_t_int : forall n1,
    degree_typ_wrt_typ n1 (t_int)
  | degree_wrt_typ_t_top : forall n1,
    degree_typ_wrt_typ n1 (t_top)
  | degree_wrt_typ_t_bot : forall n1,
    degree_typ_wrt_typ n1 (t_bot)
  | degree_wrt_typ_t_forall : forall n1 A1 B1,
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ (S n1) B1 ->
    degree_typ_wrt_typ n1 (t_forall A1 B1)
  | degree_wrt_typ_t_arrow : forall n1 A1 B1,
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 B1 ->
    degree_typ_wrt_typ n1 (t_arrow A1 B1)
  | degree_wrt_typ_t_and : forall n1 A1 B1,
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 B1 ->
    degree_typ_wrt_typ n1 (t_and A1 B1)
  | degree_wrt_typ_t_rcd : forall n1 l1 A1,
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 (t_rcd l1 A1).

Scheme degree_typ_wrt_typ_ind' := Induction for degree_typ_wrt_typ Sort Prop.

Definition degree_typ_wrt_typ_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  degree_typ_wrt_typ_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.

Inductive degree_exp_wrt_typ : nat -> exp -> Prop :=
  | degree_wrt_typ_e_var_f : forall n1 x1,
    degree_exp_wrt_typ n1 (e_var_f x1)
  | degree_wrt_typ_e_var_b : forall n1 n2,
    degree_exp_wrt_typ n1 (e_var_b n2)
  | degree_wrt_typ_e_top : forall n1,
    degree_exp_wrt_typ n1 (e_top)
  | degree_wrt_typ_e_lit : forall n1 i1,
    degree_exp_wrt_typ n1 (e_lit i1)
  | degree_wrt_typ_e_abs : forall n1 A1 e1,
    degree_typ_wrt_typ n1 A1 ->
    degree_exp_wrt_typ n1 e1 ->
    degree_exp_wrt_typ n1 (e_abs A1 e1)
  | degree_wrt_typ_e_fixpoint : forall n1 A1 e1,
    degree_typ_wrt_typ n1 A1 ->
    degree_exp_wrt_typ n1 e1 ->
    degree_exp_wrt_typ n1 (e_fixpoint A1 e1)
  | degree_wrt_typ_e_app : forall n1 e1 e2,
    degree_exp_wrt_typ n1 e1 ->
    degree_exp_wrt_typ n1 e2 ->
    degree_exp_wrt_typ n1 (e_app e1 e2)
  | degree_wrt_typ_e_merge : forall n1 e1 e2,
    degree_exp_wrt_typ n1 e1 ->
    degree_exp_wrt_typ n1 e2 ->
    degree_exp_wrt_typ n1 (e_merge e1 e2)
  | degree_wrt_typ_e_anno : forall n1 e1 A1,
    degree_exp_wrt_typ n1 e1 ->
    degree_typ_wrt_typ n1 A1 ->
    degree_exp_wrt_typ n1 (e_anno e1 A1)
  | degree_wrt_typ_e_rcd : forall n1 l1 e1,
    degree_exp_wrt_typ n1 e1 ->
    degree_exp_wrt_typ n1 (e_rcd l1 e1)
  | degree_wrt_typ_e_proj : forall n1 e1 l1,
    degree_exp_wrt_typ n1 e1 ->
    degree_exp_wrt_typ n1 (e_proj e1 l1)
  | degree_wrt_typ_e_tabs : forall n1 e1,
    degree_exp_wrt_typ (S n1) e1 ->
    degree_exp_wrt_typ n1 (e_tabs e1)
  | degree_wrt_typ_e_tapp : forall n1 e1 A1,
    degree_exp_wrt_typ n1 e1 ->
    degree_typ_wrt_typ n1 A1 ->
    degree_exp_wrt_typ n1 (e_tapp e1 A1).

Inductive degree_exp_wrt_exp : nat -> exp -> Prop :=
  | degree_wrt_exp_e_var_f : forall n1 x1,
    degree_exp_wrt_exp n1 (e_var_f x1)
  | degree_wrt_exp_e_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_exp_wrt_exp n1 (e_var_b n2)
  | degree_wrt_exp_e_top : forall n1,
    degree_exp_wrt_exp n1 (e_top)
  | degree_wrt_exp_e_lit : forall n1 i1,
    degree_exp_wrt_exp n1 (e_lit i1)
  | degree_wrt_exp_e_abs : forall n1 A1 e1,
    degree_exp_wrt_exp (S n1) e1 ->
    degree_exp_wrt_exp n1 (e_abs A1 e1)
  | degree_wrt_exp_e_fixpoint : forall n1 A1 e1,
    degree_exp_wrt_exp (S n1) e1 ->
    degree_exp_wrt_exp n1 (e_fixpoint A1 e1)
  | degree_wrt_exp_e_app : forall n1 e1 e2,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 e2 ->
    degree_exp_wrt_exp n1 (e_app e1 e2)
  | degree_wrt_exp_e_merge : forall n1 e1 e2,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 e2 ->
    degree_exp_wrt_exp n1 (e_merge e1 e2)
  | degree_wrt_exp_e_anno : forall n1 e1 A1,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 (e_anno e1 A1)
  | degree_wrt_exp_e_rcd : forall n1 l1 e1,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 (e_rcd l1 e1)
  | degree_wrt_exp_e_proj : forall n1 e1 l1,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 (e_proj e1 l1)
  | degree_wrt_exp_e_tabs : forall n1 e1,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 (e_tabs e1)
  | degree_wrt_exp_e_tapp : forall n1 e1 A1,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 (e_tapp e1 A1).

Scheme degree_exp_wrt_typ_ind' := Induction for degree_exp_wrt_typ Sort Prop.

Definition degree_exp_wrt_typ_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 =>
  degree_exp_wrt_typ_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14.

Scheme degree_exp_wrt_exp_ind' := Induction for degree_exp_wrt_exp Sort Prop.

Definition degree_exp_wrt_exp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 =>
  degree_exp_wrt_exp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14.

Inductive lc_set_typ : typ -> Set :=
  | lc_set_t_tvar_f : forall X1,
    lc_set_typ (t_tvar_f X1)
  | lc_set_t_int :
    lc_set_typ (t_int)
  | lc_set_t_top :
    lc_set_typ (t_top)
  | lc_set_t_bot :
    lc_set_typ (t_bot)
  | lc_set_t_forall : forall A1 B1,
    lc_set_typ A1 ->
    (forall X1 : typevar, lc_set_typ (open_typ_wrt_typ B1 (t_tvar_f X1))) ->
    lc_set_typ (t_forall A1 B1)
  | lc_set_t_arrow : forall A1 B1,
    lc_set_typ A1 ->
    lc_set_typ B1 ->
    lc_set_typ (t_arrow A1 B1)
  | lc_set_t_and : forall A1 B1,
    lc_set_typ A1 ->
    lc_set_typ B1 ->
    lc_set_typ (t_and A1 B1)
  | lc_set_t_rcd : forall l1 A1,
    lc_set_typ A1 ->
    lc_set_typ (t_rcd l1 A1).

Scheme lc_typ_ind' := Induction for lc_typ Sort Prop.

Definition lc_typ_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 =>
  lc_typ_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9.

Scheme lc_set_typ_ind' := Induction for lc_set_typ Sort Prop.

Definition lc_set_typ_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 =>
  lc_set_typ_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9.

Scheme lc_set_typ_rec' := Induction for lc_set_typ Sort Set.

Definition lc_set_typ_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 =>
  lc_set_typ_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9.

Inductive lc_set_exp : exp -> Set :=
  | lc_set_e_var_f : forall x1,
    lc_set_exp (e_var_f x1)
  | lc_set_e_top :
    lc_set_exp (e_top)
  | lc_set_e_lit : forall i1,
    lc_set_exp (e_lit i1)
  | lc_set_e_abs : forall A1 e1,
    lc_set_typ A1 ->
    (forall x1 : termvar, lc_set_exp (open_exp_wrt_exp e1 (e_var_f x1))) ->
    lc_set_exp (e_abs A1 e1)
  | lc_set_e_fixpoint : forall A1 e1,
    lc_set_typ A1 ->
    (forall x1 : termvar, lc_set_exp (open_exp_wrt_exp e1 (e_var_f x1))) ->
    lc_set_exp (e_fixpoint A1 e1)
  | lc_set_e_app : forall e1 e2,
    lc_set_exp e1 ->
    lc_set_exp e2 ->
    lc_set_exp (e_app e1 e2)
  | lc_set_e_merge : forall e1 e2,
    lc_set_exp e1 ->
    lc_set_exp e2 ->
    lc_set_exp (e_merge e1 e2)
  | lc_set_e_anno : forall e1 A1,
    lc_set_exp e1 ->
    lc_set_typ A1 ->
    lc_set_exp (e_anno e1 A1)
  | lc_set_e_rcd : forall l1 e1,
    lc_set_exp e1 ->
    lc_set_exp (e_rcd l1 e1)
  | lc_set_e_proj : forall e1 l1,
    lc_set_exp e1 ->
    lc_set_exp (e_proj e1 l1)
  | lc_set_e_tabs : forall e1,
    (forall X1 : typevar, lc_set_exp (open_exp_wrt_typ e1 (t_tvar_f X1))) ->
    lc_set_exp (e_tabs e1)
  | lc_set_e_tapp : forall e1 A1,
    lc_set_exp e1 ->
    lc_set_typ A1 ->
    lc_set_exp (e_tapp e1 A1).

Scheme lc_exp_ind' := Induction for lc_exp Sort Prop.

Definition lc_exp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 =>
  lc_exp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13.

Scheme lc_set_exp_ind' := Induction for lc_set_exp Sort Prop.

Definition lc_set_exp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 =>
  lc_set_exp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13.

Scheme lc_set_exp_rec' := Induction for lc_set_exp Sort Set.

Definition lc_set_exp_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 =>
  lc_set_exp_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13.

Definition body_typ_wrt_typ A1 := forall X1, lc_typ (open_typ_wrt_typ A1 (t_tvar_f X1)).

Definition body_exp_wrt_typ e1 := forall X1, lc_exp (open_exp_wrt_typ e1 (t_tvar_f X1)).

Definition body_exp_wrt_exp e1 := forall x1, lc_exp (open_exp_wrt_exp e1 (e_var_f x1)).
