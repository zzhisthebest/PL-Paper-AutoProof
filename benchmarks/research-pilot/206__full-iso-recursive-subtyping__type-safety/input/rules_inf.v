Require Import Coq.Arith.Wf_nat.

Require Import Coq.Logic.FunctionalExtensionality.

Require Import Coq.Program.Equality.

Require Export Metalib.Metatheory.

Require Export Metalib.LibLNgen.

Require Export syntax_ott.

Scheme typ_ind' := Induction for typ Sort Prop.

Combined Scheme typ_mutind from typ_ind'.

Scheme typ_rec' := Induction for typ Sort Set.

Combined Scheme typ_mutrec from typ_rec'.

Scheme castop_ind' := Induction for castop Sort Prop.

Combined Scheme castop_mutind from castop_ind'.

Scheme castop_rec' := Induction for castop Sort Set.

Combined Scheme castop_mutrec from castop_rec'.

Scheme exp_ind' := Induction for exp Sort Prop.

Combined Scheme exp_mutind from exp_ind'.

Scheme exp_rec' := Induction for exp Sort Set.

Combined Scheme exp_mutrec from exp_rec'.

Fixpoint size_typ (A1 : typ) {struct A1} : nat :=
  match A1 with
    | t_var_f X1 => 1
    | t_var_b n1 => 1
    | t_int => 1
    | t_top => 1
    | t_arrow A2 B1 => 1 + (size_typ A2) + (size_typ B1)
    | t_mu A2 => 1 + (size_typ A2)
  end.

Fixpoint size_castop (c1 : castop) {struct c1} : nat :=
  match c1 with
    | c_var_f cx1 => 1
    | c_var_b n1 => 1
    | c_id => 1
    | c_unfold A1 => 1 + (size_typ A1)
    | c_fold A1 => 1 + (size_typ A1)
    | c_arrow c2 c3 => 1 + (size_castop c2) + (size_castop c3)
    | c_seq c2 c3 => 1 + (size_castop c2) + (size_castop c3)
    | c_fixc c2 => 1 + (size_castop c2)
  end.

Fixpoint size_exp (e1 : exp) {struct e1} : nat :=
  match e1 with
    | e_var_f x1 => 1
    | e_var_b n1 => 1
    | e_lit i1 => 1
    | e_abs A1 e2 => 1 + (size_typ A1) + (size_exp e2)
    | e_app e2 e3 => 1 + (size_exp e2) + (size_exp e3)
    | e_cast c1 e2 => 1 + (size_castop c1) + (size_exp e2)
  end.

Inductive degree_typ_wrt_typ : nat -> typ -> Prop :=
  | degree_wrt_typ_t_var_f : forall n1 X1,
    degree_typ_wrt_typ n1 (t_var_f X1)
  | degree_wrt_typ_t_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_typ_wrt_typ n1 (t_var_b n2)
  | degree_wrt_typ_t_int : forall n1,
    degree_typ_wrt_typ n1 (t_int)
  | degree_wrt_typ_t_top : forall n1,
    degree_typ_wrt_typ n1 (t_top)
  | degree_wrt_typ_t_arrow : forall n1 A1 B1,
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 B1 ->
    degree_typ_wrt_typ n1 (t_arrow A1 B1)
  | degree_wrt_typ_t_mu : forall n1 A1,
    degree_typ_wrt_typ (S n1) A1 ->
    degree_typ_wrt_typ n1 (t_mu A1).

Scheme degree_typ_wrt_typ_ind' := Induction for degree_typ_wrt_typ Sort Prop.

Combined Scheme degree_typ_wrt_typ_mutind from degree_typ_wrt_typ_ind'.

Inductive degree_castop_wrt_typ : nat -> castop -> Prop :=
  | degree_wrt_typ_c_var_f : forall n1 cx1,
    degree_castop_wrt_typ n1 (c_var_f cx1)
  | degree_wrt_typ_c_var_b : forall n1 n2,
    degree_castop_wrt_typ n1 (c_var_b n2)
  | degree_wrt_typ_c_id : forall n1,
    degree_castop_wrt_typ n1 (c_id)
  | degree_wrt_typ_c_unfold : forall n1 A1,
    degree_typ_wrt_typ n1 A1 ->
    degree_castop_wrt_typ n1 (c_unfold A1)
  | degree_wrt_typ_c_fold : forall n1 A1,
    degree_typ_wrt_typ n1 A1 ->
    degree_castop_wrt_typ n1 (c_fold A1)
  | degree_wrt_typ_c_arrow : forall n1 c1 c2,
    degree_castop_wrt_typ n1 c1 ->
    degree_castop_wrt_typ n1 c2 ->
    degree_castop_wrt_typ n1 (c_arrow c1 c2)
  | degree_wrt_typ_c_seq : forall n1 c1 c2,
    degree_castop_wrt_typ n1 c1 ->
    degree_castop_wrt_typ n1 c2 ->
    degree_castop_wrt_typ n1 (c_seq c1 c2)
  | degree_wrt_typ_c_fixc : forall n1 c1,
    degree_castop_wrt_typ n1 c1 ->
    degree_castop_wrt_typ n1 (c_fixc c1).

Inductive degree_castop_wrt_castop : nat -> castop -> Prop :=
  | degree_wrt_castop_c_var_f : forall n1 cx1,
    degree_castop_wrt_castop n1 (c_var_f cx1)
  | degree_wrt_castop_c_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_castop_wrt_castop n1 (c_var_b n2)
  | degree_wrt_castop_c_id : forall n1,
    degree_castop_wrt_castop n1 (c_id)
  | degree_wrt_castop_c_unfold : forall n1 A1,
    degree_castop_wrt_castop n1 (c_unfold A1)
  | degree_wrt_castop_c_fold : forall n1 A1,
    degree_castop_wrt_castop n1 (c_fold A1)
  | degree_wrt_castop_c_arrow : forall n1 c1 c2,
    degree_castop_wrt_castop n1 c1 ->
    degree_castop_wrt_castop n1 c2 ->
    degree_castop_wrt_castop n1 (c_arrow c1 c2)
  | degree_wrt_castop_c_seq : forall n1 c1 c2,
    degree_castop_wrt_castop n1 c1 ->
    degree_castop_wrt_castop n1 c2 ->
    degree_castop_wrt_castop n1 (c_seq c1 c2)
  | degree_wrt_castop_c_fixc : forall n1 c1,
    degree_castop_wrt_castop (S n1) c1 ->
    degree_castop_wrt_castop n1 (c_fixc c1).

Scheme degree_castop_wrt_typ_ind' := Induction for degree_castop_wrt_typ Sort Prop.

Combined Scheme degree_castop_wrt_typ_mutind from degree_castop_wrt_typ_ind'.

Scheme degree_castop_wrt_castop_ind' := Induction for degree_castop_wrt_castop Sort Prop.

Combined Scheme degree_castop_wrt_castop_mutind from degree_castop_wrt_castop_ind'.

Inductive degree_exp_wrt_typ : nat -> exp -> Prop :=
  | degree_wrt_typ_e_var_f : forall n1 x1,
    degree_exp_wrt_typ n1 (e_var_f x1)
  | degree_wrt_typ_e_var_b : forall n1 n2,
    degree_exp_wrt_typ n1 (e_var_b n2)
  | degree_wrt_typ_e_lit : forall n1 i1,
    degree_exp_wrt_typ n1 (e_lit i1)
  | degree_wrt_typ_e_abs : forall n1 A1 e1,
    degree_typ_wrt_typ n1 A1 ->
    degree_exp_wrt_typ n1 e1 ->
    degree_exp_wrt_typ n1 (e_abs A1 e1)
  | degree_wrt_typ_e_app : forall n1 e1 e2,
    degree_exp_wrt_typ n1 e1 ->
    degree_exp_wrt_typ n1 e2 ->
    degree_exp_wrt_typ n1 (e_app e1 e2)
  | degree_wrt_typ_e_cast : forall n1 c1 e1,
    degree_castop_wrt_typ n1 c1 ->
    degree_exp_wrt_typ n1 e1 ->
    degree_exp_wrt_typ n1 (e_cast c1 e1).

Inductive degree_exp_wrt_castop : nat -> exp -> Prop :=
  | degree_wrt_castop_e_var_f : forall n1 x1,
    degree_exp_wrt_castop n1 (e_var_f x1)
  | degree_wrt_castop_e_var_b : forall n1 n2,
    degree_exp_wrt_castop n1 (e_var_b n2)
  | degree_wrt_castop_e_lit : forall n1 i1,
    degree_exp_wrt_castop n1 (e_lit i1)
  | degree_wrt_castop_e_abs : forall n1 A1 e1,
    degree_exp_wrt_castop n1 e1 ->
    degree_exp_wrt_castop n1 (e_abs A1 e1)
  | degree_wrt_castop_e_app : forall n1 e1 e2,
    degree_exp_wrt_castop n1 e1 ->
    degree_exp_wrt_castop n1 e2 ->
    degree_exp_wrt_castop n1 (e_app e1 e2)
  | degree_wrt_castop_e_cast : forall n1 c1 e1,
    degree_castop_wrt_castop n1 c1 ->
    degree_exp_wrt_castop n1 e1 ->
    degree_exp_wrt_castop n1 (e_cast c1 e1).

Inductive degree_exp_wrt_exp : nat -> exp -> Prop :=
  | degree_wrt_exp_e_var_f : forall n1 x1,
    degree_exp_wrt_exp n1 (e_var_f x1)
  | degree_wrt_exp_e_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_exp_wrt_exp n1 (e_var_b n2)
  | degree_wrt_exp_e_lit : forall n1 i1,
    degree_exp_wrt_exp n1 (e_lit i1)
  | degree_wrt_exp_e_abs : forall n1 A1 e1,
    degree_exp_wrt_exp (S n1) e1 ->
    degree_exp_wrt_exp n1 (e_abs A1 e1)
  | degree_wrt_exp_e_app : forall n1 e1 e2,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 e2 ->
    degree_exp_wrt_exp n1 (e_app e1 e2)
  | degree_wrt_exp_e_cast : forall n1 c1 e1,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 (e_cast c1 e1).

Scheme degree_exp_wrt_typ_ind' := Induction for degree_exp_wrt_typ Sort Prop.

Combined Scheme degree_exp_wrt_typ_mutind from degree_exp_wrt_typ_ind'.

Scheme degree_exp_wrt_castop_ind' := Induction for degree_exp_wrt_castop Sort Prop.

Combined Scheme degree_exp_wrt_castop_mutind from degree_exp_wrt_castop_ind'.

Scheme degree_exp_wrt_exp_ind' := Induction for degree_exp_wrt_exp Sort Prop.

Combined Scheme degree_exp_wrt_exp_mutind from degree_exp_wrt_exp_ind'.

Inductive lc_set_typ : typ -> Set :=
  | lc_set_t_var_f : forall X1,
    lc_set_typ (t_var_f X1)
  | lc_set_t_int :
    lc_set_typ (t_int)
  | lc_set_t_top :
    lc_set_typ (t_top)
  | lc_set_t_arrow : forall A1 B1,
    lc_set_typ A1 ->
    lc_set_typ B1 ->
    lc_set_typ (t_arrow A1 B1)
  | lc_set_t_mu : forall A1,
    (forall X1 : typevar, lc_set_typ (open_typ_wrt_typ A1 (t_var_f X1))) ->
    lc_set_typ (t_mu A1).

Scheme lc_typ_ind' := Induction for lc_typ Sort Prop.

Combined Scheme lc_typ_mutind from lc_typ_ind'.

Scheme lc_set_typ_ind' := Induction for lc_set_typ Sort Prop.

Combined Scheme lc_set_typ_mutind from lc_set_typ_ind'.

Scheme lc_set_typ_rec' := Induction for lc_set_typ Sort Set.

Combined Scheme lc_set_typ_mutrec from lc_set_typ_rec'.

Inductive lc_set_castop : castop -> Set :=
  | lc_set_c_var_f : forall cx1,
    lc_set_castop (c_var_f cx1)
  | lc_set_c_id :
    lc_set_castop (c_id)
  | lc_set_c_unfold : forall A1,
    lc_set_typ A1 ->
    lc_set_castop (c_unfold A1)
  | lc_set_c_fold : forall A1,
    lc_set_typ A1 ->
    lc_set_castop (c_fold A1)
  | lc_set_c_arrow : forall c1 c2,
    lc_set_castop c1 ->
    lc_set_castop c2 ->
    lc_set_castop (c_arrow c1 c2)
  | lc_set_c_seq : forall c1 c2,
    lc_set_castop c1 ->
    lc_set_castop c2 ->
    lc_set_castop (c_seq c1 c2)
  | lc_set_c_fixc : forall c1,
    (forall cx1 : castvar, lc_set_castop (open_castop_wrt_castop c1 (c_var_f cx1))) ->
    lc_set_castop (c_fixc c1).

Scheme lc_castop_ind' := Induction for lc_castop Sort Prop.

Combined Scheme lc_castop_mutind from lc_castop_ind'.

Scheme lc_set_castop_ind' := Induction for lc_set_castop Sort Prop.

Combined Scheme lc_set_castop_mutind from lc_set_castop_ind'.

Scheme lc_set_castop_rec' := Induction for lc_set_castop Sort Set.

Combined Scheme lc_set_castop_mutrec from lc_set_castop_rec'.

Inductive lc_set_exp : exp -> Set :=
  | lc_set_e_var_f : forall x1,
    lc_set_exp (e_var_f x1)
  | lc_set_e_lit : forall i1,
    lc_set_exp (e_lit i1)
  | lc_set_e_abs : forall A1 e1,
    lc_set_typ A1 ->
    (forall x1 : termvar, lc_set_exp (open_exp_wrt_exp e1 (e_var_f x1))) ->
    lc_set_exp (e_abs A1 e1)
  | lc_set_e_app : forall e1 e2,
    lc_set_exp e1 ->
    lc_set_exp e2 ->
    lc_set_exp (e_app e1 e2)
  | lc_set_e_cast : forall c1 e1,
    lc_set_castop c1 ->
    lc_set_exp e1 ->
    lc_set_exp (e_cast c1 e1).

Scheme lc_exp_ind' := Induction for lc_exp Sort Prop.

Combined Scheme lc_exp_mutind from lc_exp_ind'.

Scheme lc_set_exp_ind' := Induction for lc_set_exp Sort Prop.

Combined Scheme lc_set_exp_mutind from lc_set_exp_ind'.

Scheme lc_set_exp_rec' := Induction for lc_set_exp Sort Set.

Combined Scheme lc_set_exp_mutrec from lc_set_exp_rec'.

Definition body_typ_wrt_typ A1 := forall X1, lc_typ (open_typ_wrt_typ A1 (t_var_f X1)).

Definition body_castop_wrt_typ c1 := forall X1, lc_castop (open_castop_wrt_typ c1 (t_var_f X1)).

Definition body_castop_wrt_castop c1 := forall cx1, lc_castop (open_castop_wrt_castop c1 (c_var_f cx1)).

Definition body_exp_wrt_typ e1 := forall X1, lc_exp (open_exp_wrt_typ e1 (t_var_f X1)).

Definition body_exp_wrt_castop e1 := forall cx1, lc_exp (open_exp_wrt_castop e1 (c_var_f cx1)).

Definition body_exp_wrt_exp e1 := forall x1, lc_exp (open_exp_wrt_exp e1 (e_var_f x1)).
