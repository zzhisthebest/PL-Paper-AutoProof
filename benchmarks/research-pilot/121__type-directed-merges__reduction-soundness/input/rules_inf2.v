Require Import Coq.Arith.Wf_nat.

Require Import Coq.Program.Equality.

Require Export Metalib.Metatheory.

Require Export Metalib.LibLNgen.

Require Export syntax_ott.

Scheme dexp_ind' := Induction for dexp Sort Prop.

Definition dexp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 =>
  dexp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9.

Scheme dexp_rec' := Induction for dexp Sort Set.

Definition dexp_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 =>
  dexp_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9.

Fixpoint close_dexp_wrt_dexp_rec (n1 : nat) (x1 : var) (ee1 : dexp) {struct ee1} : dexp :=
  match ee1 with
    | de_var_f x2 => if (x1 == x2) then (de_var_b n1) else (de_var_f x2)
    | de_var_b n2 => if (lt_ge_dec n2 n1) then (de_var_b n2) else (de_var_b (S n2))
    | de_top => de_top
    | de_lit i1 => de_lit i1
    | de_abs ee2 => de_abs (close_dexp_wrt_dexp_rec (S n1) x1 ee2)
    | de_app ee2 ee3 => de_app (close_dexp_wrt_dexp_rec n1 x1 ee2) (close_dexp_wrt_dexp_rec n1 x1 ee3)
    | de_merge ee2 ee3 => de_merge (close_dexp_wrt_dexp_rec n1 x1 ee2) (close_dexp_wrt_dexp_rec n1 x1 ee3)
    | de_fixpoint ee2 => de_fixpoint (close_dexp_wrt_dexp_rec (S n1) x1 ee2)
  end.

Definition close_dexp_wrt_dexp x1 ee1 := close_dexp_wrt_dexp_rec 0 x1 ee1.

Fixpoint size_dexp (ee1 : dexp) {struct ee1} : nat :=
  match ee1 with
    | de_var_f x1 => 1
    | de_var_b n1 => 1
    | de_top => 1
    | de_lit i1 => 1
    | de_abs ee2 => 1 + (size_dexp ee2)
    | de_app ee2 ee3 => 1 + (size_dexp ee2) + (size_dexp ee3)
    | de_merge ee2 ee3 => 1 + (size_dexp ee2) + (size_dexp ee3)
    | de_fixpoint ee2 => 1 + (size_dexp ee2)
  end.

Inductive degree_dexp_wrt_dexp : nat -> dexp -> Prop :=
  | degree_wrt_dexp_de_var_f : forall n1 x1,
    degree_dexp_wrt_dexp n1 (de_var_f x1)
  | degree_wrt_dexp_de_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_dexp_wrt_dexp n1 (de_var_b n2)
  | degree_wrt_dexp_de_top : forall n1,
    degree_dexp_wrt_dexp n1 (de_top)
  | degree_wrt_dexp_de_lit : forall n1 i1,
    degree_dexp_wrt_dexp n1 (de_lit i1)
  | degree_wrt_dexp_de_abs : forall n1 ee1,
    degree_dexp_wrt_dexp (S n1) ee1 ->
    degree_dexp_wrt_dexp n1 (de_abs ee1)
  | degree_wrt_dexp_de_app : forall n1 ee1 ee2,
    degree_dexp_wrt_dexp n1 ee1 ->
    degree_dexp_wrt_dexp n1 ee2 ->
    degree_dexp_wrt_dexp n1 (de_app ee1 ee2)
  | degree_wrt_dexp_de_merge : forall n1 ee1 ee2,
    degree_dexp_wrt_dexp n1 ee1 ->
    degree_dexp_wrt_dexp n1 ee2 ->
    degree_dexp_wrt_dexp n1 (de_merge ee1 ee2)
  | degree_wrt_dexp_de_fixpoint : forall n1 ee1,
    degree_dexp_wrt_dexp (S n1) ee1 ->
    degree_dexp_wrt_dexp n1 (de_fixpoint ee1).

Scheme degree_dexp_wrt_dexp_ind' := Induction for degree_dexp_wrt_dexp Sort Prop.

Definition degree_dexp_wrt_dexp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 =>
  degree_dexp_wrt_dexp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9.

Inductive lc_set_dexp : dexp -> Set :=
  | lc_set_de_var_f : forall x1,
    lc_set_dexp (de_var_f x1)
  | lc_set_de_top :
    lc_set_dexp (de_top)
  | lc_set_de_lit : forall i1,
    lc_set_dexp (de_lit i1)
  | lc_set_de_abs : forall ee1,
    (forall x1 : var, lc_set_dexp (open_dexp_wrt_dexp ee1 (de_var_f x1))) ->
    lc_set_dexp (de_abs ee1)
  | lc_set_de_app : forall ee1 ee2,
    lc_set_dexp ee1 ->
    lc_set_dexp ee2 ->
    lc_set_dexp (de_app ee1 ee2)
  | lc_set_de_merge : forall ee1 ee2,
    lc_set_dexp ee1 ->
    lc_set_dexp ee2 ->
    lc_set_dexp (de_merge ee1 ee2)
  | lc_set_de_fixpoint : forall ee1,
    (forall x1 : var, lc_set_dexp (open_dexp_wrt_dexp ee1 (de_var_f x1))) ->
    lc_set_dexp (de_fixpoint ee1).

Scheme lc_dexp_ind' := Induction for lc_dexp Sort Prop.

Definition lc_dexp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 =>
  lc_dexp_ind' H1 H2 H3 H4 H5 H6 H7 H8.

Scheme lc_set_dexp_ind' := Induction for lc_set_dexp Sort Prop.

Definition lc_set_dexp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 =>
  lc_set_dexp_ind' H1 H2 H3 H4 H5 H6 H7 H8.

Scheme lc_set_dexp_rec' := Induction for lc_set_dexp Sort Set.

Definition lc_set_dexp_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 =>
  lc_set_dexp_rec' H1 H2 H3 H4 H5 H6 H7 H8.

Definition body_dexp_wrt_dexp ee1 := forall x1, lc_dexp (open_dexp_wrt_dexp ee1 (de_var_f x1)).
