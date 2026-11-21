Require Import Coq.Logic.FunctionalExtensionality.

Require Import Coq.Program.Equality.

Require Export Metalib.Metatheory.

Require Export Metalib.LibLNgen.

Require Export Syntax_ott.

Scheme sty_ind' := Induction for sty Sort Prop.

Definition sty_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  sty_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.

Scheme sty_rec' := Induction for sty Sort Set.

Definition sty_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  sty_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.

Scheme sexp_ind' := Induction for sexp Sort Prop.

Definition sexp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 =>
  sexp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13.

Scheme sexp_rec' := Induction for sexp Sort Set.

Definition sexp_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 =>
  sexp_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13.

Fixpoint close_sty_wrt_sty_rec (n1 : nat) (X1 : typvar) (A1 : sty) {struct A1} : sty :=
  match A1 with
    | sty_nat => sty_nat
    | sty_top => sty_top
    | sty_bot => sty_bot
    | sty_var_f X2 => if (X1 == X2) then (sty_var_b n1) else (sty_var_f X2)
    | sty_var_b n2 => if (lt_ge_dec n2 n1) then (sty_var_b n2) else (sty_var_b (S n2))
    | sty_arrow A2 B1 => sty_arrow (close_sty_wrt_sty_rec n1 X1 A2) (close_sty_wrt_sty_rec n1 X1 B1)
    | sty_and A2 B1 => sty_and (close_sty_wrt_sty_rec n1 X1 A2) (close_sty_wrt_sty_rec n1 X1 B1)
    | sty_all A2 B1 => sty_all (close_sty_wrt_sty_rec n1 X1 A2) (close_sty_wrt_sty_rec (S n1) X1 B1)
    | sty_rcd l1 A2 => sty_rcd l1 (close_sty_wrt_sty_rec n1 X1 A2)
  end.

Definition close_sty_wrt_sty X1 A1 := close_sty_wrt_sty_rec 0 X1 A1.

Fixpoint close_sexp_wrt_sty_rec (n1 : nat) (X1 : typvar) (ee1 : sexp) {struct ee1} : sexp :=
  match ee1 with
    | sexp_var_f x1 => sexp_var_f x1
    | sexp_var_b n2 => sexp_var_b n2
    | sexp_top => sexp_top
    | sexp_lit i5 => sexp_lit i5
    | sexp_abs ee2 => sexp_abs (close_sexp_wrt_sty_rec n1 X1 ee2)
    | sexp_app ee2 ee3 => sexp_app (close_sexp_wrt_sty_rec n1 X1 ee2) (close_sexp_wrt_sty_rec n1 X1 ee3)
    | sexp_merge ee2 ee3 => sexp_merge (close_sexp_wrt_sty_rec n1 X1 ee2) (close_sexp_wrt_sty_rec n1 X1 ee3)
    | sexp_tabs A1 ee2 => sexp_tabs (close_sty_wrt_sty_rec n1 X1 A1) (close_sexp_wrt_sty_rec (S n1) X1 ee2)
    | sexp_tapp ee2 A1 => sexp_tapp (close_sexp_wrt_sty_rec n1 X1 ee2) (close_sty_wrt_sty_rec n1 X1 A1)
    | sexp_anno ee2 A1 => sexp_anno (close_sexp_wrt_sty_rec n1 X1 ee2) (close_sty_wrt_sty_rec n1 X1 A1)
    | sexp_rcd l1 ee2 => sexp_rcd l1 (close_sexp_wrt_sty_rec n1 X1 ee2)
    | sexp_proj ee2 l1 => sexp_proj (close_sexp_wrt_sty_rec n1 X1 ee2) l1
  end.

Fixpoint close_sexp_wrt_sexp_rec (n1 : nat) (x1 : expvar) (ee1 : sexp) {struct ee1} : sexp :=
  match ee1 with
    | sexp_var_f x2 => if (x1 == x2) then (sexp_var_b n1) else (sexp_var_f x2)
    | sexp_var_b n2 => if (lt_ge_dec n2 n1) then (sexp_var_b n2) else (sexp_var_b (S n2))
    | sexp_top => sexp_top
    | sexp_lit i5 => sexp_lit i5
    | sexp_abs ee2 => sexp_abs (close_sexp_wrt_sexp_rec (S n1) x1 ee2)
    | sexp_app ee2 ee3 => sexp_app (close_sexp_wrt_sexp_rec n1 x1 ee2) (close_sexp_wrt_sexp_rec n1 x1 ee3)
    | sexp_merge ee2 ee3 => sexp_merge (close_sexp_wrt_sexp_rec n1 x1 ee2) (close_sexp_wrt_sexp_rec n1 x1 ee3)
    | sexp_tabs A1 ee2 => sexp_tabs A1 (close_sexp_wrt_sexp_rec n1 x1 ee2)
    | sexp_tapp ee2 A1 => sexp_tapp (close_sexp_wrt_sexp_rec n1 x1 ee2) A1
    | sexp_anno ee2 A1 => sexp_anno (close_sexp_wrt_sexp_rec n1 x1 ee2) A1
    | sexp_rcd l1 ee2 => sexp_rcd l1 (close_sexp_wrt_sexp_rec n1 x1 ee2)
    | sexp_proj ee2 l1 => sexp_proj (close_sexp_wrt_sexp_rec n1 x1 ee2) l1
  end.

Definition close_sexp_wrt_sty X1 ee1 := close_sexp_wrt_sty_rec 0 X1 ee1.

Definition close_sexp_wrt_sexp x1 ee1 := close_sexp_wrt_sexp_rec 0 x1 ee1.

Fixpoint size_sty (A1 : sty) {struct A1} : nat :=
  match A1 with
    | sty_nat => 1
    | sty_top => 1
    | sty_bot => 1
    | sty_var_f X1 => 1
    | sty_var_b n1 => 1
    | sty_arrow A2 B1 => 1 + (size_sty A2) + (size_sty B1)
    | sty_and A2 B1 => 1 + (size_sty A2) + (size_sty B1)
    | sty_all A2 B1 => 1 + (size_sty A2) + (size_sty B1)
    | sty_rcd l1 A2 => 1 + (size_sty A2)
  end.

Fixpoint size_sexp (ee1 : sexp) {struct ee1} : nat :=
  match ee1 with
    | sexp_var_f x1 => 1
    | sexp_var_b n1 => 1
    | sexp_top => 1
    | sexp_lit i5 => 1
    | sexp_abs ee2 => 1 + (size_sexp ee2)
    | sexp_app ee2 ee3 => 1 + (size_sexp ee2) + (size_sexp ee3)
    | sexp_merge ee2 ee3 => 1 + (size_sexp ee2) + (size_sexp ee3)
    | sexp_tabs A1 ee2 => 1 + (size_sty A1) + (size_sexp ee2)
    | sexp_tapp ee2 A1 => 1 + (size_sexp ee2) + (size_sty A1)
    | sexp_anno ee2 A1 => 1 + (size_sexp ee2) + (size_sty A1)
    | sexp_rcd l1 ee2 => 1 + (size_sexp ee2)
    | sexp_proj ee2 l1 => 1 + (size_sexp ee2)
  end.

Inductive degree_sty_wrt_sty : nat -> sty -> Prop :=
  | degree_wrt_sty_sty_nat : forall n1,
    degree_sty_wrt_sty n1 (sty_nat)
  | degree_wrt_sty_sty_top : forall n1,
    degree_sty_wrt_sty n1 (sty_top)
  | degree_wrt_sty_sty_bot : forall n1,
    degree_sty_wrt_sty n1 (sty_bot)
  | degree_wrt_sty_sty_var_f : forall n1 X1,
    degree_sty_wrt_sty n1 (sty_var_f X1)
  | degree_wrt_sty_sty_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_sty_wrt_sty n1 (sty_var_b n2)
  | degree_wrt_sty_sty_arrow : forall n1 A1 B1,
    degree_sty_wrt_sty n1 A1 ->
    degree_sty_wrt_sty n1 B1 ->
    degree_sty_wrt_sty n1 (sty_arrow A1 B1)
  | degree_wrt_sty_sty_and : forall n1 A1 B1,
    degree_sty_wrt_sty n1 A1 ->
    degree_sty_wrt_sty n1 B1 ->
    degree_sty_wrt_sty n1 (sty_and A1 B1)
  | degree_wrt_sty_sty_all : forall n1 A1 B1,
    degree_sty_wrt_sty n1 A1 ->
    degree_sty_wrt_sty (S n1) B1 ->
    degree_sty_wrt_sty n1 (sty_all A1 B1)
  | degree_wrt_sty_sty_rcd : forall n1 l1 A1,
    degree_sty_wrt_sty n1 A1 ->
    degree_sty_wrt_sty n1 (sty_rcd l1 A1).

Scheme degree_sty_wrt_sty_ind' := Induction for degree_sty_wrt_sty Sort Prop.

Definition degree_sty_wrt_sty_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  degree_sty_wrt_sty_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.

Inductive degree_sexp_wrt_sty : nat -> sexp -> Prop :=
  | degree_wrt_sty_sexp_var_f : forall n1 x1,
    degree_sexp_wrt_sty n1 (sexp_var_f x1)
  | degree_wrt_sty_sexp_var_b : forall n1 n2,
    degree_sexp_wrt_sty n1 (sexp_var_b n2)
  | degree_wrt_sty_sexp_top : forall n1,
    degree_sexp_wrt_sty n1 (sexp_top)
  | degree_wrt_sty_sexp_lit : forall n1 i5,
    degree_sexp_wrt_sty n1 (sexp_lit i5)
  | degree_wrt_sty_sexp_abs : forall n1 ee1,
    degree_sexp_wrt_sty n1 ee1 ->
    degree_sexp_wrt_sty n1 (sexp_abs ee1)
  | degree_wrt_sty_sexp_app : forall n1 ee1 ee2,
    degree_sexp_wrt_sty n1 ee1 ->
    degree_sexp_wrt_sty n1 ee2 ->
    degree_sexp_wrt_sty n1 (sexp_app ee1 ee2)
  | degree_wrt_sty_sexp_merge : forall n1 ee1 ee2,
    degree_sexp_wrt_sty n1 ee1 ->
    degree_sexp_wrt_sty n1 ee2 ->
    degree_sexp_wrt_sty n1 (sexp_merge ee1 ee2)
  | degree_wrt_sty_sexp_tabs : forall n1 A1 ee1,
    degree_sty_wrt_sty n1 A1 ->
    degree_sexp_wrt_sty (S n1) ee1 ->
    degree_sexp_wrt_sty n1 (sexp_tabs A1 ee1)
  | degree_wrt_sty_sexp_tapp : forall n1 ee1 A1,
    degree_sexp_wrt_sty n1 ee1 ->
    degree_sty_wrt_sty n1 A1 ->
    degree_sexp_wrt_sty n1 (sexp_tapp ee1 A1)
  | degree_wrt_sty_sexp_anno : forall n1 ee1 A1,
    degree_sexp_wrt_sty n1 ee1 ->
    degree_sty_wrt_sty n1 A1 ->
    degree_sexp_wrt_sty n1 (sexp_anno ee1 A1)
  | degree_wrt_sty_sexp_rcd : forall n1 l1 ee1,
    degree_sexp_wrt_sty n1 ee1 ->
    degree_sexp_wrt_sty n1 (sexp_rcd l1 ee1)
  | degree_wrt_sty_sexp_proj : forall n1 ee1 l1,
    degree_sexp_wrt_sty n1 ee1 ->
    degree_sexp_wrt_sty n1 (sexp_proj ee1 l1).

Inductive degree_sexp_wrt_sexp : nat -> sexp -> Prop :=
  | degree_wrt_sexp_sexp_var_f : forall n1 x1,
    degree_sexp_wrt_sexp n1 (sexp_var_f x1)
  | degree_wrt_sexp_sexp_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_sexp_wrt_sexp n1 (sexp_var_b n2)
  | degree_wrt_sexp_sexp_top : forall n1,
    degree_sexp_wrt_sexp n1 (sexp_top)
  | degree_wrt_sexp_sexp_lit : forall n1 i5,
    degree_sexp_wrt_sexp n1 (sexp_lit i5)
  | degree_wrt_sexp_sexp_abs : forall n1 ee1,
    degree_sexp_wrt_sexp (S n1) ee1 ->
    degree_sexp_wrt_sexp n1 (sexp_abs ee1)
  | degree_wrt_sexp_sexp_app : forall n1 ee1 ee2,
    degree_sexp_wrt_sexp n1 ee1 ->
    degree_sexp_wrt_sexp n1 ee2 ->
    degree_sexp_wrt_sexp n1 (sexp_app ee1 ee2)
  | degree_wrt_sexp_sexp_merge : forall n1 ee1 ee2,
    degree_sexp_wrt_sexp n1 ee1 ->
    degree_sexp_wrt_sexp n1 ee2 ->
    degree_sexp_wrt_sexp n1 (sexp_merge ee1 ee2)
  | degree_wrt_sexp_sexp_tabs : forall n1 A1 ee1,
    degree_sexp_wrt_sexp n1 ee1 ->
    degree_sexp_wrt_sexp n1 (sexp_tabs A1 ee1)
  | degree_wrt_sexp_sexp_tapp : forall n1 ee1 A1,
    degree_sexp_wrt_sexp n1 ee1 ->
    degree_sexp_wrt_sexp n1 (sexp_tapp ee1 A1)
  | degree_wrt_sexp_sexp_anno : forall n1 ee1 A1,
    degree_sexp_wrt_sexp n1 ee1 ->
    degree_sexp_wrt_sexp n1 (sexp_anno ee1 A1)
  | degree_wrt_sexp_sexp_rcd : forall n1 l1 ee1,
    degree_sexp_wrt_sexp n1 ee1 ->
    degree_sexp_wrt_sexp n1 (sexp_rcd l1 ee1)
  | degree_wrt_sexp_sexp_proj : forall n1 ee1 l1,
    degree_sexp_wrt_sexp n1 ee1 ->
    degree_sexp_wrt_sexp n1 (sexp_proj ee1 l1).

Scheme degree_sexp_wrt_sty_ind' := Induction for degree_sexp_wrt_sty Sort Prop.

Definition degree_sexp_wrt_sty_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 =>
  degree_sexp_wrt_sty_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13.

Scheme degree_sexp_wrt_sexp_ind' := Induction for degree_sexp_wrt_sexp Sort Prop.

Definition degree_sexp_wrt_sexp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 =>
  degree_sexp_wrt_sexp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13.

Inductive lc_set_sty : sty -> Set :=
  | lc_set_sty_nat :
    lc_set_sty (sty_nat)
  | lc_set_sty_top :
    lc_set_sty (sty_top)
  | lc_set_sty_bot :
    lc_set_sty (sty_bot)
  | lc_set_sty_var_f : forall X1,
    lc_set_sty (sty_var_f X1)
  | lc_set_sty_arrow : forall A1 B1,
    lc_set_sty A1 ->
    lc_set_sty B1 ->
    lc_set_sty (sty_arrow A1 B1)
  | lc_set_sty_and : forall A1 B1,
    lc_set_sty A1 ->
    lc_set_sty B1 ->
    lc_set_sty (sty_and A1 B1)
  | lc_set_sty_all : forall A1 B1,
    lc_set_sty A1 ->
    (forall X1 : typvar, lc_set_sty (open_sty_wrt_sty B1 (sty_var_f X1))) ->
    lc_set_sty (sty_all A1 B1)
  | lc_set_sty_rcd : forall l1 A1,
    lc_set_sty A1 ->
    lc_set_sty (sty_rcd l1 A1).

Scheme lc_sty_ind' := Induction for lc_sty Sort Prop.

Definition lc_sty_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 =>
  lc_sty_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9.

Scheme lc_set_sty_ind' := Induction for lc_set_sty Sort Prop.

Definition lc_set_sty_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 =>
  lc_set_sty_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9.

Scheme lc_set_sty_rec' := Induction for lc_set_sty Sort Set.

Definition lc_set_sty_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 =>
  lc_set_sty_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9.

Inductive lc_set_sexp : sexp -> Set :=
  | lc_set_sexp_var_f : forall x1,
    lc_set_sexp (sexp_var_f x1)
  | lc_set_sexp_top :
    lc_set_sexp (sexp_top)
  | lc_set_sexp_lit : forall i5,
    lc_set_sexp (sexp_lit i5)
  | lc_set_sexp_abs : forall ee1,
    (forall x1 : expvar, lc_set_sexp (open_sexp_wrt_sexp ee1 (sexp_var_f x1))) ->
    lc_set_sexp (sexp_abs ee1)
  | lc_set_sexp_app : forall ee1 ee2,
    lc_set_sexp ee1 ->
    lc_set_sexp ee2 ->
    lc_set_sexp (sexp_app ee1 ee2)
  | lc_set_sexp_merge : forall ee1 ee2,
    lc_set_sexp ee1 ->
    lc_set_sexp ee2 ->
    lc_set_sexp (sexp_merge ee1 ee2)
  | lc_set_sexp_tabs : forall A1 ee1,
    lc_set_sty A1 ->
    (forall X1 : typvar, lc_set_sexp (open_sexp_wrt_sty ee1 (sty_var_f X1))) ->
    lc_set_sexp (sexp_tabs A1 ee1)
  | lc_set_sexp_tapp : forall ee1 A1,
    lc_set_sexp ee1 ->
    lc_set_sty A1 ->
    lc_set_sexp (sexp_tapp ee1 A1)
  | lc_set_sexp_anno : forall ee1 A1,
    lc_set_sexp ee1 ->
    lc_set_sty A1 ->
    lc_set_sexp (sexp_anno ee1 A1)
  | lc_set_sexp_rcd : forall l1 ee1,
    lc_set_sexp ee1 ->
    lc_set_sexp (sexp_rcd l1 ee1)
  | lc_set_sexp_proj : forall ee1 l1,
    lc_set_sexp ee1 ->
    lc_set_sexp (sexp_proj ee1 l1).

Scheme lc_sexp_ind' := Induction for lc_sexp Sort Prop.

Definition lc_sexp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 =>
  lc_sexp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12.

Scheme lc_set_sexp_ind' := Induction for lc_set_sexp Sort Prop.

Definition lc_set_sexp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 =>
  lc_set_sexp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12.

Scheme lc_set_sexp_rec' := Induction for lc_set_sexp Sort Set.

Definition lc_set_sexp_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 =>
  lc_set_sexp_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12.

Definition body_sty_wrt_sty A1 := forall X1, lc_sty (open_sty_wrt_sty A1 (sty_var_f X1)).

Definition body_sexp_wrt_sty ee1 := forall X1, lc_sexp (open_sexp_wrt_sty ee1 (sty_var_f X1)).

Definition body_sexp_wrt_sexp ee1 := forall x1, lc_sexp (open_sexp_wrt_sexp ee1 (sexp_var_f x1)).
