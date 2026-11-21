Set Implicit Arguments.

From TLC Require Import LibLN.

Require Import DeclDef.

Fixpoint dfv_ee (e : dtrm) {struct e} : vars :=
  match e with
  | dtrm_bvar i       => \{}
  | dtrm_fvar x       => \{x}
  | dtrm_nat i        => \{}
  | dtrm_absann V e1  => (dfv_ee e1)
  | dtrm_abs e1       => (dfv_ee e1)
  | dtrm_app e1 e2    => (dfv_ee e1) \u (dfv_ee e2)
  | dtrm_let e1 e2    => (dfv_ee e1) \u (dfv_ee e2)
  end.

Fixpoint dsubst_ee (z : var) (u : dtrm) (e : dtrm) {struct e} : dtrm :=
  match e with
  | dtrm_bvar i       => dtrm_bvar i
  | dtrm_fvar x       => If x = z then u else (dtrm_fvar x)
  | dtrm_nat i        => dtrm_nat i
  | dtrm_absann V e1  => dtrm_absann V (dsubst_ee z u e1)
  | dtrm_abs e1       => dtrm_abs (dsubst_ee z u e1)
  | dtrm_app e1 e2    => dtrm_app (dsubst_ee z u e1) (dsubst_ee z u e2)
  | dtrm_let e1 e2    => dtrm_let (dsubst_ee z u e1) (dsubst_ee z u e2)
  end.

Fixpoint dfv_tt (T : dtyp) {struct T} : vars :=
  match T with
  | dtyp_nat         => \{}
  | dtyp_unknown     => \{}
  | dtyp_bvar J      => \{}
  | dtyp_fvar X      => \{X}
  | dtyp_arrow T1 T2 => (dfv_tt T1) \u (dfv_tt T2)
  | dtyp_all T1      => (dfv_tt T1)
  end.

Fixpoint dsubst_tt (Z : var) (U : dtyp) (T : dtyp) {struct T} : dtyp :=
  match T with
  | dtyp_nat         => dtyp_nat
  | dtyp_unknown     => dtyp_unknown
  | dtyp_bvar J      => dtyp_bvar J
  | dtyp_fvar X      => If X = Z then U else (dtyp_fvar X)
  | dtyp_arrow T1 T2 => dtyp_arrow (dsubst_tt Z U T1) (dsubst_tt Z U T2)
  | dtyp_all T1      => dtyp_all (dsubst_tt Z U T1)
  end.

Definition dsubst_tb (Z : var) (P : dtyp) (b : dbind) : dbind :=
  match b with
  | dbind_tvar => dbind_tvar
  | dbind_typ T => dbind_typ (dsubst_tt Z P T)
  end.

Fixpoint dfv_tt_env (E : denv) {struct E} : vars :=
  match E with
  | nil                      => \{}
  | cons (x, dbind_typ t) E' => dfv_tt t \u dfv_tt_env E'
  | cons (x, dbind_tvar) E'  => dfv_tt_env E'
  end.

Fixpoint dclose_ee_rec (k : nat) (z : var) (t : dtrm) {struct t} : dtrm :=
  match t with
  | dtrm_bvar i        => dtrm_bvar i
  | dtrm_fvar x        => If x = z then (dtrm_bvar k) else (dtrm_fvar x)
  | dtrm_nat  i        => dtrm_nat i
  | dtrm_absann t1 t2  => dtrm_absann t1 (dclose_ee_rec (S k) z t2)
  | dtrm_abs t         => dtrm_abs (dclose_ee_rec (S k) z t)
  | dtrm_app t1 t2     => dtrm_app (dclose_ee_rec k z t1) (dclose_ee_rec k z t2)
  | dtrm_let t1 t2     => dtrm_let (dclose_ee_rec k z t1) (dclose_ee_rec (S k) z t2)
  end.

Definition dclose_ee z t := dclose_ee_rec 0 z t.

Fixpoint dclose_tt_rec (k : nat) (z : var) (t : dtyp) {struct t} : dtyp :=
  match t with
  | dtyp_bvar i        => dtyp_bvar i
  | dtyp_unknown       => dtyp_unknown
  | dtyp_fvar x        => If x = z then (dtyp_bvar k) else (dtyp_fvar x)
  | dtyp_nat           => dtyp_nat
  | dtyp_arrow t1 t2   => dtyp_arrow (dclose_tt_rec k z t1) (dclose_tt_rec k z t2)
  | dtyp_all t1        => dtyp_all (dclose_tt_rec (S k) z t1)
  end.

Definition dclose_tt z t := dclose_tt_rec 0 z t.

Fixpoint num_of_all (t: dtyp) : nat :=
  match t with
      | dtyp_nat => 0
      | dtyp_unknown => 0
      | dtyp_fvar x => 0
      | dtyp_bvar x => 0
      | dtyp_arrow n1 n2 => (num_of_all n1) + (num_of_all n2)
      | dtyp_all n => 1 + (num_of_all n)
  end.

Fixpoint dtyp_len (t: dtyp) : nat :=
  match t with
  | dtyp_nat => 1
  | dtyp_unknown => 1
  | dtyp_fvar _ => 1
  | dtyp_bvar _ => 1
  | dtyp_arrow t1 t2 =>
      1 + dtyp_len t1 + dtyp_len t2
  | dtyp_all t1 =>
    1 + dtyp_len t1
  end.
