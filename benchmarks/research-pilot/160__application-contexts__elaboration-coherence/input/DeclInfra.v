Set Implicit Arguments.

From TLC Require Import LibList LibLN.

Require Import DeclDef.

Fixpoint dfv_ee (e : dtrm) {struct e} : vars :=
  match e with
  | dtrm_bvar i       => \{}
  | dtrm_fvar x       => \{x}
  | dtrm_nat i           => \{}
  | dtrm_abs e1       => (dfv_ee e1)
  | dtrm_absann V e1  => (dfv_ee e1)
  | dtrm_app e1 e2    => (dfv_ee e1) \u (dfv_ee e2)
  | dtrm_pair e1 e2   => (dfv_ee e1) \u (dfv_ee e2)
  | dtrm_fst          => \{}
  | dtrm_snd          => \{}
  end.

Fixpoint dfv_stack (G : dstack) {struct G} : vars :=
  match G with
  | nil => \{}
  | cons c cs => dfv_tt c \u (dfv_stack cs)
  end.

Fixpoint dfv_aenv (G : aenv) {struct G} : vars :=
  match G with
  | plain => \{}
  | stack s => dfv_stack s
  end.

Fixpoint dsubst_tt (Z : var) (U : dtyp) (T : dtyp) {struct T} : dtyp :=
  match T with
  | dtyp_nat         => dtyp_nat
  | dtyp_bvar J      => dtyp_bvar J
  | dtyp_fvar X      => If X = Z then U else (dtyp_fvar X)
  | dtyp_arrow T1 T2 => dtyp_arrow (dsubst_tt Z U T1) (dsubst_tt Z U T2)
  | dtyp_all T1      => dtyp_all (dsubst_tt Z U T1)
  | dtyp_pair T1 T2  => dtyp_pair (dsubst_tt Z U T1) (dsubst_tt Z U T2)
  end.

Fixpoint dsubst_ee (z : var) (u : dtrm) (e : dtrm) {struct e} : dtrm :=
  match e with
  | dtrm_bvar i       => dtrm_bvar i
  | dtrm_fvar x       => If x = z then u else (dtrm_fvar x)
  | dtrm_nat i        => dtrm_nat i
  | dtrm_abs e1       => dtrm_abs (dsubst_ee z u e1)
  | dtrm_absann V e1  => dtrm_absann V (dsubst_ee z u e1)
  | dtrm_app e1 e2    => dtrm_app (dsubst_ee z u e1) (dsubst_ee z u e2)
  | dtrm_pair e1 e2   => dtrm_pair (dsubst_ee z u e1) (dsubst_ee z u e2)
  | dtrm_fst          => dtrm_fst
  | dtrm_snd          => dtrm_snd
  end.

Definition dsubst_stack (Z: var) (P: dtyp) (b:dstack) : dstack := List.map (dsubst_tt Z P) b.

Definition dsubst_aenv (Z: var) (P: dtyp) (a:aenv) : aenv :=
  match a with
    | plain => plain
    | stack s => stack (dsubst_stack Z P s)
  end.

Inductive dstack_type : dstack -> Prop :=
| dstack_type_empty: dstack_type nil
| dstack_type_cons : forall t s,
    dtype t ->
    dstack_type s ->
    dstack_type (t :: s).

Inductive daenv_type : aenv -> Prop :=
| daenv_type_plain: daenv_type plain
| daenv_type_stack : forall s,
    dstack_type s ->
    daenv_type (stack s).

Fixpoint dclose_ee_rec (k : nat) (z : var) (t : dtrm) {struct t} : dtrm :=
  match t with
  | dtrm_bvar i        => dtrm_bvar i
  | dtrm_fvar x        => If x = z then (dtrm_bvar k) else (dtrm_fvar x)
  | dtrm_nat  i        => dtrm_nat i
  | dtrm_abs  t2       => dtrm_abs (dclose_ee_rec (S k) z t2)
  | dtrm_absann t1 t2  => dtrm_absann t1 (dclose_ee_rec (S k) z t2)
  | dtrm_app t1 t2     => dtrm_app (dclose_ee_rec k z t1) (dclose_ee_rec k z t2)
  | dtrm_pair t1 t2    => dtrm_pair (dclose_ee_rec k z t1) (dclose_ee_rec k z t2)
  | dtrm_fst           => dtrm_fst
  | dtrm_snd           => dtrm_snd
  end.

Definition dclose_ee z t := dclose_ee_rec 0 z t.

Fixpoint dclose_tt_rec (k : nat) (z : var) (t : dtyp) {struct t} : dtyp :=
  match t with
  | dtyp_bvar i        => dtyp_bvar i
  | dtyp_fvar x        => If x = z then (dtyp_bvar k) else (dtyp_fvar x)
  | dtyp_nat           => dtyp_nat
  | dtyp_arrow t1 t2   => dtyp_arrow (dclose_tt_rec k z t1) (dclose_tt_rec k z t2)
  | dtyp_all t1        => dtyp_all (dclose_tt_rec (S k) z t1)
  | dtyp_pair t1 t2    => dtyp_pair (dclose_tt_rec k z t1) (dclose_tt_rec k z t2)
  end.

Fixpoint dclose_te_rec (k : nat) (z : var) (t : dtrm) {struct t} : dtrm :=
  match t with
  | dtrm_bvar i        => dtrm_bvar i
  | dtrm_fvar x        => dtrm_fvar x
  | dtrm_nat  i        => dtrm_nat i
  | dtrm_abs  t2       => dtrm_abs (dclose_te_rec k z t2)
  | dtrm_absann t1 t2  => dtrm_absann (dclose_tt_rec k z t1) (dclose_te_rec k z t2)
  | dtrm_app t1 t2     => dtrm_app (dclose_te_rec k z t1) (dclose_te_rec k z t2)
  | dtrm_pair t1 t2    => dtrm_pair (dclose_te_rec k z t1) (dclose_te_rec k z t2)
  | dtrm_fst           => dtrm_fst
  | dtrm_snd           => dtrm_snd
  end.

Definition dclose_tt z t := dclose_tt_rec 0 z t.

Definition dclose_te z t := dclose_te_rec 0 z t.
