Set Implicit Arguments.

Require Import TLC.LibLN DeclDef.

Require Import PBCDef DeclInfra.

Fixpoint pfv_ee (e : ptrm) {struct e} : vars :=
  match e with
  | ptrm_bvar i       => \{}
  | ptrm_fvar x       => \{x}
  | ptrm_nat i        => \{}
  | ptrm_absann V e1  => (pfv_ee e1)
  | ptrm_app e1 e2    => (pfv_ee e1) \u (pfv_ee e2)
  | ptrm_cast A B e1  => (pfv_ee e1)
  | ptrm_tabs e       => (pfv_ee e)
  end.

Fixpoint pfv_te (e : ptrm) {struct e} : vars :=
  match e with
  | ptrm_bvar i       => \{}
  | ptrm_fvar x       => \{}
  | ptrm_nat i        => \{}
  | ptrm_absann V e1  => (dfv_tt V) \u (pfv_te e1)
  | ptrm_app e1 e2    => (pfv_te e1) \u (pfv_te e2)
  | ptrm_cast A B e1  => (dfv_tt A) \u (dfv_tt B) \u (pfv_te e1)
  | ptrm_tabs e1      => (pfv_te e1)
  end.

Fixpoint psubst_ee (z : var) (u : ptrm) (e : ptrm) {struct e} : ptrm :=
  match e with
  | ptrm_bvar i       => ptrm_bvar i
  | ptrm_fvar x       => If x = z then u else (ptrm_fvar x)
  | ptrm_nat i        => ptrm_nat i
  | ptrm_absann V e1  => ptrm_absann V (psubst_ee z u e1)
  | ptrm_app e1 e2    => ptrm_app (psubst_ee z u e1) (psubst_ee z u e2)
  | ptrm_cast A B e   => ptrm_cast A B (psubst_ee z u e)
  | ptrm_tabs e1      => ptrm_tabs (psubst_ee z u e1)
  end.

Fixpoint psubst_te (z : var) (u : dtyp) (e : ptrm) {struct e} : ptrm :=
  match e with
  | ptrm_bvar i       => ptrm_bvar i
  | ptrm_fvar x       => ptrm_fvar x
  | ptrm_nat i        => ptrm_nat i
  | ptrm_absann V e1  => ptrm_absann (dsubst_tt z u V) (psubst_te z u e1)
  | ptrm_app e1 e2    => ptrm_app (psubst_te z u e1) (psubst_te z u e2)
  | ptrm_cast A B e   => ptrm_cast (dsubst_tt z u A) (dsubst_tt z u B) (psubst_te z u e)
  | ptrm_tabs e1      => ptrm_tabs (psubst_te z u e1)
  end.

Fixpoint pclose_te_rec (k : nat) (z : var) (t : ptrm) {struct t} : ptrm :=
  match t with
  | ptrm_bvar i        => ptrm_bvar i
  | ptrm_fvar x        => ptrm_fvar x
  | ptrm_nat  i        => ptrm_nat i
  | ptrm_absann t1 t2  => ptrm_absann (dclose_tt_rec k z t1) (pclose_te_rec k z t2)
  | ptrm_app t1 t2     => ptrm_app (pclose_te_rec k z t1) (pclose_te_rec k z t2)
  | ptrm_cast t1 t2 e1 => ptrm_cast (dclose_tt_rec k z t1) (dclose_tt_rec k z t2) (pclose_te_rec k z e1)
  | ptrm_tabs t2       => ptrm_tabs (pclose_te_rec (S k) z t2)
  end.

Definition pclose_te z t := pclose_te_rec 0 z t.

Fixpoint pclose_ee_rec (k : nat) (z : var) (t : ptrm) {struct t} : ptrm :=
  match t with
  | ptrm_bvar i        => ptrm_bvar i
  | ptrm_fvar x        => If x = z then (ptrm_bvar k) else (ptrm_fvar x)
  | ptrm_nat  i        => ptrm_nat i
  | ptrm_absann t1 t2  => ptrm_absann t1 (pclose_ee_rec (S k) z t2)
  | ptrm_app t1 t2     => ptrm_app (pclose_ee_rec k z t1) (pclose_ee_rec k z t2)
  | ptrm_cast t1 t2 e1 => ptrm_cast t1 t2 (pclose_ee_rec k z e1)
  | ptrm_tabs t2       => ptrm_tabs (pclose_ee_rec k z t2)
  end.

Definition pclose_ee z t := pclose_ee_rec 0 z t.
