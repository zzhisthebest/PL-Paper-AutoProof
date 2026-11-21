Set Implicit Arguments.

From TLC Require Import LibLN.

Require Import DeclDef FDef.

Require Import DeclInfra.

Definition ffv_tt := dfv_tt.

Fixpoint ffv_te (e : ftrm) {struct e} : vars :=
  match e with
  | ftrm_bvar i       => \{}
  | ftrm_fvar x       => \{}
  | ftrm_nat  i       => \{}
  | ftrm_absann V e1  => (ffv_tt V) \u (ffv_te e1)
  | ftrm_app e1 e2    => (ffv_te e1) \u (ffv_te e2)
  | ftrm_tabs e1      => (ffv_te e1)
  | ftrm_tapp e1 V    => (ffv_tt V) \u (ffv_te e1)
  | ftrm_pair e1 e2   => (ffv_te e1) \u (ffv_te e2)
  | ftrm_fst e1       => (ffv_te e1)
  | ftrm_snd e1       => (ffv_te e1)
  end.

Fixpoint ffv_ee (e : ftrm) {struct e} : vars :=
  match e with
  | ftrm_bvar i       => \{}
  | ftrm_fvar x       => \{x}
  | ftrm_nat i        => \{}
  | ftrm_absann V e1  => (ffv_ee e1)
  | ftrm_app e1 e2    => (ffv_ee e1) \u (ffv_ee e2)
  | ftrm_tabs e1      => (ffv_ee e1)
  | ftrm_tapp e1 V    => (ffv_ee e1)
  | ftrm_pair e1 e2   => (ffv_ee e1) \u (ffv_ee e2)
  | ftrm_fst e1       => (ffv_ee e1)
  | ftrm_snd e1       => (ffv_ee e1)
  end.

Definition fsubst_tt := dsubst_tt.

Fixpoint fsubst_te (Z : var) (U : ftyp) (e : ftrm) {struct e} : ftrm :=
  match e with
  | ftrm_bvar i       => ftrm_bvar i
  | ftrm_fvar x       => ftrm_fvar x
  | ftrm_nat i        => ftrm_nat i
  | ftrm_absann V e1  => ftrm_absann  (fsubst_tt Z U V)  (fsubst_te Z U e1)
  | ftrm_app e1 e2    => ftrm_app  (fsubst_te Z U e1) (fsubst_te Z U e2)
  | ftrm_tabs e1      => ftrm_tabs (fsubst_te Z U e1)
  | ftrm_tapp e1 V    => ftrm_tapp (fsubst_te Z U e1) (fsubst_tt Z U V)
  | ftrm_pair e1 e2   => ftrm_pair  (fsubst_te Z U e1) (fsubst_te Z U e2)
  | ftrm_fst e1       => ftrm_fst  (fsubst_te Z U e1)
  | ftrm_snd e1       => ftrm_snd  (fsubst_te Z U e1)
  end.

Fixpoint fsubst_ee (z : var) (u : ftrm) (e : ftrm) {struct e} : ftrm :=
  match e with
  | ftrm_bvar i       => ftrm_bvar i
  | ftrm_fvar x       => If x = z then u else (ftrm_fvar x)
  | ftrm_nat i        => ftrm_nat i
  | ftrm_absann V e1  => ftrm_absann V (fsubst_ee z u e1)
  | ftrm_app e1 e2    => ftrm_app  (fsubst_ee z u e1) (fsubst_ee z u e2)
  | ftrm_tabs e1      => ftrm_tabs (fsubst_ee z u e1)
  | ftrm_tapp e1 V    => ftrm_tapp (fsubst_ee z u e1) V
  | ftrm_pair e1 e2   => ftrm_pair (fsubst_ee z u e1) (fsubst_ee z u e2)
  | ftrm_fst e1       => ftrm_fst (fsubst_ee z u e1)
  | ftrm_snd e1       => ftrm_snd (fsubst_ee z u e1)
  end.

Fixpoint fclose_ee_rec (k : nat) (z : var) (t : ftrm) {struct t} : ftrm :=
  match t with
  | ftrm_bvar i        => ftrm_bvar i
  | ftrm_fvar x        => If x = z then (ftrm_bvar k) else (ftrm_fvar x)
  | ftrm_nat  i        => ftrm_nat i
  | ftrm_absann t1 t2  => ftrm_absann t1 (fclose_ee_rec (S k) z t2)
  | ftrm_app t1 t2     => ftrm_app (fclose_ee_rec k z t1) (fclose_ee_rec k z t2)
  | ftrm_tabs t1       => ftrm_tabs (fclose_ee_rec k z t1)
  | ftrm_tapp t1 t2    => ftrm_tapp (fclose_ee_rec k z t1) t2
  | ftrm_pair t1 t2    => ftrm_pair (fclose_ee_rec k z t1) (fclose_ee_rec k z t2)
  | ftrm_fst t1        => ftrm_fst (fclose_ee_rec k z t1)
  | ftrm_snd t1        => ftrm_snd (fclose_ee_rec k z t1)
  end.

Definition fclose_ee z t := fclose_ee_rec 0 z t.

Fixpoint fclose_tt_rec (k : nat) (z : var) (t : ftyp) {struct t} : ftyp :=
  match t with
  | dtyp_bvar i        => ftyp_bvar i
  | dtyp_fvar x        => If x = z then (dtyp_bvar k) else (dtyp_fvar x)
  | dtyp_nat           => ftyp_nat
  | dtyp_arrow t1 t2   => dtyp_arrow (fclose_tt_rec k z t1) (fclose_tt_rec k z t2)
  | dtyp_all t1        => dtyp_all (fclose_tt_rec (S k) z t1)
  | dtyp_pair t1 t2    => dtyp_pair (fclose_tt_rec k z t1) (fclose_tt_rec k z t2)
  end.

Fixpoint fclose_te_rec (k : nat) (z : var) (t : ftrm) {struct t} : ftrm :=
  match t with
  | ftrm_bvar i        => ftrm_bvar i
  | ftrm_fvar x        => ftrm_fvar x
  | ftrm_nat  i        => ftrm_nat i
  | ftrm_absann t1 t2  => ftrm_absann (fclose_tt_rec k z t1) (fclose_te_rec k z t2)
  | ftrm_app t1 t2     => ftrm_app (fclose_te_rec k z t1) (fclose_te_rec k z t2)
  | ftrm_tabs t1       => ftrm_tabs (fclose_te_rec (S k) z t1)
  | ftrm_tapp t1 t2    => ftrm_tapp (fclose_te_rec k z t1) (fclose_tt_rec k z t2)
  | ftrm_pair t1 t2    => ftrm_pair (fclose_te_rec k z t1) (fclose_te_rec k z t2)
  | ftrm_fst t1        => ftrm_fst (fclose_te_rec k z t1)
  | ftrm_snd t1        => ftrm_snd (fclose_te_rec k z t1)
  end.

Definition fclose_tt z t := fclose_tt_rec 0 z t.

Definition fclose_te z t := fclose_te_rec 0 z t.
