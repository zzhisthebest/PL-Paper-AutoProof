Require Export Fsub.EffectExclusion.Fsub_LetSum_Definitions.

Fixpoint fv_tt (T : typ) {struct T} : atoms :=
  match T with
  | typ_top => {}
  | typ_int => {}
  | typ_bvar J => {}
  | typ_fvar X => {{ X }}
  | typ_arrow T1 T2 => (fv_tqt T1) `union` (fv_tqt T2)
  | typ_all T1 T2 => (fv_tt T1) `union` (fv_tqt T2)
  | typ_qall Q T  => (fv_tqt T)
  | typ_sum T1 T2 => (fv_tqt T1) `union` (fv_tqt T2)
  | typ_pair T1 T2 => (fv_tqt T1) `union` (fv_tqt T2)
  | typ_ref T1 => (fv_tqt T1)
  end
with fv_tqt (T : qtyp) {struct T} : atoms :=
  match T with
  | qtyp_qtyp Q T => (fv_tt T)
  end.

Fixpoint fv_te (e : exp) {struct e} : atoms :=
  match e with
  | exp_int P i => {}
  | exp_bvar i => {}
  | exp_fvar x => {}
  | exp_abs P V e1  => (fv_tqt V) `union` (fv_te e1)
  | exp_app e1 e2 => (fv_te e1) `union` (fv_te e2)
  | exp_tabs P V e1 => (fv_tt V) `union` (fv_te e1)
  | exp_tapp e1 V => (fv_tt V) `union` (fv_te e1)
  | exp_qabs P V e1 => (fv_te e1)
  | exp_qapp e1 V => (fv_te e1)
  | exp_let e1 e2 => (fv_te e1) `union` (fv_te e2)
  | exp_inl P e1 => (fv_te e1)
  | exp_inr P e1 => (fv_te e1)
  | exp_case e1 e2 e3 => (fv_te e1) `union` (fv_te e2) `union` (fv_te e3)
  | exp_pair P e1 e2 => (fv_te e1) `union` (fv_te e2)
  | exp_first e1 => (fv_te e1)
  | exp_second e1 => (fv_te e1)
  | exp_ref P e1 => (fv_te e1)
  | exp_ref_label P l => {}
  | exp_deref e1 => (fv_te e1)
  | exp_set_ref e1 e2 => (fv_te e1) `union` (fv_te e2)
  | exp_upqual P e1 => (fv_te e1)
  | exp_check P e1 => (fv_te e1)
  | exp_without P e1 => (fv_te e1)
  | exp_do b => {}
  | exp_if0 e1 e2 e3 => (fv_te e1) `union` (fv_te e2) `union` (fv_te e3)
  end.

Fixpoint fv_qq (Q : qua) {struct Q} : atoms :=
  match Q with
  | qua_base b => {}
  | qua_bvar i => {}
  | qua_fvar X => {{ X }}
  | qua_meet Q1 Q2 => fv_qq Q1 `union` fv_qq Q2
  | qua_join Q1 Q2 => fv_qq Q1 `union` fv_qq Q2
  | qua_negate Q1 => fv_qq Q1
  end.

Fixpoint fv_qt (T : typ) {struct T} : atoms :=
  match T with
  | typ_int => {}
  | typ_top => {}
  | typ_bvar J => {}
  | typ_fvar X => {}
  | typ_arrow T1 T2 => (fv_qqt T1) `union` (fv_qqt T2)
  | typ_all T1 T2 => (fv_qt T1) `union` (fv_qqt T2)
  | typ_qall Q T  => (fv_qq Q) `union` (fv_qqt T)
  | typ_sum T1 T2 => (fv_qqt T1) `union` (fv_qqt T2)
  | typ_pair T1 T2 => (fv_qqt T1) `union` (fv_qqt T2)
  | typ_ref T1 => fv_qqt T1
  end
with fv_qqt (T : qtyp) {struct T} : atoms :=
  match T with
  | qtyp_qtyp Q T => (fv_qq Q) `union` (fv_qt T)
  end.

Fixpoint fv_qe (e : exp) {struct e} : atoms :=
  match e with
  | exp_int P i => fv_qq P
  | exp_bvar i => {}
  | exp_fvar x => {}
  | exp_abs P V e1  => (fv_qq P) `union` (fv_qqt V) `union` (fv_qe e1)
  | exp_app e1 e2 => (fv_qe e1) `union` (fv_qe e2)
  | exp_tabs P V e1 => (fv_qq P) `union` (fv_qt V) `union` (fv_qe e1)
  | exp_tapp e1 V => (fv_qt V) `union` (fv_qe e1)
  | exp_qabs P V e1 => (fv_qq P) `union` (fv_qe e1) `union` (fv_qq V)
  | exp_qapp e1 V => (fv_qe e1) `union` (fv_qq V)
  | exp_let e1 e2 => (fv_qe e1) `union` (fv_qe e2)
  | exp_inl P e1 => (fv_qq P) `union` (fv_qe e1)
  | exp_inr P e1 => (fv_qq P) `union` (fv_qe e1)
  | exp_case e1 e2 e3 => (fv_qe e1) `union` (fv_qe e2) `union` (fv_qe e3)
  | exp_pair P e1 e2 => (fv_qq P) `union` (fv_qe e1) `union` (fv_qe e2)
  | exp_first e1 => (fv_qe e1)
  | exp_second e1 => (fv_qe e1)
  | exp_ref P e1 => (fv_qq P) `union` (fv_qe e1)
  | exp_ref_label P l => (fv_qq P)
  | exp_deref e1 => (fv_qe e1)
  | exp_set_ref e1 e2 => (fv_qe e1) `union` (fv_qe e2)
  | exp_upqual P e1 => (fv_qq P) `union` (fv_qe e1)
  | exp_check P e1 => (fv_qq P) `union` (fv_qe e1)
  | exp_without P e1 => (fv_qq P) `union` (fv_qe e1)
  | exp_do b => {}
  | exp_if0 e1 e2 e3 => (fv_qe e1) `union` (fv_qe e2) `union` (fv_qe e3)
  end.

Fixpoint fv_ee (e : exp) {struct e} : atoms :=
  match e with
  | exp_int P i => {}
  | exp_bvar i => {}
  | exp_fvar x => {{ x }}
  | exp_abs P V e1 => (fv_ee e1)
  | exp_app e1 e2 => (fv_ee e1) `union` (fv_ee e2)
  | exp_tabs P V e1 => (fv_ee e1)
  | exp_tapp e1 V => (fv_ee e1)
  | exp_qabs P V e1 => (fv_ee e1)
  | exp_qapp e1 V => (fv_ee e1)
  | exp_let e1 e2 => (fv_ee e1) `union` (fv_ee e2)
  | exp_inl P e1 => (fv_ee e1)
  | exp_inr P e1 => (fv_ee e1)
  | exp_case e1 e2 e3 => (fv_ee e1) `union` (fv_ee e2) `union` (fv_ee e3)
  | exp_pair P e1 e2 => (fv_ee e1) `union` (fv_ee e2)
  | exp_first e1 => (fv_ee e1)
  | exp_second e1 => (fv_ee e1)
  | exp_ref P e1 => (fv_ee e1)
  | exp_ref_label P l => {}
  | exp_deref e1 => (fv_ee e1)
  | exp_set_ref e1 e2 => (fv_ee e1) `union` (fv_ee e2)
  | exp_upqual P e1 => (fv_ee e1)
  | exp_check P e1 => (fv_ee e1)
  | exp_without P e1 => (fv_ee e1)
  | exp_do b => {}
  | exp_if0 e1 e2 e3 => (fv_ee e1) `union` (fv_ee e2) `union` (fv_ee e3)
  end.

Fixpoint subst_tt (Z : atom) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | typ_top => typ_top
  | typ_int => typ_int
  | typ_bvar J => typ_bvar J
  | typ_fvar X => if X == Z then U else T
  | typ_arrow T1 T2 => typ_arrow (subst_tqt Z U T1) (subst_tqt Z U T2)
  | typ_all T1 T2 => typ_all (subst_tt Z U T1) (subst_tqt Z U T2)
  | typ_qall Q T => typ_qall Q (subst_tqt Z U T)
  | typ_sum T1 T2 => typ_sum (subst_tqt Z U T1) (subst_tqt Z U T2)
  | typ_pair T1 T2 => typ_pair (subst_tqt Z U T1) (subst_tqt Z U T2)
  | typ_ref T1 => typ_ref (subst_tqt Z U T1)
  end
with subst_tqt (Z : atom) (U : typ) (T : qtyp) {struct T} : qtyp :=
  match T with
  | qtyp_qtyp Q T => qtyp_qtyp Q (subst_tt Z U T)
  end
  .

Fixpoint subst_qq (Z : atom) (U : qua) (T : qua) {struct T} : qua :=
  match T with
  | qua_base b => qua_base b
  | qua_bvar J => qua_bvar J
  | qua_fvar X => if X == Z then U else T
  | qua_meet T1 T2 => qua_meet (subst_qq Z U T1) (subst_qq Z U T2)
  | qua_join T1 T2 => qua_join (subst_qq Z U T1) (subst_qq Z U T2)
  | qua_negate T1 => qua_negate (subst_qq Z U T1)
  end.

Fixpoint subst_qt (Z : atom) (U : qua) (T : typ) {struct T} : typ :=
  match T with
  | typ_top => typ_top
  | typ_int => typ_int
  | typ_bvar J => typ_bvar J
  | typ_fvar X => typ_fvar X
  | typ_arrow T1 T2 => typ_arrow (subst_qqt Z U T1) (subst_qqt Z U T2)
  | typ_all T1 T2 => typ_all (subst_qt Z U T1) (subst_qqt Z U T2)
  | typ_qall Q T => typ_qall (subst_qq Z U Q) (subst_qqt Z U T)
  | typ_sum T1 T2 => typ_sum (subst_qqt Z U T1) (subst_qqt Z U T2)
  | typ_pair T1 T2 => typ_pair (subst_qqt Z U T1) (subst_qqt Z U T2)
  | typ_ref T1 => typ_ref (subst_qqt Z U T1)
  end
with subst_qqt (Z : atom) (U : qua) (T : qtyp) {struct T} : qtyp :=
  match T with
  | qtyp_qtyp Q T => qtyp_qtyp (subst_qq Z U Q) (subst_qt Z U T)
  end.

Fixpoint subst_qe (Z : atom) (U : qua) (e : exp) {struct e} : exp :=
  match e with
  | exp_int P i => exp_int (subst_qq Z U P) i
  | exp_bvar i => exp_bvar i
  | exp_fvar x => exp_fvar x
  | exp_abs P V e1 => exp_abs (subst_qq Z U P) (subst_qqt Z U V)  (subst_qe Z U e1)
  | exp_app e1 e2 => exp_app  (subst_qe Z U e1) (subst_qe Z U e2)
  | exp_tabs P V e1 => exp_tabs (subst_qq Z U P) (subst_qt Z U V)  (subst_qe Z U e1)
  | exp_tapp e1 V => exp_tapp (subst_qe Z U e1) (subst_qt Z U V)
  | exp_qabs P Q e1 => exp_qabs (subst_qq Z U P) (subst_qq Z U Q)  (subst_qe Z U e1)
  | exp_qapp e1 Q => exp_qapp (subst_qe Z U e1) (subst_qq Z U Q)
  | exp_let e1 e2 => exp_let (subst_qe Z U e1) (subst_qe Z U e2)
  | exp_inl P e1 => exp_inl (subst_qq Z U P) (subst_qe Z U e1)
  | exp_inr P e1 => exp_inr (subst_qq Z U P) (subst_qe Z U e1)
  | exp_case e1 e2 e3 => exp_case (subst_qe Z U e1)
                                  (subst_qe Z U e2) (subst_qe Z U e3)
  | exp_pair P e1 e2 => exp_pair (subst_qq Z U P) (subst_qe Z U e1) (subst_qe Z U e2)
  | exp_first e1 => exp_first (subst_qe Z U e1)
  | exp_second e1 => exp_second (subst_qe Z U e1)
  | exp_ref P e1 => exp_ref (subst_qq Z U P) (subst_qe Z U e1)
  | exp_ref_label P l => exp_ref_label  (subst_qq Z U P) l
  | exp_deref e1 => exp_deref (subst_qe Z U e1)
  | exp_set_ref e1 e2 => exp_set_ref (subst_qe Z U e1) (subst_qe Z U e2)
  | exp_upqual P e1 => exp_upqual (subst_qq Z U P) (subst_qe Z U e1)
  | exp_check P e1 => exp_check (subst_qq Z U P) (subst_qe Z U e1)
  | exp_without P e1 => exp_without (subst_qq Z U P) (subst_qe Z U e1)
  | exp_do b => exp_do b
  | exp_if0 e1 e2 e3 => exp_if0 (subst_qe Z U e1)
                                  (subst_qe Z U e2) (subst_qe Z U e3)
  end.

Fixpoint subst_te (Z : atom) (U : typ) (e : exp) {struct e} : exp :=
  match e with
  | exp_int P i => exp_int P i
  | exp_bvar i => exp_bvar i
  | exp_fvar x => exp_fvar x
  | exp_abs P V e1 => exp_abs P (subst_tqt Z U V)  (subst_te Z U e1)
  | exp_app e1 e2 => exp_app  (subst_te Z U e1) (subst_te Z U e2)
  | exp_tabs P V e1 => exp_tabs P (subst_tt Z U V)  (subst_te Z U e1)
  | exp_tapp e1 V => exp_tapp (subst_te Z U e1) (subst_tt Z U V)
  | exp_qabs P Q e1 => exp_qabs P Q (subst_te Z U e1)
  | exp_qapp e1 Q => exp_qapp (subst_te Z U e1) Q
  | exp_let e1 e2 => exp_let (subst_te Z U e1) (subst_te Z U e2)
  | exp_inl P e1 => exp_inl P (subst_te Z U e1)
  | exp_inr P e1 => exp_inr P (subst_te Z U e1)
  | exp_case e1 e2 e3 => exp_case (subst_te Z U e1)
                                  (subst_te Z U e2) (subst_te Z U e3)
  | exp_pair P e1 e2 => exp_pair P (subst_te Z U e1) (subst_te Z U e2)
  | exp_first e1 => exp_first (subst_te Z U e1)
  | exp_second e1 => exp_second (subst_te Z U e1)
  | exp_ref P e1 => exp_ref P (subst_te Z U e1)
  | exp_ref_label P l => exp_ref_label P l
  | exp_deref e1 => exp_deref (subst_te Z U e1)
  | exp_set_ref e1 e2 => exp_set_ref (subst_te Z U e1) (subst_te Z U e2)
  | exp_upqual P e1 => exp_upqual P (subst_te Z U e1)
  | exp_check P e1 => exp_check P (subst_te Z U e1)
  | exp_without P e1 => exp_without P (subst_te Z U e1)
  | exp_do b => exp_do b
  | exp_if0 e1 e2 e3 => exp_if0 (subst_te Z U e1)
                                  (subst_te Z U e2) (subst_te Z U e3)
  end.

Fixpoint subst_ee (z : atom) (u : exp) (e : exp) {struct e} : exp :=
  match e with
  | exp_int P i => exp_int P i
  | exp_bvar i => exp_bvar i
  | exp_fvar x => if x == z then u else e
  | exp_abs P V e1 => exp_abs P V (subst_ee z u e1)
  | exp_app e1 e2 => exp_app (subst_ee z u e1) (subst_ee z u e2)
  | exp_tabs P V e1 => exp_tabs P V (subst_ee z u e1)
  | exp_tapp e1 V => exp_tapp (subst_ee z u e1) V
  | exp_qabs P Q e1 => exp_qabs P Q (subst_ee z u e1)
  | exp_qapp e1 Q => exp_qapp (subst_ee z u e1) Q
  | exp_let e1 e2 => exp_let (subst_ee z u e1) (subst_ee z u e2)
  | exp_inl P e1 => exp_inl P (subst_ee z u e1)
  | exp_inr P e1 => exp_inr P (subst_ee z u e1)
  | exp_case e1 e2 e3 => exp_case (subst_ee z u e1)
                                  (subst_ee z u e2) (subst_ee z u e3)
  | exp_pair P e1 e2 => exp_pair P (subst_ee z u e1) (subst_ee z u e2)
  | exp_first e1 => exp_first (subst_ee z u e1)
  | exp_second e1 => exp_second (subst_ee z u e1)
  | exp_ref P e1 => exp_ref P (subst_ee z u e1)
  | exp_ref_label P l => exp_ref_label P l
  | exp_deref e1 => exp_deref (subst_ee z u e1)
  | exp_set_ref e1 e2 => exp_set_ref (subst_ee z u e1) (subst_ee z u e2)
  | exp_upqual P e1 => exp_upqual P (subst_ee z u e1)
  | exp_check P e1 => exp_check P (subst_ee z u e1)
  | exp_without P e1 => exp_without P (subst_ee z u e1)
  | exp_do b => exp_do b
  | exp_if0 e1 e2 e3 => exp_if0 (subst_ee z u e1)
                                  (subst_ee z u e2) (subst_ee z u e3)
  end.

Definition subst_tb (Z : atom) (P : typ) (b : binding) : binding :=
  match b with
  | bind_sub T => bind_sub (subst_tt Z P T)
  | bind_typ T => bind_typ (subst_tqt Z P T)
  | bind_qua Q => bind_qua Q
  end.

Definition subst_qb (Z : atom) (P : qua) (b : binding) : binding :=
  match b with
  | bind_sub T => bind_sub (subst_qt Z P T)
  | bind_typ T => bind_typ (subst_qqt Z P T)
  | bind_qua Q => bind_qua (subst_qq Z P Q)
  end.
