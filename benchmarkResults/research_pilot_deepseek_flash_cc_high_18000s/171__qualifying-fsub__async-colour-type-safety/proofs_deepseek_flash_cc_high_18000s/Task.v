From Fsub.FuncColour Require Import Fsub_LetSum_Definitions.
From Stdlib Require Import Lia.
From Stdlib Require Import Program.Equality.


(* ===== inlined from /workspace/Task.v ===== *)

(* ===================================================================== *)
(* Free atoms                                                            *)
(* ===================================================================== *)

Fixpoint fv_qq (Q : qua) : atoms :=
  match Q with
  | qua_top => AtomSetImpl.empty
  | qua_bot => AtomSetImpl.empty
  | qua_bvar _ => AtomSetImpl.empty
  | qua_fvar X => singleton X
  | qua_meet Q1 Q2 => union (fv_qq Q1) (fv_qq Q2)
  | qua_join Q1 Q2 => union (fv_qq Q1) (fv_qq Q2)
  end.

Fixpoint fv_tt (T : typ) : atoms :=
  match T with
  | typ_top => AtomSetImpl.empty
  | typ_bvar _ => AtomSetImpl.empty
  | typ_fvar X => singleton X
  | typ_arrow T1 T2 => union (fv_tqt T1) (fv_tqt T2)
  | typ_all T1 T2 => union (fv_tt T1) (fv_tqt T2)
  | typ_qall Q T => union (fv_qq Q) (fv_tqt T)
  | typ_sum T1 T2 => union (fv_tqt T1) (fv_tqt T2)
  | typ_pair T1 T2 => union (fv_tqt T1) (fv_tqt T2)
  | typ_ref T1 => fv_tqt T1
  end
with fv_tqt (T : qtyp) : atoms :=
  match T with
  | qtyp_qtyp Q T => union (fv_qq Q) (fv_tt T)
  end.

Fixpoint fv_ee (e : exp) : atoms :=
  match e with
  | exp_bvar _ => AtomSetImpl.empty
  | exp_fvar x => singleton x
  | exp_abs P V e1 => union (fv_qq P) (union (fv_tqt V) (fv_ee e1))
  | exp_app e1 e2 => union (fv_ee e1) (fv_ee e2)
  | exp_tabs P V e1 => union (fv_qq P) (union (fv_tt V) (fv_ee e1))
  | exp_tapp e1 V => union (fv_ee e1) (fv_tt V)
  | exp_qabs P Q e1 => union (fv_qq P) (union (fv_qq Q) (fv_ee e1))
  | exp_qapp e1 Q => union (fv_ee e1) (fv_qq Q)
  | exp_let e1 e2 => union (fv_ee e1) (fv_ee e2)
  | exp_inl P e1 => union (fv_qq P) (fv_ee e1)
  | exp_inr P e1 => union (fv_qq P) (fv_ee e1)
  | exp_case e1 e2 e3 => union (fv_ee e1) (union (fv_ee e2) (fv_ee e3))
  | exp_pair P e1 e2 => union (fv_qq P) (union (fv_ee e1) (fv_ee e2))
  | exp_first e1 => fv_ee e1
  | exp_second e1 => fv_ee e1
  | exp_ref P e1 => union (fv_qq P) (fv_ee e1)
  | exp_ref_label P _ => fv_qq P
  | exp_deref e1 => fv_ee e1
  | exp_set_ref e1 e2 => union (fv_ee e1) (fv_ee e2)
  | exp_upqual P e1 => union (fv_qq P) (fv_ee e1)
  | exp_check P e1 => union (fv_qq P) (fv_ee e1)
  end.

Definition fv_binding (b : binding) : atoms :=
  match b with
  | bind_sub T => fv_tt T
  | bind_typ T => fv_tqt T
  | bind_qua Q => fv_qq Q
  end.

Definition fv_env (E : env) : atoms :=
  fold_right (fun xb acc => union (fv_binding (snd xb)) acc) AtomSetImpl.empty E.

(* ===================================================================== *)
(* Substitutions                                                          *)
(* ===================================================================== *)

Fixpoint subst_tt (X : atom) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | typ_top => typ_top
  | typ_bvar J => typ_bvar J
  | typ_fvar Y => if X == Y then U else typ_fvar Y
  | typ_arrow T1 T2 => typ_arrow (subst_tqt X U T1) (subst_tqt X U T2)
  | typ_all T1 T2 => typ_all (subst_tt X U T1) (subst_tqt X U T2)
  | typ_qall Q T => typ_qall Q (subst_tqt X U T)
  | typ_sum T1 T2 => typ_sum (subst_tqt X U T1) (subst_tqt X U T2)
  | typ_pair T1 T2 => typ_pair (subst_tqt X U T1) (subst_tqt X U T2)
  | typ_ref T1 => typ_ref (subst_tqt X U T1)
  end
with subst_tqt (X : atom) (U : typ) (T : qtyp) {struct T} : qtyp :=
  match T with
  | qtyp_qtyp Q T => qtyp_qtyp Q (subst_tt X U T)
  end.

Fixpoint subst_qq (X : atom) (R : qua) (Q : qua) {struct Q} : qua :=
  match Q with
  | qua_top => qua_top
  | qua_bot => qua_bot
  | qua_bvar J => qua_bvar J
  | qua_fvar Y => if X == Y then R else qua_fvar Y
  | qua_meet Q1 Q2 => qua_meet (subst_qq X R Q1) (subst_qq X R Q2)
  | qua_join Q1 Q2 => qua_join (subst_qq X R Q1) (subst_qq X R Q2)
  end.

Fixpoint subst_qt (X : atom) (R : qua) (T : typ) {struct T} : typ :=
  match T with
  | typ_top => typ_top
  | typ_bvar J => typ_bvar J
  | typ_fvar Y => typ_fvar Y
  | typ_arrow T1 T2 => typ_arrow (subst_qqt X R T1) (subst_qqt X R T2)
  | typ_all T1 T2 => typ_all (subst_qt X R T1) (subst_qqt X R T2)
  | typ_qall Q T => typ_qall (subst_qq X R Q) (subst_qqt X R T)
  | typ_sum T1 T2 => typ_sum (subst_qqt X R T1) (subst_qqt X R T2)
  | typ_pair T1 T2 => typ_pair (subst_qqt X R T1) (subst_qqt X R T2)
  | typ_ref T1 => typ_ref (subst_qqt X R T1)
  end
with subst_qqt (X : atom) (R : qua) (T : qtyp) {struct T} : qtyp :=
  match T with
  | qtyp_qtyp Q T => qtyp_qtyp (subst_qq X R Q) (subst_qt X R T)
  end.

Fixpoint subst_ee (x : atom) (v : exp) (e : exp) {struct e} : exp :=
  match e with
  | exp_bvar i => exp_bvar i
  | exp_fvar y => if x == y then v else exp_fvar y
  | exp_abs P V e1 => exp_abs P V (subst_ee x v e1)
  | exp_app e1 e2 => exp_app (subst_ee x v e1) (subst_ee x v e2)
  | exp_tabs P V e1 => exp_tabs P V (subst_ee x v e1)
  | exp_tapp e1 V => exp_tapp (subst_ee x v e1) V
  | exp_qabs P Q e1 => exp_qabs P Q (subst_ee x v e1)
  | exp_qapp e1 Q => exp_qapp (subst_ee x v e1) Q
  | exp_let e1 e2 => exp_let (subst_ee x v e1) (subst_ee x v e2)
  | exp_inl P e1 => exp_inl P (subst_ee x v e1)
  | exp_inr P e1 => exp_inr P (subst_ee x v e1)
  | exp_case e1 e2 e3 => exp_case (subst_ee x v e1) (subst_ee x v e2) (subst_ee x v e3)
  | exp_pair P e1 e2 => exp_pair P (subst_ee x v e1) (subst_ee x v e2)
  | exp_first e1 => exp_first (subst_ee x v e1)
  | exp_second e1 => exp_second (subst_ee x v e1)
  | exp_ref P e1 => exp_ref P (subst_ee x v e1)
  | exp_ref_label P l => exp_ref_label P l
  | exp_deref e1 => exp_deref (subst_ee x v e1)
  | exp_set_ref e1 e2 => exp_set_ref (subst_ee x v e1) (subst_ee x v e2)
  | exp_upqual P e1 => exp_upqual P (subst_ee x v e1)
  | exp_check P e1 => exp_check P (subst_ee x v e1)
  end.

Fixpoint subst_te (X : atom) (U : typ) (e : exp) {struct e} : exp :=
  match e with
  | exp_bvar i => exp_bvar i
  | exp_fvar y => exp_fvar y
  | exp_abs P V e1 => exp_abs P (subst_tqt X U V) (subst_te X U e1)
  | exp_app e1 e2 => exp_app (subst_te X U e1) (subst_te X U e2)
  | exp_tabs P V e1 => exp_tabs P (subst_tt X U V) (subst_te X U e1)
  | exp_tapp e1 V => exp_tapp (subst_te X U e1) (subst_tt X U V)
  | exp_qabs P Q e1 => exp_qabs P Q (subst_te X U e1)
  | exp_qapp e1 Q => exp_qapp (subst_te X U e1) Q
  | exp_let e1 e2 => exp_let (subst_te X U e1) (subst_te X U e2)
  | exp_inl P e1 => exp_inl P (subst_te X U e1)
  | exp_inr P e1 => exp_inr P (subst_te X U e1)
  | exp_case e1 e2 e3 => exp_case (subst_te X U e1) (subst_te X U e2) (subst_te X U e3)
  | exp_pair P e1 e2 => exp_pair P (subst_te X U e1) (subst_te X U e2)
  | exp_first e1 => exp_first (subst_te X U e1)
  | exp_second e1 => exp_second (subst_te X U e1)
  | exp_ref P e1 => exp_ref P (subst_te X U e1)
  | exp_ref_label P l => exp_ref_label P l
  | exp_deref e1 => exp_deref (subst_te X U e1)
  | exp_set_ref e1 e2 => exp_set_ref (subst_te X U e1) (subst_te X U e2)
  | exp_upqual P e1 => exp_upqual P (subst_te X U e1)
  | exp_check P e1 => exp_check P (subst_te X U e1)
  end.

Fixpoint subst_qe (X : atom) (R : qua) (e : exp) {struct e} : exp :=
  match e with
  | exp_bvar i => exp_bvar i
  | exp_fvar y => exp_fvar y
  | exp_abs P V e1 => exp_abs (subst_qq X R P) (subst_qqt X R V) (subst_qe X R e1)
  | exp_app e1 e2 => exp_app (subst_qe X R e1) (subst_qe X R e2)
  | exp_tabs P V e1 => exp_tabs (subst_qq X R P) (subst_qt X R V) (subst_qe X R e1)
  | exp_tapp e1 V => exp_tapp (subst_qe X R e1) (subst_qt X R V)
  | exp_qabs P Q e1 => exp_qabs (subst_qq X R P) (subst_qq X R Q) (subst_qe X R e1)
  | exp_qapp e1 Q => exp_qapp (subst_qe X R e1) (subst_qq X R Q)
  | exp_let e1 e2 => exp_let (subst_qe X R e1) (subst_qe X R e2)
  | exp_inl P e1 => exp_inl (subst_qq X R P) (subst_qe X R e1)
  | exp_inr P e1 => exp_inr (subst_qq X R P) (subst_qe X R e1)
  | exp_case e1 e2 e3 => exp_case (subst_qe X R e1) (subst_qe X R e2) (subst_qe X R e3)
  | exp_pair P e1 e2 => exp_pair (subst_qq X R P) (subst_qe X R e1) (subst_qe X R e2)
  | exp_first e1 => exp_first (subst_qe X R e1)
  | exp_second e1 => exp_second (subst_qe X R e1)
  | exp_ref P e1 => exp_ref (subst_qq X R P) (subst_qe X R e1)
  | exp_ref_label P l => exp_ref_label (subst_qq X R P) l
  | exp_deref e1 => exp_deref (subst_qe X R e1)
  | exp_set_ref e1 e2 => exp_set_ref (subst_qe X R e1) (subst_qe X R e2)
  | exp_upqual P e1 => exp_upqual (subst_qq X R P) (subst_qe X R e1)
  | exp_check P e1 => exp_check (subst_qq X R P) (subst_qe X R e1)
  end.

Definition subst_bind_te (X : atom) (U : typ) (b : binding) : binding :=
  match b with
  | bind_sub T => bind_sub (subst_tt X U T)
  | bind_typ T => bind_typ (subst_tqt X U T)
  | bind_qua Q => bind_qua Q
  end.

Definition subst_env_te (X : atom) (U : typ) (E : env) : env :=
  map (subst_bind_te X U) E.

Definition subst_bind_qe (X : atom) (R : qua) (b : binding) : binding :=
  match b with
  | bind_sub T => bind_sub (subst_qt X R T)
  | bind_typ T => bind_typ (subst_qqt X R T)
  | bind_qua Q => bind_qua (subst_qq X R Q)
  end.

Definition subst_env_qe (X : atom) (R : qua) (E : env) : env :=
  map (subst_bind_qe X R) E.

Scheme typ_mut_ind := Induction for typ Sort Prop
  with qtyp_mut_ind := Induction for qtyp Sort Prop.

Scheme wf_typ_mut_ind := Induction for wf_typ Sort Prop
  with wf_qtyp_mut_ind := Induction for wf_qtyp Sort Prop.

Scheme sub_mut_ind := Induction for sub Sort Prop
  with subqtype_mut_ind := Induction for subqtype Sort Prop.

(* ===================================================================== *)
(* Basic substitution lemmas                                             *)
(* ===================================================================== *)

#[global] Hint Rewrite eq_dec_refl : core.
#[global] Hint Extern 1 (_ `notin` _) => fsetdec : core.

Fixpoint subst_tt_nofv (X : atom) (U : typ) (T : typ) {struct T}
  : X `notin` fv_tt T -> subst_tt X U T = T
with subst_tqt_nofv (X : atom) (U : typ) (T : qtyp) {struct T}
  : X `notin` fv_tqt T -> subst_tqt X U T = T.
Proof.
  - intros H. destruct T; simpl in *; try reflexivity.
    + destruct (X == a) as [Heq|Hneq]; [subst; fsetdec | reflexivity].
    + f_equal; [apply subst_tqt_nofv | apply subst_tqt_nofv]; auto.
    + f_equal; [apply subst_tt_nofv | apply subst_tqt_nofv]; auto.
    + f_equal; apply subst_tqt_nofv; auto.
    + f_equal; [apply subst_tqt_nofv | apply subst_tqt_nofv]; auto.
    + f_equal; [apply subst_tqt_nofv | apply subst_tqt_nofv]; auto.
    + f_equal; apply subst_tqt_nofv; auto.
  - intros H. destruct T as [Q T]. simpl in *.
    f_equal; apply subst_tt_nofv; auto.
Defined.

Fixpoint subst_qq_nofv (X : atom) (R : qua) (Q : qua) {struct Q}
  : X `notin` fv_qq Q -> subst_qq X R Q = Q.
Proof.
  intros H. destruct Q; simpl in *; try reflexivity.
  - destruct (X == a) as [Heq|Hneq]; [subst; fsetdec | reflexivity].
  - f_equal; [apply subst_qq_nofv | apply subst_qq_nofv]; auto.
  - f_equal; [apply subst_qq_nofv | apply subst_qq_nofv]; auto.
Defined.

Fixpoint subst_qt_nofv (X : atom) (R : qua) (T : typ) {struct T}
  : X `notin` fv_tt T -> subst_qt X R T = T
with subst_qqt_nofv (X : atom) (R : qua) (T : qtyp) {struct T}
  : X `notin` fv_tqt T -> subst_qqt X R T = T.
Proof.
  - intros H. destruct T; simpl in *; try reflexivity.
    + f_equal; [apply subst_qqt_nofv | apply subst_qqt_nofv]; auto.
    + f_equal; [apply subst_qt_nofv | apply subst_qqt_nofv]; auto.
    + f_equal; [apply subst_qq_nofv | apply subst_qqt_nofv]; auto.
    + f_equal; [apply subst_qqt_nofv | apply subst_qqt_nofv]; auto.
    + f_equal; [apply subst_qqt_nofv | apply subst_qqt_nofv]; auto.
    + f_equal; apply subst_qqt_nofv; auto.
  - intros H. destruct T as [Q T]. simpl in *.
    f_equal; [apply subst_qq_nofv | apply subst_qt_nofv]; auto.
Defined.

Fixpoint subst_ee_nofv (x : atom) (v : exp) (e : exp) {struct e}
  : x `notin` fv_ee e -> subst_ee x v e = e.
Proof.
  intros H. destruct e; simpl in *; try reflexivity.
  - destruct (x == a) as [Heq|Hneq]; [subst; fsetdec | reflexivity].
  - f_equal; apply subst_ee_nofv; auto.                                     (* abs *)
  - f_equal; [apply subst_ee_nofv | apply subst_ee_nofv]; auto.             (* app *)
  - f_equal; apply subst_ee_nofv; auto.                                     (* tabs *)
  - f_equal; apply subst_ee_nofv; auto.                                     (* tapp *)
  - f_equal; apply subst_ee_nofv; auto.                                     (* qabs *)
  - f_equal; apply subst_ee_nofv; auto.                                     (* qapp *)
  - f_equal; [apply subst_ee_nofv | apply subst_ee_nofv]; auto.             (* let *)
  - f_equal; apply subst_ee_nofv; auto.                                     (* inl *)
  - f_equal; apply subst_ee_nofv; auto.                                     (* inr *)
  - f_equal; [apply subst_ee_nofv | apply subst_ee_nofv | apply subst_ee_nofv]; auto. (* case *)
  - f_equal; [apply subst_ee_nofv | apply subst_ee_nofv]; auto.             (* pair *)
  - f_equal; apply subst_ee_nofv; auto.                                     (* first *)
  - f_equal; apply subst_ee_nofv; auto.                                     (* second *)
  - f_equal; apply subst_ee_nofv; auto.                                     (* ref *)
  - f_equal; apply subst_ee_nofv; auto.                                     (* deref *)
  - f_equal; [apply subst_ee_nofv | apply subst_ee_nofv]; auto.             (* set_ref *)
  - f_equal; apply subst_ee_nofv; auto.                                     (* upqual *)
  - f_equal; apply subst_ee_nofv; auto.                                     (* check *)
Defined.

Fixpoint subst_te_nofv (X : atom) (U : typ) (e : exp) {struct e}
  : X `notin` fv_ee e -> subst_te X U e = e.
Proof.
  intros H. destruct e; simpl in *; try reflexivity.
  - f_equal; [apply subst_tqt_nofv | apply subst_te_nofv]; auto.            (* abs *)
  - f_equal; [apply subst_te_nofv | apply subst_te_nofv]; auto.             (* app *)
  - f_equal; [apply subst_tt_nofv | apply subst_te_nofv]; auto.             (* tabs *)
  - f_equal; [apply subst_te_nofv | apply subst_tt_nofv]; auto.             (* tapp *)
  - f_equal; apply subst_te_nofv; auto.                                     (* qabs *)
  - f_equal; apply subst_te_nofv; auto.                                     (* qapp *)
  - f_equal; [apply subst_te_nofv | apply subst_te_nofv]; auto.             (* let *)
  - f_equal; apply subst_te_nofv; auto.                                     (* inl *)
  - f_equal; apply subst_te_nofv; auto.                                     (* inr *)
  - f_equal; [apply subst_te_nofv | apply subst_te_nofv | apply subst_te_nofv]; auto. (* case *)
  - f_equal; [apply subst_te_nofv | apply subst_te_nofv]; auto.             (* pair *)
  - f_equal; apply subst_te_nofv; auto.                                     (* first *)
  - f_equal; apply subst_te_nofv; auto.                                     (* second *)
  - f_equal; apply subst_te_nofv; auto.                                     (* ref *)
  - f_equal; apply subst_te_nofv; auto.                                     (* deref *)
  - f_equal; [apply subst_te_nofv | apply subst_te_nofv]; auto.             (* set_ref *)
  - f_equal; apply subst_te_nofv; auto.                                     (* upqual *)
  - f_equal; apply subst_te_nofv; auto.                                     (* check *)
Defined.

Fixpoint subst_qe_nofv (X : atom) (R : qua) (e : exp) {struct e}
  : X `notin` fv_ee e -> subst_qe X R e = e.
Proof.
  intros H. destruct e; simpl in *; try reflexivity.
  - f_equal; [apply subst_qq_nofv | apply subst_qqt_nofv | apply subst_qe_nofv]; auto. (* abs *)
  - f_equal; [apply subst_qe_nofv | apply subst_qe_nofv]; auto.             (* app *)
  - f_equal; [apply subst_qq_nofv | apply subst_qt_nofv | apply subst_qe_nofv]; auto.  (* tabs *)
  - f_equal; [apply subst_qe_nofv | apply subst_qt_nofv]; auto.             (* tapp *)
  - f_equal; [apply subst_qq_nofv | apply subst_qq_nofv | apply subst_qe_nofv]; auto. (* qabs *)
  - f_equal; [apply subst_qe_nofv | apply subst_qq_nofv]; auto.             (* qapp *)
  - f_equal; [apply subst_qe_nofv | apply subst_qe_nofv]; auto.             (* let *)
  - f_equal; [apply subst_qq_nofv | apply subst_qe_nofv]; auto.             (* inl *)
  - f_equal; [apply subst_qq_nofv | apply subst_qe_nofv]; auto.             (* inr *)
  - f_equal; [apply subst_qe_nofv | apply subst_qe_nofv | apply subst_qe_nofv]; auto. (* case *)
  - f_equal; [apply subst_qq_nofv | apply subst_qe_nofv | apply subst_qe_nofv]; auto. (* pair *)
  - f_equal; apply subst_qe_nofv; auto.                                     (* first *)
  - f_equal; apply subst_qe_nofv; auto.                                     (* second *)
  - f_equal; [apply subst_qq_nofv | apply subst_qe_nofv]; auto.             (* ref *)
  - f_equal; apply subst_qq_nofv; auto.                                     (* ref_label *)
  - f_equal; apply subst_qe_nofv; auto.                                     (* deref *)
  - f_equal; [apply subst_qe_nofv | apply subst_qe_nofv]; auto.             (* set_ref *)
  - f_equal; [apply subst_qq_nofv | apply subst_qe_nofv]; auto.             (* upqual *)
  - f_equal; [apply subst_qq_nofv | apply subst_qe_nofv]; auto.             (* check *)
Defined.

#[global] Hint Resolve subst_tt_nofv subst_tqt_nofv subst_qq_nofv
  subst_qt_nofv subst_qqt_nofv subst_ee_nofv subst_te_nofv subst_qe_nofv : core.

(* ===================================================================== *)
(* Weakening                                                              *)
(* ===================================================================== *)

Lemma wf_env_uniq : forall E, wf_env E -> uniq E.
Proof.
  intros E H. induction H; simpl; eauto using uniq_nil, uniq_push.
Qed.

Lemma wf_env_cons_inv : forall (x : atom) (b : binding) (E : env),
  wf_env ((x,b) :: E) ->
  wf_env E /\ x `notin` dom E /\
  (match b with
   | bind_sub T => wf_typ E T
   | bind_typ T => wf_qtyp E T
   | bind_qua Q => wf_qua E Q
   end).
Proof.
  intros x b E H. destruct b; simpl in *.
  - inversion H; subst. repeat split; auto.
  - inversion H; subst. repeat split; auto.
  - inversion H; subst. repeat split; auto.
Qed.

(* ===================================================================== *)
(* Environment extension and weakening                                   *)
(* ===================================================================== *)

Definition env_extends (E E' : env) : Prop :=
  forall (x : atom) (b : binding), binds x b E -> binds x b E'.

Lemma env_extends_refl : forall E, env_extends E E.
Proof. intros E x b H. assumption. Qed.

Lemma env_extends_trans : forall E1 E2 E3,
  env_extends E1 E2 -> env_extends E2 E3 -> env_extends E1 E3.
Proof. intros E1 E2 E3 H12 H23 x b H. eauto. Qed.

Lemma env_extends_cons : forall E E' (x : atom) (b : binding),
  env_extends E E' -> env_extends ((x,b) :: E) ((x,b) :: E').
Proof.
  intros E E' x b H y c Hyc. simpl in *.
  destruct Hyc as [Heq|Hin].
  - left; assumption.
  - right; apply H; assumption.
Qed.

Lemma env_extends_insert : forall E1 E2 E3,
  env_extends E2 (E1 ++ E2 ++ E3).
Proof.
  intros E1 E2 E3 x b H.
  apply binds_app_3.
  apply binds_app_2.
  exact H.
Qed.

Lemma wf_qua_weaken : forall E E' Q,
  wf_env E' -> env_extends E E' -> wf_qua E Q -> wf_qua E' Q.
Proof.
  intros E E' Q Hwf Hext Hq.
  induction Hq as [E0|R E0 X Hb|E0 Q1 Q2 H1 IH1 H2 IH2|E0 Q1 Q2 H1 IH1 H2 IH2|E0].
  - apply wf_qua_top.
  - apply wf_qua_fvar with (R := R). apply Hext. exact Hb.
  - apply wf_qua_meet.
    + apply IH1. exact Hext.
    + apply IH2. exact Hext.
  - apply wf_qua_join.
    + apply IH1. exact Hext.
    + apply IH2. exact Hext.
  - apply wf_qua_bot.
Qed.

Lemma wf_typ_weaken : forall E E' T,
  wf_env E' -> env_extends E E' -> wf_typ E T -> wf_typ E' T.
Proof.
  intros E E' T Hwf Hext Hwt.
  revert E' Hwf Hext.
  induction Hwt using wf_typ_mut_ind
    with (P := fun E T w => forall E' : env, wf_env E' -> env_extends E E' -> wf_typ E' T)
         (P0 := fun E T w => forall E' : env, wf_env E' -> env_extends E E' -> wf_qtyp E' T).
  + intros E0 Hwf0 Hext0. apply wf_typ_top.
  + intros E0 Hwf0 Hext0. apply wf_typ_var with (U := U). apply Hext0. assumption.
  + intros E0 Hwf0 Hext0. apply wf_typ_arrow.
    * apply IHHwt; assumption.
    * apply IHHwt0; assumption.
  + intros E0 Hwf0 Hext0. apply wf_typ_all with (L := union L (dom E0)).
    * apply IHHwt; assumption.
    * intros X Hx.
      assert (HxL : X `notin` L) by fsetdec.
      assert (Hxd : X `notin` dom E0) by fsetdec.
      apply (H X HxL (X ~ bind_sub T1 ++ E0)).
      -- apply wf_env_sub with (X := X) (T := T1).
         ++ exact Hwf0.
         ++ apply IHHwt; assumption.
         ++ exact Hxd.
      -- apply env_extends_cons; assumption.
  + intros E0 Hwf0 Hext0. apply wf_typ_qall with (L := union L (dom E0)).
    * apply (wf_qua_weaken E E0 T1 Hwf0 Hext0 w).
    * intros X Hx.
      assert (HxL : X `notin` L) by fsetdec.
      assert (Hxd : X `notin` dom E0) by fsetdec.
      apply (H X HxL (X ~ bind_qua T1 ++ E0)).
      -- apply wf_env_qua with (X := X) (Q := T1).
         ++ exact Hwf0.
         ++ apply (wf_qua_weaken E E0 T1 Hwf0 Hext0 w).
         ++ exact Hxd.
      -- apply env_extends_cons; assumption.
  + intros E0 Hwf0 Hext0. apply wf_typ_sum.
    * apply IHHwt; assumption.
    * apply IHHwt0; assumption.
  + intros E0 Hwf0 Hext0. apply wf_typ_pair.
    * apply IHHwt; assumption.
    * apply IHHwt0; assumption.
  + intros E0 Hwf0 Hext0. apply wf_qtyp_qtyp.
    * apply (wf_qua_weaken E E0 Q Hwf0 Hext0 w).
    * apply IHHwt; assumption.
Qed.

Lemma wf_qtyp_weaken : forall E E' T,
  wf_env E' -> env_extends E E' -> wf_qtyp E T -> wf_qtyp E' T.
Proof.
  intros E E' T Hwf Hext Hwt. destruct T as [Q T]. inversion Hwt; subst.
  apply wf_qtyp_qtyp.
  - apply wf_qua_weaken with (E := E); assumption.
  - apply wf_typ_weaken with (E := E); assumption.
Qed.

Lemma env_extends_cons_tail : forall E (x : atom) (b : binding),
  env_extends E ((x,b) :: E).
Proof.
  intros E x b y c H. apply binds_cons_3. assumption.
Qed.

Lemma wf_binding_weaken : forall E E' (b : binding),
  wf_env E' -> env_extends E E' ->
  (match b with
   | bind_sub T => wf_typ E T
   | bind_typ T => wf_qtyp E T
   | bind_qua Q => wf_qua E Q
   end) ->
  (match b with
   | bind_sub T => wf_typ E' T
   | bind_typ T => wf_qtyp E' T
   | bind_qua Q => wf_qua E' Q
   end).
Proof.
  intros E E' b Hwf Hext. destruct b; simpl; intros H;
  [apply wf_typ_weaken with (E := E) | apply wf_qtyp_weaken with (E := E)
  | apply wf_qua_weaken with (E := E)]; assumption.
Qed.

Lemma wf_env_binds_wf : forall E, wf_env E -> forall (x : atom) (b : binding),
  binds x b E ->
  match b with
  | bind_sub T => wf_typ E T
  | bind_typ T => wf_qtyp E T
  | bind_qua Q => wf_qua E Q
  end.
Proof.
  intros E Hwf. induction Hwf; intros y b Hb.
  - destruct Hb.
  - simpl in Hb. destruct Hb as [Heq|Hin].
    + inversion Heq; subst. simpl.
      apply wf_typ_weaken with (E := E).
      * apply wf_env_sub; assumption.
      * apply env_extends_cons_tail.
      * assumption.
    + apply IHHwf in Hin. destruct b; simpl in *.
      * apply wf_typ_weaken with (E := E); auto.
        apply wf_env_sub; assumption.
        apply env_extends_cons_tail.
      * apply wf_qtyp_weaken with (E := E); auto.
        apply wf_env_sub; assumption.
        apply env_extends_cons_tail.
      * apply wf_qua_weaken with (E := E); auto.
        apply wf_env_sub; assumption.
        apply env_extends_cons_tail.
  - simpl in Hb. destruct Hb as [Heq|Hin].
    + inversion Heq; subst. simpl.
      apply wf_qtyp_weaken with (E := E).
      * apply wf_env_typ; assumption.
      * apply env_extends_cons_tail.
      * assumption.
    + apply IHHwf in Hin. destruct b; simpl in *.
      * apply wf_typ_weaken with (E := E); auto.
        apply wf_env_typ; assumption.
        apply env_extends_cons_tail.
      * apply wf_qtyp_weaken with (E := E); auto.
        apply wf_env_typ; assumption.
        apply env_extends_cons_tail.
      * apply wf_qua_weaken with (E := E); auto.
        apply wf_env_typ; assumption.
        apply env_extends_cons_tail.
  - simpl in Hb. destruct Hb as [Heq|Hin].
    + inversion Heq; subst. simpl.
      apply wf_qua_weaken with (E := E).
      * apply wf_env_qua; assumption.
      * apply env_extends_cons_tail.
      * assumption.
    + apply IHHwf in Hin. destruct b; simpl in *.
      * apply wf_typ_weaken with (E := E); auto.
        apply wf_env_qua; assumption.
        apply env_extends_cons_tail.
      * apply wf_qtyp_weaken with (E := E); auto.
        apply wf_env_qua; assumption.
        apply env_extends_cons_tail.
      * apply wf_qua_weaken with (E := E); auto.
        apply wf_env_qua; assumption.
        apply env_extends_cons_tail.
Qed.

(* ===================================================================== *)
(* Subqualifier facts                                                     *)
(* ===================================================================== *)

Lemma subqual_wf : forall E Q R,
  wf_env E -> subqual E Q R -> wf_qua E Q /\ wf_qua E R.
Proof.
  intros E Q R Hwf Hsq. induction Hsq.
  - split; [assumption | apply wf_qua_top].
  - split; [apply wf_qua_bot | assumption].
  - split; assumption.
  - destruct (IHHsq Hwf) as [HR HQ]. split.
    + eapply wf_qua_fvar. eassumption.
    + exact HQ.
  - destruct (IHHsq Hwf) as [HQ HR1]. split; [exact HQ | apply wf_qua_join; assumption].
  - destruct (IHHsq Hwf) as [HQ HR2]. split; [exact HQ | apply wf_qua_join; assumption].
  - destruct (IHHsq1 Hwf) as [HR1 HQ]. destruct (IHHsq2 Hwf) as [HR2 _].
    split; [apply wf_qua_join; assumption | exact HQ].
  - destruct (IHHsq Hwf) as [HR1 HQ]. split; [apply wf_qua_meet; assumption | exact HQ].
  - destruct (IHHsq Hwf) as [HR2 HQ]. split; [apply wf_qua_meet; assumption | exact HQ].
  - destruct (IHHsq1 Hwf) as [HQ HR1]. destruct (IHHsq2 Hwf) as [_ HR2].
    split; [exact HQ | apply wf_qua_meet; assumption].
Qed.


Lemma subqual_refl : forall E Q, wf_env E -> wf_qua E Q -> subqual E Q Q.
Proof.
  intros E Q Hwf Hq. induction Hq.
  - apply subqual_top; [assumption | apply wf_qua_top].
  - apply subqual_refl_qvar; [exact Hwf | apply wf_qua_fvar with (R := R); exact H].
  - apply subqual_meet_intro.
    + apply subqual_meet_eliml; [apply IHHq1; exact Hwf | exact Hq2].
    + apply subqual_meet_elimr; [exact Hq1 | apply IHHq2; exact Hwf].
  - apply subqual_join_elim.
    + apply subqual_join_inl; [apply IHHq1; exact Hwf | exact Hq2].
    + apply subqual_join_inr; [exact Hq1 | apply IHHq2; exact Hwf].
  - apply subqual_bot; [assumption | apply wf_qua_bot].
Qed.






Lemma subqual_bot_elim : forall E Q,
  wf_env E -> subqual E Q qua_bot ->
  forall S, wf_qua E S -> subqual E Q S.
Proof.
  intros E Q Hwf H1 S HS. dependent induction H1.
  - apply subqual_bot; assumption.
  - eapply subqual_trans_qvar; [exact H | apply (IHsubqual Hwf eq_refl S HS)].
  - apply subqual_join_elim;
      [apply (IHsubqual1 Hwf eq_refl S HS) | apply (IHsubqual2 Hwf eq_refl S HS)].
  - apply subqual_meet_eliml; [apply (IHsubqual Hwf eq_refl S HS) | exact H].
  - apply subqual_meet_elimr; [exact H | apply (IHsubqual Hwf eq_refl S HS)].
Qed.

Lemma subqual_fvar_elim : forall E Q X,
  wf_env E -> subqual E Q (qua_fvar X) ->
  forall R0, binds X (bind_qua R0) E ->
  forall S, subqual E R0 S -> subqual E Q S.
Proof.
  intros E Q X Hwf H1 R0 Hb S H2. dependent induction H1.
  - (* bot *) apply subqual_bot; [exact Hwf | ].
    apply (proj2 (subqual_wf E R0 S Hwf H2)).
  - (* refl *) eapply subqual_trans_qvar; [exact Hb | exact H2].
  - (* trans_qvar *)
    eapply subqual_trans_qvar; [exact H | ].
    apply (IHsubqual X Hwf eq_refl R0 Hb S H2).
  - (* join_elim *)
    apply subqual_join_elim;
      [apply (IHsubqual1 X Hwf eq_refl R0 Hb S H2)
      | apply (IHsubqual2 X Hwf eq_refl R0 Hb S H2)].
  - (* meet_eliml *)
    apply subqual_meet_eliml; [apply (IHsubqual X Hwf eq_refl R0 Hb S H2) | exact H].
  - (* meet_elimr *)
    apply subqual_meet_elimr; [exact H | apply (IHsubqual X Hwf eq_refl R0 Hb S H2)].
Qed.

(* ===================================================================== *)
(* Typing: well-formedness of environments and qualifiers                 *)
(* ===================================================================== *)

Lemma typing_wf_env : forall E Q e T,
  typing E Q e T -> wf_env E.
Proof.
  intros E Q e T H. induction H.
  - assumption.
  - pick fresh xx. assert (Hx : xx `notin` L) by fsetdec.
    exact (proj1 (wf_env_cons_inv xx (bind_typ V) E (H0 xx Hx))).
  - assumption.
  - pick fresh xx. assert (Hx : xx `notin` L) by fsetdec.
    exact (proj1 (wf_env_cons_inv xx (bind_sub V) E (H0 xx Hx))).
  - assumption.
  - pick fresh xx. assert (Hx : xx `notin` L) by fsetdec.
    exact (proj1 (wf_env_cons_inv xx (bind_qua Q) E (H1 xx Hx))).
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
Qed.

Lemma typing_wf_qua : forall E Q e T,
  wf_env E -> typing E Q e T -> wf_qua E Q.
Proof.
  intros E Q e T Hwf Ht. induction Ht;
    try (eauto using wf_qua_bot);
    try (apply (proj2 (subqual_wf E Q R Hwf H))).
Qed.


(* ===================================================================== *)
(* Structural (env-free) well-formedness predicates                      *)
(* ===================================================================== *)

Lemma wf_qua_qual : forall E Q, wf_qua E Q -> qual Q.
Proof. intros E Q H. induction H; eauto using qual_top, qual_fvar, qual_meet, qual_join, qual_bot. Qed.

Lemma wf_typ_type : forall E T, wf_typ E T -> type T
with wf_qtyp_qtype : forall E T, wf_qtyp E T -> qtype T.
Proof.
  - intros E T H. induction H using wf_typ_mut_ind
      with (P := fun E T w => type T) (P0 := fun E T w => qtype T).
    + apply type_top.
    + apply type_var.
    + apply type_arrow; assumption.
    + apply (type_all L T1 T2).
      exact IHwf_typ.
      intros X Hx. apply H0. assumption.
    + apply (type_qall L T1 T2).
      apply (wf_qua_qual E T1 w).
      intros X Hx. apply H. assumption.
    + apply type_sum; assumption.
    + apply type_pair; assumption.
    + apply qtype_qtyp.
      * apply (wf_qua_qual E Q w).
      * exact IHwf_typ.
  - intros E T H. destruct T as [Q T]. inversion H; subst.
    apply qtype_qtyp.
    + eapply wf_qua_qual. eassumption.
    + eapply wf_typ_type. eassumption.
Qed.

Lemma subqual_qual : forall E Q R, subqual E Q R -> qual Q /\ qual R.
Proof.
  intros E Q R H. induction H.
  - split; [eapply wf_qua_qual; eassumption | apply qual_top].
  - split; [apply qual_bot | eapply wf_qua_qual; eassumption].
  - split; apply qual_fvar.
  - destruct IHsubqual as [_ HQ]. split; [apply qual_fvar | exact HQ].
  - destruct IHsubqual as [HQ HR1]. split;
      [exact HQ | apply qual_join; [exact HR1 | eapply wf_qua_qual; eassumption]].
  - destruct IHsubqual as [HQ HR2]. split;
      [exact HQ | apply qual_join; [eapply wf_qua_qual; eassumption | exact HR2]].
  - destruct IHsubqual1 as [HR1 HQ]. destruct IHsubqual2 as [HR2 _].
    split; [apply qual_join; assumption | exact HQ].
  - destruct IHsubqual as [HR1 HQ]. split;
      [apply qual_meet; [exact HR1 | eapply wf_qua_qual; eassumption] | exact HQ].
  - destruct IHsubqual as [HR2 HQ]. split;
      [apply qual_meet; [eapply wf_qua_qual; eassumption | exact HR2] | exact HQ].
  - destruct IHsubqual1 as [HQ HR1]. destruct IHsubqual2 as [_ HR2].
    split; [exact HQ | apply qual_meet; assumption].
Qed.


Lemma sub_type : forall E S T, sub E S T -> type S /\ type T.
Proof.
  intros E S T H. induction H using sub_mut_ind
    with (P := fun E S T w => type S /\ type T)
         (P0 := fun E S T w => qtype S /\ qtype T).
  - split; [apply (wf_typ_type E S w0) | apply type_top].
  - split; apply type_var.
  - split; [apply type_var | exact (proj2 IHsub)].
  - destruct IHsub as [HT1 HS1]. destruct IHsub0 as [HS2 HT2]. split.
    + apply type_arrow; assumption.
    + apply type_arrow; assumption.
  - destruct IHsub as [HT1 HS1]. split.
    + apply (type_all L S1 S2).
      * exact HS1.
      * intros X Hx. exact (proj1 (H0 X Hx)).
    + apply (type_all L T1 T2).
      * exact HT1.
      * intros X Hx. exact (proj2 (H0 X Hx)).
  - split.
    + apply (type_qall L S1 S2).
      * apply subqual_qual in s. exact (proj2 s).
      * intros X Hx. exact (proj1 (H X Hx)).
    + apply (type_qall L T1 T2).
      * apply subqual_qual in s. exact (proj1 s).
      * intros X Hx. exact (proj2 (H X Hx)).
  - destruct IHsub as [HS1 HT1]. destruct IHsub0 as [HS2 HT2]. split.
    + apply type_sum; assumption.
    + apply type_sum; assumption.
  - destruct IHsub as [HS1 HT1]. destruct IHsub0 as [HS2 HT2]. split.
    + apply type_pair; assumption.
    + apply type_pair; assumption.
  - split.
    + apply qtype_qtyp.
      * apply subqual_qual in s. exact (proj1 s).
      * exact (proj1 IHsub).
    + apply qtype_qtyp.
      * apply subqual_qual in s. exact (proj2 s).
      * exact (proj2 IHsub).
Qed.

Lemma subqtype_type : forall E S T, subqtype E S T -> qtype S /\ qtype T.
Proof.
  intros E S T H. destruct S as [Q1 T1]. destruct T as [Q2 T2].
  inversion H; subst. split.
  - apply qtype_qtyp.
    + apply subqual_qual in H4. exact (proj1 H4).
    + apply (proj1 (sub_type E T1 T2 H6)).
  - apply qtype_qtyp.
    + apply subqual_qual in H4. exact (proj2 H4).
    + apply (proj2 (sub_type E T1 T2 H6)).
Qed.



(* ===================================================================== *)
(* Typing implies expression well-formedness                             *)
(* ===================================================================== *)

Lemma typing_expr : forall E Q e T,
  typing E Q e T -> expr e.
Proof.
  intros E Q e T H. induction H.
  - apply expr_var.
  - (* abs *) pick fresh xx. assert (Hx : xx `notin` L) by fsetdec.
    pose proof (typing_wf_env _ _ _ _ (H xx Hx)) as Hwfext.
    destruct (wf_env_cons_inv xx (bind_typ V) E Hwfext) as [HE [Hdom HV]].
    pose proof (typing_wf_qua (xx ~ bind_typ V ++ E) P (open_ee e1 xx) T1 Hwfext (H xx Hx)) as HP.
    apply expr_abs with (L := L).
    + apply (wf_qua_qual _ _ HP).
    + apply (wf_qtyp_qtype _ _ HV).
    + apply (wf_qua_qual _ _ HP).
    + intros x Hxn. apply H0. assumption.
  - apply expr_app; assumption.
  - (* tabs *) pick fresh xx. assert (Hx : xx `notin` L) by fsetdec.
    pose proof (typing_wf_env _ _ _ _ (H xx Hx)) as Hwfext.
    destruct (wf_env_cons_inv xx (bind_sub V) E Hwfext) as [HE [Hdom HV]].
    pose proof (typing_wf_qua (xx ~ bind_sub V ++ E) P (open_te e1 xx) (open_tqt T1 xx) Hwfext (H xx Hx)) as HP.
    apply expr_tabs with (L := L).
    + apply (wf_qua_qual _ _ HP).
    + apply (wf_typ_type _ _ HV).
    + intros X Hxn. apply H0. assumption.
  - (* tapp *) apply expr_tapp.
    + assumption.
    + apply (proj1 (sub_type E T T1 H0)).
  - (* qabs *) pick fresh xx. assert (Hx : xx `notin` L) by fsetdec.
    pose proof (typing_wf_env _ _ _ _ (H0 xx Hx)) as Hwfext.
    destruct (wf_env_cons_inv xx (bind_qua Q) E Hwfext) as [HE [Hdom HQ]].
    apply expr_qabs with (L := L).
    + apply (wf_qua_qual _ _ H).
    + apply (wf_qua_qual _ _ HQ).
    + intros X Hxn. apply H1. assumption.
  - (* qapp *) apply expr_qapp.
    + assumption.
    + apply (wf_qua_qual _ _ (typing_wf_qua E Q e1 _ (typing_wf_env _ _ _ _ H) H)).
  - (* sub *) apply IHtyping.
  - (* subqual *) apply IHtyping.
  - (* let *) apply expr_let with (L := L).
    + assumption.
    + intros x Hxn. apply H1. assumption.
  - (* inl *) apply expr_inl.
    + apply (wf_qua_qual _ _ H).
    + assumption.
  - (* inr *) apply expr_inr.
    + apply (wf_qua_qual _ _ H).
    + assumption.
  - (* case *) apply expr_case with (L := L).
    + assumption.
    + intros x Hxn. apply H1. assumption.
    + intros x Hxn. apply H3. assumption.
  - (* pair *) apply expr_pair.
    + apply (wf_qua_qual _ _ H).
    + assumption.
    + assumption.
  - apply expr_first; assumption.
  - apply expr_second; assumption.
  - (* upqual *) apply expr_upqual.
    + apply subqual_qual in H0. exact (proj2 H0).
    + assumption.
  - (* check *) apply expr_check.
    + apply subqual_qual in H0. exact (proj2 H0).
    + assumption.
Qed.

(* ===================================================================== *)
(* Concrete qualifiers                                                   *)
(* ===================================================================== *)

Lemma wf_qua_empty_concretize : forall Q,
  wf_qua empty Q -> exists c, concretize Q = Some c.
Proof.
  intros Q H. remember empty as E eqn:EE. induction H.
  - exists cqua_top. reflexivity.
  - subst E. destruct H.
  - destruct (IHwf_qua1 EE) as [c1 H1]. destruct (IHwf_qua2 EE) as [c2 H2].
    simpl. rewrite H1. destruct c1; simpl.
    + exists c2. exact H2.
    + exists cqua_bot. reflexivity.
  - destruct (IHwf_qua1 EE) as [c1 H1]. destruct (IHwf_qua2 EE) as [c2 H2].
    simpl. rewrite H1. destruct c1; simpl.
    + exists cqua_top. reflexivity.
    + exists c2. exact H2.
  - exists cqua_bot. reflexivity.
Qed.


Lemma concretize_abstractize : forall s, concretize (abstractize s) = Some s.
Proof. intros []; reflexivity. Qed.

Lemma cqua_compatible_refl : forall s, cqua_compatible s s.
Proof. intros s. destruct s; constructor. Qed.

Lemma cqua_compatible_trans : forall s t u,
  cqua_compatible s t -> cqua_compatible t u -> cqua_compatible s u.
Proof.
  intros s t u H1 H2. destruct s; destruct t; destruct u; simpl in *.
  - constructor.
  - inversion H2.
  - inversion H1.
  - inversion H1.
  - constructor.
  - inversion H2.
  - constructor.
  - constructor.
Qed.



Lemma subqual_abstractize : forall E s t,
  wf_env E -> cqua_compatible s t -> subqual E (abstractize s) (abstractize t).
Proof.
  intros E s t Hwf H. destruct H.
  - destruct s.
    + apply subqual_top; [exact Hwf | apply wf_qua_top].
    + apply subqual_bot; [exact Hwf | apply wf_qua_bot].
  - (* bot <= top *) apply subqual_bot; [exact Hwf | apply wf_qua_top].
Qed.

Lemma wf_qua_concretize_subqual : forall E Q c,
  wf_env E -> wf_qua E Q -> concretize Q = Some c -> subqual E (abstractize c) Q.
Proof.
  intros E Q c Hwf HQ Hc. revert c Hc.
  induction HQ; intros c Hc; simpl in Hc.
  - inversion Hc; subst. apply subqual_top; [exact Hwf | apply wf_qua_top].
  - discriminate Hc.
  - destruct (concretize Q1) as [c1|] eqn:E1; try discriminate.
    destruct c1; simpl in Hc.
    + destruct (concretize Q2) as [c2|] eqn:E2; try discriminate.
      inversion Hc; subst c.
      apply subqual_meet_intro.
      * destruct c2; simpl.
        -- apply (IHHQ1 Hwf cqua_top eq_refl).
        -- apply subqual_bot; [exact Hwf | exact HQ1].
      * apply (IHHQ2 Hwf c2 eq_refl).
    + inversion Hc; subst c.
      apply subqual_bot; [exact Hwf | apply wf_qua_meet; assumption].
  - destruct (concretize Q1) as [c1|] eqn:E1; try discriminate.
    destruct c1; simpl in Hc.
    + inversion Hc; subst c.
      apply subqual_join_inl.
      * apply (IHHQ1 Hwf cqua_top eq_refl).
      * exact HQ2.
    + destruct (concretize Q2) as [c2|] eqn:E2; try discriminate.
      inversion Hc; subst c.
      apply subqual_join_inr.
      * exact HQ1.
      * apply (IHHQ2 Hwf c2 eq_refl).
  - inversion Hc; subst. apply subqual_bot; [exact Hwf | apply wf_qua_bot].
Qed.




(* ===================================================================== *)
(* Typing contexts: basic well-formedness                                *)
(* ===================================================================== *)

Lemma typing_ctx_wf_env : forall E Q c T,
  typing_ctx E Q c T -> wf_env E.
Proof.
  intros E Q c T H. induction H; try assumption;
    try (eapply typing_wf_env; eassumption).
Qed.

Lemma typing_ctx_wf_qua : forall E Q c T,
  wf_env E -> typing_ctx E Q c T -> wf_qua E Q.
Proof.
  intros E Q c T Hwf H. induction H.
  all: try assumption.
  all: try (apply (IHtyping_ctx Hwf)).
  - (* barrier *) destruct t.
    + apply wf_qua_top.
    + apply wf_qua_bot.
  - (* subqual *) apply (proj1 (subqual_wf E R Q Hwf H0)).
Qed.




(* ===================================================================== *)
(* Environment kind-equivalence and wf invariance                        *)
(* ===================================================================== *)

Definition kind_of (b : binding) : nat :=
  match b with
  | bind_sub _ => 0
  | bind_typ _ => 1
  | bind_qua _ => 2
  end.

Definition env_kind_eq (E E' : env) : Prop :=
  (forall x b, binds x b E -> exists b', binds x b' E' /\ kind_of b' = kind_of b) /\
  (forall x b, binds x b E' -> exists b0, binds x b0 E /\ kind_of b0 = kind_of b).

Lemma env_kind_eq_cons : forall E E' x b b',
  env_kind_eq E E' -> kind_of b = kind_of b' ->
  env_kind_eq ((x,b) :: E) ((x,b') :: E').
Proof.
  intros E E' x b b' [H1 H2] Kb. split.
  - intros y c Hyc. simpl in Hyc. destruct Hyc as [Heq|Hin].
    + inversion Heq; subst. exists b'. split; [left; reflexivity | symmetry; assumption].
    + destruct (H1 y c Hin) as [c' [Hin' Kc]].
      exists c'. split; [right; assumption | assumption].
  - intros y c Hyc. simpl in Hyc. destruct Hyc as [Heq|Hin].
    + inversion Heq; subst. exists b. split; [left; reflexivity | assumption].
    + destruct (H2 y c Hin) as [c' [Hin' Kc]].
      exists c'. split; [right; assumption | assumption].
Qed.

Lemma wf_qua_kind_eq : forall E Q,
  wf_qua E Q -> forall E', env_kind_eq E E' -> wf_qua E' Q.
Proof.
  intros E Q H. induction H; intros E' Hk.
  - apply wf_qua_top.
  - destruct Hk as [H1 H2]. destruct (H1 X (bind_qua R) H) as [b' [Hb' Kb]].
    destruct b'; simpl in Kb; try discriminate.
    apply wf_qua_fvar with (R := q). exact Hb'.
  - apply wf_qua_meet; [apply IHwf_qua1 | apply IHwf_qua2]; exact Hk.
  - apply wf_qua_join; [apply IHwf_qua1 | apply IHwf_qua2]; exact Hk.
  - apply wf_qua_bot.
Qed.

Lemma wf_typ_kind_eq : forall E T,
  wf_typ E T -> forall E', env_kind_eq E E' -> wf_typ E' T.
Proof.
  intros E T H. induction H using wf_typ_mut_ind
    with (P := fun E T w => forall E', env_kind_eq E E' -> wf_typ E' T)
         (P0 := fun E T w => forall E', env_kind_eq E E' -> wf_qtyp E' T).
  - intros E' Hk. apply wf_typ_top.
  - intros E' Hk.
    destruct Hk as [H1 H2]. destruct (H1 X (bind_sub U) b) as [b' [Hb' Kb]].
    destruct b'; simpl in Kb; try discriminate.
    apply wf_typ_var with (U := t). exact Hb'.
  - intros E' Hk. apply wf_typ_arrow.
    + apply IHwf_typ; assumption.
    + apply IHwf_typ0; assumption.
  - intros E' Hk. apply wf_typ_all with (L := L).
    + apply IHwf_typ; assumption.
    + intros X Hx. apply (H0 X Hx (X ~ bind_sub T1 ++ E')).
      apply env_kind_eq_cons; [assumption | reflexivity].
  - intros E' Hk. apply wf_typ_qall with (L := L).
    + apply (wf_qua_kind_eq E T1 w E' Hk).
    + intros X Hx. apply (H X Hx (X ~ bind_qua T1 ++ E')).
      apply env_kind_eq_cons; [assumption | reflexivity].
  - intros E' Hk. apply wf_typ_sum.
    + apply IHwf_typ; assumption.
    + apply IHwf_typ0; assumption.
  - intros E' Hk. apply wf_typ_pair.
    + apply IHwf_typ; assumption.
    + apply IHwf_typ0; assumption.
  - intros E' Hk. apply wf_qtyp_qtyp.
    + apply (wf_qua_kind_eq E Q w E' Hk).
    + apply IHwf_typ; assumption.
Qed.

Lemma wf_qtyp_kind_eq : forall E T,
  wf_qtyp E T -> forall E', env_kind_eq E E' -> wf_qtyp E' T.
Proof.
  intros E T H E' Hk. destruct T as [Q T]. inversion H; subst.
  apply wf_qtyp_qtyp.
  - eapply wf_qua_kind_eq; [eassumption | exact Hk].
  - eapply wf_typ_kind_eq; [eassumption | exact Hk].
Qed.


Lemma env_kind_eq_refl : forall E, env_kind_eq E E.
Proof.
  intros E. split.
  - intros x b Hb. exists b. split; [assumption | reflexivity].
  - intros x b Hb. exists b. split; [assumption | reflexivity].
Qed.

Lemma sub_wf : forall E S T, wf_env E -> sub E S T -> wf_typ E S /\ wf_typ E T
with subqtype_wf : forall E S T, wf_env E -> subqtype E S T -> wf_qtyp E S /\ wf_qtyp E T.
Proof.
  - intros E S T Hwf H. induction H using sub_mut_ind
      with (P := fun E S T w => wf_env E -> wf_typ E S /\ wf_typ E T)
           (P0 := fun E S T w => wf_env E -> wf_qtyp E S /\ wf_qtyp E T).
    + split; [exact w0 | apply wf_typ_top].
    + split; assumption.
    + split.
      * apply wf_typ_var with (U := U). exact b.
      * exact (proj2 (IHsub Hwf)).
    + split.
      * apply wf_typ_arrow.
        -- apply IHsub; exact Hwf.
        -- apply IHsub0; exact Hwf.
      * apply wf_typ_arrow.
        -- apply IHsub; exact Hwf.
        -- apply IHsub0; exact Hwf.
    + destruct (IHsub Hwf) as [Hwt1 Hws1]. split.
      * apply wf_typ_all with (L := union L (dom E)).
        -- exact Hws1.
        -- intros X Hx.
           assert (HxL : X `notin` L) by fsetdec.
           assert (Hxd : X `notin` dom E) by fsetdec.
           assert (Hwfext : wf_env (X ~ bind_sub T1 ++ E)).
           { apply wf_env_sub; assumption. }
           pose proof (H0 X HxL Hwfext) as [Hs2 Ht2].
           assert (Hk : env_kind_eq (X ~ bind_sub T1 ++ E) (X ~ bind_sub S1 ++ E)).
           { apply env_kind_eq_cons; [apply env_kind_eq_refl | reflexivity]. }
           exact (wf_qtyp_kind_eq _ _ Hs2 _ Hk).
      * apply wf_typ_all with (L := union L (dom E)).
        -- exact Hwt1.
        -- intros X Hx.
           assert (HxL : X `notin` L) by fsetdec.
           assert (Hxd : X `notin` dom E) by fsetdec.
           assert (Hwfext : wf_env (X ~ bind_sub T1 ++ E)).
           { apply wf_env_sub; assumption. }
           destruct (H0 X HxL Hwfext) as [Hs2 Ht2].
           exact Ht2.
    + split.
      * apply wf_typ_qall with (L := union L (dom E)).
        -- apply (proj2 (subqual_wf E T1 S1 Hwf s)).
        -- intros X Hx.
           assert (HxL : X `notin` L) by fsetdec.
           assert (Hxd : X `notin` dom E) by fsetdec.
           assert (Hwfext : wf_env (X ~ bind_qua T1 ++ E)).
           { apply wf_env_qua; [assumption | apply (proj1 (subqual_wf E T1 S1 Hwf s)) | assumption]. }
           destruct (H X HxL Hwfext) as [Hs2 Ht2].
           assert (Hk : env_kind_eq (X ~ bind_qua T1 ++ E) (X ~ bind_qua S1 ++ E)).
           { apply env_kind_eq_cons; [apply env_kind_eq_refl | reflexivity]. }
           exact (wf_qtyp_kind_eq _ _ Hs2 _ Hk).
      * apply wf_typ_qall with (L := union L (dom E)).
        -- apply (proj1 (subqual_wf E T1 S1 Hwf s)).
        -- intros X Hx.
           assert (HxL : X `notin` L) by fsetdec.
           assert (Hxd : X `notin` dom E) by fsetdec.
           assert (Hwfext : wf_env (X ~ bind_qua T1 ++ E)).
           { apply wf_env_qua; [assumption | apply (proj1 (subqual_wf E T1 S1 Hwf s)) | assumption]. }
           destruct (H X HxL Hwfext) as [Hs2 Ht2].
           exact Ht2.
    + split.
      * apply wf_typ_sum.
        -- apply IHsub; exact Hwf.
        -- apply IHsub0; exact Hwf.
      * apply wf_typ_sum.
        -- apply IHsub; exact Hwf.
        -- apply IHsub0; exact Hwf.
    + split.
      * apply wf_typ_pair.
        -- apply IHsub; exact Hwf.
        -- apply IHsub0; exact Hwf.
      * apply wf_typ_pair.
        -- apply IHsub; exact Hwf.
        -- apply IHsub0; exact Hwf.
    + split.
      * apply wf_qtyp_qtyp.
        -- apply (proj1 (subqual_wf E Q1 Q2 Hwf s)).
        -- exact (proj1 (IHsub Hwf)).
      * apply wf_qtyp_qtyp.
        -- apply (proj2 (subqual_wf E Q1 Q2 Hwf s)).
        -- exact (proj2 (IHsub Hwf)).
  - intros E S T Hwf H. inversion H; subst. split.
    + apply wf_qtyp_qtyp.
      * match goal with
        | Hs : subqual ?E ?Q1 ?Q2 |- wf_qua ?E ?Q1 =>
            exact (proj1 (subqual_wf E Q1 Q2 Hwf Hs))
        end.
      * match goal with
        | Hs : sub ?E ?T1 ?T2 |- wf_typ ?E ?T1 =>
            exact (proj1 (sub_wf E T1 T2 Hwf Hs))
        end.
    + apply wf_qtyp_qtyp.
      * match goal with
        | Hs : subqual ?E ?Q1 ?Q2 |- wf_qua ?E ?Q2 =>
            exact (proj2 (subqual_wf E Q1 Q2 Hwf Hs))
        end.
      * match goal with
        | Hs : sub ?E ?T1 ?T2 |- wf_typ ?E ?T2 =>
            exact (proj2 (sub_wf E T1 T2 Hwf Hs))
        end.
Qed.

(* ===================================================================== *)
(* Weakening for subtyping and qualifier ordering                        *)
(* ===================================================================== *)

Lemma env_extends_dom : forall E E' (X : atom),
  env_extends E E' -> X `in` dom E -> X `in` dom E'.
Proof.
  intros E E' X Hext Hx. destruct (binds_In_inv binding X E Hx) as [b Hb].
  apply binds_In with (a := b). apply Hext. assumption.
Qed.

Lemma env_extends_dom_notin : forall E E' (X : atom),
  env_extends E E' -> X `notin` dom E' -> X `notin` dom E.
Proof.
  intros E E' X Hext Hx Hxe. apply Hx. apply env_extends_dom with (E := E); assumption.
Qed.

Lemma subqual_weaken : forall E Q R,
  subqual E Q R -> forall E', wf_env E' -> env_extends E E' -> subqual E' Q R.
Proof.
  intros E Q R H. induction H; intros E' Hwf' Hext'.
  - apply subqual_top; [exact Hwf' | apply wf_qua_weaken with (E := E); assumption].
  - apply subqual_bot; [exact Hwf' | apply wf_qua_weaken with (E := E); assumption].
  - apply subqual_refl_qvar; [exact Hwf' | apply wf_qua_weaken with (E := E); assumption].
  - eapply subqual_trans_qvar; [apply Hext'; eassumption | ].
    apply IHsubqual; assumption.
  - apply subqual_join_inl.
    + apply IHsubqual; assumption.
    + apply wf_qua_weaken with (E := E); assumption.
  - apply subqual_join_inr.
    + apply wf_qua_weaken with (E := E); assumption.
    + apply IHsubqual; assumption.
  - apply subqual_join_elim; [apply IHsubqual1|apply IHsubqual2]; assumption.
  - apply subqual_meet_eliml.
    + apply IHsubqual; assumption.
    + apply wf_qua_weaken with (E := E); assumption.
  - apply subqual_meet_elimr.
    + apply wf_qua_weaken with (E := E); assumption.
    + apply IHsubqual; assumption.
  - apply subqual_meet_intro; [apply IHsubqual1|apply IHsubqual2]; assumption.
Qed.

Lemma sub_weaken : forall E S T,
  wf_env E -> sub E S T -> forall E', wf_env E' -> env_extends E E' -> sub E' S T.
Proof.
  intros E S T HwfE H. revert HwfE. induction H using sub_mut_ind
    with (P := fun E S T w => wf_env E -> forall E', wf_env E' -> env_extends E E' -> sub E' S T)
         (P0 := fun E S T w => wf_env E -> forall E', wf_env E' -> env_extends E E' -> subqtype E' S T).
  - intros Hwf0 E' Hwf' Hext'. apply sub_top.
    + exact Hwf'.
    + apply wf_typ_weaken with (E := E); assumption.
  - intros Hwf0 E' Hwf' Hext'. apply sub_refl_tvar.
    + exact Hwf'.
    + apply wf_typ_weaken with (E := E); assumption.
  - intros Hwf0 E' Hwf' Hext'. eapply sub_trans_tvar.
    + apply Hext'. eassumption.
    + apply IHsub; assumption.
  - intros Hwf0 E' Hwf' Hext'. apply sub_arrow.
    + apply IHsub; assumption.
    + apply IHsub0; assumption.
  - intros Hwf0 E' Hwf' Hext'. apply sub_all with (L := union L (dom E')).
    + apply IHsub; assumption.
    + intros X Hx.
      assert (HxL : X `notin` L) by fsetdec.
      assert (Hxd : X `notin` dom E') by fsetdec.
      assert (HxdE : X `notin` dom E).
      { apply (env_extends_dom_notin E E' X Hext' Hxd). }
      assert (Hwt1 : wf_typ E T1).
      { apply (proj1 (sub_wf E T1 S1 Hwf0 H)). }
      assert (Hwt1' : wf_typ E' T1).
      { apply (proj1 (sub_wf E' T1 S1 Hwf' (IHsub Hwf0 E' Hwf' Hext'))). }
      assert (Hwfext : wf_env (X ~ bind_sub T1 ++ E)).
      { apply wf_env_sub; [exact Hwf0 | exact Hwt1 | exact HxdE]. }
      apply (H0 X HxL Hwfext (X ~ bind_sub T1 ++ E')).
      * apply wf_env_sub; [exact Hwf' | exact Hwt1' | exact Hxd].
      * apply env_extends_cons; assumption.
  - intros Hwf0 E' Hwf' Hext'. apply sub_qall with (L := union L (dom E')).
    + apply subqual_weaken with (E := E); assumption.
    + intros X Hx.
      assert (HxL : X `notin` L) by fsetdec.
      assert (Hxd : X `notin` dom E') by fsetdec.
      assert (HxdE : X `notin` dom E).
      { apply (env_extends_dom_notin E E' X Hext' Hxd). }
      assert (Hwq : wf_qua E T1).
      { apply (proj1 (subqual_wf E T1 S1 Hwf0 s)). }
      assert (Hwq' : wf_qua E' T1).
      { apply (wf_qua_weaken E E' T1 Hwf' Hext' Hwq). }
      assert (Hwfext : wf_env (X ~ bind_qua T1 ++ E)).
      { apply wf_env_qua; [exact Hwf0 | exact Hwq | exact HxdE]. }
      apply (H X HxL Hwfext (X ~ bind_qua T1 ++ E')).
      * apply wf_env_qua; [exact Hwf' | exact Hwq' | exact Hxd].
      * apply env_extends_cons; assumption.
  - intros Hwf0 E' Hwf' Hext'. apply sub_sum; [apply IHsub|apply IHsub0]; assumption.
  - intros Hwf0 E' Hwf' Hext'. apply sub_pair; [apply IHsub|apply IHsub0]; assumption.
  - intros Hwf0 E' Hwf' Hext'. apply sub_qtyp_qtyp.
    + apply subqual_weaken with (E := E); assumption.
    + apply IHsub; assumption.
Qed.

Lemma subqtype_weaken : forall E S T,
  wf_env E -> subqtype E S T -> forall E', wf_env E' -> env_extends E E' -> subqtype E' S T.
Proof.
  intros E S T HwfE H E' Hwf' Hext'. inversion H; subst.
  apply sub_qtyp_qtyp.
  - apply subqual_weaken with (E := E); [eassumption | exact Hwf' | exact Hext'].
  - apply sub_weaken with (E := E); [exact HwfE | eassumption | exact Hwf' | exact Hext'].
Qed.


(* ===================================================================== *)
(* Environment morphisms ignoring term-variable bindings                 *)
(* ===================================================================== *)

Definition env_subqua_extends (E E' : env) : Prop :=
  (forall (X : atom) (U : typ), binds X (bind_sub U) E -> binds X (bind_sub U) E') /\
  (forall (X : atom) (Q : qua), binds X (bind_qua Q) E -> binds X (bind_qua Q) E').

Lemma env_subqua_extends_cons : forall E E' (y : atom) (b : binding),
  env_subqua_extends E E' ->
  env_subqua_extends (y ~ b ++ E) (y ~ b ++ E').
Proof.
  intros E E' y b [H1 H2]. simpl. split.
  - intros X U HX. apply (binds_cons_1 binding X y (bind_sub U) b E) in HX. destruct HX as [[Heq Hbeq]|Hin].
    + subst X. subst b. unfold binds. simpl. left. reflexivity.
    + unfold binds. simpl. right. apply H1; assumption.
  - intros X Q HX. apply (binds_cons_1 binding X y (bind_qua Q) b E) in HX. destruct HX as [[Heq Hbeq]|Hin].
    + subst X. subst b. unfold binds. simpl. left. reflexivity.
    + unfold binds. simpl. right. apply H2; assumption.
Qed.

Lemma binds_mid_remove : forall (E1 E2 : env) (x : atom) (V : qtyp)
  (y : atom) (b : binding),
  binds y b (E1 ++ x ~ bind_typ V ++ E2) -> y <> x -> binds y b (E1 ++ E2).
Proof.
  intros E1. induction E1 as [| p E1 IH]; intros E2 x V y b Hb Hne.
  - simpl in Hb. apply (binds_cons_1 binding y x b (bind_typ V) E2) in Hb.
    destruct Hb as [[Heq Hbeq]|Hin].
    + subst y. exfalso; apply Hne; reflexivity.
    + assumption.
  - destruct p as [z c]. simpl in Hb.
    apply (binds_cons_1 binding y z b c (E1 ++ x ~ bind_typ V ++ E2)) in Hb.
    destruct Hb as [[Heq Hbeq]|Hin].
    + unfold binds. left. subst y. subst b. reflexivity.
    + unfold binds. right. apply (IH E2 x V y b); assumption.
Qed.


Lemma env_subqua_extends_mid : forall (E1 E2 : env) (x : atom) (V : qtyp),
  wf_env (E1 ++ x ~ bind_typ V ++ E2) ->
  env_subqua_extends (E1 ++ x ~ bind_typ V ++ E2) (E1 ++ E2).
Proof.
  intros E1 E2 x V Hwf. split.
  - intros X U HX.
    destruct (eq_dec X x) as [->|Hne].
    + exfalso. pose proof (wf_env_uniq _ Hwf) as Hu.
      assert (Hb1 : binds x (bind_sub U) (E1 ++ x ~ bind_typ V ++ E2)) by assumption.
      assert (Hb2 : binds x (bind_typ V) (E1 ++ x ~ bind_typ V ++ E2)).
      { apply binds_app_3. apply binds_app_2. apply binds_cons_2; reflexivity. }
      pose proof (binds_unique binding x (bind_sub U) (bind_typ V) (E1 ++ x ~ bind_typ V ++ E2) Hb1 Hb2 Hu). discriminate.
    + apply binds_mid_remove with (x := x) (V := V); assumption.
  - intros X Q HX.
    destruct (eq_dec X x) as [->|Hne].
    + exfalso. pose proof (wf_env_uniq _ Hwf) as Hu.
      assert (Hb1 : binds x (bind_qua Q) (E1 ++ x ~ bind_typ V ++ E2)) by assumption.
      assert (Hb2 : binds x (bind_typ V) (E1 ++ x ~ bind_typ V ++ E2)).
      { apply binds_app_3. apply binds_app_2. apply binds_cons_2; reflexivity. }
      pose proof (binds_unique binding x (bind_qua Q) (bind_typ V) (E1 ++ x ~ bind_typ V ++ E2) Hb1 Hb2 Hu). discriminate.
    + apply binds_mid_remove with (x := x) (V := V); assumption.
Qed.

Lemma wf_qua_subqua : forall E Q,
  wf_qua E Q -> forall E', env_subqua_extends E E' -> wf_qua E' Q.
Proof.
  intros E Q H. induction H; intros E' Hext.
  - apply wf_qua_top.
  - destruct Hext as [H1 H2]. eapply wf_qua_fvar. apply H2. eassumption.
  - apply wf_qua_meet; [apply IHwf_qua1|apply IHwf_qua2]; assumption.
  - apply wf_qua_join; [apply IHwf_qua1|apply IHwf_qua2]; assumption.
  - apply wf_qua_bot.
Qed.

Lemma wf_typ_subqua : forall E T,
  wf_typ E T -> forall E', wf_env E' -> env_subqua_extends E E' -> wf_typ E' T.
Proof.
  intros E T H. induction H using wf_typ_mut_ind
    with (P := fun E T w => forall E', wf_env E' -> env_subqua_extends E E' -> wf_typ E' T)
         (P0 := fun E T w => forall E', wf_env E' -> env_subqua_extends E E' -> wf_qtyp E' T).
  - intros E' Hwf' Hext. apply wf_typ_top.
  - intros E' Hwf' Hext. apply wf_typ_var with (U := U).
    destruct Hext as [H1 H2]. apply H1. assumption.
  - intros E' Hwf' Hext. apply wf_typ_arrow.
    + apply IHwf_typ; assumption.
    + apply IHwf_typ0; assumption.
  - intros E' Hwf' Hext. apply wf_typ_all with (L := union L (dom E')).
    + apply IHwf_typ; assumption.
    + intros X Hx.
      assert (HxL : X `notin` L) by fsetdec.
      assert (Hxd : X `notin` dom E') by fsetdec.
      assert (Hwt : wf_typ E' T1). { apply IHwf_typ; assumption. }
      apply (H0 X HxL (X ~ bind_sub T1 ++ E')).
      * apply wf_env_sub; [exact Hwf' | exact Hwt | exact Hxd].
      * apply env_subqua_extends_cons; assumption.
  - intros E' Hwf' Hext. apply wf_typ_qall with (L := union L (dom E')).
    + apply wf_qua_subqua with (E := E); assumption.
    + intros X Hx.
      assert (HxL : X `notin` L) by fsetdec.
      assert (Hxd : X `notin` dom E') by fsetdec.
      assert (Hwq : wf_qua E' T1). { apply wf_qua_subqua with (E := E); assumption. }
      apply (H X HxL (X ~ bind_qua T1 ++ E')).
      * apply wf_env_qua; [exact Hwf' | exact Hwq | exact Hxd].
      * apply env_subqua_extends_cons; assumption.
  - intros E' Hwf' Hext. apply wf_typ_sum.
    + apply IHwf_typ; assumption.
    + apply IHwf_typ0; assumption.
  - intros E' Hwf' Hext. apply wf_typ_pair.
    + apply IHwf_typ; assumption.
    + apply IHwf_typ0; assumption.
  - intros E' Hwf' Hext. apply wf_qtyp_qtyp.
    + apply wf_qua_subqua with (E := E); assumption.
    + apply IHwf_typ; assumption.
Qed.

Lemma wf_qtyp_subqua : forall E T,
  wf_qtyp E T -> forall E', wf_env E' -> env_subqua_extends E E' -> wf_qtyp E' T.
Proof.
  intros E T H E' Hwf' Hext. destruct T as [Q T]. inversion H; subst.
  apply wf_qtyp_qtyp.
  - eapply wf_qua_subqua; eassumption.
  - eapply wf_typ_subqua; eassumption.
Qed.

Lemma subqual_subqua : forall E Q R,
  subqual E Q R -> forall E', wf_env E' -> env_subqua_extends E E' -> subqual E' Q R.
Proof.
  intros E Q R H. induction H; intros E' Hwf' Hext.
  - apply subqual_top; [exact Hwf' | apply wf_qua_subqua with (E := E); assumption].
  - apply subqual_bot; [exact Hwf' | apply wf_qua_subqua with (E := E); assumption].
  - apply subqual_refl_qvar; [exact Hwf' | apply wf_qua_subqua with (E := E); assumption].
  - eapply subqual_trans_qvar; [| apply IHsubqual; assumption].
    destruct Hext as [H1 H2]. apply H2. assumption.
  - apply subqual_join_inl.
    + apply IHsubqual; assumption.
    + apply wf_qua_subqua with (E := E); assumption.
  - apply subqual_join_inr.
    + apply wf_qua_subqua with (E := E); assumption.
    + apply IHsubqual; assumption.
  - apply subqual_join_elim; [apply IHsubqual1|apply IHsubqual2]; assumption.
  - apply subqual_meet_eliml.
    + apply IHsubqual; assumption.
    + apply wf_qua_subqua with (E := E); assumption.
  - apply subqual_meet_elimr.
    + apply wf_qua_subqua with (E := E); assumption.
    + apply IHsubqual; assumption.
  - apply subqual_meet_intro; [apply IHsubqual1|apply IHsubqual2]; assumption.
Qed.

Lemma sub_subqua : forall E S T,
  wf_env E -> sub E S T -> forall E', wf_env E' -> env_subqua_extends E E' -> sub E' S T.
Proof.
  intros E S T HwfE H. revert HwfE. induction H using sub_mut_ind
    with (P := fun E S T w => wf_env E -> forall E', wf_env E' -> env_subqua_extends E E' -> sub E' S T)
         (P0 := fun E S T w => wf_env E -> forall E', wf_env E' -> env_subqua_extends E E' -> subqtype E' S T).
  - intros Hwf0 E' Hwf' Hext'. apply sub_top.
    + exact Hwf'.
    + apply wf_typ_subqua with (E := E); assumption.
  - intros Hwf0 E' Hwf' Hext'. apply sub_refl_tvar.
    + exact Hwf'.
    + apply wf_typ_subqua with (E := E); assumption.
  - intros Hwf0 E' Hwf' Hext'. eapply sub_trans_tvar.
    + destruct Hext' as [H1 H2]. apply H1. eassumption.
    + apply IHsub; assumption.
  - intros Hwf0 E' Hwf' Hext'. apply sub_arrow.
    + apply IHsub; assumption.
    + apply IHsub0; assumption.
  - intros Hwf0 E' Hwf' Hext'. apply sub_all with (L := union L (union (dom E) (dom E'))).
    + apply IHsub; assumption.
    + intros X Hx.
      assert (HxL : X `notin` L) by fsetdec.
      assert (Hxd : X `notin` dom E') by fsetdec.
      assert (Hwt1' : wf_typ E' T1).
      { apply (proj1 (sub_wf E' T1 S1 Hwf' (IHsub Hwf0 E' Hwf' Hext'))). }
      assert (Hwt1 : wf_typ E T1).
      { apply (proj1 (sub_wf E T1 S1 Hwf0 H)). }
      assert (HxdE : X `notin` dom E) by fsetdec.
      assert (Hwfext : wf_env (X ~ bind_sub T1 ++ E)).
      { apply wf_env_sub; [exact Hwf0 | exact Hwt1 | exact HxdE]. }
      apply (H0 X HxL Hwfext (X ~ bind_sub T1 ++ E')).
      * apply wf_env_sub; [exact Hwf' | exact Hwt1' | exact Hxd].
      * apply env_subqua_extends_cons; assumption.
  - intros Hwf0 E' Hwf' Hext'. apply sub_qall with (L := union L (union (dom E) (dom E'))).
    + apply subqual_subqua with (E := E); assumption.
    + intros X Hx.
      assert (HxL : X `notin` L) by fsetdec.
      assert (Hxd : X `notin` dom E') by fsetdec.
      assert (Hwq : wf_qua E T1).
      { apply (proj1 (subqual_wf E T1 S1 Hwf0 s)). }
      assert (Hwq' : wf_qua E' T1).
      { apply wf_qua_subqua with (E := E); assumption. }
      assert (HxdE : X `notin` dom E) by fsetdec.
      assert (Hwfext : wf_env (X ~ bind_qua T1 ++ E)).
      { apply wf_env_qua; [exact Hwf0 | exact Hwq | exact HxdE]. }
      apply (H X HxL Hwfext (X ~ bind_qua T1 ++ E')).
      * apply wf_env_qua; [exact Hwf' | exact Hwq' | exact Hxd].
      * apply env_subqua_extends_cons; assumption.
  - intros Hwf0 E' Hwf' Hext'. apply sub_sum; [apply IHsub|apply IHsub0]; assumption.
  - intros Hwf0 E' Hwf' Hext'. apply sub_pair; [apply IHsub|apply IHsub0]; assumption.
  - intros Hwf0 E' Hwf' Hext'. apply sub_qtyp_qtyp.
    + apply subqual_subqua with (E := E); assumption.
    + apply IHsub; assumption.
Qed.

Lemma subqtype_subqua : forall E S T,
  wf_env E -> subqtype E S T -> forall E', wf_env E' -> env_subqua_extends E E' -> subqtype E' S T.
Proof.
  intros E S T HwfE H E' Hwf' Hext'. inversion H; subst.
  apply sub_qtyp_qtyp.
  - apply subqual_subqua with (E := E); [eassumption | exact Hwf' | exact Hext'].
  - apply sub_subqua with (E := E); [exact HwfE | eassumption | exact Hwf' | exact Hext'].
Qed.

Lemma dom_mid_remove_notin : forall (E1 E2 : env) (x : atom) (V : qtyp) (X : atom),
  X `notin` dom (E1 ++ x ~ bind_typ V ++ E2) -> X `notin` dom (E1 ++ E2).
Proof.
  intros E1 E2 x V X H. rewrite dom_app in *. rewrite dom_app in H. fsetdec.
Qed.

Lemma wf_env_mid_remove : forall (E1 E2 : env) (x : atom) (V : qtyp),
  wf_env (E1 ++ x ~ bind_typ V ++ E2) -> wf_env (E1 ++ E2).
Proof.
  intros E1. induction E1 as [| p E1 IH]; intros E2 x V Hwf.
  - simpl in Hwf. destruct (wf_env_cons_inv x (bind_typ V) E2 Hwf) as [HE _]. exact HE.
  - destruct p as [z c]. simpl in Hwf.
    destruct (wf_env_cons_inv z c (E1 ++ x ~ bind_typ V ++ E2) Hwf) as [Hwf0 [Hdom Hwfc]].
    assert (Hwf_tail : wf_env (E1 ++ E2)) by (apply (IH E2 x V); exact Hwf0).
    assert (Hrel : env_subqua_extends (E1 ++ x ~ bind_typ V ++ E2) (E1 ++ E2)).
    { apply env_subqua_extends_mid. exact Hwf0. }
    assert (Hdom' : z `notin` dom (E1 ++ E2)).
    { apply (dom_mid_remove_notin E1 E2 x V z). exact Hdom. }
    destruct c as [T|T|Q]; simpl in *.
    + apply wf_env_sub; [exact Hwf_tail | | exact Hdom'].
      apply wf_typ_subqua with (E := E1 ++ x ~ bind_typ V ++ E2); assumption.
    + apply wf_env_typ; [exact Hwf_tail | | exact Hdom'].
      apply wf_qtyp_subqua with (E := E1 ++ x ~ bind_typ V ++ E2); assumption.
    + apply wf_env_qua; [exact Hwf_tail | | exact Hdom'].
      eapply wf_qua_subqua; [exact Hwfc | exact Hrel].
Qed.

(* ===================================================================== *)
(* Weakening for typing                                                  *)
(* ===================================================================== *)

Lemma typing_weaken : forall E Q e T,
  typing E Q e T -> forall E', wf_env E' -> env_extends E E' -> typing E' Q e T.
Proof.
  intros E Q e T H. induction H using typing_ind
    with (P := fun E Q e T => forall E', wf_env E' -> env_extends E E' -> typing E' Q e T).
  - intros E' Hwf' Hext'. apply typing_var.
    + exact Hwf'.
    + apply Hext'. eassumption.
  - intros E' Hwf' Hext'. apply typing_abs with (L := union L (dom E')).
    intros xx Hx.
    assert (HxL : xx `notin` L) by fsetdec.
    assert (Hxd : xx `notin` dom E') by fsetdec.
    assert (Hwf_src : wf_env (xx ~ bind_typ V ++ E)).
    { apply typing_wf_env with (Q := P) (e := open_ee e1 xx) (T := T1).
      apply H. exact HxL. }
    destruct (wf_env_cons_inv xx (bind_typ V) E Hwf_src) as [HE [HD HV]].
    assert (HV' : wf_qtyp E' V).
    { apply wf_qtyp_weaken with (E := E); assumption. }
    apply (H0 xx HxL (xx ~ bind_typ V ++ E')).
    + apply wf_env_typ; assumption.
    + apply env_extends_cons; assumption.
  - intros E' Hwf' Hext'. apply typing_app with (T1 := T1).
    + apply IHtyping1; assumption.
    + apply IHtyping2; assumption.
  - intros E' Hwf' Hext'. apply typing_tabs with (L := union L (dom E')).
    intros XX Hx.
    assert (HxL : XX `notin` L) by fsetdec.
    assert (Hxd : XX `notin` dom E') by fsetdec.
    assert (Hwf_src : wf_env (XX ~ bind_sub V ++ E)).
    { apply typing_wf_env with (Q := P) (e := open_te e1 XX) (T := open_tqt T1 XX).
      apply H. exact HxL. }
    destruct (wf_env_cons_inv XX (bind_sub V) E Hwf_src) as [HE [HD HV]].
    assert (HV' : wf_typ E' V).
    { apply wf_typ_weaken with (E := E); assumption. }
    apply (H0 XX HxL (XX ~ bind_sub V ++ E')).
    + apply wf_env_sub; assumption.
    + apply env_extends_cons; assumption.
  - intros E' Hwf' Hext'. eapply typing_tapp.
    + apply IHtyping; assumption.
    + apply (sub_weaken E T T1).
      * apply typing_wf_env with (Q := Q) (e := e1) (T := qtyp_qtyp Q (typ_all T1 T2)).
        exact H.
      * exact H0.
      * exact Hwf'.
      * exact Hext'.
  - intros E' Hwf' Hext'. apply typing_qabs with (L := union L (dom E')).
    + apply wf_qua_weaken with (E := E); assumption.
    + intros XX Hx.
      assert (HxL : XX `notin` L) by fsetdec.
      assert (Hxd : XX `notin` dom E') by fsetdec.
      assert (Hwf_src : wf_env (XX ~ bind_qua Q ++ E)).
      { apply typing_wf_env with (Q := P) (e := open_qe e1 XX) (T := open_qqt T1 XX).
        apply H0. exact HxL. }
      destruct (wf_env_cons_inv XX (bind_qua Q) E Hwf_src) as [HE [HD HQ]].
      assert (HQ' : wf_qua E' Q).
      { apply wf_qua_weaken with (E := E); assumption. }
      apply (H1 XX HxL (XX ~ bind_qua Q ++ E')).
      * apply wf_env_qua; assumption.
      * apply env_extends_cons; assumption.
  - intros E' Hwf' Hext'. eapply typing_qapp.
    + apply IHtyping; assumption.
    + apply subqual_weaken with (E := E); assumption.
  - intros E' Hwf' Hext'. apply typing_sub with (S := S).
    + apply IHtyping; assumption.
    + apply (subqtype_weaken E S T).
      * apply typing_wf_env with (Q := Q) (e := e) (T := S). exact H.
      * exact H0.
      * exact Hwf'.
      * exact Hext'.
  - intros E' Hwf' Hext'. eapply typing_subqual.
    + apply IHtyping; assumption.
    + apply subqual_weaken with (E := E); assumption.
  - intros E' Hwf' Hext'. eapply typing_let with (L := union L (dom E')).
    + apply IHtyping; assumption.
    + intros xx Hx.
      assert (HxL : xx `notin` L) by fsetdec.
      assert (Hxd : xx `notin` dom E') by fsetdec.
      assert (Hwf_src : wf_env (xx ~ bind_typ T1 ++ E)).
      { apply typing_wf_env with (Q := Q) (e := open_ee e2 xx) (T := T2).
        apply H0. exact HxL. }
      destruct (wf_env_cons_inv xx (bind_typ T1) E Hwf_src) as [HE [HD HV]].
      assert (HV' : wf_qtyp E' T1).
      { apply wf_qtyp_weaken with (E := E); assumption. }
      apply (H1 xx HxL (xx ~ bind_typ T1 ++ E')).
      * apply wf_env_typ; assumption.
      * apply env_extends_cons; assumption.
  - intros E' Hwf' Hext'. apply typing_inl with (T1 := T1).
    + apply wf_qua_weaken with (E := E); assumption.
    + apply IHtyping; assumption.
    + apply wf_qtyp_weaken with (E := E); assumption.
  - intros E' Hwf' Hext'. apply typing_inr with (T2 := T2).
    + apply wf_qua_weaken with (E := E); assumption.
    + apply IHtyping; assumption.
    + apply wf_qtyp_weaken with (E := E); assumption.
  - intros E' Hwf' Hext'. eapply typing_case with (L := union L (dom E')).
    + apply IHtyping; assumption.
    + intros xx Hx.
      assert (HxL : xx `notin` L) by fsetdec.
      assert (Hxd : xx `notin` dom E') by fsetdec.
      assert (Hwf_src : wf_env (xx ~ bind_typ T1 ++ E)).
      { apply typing_wf_env with (Q := Q) (e := open_ee e2 xx) (T := T).
        apply H0. exact HxL. }
      destruct (wf_env_cons_inv xx (bind_typ T1) E Hwf_src) as [HE [HD HV]].
      assert (HV' : wf_qtyp E' T1).
      { apply wf_qtyp_weaken with (E := E); assumption. }
      apply (H1 xx HxL (xx ~ bind_typ T1 ++ E')).
      * apply wf_env_typ; assumption.
      * apply env_extends_cons; assumption.
    + intros xx Hx.
      assert (HxL : xx `notin` L) by fsetdec.
      assert (Hxd : xx `notin` dom E') by fsetdec.
      assert (Hwf_src : wf_env (xx ~ bind_typ T2 ++ E)).
      { apply typing_wf_env with (Q := Q) (e := open_ee e3 xx) (T := T).
        apply H2. exact HxL. }
      destruct (wf_env_cons_inv xx (bind_typ T2) E Hwf_src) as [HE [HD HV]].
      assert (HV' : wf_qtyp E' T2).
      { apply wf_qtyp_weaken with (E := E); assumption. }
      apply (H3 xx HxL (xx ~ bind_typ T2 ++ E')).
      * apply wf_env_typ; assumption.
      * apply env_extends_cons; assumption.
  - intros E' Hwf' Hext'. apply typing_pair with (T1 := T1) (T2 := T2).
    + apply wf_qua_weaken with (E := E); assumption.
    + apply IHtyping1; assumption.
    + apply IHtyping2; assumption.
  - intros E' Hwf' Hext'. eapply typing_first.
    apply IHtyping; assumption.
  - intros E' Hwf' Hext'. eapply typing_second.
    apply IHtyping; assumption.
  - intros E' Hwf' Hext'. eapply typing_upqual.
    + apply IHtyping; assumption.
    + apply subqual_weaken with (E := E); assumption.
  - intros E' Hwf' Hext'. eapply typing_check.
    + apply IHtyping; assumption.
    + apply subqual_weaken with (E := E); assumption.
Qed.

(* ===================================================================== *)
(* Closedness of typable expressions                                     *)
(* ===================================================================== *)

Definition closed_exp (e : exp) : Prop :=
  forall (k : nat) (a : atom), open_ee_rec k (exp_fvar a) e = e.

Fixpoint close_ee_rec (k : nat) (xx : atom) (e : exp) {struct e} : exp :=
  match e with
  | exp_bvar i => exp_bvar i
  | exp_fvar y => if xx == y then exp_bvar k else exp_fvar y
  | exp_abs P V e1 => exp_abs P V (close_ee_rec (S k) xx e1)
  | exp_app e1 e2 => exp_app (close_ee_rec k xx e1) (close_ee_rec k xx e2)
  | exp_tabs P V e1 => exp_tabs P V (close_ee_rec (S k) xx e1)
  | exp_tapp e1 V => exp_tapp (close_ee_rec k xx e1) V
  | exp_qabs P Q e1 => exp_qabs P Q (close_ee_rec (S k) xx e1)
  | exp_qapp e1 Q => exp_qapp (close_ee_rec k xx e1) Q
  | exp_let e1 e2 => exp_let (close_ee_rec k xx e1) (close_ee_rec (S k) xx e2)
  | exp_inl P e1 => exp_inl P (close_ee_rec k xx e1)
  | exp_inr P e1 => exp_inr P (close_ee_rec k xx e1)
  | exp_case e1 e2 e3 =>
      exp_case (close_ee_rec k xx e1) (close_ee_rec (S k) xx e2) (close_ee_rec (S k) xx e3)
  | exp_pair P e1 e2 => exp_pair P (close_ee_rec k xx e1) (close_ee_rec k xx e2)
  | exp_first e1 => exp_first (close_ee_rec k xx e1)
  | exp_second e1 => exp_second (close_ee_rec k xx e1)
  | exp_ref P e1 => exp_ref P (close_ee_rec k xx e1)
  | exp_ref_label P l => exp_ref_label P l
  | exp_deref e1 => exp_deref (close_ee_rec k xx e1)
  | exp_set_ref e1 e2 => exp_set_ref (close_ee_rec k xx e1) (close_ee_rec k xx e2)
  | exp_upqual P e1 => exp_upqual P (close_ee_rec k xx e1)
  | exp_check P e1 => exp_check P (close_ee_rec k xx e1)
  end.

Lemma close_open_ee : forall (k : nat) (xx : atom) (e : exp),
  xx `notin` fv_ee e -> close_ee_rec k xx (open_ee_rec k xx e) = e.
Proof.
  intros k xx e. revert k. induction e; intros k H; simpl in *; try reflexivity.
  - (* bvar *) destruct (k == n) as [Heq|Hneq]; simpl.
    + rewrite Heq. rewrite eq_dec_refl. reflexivity.
    + reflexivity.
  - (* fvar *) destruct (xx == a) as [Heq|Hneq]; [fsetdec | reflexivity].
  - (* abs *) rewrite IHe; auto.
  - (* app *) rewrite IHe1, IHe2; auto.
  - (* tabs *) rewrite IHe; auto.
  - (* tapp *) rewrite IHe; auto.
  - (* qabs *) rewrite IHe; auto.
  - (* qapp *) rewrite IHe; auto.
  - (* let *) rewrite IHe1, IHe2; auto.
  - (* inl *) rewrite IHe; auto.
  - (* inr *) rewrite IHe; auto.
  - (* case *) rewrite IHe1, IHe2, IHe3; auto.
  - (* pair *) rewrite IHe1, IHe2; auto.
  - (* first *) rewrite IHe; auto.
  - (* second *) rewrite IHe; auto.
  - (* ref *) rewrite IHe; auto.
  - (* deref *) rewrite IHe; auto.
  - (* set_ref *) rewrite IHe1, IHe2; auto.
  - (* upqual *) rewrite IHe; auto.
  - (* check *) rewrite IHe; auto.
Qed.
Lemma S_neq : forall (i j : nat), i <> j -> S i <> S j.
Proof. intros i j H Hc. apply H. injection Hc. auto. Qed.

Lemma close_open_comm : forall (e : exp) (i j : nat) (xx a : atom),
  i <> j -> a <> xx ->
  close_ee_rec i xx (open_ee_rec j (exp_fvar a) e) =
  open_ee_rec j (exp_fvar a) (close_ee_rec i xx e).
Proof.
  intros e. induction e; intros i0 j0 xx aa Hij Hax; simpl in *; try reflexivity.
  - (* bvar *) destruct (j0 == n) as [Hj|Hj]; simpl.
    + destruct (xx == aa) as [Hxa|Hxa]; [exfalso; apply Hax; symmetry; exact Hxa | reflexivity].
    + reflexivity.
  - (* fvar *) destruct (xx == a) as [Hxa|Hxa]; simpl.
    + destruct (j0 == i0) as [Hji|Hji]; [exfalso; apply Hij; symmetry; exact Hji | reflexivity].
    + reflexivity.
  - (* abs *) assert (Hne : S i0 <> S j0) by (apply S_neq; exact Hij).
    assert (He : close_ee_rec (S i0) xx (open_ee_rec (S j0) aa e) =
                 open_ee_rec (S j0) aa (close_ee_rec (S i0) xx e))
      by (apply (IHe (S i0) (S j0) xx aa Hne Hax)).
    rewrite He. reflexivity.
  - (* app *) assert (H1 : close_ee_rec i0 xx (open_ee_rec j0 aa e1) =
                        open_ee_rec j0 aa (close_ee_rec i0 xx e1))
      by (apply (IHe1 i0 j0 xx aa Hij Hax)).
    assert (H2 : close_ee_rec i0 xx (open_ee_rec j0 aa e2) =
                 open_ee_rec j0 aa (close_ee_rec i0 xx e2))
      by (apply (IHe2 i0 j0 xx aa Hij Hax)).
    rewrite H1, H2. reflexivity.
  - (* tabs *) assert (Hne : S i0 <> S j0) by (apply S_neq; exact Hij).
    assert (He : close_ee_rec (S i0) xx (open_ee_rec (S j0) aa e) =
                 open_ee_rec (S j0) aa (close_ee_rec (S i0) xx e))
      by (apply (IHe (S i0) (S j0) xx aa Hne Hax)).
    rewrite He. reflexivity.
  - (* tapp *) assert (He : close_ee_rec i0 xx (open_ee_rec j0 aa e) =
                 open_ee_rec j0 aa (close_ee_rec i0 xx e))
      by (apply (IHe i0 j0 xx aa Hij Hax)).
    rewrite He. reflexivity.
  - (* qabs *) assert (Hne : S i0 <> S j0) by (apply S_neq; exact Hij).
    assert (He : close_ee_rec (S i0) xx (open_ee_rec (S j0) aa e) =
                 open_ee_rec (S j0) aa (close_ee_rec (S i0) xx e))
      by (apply (IHe (S i0) (S j0) xx aa Hne Hax)).
    rewrite He. reflexivity.
  - (* qapp *) assert (He : close_ee_rec i0 xx (open_ee_rec j0 aa e) =
                 open_ee_rec j0 aa (close_ee_rec i0 xx e))
      by (apply (IHe i0 j0 xx aa Hij Hax)).
    rewrite He. reflexivity.
  - (* let *) assert (H1 : close_ee_rec i0 xx (open_ee_rec j0 aa e1) =
                        open_ee_rec j0 aa (close_ee_rec i0 xx e1))
      by (apply (IHe1 i0 j0 xx aa Hij Hax)).
    assert (Hne : S i0 <> S j0) by (apply S_neq; exact Hij).
    assert (H2 : close_ee_rec (S i0) xx (open_ee_rec (S j0) aa e2) =
                 open_ee_rec (S j0) aa (close_ee_rec (S i0) xx e2))
      by (apply (IHe2 (S i0) (S j0) xx aa Hne Hax)).
    rewrite H1, H2. reflexivity.
  - (* inl *) assert (He : close_ee_rec i0 xx (open_ee_rec j0 aa e) =
                 open_ee_rec j0 aa (close_ee_rec i0 xx e))
      by (apply (IHe i0 j0 xx aa Hij Hax)).
    rewrite He. reflexivity.
  - (* inr *) assert (He : close_ee_rec i0 xx (open_ee_rec j0 aa e) =
                 open_ee_rec j0 aa (close_ee_rec i0 xx e))
      by (apply (IHe i0 j0 xx aa Hij Hax)).
    rewrite He. reflexivity.
  - (* case *) assert (H1 : close_ee_rec i0 xx (open_ee_rec j0 aa e1) =
                        open_ee_rec j0 aa (close_ee_rec i0 xx e1))
      by (apply (IHe1 i0 j0 xx aa Hij Hax)).
    assert (Hne : S i0 <> S j0) by (apply S_neq; exact Hij).
    assert (H2 : close_ee_rec (S i0) xx (open_ee_rec (S j0) aa e2) =
                 open_ee_rec (S j0) aa (close_ee_rec (S i0) xx e2))
      by (apply (IHe2 (S i0) (S j0) xx aa Hne Hax)).
    assert (H3 : close_ee_rec (S i0) xx (open_ee_rec (S j0) aa e3) =
                 open_ee_rec (S j0) aa (close_ee_rec (S i0) xx e3))
      by (apply (IHe3 (S i0) (S j0) xx aa Hne Hax)).
    rewrite H1, H2, H3. reflexivity.
  - (* pair *) assert (H1 : close_ee_rec i0 xx (open_ee_rec j0 aa e1) =
                        open_ee_rec j0 aa (close_ee_rec i0 xx e1))
      by (apply (IHe1 i0 j0 xx aa Hij Hax)).
    assert (H2 : close_ee_rec i0 xx (open_ee_rec j0 aa e2) =
                 open_ee_rec j0 aa (close_ee_rec i0 xx e2))
      by (apply (IHe2 i0 j0 xx aa Hij Hax)).
    rewrite H1, H2. reflexivity.
  - (* first *) assert (He : close_ee_rec i0 xx (open_ee_rec j0 aa e) =
                 open_ee_rec j0 aa (close_ee_rec i0 xx e))
      by (apply (IHe i0 j0 xx aa Hij Hax)).
    rewrite He. reflexivity.
  - (* second *) assert (He : close_ee_rec i0 xx (open_ee_rec j0 aa e) =
                 open_ee_rec j0 aa (close_ee_rec i0 xx e))
      by (apply (IHe i0 j0 xx aa Hij Hax)).
    rewrite He. reflexivity.
  - (* ref *) assert (He : close_ee_rec i0 xx (open_ee_rec j0 aa e) =
                 open_ee_rec j0 aa (close_ee_rec i0 xx e))
      by (apply (IHe i0 j0 xx aa Hij Hax)).
    rewrite He. reflexivity.
  - (* deref *) assert (He : close_ee_rec i0 xx (open_ee_rec j0 aa e) =
                 open_ee_rec j0 aa (close_ee_rec i0 xx e))
      by (apply (IHe i0 j0 xx aa Hij Hax)).
    rewrite He. reflexivity.
  - (* set_ref *) assert (H1 : close_ee_rec i0 xx (open_ee_rec j0 aa e1) =
                        open_ee_rec j0 aa (close_ee_rec i0 xx e1))
      by (apply (IHe1 i0 j0 xx aa Hij Hax)).
    assert (H2 : close_ee_rec i0 xx (open_ee_rec j0 aa e2) =
                 open_ee_rec j0 aa (close_ee_rec i0 xx e2))
      by (apply (IHe2 i0 j0 xx aa Hij Hax)).
    rewrite H1, H2. reflexivity.
  - (* upqual *) assert (He : close_ee_rec i0 xx (open_ee_rec j0 aa e) =
                 open_ee_rec j0 aa (close_ee_rec i0 xx e))
      by (apply (IHe i0 j0 xx aa Hij Hax)).
    rewrite He. reflexivity.
  - (* check *) assert (He : close_ee_rec i0 xx (open_ee_rec j0 aa e) =
                 open_ee_rec j0 aa (close_ee_rec i0 xx e))
      by (apply (IHe i0 j0 xx aa Hij Hax)).
    rewrite He. reflexivity.
Qed.






(* ===================================================================== *)
(* Closing and injectivity of opening                                    *)
(* ===================================================================== *)



Lemma open_ee_rec_indep_all : forall (e : exp) (k : nat) (b : atom),
  open_ee_rec k (exp_fvar b) e = e ->
  forall a, open_ee_rec k (exp_fvar a) e = e.
Proof.
  intros e. induction e; intros k0 b Hb a0; simpl in *; try reflexivity.
  - (* bvar *) destruct (k0 == n) as [Hk|Hk]; simpl.
    + discriminate Hb.
    + reflexivity.
  - (* abs *) f_equal. apply IHe with (b := b); injection Hb; intros; assumption.
  - (* app *) f_equal.
    + apply IHe1 with (b := b); injection Hb; intros; assumption.
    + apply IHe2 with (b := b); injection Hb; intros; assumption.
  - (* tabs *) f_equal. apply IHe with (b := b); injection Hb; intros; assumption.
  - (* tapp *) f_equal. apply IHe with (b := b); injection Hb; intros; assumption.
  - (* qabs *) f_equal. apply IHe with (b := b); injection Hb; intros; assumption.
  - (* qapp *) f_equal. apply IHe with (b := b); injection Hb; intros; assumption.
  - (* let *) f_equal.
    + apply IHe1 with (b := b); injection Hb; intros; assumption.
    + apply IHe2 with (b := b); injection Hb; intros; assumption.
  - (* inl *) f_equal. apply IHe with (b := b); injection Hb; intros; assumption.
  - (* inr *) f_equal. apply IHe with (b := b); injection Hb; intros; assumption.
  - (* case *) f_equal.
    + apply IHe1 with (b := b); injection Hb; intros; assumption.
    + apply IHe2 with (b := b); injection Hb; intros; assumption.
    + apply IHe3 with (b := b); injection Hb; intros; assumption.
  - (* pair *) f_equal.
    + apply IHe1 with (b := b); injection Hb; intros; assumption.
    + apply IHe2 with (b := b); injection Hb; intros; assumption.
  - (* first *) f_equal. apply IHe with (b := b); injection Hb; intros; assumption.
  - (* second *) f_equal. apply IHe with (b := b); injection Hb; intros; assumption.
  - (* ref *) f_equal. apply IHe with (b := b); injection Hb; intros; assumption.
  - (* deref *) f_equal. apply IHe with (b := b); injection Hb; intros; assumption.
  - (* set_ref *) f_equal.
    + apply IHe1 with (b := b); injection Hb; intros; assumption.
    + apply IHe2 with (b := b); injection Hb; intros; assumption.
  - (* upqual *) f_equal. apply IHe with (b := b); injection Hb; intros; assumption.
  - (* check *) f_equal. apply IHe with (b := b); injection Hb; intros; assumption.
Qed.

Lemma close_ee_id : forall (e : exp) (k : nat) (xx : atom),
  xx `notin` fv_ee e -> close_ee_rec k xx e = e.
Proof.
  intros e. induction e; intros k xx H; simpl in *; try reflexivity.
  - destruct (xx == a) as [Heq|Hneq]; [subst; fsetdec | reflexivity].
  - rewrite IHe; auto.
  - rewrite IHe1, IHe2; auto.
  - rewrite IHe; auto.
  - rewrite IHe; auto.
  - rewrite IHe; auto.
  - rewrite IHe; auto.
  - rewrite IHe1, IHe2; auto.
  - rewrite IHe; auto.
  - rewrite IHe; auto.
  - rewrite IHe1, IHe2, IHe3; auto.
  - rewrite IHe1, IHe2; auto.
  - rewrite IHe; auto.
  - rewrite IHe; auto.
  - rewrite IHe; auto.
  - rewrite IHe; auto.
  - rewrite IHe1, IHe2; auto.
  - rewrite IHe; auto.
  - rewrite IHe; auto.
Qed.

Lemma closed_inv_open_ee : forall (body : exp) (xx : atom),
  xx `notin` fv_ee body -> closed_exp (open_ee body xx) ->
  forall (k : nat) (a : atom), open_ee_rec (S k) (exp_fvar a) body = body.
Proof.
  intros body xx Hfresh Hc k a.
  pick fresh bb.
  assert (Hbbx : bb <> xx) by fsetdec.
  assert (Hbba : bb <> a) by fsetdec.
  assert (Hopen : open_ee_rec (S k) (exp_fvar bb) (open_ee_rec 0 xx body) = open_ee_rec 0 xx body).
  { apply Hc. }
  assert (Hopen' : open_ee_rec (S k) (exp_fvar bb) body = body).
  { (* close at 0 with xx *)
    assert (Hcl : close_ee_rec 0 xx (open_ee_rec (S k) (exp_fvar bb) (open_ee_rec 0 xx body)) =
                  close_ee_rec 0 xx (open_ee_rec 0 xx body)).
    { rewrite Hopen. reflexivity. }
    rewrite (close_open_comm (open_ee_rec 0 xx body) 0 (S k) xx bb) in Hcl.
    - rewrite (close_open_ee 0 xx body Hfresh) in Hcl.
      exact Hcl.
    - intro Hc0. discriminate Hc0.
    - intro Hc0. exact (Hbbx Hc0).
  }
  apply (open_ee_rec_indep_all body (S k) bb Hopen' a).
Qed.


(* ===== inlined from /tmp/pkg/Base.v ===== *)

Record env_narrow_full (E E' : env) : Prop := {
  enf_wf_old : wf_env E;
  enf_wf_new : wf_env E';
  enf_dom : dom E = dom E';
  enf_sub : forall (X : atom) (U : typ),
     binds X (bind_sub U) E ->
     (binds X (bind_sub U) E') \/
     (exists U', binds X (bind_sub U') E' /\ wf_typ E' U' /\ sub E' U' U /\
        forall E'', wf_env E'' -> env_extends E' E'' ->
          forall W, sub E'' U W -> sub E'' U' W);
  enf_qua : forall (X : atom) (Q : qua),
     binds X (bind_qua Q) E ->
     (binds X (bind_qua Q) E') \/
     (exists Q', binds X (bind_qua Q') E' /\ wf_qua E' Q' /\ subqual E' Q' Q /\
        forall E'', wf_env E'' -> env_extends E' E'' ->
          forall S, subqual E'' Q S -> subqual E'' Q' S);
  enf_typ : forall (X : atom) (T : qtyp),
     binds X (bind_typ T) E -> binds X (bind_typ T) E'
}.

Lemma env_narrow_refl : forall E, wf_env E -> env_narrow_full E E.
Proof.
  intros E Hwf. constructor.
  - exact Hwf.
  - exact Hwf.
  - reflexivity.
  - intros X U Hb. left; assumption.
  - intros X Q Hb. left; assumption.
  - intros X T Hb. assumption.
Qed.

Lemma env_narrow_binds_sub : forall E E' X U,
  env_narrow_full E E' -> binds X (bind_sub U) E ->
  (binds X (bind_sub U) E') \/
  (exists U', binds X (bind_sub U') E' /\ wf_typ E' U' /\ sub E' U' U /\
     forall E'', wf_env E'' -> env_extends E' E'' ->
       forall W, sub E'' U W -> sub E'' U' W).
Proof. intros. apply (enf_sub E E' H X U H0). Qed.

Lemma env_narrow_binds_qua : forall E E' X Q,
  env_narrow_full E E' -> binds X (bind_qua Q) E ->
  (binds X (bind_qua Q) E') \/
  (exists Q', binds X (bind_qua Q') E' /\ wf_qua E' Q' /\ subqual E' Q' Q /\
     forall E'', wf_env E'' -> env_extends E' E'' ->
       forall S, subqual E'' Q S -> subqual E'' Q' S).
Proof. intros. apply (enf_qua E E' H X Q H0). Qed.

Lemma env_narrow_binds_typ : forall E E' X T,
  env_narrow_full E E' -> binds X (bind_typ T) E -> binds X (bind_typ T) E'.
Proof. intros. apply (enf_typ E E' H X T H0). Qed.

(* Extend the narrowing relation with a binder that is unchanged in both envs. *)
Lemma binds_cons_sub_eq : forall X y (U : typ) b E,
  binds X (bind_sub U) (y ~ b ++ E) ->
  (X = y /\ b = bind_sub U) \/ binds X (bind_sub U) E.
Proof.
  intros. unfold binds in *. simpl in H. destruct H as [Heq|Hin].
  - left. injection Heq as -> ->. auto.
  - right. exact Hin.
Qed.

Lemma binds_cons_qua_eq : forall X y (Q : qua) b E,
  binds X (bind_qua Q) (y ~ b ++ E) ->
  (X = y /\ b = bind_qua Q) \/ binds X (bind_qua Q) E.
Proof.
  intros. unfold binds in *. simpl in H. destruct H as [Heq|Hin].
  - left. injection Heq as -> ->. auto.
  - right. exact Hin.
Qed.

Lemma binds_cons_typ_eq : forall X y (T : qtyp) b E,
  binds X (bind_typ T) (y ~ b ++ E) ->
  (X = y /\ b = bind_typ T) \/ binds X (bind_typ T) E.
Proof.
  intros. unfold binds in *. simpl in H. destruct H as [Heq|Hin].
  - left. injection Heq as -> ->. auto.
  - right. exact Hin.
Qed.

Lemma wf_env_cons_wf_typ : forall E X (U : typ),
  wf_env (X ~ bind_sub U ++ E) -> wf_typ E U.
Proof.
  intros. destruct (wf_env_cons_inv X (bind_sub U) E H) as [_ [_ Hwf]].
  exact Hwf.
Qed.

Lemma wf_env_cons_wf_qua : forall E X (Q : qua),
  wf_env (X ~ bind_qua Q ++ E) -> wf_qua E Q.
Proof.
  intros. destruct (wf_env_cons_inv X (bind_qua Q) E H) as [_ [_ Hwf]].
  exact Hwf.
Qed.

Lemma wf_env_cons_wf_qtyp : forall E X (T : qtyp),
  wf_env (X ~ bind_typ T ++ E) -> wf_qtyp E T.
Proof.
  intros. destruct (wf_env_cons_inv X (bind_typ T) E H) as [_ [_ Hwf]].
  exact Hwf.
Qed.

Lemma binds_cons_tail : forall (A : Type) (X y : atom) (a b : A) (E : list (atom * A)),
  binds X a E -> binds X a (y ~ b ++ E).
Proof. intros A X y a b E H. unfold binds in *. simpl. right. assumption. Qed.

Lemma env_narrow_cons_sub_same : forall E E' X U,
  env_narrow_full E E' ->
  wf_env (X ~ bind_sub U ++ E) -> wf_env (X ~ bind_sub U ++ E') ->
  env_narrow_full (X ~ bind_sub U ++ E) (X ~ bind_sub U ++ E').
Proof.
  intros E E' X0 U Hn Hwo Hwn. constructor.
  - exact Hwo.
  - exact Hwn.
  - simpl. f_equal. apply (enf_dom E E' Hn).
  - intros X U0 Hb. apply binds_cons_sub_eq in Hb. destruct Hb as [[Heq Hbeq]|Hin].
    + subst. injection Hbeq as ->. left. apply binds_cons_2; reflexivity.
    + destruct (enf_sub E E' Hn X U0 Hin) as [Hl|[U' [Hb' [Hwt [Hsub Hclo]]]]].
      * left. apply binds_cons_tail; assumption.
      * right. exists U'. split; [|split; [|split]].
        -- apply binds_cons_tail; assumption.
        -- apply (wf_typ_weaken E' (X0 ~ bind_sub U ++ E') U' Hwn (env_extends_cons_tail E' X0 (bind_sub U)) Hwt).
        -- apply (sub_weaken E' U' U0 (enf_wf_new E E' Hn) Hsub (X0 ~ bind_sub U ++ E') Hwn (env_extends_cons_tail E' X0 (bind_sub U))).
        -- intros E'' Hwf'' Hext. apply Hclo; [exact Hwf''|].
           apply (env_extends_trans E' (X0 ~ bind_sub U ++ E') E'' (env_extends_cons_tail E' X0 (bind_sub U)) Hext).
  - intros X Q Hb. apply binds_cons_qua_eq in Hb. destruct Hb as [[Heq Hbeq]|Hin].
    + subst. discriminate Hbeq.
    + destruct (enf_qua E E' Hn X Q Hin) as [Hl|[Q' [Hb' [Hwq [Hsub Hclo]]]]].
      * left. apply binds_cons_tail; assumption.
      * right. exists Q'. split; [|split; [|split]].
        -- apply binds_cons_tail; assumption.
        -- apply (wf_qua_weaken E' (X0 ~ bind_sub U ++ E') Q' Hwn (env_extends_cons_tail E' X0 (bind_sub U)) Hwq).
        -- apply (subqual_weaken E' Q' Q Hsub (X0 ~ bind_sub U ++ E') Hwn (env_extends_cons_tail E' X0 (bind_sub U))).
        -- intros E'' Hwf'' Hext. apply Hclo; [exact Hwf''|].
           apply (env_extends_trans E' (X0 ~ bind_sub U ++ E') E'' (env_extends_cons_tail E' X0 (bind_sub U)) Hext).
  - intros X T Hb. apply binds_cons_typ_eq in Hb. destruct Hb as [[Heq Hbeq]|Hin].
    + subst. discriminate Hbeq.
    + apply binds_cons_tail. apply (enf_typ E E' Hn). exact Hin.
Qed.

Lemma env_narrow_cons_sub_changed : forall E E' X U U',
  env_narrow_full E E' ->
  wf_env (X ~ bind_sub U ++ E) -> wf_env (X ~ bind_sub U' ++ E') ->
  sub E' U' U ->
  (forall E'', wf_env E'' -> env_extends E' E'' ->
     forall W, sub E'' U W -> sub E'' U' W) ->
  env_narrow_full (X ~ bind_sub U ++ E) (X ~ bind_sub U' ++ E').
Proof.
  intros E E' X0 U U' Hn Hwo Hwn Hsub Hclo. constructor.
  - exact Hwo.
  - exact Hwn.
  - simpl. f_equal. apply (enf_dom E E' Hn).
  - intros X U0 Hb. apply binds_cons_sub_eq in Hb. destruct Hb as [[Heq Hbeq]|Hin].
    + subst. injection Hbeq as ->. right. exists U'. split; [|split; [|split]].
      * apply binds_cons_2; reflexivity.
      * apply (wf_typ_weaken E' (X0 ~ bind_sub U' ++ E') U' Hwn (env_extends_cons_tail E' X0 (bind_sub U')) (proj1 (sub_wf E' U' _ (enf_wf_new E E' Hn) Hsub))).
      * apply (sub_weaken E' U' _ (enf_wf_new E E' Hn) Hsub (X0 ~ bind_sub U' ++ E') Hwn (env_extends_cons_tail E' X0 (bind_sub U'))).
      * intros E'' Hwf'' Hext. apply Hclo; [exact Hwf''|].
        apply (env_extends_trans E' (X0 ~ bind_sub U' ++ E') E'' (env_extends_cons_tail E' X0 (bind_sub U')) Hext).
    + destruct (enf_sub E E' Hn X U0 Hin) as [Hl|[U'' [Hb' [Hwt [Hsub' Hclo']]]]].
      * left. apply binds_cons_tail; assumption.
      * right. exists U''. split; [|split; [|split]].
        -- apply binds_cons_tail; assumption.
        -- apply (wf_typ_weaken E' (X0 ~ bind_sub U' ++ E') U'' Hwn (env_extends_cons_tail E' X0 (bind_sub U')) Hwt).
        -- apply (sub_weaken E' U'' U0 (enf_wf_new E E' Hn) Hsub' (X0 ~ bind_sub U' ++ E') Hwn (env_extends_cons_tail E' X0 (bind_sub U'))).
        -- intros E'' Hwf'' Hext. apply Hclo'; [exact Hwf''|].
           apply (env_extends_trans E' (X0 ~ bind_sub U' ++ E') E'' (env_extends_cons_tail E' X0 (bind_sub U')) Hext).
  - intros X Q Hb. apply binds_cons_qua_eq in Hb. destruct Hb as [[Heq Hbeq]|Hin].
    + subst. discriminate Hbeq.
    + destruct (enf_qua E E' Hn X Q Hin) as [Hl|[Q' [Hb' [Hwq [Hsub' Hclo']]]]].
      * left. apply binds_cons_tail; assumption.
      * right. exists Q'. split; [|split; [|split]].
        -- apply binds_cons_tail; assumption.
        -- apply (wf_qua_weaken E' (X0 ~ bind_sub U' ++ E') Q' Hwn (env_extends_cons_tail E' X0 (bind_sub U')) Hwq).
        -- apply (subqual_weaken E' Q' Q Hsub' (X0 ~ bind_sub U' ++ E') Hwn (env_extends_cons_tail E' X0 (bind_sub U'))).
        -- intros E'' Hwf'' Hext. apply Hclo'; [exact Hwf''|].
           apply (env_extends_trans E' (X0 ~ bind_sub U' ++ E') E'' (env_extends_cons_tail E' X0 (bind_sub U')) Hext).
  - intros X T Hb. apply binds_cons_typ_eq in Hb. destruct Hb as [[Heq Hbeq]|Hin].
    + subst. discriminate Hbeq.
    + apply binds_cons_tail. apply (enf_typ E E' Hn). exact Hin.
Qed.

Lemma env_narrow_cons_qua_same : forall E E' X Q,
  env_narrow_full E E' ->
  wf_env (X ~ bind_qua Q ++ E) -> wf_env (X ~ bind_qua Q ++ E') ->
  env_narrow_full (X ~ bind_qua Q ++ E) (X ~ bind_qua Q ++ E').
Proof.
  intros E E' X0 Q Hn Hwo Hwn. constructor.
  - exact Hwo.
  - exact Hwn.
  - simpl. f_equal. apply (enf_dom E E' Hn).
  - intros X U Hb. apply binds_cons_sub_eq in Hb. destruct Hb as [[Heq Hbeq]|Hin].
    + subst. discriminate Hbeq.
    + destruct (enf_sub E E' Hn X U Hin) as [Hl|[U' [Hb' [Hwt [Hsub Hclo]]]]].
      * left. apply binds_cons_tail; assumption.
      * right. exists U'. split; [|split; [|split]].
        -- apply binds_cons_tail; assumption.
        -- apply (wf_typ_weaken E' (X0 ~ bind_qua Q ++ E') U' Hwn (env_extends_cons_tail E' X0 (bind_qua Q)) Hwt).
        -- apply (sub_weaken E' U' U (enf_wf_new E E' Hn) Hsub (X0 ~ bind_qua Q ++ E') Hwn (env_extends_cons_tail E' X0 (bind_qua Q))).
        -- intros E'' Hwf'' Hext. apply Hclo; [exact Hwf''|].
           apply (env_extends_trans E' (X0 ~ bind_qua Q ++ E') E'' (env_extends_cons_tail E' X0 (bind_qua Q)) Hext).
  - intros X Q0 Hb. apply binds_cons_qua_eq in Hb. destruct Hb as [[Heq Hbeq]|Hin].
    + subst. injection Hbeq as ->. left. apply binds_cons_2; reflexivity.
    + destruct (enf_qua E E' Hn X Q0 Hin) as [Hl|[Q' [Hb' [Hwq [Hsub Hclo]]]]].
      * left. apply binds_cons_tail; assumption.
      * right. exists Q'. split; [|split; [|split]].
        -- apply binds_cons_tail; assumption.
        -- apply (wf_qua_weaken E' (X0 ~ bind_qua Q ++ E') Q' Hwn (env_extends_cons_tail E' X0 (bind_qua Q)) Hwq).
        -- apply (subqual_weaken E' Q' Q0 Hsub (X0 ~ bind_qua Q ++ E') Hwn (env_extends_cons_tail E' X0 (bind_qua Q))).
        -- intros E'' Hwf'' Hext. apply Hclo; [exact Hwf''|].
           apply (env_extends_trans E' (X0 ~ bind_qua Q ++ E') E'' (env_extends_cons_tail E' X0 (bind_qua Q)) Hext).
  - intros X T Hb. apply binds_cons_typ_eq in Hb. destruct Hb as [[Heq Hbeq]|Hin].
    + subst. discriminate Hbeq.
    + apply binds_cons_tail. apply (enf_typ E E' Hn). exact Hin.
Qed.

Lemma env_narrow_cons_qua_changed : forall E E' X Q Q',
  env_narrow_full E E' ->
  wf_env (X ~ bind_qua Q ++ E) -> wf_env (X ~ bind_qua Q' ++ E') ->
  subqual E' Q' Q ->
  (forall E'', wf_env E'' -> env_extends E' E'' ->
     forall S, subqual E'' Q S -> subqual E'' Q' S) ->
  env_narrow_full (X ~ bind_qua Q ++ E) (X ~ bind_qua Q' ++ E').
Proof.
  intros E E' X0 Q Q' Hn Hwo Hwn Hsub Hclo. constructor.
  - exact Hwo.
  - exact Hwn.
  - simpl. f_equal. apply (enf_dom E E' Hn).
  - intros X U Hb. apply binds_cons_sub_eq in Hb. destruct Hb as [[Heq Hbeq]|Hin].
    + subst. discriminate Hbeq.
    + destruct (enf_sub E E' Hn X U Hin) as [Hl|[U' [Hb' [Hwt [Hsub' Hclo']]]]].
      * left. apply binds_cons_tail; assumption.
      * right. exists U'. split; [|split; [|split]].
        -- apply binds_cons_tail; assumption.
        -- apply (wf_typ_weaken E' (X0 ~ bind_qua Q' ++ E') U' Hwn (env_extends_cons_tail E' X0 (bind_qua Q')) Hwt).
        -- apply (sub_weaken E' U' U (enf_wf_new E E' Hn) Hsub' (X0 ~ bind_qua Q' ++ E') Hwn (env_extends_cons_tail E' X0 (bind_qua Q'))).
        -- intros E'' Hwf'' Hext. apply Hclo'; [exact Hwf''|].
           apply (env_extends_trans E' (X0 ~ bind_qua Q' ++ E') E'' (env_extends_cons_tail E' X0 (bind_qua Q')) Hext).
  - intros X Q0 Hb. apply binds_cons_qua_eq in Hb. destruct Hb as [[Heq Hbeq]|Hin].
    + subst. injection Hbeq as ->. right. exists Q'. split; [|split; [|split]].
      * apply binds_cons_2; reflexivity.
      * apply (wf_qua_weaken E' (X0 ~ bind_qua Q' ++ E') Q' Hwn (env_extends_cons_tail E' X0 (bind_qua Q')) (proj1 (subqual_wf E' Q' _ (enf_wf_new E E' Hn) Hsub))).
      * apply (subqual_weaken E' Q' _ Hsub (X0 ~ bind_qua Q' ++ E') Hwn (env_extends_cons_tail E' X0 (bind_qua Q'))).
      * intros E'' Hwf'' Hext. apply Hclo; [exact Hwf''|].
        apply (env_extends_trans E' (X0 ~ bind_qua Q' ++ E') E'' (env_extends_cons_tail E' X0 (bind_qua Q')) Hext).
    + destruct (enf_qua E E' Hn X Q0 Hin) as [Hl|[Q'' [Hb' [Hwq [Hsub' Hclo']]]]].
      * left. apply binds_cons_tail; assumption.
      * right. exists Q''. split; [|split; [|split]].
        -- apply binds_cons_tail; assumption.
        -- apply (wf_qua_weaken E' (X0 ~ bind_qua Q' ++ E') Q'' Hwn (env_extends_cons_tail E' X0 (bind_qua Q')) Hwq).
        -- apply (subqual_weaken E' Q'' Q0 Hsub' (X0 ~ bind_qua Q' ++ E') Hwn (env_extends_cons_tail E' X0 (bind_qua Q'))).
        -- intros E'' Hwf'' Hext. apply Hclo'; [exact Hwf''|].
           apply (env_extends_trans E' (X0 ~ bind_qua Q' ++ E') E'' (env_extends_cons_tail E' X0 (bind_qua Q')) Hext).
  - intros X T Hb. apply binds_cons_typ_eq in Hb. destruct Hb as [[Heq Hbeq]|Hin].
    + subst. discriminate Hbeq.
    + apply binds_cons_tail. apply (enf_typ E E' Hn). exact Hin.
Qed.

Lemma env_narrow_cons_typ : forall E E' X T,
  env_narrow_full E E' ->
  wf_env (X ~ bind_typ T ++ E) -> wf_env (X ~ bind_typ T ++ E') ->
  env_narrow_full (X ~ bind_typ T ++ E) (X ~ bind_typ T ++ E').
Proof.
  intros E E' X0 T Hn Hwo Hwn. constructor.
  - exact Hwo.
  - exact Hwn.
  - simpl. f_equal. apply (enf_dom E E' Hn).
  - intros X U Hb. apply binds_cons_sub_eq in Hb. destruct Hb as [[Heq Hbeq]|Hin].
    + subst. discriminate Hbeq.
    + destruct (enf_sub E E' Hn X U Hin) as [Hl|[U' [Hb' [Hwt [Hsub Hclo]]]]].
      * left. apply binds_cons_tail; assumption.
      * right. exists U'. split; [|split; [|split]].
        -- apply binds_cons_tail; assumption.
        -- apply (wf_typ_weaken E' (X0 ~ bind_typ T ++ E') U' Hwn (env_extends_cons_tail E' X0 (bind_typ T)) Hwt).
        -- apply (sub_weaken E' U' U (enf_wf_new E E' Hn) Hsub (X0 ~ bind_typ T ++ E') Hwn (env_extends_cons_tail E' X0 (bind_typ T))).
        -- intros E'' Hwf'' Hext. apply Hclo; [exact Hwf''|].
           apply (env_extends_trans E' (X0 ~ bind_typ T ++ E') E'' (env_extends_cons_tail E' X0 (bind_typ T)) Hext).
  - intros X Q Hb. apply binds_cons_qua_eq in Hb. destruct Hb as [[Heq Hbeq]|Hin].
    + subst. discriminate Hbeq.
    + destruct (enf_qua E E' Hn X Q Hin) as [Hl|[Q' [Hb' [Hwq [Hsub Hclo]]]]].
      * left. apply binds_cons_tail; assumption.
      * right. exists Q'. split; [|split; [|split]].
        -- apply binds_cons_tail; assumption.
        -- apply (wf_qua_weaken E' (X0 ~ bind_typ T ++ E') Q' Hwn (env_extends_cons_tail E' X0 (bind_typ T)) Hwq).
        -- apply (subqual_weaken E' Q' Q Hsub (X0 ~ bind_typ T ++ E') Hwn (env_extends_cons_tail E' X0 (bind_typ T))).
        -- intros E'' Hwf'' Hext. apply Hclo; [exact Hwf''|].
           apply (env_extends_trans E' (X0 ~ bind_typ T ++ E') E'' (env_extends_cons_tail E' X0 (bind_typ T)) Hext).
  - intros X T0 Hb. apply binds_cons_typ_eq in Hb. destruct Hb as [[Heq Hbeq]|Hin].
    + subst. injection Hbeq as ->. apply binds_cons_2; reflexivity.
    + apply binds_cons_tail. apply (enf_typ E E' Hn). exact Hin.
Qed.


(* ===== inlined from /tmp/pkg/Part2.v ===== *)

Lemma wf_qua_narrow : forall E E' Q,
  env_narrow_full E E' -> wf_qua E Q -> wf_qua E' Q.
Proof.
  intros E E' Q Hn Hq. induction Hq.
  - apply wf_qua_top.
  - destruct (env_narrow_binds_qua E E' X R Hn H) as [Hl|[Q' [Hb' [Hwq Hsub]]]].
    + apply wf_qua_fvar with (R := R). exact Hl.
    + apply wf_qua_fvar with (R := Q'). exact Hb'.
  - apply wf_qua_meet; [apply IHHq1|apply IHHq2]; exact Hn.
  - apply wf_qua_join; [apply IHHq1|apply IHHq2]; exact Hn.
  - apply wf_qua_bot.
Qed.

Lemma wf_typ_narrow : forall E T,
  wf_typ E T -> forall E', env_narrow_full E E' -> wf_typ E' T
with wf_qtyp_narrow : forall E T,
  wf_qtyp E T -> forall E', env_narrow_full E E' -> wf_qtyp E' T.
Proof.
  - intros E T H. induction H using wf_typ_mut_ind
      with (P := fun E T _ => forall E', env_narrow_full E E' -> wf_typ E' T)
           (P0 := fun E T _ => forall E', env_narrow_full E E' -> wf_qtyp E' T).
    + intros E' Hn. apply wf_typ_top.
    + intros E' Hn. match goal with
      | Hb : binds ?X (bind_sub ?U) E |- _ =>
        destruct (env_narrow_binds_sub E E' X U Hn Hb) as [Hl|[U' [Hb' [Hwt Hsub]]]]
      end.
      * match goal with Hl : binds ?X (bind_sub ?U) E' |- _ => apply wf_typ_var with (U := U); exact Hl end.
      * match goal with Hb' : binds ?X (bind_sub ?U') E' |- _ => apply wf_typ_var with (U := U'); exact Hb' end.
    + intros E' Hn. apply wf_typ_arrow.
      * apply IHwf_typ. exact Hn.
      * apply IHwf_typ0. exact Hn.
    + intros E' Hn. apply wf_typ_all with (L := union L (union (dom E) (dom E'))).
      * apply IHwf_typ. exact Hn.
      * intros X Hx.
        assert (HxL : X `notin` L) by fsetdec.
        assert (Hxd : X `notin` dom E) by fsetdec.
        assert (Hxd' : X `notin` dom E') by (rewrite <- (enf_dom E E' Hn); exact Hxd).
        assert (Hwt1' : wf_typ E' T1). { apply IHwf_typ. exact Hn. }
        assert (Hwfo : wf_env (X ~ bind_sub T1 ++ E)).
        { apply wf_env_sub; [apply (enf_wf_old E E' Hn)| | exact Hxd]; assumption. }
        assert (Hwfn : wf_env (X ~ bind_sub T1 ++ E')).
        { apply wf_env_sub; [apply (enf_wf_new E E' Hn)| | exact Hxd']; assumption. }
        assert (Hrel : env_narrow_full (X ~ bind_sub T1 ++ E) (X ~ bind_sub T1 ++ E')).
        { apply env_narrow_cons_sub_same; assumption. }
        apply (H0 X HxL (X ~ bind_sub T1 ++ E') Hrel).
    + intros E' Hn. apply wf_typ_qall with (L := union L (union (dom E) (dom E'))).
      * apply wf_qua_narrow with (E := E); assumption.
      * intros X Hx.
        assert (HxL : X `notin` L) by fsetdec.
        assert (Hxd : X `notin` dom E) by fsetdec.
        assert (Hxd' : X `notin` dom E') by (rewrite <- (enf_dom E E' Hn); exact Hxd).
        assert (Hwq' : wf_qua E' T1). { apply wf_qua_narrow with (E := E); assumption. }
        assert (Hwfo : wf_env (X ~ bind_qua T1 ++ E)).
        { apply wf_env_qua; [apply (enf_wf_old E E' Hn)| | exact Hxd]; assumption. }
        assert (Hwfn : wf_env (X ~ bind_qua T1 ++ E')).
        { apply wf_env_qua; [apply (enf_wf_new E E' Hn)| | exact Hxd']; assumption. }
        assert (Hrel : env_narrow_full (X ~ bind_qua T1 ++ E) (X ~ bind_qua T1 ++ E')).
        { apply env_narrow_cons_qua_same; assumption. }
        apply (H X HxL (X ~ bind_qua T1 ++ E') Hrel).
    + intros E' Hn. apply wf_typ_sum; [apply IHwf_typ|apply IHwf_typ0]; exact Hn.
    + intros E' Hn. apply wf_typ_pair; [apply IHwf_typ|apply IHwf_typ0]; exact Hn.
    + intros E' Hn. apply wf_qtyp_qtyp.
      * apply wf_qua_narrow with (E := E); assumption.
      * apply IHwf_typ. exact Hn.
  - intros E T H E' Hn. destruct T as [Q T]. inversion H; subst.
    apply wf_qtyp_qtyp.
    + apply wf_qua_narrow with (E := E); assumption.
    + apply wf_typ_narrow with (E := E); assumption.
Qed.

Lemma wf_env_narrow : forall E E',
  env_narrow_full E E' -> wf_env E'.
Proof. intros. apply (enf_wf_new E E' H). Qed.


(* ===== inlined from /tmp/merge/Helpers_clean.v ===== *)
Lemma subqual_trans_fvar : forall E S X,
  subqual E S (qua_fvar X) -> forall U, subqual E (qua_fvar X) U -> subqual E S U.
Proof.
  intros E S X H U H2. dependent induction H.
  - (* bot *) apply subqual_bot; [assumption|].
    exact (proj2 (subqual_wf E (qua_fvar X) U H H2)).
  - (* refl *) exact H2.
  - (* trans_qvar *) eapply subqual_trans_qvar; [exact H|].
    eapply IHsubqual; [reflexivity|exact H2].
  - (* join_elim *) apply subqual_join_elim.
    + eapply IHsubqual1; [reflexivity|exact H2].
    + eapply IHsubqual2; [reflexivity|exact H2].
  - (* meet_eliml *) apply subqual_meet_eliml.
    + eapply IHsubqual; [reflexivity|exact H2].
    + assumption.
  - (* meet_elimr *) apply subqual_meet_elimr.
    + assumption.
    + eapply IHsubqual; [reflexivity|exact H2].
Qed.

Lemma subqual_after_bot : forall E S,
  subqual E S qua_bot -> forall U, wf_env E -> wf_qua E U -> subqual E S U.
Proof.
  intros E S H U Hwf HU. dependent induction H.
  - (* bot *) apply subqual_bot; assumption.
  - (* trans_qvar *) eapply subqual_trans_qvar; [exact H|].
    eapply IHsubqual; [reflexivity|exact Hwf|exact HU].
  - (* join_elim *) apply subqual_join_elim.
    + eapply IHsubqual1; [reflexivity|exact Hwf|exact HU].
    + eapply IHsubqual2; [reflexivity|exact Hwf|exact HU].
  - (* meet_eliml *) apply subqual_meet_eliml.
    + eapply IHsubqual; [reflexivity|exact Hwf|exact HU].
    + assumption.
  - (* meet_elimr *) apply subqual_meet_elimr.
    + assumption.
    + eapply IHsubqual; [reflexivity|exact Hwf|exact HU].
Qed.


(* ===== inlined from /tmp/pkg/FromLattice.v ===== *)

Lemma subqual_from_join : forall E R1 R2 Q,
  (forall S, subqual E S R1 -> subqual E S Q) ->
  (forall S, subqual E S R2 -> subqual E S Q) ->
  wf_env E -> wf_qua E Q ->
  forall S, subqual E S (qua_join R1 R2) -> subqual E S Q.
Proof.
  intros E R1 R2 Q H1 H2 Hwf HQ S dd.
  dependent induction dd.
  - (* bot *) apply subqual_bot; assumption.
  - (* trans_qvar *) eapply subqual_trans_qvar; [exact H|].
    eapply IHdd; [exact H1|exact H2|exact Hwf|exact HQ|reflexivity].
  - (* join_inl *) eapply H1; eassumption.
  - (* join_inr *) eapply H2; eassumption.
  - (* join_elim *) apply subqual_join_elim.
    + eapply IHdd1; [exact H1|exact H2|exact Hwf|exact HQ|reflexivity].
    + eapply IHdd2; [exact H1|exact H2|exact Hwf|exact HQ|reflexivity].
  - (* meet_eliml *) apply subqual_meet_eliml.
    + eapply IHdd; [exact H1|exact H2|exact Hwf|exact HQ|reflexivity].
    + assumption.
  - (* meet_elimr *) apply subqual_meet_elimr.
    + assumption.
    + eapply IHdd; [exact H1|exact H2|exact Hwf|exact HQ|reflexivity].
Qed.

Lemma subqual_from_meet_l : forall E R1 R2 Q,
  (forall S, subqual E S R1 -> subqual E S Q) ->
  wf_qua E R2 -> wf_env E -> wf_qua E Q ->
  forall S, subqual E S (qua_meet R1 R2) -> subqual E S Q.
Proof.
  intros E R1 R2 Q H1 HR2 Hwf HQ S dd.
  dependent induction dd.
  - (* bot *) apply subqual_bot; assumption.
  - (* trans_qvar *) eapply subqual_trans_qvar; [exact H|].
    eapply IHdd; [exact H1|exact HR2|exact Hwf|exact HQ|reflexivity].
  - (* join_elim *) apply subqual_join_elim.
    + eapply IHdd1; [exact H1|exact HR2|exact Hwf|exact HQ|reflexivity].
    + eapply IHdd2; [exact H1|exact HR2|exact Hwf|exact HQ|reflexivity].
  - (* meet_eliml *) apply subqual_meet_eliml.
    + eapply IHdd; [exact H1|exact HR2|exact Hwf|exact HQ|reflexivity].
    + assumption.
  - (* meet_elimr *) apply subqual_meet_elimr.
    + assumption.
    + eapply IHdd; [exact H1|exact HR2|exact Hwf|exact HQ|reflexivity].
  - (* meet_intro *) eapply H1; eassumption.
Qed.

Lemma subqual_from_meet_r : forall E R1 R2 Q,
  (forall S, subqual E S R2 -> subqual E S Q) ->
  wf_qua E R1 -> wf_env E -> wf_qua E Q ->
  forall S, subqual E S (qua_meet R1 R2) -> subqual E S Q.
Proof.
  intros E R1 R2 Q H2 HR1 Hwf HQ S dd.
  dependent induction dd.
  - (* bot *) apply subqual_bot; assumption.
  - (* trans_qvar *) eapply subqual_trans_qvar; [exact H|].
    eapply IHdd; [exact H2|exact HR1|exact Hwf|exact HQ|reflexivity].
  - (* join_elim *) apply subqual_join_elim.
    + eapply IHdd1; [exact H2|exact HR1|exact Hwf|exact HQ|reflexivity].
    + eapply IHdd2; [exact H2|exact HR1|exact Hwf|exact HQ|reflexivity].
  - (* meet_eliml *) apply subqual_meet_eliml.
    + eapply IHdd; [exact H2|exact HR1|exact Hwf|exact HQ|reflexivity].
    + assumption.
  - (* meet_elimr *) apply subqual_meet_elimr.
    + assumption.
    + eapply IHdd; [exact H2|exact HR1|exact Hwf|exact HQ|reflexivity].
  - (* meet_intro *) eapply H2; eassumption.
Qed.


(* ===== inlined from /tmp/merge/SqT9_clean.v ===== *)
Lemma subqual_trans2 : forall E S T U,
  wf_env E -> subqual E S T -> subqual E T U -> subqual E S U.
Proof.
  intros E S T U Hwf d e. revert S d.
  induction e using subqual_ind; intros S d.
  - (* top *) match goal with
      | d : subqual ?E ?S ?T |- subqual ?E ?S qua_top =>
          apply subqual_top; [exact Hwf| exact (proj1 (subqual_wf E S T Hwf d))]
      end.
  - (* bot *) match goal with
      | d : subqual ?E ?S qua_bot, HQ : wf_qua ?E ?Q |- subqual ?E ?S ?Q =>
          eapply subqual_after_bot; [exact d|exact Hwf|exact HQ]
      end.
  - (* refl *) exact d.
  - (* trans_qvar *) assert (He : subqual E (qua_fvar X) Q) by
      (eapply subqual_trans_qvar; [exact H|exact e]).
    eapply subqual_trans_fvar; [exact d|exact He].
  - (* join_inl *) apply subqual_join_inl.
    + eapply IHe; [exact Hwf|exact d].
    + assumption.
  - (* join_inr *) apply subqual_join_inr.
    + assumption.
    + eapply IHe; [exact Hwf|exact d].
  - (* join_elim *) 
    pose proof (proj2 (subqual_wf E R1 Q Hwf e1)) as HwQ.
    apply (subqual_from_join E R1 R2 Q
      (fun S0 h => IHe1 Hwf S0 h) (fun S0 h => IHe2 Hwf S0 h) Hwf HwQ S d).
  - (* meet_eliml *)
    pose proof (proj2 (subqual_wf E R1 Q Hwf e)) as HwQ.
    apply (subqual_from_meet_l E R1 R2 Q
      (fun S0 h => IHe Hwf S0 h) H Hwf HwQ S d).
  - (* meet_elimr *)
    pose proof (proj2 (subqual_wf E R2 Q Hwf e)) as HwQ.
    apply (subqual_from_meet_r E R1 R2 Q
      (fun S0 h => IHe Hwf S0 h) H Hwf HwQ S d).
  - (* meet_intro *) apply subqual_meet_intro.
    + eapply IHe1; [exact Hwf|exact d].
    + eapply IHe2; [exact Hwf|exact d].
Qed.

Lemma subqual_trans : forall E Q R S,
  wf_env E -> subqual E Q R -> subqual E R S -> subqual E Q S.
Proof. intros. eapply subqual_trans2; eassumption. Qed.


(* ===== inlined from /tmp/pkg/Part3.v ===== *)

Lemma subqual_narrow : forall E Q R,
  wf_env E -> subqual E Q R ->
  forall E', wf_env E' -> env_narrow_full E E' -> subqual E' Q R.
Proof.
  intros E Q R Hwf d. induction d using subqual_ind; intros E' Hwf' Hn.
  - (* top *) apply subqual_top; [exact Hwf'|].
    apply wf_qua_narrow with (E := E); assumption.
  - (* bot *) apply subqual_bot; [exact Hwf'|].
    apply wf_qua_narrow with (E := E); assumption.
  - (* refl *) apply subqual_refl_qvar; [exact Hwf'|].
    apply wf_qua_narrow with (E := E); assumption.
  - (* trans_qvar *) destruct (env_narrow_binds_qua E E' X R Hn H) as
      [Hl|[R' [Hb' [Hwq' [Hsub' Hclo']]]]].
    + eapply subqual_trans_qvar; [exact Hl|]. apply IHd; assumption.
    + eapply subqual_trans_qvar; [exact Hb'|].
      apply Hclo'.
      * exact Hwf'.
      * apply env_extends_refl; exact Hwf'.
      * apply IHd; assumption.
  - (* join_inl *) apply subqual_join_inl.
    + apply IHd; assumption.
    + apply wf_qua_narrow with (E := E); assumption.
  - (* join_inr *) apply subqual_join_inr.
    + apply wf_qua_narrow with (E := E); assumption.
    + apply IHd; assumption.
  - (* join_elim *) apply subqual_join_elim; [apply IHd1; assumption|apply IHd2; assumption].
  - (* meet_eliml *) apply subqual_meet_eliml.
    + apply IHd; assumption.
    + apply wf_qua_narrow with (E := E); assumption.
  - (* meet_elimr *) apply subqual_meet_elimr.
    + apply wf_qua_narrow with (E := E); assumption.
    + apply IHd; assumption.
  - (* meet_intro *) apply subqual_meet_intro; [apply IHd1; assumption|apply IHd2; assumption].
Qed.

Lemma subqual_post : forall E Q R,
  wf_env E -> subqual E Q R ->
  forall E', wf_env E' -> env_extends E E' ->
  forall S, subqual E' R S -> subqual E' Q S.
Proof.
  intros E Q R Hwf Hd E' Hwf' Hext S He.
  pose proof (subqual_weaken E Q R Hd E' Hwf' Hext) as Hd'.
  exact (subqual_trans E' Q R S Hwf' Hd' He).
Qed.

Lemma subqual_pre : forall E Q R,
  wf_env E -> subqual E Q R ->
  forall E', wf_env E' -> env_extends E E' ->
  forall S, subqual E' S Q -> subqual E' S R.
Proof.
  intros E Q R Hwf Hd E' Hwf' Hext S He.
  pose proof (subqual_weaken E Q R Hd E' Hwf' Hext) as Hd'.
  exact (subqual_trans E' S Q R Hwf' He Hd').
Qed.

Lemma subqual_narrow_ext : forall E Q R,
  wf_env E -> subqual E Q R ->
  forall E', env_narrow_full E E' ->
  forall E'', wf_env E'' -> env_extends E' E'' -> subqual E'' Q R.
Proof.
  intros E Q R Hwf Hd E' Hn E'' Hwf'' Hext.
  pose proof (subqual_narrow E Q R Hwf Hd E' (enf_wf_new E E' Hn) Hn) as Hd'.
  exact (subqual_weaken E' Q R Hd' E'' Hwf'' Hext).
Qed.

Lemma subqual_wf_env : forall E Q R, subqual E Q R -> wf_env E.
Proof.
  intros E Q R H. induction H; try assumption;
    try (eapply IHsubqual; eassumption);
    try (eapply IHsubqual1; eassumption);
    try (eapply IHsubqual2; eassumption).
Qed.

Lemma subqual_trans_nowf : forall E Q R S,
  subqual E Q R -> subqual E R S -> subqual E Q S.
Proof.
  intros E Q R S H1 H2.
  exact (subqual_trans E Q R S (subqual_wf_env E Q R H1) H1 H2).
Qed.


(* ===== inlined from /tmp/pkg/PkgNarrow.v ===== *)

Lemma sub_narrow : forall E S T,
  wf_env E -> sub E S T ->
  forall E', wf_env E' -> env_narrow_full E E' -> sub E' S T.
Proof.
  - intros E S T Hwf d. revert Hwf. induction d using sub_mut_ind
      with (P := fun E S T _ => wf_env E -> forall E', wf_env E' -> env_narrow_full E E' -> sub E' S T)
           (P0 := fun E S T _ => wf_env E -> forall E', wf_env E' -> env_narrow_full E E' -> subqtype E' S T).
    + (* top *) intros HE E' HE' Hn. apply sub_top; [exact HE'|].
      eapply wf_typ_narrow; eassumption.
    + (* refl *) intros HE E' HE' Hn. apply sub_refl_tvar; [exact HE'|].
      eapply wf_typ_narrow; eassumption.
    + (* trans_tvar *) intros HE E' HE' Hn.
      destruct (env_narrow_binds_sub E E' X U Hn b) as
        [Hl|[U' [Hb' [Hwt [Hsub Hclo]]]]].
      * eapply sub_trans_tvar; [exact Hl|]. apply IHd; assumption.
      * eapply sub_trans_tvar; [exact Hb'|].
        exact (Hclo E' HE' (env_extends_refl E') T (IHd HE E' HE' Hn)).
    + (* arrow *) intros HE E' HE' Hn. apply sub_arrow.
      * apply IHd; assumption.
      * apply IHd0; assumption.
    + (* all *) intros HE E' HE' Hn.
      apply sub_all with (L := union L (union (dom E) (dom E'))).
      * apply IHd; assumption.
      * intros X Hx.
        assert (HxL : X `notin` L) by fsetdec.
        assert (Hxd : X `notin` dom E) by fsetdec.
        assert (Hxd' : X `notin` dom E') by (rewrite <- (enf_dom E E' Hn); exact Hxd).
        assert (Hwt : wf_typ E T1) by (apply (proj1 (sub_wf E T1 S1 HE d))).
        assert (Hwt' : wf_typ E' T1). { eapply wf_typ_narrow; eassumption. }
        assert (Hwo : wf_env (X ~ bind_sub T1 ++ E)).
        { apply wf_env_sub; [exact HE|exact Hwt|exact Hxd]. }
        assert (Hwn : wf_env (X ~ bind_sub T1 ++ E')).
        { apply wf_env_sub; [exact HE'|exact Hwt'|exact Hxd']. }
        assert (Hrel : env_narrow_full (X ~ bind_sub T1 ++ E) (X ~ bind_sub T1 ++ E')).
        { apply env_narrow_cons_sub_same; assumption. }
        exact (H X HxL Hwo (X ~ bind_sub T1 ++ E') Hwn Hrel).
    + (* qall *) intros HE E' HE' Hn.
      apply sub_qall with (L := union L (union (dom E) (dom E'))).
      * eapply subqual_narrow; [exact HE|exact s|exact HE'|exact Hn].
      * intros X Hx.
        assert (HxL : X `notin` L) by fsetdec.
        assert (Hxd : X `notin` dom E) by fsetdec.
        assert (Hxd' : X `notin` dom E') by (rewrite <- (enf_dom E E' Hn); exact Hxd).
        assert (Hwq : wf_qua E T1) by (apply (proj1 (subqual_wf E T1 S1 HE s))).
        assert (Hwq' : wf_qua E' T1). { eapply wf_qua_narrow; eassumption. }
        assert (Hwo : wf_env (X ~ bind_qua T1 ++ E)).
        { apply wf_env_qua; [exact HE|exact Hwq|exact Hxd]. }
        assert (Hwn : wf_env (X ~ bind_qua T1 ++ E')).
        { apply wf_env_qua; [exact HE'|exact Hwq'|exact Hxd']. }
        assert (Hrel : env_narrow_full (X ~ bind_qua T1 ++ E) (X ~ bind_qua T1 ++ E')).
        { apply env_narrow_cons_qua_same; assumption. }
        exact (H X HxL Hwo (X ~ bind_qua T1 ++ E') Hwn Hrel).
    + (* sum *) intros HE E' HE' Hn. apply sub_sum; [apply IHd|apply IHd0]; assumption.
    + (* pair *) intros HE E' HE' Hn. apply sub_pair; [apply IHd|apply IHd0]; assumption.
  + (* qtyp *) intros HE E' HE' Hn.
    match goal with
    | Hs : subqual E ?Q1 ?Q2, Ht : sub E ?T1 ?T2,
      IH : wf_env E -> forall E', wf_env E' -> env_narrow_full E E' -> sub E' ?T1 ?T2 |- _ =>
        apply sub_qtyp_qtyp;
        [ eapply subqual_narrow; [exact HE|exact Hs|exact HE'|exact Hn]
        | exact (IH HE E' HE' Hn) ]
    end.
Qed.

Lemma subqtype_narrow : forall E S T,
  wf_env E -> subqtype E S T ->
  forall E', wf_env E' -> env_narrow_full E E' -> subqtype E' S T.
Proof.
  intros E S T Hwf st E' HE' Hn. inversion st; subst.
  match goal with
  | Hs : subqual E ?Q1 ?Q2, Ht : sub E ?T1 ?T2 |- _ =>
      apply sub_qtyp_qtyp;
      [ eapply subqual_narrow; [exact Hwf|exact Hs|exact HE'|exact Hn]
      | eapply sub_narrow; [exact Hwf|exact Ht|exact HE'|exact Hn] ]
  end.
Qed.


(* ===== inlined from /tmp/w7/Size.v ===== *)

Fixpoint sz_typ (T : typ) : nat :=
  match T with
  | typ_top => 1
  | typ_bvar _ => 1
  | typ_fvar _ => 1
  | typ_arrow T1 T2 => S (sz_qtyp T1 + sz_qtyp T2)
  | typ_all T1 T2 => S (sz_typ T1 + sz_qtyp T2)
  | typ_qall _ T => S (sz_qtyp T)
  | typ_sum T1 T2 => S (sz_qtyp T1 + sz_qtyp T2)
  | typ_pair T1 T2 => S (sz_qtyp T1 + sz_qtyp T2)
  | typ_ref T1 => S (sz_qtyp T1)
  end
with sz_qtyp (T : qtyp) : nat :=
  match T with qtyp_qtyp _ T => sz_typ T end.

Lemma sz_open_tt : forall T j U,
  sz_typ (open_tt_rec j (typ_fvar U) T) = sz_typ T.
Proof.
  intros T. induction T using typ_mut_ind
    with (P := fun T => forall j U, sz_typ (open_tt_rec j (typ_fvar U) T) = sz_typ T)
         (P0 := fun T => forall j U, sz_qtyp (open_tqt_rec j (typ_fvar U) T) = sz_qtyp T).
  - intros; reflexivity.
  - intros j U. simpl. destruct (j == n); reflexivity.
  - intros; reflexivity.
  - intros j U. simpl. f_equal; eauto.
  - intros j U. simpl. f_equal; eauto.
  - intros j U. simpl. f_equal; eauto.
  - intros j U. simpl. f_equal; eauto.
  - intros j U. simpl. f_equal; eauto.
  - intros j U. simpl. f_equal; eauto.
  - intros j U. simpl. eauto.
Qed.

Lemma sz_open_tqt : forall T j U,
  sz_qtyp (open_tqt_rec j (typ_fvar U) T) = sz_qtyp T.
Proof.
  intros T j U.
  assert (H := sz_open_tt (typ_ref T) j U).
  simpl in H. apply Nat.succ_inj in H. exact H.
Qed.

Lemma sz_open_qt : forall T j R,
  sz_typ (open_qt_rec j (qua_fvar R) T) = sz_typ T.
Proof.
  intros T. induction T using typ_mut_ind
    with (P := fun T => forall j R, sz_typ (open_qt_rec j (qua_fvar R) T) = sz_typ T)
         (P0 := fun T => forall j R, sz_qtyp (open_qqt_rec j (qua_fvar R) T) = sz_qtyp T).
  - intros; reflexivity.
  - intros j R. simpl. destruct (j == n); reflexivity.
  - intros; reflexivity.
  - intros j R. simpl. f_equal; eauto.
  - intros j R. simpl. f_equal; eauto.
  - intros j R. simpl. f_equal; eauto.
  - intros j R. simpl. f_equal; eauto.
  - intros j R. simpl. f_equal; eauto.
  - intros j R. simpl. f_equal; eauto.
  - intros j R. simpl. eauto.
Qed.

Lemma sz_open_qqt : forall T j R,
  sz_qtyp (open_qqt_rec j (qua_fvar R) T) = sz_qtyp T.
Proof.
  intros T j R.
  assert (H := sz_open_qt (typ_ref T) j R).
  simpl in H. apply Nat.succ_inj in H. exact H.
Qed.

Lemma sz_all_dom : forall T1 T2, sz_typ T1 < sz_typ (typ_all T1 T2).
Proof. intros. simpl. lia. Qed.
Lemma sz_all_body : forall T1 T2, sz_qtyp T2 < sz_typ (typ_all T1 T2).
Proof. intros. simpl. lia. Qed.
Lemma sz_qall_body : forall Q T, sz_qtyp T < sz_typ (typ_qall Q T).
Proof. intros. simpl. lia. Qed.
Lemma sz_arrow_dom : forall T1 T2, sz_qtyp T1 < sz_typ (typ_arrow T1 T2).
Proof. intros. simpl. lia. Qed.
Lemma sz_arrow_cod : forall T1 T2, sz_qtyp T2 < sz_typ (typ_arrow T1 T2).
Proof. intros. simpl. lia. Qed.
Lemma sz_sum_l : forall T1 T2, sz_qtyp T1 < sz_typ (typ_sum T1 T2).
Proof. intros. simpl. lia. Qed.
Lemma sz_sum_r : forall T1 T2, sz_qtyp T2 < sz_typ (typ_sum T1 T2).
Proof. intros. simpl. lia. Qed.
Lemma sz_pair_l : forall T1 T2, sz_qtyp T1 < sz_typ (typ_pair T1 T2).
Proof. intros. simpl. lia. Qed.
Lemma sz_pair_r : forall T1 T2, sz_qtyp T2 < sz_typ (typ_pair T1 T2).
Proof. intros. simpl. lia. Qed.

Lemma sz_typ_pos : forall T, 1 <= sz_typ T.
Proof. intros T. destruct T; simpl; lia. Qed.
Lemma sz_qtyp_pos : forall T, 1 <= sz_qtyp T.
Proof. intros [Q T]. simpl. apply sz_typ_pos. Qed.


(* ===== inlined from /tmp/w7/TransSize.v ===== *)

Definition A (n : nat) : Prop :=
  forall E S T U, wf_env E -> sz_typ T <= n -> sub E S T -> sub E T U -> sub E S U.
Definition B (n : nat) : Prop :=
  forall E S T U, wf_env E -> sz_qtyp T <= n -> subqtype E S T -> subqtype E T U -> subqtype E S U.

Lemma subqtype_inv_parts : forall E S T,
  subqtype E S T ->
  exists Q1 T1 Q2 T2, S = qtyp_qtyp Q1 T1 /\ T = qtyp_qtyp Q2 T2 /\
    subqual E Q1 Q2 /\ sub E T1 T2.
Proof.
  intros E S T H. inversion H; subst.
  match goal with
  | Hs : subqual E ?Q1 ?Q2, Ht : sub E ?T1 ?T2 |- _ =>
      exists Q1, T1, Q2, T2; repeat split; assumption
  end.
Qed.

Lemma trans_pair : forall n, A n /\ B n.
Proof.
  intros n. induction n as [n IH] using lt_wf_ind.
  assert (HA : A n).
  { unfold A. intros E S T U Hwf Hsz d1 d2.
    revert U Hwf Hsz d2.
    unfold A in IH.
    change (forall U : typ,
      wf_env E -> sz_typ T <= n -> sub E T U -> sub E S U).
    induction d1 using sub_mut_ind
      with (P := fun E S T _ => forall U, wf_env E -> sz_typ T <= n -> sub E T U -> sub E S U)
           (P0 := fun _ _ _ _ => True).
    + (* top *) intros U Hwf' Hsz' d2. inversion d2; subst.
      apply sub_top; [exact Hwf'|exact w0].
    + (* refl *) intros U Hwf' Hsz' d2. exact d2.
    + (* trans_tvar *) intros U0 Hwf' Hsz' d2.
      eapply sub_trans_tvar; [exact b|].
      match goal with
      | IHx : forall U1, wf_env E -> sz_typ T <= n -> sub E T U1 -> sub E U U1 |- _ =>
          apply (IHx U0 Hwf' Hsz' d2)
      end.
    + (* arrow *) intros U0 Hwf' Hsz' d2.
      assert (Hnpos : 0 < n) by (pose proof (sz_typ_pos (typ_arrow T1 T2)); lia).
      dependent destruction d2.
      * (* top *) apply sub_top; [exact Hwf'|].
        exact (proj1 (sub_wf E (typ_arrow S1 S2) (typ_arrow T1 T2) Hwf'
          (sub_arrow E S1 S2 T1 T2 s s0))).
      * (* arrow *) apply sub_arrow.
        -- (* U1 <: S1 *) 
           destruct (IH (sz_qtyp T1) ltac:(pose proof (sz_arrow_dom T1 T2); lia))
             as [HA1 HB1].
           eapply HB1.
           ++ exact Hwf'.
           ++ apply le_n.
           ++ exact H.
           ++ exact s.
        -- destruct (IH (sz_qtyp T2) ltac:(pose proof (sz_arrow_cod T1 T2); lia))
             as [HA2 HB2].
           eapply HB2.
           ++ exact Hwf'.
           ++ apply le_n.
           ++ exact s0.
           ++ exact H0.
    + (* all *) intros U0 Hwf' Hsz' d2.
      assert (Hnpos : 0 < n) by (pose proof (sz_typ_pos (typ_all T1 T2)); lia).
      dependent destruction d2.
      * (* top *) apply sub_top; [exact Hwf'|].
        exact (proj1 (sub_wf E (typ_all S1 S2) (typ_all T1 T2) Hwf'
          (sub_all L E S1 S2 T1 T2 d1 s))).
      * (* all *)
        set (L' := union L (union L0 (dom E))).
        apply sub_all with (L := L').
        -- (* domain *)
           destruct (IH (sz_typ T1) ltac:(pose proof (sz_all_dom T1 T2); lia))
             as [HA1 HB1].
           eapply HA1.
           ++ exact Hwf'.
           ++ exact (le_n (sz_typ T1)).
           ++ exact d2.
           ++ exact d1.
        -- intros X HX.
           assert (HXL : X `notin` L) by (unfold L' in HX; fsetdec).
           assert (HXL0 : X `notin` L0) by (unfold L' in HX; fsetdec).
           assert (HXd : X `notin` dom E) by (unfold L' in HX; fsetdec).
           set (Eold := X ~ bind_sub T1 ++ E).
           set (Enew := X ~ bind_sub T0 ++ E).
           assert (HwtT : wf_typ E T1) by exact (proj1 (sub_wf E T1 S1 Hwf' d1)).
           assert (HwtC : wf_typ E T0) by exact (proj1 (sub_wf E T0 T1 Hwf' d2)).
           assert (Hwfo : wf_env Eold).
           { apply wf_env_sub; [exact Hwf'|exact HwtT|exact HXd]. }
           assert (Hwfn : wf_env Enew).
           { apply wf_env_sub; [exact Hwf'|exact HwtC|exact HXd]. }
           assert (HsubT0T1 : sub Enew T0 T1).
           { eapply sub_weaken; [exact Hwf'|exact d2|exact Hwfn|].
             apply env_extends_cons_tail. }
           assert (Hclo : forall E'' , wf_env E'' -> env_extends E E'' ->
               forall W, sub E'' T1 W -> sub E'' T0 W).
           { intros E'' Hwf'' Hext W HW.
             destruct (IH (sz_typ T1) ltac:(pose proof (sz_all_dom T1 T2); lia))
               as [HA1 HB1].
             eapply HA1.
             - exact Hwf''.
             - apply le_n.
             - eapply sub_weaken; [exact Hwf'|exact d2|exact Hwf''|exact Hext].
             - exact HW. }
           assert (Hrel : env_narrow_full Eold Enew).
           { apply env_narrow_cons_sub_changed with (E := E) (E' := E)
               (X := X) (U := T1) (U' := T0).
             - apply env_narrow_refl; exact Hwf'.
             - exact Hwfo.
             - exact Hwfn.
             - exact d2.
             - exact Hclo. }
           assert (Hnb : subqtype Enew (open_tqt S2 X) (open_tqt T2 X)).
           { eapply subqtype_narrow; [exact Hwfo| |exact Hwfn|exact Hrel].
             apply s; exact HXL. }
           pose proof (H0 X HXL0) as Hd2b.
           destruct (IH (sz_qtyp T2) ltac:(pose proof (sz_all_body T1 T2); lia))
             as [HA2 HB2].
           eapply HB2.
           ++ exact Hwfn.
           ++ pose proof (sz_open_tqt T2 0 X) as Hz; rewrite Hz; apply le_n.
           ++ exact Hnb.
           ++ exact Hd2b.
    + (* qall *) intros U0 Hwf' Hsz' d2.
      assert (Hnpos : 0 < n) by (pose proof (sz_typ_pos (typ_qall T1 T2)); lia).
      dependent destruction d2.
      * apply sub_top; [exact Hwf'|].
        exact (proj1 (sub_wf E (typ_qall S1 S2) (typ_qall T1 T2) Hwf'
          (sub_qall L E S1 S2 T1 T2 s s0))).
      * set (L' := union L (union L0 (dom E))).
        apply sub_qall with (L := L').
        -- (* qualifier *) eapply subqual_trans_nowf; [exact H0|exact s].
        -- intros X HX.
           assert (HXL : X `notin` L) by (unfold L' in HX; fsetdec).
           assert (HXL0 : X `notin` L0) by (unfold L' in HX; fsetdec).
           assert (HXd : X `notin` dom E) by (unfold L' in HX; fsetdec).
           set (Eold := X ~ bind_qua T1 ++ E).
           set (Enew := X ~ bind_qua T0 ++ E).
           assert (HwqT : wf_qua E T1) by exact (proj1 (subqual_wf E T1 S1 Hwf' s)).
           assert (HwqC : wf_qua E T0) by exact (proj1 (subqual_wf E T0 T1 Hwf' H0)).
           assert (Hwfo : wf_env Eold).
           { apply wf_env_qua; [exact Hwf'|exact HwqT|exact HXd]. }
           assert (Hwfn : wf_env Enew).
           { apply wf_env_qua; [exact Hwf'|exact HwqC|exact HXd]. }
           assert (Hclo : forall E'' , wf_env E'' -> env_extends E E'' ->
               forall W, subqual E'' T1 W -> subqual E'' T0 W).
           { intros E'' Hwf'' Hext W HW.
             eapply subqual_trans_nowf.
             - eapply subqual_weaken; [exact H0|exact Hwf''|exact Hext].
             - exact HW. }
           assert (Hrel : env_narrow_full Eold Enew).
           { apply env_narrow_cons_qua_changed with (E := E) (E' := E)
               (X := X) (Q := T1) (Q' := T0).
             - apply env_narrow_refl; exact Hwf'.
             - exact Hwfo.
             - exact Hwfn.
             - exact H0.
             - exact Hclo. }
           assert (Hnb : subqtype Enew (open_qqt S2 X) (open_qqt T2 X)).
           { eapply subqtype_narrow; [exact Hwfo| |exact Hwfn|exact Hrel].
             apply s0; exact HXL. }
           pose proof (H1 X HXL0) as Hd2b.
           destruct (IH (sz_qtyp T2) ltac:(pose proof (sz_qall_body T1 T2); lia))
             as [HA2 HB2].
           eapply HB2.
           ++ exact Hwfn.
           ++ pose proof (sz_open_qqt T2 0 X) as Hz; rewrite Hz; apply le_n.
           ++ exact Hnb.
           ++ exact Hd2b.
    + (* sum *) intros U0 Hwf' Hsz' d2.
      assert (Hnpos : 0 < n) by (pose proof (sz_typ_pos (typ_sum T1 T2)); lia).
      dependent destruction d2.
      * apply sub_top; [exact Hwf'|].
        exact (proj1 (sub_wf E (typ_sum S1 S2) (typ_sum T1 T2) Hwf'
          (sub_sum E S1 S2 T1 T2 s s0))).
      * apply sub_sum.
        -- destruct (IH (sz_qtyp T1) ltac:(pose proof (sz_sum_l T1 T2); lia))
             as [HA1 HB1].
           eapply HB1; [exact Hwf'|apply le_n|exact s|exact H].
        -- destruct (IH (sz_qtyp T2) ltac:(pose proof (sz_sum_r T1 T2); lia))
             as [HA2 HB2].
           eapply HB2; [exact Hwf'|apply le_n|exact s0|exact H0].
    + (* pair *) intros U0 Hwf' Hsz' d2.
      assert (Hnpos : 0 < n) by (pose proof (sz_typ_pos (typ_pair T1 T2)); lia).
      dependent destruction d2.
      * apply sub_top; [exact Hwf'|].
        exact (proj1 (sub_wf E (typ_pair S1 S2) (typ_pair T1 T2) Hwf'
          (sub_pair E S1 S2 T1 T2 s s0))).
      * apply sub_pair.
        -- destruct (IH (sz_qtyp T1) ltac:(pose proof (sz_pair_l T1 T2); lia))
             as [HA1 HB1].
           eapply HB1; [exact Hwf'|apply le_n|exact s|exact H].
        -- destruct (IH (sz_qtyp T2) ltac:(pose proof (sz_pair_r T1 T2); lia))
             as [HA2 HB2].
           eapply HB2; [exact Hwf'|apply le_n|exact s0|exact H0].
    + (* qtyp subqtype premise case of mutual scheme *) exact I.
  }
  assert (HB : B n).
  { unfold B. intros E S T U Hwf Hsz st1 st2.
    destruct S as [Qa Ta]. destruct T as [Qb Tb]. destruct U as [Qd Td].
    inversion st1; subst. inversion st2; subst.
    apply sub_qtyp_qtyp.
    - match goal with
      | H1 : subqual E Qa Qb, H2 : subqual E Qb Qd |- subqual E Qa Qd =>
          eapply subqual_trans_nowf; [exact H1|exact H2]
      end.
    - match goal with
      | H1 : sub E Ta Tb, H2 : sub E Tb Td |- sub E Ta Td =>
          eapply HA; [exact Hwf| |exact H1|exact H2]
      end.
      simpl. exact Hsz.
  }
  split; assumption.
Qed.

Lemma sub_trans_size : forall E S T U,
  wf_env E -> sub E S T -> sub E T U -> sub E S U.
Proof.
  intros. exact (proj1 (trans_pair (sz_typ T)) E S T U H (le_n (sz_typ T)) H0 H1).
Qed.

Lemma subqtype_trans_size : forall E S T U,
  wf_env E -> subqtype E S T -> subqtype E T U -> subqtype E S U.
Proof.
  intros. exact (proj2 (trans_pair (sz_qtyp T)) E S T U H (le_n (sz_qtyp T)) H0 H1).
Qed.

Lemma sub_post_env : forall E S T (d : sub E S T),
  wf_env E -> forall E', wf_env E' -> env_extends E E' ->
  forall U, sub E' T U -> sub E' S U.
Proof.
  intros E S T d Hwf E' Hwf' Hext U d2.
  eapply sub_trans_size.
  - exact Hwf'.
  - eapply sub_weaken; [exact Hwf|exact d|exact Hwf'|exact Hext].
  - exact d2.
Qed.

Lemma sub_pre_env : forall E S T (d : sub E S T),
  wf_env E -> forall E', wf_env E' -> env_extends E E' ->
  forall R, sub E' R S -> sub E' R T.
Proof.
  intros E S T d Hwf E' Hwf' Hext R d1.
  eapply sub_trans_size.
  - exact Hwf'.
  - exact d1.
  - eapply sub_weaken; [exact Hwf|exact d|exact Hwf'|exact Hext].
Qed.

Lemma subqtype_post_env : forall E S T (d : subqtype E S T),
  wf_env E -> forall E', wf_env E' -> env_extends E E' ->
  forall U, subqtype E' T U -> subqtype E' S U.
Proof.
  intros E S T d Hwf E' Hwf' Hext U d2.
  eapply subqtype_trans_size.
  - exact Hwf'.
  - eapply subqtype_weaken; [exact Hwf|exact d|exact Hwf'|exact Hext].
  - exact d2.
Qed.

Lemma subqtype_pre_env : forall E S T (d : subqtype E S T),
  wf_env E -> forall E', wf_env E' -> env_extends E E' ->
  forall R, subqtype E' R S -> subqtype E' R T.
Proof.
  intros E S T d Hwf E' Hwf' Hext R d1.
  eapply subqtype_trans_size.
  - exact Hwf'.
  - exact d1.
  - eapply subqtype_weaken; [exact Hwf|exact d|exact Hwf'|exact Hext].
Qed.


(* ===== inlined from /tmp/main/Closures.v ===== *)

Inductive qualR (E : env) : qua -> qua -> Prop :=
| qualR_refl : forall Q, qualR E Q Q
| qualR_step : forall Q R S, qualR E Q R -> subqual E R S -> qualR E Q S.

Inductive qsubR (E : env) : qtyp -> qtyp -> Prop :=
| qsubR_refl : forall T, qsubR E T T
| qsubR_step : forall S T U, qsubR E S T -> subqtype E T U -> qsubR E S U.

Lemma typing_forward_qsubR : forall E S T,
  qsubR E S T -> forall Q e, typing E Q e S -> typing E Q e T.
Proof.
  intros E S T H. induction H as [T0|S0 T0 U H0 IH Hstep];
    intros Q e Hty.
  - exact Hty.
  - apply (typing_sub T0 E Q e U (IH Q e Hty) Hstep).
Qed.

Lemma typing_forward_qualR : forall E S T,
  qualR E S T -> forall e U, typing E S e U -> typing E T e U.
Proof.
  intros E S T H. induction H as [S0|S0 R T0 H0 IH Hstep];
    intros e U Hty.
  - exact Hty.
  - apply (typing_subqual E R T0 e U (IH e U Hty) Hstep).
Qed.

Lemma typing_ctx_back_qsubR : forall E S T,
  qsubR E S T -> forall Q c, typing_ctx E Q c T -> typing_ctx E Q c S.
Proof.
  intros E S T H. induction H as [T0|S0 T0 U H0 IH Hstep];
    intros Q c Hc.
  - exact Hc.
  - apply (IH Q c (typing_ctx_sub E Q c T0 U Hc Hstep)).
Qed.

Lemma typing_ctx_back_qualR : forall E S T,
  qualR E S T -> forall c U, typing_ctx E T c U -> typing_ctx E S c U.
Proof.
  intros E S T H. induction H as [S0|S0 R T0 H0 IH Hstep];
    intros c U Hc.
  - exact Hc.
  - apply (IH c U (typing_ctx_subqual E T0 R c U Hc Hstep)).
Qed.


Inductive qualL (E : env) : qua -> qua -> Prop :=
| qualL_refl : forall Q, qualL E Q Q
| qualL_step : forall Q R S, subqual E Q R -> qualL E R S -> qualL E Q S.

Inductive qsubL (E : env) : qtyp -> qtyp -> Prop :=
| qsubL_refl : forall T, qsubL E T T
| qsubL_step : forall S T U, subqtype E S T -> qsubL E T U -> qsubL E S U.

Lemma typing_ctx_to_qsubL : forall E S T,
  qsubL E S T -> forall Q c, typing_ctx E Q c T -> typing_ctx E Q c S.
Proof.
  intros E S T H. induction H as [T0|S0 T0 U Hstep Htail IH];
    intros Q c Hc.
  - exact Hc.
  - apply (typing_ctx_sub E Q c S0 T0 (IH Q c Hc) Hstep).
Qed.

Lemma typing_ctx_to_qualL : forall E S T,
  qualL E S T -> forall c U, typing_ctx E T c U -> typing_ctx E S c U.
Proof.
  intros E S T H. induction H as [S0|S0 R T0 Hstep Htail IH];
    intros c U Hc.
  - exact Hc.
  - apply (typing_ctx_subqual E R S0 c U (IH c U Hc) Hstep).
Qed.

Lemma qualL_append : forall E Q R S,
  qualL E Q R -> subqual E R S -> qualL E Q S.
Proof.
  intros E Q R S H. induction H as [X|X Y Z Hstep Htail IH]; intros Hlast.
  - eapply qualL_step; [exact Hlast|apply qualL_refl].
  - eapply qualL_step; [exact Hstep|apply IH; exact Hlast].
Qed.

Lemma qsubL_append : forall E S T U,
  qsubL E S T -> subqtype E T U -> qsubL E S U.
Proof.
  intros E S T U H. induction H as [X|X Y Z Hstep Htail IH]; intros Hlast.
  - eapply qsubL_step; [exact Hlast|apply qsubL_refl].
  - eapply qsubL_step; [exact Hstep|apply IH; exact Hlast].
Qed.

Lemma qualL_concat : forall E Q R S,
  qualL E Q R -> qualL E R S -> qualL E Q S.
Proof.
  intros E Q R S H1 H2. revert Q H1. induction H2 as [X|X Y Z Hstep Htail IH];
    intros Q H1.
  - exact H1.
  - apply IH. eapply qualL_append; eauto.
Qed.

Lemma qsubL_concat : forall E S T U,
  qsubL E S T -> qsubL E T U -> qsubL E S U.
Proof.
  intros E S T U H1 H2. revert S H1. induction H2 as [X|X Y Z Hstep Htail IH];
    intros S H1.
  - exact H1.
  - apply IH. eapply qsubL_append; eauto.
Qed.

Lemma qualR_to_qualL : forall E Q R, qualR E Q R -> qualL E Q R.
Proof.
  intros E Q R H. induction H as [X|X Y Z H0 IH Hstep].
  - apply qualL_refl.
  - eapply qualL_append; eauto.
Qed.

Lemma qsubR_to_qsubL : forall E S T, qsubR E S T -> qsubL E S T.
Proof.
  intros E S T H. induction H as [X|X Y Z H0 IH Hstep].
  - apply qsubL_refl.
  - eapply qsubL_append; eauto.
Qed.

Lemma qualR_comp_qualL : forall E Q R S,
  qualR E Q R -> qualL E R S -> qualL E Q S.
Proof.
  intros. apply qualL_concat with (R := R);
    [apply qualR_to_qualL; assumption|assumption].
Qed.

Lemma qsubR_comp_qsubL : forall E S T U,
  qsubR E S T -> qsubL E T U -> qsubL E S U.
Proof.
  intros. apply qsubL_concat with (T := T);
    [apply qsubR_to_qsubL; assumption|assumption].
Qed.

Lemma typing_forward_qsubL : forall E S T,
  qsubL E S T -> forall Q e, typing E Q e S -> typing E Q e T.
Proof.
  intros E S T H. induction H as [X|X Y Z Hstep Htail IH];
    intros Q e Hty.
  - exact Hty.
  - apply IH. apply (typing_sub X E Q e Y Hty Hstep).
Qed.

Lemma typing_forward_qualL : forall E S T,
  qualL E S T -> forall e U, typing E S e U -> typing E T e U.
Proof.
  intros E S T H. induction H as [X|X Y Z Hstep Htail IH];
    intros e U Hty.
  - exact Hty.
  - apply IH. apply (typing_subqual E X Y e U Hty Hstep).
Qed.


(* ===== inlined from /tmp/main/Inv.v ===== *)

Lemma typing_app_inv : forall E Q e T,
  typing E Q e T ->
  forall f1 f2, e = exp_app f1 f2 ->
  exists Q0 T1 T2,
    typing E Q0 f1 (qtyp_qtyp Q0 (typ_arrow T1 T2)) /\
    typing E Q0 f2 T1 /\
    qualR E Q0 Q /\ qsubR E T2 T.
Proof.
  intros E Q e T Hty. dependent induction Hty; intros f1 f2 Heq; try discriminate Heq.
  - (* typing_app *) inversion Heq; subst.
    exists Q, T1, T2. split; [|split; [|split]].
    + assumption.
    + assumption.
    + apply qualR_refl.
    + apply qsubR_refl.
  - (* typing_sub *) inversion Heq; subst.
    destruct (IHHty f1 f2 eq_refl) as [Q0 [T1 [T2 [H1 [H2 [Hq Hqsub]]]]]].
    exists Q0, T1, T2. split; [|split; [|split]].
    + assumption.
    + assumption.
    + assumption.
    + apply qsubR_step with (T := S); assumption.
  - (* typing_subqual *) inversion Heq; subst.
    destruct (IHHty f1 f2 eq_refl) as [Q0 [T1 [T2 [H1 [H2 [Hq Hqsub]]]]]].
    exists Q0, T1, T2. split; [|split; [|split]].
    + assumption.
    + assumption.
    + apply qualR_step with (R := Q); assumption.
    + assumption.
Qed.


(* ===== inlined from /tmp/main/InvCtx.v ===== *)

Lemma typing_ctx_abs_inv : forall E Q c T,
  typing_ctx E Q c T ->
  forall f k, c = frame_abs f :: k ->
  exists Q0 T1 T2,
    typing_ctx E Q0 k T2 /\
    typing E Q0 f T1 /\
    qualL E Q Q0 /\
    qsubL E T (qtyp_qtyp Q0 (typ_arrow T1 T2)).
Proof.
  intros E Q c T Hty. dependent induction Hty; intros f k Heq; try discriminate Heq.
  - (* typing_ctx_abs *) inversion Heq; subst.
    exists Q, T1, T2. split; [|split; [|split]].
    + assumption.
    + assumption.
    + apply qualL_refl.
    + apply qsubL_refl.
  - (* typing_ctx_sub *) inversion Heq; subst.
    destruct (IHHty f k eq_refl) as [Q0 [T1 [T2 [Hk [Hf [Hq Hs]]]]]].
    exists Q0, T1, T2. split; [|split; [|split]].
    + assumption.
    + assumption.
    + assumption.
    + eapply qsubL_step; [eassumption|exact Hs].
  - (* typing_ctx_subqual *) inversion Heq; subst.
    destruct (IHHty f k eq_refl) as [Q0 [T1 [T2 [Hk [Hf [Hq Hs]]]]]].
    exists Q0, T1, T2. split; [|split; [|split]].
    + assumption.
    + assumption.
    + eapply qualL_step; [eassumption|exact Hq].
    + assumption.
Qed.


(* ===== inlined from /tmp/main/Refl.v ===== *)

Lemma sub_refl_wf : forall E T,
  wf_typ E T -> wf_env E -> sub E T T
with subqtype_refl_wf : forall E T,
  wf_qtyp E T -> wf_env E -> subqtype E T T.
Proof.
  - intros E T H. induction H using wf_typ_mut_ind
      with (P := fun E T _ => wf_env E -> sub E T T)
           (P0 := fun E T _ => wf_env E -> subqtype E T T).
    + intros Hwf. apply sub_top; [exact Hwf|apply wf_typ_top].
    + intros Hwf. apply sub_refl_tvar; [exact Hwf|eapply wf_typ_var; eassumption].
    + intros Hwf. apply sub_arrow.
      * apply IHwf_typ. exact Hwf.
      * apply IHwf_typ0. exact Hwf.
    + intros Hwf. apply sub_all with (L := union L (dom E)).
      * apply IHwf_typ. exact Hwf.
      * intros X Hx.
        assert (HxL : X `notin` L) by fsetdec.
        assert (Hxd : X `notin` dom E) by fsetdec.
        assert (Hwext : wf_env (X ~ bind_sub T1 ++ E)).
        { apply wf_env_sub; [exact Hwf| | exact Hxd].
          (* need wf_typ E T1 : this is the domain wf premise *)
          assumption. }
        apply (H0 X HxL Hwext).
    + intros Hwf. apply sub_qall with (L := union L (dom E)).
      * apply subqual_refl; [exact Hwf|assumption].
      * intros X Hx.
        assert (HxL : X `notin` L) by fsetdec.
        assert (Hxd : X `notin` dom E) by fsetdec.
        assert (Hwext : wf_env (X ~ bind_qua T1 ++ E)).
        { apply wf_env_qua; [exact Hwf|assumption|exact Hxd]. }
        apply (H X HxL Hwext).
    + intros Hwf. apply sub_sum.
      * apply IHwf_typ. exact Hwf.
      * apply IHwf_typ0. exact Hwf.
    + intros Hwf. apply sub_pair.
      * apply IHwf_typ. exact Hwf.
      * apply IHwf_typ0. exact Hwf.
    + intros Hwf. apply sub_qtyp_qtyp.
      * apply subqual_refl; [exact Hwf|assumption].
      * apply IHwf_typ. exact Hwf.
  - intros E T H Hwf. inversion H; subst.
    apply sub_qtyp_qtyp.
    + apply subqual_refl; [exact Hwf|assumption].
    + apply sub_refl_wf; assumption.
Qed.


(* ===== inlined from /tmp/me/Closed.v ===== *)

(* Erase all type/qualifier annotations, preserving term structure. *)
Fixpoint erase_exp (e : exp) : exp :=
  match e with
  | exp_bvar i => exp_bvar i
  | exp_fvar x => exp_fvar x
  | exp_abs _ _ e1 => exp_abs qua_top (qtyp_qtyp qua_top typ_top) (erase_exp e1)
  | exp_app e1 e2 => exp_app (erase_exp e1) (erase_exp e2)
  | exp_tabs _ _ e1 => exp_tabs qua_top typ_top (erase_exp e1)
  | exp_tapp e1 _ => exp_tapp (erase_exp e1) typ_top
  | exp_qabs _ _ e1 => exp_qabs qua_top qua_top (erase_exp e1)
  | exp_qapp e1 _ => exp_qapp (erase_exp e1) qua_top
  | exp_let e1 e2 => exp_let (erase_exp e1) (erase_exp e2)
  | exp_inl _ e1 => exp_inl qua_top (erase_exp e1)
  | exp_inr _ e1 => exp_inr qua_top (erase_exp e1)
  | exp_case e1 e2 e3 => exp_case (erase_exp e1) (erase_exp e2) (erase_exp e3)
  | exp_pair _ e1 e2 => exp_pair qua_top (erase_exp e1) (erase_exp e2)
  | exp_first e1 => exp_first (erase_exp e1)
  | exp_second e1 => exp_second (erase_exp e1)
  | exp_ref _ e1 => exp_ref qua_top (erase_exp e1)
  | exp_ref_label _ l => exp_ref_label qua_top l
  | exp_deref e1 => exp_deref (erase_exp e1)
  | exp_set_ref e1 e2 => exp_set_ref (erase_exp e1) (erase_exp e2)
  | exp_upqual _ e1 => exp_upqual qua_top (erase_exp e1)
  | exp_check _ e1 => exp_check qua_top (erase_exp e1)
  end.

Lemma erase_open_te : forall (j : nat) (U : typ) (e : exp),
  erase_exp (open_te_rec j U e) = erase_exp e.
Proof.
  intros j U e. revert j U. induction e; intros j0 U0; simpl.
  - reflexivity.
  - reflexivity.
  - (* abs *) f_equal. apply IHe.
  - (* app *) f_equal; [apply IHe1|apply IHe2].
  - (* tabs *) f_equal. apply IHe.
  - (* tapp *) f_equal. apply IHe.
  - (* qabs *) f_equal. apply IHe.
  - (* qapp *) f_equal. apply IHe.
  - (* let *) f_equal; [apply IHe1|apply IHe2].
  - (* inl *) f_equal. apply IHe.
  - (* inr *) f_equal. apply IHe.
  - (* case *) f_equal; [apply IHe1|apply IHe2|apply IHe3].
  - (* pair *) f_equal; [apply IHe1|apply IHe2].
  - (* first *) f_equal. apply IHe.
  - (* second *) f_equal. apply IHe.
  - (* ref *) f_equal. apply IHe.
  - (* ref_label *) reflexivity.
  - (* deref *) f_equal. apply IHe.
  - (* set_ref *) f_equal; [apply IHe1|apply IHe2].
  - (* upqual *) f_equal. apply IHe.
  - (* check *) f_equal. apply IHe.
Qed.

Lemma erase_open_qe : forall (j : nat) (R : qua) (e : exp),
  erase_exp (open_qe_rec j R e) = erase_exp e.
Proof.
  intros j R e. revert j R. induction e; intros j0 R0; simpl.
  - reflexivity.
  - reflexivity.
  - (* abs *) f_equal. apply IHe.
  - (* app *) f_equal; [apply IHe1|apply IHe2].
  - (* tabs *) f_equal. apply IHe.
  - (* tapp *) f_equal. apply IHe.
  - (* qabs *) f_equal. apply IHe.
  - (* qapp *) f_equal. apply IHe.
  - (* let *) f_equal; [apply IHe1|apply IHe2].
  - (* inl *) f_equal. apply IHe.
  - (* inr *) f_equal. apply IHe.
  - (* case *) f_equal; [apply IHe1|apply IHe2|apply IHe3].
  - (* pair *) f_equal; [apply IHe1|apply IHe2].
  - (* first *) f_equal. apply IHe.
  - (* second *) f_equal. apply IHe.
  - (* ref *) f_equal. apply IHe.
  - (* ref_label *) reflexivity.
  - (* deref *) f_equal. apply IHe.
  - (* set_ref *) f_equal; [apply IHe1|apply IHe2].
  - (* upqual *) f_equal. apply IHe.
  - (* check *) f_equal. apply IHe.
Qed.

Lemma open_ee_comm_te : forall (k j : nat) (a : atom) (U : typ) (e : exp),
  open_ee_rec k (exp_fvar a) (open_te_rec j U e) = open_te_rec j U (open_ee_rec k (exp_fvar a) e).
Proof.
  intros k j a U e. revert k j. induction e; intros k0 j0; simpl.
  - destruct (k0 == n); reflexivity.
  - reflexivity.
  - f_equal. apply IHe.
  - f_equal; [apply IHe1|apply IHe2].
  - f_equal. apply IHe.
  - f_equal. apply IHe.
  - f_equal. apply IHe.
  - f_equal. apply IHe.
  - f_equal; [apply IHe1|apply IHe2].
  - f_equal. apply IHe.
  - f_equal. apply IHe.
  - f_equal; [apply IHe1|apply IHe2|apply IHe3].
  - f_equal; [apply IHe1|apply IHe2].
  - f_equal. apply IHe.
  - f_equal. apply IHe.
  - f_equal. apply IHe.
  - reflexivity.
  - f_equal. apply IHe.
  - f_equal; [apply IHe1|apply IHe2].
  - f_equal. apply IHe.
  - f_equal. apply IHe.
Qed.

Lemma open_ee_comm_qe : forall (k j : nat) (a : atom) (R : qua) (e : exp),
  open_ee_rec k (exp_fvar a) (open_qe_rec j R e) = open_qe_rec j R (open_ee_rec k (exp_fvar a) e).
Proof.
  intros k j a R e. revert k j. induction e; intros k0 j0; simpl.
  - destruct (k0 == n); reflexivity.
  - reflexivity.
  - f_equal. apply IHe.
  - f_equal; [apply IHe1|apply IHe2].
  - f_equal. apply IHe.
  - f_equal. apply IHe.
  - f_equal. apply IHe.
  - f_equal. apply IHe.
  - f_equal; [apply IHe1|apply IHe2].
  - f_equal. apply IHe.
  - f_equal. apply IHe.
  - f_equal; [apply IHe1|apply IHe2|apply IHe3].
  - f_equal; [apply IHe1|apply IHe2].
  - f_equal. apply IHe.
  - f_equal. apply IHe.
  - f_equal. apply IHe.
  - reflexivity.
  - f_equal. apply IHe.
  - f_equal; [apply IHe1|apply IHe2].
  - f_equal. apply IHe.
  - f_equal. apply IHe.
Qed.

Lemma erase_open_ee_eq : forall (k : nat) (a : atom) (e : exp),
  erase_exp (open_ee_rec k (exp_fvar a) e) = erase_exp e ->
  open_ee_rec k (exp_fvar a) e = e.
Proof.
  intros k a e. revert k. induction e; intros k0 H; simpl in *.
  - (* bvar *) destruct (k0 == n) as [Heq|Hne]; [|reflexivity].
    simpl in H. discriminate H.
  - (* fvar *) reflexivity.
  - (* abs *) injection H as H. f_equal. apply IHe; exact H.
  - (* app *) injection H as H1 H2. f_equal.
    + apply IHe1; exact H1.
    + apply IHe2; exact H2.
  - (* tabs *) injection H as H. f_equal. apply IHe; exact H.
  - (* tapp *) injection H as H. f_equal. apply IHe; exact H.
  - (* qabs *) injection H as H. f_equal. apply IHe; exact H.
  - (* qapp *) injection H as H. f_equal. apply IHe; exact H.
  - (* let *) injection H as H1 H2. f_equal.
    + apply IHe1; exact H1.
    + apply IHe2; exact H2.
  - (* inl *) injection H as H. f_equal. apply IHe; exact H.
  - (* inr *) injection H as H. f_equal. apply IHe; exact H.
  - (* case *) injection H as H1 H2 H3. f_equal.
    + apply IHe1; exact H1.
    + apply IHe2; exact H2.
    + apply IHe3; exact H3.
  - (* pair *) injection H as H1 H2. f_equal.
    + apply IHe1; exact H1.
    + apply IHe2; exact H2.
  - (* first *) injection H as H. f_equal. apply IHe; exact H.
  - (* second *) injection H as H. f_equal. apply IHe; exact H.
  - (* ref *) injection H as H. f_equal. apply IHe; exact H.
  - (* ref_label *) simpl in H. reflexivity.
  - (* deref *) injection H as H. f_equal. apply IHe; exact H.
  - (* set_ref *) injection H as H1 H2. f_equal.
    + apply IHe1; exact H1.
    + apply IHe2; exact H2.
  - (* upqual *) injection H as H. f_equal. apply IHe; exact H.
  - (* check *) injection H as H. f_equal. apply IHe; exact H.
Qed.

Lemma expr_closed : forall e, expr e -> closed_exp e.
Proof.
  intros e H. induction H as
    [ x
    | L P T e1 Hq HT Hq2 Hbody IHbody
    | e1 e2 H1 IH1 H2 IH2
    | L P T e1 Hq HT Hbody IHbody
    | e1 V H1 IH1 HT
    | L P Q e1 HqP HqQ Hbody IHbody
    | e1 Q H1 IH1 Hq
    | L e1 e2 H1 IH1 Hbody IHbody
    | P e1 Hq H1 IH1
    | P e1 Hq H1 IH1
    | L e1 e2 e3 H1 IH1 Hbody2 IHbody2 Hbody3 IHbody3
    | P e1 e2 Hq H1 IH1 H2 IH2
    | e1 H1 IH1
    | e1 H1 IH1
    | P e1 Hq H1 IH1
    | P e1 Hq H1 IH1 ].
  - (* var *) intros k a. reflexivity.
  - (* abs *) intros k a. simpl.
    destruct (atom_fresh (union L (union (fv_ee e1) (singleton a)))) as [y Hy].
    assert (HyL : y `notin` L) by fsetdec.
    assert (Hyf : y `notin` fv_ee e1) by fsetdec.
    assert (Hc : closed_exp (open_ee e1 y)). { apply IHbody; exact HyL. }
    f_equal. exact (closed_inv_open_ee e1 y Hyf Hc k a).
  - (* app *) intros k a. simpl. f_equal; [apply IH1|apply IH2].
  - (* tabs *) intros k a. simpl.
    destruct (atom_fresh L) as [X HX].
    assert (Hc : closed_exp (open_te e1 X)). { apply IHbody; exact HX. }
    assert (Hk : open_ee_rec (S k) (exp_fvar a) (open_te_rec 0 (typ_fvar X) e1) =
                 open_te_rec 0 (typ_fvar X) e1) by (apply Hc).
    rewrite open_ee_comm_te in Hk.
    assert (Heq : open_te_rec 0 (typ_fvar X) (open_ee_rec (S k) (exp_fvar a) e1) =
                  open_te_rec 0 (typ_fvar X) e1) by exact Hk.
    assert (Her : erase_exp (open_ee_rec (S k) (exp_fvar a) e1) = erase_exp e1).
    { rewrite <- (erase_open_te 0 (typ_fvar X) (open_ee_rec (S k) (exp_fvar a) e1)).
      rewrite Heq. apply erase_open_te. }
    f_equal. exact (erase_open_ee_eq (S k) a e1 Her).
  - (* tapp *) intros k a. simpl. f_equal. apply IH1.
  - (* qabs *) intros k a. simpl.
    destruct (atom_fresh L) as [X HX].
    assert (Hc : closed_exp (open_qe e1 X)). { apply IHbody; exact HX. }
    assert (Hk : open_ee_rec (S k) (exp_fvar a) (open_qe_rec 0 (qua_fvar X) e1) =
                 open_qe_rec 0 (qua_fvar X) e1) by (apply Hc).
    rewrite open_ee_comm_qe in Hk.
    assert (Heq : open_qe_rec 0 (qua_fvar X) (open_ee_rec (S k) (exp_fvar a) e1) =
                  open_qe_rec 0 (qua_fvar X) e1) by exact Hk.
    assert (Her : erase_exp (open_ee_rec (S k) (exp_fvar a) e1) = erase_exp e1).
    { rewrite <- (erase_open_qe 0 (qua_fvar X) (open_ee_rec (S k) (exp_fvar a) e1)).
      rewrite Heq. apply erase_open_qe. }
    f_equal. exact (erase_open_ee_eq (S k) a e1 Her).
  - (* qapp *) intros k a. simpl. f_equal. apply IH1.
  - (* let *) intros k a. simpl. f_equal.
    + apply IH1.
    + destruct (atom_fresh (union L (union (fv_ee e2) (singleton a)))) as [y Hy].
      assert (HyL : y `notin` L) by fsetdec.
      assert (Hyf : y `notin` fv_ee e2) by fsetdec.
      assert (Hc : closed_exp (open_ee e2 y)). { apply IHbody; exact HyL. }
      exact (closed_inv_open_ee e2 y Hyf Hc k a).
  - (* inl *) intros k a. simpl. f_equal. apply IH1.
  - (* inr *) intros k a. simpl. f_equal. apply IH1.
  - (* case *) intros k a. simpl. f_equal.
    + apply IH1.
    + destruct (atom_fresh (union L (union (fv_ee e2) (singleton a)))) as [y Hy].
      assert (HyL : y `notin` L) by fsetdec.
      assert (Hyf : y `notin` fv_ee e2) by fsetdec.
      assert (Hc : closed_exp (open_ee e2 y)). { apply IHbody2; exact HyL. }
      exact (closed_inv_open_ee e2 y Hyf Hc k a).
    + destruct (atom_fresh (union L (union (fv_ee e3) (singleton a)))) as [y Hy].
      assert (HyL : y `notin` L) by fsetdec.
      assert (Hyf : y `notin` fv_ee e3) by fsetdec.
      assert (Hc : closed_exp (open_ee e3 y)). { apply IHbody3; exact HyL. }
      exact (closed_inv_open_ee e3 y Hyf Hc k a).
  - (* pair *) intros k a. simpl. f_equal; [apply IH1|apply IH2].
  - (* first *) intros k a. simpl. f_equal. apply IH1.
  - (* second *) intros k a. simpl. f_equal. apply IH1.
  - (* upqual *) intros k a. simpl. f_equal. apply IH1.
  - (* check *) intros k a. simpl. f_equal. apply IH1.
Qed.

Lemma typing_closed : forall E Q e T, typing E Q e T -> closed_exp e.
Proof. intros. apply expr_closed. apply typing_expr with (E := E) (Q := Q) (T := T). assumption. Qed.


(* ===== inlined from /tmp/w2/Ann.v ===== *)

Scheme type_mut_ind := Induction for type Sort Prop
  with qtype_mut_ind := Induction for qtype Sort Prop.

Lemma qual_open_qq : forall Q, qual Q -> forall j R, open_qq_rec j R Q = Q.
Proof.
  intros Q H. induction H as [|X|Q1 Q2 H1 IH1 H2 IH2|Q1 Q2 H1 IH1 H2 IH2|]; intros j0 R0; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal; [apply IH1|apply IH2].
  - f_equal; [apply IH1|apply IH2].
  - reflexivity.
Qed.

Lemma open_qq_swap : forall Q i j X Y, i <> j ->
  open_qq_rec i (qua_fvar Y) (open_qq_rec j (qua_fvar X) Q) =
  open_qq_rec j (qua_fvar X) (open_qq_rec i (qua_fvar Y) Q).
Proof.
  intros Q. induction Q; intros i0 j0 X Y Hij; simpl.
  - reflexivity.
  - repeat (simpl; match goal with
      | |- context [if ?a == ?b then _ else _] => destruct (a == b)
      | H : _ = _ |- _ => subst
      | H : context [if ?p == ?q then _ else _] |- _ => destruct (p == q)
      end).
    all: try (exfalso; apply Hij; congruence);
         simpl; try rewrite !eq_dec_refl; reflexivity.
  - reflexivity.
  - f_equal; [apply IHQ1|apply IHQ2]; assumption.
  - f_equal; [apply IHQ1|apply IHQ2]; assumption.
  - reflexivity.
Qed.

Lemma open_tt_swap : forall T i j X Y, i <> j ->
  open_tt_rec i (typ_fvar Y) (open_tt_rec j (typ_fvar X) T) =
  open_tt_rec j (typ_fvar X) (open_tt_rec i (typ_fvar Y) T)
with open_tqt_swap : forall T i j X Y, i <> j ->
  open_tqt_rec i (typ_fvar Y) (open_tqt_rec j (typ_fvar X) T) =
  open_tqt_rec j (typ_fvar X) (open_tqt_rec i (typ_fvar Y) T).
Proof.
  - intros T. induction T; intros i0 j0 X Y Hij; simpl.
    + reflexivity.
  + repeat (simpl; match goal with
      | |- context [if ?a == ?b then _ else _] => destruct (a == b)
      | H : _ = _ |- _ => subst
      | H : context [if ?p == ?q then _ else _] |- _ => destruct (p == q)
      end).
    all: try (exfalso; apply Hij; congruence);
         simpl; try rewrite !eq_dec_refl; reflexivity.
    + reflexivity.
    + f_equal; eauto using open_tqt_swap, open_qq_swap, S_neq.
    + f_equal; eauto using open_tqt_swap, open_qq_swap, S_neq.
    + f_equal; eauto using open_tqt_swap, open_qq_swap, S_neq.
    + f_equal; eauto using open_tqt_swap, open_qq_swap, S_neq.
    + f_equal; eauto using open_tqt_swap, open_qq_swap, S_neq.
    + f_equal; eauto using open_tqt_swap, open_qq_swap, S_neq.
  - intros T i0 j0 X Y Hij. destruct T as [Q T0]. simpl. f_equal.
    exact (open_tt_swap T0 i0 j0 X Y Hij).
Qed.


Lemma open_qt_swap : forall T i j X Y, i <> j ->
  open_qt_rec i (qua_fvar Y) (open_qt_rec j (qua_fvar X) T) =
  open_qt_rec j (qua_fvar X) (open_qt_rec i (qua_fvar Y) T)
with open_qqt_swap : forall T i j X Y, i <> j ->
  open_qqt_rec i (qua_fvar Y) (open_qqt_rec j (qua_fvar X) T) =
  open_qqt_rec j (qua_fvar X) (open_qqt_rec i (qua_fvar Y) T).
Proof.
  - intros T. induction T; intros i0 j0 X Y Hij; simpl.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + f_equal; eauto using open_qqt_swap, open_qq_swap, S_neq.
    + f_equal; eauto using open_qqt_swap, open_qq_swap, S_neq.
    + f_equal; eauto using open_qqt_swap, open_qq_swap, S_neq.
    + f_equal; eauto using open_qqt_swap, open_qq_swap, S_neq.
    + f_equal; eauto using open_qqt_swap, open_qq_swap, S_neq.
    + f_equal; eauto using open_qqt_swap, open_qq_swap, S_neq.
  - intros T i0 j0 X Y Hij. destruct T as [Q T0]. simpl. f_equal.
    + exact (open_qq_swap Q i0 j0 X Y Hij).
    + exact (open_qt_swap T0 i0 j0 X Y Hij).
Qed.

Lemma open_qq_cancel_diff : forall Q a b X Y, a <> b ->
  open_qq_rec a (qua_fvar Y) (open_qq_rec b (qua_fvar X) Q) =
  open_qq_rec a (qua_fvar Y) Q ->
  open_qq_rec b (qua_fvar X) Q = Q.
Proof.
  intros Q. induction Q; intros a0 b0 X Y Hab H; simpl in *.
  - reflexivity.
  - repeat match goal with
      | |- context [if ?p == ?q then _ else _] => destruct (p == q)
      | H : context [if ?p == ?q then _ else _] |- _ => destruct (p == q)
      | H : _ = _ |- _ => subst
      end.
    all: simpl in *; try discriminate; try reflexivity; try assumption;
      try (exfalso; apply Hab; congruence).
  - reflexivity.
  - injection H as H1 H2. f_equal; [exact (IHQ1 a0 b0 X Y Hab H1)|exact (IHQ2 a0 b0 X Y Hab H2)].
  - injection H as H1 H2. f_equal; [exact (IHQ1 a0 b0 X Y Hab H1)|exact (IHQ2 a0 b0 X Y Hab H2)].
  - reflexivity.
Qed.

Lemma open_tt_cancel_diff : forall T a b X Y, a <> b ->
  open_tt_rec a (typ_fvar Y) (open_tt_rec b (typ_fvar X) T) =
  open_tt_rec a (typ_fvar Y) T ->
  open_tt_rec b (typ_fvar X) T = T
with open_tqt_cancel_diff : forall T a b X Y, a <> b ->
  open_tqt_rec a (typ_fvar Y) (open_tqt_rec b (typ_fvar X) T) =
  open_tqt_rec a (typ_fvar Y) T ->
  open_tqt_rec b (typ_fvar X) T = T.
Proof.
  - intros T. induction T; intros a0 b0 X Y Hab H; simpl in *.
    + reflexivity.
    + repeat match goal with
        | |- context [if ?p == ?q then _ else _] => destruct (p == q)
        | H : context [if ?p == ?q then _ else _] |- _ => destruct (p == q)
        | H : _ = _ |- _ => subst
        end.
      all: simpl in *; try discriminate; try reflexivity; try assumption;
        try (exfalso; apply Hab; congruence).
    + reflexivity.
    + injection H as H1 H2. f_equal; eauto using S_neq.
    + injection H as H1 H2. f_equal; eauto using S_neq.
    + injection H as H1. f_equal; eauto using S_neq.
    + injection H as H1 H2. f_equal; eauto using S_neq.
    + injection H as H1 H2. f_equal; eauto using S_neq.
    + injection H as H1. f_equal; eauto using S_neq.
  - intros T a0 b0 X Y Hab H. destruct T as [Q T0]. simpl in *. injection H as H1.
    f_equal; eauto using S_neq.
Qed.

Lemma open_qt_cancel_diff : forall T a b X Y, a <> b ->
  open_qt_rec a (qua_fvar Y) (open_qt_rec b (qua_fvar X) T) =
  open_qt_rec a (qua_fvar Y) T ->
  open_qt_rec b (qua_fvar X) T = T
with open_qqt_cancel_diff : forall T a b X Y, a <> b ->
  open_qqt_rec a (qua_fvar Y) (open_qqt_rec b (qua_fvar X) T) =
  open_qqt_rec a (qua_fvar Y) T ->
  open_qqt_rec b (qua_fvar X) T = T.
Proof.
  - intros T. induction T; intros a0 b0 X Y Hab H; simpl in *.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + injection H as H1 H2. f_equal; eauto using open_qqt_cancel_diff, open_qt_cancel_diff, open_qq_cancel_diff, S_neq.
    + injection H as H1 H2. f_equal; eauto using open_qqt_cancel_diff, open_qt_cancel_diff, open_qq_cancel_diff, S_neq.
    + injection H as H1 H2. f_equal; eauto using open_qqt_cancel_diff, open_qt_cancel_diff, open_qq_cancel_diff, S_neq.
    + injection H as H1 H2. f_equal; eauto using open_qqt_cancel_diff, open_qt_cancel_diff, open_qq_cancel_diff, S_neq.
    + injection H as H1 H2. f_equal; eauto using open_qqt_cancel_diff, open_qt_cancel_diff, open_qq_cancel_diff, S_neq.
    + injection H as H1. f_equal; eauto using open_qqt_cancel_diff, open_qt_cancel_diff, open_qq_cancel_diff, S_neq.
  - intros T a0 b0 X Y Hab H. destruct T as [Q T0]. simpl in *. injection H as H1 H2.
    f_equal; eauto using open_qqt_cancel_diff, open_qt_cancel_diff, open_qq_cancel_diff, S_neq.
Qed.

Lemma open_tt_qt_comm : forall T a b X Y,
  open_tt_rec b (typ_fvar X) (open_qt_rec a (qua_fvar Y) T) =
  open_qt_rec a (qua_fvar Y) (open_tt_rec b (typ_fvar X) T)
with open_tqt_qqt_comm : forall T a b X Y,
  open_tqt_rec b (typ_fvar X) (open_qqt_rec a (qua_fvar Y) T) =
  open_qqt_rec a (qua_fvar Y) (open_tqt_rec b (typ_fvar X) T).
Proof.
  - intros T. induction T; intros a0 b0 X Y; simpl.
    + reflexivity.
    + destruct (b0 == n); simpl; reflexivity.
    + reflexivity.
    + f_equal; eauto using open_tt_qt_comm, open_tqt_qqt_comm.
    + f_equal; eauto using open_tt_qt_comm, open_tqt_qqt_comm.
    + f_equal; eauto using open_tt_qt_comm, open_tqt_qqt_comm.
    + f_equal; eauto using open_tt_qt_comm, open_tqt_qqt_comm.
    + f_equal; eauto using open_tt_qt_comm, open_tqt_qqt_comm.
    + f_equal; eauto using open_tt_qt_comm, open_tqt_qqt_comm.
  - intros T a0 b0 X Y. destruct T as [Q T0]. simpl. f_equal; eauto using open_tt_qt_comm, open_tqt_qqt_comm.
Qed.

Lemma open_tt_cancel_qqt : forall T a b X Y,
  open_tt_rec b (typ_fvar X) (open_qt_rec a (qua_fvar Y) T) =
  open_tt_rec b (typ_fvar X) T ->
  open_qt_rec a (qua_fvar Y) T = T
with open_tqt_cancel_qqt : forall T a b X Y,
  open_tqt_rec b (typ_fvar X) (open_qqt_rec a (qua_fvar Y) T) =
  open_tqt_rec b (typ_fvar X) T ->
  open_qqt_rec a (qua_fvar Y) T = T.
Proof.
  - intros T. induction T; intros a0 b0 X Y H; simpl in *.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + injection H as H1 H2. f_equal; eauto using open_tqt_cancel_qqt.
    + injection H as H1 H2. f_equal; eauto using open_tt_cancel_qqt, open_tqt_cancel_qqt.
    + injection H as H1 H2. f_equal; [exact H1 | eauto using open_tqt_cancel_qqt].
    + injection H as H1 H2. f_equal; eauto using open_tqt_cancel_qqt.
    + injection H as H1 H2. f_equal; eauto using open_tqt_cancel_qqt.
    + injection H as H1. f_equal; eauto using open_tqt_cancel_qqt.
  - intros T a0 b0 X Y H. destruct T as [Q T0]. simpl in *. injection H as H1 H2.
    f_equal; [exact H1 | eauto using open_tt_cancel_qqt].
Qed.

Lemma open_qt_cancel_tqt : forall T a b X Y,
  open_qt_rec a (qua_fvar Y) (open_tt_rec b (typ_fvar X) T) =
  open_qt_rec a (qua_fvar Y) T ->
  open_tt_rec b (typ_fvar X) T = T
with open_qqt_cancel_tqt : forall T a b X Y,
  open_qqt_rec a (qua_fvar Y) (open_tqt_rec b (typ_fvar X) T) =
  open_qqt_rec a (qua_fvar Y) T ->
  open_tqt_rec b (typ_fvar X) T = T.
Proof.
  - intros T. induction T; intros a0 b0 X Y H; simpl in *.
    + reflexivity.
    + destruct (b0 == n) as [Hb|Hb].
      * simpl in H. exact H.
      * reflexivity.
    + reflexivity.
    + injection H as H1 H2. f_equal; eauto using open_qqt_cancel_tqt.
    + injection H as H1 H2. f_equal; eauto using open_qt_cancel_tqt, open_qqt_cancel_tqt.
    + injection H as H1. f_equal; eauto using open_qqt_cancel_tqt.
    + injection H as H1 H2. f_equal; eauto using open_qqt_cancel_tqt.
    + injection H as H1 H2. f_equal; eauto using open_qqt_cancel_tqt.
    + injection H as H1. f_equal; eauto using open_qqt_cancel_tqt.
  - intros T a0 b0 X Y H. destruct T as [Q T0]. simpl in *. injection H as H1.
    f_equal; eauto using open_qt_cancel_tqt.
Qed.

Lemma type_open_tt_fvar : forall T, type T -> forall j X, open_tt_rec j (typ_fvar X) T = T
with qtype_open_tqt_fvar : forall T, qtype T -> forall j X, open_tqt_rec j (typ_fvar X) T = T
with type_open_qt_fvar : forall T, type T -> forall j X, open_qt_rec j (qua_fvar X) T = T
with qtype_open_qqt_fvar : forall T, qtype T -> forall j X, open_qqt_rec j (qua_fvar X) T = T.
Proof.
  - intros T H. induction H using type_mut_ind
      with (P := fun T _ => forall j X, open_tt_rec j (typ_fvar X) T = T)
           (P0 := fun T _ => forall j X, open_tqt_rec j (typ_fvar X) T = T).
    + intros; reflexivity.
    + intros; reflexivity.
    + intros j X; simpl; f_equal; eauto 8.
    + intros j X; simpl; f_equal.
      * eauto.
      * destruct (atom_fresh (union L (singleton X))) as [Y HY].
        assert (HYL : Y `notin` L) by fsetdec.
        assert (HbodyY := H0 Y HYL).
        assert (Hc := HbodyY (S j) X).
        unfold open_tqt in Hc.
        rewrite <- (open_tqt_swap T2 0 (S j) X Y (ltac:(congruence))) in Hc.
        exact (open_tqt_cancel_diff T2 0 (S j) X Y (ltac:(congruence)) Hc).
    + intros j X; simpl; f_equal.
      destruct (atom_fresh (union L (singleton X))) as [Y HY].
      assert (HYL : Y `notin` L) by fsetdec.
      assert (HbodyY := H Y HYL).
      assert (Hc := HbodyY (S j) X).
      unfold open_qqt in Hc.
      rewrite (open_tqt_qqt_comm T 0 (S j) X Y) in Hc.
      exact (open_qqt_cancel_tqt T 0 (S j) X Y Hc).
    + intros j X; simpl; f_equal; eauto 8.
    + intros j X; simpl; f_equal; eauto 8.
    + intros j X; simpl. f_equal.
      exact (IHtype j X).
  - intros T H. destruct T as [Q T0]. inversion H; subst. intros j X. simpl. f_equal.
    exact (type_open_tt_fvar T0 H3 j X).
  - intros T H. induction H using type_mut_ind
      with (P := fun T _ => forall j X, open_qt_rec j (qua_fvar X) T = T)
           (P0 := fun T _ => forall j X, open_qqt_rec j (qua_fvar X) T = T).
    + intros; reflexivity.
    + intros; reflexivity.
    + intros j X; simpl; f_equal; eauto 8.
    + intros j X; simpl; f_equal.
      * eauto.
      * destruct (atom_fresh (union L (singleton X))) as [Y HY].
        assert (HYL : Y `notin` L) by fsetdec.
        assert (HbodyY := H0 Y HYL).
        assert (Hc := HbodyY (S j) X).
        unfold open_tqt in Hc.
        rewrite <- (open_tqt_qqt_comm T2 (S j) 0 Y X) in Hc.
        exact (open_tqt_cancel_qqt T2 (S j) 0 Y X Hc).
    + intros j X; simpl; f_equal.
      * match goal with Hq : qual ?Q0 |- open_qq_rec j ?Rq ?Q0 = ?Q0 =>
          exact (qual_open_qq Q0 Hq j Rq) end.
      * destruct (atom_fresh (union L (singleton X))) as [Y HY].
        assert (HYL : Y `notin` L) by fsetdec.
        assert (HbodyY := H Y HYL).
        assert (Hc := HbodyY (S j) X).
        unfold open_qqt in Hc.
        rewrite <- (open_qqt_swap T 0 (S j) X Y (ltac:(congruence))) in Hc.
        exact (open_qqt_cancel_diff T 0 (S j) X Y (ltac:(congruence)) Hc).
    + intros j X; simpl; f_equal; eauto 8.
    + intros j X; simpl; f_equal; eauto 8.
    + intros j X; simpl; f_equal.
      * exact (qual_open_qq Q q j X).
      * exact (IHtype j X).
  - intros T H. destruct T as [Q T0]. inversion H; subst. intros j X. simpl. f_equal.
    + exact (qual_open_qq Q H2 j X).
    + exact (type_open_qt_fvar T0 H3 j X).
Qed.



(* ===== inlined from /tmp/w2/Closed3.v ===== *)

(* Expression-level swapping of two type openings at distinct depths. *)
Lemma open_te_swap_exp : forall e a b X Y, a <> b ->
  open_te_rec a (typ_fvar Y) (open_te_rec b (typ_fvar X) e) =
  open_te_rec b (typ_fvar X) (open_te_rec a (typ_fvar Y) e).
Proof.
  intros e. induction e; intros a0 b0 X Y Hab; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal; eauto using open_tqt_swap, S_neq.
  - f_equal; eauto.
  - f_equal; eauto using open_tt_swap, S_neq.
  - f_equal; eauto using open_tt_swap.
  - f_equal; eauto using S_neq.
  - f_equal; eauto.
  - f_equal; eauto using S_neq.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto using S_neq.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
  - reflexivity.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
Qed.

Lemma open_qe_swap_exp : forall e a b X Y, a <> b ->
  open_qe_rec a (qua_fvar Y) (open_qe_rec b (qua_fvar X) e) =
  open_qe_rec b (qua_fvar X) (open_qe_rec a (qua_fvar Y) e).
Proof.
  intros e. induction e; intros a0 b0 X Y Hab; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal; eauto using open_qq_swap, open_qqt_swap, S_neq.
  - f_equal; eauto.
  - f_equal; eauto using open_qq_swap, open_qt_swap, S_neq.
  - f_equal; eauto using open_qt_swap.
  - f_equal; eauto using open_qq_swap, S_neq.
  - f_equal; eauto using open_qq_swap.
  - f_equal; eauto using S_neq.
  - f_equal; eauto using open_qq_swap.
  - f_equal; eauto using open_qq_swap.
  - f_equal; eauto using S_neq.
  - f_equal; eauto using open_qq_swap.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto using open_qq_swap.
  - f_equal; eauto using open_qq_swap.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto using open_qq_swap.
  - f_equal; eauto using open_qq_swap.
Qed.

Lemma open_te_cancel_te : forall e a b X Y, a <> b ->
  open_te_rec a (typ_fvar Y) (open_te_rec b (typ_fvar X) e) =
  open_te_rec a (typ_fvar Y) e ->
  open_te_rec b (typ_fvar X) e = e.
Proof.
  intros e. induction e; intros a0 b0 X Y Hab H; simpl in *.
  - reflexivity.
  - reflexivity.
  - injection H as H1 H2. f_equal.
    + eapply open_tqt_cancel_diff; eassumption.
    + eapply IHe; [apply S_neq; exact Hab|eassumption].
  - injection H as H1 H2. f_equal.
    + eapply IHe1; eassumption.
    + eapply IHe2; eassumption.
  - injection H as H1 H2. f_equal.
    + eapply open_tt_cancel_diff; eassumption.
    + eapply IHe; [apply S_neq; exact Hab|eassumption].
  - injection H as H1 H2. f_equal.
    + eapply IHe; eassumption.
    + eapply open_tt_cancel_diff; eassumption.
  - injection H as H1. f_equal.
    + eapply IHe; [apply S_neq; exact Hab|eassumption].
  - injection H as H1. f_equal.
    + eapply IHe; eassumption.
  - injection H as H1 H2. f_equal.
    + eapply IHe1; eassumption.
    + eapply IHe2; [apply S_neq; exact Hab|eassumption].
  - injection H as H1. f_equal. eapply IHe; eassumption.
  - injection H as H1. f_equal. eapply IHe; eassumption.
  - injection H as H1 H2 H3. f_equal.
    + eapply IHe1; eassumption.
    + eapply IHe2; [apply S_neq; exact Hab|eassumption].
    + eapply IHe3; [apply S_neq; exact Hab|eassumption].
  - injection H as H1 H2. f_equal; [eapply IHe1; eassumption|eapply IHe2; eassumption].
  - injection H as H1. f_equal. eapply IHe; eassumption.
  - injection H as H1. f_equal. eapply IHe; eassumption.
  - injection H as H1. f_equal. eapply IHe; eassumption.
  - reflexivity.
  - injection H as H1. f_equal. eapply IHe; eassumption.
  - injection H as H1 H2. f_equal; [eapply IHe1; eassumption|eapply IHe2; eassumption].
  - injection H as H1. f_equal. eapply IHe; eassumption.
  - injection H as H1. f_equal. eapply IHe; eassumption.
Qed.

Lemma open_qe_cancel_qe : forall e a b X Y, a <> b ->
  open_qe_rec a (qua_fvar Y) (open_qe_rec b (qua_fvar X) e) =
  open_qe_rec a (qua_fvar Y) e ->
  open_qe_rec b (qua_fvar X) e = e.
Proof.
  intros e. induction e; intros a0 b0 X Y Hab H; simpl in *.
  - reflexivity.
  - reflexivity.
  - injection H as Hp HV Hb. f_equal.
    + eapply open_qq_cancel_diff; eassumption.
    + eapply open_qqt_cancel_diff; eassumption.
    + eapply IHe; [apply S_neq; exact Hab|eassumption].
  - injection H as H1 H2. f_equal; [eapply IHe1; eassumption|eapply IHe2; eassumption].
  - injection H as Hp HV Hb. f_equal.
    + eapply open_qq_cancel_diff; eassumption.
    + eapply open_qt_cancel_diff; eassumption.
    + eapply IHe; [apply S_neq; exact Hab|eassumption].
  - injection H as H1 H2. f_equal.
    + eapply IHe; eassumption.
    + eapply open_qt_cancel_diff; eassumption.
  - injection H as H1 H2 H3. f_equal.
    + eapply open_qq_cancel_diff; eassumption.
    + eapply open_qq_cancel_diff; eassumption.
    + eapply IHe; [apply S_neq; exact Hab|eassumption].
  - injection H as H1 H2. f_equal.
    + eapply IHe; eassumption.
    + eapply open_qq_cancel_diff; eassumption.
  - injection H as H1 H2. f_equal.
    + eapply IHe1; eassumption.
    + eapply IHe2; [apply S_neq; exact Hab|eassumption].
  - injection H as H1 H2. f_equal.
    + eapply open_qq_cancel_diff; eassumption.
    + eapply IHe; eassumption.
  - injection H as H1 H2. f_equal.
    + eapply open_qq_cancel_diff; eassumption.
    + eapply IHe; eassumption.
  - injection H as H1 H2 H3. f_equal.
    + eapply IHe1; eassumption.
    + eapply IHe2; [apply S_neq; exact Hab|eassumption].
    + eapply IHe3; [apply S_neq; exact Hab|eassumption].
  - injection H as H1 H2 H3. f_equal.
    + eapply open_qq_cancel_diff; eassumption.
    + eapply IHe1; eassumption.
    + eapply IHe2; eassumption.
  - injection H as H1. f_equal. eapply IHe; eassumption.
  - injection H as H1. f_equal. eapply IHe; eassumption.
  - injection H as H1 H2. f_equal.
    + eapply open_qq_cancel_diff; eassumption.
    + eapply IHe; eassumption.
  - injection H as H1. f_equal. eapply open_qq_cancel_diff; eassumption.
  - injection H as H1. f_equal. eapply IHe; eassumption.
  - injection H as H1 H2. f_equal; [eapply IHe1; eassumption|eapply IHe2; eassumption].
  - injection H as H1 H2. f_equal.
    + eapply open_qq_cancel_diff; eassumption.
    + eapply IHe; eassumption.
  - injection H as H1 H2. f_equal.
    + eapply open_qq_cancel_diff; eassumption.
    + eapply IHe; eassumption.
Qed.


(* ===== inlined from /tmp/w2/Closed4.v ===== *)

Lemma open_te_cancel_ee : forall e j U k a,
  open_ee_rec k (exp_fvar a) (open_te_rec j U e) =
  open_ee_rec k (exp_fvar a) e ->
  open_te_rec j U e = e.
Proof.
  intros e. induction e; intros j0 U0 k0 a0 H; simpl in *.
  - reflexivity.
  - reflexivity.
  - injection H as H1 H2. f_equal.
    + exact H1.
    + eapply IHe; eassumption.
  - injection H as H1 H2. f_equal; [eapply IHe1; eassumption|eapply IHe2; eassumption].
  - injection H as H1 H2. f_equal.
    + exact H1.
    + eapply IHe; eassumption.
  - injection H as H1 H2. f_equal.
    + eapply IHe; eassumption.
    + exact H2.
  - injection H as H1. f_equal. eapply IHe; eassumption.
  - injection H as H1. f_equal. eapply IHe; eassumption.
  - injection H as H1 H2. f_equal; [eapply IHe1; eassumption|eapply IHe2; eassumption].
  - injection H as H1. f_equal. eapply IHe; eassumption.
  - injection H as H1. f_equal. eapply IHe; eassumption.
  - injection H as H1 H2 H3. f_equal; [eapply IHe1; eassumption|eapply IHe2; eassumption|eapply IHe3; eassumption].
  - injection H as H1 H2. f_equal; [eapply IHe1; eassumption|eapply IHe2; eassumption].
  - injection H as H1. f_equal. eapply IHe; eassumption.
  - injection H as H1. f_equal. eapply IHe; eassumption.
  - injection H as H1. f_equal. eapply IHe; eassumption.
  - reflexivity.
  - injection H as H1. f_equal. eapply IHe; eassumption.
  - injection H as H1 H2. f_equal; [eapply IHe1; eassumption|eapply IHe2; eassumption].
  - injection H as H1. f_equal. eapply IHe; eassumption.
  - injection H as H1. f_equal. eapply IHe; eassumption.
Qed.

Lemma open_qe_cancel_ee : forall e j R k a,
  open_ee_rec k (exp_fvar a) (open_qe_rec j R e) =
  open_ee_rec k (exp_fvar a) e ->
  open_qe_rec j R e = e.
Proof.
  intros e. induction e; intros j0 R0 k0 a0 H; simpl in *.
  - reflexivity.
  - reflexivity.
  - injection H as Hp HV Hb. f_equal.
    + exact Hp.
    + exact HV.
    + eapply IHe; eassumption.
  - injection H as H1 H2. f_equal; [eapply IHe1; eassumption|eapply IHe2; eassumption].
  - injection H as Hp HV Hb. f_equal.
    + exact Hp.
    + exact HV.
    + eapply IHe; eassumption.
  - injection H as H1 H2. f_equal; [eapply IHe; eassumption|exact H2].
  - injection H as H1 H2 H3. f_equal.
    + exact H1.
    + exact H2.
    + eapply IHe; eassumption.
  - injection H as H1 H2. f_equal; [eapply IHe; eassumption|exact H2].
  - injection H as H1 H2. f_equal; [eapply IHe1; eassumption|eapply IHe2; eassumption].
  - injection H as H1 H2. f_equal; [exact H1|eapply IHe; eassumption].
  - injection H as H1 H2. f_equal; [exact H1|eapply IHe; eassumption].
  - injection H as H1 H2 H3. f_equal; [eapply IHe1; eassumption|eapply IHe2; eassumption|eapply IHe3; eassumption].
  - injection H as H1 H2 H3. f_equal; [exact H1|eapply IHe1; eassumption|eapply IHe2; eassumption].
  - injection H as H1. f_equal. eapply IHe; eassumption.
  - injection H as H1. f_equal. eapply IHe; eassumption.
  - injection H as H1 H2. f_equal; [exact H1|eapply IHe; eassumption].
  - injection H as H1. f_equal. exact H1.
  - injection H as H1. f_equal. eapply IHe; eassumption.
  - injection H as H1 H2. f_equal; [eapply IHe1; eassumption|eapply IHe2; eassumption].
  - injection H as H1 H2. f_equal; [exact H1|eapply IHe; eassumption].
  - injection H as H1 H2. f_equal; [exact H1|eapply IHe; eassumption].
Qed.

Lemma open_te_qe_comm_exp : forall e j a X Y,
  open_te_rec j (typ_fvar X) (open_qe_rec a (qua_fvar Y) e) =
  open_qe_rec a (qua_fvar Y) (open_te_rec j (typ_fvar X) e).
Proof.
  intros e. induction e; intros j0 a0 X Y; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal; eauto using open_tqt_qqt_comm, open_qq_swap.
  - f_equal; eauto.
  - f_equal; eauto using open_tt_qt_comm, open_qq_swap.
  - f_equal; eauto using open_tt_qt_comm.
  - f_equal; eauto using open_qq_swap.
  - f_equal; eauto using open_qq_swap.
  - f_equal; eauto.
  - f_equal; eauto using open_qq_swap.
  - f_equal; eauto using open_qq_swap.
  - f_equal; eauto.
  - f_equal; eauto using open_qq_swap.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto using open_qq_swap.
  - f_equal; eauto using open_qq_swap.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto using open_qq_swap.
  - f_equal; eauto using open_qq_swap.
Qed.

Lemma open_qe_te_comm_exp : forall e j a X Y,
  open_qe_rec a (qua_fvar Y) (open_te_rec j (typ_fvar X) e) =
  open_te_rec j (typ_fvar X) (open_qe_rec a (qua_fvar Y) e).
Proof. intros; symmetry; apply open_te_qe_comm_exp. Qed.

Lemma open_qe_cancel_te_exp : forall e a b X Y,
  open_qe_rec a (qua_fvar Y) (open_te_rec b (typ_fvar X) e) =
  open_qe_rec a (qua_fvar Y) e ->
  open_te_rec b (typ_fvar X) e = e.
Proof.
  intros e. induction e; intros a0 b0 X Y H; simpl in *.
  - reflexivity.
  - reflexivity.
  - injection H as H1 H2. f_equal.
    + eapply open_qqt_cancel_tqt; eassumption.
    + eapply IHe; eassumption.
  - injection H as H1 H2. f_equal; [eapply IHe1; eassumption|eapply IHe2; eassumption].
  - injection H as H1 H2. f_equal.
    + eapply open_qt_cancel_tqt; eassumption.
    + eapply IHe; eassumption.
  - injection H as H1 H2. f_equal.
    + eapply IHe; eassumption.
    + eapply open_qt_cancel_tqt; eassumption.
  - injection H as H1. f_equal. eapply IHe; eassumption.
  - injection H as H1. f_equal. eapply IHe; eassumption.
  - injection H as H1 H2. f_equal; [eapply IHe1; eassumption|eapply IHe2; eassumption].
  - injection H as H1. f_equal. eapply IHe; eassumption.
  - injection H as H1. f_equal. eapply IHe; eassumption.
  - injection H as H1 H2 H3. f_equal; [eapply IHe1; eassumption|eapply IHe2; eassumption|eapply IHe3; eassumption].
  - injection H as H1 H2. f_equal; [eapply IHe1; eassumption|eapply IHe2; eassumption].
  - injection H as H1. f_equal. eapply IHe; eassumption.
  - injection H as H1. f_equal. eapply IHe; eassumption.
  - injection H as H1. f_equal. eapply IHe; eassumption.
  - reflexivity.
  - injection H as H1. f_equal. eapply IHe; eassumption.
  - injection H as H1 H2. f_equal; [eapply IHe1; eassumption|eapply IHe2; eassumption].
  - injection H as H1. f_equal. eapply IHe; eassumption.
  - injection H as H1. f_equal. eapply IHe; eassumption.
Qed.

Lemma open_te_cancel_qe_exp : forall e a b X Y,
  open_te_rec b (typ_fvar X) (open_qe_rec a (qua_fvar Y) e) =
  open_te_rec b (typ_fvar X) e ->
  open_qe_rec a (qua_fvar Y) e = e.
Proof.
  intros e. induction e; intros a0 b0 X Y H; simpl in *.
  - reflexivity.
  - reflexivity.
  - injection H as Hp HV Hb. f_equal.
    + exact Hp.
    + eapply open_tqt_cancel_qqt; eassumption.
    + eapply IHe; eassumption.
  - injection H as H1 H2. f_equal; [eapply IHe1; eassumption|eapply IHe2; eassumption].
  - injection H as Hp HV Hb. f_equal.
    + exact Hp.
    + eapply open_tt_cancel_qqt; eassumption.
    + eapply IHe; eassumption.
  - injection H as H1 H2. f_equal.
    + eapply IHe; eassumption.
    + eapply open_tt_cancel_qqt; eassumption.
  - injection H as H1 H2 H3. f_equal.
    + exact H1.
    + exact H2.
    + eapply IHe; eassumption.
  - injection H as H1 H2. f_equal.
    + eapply IHe; eassumption.
    + exact H2.
  - injection H as H1 H2. f_equal; [eapply IHe1; eassumption|eapply IHe2; eassumption].
  - injection H as H1 H2. f_equal.
    + exact H1.
    + eapply IHe; eassumption.
  - injection H as H1 H2. f_equal.
    + exact H1.
    + eapply IHe; eassumption.
  - injection H as H1 H2 H3. f_equal; [eapply IHe1; eassumption|eapply IHe2; eassumption|eapply IHe3; eassumption].
  - injection H as H1 H2 H3. f_equal.
    + exact H1.
    + eapply IHe1; eassumption.
    + eapply IHe2; eassumption.
  - injection H as H1. f_equal. eapply IHe; eassumption.
  - injection H as H1. f_equal. eapply IHe; eassumption.
  - injection H as H1 H2. f_equal.
    + exact H1.
    + eapply IHe; eassumption.
  - injection H as H1. f_equal. exact H1.
  - injection H as H1. f_equal. eapply IHe; eassumption.
  - injection H as H1 H2. f_equal; [eapply IHe1; eassumption|eapply IHe2; eassumption].
  - injection H as H1 H2. f_equal.
    + exact H1.
    + eapply IHe; eassumption.
  - injection H as H1 H2. f_equal.
    + exact H1.
    + eapply IHe; eassumption.
Qed.


(* ===== inlined from /tmp/w2/Closed5.v ===== *)

Lemma expr_open_te_fvar : forall e, expr e -> forall j X, open_te_rec j (typ_fvar X) e = e.
Proof.
  intros e H. induction H as
    [ x
    | L P T e1 Hq HT Hq2 Hbody IHbody
    | e1 e2 H1 IH1 H2 IH2
    | L P T e1 Hq HT Hbody IHbody
    | e1 V H1 IH1 HT
    | L P Q e1 HqP HqQ Hbody IHbody
    | e1 Q H1 IH1 Hq
    | L e1 e2 H1 IH1 Hbody IHbody
    | P e1 Hq H1 IH1
    | P e1 Hq H1 IH1
    | L e1 e2 e3 H1 IH1 Hbody2 IHbody2 Hbody3 IHbody3
    | P e1 e2 Hq H1 IH1 H2 IH2
    | e1 H1 IH1
    | e1 H1 IH1
    | P e1 Hq H1 IH1
    | P e1 Hq H1 IH1 ]; intros j X.
  - reflexivity.
  - simpl. f_equal.
    + apply (qtype_open_tqt_fvar T HT j X).
    + destruct (atom_fresh L) as [y Hy].
      assert (Hc := IHbody y Hy (S j) X).
      unfold open_ee in Hc.
      rewrite <- (open_ee_comm_te 0 (S j) y (typ_fvar X) e1) in Hc.
      exact (open_te_cancel_ee e1 (S j) (typ_fvar X) 0 y Hc).
  - simpl. f_equal; [apply IH1|apply IH2].
  - simpl. f_equal.
    + apply (type_open_tt_fvar T HT j X).
    + destruct (atom_fresh L) as [Y HY].
      assert (Hc := IHbody Y HY (S j) X).
      unfold open_te in Hc.
      rewrite (open_te_swap_exp e1 (S j) 0 Y X (ltac:(congruence))) in Hc.
      exact (open_te_cancel_te e1 0 (S j) X Y (ltac:(congruence)) Hc).
  - simpl. f_equal.
    + apply IH1.
    + apply (type_open_tt_fvar V HT j X).
  - simpl. f_equal.
    destruct (atom_fresh L) as [Y HY].
    assert (Hc := IHbody Y HY (S j) X).
    unfold open_qe in Hc.
    rewrite (open_te_qe_comm_exp e1 (S j) 0 X Y) in Hc.
    exact (open_qe_cancel_te_exp e1 0 (S j) X Y Hc).
  - simpl. f_equal. apply IH1.
  - simpl. f_equal.
    + apply IH1.
    + destruct (atom_fresh L) as [y Hy].
      assert (Hc := IHbody y Hy (S j) X).
      unfold open_ee in Hc.
      rewrite <- (open_ee_comm_te 0 (S j) y (typ_fvar X) e2) in Hc.
      exact (open_te_cancel_ee e2 (S j) (typ_fvar X) 0 y Hc).
  - simpl. f_equal. apply IH1.
  - simpl. f_equal. apply IH1.
  - simpl. f_equal.
    + apply IH1.
    + destruct (atom_fresh L) as [y Hy].
      assert (Hc := IHbody2 y Hy (S j) X).
      unfold open_ee in Hc.
      rewrite <- (open_ee_comm_te 0 (S j) y (typ_fvar X) e2) in Hc.
      exact (open_te_cancel_ee e2 (S j) (typ_fvar X) 0 y Hc).
    + destruct (atom_fresh L) as [y Hy].
      assert (Hc := IHbody3 y Hy (S j) X).
      unfold open_ee in Hc.
      rewrite <- (open_ee_comm_te 0 (S j) y (typ_fvar X) e3) in Hc.
      exact (open_te_cancel_ee e3 (S j) (typ_fvar X) 0 y Hc).
  - simpl. f_equal; [apply IH1|apply IH2].
  - simpl. f_equal. apply IH1.
  - simpl. f_equal. apply IH1.
  - simpl. f_equal. apply IH1.
  - simpl. f_equal. apply IH1.
Qed.

Lemma expr_open_qe_fvar : forall e, expr e -> forall j X, open_qe_rec j (qua_fvar X) e = e.
Proof.
  intros e H. induction H as
    [ x
    | L P T e1 Hq HT Hq2 Hbody IHbody
    | e1 e2 H1 IH1 H2 IH2
    | L P T e1 Hq HT Hbody IHbody
    | e1 V H1 IH1 HT
    | L P Q e1 HqP HqQ Hbody IHbody
    | e1 Q H1 IH1 Hq
    | L e1 e2 H1 IH1 Hbody IHbody
    | P e1 Hq H1 IH1
    | P e1 Hq H1 IH1
    | L e1 e2 e3 H1 IH1 Hbody2 IHbody2 Hbody3 IHbody3
    | P e1 e2 Hq H1 IH1 H2 IH2
    | e1 H1 IH1
    | e1 H1 IH1
    | P e1 Hq H1 IH1
    | P e1 Hq H1 IH1 ]; intros j X.
  - reflexivity.
  - simpl. f_equal.
    + apply (qual_open_qq P Hq j X).
    + apply (qtype_open_qqt_fvar T HT j X).
    + destruct (atom_fresh L) as [y Hy].
      assert (Hc := IHbody y Hy (S j) X).
      unfold open_ee in Hc.
      rewrite <- (open_ee_comm_qe 0 (S j) y (qua_fvar X) e1) in Hc.
      exact (open_qe_cancel_ee e1 (S j) (qua_fvar X) 0 y Hc).
  - simpl. f_equal; [apply IH1|apply IH2].
  - simpl. f_equal.
    + apply (qual_open_qq P Hq j X).
    + apply (type_open_qt_fvar T HT j X).
    + destruct (atom_fresh L) as [Y HY].
      assert (Hc := IHbody Y HY (S j) X).
      unfold open_te in Hc.
      rewrite (open_qe_te_comm_exp e1 0 (S j) Y X) in Hc.
      exact (open_te_cancel_qe_exp e1 (S j) 0 Y X Hc).
  - simpl. f_equal.
    + apply IH1.
    + apply (type_open_qt_fvar V HT j X).
  - simpl. f_equal.
    + apply (qual_open_qq P HqP j X).
    + apply (qual_open_qq Q HqQ j X).
    + destruct (atom_fresh L) as [Y HY].
      assert (Hc := IHbody Y HY (S j) X).
      unfold open_qe in Hc.
      rewrite (open_qe_swap_exp e1 (S j) 0 Y X (ltac:(congruence))) in Hc.
      exact (open_qe_cancel_qe e1 0 (S j) X Y (ltac:(congruence)) Hc).
  - simpl. f_equal.
    + apply IH1.
    + apply (qual_open_qq Q Hq j X).
  - simpl. f_equal.
    + apply IH1.
    + destruct (atom_fresh L) as [y Hy].
      assert (Hc := IHbody y Hy (S j) X).
      unfold open_ee in Hc.
      rewrite <- (open_ee_comm_qe 0 (S j) y (qua_fvar X) e2) in Hc.
      exact (open_qe_cancel_ee e2 (S j) (qua_fvar X) 0 y Hc).
  - simpl. f_equal; [apply (qual_open_qq P Hq j X)|apply IH1].
  - simpl. f_equal; [apply (qual_open_qq P Hq j X)|apply IH1].
  - simpl. f_equal.
    + apply IH1.
    + destruct (atom_fresh L) as [y Hy].
      assert (Hc := IHbody2 y Hy (S j) X).
      unfold open_ee in Hc.
      rewrite <- (open_ee_comm_qe 0 (S j) y (qua_fvar X) e2) in Hc.
      exact (open_qe_cancel_ee e2 (S j) (qua_fvar X) 0 y Hc).
    + destruct (atom_fresh L) as [y Hy].
      assert (Hc := IHbody3 y Hy (S j) X).
      unfold open_ee in Hc.
      rewrite <- (open_ee_comm_qe 0 (S j) y (qua_fvar X) e3) in Hc.
      exact (open_qe_cancel_ee e3 (S j) (qua_fvar X) 0 y Hc).
  - simpl. f_equal; [apply (qual_open_qq P Hq j X)|apply IH1|apply IH2].
  - simpl. f_equal. apply IH1.
  - simpl. f_equal. apply IH1.
  - simpl. f_equal; [apply (qual_open_qq P Hq j X)|apply IH1].
  - simpl. f_equal; [apply (qual_open_qq P Hq j X)|apply IH1].
Qed.


(* ===== inlined from /tmp/w2/Closed6.v ===== *)

Lemma typing_open_te_fvar : forall E Q e T, typing E Q e T ->
  forall j X, open_te_rec j (typ_fvar X) e = e.
Proof. intros. apply expr_open_te_fvar. eapply typing_expr; eassumption. Qed.

Lemma typing_open_qe_fvar : forall E Q e T, typing E Q e T ->
  forall j X, open_qe_rec j (qua_fvar X) e = e.
Proof. intros. apply expr_open_qe_fvar. eapply typing_expr; eassumption. Qed.

Lemma subst_ee_open_te_comm_inv : forall x v e,
  (forall j X, open_te_rec j (typ_fvar X) v = v) ->
  forall j X, subst_ee x v (open_te_rec j (typ_fvar X) e) =
             open_te_rec j (typ_fvar X) (subst_ee x v e).
Proof.
  intros x v e Hinv. induction e; intros j X; simpl.
  - reflexivity.
  - destruct (x == a) as [Heq|Hne]; [subst; symmetry; apply Hinv|reflexivity].
  - f_equal; apply IHe.
  - f_equal; [apply IHe1|apply IHe2].
  - f_equal; apply IHe.
  - f_equal; apply IHe.
  - f_equal; apply IHe.
  - f_equal; apply IHe.
  - f_equal; [apply IHe1|apply IHe2].
  - f_equal; apply IHe.
  - f_equal; apply IHe.
  - f_equal; [apply IHe1|apply IHe2|apply IHe3].
  - f_equal; [apply IHe1|apply IHe2].
  - f_equal; apply IHe.
  - f_equal; apply IHe.
  - f_equal; apply IHe.
  - reflexivity.
  - f_equal; apply IHe.
  - f_equal; [apply IHe1|apply IHe2].
  - f_equal; apply IHe.
  - f_equal; apply IHe.
Qed.

Lemma subst_ee_open_qe_comm_inv : forall x v e,
  (forall j X, open_qe_rec j (qua_fvar X) v = v) ->
  forall j X, subst_ee x v (open_qe_rec j (qua_fvar X) e) =
             open_qe_rec j (qua_fvar X) (subst_ee x v e).
Proof.
  intros x v e Hinv. induction e; intros j X; simpl.
  - reflexivity.
  - destruct (x == a) as [Heq|Hne]; [subst; symmetry; apply Hinv|reflexivity].
  - f_equal; apply IHe.
  - f_equal; [apply IHe1|apply IHe2].
  - f_equal; apply IHe.
  - f_equal; apply IHe.
  - f_equal; apply IHe.
  - f_equal; apply IHe.
  - f_equal; [apply IHe1|apply IHe2].
  - f_equal; apply IHe.
  - f_equal; apply IHe.
  - f_equal; [apply IHe1|apply IHe2|apply IHe3].
  - f_equal; [apply IHe1|apply IHe2].
  - f_equal; apply IHe.
  - f_equal; apply IHe.
  - f_equal; apply IHe.
  - reflexivity.
  - f_equal; apply IHe.
  - f_equal; [apply IHe1|apply IHe2].
  - f_equal; apply IHe.
  - f_equal; apply IHe.
Qed.

(* term-opening commutation for substitution under a term binder. *)
Lemma subst_ee_open_comm : forall (x : atom) (v : exp) (e : exp) (k : nat) (y : atom),
  closed_exp v -> x <> y -> y `notin` fv_ee v ->
  subst_ee x v (open_ee_rec k (exp_fvar y) e) =
  open_ee_rec k (exp_fvar y) (subst_ee x v e).
Proof.
  intros x v e. induction e; intros k0 y Hc Hxy Hyv; simpl.
  - destruct (k0 == n); simpl.
    + destruct (x == y) as [Heq|Hne]; [subst; exfalso; apply Hxy; reflexivity|reflexivity].
    + reflexivity.
  - destruct (x == a) as [Heq|Hne].
    + subst. simpl. symmetry. apply Hc.
    + reflexivity.
  - f_equal. apply IHe; assumption.
  - f_equal; [apply IHe1|apply IHe2]; assumption.
  - f_equal. apply IHe; assumption.
  - f_equal. apply IHe; assumption.
  - f_equal. apply IHe; assumption.
  - f_equal. apply IHe; assumption.
  - f_equal; [apply IHe1|apply IHe2]; assumption.
  - f_equal. apply IHe; assumption.
  - f_equal. apply IHe; assumption.
  - f_equal; [apply IHe1|apply IHe2|apply IHe3]; assumption.
  - f_equal; [apply IHe1|apply IHe2]; assumption.
  - f_equal. apply IHe; assumption.
  - f_equal. apply IHe; assumption.
  - f_equal. apply IHe; assumption.
  - reflexivity.
  - f_equal. apply IHe; assumption.
  - f_equal; [apply IHe1|apply IHe2]; assumption.
  - f_equal. apply IHe; assumption.
  - f_equal. apply IHe; assumption.
Qed.


(* ===== inlined from /tmp/w2/SubstE.v ===== *)

Definition subst_ee_motive (E : env) (Q : qua) (e : exp) (T : qtyp) : Prop :=
  forall (x : atom) (v : exp) (V : qtyp) (E1 E2 : env),
    wf_env E ->
    E = E1 ++ x ~ bind_typ V ++ E2 ->
    typing (E1 ++ E2) qua_bot v V ->
    typing (E1 ++ E2) Q (subst_ee x v e) T.

Lemma eq_cons_mid : forall E1 E2 (x y : atom) (B : binding) (V : qtyp),
  (y ~ B ++ (E1 ++ x ~ bind_typ V ++ E2)) =
  ((y ~ B ++ E1) ++ x ~ bind_typ V ++ E2).
Proof. intros. rewrite <- app_assoc. reflexivity. Qed.

Lemma typing_weaken_mid_binder : forall E1 E2 (x : atom) (V : qtyp)
  (y : atom) (B : binding) (v : exp) (Vb : qtyp),
  wf_env ((y ~ B ++ E1) ++ x ~ bind_typ V ++ E2) ->
  typing (E1 ++ E2) qua_bot v Vb ->
  typing ((y ~ B ++ E1) ++ E2) qua_bot v Vb.
Proof.
  intros E1 E2 x V y B v Vb Hwf Hty.
  assert (Hwf' : wf_env ((y ~ B ++ E1) ++ E2)).
  { apply (wf_env_mid_remove (y ~ B ++ E1) E2 x V). exact Hwf. }
  apply (typing_weaken (E1 ++ E2) qua_bot v Vb Hty ((y ~ B ++ E1) ++ E2) Hwf').
  eapply env_extends_trans with (E2 := (y ~ B) ++ (E1 ++ E2)).
  - apply env_extends_cons_tail.
  - rewrite app_assoc. apply env_extends_refl.
Qed.

Lemma typing_subst_ee_gen_aux : forall E Q e T,
  typing E Q e T -> subst_ee_motive E Q e T.
Proof.
  intros E Q e T Hty.
  change (subst_ee_motive E Q e T).
  apply typing_ind with (P := subst_ee_motive).
  - (* var *) intros E0 y T0 Hwf Hb. unfold subst_ee_motive.
    intros x v V E1 E2 Hwf0 Heq Hv. subst E0.
    simpl. destruct (x == y) as [Hxy|Hxy].
    + subst y.
      assert (HbV : binds x (bind_typ V) (E1 ++ x ~ bind_typ V ++ E2)).
      { apply binds_app_3. apply binds_app_2. apply binds_cons_2; reflexivity. }
      assert (Hbeq : bind_typ T0 = bind_typ V) by
        (eapply (binds_unique binding x (bind_typ T0) (bind_typ V) (E1 ++ x ~ bind_typ V ++ E2));
         [exact Hb|exact HbV|apply wf_env_uniq; exact Hwf0]).
      injection Hbeq as HTV. subst T0. exact Hv.
    + assert (Hb' : binds y (bind_typ T0) (E1 ++ E2)).
      { apply (binds_mid_remove E1 E2 x V y (bind_typ T0) Hb). intro H; apply Hxy; symmetry; exact H. }
      assert (Hwf' : wf_env (E1 ++ E2)) by (apply (wf_env_mid_remove E1 E2 x V Hwf)).
      eapply typing_var; eassumption.
  - (* abs *) intros L E0 P V0 e1 T1 Hbody IHbody. unfold subst_ee_motive.
    intros x v V E1 E2 Hwf Heq Hv. subst E0.
    set (L' := L \u dom (E1 ++ x ~ bind_typ V ++ E2) \u dom (E1 ++ E2) \u fv_ee v \u singleton x).
    eapply typing_abs with (L := L').
    + intros y Hy.
      assert (HyL : y `notin` L) by (unfold L' in Hy; fsetdec).
      assert (Hyd : y `notin` dom (E1 ++ x ~ bind_typ V ++ E2)) by (unfold L' in Hy; fsetdec).
      assert (Hxd : y <> x) by (unfold L' in Hy; fsetdec).
      assert (Hyv : y `notin` fv_ee v) by (unfold L' in Hy; fsetdec).
      (* get wf_qtyp of V0 in Ebody *)
      destruct (atom_fresh L) as [y0 Hy0].
      assert (Hwfb : wf_env (y0 ~ bind_typ V0 ++ (E1 ++ x ~ bind_typ V ++ E2))).
      { eapply typing_wf_env. apply Hbody. exact Hy0. }
      assert (HwqV0 : wf_qtyp (E1 ++ x ~ bind_typ V ++ E2) V0).
      { eapply wf_env_cons_wf_qtyp; exact Hwfb. }
      assert (Hwfo : wf_env (y ~ bind_typ V0 ++ (E1 ++ x ~ bind_typ V ++ E2))).
      { eapply wf_env_typ; [exact Hwf|exact HwqV0|exact Hyd]. }
      assert (Htyb := IHbody y HyL x v V (y ~ bind_typ V0 ++ E1) E2 Hwfo (eq_cons_mid E1 E2 x y (bind_typ V0) V)
        (typing_weaken_mid_binder E1 E2 x V y (bind_typ V0) v V Hwfo Hv)).
      assert (Hc : subst_ee x v (open_ee e1 y) = open_ee (subst_ee x v e1) y).
      { assert (Hcl : closed_exp v) by (apply typing_closed with (E := E1 ++ E2) (Q := qua_bot) (T := V); exact Hv).
        apply (subst_ee_open_comm x v e1 0 y); [exact Hcl | (intro Hxy; apply Hxd; symmetry; exact Hxy) | exact Hyv]. }
      rewrite Hc in Htyb. exact Htyb.
  - (* app *) intros Q0 T1 E0 e1 e2 T2 H1 IH1 H2 IH2. unfold subst_ee_motive.
    intros x v V E1 E2 Hwf Heq Hv. subst E0.
    eapply typing_app.
    + exact (IH1 x v V E1 E2 Hwf eq_refl Hv).
    + exact (IH2 x v V E1 E2 Hwf eq_refl Hv).
  - (* tabs *) intros L E0 P V0 e1 T1 Hbody IHbody. unfold subst_ee_motive.
    intros x v V E1 E2 Hwf Heq Hv. subst E0.
    set (L' := L \u dom (E1 ++ x ~ bind_typ V ++ E2) \u dom (E1 ++ E2) \u fv_ee v \u singleton x).
    eapply typing_tabs with (L := L').
    + intros y Hy.
      assert (HyL : y `notin` L) by (unfold L' in Hy; fsetdec).
      assert (Hyd : y `notin` dom (E1 ++ x ~ bind_typ V ++ E2)) by (unfold L' in Hy; fsetdec).
      destruct (atom_fresh L) as [y0 Hy0].
      assert (Hwfb : wf_env (y0 ~ bind_sub V0 ++ (E1 ++ x ~ bind_typ V ++ E2))).
      { eapply typing_wf_env. apply Hbody. exact Hy0. }
      assert (HwtV0 : wf_typ (E1 ++ x ~ bind_typ V ++ E2) V0).
      { eapply wf_env_cons_wf_typ; exact Hwfb. }
      assert (Hwfo : wf_env (y ~ bind_sub V0 ++ (E1 ++ x ~ bind_typ V ++ E2))).
      { eapply wf_env_sub; [exact Hwf|exact HwtV0|exact Hyd]. }
      assert (Htyb := IHbody y HyL x v V (y ~ bind_sub V0 ++ E1) E2 Hwfo (eq_cons_mid E1 E2 x y (bind_sub V0) V)
        (typing_weaken_mid_binder E1 E2 x V y (bind_sub V0) v V Hwfo Hv)).
      assert (Hinv : forall j X, open_te_rec j (typ_fvar X) v = v) by (apply typing_open_te_fvar with (E := E1 ++ E2) (Q := qua_bot) (T := V); exact Hv).
      unfold open_te in Htyb.
      rewrite (subst_ee_open_te_comm_inv x v e1 Hinv 0 y) in Htyb.
      exact Htyb.
  - (* tapp *) intros Q0 T1 E0 e1 T0 T2 H1 IH1 Hsub. unfold subst_ee_motive.
    intros x v V E1 E2 Hwf Heq Hv. subst E0.
    assert (Hwf' : wf_env (E1 ++ E2)) by (eapply wf_env_mid_remove; eassumption).
    assert (Hext : env_subqua_extends (E1 ++ x ~ bind_typ V ++ E2) (E1 ++ E2)).
    { eapply env_subqua_extends_mid; exact Hwf. }
    assert (Hsub' : sub (E1 ++ E2) T0 T1).
    { eapply sub_subqua; [exact Hwf|exact Hsub|exact Hwf'|exact Hext]. }
    eapply typing_tapp.
    + exact (IH1 x v V E1 E2 Hwf eq_refl Hv).
    + exact Hsub'.
  - (* qabs *) intros L E0 P Q0 e1 T1 HwfP Hbody IHbody. unfold subst_ee_motive.
    intros x v V E1 E2 Hwf Heq Hv. subst E0.
    set (L' := L \u dom (E1 ++ x ~ bind_typ V ++ E2) \u dom (E1 ++ E2) \u fv_ee v \u singleton x).
    assert (Hwf' : wf_env (E1 ++ E2)) by (eapply wf_env_mid_remove; eassumption).
    assert (Hext : env_subqua_extends (E1 ++ x ~ bind_typ V ++ E2) (E1 ++ E2)).
    { eapply env_subqua_extends_mid; exact Hwf. }
    assert (HwfP' : wf_qua (E1 ++ E2) P).
    { eapply wf_qua_subqua; [exact HwfP|exact Hext]. }
    eapply typing_qabs with (L := L').
    + exact HwfP'.
    + intros y Hy.
      assert (HyL : y `notin` L) by (unfold L' in Hy; fsetdec).
      assert (Hyd : y `notin` dom (E1 ++ x ~ bind_typ V ++ E2)) by (unfold L' in Hy; fsetdec).
      destruct (atom_fresh L) as [y0 Hy0].
      assert (Hwfb : wf_env (y0 ~ bind_qua Q0 ++ (E1 ++ x ~ bind_typ V ++ E2))).
      { eapply typing_wf_env. apply Hbody. exact Hy0. }
      assert (HwqQ0 : wf_qua (E1 ++ x ~ bind_typ V ++ E2) Q0).
      { eapply wf_env_cons_wf_qua; exact Hwfb. }
      assert (Hwfo : wf_env (y ~ bind_qua Q0 ++ (E1 ++ x ~ bind_typ V ++ E2))).
      { eapply wf_env_qua; [exact Hwf|exact HwqQ0|exact Hyd]. }
      assert (Htyb := IHbody y HyL x v V (y ~ bind_qua Q0 ++ E1) E2 Hwfo (eq_cons_mid E1 E2 x y (bind_qua Q0) V)
        (typing_weaken_mid_binder E1 E2 x V y (bind_qua Q0) v V Hwfo Hv)).
      assert (Hinv : forall j X, open_qe_rec j (qua_fvar X) v = v) by (apply typing_open_qe_fvar with (E := E1 ++ E2) (Q := qua_bot) (T := V); exact Hv).
      unfold open_qe in Htyb.
      rewrite (subst_ee_open_qe_comm_inv x v e1 Hinv 0 y) in Htyb.
      exact Htyb.
  - (* qapp *) intros Q0 E0 e1 Q1 T0 H1 IH1 Hsubq. unfold subst_ee_motive.
    intros x v V E1 E2 Hwf Heq Hv. subst E0.
    assert (Hwf' : wf_env (E1 ++ E2)) by (eapply wf_env_mid_remove; eassumption).
    assert (Hext : env_subqua_extends (E1 ++ x ~ bind_typ V ++ E2) (E1 ++ E2)).
    { eapply env_subqua_extends_mid; exact Hwf. }
    assert (Hsubq' : subqual (E1 ++ E2) Q0 Q1).
    { eapply subqual_subqua; [exact Hsubq|exact Hwf'|exact Hext]. }
    eapply typing_qapp.
    + exact (IH1 x v V E1 E2 Hwf eq_refl Hv).
    + exact Hsubq'.
  - (* typing_sub *) intros S E0 Q0 e1 T0 H1 IH1 Hsub. unfold subst_ee_motive.
    intros x v V E1 E2 Hwf Heq Hv. subst E0.
    assert (Hwf' : wf_env (E1 ++ E2)) by (eapply wf_env_mid_remove; eassumption).
    assert (Hext : env_subqua_extends (E1 ++ x ~ bind_typ V ++ E2) (E1 ++ E2)).
    { eapply env_subqua_extends_mid; exact Hwf. }
    assert (Hsub' : subqtype (E1 ++ E2) S T0).
    { eapply subqtype_subqua; [exact Hwf|exact Hsub|exact Hwf'|exact Hext]. }
    eapply typing_sub.
    + exact (IH1 x v V E1 E2 Hwf eq_refl Hv).
    + exact Hsub'.
  - (* typing_subqual *) intros E0 Q0 R e1 T0 H1 IH1 Hsq. unfold subst_ee_motive.
    intros x v V E1 E2 Hwf Heq Hv. subst E0.
    assert (Hwf' : wf_env (E1 ++ E2)) by (eapply wf_env_mid_remove; eassumption).
    assert (Hext : env_subqua_extends (E1 ++ x ~ bind_typ V ++ E2) (E1 ++ E2)).
    { eapply env_subqua_extends_mid; exact Hwf. }
    assert (Hsq' : subqual (E1 ++ E2) Q0 R).
    { eapply subqual_subqua; [exact Hsq|exact Hwf'|exact Hext]. }
    eapply typing_subqual.
    + exact (IH1 x v V E1 E2 Hwf eq_refl Hv).
    + exact Hsq'.
  - (* let *) intros L T1 T2 e1 e2 E0 Q0 H1 IH1 Hbody IHbody. unfold subst_ee_motive.
    intros x v V E1 E2 Hwf Heq Hv. subst E0.
    set (L' := L \u dom (E1 ++ x ~ bind_typ V ++ E2) \u dom (E1 ++ E2) \u fv_ee v \u singleton x).
    eapply typing_let with (L := L').
    + exact (IH1 x v V E1 E2 Hwf eq_refl Hv).
    + intros y Hy.
      assert (HyL : y `notin` L) by (unfold L' in Hy; fsetdec).
      assert (Hyd : y `notin` dom (E1 ++ x ~ bind_typ V ++ E2)) by (unfold L' in Hy; fsetdec).
      assert (Hxd : y <> x) by (unfold L' in Hy; fsetdec).
      assert (Hyv : y `notin` fv_ee v) by (unfold L' in Hy; fsetdec).
      destruct (atom_fresh L) as [y0 Hy0].
      assert (Hwfb : wf_env (y0 ~ bind_typ T1 ++ (E1 ++ x ~ bind_typ V ++ E2))).
      { eapply typing_wf_env. apply Hbody. exact Hy0. }
      assert (HwqT1 : wf_qtyp (E1 ++ x ~ bind_typ V ++ E2) T1).
      { eapply wf_env_cons_wf_qtyp; exact Hwfb. }
      assert (Hwfo : wf_env (y ~ bind_typ T1 ++ (E1 ++ x ~ bind_typ V ++ E2))).
      { eapply wf_env_typ; [exact Hwf|exact HwqT1|exact Hyd]. }
      assert (Htyb := IHbody y HyL x v V (y ~ bind_typ T1 ++ E1) E2 Hwfo (eq_cons_mid E1 E2 x y (bind_typ T1) V)
        (typing_weaken_mid_binder E1 E2 x V y (bind_typ T1) v V Hwfo Hv)).
      assert (Hc : subst_ee x v (open_ee e2 y) = open_ee (subst_ee x v e2) y).
      { assert (Hcl : closed_exp v) by (apply typing_closed with (E := E1 ++ E2) (Q := qua_bot) (T := V); exact Hv).
        apply (subst_ee_open_comm x v e2 0 y); [exact Hcl | (intro Hxy; apply Hxd; symmetry; exact Hxy) | exact Hyv]. }
      rewrite Hc in Htyb. exact Htyb.
  - (* inl *) intros T1 T2 P e1 E0 Q0 HwfP H1 IH1 HwfT2. unfold subst_ee_motive.
    intros x v V E1 E2 Hwf Heq Hv. subst E0.
    assert (Hwf' : wf_env (E1 ++ E2)) by (eapply wf_env_mid_remove; eassumption).
    assert (Hext : env_subqua_extends (E1 ++ x ~ bind_typ V ++ E2) (E1 ++ E2)).
    { eapply env_subqua_extends_mid; exact Hwf. }
    assert (HwfP' : wf_qua (E1 ++ E2) P).
    { eapply wf_qua_subqua; [exact HwfP|exact Hext]. }
    assert (HwfT2' : wf_qtyp (E1 ++ E2) T2).
    { eapply wf_qtyp_subqua; [exact HwfT2|exact Hwf'|exact Hext]. }
    eapply typing_inl.
    + exact HwfP'.
    + exact (IH1 x v V E1 E2 Hwf eq_refl Hv).
    + exact HwfT2'.
  - (* inr *) intros T1 T2 P e1 E0 Q0 HwfP H1 IH1 HwfT1. unfold subst_ee_motive.
    intros x v V E1 E2 Hwf Heq Hv. subst E0.
    assert (Hwf' : wf_env (E1 ++ E2)) by (eapply wf_env_mid_remove; eassumption).
    assert (Hext : env_subqua_extends (E1 ++ x ~ bind_typ V ++ E2) (E1 ++ E2)).
    { eapply env_subqua_extends_mid; exact Hwf. }
    assert (HwfP' : wf_qua (E1 ++ E2) P).
    { eapply wf_qua_subqua; [exact HwfP|exact Hext]. }
    assert (HwfT1' : wf_qtyp (E1 ++ E2) T1).
    { eapply wf_qtyp_subqua; [exact HwfT1|exact Hwf'|exact Hext]. }
    eapply typing_inr.
    + exact HwfP'.
    + exact (IH1 x v V E1 E2 Hwf eq_refl Hv).
    + exact HwfT1'.
  - (* case *) intros L T1 T2 P T0 e1 e2 e3 E0 Q0 H1 IH1 Hbody2 IHbody2 Hbody3 IHbody3. unfold subst_ee_motive.
    intros x v V E1 E2 Hwf Heq Hv. subst E0.
    set (L' := L \u dom (E1 ++ x ~ bind_typ V ++ E2) \u dom (E1 ++ E2) \u fv_ee v \u singleton x).
    eapply typing_case with (L := L').
    + exact (IH1 x v V E1 E2 Hwf eq_refl Hv).
    + intros y Hy.
      assert (HyL : y `notin` L) by (unfold L' in Hy; fsetdec).
      assert (Hyd : y `notin` dom (E1 ++ x ~ bind_typ V ++ E2)) by (unfold L' in Hy; fsetdec).
      assert (Hxd : y <> x) by (unfold L' in Hy; fsetdec).
      assert (Hyv : y `notin` fv_ee v) by (unfold L' in Hy; fsetdec).
      destruct (atom_fresh L) as [y0 Hy0].
      assert (Hwfb : wf_env (y0 ~ bind_typ T1 ++ (E1 ++ x ~ bind_typ V ++ E2))).
      { eapply typing_wf_env. apply Hbody2. exact Hy0. }
      assert (HwqT1 : wf_qtyp (E1 ++ x ~ bind_typ V ++ E2) T1).
      { eapply wf_env_cons_wf_qtyp; exact Hwfb. }
      assert (Hwfo : wf_env (y ~ bind_typ T1 ++ (E1 ++ x ~ bind_typ V ++ E2))).
      { eapply wf_env_typ; [exact Hwf|exact HwqT1|exact Hyd]. }
      assert (Htyb := IHbody2 y HyL x v V (y ~ bind_typ T1 ++ E1) E2 Hwfo (eq_cons_mid E1 E2 x y (bind_typ T1) V)
        (typing_weaken_mid_binder E1 E2 x V y (bind_typ T1) v V Hwfo Hv)).
      assert (Hc : subst_ee x v (open_ee e2 y) = open_ee (subst_ee x v e2) y).
      { assert (Hcl : closed_exp v) by (apply typing_closed with (E := E1 ++ E2) (Q := qua_bot) (T := V); exact Hv).
        apply (subst_ee_open_comm x v e2 0 y); [exact Hcl | (intro Hxy; apply Hxd; symmetry; exact Hxy) | exact Hyv]. }
      rewrite Hc in Htyb. exact Htyb.
    + intros y Hy.
      assert (HyL : y `notin` L) by (unfold L' in Hy; fsetdec).
      assert (Hyd : y `notin` dom (E1 ++ x ~ bind_typ V ++ E2)) by (unfold L' in Hy; fsetdec).
      assert (Hxd : y <> x) by (unfold L' in Hy; fsetdec).
      assert (Hyv : y `notin` fv_ee v) by (unfold L' in Hy; fsetdec).
      destruct (atom_fresh L) as [y0 Hy0].
      assert (Hwfb : wf_env (y0 ~ bind_typ T2 ++ (E1 ++ x ~ bind_typ V ++ E2))).
      { eapply typing_wf_env. apply Hbody3. exact Hy0. }
      assert (HwqT2 : wf_qtyp (E1 ++ x ~ bind_typ V ++ E2) T2).
      { eapply wf_env_cons_wf_qtyp; exact Hwfb. }
      assert (Hwfo : wf_env (y ~ bind_typ T2 ++ (E1 ++ x ~ bind_typ V ++ E2))).
      { eapply wf_env_typ; [exact Hwf|exact HwqT2|exact Hyd]. }
      assert (Htyb := IHbody3 y HyL x v V (y ~ bind_typ T2 ++ E1) E2 Hwfo (eq_cons_mid E1 E2 x y (bind_typ T2) V)
        (typing_weaken_mid_binder E1 E2 x V y (bind_typ T2) v V Hwfo Hv)).
      assert (Hc : subst_ee x v (open_ee e3 y) = open_ee (subst_ee x v e3) y).
      { assert (Hcl : closed_exp v) by (apply typing_closed with (E := E1 ++ E2) (Q := qua_bot) (T := V); exact Hv).
        apply (subst_ee_open_comm x v e3 0 y); [exact Hcl | (intro Hxy; apply Hxd; symmetry; exact Hxy) | exact Hyv]. }
      rewrite Hc in Htyb. exact Htyb.
  - (* pair *) intros T1 T2 P e1 e2 E0 Q0 HwfP H1 IH1 H2 IH2. unfold subst_ee_motive.
    intros x v V E1 E2 Hwf Heq Hv. subst E0.
    assert (Hwf' : wf_env (E1 ++ E2)) by (eapply wf_env_mid_remove; eassumption).
    assert (Hext : env_subqua_extends (E1 ++ x ~ bind_typ V ++ E2) (E1 ++ E2)).
    { eapply env_subqua_extends_mid; exact Hwf. }
    assert (HwfP' : wf_qua (E1 ++ E2) P).
    { eapply wf_qua_subqua; [exact HwfP|exact Hext]. }
    eapply typing_pair.
    + exact HwfP'.
    + exact (IH1 x v V E1 E2 Hwf eq_refl Hv).
    + exact (IH2 x v V E1 E2 Hwf eq_refl Hv).
  - (* first *) intros Q0 T1 T2 P e1 E0 H1 IH1. unfold subst_ee_motive.
    intros x v V E1 E2 Hwf Heq Hv. subst E0.
    eapply typing_first. exact (IH1 x v V E1 E2 Hwf eq_refl Hv).
  - (* second *) intros Q0 T1 T2 P e1 E0 H1 IH1. unfold subst_ee_motive.
    intros x v V E1 E2 Hwf Heq Hv. subst E0.
    eapply typing_second. exact (IH1 x v V E1 E2 Hwf eq_refl Hv).
  - (* upqual *) intros E0 R Q0 T0 P e1 H1 IH1 Hsq. unfold subst_ee_motive.
    intros x v V E1 E2 Hwf Heq Hv. subst E0.
    assert (Hwf' : wf_env (E1 ++ E2)) by (eapply wf_env_mid_remove; eassumption).
    assert (Hext : env_subqua_extends (E1 ++ x ~ bind_typ V ++ E2) (E1 ++ E2)).
    { eapply env_subqua_extends_mid; exact Hwf. }
    assert (Hsq' : subqual (E1 ++ E2) Q0 P).
    { eapply subqual_subqua; [exact Hsq|exact Hwf'|exact Hext]. }
    eapply typing_upqual.
    + exact (IH1 x v V E1 E2 Hwf eq_refl Hv).
    + exact Hsq'.
  - (* check *) intros E0 R Q0 T0 P e1 H1 IH1 Hsq. unfold subst_ee_motive.
    intros x v V E1 E2 Hwf Heq Hv. subst E0.
    assert (Hwf' : wf_env (E1 ++ E2)) by (eapply wf_env_mid_remove; eassumption).
    assert (Hext : env_subqua_extends (E1 ++ x ~ bind_typ V ++ E2) (E1 ++ E2)).
    { eapply env_subqua_extends_mid; exact Hwf. }
    assert (Hsq' : subqual (E1 ++ E2) Q0 P).
    { eapply subqual_subqua; [exact Hsq|exact Hwf'|exact Hext]. }
    eapply typing_check.
    + exact (IH1 x v V E1 E2 Hwf eq_refl Hv).
    + exact Hsq'.
- exact Hty.
Qed.




Theorem typing_subst_ee_gen : forall (E : env) (Q : qua) (e : exp) (T : qtyp),
  typing E Q e T ->
  forall (x : atom) (v : exp) (V : qtyp) (E1 E2 : env),
    wf_env E ->
    E = E1 ++ x ~ bind_typ V ++ E2 ->
    typing (E1 ++ E2) qua_bot v V ->
    typing (E1 ++ E2) Q (subst_ee x v e) T.
Proof. intros. eapply typing_subst_ee_gen_aux; eassumption. Qed.


(* ===== inlined from /tmp/w4/InvExpr.v ===== *)

Lemma typing_var_inv : forall E Q e T,
  typing E Q e T ->
  forall vx, e = exp_fvar vx ->
  exists T0, binds vx (bind_typ T0) E /\ qsubR E T0 T /\ qualR E qua_bot Q.
Proof.
  intros E Q e T Hty. dependent induction Hty; intros vx Heq; try discriminate Heq.
  - (* typing_var *) inversion Heq; subst.
    exists T. split; [|split].
    + assumption.
    + apply qsubR_refl.
    + apply qualR_refl.
  - (* typing_sub *) inversion Heq; subst.
    destruct (IHHty vx eq_refl) as [T0 [Hb [Hq Hqual]]].
    exists T0. split; [|split].
    + assumption.
    + apply qsubR_step with (T := S); assumption.
    + assumption.
  - (* typing_subqual *) inversion Heq; subst.
    destruct (IHHty vx eq_refl) as [T0 [Hb [Hq Hqual]]].
    exists T0. split; [|split].
    + assumption.
    + assumption.
    + apply qualR_step with (R := Q); assumption.
Qed.

Lemma typing_abs_inv : forall E Q e T,
  typing E Q e T ->
  forall (fP : qua) (fV : qtyp) (fb : exp), e = exp_abs fP fV fb ->
  exists (L : atoms) (P : qua) (V : qtyp) (T1 : qtyp),
    (forall x : atom, x `notin` L -> typing (x ~ bind_typ V ++ E) P (open_ee fb x) T1) /\
    qualR E qua_bot Q /\
    qsubR E (qtyp_qtyp P (typ_arrow V T1)) T.
Proof.
  intros E Q e T Hty. dependent induction Hty; intros fP fV fb Heq; try discriminate Heq.
  - (* typing_abs *) inversion Heq; subst.
    exists L, fP, fV, T1. split; [|split].
    + assumption.
    + apply qualR_refl.
    + apply qsubR_refl.
  - (* typing_sub *) inversion Heq; subst.
    destruct (IHHty fP fV fb eq_refl) as [L [P [V [T1 [Hbody [Hqual Hq]]]]]].
    exists L, P, V, T1. split; [|split].
    + assumption.
    + assumption.
    + apply qsubR_step with (T := S); assumption.
  - (* typing_subqual *) inversion Heq; subst.
    destruct (IHHty fP fV fb eq_refl) as [L [P [V [T1 [Hbody [Hqual Hq]]]]]].
    exists L, P, V, T1. split; [|split].
    + assumption.
    + apply qualR_step with (R := Q); assumption.
    + assumption.
Qed.

Lemma typing_tabs_inv : forall E Q e T,
  typing E Q e T ->
  forall (fP : qua) (fV : typ) (fb : exp), e = exp_tabs fP fV fb ->
  exists (L : atoms) (P : qua) (V : typ) (T1 : qtyp),
    (forall X : atom, X `notin` L -> typing (X ~ bind_sub V ++ E) P (open_te fb X) (open_tqt T1 X)) /\
    qualR E qua_bot Q /\
    qsubR E (qtyp_qtyp P (typ_all V T1)) T.
Proof.
  intros E Q e T Hty. dependent induction Hty; intros fP fV fb Heq; try discriminate Heq.
  - (* typing_tabs *) inversion Heq; subst.
    exists L, fP, fV, T1. split; [|split].
    + assumption.
    + apply qualR_refl.
    + apply qsubR_refl.
  - (* typing_sub *) inversion Heq; subst.
    destruct (IHHty fP fV fb eq_refl) as [L [P [V [T1 [Hbody [Hqual Hq]]]]]].
    exists L, P, V, T1. split; [|split].
    + assumption.
    + assumption.
    + apply qsubR_step with (T := S); assumption.
  - (* typing_subqual *) inversion Heq; subst.
    destruct (IHHty fP fV fb eq_refl) as [L [P [V [T1 [Hbody [Hqual Hq]]]]]].
    exists L, P, V, T1. split; [|split].
    + assumption.
    + apply qualR_step with (R := Q); assumption.
    + assumption.
Qed.

Lemma typing_qabs_inv : forall E Q e T,
  typing E Q e T ->
  forall (fP : qua) (fQ : qua) (fb : exp), e = exp_qabs fP fQ fb ->
  exists (L : atoms) (P : qua) (Q0 : qua) (T1 : qtyp),
    wf_qua E P /\
    (forall X : atom, X `notin` L -> typing (X ~ bind_qua Q0 ++ E) P (open_qe fb X) (open_qqt T1 X)) /\
    qualR E qua_bot Q /\
    qsubR E (qtyp_qtyp P (typ_qall Q0 T1)) T.
Proof.
  intros E Q e T Hty. dependent induction Hty; intros fP fQ fb Heq; try discriminate Heq.
  - (* typing_qabs *) inversion Heq; subst.
    exists L, fP, fQ, T1. split; [|split; [|split]].
    + assumption.
    + assumption.
    + apply qualR_refl.
    + apply qsubR_refl.
  - (* typing_sub *) inversion Heq; subst.
    destruct (IHHty fP fQ fb eq_refl) as [L [P [Q0 [T1 [Hwf [Hbody [Hqual Hq]]]]]]].
    exists L, P, Q0, T1. split; [|split; [|split]].
    + assumption.
    + assumption.
    + assumption.
    + apply qsubR_step with (T := S); assumption.
  - (* typing_subqual *) inversion Heq; subst.
    destruct (IHHty fP fQ fb eq_refl) as [L [P [Q0 [T1 [Hwf [Hbody [Hqual Hq]]]]]]].
    exists L, P, Q0, T1. split; [|split; [|split]].
    + assumption.
    + assumption.
    + apply qualR_step with (R := Q); assumption.
    + assumption.
Qed.

Lemma typing_tapp_inv : forall E Q e T,
  typing E Q e T ->
  forall (f1 : exp) (fV : typ), e = exp_tapp f1 fV ->
  exists Q0 T1 T2,
    typing E Q0 f1 (qtyp_qtyp Q0 (typ_all T1 T2)) /\
    sub E fV T1 /\
    qualR E Q0 Q /\
    qsubR E (open_tqt T2 fV) T.
Proof.
  intros E Q e T Hty. dependent induction Hty; intros f1 fV Heq; try discriminate Heq.
  - (* typing_tapp *) inversion Heq; subst.
    exists Q, T1, T2. split; [|split; [|split]].
    + assumption.
    + assumption.
    + apply qualR_refl.
    + apply qsubR_refl.
  - (* typing_sub *) inversion Heq; subst.
    destruct (IHHty f1 fV eq_refl) as [Q0 [T1 [T2 [He [Hs [Hq Hqs]]]]]].
    exists Q0, T1, T2. split; [|split; [|split]].
    + assumption.
    + assumption.
    + assumption.
    + apply qsubR_step with (T := S); assumption.
  - (* typing_subqual *) inversion Heq; subst.
    destruct (IHHty f1 fV eq_refl) as [Q0 [T1 [T2 [He [Hs [Hq Hqs]]]]]].
    exists Q0, T1, T2. split; [|split; [|split]].
    + assumption.
    + assumption.
    + apply qualR_step with (R := Q); assumption.
    + assumption.
Qed.

Lemma typing_qapp_inv : forall E Q e T,
  typing E Q e T ->
  forall (f1 : exp) (fQ : qua), e = exp_qapp f1 fQ ->
  exists Q0 Q1 T0,
    typing E Q0 f1 (qtyp_qtyp Q0 (typ_qall Q1 T0)) /\
    subqual E Q0 Q1 /\
    qualR E Q0 Q /\
    qsubR E (open_qqt T0 Q0) T.
Proof.
  intros E Q e T Hty. dependent induction Hty; intros f1 fQ Heq; try discriminate Heq.
  - (* typing_qapp *) inversion Heq; subst.
    exists fQ, Q1, T. split; [|split; [|split]].
    + assumption.
    + assumption.
    + apply qualR_refl.
    + apply qsubR_refl.
  - (* typing_sub *) inversion Heq; subst.
    destruct (IHHty f1 fQ eq_refl) as [Q0 [Q1 [T0 [He [Hs [Hq Hqs]]]]]].
    exists Q0, Q1, T0. split; [|split; [|split]].
    + assumption.
    + assumption.
    + assumption.
    + apply qsubR_step with (T := S); assumption.
  - (* typing_subqual *) inversion Heq; subst.
    destruct (IHHty f1 fQ eq_refl) as [Q0 [Q1 [T0 [He [Hs [Hq Hqs]]]]]].
    exists Q0, Q1, T0. split; [|split; [|split]].
    + assumption.
    + assumption.
    + apply qualR_step with (R := Q); assumption.
    + assumption.
Qed.

Lemma typing_let_inv : forall E Q e T,
  typing E Q e T ->
  forall (f1 f2 : exp), e = exp_let f1 f2 ->
  exists Q0 T1 T2,
    typing E Q0 f1 T1 /\
    (exists L : atoms,
       forall x : atom, x `notin` L ->
         typing (x ~ bind_typ T1 ++ E) Q0 (open_ee f2 x) T2) /\
    qualR E Q0 Q /\
    qsubR E T2 T.
Proof.
  intros E Q e T Hty. dependent induction Hty; intros f1 f2 Heq; try discriminate Heq.
  - (* typing_sub *) inversion Heq; subst.
    destruct (IHHty f1 f2 eq_refl) as [Q0 [T1 [T2 Hrest]]].
    destruct Hrest as [He Hrest].
    destruct Hrest as [[Lb Hbody] Hrest].
    destruct Hrest as [Hq Hqs].
    exists Q0, T1, T2. split; [|split; [|split]].
    + assumption.
    + exists Lb. assumption.
    + assumption.
    + apply qsubR_step with (T := S); assumption.
  - (* typing_subqual *) inversion Heq; subst.
    destruct (IHHty f1 f2 eq_refl) as [Q0 [T1 [T2 Hrest]]].
    destruct Hrest as [He Hrest].
    destruct Hrest as [[Lb Hbody] Hrest].
    destruct Hrest as [Hq Hqs].
    exists Q0, T1, T2. split; [|split; [|split]].
    + assumption.
    + exists Lb. assumption.
    + apply qualR_step with (R := Q); assumption.
    + assumption.
  - (* typing_let *) inversion Heq; subst.
    eexists; eexists; eexists. split; [|split; [|split]].
    + eassumption.
    + eexists; eassumption.
    + apply qualR_refl.
    + apply qsubR_refl.
Qed.


Lemma typing_inl_inv : forall E Q e T,
  typing E Q e T ->
  forall (fP : qua) (f1 : exp), e = exp_inl fP f1 ->
  exists Q0 P T1 T2,
    typing E Q0 f1 T1 /\ wf_qua E P /\ wf_qtyp E T2 /\
    qualR E Q0 Q /\ qsubR E (qtyp_qtyp P (typ_sum T1 T2)) T.
Proof.
  intros E Q e T Hty. dependent induction Hty; intros fP f1 Heq; try discriminate Heq.
  - (* sub *) inversion Heq; subst.
    destruct (IHHty fP f1 eq_refl) as [Q0 [P [T1 [T2 [He [Hw [Hw2 [Hq Hqs]]]]]]]].
    exists Q0, P, T1, T2. split; [|split; [|split; [|split]]].
    + assumption. + assumption. + assumption. + assumption.
    + apply qsubR_step with (T := S); assumption.
  - (* subqual *) inversion Heq; subst.
    destruct (IHHty fP f1 eq_refl) as [Q0 [P [T1 [T2 [He [Hw [Hw2 [Hq Hqs]]]]]]]].
    exists Q0, P, T1, T2. split; [|split; [|split; [|split]]].
    + assumption. + assumption. + assumption.
    + apply qualR_step with (R := Q); assumption.
    + assumption.
  - (* inl *) inversion Heq; subst.
    eexists; eexists; eexists; eexists. split; [|split; [|split; [|split]]].
    + eassumption. + eassumption. + eassumption.
    + apply qualR_refl. + apply qsubR_refl.
Qed.

Lemma typing_inr_inv : forall E Q e T,
  typing E Q e T ->
  forall (fP : qua) (f1 : exp), e = exp_inr fP f1 ->
  exists Q0 P T1 T2,
    typing E Q0 f1 T2 /\ wf_qua E P /\ wf_qtyp E T1 /\
    qualR E Q0 Q /\ qsubR E (qtyp_qtyp P (typ_sum T1 T2)) T.
Proof.
  intros E Q e T Hty. dependent induction Hty; intros fP f1 Heq; try discriminate Heq.
  - (* sub *) inversion Heq; subst.
    destruct (IHHty fP f1 eq_refl) as [Q0 [P [T1 [T2 [He [Hw [Hw2 [Hq Hqs]]]]]]]].
    exists Q0, P, T1, T2. split; [|split; [|split; [|split]]].
    + assumption. + assumption. + assumption. + assumption.
    + apply qsubR_step with (T := S); assumption.
  - (* subqual *) inversion Heq; subst.
    destruct (IHHty fP f1 eq_refl) as [Q0 [P [T1 [T2 [He [Hw [Hw2 [Hq Hqs]]]]]]]].
    exists Q0, P, T1, T2. split; [|split; [|split; [|split]]].
    + assumption. + assumption. + assumption.
    + apply qualR_step with (R := Q); assumption.
    + assumption.
  - (* inr *) inversion Heq; subst.
    eexists; eexists; eexists; eexists. split; [|split; [|split; [|split]]].
    + eassumption. + eassumption. + eassumption.
    + apply qualR_refl. + apply qsubR_refl.
Qed.

Lemma typing_case_inv : forall E Q e T,
  typing E Q e T ->
  forall (f1 f2 f3 : exp), e = exp_case f1 f2 f3 ->
  exists Q0 P T1 T2 Tbody,
    typing E Q0 f1 (qtyp_qtyp P (typ_sum T1 T2)) /\
    (exists L : atoms, forall x : atom, x `notin` L ->
       typing (x ~ bind_typ T1 ++ E) Q0 (open_ee f2 x) Tbody) /\
    (exists L : atoms, forall x : atom, x `notin` L ->
       typing (x ~ bind_typ T2 ++ E) Q0 (open_ee f3 x) Tbody) /\
    qualR E Q0 Q /\ qsubR E Tbody T.
Proof.
  intros E Q e T Hty. dependent induction Hty; intros f1 f2 f3 Heq; try discriminate Heq.
  - (* sub *) inversion Heq; subst.
    destruct (IHHty f1 f2 f3 eq_refl) as [Q0 [P [T1 [T2 [Tb Hrest]]]]].
    destruct Hrest as [He Hrest]; destruct Hrest as [[L2 Hb2] Hrest].
    destruct Hrest as [[L3 Hb3] Hrest]; destruct Hrest as [Hq Hqs].
    exists Q0, P, T1, T2, Tb. split; [|split; [|split; [|split]]].
    + assumption. + exists L2; assumption. + exists L3; assumption. + assumption.
    + apply qsubR_step with (T := S); assumption.
  - (* subqual *) inversion Heq; subst.
    destruct (IHHty f1 f2 f3 eq_refl) as [Q0 [P [T1 [T2 [Tb Hrest]]]]].
    destruct Hrest as [He Hrest]; destruct Hrest as [[L2 Hb2] Hrest].
    destruct Hrest as [[L3 Hb3] Hrest]; destruct Hrest as [Hq Hqs].
    exists Q0, P, T1, T2, Tb. split; [|split; [|split; [|split]]].
    + assumption. + exists L2; assumption. + exists L3; assumption.
    + apply qualR_step with (R := Q); assumption.
    + assumption.
  - (* case *) inversion Heq; subst.
    eexists; eexists; eexists; eexists; eexists. split; [|split; [|split; [|split]]].
    + eassumption.
    + eexists; eassumption.
    + eexists; eassumption.
    + apply qualR_refl. + apply qsubR_refl.
Qed.

Lemma typing_pair_inv : forall E Q e T,
  typing E Q e T ->
  forall (fP : qua) (f1 f2 : exp), e = exp_pair fP f1 f2 ->
  exists Q0 P T1 T2,
    typing E Q0 f1 T1 /\ typing E Q0 f2 T2 /\ wf_qua E P /\
    qualR E Q0 Q /\ qsubR E (qtyp_qtyp P (typ_pair T1 T2)) T.
Proof.
  intros E Q e T Hty. dependent induction Hty; intros fP f1 f2 Heq; try discriminate Heq.
  - (* sub *) inversion Heq; subst.
    destruct (IHHty fP f1 f2 eq_refl) as [Q0 [P [T1 [T2 [H1 [H2 [Hw [Hq Hqs]]]]]]]].
    exists Q0, P, T1, T2. split; [|split; [|split; [|split]]].
    + assumption. + assumption. + assumption. + assumption.
    + apply qsubR_step with (T := S); assumption.
  - (* subqual *) inversion Heq; subst.
    destruct (IHHty fP f1 f2 eq_refl) as [Q0 [P [T1 [T2 [H1 [H2 [Hw [Hq Hqs]]]]]]]].
    exists Q0, P, T1, T2. split; [|split; [|split; [|split]]].
    + assumption. + assumption. + assumption.
    + apply qualR_step with (R := Q); assumption.
    + assumption.
  - (* pair *) inversion Heq; subst.
    eexists; eexists; eexists; eexists. split; [|split; [|split; [|split]]].
    + eassumption. + eassumption. + eassumption.
    + apply qualR_refl. + apply qsubR_refl.
Qed.

Lemma typing_first_inv : forall E Q e T,
  typing E Q e T ->
  forall (f1 : exp), e = exp_first f1 ->
  exists Q0 P T1 T2,
    typing E Q0 f1 (qtyp_qtyp P (typ_pair T1 T2)) /\
    qualR E Q0 Q /\ qsubR E T1 T.
Proof.
  intros E Q e T Hty. dependent induction Hty; intros f1 Heq; try discriminate Heq.
  - (* sub *) inversion Heq; subst.
    destruct (IHHty f1 eq_refl) as [Q0 [P [T1 [T2 [He [Hq Hqs]]]]]].
    exists Q0, P, T1, T2. split; [|split].
    + assumption. + assumption.
    + apply qsubR_step with (T := S); assumption.
  - (* subqual *) inversion Heq; subst.
    destruct (IHHty f1 eq_refl) as [Q0 [P [T1 [T2 [He [Hq Hqs]]]]]].
    exists Q0, P, T1, T2. split; [|split].
    + assumption.
    + apply qualR_step with (R := Q); assumption.
    + assumption.
  - (* first *) inversion Heq; subst.
    eexists; eexists; eexists; eexists. split; [|split].
    + eassumption. + apply qualR_refl. + apply qsubR_refl.
Qed.

Lemma typing_second_inv : forall E Q e T,
  typing E Q e T ->
  forall (f1 : exp), e = exp_second f1 ->
  exists Q0 P T1 T2,
    typing E Q0 f1 (qtyp_qtyp P (typ_pair T1 T2)) /\
    qualR E Q0 Q /\ qsubR E T2 T.
Proof.
  intros E Q e T Hty. dependent induction Hty; intros f1 Heq; try discriminate Heq.
  - (* sub *) inversion Heq; subst.
    destruct (IHHty f1 eq_refl) as [Q0 [P [T1 [T2 [He [Hq Hqs]]]]]].
    exists Q0, P, T1, T2. split; [|split].
    + assumption. + assumption.
    + apply qsubR_step with (T := S); assumption.
  - (* subqual *) inversion Heq; subst.
    destruct (IHHty f1 eq_refl) as [Q0 [P [T1 [T2 [He [Hq Hqs]]]]]].
    exists Q0, P, T1, T2. split; [|split].
    + assumption.
    + apply qualR_step with (R := Q); assumption.
    + assumption.
  - (* second *) inversion Heq; subst.
    eexists; eexists; eexists; eexists. split; [|split].
    + eassumption. + apply qualR_refl. + apply qsubR_refl.
Qed.

Lemma typing_upqual_inv : forall E Q e T,
  typing E Q e T ->
  forall (fP : qua) (f1 : exp), e = exp_upqual fP f1 ->
  exists Qe Qtyp P T0,
    typing E Qe f1 (qtyp_qtyp Qtyp T0) /\
    subqual E Qtyp P /\
    qualR E Qe Q /\
    qsubR E (qtyp_qtyp P T0) T.
Proof.
  intros E Q e T Hty. dependent induction Hty; intros fP f1 Heq; try discriminate Heq.
  - (* sub *) inversion Heq; subst.
    destruct (IHHty fP f1 eq_refl) as [Qe [Qt [P [T0 [He [Hs [Hq Hqs]]]]]]].
    exists Qe, Qt, P, T0. split; [|split; [|split]].
    + assumption. + assumption. + assumption.
    + apply qsubR_step with (T := S); assumption.
  - (* subqual *) inversion Heq; subst.
    destruct (IHHty fP f1 eq_refl) as [Qe [Qt [P [T0 [He [Hs [Hq Hqs]]]]]]].
    exists Qe, Qt, P, T0. split; [|split; [|split]].
    + assumption. + assumption.
    + apply qualR_step with (R := Q); assumption.
    + assumption.
  - (* upqual *) inversion Heq; subst.
    eexists; eexists; eexists; eexists. split; [|split; [|split]].
    + eassumption. + eassumption. + apply qualR_refl. + apply qsubR_refl.
Qed.

Lemma typing_check_inv : forall E Q e T,
  typing E Q e T ->
  forall (fP : qua) (f1 : exp), e = exp_check fP f1 ->
  exists Qe Qtyp P T0,
    typing E Qe f1 (qtyp_qtyp Qtyp T0) /\
    subqual E Qtyp P /\
    qualR E Qe Q /\
    qsubR E (qtyp_qtyp Qtyp T0) T.
Proof.
  intros E Q e T Hty. dependent induction Hty; intros fP f1 Heq; try discriminate Heq.
  - (* sub *) inversion Heq; subst.
    destruct (IHHty fP f1 eq_refl) as [Qe [Qt [P [T0 [He [Hs [Hq Hqs]]]]]]].
    exists Qe, Qt, P, T0. split; [|split; [|split]].
    + assumption. + assumption. + assumption.
    + apply qsubR_step with (T := S); assumption.
  - (* subqual *) inversion Heq; subst.
    destruct (IHHty fP f1 eq_refl) as [Qe [Qt [P [T0 [He [Hs [Hq Hqs]]]]]]].
    exists Qe, Qt, P, T0. split; [|split; [|split]].
    + assumption. + assumption.
    + apply qualR_step with (R := Q); assumption.
    + assumption.
  - (* check *) inversion Heq; subst.
    eexists; eexists; eexists; eexists. split; [|split; [|split]].
    + eassumption. + eassumption. + apply qualR_refl. + apply qsubR_refl.
Qed.


(* ===== inlined from /tmp/w4/InvExprSyn.v ===== *)

Lemma typing_qapp_inv_syn : forall E Q e T R e1,
  typing E Q e T -> e = exp_qapp e1 R ->
  exists Q1 T0,
    typing E R e1 (qtyp_qtyp R (typ_qall Q1 T0)) /\
    subqual E R Q1 /\ qualR E R Q /\ qsubR E (open_qqt T0 R) T.
Proof.
  intros E Q e T R e1 Hty Heq. dependent induction Hty; try discriminate Heq.
  - (* qapp *) inversion Heq; subst.
    exists Q1, T. split; [|split; [|split]].
    + assumption. + assumption. + apply qualR_refl. + apply qsubR_refl.
  - (* sub *) inversion Heq; subst.
    destruct (IHHty eq_refl) as [Q1 [T0 [He [Hs [Hq Hqs]]]]].
    exists Q1, T0. split; [|split; [|split]].
    + assumption. + assumption. + assumption.
    + apply qsubR_step with (T := S); assumption.
  - (* subqual *) inversion Heq; subst.
    destruct (IHHty eq_refl) as [Q1 [T0 [He [Hs [Hq Hqs]]]]].
    exists Q1, T0. split; [|split; [|split]].
    + assumption. + assumption.
    + eapply qualR_step; [exact Hq|eassumption].
    + assumption.
Qed.

Lemma typing_inl_inv_syn : forall E Q P e1 T,
  typing E Q (exp_inl P e1) T ->
  exists Q0 T1 T2,
    typing E Q0 e1 T1 /\ wf_qua E P /\ wf_qtyp E T2 /\
    qualR E Q0 Q /\ qsubR E (qtyp_qtyp P (typ_sum T1 T2)) T.
Proof.
  intros E Q P e1 T Hty. dependent induction Hty.
  - (* sub *) destruct (IHHty P e1 eq_refl) as [Q0 [T1 [T2 [He [Hw [Hw2 [Hq Hqs]]]]]]].
    exists Q0, T1, T2. split; [|split; [|split; [|split]]].
    + assumption. + assumption. + assumption. + assumption.
    + apply qsubR_step with (T := S); assumption.
  - (* subqual *) destruct (IHHty P e1 eq_refl) as [Q0 [T1 [T2 [He [Hw [Hw2 [Hq Hqs]]]]]]].
    exists Q0, T1, T2. split; [|split; [|split; [|split]]].
    + assumption. + assumption. + assumption.
    + eapply qualR_step; [exact Hq|eassumption].
    + assumption.
  - (* inl *) eexists; eexists; eexists. split; [|split; [|split; [|split]]].
    + eassumption. + eassumption. + eassumption.
    + apply qualR_refl. + apply qsubR_refl.
Qed.

Lemma typing_inr_inv_syn : forall E Q P e1 T,
  typing E Q (exp_inr P e1) T ->
  exists Q0 T1 T2,
    typing E Q0 e1 T2 /\ wf_qua E P /\ wf_qtyp E T1 /\
    qualR E Q0 Q /\ qsubR E (qtyp_qtyp P (typ_sum T1 T2)) T.
Proof.
  intros E Q P e1 T Hty. dependent induction Hty.
  - (* sub *) destruct (IHHty P e1 eq_refl) as [Q0 [T1 [T2 [He [Hw [Hw2 [Hq Hqs]]]]]]].
    exists Q0, T1, T2. split; [|split; [|split; [|split]]].
    + assumption. + assumption. + assumption. + assumption.
    + apply qsubR_step with (T := S); assumption.
  - (* subqual *) destruct (IHHty P e1 eq_refl) as [Q0 [T1 [T2 [He [Hw [Hw2 [Hq Hqs]]]]]]].
    exists Q0, T1, T2. split; [|split; [|split; [|split]]].
    + assumption. + assumption. + assumption.
    + eapply qualR_step; [exact Hq|eassumption].
    + assumption.
  - (* inr *) eexists; eexists; eexists. split; [|split; [|split; [|split]]].
    + eassumption. + eassumption. + eassumption.
    + apply qualR_refl. + apply qsubR_refl.
Qed.

Lemma typing_pair_inv_syn : forall E Q P e1 e2 T,
  typing E Q (exp_pair P e1 e2) T ->
  exists Q0 T1 T2,
    typing E Q0 e1 T1 /\ typing E Q0 e2 T2 /\ wf_qua E P /\
    qualR E Q0 Q /\ qsubR E (qtyp_qtyp P (typ_pair T1 T2)) T.
Proof.
  intros E Q P e1 e2 T Hty. dependent induction Hty.
  - (* sub *) destruct (IHHty P e1 e2 eq_refl) as [Q0 [T1 [T2 [H1 [H2 [Hw [Hq Hqs]]]]]]].
    exists Q0, T1, T2. split; [|split; [|split; [|split]]].
    + assumption. + assumption. + assumption. + assumption.
    + apply qsubR_step with (T := S); assumption.
  - (* subqual *) destruct (IHHty P e1 e2 eq_refl) as [Q0 [T1 [T2 [H1 [H2 [Hw [Hq Hqs]]]]]]].
    exists Q0, T1, T2. split; [|split; [|split; [|split]]].
    + assumption. + assumption. + assumption.
    + eapply qualR_step; [exact Hq|eassumption].
    + assumption.
  - (* pair *) eexists; eexists; eexists. split; [|split; [|split; [|split]]].
    + eassumption. + eassumption. + eassumption.
    + apply qualR_refl. + apply qsubR_refl.
Qed.

Lemma typing_abs_inv_syn : forall E Q P V b T,
  typing E Q (exp_abs P V b) T ->
  exists L T1,
    (forall x, x `notin` L -> typing (x ~ bind_typ V ++ E) P (open_ee b x) T1) /\
    qualR E qua_bot Q /\ qsubR E (qtyp_qtyp P (typ_arrow V T1)) T.
Proof.
  intros E Q P V b T Hty. dependent induction Hty.
  - (* abs *) exists L, T1. split; [|split].
    + assumption.
    + apply qualR_refl.
    + apply qsubR_refl.
  - (* sub *) destruct (IHHty P V b eq_refl) as [L [T1 [Hbody [Hq Hqs]]]].
    exists L, T1. split; [|split].
    + assumption.
    + assumption.
    + apply qsubR_step with (T := S); assumption.
  - (* subqual *) destruct (IHHty P V b eq_refl) as [L [T1 [Hbody [Hq Hqs]]]].
    exists L, T1. split; [|split].
    + assumption.
    + eapply qualR_step; [exact Hq|eassumption].
    + assumption.
Qed.

Lemma typing_tabs_inv_syn : forall E Q P V b T,
  typing E Q (exp_tabs P V b) T ->
  exists L T1,
    (forall X, X `notin` L -> typing (X ~ bind_sub V ++ E) P (open_te b X) (open_tqt T1 X)) /\
    qualR E qua_bot Q /\ qsubR E (qtyp_qtyp P (typ_all V T1)) T.
Proof.
  intros E Q P V b T Hty. dependent induction Hty.
  - (* tabs *) exists L, T1. split; [|split].
    + assumption.
    + apply qualR_refl.
    + apply qsubR_refl.
  - (* sub *) destruct (IHHty P V b eq_refl) as [L [T1 [Hbody [Hq Hqs]]]].
    exists L, T1. split; [|split].
    + assumption.
    + assumption.
    + apply qsubR_step with (T := S); assumption.
  - (* subqual *) destruct (IHHty P V b eq_refl) as [L [T1 [Hbody [Hq Hqs]]]].
    exists L, T1. split; [|split].
    + assumption.
    + eapply qualR_step; [exact Hq|eassumption].
    + assumption.
Qed.

Lemma typing_qabs_inv_syn : forall E Q P R b T,
  typing E Q (exp_qabs P R b) T ->
  exists L T1,
    wf_qua E P /\
    (forall X, X `notin` L -> typing (X ~ bind_qua R ++ E) P (open_qe b X) (open_qqt T1 X)) /\
    qualR E qua_bot Q /\ qsubR E (qtyp_qtyp P (typ_qall R T1)) T.
Proof.
  intros E Q P R b T Hty. dependent induction Hty.
  - (* qabs *) exists L, T1. split; [|split; [|split]].
    + assumption.
    + assumption.
    + apply qualR_refl.
    + apply qsubR_refl.
  - (* sub *) destruct (IHHty P R b eq_refl) as [L [T1 [Hw [Hbody [Hq Hqs]]]]].
    exists L, T1. split; [|split; [|split]].
    + assumption. + assumption. + assumption.
    + apply qsubR_step with (T := S); assumption.
  - (* subqual *) destruct (IHHty P R b eq_refl) as [L [T1 [Hw [Hbody [Hq Hqs]]]]].
    exists L, T1. split; [|split; [|split]].
    + assumption. + assumption.
    + eapply qualR_step; [exact Hq|eassumption].
    + assumption.
Qed.

Lemma typing_upqual_inv_syn : forall E Q P e1 T,
  typing E Q (exp_upqual P e1) T ->
  exists Qe Qtyp T0,
    typing E Qe e1 (qtyp_qtyp Qtyp T0) /\ subqual E Qtyp P /\
    qualR E Qe Q /\ qsubR E (qtyp_qtyp P T0) T.
Proof.
  intros E Q P e1 T Hty. dependent induction Hty.
  - (* sub *) destruct (IHHty P e1 eq_refl) as [Qe [Qt [T0 [He [Hs [Hq Hqs]]]]]].
    exists Qe, Qt, T0. split; [|split; [|split]].
    + assumption. + assumption. + assumption.
    + apply qsubR_step with (T := S); assumption.
  - (* subqual *) destruct (IHHty P e1 eq_refl) as [Qe [Qt [T0 [He [Hs [Hq Hqs]]]]]].
    exists Qe, Qt, T0. split; [|split; [|split]].
    + assumption. + assumption.
    + eapply qualR_step; [exact Hq|eassumption].
    + assumption.
  - (* upqual *) eexists; eexists; eexists. split; [|split; [|split]].
    + eassumption. + eassumption. + apply qualR_refl. + apply qsubR_refl.
Qed.

Lemma typing_check_inv_syn : forall E Q P e1 T,
  typing E Q (exp_check P e1) T ->
  exists Qe Qtyp T0,
    typing E Qe e1 (qtyp_qtyp Qtyp T0) /\ subqual E Qtyp P /\
    qualR E Qe Q /\ qsubR E (qtyp_qtyp Qtyp T0) T.
Proof.
  intros E Q P e1 T Hty. dependent induction Hty.
  - (* sub *) destruct (IHHty P e1 eq_refl) as [Qe [Qt [T0 [He [Hs [Hq Hqs]]]]]].
    exists Qe, Qt, T0. split; [|split; [|split]].
    + assumption. + assumption. + assumption.
    + apply qsubR_step with (T := S); assumption.
  - (* subqual *) destruct (IHHty P e1 eq_refl) as [Qe [Qt [T0 [He [Hs [Hq Hqs]]]]]].
    exists Qe, Qt, T0. split; [|split; [|split]].
    + assumption. + assumption.
    + eapply qualR_step; [exact Hq|eassumption].
    + assumption.
  - (* check *) eexists; eexists; eexists. split; [|split; [|split]].
    + eassumption. + eassumption. + apply qualR_refl. + apply qsubR_refl.
Qed.


(* ===== inlined from /tmp/w5/InvCtxAll.v ===== *)

Lemma typing_ctx_app_inv : forall E Q c T,
  typing_ctx E Q c T ->
  forall f k, c = frame_app f :: k ->
  exists Q0 T1 T2,
    typing_ctx E Q0 k T2 /\
    value f /\
    typing E Q0 f (qtyp_qtyp Q0 (typ_arrow T1 T2)) /\
    qualL E Q Q0 /\
    qsubL E T T1.
Proof.
  intros E Q c T Hty. dependent induction Hty; intros f k Heq; try discriminate Heq.
  - inversion Heq; subst. repeat eexists; repeat match goal with |- _ /\ _ => split end; eauto 10; try apply qualL_refl; try apply qsubL_refl.
  - inversion Heq; subst.
    destruct (IHHty f k eq_refl) as [Q0 [T1 [T2 [Hk [Hv [Hf [Hq Hs]]]]]]].
    exists Q0, T1, T2. repeat match goal with |- _ /\ _ => split end; eauto.
    eapply qsubL_step; [eassumption|exact Hs].
  - inversion Heq; subst.
    destruct (IHHty f k eq_refl) as [Q0 [T1 [T2 [Hk [Hv [Hf [Hq Hs]]]]]]].
    exists Q0, T1, T2. repeat match goal with |- _ /\ _ => split end; eauto.
    eapply qualL_step; [eassumption|exact Hq].
Qed.

Lemma typing_ctx_tabs_inv : forall E Q c T,
  typing_ctx E Q c T ->
  forall V k, c = frame_tabs V :: k ->
  exists Q0 T1 T1' T2 L,
    typing_ctx E Q0 k (open_tqt T2 T1') /\
    sub E T1' T1 /\
    (forall X : atom, X `notin` L -> wf_qtyp (X ~ bind_sub T1 ++ E) (open_tqt T2 X)) /\
    qualL E Q Q0 /\
    qsubL E T (qtyp_qtyp Q0 (typ_all T1 T2)).
Proof.
  intros E Q c T Hty. dependent induction Hty; intros V k Heq; try discriminate Heq.
  - inversion Heq; subst. repeat eexists; repeat match goal with |- _ /\ _ => split end; eauto 10; try apply qualL_refl; try apply qsubL_refl.
  - inversion Heq; subst.
    destruct (IHHty V k eq_refl) as [Q0 [T1 [T1' [T2 [L [Hk [Hs [Hwf [Hq Hs2]]]]]]]]].
    exists Q0, T1, T1', T2, L. repeat match goal with |- _ /\ _ => split end; eauto.
    eapply qsubL_step; [eassumption|exact Hs2].
  - inversion Heq; subst.
    destruct (IHHty V k eq_refl) as [Q0 [T1 [T1' [T2 [L [Hk [Hs [Hwf [Hq Hs2]]]]]]]]].
    exists Q0, T1, T1', T2, L. repeat match goal with |- _ /\ _ => split end; eauto.
    eapply qualL_step; [eassumption|exact Hq].
Qed.

Lemma typing_ctx_qabs_inv : forall E Q c T,
  typing_ctx E Q c T ->
  forall Rarg k, c = frame_qabs Rarg :: k ->
  exists Q0 R0 Rinv T2 L,
    typing_ctx E Q0 k (open_qqt T2 Rinv) /\
    subqual E Rinv R0 /\
    (forall X : atom, X `notin` L -> wf_qtyp (X ~ bind_qua R0 ++ E) (open_qqt T2 X)) /\
    qualL E Q Q0 /\
    qsubL E T (qtyp_qtyp Q0 (typ_qall R0 T2)).
Proof.
  intros E Q c T Hty. dependent induction Hty; intros Rarg k Heq; try discriminate Heq.
  - inversion Heq; subst.
    repeat eexists; repeat match goal with |- _ /\ _ => split end; eauto 10; try apply qualL_refl; try apply qsubL_refl.
  - inversion Heq; subst.
    destruct (IHHty Rarg k eq_refl) as (Q0 & R0 & Rinv & T2 & L & Hk & Hs & Hwf & Hq & Hs2).
    exists Q0, R0, Rinv, T2, L. repeat match goal with |- _ /\ _ => split end; eauto.
    eapply qsubL_step; [eassumption|exact Hs2].
  - inversion Heq; subst.
    destruct (IHHty Rarg k eq_refl) as (Q0 & R0 & Rinv & T2 & L & Hk & Hs & Hwf & Hq & Hs2).
    exists Q0, R0, Rinv, T2, L. repeat match goal with |- _ /\ _ => split end; eauto.
    eapply qualL_step; [eassumption|exact Hq].
Qed.

Lemma typing_ctx_let_inv : forall E Q c T,
  typing_ctx E Q c T ->
  forall earg k, c = frame_let earg :: k ->
  exists Q0 T1 T2 L,
    typing_ctx E Q0 k T2 /\
    (forall x : atom, x `notin` L -> typing (x ~ bind_typ T1 ++ E) Q0 (open_ee earg x) T2) /\
    qualL E Q Q0 /\
    qsubL E T T1.
Proof.
  intros E Q c T Hty. dependent induction Hty; intros earg k Heq; try discriminate Heq.
  - inversion Heq; subst. repeat eexists; repeat match goal with |- _ /\ _ => split end; eauto 10; try apply qualL_refl; try apply qsubL_refl.
  - inversion Heq; subst.
    destruct (IHHty earg k eq_refl) as [Q0 [T1 [T2 [L [Hk [Hb [Hq Hs]]]]]]].
    exists Q0, T1, T2, L. repeat match goal with |- _ /\ _ => split end; eauto.
    eapply qsubL_step; [eassumption|exact Hs].
  - inversion Heq; subst.
    destruct (IHHty earg k eq_refl) as [Q0 [T1 [T2 [L [Hk [Hb [Hq Hs]]]]]]].
    exists Q0, T1, T2, L. repeat match goal with |- _ /\ _ => split end; eauto.
    eapply qualL_step; [eassumption|exact Hq].
Qed.

Lemma typing_ctx_inl_inv : forall E Q c T,
  typing_ctx E Q c T ->
  forall Parg k, c = frame_inl Parg :: k ->
  exists Q0 P0 T1 T2,
    typing_ctx E Q0 k (qtyp_qtyp P0 (typ_sum T1 T2)) /\
    qualL E Q Q0 /\
    qsubL E T T1.
Proof.
  intros E Q c T Hty. dependent induction Hty; intros Parg k Heq; try discriminate Heq.
  - inversion Heq; subst. repeat eexists; repeat match goal with |- _ /\ _ => split end; eauto 10; try apply qualL_refl; try apply qsubL_refl.
  - inversion Heq; subst.
    destruct (IHHty Parg k eq_refl) as [Q0 [P0 [T1 [T2 [Hk [Hq Hs]]]]]].
    exists Q0, P0, T1, T2. repeat match goal with |- _ /\ _ => split end; eauto.
    eapply qsubL_step; [eassumption|exact Hs].
  - inversion Heq; subst.
    destruct (IHHty Parg k eq_refl) as [Q0 [P0 [T1 [T2 [Hk [Hq Hs]]]]]].
    exists Q0, P0, T1, T2. repeat match goal with |- _ /\ _ => split end; eauto.
    eapply qualL_step; [eassumption|exact Hq].
Qed.

Lemma typing_ctx_inr_inv : forall E Q c T,
  typing_ctx E Q c T ->
  forall Parg k, c = frame_inr Parg :: k ->
  exists Q0 P0 T1 T2,
    typing_ctx E Q0 k (qtyp_qtyp P0 (typ_sum T1 T2)) /\
    qualL E Q Q0 /\
    qsubL E T T2.
Proof.
  intros E Q c T Hty. dependent induction Hty; intros Parg k Heq; try discriminate Heq.
  - inversion Heq; subst. repeat eexists; repeat match goal with |- _ /\ _ => split end; eauto 10; try apply qualL_refl; try apply qsubL_refl.
  - inversion Heq; subst.
    destruct (IHHty Parg k eq_refl) as [Q0 [P0 [T1 [T2 [Hk [Hq Hs]]]]]].
    exists Q0, P0, T1, T2. repeat match goal with |- _ /\ _ => split end; eauto.
    eapply qsubL_step; [eassumption|exact Hs].
  - inversion Heq; subst.
    destruct (IHHty Parg k eq_refl) as [Q0 [P0 [T1 [T2 [Hk [Hq Hs]]]]]].
    exists Q0, P0, T1, T2. repeat match goal with |- _ /\ _ => split end; eauto.
    eapply qualL_step; [eassumption|exact Hq].
Qed.

Lemma typing_ctx_case_inv : forall E Q c T,
  typing_ctx E Q c T ->
  forall earg2 earg3 k, c = frame_case earg2 earg3 :: k ->
  exists Q0 P Tbody T1 T2 L,
    wf_qua E P /\
    typing_ctx E Q0 k Tbody /\
    (forall x : atom, x `notin` L -> typing (x ~ bind_typ T1 ++ E) Q0 (open_ee earg2 x) Tbody) /\
    (forall x : atom, x `notin` L -> typing (x ~ bind_typ T2 ++ E) Q0 (open_ee earg3 x) Tbody) /\
    qualL E Q Q0 /\
    qsubL E T (qtyp_qtyp P (typ_sum T1 T2)).
Proof.
  intros E Q c T Hty. dependent induction Hty; intros earg2 earg3 k Heq; try discriminate Heq.
  - inversion Heq; subst. repeat eexists; repeat match goal with |- _ /\ _ => split end; eauto 10; try apply qualL_refl; try apply qsubL_refl.
  - inversion Heq; subst.
    destruct (IHHty earg2 earg3 k eq_refl) as [Q0 [P [Tbody [T1 [T2 [L [Hwf [Hk [Hb2 [Hb3 [Hq Hs]]]]]]]]]]].
    exists Q0, P, Tbody, T1, T2, L. repeat match goal with |- _ /\ _ => split end; eauto.
    eapply qsubL_step; [eassumption|exact Hs].
  - inversion Heq; subst.
    destruct (IHHty earg2 earg3 k eq_refl) as [Q0 [P [Tbody [T1 [T2 [L [Hwf [Hk [Hb2 [Hb3 [Hq Hs]]]]]]]]]]].
    exists Q0, P, Tbody, T1, T2, L. repeat match goal with |- _ /\ _ => split end; eauto.
    eapply qualL_step; [eassumption|exact Hq].
Qed.

Lemma typing_ctx_pair_1_inv : forall E Q c T,
  typing_ctx E Q c T ->
  forall Parg earg k, c = frame_pair_1 Parg earg :: k ->
  exists Q0 P0 T1 T2,
    wf_qua E P0 /\
    typing_ctx E Q0 k (qtyp_qtyp P0 (typ_pair T1 T2)) /\
    typing E Q0 earg T2 /\
    qualL E Q Q0 /\
    qsubL E T T1.
Proof.
  intros E Q c T Hty. dependent induction Hty; intros Parg earg k Heq; try discriminate Heq.
  - inversion Heq; subst. repeat eexists; repeat match goal with |- _ /\ _ => split end; eauto 10; try apply qualL_refl; try apply qsubL_refl.
  - inversion Heq; subst.
    destruct (IHHty Parg earg k eq_refl) as [Q0 [P0 [T1 [T2 [Hwf [Hk [He [Hq Hs]]]]]]]].
    exists Q0, P0, T1, T2. repeat match goal with |- _ /\ _ => split end; eauto.
    eapply qsubL_step; [eassumption|exact Hs].
  - inversion Heq; subst.
    destruct (IHHty Parg earg k eq_refl) as [Q0 [P0 [T1 [T2 [Hwf [Hk [He [Hq Hs]]]]]]]].
    exists Q0, P0, T1, T2. repeat match goal with |- _ /\ _ => split end; eauto.
    eapply qualL_step; [eassumption|exact Hq].
Qed.

Lemma typing_ctx_pair_2_inv : forall E Q c T,
  typing_ctx E Q c T ->
  forall Parg varg k, c = frame_pair_2 Parg varg :: k ->
  exists Q0 P0 T1 T2,
    wf_qua E P0 /\
    typing_ctx E Q0 k (qtyp_qtyp P0 (typ_pair T1 T2)) /\
    value varg /\
    typing E Q0 varg T1 /\
    qualL E Q Q0 /\
    qsubL E T T2.
Proof.
  intros E Q c T Hty. dependent induction Hty; intros Parg varg k Heq; try discriminate Heq.
  - inversion Heq; subst. repeat eexists; repeat match goal with |- _ /\ _ => split end; eauto 10; try apply qualL_refl; try apply qsubL_refl.
  - inversion Heq; subst.
    destruct (IHHty Parg varg k eq_refl) as [Q0 [P0 [T1 [T2 [Hwf [Hk [Hv [He [Hq Hs]]]]]]]]].
    exists Q0, P0, T1, T2. repeat match goal with |- _ /\ _ => split end; eauto.
    eapply qsubL_step; [eassumption|exact Hs].
  - inversion Heq; subst.
    destruct (IHHty Parg varg k eq_refl) as [Q0 [P0 [T1 [T2 [Hwf [Hk [Hv [He [Hq Hs]]]]]]]]].
    exists Q0, P0, T1, T2. repeat match goal with |- _ /\ _ => split end; eauto.
    eapply qualL_step; [eassumption|exact Hq].
Qed.

Lemma typing_ctx_first_inv : forall E Q c T,
  typing_ctx E Q c T ->
  forall k, c = frame_first :: k ->
  exists Q0 P T1 T2,
    wf_qua E P /\
    typing_ctx E Q0 k T1 /\
    wf_qtyp E T2 /\
    qualL E Q Q0 /\
    qsubL E T (qtyp_qtyp P (typ_pair T1 T2)).
Proof.
  intros E Q c T Hty. dependent induction Hty; intros k Heq; try discriminate Heq.
  - inversion Heq; subst. exists Q, P, T1, T2. repeat match goal with |- _ /\ _ => split end; eauto 10; try apply qualL_refl; try apply qsubL_refl.
  - inversion Heq; subst.
    destruct (IHHty k eq_refl) as [Q0 [P [T1 [T2 [Hwf [Hk [Hwt [Hq Hs]]]]]]]].
    exists Q0, P, T1, T2. repeat match goal with |- _ /\ _ => split end; eauto.
    eapply qsubL_step; [eassumption|exact Hs].
  - inversion Heq; subst.
    destruct (IHHty k eq_refl) as [Q0 [P [T1 [T2 [Hwf [Hk [Hwt [Hq Hs]]]]]]]].
    exists Q0, P, T1, T2. repeat match goal with |- _ /\ _ => split end; eauto.
    eapply qualL_step; [eassumption|exact Hq].
Qed.

Lemma typing_ctx_second_inv : forall E Q c T,
  typing_ctx E Q c T ->
  forall k, c = frame_second :: k ->
  exists Q0 P T1 T2,
    wf_qua E P /\
    typing_ctx E Q0 k T2 /\
    wf_qtyp E T1 /\
    qualL E Q Q0 /\
    qsubL E T (qtyp_qtyp P (typ_pair T1 T2)).
Proof.
  intros E Q c T Hty. dependent induction Hty; intros k Heq; try discriminate Heq.
  - inversion Heq; subst. exists Q, P, T1, T2. repeat match goal with |- _ /\ _ => split end; eauto 10; try apply qualL_refl; try apply qsubL_refl.
  - inversion Heq; subst.
    destruct (IHHty k eq_refl) as [Q0 [P [T1 [T2 [Hwf [Hk [Hwt [Hq Hs]]]]]]]].
    exists Q0, P, T1, T2. repeat match goal with |- _ /\ _ => split end; eauto.
    eapply qsubL_step; [eassumption|exact Hs].
  - inversion Heq; subst.
    destruct (IHHty k eq_refl) as [Q0 [P [T1 [T2 [Hwf [Hk [Hwt [Hq Hs]]]]]]]].
    exists Q0, P, T1, T2. repeat match goal with |- _ /\ _ => split end; eauto.
    eapply qualL_step; [eassumption|exact Hq].
Qed.

Lemma typing_ctx_barrier_inv : forall E Q c T,
  typing_ctx E Q c T ->
  forall targ k, c = frame_barrier targ :: k ->
  exists Q0 Tbody t0 s,
    typing_ctx E Q0 k Tbody /\
    concretize Q0 = Some s /\
    t0 ≤ s /\
    qualL E Q (abstractize t0) /\
    qsubL E T Tbody.
Proof.
  intros E Q c T Hty. dependent induction Hty; intros targ k Heq; try discriminate Heq.
  - (* typing_ctx_barrier *) inversion Heq; subst.
    repeat eexists; repeat match goal with |- _ /\ _ => split end; eauto 10; try apply qualL_refl; try apply qsubL_refl.
  - inversion Heq; subst.
    destruct (IHHty targ k eq_refl) as [Q0 [Tbody [t0 [s [Hk [Hc [Hle [Hq Hs]]]]]]]].
    exists Q0, Tbody, t0, s. repeat match goal with |- _ /\ _ => split end; eauto.
    eapply qsubL_step; [eassumption|exact Hs].
  - inversion Heq; subst.
    destruct (IHHty targ k eq_refl) as [Q0 [Tbody [t0 [s [Hk [Hc [Hle [Hq Hs]]]]]]]].
    exists Q0, Tbody, t0, s. repeat match goal with |- _ /\ _ => split end; eauto.
    eapply qualL_step; [eassumption|exact Hq].
Qed.

Lemma typing_ctx_upqual_inv : forall E Q c T,
  typing_ctx E Q c T ->
  forall Parg k, c = frame_upqual Parg :: k ->
  exists Q0 P0 T0,
    typing_ctx E Q0 k (qtyp_qtyp P0 T0) /\
    qualL E Q Q0 /\
    qsubL E T (qtyp_qtyp P0 T0).
Proof.
  intros E Q c T Hty. dependent induction Hty; intros Parg k Heq; try discriminate Heq.
  - inversion Heq; subst. repeat eexists; repeat match goal with |- _ /\ _ => split end; eauto 10; try apply qualL_refl; try apply qsubL_refl.
  - inversion Heq; subst.
    destruct (IHHty Parg k eq_refl) as [Q0 [P0 [T0 [Hk [Hq Hs]]]]].
    exists Q0, P0, T0. repeat match goal with |- _ /\ _ => split end; eauto.
    eapply qsubL_step; [eassumption|exact Hs].
  - inversion Heq; subst.
    destruct (IHHty Parg k eq_refl) as [Q0 [P0 [T0 [Hk [Hq Hs]]]]].
    exists Q0, P0, T0. repeat match goal with |- _ /\ _ => split end; eauto.
    eapply qualL_step; [eassumption|exact Hq].
Qed.

Lemma typing_ctx_check_inv : forall E Q c T,
  typing_ctx E Q c T ->
  forall Rarg k, c = frame_check Rarg :: k ->
  exists Q0 R0 P T0,
    wf_qua E R0 /\
    typing_ctx E Q0 k (qtyp_qtyp P T0) /\
    qualL E Q Q0 /\
    qsubL E T (qtyp_qtyp (qua_meet P R0) T0).
Proof.
  intros E Q c T Hty. dependent induction Hty; intros Rarg k Heq; try discriminate Heq.
  - inversion Heq; subst. repeat eexists; repeat match goal with |- _ /\ _ => split end; eauto 10; try apply qualL_refl; try apply qsubL_refl.
  - inversion Heq; subst.
    destruct (IHHty Rarg k eq_refl) as [Q0 [R0 [P [T0 [Hwf [Hk [Hq Hs]]]]]]].
    exists Q0, R0, P, T0. repeat match goal with |- _ /\ _ => split end; eauto.
    eapply qsubL_step; [eassumption|exact Hs].
  - inversion Heq; subst.
    destruct (IHHty Rarg k eq_refl) as [Q0 [R0 [P [T0 [Hwf [Hk [Hq Hs]]]]]]].
    exists Q0, R0, P, T0. repeat match goal with |- _ /\ _ => split end; eauto.
    eapply qualL_step; [eassumption|exact Hq].
Qed.


(* ===== inlined from /tmp/w5/InvCtxSyn.v ===== *)

Lemma typing_ctx_app_inv_syn : forall E Q f k T,
  typing_ctx E Q (frame_app f :: k) T ->
  exists Q0 T1 T2,
    typing_ctx E Q0 k T2 /\ value f /\
    typing E Q0 f (qtyp_qtyp Q0 (typ_arrow T1 T2)) /\
    qualL E Q Q0 /\ qsubL E T T1.
Proof.
  intros E Q f k T Hty. dependent induction Hty.
  - repeat eexists; repeat match goal with |- _ /\ _ => split end; eauto 10; try apply qualL_refl; try apply qsubL_refl.
  - destruct (IHHty f k eq_refl) as [Q0 [T1 [T2 [Hk [Hv [Hf [Hq Hs]]]]]]].
    exists Q0, T1, T2. repeat match goal with |- _ /\ _ => split end; eauto.
    eapply qsubL_step; [eassumption|exact Hs].
  - destruct (IHHty f k eq_refl) as [Q0 [T1 [T2 [Hk [Hv [Hf [Hq Hs]]]]]]].
    exists Q0, T1, T2. repeat match goal with |- _ /\ _ => split end; eauto.
    eapply qualL_step; [eassumption|exact Hq].
Qed.

Lemma typing_ctx_tabs_inv_syn : forall E Q V k T,
  typing_ctx E Q (frame_tabs V :: k) T ->
  exists Q0 T1 T2 L,
    typing_ctx E Q0 k (open_tqt T2 V) /\ sub E V T1 /\
    (forall X : atom, X `notin` L -> wf_qtyp (X ~ bind_sub T1 ++ E) (open_tqt T2 X)) /\
    qualL E Q Q0 /\ qsubL E T (qtyp_qtyp Q0 (typ_all T1 T2)).
Proof.
  intros E Q V k T Hty. dependent induction Hty.
  - repeat eexists; repeat match goal with |- _ /\ _ => split end; eauto 10; try apply qualL_refl; try apply qsubL_refl.
  - destruct (IHHty V k eq_refl) as [Q0 [T1 [T2 [L [Hk [Hs [Hwf [Hq Hs2]]]]]]]].
    exists Q0, T1, T2, L. repeat match goal with |- _ /\ _ => split end; eauto.
    eapply qsubL_step; [eassumption|exact Hs2].
  - destruct (IHHty V k eq_refl) as [Q0 [T1 [T2 [L [Hk [Hs [Hwf [Hq Hs2]]]]]]]].
    exists Q0, T1, T2, L. repeat match goal with |- _ /\ _ => split end; eauto.
    eapply qualL_step; [eassumption|exact Hq].
Qed.

Lemma typing_ctx_qabs_inv_syn : forall E Q R k T,
  typing_ctx E Q (frame_qabs R :: k) T ->
  exists Q0 R0 T2 L,
    typing_ctx E Q0 k (open_qqt T2 R) /\ subqual E R R0 /\
    (forall X : atom, X `notin` L -> wf_qtyp (X ~ bind_qua R0 ++ E) (open_qqt T2 X)) /\
    qualL E Q Q0 /\ qsubL E T (qtyp_qtyp Q0 (typ_qall R0 T2)).
Proof.
  intros E Q R k T Hty. dependent induction Hty.
  - repeat eexists; repeat match goal with |- _ /\ _ => split end; eauto 10; try apply qualL_refl; try apply qsubL_refl.
  - destruct (IHHty R k eq_refl) as (Q0 & Rq & T2 & L & Hk & Hs & Hwf & Hq & Hs2).
    exists Q0, Rq, T2, L. repeat match goal with |- _ /\ _ => split end; eauto.
    eapply qsubL_step; [eassumption|exact Hs2].
  - destruct (IHHty R k eq_refl) as (Q0 & Rq & T2 & L & Hk & Hs & Hwf & Hq & Hs2).
    exists Q0, Rq, T2, L. repeat match goal with |- _ /\ _ => split end; eauto.
    eapply qualL_step; [eassumption|exact Hq].
Qed.

Lemma typing_ctx_inl_inv_syn : forall E Q P k T,
  typing_ctx E Q (frame_inl P :: k) T ->
  exists Q0 T1 T2,
    typing_ctx E Q0 k (qtyp_qtyp P (typ_sum T1 T2)) /\
    qualL E Q Q0 /\ qsubL E T T1.
Proof.
  intros E Q P k T Hty. dependent induction Hty.
  - repeat eexists; repeat match goal with |- _ /\ _ => split end; eauto 10; try apply qualL_refl; try apply qsubL_refl.
  - destruct (IHHty P k eq_refl) as [Q0 [T1 [T2 [Hk [Hq Hs]]]]].
    exists Q0, T1, T2. repeat match goal with |- _ /\ _ => split end; eauto.
    eapply qsubL_step; [eassumption|exact Hs].
  - destruct (IHHty P k eq_refl) as [Q0 [T1 [T2 [Hk [Hq Hs]]]]].
    exists Q0, T1, T2. repeat match goal with |- _ /\ _ => split end; eauto.
    eapply qualL_step; [eassumption|exact Hq].
Qed.

Lemma typing_ctx_inr_inv_syn : forall E Q P k T,
  typing_ctx E Q (frame_inr P :: k) T ->
  exists Q0 T1 T2,
    typing_ctx E Q0 k (qtyp_qtyp P (typ_sum T1 T2)) /\
    qualL E Q Q0 /\ qsubL E T T2.
Proof.
  intros E Q P k T Hty. dependent induction Hty.
  - repeat eexists; repeat match goal with |- _ /\ _ => split end; eauto 10; try apply qualL_refl; try apply qsubL_refl.
  - destruct (IHHty P k eq_refl) as [Q0 [T1 [T2 [Hk [Hq Hs]]]]].
    exists Q0, T1, T2. repeat match goal with |- _ /\ _ => split end; eauto.
    eapply qsubL_step; [eassumption|exact Hs].
  - destruct (IHHty P k eq_refl) as [Q0 [T1 [T2 [Hk [Hq Hs]]]]].
    exists Q0, T1, T2. repeat match goal with |- _ /\ _ => split end; eauto.
    eapply qualL_step; [eassumption|exact Hq].
Qed.

Lemma typing_ctx_pair_1_inv_syn : forall E Q P e k T,
  typing_ctx E Q (frame_pair_1 P e :: k) T ->
  exists Q0 T1 T2,
    wf_qua E P /\
    typing_ctx E Q0 k (qtyp_qtyp P (typ_pair T1 T2)) /\
    typing E Q0 e T2 /\ qualL E Q Q0 /\ qsubL E T T1.
Proof.
  intros E Q P e k T Hty. dependent induction Hty.
  - repeat eexists; repeat match goal with |- _ /\ _ => split end; eauto 10; try apply qualL_refl; try apply qsubL_refl.
  - destruct (IHHty P e k eq_refl) as [Q0 [T1 [T2 [Hwf [Hk [He [Hq Hs]]]]]]].
    exists Q0, T1, T2. repeat match goal with |- _ /\ _ => split end; eauto.
    eapply qsubL_step; [eassumption|exact Hs].
  - destruct (IHHty P e k eq_refl) as [Q0 [T1 [T2 [Hwf [Hk [He [Hq Hs]]]]]]].
    exists Q0, T1, T2. repeat match goal with |- _ /\ _ => split end; eauto.
    eapply qualL_step; [eassumption|exact Hq].
Qed.

Lemma typing_ctx_pair_2_inv_syn : forall E Q P v k T,
  typing_ctx E Q (frame_pair_2 P v :: k) T ->
  exists Q0 T1 T2,
    wf_qua E P /\
    typing_ctx E Q0 k (qtyp_qtyp P (typ_pair T1 T2)) /\
    value v /\ typing E Q0 v T1 /\ qualL E Q Q0 /\ qsubL E T T2.
Proof.
  intros E Q P v k T Hty. dependent induction Hty.
  - repeat eexists; repeat match goal with |- _ /\ _ => split end; eauto 10; try apply qualL_refl; try apply qsubL_refl.
  - destruct (IHHty P v k eq_refl) as [Q0 [T1 [T2 [Hwf [Hk [Hv [He [Hq Hs]]]]]]]].
    exists Q0, T1, T2. repeat match goal with |- _ /\ _ => split end; eauto.
    eapply qsubL_step; [eassumption|exact Hs].
  - destruct (IHHty P v k eq_refl) as [Q0 [T1 [T2 [Hwf [Hk [Hv [He [Hq Hs]]]]]]]].
    exists Q0, T1, T2. repeat match goal with |- _ /\ _ => split end; eauto.
    eapply qualL_step; [eassumption|exact Hq].
Qed.

Lemma typing_ctx_upqual_inv_syn : forall E Q P k T,
  typing_ctx E Q (frame_upqual P :: k) T ->
  exists Q0 T0,
    typing_ctx E Q0 k (qtyp_qtyp P T0) /\
    qualL E Q Q0 /\ qsubL E T (qtyp_qtyp P T0).
Proof.
  intros E Q P k T Hty. dependent induction Hty.
  - repeat eexists; repeat match goal with |- _ /\ _ => split end; eauto 10; try apply qualL_refl; try apply qsubL_refl.
  - destruct (IHHty P k eq_refl) as [Q0 [T0 [Hk [Hq Hs]]]].
    exists Q0, T0. repeat match goal with |- _ /\ _ => split end; eauto.
    eapply qsubL_step; [eassumption|exact Hs].
  - destruct (IHHty P k eq_refl) as [Q0 [T0 [Hk [Hq Hs]]]].
    exists Q0, T0. repeat match goal with |- _ /\ _ => split end; eauto.
    eapply qualL_step; [eassumption|exact Hq].
Qed.

Lemma typing_ctx_check_inv_syn : forall E Q R k T,
  typing_ctx E Q (frame_check R :: k) T ->
  exists Q0 P T0,
    wf_qua E R /\ typing_ctx E Q0 k (qtyp_qtyp P T0) /\
    qualL E Q Q0 /\ qsubL E T (qtyp_qtyp (qua_meet P R) T0).
Proof.
  intros E Q R k T Hty. dependent induction Hty.
  - repeat eexists; repeat match goal with |- _ /\ _ => split end; eauto 10; try apply qualL_refl; try apply qsubL_refl.
  - destruct (IHHty R k eq_refl) as [Q0 [P [T0 [Hwf [Hk [Hq Hs]]]]]].
    exists Q0, P, T0. repeat match goal with |- _ /\ _ => split end; eauto.
    eapply qsubL_step; [eassumption|exact Hs].
  - destruct (IHHty R k eq_refl) as [Q0 [P [T0 [Hwf [Hk [Hq Hs]]]]]].
    exists Q0, P, T0. repeat match goal with |- _ /\ _ => split end; eauto.
    eapply qualL_step; [eassumption|exact Hq].
Qed.


(* ===== inlined from /tmp/w1/SynInv.v ===== *)

Lemma syn_typing_var_inv : forall E Q e T,
  typing E Q e T ->
  forall vx, e = exp_fvar vx ->
  exists T0, binds vx (bind_typ T0) E /\ qsubR E T0 T /\ qualR E qua_bot Q.
Proof.
  intros E Q e T Hty. dependent induction Hty; intros vx Heq; try discriminate Heq.
  - (* typing_var *) inversion Heq; subst.
    exists T. split; [|split].
    + assumption.
    + apply qsubR_refl.
    + apply qualR_refl.
  - (* typing_sub *) inversion Heq; subst.
    destruct (IHHty vx eq_refl) as [T0 [Hb [Hq Hqual]]].
    exists T0. split; [|split].
    + assumption.
    + apply qsubR_step with (T := S); assumption.
    + assumption.
  - (* typing_subqual *) inversion Heq; subst.
    destruct (IHHty vx eq_refl) as [T0 [Hb [Hq Hqual]]].
    exists T0. split; [|split].
    + assumption.
    + assumption.
    + apply qualR_step with (R := Q); assumption.
Qed.

Lemma syn_typing_abs_inv : forall E Q e T,
  typing E Q e T ->
  forall (fP : qua) (fV : qtyp) (fb : exp), e = exp_abs fP fV fb ->
  exists (L : atoms) (V : qtyp) (T1 : qtyp),
    (forall x : atom, x `notin` L -> typing (x ~ bind_typ V ++ E) fP (open_ee fb x) T1) /\
    qualR E qua_bot Q /\
    qsubR E (qtyp_qtyp fP (typ_arrow V T1)) T.
Proof.
  intros E Q e T Hty. dependent induction Hty; intros fP fV fb Heq; try discriminate Heq.
  - inversion Heq; subst. exists L, fV, T1. split; [|split].
    + assumption. + apply qualR_refl. + apply qsubR_refl.
  - inversion Heq; subst.
    destruct (IHHty fP fV fb eq_refl) as [L [V [T1 [Hbody [Hqual Hq]]]]].
    exists L, V, T1. split; [|split].
    + assumption. + assumption. + apply qsubR_step with (T := S); assumption.
  - inversion Heq; subst.
    destruct (IHHty fP fV fb eq_refl) as [L [V [T1 [Hbody [Hqual Hq]]]]].
    exists L, V, T1. split; [|split].
    + assumption. + apply qualR_step with (R := Q); assumption. + assumption.
Qed.

Lemma syn_typing_tabs_inv : forall E Q e T,
  typing E Q e T ->
  forall (fP : qua) (fV : typ) (fb : exp), e = exp_tabs fP fV fb ->
  exists (L : atoms) (V : typ) (T1 : qtyp),
    (forall X : atom, X `notin` L -> typing (X ~ bind_sub V ++ E) fP (open_te fb X) (open_tqt T1 X)) /\
    qualR E qua_bot Q /\
    qsubR E (qtyp_qtyp fP (typ_all V T1)) T.
Proof.
  intros E Q e T Hty. dependent induction Hty; intros fP fV fb Heq; try discriminate Heq.
  - inversion Heq; subst. exists L, fV, T1. split; [|split].
    + assumption. + apply qualR_refl. + apply qsubR_refl.
  - inversion Heq; subst.
    destruct (IHHty fP fV fb eq_refl) as [L [V [T1 [Hbody [Hqual Hq]]]]].
    exists L, V, T1. split; [|split].
    + assumption. + assumption. + apply qsubR_step with (T := S); assumption.
  - inversion Heq; subst.
    destruct (IHHty fP fV fb eq_refl) as [L [V [T1 [Hbody [Hqual Hq]]]]].
    exists L, V, T1. split; [|split].
    + assumption. + apply qualR_step with (R := Q); assumption. + assumption.
Qed.

Lemma syn_typing_qabs_inv : forall E Q e T,
  typing E Q e T ->
  forall (fP : qua) (fQ : qua) (fb : exp), e = exp_qabs fP fQ fb ->
  exists (L : atoms) (Q0 : qua) (T1 : qtyp),
    wf_qua E fP /\
    (forall X : atom, X `notin` L -> typing (X ~ bind_qua Q0 ++ E) fP (open_qe fb X) (open_qqt T1 X)) /\
    qualR E qua_bot Q /\
    qsubR E (qtyp_qtyp fP (typ_qall Q0 T1)) T.
Proof.
  intros E Q e T Hty. dependent induction Hty; intros fP fQ fb Heq; try discriminate Heq.
  - inversion Heq; subst. exists L, fQ, T1. split; [|split; [|split]].
    + assumption. + assumption. + apply qualR_refl. + apply qsubR_refl.
  - inversion Heq; subst.
    destruct (IHHty fP fQ fb eq_refl) as [L [Q0 [T1 [Hwf [Hbody [Hqual Hq]]]]]].
    exists L, Q0, T1. split; [|split; [|split]].
    + assumption. + assumption. + assumption. + apply qsubR_step with (T := S); assumption.
  - inversion Heq; subst.
    destruct (IHHty fP fQ fb eq_refl) as [L [Q0 [T1 [Hwf [Hbody [Hqual Hq]]]]]].
    exists L, Q0, T1. split; [|split; [|split]].
    + assumption. + assumption. + apply qualR_step with (R := Q); assumption. + assumption.
Qed.

Lemma syn_typing_tapp_inv : forall E Q e T,
  typing E Q e T ->
  forall (f1 : exp) (fV : typ), e = exp_tapp f1 fV ->
  exists Q0 T1 T2,
    typing E Q0 f1 (qtyp_qtyp Q0 (typ_all T1 T2)) /\
    sub E fV T1 /\
    qualR E Q0 Q /\
    qsubR E (open_tqt T2 fV) T.
Proof.
  intros E Q e T Hty. dependent induction Hty; intros f1 fV Heq; try discriminate Heq.
  - (* typing_tapp *) inversion Heq; subst.
    exists Q, T1, T2. split; [|split; [|split]].
    + assumption.
    + assumption.
    + apply qualR_refl.
    + apply qsubR_refl.
  - (* typing_sub *) inversion Heq; subst.
    destruct (IHHty f1 fV eq_refl) as [Q0 [T1 [T2 [He [Hs [Hq Hqs]]]]]].
    exists Q0, T1, T2. split; [|split; [|split]].
    + assumption.
    + assumption.
    + assumption.
    + apply qsubR_step with (T := S); assumption.
  - (* typing_subqual *) inversion Heq; subst.
    destruct (IHHty f1 fV eq_refl) as [Q0 [T1 [T2 [He [Hs [Hq Hqs]]]]]].
    exists Q0, T1, T2. split; [|split; [|split]].
    + assumption.
    + assumption.
    + apply qualR_step with (R := Q); assumption.
    + assumption.
Qed.

Lemma syn_typing_qapp_inv : forall E Q e T,
  typing E Q e T ->
  forall (f1 : exp) (fQ : qua), e = exp_qapp f1 fQ ->
  exists Q0 Q1 T0,
    typing E Q0 f1 (qtyp_qtyp Q0 (typ_qall Q1 T0)) /\
    subqual E Q0 Q1 /\
    qualR E Q0 Q /\
    qsubR E (open_qqt T0 Q0) T.
Proof.
  intros E Q e T Hty. dependent induction Hty; intros f1 fQ Heq; try discriminate Heq.
  - (* typing_qapp *) inversion Heq; subst.
    exists fQ, Q1, T. split; [|split; [|split]].
    + assumption.
    + assumption.
    + apply qualR_refl.
    + apply qsubR_refl.
  - (* typing_sub *) inversion Heq; subst.
    destruct (IHHty f1 fQ eq_refl) as [Q0 [Q1 [T0 [He [Hs [Hq Hqs]]]]]].
    exists Q0, Q1, T0. split; [|split; [|split]].
    + assumption.
    + assumption.
    + assumption.
    + apply qsubR_step with (T := S); assumption.
  - (* typing_subqual *) inversion Heq; subst.
    destruct (IHHty f1 fQ eq_refl) as [Q0 [Q1 [T0 [He [Hs [Hq Hqs]]]]]].
    exists Q0, Q1, T0. split; [|split; [|split]].
    + assumption.
    + assumption.
    + apply qualR_step with (R := Q); assumption.
    + assumption.
Qed.

Lemma syn_typing_let_inv : forall E Q e T,
  typing E Q e T ->
  forall (f1 f2 : exp), e = exp_let f1 f2 ->
  exists Q0 T1 T2,
    typing E Q0 f1 T1 /\
    (exists L : atoms,
       forall x : atom, x `notin` L ->
         typing (x ~ bind_typ T1 ++ E) Q0 (open_ee f2 x) T2) /\
    qualR E Q0 Q /\
    qsubR E T2 T.
Proof.
  intros E Q e T Hty. dependent induction Hty; intros f1 f2 Heq; try discriminate Heq.
  - (* typing_sub *) inversion Heq; subst.
    destruct (IHHty f1 f2 eq_refl) as [Q0 [T1 [T2 Hrest]]].
    destruct Hrest as [He Hrest].
    destruct Hrest as [[Lb Hbody] Hrest].
    destruct Hrest as [Hq Hqs].
    exists Q0, T1, T2. split; [|split; [|split]].
    + assumption.
    + exists Lb. assumption.
    + assumption.
    + apply qsubR_step with (T := S); assumption.
  - (* typing_subqual *) inversion Heq; subst.
    destruct (IHHty f1 f2 eq_refl) as [Q0 [T1 [T2 Hrest]]].
    destruct Hrest as [He Hrest].
    destruct Hrest as [[Lb Hbody] Hrest].
    destruct Hrest as [Hq Hqs].
    exists Q0, T1, T2. split; [|split; [|split]].
    + assumption.
    + exists Lb. assumption.
    + apply qualR_step with (R := Q); assumption.
    + assumption.
  - (* typing_let *) inversion Heq; subst.
    eexists; eexists; eexists. split; [|split; [|split]].
    + eassumption.
    + eexists; eassumption.
    + apply qualR_refl.
    + apply qsubR_refl.
Qed.


Lemma syn_typing_inl_inv : forall E Q e T,
  typing E Q e T ->
  forall (fP : qua) (f1 : exp), e = exp_inl fP f1 ->
  exists Q0 T1 T2,
    typing E Q0 f1 T1 /\ wf_qua E fP /\ wf_qtyp E T2 /\
    qualR E Q0 Q /\ qsubR E (qtyp_qtyp fP (typ_sum T1 T2)) T.
Proof.
  intros E Q e T Hty. dependent induction Hty; intros fP f1 Heq; try discriminate Heq.
  - inversion Heq; subst.
    destruct (IHHty fP f1 eq_refl) as [Q0 [T1 [T2 [He [Hw [Hw2 [Hq Hqs]]]]]]].
    exists Q0, T1, T2. split; [|split; [|split; [|split]]].
    + assumption. + assumption. + assumption. + assumption.
    + apply qsubR_step with (T := S); assumption.
  - inversion Heq; subst.
    destruct (IHHty fP f1 eq_refl) as [Q0 [T1 [T2 [He [Hw [Hw2 [Hq Hqs]]]]]]].
    exists Q0, T1, T2. split; [|split; [|split; [|split]]].
    + assumption. + assumption. + assumption.
    + apply qualR_step with (R := Q); assumption. + assumption.
  - inversion Heq; subst. eexists; eexists; eexists. split; [|split; [|split; [|split]]].
    + eassumption. + eassumption. + eassumption. + apply qualR_refl. + apply qsubR_refl.
Qed.

Lemma syn_typing_inr_inv : forall E Q e T,
  typing E Q e T ->
  forall (fP : qua) (f1 : exp), e = exp_inr fP f1 ->
  exists Q0 T1 T2,
    typing E Q0 f1 T2 /\ wf_qua E fP /\ wf_qtyp E T1 /\
    qualR E Q0 Q /\ qsubR E (qtyp_qtyp fP (typ_sum T1 T2)) T.
Proof.
  intros E Q e T Hty. dependent induction Hty; intros fP f1 Heq; try discriminate Heq.
  - inversion Heq; subst.
    destruct (IHHty fP f1 eq_refl) as [Q0 [T1 [T2 [He [Hw [Hw2 [Hq Hqs]]]]]]].
    exists Q0, T1, T2. split; [|split; [|split; [|split]]].
    + assumption. + assumption. + assumption. + assumption.
    + apply qsubR_step with (T := S); assumption.
  - inversion Heq; subst.
    destruct (IHHty fP f1 eq_refl) as [Q0 [T1 [T2 [He [Hw [Hw2 [Hq Hqs]]]]]]].
    exists Q0, T1, T2. split; [|split; [|split; [|split]]].
    + assumption. + assumption. + assumption.
    + apply qualR_step with (R := Q); assumption. + assumption.
  - inversion Heq; subst. eexists; eexists; eexists. split; [|split; [|split; [|split]]].
    + eassumption. + eassumption. + eassumption. + apply qualR_refl. + apply qsubR_refl.
Qed.

Lemma syn_typing_case_inv : forall E Q e T,
  typing E Q e T ->
  forall (f1 f2 f3 : exp), e = exp_case f1 f2 f3 ->
  exists Q0 P T1 T2 Tbody,
    typing E Q0 f1 (qtyp_qtyp P (typ_sum T1 T2)) /\
    (exists L : atoms, forall x : atom, x `notin` L ->
       typing (x ~ bind_typ T1 ++ E) Q0 (open_ee f2 x) Tbody) /\
    (exists L : atoms, forall x : atom, x `notin` L ->
       typing (x ~ bind_typ T2 ++ E) Q0 (open_ee f3 x) Tbody) /\
    qualR E Q0 Q /\ qsubR E Tbody T.
Proof.
  intros E Q e T Hty. dependent induction Hty; intros f1 f2 f3 Heq; try discriminate Heq.
  - (* sub *) inversion Heq; subst.
    destruct (IHHty f1 f2 f3 eq_refl) as [Q0 [P [T1 [T2 [Tb Hrest]]]]].
    destruct Hrest as [He Hrest]; destruct Hrest as [[L2 Hb2] Hrest].
    destruct Hrest as [[L3 Hb3] Hrest]; destruct Hrest as [Hq Hqs].
    exists Q0, P, T1, T2, Tb. split; [|split; [|split; [|split]]].
    + assumption. + exists L2; assumption. + exists L3; assumption. + assumption.
    + apply qsubR_step with (T := S); assumption.
  - (* subqual *) inversion Heq; subst.
    destruct (IHHty f1 f2 f3 eq_refl) as [Q0 [P [T1 [T2 [Tb Hrest]]]]].
    destruct Hrest as [He Hrest]; destruct Hrest as [[L2 Hb2] Hrest].
    destruct Hrest as [[L3 Hb3] Hrest]; destruct Hrest as [Hq Hqs].
    exists Q0, P, T1, T2, Tb. split; [|split; [|split; [|split]]].
    + assumption. + exists L2; assumption. + exists L3; assumption.
    + apply qualR_step with (R := Q); assumption.
    + assumption.
  - (* case *) inversion Heq; subst.
    eexists; eexists; eexists; eexists; eexists. split; [|split; [|split; [|split]]].
    + eassumption.
    + eexists; eassumption.
    + eexists; eassumption.
    + apply qualR_refl. + apply qsubR_refl.
Qed.

Lemma syn_typing_pair_inv : forall E Q e T,
  typing E Q e T ->
  forall (fP : qua) (f1 f2 : exp), e = exp_pair fP f1 f2 ->
  exists Q0 T1 T2,
    typing E Q0 f1 T1 /\ typing E Q0 f2 T2 /\ wf_qua E fP /\
    qualR E Q0 Q /\ qsubR E (qtyp_qtyp fP (typ_pair T1 T2)) T.
Proof.
  intros E Q e T Hty. dependent induction Hty; intros fP f1 f2 Heq; try discriminate Heq.
  - inversion Heq; subst.
    destruct (IHHty fP f1 f2 eq_refl) as [Q0 [T1 [T2 [H1 [H2 [Hw [Hq Hqs]]]]]]].
    exists Q0, T1, T2. split; [|split; [|split; [|split]]].
    + assumption. + assumption. + assumption. + assumption.
    + apply qsubR_step with (T := S); assumption.
  - inversion Heq; subst.
    destruct (IHHty fP f1 f2 eq_refl) as [Q0 [T1 [T2 [H1 [H2 [Hw [Hq Hqs]]]]]]].
    exists Q0, T1, T2. split; [|split; [|split; [|split]]].
    + assumption. + assumption. + assumption.
    + apply qualR_step with (R := Q); assumption. + assumption.
  - inversion Heq; subst. eexists; eexists; eexists. split; [|split; [|split; [|split]]].
    + eassumption. + eassumption. + eassumption. + apply qualR_refl. + apply qsubR_refl.
Qed.

Lemma syn_typing_first_inv : forall E Q e T,
  typing E Q e T ->
  forall (f1 : exp), e = exp_first f1 ->
  exists Q0 P T1 T2,
    typing E Q0 f1 (qtyp_qtyp P (typ_pair T1 T2)) /\
    qualR E Q0 Q /\ qsubR E T1 T.
Proof.
  intros E Q e T Hty. dependent induction Hty; intros f1 Heq; try discriminate Heq.
  - (* sub *) inversion Heq; subst.
    destruct (IHHty f1 eq_refl) as [Q0 [P [T1 [T2 [He [Hq Hqs]]]]]].
    exists Q0, P, T1, T2. split; [|split].
    + assumption. + assumption.
    + apply qsubR_step with (T := S); assumption.
  - (* subqual *) inversion Heq; subst.
    destruct (IHHty f1 eq_refl) as [Q0 [P [T1 [T2 [He [Hq Hqs]]]]]].
    exists Q0, P, T1, T2. split; [|split].
    + assumption.
    + apply qualR_step with (R := Q); assumption.
    + assumption.
  - (* first *) inversion Heq; subst.
    eexists; eexists; eexists; eexists. split; [|split].
    + eassumption. + apply qualR_refl. + apply qsubR_refl.
Qed.

Lemma syn_typing_second_inv : forall E Q e T,
  typing E Q e T ->
  forall (f1 : exp), e = exp_second f1 ->
  exists Q0 P T1 T2,
    typing E Q0 f1 (qtyp_qtyp P (typ_pair T1 T2)) /\
    qualR E Q0 Q /\ qsubR E T2 T.
Proof.
  intros E Q e T Hty. dependent induction Hty; intros f1 Heq; try discriminate Heq.
  - (* sub *) inversion Heq; subst.
    destruct (IHHty f1 eq_refl) as [Q0 [P [T1 [T2 [He [Hq Hqs]]]]]].
    exists Q0, P, T1, T2. split; [|split].
    + assumption. + assumption.
    + apply qsubR_step with (T := S); assumption.
  - (* subqual *) inversion Heq; subst.
    destruct (IHHty f1 eq_refl) as [Q0 [P [T1 [T2 [He [Hq Hqs]]]]]].
    exists Q0, P, T1, T2. split; [|split].
    + assumption.
    + apply qualR_step with (R := Q); assumption.
    + assumption.
  - (* second *) inversion Heq; subst.
    eexists; eexists; eexists; eexists. split; [|split].
    + eassumption. + apply qualR_refl. + apply qsubR_refl.
Qed.

Lemma syn_typing_upqual_inv : forall E Q e T,
  typing E Q e T ->
  forall (fP : qua) (f1 : exp), e = exp_upqual fP f1 ->
  exists Qe Qtyp P T0,
    typing E Qe f1 (qtyp_qtyp Qtyp T0) /\
    subqual E Qtyp P /\
    qualR E Qe Q /\
    qsubR E (qtyp_qtyp P T0) T.
Proof.
  intros E Q e T Hty. dependent induction Hty; intros fP f1 Heq; try discriminate Heq.
  - (* sub *) inversion Heq; subst.
    destruct (IHHty fP f1 eq_refl) as [Qe [Qt [P [T0 [He [Hs [Hq Hqs]]]]]]].
    exists Qe, Qt, P, T0. split; [|split; [|split]].
    + assumption. + assumption. + assumption.
    + apply qsubR_step with (T := S); assumption.
  - (* subqual *) inversion Heq; subst.
    destruct (IHHty fP f1 eq_refl) as [Qe [Qt [P [T0 [He [Hs [Hq Hqs]]]]]]].
    exists Qe, Qt, P, T0. split; [|split; [|split]].
    + assumption. + assumption.
    + apply qualR_step with (R := Q); assumption.
    + assumption.
  - (* upqual *) inversion Heq; subst.
    eexists; eexists; eexists; eexists. split; [|split; [|split]].
    + eassumption. + eassumption. + apply qualR_refl. + apply qsubR_refl.
Qed.

Lemma syn_typing_check_inv : forall E Q e T,
  typing E Q e T ->
  forall (fP : qua) (f1 : exp), e = exp_check fP f1 ->
  exists Qe Qtyp P T0,
    typing E Qe f1 (qtyp_qtyp Qtyp T0) /\
    subqual E Qtyp P /\
    qualR E Qe Q /\
    qsubR E (qtyp_qtyp Qtyp T0) T.
Proof.
  intros E Q e T Hty. dependent induction Hty; intros fP f1 Heq; try discriminate Heq.
  - (* sub *) inversion Heq; subst.
    destruct (IHHty fP f1 eq_refl) as [Qe [Qt [P [T0 [He [Hs [Hq Hqs]]]]]]].
    exists Qe, Qt, P, T0. split; [|split; [|split]].
    + assumption. + assumption. + assumption.
    + apply qsubR_step with (T := S); assumption.
  - (* subqual *) inversion Heq; subst.
    destruct (IHHty fP f1 eq_refl) as [Qe [Qt [P [T0 [He [Hs [Hq Hqs]]]]]]].
    exists Qe, Qt, P, T0. split; [|split; [|split]].
    + assumption. + assumption.
    + apply qualR_step with (R := Q); assumption.
    + assumption.
  - (* check *) inversion Heq; subst.
    eexists; eexists; eexists; eexists. split; [|split; [|split]].
    + eassumption. + eassumption. + apply qualR_refl. + apply qsubR_refl.
Qed.


(* ===== inlined from /tmp/w1/Part1.v ===== *)

Section Hyp.
Context (subqual_trans_env : forall E Q R S,
  wf_env E -> subqual E Q R -> subqual E R S -> subqual E Q S).

Lemma abstractize_compat_inv : forall E (r q : concrete_qua),
  subqual E (abstractize r) (abstractize q) -> cqua_compatible r q.
Proof.
  intros E r q H. destruct r; destruct q; simpl in *;
    try (inversion H; constructor); try (inversion H).
Qed.

Lemma subqual_concretize_le : forall E Q c,
  wf_env E -> wf_qua E Q -> concretize Q = Some c ->
  subqual E Q (abstractize c).
Proof.
  intros E Q c Hwf HQ Hc. revert c Hc. induction HQ; intros c0 Hc; simpl in Hc.
  - (* top *) inversion Hc; subst c0. apply subqual_top; [exact Hwf|apply wf_qua_top].
  - (* fvar *) discriminate Hc.
  - (* meet *) destruct (concretize Q1) as [c1|] eqn:E1; try discriminate.
    destruct c1; simpl in Hc.
    + destruct (concretize Q2) as [c2|] eqn:E2; try discriminate.
      inversion Hc; subst c0.
      destruct c2.
      * apply subqual_top; [exact Hwf|apply wf_qua_meet; assumption].
      * apply subqual_meet_elimr.
        -- exact HQ1.
        -- apply (IHHQ2 Hwf cqua_bot eq_refl).
    + inversion Hc; subst c0.
      apply subqual_meet_eliml.
      * apply (IHHQ1 Hwf cqua_bot eq_refl).
      * exact HQ2.
  - (* join *) destruct (concretize Q1) as [c1|] eqn:E1; try discriminate.
    destruct c1; simpl in Hc.
    + inversion Hc; subst c0. apply subqual_top; [exact Hwf|apply wf_qua_join; assumption].
    + destruct (concretize Q2) as [c2|] eqn:E2; try discriminate.
      inversion Hc; subst c0.
      apply subqual_join_elim.
      * eapply subqual_trans_env.
        -- exact Hwf.
        -- apply (IHHQ1 Hwf cqua_bot eq_refl).
        -- apply subqual_bot.
           ++ exact Hwf.
           ++ destruct c2; simpl; [apply wf_qua_top|apply wf_qua_bot].
      * apply (IHHQ2 Hwf c2 eq_refl).
  - (* bot *) inversion Hc; subst c0. apply subqual_bot; [exact Hwf|apply wf_qua_bot].
Qed.

Lemma subqual_concretize : forall E Q R r q,
  wf_env E -> subqual E Q R -> concretize Q = Some r -> concretize R = Some q ->
  cqua_compatible r q.
Proof.
  intros E Q R r q Hwf Hsq Hr Hq.
  destruct (subqual_wf E Q R Hwf Hsq) as [HQ HR].
  assert (H1 : subqual E (abstractize r) Q).
  { apply wf_qua_concretize_subqual; assumption. }
  assert (H2 : subqual E (abstractize r) R).
  { eapply subqual_trans_env; [exact Hwf|exact H1|exact Hsq]. }
  assert (H3 : subqual E R (abstractize q)).
  { apply subqual_concretize_le; assumption. }
  assert (H4 : subqual E (abstractize r) (abstractize q)).
  { eapply subqual_trans_env; [exact Hwf|exact H2|exact H3]. }
  apply (abstractize_compat_inv E r q). exact H4.
Qed.

Lemma conc_abstractize_inv : forall (t : concrete_qua) (q : concrete_qua),
  concretize (abstractize t) = Some q -> q = t.
Proof. intros t q H. destruct t; simpl in H; inversion H; reflexivity. Qed.

Lemma cqua_compat_top : forall s, cqua_compatible s cqua_top.
Proof. destruct s; constructor. Qed.
Lemma cqua_compat_bot : forall s, cqua_compatible cqua_bot s.
Proof. destruct s; constructor. Qed.

Lemma typing_ctx_barrier_invariant : forall E Q c T,
  typing_ctx E Q c T -> wf_env E ->
  forall RR, subqual E RR Q ->
  forall tt, concretize RR = Some tt -> barrier_compatible c tt.
Proof.
  intros E Q c T H. induction H; intros Hwf RR Hsub tt Ht.
  - apply barrier_compatible_done.
  - apply barrier_compatible_other.
    + apply (IHtyping_ctx Hwf RR Hsub tt Ht).
    + intros t0 Hc; inversion Hc.
  - apply barrier_compatible_other.
    + apply (IHtyping_ctx Hwf RR Hsub tt Ht).
    + intros t0 Hc; inversion Hc.
  - apply barrier_compatible_other.
    + apply (IHtyping_ctx Hwf RR Hsub tt Ht).
    + intros t0 Hc; inversion Hc.
  - apply barrier_compatible_other.
    + apply (IHtyping_ctx Hwf RR Hsub tt Ht).
    + intros t0 Hc; inversion Hc.
  - apply barrier_compatible_other.
    + apply (IHtyping_ctx Hwf RR Hsub tt Ht).
    + intros t0 Hc; inversion Hc.
  - apply barrier_compatible_other.
    + apply (IHtyping_ctx Hwf RR Hsub tt Ht).
    + intros t0 Hc; inversion Hc.
  - apply barrier_compatible_other.
    + apply (IHtyping_ctx Hwf RR Hsub tt Ht).
    + intros t0 Hc; inversion Hc.
  - apply barrier_compatible_other.
    + apply (IHtyping_ctx Hwf RR Hsub tt Ht).
    + intros t0 Hc; inversion Hc.
  - apply barrier_compatible_other.
    + apply (IHtyping_ctx Hwf RR Hsub tt Ht).
    + intros t0 Hc; inversion Hc.
  - apply barrier_compatible_other.
    + apply (IHtyping_ctx Hwf RR Hsub tt Ht).
    + intros t0 Hc; inversion Hc.
  - apply barrier_compatible_other.
    + apply (IHtyping_ctx Hwf RR Hsub tt Ht).
    + intros t0 Hc; inversion Hc.
  - apply barrier_compatible_other.
    + apply (IHtyping_ctx Hwf RR Hsub tt Ht).
    + intros t0 Hc; inversion Hc.
  - (* barrier *) simpl in Ht.
    match goal with
    | Hconc : concretize ?Qp = Some ?s0, Hle : ?b ≤ ?s0 |- _ =>
        assert (Httb : cqua_compatible tt b) by
          (eapply subqual_concretize; [exact Hwf|exact Hsub|exact Ht|apply concretize_abstractize]);
        apply barrier_compatible_frame;
        [ assert (HQwf : wf_qua E Qp) by
            (eapply typing_ctx_wf_qua; [exact Hwf|exact H]);
          assert (Habs0 : subqual E (abstractize b) (abstractize s0)) by
            (apply subqual_abstractize; [exact Hwf|exact Hle]);
          assert (HabsQ : subqual E (abstractize s0) Qp) by
            (apply wf_qua_concretize_subqual; assumption);
          assert (HRQ : subqual E RR Qp) by
            (eapply subqual_trans_env; [exact Hwf|exact Hsub|];
             eapply subqual_trans_env; [exact Hwf|exact Habs0|exact HabsQ]);
          apply (IHtyping_ctx Hwf RR HRQ tt Ht)
        | exact Httb ]
    end.
  - apply barrier_compatible_other.
    + apply (IHtyping_ctx Hwf RR Hsub tt Ht).
    + intros t0 Hc; inversion Hc.
  - apply barrier_compatible_other.
    + apply (IHtyping_ctx Hwf RR Hsub tt Ht).
    + intros t0 Hc; inversion Hc.
  - apply (IHtyping_ctx Hwf RR Hsub tt Ht).
  - (* subqual *) match goal with
    | Hsq : subqual E ?R0 ?Q0 |- _ =>
        assert (HRQ : subqual E RR Q0) by
          (eapply subqual_trans_env; [exact Hwf|exact Hsub|exact Hsq]);
        apply (IHtyping_ctx Hwf RR HRQ tt Ht)
    end.
Qed.

End Hyp.


(* ===== inlined from /tmp/w1/Shape.v ===== *)

Section Hyp.
Context (subqual_trans_env : forall E Q R S,
  wf_env E -> subqual E Q R -> subqual E R S -> subqual E Q S).

Lemma binds_empty : forall (x:atom) (b:binding), binds x b empty -> False.
Proof. intros. destruct H. Qed.

Lemma sub_arrow_empty : forall S T1 T2, sub empty S (typ_arrow T1 T2) ->
  exists S1 S2, S = typ_arrow S1 S2.
Proof.
  intros S T1 T2 H. dependent induction H;
    try (exfalso; eapply binds_empty; eassumption); try discriminate.
  - exists S1, S2. reflexivity.
Qed.
Lemma sub_all_empty : forall S T1 T2, sub empty S (typ_all T1 T2) ->
  exists S1 S2, S = typ_all S1 S2.
Proof.
  intros S T1 T2 H. dependent induction H;
    try (exfalso; eapply binds_empty; eassumption); try discriminate.
  - exists S1, S2. reflexivity.
Qed.
Lemma sub_qall_empty : forall S Q T, sub empty S (typ_qall Q T) ->
  exists S1 S2, S = typ_qall S1 S2.
Proof.
  intros S Q T H. dependent induction H;
    try (exfalso; eapply binds_empty; eassumption); try discriminate.
  - exists S1, S2. reflexivity.
Qed.
Lemma sub_sum_empty : forall S T1 T2, sub empty S (typ_sum T1 T2) ->
  exists S1 S2, S = typ_sum S1 S2.
Proof.
  intros S T1 T2 H. dependent induction H;
    try (exfalso; eapply binds_empty; eassumption); try discriminate.
  - exists S1, S2. reflexivity.
Qed.
Lemma sub_pair_empty : forall S T1 T2, sub empty S (typ_pair T1 T2) ->
  exists S1 S2, S = typ_pair S1 S2.
Proof.
  intros S T1 T2 H. dependent induction H;
    try (exfalso; eapply binds_empty; eassumption); try discriminate.
  - exists S1, S2. reflexivity.
Qed.

Lemma subqtype_arrow_empty : forall S Qt T1 T2,
  subqtype empty S (qtyp_qtyp Qt (typ_arrow T1 T2)) ->
  exists QS S1 S2, S = qtyp_qtyp QS (typ_arrow S1 S2) /\ subqual empty QS Qt.
Proof.
  intros S Qt T1 T2 H. inversion H; subst.
  destruct (sub_arrow_empty _ _ _ H5) as [S1 [S2 HS]].
  exists Q1, S1, S2. split; [rewrite HS; reflexivity|exact H4].
Qed.
Lemma subqtype_all_empty : forall S Qt T1 T2,
  subqtype empty S (qtyp_qtyp Qt (typ_all T1 T2)) ->
  exists QS V S2, S = qtyp_qtyp QS (typ_all V S2) /\ subqual empty QS Qt.
Proof.
  intros S Qt T1 T2 H. inversion H; subst.
  destruct (sub_all_empty _ _ _ H5) as [V [S2 HS]].
  exists Q1, V, S2. split; [rewrite HS; reflexivity|exact H4].
Qed.
Lemma subqtype_qall_empty : forall S Qt Q T,
  subqtype empty S (qtyp_qtyp Qt (typ_qall Q T)) ->
  exists QS Q1 S2, S = qtyp_qtyp QS (typ_qall Q1 S2) /\ subqual empty QS Qt.
Proof.
  intros S Qt Q T H. inversion H; subst.
  destruct (sub_qall_empty _ _ _ H5) as [Qq [S2 HS]].
  exists Q1, Qq, S2. split; [rewrite HS; reflexivity|exact H4].
Qed.
Lemma subqtype_sum_empty : forall S Qt T1 T2,
  subqtype empty S (qtyp_qtyp Qt (typ_sum T1 T2)) ->
  exists QS S1 S2, S = qtyp_qtyp QS (typ_sum S1 S2) /\ subqual empty QS Qt.
Proof.
  intros S Qt T1 T2 H. inversion H; subst.
  destruct (sub_sum_empty _ _ _ H5) as [S1 [S2 HS]].
  exists Q1, S1, S2. split; [rewrite HS; reflexivity|exact H4].
Qed.
Lemma subqtype_pair_empty : forall S Qt T1 T2,
  subqtype empty S (qtyp_qtyp Qt (typ_pair T1 T2)) ->
  exists QS S1 S2, S = qtyp_qtyp QS (typ_pair S1 S2) /\ subqual empty QS Qt.
Proof.
  intros S Qt T1 T2 H. inversion H; subst.
  destruct (sub_pair_empty _ _ _ H5) as [S1 [S2 HS]].
  exists Q1, S1, S2. split; [rewrite HS; reflexivity|exact H4].
Qed.

Lemma wf_qua_bind_typ_inv : forall E x (V : qtyp) Q,
  wf_qua (x ~ bind_typ V ++ E) Q -> wf_qua E Q.
Proof.
  intros E x V Q H. remember (x ~ bind_typ V ++ E) as Ebody eqn:Eb.
  induction H; subst.
  - apply wf_qua_top.
  - simpl in H. apply binds_cons_1 in H. destruct H as [[Heq Hbeq]|Hin].
    + discriminate Hbeq.
    + apply wf_qua_fvar with (R := R). exact Hin.
  - apply wf_qua_meet; eauto.
  - apply wf_qua_join; eauto.
  - apply wf_qua_bot.
Qed.
Lemma wf_qua_bind_sub_inv : forall E x (V : typ) Q,
  wf_qua (x ~ bind_sub V ++ E) Q -> wf_qua E Q.
Proof.
  intros E x V Q H. remember (x ~ bind_sub V ++ E) as Ebody eqn:Eb.
  induction H; subst.
  - apply wf_qua_top.
  - simpl in H. apply binds_cons_1 in H. destruct H as [[Heq Hbeq]|Hin].
    + discriminate Hbeq.
    + apply wf_qua_fvar with (R := R). exact Hin.
  - apply wf_qua_meet; eauto.
  - apply wf_qua_join; eauto.
  - apply wf_qua_bot.
Qed.

Inductive tshape : Set := tTop | tArrow | tAll | tQall | tSum | tPair | tRef | tFvar.
Definition tshape_of (T : typ) : tshape :=
  match T with
  | typ_top => tTop
  | typ_fvar _ => tFvar
  | typ_arrow _ _ => tArrow
  | typ_all _ _ => tAll
  | typ_qall _ _ => tQall
  | typ_sum _ _ => tSum
  | typ_pair _ _ => tPair
  | typ_ref _ => tRef
  | typ_bvar _ => tFvar
  end.

Lemma sub_target_tshape_env : forall E S T, sub E S T ->
  E = empty -> tshape_of T <> tTop -> tshape_of S = tshape_of T.
Proof.
  intros E S T H. induction H using sub_mut_ind
    with (P := fun E S T _ => E = empty ->
              tshape_of T <> tTop -> tshape_of S = tshape_of T)
         (P0 := fun E S T _ => True).
  - intros HE Hn; subst E; exfalso; apply Hn; reflexivity.
  - intros HE Hn; subst E; reflexivity.
  - intros HE Hn; subst E;
      match goal with b : binds _ _ empty |- _ => destruct b end.
  - intros HE Hn; subst E; reflexivity.
  - intros HE Hn; subst E; reflexivity.
  - intros HE Hn; subst E; reflexivity.
  - intros HE Hn; subst E; reflexivity.
  - intros HE Hn; subst E; reflexivity.
  - trivial.
Qed.

Lemma sub_target_tshape_empty : forall S T, sub empty S T ->
  tshape_of T <> tTop -> tshape_of S = tshape_of T.
Proof. intros. eapply sub_target_tshape_env; [exact H|reflexivity|exact H0]. Qed.

Lemma subqtype_target_tshape_empty : forall S T,
  subqtype empty S T ->
  forall Qt Tt, T = qtyp_qtyp Qt Tt -> tshape_of Tt <> tTop ->
  exists Qs Ts, S = qtyp_qtyp Qs Ts /\ tshape_of Ts = tshape_of Tt.
Proof.
  intros S T H. inversion H; subst. intros Qt Tt HT Hn.
  inversion HT; subst.
  eexists; eexists. split; [reflexivity|].
  eapply sub_target_tshape_empty; [eassumption|exact Hn].
Qed.

Lemma qsubR_tshape_empty : forall S T, qsubR empty S T ->
  forall Qt Tt, T = qtyp_qtyp Qt Tt -> tshape_of Tt <> tTop ->
  exists Qs Ts, S = qtyp_qtyp Qs Ts /\ tshape_of Ts = tshape_of Tt.
Proof.
  intros S T H. induction H as [T0|S0 T0 U H0 IH Hstep];
    intros Qt Tt HT Hn.
  - exists Qt, Tt. split; [exact HT|reflexivity].
  - destruct (subqtype_target_tshape_empty T0 U Hstep Qt Tt HT Hn) as
      [QS [TS Hpair]].
    destruct Hpair as [HT0 Hshape].
    assert (HnTS : tshape_of TS <> tTop) by (rewrite Hshape; exact Hn).
    destruct (IH QS TS HT0 HnTS) as [Q' [T' [HS Hshape']]].
    exists Q', T'. split; [exact HS|].
    rewrite Hshape'. exact Hshape.
Qed.

Lemma qsubR_tshape_eq : forall Qs Ts Qt Tt,
  qsubR empty (qtyp_qtyp Qs Ts) (qtyp_qtyp Qt Tt) ->
  tshape_of Tt <> tTop -> tshape_of Ts = tshape_of Tt.
Proof.
  intros Qs Ts Qt Tt H Hn.
  destruct (qsubR_tshape_empty _ _ H Qt Tt eq_refl Hn) as
    [Q' [T' [Heq Hshape]]].
  inversion Heq; subst. exact Hshape.
Qed.

Lemma qsubR_qual_empty : forall S T,
  qsubR empty S T ->
  forall Qs Ts Qt Tt,
    S = qtyp_qtyp Qs Ts -> T = qtyp_qtyp Qt Tt ->
    wf_qua empty Qs -> subqual empty Qs Qt.
Proof.
  intros S T H. induction H as [R|S0 R U H0 IH Hstep];
    intros Qs Ts Qt Tt HS HT Hwf.
  - inversion HS; subst. inversion HT; subst.
    apply subqual_refl; [apply wf_env_empty|exact Hwf].
  - destruct R as [QT TT]. inversion Hstep; subst.
    inversion H4; subst.
    eapply subqual_trans_env; [apply wf_env_empty| |exact H3].
    eapply IH; [reflexivity|reflexivity|exact Hwf].
Qed.

Lemma abs_qsub_shape : forall Q Qs V b Qt T0,
  typing empty Q (exp_abs Qs V b) (qtyp_qtyp Qt T0) ->
  exists Ts, qsubR empty (qtyp_qtyp Qs Ts) (qtyp_qtyp Qt T0) /\ tshape_of Ts = tArrow.
Proof.
  intros Q Qs V b Qt T0 Hty.
  destruct (syn_typing_abs_inv empty Q (exp_abs Qs V b) (qtyp_qtyp Qt T0) Hty Qs V b eq_refl)
    as [L [V' [T1 [Hbody [Hqual Hq]]]]].
  exists (typ_arrow V' T1). split; [exact Hq|reflexivity].
Qed.
Lemma tabs_qsub_shape : forall Q Qs V b Qt T0,
  typing empty Q (exp_tabs Qs V b) (qtyp_qtyp Qt T0) ->
  exists Ts, qsubR empty (qtyp_qtyp Qs Ts) (qtyp_qtyp Qt T0) /\ tshape_of Ts = tAll.
Proof.
  intros Q Qs V b Qt T0 Hty.
  destruct (syn_typing_tabs_inv empty Q (exp_tabs Qs V b) (qtyp_qtyp Qt T0) Hty Qs V b eq_refl)
    as [L [V' [T1 [Hbody [Hqual Hq]]]]].
  exists (typ_all V' T1). split; [exact Hq|reflexivity].
Qed.
Lemma qabs_qsub_shape : forall Q Qs Qb b Qt T0,
  typing empty Q (exp_qabs Qs Qb b) (qtyp_qtyp Qt T0) ->
  exists Ts, qsubR empty (qtyp_qtyp Qs Ts) (qtyp_qtyp Qt T0) /\ tshape_of Ts = tQall.
Proof.
  intros Q Qs Qb b Qt T0 Hty.
  destruct (syn_typing_qabs_inv empty Q (exp_qabs Qs Qb b) (qtyp_qtyp Qt T0) Hty Qs Qb b eq_refl)
    as [L [Q0 [T1 [Hwf [Hbody [Hqual Hq]]]]]].
  exists (typ_qall Q0 T1). split; [exact Hq|reflexivity].
Qed.
Lemma inl_qsub_shape : forall Q Qs v1 Qt T0,
  typing empty Q (exp_inl Qs v1) (qtyp_qtyp Qt T0) ->
  exists Ts, qsubR empty (qtyp_qtyp Qs Ts) (qtyp_qtyp Qt T0) /\ tshape_of Ts = tSum.
Proof.
  intros Q Qs v1 Qt T0 Hty.
  destruct (syn_typing_inl_inv empty Q (exp_inl Qs v1) (qtyp_qtyp Qt T0) Hty Qs v1 eq_refl)
    as [Q0 [T1 [T2 [Hv [Hwf [Hw2 [Hqual Hq]]]]]]].
  exists (typ_sum T1 T2). split; [exact Hq|reflexivity].
Qed.
Lemma inr_qsub_shape : forall Q Qs v1 Qt T0,
  typing empty Q (exp_inr Qs v1) (qtyp_qtyp Qt T0) ->
  exists Ts, qsubR empty (qtyp_qtyp Qs Ts) (qtyp_qtyp Qt T0) /\ tshape_of Ts = tSum.
Proof.
  intros Q Qs v1 Qt T0 Hty.
  destruct (syn_typing_inr_inv empty Q (exp_inr Qs v1) (qtyp_qtyp Qt T0) Hty Qs v1 eq_refl)
    as [Q0 [T1 [T2 [Hv [Hwf [Hw2 [Hqual Hq]]]]]]].
  exists (typ_sum T1 T2). split; [exact Hq|reflexivity].
Qed.
Lemma pair_qsub_shape : forall Q Qs v1 v2 Qt T0,
  typing empty Q (exp_pair Qs v1 v2) (qtyp_qtyp Qt T0) ->
  exists Ts, qsubR empty (qtyp_qtyp Qs Ts) (qtyp_qtyp Qt T0) /\ tshape_of Ts = tPair.
Proof.
  intros Q Qs v1 v2 Qt T0 Hty.
  destruct (syn_typing_pair_inv empty Q (exp_pair Qs v1 v2) (qtyp_qtyp Qt T0) Hty Qs v1 v2 eq_refl)
    as [Q0 [T1 [T2 [H1 [H2 [Hwf [Hqual Hq]]]]]]].
  exists (typ_pair T1 T2). split; [exact Hq|reflexivity].
Qed.

Lemma typing_abs_qual_empty : forall Q Qs V b Qt T0,
  typing empty Q (exp_abs Qs V b) (qtyp_qtyp Qt T0) ->
  wf_qua empty Qs /\ subqual empty Qs Qt.
Proof.
  intros Q Qs V b Qt T0 Hty.
  destruct (syn_typing_abs_inv empty Q (exp_abs Qs V b) (qtyp_qtyp Qt T0) Hty Qs V b eq_refl)
    as [L [V' [T1 [Hbody [Hqual Hq]]]]].
  pick fresh z. assert (Hz : z `notin` L) by fsetdec.
  pose proof (typing_wf_env _ _ _ _ (Hbody z Hz)) as HwfE.
  pose proof (typing_wf_qua _ _ _ _ HwfE (Hbody z Hz)) as Hwq.
  destruct (wf_env_cons_inv z (bind_typ V') empty HwfE) as [HE _].
  split.
  - apply wf_qua_bind_typ_inv with (x := z) (V := V'). exact Hwq.
  - eapply (qsubR_qual_empty _ _ Hq Qs (typ_arrow V' T1) Qt T0);
    [reflexivity|reflexivity|apply wf_qua_bind_typ_inv with (x := z) (V := V'); exact Hwq].
Qed.

Lemma typing_tabs_qual_empty : forall Q Qs V b Qt T0,
  typing empty Q (exp_tabs Qs V b) (qtyp_qtyp Qt T0) ->
  wf_qua empty Qs /\ subqual empty Qs Qt.
Proof.
  intros Q Qs V b Qt T0 Hty.
  destruct (syn_typing_tabs_inv empty Q (exp_tabs Qs V b) (qtyp_qtyp Qt T0) Hty Qs V b eq_refl)
    as [L [V' [T1 [Hbody [Hqual Hq]]]]].
  pick fresh z. assert (Hz : z `notin` L) by fsetdec.
  pose proof (typing_wf_env _ _ _ _ (Hbody z Hz)) as HwfE.
  pose proof (typing_wf_qua _ _ _ _ HwfE (Hbody z Hz)) as Hwq.
  destruct (wf_env_cons_inv z (bind_sub V') empty HwfE) as [HE _].
  split.
  - apply wf_qua_bind_sub_inv with (x := z) (V := V'). exact Hwq.
  - eapply (qsubR_qual_empty _ _ Hq Qs (typ_all V' T1) Qt T0);
    [reflexivity|reflexivity|apply wf_qua_bind_sub_inv with (x := z) (V := V'); exact Hwq].
Qed.

Lemma typing_qabs_qual_empty : forall Q Qs Qb b Qt T0,
  typing empty Q (exp_qabs Qs Qb b) (qtyp_qtyp Qt T0) ->
  wf_qua empty Qs /\ subqual empty Qs Qt.
Proof.
  intros Q Qs Qb b Qt T0 Hty.
  destruct (syn_typing_qabs_inv empty Q (exp_qabs Qs Qb b) (qtyp_qtyp Qt T0) Hty Qs Qb b eq_refl)
    as [L [Q0 [T1 [Hwf [Hbody [Hqual Hq]]]]]].
  split; [exact Hwf|].
  eapply (qsubR_qual_empty _ _ Hq Qs (typ_qall Q0 T1) Qt T0);
    [reflexivity|reflexivity|exact Hwf].
Qed.

Lemma typing_inl_qual_empty : forall Q Qs v1 Qt T0,
  typing empty Q (exp_inl Qs v1) (qtyp_qtyp Qt T0) ->
  wf_qua empty Qs /\ subqual empty Qs Qt.
Proof.
  intros Q Qs v1 Qt T0 Hty.
  destruct (syn_typing_inl_inv empty Q (exp_inl Qs v1) (qtyp_qtyp Qt T0) Hty Qs v1 eq_refl)
    as [Q0 [T1 [T2 [Hv [Hwf [Hw2 [Hqual Hq]]]]]]].
  split; [exact Hwf|].
  eapply (qsubR_qual_empty _ _ Hq Qs (typ_sum T1 T2) Qt T0);
    [reflexivity|reflexivity|exact Hwf].
Qed.
Lemma typing_inr_qual_empty : forall Q Qs v1 Qt T0,
  typing empty Q (exp_inr Qs v1) (qtyp_qtyp Qt T0) ->
  wf_qua empty Qs /\ subqual empty Qs Qt.
Proof.
  intros Q Qs v1 Qt T0 Hty.
  destruct (syn_typing_inr_inv empty Q (exp_inr Qs v1) (qtyp_qtyp Qt T0) Hty Qs v1 eq_refl)
    as [Q0 [T1 [T2 [Hv [Hwf [Hw2 [Hqual Hq]]]]]]].
  split; [exact Hwf|].
  eapply (qsubR_qual_empty _ _ Hq Qs (typ_sum T1 T2) Qt T0);
    [reflexivity|reflexivity|exact Hwf].
Qed.
Lemma typing_pair_qual_empty : forall Q Qs v1 v2 Qt T0,
  typing empty Q (exp_pair Qs v1 v2) (qtyp_qtyp Qt T0) ->
  wf_qua empty Qs /\ subqual empty Qs Qt.
Proof.
  intros Q Qs v1 v2 Qt T0 Hty.
  destruct (syn_typing_pair_inv empty Q (exp_pair Qs v1 v2) (qtyp_qtyp Qt T0) Hty Qs v1 v2 eq_refl)
    as [Q0 [T1 [T2 [H1 [H2 [Hwf [Hqual Hq]]]]]]].
  split; [exact Hwf|].
  eapply (qsubR_qual_empty _ _ Hq Qs (typ_pair T1 T2) Qt T0);
    [reflexivity|reflexivity|exact Hwf].
Qed.

End Hyp.


(* ===== inlined from /tmp/w1/CtxSyn.v ===== *)

Lemma w1_typing_ctx_tabs_inv_syn : forall E Q c T,
  typing_ctx E Q c T ->
  forall Varg k, c = frame_tabs Varg :: k ->
  exists Q0 T1 T2 L,
    typing_ctx E Q0 k (open_tqt T2 Varg) /\
    sub E Varg T1 /\
    (forall X : atom, X `notin` L -> wf_qtyp (X ~ bind_sub T1 ++ E) (open_tqt T2 X)) /\
    qualL E Q Q0 /\
    qsubL E T (qtyp_qtyp Q0 (typ_all T1 T2)).
Proof.
  intros E Q c T Hty. dependent induction Hty; intros Varg k Heq; try discriminate Heq.
  - inversion Heq; subst. repeat eexists; repeat match goal with |- _ /\ _ => split end; eauto 10; try apply qualL_refl; try apply qsubL_refl.
  - inversion Heq; subst.
    destruct (IHHty Varg k eq_refl) as [Q0 [T1 [T2 [L [Hk [Hs [Hwf [Hq Hs2]]]]]]]].
    exists Q0, T1, T2, L. repeat match goal with |- _ /\ _ => split end; eauto.
    eapply qsubL_step; [eassumption|exact Hs2].
  - inversion Heq; subst.
    destruct (IHHty Varg k eq_refl) as [Q0 [T1 [T2 [L [Hk [Hs [Hwf [Hq Hs2]]]]]]]].
    exists Q0, T1, T2, L. repeat match goal with |- _ /\ _ => split end; eauto.
    eapply qualL_step; [eassumption|exact Hq].
Qed.

Lemma w1_typing_ctx_qabs_inv_syn : forall E Q c T,
  typing_ctx E Q c T ->
  forall Rarg k, c = frame_qabs Rarg :: k ->
  exists Q0 R0 T2 L,
    typing_ctx E Q0 k (open_qqt T2 Rarg) /\
    subqual E Rarg R0 /\
    (forall X : atom, X `notin` L -> wf_qtyp (X ~ bind_qua R0 ++ E) (open_qqt T2 X)) /\
    qualL E Q Q0 /\
    qsubL E T (qtyp_qtyp Q0 (typ_qall R0 T2)).
Proof.
  intros E Q c T Hty. dependent induction Hty; intros Rarg k Heq; try discriminate Heq.
  - inversion Heq; subst. repeat eexists; repeat match goal with |- _ /\ _ => split end; eauto 10; try apply qualL_refl; try apply qsubL_refl.
  - inversion Heq; subst.
    destruct (IHHty Rarg k eq_refl) as (Q0 & R0 & T2 & L & Hk & Hs & Hwf & Hq & Hs2).
    exists Q0, R0, T2, L. repeat match goal with |- _ /\ _ => split end; eauto.
    eapply qsubL_step; [eassumption|exact Hs2].
  - inversion Heq; subst.
    destruct (IHHty Rarg k eq_refl) as (Q0 & R0 & T2 & L & Hk & Hs & Hwf & Hq & Hs2).
    exists Q0, R0, T2, L. repeat match goal with |- _ /\ _ => split end; eauto.
    eapply qualL_step; [eassumption|exact Hq].
Qed.

Lemma w1_typing_ctx_upqual_inv_syn : forall E Q c T,
  typing_ctx E Q c T ->
  forall Parg k, c = frame_upqual Parg :: k ->
  exists Q0 T0,
    typing_ctx E Q0 k (qtyp_qtyp Parg T0) /\
    qualL E Q Q0 /\
    qsubL E T (qtyp_qtyp Parg T0).
Proof.
  intros E Q c T Hty. dependent induction Hty; intros Parg k Heq; try discriminate Heq.
  - inversion Heq; subst. repeat eexists; repeat match goal with |- _ /\ _ => split end; eauto 10; try apply qualL_refl; try apply qsubL_refl.
  - inversion Heq; subst.
    destruct (IHHty Parg k eq_refl) as [Q0 [T0 [Hk [Hq Hs]]]].
    exists Q0, T0. repeat match goal with |- _ /\ _ => split end; eauto.
    eapply qsubL_step; [eassumption|exact Hs].
  - inversion Heq; subst.
    destruct (IHHty Parg k eq_refl) as [Q0 [T0 [Hk [Hq Hs]]]].
    exists Q0, T0. repeat match goal with |- _ /\ _ => split end; eauto.
    eapply qualL_step; [eassumption|exact Hq].
Qed.

Lemma w1_typing_ctx_check_inv_syn : forall E Q c T,
  typing_ctx E Q c T ->
  forall Rarg k, c = frame_check Rarg :: k ->
  exists Q0 P T0,
    wf_qua E Rarg /\
    typing_ctx E Q0 k (qtyp_qtyp P T0) /\
    qualL E Q Q0 /\
    qsubL E T (qtyp_qtyp (qua_meet P Rarg) T0).
Proof.
  intros E Q c T Hty. dependent induction Hty; intros Rarg k Heq; try discriminate Heq.
  - inversion Heq; subst. repeat eexists; repeat match goal with |- _ /\ _ => split end; eauto 10; try apply qualL_refl; try apply qsubL_refl.
  - inversion Heq; subst.
    destruct (IHHty Rarg k eq_refl) as [Q0 [P [T0 [Hwf [Hk [Hq Hs]]]]]].
    exists Q0, P, T0. repeat match goal with |- _ /\ _ => split end; eauto.
    eapply qsubL_step; [eassumption|exact Hs].
  - inversion Heq; subst.
    destruct (IHHty Rarg k eq_refl) as [Q0 [P [T0 [Hwf [Hk [Hq Hs]]]]]].
    exists Q0, P, T0. repeat match goal with |- _ /\ _ => split end; eauto.
    eapply qualL_step; [eassumption|exact Hq].
Qed.


(* ===== inlined from /tmp/w1/Progress2.v ===== *)

Lemma expr_bvar_false : forall i, expr (exp_bvar i) -> False.
Proof. intros i H. remember (exp_bvar i) as e eqn:E. induction H; discriminate E. Qed.
Lemma expr_ref_false : forall q e, expr (exp_ref q e) -> False.
Proof. intros q e H. remember (exp_ref q e) as ee eqn:E. induction H; discriminate E. Qed.
Lemma expr_ref_label_false : forall q l, expr (exp_ref_label q l) -> False.
Proof. intros q l H. remember (exp_ref_label q l) as ee eqn:E. induction H; discriminate E. Qed.
Lemma expr_deref_false : forall e, expr (exp_deref e) -> False.
Proof. intros e H. remember (exp_deref e) as ee eqn:E. induction H; discriminate E. Qed.
Lemma expr_set_ref_false : forall e1 e2, expr (exp_set_ref e1 e2) -> False.
Proof. intros e1 e2 H. remember (exp_set_ref e1 e2) as ee eqn:E. induction H; discriminate E. Qed.
Lemma typing_empty_bvar : forall Q i T, typing empty Q (exp_bvar i) T -> False.
Proof. intros Q i T H. exact (expr_bvar_false i (typing_expr empty Q (exp_bvar i) T H)). Qed.
Lemma typing_empty_fvar : forall Q x T, typing empty Q (exp_fvar x) T -> False.
Proof.
  intros Q x T H. dependent induction H.
  - destruct H0.
  - eapply IHtyping; reflexivity.
  - eapply IHtyping; reflexivity.
Qed.

Section Hyp.
Context (subqual_trans_env : forall E Q R S,
  wf_env E -> subqual E Q R -> subqual E R S -> subqual E Q S).

Ltac shape_bad Hq Hsh :=
  exfalso;
  match type of Hq with
  | qsubR empty (qtyp_qtyp ?Qs ?Ts) (qtyp_qtyp ?Qt ?Tt) =>
      let Hs := fresh "Hs" in
      assert (Hs : tshape_of Ts = tshape_of Tt) by
        (eapply qsubR_tshape_eq; [exact Hq | simpl; discriminate]);
      rewrite Hsh in Hs; simpl in Hs; discriminate Hs
  end.

Lemma progress_app_frame : forall e f k Q T,
  value e -> typing_ctx empty Q (frame_app f :: k) T ->
  exists s', step 〈 e | frame_app f :: k 〉 s'.
Proof.
  intros e f k Q T Hv Hctx.
  destruct (typing_ctx_app_inv empty Q (frame_app f :: k) T Hctx f k eq_refl)
    as [Q0 [A [B [Hk [Hvf [Hfty Hqualq]]]]]].
  destruct Hqualq as [Hqual Hqsub].
  destruct f as [i | a | P V b | f1 f2 | P V b | f1 V | P Qb b | f1 Qa
                | f1 f2 | P f1 | P f1 | f1 f2 f3 | P f1 f2 | f1 | f1
                | P f1 | P l | f1 | f1 f2 | P f1 | P f1].
  - exfalso; inversion Hvf.
  - exfalso; inversion Hvf.
  - (* abs *) simpl in Hfty.
    destruct (typing_abs_qual_empty subqual_trans_env Q0 P V b Q0 (typ_arrow A B) Hfty)
      as [Hwf Hsq].
    destruct (wf_qua_empty_concretize P Hwf) as [t Hconc].
    assert (Hbar : barrier_compatible k t).
    { eapply (typing_ctx_barrier_invariant subqual_trans_env); [exact Hk|apply wf_env_empty| exact Hsq|exact Hconc]. }
    exists 〈 open_ee b e | frame_barrier t :: k 〉.
    eapply step_app_abs; [exact Hv|exact Hconc|exact Hbar].
  - exfalso; inversion Hvf.
  - (* tabs *) simpl in Hfty.
    destruct (tabs_qsub_shape Q0 P V b Q0 (typ_arrow A B) Hfty)
      as [Ts [Hq Hsh]].
    shape_bad Hq Hsh.
  - exfalso; inversion Hvf.
  - (* qabs *) simpl in Hfty.
    destruct (qabs_qsub_shape Q0 P Qb b Q0 (typ_arrow A B) Hfty)
      as [Ts [Hq Hsh]].
    shape_bad Hq Hsh.
  - exfalso; inversion Hvf.
  - exfalso; inversion Hvf.
  - (* inl *) simpl in Hfty.
    destruct (inl_qsub_shape Q0 P f1 Q0 (typ_arrow A B) Hfty)
      as [Ts [Hq Hsh]].
    shape_bad Hq Hsh.
  - (* inr *) simpl in Hfty.
    destruct (inr_qsub_shape Q0 P f1 Q0 (typ_arrow A B) Hfty)
      as [Ts [Hq Hsh]].
    shape_bad Hq Hsh.
  - exfalso; inversion Hvf.
  - (* pair *) simpl in Hfty.
    destruct (pair_qsub_shape Q0 P f1 f2 Q0 (typ_arrow A B) Hfty)
      as [Ts [Hq Hsh]].
    shape_bad Hq Hsh.
  - exfalso; inversion Hvf.
  - exfalso; inversion Hvf.
  - exfalso; inversion Hvf.
  - exfalso; inversion Hvf.
  - exfalso; inversion Hvf.
  - exfalso; inversion Hvf.
  - exfalso; inversion Hvf.
  - exfalso; inversion Hvf.
Qed.

Lemma progress_abs_ctx : forall (P : qua) (V : qtyp) (b : exp) Q T,
  typing empty Q (exp_abs P V b) T ->
  forall c, typing_ctx empty Q c T ->
  done_state 〈 exp_abs P V b | c 〉 \/ exists s', step 〈 exp_abs P V b | c 〉 s'.
Proof.
  intros P V b Q T Hty c Hctx.
  assert (Hv : value (exp_abs P V b)).
  { apply value_abs. apply (typing_expr empty Q (exp_abs P V b) T). assumption. }
  destruct c as [|f k].
  - left. apply done_value. exact Hv.
  - destruct f as [earg | farg | Varg | Rarg | earg | Parg | Parg | e2arg e3arg | Parg earg | Parg varg | | | Parg | Parg | sarg].
    + (* frame_abs *) right. exists 〈 earg | frame_app (exp_abs P V b) :: k 〉.
      apply step_app_2. exact Hv.
    + (* frame_app *) right. eapply progress_app_frame; eassumption.
    + (* frame_tabs *) right.
      destruct (w1_typing_ctx_tabs_inv_syn empty Q (frame_tabs Varg :: k) T Hctx Varg k eq_refl)
        as [Q0 [T1 [T2 [L [Hk [Hsub [Hwf [Hqual Hqsub]]]]]]]].
      assert (Hty2 : typing empty Q (exp_abs P V b) (qtyp_qtyp Q0 (typ_all T1 T2))).
      { eapply typing_forward_qsubL; eassumption. }
      destruct (abs_qsub_shape Q P V b Q0 (typ_all T1 T2) Hty2) as [Ts [Hq Hsh]].
      shape_bad Hq Hsh.
    + (* frame_qabs *) right.
      destruct (w1_typing_ctx_qabs_inv_syn empty Q (frame_qabs Rarg :: k) T Hctx Rarg k eq_refl)
        as [Q0 [R0 [T2 [L [Hk [Hsub [Hwf [Hqual Hqsub]]]]]]]].
      assert (Hty2 : typing empty Q (exp_abs P V b) (qtyp_qtyp Q0 (typ_qall R0 T2))).
      { eapply typing_forward_qsubL; eassumption. }
      destruct (abs_qsub_shape Q P V b Q0 (typ_qall R0 T2) Hty2) as [Ts [Hq Hsh]].
      shape_bad Hq Hsh.
    + (* frame_let *) right. exists 〈 open_ee earg (exp_abs P V b) | k 〉. apply step_let_value. exact Hv.
    + (* frame_inl *) right. exists 〈 exp_inl Parg (exp_abs P V b) | k 〉.
      apply step_make_inl. exact Hv.
    + (* frame_inr *) right. exists 〈 exp_inr Parg (exp_abs P V b) | k 〉.
      apply step_make_inr. exact Hv.
    + (* frame_case *) right.
      destruct (typing_ctx_case_inv empty Q (frame_case e2arg e3arg :: k) T Hctx e2arg e3arg k eq_refl)
        as [Q0 [P0 [Tbody [T1 [T2 [L [Hwf [Hk [Hb1 [Hb2 [Hqual Hqsub]]]]]]]]]]].
      assert (Hty2 : typing empty Q (exp_abs P V b) (qtyp_qtyp P0 (typ_sum T1 T2))).
      { eapply typing_forward_qsubL; eassumption. }
      destruct (abs_qsub_shape Q P V b P0 (typ_sum T1 T2) Hty2) as [Ts [Hq Hsh]].
      shape_bad Hq Hsh.
    + (* frame_pair_1 *) right. exists 〈 earg | frame_pair_2 Parg (exp_abs P V b) :: k 〉.
      apply step_pair_2. exact Hv.
    + (* frame_pair_2 *) right.
      destruct (typing_ctx_pair_2_inv empty Q (frame_pair_2 Parg varg :: k) T Hctx Parg varg k eq_refl)
        as [Q0 [P0 [T1 [T2 [Hwf [Hk [Hve [Hte [Hqual Hqsub]]]]]]]]].
      exists 〈 exp_pair Parg varg (exp_abs P V b) | k 〉.
      eapply step_make_pair; [exact Hv|exact Hve].
    + (* frame_first *) right.
      destruct (typing_ctx_first_inv empty Q (frame_first :: k) T Hctx k eq_refl)
        as [Q0 [P0 [T1 [T2 [Hwf [Hk [Hwt [Hqual Hqsub]]]]]]]].
      assert (Hty2 : typing empty Q (exp_abs P V b) (qtyp_qtyp P0 (typ_pair T1 T2))).
      { eapply typing_forward_qsubL; eassumption. }
      destruct (abs_qsub_shape Q P V b P0 (typ_pair T1 T2) Hty2) as [Ts [Hq Hsh]].
      shape_bad Hq Hsh.
    + (* frame_second *) right.
      destruct (typing_ctx_second_inv empty Q (frame_second :: k) T Hctx k eq_refl)
        as [Q0 [P0 [T1 [T2 [Hwf [Hk [Hwt [Hqual Hqsub]]]]]]]].
      assert (Hty2 : typing empty Q (exp_abs P V b) (qtyp_qtyp P0 (typ_pair T1 T2))).
      { eapply typing_forward_qsubL; eassumption. }
      destruct (abs_qsub_shape Q P V b P0 (typ_pair T1 T2) Hty2) as [Ts [Hq Hsh]].
      shape_bad Hq Hsh.
    + (* frame_upqual *) right.
      destruct (w1_typing_ctx_upqual_inv_syn empty Q (frame_upqual Parg :: k) T Hctx Parg k eq_refl)
        as [Q0 [T0 [Hk [Hqual Hqsub]]]].
      assert (Hty2 : typing empty Q (exp_abs P V b) (qtyp_qtyp Parg T0)).
      { eapply typing_forward_qsubL; eassumption. }
      destruct (typing_abs_qual_empty subqual_trans_env Q P V b Parg T0 Hty2) as [HwfP Hsq].
      assert (Hwfq : wf_qua empty Parg).
      { apply (proj2 (subqual_wf empty P Parg wf_env_empty Hsq)). }
      destruct (wf_qua_empty_concretize P HwfP) as [cP HcP].
      destruct (wf_qua_empty_concretize Parg Hwfq) as [cq Hcq].
      assert (Hcompat : cqua_compatible cP cq).
      { eapply (subqual_concretize subqual_trans_env); [apply wf_env_empty|exact Hsq|exact HcP|exact Hcq]. }
      exists 〈 exp_abs Parg V b | k 〉.
      eapply step_upqual_abs; [exact Hcq|exact HcP|exact Hcompat].
    + (* frame_check *) right.
      destruct (w1_typing_ctx_check_inv_syn empty Q (frame_check Parg :: k) T Hctx Parg k eq_refl)
        as [Q0 [P0 [T0 [Hwfq [Hk [Hqual Hqsub]]]]]].
      assert (Hty2 : typing empty Q (exp_abs P V b) (qtyp_qtyp (qua_meet P0 Parg) T0)).
      { eapply typing_forward_qsubL; eassumption. }
      destruct (typing_abs_qual_empty subqual_trans_env Q P V b (qua_meet P0 Parg) T0 Hty2)
        as [HwfP Hsq].
      assert (Hwfm : wf_qua empty (qua_meet P0 Parg)).
      { apply (proj2 (subqual_wf empty P (qua_meet P0 Parg) wf_env_empty Hsq)). }
      assert (HwfP0 : wf_qua empty P0) by (inversion Hwfm; assumption).
      assert (Hsqm : subqual empty (qua_meet P0 Parg) Parg).
      { eapply subqual_meet_elimr; [exact HwfP0|apply subqual_refl; [apply wf_env_empty|exact Hwfq]]. }
      assert (Hsq2 : subqual empty P Parg).
      { eapply (subqual_trans_env empty); [apply wf_env_empty|exact Hsq|exact Hsqm]. }
      destruct (wf_qua_empty_concretize P HwfP) as [cP HcP].
      destruct (wf_qua_empty_concretize Parg Hwfq) as [cq Hcq].
      destruct (wf_qua_empty_concretize (qua_meet P0 Parg) Hwfm) as [cm Hcm].
      assert (Hcmq : cqua_compatible cm cq).
      { eapply (subqual_concretize subqual_trans_env); [apply wf_env_empty|exact Hsqm|exact Hcm|exact Hcq]. }
      assert (Hcompat : cqua_compatible cP cq).
      { eapply cqua_compatible_trans with (t := cm); [|exact Hcmq].
        eapply (subqual_concretize subqual_trans_env); [apply wf_env_empty|exact Hsq|exact HcP|exact Hcm]. }
      exists 〈 exp_abs P V b | k 〉.
      eapply step_check_abs; [exact Hcq|exact HcP|exact Hcompat].
    + (* frame_barrier *) right. exists 〈 exp_abs P V b | k 〉.
      apply step_barrier. exact Hv.
Qed.

Lemma progress_tabs_ctx : forall (P : qua) (V : typ) (b : exp) Q T,
  typing empty Q (exp_tabs P V b) T ->
  forall c, typing_ctx empty Q c T ->
  done_state 〈 exp_tabs P V b | c 〉 \/ exists s', step 〈 exp_tabs P V b | c 〉 s'.
Proof.
  intros P V b Q T Hty c Hctx.
  assert (Hv : value (exp_tabs P V b)).
  { apply value_tabs. apply (typing_expr empty Q (exp_tabs P V b) T). assumption. }
  destruct c as [|f k].
  - left. apply done_value. exact Hv.
  - destruct f as [earg | farg | Varg | Rarg | earg | Parg | Parg | e2arg e3arg | Parg earg | Parg varg | | | Parg | Parg | sarg].
    + (* frame_abs *) right. exists 〈 earg | frame_app (exp_tabs P V b) :: k 〉.
      apply step_app_2. exact Hv.
    + (* frame_app *) right. eapply progress_app_frame; eassumption.
    + (* frame_tabs *) right.
      destruct (w1_typing_ctx_tabs_inv_syn empty Q (frame_tabs Varg :: k) T Hctx Varg k eq_refl)
        as [Q0 [T1 [T2 [L [Hk [Hsub [Hwf [Hqual Hqsub]]]]]]]].
      assert (Hty2 : typing empty Q (exp_tabs P V b) (qtyp_qtyp Q0 (typ_all T1 T2))).
      { eapply typing_forward_qsubL; eassumption. }
      destruct (typing_tabs_qual_empty subqual_trans_env Q P V b Q0 (typ_all T1 T2) Hty2)
        as [HwfP Hsq].
      assert (HtypeV : type Varg) by (apply (proj1 (sub_type empty Varg T1 Hsub))).
      destruct (wf_qua_empty_concretize P HwfP) as [t Hconc].
      assert (Hbar : barrier_compatible k t).
      { eapply (typing_ctx_barrier_invariant subqual_trans_env); [exact Hk|apply wf_env_empty|exact Hsq|exact Hconc]. }
      exists 〈 open_te b Varg | frame_barrier t :: k 〉.
      eapply step_app_tabs; [exact HtypeV|exact Hconc|exact Hbar].
    + (* frame_qabs *) right.
      destruct (w1_typing_ctx_qabs_inv_syn empty Q (frame_qabs Rarg :: k) T Hctx Rarg k eq_refl)
        as [Q0 [R0 [T2 [L [Hk [Hsub [Hwf [Hqual Hqsub]]]]]]]].
      assert (Hty2 : typing empty Q (exp_tabs P V b) (qtyp_qtyp Q0 (typ_qall R0 T2))).
      { eapply typing_forward_qsubL; eassumption. }
      destruct (tabs_qsub_shape Q P V b Q0 (typ_qall R0 T2) Hty2) as [Ts [Hq Hsh]].
      shape_bad Hq Hsh.
    + (* frame_let *) right. exists 〈 open_ee earg (exp_tabs P V b) | k 〉. apply step_let_value. exact Hv.
    + (* frame_inl *) right. exists 〈 exp_inl Parg (exp_tabs P V b) | k 〉.
      apply step_make_inl. exact Hv.
    + (* frame_inr *) right. exists 〈 exp_inr Parg (exp_tabs P V b) | k 〉.
      apply step_make_inr. exact Hv.
    + (* frame_case *) right.
      destruct (typing_ctx_case_inv empty Q (frame_case e2arg e3arg :: k) T Hctx e2arg e3arg k eq_refl)
        as [Q0 [P0 [Tbody [T1 [T2 [L [Hwf [Hk [Hb1 [Hb2 [Hqual Hqsub]]]]]]]]]]].
      assert (Hty2 : typing empty Q (exp_tabs P V b) (qtyp_qtyp P0 (typ_sum T1 T2))).
      { eapply typing_forward_qsubL; eassumption. }
      destruct (tabs_qsub_shape Q P V b P0 (typ_sum T1 T2) Hty2) as [Ts [Hq Hsh]].
      shape_bad Hq Hsh.
    + (* frame_pair_1 *) right. exists 〈 earg | frame_pair_2 Parg (exp_tabs P V b) :: k 〉.
      apply step_pair_2. exact Hv.
    + (* frame_pair_2 *) right.
      destruct (typing_ctx_pair_2_inv empty Q (frame_pair_2 Parg varg :: k) T Hctx Parg varg k eq_refl)
        as [Q0 [P0 [T1 [T2 [Hwf [Hk [Hve [Hte [Hqual Hqsub]]]]]]]]].
      exists 〈 exp_pair Parg varg (exp_tabs P V b) | k 〉.
      eapply step_make_pair; [exact Hv|exact Hve].
    + (* frame_first *) right.
      destruct (typing_ctx_first_inv empty Q (frame_first :: k) T Hctx k eq_refl)
        as [Q0 [P0 [T1 [T2 [Hwf [Hk [Hwt [Hqual Hqsub]]]]]]]].
      assert (Hty2 : typing empty Q (exp_tabs P V b) (qtyp_qtyp P0 (typ_pair T1 T2))).
      { eapply typing_forward_qsubL; eassumption. }
      destruct (tabs_qsub_shape Q P V b P0 (typ_pair T1 T2) Hty2) as [Ts [Hq Hsh]].
      shape_bad Hq Hsh.
    + (* frame_second *) right.
      destruct (typing_ctx_second_inv empty Q (frame_second :: k) T Hctx k eq_refl)
        as [Q0 [P0 [T1 [T2 [Hwf [Hk [Hwt [Hqual Hqsub]]]]]]]].
      assert (Hty2 : typing empty Q (exp_tabs P V b) (qtyp_qtyp P0 (typ_pair T1 T2))).
      { eapply typing_forward_qsubL; eassumption. }
      destruct (tabs_qsub_shape Q P V b P0 (typ_pair T1 T2) Hty2) as [Ts [Hq Hsh]].
      shape_bad Hq Hsh.
    + (* frame_upqual *) right.
      destruct (w1_typing_ctx_upqual_inv_syn empty Q (frame_upqual Parg :: k) T Hctx Parg k eq_refl)
        as [Q0 [T0 [Hk [Hqual Hqsub]]]].
      assert (Hty2 : typing empty Q (exp_tabs P V b) (qtyp_qtyp Parg T0)).
      { eapply typing_forward_qsubL; eassumption. }
      destruct (typing_tabs_qual_empty subqual_trans_env Q P V b Parg T0 Hty2) as [HwfP Hsq].
      assert (Hwfq : wf_qua empty Parg).
      { apply (proj2 (subqual_wf empty P Parg wf_env_empty Hsq)). }
      destruct (wf_qua_empty_concretize P HwfP) as [cP HcP].
      destruct (wf_qua_empty_concretize Parg Hwfq) as [cq Hcq].
      assert (Hcompat : cqua_compatible cP cq).
      { eapply (subqual_concretize subqual_trans_env); [apply wf_env_empty|exact Hsq|exact HcP|exact Hcq]. }
      exists 〈 exp_tabs Parg V b | k 〉.
      eapply step_upqual_tabs; [exact Hcq|exact HcP|exact Hcompat].
    + (* frame_check *) right.
      destruct (w1_typing_ctx_check_inv_syn empty Q (frame_check Parg :: k) T Hctx Parg k eq_refl)
        as [Q0 [P0 [T0 [Hwfq [Hk [Hqual Hqsub]]]]]].
      assert (Hty2 : typing empty Q (exp_tabs P V b) (qtyp_qtyp (qua_meet P0 Parg) T0)).
      { eapply typing_forward_qsubL; eassumption. }
      destruct (typing_tabs_qual_empty subqual_trans_env Q P V b (qua_meet P0 Parg) T0 Hty2)
        as [HwfP Hsq].
      assert (Hwfm : wf_qua empty (qua_meet P0 Parg)).
      { apply (proj2 (subqual_wf empty P (qua_meet P0 Parg) wf_env_empty Hsq)). }
      assert (HwfP0 : wf_qua empty P0) by (inversion Hwfm; assumption).
      assert (Hsqm : subqual empty (qua_meet P0 Parg) Parg).
      { eapply subqual_meet_elimr; [exact HwfP0|apply subqual_refl; [apply wf_env_empty|exact Hwfq]]. }
      assert (Hsq2 : subqual empty P Parg).
      { eapply (subqual_trans_env empty); [apply wf_env_empty|exact Hsq|exact Hsqm]. }
      destruct (wf_qua_empty_concretize P HwfP) as [cP HcP].
      destruct (wf_qua_empty_concretize Parg Hwfq) as [cq Hcq].
      destruct (wf_qua_empty_concretize (qua_meet P0 Parg) Hwfm) as [cm Hcm].
      assert (Hcmq : cqua_compatible cm cq).
      { eapply (subqual_concretize subqual_trans_env); [apply wf_env_empty|exact Hsqm|exact Hcm|exact Hcq]. }
      assert (Hcompat : cqua_compatible cP cq).
      { eapply cqua_compatible_trans with (t := cm); [|exact Hcmq].
        eapply (subqual_concretize subqual_trans_env); [apply wf_env_empty|exact Hsq|exact HcP|exact Hcm]. }
      exists 〈 exp_tabs P V b | k 〉.
      eapply step_check_tabs; [exact Hcq|exact HcP|exact Hcompat].
    + (* frame_barrier *) right. exists 〈 exp_tabs P V b | k 〉.
      apply step_barrier. exact Hv.
Qed.

Lemma progress_qabs_ctx : forall (P : qua) (V : qua) (b : exp) Q T,
  typing empty Q (exp_qabs P V b) T ->
  forall c, typing_ctx empty Q c T ->
  done_state 〈 exp_qabs P V b | c 〉 \/ exists s', step 〈 exp_qabs P V b | c 〉 s'.
Proof.
  intros P V b Q T Hty c Hctx.
  assert (Hv : value (exp_qabs P V b)).
  { apply value_qabs. apply (typing_expr empty Q (exp_qabs P V b) T). assumption. }
  destruct c as [|f k].
  - left. apply done_value. exact Hv.
  - destruct f as [earg | farg | Varg | Rarg | earg | Parg | Parg | e2arg e3arg | Parg earg | Parg varg | | | Parg | Parg | sarg].
    + (* frame_abs *) right. exists 〈 earg | frame_app (exp_qabs P V b) :: k 〉.
      apply step_app_2. exact Hv.
    + (* frame_app *) right. eapply progress_app_frame; eassumption.
    + (* frame_tabs *) right.
      destruct (w1_typing_ctx_tabs_inv_syn empty Q (frame_tabs Varg :: k) T Hctx Varg k eq_refl)
        as [Q0 [T1 [T2 [L [Hk [Hsub [Hwf [Hqual Hqsub]]]]]]]].
      assert (Hty2 : typing empty Q (exp_qabs P V b) (qtyp_qtyp Q0 (typ_all T1 T2))).
      { eapply typing_forward_qsubL; eassumption. }
      destruct (qabs_qsub_shape Q P V b Q0 (typ_all T1 T2) Hty2) as [Ts [Hq Hsh]].
      shape_bad Hq Hsh.
    + (* frame_qabs *) right.
      destruct (w1_typing_ctx_qabs_inv_syn empty Q (frame_qabs Rarg :: k) T Hctx Rarg k eq_refl)
        as [Q0 [R0 [T2 [L [Hk [Hsub [Hwf [Hqual Hqsub]]]]]]]].
      assert (Hty2 : typing empty Q (exp_qabs P V b) (qtyp_qtyp Q0 (typ_qall R0 T2))).
      { eapply typing_forward_qsubL; eassumption. }
      destruct (typing_qabs_qual_empty subqual_trans_env Q P V b Q0 (typ_qall R0 T2) Hty2)
        as [HwfP Hsq].
      assert (HqualR : qual Rarg) by (apply (proj1 (subqual_qual empty Rarg R0 Hsub))).
      destruct (wf_qua_empty_concretize P HwfP) as [t Hconc].
      assert (Hbar : barrier_compatible k t).
      { eapply (typing_ctx_barrier_invariant subqual_trans_env); [exact Hk|apply wf_env_empty|exact Hsq|exact Hconc]. }
      exists 〈 open_qe b Rarg | frame_barrier t :: k 〉.
      eapply step_app_qabs; [exact HqualR|exact Hconc|exact Hbar].
    + (* frame_let *) right. exists 〈 open_ee earg (exp_qabs P V b) | k 〉. apply step_let_value. exact Hv.
    + (* frame_inl *) right. exists 〈 exp_inl Parg (exp_qabs P V b) | k 〉.
      apply step_make_inl. exact Hv.
    + (* frame_inr *) right. exists 〈 exp_inr Parg (exp_qabs P V b) | k 〉.
      apply step_make_inr. exact Hv.
    + (* frame_case *) right.
      destruct (typing_ctx_case_inv empty Q (frame_case e2arg e3arg :: k) T Hctx e2arg e3arg k eq_refl)
        as [Q0 [P0 [Tbody [T1 [T2 [L [Hwf [Hk [Hb1 [Hb2 [Hqual Hqsub]]]]]]]]]]].
      assert (Hty2 : typing empty Q (exp_qabs P V b) (qtyp_qtyp P0 (typ_sum T1 T2))).
      { eapply typing_forward_qsubL; eassumption. }
      destruct (qabs_qsub_shape Q P V b P0 (typ_sum T1 T2) Hty2) as [Ts [Hq Hsh]].
      shape_bad Hq Hsh.
    + (* frame_pair_1 *) right. exists 〈 earg | frame_pair_2 Parg (exp_qabs P V b) :: k 〉.
      apply step_pair_2. exact Hv.
    + (* frame_pair_2 *) right.
      destruct (typing_ctx_pair_2_inv empty Q (frame_pair_2 Parg varg :: k) T Hctx Parg varg k eq_refl)
        as [Q0 [P0 [T1 [T2 [Hwf [Hk [Hve [Hte [Hqual Hqsub]]]]]]]]].
      exists 〈 exp_pair Parg varg (exp_qabs P V b) | k 〉.
      eapply step_make_pair; [exact Hv|exact Hve].
    + (* frame_first *) right.
      destruct (typing_ctx_first_inv empty Q (frame_first :: k) T Hctx k eq_refl)
        as [Q0 [P0 [T1 [T2 [Hwf [Hk [Hwt [Hqual Hqsub]]]]]]]].
      assert (Hty2 : typing empty Q (exp_qabs P V b) (qtyp_qtyp P0 (typ_pair T1 T2))).
      { eapply typing_forward_qsubL; eassumption. }
      destruct (qabs_qsub_shape Q P V b P0 (typ_pair T1 T2) Hty2) as [Ts [Hq Hsh]].
      shape_bad Hq Hsh.
    + (* frame_second *) right.
      destruct (typing_ctx_second_inv empty Q (frame_second :: k) T Hctx k eq_refl)
        as [Q0 [P0 [T1 [T2 [Hwf [Hk [Hwt [Hqual Hqsub]]]]]]]].
      assert (Hty2 : typing empty Q (exp_qabs P V b) (qtyp_qtyp P0 (typ_pair T1 T2))).
      { eapply typing_forward_qsubL; eassumption. }
      destruct (qabs_qsub_shape Q P V b P0 (typ_pair T1 T2) Hty2) as [Ts [Hq Hsh]].
      shape_bad Hq Hsh.
    + (* frame_upqual *) right.
      destruct (w1_typing_ctx_upqual_inv_syn empty Q (frame_upqual Parg :: k) T Hctx Parg k eq_refl)
        as [Q0 [T0 [Hk [Hqual Hqsub]]]].
      assert (Hty2 : typing empty Q (exp_qabs P V b) (qtyp_qtyp Parg T0)).
      { eapply typing_forward_qsubL; eassumption. }
      destruct (typing_qabs_qual_empty subqual_trans_env Q P V b Parg T0 Hty2) as [HwfP Hsq].
      assert (Hwfq : wf_qua empty Parg).
      { apply (proj2 (subqual_wf empty P Parg wf_env_empty Hsq)). }
      destruct (wf_qua_empty_concretize P HwfP) as [cP HcP].
      destruct (wf_qua_empty_concretize Parg Hwfq) as [cq Hcq].
      assert (Hcompat : cqua_compatible cP cq).
      { eapply (subqual_concretize subqual_trans_env); [apply wf_env_empty|exact Hsq|exact HcP|exact Hcq]. }
      exists 〈 exp_qabs Parg V b | k 〉.
      eapply step_upqual_qabs; [exact Hcq|exact HcP|exact Hcompat].
    + (* frame_check *) right.
      destruct (w1_typing_ctx_check_inv_syn empty Q (frame_check Parg :: k) T Hctx Parg k eq_refl)
        as [Q0 [P0 [T0 [Hwfq [Hk [Hqual Hqsub]]]]]].
      assert (Hty2 : typing empty Q (exp_qabs P V b) (qtyp_qtyp (qua_meet P0 Parg) T0)).
      { eapply typing_forward_qsubL; eassumption. }
      destruct (typing_qabs_qual_empty subqual_trans_env Q P V b (qua_meet P0 Parg) T0 Hty2)
        as [HwfP Hsq].
      assert (Hwfm : wf_qua empty (qua_meet P0 Parg)).
      { apply (proj2 (subqual_wf empty P (qua_meet P0 Parg) wf_env_empty Hsq)). }
      assert (HwfP0 : wf_qua empty P0) by (inversion Hwfm; assumption).
      assert (Hsqm : subqual empty (qua_meet P0 Parg) Parg).
      { eapply subqual_meet_elimr; [exact HwfP0|apply subqual_refl; [apply wf_env_empty|exact Hwfq]]. }
      assert (Hsq2 : subqual empty P Parg).
      { eapply (subqual_trans_env empty); [apply wf_env_empty|exact Hsq|exact Hsqm]. }
      destruct (wf_qua_empty_concretize P HwfP) as [cP HcP].
      destruct (wf_qua_empty_concretize Parg Hwfq) as [cq Hcq].
      destruct (wf_qua_empty_concretize (qua_meet P0 Parg) Hwfm) as [cm Hcm].
      assert (Hcmq : cqua_compatible cm cq).
      { eapply (subqual_concretize subqual_trans_env); [apply wf_env_empty|exact Hsqm|exact Hcm|exact Hcq]. }
      assert (Hcompat : cqua_compatible cP cq).
      { eapply cqua_compatible_trans with (t := cm); [|exact Hcmq].
        eapply (subqual_concretize subqual_trans_env); [apply wf_env_empty|exact Hsq|exact HcP|exact Hcm]. }
      exists 〈 exp_qabs P V b | k 〉.
      eapply step_check_qabs; [exact Hcq|exact HcP|exact Hcompat].
    + (* frame_barrier *) right. exists 〈 exp_qabs P V b | k 〉.
      apply step_barrier. exact Hv.
Qed.

Theorem progress_section : forall s, typing_state empty s -> done_state s \/ exists s', s --> s'.
Proof.
  intros [e c] Hts.
  inversion Hts as [E Q e0 c0 T Hty Hctx]; subst.
  destruct e as [i | a | P V b | e1 e2 | P V b | e1 V | P Qb b | e1 Qa
                | e1 e2 | P e1 | P e1 | e1 e2 e3 | P e1 e2 | e1 | e1
                | P e1 | P l | e1 | e1 e2 | P e1 | P e1].
  - exfalso. eapply typing_empty_bvar; eassumption.
  - exfalso. eapply typing_empty_fvar; eassumption.
  - (* abs *) eapply progress_abs_ctx; eassumption.
  - (* app *) right. exists 〈 e1 | frame_abs e2 :: c 〉. apply step_app_1.
  - (* tabs *) eapply progress_tabs_ctx; eassumption.
  - (* tapp *) right. exists 〈 e1 | frame_tabs V :: c 〉. apply step_tapp.
  - (* qabs *) eapply progress_qabs_ctx; eassumption.
  - (* qapp *) right. exists 〈 e1 | frame_qabs Qa :: c 〉. apply step_qapp.
  - (* let *) right. exists 〈 e1 | frame_let e2 :: c 〉. apply step_let.
  - (* inl *) right. exists 〈 e1 | frame_inl P :: c 〉. apply step_inl.
  - (* inr *) right. exists 〈 e1 | frame_inr P :: c 〉. apply step_inr.
  - (* case *) right. exists 〈 e1 | frame_case e2 e3 :: c 〉. apply step_case.
  - (* pair *) right. exists 〈 e1 | frame_pair_1 P e2 :: c 〉. apply step_pair_1.
  - (* first *) right. exists 〈 e1 | frame_first :: c 〉. apply step_first.
  - (* second *) right. exists 〈 e1 | frame_second :: c 〉. apply step_second.
  - (* ref *) exfalso. apply (expr_ref_false P e1). apply (typing_expr empty Q (exp_ref P e1) T). assumption.
  - (* ref_label *) exfalso. apply (expr_ref_label_false P l). apply (typing_expr empty Q (exp_ref_label P l) T). assumption.
  - (* deref *) exfalso. apply (expr_deref_false e1). apply (typing_expr empty Q (exp_deref e1) T). assumption.
  - (* set_ref *) exfalso. apply (expr_set_ref_false e1 e2). apply (typing_expr empty Q (exp_set_ref e1 e2) T). assumption.
  - (* upqual *) right. exists 〈 e1 | frame_upqual P :: c 〉. apply step_upqual_1.
  - (* check *) right. exists 〈 e1 | frame_check P :: c 〉. apply step_check_1.
Qed.

End Hyp.


(* ===== inlined from /tmp/w1/ProgressGlobal.v ===== *)

Definition subqual_trans_wf : forall E Q R S,
  wf_env E -> subqual E Q R -> subqual E R S -> subqual E Q S :=
  fun E Q R S Hwf H1 H2 => subqual_trans E Q R S Hwf H1 H2.

Theorem progress_final : forall s,
  typing_state empty s -> done_state s \/ exists s', s --> s'.
Proof.
  intros s H. exact (progress_section subqual_trans_wf s H).
Qed.


(* ===== inlined from /tmp/main/Components.v ===== *)

Lemma wf_qtyp_inv : forall E Q T,
  wf_qtyp E (qtyp_qtyp Q T) -> wf_qua E Q /\ wf_typ E T.
Proof. intros. inversion H; subst. auto. Qed.

Lemma subqtype_wf_target : forall E S T,
  subqtype E S T -> wf_env E -> wf_qtyp E S -> wf_qtyp E T.
Proof.
  intros E S T H Hwf HS. destruct S as [Q1 T1]; destruct T as [Q2 T2].
  inversion H; subst.
  match goal with Hq : subqual E Q1 Q2, Ht : sub E T1 T2 |- _ =>
    destruct (subqual_wf E Q1 Q2 Hwf Hq) as [_ Hq2];
    destruct (sub_wf E T1 T2 Hwf Ht) as [_ Hw2];
    apply wf_qtyp_qtyp; assumption
  end.
Qed.

Lemma qsubL_to_subqtype_wf : forall E S T,
  wf_env E -> wf_qtyp E S -> wf_qtyp E T -> qsubL E S T -> subqtype E S T.
Proof.
  intros E S T Hwf HwS HwT H. induction H as [X | S0 T0 U Hstep Htail IH].
  - (* refl *) destruct X as [Q Tx].
    destruct (wf_qtyp_inv E Q Tx HwS) as [Hq Ht].
    apply sub_qtyp_qtyp.
    + apply subqual_refl; assumption.
    + apply sub_refl_wf; assumption.
  - (* step *)
    destruct T0 as [Qm Tm].
    assert (Hwmid : wf_qtyp E (qtyp_qtyp Qm Tm))
      by (eapply subqtype_wf_target; eassumption).
    eapply subqtype_trans_size; [exact Hwf|exact Hstep|].
    apply (IH Hwmid HwT).
Qed.

Lemma subqtype_typ_components : forall E Q1 T1 Q2 T2,
  subqtype E (qtyp_qtyp Q1 T1) (qtyp_qtyp Q2 T2) ->
  subqual E Q1 Q2 /\ sub E T1 T2.
Proof. intros. inversion H; subst. auto. Qed.

Lemma qsubL_qtyp_components_wf : forall E Q1 T1 Q2 T2,
  wf_env E -> wf_qtyp E (qtyp_qtyp Q1 T1) -> wf_qtyp E (qtyp_qtyp Q2 T2) ->
  qsubL E (qtyp_qtyp Q1 T1) (qtyp_qtyp Q2 T2) ->
  subqual E Q1 Q2 /\ sub E T1 T2.
Proof.
  intros. eapply subqtype_typ_components.
  eapply qsubL_to_subqtype_wf; eassumption.
Qed.

Lemma qsubL_pair_components_wf : forall E P1 A1 B1 P2 A2 B2,
  wf_env E ->
  wf_qtyp E (qtyp_qtyp P1 (typ_pair A1 B1)) ->
  wf_qtyp E (qtyp_qtyp P2 (typ_pair A2 B2)) ->
  qsubL E (qtyp_qtyp P1 (typ_pair A1 B1)) (qtyp_qtyp P2 (typ_pair A2 B2)) ->
  subqtype E A1 A2 /\ subqtype E B1 B2.
Proof.
  intros E P1 A1 B1 P2 A2 B2 Hwf Hw1 Hw2 Hq.
  pose proof (qsubL_to_subqtype_wf E _ _ Hwf Hw1 Hw2 Hq) as Hst.
  inversion Hst; subst.
  match goal with Hs : sub E (typ_pair _ _) (typ_pair _ _) |- _ =>
    inversion Hs; subst; auto
  end.
Qed.

Lemma qsubL_sum_components_wf : forall E P1 A1 B1 P2 A2 B2,
  wf_env E ->
  wf_qtyp E (qtyp_qtyp P1 (typ_sum A1 B1)) ->
  wf_qtyp E (qtyp_qtyp P2 (typ_sum A2 B2)) ->
  qsubL E (qtyp_qtyp P1 (typ_sum A1 B1)) (qtyp_qtyp P2 (typ_sum A2 B2)) ->
  subqtype E A1 A2 /\ subqtype E B1 B2.
Proof.
  intros E P1 A1 B1 P2 A2 B2 Hwf Hw1 Hw2 Hq.
  pose proof (qsubL_to_subqtype_wf E _ _ Hwf Hw1 Hw2 Hq) as Hst.
  inversion Hst; subst.
  match goal with Hs : sub E (typ_sum _ _) (typ_sum _ _) |- _ =>
    inversion Hs; subst; auto
  end.
Qed.

Lemma qsubL_arrow_components_wf : forall E Q1 A1 B1 Q2 A2 B2,
  wf_env E ->
  wf_qtyp E (qtyp_qtyp Q1 (typ_arrow A1 B1)) ->
  wf_qtyp E (qtyp_qtyp Q2 (typ_arrow A2 B2)) ->
  qsubL E (qtyp_qtyp Q1 (typ_arrow A1 B1)) (qtyp_qtyp Q2 (typ_arrow A2 B2)) ->
  subqtype E A2 A1 /\ subqtype E B1 B2.
Proof.
  intros E Q1 A1 B1 Q2 A2 B2 Hwf Hw1 Hw2 Hq.
  pose proof (qsubL_to_subqtype_wf E _ _ Hwf Hw1 Hw2 Hq) as Hst.
  inversion Hst; subst.
  match goal with Hs : sub E (typ_arrow _ _) (typ_arrow _ _) |- _ =>
    inversion Hs; subst; auto
  end.
Qed.

Lemma qsubR_pair_components_wf : forall E P1 A1 B1 P2 A2 B2,
  wf_env E ->
  wf_qtyp E (qtyp_qtyp P1 (typ_pair A1 B1)) ->
  wf_qtyp E (qtyp_qtyp P2 (typ_pair A2 B2)) ->
  qsubR E (qtyp_qtyp P1 (typ_pair A1 B1)) (qtyp_qtyp P2 (typ_pair A2 B2)) ->
  subqtype E A1 A2 /\ subqtype E B1 B2.
Proof. intros. apply qsubL_pair_components_wf with (P1:=P1)(P2:=P2); auto using qsubR_to_qsubL. Qed.

Lemma qsubR_sum_components_wf : forall E P1 A1 B1 P2 A2 B2,
  wf_env E ->
  wf_qtyp E (qtyp_qtyp P1 (typ_sum A1 B1)) ->
  wf_qtyp E (qtyp_qtyp P2 (typ_sum A2 B2)) ->
  qsubR E (qtyp_qtyp P1 (typ_sum A1 B1)) (qtyp_qtyp P2 (typ_sum A2 B2)) ->
  subqtype E A1 A2 /\ subqtype E B1 B2.
Proof. intros. apply qsubL_sum_components_wf with (P1:=P1)(P2:=P2); auto using qsubR_to_qsubL. Qed.

Lemma qsubR_arrow_components_wf : forall E Q1 A1 B1 Q2 A2 B2,
  wf_env E ->
  wf_qtyp E (qtyp_qtyp Q1 (typ_arrow A1 B1)) ->
  wf_qtyp E (qtyp_qtyp Q2 (typ_arrow A2 B2)) ->
  qsubR E (qtyp_qtyp Q1 (typ_arrow A1 B1)) (qtyp_qtyp Q2 (typ_arrow A2 B2)) ->
  subqtype E A2 A1 /\ subqtype E B1 B2.
Proof. intros. apply qsubL_arrow_components_wf with (Q1:=Q1)(Q2:=Q2); auto using qsubR_to_qsubL. Qed.

Lemma qsubR_qtyp_qual_wf : forall E Q1 Q2 T1 T2,
  wf_env E -> wf_qtyp E (qtyp_qtyp Q1 T1) -> wf_qtyp E (qtyp_qtyp Q2 T2) ->
  qsubR E (qtyp_qtyp Q1 T1) (qtyp_qtyp Q2 T2) -> subqual E Q1 Q2.
Proof.
  intros. destruct (qsubL_qtyp_components_wf E Q1 T1 Q2 T2 H H0 H1 (qsubR_to_qsubL E _ _ H2)).
  assumption.
Qed.


(* ===== inlined from /tmp/main/AllComponents.v ===== *)

Lemma qsubL_all_components : forall E Q1 A1 B1 Q2 A2 B2,
  wf_env E ->
  wf_qtyp E (qtyp_qtyp Q1 (typ_all A1 B1)) ->
  wf_qtyp E (qtyp_qtyp Q2 (typ_all A2 B2)) ->
  qsubL E (qtyp_qtyp Q1 (typ_all A1 B1)) (qtyp_qtyp Q2 (typ_all A2 B2)) ->
  subqual E Q1 Q2 /\ sub E A2 A1 /\
  exists L, forall X, X `notin` L ->
    subqtype (X ~ bind_sub A2 ++ E) (open_tqt B1 X) (open_tqt B2 X).
Proof.
  intros E Q1 A1 B1 Q2 A2 B2 Hwf Hw1 Hw2 Hq.
  pose proof (qsubL_to_subqtype_wf E _ _ Hwf Hw1 Hw2 Hq) as Hst.
  inversion Hst; subst.
  match goal with Hsub : sub E (typ_all _ _) (typ_all _ _) |- _ =>
    inversion Hsub; subst
  end.
  match goal with H : forall X : atom, X `notin` ?L -> _ |- _ =>
    split; [assumption|split; [assumption|exists L; exact H]]
  end.
Qed.

Lemma qsubL_qall_components : forall E Q1 R1 B1 Q2 R2 B2,
  wf_env E ->
  wf_qtyp E (qtyp_qtyp Q1 (typ_qall R1 B1)) ->
  wf_qtyp E (qtyp_qtyp Q2 (typ_qall R2 B2)) ->
  qsubL E (qtyp_qtyp Q1 (typ_qall R1 B1)) (qtyp_qtyp Q2 (typ_qall R2 B2)) ->
  subqual E Q1 Q2 /\ subqual E R2 R1 /\
  exists L, forall X, X `notin` L ->
    subqtype (X ~ bind_qua R2 ++ E) (open_qqt B1 X) (open_qqt B2 X).
Proof.
  intros E Q1 R1 B1 Q2 R2 B2 Hwf Hw1 Hw2 Hq.
  pose proof (qsubL_to_subqtype_wf E _ _ Hwf Hw1 Hw2 Hq) as Hst.
  inversion Hst; subst.
  match goal with Hsub : sub E (typ_qall _ _) (typ_qall _ _) |- _ =>
    inversion Hsub; subst
  end.
  match goal with H : forall X : atom, X `notin` ?L -> _ |- _ =>
    split; [assumption|split; [assumption|exists L; exact H]]
  end.
Qed.


(* ===== inlined from /tmp/main/ValueBot.v ===== *)

Lemma value_typing_bot : forall E Q v T,
  wf_env E -> value v -> typing E Q v T -> typing E qua_bot v T.
Proof.
  intros E Q v T Hwf Hv. revert Q T. induction Hv; intros Q0 T0 Hty.
  - (* value_abs *) destruct (typing_abs_inv_syn E Q0 P T e1 T0 Hty)
      as [L [T1 [Hbody [Hqual Hqs]]]].
    assert (Hint : typing E qua_bot (exp_abs P T e1) (qtyp_qtyp P (typ_arrow T T1))).
    { apply typing_abs with (L := L); exact Hbody. }
    apply (typing_forward_qsubR E (qtyp_qtyp P (typ_arrow T T1)) T0 Hqs qua_bot (exp_abs P T e1) Hint).
  - (* value_tabs *) destruct (typing_tabs_inv_syn E Q0 P T e1 T0 Hty)
      as [L [T1 [Hbody [Hqual Hqs]]]].
    assert (Hint : typing E qua_bot (exp_tabs P T e1) (qtyp_qtyp P (typ_all T T1))).
    { apply typing_tabs with (L := L); exact Hbody. }
    apply (typing_forward_qsubR E (qtyp_qtyp P (typ_all T T1)) T0 Hqs qua_bot (exp_tabs P T e1) Hint).
  - (* value_qabs *) destruct (typing_qabs_inv_syn E Q0 P Q e1 T0 Hty)
      as [L [T1 [HwP [Hbody [Hqual Hqs]]]]].
    assert (Hint : typing E qua_bot (exp_qabs P Q e1) (qtyp_qtyp P (typ_qall Q T1))).
    { apply typing_qabs with (L := L); [exact HwP|exact Hbody]. }
    apply (typing_forward_qsubR E (qtyp_qtyp P (typ_qall Q T1)) T0 Hqs qua_bot (exp_qabs P Q e1) Hint).
  - (* value_inl *) destruct (typing_inl_inv_syn E Q0 P e1 T0 Hty)
      as [Q1 [T1 [T2 [He1 [HwP [HwT2 [Hq Hqs]]]]]]].
    pose proof (IHHv Q1 T1 He1) as He1'.
    assert (Hint : typing E qua_bot (exp_inl P e1) (qtyp_qtyp P (typ_sum T1 T2))).
    { apply typing_inl with (Q := qua_bot); [exact HwP|exact He1'|exact HwT2]. }
    apply (typing_forward_qsubR E (qtyp_qtyp P (typ_sum T1 T2)) T0 Hqs qua_bot (exp_inl P e1) Hint).
  - (* value_inr *) destruct (typing_inr_inv_syn E Q0 P e1 T0 Hty)
      as [Q1 [T1 [T2 [He1 [HwP [HwT1 [Hq Hqs]]]]]]].
    pose proof (IHHv Q1 T2 He1) as He1'.
    assert (Hint : typing E qua_bot (exp_inr P e1) (qtyp_qtyp P (typ_sum T1 T2))).
    { apply typing_inr with (Q := qua_bot); [exact HwP|exact He1'|exact HwT1]. }
    apply (typing_forward_qsubR E (qtyp_qtyp P (typ_sum T1 T2)) T0 Hqs qua_bot (exp_inr P e1) Hint).
  - (* value_pair *) destruct (typing_pair_inv_syn E Q0 P e1 e2 T0 Hty)
      as [Q1 [T1 [T2 [He1 [He2 [HwP [Hq Hqs]]]]]]].
    pose proof (IHHv1 Q1 T1 He1) as He1'.
    pose proof (IHHv2 Q1 T2 He2) as He2'.
    assert (Hint : typing E qua_bot (exp_pair P e1 e2) (qtyp_qtyp P (typ_pair T1 T2))).
    { apply typing_pair with (Q := qua_bot); [exact HwP|exact He1'|exact He2']. }
    apply (typing_forward_qsubR E (qtyp_qtyp P (typ_pair T1 T2)) T0 Hqs qua_bot (exp_pair P e1 e2) Hint).
Qed.


(* ===== inlined from /tmp/main/ValueSteps.v ===== *)

Section ValueSteps.
Context (typing_ctx_wf_qtyp : forall E Q c T,
  typing_ctx E Q c T -> wf_env E -> wf_qtyp E T).

Lemma check_step_generic : forall E Q v P K T,
  value v -> typing E Q v T -> typing_ctx E Q (frame_check P :: K) T ->
  typing_state E〈 v | K 〉.
Proof.
  intros E Q v P K T Hval Hty Hctx.
  destruct (typing_ctx_check_inv_syn E Q P K T Hctx)
    as [Q0 [P0 [T0 [HwfP [Hk [HqL HqsL]]]]]].
  assert (Hwf : wf_env E) by (eapply typing_wf_env; eassumption).
  set (Tn := qtyp_qtyp (qua_meet P0 P) T0).
  assert (Hwt0 : wf_qtyp E (qtyp_qtyp P0 T0)).
  { eapply typing_ctx_wf_qtyp; eassumption. }
  destruct (wf_qtyp_inv E P0 T0 Hwt0) as [HwqP0 HwT0].
  assert (Hsq : subqtype E (qtyp_qtyp (qua_meet P0 P) T0) (qtyp_qtyp P0 T0)).
  { apply sub_qtyp_qtyp.
    - apply subqual_meet_eliml.
      + apply subqual_refl; [exact Hwf|exact HwqP0].
      + exact HwfP.
    - apply sub_refl_wf; [exact HwT0|exact Hwf]. }
  apply (typing_step E Q0 v K Tn).
  - eapply typing_forward_qualL; [exact HqL|].
    apply (typing_forward_qsubL E T Tn HqsL Q v Hty).
  - apply (typing_ctx_sub E Q0 K Tn (qtyp_qtyp P0 T0) Hk Hsq).
Qed.

End ValueSteps.


(* ===== inlined from /tmp/main/Step.v ===== *)

Lemma preserve_app_1 : forall E Q e1 e2 K T,
  typing E Q (exp_app e1 e2) T ->
  typing_ctx E Q K T ->
  typing_state E〈 e1 | frame_abs e2 :: K 〉.
Proof.
  intros E Q e1 e2 K T Hty Hctx.
  destruct (typing_app_inv E Q (exp_app e1 e2) T Hty e1 e2 eq_refl)
    as [Q0 [T1 [T2 [He1 [He2 [Hq Hqs]]]]]].
  apply (typing_step E Q0 e1 (frame_abs e2 :: K) (qtyp_qtyp Q0 (typ_arrow T1 T2))).
  - exact He1.
  - apply typing_ctx_abs.
    + apply (typing_ctx_to_qsubL E T2 T).
      * apply qsubR_to_qsubL. exact Hqs.
      * apply (typing_ctx_to_qualL E Q0 Q).
        -- apply qualR_to_qualL. exact Hq.
        -- exact Hctx.
    + exact He2.
Qed.

Lemma preserve_app_2 : forall E Q v f K T,
  value v ->
  typing E Q v T ->
  typing_ctx E Q (frame_abs f :: K) T ->
  typing_state E〈 f | frame_app v :: K 〉.
Proof.
  intros E Q v f K T Hval Hty Hctx.
  destruct (typing_ctx_abs_inv E Q (frame_abs f :: K) T Hctx f K eq_refl)
    as [Q0 [T1 [T2 [Hk [Hf [HqL HqsL]]]]]].
  apply (typing_step E Q0 f (frame_app v :: K) T1).
  - exact Hf.
  - apply typing_ctx_app with (T1 := T1) (T2 := T2).
    + exact Hk.
    + exact Hval.
    + apply (typing_forward_qualL E Q Q0).
      * exact HqL.
      * apply (typing_forward_qsubL E T (qtyp_qtyp Q0 (typ_arrow T1 T2))).
        -- exact HqsL.
        -- exact Hty.
Qed.

Section BarrierHyp.
Context (subqual_trans_env : forall E Q R S, wf_env E -> subqual E Q R -> subqual E R S -> subqual E Q S).

Lemma preserve_barrier : forall E Q e s K T,
  typing E Q e T ->
  typing_ctx E Q (frame_barrier s :: K) T ->
  typing_state E〈 e | K 〉.
Proof.
  intros E Q e s K T Hty Hctx.
  destruct (typing_ctx_barrier_inv E Q (frame_barrier s :: K) T Hctx s K eq_refl)
    as [Q0 [Tbody [t0 [s0 [Hk [Hconc [Hle [HqL HqsL]]]]]]]].
  assert (Hwf : wf_env E) by (eapply typing_wf_env; eassumption).
  assert (Hwq0 : wf_qua E Q0) by (eapply typing_ctx_wf_qua; eassumption).
  assert (Hsub1 : subqual E (abstractize t0) (abstractize s0)).
  { apply subqual_abstractize; assumption. }
  assert (Hsub2 : subqual E (abstractize s0) Q0).
  { apply wf_qua_concretize_subqual; assumption. }
  assert (Hsub3 : subqual E (abstractize t0) Q0).
  { eapply subqual_trans_env; eassumption. }
  assert (Htail : qualL E (abstractize t0) Q0).
  { eapply qualL_step; [exact Hsub3|apply qualL_refl]. }
  assert (HqL' : qualL E Q Q0).
  { apply (qualL_concat E Q (abstractize t0) Q0); assumption. }
  apply (typing_step E Q0 e K Tbody).
  - apply (typing_forward_qualL E Q Q0).
    + exact HqL'.
    + apply (typing_forward_qsubL E T Tbody).
      * exact HqsL.
      * exact Hty.
  - exact Hk.
Qed.

End BarrierHyp.


(* ===== inlined from /tmp/w3/Basics.v ===== *)

Lemma subst_env_te_cons : forall X V y b E,
  subst_env_te X V (y ~ b ++ E) = y ~ subst_bind_te X V b ++ subst_env_te X V E.
Proof. intros. reflexivity. Qed.

Lemma subst_env_qe_cons : forall X R y b E,
  subst_env_qe X R (y ~ b ++ E) = y ~ subst_bind_qe X R b ++ subst_env_qe X R E.
Proof. intros. reflexivity. Qed.

Lemma kind_of_subst_bind_te : forall X V b,
  kind_of (subst_bind_te X V b) = kind_of b.
Proof. intros. destruct b; reflexivity. Qed.

Lemma kind_of_subst_bind_qe : forall X R b,
  kind_of (subst_bind_qe X R b) = kind_of b.
Proof. intros. destruct b; reflexivity. Qed.

Lemma dom_subst_env_te : forall X V E,
  dom (subst_env_te X V E) = dom E.
Proof.
  intros. unfold subst_env_te. induction E as [|[y b] E IH]; simpl; [reflexivity|].
  simpl. f_equal. exact IH.
Qed.

Lemma dom_subst_env_qe : forall X R E,
  dom (subst_env_qe X R E) = dom E.
Proof.
  intros. unfold subst_env_qe. induction E as [|[y b] E IH]; simpl; [reflexivity|].
  simpl. f_equal. exact IH.
Qed.

Lemma env_kind_eq_subst_env_te : forall X V E,
  env_kind_eq E (subst_env_te X V E).
Proof.
  intros X V E. induction E as [|[y b] E IH]; simpl.
  - unfold env_kind_eq. split; intros x c H; destruct H.
  - apply env_kind_eq_cons.
    + exact IH.
    + rewrite kind_of_subst_bind_te. reflexivity.
Qed.


(* ===== inlined from /tmp/w3/Phase1.v ===== *)

Inductive env_drop_te (X : atom) (V : typ) : env -> env -> Prop :=
| edt_base : forall (V0 : typ) (E2 : env),
    env_drop_te X V (X ~ bind_sub V0 ++ E2) (subst_env_te X V E2)
| edt_cons : forall (y : atom) (b : binding) (Eold Enew : env),
    y <> X ->
    env_drop_te X V Eold Enew ->
    env_drop_te X V (y ~ b ++ Eold) (y ~ subst_bind_te X V b ++ Enew).

Inductive env_drop_qe (X : atom) (R : qua) : env -> env -> Prop :=
| edq_base : forall (Q0 : qua) (E2 : env),
    env_drop_qe X R (X ~ bind_qua Q0 ++ E2) (subst_env_qe X R E2)
| edq_cons : forall (y : atom) (b : binding) (Eold Enew : env),
    y <> X ->
    env_drop_qe X R Eold Enew ->
    env_drop_qe X R (y ~ b ++ Eold) (y ~ subst_bind_qe X R b ++ Enew).

Lemma fv_binding_subst_bind_te_eq : forall X V b,
  X `notin` fv_binding b -> subst_bind_te X V b = b.
Proof.
  intros X V b H. destruct b; simpl in *; try reflexivity.
  - f_equal. apply subst_tt_nofv; exact H.
  - f_equal. apply subst_tqt_nofv; exact H.
Qed.

Lemma fv_binding_subst_bind_qe_eq : forall X R b,
  X `notin` fv_binding b -> subst_bind_qe X R b = b.
Proof.
  intros X R b H. destruct b; simpl in *; try reflexivity.
  - f_equal. apply subst_qt_nofv; exact H.
  - f_equal. apply subst_qqt_nofv; exact H.
  - f_equal. apply subst_qq_nofv; exact H.
Qed.



(* ===== inlined from /tmp/w3/Direct.v ===== *)

Lemma subst_env_te_app : forall X V E1 E2,
  subst_env_te X V (E1 ++ E2) = subst_env_te X V E1 ++ subst_env_te X V E2.
Proof. intros. unfold subst_env_te. apply map_app. Qed.

Lemma subst_env_qe_app : forall X R E1 E2,
  subst_env_qe X R (E1 ++ E2) = subst_env_qe X R E1 ++ subst_env_qe X R E2.
Proof. intros. unfold subst_env_qe. apply map_app. Qed.

Lemma binds_subst_env_te_map : forall X V E y b,
  binds y b E -> y <> X ->
  binds y (subst_bind_te X V b) (subst_env_te X V E).
Proof.
  intros X V E. induction E as [|[z c] E IH]; intros y b Hb Hne.
  - destruct Hb.
  - simpl in Hb. destruct Hb as [Heq|Hin].
    + injection Heq as -> ->.
      unfold subst_env_te. simpl. left. reflexivity.
    + unfold subst_env_te in *. simpl. right. apply IH; assumption.
Qed.

Lemma binds_subst_env_qe_map : forall X R E y b,
  binds y b E -> y <> X ->
  binds y (subst_bind_qe X R b) (subst_env_qe X R E).
Proof.
  intros X R E. induction E as [|[z c] E IH]; intros y b Hb Hne.
  - destruct Hb.
  - simpl in Hb. destruct Hb as [Heq|Hin].
    + injection Heq as -> ->.
      unfold subst_env_qe. simpl. left. reflexivity.
    + unfold subst_env_qe in *. simpl. right. apply IH; assumption.
Qed.

(* Well-formed types/quals only contain free atoms from the environment domain. *)
Lemma wf_qua_fv_dom : forall E Q, wf_qua E Q -> forall X, X `in` fv_qq Q -> X `in` dom E.
Proof.
  intros E Q H. induction H; intros Z Hx.
  - exfalso; fsetdec.
  - simpl in Hx. assert (Z = X) by fsetdec. subst. apply (binds_In _ _ _ E H).
  - simpl in Hx. assert (Hu : Z `in` fv_qq Q1 \/ Z `in` fv_qq Q2) by fsetdec.
    destruct Hu as [H1|H2].
    + apply IHwf_qua1; exact H1.
    + apply IHwf_qua2; exact H2.
  - simpl in Hx. assert (Hu : Z `in` fv_qq Q1 \/ Z `in` fv_qq Q2) by fsetdec.
    destruct Hu as [H1|H2].
    + apply IHwf_qua1; exact H1.
    + apply IHwf_qua2; exact H2.
  - exfalso; fsetdec.
Qed.

Lemma fv_open_qq_incl : forall (Q : qua) (j : nat) (R : qua),
  fv_qq Q [<=] fv_qq (open_qq_rec j R Q).
Proof.
  intros Q. induction Q; intros j0 R0; simpl.
  - apply Subset_refl.
  - destruct (j0 == n); simpl; fsetdec.
  - apply Subset_refl.
  - apply union_s_m; [apply IHQ1|apply IHQ2].
  - apply union_s_m; [apply IHQ1|apply IHQ2].
  - apply Subset_refl.
Qed.

Fixpoint fv_open_tt_incl (T : typ) {struct T} :
  forall (j : nat) (U : typ), fv_tt T [<=] fv_tt (open_tt_rec j U T)
with fv_open_tqt_incl (T : qtyp) {struct T} :
  forall (j : nat) (U : typ), fv_tqt T [<=] fv_tqt (open_tqt_rec j U T).
Proof.
  - destruct T; intros j0 U0; simpl.
    + apply Subset_refl.
    + destruct (j0 == n); simpl; fsetdec.
    + fsetdec.
    + apply union_s_m; [apply fv_open_tqt_incl|apply fv_open_tqt_incl].
    + apply union_s_m; [apply fv_open_tt_incl|apply fv_open_tqt_incl].
    + apply union_s_m; [apply Subset_refl|apply fv_open_tqt_incl].
    + apply union_s_m; [apply fv_open_tqt_incl|apply fv_open_tqt_incl].
    + apply union_s_m; [apply fv_open_tqt_incl|apply fv_open_tqt_incl].
    + apply fv_open_tqt_incl.
  - destruct T as [Q T0]; intros j0 U0; simpl.
    apply union_s_m; [apply Subset_refl|apply fv_open_tt_incl].
Qed.

Fixpoint fv_open_qt_incl (T : typ) {struct T} :
  forall (j : nat) (R : qua), fv_tt T [<=] fv_tt (open_qt_rec j R T)
with fv_open_qqt_incl (T : qtyp) {struct T} :
  forall (j : nat) (R : qua), fv_tqt T [<=] fv_tqt (open_qqt_rec j R T).
Proof.
  - destruct T; intros j0 R0; simpl.
    + apply Subset_refl.
    + fsetdec.
    + fsetdec.
    + apply union_s_m; [apply fv_open_qqt_incl|apply fv_open_qqt_incl].
    + apply union_s_m; [apply fv_open_qt_incl|apply fv_open_qqt_incl].
    + apply union_s_m; [apply fv_open_qq_incl|apply fv_open_qqt_incl].
    + apply union_s_m; [apply fv_open_qqt_incl|apply fv_open_qqt_incl].
    + apply union_s_m; [apply fv_open_qqt_incl|apply fv_open_qqt_incl].
    + apply fv_open_qqt_incl.
  - destruct T as [Q T0]; intros j0 R0; simpl.
    apply union_s_m; [apply fv_open_qq_incl|apply fv_open_qt_incl].
Qed.

Fixpoint wf_typ_fv_dom (E : env) (T : typ) (H : wf_typ E T) {struct H} :
  forall X, X `in` fv_tt T -> X `in` dom E
with wf_qtyp_fv_dom (E : env) (T : qtyp) (H : wf_qtyp E T) {struct H} :
  forall X, X `in` fv_tqt T -> X `in` dom E.
Proof.
  - destruct H; intros Z Hx; simpl in Hx.
    + exfalso; fsetdec.
    + assert (Z = X) by fsetdec. subst Z. apply (binds_In _ _ _ E H).
    + assert (Hu : Z `in` fv_tqt T1 \/ Z `in` fv_tqt T2) by fsetdec.
      destruct Hu as [H1|H2].
      * apply (wf_qtyp_fv_dom E T1 H Z H1).
      * apply (wf_qtyp_fv_dom E T2 H0 Z H2).
    + assert (Hu : Z `in` fv_tt T1 \/ Z `in` fv_tqt T2) by fsetdec.
      destruct Hu as [H1|H2].
      * apply (wf_typ_fv_dom E T1 H Z H1).
      * destruct (atom_fresh (union L (singleton Z))) as [Y Hy].
        assert (HYL : Y `notin` L) by fsetdec.
        assert (HYZ : Y <> Z) by fsetdec.
        assert (Hmem : Z `in` fv_tqt (open_tqt T2 Y)).
        { exact (fv_open_tqt_incl T2 0 Y Z H2). }
        pose proof (wf_qtyp_fv_dom (Y ~ bind_sub T1 ++ E) (open_tqt T2 Y) (H0 Y HYL) Z Hmem) as Hdom.
        simpl in Hdom. fsetdec.
    + assert (Hu : Z `in` fv_qq T1 \/ Z `in` fv_tqt T2) by fsetdec.
      destruct Hu as [H1|H2].
      * apply wf_qua_fv_dom with (Q := T1); assumption.
      * destruct (atom_fresh (union L (singleton Z))) as [Y Hy].
        assert (HYL : Y `notin` L) by fsetdec.
        assert (HYZ : Y <> Z) by fsetdec.
        assert (Hmem : Z `in` fv_tqt (open_qqt T2 Y)).
        { exact (fv_open_qqt_incl T2 0 Y Z H2). }
        pose proof (wf_qtyp_fv_dom (Y ~ bind_qua T1 ++ E) (open_qqt T2 Y) (H0 Y HYL) Z Hmem) as Hdom.
        simpl in Hdom. fsetdec.
    + assert (Hu : Z `in` fv_tqt T1 \/ Z `in` fv_tqt T2) by fsetdec.
      destruct Hu as [H1|H2].
      * apply (wf_qtyp_fv_dom E T1 H Z H1).
      * apply (wf_qtyp_fv_dom E T2 H0 Z H2).
    + assert (Hu : Z `in` fv_tqt T1 \/ Z `in` fv_tqt T2) by fsetdec.
      destruct Hu as [H1|H2].
      * apply (wf_qtyp_fv_dom E T1 H Z H1).
      * apply (wf_qtyp_fv_dom E T2 H0 Z H2).
  - destruct H as [E0 Q0 T0 Hq HT]. intros Z Hx. simpl in Hx.
    assert (Hu : Z `in` fv_qq Q0 \/ Z `in` fv_tt T0) by fsetdec.
    destruct Hu as [H1|H2].
    + apply wf_qua_fv_dom with (Q := Q0); assumption.
    + apply (wf_typ_fv_dom E0 T0 HT Z H2).
Qed.

Lemma wf_env_binds_fv_dom : forall E (Hwf : wf_env E) y b,
  binds y b E -> forall X, X `in` fv_binding b -> X `in` dom E.
Proof.
  intros E Hwf y b Hb X Hx. destruct b as [T|T|Q]; simpl in Hx.
  - apply (wf_typ_fv_dom E T (wf_env_binds_wf E Hwf y (bind_sub T) Hb) X Hx).
  - apply (wf_qtyp_fv_dom E T (wf_env_binds_wf E Hwf y (bind_typ T) Hb) X Hx).
  - apply wf_qua_fv_dom with (Q := Q); [apply (wf_env_binds_wf E Hwf y (bind_qua Q) Hb)|exact Hx].
Qed.

Lemma subst_bind_te_id : forall X V b,
  X `notin` fv_binding b -> subst_bind_te X V b = b.
Proof. apply fv_binding_subst_bind_te_eq. Qed.

Lemma subst_bind_qe_id : forall X R b,
  X `notin` fv_binding b -> subst_bind_qe X R b = b.
Proof. apply fv_binding_subst_bind_qe_eq. Qed.

Lemma subst_env_te_id : forall X V E,
  wf_env E -> X `notin` dom E -> subst_env_te X V E = E.
Proof.
  intros X V E. induction E as [|[y b] E IH]; intros Hwf Hdom; simpl.
  - reflexivity.
  - assert (Hyb : X `notin` fv_binding b).
    { intro Hc. apply Hdom. cbn. apply (wf_env_binds_fv_dom (y ~ b ++ E) Hwf y b); [left; reflexivity|exact Hc]. }
    rewrite (subst_bind_te_id X V b Hyb).
    assert (HwfE : wf_env E) by (apply (proj1 (wf_env_cons_inv y b E Hwf))).
    assert (HdomE : X `notin` dom E) by (cbn in Hdom; fsetdec).
    rewrite IH; [reflexivity|exact HwfE|exact HdomE].
Qed.

Lemma subst_env_qe_id : forall X R E,
  wf_env E -> X `notin` dom E -> subst_env_qe X R E = E.
Proof.
  intros X R E. induction E as [|[y b] E IH]; intros Hwf Hdom; simpl.
  - reflexivity.
  - assert (Hyb : X `notin` fv_binding b).
    { intro Hc. apply Hdom. cbn. apply (wf_env_binds_fv_dom (y ~ b ++ E) Hwf y b); [left; reflexivity|exact Hc]. }
    rewrite (subst_bind_qe_id X R b Hyb).
    assert (HwfE : wf_env E) by (apply (proj1 (wf_env_cons_inv y b E Hwf))).
    assert (HdomE : X `notin` dom E) by (cbn in Hdom; fsetdec).
    rewrite IH; [reflexivity|exact HwfE|exact HdomE].
Qed.

Lemma wf_env_mid_bind_wf : forall E1 x b E2,
  wf_env (E1 ++ x ~ b ++ E2) ->
  match b with
  | bind_sub T => wf_typ E2 T
  | bind_typ T => wf_qtyp E2 T
  | bind_qua Q => wf_qua E2 Q
  end.
Proof.
  intros E1. induction E1 as [|[y c] E1 IH]; intros x b E2 Hwf.
  - destruct (wf_env_cons_inv x b E2 Hwf) as [_ [_ Hb]]; exact Hb.
  - simpl in Hwf.
    destruct (wf_env_cons_inv y c (E1 ++ x ~ b ++ E2) Hwf) as [Htail _].
    apply (IH x b E2 Htail).
Qed.

Lemma wf_env_mid_notin_tail : forall E1 x b E2,
  wf_env (E1 ++ x ~ b ++ E2) -> x `notin` dom E2.
Proof.
  intros E1. induction E1 as [|[y c] E1 IH]; intros x b E2 Hwf.
  - destruct (wf_env_cons_inv x b E2 Hwf) as [_ [Hdom _]]; exact Hdom.
  - simpl in Hwf.
    destruct (wf_env_cons_inv y c (E1 ++ x ~ b ++ E2) Hwf) as [Htail _].
    apply (IH x b E2 Htail).
Qed.



(* ===== inlined from /tmp/w3/Extra.v ===== *)

Section VOpen.
Context (X : atom) (V : typ).
Context (V_open_tt : forall (j : nat) (Y : atom), open_tt_rec j (typ_fvar Y) V = V).
Context (V_open_qt : forall (j : nat) (Y : atom), open_qt_rec j (qua_fvar Y) V = V).

Fixpoint subst_tt_open_tt (T : typ) {struct T} :
  forall (j : nat) (Y : atom), Y <> X ->
    subst_tt X V (open_tt_rec j (typ_fvar Y) T) =
    open_tt_rec j (typ_fvar Y) (subst_tt X V T)
with subst_tqt_open_tqt (T : qtyp) {struct T} :
  forall (j : nat) (Y : atom), Y <> X ->
    subst_tqt X V (open_tqt_rec j (typ_fvar Y) T) =
    open_tqt_rec j (typ_fvar Y) (subst_tqt X V T).
Proof.
  - destruct T; intros j0 Y0 Hne; simpl.
    + reflexivity.
    + destruct (j0 == n); simpl.
      * destruct (X == Y0) as [Heq|Hneq]; [exfalso; apply Hne; symmetry; exact Heq|reflexivity].
      * reflexivity.
    + destruct (X == a) as [Heq|Hneq]; simpl; [exact (eq_sym (V_open_tt j0 Y0))|reflexivity].
    + f_equal. all: (try reflexivity; first [apply subst_tqt_open_tqt; exact Hne | symmetry; apply subst_tqt_open_tqt; exact Hne]).
    + f_equal. all: (try reflexivity; first [apply subst_tt_open_tt; exact Hne | apply subst_tqt_open_tqt; exact Hne | symmetry; apply subst_tt_open_tt; exact Hne | symmetry; apply subst_tqt_open_tqt; exact Hne]).
    + f_equal. all: (try reflexivity; first [apply subst_tqt_open_tqt; exact Hne | symmetry; apply subst_tqt_open_tqt; exact Hne]).
    + f_equal. all: (try reflexivity; first [apply subst_tqt_open_tqt; exact Hne | symmetry; apply subst_tqt_open_tqt; exact Hne]).
    + f_equal. all: (try reflexivity; first [apply subst_tqt_open_tqt; exact Hne | symmetry; apply subst_tqt_open_tqt; exact Hne]).
    + f_equal; apply subst_tqt_open_tqt; exact Hne.
  - destruct T as [Q T0]; intros j0 Y0 Hne; simpl.
    f_equal; try reflexivity; apply subst_tt_open_tt; exact Hne.
Qed.

Fixpoint subst_tt_open_qt (T : typ) {struct T} :
  forall (j : nat) (Y : atom), Y <> X ->
    subst_tt X V (open_qt_rec j (qua_fvar Y) T) =
    open_qt_rec j (qua_fvar Y) (subst_tt X V T)
with subst_tqt_open_qqt (T : qtyp) {struct T} :
  forall (j : nat) (Y : atom), Y <> X ->
    subst_tqt X V (open_qqt_rec j (qua_fvar Y) T) =
    open_qqt_rec j (qua_fvar Y) (subst_tqt X V T).
Proof.
  - destruct T; intros j0 Y0 Hne; simpl.
    + reflexivity.
    + reflexivity.
    + destruct (X == a) as [Heq|Hneq]; simpl; [exact (eq_sym (V_open_qt j0 Y0))|reflexivity].
    + f_equal. all: (try reflexivity; first [apply subst_tqt_open_qqt; exact Hne | symmetry; apply subst_tqt_open_qqt; exact Hne]).
    + f_equal. all: (try reflexivity; first [apply subst_tt_open_qt; exact Hne | apply subst_tqt_open_qqt; exact Hne | symmetry; apply subst_tt_open_qt; exact Hne | symmetry; apply subst_tqt_open_qqt; exact Hne]).
    + f_equal. all: (try reflexivity; first [apply subst_tqt_open_qqt; exact Hne | symmetry; apply subst_tqt_open_qqt; exact Hne]).
    + f_equal. all: (try reflexivity; first [apply subst_tqt_open_qqt; exact Hne | symmetry; apply subst_tqt_open_qqt; exact Hne]).
    + f_equal. all: (try reflexivity; first [apply subst_tqt_open_qqt; exact Hne | symmetry; apply subst_tqt_open_qqt; exact Hne]).
    + f_equal; apply subst_tqt_open_qqt; exact Hne.
  - destruct T as [Q T0]; intros j0 Y0 Hne; simpl.
    f_equal; try reflexivity; apply subst_tt_open_qt; exact Hne.
Qed.

End VOpen.


(* ===== inlined from /tmp/w3/WFSubst.v ===== *)

Lemma binds_subst_env_te_drop : forall E1 E2 X V0 V y b,
  y <> X ->
  binds y b (E1 ++ X ~ bind_sub V0 ++ E2) ->
  binds y (subst_bind_te X V b) (subst_env_te X V (E1 ++ E2)).
Proof.
  intros E1 E2 X V0 V y b Hne Hb.
  apply binds_app_1 in Hb. destruct Hb as [Hb1|Hb2].
  - rewrite subst_env_te_app. apply binds_app_l. apply binds_subst_env_te_map; assumption.
  - apply binds_cons_1 in Hb2. destruct Hb2 as [[Heq Hbeq]|Hb2].
    + subst y. exfalso; apply Hne; reflexivity.
    + rewrite subst_env_te_app. apply binds_app_r. apply binds_subst_env_te_map; assumption.
Qed.


Lemma binds_subst_env_te_qua : forall X V E y Q,
  binds y (bind_qua Q) E -> binds y (bind_qua Q) (subst_env_te X V E).
Proof.
  intros X V E. induction E as [|[z c] E IH]; intros y Q Hb.
  - destruct Hb.
  - simpl in Hb. destruct Hb as [Heq|Hin].
    + injection Heq as -> ->. unfold subst_env_te. simpl. left. reflexivity.
    + unfold subst_env_te in *. simpl. right. apply IH; assumption.
Qed.

Lemma wf_qua_subst_env_te : forall E Q,
  wf_qua E Q -> forall X V, wf_qua (subst_env_te X V E) Q.
Proof.
  intros E Q H. induction H; intros X0 V0.
  - apply wf_qua_top.
  - apply wf_qua_fvar with (R := R). apply binds_subst_env_te_qua. exact H.
  - apply wf_qua_meet; [apply IHwf_qua1|apply IHwf_qua2].
  - apply wf_qua_join; [apply IHwf_qua1|apply IHwf_qua2].
  - apply wf_qua_bot.
Qed.

Lemma subst_env_te_cons_app : forall X V y b E1 E2,
  subst_env_te X V ((y ~ b ++ E1) ++ E2) =
  y ~ subst_bind_te X V b ++ subst_env_te X V (E1 ++ E2).
Proof.
  intros. simpl. rewrite subst_env_te_app. reflexivity.
Qed.



Lemma subst_tqt_open_tqt_wf : forall (E : env) (X : atom) (V : typ) (T : qtyp) j Y,
  wf_typ E V -> Y <> X ->
  subst_tqt X V (open_tqt_rec j (typ_fvar Y) T) =
  open_tqt_rec j (typ_fvar Y) (subst_tqt X V T).
Proof.
  intros. eapply (subst_tqt_open_tqt X V).
  - intros j0 Y0. exact (type_open_tt_fvar V (wf_typ_type E V H) j0 Y0).
  - exact H0.
Qed.

Lemma subst_tqt_open_qqt_wf : forall (E : env) (X : atom) (V : typ) (T : qtyp) j Y,
  wf_typ E V -> Y <> X ->
  subst_tqt X V (open_qqt_rec j (qua_fvar Y) T) =
  open_qqt_rec j (qua_fvar Y) (subst_tqt X V T).
Proof.
  intros. eapply (subst_tqt_open_qqt X V).
  - intros j0 Y0. exact (type_open_qt_fvar V (wf_typ_type E V H) j0 Y0).
  - exact H0.
Qed.

Lemma binds_X_mid : forall E1 E2 X V0,
  binds X (bind_sub V0) (E1 ++ X ~ bind_sub V0 ++ E2).
Proof.
  intros. apply binds_app_r, binds_app_l, binds_cons_2; reflexivity.
Qed.

Lemma dom_mid_remove_notin_sub : forall (E1 E2 : env) (x : atom) (V0 : typ) (Y : atom),
  Y `notin` dom (E1 ++ x ~ bind_sub V0 ++ E2) -> Y `notin` dom (E1 ++ E2).
Proof.
  intros. rewrite dom_app in *. rewrite dom_app in H. fsetdec.
Qed.

Lemma binds_mid_remove_any : forall (E1 E2 : env) (x : atom) (b : binding)
  (y : atom) (c : binding),
  y <> x -> binds y c (E1 ++ x ~ b ++ E2) -> binds y c (E1 ++ E2).
Proof.
  intros E1. induction E1 as [|[z d] E1 IH]; intros E2 x b y c Hne Hb.
  - simpl in Hb. apply binds_cons_1 in Hb. destruct Hb as [[Heq Hbeq]|Hin].
    + subst y. exfalso; apply Hne; reflexivity.
    + exact Hin.
  - simpl in Hb. apply binds_cons_1 in Hb. destruct Hb as [[Heq Hbeq]|Hin].
    + subst y. subst c. simpl. left. reflexivity.
    + simpl. right. apply (IH E2 x b y c Hne Hin).
Qed.

Lemma wf_qua_mid_remove_sub : forall E1 E2 x (V0 : typ) Q,
  wf_env (E1 ++ x ~ bind_sub V0 ++ E2) ->
  wf_qua (E1 ++ x ~ bind_sub V0 ++ E2) Q -> wf_qua (E1 ++ E2) Q.
Proof.
  intros E1 E2 x V0 Q Hwf Hq.
  remember (E1 ++ x ~ bind_sub V0 ++ E2) as E eqn:HE.
  revert E1 E2 x V0 Hwf HE.
  induction Hq; intros E1 E2 x0 V0 Hwf HE.
  - apply wf_qua_top.
  - subst E.
    apply wf_qua_fvar with (R := R).
    assert (Xneq : X <> x0).
    { intro Heq. subst X.
      assert (Hbq : binds x0 (bind_qua R) (E1 ++ x0 ~ bind_sub V0 ++ E2)) by exact H.
      assert (Hbs : binds x0 (bind_sub V0) (E1 ++ x0 ~ bind_sub V0 ++ E2)).
      { apply binds_app_r, binds_app_l, binds_cons_2; reflexivity. }
      pose proof (binds_unique binding x0 (bind_qua R) (bind_sub V0)
                    (E1 ++ x0 ~ bind_sub V0 ++ E2) Hbq Hbs (wf_env_uniq _ Hwf)) as Heqb.
      discriminate Heqb. }
    exact (binds_mid_remove_any E1 E2 x0 (bind_sub V0) X (bind_qua R) Xneq H).
  - subst E. apply wf_qua_meet.
    + apply (IHHq1 E1 E2 x0 V0 Hwf eq_refl).
    + apply (IHHq2 E1 E2 x0 V0 Hwf eq_refl).
  - subst E. apply wf_qua_join.
    + apply (IHHq1 E1 E2 x0 V0 Hwf eq_refl).
    + apply (IHHq2 E1 E2 x0 V0 Hwf eq_refl).
  - apply wf_qua_bot.
Qed.



(* ===== inlined from /tmp/w3/WfSubst2.v ===== *)

Definition Pwf_subst (E : env) (T : typ) (H : wf_typ E T) : Prop :=
  forall E1 E2 (X : atom) (V0 V : typ),
    E = E1 ++ X ~ bind_sub V0 ++ E2 ->
    wf_env E ->
    wf_env (subst_env_te X V (E1 ++ E2)) ->
    wf_typ (subst_env_te X V (E1 ++ E2)) V ->
    wf_typ (subst_env_te X V (E1 ++ E2)) (subst_tt X V T).

Definition Pwfq_subst (E : env) (T : qtyp) (H : wf_qtyp E T) : Prop :=
  forall E1 E2 (X : atom) (V0 V : typ),
    E = E1 ++ X ~ bind_sub V0 ++ E2 ->
    wf_env E ->
    wf_env (subst_env_te X V (E1 ++ E2)) ->
    wf_typ (subst_env_te X V (E1 ++ E2)) V ->
    wf_qtyp (subst_env_te X V (E1 ++ E2)) (subst_tqt X V T).

Lemma wf_typ_subst_drop : forall E T (H : wf_typ E T), Pwf_subst E T H
with wf_qtyp_subst_drop : forall E T (H : wf_qtyp E T), Pwfq_subst E T H.
Proof.
  - intros E T H.
    refine (wf_typ_mut_ind Pwf_subst Pwfq_subst _ _ _ _ _ _ _ _ E T H).
    + intros E0. unfold Pwf_subst. intros E1 E2 X V0 V HE HwfE Hwtgt2 HVtgt. apply wf_typ_top.
    + intros U E0 Y b E1 E2 X V0 V HE HwfE Hwtgt2 HVtgt.
      subst E0.
      simpl. destruct (eq_dec Y X) as [Heq|Hne].
      * subst Y. rewrite eq_dec_refl. simpl. exact HVtgt.
      * destruct (X == Y) as [Heq'|Hne']; [exfalso; apply Hne; symmetry; exact Heq'|].
        simpl. eapply wf_typ_var.
        eapply (binds_subst_env_te_drop E1 E2 X V0 V Y (bind_sub U)).
        -- exact Hne.
        -- exact b.
    + intros E0 T1 T2 w IHw w0 IHw0 E1 E2 X V0 V HE HwfE Hwtgt2 HVtgt.
      subst E0. simpl. apply wf_typ_arrow.
      * apply (IHw E1 E2 X V0 V eq_refl HwfE Hwtgt2 HVtgt).
      * apply (IHw0 E1 E2 X V0 V eq_refl HwfE Hwtgt2 HVtgt).
    + intros L E0 T1 T2 w IHw w0 IHw0 E1 E2 X V0 V HE HwfE Hwtgt2 HVtgt.
      subst E0.
      apply wf_typ_all with (L := union L (union (singleton X)
        (union (dom (E1 ++ X ~ bind_sub V0 ++ E2)) (dom (subst_env_te X V (E1 ++ E2)))))).
      * apply (IHw E1 E2 X V0 V eq_refl HwfE Hwtgt2 HVtgt).
      * intros Y HY.
        assert (HYL : Y `notin` L) by fsetdec.
        assert (HYX : Y <> X) by fsetdec.
        assert (HYdom : Y `notin` dom (E1 ++ X ~ bind_sub V0 ++ E2)) by fsetdec.
        assert (Hwfold' : wf_env ((Y ~ bind_sub T1 ++ E1) ++ X ~ bind_sub V0 ++ E2)).
        { simpl. apply wf_env_sub.
          - exact HwfE.
          - exact w.
          - exact HYdom. }
        assert (HsubT1 : wf_typ (subst_env_te X V (E1 ++ E2)) (subst_tt X V T1)).
        { apply (IHw E1 E2 X V0 V eq_refl HwfE Hwtgt2 HVtgt). }
        assert (HYtgt : Y `notin` dom (subst_env_te X V (E1 ++ E2))).
        { rewrite dom_subst_env_te. apply dom_mid_remove_notin_sub with (x:=X)(V0:=V0). exact HYdom. }
        assert (HwfE' : wf_env (subst_env_te X V ((Y ~ bind_sub T1 ++ E1) ++ E2))).
        { rewrite subst_env_te_cons_app. apply wf_env_sub; [exact Hwtgt2|exact HsubT1|exact HYtgt]. }
        assert (HV' : wf_typ (subst_env_te X V ((Y ~ bind_sub T1 ++ E1) ++ E2)) V).
        { rewrite subst_env_te_cons_app. exact (wf_typ_weaken (subst_env_te X V (E1++E2))
            (Y ~ bind_sub (subst_tt X V T1) ++ subst_env_te X V (E1++E2)) V HwfE'
            (env_extends_cons_tail (subst_env_te X V (E1++E2)) Y (bind_sub (subst_tt X V T1))) HVtgt). }
        assert (HEq : Y ~ bind_sub T1 ++ (E1 ++ X ~ bind_sub V0 ++ E2) =
                      (Y ~ bind_sub T1 ++ E1) ++ X ~ bind_sub V0 ++ E2).
        { rewrite app_assoc. reflexivity. }
        pose proof (IHw0 Y HYL (Y ~ bind_sub T1 ++ E1) E2 X V0 V HEq Hwfold' HwfE' HV') as Hbody.
        rewrite subst_env_te_cons_app in Hbody.
        change (wf_qtyp (subst_env_te X V ((Y ~ bind_sub T1 ++ E1) ++ E2))
                 (subst_tqt X V (open_tqt_rec 0 (typ_fvar Y) T2))) in Hbody.
        rewrite (subst_tqt_open_tqt_wf (subst_env_te X V ((Y ~ bind_sub T1 ++ E1) ++ E2)) X V T2 0 Y HV' HYX) in Hbody.
        change (wf_qtyp (subst_env_te X V ((Y ~ bind_sub T1 ++ E1) ++ E2))
                 (open_tqt_rec 0 (typ_fvar Y) (subst_tqt X V T2))) in Hbody.
        exact Hbody.
    + intros L E0 Qv T2 Hq w0 IHw0 E1 E2 X V0 V HE HwfE Hwtgt2 HVtgt.
      subst E0.
      apply wf_typ_qall with (L := union L (union (singleton X)
        (union (dom (E1 ++ X ~ bind_sub V0 ++ E2)) (dom (subst_env_te X V (E1 ++ E2)))))).
      * apply wf_qua_subst_env_te. eapply wf_qua_mid_remove_sub; [exact HwfE|exact Hq].
      * intros Y HY.
        assert (HYL : Y `notin` L) by fsetdec.
        assert (HYX : Y <> X) by fsetdec.
        assert (HYdom : Y `notin` dom (E1 ++ X ~ bind_sub V0 ++ E2)) by fsetdec.
        assert (HYtgt : Y `notin` dom (subst_env_te X V (E1 ++ E2))).
        { rewrite dom_subst_env_te. apply dom_mid_remove_notin_sub with (x:=X)(V0:=V0). exact HYdom. }
        assert (Hwfold' : wf_env (Y ~ bind_qua Qv ++ (E1 ++ X ~ bind_sub V0 ++ E2))).
        { apply wf_env_qua; [exact HwfE|exact Hq|exact HYdom]. }
        assert (HwfE' : wf_env (subst_env_te X V ((Y ~ bind_qua Qv ++ E1) ++ E2))).
        { rewrite subst_env_te_cons_app. apply wf_env_qua; [exact Hwtgt2| |exact HYtgt].
          apply wf_qua_subst_env_te. eapply wf_qua_mid_remove_sub; [exact HwfE|exact Hq]. }
        assert (HV' : wf_typ (subst_env_te X V ((Y ~ bind_qua Qv ++ E1) ++ E2)) V).
        { rewrite subst_env_te_cons_app. exact (wf_typ_weaken (subst_env_te X V (E1++E2))
            (Y ~ subst_bind_te X V (bind_qua Qv) ++ subst_env_te X V (E1++E2)) V HwfE'
            (env_extends_cons_tail (subst_env_te X V (E1++E2)) Y (subst_bind_te X V (bind_qua Qv))) HVtgt). }
        assert (HEq : Y ~ bind_qua Qv ++ (E1 ++ X ~ bind_sub V0 ++ E2) =
                      (Y ~ bind_qua Qv ++ E1) ++ X ~ bind_sub V0 ++ E2).
        { rewrite app_assoc. reflexivity. }
        pose proof (IHw0 Y HYL (Y ~ bind_qua Qv ++ E1) E2 X V0 V HEq Hwfold' HwfE' HV') as Hbody.
        rewrite subst_env_te_cons_app in Hbody.
        change (wf_qtyp (subst_env_te X V ((Y ~ bind_qua Qv ++ E1) ++ E2))
                 (subst_tqt X V (open_qqt_rec 0 (qua_fvar Y) T2))) in Hbody.
        rewrite (subst_tqt_open_qqt_wf (subst_env_te X V ((Y ~ bind_qua Qv ++ E1) ++ E2)) X V T2 0 Y HV' HYX) in Hbody.
        change (wf_qtyp (subst_env_te X V ((Y ~ bind_qua Qv ++ E1) ++ E2))
                 (open_qqt_rec 0 (qua_fvar Y) (subst_tqt X V T2))) in Hbody.
        exact Hbody.
    + intros E0 T1 T2 w IHw w0 IHw0 E1 E2 X V0 V HE HwfE Hwtgt2 HVtgt.
      subst E0. simpl. apply wf_typ_sum.
      * apply (IHw E1 E2 X V0 V eq_refl HwfE Hwtgt2 HVtgt).
      * apply (IHw0 E1 E2 X V0 V eq_refl HwfE Hwtgt2 HVtgt).
    + intros E0 T1 T2 w IHw w0 IHw0 E1 E2 X V0 V HE HwfE Hwtgt2 HVtgt.
      subst E0. simpl. apply wf_typ_pair.
      * apply (IHw E1 E2 X V0 V eq_refl HwfE Hwtgt2 HVtgt).
      * apply (IHw0 E1 E2 X V0 V eq_refl HwfE Hwtgt2 HVtgt).
    + intros E0 Q0 T0 w w0 IHw0 E1 E2 X V0 V HE HwfE Hwtgt2 HVtgt.
      subst E0. simpl. apply wf_qtyp_qtyp.
      * apply wf_qua_subst_env_te. eapply wf_qua_mid_remove_sub; [exact HwfE|exact w].
      * apply (IHw0 E1 E2 X V0 V eq_refl HwfE Hwtgt2 HVtgt).
  - intros E T H. destruct T as [Q T0].
    inversion H as [E0 Q0 T0' Hq HT]; subst.
    unfold Pwfq_subst. intros E1 E2 X V0 V HE HwfE Hwtgt2 HVtgt.
    rewrite HE in HwfE. rewrite HE in Hq. rewrite HE in HT.
    simpl. apply wf_qtyp_qtyp.
    + apply wf_qua_subst_env_te. eapply wf_qua_mid_remove_sub; [exact HwfE|exact Hq].
    + exact (wf_typ_subst_drop (E1 ++ X ~ bind_sub V0 ++ E2) T0 HT
               E1 E2 X V0 V eq_refl HwfE Hwtgt2 HVtgt).
Qed.


(* ===== inlined from /tmp/w3/OpenSubst.v ===== *)

Fixpoint subst_qq_open_same (Q : qua) {struct Q} :
  forall k X R, X `notin` fv_qq Q ->
    subst_qq X R (open_qq_rec k (qua_fvar X) Q) = open_qq_rec k R Q.
Proof.
  destruct Q; intros k X R Hfv; simpl in *.
  - reflexivity.
  - destruct (k == n); simpl.
    + rewrite eq_dec_refl. reflexivity.
    + reflexivity.
  - assert (a <> X) by (intro; subst; fsetdec).
    simpl. destruct (X == a) as [Heq|Hne]; [exfalso; apply H; symmetry; exact Heq|reflexivity].
  - f_equal; [apply subst_qq_open_same|apply subst_qq_open_same]; fsetdec.
  - f_equal; [apply subst_qq_open_same|apply subst_qq_open_same]; fsetdec.
  - reflexivity.
Qed.

Fixpoint subst_tt_open_same (T : typ) {struct T} :
  forall k X V, X `notin` fv_tt T ->
    subst_tt X V (open_tt_rec k (typ_fvar X) T) = open_tt_rec k V T
with subst_tqt_open_same (T : qtyp) {struct T} :
  forall k X V, X `notin` fv_tqt T ->
    subst_tqt X V (open_tqt_rec k (typ_fvar X) T) = open_tqt_rec k V T.
Proof.
  - destruct T; intros k X V Hfv; simpl in *.
    + reflexivity.
    + destruct (k == n); simpl.
      * rewrite eq_dec_refl. simpl. reflexivity.
      * reflexivity.
    + assert (a <> X) by (intro; subst; fsetdec).
      simpl. destruct (X == a) as [Heq|Hne]; [exfalso; apply H; symmetry; exact Heq|reflexivity].
    + f_equal; [apply subst_tqt_open_same|apply subst_tqt_open_same with (k:=S k)]; fsetdec.
    + f_equal; [apply subst_tt_open_same|apply subst_tqt_open_same with (k:=S k)]; fsetdec.
    + f_equal; apply subst_tqt_open_same with (k:=S k); fsetdec.
    + f_equal; [apply subst_tqt_open_same|apply subst_tqt_open_same]; fsetdec.
    + f_equal; [apply subst_tqt_open_same|apply subst_tqt_open_same]; fsetdec.
    + f_equal; apply subst_tqt_open_same; fsetdec.
  - destruct T as [Q T0]; intros k X V Hfv; simpl in *. f_equal.
    assert (Hfv' : X `notin` fv_tt T0) by fsetdec.
    exact (subst_tt_open_same T0 k X V Hfv').
Qed.

Fixpoint subst_qt_open_same (T : typ) {struct T} :
  forall k X R, X `notin` fv_tt T ->
    subst_qt X R (open_qt_rec k (qua_fvar X) T) = open_qt_rec k R T
with subst_qqt_open_same (T : qtyp) {struct T} :
  forall k X R, X `notin` fv_tqt T ->
    subst_qqt X R (open_qqt_rec k (qua_fvar X) T) = open_qqt_rec k R T.
Proof.
  - destruct T; intros k X R Hfv; simpl in *.
    + reflexivity.
    + reflexivity.
    + assert (a <> X) by (intro; subst; fsetdec).
      simpl. destruct (X == a) as [Heq|Hne]; [exfalso; apply H; symmetry; exact Heq|reflexivity].
    + f_equal; [apply subst_qqt_open_same|apply subst_qqt_open_same with (k:=S k)]; fsetdec.
    + f_equal; [apply subst_qt_open_same|apply subst_qqt_open_same with (k:=S k)]; fsetdec.
    + f_equal; [apply subst_qq_open_same|apply subst_qqt_open_same with (k:=S k)]; fsetdec.
    + f_equal; [apply subst_qqt_open_same|apply subst_qqt_open_same]; fsetdec.
    + f_equal; [apply subst_qqt_open_same|apply subst_qqt_open_same]; fsetdec.
    + f_equal; apply subst_qqt_open_same; fsetdec.
  - destruct T as [Q T0]; intros k X R Hfv; simpl in *. f_equal.
    + apply subst_qq_open_same; fsetdec.
    + assert (Hfv' : X `notin` fv_tt T0) by fsetdec.
    exact (subst_qt_open_same T0 k X R Hfv').
Qed.

Lemma wf_qtyp_open_te_fresh : forall (E : env) (X : atom) (V0 V : typ) (T2 : qtyp),
  wf_env E -> X `notin` dom E -> X `notin` fv_tqt T2 ->
  wf_typ E V0 -> wf_typ E V ->
  wf_qtyp (X ~ bind_sub V0 ++ E) (open_tqt_rec 0 (typ_fvar X) T2) ->
  wf_qtyp E (open_tqt_rec 0 V T2).
Proof.
  intros E X V0 V T2 HwfE HdomX Hfv HwV0 HV Hbody.
  assert (HwfEold : wf_env (X ~ bind_sub V0 ++ E)) by (apply wf_env_sub; assumption).
  assert (Hwtgt : wf_env (subst_env_te X V (nil ++ E)))
    by (simpl; rewrite (subst_env_te_id X V E HwfE HdomX); exact HwfE).
  assert (HVtgt : wf_typ (subst_env_te X V (nil ++ E)) V)
    by (simpl; rewrite (subst_env_te_id X V E HwfE HdomX); exact HV).
  pose proof (wf_qtyp_subst_drop (X ~ bind_sub V0 ++ E) (open_tqt_rec 0 (typ_fvar X) T2) Hbody
                nil E X V0 V eq_refl HwfEold Hwtgt HVtgt) as Hres.
  simpl in Hres.
  rewrite (subst_env_te_id X V E HwfE HdomX) in Hres.
  rewrite (subst_tqt_open_same T2 0 X V Hfv) in Hres.
  exact Hres.
Qed.


(* ===== inlined from /tmp/w3/OpenSubstE.v ===== *)

Lemma subst_te_open_te_same_rec : forall (e : exp) k X V,
  X `notin` fv_ee e ->
  subst_te X V (open_te_rec k (typ_fvar X) e) = open_te_rec k V e.
Proof.
  induction e; intros k X V Hfv; simpl in *.
  - reflexivity.
  - reflexivity.
  - (* abs *) f_equal.
    + apply subst_tqt_open_same; fsetdec.
    + apply IHe; fsetdec.
  - (* app *) f_equal; [apply IHe1|apply IHe2]; fsetdec.
  - (* tabs *) f_equal.
    + apply subst_tt_open_same; fsetdec.
    + apply IHe; fsetdec.
  - (* tapp *) f_equal.
    + apply IHe; fsetdec.
    + apply subst_tt_open_same; fsetdec.
  - (* qabs *) f_equal. apply IHe; fsetdec.
  - (* qapp *) f_equal. apply IHe; fsetdec.
  - (* let *) f_equal; [apply IHe1|apply IHe2]; fsetdec.
  - (* inl *) f_equal. apply IHe; fsetdec.
  - (* inr *) f_equal. apply IHe; fsetdec.
  - (* case *) f_equal; [apply IHe1|apply IHe2|apply IHe3]; fsetdec.
  - (* pair *) f_equal; [apply IHe1|apply IHe2]; fsetdec.
  - (* first *) f_equal. apply IHe; fsetdec.
  - (* second *) f_equal. apply IHe; fsetdec.
  - (* ref *) f_equal. apply IHe; fsetdec.
  - (* ref_label *) reflexivity.
  - (* deref *) f_equal. apply IHe; fsetdec.
  - (* set_ref *) f_equal; [apply IHe1|apply IHe2]; fsetdec.
  - (* check *) f_equal. apply IHe; fsetdec.
  - (* upqual *) f_equal. apply IHe; fsetdec.
Qed.

Lemma subst_qe_open_qe_same_rec : forall (e : exp) k X R,
  X `notin` fv_ee e ->
  subst_qe X R (open_qe_rec k (qua_fvar X) e) = open_qe_rec k R e.
Proof.
  induction e; intros k X R Hfv; simpl in *.
  - reflexivity.
  - reflexivity.
  - (* abs *) f_equal.
    + apply subst_qq_open_same; fsetdec.
    + apply subst_qqt_open_same; fsetdec.
    + apply IHe; fsetdec.
  - (* app *) f_equal; [apply IHe1|apply IHe2]; fsetdec.
  - (* tabs *) f_equal.
    + apply subst_qq_open_same; fsetdec.
    + apply subst_qt_open_same; fsetdec.
    + apply IHe; fsetdec.
  - (* tapp *) f_equal.
    + apply IHe; fsetdec.
    + apply subst_qt_open_same; fsetdec.
  - (* qabs *) f_equal.
    + apply subst_qq_open_same; fsetdec.
    + apply subst_qq_open_same; fsetdec.
    + apply IHe; fsetdec.
  - (* qapp *) f_equal.
    + apply IHe; fsetdec.
    + apply subst_qq_open_same; fsetdec.
  - (* let *) f_equal; [apply IHe1|apply IHe2]; fsetdec.
  - (* inl *) f_equal; [apply subst_qq_open_same|apply IHe]; fsetdec.
  - (* inr *) f_equal; [apply subst_qq_open_same|apply IHe]; fsetdec.
  - (* case *) f_equal; [apply IHe1|apply IHe2|apply IHe3]; fsetdec.
  - (* pair *) f_equal.
    + apply subst_qq_open_same; fsetdec.
    + apply IHe1; fsetdec.
    + apply IHe2; fsetdec.
  - (* first *) f_equal. apply IHe; fsetdec.
  - (* second *) f_equal. apply IHe; fsetdec.
  - (* ref *) f_equal.
    + apply subst_qq_open_same; fsetdec.
    + apply IHe; fsetdec.
  - (* ref_label *) f_equal. apply subst_qq_open_same; fsetdec.
  - (* deref *) f_equal. apply IHe; fsetdec.
  - (* set_ref *) f_equal; [apply IHe1|apply IHe2]; fsetdec.
  - (* check *) f_equal.
    + apply subst_qq_open_same; fsetdec.
    + apply IHe; fsetdec.
  - (* upqual *) f_equal.
    + apply subst_qq_open_same; fsetdec.
    + apply IHe; fsetdec.
Qed.

Lemma subst_te_open_te_self : forall X V body,
  X `notin` fv_ee body -> subst_te X V (open_te body X) = open_te body V.
Proof. intros. exact (subst_te_open_te_same_rec body 0 X V H). Qed.

Lemma subst_qe_open_qe_self : forall X R body,
  X `notin` fv_ee body -> subst_qe X R (open_qe body X) = open_qe body R.
Proof. intros. exact (subst_qe_open_qe_same_rec body 0 X R H). Qed.

Lemma subst_tqt_open_tqt_self : forall X V T,
  X `notin` fv_tqt T -> subst_tqt X V (open_tqt T X) = open_tqt T V.
Proof. intros. exact (subst_tqt_open_same T 0 X V H). Qed.

Lemma subst_qqt_open_qqt_self : forall X R T,
  X `notin` fv_tqt T -> subst_qqt X R (open_qqt T X) = open_qqt T R.
Proof. intros. exact (subst_qqt_open_same T 0 X R H). Qed.


(* ===== inlined from /tmp/w3/Gen.v ===== *)

(* The substitution V is well formed in the fixed base environment E2.  The
   target environment therefore always ends with E2. *)
Lemma wf_typ_subst_env_te_base : forall (X : atom) (V : typ) E1 E2,
  wf_env E2 ->
  wf_env (subst_env_te X V (E1 ++ E2)) ->
  X `notin` dom E2 ->
  wf_typ E2 V ->
  wf_typ (subst_env_te X V (E1 ++ E2)) V.
Proof.
  intros X V E1 E2 HE2 Htgt HX HV.
  rewrite subst_env_te_app in Htgt.
  rewrite (subst_env_te_id X V E2 HE2 HX) in Htgt.
  rewrite subst_env_te_app.
  rewrite (subst_env_te_id X V E2 HE2 HX).
  eapply wf_typ_weaken; [exact Htgt| |exact HV].
  replace (subst_env_te X V E1 ++ E2)
    with (subst_env_te X V E1 ++ E2 ++ nil).
  - apply env_extends_insert.
  - rewrite app_nil_r; reflexivity.
Qed.

Lemma notin_dom_subst_env_te_mid : forall E1 E2 (X : atom) (V0 V : typ) y,
  y `notin` dom (E1 ++ X ~ bind_sub V0 ++ E2) ->
  y `notin` dom (subst_env_te X V (E1 ++ E2)).
Proof.
  intros. rewrite dom_subst_env_te.
  eapply dom_mid_remove_notin_sub; eauto.
Qed.

Lemma wf_qua_subst_env_te_mid : forall E1 E2 (X : atom) (V0 V : typ) Q,
  wf_env (E1 ++ X ~ bind_sub V0 ++ E2) ->
  wf_qua (E1 ++ X ~ bind_sub V0 ++ E2) Q ->
  wf_qua (subst_env_te X V (E1 ++ E2)) Q.
Proof.
  intros. apply wf_qua_subst_env_te.
  eapply wf_qua_mid_remove_sub; eauto.
Qed.

Lemma wf_env_subst_te_gen : forall E (X : atom) (V0 V : typ) E1 E2,
  wf_env E ->
  E = E1 ++ X ~ bind_sub V0 ++ E2 ->
  wf_env E2 ->
  wf_typ E2 V ->
  wf_env (subst_env_te X V (E1 ++ E2)).
Proof.
  intros E X V0 V E1. revert E X V0 V.
  induction E1 as [|[y b] E1 IH];
    intros E X V0 V E2 Hwf HE HE2 HV.
  - simpl in HE. subst E.
    change (wf_env (subst_env_te X V E2)).
    assert (Heq : subst_env_te X V E2 = E2).
    { apply subst_env_te_id.
      - exact HE2.
      - apply (wf_env_mid_notin_tail nil X (bind_sub V0) E2).
        exact Hwf. }
    rewrite Heq. exact HE2.
  - simpl in HE. subst E.
    simpl in Hwf.
    destruct (wf_env_cons_inv y b (E1 ++ X ~ bind_sub V0 ++ E2) Hwf)
      as [Htail [Hy Hbf]].
    assert (Htgt : wf_env (subst_env_te X V (E1 ++ E2))).
    { eapply IH; [exact Htail|reflexivity|exact HE2|exact HV]. }
    assert (HXnotin : X `notin` dom E2) by (eapply wf_env_mid_notin_tail; eauto).
    assert (HVtgt : wf_typ (subst_env_te X V (E1 ++ E2)) V).
    { eapply wf_typ_subst_env_te_base; eauto. }
    assert (Hytgt : y `notin` dom (subst_env_te X V (E1 ++ E2))).
    { eapply notin_dom_subst_env_te_mid; eauto. }
    change (wf_env (subst_env_te X V ((y ~ b ++ E1) ++ E2))).
    rewrite subst_env_te_cons_app.
    destruct b as [T|T|Q].
    + simpl. apply wf_env_sub; [exact Htgt| |exact Hytgt].
      eapply (wf_typ_subst_drop (E1 ++ X ~ bind_sub V0 ++ E2) T Hbf
                E1 E2 X V0 V eq_refl Htail Htgt HVtgt).
    + simpl. apply wf_env_typ; [exact Htgt| |exact Hytgt].
      eapply (wf_qtyp_subst_drop (E1 ++ X ~ bind_sub V0 ++ E2) T Hbf
                E1 E2 X V0 V eq_refl Htail Htgt HVtgt).
    + simpl. apply wf_env_qua; [exact Htgt| |exact Hytgt].
      eapply wf_qua_subst_env_te_mid; eauto.
Qed.


(* ===== inlined from /tmp/w3/OpenClosed.v ===== *)

(* A structurally closed type is insensitive to opening at any type.  The
   premise is the corresponding fvar-opening identity at the same depth. *)
Fixpoint closed_tt_any (T : typ) {struct T} :
  forall K : nat,
    (forall X : atom, open_tt_rec K (typ_fvar X) T = T) ->
    forall U : typ, open_tt_rec K U T = T
with closed_tqt_any (T : qtyp) {struct T} :
  forall K : nat,
    (forall X : atom, open_tqt_rec K (typ_fvar X) T = T) ->
    forall U : typ, open_tqt_rec K U T = T.
Proof.
  - destruct T; intros K H U; simpl.
    + reflexivity.
    + destruct (K == n) as [Heq|Hne].
      * subst K.
        exfalso.
        destruct (atom_fresh Metatheory.empty) as [X _].
        specialize (H X).
        remember (n == n) as b eqn:Heq.
        destruct b.
        -- change ((if n == n then typ_fvar X else typ_bvar n) = typ_bvar n) in H.
           rewrite eq_dec_refl in H. inversion H.
        -- exfalso. rewrite eq_dec_refl in Heq. discriminate Heq.
      * reflexivity.
    + reflexivity.
    + f_equal.
      * apply closed_tqt_any with (K := K).
        { intros X. specialize (H X). simpl in H. injection H as H1 H2. exact H1. }
      * apply closed_tqt_any with (K := S K).
        { intros X. specialize (H X). simpl in H. injection H as H1 H2. exact H2. }
    + f_equal.
      * apply closed_tt_any with (K := K).
        { intros X. specialize (H X). simpl in H. injection H as H1 H2. exact H1. }
      * apply closed_tqt_any with (K := S K).
        { intros X. specialize (H X). simpl in H. injection H as H1 H2. exact H2. }
    + f_equal.
      apply closed_tqt_any with (K := S K).
      { intros X. specialize (H X). simpl in H. injection H as H1. exact H1. }
    + f_equal.
      * apply closed_tqt_any with (K := K).
        { intros X. specialize (H X). simpl in H. injection H as H1 H2. exact H1. }
      * apply closed_tqt_any with (K := K).
        { intros X. specialize (H X). simpl in H. injection H as H1 H2. exact H2. }
    + f_equal.
      * apply closed_tqt_any with (K := K).
        { intros X. specialize (H X). simpl in H. injection H as H1 H2. exact H1. }
      * apply closed_tqt_any with (K := K).
        { intros X. specialize (H X). simpl in H. injection H as H1 H2. exact H2. }
    + f_equal.
      apply closed_tqt_any with (K := K).
      { intros X. specialize (H X). simpl in H. injection H as H1. exact H1. }
  - destruct T as [Q T0]; intros K H U; simpl.
    f_equal.
    apply closed_tt_any with (K := K).
    { intros X. specialize (H X). simpl in H. injection H as H1. exact H1. }
Qed.

Lemma wf_typ_open_tt_any : forall E T, wf_typ E T ->
  forall (K : nat) (U : typ), open_tt_rec K U T = T.
Proof.
  intros E T Hwf K U.
  apply (closed_tt_any T K).
  intros X. exact (type_open_tt_fvar T (wf_typ_type E T Hwf) K X).
Qed.


Lemma closed_qq_any : forall (Q : qua) (K : nat),
  (forall X : atom, open_qq_rec K (qua_fvar X) Q = Q) ->
  forall R : qua, open_qq_rec K R Q = Q.
Proof.
  intros Q. induction Q; intros K H R; simpl.
  - reflexivity.
  - destruct (K == n) as [Heq|Hne].
    + subst K.
      exfalso.
      destruct (atom_fresh Metatheory.empty) as [Y _].
      specialize (H Y).
      change ((if n == n then qua_fvar Y else qua_bvar n) = qua_bvar n) in H.
      rewrite eq_dec_refl in H. inversion H.
    + reflexivity.
  - reflexivity.
  - f_equal; [apply IHQ1 with (K := K)|apply IHQ2 with (K := K)];
      intros X; specialize (H X); simpl in H; injection H as H1 H2; assumption.
  - f_equal; [apply IHQ1 with (K := K)|apply IHQ2 with (K := K)];
      intros X; specialize (H X); simpl in H; injection H as H1 H2; assumption.
  - reflexivity.
Qed.

Fixpoint closed_tt_qt_any (T : typ) {struct T} :
  forall K : nat,
    (forall X : atom, open_qt_rec K (qua_fvar X) T = T) ->
    forall R : qua, open_qt_rec K R T = T
with closed_qqt_any (T : qtyp) {struct T} :
  forall K : nat,
    (forall X : atom, open_qqt_rec K (qua_fvar X) T = T) ->
    forall R : qua, open_qqt_rec K R T = T.
Proof.
  - destruct T; intros K H R; simpl.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + f_equal.
      * apply closed_qqt_any with (K := K).
        { intros X. specialize (H X). simpl in H. injection H as H1 H2. exact H1. }
      * apply closed_qqt_any with (K := S K).
        { intros X. specialize (H X). simpl in H. injection H as H1 H2. exact H2. }
    + f_equal.
      * apply closed_tt_qt_any with (K := K).
        { intros X. specialize (H X). simpl in H. injection H as H1 H2. exact H1. }
      * apply closed_qqt_any with (K := S K).
        { intros X. specialize (H X). simpl in H. injection H as H1 H2. exact H2. }
    + f_equal.
      * apply closed_qq_any with (K := K).
        { intros X. specialize (H X). simpl in H. injection H as H1 H2. exact H1. }
      * apply closed_qqt_any with (K := S K).
        { intros X. specialize (H X). simpl in H. injection H as H1 H2. exact H2. }
    + f_equal.
      * apply closed_qqt_any with (K := K).
        { intros X. specialize (H X). simpl in H. injection H as H1 H2. exact H1. }
      * apply closed_qqt_any with (K := K).
        { intros X. specialize (H X). simpl in H. injection H as H1 H2. exact H2. }
    + f_equal.
      * apply closed_qqt_any with (K := K).
        { intros X. specialize (H X). simpl in H. injection H as H1 H2. exact H1. }
      * apply closed_qqt_any with (K := K).
        { intros X. specialize (H X). simpl in H. injection H as H1 H2. exact H2. }
    + f_equal.
      apply closed_qqt_any with (K := K).
      { intros X. specialize (H X). simpl in H. injection H as H1. exact H1. }
  - destruct T as [Q T0]; intros K H R; simpl.
    f_equal.
    + apply closed_qq_any with (K := K).
      { intros X. specialize (H X). simpl in H. injection H as H1 H2. exact H1. }
    + apply closed_tt_qt_any with (K := K).
      { intros X. specialize (H X). simpl in H. injection H as H1 H2. exact H2. }
Qed.

Lemma wf_typ_open_qt_any : forall E T, wf_typ E T ->
  forall (K : nat) (R : qua), open_qt_rec K R T = T.
Proof.
  intros E T Hwf K R.
  apply (closed_tt_qt_any T K).
  intros X. exact (type_open_qt_fvar T (wf_typ_type E T Hwf) K X).
Qed.


(* ===== inlined from /tmp/w3wf/ExtraQe.v ===== *)

(* ===================================================================== *)
(* Well-formed qualifiers contain no bound variables, hence opening them *)
(* is the identity.                                                      *)
(* ===================================================================== *)

Lemma wf_qua_open_qq : forall E Q, wf_qua E Q ->
  forall (j : nat) (S : qua), open_qq_rec j S Q = Q.
Proof.
  intros E Q H. induction H; intros j0 S0; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal; [apply IHwf_qua1|apply IHwf_qua2].
  - f_equal; [apply IHwf_qua1|apply IHwf_qua2].
  - reflexivity.
Qed.

(* ===================================================================== *)
(* Commutation of qualifier substitution with type-opening              *)
(* (opening of type variables: no qualifier position is touched, and    *)
(*  subst_qqt does not touch type fvars/bvars, so no side conditions).  *)
(* ===================================================================== *)

Section QeTqt.
Context (X : atom) (R : qua).

Fixpoint subst_qt_open_tt (T : typ) {struct T} :
  forall (j : nat) (Y : atom),
    subst_qt X R (open_tt_rec j (typ_fvar Y) T) =
    open_tt_rec j (typ_fvar Y) (subst_qt X R T)
with subst_qqt_open_tqt (T : qtyp) {struct T} :
  forall (j : nat) (Y : atom),
    subst_qqt X R (open_tqt_rec j (typ_fvar Y) T) =
    open_tqt_rec j (typ_fvar Y) (subst_qqt X R T).
Proof.
  - destruct T; intros j0 Y0; simpl.
    + reflexivity.
    + destruct (j0 == n); reflexivity.
    + reflexivity.
    + f_equal; apply subst_qqt_open_tqt.
    + f_equal; [apply subst_qt_open_tt|apply subst_qqt_open_tqt].
    + f_equal; apply subst_qqt_open_tqt.
    + f_equal; apply subst_qqt_open_tqt.
    + f_equal; apply subst_qqt_open_tqt.
    + f_equal; apply subst_qqt_open_tqt.
  - destruct T as [Q T0]; intros j0 Y0; simpl.
    f_equal; apply subst_qt_open_tt.
Qed.

End QeTqt.

(* Convenience wrapper: the fvar-open / type version, no premises. *)
Lemma subst_qqt_open_tqt_wf : forall (T : qtyp) (j : nat) (X : atom)
  (R : qua) (Y : atom),
  subst_qqt X R (open_tqt_rec j (typ_fvar Y) T) =
  open_tqt_rec j (typ_fvar Y) (subst_qqt X R T).
Proof. intros. apply subst_qqt_open_tqt. Qed.

(* ===================================================================== *)
(* Commutation of qualifier substitution with qualifier-opening.        *)
(* The opening qualifier RY is itself qualifier-substituted, and the    *)
(* substituted qualifier R must contain no bound variables (otherwise   *)
(* it would be opened by the surrounding open): this is supplied by the *)
(* hypothesis R_open, which holds for every wf_qua (see wf_qua_open_qq).*)
(* ===================================================================== *)

Section QeQqt.
Context (X : atom) (R : qua).
Context (R_open : forall (j : nat) (S : qua), open_qq_rec j S R = R).

Fixpoint subst_qq_open_qqt (Q : qua) {struct Q} :
  forall (j : nat) (RY : qua),
    subst_qq X R (open_qq_rec j RY Q) =
    open_qq_rec j (subst_qq X R RY) (subst_qq X R Q).
Proof.
  destruct Q; intros j0 RY; simpl.
  - reflexivity.
  - destruct (j0 == n); reflexivity.
  - destruct (X == a) as [Heq|Hne].
    + subst a. simpl. apply eq_sym, R_open.
    + simpl. reflexivity.
  - f_equal; [apply subst_qq_open_qqt|apply subst_qq_open_qqt].
  - f_equal; [apply subst_qq_open_qqt|apply subst_qq_open_qqt].
  - reflexivity.
Qed.

Fixpoint subst_qt_open_qt (T : typ) {struct T} :
  forall (j : nat) (RY : qua),
    subst_qt X R (open_qt_rec j RY T) =
    open_qt_rec j (subst_qq X R RY) (subst_qt X R T)
with subst_qqt_open_qqt (T : qtyp) {struct T} :
  forall (j : nat) (RY : qua),
    subst_qqt X R (open_qqt_rec j RY T) =
    open_qqt_rec j (subst_qq X R RY) (subst_qqt X R T).
Proof.
  - destruct T; intros j0 RY; simpl.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + f_equal; apply subst_qqt_open_qqt.
    + f_equal; [apply subst_qt_open_qt|apply subst_qqt_open_qqt].
    + f_equal; [apply subst_qq_open_qqt|apply subst_qqt_open_qqt].
    + f_equal; apply subst_qqt_open_qqt.
    + f_equal; apply subst_qqt_open_qqt.
    + f_equal; apply subst_qqt_open_qqt.
  - destruct T as [Q T0]; intros j0 RY; simpl.
    f_equal.
    + apply subst_qq_open_qqt.
    + apply subst_qt_open_qt.
Qed.

End QeQqt.

(* Convenience wrapper: the fvar-open / qualifier version.  [R] must be
   well formed (hence bound-variable free), and the opened variable is
   distinct from the substituted one. *)
Lemma subst_qqt_open_qqt_wf : forall (E : env) (X : atom) (R : qua)
  (T : qtyp) (j : nat) (Y : atom),
  wf_qua E R -> Y <> X ->
  subst_qqt X R (open_qqt_rec j (qua_fvar Y) T) =
  open_qqt_rec j (qua_fvar Y) (subst_qqt X R T).
Proof.
  intros E X R T j Y HwfR Hne.
  assert (Hnf : X `notin` fv_qq (qua_fvar Y)) by (simpl; fsetdec).
  pose proof (subst_qqt_open_qqt X R
                (fun (k : nat) (S : qua) => wf_qua_open_qq E R HwfR k S)
                T j (qua_fvar Y)) as Hlem.
  rewrite (subst_qq_nofv X R (qua_fvar Y) Hnf) in Hlem.
  exact Hlem.
Qed.


(* ===== inlined from /tmp/w6/SubGenFix.v ===== *)

Lemma wf_typ_fvar_inv : forall E Y,
  wf_typ E (typ_fvar Y) -> exists U, binds Y (bind_sub U) E.
Proof.
  intros E Y H. inversion H; subst. eauto.
Qed.

(* te substitution maps bind_qua bindings unchanged. *)
Lemma binds_qua_target_te : forall E1 E2 (X : atom) (V0 V : typ) (Y : atom) Q,
  wf_env (E1 ++ X ~ bind_sub V0 ++ E2) ->
  binds Y (bind_qua Q) (E1 ++ X ~ bind_sub V0 ++ E2) ->
  binds Y (bind_qua Q) (subst_env_te X V (E1 ++ E2)).
Proof.
  intros E1 E2 X V0 V Y Q Hwf Hb.
  assert (HYX : Y <> X).
  { intro Heq. subst Y.
    assert (HbX : binds X (bind_sub V0) (E1 ++ X ~ bind_sub V0 ++ E2)).
    { apply binds_X_mid. }
    pose proof (binds_unique binding X (bind_qua Q) (bind_sub V0)
                  (E1 ++ X ~ bind_sub V0 ++ E2) Hb HbX (wf_env_uniq _ Hwf)) as Heqb.
    discriminate Heqb. }
  change (binds Y (subst_bind_te X V (bind_qua Q)) (subst_env_te X V (E1 ++ E2))).
  eapply binds_subst_env_te_drop; [exact HYX|exact Hb].
Qed.

Lemma subqual_subst_te_gen : forall E Q R, subqual E Q R ->
  forall (Z : atom) (V0 V : typ) E1 E2,
    wf_env E -> E = E1 ++ Z ~ bind_sub V0 ++ E2 ->
    wf_env E2 -> wf_typ E2 V ->
    subqual (subst_env_te Z V (E1 ++ E2)) Q R.
Proof.
  intros E Q R H. induction H; intros Z V0 V E1 E2 HwfE HE HE2 HV.
  - subst E. apply subqual_top.
    + exact (wf_env_subst_te_gen (E1 ++ Z ~ bind_sub V0 ++ E2)
               Z V0 V E1 E2 HwfE eq_refl HE2 HV).
    + eapply wf_qua_subst_env_te_mid; eauto.
  - subst E. apply subqual_bot.
    + exact (wf_env_subst_te_gen (E1 ++ Z ~ bind_sub V0 ++ E2)
               Z V0 V E1 E2 HwfE eq_refl HE2 HV).
    + eapply wf_qua_subst_env_te_mid; eauto.
  - subst E. apply subqual_refl_qvar.
    + exact (wf_env_subst_te_gen (E1 ++ Z ~ bind_sub V0 ++ E2)
               Z V0 V E1 E2 HwfE eq_refl HE2 HV).
    + eapply wf_qua_subst_env_te_mid; eauto.
  - subst E. eapply subqual_trans_qvar.
    + eapply binds_qua_target_te; eauto.
    + exact (IHsubqual Z V0 V E1 E2 HwfE eq_refl HE2 HV).
  - subst E. apply subqual_join_inl.
    + exact (IHsubqual Z V0 V E1 E2 HwfE eq_refl HE2 HV).
    + eapply wf_qua_subst_env_te_mid; eauto.
  - subst E. apply subqual_join_inr.
    + eapply wf_qua_subst_env_te_mid; eauto.
    + exact (IHsubqual Z V0 V E1 E2 HwfE eq_refl HE2 HV).
  - subst E. apply subqual_join_elim.
    + exact (IHsubqual1 Z V0 V E1 E2 HwfE eq_refl HE2 HV).
    + exact (IHsubqual2 Z V0 V E1 E2 HwfE eq_refl HE2 HV).
  - subst E. apply subqual_meet_eliml.
    + exact (IHsubqual Z V0 V E1 E2 HwfE eq_refl HE2 HV).
    + eapply wf_qua_subst_env_te_mid; eauto.
  - subst E. apply subqual_meet_elimr.
    + eapply wf_qua_subst_env_te_mid; eauto.
    + exact (IHsubqual Z V0 V E1 E2 HwfE eq_refl HE2 HV).
  - subst E. apply subqual_meet_intro.
    + exact (IHsubqual1 Z V0 V E1 E2 HwfE eq_refl HE2 HV).
    + exact (IHsubqual2 Z V0 V E1 E2 HwfE eq_refl HE2 HV).
Qed.

Lemma subst_te_target_V_wf : forall E (Z : atom) (V0 V : typ) E1 E2,
  wf_env E -> E = E1 ++ Z ~ bind_sub V0 ++ E2 ->
  wf_env E2 -> wf_typ E2 V ->
  wf_typ (subst_env_te Z V (E1 ++ E2)) V.
Proof.
  intros. eapply wf_typ_subst_env_te_base.
  - exact H1.
  - exact (wf_env_subst_te_gen E Z V0 V E1 E2 H H0 H1 H2).
  - eapply wf_env_mid_notin_tail.
    rewrite <- H0. exact H.
  - exact H2.
Qed.

Lemma notin_fv_mid_bind_sub_te : forall E1 E2 (Z : atom) (V0 : typ),
  wf_env (E1 ++ Z ~ bind_sub V0 ++ E2) -> Z `notin` fv_tt V0.
Proof.
  intros E1 E2 Z V0 Hwf Hc.
  assert (HZdom : Z `notin` dom E2) by (eapply wf_env_mid_notin_tail; eauto).
  apply HZdom.
  eapply wf_typ_fv_dom.
  - exact (wf_env_mid_bind_wf E1 Z (bind_sub V0) E2 Hwf).
  - exact Hc.
Qed.

Lemma sub_subst_te_gen : forall E S T, sub E S T ->
  forall (Z : atom) (V0 V : typ) E1 E2,
    wf_env E -> E = E1 ++ Z ~ bind_sub V0 ++ E2 ->
    wf_env E2 -> wf_typ E2 V -> sub E2 V V0 ->
    sub (subst_env_te Z V (E1 ++ E2)) (subst_tt Z V S) (subst_tt Z V T)
with subqtype_subst_te_gen : forall E S T, subqtype E S T ->
  forall (Z : atom) (V0 V : typ) E1 E2,
    wf_env E -> E = E1 ++ Z ~ bind_sub V0 ++ E2 ->
    wf_env E2 -> wf_typ E2 V -> sub E2 V V0 ->
    subqtype (subst_env_te Z V (E1 ++ E2)) (subst_tqt Z V S) (subst_tqt Z V T).
Proof.
  - intros E S T H. induction H using sub_mut_ind
      with (P := fun E S T w => forall (Z : atom) (V0 V : typ) E1 E2,
        wf_env E -> E = E1 ++ Z ~ bind_sub V0 ++ E2 ->
        wf_env E2 -> wf_typ E2 V -> sub E2 V V0 ->
        sub (subst_env_te Z V (E1 ++ E2)) (subst_tt Z V S) (subst_tt Z V T))
           (P0 := fun E S T w => forall (Z : atom) (V0 V : typ) E1 E2,
        wf_env E -> E = E1 ++ Z ~ bind_sub V0 ++ E2 ->
        wf_env E2 -> wf_typ E2 V -> sub E2 V V0 ->
        subqtype (subst_env_te Z V (E1 ++ E2)) (subst_tqt Z V S) (subst_tqt Z V T)).
    + (* sub_top *)
      intros Z V0 V E1 E2 HwfE HE HE2 HV HVV0. subst E.
      apply sub_top.
      * exact (wf_env_subst_te_gen (E1 ++ Z ~ bind_sub V0 ++ E2)
                 Z V0 V E1 E2 HwfE eq_refl HE2 HV).
      * exact (wf_typ_subst_drop (E1 ++ Z ~ bind_sub V0 ++ E2) S w0
                 E1 E2 Z V0 V eq_refl HwfE
                 (wf_env_subst_te_gen (E1 ++ Z ~ bind_sub V0 ++ E2)
                    Z V0 V E1 E2 HwfE eq_refl HE2 HV)
                 (subst_te_target_V_wf (E1 ++ Z ~ bind_sub V0 ++ E2)
                    Z V0 V E1 E2 HwfE eq_refl HE2 HV)).
    + (* sub_refl_tvar *)
      intros Z V0 V E1 E2 HwfE HE HE2 HV HVV0. subst E.
      simpl.
      destruct (Z == X) as [Heq|Hne].
      * subst X. simpl.
        apply sub_refl_wf.
        -- exact (subst_te_target_V_wf (E1 ++ Z ~ bind_sub V0 ++ E2) Z V0 V E1 E2 HwfE eq_refl HE2 HV).
        -- exact (wf_env_subst_te_gen (E1 ++ Z ~ bind_sub V0 ++ E2)
         Z V0 V E1 E2 HwfE eq_refl HE2 HV).
      * apply sub_refl_tvar.
        -- exact (wf_env_subst_te_gen (E1 ++ Z ~ bind_sub V0 ++ E2)
         Z V0 V E1 E2 HwfE eq_refl HE2 HV).
        -- destruct (wf_typ_fvar_inv (E1 ++ Z ~ bind_sub V0 ++ E2) X w0) as [U Hb].
           eapply wf_typ_var with (U := subst_tt Z V U).
           assert (HneXZ : X <> Z) by (intro Hc; apply Hne; symmetry; exact Hc).
           exact (binds_subst_env_te_drop E1 E2 Z V0 V X (bind_sub U) HneXZ Hb).
    + (* sub_trans_tvar *)
      intros Z V0 V E1 E2 HwfE HE HE2 HV HVV0. subst E.
      simpl.
      destruct (Z == X) as [Heq|Hne].
      * subst X. simpl.
        assert (HeqU : U = V0).
        { pose proof (binds_X_mid E1 E2 Z V0) as HbX.
          pose proof (binds_unique binding Z (bind_sub U) (bind_sub V0)
                        (E1 ++ Z ~ bind_sub V0 ++ E2) b HbX
                        (wf_env_uniq _ HwfE)) as Heqb.
          injection Heqb as ->. reflexivity. }
        subst U.
        assert (Hnotin : Z `notin` fv_tt V0).
        { eapply notin_fv_mid_bind_sub_te; eauto. }
        assert (Hbody : sub (subst_env_te Z V (E1 ++ E2)) V0
                          (subst_tt Z V T)).
        { pose proof (IHsub Z V0 V E1 E2 HwfE eq_refl HE2 HV HVV0) as Hi.
          rewrite (subst_tt_nofv Z V V0 Hnotin) in Hi.
          exact Hi. }
        eapply sub_trans_size.
        -- exact (wf_env_subst_te_gen (E1 ++ Z ~ bind_sub V0 ++ E2)
         Z V0 V E1 E2 HwfE eq_refl HE2 HV).
        -- eapply sub_weaken.
           ++ exact HE2.
           ++ exact HVV0.
           ++ exact (wf_env_subst_te_gen (E1 ++ Z ~ bind_sub V0 ++ E2)
         Z V0 V E1 E2 HwfE eq_refl HE2 HV).
           ++ rewrite subst_env_te_app.
              rewrite (subst_env_te_id Z V E2 HE2).
              ** replace (subst_env_te Z V E1 ++ E2)
                   with (subst_env_te Z V E1 ++ E2 ++ nil)
                 by (rewrite app_nil_r; reflexivity).
                 apply env_extends_insert.
              ** eapply wf_env_mid_notin_tail; eauto.
        -- exact Hbody.
      * eapply sub_trans_tvar with (U := subst_tt Z V U).
        -- assert (HneXZ : X <> Z) by (intro Hc; apply Hne; symmetry; exact Hc).
           exact (binds_subst_env_te_drop E1 E2 Z V0 V X (bind_sub U) HneXZ b).
        -- exact (IHsub Z V0 V E1 E2 HwfE eq_refl HE2 HV HVV0).
    + (* sub_arrow *)
      intros Z V0 V E1 E2 HwfE HE HE2 HV HVV0. subst E.
      simpl. apply sub_arrow.
      * exact (IHsub Z V0 V E1 E2 HwfE eq_refl HE2 HV HVV0).
      * exact (IHsub0 Z V0 V E1 E2 HwfE eq_refl HE2 HV HVV0).
    + (* sub_all *)
      intros Z V0 V E1 E2 HwfE HE HE2 HV HVV0. subst E.
      simpl.
      assert (HVtgt : wf_typ (subst_env_te Z V (E1 ++ E2)) V).
      { exact (subst_te_target_V_wf (E1 ++ Z ~ bind_sub V0 ++ E2) Z V0 V E1 E2 HwfE eq_refl HE2 HV). }
      apply sub_all with (L := union L (union (singleton Z)
        (union (dom (E1 ++ Z ~ bind_sub V0 ++ E2))
               (union (dom (subst_env_te Z V (E1 ++ E2)))
                      (union (fv_tt V) (fv_tt (subst_tt Z V T1))))))).
      * exact (IHsub Z V0 V E1 E2 HwfE eq_refl HE2 HV HVV0).
      * intros Y HY.
        assert (HYL : Y `notin` L) by fsetdec.
        assert (HYZ : Y <> Z) by fsetdec.
        assert (HYdom : Y `notin` dom (E1 ++ Z ~ bind_sub V0 ++ E2)) by fsetdec.
        assert (Hwt1 : wf_typ (E1 ++ Z ~ bind_sub V0 ++ E2) T1).
        { exact (proj1 (sub_wf (E1 ++ Z ~ bind_sub V0 ++ E2) T1 S1 HwfE H)). }
        assert (Hwfext : wf_env ((Y ~ bind_sub T1 ++ E1) ++ Z ~ bind_sub V0 ++ E2)).
        { apply wf_env_sub; [exact HwfE|exact Hwt1|exact HYdom]. }
        assert (HsubT1 : sub (subst_env_te Z V (E1 ++ E2))
                           (subst_tt Z V T1) (subst_tt Z V S1)).
        { exact (IHsub Z V0 V E1 E2 HwfE eq_refl HE2 HV HVV0). }
        assert (Htgt : wf_env (subst_env_te Z V ((Y ~ bind_sub T1 ++ E1) ++ E2))).
        { rewrite subst_env_te_cons_app.
          apply wf_env_sub.
          - exact (wf_env_subst_te_gen (E1 ++ Z ~ bind_sub V0 ++ E2) Z V0 V E1 E2 HwfE eq_refl HE2 HV).
          - exact (wf_typ_subst_drop (E1 ++ Z ~ bind_sub V0 ++ E2) T1 Hwt1
                     E1 E2 Z V0 V eq_refl HwfE
                     (wf_env_subst_te_gen (E1 ++ Z ~ bind_sub V0 ++ E2) Z V0 V E1 E2 HwfE eq_refl HE2 HV)
                     HVtgt).
          - rewrite dom_subst_env_te.
            eapply dom_mid_remove_notin_sub; eauto. }
        assert (HVext : wf_typ (subst_env_te Z V ((Y ~ bind_sub T1 ++ E1) ++ E2)) V).
        { rewrite subst_env_te_cons_app.
          eapply wf_typ_weaken.
          - exact Htgt.
          - apply env_extends_cons_tail.
          - exact HVtgt. }
        assert (HEbody : Y ~ bind_sub T1 ++ (E1 ++ Z ~ bind_sub V0 ++ E2) =
                         (Y ~ bind_sub T1 ++ E1) ++ Z ~ bind_sub V0 ++ E2).
        { rewrite app_assoc. reflexivity. }
        pose proof (H0 Y HYL Z V0 V (Y ~ bind_sub T1 ++ E1) E2
                      Hwfext HEbody HE2 HV HVV0) as Hbody.
        rewrite subst_env_te_cons_app in Hbody.
        change (subqtype
          (Y ~ bind_sub (subst_tt Z V T1) ++ subst_env_te Z V (E1 ++ E2))
          (subst_tqt Z V (open_tqt_rec 0 (typ_fvar Y) S2))
          (subst_tqt Z V (open_tqt_rec 0 (typ_fvar Y) T2))) in Hbody.
        rewrite (subst_tqt_open_tqt_wf (Y ~ bind_sub (subst_tt Z V T1) ++ subst_env_te Z V (E1 ++ E2))
                   Z V S2 0 Y HVext HYZ) in Hbody.
        rewrite (subst_tqt_open_tqt_wf (Y ~ bind_sub (subst_tt Z V T1) ++ subst_env_te Z V (E1 ++ E2))
                   Z V T2 0 Y HVext HYZ) in Hbody.
        change (subqtype
          (Y ~ bind_sub (subst_tt Z V T1) ++ subst_env_te Z V (E1 ++ E2))
          (open_tqt_rec 0 (typ_fvar Y) (subst_tqt Z V S2))
          (open_tqt_rec 0 (typ_fvar Y) (subst_tqt Z V T2))) in Hbody.
        exact Hbody.
    + (* sub_qall *)
      intros Z V0 V E1 E2 HwfE HE HE2 HV HVV0. subst E.
      simpl.
      apply sub_qall with (L := union L (union (singleton Z)
        (union (dom (E1 ++ Z ~ bind_sub V0 ++ E2))
               (union (dom (subst_env_te Z V (E1 ++ E2)))
                      (union (fv_qq T1) (fv_tqt T2)))))).
      * exact (subqual_subst_te_gen (E1 ++ Z ~ bind_sub V0 ++ E2) T1 S1 s
                  Z V0 V E1 E2 HwfE eq_refl HE2 HV).
      * intros Y HY.
        assert (HYL : Y `notin` L) by fsetdec.
        assert (HYZ : Y <> Z) by fsetdec.
        assert (HYdom : Y `notin` dom (E1 ++ Z ~ bind_sub V0 ++ E2)) by fsetdec.
        assert (Hwq : wf_qua (E1 ++ Z ~ bind_sub V0 ++ E2) T1).
        { exact (proj1 (subqual_wf (E1 ++ Z ~ bind_sub V0 ++ E2) T1 S1 HwfE s)). }
        assert (Hwfext : wf_env (Y ~ bind_qua T1 ++ (E1 ++ Z ~ bind_sub V0 ++ E2))).
        { apply wf_env_qua; [exact HwfE|exact Hwq|exact HYdom]. }
        assert (HVtgt : wf_typ (subst_env_te Z V (E1 ++ E2)) V).
        { exact (subst_te_target_V_wf (E1 ++ Z ~ bind_sub V0 ++ E2) Z V0 V E1 E2 HwfE eq_refl HE2 HV). }
        assert (Htgt : wf_env (subst_env_te Z V ((Y ~ bind_qua T1 ++ E1) ++ E2))).
        { rewrite subst_env_te_cons_app.
          apply wf_env_qua.
          - exact (wf_env_subst_te_gen (E1 ++ Z ~ bind_sub V0 ++ E2)
         Z V0 V E1 E2 HwfE eq_refl HE2 HV).
          - eapply wf_qua_subst_env_te_mid; eauto.
          - rewrite dom_subst_env_te.
            eapply dom_mid_remove_notin_sub; eauto. }
        assert (HVext : wf_typ (subst_env_te Z V ((Y ~ bind_qua T1 ++ E1) ++ E2)) V).
        { rewrite subst_env_te_cons_app.
          eapply wf_typ_weaken.
          - exact Htgt.
          - apply env_extends_cons_tail.
          - exact HVtgt. }
        assert (HEbody : Y ~ bind_qua T1 ++ (E1 ++ Z ~ bind_sub V0 ++ E2) =
                         (Y ~ bind_qua T1 ++ E1) ++ Z ~ bind_sub V0 ++ E2).
        { rewrite app_assoc. reflexivity. }
        pose proof (H Y HYL Z V0 V (Y ~ bind_qua T1 ++ E1) E2
                      Hwfext HEbody HE2 HV HVV0) as Hbody.
        rewrite subst_env_te_cons_app in Hbody.
        change (subqtype
          (Y ~ bind_qua T1 ++ subst_env_te Z V (E1 ++ E2))
          (subst_tqt Z V (open_qqt_rec 0 (qua_fvar Y) S2))
          (subst_tqt Z V (open_qqt_rec 0 (qua_fvar Y) T2))) in Hbody.
        rewrite (subst_tqt_open_qqt_wf (Y ~ bind_qua T1 ++ subst_env_te Z V (E1 ++ E2))
                   Z V S2 0 Y HVext HYZ) in Hbody.
        rewrite (subst_tqt_open_qqt_wf (Y ~ bind_qua T1 ++ subst_env_te Z V (E1 ++ E2))
                   Z V T2 0 Y HVext HYZ) in Hbody.
        change (subqtype
          (Y ~ bind_qua T1 ++ subst_env_te Z V (E1 ++ E2))
          (open_qqt_rec 0 (qua_fvar Y) (subst_tqt Z V S2))
          (open_qqt_rec 0 (qua_fvar Y) (subst_tqt Z V T2))) in Hbody.
        exact Hbody.
    + (* sub_sum *)
      intros Z V0 V E1 E2 HwfE HE HE2 HV HVV0. subst E.
      simpl. apply sub_sum.
      * exact (IHsub Z V0 V E1 E2 HwfE eq_refl HE2 HV HVV0).
      * exact (IHsub0 Z V0 V E1 E2 HwfE eq_refl HE2 HV HVV0).
    + (* sub_pair *)
      intros Z V0 V E1 E2 HwfE HE HE2 HV HVV0. subst E.
      simpl. apply sub_pair.
      * exact (IHsub Z V0 V E1 E2 HwfE eq_refl HE2 HV HVV0).
      * exact (IHsub0 Z V0 V E1 E2 HwfE eq_refl HE2 HV HVV0).
    + (* sub_qtyp_qtyp *)
      intros Z V0 V E1 E2 HwfE HE HE2 HV HVV0. subst E.
      simpl. apply sub_qtyp_qtyp.
      * exact (subqual_subst_te_gen
                 (E1 ++ Z ~ bind_sub V0 ++ E2) Q1 Q2 s
                 Z V0 V E1 E2 HwfE eq_refl HE2 HV).
      * exact (IHsub Z V0 V E1 E2 HwfE eq_refl HE2 HV HVV0).
  - intros E S T H. destruct S as [Q1 T1]. destruct T as [Q2 T2].
    inversion H; subst.
    intros Z V0 V E1 E2 HwfE HE HE2 HV HVV0.
    simpl. apply sub_qtyp_qtyp.
    + exact (subqual_subst_te_gen E Q1 Q2 H4
                Z V0 V E1 E2 HwfE HE HE2 HV).
    + exact (sub_subst_te_gen E T1 T2 H6
                Z V0 V E1 E2 HwfE HE HE2 HV HVV0).
Qed.


(* ===== inlined from /tmp/w3/QeSubst.v ===== *)

(* ===================================================================== *)
(* Binds lemmas under qualifier substitution                             *)
(* ===================================================================== *)

(* We need a version of [binds_subst_env_qe_map] that also applies when
   the bound name is the substituted one.  The proof is the same as in
   W3.Direct; the side condition [y <> X] there is not actually used.   *)
Lemma binds_subst_env_qe_map_any : forall X R E y b,
  binds y b E -> binds y (subst_bind_qe X R b) (subst_env_qe X R E).
Proof.
  intros X R E. induction E as [|[z c] E IH]; intros y b Hb.
  - destruct Hb.
  - simpl in Hb. destruct Hb as [Heq|Hin].
    + injection Heq as -> ->.
      unfold subst_env_qe. simpl. left. reflexivity.
    + unfold subst_env_qe in *. simpl. right. apply IH; assumption.
Qed.

Lemma binds_subst_env_qe_drop : forall E1 E2 X R0 R y b,
  y <> X ->
  binds y b (E1 ++ X ~ bind_qua R0 ++ E2) ->
  binds y (subst_bind_qe X R b) (subst_env_qe X R (E1 ++ E2)).
Proof.
  intros E1 E2 X R0 R y b Hne Hb.
  apply binds_app_1 in Hb. destruct Hb as [Hb1|Hb2].
  - rewrite subst_env_qe_app. apply binds_app_l. apply binds_subst_env_qe_map; assumption.
  - apply binds_cons_1 in Hb2. destruct Hb2 as [[Heq Hbeq]|Hb2].
    + subst y. exfalso; apply Hne; reflexivity.
    + rewrite subst_env_qe_app. apply binds_app_r. apply binds_subst_env_qe_map; assumption.
Qed.

(* A [bind_qua] binding is mapped to the binding of the substituted
   qualifier; this holds even at the substituted atom itself. *)
Lemma binds_subst_env_qe_qua : forall X R E y Q,
  binds y (bind_qua Q) E ->
  binds y (bind_qua (subst_qq X R Q)) (subst_env_qe X R E).
Proof.
  intros X R E y Q H.
  exact (binds_subst_env_qe_map_any X R E y (bind_qua Q) H).
Qed.

Lemma wf_qua_subst_env_qe : forall E Q,
  wf_qua E Q -> forall X R,
  wf_qua (subst_env_qe X R E) R ->
  wf_qua (subst_env_qe X R E) (subst_qq X R Q).
Proof.
  intros E Q H. induction H; intros X0 R0 HR.
  - apply wf_qua_top.
  - simpl. destruct (X0 == X) as [Heq|Hne].
    + subst X. simpl. exact HR.
    + apply wf_qua_fvar with (R := subst_qq X0 R0 R).
      exact (binds_subst_env_qe_map_any X0 R0 E X (bind_qua R) H).
  - simpl. apply wf_qua_meet; [apply IHwf_qua1|apply IHwf_qua2]; exact HR.
  - simpl. apply wf_qua_join; [apply IHwf_qua1|apply IHwf_qua2]; exact HR.
  - apply wf_qua_bot.
Qed.

Lemma subst_env_qe_cons_app : forall X R y b E1 E2,
  subst_env_qe X R ((y ~ b ++ E1) ++ E2) =
  y ~ subst_bind_qe X R b ++ subst_env_qe X R (E1 ++ E2).
Proof.
  intros. simpl. rewrite subst_env_qe_app. reflexivity.
Qed.

(* ===================================================================== *)
(* Domain lemmas                                                          *)
(* ===================================================================== *)

Lemma dom_mid_remove_notin_any : forall (E1 E2 : env) (x : atom)
  (b : binding) (X : atom),
  X `notin` dom (E1 ++ x ~ b ++ E2) -> X `notin` dom (E1 ++ E2).
Proof.
  intros E1 E2 x b X H. rewrite dom_app in *. rewrite dom_app in H. fsetdec.
Qed.

(* ===================================================================== *)
(* Removing a qualifier binder in the middle of an environment, while    *)
(* substituting its variable by the replacement qualifier.               *)
(* ===================================================================== *)

Lemma wf_qua_mid_remove_qe : forall (E1 E2 : env) (x : atom)
  (Rq Rout : qua) (Q : qua),
  wf_env (E1 ++ x ~ bind_qua Rq ++ E2) ->
  wf_qua (E1 ++ x ~ bind_qua Rq ++ E2) Q ->
  wf_qua (subst_env_qe x Rout (E1 ++ E2)) Rout ->
  wf_qua (subst_env_qe x Rout (E1 ++ E2)) (subst_qq x Rout Q).
Proof.
  intros E1 E2 x Rq Rout Q Hwf Hq.
  remember (E1 ++ x ~ bind_qua Rq ++ E2) as E eqn:HE.
  revert E1 E2 x Rq Hwf HE.
  induction Hq; intros E1 E2 x0 Rq0 Hwf HE HR.
  - apply wf_qua_top.
  - simpl. destruct (x0 == X) as [Heq|Hne].
    + subst X. simpl. exact HR.
    + subst E. apply wf_qua_fvar with (R := subst_qq x0 Rout R).
      assert (Xneq : X <> x0) by (intro Hc; apply Hne; symmetry; exact Hc).
      exact (binds_subst_env_qe_map_any x0 Rout (E1 ++ E2) X (bind_qua R)
               (binds_mid_remove_any E1 E2 x0 (bind_qua Rq0) X (bind_qua R) Xneq H)).
  - subst E. simpl. apply wf_qua_meet.
    + apply (IHHq1 E1 E2 x0 Rq0 Hwf eq_refl HR).
    + apply (IHHq2 E1 E2 x0 Rq0 Hwf eq_refl HR).
  - subst E. simpl. apply wf_qua_join.
    + apply (IHHq1 E1 E2 x0 Rq0 Hwf eq_refl HR).
    + apply (IHHq2 E1 E2 x0 Rq0 Hwf eq_refl HR).
  - apply wf_qua_bot.
Qed.

(* Removing a term binder in the middle of an environment.  (W1.Shape
   has the front-position case; here we transport along
   [env_subqua_extends_mid] instead, which works for any position.) *)
Lemma wf_qua_mid_remove_typ : forall (E1 E2 : env) (x : atom)
  (V : qtyp) (Q : qua),
  wf_env (E1 ++ x ~ bind_typ V ++ E2) ->
  wf_qua (E1 ++ x ~ bind_typ V ++ E2) Q -> wf_qua (E1 ++ E2) Q.
Proof.
  intros E1 E2 x V Q Hwf Hq.
  eapply wf_qua_subqua.
  - exact Hq.
  - apply env_subqua_extends_mid. exact Hwf.
Qed.

(* ===================================================================== *)
(* Substitution of a qualifier variable through well-formed types,        *)
(* removing its [bind_qua] binder from the environment.                   *)
(* ===================================================================== *)

Definition Pwf_qe (E : env) (T : typ) (H : wf_typ E T) : Prop :=
  forall E1 E2 (X : atom) (R0 R : qua),
    E = E1 ++ X ~ bind_qua R0 ++ E2 ->
    wf_env E ->
    wf_env (subst_env_qe X R (E1 ++ E2)) ->
    wf_qua (subst_env_qe X R (E1 ++ E2)) R ->
    wf_typ (subst_env_qe X R (E1 ++ E2)) (subst_qt X R T).

Definition Pwfq_qe (E : env) (T : qtyp) (H : wf_qtyp E T) : Prop :=
  forall E1 E2 (X : atom) (R0 R : qua),
    E = E1 ++ X ~ bind_qua R0 ++ E2 ->
    wf_env E ->
    wf_env (subst_env_qe X R (E1 ++ E2)) ->
    wf_qua (subst_env_qe X R (E1 ++ E2)) R ->
    wf_qtyp (subst_env_qe X R (E1 ++ E2)) (subst_qqt X R T).

Lemma wf_typ_subst_drop_qe : forall E T (H : wf_typ E T), Pwf_qe E T H
with wf_qtyp_subst_drop_qe : forall E T (H : wf_qtyp E T), Pwfq_qe E T H.
Proof.
  - intros E T H.
    refine (wf_typ_mut_ind Pwf_qe Pwfq_qe _ _ _ _ _ _ _ _ E T H).
    + intros E0. unfold Pwf_qe.
      intros E1 E2 X R0 R HE HwfE Hwtgt2 HRtgt. apply wf_typ_top.
    + intros U E0 Y b E1 E2 X R0 R HE HwfE Hwtgt2 HRtgt.
      subst E0.
      simpl.
      destruct (eq_dec Y X) as [Heq|Hne].
      * subst Y. exfalso.
        assert (Hbq : binds X (bind_qua R0) (E1 ++ X ~ bind_qua R0 ++ E2)).
        { apply binds_app_r, binds_app_l, binds_cons_2; reflexivity. }
        pose proof (binds_unique binding X (bind_sub U) (bind_qua R0)
                      (E1 ++ X ~ bind_qua R0 ++ E2) b Hbq (wf_env_uniq _ HwfE)) as Heqb.
        discriminate Heqb.
      * eapply wf_typ_var.
        eapply (binds_subst_env_qe_drop E1 E2 X R0 R Y (bind_sub U)).
        -- exact Hne.
        -- exact b.
    + intros E0 T1 T2 w IHw w0 IHw0 E1 E2 X R0 R HE HwfE Hwtgt2 HRtgt.
      subst E0. simpl. apply wf_typ_arrow.
      * apply (IHw E1 E2 X R0 R eq_refl HwfE Hwtgt2 HRtgt).
      * apply (IHw0 E1 E2 X R0 R eq_refl HwfE Hwtgt2 HRtgt).
    + intros L E0 T1 T2 w IHw w0 IHw0 E1 E2 X R0 R HE HwfE Hwtgt2 HRtgt.
      subst E0.
      simpl.
      apply wf_typ_all with (L := union L (union (singleton X)
        (union (dom (E1 ++ X ~ bind_qua R0 ++ E2)) (dom (subst_env_qe X R (E1 ++ E2)))))).
      * apply (IHw E1 E2 X R0 R eq_refl HwfE Hwtgt2 HRtgt).
      * intros Y HY.
        assert (HYL : Y `notin` L) by fsetdec.
        assert (HYX : Y <> X) by fsetdec.
        assert (HYdom : Y `notin` dom (E1 ++ X ~ bind_qua R0 ++ E2)) by fsetdec.
        assert (Hwfold' : wf_env ((Y ~ bind_sub T1 ++ E1) ++ X ~ bind_qua R0 ++ E2)).
        { simpl. apply wf_env_sub.
          - exact HwfE.
          - exact w.
          - exact HYdom. }
        assert (HsubT1 : wf_typ (subst_env_qe X R (E1 ++ E2)) (subst_qt X R T1)).
        { apply (IHw E1 E2 X R0 R eq_refl HwfE Hwtgt2 HRtgt). }
        assert (HYtgt : Y `notin` dom (subst_env_qe X R (E1 ++ E2))).
        { rewrite dom_subst_env_qe. apply dom_mid_remove_notin_any with (x:=X)(b:=bind_qua R0). exact HYdom. }
        assert (HwfE' : wf_env (subst_env_qe X R ((Y ~ bind_sub T1 ++ E1) ++ E2))).
        { rewrite subst_env_qe_cons_app. apply wf_env_sub; [exact Hwtgt2|exact HsubT1|exact HYtgt]. }
        assert (HV' : wf_qua (subst_env_qe X R ((Y ~ bind_sub T1 ++ E1) ++ E2)) R).
        { rewrite subst_env_qe_cons_app. exact (wf_qua_weaken (subst_env_qe X R (E1++E2))
            (Y ~ bind_sub (subst_qt X R T1) ++ subst_env_qe X R (E1++E2)) R HwfE'
            (env_extends_cons_tail (subst_env_qe X R (E1++E2)) Y (bind_sub (subst_qt X R T1))) HRtgt). }
        assert (HEq : Y ~ bind_sub T1 ++ (E1 ++ X ~ bind_qua R0 ++ E2) =
                      (Y ~ bind_sub T1 ++ E1) ++ X ~ bind_qua R0 ++ E2).
        { rewrite app_assoc. reflexivity. }
        pose proof (IHw0 Y HYL (Y ~ bind_sub T1 ++ E1) E2 X R0 R HEq Hwfold' HwfE' HV') as Hbody.
        rewrite subst_env_qe_cons_app in Hbody.
        change (wf_qtyp (subst_env_qe X R ((Y ~ bind_sub T1 ++ E1) ++ E2))
                 (subst_qqt X R (open_tqt_rec 0 (typ_fvar Y) T2))) in Hbody.
        rewrite (subst_qqt_open_tqt X R T2 0 Y) in Hbody.
        change (wf_qtyp (subst_env_qe X R ((Y ~ bind_sub T1 ++ E1) ++ E2))
                 (open_tqt_rec 0 (typ_fvar Y) (subst_qqt X R T2))) in Hbody.
        exact Hbody.
    + intros L E0 Qv T2 Hq w0 IHw0 E1 E2 X R0 R HE HwfE Hwtgt2 HRtgt.
      subst E0.
      simpl.
      apply wf_typ_qall with (L := union L (union (singleton X)
        (union (dom (E1 ++ X ~ bind_qua R0 ++ E2)) (dom (subst_env_qe X R (E1 ++ E2)))))).
      * apply wf_qua_mid_remove_qe with (Rq := R0); [exact HwfE | exact Hq | exact HRtgt].
      * intros Y HY.
        assert (HYL : Y `notin` L) by fsetdec.
        assert (HYX : Y <> X) by fsetdec.
        assert (HYdom : Y `notin` dom (E1 ++ X ~ bind_qua R0 ++ E2)) by fsetdec.
        assert (HYtgt : Y `notin` dom (subst_env_qe X R (E1 ++ E2))).
        { rewrite dom_subst_env_qe. apply dom_mid_remove_notin_any with (x:=X)(b:=bind_qua R0). exact HYdom. }
        assert (Hwqbody : wf_qua (subst_env_qe X R (E1 ++ E2)) (subst_qq X R Qv)).
        { apply wf_qua_mid_remove_qe with (Rq := R0); [exact HwfE | exact Hq | exact HRtgt]. }
        assert (Hwfold' : wf_env (Y ~ bind_qua Qv ++ (E1 ++ X ~ bind_qua R0 ++ E2))).
        { apply wf_env_qua; [exact HwfE|exact Hq|exact HYdom]. }
        assert (HwfE' : wf_env (subst_env_qe X R ((Y ~ bind_qua Qv ++ E1) ++ E2))).
        { rewrite subst_env_qe_cons_app. apply wf_env_qua; [exact Hwtgt2|exact Hwqbody|exact HYtgt]. }
        assert (HV' : wf_qua (subst_env_qe X R ((Y ~ bind_qua Qv ++ E1) ++ E2)) R).
        { rewrite subst_env_qe_cons_app. exact (wf_qua_weaken (subst_env_qe X R (E1++E2))
            (Y ~ bind_qua (subst_qq X R Qv) ++ subst_env_qe X R (E1++E2)) R HwfE'
            (env_extends_cons_tail (subst_env_qe X R (E1++E2)) Y (bind_qua (subst_qq X R Qv))) HRtgt). }
        assert (HEq : Y ~ bind_qua Qv ++ (E1 ++ X ~ bind_qua R0 ++ E2) =
                      (Y ~ bind_qua Qv ++ E1) ++ X ~ bind_qua R0 ++ E2).
        { rewrite app_assoc. reflexivity. }
        pose proof (IHw0 Y HYL (Y ~ bind_qua Qv ++ E1) E2 X R0 R HEq Hwfold' HwfE' HV') as Hbody.
        rewrite subst_env_qe_cons_app in Hbody.
        change (wf_qtyp (subst_env_qe X R ((Y ~ bind_qua Qv ++ E1) ++ E2))
                 (subst_qqt X R (open_qqt_rec 0 (qua_fvar Y) T2))) in Hbody.
        rewrite (subst_qqt_open_qqt_wf (subst_env_qe X R (E1++E2)) X R T2 0 Y HRtgt HYX) in Hbody.
        change (wf_qtyp (subst_env_qe X R ((Y ~ bind_qua Qv ++ E1) ++ E2))
                 (open_qqt_rec 0 (qua_fvar Y) (subst_qqt X R T2))) in Hbody.
        exact Hbody.
    + intros E0 T1 T2 w IHw w0 IHw0 E1 E2 X R0 R HE HwfE Hwtgt2 HRtgt.
      subst E0. simpl. apply wf_typ_sum.
      * apply (IHw E1 E2 X R0 R eq_refl HwfE Hwtgt2 HRtgt).
      * apply (IHw0 E1 E2 X R0 R eq_refl HwfE Hwtgt2 HRtgt).
    + intros E0 T1 T2 w IHw w0 IHw0 E1 E2 X R0 R HE HwfE Hwtgt2 HRtgt.
      subst E0. simpl. apply wf_typ_pair.
      * apply (IHw E1 E2 X R0 R eq_refl HwfE Hwtgt2 HRtgt).
      * apply (IHw0 E1 E2 X R0 R eq_refl HwfE Hwtgt2 HRtgt).
    + intros E0 Q0 T0 w w0 IHw0 E1 E2 X R0 R HE HwfE Hwtgt2 HRtgt.
      subst E0. simpl. apply wf_qtyp_qtyp.
      * apply wf_qua_mid_remove_qe with (Rq := R0); [exact HwfE | exact w | exact HRtgt].
      * apply (IHw0 E1 E2 X R0 R eq_refl HwfE Hwtgt2 HRtgt).
  - intros E T H. destruct T as [Q T0].
    inversion H as [E0 Q0 T0' Hq HT]; subst.
    unfold Pwfq_qe. intros E1 E2 X R0 R HE HwfE Hwtgt2 HRtgt.
    rewrite HE in HwfE. rewrite HE in Hq. rewrite HE in HT.
    simpl. apply wf_qtyp_qtyp.
    + apply wf_qua_mid_remove_qe with (Rq := R0); [exact HwfE | exact Hq | exact HRtgt].
    + exact (wf_typ_subst_drop_qe (E1 ++ X ~ bind_qua R0 ++ E2) T0 HT
               E1 E2 X R0 R eq_refl HwfE Hwtgt2 HRtgt).
Qed.

(* ===================================================================== *)
(* Opening a qualifier variable at a fresh atom                          *)
(* ===================================================================== *)

Lemma wf_qtyp_open_qe_fresh : forall (E : env) (X : atom) (R0 R : qua) (T : qtyp),
  wf_env E -> X `notin` dom E -> X `notin` fv_tqt T ->
  wf_qua E R0 -> wf_qua E R ->
  wf_qtyp (X ~ bind_qua R0 ++ E) (open_qqt T X) ->
  wf_qtyp E (open_qqt T R).
Proof.
  intros E X R0 R T HwfE HdomX Hfv HR0 HR Hbody.
  assert (HwfEold : wf_env (X ~ bind_qua R0 ++ E))
    by (apply wf_env_qua; assumption).
  assert (Hwtgt : wf_env (subst_env_qe X R (nil ++ E)))
    by (simpl; rewrite (subst_env_qe_id X R E HwfE HdomX); exact HwfE).
  assert (HRtgt : wf_qua (subst_env_qe X R (nil ++ E)) R)
    by (simpl; rewrite (subst_env_qe_id X R E HwfE HdomX); exact HR).
  pose proof (wf_qtyp_subst_drop_qe (X ~ bind_qua R0 ++ E) (open_qqt T X) Hbody
                nil E X R0 R eq_refl HwfEold Hwtgt HRtgt) as Hres.
  simpl in Hres.
  rewrite (subst_env_qe_id X R E HwfE HdomX) in Hres.
  change (wf_qtyp E (subst_qqt X R (open_qqt_rec 0 (qua_fvar X) T))) in Hres.
  rewrite (subst_qqt_open_same T 0 X R Hfv) in Hres.
  change (wf_qtyp E (open_qqt_rec 0 R T)) in Hres.
  exact Hres.
Qed.


(* ===== inlined from /tmp/w3/QeGen.v ===== *)

Lemma wf_qua_subst_env_qe_base : forall (X : atom) (R : qua) E1 E2,
  wf_env E2 ->
  wf_env (subst_env_qe X R (E1 ++ E2)) ->
  X `notin` dom E2 ->
  wf_qua E2 R ->
  wf_qua (subst_env_qe X R (E1 ++ E2)) R.
Proof.
  intros X R E1 E2 HE2 Htgt HX HR.
  rewrite subst_env_qe_app in Htgt.
  rewrite (subst_env_qe_id X R E2 HE2 HX) in Htgt.
  rewrite subst_env_qe_app.
  rewrite (subst_env_qe_id X R E2 HE2 HX).
  eapply wf_qua_weaken; [exact Htgt| |exact HR].
  replace (subst_env_qe X R E1 ++ E2)
    with (subst_env_qe X R E1 ++ E2 ++ nil).
  - apply env_extends_insert.
  - rewrite app_nil_r; reflexivity.
Qed.

Lemma notin_dom_subst_env_qe_mid : forall E1 E2 (X : atom) (R0 R : qua) y,
  y `notin` dom (E1 ++ X ~ bind_qua R0 ++ E2) ->
  y `notin` dom (subst_env_qe X R (E1 ++ E2)).
Proof.
  intros. rewrite dom_subst_env_qe.
  eapply dom_mid_remove_notin_any; eauto.
Qed.

Lemma wf_env_subst_qe_gen : forall E (X : atom) (R0 R : qua) E1 E2,
  wf_env E ->
  E = E1 ++ X ~ bind_qua R0 ++ E2 ->
  wf_env E2 ->
  wf_qua E2 R ->
  wf_env (subst_env_qe X R (E1 ++ E2)).
Proof.
  intros E X R0 R E1. revert E X R0 R.
  induction E1 as [|[y b] E1 IH];
    intros E X R0 R E2 Hwf HE HE2 HR.
  - simpl in HE. subst E.
    change (wf_env (subst_env_qe X R E2)).
    assert (Heq : subst_env_qe X R E2 = E2).
    { apply subst_env_qe_id.
      - exact HE2.
      - apply (wf_env_mid_notin_tail nil X (bind_qua R0) E2).
        exact Hwf. }
    rewrite Heq. exact HE2.
  - simpl in HE. subst E.
    simpl in Hwf.
    destruct (wf_env_cons_inv y b (E1 ++ X ~ bind_qua R0 ++ E2) Hwf)
      as [Htail [Hy Hbf]].
    assert (Htgt : wf_env (subst_env_qe X R (E1 ++ E2))).
    { eapply IH; [exact Htail|reflexivity|exact HE2|exact HR]. }
    assert (HXnotin : X `notin` dom E2) by (eapply wf_env_mid_notin_tail; eauto).
    assert (HRtgt : wf_qua (subst_env_qe X R (E1 ++ E2)) R).
    { eapply wf_qua_subst_env_qe_base; eauto. }
    assert (Hytgt : y `notin` dom (subst_env_qe X R (E1 ++ E2))).
    { eapply notin_dom_subst_env_qe_mid; eauto. }
    change (wf_env (subst_env_qe X R ((y ~ b ++ E1) ++ E2))).
    rewrite subst_env_qe_cons_app.
    destruct b as [T|T|Q].
    + simpl. apply wf_env_sub; [exact Htgt| |exact Hytgt].
      eapply (wf_typ_subst_drop_qe (E1 ++ X ~ bind_qua R0 ++ E2) T Hbf
                E1 E2 X R0 R eq_refl Htail Htgt HRtgt).
    + simpl. apply wf_env_typ; [exact Htgt| |exact Hytgt].
      eapply (wf_qtyp_subst_drop_qe (E1 ++ X ~ bind_qua R0 ++ E2) T Hbf
                E1 E2 X R0 R eq_refl Htail Htgt HRtgt).
    + simpl. apply wf_env_qua; [exact Htgt| |exact Hytgt].
      eapply wf_qua_mid_remove_qe; [exact Htail|exact Hbf|exact HRtgt].
Qed.

Lemma binds_X_mid_qua : forall E1 E2 X R0,
  binds X (bind_qua R0) (E1 ++ X ~ bind_qua R0 ++ E2).
Proof.
  intros. apply binds_app_r, binds_app_l, binds_cons_2; reflexivity.
Qed.

Lemma wf_qua_fvar_inv : forall E X,
  wf_qua E (qua_fvar X) -> exists R, binds X (bind_qua R) E.
Proof.
  intros E X H. inversion H; subst. eauto.
Qed.

Lemma subst_qe_target_R_wf : forall E (Z : atom) (R0 R : qua) E1 E2,
  wf_env E -> E = E1 ++ Z ~ bind_qua R0 ++ E2 ->
  wf_env E2 -> wf_qua E2 R ->
  wf_qua (subst_env_qe Z R (E1 ++ E2)) R.
Proof.
  intros. eapply wf_qua_subst_env_qe_base.
  - exact H1.
  - exact (wf_env_subst_qe_gen E Z R0 R E1 E2 H H0 H1 H2).
  - eapply wf_env_mid_notin_tail.
    rewrite <- H0. exact H.
  - exact H2.
Qed.

Lemma notin_fv_mid_bind_qua_qe : forall E1 E2 (Z : atom) (R0 : qua),
  wf_env (E1 ++ Z ~ bind_qua R0 ++ E2) -> Z `notin` fv_qq R0.
Proof.
  intros E1 E2 Z R0 Hwf Hc.
  assert (HZdom : Z `notin` dom E2) by (eapply wf_env_mid_notin_tail; eauto).
  apply HZdom.
  eapply wf_qua_fv_dom.
  - exact (wf_env_mid_bind_wf E1 Z (bind_qua R0) E2 Hwf).
  - exact Hc.
Qed.

Lemma subqual_subst_qe_gen : forall E Q R, subqual E Q R ->
  forall (Z : atom) (R0 S : qua) E1 E2,
    wf_env E -> E = E1 ++ Z ~ bind_qua R0 ++ E2 ->
    wf_env E2 -> wf_qua E2 S -> subqual E2 S R0 ->
    subqual (subst_env_qe Z S (E1 ++ E2))
            (subst_qq Z S Q) (subst_qq Z S R).
Proof.
  intros E Q R H. induction H; intros Z R0 S E1 E2 HwfE HE HE2 HS HSR0.
  - subst E. simpl. apply subqual_top.
    + exact (wf_env_subst_qe_gen (E1 ++ Z ~ bind_qua R0 ++ E2)
               Z R0 S E1 E2 HwfE eq_refl HE2 HS).
    + eapply wf_qua_mid_remove_qe; [exact HwfE|assumption|].
      exact (subst_qe_target_R_wf (E1 ++ Z ~ bind_qua R0 ++ E2)
               Z R0 S E1 E2 HwfE eq_refl HE2 HS).
  - subst E. simpl. apply subqual_bot.
    + exact (wf_env_subst_qe_gen (E1 ++ Z ~ bind_qua R0 ++ E2)
               Z R0 S E1 E2 HwfE eq_refl HE2 HS).
    + eapply wf_qua_mid_remove_qe; [exact HwfE|assumption|].
      exact (subst_qe_target_R_wf (E1 ++ Z ~ bind_qua R0 ++ E2)
               Z R0 S E1 E2 HwfE eq_refl HE2 HS).
  - subst E. simpl.
    destruct (Z == X) as [Heq|Hne].
    + subst X. simpl. apply subqual_refl.
      * exact (wf_env_subst_qe_gen (E1 ++ Z ~ bind_qua R0 ++ E2)
                 Z R0 S E1 E2 HwfE eq_refl HE2 HS).
      * exact (subst_qe_target_R_wf (E1 ++ Z ~ bind_qua R0 ++ E2)
                 Z R0 S E1 E2 HwfE eq_refl HE2 HS).
    + apply subqual_refl_qvar.
      * exact (wf_env_subst_qe_gen (E1 ++ Z ~ bind_qua R0 ++ E2)
                 Z R0 S E1 E2 HwfE eq_refl HE2 HS).
      * destruct (wf_qua_fvar_inv (E1 ++ Z ~ bind_qua R0 ++ E2) X H0) as [Rq Hb].
        apply wf_qua_fvar with (R := subst_qq Z S Rq).
        assert (HneXZ : X <> Z) by (intro Hc; apply Hne; symmetry; exact Hc).
        exact (binds_subst_env_qe_drop E1 E2 Z R0 S X (bind_qua Rq) HneXZ Hb).
  - subst E. simpl.
    destruct (Z == X) as [Heq|Hne].
    + subst X. simpl.
      assert (HeqR : R = R0).
      { pose proof (binds_X_mid_qua E1 E2 Z R0) as HbZ.
        match goal with
        | HbR : binds Z (bind_qua R) (E1 ++ Z ~ bind_qua R0 ++ E2) |- _ =>
            pose proof (binds_unique binding Z (bind_qua R) (bind_qua R0)
                          (E1 ++ Z ~ bind_qua R0 ++ E2) HbR HbZ
                          (wf_env_uniq _ HwfE)) as Heqb
        end.
        injection Heqb as ->. reflexivity. }
      subst R.
      assert (Hnotin : Z `notin` fv_qq R0).
      { eapply notin_fv_mid_bind_qua_qe; eauto. }
      assert (HSR0tgt : subqual (subst_env_qe Z S (E1 ++ E2)) S R0).
      { eapply subqual_weaken.
        - exact HSR0.
        - exact (wf_env_subst_qe_gen (E1 ++ Z ~ bind_qua R0 ++ E2)
                   Z R0 S E1 E2 HwfE eq_refl HE2 HS).
        - rewrite subst_env_qe_app.
          rewrite (subst_env_qe_id Z S E2 HE2).
          * replace (subst_env_qe Z S E1 ++ E2)
              with (subst_env_qe Z S E1 ++ E2 ++ nil)
            by (rewrite app_nil_r; reflexivity).
            apply env_extends_insert.
          * eapply wf_env_mid_notin_tail; eauto. }
      eapply subqual_trans_nowf; [exact HSR0tgt|].
      pose proof (IHsubqual Z R0 S E1 E2 HwfE eq_refl HE2 HS HSR0) as Hi.
      rewrite (subst_qq_nofv Z S R0 Hnotin) in Hi.
      exact Hi.
    + eapply subqual_trans_qvar.
      * assert (HneXZ : X <> Z) by (intro Hc; apply Hne; symmetry; exact Hc).
        match goal with
        | Hb : binds X (bind_qua R) (E1 ++ Z ~ bind_qua R0 ++ E2) |- _ =>
            exact (binds_subst_env_qe_drop E1 E2 Z R0 S X (bind_qua R) HneXZ Hb)
        end.
      * exact (IHsubqual Z R0 S E1 E2 HwfE eq_refl HE2 HS HSR0).
  - subst E. simpl. apply subqual_join_inl.
    + exact (IHsubqual Z R0 S E1 E2 HwfE eq_refl HE2 HS HSR0).
    + eapply wf_qua_mid_remove_qe; [exact HwfE|assumption|].
      exact (subst_qe_target_R_wf (E1 ++ Z ~ bind_qua R0 ++ E2)
               Z R0 S E1 E2 HwfE eq_refl HE2 HS).
  - subst E. simpl. apply subqual_join_inr.
    + eapply wf_qua_mid_remove_qe; [exact HwfE|assumption|].
      exact (subst_qe_target_R_wf (E1 ++ Z ~ bind_qua R0 ++ E2)
               Z R0 S E1 E2 HwfE eq_refl HE2 HS).
    + exact (IHsubqual Z R0 S E1 E2 HwfE eq_refl HE2 HS HSR0).
  - subst E. simpl. apply subqual_join_elim.
    + exact (IHsubqual1 Z R0 S E1 E2 HwfE eq_refl HE2 HS HSR0).
    + exact (IHsubqual2 Z R0 S E1 E2 HwfE eq_refl HE2 HS HSR0).
  - subst E. simpl. apply subqual_meet_eliml.
    + exact (IHsubqual Z R0 S E1 E2 HwfE eq_refl HE2 HS HSR0).
    + eapply wf_qua_mid_remove_qe; [exact HwfE|assumption|].
      exact (subst_qe_target_R_wf (E1 ++ Z ~ bind_qua R0 ++ E2)
               Z R0 S E1 E2 HwfE eq_refl HE2 HS).
  - subst E. simpl. apply subqual_meet_elimr.
    + eapply wf_qua_mid_remove_qe; [exact HwfE|assumption|].
      exact (subst_qe_target_R_wf (E1 ++ Z ~ bind_qua R0 ++ E2)
               Z R0 S E1 E2 HwfE eq_refl HE2 HS).
    + exact (IHsubqual Z R0 S E1 E2 HwfE eq_refl HE2 HS HSR0).
  - subst E. simpl. apply subqual_meet_intro.
    + exact (IHsubqual1 Z R0 S E1 E2 HwfE eq_refl HE2 HS HSR0).
    + exact (IHsubqual2 Z R0 S E1 E2 HwfE eq_refl HE2 HS HSR0).
Qed.

Lemma sub_subst_qe_gen : forall E S T, sub E S T ->
  forall (Z : atom) (R0 R : qua) E1 E2,
    wf_env E -> E = E1 ++ Z ~ bind_qua R0 ++ E2 ->
    wf_env E2 -> wf_qua E2 R -> subqual E2 R R0 ->
    sub (subst_env_qe Z R (E1 ++ E2)) (subst_qt Z R S) (subst_qt Z R T)
with subqtype_subst_qe_gen : forall E S T, subqtype E S T ->
  forall (Z : atom) (R0 R : qua) E1 E2,
    wf_env E -> E = E1 ++ Z ~ bind_qua R0 ++ E2 ->
    wf_env E2 -> wf_qua E2 R -> subqual E2 R R0 ->
    subqtype (subst_env_qe Z R (E1 ++ E2)) (subst_qqt Z R S) (subst_qqt Z R T).
Proof.
  - intros E S T H. induction H using sub_mut_ind
      with (P := fun E S T w => forall (Z : atom) (R0 R : qua) E1 E2,
        wf_env E -> E = E1 ++ Z ~ bind_qua R0 ++ E2 ->
        wf_env E2 -> wf_qua E2 R -> subqual E2 R R0 ->
        sub (subst_env_qe Z R (E1 ++ E2)) (subst_qt Z R S) (subst_qt Z R T))
           (P0 := fun E S T w => forall (Z : atom) (R0 R : qua) E1 E2,
        wf_env E -> E = E1 ++ Z ~ bind_qua R0 ++ E2 ->
        wf_env E2 -> wf_qua E2 R -> subqual E2 R R0 ->
        subqtype (subst_env_qe Z R (E1 ++ E2)) (subst_qqt Z R S) (subst_qqt Z R T)).
    + (* sub_top *)
      intros Z R0 R E1 E2 HwfE HE HE2 HR HSR0. subst E.
      apply sub_top.
      * exact (wf_env_subst_qe_gen (E1 ++ Z ~ bind_qua R0 ++ E2)
                 Z R0 R E1 E2 HwfE eq_refl HE2 HR).
      * exact (wf_typ_subst_drop_qe (E1 ++ Z ~ bind_qua R0 ++ E2) S w0
                 E1 E2 Z R0 R eq_refl HwfE
                 (wf_env_subst_qe_gen (E1 ++ Z ~ bind_qua R0 ++ E2)
                    Z R0 R E1 E2 HwfE eq_refl HE2 HR)
                 (subst_qe_target_R_wf (E1 ++ Z ~ bind_qua R0 ++ E2)
                    Z R0 R E1 E2 HwfE eq_refl HE2 HR)).
    + (* sub_refl_tvar *)
      intros Z R0 R E1 E2 HwfE HE HE2 HR HSR0. subst E.
      simpl.
      assert (HXZ : X <> Z).
      { intro Hc. subst X.
        destruct (wf_typ_fvar_inv (E1 ++ Z ~ bind_qua R0 ++ E2) Z w0) as [U0 Hb].
        pose proof (binds_X_mid_qua E1 E2 Z R0) as HbZ.
        pose proof (binds_unique binding Z (bind_sub U0) (bind_qua R0)
                      (E1 ++ Z ~ bind_qua R0 ++ E2) Hb HbZ
                      (wf_env_uniq _ HwfE)) as Heqb.
        discriminate Heqb. }
      apply sub_refl_tvar.
      * exact (wf_env_subst_qe_gen (E1 ++ Z ~ bind_qua R0 ++ E2)
                 Z R0 R E1 E2 HwfE eq_refl HE2 HR).
      * destruct (wf_typ_fvar_inv (E1 ++ Z ~ bind_qua R0 ++ E2) X w0)
          as [U0 Hb].
        eapply wf_typ_var with (U := subst_qt Z R U0).
        exact (binds_subst_env_qe_drop E1 E2 Z R0 R X (bind_sub U0) HXZ Hb).
    + (* sub_trans_tvar *)
      intros Z R0 R E1 E2 HwfE HE HE2 HR HSR0. subst E.
      simpl.
      assert (HXZ : X <> Z).
      { intro Hc. subst X.
        pose proof (binds_X_mid_qua E1 E2 Z R0) as HbZ.
        pose proof (binds_unique binding Z (bind_sub U) (bind_qua R0)
                      (E1 ++ Z ~ bind_qua R0 ++ E2) b HbZ
                      (wf_env_uniq _ HwfE)) as Heqb.
        discriminate Heqb. }
      eapply sub_trans_tvar with (U := subst_qt Z R U).
      * exact (binds_subst_env_qe_drop E1 E2 Z R0 R X (bind_sub U) HXZ b).
      * exact (IHsub Z R0 R E1 E2 HwfE eq_refl HE2 HR HSR0).
    + (* sub_arrow *)
      intros Z R0 R E1 E2 HwfE HE HE2 HR HSR0. subst E.
      simpl. apply sub_arrow.
      * exact (IHsub Z R0 R E1 E2 HwfE eq_refl HE2 HR HSR0).
      * exact (IHsub0 Z R0 R E1 E2 HwfE eq_refl HE2 HR HSR0).
    + (* sub_all *)
      intros Z R0 R E1 E2 HwfE HE HE2 HR HSR0. subst E.
      simpl.
      apply sub_all with (L := union L (union (singleton Z)
        (union (dom (E1 ++ Z ~ bind_qua R0 ++ E2))
               (union (dom (subst_env_qe Z R (E1 ++ E2))) (fv_tqt T2))))).
      * exact (IHsub Z R0 R E1 E2 HwfE eq_refl HE2 HR HSR0).
      * intros Y HY.
        assert (HYL : Y `notin` L) by fsetdec.
        assert (HYZ : Y <> Z) by fsetdec.
        assert (HYdom : Y `notin` dom (E1 ++ Z ~ bind_qua R0 ++ E2)) by fsetdec.
        assert (Hwt1 : wf_typ (E1 ++ Z ~ bind_qua R0 ++ E2) T1).
        { exact (proj1 (sub_wf (E1 ++ Z ~ bind_qua R0 ++ E2) T1 S1 HwfE H)). }
        assert (Hwfext : wf_env ((Y ~ bind_sub T1 ++ E1) ++ Z ~ bind_qua R0 ++ E2)).
        { apply wf_env_sub; [exact HwfE|exact Hwt1|exact HYdom]. }
        assert (HEbody : Y ~ bind_sub T1 ++ (E1 ++ Z ~ bind_qua R0 ++ E2) =
                         (Y ~ bind_sub T1 ++ E1) ++ Z ~ bind_qua R0 ++ E2).
        { rewrite app_assoc. reflexivity. }
        pose proof (H0 Y HYL Z R0 R (Y ~ bind_sub T1 ++ E1) E2
                      Hwfext HEbody HE2 HR HSR0) as Hbody.
        rewrite subst_env_qe_cons_app in Hbody.
        change (subqtype
          (Y ~ bind_sub (subst_qt Z R T1) ++ subst_env_qe Z R (E1 ++ E2))
          (subst_qqt Z R (open_tqt_rec 0 (typ_fvar Y) S2))
          (subst_qqt Z R (open_tqt_rec 0 (typ_fvar Y) T2))) in Hbody.
        rewrite (subst_qqt_open_tqt Z R S2 0 Y) in Hbody.
        rewrite (subst_qqt_open_tqt Z R T2 0 Y) in Hbody.
        change (subqtype
          (Y ~ bind_sub (subst_qt Z R T1) ++ subst_env_qe Z R (E1 ++ E2))
          (open_tqt_rec 0 (typ_fvar Y) (subst_qqt Z R S2))
          (open_tqt_rec 0 (typ_fvar Y) (subst_qqt Z R T2))) in Hbody.
        exact Hbody.
    + (* sub_qall *)
      intros Z R0 R E1 E2 HwfE HE HE2 HR HSR0. subst E.
      simpl.
      assert (HRtgt : wf_qua (subst_env_qe Z R (E1 ++ E2)) R).
      { exact (subst_qe_target_R_wf (E1 ++ Z ~ bind_qua R0 ++ E2)
                 Z R0 R E1 E2 HwfE eq_refl HE2 HR). }
      apply sub_qall with (L := union L (union (singleton Z)
        (union (dom (E1 ++ Z ~ bind_qua R0 ++ E2))
               (union (dom (subst_env_qe Z R (E1 ++ E2))) (fv_tqt T2))))).
      * exact (subqual_subst_qe_gen (E1 ++ Z ~ bind_qua R0 ++ E2) T1 S1 s
                 Z R0 R E1 E2 HwfE eq_refl HE2 HR HSR0).
      * intros Y HY.
        assert (HYL : Y `notin` L) by fsetdec.
        assert (HYZ : Y <> Z) by fsetdec.
        assert (HYdom : Y `notin` dom (E1 ++ Z ~ bind_qua R0 ++ E2)) by fsetdec.
        assert (Hwq1 : wf_qua (E1 ++ Z ~ bind_qua R0 ++ E2) T1).
        { exact (proj1 (subqual_wf (E1 ++ Z ~ bind_qua R0 ++ E2) T1 S1 HwfE s)). }
        assert (Hwfext : wf_env (Y ~ bind_qua T1 ++ (E1 ++ Z ~ bind_qua R0 ++ E2))).
        { apply wf_env_qua; [exact HwfE|exact Hwq1|exact HYdom]. }
        assert (HEbody : Y ~ bind_qua T1 ++ (E1 ++ Z ~ bind_qua R0 ++ E2) =
                         (Y ~ bind_qua T1 ++ E1) ++ Z ~ bind_qua R0 ++ E2).
        { rewrite app_assoc. reflexivity. }
        pose proof (H Y HYL Z R0 R (Y ~ bind_qua T1 ++ E1) E2
                      Hwfext HEbody HE2 HR HSR0) as Hbody.
        rewrite subst_env_qe_cons_app in Hbody.
        change (subqtype
          (Y ~ bind_qua (subst_qq Z R T1) ++ subst_env_qe Z R (E1 ++ E2))
          (subst_qqt Z R (open_qqt_rec 0 (qua_fvar Y) S2))
          (subst_qqt Z R (open_qqt_rec 0 (qua_fvar Y) T2))) in Hbody.
        rewrite (subst_qqt_open_qqt_wf (subst_env_qe Z R (E1 ++ E2))
                   Z R S2 0 Y HRtgt HYZ) in Hbody.
        rewrite (subst_qqt_open_qqt_wf (subst_env_qe Z R (E1 ++ E2))
                   Z R T2 0 Y HRtgt HYZ) in Hbody.
        change (subqtype
          (Y ~ bind_qua (subst_qq Z R T1) ++ subst_env_qe Z R (E1 ++ E2))
          (open_qqt_rec 0 (qua_fvar Y) (subst_qqt Z R S2))
          (open_qqt_rec 0 (qua_fvar Y) (subst_qqt Z R T2))) in Hbody.
        exact Hbody.
    + (* sub_sum *)
      intros Z R0 R E1 E2 HwfE HE HE2 HR HSR0. subst E.
      simpl. apply sub_sum.
      * exact (IHsub Z R0 R E1 E2 HwfE eq_refl HE2 HR HSR0).
      * exact (IHsub0 Z R0 R E1 E2 HwfE eq_refl HE2 HR HSR0).
    + (* sub_pair *)
      intros Z R0 R E1 E2 HwfE HE HE2 HR HSR0. subst E.
      simpl. apply sub_pair.
      * exact (IHsub Z R0 R E1 E2 HwfE eq_refl HE2 HR HSR0).
      * exact (IHsub0 Z R0 R E1 E2 HwfE eq_refl HE2 HR HSR0).
    + (* sub_qtyp_qtyp *)
      intros Z R0 R E1 E2 HwfE HE HE2 HR HSR0. subst E.
      simpl. apply sub_qtyp_qtyp.
      * exact (subqual_subst_qe_gen (E1 ++ Z ~ bind_qua R0 ++ E2) Q1 Q2 s
                 Z R0 R E1 E2 HwfE eq_refl HE2 HR HSR0).
      * exact (IHsub Z R0 R E1 E2 HwfE eq_refl HE2 HR HSR0).
  - intros E S T H. destruct S as [Q1 T1]. destruct T as [Q2 T2].
    inversion H; subst.
    intros Z R0 R E1 E2 HwfE HE HE2 HR HSR0. subst E.
    simpl. apply sub_qtyp_qtyp.
    + exact (subqual_subst_qe_gen (E1 ++ Z ~ bind_qua R0 ++ E2) Q1 Q2 H4
                Z R0 R E1 E2 HwfE eq_refl HE2 HR HSR0).
    + exact (sub_subst_qe_gen (E1 ++ Z ~ bind_qua R0 ++ E2) T1 T2 H6
                Z R0 R E1 E2 HwfE eq_refl HE2 HR HSR0).
Qed.


(* ===== inlined from /tmp/finish/QeCompat.v ===== *)

Lemma wf_qua_subst_env_qe_mid : forall E1 E2 (X : atom) (R0 R : qua) Q,
  wf_env (E1 ++ X ~ bind_qua R0 ++ E2) ->
  wf_qua (E1 ++ X ~ bind_qua R0 ++ E2) Q ->
  wf_qua (subst_env_qe X R (E1 ++ E2)) R ->
  wf_qua (subst_env_qe X R (E1 ++ E2)) (subst_qq X R Q).
Proof. intros. eapply wf_qua_mid_remove_qe; eassumption. Qed.


(* ===== inlined from /tmp/w6/SubstComm.v ===== *)

(* (a) *)
Lemma subst_te_open_ee_rec : forall Z W e k x,
  subst_te Z W (open_ee_rec k (exp_fvar x) e) =
  open_ee_rec k (exp_fvar x) (subst_te Z W e).
Proof.
  intros Z W e. induction e; intros k x; simpl;
    (try destruct (k == n); try reflexivity; try (f_equal; auto)).
Qed.

(* (d) *)
Lemma subst_qe_open_ee_rec : forall Z R e k x,
  subst_qe Z R (open_ee_rec k (exp_fvar x) e) =
  open_ee_rec k (exp_fvar x) (subst_qe Z R e).
Proof.
  intros Z R e. induction e; intros k x; simpl;
    (try destruct (k == n); try reflexivity; try (f_equal; auto)).
Qed.

(* (b) *)
Lemma subst_te_open_te_rec : forall Z W e k X,
  (forall (j : nat) (Y : atom), open_tt_rec j (typ_fvar Y) W = W) ->
  X <> Z ->
  subst_te Z W (open_te_rec k (typ_fvar X) e) =
  open_te_rec k (typ_fvar X) (subst_te Z W e).
Proof.
  intros Z W e. induction e; intros k X Hwt Hne; simpl;
    (try destruct (k == n);
     try (destruct (Z == X) as [Heq|_]; [exfalso; apply Hne; symmetry; exact Heq|]);
     try reflexivity;
     try (f_equal; auto using subst_tqt_open_tqt, subst_tt_open_tt)).
Qed.

(* (c) *)
Lemma subst_te_open_qe_rec : forall Z W e k Y,
  (forall (j : nat) (X : atom), open_qt_rec j (qua_fvar X) W = W) ->
  Y <> Z ->
  subst_te Z W (open_qe_rec k (qua_fvar Y) e) =
  open_qe_rec k (qua_fvar Y) (subst_te Z W e).
Proof.
  intros Z W e. induction e; intros k Y Hwt Hne; simpl;
    (try reflexivity;
     try (f_equal; auto using subst_tqt_open_qqt, subst_tt_open_qt)).
Qed.

Lemma subst_qq_open_qqt_fresh : forall E Z R Q j Y,
  wf_qua E R -> Y <> Z ->
  subst_qq Z R (open_qq_rec j (qua_fvar Y) Q) =
  open_qq_rec j (qua_fvar Y) (subst_qq Z R Q).
Proof.
  intros E Z R Q j Y HR Hne.
  pose proof (subst_qq_open_qqt Z R
                (fun k S => wf_qua_open_qq E R HR k S) Q j (qua_fvar Y)) as Hq.
  assert (Hnf : Z `notin` fv_qq (qua_fvar Y)) by (simpl; fsetdec).
  rewrite (subst_qq_nofv Z R (qua_fvar Y) Hnf) in Hq.
  exact Hq.
Qed.

Lemma subst_qt_open_qt_fresh : forall E Z R T j Y,
  wf_qua E R -> Y <> Z ->
  subst_qt Z R (open_qt_rec j (qua_fvar Y) T) =
  open_qt_rec j (qua_fvar Y) (subst_qt Z R T).
Proof.
  intros E Z R T j Y HR Hne.
  pose proof (subst_qt_open_qt Z R
                (fun k S => wf_qua_open_qq E R HR k S) T j (qua_fvar Y)) as Hq.
  assert (Hnf : Z `notin` fv_qq (qua_fvar Y)) by (simpl; fsetdec).
  rewrite (subst_qq_nofv Z R (qua_fvar Y) Hnf) in Hq.
  exact Hq.
Qed.

(* (e) *)
Lemma subst_qe_open_te_rec : forall Z R e k X,
  subst_qe Z R (open_te_rec k (typ_fvar X) e) =
  open_te_rec k (typ_fvar X) (subst_qe Z R e).
Proof.
  intros Z R e. induction e; intros k X; simpl;
    (try destruct (k == n); try reflexivity;
     try (f_equal; auto using subst_qqt_open_tqt, subst_qt_open_tt)).
Qed.

(* (f) *)
Lemma subst_qe_open_qe_rec : forall E Z R e k Y,
  wf_qua E R -> Y <> Z ->
  subst_qe Z R (open_qe_rec k (qua_fvar Y) e) =
  open_qe_rec k (qua_fvar Y) (subst_qe Z R e).
Proof.
  intros E Z R e. induction e; intros k Y HR Hne; simpl; try reflexivity.
  all: try f_equal.
  all: try (apply (subst_qqt_open_qqt_wf E Z R _ _ Y HR Hne)).
  all: try (apply (subst_qt_open_qt_fresh E Z R _ _ Y HR Hne)).
  all: try (apply (subst_qq_open_qqt_fresh E Z R _ _ Y HR Hne)).
  all: try (first [eapply IHe; eassumption | eapply IHe1; eassumption |
              eapply IHe2; eassumption | eapply IHe3; eassumption]).
Qed.

(* Generic type-level commutations (for tapp) *)

Section TeTypeGen.
Context (X : atom) (V : typ).
Context (V_open_tt : forall (k : nat) (U : typ), open_tt_rec k U V = V).
Context (V_open_qt : forall (k : nat) (R : qua), open_qt_rec k R V = V).

Fixpoint subst_tt_open_tt_gen (T : typ) {struct T} :
  forall (k : nat) (U : typ),
    subst_tt X V (open_tt_rec k U T) =
    open_tt_rec k (subst_tt X V U) (subst_tt X V T)
with subst_tqt_open_tqt_gen (T : qtyp) {struct T} :
  forall (k : nat) (U : typ),
    subst_tqt X V (open_tqt_rec k U T) =
    open_tqt_rec k (subst_tt X V U) (subst_tqt X V T).
Proof.
  - destruct T; intros k0 U0; simpl.
    + reflexivity.
    + destruct (k0 == n); reflexivity.
    + destruct (X == a) as [Heq|Hne].
      * subst a. simpl. rewrite V_open_tt. reflexivity.
      * reflexivity.
    + f_equal; [apply subst_tqt_open_tqt_gen|apply subst_tqt_open_tqt_gen].
    + f_equal; [apply subst_tt_open_tt_gen|apply subst_tqt_open_tqt_gen].
    + f_equal; apply subst_tqt_open_tqt_gen.
    + f_equal; [apply subst_tqt_open_tqt_gen|apply subst_tqt_open_tqt_gen].
    + f_equal; [apply subst_tqt_open_tqt_gen|apply subst_tqt_open_tqt_gen].
    + f_equal; apply subst_tqt_open_tqt_gen.
  - destruct T as [Q T0]; intros k0 U0; simpl.
    f_equal. apply subst_tt_open_tt_gen.
Qed.

Fixpoint subst_tt_open_qt_gen (T : typ) {struct T} :
  forall (k : nat) (R : qua),
    subst_tt X V (open_qt_rec k R T) =
    open_qt_rec k R (subst_tt X V T)
with subst_tqt_open_qqt_gen (T : qtyp) {struct T} :
  forall (k : nat) (R : qua),
    subst_tqt X V (open_qqt_rec k R T) =
    open_qqt_rec k R (subst_tqt X V T).
Proof.
  - destruct T; intros k0 R0; simpl.
    + reflexivity.
    + reflexivity.
    + destruct (X == a) as [Heq|Hne].
      * subst a. simpl. rewrite V_open_qt. reflexivity.
      * reflexivity.
    + f_equal; [apply subst_tqt_open_qqt_gen|apply subst_tqt_open_qqt_gen].
    + f_equal; [apply subst_tt_open_qt_gen|apply subst_tqt_open_qqt_gen].
    + f_equal; apply subst_tqt_open_qqt_gen.
    + f_equal; [apply subst_tqt_open_qqt_gen|apply subst_tqt_open_qqt_gen].
    + f_equal; [apply subst_tqt_open_qqt_gen|apply subst_tqt_open_qqt_gen].
    + f_equal; apply subst_tqt_open_qqt_gen.
  - destruct T as [Q T0]; intros k0 R0; simpl.
    f_equal. apply subst_tt_open_qt_gen.
Qed.

End TeTypeGen.

Lemma subst_tqt_open_tqt_gen_wf : forall E X V T k U,
  wf_typ E V ->
  subst_tqt X V (open_tqt_rec k U T) =
  open_tqt_rec k (subst_tt X V U) (subst_tqt X V T).
Proof.
  intros E X V T k U HV.
  exact (subst_tqt_open_tqt_gen X V
           (fun j U0 => wf_typ_open_tt_any E V HV j U0)
           T k U).
Qed.


Lemma subst_tqt_open_qqt_gen_wf : forall E X V T k R,
  wf_typ E V ->
  subst_tqt X V (open_qqt_rec k R T) =
  open_qqt_rec k R (subst_tqt X V T).
Proof.
  intros E X V T k R HV.
  exact (subst_tqt_open_qqt_gen X V
           (fun j R0 => wf_typ_open_qt_any E V HV j R0)
           T k R).
Qed.

Section QeTypeGen.
Context (X : atom) (R : qua).

Fixpoint subst_qt_open_tt_gen (T : typ) {struct T} :
  forall (k : nat) (U : typ),
    subst_qt X R (open_tt_rec k U T) =
    open_tt_rec k (subst_qt X R U) (subst_qt X R T)
with subst_qqt_open_tqt_gen (T : qtyp) {struct T} :
  forall (k : nat) (U : typ),
    subst_qqt X R (open_tqt_rec k U T) =
    open_tqt_rec k (subst_qt X R U) (subst_qqt X R T).
Proof.
  - destruct T; intros k0 U0; simpl.
    + reflexivity.
    + destruct (k0 == n); reflexivity.
    + reflexivity.
    + f_equal; [apply subst_qqt_open_tqt_gen|apply subst_qqt_open_tqt_gen].
    + f_equal; [apply subst_qt_open_tt_gen|apply subst_qqt_open_tqt_gen].
    + f_equal; apply subst_qqt_open_tqt_gen.
    + f_equal; [apply subst_qqt_open_tqt_gen|apply subst_qqt_open_tqt_gen].
    + f_equal; [apply subst_qqt_open_tqt_gen|apply subst_qqt_open_tqt_gen].
    + f_equal; apply subst_qqt_open_tqt_gen.
  - destruct T as [Q T0]; intros k0 U0; simpl.
    f_equal. apply subst_qt_open_tt_gen.
Qed.

End QeTypeGen.


(* ===== inlined from /tmp/w6/Wf.v ===== *)

Lemma wf_qtyp_qtyp_inv0 : forall E Q T,
  wf_qtyp E (qtyp_qtyp Q T) -> wf_qua E Q /\ wf_typ E T.
Proof. intros E Q T H. inversion H; subst. auto. Qed.

Lemma wf_typ_all_inv0 : forall E T1 T2,
  wf_typ E (typ_all T1 T2) ->
  wf_typ E T1 /\ exists L, forall X, X `notin` L ->
    wf_qtyp (X ~ bind_sub T1 ++ E) (open_tqt T2 X).
Proof. intros E T1 T2 H. inversion H; subst. split; [assumption|].
  exists L. assumption. Qed.

Lemma wf_typ_qall_inv0 : forall E Q T,
  wf_typ E (typ_qall Q T) ->
  wf_qua E Q /\ exists L, forall X, X `notin` L ->
    wf_qtyp (X ~ bind_qua Q ++ E) (open_qqt T X).
Proof. intros E Q T H. inversion H; subst. split; [assumption|].
  exists L. assumption. Qed.

Lemma wf_typ_pair_inv0 : forall E T1 T2,
  wf_typ E (typ_pair T1 T2) -> wf_qtyp E T1 /\ wf_qtyp E T2.
Proof. intros E T1 T2 H. inversion H; subst. auto. Qed.

Lemma wf_typ_arrow_inv0 : forall E T1 T2,
  wf_typ E (typ_arrow T1 T2) -> wf_qtyp E T1 /\ wf_qtyp E T2.
Proof. intros E T1 T2 H. inversion H; subst. auto. Qed.

Lemma wf_typ_sum_inv0 : forall E T1 T2,
  wf_typ E (typ_sum T1 T2) -> wf_qtyp E T1 /\ wf_qtyp E T2.
Proof. intros E T1 T2 H. inversion H; subst. auto. Qed.

Lemma env_subqua_drop_typ_mid : forall E1 E2 x (V : qtyp),
  wf_env (E1 ++ x ~ bind_typ V ++ E2) ->
  env_subqua_extends (E1 ++ x ~ bind_typ V ++ E2) (E1 ++ E2).
Proof. intros. eapply env_subqua_extends_mid; eassumption. Qed.

Lemma typing_wf_qtyp : forall E Q e T,
  typing E Q e T -> wf_env E -> wf_qtyp E T.
Proof.
  intros E Q e T Ht. induction Ht; intros Hwf.
  - (* var *) simpl. apply (wf_env_binds_wf E Hwf x (bind_typ T) H0).
  - (* abs *) pick fresh x.
    assert (Hx : x `notin` L) by fsetdec.
    pose proof (typing_wf_env _ _ _ _ (H x Hx)) as Hwfext.
    destruct (wf_env_cons_inv x (bind_typ V) E Hwfext) as [HE [Hdom HV]].
    pose proof (env_subqua_extends_mid nil E x V Hwfext) as Hext.
    simpl in Hext.
    pose proof (H0 x Hx Hwfext) as HwT1ext.
    pose proof (typing_wf_qua _ _ _ _ Hwfext (H x Hx)) as HPext.
    assert (HPE : wf_qua E P) by (eapply wf_qua_subqua; eassumption).
    assert (HwT1E : wf_qtyp E T1) by (eapply wf_qtyp_subqua; eassumption).
    apply wf_qtyp_qtyp.
    + exact HPE.
    + apply wf_typ_arrow; assumption.
  - (* app *) pose proof (IHHt1 Hwf) as HIH. inversion HIH as [E0 Q0 T0 Hq Ha]; subst.
    inversion Ha; subst. assumption.
  - (* tabs *) pick fresh x.
    assert (Hx : x `notin` L) by fsetdec.
    pose proof (typing_wf_env _ _ _ _ (H x Hx)) as Hwfext.
    destruct (wf_env_cons_inv x (bind_sub V) E Hwfext) as [HE [Hdom HV]].
    pose proof (typing_wf_qua _ _ _ _ Hwfext (H x Hx)) as HPext.
    assert (HPE : wf_qua E P) by (eapply (wf_qua_mid_remove_sub nil E x V P); [exact Hwfext|simpl; exact HPext]).
    apply wf_qtyp_qtyp.
    + exact HPE.
    + apply wf_typ_all with (L := L).
      * exact HV.
      * intros X HX. apply (H0 X HX). eapply typing_wf_env. apply H. exact HX.
  - (* tapp *) pose proof (IHHt Hwf) as HIH. inversion HIH as [E0 Q0 T0 Hq Hall]; subst.
    destruct (wf_typ_all_inv0 E T1 T2 Hall) as [HwT1 [L0 Hbody]].
    destruct (sub_wf E T T1 Hwf H) as [HwT _].
    pick fresh X for (L0 \u dom E \u fv_tqt T2).
    assert (HXL : X `notin` L0) by fsetdec.
    assert (HXd : X `notin` dom E) by fsetdec.
    assert (HXf : X `notin` fv_tqt T2) by fsetdec.
    exact (wf_qtyp_open_te_fresh E X T1 T T2 Hwf HXd HXf HwT1 HwT (Hbody X HXL)).
  - (* qabs *) pick fresh x.
    assert (Hx : x `notin` L) by fsetdec.
    pose proof (typing_wf_env _ _ _ _ (H0 x Hx)) as Hwfext.
    destruct (wf_env_cons_inv x (bind_qua Q) E Hwfext) as [HE [Hdom HQ]].
    apply wf_qtyp_qtyp.
    + exact H.
    + apply wf_typ_qall with (L := L).
      * exact HQ.
      * intros X HX. apply (H1 X HX). eapply typing_wf_env. apply H0. exact HX.
  - (* qapp *) pose proof (IHHt Hwf) as HIH. inversion HIH as [E0 Q0 T0 Hq Hall]; subst.
    destruct (wf_typ_qall_inv0 E Q1 T Hall) as [HQ1 [L0 Hbody]].
    destruct (subqual_wf E Q Q1 Hwf H) as [HwQ _].
    pick fresh X for (L0 \u dom E \u fv_tqt T).
    assert (HXL : X `notin` L0) by fsetdec.
    assert (HXd : X `notin` dom E) by fsetdec.
    assert (HXf : X `notin` fv_tqt T) by fsetdec.
    assert (Hwfext : wf_env (X ~ bind_qua Q1 ++ E)) by (apply wf_env_qua; assumption).
    exact (wf_qtyp_open_qe_fresh E X Q1 Q T Hwf HXd HXf HQ1 HwQ (Hbody X HXL)).
  - (* sub *) eapply subqtype_wf; eassumption.
  - (* subqual *) exact (IHHt Hwf).
  - (* let *) pick fresh x.
    assert (Hx : x `notin` L) by fsetdec.
    pose proof (typing_wf_env _ _ _ _ (H x Hx)) as Hwfext.
    destruct (wf_env_cons_inv x (bind_typ T1) E Hwfext) as [HE [Hdom HT1]].
    pose proof (env_subqua_extends_mid nil E x T1 Hwfext) as Hext.
    simpl in Hext.
    pose proof (H0 x Hx Hwfext) as HT2ext.
    exact (wf_qtyp_subqua (x ~ bind_typ T1 ++ E) T2 HT2ext E HE Hext).
  - (* inl *) apply wf_qtyp_qtyp; [exact H|apply wf_typ_sum; [exact (IHHt Hwf)|exact H0]].
  - (* inr *) apply wf_qtyp_qtyp; [exact H|apply wf_typ_sum; [exact H0|exact (IHHt Hwf)]].
  - (* case *) pick fresh x.
    assert (Hx : x `notin` L) by fsetdec.
    pose proof (typing_wf_env _ _ _ _ (H x Hx)) as Hwfext.
    destruct (wf_env_cons_inv x (bind_typ T1) E Hwfext) as [HE [Hdom HT1]].
    pose proof (env_subqua_extends_mid nil E x T1 Hwfext) as Hext.
    simpl in Hext.
    pose proof (H0 x Hx Hwfext) as HTtext.
    exact (wf_qtyp_subqua (x ~ bind_typ T1 ++ E) T HTtext E HE Hext).
  - (* pair *) apply wf_qtyp_qtyp; [exact H|apply wf_typ_pair; [exact (IHHt1 Hwf)|exact (IHHt2 Hwf)]].
  - (* first *) pose proof (IHHt Hwf) as HIH. inversion HIH as [E0 Q0 T0 Hq Hpair]; subst.
    destruct (wf_typ_pair_inv0 E T1 T2 Hpair) as [HT1 _]. exact HT1.
  - (* second *) pose proof (IHHt Hwf) as HIH. inversion HIH as [E0 Q0 T0 Hq Hpair]; subst.
    destruct (wf_typ_pair_inv0 E T1 T2 Hpair) as [_ HT2]. exact HT2.
  - (* upqual *) pose proof (IHHt Hwf) as HIH. inversion HIH as [E0 Q0 T0 Hq HT]; subst.
    apply wf_qtyp_qtyp.
    + apply (proj2 (subqual_wf E Q P Hwf H)).
    + exact HT.
  - (* check *) exact (IHHt Hwf).
Qed.



(* ===== inlined from /tmp/w6/CtxWf2.v ===== *)

Lemma wf_typ_all_inv1 : forall E T1 T2,
  wf_typ E (typ_all T1 T2) -> wf_typ E T1.
Proof. intros E T1 T2 H. inversion H; subst. assumption. Qed.

Lemma wf_qtyp_qtyp_inv1 : forall E Q T,
  wf_qtyp E (qtyp_qtyp Q T) -> wf_qua E Q /\ wf_typ E T.
Proof. intros E Q T H. inversion H; subst. auto. Qed.

Lemma wf_typ_sum_inv1 : forall E T1 T2,
  wf_typ E (typ_sum T1 T2) -> wf_qtyp E T1 /\ wf_qtyp E T2.
Proof. intros E T1 T2 H. inversion H; subst. auto. Qed.

Lemma wf_typ_pair_inv1 : forall E T1 T2,
  wf_typ E (typ_pair T1 T2) -> wf_qtyp E T1 /\ wf_qtyp E T2.
Proof. intros E T1 T2 H. inversion H; subst. auto. Qed.

Lemma wf_typ_arrow_inv1 : forall E T1 T2,
  wf_typ E (typ_arrow T1 T2) -> wf_qtyp E T1 /\ wf_qtyp E T2.
Proof. intros E T1 T2 H. inversion H; subst. auto. Qed.

Lemma typing_ctx_wf_qtyp : forall E Q c T,
  typing_ctx E Q c T -> wf_env E -> wf_qtyp E T.
Proof.
  intros E Q c T Hc. induction Hc; intros Hwf.
  - (* done *) assumption.
  - (* abs *) apply wf_qtyp_qtyp.
    + eapply typing_ctx_wf_qua; eassumption.
    + apply wf_typ_arrow.
      * eapply typing_wf_qtyp; eassumption.
      * apply IHHc; exact Hwf.
  - (* app *) pose proof (typing_wf_qtyp E Q e1 (qtyp_qtyp Q (typ_arrow T1 T2)) H0 Hwf) as Harr.
    destruct (wf_qtyp_qtyp_inv1 E Q (typ_arrow T1 T2) Harr) as [_ Ha].
    destruct (wf_typ_arrow_inv1 E T1 T2 Ha) as [HT1 _]. exact HT1.
  - (* tabs *) apply wf_qtyp_qtyp.
    + eapply typing_ctx_wf_qua; eassumption.
    + apply wf_typ_all with (L := L).
      * eapply sub_wf; eassumption.
      * exact H0.
  - (* qabs *) apply wf_qtyp_qtyp.
    + eapply typing_ctx_wf_qua; eassumption.
    + apply wf_typ_qall with (L := L).
      * apply (proj2 (subqual_wf E R' R Hwf H)).
      * exact H0.
  - (* let *) pick fresh x.
    assert (Hx : x `notin` L) by fsetdec.
    pose proof (typing_wf_env _ _ _ _ (H x Hx)) as Hwfext.
    destruct (wf_env_cons_inv x (bind_typ T1) E Hwfext) as [_ [_ HT1]].
    exact HT1.
  - (* inl *) pose proof (IHHc Hwf) as Hsrc.
    destruct (wf_qtyp_qtyp_inv1 E P (typ_sum T1 T2) Hsrc) as [_ Hsum].
    exact (proj1 (wf_typ_sum_inv1 E T1 T2 Hsum)).
  - (* inr *) pose proof (IHHc Hwf) as Hsrc.
    destruct (wf_qtyp_qtyp_inv1 E P (typ_sum T1 T2) Hsrc) as [_ Hsum].
    exact (proj2 (wf_typ_sum_inv1 E T1 T2 Hsum)).
  - (* case *) apply wf_qtyp_qtyp.
    + exact H.
    + pick fresh x.
      assert (Hx : x `notin` L) by fsetdec.
      pose proof (typing_wf_env _ _ _ _ (H0 x Hx)) as Hwfext1.
      destruct (wf_env_cons_inv x (bind_typ T1) E Hwfext1) as [_ [_ HT1]].
      pose proof (typing_wf_env _ _ _ _ (H1 x Hx)) as Hwfext2.
      destruct (wf_env_cons_inv x (bind_typ T2) E Hwfext2) as [_ [_ HT2]].
      apply wf_typ_sum; assumption.
  - (* pair_1 *) pose proof (IHHc Hwf) as Hsrc.
    destruct (wf_qtyp_qtyp_inv1 E P (typ_pair T1 T2) Hsrc) as [_ Hpair].
    exact (proj1 (wf_typ_pair_inv1 E T1 T2 Hpair)).
  - (* pair_2 *) pose proof (IHHc Hwf) as Hsrc.
    destruct (wf_qtyp_qtyp_inv1 E P (typ_pair T1 T2) Hsrc) as [_ Hpair].
    exact (proj2 (wf_typ_pair_inv1 E T1 T2 Hpair)).
  - (* first *) apply wf_qtyp_qtyp; [exact H|apply wf_typ_pair; [exact (IHHc Hwf)|exact H0]].
  - (* second *) apply wf_qtyp_qtyp; [exact H|apply wf_typ_pair; [exact H0|exact (IHHc Hwf)]].
  - (* barrier *) apply IHHc; exact Hwf.
  - (* upqual *) pose proof (IHHc Hwf) as Hsrc.
    destruct (wf_qtyp_qtyp_inv1 E P T Hsrc) as [HP HT].
    apply wf_qtyp_qtyp; assumption.
  - (* check *) pose proof (IHHc Hwf) as Hsrc.
    destruct (wf_qtyp_qtyp_inv1 E P T Hsrc) as [HP HT].
    apply wf_qtyp_qtyp.
    + apply wf_qua_meet; assumption.
    + exact HT.
  - (* sub *) exact (proj1 (subqtype_wf E S T Hwf H)).
  - (* subqual *) apply IHHc; exact Hwf.
Qed.


(* ===== inlined from /tmp/w6/TypTe.v ===== *)

Lemma wf_typ_subst_target_te : forall E T X V0 V E1 E2,
  wf_env E -> E = E1 ++ X ~ bind_sub V0 ++ E2 ->
  wf_env E2 -> wf_typ E2 V -> wf_typ E T ->
  wf_typ (subst_env_te X V (E1 ++ E2)) (subst_tt X V T).
Proof.
  intros E T X V0 V E1 E2 Hwf HE HE2 HV HT.
  assert (Hwtgt : wf_env (subst_env_te X V (E1 ++ E2)))
    by (exact (wf_env_subst_te_gen E X V0 V E1 E2 Hwf HE HE2 HV)).
  assert (HVtgt : wf_typ (subst_env_te X V (E1 ++ E2)) V)
    by (exact (subst_te_target_V_wf E X V0 V E1 E2 Hwf HE HE2 HV)).
  exact (wf_typ_subst_drop E T HT E1 E2 X V0 V HE Hwf Hwtgt HVtgt).
Qed.

Lemma wf_qtyp_subst_target_te : forall E T X V0 V E1 E2,
  wf_env E -> E = E1 ++ X ~ bind_sub V0 ++ E2 ->
  wf_env E2 -> wf_typ E2 V -> wf_qtyp E T ->
  wf_qtyp (subst_env_te X V (E1 ++ E2)) (subst_tqt X V T).
Proof.
  intros E T X V0 V E1 E2 Hwf HE HE2 HV HT.
  assert (Hwtgt : wf_env (subst_env_te X V (E1 ++ E2)))
    by (exact (wf_env_subst_te_gen E X V0 V E1 E2 Hwf HE HE2 HV)).
  assert (HVtgt : wf_typ (subst_env_te X V (E1 ++ E2)) V)
    by (exact (subst_te_target_V_wf E X V0 V E1 E2 Hwf HE HE2 HV)).
  exact (wf_qtyp_subst_drop E T HT E1 E2 X V0 V HE Hwf Hwtgt HVtgt).
Qed.

Definition te_motive (E : env) (Q : qua) (e : exp) (T : qtyp) : Prop :=
  forall X V0 V E1 E2,
    wf_env E -> E = E1 ++ X ~ bind_sub V0 ++ E2 ->
    wf_env E2 -> wf_typ E2 V -> sub E2 V V0 ->
    typing (subst_env_te X V (E1 ++ E2)) Q
      (subst_te X V e) (subst_tqt X V T).

Lemma typing_subst_te_gen : forall E Q e T,
  typing E Q e T -> te_motive E Q e T.
Proof.
  intros E Q e T Hty. change (te_motive E Q e T).
  apply typing_ind with (P := te_motive).
  - (* var *) intros E0 x T0 HwfE Hb. unfold te_motive.
    intros X V0 V E1 E2 Hwf HE HE2 HV HVV0. subst E0.
    simpl. eapply typing_var.
    + exact (wf_env_subst_te_gen (E1 ++ X ~ bind_sub V0 ++ E2) X V0 V E1 E2 Hwf eq_refl HE2 HV).
    + destruct (eq_dec x X) as [Heq|Hne].
      * subst x. exfalso.
        assert (HbX : binds X (bind_sub V0) (E1 ++ X ~ bind_sub V0 ++ E2)).
        { apply binds_app_r, binds_app_l, binds_cons_2; reflexivity. }
        pose proof (binds_unique binding X (bind_typ T0) (bind_sub V0)
                      (E1 ++ X ~ bind_sub V0 ++ E2) Hb HbX (wf_env_uniq _ Hwf)) as Hbad.
        discriminate Hbad.
      * exact (binds_subst_env_te_drop E1 E2 X V0 V x (bind_typ T0) Hne Hb).
  - (* abs *) intros L E0 P Vabs e1 T1 Hbody IHbody. unfold te_motive.
    intros X V0 V E1 E2 Hwf HE HE2 HV HVV0. subst E0.
    simpl. eapply typing_abs with (L := L).
    intros x HxL.
    assert (Htyb : typing (x ~ bind_typ Vabs ++ E1 ++ X ~ bind_sub V0 ++ E2) P
                     (open_ee e1 x) T1) by (apply Hbody; exact HxL).
    assert (Hwfb : wf_env (x ~ bind_typ Vabs ++ E1 ++ X ~ bind_sub V0 ++ E2))
      by (eapply typing_wf_env; eassumption).
    assert (HEb : x ~ bind_typ Vabs ++ E1 ++ X ~ bind_sub V0 ++ E2 =
                  (x ~ bind_typ Vabs ++ E1) ++ X ~ bind_sub V0 ++ E2)
      by (rewrite app_assoc; reflexivity).
    pose proof (IHbody x HxL X V0 V (x ~ bind_typ Vabs ++ E1) E2
                  Hwfb HEb HE2 HV HVV0) as Hres.
    rewrite subst_env_te_cons_app in Hres.
    unfold open_ee in Hres.
    rewrite (subst_te_open_ee_rec X V e1 0 x) in Hres.
    exact Hres.
  - (* app *) intros Q0 T1 E0 e1 e2 T2 H1 IH1 H2 IH2. unfold te_motive.
    intros X V0 V E1 E2 Hwf HE HE2 HV HVV0. subst E0.
    simpl. eapply typing_app.
    + exact (IH1 X V0 V E1 E2 Hwf eq_refl HE2 HV HVV0).
    + exact (IH2 X V0 V E1 E2 Hwf eq_refl HE2 HV HVV0).
  - (* tabs *) intros L E0 P Vabs e1 T1 Hbody IHbody. unfold te_motive.
    intros X V0 V E1 E2 Hwf HE HE2 HV HVV0. subst E0.
    simpl. eapply typing_tabs with (L := union L (singleton X)).
    intros Y HY.
    assert (HYL : Y `notin` L) by fsetdec.
    assert (HYX : Y <> X) by fsetdec.
    assert (Htyb : typing (Y ~ bind_sub Vabs ++ E1 ++ X ~ bind_sub V0 ++ E2) P
                     (open_te e1 Y) (open_tqt T1 Y)) by (apply Hbody; exact HYL).
    assert (Hwfb : wf_env (Y ~ bind_sub Vabs ++ E1 ++ X ~ bind_sub V0 ++ E2))
      by (eapply typing_wf_env; eassumption).
    assert (HEb : Y ~ bind_sub Vabs ++ E1 ++ X ~ bind_sub V0 ++ E2 =
                  (Y ~ bind_sub Vabs ++ E1) ++ X ~ bind_sub V0 ++ E2)
      by (rewrite app_assoc; reflexivity).
    pose proof (IHbody Y HYL X V0 V (Y ~ bind_sub Vabs ++ E1) E2
                  Hwfb HEb HE2 HV HVV0) as Hres.
    rewrite subst_env_te_cons_app in Hres.
    assert (Hwt : forall (j : nat) (Z : atom), open_tt_rec j (typ_fvar Z) V = V).
    { intros. apply (type_open_tt_fvar V (wf_typ_type E2 V HV) j Z). }
    unfold open_te in Hres.
    rewrite (subst_te_open_te_rec X V e1 0 Y Hwt HYX) in Hres.
    unfold open_tqt in Hres.
    rewrite (subst_tqt_open_tqt X V Hwt T1 0 Y HYX) in Hres.
    exact Hres.
  - (* tapp *) intros Q0 T1 E0 e1 Targ T2 H1 IH1 Hsub. unfold te_motive.
    intros X V0 V E1 E2 Hwf HE HE2 HV HVV0. subst E0.
    simpl. unfold open_tqt. rewrite (subst_tqt_open_tqt_gen_wf E2 X V T2 0 Targ HV).
    eapply typing_tapp.
    + exact (IH1 X V0 V E1 E2 Hwf eq_refl HE2 HV HVV0).
    + exact (sub_subst_te_gen (E1 ++ X ~ bind_sub V0 ++ E2) Targ T1 Hsub X V0 V E1 E2 Hwf eq_refl HE2 HV HVV0).
  - (* qabs *) intros L E0 P Q0 e1 T1 HwfP Hbody IHbody. unfold te_motive.
    intros X V0 V E1 E2 Hwf HE HE2 HV HVV0. subst E0.
    simpl. eapply typing_qabs with (L := union L (singleton X)).
    + exact (wf_qua_subst_env_te_mid E1 E2 X V0 V P Hwf HwfP).
    + intros Y HY.
      assert (HYL : Y `notin` L) by fsetdec.
      assert (HYX : Y <> X) by fsetdec.
      assert (Htyb : typing (Y ~ bind_qua Q0 ++ E1 ++ X ~ bind_sub V0 ++ E2) P
                       (open_qe e1 Y) (open_qqt T1 Y)) by (apply Hbody; exact HYL).
      assert (Hwfb : wf_env (Y ~ bind_qua Q0 ++ E1 ++ X ~ bind_sub V0 ++ E2))
        by (eapply typing_wf_env; eassumption).
      assert (HEb : Y ~ bind_qua Q0 ++ E1 ++ X ~ bind_sub V0 ++ E2 =
                    (Y ~ bind_qua Q0 ++ E1) ++ X ~ bind_sub V0 ++ E2)
        by (rewrite app_assoc; reflexivity).
      pose proof (IHbody Y HYL X V0 V (Y ~ bind_qua Q0 ++ E1) E2
                    Hwfb HEb HE2 HV HVV0) as Hres.
      rewrite subst_env_te_cons_app in Hres.
      assert (Hwt : forall (j : nat) (Z : atom), open_qt_rec j (qua_fvar Z) V = V).
      { intros. apply (type_open_qt_fvar V (wf_typ_type E2 V HV) j Z). }
      unfold open_qe in Hres.
      rewrite (subst_te_open_qe_rec X V e1 0 Y Hwt HYX) in Hres.
      unfold open_qqt in Hres.
      rewrite (subst_tqt_open_qqt X V Hwt T1 0 Y HYX) in Hres.
      exact Hres.
  - (* qapp *) intros Q0 E0 e1 Q1 T0 H1 IH1 Hsubq. unfold te_motive.
    intros X V0 V E1 E2 Hwf HE HE2 HV HVV0. subst E0.
    simpl. unfold open_qqt. rewrite (subst_tqt_open_qqt_gen_wf E2 X V T0 0 Q0 HV).
    eapply typing_qapp.
    + exact (IH1 X V0 V E1 E2 Hwf eq_refl HE2 HV HVV0).
    + exact (subqual_subst_te_gen (E1 ++ X ~ bind_sub V0 ++ E2) Q0 Q1 Hsubq X V0 V E1 E2 Hwf eq_refl HE2 HV).
  - (* sub *) intros S E0 Q0 e1 T0 H1 IH1 Hsub. unfold te_motive.
    intros X V0 V E1 E2 Hwf HE HE2 HV HVV0. subst E0.
    simpl. eapply typing_sub.
    + exact (IH1 X V0 V E1 E2 Hwf eq_refl HE2 HV HVV0).
    + exact (subqtype_subst_te_gen (E1 ++ X ~ bind_sub V0 ++ E2) S T0 Hsub X V0 V E1 E2 Hwf eq_refl HE2 HV HVV0).
  - (* subqual *) intros E0 Q0 R e1 T0 H1 IH1 Hsubq. unfold te_motive.
    intros X V0 V E1 E2 Hwf HE HE2 HV HVV0. subst E0.
    simpl. eapply typing_subqual.
    + exact (IH1 X V0 V E1 E2 Hwf eq_refl HE2 HV HVV0).
    + exact (subqual_subst_te_gen (E1 ++ X ~ bind_sub V0 ++ E2) Q0 R Hsubq X V0 V E1 E2 Hwf eq_refl HE2 HV).
  - (* let *) intros L T1 T2 e1 e2 E0 Q0 H1 IH1 Hbody IHbody. unfold te_motive.
    intros X V0 V E1 E2 Hwf HE HE2 HV HVV0. subst E0.
    simpl. eapply typing_let with (L := L).
    + exact (IH1 X V0 V E1 E2 Hwf eq_refl HE2 HV HVV0).
    + intros x HxL.
      assert (Htyb : typing (x ~ bind_typ T1 ++ E1 ++ X ~ bind_sub V0 ++ E2) Q0
                       (open_ee e2 x) T2) by (apply Hbody; exact HxL).
      assert (Hwfb : wf_env (x ~ bind_typ T1 ++ E1 ++ X ~ bind_sub V0 ++ E2))
        by (eapply typing_wf_env; eassumption).
      assert (HEb : x ~ bind_typ T1 ++ E1 ++ X ~ bind_sub V0 ++ E2 =
                    (x ~ bind_typ T1 ++ E1) ++ X ~ bind_sub V0 ++ E2)
        by (rewrite app_assoc; reflexivity).
      pose proof (IHbody x HxL X V0 V (x ~ bind_typ T1 ++ E1) E2
                    Hwfb HEb HE2 HV HVV0) as Hres.
      rewrite subst_env_te_cons_app in Hres.
      unfold open_ee in Hres.
    rewrite (subst_te_open_ee_rec X V e2 0 x) in Hres.
      exact Hres.
  - (* inl *) intros T1 T2 P e1 E0 Q0 HwfP H1 IH1 HwT2. unfold te_motive.
    intros X V0 V E1 E2 Hwf HE HE2 HV HVV0. subst E0.
    simpl. eapply typing_inl.
    + exact (wf_qua_subst_env_te_mid E1 E2 X V0 V P Hwf HwfP).
    + exact (IH1 X V0 V E1 E2 Hwf eq_refl HE2 HV HVV0).
    + exact (wf_qtyp_subst_target_te (E1 ++ X ~ bind_sub V0 ++ E2) T2 X V0 V E1 E2 Hwf eq_refl HE2 HV HwT2).
  - (* inr *) intros T1 T2 P e1 E0 Q0 HwfP H1 IH1 HwT1. unfold te_motive.
    intros X V0 V E1 E2 Hwf HE HE2 HV HVV0. subst E0.
    simpl. eapply typing_inr.
    + exact (wf_qua_subst_env_te_mid E1 E2 X V0 V P Hwf HwfP).
    + exact (IH1 X V0 V E1 E2 Hwf eq_refl HE2 HV HVV0).
    + exact (wf_qtyp_subst_target_te (E1 ++ X ~ bind_sub V0 ++ E2) T1 X V0 V E1 E2 Hwf eq_refl HE2 HV HwT1).
  - (* case *) intros L T1 T2 P T0 e1 e2 e3 E0 Q0 H1 IH1 Hbody2 IHbody2 Hbody3 IHbody3. unfold te_motive.
    intros X V0 V E1 E2 Hwf HE HE2 HV HVV0. subst E0.
    simpl. eapply typing_case with (L := L).
    + exact (IH1 X V0 V E1 E2 Hwf eq_refl HE2 HV HVV0).
    + intros x HxL.
      assert (Htyb : typing (x ~ bind_typ T1 ++ E1 ++ X ~ bind_sub V0 ++ E2) Q0
                       (open_ee e2 x) T0) by (apply Hbody2; exact HxL).
      assert (Hwfb : wf_env (x ~ bind_typ T1 ++ E1 ++ X ~ bind_sub V0 ++ E2))
        by (eapply typing_wf_env; eassumption).
      assert (HEb : x ~ bind_typ T1 ++ E1 ++ X ~ bind_sub V0 ++ E2 =
                    (x ~ bind_typ T1 ++ E1) ++ X ~ bind_sub V0 ++ E2)
        by (rewrite app_assoc; reflexivity).
      pose proof (IHbody2 x HxL X V0 V (x ~ bind_typ T1 ++ E1) E2
                    Hwfb HEb HE2 HV HVV0) as Hres.
      rewrite subst_env_te_cons_app in Hres.
      unfold open_ee in Hres.
    rewrite (subst_te_open_ee_rec X V e2 0 x) in Hres.
      exact Hres.
    + intros x HxL.
      assert (Htyb : typing (x ~ bind_typ T2 ++ E1 ++ X ~ bind_sub V0 ++ E2) Q0
                       (open_ee e3 x) T0) by (apply Hbody3; exact HxL).
      assert (Hwfb : wf_env (x ~ bind_typ T2 ++ E1 ++ X ~ bind_sub V0 ++ E2))
        by (eapply typing_wf_env; eassumption).
      assert (HEb : x ~ bind_typ T2 ++ E1 ++ X ~ bind_sub V0 ++ E2 =
                    (x ~ bind_typ T2 ++ E1) ++ X ~ bind_sub V0 ++ E2)
        by (rewrite app_assoc; reflexivity).
      pose proof (IHbody3 x HxL X V0 V (x ~ bind_typ T2 ++ E1) E2
                    Hwfb HEb HE2 HV HVV0) as Hres.
      rewrite subst_env_te_cons_app in Hres.
      unfold open_ee in Hres.
    rewrite (subst_te_open_ee_rec X V e3 0 x) in Hres.
      exact Hres.
  - (* pair *) intros T1 T2 P e1 e2 E0 Q0 HwfP H1 IH1 H2 IH2. unfold te_motive.
    intros X V0 V E1 E2 Hwf HE HE2 HV HVV0. subst E0.
    simpl. eapply typing_pair.
    + exact (wf_qua_subst_env_te_mid E1 E2 X V0 V P Hwf HwfP).
    + exact (IH1 X V0 V E1 E2 Hwf eq_refl HE2 HV HVV0).
    + exact (IH2 X V0 V E1 E2 Hwf eq_refl HE2 HV HVV0).
  - (* first *) intros Q0 T1 T2 P e1 E0 H1 IH1. unfold te_motive.
    intros X V0 V E1 E2 Hwf HE HE2 HV HVV0. subst E0.
    simpl. eapply typing_first.
    exact (IH1 X V0 V E1 E2 Hwf eq_refl HE2 HV HVV0).
  - (* second *) intros Q0 T1 T2 P e1 E0 H1 IH1. unfold te_motive.
    intros X V0 V E1 E2 Hwf HE HE2 HV HVV0. subst E0.
    simpl. eapply typing_second.
    exact (IH1 X V0 V E1 E2 Hwf eq_refl HE2 HV HVV0).
  - (* upqual *) intros E0 R Q0 T0 P e1 H1 IH1 Hsubq. unfold te_motive.
    intros X V0 V E1 E2 Hwf HE HE2 HV HVV0. subst E0.
    simpl. eapply typing_upqual.
    + exact (IH1 X V0 V E1 E2 Hwf eq_refl HE2 HV HVV0).
    + exact (subqual_subst_te_gen (E1 ++ X ~ bind_sub V0 ++ E2) Q0 P Hsubq X V0 V E1 E2 Hwf eq_refl HE2 HV).
  - (* check *) intros E0 R Q0 T0 P e1 H1 IH1 Hsubq. unfold te_motive.
    intros X V0 V E1 E2 Hwf HE HE2 HV HVV0. subst E0.
    simpl. eapply typing_check.
    + exact (IH1 X V0 V E1 E2 Hwf eq_refl HE2 HV HVV0).
    + exact (subqual_subst_te_gen (E1 ++ X ~ bind_sub V0 ++ E2) Q0 P Hsubq X V0 V E1 E2 Hwf eq_refl HE2 HV).
  - exact Hty.
Qed.


(* ===== inlined from /tmp/w6/TypQe.v ===== *)

Lemma wf_typ_subst_target_qe : forall E T X R0 Rsub E1 E2,
  wf_env E -> E = E1 ++ X ~ bind_qua R0 ++ E2 ->
  wf_env E2 -> wf_qua E2 Rsub -> wf_typ E T ->
  wf_typ (subst_env_qe X Rsub (E1 ++ E2)) (subst_qt X Rsub T).
Proof.
  intros E T X R0 Rsub E1 E2 Hwf HE HE2 HV HT.
  assert (Hwtgt : wf_env (subst_env_qe X Rsub (E1 ++ E2)))
    by (exact (wf_env_subst_qe_gen E X R0 Rsub E1 E2 Hwf HE HE2 HV)).
  assert (HVtgt : wf_qua (subst_env_qe X Rsub (E1 ++ E2)) Rsub)
    by (exact (subst_qe_target_R_wf E X R0 Rsub E1 E2 Hwf HE HE2 HV)).
  exact (wf_typ_subst_drop_qe E T HT E1 E2 X R0 Rsub HE Hwf Hwtgt HVtgt).
Qed.

Lemma wf_qtyp_subst_target_qe : forall E T X R0 Rsub E1 E2,
  wf_env E -> E = E1 ++ X ~ bind_qua R0 ++ E2 ->
  wf_env E2 -> wf_qua E2 Rsub -> wf_qtyp E T ->
  wf_qtyp (subst_env_qe X Rsub (E1 ++ E2)) (subst_qqt X Rsub T).
Proof.
  intros E T X R0 Rsub E1 E2 Hwf HE HE2 HV HT.
  assert (Hwtgt : wf_env (subst_env_qe X Rsub (E1 ++ E2)))
    by (exact (wf_env_subst_qe_gen E X R0 Rsub E1 E2 Hwf HE HE2 HV)).
  assert (HVtgt : wf_qua (subst_env_qe X Rsub (E1 ++ E2)) Rsub)
    by (exact (subst_qe_target_R_wf E X R0 Rsub E1 E2 Hwf HE HE2 HV)).
  exact (wf_qtyp_subst_drop_qe E T HT E1 E2 X R0 Rsub HE Hwf Hwtgt HVtgt).
Qed.

Definition qe_motive (E : env) (Q : qua) (e : exp) (T : qtyp) : Prop :=
  forall X R0 Rsub E1 E2,
    wf_env E -> E = E1 ++ X ~ bind_qua R0 ++ E2 ->
    wf_env E2 -> wf_qua E2 Rsub -> subqual E2 Rsub R0 ->
    typing (subst_env_qe X Rsub (E1 ++ E2)) (subst_qq X Rsub Q)
      (subst_qe X Rsub e) (subst_qqt X Rsub T).

Lemma typing_subst_qe_gen : forall E Q e T,
  typing E Q e T -> qe_motive E Q e T.
Proof.
  intros E Q e T Hty. change (qe_motive E Q e T).
  apply typing_ind with (P := qe_motive).
  - (* var *) intros E0 x T0 HwfE Hb. unfold qe_motive.
    intros X R0 Rsub E1 E2 Hwf HE HE2 HV HVV0. subst E0.
    simpl. eapply typing_var.
    + exact (wf_env_subst_qe_gen (E1 ++ X ~ bind_qua R0 ++ E2) X R0 Rsub E1 E2 Hwf eq_refl HE2 HV).
    + destruct (eq_dec x X) as [Heq|Hne].
      * subst x. exfalso.
        assert (HbX : binds X (bind_qua R0) (E1 ++ X ~ bind_qua R0 ++ E2)).
        { apply binds_app_r, binds_app_l, binds_cons_2; reflexivity. }
        pose proof (binds_unique binding X (bind_typ T0) (bind_qua R0)
                      (E1 ++ X ~ bind_qua R0 ++ E2) Hb HbX (wf_env_uniq _ Hwf)) as Hbad.
        discriminate Hbad.
      * exact (binds_subst_env_qe_drop E1 E2 X R0 Rsub x (bind_typ T0) Hne Hb).
  - (* abs *) intros L E0 P Vabs e1 T1 Hbody IHbody. unfold qe_motive.
    intros X R0 Rsub E1 E2 Hwf HE HE2 HV HVV0. subst E0.
    simpl. eapply typing_abs with (L := L).
    intros x HxL.
    assert (Htyb : typing (x ~ bind_typ Vabs ++ E1 ++ X ~ bind_qua R0 ++ E2) P
                     (open_ee e1 x) T1) by (apply Hbody; exact HxL).
    assert (Hwfb : wf_env (x ~ bind_typ Vabs ++ E1 ++ X ~ bind_qua R0 ++ E2))
      by (eapply typing_wf_env; eassumption).
    assert (HEb : x ~ bind_typ Vabs ++ E1 ++ X ~ bind_qua R0 ++ E2 =
                  (x ~ bind_typ Vabs ++ E1) ++ X ~ bind_qua R0 ++ E2)
      by (rewrite app_assoc; reflexivity).
    pose proof (IHbody x HxL X R0 Rsub (x ~ bind_typ Vabs ++ E1) E2
                  Hwfb HEb HE2 HV HVV0) as Hres.
    rewrite subst_env_qe_cons_app in Hres.
    unfold open_ee in Hres.
    rewrite (subst_qe_open_ee_rec X Rsub e1 0 x) in Hres.
    exact Hres.
  - (* app *) intros Q0 T1 E0 e1 e2 T2 H1 IH1 H2 IH2. unfold qe_motive.
    intros X R0 Rsub E1 E2 Hwf HE HE2 HV HVV0. subst E0.
    simpl. eapply typing_app.
    + exact (IH1 X R0 Rsub E1 E2 Hwf eq_refl HE2 HV HVV0).
    + exact (IH2 X R0 Rsub E1 E2 Hwf eq_refl HE2 HV HVV0).
  - (* tabs *) intros L E0 P Vabs e1 T1 Hbody IHbody. unfold qe_motive.
    intros X R0 Rsub E1 E2 Hwf HE HE2 HV HVV0. subst E0.
    simpl. eapply typing_tabs with (L := union L (singleton X)).
    intros Y HY.
    assert (HYL : Y `notin` L) by fsetdec.
    assert (HYX : Y <> X) by fsetdec.
    assert (Htyb : typing (Y ~ bind_sub Vabs ++ E1 ++ X ~ bind_qua R0 ++ E2) P
                     (open_te e1 Y) (open_tqt T1 Y)) by (apply Hbody; exact HYL).
    assert (Hwfb : wf_env (Y ~ bind_sub Vabs ++ E1 ++ X ~ bind_qua R0 ++ E2))
      by (eapply typing_wf_env; eassumption).
    assert (HEb : Y ~ bind_sub Vabs ++ E1 ++ X ~ bind_qua R0 ++ E2 =
                  (Y ~ bind_sub Vabs ++ E1) ++ X ~ bind_qua R0 ++ E2)
      by (rewrite app_assoc; reflexivity).
    pose proof (IHbody Y HYL X R0 Rsub (Y ~ bind_sub Vabs ++ E1) E2
                  Hwfb HEb HE2 HV HVV0) as Hres.
    rewrite subst_env_qe_cons_app in Hres.
    unfold open_te in Hres.
    rewrite (subst_qe_open_te_rec X Rsub e1 0 Y) in Hres.
    unfold open_tqt in Hres.
    rewrite (subst_qqt_open_tqt_gen X Rsub T1 0 Y) in Hres.
    exact Hres.
  - (* tapp *) intros Q0 T1 E0 e1 Targ T2 H1 IH1 Hsub. unfold qe_motive.
    intros X R0 Rsub E1 E2 Hwf HE HE2 HV HVV0. subst E0.
    simpl. unfold open_tqt. rewrite (subst_qqt_open_tqt_gen X Rsub T2 0 Targ).
    eapply typing_tapp.
    + exact (IH1 X R0 Rsub E1 E2 Hwf eq_refl HE2 HV HVV0).
    + exact (sub_subst_qe_gen (E1 ++ X ~ bind_qua R0 ++ E2) Targ T1 Hsub X R0 Rsub E1 E2 Hwf eq_refl HE2 HV HVV0).
  - (* qabs *) intros L E0 P Q0 e1 T1 HwfP Hbody IHbody. unfold qe_motive.
    intros X R0 Rsub E1 E2 Hwf HE HE2 HV HVV0. subst E0.
    simpl. eapply typing_qabs with (L := union L (singleton X)).
    + exact (wf_qua_subst_env_qe_mid E1 E2 X R0 Rsub P Hwf HwfP (subst_qe_target_R_wf (E1 ++ X ~ bind_qua R0 ++ E2) X R0 Rsub E1 E2 Hwf eq_refl HE2 HV)).
    + intros Y HY.
      assert (HYL : Y `notin` L) by fsetdec.
      assert (HYX : Y <> X) by fsetdec.
      assert (Htyb : typing (Y ~ bind_qua Q0 ++ E1 ++ X ~ bind_qua R0 ++ E2) P
                       (open_qe e1 Y) (open_qqt T1 Y)) by (apply Hbody; exact HYL).
      assert (Hwfb : wf_env (Y ~ bind_qua Q0 ++ E1 ++ X ~ bind_qua R0 ++ E2))
        by (eapply typing_wf_env; eassumption).
      assert (HEb : Y ~ bind_qua Q0 ++ E1 ++ X ~ bind_qua R0 ++ E2 =
                    (Y ~ bind_qua Q0 ++ E1) ++ X ~ bind_qua R0 ++ E2)
        by (rewrite app_assoc; reflexivity).
      pose proof (IHbody Y HYL X R0 Rsub (Y ~ bind_qua Q0 ++ E1) E2
                    Hwfb HEb HE2 HV HVV0) as Hres.
      rewrite subst_env_qe_cons_app in Hres.
      unfold open_qe in Hres.
      rewrite (subst_qe_open_qe_rec E2 X Rsub e1 0 Y HV HYX) in Hres.
      unfold open_qqt in Hres.
      rewrite (subst_qqt_open_qqt_wf E2 X Rsub T1 0 Y HV HYX) in Hres.
      exact Hres.
  - (* qapp *) intros Q0 E0 e1 Q1 T0 H1 IH1 Hsubq. unfold qe_motive.
    intros X R0 Rsub E1 E2 Hwf HE HE2 HV HVV0. subst E0.
    simpl. unfold open_qqt.
    rewrite (subst_qqt_open_qqt X Rsub (fun j S => wf_qua_open_qq E2 Rsub HV j S) T0 0 Q0).
    eapply typing_qapp.
    + exact (IH1 X R0 Rsub E1 E2 Hwf eq_refl HE2 HV HVV0).
    + exact (subqual_subst_qe_gen (E1 ++ X ~ bind_qua R0 ++ E2) Q0 Q1 Hsubq X R0 Rsub E1 E2 Hwf eq_refl HE2 HV HVV0).
  - (* sub *) intros S E0 Q0 e1 T0 H1 IH1 Hsub. unfold qe_motive.
    intros X R0 Rsub E1 E2 Hwf HE HE2 HV HVV0. subst E0.
    simpl. eapply typing_sub.
    + exact (IH1 X R0 Rsub E1 E2 Hwf eq_refl HE2 HV HVV0).
    + exact (subqtype_subst_qe_gen (E1 ++ X ~ bind_qua R0 ++ E2) S T0 Hsub X R0 Rsub E1 E2 Hwf eq_refl HE2 HV HVV0).
  - (* subqual *) intros E0 Q0 R e1 T0 H1 IH1 Hsubq. unfold qe_motive.
    intros X R0 Rsub E1 E2 Hwf HE HE2 HV HVV0. subst E0.
    simpl. eapply typing_subqual.
    + exact (IH1 X R0 Rsub E1 E2 Hwf eq_refl HE2 HV HVV0).
    + exact (subqual_subst_qe_gen (E1 ++ X ~ bind_qua R0 ++ E2) Q0 R Hsubq X R0 Rsub E1 E2 Hwf eq_refl HE2 HV HVV0).
  - (* let *) intros L T1 T2 e1 e2 E0 Q0 H1 IH1 Hbody IHbody. unfold qe_motive.
    intros X R0 Rsub E1 E2 Hwf HE HE2 HV HVV0. subst E0.
    simpl. eapply typing_let with (L := L).
    + exact (IH1 X R0 Rsub E1 E2 Hwf eq_refl HE2 HV HVV0).
    + intros x HxL.
      assert (Htyb : typing (x ~ bind_typ T1 ++ E1 ++ X ~ bind_qua R0 ++ E2) Q0
                       (open_ee e2 x) T2) by (apply Hbody; exact HxL).
      assert (Hwfb : wf_env (x ~ bind_typ T1 ++ E1 ++ X ~ bind_qua R0 ++ E2))
        by (eapply typing_wf_env; eassumption).
      assert (HEb : x ~ bind_typ T1 ++ E1 ++ X ~ bind_qua R0 ++ E2 =
                    (x ~ bind_typ T1 ++ E1) ++ X ~ bind_qua R0 ++ E2)
        by (rewrite app_assoc; reflexivity).
      pose proof (IHbody x HxL X R0 Rsub (x ~ bind_typ T1 ++ E1) E2
                    Hwfb HEb HE2 HV HVV0) as Hres.
      rewrite subst_env_qe_cons_app in Hres.
      unfold open_ee in Hres.
    rewrite (subst_qe_open_ee_rec X Rsub e2 0 x) in Hres.
      exact Hres.
  - (* inl *) intros T1 T2 P e1 E0 Q0 HwfP H1 IH1 HwT2. unfold qe_motive.
    intros X R0 Rsub E1 E2 Hwf HE HE2 HV HVV0. subst E0.
    simpl. eapply typing_inl.
    + exact (wf_qua_subst_env_qe_mid E1 E2 X R0 Rsub P Hwf HwfP (subst_qe_target_R_wf (E1 ++ X ~ bind_qua R0 ++ E2) X R0 Rsub E1 E2 Hwf eq_refl HE2 HV)).
    + exact (IH1 X R0 Rsub E1 E2 Hwf eq_refl HE2 HV HVV0).
    + exact (wf_qtyp_subst_target_qe (E1 ++ X ~ bind_qua R0 ++ E2) T2 X R0 Rsub E1 E2 Hwf eq_refl HE2 HV HwT2).
  - (* inr *) intros T1 T2 P e1 E0 Q0 HwfP H1 IH1 HwT1. unfold qe_motive.
    intros X R0 Rsub E1 E2 Hwf HE HE2 HV HVV0. subst E0.
    simpl. eapply typing_inr.
    + exact (wf_qua_subst_env_qe_mid E1 E2 X R0 Rsub P Hwf HwfP (subst_qe_target_R_wf (E1 ++ X ~ bind_qua R0 ++ E2) X R0 Rsub E1 E2 Hwf eq_refl HE2 HV)).
    + exact (IH1 X R0 Rsub E1 E2 Hwf eq_refl HE2 HV HVV0).
    + exact (wf_qtyp_subst_target_qe (E1 ++ X ~ bind_qua R0 ++ E2) T1 X R0 Rsub E1 E2 Hwf eq_refl HE2 HV HwT1).
  - (* case *) intros L T1 T2 P T0 e1 e2 e3 E0 Q0 H1 IH1 Hbody2 IHbody2 Hbody3 IHbody3. unfold qe_motive.
    intros X R0 Rsub E1 E2 Hwf HE HE2 HV HVV0. subst E0.
    simpl. eapply typing_case with (L := L).
    + exact (IH1 X R0 Rsub E1 E2 Hwf eq_refl HE2 HV HVV0).
    + intros x HxL.
      assert (Htyb : typing (x ~ bind_typ T1 ++ E1 ++ X ~ bind_qua R0 ++ E2) Q0
                       (open_ee e2 x) T0) by (apply Hbody2; exact HxL).
      assert (Hwfb : wf_env (x ~ bind_typ T1 ++ E1 ++ X ~ bind_qua R0 ++ E2))
        by (eapply typing_wf_env; eassumption).
      assert (HEb : x ~ bind_typ T1 ++ E1 ++ X ~ bind_qua R0 ++ E2 =
                    (x ~ bind_typ T1 ++ E1) ++ X ~ bind_qua R0 ++ E2)
        by (rewrite app_assoc; reflexivity).
      pose proof (IHbody2 x HxL X R0 Rsub (x ~ bind_typ T1 ++ E1) E2
                    Hwfb HEb HE2 HV HVV0) as Hres.
      rewrite subst_env_qe_cons_app in Hres.
      unfold open_ee in Hres.
    rewrite (subst_qe_open_ee_rec X Rsub e2 0 x) in Hres.
      exact Hres.
    + intros x HxL.
      assert (Htyb : typing (x ~ bind_typ T2 ++ E1 ++ X ~ bind_qua R0 ++ E2) Q0
                       (open_ee e3 x) T0) by (apply Hbody3; exact HxL).
      assert (Hwfb : wf_env (x ~ bind_typ T2 ++ E1 ++ X ~ bind_qua R0 ++ E2))
        by (eapply typing_wf_env; eassumption).
      assert (HEb : x ~ bind_typ T2 ++ E1 ++ X ~ bind_qua R0 ++ E2 =
                    (x ~ bind_typ T2 ++ E1) ++ X ~ bind_qua R0 ++ E2)
        by (rewrite app_assoc; reflexivity).
      pose proof (IHbody3 x HxL X R0 Rsub (x ~ bind_typ T2 ++ E1) E2
                    Hwfb HEb HE2 HV HVV0) as Hres.
      rewrite subst_env_qe_cons_app in Hres.
      unfold open_ee in Hres.
    rewrite (subst_qe_open_ee_rec X Rsub e3 0 x) in Hres.
      exact Hres.
  - (* pair *) intros T1 T2 P e1 e2 E0 Q0 HwfP H1 IH1 H2 IH2. unfold qe_motive.
    intros X R0 Rsub E1 E2 Hwf HE HE2 HV HVV0. subst E0.
    simpl. eapply typing_pair.
    + exact (wf_qua_subst_env_qe_mid E1 E2 X R0 Rsub P Hwf HwfP (subst_qe_target_R_wf (E1 ++ X ~ bind_qua R0 ++ E2) X R0 Rsub E1 E2 Hwf eq_refl HE2 HV)).
    + exact (IH1 X R0 Rsub E1 E2 Hwf eq_refl HE2 HV HVV0).
    + exact (IH2 X R0 Rsub E1 E2 Hwf eq_refl HE2 HV HVV0).
  - (* first *) intros Q0 T1 T2 P e1 E0 H1 IH1. unfold qe_motive.
    intros X R0 Rsub E1 E2 Hwf HE HE2 HV HVV0. subst E0.
    simpl. eapply typing_first.
    exact (IH1 X R0 Rsub E1 E2 Hwf eq_refl HE2 HV HVV0).
  - (* second *) intros Q0 T1 T2 P e1 E0 H1 IH1. unfold qe_motive.
    intros X R0 Rsub E1 E2 Hwf HE HE2 HV HVV0. subst E0.
    simpl. eapply typing_second.
    exact (IH1 X R0 Rsub E1 E2 Hwf eq_refl HE2 HV HVV0).
  - (* upqual *) intros E0 R Q0 T0 P e1 H1 IH1 Hsubq. unfold qe_motive.
    intros X R0 Rsub E1 E2 Hwf HE HE2 HV HVV0. subst E0.
    simpl. eapply typing_upqual.
    + exact (IH1 X R0 Rsub E1 E2 Hwf eq_refl HE2 HV HVV0).
    + exact (subqual_subst_qe_gen (E1 ++ X ~ bind_qua R0 ++ E2) Q0 P Hsubq X R0 Rsub E1 E2 Hwf eq_refl HE2 HV HVV0).
  - (* check *) intros E0 R Q0 T0 P e1 H1 IH1 Hsubq. unfold qe_motive.
    intros X R0 Rsub E1 E2 Hwf HE HE2 HV HVV0. subst E0.
    simpl. eapply typing_check.
    + exact (IH1 X R0 Rsub E1 E2 Hwf eq_refl HE2 HV HVV0).
    + exact (subqual_subst_qe_gen (E1 ++ X ~ bind_qua R0 ++ E2) Q0 P Hsubq X R0 Rsub E1 E2 Hwf eq_refl HE2 HV HVV0).
  - exact Hty.
Qed.


(* ===== inlined from /tmp/w6/Pres.v ===== *)


Lemma wf_qtyp_qtyp_inv : forall E Q T,
  wf_qtyp E (qtyp_qtyp Q T) -> wf_qua E Q /\ wf_typ E T.
Proof. intros E Q T H. inversion H; subst. auto. Qed.

Lemma wf_typ_all_inv : forall E T1 T2,
  wf_typ E (typ_all T1 T2) ->
  wf_typ E T1 /\ exists L, forall X, X `notin` L ->
    wf_qtyp (X ~ bind_sub T1 ++ E) (open_tqt T2 X).
Proof.
  intros E T1 T2 H. inversion H; subst. split; [assumption|].
  exists L. assumption.
Qed.

Lemma wf_typ_qall_inv : forall E Q T,
  wf_typ E (typ_qall Q T) ->
  wf_qua E Q /\ exists L, forall X, X `notin` L ->
    wf_qtyp (X ~ bind_qua Q ++ E) (open_qqt T X).
Proof.
  intros E Q T H. inversion H; subst. split; [assumption|].
  exists L. assumption.
Qed.

Lemma wf_typ_pair_inv : forall E T1 T2,
  wf_typ E (typ_pair T1 T2) -> wf_qtyp E T1 /\ wf_qtyp E T2.
Proof. intros E T1 T2 H. inversion H; subst. auto. Qed.

Lemma wf_typ_sum_inv : forall E T1 T2,
  wf_typ E (typ_sum T1 T2) -> wf_qtyp E T1 /\ wf_qtyp E T2.
Proof. intros E T1 T2 H. inversion H; subst. auto. Qed.


Lemma subqual_trans_env : forall E Q R S,
  wf_env E -> subqual E Q R -> subqual E R S -> subqual E Q S.
Proof. intros E Q R S _. eapply subqual_trans_nowf; eassumption. Qed.
Definition sub_trans_env : forall E S T U,
  wf_env E -> sub E S T -> sub E T U -> sub E S U
  := sub_trans_size.
Definition subqtype_trans_env : forall E S T U,
  wf_env E -> subqtype E S T -> subqtype E T U -> subqtype E S U
  := subqtype_trans_size.


Lemma qsubR_qtyp_qual_gen : forall E S T,
  wf_env E -> qsubR E S T ->
  forall Q1 T1, S = qtyp_qtyp Q1 T1 -> wf_qua E Q1 ->
  exists Q2 T2, T = qtyp_qtyp Q2 T2 /\ subqual E Q1 Q2.
Proof.
  intros E S T Hwf Hchain. induction Hchain as [X|X Y Z Hxy IH Hstep].
  - intros Q1 T1 Heq HQ1. inversion Heq; subst.
    exists Q1, T1. split; [reflexivity|].
    apply subqual_refl; assumption.
  - intros Q1 T1 Heq HQ1.
    destruct (IH Q1 T1 Heq HQ1) as [Qm [Tm [Heqm Hqual]]].
    inversion Hstep; subst.
    match goal with H2 : qtyp_qtyp ?A ?B = qtyp_qtyp ?C ?D |- _ =>
      injection H2 as -> -> end.
    exists Q2, T2. split; [reflexivity|].
    eapply subqual_trans_env with (R := Qm).
    + exact Hwf.
    + exact Hqual.
    + match goal with H : subqual E Qm Q2 |- _ => exact H end.
Qed.

Lemma qsubR_qtyp_qual : forall E Q1 Q2 T1 T2,
  wf_env E -> wf_qua E Q1 ->
  qsubR E (qtyp_qtyp Q1 T1) (qtyp_qtyp Q2 T2) -> subqual E Q1 Q2.
Proof.
  intros E Q1 Q2 T1 T2 Hwf HQ H.
  destruct (qsubR_qtyp_qual_gen E (qtyp_qtyp Q1 T1) (qtyp_qtyp Q2 T2) Hwf H Q1 T1 eq_refl HQ)
    as [Q' [T' [Heq Hq]]].
  inversion Heq; subst. exact Hq.
Qed.


Lemma qsubL_wf_target : forall E S T,
  wf_env E -> wf_qtyp E S -> qsubL E S T -> wf_qtyp E T.
Proof.
  intros E S T Hwf HwS H. induction H as [X|S0 T0 U Hstep Htail IH].
  - exact HwS.
  - apply IH. eapply subqtype_wf_target; [exact Hstep|exact Hwf|exact HwS].
Qed.

Section Hyp.

Lemma typing_subst_te_remove : forall E Q e T X V V0,
  typing (X ~ bind_sub V0 ++ E) Q e T ->
  wf_env E -> wf_typ E V -> sub E V V0 ->
  typing E Q (subst_te X V e) (subst_tqt X V T).
Proof.
  intros E Q e T X V V0 Hty Hwf HV HVV0.
  assert (HwfFull : wf_env (X ~ bind_sub V0 ++ E))
    by (eapply typing_wf_env; eassumption).
  assert (HX : X `notin` dom E)
    by (eapply (wf_env_mid_notin_tail nil X (bind_sub V0) E); exact HwfFull).
  pose proof (typing_subst_te_gen (X ~ bind_sub V0 ++ E) Q e T Hty
                X V0 V nil E HwfFull eq_refl Hwf HV HVV0) as H.
  simpl in H.
  rewrite (subst_env_te_id X V E Hwf HX) in H.
  exact H.
Qed.

Lemma subqtype_subst_te_remove : forall E S T X V V0,
  subqtype (X ~ bind_sub V0 ++ E) S T ->
  wf_env E -> X `notin` dom E -> wf_typ E V -> sub E V V0 ->
  subqtype E (subst_tqt X V S) (subst_tqt X V T).
Proof.
  intros E S T X V V0 Hsub Hwf HX HV HVV0.
  assert (HwV0 : wf_typ E V0) by (eapply sub_wf; eassumption).
  assert (HwfFull : wf_env (X ~ bind_sub V0 ++ E)) by (apply wf_env_sub; assumption).
  pose proof (subqtype_subst_te_gen (X ~ bind_sub V0 ++ E) S T Hsub
                X V0 V nil E HwfFull eq_refl Hwf HV HVV0) as H.
  simpl in H.
  rewrite (subst_env_te_id X V E Hwf HX) in H.
  exact H.
Qed.

Lemma typing_subst_qe_remove : forall E Q e T X R R0,
  typing (X ~ bind_qua R0 ++ E) Q e T ->
  wf_env E -> wf_qua E R -> subqual E R R0 ->
  X `notin` fv_qq Q ->
  typing E Q (subst_qe X R e) (subst_qqt X R T).
Proof.
  intros E Q e T X R R0 Hty Hwf HR HRR0 HXQ.
  assert (HwfFull : wf_env (X ~ bind_qua R0 ++ E))
    by (eapply typing_wf_env; eassumption).
  assert (HX : X `notin` dom E)
    by (eapply (wf_env_mid_notin_tail nil X (bind_qua R0) E); exact HwfFull).
  pose proof (typing_subst_qe_gen (X ~ bind_qua R0 ++ E) Q e T Hty
                X R0 R nil E HwfFull eq_refl Hwf HR HRR0) as H.
  simpl in H.
  rewrite (subst_env_qe_id X R E Hwf HX) in H.
  rewrite (subst_qq_nofv X R Q HXQ) in H.
  exact H.
Qed.

Lemma subqtype_subst_qe_remove : forall E S T X R R0,
  subqtype (X ~ bind_qua R0 ++ E) S T ->
  wf_env E -> X `notin` dom E -> wf_qua E R -> subqual E R R0 ->
  subqtype E (subst_qqt X R S) (subst_qqt X R T).
Proof.
  intros E S T X R R0 Hsub Hwf HX HR HRR0.
  assert (HR0 : wf_qua E R0) by (exact (proj2 (subqual_wf E R R0 Hwf HRR0))).
  assert (HwfFull : wf_env (X ~ bind_qua R0 ++ E))
    by (apply wf_env_qua; assumption).
  pose proof (subqtype_subst_qe_gen (X ~ bind_qua R0 ++ E) S T Hsub
                X R0 R nil E HwfFull eq_refl Hwf HR HRR0) as H.
  simpl in H.
  rewrite (subst_env_qe_id X R E Hwf HX) in H.
  exact H.
Qed.



(* Remaining step families, stated as parameters (they are the cases that need
   the full substitution/barrier machinery or component-wise subtyping inversion). *)

(* ---------- value-step cases (no substitution needed) ---------- *)

Lemma preserve_pair_2 : forall E Q v P e K T,
  value v ->
  typing E Q v T ->
  typing_ctx E Q (frame_pair_1 P e :: K) T ->
  typing_state E〈 e | frame_pair_2 P v :: K 〉.
Proof.
  intros E Q v P e K T Hval Hty Hctx.
  destruct (typing_ctx_pair_1_inv_syn E Q P e K T Hctx)
    as [Q0 [T1 [T2 [HwfP [Hk [He [HqL HqsL]]]]]]].
  apply (typing_step E Q0 e (frame_pair_2 P v :: K) T2).
  - exact He.
  - eapply typing_ctx_pair_2 with (P := P) (T1 := T1) (T2 := T2).
    + exact HwfP.
    + exact Hk.
    + exact Hval.
    + apply (typing_forward_qualL E Q Q0).
      * exact HqL.
      * apply (typing_forward_qsubL E T T1).
        -- exact HqsL.
        -- exact Hty.
Qed.

Lemma preserve_make_inl : forall E Q P v K T,
  value v ->
  typing E Q v T ->
  typing_ctx E Q (frame_inl P :: K) T ->
  typing_state E〈 exp_inl P v | K 〉.
Proof.
  intros E Q P v K T Hval Hty Hctx.
  destruct (typing_ctx_inl_inv_syn E Q P K T Hctx)
    as [Q0 [T1 [T2 [Hk [HqL HqsL]]]]].
  assert (Hwf : wf_env E) by (eapply typing_ctx_wf_env; eassumption).
  assert (Hwfq : wf_qtyp E (qtyp_qtyp P (typ_sum T1 T2))).
  { apply (typing_ctx_wf_qtyp E Q0 K (qtyp_qtyp P (typ_sum T1 T2))); assumption. }
  destruct (wf_qtyp_qtyp_inv E P (typ_sum T1 T2) Hwfq) as [HwfP Hwtsum].
  destruct (wf_typ_sum_inv E T1 T2 Hwtsum) as [HwfT1 HwfT2].
  assert (Hv1 : typing E Q0 v T1).
  { apply (typing_forward_qualL E Q Q0); [exact HqL|].
    apply (typing_forward_qsubL E T T1); [exact HqsL|exact Hty]. }
  apply (typing_step E Q0 (exp_inl P v) K (qtyp_qtyp P (typ_sum T1 T2))).
  - eapply typing_inl; eassumption.
  - exact Hk.
Qed.

Lemma preserve_make_inr : forall E Q P v K T,
  value v ->
  typing E Q v T ->
  typing_ctx E Q (frame_inr P :: K) T ->
  typing_state E〈 exp_inr P v | K 〉.
Proof.
  intros E Q P v K T Hval Hty Hctx.
  destruct (typing_ctx_inr_inv_syn E Q P K T Hctx)
    as [Q0 [T1 [T2 [Hk [HqL HqsL]]]]].
  assert (Hwf : wf_env E) by (eapply typing_ctx_wf_env; eassumption).
  assert (Hwfq : wf_qtyp E (qtyp_qtyp P (typ_sum T1 T2))).
  { apply (typing_ctx_wf_qtyp E Q0 K (qtyp_qtyp P (typ_sum T1 T2))); assumption. }
  destruct (wf_qtyp_qtyp_inv E P (typ_sum T1 T2) Hwfq) as [HwfP Hwtsum].
  destruct (wf_typ_sum_inv E T1 T2 Hwtsum) as [HwfT1 HwfT2].
  assert (Hv2 : typing E Q0 v T2).
  { apply (typing_forward_qualL E Q Q0); [exact HqL|].
    apply (typing_forward_qsubL E T T2); [exact HqsL|exact Hty]. }
  apply (typing_step E Q0 (exp_inr P v) K (qtyp_qtyp P (typ_sum T1 T2))).
  - eapply typing_inr; eassumption.
  - exact Hk.
Qed.

Lemma preserve_make_pair : forall E Q P v1 v2 K T,
  value v2 ->
  typing E Q v2 T ->
  typing_ctx E Q (frame_pair_2 P v1 :: K) T ->
  typing_state E〈 exp_pair P v1 v2 | K 〉.
Proof.
  intros E Q P v1 v2 K T Hval2 Hty2 Hctx.
  destruct (typing_ctx_pair_2_inv_syn E Q P v1 K T Hctx)
    as [Q0 [T1 [T2 [HwfP [Hk [Hval1 [Hv1 [HqL HqsL]]]]]]]].
  assert (Hv2 : typing E Q0 v2 T2).
  { apply (typing_forward_qualL E Q Q0); [exact HqL|].
    apply (typing_forward_qsubL E T T2); [exact HqsL|exact Hty2]. }
  apply (typing_step E Q0 (exp_pair P v1 v2) K (qtyp_qtyp P (typ_pair T1 T2))).
  - eapply typing_pair; eassumption.
  - exact Hk.
Qed.


Lemma subqtype_qtyp_qual : forall E Q R T,
  wf_env E -> wf_qtyp E (qtyp_qtyp Q T) -> subqual E Q R ->
  subqtype E (qtyp_qtyp Q T) (qtyp_qtyp R T).
Proof.
  intros E Q R T Hwf Hwq Hs.
  destruct (wf_qtyp_qtyp_inv E Q T Hwq) as [_ Hwt].
  apply sub_qtyp_qtyp; [exact Hs|].
  apply sub_refl_wf; assumption.
Qed.

(* A helper: qtyp subtyping that only changes the qualifier. *)
Lemma subqtype_same_typ : forall E Q R T,
  wf_env E -> wf_qtyp E (qtyp_qtyp Q T) -> subqual E R Q ->
  subqtype E (qtyp_qtyp R T) (qtyp_qtyp Q T).
Proof.
  intros E Q R T Hwf Hwq Hs.
  destruct (wf_qtyp_qtyp_inv E Q T Hwq) as [_ Hwt].
  apply sub_qtyp_qtyp; [exact Hs|].
  apply sub_refl_wf; assumption.
Qed.

Lemma preserve_upqual_1 : forall E Q P e K T,
  typing E Q (exp_upqual P e) T ->
  typing_ctx E Q K T ->
  typing_state E〈 e | frame_upqual P :: K 〉.
Proof.
  intros E Q P e K T Hty Hctx.
  destruct (typing_upqual_inv_syn E Q P e T Hty)
    as [Qe [Qtyp [T0 [He [Hsub [Hq Hqs]]]]]].
  assert (Hwf : wf_env E) by (eapply typing_wf_env; eassumption).
  assert (Hwq_payload : wf_qtyp E (qtyp_qtyp Qtyp T0)).
  { apply (typing_wf_qtyp E Qe e (qtyp_qtyp Qtyp T0)); assumption. }
  assert (Hsq : subqtype E (qtyp_qtyp Qtyp T0) (qtyp_qtyp P T0)).
  { apply subqtype_qtyp_qual; [exact Hwf|exact Hwq_payload|exact Hsub]. }
  apply (typing_step E Qe e (frame_upqual P :: K) (qtyp_qtyp P T0)).
  - apply typing_sub with (S := qtyp_qtyp Qtyp T0); [exact He|exact Hsq].
  - apply typing_ctx_upqual.
    apply (typing_ctx_to_qsubL E (qtyp_qtyp P T0) T).
    + apply qsubR_to_qsubL. exact Hqs.
    + apply (typing_ctx_to_qualL E Qe Q).
      * apply qualR_to_qualL. exact Hq.
      * exact Hctx.
Qed.

Lemma preserve_check_1 : forall E Q P e K T,
  typing E Q (exp_check P e) T ->
  typing_ctx E Q K T ->
  typing_state E〈 e | frame_check P :: K 〉.
Proof.
  intros E Q P e K T Hty Hctx.
  destruct (typing_check_inv_syn E Q P e T Hty)
    as [Qe [Qtyp [T0 [He [Hsub [Hq Hqs]]]]]].
  assert (Hwf : wf_env E) by (eapply typing_wf_env; eassumption).
  assert (Hwq_payload : wf_qtyp E (qtyp_qtyp Qtyp T0)).
  { apply (typing_wf_qtyp E Qe e (qtyp_qtyp Qtyp T0)); assumption. }
  assert (HwqP : wf_qua E P).
  { apply (proj2 (subqual_wf E Qtyp P Hwf Hsub)). }
  (* payload retyped to meet Qtyp P *)
  assert (Hmeet_sub : subqual E Qtyp (qua_meet Qtyp P)).
  { apply subqual_meet_intro.
    - apply subqual_refl; [exact Hwf|].
      apply (proj1 (subqual_wf E Qtyp P Hwf Hsub)).
    - exact Hsub. }
  assert (Hsq : subqtype E (qtyp_qtyp Qtyp T0) (qtyp_qtyp (qua_meet Qtyp P) T0)).
  { apply subqtype_qtyp_qual; [exact Hwf|exact Hwq_payload|exact Hmeet_sub]. }
  apply (typing_step E Qe e (frame_check P :: K) (qtyp_qtyp (qua_meet Qtyp P) T0)).
  - apply typing_sub with (S := qtyp_qtyp Qtyp T0); [exact He|exact Hsq].
  - eapply typing_ctx_check with (R := P) (P := Qtyp) (T := T0).
    + exact HwqP.
    + apply (typing_ctx_to_qsubL E (qtyp_qtyp Qtyp T0) T).
      * apply qsubR_to_qsubL. exact Hqs.
      * apply (typing_ctx_to_qualL E Qe Q).
        -- apply qualR_to_qualL. exact Hq.
        -- exact Hctx.
Qed.


Lemma subst_ee_open_self : forall (v e : exp) (x : atom) (k : nat),
  x `notin` fv_ee e ->
  subst_ee x v (open_ee_rec k (exp_fvar x) e) = open_ee_rec k v e.
Proof.
  intros v e. induction e; intros x0 k0 Hfresh; simpl in *.
  - (* bvar *) destruct (k0 == n); simpl; try rewrite eq_dec_refl; reflexivity.
  - (* fvar *) destruct (x0 == a) as [Heq|Hne]; [subst; fsetdec|reflexivity].
  - (* abs *) f_equal. apply IHe; fsetdec.
  - (* app *) f_equal; [apply IHe1|apply IHe2]; fsetdec.
  - (* tabs *) f_equal. apply IHe; fsetdec.
  - (* tapp *) f_equal. apply IHe; fsetdec.
  - (* qabs *) f_equal. apply IHe; fsetdec.
  - (* qapp *) f_equal. apply IHe; fsetdec.
  - (* let *) f_equal; [apply IHe1|apply IHe2]; fsetdec.
  - (* inl *) f_equal. apply IHe; fsetdec.
  - (* inr *) f_equal. apply IHe; fsetdec.
  - (* case *) f_equal; [apply IHe1|apply IHe2|apply IHe3]; fsetdec.
  - (* pair *) f_equal; [apply IHe1|apply IHe2]; fsetdec.
  - (* first *) f_equal. apply IHe; fsetdec.
  - (* second *) f_equal. apply IHe; fsetdec.
  - (* ref *) f_equal. apply IHe; fsetdec.
  - (* ref_label *) reflexivity.
  - (* deref *) f_equal. apply IHe; fsetdec.
  - (* set_ref *) f_equal; [apply IHe1|apply IHe2]; fsetdec.
  - (* upqual *) f_equal. apply IHe; fsetdec.
  - (* check *) f_equal. apply IHe; fsetdec.
Qed.

Lemma preserve_let_value : forall E Q v e2 K T,
  value v ->
  typing E Q v T ->
  typing_ctx E Q (frame_let e2 :: K) T ->
  typing_state E〈 open_ee e2 v | K 〉.
Proof.
  intros E Q v e2 K T Hval Hty Hctx.
  destruct (typing_ctx_let_inv E Q (frame_let e2 :: K) T Hctx e2 K eq_refl)
    as [Q0 [T1 [T2 [L [Hk [Hbody [HqL HqsL]]]]]]].
  assert (Hwf : wf_env E) by (eapply typing_ctx_wf_env; eassumption).
  assert (Hv1 : typing E Q0 v T1).
  { apply (typing_forward_qualL E Q Q0); [exact HqL|].
    apply (typing_forward_qsubL E T T1); [exact HqsL|exact Hty]. }
  assert (Hvbot : typing E qua_bot v T1).
  { apply (value_typing_bot E Q0 v T1); assumption. }
  destruct (atom_fresh (union L (fv_ee e2))) as [x Hx].
  assert (HxL : x `notin` L) by fsetdec.
  assert (Hxf : x `notin` fv_ee e2) by fsetdec.
  assert (Hb : typing (x ~ bind_typ T1 ++ E) Q0 (open_ee e2 x) T2).
  { apply Hbody; exact HxL. }
  assert (Hwfbody : wf_env (x ~ bind_typ T1 ++ E)).
  { eapply typing_wf_env; eassumption. }
  assert (Hs : typing E Q0 (subst_ee x v (open_ee e2 x)) T2).
  { apply (typing_subst_ee_gen (x ~ bind_typ T1 ++ E) Q0 (open_ee e2 x) T2 Hb x v T1 nil E Hwfbody eq_refl Hvbot). }
  assert (Heqopen : subst_ee x v (open_ee e2 x) = open_ee e2 v).
  { apply (subst_ee_open_self v e2 x 0). exact Hxf. }
  rewrite Heqopen in Hs.
  apply (typing_step E Q0 (open_ee e2 v) K T2).
  - exact Hs.
  - exact Hk.
Qed.

Lemma preserve_first_pair_h : forall E Q P v1 v2 K T,
  value v1 -> value v2 -> typing E Q (exp_pair P v1 v2) T ->
  typing_ctx E Q (frame_first :: K) T -> typing_state E〈 v1 | K 〉.
Proof.
  intros E Q P v1 v2 K T Hval1 Hval2 Hty Hctx.
  destruct (typing_pair_inv_syn E Q P v1 v2 T Hty)
    as [Qe [T1e [T2e [He1 [He2 [HwfP [Hq Hqs]]]]]]].
  destruct (typing_ctx_first_inv E Q (frame_first :: K) T Hctx K eq_refl)
    as [Qc [Pc [T1c [T2c [HwfPc [Hk [HwfT2c [HqL HqsL]]]]]]]].
  assert (Hwf : wf_env E) by (eapply typing_wf_env; eassumption).
  assert (Hint : typing E Qe (exp_pair P v1 v2) (qtyp_qtyp P (typ_pair T1e T2e))).
  { eapply typing_pair; eassumption. }
  assert (Hwqint : wf_qtyp E (qtyp_qtyp P (typ_pair T1e T2e))).
  { apply (typing_wf_qtyp E Qe (exp_pair P v1 v2) (qtyp_qtyp P (typ_pair T1e T2e))); assumption. }
  assert (HctxInt : typing_ctx E Qc (frame_first :: K) (qtyp_qtyp Pc (typ_pair T1c T2c))).
  { eapply typing_ctx_first; eassumption. }
  assert (Hwqctx : wf_qtyp E (qtyp_qtyp Pc (typ_pair T1c T2c))).
  { apply (typing_ctx_wf_qtyp E Qc (frame_first :: K) (qtyp_qtyp Pc (typ_pair T1c T2c)) HctxInt Hwf). }
  assert (Hcomp : qsubL E (qtyp_qtyp P (typ_pair T1e T2e))
                          (qtyp_qtyp Pc (typ_pair T1c T2c))).
  { eapply qsubR_comp_qsubL; eassumption. }
  destruct (qsubL_pair_components_wf E P T1e T2e Pc T1c T2c Hwf Hwqint Hwqctx Hcomp)
    as [Hsub1 Hsub2].
  assert (Hv1c : typing E Qc v1 T1c).
  { apply typing_sub with (S := T1e); [|exact Hsub1].
    apply (typing_forward_qualL E Qe Qc).
    - eapply qualR_comp_qualL; eassumption.
    - exact He1. }
  apply (typing_step E Qc v1 K T1c).
  - exact Hv1c.
  - exact Hk.
Qed.

Lemma preserve_second_pair_h : forall E Q P v1 v2 K T,
  value v1 -> value v2 -> typing E Q (exp_pair P v1 v2) T ->
  typing_ctx E Q (frame_second :: K) T -> typing_state E〈 v2 | K 〉.
Proof.
  intros E Q P v1 v2 K T Hval1 Hval2 Hty Hctx.
  destruct (typing_pair_inv_syn E Q P v1 v2 T Hty)
    as [Qe [T1e [T2e [He1 [He2 [HwfP [Hq Hqs]]]]]]].
  destruct (typing_ctx_second_inv E Q (frame_second :: K) T Hctx K eq_refl)
    as [Qc [Pc [T1c [T2c [HwfPc [Hk [HwfT1c [HqL HqsL]]]]]]]].
  assert (Hwf : wf_env E) by (eapply typing_wf_env; eassumption).
  assert (Hint : typing E Qe (exp_pair P v1 v2) (qtyp_qtyp P (typ_pair T1e T2e))).
  { eapply typing_pair; eassumption. }
  assert (Hwqint : wf_qtyp E (qtyp_qtyp P (typ_pair T1e T2e))).
  { apply (typing_wf_qtyp E Qe (exp_pair P v1 v2) (qtyp_qtyp P (typ_pair T1e T2e))); assumption. }
  assert (HctxInt : typing_ctx E Qc (frame_second :: K) (qtyp_qtyp Pc (typ_pair T1c T2c))).
  { eapply typing_ctx_second; eassumption. }
  assert (Hwqctx : wf_qtyp E (qtyp_qtyp Pc (typ_pair T1c T2c))).
  { apply (typing_ctx_wf_qtyp E Qc (frame_second :: K) (qtyp_qtyp Pc (typ_pair T1c T2c)) HctxInt Hwf). }
  assert (Hcomp : qsubL E (qtyp_qtyp P (typ_pair T1e T2e))
                          (qtyp_qtyp Pc (typ_pair T1c T2c))).
  { eapply qsubR_comp_qsubL; eassumption. }
  destruct (qsubL_pair_components_wf E P T1e T2e Pc T1c T2c Hwf Hwqint Hwqctx Hcomp)
    as [Hsub1 Hsub2].
  assert (Hv2c : typing E Qc v2 T2c).
  { apply typing_sub with (S := T2e); [|exact Hsub2].
    apply (typing_forward_qualL E Qe Qc).
    - eapply qualR_comp_qualL; eassumption.
    - exact He2. }
  apply (typing_step E Qc v2 K T2c).
  - exact Hv2c.
  - exact Hk.
Qed.


Lemma preserve_case_inl_h : forall E Q P v e2 e3 K T,
  value v -> typing E Q (exp_inl P v) T ->
  typing_ctx E Q (frame_case e2 e3 :: K) T ->
  typing_state E〈 open_ee e2 v | K 〉.
Proof.
  intros E Q P v e2 e3 K T Hval Hty Hctx.
  destruct (typing_inl_inv_syn E Q P v T Hty)
    as [Qe [T1e [T2e [Hv [HwfP [HwfT2e [Hq Hqs]]]]]]].
  destruct (typing_ctx_case_inv E Q (frame_case e2 e3 :: K) T Hctx e2 e3 K eq_refl)
    as [Qc [Pc [Tbody [T1c [T2c [L [HwfPc [Hk [Hbody2 [Hbody3 [HqL HqsL]]]]]]]]]]].
  assert (Hwf : wf_env E) by (eapply typing_wf_env; eassumption).
  assert (Hint : typing E Qe (exp_inl P v) (qtyp_qtyp P (typ_sum T1e T2e))).
  { eapply typing_inl; eassumption. }
  assert (Hwqint : wf_qtyp E (qtyp_qtyp P (typ_sum T1e T2e))).
  { apply (typing_wf_qtyp E Qe (exp_inl P v) (qtyp_qtyp P (typ_sum T1e T2e))); assumption. }
  assert (HctxInt : typing_ctx E Qc (frame_case e2 e3 :: K) (qtyp_qtyp Pc (typ_sum T1c T2c))).
  { eapply typing_ctx_case with (T := Tbody) (T1 := T1c) (T2 := T2c) (P := Pc) (L := L);
      eassumption. }
  assert (Hwqctx : wf_qtyp E (qtyp_qtyp Pc (typ_sum T1c T2c))).
  { apply (typing_ctx_wf_qtyp E Qc (frame_case e2 e3 :: K) (qtyp_qtyp Pc (typ_sum T1c T2c)) HctxInt Hwf). }
  assert (Hcomp : qsubL E (qtyp_qtyp P (typ_sum T1e T2e))
                          (qtyp_qtyp Pc (typ_sum T1c T2c))).
  { eapply qsubR_comp_qsubL; eassumption. }
  destruct (qsubL_sum_components_wf E P T1e T2e Pc T1c T2c Hwf Hwqint Hwqctx Hcomp)
    as [Hsub1 Hsub2].
  assert (Hvc : typing E Qc v T1c).
  { apply typing_sub with (S := T1e); [|exact Hsub1].
    apply (typing_forward_qualL E Qe Qc).
    - eapply qualR_comp_qualL; eassumption.
    - exact Hv. }
  assert (Hvbot : typing E qua_bot v T1c).
  { apply (value_typing_bot E Qc v T1c); assumption. }
  destruct (atom_fresh (union L (fv_ee e2))) as [x Hx].
  assert (HxL : x `notin` L) by fsetdec.
  assert (Hxf : x `notin` fv_ee e2) by fsetdec.
  assert (Hb : typing (x ~ bind_typ T1c ++ E) Qc (open_ee e2 x) Tbody).
  { apply Hbody2; exact HxL. }
  assert (Hwfbody : wf_env (x ~ bind_typ T1c ++ E)).
  { eapply typing_wf_env; eassumption. }
  assert (Hs : typing E Qc (subst_ee x v (open_ee e2 x)) Tbody).
  { apply (typing_subst_ee_gen (x ~ bind_typ T1c ++ E) Qc (open_ee e2 x) Tbody Hb x v T1c nil E Hwfbody eq_refl Hvbot). }
  assert (Heqopen : subst_ee x v (open_ee e2 x) = open_ee e2 v).
  { apply (subst_ee_open_self v e2 x 0). exact Hxf. }
  rewrite Heqopen in Hs.
  apply (typing_step E Qc (open_ee e2 v) K Tbody).
  - exact Hs.
  - exact Hk.
Qed.

Lemma preserve_case_inr_h : forall E Q P v e2 e3 K T,
  value v -> typing E Q (exp_inr P v) T ->
  typing_ctx E Q (frame_case e2 e3 :: K) T ->
  typing_state E〈 open_ee e3 v | K 〉.
Proof.
  intros E Q P v e2 e3 K T Hval Hty Hctx.
  destruct (typing_inr_inv_syn E Q P v T Hty)
    as [Qe [T1e [T2e [Hv [HwfP [HwfT1e [Hq Hqs]]]]]]].
  destruct (typing_ctx_case_inv E Q (frame_case e2 e3 :: K) T Hctx e2 e3 K eq_refl)
    as [Qc [Pc [Tbody [T1c [T2c [L [HwfPc [Hk [Hbody2 [Hbody3 [HqL HqsL]]]]]]]]]]].
  assert (Hwf : wf_env E) by (eapply typing_wf_env; eassumption).
  assert (Hint : typing E Qe (exp_inr P v) (qtyp_qtyp P (typ_sum T1e T2e))).
  { eapply typing_inr; eassumption. }
  assert (Hwqint : wf_qtyp E (qtyp_qtyp P (typ_sum T1e T2e))).
  { apply (typing_wf_qtyp E Qe (exp_inr P v) (qtyp_qtyp P (typ_sum T1e T2e))); assumption. }
  assert (HctxInt : typing_ctx E Qc (frame_case e2 e3 :: K) (qtyp_qtyp Pc (typ_sum T1c T2c))).
  { eapply typing_ctx_case with (T := Tbody) (T1 := T1c) (T2 := T2c) (P := Pc) (L := L);
      eassumption. }
  assert (Hwqctx : wf_qtyp E (qtyp_qtyp Pc (typ_sum T1c T2c))).
  { apply (typing_ctx_wf_qtyp E Qc (frame_case e2 e3 :: K) (qtyp_qtyp Pc (typ_sum T1c T2c)) HctxInt Hwf). }
  assert (Hcomp : qsubL E (qtyp_qtyp P (typ_sum T1e T2e))
                          (qtyp_qtyp Pc (typ_sum T1c T2c))).
  { eapply qsubR_comp_qsubL; eassumption. }
  destruct (qsubL_sum_components_wf E P T1e T2e Pc T1c T2c Hwf Hwqint Hwqctx Hcomp)
    as [Hsub1 Hsub2].
  assert (Hvc : typing E Qc v T2c).
  { apply typing_sub with (S := T2e); [|exact Hsub2].
    apply (typing_forward_qualL E Qe Qc).
    - eapply qualR_comp_qualL; eassumption.
    - exact Hv. }
  assert (Hvbot : typing E qua_bot v T2c).
  { apply (value_typing_bot E Qc v T2c); assumption. }
  destruct (atom_fresh (union L (fv_ee e3))) as [x Hx].
  assert (HxL : x `notin` L) by fsetdec.
  assert (Hxf : x `notin` fv_ee e3) by fsetdec.
  assert (Hb : typing (x ~ bind_typ T2c ++ E) Qc (open_ee e3 x) Tbody).
  { apply Hbody3; exact HxL. }
  assert (Hwfbody : wf_env (x ~ bind_typ T2c ++ E)).
  { eapply typing_wf_env; eassumption. }
  assert (Hs : typing E Qc (subst_ee x v (open_ee e3 x)) Tbody).
  { apply (typing_subst_ee_gen (x ~ bind_typ T2c ++ E) Qc (open_ee e3 x) Tbody Hb x v T2c nil E Hwfbody eq_refl Hvbot). }
  assert (Heqopen : subst_ee x v (open_ee e3 x) = open_ee e3 v).
  { apply (subst_ee_open_self v e3 x 0). exact Hxf. }
  rewrite Heqopen in Hs.
  apply (typing_step E Qc (open_ee e3 v) K Tbody).
  - exact Hs.
  - exact Hk.
Qed.

Lemma preserve_app_abs_h : forall E Q Qs V body v t K T,
  value v -> concretize Qs = Some t -> barrier_compatible K t ->
  typing E Q v T ->
  typing_ctx E Q (frame_app (exp_abs Qs V body) :: K) T ->
  typing_state E〈 open_ee body v | frame_barrier t :: K 〉.
Proof.
  intros E Q Qs V body v t K T Hval Hconc _ Hty Hctx.
  destruct (typing_ctx_app_inv_syn E Q (exp_abs Qs V body) K T Hctx)
    as [Q0 [T1 [T2 [Hk [Hvalf [Hf [HqL HqsL]]]]]]].
  destruct (typing_abs_inv_syn E Q0 Qs V body (qtyp_qtyp Q0 (typ_arrow T1 T2)) Hf)
    as [L [T1b [Hbody [HqualR HqsR]]]].
  assert (Hwf : wf_env E) by (eapply typing_wf_env; eassumption).
  assert (Hintr : typing E qua_bot (exp_abs Qs V body) (qtyp_qtyp Qs (typ_arrow V T1b))).
  { eapply typing_abs. exact Hbody. }
  assert (Hwqint : wf_qtyp E (qtyp_qtyp Qs (typ_arrow V T1b))).
  { apply (typing_wf_qtyp E qua_bot (exp_abs Qs V body) (qtyp_qtyp Qs (typ_arrow V T1b))); assumption. }
  assert (Hwqtgt : wf_qtyp E (qtyp_qtyp Q0 (typ_arrow T1 T2))).
  { apply (typing_wf_qtyp E Q0 (exp_abs Qs V body) (qtyp_qtyp Q0 (typ_arrow T1 T2)) Hf Hwf). }
  destruct (qsubR_arrow_components_wf E Qs V T1b Q0 T1 T2 Hwf Hwqint Hwqtgt HqsR)
    as [Hdom Hcod].
  (* value typing at V *)
  assert (HvT1 : typing E Q0 v T1).
  { apply (typing_forward_qualL E Q Q0); [exact HqL|].
    apply (typing_forward_qsubL E T T1); [exact HqsL|exact Hty]. }
  assert (HvV : typing E Q0 v V).
  { apply typing_sub with (S := T1); [exact HvT1|exact Hdom]. }
  assert (Hvbot : typing E qua_bot v V).
  { apply (value_typing_bot E Q0 v V); assumption. }
  (* substitute into body *)
  destruct (atom_fresh (union L (fv_ee body))) as [x Hx].
  assert (HxL : x `notin` L) by fsetdec.
  assert (Hxf : x `notin` fv_ee body) by fsetdec.
  assert (Hb : typing (x ~ bind_typ V ++ E) Qs (open_ee body x) T1b).
  { apply Hbody; exact HxL. }
  assert (Hwfbody : wf_env (x ~ bind_typ V ++ E)).
  { eapply typing_wf_env; eassumption. }
  assert (Hs : typing E Qs (subst_ee x v (open_ee body x)) T1b).
  { apply (typing_subst_ee_gen (x ~ bind_typ V ++ E) Qs (open_ee body x) T1b Hb x v V nil E Hwfbody eq_refl Hvbot). }
  assert (Heqopen : subst_ee x v (open_ee body x) = open_ee body v).
  { apply (subst_ee_open_self v body x 0). exact Hxf. }
  rewrite Heqopen in Hs.
  (* wf of Qs and qualifier conversion to abstractize t *)
  destruct (wf_qtyp_qtyp_inv E Qs (typ_arrow V T1b) Hwqint) as [HwqQ _].
  assert (HqualQ : subqual E Qs Q0).
  { apply (qsubR_qtyp_qual E Qs Q0 (typ_arrow V T1b) (typ_arrow T1 T2) Hwf HwqQ HqsR). }
  assert (Hsqabs : subqual E Qs (abstractize t)).
  { apply (subqual_concretize_le subqual_trans_env E Qs t Hwf HwqQ Hconc). }
  assert (Hsabs : typing E (abstractize t) (open_ee body v) T1b).
  { apply (typing_subqual E Qs (abstractize t) (open_ee body v) T1b Hs Hsqabs). }
  (* retype tail K *)
  assert (HqL0 : qualL E Qs Q0).
  { eapply qualL_step; [exact HqualQ|apply qualL_refl]. }
  assert (HkQ : typing_ctx E Qs K T2).
  { apply (typing_ctx_to_qualL E Qs Q0 HqL0 K T2 Hk). }
  assert (Hqsub : qsubL E T1b T2).
  { eapply qsubL_step; [exact Hcod|apply qsubL_refl]. }
  assert (HkQT : typing_ctx E Qs K T1b).
  { apply (typing_ctx_to_qsubL E T1b T2 Hqsub Qs K HkQ). }
  apply (typing_step E (abstractize t) (open_ee body v) (frame_barrier t :: K) T1b).
  - exact Hsabs.
  - eapply typing_ctx_barrier.
    + exact HkQT.
    + exact Hconc.
    + apply cqua_compatible_refl.
Qed.

Lemma preserve_app_tabs_h : forall E Q P V body Varg t K T,
  type Varg -> concretize P = Some t -> barrier_compatible K t ->
  typing E Q (exp_tabs P V body) T ->
  typing_ctx E Q (frame_tabs Varg :: K) T ->
  typing_state E〈 open_te body Varg | frame_barrier t :: K 〉.
Proof.
  intros E Q P V body Varg t K T Htype Hconc _ Hty Hctx.
  destruct (typing_tabs_inv_syn E Q P V body T Hty)
    as [Lx [T1b [Hbody [HqualR HqsR]]]].
  destruct (typing_ctx_tabs_inv_syn E Q Varg K T Hctx)
    as [Q0 [T1c [T2c [Lc [Hk [Hargsub [Hwfcof [HqL HqsL]]]]]]]].
  assert (Hwf : wf_env E) by (eapply typing_wf_env; eassumption).
  assert (HcompL : qsubL E (qtyp_qtyp P (typ_all V T1b)) (qtyp_qtyp Q0 (typ_all T1c T2c))).
  { eapply qsubR_comp_qsubL; eassumption. }
  assert (HwTstate : wf_qtyp E T).
  { eapply typing_wf_qtyp; eassumption. }
  assert (HwTarget : wf_qtyp E (qtyp_qtyp Q0 (typ_all T1c T2c))).
  { eapply qsubL_wf_target; eassumption. }
  assert (HintrTabs : typing E qua_bot (exp_tabs P V body) (qtyp_qtyp P (typ_all V T1b))).
  { eapply typing_tabs. exact Hbody. }
  assert (HwSource : wf_qtyp E (qtyp_qtyp P (typ_all V T1b))).
  { eapply typing_wf_qtyp; eassumption. }
  destruct (qsubL_all_components E P V T1b Q0 T1c T2c Hwf HwSource HwTarget HcompL)
    as [Hpq [Hdom [Lb Hbod]]].
  assert (HargV : sub E Varg V).
  { eapply sub_trans_env; [exact Hwf|exact Hargsub|exact Hdom]. }
  assert (HwfVarg : wf_typ E Varg).
  { exact (proj1 (sub_wf E Varg T1c Hwf Hargsub)). }
  destruct (atom_fresh (union Lx (union Lb (union (fv_ee body) (union (fv_tqt T1b) (union (fv_tqt T2c) (dom E))))))) as [X HX].
  assert (HXLx : X `notin` Lx) by fsetdec.
  assert (HXLb : X `notin` Lb) by fsetdec.
  assert (HXbody : X `notin` fv_ee body) by fsetdec.
  assert (HXT1 : X `notin` fv_tqt T1b) by fsetdec.
  assert (HXT2 : X `notin` fv_tqt T2c) by fsetdec.
  assert (HXDom : X `notin` dom E) by fsetdec.
  assert (Hb : typing (X ~ bind_sub V ++ E) P (open_te body X) (open_tqt T1b X)).
  { apply Hbody; exact HXLx. }
  assert (Hts : typing E P (subst_te X Varg (open_te body X)) (subst_tqt X Varg (open_tqt T1b X))).
  { eapply typing_subst_te_remove; [exact Hb|exact Hwf|exact HwfVarg|exact HargV]. }
  rewrite (subst_te_open_te_self X Varg body HXbody) in Hts.
  rewrite (subst_tqt_open_tqt_self X Varg T1b HXT1) in Hts.
  assert (Hbc : subqtype (X ~ bind_sub T1c ++ E) (open_tqt T1b X) (open_tqt T2c X)).
  { apply Hbod; exact HXLb. }
  assert (Hsubc : subqtype E (subst_tqt X Varg (open_tqt T1b X)) (subst_tqt X Varg (open_tqt T2c X))).
  { eapply subqtype_subst_te_remove; [exact Hbc|exact Hwf|exact HXDom|exact HwfVarg|exact Hargsub]. }
  rewrite (subst_tqt_open_tqt_self X Varg T1b HXT1) in Hsubc.
  rewrite (subst_tqt_open_tqt_self X Varg T2c HXT2) in Hsubc.
  assert (Hts2 : typing E P (open_te body Varg) (open_tqt T2c Varg)).
  { apply typing_sub with (S := open_tqt T1b Varg); [exact Hts|exact Hsubc]. }
  assert (HwfP : wf_qua E P).
  { exact (proj1 (subqual_wf E P Q0 Hwf Hpq)). }
  assert (HsqP : subqual E P (abstractize t)).
  { apply (subqual_concretize_le subqual_trans_env E P t Hwf HwfP Hconc). }
  assert (Htsabs : typing E (abstractize t) (open_te body Varg) (open_tqt T2c Varg)).
  { apply (typing_subqual E P (abstractize t) (open_te body Varg) (open_tqt T2c Varg) Hts2 HsqP). }
  assert (HqP0 : qualL E P Q0).
  { eapply qualL_step; [exact Hpq|apply qualL_refl]. }
  assert (HkP : typing_ctx E P K (open_tqt T2c Varg)).
  { apply (typing_ctx_to_qualL E P Q0 HqP0 K (open_tqt T2c Varg) Hk). }
  apply (typing_step E (abstractize t) (open_te body Varg) (frame_barrier t :: K) (open_tqt T2c Varg)).
  - exact Htsabs.
  - eapply typing_ctx_barrier.
    + exact HkP.
    + exact Hconc.
    + apply cqua_compatible_refl.
Qed.

Lemma preserve_app_qabs_h : forall E Q P R body Rarg t K T,
  qual Rarg -> concretize P = Some t -> barrier_compatible K t ->
  typing E Q (exp_qabs P R body) T ->
  typing_ctx E Q (frame_qabs Rarg :: K) T ->
  typing_state E〈 open_qe body Rarg | frame_barrier t :: K 〉.
Proof.
  intros E Q P R body Rarg t K T HqualRarg Hconc _ Hty Hctx.
  destruct (typing_qabs_inv_syn E Q P R body T Hty)
    as [Lx [T1b [HwfPbody [Hbody [HqualR HqsR]]]]].
  destruct (typing_ctx_qabs_inv_syn E Q Rarg K T Hctx)
    as [Q0 [R0 [T2c [Lc [Hk [Hargsub [Hwfcof [HqL HqsL]]]]]]]].
  assert (Hwf : wf_env E) by (eapply typing_wf_env; eassumption).
  assert (HcompL : qsubL E (qtyp_qtyp P (typ_qall R T1b)) (qtyp_qtyp Q0 (typ_qall R0 T2c))).
  { eapply qsubR_comp_qsubL; eassumption. }
  assert (HwTstate : wf_qtyp E T).
  { eapply typing_wf_qtyp; eassumption. }
  assert (HwTarget : wf_qtyp E (qtyp_qtyp Q0 (typ_qall R0 T2c))).
  { eapply qsubL_wf_target; eassumption. }
  assert (HintrQabs : typing E qua_bot (exp_qabs P R body) (qtyp_qtyp P (typ_qall R T1b))).
  { eapply typing_qabs; [exact HwfPbody|exact Hbody]. }
  assert (HwSource : wf_qtyp E (qtyp_qtyp P (typ_qall R T1b))).
  { eapply typing_wf_qtyp; eassumption. }
  destruct (qsubL_qall_components E P R T1b Q0 R0 T2c Hwf HwSource HwTarget HcompL)
    as [Hpq [Hdom [Lb Hbod]]].
  assert (HargR : subqual E Rarg R).
  { eapply subqual_trans_env; eassumption. }
  assert (HwfRarg : wf_qua E Rarg).
  { exact (proj1 (subqual_wf E Rarg R0 Hwf Hargsub)). }
  destruct (atom_fresh (union Lx (union Lb (union (fv_ee body) (union (fv_tqt T1b) (union (fv_tqt T2c) (dom E))))))) as [X HX].
  assert (HXLx : X `notin` Lx) by fsetdec.
  assert (HXLb : X `notin` Lb) by fsetdec.
  assert (HXbody : X `notin` fv_ee body) by fsetdec.
  assert (HXT1 : X `notin` fv_tqt T1b) by fsetdec.
  assert (HXT2 : X `notin` fv_tqt T2c) by fsetdec.
  assert (HXDom : X `notin` dom E) by fsetdec.
  assert (Hb : typing (X ~ bind_qua R ++ E) P (open_qe body X) (open_qqt T1b X)).
  { apply Hbody; exact HXLx. }
  assert (Hts : typing E P (subst_qe X Rarg (open_qe body X)) (subst_qqt X Rarg (open_qqt T1b X))).
  { assert (HXQ : X `notin` fv_qq P).
    { intro Hc. apply HXDom. exact (wf_qua_fv_dom E P HwfPbody X Hc). }
    eapply typing_subst_qe_remove; [exact Hb|exact Hwf|exact HwfRarg|exact HargR|exact HXQ]. }
  rewrite (subst_qe_open_qe_self X Rarg body HXbody) in Hts.
  rewrite (subst_qqt_open_qqt_self X Rarg T1b HXT1) in Hts.
  assert (Hbc : subqtype (X ~ bind_qua R0 ++ E) (open_qqt T1b X) (open_qqt T2c X)).
  { apply Hbod; exact HXLb. }
  assert (Hsubc : subqtype E (subst_qqt X Rarg (open_qqt T1b X)) (subst_qqt X Rarg (open_qqt T2c X))).
  { eapply subqtype_subst_qe_remove; [exact Hbc|exact Hwf|exact HXDom|exact HwfRarg|exact Hargsub]. }
  rewrite (subst_qqt_open_qqt_self X Rarg T1b HXT1) in Hsubc.
  rewrite (subst_qqt_open_qqt_self X Rarg T2c HXT2) in Hsubc.
  assert (Hts2 : typing E P (open_qe body Rarg) (open_qqt T2c Rarg)).
  { apply typing_sub with (S := open_qqt T1b Rarg); [exact Hts|exact Hsubc]. }
  assert (HwfP : wf_qua E P).
  { exact (proj1 (subqual_wf E P Q0 Hwf Hpq)). }
  assert (HsqP : subqual E P (abstractize t)).
  { apply (subqual_concretize_le subqual_trans_env E P t Hwf HwfP Hconc). }
  assert (Htsabs : typing E (abstractize t) (open_qe body Rarg) (open_qqt T2c Rarg)).
  { apply (typing_subqual E P (abstractize t) (open_qe body Rarg) (open_qqt T2c Rarg) Hts2 HsqP). }
  assert (HqP0 : qualL E P Q0).
  { eapply qualL_step; [exact Hpq|apply qualL_refl]. }
  assert (HkP : typing_ctx E P K (open_qqt T2c Rarg)).
  { apply (typing_ctx_to_qualL E P Q0 HqP0 K (open_qqt T2c Rarg) Hk). }
  apply (typing_step E (abstractize t) (open_qe body Rarg) (frame_barrier t :: K) (open_qqt T2c Rarg)).
  - exact Htsabs.
  - eapply typing_ctx_barrier.
    + exact HkP.
    + exact Hconc.
    + apply cqua_compatible_refl.
Qed.

Lemma preserve_tapp : forall E Q e1 V K T,
  typing E Q (exp_tapp e1 V) T -> typing_ctx E Q K T ->
  typing_state E〈 e1 | frame_tabs V :: K 〉.
Proof.
  intros E Q e1 V K T Hty Hctx.
  destruct (typing_tapp_inv E Q (exp_tapp e1 V) T Hty e1 V eq_refl)
    as [Q0 [T1 [T2 [He1 [Hsub [Hq Hqs]]]]]].
  assert (Hwf : wf_env E) by (eapply typing_wf_env; eassumption).
  assert (Hwfq : wf_qtyp E (qtyp_qtyp Q0 (typ_all T1 T2))).
  { apply (typing_wf_qtyp E Q0 e1 (qtyp_qtyp Q0 (typ_all T1 T2))); assumption. }
  destruct (wf_qtyp_qtyp_inv E Q0 (typ_all T1 T2) Hwfq) as [Hwq Hwt].
  destruct (wf_typ_all_inv E T1 T2 Hwt) as [HwT1 [Lall Hbodywf]].
  apply (typing_step E Q0 e1 (frame_tabs V :: K) (qtyp_qtyp Q0 (typ_all T1 T2))).
  - exact He1.
  - eapply typing_ctx_tabs with (T1 := T1) (T1' := V) (T2 := T2) (L := union Lall (dom E)).
    + apply (typing_ctx_to_qsubL E (open_tqt T2 V) T).
      * apply qsubR_to_qsubL. exact Hqs.
      * apply (typing_ctx_to_qualL E Q0 Q).
        -- apply qualR_to_qualL. exact Hq.
        -- exact Hctx.
    + exact Hsub.
    + intros X Hx. apply Hbodywf. fsetdec.
Qed.

Lemma preserve_qapp : forall E Q e1 R K T,
  typing E Q (exp_qapp e1 R) T -> typing_ctx E Q K T ->
  typing_state E〈 e1 | frame_qabs R :: K 〉.
Proof.
  intros E Q e1 R K T Hty Hctx.
  destruct (typing_qapp_inv_syn E Q (exp_qapp e1 R) T R e1 Hty eq_refl)
    as [Q1 [T0 [He1 [Hsub [Hq Hqs]]]]].
  assert (Hwf : wf_env E) by (eapply typing_wf_env; eassumption).
  assert (Hwfq : wf_qtyp E (qtyp_qtyp R (typ_qall Q1 T0))).
  { apply (typing_wf_qtyp E R e1 (qtyp_qtyp R (typ_qall Q1 T0))); assumption. }
  destruct (wf_qtyp_qtyp_inv E R (typ_qall Q1 T0) Hwfq) as [Hwq Hwt].
  destruct (wf_typ_qall_inv E Q1 T0 Hwt) as [HwQ1 [Lall Hbodywf]].
  apply (typing_step E R e1 (frame_qabs R :: K) (qtyp_qtyp R (typ_qall Q1 T0))).
  - exact He1.
  - eapply typing_ctx_qabs with (R := Q1) (R' := R) (T2 := T0) (L := union Lall (dom E)).
    + apply (typing_ctx_to_qsubL E (open_qqt T0 R) T).
      * apply qsubR_to_qsubL. exact Hqs.
      * apply (typing_ctx_to_qualL E R Q).
        -- apply qualR_to_qualL. exact Hq.
        -- exact Hctx.
    + exact Hsub.
    + intros X Hx. apply Hbodywf. fsetdec.
Qed.

Lemma preserve_let : forall E Q e1 e2 K T,
  typing E Q (exp_let e1 e2) T -> typing_ctx E Q K T ->
  typing_state E〈 e1 | frame_let e2 :: K 〉.
Proof.
  intros E Q e1 e2 K T Hty Hctx.
  destruct (typing_let_inv E Q (exp_let e1 e2) T Hty e1 e2 eq_refl)
    as [Q0 [T1 [T2 [He1 [[L Hbody] [Hq Hqs]]]]]].
  apply (typing_step E Q0 e1 (frame_let e2 :: K) T1).
  - exact He1.
  - eapply typing_ctx_let with (T1 := T1) (T2 := T2) (L := L).
    + apply (typing_ctx_to_qsubL E T2 T).
      * apply qsubR_to_qsubL. exact Hqs.
      * apply (typing_ctx_to_qualL E Q0 Q).
        -- apply qualR_to_qualL. exact Hq.
        -- exact Hctx.
    + exact Hbody.
Qed.

Lemma preserve_inl : forall E Q P e1 K T,
  typing E Q (exp_inl P e1) T -> typing_ctx E Q K T ->
  typing_state E〈 e1 | frame_inl P :: K 〉.
Proof.
  intros E Q P e1 K T Hty Hctx.
  destruct (typing_inl_inv_syn E Q P e1 T Hty)
    as [Q0 [T1 [T2 [He1 [HwfP [HwfT2 [Hq Hqs]]]]]]].
  apply (typing_step E Q0 e1 (frame_inl P :: K) T1).
  - exact He1.
  - eapply typing_ctx_inl with (T1 := T1) (T2 := T2).
    apply (typing_ctx_to_qsubL E (qtyp_qtyp P (typ_sum T1 T2)) T).
    + apply qsubR_to_qsubL. exact Hqs.
    + apply (typing_ctx_to_qualL E Q0 Q).
      * apply qualR_to_qualL. exact Hq.
      * exact Hctx.
Qed.

Lemma preserve_inr : forall E Q P e1 K T,
  typing E Q (exp_inr P e1) T -> typing_ctx E Q K T ->
  typing_state E〈 e1 | frame_inr P :: K 〉.
Proof.
  intros E Q P e1 K T Hty Hctx.
  destruct (typing_inr_inv_syn E Q P e1 T Hty)
    as [Q0 [T1 [T2 [He1 [HwfP [HwfT1 [Hq Hqs]]]]]]].
  apply (typing_step E Q0 e1 (frame_inr P :: K) T2).
  - exact He1.
  - eapply typing_ctx_inr with (T1 := T1) (T2 := T2).
    apply (typing_ctx_to_qsubL E (qtyp_qtyp P (typ_sum T1 T2)) T).
    + apply qsubR_to_qsubL. exact Hqs.
    + apply (typing_ctx_to_qualL E Q0 Q).
      * apply qualR_to_qualL. exact Hq.
      * exact Hctx.
Qed.

Lemma preserve_case : forall E Q e1 e2 e3 K T,
  typing E Q (exp_case e1 e2 e3) T -> typing_ctx E Q K T ->
  typing_state E〈 e1 | frame_case e2 e3 :: K 〉.
Proof.
  intros E Q e1 e2 e3 K T Hty Hctx.
  destruct (typing_case_inv E Q (exp_case e1 e2 e3) T Hty e1 e2 e3 eq_refl)
    as [Q0 [P [T1 [T2 [Tbody [He1 [[L2 Hb2] [[L3 Hb3] [Hq Hqs]]]]]]]]].
  assert (Hwf : wf_env E) by (eapply typing_wf_env; eassumption).
  assert (Hwfq : wf_qtyp E (qtyp_qtyp P (typ_sum T1 T2))).
  { apply (typing_wf_qtyp E Q0 e1 (qtyp_qtyp P (typ_sum T1 T2))); assumption. }
  destruct (wf_qtyp_qtyp_inv E P (typ_sum T1 T2) Hwfq) as [HwfP Hwt].
  apply (typing_step E Q0 e1 (frame_case e2 e3 :: K) (qtyp_qtyp P (typ_sum T1 T2))).
  - exact He1.
  - eapply typing_ctx_case with (T := Tbody) (T1 := T1) (T2 := T2) (L := union L2 L3) (P := P).
    + exact HwfP.
    + apply (typing_ctx_to_qsubL E Tbody T).
      * apply qsubR_to_qsubL. exact Hqs.
      * apply (typing_ctx_to_qualL E Q0 Q).
        -- apply qualR_to_qualL. exact Hq.
        -- exact Hctx.
    + intros x Hx. apply Hb2. fsetdec.
    + intros x Hx. apply Hb3. fsetdec.
Qed.

Lemma preserve_pair_1 : forall E Q P e1 e2 K T,
  typing E Q (exp_pair P e1 e2) T -> typing_ctx E Q K T ->
  typing_state E〈 e1 | frame_pair_1 P e2 :: K 〉.
Proof.
  intros E Q P e1 e2 K T Hty Hctx.
  destruct (typing_pair_inv_syn E Q P e1 e2 T Hty)
    as [Q0 [T1 [T2 [He1 [He2 [HwfP [Hq Hqs]]]]]]].
  apply (typing_step E Q0 e1 (frame_pair_1 P e2 :: K) T1).
  - exact He1.
  - eapply typing_ctx_pair_1 with (P := P) (T1 := T1) (T2 := T2).
    + exact HwfP.
    + apply (typing_ctx_to_qsubL E (qtyp_qtyp P (typ_pair T1 T2)) T).
      * apply qsubR_to_qsubL. exact Hqs.
      * apply (typing_ctx_to_qualL E Q0 Q).
        -- apply qualR_to_qualL. exact Hq.
        -- exact Hctx.
    + exact He2.
Qed.

Lemma preserve_first : forall E Q e1 K T,
  typing E Q (exp_first e1) T -> typing_ctx E Q K T ->
  typing_state E〈 e1 | frame_first :: K 〉.
Proof.
  intros E Q e1 K T Hty Hctx.
  destruct (typing_first_inv E Q (exp_first e1) T Hty e1 eq_refl)
    as [Q0 [P [T1 [T2 [He1 [Hq Hqs]]]]]].
  assert (Hwf : wf_env E) by (eapply typing_wf_env; eassumption).
  assert (Hwfq : wf_qtyp E (qtyp_qtyp P (typ_pair T1 T2))).
  { apply (typing_wf_qtyp E Q0 e1 (qtyp_qtyp P (typ_pair T1 T2))); assumption. }
  destruct (wf_qtyp_qtyp_inv E P (typ_pair T1 T2) Hwfq) as [HwfP Hwt].
  destruct (wf_typ_pair_inv E T1 T2 Hwt) as [HwfT1 HwfT2].
  apply (typing_step E Q0 e1 (frame_first :: K) (qtyp_qtyp P (typ_pair T1 T2))).
  - exact He1.
  - eapply typing_ctx_first with (P := P) (T1 := T1) (T2 := T2).
    + exact HwfP.
    + apply (typing_ctx_to_qsubL E T1 T).
      * apply qsubR_to_qsubL. exact Hqs.
      * apply (typing_ctx_to_qualL E Q0 Q).
        -- apply qualR_to_qualL. exact Hq.
        -- exact Hctx.
    + exact HwfT2.
Qed.

Lemma preserve_second : forall E Q e1 K T,
  typing E Q (exp_second e1) T -> typing_ctx E Q K T ->
  typing_state E〈 e1 | frame_second :: K 〉.
Proof.
  intros E Q e1 K T Hty Hctx.
  destruct (typing_second_inv E Q (exp_second e1) T Hty e1 eq_refl)
    as [Q0 [P [T1 [T2 [He1 [Hq Hqs]]]]]].
  assert (Hwf : wf_env E) by (eapply typing_wf_env; eassumption).
  assert (Hwfq : wf_qtyp E (qtyp_qtyp P (typ_pair T1 T2))).
  { apply (typing_wf_qtyp E Q0 e1 (qtyp_qtyp P (typ_pair T1 T2))); assumption. }
  destruct (wf_qtyp_qtyp_inv E P (typ_pair T1 T2) Hwfq) as [HwfP Hwt].
  destruct (wf_typ_pair_inv E T1 T2 Hwt) as [HwfT1 HwfT2].
  apply (typing_step E Q0 e1 (frame_second :: K) (qtyp_qtyp P (typ_pair T1 T2))).
  - exact He1.
  - eapply typing_ctx_second with (P := P) (T1 := T1) (T2 := T2).
    + exact HwfP.
    + apply (typing_ctx_to_qsubL E T2 T).
      * apply qsubR_to_qsubL. exact Hqs.
      * apply (typing_ctx_to_qualL E Q0 Q).
        -- apply qualR_to_qualL. exact Hq.
        -- exact Hctx.
    + exact HwfT1.
Qed.


Lemma value_inl_typed : forall E Q P v T,
  typing E Q (exp_inl P v) T -> value v -> value (exp_inl P v).
Proof.
  intros E Q P v T Hty Hv.
  destruct (typing_inl_inv_syn E Q P v T Hty)
    as [Q0 [T1 [T2 [He [HwfP _]]]]].
  apply value_inl; [apply (wf_qua_qual E P); exact HwfP|exact Hv].
Qed.
Lemma value_inr_typed : forall E Q P v T,
  typing E Q (exp_inr P v) T -> value v -> value (exp_inr P v).
Proof.
  intros E Q P v T Hty Hv.
  destruct (typing_inr_inv_syn E Q P v T Hty)
    as [Q0 [T1 [T2 [He [HwfP _]]]]].
  apply value_inr; [apply (wf_qua_qual E P); exact HwfP|exact Hv].
Qed.
Lemma value_pair_typed : forall E Q P v1 v2 T,
  typing E Q (exp_pair P v1 v2) T -> value v1 -> value v2 ->
  value (exp_pair P v1 v2).
Proof.
  intros E Q P v1 v2 T Hty Hv1 Hv2.
  destruct (typing_pair_inv_syn E Q P v1 v2 T Hty)
    as [Q0 [T1 [T2 [He1 [He2 [HwfP _]]]]]].
  apply value_pair; [apply (wf_qua_qual E P); exact HwfP|exact Hv1|exact Hv2].
Qed.

Lemma upqual_comp_components : forall E Qs P T T0 Shape,
  wf_env E -> wf_qtyp E (qtyp_qtyp Qs Shape) ->
  wf_qtyp E (qtyp_qtyp P T0) ->
  qsubR E (qtyp_qtyp Qs Shape) T ->
  qsubL E T (qtyp_qtyp P T0) ->
  subqual E Qs P /\ sub E Shape T0.
Proof.
  intros E Qs P T T0 Shape Hwf HwS HwT HqsR HqsL.
  assert (Hcomp : qsubL E (qtyp_qtyp Qs Shape) (qtyp_qtyp P T0)).
  { eapply qsubR_comp_qsubL; eassumption. }
  pose proof (qsubL_to_subqtype_wf E _ _ Hwf HwS HwT Hcomp) as Hst.
  exact (subqtype_typ_components E Qs Shape P T0 Hst).
Qed.

Lemma qtyp_sub_same_qual : forall E P S T,
  wf_env E -> wf_qua E P -> sub E S T ->
  subqtype E (qtyp_qtyp P S) (qtyp_qtyp P T).
Proof.
  intros. apply sub_qtyp_qtyp; [apply subqual_refl; assumption|exact H1].
Qed.

Lemma preserve_upqual_abs_h : forall E Qst Qs P V body cP cQ K T,
  concretize P = Some cP -> concretize Qs = Some cQ -> cQ ≤ cP ->
  typing E Qst (exp_abs Qs V body) T ->
  typing_ctx E Qst (frame_upqual P :: K) T ->
  typing_state E〈 exp_abs P V body | K 〉.
Proof.
  intros E Qst Qs P V body cP cQ K T HcP HcQ Hle Hty Hctx.
  destruct (typing_abs_inv_syn E Qst Qs V body T Hty)
    as [L [T1 [Hbody [HqualR HqsR]]]].
  destruct (typing_ctx_upqual_inv_syn E Qst P K T Hctx)
    as [Q0 [T0 [Hk [HqL HqsL]]]].
  assert (Hwf : wf_env E) by (eapply typing_wf_env; eassumption).
  assert (HwTstate : wf_qtyp E T).
  { eapply typing_wf_qtyp; eassumption. }
  assert (HwTarget : wf_qtyp E (qtyp_qtyp P T0)).
  { eapply qsubL_wf_target; eassumption. }
  assert (Hintr : typing E qua_bot (exp_abs Qs V body) (qtyp_qtyp Qs (typ_arrow V T1))).
  { eapply typing_abs. exact Hbody. }
  assert (HwSource : wf_qtyp E (qtyp_qtyp Qs (typ_arrow V T1))).
  { eapply typing_wf_qtyp; eassumption. }
  destruct (upqual_comp_components E Qs P T T0 (typ_arrow V T1) Hwf HwSource HwTarget HqsR HqsL)
    as [HqualQP Hdom].
  assert (HwfP : wf_qua E P).
  { exact (proj2 (subqual_wf E Qs P Hwf HqualQP)). }
  assert (HbodyP : forall x, x `notin` L -> typing (x ~ bind_typ V ++ E) P (open_ee body x) T1).
  { intros x Hx.
    eapply typing_subqual.
    - apply Hbody; exact Hx.
    - eapply subqual_weaken; [exact HqualQP| | apply env_extends_cons_tail].
      eapply typing_wf_env; apply Hbody; exact Hx. }
  assert (Hexpr : typing E qua_bot (exp_abs P V body) (qtyp_qtyp P (typ_arrow V T1))).
  { eapply typing_abs. exact HbodyP. }
  assert (HwQ0 : wf_qua E Q0).
  { eapply typing_ctx_wf_qua; eassumption. }
  assert (HkBot : typing_ctx E qua_bot K (qtyp_qtyp P T0)).
  { apply (typing_ctx_subqual E Q0 qua_bot K (qtyp_qtyp P T0) Hk).
    apply subqual_bot; assumption. }
  assert (Hsq : subqtype E (qtyp_qtyp P (typ_arrow V T1)) (qtyp_qtyp P T0)).
  { apply (qtyp_sub_same_qual E P (typ_arrow V T1) T0); assumption. }
  assert (Hqsub : qsubL E (qtyp_qtyp P (typ_arrow V T1)) (qtyp_qtyp P T0)).
  { eapply qsubL_step; [exact Hsq|apply qsubL_refl]. }
  assert (HkFinal : typing_ctx E qua_bot K (qtyp_qtyp P (typ_arrow V T1))).
  { apply (typing_ctx_to_qsubL E (qtyp_qtyp P (typ_arrow V T1)) (qtyp_qtyp P T0) Hqsub qua_bot K HkBot). }
  apply (typing_step E qua_bot (exp_abs P V body) K (qtyp_qtyp P (typ_arrow V T1)) Hexpr HkFinal).
Qed.

Lemma preserve_upqual_tabs_h : forall E Qst Qs P V body cP cQ K T,
  concretize P = Some cP -> concretize Qs = Some cQ -> cQ ≤ cP ->
  typing E Qst (exp_tabs Qs V body) T ->
  typing_ctx E Qst (frame_upqual P :: K) T ->
  typing_state E〈 exp_tabs P V body | K 〉.
Proof.
  intros E Qst Qs P V body cP cQ K T HcP HcQ Hle Hty Hctx.
  destruct (typing_tabs_inv_syn E Qst Qs V body T Hty)
    as [L [T1 [Hbody [HqualR HqsR]]]].
  destruct (typing_ctx_upqual_inv_syn E Qst P K T Hctx)
    as [Q0 [T0 [Hk [HqL HqsL]]]].
  assert (Hwf : wf_env E) by (eapply typing_wf_env; eassumption).
  assert (HwTstate : wf_qtyp E T).
  { eapply typing_wf_qtyp; eassumption. }
  assert (HwTarget : wf_qtyp E (qtyp_qtyp P T0)).
  { eapply qsubL_wf_target; eassumption. }
  assert (Hintr : typing E qua_bot (exp_tabs Qs V body) (qtyp_qtyp Qs (typ_all V T1))).
  { eapply typing_tabs. exact Hbody. }
  assert (HwSource : wf_qtyp E (qtyp_qtyp Qs (typ_all V T1))).
  { eapply typing_wf_qtyp; eassumption. }
  destruct (upqual_comp_components E Qs P T T0 (typ_all V T1) Hwf HwSource HwTarget HqsR HqsL)
    as [HqualQP Hdom].
  assert (HwfP : wf_qua E P).
  { exact (proj2 (subqual_wf E Qs P Hwf HqualQP)). }
  assert (HbodyP : forall X, X `notin` L -> typing (X ~ bind_sub V ++ E) P (open_te body X) (open_tqt T1 X)).
  { intros X Hx.
    eapply typing_subqual.
    - apply Hbody; exact Hx.
    - eapply subqual_weaken; [exact HqualQP| | apply env_extends_cons_tail].
      eapply typing_wf_env; apply Hbody; exact Hx. }
  assert (Hexpr : typing E qua_bot (exp_tabs P V body) (qtyp_qtyp P (typ_all V T1))).
  { eapply typing_tabs. exact HbodyP. }
  assert (HwQ0 : wf_qua E Q0).
  { eapply typing_ctx_wf_qua; eassumption. }
  assert (HkBot : typing_ctx E qua_bot K (qtyp_qtyp P T0)).
  { apply (typing_ctx_subqual E Q0 qua_bot K (qtyp_qtyp P T0) Hk).
    apply subqual_bot; assumption. }
  assert (Hsq : subqtype E (qtyp_qtyp P (typ_all V T1)) (qtyp_qtyp P T0)).
  { apply (qtyp_sub_same_qual E P (typ_all V T1) T0); assumption. }
  assert (Hqsub : qsubL E (qtyp_qtyp P (typ_all V T1)) (qtyp_qtyp P T0)).
  { eapply qsubL_step; [exact Hsq|apply qsubL_refl]. }
  assert (HkFinal : typing_ctx E qua_bot K (qtyp_qtyp P (typ_all V T1))).
  { apply (typing_ctx_to_qsubL E (qtyp_qtyp P (typ_all V T1)) (qtyp_qtyp P T0) Hqsub qua_bot K HkBot). }
  apply (typing_step E qua_bot (exp_tabs P V body) K (qtyp_qtyp P (typ_all V T1)) Hexpr HkFinal).
Qed.

Lemma preserve_upqual_qabs_h : forall E Qst Qs P R body cP cQ K T,
  concretize P = Some cP -> concretize Qs = Some cQ -> cQ ≤ cP ->
  typing E Qst (exp_qabs Qs R body) T ->
  typing_ctx E Qst (frame_upqual P :: K) T ->
  typing_state E〈 exp_qabs P R body | K 〉.
Proof.
  intros E Qst Qs P R body cP cQ K T HcP HcQ Hle Hty Hctx.
  destruct (typing_qabs_inv_syn E Qst Qs R body T Hty)
    as [L [T1 [HwfQs [Hbody [HqualR HqsR]]]]].
  destruct (typing_ctx_upqual_inv_syn E Qst P K T Hctx)
    as [Q0 [T0 [Hk [HqL HqsL]]]].
  assert (Hwf : wf_env E) by (eapply typing_wf_env; eassumption).
  assert (HwTstate : wf_qtyp E T).
  { eapply typing_wf_qtyp; eassumption. }
  assert (HwTarget : wf_qtyp E (qtyp_qtyp P T0)).
  { eapply qsubL_wf_target; eassumption. }
  assert (Hintr : typing E qua_bot (exp_qabs Qs R body) (qtyp_qtyp Qs (typ_qall R T1))).
  { eapply typing_qabs; [exact HwfQs|exact Hbody]. }
  assert (HwSource : wf_qtyp E (qtyp_qtyp Qs (typ_qall R T1))).
  { eapply typing_wf_qtyp; eassumption. }
  destruct (upqual_comp_components E Qs P T T0 (typ_qall R T1) Hwf HwSource HwTarget HqsR HqsL)
    as [HqualQP Hdom].
  assert (HwfP : wf_qua E P).
  { exact (proj2 (subqual_wf E Qs P Hwf HqualQP)). }
  assert (HbodyP : forall X, X `notin` L -> typing (X ~ bind_qua R ++ E) P (open_qe body X) (open_qqt T1 X)).
  { intros X Hx.
    eapply typing_subqual.
    - apply Hbody; exact Hx.
    - eapply subqual_weaken; [exact HqualQP| | apply env_extends_cons_tail].
      eapply typing_wf_env; apply Hbody; exact Hx. }
  assert (Hexpr : typing E qua_bot (exp_qabs P R body) (qtyp_qtyp P (typ_qall R T1))).
  { eapply typing_qabs; [exact HwfP|exact HbodyP]. }
  assert (HwQ0 : wf_qua E Q0).
  { eapply typing_ctx_wf_qua; eassumption. }
  assert (HkBot : typing_ctx E qua_bot K (qtyp_qtyp P T0)).
  { apply (typing_ctx_subqual E Q0 qua_bot K (qtyp_qtyp P T0) Hk).
    apply subqual_bot; assumption. }
  assert (Hsq : subqtype E (qtyp_qtyp P (typ_qall R T1)) (qtyp_qtyp P T0)).
  { apply (qtyp_sub_same_qual E P (typ_qall R T1) T0); assumption. }
  assert (Hqsub : qsubL E (qtyp_qtyp P (typ_qall R T1)) (qtyp_qtyp P T0)).
  { eapply qsubL_step; [exact Hsq|apply qsubL_refl]. }
  assert (HkFinal : typing_ctx E qua_bot K (qtyp_qtyp P (typ_qall R T1))).
  { apply (typing_ctx_to_qsubL E (qtyp_qtyp P (typ_qall R T1)) (qtyp_qtyp P T0) Hqsub qua_bot K HkBot). }
  apply (typing_step E qua_bot (exp_qabs P R body) K (qtyp_qtyp P (typ_qall R T1)) Hexpr HkFinal).
Qed.

Lemma preserve_upqual_inl_h : forall E Qst Qs P v cP cQ K T,
  concretize P = Some cP -> concretize Qs = Some cQ -> cQ ≤ cP ->
  typing E Qst (exp_inl Qs v) T ->
  typing_ctx E Qst (frame_upqual P :: K) T ->
  typing_state E〈 exp_inl P v | K 〉.
Proof.
  intros E Qst Qs P v cP cQ K T HcP HcQ Hle Hty Hctx.
  destruct (typing_inl_inv_syn E Qst Qs v T Hty)
    as [Qe [T1 [T2 [Hv [HwfQs [HwfT2 [HqualR HqsR]]]]]]].
  destruct (typing_ctx_upqual_inv_syn E Qst P K T Hctx)
    as [Q0 [T0 [Hk [HqL HqsL]]]].
  assert (Hwf : wf_env E) by (eapply typing_wf_env; eassumption).
  assert (HwTstate : wf_qtyp E T) by (eapply typing_wf_qtyp; eassumption).
  assert (HwTarget : wf_qtyp E (qtyp_qtyp P T0)) by (eapply qsubL_wf_target; eassumption).
  assert (Hintr : typing E Qe (exp_inl Qs v) (qtyp_qtyp Qs (typ_sum T1 T2))).
  { eapply typing_inl; eassumption. }
  assert (HwSource : wf_qtyp E (qtyp_qtyp Qs (typ_sum T1 T2))).
  { eapply typing_wf_qtyp; eassumption. }
  destruct (upqual_comp_components E Qs P T T0 (typ_sum T1 T2) Hwf HwSource HwTarget HqsR HqsL)
    as [HqualQP Hdom].
  assert (HwfP : wf_qua E P) by (exact (proj2 (subqual_wf E Qs P Hwf HqualQP))).
  assert (Hexpr : typing E Qe (exp_inl P v) (qtyp_qtyp P (typ_sum T1 T2))).
  { eapply typing_inl; eassumption. }
  assert (HqQ : qualL E Qe Q0).
  { eapply qualR_comp_qualL; eassumption. }
  assert (HkQe : typing_ctx E Qe K (qtyp_qtyp P T0)).
  { apply (typing_ctx_to_qualL E Qe Q0 HqQ K (qtyp_qtyp P T0) Hk). }
  assert (Hsq : subqtype E (qtyp_qtyp P (typ_sum T1 T2)) (qtyp_qtyp P T0)).
  { apply (qtyp_sub_same_qual E P (typ_sum T1 T2) T0); assumption. }
  assert (Hqsub : qsubL E (qtyp_qtyp P (typ_sum T1 T2)) (qtyp_qtyp P T0)).
  { eapply qsubL_step; [exact Hsq|apply qsubL_refl]. }
  assert (HkFinal : typing_ctx E Qe K (qtyp_qtyp P (typ_sum T1 T2))).
  { apply (typing_ctx_to_qsubL E (qtyp_qtyp P (typ_sum T1 T2)) (qtyp_qtyp P T0) Hqsub Qe K HkQe). }
  apply (typing_step E Qe (exp_inl P v) K (qtyp_qtyp P (typ_sum T1 T2)) Hexpr HkFinal).
Qed.

Lemma preserve_upqual_inr_h : forall E Qst Qs P v cP cQ K T,
  concretize P = Some cP -> concretize Qs = Some cQ -> cQ ≤ cP ->
  typing E Qst (exp_inr Qs v) T ->
  typing_ctx E Qst (frame_upqual P :: K) T ->
  typing_state E〈 exp_inr P v | K 〉.
Proof.
  intros E Qst Qs P v cP cQ K T HcP HcQ Hle Hty Hctx.
  destruct (typing_inr_inv_syn E Qst Qs v T Hty)
    as [Qe [T1 [T2 [Hv [HwfQs [HwfT1 [HqualR HqsR]]]]]]].
  destruct (typing_ctx_upqual_inv_syn E Qst P K T Hctx)
    as [Q0 [T0 [Hk [HqL HqsL]]]].
  assert (Hwf : wf_env E) by (eapply typing_wf_env; eassumption).
  assert (HwTstate : wf_qtyp E T) by (eapply typing_wf_qtyp; eassumption).
  assert (HwTarget : wf_qtyp E (qtyp_qtyp P T0)) by (eapply qsubL_wf_target; eassumption).
  assert (Hintr : typing E Qe (exp_inr Qs v) (qtyp_qtyp Qs (typ_sum T1 T2))).
  { eapply typing_inr; eassumption. }
  assert (HwSource : wf_qtyp E (qtyp_qtyp Qs (typ_sum T1 T2))).
  { eapply typing_wf_qtyp; eassumption. }
  destruct (upqual_comp_components E Qs P T T0 (typ_sum T1 T2) Hwf HwSource HwTarget HqsR HqsL)
    as [HqualQP Hdom].
  assert (HwfP : wf_qua E P) by (exact (proj2 (subqual_wf E Qs P Hwf HqualQP))).
  assert (Hexpr : typing E Qe (exp_inr P v) (qtyp_qtyp P (typ_sum T1 T2))).
  { eapply typing_inr; eassumption. }
  assert (HqQ : qualL E Qe Q0) by (eapply qualR_comp_qualL; eassumption).
  assert (HkQe : typing_ctx E Qe K (qtyp_qtyp P T0)).
  { apply (typing_ctx_to_qualL E Qe Q0 HqQ K (qtyp_qtyp P T0) Hk). }
  assert (Hsq : subqtype E (qtyp_qtyp P (typ_sum T1 T2)) (qtyp_qtyp P T0)).
  { apply (qtyp_sub_same_qual E P (typ_sum T1 T2) T0); assumption. }
  assert (Hqsub : qsubL E (qtyp_qtyp P (typ_sum T1 T2)) (qtyp_qtyp P T0)).
  { eapply qsubL_step; [exact Hsq|apply qsubL_refl]. }
  assert (HkFinal : typing_ctx E Qe K (qtyp_qtyp P (typ_sum T1 T2))).
  { apply (typing_ctx_to_qsubL E (qtyp_qtyp P (typ_sum T1 T2)) (qtyp_qtyp P T0) Hqsub Qe K HkQe). }
  apply (typing_step E Qe (exp_inr P v) K (qtyp_qtyp P (typ_sum T1 T2)) Hexpr HkFinal).
Qed.

Lemma preserve_upqual_pair_h : forall E Qst Qs P v1 v2 cP cQ K T,
  concretize P = Some cP -> concretize Qs = Some cQ -> cQ ≤ cP ->
  typing E Qst (exp_pair Qs v1 v2) T ->
  typing_ctx E Qst (frame_upqual P :: K) T ->
  typing_state E〈 exp_pair P v1 v2 | K 〉.
Proof.
  intros E Qst Qs P v1 v2 cP cQ K T HcP HcQ Hle Hty Hctx.
  destruct (typing_pair_inv_syn E Qst Qs v1 v2 T Hty)
    as [Qe [T1 [T2 [He1 [He2 [HwfQs [HqualR HqsR]]]]]]].
  destruct (typing_ctx_upqual_inv_syn E Qst P K T Hctx)
    as [Q0 [T0 [Hk [HqL HqsL]]]].
  assert (Hwf : wf_env E) by (eapply typing_wf_env; eassumption).
  assert (HwTstate : wf_qtyp E T) by (eapply typing_wf_qtyp; eassumption).
  assert (HwTarget : wf_qtyp E (qtyp_qtyp P T0)) by (eapply qsubL_wf_target; eassumption).
  assert (Hintr : typing E Qe (exp_pair Qs v1 v2) (qtyp_qtyp Qs (typ_pair T1 T2))).
  { eapply typing_pair; eassumption. }
  assert (HwSource : wf_qtyp E (qtyp_qtyp Qs (typ_pair T1 T2))).
  { eapply typing_wf_qtyp; eassumption. }
  destruct (upqual_comp_components E Qs P T T0 (typ_pair T1 T2) Hwf HwSource HwTarget HqsR HqsL)
    as [HqualQP Hdom].
  assert (HwfP : wf_qua E P) by (exact (proj2 (subqual_wf E Qs P Hwf HqualQP))).
  assert (Hexpr : typing E Qe (exp_pair P v1 v2) (qtyp_qtyp P (typ_pair T1 T2))).
  { eapply typing_pair; eassumption. }
  assert (HqQ : qualL E Qe Q0) by (eapply qualR_comp_qualL; eassumption).
  assert (HkQe : typing_ctx E Qe K (qtyp_qtyp P T0)).
  { apply (typing_ctx_to_qualL E Qe Q0 HqQ K (qtyp_qtyp P T0) Hk). }
  assert (Hsq : subqtype E (qtyp_qtyp P (typ_pair T1 T2)) (qtyp_qtyp P T0)).
  { apply (qtyp_sub_same_qual E P (typ_pair T1 T2) T0); assumption. }
  assert (Hqsub : qsubL E (qtyp_qtyp P (typ_pair T1 T2)) (qtyp_qtyp P T0)).
  { eapply qsubL_step; [exact Hsq|apply qsubL_refl]. }
  assert (HkFinal : typing_ctx E Qe K (qtyp_qtyp P (typ_pair T1 T2))).
  { apply (typing_ctx_to_qsubL E (qtyp_qtyp P (typ_pair T1 T2)) (qtyp_qtyp P T0) Hqsub Qe K HkQe). }
  apply (typing_step E Qe (exp_pair P v1 v2) K (qtyp_qtyp P (typ_pair T1 T2)) Hexpr HkFinal).
Qed.
Lemma preservation_step : forall E s s',
  typing_state E s -> step s s' -> typing_state E s'.
Proof.
  intros E s s' Hts Hstep.
  destruct Hstep.
  all: inversion Hts; subst.
  - (* step_barrier *) eapply (preserve_barrier subqual_trans_env E Q e s k T); eauto.
  - (* step_app_1 *) eapply preserve_app_1; eauto.
  - (* step_app_2 *) eapply preserve_app_2; eauto.
  - (* step_tapp *) eapply preserve_tapp; eauto.
  - (* step_qapp *) eapply preserve_qapp; eauto.
  - (* step_let *) eapply preserve_let; eauto.
  - (* step_inl *) eapply preserve_inl; eauto.
  - (* step_inr *) eapply preserve_inr; eauto.
  - (* step_case *) eapply preserve_case; eauto.
  - (* step_pair_1 *) eapply preserve_pair_1; eauto.
  - (* step_pair_2 *) eapply preserve_pair_2; eauto.
  - (* step_first *) eapply preserve_first; eauto.
  - (* step_second *) eapply preserve_second; eauto.
  - (* step_app_abs *) eapply preserve_app_abs_h; eauto.
  - (* step_app_tabs *) eapply preserve_app_tabs_h; eauto.
  - (* step_app_qabs *) eapply preserve_app_qabs_h; eauto.
  - (* step_let_value *) eapply preserve_let_value; eauto.
  - (* step_case_inl *) eapply preserve_case_inl_h; eauto.
  - (* step_case_inr *) eapply preserve_case_inr_h; eauto.
  - (* step_first_pair *)
    match goal with
    | Hty0 : typing ?E0 ?Q0 (exp_pair ?P0 ?a ?b) ?T0,
      Hctx0 : typing_ctx ?E0 ?Q0 (frame_first :: ?k0) ?T0,
      Hva : value ?a, Hvb : value ?b |- _ =>
      apply (preserve_first_pair_h E0 Q0 P0 a b k0 T0 Hva Hvb Hty0 Hctx0)
    end.
  - (* step_second_pair *)
    match goal with
    | Hty0 : typing ?E0 ?Q0 (exp_pair ?P0 ?a ?b) ?T0,
      Hctx0 : typing_ctx ?E0 ?Q0 (frame_second :: ?k0) ?T0,
      Hva : value ?a, Hvb : value ?b |- _ =>
      apply (preserve_second_pair_h E0 Q0 P0 a b k0 T0 Hva Hvb Hty0 Hctx0)
    end.
  - (* step_make_inl *) eapply preserve_make_inl; eauto.
  - (* step_make_inr *) eapply preserve_make_inr; eauto.
  - (* step_make_pair *) eapply preserve_make_pair; eauto.
  - (* step_upqual_1 *) eapply preserve_upqual_1; eauto.
  - (* step_upqual_abs *) eapply preserve_upqual_abs_h; eauto 20.
  - (* step_upqual_tabs *) eapply preserve_upqual_tabs_h; eauto 20.
  - (* step_upqual_qabs *) eapply preserve_upqual_qabs_h; eauto 20.
  - (* step_upqual_inl *) eapply preserve_upqual_inl_h; eauto 20.
  - (* step_upqual_inr *) eapply preserve_upqual_inr_h; eauto 20.
  - (* step_upqual_pair *) eapply preserve_upqual_pair_h; eauto 20.
  - (* step_check_1 *) eapply preserve_check_1; eauto.
  - (* step_check_abs *) eapply (check_step_generic typing_ctx_wf_qtyp).
    + eauto 10 using typing_expr, value_abs, value_inl_typed, value_inr_typed, value_pair_typed.
    + eassumption. + eassumption.
  - (* step_check_tabs *) eapply (check_step_generic typing_ctx_wf_qtyp).
    + eauto 10 using typing_expr, value_abs, value_tabs, value_inl_typed, value_inr_typed, value_pair_typed.
    + eassumption. + eassumption.
  - (* step_check_qabs *) eapply (check_step_generic typing_ctx_wf_qtyp).
    + eauto 10 using typing_expr, value_abs, value_qabs, value_inl_typed, value_inr_typed, value_pair_typed.
    + eassumption. + eassumption.
  - (* step_check_inl *) eapply (check_step_generic typing_ctx_wf_qtyp).
    + eauto 10 using value_inl_typed.
    + eassumption. + eassumption.
  - (* step_check_inr *) eapply (check_step_generic typing_ctx_wf_qtyp).
    + eauto 10 using value_inr_typed.
    + eassumption. + eassumption.
  - (* step_check_pair *) eapply (check_step_generic typing_ctx_wf_qtyp).
    + eauto 10 using value_pair_typed.
    + eassumption. + eassumption.
Qed.

End Hyp.

Theorem preservation : forall E s s',
  typing_state E s ->
  s --> s' ->
  typing_state E s'.
Proof.
  intros E s s' Hts Hstep.
  exact (preservation_step E s s' Hts Hstep).
Qed.


(* ===== Target theorems ===== *)
Theorem progress : forall s,
  typing_state empty s -> done_state s \/ exists s', s --> s'.
Proof. exact progress_final. Qed.
