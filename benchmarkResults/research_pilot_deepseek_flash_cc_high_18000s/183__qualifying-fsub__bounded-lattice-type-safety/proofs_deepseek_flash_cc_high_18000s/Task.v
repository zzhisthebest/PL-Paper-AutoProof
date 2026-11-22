From Fsub.ExtendedBase Require Import Fsub_LetSum_Definitions.
From Stdlib Require Import Lia.

(* ================================================================== *)
(* Free variables                                                     *)
(* ================================================================== *)

Fixpoint fv_qua (Q : qua) : atoms :=
  match Q with
  | qua_base _ => AtomSetImpl.empty
  | qua_bvar _ => AtomSetImpl.empty
  | qua_fvar X => singleton X
  | qua_meet Q1 Q2 => union (fv_qua Q1) (fv_qua Q2)
  | qua_join Q1 Q2 => union (fv_qua Q1) (fv_qua Q2)
  end.

Fixpoint fv_typ (T : typ) : atoms :=
  match T with
  | typ_top => AtomSetImpl.empty
  | typ_bvar _ => AtomSetImpl.empty
  | typ_fvar X => singleton X
  | typ_arrow T1 T2 => union (fv_qtyp T1) (fv_qtyp T2)
  | typ_all T1 T2 => union (fv_typ T1) (fv_qtyp T2)
  | typ_qall Q T => union (fv_qua Q) (fv_qtyp T)
  | typ_sum T1 T2 => union (fv_qtyp T1) (fv_qtyp T2)
  | typ_pair T1 T2 => union (fv_qtyp T1) (fv_qtyp T2)
  | typ_ref T => fv_qtyp T
  end
with fv_qtyp (T : qtyp) : atoms :=
  match T with
  | qtyp_qtyp Q T => union (fv_qua Q) (fv_typ T)
  end.

Fixpoint fv_exp (e : exp) : atoms :=
  match e with
  | exp_bvar _ => AtomSetImpl.empty
  | exp_fvar x => singleton x
  | exp_abs P V e1 => union (fv_qua P) (union (fv_qtyp V) (fv_exp e1))
  | exp_app e1 e2 => union (fv_exp e1) (fv_exp e2)
  | exp_tabs P V e1 => union (fv_qua P) (union (fv_typ V) (fv_exp e1))
  | exp_tapp e1 V => union (fv_exp e1) (fv_typ V)
  | exp_qabs P Q e1 => union (fv_qua P) (union (fv_qua Q) (fv_exp e1))
  | exp_qapp e1 Q => union (fv_exp e1) (fv_qua Q)
  | exp_let e1 e2 => union (fv_exp e1) (fv_exp e2)
  | exp_inl P e1 => union (fv_qua P) (fv_exp e1)
  | exp_inr P e1 => union (fv_qua P) (fv_exp e1)
  | exp_case e1 e2 e3 => union (fv_exp e1) (union (fv_exp e2) (fv_exp e3))
  | exp_pair P e1 e2 => union (fv_qua P) (union (fv_exp e1) (fv_exp e2))
  | exp_first e1 => fv_exp e1
  | exp_second e1 => fv_exp e1
  | exp_ref P e1 => union (fv_qua P) (fv_exp e1)
  | exp_ref_label P _ => fv_qua P
  | exp_deref e1 => fv_exp e1
  | exp_set_ref e1 e2 => union (fv_exp e1) (fv_exp e2)
  | exp_upqual P e1 => union (fv_qua P) (fv_exp e1)
  | exp_check P e1 => union (fv_qua P) (fv_exp e1)
  end.

(* ================================================================== *)
(* Substitutions                                                      *)
(* ================================================================== *)

Fixpoint subst_qq (X : atom) (R Q : qua) {struct Q} : qua :=
  match Q with
  | qua_base b => qua_base b
  | qua_bvar n => qua_bvar n
  | qua_fvar Y => if X == Y then R else qua_fvar Y
  | qua_meet Q1 Q2 => qua_meet (subst_qq X R Q1) (subst_qq X R Q2)
  | qua_join Q1 Q2 => qua_join (subst_qq X R Q1) (subst_qq X R Q2)
  end.

Fixpoint subst_tt (X : atom) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | typ_top => typ_top
  | typ_bvar n => typ_bvar n
  | typ_fvar Y => if X == Y then U else typ_fvar Y
  | typ_arrow T1 T2 => typ_arrow (subst_tqt X U T1) (subst_tqt X U T2)
  | typ_all T1 T2 => typ_all (subst_tt X U T1) (subst_tqt X U T2)
  | typ_qall Q T1 => typ_qall Q (subst_tqt X U T1)
  | typ_sum T1 T2 => typ_sum (subst_tqt X U T1) (subst_tqt X U T2)
  | typ_pair T1 T2 => typ_pair (subst_tqt X U T1) (subst_tqt X U T2)
  | typ_ref T1 => typ_ref (subst_tqt X U T1)
  end
with subst_tqt (X : atom) (U : typ) (T : qtyp) {struct T} : qtyp :=
  match T with
  | qtyp_qtyp Q T1 => qtyp_qtyp Q (subst_tt X U T1)
  end.

Fixpoint subst_qt (X : atom) (R : qua) (T : typ) {struct T} : typ :=
  match T with
  | typ_top => typ_top
  | typ_bvar n => typ_bvar n
  | typ_fvar Y => typ_fvar Y
  | typ_arrow T1 T2 => typ_arrow (subst_qqt X R T1) (subst_qqt X R T2)
  | typ_all T1 T2 => typ_all (subst_qt X R T1) (subst_qqt X R T2)
  | typ_qall Q T1 => typ_qall (subst_qq X R Q) (subst_qqt X R T1)
  | typ_sum T1 T2 => typ_sum (subst_qqt X R T1) (subst_qqt X R T2)
  | typ_pair T1 T2 => typ_pair (subst_qqt X R T1) (subst_qqt X R T2)
  | typ_ref T1 => typ_ref (subst_qqt X R T1)
  end
with subst_qqt (X : atom) (R : qua) (T : qtyp) {struct T} : qtyp :=
  match T with
  | qtyp_qtyp Q T1 => qtyp_qtyp (subst_qq X R Q) (subst_qt X R T1)
  end.

Fixpoint subst_ee (x : atom) (v e : exp) {struct e} : exp :=
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
  | exp_case e1 e2 e3 =>
      exp_case (subst_ee x v e1) (subst_ee x v e2) (subst_ee x v e3)
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
  | exp_case e1 e2 e3 =>
      exp_case (subst_te X U e1) (subst_te X U e2) (subst_te X U e3)
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
  | exp_abs P V e1 =>
      exp_abs (subst_qq X R P) (subst_qqt X R V) (subst_qe X R e1)
  | exp_app e1 e2 => exp_app (subst_qe X R e1) (subst_qe X R e2)
  | exp_tabs P V e1 =>
      exp_tabs (subst_qq X R P) (subst_qt X R V) (subst_qe X R e1)
  | exp_tapp e1 V => exp_tapp (subst_qe X R e1) (subst_qt X R V)
  | exp_qabs P Q e1 =>
      exp_qabs (subst_qq X R P) (subst_qq X R Q) (subst_qe X R e1)
  | exp_qapp e1 Q => exp_qapp (subst_qe X R e1) (subst_qq X R Q)
  | exp_let e1 e2 => exp_let (subst_qe X R e1) (subst_qe X R e2)
  | exp_inl P e1 => exp_inl (subst_qq X R P) (subst_qe X R e1)
  | exp_inr P e1 => exp_inr (subst_qq X R P) (subst_qe X R e1)
  | exp_case e1 e2 e3 =>
      exp_case (subst_qe X R e1) (subst_qe X R e2) (subst_qe X R e3)
  | exp_pair P e1 e2 =>
      exp_pair (subst_qq X R P) (subst_qe X R e1) (subst_qe X R e2)
  | exp_first e1 => exp_first (subst_qe X R e1)
  | exp_second e1 => exp_second (subst_qe X R e1)
  | exp_ref P e1 => exp_ref (subst_qq X R P) (subst_qe X R e1)
  | exp_ref_label P l => exp_ref_label (subst_qq X R P) l
  | exp_deref e1 => exp_deref (subst_qe X R e1)
  | exp_set_ref e1 e2 => exp_set_ref (subst_qe X R e1) (subst_qe X R e2)
  | exp_upqual P e1 => exp_upqual (subst_qq X R P) (subst_qe X R e1)
  | exp_check P e1 => exp_check (subst_qq X R P) (subst_qe X R e1)
  end.

(* ================================================================== *)
(* Local closure (all free indices are below a given level)           *)
(* ================================================================== *)

Fixpoint lc_qua (k : nat) (Q : qua) : Prop :=
  match Q with
  | qua_base _ => True
  | qua_bvar n => n < k
  | qua_fvar _ => True
  | qua_meet Q1 Q2 => lc_qua k Q1 /\ lc_qua k Q2
  | qua_join Q1 Q2 => lc_qua k Q1 /\ lc_qua k Q2
  end.

Fixpoint lc_typ (k : nat) (T : typ) : Prop :=
  match T with
  | typ_top => True
  | typ_bvar n => n < k
  | typ_fvar _ => True
  | typ_arrow T1 T2 => lc_qtyp k T1 /\ lc_qtyp (S k) T2
  | typ_all T1 T2 => lc_typ k T1 /\ lc_qtyp (S k) T2
  | typ_qall Q T1 => lc_qua k Q /\ lc_qtyp (S k) T1
  | typ_sum T1 T2 => lc_qtyp k T1 /\ lc_qtyp k T2
  | typ_pair T1 T2 => lc_qtyp k T1 /\ lc_qtyp k T2
  | typ_ref T1 => lc_qtyp k T1
  end
with lc_qtyp (k : nat) (T : qtyp) : Prop :=
  match T with
  | qtyp_qtyp Q T1 => lc_qua k Q /\ lc_typ k T1
  end.

Fixpoint lc_exp (k : nat) (e : exp) : Prop :=
  match e with
  | exp_bvar n => n < k
  | exp_fvar _ => True
  | exp_abs P V e1 => lc_qua k P /\ lc_qtyp k V /\ lc_exp (S k) e1
  | exp_app e1 e2 => lc_exp k e1 /\ lc_exp k e2
  | exp_tabs P V e1 => lc_qua k P /\ lc_typ k V /\ lc_exp (S k) e1
  | exp_tapp e1 V => lc_exp k e1 /\ lc_typ k V
  | exp_qabs P Q e1 => lc_qua k P /\ lc_qua k Q /\ lc_exp (S k) e1
  | exp_qapp e1 Q => lc_exp k e1 /\ lc_qua k Q
  | exp_let e1 e2 => lc_exp k e1 /\ lc_exp (S k) e2
  | exp_inl P e1 => lc_qua k P /\ lc_exp k e1
  | exp_inr P e1 => lc_qua k P /\ lc_exp k e1
  | exp_case e1 e2 e3 => lc_exp k e1 /\ lc_exp (S k) e2 /\ lc_exp (S k) e3
  | exp_pair P e1 e2 => lc_qua k P /\ lc_exp k e1 /\ lc_exp k e2
  | exp_first e1 => lc_exp k e1
  | exp_second e1 => lc_exp k e1
  | exp_ref P e1 => lc_qua k P /\ lc_exp k e1
  | exp_ref_label P _ => lc_qua k P
  | exp_deref e1 => lc_exp k e1
  | exp_set_ref e1 e2 => lc_exp k e1 /\ lc_exp k e2
  | exp_upqual P e1 => lc_qua k P /\ lc_exp k e1
  | exp_check P e1 => lc_qua k P /\ lc_exp k e1
  end.

Lemma lc_qua_mono : forall k k' Q, k <= k' -> lc_qua k Q -> lc_qua k' Q.
Proof.
  intros k k' Q Hle. induction Q; simpl; auto; intros H; try lia.
  - destruct H as [H1 H2]. split; [apply IHQ1|apply IHQ2]; auto.
  - destruct H as [H1 H2]. split; [apply IHQ1|apply IHQ2]; auto.
Qed.

Scheme typ_mut_ind := Induction for typ Sort Prop
  with qtyp_mut_ind := Induction for qtyp Sort Prop.

Lemma lc_typ_mono : forall T, (forall k k', k <= k' -> lc_typ k T -> lc_typ k' T).
Proof.
  apply (typ_mut_ind
    (fun T => forall k k', k <= k' -> lc_typ k T -> lc_typ k' T)
    (fun T => forall k k', k <= k' -> lc_qtyp k T -> lc_qtyp k' T)).
  - intros; exact I.
  - intros n k k' Hle H; simpl in *; lia.
  - intros; exact I.
  - intros q1 IH1 q2 IH2 k k' Hle H. simpl in H. destruct H as [H1 H2]. split.
    + apply IH1 with (k := k) (k' := k'); auto.
    + apply IH2 with (k := S k) (k' := S k'); auto. lia.
  - intros T1 IH1 q IH2 k k' Hle H. simpl in H. destruct H as [H1 H2]. split.
    + apply IH1 with (k := k) (k' := k'); auto.
    + apply IH2 with (k := S k) (k' := S k'); auto. lia.
  - intros Q q IH2 k k' Hle H. simpl in H. destruct H as [H1 H2]. split.
    + apply lc_qua_mono with (k := k); auto.
    + apply IH2 with (k := S k) (k' := S k'); auto. lia.
  - intros q1 IH1 q2 IH2 k k' Hle H. simpl in H. destruct H as [H1 H2]. split.
    + apply IH1 with (k := k) (k' := k'); auto.
    + apply IH2 with (k := k) (k' := k'); auto.
  - intros q1 IH1 q2 IH2 k k' Hle H. simpl in H. destruct H as [H1 H2]. split.
    + apply IH1 with (k := k) (k' := k'); auto.
    + apply IH2 with (k := k) (k' := k'); auto.
  - intros q IH k k' Hle H. simpl in *. apply IH with (k := k) (k' := k'); auto.
  - intros Q T IH k k' Hle H. simpl in H. destruct H as [H1 H2]. split.
    + apply lc_qua_mono with (k := k); auto.
    + apply IH with (k := k) (k' := k'); auto.
Qed.

Lemma lc_qtyp_mono : forall T k k', k <= k' -> lc_qtyp k T -> lc_qtyp k' T.
Proof.
  intros [Q T] k k' Hle H. simpl in *. destruct H as [H1 H2].
  split; [apply lc_qua_mono with (k := k); auto| apply lc_typ_mono with (k := k); auto].
Qed.

Lemma lc_exp_mono : forall e k k', k <= k' -> lc_exp k e -> lc_exp k' e.
Proof.
  induction e; simpl; intros k k' Hle H.
  - lia.
  - exact I.
  - destruct H as [H1 [H2 H3]]. split; [|split].
    + apply lc_qua_mono with (k := k); auto.
    + apply lc_qtyp_mono with (k := k); auto.
    + apply IHe with (k := S k) (k' := S k'); auto. lia.
  - destruct H as [H1 H2]. split.
    + apply IHe1 with (k := k) (k' := k'); auto.
    + apply IHe2 with (k := k) (k' := k'); auto.
  - destruct H as [H1 [H2 H3]]. split; [|split].
    + apply lc_qua_mono with (k := k); auto.
    + apply lc_typ_mono with (k := k) (k' := k'); auto.
    + apply IHe with (k := S k) (k' := S k'); auto. lia.
  - destruct H as [H1 H2]. split.
    + apply IHe with (k := k) (k' := k'); auto.
    + apply lc_typ_mono with (k := k) (k' := k'); auto.
  - destruct H as [H1 [H2 H3]]. split; [|split].
    + apply lc_qua_mono with (k := k); auto.
    + apply lc_qua_mono with (k := k); auto.
    + apply IHe with (k := S k) (k' := S k'); auto. lia.
  - destruct H as [H1 H2]. split.
    + apply IHe with (k := k) (k' := k'); auto.
    + apply lc_qua_mono with (k := k); auto.
  - destruct H as [H1 H2]. split.
    + apply IHe1 with (k := k) (k' := k'); auto.
    + apply IHe2 with (k := S k) (k' := S k'); auto. lia.
  - destruct H as [H1 H2]. split.
    + apply lc_qua_mono with (k := k); auto.
    + apply IHe with (k := k) (k' := k'); auto.
  - destruct H as [H1 H2]. split.
    + apply lc_qua_mono with (k := k); auto.
    + apply IHe with (k := k) (k' := k'); auto.
  - destruct H as [H1 [H2 H3]]. split; [|split].
    + apply IHe1 with (k := k) (k' := k'); auto.
    + apply IHe2 with (k := S k) (k' := S k'); auto. lia.
    + apply IHe3 with (k := S k) (k' := S k'); auto. lia.
  - destruct H as [H1 [H2 H3]]. split; [|split].
    + apply lc_qua_mono with (k := k); auto.
    + apply IHe1 with (k := k) (k' := k'); auto.
    + apply IHe2 with (k := k) (k' := k'); auto.
  - apply IHe with (k := k) (k' := k'); auto.
  - apply IHe with (k := k) (k' := k'); auto.
  - destruct H as [H1 H2]. split.
    + apply lc_qua_mono with (k := k); auto.
    + apply IHe with (k := k) (k' := k'); auto.
  - apply lc_qua_mono with (k := k); auto.
  - apply IHe with (k := k) (k' := k'); auto.
  - destruct H as [H1 H2]. split.
    + apply IHe1 with (k := k) (k' := k'); auto.
    + apply IHe2 with (k := k) (k' := k'); auto.
  - destruct H as [H1 H2]. split.
    + apply lc_qua_mono with (k := k); auto.
    + apply IHe with (k := k) (k' := k'); auto.
  - destruct H as [H1 H2]. split.
    + apply lc_qua_mono with (k := k); auto.
    + apply IHe with (k := k) (k' := k'); auto.
Qed.

(* identity of opening on locally closed objects *)
Lemma lc_qua_id : forall Q k K R, lc_qua k Q -> k <= K -> open_qq_rec K R Q = Q.
Proof.
  induction Q.
  - intros k K R Hlk Hle. reflexivity.
  - intros k K R Hlk Hle. simpl. destruct (K == n) as [e|e].
    + simpl in Hlk. exfalso. lia.
    + reflexivity.
  - intros k K R Hlk Hle. reflexivity.
  - intros k K R Hlk Hle. simpl. destruct Hlk as [H1 H2]. f_equal.
    + apply IHQ1 with (k := k) (K := K) (R := R); auto.
    + apply IHQ2 with (k := k) (K := K) (R := R); auto.
  - intros k K R Hlk Hle. simpl. destruct Hlk as [H1 H2]. f_equal.
    + apply IHQ1 with (k := k) (K := K) (R := R); auto.
    + apply IHQ2 with (k := k) (K := K) (R := R); auto.
Qed.

Lemma lc_typ_id_tt : forall T, (forall k K W, lc_typ k T -> k <= K -> open_tt_rec K W T = T).
Proof.
  apply (typ_mut_ind
    (fun T => forall k K W, lc_typ k T -> k <= K -> open_tt_rec K W T = T)
    (fun T => forall k K W, lc_qtyp k T -> k <= K -> open_tqt_rec K W T = T)).
  - intros; reflexivity.
  - intros n k K W Hlk Hle. simpl. destruct (K == n) as [e|e].
    + simpl in Hlk. exfalso. lia.
    + reflexivity.
  - intros; reflexivity.
  - intros q1 IH1 q2 IH2 k K W Hlk Hle. simpl. destruct Hlk as [H1 H2].
    assert (Hle' : S k <= S K) by lia.
    rewrite (IH1 k K W H1 Hle). rewrite (IH2 (S k) (S K) W H2 Hle'). reflexivity.
  - intros T1 IH1 q IH2 k K W Hlk Hle. simpl. destruct Hlk as [H1 H2].
    assert (Hle' : S k <= S K) by lia.
    rewrite (IH1 k K W H1 Hle). rewrite (IH2 (S k) (S K) W H2 Hle'). reflexivity.
  - intros Q q IH2 k K W Hlk Hle. simpl. destruct Hlk as [H1 H2].
    assert (Hle' : S k <= S K) by lia.
    rewrite (IH2 (S k) (S K) W H2 Hle'). reflexivity.
  - intros q1 IH1 q2 IH2 k K W Hlk Hle. simpl. destruct Hlk as [H1 H2].
    rewrite (IH1 k K W H1 Hle). rewrite (IH2 k K W H2 Hle). reflexivity.
  - intros q1 IH1 q2 IH2 k K W Hlk Hle. simpl. destruct Hlk as [H1 H2].
    rewrite (IH1 k K W H1 Hle). rewrite (IH2 k K W H2 Hle). reflexivity.
  - intros q IH k K W Hlk Hle. simpl.
    rewrite (IH k K W Hlk Hle). reflexivity.
  - intros Q T IH k K W Hlk Hle. simpl. destruct Hlk as [H1 H2].
    f_equal. apply IH with (k := k) (K := K); auto.
Qed.

Lemma lc_qtyp_id_tqt : forall T k K W, lc_qtyp k T -> k <= K -> open_tqt_rec K W T = T.
Proof.
  intros [Q T] k K W Hlk Hle. simpl in *. destruct Hlk as [H1 H2]. simpl. f_equal.
  apply lc_typ_id_tt with (k := k) (K := K); auto.
Qed.

Lemma lc_typ_id_qt : forall T, (forall k K R, lc_typ k T -> k <= K -> open_qt_rec K R T = T).
Proof.
  apply (typ_mut_ind
    (fun T => forall k K R, lc_typ k T -> k <= K -> open_qt_rec K R T = T)
    (fun T => forall k K R, lc_qtyp k T -> k <= K -> open_qqt_rec K R T = T)).
  - intros; reflexivity.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros q1 IH1 q2 IH2 k K R Hlk Hle. simpl. destruct Hlk as [H1 H2].
    assert (Hle' : S k <= S K) by lia.
    rewrite (IH1 k K R H1 Hle). rewrite (IH2 (S k) (S K) R H2 Hle'). reflexivity.
  - intros T1 IH1 q IH2 k K R Hlk Hle. simpl. destruct Hlk as [H1 H2].
    assert (Hle' : S k <= S K) by lia.
    rewrite (IH1 k K R H1 Hle). rewrite (IH2 (S k) (S K) R H2 Hle'). reflexivity.
  - intros Q q IH2 k K R Hlk Hle. simpl. destruct Hlk as [H1 H2].
    assert (Hle' : S k <= S K) by lia.
    rewrite (lc_qua_id Q k K R H1 Hle). rewrite (IH2 (S k) (S K) R H2 Hle'). reflexivity.
  - intros q1 IH1 q2 IH2 k K R Hlk Hle. simpl. destruct Hlk as [H1 H2].
    rewrite (IH1 k K R H1 Hle). rewrite (IH2 k K R H2 Hle). reflexivity.
  - intros q1 IH1 q2 IH2 k K R Hlk Hle. simpl. destruct Hlk as [H1 H2].
    rewrite (IH1 k K R H1 Hle). rewrite (IH2 k K R H2 Hle). reflexivity.
  - intros q IH k K R Hlk Hle. simpl.
    rewrite (IH k K R Hlk Hle). reflexivity.
  - intros Q T IH k K R Hlk Hle. simpl. destruct Hlk as [H1 H2].
    rewrite (lc_qua_id Q k K R H1 Hle). f_equal.
    apply IH with (k := k) (K := K); auto.
Qed.

Lemma lc_qtyp_id_qqt : forall T k K R, lc_qtyp k T -> k <= K -> open_qqt_rec K R T = T.
Proof.
  intros [Q T] k K R Hlk Hle. simpl in *. destruct Hlk as [H1 H2]. simpl.
  rewrite (lc_qua_id Q k K R H1 Hle). f_equal.
  apply lc_typ_id_qt with (k := k) (K := K); auto.
Qed.

Lemma lc_qua_open_qq_body : forall Q K R, lc_qua K (open_qq_rec K R Q) -> lc_qua (S K) Q.
Proof.
  induction Q; simpl; intros K R H.
  - exact I.
  - destruct (K == n) as [e|e]; simpl in *; try exact I; lia.
  - exact I.
  - destruct H as [H1 H2]. split.
    + apply IHQ1 with (K := K) (R := R); auto.
    + apply IHQ2 with (K := K) (R := R); auto.
  - destruct H as [H1 H2]. split.
    + apply IHQ1 with (K := K) (R := R); auto.
    + apply IHQ2 with (K := K) (R := R); auto.
Qed.

Lemma lc_typ_open_tt_body :
  forall T, (forall K W, lc_typ K (open_tt_rec K W T) -> lc_typ (S K) T).
Proof.
  apply (typ_mut_ind
    (fun T => forall K W, lc_typ K (open_tt_rec K W T) -> lc_typ (S K) T)
    (fun T => forall K W, lc_qtyp K (open_tqt_rec K W T) -> lc_qtyp (S K) T)).
  - intros; exact I.
  - intros n K W H. simpl in H. destruct (K == n) as [e|e]; simpl in *; lia.
  - intros; exact I.
  - intros q1 IH1 q2 IH2 K W H. simpl in H. destruct H as [H1 H2]. split.
    + apply IH1 with (K := K) (W := W); auto.
    + apply IH2 with (K := S K) (W := W); auto.
  - intros T1 IH1 q IH2 K W H. simpl in H. destruct H as [H1 H2]. split.
    + apply IH1 with (K := K) (W := W); auto.
    + apply IH2 with (K := S K) (W := W); auto.
  - intros Q q IH2 K W H. simpl in H. destruct H as [H1 H2]. split.
    + apply lc_qua_mono with (k := K). lia. auto.
    + apply IH2 with (K := S K) (W := W); auto.
  - intros q1 IH1 q2 IH2 K W H. simpl in H. destruct H as [H1 H2]. split.
    + apply IH1 with (K := K) (W := W); auto.
    + apply IH2 with (K := K) (W := W); auto.
  - intros q1 IH1 q2 IH2 K W H. simpl in H. destruct H as [H1 H2]. split.
    + apply IH1 with (K := K) (W := W); auto.
    + apply IH2 with (K := K) (W := W); auto.
  - intros q IH K W H. simpl in H. apply IH with (K := K) (W := W); auto.
  - intros Q T IH K W H. simpl in H. destruct H as [H1 H2]. split.
    + apply lc_qua_mono with (k := K). lia. auto.
    + apply IH with (K := K) (W := W); auto.
Qed.

Lemma lc_qtyp_open_tqt_body : forall T K W, lc_qtyp K (open_tqt_rec K W T) -> lc_qtyp (S K) T.
Proof.
  intros [Q T] K W H. simpl in H. destruct H as [H1 H2]. simpl. split.
  - apply lc_qua_mono with (k := K). lia. auto.
  - apply lc_typ_open_tt_body with (K := K) (W := W); auto.
Qed.

Lemma lc_typ_open_qt_body :
  forall T, (forall K R, lc_typ K (open_qt_rec K R T) -> lc_typ (S K) T).
Proof.
  apply (typ_mut_ind
    (fun T => forall K R, lc_typ K (open_qt_rec K R T) -> lc_typ (S K) T)
    (fun T => forall K R, lc_qtyp K (open_qqt_rec K R T) -> lc_qtyp (S K) T)).
  - intros; exact I.
  - intros n K R H. simpl in *. lia.
  - intros; exact I.
  - intros q1 IH1 q2 IH2 K R H. simpl in H. destruct H as [H1 H2]. split.
    + apply IH1 with (K := K) (R := R). exact H1.
    + apply IH2 with (K := S K) (R := R). exact H2.
  - intros T1 IH1 q IH2 K R H. simpl in H. destruct H as [H1 H2]. split.
    + apply IH1 with (K := K) (R := R). exact H1.
    + apply IH2 with (K := S K) (R := R). exact H2.
  - intros Q q IH2 K R H. simpl in H. destruct H as [H1 H2]. split.
    + apply lc_qua_open_qq_body with (K := K) (R := R). exact H1.
    + apply IH2 with (K := S K) (R := R). exact H2.
  - intros q1 IH1 q2 IH2 K R H. simpl in H. destruct H as [H1 H2]. split.
    + apply IH1 with (K := K) (R := R). exact H1.
    + apply IH2 with (K := K) (R := R). exact H2.
  - intros q1 IH1 q2 IH2 K R H. simpl in H. destruct H as [H1 H2]. split.
    + apply IH1 with (K := K) (R := R). exact H1.
    + apply IH2 with (K := K) (R := R). exact H2.
  - intros q IH K R H. simpl in H. apply IH with (K := K) (R := R). exact H.
  - intros Q T IH K R H. simpl in H. destruct H as [H1 H2]. split.
    + apply lc_qua_open_qq_body with (K := K) (R := R). exact H1.
    + apply IH with (K := K) (R := R). exact H2.
Qed.

Lemma lc_qtyp_open_qqt_body : forall T K R, lc_qtyp K (open_qqt_rec K R T) -> lc_qtyp (S K) T.
Proof.
  intros [Q T] K R H. simpl in H. destruct H as [H1 H2]. simpl. split.
  - apply lc_qua_open_qq_body with (K := K) (R := R); auto.
  - apply lc_typ_open_qt_body with (K := K) (R := R); auto.
Qed.

Lemma lc_exp_open_ee_body : forall e K w, lc_exp K (open_ee_rec K w e) -> lc_exp (S K) e.
Proof.
  induction e; simpl; intros K w H.
  - destruct (K == n) as [e|e]; simpl in *; lia.
  - exact I.
  - destruct H as [H1 [H2 H3]]. split; [|split].
    + apply lc_qua_mono with (k := K). lia. exact H1.
    + apply lc_qtyp_mono with (k := K). lia. exact H2.
    + apply IHe with (K := S K) (w := w). exact H3.
  - destruct H as [H1 H2]. split.
    + apply IHe1 with (K := K) (w := w). exact H1.
    + apply IHe2 with (K := K) (w := w). exact H2.
  - destruct H as [H1 [H2 H3]]. split; [|split].
    + apply lc_qua_mono with (k := K). lia. exact H1.
    + apply lc_typ_mono with (k := K) (k' := S K). lia. exact H2.
    + apply IHe with (K := S K) (w := w). exact H3.
  - destruct H as [H1 H2]. split.
    + apply IHe with (K := K) (w := w). exact H1.
    + apply lc_typ_mono with (k := K) (k' := S K). lia. exact H2.
  - destruct H as [H1 [H2 H3]]. split; [|split].
    + apply lc_qua_mono with (k := K). lia. exact H1.
    + apply lc_qua_mono with (k := K). lia. exact H2.
    + apply IHe with (K := S K) (w := w). exact H3.
  - destruct H as [H1 H2]. split.
    + apply IHe with (K := K) (w := w). exact H1.
    + apply lc_qua_mono with (k := K). lia. exact H2.
  - destruct H as [H1 H2]. split.
    + apply IHe1 with (K := K) (w := w). exact H1.
    + apply IHe2 with (K := S K) (w := w). exact H2.
  - destruct H as [H1 H2]. split.
    + apply lc_qua_mono with (k := K). lia. exact H1.
    + apply IHe with (K := K) (w := w). exact H2.
  - destruct H as [H1 H2]. split.
    + apply lc_qua_mono with (k := K). lia. exact H1.
    + apply IHe with (K := K) (w := w). exact H2.
  - destruct H as [H1 [H2 H3]]. split; [|split].
    + apply IHe1 with (K := K) (w := w). exact H1.
    + apply IHe2 with (K := S K) (w := w). exact H2.
    + apply IHe3 with (K := S K) (w := w). exact H3.
  - destruct H as [H1 [H2 H3]]. split; [|split].
    + apply lc_qua_mono with (k := K). lia. exact H1.
    + apply IHe1 with (K := K) (w := w). exact H2.
    + apply IHe2 with (K := K) (w := w). exact H3.
  - apply IHe with (K := K) (w := w). exact H.
  - apply IHe with (K := K) (w := w). exact H.
  - destruct H as [H1 H2]. split.
    + apply lc_qua_mono with (k := K). lia. exact H1.
    + apply IHe with (K := K) (w := w). exact H2.
  - apply lc_qua_mono with (k := K). lia. exact H.
  - apply IHe with (K := K) (w := w). exact H.
  - destruct H as [H1 H2]. split.
    + apply IHe1 with (K := K) (w := w). exact H1.
    + apply IHe2 with (K := K) (w := w). exact H2.
  - destruct H as [H1 H2]. split.
    + apply lc_qua_mono with (k := K). lia. exact H1.
    + apply IHe with (K := K) (w := w). exact H2.
  - destruct H as [H1 H2]. split.
    + apply lc_qua_mono with (k := K). lia. exact H1.
    + apply IHe with (K := K) (w := w). exact H2.
Qed.

Lemma lc_exp_open_te_body : forall e K U, lc_exp K (open_te_rec K U e) -> lc_exp (S K) e.
Proof.
  induction e; simpl; intros K U H.
  - simpl in *. lia.
  - exact I.
  - destruct H as [H1 [H2 H3]]. split; [|split].
    + apply lc_qua_mono with (k := K). lia. exact H1.
    + apply lc_qtyp_open_tqt_body with (K := K) (W := U). exact H2.
    + apply IHe with (K := S K) (U := U). exact H3.
  - destruct H as [H1 H2]. split.
    + apply IHe1 with (K := K) (U := U). exact H1.
    + apply IHe2 with (K := K) (U := U). exact H2.
  - destruct H as [H1 [H2 H3]]. split; [|split].
    + apply lc_qua_mono with (k := K). lia. exact H1.
    + apply lc_typ_open_tt_body with (K := K) (W := U). exact H2.
    + apply IHe with (K := S K) (U := U). exact H3.
  - destruct H as [H1 H2]. split.
    + apply IHe with (K := K) (U := U). exact H1.
    + apply lc_typ_open_tt_body with (K := K) (W := U). exact H2.
  - destruct H as [H1 [H2 H3]]. split; [|split].
    + apply lc_qua_mono with (k := K). lia. exact H1.
    + apply lc_qua_mono with (k := K). lia. exact H2.
    + apply IHe with (K := S K) (U := U). exact H3.
  - destruct H as [H1 H2]. split.
    + apply IHe with (K := K) (U := U). exact H1.
    + apply lc_qua_mono with (k := K). lia. exact H2.
  - destruct H as [H1 H2]. split.
    + apply IHe1 with (K := K) (U := U). exact H1.
    + apply IHe2 with (K := S K) (U := U). exact H2.
  - destruct H as [H1 H2]. split.
    + apply lc_qua_mono with (k := K). lia. exact H1.
    + apply IHe with (K := K) (U := U). exact H2.
  - destruct H as [H1 H2]. split.
    + apply lc_qua_mono with (k := K). lia. exact H1.
    + apply IHe with (K := K) (U := U). exact H2.
  - destruct H as [H1 [H2 H3]]. split; [|split].
    + apply IHe1 with (K := K) (U := U). exact H1.
    + apply IHe2 with (K := S K) (U := U). exact H2.
    + apply IHe3 with (K := S K) (U := U). exact H3.
  - destruct H as [H1 [H2 H3]]. split; [|split].
    + apply lc_qua_mono with (k := K). lia. exact H1.
    + apply IHe1 with (K := K) (U := U). exact H2.
    + apply IHe2 with (K := K) (U := U). exact H3.
  - apply IHe with (K := K) (U := U). exact H.
  - apply IHe with (K := K) (U := U). exact H.
  - destruct H as [H1 H2]. split.
    + apply lc_qua_mono with (k := K). lia. exact H1.
    + apply IHe with (K := K) (U := U). exact H2.
  - apply lc_qua_mono with (k := K). lia. exact H.
  - apply IHe with (K := K) (U := U). exact H.
  - destruct H as [H1 H2]. split.
    + apply IHe1 with (K := K) (U := U). exact H1.
    + apply IHe2 with (K := K) (U := U). exact H2.
  - destruct H as [H1 H2]. split.
    + apply lc_qua_mono with (k := K). lia. exact H1.
    + apply IHe with (K := K) (U := U). exact H2.
  - destruct H as [H1 H2]. split.
    + apply lc_qua_mono with (k := K). lia. exact H1.
    + apply IHe with (K := K) (U := U). exact H2.
Qed.

Lemma lc_exp_open_qe_body : forall e K R, lc_exp K (open_qe_rec K R e) -> lc_exp (S K) e.
Proof.
  induction e; simpl; intros K R H.
  - simpl in *. lia.
  - exact I.
  - destruct H as [H1 [H2 H3]]. split; [|split].
    + apply lc_qua_open_qq_body with (K := K) (R := R). exact H1.
    + apply lc_qtyp_open_qqt_body with (K := K) (R := R). exact H2.
    + apply IHe with (K := S K) (R := R). exact H3.
  - destruct H as [H1 H2]. split.
    + apply IHe1 with (K := K) (R := R). exact H1.
    + apply IHe2 with (K := K) (R := R). exact H2.
  - destruct H as [H1 [H2 H3]]. split; [|split].
    + apply lc_qua_open_qq_body with (K := K) (R := R). exact H1.
    + apply lc_typ_open_qt_body with (K := K) (R := R). exact H2.
    + apply IHe with (K := S K) (R := R). exact H3.
  - destruct H as [H1 H2]. split.
    + apply IHe with (K := K) (R := R). exact H1.
    + apply lc_typ_open_qt_body with (K := K) (R := R). exact H2.
  - destruct H as [H1 [H2 H3]]. split; [|split].
    + apply lc_qua_open_qq_body with (K := K) (R := R). exact H1.
    + apply lc_qua_open_qq_body with (K := K) (R := R). exact H2.
    + apply IHe with (K := S K) (R := R). exact H3.
  - destruct H as [H1 H2]. split.
    + apply IHe with (K := K) (R := R). exact H1.
    + apply lc_qua_open_qq_body with (K := K) (R := R). exact H2.
  - destruct H as [H1 H2]. split.
    + apply IHe1 with (K := K) (R := R). exact H1.
    + apply IHe2 with (K := S K) (R := R). exact H2.
  - destruct H as [H1 H2]. split.
    + apply lc_qua_open_qq_body with (K := K) (R := R). exact H1.
    + apply IHe with (K := K) (R := R). exact H2.
  - destruct H as [H1 H2]. split.
    + apply lc_qua_open_qq_body with (K := K) (R := R). exact H1.
    + apply IHe with (K := K) (R := R). exact H2.
  - destruct H as [H1 [H2 H3]]. split; [|split].
    + apply IHe1 with (K := K) (R := R). exact H1.
    + apply IHe2 with (K := S K) (R := R). exact H2.
    + apply IHe3 with (K := S K) (R := R). exact H3.
  - destruct H as [H1 [H2 H3]]. split; [|split].
    + apply lc_qua_open_qq_body with (K := K) (R := R). exact H1.
    + apply IHe1 with (K := K) (R := R). exact H2.
    + apply IHe2 with (K := K) (R := R). exact H3.
  - apply IHe with (K := K) (R := R). exact H.
  - apply IHe with (K := K) (R := R). exact H.
  - destruct H as [H1 H2]. split.
    + apply lc_qua_open_qq_body with (K := K) (R := R). exact H1.
    + apply IHe with (K := K) (R := R). exact H2.
  - apply lc_qua_open_qq_body with (K := K) (R := R). exact H.
  - apply IHe with (K := K) (R := R). exact H.
  - destruct H as [H1 H2]. split.
    + apply IHe1 with (K := K) (R := R). exact H1.
    + apply IHe2 with (K := K) (R := R). exact H2.
  - destruct H as [H1 H2]. split.
    + apply lc_qua_open_qq_body with (K := K) (R := R). exact H1.
    + apply IHe with (K := K) (R := R). exact H2.
  - destruct H as [H1 H2]. split.
    + apply lc_qua_open_qq_body with (K := K) (R := R). exact H1.
    + apply IHe with (K := K) (R := R). exact H2.
Qed.

Scheme type_mut_ind := Induction for type Sort Prop
  with qtype_mut_ind := Induction for qtype Sort Prop.

Lemma qual_lc0 : forall Q, qual Q -> lc_qua 0 Q.
Proof.
  intros Q H. induction H; simpl; auto; split; auto.
Qed.

Lemma type_lc : forall T, type T -> lc_typ 0 T.
Proof.
  apply (type_mut_ind
    (fun T _ => lc_typ 0 T)
    (fun T _ => lc_qtyp 0 T)).
  - exact I.
  - intros X. exact I.
  - intros T1 T2 q1 IH1 q2 IH2. simpl. split.
    + exact IH1.
    + apply lc_qtyp_mono with (k := 0). lia. exact IH2.
  - intros L T1 T2 t IHt q IHq. simpl. split.
    + exact IHt.
    + destruct (atom_fresh L) as [X HX].
      apply lc_qtyp_open_tqt_body with (K := 0) (W := typ_fvar X).
      apply IHq. exact HX.
  - intros L Q T q qbody IHbody. simpl. split.
    + apply qual_lc0. exact q.
    + destruct (atom_fresh L) as [X HX].
      apply lc_qtyp_open_qqt_body with (K := 0) (R := qua_fvar X).
      apply IHbody. exact HX.
  - intros T1 T2 q1 IH1 q2 IH2. simpl. split; [exact IH1|exact IH2].
  - intros T1 T2 q1 IH1 q2 IH2. simpl. split; [exact IH1|exact IH2].
  - intros Q T q t IHt. simpl. split.
    + apply qual_lc0. exact q.
    + exact IHt.
Qed.

Lemma qtype_lc0 : forall T, qtype T -> lc_qtyp 0 T.
Proof.
  intros T H. inversion H; subst. simpl. split.
  - apply qual_lc0. assumption.
  - apply type_lc. assumption.
Qed.

Lemma expr_lc0 : forall e, expr e -> lc_exp 0 e.
Proof.
  intros e H. induction H; simpl.
  - exact I.
  - split; [|split].
    + apply qual_lc0. exact H.
    + apply qtype_lc0. exact H0.
    + destruct (atom_fresh L) as [x Hx].
      apply lc_exp_open_ee_body with (K := 0) (w := exp_fvar x).
      apply H2. exact Hx.
  - split.
    + exact IHexpr1.
    + exact IHexpr2.
  - split; [|split].
    + apply qual_lc0. exact H.
    + apply type_lc. exact H0.
    + destruct (atom_fresh L) as [X HX].
      apply lc_exp_open_te_body with (K := 0) (U := typ_fvar X).
      apply H2. exact HX.
  - split.
    + exact IHexpr.
    + apply type_lc. exact H0.
  - split; [|split].
    + apply qual_lc0. exact H.
    + apply qual_lc0. exact H0.
    + destruct (atom_fresh L) as [X HX].
      apply lc_exp_open_qe_body with (K := 0) (R := qua_fvar X).
      apply H2. exact HX.
  - split.
    + exact IHexpr.
    + apply qual_lc0. exact H0.
  - split.
    + exact IHexpr.
    + destruct (atom_fresh L) as [x Hx].
      apply lc_exp_open_ee_body with (K := 0) (w := exp_fvar x).
      apply H1. exact Hx.
  - split.
    + apply qual_lc0. exact H.
    + exact IHexpr.
  - split.
    + apply qual_lc0. exact H.
    + exact IHexpr.
  - split; [|split].
    + exact IHexpr.
    + destruct (atom_fresh L) as [x Hx].
      apply lc_exp_open_ee_body with (K := 0) (w := exp_fvar x).
      apply H1. exact Hx.
    + destruct (atom_fresh L) as [x Hx].
      apply lc_exp_open_ee_body with (K := 0) (w := exp_fvar x).
      apply H3. exact Hx.
  - split; [|split].
    + apply qual_lc0. exact H.
    + exact IHexpr1.
    + exact IHexpr2.
  - exact IHexpr.
  - exact IHexpr.
  - split.
    + apply qual_lc0. exact H.
    + exact IHexpr.
  - split.
    + apply qual_lc0. exact H.
    + exact IHexpr.
Qed.

Lemma lc_exp_id_ee : forall e k K w, lc_exp k e -> k <= K -> open_ee_rec K w e = e.
Proof.
  induction e; simpl; intros k K w Hlk Hle.
  - destruct (K == n) as [e|e]; simpl in *; [exfalso; lia|reflexivity].
  - reflexivity.
  - destruct Hlk as [H1 [H2 H3]]. f_equal.
    apply IHe with (k := S k) (K := S K); auto. lia.
  - destruct Hlk as [H1 H2]. f_equal.
    + apply IHe1 with (k := k) (K := K); auto.
    + apply IHe2 with (k := k) (K := K); auto.
  - destruct Hlk as [H1 [H2 H3]]. f_equal.
    apply IHe with (k := S k) (K := S K); auto. lia.
  - destruct Hlk as [H1 H2]. f_equal.
    apply IHe with (k := k) (K := K); auto.
  - destruct Hlk as [H1 [H2 H3]]. f_equal.
    apply IHe with (k := S k) (K := S K); auto. lia.
  - destruct Hlk as [H1 H2]. f_equal.
    apply IHe with (k := k) (K := K); auto.
  - destruct Hlk as [H1 H2]. f_equal.
    + apply IHe1 with (k := k) (K := K); auto.
    + apply IHe2 with (k := S k) (K := S K); auto. lia.
  - destruct Hlk as [H1 H2]. f_equal.
    apply IHe with (k := k) (K := K); auto.
  - destruct Hlk as [H1 H2]. f_equal.
    apply IHe with (k := k) (K := K); auto.
  - destruct Hlk as [H1 [H2 H3]]. f_equal.
    + apply IHe1 with (k := k) (K := K); auto.
    + apply IHe2 with (k := S k) (K := S K); auto. lia.
    + apply IHe3 with (k := S k) (K := S K); auto. lia.
  - destruct Hlk as [H1 [H2 H3]]. f_equal.
    + apply IHe1 with (k := k) (K := K); auto.
    + apply IHe2 with (k := k) (K := K); auto.
  - f_equal. apply IHe with (k := k) (K := K); auto.
  - f_equal. apply IHe with (k := k) (K := K); auto.
  - destruct Hlk as [H1 H2]. f_equal.
    apply IHe with (k := k) (K := K); auto.
  - reflexivity.
  - f_equal. apply IHe with (k := k) (K := K); auto.
  - destruct Hlk as [H1 H2]. f_equal.
    + apply IHe1 with (k := k) (K := K); auto.
    + apply IHe2 with (k := k) (K := K); auto.
  - destruct Hlk as [H1 H2]. f_equal.
    apply IHe with (k := k) (K := K); auto.
  - destruct Hlk as [H1 H2]. f_equal.
    apply IHe with (k := k) (K := K); auto.
Qed.

Lemma lc_exp_id_te : forall e k K U, lc_exp k e -> k <= K -> open_te_rec K U e = e.
Proof.
  induction e; simpl; intros k K U Hlk Hle.
  - reflexivity.
  - reflexivity.
  - destruct Hlk as [H1 [H2 H3]]. f_equal.
    + apply lc_qtyp_id_tqt with (k := k) (K := K); auto.
    + apply IHe with (k := S k) (K := S K); auto. lia.
  - destruct Hlk as [H1 H2]. f_equal.
    + apply IHe1 with (k := k) (K := K); auto.
    + apply IHe2 with (k := k) (K := K); auto.
  - destruct Hlk as [H1 [H2 H3]]. f_equal.
    + apply lc_typ_id_tt with (k := k) (K := K) (W := U); auto.
    + apply IHe with (k := S k) (K := S K); auto. lia.
  - destruct Hlk as [H1 H2]. f_equal.
    + apply IHe with (k := k) (K := K); auto.
    + apply lc_typ_id_tt with (k := k) (K := K) (W := U); auto.
  - destruct Hlk as [H1 [H2 H3]]. f_equal.
    apply IHe with (k := S k) (K := S K); auto. lia.
  - destruct Hlk as [H1 H2]. f_equal.
    apply IHe with (k := k) (K := K); auto.
  - destruct Hlk as [H1 H2]. f_equal.
    + apply IHe1 with (k := k) (K := K); auto.
    + apply IHe2 with (k := S k) (K := S K); auto. lia.
  - destruct Hlk as [H1 H2]. f_equal.
    apply IHe with (k := k) (K := K); auto.
  - destruct Hlk as [H1 H2]. f_equal.
    apply IHe with (k := k) (K := K); auto.
  - destruct Hlk as [H1 [H2 H3]]. f_equal.
    + apply IHe1 with (k := k) (K := K); auto.
    + apply IHe2 with (k := S k) (K := S K); auto. lia.
    + apply IHe3 with (k := S k) (K := S K); auto. lia.
  - destruct Hlk as [H1 [H2 H3]]. f_equal.
    + apply IHe1 with (k := k) (K := K); auto.
    + apply IHe2 with (k := k) (K := K); auto.
  - f_equal. apply IHe with (k := k) (K := K); auto.
  - f_equal. apply IHe with (k := k) (K := K); auto.
  - destruct Hlk as [H1 H2]. f_equal.
    apply IHe with (k := k) (K := K); auto.
  - reflexivity.
  - f_equal. apply IHe with (k := k) (K := K); auto.
  - destruct Hlk as [H1 H2]. f_equal.
    + apply IHe1 with (k := k) (K := K); auto.
    + apply IHe2 with (k := k) (K := K); auto.
  - destruct Hlk as [H1 H2]. f_equal.
    apply IHe with (k := k) (K := K); auto.
  - destruct Hlk as [H1 H2]. f_equal.
    apply IHe with (k := k) (K := K); auto.
Qed.

Lemma lc_exp_id_qe : forall e k K R, lc_exp k e -> k <= K -> open_qe_rec K R e = e.
Proof.
  induction e; simpl; intros k K R Hlk Hle.
  - reflexivity.
  - reflexivity.
  - destruct Hlk as [H1 [H2 H3]]. f_equal.
    + apply lc_qua_id with (k := k) (K := K); auto.
    + apply lc_qtyp_id_qqt with (k := k) (K := K); auto.
    + apply IHe with (k := S k) (K := S K); auto. lia.
  - destruct Hlk as [H1 H2]. f_equal.
    + apply IHe1 with (k := k) (K := K); auto.
    + apply IHe2 with (k := k) (K := K); auto.
  - destruct Hlk as [H1 [H2 H3]]. f_equal.
    + apply lc_qua_id with (k := k) (K := K); auto.
    + apply lc_typ_id_qt with (k := k) (K := K); auto.
    + apply IHe with (k := S k) (K := S K); auto. lia.
  - destruct Hlk as [H1 H2]. f_equal.
    + apply IHe with (k := k) (K := K); auto.
    + apply lc_typ_id_qt with (k := k) (K := K); auto.
  - destruct Hlk as [H1 [H2 H3]]. f_equal.
    + apply lc_qua_id with (k := k) (K := K); auto.
    + apply lc_qua_id with (k := k) (K := K); auto.
    + apply IHe with (k := S k) (K := S K); auto. lia.
  - destruct Hlk as [H1 H2]. f_equal.
    + apply IHe with (k := k) (K := K); auto.
    + apply lc_qua_id with (k := k) (K := K); auto.
  - destruct Hlk as [H1 H2]. f_equal.
    + apply IHe1 with (k := k) (K := K); auto.
    + apply IHe2 with (k := S k) (K := S K); auto. lia.
  - destruct Hlk as [H1 H2]. f_equal.
    + apply lc_qua_id with (k := k) (K := K); auto.
    + apply IHe with (k := k) (K := K); auto.
  - destruct Hlk as [H1 H2]. f_equal.
    + apply lc_qua_id with (k := k) (K := K); auto.
    + apply IHe with (k := k) (K := K); auto.
  - destruct Hlk as [H1 [H2 H3]]. f_equal.
    + apply IHe1 with (k := k) (K := K); auto.
    + apply IHe2 with (k := S k) (K := S K); auto. lia.
    + apply IHe3 with (k := S k) (K := S K); auto. lia.
  - destruct Hlk as [H1 [H2 H3]]. f_equal.
    + apply lc_qua_id with (k := k) (K := K); auto.
    + apply IHe1 with (k := k) (K := K); auto.
    + apply IHe2 with (k := k) (K := K); auto.
  - f_equal. apply IHe with (k := k) (K := K); auto.
  - f_equal. apply IHe with (k := k) (K := K); auto.
  - destruct Hlk as [H1 H2]. f_equal.
    + apply lc_qua_id with (k := k) (K := K); auto.
    + apply IHe with (k := k) (K := K); auto.
  - f_equal. apply lc_qua_id with (k := k) (K := K); auto.
  - f_equal. apply IHe with (k := k) (K := K); auto.
  - destruct Hlk as [H1 H2]. f_equal.
    + apply IHe1 with (k := k) (K := K); auto.
    + apply IHe2 with (k := k) (K := K); auto.
  - destruct Hlk as [H1 H2]. f_equal.
    + apply lc_qua_id with (k := k) (K := K); auto.
    + apply IHe with (k := k) (K := K); auto.
  - destruct Hlk as [H1 H2]. f_equal.
    + apply lc_qua_id with (k := k) (K := K); auto.
    + apply IHe with (k := k) (K := K); auto.
Qed.

Lemma type_open_tt_id : forall T K W, type T -> open_tt_rec K W T = T.
Proof.
  intros. apply lc_typ_id_tt with (k := 0); auto using type_lc. lia.
Qed.

Lemma qtype_open_tqt_id : forall T K W, qtype T -> open_tqt_rec K W T = T.
Proof.
  intros. apply lc_qtyp_id_tqt with (k := 0); auto using qtype_lc0. lia.
Qed.

Lemma type_open_qt_id : forall T K R, type T -> open_qt_rec K R T = T.
Proof.
  intros. apply lc_typ_id_qt with (k := 0); auto using type_lc. lia.
Qed.

Lemma qual_open_qq_id : forall Q K R, qual Q -> open_qq_rec K R Q = Q.
Proof.
  intros. apply lc_qua_id with (k := 0); auto using qual_lc0. lia.
Qed.

Lemma expr_open_ee_id : forall e K w, expr e -> open_ee_rec K w e = e.
Proof.
  intros. apply lc_exp_id_ee with (k := 0); auto using expr_lc0. lia.
Qed.

Lemma expr_open_te_id : forall e K U, expr e -> open_te_rec K U e = e.
Proof.
  intros. apply lc_exp_id_te with (k := 0); auto using expr_lc0. lia.
Qed.

Lemma expr_open_qe_id : forall e K R, expr e -> open_qe_rec K R e = e.
Proof.
  intros. apply lc_exp_id_qe with (k := 0); auto using expr_lc0. lia.
Qed.

(* ================================================================== *)
(* Freshness of substitutions                                         *)
(* ================================================================== *)

Lemma subst_qq_fresh : forall X R Q, X `notin` fv_qua Q -> subst_qq X R Q = Q.
Proof.
  induction Q; simpl; intros H.
  - reflexivity.
  - reflexivity.
  - simpl in *. destruct (X == a) as [e|e]. + exfalso. simpl in H; fsetdec. + reflexivity.
  - f_equal; [apply IHQ1|apply IHQ2]; simpl in H; fsetdec.
  - f_equal; [apply IHQ1|apply IHQ2]; simpl in H; fsetdec.
Qed.

Lemma subst_tt_fresh : forall T, (forall X U, X `notin` fv_typ T -> subst_tt X U T = T).
Proof.
  apply (typ_mut_ind
    (fun T => forall X U, X `notin` fv_typ T -> subst_tt X U T = T)
    (fun T => forall X U, X `notin` fv_qtyp T -> subst_tqt X U T = T)).
  - intros; reflexivity.
  - intros; reflexivity.
  - intros Y X U H. simpl in *. destruct (X == Y) as [e|e]; auto. exfalso. simpl in H; fsetdec.
  - intros q1 IH1 q2 IH2 X U H. simpl. f_equal.
    + apply IH1. simpl in H; fsetdec.
    + apply IH2. simpl in H; fsetdec.
  - intros T1 IH1 q IH2 X U H. simpl. f_equal.
    + apply IH1. simpl in H; fsetdec.
    + apply IH2. simpl in H; fsetdec.
  - intros Q q IH2 X U H. simpl. f_equal.
    apply IH2. simpl in H; fsetdec.
  - intros q1 IH1 q2 IH2 X U H. simpl. f_equal.
    + apply IH1. simpl in H; fsetdec.
    + apply IH2. simpl in H; fsetdec.
  - intros q1 IH1 q2 IH2 X U H. simpl. f_equal.
    + apply IH1. simpl in H; fsetdec.
    + apply IH2. simpl in H; fsetdec.
  - intros q IH X U H. simpl. f_equal. apply IH. simpl in H; fsetdec.
  - intros Q T IH X U H. simpl. f_equal. apply IH. simpl in H; fsetdec.
Qed.

Lemma subst_tqt_fresh : forall T X U, X `notin` fv_qtyp T -> subst_tqt X U T = T.
Proof.
  intros [Q T] X U H. simpl in *. f_equal. apply subst_tt_fresh. simpl in H; fsetdec.
Qed.

Lemma subst_qt_fresh : forall T, (forall X R, X `notin` fv_typ T -> subst_qt X R T = T).
Proof.
  apply (typ_mut_ind
    (fun T => forall X R, X `notin` fv_typ T -> subst_qt X R T = T)
    (fun T => forall X R, X `notin` fv_qtyp T -> subst_qqt X R T = T)).
  - intros; reflexivity.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros q1 IH1 q2 IH2 X R H. simpl. f_equal.
    + apply IH1. simpl in H; fsetdec.
    + apply IH2. simpl in H; fsetdec.
  - intros T1 IH1 q IH2 X R H. simpl. f_equal.
    + apply IH1. simpl in H; fsetdec.
    + apply IH2. simpl in H; fsetdec.
  - intros Q q IH2 X R H. simpl. f_equal.
    + apply subst_qq_fresh. simpl in H; fsetdec.
    + apply IH2. simpl in H; fsetdec.
  - intros q1 IH1 q2 IH2 X R H. simpl. f_equal.
    + apply IH1. simpl in H; fsetdec.
    + apply IH2. simpl in H; fsetdec.
  - intros q1 IH1 q2 IH2 X R H. simpl. f_equal.
    + apply IH1. simpl in H; fsetdec.
    + apply IH2. simpl in H; fsetdec.
  - intros q IH X R H. simpl. f_equal. apply IH. simpl in H; fsetdec.
  - intros Q T IH X R H. simpl. f_equal.
    + apply subst_qq_fresh. simpl in H; fsetdec.
    + apply IH. simpl in H; fsetdec.
Qed.

Lemma subst_qqt_fresh : forall T X R, X `notin` fv_qtyp T -> subst_qqt X R T = T.
Proof.
  intros [Q T] X R H. simpl in *. f_equal.
  + apply subst_qq_fresh. simpl in H; fsetdec.
  + apply subst_qt_fresh. simpl in H; fsetdec.
Qed.

Lemma subst_ee_fresh : forall x v e, x `notin` fv_exp e -> subst_ee x v e = e.
Proof.
  induction e; simpl; intros H.
  - reflexivity.
  - simpl in *. destruct (x == a) as [E|E]. + exfalso. simpl in H; fsetdec. + reflexivity.
  - f_equal. apply IHe. simpl in H; fsetdec.
  - f_equal. apply IHe1. simpl in H; fsetdec. apply IHe2. simpl in H; fsetdec.
  - f_equal. apply IHe. simpl in H; fsetdec.
  - f_equal. apply IHe. simpl in H; fsetdec.
  - f_equal. apply IHe. simpl in H; fsetdec.
  - f_equal. apply IHe. simpl in H; fsetdec.
  - f_equal. apply IHe1. simpl in H; fsetdec. apply IHe2. simpl in H; fsetdec.
  - f_equal. apply IHe. simpl in H; fsetdec.
  - f_equal. apply IHe. simpl in H; fsetdec.
  - f_equal. apply IHe1. simpl in H; fsetdec. apply IHe2. simpl in H; fsetdec. apply IHe3. simpl in H; fsetdec.
  - f_equal. apply IHe1. simpl in H; fsetdec. apply IHe2. simpl in H; fsetdec.
  - f_equal. apply IHe. simpl in H; fsetdec.
  - f_equal. apply IHe. simpl in H; fsetdec.
  - f_equal. apply IHe. simpl in H; fsetdec.
  - reflexivity.
  - f_equal. apply IHe. simpl in H; fsetdec.
  - f_equal. apply IHe1. simpl in H; fsetdec. apply IHe2. simpl in H; fsetdec.
  - f_equal. apply IHe. simpl in H; fsetdec.
  - f_equal. apply IHe. simpl in H; fsetdec.
Qed.

Lemma subst_te_fresh : forall X U e, X `notin` fv_exp e -> subst_te X U e = e.
Proof.
  induction e; simpl; intros H.
  - reflexivity.
  - reflexivity.
  - f_equal. apply subst_tqt_fresh. simpl in H; fsetdec.
    apply IHe. simpl in H; fsetdec.
  - f_equal. apply IHe1. simpl in H; fsetdec. apply IHe2. simpl in H; fsetdec.
  - f_equal. apply subst_tt_fresh. simpl in H; fsetdec.
    apply IHe. simpl in H; fsetdec.
  - f_equal. apply IHe. simpl in H; fsetdec. apply subst_tt_fresh. simpl in H; fsetdec.
  - f_equal. apply IHe. simpl in H; fsetdec.
  - f_equal. apply IHe. simpl in H; fsetdec.
  - f_equal. apply IHe1. simpl in H; fsetdec. apply IHe2. simpl in H; fsetdec.
  - f_equal. apply IHe. simpl in H; fsetdec.
  - f_equal. apply IHe. simpl in H; fsetdec.
  - f_equal. apply IHe1. simpl in H; fsetdec. apply IHe2. simpl in H; fsetdec. apply IHe3. simpl in H; fsetdec.
  - f_equal. apply IHe1. simpl in H; fsetdec. apply IHe2. simpl in H; fsetdec.
  - f_equal. apply IHe. simpl in H; fsetdec.
  - f_equal. apply IHe. simpl in H; fsetdec.
  - f_equal. apply IHe. simpl in H; fsetdec.
  - reflexivity.
  - f_equal. apply IHe. simpl in H; fsetdec.
  - f_equal. apply IHe1. simpl in H; fsetdec. apply IHe2. simpl in H; fsetdec.
  - f_equal. apply IHe. simpl in H; fsetdec.
  - f_equal. apply IHe. simpl in H; fsetdec.
Qed.

Lemma subst_qe_fresh : forall X R e, X `notin` fv_exp e -> subst_qe X R e = e.
Proof.
  induction e; simpl; intros H.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + apply subst_qq_fresh. simpl in H; fsetdec.
    + apply subst_qqt_fresh. simpl in H; fsetdec.
    + apply IHe. simpl in H; fsetdec.
  - f_equal. apply IHe1. simpl in H; fsetdec. apply IHe2. simpl in H; fsetdec.
  - f_equal.
    + apply subst_qq_fresh. simpl in H; fsetdec.
    + apply subst_qt_fresh. simpl in H; fsetdec.
    + apply IHe. simpl in H; fsetdec.
  - f_equal. apply IHe. simpl in H; fsetdec. apply subst_qt_fresh. simpl in H; fsetdec.
  - f_equal.
    + apply subst_qq_fresh. simpl in H; fsetdec.
    + apply subst_qq_fresh. simpl in H; fsetdec.
    + apply IHe. simpl in H; fsetdec.
  - f_equal. apply IHe. simpl in H; fsetdec. apply subst_qq_fresh. simpl in H; fsetdec.
  - f_equal. apply IHe1. simpl in H; fsetdec. apply IHe2. simpl in H; fsetdec.
  - f_equal. apply subst_qq_fresh. simpl in H; fsetdec. apply IHe. simpl in H; fsetdec.
  - f_equal. apply subst_qq_fresh. simpl in H; fsetdec. apply IHe. simpl in H; fsetdec.
  - f_equal. apply IHe1. simpl in H; fsetdec. apply IHe2. simpl in H; fsetdec. apply IHe3. simpl in H; fsetdec.
  - f_equal. apply subst_qq_fresh. simpl in H; fsetdec. apply IHe1. simpl in H; fsetdec. apply IHe2. simpl in H; fsetdec.
  - f_equal. apply IHe. simpl in H; fsetdec.
  - f_equal. apply IHe. simpl in H; fsetdec.
  - f_equal. apply subst_qq_fresh. simpl in H; fsetdec. apply IHe. simpl in H; fsetdec.
  - f_equal. apply subst_qq_fresh. simpl in H; fsetdec.
  - f_equal. apply IHe. simpl in H; fsetdec.
  - f_equal. apply IHe1. simpl in H; fsetdec. apply IHe2. simpl in H; fsetdec.
  - f_equal. apply subst_qq_fresh. simpl in H; fsetdec. apply IHe. simpl in H; fsetdec.
  - f_equal. apply subst_qq_fresh. simpl in H; fsetdec. apply IHe. simpl in H; fsetdec.
Qed.

(* ================================================================== *)
(* Elementary reduction lemmas for substitutions                      *)
(* ================================================================== *)

Lemma subst_qq_fvar_eq : forall X R, subst_qq X R (qua_fvar X) = R.
Proof.
  intros. simpl. destruct (X == X) as [e|e]; auto. exfalso. apply e. reflexivity.
Qed.

Lemma subst_qq_fvar_neq : forall X Y R, X <> Y -> subst_qq X R (qua_fvar Y) = qua_fvar Y.
Proof.
  intros. simpl. destruct (X == Y) as [e|e]; auto. exfalso. apply H. exact e.
Qed.

Lemma subst_tt_fvar_eq : forall X U, subst_tt X U (typ_fvar X) = U.
Proof.
  intros. simpl. destruct (X == X) as [e|e]; auto. exfalso. apply e. reflexivity.
Qed.

Lemma subst_tt_fvar_neq : forall X Y U, X <> Y -> subst_tt X U (typ_fvar Y) = typ_fvar Y.
Proof.
  intros. simpl. destruct (X == Y) as [e|e]; auto. exfalso. apply H. exact e.
Qed.

Lemma subst_ee_fvar_eq : forall x v, subst_ee x v (exp_fvar x) = v.
Proof.
  intros. simpl. destruct (x == x) as [e|e]; auto. exfalso. apply e. reflexivity.
Qed.

Lemma subst_ee_fvar_neq : forall x y v, x <> y -> subst_ee x v (exp_fvar y) = exp_fvar y.
Proof.
  intros. simpl. destruct (x == y) as [e|e]; auto. exfalso. apply H. exact e.
Qed.

(* ================================================================== *)
(* Self-substitution and opening                                      *)
(* ================================================================== *)

Lemma subst_qq_open_qq_self_gen : forall Q K X R,
  X `notin` fv_qua Q -> qual R ->
  subst_qq X R (open_qq_rec K (qua_fvar X) Q) = open_qq_rec K R Q.
Proof.
  induction Q; simpl; intros K X R H HR.
  - reflexivity.
  - destruct (K == n) as [e|e]; simpl.
    + apply subst_qq_fvar_eq.
    + reflexivity.
  - simpl in H. destruct (X == a) as [e|e].
    + exfalso. fsetdec.
    + reflexivity.
  - f_equal; [apply IHQ1|apply IHQ2]; simpl in H; fsetdec || auto.
  - f_equal; [apply IHQ1|apply IHQ2]; simpl in H; fsetdec || auto.
Qed.

Lemma subst_tt_open_tt_self_gen :
  forall T, (forall K X U, X `notin` fv_typ T -> type U ->
    subst_tt X U (open_tt_rec K (typ_fvar X) T) = open_tt_rec K U T).
Proof.
  apply (typ_mut_ind
    (fun T => forall K X U, X `notin` fv_typ T -> type U ->
       subst_tt X U (open_tt_rec K (typ_fvar X) T) = open_tt_rec K U T)
    (fun T => forall K X U, X `notin` fv_qtyp T -> type U ->
       subst_tqt X U (open_tqt_rec K (typ_fvar X) T) = open_tqt_rec K U T)).
  - intros; reflexivity.
  - intros n K X U H HU. simpl. destruct (K == n) as [e|e]; simpl.
    + apply subst_tt_fvar_eq.
    + reflexivity.
  - intros Y K X U H HU. simpl in H. simpl. destruct (X == Y) as [e|e].
    + exfalso. fsetdec.
    + reflexivity.
  - intros q1 IH1 q2 IH2 K X U H HU. simpl in H. simpl. f_equal.
    + apply IH1; simpl in H; fsetdec || auto.
    + apply IH2; simpl in H; fsetdec || auto.
  - intros T1 IH1 q IH2 K X U H HU. simpl in H. simpl. f_equal.
    + apply IH1; simpl in H; fsetdec || auto.
    + apply IH2; simpl in H; fsetdec || auto.
  - intros Q q IH2 K X U H HU. simpl in H. simpl. f_equal.
    apply IH2; simpl in H; fsetdec || auto.
  - intros q1 IH1 q2 IH2 K X U H HU. simpl in H. simpl. f_equal.
    + apply IH1; simpl in H; fsetdec || auto.
    + apply IH2; simpl in H; fsetdec || auto.
  - intros q1 IH1 q2 IH2 K X U H HU. simpl in H. simpl. f_equal.
    + apply IH1; simpl in H; fsetdec || auto.
    + apply IH2; simpl in H; fsetdec || auto.
  - intros q IH K X U H HU. simpl in H. simpl. f_equal.
    apply IH; simpl in H; fsetdec || auto.
  - intros Q T IH K X U H HU. simpl in H. simpl. f_equal.
    apply IH; simpl in H; fsetdec || auto.
Qed.

Lemma subst_tqt_open_tqt_self_gen : forall T K X U,
  X `notin` fv_qtyp T -> type U ->
  subst_tqt X U (open_tqt_rec K (typ_fvar X) T) = open_tqt_rec K U T.
Proof.
  intros [Q T] K X U H HU. simpl in *. f_equal.
  apply subst_tt_open_tt_self_gen; simpl in H; fsetdec || auto.
Qed.

Lemma subst_qt_open_qt_self_gen :
  forall T, (forall K X R, X `notin` fv_typ T -> qual R ->
    subst_qt X R (open_qt_rec K (qua_fvar X) T) = open_qt_rec K R T).
Proof.
  apply (typ_mut_ind
    (fun T => forall K X R, X `notin` fv_typ T -> qual R ->
       subst_qt X R (open_qt_rec K (qua_fvar X) T) = open_qt_rec K R T)
    (fun T => forall K X R, X `notin` fv_qtyp T -> qual R ->
       subst_qqt X R (open_qqt_rec K (qua_fvar X) T) = open_qqt_rec K R T)).
  - intros; reflexivity.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros q1 IH1 q2 IH2 K X R H HR. simpl in H. simpl. f_equal.
    + apply IH1; simpl in H; fsetdec || auto.
    + apply IH2; simpl in H; fsetdec || auto.
  - intros T1 IH1 q IH2 K X R H HR. simpl in H. simpl. f_equal.
    + apply IH1; simpl in H; fsetdec || auto.
    + apply IH2; simpl in H; fsetdec || auto.
  - intros Q q IH2 K X R H HR. simpl in H. simpl. f_equal.
    + apply subst_qq_open_qq_self_gen; simpl in H; fsetdec || auto.
    + apply IH2; simpl in H; fsetdec || auto.
  - intros q1 IH1 q2 IH2 K X R H HR. simpl in H. simpl. f_equal.
    + apply IH1; simpl in H; fsetdec || auto.
    + apply IH2; simpl in H; fsetdec || auto.
  - intros q1 IH1 q2 IH2 K X R H HR. simpl in H. simpl. f_equal.
    + apply IH1; simpl in H; fsetdec || auto.
    + apply IH2; simpl in H; fsetdec || auto.
  - intros q IH K X R H HR. simpl in H. simpl. f_equal.
    apply IH; simpl in H; fsetdec || auto.
  - intros Q T IH K X R H HR. simpl in H. simpl. f_equal.
    + apply subst_qq_open_qq_self_gen; simpl in H; fsetdec || auto.
    + apply IH; simpl in H; fsetdec || auto.
Qed.

Lemma subst_qqt_open_qqt_self_gen : forall T K X R,
  X `notin` fv_qtyp T -> qual R ->
  subst_qqt X R (open_qqt_rec K (qua_fvar X) T) = open_qqt_rec K R T.
Proof.
  intros [Q T] K X R H HR. simpl in *. f_equal.
  + apply subst_qq_open_qq_self_gen; simpl in H; fsetdec || auto.
  + apply subst_qt_open_qt_self_gen; simpl in H; fsetdec || auto.
Qed.

Lemma subst_ee_open_ee_self_gen : forall e K x v,
  x `notin` fv_exp e -> expr v ->
  subst_ee x v (open_ee_rec K (exp_fvar x) e) = open_ee_rec K v e.
Proof.
  induction e; simpl; intros K x v H Hv.
  - destruct (K == n) as [e|e]; simpl.
    + apply subst_ee_fvar_eq.
    + reflexivity.
  - simpl in H. destruct (x == a) as [e|e].
    + exfalso. fsetdec.
    + reflexivity.
  - f_equal. apply IHe with (K := S K) (x := x) (v := v).
    + simpl in H; fsetdec.
    + exact Hv.
  - f_equal.
    + apply IHe1 with (K := K) (x := x) (v := v); [simpl in H; fsetdec|exact Hv].
    + apply IHe2 with (K := K) (x := x) (v := v); [simpl in H; fsetdec|exact Hv].
  - f_equal. apply IHe with (K := S K) (x := x) (v := v).
    + simpl in H; fsetdec.
    + exact Hv.
  - f_equal. apply IHe with (K := K) (x := x) (v := v).
    + simpl in H; fsetdec.
    + exact Hv.
  - f_equal. apply IHe with (K := S K) (x := x) (v := v).
    + simpl in H; fsetdec.
    + exact Hv.
  - f_equal. apply IHe with (K := K) (x := x) (v := v).
    + simpl in H; fsetdec.
    + exact Hv.
  - f_equal.
    + apply IHe1 with (K := K) (x := x) (v := v); [simpl in H; fsetdec|exact Hv].
    + apply IHe2 with (K := S K) (x := x) (v := v); [simpl in H; fsetdec|exact Hv].
  - f_equal. apply IHe with (K := K) (x := x) (v := v).
    + simpl in H; fsetdec.
    + exact Hv.
  - f_equal. apply IHe with (K := K) (x := x) (v := v).
    + simpl in H; fsetdec.
    + exact Hv.
  - f_equal.
    + apply IHe1 with (K := K) (x := x) (v := v); [simpl in H; fsetdec|exact Hv].
    + apply IHe2 with (K := S K) (x := x) (v := v); [simpl in H; fsetdec|exact Hv].
    + apply IHe3 with (K := S K) (x := x) (v := v); [simpl in H; fsetdec|exact Hv].
  - f_equal.
    + apply IHe1 with (K := K) (x := x) (v := v); [simpl in H; fsetdec|exact Hv].
    + apply IHe2 with (K := K) (x := x) (v := v); [simpl in H; fsetdec|exact Hv].
  - f_equal. apply IHe with (K := K) (x := x) (v := v).
    + simpl in H; fsetdec.
    + exact Hv.
  - f_equal. apply IHe with (K := K) (x := x) (v := v).
    + simpl in H; fsetdec.
    + exact Hv.
  - f_equal. apply IHe with (K := K) (x := x) (v := v).
    + simpl in H; fsetdec.
    + exact Hv.
  - reflexivity.
  - f_equal. apply IHe with (K := K) (x := x) (v := v).
    + simpl in H; fsetdec.
    + exact Hv.
  - f_equal.
    + apply IHe1 with (K := K) (x := x) (v := v); [simpl in H; fsetdec|exact Hv].
    + apply IHe2 with (K := K) (x := x) (v := v); [simpl in H; fsetdec|exact Hv].
  - f_equal. apply IHe with (K := K) (x := x) (v := v).
    + simpl in H; fsetdec.
    + exact Hv.
  - f_equal. apply IHe with (K := K) (x := x) (v := v).
    + simpl in H; fsetdec.
    + exact Hv.
Qed.

Lemma subst_te_open_te_self_gen : forall e K X U,
  X `notin` fv_exp e -> type U ->
  subst_te X U (open_te_rec K (typ_fvar X) e) = open_te_rec K U e.
Proof.
  induction e; simpl; intros K X U H HU.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + apply subst_tqt_open_tqt_self_gen; [simpl in H; fsetdec|exact HU].
    + apply IHe with (K := S K) (X := X) (U := U); [simpl in H; fsetdec|exact HU].
  - f_equal.
    + apply IHe1 with (K := K); [simpl in H; fsetdec|exact HU].
    + apply IHe2 with (K := K); [simpl in H; fsetdec|exact HU].
  - f_equal.
    + apply subst_tt_open_tt_self_gen; [simpl in H; fsetdec|exact HU].
    + apply IHe with (K := S K); [simpl in H; fsetdec|exact HU].
  - f_equal.
    + apply IHe with (K := K); [simpl in H; fsetdec|exact HU].
    + apply subst_tt_open_tt_self_gen; [simpl in H; fsetdec|exact HU].
  - f_equal. apply IHe with (K := S K); [simpl in H; fsetdec|exact HU].
  - f_equal. apply IHe with (K := K); [simpl in H; fsetdec|exact HU].
  - f_equal.
    + apply IHe1 with (K := K); [simpl in H; fsetdec|exact HU].
    + apply IHe2 with (K := S K); [simpl in H; fsetdec|exact HU].
  - f_equal. apply IHe with (K := K); [simpl in H; fsetdec|exact HU].
  - f_equal. apply IHe with (K := K); [simpl in H; fsetdec|exact HU].
  - f_equal.
    + apply IHe1 with (K := K); [simpl in H; fsetdec|exact HU].
    + apply IHe2 with (K := S K); [simpl in H; fsetdec|exact HU].
    + apply IHe3 with (K := S K); [simpl in H; fsetdec|exact HU].
  - f_equal.
    + apply IHe1 with (K := K); [simpl in H; fsetdec|exact HU].
    + apply IHe2 with (K := K); [simpl in H; fsetdec|exact HU].
  - f_equal. apply IHe with (K := K); [simpl in H; fsetdec|exact HU].
  - f_equal. apply IHe with (K := K); [simpl in H; fsetdec|exact HU].
  - f_equal. apply IHe with (K := K); [simpl in H; fsetdec|exact HU].
  - reflexivity.
  - f_equal. apply IHe with (K := K); [simpl in H; fsetdec|exact HU].
  - f_equal.
    + apply IHe1 with (K := K); [simpl in H; fsetdec|exact HU].
    + apply IHe2 with (K := K); [simpl in H; fsetdec|exact HU].
  - f_equal. apply IHe with (K := K); [simpl in H; fsetdec|exact HU].
  - f_equal. apply IHe with (K := K); [simpl in H; fsetdec|exact HU].
Qed.

Lemma subst_qe_open_qe_self_gen : forall e K X R,
  X `notin` fv_exp e -> qual R ->
  subst_qe X R (open_qe_rec K (qua_fvar X) e) = open_qe_rec K R e.
Proof.
  induction e; simpl; intros K X R H HR.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + apply subst_qq_open_qq_self_gen; [simpl in H; fsetdec|exact HR].
    + apply subst_qqt_open_qqt_self_gen; [simpl in H; fsetdec|exact HR].
    + apply IHe with (K := S K); [simpl in H; fsetdec|exact HR].
  - f_equal.
    + apply IHe1 with (K := K); [simpl in H; fsetdec|exact HR].
    + apply IHe2 with (K := K); [simpl in H; fsetdec|exact HR].
  - f_equal.
    + apply subst_qq_open_qq_self_gen; [simpl in H; fsetdec|exact HR].
    + apply subst_qt_open_qt_self_gen; [simpl in H; fsetdec|exact HR].
    + apply IHe with (K := S K); [simpl in H; fsetdec|exact HR].
  - f_equal.
    + apply IHe with (K := K); [simpl in H; fsetdec|exact HR].
    + apply subst_qt_open_qt_self_gen; [simpl in H; fsetdec|exact HR].
  - f_equal.
    + apply subst_qq_open_qq_self_gen; [simpl in H; fsetdec|exact HR].
    + apply subst_qq_open_qq_self_gen; [simpl in H; fsetdec|exact HR].
    + apply IHe with (K := S K); [simpl in H; fsetdec|exact HR].
  - f_equal.
    + apply IHe with (K := K); [simpl in H; fsetdec|exact HR].
    + apply subst_qq_open_qq_self_gen; [simpl in H; fsetdec|exact HR].
  - f_equal.
    + apply IHe1 with (K := K); [simpl in H; fsetdec|exact HR].
    + apply IHe2 with (K := S K); [simpl in H; fsetdec|exact HR].
  - f_equal.
    + apply subst_qq_open_qq_self_gen; [simpl in H; fsetdec|exact HR].
    + apply IHe with (K := K); [simpl in H; fsetdec|exact HR].
  - f_equal.
    + apply subst_qq_open_qq_self_gen; [simpl in H; fsetdec|exact HR].
    + apply IHe with (K := K); [simpl in H; fsetdec|exact HR].
  - f_equal.
    + apply IHe1 with (K := K); [simpl in H; fsetdec|exact HR].
    + apply IHe2 with (K := S K); [simpl in H; fsetdec|exact HR].
    + apply IHe3 with (K := S K); [simpl in H; fsetdec|exact HR].
  - f_equal.
    + apply subst_qq_open_qq_self_gen; [simpl in H; fsetdec|exact HR].
    + apply IHe1 with (K := K); [simpl in H; fsetdec|exact HR].
    + apply IHe2 with (K := K); [simpl in H; fsetdec|exact HR].
  - f_equal. apply IHe with (K := K); [simpl in H; fsetdec|exact HR].
  - f_equal. apply IHe with (K := K); [simpl in H; fsetdec|exact HR].
  - f_equal.
    + apply subst_qq_open_qq_self_gen; [simpl in H; fsetdec|exact HR].
    + apply IHe with (K := K); [simpl in H; fsetdec|exact HR].
  - f_equal. apply subst_qq_open_qq_self_gen; [simpl in H; fsetdec|exact HR].
  - f_equal. apply IHe with (K := K); [simpl in H; fsetdec|exact HR].
  - f_equal.
    + apply IHe1 with (K := K); [simpl in H; fsetdec|exact HR].
    + apply IHe2 with (K := K); [simpl in H; fsetdec|exact HR].
  - f_equal.
    + apply subst_qq_open_qq_self_gen; [simpl in H; fsetdec|exact HR].
    + apply IHe with (K := K); [simpl in H; fsetdec|exact HR].
  - f_equal.
    + apply subst_qq_open_qq_self_gen; [simpl in H; fsetdec|exact HR].
    + apply IHe with (K := K); [simpl in H; fsetdec|exact HR].
Qed.

(* ================================================================== *)
(* Commutation of type substitution with type opening                 *)
(* ================================================================== *)

Lemma subst_tt_open_tt_rec :
  forall T, (forall K X U W, type U ->
    subst_tt X U (open_tt_rec K W T) = open_tt_rec K (subst_tt X U W) (subst_tt X U T)).
Proof.
  apply (typ_mut_ind
    (fun T => forall K X U W, type U ->
       subst_tt X U (open_tt_rec K W T) = open_tt_rec K (subst_tt X U W) (subst_tt X U T))
    (fun T => forall K X U W, type U ->
       subst_tqt X U (open_tqt_rec K W T) = open_tqt_rec K (subst_tt X U W) (subst_tqt X U T))).
  - intros; reflexivity.
  - intros n K X U W HU. simpl. destruct (K == n) as [e|e]; reflexivity.
  - intros Y K X U W HU. simpl. destruct (X == Y) as [e|e]; simpl.
    + symmetry. apply type_open_tt_id. exact HU.
    + reflexivity.
  - intros q1 IH1 q2 IH2 K X U W HU. simpl. f_equal.
    + apply IH1 with (K := K) (W := W); exact HU.
    + apply IH2 with (K := S K) (W := W); exact HU.
  - intros T1 IH1 q IH2 K X U W HU. simpl. f_equal.
    + apply IH1 with (K := K) (W := W); exact HU.
    + apply IH2 with (K := S K) (W := W); exact HU.
  - intros Q q IH2 K X U W HU. simpl. f_equal.
    apply IH2 with (K := S K) (W := W); exact HU.
  - intros q1 IH1 q2 IH2 K X U W HU. simpl. f_equal.
    + apply IH1 with (K := K) (W := W); exact HU.
    + apply IH2 with (K := K) (W := W); exact HU.
  - intros q1 IH1 q2 IH2 K X U W HU. simpl. f_equal.
    + apply IH1 with (K := K) (W := W); exact HU.
    + apply IH2 with (K := K) (W := W); exact HU.
  - intros q IH K X U W HU. simpl. f_equal.
    apply IH with (K := K) (W := W); exact HU.
  - intros Q T IH K X U W HU. simpl. f_equal.
    apply IH with (K := K) (W := W); exact HU.
Qed.

Lemma subst_tqt_open_tqt_rec : forall T K X U W, type U ->
  subst_tqt X U (open_tqt_rec K W T) = open_tqt_rec K (subst_tt X U W) (subst_tqt X U T).
Proof.
  intros [Q T] K X U W HU. simpl. f_equal.
  apply subst_tt_open_tt_rec with (K := K) (W := W); exact HU.
Qed.

Lemma subst_qq_open_qq_rec : forall Q K X R R0, qual R ->
  subst_qq X R (open_qq_rec K R0 Q) = open_qq_rec K (subst_qq X R R0) (subst_qq X R Q).
Proof.
  induction Q; simpl; intros K X R R0 HR.
  - reflexivity.
  - destruct (K == n) as [e|e]; simpl; reflexivity.
  - simpl. destruct (X == a) as [e|e]; simpl.
    + symmetry. apply qual_open_qq_id. exact HR.
    + reflexivity.
  - f_equal; [apply IHQ1|apply IHQ2]; exact HR.
  - f_equal; [apply IHQ1|apply IHQ2]; exact HR.
Qed.

Lemma subst_qt_open_qt_rec :
  forall T, (forall K X R R0, qual R ->
    subst_qt X R (open_qt_rec K R0 T) = open_qt_rec K (subst_qq X R R0) (subst_qt X R T)).
Proof.
  apply (typ_mut_ind
    (fun T => forall K X R R0, qual R ->
       subst_qt X R (open_qt_rec K R0 T) = open_qt_rec K (subst_qq X R R0) (subst_qt X R T))
    (fun T => forall K X R R0, qual R ->
       subst_qqt X R (open_qqt_rec K R0 T) = open_qqt_rec K (subst_qq X R R0) (subst_qqt X R T))).
  - intros; reflexivity.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros q1 IH1 q2 IH2 K X R R0 HR. simpl. f_equal.
    + apply IH1 with (K := K); exact HR.
    + apply IH2 with (K := S K); exact HR.
  - intros T1 IH1 q IH2 K X R R0 HR. simpl. f_equal.
    + apply IH1 with (K := K); exact HR.
    + apply IH2 with (K := S K); exact HR.
  - intros Q q IH2 K X R R0 HR. simpl. f_equal.
    + apply subst_qq_open_qq_rec with (K := K); exact HR.
    + apply IH2 with (K := S K); exact HR.
  - intros q1 IH1 q2 IH2 K X R R0 HR. simpl. f_equal.
    + apply IH1 with (K := K); exact HR.
    + apply IH2 with (K := K); exact HR.
  - intros q1 IH1 q2 IH2 K X R R0 HR. simpl. f_equal.
    + apply IH1 with (K := K); exact HR.
    + apply IH2 with (K := K); exact HR.
  - intros q IH K X R R0 HR. simpl. f_equal.
    apply IH with (K := K); exact HR.
  - intros Q T IH K X R R0 HR. simpl. f_equal.
    + apply subst_qq_open_qq_rec with (K := K); exact HR.
    + apply IH with (K := K); exact HR.
Qed.

Lemma subst_qqt_open_qqt_rec : forall T K X R R0, qual R ->
  subst_qqt X R (open_qqt_rec K R0 T) = open_qqt_rec K (subst_qq X R R0) (subst_qqt X R T).
Proof.
  intros [Q T] K X R R0 HR. simpl. f_equal.
  + apply subst_qq_open_qq_rec with (K := K); exact HR.
  + apply subst_qt_open_qt_rec with (K := K); exact HR.
Qed.

Lemma subst_qt_open_tt_rec :
  forall T, (forall K X R W, qual R -> X `notin` fv_typ W ->
    subst_qt X R (open_tt_rec K W T) = open_tt_rec K W (subst_qt X R T)).
Proof.
  apply (typ_mut_ind
    (fun T => forall K X R W, qual R -> X `notin` fv_typ W ->
       subst_qt X R (open_tt_rec K W T) = open_tt_rec K W (subst_qt X R T))
    (fun T => forall K X R W, qual R -> X `notin` fv_typ W ->
       subst_qqt X R (open_tqt_rec K W T) = open_tqt_rec K W (subst_qqt X R T))).
  - intros; reflexivity.
  - intros n K X R W HR HW. simpl. destruct (K == n) as [e|e]; simpl.
    + apply subst_qt_fresh. exact HW.
    + reflexivity.
  - intros; reflexivity.
  - intros q1 IH1 q2 IH2 K X R W HR HW. simpl. f_equal.
    + apply IH1 with (K := K) (W := W); [exact HR|simpl in HW; fsetdec].
    + apply IH2 with (K := S K) (W := W); [exact HR|simpl in HW; fsetdec].
  - intros T1 IH1 q IH2 K X R W HR HW. simpl. f_equal.
    + apply IH1 with (K := K) (W := W); [exact HR|simpl in HW; fsetdec].
    + apply IH2 with (K := S K) (W := W); [exact HR|simpl in HW; fsetdec].
  - intros Q q IH2 K X R W HR HW. simpl. f_equal.
    apply IH2 with (K := S K) (W := W); [exact HR|simpl in HW; fsetdec].
  - intros q1 IH1 q2 IH2 K X R W HR HW. simpl. f_equal.
    + apply IH1 with (K := K) (W := W); [exact HR|simpl in HW; fsetdec].
    + apply IH2 with (K := K) (W := W); [exact HR|simpl in HW; fsetdec].
  - intros q1 IH1 q2 IH2 K X R W HR HW. simpl. f_equal.
    + apply IH1 with (K := K) (W := W); [exact HR|simpl in HW; fsetdec].
    + apply IH2 with (K := K) (W := W); [exact HR|simpl in HW; fsetdec].
  - intros q IH K X R W HR HW. simpl. f_equal.
    apply IH with (K := K) (W := W); [exact HR|simpl in HW; fsetdec].
  - intros Q T IH K X R W HR HW. simpl. f_equal.
    apply IH with (K := K) (W := W); [exact HR|simpl in HW; fsetdec].
Qed.

Lemma subst_qqt_open_tqt_rec : forall T K X R W, qual R -> X `notin` fv_typ W ->
  subst_qqt X R (open_tqt_rec K W T) = open_tqt_rec K W (subst_qqt X R T).
Proof.
  intros [Q T] K X R W HR HW. simpl. f_equal.
  apply subst_qt_open_tt_rec with (K := K) (W := W); [exact HR|simpl in HW; exact HW].
Qed.

Lemma subst_tt_open_qt_rec :
  forall T, (forall K X U R, type U ->
    subst_tt X U (open_qt_rec K R T) = open_qt_rec K R (subst_tt X U T)).
Proof.
  apply (typ_mut_ind
    (fun T => forall K X U R, type U ->
       subst_tt X U (open_qt_rec K R T) = open_qt_rec K R (subst_tt X U T))
    (fun T => forall K X U R, type U ->
       subst_tqt X U (open_qqt_rec K R T) = open_qqt_rec K R (subst_tqt X U T))).
  - intros; reflexivity.
  - intros; reflexivity.
  - intros Y K X U R HU. simpl. destruct (X == Y) as [e|e]; simpl.
    + symmetry. apply type_open_qt_id. exact HU.
    + reflexivity.
  - intros q1 IH1 q2 IH2 K X U R HU. simpl. f_equal.
    + apply IH1 with (K := K); exact HU.
    + apply IH2 with (K := S K); exact HU.
  - intros T1 IH1 q IH2 K X U R HU. simpl. f_equal.
    + apply IH1 with (K := K); exact HU.
    + apply IH2 with (K := S K); exact HU.
  - intros Q q IH2 K X U R HU. simpl. f_equal.
    apply IH2 with (K := S K); exact HU.
  - intros q1 IH1 q2 IH2 K X U R HU. simpl. f_equal.
    + apply IH1 with (K := K); exact HU.
    + apply IH2 with (K := K); exact HU.
  - intros q1 IH1 q2 IH2 K X U R HU. simpl. f_equal.
    + apply IH1 with (K := K); exact HU.
    + apply IH2 with (K := K); exact HU.
  - intros q IH K X U R HU. simpl. f_equal.
    apply IH with (K := K); exact HU.
  - intros Q T IH K X U R HU. simpl. f_equal.
    apply IH with (K := K); exact HU.
Qed.

Lemma subst_tqt_open_qqt_rec : forall T K X U R, type U ->
  subst_tqt X U (open_qqt_rec K R T) = open_qqt_rec K R (subst_tqt X U T).
Proof.
  intros [Q T] K X U R HU. simpl. f_equal.
  apply subst_tt_open_qt_rec with (K := K); exact HU.
Qed.

(* ================================================================== *)
(* Commutation of substitution with opening in expressions            *)
(* ================================================================== *)

Lemma subst_ee_open_ee_rec : forall e K x v w,
  expr v -> x `notin` fv_exp w ->
  subst_ee x v (open_ee_rec K w e) = open_ee_rec K w (subst_ee x v e).
Proof.
  induction e; simpl; intros K x v w Hv Hw.
  - destruct (K == n) as [e|e]; simpl.
    + apply subst_ee_fresh. exact Hw.
    + reflexivity.
  - destruct (x == a) as [e|e]; simpl.
    + symmetry. apply expr_open_ee_id. exact Hv.
    + reflexivity.
  - f_equal. apply IHe with (K := S K) (x := x) (v := v) (w := w); auto.
  - f_equal.
    + apply IHe1 with (K := K) (x := x) (v := v) (w := w); auto.
    + apply IHe2 with (K := K) (x := x) (v := v) (w := w); auto.
  - f_equal. apply IHe with (K := S K) (x := x) (v := v) (w := w); auto.
  - f_equal. apply IHe with (K := K) (x := x) (v := v) (w := w); auto.
  - f_equal. apply IHe with (K := S K) (x := x) (v := v) (w := w); auto.
  - f_equal. apply IHe with (K := K) (x := x) (v := v) (w := w); auto.
  - f_equal.
    + apply IHe1 with (K := K) (x := x) (v := v) (w := w); auto.
    + apply IHe2 with (K := S K) (x := x) (v := v) (w := w); auto.
  - f_equal. apply IHe with (K := K) (x := x) (v := v) (w := w); auto.
  - f_equal. apply IHe with (K := K) (x := x) (v := v) (w := w); auto.
  - f_equal.
    + apply IHe1 with (K := K) (x := x) (v := v) (w := w); auto.
    + apply IHe2 with (K := S K) (x := x) (v := v) (w := w); auto.
    + apply IHe3 with (K := S K) (x := x) (v := v) (w := w); auto.
  - f_equal.
    + apply IHe1 with (K := K) (x := x) (v := v) (w := w); auto.
    + apply IHe2 with (K := K) (x := x) (v := v) (w := w); auto.
  - f_equal. apply IHe with (K := K) (x := x) (v := v) (w := w); auto.
  - f_equal. apply IHe with (K := K) (x := x) (v := v) (w := w); auto.
  - f_equal. apply IHe with (K := K) (x := x) (v := v) (w := w); auto.
  - reflexivity.
  - f_equal. apply IHe with (K := K) (x := x) (v := v) (w := w); auto.
  - f_equal.
    + apply IHe1 with (K := K) (x := x) (v := v) (w := w); auto.
    + apply IHe2 with (K := K) (x := x) (v := v) (w := w); auto.
  - f_equal. apply IHe with (K := K) (x := x) (v := v) (w := w); auto.
  - f_equal. apply IHe with (K := K) (x := x) (v := v) (w := w); auto.
Qed.

Lemma subst_ee_open_te_rec : forall e K x v U,
  expr v -> subst_ee x v (open_te_rec K U e) = open_te_rec K U (subst_ee x v e).
Proof.
  induction e; simpl; intros K x v U Hv.
  - reflexivity.
  - destruct (x == a) as [e|e]; simpl.
    + symmetry. apply expr_open_te_id. exact Hv.
    + reflexivity.
  - f_equal. apply IHe with (K := S K); auto.
  - f_equal.
    + apply IHe1 with (K := K); auto.
    + apply IHe2 with (K := K); auto.
  - f_equal. apply IHe with (K := S K); auto.
  - f_equal. apply IHe with (K := K); auto.
  - f_equal. apply IHe with (K := S K); auto.
  - f_equal. apply IHe with (K := K); auto.
  - f_equal.
    + apply IHe1 with (K := K); auto.
    + apply IHe2 with (K := S K); auto.
  - f_equal. apply IHe with (K := K); auto.
  - f_equal. apply IHe with (K := K); auto.
  - f_equal.
    + apply IHe1 with (K := K); auto.
    + apply IHe2 with (K := S K); auto.
    + apply IHe3 with (K := S K); auto.
  - f_equal.
    + apply IHe1 with (K := K); auto.
    + apply IHe2 with (K := K); auto.
  - f_equal. apply IHe with (K := K); auto.
  - f_equal. apply IHe with (K := K); auto.
  - f_equal. apply IHe with (K := K); auto.
  - reflexivity.
  - f_equal. apply IHe with (K := K); auto.
  - f_equal.
    + apply IHe1 with (K := K); auto.
    + apply IHe2 with (K := K); auto.
  - f_equal. apply IHe with (K := K); auto.
  - f_equal. apply IHe with (K := K); auto.
Qed.

Lemma subst_ee_open_qe_rec : forall e K x v R,
  expr v -> subst_ee x v (open_qe_rec K R e) = open_qe_rec K R (subst_ee x v e).
Proof.
  induction e; simpl; intros K x v R Hv.
  - reflexivity.
  - destruct (x == a) as [e|e]; simpl.
    + symmetry. apply expr_open_qe_id. exact Hv.
    + reflexivity.
  - f_equal. apply IHe with (K := S K); auto.
  - f_equal.
    + apply IHe1 with (K := K); auto.
    + apply IHe2 with (K := K); auto.
  - f_equal. apply IHe with (K := S K); auto.
  - f_equal. apply IHe with (K := K); auto.
  - f_equal. apply IHe with (K := S K); auto.
  - f_equal. apply IHe with (K := K); auto.
  - f_equal.
    + apply IHe1 with (K := K); auto.
    + apply IHe2 with (K := S K); auto.
  - f_equal. apply IHe with (K := K); auto.
  - f_equal. apply IHe with (K := K); auto.
  - f_equal.
    + apply IHe1 with (K := K); auto.
    + apply IHe2 with (K := S K); auto.
    + apply IHe3 with (K := S K); auto.
  - f_equal.
    + apply IHe1 with (K := K); auto.
    + apply IHe2 with (K := K); auto.
  - f_equal. apply IHe with (K := K); auto.
  - f_equal. apply IHe with (K := K); auto.
  - f_equal. apply IHe with (K := K); auto.
  - reflexivity.
  - f_equal. apply IHe with (K := K); auto.
  - f_equal.
    + apply IHe1 with (K := K); auto.
    + apply IHe2 with (K := K); auto.
  - f_equal. apply IHe with (K := K); auto.
  - f_equal. apply IHe with (K := K); auto.
Qed.

Lemma subst_te_open_ee_rec : forall e K X U w,
  type U -> X `notin` fv_exp w ->
  subst_te X U (open_ee_rec K w e) = open_ee_rec K w (subst_te X U e).
Proof.
  induction e; simpl; intros K X U w HU Hw.
  - destruct (K == n) as [e|e]; simpl.
    + apply subst_te_fresh. exact Hw.
    + reflexivity.
  - reflexivity.
  - f_equal. apply IHe with (K := S K); auto.
  - f_equal.
    + apply IHe1 with (K := K); auto.
    + apply IHe2 with (K := K); auto.
  - f_equal. apply IHe with (K := S K); auto.
  - f_equal. apply IHe with (K := K); auto.
  - f_equal. apply IHe with (K := S K); auto.
  - f_equal. apply IHe with (K := K); auto.
  - f_equal.
    + apply IHe1 with (K := K); auto.
    + apply IHe2 with (K := S K); auto.
  - f_equal. apply IHe with (K := K); auto.
  - f_equal. apply IHe with (K := K); auto.
  - f_equal.
    + apply IHe1 with (K := K); auto.
    + apply IHe2 with (K := S K); auto.
    + apply IHe3 with (K := S K); auto.
  - f_equal.
    + apply IHe1 with (K := K); auto.
    + apply IHe2 with (K := K); auto.
  - f_equal. apply IHe with (K := K); auto.
  - f_equal. apply IHe with (K := K); auto.
  - f_equal. apply IHe with (K := K); auto.
  - reflexivity.
  - f_equal. apply IHe with (K := K); auto.
  - f_equal.
    + apply IHe1 with (K := K); auto.
    + apply IHe2 with (K := K); auto.
  - f_equal. apply IHe with (K := K); auto.
  - f_equal. apply IHe with (K := K); auto.
Qed.

Lemma subst_te_open_te_rec : forall e K X U W,
  type U ->
  subst_te X U (open_te_rec K W e) = open_te_rec K (subst_tt X U W) (subst_te X U e).
Proof.
  induction e; simpl; intros K X U W HU.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + apply subst_tqt_open_tqt_rec with (K := K) (W := W). exact HU.
    + apply IHe with (K := S K); exact HU.
  - f_equal.
    + apply IHe1 with (K := K); exact HU.
    + apply IHe2 with (K := K); exact HU.
  - f_equal.
    + apply subst_tt_open_tt_rec with (K := K) (W := W). exact HU.
    + apply IHe with (K := S K); exact HU.
  - f_equal.
    + apply IHe with (K := K); exact HU.
    + apply subst_tt_open_tt_rec with (K := K) (W := W). exact HU.
  - f_equal. apply IHe with (K := S K); exact HU.
  - f_equal. apply IHe with (K := K); exact HU.
  - f_equal.
    + apply IHe1 with (K := K); exact HU.
    + apply IHe2 with (K := S K); exact HU.
  - f_equal. apply IHe with (K := K); exact HU.
  - f_equal. apply IHe with (K := K); exact HU.
  - f_equal.
    + apply IHe1 with (K := K); exact HU.
    + apply IHe2 with (K := S K); exact HU.
    + apply IHe3 with (K := S K); exact HU.
  - f_equal.
    + apply IHe1 with (K := K); exact HU.
    + apply IHe2 with (K := K); exact HU.
  - f_equal. apply IHe with (K := K); exact HU.
  - f_equal. apply IHe with (K := K); exact HU.
  - f_equal. apply IHe with (K := K); exact HU.
  - reflexivity.
  - f_equal. apply IHe with (K := K); exact HU.
  - f_equal.
    + apply IHe1 with (K := K); exact HU.
    + apply IHe2 with (K := K); exact HU.
  - f_equal. apply IHe with (K := K); exact HU.
  - f_equal. apply IHe with (K := K); exact HU.
Qed.

Lemma subst_te_open_qe_rec : forall e K X U R,
  type U ->
  subst_te X U (open_qe_rec K R e) = open_qe_rec K R (subst_te X U e).
Proof.
  induction e; simpl; intros K X U R HU.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + apply subst_tqt_open_qqt_rec with (K := K) (R := R). exact HU.
    + apply IHe with (K := S K); exact HU.
  - f_equal.
    + apply IHe1 with (K := K); exact HU.
    + apply IHe2 with (K := K); exact HU.
  - f_equal.
    + apply subst_tt_open_qt_rec with (K := K) (R := R). exact HU.
    + apply IHe with (K := S K); exact HU.
  - f_equal.
    + apply IHe with (K := K); exact HU.
    + apply subst_tt_open_qt_rec with (K := K) (R := R). exact HU.
  - f_equal. apply IHe with (K := S K); exact HU.
  - f_equal. apply IHe with (K := K); exact HU.
  - f_equal.
    + apply IHe1 with (K := K); exact HU.
    + apply IHe2 with (K := S K); exact HU.
  - f_equal. apply IHe with (K := K); exact HU.
  - f_equal. apply IHe with (K := K); exact HU.
  - f_equal.
    + apply IHe1 with (K := K); exact HU.
    + apply IHe2 with (K := S K); exact HU.
    + apply IHe3 with (K := S K); exact HU.
  - f_equal.
    + apply IHe1 with (K := K); exact HU.
    + apply IHe2 with (K := K); exact HU.
  - f_equal. apply IHe with (K := K); exact HU.
  - f_equal. apply IHe with (K := K); exact HU.
  - f_equal. apply IHe with (K := K); exact HU.
  - reflexivity.
  - f_equal. apply IHe with (K := K); exact HU.
  - f_equal.
    + apply IHe1 with (K := K); exact HU.
    + apply IHe2 with (K := K); exact HU.
  - f_equal. apply IHe with (K := K); exact HU.
  - f_equal. apply IHe with (K := K); exact HU.
Qed.

Lemma subst_qe_open_ee_rec : forall e K X R w,
  qual R -> X `notin` fv_exp w ->
  subst_qe X R (open_ee_rec K w e) = open_ee_rec K w (subst_qe X R e).
Proof.
  induction e; simpl; intros K X R w HR Hw.
  - destruct (K == n) as [e|e]; simpl.
    + apply subst_qe_fresh. exact Hw.
    + reflexivity.
  - reflexivity.
  - f_equal. apply IHe with (K := S K); auto.
  - f_equal.
    + apply IHe1 with (K := K); auto.
    + apply IHe2 with (K := K); auto.
  - f_equal. apply IHe with (K := S K); auto.
  - f_equal. apply IHe with (K := K); auto.
  - f_equal. apply IHe with (K := S K); auto.
  - f_equal. apply IHe with (K := K); auto.
  - f_equal.
    + apply IHe1 with (K := K); auto.
    + apply IHe2 with (K := S K); auto.
  - f_equal. apply IHe with (K := K); auto.
  - f_equal. apply IHe with (K := K); auto.
  - f_equal.
    + apply IHe1 with (K := K); auto.
    + apply IHe2 with (K := S K); auto.
    + apply IHe3 with (K := S K); auto.
  - f_equal.
    + apply IHe1 with (K := K); auto.
    + apply IHe2 with (K := K); auto.
  - f_equal. apply IHe with (K := K); auto.
  - f_equal. apply IHe with (K := K); auto.
  - f_equal. apply IHe with (K := K); auto.
  - reflexivity.
  - f_equal. apply IHe with (K := K); auto.
  - f_equal.
    + apply IHe1 with (K := K); auto.
    + apply IHe2 with (K := K); auto.
  - f_equal. apply IHe with (K := K); auto.
  - f_equal. apply IHe with (K := K); auto.
Qed.

Lemma subst_qe_open_te_rec : forall e K X R U,
  qual R -> X `notin` fv_typ U ->
  subst_qe X R (open_te_rec K U e) = open_te_rec K U (subst_qe X R e).
Proof.
  induction e; simpl; intros K X R U HR HU.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + apply subst_qqt_open_tqt_rec with (K := K) (W := U).
      * exact HR.
      * simpl in HU; exact HU.
    + apply IHe with (K := S K); auto.
  - f_equal.
    + apply IHe1 with (K := K); auto.
    + apply IHe2 with (K := K); auto.
  - f_equal.
    + apply subst_qt_open_tt_rec with (K := K) (W := U).
      * exact HR.
      * simpl in HU; exact HU.
    + apply IHe with (K := S K); auto.
  - f_equal.
    + apply IHe with (K := K); auto.
    + apply subst_qt_open_tt_rec with (K := K) (W := U).
      * exact HR.
      * simpl in HU; exact HU.
  - f_equal. apply IHe with (K := S K); auto.
  - f_equal. apply IHe with (K := K); auto.
  - f_equal.
    + apply IHe1 with (K := K); auto.
    + apply IHe2 with (K := S K); auto.
  - f_equal. apply IHe with (K := K); auto.
  - f_equal. apply IHe with (K := K); auto.
  - f_equal.
    + apply IHe1 with (K := K); auto.
    + apply IHe2 with (K := S K); auto.
    + apply IHe3 with (K := S K); auto.
  - f_equal.
    + apply IHe1 with (K := K); auto.
    + apply IHe2 with (K := K); auto.
  - f_equal. apply IHe with (K := K); auto.
  - f_equal. apply IHe with (K := K); auto.
  - f_equal. apply IHe with (K := K); auto.
  - reflexivity.
  - f_equal. apply IHe with (K := K); auto.
  - f_equal.
    + apply IHe1 with (K := K); auto.
    + apply IHe2 with (K := K); auto.
  - f_equal. apply IHe with (K := K); auto.
  - f_equal. apply IHe with (K := K); auto.
Qed.

Lemma subst_qe_open_qe_rec : forall e K X R R0,
  qual R ->
  subst_qe X R (open_qe_rec K R0 e) = open_qe_rec K (subst_qq X R R0) (subst_qe X R e).
Proof.
  induction e; simpl; intros K X R R0 HR.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + apply subst_qq_open_qq_rec with (K := K); exact HR.
    + apply subst_qqt_open_qqt_rec with (K := K); exact HR.
    + apply IHe with (K := S K); exact HR.
  - f_equal.
    + apply IHe1 with (K := K); exact HR.
    + apply IHe2 with (K := K); exact HR.
  - f_equal.
    + apply subst_qq_open_qq_rec with (K := K); exact HR.
    + apply subst_qt_open_qt_rec with (K := K); exact HR.
    + apply IHe with (K := S K); exact HR.
  - f_equal.
    + apply IHe with (K := K); exact HR.
    + apply subst_qt_open_qt_rec with (K := K); exact HR.
  - f_equal.
    + apply subst_qq_open_qq_rec with (K := K); exact HR.
    + apply subst_qq_open_qq_rec with (K := K); exact HR.
    + apply IHe with (K := S K); exact HR.
  - f_equal.
    + apply IHe with (K := K); exact HR.
    + apply subst_qq_open_qq_rec with (K := K); exact HR.
  - f_equal.
    + apply IHe1 with (K := K); exact HR.
    + apply IHe2 with (K := S K); exact HR.
  - f_equal.
    + apply subst_qq_open_qq_rec with (K := K); exact HR.
    + apply IHe with (K := K); exact HR.
  - f_equal.
    + apply subst_qq_open_qq_rec with (K := K); exact HR.
    + apply IHe with (K := K); exact HR.
  - f_equal.
    + apply IHe1 with (K := K); exact HR.
    + apply IHe2 with (K := S K); exact HR.
    + apply IHe3 with (K := S K); exact HR.
  - f_equal.
    + apply subst_qq_open_qq_rec with (K := K); exact HR.
    + apply IHe1 with (K := K); exact HR.
    + apply IHe2 with (K := K); exact HR.
  - f_equal. apply IHe with (K := K); exact HR.
  - f_equal. apply IHe with (K := K); exact HR.
  - f_equal.
    + apply subst_qq_open_qq_rec with (K := K); exact HR.
    + apply IHe with (K := K); exact HR.
  - f_equal. apply subst_qq_open_qq_rec with (K := K); exact HR.
  - f_equal. apply IHe with (K := K); exact HR.
  - f_equal.
    + apply IHe1 with (K := K); exact HR.
    + apply IHe2 with (K := K); exact HR.
  - f_equal.
    + apply subst_qq_open_qq_rec with (K := K); exact HR.
    + apply IHe with (K := K); exact HR.
  - f_equal.
    + apply subst_qq_open_qq_rec with (K := K); exact HR.
    + apply IHe with (K := K); exact HR.
Qed.

(* ================================================================== *)
(* Basic well-formedness lemmas                                       *)
(* ================================================================== *)

Lemma wf_env_uniq : forall E, wf_env E -> uniq E.
Proof.
  intros E H. induction H.
  - apply uniq_nil.
  - apply uniq_push; auto.
  - apply uniq_push; auto.
  - apply uniq_push; auto.
Qed.

Definition wf_binding (E : env) (b : binding) : Prop :=
  match b with
  | bind_sub T => wf_typ E T
  | bind_typ T => wf_qtyp E T
  | bind_qua Q => wf_qua E Q
  end.


(* ================================================================== *)
(* Environment relation: preservation of bound type/qualifier vars    *)
(* ================================================================== *)

Definition env_rel (E E' : env) : Prop :=
  (forall x U, binds x (bind_sub U) E -> exists U', binds x (bind_sub U') E') /\
  (forall x Q, binds x (bind_qua Q) E -> exists Q', binds x (bind_qua Q') E').

Lemma env_rel_refl : forall E, env_rel E E.
Proof.
  intros E. split; intros; eauto.
Qed.

Lemma binds_not_middle : forall (A : Type) (z : atom) (p : A) (x : atom) (b b0 : A) (F G : list (atom * A)),
  binds z p (F ++ (x, b) :: G) -> p <> b -> binds z p (F ++ G).
Proof.
  intros A z p x b b0 F G H Hne.
  apply binds_app_iff in H. destruct H as [H|H].
  - apply binds_app_2. exact H.
  - apply binds_cons_iff in H. destruct H as [[Heq Hp]|H].
    + exfalso. apply Hne. inversion Heq. exact Hp.
    + apply binds_app_3. exact H.
Qed.

Lemma env_rel_ctx : forall E E' E1 E2,
  env_rel E E' -> env_rel (E1 ++ E ++ E2) (E1 ++ E' ++ E2).
Proof.
  intros E E' E1 E2 [Hsub Hqua]. split.
  - intros x U Hb. apply binds_app_iff in Hb. destruct Hb as [Hb|Hb].
    + exists U. apply binds_app_2. exact Hb.
    + apply binds_app_iff in Hb. destruct Hb as [Hb|Hb].
      * destruct (Hsub x U Hb) as [U' HU']. exists U'.
        assert (H1 : binds x (bind_sub U') (E' ++ E2)) by (apply binds_app_2; exact HU').
        apply binds_app_3 with (E := E1) in H1. exact H1.
      * exists U. apply binds_app_3 with (E := E1).
        apply binds_app_3 with (E := E'). exact Hb.
  - intros x Q Hb. apply binds_app_iff in Hb. destruct Hb as [Hb|Hb].
    + exists Q. apply binds_app_2. exact Hb.
    + apply binds_app_iff in Hb. destruct Hb as [Hb|Hb].
      * destruct (Hqua x Q Hb) as [Q' HQ']. exists Q'.
        assert (H1 : binds x (bind_qua Q') (E' ++ E2)) by (apply binds_app_2; exact HQ').
        apply binds_app_3 with (E := E1) in H1. exact H1.
      * exists Q. apply binds_app_3 with (E := E1).
        apply binds_app_3 with (E := E'). exact Hb.
Qed.

Lemma env_rel_weaken : forall E E1 E2, env_rel E (E1 ++ E ++ E2).
Proof.
  intros E E1 E2. split.
  - intros x T Hb. exists T.
    assert (H1 : binds x (bind_sub T) (E ++ E2)) by (apply binds_app_2; exact Hb).
    apply binds_app_3 with (E := E1) in H1. exact H1.
  - intros x Q Hb. exists Q.
    assert (H1 : binds x (bind_qua Q) (E ++ E2)) by (apply binds_app_2; exact Hb).
    apply binds_app_3 with (E := E1) in H1. exact H1.
Qed.

Lemma env_rel_cons : forall E E' x b,
  env_rel E E' -> env_rel (x ~ b ++ E) (x ~ b ++ E').
Proof.
  intros E E' x b [Hsub Hqua]. split.
  - intros y T Hb. apply binds_cons_iff in Hb. destruct Hb as [[Heq Hp]|Hb].
    + subst. exists T. apply binds_cons_2; auto.
    + destruct (Hsub y T Hb) as [T' HT']. exists T'. apply binds_cons_3. exact HT'.
  - intros y Q Hb. apply binds_cons_iff in Hb. destruct Hb as [[Heq Hp]|Hb].
    + subst. exists Q. apply binds_cons_2; auto.
    + destruct (Hqua y Q Hb) as [Q' HQ']. exists Q'. apply binds_cons_3. exact HQ'.
Qed.

Lemma env_rel_remove_typ : forall E1 E2 x U,
  env_rel (E1 ++ (x, bind_typ U) :: E2) (E1 ++ E2).
Proof.
  split.
  - intros y V Hb. apply binds_app_iff in Hb. destruct Hb as [Hb|Hb].
    + exists V. apply binds_app_2. exact Hb.
    + apply binds_cons_iff in Hb. destruct Hb as [[Heq Hp]|Hb].
      * exfalso. inversion Heq. inversion Hp.
      * exists V. apply binds_app_3 with (E := E1). exact Hb.
  - intros y Q Hb. apply binds_app_iff in Hb. destruct Hb as [Hb|Hb].
    + exists Q. apply binds_app_2. exact Hb.
    + apply binds_cons_iff in Hb. destruct Hb as [[Heq Hp]|Hb].
      * exfalso. inversion Heq. inversion Hp.
      * exists Q. apply binds_app_3 with (E := E1). exact Hb.
Qed.

Lemma env_rel_bind_sub_change : forall E1 E2 x U1 U2,
  env_rel (E1 ++ (x, bind_sub U1) :: E2) (E1 ++ (x, bind_sub U2) :: E2).
Proof.
  split.
  - intros y V Hb. apply binds_app_iff in Hb. destruct Hb as [Hb|Hb].
    + exists V. apply binds_app_2. exact Hb.
    + apply binds_cons_iff in Hb. destruct Hb as [[Heq Hp]|Hb].
      * exists U2. inversion Heq. inversion Hp. subst.
        apply binds_app_3 with (E := E1). apply binds_cons_2; auto.
      * exists V. apply binds_app_3 with (E := E1).
        apply binds_cons_3. exact Hb.
  - intros y Q Hb. apply binds_app_iff in Hb. destruct Hb as [Hb|Hb].
    + exists Q. apply binds_app_2. exact Hb.
    + apply binds_cons_iff in Hb. destruct Hb as [[Heq Hp]|Hb].
      * exfalso. inversion Heq. inversion Hp.
      * exists Q. apply binds_app_3 with (E := E1).
        apply binds_cons_3. exact Hb.
Qed.

Lemma env_rel_bind_qua_change : forall E1 E2 x Q1 Q2,
  env_rel (E1 ++ (x, bind_qua Q1) :: E2) (E1 ++ (x, bind_qua Q2) :: E2).
Proof.
  split.
  - intros y V Hb. apply binds_app_iff in Hb. destruct Hb as [Hb|Hb].
    + exists V. apply binds_app_2. exact Hb.
    + apply binds_cons_iff in Hb. destruct Hb as [[Heq Hp]|Hb].
      * exfalso. inversion Heq. inversion Hp.
      * exists V. apply binds_app_3 with (E := E1).
        apply binds_cons_3. exact Hb.
  - intros y Q Hb. apply binds_app_iff in Hb. destruct Hb as [Hb|Hb].
    + exists Q. apply binds_app_2. exact Hb.
    + apply binds_cons_iff in Hb. destruct Hb as [[Heq Hp]|Hb].
      * exists Q2. inversion Heq. inversion Hp. subst.
        apply binds_app_3 with (E := E1). apply binds_cons_2; auto.
      * exists Q. apply binds_app_3 with (E := E1).
        apply binds_cons_3. exact Hb.
Qed.

Lemma wf_qua_env_rel : forall E E' Q, env_rel E E' -> wf_qua E Q -> wf_qua E' Q.
Proof.
  intros E E' Q Hrel H.
  induction H as [E0 b | R E0 X Hb | E0 Q1 Q2 H1 IH1 H2 IH2 | E0 Q1 Q2 H1 IH1 H2 IH2].
  - constructor.
  - destruct Hrel as [Hsub Hqua].
    destruct (Hqua X R Hb) as [R' HR']. apply (wf_qua_fvar R'). exact HR'.
  - constructor; auto.
  - constructor; auto.
Qed.

Scheme wf_mut_ind := Induction for wf_typ Sort Prop
  with wfq_mut_ind := Induction for wf_qtyp Sort Prop.

Lemma wf_typ_env_rel : forall E T, wf_typ E T ->
  forall E', env_rel E E' -> wf_typ E' T.
Proof.
  intros E T H Eout Hrelout.
  refine (wf_mut_ind
    (fun E T _ => forall E', env_rel E E' -> wf_typ E' T)
    (fun E T _ => forall E', env_rel E E' -> wf_qtyp E' T)
    _ _ _ _ _ _ _ _ E T H Eout Hrelout).
  - intros E0 E' Hrel. constructor.
  - intros U E0 X b E' Hrel. destruct Hrel as [Hsub Hqua].
    destruct (Hsub X U b) as [U' HU']. apply (wf_typ_var U'). exact HU'.
  - intros E0 T1 T2 w IHw w0 IH0 E' Hrel. constructor.
    + apply IHw. exact Hrel.
    + apply IH0. exact Hrel.
  - intros L E0 T1 T2 w IHw w0 IH0 E' Hrel. apply (wf_typ_all L).
    + apply IHw. exact Hrel.
    + intros X HX. apply (IH0 X HX) with (E' := X ~ bind_sub T1 ++ E').
      apply env_rel_cons. exact Hrel.
  - intros L E0 T1 T2 w w0 IH0 E' Hrel. apply (wf_typ_qall L).
    + apply wf_qua_env_rel with (E := E0); auto.
    + intros X HX. apply (IH0 X HX) with (E' := X ~ bind_qua T1 ++ E').
      apply env_rel_cons. exact Hrel.
  - intros E0 T1 T2 w IHw w0 IH0 E' Hrel. constructor.
    + apply IHw. exact Hrel.
    + apply IH0. exact Hrel.
  - intros E0 T1 T2 w IHw w0 IH0 E' Hrel. constructor.
    + apply IHw. exact Hrel.
    + apply IH0. exact Hrel.
  - intros E0 Q T1 w w0 IHw E' Hrel. simpl. apply wf_qtyp_qtyp.
    + apply wf_qua_env_rel with (E := E0); auto.
    + apply IHw. exact Hrel.
Qed.

Lemma wf_qtyp_env_rel : forall E T, wf_qtyp E T ->
  forall E', env_rel E E' -> wf_qtyp E' T.
Proof.
  intros E0 Tq H E1 Hrel. destruct Tq as [Q0 T0].
  inversion H; subst.
  split.
  - apply wf_qua_env_rel with (E := E0); auto.
  - apply wf_typ_env_rel with (E := E0); auto.
Qed.

Lemma wf_typ_weaken_env : forall E T, wf_typ E T -> forall E1 E2, wf_typ (E1 ++ E ++ E2) T.
Proof.
  intros E T H E1 E2. apply wf_typ_env_rel with (E := E); auto using env_rel_weaken.
Qed.

Lemma wf_qtyp_weaken_env : forall E T, wf_qtyp E T -> forall E1 E2, wf_qtyp (E1 ++ E ++ E2) T.
Proof.
  intros E T H E1 E2. apply wf_qtyp_env_rel with (E := E); auto using env_rel_weaken.
Qed.

Lemma wf_qua_weaken_env : forall E Q, wf_qua E Q -> forall E1 E2, wf_qua (E1 ++ E ++ E2) Q.
Proof.
  intros E Q H E1 E2. apply wf_qua_env_rel with (E := E); auto using env_rel_weaken.
Qed.

Lemma wf_binding_weaken : forall E b, wf_binding E b ->
  forall E1 E2, wf_binding (E1 ++ E ++ E2) b.
Proof.
  intros E b H. destruct b.
  - simpl in *. intros. apply wf_typ_weaken_env with (E := E); auto.
  - simpl in *. intros. apply wf_qtyp_weaken_env with (E := E); auto.
  - simpl in *. intros. apply wf_qua_weaken_env with (E := E); auto.
Qed.

Lemma wf_env_binds : forall E, wf_env E -> forall x b, binds x b E -> wf_binding E b.
Proof.
  intros E. induction E as [| [y b0] E' IHE'].
  - intros Hwf x b Hb. inversion Hb.
  - intros Hwf x b Hb. destruct b0 as [T0|T0|Q0]; inversion Hwf; subst.
    + (* bind_sub *) apply binds_cons_iff in Hb. destruct Hb as [[Heq Hpb]|Hb].
      * subst. simpl.
        assert (Hx : wf_typ ((y ~ bind_sub T0) ++ E' ++ nil) T0) by
          (apply wf_typ_weaken_env with (E := E'); auto).
        simpl in Hx. rewrite app_nil_r in Hx. exact Hx.
      * assert (Hx : wf_binding ((y ~ bind_sub T0) ++ E' ++ nil) b) by
          (apply wf_binding_weaken; apply IHE' with (x := x) (b := b); auto).
        simpl in Hx. rewrite app_nil_r in Hx. exact Hx.
    + (* bind_typ *) apply binds_cons_iff in Hb. destruct Hb as [[Heq Hpb]|Hb].
      * subst. simpl.
        assert (Hx : wf_qtyp ((y ~ bind_typ T0) ++ E' ++ nil) T0) by
          (apply wf_qtyp_weaken_env with (E := E'); auto).
        simpl in Hx. rewrite app_nil_r in Hx. exact Hx.
      * assert (Hx : wf_binding ((y ~ bind_typ T0) ++ E' ++ nil) b) by
          (apply wf_binding_weaken; apply IHE' with (x := x) (b := b); auto).
        simpl in Hx. rewrite app_nil_r in Hx. exact Hx.
    + (* bind_qua *) apply binds_cons_iff in Hb. destruct Hb as [[Heq Hpb]|Hb].
      * subst. simpl.
        assert (Hx : wf_qua ((y ~ bind_qua Q0) ++ E' ++ nil) Q0) by
          (apply wf_qua_weaken_env with (E := E'); auto).
        simpl in Hx. rewrite app_nil_r in Hx. exact Hx.
      * assert (Hx : wf_binding ((y ~ bind_qua Q0) ++ E' ++ nil) b) by
          (apply wf_binding_weaken; apply IHE' with (x := x) (b := b); auto).
        simpl in Hx. rewrite app_nil_r in Hx. exact Hx.
Qed.

Lemma wf_env_remove_typ : forall E1 E2 x U,
  wf_env (E1 ++ (x, bind_typ U) :: E2) -> wf_env (E1 ++ E2).
Proof.
  intros E1. induction E1 as [| [y b0] E1' IH]; intros E2 x U Hwf.
  - simpl in Hwf. inversion Hwf; subst. assumption.
  - simpl in Hwf. destruct b0 as [T0|T0|Q0].
    + inversion Hwf; subst. constructor.
      * apply (IH E2 x U). assumption.
      * apply wf_typ_env_rel with (E := E1' ++ (x, bind_typ U) :: E2).
        -- assumption.
        -- apply env_rel_remove_typ.
      * rewrite dom_app. rewrite dom_app in H4. simpl in H4. simpl. fsetdec.
    + inversion Hwf; subst. constructor.
      * apply (IH E2 x U). assumption.
      * apply wf_qtyp_env_rel with (E := E1' ++ (x, bind_typ U) :: E2).
        -- assumption.
        -- apply env_rel_remove_typ.
      * rewrite dom_app. rewrite dom_app in H4. simpl in H4. simpl. fsetdec.
    + inversion Hwf; subst. constructor.
      * apply (IH E2 x U). assumption.
      * apply wf_qua_env_rel with (E := E1' ++ (x, bind_typ U) :: E2).
        -- apply env_rel_remove_typ.
        -- assumption.
      * rewrite dom_app. rewrite dom_app in H4. simpl in H4. simpl. fsetdec.
Qed.

Lemma subqual_wf_env : forall E Q R, subqual E Q R -> wf_env E.
Proof.
  intros E Q R H. induction H; eauto.
Qed.

Lemma subqual_wf : forall E Q R, subqual E Q R -> wf_qua E Q /\ wf_qua E R.
Proof.
  intros E Q R H.
  induction H as
    [ E0 Q0 Hwf HQ
    | E0 Q0 Hwf HQ
    | E0 Q' Q0 R0 b H1 IH1 Hc H2 IH2
    | E0 Q' Q0 R0 b H1 IH1 Hc H2 IH2
    | E0 b1 b2 Hwf Hord
    | E0 X Hwf HQ
    | R0 E0 Q0 X Hb H1 IH1
    | E0 R1 R2 Q0 H1 IH1 HR2
    | E0 R1 R2 Q0 HR1 H1 IH1
    | E0 R1 R2 Q0 H1 IH1 H2 IH2
    | E0 R1 R2 Q0 H1 IH1 HR2
    | E0 R1 R2 Q0 HR1 H1 IH1
    | E0 R1 R2 Q0 H1 IH1 H2 IH2 ].
  - split; [exact HQ|constructor].
  - split; [constructor|exact HQ].
  - destruct IH1 as [HQ1 HQ2]. destruct IH2 as [_ HR]. split; auto.
  - destruct IH1 as [HQ' HR]. destruct IH2 as [HQ _]. split; auto.
  - split; constructor.
  - split; [exact HQ|exact HQ].
  - destruct IH1 as [HR0 HQ]. split.
    + apply (wf_qua_fvar R0). exact Hb.
    + exact HQ.
  - destruct IH1 as [HQ HR1]. split.
    + exact HQ.
    + constructor; auto.
  - destruct IH1 as [HQ HR2]. split.
    + exact HQ.
    + constructor; auto.
  - destruct IH1 as [HR1 HQ1]. destruct IH2 as [HR2 HQ2]. split.
    + constructor; auto.
    + exact HQ1.
  - destruct IH1 as [HR1 HQ]. split.
    + constructor; auto.
    + exact HQ.
  - destruct IH1 as [HR2 HQ]. split.
    + constructor; auto.
    + exact HQ.
  - destruct IH1 as [HQ HR1]. destruct IH2 as [_ HR2]. split.
    + exact HQ.
    + constructor; auto.
Qed.

Lemma subqual_refl : forall E Q, wf_env E -> wf_qua E Q -> subqual E Q Q.
Proof.
  intros E Q Hwf HQ.
  induction HQ as [E0 b | R E0 X Hb | E0 Q1 Q2 H1 IH1 H2 IH2 | E0 Q1 Q2 H1 IH1 H2 IH2].
  - apply subqual_lift_elem. exact Hwf. exact (Fsub.ExtendedBase.Lattice.reflexive b).
  - apply subqual_refl_qvar. exact Hwf. apply (wf_qua_fvar R). exact Hb.
  - apply subqual_meet_intro.
    + apply subqual_meet_eliml.
      * apply IH1. exact Hwf.
      * exact H2.
    + apply subqual_meet_elimr.
      * exact H1.
      * apply IH2. exact Hwf.
  - apply subqual_join_elim.
    + apply subqual_join_inl.
      * apply IH1. exact Hwf.
      * exact H2.
    + apply subqual_join_inr.
      * exact H1.
      * apply IH2. exact Hwf.
Qed.

Lemma subqual_top_l : forall E R Q S,
  subqual E R S -> subqual E Q R -> R = qua_base top -> subqual E Q S.
Proof.
  intros E R Q S H2. revert Q.
  induction H2 as
    [ E0 Q0 Hwf HQ
    | E0 Q0 Hwf HQ
    | E0 Q' Q0 R0 b Ha IHa Hc Hc2 IHc2
    | E0 Q' Q0 R0 b Ha IHa Hc Hc2 IHc2
    | E0 b1 b2 Hwf Hord
    | E0 X Hwf HQ
    | R0 E0 Q0 X Hb Ha IHa
    | E0 R1 R2 Q0 Ha IHa HR2
    | E0 R1 R2 Q0 HR1 Ha IHa
    | E0 R1 R2 Q0 Ha IHa Hb IHb
    | E0 R1 R2 Q0 Ha IHa HR2
    | E0 R1 R2 Q0 HR1 Ha IHa
    | E0 R1 R2 Q0 Ha IHa Hb IHb ]; intros Q1 H1 HR.
  - subst. exact H1.
  - exfalso. injection HR as Hbt. symmetry in Hbt.
    exact (Fsub.ExtendedBase.Lattice.nontrivial (A := B) Hbt).
  - apply subqual_eval_elim with (Q' := Q') (b := b).
    + apply IHa with (Q := Q1); auto.
    + exact Hc.
    + exact Hc2.
  - apply subqual_eval_intro with (Q' := Q') (b := b).
    + exact Ha.
    + exact Hc.
    + apply IHc2 with (Q := Q1); auto.
  - apply subqual_eval_elim with (Q' := qua_base b1) (b := b1).
    + exact H1.
    + reflexivity.
    + apply subqual_lift_elem; auto.
  - discriminate HR.
  - discriminate HR.
  - apply subqual_join_inl. apply IHa with (Q := Q1); auto. exact HR2.
  - apply subqual_join_inr. exact HR1. apply IHa with (Q := Q1); auto.
  - discriminate HR.
  - discriminate HR.
  - discriminate HR.
  - apply subqual_meet_intro.
    + apply IHa with (Q := Q1); auto.
    + apply IHb with (Q := Q1); auto.
Qed.

Lemma subqual_trans : forall E Q R S,
  subqual E Q R -> subqual E R S -> subqual E Q S.
Proof.
  intros E Q R S H1. revert S.
  induction H1 as
    [ E0 Q0 Hwf HQ
    | E0 Q0 Hwf HQ
    | E0 Q' Q0 R0 b Ha IHa Hc Hc2 IHc2
    | E0 Q' Q0 R0 b Ha IHa Hc Hc2 IHc2
    | E0 b1 b2 Hwf Hord
    | E0 X Hwf HQ
    | R0 E0 Q0 X Hb Ha IHa
    | E0 R1 R2 Q0 Ha IHa HR2
    | E0 R1 R2 Q0 HR1 Ha IHa
    | E0 R1 R2 Q0 Ha IHa Hb IHb
    | E0 R1 R2 Q0 Ha IHa HR2
    | E0 R1 R2 Q0 HR1 Ha IHa
    | E0 R1 R2 Q0 Ha IHa Hb IHb ]; intros S H2.
  - apply (subqual_top_l E0 (qua_base top) Q0 S); auto.
    apply subqual_top; auto.
  - apply subqual_bot.
    + exact (subqual_wf_env E0 Q0 S H2).
    + destruct (subqual_wf E0 Q0 S H2) as [_ HS]. exact HS.
  - apply subqual_eval_elim with (Q' := Q') (b := b).
    + exact Ha.
    + exact Hc.
    + apply IHc2. exact H2.
  - apply subqual_eval_intro with (Q' := Q') (b := b).
    + apply IHa. exact H2.
    + exact Hc.
    + exact Hc2.
  - apply subqual_eval_elim with (Q' := qua_base b2) (b := b2).
    + apply subqual_lift_elem; auto.
    + reflexivity.
    + exact H2.
  - exact H2.
  - apply subqual_trans_qvar with (R := R0).
    + exact Hb.
    + apply IHa. exact H2.
  - (* join_inl : hard *)
    remember (qua_join R1 R2) as RJ eqn:HRJ.
    revert HRJ. induction H2 as
      [ E1 Qx Hwf HQx
      | E1 Qx Hwf HQx
      | E1 Q' Qx R' b2 Ha2 IHa2 Hc2 Hc3 IHc3
      | E1 Q' Qx R' b2 Ha2 IHa2 Hc2 Hc3 IHc3
      | E1 c1 c2 Hwf Hord
      | E1 X2 Hwf HQx
      | R2' E1 Qx X2 Hb2 Ha2 IHa2
      | E1 R1' R2' Qx Ha2 IHa2 HR2'
      | E1 R1' R2' Qx HR1' Ha2 IHa2
      | E1 R1' R2' Qx Ha2 IHa2 Hb2 IHb2
      | E1 R1' R2' Qx Ha2 IHa2 HR2'
      | E1 R1' R2' Qx HR1' Ha2 IHa2
      | E1 R1' R2' Qx Ha2 IHa2 Hb2 IHb2 ]; intros HRJ.
    + apply subqual_top; auto.
      destruct (subqual_wf E1 Q0 R1 Ha) as [HQ1 _]. exact HQ1.
    + discriminate HRJ.
    + apply subqual_eval_elim with (Q' := Q') (b := b2).
      * apply IHa2; auto.
      * exact Hc2.
      * exact Hc3.
    + apply subqual_eval_intro with (Q' := Q') (b := b2).
      * exact Ha2.
      * exact Hc2.
      * apply IHc3; auto.
    + discriminate HRJ.
    + discriminate HRJ.
    + discriminate HRJ.
    + apply subqual_join_inl.
      * apply IHa2; auto.
      * exact HR2'.
    + apply subqual_join_inr.
      * exact HR1'.
      * apply IHa2; auto.
    + injection HRJ as ER1 ER2. subst.
      apply (IHa Qx). exact Ha2.
    + discriminate HRJ.
    + discriminate HRJ.
    + apply subqual_meet_intro.
      * apply IHa2; auto.
      * apply IHb2; auto.
  - (* join_inr : hard *)
    remember (qua_join R1 R2) as RJ eqn:HRJ.
    revert HRJ. induction H2 as
      [ E1 Qx Hwf HQx
      | E1 Qx Hwf HQx
      | E1 Q' Qx R' b2 Ha2 IHa2 Hc2 Hc3 IHc3
      | E1 Q' Qx R' b2 Ha2 IHa2 Hc2 Hc3 IHc3
      | E1 c1 c2 Hwf Hord
      | E1 X2 Hwf HQx
      | R2' E1 Qx X2 Hb2 Ha2 IHa2
      | E1 R1' R2' Qx Ha2 IHa2 HR2'
      | E1 R1' R2' Qx HR1' Ha2 IHa2
      | E1 R1' R2' Qx Ha2 IHa2 Hb2 IHb2
      | E1 R1' R2' Qx Ha2 IHa2 HR2'
      | E1 R1' R2' Qx HR1' Ha2 IHa2
      | E1 R1' R2' Qx Ha2 IHa2 Hb2 IHb2 ]; intros HRJ.
    + apply subqual_top; auto.
      destruct (subqual_wf E1 Q0 R2 Ha) as [HQ1 _]. exact HQ1.
    + discriminate HRJ.
    + apply subqual_eval_elim with (Q' := Q') (b := b2).
      * apply IHa2; auto.
      * exact Hc2.
      * exact Hc3.
    + apply subqual_eval_intro with (Q' := Q') (b := b2).
      * exact Ha2.
      * exact Hc2.
      * apply IHc3; auto.
    + discriminate HRJ.
    + discriminate HRJ.
    + discriminate HRJ.
    + apply subqual_join_inl.
      * apply IHa2; auto.
      * exact HR2'.
    + apply subqual_join_inr.
      * exact HR1'.
      * apply IHa2; auto.
    + injection HRJ as ER1 ER2. subst.
      apply (IHa Qx). exact Hb2.
    + discriminate HRJ.
    + discriminate HRJ.
    + apply subqual_meet_intro.
      * apply IHa2; auto.
      * apply IHb2; auto.
  - apply subqual_join_elim.
    + apply IHa. exact H2.
    + apply IHb. exact H2.
  - apply subqual_meet_eliml.
    + apply IHa. exact H2.
    + exact HR2.
  - apply subqual_meet_elimr.
    + exact HR1.
    + apply IHa. exact H2.
  - (* meet_intro : hard *)
    remember (qua_meet R1 R2) as RJ eqn:HRJ.
    revert HRJ. induction H2 as
      [ E1 Qx Hwf HQx
      | E1 Qx Hwf HQx
      | E1 Q' Qx R' b2 Ha2 IHa2 Hc2 Hc3 IHc3
      | E1 Q' Qx R' b2 Ha2 IHa2 Hc2 Hc3 IHc3
      | E1 c1 c2 Hwf Hord
      | E1 X2 Hwf HQx
      | R2' E1 Qx X2 Hb2 Ha2 IHa2
      | E1 R1' R2' Qx Ha2 IHa2 HR2'
      | E1 R1' R2' Qx HR1' Ha2 IHa2
      | E1 R1' R2' Qx Ha2 IHa2 Hb2 IHb2
      | E1 R1' R2' Qx Ha2 IHa2 HR2'
      | E1 R1' R2' Qx HR1' Ha2 IHa2
      | E1 R1' R2' Qx Ha2 IHa2 Hb2 IHb2 ]; intros HRJ.
    + apply subqual_top; auto.
      destruct (subqual_wf E1 Q0 R1 Ha) as [HQ1 _]. exact HQ1.
    + discriminate HRJ.
    + apply subqual_eval_elim with (Q' := Q') (b := b2).
      * apply IHa2; auto.
      * exact Hc2.
      * exact Hc3.
    + apply subqual_eval_intro with (Q' := Q') (b := b2).
      * exact Ha2.
      * exact Hc2.
      * apply IHc3; auto.
    + discriminate HRJ.
    + discriminate HRJ.
    + discriminate HRJ.
    + apply subqual_join_inl.
      * apply IHa2; auto.
      * exact HR2'.
    + apply subqual_join_inr.
      * exact HR1'.
      * apply IHa2; auto.
    + discriminate HRJ.
    + injection HRJ as ER1 ER2. subst. apply (IHa Qx). exact Ha2.
    + injection HRJ as ER1 ER2. subst. apply (IHb Qx). exact Ha2.
    + apply subqual_meet_intro.
      * apply IHa2; auto.
      * apply IHb2; auto.
Qed.

Scheme sub_mut_ind := Induction for sub Sort Prop
  with subq_mut_ind := Induction for subqtype Sort Prop.

Lemma sub_wf : forall E S T, sub E S T ->
  wf_env E /\ wf_typ E S /\ wf_typ E T.
Proof.
  intros E S T H.
  refine (sub_mut_ind
    (fun E S T _ => wf_env E /\ wf_typ E S /\ wf_typ E T)
    (fun E S T _ => wf_env E /\ wf_qtyp E S /\ wf_qtyp E T)
    _ _ _ _ _ _ _ _ _ E S T H).
  - intros E0 S0 Hwf HwS. split; [exact Hwf|split; [exact HwS|constructor]].
  - intros E0 X Hwf HwX. split; [exact Hwf|split; assumption].
  - intros U E0 T0 X Hb Hs IH. destruct IH as [Hwe [HwU HwT]]. split; [exact Hwe|split].
    + apply (wf_typ_var U). exact Hb.
    + exact HwT.
  - intros E0 S1 S2 T1 T2 s1 IH1 s2 IH2.
    destruct IH1 as [Hwe [HT1 HS1]]. destruct IH2 as [_ [HS2 HT2]].
    split; [exact Hwe|split]; constructor; auto.
  - intros L E0 S1 S2 T1 T2 s IH s0 IH0.
    destruct IH as [Hwe [HT1 HS1]]. split; [exact Hwe|split].
    + apply (wf_typ_all L). exact HS1.
      intros X HX. destruct (IH0 X HX) as [_ [HS2 _]].
      apply wf_qtyp_env_rel with (E := X ~ bind_sub T1 ++ E0).
      * exact HS2.
      * exact (env_rel_bind_sub_change nil E0 X T1 S1).
    + apply (wf_typ_all L). exact HT1.
      intros X HX. destruct (IH0 X HX) as [_ [_ HT2]]. exact HT2.
  - intros L E0 S1 S2 T1 T2 s s0 IH0.
    destruct (subqual_wf E0 T1 S1 s) as [HT1 HS1].
    split; [apply (subqual_wf_env E0 T1 S1 s)|split].
    + apply (wf_typ_qall L). exact HS1.
      intros X HX. destruct (IH0 X HX) as [_ [HS2 _]].
      apply wf_qtyp_env_rel with (E := X ~ bind_qua T1 ++ E0).
      * exact HS2.
      * exact (env_rel_bind_qua_change nil E0 X T1 S1).
    + apply (wf_typ_qall L). exact HT1.
      intros X HX. destruct (IH0 X HX) as [_ [_ HT2]]. exact HT2.
  - intros E0 S1 S2 T1 T2 s1 IH1 s2 IH2.
    destruct IH1 as [Hwe [HS1 HT1]]. destruct IH2 as [_ [HS2 HT2]].
    split; [exact Hwe|split]; constructor; auto.
  - intros E0 S1 S2 T1 T2 s1 IH1 s2 IH2.
    destruct IH1 as [Hwe [HS1 HT1]]. destruct IH2 as [_ [HS2 HT2]].
    split; [exact Hwe|split]; constructor; auto.
  - intros E0 Q1 T1 Q2 T2 s s0 IH.
    destruct (subqual_wf E0 Q1 Q2 s) as [HQ1 HQ2].
    destruct IH as [Hwe [HT1 HT2]]. split; [exact Hwe|split]; apply wf_qtyp_qtyp; auto.
Qed.

Lemma subqtype_wf : forall E S T, subqtype E S T ->
  wf_env E /\ wf_qtyp E S /\ wf_qtyp E T.
Proof.
  intros E S T H. destruct S as [Q1 T1]. destruct T as [Q2 T2].
  destruct H as [E0 Q1' T1' Q2' T2' Hs Hsub].
  destruct (subqual_wf E0 Q1' Q2' Hs) as [HQ1 HQ2].
  destruct (sub_wf E0 T1' T2' Hsub) as [Hwe [HT1 HT2]].
  split; [exact Hwe|split]; apply wf_qtyp_qtyp; auto.
Qed.

Lemma sub_wf_env : forall E S T, sub E S T -> wf_env E.
Proof. intros. apply (sub_wf E S T); assumption. Qed.

Lemma subqtype_wf_env : forall E S T, subqtype E S T -> wf_env E.
Proof. intros. apply (subqtype_wf E S T); assumption. Qed.

Lemma sub_refl : forall E T, wf_env E -> wf_typ E T -> sub E T T.
Proof.
  intros E T HwfT Hwf.
  refine (wf_mut_ind
    (fun E T _ => wf_env E -> wf_typ E T -> sub E T T)
    (fun E T _ => wf_env E -> wf_qtyp E T -> subqtype E T T)
    _ _ _ _ _ _ _ _ E T Hwf HwfT Hwf).
  - intros E0 H HX. apply sub_top; auto.
  - intros U E0 X Hb H HX. apply sub_refl_tvar; auto.
  - intros E0 T1 T2 w1 IH1 w2 IH2 H HX. apply sub_arrow.
    + apply IH1; auto.
    + apply IH2; auto.
  - intros L E0 T1 T2 w1 IH1 w0 IH0 H HX. apply (sub_all (union L (dom E0))).
    + apply IH1; auto.
    + intros X HX2. apply (IH0 X).
      * simpl in HX2; fsetdec.
      * apply wf_env_sub; auto.
      * apply w0. simpl in HX2; fsetdec.
  - intros L E0 Q T0 wq w0 IH0 H HX. apply (sub_qall (union L (dom E0))).
    + apply subqual_refl; auto.
    + intros X HX2. apply (IH0 X).
      * simpl in HX2; fsetdec.
      * apply wf_env_qua; auto.
      * apply w0. simpl in HX2; fsetdec.
  - intros E0 T1 T2 w1 IH1 w2 IH2 H HX. apply sub_sum.
    + apply IH1; auto.
    + apply IH2; auto.
  - intros E0 T1 T2 w1 IH1 w2 IH2 H HX. apply sub_pair.
    + apply IH1; auto.
    + apply IH2; auto.
  - intros E0 Q T0 wq wT IH H HX. apply sub_qtyp_qtyp.
    + apply subqual_refl; auto.
    + apply IH; auto.
Qed.

Lemma subqtype_refl : forall E T, wf_env E -> wf_qtyp E T -> subqtype E T T.
Proof.
  intros E [Q T] Hwf Hq. simpl in Hq. destruct Hq as [HQ HT].
  apply sub_qtyp_qtyp.
  - apply subqual_refl; auto.
  - apply sub_refl; auto.
Qed.

Lemma wf_typ_remove_typ : forall E1 E2 x U T,
  wf_typ (E1 ++ (x, bind_typ U) :: E2) T -> wf_typ (E1 ++ E2) T.
Proof.
  intros. apply wf_typ_env_rel with (E := E1 ++ (x, bind_typ U) :: E2); auto.
  apply env_rel_remove_typ.
Qed.

Lemma wf_qtyp_remove_typ : forall E1 E2 x U T,
  wf_qtyp (E1 ++ (x, bind_typ U) :: E2) T -> wf_qtyp (E1 ++ E2) T.
Proof.
  intros. apply wf_qtyp_env_rel with (E := E1 ++ (x, bind_typ U) :: E2); auto.
  apply env_rel_remove_typ.
Qed.

Lemma wf_qua_remove_typ : forall E1 E2 x U Q,
  wf_qua (E1 ++ (x, bind_typ U) :: E2) Q -> wf_qua (E1 ++ E2) Q.
Proof.
  intros. apply wf_qua_env_rel with (E := E1 ++ (x, bind_typ U) :: E2); auto.
  apply env_rel_remove_typ.
Qed.

Lemma wf_qua_qual : forall E Q, wf_qua E Q -> qual Q.
Proof.
  intros E Q H. induction H.
  - constructor.
  - constructor.
  - constructor; auto.
  - constructor; auto.
Qed.

Lemma wf_typ_type : forall E T, wf_typ E T -> type T.
Proof.
  intros E T H.
  refine (wf_mut_ind
    (fun E T _ => type T)
    (fun E T _ => qtype T)
    _ _ _ _ _ _ _ _ E T H).
  - constructor.
  - intros U E0 X b. constructor.
  - intros E0 T1 T2 w1 IH1 w2 IH2. constructor; auto.
  - intros L E0 T1 T2 w1 IH1 w0 IH0. apply (type_all L).
    + exact IH1.
    + intros X HX. apply (IH0 X HX).
  - intros L E0 Q T0 wq w0 IH0. apply (type_qall L).
    + apply (wf_qua_qual E0 Q); exact wq.
    + intros X HX. apply (IH0 X HX).
  - intros E0 T1 T2 w1 IH1 w2 IH2. constructor; auto.
  - intros E0 T1 T2 w1 IH1 w2 IH2. constructor; auto.
  - intros E0 Q T0 wq wT IH. apply (wf_qua_qual E0 Q) in wq. constructor; auto.
Qed.

Lemma wf_qtyp_qtype : forall E T, wf_qtyp E T -> qtype T.
Proof.
  intros E T H. destruct T as [Q T0]. inversion H; subst.
  constructor.
  - apply (wf_qua_qual E Q). assumption.
  - apply (wf_typ_type E T0). assumption.
Qed.

Lemma qual_subst_qq : forall Q X R, qual Q -> qual R -> qual (subst_qq X R Q).
Proof.
  intros Q X R HQ HR.
  induction HQ as [b | Y | Q1 Q2 H1 IH1 H2 IH2 | Q1 Q2 H1 IH1 H2 IH2]; simpl.
  - constructor.
  - destruct (X == Y) as [e|e]; [exact HR|constructor].
  - constructor; auto.
  - constructor; auto.
Qed.

Lemma type_subst_tt : forall T, type T -> forall X U, type U -> type (subst_tt X U T).
Proof.
  intros T Ht.
  refine (type_mut_ind
    (fun T _ => forall X U, type U -> type (subst_tt X U T))
    (fun T _ => forall X U, type U -> qtype (subst_tqt X U T))
    _ _ _ _ _ _ _ _ T Ht).
  - intros X U HU. simpl. constructor.
  - intros Y X U HU. simpl. destruct (X == Y) as [e|e]; [exact HU|constructor].
  - intros T1 T2 q1 IH1 q2 IH2 X U HU. simpl. constructor.
    + apply IH1; auto.
    + apply IH2; auto.
  - intros L T1 T2 t IHt q IHq X U HU. simpl. apply (type_all (union L (singleton X))).
    + apply IHt; auto.
    + intros Y HY. simpl in HY.
      assert (HXY : X <> Y) by fsetdec.
      assert (Hc : subst_tqt X U (open_tqt T2 Y) = open_tqt (subst_tqt X U T2) Y).
      { unfold open_tqt. rewrite (subst_tqt_open_tqt_rec T2 0 X U (typ_fvar Y) HU).
        f_equal. apply subst_tt_fvar_neq. exact HXY. }
      rewrite <- Hc. apply (IHq Y); [fsetdec|exact HU].
  - intros L Q T0 q qbody IHbody X U HU. simpl. apply (type_qall L).
    + exact q.
    + intros Y HY.
      assert (Hc : subst_tqt X U (open_qqt T0 Y) = open_qqt (subst_tqt X U T0) Y).
      { unfold open_qqt. apply subst_tqt_open_qqt_rec. exact HU. }
      rewrite <- Hc. apply (IHbody Y); [exact HY|exact HU].
  - intros T1 T2 q1 IH1 q2 IH2 X U HU. simpl. constructor; auto.
  - intros T1 T2 q1 IH1 q2 IH2 X U HU. simpl. constructor; auto.
  - intros Q T0 q t IHt X U HU. simpl. apply qtype_qtyp; auto.
Qed.

Lemma type_subst_qt : forall T, type T -> forall X R, qual R -> type (subst_qt X R T).
Proof.
  intros T Ht.
  refine (type_mut_ind
    (fun T _ => forall X R, qual R -> type (subst_qt X R T))
    (fun T _ => forall X R, qual R -> qtype (subst_qqt X R T))
    _ _ _ _ _ _ _ _ T Ht).
  - intros X R HR. simpl. constructor.
  - intros Y X R HR. simpl. constructor.
  - intros T1 T2 q1 IH1 q2 IH2 X R HR. simpl. constructor; auto.
  - intros L T1 T2 t IHt q IHq X R HR. simpl. apply (type_all (union L (singleton X))).
    + apply IHt; auto.
    + intros Y HY. simpl in HY.
      assert (HXY : X <> Y) by fsetdec.
      assert (Hc : subst_qqt X R (open_tqt T2 Y) = open_tqt (subst_qqt X R T2) Y).
      { unfold open_tqt. apply subst_qqt_open_tqt_rec; [exact HR | simpl; fsetdec]. }
      rewrite <- Hc. apply (IHq Y); [fsetdec|exact HR].
  - intros L Q T0 q qbody IHbody X R HR. simpl. apply (type_qall (union L (singleton X))).
    + apply qual_subst_qq; auto.
    + intros Y HY. simpl in HY.
      assert (HXY : X <> Y) by fsetdec.
      assert (Hc : subst_qqt X R (open_qqt T0 Y) = open_qqt (subst_qqt X R T0) Y).
      { unfold open_qqt. rewrite (subst_qqt_open_qqt_rec T0 0 X R (qua_fvar Y) HR).
        f_equal. apply subst_qq_fvar_neq. exact HXY. }
      rewrite <- Hc. apply (IHbody Y); [fsetdec|exact HR].
  - intros T1 T2 q1 IH1 q2 IH2 X R HR. simpl. constructor; auto.
  - intros T1 T2 q1 IH1 q2 IH2 X R HR. simpl. constructor; auto.
  - intros Q T0 q t IHt X R HR. simpl. apply qtype_qtyp.
    + apply qual_subst_qq; auto.
    + apply IHt; auto.
Qed.


(* ================================================================== *)
(* Weakening of subtyping under environment inclusion                 *)
(* ================================================================== *)

Definition env_incl (E E' : env) : Prop :=
  forall x b, binds x b E -> binds x b E'.

Lemma env_incl_refl : forall E, env_incl E E.
Proof. intros E x b H. exact H. Qed.

Lemma env_incl_cons : forall E E' x b,
  env_incl E E' -> env_incl (x ~ b ++ E) (x ~ b ++ E').
Proof.
  intros E E' x b H. intros y c Hy.
  apply binds_cons_iff in Hy. destruct Hy as [[Heq Hc]|Hy].
  - subst. apply binds_cons_2; auto.
  - apply binds_cons_3. apply H. exact Hy.
Qed.

Lemma env_rel_of_incl : forall E E', env_incl E E' -> env_rel E E'.
Proof.
  intros E E' H. split.
  - intros x U Hb. exists U. apply H. exact Hb.
  - intros x Q Hb. exists Q. apply H. exact Hb.
Qed.

Lemma wf_qua_incl : forall E E' Q,
  env_incl E E' -> wf_qua E Q -> wf_qua E' Q.
Proof. intros. apply wf_qua_env_rel with (E := E); auto. apply env_rel_of_incl; auto. Qed.

Lemma wf_typ_incl : forall E E' T,
  env_incl E E' -> wf_typ E T -> wf_typ E' T.
Proof. intros. apply wf_typ_env_rel with (E := E); auto. apply env_rel_of_incl; auto. Qed.

Lemma wf_qtyp_incl : forall E E' T,
  env_incl E E' -> wf_qtyp E T -> wf_qtyp E' T.
Proof. intros. apply wf_qtyp_env_rel with (E := E); auto. apply env_rel_of_incl; auto. Qed.

Lemma subqual_env_incl : forall E Q R, subqual E Q R ->
  forall E', env_incl E E' -> wf_env E' -> subqual E' Q R.
Proof.
  intros E Q R H.
  induction H as
    [ E0 Q0 Hwf HQ
    | E0 Q0 Hwf HQ
    | E0 Q' Q0 R0 b H1 IH1 Hc H2 IH2
    | E0 Q' Q0 R0 b H1 IH1 Hc H2 IH2
    | E0 b1 b2 Hwf Hord
    | E0 X Hwf HQ
    | R0 E0 Q0 X Hb H1 IH1
    | E0 R1 R2 Q0 H1 IH1 HR2
    | E0 R1 R2 Q0 HR1 H1 IH1
    | E0 R1 R2 Q0 H1 IH1 H2 IH2
    | E0 R1 R2 Q0 H1 IH1 HR2
    | E0 R1 R2 Q0 HR1 H1 IH1
    | E0 R1 R2 Q0 H1 IH1 H2 IH2 ]; intros E' Hincl Hwf'.
  - apply subqual_top.
    + exact Hwf'.
    + apply (wf_qua_incl E0 E' Q0); auto.
  - apply subqual_bot.
    + exact Hwf'.
    + apply (wf_qua_incl E0 E' Q0); auto.
  - apply subqual_eval_elim with (Q' := Q') (b := b).
    + apply IH1; auto.
    + exact Hc.
    + apply IH2; auto.
  - apply subqual_eval_intro with (Q' := Q') (b := b).
    + apply IH1; auto.
    + exact Hc.
    + apply IH2; auto.
  - apply subqual_lift_elem; auto.
  - apply subqual_refl_qvar; auto.
    apply (wf_qua_incl E0 E' (qua_fvar X) Hincl HQ).
  - apply subqual_trans_qvar with (R := R0).
    + apply Hincl. exact Hb.
    + apply IH1; auto.
  - apply subqual_join_inl.
    + apply IH1; auto.
    + apply (wf_qua_incl E0 E' R2); auto.
  - apply subqual_join_inr.
    + apply (wf_qua_incl E0 E' R1); auto.
    + apply IH1; auto.
  - apply subqual_join_elim.
    + apply IH1; auto.
    + apply IH2; auto.
  - apply subqual_meet_eliml.
    + apply IH1; auto.
    + apply (wf_qua_incl E0 E' R2); auto.
  - apply subqual_meet_elimr.
    + apply (wf_qua_incl E0 E' R1); auto.
    + apply IH1; auto.
  - apply subqual_meet_intro.
    + apply IH1; auto.
    + apply IH2; auto.
Qed.

Lemma sub_weaken : forall E S T, sub E S T ->
  forall E', env_incl E E' -> wf_env E' -> sub E' S T.
Proof.
  intros E S T H.
  refine (sub_mut_ind
    (fun E S T _ => forall E', env_incl E E' -> wf_env E' -> sub E' S T)
    (fun E S T _ => forall E', env_incl E E' -> wf_env E' -> subqtype E' S T)
    _ _ _ _ _ _ _ _ _ E S T H).
  - intros E0 S0 Hwf HwS E' Hincl Hwf'. apply sub_top; auto.
    apply (wf_typ_incl E0 E' S0); auto.
  - intros E0 X Hwf HwX E' Hincl Hwf'. apply sub_refl_tvar; auto.
    apply (wf_typ_incl E0 E' (typ_fvar X)); auto.
  - intros U E0 T0 X b s IH E' Hincl Hwf'.
    apply sub_trans_tvar with (U := U).
    + apply Hincl. exact b.
    + apply IH; auto.
  - intros E0 S1 S2 T1 T2 s1 IH1 s2 IH2 E' Hincl Hwf'.
    apply sub_arrow.
    + apply IH1; auto.
    + apply IH2; auto.
  - intros L E0 S1 S2 T1 T2 s IH s0 IH0 E' Hincl Hwf'.
    apply (sub_all (union L (dom E'))).
    + apply IH; auto.
    + intros X HX. apply (IH0 X).
      * simpl in HX; fsetdec.
      * apply env_incl_cons; auto.
      * apply wf_env_sub.
        -- exact Hwf'.
        -- apply (wf_typ_incl E0 E' T1); auto.
           destruct (sub_wf E0 T1 S1 s) as [_ [HT1 _]]. exact HT1.
        -- simpl in HX; fsetdec.
  - intros L E0 S1 S2 T1 T2 s s0 IH0 E' Hincl Hwf'.
    apply (sub_qall (union L (dom E'))).
    + exact (subqual_env_incl E0 T1 S1 s E' Hincl Hwf').
    + intros X HX. apply (IH0 X).
      * simpl in HX; fsetdec.
      * apply env_incl_cons; auto.
      * apply wf_env_qua.
        -- exact Hwf'.
        -- apply (wf_qua_incl E0 E' T1); auto.
           destruct (subqual_wf E0 T1 S1 s) as [HT1 _]. exact HT1.
        -- simpl in HX; fsetdec.
  - intros E0 S1 S2 T1 T2 s1 IH1 s2 IH2 E' Hincl Hwf'.
    apply sub_sum.
    + apply IH1; auto.
    + apply IH2; auto.
  - intros E0 S1 S2 T1 T2 s1 IH1 s2 IH2 E' Hincl Hwf'.
    apply sub_pair.
    + apply IH1; auto.
    + apply IH2; auto.
  - intros E0 Q1 T1 Q2 T2 s s0 IH E' Hincl Hwf'.
    apply sub_qtyp_qtyp.
    + exact (subqual_env_incl E0 Q1 Q2 s E' Hincl Hwf').
    + apply IH; auto.
Qed.

Lemma wf_env_head_inv : forall x b E, wf_env (x ~ b ++ E) -> wf_env E.
Proof.
  intros x b E H. destruct b; inversion H; subst; assumption.
Qed.

Lemma wf_env_typ_head : forall x V E,
  wf_env (x ~ bind_typ V ++ E) -> wf_env E /\ wf_qtyp E V.
Proof.
  intros x V E H. inversion H; subst. split; assumption.
Qed.

Lemma wf_env_sub_head : forall x V E,
  wf_env (x ~ bind_sub V ++ E) -> wf_env E /\ wf_typ E V.
Proof.
  intros x V E H. inversion H; subst. split; assumption.
Qed.

Lemma wf_env_qua_head : forall x Q E,
  wf_env (x ~ bind_qua Q ++ E) -> wf_env E /\ wf_qua E Q.
Proof.
  intros x Q E H. inversion H; subst. split; assumption.
Qed.

Lemma typing_wf_env : forall E e T, typing E e T -> wf_env E.
Proof.
  intros E e T H.
  induction H as
    [ E0 x T0 Hwf Hb
    | L E0 P V e1 T1 Hq Hbody IHbody
    | Q T1 E0 e1 e2 T2 H1 IH1 H2 IH2
    | L P E0 V e1 T1 Hq Hbody IHbody
    | Q T1 E0 e1 T T2 H1 IH1 Hsub
    | L E0 P Q e1 T1 HqP Hbody IHbody
    | R Q E0 e1 Q1 T H1 IH1 Hsubq
    | S E0 e T0 H1 IH1 Hsub
    | L T1 T2 e1 e2 E0 H1 IH1 Hbody IHbody
    | P T1 T2 e1 E0 Hq H1 IH1 HwfT2
    | P T1 T2 e1 E0 Hq H1 IH1 HwfT1
    | L Q T1 T2 T0 e1 e2 e3 E0 H1 IH1 Hbody2 IHbody2 Hbody3 IHbody3
    | P T1 T2 e1 e2 E0 Hq H1 IH1 H2 IH2
    | Q T1 T2 e E0 H1 IH1
    | Q T1 T2 e E0 H1 IH1
    | E0 Q T0 P e H1 IH1 Hsubq
    | E0 Q T0 P e H1 IH1 Hsubq ].
  - exact Hwf.
  - destruct (atom_fresh L) as [x Hx]. eapply wf_env_head_inv. apply (IHbody x Hx).
  - exact IH1.
  - destruct (atom_fresh L) as [x Hx]. eapply wf_env_head_inv. apply (IHbody x Hx).
  - exact IH1.
  - destruct (atom_fresh L) as [x Hx]. eapply wf_env_head_inv. apply (IHbody x Hx).
  - exact IH1.
  - exact IH1.
  - destruct (atom_fresh L) as [x Hx]. eapply wf_env_head_inv. apply (IHbody x Hx).
  - exact IH1.
  - exact IH1.
  - destruct (atom_fresh L) as [x Hx]. eapply wf_env_head_inv. apply (IHbody2 x Hx).
  - exact IH1.
  - exact IH1.
  - exact IH1.
  - exact IH1.
  - exact IH1.
Qed.

Lemma subqtype_weaken : forall E S T, subqtype E S T ->
  forall E', env_incl E E' -> wf_env E' -> subqtype E' S T.
Proof.
  intros E S T H. destruct S as [Q1 T1]. destruct T as [Q2 T2].
  destruct H as [E0 Q1' T1' Q2' T2' Hs Hsub].
  intros E' Hincl Hwf'. apply sub_qtyp_qtyp.
  - exact (subqual_env_incl E0 Q1' Q2' Hs E' Hincl Hwf').
  - exact (sub_weaken E0 T1' T2' Hsub E' Hincl Hwf').
Qed.

Lemma typing_weaken : forall E e T, typing E e T ->
  forall E', env_incl E E' -> wf_env E' -> typing E' e T.
Proof.
  intros E e T H.
  induction H as
    [ E0 x T0 Hwf Hb
    | L E0 P V e1 T1 Hq Hbody IHbody
    | Q T1 E0 e1 e2 T2 H1 IH1 H2 IH2
    | L P E0 V e1 T1 Hq Hbody IHbody
    | Q T1 E0 e1 T T2 H1 IH1 Hsub
    | L E0 P Q e1 T1 HqP Hbody IHbody
    | R Q E0 e1 Q1 T H1 IH1 Hsubq
    | S E0 e T0 H1 IH1 Hsub
    | L T1 T2 e1 e2 E0 H1 IH1 Hbody IHbody
    | P T1 T2 e1 E0 Hq H1 IH1 HwfT2
    | P T1 T2 e1 E0 Hq H1 IH1 HwfT1
    | L Q T1 T2 T0 e1 e2 e3 E0 H1 IH1 Hbody2 IHbody2 Hbody3 IHbody3
    | P T1 T2 e1 e2 E0 Hq H1 IH1 H2 IH2
    | Q T1 T2 e E0 H1 IH1
    | Q T1 T2 e E0 H1 IH1
    | E0 Q T0 P e H1 IH1 Hsubq
    | E0 Q T0 P e H1 IH1 Hsubq ]; intros E' Hincl Hwf'.
  - apply typing_var; auto.
  - destruct (atom_fresh L) as [x0 Hx0].
    destruct (wf_env_typ_head x0 V E0 (typing_wf_env _ _ _ (Hbody x0 Hx0))) as [_ HV].
    apply (typing_abs (union L (dom E'))).
    + apply (wf_qua_incl E0 E' P); auto.
    + intros x HX. apply IHbody.
      * simpl in HX; fsetdec.
      * apply env_incl_cons; exact Hincl.
      * apply wf_env_typ.
        -- exact Hwf'.
        -- apply (wf_qtyp_incl E0 E' V); auto.
        -- simpl in HX; fsetdec.
  - apply typing_app with (Q := Q) (T1 := T1) (T2 := T2); auto.
  - destruct (atom_fresh L) as [x0 Hx0].
    destruct (wf_env_sub_head x0 V E0 (typing_wf_env _ _ _ (Hbody x0 Hx0))) as [_ HV].
    apply (typing_tabs (union L (dom E'))).
    + apply (wf_qua_incl E0 E' P); auto.
    + intros x HX. apply IHbody.
      * simpl in HX; fsetdec.
      * apply env_incl_cons; exact Hincl.
      * apply wf_env_sub.
        -- exact Hwf'.
        -- apply (wf_typ_incl E0 E' V); auto.
        -- simpl in HX; fsetdec.
  - apply typing_tapp with (Q := Q) (T1 := T1) (T2 := T2) (T := T); auto.
    apply (sub_weaken E0 T T1 Hsub E' Hincl Hwf').
  - destruct (atom_fresh L) as [x0 Hx0].
    destruct (wf_env_qua_head x0 Q E0 (typing_wf_env _ _ _ (Hbody x0 Hx0))) as [_ HQ].
    apply (typing_qabs (union L (dom E'))).
    + apply (wf_qua_incl E0 E' P); auto.
    + intros x HX. apply IHbody.
      * simpl in HX; fsetdec.
      * apply env_incl_cons; exact Hincl.
      * apply wf_env_qua.
        -- exact Hwf'.
        -- apply (wf_qua_incl E0 E' Q); auto.
        -- simpl in HX; fsetdec.
  - apply typing_qapp with (R := R) (Q1 := Q1) (T := T); auto.
    exact (subqual_env_incl E0 Q Q1 Hsubq E' Hincl Hwf').
  - apply typing_sub with (S := S); auto.
    apply (subqtype_weaken E0 S T0 Hsub E' Hincl Hwf').
  - destruct (atom_fresh L) as [x0 Hx0].
    destruct (wf_env_typ_head x0 T1 E0 (typing_wf_env _ _ _ (Hbody x0 Hx0))) as [_ HT1].
    apply (typing_let (union L (dom E')) T1 T2 e1 e2 E').
    + apply IH1; auto.
    + intros x HX. apply IHbody.
      * simpl in HX; fsetdec.
      * apply env_incl_cons; exact Hincl.
      * apply wf_env_typ.
        -- exact Hwf'.
        -- apply (wf_qtyp_incl E0 E' T1); auto.
        -- simpl in HX; fsetdec.
  - apply typing_inl with (P := P) (T1 := T1) (T2 := T2); auto.
    + apply (wf_qua_incl E0 E' P); auto.
    + apply (wf_qtyp_incl E0 E' T2); auto.
  - apply typing_inr with (P := P) (T1 := T1) (T2 := T2); auto.
    + apply (wf_qua_incl E0 E' P); auto.
    + apply (wf_qtyp_incl E0 E' T1); auto.
  - destruct (atom_fresh L) as [x0 Hx0].
    destruct (wf_env_typ_head x0 T1 E0 (typing_wf_env _ _ _ (Hbody2 x0 Hx0))) as [_ HT1].
    destruct (wf_env_typ_head x0 T2 E0 (typing_wf_env _ _ _ (Hbody3 x0 Hx0))) as [_ HT2].
    apply (typing_case (union L (dom E')) Q T1 T2 T0 e1 e2 e3 E').
    + apply IH1; auto.
    + intros x HX. apply IHbody2.
      * simpl in HX; fsetdec.
      * apply env_incl_cons; exact Hincl.
      * apply wf_env_typ.
        -- exact Hwf'.
        -- apply (wf_qtyp_incl E0 E' T1); auto.
        -- simpl in HX; fsetdec.
    + intros x HX. apply IHbody3.
      * simpl in HX; fsetdec.
      * apply env_incl_cons; exact Hincl.
      * apply wf_env_typ.
        -- exact Hwf'.
        -- apply (wf_qtyp_incl E0 E' T2); auto.
        -- simpl in HX; fsetdec.
  - apply typing_pair with (P := P) (T1 := T1) (T2 := T2); auto.
    apply (wf_qua_incl E0 E' P); auto.
  - apply typing_first with (Q := Q) (T1 := T1) (T2 := T2); auto.
  - apply typing_second with (Q := Q) (T1 := T1) (T2 := T2); auto.
  - apply typing_upqual with (Q := Q) (T := T0) (P := P); auto.
    exact (subqual_env_incl E0 Q P Hsubq E' Hincl Hwf').
  - apply typing_check with (Q := Q) (T := T0) (P := P); auto.
    exact (subqual_env_incl E0 Q P Hsubq E' Hincl Hwf').
Qed.

(* ================================================================== *)
(* Environment narrowing: changing binding payloads via subtyping     *)
(* ================================================================== *)

Inductive env_narrow : env -> env -> Prop :=
  | env_narrow_nil : forall E,
      env_narrow E E
  | env_narrow_sub_keep : forall x W E E',
      env_narrow E E' ->
      env_narrow (x ~ bind_sub W ++ E) (x ~ bind_sub W ++ E')
  | env_narrow_sub_change : forall x W W' E E',
      env_narrow E E' ->
      sub E' W' W ->
      env_narrow (x ~ bind_sub W ++ E) (x ~ bind_sub W' ++ E')
  | env_narrow_qua_keep : forall x Q E E',
      env_narrow E E' ->
      env_narrow (x ~ bind_qua Q ++ E) (x ~ bind_qua Q ++ E')
  | env_narrow_qua_change : forall x Q Q' E E',
      env_narrow E E' ->
      subqual E' Q' Q ->
      env_narrow (x ~ bind_qua Q ++ E) (x ~ bind_qua Q' ++ E')
  | env_narrow_typ_keep : forall x T E E',
      env_narrow E E' ->
      env_narrow (x ~ bind_typ T ++ E) (x ~ bind_typ T ++ E')
.

Lemma env_narrow_refl : forall E, env_narrow E E.
Proof. intros E. constructor. Qed.

Lemma env_narrow_dom : forall E E', env_narrow E E' -> dom E = dom E'.
Proof.
  intros E E' H. induction H; simpl; auto.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
Qed.

Lemma env_narrow_env_rel : forall E E', env_narrow E E' -> env_rel E E'.
Proof.
  intros E E' H.
  induction H as [E0 | x W E0 E1 Hn IHn | x W W' E0 E1 Hn IHn HR | x Q E0 E1 Hn IHn | x Q Q' E0 E1 Hn IHn HR | x T E0 E1 Hn IHn].
  - apply env_rel_refl.
  - (* sub keep *) split.
    + intros y V Hb. apply binds_cons_iff in Hb. destruct Hb as [[Heq Hp]|Hb].
      * subst. exists W. apply binds_cons_2; auto.
      * destruct (proj1 IHn y V Hb) as [V' HV']. exists V'.
        apply binds_cons_3. exact HV'.
    + intros y Q0 Hb. apply binds_cons_iff in Hb. destruct Hb as [[Heq Hp]|Hb].
      * inversion Heq. inversion Hp.
      * destruct (proj2 IHn y Q0 Hb) as [Q0' HQ']. exists Q0'.
        apply binds_cons_3. exact HQ'.
  - (* sub change *) split.
    + intros y V Hb. apply binds_cons_iff in Hb. destruct Hb as [[Heq Hp]|Hb].
      * subst. exists W'. apply binds_cons_2; auto.
      * destruct (proj1 IHn y V Hb) as [V' HV']. exists V'.
        apply binds_cons_3. exact HV'.
    + intros y Q0 Hb. apply binds_cons_iff in Hb. destruct Hb as [[Heq Hp]|Hb].
      * inversion Heq. inversion Hp.
      * destruct (proj2 IHn y Q0 Hb) as [Q0' HQ']. exists Q0'.
        apply binds_cons_3. exact HQ'.
  - (* qua keep *) split.
    + intros y V Hb. apply binds_cons_iff in Hb. destruct Hb as [[Heq Hp]|Hb].
      * inversion Heq. inversion Hp.
      * destruct (proj1 IHn y V Hb) as [V' HV']. exists V'.
        apply binds_cons_3. exact HV'.
    + intros y Q0 Hb. apply binds_cons_iff in Hb. destruct Hb as [[Heq Hp]|Hb].
      * subst. exists Q. apply binds_cons_2; auto.
      * destruct (proj2 IHn y Q0 Hb) as [Q0' HQ']. exists Q0'.
        apply binds_cons_3. exact HQ'.
  - (* qua change *) split.
    + intros y V Hb. apply binds_cons_iff in Hb. destruct Hb as [[Heq Hp]|Hb].
      * inversion Heq. inversion Hp.
      * destruct (proj1 IHn y V Hb) as [V' HV']. exists V'.
        apply binds_cons_3. exact HV'.
    + intros y Q0 Hb. apply binds_cons_iff in Hb. destruct Hb as [[Heq Hp]|Hb].
      * subst. exists Q'. apply binds_cons_2; auto.
      * destruct (proj2 IHn y Q0 Hb) as [Q0' HQ']. exists Q0'.
        apply binds_cons_3. exact HQ'.
  - (* typ keep *) split.
    + intros y V Hb. apply binds_cons_iff in Hb. destruct Hb as [[Heq Hp]|Hb].
      * inversion Heq. inversion Hp.
      * destruct (proj1 IHn y V Hb) as [V' HV']. exists V'.
        apply binds_cons_3. exact HV'.
    + intros y Q0 Hb. apply binds_cons_iff in Hb. destruct Hb as [[Heq Hp]|Hb].
      * inversion Heq. inversion Hp.
      * destruct (proj2 IHn y Q0 Hb) as [Q0' HQ']. exists Q0'.
        apply binds_cons_3. exact HQ'.
Qed.

Lemma wf_typ_narrow : forall E E' T,
  env_narrow E E' -> wf_typ E T -> wf_typ E' T.
Proof.
  intros. apply (wf_typ_env_rel E T); auto.
  apply env_narrow_env_rel. exact H.
Qed.

Lemma wf_qtyp_narrow : forall E E' T,
  env_narrow E E' -> wf_qtyp E T -> wf_qtyp E' T.
Proof.
  intros. apply (wf_qtyp_env_rel E T); auto.
  apply env_narrow_env_rel. exact H.
Qed.

Lemma wf_qua_narrow : forall E E' Q,
  env_narrow E E' -> wf_qua E Q -> wf_qua E' Q.
Proof.
  intros. apply (wf_qua_env_rel E E' Q); auto.
  apply env_narrow_env_rel. exact H.
Qed.

Lemma wf_env_narrow : forall E E', wf_env E -> env_narrow E E' -> wf_env E'.
Proof.
  intros E E' Hwf Hn.
  induction Hn as [E0 | x W E0 E1 Hn IHn | x W W' E0 E1 Hn IHn HR | x Q E0 E1 Hn IHn | x Q Q' E0 E1 Hn IHn HR | x T E0 E1 Hn IHn].
  - exact Hwf.
  - (* sub keep *)
    assert (Htail : wf_env E0) by (apply (wf_env_head_inv x (bind_sub W) E0 Hwf)).
    assert (Hfresh : x `notin` dom E0).
    { apply (uniq_cons_2 _ x (bind_sub W) E0); apply wf_env_uniq; exact Hwf. }
    destruct (wf_env_sub_head x W E0 Hwf) as [Hw Hpay].
    apply wf_env_sub.
    + apply IHn. exact Htail.
    + apply (wf_typ_narrow E0 E1 W); auto.
    + rewrite <- (env_narrow_dom E0 E1 Hn). exact Hfresh.
  - (* sub change *)
    assert (Htail : wf_env E0) by (apply (wf_env_head_inv x (bind_sub W) E0 Hwf)).
    assert (Hfresh : x `notin` dom E0).
    { apply (uniq_cons_2 _ x (bind_sub W) E0); apply wf_env_uniq; exact Hwf. }
    apply wf_env_sub.
    + apply IHn. exact Htail.
    + apply (sub_wf E1 W' W); auto.
    + rewrite <- (env_narrow_dom E0 E1 Hn). exact Hfresh.
  - (* qua keep *)
    assert (Htail : wf_env E0) by (apply (wf_env_head_inv x (bind_qua Q) E0 Hwf)).
    assert (Hfresh : x `notin` dom E0).
    { apply (uniq_cons_2 _ x (bind_qua Q) E0); apply wf_env_uniq; exact Hwf. }
    destruct (wf_env_qua_head x Q E0 Hwf) as [Hw Hpay].
    apply wf_env_qua.
    + apply IHn. exact Htail.
    + apply (wf_qua_narrow E0 E1 Q); auto.
    + rewrite <- (env_narrow_dom E0 E1 Hn). exact Hfresh.
  - (* qua change *)
    assert (Htail : wf_env E0) by (apply (wf_env_head_inv x (bind_qua Q) E0 Hwf)).
    assert (Hfresh : x `notin` dom E0).
    { apply (uniq_cons_2 _ x (bind_qua Q) E0); apply wf_env_uniq; exact Hwf. }
    apply wf_env_qua.
    + apply IHn. exact Htail.
    + apply (subqual_wf E1 Q' Q); auto.
    + rewrite <- (env_narrow_dom E0 E1 Hn). exact Hfresh.
  - (* typ keep *)
    assert (Htail : wf_env E0) by (apply (wf_env_head_inv x (bind_typ T) E0 Hwf)).
    assert (Hfresh : x `notin` dom E0).
    { apply (uniq_cons_2 _ x (bind_typ T) E0); apply wf_env_uniq; exact Hwf. }
    destruct (wf_env_typ_head x T E0 Hwf) as [Hw Hpay].
    apply wf_env_typ.
    + apply IHn. exact Htail.
    + apply (wf_qtyp_narrow E0 E1 T); auto.
    + rewrite <- (env_narrow_dom E0 E1 Hn). exact Hfresh.
Qed.


Lemma wf_env_narrow_cons_sub : forall x W E E',
  wf_env (x ~ bind_sub W ++ E) -> env_narrow E E' ->
  wf_env (x ~ bind_sub W ++ E').
Proof.
  intros x W E E' Hwf Hn.
  assert (Htail : wf_env E) by (apply (wf_env_head_inv x (bind_sub W) E Hwf)).
  assert (Hfresh : x `notin` dom E).
  { apply (uniq_cons_2 _ x (bind_sub W) E); apply wf_env_uniq; exact Hwf. }
  destruct (wf_env_sub_head x W E Hwf) as [Hw Hpay].
  apply wf_env_sub.
  - apply (wf_env_narrow E E').
    + apply (wf_env_head_inv x (bind_sub W) E); exact Hwf.
    + exact Hn.
  - apply (wf_typ_narrow E E' W); auto.
  - rewrite <- (env_narrow_dom E E' Hn). exact Hfresh.
Qed.

Lemma wf_env_narrow_cons_qua : forall x Q E E',
  wf_env (x ~ bind_qua Q ++ E) -> env_narrow E E' ->
  wf_env (x ~ bind_qua Q ++ E').
Proof.
  intros x Q E E' Hwf Hn.
  assert (Htail : wf_env E) by (apply (wf_env_head_inv x (bind_qua Q) E Hwf)).
  assert (Hfresh : x `notin` dom E).
  { apply (uniq_cons_2 _ x (bind_qua Q) E); apply wf_env_uniq; exact Hwf. }
  destruct (wf_env_qua_head x Q E Hwf) as [Hw Hpay].
  apply wf_env_qua.
  - apply (wf_env_narrow E E').
    + apply (wf_env_head_inv x (bind_qua Q) E); exact Hwf.
    + exact Hn.
  - apply (wf_qua_narrow E E' Q); auto.
  - rewrite <- (env_narrow_dom E E' Hn). exact Hfresh.
Qed.

Lemma wf_env_narrow_cons_typ : forall x T E E',
  wf_env (x ~ bind_typ T ++ E) -> env_narrow E E' ->
  wf_env (x ~ bind_typ T ++ E').
Proof.
  intros x T E E' Hwf Hn.
  assert (Htail : wf_env E) by (apply (wf_env_head_inv x (bind_typ T) E Hwf)).
  assert (Hfresh : x `notin` dom E).
  { apply (uniq_cons_2 _ x (bind_typ T) E); apply wf_env_uniq; exact Hwf. }
  destruct (wf_env_typ_head x T E Hwf) as [Hw Hpay].
  apply wf_env_typ.
  - apply (wf_env_narrow E E').
    + apply (wf_env_head_inv x (bind_typ T) E); exact Hwf.
    + exact Hn.
  - apply (wf_qtyp_narrow E E' T); auto.
  - rewrite <- (env_narrow_dom E E' Hn). exact Hfresh.
Qed.

Lemma wf_env_narrow_change_sub : forall x W W' E E',
  wf_env (x ~ bind_sub W ++ E) -> env_narrow E E' ->
  sub E' W' W -> wf_env (x ~ bind_sub W' ++ E').
Proof.
  intros x W W' E E' Hwf Hn HR.
  assert (Hfresh : x `notin` dom E).
  { apply (uniq_cons_2 _ x (bind_sub W) E); apply wf_env_uniq; exact Hwf. }
  apply wf_env_sub.
  - apply (wf_env_narrow E E').
    + apply (wf_env_head_inv x (bind_sub W) E); exact Hwf.
    + exact Hn.
  - apply (sub_wf E' W' W); auto.
  - rewrite <- (env_narrow_dom E E' Hn). exact Hfresh.
Qed.

Lemma wf_env_narrow_change_qua : forall x Q Q' E E',
  wf_env (x ~ bind_qua Q ++ E) -> env_narrow E E' ->
  subqual E' Q' Q -> wf_env (x ~ bind_qua Q' ++ E').
Proof.
  intros x Q Q' E E' Hwf Hn HR.
  assert (Hfresh : x `notin` dom E).
  { apply (uniq_cons_2 _ x (bind_qua Q) E); apply wf_env_uniq; exact Hwf. }
  apply wf_env_qua.
  - apply (wf_env_narrow E E').
    + apply (wf_env_head_inv x (bind_qua Q) E); exact Hwf.
    + exact Hn.
  - apply (subqual_wf E' Q' Q); auto.
  - rewrite <- (env_narrow_dom E E' Hn). exact Hfresh.
Qed.

Lemma env_narrow_binds_sub : forall E E' Y U,
  wf_env E -> env_narrow E E' ->
  binds Y (bind_sub U) E ->
  (binds Y (bind_sub U) E') \/
  (exists U', binds Y (bind_sub U') E' /\ sub E' U' U).
Proof.
  intros E E' Y U Hwf Hn.
  induction Hn; intros Hb.
  - left. exact Hb.
  - (* sub keep *)
    apply binds_cons_iff in Hb. destruct Hb as [[Heq Hp]|Hb].
    + inversion Heq; inversion Hp; subst. left. apply binds_cons_2; auto.
    + destruct (IHHn (wf_env_head_inv _ _ _ Hwf) Hb) as [Hsame|[U' [HU' HR]]].
      * left. apply binds_cons. exact Hsame.
      * right. exists U'. split.
        -- apply binds_cons. exact HU'.
        -- apply (sub_weaken E' U' U HR (x ~ bind_sub W ++ E'));
             [ intros z bz Hz; apply binds_cons; exact Hz
             | apply (wf_env_narrow_cons_sub x W E E' Hwf Hn) ].
  - (* sub change *)
    apply binds_cons_iff in Hb. destruct Hb as [[Heq Hp]|Hb].
    + inversion Heq; inversion Hp; subst. right. exists W'. split.
      * apply binds_cons_2; auto.
      * apply (sub_weaken E' W' W H (x ~ bind_sub W' ++ E'));
          [ intros z bz Hz; apply binds_cons; exact Hz
          | apply (wf_env_narrow_change_sub x W W' E E' Hwf Hn H) ].
    + destruct (IHHn (wf_env_head_inv _ _ _ Hwf) Hb) as [Hsame|[U' [HU' HR]]].
      * left. apply binds_cons. exact Hsame.
      * right. exists U'. split.
        -- apply binds_cons. exact HU'.
        -- apply (sub_weaken E' U' U HR (x ~ bind_sub W' ++ E'));
             [ intros z bz Hz; apply binds_cons; exact Hz
             | apply (wf_env_narrow_change_sub x W W' E E' Hwf Hn H) ].
  - (* qua keep *)
    apply binds_cons_iff in Hb. destruct Hb as [[Heq Hp]|Hb].
    + inversion Heq. inversion Hp.
    + destruct (IHHn (wf_env_head_inv _ _ _ Hwf) Hb) as [Hsame|[U' [HU' HR]]].
      * left. apply binds_cons. exact Hsame.
      * right. exists U'. split.
        -- apply binds_cons. exact HU'.
        -- apply (sub_weaken E' U' U HR (x ~ bind_qua Q ++ E'));
             [ intros z bz Hz; apply binds_cons; exact Hz
             | apply (wf_env_narrow_cons_qua x Q E E' Hwf Hn) ].
  - (* qua change *)
    apply binds_cons_iff in Hb. destruct Hb as [[Heq Hp]|Hb].
    + inversion Heq. inversion Hp.
    + destruct (IHHn (wf_env_head_inv _ _ _ Hwf) Hb) as [Hsame|[U' [HU' HR]]].
      * left. apply binds_cons. exact Hsame.
      * right. exists U'. split.
        -- apply binds_cons. exact HU'.
        -- apply (sub_weaken E' U' U HR (x ~ bind_qua Q' ++ E'));
             [ intros z bz Hz; apply binds_cons; exact Hz
             | apply (wf_env_narrow_change_qua x Q Q' E E' Hwf Hn H) ].
  - (* typ keep *)
    apply binds_cons_iff in Hb. destruct Hb as [[Heq Hp]|Hb].
    + inversion Heq. inversion Hp.
    + destruct (IHHn (wf_env_head_inv _ _ _ Hwf) Hb) as [Hsame|[U' [HU' HR]]].
      * left. apply binds_cons. exact Hsame.
      * right. exists U'. split.
        -- apply binds_cons. exact HU'.
        -- apply (sub_weaken E' U' U HR (x ~ bind_typ T ++ E'));
             [ intros z bz Hz; apply binds_cons; exact Hz
             | apply (wf_env_narrow_cons_typ x T E E' Hwf Hn) ].
Qed.

Lemma env_narrow_binds_qua : forall E E' Y Q,
  wf_env E -> env_narrow E E' ->
  binds Y (bind_qua Q) E ->
  (binds Y (bind_qua Q) E') \/
  (exists Q', binds Y (bind_qua Q') E' /\ subqual E' Q' Q).
Proof.
  intros E E' Y Q Hwf Hn.
  induction Hn; intros Hb.
  - left. exact Hb.
  - (* sub keep *)
    apply binds_cons_iff in Hb. destruct Hb as [[Heq Hp]|Hb].
    + inversion Heq; inversion Hp.
    + destruct (IHHn (wf_env_head_inv _ _ _ Hwf) Hb) as [Hsame|[Qx [HQx HR]]].
      * left. apply binds_cons. exact Hsame.
      * right. exists Qx. split.
        -- apply binds_cons. exact HQx.
        -- apply (subqual_env_incl E' Qx Q HR (x ~ bind_sub W ++ E')).
           ++ intros z bz Hz; apply binds_cons; exact Hz.
           ++ apply (wf_env_narrow_cons_sub x W E E' Hwf Hn).
  - (* sub change *)
    apply binds_cons_iff in Hb. destruct Hb as [[Heq Hp]|Hb].
    + inversion Heq; inversion Hp.
    + destruct (IHHn (wf_env_head_inv _ _ _ Hwf) Hb) as [Hsame|[Qx [HQx HR]]].
      * left. apply binds_cons. exact Hsame.
      * right. exists Qx. split.
        -- apply binds_cons. exact HQx.
        -- apply (subqual_env_incl E' Qx Q HR (x ~ bind_sub W' ++ E')).
           ++ intros z bz Hz; apply binds_cons; exact Hz.
           ++ apply (wf_env_narrow_change_sub x W W' E E' Hwf Hn H).
  - (* qua keep *)
    apply binds_cons_iff in Hb. destruct Hb as [[Heq Hp]|Hb].
    + inversion Heq; inversion Hp; subst. left. apply binds_cons_2; auto.
    + destruct (IHHn (wf_env_head_inv _ _ _ Hwf) Hb) as [Hsame|[Qx [HQx HR]]].
      * left. apply binds_cons. exact Hsame.
      * right. exists Qx. split.
        -- apply binds_cons. exact HQx.
        -- apply (subqual_env_incl E' Qx Q HR (x ~ bind_qua Q0 ++ E')).
           ++ intros z bz Hz; apply binds_cons; exact Hz.
           ++ apply (wf_env_narrow_cons_qua x Q0 E E' Hwf Hn).
  - (* qua change *)
    apply binds_cons_iff in Hb. destruct Hb as [[Heq Hp]|Hb].
    + inversion Heq; inversion Hp; subst. right. exists Q'. split.
      * apply binds_cons_2; auto.
      * apply (subqual_env_incl E' Q' Q0 H (x ~ bind_qua Q' ++ E')).
        -- intros z bz Hz; apply binds_cons; exact Hz.
        -- apply (wf_env_narrow_change_qua x Q0 Q' E E' Hwf Hn H).
    + destruct (IHHn (wf_env_head_inv _ _ _ Hwf) Hb) as [Hsame|[Qx [HQx HR]]].
      * left. apply binds_cons. exact Hsame.
      * right. exists Qx. split.
        -- apply binds_cons. exact HQx.
        -- apply (subqual_env_incl E' Qx Q HR (x ~ bind_qua Q' ++ E')).
           ++ intros z bz Hz; apply binds_cons; exact Hz.
           ++ apply (wf_env_narrow_change_qua x Q0 Q' E E' Hwf Hn H).
  - (* typ keep *)
    apply binds_cons_iff in Hb. destruct Hb as [[Heq Hp]|Hb].
    + inversion Heq; inversion Hp.
    + destruct (IHHn (wf_env_head_inv _ _ _ Hwf) Hb) as [Hsame|[Qx [HQx HR]]].
      * left. apply binds_cons. exact Hsame.
      * right. exists Qx. split.
        -- apply binds_cons. exact HQx.
        -- apply (subqual_env_incl E' Qx Q HR (x ~ bind_typ T ++ E')).
           ++ intros z bz Hz; apply binds_cons; exact Hz.
           ++ apply (wf_env_narrow_cons_typ x T E E' Hwf Hn).
Qed.


Lemma subqual_narrow : forall E E' Q R,
  wf_env E -> subqual E Q R -> env_narrow E E' -> subqual E' Q R.
Proof.
  intros E E' Q R Hwf Hs.
  induction Hs; intros Hn.
  - apply subqual_top.
    + apply (wf_env_narrow E E'); auto.
    + apply (wf_qua_narrow E E' Q); auto.
  - apply subqual_bot.
    + apply (wf_env_narrow E E'); auto.
    + apply (wf_qua_narrow E E' Q); auto.
  - eapply subqual_eval_elim.
    + apply IHHs1; auto.
    + exact H.
    + apply IHHs2; auto.
  - eapply subqual_eval_intro.
    + apply IHHs1; auto.
    + exact H.
    + apply IHHs2; auto.
  - apply subqual_lift_elem.
    + apply (wf_env_narrow E E'); auto.
    + assumption.
  - apply subqual_refl_qvar.
    + apply (wf_env_narrow E E'); auto.
    + apply (wf_qua_narrow E E' (qua_fvar X)); auto.
  - (* trans_qvar *)
    match goal with
    | Hb : binds X (bind_qua R) E |- _ =>
      destruct (env_narrow_binds_qua E E' X R Hwf Hn Hb)
        as [Hsame|[Rx [Hbx HR]]]
    end.
    + eapply subqual_trans_qvar with (R := R) (E := E') (X := X).
      * exact Hsame.
      * apply IHHs; auto.
    + eapply subqual_trans_qvar with (R := Rx) (E := E') (X := X).
      * exact Hbx.
      * eapply subqual_trans.
        -- exact HR.
        -- apply IHHs; auto.
  - apply subqual_join_inl.
    + apply IHHs; auto.
    + apply (wf_qua_narrow E E' R2); auto.
  - apply subqual_join_inr.
    + apply (wf_qua_narrow E E' R1); auto.
    + apply IHHs; auto.
  - apply subqual_join_elim.
    + apply IHHs1; auto.
    + apply IHHs2; auto.
  - apply subqual_meet_eliml.
    + apply IHHs; auto.
    + apply (wf_qua_narrow E E' R2); auto.
  - apply subqual_meet_elimr.
    + apply (wf_qua_narrow E E' R1); auto.
    + apply IHHs; auto.
  - apply subqual_meet_intro.
    + apply IHHs1; auto.
    + apply IHHs2; auto.
Qed.

(* ================================================================== *)
(* Well-founded measure over derivation trees                         *)
(* ================================================================== *)

Inductive deriv : Type :=
  | Dsub : forall {E S T}, sub E S T -> deriv
  | Dqt  : forall {E S T}, subqtype E S T -> deriv
  | Dsq  : forall {E Q R}, subqual E Q R -> deriv
  | Dn   : forall {E E'}, env_narrow E E' -> deriv.

Inductive isub : deriv -> deriv -> Prop :=
  | isub_sub_trans : forall U E T X (b : binds X (bind_sub U) E) (s : sub E U T),
      isub (Dsub s) (Dsub (sub_trans_tvar U E T X b s))
  | isub_sub_arrow1 : forall E S1 S2 T1 T2 (q1 : subqtype E T1 S1) (q2 : subqtype E S2 T2),
      isub (Dqt q1) (Dsub (sub_arrow E S1 S2 T1 T2 q1 q2))
  | isub_sub_arrow2 : forall E S1 S2 T1 T2 (q1 : subqtype E T1 S1) (q2 : subqtype E S2 T2),
      isub (Dqt q2) (Dsub (sub_arrow E S1 S2 T1 T2 q1 q2))
  | isub_sub_all1 : forall L E S1 S2 T1 T2 (s1 : sub E T1 S1)
        (s2 : forall X, X `notin` L -> subqtype (X ~ bind_sub T1 ++ E) (open_tqt S2 X) (open_tqt T2 X)),
      isub (Dsub s1) (Dsub (sub_all L E S1 S2 T1 T2 s1 s2))
  | isub_sub_all2 : forall L E S1 S2 T1 T2 (s1 : sub E T1 S1)
        (s2 : forall X, X `notin` L -> subqtype (X ~ bind_sub T1 ++ E) (open_tqt S2 X) (open_tqt T2 X))
        (X : atom) (HX : X `notin` L),
      isub (Dqt (s2 X HX)) (Dsub (sub_all L E S1 S2 T1 T2 s1 s2))
  | isub_sub_qall1 : forall L E S1 S2 T1 T2 (sq : subqual E T1 S1)
        (s2 : forall X, X `notin` L -> subqtype (X ~ bind_qua T1 ++ E) (open_qqt S2 X) (open_qqt T2 X)),
      isub (Dsq sq) (Dsub (sub_qall L E S1 S2 T1 T2 sq s2))
  | isub_sub_qall2 : forall L E S1 S2 T1 T2 (sq : subqual E T1 S1)
        (s2 : forall X, X `notin` L -> subqtype (X ~ bind_qua T1 ++ E) (open_qqt S2 X) (open_qqt T2 X))
        (X : atom) (HX : X `notin` L),
      isub (Dqt (s2 X HX)) (Dsub (sub_qall L E S1 S2 T1 T2 sq s2))
  | isub_sub_sum1 : forall E S1 S2 T1 T2 (q1 : subqtype E S1 T1) (q2 : subqtype E S2 T2),
      isub (Dqt q1) (Dsub (sub_sum E S1 S2 T1 T2 q1 q2))
  | isub_sub_sum2 : forall E S1 S2 T1 T2 (q1 : subqtype E S1 T1) (q2 : subqtype E S2 T2),
      isub (Dqt q2) (Dsub (sub_sum E S1 S2 T1 T2 q1 q2))
  | isub_sub_pair1 : forall E S1 S2 T1 T2 (q1 : subqtype E S1 T1) (q2 : subqtype E S2 T2),
      isub (Dqt q1) (Dsub (sub_pair E S1 S2 T1 T2 q1 q2))
  | isub_sub_pair2 : forall E S1 S2 T1 T2 (q1 : subqtype E S1 T1) (q2 : subqtype E S2 T2),
      isub (Dqt q2) (Dsub (sub_pair E S1 S2 T1 T2 q1 q2))
  | isub_qt_qual : forall E Q1 T1 Q2 T2 (sq : subqual E Q1 Q2) (s : sub E T1 T2),
      isub (Dsq sq) (Dqt (sub_qtyp_qtyp E Q1 T1 Q2 T2 sq s))
  | isub_qt_sub : forall E Q1 T1 Q2 T2 (sq : subqual E Q1 Q2) (s : sub E T1 T2),
      isub (Dsub s) (Dqt (sub_qtyp_qtyp E Q1 T1 Q2 T2 sq s))
  | isub_sq_eval_elim1 : forall E Q' Q R b (s1 : subqual E Q Q') (Hc : concretize Q' = Some b) (s2 : subqual E (qua_base b) R),
      isub (Dsq s1) (Dsq (subqual_eval_elim E Q' Q R b s1 Hc s2))
  | isub_sq_eval_elim2 : forall E Q' Q R b (s1 : subqual E Q Q') (Hc : concretize Q' = Some b) (s2 : subqual E (qua_base b) R),
      isub (Dsq s2) (Dsq (subqual_eval_elim E Q' Q R b s1 Hc s2))
  | isub_sq_eval_intro1 : forall E Q' Q R b (s1 : subqual E Q' R) (Hc : concretize Q' = Some b) (s2 : subqual E Q (qua_base b)),
      isub (Dsq s1) (Dsq (subqual_eval_intro E Q' Q R b s1 Hc s2))
  | isub_sq_eval_intro2 : forall E Q' Q R b (s1 : subqual E Q' R) (Hc : concretize Q' = Some b) (s2 : subqual E Q (qua_base b)),
      isub (Dsq s2) (Dsq (subqual_eval_intro E Q' Q R b s1 Hc s2))
  | isub_sq_trans_qvar : forall R E Q X (b : binds X (bind_qua R) E) (s : subqual E R Q),
      isub (Dsq s) (Dsq (subqual_trans_qvar R E Q X b s))
  | isub_sq_join_inl : forall E R1 R2 Q (s : subqual E Q R1) (w : wf_qua E R2),
      isub (Dsq s) (Dsq (subqual_join_inl E R1 R2 Q s w))
  | isub_sq_join_inr : forall E R1 R2 Q (w : wf_qua E R1) (s : subqual E Q R2),
      isub (Dsq s) (Dsq (subqual_join_inr E R1 R2 Q w s))
  | isub_sq_join_elim1 : forall E R1 R2 Q (s1 : subqual E R1 Q) (s2 : subqual E R2 Q),
      isub (Dsq s1) (Dsq (subqual_join_elim E R1 R2 Q s1 s2))
  | isub_sq_join_elim2 : forall E R1 R2 Q (s1 : subqual E R1 Q) (s2 : subqual E R2 Q),
      isub (Dsq s2) (Dsq (subqual_join_elim E R1 R2 Q s1 s2))
  | isub_sq_meet_eliml : forall E R1 R2 Q (s : subqual E R1 Q) (w : wf_qua E R2),
      isub (Dsq s) (Dsq (subqual_meet_eliml E R1 R2 Q s w))
  | isub_sq_meet_elimr : forall E R1 R2 Q (w : wf_qua E R1) (s : subqual E R2 Q),
      isub (Dsq s) (Dsq (subqual_meet_elimr E R1 R2 Q w s))
  | isub_sq_meet_intro1 : forall E R1 R2 Q (s1 : subqual E Q R1) (s2 : subqual E Q R2),
      isub (Dsq s1) (Dsq (subqual_meet_intro E R1 R2 Q s1 s2))
  | isub_sq_meet_intro2 : forall E R1 R2 Q (s1 : subqual E Q R1) (s2 : subqual E Q R2),
      isub (Dsq s2) (Dsq (subqual_meet_intro E R1 R2 Q s1 s2))
  | isub_n_sub_keep : forall x W E E' (Hn : env_narrow E E'),
      isub (Dn Hn) (Dn (env_narrow_sub_keep x W E E' Hn))
  | isub_n_sub_change1 : forall x W W' E E' (Hn : env_narrow E E') (HR : sub E' W' W),
      isub (Dn Hn) (Dn (env_narrow_sub_change x W W' E E' Hn HR))
  | isub_n_sub_change2 : forall x W W' E E' (Hn : env_narrow E E') (HR : sub E' W' W),
      isub (Dsub HR) (Dn (env_narrow_sub_change x W W' E E' Hn HR))
  | isub_n_qua_keep : forall x Q E E' (Hn : env_narrow E E'),
      isub (Dn Hn) (Dn (env_narrow_qua_keep x Q E E' Hn))
  | isub_n_qua_change1 : forall x Q Q' E E' (Hn : env_narrow E E') (HR : subqual E' Q' Q),
      isub (Dn Hn) (Dn (env_narrow_qua_change x Q Q' E E' Hn HR))
  | isub_n_qua_change2 : forall x Q Q' E E' (Hn : env_narrow E E') (HR : subqual E' Q' Q),
      isub (Dsq HR) (Dn (env_narrow_qua_change x Q Q' E E' Hn HR))
  | isub_n_typ_keep : forall x T E E' (Hn : env_narrow E E'),
      isub (Dn Hn) (Dn (env_narrow_typ_keep x T E E' Hn)).

Scheme subqual_dep_ind := Induction for subqual Sort Prop.


Lemma typing_expr : forall E e T, typing E e T -> expr e.
Proof.
  intros E e T H. induction H; try (constructor; eauto).
  - (* abs *)
    apply (expr_abs L P V e1).
    + apply (wf_qua_qual E P); assumption.
    + apply (wf_qtyp_qtype E V).
      destruct (atom_fresh L) as [x Hx].
      apply (wf_env_typ_head x V E).
      apply (typing_wf_env (x ~ bind_typ V ++ E) (open_ee e1 x) T1).
      apply H0; exact Hx.
    + intros x Hx. apply H1; exact Hx.
  - (* tabs *)
    apply (expr_tabs L P V e1).
    + apply (wf_qua_qual E P); assumption.
    + apply (wf_typ_type E V).
      destruct (atom_fresh L) as [x Hx].
      apply (wf_env_sub_head x V E).
      apply (typing_wf_env (x ~ bind_sub V ++ E) (open_te e1 x) (open_tqt T1 x)).
      apply H0; exact Hx.
    + intros x Hx. apply H1; exact Hx.
  - (* tapp type argument *)
    apply (wf_typ_type E T). apply (sub_wf E T T1); assumption.
  - (* qabs *)
    apply (expr_qabs L P Q e1).
    + apply (wf_qua_qual E P); assumption.
    + apply (wf_qua_qual E Q).
      destruct (atom_fresh L) as [x Hx].
      apply (wf_env_qua_head x Q E).
      apply (typing_wf_env (x ~ bind_qua Q ++ E) (open_qe e1 x) (open_qqt T1 x)).
      apply H0; exact Hx.
    + intros x Hx. apply H1; exact Hx.
  - (* qapp qualifier *)
    apply (wf_qua_qual E Q). apply (subqual_wf E Q Q1); assumption.
  - (* sub *) assumption.
  - (* let *)
    eapply expr_let; eauto.
  - (* inl qual *) apply (wf_qua_qual E P); assumption.
  - (* inr qual *) apply (wf_qua_qual E P); assumption.
  - (* case *)
    eapply expr_case; eauto.
  - (* pair qual *) apply (wf_qua_qual E P); assumption.
  - (* upqual qual *) apply (wf_qua_qual E P). apply (subqual_wf E Q P); assumption.
  - (* check qual *) apply (wf_qua_qual E P). apply (subqual_wf E Q P); assumption.
Qed.

Lemma typing_body_e : forall L E T1 T2 e2,
  (forall x : atom, x `notin` L ->
     typing (x ~ bind_typ T1 ++ E) (open_ee e2 x) T2) ->
  body_e e2.
Proof.
  intros L E T1 T2 e2 H.
  exists L. intros x Hx.
  apply (typing_expr (x ~ bind_typ T1 ++ E) (open_ee e2 x) T2).
  apply H; exact Hx.
Qed.

Lemma typing_body_e_var : forall L E T1 T2 v,
  (forall x : atom, x `notin` L ->
     typing (x ~ bind_typ T1 ++ E) (open_ee v x) T2) ->
  body_e v.
Proof. intros. apply typing_body_e with (L:=L) (E:=E) (T1:=T1) (T2:=T2); auto. Qed.

Lemma value_expr : forall v, value v -> expr v.
Proof.
  intros v H. induction H; try assumption; try (constructor; auto).
Qed.

Lemma sub_all_arrow_inv : forall E S1 S2 T1 T2,
  sub E (typ_all S1 S2) (typ_arrow T1 T2) -> False.
Proof. intros. inversion H. Qed.

Lemma sub_all_sum_inv : forall E S1 S2 T1 T2,
  sub E (typ_all S1 S2) (typ_sum T1 T2) -> False.
Proof. intros. inversion H. Qed.

Lemma sub_all_pair_inv : forall E S1 S2 T1 T2,
  sub E (typ_all S1 S2) (typ_pair T1 T2) -> False.
Proof. intros. inversion H. Qed.

Lemma sub_arrow_all_inv : forall E S1 S2 T1 T2,
  sub E (typ_arrow S1 S2) (typ_all T1 T2) -> False.
Proof. intros. inversion H. Qed.

Lemma sub_arrow_sum_inv : forall E S1 S2 T1 T2,
  sub E (typ_arrow S1 S2) (typ_sum T1 T2) -> False.
Proof. intros. inversion H. Qed.

Lemma sub_arrow_pair_inv : forall E S1 S2 T1 T2,
  sub E (typ_arrow S1 S2) (typ_pair T1 T2) -> False.
Proof. intros. inversion H. Qed.

Lemma sub_qall_arrow_inv : forall E S1 S2 T1 T2,
  sub E (typ_qall S1 S2) (typ_arrow T1 T2) -> False.
Proof. intros. inversion H. Qed.

Lemma sub_qall_all_inv : forall E S1 S2 T1 T2,
  sub E (typ_qall S1 S2) (typ_all T1 T2) -> False.
Proof. intros. inversion H. Qed.

Lemma sub_qall_sum_inv : forall E S1 S2 T1 T2,
  sub E (typ_qall S1 S2) (typ_sum T1 T2) -> False.
Proof. intros. inversion H. Qed.

Lemma sub_qall_pair_inv : forall E S1 S2 T1 T2,
  sub E (typ_qall S1 S2) (typ_pair T1 T2) -> False.
Proof. intros. inversion H. Qed.

Lemma sub_sum_arrow_inv : forall E S1 S2 T1 T2,
  sub E (typ_sum S1 S2) (typ_arrow T1 T2) -> False.
Proof. intros. inversion H. Qed.

Lemma sub_sum_all_inv : forall E S1 S2 T1 T2,
  sub E (typ_sum S1 S2) (typ_all T1 T2) -> False.
Proof. intros. inversion H. Qed.

Lemma sub_sum_pair_inv : forall E S1 S2 T1 T2,
  sub E (typ_sum S1 S2) (typ_pair T1 T2) -> False.
Proof. intros. inversion H. Qed.

Lemma sub_pair_arrow_inv : forall E S1 S2 T1 T2,
  sub E (typ_pair S1 S2) (typ_arrow T1 T2) -> False.
Proof. intros. inversion H. Qed.

Lemma sub_pair_all_inv : forall E S1 S2 T1 T2,
  sub E (typ_pair S1 S2) (typ_all T1 T2) -> False.
Proof. intros. inversion H. Qed.

Lemma sub_pair_sum_inv : forall E S1 S2 T1 T2,
  sub E (typ_pair S1 S2) (typ_sum T1 T2) -> False.
Proof. intros. inversion H. Qed.

Lemma sub_target_fvar_inv : forall E S X,
  sub E S (typ_fvar X) -> exists Y, S = typ_fvar Y.
Proof. intros. inversion H; subst; eauto. Qed.

Lemma value_typing_fvar_false : forall E e Q X,
  typing E e (qtyp_qtyp Q (typ_fvar X)) -> value e -> False.
Proof.
  intros E e Q X Hty Hval.
  remember (qtyp_qtyp Q (typ_fvar X)) as R eqn:HR.
  revert Q X Hval HR.
  induction Hty; intros Q0 X0 Hval HR.
  - inversion Hval.
  - inversion HR.
  - inversion Hval.
  - inversion HR.
  - inversion Hval.
  - inversion HR.
  - inversion Hval.
  - (* sub *)
    subst T.
    inversion H; subst.
    match goal with
    | Hs : subqual ?E ?Q1 ?Q2, Hsub : sub ?E ?S (typ_fvar X0) |- _ =>
        destruct (sub_target_fvar_inv E S X0 Hsub) as [Y HY]; subst;
        eapply IHHty; [ exact Hval | reflexivity ]
    end.
  - inversion Hval.
  - inversion HR.
  - inversion HR.
  - inversion Hval.
  - inversion HR.
  - inversion Hval.
  - inversion Hval.
  - inversion Hval.
  - inversion Hval.
Qed.

Lemma sub_target_arrow_inv : forall E S T1 T2,
  sub E S (typ_arrow T1 T2) ->
  (exists S1 S2, S = typ_arrow S1 S2) \/ (exists X, S = typ_fvar X).
Proof. intros. inversion H; subst; eauto. Qed.

Lemma typing_value_abs : forall E e Q T1 T2,
  typing E e (qtyp_qtyp Q (typ_arrow T1 T2)) -> value e ->
  exists P V e1, e = exp_abs P V e1.
Proof.
  intros E e Q T1 T2 Hty Hval.
  remember (qtyp_qtyp Q (typ_arrow T1 T2)) as R eqn:HR.
  revert Q T1 T2 Hval HR.
  induction Hty; intros Q0 Ta Tb Hval HR.
  - inversion Hval.
  - exists P, V, e1. reflexivity.
  - inversion Hval.
  - inversion HR.
  - inversion Hval.
  - inversion HR.
  - inversion Hval.
  - (* sub *)
    subst T. inversion H; subst.
    match goal with
    | Hs : subqual ?E ?Q1 ?Q2, Hsub : sub ?E ?S (typ_arrow Ta Tb) |- _ =>
        destruct (sub_target_arrow_inv E S Ta Tb Hsub) as [[S1 [S2 HS]]|[X HX]]; subst
    end.
    + eapply IHHty; [ exact Hval | reflexivity ].
    + exfalso. eapply (value_typing_fvar_false E e Q1 X); [ exact Hty | exact Hval ].
  - inversion Hval.
  - inversion HR.
  - inversion HR.
  - inversion Hval.
  - inversion HR.
  - inversion Hval.
  - inversion Hval.
  - inversion Hval.
  - inversion Hval.
Qed.

Lemma sub_target_all_inv : forall E S T1 T2,
  sub E S (typ_all T1 T2) ->
  (exists S1 S2, S = typ_all S1 S2) \/ (exists X, S = typ_fvar X).
Proof. intros. inversion H; subst; eauto. Qed.

Lemma sub_target_qall_inv : forall E S T1 T2,
  sub E S (typ_qall T1 T2) ->
  (exists S1 S2, S = typ_qall S1 S2) \/ (exists X, S = typ_fvar X).
Proof. intros. inversion H; subst; eauto. Qed.

Lemma sub_target_sum_inv : forall E S T1 T2,
  sub E S (typ_sum T1 T2) ->
  (exists S1 S2, S = typ_sum S1 S2) \/ (exists X, S = typ_fvar X).
Proof. intros. inversion H; subst; eauto. Qed.

Lemma sub_target_pair_inv : forall E S T1 T2,
  sub E S (typ_pair T1 T2) ->
  (exists S1 S2, S = typ_pair S1 S2) \/ (exists X, S = typ_fvar X).
Proof. intros. inversion H; subst; eauto. Qed.

Lemma typing_value_tabs : forall E e Q T1 T2,
  typing E e (qtyp_qtyp Q (typ_all T1 T2)) -> value e ->
  exists P V e1, e = exp_tabs P V e1.
Proof.
  intros E e Q T1 T2 Hty Hval.
  remember (qtyp_qtyp Q (typ_all T1 T2)) as R eqn:HR.
  revert Q T1 T2 Hval HR.
  induction Hty; intros Q0 Ta Tb Hval HR.
  - inversion Hval.
  - inversion HR.
  - inversion Hval.
  - exists P, V, e1. reflexivity.
  - inversion Hval.
  - inversion HR.
  - inversion Hval.
  - (* sub *)
    subst T. inversion H; subst.
    match goal with
    | Hs : subqual ?E ?Q1 ?Q2, Hsub : sub ?E ?S (typ_all Ta Tb) |- _ =>
        destruct (sub_target_all_inv E S Ta Tb Hsub) as [[S1 [S2 HS]]|[X HX]]; subst
    end.
    + eapply IHHty; [ exact Hval | reflexivity ].
    + exfalso. eapply (value_typing_fvar_false E e Q1 X); [ exact Hty | exact Hval ].
  - inversion Hval.
  - inversion HR.
  - inversion HR.
  - inversion Hval.
  - inversion HR.
  - inversion Hval.
  - inversion Hval.
  - inversion Hval.
  - inversion Hval.
Qed.

Lemma typing_value_qabs : forall E e Q T1 T2,
  typing E e (qtyp_qtyp Q (typ_qall T1 T2)) -> value e ->
  exists P Qq e1, e = exp_qabs P Qq e1.
Proof.
  intros E e Q T1 T2 Hty Hval.
  remember (qtyp_qtyp Q (typ_qall T1 T2)) as R eqn:HR.
  revert Q T1 T2 Hval HR.
  induction Hty; intros Q0 Ta Tb Hval HR.
  - inversion Hval.
  - inversion HR.
  - inversion Hval.
  - inversion HR.
  - inversion Hval.
  - eexists; eexists; eexists; reflexivity.
  - inversion Hval.
  - (* sub *)
    subst T. inversion H; subst.
    match goal with
    | Hs : subqual ?E ?Q1 ?Q2, Hsub : sub ?E ?S (typ_qall Ta Tb) |- _ =>
        destruct (sub_target_qall_inv E S Ta Tb Hsub) as [[S1 [S2 HS]]|[X HX]]; subst
    end.
    + eapply IHHty; [ exact Hval | reflexivity ].
    + exfalso. eapply (value_typing_fvar_false E e Q1 X); [ exact Hty | exact Hval ].
  - inversion Hval.
  - inversion HR.
  - inversion HR.
  - inversion Hval.
  - inversion HR.
  - inversion Hval.
  - inversion Hval.
  - inversion Hval.
  - inversion Hval.
Qed.

Lemma typing_value_sum : forall E e Q T1 T2,
  typing E e (qtyp_qtyp Q (typ_sum T1 T2)) -> value e ->
  (exists P e1, e = exp_inl P e1) \/ (exists P e1, e = exp_inr P e1).
Proof.
  intros E e Q T1 T2 Hty Hval.
  remember (qtyp_qtyp Q (typ_sum T1 T2)) as R eqn:HR.
  revert Q T1 T2 Hval HR.
  induction Hty; intros Q0 Ta Tb Hval HR.
  - inversion Hval.
  - inversion HR.
  - inversion Hval.
  - inversion HR.
  - inversion Hval.
  - inversion HR.
  - inversion Hval.
  - (* sub *)
    subst T. inversion H; subst.
    match goal with
    | Hs : subqual ?E ?Q1 ?Q2, Hsub : sub ?E ?S (typ_sum Ta Tb) |- _ =>
        destruct (sub_target_sum_inv E S Ta Tb Hsub) as [[S1 [S2 HS]]|[X HX]]; subst
    end.
    + eapply IHHty; [ exact Hval | reflexivity ].
    + exfalso. eapply (value_typing_fvar_false E e Q1 X); [ exact Hty | exact Hval ].
  - inversion Hval.
  - left; eexists; eexists; reflexivity.
  - right; eexists; eexists; reflexivity.
  - inversion Hval.
  - inversion HR.
  - inversion Hval.
  - inversion Hval.
  - inversion Hval.
  - inversion Hval.
Qed.

Lemma typing_value_pair : forall E e Q T1 T2,
  typing E e (qtyp_qtyp Q (typ_pair T1 T2)) -> value e ->
  exists P e1 e2, e = exp_pair P e1 e2.
Proof.
  intros E e Q T1 T2 Hty Hval.
  remember (qtyp_qtyp Q (typ_pair T1 T2)) as R eqn:HR.
  revert Q T1 T2 Hval HR.
  induction Hty; intros Q0 Ta Tb Hval HR.
  - inversion Hval.
  - inversion HR.
  - inversion Hval.
  - inversion HR.
  - inversion Hval.
  - inversion HR.
  - inversion Hval.
  - (* sub *)
    subst T. inversion H; subst.
    match goal with
    | Hs : subqual ?E ?Q1 ?Q2, Hsub : sub ?E ?S (typ_pair Ta Tb) |- _ =>
        destruct (sub_target_pair_inv E S Ta Tb Hsub) as [[S1 [S2 HS]]|[X HX]]; subst
    end.
    + eapply IHHty; [ exact Hval | reflexivity ].
    + exfalso. eapply (value_typing_fvar_false E e Q1 X); [ exact Hty | exact Hval ].
  - inversion Hval.
  - inversion HR.
  - inversion HR.
  - inversion Hval.
  - eexists; eexists; eexists; reflexivity.
  - inversion Hval.
  - inversion Hval.
  - inversion Hval.
  - inversion Hval.
Qed.

Lemma le_top_b : forall a : B, a ≤ top.
Proof.
  intros a.
  apply (proj2 (join_is_lub a top top)).
  rewrite join_top.
  apply Fsub.ExtendedBase.Lattice.reflexive.
Qed.

Lemma bot_le_b : forall a : B, bot ≤ a.
Proof.
  intros a.
  apply (proj2 (meet_consistent bot a)).
  rewrite meet_commutative, meet_bot. reflexivity.
Qed.

Lemma join_le_l : forall a b : B, a ≤ a ⊔ b.
Proof. intros. apply (join_prime a b a). left. apply Fsub.ExtendedBase.Lattice.reflexive. Qed.

Lemma join_le_r : forall a b : B, b ≤ a ⊔ b.
Proof. intros. apply (join_prime a b b). right. apply Fsub.ExtendedBase.Lattice.reflexive. Qed.

Lemma meet_le_l : forall a b : B, a ⊓ b ≤ a.
Proof. intros. apply (meet_prime a b a). left. apply Fsub.ExtendedBase.Lattice.reflexive. Qed.

Lemma meet_le_r : forall a b : B, a ⊓ b ≤ b.
Proof. intros. apply (meet_prime a b b). right. apply Fsub.ExtendedBase.Lattice.reflexive. Qed.

Lemma le_trans_b : forall a b c : B, a ≤ b -> b ≤ c -> a ≤ c.
Proof. intros a b c H1 H2. exact (Fsub.ExtendedBase.Lattice.transitive a b c H1 H2). Qed.



Lemma concretize_join_some : forall Q1 Q2 b,
  concretize (qua_join Q1 Q2) = Some b ->
  exists b1 b2, concretize Q1 = Some b1 /\ concretize Q2 = Some b2 /\ b = b1 ⊔ b2.
Proof.
  intros Q1 Q2 b H.
  destruct (concretize Q1) as [b1|] eqn:H1;
    [| exfalso; simpl in H; rewrite H1 in H; discriminate].
  destruct (concretize Q2) as [b2|] eqn:H2;
    [| exfalso; simpl in H; rewrite H1, H2 in H; discriminate].
  simpl in H. rewrite H1, H2 in H. simpl in H. inversion H; subst.
  exists b1, b2. split; [reflexivity|split; [reflexivity|reflexivity]].
Qed.

Lemma concretize_meet_some : forall Q1 Q2 b,
  concretize (qua_meet Q1 Q2) = Some b ->
  exists b1 b2, concretize Q1 = Some b1 /\ concretize Q2 = Some b2 /\ b = b1 ⊓ b2.
Proof.
  intros Q1 Q2 b H.
  destruct (concretize Q1) as [b1|] eqn:H1;
    [| exfalso; simpl in H; rewrite H1 in H; discriminate].
  destruct (concretize Q2) as [b2|] eqn:H2;
    [| exfalso; simpl in H; rewrite H1, H2 in H; discriminate].
  simpl in H. rewrite H1, H2 in H. simpl in H. inversion H; subst.
  exists b1, b2. split; [reflexivity|split; [reflexivity|reflexivity]].
Qed.

Lemma subqual_concretize_ord : forall E Q P,
  subqual E Q P ->
  forall b1 b2, concretize Q = Some b1 -> concretize P = Some b2 -> b1 ≤ b2.
Proof.
  intros E Q P Hs.
  induction Hs as [E0 Q0 w wq | E0 Q0 w wq
    | E0 Q' Q0 R0 b0 s1 IH1 Hc s2 IH2
    | E0 Q' Q0 R0 b0 s1 IH1 Hc s2 IH2
    | E0 bb1 bb2 w Ho
    | E0 X0 w wq
    | R0 E0 Q0 X0 Hb s IH
    | E0 R1 R2 Q0 s IH w
    | E0 R1 R2 Q0 w s IH
    | E0 R1 R2 Q0 s1 IH1 s2 IH2
    | E0 R1 R2 Q0 s IH w
    | E0 R1 R2 Q0 w s IH
    | E0 R1 R2 Q0 s1 IH1 s2 IH2]; intros b1 b2 HQ HP.
  - simpl in HP. inversion HP; subst. apply le_top_b.
  - simpl in HQ. inversion HQ; subst. apply bot_le_b.
  - (* eval_elim *)
    assert (H1 : b1 ≤ b0) by (apply IH1; assumption).
    assert (H2 : b0 ≤ b2) by (apply IH2; [reflexivity|exact HP]).
    eapply le_trans_b; eassumption.
  - (* eval_intro *)
    assert (H1 : b0 ≤ b2) by (apply IH1; assumption).
    assert (H2 : b1 ≤ b0) by (apply IH2; [exact HQ|reflexivity]).
    eapply le_trans_b; eassumption.
  - (* lift_elem *)
    simpl in HQ; simpl in HP. inversion HQ; inversion HP; subst.
    exact Ho.
  - (* refl_qvar *) simpl in HQ; discriminate.
  - (* trans_qvar *) simpl in HQ; discriminate.
  - (* join_inl *)
    destruct (concretize_join_some R1 R2 b2 HP) as [b2a [b2b [HP1 [HP2 Hb2]]]].
    assert (H1 : b1 ≤ b2a) by (apply IH; assumption).
    rewrite Hb2. eapply le_trans_b; [exact H1|apply join_le_l].
  - (* join_inr *)
    destruct (concretize_join_some R1 R2 b2 HP) as [b2a [b2b [HP1 [HP2 Hb2]]]].
    assert (H1 : b1 ≤ b2b) by (apply IH; assumption).
    rewrite Hb2. eapply le_trans_b; [exact H1|apply join_le_r].
  - (* join_elim *)
    destruct (concretize_join_some R1 R2 b1 HQ) as [b1a [b1b [HQ1 [HQ2 Hb1]]]].
    assert (H1 : b1a ≤ b2) by (apply IH1; assumption).
    assert (H2 : b1b ≤ b2) by (apply IH2; assumption).
    rewrite Hb1. apply (proj1 (join_is_lub b1a b1b b2)). split; assumption.
  - (* meet_eliml *)
    destruct (concretize_meet_some R1 R2 b1 HQ) as [b1a [b1b [HQ1 [HQ2 Hb1]]]].
    assert (H1 : b1a ≤ b2) by (apply IH; assumption).
    rewrite Hb1. eapply le_trans_b; [apply meet_le_l|exact H1].
  - (* meet_elimr *)
    destruct (concretize_meet_some R1 R2 b1 HQ) as [b1a [b1b [HQ1 [HQ2 Hb1]]]].
    assert (H1 : b1b ≤ b2) by (apply IH; assumption).
    rewrite Hb1. eapply le_trans_b; [apply meet_le_r|exact H1].
  - (* meet_intro *)
    destruct (concretize_meet_some R1 R2 b2 HP) as [b2a [b2b [HP1 [HP2 Hb2]]]].
    assert (H1 : b1 ≤ b2a) by (apply IH1; assumption).
    assert (H2 : b1 ≤ b2b) by (apply IH2; assumption).
    rewrite Hb2. apply (proj1 (meet_is_glb b2a b2b b1)). split; assumption.
Qed.


Scheme wf_qua_dep_ind := Induction for wf_qua Sort Prop.

Lemma concretize_wf_empty_aux : forall E Q,
  wf_qua E Q -> E = (@nil (atom * binding)) ->
  exists b, concretize Q = Some b.
Proof.
  intros E Q H.
  refine (wf_qua_dep_ind (fun E Q H => E = (@nil (atom * binding)) -> exists b, concretize Q = Some b) _ _ _ _ E Q H).
  - intros E0 b HE. exists b. reflexivity.
  - intros R E0 X Hb HE. subst E0. apply binds_nil_iff in Hb. contradiction.
  - intros E0 Q1 Q2 H1 IH1 H2 IH2 HE.
    destruct (IH1 HE) as [b1 Hb1]. destruct (IH2 HE) as [b2 Hb2].
    exists (b1 ⊓ b2). simpl. rewrite Hb1, Hb2. reflexivity.
  - intros E0 Q1 Q2 H1 IH1 H2 IH2 HE.
    destruct (IH1 HE) as [b1 Hb1]. destruct (IH2 HE) as [b2 Hb2].
    exists (b1 ⊔ b2). simpl. rewrite Hb1, Hb2. reflexivity.
Qed.

Lemma concretize_wf_empty : forall Q,
  wf_qua (@nil (atom * binding)) Q -> exists b, concretize Q = Some b.
Proof.
  intros Q H. eapply concretize_wf_empty_aux; [exact H|reflexivity].
Qed.


From Stdlib Require Import Program.Equality.

Lemma typing_abs_qual_le : forall E P0 V body Q T,
  typing E (exp_abs P0 V body) (qtyp_qtyp Q T) -> subqual E P0 Q.
Proof.
  intros E P0 V body Q T Hty.
  dependent induction Hty.
  - apply subqual_refl.
    + destruct (atom_fresh L) as [x Hx].
      apply (wf_env_head_inv x (bind_typ V) E).
      apply (typing_wf_env (x ~ bind_typ V ++ E) (open_ee body x) T1).
      apply H0; exact Hx.
    + exact H.
  - inversion H; subst.
    assert (H1 : subqual E P0 Q1) by (eapply IHHty; reflexivity).
    eapply subqual_trans; [exact H1|exact H4].
Qed.

Lemma typing_tabs_qual_le : forall E P0 V body Q T,
  typing E (exp_tabs P0 V body) (qtyp_qtyp Q T) -> subqual E P0 Q.
Proof.
  intros E P0 V body Q T Hty.
  dependent induction Hty.
  - apply subqual_refl.
    + destruct (atom_fresh L) as [x Hx].
      apply (wf_env_head_inv x (bind_sub V) E).
      apply (typing_wf_env (x ~ bind_sub V ++ E) (open_te body x) (open_tqt T1 x)).
      apply H0; exact Hx.
    + exact H.
  - inversion H; subst.
    assert (H1 : subqual E P0 Q1) by (eapply IHHty; reflexivity).
    eapply subqual_trans; [exact H1|exact H4].
Qed.

Lemma typing_qabs_qual_le : forall E P0 Q0 body Q T,
  typing E (exp_qabs P0 Q0 body) (qtyp_qtyp Q T) -> subqual E P0 Q.
Proof.
  intros E P0 Q0 body Q T Hty.
  dependent induction Hty.
  - apply subqual_refl.
    + destruct (atom_fresh L) as [x Hx].
      apply (wf_env_head_inv x (bind_qua Q0) E).
      apply (typing_wf_env (x ~ bind_qua Q0 ++ E) (open_qe body x) (open_qqt T1 x)).
      apply H0; exact Hx.
    + exact H.
  - inversion H; subst.
    assert (H1 : subqual E P0 Q1) by (eapply IHHty; reflexivity).
    eapply subqual_trans; [exact H1|exact H4].
Qed.

Lemma typing_inl_qual_le : forall E P0 body Q T,
  typing E (exp_inl P0 body) (qtyp_qtyp Q T) -> subqual E P0 Q.
Proof.
  intros E P0 body Q T Hty.
  dependent induction Hty.
  - inversion H; subst.
    assert (H1 : subqual E P0 Q1) by (eapply IHHty; reflexivity).
    eapply subqual_trans; [exact H1|exact H4].
  - apply subqual_refl.
    + apply (typing_wf_env E body T1). exact Hty.
    + exact H.
Qed.

Lemma typing_inr_qual_le : forall E P0 body Q T,
  typing E (exp_inr P0 body) (qtyp_qtyp Q T) -> subqual E P0 Q.
Proof.
  intros E P0 body Q T Hty.
  dependent induction Hty.
  - inversion H; subst.
    assert (H1 : subqual E P0 Q1) by (eapply IHHty; reflexivity).
    eapply subqual_trans; [exact H1|exact H4].
  - apply subqual_refl.
    + apply (typing_wf_env E body T2). exact Hty.
    + exact H.
Qed.

Lemma typing_pair_qual_le : forall E P0 body1 body2 Q T,
  typing E (exp_pair P0 body1 body2) (qtyp_qtyp Q T) -> subqual E P0 Q.
Proof.
  intros E P0 body1 body2 Q T Hty.
  dependent induction Hty.
  - inversion H; subst.
    assert (H1 : subqual E P0 Q1) by (eapply IHHty; reflexivity).
    eapply subqual_trans; [exact H1|exact H4].
  - apply subqual_refl.
    + match goal with HT : typing E _ _ |- _ => exact (typing_wf_env E _ _ HT) end.
    + exact H.
Qed.


(* Motive for mutual transitivity and narrowing of subtyping. *)
Definition Psub (E : env) (S T : typ) : Prop :=
  (forall U, sub E T U -> sub E S U) /\
  (forall W, sub E W S -> sub E W T) /\
  (forall E', env_narrow E E' -> sub E' S T) /\
  (forall E', env_narrow E E' -> forall U, sub E' T U -> sub E' S U) /\
  (forall E', env_narrow E E' -> forall W, sub E' W S -> sub E' W T).

Definition Pqt (E : env) (S T : qtyp) : Prop :=
  (forall U, subqtype E T U -> subqtype E S U) /\
  (forall W, subqtype E W S -> subqtype E W T) /\
  (forall E', env_narrow E E' -> subqtype E' S T) /\
  (forall E', env_narrow E E' -> forall U, subqtype E' T U -> subqtype E' S U) /\
  (forall E', env_narrow E E' -> forall W, subqtype E' W S -> subqtype E' W T).

Lemma env_narrow_ctx_sub : forall ctx X W1 W2 E,
  sub E W2 W1 ->
  env_narrow (ctx ++ (X, bind_sub W1) :: E) (ctx ++ (X, bind_sub W2) :: E).
Proof.
  induction ctx as [| [y b] ctx IH]; intros X W1 W2 E Rel.
  - simpl. apply env_narrow_sub_change; [ apply env_narrow_nil | exact Rel ].
  - simpl. destruct b.
    + apply env_narrow_sub_keep. apply IH. exact Rel.
    + apply env_narrow_typ_keep. apply IH. exact Rel.
    + apply env_narrow_qua_keep. apply IH. exact Rel.
Qed.

Lemma env_narrow_ctx_qua : forall ctx X Q1 Q2 E,
  subqual E Q2 Q1 ->
  env_narrow (ctx ++ (X, bind_qua Q1) :: E) (ctx ++ (X, bind_qua Q2) :: E).
Proof.
  induction ctx as [| [y b] ctx IH]; intros X Q1 Q2 E Rel.
  - simpl. apply env_narrow_qua_change; [ apply env_narrow_nil | exact Rel ].
  - simpl. destruct b.
    + apply env_narrow_sub_keep. apply IH. exact Rel.
    + apply env_narrow_typ_keep. apply IH. exact Rel.
    + apply env_narrow_qua_keep. apply IH. exact Rel.
Qed.

Lemma binds_narrow_split : forall ctx X W1 E0 Y U,
  uniq (ctx ++ (X, bind_sub W1) :: E0) ->
  binds Y (bind_sub U) (ctx ++ (X, bind_sub W1) :: E0) ->
  (Y = X /\ U = W1) \/ binds Y (bind_sub U) (ctx ++ E0).
Proof.
  intros ctx X W1 E0 Y U Huniq Hb.
  pose proof (uniq_app_2 _ _ _ Huniq) as HuniqF.
  rewrite (binds_app_uniq_iff binding Y (bind_sub U) ctx ((X, bind_sub W1) :: E0) Huniq) in Hb.
  destruct Hb as [[Hbctx HnotF]|[HbF Hnotctx]].
  - right. apply binds_app_2. exact Hbctx.
  - rewrite (binds_cons_uniq_iff binding Y X (bind_sub U) (bind_sub W1) E0 HuniqF) in HbF.
    destruct HbF as [[HY [HU HnotE]]|[HbE HYneq]].
    + left. split. exact HY. inversion HU. reflexivity.
    + right. apply binds_app_3 with (E := ctx). exact HbE.
Qed.

Lemma binds_ctx_new : forall ctx X0 W2 E0 X U,
  binds X (bind_sub U) (ctx ++ E0) ->
  binds X (bind_sub U) (ctx ++ (X0, bind_sub W2) :: E0).
Proof.
  intros ctx X0 W2 E0 X U H.
  apply binds_app_iff in H. destruct H as [H|H].
  - apply binds_app_l. exact H.
  - apply binds_app_r. apply binds_cons. exact H.
Qed.

Definition Nsub (E : env) (S T : typ) (D : sub E S T) : Prop :=
  forall ctx X W1 W2 E0 (Rel : sub E0 W2 W1)
    (Grel : forall ctx' U,
       sub (ctx' ++ (X, bind_sub W2) :: E0) W1 U ->
       sub (ctx' ++ (X, bind_sub W2) :: E0) W2 U),
  E = ctx ++ (X, bind_sub W1) :: E0 ->
  sub (ctx ++ (X, bind_sub W2) :: E0) S T.

Definition Nqt (E : env) (S T : qtyp) (D : subqtype E S T) : Prop :=
  forall ctx X W1 W2 E0 (Rel : sub E0 W2 W1)
    (Grel : forall ctx' U,
       sub (ctx' ++ (X, bind_sub W2) :: E0) W1 U ->
       sub (ctx' ++ (X, bind_sub W2) :: E0) W2 U),
  E = ctx ++ (X, bind_sub W1) :: E0 ->
  subqtype (ctx ++ (X, bind_sub W2) :: E0) S T.

Lemma Nsub_proof : forall E S T (D : sub E S T), Nsub E S T D.
Proof.
  apply (sub_mut_ind Nsub Nqt).
  - (* top *) intros E S w w0. unfold Nsub.
    intros ctx X W1 W2 E0 Rel Grel eq_refl. subst E.
    pose proof (env_narrow_ctx_sub ctx X W1 W2 E0 Rel) as Hn.
    apply sub_top.
    + apply (wf_env_narrow _ _ w Hn).
    + apply (wf_typ_narrow _ _ S Hn w0).
  - (* refl *) intros E X w w0. unfold Nsub.
    intros ctx X0 W1 W2 E0 Rel Grel eq_refl. subst E.
    pose proof (env_narrow_ctx_sub ctx X0 W1 W2 E0 Rel) as Hn.
    apply sub_refl_tvar.
    + apply (wf_env_narrow _ _ w Hn).
    + apply (wf_typ_narrow _ _ X Hn w0).
  - (* trans_tvar *) intros U E T X b s IH. unfold Nsub.
    intros ctx X0 W1 W2 E0 Rel Grel eq_refl. subst E.
    assert (Hwf : wf_env (ctx ++ (X0, bind_sub W1) :: E0)).
    { apply (sub_wf_env _ _ _ (sub_trans_tvar U _ T _ b s)). }
    pose proof (wf_env_uniq _ Hwf) as Hun.
    destruct (binds_narrow_split ctx X0 W1 E0 X U Hun b) as [[Heq HU]|Hb].
    + subst X. subst U.
      apply (sub_trans_tvar W2 (ctx ++ (X0, bind_sub W2) :: E0) T X0).
      * apply binds_app_r. apply binds_cons_2; auto.
      * apply (Grel ctx T). apply (IH ctx X0 W1 W2 E0 Rel Grel eq_refl).
    + apply (sub_trans_tvar U (ctx ++ (X0, bind_sub W2) :: E0) T X).
      * apply binds_ctx_new. exact Hb.
      * apply (IH ctx X0 W1 W2 E0 Rel Grel eq_refl).
  - (* arrow *) intros E S1 S2 T1 T2 s1 IH1 s2 IH2. unfold Nsub.
    intros ctx X W1 W2 E0 Rel Grel eq_refl. subst E.
    apply sub_arrow.
    + apply (IH1 ctx X W1 W2 E0 Rel Grel eq_refl).
    + apply (IH2 ctx X W1 W2 E0 Rel Grel eq_refl).
  - (* all *) intros L E S1 S2 T1 T2 s1 IH1 s2 IH2. unfold Nsub.
    intros ctx X W1 W2 E0 Rel Grel eq_refl. subst E.
    apply (sub_all (union L (add X (dom ctx)))).
    + apply (IH1 ctx X W1 W2 E0 Rel Grel eq_refl).
    + intros Y HY.
      assert (HYL : Y `notin` L) by (simpl in HY; fsetdec).
      apply (IH2 Y HYL ((Y, bind_sub T1) :: ctx) X W1 W2 E0 Rel Grel).
      reflexivity.
  - (* qall *) intros L E S1 S2 T1 T2 sq s2 IH2. unfold Nsub.
    intros ctx X W1 W2 E0 Rel Grel eq_refl. subst E.
    pose proof (env_narrow_ctx_sub ctx X W1 W2 E0 Rel) as Hn.
    apply (sub_qall (union L (add X (dom ctx)))).
    + apply (subqual_narrow _ _ T1 S1 (subqual_wf_env _ _ _ sq) sq Hn).
    + intros Y HY.
      assert (HYL : Y `notin` L) by (simpl in HY; fsetdec).
      apply (IH2 Y HYL ((Y, bind_qua T1) :: ctx) X W1 W2 E0 Rel Grel).
      reflexivity.
  - (* sum *) intros E S1 S2 T1 T2 s1 IH1 s2 IH2. unfold Nsub.
    intros ctx X W1 W2 E0 Rel Grel eq_refl. subst E.
    apply sub_sum.
    + apply (IH1 ctx X W1 W2 E0 Rel Grel eq_refl).
    + apply (IH2 ctx X W1 W2 E0 Rel Grel eq_refl).
  - (* pair *) intros E S1 S2 T1 T2 s1 IH1 s2 IH2. unfold Nsub.
    intros ctx X W1 W2 E0 Rel Grel eq_refl. subst E.
    apply sub_pair.
    + apply (IH1 ctx X W1 W2 E0 Rel Grel eq_refl).
    + apply (IH2 ctx X W1 W2 E0 Rel Grel eq_refl).
  - (* qtyp *) intros E Q1 T1 Q2 T2 sq s IH. unfold Nqt.
    intros ctx X W1 W2 E0 Rel Grel eq_refl. subst E.
    pose proof (env_narrow_ctx_sub ctx X W1 W2 E0 Rel) as Hn.
    apply sub_qtyp_qtyp.
    + apply (subqual_narrow _ _ Q1 Q2 (subqual_wf_env _ _ _ sq) sq Hn).
    + apply (IH ctx X W1 W2 E0 Rel Grel eq_refl).
Qed.
Lemma Nqt_proof : forall E S T (D : subqtype E S T), Nqt E S T D.
Proof.
  intros E S T D. destruct D as [ED Q1 T1 Q2 T2 sq s]. simpl in *.
  unfold Nqt. intros ctx X W1 W2 Ebase Rel Grel HE. subst ED.
  pose proof (env_narrow_ctx_sub ctx X W1 W2 Ebase Rel) as Hn.
  apply sub_qtyp_qtyp.
  - apply (subqual_narrow _ _ Q1 Q2 (subqual_wf_env _ _ _ sq) sq Hn).
  - apply (Nsub_proof _ _ _ s ctx X W1 W2 Ebase Rel Grel eq_refl).
Qed.

Lemma sub_source_top_inv : forall E U, sub E typ_top U -> U = typ_top.
Proof.
  intros E U H. dependent induction H; try discriminate; reflexivity.
Qed.

Lemma sub_trans_to_fvar : forall E W X U,
  sub E W (typ_fvar X) -> sub E (typ_fvar X) U -> sub E W U.
Proof.
  intros E W X U H1 H2.
  remember (typ_fvar X) as R eqn:HR in H1.
  dependent induction H1; try discriminate HR.
  - rewrite <- HR in H2. exact H2.
  - eapply sub_trans_tvar; [ exact H | apply (IHsub HR H2) ].
Qed.

(* Context-parametric transitivity motives used for the remaining F/G proof. *)
Definition Fw (E : env) (S T : typ) (D : sub E S T) : Prop :=
  forall ctx W, sub (ctx ++ E) W S -> sub (ctx ++ E) W T.

Definition Gw (E : env) (S T : typ) (D : sub E S T) : Prop :=
  forall ctx U, sub (ctx ++ E) T U -> sub (ctx ++ E) S U.

Definition Fwq (E : env) (S T : qtyp) (D : subqtype E S T) : Prop :=
  forall ctx W, subqtype (ctx ++ E) W S -> subqtype (ctx ++ E) W T.

Definition Gwq (E : env) (S T : qtyp) (D : subqtype E S T) : Prop :=
  forall ctx U, subqtype (ctx ++ E) T U -> subqtype (ctx ++ E) S U.

(* Environment-inclusion formulation of transitivity, aligned with binder
   extension for the all/qall body cases. *)
Definition Fwi (E : env) (S T : typ) (D : sub E S T) : Prop :=
  forall E', env_incl E E' -> wf_env E' ->
    forall W, sub E' W S -> sub E' W T.

Definition Gwi (E : env) (S T : typ) (D : sub E S T) : Prop :=
  forall E', env_incl E E' -> wf_env E' ->
    forall U, sub E' T U -> sub E' S U.

Definition Fwiq (E : env) (S T : qtyp) (D : subqtype E S T) : Prop :=
  forall E', env_incl E E' -> wf_env E' ->
    forall W, subqtype E' W S -> subqtype E' W T.

Definition Gwiq (E : env) (S T : qtyp) (D : subqtype E S T) : Prop :=
  forall E', env_incl E E' -> wf_env E' ->
    forall U, subqtype E' T U -> subqtype E' S U.

Lemma env_incl_ctx_r : forall E ctx, env_incl E (ctx ++ E).
Proof.
  intros E ctx x b Hb. apply binds_app_r. exact Hb.
Qed.

Lemma env_incl_cons_r : forall E E' x b,
  env_incl E E' -> env_incl E (x ~ b ++ E').
Proof.
  intros E E' x b H x0 b0 Hb. apply binds_cons. apply H. exact Hb.
Qed.

Lemma env_incl_trans : forall E E' E'',
  env_incl E E' -> env_incl E' E'' -> env_incl E E''.
Proof.
  intros E E' E'' H1 H2 x b Hb. apply H2. apply H1. exact Hb.
Qed.

Lemma env_incl_ctx_mid : forall E ctx x b,
  env_incl E (ctx ++ (x, b) :: E).
Proof.
  intros E ctx x b y c Hy.
  apply binds_app_r. apply binds_cons. exact Hy.
Qed.


(* ================================================================== *)
(* Transitivity by middle-type size, narrowing, and term substitution *)
(* ================================================================== *)
From Stdlib Require Import Wellfounded.

(* ------------------------------------------------------------------ *)
(* Syntactic sizes                                                    *)
(* ------------------------------------------------------------------ *)

Fixpoint size_qua (Q : qua) : nat :=
  match Q with
  | qua_base _ => 1
  | qua_bvar _ => 1
  | qua_fvar _ => 1
  | qua_meet Q1 Q2 => 1 + size_qua Q1 + size_qua Q2
  | qua_join Q1 Q2 => 1 + size_qua Q1 + size_qua Q2
  end.

Fixpoint size_typ (T : typ) : nat :=
  match T with
  | typ_top => 1
  | typ_bvar _ => 1
  | typ_fvar _ => 1
  | typ_arrow T1 T2 => 1 + size_qtyp T1 + size_qtyp T2
  | typ_all T1 T2 => 1 + size_typ T1 + size_qtyp T2
  | typ_qall Q T => 1 + size_qua Q + size_qtyp T
  | typ_sum T1 T2 => 1 + size_qtyp T1 + size_qtyp T2
  | typ_pair T1 T2 => 1 + size_qtyp T1 + size_qtyp T2
  | typ_ref T => 1 + size_qtyp T
  end
with size_qtyp (T : qtyp) : nat :=
  match T with
  | qtyp_qtyp Q T => 1 + size_qua Q + size_typ T
  end.

Lemma size_qua_open_qq_one : forall Q K R,
  size_qua R = 1 -> size_qua (open_qq_rec K R Q) = size_qua Q.
Proof.
  induction Q; intros K R HR; simpl.
  - reflexivity.
  - destruct (K == n); [ exact HR | reflexivity ].
  - reflexivity.
  - rewrite IHQ1, IHQ2; auto.
  - rewrite IHQ1, IHQ2; auto.
Qed.

Lemma size_open_tt_one :
  (forall T, forall K (U : typ), size_typ U = 1 ->
     size_typ (open_tt_rec K U T) = size_typ T) /\
  (forall T : qtyp, forall K (U : typ), size_typ U = 1 ->
     size_qtyp (open_tqt_rec K U T) = size_qtyp T).
Proof.
  split.
  - apply (typ_mut_ind
      (fun T => forall K (U : typ), size_typ U = 1 ->
         size_typ (open_tt_rec K U T) = size_typ T)
      (fun T => forall K (U : typ), size_typ U = 1 ->
         size_qtyp (open_tqt_rec K U T) = size_qtyp T)).
    + intros; reflexivity.
    + intros n K U HU. simpl. destruct (K == n); [ exact HU | reflexivity ].
    + intros; reflexivity.
    + intros q1 IH1 q2 IH2 K U HU. simpl.
      rewrite (IH1 K U HU), (IH2 (S K) U HU). reflexivity.
    + intros T1 IH1 q IH2 K U HU. simpl.
      rewrite (IH1 K U HU), (IH2 (S K) U HU). reflexivity.
    + intros Q q IH K U HU. simpl.
      rewrite (IH (S K) U HU). reflexivity.
    + intros q1 IH1 q2 IH2 K U HU. simpl.
      rewrite (IH1 K U HU), (IH2 K U HU). reflexivity.
    + intros q1 IH1 q2 IH2 K U HU. simpl.
      rewrite (IH1 K U HU), (IH2 K U HU). reflexivity.
    + intros q IH K U HU. simpl. rewrite (IH K U HU). reflexivity.
    + intros Q T IH K U HU. simpl. rewrite (IH K U HU). reflexivity.
  - apply (qtyp_mut_ind
      (fun T => forall K (U : typ), size_typ U = 1 ->
         size_typ (open_tt_rec K U T) = size_typ T)
      (fun T => forall K (U : typ), size_typ U = 1 ->
         size_qtyp (open_tqt_rec K U T) = size_qtyp T)).
    + intros; reflexivity.
    + intros n K U HU. simpl. destruct (K == n); [ exact HU | reflexivity ].
    + intros; reflexivity.
    + intros q1 IH1 q2 IH2 K U HU. simpl.
      rewrite (IH1 K U HU), (IH2 (S K) U HU). reflexivity.
    + intros T1 IH1 q IH2 K U HU. simpl.
      rewrite (IH1 K U HU), (IH2 (S K) U HU). reflexivity.
    + intros Q q IH K U HU. simpl.
      rewrite (IH (S K) U HU). reflexivity.
    + intros q1 IH1 q2 IH2 K U HU. simpl.
      rewrite (IH1 K U HU), (IH2 K U HU). reflexivity.
    + intros q1 IH1 q2 IH2 K U HU. simpl.
      rewrite (IH1 K U HU), (IH2 K U HU). reflexivity.
    + intros q IH K U HU. simpl. rewrite (IH K U HU). reflexivity.
    + intros Q T IH K U HU. simpl. rewrite (IH K U HU). reflexivity.
Qed.

Lemma size_qtyp_open_tqt_one : forall (T : qtyp) (X : atom),
  size_qtyp (open_tqt T X) = size_qtyp T.
Proof.
  intros T X. apply (proj2 size_open_tt_one T 0 (typ_fvar X)). reflexivity.
Qed.

Lemma size_open_qt_one :
  (forall T, forall K (R : qua), size_qua R = 1 ->
     size_typ (open_qt_rec K R T) = size_typ T) /\
  (forall T : qtyp, forall K (R : qua), size_qua R = 1 ->
     size_qtyp (open_qqt_rec K R T) = size_qtyp T).
Proof.
  split.
  - apply (typ_mut_ind
      (fun T => forall K (R : qua), size_qua R = 1 ->
         size_typ (open_qt_rec K R T) = size_typ T)
      (fun T => forall K (R : qua), size_qua R = 1 ->
         size_qtyp (open_qqt_rec K R T) = size_qtyp T)).
    + intros; reflexivity.
    + intros; reflexivity.
    + intros; reflexivity.
    + intros q1 IH1 q2 IH2 K R HR. simpl.
      rewrite (IH1 K R HR), (IH2 (S K) R HR). reflexivity.
    + intros T1 IH1 q IH2 K R HR. simpl.
      rewrite (IH1 K R HR), (IH2 (S K) R HR). reflexivity.
    + intros Q q IH K R HR. simpl.
      rewrite (size_qua_open_qq_one Q K R HR), (IH (S K) R HR). reflexivity.
    + intros q1 IH1 q2 IH2 K R HR. simpl.
      rewrite (IH1 K R HR), (IH2 K R HR). reflexivity.
    + intros q1 IH1 q2 IH2 K R HR. simpl.
      rewrite (IH1 K R HR), (IH2 K R HR). reflexivity.
    + intros q IH K R HR. simpl. rewrite (IH K R HR). reflexivity.
    + intros Q T IH K R HR. simpl.
      rewrite (size_qua_open_qq_one Q K R HR), (IH K R HR). reflexivity.
  - apply (qtyp_mut_ind
      (fun T => forall K (R : qua), size_qua R = 1 ->
         size_typ (open_qt_rec K R T) = size_typ T)
      (fun T => forall K (R : qua), size_qua R = 1 ->
         size_qtyp (open_qqt_rec K R T) = size_qtyp T)).
    + intros; reflexivity.
    + intros; reflexivity.
    + intros; reflexivity.
    + intros q1 IH1 q2 IH2 K R HR. simpl.
      rewrite (IH1 K R HR), (IH2 (S K) R HR). reflexivity.
    + intros T1 IH1 q IH2 K R HR. simpl.
      rewrite (IH1 K R HR), (IH2 (S K) R HR). reflexivity.
    + intros Q q IH K R HR. simpl.
      rewrite (size_qua_open_qq_one Q K R HR), (IH (S K) R HR). reflexivity.
    + intros q1 IH1 q2 IH2 K R HR. simpl.
      rewrite (IH1 K R HR), (IH2 K R HR). reflexivity.
    + intros q1 IH1 q2 IH2 K R HR. simpl.
      rewrite (IH1 K R HR), (IH2 K R HR). reflexivity.
    + intros q IH K R HR. simpl. rewrite (IH K R HR). reflexivity.
    + intros Q T IH K R HR. simpl.
      rewrite (size_qua_open_qq_one Q K R HR), (IH K R HR). reflexivity.
Qed.

Lemma size_qtyp_open_qqt_one : forall (T : qtyp) (X : atom),
  size_qtyp (open_qqt T X) = size_qtyp T.
Proof.
  intros T X. apply (proj2 size_open_qt_one T 0 (qua_fvar X)). reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Exact bind_sub lookup is unchanged by a bind_qua replacement       *)
(* ------------------------------------------------------------------ *)

Lemma binds_change_qua_head : forall (ctx : env) X Q1 Q2 E Y U,
  binds Y (bind_sub U) (ctx ++ (X, bind_qua Q1) :: E) ->
  binds Y (bind_sub U) (ctx ++ (X, bind_qua Q2) :: E).
Proof.
  induction ctx as [| [y b] ctx IH]; intros X Q1 Q2 E Y U Hb; simpl in *.
  - apply binds_cons_iff in Hb. destruct Hb as [[HY HU]|Hb].
    + inversion HU.
    + apply binds_cons. exact Hb.
  - apply binds_cons_iff in Hb. destruct Hb as [[HY Hbnd]|Hb].
    + apply binds_cons_2; auto.
    + apply binds_cons. apply (IH X Q1 Q2 E Y U Hb).
Qed.

(* ------------------------------------------------------------------ *)
(* Narrowing a bind_qua binder                                       *)
(* ------------------------------------------------------------------ *)

Definition QNsub (E : env) (S T : typ) (D : sub E S T) : Prop :=
  forall ctx X Q1 Q2 E0,
    E = ctx ++ (X, bind_qua Q1) :: E0 ->
    subqual E0 Q2 Q1 ->
    wf_env E ->
    sub (ctx ++ (X, bind_qua Q2) :: E0) S T.

Definition QNqt (E : env) (S T : qtyp) (D : subqtype E S T) : Prop :=
  forall ctx X Q1 Q2 E0,
    E = ctx ++ (X, bind_qua Q1) :: E0 ->
    subqual E0 Q2 Q1 ->
    wf_env E ->
    subqtype (ctx ++ (X, bind_qua Q2) :: E0) S T.

Lemma QNsub_proof : forall E S T (D : sub E S T), QNsub E S T D.
Proof.
  apply (sub_mut_ind QNsub QNqt).
  - (* top *) intros E S HwfE HwS. unfold QNsub.
    intros ctx X Q1 Q2 E0 HE Hs HwfOld. subst E.
    apply sub_top.
    + apply (wf_env_narrow _ _ HwfOld (env_narrow_ctx_qua ctx X Q1 Q2 E0 Hs)).
    + apply (wf_typ_narrow _ _ S (env_narrow_ctx_qua ctx X Q1 Q2 E0 Hs) HwS).
  - (* refl *) intros E X HwfE HwX. unfold QNsub.
    intros ctx X0 Q1 Q2 E0 HE Hs HwfOld. subst E.
    apply sub_refl_tvar.
    + apply (wf_env_narrow _ _ HwfOld (env_narrow_ctx_qua ctx X0 Q1 Q2 E0 Hs)).
    + apply (wf_typ_narrow _ _ (typ_fvar X) (env_narrow_ctx_qua ctx X0 Q1 Q2 E0 Hs) HwX).
  - (* trans_tvar *) intros U E T Xb b s IH. unfold QNsub.
    intros ctx X0 Q1 Q2 E0 HE Hs HwfOld. subst E.
    apply sub_trans_tvar with (U := U).
    + apply (binds_change_qua_head ctx X0 Q1 Q2 E0 Xb U b).
    + apply (IH ctx X0 Q1 Q2 E0 eq_refl Hs HwfOld).
  - (* arrow *) intros E S1 S2 T1 T2 s1 IH1 s2 IH2. unfold QNsub.
    intros ctx X0 Q1 Q2 E0 HE Hs HwfOld. subst E.
    apply sub_arrow.
    + apply (IH1 ctx X0 Q1 Q2 E0 eq_refl Hs HwfOld).
    + apply (IH2 ctx X0 Q1 Q2 E0 eq_refl Hs HwfOld).
  - (* all *) intros L E S1 S2 T1 T2 s1 IH1 s2 IH2. unfold QNsub.
    intros ctx X0 Q1 Q2 E0 HE Hs HwfOld. subst E.
    apply (sub_all (union L (add X0 (dom ctx)))).
    + apply (IH1 ctx X0 Q1 Q2 E0 eq_refl Hs HwfOld).
    + intros Y HY.
      assert (HYL : Y `notin` L) by (simpl in HY; fsetdec).
      apply (IH2 Y HYL ((Y, bind_sub T1) :: ctx) X0 Q1 Q2 E0 eq_refl Hs).
      apply (subqtype_wf_env _ _ _ (s2 Y HYL)).
  - (* qall *) intros L E S1 S2 T1 T2 sq s2 IH2. unfold QNsub.
    intros ctx X0 Q1 Q2 E0 HE Hs HwfOld. subst E.
    apply (sub_qall (union L (add X0 (dom ctx)))).
    + eapply subqual_narrow.
      * apply (subqual_wf_env _ _ _ sq).
      * exact sq.
      * apply (env_narrow_ctx_qua ctx X0 Q1 Q2 E0 Hs).
    + intros Y HY.
      assert (HYL : Y `notin` L) by (simpl in HY; fsetdec).
      apply (IH2 Y HYL ((Y, bind_qua T1) :: ctx) X0 Q1 Q2 E0 eq_refl Hs).
      apply (subqtype_wf_env _ _ _ (s2 Y HYL)).
  - (* sum *) intros E S1 S2 T1 T2 s1 IH1 s2 IH2. unfold QNsub.
    intros ctx X0 Q1 Q2 E0 HE Hs HwfOld. subst E.
    apply sub_sum.
    + apply (IH1 ctx X0 Q1 Q2 E0 eq_refl Hs HwfOld).
    + apply (IH2 ctx X0 Q1 Q2 E0 eq_refl Hs HwfOld).
  - (* pair *) intros E S1 S2 T1 T2 s1 IH1 s2 IH2. unfold QNsub.
    intros ctx X0 Q1 Q2 E0 HE Hs HwfOld. subst E.
    apply sub_pair.
    + apply (IH1 ctx X0 Q1 Q2 E0 eq_refl Hs HwfOld).
    + apply (IH2 ctx X0 Q1 Q2 E0 eq_refl Hs HwfOld).
  - (* qtyp *) intros E Q1 T1 Q2 T2 sq s IH. unfold QNqt.
    intros ctx X0 Q1' Q2' E0 HE Hs HwfOld. subst E.
    apply sub_qtyp_qtyp.
    + eapply subqual_narrow.
      * apply (subqual_wf_env _ _ _ sq).
      * exact sq.
      * apply (env_narrow_ctx_qua ctx X0 Q1' Q2' E0 Hs).
    + apply (IH ctx X0 Q1' Q2' E0 eq_refl Hs HwfOld).
Qed.

Lemma QNqt_proof : forall E S T (D : subqtype E S T), QNqt E S T D.
Proof.
  intros E S T D. destruct D as [E0 Qa Ta Qb Tb sq s]. simpl in *.
  unfold QNqt. intros ctx X Q1 Q2 Ebase HE Hs HwfOld. subst E0.
  apply sub_qtyp_qtyp.
  - eapply subqual_narrow.
    + apply (subqual_wf_env _ _ _ sq).
    + exact sq.
    + apply (env_narrow_ctx_qua ctx X Q1 Q2 Ebase Hs).
  - apply (QNsub_proof (ctx ++ (X, bind_qua Q1) :: Ebase) Ta Tb s
                        ctx X Q1 Q2 Ebase eq_refl Hs HwfOld).
Qed.

Lemma sub_qua_narrow : forall ctx X Q1 Q2 E S T,
  subqual E Q2 Q1 ->
  wf_env (ctx ++ (X, bind_qua Q1) :: E) ->
  sub (ctx ++ (X, bind_qua Q1) :: E) S T ->
  sub (ctx ++ (X, bind_qua Q2) :: E) S T.
Proof.
  intros ctx X Q1 Q2 E S T Hs Hwf H.
  exact (QNsub_proof (ctx ++ (X, bind_qua Q1) :: E) S T H
                     ctx X Q1 Q2 E eq_refl Hs Hwf).
Qed.

Lemma subqtype_qua_narrow : forall ctx X Q1 Q2 E S T,
  subqual E Q2 Q1 ->
  wf_env (ctx ++ (X, bind_qua Q1) :: E) ->
  subqtype (ctx ++ (X, bind_qua Q1) :: E) S T ->
  subqtype (ctx ++ (X, bind_qua Q2) :: E) S T.
Proof.
  intros ctx X Q1 Q2 E S T Hs Hwf H.
  exact (QNqt_proof (ctx ++ (X, bind_qua Q1) :: E) S T H
                    ctx X Q1 Q2 E eq_refl Hs Hwf).
Qed.

(* ------------------------------------------------------------------ *)
(* Transitivity by induction on the size of the middle type           *)
(* ------------------------------------------------------------------ *)

Definition TransN (n : nat) : Prop :=
  (forall (E : env) (S T : typ) (Dl : sub E S T),
      size_typ T <= n -> forall U, sub E T U -> sub E S U) /\
  (forall (E : env) (S T : qtyp) (Dl : subqtype E S T),
      size_qtyp T <= n -> forall U, subqtype E T U -> subqtype E S U).

Lemma transN : forall n, TransN n.
Proof.
  apply (well_founded_ind lt_wf (fun n => TransN n)).
  intros n IHn. unfold TransN.
  assert (Hsub : forall (E : env) (S T : typ) (Dl : sub E S T),
      size_typ T <= n -> forall U, sub E T U -> sub E S U).
  { apply (sub_mut_ind
      (fun E S T Dl => size_typ T <= n -> forall U, sub E T U -> sub E S U)
      (fun E S T Dl => size_qtyp T <= n -> forall U, subqtype E T U -> subqtype E S U)).
    - (* top *) intros E S HwfE HwS Hsize U Dr.
      apply sub_source_top_inv in Dr. subst U.
      apply sub_top; assumption.
    - (* refl *) intros E X HwfE HwX Hsize U Dr. exact Dr.
    - (* trans_tvar *) intros U0 E T X b s IH Hsize U Dr.
      apply (sub_trans_tvar U0 E U X b).
      apply (IH Hsize U Dr).
    - (* arrow *) intros E S1 S2 T1 T2 s1 IH1 s2 IH2 Hsize U Dr.
      simpl in Hsize.
      dependent destruction Dr.
      + apply sub_top.
        * exact H.
        * apply wf_typ_arrow.
          -- destruct (subqtype_wf E T1 S1 s1) as [_ [_ HS1]]. exact HS1.
          -- destruct (subqtype_wf E S2 T2 s2) as [_ [HS2 _]]. exact HS2.
      + apply sub_arrow.
        * assert (Hlt : size_qtyp T1 < n) by lia.
          destruct (IHn (size_qtyp T1) Hlt) as [IHs IHq].
          exact (IHq E T0 T1 H (Nat.le_refl _) S1 s1).
        * assert (Hlt : size_qtyp T2 < n) by lia.
          destruct (IHn (size_qtyp T2) Hlt) as [IHs IHq].
          exact (IHq E S2 T2 s2 (Nat.le_refl _) T3 H0).
    - (* all *) intros L E S1 S2 T1 T2 s1 IH1 s2 IH2 Hsize U Dr.
      simpl in Hsize.
      dependent destruction Dr.
      + apply sub_top.
        * exact H.
        * destruct (sub_wf E (typ_all S1 S2) (typ_all T1 T2)
                     (sub_all L E S1 S2 T1 T2 s1 s2)) as [_ [HwS _]].
          exact HwS.
      + apply (sub_all (union L (union L0 (dom E)))).
        * assert (HltT1 : size_typ T1 < n) by lia.
          destruct (IHn (size_typ T1) HltT1) as [IHs IHq].
          exact (IHs E T0 T1 Dr (Nat.le_refl _) S1 s1).
        * intros X HX.
          assert (HXL : X `notin` L) by (simpl in HX; fsetdec).
          assert (HXL0 : X `notin` L0) by (simpl in HX; fsetdec).
          pose proof (s2 X HXL) as HL.
          pose proof (H X HXL0) as HR.
          assert (HltT1 : size_typ T1 < n) by lia.
          assert (Hrel : sub E T0 T1) by exact Dr.
          assert (Grel : forall ctx' U',
              sub (ctx' ++ (X, bind_sub T0) :: E) T1 U' ->
              sub (ctx' ++ (X, bind_sub T0) :: E) T0 U').
          { intros ctx' U' Hsub.
            destruct (IHn (size_typ T1) HltT1) as [IHs IHq].
            apply (IHs (ctx' ++ (X, bind_sub T0) :: E) T0 T1
                      (sub_weaken E T0 T1 Dr (ctx' ++ (X, bind_sub T0) :: E)
                                  (env_incl_ctx_mid E ctx' X (bind_sub T0))
                                  (sub_wf_env _ _ _ Hsub))
                      (Nat.le_refl _) U' Hsub). }
          assert (Hn : subqtype (X ~ bind_sub T0 ++ E)
                                (open_tqt S2 X) (open_tqt T2 X)).
          { exact (Nqt_proof (X ~ bind_sub T1 ++ E) (open_tqt S2 X) (open_tqt T2 X) HL
                              (@nil (atom * binding)) X T1 T0 E Dr Grel eq_refl). }
          assert (HltB : size_qtyp (open_tqt T2 X) < n).
          { rewrite size_qtyp_open_tqt_one. lia. }
          destruct (IHn (size_qtyp (open_tqt T2 X)) HltB) as [IHs IHq].
          exact (IHq (X ~ bind_sub T0 ++ E) (open_tqt S2 X) (open_tqt T2 X) Hn
                     (Nat.le_refl _) (open_tqt T3 X) HR).
    - (* qall *) intros L E S1 S2 T1 T2 sq s2 IH2 Hsize U Dr.
      simpl in Hsize.
      dependent destruction Dr.
      + apply sub_top.
        * exact H.
        * destruct (sub_wf E (typ_qall S1 S2) (typ_qall T1 T2)
                     (sub_qall L E S1 S2 T1 T2 sq s2)) as [_ [HwS _]].
          exact HwS.
      + apply (sub_qall (union L (union L0 (dom E)))).
        * eapply subqual_trans; [ exact H | exact sq ].
        * intros X HX.
          assert (HXL : X `notin` L) by (simpl in HX; fsetdec).
          assert (HXL0 : X `notin` L0) by (simpl in HX; fsetdec).
          pose proof (s2 X HXL) as HL.
          pose proof (H0 X HXL0) as HR.
          assert (Hn : subqtype (X ~ bind_qua T0 ++ E)
                                (open_qqt S2 X) (open_qqt T2 X)).
          { exact (subqtype_qua_narrow (@nil (atom * binding)) X T1 T0 E
                     (open_qqt S2 X) (open_qqt T2 X) H
                     (subqtype_wf_env _ _ _ HL) HL). }
          assert (HltB : size_qtyp (open_qqt T2 X) < n).
          { rewrite size_qtyp_open_qqt_one. lia. }
          destruct (IHn (size_qtyp (open_qqt T2 X)) HltB) as [IHs IHq].
          exact (IHq (X ~ bind_qua T0 ++ E) (open_qqt S2 X) (open_qqt T2 X) Hn
                     (Nat.le_refl _) (open_qqt T3 X) HR).
    - (* sum *) intros E S1 S2 T1 T2 s1 IH1 s2 IH2 Hsize U Dr.
      simpl in Hsize.
      dependent destruction Dr.
      + apply sub_top.
        * exact H.
        * apply wf_typ_sum.
          -- destruct (subqtype_wf E S1 T1 s1) as [_ [HS1 _]]. exact HS1.
          -- destruct (subqtype_wf E S2 T2 s2) as [_ [HS2 _]]. exact HS2.
      + apply sub_sum.
        * assert (Hlt : size_qtyp T1 < n) by lia.
          destruct (IHn (size_qtyp T1) Hlt) as [IHs IHq].
          exact (IHq E S1 T1 s1 (Nat.le_refl _) T0 H).
        * assert (Hlt : size_qtyp T2 < n) by lia.
          destruct (IHn (size_qtyp T2) Hlt) as [IHs IHq].
          exact (IHq E S2 T2 s2 (Nat.le_refl _) T3 H0).
    - (* pair *) intros E S1 S2 T1 T2 s1 IH1 s2 IH2 Hsize U Dr.
      simpl in Hsize.
      dependent destruction Dr.
      + apply sub_top.
        * exact H.
        * apply wf_typ_pair.
          -- destruct (subqtype_wf E S1 T1 s1) as [_ [HS1 _]]. exact HS1.
          -- destruct (subqtype_wf E S2 T2 s2) as [_ [HS2 _]]. exact HS2.
      + apply sub_pair.
        * assert (Hlt : size_qtyp T1 < n) by lia.
          destruct (IHn (size_qtyp T1) Hlt) as [IHs IHq].
          exact (IHq E S1 T1 s1 (Nat.le_refl _) T0 H).
        * assert (Hlt : size_qtyp T2 < n) by lia.
          destruct (IHn (size_qtyp T2) Hlt) as [IHs IHq].
          exact (IHq E S2 T2 s2 (Nat.le_refl _) T3 H0).
    - (* qtyp *) intros E Q1 T1 Q2 T2 sq s IH Hsize U Dr.
      dependent destruction Dr.
      apply sub_qtyp_qtyp.
      + eapply subqual_trans; [ exact sq | exact H ].
      + simpl in Hsize.
        assert (Hle : size_typ T2 <= n) by lia.
        exact (IH Hle T3 H0).
  }
  assert (Hqt : forall (E : env) (S T : qtyp) (Dl : subqtype E S T),
      size_qtyp T <= n -> forall U, subqtype E T U -> subqtype E S U).
  { intros E S T Dl Hsize U Dr.
    destruct Dl as [E0 Q1 T1 Q2 T2 sq s]. simpl in *.
    dependent destruction Dr.
    apply sub_qtyp_qtyp.
    - eapply subqual_trans; [ exact sq | exact H ].
    - assert (Hle : size_typ T2 <= n) by lia.
      exact (Hsub E T1 T2 s Hle T3 H0).
  }
  split; [exact Hsub | exact Hqt].
Qed.

Lemma sub_trans : forall E S T U,
  sub E S T -> sub E T U -> sub E S U.
Proof.
  intros E S T U H1 H2.
  exact (proj1 (transN (size_typ T)) E S T H1 (Nat.le_refl _) U H2).
Qed.

Lemma subqtype_trans : forall E S T U,
  subqtype E S T -> subqtype E T U -> subqtype E S U.
Proof.
  intros E S T U H1 H2.
  exact (proj2 (transN (size_qtyp T)) E S T H1 (Nat.le_refl _) U H2).
Qed.

(* Compatibility with the Fwi/Gwi scaffolds already present in Task.v. *)
Lemma FGi : forall E S T (D : sub E S T), Fwi E S T D /\ Gwi E S T D.
Proof.
  intros E S T D. split.
  - unfold Fwi. intros E' Hincl Hwf W HW.
    apply (sub_trans E' W S T HW).
    apply (sub_weaken E S T D E' Hincl Hwf).
  - unfold Gwi. intros E' Hincl Hwf U HU.
    apply (sub_trans E' S T U).
    + apply (sub_weaken E S T D E' Hincl Hwf).
    + exact HU.
Qed.

Lemma FGiq : forall E S T (D : subqtype E S T), Fwiq E S T D /\ Gwiq E S T D.
Proof.
  intros E S T D. split.
  - unfold Fwiq. intros E' Hincl Hwf W HW.
    apply (subqtype_trans E' W S T HW).
    apply (subqtype_weaken E S T D E' Hincl Hwf).
  - unfold Gwiq. intros E' Hincl Hwf U HU.
    apply (subqtype_trans E' S T U).
    + apply (subqtype_weaken E S T D E' Hincl Hwf).
    + exact HU.
Qed.

Lemma subqual_remove_typ : forall E1 E2 x U Q R,
  subqual (E1 ++ (x, bind_typ U) :: E2) Q R -> subqual (E1 ++ E2) Q R.
Proof.
  intros E1 E2 x U Q R H.
  dependent induction H.
  - (* top *) apply subqual_top.
    + apply (wf_env_remove_typ E1 E2 x U H).
    + apply (wf_qua_remove_typ E1 E2 x U Q H0).
  - (* bot *) apply subqual_bot.
    + apply (wf_env_remove_typ E1 E2 x U H).
    + apply (wf_qua_remove_typ E1 E2 x U Q H0).
  - (* eval_elim *) eapply subqual_eval_elim.
    + apply (IHsubqual1 E1 E2 x U eq_refl).
    + exact H0.
    + apply (IHsubqual2 E1 E2 x U eq_refl).
  - (* eval_intro *) eapply subqual_eval_intro.
    + apply (IHsubqual1 E1 E2 x U eq_refl).
    + exact H0.
    + apply (IHsubqual2 E1 E2 x U eq_refl).
  - (* lift *) apply subqual_lift_elem.
    + apply (wf_env_remove_typ E1 E2 x U H).
    + exact H0.
  - (* refl_qvar *) apply subqual_refl_qvar.
    + apply (wf_env_remove_typ E1 E2 x U H).
    + apply (wf_qua_remove_typ E1 E2 x U (qua_fvar X) H0).
  - (* trans_qvar *) eapply subqual_trans_qvar.
    + apply (binds_not_middle binding X (bind_qua R) x (bind_typ U) (bind_typ U) E1 E2 H).
      discriminate.
    + apply (IHsubqual E1 E2 x U eq_refl).
  - (* join_inl *) apply subqual_join_inl.
    + apply (IHsubqual E1 E2 x U eq_refl).
    + apply (wf_qua_remove_typ E1 E2 x U R2 H0).
  - (* join_inr *) apply subqual_join_inr.
    + apply (wf_qua_remove_typ E1 E2 x U R1 H).
    + apply (IHsubqual E1 E2 x U eq_refl).
  - (* join_elim *) apply subqual_join_elim.
    + apply (IHsubqual1 E1 E2 x U eq_refl).
    + apply (IHsubqual2 E1 E2 x U eq_refl).
  - (* meet_eliml *) apply subqual_meet_eliml.
    + apply (IHsubqual E1 E2 x U eq_refl).
    + apply (wf_qua_remove_typ E1 E2 x U R2 H0).
  - (* meet_elimr *) apply subqual_meet_elimr.
    + apply (wf_qua_remove_typ E1 E2 x U R1 H).
    + apply (IHsubqual E1 E2 x U eq_refl).
  - (* meet_intro *) apply subqual_meet_intro.
    + apply (IHsubqual1 E1 E2 x U eq_refl).
    + apply (IHsubqual2 E1 E2 x U eq_refl).
Qed.

Definition Rsub (E : env) (S T : typ) (D : sub E S T) : Prop :=
  forall E1 E2 x U,
    E = E1 ++ (x, bind_typ U) :: E2 -> sub (E1 ++ E2) S T.
Definition Rqt (E : env) (S T : qtyp) (D : subqtype E S T) : Prop :=
  forall E1 E2 x U,
    E = E1 ++ (x, bind_typ U) :: E2 -> subqtype (E1 ++ E2) S T.

Lemma Rsub_proof : forall E S T (D : sub E S T), Rsub E S T D.
Proof.
  apply (sub_mut_ind Rsub Rqt).
  - (* top *) intros E S Hwf HwS E1 E2 x U HE. subst E.
    apply sub_top.
    + apply (wf_env_remove_typ E1 E2 x U Hwf).
    + apply (wf_typ_remove_typ E1 E2 x U S HwS).
  - (* refl *) intros E X Hwf HwX E1 E2 x U HE. subst E.
    apply sub_refl_tvar.
    + apply (wf_env_remove_typ E1 E2 x U Hwf).
    + apply (wf_typ_remove_typ E1 E2 x U (typ_fvar X) HwX).
  - (* trans_tvar *) intros U0 E T X b s IH E1 E2 x U HE. subst E.
    apply sub_trans_tvar with (U := U0).
    + apply (binds_not_middle binding X (bind_sub U0) x (bind_typ U) (bind_typ U) E1 E2 b).
      discriminate.
    + apply (IH E1 E2 x U eq_refl).
  - (* arrow *) intros E S1 S2 T1 T2 s1 IH1 s2 IH2 E1 E2 x U HE. subst E.
    apply sub_arrow.
    + apply (IH1 E1 E2 x U eq_refl).
    + apply (IH2 E1 E2 x U eq_refl).
  - (* all *) intros L E S1 S2 T1 T2 s1 IH1 s2 IH2 E1 E2 x U HE. subst E.
    apply (sub_all (union L (add x (dom E1)))).
    + apply (IH1 E1 E2 x U eq_refl).
    + intros Y HY.
      assert (HYL : Y `notin` L) by (simpl in HY; fsetdec).
      apply (IH2 Y HYL ((Y, bind_sub T1) :: E1) E2 x U eq_refl).
  - (* qall *) intros L E S1 S2 T1 T2 sq s2 IH2 E1 E2 x U HE. subst E.
    apply (sub_qall (union L (add x (dom E1)))).
    + apply (subqual_remove_typ E1 E2 x U T1 S1 sq).
    + intros Y HY.
      assert (HYL : Y `notin` L) by (simpl in HY; fsetdec).
      apply (IH2 Y HYL ((Y, bind_qua T1) :: E1) E2 x U eq_refl).
  - (* sum *) intros E S1 S2 T1 T2 s1 IH1 s2 IH2 E1 E2 x U HE. subst E.
    apply sub_sum.
    + apply (IH1 E1 E2 x U eq_refl).
    + apply (IH2 E1 E2 x U eq_refl).
  - (* pair *) intros E S1 S2 T1 T2 s1 IH1 s2 IH2 E1 E2 x U HE. subst E.
    apply sub_pair.
    + apply (IH1 E1 E2 x U eq_refl).
    + apply (IH2 E1 E2 x U eq_refl).
  - (* qtyp *) intros E Q1 T1 Q2 T2 sq s IH E1 E2 x U HE. subst E.
    apply sub_qtyp_qtyp.
    + apply (subqual_remove_typ E1 E2 x U Q1 Q2 sq).
    + apply (IH E1 E2 x U eq_refl).
Qed.

Lemma Rqt_proof : forall E S T (D : subqtype E S T), Rqt E S T D.
Proof.
  intros E S T D. destruct D as [E0 Q1 T1 Q2 T2 sq s]. simpl in *.
  intros E1 E2 x U HE. subst E0.
  apply sub_qtyp_qtyp.
  - apply (subqual_remove_typ E1 E2 x U Q1 Q2 sq).
  - apply (Rsub_proof (E1 ++ (x, bind_typ U) :: E2) T1 T2 s E1 E2 x U eq_refl).
Qed.

Lemma sub_remove_typ : forall E1 E2 x U S T,
  sub (E1 ++ (x, bind_typ U) :: E2) S T -> sub (E1 ++ E2) S T.
Proof.
  intros. exact (Rsub_proof _ _ _ H E1 E2 x U eq_refl).
Qed.

Lemma subqtype_remove_typ : forall E1 E2 x U S T,
  subqtype (E1 ++ (x, bind_typ U) :: E2) S T -> subqtype (E1 ++ E2) S T.
Proof.
  intros. exact (Rqt_proof _ _ _ H E1 E2 x U eq_refl).
Qed.

Lemma typing_subst_ee_gen : forall E1 E2 x v T1 e T,
  typing E2 v T1 ->
  typing (E1 ++ (x, bind_typ T1) :: E2) e T ->
  typing (E1 ++ E2) (subst_ee x v e) T.
Proof.
  intros E1 E2 x v T1 e T Hv H.
  dependent induction H.
  - (* var *)
    pose proof (wf_env_uniq _ H) as Hu.
    pose proof (uniq_app_2 binding E1 ((x, bind_typ T1) :: E2) Hu) as HuF.
    rewrite (binds_app_uniq_iff binding x0 (bind_typ T) E1 ((x, bind_typ T1) :: E2) Hu) in H0.
    destruct H0 as [[HbE1 Hnotin] | [HbMid HnotinE1]].
    + assert (Hxneq : x0 <> x).
      { intro Heq. subst x0. apply Hnotin. simpl. fsetdec. }
      rewrite subst_ee_fvar_neq; auto.
      apply typing_var.
      * apply (wf_env_remove_typ E1 E2 x T1 H).
      * apply binds_app_l. exact HbE1.
    + rewrite (binds_cons_uniq_iff binding x0 x (bind_typ T) (bind_typ T1) E2 HuF) in HbMid.
      destruct HbMid as [[Heq [HT HnotinE2]] | [HbE2 Hxneq]].
      * subst x0. inversion HT. subst T.
        rewrite subst_ee_fvar_eq.
        apply (typing_weaken E2 v T1 Hv (E1 ++ E2)).
        -- apply env_incl_ctx_r.
        -- apply (wf_env_remove_typ E1 E2 x T1 H).
      * rewrite subst_ee_fvar_neq; auto.
        apply typing_var.
        -- apply (wf_env_remove_typ E1 E2 x T1 H).
        -- apply binds_app_r. exact HbE2.
  - (* abs *)
    apply (typing_abs (union L (add x (dom (E1 ++ E2)))) (E1 ++ E2) P V (subst_ee x v e1) T0).
    + apply (wf_qua_remove_typ E1 E2 x T1 P H).
    + intros x0 Hx.
      assert (HxL : x0 `notin` L) by (simpl in Hx; fsetdec).
      assert (Hxx : x0 <> x) by (intro Heq; subst x0; simpl in Hx; fsetdec).
      assert (Hxf : x `notin` fv_exp (exp_fvar x0)).
      { intro Hc. simpl in Hc. apply Hxx. fsetdec. }
      replace (open_ee (subst_ee x v e1) x0)
        with (subst_ee x v (open_ee e1 x0))
        by (exact (subst_ee_open_ee_rec e1 0 x v (exp_fvar x0) (typing_expr _ _ _ Hv) Hxf)).
      apply (H1 x0 HxL ((x0, bind_typ V) :: E1) E2 x T1 Hv eq_refl).
  - (* app *)
    eapply typing_app.
    + apply (IHtyping1 E1 E2 x T1 Hv eq_refl).
    + apply (IHtyping2 E1 E2 x T1 Hv eq_refl).
  - (* tabs *)
    apply (typing_tabs (union L (add x (dom (E1 ++ E2)))) P (E1 ++ E2) V (subst_ee x v e1) T0).
    + apply (wf_qua_remove_typ E1 E2 x T1 P H).
    + intros x0 Hx.
      assert (HxL : x0 `notin` L) by (simpl in Hx; fsetdec).
      assert (Hxx : x0 <> x) by (intro Heq; subst x0; simpl in Hx; fsetdec).
      assert (Hxf : x `notin` fv_exp (exp_fvar x0)).
      { intro Hc. simpl in Hc. apply Hxx. fsetdec. }
      replace (open_te (subst_ee x v e1) x0)
        with (subst_ee x v (open_te e1 x0))
        by (exact (subst_ee_open_te_rec e1 0 x v (typ_fvar x0) (typing_expr _ _ _ Hv))).
      apply (H1 x0 HxL ((x0, bind_sub V) :: E1) E2 x T1 Hv eq_refl).
  - (* tapp *)
    eapply typing_tapp.
    + apply (IHtyping E1 E2 x T1 Hv eq_refl).
    + apply (sub_remove_typ E1 E2 x T1 T T0 H0).
  - (* qabs *)
    apply (typing_qabs (union L (add x (dom (E1 ++ E2)))) (E1 ++ E2) P Q (subst_ee x v e1) T0).
    + apply (wf_qua_remove_typ E1 E2 x T1 P H).
    + intros x0 Hx.
      assert (HxL : x0 `notin` L) by (simpl in Hx; fsetdec).
      assert (Hxx : x0 <> x) by (intro Heq; subst x0; simpl in Hx; fsetdec).
      assert (Hxf : x `notin` fv_exp (exp_fvar x0)).
      { intro Hc. simpl in Hc. apply Hxx. fsetdec. }
      replace (open_qe (subst_ee x v e1) x0)
        with (subst_ee x v (open_qe e1 x0))
        by (exact (subst_ee_open_qe_rec e1 0 x v (qua_fvar x0) (typing_expr _ _ _ Hv))).
      apply (H1 x0 HxL ((x0, bind_qua Q) :: E1) E2 x T1 Hv eq_refl).
  - (* qapp *)
    eapply typing_qapp.
    + apply (IHtyping E1 E2 x T1 Hv eq_refl).
    + apply (subqual_remove_typ E1 E2 x T1 Q Q1 H0).
  - (* sub *)
    eapply typing_sub.
    + apply (IHtyping E1 E2 x T1 Hv eq_refl).
    + apply (subqtype_remove_typ E1 E2 x T1 S T H0).
  - (* let *)
    apply (typing_let (union L (add x (dom (E1 ++ E2)))) T0 T2
                      (subst_ee x v e1) (subst_ee x v e2) (E1 ++ E2)).
    + apply (IHtyping E1 E2 x T1 Hv eq_refl).
    + intros x0 Hx.
      assert (HxL : x0 `notin` L) by (simpl in Hx; fsetdec).
      assert (Hxx : x0 <> x) by (intro Heq; subst x0; simpl in Hx; fsetdec).
      assert (Hxf : x `notin` fv_exp (exp_fvar x0)).
      { intro Hc. simpl in Hc. apply Hxx. fsetdec. }
      replace (open_ee (subst_ee x v e2) x0)
        with (subst_ee x v (open_ee e2 x0))
        by (exact (subst_ee_open_ee_rec e2 0 x v (exp_fvar x0) (typing_expr _ _ _ Hv) Hxf)).
      apply (H1 x0 HxL ((x0, bind_typ T0) :: E1) E2 x T1 Hv eq_refl).
  - (* inl *)
    eapply typing_inl.
    + apply (wf_qua_remove_typ E1 E2 x T1 P H).
    + apply (IHtyping E1 E2 x T1 Hv eq_refl).
    + apply (wf_qtyp_remove_typ E1 E2 x T1 T2 H1).
  - (* inr *)
    eapply typing_inr.
    + apply (wf_qua_remove_typ E1 E2 x T1 P H).
    + apply (IHtyping E1 E2 x T1 Hv eq_refl).
    + apply (wf_qtyp_remove_typ E1 E2 x T1 T0 H1).
  - (* case *)
    apply (typing_case (union L (add x (dom (E1 ++ E2)))) Q T0 T2 T
                       (subst_ee x v e1) (subst_ee x v e2) (subst_ee x v e3) (E1 ++ E2)).
    + apply (IHtyping E1 E2 x T1 Hv eq_refl).
    + intros x0 Hx.
      assert (HxL : x0 `notin` L) by (simpl in Hx; fsetdec).
      assert (Hxx : x0 <> x) by (intro Heq; subst x0; simpl in Hx; fsetdec).
      assert (Hxf : x `notin` fv_exp (exp_fvar x0)).
      { intro Hc. simpl in Hc. apply Hxx. fsetdec. }
      replace (open_ee (subst_ee x v e2) x0)
        with (subst_ee x v (open_ee e2 x0))
        by (exact (subst_ee_open_ee_rec e2 0 x v (exp_fvar x0) (typing_expr _ _ _ Hv) Hxf)).
      apply (H1 x0 HxL ((x0, bind_typ T0) :: E1) E2 x T1 Hv eq_refl).
    + intros x0 Hx.
      assert (HxL : x0 `notin` L) by (simpl in Hx; fsetdec).
      assert (Hxx : x0 <> x) by (intro Heq; subst x0; simpl in Hx; fsetdec).
      assert (Hxf : x `notin` fv_exp (exp_fvar x0)).
      { intro Hc. simpl in Hc. apply Hxx. fsetdec. }
      replace (open_ee (subst_ee x v e3) x0)
        with (subst_ee x v (open_ee e3 x0))
        by (exact (subst_ee_open_ee_rec e3 0 x v (exp_fvar x0) (typing_expr _ _ _ Hv) Hxf)).
      apply (H3 x0 HxL ((x0, bind_typ T2) :: E1) E2 x T1 Hv eq_refl).
  - (* pair *)
    eapply typing_pair.
    + apply (wf_qua_remove_typ E1 E2 x T1 P H).
    + apply (IHtyping1 E1 E2 x T1 Hv eq_refl).
    + apply (IHtyping2 E1 E2 x T1 Hv eq_refl).
  - (* first *)
    eapply typing_first.
    apply (IHtyping E1 E2 x T1 Hv eq_refl).
  - (* second *)
    eapply typing_second.
    apply (IHtyping E1 E2 x T1 Hv eq_refl).
  - (* upqual *)
    eapply typing_upqual.
    + apply (IHtyping E1 E2 x T1 Hv eq_refl).
    + apply (subqual_remove_typ E1 E2 x T1 Q P H0).
  - (* check *)
    eapply typing_check.
    + apply (IHtyping E1 E2 x T1 Hv eq_refl).
    + apply (subqual_remove_typ E1 E2 x T1 Q P H0).
Qed.


(* ================================================================== *)
(* Type-variable substitution for environments and wf judgments    *)
(* ================================================================== *)
Definition subst_binding_te (X : atom) (U : typ) (b : binding) : binding :=
  match b with
  | bind_sub V => bind_sub (subst_tt X U V)
  | bind_typ T => bind_typ (subst_tqt X U T)
  | bind_qua Q => bind_qua Q
  end.

Fixpoint subst_env_te (X : atom) (U : typ) (E : env) {struct E} : env :=
  match E with
  | nil => nil
  | cons (y, b) E' => cons (y, subst_binding_te X U b) (subst_env_te X U E')
  end.

Lemma subst_env_te_app : forall X U E1 E2,
  subst_env_te X U (E1 ++ E2) = subst_env_te X U E1 ++ subst_env_te X U E2.
Proof.
  intros X U E1. induction E1 as [|[y b] E1 IH]; intros E2; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma dom_subst_env_te : forall X U E,
  dom (subst_env_te X U E) = dom E.
Proof.
  intros X U E. induction E as [|[y b] E IH]; simpl.
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma binds_subst_env_te_sub : forall E1 E2 X U V Y W,
  binds Y (bind_sub W) (E1 ++ (X, bind_sub V) :: E2) ->
  Y = X \/ exists W', binds Y (bind_sub W') (subst_env_te X U E1 ++ E2).
Proof.
  induction E1 as [|[y b] E1 IH]; intros E2 X U V Y W Hb; simpl in *.
  - apply binds_cons_iff in Hb. destruct Hb as [[HY Hb]|Hb].
    + left. exact HY.
    + right. exists W. simpl. exact Hb.
  - apply binds_cons_iff in Hb. destruct Hb as [[HY Hb]|Hb].
    + right. subst y.
      destruct b as [Vb|Tb|Qb].
      * inversion Hb. subst Vb. exists (subst_tt X U W). simpl. apply binds_cons_2; auto.
      * inversion Hb.
      * inversion Hb.
    + destruct (IH E2 X U V Y W Hb) as [HY|HW'].
      * left. exact HY.
      * right. destruct HW' as [W' HW']. exists W'. apply binds_cons. exact HW'.
Qed.

Lemma binds_subst_env_te_qua : forall E1 E2 X U V Y Q,
  binds Y (bind_qua Q) (E1 ++ (X, bind_sub V) :: E2) ->
  exists Q', binds Y (bind_qua Q') (subst_env_te X U E1 ++ E2).
Proof.
  induction E1 as [|[y b] E1 IH]; intros E2 X U V Y Q Hb; simpl in *.
  - apply binds_cons_iff in Hb. destruct Hb as [[HY Hb]|Hb].
    + inversion Hb.
    + exists Q. simpl. exact Hb.
  - apply binds_cons_iff in Hb. destruct Hb as [[HY Hb]|Hb].
    + exists Q. 
      (* goal: binds Y (bind_qua Q) ((y, subst_binding_te X U b) :: subst_env_te X U E1 ++ E2) *)
      subst y. destruct b as [Vb|Tb|Qb].
      * inversion Hb.
      * inversion Hb.
      * simpl in Hb. inversion Hb. subst Qb. simpl. apply binds_cons_2; auto.
    + destruct (IH E2 X U V Y Q Hb) as [Q' HQ']. exists Q'. apply binds_cons. exact HQ'.
Qed.

Lemma wf_qua_te_subst_gen : forall E1 E2 X U V Q,
  wf_qua (E1 ++ (X, bind_sub V) :: E2) Q ->
  wf_qua (subst_env_te X U E1 ++ E2) Q.
Proof.
  intros E1 E2 X U V Q H.
  dependent induction H.
  - apply wf_qua_base.
  - destruct (binds_subst_env_te_qua E1 E2 X U V X0 R H) as [R' HR'].
    eapply wf_qua_fvar. exact HR'.
  - apply wf_qua_meet.
    + apply (IHwf_qua1 E1 E2 X V eq_refl).
    + apply (IHwf_qua2 E1 E2 X V eq_refl).
  - apply wf_qua_join.
    + apply (IHwf_qua1 E1 E2 X V eq_refl).
    + apply (IHwf_qua2 E1 E2 X V eq_refl).
Qed.

Lemma wf_typ_te_subst_gen :
  (forall E T, wf_typ E T -> forall E1 E2 X U V,
     E = E1 ++ (X, bind_sub V) :: E2 -> sub E2 U V ->
     wf_typ (subst_env_te X U E1 ++ E2) (subst_tt X U T)) /\
  (forall E T, wf_qtyp E T -> forall E1 E2 X U V,
     E = E1 ++ (X, bind_sub V) :: E2 -> sub E2 U V ->
     wf_qtyp (subst_env_te X U E1 ++ E2) (subst_tqt X U T)).
Proof.
  split.
  - apply (wf_mut_ind
      (fun E T D => forall E1 E2 X U V,
         E = E1 ++ (X, bind_sub V) :: E2 -> sub E2 U V ->
         wf_typ (subst_env_te X U E1 ++ E2) (subst_tt X U T))
      (fun E T D => forall E1 E2 X U V,
         E = E1 ++ (X, bind_sub V) :: E2 -> sub E2 U V ->
         wf_qtyp (subst_env_te X U E1 ++ E2) (subst_tqt X U T))).
    + (* top *) intros E E1 E2 X U V HE Hs. subst E. apply wf_typ_top.
    + (* var *) intros U0 E Y Hb E1 E2 X U V HE Hs. subst E.
      destruct (X == Y) as [Heq|Hneq].
      * subst Y. rewrite subst_tt_fvar_eq.
        destruct (sub_wf E2 U V Hs) as [_ [HU _]].
        apply (wf_typ_incl E2 (subst_env_te X U E1 ++ E2) U).
        -- intros z b Hz. apply binds_app_r with (E := subst_env_te X U E1). exact Hz.
        -- exact HU.
      * rewrite (subst_tt_fvar_neq X Y U Hneq).
        destruct (binds_subst_env_te_sub E1 E2 X U V Y U0 Hb) as [HY|[W' HW']].
        -- subst Y. contradiction.
        -- eapply wf_typ_var. exact HW'.
    + (* arrow *) intros E T1 T2 H1 IH1 H2 IH2 E1 E2 X U V HE Hs. subst E.
      simpl. apply wf_typ_arrow.
      * apply (IH1 E1 E2 X U V eq_refl Hs).
      * apply (IH2 E1 E2 X U V eq_refl Hs).
    + (* all *) intros L E T1 T2 H1 IH1 H2 IH2 E1 E2 X U V HE Hs. subst E.
      simpl.
      destruct (sub_wf E2 U V Hs) as [_ [HU _]].
      pose proof (wf_typ_type E2 U HU) as HUt.
      apply (wf_typ_all (add X L) (subst_env_te X U E1 ++ E2)
             (subst_tt X U T1) (subst_tqt X U T2)).
      * apply (IH1 E1 E2 X U V eq_refl Hs).
      * intros Y HY.
        assert (HYL : Y `notin` L) by (simpl in HY; fsetdec).
        assert (HYX : Y <> X) by (intro Hc; subst Y; simpl in HY; fsetdec).
        assert (Hcomm : subst_tqt X U (open_tqt_rec 0 Y T2) =
                        open_tqt_rec 0 Y (subst_tqt X U T2)).
        { rewrite (subst_tqt_open_tqt_rec T2 0 X U Y HUt).
          rewrite (subst_tt_fvar_neq X Y U (fun Hc => HYX (eq_sym Hc))).
          reflexivity. }
        unfold open_tqt.
        rewrite <- Hcomm.
        apply (IH2 Y HYL ((Y, bind_sub T1) :: E1) E2 X U V eq_refl Hs).
    + (* qall *) intros L E T1 T2 H1 H2 IH2 E1 E2 X U V HE Hs. subst E.
      simpl.
      destruct (sub_wf E2 U V Hs) as [_ [HU _]].
      pose proof (wf_typ_type E2 U HU) as HUt.
      apply (wf_typ_qall L (subst_env_te X U E1 ++ E2) T1 (subst_tqt X U T2)).
      * apply (wf_qua_te_subst_gen E1 E2 X U V T1 H1).
      * intros Y HY.
        assert (Hcomm : subst_tqt X U (open_qqt_rec 0 Y T2) =
                        open_qqt_rec 0 Y (subst_tqt X U T2)).
        { rewrite (subst_tqt_open_qqt_rec T2 0 X U Y HUt). reflexivity. }
        unfold open_qqt.
        rewrite <- Hcomm.
        apply (IH2 Y HY ((Y, bind_qua T1) :: E1) E2 X U V eq_refl Hs).
    + (* sum *) intros E T1 T2 H1 IH1 H2 IH2 E1 E2 X U V HE Hs. subst E.
      simpl. apply wf_typ_sum;
        [apply (IH1 E1 E2 X U V eq_refl Hs)|apply (IH2 E1 E2 X U V eq_refl Hs)].
    + (* pair *) intros E T1 T2 H1 IH1 H2 IH2 E1 E2 X U V HE Hs. subst E.
      simpl. apply wf_typ_pair;
        [apply (IH1 E1 E2 X U V eq_refl Hs)|apply (IH2 E1 E2 X U V eq_refl Hs)].
    + (* qtyp *) intros E Q T Hq Ht IH E1 E2 X U V HE Hs. subst E.
      simpl. apply wf_qtyp_qtyp.
      * apply (wf_qua_te_subst_gen E1 E2 X U V Q Hq).
      * apply (IH E1 E2 X U V eq_refl Hs).
  - apply (wfq_mut_ind
      (fun E T D => forall E1 E2 X U V,
         E = E1 ++ (X, bind_sub V) :: E2 -> sub E2 U V ->
         wf_typ (subst_env_te X U E1 ++ E2) (subst_tt X U T))
      (fun E T D => forall E1 E2 X U V,
         E = E1 ++ (X, bind_sub V) :: E2 -> sub E2 U V ->
         wf_qtyp (subst_env_te X U E1 ++ E2) (subst_tqt X U T))).
    + intros E E1 E2 X U V HE Hs. subst E. apply wf_typ_top.
    + intros U0 E Y Hb E1 E2 X U V HE Hs. subst E.
      destruct (X == Y) as [Heq|Hneq].
      * subst Y. rewrite subst_tt_fvar_eq.
        destruct (sub_wf E2 U V Hs) as [_ [HU _]].
        apply (wf_typ_incl E2 (subst_env_te X U E1 ++ E2) U).
        -- intros z b Hz. apply binds_app_r with (E := subst_env_te X U E1). exact Hz.
        -- exact HU.
      * rewrite (subst_tt_fvar_neq X Y U Hneq).
        destruct (binds_subst_env_te_sub E1 E2 X U V Y U0 Hb) as [HY|[W' HW']].
        -- subst Y. contradiction.
        -- eapply wf_typ_var. exact HW'.
    + intros E T1 T2 H1 IH1 H2 IH2 E1 E2 X U V HE Hs. subst E.
      simpl. apply wf_typ_arrow;
        [apply (IH1 E1 E2 X U V eq_refl Hs)|apply (IH2 E1 E2 X U V eq_refl Hs)].
    + intros L E T1 T2 H1 IH1 H2 IH2 E1 E2 X U V HE Hs. subst E.
      simpl.
      destruct (sub_wf E2 U V Hs) as [_ [HU _]].
      pose proof (wf_typ_type E2 U HU) as HUt.
      apply (wf_typ_all (add X L) (subst_env_te X U E1 ++ E2)
             (subst_tt X U T1) (subst_tqt X U T2)).
      * apply (IH1 E1 E2 X U V eq_refl Hs).
      * intros Y HY.
        assert (HYL : Y `notin` L) by (simpl in HY; fsetdec).
        assert (HYX : Y <> X) by (intro Hc; subst Y; simpl in HY; fsetdec).
        assert (Hcomm : subst_tqt X U (open_tqt_rec 0 Y T2) =
                        open_tqt_rec 0 Y (subst_tqt X U T2)).
        { rewrite (subst_tqt_open_tqt_rec T2 0 X U Y HUt).
          rewrite (subst_tt_fvar_neq X Y U (fun Hc => HYX (eq_sym Hc))).
          reflexivity. }
        unfold open_tqt.
        rewrite <- Hcomm.
        apply (IH2 Y HYL ((Y, bind_sub T1) :: E1) E2 X U V eq_refl Hs).
    + intros L E T1 T2 H1 H2 IH2 E1 E2 X U V HE Hs. subst E.
      simpl.
      destruct (sub_wf E2 U V Hs) as [_ [HU _]].
      pose proof (wf_typ_type E2 U HU) as HUt.
      apply (wf_typ_qall L (subst_env_te X U E1 ++ E2) T1 (subst_tqt X U T2)).
      * apply (wf_qua_te_subst_gen E1 E2 X U V T1 H1).
      * intros Y HY.
        assert (Hcomm : subst_tqt X U (open_qqt_rec 0 Y T2) =
                        open_qqt_rec 0 Y (subst_tqt X U T2)).
        { rewrite (subst_tqt_open_qqt_rec T2 0 X U Y HUt). reflexivity. }
        unfold open_qqt.
        rewrite <- Hcomm.
        apply (IH2 Y HY ((Y, bind_qua T1) :: E1) E2 X U V eq_refl Hs).
    + intros E T1 T2 H1 IH1 H2 IH2 E1 E2 X U V HE Hs. subst E.
      simpl. apply wf_typ_sum;
        [apply (IH1 E1 E2 X U V eq_refl Hs)|apply (IH2 E1 E2 X U V eq_refl Hs)].
    + intros E T1 T2 H1 IH1 H2 IH2 E1 E2 X U V HE Hs. subst E.
      simpl. apply wf_typ_pair;
        [apply (IH1 E1 E2 X U V eq_refl Hs)|apply (IH2 E1 E2 X U V eq_refl Hs)].
    + intros E Q T Hq Ht IH E1 E2 X U V HE Hs. subst E.
      simpl. apply wf_qtyp_qtyp.
      * apply (wf_qua_te_subst_gen E1 E2 X U V Q Hq).
      * apply (IH E1 E2 X U V eq_refl Hs).
Qed.

Lemma notin_dom_subst_env : forall E1 E2 X U V y,
  y `notin` dom (E1 ++ (X, bind_sub V) :: E2) ->
  y `notin` dom (subst_env_te X U E1 ++ E2).
Proof.
  intros E1 E2 X U V y H.
  assert (Hd : dom (subst_env_te X U E1 ++ E2) [=] union (dom E1) (dom E2)).
  { rewrite dom_app. rewrite dom_subst_env_te. reflexivity. }
  assert (Hd2 : dom (E1 ++ (X, bind_sub V) :: E2) [=]
                union (dom E1) (union (singleton X) (dom E2))).
  { rewrite dom_app. rewrite dom_cons. reflexivity. }
  setoid_rewrite Hd.
  setoid_rewrite Hd2 in H.
  fsetdec.
Qed.

Lemma wf_env_te_subst_gen : forall E1 E2 X U V,
  sub E2 U V ->
  wf_env (E1 ++ (X, bind_sub V) :: E2) ->
  wf_env (subst_env_te X U E1 ++ E2).
Proof.
  induction E1 as [|[y b] E1 IH]; intros E2 X U V Hs Hwf; simpl in *.
  - inversion Hwf; subst. assumption.
  - destruct b as [T|T|Q].
    + inversion Hwf; subst.
      apply wf_env_sub with (X := y).
      * apply (IH E2 X U V Hs H2).
      * apply (proj1 wf_typ_te_subst_gen (E1 ++ (X, bind_sub V) :: E2) T H3 E1 E2 X U V eq_refl Hs).
      * apply (notin_dom_subst_env E1 E2 X U V y H4).
    + inversion Hwf; subst.
      apply wf_env_typ with (x := y).
      * apply (IH E2 X U V Hs H2).
      * apply (proj2 wf_typ_te_subst_gen (E1 ++ (X, bind_sub V) :: E2) T H3 E1 E2 X U V eq_refl Hs).
      * apply (notin_dom_subst_env E1 E2 X U V y H4).
    + inversion Hwf; subst.
      apply wf_env_qua with (X := y).
      * apply (IH E2 X U V Hs H2).
      * apply (wf_qua_te_subst_gen E1 E2 X U V Q H3).
      * apply (notin_dom_subst_env E1 E2 X U V y H4).
Qed.


(* ================================================================== *)
(* Free-variable/domain facts for well-formed types                 *)
(* ================================================================== *)
Lemma fv_qua_open_qq_sub : forall Q K (X : atom),
  fv_qua (open_qq_rec K (qua_fvar X) Q) [<=] union (fv_qua Q) (singleton X).
Proof.
  induction Q; intros K X z Hz; simpl in *.
  - fsetdec.
  - destruct (K == n); simpl in *; fsetdec.
  - fsetdec.
  - apply union_iff in Hz. destruct Hz as [Hz|Hz].
    + apply (IHQ1 K X) in Hz. fsetdec.
    + apply (IHQ2 K X) in Hz. fsetdec.
  - apply union_iff in Hz. destruct Hz as [Hz|Hz].
    + apply (IHQ1 K X) in Hz. fsetdec.
    + apply (IHQ2 K X) in Hz. fsetdec.
Qed.

Lemma fv_qua_open_qq_rev : forall Q K (X : atom),
  fv_qua Q [<=] union (fv_qua (open_qq_rec K (qua_fvar X) Q)) (singleton X).
Proof.
  induction Q; intros K X z Hz; simpl in *.
  - fsetdec.
  - destruct (K == n); simpl in *; fsetdec.
  - fsetdec.
  - apply union_iff in Hz. destruct Hz as [Hz|Hz].
    + apply (IHQ1 K X) in Hz. fsetdec.
    + apply (IHQ2 K X) in Hz. fsetdec.
  - apply union_iff in Hz. destruct Hz as [Hz|Hz].
    + apply (IHQ1 K X) in Hz. fsetdec.
    + apply (IHQ2 K X) in Hz. fsetdec.
Qed.

Lemma fv_open_tt_sub :
  (forall T K (X : atom), fv_typ (open_tt_rec K X T) [<=] union (fv_typ T) (singleton X)) /\
  (forall T : qtyp, forall K (X : atom),
     fv_qtyp (open_tqt_rec K X T) [<=] union (fv_qtyp T) (singleton X)).
Proof.
  split.
  - apply (typ_mut_ind
      (fun T => forall K (X : atom), fv_typ (open_tt_rec K X T) [<=] union (fv_typ T) (singleton X))
      (fun T => forall K (X : atom), fv_qtyp (open_tqt_rec K X T) [<=] union (fv_qtyp T) (singleton X))).
    + intros; simpl. intros z Hz; fsetdec.
    + intros n K X. simpl. destruct (K == n); simpl.
      * intros z Hz. simpl in *. fsetdec.
      * intros z Hz; fsetdec.
    + intros; simpl. intros z Hz; fsetdec.
    + intros q1 IH1 q2 IH2 K X. simpl. intros z Hz.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * apply (IH1 K X) in Hz. apply union_iff in Hz. destruct Hz as [Hz|Hz].
        -- fsetdec.
        -- fsetdec.
      * apply (IH2 (S K) X) in Hz. apply union_iff in Hz. destruct Hz as [Hz|Hz].
        -- fsetdec.
        -- fsetdec.
    + intros T1 IH1 q IH2 K X. simpl. intros z Hz.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * apply (IH1 K X) in Hz. apply union_iff in Hz. destruct Hz as [Hz|Hz]; fsetdec.
      * apply (IH2 (S K) X) in Hz. apply union_iff in Hz. destruct Hz as [Hz|Hz]; fsetdec.
    + intros Q q IH K X z Hz. simpl in *.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * fsetdec.
      * apply (IH (S K) X) in Hz. fsetdec.
    + intros q1 IH1 q2 IH2 K X. simpl. intros z Hz.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * apply (IH1 K X) in Hz. apply union_iff in Hz. destruct Hz as [Hz|Hz]; fsetdec.
      * apply (IH2 K X) in Hz. apply union_iff in Hz. destruct Hz as [Hz|Hz]; fsetdec.
    + intros q1 IH1 q2 IH2 K X. simpl. intros z Hz.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * apply (IH1 K X) in Hz. apply union_iff in Hz. destruct Hz as [Hz|Hz]; fsetdec.
      * apply (IH2 K X) in Hz. apply union_iff in Hz. destruct Hz as [Hz|Hz]; fsetdec.
    + intros q IH K X. simpl. intros z Hz. apply (IH K X) in Hz.
      apply union_iff in Hz. destruct Hz as [Hz|Hz]; fsetdec.
    + intros Q T IH K X z Hz. simpl in *.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * fsetdec.
      * apply (IH K X) in Hz. fsetdec.
  - apply (qtyp_mut_ind
      (fun T => forall K (X : atom), fv_typ (open_tt_rec K X T) [<=] union (fv_typ T) (singleton X))
      (fun T => forall K (X : atom), fv_qtyp (open_tqt_rec K X T) [<=] union (fv_qtyp T) (singleton X))).
    + intros; simpl. intros z Hz; fsetdec.
    + intros n K X. simpl. destruct (K == n); simpl.
      * intros z Hz. simpl in *. fsetdec.
      * intros z Hz; fsetdec.
    + intros; simpl. intros z Hz; fsetdec.
    + intros q1 IH1 q2 IH2 K X. simpl. intros z Hz.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * apply (IH1 K X) in Hz. apply union_iff in Hz. destruct Hz as [Hz|Hz]; fsetdec.
      * apply (IH2 (S K) X) in Hz. apply union_iff in Hz. destruct Hz as [Hz|Hz]; fsetdec.
    + intros T1 IH1 q IH2 K X. simpl. intros z Hz.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * apply (IH1 K X) in Hz. apply union_iff in Hz. destruct Hz as [Hz|Hz]; fsetdec.
      * apply (IH2 (S K) X) in Hz. apply union_iff in Hz. destruct Hz as [Hz|Hz]; fsetdec.
    + intros Q q IH K X z Hz. simpl in *.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * fsetdec.
      * apply (IH (S K) X) in Hz. fsetdec.
    + intros q1 IH1 q2 IH2 K X. simpl. intros z Hz.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * apply (IH1 K X) in Hz. apply union_iff in Hz. destruct Hz as [Hz|Hz]; fsetdec.
      * apply (IH2 K X) in Hz. apply union_iff in Hz. destruct Hz as [Hz|Hz]; fsetdec.
    + intros q1 IH1 q2 IH2 K X. simpl. intros z Hz.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * apply (IH1 K X) in Hz. apply union_iff in Hz. destruct Hz as [Hz|Hz]; fsetdec.
      * apply (IH2 K X) in Hz. apply union_iff in Hz. destruct Hz as [Hz|Hz]; fsetdec.
    + intros q IH K X. simpl. intros z Hz. apply (IH K X) in Hz.
      apply union_iff in Hz. destruct Hz as [Hz|Hz]; fsetdec.
    + intros Q T IH K X z Hz. simpl in *.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * fsetdec.
      * apply (IH K X) in Hz. fsetdec.
Qed.

Lemma fv_open_tt_rev :
  (forall T K (X : atom), fv_typ T [<=] union (fv_typ (open_tt_rec K X T)) (singleton X)) /\
  (forall T : qtyp, forall K (X : atom),
     fv_qtyp T [<=] union (fv_qtyp (open_tqt_rec K X T)) (singleton X)).
Proof.
  split.
  - apply (typ_mut_ind
      (fun T => forall K (X : atom), fv_typ T [<=] union (fv_typ (open_tt_rec K X T)) (singleton X))
      (fun T => forall K (X : atom), fv_qtyp T [<=] union (fv_qtyp (open_tqt_rec K X T)) (singleton X))).
    + intros; simpl. intros z Hz; fsetdec.
    + intros n K X. simpl. destruct (K == n); simpl.
      * intros z Hz. simpl in *. fsetdec.
      * intros z Hz; fsetdec.
    + intros; simpl. intros z Hz; fsetdec.
    + intros q1 IH1 q2 IH2 K X. simpl. intros z Hz.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * apply (IH1 K X) in Hz. apply union_iff in Hz. destruct Hz as [Hz|Hz]; fsetdec.
      * apply (IH2 (S K) X) in Hz. apply union_iff in Hz. destruct Hz as [Hz|Hz]; fsetdec.
    + intros T1 IH1 q IH2 K X. simpl. intros z Hz.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * apply (IH1 K X) in Hz. apply union_iff in Hz. destruct Hz as [Hz|Hz]; fsetdec.
      * apply (IH2 (S K) X) in Hz. apply union_iff in Hz. destruct Hz as [Hz|Hz]; fsetdec.
    + intros Q q IH K X z Hz. simpl in *.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * fsetdec.
      * apply (IH (S K) X) in Hz. fsetdec.
    + intros q1 IH1 q2 IH2 K X. simpl. intros z Hz.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * apply (IH1 K X) in Hz. apply union_iff in Hz. destruct Hz as [Hz|Hz]; fsetdec.
      * apply (IH2 K X) in Hz. apply union_iff in Hz. destruct Hz as [Hz|Hz]; fsetdec.
    + intros q1 IH1 q2 IH2 K X. simpl. intros z Hz.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * apply (IH1 K X) in Hz. apply union_iff in Hz. destruct Hz as [Hz|Hz]; fsetdec.
      * apply (IH2 K X) in Hz. apply union_iff in Hz. destruct Hz as [Hz|Hz]; fsetdec.
    + intros q IH K X. simpl. intros z Hz.
      apply (IH K X) in Hz. apply union_iff in Hz. destruct Hz as [Hz|Hz]; fsetdec.
    + intros Q T IH K X z Hz. simpl in *.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * fsetdec.
      * apply (IH K X) in Hz. fsetdec.
  - apply (qtyp_mut_ind
      (fun T => forall K (X : atom), fv_typ T [<=] union (fv_typ (open_tt_rec K X T)) (singleton X))
      (fun T => forall K (X : atom), fv_qtyp T [<=] union (fv_qtyp (open_tqt_rec K X T)) (singleton X))).
    + intros; simpl. intros z Hz; fsetdec.
    + intros n K X. simpl. destruct (K == n); simpl.
      * intros z Hz. simpl in *. fsetdec.
      * intros z Hz; fsetdec.
    + intros; simpl. intros z Hz; fsetdec.
    + intros q1 IH1 q2 IH2 K X. simpl. intros z Hz.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * apply (IH1 K X) in Hz. apply union_iff in Hz. destruct Hz as [Hz|Hz]; fsetdec.
      * apply (IH2 (S K) X) in Hz. apply union_iff in Hz. destruct Hz as [Hz|Hz]; fsetdec.
    + intros T1 IH1 q IH2 K X. simpl. intros z Hz.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * apply (IH1 K X) in Hz. apply union_iff in Hz. destruct Hz as [Hz|Hz]; fsetdec.
      * apply (IH2 (S K) X) in Hz. apply union_iff in Hz. destruct Hz as [Hz|Hz]; fsetdec.
    + intros Q q IH K X z Hz. simpl in *.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * fsetdec.
      * apply (IH (S K) X) in Hz. fsetdec.
    + intros q1 IH1 q2 IH2 K X. simpl. intros z Hz.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * apply (IH1 K X) in Hz. apply union_iff in Hz. destruct Hz as [Hz|Hz]; fsetdec.
      * apply (IH2 K X) in Hz. apply union_iff in Hz. destruct Hz as [Hz|Hz]; fsetdec.
    + intros q1 IH1 q2 IH2 K X. simpl. intros z Hz.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * apply (IH1 K X) in Hz. apply union_iff in Hz. destruct Hz as [Hz|Hz]; fsetdec.
      * apply (IH2 K X) in Hz. apply union_iff in Hz. destruct Hz as [Hz|Hz]; fsetdec.
    + intros q IH K X. simpl. intros z Hz.
      apply (IH K X) in Hz. apply union_iff in Hz. destruct Hz as [Hz|Hz]; fsetdec.
    + intros Q T IH K X z Hz. simpl in *.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * fsetdec.
      * apply (IH K X) in Hz. fsetdec.
Qed.

Lemma fv_open_qt_sub :
  (forall T K (X : atom),
     fv_typ (open_qt_rec K (qua_fvar X) T) [<=] union (fv_typ T) (singleton X)) /\
  (forall T : qtyp, forall K (X : atom),
     fv_qtyp (open_qqt_rec K (qua_fvar X) T) [<=] union (fv_qtyp T) (singleton X)).
Proof.
  split.
  - apply (typ_mut_ind
      (fun T => forall K (X : atom),
         fv_typ (open_qt_rec K (qua_fvar X) T) [<=] union (fv_typ T) (singleton X))
      (fun T => forall K (X : atom),
         fv_qtyp (open_qqt_rec K (qua_fvar X) T) [<=] union (fv_qtyp T) (singleton X))).
    + intros; simpl. intros z Hz; fsetdec.
    + intros; simpl. intros z Hz; fsetdec.
    + intros; simpl. intros z Hz; fsetdec.
    + intros q1 IH1 q2 IH2 K X z Hz. simpl in *.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * apply (IH1 K X) in Hz. fsetdec.
      * apply (IH2 (S K) X) in Hz. fsetdec.
    + intros T1 IH1 q IH2 K X z Hz. simpl in *.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * apply (IH1 K X) in Hz. fsetdec.
      * apply (IH2 (S K) X) in Hz. fsetdec.
    + intros Q q IH K X z Hz. simpl in *.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * apply (fv_qua_open_qq_sub Q K X) in Hz. fsetdec.
      * apply (IH (S K) X) in Hz. fsetdec.
    + intros q1 IH1 q2 IH2 K X z Hz. simpl in *.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * apply (IH1 K X) in Hz. fsetdec.
      * apply (IH2 K X) in Hz. fsetdec.
    + intros q1 IH1 q2 IH2 K X z Hz. simpl in *.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * apply (IH1 K X) in Hz. fsetdec.
      * apply (IH2 K X) in Hz. fsetdec.
    + intros q IH K X z Hz. simpl in *.
      apply (IH K X) in Hz. fsetdec.
    + intros Q T IH K X z Hz. simpl in *.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * apply (fv_qua_open_qq_sub Q K X) in Hz. fsetdec.
      * apply (IH K X) in Hz. fsetdec.
  - apply (qtyp_mut_ind
      (fun T => forall K (X : atom),
         fv_typ (open_qt_rec K (qua_fvar X) T) [<=] union (fv_typ T) (singleton X))
      (fun T => forall K (X : atom),
         fv_qtyp (open_qqt_rec K (qua_fvar X) T) [<=] union (fv_qtyp T) (singleton X))).
    + intros; simpl. intros z Hz; fsetdec.
    + intros; simpl. intros z Hz; fsetdec.
    + intros; simpl. intros z Hz; fsetdec.
    + intros q1 IH1 q2 IH2 K X z Hz. simpl in *.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * apply (IH1 K X) in Hz. fsetdec.
      * apply (IH2 (S K) X) in Hz. fsetdec.
    + intros T1 IH1 q IH2 K X z Hz. simpl in *.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * apply (IH1 K X) in Hz. fsetdec.
      * apply (IH2 (S K) X) in Hz. fsetdec.
    + intros Q q IH K X z Hz. simpl in *.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * apply (fv_qua_open_qq_sub Q K X) in Hz. fsetdec.
      * apply (IH (S K) X) in Hz. fsetdec.
    + intros q1 IH1 q2 IH2 K X z Hz. simpl in *.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * apply (IH1 K X) in Hz. fsetdec.
      * apply (IH2 K X) in Hz. fsetdec.
    + intros q1 IH1 q2 IH2 K X z Hz. simpl in *.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * apply (IH1 K X) in Hz. fsetdec.
      * apply (IH2 K X) in Hz. fsetdec.
    + intros q IH K X z Hz. simpl in *.
      apply (IH K X) in Hz. fsetdec.
    + intros Q T IH K X z Hz. simpl in *.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * apply (fv_qua_open_qq_sub Q K X) in Hz. fsetdec.
      * apply (IH K X) in Hz. fsetdec.
Qed.

Lemma fv_open_qt_rev :
  (forall T K (X : atom),
     fv_typ T [<=] union (fv_typ (open_qt_rec K (qua_fvar X) T)) (singleton X)) /\
  (forall T : qtyp, forall K (X : atom),
     fv_qtyp T [<=] union (fv_qtyp (open_qqt_rec K (qua_fvar X) T)) (singleton X)).
Proof.
  split.
  - apply (typ_mut_ind
      (fun T => forall K (X : atom),
         fv_typ T [<=] union (fv_typ (open_qt_rec K (qua_fvar X) T)) (singleton X))
      (fun T => forall K (X : atom),
         fv_qtyp T [<=] union (fv_qtyp (open_qqt_rec K (qua_fvar X) T)) (singleton X))).
    + intros; simpl. intros z Hz; fsetdec.
    + intros; simpl. intros z Hz; fsetdec.
    + intros; simpl. intros z Hz; fsetdec.
    + intros q1 IH1 q2 IH2 K X z Hz. simpl in *.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * apply (IH1 K X) in Hz. fsetdec.
      * apply (IH2 (S K) X) in Hz. fsetdec.
    + intros T1 IH1 q IH2 K X z Hz. simpl in *.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * apply (IH1 K X) in Hz. fsetdec.
      * apply (IH2 (S K) X) in Hz. fsetdec.
    + intros Q q IH K X z Hz. simpl in *.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * apply (fv_qua_open_qq_rev Q K X) in Hz. fsetdec.
      * apply (IH (S K) X) in Hz. fsetdec.
    + intros q1 IH1 q2 IH2 K X z Hz. simpl in *.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * apply (IH1 K X) in Hz. fsetdec.
      * apply (IH2 K X) in Hz. fsetdec.
    + intros q1 IH1 q2 IH2 K X z Hz. simpl in *.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * apply (IH1 K X) in Hz. fsetdec.
      * apply (IH2 K X) in Hz. fsetdec.
    + intros q IH K X z Hz. simpl in *.
      apply (IH K X) in Hz. fsetdec.
    + intros Q T IH K X z Hz. simpl in *.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * apply (fv_qua_open_qq_rev Q K X) in Hz. fsetdec.
      * apply (IH K X) in Hz. fsetdec.
  - apply (qtyp_mut_ind
      (fun T => forall K (X : atom),
         fv_typ T [<=] union (fv_typ (open_qt_rec K (qua_fvar X) T)) (singleton X))
      (fun T => forall K (X : atom),
         fv_qtyp T [<=] union (fv_qtyp (open_qqt_rec K (qua_fvar X) T)) (singleton X))).
    + intros; simpl. intros z Hz; fsetdec.
    + intros; simpl. intros z Hz; fsetdec.
    + intros; simpl. intros z Hz; fsetdec.
    + intros q1 IH1 q2 IH2 K X z Hz. simpl in *.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * apply (IH1 K X) in Hz. fsetdec.
      * apply (IH2 (S K) X) in Hz. fsetdec.
    + intros T1 IH1 q IH2 K X z Hz. simpl in *.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * apply (IH1 K X) in Hz. fsetdec.
      * apply (IH2 (S K) X) in Hz. fsetdec.
    + intros Q q IH K X z Hz. simpl in *.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * apply (fv_qua_open_qq_rev Q K X) in Hz. fsetdec.
      * apply (IH (S K) X) in Hz. fsetdec.
    + intros q1 IH1 q2 IH2 K X z Hz. simpl in *.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * apply (IH1 K X) in Hz. fsetdec.
      * apply (IH2 K X) in Hz. fsetdec.
    + intros q1 IH1 q2 IH2 K X z Hz. simpl in *.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * apply (IH1 K X) in Hz. fsetdec.
      * apply (IH2 K X) in Hz. fsetdec.
    + intros q IH K X z Hz. simpl in *.
      apply (IH K X) in Hz. fsetdec.
    + intros Q T IH K X z Hz. simpl in *.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * apply (fv_qua_open_qq_rev Q K X) in Hz. fsetdec.
      * apply (IH K X) in Hz. fsetdec.
Qed.

Lemma wf_qua_fv_dom : forall E Q, wf_qua E Q -> fv_qua Q [<=] dom E.
Proof.
  intros E Q H. induction H as
    [ E b
    | R E X Hb
    | E Q1 Q2 H1 IH1 H2 IH2
    | E Q1 Q2 H1 IH1 H2 IH2 ]; intros z Hz; simpl in *.
  - fsetdec.
  - apply binds_In in Hb. fsetdec.
  - apply union_iff in Hz. destruct Hz as [Hz|Hz].
    + apply IH1 in Hz. fsetdec.
    + apply IH2 in Hz. fsetdec.
  - apply union_iff in Hz. destruct Hz as [Hz|Hz].
    + apply IH1 in Hz. fsetdec.
    + apply IH2 in Hz. fsetdec.
Qed.

Lemma wf_typ_fv_dom :
  (forall E T, wf_typ E T -> fv_typ T [<=] dom E) /\
  (forall E T, wf_qtyp E T -> fv_qtyp T [<=] dom E).
Proof.
  split.
  - apply (wf_mut_ind
      (fun E T D => fv_typ T [<=] dom E)
      (fun E T D => fv_qtyp T [<=] dom E)).
    + intros E z Hz; simpl in *; fsetdec.
    + intros U E X Hb z Hz. simpl in *. apply binds_In in Hb. fsetdec.
    + intros E T1 T2 H1 IH1 H2 IH2 z Hz. simpl in *.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * apply IH1 in Hz. fsetdec.
      * apply IH2 in Hz. fsetdec.
    + intros L E T1 T2 H1 IH1 H2 IH2 z Hz. simpl in *.
      apply union_iff in Hz. destruct Hz as [Hzdom|Hzfv].
      * apply IH1 in Hzdom. fsetdec.
      * destruct (atom_fresh (union L (union (dom E) (fv_qtyp T2)))) as [Y HY].
        assert (HYL : Y `notin` L) by fsetdec.
        assert (HYdom : Y `notin` dom E) by fsetdec.
        assert (HYfv : Y `notin` fv_qtyp T2) by fsetdec.
        pose proof ((proj2 fv_open_tt_rev) T2 0 Y z Hzfv) as Hzo.
        apply union_iff in Hzo. destruct Hzo as [Hzo|HzY].
        { pose proof ((IH2 Y HYL) z Hzo). simpl in H. fsetdec. }
        { assert (Hz_eq : z = Y) by fsetdec. subst z. exfalso. exact (HYfv Hzfv). }
    + intros L E T1 T2 H1 H2 IH2 z Hz. simpl in *.
      apply union_iff in Hz. destruct Hz as [Hzdom|Hzfv].
      * apply (wf_qua_fv_dom E T1 H1) in Hzdom. fsetdec.
      * destruct (atom_fresh (union L (union (dom E) (fv_qtyp T2)))) as [Y HY].
        assert (HYL : Y `notin` L) by fsetdec.
        assert (HYdom : Y `notin` dom E) by fsetdec.
        assert (HYfv : Y `notin` fv_qtyp T2) by fsetdec.
        pose proof ((proj2 fv_open_qt_rev) T2 0 Y z Hzfv) as Hzo.
        apply union_iff in Hzo. destruct Hzo as [Hzo|HzY].
        { pose proof ((IH2 Y HYL) z Hzo). simpl in H. fsetdec. }
        { assert (Hz_eq : z = Y) by fsetdec. subst z. exfalso. exact (HYfv Hzfv). }
    + intros E T1 T2 H1 IH1 H2 IH2 z Hz. simpl in *.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * apply IH1 in Hz. fsetdec.
      * apply IH2 in Hz. fsetdec.
    + intros E T1 T2 H1 IH1 H2 IH2 z Hz. simpl in *.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * apply IH1 in Hz. fsetdec.
      * apply IH2 in Hz. fsetdec.
    + intros E Q T Hq Ht IH z Hz. simpl in *.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * apply (wf_qua_fv_dom E Q Hq) in Hz. fsetdec.
      * apply IH in Hz. fsetdec.
  - apply (wfq_mut_ind
      (fun E T D => fv_typ T [<=] dom E)
      (fun E T D => fv_qtyp T [<=] dom E)).
    + intros E z Hz; simpl in *; fsetdec.
    + intros U E X Hb z Hz. simpl in *. apply binds_In in Hb. fsetdec.
    + intros E T1 T2 H1 IH1 H2 IH2 z Hz. simpl in *.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * apply IH1 in Hz. fsetdec.
      * apply IH2 in Hz. fsetdec.
    + intros L E T1 T2 H1 IH1 H2 IH2 z Hz. simpl in *.
      apply union_iff in Hz. destruct Hz as [Hzdom|Hzfv].
      * apply IH1 in Hzdom. fsetdec.
      * destruct (atom_fresh (union L (union (dom E) (fv_qtyp T2)))) as [Y HY].
        assert (HYL : Y `notin` L) by fsetdec.
        assert (HYdom : Y `notin` dom E) by fsetdec.
        assert (HYfv : Y `notin` fv_qtyp T2) by fsetdec.
        pose proof ((proj2 fv_open_tt_rev) T2 0 Y z Hzfv) as Hzo.
        apply union_iff in Hzo. destruct Hzo as [Hzo|HzY].
        { pose proof ((IH2 Y HYL) z Hzo). simpl in H. fsetdec. }
        { assert (Hz_eq : z = Y) by fsetdec. subst z. exfalso. exact (HYfv Hzfv). }
    + intros L E T1 T2 H1 H2 IH2 z Hz. simpl in *.
      apply union_iff in Hz. destruct Hz as [Hzdom|Hzfv].
      * apply (wf_qua_fv_dom E T1 H1) in Hzdom. fsetdec.
      * destruct (atom_fresh (union L (union (dom E) (fv_qtyp T2)))) as [Y HY].
        assert (HYL : Y `notin` L) by fsetdec.
        assert (HYdom : Y `notin` dom E) by fsetdec.
        assert (HYfv : Y `notin` fv_qtyp T2) by fsetdec.
        pose proof ((proj2 fv_open_qt_rev) T2 0 Y z Hzfv) as Hzo.
        apply union_iff in Hzo. destruct Hzo as [Hzo|HzY].
        { pose proof ((IH2 Y HYL) z Hzo). simpl in H. fsetdec. }
        { assert (Hz_eq : z = Y) by fsetdec. subst z. exfalso. exact (HYfv Hzfv). }
    + intros E T1 T2 H1 IH1 H2 IH2 z Hz. simpl in *.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * apply IH1 in Hz. fsetdec.
      * apply IH2 in Hz. fsetdec.
    + intros E T1 T2 H1 IH1 H2 IH2 z Hz. simpl in *.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * apply IH1 in Hz. fsetdec.
      * apply IH2 in Hz. fsetdec.
    + intros E Q T Hq Ht IH z Hz. simpl in *.
      apply union_iff in Hz. destruct Hz as [Hz|Hz].
      * apply (wf_qua_fv_dom E Q Hq) in Hz. fsetdec.
      * apply IH in Hz. fsetdec.
Qed.


(* ================================================================== *)
(* Type-variable substitution for subtyping                       *)
(* ================================================================== *)
Lemma wf_env_suffix : forall E1 E2, wf_env (E1 ++ E2) -> wf_env E2.
Proof.
  induction E1 as [|[y b] E1 IH]; intros E2 Hwf; simpl in *.
  - exact Hwf.
  - apply IH. apply (wf_env_head_inv y b (E1 ++ E2) Hwf).
Qed.

Lemma wf_typ_fv_notin : forall E T X,
  wf_typ E T -> X `notin` dom E -> X `notin` fv_typ T.
Proof.
  intros E T X Hwf Hdom Hx.
  pose proof (proj1 wf_typ_fv_dom E T Hwf) as Hsub.
  apply Hsub in Hx. fsetdec.
Qed.

Lemma wf_qtyp_fv_notin : forall E T X,
  wf_qtyp E T -> X `notin` dom E -> X `notin` fv_qtyp T.
Proof.
  intros E T X Hwf Hdom Hx.
  pose proof (proj2 wf_typ_fv_dom E T Hwf) as Hsub.
  apply Hsub in Hx. fsetdec.
Qed.

Lemma wf_qua_fv_notin : forall E Q X,
  wf_qua E Q -> X `notin` dom E -> X `notin` fv_qua Q.
Proof.
  intros E Q X Hwf Hdom Hx.
  pose proof (wf_qua_fv_dom E Q Hwf) as Hsub.
  apply Hsub in Hx. fsetdec.
Qed.

Lemma binds_subst_env_te_sub_payload : forall E1 X U Y W,
  binds Y (bind_sub W) E1 ->
  exists W', binds Y (bind_sub W') (subst_env_te X U E1) /\
              W' = subst_tt X U W.
Proof.
  induction E1 as [|[y b] E1 IH]; intros X U Y W Hb; simpl in *.
  - inversion Hb.
  - apply binds_cons_iff in Hb. destruct Hb as [[HY Hb]|Hb].
    + subst y. destruct b as [Vb|Tb|Qb].
      * inversion Hb. subst Vb.
        exists (subst_tt X U W). split.
        -- simpl. apply binds_cons_2; auto.
        -- reflexivity.
      * inversion Hb.
      * inversion Hb.
    + destruct (IH X U Y W Hb) as [W' [HW' Heq]].
      exists W'. split.
      * apply binds_cons. exact HW'.
      * exact Heq.
Qed.

Lemma binds_te_qua_payload : forall E1 E2 X U V Y Q,
  binds Y (bind_qua Q) (E1 ++ (X, bind_sub V) :: E2) ->
  exists Q', binds Y (bind_qua Q') (subst_env_te X U E1 ++ E2) /\ Q' = Q.
Proof.
  induction E1 as [|[y b] E1 IH]; intros E2 X U V Y Q Hb; simpl in *.
  - apply binds_cons_iff in Hb. destruct Hb as [[HY Hb]|Hb].
    + inversion Hb.
    + exists Q. split; [ simpl; exact Hb | reflexivity ].
  - apply binds_cons_iff in Hb. destruct Hb as [[HY Hb]|Hb].
    + subst y. destruct b as [Vb|Tb|Qb].
      * inversion Hb.
      * inversion Hb.
      * inversion Hb. subst Qb. exists Q. split.
        -- simpl. apply binds_cons_2; auto.
        -- reflexivity.
    + destruct (IH E2 X U V Y Q Hb) as [Q' [HQ' Heq]].
      exists Q'. split.
      * apply binds_cons. exact HQ'.
      * exact Heq.
Qed.

Lemma binds_te_split : forall E1 E2 X U V Y W,
  wf_env (E1 ++ (X, bind_sub V) :: E2) ->
  binds Y (bind_sub W) (E1 ++ (X, bind_sub V) :: E2) ->
  (Y = X /\ W = V) \/
  (Y <> X /\ exists W', binds Y (bind_sub W') (subst_env_te X U E1 ++ E2) /\
                         W' = subst_tt X U W).
Proof.
  intros E1 E2 X U V Y W Hwf Hb.
  pose proof (wf_env_uniq _ Hwf) as Hu.
  pose proof (uniq_app_2 binding E1 ((X, bind_sub V) :: E2) Hu) as HuF.
  rewrite (binds_app_uniq_iff binding Y (bind_sub W) E1 ((X, bind_sub V) :: E2) Hu) in Hb.
  destruct Hb as [[HbE1 Hnotin] | [HbMid HnotinE1]].
  - right. assert (HYX : Y <> X).
    { intro Heq. subst Y. apply Hnotin. simpl. fsetdec. }
    split; [exact HYX|].
    destruct (binds_subst_env_te_sub_payload E1 X U Y W HbE1) as [W' [HW' Heq]].
    exists W'. split.
    + apply binds_app_l. exact HW'.
    + exact Heq.
  - rewrite (binds_cons_uniq_iff binding Y X (bind_sub W) (bind_sub V) E2 HuF) in HbMid.
    destruct HbMid as [[Heq [HWV HnotinE2]] | [HbE2 Hneq]].
    + left. split.
      * exact Heq.
      * inversion HWV. reflexivity.
    + right. split; [exact Hneq|].
      assert (HwfE2 : wf_env E2).
      { apply (wf_env_head_inv X (bind_sub V) E2).
        apply (wf_env_suffix E1 ((X, bind_sub V) :: E2) Hwf). }
      assert (HWE2 : wf_typ E2 W).
      { change (wf_typ E2 W).
        apply (wf_env_binds E2 HwfE2 Y (bind_sub W) HbE2). }
      assert (HXnotE2 : X `notin` dom E2).
      { apply (uniq_cons_2 binding X (bind_sub V) E2 HuF). }
      assert (Hfv : X `notin` fv_typ W).
      { apply (wf_typ_fv_notin E2 W X HWE2 HXnotE2). }
      exists W. split.
      * apply binds_app_r with (E := subst_env_te X U E1). exact HbE2.
      * symmetry. apply subst_tt_fresh. exact Hfv.
Qed.

Lemma subqual_te_subst_gen : forall E1 E2 X U V Q R,
  sub E2 U V ->
  subqual (E1 ++ (X, bind_sub V) :: E2) Q R ->
  subqual (subst_env_te X U E1 ++ E2) Q R.
Proof.
  intros E1 E2 X U V Q R Hs H.
  dependent induction H.
  - (* top *) apply subqual_top.
    + apply (wf_env_te_subst_gen E1 E2 X U V Hs H).
    + apply (wf_qua_te_subst_gen E1 E2 X U V Q H0).
  - (* bot *) apply subqual_bot.
    + apply (wf_env_te_subst_gen E1 E2 X U V Hs H).
    + apply (wf_qua_te_subst_gen E1 E2 X U V Q H0).
  - (* eval_elim *) eapply subqual_eval_elim.
    + apply (IHsubqual1 E1 E2 X V Hs eq_refl).
    + exact H0.
    + apply (IHsubqual2 E1 E2 X V Hs eq_refl).
  - (* eval_intro *) eapply subqual_eval_intro.
    + apply (IHsubqual1 E1 E2 X V Hs eq_refl).
    + exact H0.
    + apply (IHsubqual2 E1 E2 X V Hs eq_refl).
  - (* lift *) apply subqual_lift_elem.
    + apply (wf_env_te_subst_gen E1 E2 X U V Hs H).
    + exact H0.
  - (* refl_qvar *) apply subqual_refl_qvar.
    + apply (wf_env_te_subst_gen E1 E2 X U V Hs H).
    + apply (wf_qua_te_subst_gen E1 E2 X U V (qua_fvar X0) H0).
  - (* trans_qvar *) 
    destruct (binds_te_qua_payload E1 E2 X U V X0 R H) as [R' [HR' Heq]].
    subst R'.
    eapply subqual_trans_qvar.
    + exact HR'.
    + apply (IHsubqual E1 E2 X V Hs eq_refl).
  - (* join_inl *) apply subqual_join_inl.
    + apply (IHsubqual E1 E2 X V Hs eq_refl).
    + apply (wf_qua_te_subst_gen E1 E2 X U V R2 H0).
  - (* join_inr *) apply subqual_join_inr.
    + apply (wf_qua_te_subst_gen E1 E2 X U V R1 H).
    + apply (IHsubqual E1 E2 X V Hs eq_refl).
  - (* join_elim *) apply subqual_join_elim.
    + apply (IHsubqual1 E1 E2 X V Hs eq_refl).
    + apply (IHsubqual2 E1 E2 X V Hs eq_refl).
  - (* meet_eliml *) apply subqual_meet_eliml.
    + apply (IHsubqual E1 E2 X V Hs eq_refl).
    + apply (wf_qua_te_subst_gen E1 E2 X U V R2 H0).
  - (* meet_elimr *) apply subqual_meet_elimr.
    + apply (wf_qua_te_subst_gen E1 E2 X U V R1 H).
    + apply (IHsubqual E1 E2 X V Hs eq_refl).
  - (* meet_intro *) apply subqual_meet_intro.
    + apply (IHsubqual1 E1 E2 X V Hs eq_refl).
    + apply (IHsubqual2 E1 E2 X V Hs eq_refl).
Qed.

Definition TSsub (E : env) (S T : typ) (D : sub E S T) : Prop :=
  forall E1 E2 X U V,
    E = E1 ++ (X, bind_sub V) :: E2 ->
    sub E2 U V ->
    wf_env E ->
    sub (subst_env_te X U E1 ++ E2) (subst_tt X U S) (subst_tt X U T).

Definition TSqt (E : env) (S T : qtyp) (D : subqtype E S T) : Prop :=
  forall E1 E2 X U V,
    E = E1 ++ (X, bind_sub V) :: E2 ->
    sub E2 U V ->
    wf_env E ->
    subqtype (subst_env_te X U E1 ++ E2) (subst_tqt X U S) (subst_tqt X U T).

Lemma TSsub_proof : forall E S T (D : sub E S T), TSsub E S T D.
Proof.
  apply (sub_mut_ind TSsub TSqt).
  - (* top *) intros E S HwfE HwS E1 E2 X U V HE Hs HwfOld. subst E.
    apply sub_top.
    + apply (wf_env_te_subst_gen E1 E2 X U V Hs HwfE).
    + apply (proj1 wf_typ_te_subst_gen (E1 ++ (X, bind_sub V) :: E2) S HwS
               E1 E2 X U V eq_refl Hs).
  - (* refl *) intros E Y HwfE HwY E1 E2 X U V HE Hs HwfOld. subst E.
    destruct (X == Y) as [Heq|Hneq].
    + subst Y. rewrite subst_tt_fvar_eq.
      apply sub_refl.
      * apply (wf_env_te_subst_gen E1 E2 X U V Hs HwfE).
      * destruct (sub_wf E2 U V Hs) as [_ [HU0 _]].
        apply (wf_typ_incl E2 (subst_env_te X U E1 ++ E2) U).
        -- intros z b Hz. apply binds_app_r with (E := subst_env_te X U E1). exact Hz.
        -- exact HU0.
    + rewrite (subst_tt_fvar_neq X Y U Hneq).
      apply sub_refl_tvar.
      * apply (wf_env_te_subst_gen E1 E2 X U V Hs HwfE).
      * pose proof (proj1 wf_typ_te_subst_gen (E1 ++ (X, bind_sub V) :: E2)
                      (typ_fvar Y) HwY E1 E2 X U V eq_refl Hs) as HY.
        rewrite (subst_tt_fvar_neq X Y U Hneq) in HY. exact HY.
  - (* trans_tvar *) intros U0 E T Y b s IH E1 E2 X U V HE Hs HwfOld. subst E.
    destruct (binds_te_split E1 E2 X U V Y U0 HwfOld b)
      as [[HY HU0]|[Hneq [W' [HW' HWeq]]]].
    + subst Y. subst U0.
      pose proof (wf_env_suffix E1 ((X, bind_sub V) :: E2) HwfOld) as HwfSuffix.
      destruct (wf_env_sub_head X V E2 HwfSuffix) as [HwfE2 HV].
      assert (HXnotE2 : X `notin` dom E2).
      { pose proof (wf_env_uniq _ HwfOld) as Hu.
        pose proof (uniq_app_2 binding E1 ((X, bind_sub V) :: E2) Hu) as HuF.
        apply (uniq_cons_2 binding X (bind_sub V) E2 HuF). }
      assert (HfvV : X `notin` fv_typ V).
      { apply (wf_typ_fv_notin E2 V X HV HXnotE2). }
      assert (HsubstV : subst_tt X U V = V).
      { apply subst_tt_fresh. exact HfvV. }
      rewrite subst_tt_fvar_eq.
      pose proof (IH E1 E2 X U V eq_refl Hs HwfOld) as IHs.
      rewrite HsubstV in IHs.
      apply (sub_trans (subst_env_te X U E1 ++ E2) U V (subst_tt X U T)).
      * apply (sub_weaken E2 U V Hs (subst_env_te X U E1 ++ E2)).
        -- intros z bz Hz. apply binds_app_r with (E := subst_env_te X U E1). exact Hz.
        -- apply (wf_env_te_subst_gen E1 E2 X U V Hs HwfOld).
      * exact IHs.
    + rewrite (subst_tt_fvar_neq X Y U (fun Hc => Hneq (eq_sym Hc))).
      apply (sub_trans_tvar W' (subst_env_te X U E1 ++ E2) (subst_tt X U T) Y).
      * exact HW'.
      * rewrite HWeq. apply (IH E1 E2 X U V eq_refl Hs HwfOld).
  - (* arrow *) intros E S1 S2 T1 T2 s1 IH1 s2 IH2 E1 E2 X U V HE Hs HwfOld. subst E.
    assert (HwfE : wf_env (E1 ++ (X, bind_sub V) :: E2)) by (apply (sub_wf_env (E1 ++ (X, bind_sub V) :: E2) (typ_arrow S1 S2) (typ_arrow T1 T2) (sub_arrow (E1 ++ (X, bind_sub V) :: E2) S1 S2 T1 T2 s1 s2))).
    simpl. apply sub_arrow.
    + apply (IH1 E1 E2 X U V eq_refl Hs HwfE).
    + apply (IH2 E1 E2 X U V eq_refl Hs HwfE).
  - (* all *) intros L E S1 S2 T1 T2 s1 IH1 s2 IH2 E1 E2 X U V HE Hs HwfOld. subst E.
    assert (HwfE : wf_env (E1 ++ (X, bind_sub V) :: E2)) by (apply (sub_wf_env (E1 ++ (X, bind_sub V) :: E2) (typ_all S1 S2) (typ_all T1 T2) (sub_all L (E1 ++ (X, bind_sub V) :: E2) S1 S2 T1 T2 s1 s2))).
    destruct (sub_wf E2 U V Hs) as [_ [HU _]].
    pose proof (wf_typ_type E2 U HU) as HUt.
    simpl. apply (sub_all (add X L) (subst_env_te X U E1 ++ E2)).
    + apply (IH1 E1 E2 X U V eq_refl Hs HwfE).
    + intros Y HY.
      assert (HYL : Y `notin` L) by (simpl in HY; fsetdec).
      assert (HYX : Y <> X) by (intro Hc; subst Y; simpl in HY; fsetdec).
      assert (Hcomm : subst_tqt X U (open_tqt_rec 0 Y T2) =
                      open_tqt_rec 0 Y (subst_tqt X U T2)).
      { rewrite (subst_tqt_open_tqt_rec T2 0 X U Y HUt).
        rewrite (subst_tt_fvar_neq X Y U (fun Hc => HYX (eq_sym Hc))). reflexivity. }
      assert (HcommS : subst_tqt X U (open_tqt_rec 0 Y S2) =
                       open_tqt_rec 0 Y (subst_tqt X U S2)).
      { rewrite (subst_tqt_open_tqt_rec S2 0 X U Y HUt).
        rewrite (subst_tt_fvar_neq X Y U (fun Hc => HYX (eq_sym Hc))). reflexivity. }
      unfold open_tqt.
      rewrite <- HcommS. rewrite <- Hcomm.
      apply (IH2 Y HYL ((Y, bind_sub T1) :: E1) E2 X U V eq_refl Hs
                (subqtype_wf_env _ _ _ (s2 Y HYL))).
  - (* qall *) intros L E S1 S2 T1 T2 sq s2 IH2 E1 E2 X U V HE Hs HwfOld. subst E.
    assert (HwfE : wf_env (E1 ++ (X, bind_sub V) :: E2)) by (apply (sub_wf_env (E1 ++ (X, bind_sub V) :: E2) (typ_qall S1 S2) (typ_qall T1 T2) (sub_qall L (E1 ++ (X, bind_sub V) :: E2) S1 S2 T1 T2 sq s2))).
    destruct (sub_wf E2 U V Hs) as [_ [HU _]].
    pose proof (wf_typ_type E2 U HU) as HUt.
    simpl. apply (sub_qall (add X L) (subst_env_te X U E1 ++ E2) S1 (subst_tqt X U S2) T1 (subst_tqt X U T2)).
    + apply (subqual_te_subst_gen E1 E2 X U V T1 S1 Hs sq).
    + intros Y HY.
      assert (HYL : Y `notin` L) by (simpl in HY; fsetdec).
      assert (Hcomm : subst_tqt X U (open_qqt_rec 0 Y T2) =
                      open_qqt_rec 0 Y (subst_tqt X U T2)).
      { rewrite (subst_tqt_open_qqt_rec T2 0 X U (qua_fvar Y) HUt). reflexivity. }
      assert (HcommS : subst_tqt X U (open_qqt_rec 0 Y S2) =
                       open_qqt_rec 0 Y (subst_tqt X U S2)).
      { rewrite (subst_tqt_open_qqt_rec S2 0 X U (qua_fvar Y) HUt). reflexivity. }
      unfold open_qqt.
      rewrite <- HcommS. rewrite <- Hcomm.
      apply (IH2 Y HYL ((Y, bind_qua T1) :: E1) E2 X U V eq_refl Hs
                (subqtype_wf_env _ _ _ (s2 Y HYL))).
  - (* sum *) intros E S1 S2 T1 T2 s1 IH1 s2 IH2 E1 E2 X U V HE Hs HwfOld. subst E.
    assert (HwfE : wf_env (E1 ++ (X, bind_sub V) :: E2)) by (apply (sub_wf_env (E1 ++ (X, bind_sub V) :: E2) (typ_sum S1 S2) (typ_sum T1 T2) (sub_sum (E1 ++ (X, bind_sub V) :: E2) S1 S2 T1 T2 s1 s2))).
    simpl. apply sub_sum.
    + apply (IH1 E1 E2 X U V eq_refl Hs HwfE).
    + apply (IH2 E1 E2 X U V eq_refl Hs HwfE).
  - (* pair *) intros E S1 S2 T1 T2 s1 IH1 s2 IH2 E1 E2 X U V HE Hs HwfOld. subst E.
    assert (HwfE : wf_env (E1 ++ (X, bind_sub V) :: E2)) by (apply (sub_wf_env (E1 ++ (X, bind_sub V) :: E2) (typ_pair S1 S2) (typ_pair T1 T2) (sub_pair (E1 ++ (X, bind_sub V) :: E2) S1 S2 T1 T2 s1 s2))).
    simpl. apply sub_pair.
    + apply (IH1 E1 E2 X U V eq_refl Hs HwfE).
    + apply (IH2 E1 E2 X U V eq_refl Hs HwfE).
  - (* qtyp *) intros E Q1 T1 Q2 T2 sq s IH E1 E2 X U V HE Hs HwfOld. subst E.
    assert (HwfE : wf_env (E1 ++ (X, bind_sub V) :: E2)) by (apply (subqtype_wf_env (E1 ++ (X, bind_sub V) :: E2) (qtyp_qtyp Q1 T1) (qtyp_qtyp Q2 T2) (sub_qtyp_qtyp (E1 ++ (X, bind_sub V) :: E2) Q1 T1 Q2 T2 sq s))).
    simpl. apply sub_qtyp_qtyp.
    + apply (subqual_te_subst_gen E1 E2 X U V Q1 Q2 Hs sq).
    + apply (IH E1 E2 X U V eq_refl Hs HwfE).
Qed.

Lemma TSqt_proof : forall E S T (D : subqtype E S T), TSqt E S T D.
Proof.
  intros E S T D. destruct D as [E0 Q1 T1 Q2 T2 sq s]. simpl in *.
  unfold TSqt. intros E1 E2 X U V HE Hs Hwf. subst E0.
  apply sub_qtyp_qtyp.
  - apply (subqual_te_subst_gen E1 E2 X U V Q1 Q2 Hs sq).
  - apply (TSsub_proof (E1 ++ (X, bind_sub V) :: E2) T1 T2 s
                       E1 E2 X U V eq_refl Hs Hwf).
Qed.

Lemma sub_te_subst_gen : forall E1 E2 X U V S T,
  sub E2 U V ->
  sub (E1 ++ (X, bind_sub V) :: E2) S T ->
  sub (subst_env_te X U E1 ++ E2) (subst_tt X U S) (subst_tt X U T).
Proof.
  intros E1 E2 X U V S T Hs H.
  exact (TSsub_proof (E1 ++ (X, bind_sub V) :: E2) S T H
                     E1 E2 X U V eq_refl Hs
                     (sub_wf_env _ _ _ H)).
Qed.

Lemma subqtype_te_subst_gen : forall E1 E2 X U V S T,
  sub E2 U V ->
  subqtype (E1 ++ (X, bind_sub V) :: E2) S T ->
  subqtype (subst_env_te X U E1 ++ E2) (subst_tqt X U S) (subst_tqt X U T).
Proof.
  intros E1 E2 X U V S T Hs H.
  exact (TSqt_proof (E1 ++ (X, bind_sub V) :: E2) S T H
                    E1 E2 X U V eq_refl Hs
                    (subqtype_wf_env _ _ _ H)).
Qed.

Lemma sub_te_subst : forall E X U V S T,
  sub E U V ->
  sub (X ~ bind_sub V ++ E) S T ->
  sub E (subst_tt X U S) (subst_tt X U T).
Proof.
  intros E X U V S T Hs H.
  pose proof (sub_te_subst_gen (@nil (atom * binding)) E X U V S T Hs H) as Hres.
  simpl in Hres. exact Hres.
Qed.

Lemma subqtype_te_subst : forall E X U V S T,
  sub E U V ->
  subqtype (X ~ bind_sub V ++ E) S T ->
  subqtype E (subst_tqt X U S) (subst_tqt X U T).
Proof.
  intros E X U V S T Hs H.
  pose proof (subqtype_te_subst_gen (@nil (atom * binding)) E X U V S T Hs H) as Hres.
  simpl in Hres. exact Hres.
Qed.


(* ================================================================== *)
(* Type-variable substitution for typing                         *)
(* ================================================================== *)
Lemma binds_subst_env_te_typ_payload : forall E X U Y T,
  binds Y (bind_typ T) E ->
  exists T', binds Y (bind_typ T') (subst_env_te X U E) /\
              T' = subst_tqt X U T.
Proof.
  induction E as [|[y b] E IH]; intros X U Y T Hb; simpl in *.
  - inversion Hb.
  - apply binds_cons_iff in Hb. destruct Hb as [[HY Hb]|Hb].
    + subst y. destruct b as [Vb|Tb|Qb].
      * inversion Hb.
      * inversion Hb. subst Tb.
        exists (subst_tqt X U T). split.
        -- simpl. apply binds_cons_2; auto.
        -- reflexivity.
      * inversion Hb.
    + destruct (IH X U Y T Hb) as [T' [HT' Heq]].
      exists T'. split.
      * apply binds_cons. exact HT'.
      * exact Heq.
Qed.

Lemma binds_te_typ_split : forall E1 E2 X U V Y T,
  wf_env (E1 ++ (X, bind_sub V) :: E2) ->
  binds Y (bind_typ T) (E1 ++ (X, bind_sub V) :: E2) ->
  exists T', binds Y (bind_typ T') (subst_env_te X U E1 ++ E2) /\
              T' = subst_tqt X U T.
Proof.
  intros E1 E2 X U V Y T Hwf Hb.
  pose proof (wf_env_uniq _ Hwf) as Hu.
  pose proof (uniq_app_2 binding E1 ((X, bind_sub V) :: E2) Hu) as HuF.
  rewrite (binds_app_uniq_iff binding Y (bind_typ T) E1 ((X, bind_sub V) :: E2) Hu) in Hb.
  destruct Hb as [[HbE1 Hnotin] | [HbMid HnotinE1]].
  - destruct (binds_subst_env_te_typ_payload E1 X U Y T HbE1) as [T' [HT' Heq]].
    exists T'. split.
    + apply binds_app_l. exact HT'.
    + exact Heq.
  - rewrite (binds_cons_uniq_iff binding Y X (bind_typ T) (bind_sub V) E2 HuF) in HbMid.
    destruct HbMid as [[Heq [Hbad HnotinE2]] | [HbE2 Hneq]].
    + inversion Hbad.
    + assert (HwfE2 : wf_env E2).
      { apply (wf_env_head_inv X (bind_sub V) E2).
        apply (wf_env_suffix E1 ((X, bind_sub V) :: E2) Hwf). }
      assert (HOW : wf_qtyp E2 T).
      { change (wf_qtyp E2 T).
        apply (wf_env_binds E2 HwfE2 Y (bind_typ T) HbE2). }
      assert (HXnotE2 : X `notin` dom E2).
      { apply (uniq_cons_2 binding X (bind_sub V) E2 HuF). }
      assert (Hfv : X `notin` fv_qtyp T).
      { apply (wf_qtyp_fv_notin E2 T X HOW HXnotE2). }
      exists T. split.
      * apply binds_app_r with (E := subst_env_te X U E1). exact HbE2.
      * symmetry. apply subst_tqt_fresh. exact Hfv.
Qed.

Lemma typing_subst_te_gen : forall E1 E2 X U V e T,
  sub E2 U V ->
  typing (E1 ++ (X, bind_sub V) :: E2) e T ->
  typing (subst_env_te X U E1 ++ E2) (subst_te X U e) (subst_tqt X U T).
Proof.
  intros E1 E2 X U V e T Hs H.
  dependent induction H.
  - (* var *) destruct (binds_te_typ_split E1 E2 X U V x T H H0) as [T' [HT' Heq]].
    rewrite <- Heq. simpl.
    apply typing_var.
    + apply (wf_env_te_subst_gen E1 E2 X U V Hs H).
    + exact HT'.
  - (* abs *) simpl.
    destruct (sub_wf E2 U V Hs) as [_ [HU _]].
    pose proof (wf_typ_type E2 U HU) as HUt.
    eapply typing_abs with (V := subst_tqt X U V0) (T1 := subst_tqt X U T1)
                           (L := union L (add X (dom (subst_env_te X U E1 ++ E2)))).
    + apply (wf_qua_te_subst_gen E1 E2 X U V P H).
    + intros x Hx.
      assert (HxL : x `notin` L) by (simpl in Hx; fsetdec).
      assert (HxX : x <> X) by (intro Hc; subst x; simpl in Hx; fsetdec).
      assert (Hxf : X `notin` fv_exp (exp_fvar x)).
      { intro Hc. simpl in Hc. apply HxX. fsetdec. }
      replace (open_ee (subst_te X U e1) x)
        with (subst_te X U (open_ee e1 x))
        by (exact (subst_te_open_ee_rec e1 0 X U (exp_fvar x) HUt Hxf)).
      exact (H1 x HxL ((x, bind_typ V0) :: E1) E2 X V Hs eq_refl).
  - (* app *) simpl. eapply typing_app.
    + apply (IHtyping1 E1 E2 X V Hs eq_refl).
    + apply (IHtyping2 E1 E2 X V Hs eq_refl).
  - (* tabs *) simpl.
    destruct (sub_wf E2 U V Hs) as [_ [HU _]].
    pose proof (wf_typ_type E2 U HU) as HUt.
    eapply typing_tabs with (V := subst_tt X U V0) (T1 := subst_tqt X U T1)
                            (L := union L (add X (dom (subst_env_te X U E1 ++ E2)))).
    + apply (wf_qua_te_subst_gen E1 E2 X U V P H).
    + intros x Hx.
      assert (HxL : x `notin` L) by (simpl in Hx; fsetdec).
      assert (HxX : x <> X) by (intro Hc; subst x; simpl in Hx; fsetdec).
      replace (open_te (subst_te X U e1) x)
        with (subst_te X U (open_te e1 x))
        by (change (subst_te X U (open_te_rec 0 x e1) =
                    open_te_rec 0 x (subst_te X U e1));
            rewrite (subst_te_open_te_rec e1 0 X U x HUt);
            rewrite (subst_tt_fvar_neq X x U (fun Hc => HxX (eq_sym Hc))); reflexivity).
      assert (HcommT : subst_tqt X U (open_tqt_rec 0 x T1) =
                       open_tqt_rec 0 x (subst_tqt X U T1)).
      { rewrite (subst_tqt_open_tqt_rec T1 0 X U x HUt).
        rewrite (subst_tt_fvar_neq X x U (fun Hc => HxX (eq_sym Hc))). reflexivity. }
      unfold open_tqt. rewrite <- HcommT. simpl.
      exact (H1 x HxL ((x, bind_sub V0) :: E1) E2 X V Hs eq_refl).
  - (* tapp *) simpl.
    destruct (sub_wf E2 U V Hs) as [_ [HU _]].
    pose proof (wf_typ_type E2 U HU) as HUt.
    pose proof (IHtyping E1 E2 X V Hs eq_refl) as IHt.
    pose proof (sub_te_subst_gen E1 E2 X U V T T1 Hs H0) as Hsub'.
    unfold open_tqt. rewrite (subst_tqt_open_tqt_rec T2 0 X U T HUt).
    eapply typing_tapp.
    + exact IHt.
    + exact Hsub'.
  - (* qabs *) simpl.
    destruct (sub_wf E2 U V Hs) as [_ [HU _]].
    pose proof (wf_typ_type E2 U HU) as HUt.
    eapply typing_qabs with (Q := Q) (T1 := subst_tqt X U T1)
                             (L := union L (add X (dom (subst_env_te X U E1 ++ E2)))).
    + apply (wf_qua_te_subst_gen E1 E2 X U V P H).
    + intros x Hx.
      assert (HxL : x `notin` L) by (simpl in Hx; fsetdec).
      replace (open_qe (subst_te X U e1) x)
        with (subst_te X U (open_qe e1 x))
        by (exact (subst_te_open_qe_rec e1 0 X U x HUt)).
      assert (HcommT : subst_tqt X U (open_qqt_rec 0 x T1) =
                       open_qqt_rec 0 x (subst_tqt X U T1)).
      { rewrite (subst_tqt_open_qqt_rec T1 0 X U x HUt). reflexivity. }
      unfold open_qqt. rewrite <- HcommT. simpl.
      exact (H1 x HxL ((x, bind_qua Q) :: E1) E2 X V Hs eq_refl).
  - (* qapp *) simpl.
    destruct (sub_wf E2 U V Hs) as [_ [HU _]].
    pose proof (wf_typ_type E2 U HU) as HUt.
    unfold open_qqt. rewrite (subst_tqt_open_qqt_rec T 0 X U Q HUt).
    eapply typing_qapp.
    + apply (IHtyping E1 E2 X V Hs eq_refl).
    + apply (subqual_te_subst_gen E1 E2 X U V Q Q1 Hs H0).
  - (* sub *) simpl.
    eapply typing_sub.
    + apply (IHtyping E1 E2 X V Hs eq_refl).
    + apply (subqtype_te_subst_gen E1 E2 X U V S T Hs H0).
  - (* let *) simpl.
    destruct (sub_wf E2 U V Hs) as [_ [HU _]].
    pose proof (wf_typ_type E2 U HU) as HUt.
    eapply typing_let with (T1 := subst_tqt X U T1) (T2 := subst_tqt X U T2)
                            (L := union L (add X (dom (subst_env_te X U E1 ++ E2)))).
    + apply (IHtyping E1 E2 X V Hs eq_refl).
    + intros x Hx.
      assert (HxL : x `notin` L) by (simpl in Hx; fsetdec).
      assert (HxX : x <> X) by (intro Hc; subst x; simpl in Hx; fsetdec).
      assert (Hxf : X `notin` fv_exp (exp_fvar x)).
      { intro Hc. simpl in Hc. apply HxX. fsetdec. }
      replace (open_ee (subst_te X U e2) x)
        with (subst_te X U (open_ee e2 x))
        by (exact (subst_te_open_ee_rec e2 0 X U (exp_fvar x) HUt Hxf)).
      simpl. exact (H1 x HxL ((x, bind_typ T1) :: E1) E2 X V Hs eq_refl).
  - (* inl *) simpl. eapply typing_inl.
    + apply (wf_qua_te_subst_gen E1 E2 X U V P H).
    + apply (IHtyping E1 E2 X V Hs eq_refl).
    + apply (proj2 wf_typ_te_subst_gen (E1 ++ (X, bind_sub V) :: E2) T2 H1
                E1 E2 X U V eq_refl Hs).
  - (* inr *) simpl. eapply typing_inr.
    + apply (wf_qua_te_subst_gen E1 E2 X U V P H).
    + apply (IHtyping E1 E2 X V Hs eq_refl).
    + apply (proj2 wf_typ_te_subst_gen (E1 ++ (X, bind_sub V) :: E2) T1 H1
                E1 E2 X U V eq_refl Hs).
  - (* case *) simpl.
    destruct (sub_wf E2 U V Hs) as [_ [HU _]].
    pose proof (wf_typ_type E2 U HU) as HUt.
    eapply typing_case with (T1 := subst_tqt X U T1) (T2 := subst_tqt X U T2)
                             (T := subst_tqt X U T)
                             (Q := Q)
                             (L := union L (add X (dom (subst_env_te X U E1 ++ E2)))).
    + apply (IHtyping E1 E2 X V Hs eq_refl).
    + intros x Hx.
      assert (HxL : x `notin` L) by (simpl in Hx; fsetdec).
      assert (HxX : x <> X) by (intro Hc; subst x; simpl in Hx; fsetdec).
      assert (Hxf : X `notin` fv_exp (exp_fvar x)).
      { intro Hc. simpl in Hc. apply HxX. fsetdec. }
      replace (open_ee (subst_te X U e2) x)
        with (subst_te X U (open_ee e2 x))
        by (exact (subst_te_open_ee_rec e2 0 X U (exp_fvar x) HUt Hxf)).
      simpl. exact (H1 x HxL ((x, bind_typ T1) :: E1) E2 X V Hs eq_refl).
    + intros x Hx.
      assert (HxL : x `notin` L) by (simpl in Hx; fsetdec).
      assert (HxX : x <> X) by (intro Hc; subst x; simpl in Hx; fsetdec).
      assert (Hxf : X `notin` fv_exp (exp_fvar x)).
      { intro Hc. simpl in Hc. apply HxX. fsetdec. }
      replace (open_ee (subst_te X U e3) x)
        with (subst_te X U (open_ee e3 x))
        by (exact (subst_te_open_ee_rec e3 0 X U (exp_fvar x) HUt Hxf)).
      simpl. exact (H3 x HxL ((x, bind_typ T2) :: E1) E2 X V Hs eq_refl).
  - (* pair *) simpl. eapply typing_pair.
    + apply (wf_qua_te_subst_gen E1 E2 X U V P H).
    + apply (IHtyping1 E1 E2 X V Hs eq_refl).
    + apply (IHtyping2 E1 E2 X V Hs eq_refl).
  - (* first *) simpl. eapply typing_first.
    apply (IHtyping E1 E2 X V Hs eq_refl).
  - (* second *) simpl. eapply typing_second.
    apply (IHtyping E1 E2 X V Hs eq_refl).
  - (* upqual *) simpl. eapply typing_upqual.
    + apply (IHtyping E1 E2 X V Hs eq_refl).
    + apply (subqual_te_subst_gen E1 E2 X U V Q P Hs H0).
  - (* check *) simpl. eapply typing_check.
    + apply (IHtyping E1 E2 X V Hs eq_refl).
    + apply (subqual_te_subst_gen E1 E2 X U V Q P Hs H0).
Qed.

Lemma typing_subst_te : forall E X U V e T,
  sub E U V ->
  typing (X ~ bind_sub V ++ E) e T ->
  typing E (subst_te X U e) (subst_tqt X U T).
Proof.
  intros E X U V e T Hs H.
  pose proof (typing_subst_te_gen (@nil (atom * binding)) E X U V e T Hs H) as Hres.
  simpl in Hres. exact Hres.
Qed.


(* ================================================================== *)
(* Qualifier-variable substitution                                 *)
(* ================================================================== *)
Definition subst_binding_qe (X : atom) (R : qua) (b : binding) : binding :=
  match b with
  | bind_sub V => bind_sub (subst_qt X R V)
  | bind_typ T => bind_typ (subst_qqt X R T)
  | bind_qua Q => bind_qua (subst_qq X R Q)
  end.

Fixpoint subst_env_qe (X : atom) (R : qua) (E : env) {struct E} : env :=
  match E with
  | nil => nil
  | cons (y, b) E' => cons (y, subst_binding_qe X R b) (subst_env_qe X R E')
  end.

Lemma subst_env_qe_app : forall X R E1 E2,
  subst_env_qe X R (E1 ++ E2) = subst_env_qe X R E1 ++ subst_env_qe X R E2.
Proof.
  intros X R E1. induction E1 as [|[y b] E1 IH]; intros E2; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma dom_subst_env_qe : forall X R E, dom (subst_env_qe X R E) = dom E.
Proof.
  intros X R E. induction E as [|[y b] E IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma binds_subst_env_qe_qua_payload : forall E X R Y Q,
  binds Y (bind_qua Q) E ->
  exists Q', binds Y (bind_qua Q') (subst_env_qe X R E) /\
              Q' = subst_qq X R Q.
Proof.
  induction E as [|[y b] E IH]; intros X R Y Q Hb; simpl in *.
  - inversion Hb.
  - apply binds_cons_iff in Hb. destruct Hb as [[HY Hb]|Hb].
    + subst y. destruct b as [Vb|Tb|Qb].
      * inversion Hb.
      * inversion Hb.
      * inversion Hb. subst Qb.
        exists (subst_qq X R Q). split.
        -- simpl. apply binds_cons_2; auto.
        -- reflexivity.
    + destruct (IH X R Y Q Hb) as [Q' [HQ' Heq]].
      exists Q'. split.
      * apply binds_cons. exact HQ'.
      * exact Heq.
Qed.

Lemma binds_subst_env_qe_sub_payload : forall E X R Y U,
  binds Y (bind_sub U) E ->
  exists U', binds Y (bind_sub U') (subst_env_qe X R E) /\
              U' = subst_qt X R U.
Proof.
  induction E as [|[y b] E IH]; intros X R Y U Hb; simpl in *.
  - inversion Hb.
  - apply binds_cons_iff in Hb. destruct Hb as [[HY Hb]|Hb].
    + subst y. destruct b as [Vb|Tb|Qb].
      * inversion Hb. subst Vb.
        exists (subst_qt X R U). split.
        -- simpl. apply binds_cons_2; auto.
        -- reflexivity.
      * inversion Hb.
      * inversion Hb.
    + destruct (IH X R Y U Hb) as [U' [HU' Heq]].
      exists U'. split.
      * apply binds_cons. exact HU'.
      * exact Heq.
Qed.

Lemma binds_subst_env_qe_typ_payload : forall E X R Y T,
  binds Y (bind_typ T) E ->
  exists T', binds Y (bind_typ T') (subst_env_qe X R E) /\
              T' = subst_qqt X R T.
Proof.
  induction E as [|[y b] E IH]; intros X R Y T Hb; simpl in *.
  - inversion Hb.
  - apply binds_cons_iff in Hb. destruct Hb as [[HY Hb]|Hb].
    + subst y. destruct b as [Vb|Tb|Qb].
      * inversion Hb.
      * inversion Hb. subst Tb.
        exists (subst_qqt X R T). split.
        -- simpl. apply binds_cons_2; auto.
        -- reflexivity.
      * inversion Hb.
    + destruct (IH X R Y T Hb) as [T' [HT' Heq]].
      exists T'. split.
      * apply binds_cons. exact HT'.
      * exact Heq.
Qed.

Lemma binds_qe_qua_exists : forall E1 E2 X R Qm Y Q0,
  Y <> X ->
  binds Y (bind_qua Q0) (E1 ++ (X, bind_qua Qm) :: E2) ->
  exists Q', binds Y (bind_qua Q') (subst_env_qe X R E1 ++ E2).
Proof.
  induction E1 as [|[y b] E1 IH]; intros E2 X R Qm Y Q0 Hneq Hb; simpl in *.
  - apply binds_cons_iff in Hb. destruct Hb as [[HY Hb]|Hb].
    + subst Y. contradiction.
    + exists Q0. simpl. exact Hb.
  - apply binds_cons_iff in Hb. destruct Hb as [[HY Hb]|Hb].
    + subst y. destruct b as [Vb|Tb|Qb].
      * inversion Hb.
      * inversion Hb.
      * inversion Hb. subst Qb. exists (subst_qq X R Q0).
        simpl. apply binds_cons_2; auto.
    + destruct (IH E2 X R Qm Y Q0 Hneq Hb) as [Q' HQ'].
      exists Q'. apply binds_cons. exact HQ'.
Qed.

Lemma binds_qe_sub_exists : forall E1 E2 X R Qm Y U,
  Y <> X ->
  binds Y (bind_sub U) (E1 ++ (X, bind_qua Qm) :: E2) ->
  exists U', binds Y (bind_sub U') (subst_env_qe X R E1 ++ E2).
Proof.
  induction E1 as [|[y b] E1 IH]; intros E2 X R Qm Y U Hneq Hb; simpl in *.
  - apply binds_cons_iff in Hb. destruct Hb as [[HY Hb]|Hb].
    + subst Y. contradiction.
    + exists U. simpl. exact Hb.
  - apply binds_cons_iff in Hb. destruct Hb as [[HY Hb]|Hb].
    + subst y. destruct b as [Vb|Tb|Qb].
      * inversion Hb. subst Vb. exists (subst_qt X R U).
        simpl. apply binds_cons_2; auto.
      * inversion Hb.
      * inversion Hb.
    + destruct (IH E2 X R Qm Y U Hneq Hb) as [U' HU'].
      exists U'. apply binds_cons. exact HU'.
Qed.

Lemma binds_qe_typ_exists : forall E1 E2 X R Qm Y T,
  Y <> X ->
  binds Y (bind_typ T) (E1 ++ (X, bind_qua Qm) :: E2) ->
  exists T', binds Y (bind_typ T') (subst_env_qe X R E1 ++ E2).
Proof.
  induction E1 as [|[y b] E1 IH]; intros E2 X R Qm Y T Hneq Hb; simpl in *.
  - apply binds_cons_iff in Hb. destruct Hb as [[HY Hb]|Hb].
    + subst Y. contradiction.
    + exists T. simpl. exact Hb.
  - apply binds_cons_iff in Hb. destruct Hb as [[HY Hb]|Hb].
    + subst y. destruct b as [Vb|Tb|Qb].
      * inversion Hb.
      * inversion Hb. subst Tb. exists (subst_qqt X R T).
        simpl. apply binds_cons_2; auto.
      * inversion Hb.
    + destruct (IH E2 X R Qm Y T Hneq Hb) as [T' HT'].
      exists T'. apply binds_cons. exact HT'.
Qed.

Lemma wf_qua_qe_subst_gen : forall E1 E2 X R Qm Q,
  wf_env (E1 ++ (X, bind_qua Qm) :: E2) ->
  subqual E2 R Qm ->
  wf_qua (E1 ++ (X, bind_qua Qm) :: E2) Q ->
  wf_qua (subst_env_qe X R E1 ++ E2) (subst_qq X R Q).
Proof.
  intros E1 E2 X R Qm Q Hwf Hs H.
  dependent induction H.
  - apply wf_qua_base.
  - destruct (X == X0) as [Heq|Hneq].
    + subst X0. rewrite subst_qq_fvar_eq.
      destruct (subqual_wf E2 R Qm Hs) as [HR _].
      apply (wf_qua_incl E2 (subst_env_qe X R E1 ++ E2) R).
      * intros z b Hz. apply binds_app_r with (E := subst_env_qe X R E1). exact Hz.
      * exact HR.
    + rewrite (subst_qq_fvar_neq X X0 R (fun Hc => Hneq Hc)).
      destruct (binds_qe_qua_exists E1 E2 X R Qm X0 R0
                  (fun Hc => Hneq (eq_sym Hc)) H) as [Q' HQ'].
      eapply wf_qua_fvar. exact HQ'.
  - apply wf_qua_meet.
    + apply (IHwf_qua1 Qm X E2 Hs E1 Hwf eq_refl).
    + apply (IHwf_qua2 Qm X E2 Hs E1 Hwf eq_refl).
  - apply wf_qua_join.
    + apply (IHwf_qua1 Qm X E2 Hs E1 Hwf eq_refl).
    + apply (IHwf_qua2 Qm X E2 Hs E1 Hwf eq_refl).
Qed.

Lemma wf_typ_qe_subst_gen :
  (forall E T, wf_typ E T -> forall E1 E2 X R Qm,
     E = E1 ++ (X, bind_qua Qm) :: E2 ->
     wf_env E -> subqual E2 R Qm ->
     wf_typ (subst_env_qe X R E1 ++ E2) (subst_qt X R T)) /\
  (forall E T, wf_qtyp E T -> forall E1 E2 X R Qm,
     E = E1 ++ (X, bind_qua Qm) :: E2 ->
     wf_env E -> subqual E2 R Qm ->
     wf_qtyp (subst_env_qe X R E1 ++ E2) (subst_qqt X R T)).
Proof.
  split.
  - apply (wf_mut_ind
      (fun E T D => forall E1 E2 X R Qm,
         E = E1 ++ (X, bind_qua Qm) :: E2 -> wf_env E -> subqual E2 R Qm ->
         wf_typ (subst_env_qe X R E1 ++ E2) (subst_qt X R T))
      (fun E T D => forall E1 E2 X R Qm,
         E = E1 ++ (X, bind_qua Qm) :: E2 -> wf_env E -> subqual E2 R Qm ->
         wf_qtyp (subst_env_qe X R E1 ++ E2) (subst_qqt X R T))).
    + intros E E1 E2 X R Qm HE Hwf Hs. subst E. apply wf_typ_top.
    + intros U E Y Hb E1 E2 X R Qm HE Hwf Hs. subst E.
      simpl. destruct (X == Y) as [Heq|Hneq].
      * subst Y. exfalso.
        pose proof (wf_env_uniq _ Hwf) as Hu.
        assert (HbMid : binds X (bind_qua Qm) (E1 ++ (X, bind_qua Qm) :: E2)).
        { apply binds_app_r with (E := E1). simpl. apply binds_cons_2; auto. }
        pose proof (binds_unique binding X (bind_sub U) (bind_qua Qm)
                    (E1 ++ (X, bind_qua Qm) :: E2) Hb HbMid Hu) as Hbad.
        inversion Hbad.
      * destruct (binds_qe_sub_exists E1 E2 X R Qm Y U
                    (fun Hc => Hneq (eq_sym Hc)) Hb) as [U' HU'].
        eapply wf_typ_var. exact HU'.
    + intros E T1 T2 H1 IH1 H2 IH2 E1 E2 X R Qm HE Hwf Hs. subst E.
      simpl. apply wf_typ_arrow.
      * apply (IH1 E1 E2 X R Qm eq_refl Hwf Hs).
      * apply (IH2 E1 E2 X R Qm eq_refl Hwf Hs).
    + intros L E T1 T2 H1 IH1 H2 IH2 E1 E2 X R Qm HE Hwf Hs. subst E.
      destruct (subqual_wf E2 R Qm Hs) as [HRq _].
      pose proof (wf_qua_qual E2 R HRq) as HqualR.
      simpl.
      apply (wf_typ_all (union (add X L) (dom (E1 ++ (X, bind_qua Qm) :: E2)))
             (subst_env_qe X R E1 ++ E2) (subst_qt X R T1) (subst_qqt X R T2)).
      * apply (IH1 E1 E2 X R Qm eq_refl Hwf Hs).
      * intros Y HY.
        assert (HYL : Y `notin` L) by (simpl in HY; fsetdec).
        assert (HYX : Y <> X) by (intro Hc; subst Y; simpl in HY; fsetdec).
        assert (HYdom : Y `notin` dom (E1 ++ (X, bind_qua Qm) :: E2)) by (simpl in HY; fsetdec).
        assert (HwfBody : wf_env (Y ~ bind_sub T1 ++ E1 ++ (X, bind_qua Qm) :: E2)).
        { apply wf_env_sub with (X := Y).
          - exact Hwf.
          - exact H1.
          - exact HYdom. }
        assert (Hcond : X `notin` fv_typ Y).
        { intro Hc. simpl in Hc. apply HYX. fsetdec. }
        assert (Hcomm : subst_qqt X R (open_tqt_rec 0 Y T2) =
                        open_tqt_rec 0 Y (subst_qqt X R T2)).
        { rewrite (subst_qqt_open_tqt_rec T2 0 X R Y HqualR Hcond). reflexivity. }
        unfold open_tqt. rewrite <- Hcomm. simpl.
        apply (IH2 Y HYL ((Y, bind_sub T1) :: E1) E2 X R Qm eq_refl HwfBody Hs).
    + intros L E T1 T2 H1 H2 IH2 E1 E2 X R Qm HE Hwf Hs. subst E.
      destruct (subqual_wf E2 R Qm Hs) as [HRq _].
      pose proof (wf_qua_qual E2 R HRq) as HqualR.
      simpl.
      apply (wf_typ_qall (union (add X L) (dom (E1 ++ (X, bind_qua Qm) :: E2)))
             (subst_env_qe X R E1 ++ E2) (subst_qq X R T1) (subst_qqt X R T2)).
      * apply (wf_qua_qe_subst_gen E1 E2 X R Qm T1 Hwf Hs H1).
      * intros Y HY.
        assert (HYL : Y `notin` L) by (simpl in HY; fsetdec).
        assert (HYX : Y <> X) by (intro Hc; subst Y; simpl in HY; fsetdec).
        assert (HYdom : Y `notin` dom (E1 ++ (X, bind_qua Qm) :: E2)) by (simpl in HY; fsetdec).
        assert (HwfBody : wf_env (Y ~ bind_qua T1 ++ E1 ++ (X, bind_qua Qm) :: E2)).
        { apply wf_env_qua with (X := Y).
          - exact Hwf.
          - exact H1.
          - exact HYdom. }
        assert (Hcomm : subst_qqt X R (open_qqt_rec 0 (qua_fvar Y) T2) =
                        open_qqt_rec 0 (qua_fvar Y) (subst_qqt X R T2)).
        { rewrite (subst_qqt_open_qqt_rec T2 0 X R (qua_fvar Y) HqualR).
          rewrite (subst_qq_fvar_neq X Y R (fun Hc => HYX (eq_sym Hc))). reflexivity. }
        unfold open_qqt. rewrite <- Hcomm. simpl.
        apply (IH2 Y HYL ((Y, bind_qua T1) :: E1) E2 X R Qm eq_refl HwfBody Hs).
    + intros E T1 T2 H1 IH1 H2 IH2 E1 E2 X R Qm HE Hwf Hs. subst E.
      simpl. apply wf_typ_sum;
        [apply (IH1 E1 E2 X R Qm eq_refl Hwf Hs)|apply (IH2 E1 E2 X R Qm eq_refl Hwf Hs)].
    + intros E T1 T2 H1 IH1 H2 IH2 E1 E2 X R Qm HE Hwf Hs. subst E.
      simpl. apply wf_typ_pair;
        [apply (IH1 E1 E2 X R Qm eq_refl Hwf Hs)|apply (IH2 E1 E2 X R Qm eq_refl Hwf Hs)].
    + intros E Q T Hq Ht IH E1 E2 X R Qm HE Hwf Hs. subst E.
      simpl. apply wf_qtyp_qtyp.
      * apply (wf_qua_qe_subst_gen E1 E2 X R Qm Q Hwf Hs Hq).
      * apply (IH E1 E2 X R Qm eq_refl Hwf Hs).
  - apply (wfq_mut_ind
      (fun E T D => forall E1 E2 X R Qm,
         E = E1 ++ (X, bind_qua Qm) :: E2 -> wf_env E -> subqual E2 R Qm ->
         wf_typ (subst_env_qe X R E1 ++ E2) (subst_qt X R T))
      (fun E T D => forall E1 E2 X R Qm,
         E = E1 ++ (X, bind_qua Qm) :: E2 -> wf_env E -> subqual E2 R Qm ->
         wf_qtyp (subst_env_qe X R E1 ++ E2) (subst_qqt X R T))).
    + intros E E1 E2 X R Qm HE Hwf Hs. subst E. apply wf_typ_top.
    + intros U E Y Hb E1 E2 X R Qm HE Hwf Hs. subst E.
      simpl. destruct (X == Y) as [Heq|Hneq].
      * subst Y. exfalso.
        pose proof (wf_env_uniq _ Hwf) as Hu.
        assert (HbMid : binds X (bind_qua Qm) (E1 ++ (X, bind_qua Qm) :: E2)).
        { apply binds_app_r with (E := E1). simpl. apply binds_cons_2; auto. }
        pose proof (binds_unique binding X (bind_sub U) (bind_qua Qm)
                    (E1 ++ (X, bind_qua Qm) :: E2) Hb HbMid Hu) as Hbad.
        inversion Hbad.
      * destruct (binds_qe_sub_exists E1 E2 X R Qm Y U
                    (fun Hc => Hneq (eq_sym Hc)) Hb) as [U' HU'].
        eapply wf_typ_var. exact HU'.
    + intros E T1 T2 H1 IH1 H2 IH2 E1 E2 X R Qm HE Hwf Hs. subst E.
      simpl. apply wf_typ_arrow;
        [apply (IH1 E1 E2 X R Qm eq_refl Hwf Hs)|apply (IH2 E1 E2 X R Qm eq_refl Hwf Hs)].
    + intros L E T1 T2 H1 IH1 H2 IH2 E1 E2 X R Qm HE Hwf Hs. subst E.
      destruct (subqual_wf E2 R Qm Hs) as [HRq _].
      pose proof (wf_qua_qual E2 R HRq) as HqualR.
      simpl. apply (wf_typ_all (union (add X L) (dom (E1 ++ (X, bind_qua Qm) :: E2)))
             (subst_env_qe X R E1 ++ E2) (subst_qt X R T1) (subst_qqt X R T2)).
      * apply (IH1 E1 E2 X R Qm eq_refl Hwf Hs).
      * intros Y HY.
        assert (HYL : Y `notin` L) by (simpl in HY; fsetdec).
        assert (HYX : Y <> X) by (intro Hc; subst Y; simpl in HY; fsetdec).
        assert (HYdom : Y `notin` dom (E1 ++ (X, bind_qua Qm) :: E2)) by (simpl in HY; fsetdec).
        assert (HwfBody : wf_env (Y ~ bind_sub T1 ++ E1 ++ (X, bind_qua Qm) :: E2)).
        { apply wf_env_sub with (X := Y); [exact Hwf|exact H1|exact HYdom]. }
        assert (Hcond : X `notin` fv_typ Y).
        { intro Hc. simpl in Hc. apply HYX. fsetdec. }
        assert (Hcomm : subst_qqt X R (open_tqt_rec 0 Y T2) =
                        open_tqt_rec 0 Y (subst_qqt X R T2)).
        { rewrite (subst_qqt_open_tqt_rec T2 0 X R Y HqualR Hcond). reflexivity. }
        unfold open_tqt. rewrite <- Hcomm. simpl.
        apply (IH2 Y HYL ((Y, bind_sub T1) :: E1) E2 X R Qm eq_refl HwfBody Hs).
    + intros L E T1 T2 H1 H2 IH2 E1 E2 X R Qm HE Hwf Hs. subst E.
      destruct (subqual_wf E2 R Qm Hs) as [HRq _].
      pose proof (wf_qua_qual E2 R HRq) as HqualR.
      simpl. apply (wf_typ_qall (union (add X L) (dom (E1 ++ (X, bind_qua Qm) :: E2)))
             (subst_env_qe X R E1 ++ E2) (subst_qq X R T1) (subst_qqt X R T2)).
      * apply (wf_qua_qe_subst_gen E1 E2 X R Qm T1 Hwf Hs H1).
      * intros Y HY.
        assert (HYL : Y `notin` L) by (simpl in HY; fsetdec).
        assert (HYX : Y <> X) by (intro Hc; subst Y; simpl in HY; fsetdec).
        assert (HYdom : Y `notin` dom (E1 ++ (X, bind_qua Qm) :: E2)) by (simpl in HY; fsetdec).
        assert (HwfBody : wf_env (Y ~ bind_qua T1 ++ E1 ++ (X, bind_qua Qm) :: E2)).
        { apply wf_env_qua with (X := Y); [exact Hwf|exact H1|exact HYdom]. }
        assert (Hcomm : subst_qqt X R (open_qqt_rec 0 (qua_fvar Y) T2) =
                        open_qqt_rec 0 (qua_fvar Y) (subst_qqt X R T2)).
        { rewrite (subst_qqt_open_qqt_rec T2 0 X R (qua_fvar Y) HqualR).
          rewrite (subst_qq_fvar_neq X Y R (fun Hc => HYX (eq_sym Hc))). reflexivity. }
        unfold open_qqt. rewrite <- Hcomm. simpl.
        apply (IH2 Y HYL ((Y, bind_qua T1) :: E1) E2 X R Qm eq_refl HwfBody Hs).
    + intros E T1 T2 H1 IH1 H2 IH2 E1 E2 X R Qm HE Hwf Hs. subst E.
      simpl. apply wf_typ_sum;
        [apply (IH1 E1 E2 X R Qm eq_refl Hwf Hs)|apply (IH2 E1 E2 X R Qm eq_refl Hwf Hs)].
    + intros E T1 T2 H1 IH1 H2 IH2 E1 E2 X R Qm HE Hwf Hs. subst E.
      simpl. apply wf_typ_pair;
        [apply (IH1 E1 E2 X R Qm eq_refl Hwf Hs)|apply (IH2 E1 E2 X R Qm eq_refl Hwf Hs)].
    + intros E Q T Hq Ht IH E1 E2 X R Qm HE Hwf Hs. subst E.
      simpl. apply wf_qtyp_qtyp.
      * apply (wf_qua_qe_subst_gen E1 E2 X R Qm Q Hwf Hs Hq).
      * apply (IH E1 E2 X R Qm eq_refl Hwf Hs).
Qed.

Lemma notin_dom_subst_env_qe : forall E1 E2 X R Qm y,
  y `notin` dom (E1 ++ (X, bind_qua Qm) :: E2) ->
  y `notin` dom (subst_env_qe X R E1 ++ E2).
Proof.
  intros E1 E2 X R Qm y H.
  assert (Hd : dom (subst_env_qe X R E1 ++ E2) [=] union (dom E1) (dom E2)).
  { rewrite dom_app. rewrite dom_subst_env_qe. reflexivity. }
  assert (Hd2 : dom (E1 ++ (X, bind_qua Qm) :: E2) [=]
                union (dom E1) (union (singleton X) (dom E2))).
  { rewrite dom_app. rewrite dom_cons. reflexivity. }
  setoid_rewrite Hd.
  setoid_rewrite Hd2 in H.
  fsetdec.
Qed.

Lemma wf_env_qe_subst_gen : forall E1 E2 X R Qm,
  wf_env (E1 ++ (X, bind_qua Qm) :: E2) ->
  subqual E2 R Qm ->
  wf_env (subst_env_qe X R E1 ++ E2).
Proof.
  induction E1 as [|[y b] E1 IH]; intros E2 X R Qm Hwf Hs; simpl in *.
  - inversion Hwf; subst. assumption.
  - destruct b as [T|T|Q].
    + inversion Hwf; subst.
      apply wf_env_sub with (X := y).
      * apply (IH E2 X R Qm H2 Hs).
      * apply (proj1 wf_typ_qe_subst_gen (E1 ++ (X, bind_qua Qm) :: E2) T H3
                E1 E2 X R Qm eq_refl H2 Hs).
      * apply (notin_dom_subst_env_qe E1 E2 X R Qm y H4).
    + inversion Hwf; subst.
      apply wf_env_typ with (x := y).
      * apply (IH E2 X R Qm H2 Hs).
      * apply (proj2 wf_typ_qe_subst_gen (E1 ++ (X, bind_qua Qm) :: E2) T H3
                E1 E2 X R Qm eq_refl H2 Hs).
      * apply (notin_dom_subst_env_qe E1 E2 X R Qm y H4).
    + inversion Hwf; subst.
      apply wf_env_qua with (X := y).
      * apply (IH E2 X R Qm H2 Hs).
      * apply (wf_qua_qe_subst_gen E1 E2 X R Qm Q H2 Hs H3).
      * apply (notin_dom_subst_env_qe E1 E2 X R Qm y H4).
Qed.

Lemma binds_qe_qua_split : forall E1 E2 X R Qm Y Q0,
  wf_env (E1 ++ (X, bind_qua Qm) :: E2) ->
  binds Y (bind_qua Q0) (E1 ++ (X, bind_qua Qm) :: E2) ->
  (Y = X /\ Q0 = Qm) \/
  (Y <> X /\ exists Q', binds Y (bind_qua Q') (subst_env_qe X R E1 ++ E2) /\
                         Q' = subst_qq X R Q0).
Proof.
  intros E1 E2 X R Qm Y Q0 Hwf Hb.
  pose proof (wf_env_uniq _ Hwf) as Hu.
  pose proof (uniq_app_2 binding E1 ((X, bind_qua Qm) :: E2) Hu) as HuF.
  rewrite (binds_app_uniq_iff binding Y (bind_qua Q0) E1 ((X, bind_qua Qm) :: E2) Hu) in Hb.
  destruct Hb as [[HbE1 Hnotin] | [HbMid HnotinE1]].
  - right. assert (HYX : Y <> X).
    { intro Heq. subst Y. apply Hnotin. simpl. fsetdec. }
    split; [exact HYX|].
    destruct (binds_subst_env_qe_qua_payload E1 X R Y Q0 HbE1) as [Q' [HQ' Heq]].
    exists Q'. split; [apply binds_app_l; exact HQ'|exact Heq].
  - rewrite (binds_cons_uniq_iff binding Y X (bind_qua Q0) (bind_qua Qm) E2 HuF) in HbMid.
    destruct HbMid as [[Heq [HQQ HnotinE2]] | [HbE2 Hneq]].
    + left. split; [exact Heq|]. inversion HQQ. reflexivity.
    + right. split; [exact Hneq|].
      assert (HwfE2 : wf_env E2).
      { apply (wf_env_head_inv X (bind_qua Qm) E2).
        apply (wf_env_suffix E1 ((X, bind_qua Qm) :: E2) Hwf). }
      assert (HWQ : wf_qua E2 Q0).
      { change (wf_qua E2 Q0).
        apply (wf_env_binds E2 HwfE2 Y (bind_qua Q0) HbE2). }
      assert (HXnotE2 : X `notin` dom E2).
      { apply (uniq_cons_2 binding X (bind_qua Qm) E2 HuF). }
      assert (Hfv : X `notin` fv_qua Q0).
      { apply (wf_qua_fv_notin E2 Q0 X HWQ HXnotE2). }
      exists Q0. split.
      * apply binds_app_r with (E := subst_env_qe X R E1). exact HbE2.
      * symmetry. apply subst_qq_fresh. exact Hfv.
Qed.

Lemma binds_qe_sub_split : forall E1 E2 X R Qm Y U,
  wf_env (E1 ++ (X, bind_qua Qm) :: E2) ->
  binds Y (bind_sub U) (E1 ++ (X, bind_qua Qm) :: E2) ->
  Y <> X /\ exists U', binds Y (bind_sub U') (subst_env_qe X R E1 ++ E2) /\
                        U' = subst_qt X R U.
Proof.
  intros E1 E2 X R Qm Y U Hwf Hb.
  pose proof (wf_env_uniq _ Hwf) as Hu.
  pose proof (uniq_app_2 binding E1 ((X, bind_qua Qm) :: E2) Hu) as HuF.
  rewrite (binds_app_uniq_iff binding Y (bind_sub U) E1 ((X, bind_qua Qm) :: E2) Hu) in Hb.
  destruct Hb as [[HbE1 Hnotin] | [HbMid HnotinE1]].
  - assert (HYX : Y <> X).
    { intro Heq. subst Y. apply Hnotin. simpl. fsetdec. }
    split; [exact HYX|].
    destruct (binds_subst_env_qe_sub_payload E1 X R Y U HbE1) as [U' [HU' Heq]].
    exists U'. split; [apply binds_app_l; exact HU'|exact Heq].
  - rewrite (binds_cons_uniq_iff binding Y X (bind_sub U) (bind_qua Qm) E2 HuF) in HbMid.
    destruct HbMid as [[Heq [Hbad HnotinE2]] | [HbE2 Hneq]].
    + inversion Hbad.
    + split; [exact Hneq|].
      assert (HwfE2 : wf_env E2).
      { apply (wf_env_head_inv X (bind_qua Qm) E2).
        apply (wf_env_suffix E1 ((X, bind_qua Qm) :: E2) Hwf). }
      assert (HWU : wf_typ E2 U).
      { change (wf_typ E2 U).
        apply (wf_env_binds E2 HwfE2 Y (bind_sub U) HbE2). }
      assert (HXnotE2 : X `notin` dom E2).
      { apply (uniq_cons_2 binding X (bind_qua Qm) E2 HuF). }
      assert (Hfv : X `notin` fv_typ U).
      { apply (wf_typ_fv_notin E2 U X HWU HXnotE2). }
      exists U. split.
      * apply binds_app_r with (E := subst_env_qe X R E1). exact HbE2.
      * symmetry. apply subst_qt_fresh. exact Hfv.
Qed.

Lemma binds_qe_typ_split : forall E1 E2 X R Qm Y T,
  wf_env (E1 ++ (X, bind_qua Qm) :: E2) ->
  binds Y (bind_typ T) (E1 ++ (X, bind_qua Qm) :: E2) ->
  Y <> X /\ exists T', binds Y (bind_typ T') (subst_env_qe X R E1 ++ E2) /\
                        T' = subst_qqt X R T.
Proof.
  intros E1 E2 X R Qm Y T Hwf Hb.
  pose proof (wf_env_uniq _ Hwf) as Hu.
  pose proof (uniq_app_2 binding E1 ((X, bind_qua Qm) :: E2) Hu) as HuF.
  rewrite (binds_app_uniq_iff binding Y (bind_typ T) E1 ((X, bind_qua Qm) :: E2) Hu) in Hb.
  destruct Hb as [[HbE1 Hnotin] | [HbMid HnotinE1]].
  - assert (HYX : Y <> X).
    { intro Heq. subst Y. apply Hnotin. simpl. fsetdec. }
    split; [exact HYX|].
    destruct (binds_subst_env_qe_typ_payload E1 X R Y T HbE1) as [T' [HT' Heq]].
    exists T'. split; [apply binds_app_l; exact HT'|exact Heq].
  - rewrite (binds_cons_uniq_iff binding Y X (bind_typ T) (bind_qua Qm) E2 HuF) in HbMid.
    destruct HbMid as [[Heq [Hbad HnotinE2]] | [HbE2 Hneq]].
    + inversion Hbad.
    + split; [exact Hneq|].
      assert (HwfE2 : wf_env E2).
      { apply (wf_env_head_inv X (bind_qua Qm) E2).
        apply (wf_env_suffix E1 ((X, bind_qua Qm) :: E2) Hwf). }
      assert (HWT : wf_qtyp E2 T).
      { change (wf_qtyp E2 T).
        apply (wf_env_binds E2 HwfE2 Y (bind_typ T) HbE2). }
      assert (HXnotE2 : X `notin` dom E2).
      { apply (uniq_cons_2 binding X (bind_qua Qm) E2 HuF). }
      assert (Hfv : X `notin` fv_qtyp T).
      { apply (wf_qtyp_fv_notin E2 T X HWT HXnotE2). }
      exists T. split.
      * apply binds_app_r with (E := subst_env_qe X R E1). exact HbE2.
      * symmetry. apply subst_qqt_fresh. exact Hfv.
Qed.

Lemma subst_qq_concretize_some : forall Q X R b,
  concretize Q = Some b -> subst_qq X R Q = Q.
Proof.
  induction Q; intros X R b0 Hc; simpl in *.
  - reflexivity.
  - discriminate.
  - discriminate.
  - destruct (concretize Q1) as [b1|] eqn:E1; [|discriminate].
    destruct (concretize Q2) as [b2|] eqn:E2; [|discriminate].
    injection Hc as Hb. subst b0.
    rewrite (IHQ1 X R b1 eq_refl), (IHQ2 X R b2 eq_refl). reflexivity.
  - destruct (concretize Q1) as [b1|] eqn:E1; [|discriminate].
    destruct (concretize Q2) as [b2|] eqn:E2; [|discriminate].
    injection Hc as Hb. subst b0.
    rewrite (IHQ1 X R b1 eq_refl), (IHQ2 X R b2 eq_refl). reflexivity.
Qed.

Lemma subqual_qe_subst_gen : forall E1 E2 X R Qm Q Q',
  wf_env (E1 ++ (X, bind_qua Qm) :: E2) ->
  subqual E2 R Qm ->
  subqual (E1 ++ (X, bind_qua Qm) :: E2) Q Q' ->
  subqual (subst_env_qe X R E1 ++ E2) (subst_qq X R Q) (subst_qq X R Q').
Proof.
  intros E1 E2 X R Qm Q Q' Hwf Hs H.
  dependent induction H.
  - (* top *) simpl. apply subqual_top.
    + apply (wf_env_qe_subst_gen E1 E2 X R Qm Hwf Hs).
    + apply (wf_qua_qe_subst_gen E1 E2 X R Qm Q Hwf Hs H0).
  - (* bot *) simpl. apply subqual_bot.
    + apply (wf_env_qe_subst_gen E1 E2 X R Qm Hwf Hs).
    + apply (wf_qua_qe_subst_gen E1 E2 X R Qm Q Hwf Hs H0).
  - (* eval_elim *) eapply subqual_eval_elim.
    + apply (IHsubqual1 Qm X E2 Hs E1 Hwf eq_refl).
    + rewrite (subst_qq_concretize_some Q' X R b H0). exact H0.
    + apply (IHsubqual2 Qm X E2 Hs E1 Hwf eq_refl).
  - (* eval_intro *) eapply subqual_eval_intro.
    + apply (IHsubqual1 Qm X E2 Hs E1 Hwf eq_refl).
    + rewrite (subst_qq_concretize_some Q' X R b H0). exact H0.
    + apply (IHsubqual2 Qm X E2 Hs E1 Hwf eq_refl).
  - (* lift *) simpl. apply subqual_lift_elem.
    + apply (wf_env_qe_subst_gen E1 E2 X R Qm Hwf Hs).
    + exact H0.
  - (* refl_qvar *) destruct (X == X0) as [Heq|Hneq].
    + subst X0. rewrite subst_qq_fvar_eq.
      apply subqual_refl.
      * apply (wf_env_qe_subst_gen E1 E2 X R Qm Hwf Hs).
      * destruct (subqual_wf E2 R Qm Hs) as [HR _].
        apply (wf_qua_incl E2 (subst_env_qe X R E1 ++ E2) R).
        -- intros z b Hz. apply binds_app_r with (E := subst_env_qe X R E1). exact Hz.
        -- exact HR.
    + rewrite (subst_qq_fvar_neq X X0 R (fun Hc => Hneq Hc)).
      apply subqual_refl_qvar.
      * apply (wf_env_qe_subst_gen E1 E2 X R Qm Hwf Hs).
      * pose proof (wf_qua_qe_subst_gen E1 E2 X R Qm (qua_fvar X0) Hwf Hs H0) as HQ.
        rewrite (subst_qq_fvar_neq X X0 R (fun Hc => Hneq Hc)) in HQ.
        exact HQ.
  - (* trans_qvar *) destruct (binds_qe_qua_split E1 E2 X R Qm X0 R0 Hwf H)
      as [[HY HQ]| [Hneq [Q'' [HQ'' Heq]]]].
    + subst X0. subst R0. rewrite subst_qq_fvar_eq.
      assert (HwE : wf_env (subst_env_qe X R E1 ++ E2))
        by (apply (wf_env_qe_subst_gen E1 E2 X R Qm Hwf Hs)).
      assert (HsubR : subqual (subst_env_qe X R E1 ++ E2) R Qm).
      { apply (subqual_env_incl E2 R Qm Hs (subst_env_qe X R E1 ++ E2)).
        - intros z b Hz. apply binds_app_r with (E := subst_env_qe X R E1). exact Hz.
        - exact HwE. }
      eapply subqual_trans.
      * exact HsubR.
      * pose proof (IHsubqual Qm X E2 Hs E1 Hwf eq_refl) as IHx.
        assert (HwfE2 : wf_env E2).
        { apply (wf_env_head_inv X (bind_qua Qm) E2).
          apply (wf_env_suffix E1 ((X, bind_qua Qm) :: E2) Hwf). }
        assert (HwfQm : wf_qua E2 Qm).
        { exact (proj2 (subqual_wf E2 R Qm Hs)). }
        assert (HXnotE2 : X `notin` dom E2).
        { pose proof (wf_env_uniq _ Hwf) as Hu.
          pose proof (uniq_app_2 binding E1 ((X, bind_qua Qm) :: E2) Hu) as HuF.
          apply (uniq_cons_2 binding X (bind_qua Qm) E2 HuF). }
        assert (Hfv : X `notin` fv_qua Qm).
        { apply (wf_qua_fv_notin E2 Qm X HwfQm HXnotE2). }
        rewrite (subst_qq_fresh X R Qm Hfv) in IHx. exact IHx.
    + rewrite (subst_qq_fvar_neq X X0 R (fun Hc => Hneq (eq_sym Hc))).
      eapply subqual_trans_qvar.
      * exact HQ''.
      * rewrite Heq. apply (IHsubqual Qm X E2 Hs E1 Hwf eq_refl).
  - (* join_inl *) simpl. apply subqual_join_inl.
    + apply (IHsubqual Qm X E2 Hs E1 Hwf eq_refl).
    + apply (wf_qua_qe_subst_gen E1 E2 X R Qm R2 Hwf Hs H0).
  - (* join_inr *) simpl. apply subqual_join_inr.
    + apply (wf_qua_qe_subst_gen E1 E2 X R Qm R1 Hwf Hs H).
    + apply (IHsubqual Qm X E2 Hs E1 Hwf eq_refl).
  - (* join_elim *) simpl. apply subqual_join_elim.
    + apply (IHsubqual1 Qm X E2 Hs E1 Hwf eq_refl).
    + apply (IHsubqual2 Qm X E2 Hs E1 Hwf eq_refl).
  - (* meet_eliml *) simpl. apply subqual_meet_eliml.
    + apply (IHsubqual Qm X E2 Hs E1 Hwf eq_refl).
    + apply (wf_qua_qe_subst_gen E1 E2 X R Qm R2 Hwf Hs H0).
  - (* meet_elimr *) simpl. apply subqual_meet_elimr.
    + apply (wf_qua_qe_subst_gen E1 E2 X R Qm R1 Hwf Hs H).
    + apply (IHsubqual Qm X E2 Hs E1 Hwf eq_refl).
  - (* meet_intro *) simpl. apply subqual_meet_intro.
    + apply (IHsubqual1 Qm X E2 Hs E1 Hwf eq_refl).
    + apply (IHsubqual2 Qm X E2 Hs E1 Hwf eq_refl).
Qed.


Definition TSsubQ (E : env) (S T : typ) (D : sub E S T) : Prop :=
  forall E1 E2 X R Qm,
    E = E1 ++ (X, bind_qua Qm) :: E2 ->
    wf_env E ->
    subqual E2 R Qm ->
    sub (subst_env_qe X R E1 ++ E2) (subst_qt X R S) (subst_qt X R T).

Definition TSqtQ (E : env) (S T : qtyp) (D : subqtype E S T) : Prop :=
  forall E1 E2 X R Qm,
    E = E1 ++ (X, bind_qua Qm) :: E2 ->
    wf_env E ->
    subqual E2 R Qm ->
    subqtype (subst_env_qe X R E1 ++ E2) (subst_qqt X R S) (subst_qqt X R T).

Lemma TSsubQ_proof : forall E S T (D : sub E S T), TSsubQ E S T D.
Proof.
  apply (sub_mut_ind TSsubQ TSqtQ).
  - (* top *) intros E S HwfE HwS E1 E2 X R Qm HE Hwf Hs. subst E.
    apply sub_top.
    + apply (wf_env_qe_subst_gen E1 E2 X R Qm HwfE Hs).
    + apply (proj1 wf_typ_qe_subst_gen (E1 ++ (X, bind_qua Qm) :: E2) S HwS
               E1 E2 X R Qm eq_refl HwfE Hs).
  - (* refl *) intros E Y HwfE HwY E1 E2 X R Qm HE Hwf Hs. subst E.
    destruct (X == Y) as [Heq|Hneq].
    + subst Y. exfalso.
      inversion HwY; subst.
      pose proof (wf_env_uniq _ HwfE) as Hu.
      assert (HbMid : binds X (bind_qua Qm) (E1 ++ (X, bind_qua Qm) :: E2)).
      { apply binds_app_r with (E := E1). simpl. apply binds_cons_2; auto. }
      match goal with
      | Hb : binds X (bind_sub ?U0) _ |- _ =>
          pose proof (binds_unique binding X (bind_sub U0) (bind_qua Qm)
                      (E1 ++ (X, bind_qua Qm) :: E2) Hb HbMid Hu) as Hbad;
          inversion Hbad
      end.
    + apply sub_refl_tvar.
      * apply (wf_env_qe_subst_gen E1 E2 X R Qm HwfE Hs).
      * pose proof (proj1 wf_typ_qe_subst_gen (E1 ++ (X, bind_qua Qm) :: E2)
                      (typ_fvar Y) HwY E1 E2 X R Qm eq_refl HwfE Hs) as HY.
        simpl in HY. exact HY.
  - (* trans_tvar *) intros U E T Y b s IH E1 E2 X R Qm HE Hwf Hs. subst E.
    assert (HwfOld : wf_env (E1 ++ (X, bind_qua Qm) :: E2))
      by (apply (sub_wf_env (E1 ++ (X, bind_qua Qm) :: E2) (typ_fvar Y) T
                 (sub_trans_tvar U (E1 ++ (X, bind_qua Qm) :: E2) T Y b s))).
    destruct (binds_qe_sub_split E1 E2 X R Qm Y U HwfOld b) as [Hneq [U' [HU' Heq]]].
    simpl.
    apply (sub_trans_tvar U' (subst_env_qe X R E1 ++ E2) (subst_qt X R T) Y).
    + exact HU'.
    + rewrite Heq. apply (IH E1 E2 X R Qm eq_refl HwfOld Hs).
  - (* arrow *) intros E S1 S2 T1 T2 s1 IH1 s2 IH2 E1 E2 X R Qm HE Hwf Hs. subst E.
    assert (HwfOld : wf_env (E1 ++ (X, bind_qua Qm) :: E2))
      by (apply (sub_wf_env (E1 ++ (X, bind_qua Qm) :: E2) (typ_arrow S1 S2) (typ_arrow T1 T2)
                 (sub_arrow (E1 ++ (X, bind_qua Qm) :: E2) S1 S2 T1 T2 s1 s2))).
    simpl. apply sub_arrow.
    + apply (IH1 E1 E2 X R Qm eq_refl HwfOld Hs).
    + apply (IH2 E1 E2 X R Qm eq_refl HwfOld Hs).
  - (* all *) intros L E S1 S2 T1 T2 s1 IH1 s2 IH2 E1 E2 X R Qm HE Hwf Hs. subst E.
    assert (HwfOld : wf_env (E1 ++ (X, bind_qua Qm) :: E2))
      by (apply (sub_wf_env (E1 ++ (X, bind_qua Qm) :: E2) (typ_all S1 S2) (typ_all T1 T2)
                 (sub_all L (E1 ++ (X, bind_qua Qm) :: E2) S1 S2 T1 T2 s1 s2))).
    destruct (subqual_wf E2 R Qm Hs) as [HRq _].
    pose proof (wf_qua_qual E2 R HRq) as HqualR.
    simpl. apply (sub_all (union (add X L) (dom (E1 ++ (X, bind_qua Qm) :: E2))) (subst_env_qe X R E1 ++ E2)).
    + apply (IH1 E1 E2 X R Qm eq_refl HwfOld Hs).
    + intros Y HY.
      assert (HYL : Y `notin` L) by (simpl in HY; fsetdec).
      assert (HYX : Y <> X) by (intro Hc; subst Y; simpl in HY; fsetdec).
      assert (HYdom : Y `notin` dom (E1 ++ (X, bind_qua Qm) :: E2)) by (simpl in HY; fsetdec).
      assert (HwfBody : wf_env (Y ~ bind_sub T1 ++ E1 ++ (X, bind_qua Qm) :: E2)).
      { destruct (sub_wf (E1 ++ (X, bind_qua Qm) :: E2) T1 S1 s1) as [_ [HT1 _]].
        apply wf_env_sub with (X := Y); [exact HwfOld|exact HT1|exact HYdom]. }
      assert (Hcond : X `notin` fv_typ Y).
      { intro Hc. simpl in Hc. apply HYX. fsetdec. }
      assert (Hcomm : subst_qqt X R (open_tqt_rec 0 Y T2) =
                      open_tqt_rec 0 Y (subst_qqt X R T2)).
      { rewrite (subst_qqt_open_tqt_rec T2 0 X R Y HqualR Hcond). reflexivity. }
      assert (HcommS : subst_qqt X R (open_tqt_rec 0 Y S2) =
                       open_tqt_rec 0 Y (subst_qqt X R S2)).
      { rewrite (subst_qqt_open_tqt_rec S2 0 X R Y HqualR Hcond). reflexivity. }
      unfold open_tqt. rewrite <- HcommS. rewrite <- Hcomm. simpl.
      apply (IH2 Y HYL ((Y, bind_sub T1) :: E1) E2 X R Qm eq_refl HwfBody Hs).
  - (* qall *) intros L E S1 S2 T1 T2 sq s2 IH2 E1 E2 X R Qm HE Hwf Hs. subst E.
    assert (HwfOld : wf_env (E1 ++ (X, bind_qua Qm) :: E2))
      by (apply (sub_wf_env (E1 ++ (X, bind_qua Qm) :: E2) (typ_qall S1 S2) (typ_qall T1 T2)
                 (sub_qall L (E1 ++ (X, bind_qua Qm) :: E2) S1 S2 T1 T2 sq s2))).
    destruct (subqual_wf E2 R Qm Hs) as [HRq _].
    pose proof (wf_qua_qual E2 R HRq) as HqualR.
    simpl. apply (sub_qall (union (add X L) (dom (E1 ++ (X, bind_qua Qm) :: E2))) (subst_env_qe X R E1 ++ E2) (subst_qq X R S1)
                  (subst_qqt X R S2) (subst_qq X R T1) (subst_qqt X R T2)).
    + apply (subqual_qe_subst_gen E1 E2 X R Qm T1 S1 HwfOld Hs sq).
    + intros Y HY.
      assert (HYL : Y `notin` L) by (simpl in HY; fsetdec).
      assert (HYX : Y <> X) by (intro Hc; subst Y; simpl in HY; fsetdec).
      assert (HYdom : Y `notin` dom (E1 ++ (X, bind_qua Qm) :: E2)) by (simpl in HY; fsetdec).
      assert (HwfBody : wf_env (Y ~ bind_qua T1 ++ E1 ++ (X, bind_qua Qm) :: E2)).
      { destruct (subqual_wf (E1 ++ (X, bind_qua Qm) :: E2) T1 S1 sq) as [HQ1 _].
        apply wf_env_qua with (X := Y); [exact HwfOld|exact HQ1|exact HYdom]. }
      assert (Hcomm : subst_qqt X R (open_qqt_rec 0 (qua_fvar Y) T2) =
                      open_qqt_rec 0 (qua_fvar Y) (subst_qqt X R T2)).
      { rewrite (subst_qqt_open_qqt_rec T2 0 X R (qua_fvar Y) HqualR).
        rewrite (subst_qq_fvar_neq X Y R (fun Hc => HYX (eq_sym Hc))). reflexivity. }
      assert (HcommS : subst_qqt X R (open_qqt_rec 0 (qua_fvar Y) S2) =
                       open_qqt_rec 0 (qua_fvar Y) (subst_qqt X R S2)).
      { rewrite (subst_qqt_open_qqt_rec S2 0 X R (qua_fvar Y) HqualR).
        rewrite (subst_qq_fvar_neq X Y R (fun Hc => HYX (eq_sym Hc))). reflexivity. }
      unfold open_qqt. rewrite <- HcommS. rewrite <- Hcomm. simpl.
      apply (IH2 Y HYL ((Y, bind_qua T1) :: E1) E2 X R Qm eq_refl HwfBody Hs).
  - (* sum *) intros E S1 S2 T1 T2 s1 IH1 s2 IH2 E1 E2 X R Qm HE Hwf Hs. subst E.
    assert (HwfOld : wf_env (E1 ++ (X, bind_qua Qm) :: E2))
      by (apply (sub_wf_env (E1 ++ (X, bind_qua Qm) :: E2) (typ_sum S1 S2) (typ_sum T1 T2)
                 (sub_sum (E1 ++ (X, bind_qua Qm) :: E2) S1 S2 T1 T2 s1 s2))).
    simpl. apply sub_sum;
      [apply (IH1 E1 E2 X R Qm eq_refl HwfOld Hs)|apply (IH2 E1 E2 X R Qm eq_refl HwfOld Hs)].
  - (* pair *) intros E S1 S2 T1 T2 s1 IH1 s2 IH2 E1 E2 X R Qm HE Hwf Hs. subst E.
    assert (HwfOld : wf_env (E1 ++ (X, bind_qua Qm) :: E2))
      by (apply (sub_wf_env (E1 ++ (X, bind_qua Qm) :: E2) (typ_pair S1 S2) (typ_pair T1 T2)
                 (sub_pair (E1 ++ (X, bind_qua Qm) :: E2) S1 S2 T1 T2 s1 s2))).
    simpl. apply sub_pair;
      [apply (IH1 E1 E2 X R Qm eq_refl HwfOld Hs)|apply (IH2 E1 E2 X R Qm eq_refl HwfOld Hs)].
  - (* qtyp *) intros E Q1 T1 Q2 T2 sq s IH E1 E2 X R Qm HE Hwf Hs. subst E.
    assert (HwfOld : wf_env (E1 ++ (X, bind_qua Qm) :: E2))
      by (apply (subqtype_wf_env (E1 ++ (X, bind_qua Qm) :: E2) (qtyp_qtyp Q1 T1) (qtyp_qtyp Q2 T2)
                 (sub_qtyp_qtyp (E1 ++ (X, bind_qua Qm) :: E2) Q1 T1 Q2 T2 sq s))).
    simpl. apply sub_qtyp_qtyp.
    + apply (subqual_qe_subst_gen E1 E2 X R Qm Q1 Q2 HwfOld Hs sq).
    + apply (IH E1 E2 X R Qm eq_refl HwfOld Hs).
Qed.

Lemma TSqtQ_proof : forall E S T (D : subqtype E S T), TSqtQ E S T D.
Proof.
  intros E S T D. destruct D as [E0 Q1 T1 Q2 T2 sq s]. simpl in *.
  unfold TSqtQ. intros E1 E2 X R Qm HE Hwf Hs. subst E0.
  apply sub_qtyp_qtyp.
  - apply (subqual_qe_subst_gen E1 E2 X R Qm Q1 Q2 Hwf Hs sq).
  - apply (TSsubQ_proof (E1 ++ (X, bind_qua Qm) :: E2) T1 T2 s
                       E1 E2 X R Qm eq_refl Hwf Hs).
Qed.

Lemma sub_qt_subst_gen : forall E1 E2 X R Qm S T,
  subqual E2 R Qm ->
  sub (E1 ++ (X, bind_qua Qm) :: E2) S T ->
  sub (subst_env_qe X R E1 ++ E2) (subst_qt X R S) (subst_qt X R T).
Proof.
  intros E1 E2 X R Qm S T Hs H.
  exact (TSsubQ_proof (E1 ++ (X, bind_qua Qm) :: E2) S T H
                     E1 E2 X R Qm eq_refl (sub_wf_env _ _ _ H) Hs).
Qed.

Lemma subqtype_qt_subst_gen : forall E1 E2 X R Qm S T,
  subqual E2 R Qm ->
  subqtype (E1 ++ (X, bind_qua Qm) :: E2) S T ->
  subqtype (subst_env_qe X R E1 ++ E2) (subst_qqt X R S) (subst_qqt X R T).
Proof.
  intros E1 E2 X R Qm S T Hs H.
  exact (TSqtQ_proof (E1 ++ (X, bind_qua Qm) :: E2) S T H
                    E1 E2 X R Qm eq_refl (subqtype_wf_env _ _ _ H) Hs).
Qed.

Lemma sub_qt_subst : forall E X R Q S T,
  subqual E R Q ->
  sub (X ~ bind_qua Q ++ E) S T ->
  sub E (subst_qt X R S) (subst_qt X R T).
Proof.
  intros E X R Q S T Hs H.
  pose proof (sub_qt_subst_gen (@nil (atom * binding)) E X R Q S T Hs H) as Hres.
  simpl in Hres. exact Hres.
Qed.

Lemma subqtype_qt_subst : forall E X R Q S T,
  subqual E R Q ->
  subqtype (X ~ bind_qua Q ++ E) S T ->
  subqtype E (subst_qqt X R S) (subst_qqt X R T).
Proof.
  intros E X R Q S T Hs H.
  pose proof (subqtype_qt_subst_gen (@nil (atom * binding)) E X R Q S T Hs H) as Hres.
  simpl in Hres. exact Hres.
Qed.

Lemma subst_qt_open_tt_rec_gen :
  (forall T K X R W, qual R ->
     subst_qt X R (open_tt_rec K W T) =
     open_tt_rec K (subst_qt X R W) (subst_qt X R T)) /\
  (forall T : qtyp, forall K X R W, qual R ->
     subst_qqt X R (open_tqt_rec K W T) =
     open_tqt_rec K (subst_qt X R W) (subst_qqt X R T)).
Proof.
  split.
  - apply (typ_mut_ind
      (fun T => forall K X R W, qual R ->
         subst_qt X R (open_tt_rec K W T) =
         open_tt_rec K (subst_qt X R W) (subst_qt X R T))
      (fun T => forall K X R W, qual R ->
         subst_qqt X R (open_tqt_rec K W T) =
         open_tqt_rec K (subst_qt X R W) (subst_qqt X R T))).
    + intros; reflexivity.
    + intros n K X R W HR. simpl. destruct (K == n); simpl; reflexivity.
    + intros; reflexivity.
    + intros q1 IH1 q2 IH2 K X R W HR. simpl. f_equal.
      * apply IH1. exact HR.
      * apply IH2. exact HR.
    + intros T1 IH1 q IH2 K X R W HR. simpl. f_equal.
      * apply IH1. exact HR.
      * apply IH2. exact HR.
    + intros Q q IH K X R W HR. simpl. f_equal. apply IH. exact HR.
    + intros q1 IH1 q2 IH2 K X R W HR. simpl. f_equal;
        [apply IH1|apply IH2]; exact HR.
    + intros q1 IH1 q2 IH2 K X R W HR. simpl. f_equal;
        [apply IH1|apply IH2]; exact HR.
    + intros q IH K X R W HR. simpl. f_equal. apply IH. exact HR.
    + intros Q T IH K X R W HR. simpl. f_equal. apply IH. exact HR.
  - apply (qtyp_mut_ind
      (fun T => forall K X R W, qual R ->
         subst_qt X R (open_tt_rec K W T) =
         open_tt_rec K (subst_qt X R W) (subst_qt X R T))
      (fun T => forall K X R W, qual R ->
         subst_qqt X R (open_tqt_rec K W T) =
         open_tqt_rec K (subst_qt X R W) (subst_qqt X R T))).
    + intros; reflexivity.
    + intros n K X R W HR. simpl. destruct (K == n); simpl; reflexivity.
    + intros; reflexivity.
    + intros q1 IH1 q2 IH2 K X R W HR. simpl. f_equal;
        [apply IH1|apply IH2]; exact HR.
    + intros T1 IH1 q IH2 K X R W HR. simpl. f_equal;
        [apply IH1|apply IH2]; exact HR.
    + intros Q q IH K X R W HR. simpl. f_equal. apply IH. exact HR.
    + intros q1 IH1 q2 IH2 K X R W HR. simpl. f_equal;
        [apply IH1|apply IH2]; exact HR.
    + intros q1 IH1 q2 IH2 K X R W HR. simpl. f_equal;
        [apply IH1|apply IH2]; exact HR.
    + intros q IH K X R W HR. simpl. f_equal. apply IH. exact HR.
    + intros Q T IH K X R W HR. simpl. f_equal. apply IH. exact HR.
Qed.


(* ================================================================== *)
(* Qualifier-variable substitution for typing                    *)
(* ================================================================== *)
Lemma typing_subst_qe_gen : forall E1 E2 X R Qm e T,
  subqual E2 R Qm ->
  typing (E1 ++ (X, bind_qua Qm) :: E2) e T ->
  typing (subst_env_qe X R E1 ++ E2) (subst_qe X R e) (subst_qqt X R T).
Proof.
  intros E1 E2 X R Qm e T Hs H.
  dependent induction H.
  - (* var *) destruct (binds_qe_typ_split E1 E2 X R Qm x T H H0) as [Hneq [T' [HT' Heq]]].
    rewrite <- Heq. simpl.
    apply typing_var.
    + apply (wf_env_qe_subst_gen E1 E2 X R Qm H Hs).
    + exact HT'.
  - (* abs *) simpl.
    destruct (subqual_wf E2 R Qm Hs) as [HRq _].
    pose proof (wf_qua_qual E2 R HRq) as HqualR.
    destruct (atom_fresh L) as [x0 Hx0].
    assert (HwfOld : wf_env (E1 ++ (X, bind_qua Qm) :: E2)).
    { apply (wf_env_head_inv x0 (bind_typ V) (E1 ++ (X, bind_qua Qm) :: E2)).
      apply (typing_wf_env _ _ _ (H0 x0 Hx0)). }
    eapply typing_abs with (L := union L (add X (dom (subst_env_qe X R E1 ++ E2)))).
    + apply (wf_qua_qe_subst_gen E1 E2 X R Qm P HwfOld Hs H).
    + intros x Hx.
      assert (HxL : x `notin` L) by (simpl in Hx; fsetdec).
      assert (HxX : x <> X) by (intro Hc; subst x; simpl in Hx; fsetdec).
      assert (Hxf : X `notin` fv_exp (exp_fvar x)).
      { intro Hc. simpl in Hc. apply HxX. fsetdec. }
      replace (open_ee (subst_qe X R e1) x)
        with (subst_qe X R (open_ee e1 x))
        by (exact (subst_qe_open_ee_rec e1 0 X R (exp_fvar x) HqualR Hxf)).
      simpl. apply (H1 x HxL ((x, bind_typ V) :: E1) E2 X Qm Hs eq_refl).
  - (* app *) simpl. eapply typing_app.
    + apply (IHtyping1 E1 E2 X Qm Hs eq_refl).
    + apply (IHtyping2 E1 E2 X Qm Hs eq_refl).
  - (* tabs *) simpl.
    destruct (subqual_wf E2 R Qm Hs) as [HRq _].
    pose proof (wf_qua_qual E2 R HRq) as HqualR.
    destruct (atom_fresh L) as [x0 Hx0].
    assert (HwfOld : wf_env (E1 ++ (X, bind_qua Qm) :: E2)).
    { apply (wf_env_head_inv x0 (bind_sub V) (E1 ++ (X, bind_qua Qm) :: E2)).
      apply (typing_wf_env _ _ _ (H0 x0 Hx0)). }
    eapply typing_tabs with (L := union L (add X (dom (subst_env_qe X R E1 ++ E2)))).
    + apply (wf_qua_qe_subst_gen E1 E2 X R Qm P HwfOld Hs H).
    + intros Y HY.
      assert (HYL : Y `notin` L) by (simpl in HY; fsetdec).
      assert (HYX : Y <> X) by (intro Hc; subst Y; simpl in HY; fsetdec).
      assert (HcondY : X `notin` fv_typ (typ_fvar Y)).
      { intro Hc. simpl in Hc. apply HYX. fsetdec. }
      replace (open_te (subst_qe X R e1) Y)
        with (subst_qe X R (open_te e1 Y))
        by (exact (subst_qe_open_te_rec e1 0 X R (typ_fvar Y) HqualR HcondY)).
      assert (Hcomm : subst_qqt X R (open_tqt_rec 0 Y T1) =
                      open_tqt_rec 0 Y (subst_qqt X R T1)).
      { rewrite ((proj2 subst_qt_open_tt_rec_gen) T1 0 X R Y HqualR). simpl. reflexivity. }
      unfold open_tqt. rewrite <- Hcomm. simpl.
      apply (H1 Y HYL ((Y, bind_sub V) :: E1) E2 X Qm Hs eq_refl).
  - (* tapp *) simpl.
    destruct (subqual_wf E2 R Qm Hs) as [HRq _].
    pose proof (wf_qua_qual E2 R HRq) as HqualR.
    pose proof (IHtyping E1 E2 X Qm Hs eq_refl) as IHt.
    pose proof (sub_qt_subst_gen E1 E2 X R Qm T T1 Hs H0) as Hsub'.
    unfold open_tqt. rewrite ((proj2 subst_qt_open_tt_rec_gen) T2 0 X R T HqualR).
    eapply typing_tapp.
    + exact IHt.
    + exact Hsub'.
  - (* qabs *) simpl.
    destruct (subqual_wf E2 R Qm Hs) as [HRq _].
    pose proof (wf_qua_qual E2 R HRq) as HqualR.
    destruct (atom_fresh L) as [x0 Hx0].
    assert (HwfOld : wf_env (E1 ++ (X, bind_qua Qm) :: E2)).
    { apply (wf_env_head_inv x0 (bind_qua Q) (E1 ++ (X, bind_qua Qm) :: E2)).
      apply (typing_wf_env _ _ _ (H0 x0 Hx0)). }
    eapply typing_qabs with (L := union L (add X (dom (subst_env_qe X R E1 ++ E2)))).
    + apply (wf_qua_qe_subst_gen E1 E2 X R Qm P HwfOld Hs H).
    + intros Y HY.
      assert (HYL : Y `notin` L) by (simpl in HY; fsetdec).
      assert (HYX : Y <> X) by (intro Hc; subst Y; simpl in HY; fsetdec).
      replace (open_qe (subst_qe X R e1) Y)
        with (subst_qe X R (open_qe e1 Y))
        by (change (subst_qe X R (open_qe_rec 0 (qua_fvar Y) e1) =
                    open_qe_rec 0 (qua_fvar Y) (subst_qe X R e1));
            rewrite (subst_qe_open_qe_rec e1 0 X R (qua_fvar Y) HqualR);
            rewrite (subst_qq_fvar_neq X Y R (fun Hc => HYX (eq_sym Hc))); reflexivity).
      assert (Hcomm : subst_qqt X R (open_qqt_rec 0 (qua_fvar Y) T1) =
                      open_qqt_rec 0 (qua_fvar Y) (subst_qqt X R T1)).
      { rewrite (subst_qqt_open_qqt_rec T1 0 X R (qua_fvar Y) HqualR).
        rewrite (subst_qq_fvar_neq X Y R (fun Hc => HYX (eq_sym Hc))). reflexivity. }
      unfold open_qqt. rewrite <- Hcomm. simpl.
      apply (H1 Y HYL ((Y, bind_qua Q) :: E1) E2 X Qm Hs eq_refl).
  - (* qapp *) simpl.
    destruct (subqual_wf E2 R Qm Hs) as [HRq _].
    pose proof (wf_qua_qual E2 R HRq) as HqualR.
    assert (HwfOld : wf_env (E1 ++ (X, bind_qua Qm) :: E2))
      by (apply (typing_wf_env _ _ _ H)).
    unfold open_qqt. rewrite (subst_qqt_open_qqt_rec T 0 X R Q HqualR).
    eapply typing_qapp.
    + apply (IHtyping E1 E2 X Qm Hs eq_refl).
    + apply (subqual_qe_subst_gen E1 E2 X R Qm Q Q1 HwfOld Hs H0).
  - (* sub *) simpl.
    eapply typing_sub.
    + apply (IHtyping E1 E2 X Qm Hs eq_refl).
    + apply (subqtype_qt_subst_gen E1 E2 X R Qm S T Hs H0).
  - (* let *) simpl.
    destruct (subqual_wf E2 R Qm Hs) as [HRq _].
    pose proof (wf_qua_qual E2 R HRq) as HqualR.
    eapply typing_let with (T1 := subst_qqt X R T1) (T2 := subst_qqt X R T2)
                            (L := union L (add X (dom (subst_env_qe X R E1 ++ E2)))).
    + apply (IHtyping E1 E2 X Qm Hs eq_refl).
    + intros x Hx.
      assert (HxL : x `notin` L) by (simpl in Hx; fsetdec).
      assert (HxX : x <> X) by (intro Hc; subst x; simpl in Hx; fsetdec).
      assert (Hxf : X `notin` fv_exp (exp_fvar x)).
      { intro Hc. simpl in Hc. apply HxX. fsetdec. }
      replace (open_ee (subst_qe X R e2) x)
        with (subst_qe X R (open_ee e2 x))
        by (exact (subst_qe_open_ee_rec e2 0 X R (exp_fvar x) HqualR Hxf)).
      simpl. apply (H1 x HxL ((x, bind_typ T1) :: E1) E2 X Qm Hs eq_refl).
  - (* inl *) simpl.
    assert (HwfOld : wf_env (E1 ++ (X, bind_qua Qm) :: E2))
      by (apply (typing_wf_env _ _ _ H0)).
    eapply typing_inl.
    + apply (wf_qua_qe_subst_gen E1 E2 X R Qm P HwfOld Hs H).
    + apply (IHtyping E1 E2 X Qm Hs eq_refl).
    + apply (proj2 wf_typ_qe_subst_gen (E1 ++ (X, bind_qua Qm) :: E2) T2 H1
                E1 E2 X R Qm eq_refl HwfOld Hs).
  - (* inr *) simpl.
    assert (HwfOld : wf_env (E1 ++ (X, bind_qua Qm) :: E2))
      by (apply (typing_wf_env _ _ _ H0)).
    eapply typing_inr.
    + apply (wf_qua_qe_subst_gen E1 E2 X R Qm P HwfOld Hs H).
    + apply (IHtyping E1 E2 X Qm Hs eq_refl).
    + apply (proj2 wf_typ_qe_subst_gen (E1 ++ (X, bind_qua Qm) :: E2) T1 H1
                E1 E2 X R Qm eq_refl HwfOld Hs).
  - (* case *) simpl.
    destruct (subqual_wf E2 R Qm Hs) as [HRq _].
    pose proof (wf_qua_qual E2 R HRq) as HqualR.
    eapply typing_case with (T1 := subst_qqt X R T1) (T2 := subst_qqt X R T2)
                             (T := subst_qqt X R T) (Q := subst_qq X R Q)
                             (L := union L (add X (dom (subst_env_qe X R E1 ++ E2)))).
    + apply (IHtyping E1 E2 X Qm Hs eq_refl).
    + intros x Hx.
      assert (HxL : x `notin` L) by (simpl in Hx; fsetdec).
      assert (HxX : x <> X) by (intro Hc; subst x; simpl in Hx; fsetdec).
      assert (Hxf : X `notin` fv_exp (exp_fvar x)).
      { intro Hc. simpl in Hc. apply HxX. fsetdec. }
      replace (open_ee (subst_qe X R e2) x)
        with (subst_qe X R (open_ee e2 x))
        by (exact (subst_qe_open_ee_rec e2 0 X R (exp_fvar x) HqualR Hxf)).
      simpl. apply (H1 x HxL ((x, bind_typ T1) :: E1) E2 X Qm Hs eq_refl).
    + intros x Hx.
      assert (HxL : x `notin` L) by (simpl in Hx; fsetdec).
      assert (HxX : x <> X) by (intro Hc; subst x; simpl in Hx; fsetdec).
      assert (Hxf : X `notin` fv_exp (exp_fvar x)).
      { intro Hc. simpl in Hc. apply HxX. fsetdec. }
      replace (open_ee (subst_qe X R e3) x)
        with (subst_qe X R (open_ee e3 x))
        by (exact (subst_qe_open_ee_rec e3 0 X R (exp_fvar x) HqualR Hxf)).
      simpl. apply (H3 x HxL ((x, bind_typ T2) :: E1) E2 X Qm Hs eq_refl).
  - (* pair *) simpl.
    assert (HwfOld : wf_env (E1 ++ (X, bind_qua Qm) :: E2))
      by (apply (typing_wf_env _ _ _ H0)).
    eapply typing_pair.
    + apply (wf_qua_qe_subst_gen E1 E2 X R Qm P HwfOld Hs H).
    + apply (IHtyping1 E1 E2 X Qm Hs eq_refl).
    + apply (IHtyping2 E1 E2 X Qm Hs eq_refl).
  - (* first *) simpl. eapply typing_first.
    apply (IHtyping E1 E2 X Qm Hs eq_refl).
  - (* second *) simpl. eapply typing_second.
    apply (IHtyping E1 E2 X Qm Hs eq_refl).
  - (* upqual *) simpl.
    assert (HwfOld : wf_env (E1 ++ (X, bind_qua Qm) :: E2))
      by (apply (typing_wf_env _ _ _ H)).
    eapply typing_upqual.
    + apply (IHtyping E1 E2 X Qm Hs eq_refl).
    + apply (subqual_qe_subst_gen E1 E2 X R Qm Q P HwfOld Hs H0).
  - (* check *) simpl.
    assert (HwfOld : wf_env (E1 ++ (X, bind_qua Qm) :: E2))
      by (apply (typing_wf_env _ _ _ H)).
    eapply typing_check.
    + apply (IHtyping E1 E2 X Qm Hs eq_refl).
    + apply (subqual_qe_subst_gen E1 E2 X R Qm Q P HwfOld Hs H0).
Qed.

Lemma typing_subst_qe : forall E X R Q e T,
  subqual E R Q ->
  typing (X ~ bind_qua Q ++ E) e T ->
  typing E (subst_qe X R e) (subst_qqt X R T).
Proof.
  intros E X R Q e T Hs H.
  pose proof (typing_subst_qe_gen (@nil (atom * binding)) E X R Q e T Hs H) as Hres.
  simpl in Hres. exact Hres.
Qed.

Lemma typing_subst_ee : forall E x v T1 e T,
  typing E v T1 ->
  typing (x ~ bind_typ T1 ++ E) e T ->
  typing E (subst_ee x v e) T.
Proof.
  intros E x v T1 e T Hv H.
  pose proof (typing_subst_ee_gen (@nil (atom * binding)) E x v T1 e T Hv H) as Hres.
  simpl in Hres. exact Hres.
Qed.


(* ================================================================== *)
(* Inversion lemmas for value typing                              *)
(* ================================================================== *)
Lemma subqtype_inv_comp : forall E Q1 T1 Q2 T2,
  subqtype E (qtyp_qtyp Q1 T1) (qtyp_qtyp Q2 T2) ->
  subqual E Q1 Q2 /\ sub E T1 T2.
Proof. intros. inversion H; subst; split; assumption. Qed.

Lemma sub_arrow_inv_comp : forall E S1 S2 T1 T2,
  sub E (typ_arrow S1 S2) (typ_arrow T1 T2) ->
  subqtype E T1 S1 /\ subqtype E S2 T2.
Proof. intros. inversion H; subst; split; assumption. Qed.

Lemma sub_sum_inv_comp : forall E S1 S2 T1 T2,
  sub E (typ_sum S1 S2) (typ_sum T1 T2) ->
  subqtype E S1 T1 /\ subqtype E S2 T2.
Proof. intros. inversion H; subst; split; assumption. Qed.

Lemma sub_pair_inv_comp : forall E S1 S2 T1 T2,
  sub E (typ_pair S1 S2) (typ_pair T1 T2) ->
  subqtype E S1 T1 /\ subqtype E S2 T2.
Proof. intros. inversion H; subst; split; assumption. Qed.

Lemma sub_all_inv_comp : forall E S1 S2 T1 T2,
  sub E (typ_all S1 S2) (typ_all T1 T2) ->
  exists L, sub E T1 S1 /\
    (forall X, X `notin` L ->
       subqtype (X ~ bind_sub T1 ++ E) (open_tqt S2 X) (open_tqt T2 X)).
Proof. intros. inversion H; subst. eexists. split; eassumption. Qed.

Lemma sub_qall_inv_comp : forall E S1 S2 T1 T2,
  sub E (typ_qall S1 S2) (typ_qall T1 T2) ->
  exists L, subqual E T1 S1 /\
    (forall X, X `notin` L ->
       subqtype (X ~ bind_qua T1 ++ E) (open_qqt S2 X) (open_qqt T2 X)).
Proof. intros. inversion H; subst. eexists. split; eassumption. Qed.

Lemma typing_abs_inv_gen : forall E P V e1 T,
  typing E (exp_abs P V e1) T ->
  exists bodyTy L,
    wf_qua E P /\
    (forall x, x `notin` L ->
       typing (x ~ bind_typ V ++ E) (open_ee e1 x) bodyTy) /\
    (T = qtyp_qtyp P (typ_arrow V bodyTy) \/
     subqtype E (qtyp_qtyp P (typ_arrow V bodyTy)) T).
Proof.
  intros E P V e1 T H.
  remember (exp_abs P V e1) as e0 eqn:He.
  dependent induction H; try discriminate.
  - inversion He; subst. exists T1, L. split; [exact H|]. split; [intros x Hx; apply H0; exact Hx|].
    left. subst. reflexivity.
  - destruct (IHtyping He) as [bodyTy [L [Hq [Hbody Hrel]]]].
    exists bodyTy, L. split; [exact Hq|]. split; [exact Hbody|].
    destruct Hrel as [Heq|Hsub].
    + subst S. right. exact H0.
    + right. apply (subqtype_trans E (qtyp_qtyp P (typ_arrow V bodyTy)) S T Hsub H0).
Qed.

Lemma typing_tabs_inv_gen : forall E P V e1 T,
  typing E (exp_tabs P V e1) T ->
  exists bodyTy L,
    wf_qua E P /\
    (forall X, X `notin` L ->
       typing (X ~ bind_sub V ++ E) (open_te e1 X) (open_tqt bodyTy X)) /\
    (T = qtyp_qtyp P (typ_all V bodyTy) \/
     subqtype E (qtyp_qtyp P (typ_all V bodyTy)) T).
Proof.
  intros E P V e1 T H.
  remember (exp_tabs P V e1) as e0 eqn:He.
  dependent induction H; try discriminate.
  - inversion He; subst. exists T1, L. split; [exact H|]. split; [intros x Hx; apply H0; exact Hx|].
    left. subst. reflexivity.
  - destruct (IHtyping He) as [bodyTy [L [Hq [Hbody Hrel]]]].
    exists bodyTy, L. split; [exact Hq|]. split; [exact Hbody|].
    destruct Hrel as [Heq|Hsub].
    + subst S. right. exact H0.
    + right. apply (subqtype_trans E (qtyp_qtyp P (typ_all V bodyTy)) S T Hsub H0).
Qed.

Lemma typing_qabs_inv_gen : forall E P Q e1 T,
  typing E (exp_qabs P Q e1) T ->
  exists bodyTy L,
    wf_qua E P /\
    (forall X, X `notin` L ->
       typing (X ~ bind_qua Q ++ E) (open_qe e1 X) (open_qqt bodyTy X)) /\
    (T = qtyp_qtyp P (typ_qall Q bodyTy) \/
     subqtype E (qtyp_qtyp P (typ_qall Q bodyTy)) T).
Proof.
  intros E P Q e1 T H.
  remember (exp_qabs P Q e1) as e0 eqn:He.
  dependent induction H; try discriminate.
  - inversion He; subst. exists T1, L. split; [exact H|]. split; [intros x Hx; apply H0; exact Hx|].
    left. subst. reflexivity.
  - destruct (IHtyping He) as [bodyTy [L [Hq [Hbody Hrel]]]].
    exists bodyTy, L. split; [exact Hq|]. split; [exact Hbody|].
    destruct Hrel as [Heq|Hsub].
    + subst S. right. exact H0.
    + right. apply (subqtype_trans E (qtyp_qtyp P (typ_qall Q bodyTy)) S T Hsub H0).
Qed.

Lemma typing_inl_inv_gen : forall E P e1 T,
  typing E (exp_inl P e1) T ->
  exists V1 V2,
    wf_qua E P /\ typing E e1 V1 /\ wf_qtyp E V2 /\
    (T = qtyp_qtyp P (typ_sum V1 V2) \/
     subqtype E (qtyp_qtyp P (typ_sum V1 V2)) T).
Proof.
  intros E P e1 T H.
  remember (exp_inl P e1) as e0 eqn:He.
  dependent induction H; try discriminate.
  - destruct (IHtyping He) as [V1 [V2 [Hq [H1 [Hwf Hrel]]]]].
    exists V1, V2. split; [exact Hq|]. split; [exact H1|]. split; [exact Hwf|].
    destruct Hrel as [Heq|Hsub].
    + subst S. right. exact H0.
    + right. apply (subqtype_trans E (qtyp_qtyp P (typ_sum V1 V2)) S T Hsub H0).
  - inversion He; subst. exists T1, T2. split; [exact H|]. split; [exact H0|]. split; [exact H1|].
    left. reflexivity.
Qed.

Lemma typing_inr_inv_gen : forall E P e1 T,
  typing E (exp_inr P e1) T ->
  exists V1 V2,
    wf_qua E P /\ typing E e1 V2 /\ wf_qtyp E V1 /\
    (T = qtyp_qtyp P (typ_sum V1 V2) \/
     subqtype E (qtyp_qtyp P (typ_sum V1 V2)) T).
Proof.
  intros E P e1 T H.
  remember (exp_inr P e1) as e0 eqn:He.
  dependent induction H; try discriminate.
  - destruct (IHtyping He) as [V1 [V2 [Hq [H1 [Hwf Hrel]]]]].
    exists V1, V2. split; [exact Hq|]. split; [exact H1|]. split; [exact Hwf|].
    destruct Hrel as [Heq|Hsub].
    + subst S. right. exact H0.
    + right. apply (subqtype_trans E (qtyp_qtyp P (typ_sum V1 V2)) S T Hsub H0).
  - inversion He; subst. exists T1, T2. split; [exact H|]. split; [exact H0|]. split; [exact H1|].
    left. reflexivity.
Qed.

Lemma typing_pair_inv_gen : forall E P e1 e2 T,
  typing E (exp_pair P e1 e2) T ->
  exists V1 V2,
    wf_qua E P /\ typing E e1 V1 /\ typing E e2 V2 /\
    (T = qtyp_qtyp P (typ_pair V1 V2) \/
     subqtype E (qtyp_qtyp P (typ_pair V1 V2)) T).
Proof.
  intros E P e1 e2 T H.
  remember (exp_pair P e1 e2) as e0 eqn:He.
  dependent induction H; try discriminate.
  - destruct (IHtyping He) as [V1 [V2 [Hq [H1 [H2 Hrel]]]]].
    exists V1, V2. split; [exact Hq|]. split; [exact H1|]. split; [exact H2|].
    destruct Hrel as [Heq|Hsub].
    + subst S. right. exact H0.
    + right. apply (subqtype_trans E (qtyp_qtyp P (typ_pair V1 V2)) S T Hsub H0).
  - inversion He; subst. exists T1, T2. split; [exact H|]. split; [exact H0|]. split; [exact H1|].
    left. reflexivity.
Qed.


(* ================================================================== *)
(* Inversion lemmas for compound expression typing                *)
(* ================================================================== *)
Lemma typing_app_inv_gen : forall E e1 e2 T,
  typing E (exp_app e1 e2) T ->
  exists Q T1 T2,
    typing E e1 (qtyp_qtyp Q (typ_arrow T1 T2)) /\ typing E e2 T1 /\
    (T = T2 \/ subqtype E T2 T).
Proof.
  intros E e1 e2 T H.
  remember (exp_app e1 e2) as e0 eqn:He.
  dependent induction H; try discriminate.
  - inversion He; subst. exists Q, T1, T2. split; [exact H|]. split; [exact H0|].
    left. reflexivity.
  - destruct (IHtyping He) as [Q [T1 [T2 [H1 [H2 Hrel]]]]].
    exists Q, T1, T2. split; [exact H1|]. split; [exact H2|].
    destruct Hrel as [Heq|Hsub].
    + subst S. right. exact H0.
    + right. apply (subqtype_trans E T2 S T Hsub H0).
Qed.

Lemma typing_tapp_inv_gen : forall E e1 T0 T,
  typing E (exp_tapp e1 T0) T ->
  exists Q T1 T2,
    typing E e1 (qtyp_qtyp Q (typ_all T1 T2)) /\ sub E T0 T1 /\
    (T = open_tqt T2 T0 \/ subqtype E (open_tqt T2 T0) T).
Proof.
  intros E e1 T0 T H.
  remember (exp_tapp e1 T0) as e0 eqn:He.
  dependent induction H; try discriminate.
  - inversion He; subst. exists Q, T1, T2. split; [exact H|]. split; [exact H0|].
    left. reflexivity.
  - destruct (IHtyping He) as [Q [T1 [T2 [H1 [Hsub Hrel]]]]].
    exists Q, T1, T2. split; [exact H1|]. split; [exact Hsub|].
    destruct Hrel as [Heq|Hsubq].
    + subst S. right. exact H0.
    + right. apply (subqtype_trans E (open_tqt T2 T0) S T Hsubq H0).
Qed.

Lemma typing_qapp_inv_gen : forall E e1 Q0 T,
  typing E (exp_qapp e1 Q0) T ->
  exists R Q1 T1,
    typing E e1 (qtyp_qtyp R (typ_qall Q1 T1)) /\ subqual E Q0 Q1 /\
    (T = open_qqt T1 Q0 \/ subqtype E (open_qqt T1 Q0) T).
Proof.
  intros E e1 Q0 T H.
  remember (exp_qapp e1 Q0) as e0 eqn:He.
  dependent induction H; try discriminate.
  - inversion He; subst. exists R, Q1, T. split; [exact H|]. split; [exact H0|].
    left. reflexivity.
  - destruct (IHtyping He) as [R [Q1 [T1 [H1 [Hsub Hrel]]]]].
    exists R, Q1, T1. split; [exact H1|]. split; [exact Hsub|].
    destruct Hrel as [Heq|Hsubq].
    + subst S. right. exact H0.
    + right. apply (subqtype_trans E (open_qqt T1 Q0) S T Hsubq H0).
Qed.

Lemma typing_let_inv_gen : forall E e1 e2 T,
  typing E (exp_let e1 e2) T ->
  exists T1 T2 L,
    typing E e1 T1 /\
    (forall x, x `notin` L -> typing (x ~ bind_typ T1 ++ E) (open_ee e2 x) T2) /\
    (T = T2 \/ subqtype E T2 T).
Proof.
  intros E e1 e2 T H.
  remember (exp_let e1 e2) as e0 eqn:He.
  dependent induction H; try discriminate.
  - destruct (IHtyping He) as [T1 [T2 [L [H1 [Hbody Hrel]]]]].
    exists T1, T2, L. split; [exact H1|]. split; [exact Hbody|].
    destruct Hrel as [Heq|Hsub].
    + subst S. right. exact H0.
    + right. apply (subqtype_trans E T2 S T Hsub H0).
  - inversion He; subst. exists T1, T2, L. split; [exact H|]. split; [exact H0|].
    left. reflexivity.
Qed.

Lemma typing_case_inv_gen : forall E e1 e2 e3 T,
  typing E (exp_case e1 e2 e3) T ->
  exists Q T1 T2 Tbody L,
    typing E e1 (qtyp_qtyp Q (typ_sum T1 T2)) /\
    (forall x, x `notin` L -> typing (x ~ bind_typ T1 ++ E) (open_ee e2 x) Tbody) /\
    (forall x, x `notin` L -> typing (x ~ bind_typ T2 ++ E) (open_ee e3 x) Tbody) /\
    (T = Tbody \/ subqtype E Tbody T).
Proof.
  intros E e1 e2 e3 T H.
  remember (exp_case e1 e2 e3) as e0 eqn:He.
  dependent induction H; try discriminate.
  - destruct (IHtyping He) as [Q [T1 [T2 [Tbody [L [H1 [Hb2 [Hb3 Hrel]]]]]]]].
    exists Q, T1, T2, Tbody, L. split; [exact H1|]. split; [exact Hb2|]. split; [exact Hb3|].
    destruct Hrel as [Heq|Hsub].
    + subst S. right. exact H0.
    + right. apply (subqtype_trans E Tbody S T Hsub H0).
  - inversion He; subst. exists Q, T1, T2, T, L. split; [exact H|]. split; [exact H0|].
    split; [exact H2|]. left. reflexivity.
Qed.

Lemma typing_first_inv_gen : forall E e T,
  typing E (exp_first e) T ->
  exists Q T1 T2,
    typing E e (qtyp_qtyp Q (typ_pair T1 T2)) /\ (T = T1 \/ subqtype E T1 T).
Proof.
  intros E e T H.
  remember (exp_first e) as e0 eqn:He.
  dependent induction H; try discriminate.
  - destruct (IHtyping He) as [Q [T1 [T2 [H1 Hrel]]]].
    exists Q, T1, T2. split; [exact H1|].
    destruct Hrel as [Heq|Hsub].
    + subst S. right. exact H0.
    + right. apply (subqtype_trans E T1 S T Hsub H0).
  - inversion He; subst. exists Q, T1, T2. split; [exact H|]. left. reflexivity.
Qed.

Lemma typing_second_inv_gen : forall E e T,
  typing E (exp_second e) T ->
  exists Q T1 T2,
    typing E e (qtyp_qtyp Q (typ_pair T1 T2)) /\ (T = T2 \/ subqtype E T2 T).
Proof.
  intros E e T H.
  remember (exp_second e) as e0 eqn:He.
  dependent induction H; try discriminate.
  - destruct (IHtyping He) as [Q [T1 [T2 [H1 Hrel]]]].
    exists Q, T1, T2. split; [exact H1|].
    destruct Hrel as [Heq|Hsub].
    + subst S. right. exact H0.
    + right. apply (subqtype_trans E T2 S T Hsub H0).
  - inversion He; subst. exists Q, T1, T2. split; [exact H|]. left. reflexivity.
Qed.

Lemma typing_upqual_inv_gen : forall E P e T,
  typing E (exp_upqual P e) T ->
  exists Q T0,
    typing E e (qtyp_qtyp Q T0) /\ subqual E Q P /\
    (T = qtyp_qtyp P T0 \/ subqtype E (qtyp_qtyp P T0) T).
Proof.
  intros E P e T H.
  remember (exp_upqual P e) as e0 eqn:He.
  dependent induction H; try discriminate.
  - destruct (IHtyping He) as [Q [T0 [H1 [Hsub Hrel]]]].
    exists Q, T0. split; [exact H1|]. split; [exact Hsub|].
    destruct Hrel as [Heq|Hsubq].
    + subst S. right. exact H0.
    + right. apply (subqtype_trans E (qtyp_qtyp P T0) S T Hsubq H0).
  - inversion He; subst. exists Q, T. split; [exact H|]. split; [exact H0|].
    left. reflexivity.
Qed.

Lemma typing_check_inv_gen : forall E P e T,
  typing E (exp_check P e) T ->
  exists Q T0,
    typing E e (qtyp_qtyp Q T0) /\ subqual E Q P /\
    (T = qtyp_qtyp Q T0 \/ subqtype E (qtyp_qtyp Q T0) T).
Proof.
  intros E P e T H.
  remember (exp_check P e) as e0 eqn:He.
  dependent induction H; try discriminate.
  - destruct (IHtyping He) as [Q [T0 [H1 [Hsub Hrel]]]].
    exists Q, T0. split; [exact H1|]. split; [exact Hsub|].
    destruct Hrel as [Heq|Hsubq].
    + subst S. right. exact H0.
    + right. apply (subqtype_trans E (qtyp_qtyp Q T0) S T Hsubq H0).
  - inversion He; subst. exists Q, T. split; [exact H|]. split; [exact H0|].
    left. reflexivity.
Qed.


(* ================================================================== *)
(* Preservation                                                      *)
(* ================================================================== *)
Lemma typing_rel : forall E e S T,
  typing E e S -> (T = S \/ subqtype E S T) -> typing E e T.
Proof.
  intros E e S T Hty Hrel.
  destruct Hrel as [Heq|Hsub].
  - subst. exact Hty.
  - exact (typing_sub S E e T Hty Hsub).
Qed.

Theorem preservation : forall E e e' T,
  typing E e T ->
  red e e' ->
  typing E e' T.
Proof.
  intros E e e' T Hty Hred. revert T Hty.
  induction Hred; intros Tres Hty.
  - (* red_app_1 *) destruct (typing_app_inv_gen E e1 e2 Tres Hty) as [Q [T1 [T2 [H1 [H2 Hrel]]]]].
    pose proof (IHHred _ H1) as H1'.
    exact (typing_rel E (exp_app e1' e2) T2 Tres (typing_app Q T1 E e1' e2 T2 H1' H2) Hrel).
  - (* red_app_2 *) destruct (typing_app_inv_gen E e1 e2 Tres Hty) as [Q [T1 [T2 [H1 [H2 Hrel]]]]].
    pose proof (IHHred _ H2) as H2'.
    exact (typing_rel E (exp_app e1 e2') T2 Tres (typing_app Q T1 E e1 e2' T2 H1 H2') Hrel).
  - (* red_tapp *) destruct (typing_tapp_inv_gen E e1 V Tres Hty) as [Q [T1 [T2 [H1 [Hsub Hrel]]]]].
    pose proof (IHHred _ H1) as H1'.
    exact (typing_rel E (exp_tapp e1' V) (open_tqt T2 V) Tres
             (typing_tapp Q T1 E e1' V T2 H1' Hsub) Hrel).
  - (* red_qapp *) destruct (typing_qapp_inv_gen E e1 R Tres Hty) as [Q [Q1 [T1 [H1 [Hsub Hrel]]]]].
    pose proof (IHHred _ H1) as H1'.
    exact (typing_rel E (exp_qapp e1' R) (open_qqt T1 R) Tres
             (typing_qapp Q R E e1' Q1 T1 H1' Hsub) Hrel).
  - (* red_abs *) destruct (typing_app_inv_gen E (exp_abs P T e1) v2 Tres Hty)
      as [Q [T1 [T2 [H1 [H2 HrelApp]]]]].
    destruct (typing_abs_inv_gen E P T e1 (qtyp_qtyp Q (typ_arrow T1 T2)) H1)
      as [bodyTy [L [Hq [Hbody HrelAbs]]]].
    destruct (atom_fresh (union L (fv_exp e1))) as [x Hx].
    assert (HxL : x `notin` L) by (simpl in Hx; fsetdec).
    assert (Hxf : x `notin` fv_exp e1) by (simpl in Hx; fsetdec).
    pose proof (typing_expr E v2 T1 H2) as Hexpr.
    destruct HrelAbs as [Heq|Hbase].
    + inversion Heq; subst.
      pose proof (typing_subst_ee E x v2 T (open_ee e1 x) bodyTy H2 (Hbody x HxL)) as Hres.
      change (typing E (subst_ee x v2 (open_ee_rec 0 (exp_fvar x) e1)) bodyTy) in Hres.
      rewrite (subst_ee_open_ee_self_gen e1 0 x v2 Hxf Hexpr) in Hres.
      exact (typing_rel E (open_ee e1 v2) bodyTy Tres Hres HrelApp).
    + destruct (subqtype_inv_comp E P (typ_arrow T bodyTy) Q (typ_arrow T1 T2) Hbase)
        as [Hqual HsubArr].
      destruct (sub_arrow_inv_comp E T bodyTy T1 T2 HsubArr) as [HsubT HsubBody].
      pose proof (typing_sub T1 E v2 T H2 HsubT) as H2V.
      pose proof (typing_subst_ee E x v2 T (open_ee e1 x) bodyTy H2V (Hbody x HxL)) as Hres.
      change (typing E (subst_ee x v2 (open_ee_rec 0 (exp_fvar x) e1)) bodyTy) in Hres.
      rewrite (subst_ee_open_ee_self_gen e1 0 x v2 Hxf Hexpr) in Hres.
      pose proof (typing_sub bodyTy E (open_ee e1 v2) T2 Hres HsubBody) as Hres2.
      exact (typing_rel E (open_ee e1 v2) T2 Tres Hres2 HrelApp).
  - (* red_tabs *) destruct (typing_tapp_inv_gen E (exp_tabs P T1 e1) T2 Tres Hty)
      as [Q [S1 [S2 [H1 [Hsub HrelApp]]]]].
    destruct (typing_tabs_inv_gen E P T1 e1 (qtyp_qtyp Q (typ_all S1 S2)) H1)
      as [bodyTy [L [Hq [Hbody HrelTabs]]]].
    destruct (sub_wf E T2 S1 Hsub) as [_ [HWV _]].
    pose proof (wf_typ_type E T2 HWV) as HtypeV.
    destruct HrelTabs as [Heq|Hbase].
    + inversion Heq; subst.
      destruct (atom_fresh (union L (union (fv_exp e1) (fv_qtyp bodyTy)))) as [X HX].
      assert (HXL : X `notin` L) by (simpl in HX; fsetdec).
      assert (HXe : X `notin` fv_exp e1) by (simpl in HX; fsetdec).
      assert (HXb : X `notin` fv_qtyp bodyTy) by (simpl in HX; fsetdec).
      pose proof (typing_subst_te E X T2 T1 (open_te e1 X) (open_tqt bodyTy X) Hsub (Hbody X HXL)) as Hres.
      change (typing E (subst_te X T2 (open_te_rec 0 (typ_fvar X) e1))
                (subst_tqt X T2 (open_tqt_rec 0 (typ_fvar X) bodyTy))) in Hres.
      rewrite (subst_te_open_te_self_gen e1 0 X T2 HXe HtypeV) in Hres.
      rewrite (subst_tqt_open_tqt_self_gen bodyTy 0 X T2 HXb HtypeV) in Hres.
      exact (typing_rel E (open_te e1 T2) (open_tqt bodyTy T2) Tres Hres HrelApp).
    + destruct (subqtype_inv_comp E P (typ_all T1 bodyTy) Q (typ_all S1 S2) Hbase)
        as [Hqual HsubAll].
      destruct (sub_all_inv_comp E T1 bodyTy S1 S2 HsubAll) as [L2 [HsubHead HbodySub]].
      destruct (atom_fresh (union L (union L2 (union (fv_exp e1) (union (fv_qtyp bodyTy) (fv_qtyp S2))))))
        as [X HX].
      assert (HXL : X `notin` L) by (simpl in HX; fsetdec).
      assert (HXL2 : X `notin` L2) by (simpl in HX; fsetdec).
      assert (HXe : X `notin` fv_exp e1) by (simpl in HX; fsetdec).
      assert (HXb : X `notin` fv_qtyp bodyTy) by (simpl in HX; fsetdec).
      assert (HX2 : X `notin` fv_qtyp S2) by (simpl in HX; fsetdec).
      pose proof (sub_trans E T2 S1 T1 Hsub HsubHead) as HsubTa.
      pose proof (typing_subst_te E X T2 T1 (open_te e1 X) (open_tqt bodyTy X) HsubTa (Hbody X HXL)) as Hres.
      change (typing E (subst_te X T2 (open_te_rec 0 (typ_fvar X) e1))
                (subst_tqt X T2 (open_tqt_rec 0 (typ_fvar X) bodyTy))) in Hres.
      rewrite (subst_te_open_te_self_gen e1 0 X T2 HXe HtypeV) in Hres.
      rewrite (subst_tqt_open_tqt_self_gen bodyTy 0 X T2 HXb HtypeV) in Hres.
      pose proof (subqtype_te_subst E X T2 S1 (open_tqt bodyTy X) (open_tqt S2 X)
                    Hsub (HbodySub X HXL2)) as HsubBody.
      change (subqtype E (subst_tqt X T2 (open_tqt_rec 0 (typ_fvar X) bodyTy))
                (subst_tqt X T2 (open_tqt_rec 0 (typ_fvar X) S2))) in HsubBody.
      rewrite (subst_tqt_open_tqt_self_gen bodyTy 0 X T2 HXb HtypeV) in HsubBody.
      rewrite (subst_tqt_open_tqt_self_gen S2 0 X T2 HX2 HtypeV) in HsubBody.
      pose proof (typing_sub (open_tqt bodyTy T2) E (open_te e1 T2) (open_tqt S2 T2)
                    Hres HsubBody) as Hres2.
      exact (typing_rel E (open_te e1 T2) (open_tqt S2 T2) Tres Hres2 HrelApp).
  - (* red_qabs *) destruct (typing_qapp_inv_gen E (exp_qabs P Q1 e1) Q2 Tres Hty)
      as [R [R1 [T1 [H1 [Hsub HrelApp]]]]].
    destruct (typing_qabs_inv_gen E P Q1 e1 (qtyp_qtyp R (typ_qall R1 T1)) H1)
      as [bodyTy [L [Hq [Hbody HrelAbs]]]].
    destruct (subqual_wf E Q2 R1 Hsub) as [HQ2 _].
    pose proof (wf_qua_qual E Q2 HQ2) as HqualQ2.
    destruct HrelAbs as [Heq|Hbase].
    + inversion Heq; subst.
      destruct (atom_fresh (union L (union (fv_exp e1) (fv_qtyp bodyTy)))) as [X HX].
      assert (HXL : X `notin` L) by (simpl in HX; fsetdec).
      assert (HXe : X `notin` fv_exp e1) by (simpl in HX; fsetdec).
      assert (HXb : X `notin` fv_qtyp bodyTy) by (simpl in HX; fsetdec).
      pose proof (typing_subst_qe E X Q2 Q1 (open_qe e1 X) (open_qqt bodyTy X) Hsub (Hbody X HXL)) as Hres.
      change (typing E (subst_qe X Q2 (open_qe_rec 0 (qua_fvar X) e1))
                (subst_qqt X Q2 (open_qqt_rec 0 (qua_fvar X) bodyTy))) in Hres.
      rewrite (subst_qe_open_qe_self_gen e1 0 X Q2 HXe HqualQ2) in Hres.
      rewrite (subst_qqt_open_qqt_self_gen bodyTy 0 X Q2 HXb HqualQ2) in Hres.
      exact (typing_rel E (open_qe e1 Q2) (open_qqt bodyTy Q2) Tres Hres HrelApp).
    + destruct (subqtype_inv_comp E P (typ_qall Q1 bodyTy) R (typ_qall R1 T1) Hbase)
        as [Hqual HsubAll].
      destruct (sub_qall_inv_comp E Q1 bodyTy R1 T1 HsubAll) as [L2 [HsubHead HbodySub]].
      destruct (atom_fresh (union L (union L2 (union (fv_exp e1) (union (fv_qtyp bodyTy) (fv_qtyp T1))))))
        as [X HX].
      assert (HXL : X `notin` L) by (simpl in HX; fsetdec).
      assert (HXL2 : X `notin` L2) by (simpl in HX; fsetdec).
      assert (HXe : X `notin` fv_exp e1) by (simpl in HX; fsetdec).
      assert (HXb : X `notin` fv_qtyp bodyTy) by (simpl in HX; fsetdec).
      assert (HX1 : X `notin` fv_qtyp T1) by (simpl in HX; fsetdec).
      pose proof (subqual_trans E Q2 R1 Q1 Hsub HsubHead) as HsubQ1.
      pose proof (typing_subst_qe E X Q2 Q1 (open_qe e1 X) (open_qqt bodyTy X) HsubQ1 (Hbody X HXL)) as Hres.
      change (typing E (subst_qe X Q2 (open_qe_rec 0 (qua_fvar X) e1))
                (subst_qqt X Q2 (open_qqt_rec 0 (qua_fvar X) bodyTy))) in Hres.
      rewrite (subst_qe_open_qe_self_gen e1 0 X Q2 HXe HqualQ2) in Hres.
      rewrite (subst_qqt_open_qqt_self_gen bodyTy 0 X Q2 HXb HqualQ2) in Hres.
      pose proof (subqtype_qt_subst_gen (@nil (atom * binding)) E X Q2 R1
                    (open_qqt bodyTy X) (open_qqt T1 X) Hsub (HbodySub X HXL2)) as HsubBody.
      change (subqtype E (subst_qqt X Q2 (open_qqt_rec 0 (qua_fvar X) bodyTy))
                (subst_qqt X Q2 (open_qqt_rec 0 (qua_fvar X) T1))) in HsubBody.
      rewrite (subst_qqt_open_qqt_self_gen bodyTy 0 X Q2 HXb HqualQ2) in HsubBody.
      rewrite (subst_qqt_open_qqt_self_gen T1 0 X Q2 HX1 HqualQ2) in HsubBody.
      pose proof (typing_sub (open_qqt bodyTy Q2) E (open_qe e1 Q2) (open_qqt T1 Q2)
                    Hres HsubBody) as Hres2.
      exact (typing_rel E (open_qe e1 Q2) (open_qqt T1 Q2) Tres Hres2 HrelApp).
  - (* red_let_1 *) destruct (typing_let_inv_gen E e1 e2 Tres Hty)
      as [T1 [T2 [L [H1 [Hbody Hrel]]]]].
    pose proof (IHHred _ H1) as H1'.
    exact (typing_rel E (exp_let e1' e2) T2 Tres
             (typing_let L T1 T2 e1' e2 E H1' Hbody) Hrel).
  - (* red_let *) destruct (typing_let_inv_gen E v1 e2 Tres Hty)
      as [T1 [T2 [L [H1 [Hbody Hrel]]]]].
    destruct (atom_fresh (union L (fv_exp e2))) as [x Hx].
    assert (HxL : x `notin` L) by (simpl in Hx; fsetdec).
    assert (Hxf : x `notin` fv_exp e2) by (simpl in Hx; fsetdec).
    pose proof (typing_expr E v1 T1 H1) as Hexpr.
    pose proof (typing_subst_ee E x v1 T1 (open_ee e2 x) T2 H1 (Hbody x HxL)) as Hres.
    change (typing E (subst_ee x v1 (open_ee_rec 0 (exp_fvar x) e2)) T2) in Hres.
    rewrite (subst_ee_open_ee_self_gen e2 0 x v1 Hxf Hexpr) in Hres.
    exact (typing_rel E (open_ee e2 v1) T2 Tres Hres Hrel).
  - (* red_inl_1 *) destruct (typing_inl_inv_gen E P e1 Tres Hty)
      as [V1 [V2 [Hq [H1 [Hwf Hrel]]]]].
    pose proof (IHHred _ H1) as H1'.
    exact (typing_rel E (exp_inl P e1') (qtyp_qtyp P (typ_sum V1 V2)) Tres
             (typing_inl P V1 V2 e1' E Hq H1' Hwf) Hrel).
  - (* red_inr_1 *) destruct (typing_inr_inv_gen E P e1 Tres Hty)
      as [V1 [V2 [Hq [H1 [Hwf Hrel]]]]].
    pose proof (IHHred _ H1) as H1'.
    exact (typing_rel E (exp_inr P e1') (qtyp_qtyp P (typ_sum V1 V2)) Tres
             (typing_inr P V1 V2 e1' E Hq H1' Hwf) Hrel).
  - (* red_case_1 *) destruct (typing_case_inv_gen E e1 e2 e3 Tres Hty)
      as [Q [T1 [T2 [Tb [L [H1 [Hb2 [Hb3 Hrel]]]]]]]].
    pose proof (IHHred _ H1) as H1'.
    exact (typing_rel E (exp_case e1' e2 e3) Tb Tres
             (typing_case L Q T1 T2 Tb e1' e2 e3 E H1' Hb2 Hb3) Hrel).
  - (* red_case_inl *) destruct (typing_case_inv_gen E (exp_inl P v1) e2 e3 Tres Hty)
      as [Q [S1 [S2 [Tb [L [HTc [Hb2 [Hb3 Hrel]]]]]]]].
    destruct (typing_inl_inv_gen E P v1 (qtyp_qtyp Q (typ_sum S1 S2)) HTc)
      as [V1 [V2 [Hq [Hv1 [Hwf HrelInl]]]]].
    assert (Hv1T1 : typing E v1 S1).
    { destruct HrelInl as [Heq|Hbase].
      - inversion Heq; subst. exact Hv1.
      - destruct (subqtype_inv_comp E P (typ_sum V1 V2) Q (typ_sum S1 S2) Hbase)
          as [Hqual HsubSum].
        destruct (sub_sum_inv_comp E V1 V2 S1 S2 HsubSum) as [Hsub1 _].
        exact (typing_sub V1 E v1 S1 Hv1 Hsub1). }
    destruct (atom_fresh (union L (fv_exp e2))) as [x Hx].
    assert (HxL : x `notin` L) by (simpl in Hx; fsetdec).
    assert (Hxf : x `notin` fv_exp e2) by (simpl in Hx; fsetdec).
    pose proof (typing_expr E v1 V1 Hv1) as Hexpr.
    pose proof (typing_subst_ee E x v1 S1 (open_ee e2 x) Tb Hv1T1 (Hb2 x HxL)) as Hres.
    change (typing E (subst_ee x v1 (open_ee_rec 0 (exp_fvar x) e2)) Tb) in Hres.
    rewrite (subst_ee_open_ee_self_gen e2 0 x v1 Hxf Hexpr) in Hres.
    exact (typing_rel E (open_ee e2 v1) Tb Tres Hres Hrel).
  - (* red_case_inr *) destruct (typing_case_inv_gen E (exp_inr P v1) e2 e3 Tres Hty)
      as [Q [S1 [S2 [Tb [L [HTc [Hb2 [Hb3 Hrel]]]]]]]].
    destruct (typing_inr_inv_gen E P v1 (qtyp_qtyp Q (typ_sum S1 S2)) HTc)
      as [V1 [V2 [Hq [Hv1 [Hwf HrelInr]]]]].
    assert (Hv1T2 : typing E v1 S2).
    { destruct HrelInr as [Heq|Hbase].
      - inversion Heq; subst. exact Hv1.
      - destruct (subqtype_inv_comp E P (typ_sum V1 V2) Q (typ_sum S1 S2) Hbase)
          as [Hqual HsubSum].
        destruct (sub_sum_inv_comp E V1 V2 S1 S2 HsubSum) as [_ Hsub2].
        exact (typing_sub V2 E v1 S2 Hv1 Hsub2). }
    destruct (atom_fresh (union L (fv_exp e3))) as [x Hx].
    assert (HxL : x `notin` L) by (simpl in Hx; fsetdec).
    assert (Hxf : x `notin` fv_exp e3) by (simpl in Hx; fsetdec).
    pose proof (typing_expr E v1 V2 Hv1) as Hexpr.
    pose proof (typing_subst_ee E x v1 S2 (open_ee e3 x) Tb Hv1T2 (Hb3 x HxL)) as Hres.
    change (typing E (subst_ee x v1 (open_ee_rec 0 (exp_fvar x) e3)) Tb) in Hres.
    rewrite (subst_ee_open_ee_self_gen e3 0 x v1 Hxf Hexpr) in Hres.
    exact (typing_rel E (open_ee e3 v1) Tb Tres Hres Hrel).
  - (* red_pair_1 *) destruct (typing_pair_inv_gen E P e1 e2 Tres Hty)
      as [V1 [V2 [Hq [H1 [H2 Hrel]]]]].
    pose proof (IHHred _ H1) as H1'.
    exact (typing_rel E (exp_pair P e1' e2) (qtyp_qtyp P (typ_pair V1 V2)) Tres
             (typing_pair P V1 V2 e1' e2 E Hq H1' H2) Hrel).
  - (* red_pair_2 *) destruct (typing_pair_inv_gen E P v1 e2 Tres Hty)
      as [V1 [V2 [Hq [H1 [H2 Hrel]]]]].
    pose proof (IHHred _ H2) as H2'.
    exact (typing_rel E (exp_pair P v1 e2') (qtyp_qtyp P (typ_pair V1 V2)) Tres
             (typing_pair P V1 V2 v1 e2' E Hq H1 H2') Hrel).
  - (* red_pair_first_1 *) destruct (typing_first_inv_gen E e1 Tres Hty)
      as [Q [T1 [T2 [H1 Hrel]]]].
    pose proof (IHHred _ H1) as H1'.
    exact (typing_rel E (exp_first e1') T1 Tres (typing_first Q T1 T2 e1' E H1') Hrel).
  - (* red_pair_second_1 *) destruct (typing_second_inv_gen E e1 Tres Hty)
      as [Q [T1 [T2 [H1 Hrel]]]].
    pose proof (IHHred _ H1) as H1'.
    exact (typing_rel E (exp_second e1') T2 Tres (typing_second Q T1 T2 e1' E H1') Hrel).
  - (* red_pair_first_2 *) destruct (typing_first_inv_gen E (exp_pair P v1 v2) Tres Hty)
      as [Q [T1 [T2 [HTyP HrelFirst]]]].
    destruct (typing_pair_inv_gen E P v1 v2 (qtyp_qtyp Q (typ_pair T1 T2)) HTyP)
      as [V1 [V2 [Hq [Hv1 [Hv2 HrelPair]]]]].
    assert (Hv1T1 : typing E v1 T1).
    { destruct HrelPair as [Heq|Hbase].
      - inversion Heq; subst. exact Hv1.
      - destruct (subqtype_inv_comp E P (typ_pair V1 V2) Q (typ_pair T1 T2) Hbase)
          as [Hqual HsubPair].
        destruct (sub_pair_inv_comp E V1 V2 T1 T2 HsubPair) as [Hsub1 _].
        exact (typing_sub V1 E v1 T1 Hv1 Hsub1). }
    exact (typing_rel E v1 T1 Tres Hv1T1 HrelFirst).
  - (* red_pair_second_2 *) destruct (typing_second_inv_gen E (exp_pair P v1 v2) Tres Hty)
      as [Q [T1 [T2 [HTyP HrelSecond]]]].
    destruct (typing_pair_inv_gen E P v1 v2 (qtyp_qtyp Q (typ_pair T1 T2)) HTyP)
      as [V1 [V2 [Hq [Hv1 [Hv2 HrelPair]]]]].
    assert (Hv2T2 : typing E v2 T2).
    { destruct HrelPair as [Heq|Hbase].
      - inversion Heq; subst. exact Hv2.
      - destruct (subqtype_inv_comp E P (typ_pair V1 V2) Q (typ_pair T1 T2) Hbase)
          as [Hqual HsubPair].
        destruct (sub_pair_inv_comp E V1 V2 T1 T2 HsubPair) as [_ Hsub2].
        exact (typing_sub V2 E v2 T2 Hv2 Hsub2). }
    exact (typing_rel E v2 T2 Tres Hv2T2 HrelSecond).
  - (* red_upqual_1 *) destruct (typing_upqual_inv_gen E P e1 Tres Hty)
      as [Q [T0 [H1 [Hsub Hrel]]]].
    pose proof (IHHred _ H1) as H1'.
    exact (typing_rel E (exp_upqual P e1') (qtyp_qtyp P T0) Tres
             (typing_upqual E Q T0 P e1' H1' Hsub) Hrel).
  - (* red_upqual_abs *) destruct (typing_upqual_inv_gen E P (exp_abs Q V e1) Tres Hty)
      as [R [T0 [HTyOp [Hsub HrelUp]]]].
    destruct (typing_abs_inv_gen E Q V e1 (qtyp_qtyp R T0) HTyOp)
      as [bodyTy [L [Hq [Hbody HrelAbs]]]].
    destruct (subqual_wf E R P Hsub) as [_ HP].
    assert (HwfE : wf_env E) by (apply (typing_wf_env _ _ _ HTyOp)).
    assert (Hres : typing E (exp_abs P V e1) (qtyp_qtyp P T0)).
    { destruct HrelAbs as [Heq|Hbase].
      - inversion Heq; subst. apply (typing_abs L E P V e1 bodyTy HP Hbody).
      - destruct (subqtype_inv_comp E Q (typ_arrow V bodyTy) R T0 Hbase) as [Hqual HsubArrow].
        pose proof (typing_abs L E P V e1 bodyTy HP Hbody) as HbaseTy.
        apply (typing_sub (qtyp_qtyp P (typ_arrow V bodyTy)) E (exp_abs P V e1) (qtyp_qtyp P T0) HbaseTy).
        apply sub_qtyp_qtyp.
        + apply (subqual_refl E P HwfE HP).
        + exact HsubArrow. }
    exact (typing_rel E (exp_abs P V e1) (qtyp_qtyp P T0) Tres Hres HrelUp).
  - (* red_upqual_tabs *) destruct (typing_upqual_inv_gen E P (exp_tabs Q V e1) Tres Hty)
      as [R [T0 [HTyOp [Hsub HrelUp]]]].
    destruct (typing_tabs_inv_gen E Q V e1 (qtyp_qtyp R T0) HTyOp)
      as [bodyTy [L [Hq [Hbody HrelAbs]]]].
    destruct (subqual_wf E R P Hsub) as [_ HP].
    assert (HwfE : wf_env E) by (apply (typing_wf_env _ _ _ HTyOp)).
    assert (Hres : typing E (exp_tabs P V e1) (qtyp_qtyp P T0)).
    { destruct HrelAbs as [Heq|Hbase].
      - inversion Heq; subst. apply (typing_tabs L P E V e1 bodyTy HP Hbody).
      - destruct (subqtype_inv_comp E Q (typ_all V bodyTy) R T0 Hbase) as [Hqual HsubAll].
        pose proof (typing_tabs L P E V e1 bodyTy HP Hbody) as HbaseTy.
        apply (typing_sub (qtyp_qtyp P (typ_all V bodyTy)) E (exp_tabs P V e1) (qtyp_qtyp P T0) HbaseTy).
        apply sub_qtyp_qtyp.
        + apply (subqual_refl E P HwfE HP).
        + exact HsubAll. }
    exact (typing_rel E (exp_tabs P V e1) (qtyp_qtyp P T0) Tres Hres HrelUp).
  - (* red_upqual_qabs *) destruct (typing_upqual_inv_gen E P (exp_qabs Q V e1) Tres Hty)
      as [R [T0 [HTyOp [Hsub HrelUp]]]].
    destruct (typing_qabs_inv_gen E Q V e1 (qtyp_qtyp R T0) HTyOp)
      as [bodyTy [L [Hq [Hbody HrelAbs]]]].
    destruct (subqual_wf E R P Hsub) as [_ HP].
    assert (HwfE : wf_env E) by (apply (typing_wf_env _ _ _ HTyOp)).
    assert (Hres : typing E (exp_qabs P V e1) (qtyp_qtyp P T0)).
    { destruct HrelAbs as [Heq|Hbase].
      - inversion Heq; subst. apply (typing_qabs L E P V e1 bodyTy HP Hbody).
      - destruct (subqtype_inv_comp E Q (typ_qall V bodyTy) R T0 Hbase) as [Hqual HsubAll].
        pose proof (typing_qabs L E P V e1 bodyTy HP Hbody) as HbaseTy.
        apply (typing_sub (qtyp_qtyp P (typ_qall V bodyTy)) E (exp_qabs P V e1) (qtyp_qtyp P T0) HbaseTy).
        apply sub_qtyp_qtyp.
        + apply (subqual_refl E P HwfE HP).
        + exact HsubAll. }
    exact (typing_rel E (exp_qabs P V e1) (qtyp_qtyp P T0) Tres Hres HrelUp).
  - (* red_upqual_inl *) destruct (typing_upqual_inv_gen E P (exp_inl Q e1) Tres Hty)
      as [R [T0 [HTyOp [Hsub HrelUp]]]].
    destruct (typing_inl_inv_gen E Q e1 (qtyp_qtyp R T0) HTyOp)
      as [V1 [V2 [Hq [Hval [Hwf HrelInl]]]]].
    destruct (subqual_wf E R P Hsub) as [_ HP].
    assert (HwfE : wf_env E) by (apply (typing_wf_env _ _ _ HTyOp)).
    assert (Hres : typing E (exp_inl P e1) (qtyp_qtyp P T0)).
    { destruct HrelInl as [Heq|Hbase].
      - inversion Heq; subst. apply (typing_inl P V1 V2 e1 E HP Hval Hwf).
      - destruct (subqtype_inv_comp E Q (typ_sum V1 V2) R T0 Hbase) as [Hqual HsubSum].
        pose proof (typing_inl P V1 V2 e1 E HP Hval Hwf) as HbaseTy.
        apply (typing_sub (qtyp_qtyp P (typ_sum V1 V2)) E (exp_inl P e1) (qtyp_qtyp P T0) HbaseTy).
        apply sub_qtyp_qtyp.
        + apply (subqual_refl E P HwfE HP).
        + exact HsubSum. }
    exact (typing_rel E (exp_inl P e1) (qtyp_qtyp P T0) Tres Hres HrelUp).
  - (* red_upqual_inr *) destruct (typing_upqual_inv_gen E P (exp_inr Q e1) Tres Hty)
      as [R [T0 [HTyOp [Hsub HrelUp]]]].
    destruct (typing_inr_inv_gen E Q e1 (qtyp_qtyp R T0) HTyOp)
      as [V1 [V2 [Hq [Hval [Hwf HrelInr]]]]].
    destruct (subqual_wf E R P Hsub) as [_ HP].
    assert (HwfE : wf_env E) by (apply (typing_wf_env _ _ _ HTyOp)).
    assert (Hres : typing E (exp_inr P e1) (qtyp_qtyp P T0)).
    { destruct HrelInr as [Heq|Hbase].
      - inversion Heq; subst. apply (typing_inr P V1 V2 e1 E HP Hval Hwf).
      - destruct (subqtype_inv_comp E Q (typ_sum V1 V2) R T0 Hbase) as [Hqual HsubSum].
        pose proof (typing_inr P V1 V2 e1 E HP Hval Hwf) as HbaseTy.
        apply (typing_sub (qtyp_qtyp P (typ_sum V1 V2)) E (exp_inr P e1) (qtyp_qtyp P T0) HbaseTy).
        apply sub_qtyp_qtyp.
        + apply (subqual_refl E P HwfE HP).
        + exact HsubSum. }
    exact (typing_rel E (exp_inr P e1) (qtyp_qtyp P T0) Tres Hres HrelUp).
  - (* red_upqual_pair *) destruct (typing_upqual_inv_gen E P (exp_pair Q e1 e2) Tres Hty)
      as [R [T0 [HTyOp [Hsub HrelUp]]]].
    destruct (typing_pair_inv_gen E Q e1 e2 (qtyp_qtyp R T0) HTyOp)
      as [V1 [V2 [Hq [Hv1 [Hv2 HrelPair]]]]].
    destruct (subqual_wf E R P Hsub) as [_ HP].
    assert (HwfE : wf_env E) by (apply (typing_wf_env _ _ _ HTyOp)).
    assert (Hres : typing E (exp_pair P e1 e2) (qtyp_qtyp P T0)).
    { destruct HrelPair as [Heq|Hbase].
      - inversion Heq; subst. apply (typing_pair P V1 V2 e1 e2 E HP Hv1 Hv2).
      - destruct (subqtype_inv_comp E Q (typ_pair V1 V2) R T0 Hbase) as [Hqual HsubPair].
        pose proof (typing_pair P V1 V2 e1 e2 E HP Hv1 Hv2) as HbaseTy.
        apply (typing_sub (qtyp_qtyp P (typ_pair V1 V2)) E (exp_pair P e1 e2) (qtyp_qtyp P T0) HbaseTy).
        apply sub_qtyp_qtyp.
        + apply (subqual_refl E P HwfE HP).
        + exact HsubPair. }
    exact (typing_rel E (exp_pair P e1 e2) (qtyp_qtyp P T0) Tres Hres HrelUp).
  - (* red_check_1 *) destruct (typing_check_inv_gen E P e1 Tres Hty)
      as [Q [T0 [H1 [Hsub Hrel]]]].
    pose proof (IHHred _ H1) as H1'.
    exact (typing_rel E (exp_check P e1') (qtyp_qtyp Q T0) Tres
             (typing_check E Q T0 P e1' H1' Hsub) Hrel).
  - (* red_check_abs *) destruct (typing_check_inv_gen E P (exp_abs Q V e1) Tres Hty)
      as [R [T0 [HTyOp [Hsub Hrel]]]].
    exact (typing_rel E (exp_abs Q V e1) (qtyp_qtyp R T0) Tres HTyOp Hrel).
  - (* red_check_tabs *) destruct (typing_check_inv_gen E P (exp_tabs Q V e1) Tres Hty)
      as [R [T0 [HTyOp [Hsub Hrel]]]].
    exact (typing_rel E (exp_tabs Q V e1) (qtyp_qtyp R T0) Tres HTyOp Hrel).
  - (* red_check_qabs *) destruct (typing_check_inv_gen E P (exp_qabs Q V e1) Tres Hty)
      as [R [T0 [HTyOp [Hsub Hrel]]]].
    exact (typing_rel E (exp_qabs Q V e1) (qtyp_qtyp R T0) Tres HTyOp Hrel).
  - (* red_check_inl *) destruct (typing_check_inv_gen E P (exp_inl Q e1) Tres Hty)
      as [R [T0 [HTyOp [Hsub Hrel]]]].
    exact (typing_rel E (exp_inl Q e1) (qtyp_qtyp R T0) Tres HTyOp Hrel).
  - (* red_check_inr *) destruct (typing_check_inv_gen E P (exp_inr Q e1) Tres Hty)
      as [R [T0 [HTyOp [Hsub Hrel]]]].
    exact (typing_rel E (exp_inr Q e1) (qtyp_qtyp R T0) Tres HTyOp Hrel).
  - (* red_check_pair *) destruct (typing_check_inv_gen E P (exp_pair Q e1 e2) Tres Hty)
      as [R [T0 [HTyOp [Hsub Hrel]]]].
    exact (typing_rel E (exp_pair Q e1 e2) (qtyp_qtyp R T0) Tres HTyOp Hrel).
Qed.

Theorem progress : forall e T,
  typing empty e T ->
  value e \/ exists e', red e e'.
Proof.
  intros e T H. dependent induction H.
  - apply binds_nil_iff in H0. contradiction.
  - left. apply value_abs. apply (expr_abs L P V e1).
    + apply (wf_qua_qual empty P); exact H.
    + destruct (atom_fresh L) as [x Hx].
      apply (wf_qtyp_qtype empty V).
      apply (wf_env_typ_head x V empty).
      apply (typing_wf_env (x ~ bind_typ V ++ empty) (open_ee e1 x) T1).
      apply H0; exact Hx.
    + intros x Hx. apply (typing_expr (x ~ bind_typ V ++ empty) (open_ee e1 x) T1).
      apply H0; exact Hx.
  - destruct (IHtyping1 eq_refl) as [Hv1|Hr1];
    destruct (IHtyping2 eq_refl) as [Hv2|Hr2].
    + right. destruct (typing_value_abs empty e1 Q T1 T2 H Hv1) as [P0 [V [body Heq]]].
      subst e1. exists (open_ee body e2). apply red_abs.
      * apply (value_expr (exp_abs P0 V body) Hv1).
      * exact Hv2.
    + right. destruct Hr2 as [e2' Hred]. exists (exp_app e1 e2'). apply red_app_2; auto.
    + right. destruct Hr1 as [e1' Hred]. exists (exp_app e1' e2). apply red_app_1.
      * apply (typing_expr empty e2 T1); exact H0.
      * exact Hred.
    + right. destruct Hr1 as [e1' Hred]. exists (exp_app e1' e2). apply red_app_1.
      * apply (typing_expr empty e2 T1); exact H0.
      * exact Hred.
  - left. apply value_tabs. apply (expr_tabs L P V e1).
    + apply (wf_qua_qual empty P); exact H.
    + destruct (atom_fresh L) as [x Hx].
      apply (wf_typ_type empty V).
      apply (wf_env_sub_head x V empty).
      apply (typing_wf_env (x ~ bind_sub V ++ empty) (open_te e1 x) (open_tqt T1 x)).
      apply H0; exact Hx.
    + intros x Hx. apply (typing_expr (x ~ bind_sub V ++ empty) (open_te e1 x) (open_tqt T1 x)).
      apply H0; exact Hx.
  - destruct (IHtyping eq_refl) as [Hv|Hr].
    + right. destruct (typing_value_tabs empty e1 Q T1 T2 H Hv) as [P0 [V [body Heq]]].
      subst e1. exists (open_te body T). apply red_tabs.
      * apply (value_expr (exp_tabs P0 V body) Hv).
      * apply (wf_typ_type empty T). apply (sub_wf empty T T1); exact H0.
    + right. destruct Hr as [e1' Hred]. exists (exp_tapp e1' T). apply red_tapp.
      * apply (wf_typ_type empty T). apply (sub_wf empty T T1); exact H0.
      * exact Hred.
  - left. apply value_qabs. apply (expr_qabs L P Q e1).
    + apply (wf_qua_qual empty P); exact H.
    + destruct (atom_fresh L) as [x Hx].
      apply (wf_qua_qual empty Q).
      apply (wf_env_qua_head x Q empty).
      apply (typing_wf_env (x ~ bind_qua Q ++ empty) (open_qe e1 x) (open_qqt T1 x)).
      apply H0; exact Hx.
    + intros x Hx. apply (typing_expr (x ~ bind_qua Q ++ empty) (open_qe e1 x) (open_qqt T1 x)).
      apply H0; exact Hx.
  - destruct (IHtyping eq_refl) as [Hv|Hr].
    + right. destruct (typing_value_qabs empty e1 R Q1 T H Hv) as [P0 [Q0 [body Heq]]].
      subst e1. exists (open_qe body Q). apply red_qabs.
      * apply (value_expr (exp_qabs P0 Q0 body) Hv).
      * apply (wf_qua_qual empty Q). apply (subqual_wf empty Q Q1); exact H0.
    + right. destruct Hr as [e1' Hred]. exists (exp_qapp e1' Q). apply red_qapp.
      * apply (wf_qua_qual empty Q). apply (subqual_wf empty Q Q1); exact H0.
      * exact Hred.
  - destruct (IHtyping eq_refl); [left|right]; assumption.
  - destruct (IHtyping eq_refl) as [Hv1|Hr1].
    + right. exists (open_ee e2 e1). apply red_let.
      * exact Hv1.
      * apply (typing_body_e L empty T1 T2 e2); exact H0.
    + right. destruct Hr1 as [e1' Hred]. exists (exp_let e1' e2). apply red_let_1.
      * exact Hred.
      * apply (typing_body_e L empty T1 T2 e2); exact H0.
  - destruct (IHtyping eq_refl) as [Hv|Hr].
    + left. apply value_inl.
      * apply (wf_qua_qual empty P); exact H.
      * exact Hv.
    + right. destruct Hr as [e1' Hred]. exists (exp_inl P e1').
      apply (red_inl_1 P e1 e1').
      * apply (wf_qua_qual empty P); exact H.
      * exact Hred.
  - destruct (IHtyping eq_refl) as [Hv|Hr].
    + left. apply value_inr.
      * apply (wf_qua_qual empty P); exact H.
      * exact Hv.
    + right. destruct Hr as [e1' Hred]. exists (exp_inr P e1').
      apply (red_inr_1 P e1 e1').
      * apply (wf_qua_qual empty P); exact H.
      * exact Hred.
  - destruct (IHtyping eq_refl) as [Hv1|Hr1].
    + destruct (typing_value_sum empty e1 Q T1 T2 H Hv1) as [[P0 [v1 Heq]]|[P0 [v1 Heq]]];
      subst e1; inversion Hv1; subst.
      * right. exists (open_ee e2 v1). apply (red_case_inl P0 v1 e2 e3); auto.
        -- apply (typing_body_e L empty T1 T e2); exact H0.
        -- apply (typing_body_e L empty T2 T e3); exact H2.
      * right. exists (open_ee e3 v1). apply (red_case_inr P0 v1 e2 e3); auto.
        -- apply (typing_body_e L empty T1 T e2); exact H0.
        -- apply (typing_body_e L empty T2 T e3); exact H2.
    + right. destruct Hr1 as [e1' Hred]. exists (exp_case e1' e2 e3).
      apply (red_case_1 e1 e1' e2 e3).
      * exact Hred.
      * apply (typing_body_e L empty T1 T e2); exact H0.
      * apply (typing_body_e L empty T2 T e3); exact H2.
  - destruct (IHtyping1 eq_refl) as [Hv1|Hr1];
    destruct (IHtyping2 eq_refl) as [Hv2|Hr2].
    + left. apply value_pair.
      * apply (wf_qua_qual empty P); exact H.
      * exact Hv1.
      * exact Hv2.
    + right. destruct Hr2 as [e2' Hred]. exists (exp_pair P e1 e2').
      apply (red_pair_2 P e1 e2 e2').
      * apply (wf_qua_qual empty P); exact H.
      * exact Hv1.
      * exact Hred.
    + right. destruct Hr1 as [e1' Hred]. exists (exp_pair P e1' e2).
      apply (red_pair_1 P e1 e1' e2).
      * apply (wf_qua_qual empty P); exact H.
      * exact Hred.
      * apply (typing_expr empty e2 T2); exact H1.
    + right. destruct Hr1 as [e1' Hred]. exists (exp_pair P e1' e2).
      apply (red_pair_1 P e1 e1' e2).
      * apply (wf_qua_qual empty P); exact H.
      * exact Hred.
      * apply (typing_expr empty e2 T2); exact H1.
  - destruct (IHtyping eq_refl) as [Hv|Hr].
    + destruct (typing_value_pair empty e Q T1 T2 H Hv) as [P0 [v1 [v2 Heq]]]; subst e; inversion Hv; subst.
      right. exists v1. apply (red_pair_first_2 P0 v1 v2); auto.
    + right. destruct Hr as [e' Hred]. exists (exp_first e'). apply red_pair_first_1; exact Hred.
  - destruct (IHtyping eq_refl) as [Hv|Hr].
    + destruct (typing_value_pair empty e Q T1 T2 H Hv) as [P0 [v1 [v2 Heq]]]; subst e; inversion Hv; subst.
      right. exists v2. apply (red_pair_second_2 P0 v1 v2); auto.
    + right. destruct Hr as [e' Hred]. exists (exp_second e'). apply red_pair_second_1; exact Hred.
  - destruct (IHtyping eq_refl) as [Hv|Hr].
    + destruct (subqual_wf empty Q P H0) as [HQ HP].
      destruct (concretize_wf_empty Q HQ) as [cQ HcQ].
      destruct (concretize_wf_empty P HP) as [cP HcP].
      assert (Hexpr : expr e) by (apply value_expr; exact Hv).
      destruct Hv.
      { (* abs *) assert (Hsub0 : subqual empty P0 Q) by (apply (typing_abs_qual_le empty P0 T0 e1 Q T); exact H).
        destruct (subqual_wf empty P0 Q Hsub0) as [HP0 _].
        destruct (concretize_wf_empty P0 HP0) as [cP0 HcP0].
        assert (Hord : cP0 ≤ cP) by
          (eapply subqual_concretize_ord; [exact (subqual_trans empty P0 Q P Hsub0 H0)|exact HcP0|exact HcP]).
        right. exists (exp_abs P T0 e1).
        apply (red_upqual_abs P P0 cP cP0 T0 e1).
        - apply (wf_qua_qual empty P); exact HP.
        - apply (wf_qua_qual empty P0); exact HP0.
        - exact Hexpr.
        - exact HcP.
        - exact HcP0.
        - exact Hord. }
      { (* tabs *) assert (Hsub0 : subqual empty P0 Q) by (apply (typing_tabs_qual_le empty P0 T0 e1 Q T); exact H).
        destruct (subqual_wf empty P0 Q Hsub0) as [HP0 _].
        destruct (concretize_wf_empty P0 HP0) as [cP0 HcP0].
        assert (Hord : cP0 ≤ cP) by
          (eapply subqual_concretize_ord; [exact (subqual_trans empty P0 Q P Hsub0 H0)|exact HcP0|exact HcP]).
        right. exists (exp_tabs P T0 e1).
        apply (red_upqual_tabs P P0 cP cP0 T0 e1).
        - apply (wf_qua_qual empty P); exact HP.
        - apply (wf_qua_qual empty P0); exact HP0.
        - exact Hexpr.
        - exact HcP.
        - exact HcP0.
        - exact Hord. }
      { (* qabs *) assert (Hsub0 : subqual empty P0 Q) by (apply (typing_qabs_qual_le empty P0 Q0 e1 Q T); exact H).
        destruct (subqual_wf empty P0 Q Hsub0) as [HP0 _].
        destruct (concretize_wf_empty P0 HP0) as [cP0 HcP0].
        assert (Hord : cP0 ≤ cP) by
          (eapply subqual_concretize_ord; [exact (subqual_trans empty P0 Q P Hsub0 H0)|exact HcP0|exact HcP]).
        right. exists (exp_qabs P Q0 e1).
        apply (red_upqual_qabs P P0 cP cP0 Q0 e1).
        - apply (wf_qua_qual empty P); exact HP.
        - apply (wf_qua_qual empty P0); exact HP0.
        - exact Hexpr.
        - exact HcP.
        - exact HcP0.
        - exact Hord. }
      { (* inl *) assert (Hsub0 : subqual empty P0 Q) by (apply (typing_inl_qual_le empty P0 e1 Q T); exact H).
        destruct (subqual_wf empty P0 Q Hsub0) as [HP0 _].
        destruct (concretize_wf_empty P0 HP0) as [cP0 HcP0].
        assert (Hord : cP0 ≤ cP) by
          (eapply subqual_concretize_ord; [exact (subqual_trans empty P0 Q P Hsub0 H0)|exact HcP0|exact HcP]).
        right. exists (exp_inl P e1).
        apply (red_upqual_inl P P0 cP cP0 e1).
        - apply (wf_qua_qual empty P); exact HP.
        - apply (wf_qua_qual empty P0); exact HP0.
        - exact Hexpr.
        - exact HcP.
        - exact HcP0.
        - exact Hord. }
      { (* inr *) assert (Hsub0 : subqual empty P0 Q) by (apply (typing_inr_qual_le empty P0 e1 Q T); exact H).
        destruct (subqual_wf empty P0 Q Hsub0) as [HP0 _].
        destruct (concretize_wf_empty P0 HP0) as [cP0 HcP0].
        assert (Hord : cP0 ≤ cP) by
          (eapply subqual_concretize_ord; [exact (subqual_trans empty P0 Q P Hsub0 H0)|exact HcP0|exact HcP]).
        right. exists (exp_inr P e1).
        apply (red_upqual_inr P P0 cP cP0 e1).
        - apply (wf_qua_qual empty P); exact HP.
        - apply (wf_qua_qual empty P0); exact HP0.
        - exact Hexpr.
        - exact HcP.
        - exact HcP0.
        - exact Hord. }
      { (* pair *) assert (Hsub0 : subqual empty P0 Q) by (apply (typing_pair_qual_le empty P0 e1 e2 Q T); exact H).
        destruct (subqual_wf empty P0 Q Hsub0) as [HP0 _].
        destruct (concretize_wf_empty P0 HP0) as [cP0 HcP0].
        assert (Hord : cP0 ≤ cP) by
          (eapply subqual_concretize_ord; [exact (subqual_trans empty P0 Q P Hsub0 H0)|exact HcP0|exact HcP]).
        right. exists (exp_pair P e1 e2).
        apply (red_upqual_pair P P0 cP cP0 e1 e2).
        - apply (wf_qua_qual empty P); exact HP.
        - apply (wf_qua_qual empty P0); exact HP0.
        - exact Hexpr.
        - exact HcP.
        - exact HcP0.
        - exact Hord. }
    + right. destruct (subqual_wf empty Q P H0) as [_ HP].
      destruct Hr as [e' Hred]. exists (exp_upqual P e'). apply red_upqual_1.
      * apply (wf_qua_qual empty P); exact HP.
      * exact Hred.
  - destruct (IHtyping eq_refl) as [Hv|Hr].
    + destruct (subqual_wf empty Q P H0) as [HQ HP].
      destruct (concretize_wf_empty Q HQ) as [cQ HcQ].
      destruct (concretize_wf_empty P HP) as [cP HcP].
      assert (Hexpr : expr e) by (apply value_expr; exact Hv).
      destruct Hv.
      { (* abs *) assert (Hsub0 : subqual empty P0 Q) by (apply (typing_abs_qual_le empty P0 T0 e1 Q T); exact H).
        destruct (subqual_wf empty P0 Q Hsub0) as [HP0 _].
        destruct (concretize_wf_empty P0 HP0) as [cP0 HcP0].
        assert (Hord : cP0 ≤ cP) by
          (eapply subqual_concretize_ord; [exact (subqual_trans empty P0 Q P Hsub0 H0)|exact HcP0|exact HcP]).
        right. exists (exp_abs P0 T0 e1).
        apply (red_check_abs P P0 cP cP0 T0 e1).
        - apply (wf_qua_qual empty P); exact HP.
        - apply (wf_qua_qual empty P0); exact HP0.
        - exact Hexpr.
        - exact HcP.
        - exact HcP0.
        - exact Hord. }
      { (* tabs *) assert (Hsub0 : subqual empty P0 Q) by (apply (typing_tabs_qual_le empty P0 T0 e1 Q T); exact H).
        destruct (subqual_wf empty P0 Q Hsub0) as [HP0 _].
        destruct (concretize_wf_empty P0 HP0) as [cP0 HcP0].
        assert (Hord : cP0 ≤ cP) by
          (eapply subqual_concretize_ord; [exact (subqual_trans empty P0 Q P Hsub0 H0)|exact HcP0|exact HcP]).
        right. exists (exp_tabs P0 T0 e1).
        apply (red_check_tabs P P0 cP cP0 T0 e1).
        - apply (wf_qua_qual empty P); exact HP.
        - apply (wf_qua_qual empty P0); exact HP0.
        - exact Hexpr.
        - exact HcP.
        - exact HcP0.
        - exact Hord. }
      { (* qabs *) assert (Hsub0 : subqual empty P0 Q) by (apply (typing_qabs_qual_le empty P0 Q0 e1 Q T); exact H).
        destruct (subqual_wf empty P0 Q Hsub0) as [HP0 _].
        destruct (concretize_wf_empty P0 HP0) as [cP0 HcP0].
        assert (Hord : cP0 ≤ cP) by
          (eapply subqual_concretize_ord; [exact (subqual_trans empty P0 Q P Hsub0 H0)|exact HcP0|exact HcP]).
        right. exists (exp_qabs P0 Q0 e1).
        apply (red_check_qabs P P0 cP cP0 Q0 e1).
        - apply (wf_qua_qual empty P); exact HP.
        - apply (wf_qua_qual empty P0); exact HP0.
        - exact Hexpr.
        - exact HcP.
        - exact HcP0.
        - exact Hord. }
      { (* inl *) assert (Hsub0 : subqual empty P0 Q) by (apply (typing_inl_qual_le empty P0 e1 Q T); exact H).
        destruct (subqual_wf empty P0 Q Hsub0) as [HP0 _].
        destruct (concretize_wf_empty P0 HP0) as [cP0 HcP0].
        assert (Hord : cP0 ≤ cP) by
          (eapply subqual_concretize_ord; [exact (subqual_trans empty P0 Q P Hsub0 H0)|exact HcP0|exact HcP]).
        right. exists (exp_inl P0 e1).
        apply (red_check_inl P P0 cP cP0 e1).
        - apply (wf_qua_qual empty P); exact HP.
        - apply (wf_qua_qual empty P0); exact HP0.
        - exact Hexpr.
        - exact HcP.
        - exact HcP0.
        - exact Hord. }
      { (* inr *) assert (Hsub0 : subqual empty P0 Q) by (apply (typing_inr_qual_le empty P0 e1 Q T); exact H).
        destruct (subqual_wf empty P0 Q Hsub0) as [HP0 _].
        destruct (concretize_wf_empty P0 HP0) as [cP0 HcP0].
        assert (Hord : cP0 ≤ cP) by
          (eapply subqual_concretize_ord; [exact (subqual_trans empty P0 Q P Hsub0 H0)|exact HcP0|exact HcP]).
        right. exists (exp_inr P0 e1).
        apply (red_check_inr P P0 cP cP0 e1).
        - apply (wf_qua_qual empty P); exact HP.
        - apply (wf_qua_qual empty P0); exact HP0.
        - exact Hexpr.
        - exact HcP.
        - exact HcP0.
        - exact Hord. }
      { (* pair *) assert (Hsub0 : subqual empty P0 Q) by (apply (typing_pair_qual_le empty P0 e1 e2 Q T); exact H).
        destruct (subqual_wf empty P0 Q Hsub0) as [HP0 _].
        destruct (concretize_wf_empty P0 HP0) as [cP0 HcP0].
        assert (Hord : cP0 ≤ cP) by
          (eapply subqual_concretize_ord; [exact (subqual_trans empty P0 Q P Hsub0 H0)|exact HcP0|exact HcP]).
        right. exists (exp_pair P0 e1 e2).
        apply (red_check_pair P P0 cP cP0 e1 e2).
        - apply (wf_qua_qual empty P); exact HP.
        - apply (wf_qua_qual empty P0); exact HP0.
        - exact Hexpr.
        - exact HcP.
        - exact HcP0.
        - exact Hord. }
    + right. destruct (subqual_wf empty Q P H0) as [_ HP].
      destruct Hr as [e' Hred]. exists (exp_check P e'). apply red_check_1.
      * apply (wf_qua_qual empty P); exact HP.
      * exact Hred.
Qed.
