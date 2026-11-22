Require Import Metalib.Metatheory.

Require Import syntax_ott rules_inf Infrastructure rules_inf2.

Require Import Coq.Strings.String.

Fixpoint erase_anno (e:exp) : dexp :=
  match e with
  | (e_var_b nat) => de_var_b nat
  | (e_var_f x) => de_var_f x
  | e_top => de_top
  | (e_lit i5) => de_lit i5
  | (e_abs A e B) => de_abs (erase_anno e)
  | (e_fixpoint e A) => de_fixpoint (erase_anno e)
  | (e_app e1 e2) => de_app (erase_anno e1) (erase_anno e2)
  | (e_merge e1 e2) => de_merge (erase_anno e1) (erase_anno e2)
  | (e_anno e A) => erase_anno e
  end.

Notation "| e |" := (erase_anno e) (at level 30, e at level 39).

From Stdlib Require Import Lia.

(* ------------------------------------------------------------------ *)
(* Auxiliary lemmas about erasure.                                     *)
(* ------------------------------------------------------------------ *)

(* Erasure commutes with opening. *)
Lemma erase_open_rec : forall k (t r : exp),
  erase_anno (open_exp_wrt_exp_rec k r t) =
  open_dexp_wrt_dexp_rec k (erase_anno r) (erase_anno t).
Proof.
  intros k t. revert k. induction t as
    [ n | x | | i5 | A e IHe B | e IHe A | e1 IHe1 e2 IHe2
    | e1 IHe1 e2 IHe2 | e IHe A ]; intros k r; simpl.
  - destruct (lt_eq_lt_dec n k) as [[h|h]|h]; reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IHe. reflexivity.
  - rewrite IHe. reflexivity.
  - rewrite IHe1, IHe2. reflexivity.
  - rewrite IHe1, IHe2. reflexivity.
  - apply IHe.
Qed.

Lemma erase_open : forall (t r : exp),
  erase_anno (open_exp_wrt_exp t r) =
  open_dexp_wrt_dexp (erase_anno t) (erase_anno r).
Proof.
  intros. unfold open_exp_wrt_exp, open_dexp_wrt_dexp.
  apply erase_open_rec.
Qed.

Lemma erase_open_var : forall (t : exp) x,
  open_dexp_wrt_dexp (erase_anno t) (de_var_f x) =
  erase_anno (open_exp_wrt_exp t (e_var_f x)).
Proof.
  intros. rewrite erase_open. reflexivity.
Qed.

(* Locally closed expressions erase to locally closed de Bruijn terms. *)
Lemma lc_exp_erase : forall e, lc_exp e -> lc_dexp (erase_anno e).
Proof.
  intros e H. induction H as
    [ x | | i5 | A e B Hbody IHbody | e A Hbody IHbody
    | e1 e2 H1 IH1 H2 IH2 | e1 e2 H1 IH1 H2 IH2 | e A H IH ]; simpl.
  - apply lc_de_var_f.
  - apply lc_de_top.
  - apply lc_de_lit.
  - apply lc_de_abs. intro x. rewrite erase_open_var. apply IHbody.
  - apply lc_de_fixpoint. intro x. rewrite erase_open_var. apply IHbody.
  - apply lc_de_app; assumption.
  - apply lc_de_merge; assumption.
  - apply IH.
Qed.

(* Changing the result annotation of an abstraction preserves local closure. *)
Lemma lc_exp_abs_anno : forall A e B D,
  lc_exp (e_abs A e B) -> lc_exp (e_abs A e D).
Proof.
  intros A e B D H. inversion H; subst. apply lc_e_abs. assumption.
Qed.

Lemma lc_exp_topabs : forall B, lc_exp (e_abs t_top e_top B).
Proof.
  intro B. apply lc_e_abs. intro x. simpl. apply lc_e_top.
Qed.

(* Values erase to Dunfield values. *)
Lemma value_erase : forall v, value v -> DValue (erase_anno v).
Proof.
  intros v H. induction H as
    [ | i5 | A e B Hlc | v1 v2 Hv1 IH1 Hv2 IH2 ]; simpl.
  - apply DVal_top.
  - apply DVal_nat.
  - apply DVal_abs. apply (lc_exp_erase (e_abs A e B)). apply Hlc.
  - apply DVal_merge; assumption.
Qed.

(* Type-directed reduction preserves valuehood. *)
Lemma value_typedreduce : forall v A v',
  TypedReduce v A v' -> value v -> value v'.
Proof.
  intros v A v' H. induction H as
    [ i5
    | v Hlc
    | v A B Hlc Htop
    | A e B C D Hlc Hnt Hs1 Hs2
    | v1 v2 A v1' Hlc2 Hderiv IH Hord
    | v1 v2 A v2' Hlc1 Hderiv IH Hord
    | v A B v1 v2 Hderiv1 IH1 Hderiv2 IH2 ]; intros Hv.
  - apply value_lit.
  - apply value_unit.
  - apply value_anno. apply lc_exp_topabs.
  - apply value_anno. eapply lc_exp_abs_anno; eassumption.
  - apply IH. inversion Hv; subst; assumption.
  - apply IH. inversion Hv; subst; assumption.
  - apply value_merge; [ apply IH1; assumption | apply IH2; assumption ].
Qed.

(* Type-directed reduction relates locally closed expressions. *)
Lemma typedreduce_lc : forall v A v',
  TypedReduce v A v' -> lc_exp v /\ lc_exp v'.
Proof.
  intros v A v' H. induction H as
    [ i5
    | v Hlc
    | v A B Hlc Htop
    | A e B C D Hlc Hnt Hs1 Hs2
    | v1 v2 A v1' Hlc2 Hderiv IH Hord
    | v1 v2 A v2' Hlc1 Hderiv IH Hord
    | v A B v1 v2 Hderiv1 IH1 Hderiv2 IH2 ].
  - split; apply lc_e_lit.
  - split; [ assumption | apply lc_e_top ].
  - split; [ assumption | apply lc_exp_topabs ].
  - split.
    + eapply lc_exp_abs_anno; eassumption.
    + eapply lc_exp_abs_anno; eassumption.
  - destruct IH as [Hl Hr]. split.
    + apply lc_e_merge; assumption.
    + assumption.
  - destruct IH as [Hl Hr]. split.
    + apply lc_e_merge; assumption.
    + assumption.
  - destruct IH1 as [Hv H1], IH2 as [Hv2 H2]. split.
    + assumption.
    + apply lc_e_merge; assumption.
Qed.

(* ------------------------------------------------------------------ *)
(* Star lemmas for the Dunfield reduction.                             *)
(* ------------------------------------------------------------------ *)

Lemma mul_dstep_trans : forall a b c : dexp,
  (a ->>* b) -> (b ->>* c) -> (a ->>* c).
Proof.
  intros a b c H. induction H as
    [ a | a b0 c0 Hstep Hrest IH ]; intros Hbc.
  - apply Hbc.
  - eapply star_step. apply Hstep. apply IH. apply Hbc.
Qed.

Lemma mul_dstep_appl : forall e1 e1' : dexp,
  (e1 ->>* e1') ->
  forall e2, lc_dexp e2 -> (de_app e1 e2) ->>* (de_app e1' e2).
Proof.
  intros e1 e1' H. induction H as
    [ a | a b c Hstep Hrest IH ]; intros e2 Hlc.
  - apply star_refl.
  - eapply star_step. apply DStep_appl; [ apply Hlc | apply Hstep ].
    apply IH. apply Hlc.
Qed.

Lemma mul_dstep_appr : forall (v1 : dexp) e2 e2',
  DValue v1 -> (e2 ->>* e2') -> (de_app v1 e2) ->>* (de_app v1 e2').
Proof.
  intros v1 e2 e2' Hv H. induction H as
    [ a | a b c Hstep Hrest IH ].
  - apply star_refl.
  - eapply star_step. apply DStep_appr; [ apply Hv | apply Hstep ]. apply IH.
Qed.

Lemma mul_dstep_mergel : forall e1 e1' : dexp,
  (e1 ->>* e1') ->
  forall e2, lc_dexp e2 -> (de_merge e1 e2) ->>* (de_merge e1' e2).
Proof.
  intros e1 e1' H. induction H as
    [ a | a b c Hstep Hrest IH ]; intros e2 Hlc.
  - apply star_refl.
  - eapply star_step. apply DStep_mergel; [ apply Hlc | apply Hstep ].
    apply IH. apply Hlc.
Qed.

Lemma mul_dstep_merger : forall (v1 : dexp) e2 e2',
  DValue v1 -> (e2 ->>* e2') -> (de_merge v1 e2) ->>* (de_merge v1 e2').
Proof.
  intros v1 e2 e2' Hv H. induction H as
    [ a | a b c Hstep Hrest IH ].
  - apply star_refl.
  - eapply star_step. apply DStep_merger; [ apply Hv | apply Hstep ]. apply IH.
Qed.

(* ------------------------------------------------------------------ *)
(* Main simulation lemma for type-directed reduction.                  *)
(* ------------------------------------------------------------------ *)

Lemma typedreduce_erase : forall v A v',
  value v -> TypedReduce v A v' -> (erase_anno v) ->>* (erase_anno v').
Proof.
  intros v A v' Hv H. revert Hv. induction H as
    [ i5
    | v Hlc
    | v A B Hlc Htop
    | A e B C D Hlc Hnt Hs1 Hs2
    | v1 v2 A v1' Hlc2 Hderiv IH Hord
    | v1 v2 A v2' Hlc1 Hderiv IH Hord
    | v A B v1 v2 Hderiv1 IH1 Hderiv2 IH2 ]; intros Hv.
  - simpl. apply star_refl.
  - simpl. eapply star_step.
    + apply DStep_top. apply lc_exp_erase. apply Hlc.
    + apply star_refl.
  - simpl. eapply star_step.
    + apply DStep_top. apply lc_exp_erase. apply Hlc.
    + eapply star_step.
      * apply DStep_toparr.
      * apply star_refl.
  - simpl. apply star_refl.
  - simpl.
    destruct (typedreduce_lc v1 A v1' Hderiv) as [Hlcv1 _].
    eapply star_step.
    + apply DStep_unmergel.
      * apply lc_exp_erase. apply Hlc2.
      * apply lc_exp_erase. apply Hlcv1.
    + apply IH. inversion Hv; subst; assumption.
  - simpl.
    destruct (typedreduce_lc v2 A v2' Hderiv) as [Hlcv2 _].
    eapply star_step.
    + apply DStep_unmerger.
      * apply lc_exp_erase. apply Hlc1.
      * apply lc_exp_erase. apply Hlcv2.
    + apply IH. inversion Hv; subst; assumption.
  - simpl.
    assert (Hvv1 : value v1) by (apply (value_typedreduce v A v1 Hderiv1); apply Hv).
    assert (Hvv2 : value v2) by (apply (value_typedreduce v B v2 Hderiv2); apply Hv).
    assert (Hlcv : lc_exp v) by (apply (proj1 (typedreduce_lc v A v1 Hderiv1))).
    assert (Hlcdv : lc_dexp (erase_anno v)) by (apply lc_exp_erase; apply Hlcv).
    assert (Hdv1 : DValue (erase_anno v1)) by (apply value_erase; apply Hvv1).
    assert (Hstar1 : (erase_anno v) ->>* (erase_anno v1)) by (apply IH1; apply Hv).
    assert (Hstar2 : (erase_anno v) ->>* (erase_anno v2)) by (apply IH2; apply Hv).
    eapply mul_dstep_trans.
    + eapply star_step.
      * apply DStep_split. apply Hlcdv.
      * eapply mul_dstep_mergel.
        -- apply Hstar1.
        -- apply Hlcdv.
    + eapply mul_dstep_merger.
      * apply Hdv1.
      * apply Hstar2.
Qed.

(* ------------------------------------------------------------------ *)
(* Main theorem.                                                       *)
(* ------------------------------------------------------------------ *)

Theorem reduction_soundness : forall e e',
    step e e' -> (erase_anno e) ->>* (erase_anno e').
Proof.
  intros e e' H. induction H as
    [ A e D v v' Hlc Hval Hred
    | v A v' Hval Hred
    | e1 e2 e1' Hlc Hstep IH
    | v1 e2 e2' Hval Hstep IH
    | e1 e2 e1' Hlc Hstep IH
    | v1 e2 e2' Hval Hstep IH
    | e A e' Hstep IH
    | e A Hlc ].
  - (* Step_beta *)
    simpl. rewrite erase_open.
    pose proof (typedreduce_erase v A v' Hval Hred) as Hstar.
    pose proof (value_typedreduce v A v' Hred Hval) as Hval'.
    pose proof (DVal_abs (erase_anno e) (lc_exp_erase (e_abs A e D) Hlc)) as Hdabs.
    pose proof (mul_dstep_appr (de_abs (erase_anno e)) (erase_anno v) (erase_anno v')
                  Hdabs Hstar) as Happ.
    pose proof (value_erase v' Hval') as Hdv'.
    eapply mul_dstep_trans.
    + apply Happ.
    + eapply star_step.
      * apply DStep_beta.
        -- apply (lc_exp_erase (e_abs A e D)). apply Hlc.
        -- apply Hdv'.
      * apply star_refl.
  - (* Step_annov *)
    simpl. eapply typedreduce_erase; eassumption.
  - (* Step_appl *)
    simpl. eapply mul_dstep_appl; [ apply IH | apply lc_exp_erase; apply Hlc ].
  - (* Step_appr *)
    simpl. eapply mul_dstep_appr.
    + apply value_erase. apply Hval.
    + apply IH.
  - (* Step_mergel *)
    simpl. eapply mul_dstep_mergel; [ apply IH | apply lc_exp_erase; apply Hlc ].
  - (* Step_merger *)
    simpl. eapply mul_dstep_merger.
    + apply value_erase. apply Hval.
    + apply IH.
  - (* Step_anno *)
    simpl. apply IH.
  - (* Step_fix *)
    simpl. rewrite erase_open. eapply star_step.
    + apply DStep_fix. apply (lc_exp_erase (e_fixpoint e A)). apply Hlc.
    + apply star_refl.
Qed.
