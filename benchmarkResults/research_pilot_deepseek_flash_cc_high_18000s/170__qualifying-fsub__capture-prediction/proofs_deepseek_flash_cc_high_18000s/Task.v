From Fsub.CaptureTrack Require Import Fsub_LetSum_Definitions.

(* ------------------------------------------------------------------ *)
(* Well-formedness of typing environments                              *)
(* ------------------------------------------------------------------ *)

Lemma typing_wf_env : forall E e T,
  typing E e T -> wf_env E.
Proof.
  intros E e T H. induction H; auto.
  all: match goal with
       | Hx : forall x, x `notin` ?L -> wf_env (x ~ _ ++ ?E) |- wf_env ?E =>
           destruct (atom_fresh L) as [x Hxnot];
           specialize (Hx x Hxnot); inversion Hx; assumption
       end.
Qed.

(* ------------------------------------------------------------------ *)
(* Subqualifiers are well formed                                        *)
(* ------------------------------------------------------------------ *)

Lemma subqual_wf : forall E Q1 Q2,
  subqual E Q1 Q2 -> wf_env E -> wf_qua E Q1 /\ wf_qua E Q2.
Proof.
  intros E Q1 Q2 H. induction H; intros W.
  - split; [assumption|constructor].
  - split; [constructor|assumption].
  - split; assumption.
  - destruct (IHsubqual W) as [_ Hq]. split; [eapply wf_qua_fvar; eauto | exact Hq].
  - destruct (IHsubqual W) as [_ Hq]. split; [eapply wf_qua_term_fvar; eauto | exact Hq].
  - destruct (IHsubqual W) as [Hq HR1]. split; [exact Hq | apply wf_qua_join; assumption].
  - destruct (IHsubqual W) as [Hq HR2]. split; [exact Hq | apply wf_qua_join; assumption].
  - destruct (IHsubqual1 W) as [HR1 Hq]. destruct (IHsubqual2 W) as [HR2 _]. split; [apply wf_qua_join; assumption | exact Hq].
  - destruct (IHsubqual W) as [HR1 Hq]. split; [apply wf_qua_meet; assumption | exact Hq].
  - destruct (IHsubqual W) as [HR2 Hq]. split; [apply wf_qua_meet; assumption | exact Hq].
  - destruct (IHsubqual1 W) as [Hq HR1]. destruct (IHsubqual2 W) as [_ HR2]. split; [exact Hq | apply wf_qua_meet; assumption].
Qed.

(* ------------------------------------------------------------------ *)
(* Transitivity helpers for subqual                                    *)
(* ------------------------------------------------------------------ *)

Lemma top_trans : forall E Q1 Q3,
  subqual E Q1 qua_top -> subqual E qua_top Q3 -> subqual E Q1 Q3.
Proof.
  intros E Q1 Q3 H1 H2.
  remember qua_top as S eqn:HS in H2.
  revert Q1 H1 HS.
  induction H2; intros Q1 H1 HS.
  - (* top *) subst. exact H1.
  - (* bot *) discriminate HS.
  - (* refl *) discriminate HS.
  - (* trans_qvar *) discriminate HS.
  - (* trans_term_qvar *) discriminate HS.
  - (* join_inl *) subst. apply subqual_join_inl.
    + eapply IHsubqual; eauto.
    + exact H.
  - (* join_inr *) subst. apply subqual_join_inr.
    + exact H.
    + eapply IHsubqual; eauto.
  - (* join_elim *) discriminate HS.
  - (* meet_eliml *) discriminate HS.
  - (* meet_elimr *) discriminate HS.
  - (* meet_intro *) subst. apply subqual_meet_intro.
    + eapply IHsubqual1; eauto.
    + eapply IHsubqual2; eauto.
Qed.

Lemma join_trans_l : forall E Q R1 R2 Q3,
  wf_env E -> subqual E Q R1 -> wf_qua E R2 ->
  (forall S, subqual E R1 S -> subqual E Q S) ->
  subqual E (qua_join R1 R2) Q3 -> subqual E Q Q3.
Proof.
  intros E Q R1 R2 Q3 W HQR1 WR2 IH H.
  remember (qua_join R1 R2) as S eqn:HS in H.
  induction H.
  - (* top *) apply subqual_top; [exact W | exact (proj1 (subqual_wf E Q R1 HQR1 W))].
  - (* bot *) discriminate HS.
  - (* refl *) discriminate HS.
  - (* trans_qvar *) discriminate HS.
  - (* trans_term_qvar *) discriminate HS.
  - (* join_inl *) apply subqual_join_inl.
    + exact (IHsubqual W HQR1 WR2 IH HS).
    + exact H0.
  - (* join_inr *) apply subqual_join_inr.
    + exact H.
    + exact (IHsubqual W HQR1 WR2 IH HS).
  - (* join_elim *) injection HS as E1 E2; subst. apply IH. exact H.
  - (* meet_eliml *) discriminate HS.
  - (* meet_elimr *) discriminate HS.
  - (* meet_intro *) apply subqual_meet_intro.
    + exact (IHsubqual1 W HQR1 WR2 IH HS).
    + exact (IHsubqual2 W HQR1 WR2 IH HS).
Qed.

Lemma join_trans_r : forall E Q R1 R2 Q3,
  wf_env E -> wf_qua E R1 -> subqual E Q R2 ->
  (forall S, subqual E R2 S -> subqual E Q S) ->
  subqual E (qua_join R1 R2) Q3 -> subqual E Q Q3.
Proof.
  intros E Q R1 R2 Q3 W WR1 HQR2 IH H.
  remember (qua_join R1 R2) as S eqn:HS in H.
  induction H.
  - (* top *) apply subqual_top; [exact W | exact (proj1 (subqual_wf E Q R2 HQR2 W))].
  - (* bot *) discriminate HS.
  - (* refl *) discriminate HS.
  - (* trans_qvar *) discriminate HS.
  - (* trans_term_qvar *) discriminate HS.
  - (* join_inl *) apply subqual_join_inl.
    + exact (IHsubqual W WR1 HQR2 IH HS).
    + exact H0.
  - (* join_inr *) apply subqual_join_inr.
    + exact H.
    + exact (IHsubqual W WR1 HQR2 IH HS).
  - (* join_elim *) injection HS as E1 E2; subst. apply IH. exact H0.
  - (* meet_eliml *) discriminate HS.
  - (* meet_elimr *) discriminate HS.
  - (* meet_intro *) apply subqual_meet_intro.
    + exact (IHsubqual1 W WR1 HQR2 IH HS).
    + exact (IHsubqual2 W WR1 HQR2 IH HS).
Qed.

Lemma meet_trans : forall E Q R1 R2 Q3,
  wf_env E -> subqual E Q R1 -> subqual E Q R2 ->
  (forall S, subqual E R1 S -> subqual E Q S) ->
  (forall S, subqual E R2 S -> subqual E Q S) ->
  subqual E (qua_meet R1 R2) Q3 -> subqual E Q Q3.
Proof.
  intros E Q R1 R2 Q3 W HQR1 HQR2 IH1 IH2 H.
  remember (qua_meet R1 R2) as S eqn:HS in H.
  induction H.
  - (* top *) apply subqual_top; [exact W | exact (proj1 (subqual_wf E Q R1 HQR1 W))].
  - (* bot *) discriminate HS.
  - (* refl *) discriminate HS.
  - (* trans_qvar *) discriminate HS.
  - (* trans_term_qvar *) discriminate HS.
  - (* join_inl *) apply subqual_join_inl.
    + exact (IHsubqual W HQR1 HQR2 IH1 IH2 HS).
    + exact H0.
  - (* join_inr *) apply subqual_join_inr.
    + exact H.
    + exact (IHsubqual W HQR1 HQR2 IH1 IH2 HS).
  - (* join_elim *) discriminate HS.
  - (* meet_eliml *) injection HS as E1 E2; subst. apply IH1. exact H.
  - (* meet_elimr *) injection HS as E1 E2; subst. apply IH2. exact H0.
  - (* meet_intro *) apply subqual_meet_intro.
    + exact (IHsubqual1 W HQR1 HQR2 IH1 IH2 HS).
    + exact (IHsubqual2 W HQR1 HQR2 IH1 IH2 HS).
Qed.

Lemma subqual_trans : forall E,
  wf_env E -> forall Q1 Q2 Q3,
  subqual E Q1 Q2 -> subqual E Q2 Q3 -> subqual E Q1 Q3.
Proof.
  intros E W Q1 Q2 Q3 H12 H23.
  revert Q3 H23.
  induction H12; intros Qz H23.
  - (* top *)
    apply (top_trans E Q Qz).
    + apply subqual_top; [exact H | exact H0].
    + exact H23.
  - (* bot *)
    apply subqual_bot; [exact W | exact (proj2 (subqual_wf E Q Qz H23 W))].
  - (* refl *) exact H23.
  - (* trans_qvar *)
    eapply subqual_trans_qvar; [exact H | apply (IHsubqual W Qz H23)].
  - (* trans_term_qvar *)
    eapply subqual_trans_term_qvar; [exact H | apply (IHsubqual W Qz H23)].
  - (* join_inl *)
    apply (join_trans_l E Q R1 R2 Qz W H12 H (fun S HS => IHsubqual W S HS) H23).
  - (* join_inr *)
    apply (join_trans_r E Q R1 R2 Qz W H H12 (fun S HS => IHsubqual W S HS) H23).
  - (* join_elim *)
    apply subqual_join_elim;
      [apply (IHsubqual1 W Qz H23) | apply (IHsubqual2 W Qz H23)].
  - (* meet_eliml *)
    apply subqual_meet_eliml; [apply (IHsubqual W Qz H23) | exact H].
  - (* meet_elimr *)
    apply subqual_meet_elimr; [exact H | apply (IHsubqual W Qz H23)].
  - (* meet_intro *)
    apply (meet_trans E Q R1 R2 Qz W H12_ H12_0
             (fun S HS => IHsubqual1 W S HS)
             (fun S HS => IHsubqual2 W S HS) H23).
Qed.

Theorem capture_prediction : forall E u Q U,
  value u ->
  typing E u (qtyp_qtyp Q U) ->
  subqual E (fv_exp_for_qua u) Q.
Proof.
  intros E u Q U Hval Hty.
  remember (qtyp_qtyp Q U) as T eqn:HT in Hty.
  revert Q U HT Hval.
  induction Hty; intros Q0 U0 HT Hval.
  - (* var *) inversion Hval.
  - (* abs *) inversion HT; subst; assumption.
  - (* app *) inversion Hval.
  - (* tabs *) inversion HT; subst; assumption.
  - (* tapp *) inversion Hval.
  - (* qabs *) inversion HT; subst; assumption.
  - (* qapp *) inversion Hval.
  - (* sub *) destruct S as [Qs Us].
    pose proof (IHHty Qs Us eq_refl Hval) as Hfv.
    subst T.
    inversion H; subst.
    exact (subqual_trans E (typing_wf_env E e (qtyp_qtyp Qs Us) Hty)
             (fv_exp_for_qua e) Qs Q0 Hfv H4).
  - (* let *) inversion Hval.
  - (* inl *) inversion HT; subst. inversion Hval; subst.
    exact (subqual_trans E (typing_wf_env E e1 (qtyp_qtyp Q1 S1) Hty)
             (fv_exp_for_qua e1) Q1 Q0 (IHHty Q1 S1 eq_refl H4) H).
  - (* inr *) inversion HT; subst. inversion Hval; subst.
    exact (subqual_trans E (typing_wf_env E e1 (qtyp_qtyp Q2 S2) Hty)
             (fv_exp_for_qua e1) Q2 Q0 (IHHty Q2 S2 eq_refl H4) H).
  - (* case *) inversion Hval.
  - (* pair *) inversion HT; subst. inversion Hval; subst.
    destruct (subqual_wf E (qua_join Q1 Q2) Q0 H
                (typing_wf_env E e1 (qtyp_qtyp Q1 S1) Hty1)) as [Hwf _].
    inversion Hwf; subst.
    assert (H1P : subqual E (fv_exp_for_qua e1) Q0).
    { eapply (subqual_trans E).
      - eapply typing_wf_env; exact Hty1.
      - eapply subqual_join_inl; [exact (IHHty1 Q1 S1 eq_refl H4) | exact H7].
      - exact H. }
    assert (H2P : subqual E (fv_exp_for_qua e2) Q0).
    { eapply (subqual_trans E).
      - eapply typing_wf_env; exact Hty1.
      - eapply subqual_join_inr; [exact H6 | exact (IHHty2 Q2 S2 eq_refl H5)].
      - exact H. }
    cbn.
    apply subqual_join_elim; [exact H1P | exact H2P].
  - (* first *) inversion Hval.
  - (* second *) inversion Hval.
  - (* upqual *) inversion Hval.
  - (* check *) inversion Hval.
Qed.
