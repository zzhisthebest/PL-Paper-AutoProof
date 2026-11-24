From Fsub.CaptureTrack Require Import Fsub_LetSum_Definitions.

Local Lemma subqual_regular : forall E P Q,
  subqual E P Q -> wf_env E /\ wf_qua E P /\ wf_qua E Q.
Proof.
  intros E P Q H.
  induction H; intuition eauto using wf_qua.
Qed.

Local Definition subqual_cut (M : qua) : Prop :=
  forall E P Q, subqual E P M -> subqual E M Q -> subqual E P Q.

Local Lemma subqual_cut_step : forall M,
  (match M with
   | qua_meet M1 M2 | qua_join M1 M2 => subqual_cut M1 /\ subqual_cut M2
   | _ => True
   end) -> subqual_cut M.
Proof.
  intros M Hparts.
  unfold subqual_cut.
  intros E P Q Hleft Hright.
  revert Q Hright Hparts.
  induction Hleft; intros Z Hright Hparts.
  all: try solve [assumption
    | destruct (subqual_regular _ _ _ Hright) as [? [? ?]];
      auto using subqual_bot
    | eauto using subqual_trans_qvar, subqual_trans_term_qvar,
        subqual_join_elim, subqual_meet_eliml, subqual_meet_elimr].
  (* Commute the cut past right introductions. A matching elimination
     reduces the cut to a component of the middle qualifier. *)
  all: match type of Hright with
       | subqual _ ?M _ => remember M as middle eqn:Hmiddle in Hright
       end;
       induction Hright; inversion Hmiddle; subst; simpl in Hparts.
  all: intuition eauto using subqual_top, subqual_join_inl,
    subqual_join_inr, subqual_meet_intro.
  all: match goal with
       | H : subqual ?E ?P _ |- subqual ?E ?P qua_top =>
           apply subqual_top;
             [assumption | exact (proj1 (proj2 (subqual_regular _ _ _ H)))]
       end.
Qed.

Local Lemma subqual_transitive : forall M, subqual_cut M.
Proof.
  induction M; apply subqual_cut_step; simpl; auto.
Qed.

Theorem capture_prediction : forall E u Q U,
  value u ->
  typing E u (qtyp_qtyp Q U) ->
  subqual E (fv_exp_for_qua u) Q.
Proof.
  intros E u Q U Hvalue Htyping.
  change (subqual E (fv_exp_for_qua u)
    (let 'qtyp_qtyp P _ := qtyp_qtyp Q U in P)).
  revert Hvalue.
  induction Htyping; intros Hvalue; try solve [inversion Hvalue | assumption].
  - destruct H; simpl in *.
    eapply subqual_transitive; [apply IHHtyping; exact Hvalue | eassumption].
  - inversion Hvalue; subst; simpl.
    eapply subqual_transitive; [apply IHHtyping; assumption | eassumption].
  - inversion Hvalue; subst; simpl.
    eapply subqual_transitive; [apply IHHtyping; assumption | eassumption].
  - inversion Hvalue; subst; simpl.
    assert (Hfirst : subqual E (fv_exp_for_qua e1) Q1) by
      (apply IHHtyping1; assumption).
    assert (Hsecond : subqual E (fv_exp_for_qua e2) Q2) by
      (apply IHHtyping2; assumption).
    destruct (subqual_regular _ _ _ Hfirst) as [_ [_ Hwf1]].
    destruct (subqual_regular _ _ _ Hsecond) as [_ [_ Hwf2]].
    eapply subqual_transitive; [| exact H].
    apply subqual_join_elim.
    + now apply subqual_join_inl.
    + now apply subqual_join_inr.
Qed.
