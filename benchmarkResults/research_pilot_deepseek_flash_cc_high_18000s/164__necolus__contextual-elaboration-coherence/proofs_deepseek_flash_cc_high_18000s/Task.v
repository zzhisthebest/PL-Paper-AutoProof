Require Import Metalib.Metatheory.
From Stdlib Require Import Arith Lia.
From Coq Require Import Program.Equality.

Require Import Observations Infrastructure target_inf.


(* ==================== helper development ==================== *)
Lemma value_no_step : forall v, value v -> forall z, ~ step v z.
Proof.
  intros v Hv. induction Hv; intros z Hs; inversion Hs; subst; eauto.
  all: match goal with H : step ?a ?b, IH : forall z, ~ step ?a z |- False => exact (IH b H) end.
Qed.

Lemma step_det : forall a b, step a b -> forall z, step a z -> b = z.
Proof.
  intros a b H. induction H; intros z H2; inversion H2; subst;
    try reflexivity; try discriminate; try (f_equal; eauto).
  all: exfalso.
  all: try (multimatch goal with Hs : step ?t ?b |- False =>
         (assert (Hv : value t) by (eauto using value_unit, value_lit, value_abs, value_pair, value_rcd, value_cabs, value_cpair, value_topArr);
          exact (@value_no_step t Hv b Hs)) end).
Qed.

Lemma star_from_value : forall e e', value e -> (step star) e e' -> e' = e.
Proof.
  intros e e' Hv H. induction H.
  - reflexivity.
  - exfalso. eapply value_no_step; eauto.
Qed.

Lemma star_value_det : forall a v, (step star) a v -> value v -> forall w, (step star) a w -> value w -> v = w.
Proof.
  intros a v H. induction H; intros Hv w Hw Hvalw.
  - symmetry. eapply star_from_value; eauto.
  - inversion Hw; subst.
    all: try (exfalso; eapply value_no_step; [exact Hvalw | exact H]).
    all: try (match goal with H1 : step _ ?b0, H2 : ?b0 ->* _ |- _ =>
                assert (b = b0) by (eapply step_det; eauto); subst b0 end).
    all: try (eapply IHstar; eauto).
Qed.

Lemma star_trans : forall (R:Infrastructure.relation) a b c, (R star) a b -> (R star) b c -> (R star) a c.
Proof. intros R a b c H1. induction H1; intros H2.
- exact H2.
- eapply star_step. apply H. apply IHstar. exact H2. Qed.

Lemma star_capp : forall c e e', (step star) e e' -> (step star) (trm_capp c e) (trm_capp c e').
Proof. intros c e e' H. induction H.
- constructor.
- eapply star_step. apply step_capp. apply H. apply IHstar. Qed.

Lemma star_app_l : forall e1 e1' e2, (step star) e1 e1' -> lc_exp e2 -> (step star) (trm_app e1 e2) (trm_app e1' e2).
Proof. intros e1 e1' e2 H. induction H; intros Hlc.
- constructor.
- eapply (star_step step (trm_app a e2) (trm_app b e2) (trm_app c e2)).
  apply step_app1; assumption. apply IHstar; assumption. Qed.

Lemma star_app_r : forall v e2 e2', value v -> (step star) e2 e2' -> (step star) (trm_app v e2) (trm_app v e2').
Proof. intros v e2 e2' Hv H. induction H.
- constructor.
- eapply (star_step step (trm_app v a) (trm_app v b) (trm_app v c)).
  apply step_app2; assumption. apply IHstar. Qed.

Lemma star_rcd : forall l e e', (step star) e e' -> (step star) (trm_rcd l e) (trm_rcd l e').
Proof. intros l e e' H. induction H.
- constructor.
- eapply (star_step step (trm_rcd l a) (trm_rcd l b) (trm_rcd l c)).
  apply step_rcd1. apply H. apply IHstar. Qed.

Lemma star_proj : forall l e e', (step star) e e' -> (step star) (trm_proj e l) (trm_proj e' l).
Proof. intros l e e' H. induction H.
- constructor.
- eapply (star_step step (trm_proj a l) (trm_proj b l) (trm_proj c l)).
  apply step_rcd2. apply H. apply IHstar. Qed.

Lemma star_pair_l : forall e1 e1' e2, (step star) e1 e1' -> lc_exp e2 -> (step star) (trm_pair e1 e2) (trm_pair e1' e2).
Proof. intros e1 e1' e2 H. induction H; intros Hlc.
- constructor.
- eapply (star_step step (trm_pair a e2) (trm_pair b e2) (trm_pair c e2)).
  apply step_pair1; assumption. apply IHstar; assumption. Qed.

Lemma star_pair_r : forall v1 e2 e2', value v1 -> (step star) e2 e2' -> (step star) (trm_pair v1 e2) (trm_pair v1 e2').
Proof. intros v1 e2 e2' Hv H. induction H.
- constructor.
- eapply (star_step step (trm_pair v1 a) (trm_pair v1 b) (trm_pair v1 c)).
  apply step_pair2; assumption. apply IHstar. Qed.

Fixpoint WF (A:styp) : exp -> Prop :=
  match A with
  | styp_top => fun v => v = trm_unit
  | styp_nat => fun v => exists k, v = trm_lit k
  | styp_and A1 A2 => fun v => exists a b, v = trm_pair a b /\ WF A1 a /\ WF A2 b
  | styp_rcd l A1 => fun v => exists a, v = trm_rcd l a /\ WF A1 a
  | styp_arrow A1 A2 => fun v =>
      lc_exp v /\ value v /\
      (forall u1 u2, WF A1 u1 -> WF A1 u2 -> AE A1 u1 u2 ->
         exists w1 w2, (step star) (trm_app v u1) w1 /\ (step star) (trm_app v u2) w2 /\
                       WF A2 w1 /\ WF A2 w2 /\ AE A2 w1 w2)
  end
with AE (A:styp) : exp -> exp -> Prop :=
  match A with
  | styp_top => fun v1 v2 => v1 = trm_unit /\ v2 = trm_unit
  | styp_nat => fun v1 v2 => exists k, v1 = trm_lit k /\ v2 = trm_lit k
  | styp_and A1 A2 => fun v1 v2 => exists a1 b1 a2 b2,
        v1 = trm_pair a1 b1 /\ v2 = trm_pair a2 b2 /\ AE A1 a1 a2 /\ AE A2 b1 b2
  | styp_rcd l A1 => fun v1 v2 => exists a1 a2, v1 = trm_rcd l a1 /\ v2 = trm_rcd l a2 /\ AE A1 a1 a2
  | styp_arrow A1 A2 => fun v1 v2 =>
      lc_exp v1 /\ lc_exp v2 /\ value v1 /\ value v2 /\
      (forall u1 u2, WF A1 u1 -> WF A1 u2 -> AE A1 u1 u2 ->
         exists w1 w2, (step star) (trm_app v1 u1) w1 /\ (step star) (trm_app v2 u2) w2 /\
                       WF A2 w1 /\ WF A2 w2 /\ AE A2 w1 w2)
  end.

Definition V (A:styp) (v1 v2:exp) : Prop := WF A v1 /\ WF A v2 /\ AE A v1 v2.
Definition E (A:styp) (e1 e2:exp) : Prop :=
  exists v1 v2, (step star) e1 v1 /\ (step star) e2 v2 /\ WF A v1 /\ WF A v2 /\ AE A v1 v2.

Lemma WF_value : forall A v, WF A v -> value v.
Proof.
  intros A. induction A; intros v H; simpl in H.
  - subst; apply value_unit.
  - destruct H as [k Hk]; subst; apply value_lit.
  - destruct H as [a [b [He [Ha Hb]]]]; subst; apply value_pair; auto.
  - destruct H as [Hlc [Hv _]]; exact Hv.
  - destruct H as [a [He Ha]]; subst; apply value_rcd; auto.
Qed.

Lemma WF_lc : forall A v, WF A v -> lc_exp v.
Proof.
  intros A. induction A; intros v H; simpl in H.
  - subst; constructor.
  - destruct H as [k Hk]; subst; constructor.
  - destruct H as [a [b [He [Ha Hb]]]]; subst; constructor; auto.
  - destruct H as [Hlc _]; exact Hlc.
  - destruct H as [a [He Ha]]; subst; constructor; auto.
Qed.

Lemma WF_star : forall A e e', (step star) e e' -> WF A e -> WF A e'.
Proof.
  intros A e e' H. induction H; intros Hw; auto.
  exfalso. eapply value_no_step. eapply WF_value; eauto. eauto.
Qed.

Lemma E_WF_l : forall A e1 e2, E A e1 e2 -> exists v, (step star) e1 v /\ WF A v.
Proof. intros A e1 e2 [v1 [v2 [H1 [H2 [W1 _]]]]]. exists v1; auto. Qed.
Lemma E_WF_r : forall A e1 e2, E A e1 e2 -> exists v, (step star) e2 v /\ WF A v.
Proof. intros A e1 e2 [v1 [v2 [H1 [H2 [_ [W2 _]]]]]]. exists v2; auto. Qed.

Lemma AE_refl : forall A v, WF A v -> AE A v v.
Proof.
  intros A. induction A; intros v H; simpl in *.
  - subst; auto.
  - destruct H as [k Hk]; subst; eauto.
  - destruct H as [a [b [He [Ha Hb]]]]; subst. exists a, b, a, b; simpl; auto.
  - destruct H as [Hlc [Hv Hap]]. repeat split; auto.
  - destruct H as [a [He Ha]]; subst. exists a, a; auto.
Qed.

Lemma AE_sym : forall A v1 v2, AE A v1 v2 -> AE A v2 v1.
Proof.
  induction A as [| |A1 IH1 A2 IH2| A1 IH1 A2 IH2| l A1 IH1]; simpl; intros v1 v2 H.
  - destruct H as [H1 H2]; auto.
  - destruct H as [k [H1 H2]]; eauto.
  - destruct H as [a1 [b1 [a2 [b2 [H1 [H2 [X Y]]]]]]].
    exists a2, b2, a1, b1. simpl. repeat split; auto.
  - destruct H as [Hl1 [Hl2 [Hv1 [Hv2 Hap]]]]. repeat split; auto.
    intros u1 u2 W1 W2 A12.
    destruct (Hap u2 u1 W2 W1 (IH1 u1 u2 A12)) as [wa [wb [Sa [Sb [Wa [Wb A]]]]]].
    exists wb, wa; repeat split; auto.
  - destruct H as [a1 [a2 [H1 [H2 X]]]].
    exists a2, a1. simpl. repeat split; auto.
Qed.

Lemma E_sym : forall A e1 e2, E A e1 e2 -> E A e2 e1.
Proof.
  intros A e1 e2 [v1 [v2 [H1 [H2 [W1 [W2 AE1]]]]]].
  exists v2, v1; repeat split; auto. apply AE_sym; auto.
Qed.

Lemma AE_trans : forall A v1 v2 v3, WF A v1 -> WF A v2 -> WF A v3 ->
  AE A v1 v2 -> AE A v2 v3 -> AE A v1 v3.
Proof.
  induction A as [| |A1 IH1 A2 IH2| A1 IH1 A2 IH2| l A1 IH1]; simpl;
    intros v1 v2 v3 W1 W2 W3 H12 H23.
  - destruct H12 as [H1 _]; destruct H23 as [_ H3]; auto.
  - destruct H12 as [k1 [H1 H2]]; destruct H23 as [k2 [H2' H3]].
    assert (k1 = k2) by congruence; subst; eauto.
  - destruct H12 as [a1 [b1 [a2 [b2 [H1 [H2 [X12 Y12]]]]]]].
    destruct H23 as [a2x [b2x [a3 [b3 [H2x [H3 [X23 Y23]]]]]]].
    assert (a2 = a2x) by congruence. assert (b2 = b2x) by congruence. subst a2x b2x.
    simpl in W1. destruct W1 as [a1w [b1w [E1 [Wa1 Wb1]]]].
    simpl in W2. destruct W2 as [a2w [b2w [E2 [Wa2 Wb2]]]].
    simpl in W3. destruct W3 as [a3w [b3w [E3 [Wa3 Wb3]]]].
    assert (a1 = a1w) by congruence. assert (b1 = b1w) by congruence. subst a1w b1w.
    assert (a2 = a2w) by congruence. assert (b2 = b2w) by congruence. subst a2w b2w.
    assert (a3 = a3w) by congruence. assert (b3 = b3w) by congruence. subst a3w b3w.
    exists a1, b1, a3, b3. simpl. repeat split; auto.
    + exact (IH1 a1 a2 a3 Wa1 Wa2 Wa3 X12 X23).
    + exact (IH2 b1 b2 b3 Wb1 Wb2 Wb3 Y12 Y23).
  - destruct H12 as [Hl1 [Hl2 [Hv1 [Hv2 Hap12]]]].
    destruct H23 as [Hl2x [Hl3 [Hv2x [Hv3 Hap23]]]].
    repeat split; auto.
    intros u1 u2 Wu1 Wu2 Au.
    destruct (Hap12 u1 u2 Wu1 Wu2 Au) as [w1 [w2 [S1 [S2 [Ww1 [Ww2 AEw]]]]]].
    destruct (Hap23 u2 u2 Wu2 Wu2 (AE_refl A1 u2 Wu2)) as [x2 [w3 [T2 [T3 [Wx2 [Ww3 AEw23]]]]]].
    assert (w2 = x2) by (exact (@star_value_det (trm_app v2 u2) w2 S2 (WF_value A2 w2 Ww2) x2 T2 (WF_value A2 x2 Wx2))). subst x2.
    exists w1, w3; repeat split; auto.
    exact (IH2 w1 w2 w3 Ww1 Ww2 Ww3 AEw AEw23).
  - destruct H12 as [a1 [a2 [H1 [H2 X12]]]].
    destruct H23 as [a2x [a3 [H2x [H3 X23]]]].
    assert (a2 = a2x) by congruence; subst a2x.
    simpl in W1. destruct W1 as [a1w [E1 Wa1]].
    simpl in W2. destruct W2 as [a2w [E2 Wa2]].
    simpl in W3. destruct W3 as [a3w [E3 Wa3]].
    assert (a1 = a1w) by congruence; subst a1w.
    assert (a2 = a2w) by congruence; subst a2w.
    assert (a3 = a3w) by congruence; subst a3w.
    exists a1, a3. simpl. repeat split; auto.
    exact (IH1 a1 a2 a3 Wa1 Wa2 Wa3 X12 X23).
Qed.

Lemma E_trans : forall A a b c, E A a b -> E A b c -> E A a c.
Proof.
  intros A a b c [v1 [v2 [H1 [H2 [W1 [W2 A12]]]]]] [v2' [v3 [H2' [H3 [W2' [W3 A23]]]]]].
  assert (v2 = v2') by (exact (@star_value_det b v2 H2 (WF_value A v2 W2) v2' H2' (WF_value A v2' W2'))). subst v2'.
  exists v1, v3; repeat split; auto.
  exact (AE_trans A v1 v2 v3 W1 W2 W3 A12 A23).
Qed.

Lemma V_E : forall A v1 v2, V A v1 v2 -> E A v1 v2.
Proof.
  intros A v1 v2 [W1 [W2 AE1]]. exists v1, v2; repeat split; auto; apply star_refl.
Qed.

Lemma WF_arrow_top_top_val : WF (styp_arrow styp_top styp_top) (trm_capp co_topArr trm_unit).
Proof.
  simpl. split; [|split].
  - apply lc_trm_capp; constructor.
  - apply value_topArr; apply value_unit.
  - intros u1 u2 W1 W2 A. simpl in W1, W2. subst u1 u2.
    exists trm_unit, trm_unit. repeat split; auto.
    all: try (simpl; auto).
    all: try (apply star_step with (b:=trm_unit); [apply step_topArr | constructor]).
Qed.

Lemma WF_rcd_top_val : forall l, WF (styp_rcd l styp_top) (trm_rcd l trm_unit).
Proof. intros l. simpl. exists trm_unit. split; auto. Qed.

Lemma AE_of_WF : forall A v, WF A v -> AE A v v. Proof. exact AE_refl. Qed.

Lemma sub_coherent : forall A B c, sub A B c ->
  (forall v, WF A v -> exists w, (step star) (trm_capp c v) w /\ WF B w) /\
  (forall v1 v2, WF A v1 -> WF A v2 -> AE A v1 v2 ->
     exists w1 w2, (step star) (trm_capp c v1) w1 /\ (step star) (trm_capp c v2) w2 /\
                   WF B w1 /\ WF B w2 /\ AE B w1 w2).
Proof.
  intros A B c Hsub. induction Hsub; simpl.
  - (* S_refl *)
    split.
    + intros v W. exists v. split.
      * apply star_step with (b:=v). apply step_id. eapply WF_value; eauto. constructor.
      * exact W.
    + intros v1 v2 W1 W2 AE12. exists v1, v2. split; [|split;[|split;[|split]]].
      * apply star_step with (b:=v1). apply step_id. eapply WF_value; eauto. constructor.
      * apply star_step with (b:=v2). apply step_id. eapply WF_value; eauto. constructor.
      * exact W1. * exact W2. * exact AE12.
  - (* S_trans *)
    split.
    + intros v W. destruct ((proj1 IHHsub2) v W) as [w2 [S2 W2]].
      destruct ((proj1 IHHsub1) w2 W2) as [w [S1 W1]].
      exists w. split; auto.
      eapply star_trans.
      * apply star_step with (b := trm_capp c1 (trm_capp c2 v)).
        apply step_trans; eapply WF_value; eauto. constructor.
      * eapply star_trans. apply star_capp; exact S2. exact S1.
    + intros v1 v2 W1 W2 AE12. destruct ((proj2 IHHsub2) v1 v2 W1 W2 AE12) as [w1 [w2 [S1 [S2 [Ww1 [Ww2 AEw]]]]]].
      destruct ((proj2 IHHsub1) w1 w2 Ww1 Ww2 AEw) as [z1 [z2 [T1 [T2 [Wz1 [Wz2 AEz]]]]]].
      exists z1, z2. split; [|split;[|split;[|split]]].
      * eapply star_trans.
        -- apply star_step with (b := trm_capp c1 (trm_capp c2 v1)).
           apply step_trans; eapply WF_value; eauto. constructor.
        -- eapply star_trans. apply star_capp; exact S1. exact T1.
      * eapply star_trans.
        -- apply star_step with (b := trm_capp c1 (trm_capp c2 v2)).
           apply step_trans; eapply WF_value; eauto. constructor.
        -- eapply star_trans. apply star_capp; exact S2. exact T2.
      * exact Wz1. * exact Wz2. * exact AEz.
  - (* S_top *)
    split.
    + intros v W. exists trm_unit. split.
      * apply star_step with (b:=trm_unit). apply step_top; eapply WF_value; eauto. constructor.
      * simpl; reflexivity.
    + intros v1 v2 W1 W2 AE12. exists trm_unit, trm_unit.
      split; [|split;[|split;[|split]]].
      * apply star_step with (b:=trm_unit). apply step_top; eapply WF_value; eauto. constructor.
      * apply star_step with (b:=trm_unit). apply step_top; eapply WF_value; eauto. constructor.
      * simpl; reflexivity. * simpl; reflexivity. * simpl; auto.
  - (* S_topArr *)
    split.
    + intros v W. simpl in W. subst v. exists (trm_capp co_topArr trm_unit). split.
      * constructor.
      * exact WF_arrow_top_top_val.
    + intros v1 v2 W1 W2 AE12. simpl in W1, W2. subst v1 v2.
      exists (trm_capp co_topArr trm_unit), (trm_capp co_topArr trm_unit). split; [|split;[|split;[|split]]].
      * constructor. * constructor.
      * exact WF_arrow_top_top_val. * exact WF_arrow_top_top_val.
      * exact (AE_of_WF _ _ WF_arrow_top_top_val).
  - (* S_topRcd *)
    split.
    + intros v W. simpl in W. subst v. exists (trm_rcd l trm_unit). split.
      * apply star_step with (b:=trm_rcd l trm_unit). apply step_topRcd. constructor.
      * apply WF_rcd_top_val.
    + intros v1 v2 W1 W2 AE12. simpl in W1, W2. subst v1 v2.
      exists (trm_rcd l trm_unit), (trm_rcd l trm_unit). split; [|split;[|split;[|split]]].
      * apply star_step with (b:=trm_rcd l trm_unit). apply step_topRcd. constructor.
      * apply star_step with (b:=trm_rcd l trm_unit). apply step_topRcd. constructor.
      * apply WF_rcd_top_val. * apply WF_rcd_top_val.
      * exact (AE_of_WF _ _ (WF_rcd_top_val l)).
  - (* S_arr *)
    split.
    + intros v W. simpl in W. destruct W as [Wlc [Wv Wap]].
      exists (trm_capp (co_arr c1 c2) v). split.
      * constructor.
      * simpl. split; [|split].
        -- apply lc_trm_capp; assumption.
        -- apply value_cabs; assumption.
        -- intros u1 u2 Wu1 Wu2 Wu12.
           destruct ((proj1 IHHsub1) u1 Wu1) as [t1 [T1 Wt1]].
           destruct ((proj1 IHHsub1) u2 Wu2) as [t2 [T2 Wt2]].
           assert (AE1 : AE A1 t1 t2).
           { destruct ((proj2 IHHsub1) u1 u2 Wu1 Wu2 Wu12) as [x1 [x2 [S1 [S2 [Wx1 [Wx2 Ax]]]]]].
             assert (x1 = t1) by (exact (@star_value_det (trm_capp c1 u1) x1 S1 (WF_value A1 x1 Wx1) t1 T1 (WF_value A1 t1 Wt1))).
             assert (x2 = t2) by (exact (@star_value_det (trm_capp c1 u2) x2 S2 (WF_value A1 x2 Wx2) t2 T2 (WF_value A1 t2 Wt2))).
             subst x1 x2. exact Ax. }
           destruct (Wap t1 t2 Wt1 Wt2 AE1) as [s1 [s2 [Ss1 [Ss2 [Ws1 [Ws2 As]]]]]].
           destruct ((proj2 IHHsub2) s1 s2 Ws1 Ws2 As) as [z1 [z2 [Z1 [Z2 [Wz1 [Wz2 Az]]]]]].
           exists z1, z2. split; [|split;[|split;[|split]]].
           ++ eapply star_trans.
              { apply star_step with (b := trm_capp c2 (trm_app v (trm_capp c1 u1))).
                apply step_arr; [exact Wv | eapply WF_value; eauto]. constructor. }
              eapply star_trans.
              { apply star_capp. apply star_app_r; [exact Wv | exact T1]. }
              eapply star_trans.
              { apply star_capp. exact Ss1. }
              exact Z1.
           ++ eapply star_trans.
              { apply star_step with (b := trm_capp c2 (trm_app v (trm_capp c1 u2))).
                apply step_arr; [exact Wv | eapply WF_value; eauto]. constructor. }
              eapply star_trans.
              { apply star_capp. apply star_app_r; [exact Wv | exact T2]. }
              eapply star_trans.
              { apply star_capp. exact Ss2. }
              exact Z2.
           ++ exact Wz1. ++ exact Wz2. ++ exact Az.
    + intros v1 v2 W1 W2 AE12. simpl in W1, W2, AE12.
      destruct W1 as [Wl1 [Wv1 Wap1]]. destruct W2 as [Wl2 [Wv2 Wap2]].
      assert (W1' : WF (styp_arrow A1 A2) v1) by (split; [exact Wl1 | split; [exact Wv1 | exact Wap1]]).
      assert (W2' : WF (styp_arrow A1 A2) v2) by (split; [exact Wl2 | split; [exact Wv2 | exact Wap2]]).
      destruct AE12 as [Al1 [Al2 [Av1 [Av2 Aap]]]].
      assert (Hstep : forall vA vB, WF (styp_arrow A1 A2) vA -> WF (styp_arrow A1 A2) vB ->
        (forall u1 u2, WF A1 u1 -> WF A1 u2 -> AE A1 u1 u2 ->
           exists s1 s2, (step star) (trm_app vA u1) s1 /\ (step star) (trm_app vB u2) s2 /\
                         WF A2 s1 /\ WF A2 s2 /\ AE A2 s1 s2) ->
        forall u1 u2, WF B1 u1 -> WF B1 u2 -> AE B1 u1 u2 ->
           exists z1 z2, (step star) (trm_app (trm_capp (co_arr c1 c2) vA) u1) z1 /\
                         (step star) (trm_app (trm_capp (co_arr c1 c2) vB) u2) z2 /\
                         WF B2 z1 /\ WF B2 z2 /\ AE B2 z1 z2).
      { intros vA vB WA WB Hap u1 u2 Wu1 Wu2 Wu12.
        assert (WAv : value vA) by (eapply WF_value; eauto).
        assert (WBv : value vB) by (eapply WF_value; eauto).
        destruct ((proj2 IHHsub1) u1 u2 Wu1 Wu2 Wu12) as [t1 [t2 [T1 [T2 [Wt1 [Wt2 Ax]]]]]].
        destruct (Hap t1 t2 Wt1 Wt2 Ax) as [s1 [s2 [Ss1 [Ss2 [Ws1 [Ws2 As]]]]]].
        destruct ((proj2 IHHsub2) s1 s2 Ws1 Ws2 As) as [z1 [z2 [Z1 [Z2 [Wz1 [Wz2 Az]]]]]].
        exists z1, z2. split; [|split;[|split;[|split]]].
        ++ eapply star_trans.
           { apply star_step with (b := trm_capp c2 (trm_app vA (trm_capp c1 u1))).
             apply step_arr; [exact WAv | eapply WF_value; eauto]. constructor. }
           eapply star_trans.
           { apply star_capp. apply star_app_r; [exact WAv | exact T1]. }
           eapply star_trans.
           { apply star_capp. exact Ss1. }
           exact Z1.
        ++ eapply star_trans.
           { apply star_step with (b := trm_capp c2 (trm_app vB (trm_capp c1 u2))).
             apply step_arr; [exact WBv | eapply WF_value; eauto]. constructor. }
           eapply star_trans.
           { apply star_capp. apply star_app_r; [exact WBv | exact T2]. }
           eapply star_trans.
           { apply star_capp. exact Ss2. }
           exact Z2.
        ++ exact Wz1. ++ exact Wz2. ++ exact Az. }
      exists (trm_capp (co_arr c1 c2) v1), (trm_capp (co_arr c1 c2) v2).
      split; [|split;[|split;[|split]]].
      * constructor. * constructor.
      * simpl. split; [|split].
        -- apply lc_trm_capp; assumption.
        -- apply value_cabs; assumption.
        -- exact (Hstep v1 v1 W1' W1' Wap1).
      * simpl. split; [|split].
        -- apply lc_trm_capp; assumption.
        -- apply value_cabs; assumption.
        -- exact (Hstep v2 v2 W2' W2' Wap2).
      * simpl. split; [|split;[|split;[|split]]].
        -- apply lc_trm_capp; assumption.
        -- apply lc_trm_capp; assumption.
        -- apply value_cabs; assumption.
        -- apply value_cabs; assumption.
        -- exact (Hstep v1 v2 W1' W2' Aap).
  - (* S_and *)
    split.
    + intros v W. destruct ((proj1 IHHsub1) v W) as [w1 [S1 W1]].
      destruct ((proj1 IHHsub2) v W) as [w2 [S2 W2]].
      exists (trm_pair w1 w2). split.
      * eapply star_trans.
        { apply star_step with (b := trm_pair (trm_capp c1 v) (trm_capp c2 v)).
          apply step_pair; eapply WF_value; eauto. constructor. }
        eapply star_trans.
        { apply star_pair_l; [exact S1 | apply lc_trm_capp; eapply WF_lc; eauto]. }
        apply star_pair_r; [eapply WF_value; eauto | exact S2].
      * simpl. exists w1, w2. split; [reflexivity | split; assumption].
    + intros v1 v2 W1 W2 AE12.
      destruct ((proj2 IHHsub1) v1 v2 W1 W2 AE12) as [a1 [a2 [S1 [S2 [Wa1 [Wa2 Aa]]]]]].
      destruct ((proj2 IHHsub2) v1 v2 W1 W2 AE12) as [b1 [b2 [T1 [T2 [Wb1 [Wb2 Ab]]]]]].
      exists (trm_pair a1 b1), (trm_pair a2 b2).
      split; [|split;[|split;[|split]]].
      * eapply star_trans.
        { apply star_step with (b := trm_pair (trm_capp c1 v1) (trm_capp c2 v1)).
          apply step_pair; eapply WF_value; eauto. constructor. }
        eapply star_trans.
        { apply star_pair_l; [exact S1 | apply lc_trm_capp; eapply WF_lc; eauto]. }
        apply star_pair_r; [eapply WF_value; eauto | exact T1].
      * eapply star_trans.
        { apply star_step with (b := trm_pair (trm_capp c1 v2) (trm_capp c2 v2)).
          apply step_pair; eapply WF_value; eauto. constructor. }
        eapply star_trans.
        { apply star_pair_l; [exact S2 | apply lc_trm_capp; eapply WF_lc; eauto]. }
        apply star_pair_r; [eapply WF_value; eauto | exact T2].
      * simpl. exists a1, b1. split; [reflexivity | split; assumption].
      * simpl. exists a2, b2. split; [reflexivity | split; assumption].
      * simpl. exists a1, b1, a2, b2. split; [reflexivity | split; [reflexivity | split; assumption]].
  - (* S_andl *)
    split.
    + intros v W. simpl in W. destruct W as [a [b [E [Wa Wb]]]]. subst v.
      exists a. split.
      * apply star_step with (b:=a). apply step_projl; eapply WF_value; eauto. constructor.
      * exact Wa.
    + intros v1 v2 W1 W2 AE12. simpl in W1, W2, AE12.
      destruct W1 as [a1 [b1 [E1 [Wa1 Wb1]]]]. subst v1.
      destruct W2 as [a2 [b2 [E2 [Wa2 Wb2]]]]. subst v2.
      destruct AE12 as [a1' [b1' [a2' [b2' [F1 [F2 [Aa Ab]]]]]]].
      assert (a1 = a1') by congruence. assert (a2 = a2') by congruence. subst a1' a2'.
      exists a1, a2. split; [|split;[|split;[|split]]].
      * apply star_step with (b:=a1). apply step_projl; eapply WF_value; eauto. constructor.
      * apply star_step with (b:=a2). apply step_projl; eapply WF_value; eauto. constructor.
      * exact Wa1. * exact Wa2. * exact Aa.
  - (* S_andr *)
    split.
    + intros v W. simpl in W. destruct W as [a [b [E [Wa Wb]]]]. subst v.
      exists b. split.
      * apply star_step with (b:=b). apply step_projr; eapply WF_value; eauto. constructor.
      * exact Wb.
    + intros v1 v2 W1 W2 AE12. simpl in W1, W2, AE12.
      destruct W1 as [a1 [b1 [E1 [Wa1 Wb1]]]]. subst v1.
      destruct W2 as [a2 [b2 [E2 [Wa2 Wb2]]]]. subst v2.
      destruct AE12 as [a1' [b1' [a2' [b2' [F1 [F2 [Aa Ab]]]]]]].
      assert (b1 = b1') by congruence. assert (b2 = b2') by congruence. subst b1' b2'.
      exists b1, b2. split; [|split;[|split;[|split]]].
      * apply star_step with (b:=b1). apply step_projr; eapply WF_value; eauto. constructor.
      * apply star_step with (b:=b2). apply step_projr; eapply WF_value; eauto. constructor.
      * exact Wb1. * exact Wb2. * exact Ab.
  - (* S_distArr *)
    split.
    + intros v W. simpl in W. destruct W as [f [g [E [Wf Wg]]]]. subst v.
      assert (Wf' : WF (styp_arrow A1 A2) f) by exact Wf.
      assert (Wg' : WF (styp_arrow A1 A3) g) by exact Wg.
      destruct Wf' as [Wflc [Wfv Wfap]]. destruct Wg' as [Wglc [Wgv Wgap]].
      exists (trm_capp co_distArr (trm_pair f g)). split.
      * constructor.
      * simpl. split; [|split].
        -- apply lc_trm_capp; apply lc_trm_pair; auto.
        -- apply value_cpair; apply value_pair; assumption.
        -- intros u1 u2 Wu1 Wu2 Wu12.
           destruct (Wfap u1 u2 Wu1 Wu2 Wu12) as [s1 [s2 [S1 [S2 [Ws1 [Ws2 As]]]]]].
           destruct (Wgap u1 u2 Wu1 Wu2 Wu12) as [t1 [t2 [T1 [T2 [Wt1 [Wt2 At]]]]]].
           exists (trm_pair s1 t1), (trm_pair s2 t2).
           split; [|split;[|split;[|split]]].
           ++ eapply star_trans.
              { apply star_step with (b := trm_pair (trm_app f u1) (trm_app g u1)).
                apply step_distArr; [exact Wfv | exact Wgv | eapply WF_value; eauto]. constructor. }
              eapply star_trans.
              { apply star_pair_l; [exact S1 | apply lc_trm_app; [exact Wglc | eapply WF_lc; eauto]]. }
              apply star_pair_r; [eapply WF_value; eauto | exact T1].
           ++ eapply star_trans.
              { apply star_step with (b := trm_pair (trm_app f u2) (trm_app g u2)).
                apply step_distArr; [exact Wfv | exact Wgv | exact (WF_value A1 u2 Wu2)]. constructor. }
              eapply star_trans.
              { apply star_pair_l; [exact S2 | apply lc_trm_app; [exact Wglc | eapply WF_lc; eauto]]. }
              apply star_pair_r; [eapply WF_value; eauto | exact T2].
           ++ simpl. exists s1, t1. split; [reflexivity|split; assumption].
           ++ simpl. exists s2, t2. split; [reflexivity|split; assumption].
           ++ simpl. exists s1, t1, s2, t2. split; [reflexivity|split; [reflexivity|split; assumption]].
    + intros v1 v2 W1 W2 AE12. simpl in W1, W2, AE12.
      destruct W1 as [f1 [g1 [E1 [Wf1 Wg1]]]]. subst v1.
      destruct W2 as [f2 [g2 [E2 [Wf2 Wg2]]]]. subst v2.
      assert (Wf1' : WF (styp_arrow A1 A2) f1) by exact Wf1.
      assert (Wg1' : WF (styp_arrow A1 A3) g1) by exact Wg1.
      assert (Wf2' : WF (styp_arrow A1 A2) f2) by exact Wf2.
      assert (Wg2' : WF (styp_arrow A1 A3) g2) by exact Wg2.
      destruct Wf1' as [Wf1lc [Wf1v Wf1ap]]. destruct Wg1' as [Wg1lc [Wg1v Wg1ap]].
      destruct Wf2' as [Wf2lc [Wf2v Wf2ap]]. destruct Wg2' as [Wg2lc [Wg2v Wg2ap]].
      destruct AE12 as [f1x [g1x [f2x [g2x [F1 [F2 [Af Ag]]]]]]].
      assert (f1 = f1x) by congruence. assert (g1 = g1x) by congruence.
      assert (f2 = f2x) by congruence. assert (g2 = g2x) by congruence. subst f1x g1x f2x g2x.
      destruct Af as [Af1lc [Af2lc [Af1v [Af2v Afap]]]].
      destruct Ag as [Ag1lc [Ag2lc [Ag1v [Ag2v Agap]]]].
      assert (Hred2 : forall (fA fB gA gB : exp)
        (vfA : value fA) (vgA : value gA) (vfB : value fB) (vgB : value gB)
        (lcfA : lc_exp fA) (lcgA : lc_exp gA) (lcfB : lc_exp fB) (lcgB : lc_exp gB)
        (Cff : forall u1 u2, WF A1 u1 -> WF A1 u2 -> AE A1 u1 u2 ->
                 exists s1 s2, (step star) (trm_app fA u1) s1 /\ (step star) (trm_app fB u2) s2 /\
                               WF A2 s1 /\ WF A2 s2 /\ AE A2 s1 s2)
        (Cgg : forall u1 u2, WF A1 u1 -> WF A1 u2 -> AE A1 u1 u2 ->
                 exists t1 t2, (step star) (trm_app gA u1) t1 /\ (step star) (trm_app gB u2) t2 /\
                               WF A3 t1 /\ WF A3 t2 /\ AE A3 t1 t2),
        forall u1 u2, WF A1 u1 -> WF A1 u2 -> AE A1 u1 u2 ->
          exists z1 z2, (step star) (trm_app (trm_capp co_distArr (trm_pair fA gA)) u1) z1 /\
                        (step star) (trm_app (trm_capp co_distArr (trm_pair fB gB)) u2) z2 /\
                        WF (styp_and A2 A3) z1 /\ WF (styp_and A2 A3) z2 /\
                        AE (styp_and A2 A3) z1 z2).
      { intros fA fB gA gB vfA vgA vfB vgB lcfA lcgA lcfB lcgB Cff Cgg u1 u2 Wu1 Wu2 Wu12.
        destruct (Cff u1 u2 Wu1 Wu2 Wu12) as [s1 [s2 [S1 [S2 [Ws1 [Ws2 As]]]]]].
        destruct (Cgg u1 u2 Wu1 Wu2 Wu12) as [t1 [t2 [T1 [T2 [Wt1 [Wt2 At]]]]]].
        exists (trm_pair s1 t1), (trm_pair s2 t2).
        split; [|split;[|split;[|split]]].
        ++ eapply star_trans.
           { apply star_step with (b := trm_pair (trm_app fA u1) (trm_app gA u1)).
             apply step_distArr; [exact vfA | exact vgA | eapply WF_value; eauto]. constructor. }
           eapply star_trans.
           { apply star_pair_l; [exact S1 | apply lc_trm_app; [exact lcgA | eapply WF_lc; eauto]]. }
           apply star_pair_r; [eapply WF_value; eauto | exact T1].
        ++ eapply star_trans.
           { apply star_step with (b := trm_pair (trm_app fB u2) (trm_app gB u2)).
             apply step_distArr; [exact vfB | exact vgB | eapply WF_value; eauto]. constructor. }
           eapply star_trans.
           { apply star_pair_l; [exact S2 | apply lc_trm_app; [exact lcgB | eapply WF_lc; eauto]]. }
           apply star_pair_r; [eapply WF_value; eauto | exact T2].
        ++ simpl. exists s1, t1. split; [reflexivity|split; assumption].
        ++ simpl. exists s2, t2. split; [reflexivity|split; assumption].
        ++ simpl. exists s1, t1, s2, t2. split; [reflexivity|split; [reflexivity|split; assumption]]. }
      exists (trm_capp co_distArr (trm_pair f1 g1)), (trm_capp co_distArr (trm_pair f2 g2)).
      split; [|split;[|split;[|split]]].
      * constructor. * constructor.
      * simpl. split; [|split].
        -- apply lc_trm_capp; apply lc_trm_pair; auto.
        -- apply value_cpair; apply value_pair; assumption.
        -- exact (Hred2 f1 f1 g1 g1 Wf1v Wg1v Wf1v Wg1v Wf1lc Wg1lc Wf1lc Wg1lc Wf1ap Wg1ap).
      * simpl. split; [|split].
        -- apply lc_trm_capp; apply lc_trm_pair; auto.
        -- apply value_cpair; apply value_pair; assumption.
        -- exact (Hred2 f2 f2 g2 g2 Wf2v Wg2v Wf2v Wg2v Wf2lc Wg2lc Wf2lc Wg2lc Wf2ap Wg2ap).
      * simpl. split; [|split;[|split;[|split]]].
        -- apply lc_trm_capp; apply lc_trm_pair; auto.
        -- apply lc_trm_capp; apply lc_trm_pair; auto.
        -- apply value_cpair; apply value_pair; assumption.
        -- apply value_cpair; apply value_pair; assumption.
        -- exact (Hred2 f1 f2 g1 g2 Wf1v Wg1v Wf2v Wg2v Wf1lc Wg1lc Wf2lc Wg2lc Afap Agap).
  - (* S_rcd *)
    split.
    + intros v W. simpl in W. destruct W as [a [E Wa]]. subst.
      destruct ((proj1 IHHsub) a Wa) as [w [S Ww]].
      exists (trm_rcd l w). split.
      * eapply star_trans.
        { apply star_step with (b := trm_rcd l (trm_capp c a)). apply step_crcd; eapply WF_value; eauto. constructor. }
        apply star_rcd; exact S.
      * simpl. exists w. split; [reflexivity | exact Ww].
    + intros v1 v2 W1 W2 AE12. simpl in W1, W2, AE12.
      destruct W1 as [a1 [E1 Wa1]]. subst. destruct W2 as [a2 [E2 Wa2]]. subst.
      destruct AE12 as [a1x [a2x [F1 [F2 Aa]]]]. assert (a1 = a1x) by congruence. assert (a2 = a2x) by congruence. subst a1x a2x.
      destruct ((proj2 IHHsub) a1 a2 Wa1 Wa2 Aa) as [w1 [w2 [S1 [S2 [Ww1 [Ww2 Aw]]]]]].
      exists (trm_rcd l w1), (trm_rcd l w2).
      split; [|split;[|split;[|split]]].
      * eapply star_trans.
        { apply star_step with (b := trm_rcd l (trm_capp c a1)). apply step_crcd; eapply WF_value; eauto. constructor. }
        apply star_rcd; exact S1.
      * eapply star_trans.
        { apply star_step with (b := trm_rcd l (trm_capp c a2)). apply step_crcd; eapply WF_value; eauto. constructor. }
        apply star_rcd; exact S2.
      * simpl. exists w1. split; [reflexivity | exact Ww1].
      * simpl. exists w2. split; [reflexivity | exact Ww2].
      * simpl. exists w1, w2. split; [reflexivity | split; [reflexivity | exact Aw]].
  - (* S_distRcd *)
    split.
    + intros v W. simpl in W. destruct W as [a [b [E [Wa Wb]]]]. subst v.
      destruct Wa as [a' [Ea Wa']]. destruct Wb as [b' [Eb Wb']].
      assert (a = trm_rcd l a') by congruence. assert (b = trm_rcd l b') by congruence. subst a b.
      exists (trm_rcd l (trm_pair a' b')). split.
      * apply star_step with (b := trm_rcd l (trm_pair a' b')).
        apply step_distRcd; eapply WF_value; eauto. constructor.
      * simpl. exists (trm_pair a' b'). split; [reflexivity | ].
        simpl. exists a', b'. split; [reflexivity | split; assumption].
    + intros v1 v2 W1 W2 AE12. simpl in W1, W2, AE12.
      destruct W1 as [a1 [b1 [E1 [Wa1 Wb1]]]]. subst v1.
      destruct W2 as [a2 [b2 [E2 [Wa2 Wb2]]]]. subst v2.
      destruct Wa1 as [a1' [Ea1 Wa1']]. destruct Wb1 as [b1' [Eb1 Wb1']].
      destruct Wa2 as [a2' [Ea2 Wa2']]. destruct Wb2 as [b2' [Eb2 Wb2']].
      assert (a1 = trm_rcd l a1') by congruence. assert (b1 = trm_rcd l b1') by congruence. subst a1 b1.
      assert (a2 = trm_rcd l a2') by congruence. assert (b2 = trm_rcd l b2') by congruence. subst a2 b2.
      destruct AE12 as [u1 [v1x [u2 [v2x [F1 [F2 [Au Av]]]]]]].
      assert (u1 = trm_rcd l a1') by congruence. assert (u2 = trm_rcd l a2') by congruence. subst u1 u2.
      destruct Au as [s1 [s2 [G1 [G2 Aa]]]]. assert (s1 = a1') by congruence. assert (s2 = a2') by congruence. subst s1 s2.
      destruct Av as [t1 [t2 [J1 [J2 Ab]]]]. assert (t1 = b1') by congruence. assert (t2 = b2') by congruence. subst t1 t2.
      exists (trm_rcd l (trm_pair a1' b1')), (trm_rcd l (trm_pair a2' b2')).
      split; [|split;[|split;[|split]]].
      * apply star_step with (b := trm_rcd l (trm_pair a1' b1')).
        apply step_distRcd; eapply WF_value; eauto. constructor.
      * apply star_step with (b := trm_rcd l (trm_pair a2' b2')).
        apply step_distRcd; eapply WF_value; eauto. constructor.
      * simpl. exists (trm_pair a1' b1'). split; [reflexivity | ].
        simpl. exists a1', b1'. split; [reflexivity | split; assumption].
      * simpl. exists (trm_pair a2' b2'). split; [reflexivity | ].
        simpl. exists a2', b2'. split; [reflexivity | split; assumption].
      * simpl. exists (trm_pair a1' b1'), (trm_pair a2' b2').
        split; [reflexivity | split; [reflexivity | ]].
        simpl. exists a1', b1', a2', b2'. split; [reflexivity | split; [reflexivity | split; assumption]].
Qed.

Lemma SC_same : forall A B c, sub A B c -> forall v1 v2, V A v1 v2 -> E B (trm_capp c v1) (trm_capp c v2).
Proof.
  intros A B c H v1 v2 [W1 [W2 AE12]].
  exact (proj2 (@sub_coherent A B c H) v1 v2 W1 W2 AE12).
Qed.

Fixpoint lcg (n:nat) (e:exp) : Prop :=
  match e with
  | trm_var_b i => i < n
  | trm_var_f _ => True
  | trm_unit => True
  | trm_lit _ => True
  | trm_abs e' => lcg (S n) e'
  | trm_app e1 e2 => lcg n e1 /\ lcg n e2
  | trm_pair e1 e2 => lcg n e1 /\ lcg n e2
  | trm_rcd _ e' => lcg n e'
  | trm_proj e' _ => lcg n e'
  | trm_capp _ e' => lcg n e'
  end.

Lemma size_exp_open_rec : forall e k y, size_exp (open_exp_wrt_exp_rec k (trm_var_f y) e) = size_exp e.
Proof.
  intros e. induction e; intros k y; simpl; auto;
    try (destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; auto);
    try (rewrite IHe; reflexivity);
    try (rewrite IHe1, IHe2; reflexivity).
Qed.

Lemma lcg_open_rec : forall e kk yy, lcg kk (open_exp_wrt_exp_rec kk (trm_var_f yy) e) <-> lcg (S kk) e.
Proof.
  intros ee. induction ee; intros kk yy; simpl.
  - destruct (lt_eq_lt_dec n kk) as [[H1|H1]|H1]; simpl; lia.
  - tauto.
  - tauto.
  - tauto.
  - exact (IHee (S kk) yy).
  - rewrite IHee1, IHee2; tauto.
  - rewrite IHee1, IHee2; tauto.
  - exact (IHee kk yy).
  - exact (IHee kk yy).
  - exact (IHee kk yy).
Qed.

Lemma open_rec_lcg : forall e nn, lcg nn e -> forall kk uu, nn <= kk -> open_exp_wrt_exp_rec kk uu e = e.
Proof.
  intros e. induction e; intros nn H kk uu Hle; simpl in *; auto.
  - destruct (lt_eq_lt_dec n kk) as [[H1|H1]|H1]; auto; lia.
  - rewrite (IHe (S nn) H (S kk) uu ltac:(lia)). reflexivity.
  - destruct H as [H1 H2]. rewrite (IHe1 nn H1 kk uu Hle), (IHe2 nn H2 kk uu Hle). reflexivity.
  - destruct H as [H1 H2]. rewrite (IHe1 nn H1 kk uu Hle), (IHe2 nn H2 kk uu Hle). reflexivity.
  - rewrite (IHe nn H kk uu Hle). reflexivity.
  - rewrite (IHe nn H kk uu Hle). reflexivity.
  - rewrite (IHe nn H kk uu Hle). reflexivity.
Qed.

Lemma lcg_iff_lc : forall e, lcg 0 e <-> lc_exp e.
Proof.
  intros e0. remember (size_exp e0) as n eqn:Eq0. revert e0 Eq0.
  induction n as [n IH] using Wf_nat.lt_wf_ind.
  intros e Eq. destruct e; simpl in *.
  - split; intros H.
    + exfalso; lia.
    + inversion H.
  - split; intros; constructor.
  - split; intros; constructor.
  - split; intros; constructor.
  - split; intros H.
    + apply lc_trm_abs. intros y.
      assert (H0 : lcg 0 (open_exp_wrt_exp e (trm_var_f y))) by (apply (proj2 (lcg_open_rec e 0 y)); simpl; exact H).
      apply (proj1 (IH (size_exp (open_exp_wrt_exp e (trm_var_f y))) ltac:(unfold open_exp_wrt_exp; rewrite size_exp_open_rec; simpl in Eq; lia)
                     (open_exp_wrt_exp e (trm_var_f y)) eq_refl)).
      exact H0.
    + assert (He : forall y, lc_exp (open_exp_wrt_exp e (trm_var_f y))) by (inversion H; assumption).
      apply (proj1 (lcg_open_rec e 0 (proj1_sig (atom_fresh empty)))). simpl.
      apply (proj2 (IH (size_exp (open_exp_wrt_exp e (trm_var_f (proj1_sig (atom_fresh empty)))))
                     ltac:(unfold open_exp_wrt_exp; rewrite size_exp_open_rec; simpl in Eq; lia)
                     (open_exp_wrt_exp e (trm_var_f (proj1_sig (atom_fresh empty)))) eq_refl)).
      apply He.
  - split; intros H.
    + destruct H as [H1 H2]. apply lc_trm_app.
      * apply (proj1 (IH (size_exp e1) ltac:(simpl in Eq; lia) e1 eq_refl)); exact H1.
      * apply (proj1 (IH (size_exp e2) ltac:(simpl in Eq; lia) e2 eq_refl)); exact H2.
    + assert (H1 : lc_exp e1) by (inversion H; assumption).
      assert (H2 : lc_exp e2) by (inversion H; assumption).
      split.
      * apply (proj2 (IH (size_exp e1) ltac:(simpl in Eq; lia) e1 eq_refl)); exact H1.
      * apply (proj2 (IH (size_exp e2) ltac:(simpl in Eq; lia) e2 eq_refl)); exact H2.
  - split; intros H.
    + destruct H as [H1 H2]. apply lc_trm_pair.
      * apply (proj1 (IH (size_exp e1) ltac:(simpl in Eq; lia) e1 eq_refl)); exact H1.
      * apply (proj1 (IH (size_exp e2) ltac:(simpl in Eq; lia) e2 eq_refl)); exact H2.
    + assert (H1 : lc_exp e1) by (inversion H; assumption).
      assert (H2 : lc_exp e2) by (inversion H; assumption).
      split.
      * apply (proj2 (IH (size_exp e1) ltac:(simpl in Eq; lia) e1 eq_refl)); exact H1.
      * apply (proj2 (IH (size_exp e2) ltac:(simpl in Eq; lia) e2 eq_refl)); exact H2.
  - split; intros H.
    + apply lc_trm_rcd. apply (proj1 (IH (size_exp e) ltac:(simpl in Eq; lia) e eq_refl)); exact H.
    + simpl. assert (H' : lc_exp e) by (inversion H; assumption).
      apply (proj2 (IH (size_exp e) ltac:(simpl in Eq; lia) e eq_refl)); exact H'.
  - split; intros H.
    + apply lc_trm_proj. apply (proj1 (IH (size_exp e) ltac:(simpl in Eq; lia) e eq_refl)); exact H.
    + simpl. assert (H' : lc_exp e) by (inversion H; assumption).
      apply (proj2 (IH (size_exp e) ltac:(simpl in Eq; lia) e eq_refl)); exact H'.
  - split; intros H.
    + apply lc_trm_capp. apply (proj1 (IH (size_exp e) ltac:(simpl in Eq; lia) e eq_refl)); exact H.
    + simpl. assert (H' : lc_exp e) by (inversion H; assumption).
      apply (proj2 (IH (size_exp e) ltac:(simpl in Eq; lia) e eq_refl)); exact H'.
Qed.

Lemma lc_lcg : forall e, lc_exp e -> lcg 0 e.
Proof. intros. apply lcg_iff_lc; auto. Qed.

Lemma lcg_mono : forall e n0 m0, n0 <= m0 -> lcg n0 e -> lcg m0 e.
Proof.
  intros e. induction e; intros n0 m0 Hle H; simpl in *; auto.
  - lia.
  - exact (IHe (S n0) (S m0) ltac:(lia) H).
  - destruct H as [H1 H2]; split; [apply (IHe1 n0 m0) | apply (IHe2 n0 m0)]; auto.
  - destruct H as [H1 H2]; split; [apply (IHe1 n0 m0) | apply (IHe2 n0 m0)]; auto.
  - exact (IHe n0 m0 Hle H).
  - exact (IHe n0 m0 Hle H).
  - exact (IHe n0 m0 Hle H).
Qed.

Fixpoint subst_env (sigma : var -> exp) (e : exp) : exp :=
  match e with
  | trm_var_b i => trm_var_b i
  | trm_var_f x => sigma x
  | trm_unit => trm_unit
  | trm_lit i => trm_lit i
  | trm_abs e' => trm_abs (subst_env sigma e')
  | trm_app e1 e2 => trm_app (subst_env sigma e1) (subst_env sigma e2)
  | trm_pair e1 e2 => trm_pair (subst_env sigma e1) (subst_env sigma e2)
  | trm_rcd l e' => trm_rcd l (subst_env sigma e')
  | trm_proj e' l => trm_proj (subst_env sigma e') l
  | trm_capp c e' => trm_capp c (subst_env sigma e')
  end.

Definition extend (sigma : var -> exp) (x:var) (u:exp) : var -> exp :=
  fun y => if eq_var y x then u else sigma y.

Lemma subst_env_lcg : forall e m sigma, lcg m e -> (forall x, lcg m (sigma x)) -> lcg m (subst_env sigma e).
Proof.
  intros e. induction e; intros m sigma He Hs; simpl in *.
  - exact He.
  - apply Hs.
  - exact I.
  - exact I.
  - exact (IHe (S m) sigma He ltac:(intros x; apply lcg_mono with (n0:=m); [lia | apply Hs])).
  - destruct He as [H1 H2]; split.
    + exact (IHe1 m sigma H1 Hs).
    + exact (IHe2 m sigma H2 Hs).
  - destruct He as [H1 H2]; split.
    + exact (IHe1 m sigma H1 Hs).
    + exact (IHe2 m sigma H2 Hs).
  - exact (IHe m sigma He Hs).
  - exact (IHe m sigma He Hs).
  - exact (IHe m sigma He Hs).
Qed.

Lemma subst_env_lc : forall e sigma, lc_exp e -> (forall x, lc_exp (sigma x)) -> lc_exp (subst_env sigma e).
Proof.
  intros e sigma He Hs. apply lcg_iff_lc.
  apply subst_env_lcg.
  - apply lcg_iff_lc; exact He.
  - intros x. apply lcg_iff_lc. apply Hs.
Qed.

Lemma subst_env_extend_self : forall sigma x0 ee,
  sigma x0 = trm_var_f x0 ->
  subst_env (extend sigma x0 (trm_var_f x0)) ee = subst_env sigma ee.
Proof.
  intros sigma x0 ee Hs. induction ee; simpl in *; auto.
  - unfold extend. destruct (x == x0) as [Heq|Hne].
    + subst. symmetry. exact Hs.
    + reflexivity.
  - rewrite IHee; auto.
  - rewrite IHee1, IHee2; auto.
  - rewrite IHee1, IHee2; auto.
  - rewrite IHee; auto.
  - rewrite IHee; auto.
  - rewrite IHee; auto.
Qed.

Lemma subst_env_open_rec : forall ee k sigma x0 u,
  x0 \notin fv_exp ee -> (forall y, lcg 0 (sigma y)) ->
  subst_env (extend sigma x0 u) (open_exp_wrt_exp_rec k (trm_var_f x0) ee)
  = open_exp_wrt_exp_rec k u (subst_env sigma ee).
Proof.
  intros ee. induction ee; intros k sigma x0 u Hfv Hs; simpl in *.
  - (* var_b *) destruct (lt_eq_lt_dec n k) as [[H1|H1]|H1].
    + reflexivity.
    + unfold extend. change ((if x0 == x0 then u else sigma x0) = u).
      destruct (x0 == x0) as [Heq|Hne].
      * reflexivity.
      * exfalso; apply Hne; reflexivity.
    + reflexivity.
  - (* var_f x *) unfold extend. change ((if x == x0 then u else sigma x) = open_exp_wrt_exp_rec k u (sigma x)).
    rewrite (@open_rec_lcg (sigma x) 0 (Hs x) k u ltac:(lia)).
    destruct (x == x0) as [Heq|Hne].
    + exfalso; apply Hfv; subst; simpl; fsetdec.
    + reflexivity.
  - (* unit *) reflexivity.
  - (* lit *) reflexivity.
  - (* abs *) rewrite (IHee (S k) sigma x0 u ltac:(simpl in Hfv; fsetdec) Hs). reflexivity.
  - (* app *) rewrite (IHee1 k sigma x0 u ltac:(simpl in Hfv; fsetdec) Hs).
    rewrite (IHee2 k sigma x0 u ltac:(simpl in Hfv; fsetdec) Hs). reflexivity.
  - (* pair *) rewrite (IHee1 k sigma x0 u ltac:(simpl in Hfv; fsetdec) Hs).
    rewrite (IHee2 k sigma x0 u ltac:(simpl in Hfv; fsetdec) Hs). reflexivity.
  - (* rcd *) rewrite (IHee k sigma x0 u ltac:(simpl in Hfv; fsetdec) Hs). reflexivity.
  - (* proj *) rewrite (IHee k sigma x0 u ltac:(simpl in Hfv; fsetdec) Hs). reflexivity.
  - (* capp *) rewrite (IHee k sigma x0 u ltac:(simpl in Hfv; fsetdec) Hs). reflexivity.
Qed.

Lemma star_linear : forall a b, (step star) a b -> forall z, (step star) a z ->
  ((step star) b z) \/ ((step star) z b).
Proof.
  intros a b H. induction H; intros z Hz.
  - left; exact Hz.
  - inversion Hz; subst.
    + right. eapply (star_step step z b c); [exact H | exact H0].
    + assert (b0 = b) by (eapply step_det; eauto). subst b0.
      exact (IHstar z H2).
Qed.

Lemma star_join_value : forall a b c, (step star) a b -> (step star) a c -> value c -> (step star) b c.
Proof.
  intros a b c Hab Hac Hc.
  destruct (@star_linear a b Hab c Hac) as [X|X]; auto.
  assert (b = c) by (exact (@star_from_value c b Hc X)). subst; apply star_refl.
Qed.

Lemma E_red_l : forall A a a' b, (step star) a a' -> E A a b -> E A a' b.
Proof.
  intros A a a' b Ha [v1 [v2 [H1 [H2 [W1 [W2 AE1]]]]]].
  assert (X : (step star) a' v1).
  { destruct (@star_linear a a' Ha v1 H1) as [X|X]; auto.
    assert (a' = v1) by (exact (@star_from_value v1 a' (WF_value A v1 W1) X)).
    subst; apply star_refl. }
  exists v1, v2; repeat split; auto; eapply star_trans; eauto.
Qed.

Lemma E_red_r : forall A a b b', (step star) b b' -> E A a b -> E A a b'.
Proof.
  intros A a b b' Hb [v1 [v2 [H1 [H2 [W1 [W2 AE1]]]]]].
  assert (Y : (step star) b' v2).
  { destruct (@star_linear b b' Hb v2 H2) as [Y|Y]; auto.
    assert (b' = v2) by (exact (@star_from_value v2 b' (WF_value A v2 W2) Y)).
    subst; apply star_refl. }
  exists v1, v2; repeat split; auto; eapply star_trans; eauto.
Qed.

Lemma E_star_lr : forall A a a' b b', (step star) a a' -> (step star) b b' -> E A a' b' -> E A a b.
Proof.
  intros A a a' b b' Ha Hb [v1 [v2 [H1 [H2 [W1 [W2 AE1]]]]]].
  assert (X : (step star) a' v1).
  { destruct (@star_linear a a' Ha v1 (@star_trans step a a' v1 Ha H1)) as [X|X].
    - exact X.
    - assert (a' = v1) by (exact (@star_from_value v1 a' (WF_value A v1 W1) X)). subst; apply star_refl. }
  assert (Y : (step star) b' v2).
  { destruct (@star_linear b b' Hb v2 (@star_trans step b b' v2 Hb H2)) as [Y|Y].
    - exact Y.
    - assert (b' = v2) by (exact (@star_from_value v2 b' (WF_value A v2 W2) Y)). subst; apply star_refl. }
  exists v1, v2; repeat split; auto; eapply star_trans; eauto.
Qed.

Definition CohVal (A:styp) (t:exp) : Prop :=
  forall C c1 c2, sub A C c1 -> sub A C c2 -> E C (trm_capp c1 t) (trm_capp c2 t).

Lemma Coh_star : forall A t v, (step star) t v -> WF A v -> CohVal A t -> CohVal A v.
Proof.
  intros A t v Ht Wv HC C c1 c2 H1 H2.
  assert (E C (trm_capp c1 t)(trm_capp c2 t)) as HE by (apply HC; auto).
  apply E_red_r with (b := trm_capp c2 t). apply star_capp; exact Ht.
  apply E_red_l with (a := trm_capp c1 t). apply star_capp; exact Ht. exact HE.
Qed.

Lemma Coh_coerce : forall A B t c, E A t t -> CohVal A t -> sub A B c -> CohVal B (trm_capp c t).
Proof.
  intros A B t c HE HC Hs C d1 d2 Hd1 Hd2.
  assert (HEc : E C (trm_capp (co_trans d1 c) t)(trm_capp (co_trans d2 c) t))
    by (apply HC; [eapply S_trans with (A2:=B); eauto | eapply S_trans with (A2:=B); eauto]).
  destruct (@E_WF_l A t t HE) as [v [Ht Wv]].
  pose (P1 := trm_capp d1 (trm_capp c v)).
  pose (P2 := trm_capp d2 (trm_capp c v)).
  assert (HL1 : (step star) (trm_capp (co_trans d1 c) t) P1).
  { unfold P1. eapply star_trans.
    - apply star_capp; exact Ht.
    - eapply star_step; [apply step_trans; eapply WF_value; eauto | apply star_refl]. }
  assert (HL2 : (step star) (trm_capp (co_trans d2 c) t) P2).
  { unfold P2. eapply star_trans.
    - apply star_capp; exact Ht.
    - eapply star_step; [apply step_trans; eapply WF_value; eauto | apply star_refl]. }
  assert (HM1 : (step star) (trm_capp d1 (trm_capp c t)) P1).
  { unfold P1. apply star_capp. apply star_capp. exact Ht. }
  assert (HM2 : (step star) (trm_capp d2 (trm_capp c t)) P2).
  { unfold P2. apply star_capp. apply star_capp. exact Ht. }
  assert (X : E C P1 (trm_capp (co_trans d2 c) t)) by (exact (@E_red_l C (trm_capp (co_trans d1 c) t) P1 (trm_capp (co_trans d2 c) t) HL1 HEc)).
  assert (Y : E C P1 P2) by (exact (@E_red_r C P1 (trm_capp (co_trans d2 c) t) P2 HL2 X)).
  assert (Z : E C (trm_capp d1 (trm_capp c t)) P2)
    by (exact (@E_star_lr C (trm_capp d1 (trm_capp c t)) P1 P2 P2 HM1 (star_refl step P2) Y)).
  exact (@E_star_lr C (trm_capp d1 (trm_capp c t)) (trm_capp d1 (trm_capp c t)) (trm_capp d2 (trm_capp c t)) P2 (star_refl step (trm_capp d1 (trm_capp c t))) HM2 Z).
Qed.

Lemma E_app : forall A1 A2 f1 f2 g1 g2,
  E (styp_arrow A1 A2) f1 f2 -> E A1 g1 g2 -> lc_exp g1 -> lc_exp g2 ->
  E A2 (trm_app f1 g1) (trm_app f2 g2).
Proof.
  intros A1 A2 f1 f2 g1 g2
    [u1 [u2 [Hf1 [Hf2 [Wu1 [Wu2 AEu]]]]]]
    [w1 [w2 [Hg1 [Hg2 [Ww1 [Ww2 AEw]]]]]] Hg1lc Hg2lc.
  simpl in AEu.
  destruct AEu as [Ul1 [Ul2 [Uv1 [Uv2 AU]]]].
  destruct (AU w1 w2 Ww1 Ww2 AEw) as [z1 [z2 [Sz1 [Sz2 [Wz1 [Wz2 AEz]]]]]].
  exists z1, z2; repeat split; auto.
  - eapply star_trans.
    + eapply star_trans.
      * eapply star_app_l; [exact Hf1 | exact Hg1lc].
      * apply star_app_r; [eapply WF_value; eauto | exact Hg1].
    + exact Sz1.
  - eapply star_trans.
    + eapply star_trans.
      * eapply star_app_l; [exact Hf2 | exact Hg2lc].
      * apply star_app_r; [eapply WF_value; eauto | exact Hg2].
    + exact Sz2.
Qed.

Lemma E_pair : forall A1 A2 a1 a2 b1 b2,
  E A1 a1 a2 -> E A2 b1 b2 -> lc_exp b1 -> lc_exp b2 ->
  E (styp_and A1 A2) (trm_pair a1 b1) (trm_pair a2 b2).
Proof.
  intros A1 A2 a1 a2 b1 b2
    [u1 [u2 [Ha1 [Ha2 [Wu1 [Wu2 AEa]]]]]]
    [v1 [v2 [Hb1 [Hb2 [Wv1 [Wv2 AEb]]]]]] Hb1lc Hb2lc.
  exists (trm_pair u1 v1), (trm_pair u2 v2); repeat split; auto.
  - eapply star_trans.
    + apply star_pair_l; [exact Ha1 | exact Hb1lc].
    + apply star_pair_r; [eapply WF_value; eauto | exact Hb1].
  - eapply star_trans.
    + apply star_pair_l; [exact Ha2 | exact Hb2lc].
    + apply star_pair_r; [eapply WF_value; eauto | exact Hb2].
  - simpl. exists u1, v1. repeat split; auto.
  - simpl. exists u2, v2. repeat split; auto.
  - simpl. exists u1, v1, u2, v2. repeat split; auto.
Qed.

Lemma E_rcd : forall A l a1 a2, E A a1 a2 -> E (styp_rcd l A) (trm_rcd l a1)(trm_rcd l a2).
Proof.
  intros A l a1 a2 [u1 [u2 [H1 [H2 [W1 [W2 AE1]]]]]].
  exists (trm_rcd l u1), (trm_rcd l u2); repeat split; auto.
  - apply star_rcd; exact H1.
  - apply star_rcd; exact H2.
  - simpl. exists u1; auto.
  - simpl. exists u2; auto.
  - simpl. exists u1, u2; auto.
Qed.

Lemma E_proj : forall A l a1 a2, E (styp_rcd l A) a1 a2 -> E A (trm_proj a1 l)(trm_proj a2 l).
Proof.
  intros A l a1 a2 [u1 [u2 [H1 [H2 [W1 [W2 AE1]]]]]].
  simpl in W1, W2. destruct W1 as [x1 [E1 Wx1]]. destruct W2 as [x2 [E2 Wx2]]. subst u1 u2.
  simpl in AE1. destruct AE1 as [x1' [x2' [F1 [F2 Ax]]]].
  assert (x1 = x1') by congruence. assert (x2 = x2') by congruence. subst x1' x2'.
  exists x1, x2; repeat split; auto.
  - eapply star_trans.
    + apply star_proj; exact H1.
    + eapply star_step; [apply step_projRcd; eapply WF_value; eauto | apply star_refl].
  - eapply star_trans.
    + apply star_proj; exact H2.
    + eapply star_step; [apply step_projRcd; eapply WF_value; eauto | apply star_refl].
Qed.

Lemma arr_reduct_l : forall (f g v w : exp) (c : co),
  (step star) f v -> value v -> (step star) g w -> value w ->
  (step star) (trm_app (trm_capp (co_arr co_id c) v) w) (trm_capp c (trm_app v w)).
Proof.
  intros. eapply star_trans.
  - eapply star_step. apply step_arr; auto. apply star_refl.
  - apply star_capp. apply star_app_r; auto.
    eapply star_step. apply step_id; auto. apply star_refl.
Qed.

Lemma E_V : forall A v1 v2, WF A v1 -> WF A v2 -> AE A v1 v2 -> E A v1 v2.
Proof. intros. apply V_E. repeat split; auto. Qed.

Lemma Coh_app_l : forall A1 A2 (f g:exp),
  E (styp_arrow A1 A2) f f -> CohVal (styp_arrow A1 A2) f ->
  E A1 g g -> lc_exp g -> CohVal A2 (trm_app f g).
Proof.
  intros A1 A2 f g HEf HCf HEg Hgc C c1 c2 Hc1 Hc2.
  destruct (@E_WF_l (styp_arrow A1 A2) f f HEf) as [vf [Hf Wvf]].
  destruct (@E_WF_l A1 g g HEg) as [wg [Hg Wwg]].
  assert (Harr1 : sub (styp_arrow A1 A2) (styp_arrow A1 C) (co_arr co_id c1))
    by (apply S_arr; [apply S_refl | exact Hc1]).
  assert (Harr2 : sub (styp_arrow A1 A2) (styp_arrow A1 C) (co_arr co_id c2))
    by (apply S_arr; [apply S_refl | exact Hc2]).
  assert (HEF : E (styp_arrow A1 C) (trm_capp (co_arr co_id c1) f) (trm_capp (co_arr co_id c2) f))
    by (apply HCf; auto).
  destruct HEF as [u1 [u2 [HF1 [HF2 [Wu1 [Wu2 AEu]]]]]].
  simpl in AEu. destruct AEu as [Ul1 [Ul2 [Uv1 [Uv2 AU]]]].
  destruct (AU wg wg Wwg Wwg (AE_refl A1 wg Wwg)) as [z1 [z2 [Sz1 [Sz2 [Wz1 [Wz2 AEz]]]]]].
  assert (Hu1 : u1 = trm_capp (co_arr co_id c1) vf).
  { eapply star_value_det; [exact HF1 | eapply WF_value; eauto | apply star_capp; exact Hf | apply value_cabs; eapply WF_value; eauto]. }
  assert (Hu2 : u2 = trm_capp (co_arr co_id c2) vf).
  { eapply star_value_det; [exact HF2 | eapply WF_value; eauto | apply star_capp; exact Hf | apply value_cabs; eapply WF_value; eauto]. }
  subst u1 u2.
  assert (HV1 : (step star) (trm_app (trm_capp (co_arr co_id c1) vf) wg) (trm_capp c1 (trm_app vf wg)))
    by (apply arr_reduct_l with (f:=vf) (g:=wg); [apply star_refl | eapply WF_value; eauto | apply star_refl | eapply WF_value; eauto]).
  assert (HV2 : (step star) (trm_app (trm_capp (co_arr co_id c2) vf) wg) (trm_capp c2 (trm_app vf wg)))
    by (apply arr_reduct_l with (f:=vf) (g:=wg); [apply star_refl | eapply WF_value; eauto | apply star_refl | eapply WF_value; eauto]).
  assert (JV1 : (step star) (trm_capp c1 (trm_app vf wg)) z1)
    by (eapply star_join_value; [exact HV1 | exact Sz1 | eapply WF_value; eauto]).
  assert (JV2 : (step star) (trm_capp c2 (trm_app vf wg)) z2)
    by (eapply star_join_value; [exact HV2 | exact Sz2 | eapply WF_value; eauto]).
  assert (HEV : E C (trm_capp c1 (trm_app vf wg)) (trm_capp c2 (trm_app vf wg)))
    by (exact (@E_star_lr C (trm_capp c1 (trm_app vf wg)) z1 (trm_capp c2 (trm_app vf wg)) z2 JV1 JV2 (E_V C z1 z2 Wz1 Wz2 AEz))).
  assert (JU1 : (step star) (trm_capp c1 (trm_app f g)) (trm_capp c1 (trm_app vf wg))).
  { apply star_capp.
    eapply star_trans.
    - apply star_app_l with (e1:=f) (e1':=vf) (e2:=g); [exact Hf | exact Hgc].
    - apply star_app_r with (v:=vf) (e2:=g) (e2':=wg); [exact (WF_value (styp_arrow A1 A2) vf Wvf) | exact Hg]. }
  assert (JU2 : (step star) (trm_capp c2 (trm_app f g)) (trm_capp c2 (trm_app vf wg))).
  { apply star_capp.
    eapply star_trans.
    - apply star_app_l with (e1:=f) (e1':=vf) (e2:=g); [exact Hf | exact Hgc].
    - apply star_app_r with (v:=vf) (e2:=g) (e2':=wg); [exact (WF_value (styp_arrow A1 A2) vf Wvf) | exact Hg]. }
  exact (@E_star_lr C (trm_capp c1 (trm_app f g)) (trm_capp c1 (trm_app vf wg)) (trm_capp c2 (trm_app f g)) (trm_capp c2 (trm_app vf wg)) JU1 JU2 HEV).
Qed.

Lemma Coh_app_r : forall A1 A2 (f t:exp),
  E (styp_arrow A1 A2) f f -> CohVal (styp_arrow A1 A2) f ->
  E A1 t t -> lc_exp t -> CohVal A1 t -> lc_exp f -> CohVal A2 (trm_app f t).
Proof.
  intros A1 A2 f t HEf HCf HEt Htc HCt Hfc C c1 c2 Hc1 Hc2.
  destruct (@E_WF_l (styp_arrow A1 A2) f f HEf) as [vf [Hf Wvf]].
  destruct (@E_WF_l A1 t t HEt) as [w [Ht Ww]].
  assert (Harr1 : sub (styp_arrow A1 A2) (styp_arrow A1 C) (co_arr co_id c1))
    by (apply S_arr; [apply S_refl | exact Hc1]).
  assert (Harr2 : sub (styp_arrow A1 A2) (styp_arrow A1 C) (co_arr co_id c2))
    by (apply S_arr; [apply S_refl | exact Hc2]).
  assert (HEF : E (styp_arrow A1 C) (trm_capp (co_arr co_id c1) f) (trm_capp (co_arr co_id c2) f))
    by (apply HCf; auto).
  destruct HEF as [u1 [u2 [HF1 [HF2 [Wu1 [Wu2 AEu]]]]]].
  simpl in AEu. destruct AEu as [Ul1 [Ul2 [Uv1 [Uv2 AU]]]].
  destruct (AU w w Ww Ww (AE_refl A1 w Ww)) as [z1 [z2 [Sz1 [Sz2 [Wz1 [Wz2 AEz]]]]]].
  assert (Hu1 : u1 = trm_capp (co_arr co_id c1) vf).
  { eapply star_value_det; [exact HF1 | eapply WF_value; eauto | apply star_capp; exact Hf | apply value_cabs; eapply WF_value; eauto]. }
  assert (Hu2 : u2 = trm_capp (co_arr co_id c2) vf).
  { eapply star_value_det; [exact HF2 | eapply WF_value; eauto | apply star_capp; exact Hf | apply value_cabs; eapply WF_value; eauto]. }
  subst u1 u2.
  assert (HV1 : (step star) (trm_app (trm_capp (co_arr co_id c1) vf) w) (trm_capp c1 (trm_app vf w)))
    by (apply arr_reduct_l with (f:=vf) (g:=w); [apply star_refl | eapply WF_value; eauto | apply star_refl | eapply WF_value; eauto]).
  assert (HV2 : (step star) (trm_app (trm_capp (co_arr co_id c2) vf) w) (trm_capp c2 (trm_app vf w)))
    by (apply arr_reduct_l with (f:=vf) (g:=w); [apply star_refl | eapply WF_value; eauto | apply star_refl | eapply WF_value; eauto]).
  assert (JU1 : (step star) (trm_capp c1 (trm_app f t)) (trm_capp c1 (trm_app vf w))).
  { apply star_capp.
    eapply star_trans.
    - apply star_app_l with (e1:=f) (e1':=vf) (e2:=t); [exact Hf | exact Htc].
    - apply star_app_r with (v:=vf) (e2:=t) (e2':=w); [exact (WF_value (styp_arrow A1 A2) vf Wvf) | exact Ht]. }
  assert (JU2 : (step star) (trm_capp c2 (trm_app f t)) (trm_capp c2 (trm_app vf w))).
  { apply star_capp.
    eapply star_trans.
    - apply star_app_l with (e1:=f) (e1':=vf) (e2:=t); [exact Hf | exact Htc].
    - apply star_app_r with (v:=vf) (e2:=t) (e2':=w); [exact (WF_value (styp_arrow A1 A2) vf Wvf) | exact Ht]. }
  assert (J1 : (step star) (trm_capp c1 (trm_app vf w)) z1)
    by (eapply star_join_value; [exact HV1 | exact Sz1 | eapply WF_value; eauto]).
  assert (J2 : (step star) (trm_capp c2 (trm_app vf w)) z2)
    by (eapply star_join_value; [exact HV2 | exact Sz2 | eapply WF_value; eauto]).
  assert (HEV : E C (trm_capp c1 (trm_app vf w)) (trm_capp c2 (trm_app vf w)))
    by (exact (@E_star_lr C (trm_capp c1 (trm_app vf w)) z1 (trm_capp c2 (trm_app vf w)) z2 J1 J2 (E_V C z1 z2 Wz1 Wz2 AEz))).
  exact (@E_star_lr C (trm_capp c1 (trm_app f t)) (trm_capp c1 (trm_app vf w)) (trm_capp c2 (trm_app f t)) (trm_capp c2 (trm_app vf w)) JU1 JU2 HEV).
Qed.

Lemma star_rcd_inv : forall l x w, (step star) (trm_rcd l x) w -> exists y, w = trm_rcd l y /\ (step star) x y.
Proof.
  intros l x w H. remember (trm_rcd l x) as s eqn:Es. revert x Es.
  induction H; intros x0 Es.
  - exists x0. split; [|apply star_refl]. first [exact Es | symmetry; exact Es].
  - rewrite Es in H. inversion H; subst.
    destruct (IHstar e' eq_refl) as [y [Ey Hy]]. exists y; split; auto.
    eapply star_step; [eassumption | exact Hy].
Qed.

Lemma Coh_proj : forall A l t, E (styp_rcd l A) t t -> CohVal (styp_rcd l A) t ->
  CohVal A (trm_proj t l).
Proof.
  intros A l t HE HC C c1 c2 Hc1 Hc2.
  destruct (@E_WF_l (styp_rcd l A) t t HE) as [u [Htu Wu]].
  simpl in Wu. destruct Wu as [a [Eu Wa]]. subst u.
  (* reductions of the coerced terms *)
  assert (R1 : (step star) (trm_capp (co_rcd l c1) t) (trm_rcd l (trm_capp c1 a))).
  { eapply star_trans.
    - apply star_capp; exact Htu.
    - eapply star_step; [apply step_crcd; eapply WF_value; eauto | apply star_refl]. }
  assert (R2 : (step star) (trm_capp (co_rcd l c2) t) (trm_rcd l (trm_capp c2 a))).
  { eapply star_trans.
    - apply star_capp; exact Htu.
    - eapply star_step; [apply step_crcd; eapply WF_value; eauto | apply star_refl]. }
  assert (Hs1 : sub (styp_rcd l A) (styp_rcd l C) (co_rcd l c1)) by (apply S_rcd; exact Hc1).
  assert (Hs2 : sub (styp_rcd l A) (styp_rcd l C) (co_rcd l c2)) by (apply S_rcd; exact Hc2).
  assert (HErc : E (styp_rcd l C) (trm_capp (co_rcd l c1) t) (trm_capp (co_rcd l c2) t))
    by (apply HC; auto).
  assert (HR : E (styp_rcd l C) (trm_rcd l (trm_capp c1 a)) (trm_rcd l (trm_capp c2 a))).
  { assert (X : E (styp_rcd l C) (trm_rcd l (trm_capp c1 a)) (trm_capp (co_rcd l c2) t))
      by (exact (@E_red_l (styp_rcd l C) (trm_capp (co_rcd l c1) t) (trm_rcd l (trm_capp c1 a))
                    (trm_capp (co_rcd l c2) t) R1 HErc)).
    exact (@E_red_r (styp_rcd l C) (trm_rcd l (trm_capp c1 a)) (trm_capp (co_rcd l c2) t)
             (trm_rcd l (trm_capp c2 a)) R2 X). }
  (* extract the contents *)
  destruct HR as [w1 [w2 [S1 [S2 [W1 [W2 AE12]]]]]].
  simpl in W1, W2. destruct W1 as [s1 [Ew1 Ws1]]. destruct W2 as [s2 [Ew2 Ws2]]. subst w1 w2.
  simpl in AE12. destruct AE12 as [s1' [s2' [F1 [F2 As]]]].
  assert (s1 = s1') by congruence. assert (s2 = s2') by congruence. subst s1' s2'.
  (* bodies reduce *)
  destruct (@star_rcd_inv l (trm_capp c1 a) (trm_rcd l s1) S1) as [y1 [Ey1 HS1]].
  destruct (@star_rcd_inv l (trm_capp c2 a) (trm_rcd l s2) S2) as [y2 [Ey2 HS2]].
  assert (s1 = y1) by congruence. assert (s2 = y2) by congruence. subst y1 y2.
  (* targets reduce *)
  assert (T1 : (step star) (trm_capp c1 (trm_proj t l)) s1).
  { eapply star_trans.
    - apply star_capp. apply star_proj. exact Htu.
    - eapply star_trans.
      + apply star_capp. eapply star_step; [apply step_projRcd; eapply WF_value; eauto | apply star_refl].
      + exact HS1. }
  assert (T2 : (step star) (trm_capp c2 (trm_proj t l)) s2).
  { eapply star_trans.
    - apply star_capp. apply star_proj. exact Htu.
    - eapply star_trans.
      + apply star_capp. eapply star_step; [apply step_projRcd; eapply WF_value; eauto | apply star_refl].
      + exact HS2. }
  exact (@E_star_lr C (trm_capp c1 (trm_proj t l)) s1 (trm_capp c2 (trm_proj t l)) s2 T1 T2 (E_V C s1 s2 Ws1 Ws2 As)).
Qed.

(* ================= canonical values for base-type coherence ================= *)
Fixpoint CN (C:styp) (k:nat) : exp :=
  match C with
  | styp_top => trm_unit
  | styp_nat => trm_lit k
  | styp_and A B => trm_pair (CN A k) (CN B k)
  | styp_arrow A B => trm_abs (CN B k)
  | styp_rcd l A => trm_rcd l (CN A k)
  end.

Lemma CN_lcg0 : forall C k, lcg 0 (CN C k).
Proof.
  intros C. induction C; intros k; simpl.
  - exact I. - exact I.
  - split; auto.
  - apply (@lcg_mono (CN C2 k) 0 1); [lia | exact (IHC2 k)].
  - auto.
Qed.

Lemma CN_lc : forall C k, lc_exp (CN C k).
Proof. intros. apply lcg_iff_lc. apply CN_lcg0. Qed.

Lemma CN_abs_lc : forall C k, lc_exp (trm_abs (CN C k)).
Proof.
  intros. apply lc_trm_abs. intros y.
  apply lcg_iff_lc.
  unfold open_exp_wrt_exp.
  rewrite (@open_rec_lcg (CN C k) 0 (CN_lcg0 C k) 0 (trm_var_f y) ltac:(lia)).
  apply CN_lcg0.
Qed.

Lemma CN_WF : forall C k, WF C (CN C k).
Proof.
  intros C. induction C; intros k; simpl.
  - reflexivity.
  - exists k; reflexivity.
  - exists (CN C1 k), (CN C2 k); simpl; repeat split; auto.
  - split.
    + apply CN_abs_lc.
    + split.
      * apply value_abs. apply CN_abs_lc.
      * intros u1 u2 Wu1 Wu2 Au. exists (CN C2 k), (CN C2 k).
        repeat split.
        -- eapply star_step. apply step_beta.
           ++ apply CN_abs_lc.
           ++ exact (@WF_value C1 u1 Wu1).
           ++ unfold open_exp_wrt_exp.
              rewrite (@open_rec_lcg (CN C2 k) 0 (CN_lcg0 C2 k) 0 u1 ltac:(lia)).
              apply star_refl.
        -- eapply star_step. apply step_beta.
           ++ apply CN_abs_lc.
           ++ exact (@WF_value C1 u2 Wu2).
           ++ unfold open_exp_wrt_exp.
              rewrite (@open_rec_lcg (CN C2 k) 0 (CN_lcg0 C2 k) 0 u2 ltac:(lia)).
              apply star_refl.
        -- apply IHC2.
        -- apply IHC2.
        -- apply AE_of_WF. apply IHC2.
  - exists (CN C k); simpl; repeat split; auto.
Qed.


(* ---------- reduction helpers for canonical coercions ---------- *)
Lemma star1 : forall a b, step a b -> (step star) a b.
Proof. intros. eapply star_step; [exact H | apply star_refl]. Qed.

Lemma E_WF_self : forall A v, WF A v -> E A v v.
Proof. intros. apply V_E. repeat split; auto. apply AE_of_WF; auto. Qed.

Lemma step_beta_CN : forall A k u, value u ->
  (step star) (trm_app (trm_abs (CN A k)) u) (CN A k).
Proof.
  intros A k u Hv.
  eapply (@star_trans step (trm_app (trm_abs (CN A k)) u)
             (open_exp_wrt_exp (CN A k) u) (CN A k)).
  - apply star1. apply step_beta.
    + apply CN_abs_lc.
    + exact Hv.
  - unfold open_exp_wrt_exp.
    rewrite (@open_rec_lcg (CN A k) 0 (CN_lcg0 A k) 0 u ltac:(lia)).
    apply star_refl.
Qed.

Lemma capp_E : forall X C c t1 t2, sub X C c -> E X t1 t2 ->
  E C (trm_capp c t1)(trm_capp c t2).
Proof.
  intros X C c t1 t2 Hs [v1 [v2 [S1 [S2 [W1 [W2 AE]]]]]].
  eapply (@E_star_lr C (trm_capp c t1) (trm_capp c v1)
             (trm_capp c t2) (trm_capp c v2)).
  - apply star_capp; exact S1.
  - apply star_capp; exact S2.
  - apply (@SC_same X C c Hs v1 v2). repeat split; auto.
Qed.

(* ---------- comp_cn, case helpers ---------- *)
Lemma comp_cn_refl : forall A k, E A (trm_capp co_id (CN A k)) (CN A k).
Proof.
  intros. eapply (@E_star_lr A (trm_capp co_id (CN A k)) (CN A k) (CN A k) (CN A k)).
  - apply star1. apply step_id. apply (@WF_value A (CN A k) (CN_WF A k)).
  - apply star_refl.
  - apply E_WF_self. apply CN_WF.
Qed.

Lemma comp_cn_top : forall A k, E styp_top (trm_capp co_top (CN A k)) (CN styp_top k).
Proof.
  intros. eapply (@E_star_lr styp_top (trm_capp co_top (CN A k)) trm_unit trm_unit (CN styp_top k)).
  - apply star1. apply step_top. apply (@WF_value A (CN A k) (CN_WF A k)).
  - apply star_refl.
  - apply E_WF_self. apply CN_WF.
Qed.

Lemma comp_cn_topArr : forall k,
  E (styp_arrow styp_top styp_top)
    (trm_capp co_topArr (CN styp_top k))
    (CN (styp_arrow styp_top styp_top) k).
Proof.
  intros k.
  exists (trm_capp co_topArr trm_unit), (trm_abs trm_unit).
  split.
  { apply star_refl. }
  split.
  { apply star_refl. }
  split.
  { apply WF_arrow_top_top_val. }
  split.
  { change (WF (styp_arrow styp_top styp_top) (CN (styp_arrow styp_top styp_top) 0)).
    apply CN_WF. }
  { repeat split.
    - apply lc_trm_capp; constructor.
    - apply lc_trm_abs. intros. constructor.
    - apply value_topArr; constructor.
    - apply value_abs. apply lc_trm_abs. intros. constructor.
    - intros u1 u2 Wu1 Wu2 Au. simpl in Wu1, Wu2. subst u1 u2.
      exists trm_unit, trm_unit.
      split.
      { apply star1. apply step_topArr. }
      split.
      { change ((step star) (trm_app (trm_abs (CN styp_top k)) trm_unit) (CN styp_top k)).
        apply step_beta_CN. constructor. }
      split.
      { simpl. reflexivity. }
      split.
      { simpl. reflexivity. }
      { simpl. split; reflexivity. } }
Qed.

Lemma comp_cn_topRcd : forall l k,
  E (styp_rcd l styp_top)
    (trm_capp (co_topRcd l) (CN styp_top k))
    (CN (styp_rcd l styp_top) k).
Proof.
  intros. eapply (@E_star_lr (styp_rcd l styp_top)
             (trm_capp (co_topRcd l) (CN styp_top k)) (trm_rcd l trm_unit)
             (CN (styp_rcd l styp_top) k) (trm_rcd l trm_unit)).
  - apply star1. apply step_topRcd.
  - apply star_refl.
  - change (E (styp_rcd l styp_top) (trm_rcd l trm_unit) (trm_rcd l trm_unit)).
    apply E_WF_self.
    change (WF (styp_rcd l styp_top) (CN (styp_rcd l styp_top) k)).
    apply CN_WF.
Qed.

Lemma comp_cn_andl : forall A1 A2 k,
  E A1 (trm_capp co_proj1 (CN (styp_and A1 A2) k)) (CN A1 k).
Proof.
  intros. eapply (@E_star_lr A1 (trm_capp co_proj1 (CN (styp_and A1 A2) k))
             (CN A1 k) (CN A1 k) (CN A1 k)).
  - apply star1. apply step_projl.
    + apply (@WF_value A1 (CN A1 k) (CN_WF A1 k)).
    + apply (@WF_value A2 (CN A2 k) (CN_WF A2 k)).
  - apply star_refl.
  - apply E_WF_self. apply CN_WF.
Qed.

Lemma comp_cn_andr : forall A1 A2 k,
  E A2 (trm_capp co_proj2 (CN (styp_and A1 A2) k)) (CN A2 k).
Proof.
  intros. eapply (@E_star_lr A2 (trm_capp co_proj2 (CN (styp_and A1 A2) k))
             (CN A2 k) (CN A2 k) (CN A2 k)).
  - apply star1. apply step_projr.
    + apply (@WF_value A1 (CN A1 k) (CN_WF A1 k)).
    + apply (@WF_value A2 (CN A2 k) (CN_WF A2 k)).
  - apply star_refl.
  - apply E_WF_self. apply CN_WF.
Qed.

Lemma comp_cn_distRcd : forall l A B k,
  E (styp_rcd l (styp_and A B))
    (trm_capp (co_distRcd l) (CN (styp_and (styp_rcd l A) (styp_rcd l B)) k))
    (CN (styp_rcd l (styp_and A B)) k).
Proof.
  intros. eapply (@E_star_lr (styp_rcd l (styp_and A B))
             (trm_capp (co_distRcd l) (CN (styp_and (styp_rcd l A) (styp_rcd l B)) k))
             (trm_rcd l (trm_pair (CN A k) (CN B k)))
             (CN (styp_rcd l (styp_and A B)) k) (CN (styp_rcd l (styp_and A B)) k)).
  - apply star1. apply step_distRcd.
    + apply (@WF_value A (CN A k) (CN_WF A k)).
    + apply (@WF_value B (CN B k) (CN_WF B k)).
  - apply star_refl.
  - change (E (styp_rcd l (styp_and A B))
              (trm_rcd l (trm_pair (CN A k) (CN B k)))
              (trm_rcd l (CN (styp_and A B) k))).
    apply E_rcd. apply E_WF_self. apply CN_WF.
Qed.

Lemma comp_cn_and : forall A1 A2 A3 c1 c2,
  sub A1 A2 c1 -> sub A1 A3 c2 ->
  (forall k, E A2 (trm_capp c1 (CN A1 k)) (CN A2 k)) ->
  (forall k, E A3 (trm_capp c2 (CN A1 k)) (CN A3 k)) ->
  forall k, E (styp_and A2 A3) (trm_capp (co_pair c1 c2) (CN A1 k))
                (CN (styp_and A2 A3) k).
Proof.
  intros A1 A2 A3 c1 c2 Hs1 Hs2 R1 R2 k.
  eapply (@E_star_lr (styp_and A2 A3) (trm_capp (co_pair c1 c2) (CN A1 k))
             (trm_pair (trm_capp c1 (CN A1 k)) (trm_capp c2 (CN A1 k)))
             (CN (styp_and A2 A3) k) (CN (styp_and A2 A3) k)).
  - apply star1. apply step_pair. apply (@WF_value A1 (CN A1 k) (CN_WF A1 k)).
  - apply star_refl.
  - change (E (styp_and A2 A3)
              (trm_pair (trm_capp c1 (CN A1 k)) (trm_capp c2 (CN A1 k)))
              (trm_pair (CN A2 k) (CN A3 k))).
    apply (@E_pair A2 A3 (trm_capp c1 (CN A1 k)) (CN A2 k)
                   (trm_capp c2 (CN A1 k)) (CN A3 k)).
    + exact (R1 k).
    + exact (R2 k).
    + apply lc_trm_capp. apply CN_lc.
    + apply CN_lc.
Qed.

Lemma comp_cn_rcd : forall l A B c,
  sub A B c ->
  (forall k, E B (trm_capp c (CN A k)) (CN B k)) ->
  forall k, E (styp_rcd l B) (trm_capp (co_rcd l c) (CN (styp_rcd l A) k))
                (CN (styp_rcd l B) k).
Proof.
  intros l A B c Hs R k.
  eapply (@E_star_lr (styp_rcd l B)
             (trm_capp (co_rcd l c) (CN (styp_rcd l A) k))
             (trm_rcd l (trm_capp c (CN A k)))
             (CN (styp_rcd l B) k) (CN (styp_rcd l B) k)).
  - apply star1. apply step_crcd. apply (@WF_value A (CN A k) (CN_WF A k)).
  - apply star_refl.
  - change (E (styp_rcd l B) (trm_rcd l (trm_capp c (CN A k)))
              (trm_rcd l (CN B k))).
    apply E_rcd. exact (R k).
Qed.

Lemma comp_cn_arr : forall A1 A2 B1 B2 c1 c2,
  sub B1 A1 c1 -> sub A2 B2 c2 ->
  (forall k, E A1 (trm_capp c1 (CN B1 k)) (CN A1 k)) ->
  (forall k, E B2 (trm_capp c2 (CN A2 k)) (CN B2 k)) ->
  forall k, E (styp_arrow B1 B2)
    (trm_capp (co_arr c1 c2) (CN (styp_arrow A1 A2) k))
    (CN (styp_arrow B1 B2) k).
Proof.
  intros A1 A2 B1 B2 c1 c2 H1 H2 R1 R2 k.
  set (body := trm_abs (CN A2 k)).
  set (G := trm_abs (CN B2 k)).
  assert (Hbodyv : value body) by (unfold body; apply value_abs; apply CN_abs_lc).
  assert (Hbodylc : lc_exp body) by (unfold body; apply CN_abs_lc).
  assert (HGlc : lc_exp G) by (unfold G; apply CN_abs_lc).
  assert (HGv : value G) by (unfold G; apply value_abs; apply CN_abs_lc).
  exists (trm_capp (co_arr c1 c2) body), G.
  split.
  { apply star_refl. }
  split.
  { apply star_refl. }
  split.
  { (* WF F *)
    split.
    - apply lc_trm_capp. exact Hbodylc.
    - split.
      + apply value_cabs. exact Hbodyv.
      + intros u1 u2 Wu1 Wu2 Au.
        destruct (proj1 (@sub_coherent B1 A1 c1 H1) u1 Wu1) as [wa1 [S1 W1]].
        destruct (proj1 (@sub_coherent B1 A1 c1 H1) u2 Wu2) as [wa2 [S2 W2]].
        destruct (R2 k) as [w1 [w2 [T1 [T2 [Ww1 [Ww2 AEw]]]]]].
        exists w1, w1. repeat split.
        * eapply star_trans.
          -- apply star1. apply step_arr.
             ++ exact Hbodyv.
             ++ exact (@WF_value B1 u1 Wu1).
          -- eapply star_trans.
             ++ apply star_capp. apply star_app_r.
                ** exact Hbodyv.
                ** exact S1.
             ++ eapply star_trans.
                ** apply star_capp. apply step_beta_CN.
                   exact (@WF_value A1 wa1 W1).
                ** exact T1.
        * eapply star_trans.
          -- apply star1. apply step_arr.
             ++ exact Hbodyv.
             ++ exact (@WF_value B1 u2 Wu2).
          -- eapply star_trans.
             ++ apply star_capp. apply star_app_r.
                ** exact Hbodyv.
                ** exact S2.
             ++ eapply star_trans.
                ** apply star_capp. apply step_beta_CN.
                   exact (@WF_value A1 wa2 W2).
                ** exact T1.
        * exact Ww1.
        * exact Ww1.
        * apply AE_refl. exact Ww1. }
  split.
  { (* WF G *)
    change (WF (styp_arrow B1 B2) (CN (styp_arrow B1 B2) k)).
    apply CN_WF. }
  { (* AE F G *)
    repeat split.
    - apply lc_trm_capp. exact Hbodylc.
    - exact HGlc.
    - apply value_cabs. exact Hbodyv.
    - exact HGv.
    - intros u1 u2 Wu1 Wu2 Au.
      destruct (proj1 (@sub_coherent B1 A1 c1 H1) u1 Wu1) as [wa1 [S1 W1]].
      destruct (proj1 (@sub_coherent B1 A1 c1 H1) u2 Wu2) as [wa2 [S2 W2]].
      destruct (R2 k) as [w1 [w2 [T1 [T2 [Ww1 [Ww2 AEw]]]]]].
      exists w1, w2. repeat split.
      * eapply star_trans.
        -- apply star1. apply step_arr.
           ++ exact Hbodyv.
           ++ exact (@WF_value B1 u1 Wu1).
        -- eapply star_trans.
           ++ apply star_capp. apply star_app_r.
              ** exact Hbodyv.
              ** exact S1.
           ++ eapply star_trans.
              ** apply star_capp. apply step_beta_CN.
                 exact (@WF_value A1 wa1 W1).
              ** exact T1.
      * eapply star_trans.
        -- apply step_beta_CN. exact (@WF_value B1 u2 Wu2).
        -- exact T2.
      * exact Ww1.
      * exact Ww2.
      * exact AEw. }
Qed.

Lemma comp_cn_distArr : forall A1 A2 A3 k,
  E (styp_arrow A1 (styp_and A2 A3))
    (trm_capp co_distArr
      (CN (styp_and (styp_arrow A1 A2) (styp_arrow A1 A3)) k))
    (CN (styp_arrow A1 (styp_and A2 A3)) k).
Proof.
  intros A1 A2 A3 k.
  set (P := trm_pair (CN A2 k) (CN A3 k)).
  set (F := trm_capp co_distArr
              (trm_pair (trm_abs (CN A2 k)) (trm_abs (CN A3 k)))).
  set (G := trm_abs (CN (styp_and A2 A3) k)).
  assert (HPWF : WF (styp_and A2 A3) P).
  { unfold P. change (WF (styp_and A2 A3) (CN (styp_and A2 A3) k)). apply CN_WF. }
  assert (HFv : value F).
  { unfold F. apply value_cpair. apply value_pair; apply value_abs; apply CN_abs_lc. }
  assert (HFlc : lc_exp F).
  { unfold F. apply lc_trm_capp. apply lc_trm_pair; apply CN_abs_lc. }
  assert (HGv : value G).
  { unfold G. apply value_abs. apply CN_abs_lc. }
  assert (HGlc : lc_exp G).
  { unfold G. apply CN_abs_lc. }
  assert (Hstep : forall u, WF A1 u -> value u ->
            (step star) (trm_app F u) P).
  { intros u Wu Hu.
    unfold F, P.
    eapply star_trans.
    - apply star1. apply step_distArr.
      + apply value_abs. apply CN_abs_lc.
      + apply value_abs. apply CN_abs_lc.
      + exact Hu.
    - eapply star_trans.
      + apply star_pair_l.
        * apply step_beta_CN. exact Hu.
        * apply lc_trm_app; [apply CN_abs_lc | exact (@WF_lc A1 u Wu)].
      + apply star_pair_r.
        * apply (@WF_value A2 (CN A2 k) (CN_WF A2 k)).
        * apply step_beta_CN. exact Hu. }
  exists F, G.
  split.
  { unfold F. apply star_refl. }
  split.
  { unfold G. apply star_refl. }
  split.
  { split.
    - exact HFlc.
    - split.
      + exact HFv.
      + intros u1 u2 Wu1 Wu2 Au.
        exists P, P. repeat split.
        * apply Hstep; [exact Wu1 | exact (@WF_value A1 u1 Wu1)].
        * apply Hstep; [exact Wu2 | exact (@WF_value A1 u2 Wu2)].
        * exact HPWF.
        * exact HPWF.
        * apply AE_refl. exact HPWF. }
  split.
  { unfold G. change (WF (styp_arrow A1 (styp_and A2 A3))
                        (CN (styp_arrow A1 (styp_and A2 A3)) k)).
    apply CN_WF. }
  { repeat split.
    - exact HFlc.
    - exact HGlc.
    - exact HFv.
    - exact HGv.
    - intros u1 u2 Wu1 Wu2 Au.
      exists P, P. repeat split.
      * apply Hstep; [exact Wu1 | exact (@WF_value A1 u1 Wu1)].
      * unfold G. apply step_beta_CN. exact (@WF_value A1 u2 Wu2).
      * exact HPWF.
      * exact HPWF.
      * apply AE_refl. exact HPWF. }
Qed.

Lemma comp_cn_trans : forall A1 A3 c1 c2 A2,
  sub A2 A3 c1 -> sub A1 A2 c2 ->
  (forall k, E A3 (trm_capp c1 (CN A2 k)) (CN A3 k)) ->
  (forall k, E A2 (trm_capp c2 (CN A1 k)) (CN A2 k)) ->
  forall k, E A3 (trm_capp (co_trans c1 c2) (CN A1 k)) (CN A3 k).
Proof.
  intros A1 A3 c1 c2 A2 Hs1 Hs2 R1 R2 k.
  eapply (@E_star_lr A3 (trm_capp (co_trans c1 c2) (CN A1 k))
             (trm_capp c1 (trm_capp c2 (CN A1 k))) (CN A3 k) (CN A3 k)).
  - apply star1. apply step_trans.
    apply (@WF_value A1 (CN A1 k) (CN_WF A1 k)).
  - apply star_refl.
  - eapply E_trans.
    + apply (@capp_E A2 A3 c1 (trm_capp c2 (CN A1 k)) (CN A2 k) Hs1 (R2 k)).
    + exact (R1 k).
Qed.

Fixpoint comp_cn (X C:styp)(d:co)(H:sub X C d) {struct H} :
  forall k, E C (trm_capp d (CN X k)) (CN C k) :=
  match H in sub X' C' d' return forall k, E C' (trm_capp d' (CN X' k)) (CN C' k) with
  | S_refl A => comp_cn_refl A
  | S_trans A1 A3 c1 c2 A2 H1 H2 =>
      comp_cn_trans A1 A3 c1 c2 A2 H1 H2
        (comp_cn A2 A3 c1 H1) (comp_cn A1 A2 c2 H2)
  | S_top A => comp_cn_top A
  | S_topArr => comp_cn_topArr
  | S_topRcd l => comp_cn_topRcd l
  | S_arr A1 A2 B1 B2 c1 c2 H1 H2 =>
      comp_cn_arr A1 A2 B1 B2 c1 c2 H1 H2
        (comp_cn B1 A1 c1 H1) (comp_cn A2 B2 c2 H2)
  | S_and A1 A2 A3 c1 c2 H1 H2 =>
      comp_cn_and A1 A2 A3 c1 c2 H1 H2
        (comp_cn A1 A2 c1 H1) (comp_cn A1 A3 c2 H2)
  | S_andl A1 A2 => comp_cn_andl A1 A2
  | S_andr A1 A2 => comp_cn_andr A1 A2
  | S_distArr A1 A2 A3 => comp_cn_distArr A1 A2 A3
  | S_rcd l A B c H1 => comp_cn_rcd l A B c H1 (comp_cn A B c H1)
  | S_distRcd l A B => comp_cn_distRcd l A B
  end.

Lemma Coh_nat_lit : forall k, CohVal styp_nat (trm_lit k).
Proof.
  intros k C c1 c2 H1 H2.
  eapply E_trans.
  - apply (comp_cn styp_nat C c1 H1 k).
  - apply E_sym. apply (comp_cn styp_nat C c2 H2 k).
Qed.

Lemma Coh_top_unit : CohVal styp_top trm_unit.
Proof.
  intros C c1 c2 H1 H2.
  eapply E_trans.
  - apply (comp_cn styp_top C c1 H1 0).
  - apply E_sym. apply (comp_cn styp_top C c2 H2 0).
Qed.

Lemma Coh_CN : forall C k, CohVal C (CN C k).
Proof.
  intros C k C' c1 c2 H1 H2.
  eapply E_trans.
  - apply (comp_cn C C' c1 H1 k).
  - apply E_sym. apply (comp_cn C C' c2 H2 k).
Qed.

Lemma open_lc_any : forall e x y,
  lc_exp (open_exp_wrt_exp e (trm_var_f x)) ->
  lc_exp (open_exp_wrt_exp e (trm_var_f y)).
Proof.
  intros e x y H.
  apply lcg_iff_lc.
  apply (proj2 (@lcg_open_rec e 0 y)).
  apply (proj1 (@lcg_open_rec e 0 x)).
  apply lcg_iff_lc. exact H.
Qed.

Lemma has_type_lc : forall Γ E dir A e, has_type Γ E dir A e -> lc_exp e.
Proof.
  intros Γ E dir A e H. induction H; simpl.
  - constructor.
  - constructor.
  - constructor.
  - apply lc_trm_app; assumption.
  - apply lc_trm_pair; assumption.
  - apply lc_trm_rcd; assumption.
  - apply lc_trm_proj; assumption.
  - assumption.
  - (* T_abs *)
    apply lc_trm_abs. intros y.
    destruct (atom_fresh L) as [x0 Hx0].
    apply (@open_lc_any e x0 y).
    apply H0. exact Hx0.
  - apply lc_trm_capp; assumption.
Qed.

(* ---------- trivial-types relation and basic star inversion ---------- *)
Lemma star_pair_inv : forall x1 x2 w,
  (step star) (trm_pair x1 x2) w ->
  exists y1 y2, w = trm_pair y1 y2 /\ (step star) x1 y1 /\ (step star) x2 y2.
Proof.
  intros x1 x2 w H. remember (trm_pair x1 x2) as s eqn:Es.
  revert x1 x2 Es. induction H; intros aa bb Es.
  - exists aa, bb. repeat split; auto; apply star_refl.
  - rewrite Es in H. inversion H; subst.
    + destruct (IHstar e1' bb eq_refl) as [u1 [u2 [Eu [S1 S2]]]].
      exists u1, u2. repeat split; auto.
      eapply star_trans.
      * apply star1. eassumption.
      * exact S1.
    + destruct (IHstar aa e2' eq_refl) as [u1 [u2 [Eu [S1 S2]]]].
      exists u1, u2. repeat split; auto.
      eapply star_trans.
      * apply star1. eassumption.
      * exact S2.
Qed.

Lemma E_to_AE : forall A v1 v2, WF A v1 -> WF A v2 -> E A v1 v2 -> AE A v1 v2.
Proof.
  intros A v1 v2 W1 W2 [u1 [u2 [S1 [S2 [Wu1 [Wu2 AE]]]]]].
  assert (u1 = v1) by
    (eapply star_value_det; [exact S1 | exact (@WF_value A u1 Wu1) | apply star_refl | exact (@WF_value A v1 W1)]).
  assert (u2 = v2) by
    (eapply star_value_det; [exact S2 | exact (@WF_value A u2 Wu2) | apply star_refl | exact (@WF_value A v2 W2)]).
  subst u1 u2. exact AE.
Qed.

Definition TR (A:styp) : Prop :=
  forall v1 v2, WF A v1 -> WF A v2 -> E A v1 v2.

Lemma TR_top : TR styp_top.
Proof.
  intros v1 v2 W1 W2. simpl in W1, W2. subst v1 v2.
  apply E_WF_self. simpl. reflexivity.
Qed.

Lemma TR_and : forall A B, TR A -> TR B -> TR (styp_and A B).
Proof.
  intros A B HA HB v1 v2 W1 W2. simpl in W1, W2.
  destruct W1 as [a1 [b1 [E1 [Wa1 Wb1]]]].
  destruct W2 as [a2 [b2 [E2 [Wa2 Wb2]]]].
  subst v1 v2. apply E_pair.
  - apply HA; assumption.
  - apply HB; assumption.
  - exact (@WF_lc B b1 Wb1).
  - exact (@WF_lc B b2 Wb2).
Qed.

Lemma TR_rcd : forall l A, TR A -> TR (styp_rcd l A).
Proof.
  intros l A HA v1 v2 W1 W2. simpl in W1, W2.
  destruct W1 as [a1 [E1 Wa1]]. destruct W2 as [a2 [E2 Wa2]].
  subst v1 v2. apply E_rcd. apply HA; assumption.
Qed.

Lemma TR_arrow : forall A B, TR B -> TR (styp_arrow A B).
Proof.
  intros A B HB v1 v2 W1 W2.
  destruct W1 as [lc1 [val1 app1]]. destruct W2 as [lc2 [val2 app2]].
  assert (WF1 : WF (styp_arrow A B) v1) by
    (split; [exact lc1 | split; [exact val1 | exact app1]]).
  assert (WF2 : WF (styp_arrow A B) v2) by
    (split; [exact lc2 | split; [exact val2 | exact app2]]).
  exists v1, v2.
  split.
  { apply star_refl. }
  split.
  { apply star_refl. }
  split.
  { exact WF1. }
  split.
  { exact WF2. }
  split.
  - exact lc1.
  - split.
    + exact lc2.
    + split.
      * exact val1.
      * split.
        -- exact val2.
        -- intros u1 u2 Wu1 Wu2 Au.
           destruct (app1 u1 u2 Wu1 Wu2 Au) as [w1 [w2 [S1 [S2 [Ww1 [Ww2 AEw]]]]]].
           destruct (app2 u1 u2 Wu1 Wu2 Au) as [x1 [x2 [T1 [T2 [Wx1 [Wx2 AEx]]]]]].
           exists w1, x2.
           split.
           ++ exact S1.
           ++ split.
              ** exact T2.
              ** split.
                 { exact Ww1. }
                 split.
                 { exact Wx2. }
                 exact (@E_to_AE B w1 x2 Ww1 Wx2 (HB w1 x2 Ww1 Wx2)).
Qed.

Lemma const_app_star : forall B w u,
  WF B w -> value u -> (step star) (trm_app (trm_abs w) u) w.
Proof.
  intros B w u Ww Hu.
  assert (Lw : lc_exp w) by (exact (@WF_lc B w Ww)).
  assert (Lab : lc_exp (trm_abs w)).
  { apply lc_trm_abs. intros y.
    unfold open_exp_wrt_exp.
    rewrite (@open_rec_lcg w 0 (lc_lcg w Lw) 0 (trm_var_f y) ltac:(lia)). exact Lw. }
  eapply (@star_trans step (trm_app (trm_abs w) u)
             (open_exp_wrt_exp w u) w).
  - apply star1. apply step_beta; [exact Lab | exact Hu].
  - unfold open_exp_wrt_exp.
    rewrite (@open_rec_lcg w 0 (lc_lcg w Lw) 0 u ltac:(lia)).
    apply star_refl.
Qed.

Lemma const_WF : forall A B w, WF B w -> WF (styp_arrow A B) (trm_abs w).
Proof.
  intros A B w Ww.
  assert (Lw : lc_exp w) by (exact (@WF_lc B w Ww)).
  assert (Lab : lc_exp (trm_abs w)).
  { apply lc_trm_abs. intros y.
    unfold open_exp_wrt_exp.
    rewrite (@open_rec_lcg w 0 (lc_lcg w Lw) 0 (trm_var_f y) ltac:(lia)). exact Lw. }
  split.
  - exact Lab.
  - split.
    + apply value_abs. exact Lab.
    + intros u1 u2 Wu1 Wu2 Au. exists w, w.
      split.
      { exact (@const_app_star B w u1 Ww (@WF_value A u1 Wu1)). }
      split.
      { exact (@const_app_star B w u2 Ww (@WF_value A u2 Wu2)). }
      split.
      { exact Ww. }
      split.
      { exact Ww. }
      { apply AE_refl. exact Ww. }
Qed.

Lemma TR_and_l : forall A B, TR (styp_and A B) -> TR A.
Proof.
  intros A B HTR v1 v2 W1 W2.
  set (ub := CN B 0).
  assert (Wub : WF B ub) by (unfold ub; apply CN_WF).
  assert (Wp1 : WF (styp_and A B) (trm_pair v1 ub)).
  { simpl. exists v1, ub. repeat split; auto. }
  assert (Wp2 : WF (styp_and A B) (trm_pair v2 ub)).
  { simpl. exists v2, ub. repeat split; auto. }
  pose proof (@E_to_AE (styp_and A B) (trm_pair v1 ub) (trm_pair v2 ub)
                Wp1 Wp2 (HTR (trm_pair v1 ub) (trm_pair v2 ub) Wp1 Wp2)) as AEp.
  simpl in AEp.
  destruct AEp as [a1 [b1 [a2 [b2 [E1 [E2 [A1 A2]]]]]]].
  injection E1 as H1 H2. injection E2 as H3 H4.
  subst a1 b1 a2 b2.
  apply (@E_V A v1 v2 W1 W2 A1).
Qed.

Lemma TR_and_r : forall A B, TR (styp_and A B) -> TR B.
Proof.
  intros A B HTR v1 v2 W1 W2.
  set (ua := CN A 0).
  assert (Wua : WF A ua) by (unfold ua; apply CN_WF).
  assert (Wp1 : WF (styp_and A B) (trm_pair ua v1)).
  { simpl. exists ua, v1. repeat split; auto. }
  assert (Wp2 : WF (styp_and A B) (trm_pair ua v2)).
  { simpl. exists ua, v2. repeat split; auto. }
  pose proof (@E_to_AE (styp_and A B) (trm_pair ua v1) (trm_pair ua v2)
                Wp1 Wp2 (HTR (trm_pair ua v1) (trm_pair ua v2) Wp1 Wp2)) as AEp.
  simpl in AEp.
  destruct AEp as [a1 [b1 [a2 [b2 [E1 [E2 [A1 A2]]]]]]].
  injection E1 as H1 H2. injection E2 as H3 H4.
  subst a1 b1 a2 b2.
  apply (@E_V B v1 v2 W1 W2 A2).
Qed.

Lemma TR_rcd_content : forall l A, TR (styp_rcd l A) -> TR A.
Proof.
  intros l A HTR v1 v2 W1 W2.
  assert (Wp1 : WF (styp_rcd l A) (trm_rcd l v1)).
  { simpl. exists v1. repeat split; auto. }
  assert (Wp2 : WF (styp_rcd l A) (trm_rcd l v2)).
  { simpl. exists v2. repeat split; auto. }
  pose proof (@E_to_AE (styp_rcd l A) (trm_rcd l v1) (trm_rcd l v2)
                Wp1 Wp2 (HTR (trm_rcd l v1) (trm_rcd l v2) Wp1 Wp2)) as AEp.
  simpl in AEp.
  destruct AEp as [a1 [a2 [E1 [E2 A12]]]].
  injection E1 as H1. injection E2 as H2. subst a1 a2.
  apply (@E_V A v1 v2 W1 W2 A12).
Qed.

Lemma TR_arrow_cod : forall A B, TR (styp_arrow A B) -> TR B.
Proof.
  intros A B HTR w1 w2 W1 W2.
  assert (WF1 : WF (styp_arrow A B) (trm_abs w1)) by (apply const_WF; exact W1).
  assert (WF2 : WF (styp_arrow A B) (trm_abs w2)) by (apply const_WF; exact W2).
  pose proof (@E_to_AE (styp_arrow A B) (trm_abs w1) (trm_abs w2)
                WF1 WF2 (HTR (trm_abs w1) (trm_abs w2) WF1 WF2)) as AEp.
  destruct AEp as [lc1 [lc2 [val1 [val2 app]]]].
  destruct (app (CN A 0) (CN A 0) (CN_WF A 0) (CN_WF A 0)
              (AE_refl A (CN A 0) (CN_WF A 0)))
    as [x1 [x2 [T1 [T2 [Wx1 [Wx2 AEx]]]]]].
  assert (Hx1 : x1 = w1) by
    (eapply star_value_det; [exact T1 | exact (@WF_value B x1 Wx1)
      | apply (@const_app_star B w1 (CN A 0) W1 (@WF_value A (CN A 0) (CN_WF A 0)))
      | exact (@WF_value B w1 W1)]).
  assert (Hx2 : x2 = w2) by
    (eapply star_value_det; [exact T2 | exact (@WF_value B x2 Wx2)
      | apply (@const_app_star B w2 (CN A 0) W2 (@WF_value A (CN A 0) (CN_WF A 0)))
      | exact (@WF_value B w2 W2)]).
  subst x1 x2.
  apply (@E_V B w1 w2 W1 W2 AEx).
Qed.

Fixpoint TR_sub (A C:styp)(c:co)(H:sub A C c) {struct H} : TR A -> TR C :=
  match H in sub A' C' c' return TR A' -> TR C' with
  | S_refl A0 => fun HTR => HTR
  | S_trans A1 A3 c1 c2 A2 H1 H2 =>
      fun HTR => TR_sub A2 A3 c1 H1 (TR_sub A1 A2 c2 H2 HTR)
  | S_top A0 => fun _ => TR_top
  | S_topArr => fun _ => @TR_arrow styp_top styp_top TR_top
  | S_topRcd l => fun _ => @TR_rcd l styp_top TR_top
  | S_arr A1 A2 B1 B2 c1 c2 H1 H2 =>
      fun HTR => @TR_arrow B1 B2
        (TR_sub A2 B2 c2 H2 (@TR_arrow_cod A1 A2 HTR))
  | S_and A1 A2 A3 c1 c2 H1 H2 =>
      fun HTR => @TR_and A2 A3 (TR_sub A1 A2 c1 H1 HTR) (TR_sub A1 A3 c2 H2 HTR)
  | S_andl A1 A2 => fun HTR => @TR_and_l A1 A2 HTR
  | S_andr A1 A2 => fun HTR => @TR_and_r A1 A2 HTR
  | S_distArr A1 A2 A3 =>
      fun HTR => @TR_arrow A1 (styp_and A2 A3)
        (@TR_and A2 A3
          (@TR_arrow_cod A1 A2 (@TR_and_l (styp_arrow A1 A2) (styp_arrow A1 A3) HTR))
          (@TR_arrow_cod A1 A3 (@TR_and_r (styp_arrow A1 A2) (styp_arrow A1 A3) HTR)))
  | S_rcd l A B c H1 =>
      fun HTR => @TR_rcd l B (TR_sub A B c H1 (@TR_rcd_content l A HTR))
  | S_distRcd l A B =>
      fun HTR => @TR_rcd l (styp_and A B)
        (@TR_and A B
          (@TR_rcd_content l A (@TR_and_l (styp_rcd l A) (styp_rcd l B) HTR))
          (@TR_rcd_content l B (@TR_and_r (styp_rcd l A) (styp_rcd l B) HTR)))
  end.

Lemma TR_of_sub_top : forall C c, sub styp_top C c -> TR C.
Proof. intros. exact (@TR_sub styp_top C c H TR_top). Qed.

(* ---------- environment invariant for open-term semantics ---------- *)
Definition EnvOK (Γ:sctx) (σ:var->exp) : Prop :=
  forall x A, binds x A Γ -> WF A (σ x) /\ CohVal A (σ x).

Lemma EnvOK_E : forall Γ σ, EnvOK Γ σ ->
  forall x A, binds x A Γ -> E A (σ x) (σ x).
Proof.
  intros Γ σ HE x A Hb. destruct (HE x A Hb) as [W _].
  apply E_WF_self. exact W.
Qed.

Lemma EnvOK_coerce : forall Γ σ, EnvOK Γ σ ->
  forall x A B c, binds x A Γ -> sub A B c -> CohVal B (trm_capp c (σ x)).
Proof.
  intros Γ σ HE x A B c Hb Hs.
  destruct (HE x A Hb) as [W HC].
  apply (@Coh_coerce A B (σ x) c).
  - apply E_WF_self. exact W.
  - exact HC.
  - exact Hs.
Qed.

Lemma EnvOK_extend : forall Γ σ x A u,
  EnvOK Γ σ -> uniq ((x~A)++Γ) ->
  WF A u -> CohVal A u ->
  EnvOK ((x~A)++Γ) (extend σ x u).
Proof.
  intros Γ σ x A u HE HUniq WU CU y B Hb.
  apply binds_cons_1 in Hb.
  destruct Hb as [[Hxy HAB]|Htail].
  - subst y B. unfold extend.
    destruct (eq_var x x) as [E|E]; [split; assumption | exfalso; apply E; reflexivity].
  - unfold extend.
    destruct (eq_var y x) as [Hyx|Hneq].
    + exfalso. subst y.
      apply (@binds_dom_contradiction _ x B Γ Htail).
      exact (@uniq_cons_2 _ x A Γ HUniq).
    + apply HE. exact Htail.
Qed.

(* ---------- uniqueness of typing contexts and WF-environment semantics ---------- *)
Lemma has_type_uniq : forall Γ E dir A e, has_type Γ E dir A e -> uniq Γ.
Proof.
  intros Γ E dir A e H. induction H.
  - exact H.
  - exact H.
  - exact H.
  - exact IHhas_type1.
  - exact IHhas_type1.
  - exact IHhas_type.
  - exact IHhas_type.
  - exact IHhas_type.
  - (* T_abs *)
    destruct (atom_fresh L) as [x0 Hx0].
    apply (@uniq_cons_1 _ x0 A). exact (H0 x0 Hx0).
  - exact IHhas_type.
Qed.

Definition EnvWF (Γ:sctx) (σ:var->exp) : Prop :=
  (forall x, lc_exp (σ x)) /\
  (forall x A, binds x A Γ -> WF A (σ x)).

Lemma EnvWF_lcg : forall Γ σ, EnvWF Γ σ -> forall x, lcg 0 (σ x).
Proof.
  intros Γ σ [Hlc _] x. apply lc_lcg. exact (Hlc x).
Qed.

Lemma EnvWF_extend : forall Γ σ x A u,
  EnvWF Γ σ -> uniq ((x~A)++Γ) -> WF A u ->
  EnvWF ((x~A)++Γ) (extend σ x u).
Proof.
  intros Γ σ x A u [Hlc Hb] HUniq Wu. split.
  - intros y. unfold extend. destruct (eq_var y x) as [E|E]; [exact (@WF_lc A u Wu) | apply Hlc].
  - intros y B Hbind. apply binds_cons_1 in Hbind.
    destruct Hbind as [[Hxy HAB]|Htail].
    + subst y B. unfold extend.
      destruct (eq_var x x) as [E|E]; [exact Wu | exfalso; apply E; reflexivity].
    + unfold extend. destruct (eq_var y x) as [Hyx|Hneq].
      * exfalso. subst y.
        apply (@binds_dom_contradiction _ x B Γ Htail).
        exact (@uniq_cons_2 _ x A Γ HUniq).
      * apply Hb. exact Htail.
Qed.

(* ---------- contextual logical relation over values and terms ---------- *)
Fixpoint OV (A:styp) (v1 v2:exp) : Prop :=
  match A with
  | styp_top => v1 = trm_unit /\ v2 = trm_unit
  | styp_nat => exists k, v1 = trm_lit k /\ v2 = trm_lit k
  | styp_and A1 A2 =>
      disjoint A1 A2 /\
      (exists a1 b1 a2 b2,
        v1 = trm_pair a1 b1 /\ v2 = trm_pair a2 b2 /\
        OV A1 a1 a2 /\ OV A2 b1 b2)
  | styp_rcd l A1 =>
      exists a1 a2, v1 = trm_rcd l a1 /\ v2 = trm_rcd l a2 /\ OV A1 a1 a2
  | styp_arrow A1 A2 =>
      lc_exp v1 /\ lc_exp v2 /\ value v1 /\ value v2 /\
      (forall u1 u2,
        (exists a1 a2, (step star) u1 a1 /\ (step star) u2 a2 /\ OV A1 a1 a2) ->
        exists w1 w2,
          (step star) (trm_app v1 u1) w1 /\
          (step star) (trm_app v2 u2) w2 /\
          OV A2 w1 w2)
  end.

Definition Rel (A:styp) (t1 t2:exp) : Prop :=
  exists v1 v2, (step star) t1 v1 /\ (step star) t2 v2 /\ OV A v1 v2.

Lemma OV_value_l : forall A v1 v2, OV A v1 v2 -> value v1.
Proof.
  intros A. induction A; intros v1 v2 H; simpl in H.
  - destruct H; subst; constructor.
  - destruct H as [k [H1 H2]]; subst; constructor.
  - destruct H as [_ [a1 [b1 [a2 [b2 [E1 [E2 [X Y]]]]]]]].
    subst; apply value_pair; [exact (IHA1 a1 a2 X) | exact (IHA2 b1 b2 Y)].
  - destruct H as [lc1 [lc2 [val1 [val2 app]]]]; exact val1.
  - destruct H as [a1 [a2 [E1 [E2 X]]]]; subst; apply value_rcd.
    exact (IHA a1 a2 X).
Qed.

Lemma OV_value_r : forall A v1 v2, OV A v1 v2 -> value v2.
Proof.
  intros A. induction A; intros v1 v2 H; simpl in H.
  - destruct H; subst; constructor.
  - destruct H as [k [H1 H2]]; subst; constructor.
  - destruct H as [_ [a1 [b1 [a2 [b2 [E1 [E2 [X Y]]]]]]]].
    subst; apply value_pair; [exact (IHA1 a1 a2 X) | exact (IHA2 b1 b2 Y)].
  - destruct H as [lc1 [lc2 [val1 [val2 app]]]]; exact val2.
  - destruct H as [a1 [a2 [E1 [E2 X]]]]; subst; apply value_rcd.
    exact (IHA a1 a2 X).
Qed.

Lemma Rel_nat_kleene : forall t1 t2, Rel styp_nat t1 t2 -> kleene_equiv t1 t2.
Proof.
  intros t1 t2 [v1 [v2 [S1 [S2 H]]]]. simpl in H.
  destruct H as [k [E1 E2]]. subst v1 v2.
  exists k; split; assumption.
Qed.

Lemma Rel_star_l : forall A t t' u, (step star) t t' -> Rel A t' u -> Rel A t u.
Proof.
  intros A t t' u Ht [v1 [v2 [S1 [S2 H]]]].
  exists v1, v2. repeat split; auto.
  eapply star_trans; [exact Ht | exact S1].
Qed.

Lemma Rel_star_r : forall A t u u', (step star) u u' -> Rel A t u' -> Rel A t u.
Proof.
  intros A t u u' Hu [v1 [v2 [S1 [S2 H]]]].
  exists v1, v2. repeat split; auto.
  eapply star_trans; [exact Hu | exact S2].
Qed.

Lemma Rel_top : Rel styp_top trm_unit trm_unit.
Proof.
  exists trm_unit, trm_unit.
  split; [apply star_refl | split; [apply star_refl | simpl; split; reflexivity]].
Qed.

Lemma Rel_nat_lit : forall k, Rel styp_nat (trm_lit k) (trm_lit k).
Proof.
  intros. exists (trm_lit k), (trm_lit k).
  split; [apply star_refl | split; [apply star_refl | simpl; exists k; split; reflexivity]].
Qed.

Lemma Rel_and : forall A B a1 b1 a2 b2,
  disjoint A B -> OV A a1 a2 -> OV B b1 b2 ->
  Rel (styp_and A B) (trm_pair a1 b1) (trm_pair a2 b2).
Proof.
  intros A B a1 b1 a2 b2 HD X Y.
  exists (trm_pair a1 b1), (trm_pair a2 b2).
  split; [apply star_refl | split; [apply star_refl |]].
  simpl. split; [exact HD |].
  exists a1, b1, a2, b2. repeat split; auto.
Qed.

Lemma Rel_rcd : forall l A a1 a2, OV A a1 a2 ->
  Rel (styp_rcd l A) (trm_rcd l a1) (trm_rcd l a2).
Proof.
  intros l A a1 a2 X.
  exists (trm_rcd l a1), (trm_rcd l a2).
  split; [apply star_refl | split; [apply star_refl |]].
  simpl. exists a1, a2. repeat split; auto.
Qed.

Lemma OV_sym : forall A v1 v2, OV A v1 v2 -> OV A v2 v1.
Proof.
  intros A. induction A; intros v1 v2 H; simpl in H |- *.
  - destruct H as [E1 E2]; subst; auto.
  - destruct H as [k [E1 E2]]; subst; exists k; auto.
  - destruct H as [HD [a1 [b1 [a2 [b2 [E1 [E2 [X Y]]]]]]]].
    subst v1 v2. split; [exact HD |].
    exists a2, b2, a1, b1.
    split; [reflexivity | split; [reflexivity | split;
      [exact (IHA1 a1 a2 X) | exact (IHA2 b1 b2 Y)]]].
  - destruct H as [lc1 [lc2 [val1 [val2 app]]]].
    split; [exact lc2 | split; [exact lc1 | split; [exact val2 | split; [exact val1 |]]]].
    intros u1 u2 Hu.
    destruct Hu as [a1 [a2 [T1 [T2 Y]]]].
    assert (Hu' : exists a1 a2 : exp, (step star) u2 a1 /\ (step star) u1 a2 /\ OV A1 a1 a2).
    { exists a2, a1. split; [exact T2 | split; [exact T1 | exact (IHA1 a1 a2 Y)]]. }
    destruct (app u2 u1 Hu') as [w1' [w2' [S2' [S1' Z]]]].
    exists w2', w1'.
    split; [exact S1' | split; [exact S2' | exact (IHA2 w1' w2' Z)]].
  - destruct H as [a1 [a2 [E1 [E2 X]]]].
    subst v1 v2. exists a2, a1.
    split; [reflexivity | split; [reflexivity | exact (IHA a1 a2 X)]].
Qed.

Lemma OV_trans_self :
  forall A,
    (forall v1 v2 v3, OV A v1 v2 -> OV A v2 v3 -> OV A v1 v3) /\
    (forall v1 v2, OV A v1 v2 -> OV A v1 v1).
Proof.
  intros A. induction A; split; intros.
  - (* top trans *) simpl in *. destruct H as [E1 E2]; subst; auto.
  - (* top self *) simpl in *. destruct H as [E1 E2]; subst; auto.
  - (* nat trans *) simpl in *. destruct H as [k1 [E1 E2]].
    destruct H0 as [k2 [E3 E4]]. subst. exists k1; auto.
  - (* nat self *) simpl in *. destruct H as [k [E1 E2]]; subst; exists k; auto.
  - (* and trans *)
    simpl in *. destruct H as [HD1 [a1 [b1 [a2 [b2 [E1 [E2 [X1 Y1]]]]]]]].
    destruct H0 as [HD2 [a2' [b2' [a3 [b3 [E3 [E4 [X2 Y2]]]]]]]].
    assert (a2 = a2') by congruence. assert (b2 = b2') by congruence. subst a2' b2'.
    subst v1 v2 v3. split; [exact HD1 |].
    exists a1, b1, a3, b3.
    split; [reflexivity | split; [reflexivity | split;
      [exact (proj1 (IHA1) a1 a2 a3 X1 X2)
      | exact (proj1 (IHA2) b1 b2 b3 Y1 Y2)]]].
  - (* and self *)
    simpl in *. destruct H as [HD [a1 [b1 [a2 [b2 [E1 [E2 [X Y]]]]]]]].
    subst v1 v2. split; [exact HD |].
    exists a1, b1, a1, b1.
    split; [reflexivity | split; [reflexivity | split;
      [exact (proj2 (IHA1) a1 a2 X) | exact (proj2 (IHA2) b1 b2 Y)]]].
  - (* arrow trans *)
    simpl in *. destruct H as [lc1 [lc2 [val1 [val2 app12]]]].
    destruct H0 as [lc2x [lc3 [val2x [val3 app23]]]].
    split; [exact lc1 | split; [exact lc3 | split; [exact val1 | split; [exact val3 |]]]].
    intros u1 u2 Hu.
    destruct (app12 u1 u2 Hu) as [w1 [w2 [S1 [S2 X]]]].
    assert (Hu2 : exists a1 a2 : exp, (step star) u2 a1 /\ (step star) u2 a2 /\ OV A1 a1 a2).
    { destruct Hu as [a1 [a2 [T1 [T2 Y]]]]. exists a2, a2.
      split; [exact T2 | split; [exact T2 | exact (proj2 (IHA1) a2 a1 (OV_sym A1 a1 a2 Y))]]. }
    destruct (app23 u2 u2 Hu2) as [w2' [w3 [T2' [T3 Y]]]].
    assert (w2 = w2') by
      (eapply star_value_det; [exact S2 | eapply OV_value_r; exact X |
       exact T2' | eapply OV_value_l; exact Y]).
    subst w2'.
    exists w1, w3.
    split; [exact S1 | split; [exact T3 | exact (proj1 (IHA2) w1 w2 w3 X Y)]].
  - (* arrow self *)
    simpl in *. destruct H as [lc1 [lc2 [val1 [val2 app]]]].
    split; [exact lc1 | split; [exact lc1 | split; [exact val1 | split; [exact val1 |]]]].
    intros u1 u2 Hu.
    destruct (app u1 u2 Hu) as [w1 [w2 [S1 [S2 X]]]].
    assert (Hu2 : exists a1 a2 : exp, (step star) u2 a1 /\ (step star) u2 a2 /\ OV A1 a1 a2).
    { destruct Hu as [a1 [a2 [T1 [T2 Y]]]]. exists a2, a2.
      split; [exact T2 | split; [exact T2 | exact (proj2 (IHA1) a2 a1 (OV_sym A1 a1 a2 Y))]]. }
    destruct (app u2 u2 Hu2) as [w2' [w1' [T2 [T1' Y]]]].
    assert (w2 = w1') by
      (eapply star_value_det; [exact S2 | eapply OV_value_r; exact X |
       exact T1' | eapply OV_value_r; exact Y]).
    subst w1'.
    exists w1, w2'.
    split; [exact S1 | split; [exact T2 |
      exact (proj1 (IHA2) w1 w2 w2' X (OV_sym A2 w2' w2 Y))]].
  - (* rcd trans *)
    simpl in *. destruct H as [a1 [a2 [E1 [E2 X]]]].
    destruct H0 as [a2' [a3 [E3 [E4 Y]]]].
    assert (a2 = a2') by congruence. subst a2'.
    subst v1 v2 v3. exists a1, a3.
    split; [reflexivity | split; [reflexivity | exact (proj1 (IHA) a1 a2 a3 X Y)]].
  - (* rcd self *)
    simpl in *. destruct H as [a1 [a2 [E1 [E2 X]]]].
    subst v1 v2. exists a1, a1.
    split; [reflexivity | split; [reflexivity | exact (proj2 (IHA) a1 a2 X)]].
Qed.

Lemma OV_trans : forall A v1 v2 v3, OV A v1 v2 -> OV A v2 v3 -> OV A v1 v3.
Proof. intros. exact (proj1 (OV_trans_self A) v1 v2 v3 H H0). Qed.

Lemma OV_self : forall A v1 v2, OV A v1 v2 -> OV A v1 v1.
Proof. intros. exact (proj2 (OV_trans_self A) v1 v2 H). Qed.

Lemma Rel_sym : forall A t1 t2, Rel A t1 t2 -> Rel A t2 t1.
Proof.
  intros A t1 t2 [v1 [v2 [S1 [S2 X]]]].
  exists v2, v1. repeat split; auto.
  apply OV_sym; exact X.
Qed.

Lemma Rel_trans : forall A t1 t2 t3, Rel A t1 t2 -> Rel A t2 t3 -> Rel A t1 t3.
Proof.
  intros A t1 t2 t3 [v1 [v2 [S1 [S2 X]]]] [v2' [v3 [T2 [T3 Y]]]].
  assert (v2 = v2') by
    (eapply star_value_det; [exact S2 | eapply OV_value_r; exact X |
     exact T2 | eapply OV_value_l; exact Y]).
  subst v2'. exists v1, v3. repeat split; auto.
  exact (OV_trans A v1 v2 v3 X Y).
Qed.

Lemma Rel_self : forall A t1 t2, Rel A t1 t2 -> Rel A t1 t1.
Proof.
  intros A t1 t2 [v1 [v2 [S1 [S2 X]]]].
  exists v1, v1.
  split; [exact S1 | split; [exact S1 | exact (OV_self A v1 v2 X)]].
Qed.

Lemma OV_lc_l : forall A v1 v2, OV A v1 v2 -> lc_exp v1.
Proof.
  intros A. induction A; intros v1 v2 H; simpl in H.
  - destruct H as [E1 E2]; subst; constructor.
  - destruct H as [k [E1 E2]]; subst; constructor.
  - destruct H as [HD [a1 [b1 [a2 [b2 [E1 [E2 [X Y]]]]]]]].
    subst; apply lc_trm_pair; [exact (IHA1 a1 a2 X) | exact (IHA2 b1 b2 Y)].
  - destruct H as [lc1 [lc2 [val1 [val2 app]]]]; exact lc1.
  - destruct H as [a1 [a2 [E1 [E2 X]]]]; subst; apply lc_trm_rcd.
    exact (IHA a1 a2 X).
Qed.

Lemma OV_lc_r : forall A v1 v2, OV A v1 v2 -> lc_exp v2.
Proof.
  intros A. induction A; intros v1 v2 H; simpl in H.
  - destruct H as [E1 E2]; subst; constructor.
  - destruct H as [k [E1 E2]]; subst; constructor.
  - destruct H as [HD [a1 [b1 [a2 [b2 [E1 [E2 [X Y]]]]]]]].
    subst; apply lc_trm_pair; [exact (IHA1 a1 a2 X) | exact (IHA2 b1 b2 Y)].
  - destruct H as [lc1 [lc2 [val1 [val2 app]]]]; exact lc2.
  - destruct H as [a1 [a2 [E1 [E2 X]]]]; subst; apply lc_trm_rcd.
    exact (IHA a1 a2 X).
Qed.

Lemma Rel_app : forall A1 A2 f1 f2 g1 g2,
  Rel (styp_arrow A1 A2) f1 f2 ->
  Rel A1 g1 g2 -> lc_exp g1 -> lc_exp g2 ->
  Rel A2 (trm_app f1 g1) (trm_app f2 g2).
Proof.
  intros A1 A2 f1 f2 g1 g2
    [vf1 [vf2 [Sf1 [Sf2 VF]]]]
    [vg1 [vg2 [Sg1 [Sg2 VG]]]] Hg1lc Hg2lc.
  simpl in VF. destruct VF as [lcf1 [lcf2 [valf1 [valf2 app]]]].
  assert (Hrel : exists a1 a2 : exp, (step star) g1 a1 /\ (step star) g2 a2 /\ OV A1 a1 a2)
    by (exists vg1, vg2; repeat split; auto).
  destruct (app g1 g2 Hrel) as [w1 [w2 [T1 [T2 OW]]]].
  exists w1, w2.
  split.
  - eapply star_trans.
    + apply star_app_l; [exact Sf1 | exact Hg1lc].
    + exact T1.
  - split.
    + eapply star_trans.
      * apply star_app_l; [exact Sf2 | exact Hg2lc].
      * exact T2.
    + exact OW.
Qed.

(* ---------- inferred types are determined by the source ---------- *)
Lemma Inf_typ_unique : forall E Γ A1 e1,
  has_type Γ E Inf A1 e1 ->
  forall A2 e2, has_type Γ E Inf A2 e2 -> A1 = A2.
Proof.
  intros E. induction E; intros Γ A1 e1 H1 A2 e2 H2.
  - (* e_var_b *) inversion H1.
  - (* e_var_f *) inversion H1; subst. inversion H2; subst.
    eapply binds_unique; eassumption.
  - (* e_top *) inversion H1; subst. inversion H2; subst. reflexivity.
  - (* e_lit *) inversion H1; subst. inversion H2; subst. reflexivity.
  - (* e_abs *) inversion H1.
  - (* e_app *) inversion H1; subst. inversion H2; subst.
    specialize (IHE1 Γ (styp_arrow A3 A1) e0 H4 (styp_arrow A4 A2) e1 H6).
    injection IHE1 as _ HA2. exact HA2.
  - (* e_merge *) inversion H1; subst. inversion H2; subst.
    specialize (IHE1 Γ A0 e0 H3 A1 e1 H4).
    specialize (IHE2 Γ A3 e3 H5 A4 e4 H8).
    subst. reflexivity.
  - (* e_anno *) inversion H1; subst. inversion H2; subst. reflexivity.
  - (* e_rcd *) inversion H1; subst. inversion H2; subst.
    specialize (IHE Γ A e H3 A0 e0 H4). subst. reflexivity.
  - (* e_proj *) inversion H1; subst. inversion H2; subst.
    specialize (IHE Γ (styp_rcd l A1) e H3 (styp_rcd l A2) e0 H4).
    injection IHE as HA. exact HA.
Qed.

Lemma Rel_of_OV : forall A v1 v2, OV A v1 v2 -> Rel A v1 v2.
Proof.
  intros. exists v1, v2. repeat split; auto; apply star_refl.
Qed.

Lemma OV_of_Rel_values : forall A v1 v2,
  value v1 -> value v2 -> Rel A v1 v2 -> OV A v1 v2.
Proof.
  intros A v1 v2 Hv1 Hv2 [u1 [u2 [S1 [S2 X]]]].
  assert (u1 = v1) by (eapply star_from_value; eassumption).
  assert (u2 = v2) by (eapply star_from_value; eassumption).
  subst u1 u2. exact X.
Qed.

Lemma Rel_pair : forall A B a1 a2 b1 b2,
  disjoint A B -> Rel A a1 a2 -> Rel B b1 b2 ->
  lc_exp b1 -> lc_exp b2 ->
  Rel (styp_and A B) (trm_pair a1 b1) (trm_pair a2 b2).
Proof.
  intros A B a1 a2 b1 b2 HD
    [va1 [va2 [S1 [S2 X]]]] [vb1 [vb2 [T1 [T2 Y]]]] Hb1 Hb2.
  exists (trm_pair va1 vb1), (trm_pair va2 vb2).
  split.
  - eapply star_trans.
    + apply star_pair_l; [exact S1 | exact Hb1].
    + apply star_pair_r; [eapply OV_value_l; exact X | exact T1].
  - split.
    + eapply star_trans.
      * apply star_pair_l; [exact S2 | exact Hb2].
      * apply star_pair_r; [eapply OV_value_r; exact X | exact T2].
    + simpl. split; [exact HD |].
      exists va1, vb1, va2, vb2.
      split; [reflexivity | split; [reflexivity | split; [exact X | exact Y]]].
Qed.

Lemma sub_comp : forall A B C c1 c2,
  sub A B c1 -> sub B C c2 -> sub A C (co_trans c2 c1).
Proof. intros. exact (S_trans A C c2 c1 B H0 H). Qed.

Lemma Rel_rcd2 : forall l A a1 a2,
  Rel A a1 a2 -> Rel (styp_rcd l A) (trm_rcd l a1) (trm_rcd l a2).
Proof.
  intros l A a1 a2 [v1 [v2 [S1 [S2 X]]]].
  exists (trm_rcd l v1), (trm_rcd l v2).
  split.
  { apply star_rcd; exact S1. }
  split.
  { apply star_rcd; exact S2. }
  simpl. exists v1, v2. repeat split; auto.
Qed.

Lemma Rel_arrow : forall A B f1 f2,
  lc_exp f1 -> lc_exp f2 -> value f1 -> value f2 ->
  (forall u1 u2, Rel A u1 u2 ->
     exists w1 w2, (step star) (trm_app f1 u1) w1 /\
                   (step star) (trm_app f2 u2) w2 /\ OV B w1 w2) ->
  Rel (styp_arrow A B) f1 f2.
Proof.
  intros A B f1 f2 L1 L2 V1 V2 App.
  exists f1, f2.
  split.
  { apply star_refl. }
  split.
  { apply star_refl. }
  simpl. repeat split; auto.
Qed.

Lemma OV_top_inv : forall v1 v2, OV styp_top v1 v2 ->
  v1 = trm_unit /\ v2 = trm_unit.
Proof. intros. exact H. Qed.

Lemma OV_nat_inv : forall v1 v2, OV styp_nat v1 v2 ->
  exists k, v1 = trm_lit k /\ v2 = trm_lit k.
Proof. intros. exact H. Qed.

Lemma OV_arrow_inv : forall A1 A2 v1 v2, OV (styp_arrow A1 A2) v1 v2 ->
  lc_exp v1 /\ lc_exp v2 /\ value v1 /\ value v2 /\
  (forall u1 u2,
    (exists a1 a2, (step star) u1 a1 /\ (step star) u2 a2 /\ OV A1 a1 a2) ->
    exists w1 w2, (step star) (trm_app v1 u1) w1 /\
                  (step star) (trm_app v2 u2) w2 /\ OV A2 w1 w2).
Proof. intros. exact H. Qed.

Lemma Rel_nat_reduce_l : forall t k,
  (step star) t (trm_lit k) -> Rel styp_nat t (trm_lit k).
Proof.
  intros t k H. exists (trm_lit k), (trm_lit k).
  split; [exact H | split; [apply star_refl | simpl; exists k; split; reflexivity]].
Qed.

Lemma Rel_nat_reduce_r : forall t k,
  (step star) t (trm_lit k) -> Rel styp_nat (trm_lit k) t.
Proof.
  intros t k H. exists (trm_lit k), (trm_lit k).
  split; [apply star_refl | split; [exact H | simpl; exists k; split; reflexivity]].
Qed.

(* ---------- types that can be coerced to nat ---------- *)
Inductive NatReach : styp -> Prop :=
  | NR_nat : NatReach styp_nat
  | NR_andl : forall A B, NatReach A -> NatReach (styp_and A B)
  | NR_andr : forall A B, NatReach B -> NatReach (styp_and A B).

Lemma NatReach_sub : forall A B c, sub A B c -> NatReach B -> NatReach A.
Proof.
  intros A B c Hsub. induction Hsub; intros h;
    try (inversion h; subst); eauto using NR_andl, NR_andr.
Qed.

Lemma sub_nat_reach : forall A c, sub A styp_nat c -> NatReach A.
Proof. intros. apply (@NatReach_sub A styp_nat c H). constructor. Qed.

Lemma disjoint_NatReach : forall A B, disjoint A B -> NatReach A -> NatReach B -> False.
Proof.
  intros A B D. induction D; intros hA hB;
    try (inversion hA; subst); try (inversion hB; subst); eauto.
Qed.
Lemma sub_nat_nat_star : forall c, sub styp_nat styp_nat c ->
  forall k, (step star) (trm_capp c (trm_lit k)) (trm_lit k).
Proof.
  intros c Hs k.
  pose proof (comp_cn styp_nat styp_nat c Hs k) as HE.
  change (E styp_nat (trm_capp c (trm_lit k)) (trm_lit k)) in HE.
  destruct HE as [v1 [v2 [S1 [S2 [W1 [W2 AE]]]]]].
  assert (v2 = trm_lit k) by
    (exact (@star_from_value (trm_lit k) v2 (value_lit k) S2)).
  subst v2.
  simpl in AE. destruct AE as [j [E1 E2]].
  assert (j = k) by congruence. subst j. subst v1.
  exact S1.
Qed.

Lemma OV_nat_coerce : forall v1 v2, OV styp_nat v1 v2 ->
  forall c1 c2, sub styp_nat styp_nat c1 -> sub styp_nat styp_nat c2 ->
  Rel styp_nat (trm_capp c1 v1) (trm_capp c2 v2).
Proof.
  intros v1 v2 H c1 c2 H1 H2.
  destruct H as [k [E1 E2]]. subst v1 v2.
  exists (trm_lit k), (trm_lit k).
  split.
  - apply sub_nat_nat_star; assumption.
  - split.
    + apply sub_nat_nat_star; assumption.
    + simpl. exists k; split; reflexivity.
Qed.

Lemma NatReach_and_inv : forall A B,
  NatReach (styp_and A B) -> NatReach A \/ NatReach B.
Proof. intros A B h. inversion h; subst; auto. Qed.

Lemma NatReach_not_top : NatReach styp_top -> False.
Proof. intros h. inversion h. Qed.

Lemma NatReach_not_arrow : forall A B, NatReach (styp_arrow A B) -> False.
Proof. intros A B h. inversion h. Qed.

Lemma NatReach_not_rcd : forall l A, NatReach (styp_rcd l A) -> False.
Proof. intros l A h. inversion h. Qed.

Lemma disjoint_sub_nat : forall A B c1 c2,
  sub A styp_nat c1 -> sub B styp_nat c2 -> disjoint A B -> False.
Proof.
  intros A B c1 c2 H1 H2 HD.
  exact (@disjoint_NatReach A B HD (sub_nat_reach A c1 H1) (sub_nat_reach B c2 H2)).
Qed.

Lemma NatReach_and_not_both_disjoint : forall A B,
  disjoint A B -> NatReach (styp_and A B) ->
  NatReach A \/ NatReach B.
Proof. intros. apply NatReach_and_inv. exact H0. Qed.

(* ---------- coercion images of an intersection value (junk allowed) ---------- *)
Inductive ImgJ (A C:styp) (a w:exp) : styp -> exp -> Set :=
  | ImgJ_refl : ImgJ A C a w (styp_and A C) (trm_pair a w)
  | ImgJ_step : forall X Y c v,
      sub X Y c -> ImgJ A C a w X v ->
      ImgJ A C a w Y (trm_capp c v).

Lemma ImgJ_of_sub : forall A C a w X c,
  sub (styp_and A C) X c ->
  ImgJ A C a w X (trm_capp c (trm_pair a w)).
Proof.
  intros A C a w X c H.
  eapply ImgJ_step; [exact H | apply ImgJ_refl].
Defined.

Lemma ImgJ_refl_value : forall A C a w,
  value a -> value w -> ImgJ A C a w (styp_and A C) (trm_pair a w).
Proof. intros. apply ImgJ_refl. Qed.

Fixpoint ImgJ_depth (A C:styp) (a w:exp) (X:styp) (v:exp)
  (H:ImgJ A C a w X v) {struct H} : nat :=
  match H with
  | ImgJ_refl _ _ _ _ => 0
  | ImgJ_step _ _ _ _ _ _ _ _ Hsub Hprev => S (ImgJ_depth A C a w _ _ Hprev)
  end.

Lemma ImgJ_depth_of_sub : forall A C a w X c
  (H:sub (styp_and A C) X c),
  ImgJ_depth A C a w X (trm_capp c (trm_pair a w))
    (ImgJ_of_sub A C a w X c H) = 1.
Proof. intros. reflexivity. Qed.

Lemma kleene_equiv_sym : forall t1 t2, kleene_equiv t1 t2 -> kleene_equiv t2 t1.
Proof.
  intros t1 t2 [k [S1 S2]]. exists k; split; assumption.
Qed.

Lemma kleene_equiv_trans : forall t1 t2 t3,
  kleene_equiv t1 t2 -> kleene_equiv t2 t3 -> kleene_equiv t1 t3.
Proof.
  intros t1 t2 t3 [k [S1 S2]] [l [T2 T3]].
  assert (Hkl : trm_lit k = trm_lit l) by
    (eapply star_value_det; [exact S2 | apply value_lit | exact T2 | apply value_lit]).
  injection Hkl as Hkl. subst l. exists k. split; assumption.
Qed.

Lemma kleene_equiv_of_star_lit : forall t1 t2 k,
  (step star) t1 (trm_lit k) -> (step star) t2 (trm_lit k) ->
  kleene_equiv t1 t2.
Proof. intros. exists k; split; assumption. Qed.

Lemma NatReach_cases : forall A, NatReach A ->
  A = styp_nat \/ (exists B C, A = styp_and B C).
Proof.
  intros A h. inversion h; subst;
    try (left; reflexivity);
    try (right; eexists; eexists; reflexivity).
Qed.

Lemma NatReach_and_component : forall A B,
  NatReach (styp_and A B) -> NatReach A \/ NatReach B.
Proof. intros. apply NatReach_and_inv; exact H. Qed.

Lemma Rel_arrow_inv : forall A B f1 f2, Rel (styp_arrow A B) f1 f2 ->
  exists v1 v2, (step star) f1 v1 /\ (step star) f2 v2 /\
                OV (styp_arrow A B) v1 v2.
Proof. intros. exact H. Qed.

Lemma Rel_and_inv : forall A B p1 p2, Rel (styp_and A B) p1 p2 ->
  exists v1 v2, (step star) p1 v1 /\ (step star) p2 v2 /\ OV (styp_and A B) v1 v2.
Proof. intros. exact H. Qed.

Lemma Rel_rcd_inv : forall l A r1 r2, Rel (styp_rcd l A) r1 r2 ->
  exists v1 v2, (step star) r1 v1 /\ (step star) r2 v2 /\ OV (styp_rcd l A) v1 v2.
Proof. intros. exact H. Qed.

(* ---------- step-indexed coherent value relation ---------- *)
Fixpoint size_styp (A:styp) : nat :=
  match A with
  | styp_top => 1
  | styp_nat => 1
  | styp_and A1 A2 => 1 + size_styp A1 + size_styp A2
  | styp_arrow A1 A2 => 1 + size_styp A1 + size_styp A2
  | styp_rcd _ A1 => 1 + size_styp A1
  end.

Fixpoint OVn (n:nat) (A:styp) (v1 v2:exp) {struct n} : Prop :=
  match n with
  | 0 => value v1 /\ value v2
  | S m =>
      (match A with
       | styp_top => v1 = trm_unit /\ v2 = trm_unit
       | styp_nat => exists k, v1 = trm_lit k /\ v2 = trm_lit k
       | styp_and A1 A2 =>
           exists a1 b1 a2 b2,
             v1 = trm_pair a1 b1 /\ v2 = trm_pair a2 b2 /\
             OVn m A1 a1 a2 /\ OVn m A2 b1 b2
       | styp_rcd l A1 =>
           exists a1 a2, v1 = trm_rcd l a1 /\ v2 = trm_rcd l a2 /\ OVn m A1 a1 a2
       | styp_arrow A1 A2 =>
           lc_exp v1 /\ lc_exp v2 /\ value v1 /\ value v2 /\
           (forall u1 u2,
              (exists x1 x2, (step star) u1 x1 /\ (step star) u2 x2 /\ OVn m A1 x1 x2) ->
              exists w1 w2, (step star) (trm_app v1 u1) w1 /\
                            (step star) (trm_app v2 u2) w2 /\ OVn m A2 w1 w2)
       end)
      /\
      (forall C c1 c2,
         size_co c1 + size_co c2 + size_styp C <= m ->
         sub A C c1 -> sub A C c2 ->
         exists r1 r2, (step star) (trm_capp c1 v1) r1 /\
                       (step star) (trm_capp c2 v2) r2 /\ OVn m C r1 r2)
  end.

Definition Reln (n:nat) (A:styp) (t1 t2:exp) : Prop :=
  exists v1 v2, (step star) t1 v1 /\ (step star) t2 v2 /\ OVn n A v1 v2.

Lemma Reln_star_l : forall n A t t' u,
  (step star) t t' -> Reln n A t' u -> Reln n A t u.
Proof.
  intros n A t t' u Ht [v1 [v2 [S1 [S2 X]]]].
  exists v1, v2. repeat split; auto.
  eapply star_trans; [exact Ht | exact S1].
Qed.

Lemma Reln_star_r : forall n A t u u',
  (step star) u u' -> Reln n A t u' -> Reln n A t u.
Proof.
  intros n A t u u' Hu [v1 [v2 [S1 [S2 X]]]].
  exists v1, v2. repeat split; auto.
  eapply star_trans; [exact Hu | exact S2].
Qed.

Lemma OVn_coher : forall m A v1 v2 C c1 c2,
  OVn (S m) A v1 v2 ->
  size_co c1 + size_co c2 + size_styp C <= m ->
  sub A C c1 -> sub A C c2 ->
  exists r1 r2, (step star) (trm_capp c1 v1) r1 /\
                (step star) (trm_capp c2 v2) r2 /\ OVn m C r1 r2.
Proof.
  intros m A v1 v2 C c1 c2 H Hb H1 H2.
  simpl in H. exact (proj2 H C c1 c2 Hb H1 H2).
Qed.

Lemma Reln_coher : forall m A t1 t2 C c1 c2,
  Reln (S m) A t1 t2 ->
  size_co c1 + size_co c2 + size_styp C <= m ->
  sub A C c1 -> sub A C c2 ->
  Reln m C (trm_capp c1 t1) (trm_capp c2 t2).
Proof.
  intros m A t1 t2 C c1 c2 [v1 [v2 [S1 [S2 X]]]] Hb H1 H2.
  destruct (OVn_coher m A v1 v2 C c1 c2 X Hb H1 H2) as [r1 [r2 [T1 [T2 Y]]]].
  exists r1, r2. repeat split; auto.
  - eapply star_trans.
    + apply star_capp; exact S1.
    + exact T1.
  - eapply star_trans.
    + apply star_capp; exact S2.
    + exact T2.
Qed.

Lemma Reln_nat_kleene : forall n t1 t2,
  Reln (S n) styp_nat t1 t2 -> kleene_equiv t1 t2.
Proof.
  intros n t1 t2 [v1 [v2 [S1 [S2 X]]]].
  simpl in X. destruct X as [[k [E1 E2]] _].
  subst v1 v2. exists k; split; assumption.
Qed.

Lemma OVn_value_l : forall n A v1 v2, OVn n A v1 v2 -> value v1.
Proof.
  intros n. induction n; intros A v1 v2 H.
  - simpl in H. exact (proj1 H).
  - destruct A; simpl in H.
    + destruct H as [[E1 E2] _]. subst; constructor.
    + destruct H as [[k [E1 E2]] _]. subst; constructor.
    + destruct H as [[a1 [b1 [a2 [b2 [E1 [E2 [X Y]]]]]]] _].
      subst. apply value_pair; [exact (IHn A1 a1 a2 X) | exact (IHn A2 b1 b2 Y)].
    + destruct H as [[lc1 [lc2 [val1 [val2 app]]]] _]. exact val1.
    + destruct H as [[a1 [a2 [E1 [E2 X]]]] _].
      subst. apply value_rcd. exact (IHn A a1 a2 X).
Qed.

Lemma OVn_value_r : forall n A v1 v2, OVn n A v1 v2 -> value v2.
Proof.
  intros n. induction n; intros A v1 v2 H.
  - simpl in H. exact (proj2 H).
  - destruct A; simpl in H.
    + destruct H as [[E1 E2] _]. subst; constructor.
    + destruct H as [[k [E1 E2]] _]. subst; constructor.
    + destruct H as [[a1 [b1 [a2 [b2 [E1 [E2 [X Y]]]]]]] _].
      subst. apply value_pair; [exact (IHn A1 a1 a2 X) | exact (IHn A2 b1 b2 Y)].
    + destruct H as [[lc1 [lc2 [val1 [val2 app]]]] _]. exact val2.
    + destruct H as [[a1 [a2 [E1 [E2 X]]]] _].
      subst. apply value_rcd. exact (IHn A a1 a2 X).
Qed.

Lemma Reln_value_l : forall n A t1 t2, Reln n A t1 t2 ->
  exists v, (step star) t1 v /\ value v.
Proof.
  intros n A t1 t2 [v1 [v2 [S1 [S2 X]]]].
  exists v1. split; [exact S1 | apply (@OVn_value_l n A v1 v2 X)].
Qed.

Lemma Reln_value_r : forall n A t1 t2, Reln n A t1 t2 ->
  exists v, (step star) t2 v /\ value v.
Proof.
  intros n A t1 t2 [v1 [v2 [S1 [S2 X]]]].
  exists v2. split; [exact S2 | apply (@OVn_value_r n A v1 v2 X)].
Qed.

Lemma Reln_of_OVn : forall n A v1 v2, OVn n A v1 v2 -> Reln n A v1 v2.
Proof.
  intros. exists v1, v2. repeat split; auto; apply star_refl.
Qed.

Lemma OVn_of_Reln_values : forall n A v1 v2,
  value v1 -> value v2 -> Reln n A v1 v2 -> OVn n A v1 v2.
Proof.
  intros n A v1 v2 Hv1 Hv2 [u1 [u2 [S1 [S2 X]]]].
  assert (u1 = v1) by (exact (@star_from_value v1 u1 Hv1 S1)).
  assert (u2 = v2) by (exact (@star_from_value v2 u2 Hv2 S2)).
  subst u1 u2. exact X.
Qed.

Lemma Reln_app : forall m A1 A2 f1 f2 g1 g2,
  Reln (S m) (styp_arrow A1 A2) f1 f2 ->
  Reln m A1 g1 g2 -> lc_exp g1 -> lc_exp g2 ->
  Reln m A2 (trm_app f1 g1) (trm_app f2 g2).
Proof.
  intros m A1 A2 f1 f2 g1 g2
    [vf1 [vf2 [Sf1 [Sf2 X]]]] [vg1 [vg2 [Sg1 [Sg2 Y]]]] Hg1lc Hg2lc.
  simpl in X. destruct X as [[lc1 [lc2 [val1 [val2 app]]]] _].
  assert (Hrel : exists x1 x2 : exp,
            (step star) g1 x1 /\ (step star) g2 x2 /\ OVn m A1 x1 x2).
  { exists vg1, vg2. repeat split; auto. }
  destruct (app g1 g2 Hrel) as [w1 [w2 [T1 [T2 Z]]]].
  exists w1, w2.
  split.
  - eapply star_trans.
    + apply star_app_l; [exact Sf1 | exact Hg1lc].
    + exact T1.
  - split.
    + eapply star_trans.
      * apply star_app_l; [exact Sf2 | exact Hg2lc].
      * exact T2.
    + exact Z.
Qed.

Lemma OVn_zero : forall A v1 v2,
  OVn 0 A v1 v2 <-> value v1 /\ value v2.
Proof. intros. split; intros H; exact H. Qed.

Lemma Reln_zero : forall A t1 t2, Reln 0 A t1 t2 ->
  (exists v1 v2, (step star) t1 v1 /\ (step star) t2 v2 /\
                 value v1 /\ value v2).
Proof.
  intros A t1 t2 [v1 [v2 [S1 [S2 X]]]].
  destruct (proj1 (@OVn_zero A v1 v2) X) as [H1 H2].
  exists v1, v2. split; [exact S1 | split; [exact S2 | split; assumption]].
Qed.

(* ---------- fuel-indexed typing with a global coercion/size bound ---------- *)
Inductive hasT : nat -> nat -> sctx -> sexp -> dirflag -> styp -> exp -> Prop :=
  | HT_top : forall k N Γ,
      uniq Γ -> size_styp styp_top <= k ->
      hasT k (S N) Γ e_top Inf styp_top trm_unit
  | HT_lit : forall k N Γ i,
      uniq Γ -> size_styp styp_nat <= k ->
      hasT k (S N) Γ (e_lit i) Inf styp_nat (trm_lit i)
  | HT_var : forall k N Γ x A,
      uniq Γ -> binds x A Γ -> size_styp A <= k ->
      hasT k (S N) Γ (e_var_f x) Inf A (trm_var_f x)
  | HT_app : forall k N Γ E1 E2 A1 A2 e1 e2,
      hasT k N Γ E1 Inf (styp_arrow A1 A2) e1 ->
      hasT k N Γ E2 Chk A1 e2 ->
      size_styp A2 <= k ->
      hasT k (S N) Γ (e_app E1 E2) Inf A2 (trm_app e1 e2)
  | HT_merge : forall k N Γ E1 E2 A1 A2 e1 e2,
      hasT k N Γ E1 Inf A1 e1 ->
      hasT k N Γ E2 Inf A2 e2 ->
      disjoint A1 A2 -> size_styp (styp_and A1 A2) <= k ->
      hasT k (S N) Γ (e_merge E1 E2) Inf (styp_and A1 A2) (trm_pair e1 e2)
  | HT_rcd : forall k N Γ l E A e,
      hasT k N Γ E Inf A e -> size_styp (styp_rcd l A) <= k ->
      hasT k (S N) Γ (e_rcd l E) Inf (styp_rcd l A) (trm_rcd l e)
  | HT_proj : forall k N Γ E l A e,
      hasT k N Γ E Inf (styp_rcd l A) e -> size_styp A <= k ->
      hasT k (S N) Γ (e_proj E l) Inf A (trm_proj e l)
  | HT_anno : forall k N Γ E A e,
      hasT k N Γ E Chk A e -> size_styp A <= k ->
      hasT k (S N) Γ (e_anno E A) Inf A e
  | HT_abs : forall k N L Γ E A B e,
      (forall x, x \notin L -> hasT k N ((x~A)++Γ) (open_sexp_wrt_sexp E (e_var_f x))
                              Chk B (open_exp_wrt_exp e (trm_var_f x))) ->
      size_styp (styp_arrow A B) <= k ->
      hasT k (S N) Γ (e_abs E) Chk (styp_arrow A B) (trm_abs e)
  | HT_sub : forall k N Γ E A B c e,
      hasT k N Γ E Inf B e -> sub B A c ->
      size_co c <= k -> size_styp A <= k ->
      hasT k (S N) Γ E Chk A (trm_capp c e).

Lemma hasT_to_has_type : forall k N Γ E dir A e,
  hasT k N Γ E dir A e -> has_type Γ E dir A e.
Proof.
  intros k N Γ E dir A e H. induction H.
  - apply T_top; assumption.
  - apply T_lit; assumption.
  - eapply T_var; eassumption.
  - eapply T_app; eassumption.
  - eapply T_merge; eassumption.
  - eapply T_rcd; eassumption.
  - eapply T_proj; eassumption.
  - eapply T_anno; eassumption.
  - apply (@T_abs L Γ E0 A B e). exact H0.
  - eapply T_sub; eassumption.
Qed.

Lemma hasT_k_mono : forall k k' N Γ E dir A e,
  hasT k N Γ E dir A e -> k <= k' -> hasT k' N Γ E dir A e.
Proof.
  intros k k' N Γ E dir A e H. induction H; intros Hle.
  - eapply HT_top; [exact H | lia].
  - eapply HT_lit; [exact H | lia].
  - eapply HT_var; [exact H | exact H0 | lia].
  - eapply HT_app; [apply IHhasT1; exact Hle | apply IHhasT2; exact Hle | lia].
  - eapply HT_merge; [apply IHhasT1; exact Hle | apply IHhasT2; exact Hle | exact H1 | lia].
  - eapply HT_rcd; [apply IHhasT; exact Hle | lia].
  - eapply HT_proj; [apply IHhasT; exact Hle | lia].
  - eapply HT_anno; [apply IHhasT; exact Hle | lia].
  - eapply HT_abs.
    + intros x Hx. apply H0; [exact Hx | exact Hle].
    + lia.
  - eapply HT_sub; [apply IHhasT; exact Hle | exact H0 | lia | lia].
Qed.

Lemma hasT_N_mono : forall k N Γ E dir A e,
  hasT k N Γ E dir A e -> forall N', N <= N' -> hasT k N' Γ E dir A e.
Proof.
  intros k N Γ E dir A e H. induction H; intros N' Hle.
  - destruct N' as [|N'']; [inversion Hle |].
    eapply HT_top; [exact H | lia].
  - destruct N' as [|N'']; [inversion Hle |].
    eapply HT_lit; [exact H | lia].
  - destruct N' as [|N'']; [inversion Hle |].
    eapply HT_var; [exact H | exact H0 | lia].
  - destruct N' as [|N'']; [inversion Hle |].
    eapply HT_app; [apply IHhasT1; lia | apply IHhasT2; lia | lia].
  - destruct N' as [|N'']; [inversion Hle |].
    eapply HT_merge; [apply IHhasT1; lia | apply IHhasT2; lia | exact H1 | lia].
  - destruct N' as [|N'']; [inversion Hle |].
    eapply HT_rcd; [apply IHhasT; lia | lia].
  - destruct N' as [|N'']; [inversion Hle |].
    eapply HT_proj; [apply IHhasT; lia | lia].
  - destruct N' as [|N'']; [inversion Hle |].
    eapply HT_anno; [apply IHhasT; lia | lia].
  - destruct N' as [|N'']; [inversion Hle |].
    eapply HT_abs.
    + intros x Hx. apply H0; [exact Hx | lia].
    + lia.
  - destruct N' as [|N'']; [inversion Hle |].
    eapply HT_sub; [apply IHhasT; lia | exact H0 | lia | lia].
Qed.

(* ---------- atom swapping on source and target syntax ---------- *)
Definition swap_atom (a b x:atom) : atom :=
  if x == a then b else if x == b then a else x.

Fixpoint swap_exp (a b:atom) (e:exp) : exp :=
  match e with
  | trm_var_b n => trm_var_b n
  | trm_var_f x => trm_var_f (swap_atom a b x)
  | trm_unit => trm_unit
  | trm_lit i => trm_lit i
  | trm_abs e' => trm_abs (swap_exp a b e')
  | trm_app e1 e2 => trm_app (swap_exp a b e1) (swap_exp a b e2)
  | trm_pair e1 e2 => trm_pair (swap_exp a b e1) (swap_exp a b e2)
  | trm_rcd l e' => trm_rcd l (swap_exp a b e')
  | trm_proj e' l => trm_proj (swap_exp a b e') l
  | trm_capp c e' => trm_capp c (swap_exp a b e')
  end.

Fixpoint swap_sexp (a b:atom) (ee:sexp) : sexp :=
  match ee with
  | e_var_b n => e_var_b n
  | e_var_f x => e_var_f (swap_atom a b x)
  | e_top => e_top
  | e_lit i => e_lit i
  | e_abs ee' => e_abs (swap_sexp a b ee')
  | e_app ee1 ee2 => e_app (swap_sexp a b ee1) (swap_sexp a b ee2)
  | e_merge ee1 ee2 => e_merge (swap_sexp a b ee1) (swap_sexp a b ee2)
  | e_anno ee' A => e_anno (swap_sexp a b ee') A
  | e_rcd l ee' => e_rcd l (swap_sexp a b ee')
  | e_proj ee' l => e_proj (swap_sexp a b ee') l
  end.

Fixpoint swap_sctx (a b:atom) (Γ:sctx) : sctx :=
  match Γ with
  | nil => nil
  | cons p rest => cons (swap_atom a b (fst p), snd p) (swap_sctx a b rest)
  end.

Lemma swap_exp_size : forall a b e, size_exp (swap_exp a b e) = size_exp e.
Proof.
  intros a b e. induction e; simpl; auto;
    try (rewrite IHe; reflexivity);
    try (rewrite IHe1, IHe2; reflexivity).
Qed.

Lemma swap_atom_a : forall a b, swap_atom a b a = b.
Proof.
  intros. unfold swap_atom.
  destruct (a == a) as [H|H]; [reflexivity | exfalso; apply H; reflexivity].
Qed.

Lemma swap_atom_b : forall a b, swap_atom a b b = a.
Proof.
  intros. unfold swap_atom.
  destruct (b == a) as [H|H].
  - destruct (b == b) as [H2|H2]; [exact H | exfalso; apply H2; reflexivity].
  - destruct (b == b) as [H2|H2]; [reflexivity | exfalso; apply H2; reflexivity].
Qed.

Lemma swap_atom_other : forall a b x, x <> a -> x <> b -> swap_atom a b x = x.
Proof.
  intros a b x Hxa Hxb. unfold swap_atom.
  destruct (x == a) as [H|H]; [exfalso; apply Hxa; exact H |].
  destruct (x == b) as [H2|H2]; [exfalso; apply Hxb; exact H2 | reflexivity].
Qed.

Lemma swap_atom_involutive : forall a b x, swap_atom a b (swap_atom a b x) = x.
Proof.
  intros a b x.
  destruct (x == a) as [Hxa|Hxa].
  - subst x. rewrite swap_atom_a. rewrite swap_atom_b. reflexivity.
  - destruct (x == b) as [Hxb|Hxb].
    + subst x. rewrite swap_atom_b. rewrite swap_atom_a. reflexivity.
    + rewrite (swap_atom_other a b x Hxa Hxb).
      rewrite (swap_atom_other a b x Hxa Hxb). reflexivity.
Qed.

Lemma swap_exp_open_rec : forall a b e k u,
  swap_exp a b (open_exp_wrt_exp_rec k u e) =
  open_exp_wrt_exp_rec k (swap_exp a b u) (swap_exp a b e).
Proof.
  intros a b e. induction e; intros k u; simpl; auto.
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; reflexivity.
  - rewrite IHe. reflexivity.
  - rewrite IHe1, IHe2. reflexivity.
  - rewrite IHe1, IHe2. reflexivity.
  - rewrite IHe. reflexivity.
  - rewrite IHe. reflexivity.
  - rewrite IHe. reflexivity.
Qed.

Lemma swap_sexp_open_rec : forall a b ee k u,
  swap_sexp a b (open_sexp_wrt_sexp_rec k u ee) =
  open_sexp_wrt_sexp_rec k (swap_sexp a b u) (swap_sexp a b ee).
Proof.
  intros a b ee. induction ee; intros k u; simpl; auto.
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; reflexivity.
  - rewrite IHee. reflexivity.
  - rewrite IHee1, IHee2. reflexivity.
  - rewrite IHee1, IHee2. reflexivity.
  - rewrite IHee. reflexivity.
  - rewrite IHee. reflexivity.
  - rewrite IHee. reflexivity.
Qed.

Lemma swap_atom_injective : forall a b x y,
  swap_atom a b x = swap_atom a b y -> x = y.
Proof.
  intros a b x y H.
  rewrite <- (swap_atom_involutive a b x).
  rewrite <- (swap_atom_involutive a b y).
  f_equal. exact H.
Qed.

Lemma binds_swap_sctx : forall a b Γ x A,
  binds (swap_atom a b x) A (swap_sctx a b Γ) <-> binds x A Γ.
Proof.
  intros a b Γ. induction Γ as [| [y B] rest IH]; intros x A; simpl.
  - split; intros H; inversion H.
  - rewrite !binds_cons_iff. split.
    + intros [[Hxy HAB]|Htail].
      * left. split; [exact (@swap_atom_injective a b x y Hxy) | exact HAB].
      * right. apply (proj1 (IH x A)); exact Htail.
    + intros [[Hxy HAB]|Htail].
      * left. split; [f_equal; exact Hxy | exact HAB].
      * right. apply (proj2 (IH x A)); exact Htail.
Qed.

Lemma in_dom_swap_sctx : forall a b Γ x,
  x \in dom (swap_sctx a b Γ) <-> swap_atom a b x \in dom Γ.
Proof.
  intros a b Γ x. split.
  - intros Hx. apply binds_In_inv in Hx. destruct Hx as [A HA].
    apply (@binds_In _ (swap_atom a b x) A Γ).
    apply (proj1 (@binds_swap_sctx a b Γ (swap_atom a b x) A)).
    rewrite swap_atom_involutive. exact HA.
  - intros Hx. apply binds_In_inv in Hx. destruct Hx as [A HA].
    apply (@binds_In _ x A (swap_sctx a b Γ)).
    pose proof (proj2 (@binds_swap_sctx a b Γ (swap_atom a b x) A) HA) as H.
    rewrite swap_atom_involutive in H. exact H.
Qed.

Lemma uniq_swap_sctx : forall a b Γ, uniq Γ -> uniq (swap_sctx a b Γ).
Proof.
  intros a b Γ. induction Γ as [| [y B] rest IH]; intros Hu; simpl.
  - apply uniq_nil.
  - apply uniq_cons_3.
    + apply IH. apply (@uniq_cons_1 _ y B rest). exact Hu.
    + intros Hin. apply (@uniq_cons_2 _ y B rest Hu).
      pose proof (proj1 (@in_dom_swap_sctx a b rest (swap_atom a b y)) Hin) as H.
      rewrite swap_atom_involutive in H. exact H.
Qed.

Lemma swap_sctx_cons : forall a b y A Γ,
  swap_sctx a b ((y~A)++Γ) = ((swap_atom a b y)~A) ++ swap_sctx a b Γ.
Proof. intros. reflexivity. Qed.

Lemma swap_exp_open : forall a b e x,
  swap_exp a b (open_exp_wrt_exp e (trm_var_f x)) =
  open_exp_wrt_exp (swap_exp a b e) (trm_var_f (swap_atom a b x)).
Proof.
  intros. unfold open_exp_wrt_exp.
  rewrite swap_exp_open_rec. reflexivity.
Qed.

Lemma swap_sexp_open : forall a b ee x,
  swap_sexp a b (open_sexp_wrt_sexp ee (e_var_f x)) =
  open_sexp_wrt_sexp (swap_sexp a b ee) (e_var_f (swap_atom a b x)).
Proof.
  intros. unfold open_sexp_wrt_sexp.
  rewrite swap_sexp_open_rec. reflexivity.
Qed.

Lemma hasT_swap : forall a b k N Γ E dir A e,
  hasT k N Γ E dir A e ->
  hasT k N (swap_sctx a b Γ) (swap_sexp a b E) dir A (swap_exp a b e).
Proof.
  intros a b k N Γ E dir A e H. induction H.
  - eapply HT_top; [apply uniq_swap_sctx; exact H | lia].
  - eapply HT_lit; [apply uniq_swap_sctx; exact H | lia].
  - eapply HT_var.
    + apply uniq_swap_sctx. exact H.
    + apply (proj2 (@binds_swap_sctx a b Γ x A)). exact H0.
    + lia.
  - eapply HT_app; [exact IHhasT1 | exact IHhasT2 | lia].
  - eapply HT_merge; [exact IHhasT1 | exact IHhasT2 | exact H1 | lia].
  - eapply HT_rcd; [exact IHhasT | lia].
  - eapply HT_proj; [exact IHhasT | lia].
  - eapply HT_anno; [exact IHhasT | lia].
  - eapply HT_abs with (L := L \u {{a}} \u {{b}}).
    + intros x Hx.
      assert (HxL : x \notin L) by (intro Hc; apply Hx; fsetdec).
      assert (Hxa : x <> a) by (intro Hc; subst x; apply Hx; fsetdec).
      assert (Hxb : x <> b) by (intro Hc; subst x; apply Hx; fsetdec).
      pose proof (H0 x HxL) as Hb.
      rewrite (@swap_sctx_cons a b x A Γ) in Hb.
      rewrite (swap_atom_other a b x Hxa Hxb) in Hb.
      rewrite (@swap_sexp_open a b E0 x) in Hb.
      rewrite (swap_atom_other a b x Hxa Hxb) in Hb.
      rewrite (@swap_exp_open a b e x) in Hb.
      rewrite (swap_atom_other a b x Hxa Hxb) in Hb.
      exact Hb.
    + lia.
  - eapply HT_sub; [exact IHhasT | exact H0 | lia | lia].
Qed.

Fixpoint fv_sexp (ee:sexp) : atoms :=
  match ee with
  | e_var_b _ => empty
  | e_var_f x => {{x}}
  | e_top => empty
  | e_lit _ => empty
  | e_abs ee' => fv_sexp ee'
  | e_app ee1 ee2 => fv_sexp ee1 \u fv_sexp ee2
  | e_merge ee1 ee2 => fv_sexp ee1 \u fv_sexp ee2
  | e_anno ee' _ => fv_sexp ee'
  | e_rcd _ ee' => fv_sexp ee'
  | e_proj ee' _ => fv_sexp ee'
  end.

Lemma swap_sexp_id : forall x y ee,
  x \notin fv_sexp ee -> y \notin fv_sexp ee -> swap_sexp x y ee = ee.
Proof.
  intros x y ee. induction ee; intros Hx Hy; simpl in *; auto.
  - f_equal. apply swap_atom_other; fsetdec.
  - rewrite IHee; auto.
  - rewrite IHee1, IHee2; fsetdec.
  - rewrite IHee1, IHee2; fsetdec.
  - rewrite IHee; auto.
  - rewrite IHee; auto.
  - rewrite IHee; auto.
Qed.

Lemma swap_exp_id : forall x y e,
  x \notin fv_exp e -> y \notin fv_exp e -> swap_exp x y e = e.
Proof.
  intros x y e. induction e; intros Hx Hy; simpl in *; auto.
  - f_equal. apply swap_atom_other; fsetdec.
  - rewrite IHe; auto.
  - rewrite IHe1, IHe2; fsetdec.
  - rewrite IHe1, IHe2; fsetdec.
  - rewrite IHe; auto.
  - rewrite IHe; auto.
  - rewrite IHe; auto.
Qed.

Lemma swap_sctx_id : forall x y Γ,
  x \notin dom Γ -> y \notin dom Γ -> swap_sctx x y Γ = Γ.
Proof.
  intros x y Γ. induction Γ as [| [z A] rest IH]; intros Hx Hy; simpl in *.
  - reflexivity.
  - assert (Hzx : z <> x) by (intro E; subst; apply Hx; simpl; fsetdec).
    assert (Hzy : z <> y) by (intro E; subst; apply Hy; simpl; fsetdec).
    assert (Hxr : x \notin dom rest) by fsetdec.
    assert (Hyr : y \notin dom rest) by fsetdec.
    rewrite (swap_atom_other x y z Hzx Hzy).
    rewrite IH; auto.
Qed.

Lemma hasT_raise : forall k k' N N' Γ E dir A e,
  hasT k N Γ E dir A e -> k <= k' -> N <= N' ->
  hasT k' N' Γ E dir A e.
Proof.
  intros k k' N N' Γ E dir A e H Hk HN.
  exact (@hasT_N_mono k' N Γ E dir A e
           (@hasT_k_mono k k' N Γ E dir A e H Hk) N' HN).
Qed.

Lemma has_type_to_hasT : forall Γ E dir A e,
  has_type Γ E dir A e -> exists k N, hasT k N Γ E dir A e.
Proof.
  intros Γ E dir A e H. induction H.
  - exists (size_styp styp_top), 1. apply HT_top; [exact H | lia].
  - exists (size_styp styp_nat), 1. apply HT_lit; [exact H | lia].
  - exists (size_styp A), 1. eapply HT_var; [exact H | exact H0 | lia].
  - (* T_app *)
    destruct IHhas_type1 as [k1 [N1 W1]].
    destruct IHhas_type2 as [k2 [N2 W2]].
    pose (k := Nat.max k1 (Nat.max k2 (size_styp A2))).
    pose (N := Nat.max N1 N2).
    exists k, (S N).
    eapply HT_app.
    + apply hasT_raise with (k:=k1) (N:=N1); [exact W1 | subst k; lia | subst N; lia].
    + apply hasT_raise with (k:=k2) (N:=N2); [exact W2 | subst k; lia | subst N; lia].
    + subst k; lia.
  - (* T_merge *)
    destruct IHhas_type1 as [k1 [N1 W1]].
    destruct IHhas_type2 as [k2 [N2 W2]].
    pose (k := Nat.max k1 (Nat.max k2 (size_styp (styp_and A1 A2)))).
    pose (N := Nat.max N1 N2).
    exists k, (S N).
    eapply HT_merge.
    + apply hasT_raise with (k:=k1) (N:=N1); [exact W1 | subst k; lia | subst N; lia].
    + apply hasT_raise with (k:=k2) (N:=N2); [exact W2 | subst k; lia | subst N; lia].
    + exact H1.
    + subst k; lia.
  - (* T_rcd *)
    destruct IHhas_type as [k0 [N0 W0]].
    pose (k := Nat.max k0 (size_styp (styp_rcd l A))).
    exists k, (S N0).
    eapply HT_rcd.
    + apply hasT_raise with (k:=k0) (N:=N0); [exact W0 | subst k; lia | lia].
    + subst k; lia.
  - (* T_proj *)
    destruct IHhas_type as [k0 [N0 W0]].
    pose (k := Nat.max k0 (size_styp A)).
    exists k, (S N0).
    eapply HT_proj.
    + apply hasT_raise with (k:=k0) (N:=N0); [exact W0 | subst k; lia | lia].
    + subst k; lia.
  - (* T_anno *)
    destruct IHhas_type as [k0 [N0 W0]].
    pose (k := Nat.max k0 (size_styp A)).
    exists k, (S N0).
    eapply HT_anno.
    + apply hasT_raise with (k:=k0) (N:=N0); [exact W0 | subst k; lia | lia].
    + subst k; lia.
  - (* T_abs *)
    pose (SS := L \u dom GG \u fv_sexp ee \u fv_exp e).
    destruct (atom_fresh SS) as [x0 Hx0].
    assert (Hx0L : x0 \notin L) by (intro Hc; apply Hx0; subst SS; fsetdec).
    destruct (H0 x0 Hx0L) as [k0 [N0 Hbody0]].
    pose (k := Nat.max k0 (size_styp (styp_arrow A B))).
    exists k, (S N0).
    eapply HT_abs with (L := SS \u {{x0}}).
    + intros x Hx.
      assert (HxL : x \notin L) by (intro Hc; apply Hx; fsetdec).
      assert (Hxd : x \notin dom GG) by (intro Hc; apply Hx; fsetdec).
      assert (HxE : x \notin fv_sexp ee) by (intro Hc; apply Hx; fsetdec).
      assert (Hxe : x \notin fv_exp e) by (intro Hc; apply Hx; fsetdec).
      assert (Hxx0 : x <> x0) by (intro Hc; subst x; apply Hx; fsetdec).
      assert (Hx0d : x0 \notin dom GG) by (intro Hc; apply Hx0; subst SS; fsetdec).
      assert (Hx0E : x0 \notin fv_sexp ee) by (intro Hc; apply Hx0; subst SS; fsetdec).
      assert (Hx0e : x0 \notin fv_exp e) by (intro Hc; apply Hx0; subst SS; fsetdec).
      pose proof (@hasT_swap x0 x k0 N0 ((x0~A)++GG)
                    (open_sexp_wrt_sexp ee (e_var_f x0)) Chk B
                    (open_exp_wrt_exp e (trm_var_f x0)) Hbody0) as Hs.
      rewrite (@swap_sctx_cons x0 x x0 A GG) in Hs.
      rewrite swap_atom_a in Hs.
      rewrite (@swap_sctx_id x0 x GG Hx0d Hxd) in Hs.
      rewrite (@swap_sexp_open x0 x ee x0) in Hs.
      rewrite swap_atom_a in Hs.
      rewrite (@swap_sexp_id x0 x ee Hx0E HxE) in Hs.
      rewrite (@swap_exp_open x0 x e x0) in Hs.
      rewrite swap_atom_a in Hs.
      rewrite (@swap_exp_id x0 x e Hx0e Hxe) in Hs.
      apply hasT_raise with (k:=k0) (N:=N0); [exact Hs | subst k; lia | lia].
    + subst k; lia.
  - (* T_sub *)
    destruct IHhas_type as [k0 [N0 W0]].
    pose (k := Nat.max k0 (Nat.max (size_co c) (size_styp A))).
    exists k, (S N0).
    eapply HT_sub.
    + apply hasT_raise with (k:=k0) (N:=N0); [exact W0 | subst k; lia | lia].
    + exact H0.
    + subst k; lia.
    + subst k; lia.
Qed.

Lemma swap_exp_swap : forall a b e, swap_exp a b (swap_exp a b e) = e.
Proof.
  intros a b e. induction e; simpl; auto.
  - rewrite swap_atom_involutive. reflexivity.
  - rewrite IHe. reflexivity.
  - rewrite IHe1, IHe2. reflexivity.
  - rewrite IHe1, IHe2. reflexivity.
  - rewrite IHe. reflexivity.
  - rewrite IHe. reflexivity.
  - rewrite IHe. reflexivity.
Qed.

Lemma swap_sexp_swap : forall a b ee, swap_sexp a b (swap_sexp a b ee) = ee.
Proof.
  intros a b ee. induction ee; simpl; auto.
  - rewrite swap_atom_involutive. reflexivity.
  - rewrite IHee. reflexivity.
  - rewrite IHee1, IHee2. reflexivity.
  - rewrite IHee1, IHee2. reflexivity.
  - rewrite IHee. reflexivity.
  - rewrite IHee. reflexivity.
  - rewrite IHee. reflexivity.
Qed.

Lemma swap_sctx_swap : forall a b Γ, swap_sctx a b (swap_sctx a b Γ) = Γ.
Proof.
  intros a b Γ. induction Γ as [| [y A] rest IH]; simpl.
  - reflexivity.
  - rewrite swap_atom_involutive. rewrite IH. reflexivity.
Qed.

Lemma hasT_fuel_pos : forall k N Γ E dir A e,
  hasT k N Γ E dir A e -> N >= 1.
Proof. intros k N Γ E dir A e H. induction H; lia. Qed.

Lemma hasT_type_bound : forall k N Γ E dir A e,
  hasT k N Γ E dir A e -> size_styp A <= k.
Proof. intros k N Γ E dir A e H. induction H; eauto. Qed.

Lemma hasT_swap_invol : forall a b k N Γ E dir A e,
  hasT k N (swap_sctx a b Γ) (swap_sexp a b E) dir A (swap_exp a b e) ->
  hasT k N Γ E dir A e.
Proof.
  intros a b k N Γ E dir A e H.
  pose proof (@hasT_swap a b k N (swap_sctx a b Γ) (swap_sexp a b E)
                dir A (swap_exp a b e) H) as H2.
  rewrite swap_sctx_swap in H2.
  rewrite swap_sexp_swap in H2.
  rewrite swap_exp_swap in H2.
  exact H2.
Qed.

(* ---------- provenance-indexed pair relation over typing derivations ---------- *)
Inductive K : sctx -> sexp -> dirflag -> styp -> exp -> exp -> Prop :=
  | K_top : forall Γ, uniq Γ -> K Γ e_top Inf styp_top trm_unit trm_unit
  | K_lit : forall Γ i, uniq Γ -> K Γ (e_lit i) Inf styp_nat (trm_lit i) (trm_lit i)
  | K_var : forall Γ x A, uniq Γ -> binds x A Γ ->
      K Γ (e_var_f x) Inf A (trm_var_f x) (trm_var_f x)
  | K_app : forall Γ E1 E2 A1 A2 f1 f2 g1 g2,
      K Γ E1 Inf (styp_arrow A1 A2) f1 f2 ->
      K Γ E2 Chk A1 g1 g2 ->
      K Γ (e_app E1 E2) Inf A2 (trm_app f1 g1) (trm_app f2 g2)
  | K_merge : forall Γ E1 E2 A1 A2 a1 b1 a2 b2,
      K Γ E1 Inf A1 a1 a2 -> K Γ E2 Inf A2 b1 b2 ->
      disjoint A1 A2 ->
      K Γ (e_merge E1 E2) Inf (styp_and A1 A2)
        (trm_pair a1 b1) (trm_pair a2 b2)
  | K_rcd : forall Γ l E A e1 e2,
      K Γ E Inf A e1 e2 ->
      K Γ (e_rcd l E) Inf (styp_rcd l A) (trm_rcd l e1) (trm_rcd l e2)
  | K_proj : forall Γ E l A e1 e2,
      K Γ E Inf (styp_rcd l A) e1 e2 ->
      K Γ (e_proj E l) Inf A (trm_proj e1 l) (trm_proj e2 l)
  | K_anno : forall Γ E A e1 e2,
      K Γ E Chk A e1 e2 ->
      K Γ (e_anno E A) Inf A e1 e2
  | K_abs : forall L Γ E A B e1 e2,
      (forall x, x \notin L ->
         K ((x~A)++Γ) (open_sexp_wrt_sexp E (e_var_f x)) Chk B
           (open_exp_wrt_exp e1 (trm_var_f x))
           (open_exp_wrt_exp e2 (trm_var_f x))) ->
      K Γ (e_abs E) Chk (styp_arrow A B) (trm_abs e1) (trm_abs e2)
  | K_sub : forall Γ E A B c1 c2 e1 e2,
      K Γ E Inf B e1 e2 -> sub B A c1 -> sub B A c2 ->
      K Γ E Chk A (trm_capp c1 e1) (trm_capp c2 e2).

Lemma K_sound_l : forall Γ E dir A e1 e2,
  K Γ E dir A e1 e2 -> has_type Γ E dir A e1.
Proof.
  intros Γ E dir A e1 e2 H. induction H.
  - apply T_top; exact H.
  - apply T_lit; exact H.
  - eapply T_var; eassumption.
  - eapply T_app; eassumption.
  - eapply T_merge; eassumption.
  - eapply T_rcd; eassumption.
  - eapply T_proj; eassumption.
  - eapply T_anno; eassumption.
  - apply (@T_abs L Γ E0 A B _). exact H0.
  - eapply T_sub; eassumption.
Qed.

Lemma K_sound_r : forall Γ E dir A e1 e2,
  K Γ E dir A e1 e2 -> has_type Γ E dir A e2.
Proof.
  intros Γ E dir A e1 e2 H. induction H.
  - apply T_top; exact H.
  - apply T_lit; exact H.
  - eapply T_var; eassumption.
  - eapply T_app; eassumption.
  - eapply T_merge; eassumption.
  - eapply T_rcd; eassumption.
  - eapply T_proj; eassumption.
  - eapply T_anno; eassumption.
  - apply (@T_abs L Γ E0 A B _). exact H0.
  - eapply T_sub; eassumption.
Qed.

Lemma K_complete : forall Γ E dir A e1 e2,
  has_type Γ E dir A e1 -> has_type Γ E dir A e2 -> K Γ E dir A e1 e2.
Proof.
  intros Γ E dir A e1 e2 H1. revert e2. induction H1; intros ex H2;
    inversion H2; subst.
  - apply K_top. exact H.
  - apply K_lit. exact H.
  - eapply K_var; eassumption.
  - (* T_app *)
    assert (HA : styp_arrow A1 A2 = styp_arrow A3 A2) by
      (exact (@Inf_typ_unique ee1 GG (styp_arrow A1 A2) e1 H1_
                (styp_arrow A3 A2) e0 H3)).
    injection HA as HA1. subst A3.
    specialize (IHhas_type1 e0 H3).
    specialize (IHhas_type2 e3 H4).
    eapply K_app; eassumption.
  - (* T_merge *)
    specialize (IHhas_type1 e0 H6).
    specialize (IHhas_type2 e3 H7).
    eapply K_merge; [exact IHhas_type1 | exact IHhas_type2 | exact H].
  - (* T_rcd *)
    specialize (IHhas_type e0 H5).
    eapply K_rcd; exact IHhas_type.
  - (* T_proj *)
    specialize (IHhas_type _ H3).
    eapply K_proj; eassumption.
  - (* T_anno *)
    specialize (IHhas_type ex H3).
    eapply K_anno; exact IHhas_type.
  - (* T_abs *)
    eapply K_abs with (L := L \u L0).
    + intros x Hx.
      assert (HxL : x \notin L) by (intro Hc; apply Hx; fsetdec).
      assert (HxL0 : x \notin L0) by (intro Hc; apply Hx; fsetdec).
      exact (H0 x HxL (open_exp_wrt_exp e0 (trm_var_f x)) (H6 x HxL0)).
  - (* T_sub *)
    inversion H1.
  - inversion H1.
  - assert (HB : B = B0) by
      (exact (@Inf_typ_unique ee GG B e H1 B0 e0 H0)).
    subst B0.
    specialize (IHhas_type e0 H0).
    eapply K_sub; [exact IHhas_type | exact H | exact H3].
Qed.

Lemma K_sound : forall Γ E dir A e1 e2,
  K Γ E dir A e1 e2 -> has_type Γ E dir A e1 /\ has_type Γ E dir A e2.
Proof.
  intros Γ E dir A e1 e2 H. split.
  - exact (@K_sound_l Γ E dir A e1 e2 H).
  - exact (@K_sound_r Γ E dir A e1 e2 H).
Qed.

Lemma K_self : forall Γ E dir A e,
  has_type Γ E dir A e -> K Γ E dir A e e.
Proof. intros. apply K_complete; exact H. Qed.

(* ---------- closure of K under the closing-context term operations ---------- *)
Inductive KC : sctx -> dirflag -> styp -> exp -> exp -> Prop :=
  | KC_K : forall Γ E dir A e1 e2,
      K Γ E dir A e1 e2 -> KC Γ dir A e1 e2
  | KC_appL : forall Γ A1 A2 t1 t2 ee e,
      KC Γ Inf (styp_arrow A1 A2) t1 t2 ->
      has_type Γ ee Chk A1 e ->
      KC Γ Inf A2 (trm_app t1 e) (trm_app t2 e)
  | KC_appR : forall Γ A1 A2 t1 t2 ee f,
      has_type Γ ee Inf (styp_arrow A1 A2) f ->
      KC Γ Chk A1 t1 t2 ->
      KC Γ Inf A2 (trm_app f t1) (trm_app f t2)
  | KC_mergeL : forall Γ A1 A2 t1 t2 ee e,
      KC Γ Inf A1 t1 t2 ->
      has_type Γ ee Inf A2 e ->
      disjoint A1 A2 ->
      KC Γ Inf (styp_and A1 A2) (trm_pair t1 e) (trm_pair t2 e)
  | KC_mergeR : forall Γ A1 A2 t1 t2 ee e,
      has_type Γ ee Inf A1 e ->
      KC Γ Inf A2 t1 t2 ->
      disjoint A1 A2 ->
      KC Γ Inf (styp_and A1 A2) (trm_pair e t1) (trm_pair e t2)
  | KC_rcd : forall Γ l B t1 t2,
      KC Γ Inf B t1 t2 ->
      KC Γ Inf (styp_rcd l B) (trm_rcd l t1) (trm_rcd l t2)
  | KC_proj : forall Γ l B t1 t2,
      KC Γ Inf (styp_rcd l B) t1 t2 ->
      KC Γ Inf B (trm_proj t1 l) (trm_proj t2 l)
  | KC_anno : forall Γ A t1 t2,
      KC Γ Chk A t1 t2 ->
      KC Γ Inf A t1 t2
  | KC_lam : forall x Γ A B t1 t2,
      x \notin dom Γ ->
      KC ((x~A)++Γ) Chk B t1 t2 ->
      KC Γ Chk (styp_arrow A B)
        (trm_abs (close_exp_wrt_exp x t1))
        (trm_abs (close_exp_wrt_exp x t2)).

Lemma CTyp_to_KC : forall C Γ d A Γ' d' A' c,
  CTyp C Γ d A Γ' d' A' c ->
  forall E0 e1 e2, K Γ E0 d A e1 e2 ->
    KC Γ' d' A' (appctx c e1) (appctx c e2).
Proof.
  intros C Γ d A Γ' d' A' c H. induction H; intros E0 e1 e2 HK.
  - (* empty1 *) simpl. eapply KC_K with (E:=E0). exact HK.
  - (* empty2 *) simpl. eapply KC_K with (E:=E0). exact HK.
  - (* appL1 *) simpl. eapply KC_appL; [apply (IHCTyp E0 e1 e2 HK) | exact H0].
  - (* appL2 *) simpl. eapply KC_appL; [apply (IHCTyp E0 e1 e2 HK) | exact H0].
  - (* appR1 *) simpl. eapply KC_appR; [exact H | apply (IHCTyp E0 e1 e2 HK)].
  - (* appR2 *) simpl. eapply KC_appR; [exact H | apply (IHCTyp E0 e1 e2 HK)].
  - (* mergeL1 *) simpl. eapply KC_mergeL; [apply (IHCTyp E0 e1 e2 HK) | exact H0 | exact H1].
  - (* mergeL2 *) simpl. eapply KC_mergeL; [apply (IHCTyp E0 e1 e2 HK) | exact H0 | exact H1].
  - (* mergeR1 *) simpl. eapply KC_mergeR; [exact H | apply (IHCTyp E0 e1 e2 HK) | exact H1].
  - (* mergeR2 *) simpl. eapply KC_mergeR; [exact H | apply (IHCTyp E0 e1 e2 HK) | exact H1].
  - (* rcd1 *) simpl. apply KC_rcd. apply (IHCTyp E0 e1 e2 HK).
  - (* rcd2 *) simpl. apply KC_rcd. apply (IHCTyp E0 e1 e2 HK).
  - (* proj1 *) simpl. apply KC_proj. apply (IHCTyp E0 e1 e2 HK).
  - (* proj2 *) simpl. apply KC_proj. apply (IHCTyp E0 e1 e2 HK).
  - (* anno1 *) simpl. apply KC_anno. apply (IHCTyp E0 e1 e2 HK).
  - (* anno2 *) simpl. apply KC_anno. apply (IHCTyp E0 e1 e2 HK).
  - (* abs1 *) simpl. eapply KC_lam; [exact H0 | apply (IHCTyp E0 e1 e2 HK)].
  - (* abs2 *) simpl. eapply KC_lam; [exact H0 | apply (IHCTyp E0 e1 e2 HK)].
Qed.

Definition Typed (Γ:sctx) (dir:dirflag) (A:styp) (e:exp) : Prop :=
  exists E, has_type Γ E dir A e.

Lemma K_typed_l : forall Γ E dir A e1 e2,
  K Γ E dir A e1 e2 -> Typed Γ dir A e1.
Proof. intros. exists E0. exact (@K_sound_l Γ E0 dir A e1 e2 H). Qed.

Lemma K_typed_r : forall Γ E dir A e1 e2,
  K Γ E dir A e1 e2 -> Typed Γ dir A e2.
Proof. intros. exists E0. exact (@K_sound_r Γ E0 dir A e1 e2 H). Qed.

Lemma K_typed_both : forall Γ E dir A e1 e2,
  K Γ E dir A e1 e2 -> Typed Γ dir A e1 /\ Typed Γ dir A e2.
Proof.
  intros. split.
  - exists E0. exact (@K_sound_l Γ E0 dir A e1 e2 H).
  - exists E0. exact (@K_sound_r Γ E0 dir A e1 e2 H).
Qed.

Lemma size_styp_and_l : forall A B, size_styp A < size_styp (styp_and A B).
Proof. intros. simpl. lia. Qed.

Lemma size_styp_and_r : forall A B, size_styp B < size_styp (styp_and A B).
Proof. intros. simpl. lia. Qed.

Lemma size_styp_rcd_lt : forall l A, size_styp A < size_styp (styp_rcd l A).
Proof. intros. simpl. lia. Qed.

Lemma size_styp_arrow_l : forall A B, size_styp A < size_styp (styp_arrow A B).
Proof. intros. simpl. lia. Qed.

Lemma size_styp_arrow_r : forall A B, size_styp B < size_styp (styp_arrow A B).
Proof. intros. simpl. lia. Qed.

Lemma sub_top_nat_false : forall c, sub styp_top styp_nat c -> False.
Proof.
  intros c H. apply NatReach_not_top.
  exact (@sub_nat_reach styp_top c H).
Qed.

Lemma sub_arrow_nat_false : forall A B c, sub (styp_arrow A B) styp_nat c -> False.
Proof.
  intros A B c H. apply (@NatReach_not_arrow A B).
  exact (@sub_nat_reach (styp_arrow A B) c H).
Qed.

Lemma sub_rcd_nat_false : forall l A c, sub (styp_rcd l A) styp_nat c -> False.
Proof.
  intros l A c H. apply (@NatReach_not_rcd l A).
  exact (@sub_nat_reach (styp_rcd l A) c H).
Qed.

Lemma size_styp_pos : forall A, size_styp A >= 1.
Proof. intros A. destruct A; simpl; lia. Qed.

Lemma size_styp_and_gt : forall A B, size_styp (styp_and A B) > 1.
Proof. intros. simpl. pose (size_styp_pos A). pose (size_styp_pos B). lia. Qed.

Lemma size_styp_rcd_gt : forall l A, size_styp (styp_rcd l A) > 1.
Proof. intros. simpl. pose (size_styp_pos A). lia. Qed.

Lemma size_styp_arrow_gt : forall A B, size_styp (styp_arrow A B) > 1.
Proof. intros. simpl. pose (size_styp_pos A). pose (size_styp_pos B). lia. Qed.

Lemma NatReach_and_not_both : forall A B,
  disjoint A B -> NatReach (styp_and A B) -> ~ (NatReach A /\ NatReach B).
Proof.
  intros A B HD HN [HA HB].
  exact (@disjoint_NatReach A B HD HA HB).
Qed.

(* ---------- fuel-indexed provenance relation ---------- *)
Inductive KT : nat -> sctx -> sexp -> dirflag -> styp -> exp -> exp -> Prop :=
  | KT_top : forall n Γ, uniq Γ -> KT (S n) Γ e_top Inf styp_top trm_unit trm_unit
  | KT_lit : forall n Γ i, uniq Γ -> KT (S n) Γ (e_lit i) Inf styp_nat (trm_lit i) (trm_lit i)
  | KT_var : forall n Γ x A, uniq Γ -> binds x A Γ ->
      KT (S n) Γ (e_var_f x) Inf A (trm_var_f x) (trm_var_f x)
  | KT_app : forall n Γ E1 E2 A1 A2 f1 f2 g1 g2,
      KT n Γ E1 Inf (styp_arrow A1 A2) f1 f2 ->
      KT n Γ E2 Chk A1 g1 g2 ->
      KT (S n) Γ (e_app E1 E2) Inf A2 (trm_app f1 g1) (trm_app f2 g2)
  | KT_merge : forall n Γ E1 E2 A1 A2 a1 b1 a2 b2,
      KT n Γ E1 Inf A1 a1 a2 -> KT n Γ E2 Inf A2 b1 b2 ->
      disjoint A1 A2 ->
      KT (S n) Γ (e_merge E1 E2) Inf (styp_and A1 A2)
        (trm_pair a1 b1) (trm_pair a2 b2)
  | KT_rcd : forall n Γ l E A e1 e2,
      KT n Γ E Inf A e1 e2 ->
      KT (S n) Γ (e_rcd l E) Inf (styp_rcd l A) (trm_rcd l e1) (trm_rcd l e2)
  | KT_proj : forall n Γ E l A e1 e2,
      KT n Γ E Inf (styp_rcd l A) e1 e2 ->
      KT (S n) Γ (e_proj E l) Inf A (trm_proj e1 l) (trm_proj e2 l)
  | KT_anno : forall n Γ E A e1 e2,
      KT n Γ E Chk A e1 e2 ->
      KT (S n) Γ (e_anno E A) Inf A e1 e2
  | KT_abs : forall n L Γ E A B e1 e2,
      (forall x, x \notin L ->
         KT n ((x~A)++Γ) (open_sexp_wrt_sexp E (e_var_f x)) Chk B
           (open_exp_wrt_exp e1 (trm_var_f x))
           (open_exp_wrt_exp e2 (trm_var_f x))) ->
      KT (S n) Γ (e_abs E) Chk (styp_arrow A B) (trm_abs e1) (trm_abs e2)
  | KT_sub : forall n Γ E A B c1 c2 e1 e2,
      KT n Γ E Inf B e1 e2 -> sub B A c1 -> sub B A c2 ->
      KT (S n) Γ E Chk A (trm_capp c1 e1) (trm_capp c2 e2).

Lemma KT_to_K : forall n Γ E dir A e1 e2,
  KT n Γ E dir A e1 e2 -> K Γ E dir A e1 e2.
Proof.
  intros n Γ E dir A e1 e2 H. induction H.
  - apply K_top; exact H.
  - apply K_lit; exact H.
  - eapply K_var; eassumption.
  - eapply K_app; eassumption.
  - eapply K_merge; eassumption.
  - eapply K_rcd; eassumption.
  - eapply K_proj; eassumption.
  - eapply K_anno; eassumption.
  - apply (@K_abs L Γ E0 A B e1 e2). exact H0.
  - eapply K_sub; eassumption.
Qed.

Lemma KT_n_mono : forall n Γ E dir A e1 e2,
  KT n Γ E dir A e1 e2 -> forall n', n <= n' -> KT n' Γ E dir A e1 e2.
Proof.
  intros n Γ E dir A e1 e2 H. induction H; intros n' Hle.
  - destruct n' as [|n'']; [inversion Hle |]. apply KT_top; exact H.
  - destruct n' as [|n'']; [inversion Hle |]. apply KT_lit; exact H.
  - destruct n' as [|n'']; [inversion Hle |]. eapply KT_var; eassumption.
  - destruct n' as [|n'']; [inversion Hle |].
    eapply KT_app; [apply IHKT1; lia | apply IHKT2; lia].
  - destruct n' as [|n'']; [inversion Hle |].
    eapply KT_merge; [apply IHKT1; lia | apply IHKT2; lia | exact H1].
  - destruct n' as [|n'']; [inversion Hle |].
    eapply KT_rcd; apply IHKT; lia.
  - destruct n' as [|n'']; [inversion Hle |].
    eapply KT_proj; apply IHKT; lia.
  - destruct n' as [|n'']; [inversion Hle |].
    eapply KT_anno; apply IHKT; lia.
  - destruct n' as [|n'']; [inversion Hle |].
    eapply KT_abs with (L := L).
    + intros x Hx. apply H0; [exact Hx | lia].
  - destruct n' as [|n'']; [inversion Hle |].
    eapply KT_sub; [apply IHKT; lia | exact H0 | exact H1].
Qed.

Lemma KT_swap : forall a b n Γ E dir A e1 e2,
  KT n Γ E dir A e1 e2 ->
  KT n (swap_sctx a b Γ) (swap_sexp a b E) dir A
       (swap_exp a b e1) (swap_exp a b e2).
Proof.
  intros a b n Γ E dir A e1 e2 H. induction H.
  - apply KT_top. apply uniq_swap_sctx. exact H.
  - apply KT_lit. apply uniq_swap_sctx. exact H.
  - eapply KT_var.
    + apply uniq_swap_sctx; exact H.
    + apply (proj2 (@binds_swap_sctx a b Γ x A)). exact H0.
  - eapply KT_app; [exact IHKT1 | exact IHKT2].
  - eapply KT_merge; [exact IHKT1 | exact IHKT2 | exact H1].
  - eapply KT_rcd; exact IHKT.
  - eapply KT_proj; exact IHKT.
  - eapply KT_anno; exact IHKT.
  - eapply KT_abs with (L := L \u {{a}} \u {{b}}).
    + intros x Hx.
      assert (HxL : x \notin L) by (intro Hc; apply Hx; fsetdec).
      assert (Hxa : x <> a) by (intro Hc; subst x; apply Hx; fsetdec).
      assert (Hxb : x <> b) by (intro Hc; subst x; apply Hx; fsetdec).
      pose proof (H0 x HxL) as Hb.
      rewrite (@swap_sctx_cons a b x A Γ) in Hb.
      rewrite (swap_atom_other a b x Hxa Hxb) in Hb.
      rewrite (@swap_sexp_open a b E0 x) in Hb.
      rewrite (swap_atom_other a b x Hxa Hxb) in Hb.
      rewrite (@swap_exp_open a b e1 x) in Hb.
      rewrite (swap_atom_other a b x Hxa Hxb) in Hb.
      rewrite (@swap_exp_open a b e2 x) in Hb.
      rewrite (swap_atom_other a b x Hxa Hxb) in Hb.
      exact Hb.
  - eapply KT_sub; [exact IHKT | exact H0 | exact H1].
Qed.

Lemma K_to_KT : forall Γ E dir A e1 e2,
  K Γ E dir A e1 e2 -> exists n, KT n Γ E dir A e1 e2.
Proof.
  intros Γ E dir A e1 e2 H. induction H.
  - exists 1. apply KT_top; exact H.
  - exists 1. apply KT_lit; exact H.
  - exists 1. eapply KT_var; eassumption.
  - destruct IHK1 as [n1 W1]. destruct IHK2 as [n2 W2].
    exists (S (Nat.max n1 n2)).
    eapply KT_app.
    + apply KT_n_mono with (n:=n1); [exact W1 | lia].
    + apply KT_n_mono with (n:=n2); [exact W2 | lia].
  - destruct IHK1 as [n1 W1]. destruct IHK2 as [n2 W2].
    exists (S (Nat.max n1 n2)).
    eapply KT_merge.
    + apply KT_n_mono with (n:=n1); [exact W1 | lia].
    + apply KT_n_mono with (n:=n2); [exact W2 | lia].
    + exact H1.
  - destruct IHK as [n0 W0]. exists (S n0). eapply KT_rcd. exact W0.
  - destruct IHK as [n0 W0]. exists (S n0). eapply KT_proj. exact W0.
  - destruct IHK as [n0 W0]. exists (S n0). eapply KT_anno. exact W0.
  - pose (SS := L \u dom Γ \u fv_sexp E0 \u fv_exp e1 \u fv_exp e2).
    destruct (atom_fresh SS) as [x0 Hx0].
    assert (Hx0L : x0 \notin L) by (intro Hc; apply Hx0; subst SS; fsetdec).
    destruct (H0 x0 Hx0L) as [n0 Hbody0].
    exists (S n0).
    eapply KT_abs with (L := SS \u {{x0}}).
    + intros x Hx.
      assert (HxL : x \notin L) by (intro Hc; apply Hx; fsetdec).
      assert (Hxd : x \notin dom Γ) by (intro Hc; apply Hx; fsetdec).
      assert (HxE : x \notin fv_sexp E0) by (intro Hc; apply Hx; fsetdec).
      assert (Hxe1 : x \notin fv_exp e1) by (intro Hc; apply Hx; fsetdec).
      assert (Hxe2 : x \notin fv_exp e2) by (intro Hc; apply Hx; fsetdec).
      assert (Hxx0 : x <> x0) by (intro Hc; subst x; apply Hx; fsetdec).
      assert (Hx0d : x0 \notin dom Γ) by (intro Hc; apply Hx0; subst SS; fsetdec).
      assert (Hx0E : x0 \notin fv_sexp E0) by (intro Hc; apply Hx0; subst SS; fsetdec).
      assert (Hx0e1 : x0 \notin fv_exp e1) by (intro Hc; apply Hx0; subst SS; fsetdec).
      assert (Hx0e2 : x0 \notin fv_exp e2) by (intro Hc; apply Hx0; subst SS; fsetdec).
      pose proof (@KT_swap x0 x n0 ((x0~A)++Γ)
                    (open_sexp_wrt_sexp E0 (e_var_f x0)) Chk B
                    (open_exp_wrt_exp e1 (trm_var_f x0))
                    (open_exp_wrt_exp e2 (trm_var_f x0)) Hbody0) as Hs.
      rewrite (@swap_sctx_cons x0 x x0 A Γ) in Hs.
      rewrite swap_atom_a in Hs.
      rewrite (@swap_sctx_id x0 x Γ Hx0d Hxd) in Hs.
      rewrite (@swap_sexp_open x0 x E0 x0) in Hs.
      rewrite swap_atom_a in Hs.
      rewrite (@swap_sexp_id x0 x E0 Hx0E HxE) in Hs.
      rewrite (@swap_exp_open x0 x e1 x0) in Hs.
      rewrite swap_atom_a in Hs.
      rewrite (@swap_exp_id x0 x e1 Hx0e1 Hxe1) in Hs.
      rewrite (@swap_exp_open x0 x e2 x0) in Hs.
      rewrite swap_atom_a in Hs.
      rewrite (@swap_exp_id x0 x e2 Hx0e2 Hxe2) in Hs.
      exact Hs.
  - destruct IHK as [n0 W0]. exists (S n0).
    eapply KT_sub; [exact W0 | exact H0 | exact H1].
Qed.

Lemma KT_swap_invol : forall a b n Γ E dir A e1 e2,
  KT n (swap_sctx a b Γ) (swap_sexp a b E) dir A
       (swap_exp a b e1) (swap_exp a b e2) ->
  KT n Γ E dir A e1 e2.
Proof.
  intros a b n Γ E dir A e1 e2 H.
  pose proof (@KT_swap a b n (swap_sctx a b Γ) (swap_sexp a b E)
                dir A (swap_exp a b e1) (swap_exp a b e2) H) as H2.
  rewrite swap_sctx_swap in H2.
  rewrite swap_sexp_swap in H2.
  rewrite swap_exp_swap in H2.
  rewrite swap_exp_swap in H2.
  exact H2.
Qed.

Lemma KT_fuel_pos : forall n Γ E dir A e1 e2,
  KT n Γ E dir A e1 e2 -> n >= 1.
Proof. intros n Γ E dir A e1 e2 H. induction H; lia. Qed.

Lemma KT_exists_fuel_ge : forall n Γ E dir A e1 e2,
  KT n Γ E dir A e1 e2 -> exists m, m >= 1 /\ KT m Γ E dir A e1 e2.
Proof.
  intros. exists n. split; [exact (@KT_fuel_pos n Γ E0 dir A e1 e2 H) | exact H].
Qed.

Lemma K_KT_iff : forall Γ E dir A e1 e2,
  K Γ E dir A e1 e2 <-> (exists n, KT n Γ E dir A e1 e2).
Proof.
  intros. split.
  - apply K_to_KT.
  - intros [n Hn]. exact (@KT_to_K n Γ E0 dir A e1 e2 Hn).
Qed.

Definition EnvRelT (R : styp -> exp -> exp -> Prop) (Γ:sctx)
  (σ1 σ2 : var -> exp) : Prop :=
  forall x A, binds x A Γ -> R A (σ1 x) (σ2 x).

Lemma EnvRelT_extend : forall R Γ σ1 σ2 x A u1 u2,
  EnvRelT R Γ σ1 σ2 -> uniq ((x~A)++Γ) ->
  R A u1 u2 ->
  EnvRelT R ((x~A)++Γ) (extend σ1 x u1) (extend σ2 x u2).
Proof.
  intros R Γ σ1 σ2 x A u1 u2 HE HUniq HR y B Hb.
  apply binds_cons_1 in Hb.
  destruct Hb as [[Hxy HAB]|Htail].
  - subst y B. unfold extend.
    destruct (eq_var x x) as [E|E]; [exact HR | exfalso; apply E; reflexivity].
  - unfold extend.
    destruct (eq_var y x) as [Hyx|Hneq].
    + exfalso. subst y.
      apply (@binds_dom_contradiction _ x B Γ Htail).
      exact (@uniq_cons_2 _ x A Γ HUniq).
    + apply HE. exact Htail.
Qed.

Lemma hasT_K_pair : forall k1 k2 N1 N2 Γ E dir A e1 e2,
  hasT k1 N1 Γ E dir A e1 -> hasT k2 N2 Γ E dir A e2 ->
  K Γ E dir A e1 e2.
Proof.
  intros k1 k2 N1 N2 Γ E dir A e1 e2 H1 H2.
  apply K_complete.
  - exact (@hasT_to_has_type k1 N1 Γ E dir A e1 H1).
  - exact (@hasT_to_has_type k2 N2 Γ E dir A e2 H2).
Qed.

Lemma hasT_to_KT : forall k N Γ E dir A e,
  hasT k N Γ E dir A e -> exists m, KT m Γ E dir A e e.
Proof.
  intros k N Γ E dir A e H.
  apply K_to_KT.
  apply K_self.
  exact (@hasT_to_has_type k N Γ E dir A e H).
Qed.

Lemma hasT_two_to_KT : forall k1 k2 N1 N2 Γ E dir A e1 e2,
  hasT k1 N1 Γ E dir A e1 -> hasT k2 N2 Γ E dir A e2 ->
  exists m, KT m Γ E dir A e1 e2.
Proof.
  intros k1 k2 N1 N2 Γ E dir A e1 e2 H1 H2.
  apply K_to_KT.
  exact (@hasT_K_pair k1 k2 N1 N2 Γ E dir A e1 e2 H1 H2).
Qed.

Lemma WF_nat_inv : forall v, WF styp_nat v -> exists k, v = trm_lit k.
Proof. intros v H. simpl in H. exact H. Qed.

Lemma E_nat_kleene : forall t1 t2, E styp_nat t1 t2 -> kleene_equiv t1 t2.
Proof.
  intros t1 t2 [v1 [v2 [S1 [S2 [W1 [W2 AE]]]]]].
  simpl in AE. destruct AE as [k [E1 E2]]. subst v1 v2.
  exists k; split; assumption.
Qed.

Lemma WF_nat_iff : forall v,
  WF styp_nat v <-> (exists k, v = trm_lit k).
Proof.
  intros v. split.
  - apply WF_nat_inv.
  - intros [k E]. subst. simpl. exists k. reflexivity.
Qed.

Lemma AE_nat_iff : forall v1 v2,
  AE styp_nat v1 v2 <-> (exists k, v1 = trm_lit k /\ v2 = trm_lit k).
Proof. intros. simpl. tauto. Qed.

Lemma kleene_to_E_nat : forall t1 t2,
  kleene_equiv t1 t2 -> E styp_nat t1 t2.
Proof.
  intros t1 t2 [k [S1 S2]]. exists (trm_lit k), (trm_lit k).
  repeat split; auto.
  - simpl. exists k. reflexivity.
  - simpl. exists k. reflexivity.
  - simpl. exists k. split; reflexivity.
Qed.

Lemma E_nat_iff_kleene : forall t1 t2,
  E styp_nat t1 t2 <-> kleene_equiv t1 t2.
Proof.
  intros. split.
  - apply E_nat_kleene.
  - apply kleene_to_E_nat.
Qed.

Lemma binds_nil_false : forall x A, binds x A (@nil (atom*styp)) -> False.
Proof. intros x A H. apply (@binds_nil_iff styp x A) in H. exact H. Qed.

Lemma K_to_KT_ge : forall Γ E dir A e1 e2,
  K Γ E dir A e1 e2 ->
  exists n, n >= 1 /\ KT n Γ E dir A e1 e2.
Proof.
  intros Γ E dir A e1 e2 H.
  destruct (K_to_KT Γ E dir A e1 e2 H) as [n Hn].
  exists n. split.
  - exact (@KT_fuel_pos n Γ E dir A e1 e2 Hn).
  - exact Hn.
Qed.

Lemma E_nat_coerce : forall t1 t2 c1 c2,
  E styp_nat t1 t2 ->
  sub styp_nat styp_nat c1 -> sub styp_nat styp_nat c2 ->
  E styp_nat (trm_capp c1 t1) (trm_capp c2 t2).
Proof.
  intros t1 t2 c1 c2 HE H1 H2.
  destruct (E_nat_kleene t1 t2 HE) as [k [S1 S2]].
  exists (trm_lit k), (trm_lit k).
  split.
  - eapply star_trans.
    + apply star_capp; exact S1.
    + apply sub_nat_nat_star; exact H1.
  - split.
    + eapply star_trans.
      * apply star_capp; exact S2.
      * apply sub_nat_nat_star; exact H2.
    + simpl. split.
      * exists k. reflexivity.
      * split.
        -- exists k. reflexivity.
        -- exists k. split; reflexivity.
Qed.

Lemma E_top_star : forall t1 t2,
  E styp_top t1 t2 ->
  (step star) t1 trm_unit /\ (step star) t2 trm_unit.
Proof.
  intros t1 t2 [v1 [v2 [S1 [S2 [W1 [W2 AE]]]]]].
  simpl in W1, W2. subst v1 v2. split; assumption.
Qed.

Lemma E_rcd_inv : forall l A t1 t2,
  E (styp_rcd l A) t1 t2 ->
  exists a1 a2, (step star) t1 (trm_rcd l a1) /\ (step star) t2 (trm_rcd l a2) /\
                E A a1 a2.
Proof.
  intros l A t1 t2 [v1 [v2 [S1 [S2 [W1 [W2 AE]]]]]].
  simpl in W1, W2, AE.
  destruct W1 as [a1 [E1 W1]]. destruct W2 as [a2 [E2 W2]].
  destruct AE as [b1 [b2 [F1 [F2 Ab]]]].
  assert (a1 = b1) by congruence. assert (a2 = b2) by congruence.
  subst b1 b2. subst v1 v2.
  exists a1, a2. split; [exact S1 | split; [exact S2 |]].
  exists a1, a2. repeat split; auto; apply star_refl.
Qed.

Lemma E_and_inv : forall A B t1 t2,
  E (styp_and A B) t1 t2 ->
  exists a1 b1 a2 b2,
    (step star) t1 (trm_pair a1 b1) /\ (step star) t2 (trm_pair a2 b2) /\
    E A a1 a2 /\ E B b1 b2.
Proof.
  intros A B t1 t2 [v1 [v2 [S1 [S2 [W1 [W2 AE]]]]]].
  simpl in W1, W2, AE.
  destruct W1 as [a1 [b1 [E1 [Wa1 Wb1]]]].
  destruct W2 as [a2 [b2 [E2 [Wa2 Wb2]]]].
  destruct AE as [c1 [d1 [c2 [d2 [F1 [F2 [Ac Ad]]]]]]].
  assert (a1 = c1) by congruence. assert (b1 = d1) by congruence.
  assert (a2 = c2) by congruence. assert (b2 = d2) by congruence.
  subst c1 d1 c2 d2. subst v1 v2.
  exists a1, b1, a2, b2. repeat split; auto.
  - exists a1, a2. repeat split; auto; apply star_refl.
  - exists b1, b2. repeat split; auto; apply star_refl.
Qed.

Lemma E_arrow_inv : forall A B t1 t2,
  E (styp_arrow A B) t1 t2 ->
  exists f1 f2, (step star) t1 f1 /\ (step star) t2 f2 /\
                WF (styp_arrow A B) f1 /\ WF (styp_arrow A B) f2 /\
                AE (styp_arrow A B) f1 f2.
Proof. intros. exact H. Qed.

Lemma E_and_proj1 : forall A B t1 t2,
  E (styp_and A B) t1 t2 ->
  E A (trm_capp co_proj1 t1) (trm_capp co_proj1 t2).
Proof.
  intros A B t1 t2 [v1 [v2 [S1 [S2 [W1 [W2 AE]]]]]].
  simpl in W1, W2, AE.
  destruct W1 as [a1 [b1 [E1 [Wa1 Wb1]]]].
  destruct W2 as [a2 [b2 [E2 [Wa2 Wb2]]]].
  destruct AE as [c1 [d1 [c2 [d2 [F1 [F2 [Ac Ad]]]]]]].
  assert (a1 = c1) by congruence. assert (b1 = d1) by congruence.
  assert (a2 = c2) by congruence. assert (b2 = d2) by congruence.
  subst c1 d1 c2 d2. subst v1 v2.
  eapply (@E_star_lr A (trm_capp co_proj1 t1) a1
             (trm_capp co_proj1 t2) a2).
  - eapply star_trans.
    + apply star_capp; exact S1.
    + eapply star_step.
      * apply step_projl; [exact (@WF_value A a1 Wa1) | exact (@WF_value B b1 Wb1)].
      * apply star_refl.
  - eapply star_trans.
    + apply star_capp; exact S2.
    + eapply star_step.
      * apply step_projl; [exact (@WF_value A a2 Wa2) | exact (@WF_value B b2 Wb2)].
      * apply star_refl.
  - exists a1, a2. repeat split; auto; apply star_refl.
Qed.

Lemma E_and_proj2 : forall A B t1 t2,
  E (styp_and A B) t1 t2 ->
  E B (trm_capp co_proj2 t1) (trm_capp co_proj2 t2).
Proof.
  intros A B t1 t2 [v1 [v2 [S1 [S2 [W1 [W2 AE]]]]]].
  simpl in W1, W2, AE.
  destruct W1 as [a1 [b1 [E1 [Wa1 Wb1]]]].
  destruct W2 as [a2 [b2 [E2 [Wa2 Wb2]]]].
  destruct AE as [c1 [d1 [c2 [d2 [F1 [F2 [Ac Ad]]]]]]].
  assert (a1 = c1) by congruence. assert (b1 = d1) by congruence.
  assert (a2 = c2) by congruence. assert (b2 = d2) by congruence.
  subst c1 d1 c2 d2. subst v1 v2.
  eapply (@E_star_lr B (trm_capp co_proj2 t1) b1
             (trm_capp co_proj2 t2) b2).
  - eapply star_trans.
    + apply star_capp; exact S1.
    + eapply star_step.
      * apply step_projr; [exact (@WF_value A a1 Wa1) | exact (@WF_value B b1 Wb1)].
      * apply star_refl.
  - eapply star_trans.
    + apply star_capp; exact S2.
    + eapply star_step.
      * apply step_projr; [exact (@WF_value A a2 Wa2) | exact (@WF_value B b2 Wb2)].
      * apply star_refl.
  - exists b1, b2. repeat split; auto; apply star_refl.
Qed.

Lemma E_nat_star : forall t1 t2,
  E styp_nat t1 t2 ->
  exists k, (step star) t1 (trm_lit k) /\ (step star) t2 (trm_lit k).
Proof.
  intros t1 t2 [v1 [v2 [S1 [S2 [W1 [W2 AE]]]]]].
  simpl in AE. destruct AE as [k [E1 E2]].
  subst v1 v2. exists k. split; assumption.
Qed.

Lemma E_and_components : forall A B t1 t2,
  E (styp_and A B) t1 t2 ->
  E A (trm_capp co_proj1 t1) (trm_capp co_proj1 t2) /\
  E B (trm_capp co_proj2 t1) (trm_capp co_proj2 t2).
Proof.
  intros. split.
  - exact (@E_and_proj1 A B t1 t2 H).
  - exact (@E_and_proj2 A B t1 t2 H).
Qed.

(* ---------- clean syntactic relation mirroring K/KC ---------- *)
Fixpoint lk (Γ:sctx) (x:atom) : option styp :=
  match Γ with
  | nil => None
  | (y,A)::Γ' => if x == y then Some A else lk Γ' x
  end.

Lemma lk_binds : forall Γ x A,
  lk Γ x = Some A -> binds x A Γ.
Proof.
  intros Γ. induction Γ as [| [y C] rest IH]; intros x A H; simpl in *.
  - discriminate H.
  - destruct (x == y) as [E|E].
    + subst y. inversion H. subst C. simpl. left. auto.
    + simpl. right. apply IH. exact H.
Qed.

Lemma lk_dom : forall Γ x A, lk Γ x = Some A -> x \in dom Γ.
Proof.
  intros. apply (@binds_In _ x A Γ). apply lk_binds. exact H.
Qed.

Lemma uniq_binds_lk : forall Γ x A,
  uniq Γ -> binds x A Γ -> lk Γ x = Some A.
Proof.
  intros Γ. induction Γ as [| [y C] rest IH]; intros x A Hu Hb.
  - simpl in Hb. inversion Hb.
  - simpl in Hu. simpl in Hb. apply binds_cons_1 in Hb.
    destruct Hb as [[Hxy HAC]|Htail].
    + subst x A. simpl.
      destruct (y == y) as [E|E]; [reflexivity|exfalso; auto].
    + simpl. destruct (x == y) as [Exy|Exy].
      * exfalso. subst x.
        exact (@binds_dom_contradiction _ y A rest Htail
                 (@uniq_cons_2 _ y C rest Hu)).
      * apply IH.
        -- exact (@uniq_cons_1 _ y C rest Hu).
        -- exact Htail.
Qed.

Lemma lk_app_end : forall Γ x A z B,
  lk Γ x = Some A -> lk (Γ ++ [(z,B)]) x = Some A.
Proof.
  intros Γ. induction Γ as [| [y C] rest IH]; intros x A z B H; simpl in *.
  - discriminate H.
  - destruct (x == y) as [E|E]; [exact H|].
    apply IH. exact H.
Qed.

Inductive EK : sctx -> styp -> exp -> exp -> Prop :=
  | EK_top : forall Γ, EK Γ styp_top trm_unit trm_unit
  | EK_nat : forall Γ k, EK Γ styp_nat (trm_lit k) (trm_lit k)
  | EK_var : forall Γ x A, lk Γ x = Some A -> EK Γ A (trm_var_f x) (trm_var_f x)
  | EK_and : forall Γ A B a1 b1 a2 b2,
      disjoint A B -> EK Γ A a1 a2 -> EK Γ B b1 b2 ->
      EK Γ (styp_and A B) (trm_pair a1 b1) (trm_pair a2 b2)
  | EK_rcd : forall Γ l A a1 a2,
      EK Γ A a1 a2 ->
      EK Γ (styp_rcd l A) (trm_rcd l a1) (trm_rcd l a2)
  | EK_absc : forall L Γ A B e1 e2,
      (forall x, x \notin L -> EK ((x~A)++Γ) B
         (open_exp_wrt_exp e1 (trm_var_f x))
         (open_exp_wrt_exp e2 (trm_var_f x))) ->
      EK Γ (styp_arrow A B) (trm_abs e1) (trm_abs e2)
  | EK_arrow : forall x Γ A B e1 e2,
      EK ((x~A)++Γ) B e1 e2 ->
      EK Γ (styp_arrow A B)
        (trm_abs (close_exp_wrt_exp x e1))
        (trm_abs (close_exp_wrt_exp x e2))
  | EK_sub : forall Γ B A c1 c2 t1 t2,
      EK Γ B t1 t2 -> sub B A c1 -> sub B A c2 ->
      EK Γ A (trm_capp c1 t1) (trm_capp c2 t2)
  | EK_app : forall Γ A B f1 f2 g1 g2,
      EK Γ (styp_arrow A B) f1 f2 -> EK Γ A g1 g2 ->
      EK Γ B (trm_app f1 g1) (trm_app f2 g2)
  | EK_proj : forall Γ l A t1 t2,
      EK Γ (styp_rcd l A) t1 t2 ->
      EK Γ A (trm_proj t1 l) (trm_proj t2 l).

Lemma K_to_EK : forall Γ E dir A e1 e2,
  K Γ E dir A e1 e2 -> EK Γ A e1 e2.
Proof.
  intros Γ E dir A e1 e2 H. induction H.
  - apply EK_top.
  - apply EK_nat.
  - apply EK_var. apply uniq_binds_lk; [exact H | exact H0].
  - eapply EK_app; eassumption.
  - eapply EK_and; eassumption.
  - eapply EK_rcd; eassumption.
  - eapply EK_proj; eassumption.
  - exact IHK.
  - apply EK_absc with (L:=L). exact H0.
  - eapply EK_sub; eassumption.
Qed.

Lemma has_type_EK_self : forall Γ E dir A e,
  has_type Γ E dir A e -> EK Γ A e e.
Proof.
  intros. exact (@K_to_EK Γ E0 dir A e e (@K_self Γ E0 dir A e H)).
Qed.

Lemma KC_to_EK : forall Γ dir A t1 t2,
  KC Γ dir A t1 t2 -> EK Γ A t1 t2.
Proof.
  intros Γ dir A t1 t2 H. induction H.
  - exact (@K_to_EK _ _ _ _ _ _ H).
  - eapply EK_app.
    + apply IHKC.
    + exact (@has_type_EK_self Γ ee Chk A1 e H0).
  - eapply EK_app.
    + exact (@has_type_EK_self Γ ee Inf (styp_arrow A1 A2) f H).
    + apply IHKC.
  - eapply EK_and.
    + exact H1.
    + apply IHKC.
    + exact (@has_type_EK_self Γ ee Inf A2 e H0).
  - eapply EK_and.
    + exact H1.
    + exact (@has_type_EK_self Γ ee Inf A1 e H).
    + apply IHKC.
  - eapply EK_rcd. apply IHKC.
  - eapply EK_proj. apply IHKC.
  - exact IHKC.
  - eapply EK_arrow with (x:=x). apply IHKC.
Qed.

Lemma has_type_pair_to_EK : forall Γ E dir A e1 e2,
  has_type Γ E dir A e1 -> has_type Γ E dir A e2 ->
  EK Γ A e1 e2.
Proof.
  intros Γ E0 dir A e1 e2 H H0.
  exact (@K_to_EK Γ E0 dir A e1 e2 (@K_complete Γ E0 dir A e1 e2 H H0)).
Qed.

Lemma EK_of_KC_nat : forall Γ dir t1 t2,
  KC Γ dir styp_nat t1 t2 -> EK Γ styp_nat t1 t2.
Proof. intros. exact (@KC_to_EK Γ dir styp_nat t1 t2 H). Qed.

Lemma EK_id : forall Γ A t1 t2,
  EK Γ A t1 t2 -> EK Γ A (trm_capp co_id t1) (trm_capp co_id t2).
Proof.
  intros. eapply EK_sub.
  - exact H.
  - apply S_refl.
  - apply S_refl.
Qed.

Lemma EK_trans : forall Γ B A C c1 c2 d1 d2 t1 t2,
  EK Γ B t1 t2 ->
  sub B A c1 -> sub B A c2 ->
  sub A C d1 -> sub A C d2 ->
  EK Γ C (trm_capp (co_trans d1 c1) t1)
           (trm_capp (co_trans d2 c2) t2).
Proof.
  intros Γ B A C c1 c2 d1 d2 t1 t2 H H0 H1 H2 H3.
  eapply EK_sub.
  - exact H.
  - exact (S_trans B C d1 c1 A H2 H0).
  - exact (S_trans B C d2 c2 A H3 H1).
Qed.

Lemma close_rec_id : forall e k x,
  lcg k e -> x \notin fv_exp e -> close_exp_wrt_exp_rec k x e = e.
Proof.
  intros e. induction e; intros k xx Hlc Hfv; simpl in *; auto.
  - destruct (lt_ge_dec n k) as [Hlt|Hge]; [reflexivity | exfalso; lia].
  - destruct (xx == x) as [Heq|Hne].
    + exfalso. apply Hfv. subst xx. simpl. fsetdec.
    + reflexivity.
  - rewrite (IHe (S k) xx Hlc Hfv). reflexivity.
  - destruct Hlc as [H1 H2].
    rewrite (IHe1 k xx H1 ltac:(fsetdec)).
    rewrite (IHe2 k xx H2 ltac:(fsetdec)). reflexivity.
  - destruct Hlc as [H1 H2].
    rewrite (IHe1 k xx H1 ltac:(fsetdec)).
    rewrite (IHe2 k xx H2 ltac:(fsetdec)). reflexivity.
  - rewrite (IHe k xx Hlc ltac:(fsetdec)). reflexivity.
  - rewrite (IHe k xx Hlc ltac:(fsetdec)). reflexivity.
  - rewrite (IHe k xx Hlc ltac:(fsetdec)). reflexivity.
Qed.

Lemma subst_env_close : forall t k x sigma,
  lcg k t ->
  (forall y, lcg 0 (sigma y)) ->
  (forall y, x \notin fv_exp (sigma y)) ->
  subst_env sigma (close_exp_wrt_exp_rec k x t) =
  close_exp_wrt_exp_rec k x (subst_env (extend sigma x (trm_var_f x)) t).
Proof.
  intros t. induction t; intros k xx sigma Hlc Hs Hx; simpl in *.
  - (* var_b *) destruct (lt_ge_dec n k); reflexivity.
  - (* var_f *) unfold extend.
    destruct (x == xx) as [Heq|Hne].
    + subst x. simpl.
      destruct (xx == xx) as [E|E]; [reflexivity | exfalso; apply E; reflexivity].
    + destruct (xx == x) as [E|E].
      * exfalso. apply Hne. symmetry. exact E.
      * simpl. symmetry. apply close_rec_id.
        -- apply lcg_mono with (n0:=0); [lia | apply Hs].
        -- apply Hx.
  - (* unit *) reflexivity.
  - (* lit *) reflexivity.
  - (* abs *) rewrite (IHt (S k) xx sigma Hlc Hs Hx). reflexivity.
  - (* app *) destruct Hlc as [H1 H2].
    rewrite (IHt1 k xx sigma H1 Hs Hx).
    rewrite (IHt2 k xx sigma H2 Hs Hx). reflexivity.
  - (* pair *) destruct Hlc as [H1 H2].
    rewrite (IHt1 k xx sigma H1 Hs Hx).
    rewrite (IHt2 k xx sigma H2 Hs Hx). reflexivity.
  - (* rcd *) rewrite (IHt k xx sigma Hlc Hs Hx). reflexivity.
  - (* proj *) rewrite (IHt k xx sigma Hlc Hs Hx). reflexivity.
  - (* capp *) rewrite (IHt k xx sigma Hlc Hs Hx). reflexivity.
Qed.

Lemma subst_env_close_neq : forall t k x sigma,
  lcg k t ->
  (forall y, lcg 0 (sigma y)) ->
  (forall y, y <> x -> x \notin fv_exp (sigma y)) ->
  subst_env sigma (close_exp_wrt_exp_rec k x t) =
  close_exp_wrt_exp_rec k x (subst_env (extend sigma x (trm_var_f x)) t).
Proof.
  intros t. induction t; intros k xx sigma Hlc Hs Hx; simpl in *.
  - (* var_b *) destruct (lt_ge_dec n k); reflexivity.
  - (* var_f *) unfold extend.
    destruct (x == xx) as [Heq|Hne].
    + subst x. simpl.
      destruct (xx == xx) as [E|E]; [reflexivity | exfalso; apply E; reflexivity].
    + destruct (xx == x) as [E|E].
      * exfalso. apply Hne. symmetry. exact E.
      * simpl. symmetry. apply close_rec_id.
        -- apply lcg_mono with (n0:=0); [lia | apply Hs].
        -- exact (Hx x Hne).
  - (* unit *) reflexivity.
  - (* lit *) reflexivity.
  - (* abs *) rewrite (IHt (S k) xx sigma Hlc Hs Hx). reflexivity.
  - (* app *) destruct Hlc as [H1 H2].
    rewrite (IHt1 k xx sigma H1 Hs Hx).
    rewrite (IHt2 k xx sigma H2 Hs Hx). reflexivity.
  - (* pair *) destruct Hlc as [H1 H2].
    rewrite (IHt1 k xx sigma H1 Hs Hx).
    rewrite (IHt2 k xx sigma H2 Hs Hx). reflexivity.
  - (* rcd *) rewrite (IHt k xx sigma Hlc Hs Hx). reflexivity.
  - (* proj *) rewrite (IHt k xx sigma Hlc Hs Hx). reflexivity.
  - (* capp *) rewrite (IHt k xx sigma Hlc Hs Hx). reflexivity.
Qed.

Definition EnvEK (L:atoms) (Γ:sctx) (σ1 σ2:var->exp) : Prop :=
  (forall y, lcg 0 (σ1 y) /\ lcg 0 (σ2 y) /\
             fv_exp (σ1 y) [<=] L /\ fv_exp (σ2 y) [<=] L) /\
  (forall Δ x A, binds x A Γ -> EK Δ A (σ1 x) (σ2 x)).

Lemma EnvEK_lc : forall L Γ σ1 σ2 y,
  EnvEK L Γ σ1 σ2 -> lcg 0 (σ1 y) /\ lcg 0 (σ2 y).
Proof.
  intros L Γ σ1 σ2 y [Hs _]. pose (Hs y) as H. tauto.
Qed.

Lemma EnvEK_support : forall L Γ σ1 σ2 y,
  EnvEK L Γ σ1 σ2 ->
  fv_exp (σ1 y) [<=] L /\ fv_exp (σ2 y) [<=] L.
Proof.
  intros L Γ σ1 σ2 y [Hs _]. pose (Hs y) as H. tauto.
Qed.

Lemma EnvEK_typing : forall L Γ σ1 σ2 Δ x A,
  EnvEK L Γ σ1 σ2 -> binds x A Γ -> EK Δ A (σ1 x) (σ2 x).
Proof.
  intros L Γ σ1 σ2 Δ x A [_ Ht]. apply Ht.
Qed.

Lemma open_close_rec_subst : forall e k x y,
  open_exp_wrt_exp_rec k (trm_var_f y) (close_exp_wrt_exp_rec k x e) =
  subst_env (fun z => if z == x then trm_var_f y else trm_var_f z) e.
Proof.
  intros e. induction e; intros k xx yy; simpl.
  - (* var_b *) destruct k as [|k'].
    + simpl. replace (n - 0) with n by lia. reflexivity.
    + destruct (lt_ge_dec n (S k')) as [Hlt|Hge].
      * simpl. destruct (lt_eq_lt_dec n (S k')) as [[H1|H1]|H1].
        -- reflexivity.
        -- lia.
        -- lia.
      * simpl. destruct (lt_eq_lt_dec (S n) (S k')) as [[H1|H1]|H1].
        -- lia.
        -- lia.
        -- cbn [Nat.sub].
           destruct (lt_eq_lt_dec n k') as [[H2|H2]|H2].
           ++ lia.
           ++ lia.
           ++ replace (n - 0) with n by lia. reflexivity.
  - (* var_f *) unfold close_exp_wrt_exp. simpl.
    destruct (xx == x) as [Heq|Hne].
    + subst xx. simpl.
      destruct (x == x) as [Ex|Ex]; [|exfalso; auto].
      destruct (lt_eq_lt_dec k k) as [[H1|H1]|H1]; [lia| |lia].
      reflexivity.
    + simpl. destruct (x == xx) as [Heq|Hne']; [exfalso; auto|].
      simpl. reflexivity.
  - (* unit *) reflexivity.
  - (* lit *) reflexivity.
  - (* abs *) simpl. rewrite (IHe (S k) xx yy). reflexivity.
  - (* app *) simpl. rewrite (IHe1 k xx yy). rewrite (IHe2 k xx yy). reflexivity.
  - (* pair *) simpl. rewrite (IHe1 k xx yy). rewrite (IHe2 k xx yy). reflexivity.
  - (* rcd *) simpl. rewrite (IHe k xx yy). reflexivity.
  - (* proj *) simpl. rewrite (IHe k xx yy). reflexivity.
  - (* capp *) simpl. rewrite (IHe k xx yy). reflexivity.
Qed.

Lemma open_close_subst : forall e x y,
  open_exp_wrt_exp (close_exp_wrt_exp x e) (trm_var_f y) =
  subst_env (fun z => if z == x then trm_var_f y else trm_var_f z) e.
Proof. intros. apply open_close_rec_subst. Qed.

Lemma EK_lc : forall Γ A t1 t2, EK Γ A t1 t2 -> lc_exp t1 /\ lc_exp t2.
Proof.
  intros Γ A t1 t2 H.
  induction H.
  - split; apply lc_trm_unit.
  - split; apply lc_trm_lit.
  - split; apply lc_trm_var_f.
  - destruct IHEK1 as [Hl1 Hr1]. destruct IHEK2 as [Hl2 Hr2].
    split; apply lc_trm_pair; assumption.
  - destruct IHEK as [Hl Hr]. split; apply lc_trm_rcd; assumption.
  - destruct (atom_fresh L) as [x0 Hx0].
    destruct (H0 x0 Hx0) as [Hl Hr].
    split; apply lc_trm_abs; intro y;
      [apply (open_lc_any e1 x0 y Hl) | apply (open_lc_any e2 x0 y Hr)].
  - destruct IHEK as [Hl Hr]. split.
    + apply lc_trm_abs. intro y. rewrite open_close_subst.
      apply subst_env_lc. assumption.
      intro z. destruct (z == x); apply lc_trm_var_f.
    + apply lc_trm_abs. intro y. rewrite open_close_subst.
      apply subst_env_lc. assumption.
      intro z. destruct (z == x); apply lc_trm_var_f.
  - destruct IHEK as [Hl Hr]. split; apply lc_trm_capp; assumption.
  - destruct IHEK1 as [Hl1 Hr1]. destruct IHEK2 as [Hl2 Hr2].
    split; apply lc_trm_app; assumption.
  - destruct IHEK as [Hl Hr]. split; apply lc_trm_proj; assumption.
Qed.

Lemma close_rec_var_f_eq : forall k x,
  close_exp_wrt_exp_rec k x (trm_var_f x) = trm_var_b k.
Proof.
  intros. simpl. destruct (x == x) as [E|E]; [reflexivity|exfalso; auto].
Qed.

Lemma close_rec_var_f_neq : forall k x z,
  z <> x -> close_exp_wrt_exp_rec k x (trm_var_f z) = trm_var_f z.
Proof.
  intros. simpl. destruct (x == z) as [E|E]; [exfalso; auto|reflexivity].
Qed.

Lemma close_rename_rec : forall t k x y,
  y \notin fv_exp t ->
  close_exp_wrt_exp_rec k x t =
  close_exp_wrt_exp_rec k y
    (subst_env (fun z => if z == x then trm_var_f y else trm_var_f z) t).
Proof.
  intros t. induction t; intros k xx yy Hfv; simpl in *.
  - (* var_b *) reflexivity.
  - (* var_f *) simpl in Hfv.
    destruct (xx == x) as [Heq|Hne].
    + subst xx.
      destruct (x == x) as [E|E]; [|exfalso; auto].
      rewrite (close_rec_var_f_eq k yy). reflexivity.
    + simpl. destruct (x == xx) as [E|E]; [exfalso; apply Hne; symmetry; exact E|].
      rewrite (close_rec_var_f_neq k yy x).
      * reflexivity.
      * intro Hxy. apply Hfv. subst yy. simpl. fsetdec.
  - (* unit *) reflexivity.
  - (* lit *) reflexivity.
  - (* abs *) rewrite (IHt (S k) xx yy). reflexivity. exact Hfv.
  - (* app *) assert (H1 : yy \notin fv_exp t1) by fsetdec.
    assert (H2 : yy \notin fv_exp t2) by fsetdec.
    rewrite (IHt1 k xx yy H1). rewrite (IHt2 k xx yy H2). reflexivity.
  - (* pair *) assert (H1 : yy \notin fv_exp t1) by fsetdec.
    assert (H2 : yy \notin fv_exp t2) by fsetdec.
    rewrite (IHt1 k xx yy H1). rewrite (IHt2 k xx yy H2). reflexivity.
  - (* rcd *) rewrite (IHt k xx yy). reflexivity. exact Hfv.
  - (* proj *) rewrite (IHt k xx yy). reflexivity. exact Hfv.
  - (* capp *) rewrite (IHt k xx yy). reflexivity. exact Hfv.
Qed.

Lemma close_rename : forall t x y,
  y \notin fv_exp t ->
  close_exp_wrt_exp x t =
  close_exp_wrt_exp y
    (subst_env (fun z => if z == x then trm_var_f y else trm_var_f z) t).
Proof. intros. apply close_rename_rec. exact H. Qed.

Lemma subst_rename_comp : forall t x y sigma,
  y \notin fv_exp t ->
  subst_env (extend sigma y (trm_var_f y))
    (subst_env (fun z => if z == x then trm_var_f y else trm_var_f z) t)
  = subst_env (extend sigma x (trm_var_f y)) t.
Proof.
  intros t. induction t; intros xx yy sigma Hfv; simpl in *.
  - (* var_b *) reflexivity.
  - (* var_f *) simpl in Hfv.
    destruct (x == xx) as [Heq|Hne].
    + subst xx. unfold extend. simpl.
      destruct (x == x) as [E|E]; [|exfalso; auto].
      destruct (yy == yy) as [E2|E2]; [reflexivity|exfalso; auto].
    + simpl. unfold extend.
      destruct (x == xx) as [E|E]; [exfalso; auto|].
      destruct (x == yy) as [E2|E2].
      * exfalso. apply Hfv. subst yy. simpl. fsetdec.
      * reflexivity.
  - (* unit *) reflexivity.
  - (* lit *) reflexivity.
  - (* abs *) rewrite (IHt xx yy sigma). reflexivity. exact Hfv.
  - (* app *) assert (H1 : yy \notin fv_exp t1) by fsetdec.
    assert (H2 : yy \notin fv_exp t2) by fsetdec.
    rewrite (IHt1 xx yy sigma H1). rewrite (IHt2 xx yy sigma H2). reflexivity.
  - (* pair *) assert (H1 : yy \notin fv_exp t1) by fsetdec.
    assert (H2 : yy \notin fv_exp t2) by fsetdec.
    rewrite (IHt1 xx yy sigma H1). rewrite (IHt2 xx yy sigma H2). reflexivity.
  - (* rcd *) rewrite (IHt xx yy sigma). reflexivity. exact Hfv.
  - (* proj *) rewrite (IHt xx yy sigma). reflexivity. exact Hfv.
  - (* capp *) rewrite (IHt xx yy sigma). reflexivity. exact Hfv.
Qed.



Definition CohNat (A:styp) (t:exp) : Prop :=
  forall c1 c2, sub A styp_nat c1 -> sub A styp_nat c2 ->
  E styp_nat (trm_capp c1 t) (trm_capp c2 t).

Lemma CohNat_top : forall t, CohNat styp_top t.
Proof.
  intros t c1 c2 H1 H2. exfalso.
  exact (@sub_top_nat_false c1 H1).
Qed.

Lemma CohNat_arrow : forall A B t, CohNat (styp_arrow A B) t.
Proof.
  intros A B t c1 c2 H1 H2. exfalso.
  exact (@sub_arrow_nat_false A B c1 H1).
Qed.

Lemma CohNat_rcd : forall l A t, CohNat (styp_rcd l A) t.
Proof.
  intros l A t c1 c2 H1 H2. exfalso.
  exact (@sub_rcd_nat_false l A c1 H1).
Qed.

Lemma CohNat_nat_lit : forall k, CohNat styp_nat (trm_lit k).
Proof.
  intros k c1 c2 H1 H2.
  apply (@E_nat_coerce (trm_lit k) (trm_lit k) c1 c2).
  - apply E_WF_self. simpl. exists k. reflexivity.
  - exact H1.
  - exact H2.
Qed.

Lemma CohNat_of_CohVal : forall A t, CohVal A t -> CohNat A t.
Proof. intros A t H c1 c2 H1 H2. exact (H styp_nat c1 c2 H1 H2). Qed.

Lemma binds_app_end : forall Γ x (A:styp) y (B:styp),
  binds x A Γ -> binds x A (Γ ++ [(y,B)]).
Proof.
  intros Γ. induction Γ as [| [z C] rest IH]; intros x A y B Hb.
  - simpl in Hb. inversion Hb.
  - simpl in Hb. apply binds_cons_1 in Hb.
    destruct Hb as [[Hxz HAC]|Htail].
    + subst x A. simpl. left. auto.
    + simpl. right. apply in_app_iff. left. exact Htail.
Qed.

Lemma EK_weaken_end : forall Γ A t1 t2,
  EK Γ A t1 t2 -> forall x B, EK (Γ ++ [(x,B)]) A t1 t2.
Proof.
  intros Γ A t1 t2 H. induction H; intros xx BB.
  - apply EK_top.
  - apply EK_nat.
  - apply EK_var. apply lk_app_end with (z:=xx) (B:=BB). exact H.
  - eapply EK_and.
    + exact H.
    + apply IHEK1.
    + apply IHEK2.
  - apply EK_rcd. apply IHEK.
  - apply EK_absc with (L:=L). intro y. intro Hy.
    specialize (H0 y Hy). rewrite <- app_assoc. apply H0.
  - apply EK_arrow with (x:=x).
    rewrite <- app_assoc. apply IHEK.
  - eapply EK_sub.
    + apply IHEK.
    + exact H0.
    + exact H1.
  - eapply EK_app.
    + apply IHEK1.
    + apply IHEK2.
  - apply EK_proj. apply IHEK.
Qed.


Lemma EK_weaken_list : forall Δ,
  forall Γ A t1 t2, EK Γ A t1 t2 -> EK (Γ ++ Δ) A t1 t2.
Proof.
  induction Δ as [|[x B] Δ' IH]; intros Γ A t1 t2 H.
  - rewrite app_nil_r. exact H.
  - replace (Γ ++ (x,B)::Δ') with ((Γ ++ [(x,B)]) ++ Δ')
      by (rewrite app_assoc; reflexivity).
    apply (IH (Γ ++ [(x,B)]) A t1 t2).
    apply EK_weaken_end with (x:=x) (B:=B). exact H.
Qed.


Lemma EK_weaken_nil : forall Δ A t1 t2,
  EK nil A t1 t2 -> EK Δ A t1 t2.
Proof.
  intros Δ A t1 t2 H. exact (@EK_weaken_list Δ nil A t1 t2 H).
Qed.

Lemma fv_open_rec_other : forall e k z x,
  z \in fv_exp e -> z <> x ->
  z \in fv_exp (open_exp_wrt_exp_rec k (trm_var_f x) e).
Proof.
  intros e. induction e; intros k z xx Hz Hneq; simpl in *.
  - fsetdec.
  - fsetdec.
  - fsetdec.
  - fsetdec.
  - apply IHe; assumption.
  - assert (Hzd : z \in fv_exp e1 \/ z \in fv_exp e2)
      by (apply AtomSetImpl.union_1 in Hz; exact Hz).
    destruct Hzd as [Hd|Hd].
    + assert (Hzz : z \in fv_exp (open_exp_wrt_exp_rec k (trm_var_f xx) e1))
        by (apply IHe1; [exact Hd | exact Hneq]).
      fsetdec.
    + assert (Hzz : z \in fv_exp (open_exp_wrt_exp_rec k (trm_var_f xx) e2))
        by (apply IHe2; [exact Hd | exact Hneq]).
      fsetdec.
  - assert (Hzd : z \in fv_exp e1 \/ z \in fv_exp e2)
      by (apply AtomSetImpl.union_1 in Hz; exact Hz).
    destruct Hzd as [Hd|Hd].
    + assert (Hzz : z \in fv_exp (open_exp_wrt_exp_rec k (trm_var_f xx) e1))
        by (apply IHe1; [exact Hd | exact Hneq]).
      fsetdec.
    + assert (Hzz : z \in fv_exp (open_exp_wrt_exp_rec k (trm_var_f xx) e2))
        by (apply IHe2; [exact Hd | exact Hneq]).
      fsetdec.
  - apply IHe; assumption.
  - apply IHe; assumption.
  - apply IHe; assumption.
Qed.

Lemma fv_close_rec_subset : forall e k x,
  fv_exp (close_exp_wrt_exp_rec k x e) [<=] fv_exp e.
Proof.
  intros e. induction e; intros k xx; simpl.
  - destruct (lt_ge_dec n k); simpl; intros z Hz; fsetdec.
  - destruct (xx == x) as [E|E]; simpl; intros z Hz; fsetdec.
  - intros z Hz; fsetdec.
  - intros z Hz; fsetdec.
  - apply IHe.
  - intros z Hz.
    assert (Hd : z \in fv_exp (close_exp_wrt_exp_rec k xx e1) \/
                z \in fv_exp (close_exp_wrt_exp_rec k xx e2))
      by (apply AtomSetImpl.union_1 in Hz; exact Hz).
    destruct Hd as [Hd|Hd].
    + specialize (IHe1 k xx). assert (Hzz : z \in fv_exp e1) by (apply IHe1; exact Hd). fsetdec.
    + specialize (IHe2 k xx). assert (Hzz : z \in fv_exp e2) by (apply IHe2; exact Hd). fsetdec.
  - intros z Hz.
    assert (Hd : z \in fv_exp (close_exp_wrt_exp_rec k xx e1) \/
                z \in fv_exp (close_exp_wrt_exp_rec k xx e2))
      by (apply AtomSetImpl.union_1 in Hz; exact Hz).
    destruct Hd as [Hd|Hd].
    + specialize (IHe1 k xx). assert (Hzz : z \in fv_exp e1) by (apply IHe1; exact Hd). fsetdec.
    + specialize (IHe2 k xx). assert (Hzz : z \in fv_exp e2) by (apply IHe2; exact Hd). fsetdec.
  - apply IHe.
  - apply IHe.
  - apply IHe.
Qed.


Lemma fv_close_rec_not_x : forall e k x,
  x \notin fv_exp (close_exp_wrt_exp_rec k x e).
Proof.
  intros e. induction e; intros k xx; simpl.
  - destruct (lt_ge_dec n k); simpl; fsetdec.
  - destruct (xx == x) as [E|E].
    + subst xx. simpl. fsetdec.
    + simpl. fsetdec.
  - fsetdec.
  - fsetdec.
  - apply IHe.
  - intro H. apply AtomSetImpl.union_1 in H. destruct H as [Hd1|Hd2].
    + exact (IHe1 k xx Hd1).
    + exact (IHe2 k xx Hd2).
  - intro H. apply AtomSetImpl.union_1 in H. destruct H as [Hd1|Hd2].
    + exact (IHe1 k xx Hd1).
    + exact (IHe2 k xx Hd2).
  - apply IHe.
  - apply IHe.
  - apply IHe.
Qed.

Lemma EK_fv_dom : forall Γ A t1 t2,
  EK Γ A t1 t2 ->
  fv_exp t1 [<=] dom Γ /\ fv_exp t2 [<=] dom Γ.
Proof.
  intros Γ A t1 t2 H. induction H.
  - simpl. split; fsetdec.
  - simpl. split; fsetdec.
  - simpl. split; intro z; intro Hz.
    + assert (z = x) by fsetdec. subst z. apply lk_dom with A; exact H.
    + assert (z = x) by fsetdec. subst z. apply lk_dom with A; exact H.
  - destruct IHEK1 as [HA1 HA2]. destruct IHEK2 as [HB1 HB2].
    simpl. split; intro z; intro Hz.
    + assert (Hzd : z \in fv_exp a1 \/ z \in fv_exp b1)
        by (apply AtomSetImpl.union_1 in Hz; exact Hz).
      destruct Hzd as [Hd|Hd]; [apply HA1 in Hd | apply HB1 in Hd]; exact Hd.
    + assert (Hzd : z \in fv_exp a2 \/ z \in fv_exp b2)
        by (apply AtomSetImpl.union_1 in Hz; exact Hz).
      destruct Hzd as [Hd|Hd]; [apply HA2 in Hd | apply HB2 in Hd]; exact Hd.
  - destruct IHEK as [HA1 HA2]. simpl. split; assumption.
  - destruct (atom_fresh (L \u dom Γ \u fv_exp e1 \u fv_exp e2)) as [x0 Hx0].
    assert (Hx0L : x0 \notin L) by fsetdec.
    assert (Hx0e1 : x0 \notin fv_exp e1) by fsetdec.
    assert (Hx0e2 : x0 \notin fv_exp e2) by fsetdec.
    destruct (H0 x0 Hx0L) as [HA1 HA2].
    simpl. split.
    + intro z. intro Hz.
      assert (Hzne : z <> x0) by (intro E; subst z; apply Hx0e1; exact Hz).
      assert (Hzopen : z \in fv_exp (open_exp_wrt_exp e1 (trm_var_f x0)))
        by (apply fv_open_rec_other; [exact Hz | exact Hzne]).
      apply HA1 in Hzopen.
      exact (@AtomSetImpl.add_3 (dom Γ) x0 z ltac:(intro E; apply Hzne; symmetry; exact E) Hzopen).
    + intro z. intro Hz.
      assert (Hzne : z <> x0) by (intro E; subst z; apply Hx0e2; exact Hz).
      assert (Hzopen : z \in fv_exp (open_exp_wrt_exp e2 (trm_var_f x0)))
        by (apply fv_open_rec_other; [exact Hz | exact Hzne]).
      apply HA2 in Hzopen.
      exact (@AtomSetImpl.add_3 (dom Γ) x0 z ltac:(intro E; apply Hzne; symmetry; exact E) Hzopen).
  - destruct IHEK as [HA1 HA2]. simpl. split.
    + intro z. intro Hz.
      assert (Hzin : z \in fv_exp e1) by (exact (fv_close_rec_subset e1 0 x z Hz)).
      assert (Hzx : z <> x)
        by (intro E; subst z; exact (@fv_close_rec_not_x e1 0 x Hz)).
      specialize (HA1 z Hzin). simpl in HA1.
      exact (@AtomSetImpl.add_3 (dom Γ) x z
               ltac:(intro E; apply Hzx; symmetry; exact E) HA1).
    + intro z. intro Hz.
      assert (Hzin : z \in fv_exp e2) by (exact (fv_close_rec_subset e2 0 x z Hz)).
      assert (Hzx : z <> x)
        by (intro E; subst z; exact (@fv_close_rec_not_x e2 0 x Hz)).
      specialize (HA2 z Hzin). simpl in HA2.
      exact (@AtomSetImpl.add_3 (dom Γ) x z
               ltac:(intro E; apply Hzx; symmetry; exact E) HA2).
  - destruct IHEK as [HA1 HA2]. simpl. split; assumption.
  - destruct IHEK1 as [Hf1 Hf2]. destruct IHEK2 as [Hg1 Hg2].
    simpl. split; intro z; intro Hz.
    + assert (Hzd : z \in fv_exp f1 \/ z \in fv_exp g1)
        by (apply AtomSetImpl.union_1 in Hz; exact Hz).
      destruct Hzd as [Hd|Hd]; [apply Hf1 in Hd | apply Hg1 in Hd]; exact Hd.
    + assert (Hzd : z \in fv_exp f2 \/ z \in fv_exp g2)
        by (apply AtomSetImpl.union_1 in Hz; exact Hz).
      destruct Hzd as [Hd|Hd]; [apply Hf2 in Hd | apply Hg2 in Hd]; exact Hd.
  - destruct IHEK as [HA1 HA2]. simpl. split; assumption.
Qed.


Definition EnvSub (Γ Δ:sctx) (σ1 σ2:var->exp) : Prop :=
  (forall y, lcg 0 (σ1 y) /\ lcg 0 (σ2 y)) /\
  (forall y, (σ1 y = trm_var_f y /\ σ2 y = trm_var_f y) \/
             (fv_exp (σ1 y) [<=] empty /\ fv_exp (σ2 y) [<=] empty)) /\
  (forall x A, lk Γ x = Some A ->
     (lk Δ x = Some A /\ σ1 x = trm_var_f x /\ σ2 x = trm_var_f x) \/
     EK nil A (σ1 x) (σ2 x)).

Lemma EnvSub_lc : forall Γ Δ σ1 σ2 y,
  EnvSub Γ Δ σ1 σ2 -> lcg 0 (σ1 y) /\ lcg 0 (σ2 y).
Proof. intros Γ Δ σ1 σ2 y [H _]. apply H. Qed.

Lemma EnvSub_at : forall Γ Δ σ1 σ2 x A,
  EnvSub Γ Δ σ1 σ2 -> lk Γ x = Some A ->
  (lk Δ x = Some A /\ σ1 x = trm_var_f x /\ σ2 x = trm_var_f x) \/
  EK nil A (σ1 x) (σ2 x).
Proof. intros Γ Δ σ1 σ2 x A [_ [_ H]]. apply H. Qed.

Lemma EnvSub_class : forall Γ Δ σ1 σ2 y,
  EnvSub Γ Δ σ1 σ2 ->
  (σ1 y = trm_var_f y /\ σ2 y = trm_var_f y) \/
  (fv_exp (σ1 y) [<=] empty /\ fv_exp (σ2 y) [<=] empty).
Proof. intros Γ Δ σ1 σ2 y [_ [H _]]. apply H. Qed.

Lemma EK_nil_closed : forall A u1 u2,
  EK nil A u1 u2 -> forall y, y \notin fv_exp u1 /\ y \notin fv_exp u2.
Proof.
  intros A u1 u2 H y. destruct (EK_fv_dom nil A u1 u2 H) as [H1 H2].
  split; intro Hy; [specialize (H1 y Hy)|specialize (H2 y Hy)];
    simpl in H1; simpl in H2;
    [fsetdec | fsetdec].
Qed.

Lemma EnvSub_extend : forall Γ Δ σ1 σ2 y A,
  EnvSub Γ Δ σ1 σ2 ->
  EnvSub ((y~A)++Γ) ((y~A)++Δ)
    (extend σ1 y (trm_var_f y)) (extend σ2 y (trm_var_f y)).
Proof.
  intros Γ Δ σ1 σ2 y A [Hlc [Hclas Hlk]]. split.
  - intro z. unfold extend.
    destruct (eq_var z y) as [E|E].
    + subst z. simpl. split; trivial.
    + apply Hlc.
  - split.
    + intro z. unfold extend.
      destruct (eq_var z y) as [E|E].
      * subst z. simpl. left. split; reflexivity.
      * apply Hclas.
    + {
      intros x B Hlk2. simpl in Hlk2.
    destruct (x == y) as [Exy|Exy].
    + inversion Hlk2. subst B.
      left. split; [|split].
      * simpl. destruct (x == y) as [E2|E2]; [reflexivity|contradiction].
      * unfold extend. destruct (x == y) as [E2|E2]; [(rewrite Exy; reflexivity)|contradiction].
      * unfold extend. destruct (x == y) as [E2|E2]; [(rewrite Exy; reflexivity)|contradiction].
    + destruct (Hlk x B Hlk2) as [[HD [Hs1 Hs2]]|HE].
      * left. split; [|split].
        -- simpl. destruct (x == y) as [E2|E2]; [exfalso; auto|exact HD].
        -- unfold extend. destruct (x == y) as [E2|E2]; [exfalso; auto|exact Hs1].
        -- unfold extend. destruct (x == y) as [E2|E2]; [exfalso; auto|exact Hs2].
      * right. unfold extend. destruct (x == y) as [E2|E2]; [exfalso; auto|exact HE].
      }
Qed.

Lemma EnvSub_head_closed : forall y A u1 u2,
  EK nil A u1 u2 ->
  EnvSub ((y~A)++nil) nil
    (extend (fun _ => trm_unit) y u1)
    (extend (fun _ => trm_unit) y u2).
Proof.
  intros y A u1 u2 HE. split.
  - intro z. unfold extend. destruct (eq_var z y) as [E|E].
    + subst z. destruct (EK_lc nil A u1 u2 HE) as [H1 H2].
      split; apply lc_lcg; assumption.
    + simpl. split; trivial.
  - split.
    + intro z. unfold extend. destruct (eq_var z y) as [E|E].
      * subst z. right. split; intro a; intro Ha; exfalso;
          [exact (proj1 (EK_nil_closed A u1 u2 HE a) Ha) |
           exact (proj2 (EK_nil_closed A u1 u2 HE a) Ha)].
      * simpl. right. split; intros a Ha; simpl in Ha; fsetdec.
    + {
      intros x B Hlk. simpl in Hlk.
    destruct (x == y) as [Exy|Exy].
    + inversion Hlk. subst B.
      right. unfold extend. destruct (x == y) as [E2|E2]; [exact HE|exfalso; auto].
    + simpl in Hlk. discriminate Hlk.
      }
Qed.

Lemma subst_env_congr : forall e sigma sigma',
  (forall y, sigma y = sigma' y) -> subst_env sigma e = subst_env sigma' e.
Proof.
  intros e. induction e; intros sigma sigma' H; simpl.
  - reflexivity.
  - apply H.
  - reflexivity.
  - reflexivity.
  - f_equal. apply IHe. exact H.
  - f_equal; [apply IHe1|apply IHe2]; exact H.
  - f_equal; [apply IHe1|apply IHe2]; exact H.
  - f_equal. apply IHe. exact H.
  - f_equal. apply IHe. exact H.
  - f_equal. apply IHe. exact H.
Qed.

Lemma subst_env_ignore : forall e sigma sigma' x,
  x \notin fv_exp e ->
  (forall y, y <> x -> sigma y = sigma' y) ->
  subst_env sigma e = subst_env sigma' e.
Proof.
  intros e. induction e; intros sigma sigma' xx Hx Heq; simpl in *.
  - reflexivity.
  - destruct (x == xx) as [E|E].
    + exfalso. apply Hx. subst x. simpl. fsetdec.
    + apply Heq. exact E.
  - reflexivity.
  - reflexivity.
  - f_equal. apply (IHe sigma sigma' xx Hx Heq).
  - assert (Hx1 : xx \notin fv_exp e1) by fsetdec.
    assert (Hx2 : xx \notin fv_exp e2) by fsetdec.
    f_equal. apply (IHe1 sigma sigma' xx Hx1 Heq).
    apply (IHe2 sigma sigma' xx Hx2 Heq).
  - assert (Hx1 : xx \notin fv_exp e1) by fsetdec.
    assert (Hx2 : xx \notin fv_exp e2) by fsetdec.
    f_equal. apply (IHe1 sigma sigma' xx Hx1 Heq).
    apply (IHe2 sigma sigma' xx Hx2 Heq).
  - f_equal. apply (IHe sigma sigma' xx Hx Heq).
  - f_equal. apply (IHe sigma sigma' xx Hx Heq).
  - f_equal. apply (IHe sigma sigma' xx Hx Heq).
Qed.

Lemma EnvSub_avoids : forall Γ Δ σ1 σ2 y x,
  EnvSub Γ Δ σ1 σ2 -> y <> x ->
  x \notin fv_exp (σ1 y) /\ x \notin fv_exp (σ2 y).
Proof.
  intros Γ Δ σ1 σ2 y xx Henv Hneq.
  destruct (EnvSub_class Γ Δ σ1 σ2 y Henv) as [[Hs1 Hs2]|[Hf1 Hf2]].
  - rewrite Hs1, Hs2. simpl. split; intro Hx; apply Hneq; symmetry; fsetdec.
  - split; intro Hx; [specialize (Hf1 xx Hx)|specialize (Hf2 xx Hx)];
      simpl in Hf1; simpl in Hf2; [fsetdec|fsetdec].
Qed.

Lemma subst_env_close_pair : forall e x Γ Δ σ1 σ2,
  EnvSub Γ Δ σ1 σ2 -> lcg 0 e ->
  (subst_env σ1 (close_exp_wrt_exp x e) =
   close_exp_wrt_exp x (subst_env (extend σ1 x (trm_var_f x)) e)) /\
  (subst_env σ2 (close_exp_wrt_exp x e) =
   close_exp_wrt_exp x (subst_env (extend σ2 x (trm_var_f x)) e)).
Proof.
  intros e x Γ Δ σ1 σ2 Henv Hlc. split.
  - transitivity (subst_env (extend σ1 x trm_unit) (close_exp_wrt_exp x e)).
    + apply subst_env_ignore with (x:=x).
      * apply fv_close_rec_not_x.
      * intros y Hy. unfold extend.
        destruct (y == x) as [E|E]; [contradiction|reflexivity].
    + transitivity (close_exp_wrt_exp x
          (subst_env (extend (extend σ1 x trm_unit) x (trm_var_f x)) e)).
      * apply subst_env_close_neq.
        -- exact Hlc.
        -- intro y. unfold extend.
           destruct (y == x) as [E|E]; [simpl; trivial | exact (proj1 (EnvSub_lc Γ Δ σ1 σ2 y Henv))].
        -- intros y Hy. unfold extend.
           destruct (y == x) as [E|E]; [contradiction|].
           exact (proj1 (EnvSub_avoids Γ Δ σ1 σ2 y x Henv Hy)).
      * f_equal. apply subst_env_congr. intro y. unfold extend.
        destruct (y == x) as [E|E]; [reflexivity|].
        simpl. destruct (y == x) as [E2|E2]; [contradiction|reflexivity].
  - transitivity (subst_env (extend σ2 x trm_unit) (close_exp_wrt_exp x e)).
    + apply subst_env_ignore with (x:=x).
      * apply fv_close_rec_not_x.
      * intros y Hy. unfold extend.
        destruct (y == x) as [E|E]; [contradiction|reflexivity].
    + transitivity (close_exp_wrt_exp x
          (subst_env (extend (extend σ2 x trm_unit) x (trm_var_f x)) e)).
      * apply subst_env_close_neq.
        -- exact Hlc.
        -- intro y. unfold extend.
           destruct (y == x) as [E|E]; [simpl; trivial | exact (proj2 (EnvSub_lc Γ Δ σ1 σ2 y Henv))].
        -- intros y Hy. unfold extend.
           destruct (y == x) as [E|E]; [contradiction|].
           exact (proj2 (EnvSub_avoids Γ Δ σ1 σ2 y x Henv Hy)).
      * f_equal. apply subst_env_congr. intro y. unfold extend.
        destruct (y == x) as [E|E]; [reflexivity|].
        simpl. destruct (y == x) as [E2|E2]; [contradiction|reflexivity].
Qed.

Lemma subst_env_open_val : forall ee sigma x u,
  x \notin fv_exp ee ->
  (forall y, lcg 0 (sigma y)) ->
  subst_env (extend sigma x u) (open_exp_wrt_exp ee (trm_var_f x)) =
  open_exp_wrt_exp (subst_env sigma ee) u.
Proof. intros ee sigma x u Hfv Hlc. exact (@subst_env_open_rec ee 0 sigma x u Hfv Hlc). Qed.

Lemma subst_env_open_exp : forall ee sigma x,
  x \notin fv_exp ee ->
  (forall y, lcg 0 (sigma y)) ->
  subst_env (extend sigma x (trm_var_f x)) (open_exp_wrt_exp ee (trm_var_f x)) =
  open_exp_wrt_exp (subst_env sigma ee) (trm_var_f x).
Proof. intros ee sigma x Hx Hlc. exact (@subst_env_open_rec ee 0 sigma x (trm_var_f x) Hx Hlc). Qed.

Lemma EK_subst : forall Γ A t1 t2,
  EK Γ A t1 t2 ->
  forall Δ σ1 σ2, EnvSub Γ Δ σ1 σ2 ->
  EK Δ A (subst_env σ1 t1) (subst_env σ2 t2).
Proof.
  intros Γ A t1 t2 H. induction H; intros Δ σ1 σ2 Henv.
  - simpl. apply EK_top.
  - simpl. apply EK_nat.
  - simpl. destruct (EnvSub_at Γ Δ σ1 σ2 x A Henv H)
      as [[HD [Hs1 Hs2]]|HE].
    + rewrite Hs1, Hs2. apply EK_var. exact HD.
    + apply EK_weaken_nil. exact HE.
  - simpl. eapply EK_and.
    + exact H.
    + apply IHEK1. exact Henv.
    + apply IHEK2. exact Henv.
  - simpl. apply EK_rcd. apply IHEK. exact Henv.
  - (* EK_absc *)
    simpl. eapply EK_absc with (L := L \u fv_exp e1 \u fv_exp e2).
    intros z Hz.
    assert (HzL : z \notin L) by fsetdec.
    assert (Hze1 : z \notin fv_exp e1) by fsetdec.
    assert (Hze2 : z \notin fv_exp e2) by fsetdec.
    pose proof (H0 z HzL ((z~A)++Δ)
      (extend σ1 z (trm_var_f z)) (extend σ2 z (trm_var_f z))
      (EnvSub_extend Γ Δ σ1 σ2 z A Henv)) as HB.
    rewrite (@subst_env_open_exp e1 σ1 z Hze1
               ltac:(intro y; exact (proj1 (EnvSub_lc Γ Δ σ1 σ2 y Henv))))
      in HB.
    rewrite (@subst_env_open_exp e2 σ2 z Hze2
               ltac:(intro y; exact (proj2 (EnvSub_lc Γ Δ σ1 σ2 y Henv))))
      in HB.
    exact HB.
  - (* EK_arrow *)
    simpl.
    destruct (EK_lc ((x~A)++Γ) B e1 e2 H) as [Hlc1 Hlc2].
    destruct (subst_env_close_pair e1 x Γ Δ σ1 σ2 Henv (lc_lcg e1 Hlc1))
      as [E1 E2].
    destruct (subst_env_close_pair e2 x Γ Δ σ1 σ2 Henv (lc_lcg e2 Hlc2))
      as [E3 E4].
    rewrite E1, E4.
    eapply EK_arrow with (x:=x).
    apply (IHEK ((x~A)++Δ)
      (extend σ1 x (trm_var_f x)) (extend σ2 x (trm_var_f x))).
    apply EnvSub_extend. exact Henv.
  - (* EK_sub *)
    simpl. eapply EK_sub.
    + apply IHEK. exact Henv.
    + exact H0.
    + exact H1.
  - (* EK_app *)
    simpl. eapply EK_app.
    + apply IHEK1. exact Henv.
    + apply IHEK2. exact Henv.
  - (* EK_proj *)
    simpl. apply EK_proj. apply IHEK. exact Henv.
Qed.

Fixpoint EKn (n:nat) (A:styp) (t1 t2:exp) : Prop :=
  match n with
  | 0 => True
  | S m =>
      (match A with
       | styp_top => (step star) t1 trm_unit /\ (step star) t2 trm_unit
       | styp_nat => exists k, (step star) t1 (trm_lit k) /\
                               (step star) t2 (trm_lit k)
       | styp_and A1 A2 =>
           exists a1 b1 a2 b2,
             (step star) t1 (trm_pair a1 b1) /\
             (step star) t2 (trm_pair a2 b2) /\
             EKn m A1 a1 a2 /\ EKn m A2 b1 b2
       | styp_rcd l A1 =>
           exists a1 a2,
             (step star) t1 (trm_rcd l a1) /\
             (step star) t2 (trm_rcd l a2) /\
             EKn m A1 a1 a2
       | styp_arrow A1 A2 =>
           forall u1 u2,
             EK nil A1 u1 u2 ->
             exists w1 w2,
               (step star) (trm_app t1 u1) w1 /\
               (step star) (trm_app t2 u2) w2 /\
               EKn m A2 w1 w2
       end)
      /\
      (forall C c1 c2,
         size_co c1 + size_co c2 + size_styp C <= m ->
         sub A C c1 -> sub A C c2 ->
         EKn m C (trm_capp c1 t1) (trm_capp c2 t2))
  end.

Lemma EKn_zero : forall A t1 t2, EKn 0 A t1 t2.
Proof. intros. simpl. trivial. Qed.

Lemma EKn_star_l : forall n A t t' u,
  (step star) t t' -> EKn n A t' u -> EKn n A t u.
Proof.
  intros n. induction n as [|m IH]; intros A t t' u Hred H.
  - simpl in *. trivial.
  - destruct A; simpl in *.
    + (* top *) destruct H as [[S1 S2] Hco]. split.
      * split; [eapply star_trans; eauto | exact S2].
      * intros C c1 c2 Hb Hs1 Hs2.
        eapply IH; [apply star_capp; exact Hred | apply Hco; assumption].
    + (* nat *) destruct H as [[k [S1 S2]] Hco]. split.
      * exists k. split; [eapply star_trans; eauto | exact S2].
      * intros C c1 c2 Hb Hs1 Hs2.
        eapply IH; [apply star_capp; exact Hred | apply Hco; assumption].
    + (* and *) destruct H as [[a1 [b1 [a2 [b2 [S1 [S2 [EA EB]]]]]]] Hco]. split.
      * exists a1, b1, a2, b2. repeat split; auto.
        eapply star_trans; eauto.
      * intros C c1 c2 Hb Hs1 Hs2.
        eapply IH; [apply star_capp; exact Hred | apply Hco; assumption].
    + (* arrow *) destruct H as [Happ Hco]. split.
      * intros u1 u2 HE.
        destruct (Happ u1 u2 HE) as [w1 [w2 [S1 [S2 EA]]]].
        exists w1, w2. split; [|split].
        -- eapply star_trans.
           ++ apply star_app_l; [exact Hred | exact (proj1 (EK_lc nil A1 u1 u2 HE))].
           ++ exact S1.
        -- exact S2.
        -- exact EA.
      * intros C c1 c2 Hb Hs1 Hs2.
        eapply IH; [apply star_capp; exact Hred | apply Hco; assumption].
    + (* rcd *) destruct H as [[a1 [a2 [S1 [S2 EA]]]] Hco]. split.
      * exists a1, a2. repeat split; auto.
        eapply star_trans; eauto.
      * intros C c1 c2 Hb Hs1 Hs2.
        eapply IH; [apply star_capp; exact Hred | apply Hco; assumption].
Qed.

Lemma EKn_star_r : forall n A t u u',
  (step star) u u' -> EKn n A t u' -> EKn n A t u.
Proof.
  intros n. induction n as [|m IH]; intros A t u u' Hred H.
  - simpl in *. trivial.
  - destruct A; simpl in *.
    + (* top *) destruct H as [[S1 S2] Hco]. split.
      * split; [exact S1 | eapply star_trans; eauto].
      * intros C c1 c2 Hb Hs1 Hs2.
        eapply IH; [apply star_capp; exact Hred | apply Hco; assumption].
    + (* nat *) destruct H as [[k [S1 S2]] Hco]. split.
      * exists k. split; [exact S1 | eapply star_trans; eauto].
      * intros C c1 c2 Hb Hs1 Hs2.
        eapply IH; [apply star_capp; exact Hred | apply Hco; assumption].
    + (* and *) destruct H as [[a1 [b1 [a2 [b2 [S1 [S2 [EA EB]]]]]]] Hco]. split.
      * exists a1, b1, a2, b2. repeat split; auto.
        eapply star_trans; eauto.
      * intros C c1 c2 Hb Hs1 Hs2.
        eapply IH; [apply star_capp; exact Hred | apply Hco; assumption].
    + (* arrow *) destruct H as [Happ Hco]. split.
      * intros u1 u2 HE.
        destruct (Happ u1 u2 HE) as [w1 [w2 [S1 [S2 EA]]]].
        exists w1, w2. split; [|split].
        -- exact S1.
        -- eapply star_trans.
           ++ apply star_app_l; [exact Hred | exact (proj2 (EK_lc nil A1 u1 u2 HE))].
           ++ exact S2.
        -- exact EA.
      * intros C c1 c2 Hb Hs1 Hs2.
        eapply IH; [apply star_capp; exact Hred | apply Hco; assumption].
    + (* rcd *) destruct H as [[a1 [a2 [S1 [S2 EA]]]] Hco]. split.
      * exists a1, a2. repeat split; auto.
        eapply star_trans; eauto.
      * intros C c1 c2 Hb Hs1 Hs2.
        eapply IH; [apply star_capp; exact Hred | apply Hco; assumption].
Qed.

Lemma sub_and_nat_reach_component : forall A B c,
  sub (styp_and A B) styp_nat c -> NatReach A \/ NatReach B.
Proof.
  intros A B c H.
  apply NatReach_and_inv.
  apply (@sub_nat_reach (styp_and A B) c H).
Qed.

Lemma NatReach_sub_nat : forall A, NatReach A -> exists c, sub A styp_nat c.
Proof.
  intros A H. induction H as [|A B HA IHA|A B HB IHB].
  - exists co_id. apply S_refl.
  - destruct IHA as [c Hc]. exists (co_trans c co_proj1).
    exact (S_trans (styp_and A B) styp_nat c co_proj1 A Hc (S_andl A B)).
  - destruct IHB as [c Hc]. exists (co_trans c co_proj2).
    exact (S_trans (styp_and A B) styp_nat c co_proj2 B Hc (S_andr A B)).
Qed.

Lemma NatReach_disjoint_exclusive : forall A B,
  disjoint A B -> NatReach A \/ NatReach B ->
  (NatReach A /\ ~ NatReach B) \/ (~ NatReach A /\ NatReach B).
Proof.
  intros A B HD [HA|HB].
  - left. split; [exact HA|]. intro HBr.
    exact (@disjoint_NatReach A B HD HA HBr).
  - right. split; [|exact HB]. intro HAr.
    exact (@disjoint_NatReach A B HD HAr HB).
Qed.

Lemma capp_trans_star : forall c1 c2 v,
  value v ->
  (step star) (trm_capp (co_trans c1 c2) v)
             (trm_capp c1 (trm_capp c2 v)).
Proof. intros. apply star1. apply step_trans. exact H. Qed.

Lemma capp_id_star : forall v, value v -> (step star) (trm_capp co_id v) v.
Proof. intros. apply star1. apply step_id. exact H. Qed.

Lemma capp_top_star : forall v, value v -> (step star) (trm_capp co_top v) trm_unit.
Proof. intros. apply star1. apply step_top. exact H. Qed.

Lemma capp_pair_star : forall c1 c2 v,
  value v ->
  (step star) (trm_capp (co_pair c1 c2) v)
             (trm_pair (trm_capp c1 v) (trm_capp c2 v)).
Proof. intros. apply star1. apply step_pair. exact H. Qed.

Lemma capp_arr_star : forall c1 c2 v1 v2,
  value v1 -> value v2 ->
  (step star) (trm_app (trm_capp (co_arr c1 c2) v1) v2)
             (trm_capp c2 (trm_app v1 (trm_capp c1 v2))).
Proof. intros. apply star1. apply step_arr; assumption. Qed.

Lemma capp_proj1_star : forall v1 v2,
  value v1 -> value v2 ->
  (step star) (trm_capp co_proj1 (trm_pair v1 v2)) v1.
Proof. intros. apply star1. apply step_projl; assumption. Qed.

Lemma capp_proj2_star : forall v1 v2,
  value v1 -> value v2 ->
  (step star) (trm_capp co_proj2 (trm_pair v1 v2)) v2.
Proof. intros. apply star1. apply step_projr; assumption. Qed.

(* Any well-formed value coerced to [top] reduces to [unit], independently
   of the particular coercion derivation. *)
Lemma capp_top_unit : forall A c, sub A styp_top c ->
  forall v, WF A v -> (step star) (trm_capp c v) trm_unit.
Proof.
  intros A c Hs. dependent induction Hs; intros v W.
  - simpl in W. subst. apply star1. apply step_id. constructor.
  - simpl.
    destruct (proj1 (@sub_coherent A1 A2 c2 Hs2) v W) as [w2 [S2 W2]].
    destruct (proj1 (@sub_coherent A2 styp_top c1 Hs1) w2 W2) as [w [S Ww]].
    eapply star_trans.
    * apply star1. apply step_trans. apply (@WF_value A1 v W).
    * eapply star_trans.
      -- apply star_capp. exact S2.
      -- simpl in Ww. subst w. exact S.
  - apply capp_top_star. apply (@WF_value A v W).
  - simpl in W. destruct W as [a [b [E [Wa Wb]]]]. subst v.
    simpl in Wa. subst a. apply capp_proj1_star; [constructor|exact (@WF_value A2 b Wb)].
  - simpl in W. destruct W as [a [b [E [Wa Wb]]]]. subst v.
    simpl in Wb. subst b. apply capp_proj2_star; [exact (@WF_value A1 a Wa)|constructor].
Qed.

Definition EnvVE (Γ:sctx) (σ1 σ2:var->exp) : Prop :=
  (forall x, lc_exp (σ1 x) /\ lc_exp (σ2 x)) /\
  EnvRelT V Γ σ1 σ2.

Lemma EnvVE_lc : forall Γ σ1 σ2 x,
  EnvVE Γ σ1 σ2 -> lc_exp (σ1 x) /\ lc_exp (σ2 x).
Proof. intros Γ σ1 σ2 x [H _]. apply H. Qed.

Lemma EnvVE_rel : forall Γ σ1 σ2 x A,
  EnvVE Γ σ1 σ2 -> binds x A Γ -> V A (σ1 x) (σ2 x).
Proof. intros Γ σ1 σ2 x A [_ H]. apply H. Qed.

Lemma EnvVE_extend : forall Γ σ1 σ2 x A u1 u2,
  EnvVE Γ σ1 σ2 -> uniq ((x~A)++Γ) -> V A u1 u2 ->
  EnvVE ((x~A)++Γ) (extend σ1 x u1) (extend σ2 x u2).
Proof.
  intros Γ σ1 σ2 x A u1 u2 [Hlc Hrel] Hu HV. split.
  - intro y. unfold extend.
    destruct (eq_var y x) as [E|E].
    + subst y. destruct HV as [W1 [W2 _]]. split; [apply (@WF_lc A u1 W1)|apply (@WF_lc A u2 W2)].
    + exact (Hlc y).
  - eapply (@EnvRelT_extend V Γ σ1 σ2 x A u1 u2).
    + exact Hrel.
    + exact Hu.
    + exact HV.
Qed.


Lemma EnvVE_self_l : forall Γ σ1 σ2,
  EnvVE Γ σ1 σ2 -> EnvVE Γ σ1 σ1.
Proof.
  intros Γ σ1 σ2 [Hlc Hrel]. split.
  - intro x. destruct (Hlc x) as [H1 H2]. split; assumption.
  - intros x A Hb. destruct (Hrel x A Hb) as [W1 [W2 AE12]].
    split; [exact W1|split; [exact W1|apply AE_refl; exact W1]].
Qed.

Lemma EnvVE_self_r : forall Γ σ1 σ2,
  EnvVE Γ σ1 σ2 -> EnvVE Γ σ2 σ2.
Proof.
  intros Γ σ1 σ2 [Hlc Hrel]. split.
  - intro x. destruct (Hlc x) as [H1 H2]. split; assumption.
  - intros x A Hb. destruct (Hrel x A Hb) as [W1 [W2 AE12]].
    split; [exact W2|split; [exact W2|apply AE_refl; exact W2]].
Qed.
Lemma has_type_E_self : forall Γ E0 dir A e,
  has_type Γ E0 dir A e ->
  forall σ1 σ2, EnvVE Γ σ1 σ2 ->
  E A (subst_env σ1 e) (subst_env σ2 e).
Proof.
  intros GG E0 dir A e Hty.
  induction Hty; intros σ1 σ2 Henv.
  - simpl. apply E_WF_self. simpl. reflexivity.
  - simpl. apply E_WF_self. simpl. exists i5. reflexivity.
  - simpl. apply E_V.
    + exact (proj1 (EnvVE_rel GG σ1 σ2 x A Henv H0)).
    + exact (proj1 (proj2 (EnvVE_rel GG σ1 σ2 x A Henv H0))).
    + exact (proj2 (proj2 (EnvVE_rel GG σ1 σ2 x A Henv H0))).
  - simpl. eapply E_app.
    + apply IHHty1. exact Henv.
    + apply IHHty2. exact Henv.
    + apply subst_env_lc; [apply has_type_lc in Hty2; exact Hty2 | intro x; exact (proj1 (EnvVE_lc GG σ1 σ2 x Henv))].
    + apply subst_env_lc; [apply has_type_lc in Hty2; exact Hty2 | intro x; exact (proj2 (EnvVE_lc GG σ1 σ2 x Henv))].
  - simpl. eapply E_pair.
    + apply IHHty1. exact Henv.
    + apply IHHty2. exact Henv.
    + apply subst_env_lc; [apply has_type_lc in Hty2; exact Hty2 | intro x; exact (proj1 (EnvVE_lc GG σ1 σ2 x Henv))].
    + apply subst_env_lc; [apply has_type_lc in Hty2; exact Hty2 | intro x; exact (proj2 (EnvVE_lc GG σ1 σ2 x Henv))].
  - simpl. apply E_rcd. apply IHHty. exact Henv.
  - simpl. apply E_proj. apply IHHty. exact Henv.
  - simpl. apply IHHty. exact Henv.
  - (* T_abs *)
    simpl.
    destruct (atom_fresh (L \u dom GG \u fv_exp e)) as [x0 Hx0].
    assert (HxL : x0 \notin L) by fsetdec.
    assert (Hxdom : x0 \notin dom GG) by fsetdec.
    assert (Hxvf : x0 \notin fv_exp e) by fsetdec.
    pose proof (has_type_uniq _ _ _ _ _ (H x0 HxL)) as HuBody.
    apply uniq_cons_1 in HuBody.
    assert (Huniq : uniq ((x0~A)++GG)).
    { apply uniq_push; [exact HuBody|exact Hxdom]. }
    pose proof (has_type_lc _ _ _ _ _ (H x0 HxL)) as HlcOpen.
    assert (HlcAbsE : lc_exp (trm_abs e)).
    { apply lc_trm_abs. intro y. apply (open_lc_any e x0 y). exact HlcOpen. }
    assert (Hlc1 : lc_exp (trm_abs (subst_env σ1 e))).
    { change (lc_exp (subst_env σ1 (trm_abs e))). apply subst_env_lc; [exact HlcAbsE|intro y; exact (proj1 (EnvVE_lc GG σ1 σ2 y Henv))]. }
    assert (Hlc2 : lc_exp (trm_abs (subst_env σ2 e))).
    { change (lc_exp (subst_env σ2 (trm_abs e))). apply subst_env_lc; [exact HlcAbsE|intro y; exact (proj2 (EnvVE_lc GG σ1 σ2 y Henv))]. }
    assert (WF1 : WF (styp_arrow A B) (trm_abs (subst_env σ1 e))).
    { split.
      - exact Hlc1.
      - split.
        + apply value_abs. exact Hlc1.
        + intros u1 u2 Wu1 Wu2 Au.
          pose (σu1 := extend σ1 x0 u1).
          pose (σu2 := extend σ1 x0 u2).
          assert (HenvU : EnvVE ((x0~A)++GG) σu1 σu2).
          { apply EnvVE_extend; [exact (EnvVE_self_l GG σ1 σ2 Henv)|exact Huniq|].
            exact (conj Wu1 (conj Wu2 Au)). }
          specialize (H0 x0 HxL σu1 σu2 HenvU). unfold σu1 in H0. unfold σu2 in H0.
          rewrite (@subst_env_open_val e σ1 x0 u1 Hxvf
                    ltac:(intro y; apply lc_lcg; exact (proj1 (EnvVE_lc GG σ1 σ2 y Henv)))) in H0.
          rewrite (@subst_env_open_val e σ1 x0 u2 Hxvf
                    ltac:(intro y; apply lc_lcg; exact (proj1 (EnvVE_lc GG σ1 σ2 y Henv)))) in H0.
          destruct H0 as [w1 [w2 [S1 [S2 [Ww1 [Ww2 AEw]]]]]].
          exists w1, w2. split; [|split].
          -- eapply star_trans.
             ++ apply star1. apply step_beta.
                ** exact Hlc1.
                ** exact (@WF_value A u1 Wu1).
             ++ exact S1.
          -- eapply star_trans.
             ++ apply star1. apply step_beta.
                ** exact Hlc1.
                ** exact (@WF_value A u2 Wu2).
             ++ exact S2.
          -- repeat split; assumption. }
    assert (WF2 : WF (styp_arrow A B) (trm_abs (subst_env σ2 e))).
    { split.
      - exact Hlc2.
      - split.
        + apply value_abs. exact Hlc2.
        + intros u1 u2 Wu1 Wu2 Au.
          pose (σu1 := extend σ2 x0 u1).
          pose (σu2 := extend σ2 x0 u2).
          assert (HenvU : EnvVE ((x0~A)++GG) σu1 σu2).
          { apply EnvVE_extend; [exact (EnvVE_self_r GG σ1 σ2 Henv)|exact Huniq|].
            exact (conj Wu1 (conj Wu2 Au)). }
          specialize (H0 x0 HxL σu1 σu2 HenvU). unfold σu1 in H0. unfold σu2 in H0.
          rewrite (@subst_env_open_val e σ2 x0 u1 Hxvf
                    ltac:(intro y; apply lc_lcg; exact (proj2 (EnvVE_lc GG σ1 σ2 y Henv)))) in H0.
          rewrite (@subst_env_open_val e σ2 x0 u2 Hxvf
                    ltac:(intro y; apply lc_lcg; exact (proj2 (EnvVE_lc GG σ1 σ2 y Henv)))) in H0.
          destruct H0 as [w1 [w2 [S1 [S2 [Ww1 [Ww2 AEw]]]]]].
          exists w1, w2. split; [|split].
          -- eapply star_trans.
             ++ apply star1. apply step_beta.
                ** exact Hlc2.
                ** exact (@WF_value A u1 Wu1).
             ++ exact S1.
          -- eapply star_trans.
             ++ apply star1. apply step_beta.
                ** exact Hlc2.
                ** exact (@WF_value A u2 Wu2).
             ++ exact S2.
          -- repeat split; assumption. }
    assert (AE12 : AE (styp_arrow A B) (trm_abs (subst_env σ1 e)) (trm_abs (subst_env σ2 e))).
    { repeat split; [exact Hlc1|exact Hlc2|apply value_abs; exact Hlc1|apply value_abs; exact Hlc2|].
      intros u1 u2 Wu1 Wu2 Au.
      pose (σu1 := extend σ1 x0 u1).
      pose (σu2 := extend σ2 x0 u2).
      assert (HenvU : EnvVE ((x0~A)++GG) σu1 σu2).
      { apply EnvVE_extend; [exact Henv|exact Huniq|].
        exact (conj Wu1 (conj Wu2 Au)). }
      specialize (H0 x0 HxL σu1 σu2 HenvU). unfold σu1 in H0. unfold σu2 in H0.
      rewrite (@subst_env_open_val e σ1 x0 u1 Hxvf
                ltac:(intro y; apply lc_lcg; exact (proj1 (EnvVE_lc GG σ1 σ2 y Henv)))) in H0.
      rewrite (@subst_env_open_val e σ2 x0 u2 Hxvf
                ltac:(intro y; apply lc_lcg; exact (proj2 (EnvVE_lc GG σ1 σ2 y Henv)))) in H0.
      destruct H0 as [w1 [w2 [S1 [S2 [Ww1 [Ww2 AEw]]]]]].
      exists w1, w2. split; [|split].
      - eapply star_trans.
        + apply star1. apply step_beta.
          * exact Hlc1.
          * exact (@WF_value A u1 Wu1).
        + exact S1.
      - eapply star_trans.
        + apply star1. apply step_beta.
          * exact Hlc2.
          * exact (@WF_value A u2 Wu2).
        + exact S2.
      - repeat split; assumption. }
    { apply (@E_V (styp_arrow A B)
             (trm_abs (subst_env σ1 e)) (trm_abs (subst_env σ2 e))).
      - exact WF1.
      - exact WF2.
      - exact AE12. }
  - (* T_sub *)
    simpl. apply (@capp_E B A c (subst_env σ1 e) (subst_env σ2 e) H).
    apply IHHty. exact Henv.
Qed.



Definition TopSub (C:styp) : Prop := exists c, sub styp_top C c.

Lemma TopSub_top : TopSub styp_top.
Proof. exists co_top. apply S_top. Qed.

Lemma TopSub_and_intro : forall C D,
  TopSub C -> TopSub D -> TopSub (styp_and C D).
Proof.
  intros C D [c1 H1] [c2 H2]. exists (co_pair c1 c2).
  exact (S_and styp_top C D c1 c2 H1 H2).
Qed.

Lemma TopSub_and_inv_l : forall C D,
  TopSub (styp_and C D) -> TopSub C.
Proof.
  intros C D [c H]. exists (co_trans co_proj1 c).
  exact (S_trans styp_top C co_proj1 c (styp_and C D) (S_andl C D) H).
Qed.

Lemma TopSub_and_inv_r : forall C D,
  TopSub (styp_and C D) -> TopSub D.
Proof.
  intros C D [c H]. exists (co_trans co_proj2 c).
  exact (S_trans styp_top D co_proj2 c (styp_and C D) (S_andr C D) H).
Qed.

Lemma TopSub_arrow : forall A B,
  TopSub B -> TopSub (styp_arrow A B).
Proof.
  intros A B [cB HB]. exists (co_trans (co_arr co_top cB) co_topArr).
  eapply S_trans with (A2:=styp_arrow styp_top styp_top).
  - exact (S_arr styp_top styp_top A B co_top cB (S_top A) HB).
  - apply S_topArr.
Qed.

Lemma TopSub_rcd_intro : forall l A,
  TopSub A -> TopSub (styp_rcd l A).
Proof.
  intros l A [cA HA]. exists (co_trans (co_rcd l cA) (co_topRcd l)).
  eapply S_trans with (A2:=styp_rcd l styp_top).
  - exact (S_rcd l styp_top A cA HA).
  - apply S_topRcd.
Qed.

Lemma TR_to_TopSub : forall A, TR A -> TopSub A.
Proof.
  induction A as [| |A1 IH1 A2 IH2|A1 IH1 A2 IH2|l A1 IH].
  - intros _. apply TopSub_top.
  - (* nat *) intro HTR. exfalso.
    pose proof (HTR (trm_lit 0) (trm_lit 1)
      ltac:(simpl; exists 0; reflexivity)
      ltac:(simpl; exists 1; reflexivity)) as HE.
    destruct HE as [v1 [v2 [S1 [S2 [W1 [W2 AE]]]]]].
    simpl in W1, W2, AE.
    destruct W1 as [k1 H1]. destruct W2 as [k2 H2]. subst v1 v2.
    assert (Hl1 : trm_lit k1 = trm_lit 0).
    { eapply (star_value_det (trm_lit 0) (trm_lit k1)); [exact S1|apply value_lit|apply star_refl|apply value_lit]. }
    assert (Hl2 : trm_lit k2 = trm_lit 1).
    { eapply (star_value_det (trm_lit 1) (trm_lit k2)); [exact S2|apply value_lit|apply star_refl|apply value_lit]. }
    injection Hl1 as Hk1. injection Hl2 as Hk2.
    destruct AE as [k [E1 E2]].
    assert (k1 = k2) by congruence. lia.
  - (* and *) intros HTR. apply TopSub_and_intro.
    + apply IH1. apply (@TR_and_l A1 A2 HTR).
    + apply IH2. apply (@TR_and_r A1 A2 HTR).
  - (* arrow *) intros HTR. apply TopSub_arrow.
    apply IH2. apply (@TR_arrow_cod A1 A2 HTR).
  - (* rcd *) intros HTR. apply TopSub_rcd_intro.
    apply IH. apply (@TR_rcd_content l A1 HTR).
Qed.

Lemma TopSub_rcd_inv : forall l A,
  TopSub (styp_rcd l A) -> TopSub A.
Proof.
  intros l A H.
  destruct H as [c Hc].
  apply TR_to_TopSub.
  apply (@TR_rcd_content l A).
  exact (@TR_of_sub_top (styp_rcd l A) c Hc).
Qed.

Lemma TopSub_arrow_cod : forall A B,
  TopSub (styp_arrow A B) -> TopSub B.
Proof.
  intros A B H.
  destruct H as [c Hc].
  apply TR_to_TopSub.
  apply (@TR_arrow_cod A B).
  exact (@TR_of_sub_top (styp_arrow A B) c Hc).
Qed.

Lemma TopSub_iff_TR : forall C, TopSub C <-> TR C.
Proof.
  intros C. split.
  - intros [c Hc]. exact (@TR_of_sub_top C c Hc).
  - apply TR_to_TopSub.
Qed.

CoInductive SR (A:styp) (t1 t2:exp) : Prop :=
| SR_top :
    A = styp_top ->
    (step star) t1 trm_unit ->
    (step star) t2 trm_unit ->
    (forall C c1 c2, sub A C c1 -> sub A C c2 ->
       SR C (trm_capp c1 t1) (trm_capp c2 t2)) ->
    SR A t1 t2
| SR_nat : forall k,
    A = styp_nat ->
    (step star) t1 (trm_lit k) ->
    (step star) t2 (trm_lit k) ->
    (forall C c1 c2, sub A C c1 -> sub A C c2 ->
       SR C (trm_capp c1 t1) (trm_capp c2 t2)) ->
    SR A t1 t2
| SR_and : forall A1 A2 a1 b1 a2 b2,
    A = styp_and A1 A2 ->
    (step star) t1 (trm_pair a1 b1) ->
    (step star) t2 (trm_pair a2 b2) ->
    SR A1 a1 a2 -> SR A2 b1 b2 ->
    (forall C c1 c2, sub A C c1 -> sub A C c2 ->
       SR C (trm_capp c1 t1) (trm_capp c2 t2)) ->
    SR A t1 t2
| SR_rcd : forall l A1 a1 a2,
    A = styp_rcd l A1 ->
    (step star) t1 (trm_rcd l a1) ->
    (step star) t2 (trm_rcd l a2) ->
    SR A1 a1 a2 ->
    (forall C c1 c2, sub A C c1 -> sub A C c2 ->
       SR C (trm_capp c1 t1) (trm_capp c2 t2)) ->
    SR A t1 t2
| SR_arrow : forall A1 A2,
    A = styp_arrow A1 A2 ->
    (forall u1 u2, EK nil A1 u1 u2 ->
       exists w1 w2,
         (step star) (trm_app t1 u1) w1 /\
         (step star) (trm_app t2 u2) w2 /\
         SR A2 w1 w2) ->
    (forall C c1 c2, sub A C c1 -> sub A C c2 ->
       SR C (trm_capp c1 t1) (trm_capp c2 t2)) ->
    SR A t1 t2.

CoFixpoint SR_star_l (A:styp) (t t' u:exp)
  (Hred: (step star) t t') (H: SR A t' u) : SR A t u :=
  match H with
  | SR_top _ _ _ E S1 S2 Coh =>
      SR_top A t u E
        (@star_trans step _ _ _ Hred S1) S2
        (fun C c1 c2 Hs1 Hs2 =>
           SR_star_l C (trm_capp c1 t) (trm_capp c1 t') (trm_capp c2 u)
             (star_capp c1 t t' Hred) (Coh C c1 c2 Hs1 Hs2))
  | SR_nat _ _ _ k E S1 S2 Coh =>
      SR_nat A t u k E
        (@star_trans step _ _ _ Hred S1) S2
        (fun C c1 c2 Hs1 Hs2 =>
           SR_star_l C (trm_capp c1 t) (trm_capp c1 t') (trm_capp c2 u)
             (star_capp c1 t t' Hred) (Coh C c1 c2 Hs1 Hs2))
  | SR_and _ _ _ A1 A2 a1 b1 a2 b2 E S1 S2 XA XB Coh =>
      SR_and A t u A1 A2 a1 b1 a2 b2 E
        (@star_trans step _ _ _ Hred S1) S2 XA XB
        (fun C c1 c2 Hs1 Hs2 =>
           SR_star_l C (trm_capp c1 t) (trm_capp c1 t') (trm_capp c2 u)
             (star_capp c1 t t' Hred) (Coh C c1 c2 Hs1 Hs2))
  | SR_rcd _ _ _ l A1 a1 a2 E S1 S2 XA Coh =>
      SR_rcd A t u l A1 a1 a2 E
        (@star_trans step _ _ _ Hred S1) S2 XA
        (fun C c1 c2 Hs1 Hs2 =>
           SR_star_l C (trm_capp c1 t) (trm_capp c1 t') (trm_capp c2 u)
             (star_capp c1 t t' Hred) (Coh C c1 c2 Hs1 Hs2))
  | SR_arrow _ _ _ A1 A2 E App Coh =>
      SR_arrow A t u A1 A2 E
        (fun u1 u2 Hu =>
           match App u1 u2 Hu with
           | ex_intro _ w1 (ex_intro _ w2 (conj S1 (conj S2 SRw))) =>
               ex_intro _ w1 (ex_intro _ w2
                 (conj (@star_trans step _ _ _ (star_app_l t t' u1 Hred (proj1 (EK_lc nil A1 u1 u2 Hu))) S1)
                       (conj S2 SRw)))
           end)
        (fun C c1 c2 Hs1 Hs2 =>
           SR_star_l C (trm_capp c1 t) (trm_capp c1 t') (trm_capp c2 u)
             (star_capp c1 t t' Hred) (Coh C c1 c2 Hs1 Hs2))
  end.

CoFixpoint SR_star_r (A:styp) (t u u':exp)
  (Hred: (step star) u u') (H: SR A t u') : SR A t u :=
  match H with
  | SR_top _ _ _ E S1 S2 Coh =>
      SR_top A t u E S1
        (@star_trans step _ _ _ Hred S2)
        (fun C c1 c2 Hs1 Hs2 =>
           SR_star_r C (trm_capp c1 t) (trm_capp c2 u) (trm_capp c2 u')
             (star_capp c2 u u' Hred) (Coh C c1 c2 Hs1 Hs2))
  | SR_nat _ _ _ k E S1 S2 Coh =>
      SR_nat A t u k E S1
        (@star_trans step _ _ _ Hred S2)
        (fun C c1 c2 Hs1 Hs2 =>
           SR_star_r C (trm_capp c1 t) (trm_capp c2 u) (trm_capp c2 u')
             (star_capp c2 u u' Hred) (Coh C c1 c2 Hs1 Hs2))
  | SR_and _ _ _ A1 A2 a1 b1 a2 b2 E S1 S2 XA XB Coh =>
      SR_and A t u A1 A2 a1 b1 a2 b2 E S1
        (@star_trans step _ _ _ Hred S2) XA XB
        (fun C c1 c2 Hs1 Hs2 =>
           SR_star_r C (trm_capp c1 t) (trm_capp c2 u) (trm_capp c2 u')
             (star_capp c2 u u' Hred) (Coh C c1 c2 Hs1 Hs2))
  | SR_rcd _ _ _ l A1 a1 a2 E S1 S2 XA Coh =>
      SR_rcd A t u l A1 a1 a2 E S1
        (@star_trans step _ _ _ Hred S2) XA
        (fun C c1 c2 Hs1 Hs2 =>
           SR_star_r C (trm_capp c1 t) (trm_capp c2 u) (trm_capp c2 u')
             (star_capp c2 u u' Hred) (Coh C c1 c2 Hs1 Hs2))
  | SR_arrow _ _ _ A1 A2 E App Coh =>
      SR_arrow A t u A1 A2 E
        (fun u1 u2 Hu =>
           match App u1 u2 Hu with
           | ex_intro _ w1 (ex_intro _ w2 (conj S1 (conj S2 SRw))) =>
               ex_intro _ w1 (ex_intro _ w2
                 (conj S1
                       (conj (@star_trans step _ _ _ (star_app_l u u' u2 Hred (proj2 (EK_lc nil A1 u1 u2 Hu))) S2)
                             SRw)))
           end)
        (fun C c1 c2 Hs1 Hs2 =>
           SR_star_r C (trm_capp c1 t) (trm_capp c2 u) (trm_capp c2 u')
             (star_capp c2 u u' Hred) (Coh C c1 c2 Hs1 Hs2))
  end.

Lemma lk_nil_none : forall x A, lk (@nil (atom*styp)) x = Some A -> False.
Proof. intros. simpl in H. discriminate H. Qed.

Lemma open_close_rec_subst_any : forall e k x u,
  open_exp_wrt_exp_rec k u (close_exp_wrt_exp_rec k x e) =
  subst_env (fun z => if z == x then u else trm_var_f z) e.
Proof.
  intros e. induction e; intros k xx uu; simpl.
  - (* var_b *) destruct k as [|k'].
    + simpl. replace (n - 0) with n by lia. reflexivity.
    + destruct (lt_ge_dec n (S k')) as [Hlt|Hge].
      * simpl. destruct (lt_eq_lt_dec n (S k')) as [[H1|H1]|H1].
        -- reflexivity.
        -- lia.
        -- lia.
      * simpl. destruct (lt_eq_lt_dec (S n) (S k')) as [[H1|H1]|H1].
        -- lia.
        -- lia.
        -- cbn [Nat.sub].
           destruct (lt_eq_lt_dec n k') as [[H2|H2]|H2].
           ++ lia.
           ++ lia.
           ++ replace (n - 0) with n by lia. reflexivity.
  - (* var_f *) simpl.
    destruct (xx == x) as [Heq|Hne].
    + subst xx. simpl.
      destruct (x == x) as [Ex|Ex]; [|exfalso; auto].
      destruct (lt_eq_lt_dec k k) as [[H1|H1]|H1]; [lia| |lia].
      reflexivity.
    + simpl. destruct (xx == x) as [Heq|Hne']; [exfalso; auto|].
      destruct (x == xx) as [E2|E2]; [exfalso; auto|reflexivity].
  - reflexivity.
  - reflexivity.
  - rewrite (IHe (S k) xx uu). reflexivity.
  - rewrite (IHe1 k xx uu). rewrite (IHe2 k xx uu). reflexivity.
  - rewrite (IHe1 k xx uu). rewrite (IHe2 k xx uu). reflexivity.
  - rewrite (IHe k xx uu). reflexivity.
  - rewrite (IHe k xx uu). reflexivity.
  - rewrite (IHe k xx uu). reflexivity.
Qed.

Lemma open_close_subst_any : forall e x u,
  open_exp_wrt_exp (close_exp_wrt_exp x e) u =
  subst_env (fun z => if z == x then u else trm_var_f z) e.
Proof. intros. apply open_close_rec_subst_any. Qed.

Lemma subst_env_congr_fv : forall e sigma sigma',
  (forall y, y \in fv_exp e -> sigma y = sigma' y) ->
  subst_env sigma e = subst_env sigma' e.
Proof.
  intros e. induction e; intros sigma sigma' H; simpl in *.
  - reflexivity.
  - apply H. simpl. fsetdec.
  - reflexivity.
  - reflexivity.
  - f_equal. apply IHe. exact H.
  - f_equal.
    + apply IHe1. intro y. intro Hy. apply H. fsetdec.
    + apply IHe2. intro y. intro Hy. apply H. fsetdec.
  - f_equal.
    + apply IHe1. intro y. intro Hy. apply H. fsetdec.
    + apply IHe2. intro y. intro Hy. apply H. fsetdec.
  - f_equal. apply IHe. exact H.
  - f_equal. apply IHe. exact H.
  - f_equal. apply IHe. exact H.
Qed.

Lemma subst_env_single_free : forall e x u,
  (forall y, y \in fv_exp e -> y = x) ->
  subst_env (extend (fun _ => trm_unit) x u) e =
  subst_env (fun z => if z == x then u else trm_var_f z) e.
Proof.
  intros e x u H.
  apply subst_env_congr_fv. intros y Hy.
  unfold extend. destruct (y == x) as [E|E]; [reflexivity|].
  exfalso. exact (E (H y Hy)).
Qed.

Lemma SR_coher : forall A t1 t2,
  SR A t1 t2 ->
  forall C c1 c2, sub A C c1 -> sub A C c2 ->
  SR C (trm_capp c1 t1) (trm_capp c2 t2).
Proof.
  intros A t1 t2 S. destruct S; eauto.
Qed.

Lemma SR_top_inv : forall t1 t2,
  SR styp_top t1 t2 ->
  (step star) t1 trm_unit /\ (step star) t2 trm_unit /\
  (forall C c1 c2, sub styp_top C c1 -> sub styp_top C c2 ->
     SR C (trm_capp c1 t1) (trm_capp c2 t2)).
Proof.
  intros t1 t2 S. destruct S as [E S1 S2 Coh|k E S1 S2 Coh|A B a1 b1 a2 b2 E S1 S2 XA XB Coh|l A a1 a2 E S1 S2 XA Coh|A B E App Coh].
  - repeat split; assumption.
  - exfalso; discriminate E.
  - exfalso; discriminate E.
  - exfalso; discriminate E.
  - exfalso; discriminate E.
Qed.

Lemma SR_nat_inv : forall t1 t2,
  SR styp_nat t1 t2 ->
  exists k, (step star) t1 (trm_lit k) /\ (step star) t2 (trm_lit k) /\
  (forall C c1 c2, sub styp_nat C c1 -> sub styp_nat C c2 ->
     SR C (trm_capp c1 t1) (trm_capp c2 t2)).
Proof.
  intros t1 t2 S. destruct S as [E S1 S2 Coh|k E S1 S2 Coh|A B a1 b1 a2 b2 E S1 S2 XA XB Coh|l A a1 a2 E S1 S2 XA Coh|A B E App Coh].
  - exfalso; discriminate E.
  - exists k. repeat split; assumption.
  - exfalso; discriminate E.
  - exfalso; discriminate E.
  - exfalso; discriminate E.
Qed.

Lemma SR_and_inv : forall A B t1 t2,
  SR (styp_and A B) t1 t2 ->
  exists a1 b1 a2 b2,
    (step star) t1 (trm_pair a1 b1) /\
    (step star) t2 (trm_pair a2 b2) /\
    SR A a1 a2 /\ SR B b1 b2 /\
    (forall C c1 c2, sub (styp_and A B) C c1 -> sub (styp_and A B) C c2 ->
       SR C (trm_capp c1 t1) (trm_capp c2 t2)).
Proof.
  intros A B t1 t2 S. destruct S as [E S1 S2 Coh|k E S1 S2 Coh|A1 A2 a1 b1 a2 b2 E S1 S2 XA XB Coh|l A1 a1 a2 E S1 S2 XA Coh|A1 A2 E App Coh].
  - exfalso; discriminate E.
  - exfalso; discriminate E.
  - injection E as HA HB. subst A1 A2.
    exists a1, b1, a2, b2. repeat split; assumption.
  - exfalso; discriminate E.
  - exfalso; discriminate E.
Qed.

Lemma SR_rcd_inv : forall l A t1 t2,
  SR (styp_rcd l A) t1 t2 ->
  exists a1 a2,
    (step star) t1 (trm_rcd l a1) /\
    (step star) t2 (trm_rcd l a2) /\
    SR A a1 a2 /\
    (forall C c1 c2, sub (styp_rcd l A) C c1 -> sub (styp_rcd l A) C c2 ->
       SR C (trm_capp c1 t1) (trm_capp c2 t2)).
Proof.
  intros l A t1 t2 S. destruct S as [E S1 S2 Coh|k E S1 S2 Coh|A1 A2 a1 b1 a2 b2 E S1 S2 XA XB Coh|l0 A1 a1 a2 E S1 S2 XA Coh|A1 A2 E App Coh].
  - exfalso; discriminate E.
  - exfalso; discriminate E.
  - exfalso; discriminate E.
  - injection E as Hl HA. subst l0. subst A1.
    exists a1, a2. repeat split; assumption.
  - exfalso; discriminate E.
Qed.

Lemma SR_arrow_inv : forall A B t1 t2,
  SR (styp_arrow A B) t1 t2 ->
  (forall u1 u2, EK nil A u1 u2 ->
     exists w1 w2, (step star) (trm_app t1 u1) w1 /\
       (step star) (trm_app t2 u2) w2 /\ SR B w1 w2) /\
  (forall C c1 c2, sub (styp_arrow A B) C c1 -> sub (styp_arrow A B) C c2 ->
     SR C (trm_capp c1 t1) (trm_capp c2 t2)).
Proof.
  intros A B t1 t2 S. destruct S as [E S1 S2 Coh|k E S1 S2 Coh|A1 A2 a1 b1 a2 b2 E S1 S2 XA XB Coh|l A1 a1 a2 E S1 S2 XA Coh|A1 A2 E App Coh].
  - exfalso; discriminate E.
  - exfalso; discriminate E.
  - exfalso; discriminate E.
  - exfalso; discriminate E.
  - injection E as HA HB. subst A1 A2.
    split; assumption.
Qed.

Lemma subst_env_open_rec_closed : forall e k x u,
  fv_exp e [<=] empty ->
  subst_env (fun z => if z == x then u else trm_var_f z)
            (open_exp_wrt_exp_rec k (trm_var_f x) e) =
  open_exp_wrt_exp_rec k u e.
Proof.
  intros e. induction e; intros k xx uu H; simpl in *.
  - (* var_b *) destruct (lt_eq_lt_dec n k) as [[H1|H1]|H1].
    + reflexivity.
    + subst n. simpl.
      destruct (xx == xx) as [E|E]; [reflexivity|exfalso; auto].
    + reflexivity.
  - (* var_f *) exfalso.
    assert (Hx : x \in empty) by (apply (H x); fsetdec). fsetdec.
  - reflexivity.
  - reflexivity.
  - f_equal. apply IHe. exact H.
  - f_equal.
    + apply IHe1. intros y Hy. apply H. fsetdec.
    + apply IHe2. intros y Hy. apply H. fsetdec.
  - f_equal.
    + apply IHe1. intros y Hy. apply H. fsetdec.
    + apply IHe2. intros y Hy. apply H. fsetdec.
  - f_equal. apply IHe. exact H.
  - f_equal. apply IHe. exact H.
  - f_equal. apply IHe. exact H.
Qed.

Lemma subst_env_open_single : forall e x u,
  fv_exp e [<=] empty ->
  subst_env (fun z => if z == x then u else trm_var_f z)
            (open_exp_wrt_exp e (trm_var_f x)) =
  open_exp_wrt_exp e u.
Proof. intros. apply subst_env_open_rec_closed. exact H. Qed.

Lemma sub_to_and_l : forall X C D c,
  sub X (styp_and C D) c -> exists d, sub X C d.
Proof.
  intros X C D c H. dependent induction H.
  - exists co_proj1. apply S_andl.
  - destruct (IHsub1 C D eq_refl) as [d Hd].
    exists (co_trans d c2). exact (S_trans A1 C d c2 A2 Hd H0).
  - exists c1. exact H.
  - exists (co_trans co_proj1 co_proj1).
    eapply S_trans with (A2:=styp_and C D); [apply S_andl|apply S_andl].
  - exists (co_trans co_proj1 co_proj2).
    eapply S_trans with (A2:=styp_and C D); [apply S_andl|apply S_andr].
Qed.

Lemma sub_to_and_r : forall X C D c,
  sub X (styp_and C D) c -> exists d, sub X D d.
Proof.
  intros X C D c H. dependent induction H.
  - exists co_proj2. apply S_andr.
  - destruct (IHsub1 C D eq_refl) as [d Hd].
    exists (co_trans d c2). exact (S_trans A1 D d c2 A2 Hd H0).
  - exists c2. exact H0.
  - exists (co_trans co_proj2 co_proj1).
    eapply S_trans with (A2:=styp_and C D); [apply S_andr|apply S_andl].
  - exists (co_trans co_proj2 co_proj2).
    eapply S_trans with (A2:=styp_and C D); [apply S_andr|apply S_andr].
Qed.

Lemma sub_and_nat_component_exists : forall A B c,
  sub (styp_and A B) styp_nat c ->
  (exists d, sub A styp_nat d) \/ (exists d, sub B styp_nat d).
Proof.
  intros A B c H.
  destruct (@sub_and_nat_reach_component A B c H) as [HA|HB].
  - left. apply NatReach_sub_nat. exact HA.
  - right. apply NatReach_sub_nat. exact HB.
Qed.

Lemma TopSub_and_iff : forall C D,
  TopSub (styp_and C D) <-> TopSub C /\ TopSub D.
Proof.
  intros C D. split.
  - intros H. split; [apply TopSub_and_inv_l with (D:=D)|apply TopSub_and_inv_r with (C:=C)]; exact H.
  - intros [H1 H2]. apply TopSub_and_intro; assumption.
Qed.

Lemma TopSub_rcd_iff : forall l A,
  TopSub (styp_rcd l A) <-> TopSub A.
Proof.
  intros l A. split; [apply TopSub_rcd_inv|apply TopSub_rcd_intro].
Qed.

Lemma TopSub_arrow_iff : forall A B,
  TopSub (styp_arrow A B) <-> TopSub B.
Proof.
  intros A B. split; [apply TopSub_arrow_cod|apply TopSub_arrow].
Qed.

Lemma TopSub_nat_false : TopSub styp_nat -> False.
Proof. intros [c H]. exact (@sub_top_nat_false c H). Qed.

Definition ctx_equiv Γ E1 E2 A := forall e1 e2 dir dir' C c,
    has_type Γ E1 dir A e1 ->
    has_type Γ E2 dir A e2 ->
    CTyp C Γ dir A nil dir' styp_nat c ->
    kleene_equiv (appctx c e1) (appctx c e2).

Theorem coherence_thm : forall Γ E A,
    ctx_equiv Γ E E A.
