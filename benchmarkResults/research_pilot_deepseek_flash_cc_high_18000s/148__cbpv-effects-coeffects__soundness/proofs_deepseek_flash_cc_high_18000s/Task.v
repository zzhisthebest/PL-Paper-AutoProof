Require Import full.CBPV.semantics.
Require Import full.CBPV.typing.

Set Implicit Arguments.

(* ================= shapes ================= *)

Fixpoint VShape (A : ValTy) : VClos -> Prop :=
  match A with
  | VUnit => fun W => W = VClosUnit
  | VThunk ϕ B => fun W =>
      exists m γ ρ M, W = VClosThunk m γ ρ M /\
        (exists T' ϕ' ψ', EvalComp γ ρ M T' ϕ' /\ CShape B T' ψ' /\ subeff (ϕ' E+ ψ') ϕ)
  | VPair A1 A2 => fun W =>
      exists W1 W2, W = VClosPair W1 W2 /\ VShape A1 W1 /\ VShape A2 W2
  | VSum A1 A2 => fun W =>
      (exists W1, W = VClosInl W1 /\ VShape A1 W1) \/
      (exists W2, W = VClosInr W2 /\ VShape A2 W2)
  end
with CShape (B : CompTy) : CClos -> E -> Prop :=
  match B with
  | CAbs q A B' => fun T ψ =>
      exists m γ ρ M, T = CClosAbs m q γ ρ M /\
        (forall W, (q = Qzero \/ VShape A W) ->
           exists T' ϕ' ψ', EvalComp (q .: γ) (W .: ρ) M T' ϕ' /\
             CShape B' T' ψ' /\ subeff (ϕ' E+ ψ') ψ)
  | CF q A => fun T ψ =>
      ψ = ϵ /\ exists W, T = CClosRet q W /\
        (VShape A W \/ (W = JUNK /\ q = Qzero))
  | CPair B1 B2 => fun T ψ =>
      exists m γ ρ M1 M2 ψ1 ψ2,
        T = CClosPair m γ ρ M1 M2 /\
        subeff ψ1 ψ /\ subeff ψ2 ψ /\
        (exists T1 ϕ1 ψ1', EvalComp γ ρ M1 T1 ϕ1 /\ CShape B1 T1 ψ1' /\ subeff (ϕ1 E+ ψ1') ψ1) /\
        (exists T2 ϕ2 ψ2', EvalComp γ ρ M2 T2 ϕ2 /\ CShape B2 T2 ψ2' /\ subeff (ϕ2 E+ ψ2') ψ2)
  end.

Definition EnvRel {n} (γ : gradeVec n) (Γ : context n) (ρ : env n) : Prop :=
  forall i, γ i = Qzero \/ VShape (Γ i) (ρ i).

(* ================= basic Q lemmas ================= *)

Lemma Qle_zero_eq : forall q, Qle Qzero q -> q = Qzero.
Proof.
  intros q H.
  assert (H' : Qle Qzero (Qadd q Qzero)) by (rewrite Qadd_rident; exact H).
  exact (proj1 (Qsumzero q Qzero H')).
Qed.

Lemma Qadd_eq_zero_l : forall a b, Qadd a b = Qzero -> a = Qzero.
Proof. intros a b H. assert (H' : Qle Qzero (Qadd a b)) by (rewrite H; apply Qle_refl). exact (proj1 (Qsumzero a b H')). Qed.

Lemma Qadd_eq_zero_r : forall a b, Qadd a b = Qzero -> b = Qzero.
Proof. intros a b H. assert (H' : Qle Qzero (Qadd a b)) by (rewrite H; apply Qle_refl). exact (proj2 (Qsumzero a b H')). Qed.

Lemma Qmult_eq_zero_l : forall a b, Qmult a b = Qzero -> a <> Qzero -> b = Qzero.
Proof.
  intros a b H Hn. destruct (Qprodzero a b H) as [H1|H1]; auto. exfalso. auto.
Qed.

Lemma Qmult_eq_zero_r : forall a b, Qmult a b = Qzero -> b <> Qzero -> a = Qzero.
Proof.
  intros a b H Hn. destruct (Qprodzero a b H) as [H1|H1]; auto. exfalso. auto.
Qed.

Lemma Qle_zero_Qone_False : Qle Qzero Qone -> False.
Proof. intro H. apply Qnontrivial. apply Qle_zero_eq. exact H. Qed.

Lemma Qle_Qone_ne_zero : forall q, Qle q Qone -> q <> Qzero.
Proof. intros q H Heq. subst q. apply Qle_zero_Qone_False. exact H. Qed.

Lemma Qeqb_true : forall a b, Qeqb a b = true -> a = b.
Proof. intros a b H. apply (proj2 (Qeqb_eq a b)). exact H. Qed.

Lemma Qeqb_false : forall a b, Qeqb a b = false -> a <> b.
Proof. intros a b H Heq. assert (Ht := proj1 (Qeqb_eq a b) Heq). rewrite H in Ht. discriminate. Qed.

Lemma q_or_1_nonzero : forall q, q_or_1 q <> Qzero.
Proof.
  intros q. unfold q_or_1. destruct (Qeqb q Qzero) eqn:E.
  - apply Qnontrivial.
  - apply Qeqb_false. exact E.
Qed.

(* ================= effect lemmas ================= *)

Lemma subeff_idL : forall ϕ, subeff (ϵ E+ ϕ) ϕ.
Proof. intro ϕ. rewrite eff_idL. apply subeff_refl. Qed.

Lemma subeff_idR : forall ϕ, subeff (ϕ E+ ϵ) ϕ.
Proof. intro ϕ. rewrite eff_idR. apply subeff_refl. Qed.

Lemma subeff_add_congr : forall a a' b b', subeff a a' -> subeff b b' -> subeff (a E+ b) (a' E+ b').
Proof.
  intros a a' b b' Ha Hb. eapply subeff_trans.
  - apply subeff_add_right_compatible. exact Ha.
  - apply subeff_add_left_compatible. exact Hb.
Qed.

(* ================= EnvRel lemmas ================= *)

Lemma EnvRel_add_l : forall n (γ1 γ2 : gradeVec n) Γ ρ, EnvRel (γ1 Q+ γ2) Γ ρ -> EnvRel γ1 Γ ρ.
Proof.
  intros n γ1 γ2 Γ ρ H i. specialize (H i). simpl in H.
  destruct H as [H|H]; [left | right].
  - apply Qadd_eq_zero_l with (b := γ2 i). exact H.
  - exact H.
Qed.

Lemma EnvRel_add_r : forall n (γ1 γ2 : gradeVec n) Γ ρ, EnvRel (γ1 Q+ γ2) Γ ρ -> EnvRel γ2 Γ ρ.
Proof.
  intros n γ1 γ2 Γ ρ H i. specialize (H i). simpl in H.
  destruct H as [H|H]; [left | right].
  - apply Qadd_eq_zero_r with (a := γ1 i). exact H.
  - exact H.
Qed.

Lemma EnvRel_scale : forall n q (γ : gradeVec n) Γ ρ, q <> Qzero -> EnvRel (q Q* γ) Γ ρ -> EnvRel γ Γ ρ.
Proof.
  intros n q γ Γ ρ Hq H i. specialize (H i). simpl in H.
  destruct H as [H|H]; [left | right].
  - apply Qmult_eq_zero_l with (a := q); auto.
  - exact H.
Qed.

Lemma EnvRel_ge : forall n (γ γ' : gradeVec n) Γ ρ, (forall i, Qle (γ i) (γ' i)) -> EnvRel γ Γ ρ -> EnvRel γ' Γ ρ.
Proof.
  intros n γ γ' Γ ρ Hle H i. specialize (H i). destruct H as [H|H]; [left | right].
  - apply Qle_zero_eq. rewrite <- H. apply Hle.
  - exact H.
Qed.

Lemma EnvRel_cons : forall n q (γ : gradeVec n) A (Γ : context n) W (ρ : env n),
  (q = Qzero \/ VShape A W) -> EnvRel γ Γ ρ -> EnvRel (q .: γ) (A .: Γ) (W .: ρ).
Proof.
  intros n q γ A Γ W ρ Hh Ht i. destruct i as [i|].
  - simpl. apply Ht.
  - simpl. exact Hh.
Qed.

(* ================= main soundness ================= *)

Lemma sound_general : forall n γ Γ,
  (forall (V : Val n) (A : ValTy), VWt γ Γ V A -> forall ρ, EnvRel γ Γ ρ ->
     exists W, EvalVal γ ρ V W /\ VShape A W) /\
  (forall (M : Comp n) (B : CompTy) (ϕ : E), CWt γ Γ M B ϕ -> forall ρ, EnvRel γ Γ ρ ->
     exists T ϕ1 ψ, EvalComp γ ρ M T ϕ1 /\ CShape B T ψ /\ subeff (ϕ1 E+ ψ) ϕ).
Proof.
  apply (Wt_mutual
    (fun n γ Γ (V : Val n) (A : ValTy) (d : VWt γ Γ V A) =>
       forall ρ, EnvRel γ Γ ρ -> exists W, EvalVal γ ρ V W /\ VShape A W)
    (fun n γ Γ (M : Comp n) (B : CompTy) (ϕ : E) (d : CWt γ Γ M B ϕ) =>
       forall ρ, EnvRel γ Γ ρ -> exists T ϕ1 ψ, EvalComp γ ρ M T ϕ1 /\ CShape B T ψ /\ subeff (ϕ1 E+ ψ) ϕ)).
  - (* T_Var *)
    intros n γ Γ i e e0 ρ Hρ.
    specialize (Hρ i). destruct Hρ as [Hz|Hs].
    + exfalso. apply Qnontrivial. rewrite <- e. exact Hz.
    + exists (ρ i). split.
      * eapply E_Var; [reflexivity | exact e | exact e0].
      * exact Hs.
  - (* T_Thunk *)
    intros n γ Γ M B ϕ c IH ρ Hρ.
    destruct (IH ρ Hρ) as (T' & ϕ' & ψ' & Hev & Hcs & Hle).
    exists (VClosThunk n γ ρ M). split.
    + eapply E_Thunk; reflexivity.
    + simpl. exists n, γ, ρ, M. split; [reflexivity|].
      exists T', ϕ', ψ'. repeat split; assumption.
  - (* T_Unit *)
    intros n γ Γ e ρ Hρ.
    exists VClosUnit. split.
    + apply E_Unit. exact e.
    + reflexivity.
  - (* T_VPair *)
    intros n γ Γ V1 V2 A1 A2 γ1 γ2 dv1 IH1 dv2 IH2 e ρ Hρ.
    rewrite e in Hρ.
    destruct (IH1 ρ (@EnvRel_add_l _ _ _ _ _ Hρ)) as (W1 & Hev1 & Hs1).
    destruct (IH2 ρ (@EnvRel_add_r _ _ _ _ _ Hρ)) as (W2 & Hev2 & Hs2).
    exists (VClosPair W1 W2). split.
    + eapply E_VPair; [exact Hev1 | exact Hev2 | exact e].
    + simpl. exists W1, W2. split; [reflexivity|split; assumption].
  - (* T_Inl *)
    intros n γ Γ V A1 A2 dv IH ρ Hρ.
    destruct (IH ρ Hρ) as (W & Hev & Hs).
    exists (VClosInl W). split.
    + eapply E_Inl; exact Hev.
    + simpl. left. exists W. split; [reflexivity|exact Hs].
  - (* T_Inr *)
    intros n γ Γ V A1 A2 dv IH ρ Hρ.
    destruct (IH ρ Hρ) as (W & Hev & Hs).
    exists (VClosInr W). split.
    + eapply E_Inr; exact Hev.
    + simpl. right. exists W. split; [reflexivity|exact Hs].
  - (* T_VSub *)
    intros n γ Γ V A γ' dv IH Hle ρ Hρ.
    assert (Hρ' : EnvRel γ' Γ ρ) by (exact (@EnvRel_ge _ _ _ _ _ Hle Hρ)).
    destruct (IH ρ Hρ') as (W & Hev & Hs).
    exists W. split.
    + eapply E_VSub; [exact Hev | exact Hle].
    + exact Hs.
  - (* T_Abs *)
    intros n γ Γ q q' M A B ϕ c IH Hle ρ Hρ.
    exists (CClosAbs n q' γ ρ M), ϵ, ϕ. repeat split.
    + eapply E_Abs; [exact Hle | reflexivity].
    + simpl. exists n, γ, ρ, M. split; [reflexivity|].
      intros W HW.
      assert (Hq : q = Qzero \/ VShape A W).
      { destruct HW as [Hq0|Hs]; [left|right].
        - apply Qle_zero_eq. rewrite <- Hq0. exact Hle.
        - exact Hs. }
      destruct (IH (W .: ρ) (@EnvRel_cons _ _ _ _ _ _ _ Hq Hρ)) as (T' & ϕ' & ψ' & Hev & Hcs & Hle2).
      exists T', ϕ', ψ'. split; [|split].
      * eapply E_CSub.
        -- exact Hev.
        -- intros i; destruct i as [i|]; simpl.
           ++ apply Qle_refl.
           ++ exact Hle.
      * exact Hcs.
      * exact Hle2.
    + rewrite eff_idL. apply subeff_refl.
  - (* T_App *)
    intros n γ Γ q M V A B γ1 γ2 ϕ cM IHM cV IHV e ρ Hρ.
    rewrite e in Hρ.
    destruct (IHM ρ (@EnvRel_add_l _ _ _ _ _ Hρ)) as (T & ϕ1 & ψ & HevM & Hcs & Hle).
    destruct Hcs as (m & γ0 & ρ0 & M0 & HT & Hsem). subst T.
    destruct (Qeqb q Qzero) eqn:Eq.
    + apply Qeqb_true in Eq. subst q.
      destruct (Hsem JUNK (or_introl eq_refl)) as (T' & ϕ' & ψ' & HevB & HcsB & HleB).
      assert (HevM' : EvalComp γ ρ M (CClosAbs m Qzero γ0 ρ0 M0) ϕ1).
      { eapply E_CSub.
        - exact HevM.
        - intros i; rewrite e. change (Qle (Qadd (γ1 i) (Qmult Qzero (γ2 i))) (γ1 i)).
          rewrite Qzero_lannihilates. rewrite Qadd_rident. apply Qle_refl. }
      exists T', (ϕ1 E+ ϕ'), ψ'. repeat split.
      * eapply E_AppAbsZero; [exact HevM' | exact HevB | reflexivity].
      * exact HcsB.
      * rewrite eff_assoc. eapply subeff_trans.
        -- apply subeff_add_left_compatible. exact HleB.
        -- exact Hle.
    + apply Qeqb_false in Eq.
      destruct (IHV ρ (@EnvRel_scale _ _ _ _ _ Eq (@EnvRel_add_r _ _ _ _ _ Hρ))) as (W & HevV & HshapeV).
      destruct (Hsem W (or_intror HshapeV)) as (T' & ϕ' & ψ' & HevB & HcsB & HleB).
      exists T', (ϕ1 E+ ϕ'), ψ'. repeat split.
      * eapply E_AppAbs; [exact HevM | exact HevV | exact HevB | exact e | exact Eq | reflexivity].
      * exact HcsB.
      * rewrite eff_assoc. eapply subeff_trans.
        -- apply subeff_add_left_compatible. exact HleB.
        -- exact Hle.
  - (* T_Force *)
    intros n γ Γ V B ϕ cV IH ρ Hρ.
    destruct (IH ρ Hρ) as (W & Hev & Hshape).
    simpl in Hshape.
    destruct Hshape as (m & γ0 & ρ0 & M0 & HW & T' & ϕ' & ψ' & HevB & Hcs & Hle).
    subst W.
    exists T', ϕ', ψ'. repeat split.
    + eapply E_ForceThunk; [exact Hev | exact HevB].
    + exact Hcs.
    + exact Hle.
  - (* T_Split *)
    intros n γ Γ q V N A1 A2 B γ1 γ2 ϕ cV IHV cN IHN e ρ Hρ.
    rewrite e in Hρ.
    destruct (Qeqb q Qzero) eqn:Eq.
    + apply Qeqb_true in Eq. subst q.
      assert (Hρ2 : EnvRel γ2 Γ ρ) by (exact (@EnvRel_add_r _ (Qzero Q* γ1) γ2 Γ ρ Hρ)).
      destruct (IHN (JUNK .: (JUNK .: ρ))
                    (@EnvRel_cons _ _ _ _ _ _ _ (or_introl eq_refl) (@EnvRel_cons _ _ _ _ _ _ _ (or_introl eq_refl) Hρ2)))
        as (T' & ϕ' & ψ' & HevB & Hcs & Hle).
      assert (HevB' : EvalComp (Qzero .: (Qzero .: γ)) (JUNK .: (JUNK .: ρ)) N T' ϕ').
      { eapply E_CSub.
        - exact HevB.
        - intros i; rewrite e. destruct i as [i|]; simpl.
          + destruct i as [i|]; simpl.
            * change (Qle (Qadd (Qmult Qzero (γ1 i)) (γ2 i)) (γ2 i)).
              rewrite Qzero_lannihilates. rewrite Qadd_lident. apply Qle_refl.
            * apply Qle_refl.
          + apply Qle_refl. }
      exists T', ϕ', ψ'. repeat split.
      * eapply E_SplitZero; exact HevB'.
      * exact Hcs.
      * exact Hle.
    + apply Qeqb_false in Eq.
      assert (Hρ1 : EnvRel γ1 Γ ρ) by (exact (@EnvRel_scale _ q γ1 Γ ρ Eq (@EnvRel_add_l _ (q Q* γ1) γ2 Γ ρ Hρ))).
      assert (Hρ2 : EnvRel γ2 Γ ρ) by (exact (@EnvRel_add_r _ (q Q* γ1) γ2 Γ ρ Hρ)).
      destruct (IHV ρ Hρ1) as (W & HevV & Hshape).
      simpl in Hshape. destruct Hshape as (W1 & W2 & HW & Hs1 & Hs2). subst W.
      destruct (IHN (W1 .: (W2 .: ρ))
                    (@EnvRel_cons _ _ _ _ _ _ _ (or_intror Hs1) (@EnvRel_cons _ _ _ _ _ _ _ (or_intror Hs2) Hρ2)))
        as (T' & ϕ' & ψ' & HevB & Hcs & Hle).
      exists T', ϕ', ψ'. repeat split.
      * eapply E_Split; [exact HevV | exact HevB | exact e | exact Eq].
      * exact Hcs.
      * exact Hle.
  - (* T_Ret *)
    intros n γ Γ q V A γ1 ϕ cV IH e1 e2 ρ Hρ.
    rewrite e1 in Hρ.
    destruct (Qeqb q Qzero) eqn:Eq.
    + apply Qeqb_true in Eq. subst q.
      exists (CClosRet Qzero JUNK), ϵ, ϵ. split; [|split].
      * eapply E_CSub.
        -- eapply E_RetZero; reflexivity.
        -- intros i; rewrite e1. change (Qle (Qmult Qzero (γ1 i)) Qzero).
           rewrite Qzero_lannihilates. apply Qle_refl.
      * cbn [CShape]. split; [reflexivity|]. exists JUNK. split; [reflexivity|right]. split; reflexivity.
      * rewrite eff_idL. rewrite e2. apply subeff_refl.
    + apply Qeqb_false in Eq.
      assert (Hρ1 : EnvRel γ1 Γ ρ) by (exact (@EnvRel_scale _ q γ1 Γ ρ Eq Hρ)).
      destruct (IH ρ Hρ1) as (W & HevV & Hshape).
      exists (CClosRet q W), ϵ, ϵ. split; [|split].
      * eapply E_Ret; [exact HevV | exact e1 | exact Eq | reflexivity].
      * cbn [CShape]. split; [reflexivity|]. exists W. split; [reflexivity|left]. exact Hshape.
      * rewrite eff_idL. rewrite e2. apply subeff_refl.
  - (* T_Let *)
    intros n γ Γ q1 q2 q' M N A B γ1 γ2 ϕ1 ϕ2 ϕ e0 cM IHM cN IHN e1 e2 ρ Hρ.
    rewrite e1 in Hρ.
    assert (Hq' : q' <> Qzero) by (rewrite e0; apply q_or_1_nonzero).
    assert (Hρ1 : EnvRel γ1 Γ ρ) by (exact (@EnvRel_scale _ q' γ1 Γ ρ Hq' (@EnvRel_add_l _ (q' Q* γ1) γ2 Γ ρ Hρ))).
    assert (Hρ2 : EnvRel γ2 Γ ρ) by (exact (@EnvRel_add_r _ (q' Q* γ1) γ2 Γ ρ Hρ)).
    destruct (IHM ρ Hρ1) as (T1 & ϕ1' & ψ1 & HevM & HcsM & Hle1).
    destruct HcsM as (Hψ1 & W & HT1 & HshapeW). subst T1. subst ψ1.
    assert (Hhead : Qmult q1 q' = Qzero \/ VShape A W).
    { destruct HshapeW as [Hs|Hj].
      - right; exact Hs.
      - destruct Hj as [HW Hq1]. left. rewrite Hq1. apply Qzero_lannihilates. }
    destruct (IHN (W .: ρ) (@EnvRel_cons _ _ _ _ _ _ _ Hhead Hρ2)) as (T' & ϕ' & ψ' & HevB & Hcs & Hle2).
    exists T', (ϕ1' E+ ϕ'), ψ'. repeat split.
    + eapply E_LetRet; [exact e0 | exact HevM | exact HevB | exact e1 | reflexivity].
    + exact Hcs.
    + rewrite e2. rewrite eff_assoc. eapply subeff_trans.
      * apply subeff_add_left_compatible. exact Hle2.
      * rewrite eff_idR in Hle1. apply subeff_add_right_compatible. exact Hle1.
  - (* T_CPair *)
    intros n γ Γ M1 M2 B1 B2 ϕ c1 IH1 c2 IH2 ρ Hρ.
    destruct (IH1 ρ Hρ) as (T1 & ϕ1 & ψ1 & Hev1 & Hcs1 & Hle1).
    destruct (IH2 ρ Hρ) as (T2 & ϕ2 & ψ2 & Hev2 & Hcs2 & Hle2).
    exists (CClosPair n γ ρ M1 M2), ϵ, ϕ. repeat split.
    + eapply E_CPair; reflexivity.
    + simpl. exists n, γ, ρ, M1, M2, ϕ, ϕ. split; [reflexivity|].
      split; [apply subeff_refl|]. split; [apply subeff_refl|]. split.
      * exists T1, ϕ1, ψ1. split; [exact Hev1|split; [exact Hcs1|exact Hle1]].
      * exists T2, ϕ2, ψ2. split; [exact Hev2|split; [exact Hcs2|exact Hle2]].
    + rewrite eff_idL. apply subeff_refl.
  - (* T_Fst *)
    intros n γ Γ M B1 B2 ϕ c IH ρ Hρ.
    destruct (IH ρ Hρ) as (T & ϕ0 & ψ & HevM & Hcs & Hle).
    destruct Hcs as (m & γ0 & ρ0 & M1 & M2 & ψ1 & ψ2 & HT & Hle1 & Hle2
                      & (T1 & ϕ1 & ψ1' & Hev1 & Hcs1 & Hle1')
                      & (T2 & ϕ2 & ψ2' & Hev2 & Hcs2 & Hle2')).
    subst T.
    exists T1, (ϕ0 E+ ϕ1), ψ1'. repeat split.
    + eapply E_Fst; [exact HevM | exact Hev1 | reflexivity].
    + exact Hcs1.
    + rewrite eff_assoc. eapply subeff_trans.
      * apply subeff_add_left_compatible. exact Hle1'.
      * eapply subeff_trans.
        -- apply subeff_add_left_compatible. exact Hle1.
        -- exact Hle.
  - (* T_Snd *)
    intros n γ Γ M B1 B2 ϕ c IH ρ Hρ.
    destruct (IH ρ Hρ) as (T & ϕ0 & ψ & HevM & Hcs & Hle).
    destruct Hcs as (m & γ0 & ρ0 & M1 & M2 & ψ1 & ψ2 & HT & Hle1 & Hle2
                      & (T1 & ϕ1 & ψ1' & Hev1 & Hcs1 & Hle1')
                      & (T2 & ϕ2 & ψ2' & Hev2 & Hcs2 & Hle2')).
    subst T.
    exists T2, (ϕ0 E+ ϕ2), ψ2'. repeat split.
    + eapply E_Snd; [exact HevM | exact Hev2 | reflexivity].
    + exact Hcs2.
    + rewrite eff_assoc. eapply subeff_trans.
      * apply subeff_add_left_compatible. exact Hle2'.
      * eapply subeff_trans.
        -- apply subeff_add_left_compatible. exact Hle2.
        -- exact Hle.
  - (* T_Seq *)
    intros n γ Γ V N B γ1 γ2 ϕ cV IHV cN IHN e ρ Hρ.
    rewrite e in Hρ.
    destruct (IHV ρ (@EnvRel_add_l _ _ _ _ _ Hρ)) as (W & HevV & Hshape).
    simpl in Hshape. subst W.
    destruct (IHN ρ (@EnvRel_add_r _ _ _ _ _ Hρ)) as (T' & ϕ' & ψ' & HevB & Hcs & Hle).
    exists T', ϕ', ψ'. repeat split.
    + eapply E_Seq; [exact HevV | exact HevB | exact e].
    + exact Hcs.
    + exact Hle.
  - (* T_Case *)
    intros n γ Γ q V M1 M2 A1 A2 B γ1 γ2 ϕ cV IHV c1 IH1 c2 IH2 e Hqle ρ Hρ.
    rewrite e in Hρ.
    assert (Hq : q <> Qzero) by (apply Qle_Qone_ne_zero; exact Hqle).
    assert (Hρ1 : EnvRel γ1 Γ ρ) by (exact (@EnvRel_scale _ q γ1 Γ ρ Hq (@EnvRel_add_l _ (q Q* γ1) γ2 Γ ρ Hρ))).
    assert (Hρ2 : EnvRel γ2 Γ ρ) by (exact (@EnvRel_add_r _ (q Q* γ1) γ2 Γ ρ Hρ)).
    destruct (IHV ρ Hρ1) as (W & HevV & Hshape).
    simpl in Hshape. destruct Hshape as [(W1 & HW & Hs1) | (W2 & HW & Hs2)].
    + subst W.
      destruct (IH1 (W1 .: ρ) (@EnvRel_cons _ _ _ _ _ _ _ (or_intror Hs1) Hρ2)) as (T' & ϕ' & ψ' & HevB & Hcs & Hle).
      exists T', ϕ', ψ'. repeat split.
      * eapply E_Casel; [exact HevV | exact HevB | exact e | exact Hqle].
      * exact Hcs.
      * exact Hle.
    + subst W.
      destruct (IH2 (W2 .: ρ) (@EnvRel_cons _ _ _ _ _ _ _ (or_intror Hs2) Hρ2)) as (T' & ϕ' & ψ' & HevB & Hcs & Hle).
      exists T', ϕ', ψ'. repeat split.
      * eapply E_Caser; [exact HevV | exact HevB | exact e | exact Hqle].
      * exact Hcs.
      * exact Hle.
  - (* T_Tick *)
    intros n γ Γ phi e1 e2 ρ Hρ.
    exists (CClosRet Qone VClosUnit), tick, ϵ. split; [|split].
    + eapply E_Tick; [exact e1 | reflexivity].
    + cbn [CShape]. split; [reflexivity|]. exists VClosUnit. split; [reflexivity|left]. reflexivity.
    + rewrite e2. rewrite eff_idR. apply subeff_refl.
  - (* T_CSub *)
    intros n γ Γ M B ϕ γ' c IH Hle ρ Hρ.
    destruct (IH ρ (@EnvRel_ge _ _ _ _ _ Hle Hρ)) as (T & ϕ1 & ψ & Hev & Hcs & Hsub).
    exists T, ϕ1, ψ. repeat split.
    + eapply E_CSub; [exact Hev | exact Hle].
    + exact Hcs.
    + exact Hsub.
  - (* T_SubEff *)
    intros n γ Γ M B ϕ ϕ' c IH Hle ρ Hρ.
    destruct (IH ρ Hρ) as (T & ϕ1 & ψ & Hev & Hcs & Hsub).
    exists T, ϕ1, ψ. repeat split.
    + exact Hev.
    + exact Hcs.
    + eapply subeff_trans; [exact Hsub | exact Hle].
  - (* T_LetZero *)
    intros n γ Γ q1 M N A B γ1 γ2 ϕ2 ϕ cM IHM cN IHN e1 e2 ρ Hρ.
    subst γ2.
    destruct (IHN (JUNK .: ρ) (@EnvRel_cons _ _ _ _ _ _ _ (or_introl eq_refl) Hρ)) as (T' & ϕ' & ψ' & HevB & Hcs & Hle).
    exists T', ϕ', ψ'. repeat split.
    + eapply E_LetRetZero; [exact HevB | reflexivity].
    + exact Hcs.
    + rewrite e2. exact Hle.
Qed.

Theorem soundness :
  (forall V A, VWt null null V A -> exists W,
    EvalVal null null V W) /\
  (forall M q A ϕ, CWt null null M (CF q A) ϕ ->
    exists T ϕ1,
    EvalComp null null M T ϕ1 /\ ϕ1 E<= ϕ).
Proof.
  destruct (@sound_general 0 (null : gradeVec 0) (null : context 0)) as [HV HC].
  split.
  - intros V A H.
    assert (Hrel : EnvRel (null : gradeVec 0) (null : context 0) (null : env 0))
      by (intros i; destruct i).
    destruct (HV V A H null Hrel) as (W & Hev & Hs).
    exists W. exact Hev.
  - intros M q A ϕ H.
    assert (Hrel : EnvRel (null : gradeVec 0) (null : context 0) (null : env 0))
      by (intros i; destruct i).
    destruct (HC M (CF q A) ϕ H null Hrel) as (T & ϕ1 & ψ & Hev & Hcs & Hle).
    destruct Hcs as [Hψ [W [HT Hsh]]]. subst ψ.
    exists T, ϕ1. split; [exact Hev|].
    rewrite eff_idR in Hle. exact Hle.
Qed.
