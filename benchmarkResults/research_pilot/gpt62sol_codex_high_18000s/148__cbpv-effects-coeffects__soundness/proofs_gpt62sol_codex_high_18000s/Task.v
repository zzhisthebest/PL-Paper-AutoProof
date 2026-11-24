Require Import full.CBPV.semantics.

Require Import full.CBPV.typing.

(* A suspended computation must respect the effect bound when observed.
   The spent effect includes evaluation that preceded the observation. *)
Fixpoint value_realizes (A : ValTy) (W : VClos) {struct A} : Prop :=
  match A with
  | VUnit => W = VClosUnit
  | VThunk bound B =>
      match W with
      | VClosThunk _ γ ρ M =>
          exists T spent, EvalComp γ ρ M T spent /\
                          comp_realizes B spent bound T
      | _ => False
      end
  | VPair A1 A2 =>
      match W with
      | VClosPair W1 W2 => value_realizes A1 W1 /\ value_realizes A2 W2
      | _ => False
      end
  | VSum A1 A2 =>
      match W with
      | VClosInl W1 => value_realizes A1 W1
      | VClosInr W2 => value_realizes A2 W2
      | _ => False
      end
  end
with comp_realizes (B : CompTy) (spent bound : E) (T : CClos) {struct B} : Prop :=
  match B with
  | CAbs q A B' =>
      match T with
      | CClosAbs _ r γ ρ M =>
          r = q /\
          forall W, (q <> Qzero -> value_realizes A W) ->
            exists T' next, EvalComp (q .: γ) (W .: ρ) M T' next /\
                            comp_realizes B' (spent E+ next) bound T'
      | _ => False
      end
  | CF q A =>
      match T with
      | CClosRet r W =>
          r = q /\ spent E<= bound /\ (q <> Qzero -> value_realizes A W)
      | _ => False
      end
  | CPair B1 B2 =>
      match T with
      | CClosPair _ γ ρ M1 M2 =>
          (exists T1 next, EvalComp γ ρ M1 T1 next /\
                           comp_realizes B1 (spent E+ next) bound T1) /\
          (exists T2 next, EvalComp γ ρ M2 T2 next /\
                           comp_realizes B2 (spent E+ next) bound T2)
      | _ => False
      end
  end.

(* Only a variable with nonzero grade needs a realizing closure. *)
Definition env_realizes {n} (γ : gradeVec n) (Γ : context n) (ρ : env n) :=
  forall i, γ i <> Qzero -> value_realizes (Γ i) (ρ i).

Lemma grade_zero_le q : Qle Qzero q -> q = Qzero.
Proof.
  intro H.
  assert (Hsum : Qle Qzero (Qadd q Qzero)) by now rewrite Qadd_rident.
  exact (proj1 (Qsumzero q Qzero Hsum)).
Qed.

Lemma grade_zero_dec q : {q = Qzero} + {q <> Qzero}.
Proof.
  destruct (Qeqb q Qzero) eqn:H.
  - left. now apply Qeqb_eq.
  - right. intro Heq. apply Qeqb_eq in Heq. congruence.
Qed.

Lemma q_or_1_nonzero q : q_or_1 q <> Qzero.
Proof.
  unfold q_or_1. destruct (Qeqb q Qzero) eqn:H.
  - exact Qnontrivial.
  - intro Heq. apply Qeqb_eq in Heq. congruence.
Qed.

Lemma grade_scale_zero_le {n} (γ : gradeVec n) : Qzero Q* γ Q<= 0s.
Proof.
  intro i. unfold gradeVecScale, gradeVecZero.
  rewrite Qzero_lannihilates. apply Qle_refl.
Qed.

Lemma grade_add_scaled_zero_l_le {n} (γ1 γ2 : gradeVec n) :
  Qzero Q* γ1 Q+ γ2 Q<= γ2.
Proof.
  intro i. unfold gradeVecAdd, gradeVecScale.
  rewrite Qzero_lannihilates, Qadd_lident. apply Qle_refl.
Qed.

Lemma grade_add_scaled_zero_r_le {n} (γ1 γ2 : gradeVec n) :
  γ1 Q+ Qzero Q* γ2 Q<= γ1.
Proof.
  intro i. unfold gradeVecAdd, gradeVecScale.
  rewrite Qzero_lannihilates, Qadd_rident. apply Qle_refl.
Qed.

Lemma env_realizes_sub {n} (γ γ' : gradeVec n) Γ ρ :
  env_realizes γ Γ ρ -> γ Q<= γ' -> env_realizes γ' Γ ρ.
Proof.
  intros Henv Hle i Hnonzero.
  apply Henv. intro Hz. apply Hnonzero, grade_zero_le.
  rewrite <- Hz. apply Hle.
Qed.

Lemma env_realizes_add {n} (γ1 γ2 : gradeVec n) Γ ρ :
  env_realizes (γ1 Q+ γ2) Γ ρ ->
  env_realizes γ1 Γ ρ /\ env_realizes γ2 Γ ρ.
Proof.
  intros Henv.
  assert (Hzero : forall i, (γ1 Q+ γ2) i = Qzero ->
    γ1 i = Qzero /\ γ2 i = Qzero).
  { intros i Hi. apply Qsumzero.
    change (Qle Qzero ((γ1 Q+ γ2) i)).
    rewrite Hi. apply Qle_refl. }
  split; intros i Hnonzero; apply Henv; intro Hi;
    destruct (Hzero i Hi); contradiction.
Qed.

Lemma env_realizes_scale {n} q (γ : gradeVec n) Γ ρ :
  q <> Qzero -> env_realizes (q Q* γ) Γ ρ -> env_realizes γ Γ ρ.
Proof.
  intros Hq Henv i Hi. apply Henv.
  change (Qmult q (γ i) <> Qzero).
  intro Hz. destruct (Qprodzero _ _ Hz); contradiction.
Qed.

Lemma env_realizes_cons {n} q (γ : gradeVec n) A Γ W ρ :
  (q <> Qzero -> value_realizes A W) -> env_realizes γ Γ ρ ->
  env_realizes (q .: γ) (A .: Γ) (W .: ρ).
Proof.
  intros HW Henv [i|]; [apply Henv | apply HW].
Qed.

Lemma grade_cons_le {n} q q' (γ : gradeVec n) :
  Qle q q' -> (q .: γ) Q<= (q' .: γ).
Proof.
  intros Hq [i|]; [apply Qle_refl | exact Hq].
Qed.

Lemma comp_realizes_effect B T spent bound spent' bound' :
  comp_realizes B spent bound T ->
  (forall tail, (spent E+ tail) E<= bound -> (spent' E+ tail) E<= bound') ->
  comp_realizes B spent' bound' T.
Proof.
  revert T spent bound spent' bound'.
  induction B as [q A B IH | q A | B1 IH1 B2 IH2];
    intros T spent bound spent' bound' H Hchange;
    destruct T as [r W | m r γ ρ M | m γ ρ M1 M2]; cbn in H |- *;
    try contradiction.
  - destruct H as [Hr Hbody]. split; [exact Hr |].
    intros W HW. destruct (Hbody W HW) as (T & next & Heval & Hnext).
    exists T, next. split; [exact Heval |].
    eapply IH; [exact Hnext |].
    intro tail. rewrite !eff_assoc. apply Hchange.
  - destruct H as (Hr & Hspent & HW). split; [exact Hr |].
    split; [|exact HW].
    specialize (Hchange ϵ). rewrite !eff_idR in Hchange.
    exact (Hchange Hspent).
  - destruct H as [(T1 & next1 & Heval1 & Hnext1) (T2 & next2 & Heval2 & Hnext2)].
    split.
    + exists T1, next1. split; [exact Heval1 |].
      eapply IH1; [exact Hnext1 |].
      intro tail. rewrite !eff_assoc. apply Hchange.
    + exists T2, next2. split; [exact Heval2 |].
      eapply IH2; [exact Hnext2 |].
      intro tail. rewrite !eff_assoc. apply Hchange.
Qed.

Lemma effect_add_le a a' b b' :
  a E<= a' -> b E<= b' -> (a E+ b) E<= (a' E+ b').
Proof.
  intros Ha Hb. eapply subeff_trans.
  - apply subeff_add_right_compatible, Ha.
  - apply subeff_add_left_compatible, Hb.
Qed.

Lemma typed_realizes :
  forall n (γ : gradeVec n) (Γ : context n),
    (forall V A, VWt γ Γ V A ->
      forall ρ, env_realizes γ Γ ρ ->
      exists W, EvalVal γ ρ V W /\ value_realizes A W) /\
    (forall M B bound, CWt γ Γ M B bound ->
      forall ρ, env_realizes γ Γ ρ ->
      exists T spent, EvalComp γ ρ M T spent /\ comp_realizes B spent bound T).
Proof.
  apply Wt_mutual.
  - intros n γ Γ i Hi Hothers ρ Henv.
    exists (ρ i). split.
    + now apply E_Var.
    + apply Henv. rewrite Hi. exact Qnontrivial.
  - intros n γ Γ M B bound Htyped IH ρ Henv.
    exists (VClosThunk n γ ρ M). split.
    + apply E_Thunk. reflexivity.
    + exact (IH ρ Henv).
  - intros n γ Γ Hzero ρ Henv.
    exists VClosUnit. split; [now apply E_Unit | reflexivity].
  - intros n γ Γ V1 V2 A1 A2 γ1 γ2 H1 IH1 H2 IH2 -> ρ Henv.
    destruct (env_realizes_add γ1 γ2 Γ ρ Henv) as [Henv1 Henv2].
    destruct (IH1 ρ Henv1) as (W1 & Heval1 & HW1).
    destruct (IH2 ρ Henv2) as (W2 & Heval2 & HW2).
    exists (VClosPair W1 W2). split.
    + eapply E_VPair; [exact Heval1 | exact Heval2 | reflexivity].
    + exact (conj HW1 HW2).
  - intros n γ Γ V A1 A2 Htyped IH ρ Henv.
    destruct (IH ρ Henv) as (W & Heval & HW).
    exists (VClosInl W). split; [now apply E_Inl | exact HW].
  - intros n γ Γ V A1 A2 Htyped IH ρ Henv.
    destruct (IH ρ Henv) as (W & Heval & HW).
    exists (VClosInr W). split; [now apply E_Inr | exact HW].
  - intros n γ Γ V A γ' Htyped IH Hle ρ Henv.
    destruct (IH ρ (env_realizes_sub γ γ' Γ ρ Henv Hle)) as (W & Heval & HW).
    exists W. split; [|exact HW].
    eapply E_VSub; [exact Heval | exact Hle].
  - intros n γ Γ q r M A B bound Htyped IH Hle ρ Henv.
    exists (CClosAbs n r γ ρ M), ϵ. split.
    + now apply E_Abs.
    + cbn. split; [reflexivity |].
      intros W HW.
      pose proof (grade_cons_le r q γ Hle) as Hgrades.
      assert (Hbody : env_realizes (q .: γ) (A .: Γ) (W .: ρ)).
      { eapply env_realizes_sub.
        - exact (env_realizes_cons r γ A Γ W ρ HW Henv).
        - exact Hgrades. }
      destruct (IH (W .: ρ) Hbody) as (T & spent & Heval & HT).
      exists T, spent. split.
      * eapply E_CSub; [exact Heval | exact Hgrades].
      * now rewrite eff_idL.
  - intros n γ Γ q M V A B γ1 γ2 bound Hm IHm Hv IHv -> ρ Henv.
    destruct (env_realizes_add γ1 (q Q* γ2) Γ ρ Henv) as [Henv1 Hscaled].
    destruct (IHm ρ Henv1) as (F & spent & Heval & HF).
    destruct F as [r W | m r γ' ρ' M' | m γ' ρ' M1 M2]; cbn in HF; try contradiction.
    destruct HF as [-> Hbody].
    destruct (grade_zero_dec q) as [-> | Hq].
    + assert (Hjunk : Qzero <> Qzero -> value_realizes A JUNK) by contradiction.
      destruct (Hbody JUNK Hjunk) as (T & next & Hnext & HT).
      exists T, (spent E+ next). split; [|exact HT].
      eapply E_CSub.
      * eapply E_AppAbsZero; [exact Heval | exact Hnext | reflexivity].
      * apply grade_add_scaled_zero_r_le.
    + destruct (IHv ρ (env_realizes_scale q γ2 Γ ρ Hq Hscaled))
        as (W & Hval & HW).
      destruct (Hbody W (fun _ => HW)) as (T & next & Hnext & HT).
      exists T, (spent E+ next). split; [|exact HT].
      eapply E_AppAbs; [exact Heval | exact Hval | exact Hnext | reflexivity | exact Hq | reflexivity].
  - intros n γ Γ V B bound Htyped IH ρ Henv.
    destruct (IH ρ Henv) as (W & Heval & HW).
    destruct W as [| m γ' ρ' M | W1 W2 | W | W |]; cbn in HW; try contradiction.
    destruct HW as (T & spent & Hbody & HT).
    exists T, spent. split; [|exact HT].
    eapply E_ForceThunk; [exact Heval | exact Hbody].
  - intros n γ Γ q V N A1 A2 B γ1 γ2 bound Hv IHv Hn IHn -> ρ Henv.
    destruct (env_realizes_add (q Q* γ1) γ2 Γ ρ Henv) as [Hscaled Henv2].
    destruct (grade_zero_dec q) as [-> | Hq].
    + assert (Hbody : env_realizes (Qzero .: (Qzero .: γ2))
          (A1 .: (A2 .: Γ)) (JUNK .: (JUNK .: ρ))).
      { apply env_realizes_cons; [contradiction |].
        apply env_realizes_cons; [contradiction | exact Henv2]. }
      destruct (IHn _ Hbody) as (T & spent & Hnext & HT).
      exists T, spent. split; [|exact HT].
      eapply E_CSub with (γ' := γ2).
      * now apply E_SplitZero.
      * apply grade_add_scaled_zero_l_le.
    + destruct (IHv ρ (env_realizes_scale q γ1 Γ ρ Hq Hscaled))
        as (W & Heval & HW).
      destruct W as [| m γ' ρ' M | W1 W2 | W | W |]; cbn in HW; try contradiction.
      destruct HW as [HW1 HW2].
      assert (Hbody : env_realizes (q .: (q .: γ2))
          (A1 .: (A2 .: Γ)) (W1 .: (W2 .: ρ))).
      { apply env_realizes_cons; [intros _; exact HW1 |].
        apply env_realizes_cons; [intros _; exact HW2 | exact Henv2]. }
      destruct (IHn _ Hbody) as (T & spent & Hnext & HT).
      exists T, spent. split; [|exact HT].
      eapply E_Split; [exact Heval | exact Hnext | reflexivity | exact Hq].
  - intros n γ Γ q V A γ1 bound Htyped IH -> -> ρ Henv.
    destruct (grade_zero_dec q) as [-> | Hq].
    + exists (CClosRet Qzero JUNK), ϵ. split.
      * eapply E_CSub with (γ' := 0s).
        -- apply E_RetZero; reflexivity.
        -- apply grade_scale_zero_le.
      * cbn. repeat split; [apply subeff_refl | contradiction].
    + destruct (IH ρ (env_realizes_scale q γ1 Γ ρ Hq Henv)) as (W & Heval & HW).
      exists (CClosRet q W), ϵ. split.
      * eapply E_Ret; [exact Heval | reflexivity | exact Hq | reflexivity].
      * cbn. repeat split; [apply subeff_refl | intros _; exact HW].
  - intros n γ Γ q1 q2 r M N A B γ1 γ2 bound1 bound2 bound Hr
      Hm IHm Hn IHn -> -> ρ Henv.
    destruct (env_realizes_add (r Q* γ1) γ2 Γ ρ Henv) as [Hscaled Henv2].
    assert (Hnonzero : r <> Qzero) by (rewrite Hr; apply q_or_1_nonzero).
    destruct (IHm ρ (env_realizes_scale r γ1 Γ ρ Hnonzero Hscaled))
      as (R & spent & Heval & HR).
    destruct R as [q W | m q γ' ρ' M' | m γ' ρ' M1 M2]; cbn in HR; try contradiction.
    destruct HR as (-> & Hspent & HW).
    assert (Hbody : env_realizes (Qmult q1 r .: γ2) (A .: Γ) (W .: ρ)).
    { apply env_realizes_cons; [|exact Henv2].
      intros Hprod. apply HW. intro Hzero.
      apply Hprod. now rewrite Hzero, Qzero_lannihilates. }
    destruct (IHn _ Hbody) as (T & next & Hnext & HT).
    exists T, (spent E+ next). split.
    + eapply E_LetRet; [exact Hr | exact Heval | exact Hnext | reflexivity | reflexivity].
    + eapply comp_realizes_effect; [exact HT |].
      intro tail. rewrite eff_assoc. apply effect_add_le, Hspent.
  - intros n γ Γ M1 M2 B1 B2 bound H1 IH1 H2 IH2 ρ Henv.
    exists (CClosPair n γ ρ M1 M2), ϵ. split.
    + now apply E_CPair.
    + cbn. split.
      * destruct (IH1 ρ Henv) as (T & next & Heval & HT).
        exists T, next. split; [exact Heval | now rewrite eff_idL].
      * destruct (IH2 ρ Henv) as (T & next & Heval & HT).
        exists T, next. split; [exact Heval | now rewrite eff_idL].
  - intros n γ Γ M B1 B2 bound Htyped IH ρ Henv.
    destruct (IH ρ Henv) as (P & spent & Heval & HP).
    destruct P as [r W | m r γ' ρ' M' | m γ' ρ' M1 M2]; cbn in HP; try contradiction.
    destruct HP as [(T & next & Hnext & HT) _].
    exists T, (spent E+ next). split; [|exact HT].
    eapply E_Fst; [exact Heval | exact Hnext | reflexivity].
  - intros n γ Γ M B1 B2 bound Htyped IH ρ Henv.
    destruct (IH ρ Henv) as (P & spent & Heval & HP).
    destruct P as [r W | m r γ' ρ' M' | m γ' ρ' M1 M2]; cbn in HP; try contradiction.
    destruct HP as [_ (T & next & Hnext & HT)].
    exists T, (spent E+ next). split; [|exact HT].
    eapply E_Snd; [exact Heval | exact Hnext | reflexivity].
  - intros n γ Γ V N B γ1 γ2 bound Hv IHv Hn IHn -> ρ Henv.
    destruct (env_realizes_add γ1 γ2 Γ ρ Henv) as [Henv1 Henv2].
    destruct (IHv ρ Henv1) as (W & Heval & ->).
    destruct (IHn ρ Henv2) as (T & spent & Hnext & HT).
    exists T, spent. split; [|exact HT].
    eapply E_Seq; [exact Heval | exact Hnext | reflexivity].
  - intros n γ Γ q V M1 M2 A1 A2 B γ1 γ2 bound Hv IHv H1 IH1 H2 IH2 -> Hle ρ Henv.
    assert (Hq : q <> Qzero).
    { intro Hzero. rewrite Hzero in Hle. exact (Qnontrivial (grade_zero_le _ Hle)). }
    destruct (env_realizes_add (q Q* γ1) γ2 Γ ρ Henv) as [Hscaled Henv2].
    destruct (IHv ρ (env_realizes_scale q γ1 Γ ρ Hq Hscaled)) as (W & Heval & HW).
    destruct W as [| m γ' ρ' M | W1 W2 | W | W |]; cbn in HW; try contradiction.
    + destruct (IH1 _ (env_realizes_cons q γ2 A1 Γ W ρ (fun _ => HW) Henv2))
        as (T & spent & Hnext & HT).
      exists T, spent. split; [|exact HT].
      eapply E_Casel; [exact Heval | exact Hnext | reflexivity | exact Hle].
    + destruct (IH2 _ (env_realizes_cons q γ2 A2 Γ W ρ (fun _ => HW) Henv2))
        as (T & spent & Hnext & HT).
      exists T, spent. split; [|exact HT].
      eapply E_Caser; [exact Heval | exact Hnext | reflexivity | exact Hle].
  - intros n γ Γ bound Hzero -> ρ Henv.
    exists (CClosRet Qone VClosUnit), tick. split.
    + eapply E_Tick; [exact Hzero | reflexivity].
    + cbn. repeat split. apply subeff_refl.
  - intros n γ Γ M B γ' bound Htyped IH Hle ρ Henv.
    destruct (IH ρ (env_realizes_sub γ γ' Γ ρ Henv Hle)) as (T & spent & Heval & HT).
    exists T, spent. split; [|exact HT].
    eapply E_CSub; [exact Heval | exact Hle].
  - intros n γ Γ M B bound bound' Htyped IH Hle ρ Henv.
    destruct (IH ρ Henv) as (T & spent & Heval & HT).
    exists T, spent. split; [exact Heval |].
    eapply comp_realizes_effect; [exact HT |].
    intros tail Htail. eapply subeff_trans; eassumption.
  - intros n γ Γ q M N A B γ1 γ2 bound2 bound Hm IHm Hn IHn -> -> ρ Henv.
    assert (Hbody : env_realizes (Qzero .: γ2) (A .: Γ) (JUNK .: ρ)).
    { apply env_realizes_cons; [contradiction | exact Henv]. }
    destruct (IHn _ Hbody) as (T & spent & Hnext & HT).
    exists T, spent. split; [|exact HT].
    eapply E_LetRetZero; [exact Hnext | reflexivity].
Qed.

Theorem soundness :
  (forall V A, VWt null null V A -> exists W,
    EvalVal null null V W) /\
  (forall M q A ϕ, CWt null null M (CF q A) ϕ ->
    exists T ϕ1,
    EvalComp null null M T ϕ1 /\ ϕ1 E<= ϕ).
Proof.
  assert (Henv : env_realizes null null null) by (intros i; destruct i).
  destruct (typed_realizes 0 null null) as [Hval Hcomp].
  split.
  - intros V A Htyped. destruct (Hval V A Htyped null Henv) as (W & Heval & _).
    now exists W.
  - intros M q A ϕ Htyped.
    destruct (Hcomp M (CF q A) ϕ Htyped null Henv) as (T & spent & Heval & HT).
    destruct T as [r W | m r γ ρ N | m γ ρ N1 N2]; cbn in HT; try contradiction.
    destruct HT as (_ & Hbound & _).
    now exists (CClosRet r W), spent.
Qed.
