Require full.CBN.translation full.CBV.translation.
From Stdlib Require Import FunctionalExtensionality.
Import FunctionalExtensionality.
Import full.CBPV.typing.
Import full.CBPV.renaming.

(* grade transformation bundled with a renaming *)
Definition grade_up {n m} (G : gradeVec n -> gradeVec m) (δ : gradeVec (S n)) : gradeVec (S m) :=
  (δ None) .: G (fun i => δ (Some i)).

Definition G_shift {n} (γ : gradeVec n) : gradeVec (S n) := Qzero .: γ.

Definition GradeRen {n m} (ρ : fin n -> fin m) (G : gradeVec n -> gradeVec m) : Prop :=
  (forall γ1 γ2, G (γ1 Q+ γ2) = G γ1 Q+ G γ2) /\
  (forall q γ, G (q Q* γ) = q Q* G γ) /\
  (forall γ1 γ2, γ1 Q<= γ2 -> G γ1 Q<= G γ2) /\
  (G (0s) = 0s) /\
  (forall γ i, γ i = Qone -> (forall j, j <> i -> γ j = Qzero) ->
     G γ (ρ i) = Qone /\ (forall j, j <> ρ i -> G γ j = Qzero)).

Lemma grade_up_add : forall {n m} (G : gradeVec n -> gradeVec m),
  (forall γ1 γ2, G (γ1 Q+ γ2) = G γ1 Q+ G γ2) ->
  forall (δ1 δ2 : gradeVec (S n)),
  grade_up G (δ1 Q+ δ2) = grade_up G δ1 Q+ grade_up G δ2.
Proof.
  intros n m G Hadd δ1 δ2. apply functional_extensionality. intros [j0|].
  - unfold grade_up, gradeVecAdd. simpl.
    change (G ((fun i : fin n => δ1 (Some i)) Q+ (fun i : fin n => δ2 (Some i))) j0 =
            Qadd (G (fun i : fin n => δ1 (Some i)) j0) (G (fun i : fin n => δ2 (Some i)) j0)).
    rewrite Hadd. reflexivity.
  - reflexivity.
Qed.

Lemma grade_up_scale : forall {n m} (G : gradeVec n -> gradeVec m),
  (forall q γ, G (q Q* γ) = q Q* G γ) ->
  forall q (δ : gradeVec (S n)),
  grade_up G (q Q* δ) = q Q* grade_up G δ.
Proof.
  intros n m G Hscale q δ. apply functional_extensionality. intros [j0|].
  - unfold grade_up, gradeVecScale. simpl.
    change (G (q Q* (fun i : fin n => δ (Some i))) j0 =
            Qmult q (G (fun i : fin n => δ (Some i)) j0)).
    rewrite Hscale. reflexivity.
  - reflexivity.
Qed.

Lemma grade_up_zero : forall {n m} (G : gradeVec n -> gradeVec m),
  (G (0s) = 0s) -> grade_up G (0s : gradeVec (S n)) = 0s.
Proof.
  intros n m G Hzero. apply functional_extensionality. intros [j0|].
  - change (G (0s : gradeVec n) j0 = Qzero). rewrite Hzero. reflexivity.
  - reflexivity.
Qed.

Lemma grade_up_le : forall {n m} (G : gradeVec n -> gradeVec m),
  (forall γ1 γ2, γ1 Q<= γ2 -> G γ1 Q<= G γ2) ->
  forall (δ1 δ2 : gradeVec (S n)), δ1 Q<= δ2 -> grade_up G δ1 Q<= grade_up G δ2.
Proof.
  intros n m G Hle δ1 δ2 H. intros [j0|].
  - unfold grade_up. apply Hle. intro i. apply H.
  - unfold grade_up. apply H.
Qed.

Lemma GradeRen_up : forall {n m} {ρ : fin n -> fin m} {G : gradeVec n -> gradeVec m},
  GradeRen ρ G -> GradeRen (up_ren ρ) (grade_up G).
Proof.
  intros n m ρ G [Hadd [Hscale [Hle [Hzero Hvar]]]].
  split; [|split; [|split; [|split]]].
  - apply grade_up_add. exact Hadd.
  - apply grade_up_scale. exact Hscale.
  - apply grade_up_le. exact Hle.
  - apply grade_up_zero. exact Hzero.
  - intros δ i Hi Hzero_i.
    destruct i as [i0|].
    + assert (Hdelta_none : δ None = Qzero) by (apply Hzero_i; discriminate).
      split.
      * simpl.
        destruct (Hvar (fun i => δ (Some i)) i0) as [H1 H2].
        -- exact Hi.
        -- intros j Hj. apply Hzero_i. intro E. apply Hj. inversion E. reflexivity.
        -- exact H1.
      * intros j Hj. destruct j as [j0|].
        -- simpl.
           destruct (Hvar (fun i => δ (Some i)) i0) as [H1 H2].
           ++ exact Hi.
           ++ intros j' Hj'. apply Hzero_i. intro E. apply Hj'. inversion E. reflexivity.
           ++ apply H2. intro E. apply Hj. simpl. rewrite E. reflexivity.
        -- simpl. exact Hdelta_none.
    + split.
      * simpl. exact Hi.
      * intros j Hj. destruct j as [j0|].
        -- simpl.
           assert (Htail0 : (fun i : fin n => δ (Some i)) = (0s : gradeVec n)).
           { apply functional_extensionality. intro k. apply Hzero_i. discriminate. }
           rewrite Htail0.
           rewrite Hzero.
           reflexivity.
        -- exfalso; apply Hj; reflexivity.
Qed.

(* projection lemmas *)
Lemma GradeRen_add : forall {n m} {ρ : fin n -> fin m} {G : gradeVec n -> gradeVec m},
  GradeRen ρ G -> forall γ1 γ2, G (γ1 Q+ γ2) = G γ1 Q+ G γ2.
Proof. intros n m ρ G [H _]. exact H. Qed.
Lemma GradeRen_scale : forall {n m} {ρ : fin n -> fin m} {G : gradeVec n -> gradeVec m},
  GradeRen ρ G -> forall q γ, G (q Q* γ) = q Q* G γ.
Proof. intros n m ρ G [_ [H _]]. exact H. Qed.
Lemma GradeRen_le : forall {n m} {ρ : fin n -> fin m} {G : gradeVec n -> gradeVec m},
  GradeRen ρ G -> forall γ1 γ2, γ1 Q<= γ2 -> G γ1 Q<= G γ2.
Proof. intros n m ρ G [_ [_ [H _]]]. exact H. Qed.
Lemma GradeRen_zero : forall {n m} {ρ : fin n -> fin m} {G : gradeVec n -> gradeVec m},
  GradeRen ρ G -> G (0s) = 0s.
Proof. intros n m ρ G [_ [_ [_ [H _]]]]. exact H. Qed.
Lemma GradeRen_var : forall {n m} {ρ : fin n -> fin m} {G : gradeVec n -> gradeVec m},
  GradeRen ρ G -> forall γ i, γ i = Qone -> (forall j, j <> i -> γ j = Qzero) ->
    G γ (ρ i) = Qone /\ (forall j, j <> ρ i -> G γ j = Qzero).
Proof. intros n m ρ G [_ [_ [_ [_ H]]]]. exact H. Qed.

Definition VWt_ren_motive (n : nat) (γ : gradeVec n) (Γ : context n) (V : Val n) (A : ValTy) (_ : VWt γ Γ V A) : Prop :=
  forall m (ρ : fin n -> fin m) (G : gradeVec n -> gradeVec m) (Γ' : context m),
    GradeRen ρ G -> ren_match ρ Γ Γ' -> VWt (G γ) Γ' (ren_Val ρ V) A.
Definition CWt_ren_motive (n : nat) (γ : gradeVec n) (Γ : context n) (M : Comp n) (B : CompTy) (ϕ : E) (_ : CWt γ Γ M B ϕ) : Prop :=
  forall m (ρ : fin n -> fin m) (G : gradeVec n -> gradeVec m) (Γ' : context m),
    GradeRen ρ G -> ren_match ρ Γ Γ' -> CWt (G γ) Γ' (ren_Comp ρ M) B ϕ.

Lemma ren_Wt_mutual_conj : forall n (γ : gradeVec n) (Γ : context n),
  (forall V A (w : VWt γ Γ V A), VWt_ren_motive n γ Γ V A w)
  /\ (forall M B ϕ (w : CWt γ Γ M B ϕ), CWt_ren_motive n γ Γ M B ϕ w).
Proof.
  intros n0 γ0 Γ0.
  apply (Wt_mutual VWt_ren_motive CWt_ren_motive).
  - (* T_Var *)
    intros n γ Γ i Hi Hzero m ρ G Γ' HG Hctx. simpl.
    rewrite (Hctx i).
    apply T_Var.
    + exact (proj1 (GradeRen_var HG γ i Hi Hzero)).
    + exact (proj2 (GradeRen_var HG γ i Hi Hzero)).
  - (* T_Thunk *)
    intros n γ Γ M B ϕ c IH m ρ G Γ' HG Hctx. simpl.
    apply T_Thunk. apply IH; assumption.
  - (* T_Unit *)
    intros n γ Γ e m ρ G Γ' HG Hctx. simpl.
    apply T_Unit. rewrite e. exact (GradeRen_zero (ρ := ρ) HG).
  - (* T_VPair *)
    intros n γ Γ V1 V2 A1 A2 γ1 γ2 v1 IH1 v2 IH2 e m ρ G Γ' HG Hctx. simpl.
    rewrite e.
    rewrite (@GradeRen_add n m ρ G HG γ1 γ2).
    apply T_VPair with (γ1 := G γ1) (γ2 := G γ2).
    + apply IH1; assumption.
    + apply IH2; assumption.
    + reflexivity.
  - (* T_Inl *)
    intros n γ Γ V A1 A2 v IH m ρ G Γ' HG Hctx. simpl.
    apply T_Inl. apply IH; assumption.
  - (* T_Inr *)
    intros n γ Γ V A1 A2 v IH m ρ G Γ' HG Hctx. simpl.
    apply T_Inr. apply IH; assumption.
  - (* T_VSub *)
    intros n γ Γ V A γ' v IH g m ρ G Γ' HG Hctx. simpl.
    eapply T_VSub with (γ' := G γ').
    + apply IH; assumption.
    + exact (@GradeRen_le n m ρ G HG γ γ' g).
  - (* T_Abs *)
    intros n γ Γ q q' M A0 B ϕ c IH l m ρ G Γ' HG Hctx. simpl.
    eapply T_Abs.
    + apply (IH (S m) (up_ren ρ) (grade_up G) (A0 .: Γ')).
      * apply GradeRen_up. exact HG.
      * intro i. destruct i as [i0|]; simpl; [ apply Hctx | reflexivity ].
    + exact l.
  - (* T_App *)
    intros n γ Γ q M V A B γ1 γ2 ϕ c IHc v IHv e m ρ G Γ' HG Hctx. simpl.
    rewrite e, (@GradeRen_add n m ρ G HG γ1 (q Q* γ2)), (@GradeRen_scale n m ρ G HG q γ2).
    eapply T_App with (γ1 := G γ1) (γ2 := G γ2).
    + apply IHc; assumption.
    + apply IHv; assumption.
    + reflexivity.
  - (* T_Force *)
    intros n γ Γ V B ϕ v IH m ρ G Γ' HG Hctx. simpl.
    apply T_Force. apply IH; assumption.
  - (* T_Split *)
    intros n γ Γ q V N A1 A2 B γ1 γ2 ϕ v IHv c IHN e m ρ G Γ' HG Hctx. simpl.
    rewrite e, (@GradeRen_add n m ρ G HG (q Q* γ1) γ2), (@GradeRen_scale n m ρ G HG q γ1).
    eapply T_Split with (γ1 := G γ1) (γ2 := G γ2).
    + apply IHv; assumption.
    + apply (IHN (S (S m)) (up_ren (up_ren ρ)) (grade_up (grade_up G)) (A1 .: (A2 .: Γ'))).
      * apply GradeRen_up. apply GradeRen_up. exact HG.
      * intro i. destruct i as [i0|].
        -- destruct i0 as [i1|]; simpl; [ apply Hctx | reflexivity ].
        -- reflexivity.
    + reflexivity.
  - (* T_Ret *)
    intros n γ Γ q V A γ1 ϕ v IH e e0 m ρ G Γ' HG Hctx. simpl.
    rewrite e, e0, (@GradeRen_scale n m ρ G HG q γ1).
    eapply T_Ret with (γ1 := G γ1).
    + apply IH; assumption.
    + reflexivity.
    + reflexivity.
  - (* T_Let *)
    intros n γ Γ q1 q2 q' M N A0 B γ1 γ2 ϕ1 ϕ2 ϕ eq c IHc c0 IHN e0 e1 m ρ G Γ' HG Hctx. simpl.
    rewrite e0, (@GradeRen_add n m ρ G HG (q' Q* γ1) γ2), (@GradeRen_scale n m ρ G HG q' γ1).
    eapply T_Let with (γ1 := G γ1) (γ2 := G γ2).
    + exact eq.
    + apply IHc; assumption.
    + apply (IHN (S m) (up_ren ρ) (grade_up G) (A0 .: Γ')).
      * apply GradeRen_up. exact HG.
      * intro i. destruct i as [i0|]; simpl; [ apply Hctx | reflexivity ].
    + reflexivity.
    + exact e1.
  - (* T_CPair *)
    intros n γ Γ M1 M2 B1 B2 ϕ c1 IH1 c2 IH2 m ρ G Γ' HG Hctx. simpl.
    apply T_CPair.
    + apply IH1; assumption.
    + apply IH2; assumption.
  - (* T_Fst *)
    intros n γ Γ M B1 B2 ϕ c IH m ρ G Γ' HG Hctx. simpl.
    apply T_Fst with (B2 := B2). apply IH; assumption.
  - (* T_Snd *)
    intros n γ Γ M B1 B2 ϕ c IH m ρ G Γ' HG Hctx. simpl.
    apply T_Snd with (B1 := B1). apply IH; assumption.
  - (* T_Seq *)
    intros n γ Γ V N B γ1 γ2 ϕ v IHv c IHN e m ρ G Γ' HG Hctx. simpl.
    rewrite e, (@GradeRen_add n m ρ G HG γ1 γ2).
    eapply T_Seq with (γ1 := G γ1) (γ2 := G γ2).
    + apply IHv; assumption.
    + apply IHN; assumption.
    + reflexivity.
  - (* T_Case *)
    intros n γ Γ q V M1 M2 A1 A2 B γ1 γ2 ϕ v IHv c1 IH1 c2 IH2 e l m ρ G Γ' HG Hctx. simpl.
    rewrite e, (@GradeRen_add n m ρ G HG (q Q* γ1) γ2), (@GradeRen_scale n m ρ G HG q γ1).
    eapply T_Case with (γ1 := G γ1) (γ2 := G γ2).
    + apply IHv; assumption.
    + apply (IH1 (S m) (up_ren ρ) (grade_up G) (A1 .: Γ')).
      * apply GradeRen_up. exact HG.
      * intro i. destruct i as [i0|]; simpl; [ apply Hctx | reflexivity ].
    + apply (IH2 (S m) (up_ren ρ) (grade_up G) (A2 .: Γ')).
      * apply GradeRen_up. exact HG.
      * intro i. destruct i as [i0|]; simpl; [ apply Hctx | reflexivity ].
    + reflexivity.
    + exact l.
  - (* T_Tick *)
    intros n γ Γ ϕ e e0 m ρ G Γ' HG Hctx. simpl.
    rewrite e, e0.
    eapply T_Tick.
    + exact (GradeRen_zero (ρ := ρ) HG).
    + reflexivity.
  - (* T_CSub *)
    intros n γ Γ M B γ' ϕ c IH g m ρ G Γ' HG Hctx. simpl.
    eapply T_CSub with (γ' := G γ').
    + apply IH; assumption.
    + exact (@GradeRen_le n m ρ G HG γ γ' g).
  - (* T_SubEff *)
    intros n γ Γ M B ϕ ϕ' c IH s m ρ G Γ' HG Hctx. simpl.
    eapply T_SubEff.
    + apply IH; assumption.
    + exact s.
  - (* T_LetZero *)
    intros n γ Γ q1 M N A0 B γ1 γ2 ϕ2 ϕ c IHc c0 IHN e e0 m ρ G Γ' HG Hctx. simpl.
    rewrite e, e0.
    eapply T_LetZero with (γ1 := G γ1) (γ2 := G γ2).
    + apply IHc; assumption.
    + apply (IHN (S m) (up_ren ρ) (grade_up G) (A0 .: Γ')).
      * apply GradeRen_up. exact HG.
      * intro i. destruct i as [i0|]; simpl; [ apply Hctx | reflexivity ].
    + reflexivity.
    + reflexivity.
Qed.

(* ---------- grade arithmetic ---------- *)
Lemma Qone_mult_vec : forall {n} (γ : gradeVec n), Qone Q* γ = γ.
Proof. intros n γ. apply functional_extensionality. intro i. apply Qmult_lident. Qed.
Lemma Qzero_mult_vec : forall {n} (γ : gradeVec n), Qzero Q* γ = 0s.
Proof. intros n γ. apply functional_extensionality. intro i. apply Qzero_lannihilates. Qed.
Lemma Qmult_zero_vec : forall {n} (q : Q), q Q* (0s : gradeVec n) = 0s.
Proof. intros n q. apply functional_extensionality. intro i. apply Qzero_rannihilates. Qed.
Lemma add_zero_l : forall {n} (γ : gradeVec n), 0s Q+ γ = γ.
Proof. intros n γ. apply functional_extensionality. intro i. apply Qadd_lident. Qed.
Lemma add_zero_r : forall {n} (γ : gradeVec n), (γ Q+ 0s) = γ.
Proof. intros n γ. apply functional_extensionality. intro i. apply Qadd_rident. Qed.
Lemma cons_add : forall {n} (q1 q2 : Q) (γ1 γ2 : gradeVec n),
  (q1 .: γ1) Q+ (q2 .: γ2) = (Qadd q1 q2) .: (γ1 Q+ γ2).
Proof. intros. apply functional_extensionality. intros [i|]; reflexivity. Qed.
Lemma cons_scale : forall {n} (q q1 : Q) (γ : gradeVec n),
  q Q* (q1 .: γ) = (Qmult q q1) .: (q Q* γ).
Proof. intros. apply functional_extensionality. intros [i|]; reflexivity. Qed.

Lemma scale_one_cons : forall {n} (q : Q) (γ : gradeVec n),
  q Q* (Qone .: γ) = q .: (q Q* γ).
Proof. intros. rewrite cons_scale. rewrite Qmult_rident. reflexivity. Qed.

Lemma q_or_1_neq_zero : forall q, q_or_1 q <> Qzero.
Proof.
  intros q H. unfold q_or_1 in H.
  destruct (Qeqb q Qzero) eqn:E.
  - apply Qnontrivial. exact H.
  - apply Qeqb_eq in H. rewrite H in E. discriminate.
Qed.

Lemma q_or_1_idem : forall q, q_or_1 (q_or_1 q) = q_or_1 q.
Proof.
  intros q. unfold q_or_1 at 1.
  destruct (Qeqb (q_or_1 q) Qzero) eqn:E.
  - exfalso. apply (q_or_1_neq_zero q). apply Qeqb_eq. exact E.
  - reflexivity.
Qed.

Lemma q_or_1_one : q_or_1 Qone = Qone.
Proof.
  unfold q_or_1. destruct (Qeqb Qone Qzero); reflexivity.
Qed.

Lemma q_or_1_eq : forall q, q <> Qzero -> q_or_1 q = q.
Proof.
  intros q H. unfold q_or_1.
  destruct (Qeqb q Qzero) eqn:E.
  - exfalso. apply H. apply Qeqb_eq. exact E.
  - reflexivity.
Qed.

Lemma Qle_zero_one_false : ~ Qle Qzero Qone.
Proof.
  intro H.
  assert (Qle Qzero (Qadd Qone Qzero)) as Hq.
  { rewrite Qadd_rident. exact H. }
  destruct (Qsumzero Qone Qzero Hq) as [H1 _].
  exact (Qnontrivial H1).
Qed.

Lemma Qle_Qone_neq : forall q, Qle q Qone -> q <> Qzero.
Proof.
  intros q H E. subst q. exact (Qle_zero_one_false H).
Qed.

(* ---------- GradeRen for shift ---------- *)
Lemma GradeRen_shift : forall {n}, GradeRen (@shift n) (@G_shift n).
Proof.
  intros n. split; [|split; [|split; [|split]]].
  - intros γ1 γ2. apply functional_extensionality. intros [j|]; simpl.
    + reflexivity.
    + symmetry. apply Qadd_lident.
  - intros q γ. apply functional_extensionality. intros [j|]; simpl.
    + reflexivity.
    + symmetry. apply Qzero_rannihilates.
  - intros γ1 γ2 H [j|]; simpl.
    + apply H.
    + apply Qle_refl.
  - apply functional_extensionality. intros [j|]; reflexivity.
  - intros γ i Hi Hzero. split.
    + simpl. exact Hi.
    + intros j Hj. destruct j as [j0|].
      * simpl. apply Hzero. intro E. apply Hj. rewrite E. reflexivity.
      * reflexivity.
Qed.

(* ---------- user-facing renaming lemmas ---------- *)
Lemma VWt_ren : forall n (γ : gradeVec n) (Γ : context n) V A,
  VWt γ Γ V A ->
  forall m (ρ : fin n -> fin m) (G : gradeVec n -> gradeVec m) (Γ' : context m),
    GradeRen ρ G -> ren_match ρ Γ Γ' -> VWt (G γ) Γ' (ren_Val ρ V) A.
Proof. intros n γ Γ V A H m ρ G Γ' HG Hc. exact (proj1 (ren_Wt_mutual_conj n γ Γ) V A H m ρ G Γ' HG Hc). Qed.
Lemma CWt_ren : forall n (γ : gradeVec n) (Γ : context n) M B ϕ,
  CWt γ Γ M B ϕ ->
  forall m (ρ : fin n -> fin m) (G : gradeVec n -> gradeVec m) (Γ' : context m),
    GradeRen ρ G -> ren_match ρ Γ Γ' -> CWt (G γ) Γ' (ren_Comp ρ M) B ϕ.
Proof. intros n γ Γ M B ϕ H m ρ G Γ' HG Hc. exact (proj2 (ren_Wt_mutual_conj n γ Γ) M B ϕ H m ρ G Γ' HG Hc). Qed.
Lemma CWt_ren' : forall n (γ : gradeVec n) (Γ : context n) M B ϕ
  m (ρ : fin n -> fin m) (G : gradeVec n -> gradeVec m) (Gam : context m),
  CWt γ Γ M B ϕ -> GradeRen ρ G -> ren_match ρ Γ Gam -> CWt (G γ) Gam (ren_Comp ρ M) B ϕ.
Proof. intros. apply CWt_ren with (n := n) (γ := γ) (Γ := Γ) (M := M) (B := B) (ϕ := ϕ) (m := m) (ρ := ρ) (G := G) (Γ' := Gam); assumption. Qed.

Lemma wt_var_zero : forall {n} (A : ValTy) (Γ : context n),
  VWt (Qone .: (0s : gradeVec n)) (A .: Γ) (var_Val var_zero) A.
Proof.
  intros n A Γ. refine (@T_Var (S n) (Qone .: 0s) (A .: Γ) var_zero _ _).
  - reflexivity.
  - intros [j|] Hj; [reflexivity | exfalso; apply Hj; reflexivity].
Qed.

Module CBN.
Import full.CBN.translation.

Lemma ctx_cons : forall {n} (T : Ty) (Γ : contextL n),
  translateContext (T .: Γ) = VThunk ϵ (translateType T) .: translateContext Γ.
Proof. intros. apply functional_extensionality. intros [i|]; reflexivity. Qed.

Theorem cbn_translation_correct :
    forall n (γ : gradeVec n) (Γ : contextL n) e T,
    Wt γ Γ e T ->
    CWt γ (translateContext Γ) (translateTerm e) (translateType T) ϵ.
Proof.
  intros n γ Γ e T H.
  induction H as [
    n γ Γ i Hi Hzero
  | n γ Γ q q' e0 T1 T2 Hp IH Hle
  | n γ Γ q e1 e2 T1 T2 γ1 γ2 H1 IH1 H2 IH2 eeq
  | n γ Γ eeq
  | n γ Γ e1 e2 T0 γ1 γ2 H1 IH1 H2 IH2 eeq
  | n γ Γ e0 T1 T2 Hp IH
  | n γ Γ e0 T1 T2 Hp IH
  | n γ Γ e1 e2 T1 T2 H1 IH1 H2 IH2
  | n γ Γ e0 T1 T2 Hp IH
  | n γ Γ e0 T1 T2 Hp IH
  | n γ Γ q e0 e1 e2 T1 T2 T0 γ1 γ2 H1 IH1 H2 IH2 H3 IH3 eeq Hle
  | n γ Γ q e0 T0 γ1 Hp IH eeq
  | n γ Γ q1 q2 q2' e1 e2 T1 T2 γ1 γ2 qeq H1 IH1 H2 IH2 eeq
  | n γ Γ e0 T0 γ' Hp IH Hle
  | n γ Γ e0 T0 Hp IH
  | n γ Γ q' q e1 e2 T1 T2 γ1 γ2 ϕ1 ϕ2 ϕ qeq H1 IH1 H2 IH2 eeq effeq
  | n γ Γ e0 T0 ϕ ϕ' Hp IH Hsub
  | n γ Γ eeq
  ].
  - (* T_var *)
    simpl. eapply T_Force with (V := var_Val i) (B := translateType (Γ i)) (ϕ := ϵ).
    change (VWt γ (translateContext Γ) (var_Val i) (translateContext Γ i)).
    apply T_Var; assumption.
  - (* T_abs *)
    simpl. eapply T_Abs.
    + rewrite <- ctx_cons. exact IH.
    + exact Hle.
  - (* T_app *)
    simpl. rewrite eeq.
    eapply T_App with (γ1 := γ1) (γ2 := γ2).
    + exact IH1.
    + apply T_Thunk. exact IH2.
    + reflexivity.
  - (* T_unit *)
    simpl. rewrite eeq.
    eapply T_Ret with (γ1 := (0s : gradeVec n)).
    + apply T_Unit. reflexivity.
    + symmetry. apply Qone_mult_vec.
    + reflexivity.
  - (* T_seq *)
    simpl. rewrite eeq.
    eapply T_Let with (q1 := Qone) (q2 := Qone) (q' := Qone) (γ1 := γ1) (γ2 := γ2).
    + symmetry. apply q_or_1_one.
    + exact IH1.
    + rewrite Qmult_lident.
      eapply T_Seq with (γ1 := Qone .: 0s) (γ2 := Qzero .: γ2).
      * apply wt_var_zero.
      * exact (@CWt_ren' n γ2 (translateContext Γ) (translateTerm e2) (translateType T0) ϵ
                (S n) shift G_shift (VUnit .: translateContext Γ)
                IH2 GradeRen_shift (fun i => eq_refl)).
      * rewrite cons_add, Qadd_rident, add_zero_l. reflexivity.
    + rewrite Qone_mult_vec. reflexivity.
    + symmetry. apply eff_idL.
  - (* T_inl *)
    simpl. eapply T_Ret with (γ1 := γ).
    + eapply T_Inl. apply T_Thunk. exact IH.
    + symmetry. apply Qone_mult_vec.
    + reflexivity.
  - (* T_inr *)
    simpl. eapply T_Ret with (γ1 := γ).
    + eapply T_Inr. apply T_Thunk. exact IH.
    + symmetry. apply Qone_mult_vec.
    + reflexivity.
  - (* T_prod *)
    simpl. apply T_CPair; [exact IH1 | exact IH2].
  - (* T_fst *)
    simpl. eapply T_Fst with (B2 := translateType T2). exact IH.
  - (* T_snd *)
    simpl. eapply T_Snd with (B1 := translateType T1). exact IH.
  - (* T_case *)
    simpl. rewrite eeq.
    assert (Hq : q <> Qzero) by (apply Qle_Qone_neq; exact Hle).
    eapply T_Let with (q1 := Qone) (q2 := q) (q' := q) (γ1 := γ1) (γ2 := γ2).
    + symmetry. apply q_or_1_eq. exact Hq.
    + exact IH1.
    + rewrite Qmult_lident.
      eapply T_Case with (A1 := VThunk ϵ (translateType T1)) (A2 := VThunk ϵ (translateType T2))
                         (γ1 := Qone .: 0s) (γ2 := Qzero .: γ2).
      * apply wt_var_zero.
      * apply (@CWt_ren' (S n) (q .: γ2) (translateContext (T1 .: Γ)) (translateTerm e1) (translateType T0) ϵ
                (S (S n)) up_ren' (grade_up G_shift)
                (VThunk ϵ (translateType T1) .: (VSum (VThunk ϵ (translateType T1)) (VThunk ϵ (translateType T2)) .: translateContext Γ))
                IH2 (GradeRen_up GradeRen_shift)).
        -- intro i; destruct i as [j|]; reflexivity.
      * apply (@CWt_ren' (S n) (q .: γ2) (translateContext (T2 .: Γ)) (translateTerm e2) (translateType T0) ϵ
                (S (S n)) up_ren' (grade_up G_shift)
                (VThunk ϵ (translateType T2) .: (VSum (VThunk ϵ (translateType T1)) (VThunk ϵ (translateType T2)) .: translateContext Γ))
                IH3 (GradeRen_up GradeRen_shift)).
        -- intro i; destruct i as [j|]; reflexivity.
      * rewrite scale_one_cons, Qmult_zero_vec, cons_add, Qadd_rident, add_zero_l. reflexivity.
      * exact Hle.
    + reflexivity.
    + symmetry. apply eff_idL.
  - (* T_box *)
    simpl. rewrite eeq.
    eapply T_Ret with (γ1 := γ1).
    + apply T_Thunk. exact IH.
    + reflexivity.
    + reflexivity.
  - (* T_unbox *)
    simpl.
    eapply T_Let with (q1 := q1) (q2 := q2) (q' := q2') (γ1 := γ1) (γ2 := γ2).
    + exact qeq.
    + exact IH1.
    + rewrite <- ctx_cons. exact IH2.
    + exact eeq.
    + symmetry. apply eff_idL.
  - (* T_sub *)
    simpl. eapply T_CSub with (γ' := γ').
    + exact IH.
    + exact Hle.
  - (* T_ret *)
    simpl. eapply T_Ret with (γ1 := γ).
    + apply T_Thunk.
      eapply T_Ret with (γ1 := γ).
      * apply T_Thunk. exact IH.
      * symmetry. apply Qone_mult_vec.
      * reflexivity.
    + symmetry. apply Qone_mult_vec.
    + reflexivity.
  - (* T_bind *)
    simpl.
    assert (Hq0 : q_or_1 (q_or_1 q) = q_or_1 q) by apply q_or_1_idem.
    eapply T_Ret with (γ1 := γ).
    + apply T_Thunk.
      eapply T_Let with (q1 := Qone) (q2 := q_or_1 q) (q' := q_or_1 (q_or_1 q)) (γ1 := γ1) (γ2 := γ2).
      * reflexivity.
      * (* X *)
        eapply T_Let with (q1 := Qone) (q2 := Qone) (q' := Qone) (γ1 := γ1) (γ2 := (0s : gradeVec n)).
        -- symmetry. apply q_or_1_one.
        -- exact IH1.
        -- rewrite Qmult_lident.
           eapply T_Force with (V := var_Val var_zero) (B := CF Qone (VThunk ϵ (translateType T1))).
           apply wt_var_zero.
        -- rewrite Qone_mult_vec. symmetry. apply add_zero_r.
        -- symmetry. apply eff_idL.
      * (* Y *)
        rewrite Hq0, <- qeq, Qmult_lident.
        eapply T_Let with (q1 := Qone) (q2 := Qone) (q' := Qone) (γ1 := q' .: γ2) (γ2 := (0s : gradeVec (S n))).
        -- symmetry. apply q_or_1_one.
        -- rewrite <- ctx_cons. exact IH2.
        -- rewrite Qmult_lident.
           eapply T_Force with (V := var_Val var_zero) (B := CF Qone (VThunk ϵ (translateType T2))).
           apply wt_var_zero.
        -- rewrite Qone_mult_vec. symmetry. apply add_zero_r.
        -- symmetry. apply eff_idL.
      * rewrite Hq0, <- qeq, eeq. reflexivity.
      * rewrite effeq. reflexivity.
    + symmetry. apply Qone_mult_vec.
    + reflexivity.
  - (* T_coerce *)
    simpl. eapply T_Ret with (γ1 := γ).
    + apply T_Thunk.
      eapply T_SubEff.
      * eapply T_Let with (q1 := Qone) (q2 := Qone) (q' := Qone) (γ1 := γ) (γ2 := (0s : gradeVec n)).
        -- symmetry. apply q_or_1_one.
        -- exact IH.
        -- rewrite Qmult_lident.
           eapply T_Force with (V := var_Val var_zero) (B := CF Qone (VThunk ϵ (translateType T0))).
           apply wt_var_zero.
        -- rewrite Qone_mult_vec. symmetry. apply add_zero_r.
        -- symmetry. apply eff_idL.
      * exact Hsub.
    + symmetry. apply Qone_mult_vec.
    + reflexivity.
  - (* T_tickT *)
    simpl. rewrite eeq.
    eapply T_Ret with (γ1 := (0s : gradeVec n)).
    + apply T_Thunk.
      eapply T_Let with (q1 := Qone) (q2 := Qone) (q' := Qone) (γ1 := (0s : gradeVec n)) (γ2 := (0s : gradeVec n)).
      * symmetry. apply q_or_1_one.
      * apply T_Tick; reflexivity.
      * rewrite Qmult_lident.
        eapply T_Ret with (γ1 := Qone .: (0s : gradeVec n)).
        -- apply T_Thunk.
           eapply T_Ret with (γ1 := Qone .: (0s : gradeVec n)).
           ++ apply wt_var_zero.
           ++ rewrite Qone_mult_vec. reflexivity.
           ++ reflexivity.
        -- rewrite Qone_mult_vec. reflexivity.
        -- reflexivity.
      * rewrite Qone_mult_vec, add_zero_l. reflexivity.
      * symmetry. apply eff_idR.
    + symmetry. apply Qone_mult_vec.
    + reflexivity.
Qed.

End CBN.

Module CBV.
Import full.CBV.translation.

Lemma ctx_cons : forall {n} (T : Ty) (Γ : contextL n),
  translateContext (T .: Γ) = translateType T .: translateContext Γ.
Proof. intros. apply functional_extensionality. intros [i|]; reflexivity. Qed.

Lemma wt_var_one : forall {n} (A B : ValTy) (Γ : context n),
  VWt (Qzero .: (Qone .: (0s : gradeVec n))) (B .: (A .: Γ)) (var_Val (shift var_zero)) A.
Proof.
  intros n A B Γ.
  refine (@T_Var (S (S n)) (Qzero .: (Qone .: 0s)) (B .: (A .: Γ)) (shift var_zero) _ _).
  - reflexivity.
  - intros [j|] Hj.
    + destruct j as [j1|].
      * reflexivity.
      * exfalso; apply Hj; reflexivity.
    + reflexivity.
Qed.

Theorem cbv_translation_correct :
    forall n (γ : gradeVec n) (Γ : contextL n) e T,
    Wt γ Γ e T ->
    CWt γ (translateContext Γ) (translateTerm e) (CF Qone (translateType T)) ϵ.
Proof.
  intros n γ Γ e T H.
  induction H as [
    n γ Γ i Hi Hzero
  | n γ Γ q q' e0 T1 T2 Hp IH Hle
  | n γ Γ q q' e1 e2 T1 T2 γ1 γ2 qeq H1 IH1 H2 IH2 eeq
  | n γ Γ eeq
  | n γ Γ e1 e2 T0 γ1 γ2 H1 IH1 H2 IH2 eeq
  | n γ Γ e1 e2 T1 T2 γ1 γ2 H1 IH1 H2 IH2 eeq
  | n γ Γ q q' e1 e2 T1 T2 γ1 γ2 qeq H1 IH1 H2 IH2 eeq
  | n γ Γ e0 T1 T2 Hp IH
  | n γ Γ e0 T1 T2 Hp IH
  | n γ Γ q e0 e1 e2 T1 T2 T0 γ1 γ2 H1 IH1 H2 IH2 H3 IH3 eeq Hle
  | n γ Γ q q' e0 T0 γ1 qeq Hp IH eeq
  | n γ Γ q1 q2 q2' e1 e2 T1 T2 γ1 γ2 qeq H1 IH1 H2 IH2 eeq
  | n γ Γ e0 T0 γ' Hp IH Hle
  | n γ Γ e0 T0 ϕ Hp IH phieq
  | n γ Γ q' q e1 e2 T1 T2 γ1 γ2 ϕ1 ϕ2 ϕ qeq H1 IH1 H2 IH2 eeq effeq
  | n γ Γ e0 T0 ϕ ϕ' Hp IH Hsub
  | n γ Γ eeq
  ].
  - (* T_var *)
    simpl. eapply T_Ret with (γ1 := γ).
    + change (VWt γ (translateContext Γ) (var_Val i) (translateContext Γ i)).
      eapply T_Var; assumption.
    + symmetry. apply Qone_mult_vec.
    + reflexivity.
  - (* T_abs *)
    simpl. eapply T_Ret with (γ1 := γ).
    + apply T_Thunk. eapply T_Abs.
      * rewrite <- ctx_cons. exact IH.
      * exact Hle.
    + symmetry. apply Qone_mult_vec.
    + reflexivity.
  - (* T_app *)
    simpl.
    assert (Hq' : q' <> Qzero) by (rewrite qeq; apply q_or_1_neq_zero).
    assert (Hq0 : q_or_1 q' = q') by (apply q_or_1_eq; exact Hq').
    eapply T_Let with (q1 := Qone) (q2 := Qone) (q' := Qone) (γ1 := γ1) (γ2 := q' Q* γ2).
    + symmetry. apply q_or_1_one.
    + exact IH1.
    + rewrite Qmult_lident.
      eapply T_Let with (q1 := Qone) (q2 := q) (q' := q') (γ1 := Qzero .: γ2) (γ2 := Qone .: (0s : gradeVec n)).
      * exact qeq.
      * exact (@CWt_ren' n γ2 (translateContext Γ) (translateTerm e2) (CF Qone (translateType T1)) ϵ
               (S n) shift G_shift (translateType (Abs q' T1 T2) .: translateContext Γ)
               IH2 GradeRen_shift (fun i => eq_refl)).
      * rewrite Qmult_lident.
        eapply T_App with (A := translateType T1) (B := CF Qone (translateType T2))
                           (γ1 := Qzero .: (Qone .: 0s)) (γ2 := Qone .: 0s).
        -- eapply T_Force with (V := var_Val (shift var_zero)).
           apply wt_var_one.
        -- apply wt_var_zero.
        -- rewrite scale_one_cons, Qmult_zero_vec, cons_add, Qadd_lident, add_zero_r. reflexivity.
      * rewrite cons_scale, Qzero_rannihilates, cons_add, Qadd_lident, add_zero_r. reflexivity.
      * symmetry. apply eff_idL.
    + rewrite Qone_mult_vec, eeq. reflexivity.
    + symmetry. apply eff_idL.
  - (* T_unit *)
    simpl. rewrite eeq.
    eapply T_Ret with (γ1 := (0s : gradeVec n)).
    + apply T_Unit. reflexivity.
    + symmetry. apply Qone_mult_vec.
    + reflexivity.
  - (* T_seq *)
    simpl. rewrite eeq.
    eapply T_Let with (q1 := Qone) (q2 := Qone) (q' := Qone) (γ1 := γ1) (γ2 := γ2).
    + symmetry. apply q_or_1_one.
    + exact IH1.
    + rewrite Qmult_lident.
      eapply T_Seq with (γ1 := Qone .: 0s) (γ2 := Qzero .: γ2).
      * apply wt_var_zero.
      * exact (@CWt_ren' n γ2 (translateContext Γ) (translateTerm e2) (CF Qone (translateType T0)) ϵ
               (S n) shift G_shift (VUnit .: translateContext Γ)
               IH2 GradeRen_shift (fun i => eq_refl)).
      * rewrite cons_add, Qadd_rident, add_zero_l. reflexivity.
    + rewrite Qone_mult_vec. reflexivity.
    + symmetry. apply eff_idL.
  - (* T_pair *)
    simpl. rewrite eeq.
    eapply T_Let with (q1 := Qone) (q2 := Qone) (q' := Qone) (γ1 := γ1) (γ2 := γ2).
    + symmetry. apply q_or_1_one.
    + exact IH1.
    + rewrite Qmult_lident.
      eapply T_Let with (q1 := Qone) (q2 := Qone) (q' := Qone) (γ1 := Qzero .: γ2) (γ2 := Qone .: (0s : gradeVec n)).
      * symmetry. apply q_or_1_one.
      * exact (@CWt_ren' n γ2 (translateContext Γ) (translateTerm e2) (CF Qone (translateType T2)) ϵ
               (S n) shift G_shift (translateType T1 .: translateContext Γ)
               IH2 GradeRen_shift (fun i => eq_refl)).
      * rewrite Qmult_lident.
        eapply T_Ret with (γ1 := Qone .: (Qone .: 0s)).
        -- eapply T_VPair with (γ1 := Qzero .: (Qone .: 0s)) (γ2 := Qone .: 0s).
           ++ apply wt_var_one.
           ++ apply wt_var_zero.
           ++ rewrite cons_add, Qadd_lident, add_zero_r. reflexivity.
        -- rewrite Qone_mult_vec. reflexivity.
        -- reflexivity.
      * rewrite cons_scale, Qzero_rannihilates, cons_add, Qadd_lident, add_zero_r, Qone_mult_vec. reflexivity.
      * symmetry. apply eff_idL.
    + rewrite Qone_mult_vec. reflexivity.
    + symmetry. apply eff_idL.
  - (* T_split *)
    simpl.
    assert (Hq' : q_or_1 q <> Qzero) by apply q_or_1_neq_zero.
    assert (Hq0 : q_or_1 (q_or_1 q) = q_or_1 q) by apply q_or_1_idem.
    eapply T_Let with (q1 := Qone) (q2 := q_or_1 q) (q' := q_or_1 (q_or_1 q)) (γ1 := γ1) (γ2 := γ2).
    + reflexivity.
    + exact IH1.
    + rewrite Hq0, <- qeq, Qmult_lident.
      eapply T_Split with (A1 := translateType T1) (A2 := translateType T2)
                          (γ1 := Qone .: 0s) (γ2 := Qzero .: γ2).
      * apply wt_var_zero.
      * apply (@CWt_ren' (S (S n)) (q' .: (q' .: γ2)) (translateContext (T1 .: (T2 .: Γ)))
               (translateTerm e2) (CF Qone (translateType T2)) ϵ
               (S (S (S n))) up2_ren' (grade_up (grade_up G_shift))
               (translateType T1 .: (translateType T2 .: (VPair (translateType T1) (translateType T2) .: translateContext Γ)))
               IH2 (GradeRen_up (GradeRen_up GradeRen_shift))).
        -- intro i. destruct i as [i1|].
           ++ destruct i1 as [i2|]; reflexivity.
           ++ reflexivity.
      * rewrite scale_one_cons, Qmult_zero_vec, cons_add, Qadd_rident, add_zero_l. reflexivity.
    + rewrite Hq0, <- qeq, eeq. reflexivity.
    + symmetry. apply eff_idL.
  - (* T_inl *)
    simpl. eapply T_Let with (q1 := Qone) (q2 := Qone) (q' := Qone) (γ1 := γ) (γ2 := (0s : gradeVec n)).
    + symmetry. apply q_or_1_one.
    + exact IH.
    + rewrite Qmult_lident.
      eapply T_Ret with (γ1 := Qone .: 0s).
      * eapply T_Inl. apply wt_var_zero.
      * rewrite Qone_mult_vec. reflexivity.
      * reflexivity.
    + rewrite Qone_mult_vec, add_zero_r. reflexivity.
    + symmetry. apply eff_idL.
  - (* T_inr *)
    simpl. eapply T_Let with (q1 := Qone) (q2 := Qone) (q' := Qone) (γ1 := γ) (γ2 := (0s : gradeVec n)).
    + symmetry. apply q_or_1_one.
    + exact IH.
    + rewrite Qmult_lident.
      eapply T_Ret with (γ1 := Qone .: 0s).
      * eapply T_Inr. apply wt_var_zero.
      * rewrite Qone_mult_vec. reflexivity.
      * reflexivity.
    + rewrite Qone_mult_vec, add_zero_r. reflexivity.
    + symmetry. apply eff_idL.
  - (* T_case *)
    simpl. rewrite eeq.
    assert (Hq : q <> Qzero) by (apply Qle_Qone_neq; exact Hle).
    eapply T_Let with (q1 := Qone) (q2 := q) (q' := q) (γ1 := γ1) (γ2 := γ2).
    + symmetry. apply q_or_1_eq. exact Hq.
    + exact IH1.
    + rewrite Qmult_lident.
      eapply T_Case with (A1 := translateType T1) (A2 := translateType T2)
                         (γ1 := Qone .: 0s) (γ2 := Qzero .: γ2).
      * apply wt_var_zero.
      * apply (@CWt_ren' (S n) (q .: γ2) (translateContext (T1 .: Γ)) (translateTerm e1) (CF Qone (translateType T0)) ϵ
               (S (S n)) up_ren' (grade_up G_shift)
               (translateType T1 .: (VSum (translateType T1) (translateType T2) .: translateContext Γ))
               IH2 (GradeRen_up GradeRen_shift)).
        -- intro i; destruct i as [j|]; reflexivity.
      * apply (@CWt_ren' (S n) (q .: γ2) (translateContext (T2 .: Γ)) (translateTerm e2) (CF Qone (translateType T0)) ϵ
               (S (S n)) up_ren' (grade_up G_shift)
               (translateType T2 .: (VSum (translateType T1) (translateType T2) .: translateContext Γ))
               IH3 (GradeRen_up GradeRen_shift)).
        -- intro i; destruct i as [j|]; reflexivity.
      * rewrite scale_one_cons, Qmult_zero_vec, cons_add, Qadd_rident, add_zero_l. reflexivity.
      * exact Hle.
    + reflexivity.
    + symmetry. apply eff_idL.
  - (* T_box *)
    simpl.
    assert (Hq0 : q_or_1 q' = q') by (apply q_or_1_eq; rewrite qeq; apply q_or_1_neq_zero).
    eapply T_Let with (q1 := Qone) (q2 := q) (q' := q') (γ1 := γ1) (γ2 := (0s : gradeVec n)).
    + exact qeq.
    + exact IH.
    + rewrite Qmult_lident, <- qeq.
      eapply T_Ret with (γ1 := q' .: (0s : gradeVec n)).
      * apply T_Thunk.
        eapply T_Ret with (γ1 := Qone .: (0s : gradeVec n)).
        -- apply wt_var_zero.
        -- rewrite scale_one_cons, Qmult_zero_vec. reflexivity.
        -- reflexivity.
      * rewrite Qone_mult_vec. reflexivity.
      * reflexivity.
    + rewrite eeq. rewrite add_zero_r. reflexivity.
    + symmetry. apply eff_idL.
  - (* T_unbox *)
    simpl.
    eapply T_Let with (q1 := Qone) (q2 := q2) (q' := q2') (γ1 := γ1) (γ2 := γ2).
    + exact qeq.
    + exact IH1.
    + rewrite Qmult_lident.
      eapply T_Let with (q1 := q1) (q2 := q2) (q' := q2') (γ1 := Qone .: 0s) (γ2 := Qzero .: γ2).
      * exact qeq.
      * eapply T_Force with (V := var_Val var_zero) (B := CF q1 (translateType T1)).
        -- apply wt_var_zero.
      * apply (@CWt_ren' (S n) ((Qmult q1 q2') .: γ2) (translateContext (T1 .: Γ)) (translateTerm e2) (CF Qone (translateType T2)) ϵ
               (S (S n)) up_ren' (grade_up G_shift)
               (translateType T1 .: (VThunk ϵ (CF q1 (translateType T1)) .: translateContext Γ))
               IH2 (GradeRen_up GradeRen_shift)).
        -- intro i; destruct i as [j|]; reflexivity.
      * rewrite scale_one_cons, Qmult_zero_vec, cons_add, Qadd_rident, add_zero_l. reflexivity.
      * symmetry. apply eff_idL.
    + exact eeq.
    + symmetry. apply eff_idL.
  - (* T_sub *)
    simpl. eapply T_CSub with (γ' := γ').
    + exact IH.
    + exact Hle.
  - (* T_ret *)
    simpl. rewrite phieq.
    eapply T_Ret with (γ1 := γ).
    + apply T_Thunk. exact IH.
    + symmetry. apply Qone_mult_vec.
    + reflexivity.
  - (* T_bind *)
    simpl.
    eapply T_Ret with (γ1 := γ).
    + apply T_Thunk.
      eapply T_Let with (q1 := Qone) (q2 := q) (q' := q') (γ1 := γ1) (γ2 := γ2).
      * exact qeq.
      * (* X *)
        eapply T_Let with (q1 := Qone) (q2 := Qone) (q' := Qone) (γ1 := γ1) (γ2 := (0s : gradeVec n)).
        -- symmetry. apply q_or_1_one.
        -- exact IH1.
        -- rewrite Qmult_lident.
           eapply T_Force with (V := var_Val var_zero) (B := CF Qone (translateType T1)).
           apply wt_var_zero.
        -- rewrite Qone_mult_vec. symmetry. apply add_zero_r.
        -- symmetry. apply eff_idL.
      * (* Y *)
        rewrite Qmult_lident.
        eapply T_Let with (q1 := Qone) (q2 := Qone) (q' := Qone) (γ1 := q' .: γ2) (γ2 := (0s : gradeVec (S n))).
        -- symmetry. apply q_or_1_one.
        -- rewrite <- ctx_cons. exact IH2.
        -- rewrite Qmult_lident.
           eapply T_Force with (V := var_Val var_zero) (B := CF Qone (translateType T2)).
           apply wt_var_zero.
        -- rewrite Qone_mult_vec. symmetry. apply add_zero_r.
        -- symmetry. apply eff_idL.
      * exact eeq.
      * exact effeq.
    + symmetry. apply Qone_mult_vec.
    + reflexivity.
  - (* T_coerce *)
    simpl. eapply T_Ret with (γ1 := γ).
    + apply T_Thunk.
      eapply T_SubEff.
      * eapply T_Let with (q1 := Qone) (q2 := Qone) (q' := Qone) (γ1 := γ) (γ2 := (0s : gradeVec n)).
        -- symmetry. apply q_or_1_one.
        -- exact IH.
        -- rewrite Qmult_lident.
           eapply T_Force with (V := var_Val var_zero) (B := CF Qone (translateType T0)).
           apply wt_var_zero.
        -- rewrite Qone_mult_vec. symmetry. apply add_zero_r.
        -- symmetry. apply eff_idL.
      * exact Hsub.
    + symmetry. apply Qone_mult_vec.
    + reflexivity.
  - (* T_tickT *)
    simpl. rewrite eeq.
    eapply T_Ret with (γ1 := (0s : gradeVec n)).
    + apply T_Thunk.
      eapply T_Let with (q1 := Qone) (q2 := Qone) (q' := Qone) (γ1 := (0s : gradeVec n)) (γ2 := (0s : gradeVec n)).
      * symmetry. apply q_or_1_one.
      * apply T_Tick; reflexivity.
      * rewrite Qmult_lident.
        eapply T_Ret with (γ1 := Qone .: (0s : gradeVec n)).
        -- apply wt_var_zero.
        -- rewrite Qone_mult_vec. reflexivity.
        -- reflexivity.
      * rewrite Qone_mult_vec, add_zero_l. reflexivity.
      * symmetry. apply eff_idR.
    + symmetry. apply Qone_mult_vec.
    + reflexivity.
Qed.

End CBV.
