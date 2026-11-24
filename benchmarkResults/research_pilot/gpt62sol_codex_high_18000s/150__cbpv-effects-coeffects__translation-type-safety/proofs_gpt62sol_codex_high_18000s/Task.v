Require full.CBN.translation full.CBV.translation.
Require Import full.CBPV.renaming.
From Stdlib Require Import FunctionalExtensionality.

Module TranslationTyping.

Local Open Scope subst_scope.

Lemma grade_add_cons {n} a b (γ δ : gradeVec n) :
  (a .: γ) Q+ (b .: δ) = Qadd a b .: (γ Q+ δ).
Proof. apply functional_extensionality. intros [i|]; reflexivity. Qed.

Lemma grade_scale_cons {n} q a (γ : gradeVec n) :
  q Q* (a .: γ) = Qmult q a .: (q Q* γ).
Proof. apply functional_extensionality. intros [i|]; reflexivity. Qed.

Lemma grade_add_zero_l {n} (γ : gradeVec n) : (0s) Q+ γ = γ.
Proof. apply functional_extensionality. intro i. apply Qadd_lident. Qed.

Lemma grade_add_zero_r {n} (γ : gradeVec n) : γ Q+ (0s) = γ.
Proof. apply functional_extensionality. intro i. apply Qadd_rident. Qed.

Lemma grade_scale_one {n} (γ : gradeVec n) : Qone Q* γ = γ.
Proof. apply functional_extensionality. intro i. apply Qmult_lident. Qed.

Lemma grade_scale_zero {n} q : q Q* (0s : gradeVec n) = 0s.
Proof. apply functional_extensionality. intro i. apply Qzero_rannihilates. Qed.

Lemma q_or_1_nonzero q : q <> Qzero -> q_or_1 q = q.
Proof.
  intros H. unfold q_or_1. destruct (Qeqb q Qzero) eqn:Hq.
  - exfalso. apply H. now apply Qeqb_eq.
  - reflexivity.
Qed.

Lemma q_or_1_one : q_or_1 Qone = Qone.
Proof. apply q_or_1_nonzero, Qnontrivial. Qed.

Lemma q_or_1_idem q : q_or_1 (q_or_1 q) = q_or_1 q.
Proof.
  unfold q_or_1 at 2 3. destruct (Qeqb q Qzero) eqn:Hq.
  - apply q_or_1_one.
  - unfold q_or_1. now rewrite Hq.
Qed.

Lemma q_or_1_case q : Qle q Qone -> q_or_1 q = q.
Proof.
  intros H. apply q_or_1_nonzero. intros ->.
  (* The case rule's bound excludes zero by Qsumzero and Qnontrivial. *)
  apply Qnontrivial.
  rewrite <- (Qadd_lident Qone) in H.
  exact (proj2 (Qsumzero Qzero Qone H)).
Qed.

Create HintDb translation_grades.
#[export] Hint Rewrite @grade_add_cons @grade_scale_cons @grade_add_zero_l
  @grade_add_zero_r @grade_scale_one @grade_scale_zero Qadd_lident Qadd_rident
  Qmult_lident Qmult_rident Qzero_rannihilates @eff_idL @eff_idR
  q_or_1_one q_or_1_idem : translation_grades.

(* An insertion adds one slot, possibly underneath existing binders. *)
Inductive insertion : nat -> Type :=
| insert_here n : insertion n
| insert_under n : insertion n -> insertion (S n).

Arguments insert_under {n}.

Fixpoint insert_ren {n} (w : insertion n) : ren n (S n) :=
  match w with
  | insert_here _ => shift
  | insert_under w' => up_ren (insert_ren w')
  end.

Fixpoint insert_env {n X} (w : insertion n) (x : X) :
  (fin n -> X) -> fin (S n) -> X :=
  match w in insertion k return (fin k -> X) -> fin (S k) -> X with
  | insert_here _ => fun env => x .: env
  | insert_under w' =>
      fun env => env var_zero .: insert_env w' x (fun i => env (shift i))
  end.

Lemma insert_env_lookup {n X} (w : insertion n) (x : X) env i :
  insert_env w x env (insert_ren w i) = env i.
Proof.
  induction w as [n|n w IH]; [reflexivity|].
  destruct i as [i|]; [apply IH|reflexivity].
Qed.

Lemma insert_env_slots {n X} (w : insertion n) (x : X) env j :
  insert_env w x env j = x \/ exists i, j = insert_ren w i.
Proof.
  induction w as [n|n w IH].
  - destruct j as [j|].
    + right. now exists j.
    + now left.
  - destruct j as [j|].
    + destruct (IH (fun i => env (shift i)) j) as [H|[i ->]].
      * now left.
      * right. now exists (shift i).
    + right. now exists var_zero.
Qed.

Lemma insert_grade_add {n} (w : insertion n) (γ δ : gradeVec n) :
  insert_env w Qzero (γ Q+ δ) =
  insert_env w Qzero γ Q+ insert_env w Qzero δ.
Proof.
  unfold gradeVecAdd.
  apply functional_extensionality. intro i.
  induction w as [n|n w IH]; destruct i as [i|]; cbn.
  - reflexivity.
  - symmetry. apply Qadd_lident.
  - apply IH.
  - reflexivity.
Qed.

Lemma insert_grade_scale {n} (w : insertion n) q (γ : gradeVec n) :
  insert_env w Qzero (q Q* γ) = q Q* insert_env w Qzero γ.
Proof.
  unfold gradeVecScale.
  apply functional_extensionality. intro i.
  induction w as [n|n w IH]; destruct i as [i|]; cbn.
  - reflexivity.
  - symmetry. apply Qzero_rannihilates.
  - apply IH.
  - reflexivity.
Qed.

Lemma insert_grade_zero {n} (w : insertion n) :
  insert_env w Qzero (0s) = 0s.
Proof.
  apply functional_extensionality. intro i.
  destruct (insert_env_slots w Qzero (0s) i) as [H|[j ->]].
  - exact H.
  - rewrite insert_env_lookup. reflexivity.
Qed.

Lemma insert_grade_le {n} (w : insertion n) (γ δ : gradeVec n) :
  γ Q<= δ -> insert_env w Qzero γ Q<= insert_env w Qzero δ.
Proof.
  intros H i. induction w as [n|n w IH]; destruct i as [i|]; cbn.
  - apply H.
  - apply Qle_refl.
  - apply IH. intro j. apply H.
  - apply H.
Qed.

Lemma insert_typing : forall n (γ : gradeVec n) (Γ : context n),
  (forall V A, VWt γ Γ V A ->
    forall (w : insertion n) X,
      VWt (insert_env w Qzero γ) (insert_env w X Γ)
        (ren_Val (insert_ren w) V) A) /\
  (forall M B ϕ, CWt γ Γ M B ϕ ->
    forall (w : insertion n) X,
      CWt (insert_env w Qzero γ) (insert_env w X Γ)
        (ren_Comp (insert_ren w) M) B ϕ).
Proof.
  apply Wt_mutual; intros; cbn [ren_Val ren_Comp] in *; subst.
  - rewrite <- (insert_env_lookup w X Γ i).
    apply T_Var.
    + now rewrite insert_env_lookup.
    + intros j Hneq.
      destruct (insert_env_slots w Qzero γ j) as [Hz|[i' ->]].
      * exact Hz.
      * rewrite insert_env_lookup. apply e0. congruence.
  - apply T_Thunk. auto.
  - rewrite insert_grade_zero. now apply T_Unit.
  - rewrite insert_grade_add. eapply T_VPair; eauto.
  - apply T_Inl. auto.
  - apply T_Inr. auto.
  - eapply T_VSub; eauto using insert_grade_le.
  - eapply T_Abs; [ | eassumption].
    match goal with
    | IH : forall w X, CWt _ _ _ _ _ |- _ =>
        exact (IH (insert_under w) X)
    end.
  - rewrite insert_grade_add, insert_grade_scale. eapply T_App; eauto.
  - eapply T_Force; eauto.
  - rewrite insert_grade_add, insert_grade_scale.
    eapply T_Split; [apply H| |reflexivity].
    exact (H0 (insert_under (insert_under w)) X).
  - rewrite insert_grade_scale. eapply T_Ret; eauto.
  - rewrite insert_grade_add, insert_grade_scale.
    eapply T_Let; [reflexivity|apply H| |reflexivity|reflexivity].
    exact (H0 (insert_under w) X).
  - apply T_CPair; auto.
  - eapply T_Fst; eauto.
  - eapply T_Snd; eauto.
  - rewrite insert_grade_add. eapply T_Seq; eauto.
  - rewrite insert_grade_add, insert_grade_scale.
    eapply T_Case; [apply H| | |reflexivity|eassumption].
    + exact (H0 (insert_under w) X).
    + exact (H1 (insert_under w) X).
  - rewrite insert_grade_zero. now apply T_Tick.
  - eapply T_CSub; eauto using insert_grade_le.
  - eapply T_SubEff; eauto.
  - eapply T_LetZero; [apply H| |reflexivity|reflexivity].
    exact (H0 (insert_under w) X).
Qed.

Lemma weaken_computation {n} {γ : gradeVec n} {Γ : context n} {M B ϕ} X :
  CWt γ Γ M B ϕ ->
  CWt (Qzero .: γ) (X .: Γ) (ren_Comp shift M) B ϕ.
Proof. exact (fun H => (proj2 (insert_typing _ _ _)) _ _ _ H (insert_here n) X). Qed.

Lemma weaken_under_binder {n} {γ : gradeVec n} {Γ : context n}
    {M B ϕ} q A X :
  CWt (q .: γ) (A .: Γ) M B ϕ ->
  CWt (q .: (Qzero .: γ)) (A .: (X .: Γ)) (ren_Comp up_ren' M) B ϕ.
Proof.
  exact (fun H => (proj2 (insert_typing _ _ _)) _ _ _ H
    (insert_under (insert_here n)) X).
Qed.

Lemma weaken_under_two_binders {n} {γ : gradeVec n} {Γ : context n}
    {M B ϕ} q r A D X :
  CWt (q .: (r .: γ)) (A .: (D .: Γ)) M B ϕ ->
  CWt (q .: (r .: (Qzero .: γ))) (A .: (D .: (X .: Γ)))
    (ren_Comp up2_ren' M) B ϕ.
Proof.
  exact (fun H => (proj2 (insert_typing _ _ _)) _ _ _ H
    (insert_under (insert_under (insert_here n))) X).
Qed.

Lemma type_head {n} A (Γ : context n) :
  VWt (Qone .: (0s)) (A .: Γ) (var_Val var_zero) A.
Proof.
  apply T_Var.
  - reflexivity.
  - intros [i|] Hneq; [reflexivity|contradiction].
Qed.

Lemma type_second {n} A D (Γ : context n) :
  VWt (Qzero .: (Qone .: (0s))) (A .: (D .: Γ))
    (var_Val (shift var_zero)) D.
Proof.
  apply T_Var.
  - reflexivity.
  - intros [[i|]|] Hneq; try reflexivity. contradiction.
Qed.

Lemma type_return_one {n} {γ : gradeVec n} {Γ : context n} {V A} :
  VWt γ Γ V A -> CWt γ Γ (cRet Qone V) (CF Qone A) ϵ.
Proof.
  intro H. eapply T_Ret; [exact H|symmetry; apply grade_scale_one|reflexivity].
Qed.

Lemma type_let_one {n} {γ δ θ : gradeVec n} {Γ : context n}
    {M N r A B ϕ1 ϕ2 ϕ} :
  CWt γ Γ M (CF r A) ϕ1 ->
  CWt (r .: δ) (A .: Γ) N B ϕ2 ->
  θ = γ Q+ δ ->
  ϕ = ϕ1 E+ ϕ2 ->
  CWt θ Γ (cLet Qone M N) B ϕ.
Proof.
  intros HM HN Hg He.
  eapply T_Let with (q' := Qone); autorewrite with translation_grades.
  - reflexivity.
  - exact HM.
  - exact HN.
  - exact Hg.
  - exact He.
Qed.

Lemma type_let_force {n} {γ : gradeVec n} {Γ : context n} {M B ϕ} :
  CWt γ Γ M (CF Qone (VThunk ϕ B)) ϵ ->
  CWt γ Γ (cLet Qone M (cForce (var_Val var_zero))) B ϕ.
Proof.
  intro HM.
  eapply type_let_one; [exact HM|apply T_Force, type_head| | ];
    now autorewrite with translation_grades.
Qed.

Lemma type_sequence {n} {γ δ : gradeVec n} {Γ : context n} {M N B} :
  CWt γ Γ M (CF Qone VUnit) ϵ ->
  CWt δ Γ N B ϵ ->
  CWt (γ Q+ δ) Γ
    (cLet Qone M (cSeq (var_Val var_zero) (ren_Comp shift N))) B ϵ.
Proof.
  intros HM HN. eapply type_let_one; [exact HM| |reflexivity|apply eq_sym, eff_idL].
  eapply T_Seq; [apply type_head|exact (weaken_computation VUnit HN)|].
  now autorewrite with translation_grades.
Qed.

Lemma type_case {n} {γ δ : gradeVec n} {Γ : context n}
    {q M N1 N2 A1 A2 B} :
  CWt γ Γ M (CF Qone (VSum A1 A2)) ϵ ->
  CWt (q .: δ) (A1 .: Γ) N1 B ϵ ->
  CWt (q .: δ) (A2 .: Γ) N2 B ϵ ->
  Qle q Qone ->
  CWt ((q Q* γ) Q+ δ) Γ
    (cLet q M (cCase q (var_Val var_zero)
      (ren_Comp up_ren' N1) (ren_Comp up_ren' N2))) B ϵ.
Proof.
  intros HM H1 H2 Hq.
  eapply T_Let with (q' := q); [symmetry; now apply q_or_1_case|exact HM| | | ].
  - rewrite Qmult_lident.
    eapply T_Case.
    + apply type_head.
    + exact (weaken_under_binder q A1 (VSum A1 A2) H1).
    + exact (weaken_under_binder q A2 (VSum A1 A2) H2).
    + now autorewrite with translation_grades.
    + exact Hq.
  - reflexivity.
  - apply eq_sym, eff_idL.
Qed.

End TranslationTyping.

Module CBN.

Import full.CBN.translation.
Import TranslationTyping.
Local Open Scope subst_scope.

Local Lemma translate_context_cons {n} T (Γ : contextL n) :
  translateContext (T .: Γ) = VThunk ϵ (translateType T) .: translateContext Γ.
Proof. apply functional_extensionality. intros [i|]; reflexivity. Qed.

Theorem cbn_translation_correct :
    forall n (γ : gradeVec n) (Γ : contextL n) e T,
    Wt γ Γ e T ->
    CWt γ (translateContext Γ)
        (translateTerm e) (translateType T) ϵ.
Proof.
  intros n γ Γ e T H.
  induction H; cbn [translateTerm translateType] in *;
    rewrite ?translate_context_cons in *; subst.
  - apply T_Force. change (VWt γ (translateContext Γ) (var_Val i)
      (translateContext Γ i)). now apply T_Var.
  - eapply T_Abs; eassumption.
  - eapply T_App; [exact IHWt1|apply T_Thunk; exact IHWt2|reflexivity].
  - apply type_return_one, T_Unit. reflexivity.
  - now apply type_sequence.
  - apply type_return_one, T_Inl, T_Thunk. exact IHWt.
  - apply type_return_one, T_Inr, T_Thunk. exact IHWt.
  - now apply T_CPair.
  - eapply T_Fst. exact IHWt.
  - eapply T_Snd. exact IHWt.
  - eapply type_case; eassumption.
  - eapply T_Ret; [apply T_Thunk; exact IHWt|reflexivity|reflexivity].
  - eapply T_Let; [reflexivity|exact IHWt1|exact IHWt2|reflexivity|].
    apply eq_sym, eff_idL.
  - eapply T_CSub; eassumption.
  - apply type_return_one, T_Thunk, type_return_one, T_Thunk. exact IHWt.
  - apply type_return_one, T_Thunk.
    eapply T_Let with (q' := q_or_1 q).
    + symmetry. apply q_or_1_idem.
    + apply type_let_force. exact IHWt1.
    + rewrite Qmult_lident. apply type_let_force. exact IHWt2.
    + reflexivity.
    + reflexivity.
  - apply type_return_one, T_Thunk.
    eapply T_SubEff; [apply type_let_force; exact IHWt|eassumption].
  - apply type_return_one, T_Thunk.
    eapply type_let_one.
    + apply T_Tick; reflexivity.
    + apply type_return_one, T_Thunk, type_return_one, type_head.
    + now autorewrite with translation_grades.
    + now autorewrite with translation_grades.
Qed.

End CBN.

Module CBV.

Import full.CBV.translation.
Import TranslationTyping.
Local Open Scope subst_scope.

Local Lemma translate_context_cons {n} T (Γ : contextL n) :
  translateContext (T .: Γ) = translateType T .: translateContext Γ.
Proof. apply functional_extensionality. intros [i|]; reflexivity. Qed.

Theorem cbv_translation_correct :
    forall n (γ : gradeVec n) (Γ : contextL n) e T,
    Wt γ Γ e T ->
    CWt γ (translateContext Γ)
        (translateTerm e) (CF Qone (translateType T)) ϵ.
Proof.
  intros n γ Γ e T H.
  induction H; cbn [translateTerm translateType] in *;
    rewrite ?translate_context_cons in *; subst.
  - apply type_return_one. change (VWt γ (translateContext Γ) (var_Val i)
      (translateContext Γ i)). now apply T_Var.
  - apply type_return_one, T_Thunk. eapply T_Abs; eassumption.
  - eapply type_let_one; [exact IHWt1| |reflexivity|apply eq_sym, eff_idL].
    eapply T_Let with (q' := q_or_1 q).
    + reflexivity.
    + eapply weaken_computation. exact IHWt2.
    + rewrite Qmult_lident. eapply T_App.
      * apply T_Force, type_second.
      * apply type_head.
      * now autorewrite with translation_grades.
    + now autorewrite with translation_grades.
    + apply eq_sym, eff_idL.
  - apply type_return_one, T_Unit. reflexivity.
  - now apply type_sequence.
  - eapply type_let_one; [exact IHWt1| |reflexivity|apply eq_sym, eff_idL].
    eapply type_let_one.
    + eapply weaken_computation. exact IHWt2.
    + apply type_return_one. eapply T_VPair.
      * apply type_second.
      * apply type_head.
      * now autorewrite with translation_grades.
    + now autorewrite with translation_grades.
    + apply eq_sym, eff_idL.
  - eapply T_Let with (q' := q_or_1 q).
    + symmetry. apply q_or_1_idem.
    + exact IHWt1.
    + rewrite Qmult_lident. eapply T_Split.
      * apply type_head.
      * eapply weaken_under_two_binders. exact IHWt2.
      * now autorewrite with translation_grades.
    + reflexivity.
    + apply eq_sym, eff_idL.
  - eapply type_let_one.
    + exact IHWt.
    + apply type_return_one, T_Inl, type_head.
    + now autorewrite with translation_grades.
    + apply eq_sym, eff_idL.
  - eapply type_let_one.
    + exact IHWt.
    + apply type_return_one, T_Inr, type_head.
    + now autorewrite with translation_grades.
    + apply eq_sym, eff_idL.
  - eapply type_case; eassumption.
  - eapply T_Let with (q' := q_or_1 q).
    + reflexivity.
    + exact IHWt.
    + rewrite Qmult_lident. apply type_return_one, T_Thunk.
      eapply T_Ret; [apply type_head| |reflexivity].
      now autorewrite with translation_grades.
    + now autorewrite with translation_grades.
    + apply eq_sym, eff_idL.
  - eapply T_Let with (q' := q_or_1 q2).
    + reflexivity.
    + exact IHWt1.
    + rewrite Qmult_lident. eapply T_Let with (q' := q_or_1 q2).
      * reflexivity.
      * apply T_Force, type_head.
      * eapply weaken_under_binder. exact IHWt2.
      * now autorewrite with translation_grades.
      * apply eq_sym, eff_idL.
    + reflexivity.
    + apply eq_sym, eff_idL.
  - eapply T_CSub; eassumption.
  - apply type_return_one, T_Thunk. exact IHWt.
  - apply type_return_one, T_Thunk.
    eapply T_Let with (q' := q_or_1 q).
    + reflexivity.
    + apply type_let_force. exact IHWt1.
    + rewrite Qmult_lident. apply type_let_force. exact IHWt2.
    + reflexivity.
    + reflexivity.
  - apply type_return_one, T_Thunk.
    eapply T_SubEff; [apply type_let_force; exact IHWt|eassumption].
  - apply type_return_one, T_Thunk.
    eapply type_let_one.
    + apply T_Tick; reflexivity.
    + apply type_return_one, type_head.
    + now autorewrite with translation_grades.
    + now autorewrite with translation_grades.
Qed.

End CBV.
