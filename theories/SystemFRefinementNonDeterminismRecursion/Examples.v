From Stdlib Require Import Lists.List Lia ZArith.BinInt Arith.PeanoNat.
From AutoProof.SystemFRefinementNonDeterminismRecursion Require Import
  Syntax Infrastructure RefinementTyping Evaluation RefinementSoundness Safety.

Module SystemFRefinementNonDeterminismRecursionExamples.
Import ListNotations.
Import SystemFRefinementNonDeterminismRecursion SystemFRefinementNonDeterminismRecursionInfrastructure
       SystemFRefinementNonDeterminismRecursionTyping SystemFRefinementNonDeterminismRecursionEvaluation
       SystemFRefinementNonDeterminismRecursionSoundness SystemFRefinementNonDeterminismRecursionSafety.

Definition NatInput : rty := measured_input Ty_Int Pred_True (tm_bvar 0).
Definition AnyInt : rty := R_Refine Ty_Int Pred_True.
Definition SmallerNat (x : atom) : rty :=
  smaller_input Ty_Int Pred_True (tm_bvar 0) (tm_fvar x).

(* fix f (n : Int) : Int / n = ifzero n then 0 else f 0 *)
Definition jump_to_zero : tm :=
  tm_fix Ty_Int Ty_Int (tm_bvar 0)
    (tm_ifzero (tm_bvar 0) (tm_int 0%Z)
      (tm_app (tm_bvar 1) (tm_int 0%Z))).

(* fix f (n : Int) : Int / n = ifzero n then 0 else f (n / 2) *)
Definition halve_to_zero : tm :=
  tm_fix Ty_Int Ty_Int (tm_bvar 0)
    (tm_ifzero (tm_bvar 0) (tm_int 0%Z)
      (tm_app (tm_bvar 1) (tm_div (tm_bvar 0) (tm_int 2%Z)))).

Lemma jump_lc : locally_closed_tm jump_to_zero.
Proof.
  unfold jump_to_zero, locally_closed_tm.
  repeat constructor; lia.
Qed.

Lemma halve_lc : locally_closed_tm halve_to_zero.
Proof.
  unfold halve_to_zero, locally_closed_tm.
  repeat constructor; lia.
Qed.

Example unfold_halve_8 :
  tm_app halve_to_zero (tm_int 8%Z) -->
  tm_ifzero (tm_int 8%Z) (tm_int 0%Z)
    (tm_app halve_to_zero (tm_div (tm_int 8%Z) (tm_int 2%Z))).
Proof. change (tm_app halve_to_zero (tm_int 8%Z) -->
  open_fix_body
    (tm_ifzero (tm_bvar 0) (tm_int 0%Z)
      (tm_app (tm_bvar 1) (tm_div (tm_bvar 0) (tm_int 2%Z))))
    halve_to_zero (tm_int 8%Z)).
  apply ST_AppFix; [exact halve_lc | constructor].
Qed.

Example halve_argument_8_to_4 :
  tm_app halve_to_zero (tm_div (tm_int 8%Z) (tm_int 2%Z)) -->
  tm_app halve_to_zero (tm_int 4%Z).
Proof.
  apply ST_App2; [constructor; exact halve_lc |].
  change (tm_div (tm_int 8%Z) (tm_int 2%Z) --> tm_int (Z.div 8 2)).
  apply ST_DivInt. discriminate.
Qed.

Lemma value_no_step : forall v, value v -> forall t, ~ v --> t.
Proof. intros v Hv t Hs. inversion Hv; subst; inversion Hs. Qed.

Lemma value_predicate_multi : forall v t,
  value v -> predicate_multistep v t -> v = t.
Proof.
  intros v t Hv Hm. inversion Hm; subst.
  - reflexivity.
  - exfalso. eapply value_no_step; eauto.
Qed.

Lemma literal_lt : forall n m : Z,
  (n < m)%Z -> qualifier_holds (Pred_Lt (tm_int n) (tm_int m)).
Proof.
  intros n m Hlt. exists n, m.
  split; [constructor |]. split; [constructor |]. split; [assumption |].
  intros a b Ha Hb.
  pose proof (value_predicate_multi _ _ (v_int n) Ha) as Ea.
  pose proof (value_predicate_multi _ _ (v_int m) Hb) as Eb.
  inversion Ea; inversion Eb; subst; assumption.
Qed.

Example eight_to_four_is_smaller :
  qualifier_holds (Pred_Lt (tm_int 4%Z) (tm_int 8%Z)).
Proof. apply literal_lt. lia. Qed.

Example eight_to_eight_is_not_smaller :
  ~ qualifier_holds (Pred_Lt (tm_int 8%Z) (tm_int 8%Z)).
Proof.
  intros [a [b [Ha [Hb [Hlt Hall]]]]].
  pose proof (value_predicate_multi _ _ (v_int 8) Ha) as Ea.
  pose proof (value_predicate_multi _ _ (v_int 8) Hb) as Eb.
  inversion Ea; inversion Eb; subst; lia.
Qed.

Lemma wf_anyint : forall Delta RGamma, wf_rty Delta RGamma AnyInt.
Proof.
  intros. apply RWF_Refine with ([] : list atom); [constructor |].
  intros. constructor.
Qed.

Lemma wf_natinput : forall Delta RGamma, wf_rty Delta RGamma NatInput.
Proof.
  intros. apply RWF_Refine with ([] : list atom); [constructor |].
  intros x Hx. unfold qualifier_wf, open_qualifier_tm,
    open_qualifier_tm_rec, measured_input. simpl.
  apply PWF_And; [constructor |]. apply PWF_Le; [constructor |].
  apply T_Var; [apply lookup_context_update_eq | constructor].
Qed.

Lemma wf_smaller : forall Delta RGamma x,
  lookup_context x (erase_context RGamma) = Some Ty_Int ->
  wf_rty Delta RGamma (SmallerNat x).
Proof.
  intros Delta RGamma x Hx.
  apply RWF_Refine with [x]; [constructor |].
  intros y Hy. assert (Exy : x <> y) by (simpl in Hy; intuition).
  unfold qualifier_wf, open_qualifier_tm, open_qualifier_tm_rec. simpl.
  apply PWF_And; [constructor |].
  apply PWF_And.
  - apply PWF_Le; [constructor |].
    apply T_Var; [apply lookup_context_update_eq | constructor].
  - apply PWF_Lt.
    + apply T_Var; [apply lookup_context_update_eq | constructor].
    + apply T_Var; [| constructor].
      rewrite lookup_context_update_neq; [exact Hx | congruence].
Qed.

Lemma wf_recursive_type : forall Delta RGamma x,
  lookup_context x (erase_context RGamma) = Some Ty_Int ->
  wf_rty Delta RGamma (R_Func (SmallerNat x) AnyInt).
Proof.
  intros. apply RWF_Func with ([] : list atom).
  - apply wf_smaller; assumption.
  - intros. apply wf_anyint.
Qed.

Lemma int_any : forall Delta RGamma n,
  has_rtype Delta RGamma (tm_int n) AnyInt.
Proof.
  intros. eapply RT_Sub.
  - apply RT_Int.
  - apply wf_anyint.
  - apply S_Refine with ([] : list atom). intros. apply Entails_True.
Qed.

Definition PositiveAssumption : qualifier :=
  Pred_And (Pred_And Pred_True (Pred_Ge (tm_bvar 0) (tm_int 0%Z)))
    (Pred_Ne (tm_bvar 0) (tm_int 0%Z)).

Lemma eq_zero_value : forall w,
  value w -> qualifier_holds (Pred_Eq w (tm_int 0%Z)) -> w = tm_int 0%Z.
Proof.
  intros w Hw [v [Hwv [H0v Hv]]].
  pose proof (value_predicate_multi _ _ Hw Hwv).
  pose proof (value_predicate_multi _ _ (v_int 0) H0v).
  congruence.
Qed.

Lemma nonnegative_value : forall w,
  value w -> qualifier_holds (Pred_Ge w (tm_int 0%Z)) ->
  exists n : Z, w = tm_int n /\ (0 <= n)%Z.
Proof.
  intros w Hw [a [b [Ha [Hb Hab]]]].
  pose proof (value_predicate_multi _ _ (v_int 0) Ha) as Ea.
  pose proof (value_predicate_multi _ _ Hw Hb) as Eb.
  injection Ea as Ea. subst a. exists b. split; assumption.
Qed.

Lemma zero_has_smaller_type : forall Delta RGamma x,
  lookup_rcontext x RGamma = Some (R_Refine Ty_Int PositiveAssumption) ->
  has_rtype Delta RGamma (tm_int 0%Z) (SmallerNat x).
Proof.
  intros Delta RGamma x Hx. eapply RT_Sub.
  - apply RT_Int.
  - apply wf_smaller.
    exact (lookup_erase_context _ _ _ Hx).
  - apply S_Refine with [x]. intros y Hy.
    assert (Exy : x <> y) by (simpl in Hy; intuition).
    apply Entails_Valid. intros theta gamma Hvalues Hcontext Hp.
    assert (Hlookup : lookup_rcontext x
      (update_rcontext RGamma y (R_Refine Ty_Int Pred_True)) =
      Some (R_Refine Ty_Int PositiveAssumption)).
    { simpl. rewrite (proj2 (Nat.eqb_neq x y) Exy). exact Hx. }
    pose proof (Hcontext x Ty_Int PositiveAssumption Hlookup) as Hcurrent.
    cbn in Hcurrent, Hp |- *.
    destruct Hcurrent as [[_ Hnonneg] Hnonzero].
    pose proof (eq_zero_value (gamma y) (Hvalues y) Hp) as Ey.
    destruct (nonnegative_value (gamma x) (Hvalues x) Hnonneg) as [n [Ex Hn]].
    assert (Hnz : n <> 0%Z).
    { intro E. subst n. apply Hnonzero. rewrite Ex.
      exists (tm_int 0%Z). repeat split; constructor. }
    rewrite Ey, Ex. split; [exact I |]. split.
    + exists 0%Z, 0%Z. repeat split; constructor || lia.
    + apply literal_lt. lia.
Qed.

Lemma integer_division_result : forall n d v,
  predicate_multistep (tm_div (tm_int n) (tm_int d)) v ->
  value v -> v = tm_int (Z.div n d).
Proof.
  intros n d v Hm Hv. inversion Hm; subst.
  - inversion Hv.
  - match goal with Hs : step (tm_div _ _) _ |- _ => inversion Hs; subst end.
    + match goal with Hs : step (tm_int _) _ |- _ => inversion Hs end.
    + match goal with Hs : step (tm_int _) _ |- _ => inversion Hs end.
    + symmetry. eapply value_predicate_multi; [constructor | eassumption].
Qed.

Lemma half_has_smaller_type : forall Delta RGamma x,
  lookup_rcontext x RGamma = Some (R_Refine Ty_Int PositiveAssumption) ->
  has_rtype Delta RGamma (tm_div (tm_fvar x) (tm_int 2%Z)) (SmallerNat x).
Proof.
  intros Delta RGamma x Hx. eapply RT_Sub.
  - apply RT_Div.
    + eapply RT_Sub.
      * apply RT_Var; [exact Hx |].
        apply RWF_Refine with ([] : list atom); [constructor |].
        intros y Hy. unfold qualifier_wf, open_qualifier_tm,
          open_qualifier_tm_rec, PositiveAssumption. simpl.
        apply PWF_And.
        -- apply PWF_And; [constructor |].
           apply PWF_Le; [constructor |].
           apply T_Var; [apply lookup_context_update_eq | constructor].
        -- apply PWF_Not. eapply PWF_Eq.
           ++ apply T_Var; [apply lookup_context_update_eq | constructor].
           ++ constructor.
      * apply wf_anyint.
      * apply S_Refine with ([] : list atom). intros. apply Entails_True.
    + apply RT_RefineValue.
      * constructor.
      * constructor.
      * apply RWF_Refine with ([] : list atom); [constructor |].
        intros. apply PWF_Not. eapply PWF_Eq.
        -- apply T_Var; [apply lookup_context_update_eq | constructor].
        -- constructor.
      * repeat split; constructor.
      * intro Hbad.
        pose proof (eq_zero_value _ (v_int 2) Hbad). discriminate.
  - apply wf_smaller. exact (lookup_erase_context _ _ _ Hx).
  - apply S_Refine with [x]. intros y Hy.
    assert (Exy : x <> y) by (simpl in Hy; intuition).
    apply Entails_Valid. intros theta gamma Hvalues Hcontext Hp.
    assert (Hlookup : lookup_rcontext x
      (update_rcontext RGamma y (R_Refine Ty_Int Pred_True)) =
      Some (R_Refine Ty_Int PositiveAssumption)).
    { simpl. rewrite (proj2 (Nat.eqb_neq x y) Exy). exact Hx. }
    pose proof (Hcontext x Ty_Int PositiveAssumption Hlookup) as Hcurrent.
    cbn in Hcurrent, Hp |- *.
    destruct Hcurrent as [[_ Hnonneg] Hnonzero].
    destruct (nonnegative_value (gamma x) (Hvalues x) Hnonneg) as [n [Ex Hn]].
    assert (Hnz : n <> 0%Z).
    { intro E. subst n. apply Hnonzero. rewrite Ex.
      exists (tm_int 0%Z). repeat split; constructor. }
    destruct Hp as [w [Hyw [Hdivw Hw]]].
    pose proof (value_predicate_multi _ _ (Hvalues y) Hyw) as Ey.
    rewrite Ex in Hdivw.
    pose proof (integer_division_result _ _ _ Hdivw Hw) as Ew.
    rewrite Ey, Ew, Ex. split; [exact I |]. split.
    + exists 0%Z, (Z.div n 2). repeat split; try constructor.
      apply Z.div_pos; lia.
    + apply literal_lt. apply Z.div_lt_upper_bound; lia.
Qed.

Theorem jump_to_zero_typed :
  has_rtype [] empty_rcontext jump_to_zero (R_Func NatInput AnyInt).
Proof.
  unfold jump_to_zero, NatInput.
  apply (RT_Fix [] [] empty_rcontext Ty_Int Pred_True (tm_bvar 0)
    (tm_ifzero (tm_bvar 0) (tm_int 0%Z)
      (tm_app (tm_bvar 1) (tm_int 0%Z))) AnyInt).
  - apply RWF_Func with ([] : list atom).
    + apply wf_natinput.
    + intros. apply wf_anyint.
  - intros x Hx. apply T_Var; [apply lookup_context_update_eq | constructor].
  - intros f x Hf Hx.
    assert (Exf : x <> f) by (simpl in Hx; intuition).
    assert (Efx : f <> x) by congruence.
    cbn [open_fix_body open_tm open_tm_rec].
    eapply RT_IfZero.
    + cbn [lookup_rcontext update_rcontext].
      rewrite (proj2 (Nat.eqb_neq x f) Exf), Nat.eqb_refl. reflexivity.
    + apply int_any.
    + eapply RT_Sub.
      * eapply RT_App with (R1 := SmallerNat x) (R2 := AnyInt).
        -- apply RT_Var.
           ++ cbn [lookup_rcontext update_rcontext].
              rewrite (proj2 (Nat.eqb_neq f x) Efx), Nat.eqb_refl.
              reflexivity.
           ++ apply wf_recursive_type.
              simpl. rewrite Nat.eqb_refl. reflexivity.
        -- apply zero_has_smaller_type.
           simpl. rewrite Nat.eqb_refl. reflexivity.
      * apply wf_anyint.
      * apply S_Bind with ([] : list atom).
        -- apply wf_smaller. simpl. rewrite Nat.eqb_refl. reflexivity.
        -- unfold AnyInt, locally_closed_rty, lc_qualifier_at. repeat constructor.
        -- intros. apply S_Refl.
Qed.

Theorem halve_to_zero_typed :
  has_rtype [] empty_rcontext halve_to_zero (R_Func NatInput AnyInt).
Proof.
  unfold halve_to_zero, NatInput.
  apply (RT_Fix [] [] empty_rcontext Ty_Int Pred_True (tm_bvar 0)
    (tm_ifzero (tm_bvar 0) (tm_int 0%Z)
      (tm_app (tm_bvar 1) (tm_div (tm_bvar 0) (tm_int 2%Z)))) AnyInt).
  - apply RWF_Func with ([] : list atom).
    + apply wf_natinput.
    + intros. apply wf_anyint.
  - intros x Hx. apply T_Var; [apply lookup_context_update_eq | constructor].
  - intros f x Hf Hx.
    assert (Exf : x <> f) by (simpl in Hx; intuition).
    assert (Efx : f <> x) by congruence.
    cbn [open_fix_body open_tm open_tm_rec].
    eapply RT_IfZero.
    + cbn [lookup_rcontext update_rcontext].
      rewrite (proj2 (Nat.eqb_neq x f) Exf), Nat.eqb_refl. reflexivity.
    + apply int_any.
    + eapply RT_Sub.
      * eapply RT_App with (R1 := SmallerNat x) (R2 := AnyInt).
        -- apply RT_Var.
           ++ cbn [lookup_rcontext update_rcontext].
              rewrite (proj2 (Nat.eqb_neq f x) Efx), Nat.eqb_refl.
              reflexivity.
           ++ apply wf_recursive_type.
              simpl. rewrite Nat.eqb_refl. reflexivity.
        -- apply half_has_smaller_type.
           simpl. rewrite Nat.eqb_refl. reflexivity.
      * apply wf_anyint.
      * apply S_Bind with ([] : list atom).
        -- apply wf_smaller. simpl. rewrite Nat.eqb_refl. reflexivity.
        -- unfold AnyInt, locally_closed_rty, lc_qualifier_at. repeat constructor.
        -- intros. apply S_Refl.
Qed.

(* 普通 typing 不检查递减：这个程序有普通类型，却会一步回到自身。
   因此旧版的 core normalization 不能直接用于新版语言。 *)

End SystemFRefinementNonDeterminismRecursionExamples.
