From AutoProof.SecurityNoninterference Require Import LogicalRelation Noninterference.
Import ListNotations.

Definition Bool (kappa : security) : ty :=
  Ty_Sum (Ty_Unit public) (Ty_Unit public) kappa.

Definition tm_true (kappa : security) : tm := tm_inl (tm_unit public) kappa.
Definition tm_false (kappa : security) : tm := tm_inr (tm_unit public) kappa.

Definition branch (condition : tm) (r : label) : tm :=
  tm_case condition (tm_true public) (tm_false public) r.

Definition restricted_read_public_flow : security :=
  {| reader := High; indirect_reader := Low |}.

Example restricted_read_public_flow_is_valid :
  wf_security restricted_read_public_flow.
Proof. exact I. Qed.

Example secret_cannot_flow_to_public : ~ flows_to High Low.
Proof. exact (fun H => H). Qed.

Example protecting_public_makes_secret : protect_security public High = secret.
Proof. reflexivity. Qed.

Example public_true_typed : forall Gamma,
  has_type Gamma (tm_true public) (Bool public).
Proof.
  intros Gamma. apply T_Inl; [apply T_Unit | | ]; exact I.
Qed.

Example public_false_typed : forall Gamma,
  has_type Gamma (tm_false public) (Bool public).
Proof.
  intros Gamma. apply T_Inr; [ | apply T_Unit | ]; exact I.
Qed.

Example secret_true_typed : has_type empty (tm_true secret) (Bool secret).
Proof. apply T_Inl; [apply T_Unit | | ]; exact I. Qed.

Example secret_false_typed : has_type empty (tm_false secret) (Bool secret).
Proof. apply T_Inr; [ | apply T_Unit | ]; exact I. Qed.

Example secret_branch_typed :
  has_type empty (branch (tm_true secret) High) (Bool secret).
Proof.
  change (has_type empty (branch (tm_true secret) High)
    (ty_protect High (Bool public))).
  eapply T_Case with (L := []) (kappa := secret).
  - exact secret_true_typed.
  - exact I.
  - intros x Hfresh. apply public_true_typed.
  - intros x Hfresh. apply public_false_typed.
Qed.

Example secret_branch_evaluates :
  evaluates (branch (tm_true secret) High) (tm_true secret).
Proof.
  split.
  - eapply multi_step.
    + apply ST_CaseLeft; [apply v_unit | exact I].
    + eapply multi_step.
      * apply ST_ProtectValue. apply v_inl. apply v_unit.
      * apply multi_refl.
  - apply v_inl. apply v_unit.
Qed.

Example unauthorized_branch_stuck :
  forall t, ~ step (branch (tm_true secret) Low) t.
Proof.
  intros t Hstep. inversion Hstep; subst; try contradiction.
  match goal with H : step (tm_true secret) _ |- _ => inversion H; subst end.
  match goal with H : step (tm_unit public) _ |- _ => inversion H end.
Qed.

Example permitted_public_flow :
  evaluates (branch (tm_true restricted_read_public_flow) High) (tm_true public).
Proof.
  split.
  - eapply multi_step.
    + apply ST_CaseLeft; [apply v_unit | exact I].
    + eapply multi_step.
      * apply ST_ProtectValue. apply v_inl. apply v_unit.
      * apply multi_refl.
  - apply v_inl. apply v_unit.
Qed.

Example opening_under_a_binder :
  open (tm_abs (Ty_Unit public) (tm_bvar 1) public) (tm_unit secret) =
    tm_abs (Ty_Unit public) (tm_unit secret) public.
Proof. reflexivity. Qed.

Example public_bool_is_transparent : transparent (Bool public).
Proof. repeat split; exact I. Qed.

Example public_pair_with_secret_fields_is_not_transparent :
  ~ transparent (Ty_Prod (Bool secret) (Bool secret) public).
Proof. intros [_ [[[_ H] _] _]]. exact H. Qed.

Example secret_boolean_values_are_related :
  value_relation Low (Bool secret) (tm_true secret) (tm_false secret).
Proof.
  split; [apply v_inl; apply v_unit | ].
  split; [apply v_inr; apply v_unit | ].
  split; [apply public_true_typed | ].
  split; [apply public_false_typed | ].
  intros H. contradiction.
Qed.

Example public_true_and_false_are_not_related :
  ~ value_relation Low (Bool public) (tm_true public) (tm_false public).
Proof.
  intros [_ [_ [_ [_ Hvisible]]]].
  destruct (Hvisible I) as [Hleft | Hright].
  - destruct Hleft as [u1 [u2 [kappa1 [kappa2 [_ [Hbad _]]]]]].
    discriminate Hbad.
  - destruct Hright as [u1 [u2 [kappa1 [kappa2 [Hbad _]]]]].
    discriminate Hbad.
Qed.

Definition ignore_secret : program_context :=
  C_AppRight (tm_abs (Bool secret) (tm_true public) public) C_Hole Low.

Example ignore_secret_context_typed :
  context_has_type ignore_secret (Bool secret) (Bool public).
Proof.
  exists []. intros x Hfresh.
  change (has_type (update empty x (Bool secret))
    (plug ignore_secret (tm_fvar x)) (ty_protect Low (Bool public))).
  eapply T_App with (T1 := Bool secret) (kappa := public).
  - apply T_Abs with (L := []).
    + repeat split; exact I.
    + exact I.
    + intros y Hy. apply public_true_typed.
  - apply T_Var.
    + simpl. rewrite Nat.eqb_refl. reflexivity.
    + repeat split; exact I.
  - exact I.
Qed.

Example ignore_secret_noninterference :
  same_result (plug ignore_secret (tm_true secret))
    (plug ignore_secret (tm_false secret)).
Proof.
  apply noninterference with (T_secret := Bool secret) (T_result := Bool public).
  - exact secret_true_typed.
  - exact secret_false_typed.
  - exact ignore_secret_context_typed.
  - simpl. auto.
  - exact public_bool_is_transparent.
  - exact secret_cannot_flow_to_public.
Qed.

Example ignore_secret_returns_public_true : forall v,
  value v -> evaluates (plug ignore_secret v) (tm_true public).
Proof.
  intros v Hv. split.
  - eapply multi_step.
    + apply ST_AppAbs.
      * apply v_abs. exact I.
      * exact Hv.
      * exact I.
    + eapply multi_step.
      * apply ST_ProtectValue. apply v_inl. apply v_unit.
      * apply multi_refl.
  - apply v_inl. apply v_unit.
Qed.

Example public_results_are_distinguishable :
  ~ same_result (tm_true public) (tm_false public).
Proof.
  intro H.
  assert (evaluates (tm_true public) (tm_true public)) as Htrue
    by (apply evaluates_value; apply v_inl; apply v_unit).
  assert (evaluates (tm_false public) (tm_false public)) as Hfalse
    by (apply evaluates_value; apply v_inr; apply v_unit).
  specialize (H _ _ Htrue Hfalse). discriminate H.
Qed.
