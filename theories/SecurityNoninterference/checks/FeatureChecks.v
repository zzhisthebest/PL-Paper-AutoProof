From AutoProof.SecurityNoninterference Require Import
  Syntax Semantics Typing Evaluation Metatheory Substitution
  LogicalRelation Noninterference Examples.
Import ListNotations.

Module IfCheck.

Fixpoint shift (k : nat) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar (if i <? k then i else S i)
  | tm_fvar x => tm_fvar x
  | tm_unit s => tm_unit s
  | tm_abs T body s => tm_abs T (shift (S k) body) s
  | tm_app f a r => tm_app (shift k f) (shift k a) r
  | tm_pair a b s => tm_pair (shift k a) (shift k b) s
  | tm_fst a r => tm_fst (shift k a) r
  | tm_snd a r => tm_snd (shift k a) r
  | tm_inl a s => tm_inl (shift k a) s
  | tm_inr a s => tm_inr (shift k a) s
  | tm_case a b c r => tm_case (shift k a) (shift (S k) b) (shift (S k) c) r
  | tm_protect l a => tm_protect l (shift k a)
  end.

Lemma shift_lc : forall t k, lc_at k t -> shift k t = t.
Proof.
  induction t; intros k H; simpl in *; try reflexivity;
    try (destruct H as [H1 H2]); try (destruct H2 as [H2 H3]);
    try (rewrite IHt by assumption; reflexivity);
    try (rewrite IHt1, IHt2 by assumption; reflexivity);
    try (rewrite IHt1, IHt2, IHt3 by assumption; reflexivity).
  rewrite (proj2 (Nat.ltb_lt n k) H). reflexivity.
Qed.

Definition if_term (c yes no : tm) (r : label) : tm :=
  tm_case c (shift 0 yes) (shift 0 no) r.

Lemma if_typing : forall Gamma c yes no k T r,
  has_type Gamma c (Bool k) ->
  has_type Gamma yes T -> has_type Gamma no T ->
  flows_to k.(reader) r ->
  has_type Gamma (if_term c yes no r) (ty_protect k.(indirect_reader) T).
Proof.
  intros Gamma c yes no k T r Hc Hy Hn Haccess.
  unfold if_term. rewrite !shift_lc by
    (eapply typing_regular; eassumption).
  eapply T_Case with (L := map fst Gamma).
  - exact Hc.
  - exact Haccess.
  - intros x Hfresh. rewrite open_locally_closed by (exact (proj1 (typing_regular _ _ _ Hy))).
    eapply typing_weaken; [exact Hy |]. apply context_included_fresh_update. exact Hfresh.
  - intros x Hfresh. rewrite open_locally_closed by (exact (proj1 (typing_regular _ _ _ Hn))).
    eapply typing_weaken; [exact Hn |]. apply context_included_fresh_update. exact Hfresh.
Qed.

Lemma if_true_evaluates : forall yes no k r v,
  locally_closed yes -> locally_closed no ->
  flows_to k.(reader) r -> evaluates yes v ->
  evaluates (if_term (tm_true k) yes no r) (protect_value v k.(indirect_reader)).
Proof.
  intros yes no k r v Hy Hn Ha Hv.
  unfold if_term. rewrite !shift_lc by assumption.
  apply big_step_iff_evaluates. eapply B_CaseLeft.
  - apply B_Inl. apply B_Unit.
  - exact Ha.
  - rewrite open_locally_closed by exact Hy. apply big_step_iff_evaluates. exact Hv.
Qed.

Lemma if_false_evaluates : forall yes no k r v,
  locally_closed yes -> locally_closed no ->
  flows_to k.(reader) r -> evaluates no v ->
  evaluates (if_term (tm_false k) yes no r) (protect_value v k.(indirect_reader)).
Proof.
  intros yes no k r v Hy Hn Ha Hv.
  unfold if_term. rewrite !shift_lc by assumption.
  apply big_step_iff_evaluates. eapply B_CaseRight.
  - apply B_Inr. apply B_Unit.
  - exact Ha.
  - rewrite open_locally_closed by exact Hn. apply big_step_iff_evaluates. exact Hv.
Qed.

End IfCheck.

Module ChoiceCheck.

Inductive nd_tm :=
  | lift : tm -> nd_tm
  | choice : nd_tm -> nd_tm -> nd_tm.

Inductive nd_step : nd_tm -> nd_tm -> Prop :=
  | ND_Base : forall t t', step t t' -> nd_step (lift t) (lift t')
  | ND_Left : forall t u, nd_step (choice t u) t
  | ND_Right : forall t u, nd_step (choice t u) u.

Inductive nd_multi : nd_tm -> nd_tm -> Prop :=
  | ND_Refl : forall t, nd_multi t t
  | ND_Trans : forall t u v, nd_step t u -> nd_multi u v -> nd_multi t v.

Definition nd_evaluates (t : nd_tm) (v : tm) := nd_multi t (lift v) /\ value v.

Inductive nd_has_type : context -> nd_tm -> ty -> Prop :=
  | ND_TBase : forall Gamma t T, has_type Gamma t T -> nd_has_type Gamma (lift t) T
  | ND_TChoice : forall Gamma t u T,
      nd_has_type Gamma t T -> nd_has_type Gamma u T -> nd_has_type Gamma (choice t u) T.

Definition C (s : tm) : nd_tm :=
  choice (lift (plug ignore_secret s)) (lift (tm_false public)).

Lemma C_typed : forall x,
  nd_has_type (update empty x (Bool secret)) (C (tm_fvar x)) (Bool public).
Proof.
  intro x. apply ND_TChoice; apply ND_TBase.
  - unfold ignore_secret, plug. simpl.
    change (has_type (update empty x (Bool secret))
      (tm_app (tm_abs (Bool secret) (tm_true public) public) (tm_fvar x) Low)
      (ty_protect Low (Bool public))).
    eapply T_App with (T1 := Bool secret) (kappa := public).
    + apply T_Abs with (L := []); try (repeat split; exact I).
      intros y Hy. apply public_true_typed.
    + apply T_Var; [simpl; rewrite Nat.eqb_refl; reflexivity | repeat split; exact I].
    + exact I.
  - apply public_false_typed.
Qed.

Lemma lift_multi : forall t v, multi t v -> nd_multi (lift t) (lift v).
Proof.
  intros t v H. induction H.
  - apply ND_Refl.
  - eapply ND_Trans; [apply ND_Base; exact H | exact IHmulti].
Qed.

Definition nd_same_result (t u : nd_tm) :=
  forall v w, nd_evaluates t v -> nd_evaluates u w -> erase_security v = erase_security w.

Theorem current_target_fails_with_choice :
  has_type empty (tm_true secret) (Bool secret) /\
  has_type empty (tm_false secret) (Bool secret) /\
  (exists L : list atom, forall x, ~ In x L ->
    nd_has_type (update empty x (Bool secret)) (C (tm_fvar x)) (Bool public)) /\
  ground (Bool public) /\ transparent (Bool public) /\
  ~ flows_to (security_of (Bool secret)).(indirect_reader)
      (security_of (Bool public)).(indirect_reader) /\
  ~ nd_same_result (C (tm_true secret)) (C (tm_false secret)).
Proof.
  split; [exact secret_true_typed |].
  split; [exact secret_false_typed |].
  split; [exists []; intros; apply C_typed |].
  split; [simpl; auto |].
  split; [exact public_bool_is_transparent |].
  split; [exact secret_cannot_flow_to_public |].
  intro Heq.
  assert (nd_evaluates (C (tm_true secret)) (tm_true public)) as Hleft.
  { destruct (ignore_secret_returns_public_true (tm_true secret)) as [Hs Hv].
    - apply v_inl. apply v_unit.
    - split; [eapply ND_Trans; [apply ND_Left | apply lift_multi; exact Hs] | exact Hv]. }
  assert (nd_evaluates (C (tm_false secret)) (tm_false public)) as Hright.
  { split; [eapply ND_Trans; [apply ND_Right | apply ND_Refl] | apply v_inr; apply v_unit]. }
  specialize (Heq _ _ Hleft Hright). discriminate Heq.
Qed.

End ChoiceCheck.

Module RecursionCheck.

(* This checks the induction obligation for finite unfolding, not a complete
   extension with runtime natural-number terms and a primitive recursor. *)
Fixpoint unfold_natrec (n : nat) (base : tm) (step_function : nat -> tm) : tm :=
  match n with
  | O => base
  | S k => tm_app (step_function k) (unfold_natrec k base step_function) High
  end.

Lemma natrec_compatibility : forall n observer T base1 base2 step1 step2,
  expression_relation observer T base1 base2 ->
  (forall k, expression_relation observer (Ty_Arrow T T public) (step1 k) (step2 k)) ->
  expression_relation observer T
    (unfold_natrec n base1 step1) (unfold_natrec n base2 step2).
Proof.
  induction n; intros observer T base1 base2 step1 step2 Hb Hs; simpl.
  - exact Hb.
  - rewrite <- (ty_protect_low T).
    eapply expression_relation_app with (A := T) (k := public).
    + apply Hs.
    + apply IHn; assumption.
Qed.

Lemma unfolding_typed : forall n T base step_function,
  has_type empty base T ->
  (forall k, has_type empty (step_function k) (Ty_Arrow T T public)) ->
  has_type empty (unfold_natrec n base step_function) T.
Proof.
  induction n; intros T base step_function Hb Hs; simpl.
  - exact Hb.
  - rewrite <- (ty_protect_low T).
    eapply T_App with (T1 := T) (kappa := public).
    + apply Hs.
    + apply IHn; assumption.
    + exact I.
Qed.

Lemma protected_secret_counts_related : forall n m T base1 base2 step1 step2,
  has_type empty base1 T -> has_type empty base2 T ->
  (forall k, has_type empty (step1 k) (Ty_Arrow T T public)) ->
  (forall k, has_type empty (step2 k) (Ty_Arrow T T public)) ->
  expression_relation Low (ty_protect High T)
    (tm_protect High (unfold_natrec n base1 step1))
    (tm_protect High (unfold_natrec m base2 step2)).
Proof.
  intros n m T base1 base2 step1 step2 Hb1 Hb2 Hs1 Hs2.
  apply hidden_expressions_related.
  - destruct T as [k | A B k | A B k | A B k];
      destruct k as [r ir]; destruct r, ir; exact (fun H => H).
  - unfold underlying_typed. apply (typing_erasure empty). apply T_Protect.
    apply unfolding_typed; assumption.
  - unfold underlying_typed. apply (typing_erasure empty). apply T_Protect.
    apply unfolding_typed; assumption.
Qed.

Definition false_step (_ : nat) : tm := tm_abs (Bool public) (tm_false public) public.

Lemma one_iteration_returns_false :
  evaluates (unfold_natrec 1 (tm_true public) false_step) (tm_false public).
Proof.
  split.
  - eapply multi_step.
    + apply ST_AppAbs; [apply v_abs; exact I | apply v_inl; apply v_unit | exact I].
    + eapply multi_step.
      * apply ST_ProtectValue. apply v_inr. apply v_unit.
      * apply multi_refl.
  - apply v_inr. apply v_unit.
Qed.

Theorem secret_iteration_count_requires_protection :
  ~ same_result (unfold_natrec 0 (tm_true public) false_step)
                (unfold_natrec 1 (tm_true public) false_step).
Proof.
  intro H.
  assert (evaluates (unfold_natrec 0 (tm_true public) false_step) (tm_true public)) as Hzero.
  { apply evaluates_value. apply v_inl. apply v_unit. }
  specialize (H _ _ Hzero one_iteration_returns_false). discriminate H.
Qed.

End RecursionCheck.

Print Assumptions IfCheck.if_typing.
Print Assumptions IfCheck.if_true_evaluates.
Print Assumptions IfCheck.if_false_evaluates.
Print Assumptions ChoiceCheck.current_target_fails_with_choice.
Print Assumptions RecursionCheck.natrec_compatibility.
Print Assumptions RecursionCheck.protected_secret_counts_related.
Print Assumptions RecursionCheck.secret_iteration_count_requires_protection.
