From AutoProof.SecurityNoninterference Require Export Semantics.

(* A terminating evaluation, with its subcomputations exposed.  This is proved
   equivalent to [evaluates] below; it does not change the operational semantics. *)
Inductive big_step : tm -> tm -> Prop :=
  | B_Unit : forall k,
      big_step (tm_unit k) (tm_unit k)
  | B_Abs : forall A body k,
      locally_closed (tm_abs A body k) ->
      big_step (tm_abs A body k) (tm_abs A body k)
  | B_App : forall f a r A body k v w,
      big_step f (tm_abs A body k) -> big_step a v ->
      flows_to k.(reader) r -> big_step (open body v) w ->
      big_step (tm_app f a r) (protect_value w k.(indirect_reader))
  | B_Pair : forall a b k v w,
      big_step a v -> big_step b w ->
      big_step (tm_pair a b k) (tm_pair v w k)
  | B_Fst : forall t r a b k,
      big_step t (tm_pair a b k) -> flows_to k.(reader) r ->
      big_step (tm_fst t r) (protect_value a k.(indirect_reader))
  | B_Snd : forall t r a b k,
      big_step t (tm_pair a b k) -> flows_to k.(reader) r ->
      big_step (tm_snd t r) (protect_value b k.(indirect_reader))
  | B_Inl : forall t k v,
      big_step t v -> big_step (tm_inl t k) (tm_inl v k)
  | B_Inr : forall t k v,
      big_step t v -> big_step (tm_inr t k) (tm_inr v k)
  | B_CaseLeft : forall t b1 b2 r v k w,
      big_step t (tm_inl v k) -> flows_to k.(reader) r ->
      big_step (open b1 v) w ->
      big_step (tm_case t b1 b2 r) (protect_value w k.(indirect_reader))
  | B_CaseRight : forall t b1 b2 r v k w,
      big_step t (tm_inr v k) -> flows_to k.(reader) r ->
      big_step (open b2 v) w ->
      big_step (tm_case t b1 b2 r) (protect_value w k.(indirect_reader))
  | B_Protect : forall l t v,
      big_step t v -> big_step (tm_protect l t) (protect_value v l).

Lemma value_protect : forall v l, value v -> value (protect_value v l).
Proof.
  intros v l Hv. inversion Hv; subst; simpl;
    eauto using v_unit, v_abs, v_pair, v_inl, v_inr.
Qed.

Lemma big_step_result_value : forall t v, big_step t v -> value v.
Proof.
  intros t v H. induction H;
    eauto using v_unit, v_abs, v_pair, v_inl, v_inr, value_protect.
  - inversion IHbig_step; subst. apply value_protect; assumption.
  - inversion IHbig_step; subst. apply value_protect; assumption.
Qed.

Lemma big_step_value_refl : forall v, value v -> big_step v v.
Proof.
  intros v Hv. induction Hv;
    eauto using B_Unit, B_Abs, B_Pair, B_Inl, B_Inr.
Qed.

Lemma big_step_value_inv : forall v w, value v -> big_step v w -> w = v.
Proof.
  intros v w Hv. generalize dependent w. induction Hv;
    intros w Heval; inversion Heval; subst; f_equal; eauto.
Qed.

Lemma multi_congruence : forall (C : tm -> tm),
  (forall t t', step t t' -> step (C t) (C t')) ->
  forall t t', multi t t' -> multi (C t) (C t').
Proof.
  intros C HC t t' H. induction H.
  - apply multi_refl.
  - eapply multi_step; [apply HC; exact H | exact IHmulti].
Qed.

Lemma big_step_sound : forall t v, big_step t v -> evaluates t v.
Proof.
  intros t v H. split; [| eapply big_step_result_value; exact H].
  induction H.
  - apply multi_refl.
  - apply multi_refl.
  - eapply multi_trans.
    + apply (multi_congruence (fun f => tm_app f a r)); eauto using ST_App1.
    + eapply multi_trans.
      * apply (multi_congruence (fun a => tm_app (tm_abs A body k) a r));
          eauto using ST_App2, big_step_result_value.
      * eapply multi_step.
        -- eapply ST_AppAbs; eauto using big_step_result_value.
        -- eapply multi_trans.
           ++ apply (multi_congruence (tm_protect k.(indirect_reader)));
                eauto using ST_Protect.
           ++ eapply multi_step; [apply ST_ProtectValue;
                eauto using big_step_result_value | apply multi_refl].
  - eapply multi_trans.
    + apply (multi_congruence (fun a => tm_pair a b k)); eauto using ST_Pair1.
    + apply (multi_congruence (fun b => tm_pair v b k));
        eauto using ST_Pair2, big_step_result_value.
  - eapply multi_trans.
    + apply (multi_congruence (fun t => tm_fst t r)); eauto using ST_Fst.
    + pose proof (big_step_result_value _ _ H) as Hv. inversion Hv; subst.
      eapply multi_step; [apply ST_FstPair; eassumption |].
      eapply multi_step; [apply ST_ProtectValue; assumption | apply multi_refl].
  - eapply multi_trans.
    + apply (multi_congruence (fun t => tm_snd t r)); eauto using ST_Snd.
    + pose proof (big_step_result_value _ _ H) as Hv. inversion Hv; subst.
      eapply multi_step; [apply ST_SndPair; eassumption |].
      eapply multi_step; [apply ST_ProtectValue; assumption | apply multi_refl].
  - apply (multi_congruence (fun t => tm_inl t k)); eauto using ST_Inl.
  - apply (multi_congruence (fun t => tm_inr t k)); eauto using ST_Inr.
  - eapply multi_trans.
    + apply (multi_congruence (fun t => tm_case t b1 b2 r)); eauto using ST_Case.
    + pose proof (big_step_result_value _ _ H) as Hv. inversion Hv; subst.
      eapply multi_step; [apply ST_CaseLeft; eassumption |].
      eapply multi_trans.
      * apply (multi_congruence (tm_protect k.(indirect_reader)));
          eauto using ST_Protect.
      * eapply multi_step; [apply ST_ProtectValue;
          eauto using big_step_result_value | apply multi_refl].
  - eapply multi_trans.
    + apply (multi_congruence (fun t => tm_case t b1 b2 r)); eauto using ST_Case.
    + pose proof (big_step_result_value _ _ H) as Hv. inversion Hv; subst.
      eapply multi_step; [apply ST_CaseRight; eassumption |].
      eapply multi_trans.
      * apply (multi_congruence (tm_protect k.(indirect_reader)));
          eauto using ST_Protect.
      * eapply multi_step; [apply ST_ProtectValue;
          eauto using big_step_result_value | apply multi_refl].
  - eapply multi_trans.
    + apply (multi_congruence (tm_protect l)); eauto using ST_Protect.
    + eapply multi_step; [apply ST_ProtectValue;
        eauto using big_step_result_value | apply multi_refl].
Qed.

Lemma step_big_step : forall t t', step t t' ->
  forall v, big_step t' v -> big_step t v.
Proof.
  intros t t' Hstep. induction Hstep; intros result Heval.
  all: try solve [
    pose proof (big_step_value_inv _ _ (value_protect _ _ H) Heval) as ->;
    apply B_Protect; apply big_step_value_refl; exact H].
  all: inversion Heval; subst;
    eauto using B_Unit, B_Abs, B_App, B_Pair, B_Fst, B_Snd,
      B_Inl, B_Inr, B_CaseLeft, B_CaseRight, B_Protect,
      big_step_value_refl.
  all: try (match goal with Hv : value ?v, He : big_step ?v ?w |- _ =>
    pose proof (big_step_value_inv v w Hv He); subst w end).
  all: try solve [eauto using B_App, B_Fst, B_Snd, B_CaseLeft,
    B_CaseRight, B_Protect, B_Pair, B_Inl, B_Inr, big_step_value_refl].
Qed.

Theorem big_step_iff_evaluates : forall t v, big_step t v <-> evaluates t v.
Proof.
  intros t v. split; [apply big_step_sound |].
  intros [Hsteps Hv]. induction Hsteps.
  - apply big_step_value_refl; exact Hv.
  - eapply step_big_step; [exact H | apply IHHsteps; exact Hv].
Qed.

Lemma protect_value_compose : forall v l1 l2,
  protect_value (protect_value v l1) l2 = protect_value v (join l1 l2).
Proof.
  intros v l1 l2. destruct v; simpl; try reflexivity;
    match goal with k : security |- _ => destruct k as [r ir] end;
    destruct r, ir, l1, l2; reflexivity.
Qed.

Lemma erase_protect_value : forall v l,
  erase_security (protect_value v l) = erase_security v.
Proof. intros v l. destruct v; reflexivity. Qed.

Lemma evaluates_protected_function : forall f arg l result,
  value f -> value arg ->
  evaluates (tm_app (protect_value f l) arg High) result ->
  exists original,
    evaluates (tm_app f arg High) original /\
    result = protect_value original l.
Proof.
  intros f arg l result Hf Ha Heval.
  apply big_step_iff_evaluates in Heval. inversion Heval; subst.
  match goal with H : big_step (protect_value f l) _ |- _ =>
    pose proof (big_step_value_inv _ _ (value_protect _ _ Hf) H) as Hshape
  end.
  destruct f; simpl in Hshape; try discriminate Hshape.
  inversion Hshape; subst.
  match goal with H : big_step arg _ |- _ =>
    pose proof (big_step_value_inv _ _ Ha H) as ->
  end.
  exists (protect_value w s.(indirect_reader)). split.
  - apply big_step_iff_evaluates. eapply B_App;
      eauto using big_step_value_refl.
    destruct s.(reader); exact I.
  - rewrite protect_value_compose. reflexivity.
Qed.
