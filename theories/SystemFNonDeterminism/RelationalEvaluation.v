From Stdlib Require Import Lists.List.
From AutoProof.SystemFNonDeterminism Require Import Syntax Infrastructure Norm.
Import ListNotations.

Module SystemFRelationalEvaluation.
Import SystemF SystemFInfrastructure SystemFNorm.

Inductive evaluates : tm -> tm -> Prop :=
  | EvalValue : forall v, value v -> evaluates v v
  | EvalApp : forall f arg U body v result,
      evaluates f (tm_abs U body) -> evaluates arg v ->
      evaluates (open_tm body v) result -> evaluates (tm_app f arg) result
  | EvalTApp : forall f U body result,
      evaluates f (tm_tabs body) -> locally_closed_ty U ->
      evaluates (open_tm_ty body U) result -> evaluates (tm_tapp f U) result
  | EvalChoiceLeft : forall t1 t2 v,
      evaluates t1 v -> locally_closed_tm t2 -> evaluates (tm_choice t1 t2) v
  | EvalChoiceRight : forall t1 t2 v,
      locally_closed_tm t1 -> evaluates t2 v -> evaluates (tm_choice t1 t2) v.

Lemma evaluates_value : forall t v, evaluates t v -> value v.
Proof. intros t v H. induction H; assumption. Qed.

Lemma evaluates_lc : forall t v, evaluates t v -> locally_closed_tm t.
Proof.
  intros t v H. induction H.
  - apply value_regular. exact H.
  - apply lc_tm_app; assumption.
  - apply lc_tm_tapp; assumption.
  - apply lc_tm_choice; assumption.
  - apply lc_tm_choice; assumption.
Qed.

Lemma evaluates_value_inv : forall v w,
  value v -> evaluates v w -> w = v.
Proof. intros v w Hv He. inversion He; subst; try reflexivity; inversion Hv. Qed.

Lemma evaluates_app_inv : forall f arg result,
  evaluates (tm_app f arg) result ->
  exists U body v, evaluates f (tm_abs U body) /\ evaluates arg v /\
    evaluates (open_tm body v) result.
Proof.
  intros f arg result H. inversion H; subst.
  - match goal with H : value (tm_app _ _) |- _ => inversion H end.
  - eauto 8.
Qed.

Lemma evaluates_tapp_inv : forall f U result,
  evaluates (tm_tapp f U) result ->
  exists body, evaluates f (tm_tabs body) /\ locally_closed_ty U /\
    evaluates (open_tm_ty body U) result.
Proof.
  intros f U result H. inversion H; subst.
  - match goal with H : value (tm_tapp _ _) |- _ => inversion H end.
  - eauto.
Qed.

Lemma evaluates_choice_inv : forall t1 t2 v,
  evaluates (tm_choice t1 t2) v -> evaluates t1 v \/ evaluates t2 v.
Proof.
  intros t1 t2 v H. inversion H; subst; auto.
  match goal with H : value (tm_choice _ _) |- _ => inversion H end.
Qed.

Lemma multi_trans : forall t u v, t -->* u -> u -->* v -> t -->* v.
Proof. intros t u v H. induction H; eauto using multi. Qed.

Lemma multi_app_left : forall t u arg,
  t -->* u -> locally_closed_tm arg -> tm_app t arg -->* tm_app u arg.
Proof. intros t u arg H. induction H; eauto using multi, step. Qed.

Lemma multi_app_right : forall f t u,
  value f -> t -->* u -> tm_app f t -->* tm_app f u.
Proof. intros f t u Hv H. induction H; eauto using multi, step. Qed.

Lemma multi_tapp : forall t u U,
  t -->* u -> locally_closed_ty U -> tm_tapp t U -->* tm_tapp u U.
Proof. intros t u U H. induction H; eauto using multi, step. Qed.

Lemma evaluates_smallstep : forall t v, evaluates t v -> t -->* v.
Proof.
  intros t v H. induction H.
  - constructor.
  - eapply multi_trans. apply multi_app_left. exact IHevaluates1.
    eapply evaluates_lc; eauto.
    eapply multi_trans. apply multi_app_right.
    eapply evaluates_value; eauto. exact IHevaluates2.
    eapply multi_step. apply ST_AppAbs.
    apply value_regular. eapply evaluates_value; eauto.
    eapply evaluates_value; eauto. exact IHevaluates3.
  - eapply multi_trans. apply multi_tapp; eauto.
    eapply multi_step. apply ST_TAppTabs; auto.
    apply value_regular. eapply evaluates_value; eauto. exact IHevaluates2.
  - eapply multi_step. apply ST_ChoiceLeft; auto.
    eapply evaluates_lc; eauto. exact IHevaluates.
  - eapply multi_step. apply ST_ChoiceRight; auto.
    eapply evaluates_lc; eauto. exact IHevaluates.
Qed.

Lemma evaluates_backward : forall t u v,
  t --> u -> evaluates u v -> evaluates t v.
Proof.
  intros t u v Hstep. revert v. induction Hstep; intros result He.
  - eapply EvalApp; eauto using EvalValue, value.
  - destruct (evaluates_app_inv _ _ _ He) as [U [body [v [Hf [Ha Hb]]]]].
    eapply EvalApp; eauto.
  - destruct (evaluates_app_inv _ _ _ He) as [U [body [v [Hf [Ha Hb]]]]].
    eapply EvalApp; eauto.
  - eapply EvalTApp; eauto using EvalValue, value.
  - destruct (evaluates_tapp_inv _ _ _ He) as [body [Hf [HU Hb]]].
    eapply EvalTApp; eauto.
  - eapply EvalChoiceLeft; eauto.
  - eapply EvalChoiceRight; eauto.
Qed.

Lemma smallstep_evaluates : forall t v,
  t -->* v -> value v -> evaluates t v.
Proof.
  intros t v H. induction H; eauto using evaluates_backward, EvalValue.
Qed.

Theorem evaluates_iff_smallstep : forall t v,
  evaluates t v <-> t -->* v /\ value v.
Proof.
  split; intros H.
  - split; eauto using evaluates_smallstep, evaluates_value.
  - destruct H. eauto using smallstep_evaluates.
Qed.

End SystemFRelationalEvaluation.
