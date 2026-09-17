From Stdlib Require Import Lists.List.
From AutoProof.SystemFRecursion Require Import Syntax Infrastructure Norm.
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
  | EvalSucc : forall t n,
      evaluates t n -> numeric_value n -> evaluates (tm_succ t) (tm_succ n)
  | EvalRecZero : forall n b s vb vs,
      evaluates n tm_zero -> evaluates b vb -> evaluates s vs ->
      evaluates (tm_natrec n b s) vb
  | EvalRecSucc : forall n b s k vb vs result,
      evaluates n (tm_succ k) -> numeric_value k ->
      evaluates b vb -> evaluates s vs ->
      evaluates (tm_app (tm_app vs k) (tm_natrec k vb vs)) result ->
      evaluates (tm_natrec n b s) result.

Lemma evaluates_value : forall t v, evaluates t v -> value v.
Proof. intros t v H. induction H; try assumption. apply v_nat. constructor; assumption. Qed.

Lemma evaluates_lc : forall t v, evaluates t v -> locally_closed_tm t.
Proof.
  intros t v H. induction H.
  - apply value_regular. exact H.
  - apply lc_tm_app; assumption.
  - apply lc_tm_tapp; assumption.
  - apply lc_tm_succ; assumption.
  - apply lc_tm_rec; assumption.
  - apply lc_tm_rec; assumption.
Qed.

Lemma evaluates_value_inv : forall v w,
  value v -> evaluates v w -> w = v.
Proof.
  intros v w Hv He. revert Hv. induction He; intros Hv; try reflexivity.
  - inversion Hv; subst. match goal with H : numeric_value (tm_app _ _) |- _ => inversion H end.
  - inversion Hv; subst. match goal with H : numeric_value (tm_tapp _ _) |- _ => inversion H end.
  - inversion Hv; subst.
    match goal with H : numeric_value (tm_succ _) |- _ => inversion H; subst end.
    f_equal. apply IHHe. apply v_nat. assumption.
  - inversion Hv; subst. match goal with H : numeric_value (tm_natrec _ _ _) |- _ => inversion H end.
  - inversion Hv; subst. match goal with H : numeric_value (tm_natrec _ _ _) |- _ => inversion H end.
Qed.

Lemma evaluates_app_inv : forall f arg result,
  evaluates (tm_app f arg) result ->
  exists U body v, evaluates f (tm_abs U body) /\ evaluates arg v /\
    evaluates (open_tm body v) result.
Proof.
  intros f arg result H. inversion H; subst.
  - match goal with H : value (tm_app _ _) |- _ => inversion H end.
    match goal with H : numeric_value (tm_app _ _) |- _ => inversion H end.
  - eauto 8.
Qed.

Lemma evaluates_tapp_inv : forall f U result,
  evaluates (tm_tapp f U) result ->
  exists body, evaluates f (tm_tabs body) /\ locally_closed_ty U /\
    evaluates (open_tm_ty body U) result.
Proof.
  intros f U result H. inversion H; subst.
  - match goal with H : value (tm_tapp _ _) |- _ => inversion H end.
    match goal with H : numeric_value (tm_tapp _ _) |- _ => inversion H end.
  - eauto.
Qed.

Lemma evaluates_succ_inv : forall t v,
  evaluates (tm_succ t) v ->
  exists n, v = tm_succ n /\ numeric_value n /\ evaluates t n.
Proof.
  intros t v H. inversion H; subst.
  - match goal with H : value (tm_succ _) |- _ => inversion H; subst end.
    match goal with H : numeric_value (tm_succ _) |- _ => inversion H; subst end.
    exists t. repeat split; eauto using EvalValue, v_nat.
  - eauto.
Qed.

Lemma evaluates_rec_inv : forall n b s result,
  evaluates (tm_natrec n b s) result ->
  (exists vs, evaluates n tm_zero /\ evaluates b result /\ evaluates s vs) \/
  (exists k vb vs, evaluates n (tm_succ k) /\ numeric_value k /\
    evaluates b vb /\ evaluates s vs /\
    evaluates (tm_app (tm_app vs k) (tm_natrec k vb vs)) result).
Proof.
  intros n b s result H. inversion H; subst; eauto 10.
  match goal with H : value (tm_natrec _ _ _) |- _ => inversion H; subst end.
  match goal with H : numeric_value (tm_natrec _ _ _) |- _ => inversion H end.
Qed.

Lemma evaluates_rec_zero : forall b s result,
  value b -> value s ->
  (evaluates (tm_natrec tm_zero b s) result <-> evaluates b result).
Proof.
  intros b s result Hb Hs. split; intros H.
  - destruct (evaluates_rec_inv _ _ _ _ H) as [[vs [En [Eb Es]]]|[k [vb [vs [En [Hk [Eb [Es Er]]]]]]]].
    + exact Eb.
    + pose proof (evaluates_value_inv _ _ (v_nat _ nv_zero) En). discriminate.
  - eapply EvalRecZero; eauto using EvalValue, v_nat, nv_zero.
Qed.

Lemma evaluates_rec_succ : forall n b s result,
  numeric_value n -> value b -> value s ->
  (evaluates (tm_natrec (tm_succ n) b s) result <->
   evaluates (tm_app (tm_app s n) (tm_natrec n b s)) result).
Proof.
  intros n b s result Hn Hb Hs. split; intros H.
  - destruct (evaluates_rec_inv _ _ _ _ H) as [[vs [En [Eb Es]]]|[k [vb [vs [En [Hk [Eb [Es Er]]]]]]]].
    + pose proof (evaluates_value_inv _ _ (v_nat _ (nv_succ _ Hn)) En). discriminate.
    + pose proof (evaluates_value_inv _ _ (v_nat _ (nv_succ _ Hn)) En) as E.
      injection E as ->.
      pose proof (evaluates_value_inv _ _ Hb Eb) as ->.
      pose proof (evaluates_value_inv _ _ Hs Es) as ->. exact Er.
  - eapply EvalRecSucc; eauto using EvalValue, v_nat, nv_succ.
Qed.

Lemma evaluates_rec_factor : forall n b s result,
  evaluates (tm_natrec n b s) result ->
  exists nv bv sv, evaluates n nv /\ numeric_value nv /\
    evaluates b bv /\ evaluates s sv /\ evaluates (tm_natrec nv bv sv) result.
Proof.
  intros n b s result H.
  destruct (evaluates_rec_inv _ _ _ _ H) as [[vs [En [Eb Es]]]|[k [vb [vs [En [Hk [Eb [Es Er]]]]]]]].
  - exists tm_zero, result, vs. repeat split; auto using nv_zero.
    eapply EvalRecZero; eauto using EvalValue, v_nat, nv_zero, evaluates_value.
  - exists (tm_succ k), vb, vs. repeat split; auto using nv_succ.
    eapply EvalRecSucc; eauto using EvalValue, v_nat, nv_succ, evaluates_value.
Qed.

Lemma evaluates_rec_rebuild : forall n b s nv bv sv result,
  evaluates n nv -> evaluates b bv -> evaluates s sv ->
  evaluates (tm_natrec nv bv sv) result -> evaluates (tm_natrec n b s) result.
Proof.
  intros n b s nv bv sv result Hn Hb Hs H.
  pose proof (evaluates_value _ _ Hn) as Hnv.
  pose proof (evaluates_value _ _ Hb) as Hbv.
  pose proof (evaluates_value _ _ Hs) as Hsv.
  destruct (evaluates_rec_inv _ _ _ _ H) as [[vs [En [Eb Es]]]|[k [vb [vs [En [Hk [Eb [Es Er]]]]]]]].
  - pose proof (evaluates_value_inv _ _ Hnv En) as E. subst nv.
    pose proof (evaluates_value_inv _ _ Hbv Eb) as ->.
    pose proof (evaluates_value_inv _ _ Hsv Es) as ->.
    eapply EvalRecZero; eauto.
  - pose proof (evaluates_value_inv _ _ Hnv En) as E. subst nv.
    pose proof (evaluates_value_inv _ _ Hbv Eb) as ->.
    pose proof (evaluates_value_inv _ _ Hsv Es) as ->.
    eapply EvalRecSucc; eauto.
Qed.

Lemma multi_succ : forall t u, t -->* u -> tm_succ t -->* tm_succ u.
Proof. intros t u H. induction H; eauto using multi, step. Qed.
Lemma multi_rec_arg : forall n n' b s,
  n -->* n' -> locally_closed_tm b -> locally_closed_tm s ->
  tm_natrec n b s -->* tm_natrec n' b s.
Proof. intros n n' b s H. induction H; eauto using multi, step. Qed.
Lemma multi_rec_base : forall n b b' s,
  numeric_value n -> b -->* b' -> locally_closed_tm s ->
  tm_natrec n b s -->* tm_natrec n b' s.
Proof. intros n b b' s Hn H. induction H; eauto using multi, step. Qed.
Lemma multi_rec_step : forall n b s s',
  numeric_value n -> value b -> s -->* s' ->
  tm_natrec n b s -->* tm_natrec n b s'.
Proof. intros n b s s' Hn Hb H. induction H; eauto using multi, step. Qed.

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
  - apply multi_succ. exact IHevaluates.
  - eapply multi_trans. apply multi_rec_arg; eauto using evaluates_lc.
    eapply multi_trans. apply multi_rec_base; eauto using evaluates_lc, nv_zero.
    eapply multi_trans. apply multi_rec_step; eauto using evaluates_value, nv_zero.
    eapply multi_step. apply ST_RecZero; eauto using evaluates_value. constructor.
  - eapply multi_trans. apply multi_rec_arg; eauto using evaluates_lc.
    eapply multi_trans. apply multi_rec_base; eauto using evaluates_lc, nv_succ.
    eapply multi_trans. apply multi_rec_step; eauto using evaluates_value, nv_succ.
    eapply multi_step. apply ST_RecSucc; eauto using evaluates_value. exact IHevaluates4.
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
  - destruct (evaluates_succ_inv _ _ He) as [n [-> [Hn Hen]]].
    apply EvalSucc; auto.
  - destruct (evaluates_rec_inv _ _ _ _ He) as [[vs [En [Eb Es]]]|[k [vb [vs [En [Hk [Eb [Es Er]]]]]]]];
      eauto using EvalRecZero, EvalRecSucc.
  - destruct (evaluates_rec_inv _ _ _ _ He) as [[vs [En [Eb Es]]]|[k [vb [vs [En [Hk [Eb [Es Er]]]]]]]];
      eauto using EvalRecZero, EvalRecSucc.
  - destruct (evaluates_rec_inv _ _ _ _ He) as [[vs [En [Eb Es]]]|[k [vb [vs [En [Hk [Eb [Es Er]]]]]]]];
      eauto using EvalRecZero, EvalRecSucc.
  - pose proof (evaluates_value_inv _ _ H He) as ->.
    eapply EvalRecZero; eauto using EvalValue, v_nat, nv_zero.
  - eapply EvalRecSucc; eauto using EvalValue, v_nat, nv_succ.
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
