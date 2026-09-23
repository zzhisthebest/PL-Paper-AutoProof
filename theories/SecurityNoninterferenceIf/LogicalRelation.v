From AutoProof.SecurityNoninterferenceIf Require Export Substitution.
From AutoProof.SecurityNoninterferenceIf Require Import Evaluation.
Import ListNotations.

Definition expression_lifting (R : tm -> tm -> Prop) (t1 t2 : tm) : Prop :=
  forall v1 v2 : tm, evaluates t1 v1 -> evaluates t2 v2 -> R v1 v2.

Definition underlying_typed (T : ty) (t : tm) : Prop :=
  has_type empty (erase_security t) (erase_type T).

Fixpoint value_relation (observer : label) (T : ty) (v1 v2 : tm) : Prop :=
  value v1 /\ value v2 /\
  underlying_typed T v1 /\ underlying_typed T v2 /\
  (flows_to (security_of T).(indirect_reader) observer ->
    match T with
    | Ty_Unit _ =>
        exists kappa1 kappa2 : security,
          v1 = tm_unit kappa1 /\ v2 = tm_unit kappa2
    | Ty_Sum T1 T2 _ =>
        (exists (u1 u2 : tm) (kappa1 kappa2 : security),
          v1 = tm_inl u1 kappa1 /\ v2 = tm_inl u2 kappa2 /\
          value_relation observer T1 u1 u2) \/
        (exists (u1 u2 : tm) (kappa1 kappa2 : security),
          v1 = tm_inr u1 kappa1 /\ v2 = tm_inr u2 kappa2 /\
          value_relation observer T2 u1 u2)
    | Ty_Prod T1 T2 _ =>
        exists (a1 b1 a2 b2 : tm) (kappa1 kappa2 : security),
          v1 = tm_pair a1 b1 kappa1 /\ v2 = tm_pair a2 b2 kappa2 /\
          value_relation observer T1 a1 a2 /\
          value_relation observer T2 b1 b2
    | Ty_Arrow T1 T2 _ =>
        exists (U1 U2 : ty) (body1 body2 : tm) (kappa1 kappa2 : security),
          v1 = tm_abs U1 body1 kappa1 /\ v2 = tm_abs U2 body2 kappa2 /\
          forall arg1 arg2 : tm,
            value_relation observer T1 arg1 arg2 ->
            expression_lifting (value_relation observer T2)
              (tm_app v1 arg1 High) (tm_app v2 arg2 High)
    end).

Definition expression_relation (observer : label) (T : ty) (t1 t2 : tm) : Prop :=
  underlying_typed T t1 /\ underlying_typed T t2 /\
  expression_lifting (value_relation observer T) t1 t2.

Lemma value_relation_properties : forall observer T v1 v2,
  value_relation observer T v1 v2 ->
  value v1 /\ value v2 /\ underlying_typed T v1 /\ underlying_typed T v2.
Proof. intros observer T. destruct T; simpl; tauto. Qed.

Lemma value_relation_protect_values : forall T observer v1 v2 l1 l2,
  value_relation observer T v1 v2 ->
  value_relation observer T (protect_value v1 l1) (protect_value v2 l2).
Proof.
  induction T; intros observer v1 v2 l1 l2 Hrel;
    destruct Hrel as [Hv1 [Hv2 [Ht1 [Ht2 Hrel]]]].
  all: split; [apply value_protect; exact Hv1 |].
  all: split; [apply value_protect; exact Hv2 |].
  all: split; [unfold underlying_typed; rewrite erase_protect_value; exact Ht1 |].
  all: split; [unfold underlying_typed; rewrite erase_protect_value; exact Ht2 |].
  all: intros Hvis; specialize (Hrel Hvis).
  - destruct Hrel as [k1 [k2 [-> ->]]].
    exists (protect_security k1 l1), (protect_security k2 l2). auto.
  - destruct Hrel as [Hl | Hr].
    + left. destruct Hl as [a1 [a2 [k1 [k2 [-> [-> Ha]]]]]].
      exists a1, a2, (protect_security k1 l1), (protect_security k2 l2). auto.
    + right. destruct Hr as [a1 [a2 [k1 [k2 [-> [-> Ha]]]]]].
      exists a1, a2, (protect_security k1 l1), (protect_security k2 l2). auto.
  - destruct Hrel as [a1 [b1 [a2 [b2 [k1 [k2 [-> [-> [Ha Hb]]]]]]]]].
    exists a1, b1, a2, b2, (protect_security k1 l1), (protect_security k2 l2). auto.
  - destruct Hrel as [A1 [A2 [b1 [b2 [k1 [k2 [-> [-> Hfun]]]]]]]].
    exists A1, A2, b1, b2, (protect_security k1 l1), (protect_security k2 l2).
    split; [reflexivity |]. split; [reflexivity |].
    intros a1 a2 Ha w1 w2 Heval1 Heval2.
    destruct (value_relation_properties _ _ _ _ Ha) as [Ha1 [Ha2 _]].
    destruct (evaluates_protected_function _ _ _ _ Hv1 Ha1 Heval1)
      as [u1 [Hu1 ->]].
    destruct (evaluates_protected_function _ _ _ _ Hv2 Ha2 Heval2)
      as [u2 [Hu2 ->]].
    apply IHT2. eapply Hfun; eassumption.
Qed.

Lemma value_relation_ty_protect : forall T observer l v1 v2,
  value_relation observer (ty_protect l T) v1 v2 <->
  value v1 /\ value v2 /\ underlying_typed T v1 /\ underlying_typed T v2 /\
  (flows_to l observer -> value_relation observer T v1 v2).
Proof.
  intros T observer l v1 v2. destruct T; destruct s as [r ir];
    destruct r, ir, observer, l; simpl; unfold underlying_typed; simpl; tauto.
Qed.

Lemma value_relation_protect : forall T observer l v1 v2,
  value_relation observer T v1 v2 ->
  value_relation observer (ty_protect l T)
    (protect_value v1 l) (protect_value v2 l).
Proof.
  intros T observer l v1 v2 Hrel.
  destruct (value_relation_properties _ _ _ _ Hrel) as [Hv1 [Hv2 [Ht1 Ht2]]].
  apply value_relation_ty_protect.
  split; [apply value_protect; exact Hv1 |].
  split; [apply value_protect; exact Hv2 |].
  split; [unfold underlying_typed; rewrite erase_protect_value; exact Ht1 |].
  split; [unfold underlying_typed; rewrite erase_protect_value; exact Ht2 |].
  intros _. apply value_relation_protect_values; assumption.
Qed.

Lemma underlying_typed_evaluates : forall T t v,
  underlying_typed T t -> evaluates t v -> underlying_typed T v.
Proof.
  intros T t v Ht Heval. unfold underlying_typed in *.
  destruct (evaluates_erasure _ _ Heval) as [Hsteps _].
  eapply preservation_multi; eassumption.
Qed.

Lemma hidden_values_related : forall observer T v1 v2,
  ~ flows_to (security_of T).(indirect_reader) observer ->
  value v1 -> value v2 -> underlying_typed T v1 -> underlying_typed T v2 ->
  value_relation observer T v1 v2.
Proof.
  intros observer T v1 v2 Hhidden Hv1 Hv2 Ht1 Ht2.
  destruct T.
  all: split; [exact Hv1 |].
  all: split; [exact Hv2 |].
  all: split; [exact Ht1 |].
  all: split; [exact Ht2 |].
  all: contradiction.
Qed.

Lemma hidden_expressions_related : forall observer T t1 t2,
  ~ flows_to (security_of T).(indirect_reader) observer ->
  underlying_typed T t1 -> underlying_typed T t2 ->
  expression_relation observer T t1 t2.
Proof.
  intros observer T t1 t2 Hhidden Ht1 Ht2.
  split; [exact Ht1 |]. split; [exact Ht2 |].
  intros v1 v2 Heval1 Heval2. apply hidden_values_related; try assumption.
  - exact (proj2 Heval1).
  - exact (proj2 Heval2).
  - exact (underlying_typed_evaluates _ _ _ Ht1 Heval1).
  - exact (underlying_typed_evaluates _ _ _ Ht2 Heval2).
Qed.

Lemma expression_relation_protect : forall observer T t1 t2 l,
  expression_relation observer T t1 t2 ->
  expression_relation observer (ty_protect l T)
    (tm_protect l t1) (tm_protect l t2).
Proof.
  intros observer T t1 t2 l [Ht1 [Ht2 Hrel]].
  split; [unfold underlying_typed in *; simpl; rewrite erase_ty_protect; exact Ht1 |].
  split; [unfold underlying_typed in *; simpl; rewrite erase_ty_protect; exact Ht2 |].
  intros v1 v2 Heval1 Heval2.
  apply big_step_iff_evaluates in Heval1, Heval2.
  inversion Heval1; subst. inversion Heval2; subst.
  apply value_relation_protect. apply Hrel;
    apply big_step_iff_evaluates; assumption.
Qed.

Lemma flows_to_dec : forall l observer,
  {flows_to l observer} + {~ flows_to l observer}.
Proof. destruct l, observer; simpl; auto. Defined.

Lemma visible_ty_protect : forall T l observer,
  flows_to (security_of (ty_protect l T)).(indirect_reader) observer ->
  flows_to l observer.
Proof.
  destruct T; intros l observer; destruct s as [r ir];
    destruct ir, l, observer; simpl; tauto.
Qed.

Lemma value_relation_raise_type : forall observer T l v1 v2,
  value_relation observer T v1 v2 ->
  value_relation observer (ty_protect l T) v1 v2.
Proof.
  intros observer T l v1 v2 H.
  destruct (value_relation_properties _ _ _ _ H) as [Hv1 [Hv2 [Ht1 Ht2]]].
  apply value_relation_ty_protect. auto.
Qed.

Lemma expression_relation_app : forall observer A B k f1 f2 a1 a2 r,
  expression_relation observer (Ty_Arrow A B k) f1 f2 ->
  expression_relation observer A a1 a2 ->
  expression_relation observer (ty_protect k.(indirect_reader) B)
    (tm_app f1 a1 r) (tm_app f2 a2 r).
Proof.
  intros observer A B k f1 f2 a1 a2 r [Hf1 [Hf2 Hf]] [Ha1 [Ha2 Ha]].
  assert (underlying_typed (ty_protect k.(indirect_reader) B)
    (tm_app f1 a1 r)) as Htyped1.
  { unfold underlying_typed in *. simpl. rewrite erase_ty_protect.
    rewrite <- (ty_protect_low (erase_type B)).
    eapply T_App with (kappa := public); [exact Hf1 | exact Ha1 | exact I]. }
  assert (underlying_typed (ty_protect k.(indirect_reader) B)
    (tm_app f2 a2 r)) as Htyped2.
  { unfold underlying_typed in *. simpl. rewrite erase_ty_protect.
    rewrite <- (ty_protect_low (erase_type B)).
    eapply T_App with (kappa := public); [exact Hf2 | exact Ha2 | exact I]. }
  destruct (flows_to_dec k.(indirect_reader) observer) as [Hvis | Hhidden].
  - split; [exact Htyped1 |]. split; [exact Htyped2 |].
    intros w1 w2 Heval1 Heval2.
    apply big_step_iff_evaluates in Heval1, Heval2.
    inversion Heval1; subst. inversion Heval2; subst.
    assert (value_relation observer (Ty_Arrow A B k)
      (tm_abs A0 body k0) (tm_abs A1 body0 k1)) as Hfunctions.
    { apply Hf; apply big_step_iff_evaluates; assumption. }
    destruct Hfunctions as [Hval1 [Hval2 [_ [_ Hfunctions]]]].
    specialize (Hfunctions Hvis).
    destruct Hfunctions as [U1 [U2 [b1 [b2 [ka [kb [E1 [E2 Hfunctions]]]]]]]].
    inversion E1; inversion E2; subst.
    apply value_relation_raise_type.
    eapply Hfunctions.
    + apply Ha; apply big_step_iff_evaluates; eassumption.
    + apply big_step_iff_evaluates. eapply B_App;
        eauto using big_step_value_refl, big_step_result_value.
      destruct ka.(reader); exact I.
    + apply big_step_iff_evaluates. eapply B_App;
        eauto using big_step_value_refl, big_step_result_value.
      destruct kb.(reader); exact I.
  - apply hidden_expressions_related; try assumption.
    intro Hvisible. apply Hhidden. eapply visible_ty_protect; exact Hvisible.
Qed.

Lemma related_values_are_related_expressions : forall observer T v1 v2,
  value_relation observer T v1 v2 -> expression_relation observer T v1 v2.
Proof.
  intros observer T v1 v2 Hrelated.
  destruct (value_relation_properties _ _ _ _ Hrelated) as [Hv1 [Hv2 [Ht1 Ht2]]].
  split; [exact Ht1 | ]. split; [exact Ht2 | ].
  intros u1 u2 [Hsteps1 _] [Hsteps2 _].
  apply (value_multi_inv _ _ Hv1) in Hsteps1.
  apply (value_multi_inv _ _ Hv2) in Hsteps2.
  subst u1 u2. exact Hrelated.
Qed.

Lemma expression_relation_unit : forall observer k,
  expression_relation observer (Ty_Unit k) (tm_unit k) (tm_unit k).
Proof.
  intros observer k. apply related_values_are_related_expressions.
  split; [constructor |]. split; [constructor |].
  split; [apply T_Unit; exact I |]. split; [apply T_Unit; exact I |].
  intros _. exists k, k. auto.
Qed.

Lemma expression_relation_abs : forall observer A B k body1 body2,
  underlying_typed (Ty_Arrow A B k) (tm_abs A body1 k) ->
  underlying_typed (Ty_Arrow A B k) (tm_abs A body2 k) ->
  locally_closed (tm_abs A body1 k) -> locally_closed (tm_abs A body2 k) ->
  (forall a1 a2, value_relation observer A a1 a2 ->
    expression_relation observer B (open body1 a1) (open body2 a2)) ->
  expression_relation observer (Ty_Arrow A B k)
    (tm_abs A body1 k) (tm_abs A body2 k).
Proof.
  intros observer A B k body1 body2 Ht1 Ht2 Hlc1 Hlc2 Hb.
  apply related_values_are_related_expressions.
  split; [apply v_abs; exact Hlc1 |]. split; [apply v_abs; exact Hlc2 |].
  split; [exact Ht1 |]. split; [exact Ht2 |]. intros Hvis.
  exists A, A, body1, body2, k, k. split; [reflexivity |]. split; [reflexivity |].
  intros a1 a2 Ha w1 w2 He1 He2.
  destruct (value_relation_properties _ _ _ _ Ha) as [Hva1 [Hva2 _]].
  destruct (Hb a1 a2 Ha) as [_ [_ Hbody]].
  apply big_step_iff_evaluates in He1, He2.
  inversion He1; subst. inversion He2; subst.
  repeat match goal with
  | He : big_step (tm_abs _ _ _) _ |- _ => inversion He; subst; clear He
  | Hv : value ?v, He : big_step ?v ?w |- _ =>
      pose proof (big_step_value_inv _ _ Hv He) as ->; clear He
  end.
  apply value_relation_protect_values.
  apply Hbody; apply big_step_iff_evaluates; assumption.
Qed.

Lemma expression_relation_pair : forall observer A B k a1 a2 b1 b2,
  expression_relation observer A a1 a2 ->
  expression_relation observer B b1 b2 ->
  expression_relation observer (Ty_Prod A B k)
    (tm_pair a1 b1 k) (tm_pair a2 b2 k).
Proof.
  intros observer A B k a1 a2 b1 b2 [Ha1 [Ha2 Ha]] [Hb1 [Hb2 Hb]].
  split; [apply T_Pair; [exact Ha1 | exact Hb1 | exact I] |].
  split; [apply T_Pair; [exact Ha2 | exact Hb2 | exact I] |].
  intros v1 v2 He1 He2. apply big_step_iff_evaluates in He1, He2.
  inversion He1; subst. inversion He2; subst.
  assert (value_relation observer A v v0) as Hva
    by (apply Ha; apply big_step_iff_evaluates; assumption).
  assert (value_relation observer B w w0) as Hvb
    by (apply Hb; apply big_step_iff_evaluates; assumption).
  destruct (value_relation_properties _ _ _ _ Hva) as [Hav1 [Hav2 [Hat1 Hat2]]].
  destruct (value_relation_properties _ _ _ _ Hvb) as [Hbv1 [Hbv2 [Hbt1 Hbt2]]].
  split; [apply v_pair; assumption |]. split; [apply v_pair; assumption |].
  split; [apply T_Pair; [exact Hat1 | exact Hbt1 | exact I] |].
  split; [apply T_Pair; [exact Hat2 | exact Hbt2 | exact I] |].
  intros _. exists v, w, v0, w0, k, k. auto.
Qed.

Lemma expression_relation_inl : forall observer A B k t1 t2,
  expression_relation observer A t1 t2 ->
  expression_relation observer (Ty_Sum A B k) (tm_inl t1 k) (tm_inl t2 k).
Proof.
  intros observer A B k t1 t2 [Ht1 [Ht2 Hr]].
  split; [apply T_Inl; [exact Ht1 | apply erase_type_wf | exact I] |].
  split; [apply T_Inl; [exact Ht2 | apply erase_type_wf | exact I] |].
  intros v1 v2 He1 He2. apply big_step_iff_evaluates in He1, He2.
  inversion He1; subst. inversion He2; subst.
  assert (value_relation observer A v v0) as Hv
    by (apply Hr; apply big_step_iff_evaluates; assumption).
  destruct (value_relation_properties _ _ _ _ Hv) as [Hval1 [Hval2 [Hv1 Hv2]]].
  split; [apply v_inl; exact Hval1 |]. split; [apply v_inl; exact Hval2 |].
  split; [apply T_Inl; [exact Hv1 | apply erase_type_wf | exact I] |].
  split; [apply T_Inl; [exact Hv2 | apply erase_type_wf | exact I] |].
  intros _. left. exists v, v0, k, k. auto.
Qed.

Lemma expression_relation_inr : forall observer A B k t1 t2,
  expression_relation observer B t1 t2 ->
  expression_relation observer (Ty_Sum A B k) (tm_inr t1 k) (tm_inr t2 k).
Proof.
  intros observer A B k t1 t2 [Ht1 [Ht2 Hr]].
  split; [apply T_Inr; [apply erase_type_wf | exact Ht1 | exact I] |].
  split; [apply T_Inr; [apply erase_type_wf | exact Ht2 | exact I] |].
  intros v1 v2 He1 He2. apply big_step_iff_evaluates in He1, He2.
  inversion He1; subst. inversion He2; subst.
  assert (value_relation observer B v v0) as Hv
    by (apply Hr; apply big_step_iff_evaluates; assumption).
  destruct (value_relation_properties _ _ _ _ Hv) as [Hval1 [Hval2 [Hv1 Hv2]]].
  split; [apply v_inr; exact Hval1 |]. split; [apply v_inr; exact Hval2 |].
  split; [apply T_Inr; [apply erase_type_wf | exact Hv1 | exact I] |].
  split; [apply T_Inr; [apply erase_type_wf | exact Hv2 | exact I] |].
  intros _. right. exists v, v0, k, k. auto.
Qed.

Lemma expression_relation_fst : forall observer A B k t1 t2 r,
  expression_relation observer (Ty_Prod A B k) t1 t2 ->
  expression_relation observer (ty_protect k.(indirect_reader) A)
    (tm_fst t1 r) (tm_fst t2 r).
Proof.
  intros observer A B k t1 t2 r [Ht1 [Ht2 Hr]].
  assert (underlying_typed (ty_protect k.(indirect_reader) A) (tm_fst t1 r)) as HT1.
  { unfold underlying_typed in *. simpl. rewrite erase_ty_protect.
    rewrite <- (ty_protect_low (erase_type A)).
    eapply T_Fst with (kappa := public); [exact Ht1 | exact I]. }
  assert (underlying_typed (ty_protect k.(indirect_reader) A) (tm_fst t2 r)) as HT2.
  { unfold underlying_typed in *. simpl. rewrite erase_ty_protect.
    rewrite <- (ty_protect_low (erase_type A)).
    eapply T_Fst with (kappa := public); [exact Ht2 | exact I]. }
  destruct (flows_to_dec k.(indirect_reader) observer) as [Hvis | Hhidden].
  - split; [exact HT1 |]. split; [exact HT2 |].
    intros w1 w2 He1 He2. apply big_step_iff_evaluates in He1, He2.
    inversion He1; subst. inversion He2; subst.
    assert (value_relation observer (Ty_Prod A B k)
      (tm_pair a b k0) (tm_pair a0 b0 k1)) as Hpair
      by (apply Hr; apply big_step_iff_evaluates; assumption).
    destruct Hpair as [_ [_ [_ [_ Hpair]]]]. specialize (Hpair Hvis).
    destruct Hpair as [p1 [q1 [p2 [q2 [ka [kb [E1 [E2 [Hp Hq]]]]]]]]].
    inversion E1; inversion E2; subst.
    apply value_relation_raise_type. apply value_relation_protect_values. exact Hp.
  - apply hidden_expressions_related; try assumption.
    intro Hvisible. apply Hhidden. eapply visible_ty_protect; exact Hvisible.
Qed.

Lemma expression_relation_snd : forall observer A B k t1 t2 r,
  expression_relation observer (Ty_Prod A B k) t1 t2 ->
  expression_relation observer (ty_protect k.(indirect_reader) B)
    (tm_snd t1 r) (tm_snd t2 r).
Proof.
  intros observer A B k t1 t2 r [Ht1 [Ht2 Hr]].
  assert (underlying_typed (ty_protect k.(indirect_reader) B) (tm_snd t1 r)) as HT1.
  { unfold underlying_typed in *. simpl. rewrite erase_ty_protect.
    rewrite <- (ty_protect_low (erase_type B)).
    eapply T_Snd with (kappa := public); [exact Ht1 | exact I]. }
  assert (underlying_typed (ty_protect k.(indirect_reader) B) (tm_snd t2 r)) as HT2.
  { unfold underlying_typed in *. simpl. rewrite erase_ty_protect.
    rewrite <- (ty_protect_low (erase_type B)).
    eapply T_Snd with (kappa := public); [exact Ht2 | exact I]. }
  destruct (flows_to_dec k.(indirect_reader) observer) as [Hvis | Hhidden].
  - split; [exact HT1 |]. split; [exact HT2 |].
    intros w1 w2 He1 He2. apply big_step_iff_evaluates in He1, He2.
    inversion He1; subst. inversion He2; subst.
    assert (value_relation observer (Ty_Prod A B k)
      (tm_pair a b k0) (tm_pair a0 b0 k1)) as Hpair
      by (apply Hr; apply big_step_iff_evaluates; assumption).
    destruct Hpair as [_ [_ [_ [_ Hpair]]]]. specialize (Hpair Hvis).
    destruct Hpair as [p1 [q1 [p2 [q2 [ka [kb [E1 [E2 [Hp Hq]]]]]]]]].
    inversion E1; inversion E2; subst.
    apply value_relation_raise_type. apply value_relation_protect_values. exact Hq.
  - apply hidden_expressions_related; try assumption.
    intro Hvisible. apply Hhidden. eapply visible_ty_protect; exact Hvisible.
Qed.

Lemma expression_relation_case : forall observer A B T k t1 t2 b11 b12 b21 b22 r,
  underlying_typed (ty_protect k.(indirect_reader) T) (tm_case t1 b11 b12 r) ->
  underlying_typed (ty_protect k.(indirect_reader) T) (tm_case t2 b21 b22 r) ->
  expression_relation observer (Ty_Sum A B k) t1 t2 ->
  (forall a1 a2, value_relation observer A a1 a2 ->
    expression_relation observer T (open b11 a1) (open b21 a2)) ->
  (forall a1 a2, value_relation observer B a1 a2 ->
    expression_relation observer T (open b12 a1) (open b22 a2)) ->
  expression_relation observer (ty_protect k.(indirect_reader) T)
    (tm_case t1 b11 b12 r) (tm_case t2 b21 b22 r).
Proof.
  intros observer A B T k t1 t2 b11 b12 b21 b22 r HT1 HT2 [_ [_ Hr]] Hl Hright.
  destruct (flows_to_dec k.(indirect_reader) observer) as [Hvis | Hhidden].
  - split; [exact HT1 |]. split; [exact HT2 |].
    intros w1 w2 He1 He2. apply big_step_iff_evaluates in He1, He2.
    inversion He1; subst; inversion He2; subst.
    all: match goal with
    | Hrel : expression_lifting _ ?scr1 ?scr2,
      E1 : big_step ?scr1 ?v1, E2 : big_step ?scr2 ?v2 |- _ =>
      pose proof (Hrel v1 v2 (big_step_sound _ _ E1) (big_step_sound _ _ E2)) as Hsum
    end.
    all: destruct Hsum as [_ [_ [_ [_ Hsum]]]]; specialize (Hsum Hvis).
    all: destruct Hsum as [Hsum | Hsum];
      destruct Hsum as [p1 [p2 [ka [kb [E1 [E2 Hp]]]]]];
      inversion E1; inversion E2; subst.
    all: apply value_relation_raise_type; apply value_relation_protect_values.
    + destruct (Hl _ _ Hp) as [_ [_ Hbranch]].
      apply Hbranch; apply big_step_iff_evaluates; assumption.
    + destruct (Hright _ _ Hp) as [_ [_ Hbranch]].
      apply Hbranch; apply big_step_iff_evaluates; assumption.
  - apply hidden_expressions_related; try assumption.
    intro Hvisible. apply Hhidden. eapply visible_ty_protect; exact Hvisible.
Qed.

Lemma expression_lifting_step_left : forall R t1 t1' t2,
  t1 --> t1' -> (expression_lifting R t1 t2 <-> expression_lifting R t1' t2).
Proof.
  intros R t1 t1' t2 Hstep. split; intros H v1 v2 H1 H2; apply H; try exact H2.
  - apply (proj2 (evaluates_step_iff _ _ _ Hstep)); exact H1.
  - apply (proj1 (evaluates_step_iff _ _ _ Hstep)); exact H1.
Qed.

Lemma expression_lifting_step_right : forall R t1 t2 t2',
  t2 --> t2' -> (expression_lifting R t1 t2 <-> expression_lifting R t1 t2').
Proof.
  intros R t1 t2 t2' Hstep. split; intros H v1 v2 H1 H2; apply H; try exact H1.
  - apply (proj2 (evaluates_step_iff _ _ _ Hstep)); exact H2.
  - apply (proj1 (evaluates_step_iff _ _ _ Hstep)); exact H2.
Qed.

Lemma value_relation_subtype : forall T U,
  subtype T U -> forall observer v1 v2,
  value_relation observer T v1 v2 -> value_relation observer U v1 v2.
Proof.
  intros T U Hsub. induction Hsub; intros observer v1 v2 Hrelated.
  - destruct Hrelated as [Hv1 [Hv2 [Ht1 [Ht2 Hrel]]]].
    repeat split; try assumption. intros Hvis.
    apply Hrel. eapply flows_to_trans; [exact (proj2 H1) | exact Hvis].
  - destruct Hrelated as [Hv1 [Hv2 [Ht1 [Ht2 Hrel]]]].
    assert (erase_type (Ty_Sum T1 T2 kappa1) = erase_type (Ty_Sum U1 U2 kappa2)) as Herase.
    { simpl. rewrite (subtype_erasure _ _ Hsub1), (subtype_erasure _ _ Hsub2). reflexivity. }
    split; [exact Hv1 | ]. split; [exact Hv2 | ].
    split; [unfold underlying_typed in *; rewrite <- Herase; exact Ht1 | ].
    split; [unfold underlying_typed in *; rewrite <- Herase; exact Ht2 | ].
    intros Hvis. specialize (Hrel (flows_to_trans _ _ _ (proj2 H1) Hvis)).
    destruct Hrel as [Hleft | Hright].
    + left. destruct Hleft as [a1 [a2 [k1 [k2 [Heq1 [Heq2 Ha]]]]]].
      exists a1, a2, k1, k2. repeat split; try assumption. apply IHHsub1; exact Ha.
    + right. destruct Hright as [a1 [a2 [k1 [k2 [Heq1 [Heq2 Ha]]]]]].
      exists a1, a2, k1, k2. repeat split; try assumption. apply IHHsub2; exact Ha.
  - destruct Hrelated as [Hv1 [Hv2 [Ht1 [Ht2 Hrel]]]].
    assert (erase_type (Ty_Prod T1 T2 kappa1) = erase_type (Ty_Prod U1 U2 kappa2)) as Herase.
    { simpl. rewrite (subtype_erasure _ _ Hsub1), (subtype_erasure _ _ Hsub2). reflexivity. }
    split; [exact Hv1 | ]. split; [exact Hv2 | ].
    split; [unfold underlying_typed in *; rewrite <- Herase; exact Ht1 | ].
    split; [unfold underlying_typed in *; rewrite <- Herase; exact Ht2 | ].
    intros Hvis. specialize (Hrel (flows_to_trans _ _ _ (proj2 H1) Hvis)).
    destruct Hrel as [a1 [b1 [a2 [b2 [k1 [k2 [Heq1 [Heq2 [Ha Hb]]]]]]]]].
    exists a1, b1, a2, b2, k1, k2. repeat split; try assumption.
    + apply IHHsub1; exact Ha.
    + apply IHHsub2; exact Hb.
  - destruct Hrelated as [Hv1 [Hv2 [Ht1 [Ht2 Hrel]]]].
    assert (erase_type (Ty_Arrow T1 T2 kappa1) = erase_type (Ty_Arrow U1 U2 kappa2)) as Herase.
    { simpl. rewrite (subtype_erasure _ _ Hsub1), (subtype_erasure _ _ Hsub2). reflexivity. }
    split; [exact Hv1 | ]. split; [exact Hv2 | ].
    split; [unfold underlying_typed in *; rewrite <- Herase; exact Ht1 | ].
    split; [unfold underlying_typed in *; rewrite <- Herase; exact Ht2 | ].
    intros Hvis. specialize (Hrel (flows_to_trans _ _ _ (proj2 H1) Hvis)).
    destruct Hrel as [A1 [A2 [body1 [body2 [k1 [k2 [Heq1 [Heq2 Hfunctions]]]]]]]].
    exists A1, A2, body1, body2, k1, k2. split; [exact Heq1 | ]. split; [exact Heq2 | ].
    intros arg1 arg2 Hargs result1 result2 Heval1 Heval2.
    apply IHHsub2. apply (Hfunctions arg1 arg2).
    + apply IHHsub1; exact Hargs.
    + exact Heval1.
    + exact Heval2.
  - apply IHHsub2. apply IHHsub1. exact Hrelated.
Qed.

Lemma expression_relation_subtype : forall T U,
  subtype T U -> forall observer t1 t2,
  expression_relation observer T t1 t2 -> expression_relation observer U t1 t2.
Proof.
  intros T U Hsub observer t1 t2 [Ht1 [Ht2 Hrelated]].
  split.
  - unfold underlying_typed in *. rewrite <- (subtype_erasure _ _ Hsub). exact Ht1.
  - split.
    + unfold underlying_typed in *. rewrite <- (subtype_erasure _ _ Hsub). exact Ht2.
    + intros v1 v2 H1 H2. eapply value_relation_subtype.
      * exact Hsub.
      * apply Hrelated; assumption.
Qed.

Lemma expression_relation_if : forall observer k T c1 c2 y1 y2 n1 n2 r,
  expression_relation observer (Ty_Sum (Ty_Unit public) (Ty_Unit public) k) c1 c2 ->
  expression_relation observer T y1 y2 -> expression_relation observer T n1 n2 ->
  expression_relation observer (ty_protect k.(indirect_reader) T)
    (tm_if c1 y1 n1 r) (tm_if c2 y2 n2 r).
Proof.
  intros observer k T c1 c2 y1 y2 n1 n2 r [Hc1 [Hc2 Hc]] [Hy1 [Hy2 Hy]] [Hn1 [Hn2 Hn]].
  assert (forall c y n,
    underlying_typed (Ty_Sum (Ty_Unit public) (Ty_Unit public) k) c ->
    underlying_typed T y -> underlying_typed T n ->
    underlying_typed (ty_protect k.(indirect_reader) T) (tm_if c y n r)) as HT.
  { intros c y n Hct Hyt Hnt. unfold underlying_typed in *. simpl in *.
    rewrite erase_ty_protect. rewrite <- (ty_protect_low (erase_type T)).
    eapply T_If with (k := public); eauto. exact I. }
  destruct (flows_to_dec k.(indirect_reader) observer) as [Hvis | Hhidden].
  - split; [apply HT; assumption |]. split; [apply HT; assumption |].
    intros w1 w2 He1 He2. apply big_step_iff_evaluates in He1, He2.
    inversion He1; subst; inversion He2; subst.
    all: match goal with
      Hr : expression_lifting (value_relation _ (Ty_Sum _ _ _)) ?c1 ?c2,
      E1 : big_step ?c1 ?v1, E2 : big_step ?c2 ?v2 |- _ =>
      pose proof (Hr v1 v2 (big_step_sound _ _ E1) (big_step_sound _ _ E2)) as Hsum
    end.
    all: destruct Hsum as [_ [_ [_ [_ Hsum]]]]; specialize (Hsum Hvis).
    all: destruct Hsum as [Hsum | Hsum];
      destruct Hsum as [a1 [a2 [ka [kb [E1 [E2 Hargs]]]]]];
      inversion E1; inversion E2; subst.
    all: apply value_relation_raise_type; apply value_relation_protect_values.
    + apply Hy; apply big_step_iff_evaluates; assumption.
    + apply Hn; apply big_step_iff_evaluates; assumption.
  - apply hidden_expressions_related; try (apply HT; assumption).
    intro H. apply Hhidden. eapply visible_ty_protect; exact H.
Qed.

Definition related_substitutions
    (observer : label) (Gamma : context) (rho1 rho2 : term_substitution) : Prop :=
  forall (x : atom) (T : ty),
    lookup_context x Gamma = Some T ->
    value_relation observer T (rho1 x) (rho2 x).

Definition related_expression_substitutions
    (observer : label) (Gamma : context) (rho1 rho2 : term_substitution) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    expression_relation observer T (rho1 x) (rho2 x).

Lemma related_expression_update : forall observer Gamma rho1 rho2 x T v1 v2,
  related_expression_substitutions observer Gamma rho1 rho2 ->
  value_relation observer T v1 v2 ->
  related_expression_substitutions observer (update Gamma x T)
    (substitution_update rho1 x v1) (substitution_update rho2 x v2).
Proof.
  intros observer Gamma rho1 rho2 x T v1 v2 Henv Hv y U HU.
  unfold substitution_update. destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E. subst y. rewrite lookup_update_eq in HU.
    inversion HU; subst U. apply related_values_are_related_expressions; exact Hv.
  - apply Nat.eqb_neq in E. rewrite lookup_update_neq in HU by congruence.
    apply Henv; exact HU.
Qed.

Lemma related_instantiations_typed : forall Gamma t T observer rho1 rho2,
  has_type Gamma t T -> related_expression_substitutions observer Gamma rho1 rho2 ->
  underlying_typed T (instantiate rho1 t) /\ underlying_typed T (instantiate rho2 t).
Proof.
  intros Gamma t T observer rho1 rho2 Ht Henv.
  split; apply typing_instantiate_erased with (Gamma := Gamma); try exact Ht;
    intros x U HU; specialize (Henv x U HU); destruct Henv as [H1 [H2 _]]; assumption.
Qed.

Lemma related_substitution_lc : forall Gamma t T observer rho1 rho2,
  has_type Gamma t T -> related_expression_substitutions observer Gamma rho1 rho2 ->
  forall x, In x (fv t) -> locally_closed (rho1 x) /\ locally_closed (rho2 x).
Proof.
  intros Gamma t T observer rho1 rho2 Ht Henv x Hx.
  destruct (typing_free_variable _ _ _ Ht x Hx) as [U HU].
  destruct (Henv x U HU) as [H1 [H2 _]].
  split; apply erase_lc_inv; [exact (proj1 (typing_regular _ _ _ H1)) |
    exact (proj1 (typing_regular _ _ _ H2))].
Qed.

Theorem fundamental_expressions : forall Gamma t T,
  has_type Gamma t T ->
  forall observer rho1 rho2,
    related_expression_substitutions observer Gamma rho1 rho2 ->
    expression_relation observer T (instantiate rho1 t) (instantiate rho2 t).
Proof.
  intros Gamma t T Ht. pose proof Ht as Htyping.
  induction Ht; intros observer rho1 rho2 Henv.
  all: pose proof (related_instantiations_typed _ _ _ _ _ _ Htyping Henv) as [HT1 HT2].
  all: pose proof (related_substitution_lc _ _ _ _ _ _ Htyping Henv) as Hlc.
  - apply Henv; exact H.
  - apply expression_relation_unit.
  - apply expression_relation_abs; try exact HT1; try exact HT2.
    + apply erase_lc_inv. exact (proj1 (typing_regular _ _ _ HT1)).
    + apply erase_lc_inv. exact (proj1 (typing_regular _ _ _ HT2)).
    + intros a1 a2 Ha. destruct (fresh_atom (L ++ fv body)) as [x Hx].
      rewrite in_app_iff in Hx.
      rewrite <- !instantiate_open_update with (x := x) by
        (first [tauto | intros y Hy; specialize (Hlc y Hy); tauto]).
      apply H2; [tauto | apply H1; tauto |].
      apply related_expression_update; assumption.
  - eapply expression_relation_app; [apply IHHt1 | apply IHHt2]; assumption.
  - apply expression_relation_pair; [apply IHHt1 | apply IHHt2]; assumption.
  - eapply expression_relation_fst. apply IHHt; assumption.
  - eapply expression_relation_snd. apply IHHt; assumption.
  - apply expression_relation_inl. apply IHHt; assumption.
  - apply expression_relation_inr. apply IHHt; assumption.
  - eapply expression_relation_case; [exact HT1 | exact HT2 | apply IHHt; assumption | |].
    + intros a1 a2 Ha. destruct (fresh_atom (L ++ fv body1)) as [x Hx].
      rewrite in_app_iff in Hx.
      rewrite <- !instantiate_open_update with (x := x) by
        (first [tauto | intros y Hy; assert (In y (fv (tm_case t body1 body2 r))) as Hmem
          by (simpl; repeat rewrite in_app_iff; tauto); specialize (Hlc y Hmem); tauto]).
      apply H1; [tauto | apply H0; tauto |]. apply related_expression_update; assumption.
    + intros a1 a2 Ha. destruct (fresh_atom (L ++ fv body2)) as [x Hx].
      rewrite in_app_iff in Hx.
      rewrite <- !instantiate_open_update with (x := x) by
        (first [tauto | intros y Hy; assert (In y (fv (tm_case t body1 body2 r))) as Hmem
          by (simpl; repeat rewrite in_app_iff; tauto); specialize (Hlc y Hmem); tauto]).
      apply H3; [tauto | apply H2; tauto |]. apply related_expression_update; assumption.
  - apply expression_relation_protect. apply IHHt; assumption.
  - eapply expression_relation_subtype; [exact H | apply IHHt; assumption].
  - eapply expression_relation_if; [apply IHHt1 | apply IHHt2 | apply IHHt3]; assumption.
Qed.

Theorem fundamental : forall Gamma t T,
  context_wf Gamma ->
  has_type Gamma t T ->
  forall (observer : label) (rho1 rho2 : term_substitution),
    related_substitutions observer Gamma rho1 rho2 ->
    expression_relation observer T (instantiate rho1 t) (instantiate rho2 t).
Proof.
  intros Gamma t T _ Ht observer rho1 rho2 Henv.
  apply fundamental_expressions with (Gamma := Gamma); [exact Ht |].
  intros x U HU. apply related_values_are_related_expressions. apply Henv; exact HU.
Qed.
