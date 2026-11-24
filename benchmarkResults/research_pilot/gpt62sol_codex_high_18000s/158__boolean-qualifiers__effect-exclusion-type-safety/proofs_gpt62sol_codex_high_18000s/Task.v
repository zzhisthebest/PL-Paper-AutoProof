Require Import Fsub.EffectExclusion.Tactics.

Require Import Coq.Program.Equality.

Require Export Fsub.EffectExclusion.Fsub_LetSum_Lemmas.
From Stdlib Require Import Lia.

Definition transitivity_on_sub Q := forall E S T,
  sub E S Q -> sub E Q T -> sub E S T.

Definition transitivity_on_subqtype Q := forall E S T,
  subqtype E S Q -> subqtype E Q T -> subqtype E S T.

Definition transitivity_on_subqual Q := forall E S T,
  subqual E S Q -> subqual E Q T -> subqual E S T.

(* Structural facts shared by the expression and continuation arguments. *)
Local Hint Constructors qual wf_qua wf_typ wf_qtyp wf_env subqual sub subqtype
  type qtype expr typing value typing_ctx typing_state step done_state : core_safety.
Scheme wf_typ_ind' := Induction for wf_typ Sort Prop
with wf_qtyp_ind' := Induction for wf_qtyp Sort Prop.
Combined Scheme wf_types_ind from wf_typ_ind', wf_qtyp_ind'.
Scheme sub_ind' := Induction for sub Sort Prop
with subqtype_ind' := Induction for subqtype Sort Prop.
Combined Scheme sub_types_ind from sub_ind', subqtype_ind'.
Scheme type_ind' := Induction for type Sort Prop
with qtype_ind' := Induction for qtype Sort Prop.
Combined Scheme types_ind from type_ind', qtype_ind'.

Local Ltac fresh_atom x L := destruct (atom_fresh L) as [x ?].
Local Ltac invert H := inversion H; subst; clear H.

Lemma safety_wf_uniq : forall E, wf_env E -> uniq E.
Proof. induction 1; eauto using uniq_nil, uniq_push. Qed.

Local Hint Resolve safety_wf_uniq : core_safety.

Definition safety_kind (b : binding) : nat :=
  match b with bind_sub _ => 0 | bind_typ _ => 1 | bind_qua _ => 2 end.

Definition safety_scopes (E F : env) :=
  forall x b, binds x b E -> safety_kind b <> 1 ->
    exists c, binds x c F /\ safety_kind c = safety_kind b.

Lemma safety_scopes_cons : forall E F x b c,
  safety_scopes E F -> safety_kind b = safety_kind c ->
  safety_scopes ((x,b)::E) ((x,c)::F).
Proof.
  unfold safety_scopes, binds; simpl; intros E F x b c H K y a [J|J] Ha.
  - inversion J; subst. exists c; auto.
  - destruct (H _ _ J Ha) as [d [Hd Hk]]. exists d; auto.
Qed.

Lemma safety_scopes_weaken : forall E F,
  (forall x b, binds x b E -> binds x b F) -> safety_scopes E F.
Proof. unfold safety_scopes; eauto. Qed.

Lemma safety_wf_qua_scope : forall E Q, wf_qua E Q ->
  forall F, safety_scopes E F -> wf_qua F Q.
Proof.
  induction 1; intros F Hs; eauto with core_safety.
  destruct (Hs _ _ H ltac:(discriminate)) as [[T|T|R'] [Hb Hk]]; discriminate Hk || eauto with core_safety.
Qed.

Lemma safety_wf_type_scope :
  (forall E T, wf_typ E T -> forall F, safety_scopes E F -> wf_typ F T) /\
  (forall E T, wf_qtyp E T -> forall F, safety_scopes E F -> wf_qtyp F T).
Proof.
  apply wf_types_ind; intros; eauto using safety_wf_qua_scope, safety_scopes_cons with core_safety.
  match goal with
  | Hb : binds _ _ _, Hs : safety_scopes _ _ |- _ =>
      destruct (Hs _ _ Hb ltac:(discriminate)) as [[T|T|R] [Hb' Hk]];
      discriminate Hk || eauto with core_safety
  end.
  all: (eapply wf_typ_all with (L := L) || eapply wf_typ_qall with (L := L));
    intros; eauto using safety_wf_qua_scope, safety_scopes_cons with core_safety.
  all: (eapply H0 || eapply H); [eassumption | apply safety_scopes_cons; auto].
Qed.

Definition safety_wf_typ_scope := proj1 safety_wf_type_scope.
Definition safety_wf_qtyp_scope := proj2 safety_wf_type_scope.
Local Hint Resolve safety_wf_typ_scope safety_wf_qtyp_scope safety_wf_qua_scope
  safety_scopes_cons safety_scopes_weaken : core_safety.

Lemma safety_wf_cons : forall E x b, wf_env ((x,b)::E) ->
  wf_env E /\ x `notin` dom E /\
  match b with
  | bind_sub T => wf_typ E T
  | bind_typ T => wf_qtyp E T
  | bind_qua Q => wf_qua E Q
  end.
Proof. intros; inversion H; subst; auto. Qed.

Lemma safety_wf_binding : forall E, wf_env E -> forall x b, binds x b E ->
  match b with
  | bind_sub T => wf_typ E T
  | bind_typ T => wf_qtyp E T
  | bind_qua Q => wf_qua E Q
  end.
Proof.
  induction 1; intros y b Hb; [inversion Hb| | |].
  all: unfold binds in Hb; simpl in Hb; destruct Hb as [Hb|Hb].
  all: first [inversion Hb; subst; clear Hb |
    specialize (IHwf_env _ _ Hb); destruct b].
  all: (eapply safety_wf_typ_scope || eapply safety_wf_qtyp_scope ||
    eapply safety_wf_qua_scope); [eassumption|].
  all: apply safety_scopes_weaken; intros; right; assumption.
Qed.

Lemma safety_wf_qua_lc : forall E Q, wf_qua E Q -> qual Q.
Proof. induction 1; eauto with core_safety. Qed.

Lemma safety_wf_type_lc :
  (forall E T, wf_typ E T -> type T) /\
  (forall E T, wf_qtyp E T -> qtype T).
Proof. apply wf_types_ind; intros; eauto using safety_wf_qua_lc with core_safety. Qed.
Definition safety_wf_typ_lc := proj1 safety_wf_type_lc.
Definition safety_wf_qtyp_lc := proj2 safety_wf_type_lc.

Lemma safety_sq_regular : forall E Q R, subqual E Q R ->
  wf_env E /\ wf_qua E Q /\ wf_qua E R.
Proof.
  induction 1; repeat match goal with H : _ /\ _ |- _ => destruct H end;
    eauto 8 with core_safety.
Qed.

Local Ltac split_facts :=
  repeat match goal with H : _ /\ _ |- _ => destruct H end.

Lemma safety_sq_env : forall E Q R, subqual E Q R -> wf_env E.
Proof. intros; eapply safety_sq_regular in H; tauto. Qed.
Lemma safety_sq_left : forall E Q R, subqual E Q R -> wf_qua E Q.
Proof. intros; eapply safety_sq_regular in H; tauto. Qed.
Lemma safety_sq_right : forall E Q R, subqual E Q R -> wf_qua E R.
Proof. intros; eapply safety_sq_regular in H; tauto. Qed.
Local Hint Resolve safety_sq_env safety_sq_left safety_sq_right : core_safety.

Lemma safety_sub_regular :
  (forall E S T, sub E S T -> wf_env E /\ wf_typ E S /\ wf_typ E T) /\
  (forall E S T, subqtype E S T -> wf_env E /\ wf_qtyp E S /\ wf_qtyp E T).
Proof.
  apply sub_types_ind; intros; split_facts; try solve [repeat split; eauto 4 with core_safety].
  - split; [assumption|]. split.
    + eapply wf_typ_all with (L := L); [assumption|].
      intros X Hx. destruct (H0 X Hx) as [_ [Hs _]].
      eapply safety_wf_qtyp_scope; [exact Hs|].
      apply safety_scopes_cons; [apply safety_scopes_weaken; auto|reflexivity].
    + eapply wf_typ_all with (L := L); [assumption|].
      intros X Hx. destruct (H0 X Hx) as [_ [_ Ht]]. exact Ht.
  - split; [eauto with core_safety|]. split.
    + eapply wf_typ_qall with (L := L); [eauto with core_safety|].
      intros X Hx. destruct (H X Hx) as [_ [Hs _]].
      eapply safety_wf_qtyp_scope; [exact Hs|].
      apply safety_scopes_cons; [apply safety_scopes_weaken; auto|reflexivity].
    + eapply wf_typ_qall with (L := L); [eauto with core_safety|].
      intros X Hx. destruct (H X Hx) as [_ [_ Ht]]. exact Ht.
Qed.

Lemma safety_sub_left : forall E S T, sub E S T -> wf_typ E S.
Proof. intros; apply (proj1 safety_sub_regular) in H; tauto. Qed.
Lemma safety_sub_right : forall E S T, sub E S T -> wf_typ E T.
Proof. intros; apply (proj1 safety_sub_regular) in H; tauto. Qed.
Lemma safety_sub_env : forall E S T, sub E S T -> wf_env E.
Proof. intros; apply (proj1 safety_sub_regular) in H; tauto. Qed.
Lemma safety_sqt_left : forall E S T, subqtype E S T -> wf_qtyp E S.
Proof. intros; apply (proj2 safety_sub_regular) in H; tauto. Qed.
Lemma safety_sqt_right : forall E S T, subqtype E S T -> wf_qtyp E T.
Proof. intros; apply (proj2 safety_sub_regular) in H; tauto. Qed.
Lemma safety_sqt_env : forall E S T, subqtype E S T -> wf_env E.
Proof. intros; apply (proj2 safety_sub_regular) in H; tauto. Qed.

Local Hint Resolve safety_sub_left safety_sub_right safety_sub_env
  safety_sqt_left safety_sqt_right safety_sqt_env : core_safety.

Lemma safety_sq_refl : forall E Q, wf_qua E Q -> wf_env E -> subqual E Q Q.
Proof.
  induction 1; intro HE.
  - apply subqual_lift_elem; [assumption|apply reflexive].
  - apply subqual_refl_qvar; auto. econstructor; eassumption.
  - apply subqual_meet_intro.
    + apply subqual_meet_eliml; auto.
    + apply subqual_meet_elimr; auto.
  - apply subqual_join_elim.
    + apply subqual_join_inl; auto.
    + apply subqual_join_inr; auto.
  - apply subqual_refl_negate; auto.
Qed.

Lemma safety_sub_refl :
  (forall E T, wf_typ E T -> wf_env E -> sub E T T) /\
  (forall E T, wf_qtyp E T -> wf_env E -> subqtype E T T).
Proof.
  apply wf_types_ind; intros; eauto 4 using safety_sq_refl with core_safety.
  - eapply sub_all with (L := L `union` dom E); [auto|].
    intros; eapply H0 || eapply H; [solve_notin | constructor; auto; solve_notin].
  - eapply sub_qall with (L := L `union` dom E); [eauto using safety_sq_refl|].
    intros; eapply H0 || eapply H; [solve_notin | constructor; auto; solve_notin].
Qed.
Definition safety_sub_refl_typ := proj1 safety_sub_refl.
Definition safety_sub_refl_qtyp := proj2 safety_sub_refl.
Local Hint Resolve safety_sq_refl safety_sub_refl_typ safety_sub_refl_qtyp
  safety_wf_qua_lc safety_wf_typ_lc safety_wf_qtyp_lc : core_safety.

Lemma safety_qua_unbind : forall E x b Q, wf_qua ((x,b)::E) Q ->
  (forall R, b <> bind_qua R) -> wf_qua E Q.
Proof.
  intros E x b Q H. remember ((x,b)::E) as F eqn:HF.
  induction H; intros Hkind; subst; eauto 4 with core_safety.
  destruct H as [Hb|Hb].
  - inversion Hb; subst. exfalso; eapply Hkind; reflexivity.
  - eapply wf_qua_fvar; eassumption.
Qed.

Lemma safety_typing_env : forall E Q e T, typing E Q e T -> wf_env E.
Proof.
  induction 1; try assumption;
    match goal with
    | H : forall x : atom, x `notin` ?A -> wf_env _ |- _ =>
        let x := fresh "x" in
        fresh_atom x A; specialize (H x ltac:(assumption));
        destruct (safety_wf_cons _ _ _ H); assumption
    end.
Qed.

Local Hint Resolve safety_typing_env : core_safety.

Lemma safety_typing_effect : forall E Q e T, typing E Q e T -> wf_qua E Q.
Proof.
  induction 1; eauto 2 with core_safety.
Qed.

Local Hint Resolve safety_typing_effect : core_safety.

Local Ltac body_environment :=
  match goal with
  | H : forall x : atom, x `notin` ?A -> typing _ _ _ _ |- _ =>
      let x := fresh "x" in let Hbody := fresh "Body" in
      fresh_atom x A;
      pose proof (H x ltac:(assumption)) as Hbody;
      let W := fresh "Env" in pose proof (safety_typing_env _ _ _ _ Hbody) as W;
      destruct (safety_wf_cons _ _ _ W) as [? [? ?]]
  end.

Lemma safety_typing_expr : forall E Q e T, typing E Q e T -> expr e.
Proof.
  induction 1; try solve [eauto 3 with core_safety].
  - body_environment.
    assert (wf_qua E P) by
      (eapply safety_qua_unbind; [eapply safety_typing_effect; exact Body|intros; discriminate]).
    eapply expr_abs with (L := L); eauto 3 with core_safety.
  - body_environment.
    assert (wf_qua E P) by
      (eapply safety_qua_unbind; [eapply safety_typing_effect; exact Body|intros; discriminate]).
    eapply expr_tabs with (L := L); eauto 3 with core_safety.
  - apply expr_tapp; [assumption|]. eapply safety_wf_typ_lc, safety_sub_left; eassumption.
  - body_environment.
    eapply expr_qabs with (L := L); eauto 3 with core_safety.
  - apply expr_qapp; [assumption|]. eapply safety_wf_qua_lc, safety_sq_left; eassumption.
  - apply expr_upqual; [|assumption]. eapply safety_wf_qua_lc, safety_sq_right; eassumption.
  - apply expr_check; [|assumption]. eapply safety_wf_qua_lc, safety_sq_right; eassumption.
  - apply expr_without; [|assumption].
    apply safety_sq_right in H0. inversion H0; eauto 3 with core_safety.
Qed.

Lemma safety_concretize_closed : forall E Q, wf_qua E Q -> E = empty ->
  exists b, concretize Q = Some b.
Proof.
  induction 1; intro He; subst; simpl; try discriminate.
  - eauto.
  - inversion H.
  - destruct (IHwf_qua1 eq_refl) as [a Ha], (IHwf_qua2 eq_refl) as [b Hb]; rewrite Ha, Hb; eauto.
  - destruct (IHwf_qua1 eq_refl) as [a Ha], (IHwf_qua2 eq_refl) as [b Hb]; rewrite Ha, Hb; eauto.
  - destruct (IHwf_qua eq_refl) as [a Ha]; rewrite Ha; eauto.
Qed.

Definition safety_concrete (Q : qua) (b : B) :=
  concretize Q = Some b.

Lemma safety_closed_concrete : forall Q, wf_qua empty Q ->
  exists b, safety_concrete Q b.
Proof. intros; eapply safety_concretize_closed; eauto. Qed.

Lemma safety_ord_top : forall b : B, b ≤ top.
Proof. intro; apply meet_consistent; symmetry; apply meet_top. Qed.
Lemma safety_ord_bot : forall b : B, bot ≤ b.
Proof. intro; apply join_consistent; symmetry; rewrite join_commutative; apply join_bot. Qed.

(* Assigning bottom to free variables satisfies every qualifier upper bound. *)
Fixpoint safety_eval (Q : qua) : B :=
  match Q with
  | qua_base b => b
  | qua_fvar _ | qua_bvar _ => bot
  | qua_meet P R => safety_eval P ⊓ safety_eval R
  | qua_join P R => safety_eval P ⊔ safety_eval R
  | qua_negate P => negate (safety_eval P)
  end.

Lemma safety_eval_concrete : forall Q b, safety_concrete Q b -> safety_eval Q = b.
Proof.
  unfold safety_concrete.
  induction Q; intros b' Hb; simpl in *; try discriminate.
  - congruence.
  - destruct (concretize Q1), (concretize Q2); try discriminate.
    inversion Hb; subst. rewrite (IHQ1 _ eq_refl), (IHQ2 _ eq_refl); reflexivity.
  - destruct (concretize Q1), (concretize Q2); try discriminate.
    inversion Hb; subst. rewrite (IHQ1 _ eq_refl), (IHQ2 _ eq_refl); reflexivity.
  - destruct (concretize Q); try discriminate.
    inversion Hb; subst. rewrite (IHQ _ eq_refl); reflexivity.
Qed.

Lemma safety_sq_eval : forall E Q R, subqual E Q R ->
  safety_eval Q ≤ safety_eval R.
Proof.
  induction 1; simpl in *;
    try solve [auto using safety_ord_top, safety_ord_bot, reflexive].
  - let He := fresh in pose proof (safety_eval_concrete _ _ H0) as He;
    rewrite He in IHsubqual1 || rewrite He in IHsubqual2; eapply transitive; eassumption.
  - let He := fresh in pose proof (safety_eval_concrete _ _ H0) as He;
    rewrite He in IHsubqual1 || rewrite He in IHsubqual2; eapply transitive; eassumption.
  - apply join_prime; auto.
  - apply join_prime; auto.
  - apply (proj1 (join_is_lub (safety_eval R1) (safety_eval R2) (safety_eval Q))); auto.
  - apply meet_prime; auto.
  - apply meet_prime; auto.
  - apply (proj1 (meet_is_glb (safety_eval R1) (safety_eval R2) (safety_eval Q))); auto.
  - rewrite distrib. apply reflexive.
  - eapply transitive; eassumption.
  - rewrite negate_bot. apply reflexive.
  - rewrite negate_top. apply reflexive.
  - apply reflexive.
Qed.

Lemma safety_sq_concrete : forall E Q R q r, subqual E Q R ->
  safety_concrete Q q -> safety_concrete R r -> q ≤ r.
Proof.
  intros E Q R q r H Hq Hr.
  apply safety_sq_eval in H.
  now rewrite (safety_eval_concrete _ _ Hq), (safety_eval_concrete _ _ Hr) in H.
Qed.

Lemma safety_ctx_compatible : forall E Q c T U, typing_ctx E Q c T U ->
  forall b, b ≤ safety_eval Q -> barrier_compatible c b.
Proof.
  induction 1; intros b Hb; simpl in *;
    try solve [constructor];
    try solve [apply barrier_compatible_other; [auto|discriminate|discriminate]];
    try solve [eauto].
  - apply barrier_compatible_frame; [apply IHtyping_ctx|assumption].
    pose proof (safety_eval_concrete _ _ H0) as Hc. rewrite Hc.
    eapply transitive; eassumption.
  - apply IHtyping_ctx. eapply transitive; [exact Hb|eapply safety_sq_eval; eassumption].
  - destruct (proj2 (meet_is_glb (negate t) (safety_eval Q) b) Hb) as [Hleft Hright].
    apply barrier_compatible_without; auto.
Qed.

Definition safety_tag (v : exp) : qua :=
  match v with
  | exp_int P _ | exp_abs P _ _ | exp_tabs P _ _ | exp_qabs P _ _
  | exp_inl P _ | exp_inr P _ | exp_pair P _ _ => P
  | _ => qua_base bot
  end.

Lemma safety_value_tag : forall E Q v T, typing E Q v T -> value v ->
  forall P A, T = qtyp_qtyp P A -> subqual E (safety_tag v) P.
Proof.
  induction 1; intros Hv Tag Shape He; inversion He; subst;
    try solve [inversion Hv];
    simpl;
    try solve [eapply safety_sq_refl; eauto 2 with core_safety].
  - body_environment. apply safety_sq_refl; [|assumption].
    eapply safety_qua_unbind; [eapply safety_typing_effect; exact Body|intros; discriminate].
  - body_environment. apply safety_sq_refl; [|assumption].
    eapply safety_qua_unbind; [eapply safety_typing_effect; exact Body|intros; discriminate].
  - body_environment. apply safety_sq_refl; assumption.
  - destruct S as [P B']. inversion H0; subst.
    eapply subqual_trans; [eapply IHtyping; eauto|eassumption].
  - eauto.
Qed.

Definition safety_shape (v : exp) (T : typ) : Prop :=
  match T with
  | typ_top => True
  | typ_int => exists P n, v = exp_int P n
  | typ_arrow _ _ => exists P V e, v = exp_abs P V e
  | typ_all _ _ => exists P V e, v = exp_tabs P V e
  | typ_qall _ _ => exists P R e, v = exp_qabs P R e
  | typ_sum _ _ => exists P e, v = exp_inl P e \/ v = exp_inr P e
  | typ_pair _ _ => exists P e1 e2, v = exp_pair P e1 e2
  | _ => False
  end.

Lemma safety_sub_shape : forall E S T, sub E S T ->
  forall v, safety_shape v S -> safety_shape v T.
Proof. destruct 1; simpl; tauto. Qed.

Definition safety_intro (v : exp) : Prop :=
  match v with
  | exp_int _ _ | exp_abs _ _ _ | exp_tabs _ _ _ | exp_qabs _ _ _
  | exp_inl _ _ | exp_inr _ _ | exp_pair _ _ _ => True
  | _ => False
  end.

Lemma safety_intro_shape : forall E Q v T, typing E Q v T -> safety_intro v ->
  forall P A, T = qtyp_qtyp P A -> safety_shape v A.
Proof.
  induction 1; intros Hv Tag Shape He; inversion He; subst;
    simpl in *; try contradiction; try solve [eauto 6].
  destruct S as [P B']. inversion H0; subst.
  eapply safety_sub_shape; [eassumption|eapply IHtyping; eauto].
Qed.

Lemma safety_value_shape : forall E Q v T, typing E Q v T -> value v ->
  forall P A, T = qtyp_qtyp P A -> safety_shape v A.
Proof.
  intros E Q v T HT HV.
  apply (safety_intro_shape _ _ _ _ HT).
  destruct HV; exact I.
Qed.

Local Ltac focus_shape H V :=
  let S := fresh "Shape" in
  pose proof (safety_value_shape _ _ _ _ H V _ _ eq_refl) as S;
  simpl in S; repeat lazymatch type of S with ex _ => destruct S as [? S] end;
  lazymatch type of S with or _ _ => destruct S as [S|S] | _ => idtac end.

Local Ltac get_closed Q :=
  let b := fresh "concrete" in let H := fresh "Heval" in
  let W := fresh "Hwf" in
  assert (W : wf_qua empty Q) by
    (first [assumption | solve [eauto 3 with core_safety]]);
  destruct (safety_closed_concrete _ W) as [b H];
  unfold safety_concrete in H; clear W.

Lemma safety_value_compat : forall v Q A R c T U,
  typing empty R v (qtyp_qtyp Q A) -> value v ->
  typing_ctx empty Q c T U ->
  exists b, concretize (safety_tag v) = Some b /\ barrier_compatible c b.
Proof.
  intros v Q A R c T U HT HV HC.
  pose proof (safety_value_tag _ _ _ _ HT HV _ _ eq_refl) as HQ.
  get_closed (safety_tag v).
  exists concrete; split; [assumption|].
  eapply safety_ctx_compatible; [exact HC|].
  rewrite <- (safety_eval_concrete _ _ Heval).
  eapply safety_sq_eval; eassumption.
Qed.

Lemma safety_progress_upqual : forall Q v P A c,
  typing empty Q v (qtyp_qtyp P A) -> value v ->
  exists s', 〈 v | frame_upqual P :: c 〉 --> s'.
Proof.
  intros Q v P A c HT HV.
  pose proof (safety_value_tag _ _ _ _ HT HV _ _ eq_refl) as HQ.
  get_closed (safety_tag v). get_closed P.
  assert (Hle : concrete ≤ concrete0) by (eapply safety_sq_concrete; eassumption).
  destruct HV; simpl in Heval; eauto 4 with core_safety.
Qed.

Lemma safety_progress_check : forall Q v P R A c,
  typing empty Q v (qtyp_qtyp (qua_meet P R) A) -> value v -> wf_qua empty R ->
  exists s', 〈 v | frame_check R :: c 〉 --> s'.
Proof.
  intros Q v P R A c HT HV HW.
  pose proof (safety_value_tag _ _ _ _ HT HV _ _ eq_refl) as HQ.
  get_closed (safety_tag v). get_closed R.
  assert (Hle : concrete ≤ concrete0).
  { apply safety_sq_eval in HQ. simpl in HQ.
    rewrite (safety_eval_concrete _ _ Heval) in HQ.
    apply (proj2 (meet_is_glb _ _ _)) in HQ.
    rewrite <- (safety_eval_concrete _ _ Heval0). tauto. }
  destruct HV; simpl in Heval; eauto 4 with core_safety.
Qed.

Lemma safety_progress_value : forall E Q c T U, typing_ctx E Q c T U ->
  E = empty -> forall v, typing E Q v T -> value v ->
  done_state 〈 v | c 〉 \/ exists s', 〈 v | c 〉 --> s'.
Proof.
  induction 1; intros He v' HT HV; subst;
    try solve [eauto 4 with core_safety];
    right.
  - focus_shape H1 H0; subst.
    destruct (safety_value_compat _ _ _ _ _ _ _ H1 H0 H) as [b [Hb HC]].
    simpl in Hb. eauto 4 with core_safety.
  - focus_shape HT HV; subst.
    destruct (safety_value_compat _ _ _ _ _ _ _ HT HV H) as [b [Hb HC]].
    simpl in Hb. eexists; eapply step_app_tabs; [|exact Hb|exact HC].
    eapply safety_wf_typ_lc, safety_sub_left; eassumption.
  - focus_shape HT HV; subst.
    destruct (safety_value_compat _ _ _ _ _ _ _ HT HV H) as [b [Hb HC]].
    simpl in Hb. eexists; eapply step_app_qabs; [|exact Hb|exact HC].
    eapply safety_wf_qua_lc, safety_sq_left; eassumption.
  - focus_shape HT HV; subst; inversion HV; subst; eauto 3 with core_safety.
  - focus_shape HT HV; subst; inversion HV; subst; eauto 3 with core_safety.
  - focus_shape HT HV; subst; inversion HV; subst; eauto 3 with core_safety.
  - eapply safety_progress_upqual; eassumption.
  - eapply safety_progress_check; eassumption.
  - focus_shape HT HV; subst.
    match goal with |- exists s, step (state_step (exp_int _ ?n) _) _ =>
      destruct (Z.eq_dec n 0) as [->|Hn] end; eauto 3 with core_safety.
Qed.

Lemma safety_progress_focus : forall E Q e T, typing E Q e T ->
  E = empty -> forall c U, typing_ctx E Q c T U ->
  value e \/ exists s', 〈 e | c 〉 --> s'.
Proof.
  induction 1; intros He c U HC; subst; try solve [eauto 4 with core_safety].
  - inversion H0.
  - left. constructor. eapply safety_typing_expr. eapply typing_abs with (L := L); eassumption.
  - left. constructor. eapply safety_typing_expr. eapply typing_tabs with (L := L); eassumption.
  - left. constructor. eapply safety_typing_expr. eapply typing_qabs with (L := L); eassumption.
  - assert (wf_qua empty (qua_negate P)) as HW by (eapply safety_sq_right; eassumption).
    inversion HW; subst. get_closed P.
    right. eexists. eapply step_without; eassumption.
  - right. eexists. apply step_do.
    eapply safety_ctx_compatible; [exact HC|apply reflexive].
Qed.

(* Weakening keeps the bindings already in scope. *)
Definition safety_includes (E F : env) :=
  forall x b, binds x b E -> binds x b F.

Lemma safety_includes_cons : forall E F x b,
  safety_includes E F -> safety_includes ((x,b)::E) ((x,b)::F).
Proof.
  unfold safety_includes, binds; simpl; intros E F x b HI y a [H|H]; [left|right]; auto.
Qed.

Lemma safety_includes_tail : forall E x b, safety_includes E ((x,b)::E).
Proof. intros E x b y a Hb; right; assumption. Qed.

Local Hint Resolve safety_includes_cons safety_includes_tail : core_safety.

Lemma safety_sq_weaken : forall E Q R, subqual E Q R ->
  forall F, safety_includes E F -> wf_env F -> subqual F Q R.
Proof.
  induction 1; intros F HI HW;
    assert (HS : safety_scopes E F) by (apply safety_scopes_weaken; exact HI).
  all: try solve [eauto 3 with core_safety].
  all: try solve [eapply subqual_eval_elim; [eapply IHsubqual1|eassumption|eapply IHsubqual2]; eauto].
  all: try solve [eapply subqual_eval_intro; [eapply IHsubqual1|eassumption|eapply IHsubqual2]; eauto].
  all: try solve [eapply subqual_trans; [eapply IHsubqual1|eapply IHsubqual2]; eauto].
  - eapply subqual_trans_qvar; [apply HI; eassumption|eauto].
  - apply subqual_join_inl; eauto 2 with core_safety.
  - apply subqual_join_inr; eauto 2 with core_safety.
  - apply subqual_join_elim; auto.
  - apply subqual_meet_eliml; eauto 2 with core_safety.
  - apply subqual_meet_elimr; eauto 2 with core_safety.
  - apply subqual_meet_intro; auto.
  - apply subqual_dist; eauto 2 with core_safety.
Qed.
Local Hint Resolve safety_sq_weaken : core_safety.

Local Ltac weaken_binder K :=
  intros x Hx;
  match goal with
  | IH : forall y : atom, y `notin` K -> forall G, safety_includes _ G -> wf_env G -> _
    |- _ =>
    eapply (IH x); [solve_notin | apply safety_includes_cons; assumption
      | econstructor; [assumption| |solve_notin]]
  end.

Lemma safety_sub_weaken :
  (forall E S T, sub E S T ->
    forall F, safety_includes E F -> wf_env F -> sub F S T) /\
  (forall E S T, subqtype E S T ->
    forall F, safety_includes E F -> wf_env F -> subqtype F S T).
Proof.
  apply sub_types_ind; intros;
    try solve [eauto 4 using safety_scopes_weaken with core_safety].
  - eapply sub_all with (L := L `union` dom F); [eauto|].
    weaken_binder L. eapply safety_sub_left; eauto.
  - eapply sub_qall with (L := L `union` dom F); [eauto with core_safety|].
    weaken_binder L. eapply safety_wf_qua_scope; [eapply safety_sq_left; eassumption|apply safety_scopes_weaken; assumption].
Qed.
Definition safety_sub_weaken_typ := proj1 safety_sub_weaken.
Definition safety_sub_weaken_qtyp := proj2 safety_sub_weaken.
Local Hint Resolve safety_sub_weaken_typ safety_sub_weaken_qtyp : core_safety.

Lemma safety_typing_weaken : forall E Q e T, typing E Q e T ->
  forall F, safety_includes E F -> wf_env F -> typing F Q e T.
Proof.
  induction 1; intros F HI HW;
    assert (HS : safety_scopes E F) by (apply safety_scopes_weaken; exact HI);
    try solve [eauto 4 using safety_scopes_weaken with core_safety].
  all: try solve [apply typing_inl; eauto 2 with core_safety].
  all: try solve [apply typing_inr; eauto 2 with core_safety].
  all: try solve [apply typing_pair; eauto 2 with core_safety].
  - eapply typing_abs with (L := L `union` dom F).
    weaken_binder L. body_environment.
    eapply safety_wf_qtyp_scope; eauto using safety_scopes_weaken.
  - eapply typing_tabs with (L := L `union` dom F).
    weaken_binder L. body_environment.
    eapply safety_wf_typ_scope; eauto using safety_scopes_weaken.
  - eapply typing_qabs with (L := L `union` dom F).
    + eapply safety_wf_qua_scope; eauto using safety_scopes_weaken.
    + weaken_binder L. body_environment.
      eapply safety_wf_qua_scope; eauto using safety_scopes_weaken.
  - eapply typing_let with (L := L `union` dom F); [eauto|].
    weaken_binder L. body_environment.
    eapply safety_wf_qtyp_scope; eauto using safety_scopes_weaken.
  - eapply typing_case with (L := L `union` dom F); [eauto| |].
    + weaken_binder L.
      fresh_atom y L.
      destruct (safety_wf_cons _ _ _ (safety_typing_env _ _ _ _ (H0 y ltac:(assumption)))) as [_ [_ ?]].
      eapply safety_wf_qtyp_scope; eassumption.
    + weaken_binder L.
      fresh_atom y L.
      destruct (safety_wf_cons _ _ _ (safety_typing_env _ _ _ _ (H2 y ltac:(assumption)))) as [_ [_ ?]].
      eapply safety_wf_qtyp_scope; eassumption.
  - eapply typing_if0; eauto.
Qed.

Local Hint Resolve safety_typing_weaken : core_safety.

Lemma safety_value_pure : forall v, value v -> forall E Q T,
  typing E Q v T -> typing E `pure v T.
Proof.
  intros v HV E Q T HT. induction HT; inversion HV; subst;
    eauto 5 with core_safety.
Qed.
(* These depth predicates track which indices an opening may replace. *)
Fixpoint safety_depth_qua (k : nat) (T : qua) {struct T} : Prop :=
  match T with
  | qua_base _ => True
  | qua_bvar x1 => (x1 < k)%nat
  | qua_fvar _ => True
  | qua_meet x1 x2 => safety_depth_qua k x1 /\ safety_depth_qua k x2
  | qua_join x1 x2 => safety_depth_qua k x1 /\ safety_depth_qua k x2
  | qua_negate x1 => safety_depth_qua k x1
  end.
Fixpoint safety_depth_typ (k : nat) (T : typ) {struct T} : Prop :=
  match T with
  | typ_top => True
  | typ_int => True
  | typ_bvar x1 => (x1 < k)%nat
  | typ_fvar _ => True
  | typ_arrow x1 x2 => safety_depth_qtyp k x1 /\ safety_depth_qtyp (S k) x2
  | typ_all x1 x2 => safety_depth_typ k x1 /\ safety_depth_qtyp (S k) x2
  | typ_qall x1 x2 => safety_depth_qua k x1 /\ safety_depth_qtyp (S k) x2
  | typ_sum x1 x2 => safety_depth_qtyp k x1 /\ safety_depth_qtyp k x2
  | typ_pair x1 x2 => safety_depth_qtyp k x1 /\ safety_depth_qtyp k x2
  | typ_ref x1 => safety_depth_qtyp k x1
  end
with safety_depth_qtyp (k : nat) (T : qtyp) {struct T} : Prop :=
  match T with
  | qtyp_qtyp x1 x2 => safety_depth_qua k x1 /\ safety_depth_typ k x2
  end.
Fixpoint safety_depth_exp (k : nat) (T : exp) {struct T} : Prop :=
  match T with
  | exp_int x1 _ => safety_depth_qua k x1
  | exp_bvar x1 => (x1 < k)%nat
  | exp_fvar _ => True
  | exp_abs x1 x2 x3 => safety_depth_qua k x1 /\ safety_depth_qtyp k x2 /\ safety_depth_exp (S k) x3
  | exp_app x1 x2 => safety_depth_exp k x1 /\ safety_depth_exp k x2
  | exp_tabs x1 x2 x3 => safety_depth_qua k x1 /\ safety_depth_typ k x2 /\ safety_depth_exp (S k) x3
  | exp_tapp x1 x2 => safety_depth_exp k x1 /\ safety_depth_typ k x2
  | exp_qabs x1 x2 x3 => safety_depth_qua k x1 /\ safety_depth_qua k x2 /\ safety_depth_exp (S k) x3
  | exp_qapp x1 x2 => safety_depth_exp k x1 /\ safety_depth_qua k x2
  | exp_let x1 x2 => safety_depth_exp k x1 /\ safety_depth_exp (S k) x2
  | exp_inl x1 x2 => safety_depth_qua k x1 /\ safety_depth_exp k x2
  | exp_inr x1 x2 => safety_depth_qua k x1 /\ safety_depth_exp k x2
  | exp_case x1 x2 x3 => safety_depth_exp k x1 /\ safety_depth_exp (S k) x2 /\ safety_depth_exp (S k) x3
  | exp_pair x1 x2 x3 => safety_depth_qua k x1 /\ safety_depth_exp k x2 /\ safety_depth_exp k x3
  | exp_first x1 => safety_depth_exp k x1
  | exp_second x1 => safety_depth_exp k x1
  | exp_ref x1 x2 => safety_depth_qua k x1 /\ safety_depth_exp k x2
  | exp_ref_label x1 _ => safety_depth_qua k x1
  | exp_deref x1 => safety_depth_exp k x1
  | exp_set_ref x1 x2 => safety_depth_exp k x1 /\ safety_depth_exp k x2
  | exp_upqual x1 x2 => safety_depth_qua k x1 /\ safety_depth_exp k x2
  | exp_check x1 x2 => safety_depth_qua k x1 /\ safety_depth_exp k x2
  | exp_without x1 x2 => safety_depth_qua k x1 /\ safety_depth_exp k x2
  | exp_do _ => True
  | exp_if0 x1 x2 x3 => safety_depth_exp k x1 /\ safety_depth_exp k x2 /\ safety_depth_exp k x3
  end.

Scheme safety_typ_syntax := Induction for typ Sort Prop
with safety_qtyp_syntax := Induction for qtyp Sort Prop.
Combined Scheme safety_types_syntax from safety_typ_syntax, safety_qtyp_syntax.

Local Hint Resolve Nat.le_refl : safety_depth.
Local Hint Extern 2 (_ <= _)%nat => lia : safety_depth.
Lemma safety_depth_monotone_q :
  (forall (T : qua) k j, safety_depth_qua k T -> (k <= j)%nat -> safety_depth_qua j T).
Proof.
  induction T; simpl; intros; split_facts; repeat split; eauto 4 with safety_depth; lia.
Qed.

Lemma safety_depth_monotone_tu :
  (forall (T : typ) k j, safety_depth_typ k T -> (k <= j)%nat -> safety_depth_typ j T) /\
  (forall (T : qtyp) k j, safety_depth_qtyp k T -> (k <= j)%nat -> safety_depth_qtyp j T).
Proof.
  apply safety_types_syntax; simpl; intros; split_facts; repeat split; eauto 4 using safety_depth_monotone_q with safety_depth; lia.
Qed.
Definition safety_depth_monotone_tu_t := proj1 safety_depth_monotone_tu.
Definition safety_depth_monotone_tu_u := proj2 safety_depth_monotone_tu.

Local Hint Resolve safety_depth_monotone_q safety_depth_monotone_tu_t safety_depth_monotone_tu_u : safety_depth.
Lemma safety_open_q_identity_q :
  (forall (T : qua) k j U, safety_depth_qua k T -> (k <= j)%nat -> open_qq_rec j U T = T).
Proof.
  induction T; simpl; intros; split_facts;
    try solve [f_equal; eauto 4 with safety_depth];
    repeat match goal with |- context [if ?d then _ else _] => destruct d end; subst; try reflexivity; lia.
Qed.

Lemma safety_open_q_identity_tu :
  (forall (T : typ) k j U, safety_depth_typ k T -> (k <= j)%nat -> open_qt_rec j U T = T) /\
  (forall (T : qtyp) k j U, safety_depth_qtyp k T -> (k <= j)%nat -> open_qqt_rec j U T = T).
Proof.
  apply safety_types_syntax; simpl; intros; split_facts;
    try solve [f_equal; eauto 4 using safety_open_q_identity_q with safety_depth];
    repeat match goal with |- context [if ?d then _ else _] => destruct d end; subst; try reflexivity; lia.
Qed.
Definition safety_open_q_identity_tu_t := proj1 safety_open_q_identity_tu.
Definition safety_open_q_identity_tu_u := proj2 safety_open_q_identity_tu.

Lemma safety_open_q_identity_e :
  (forall (T : exp) k j U, safety_depth_exp k T -> (k <= j)%nat -> open_qe_rec j U T = T).
Proof.
  induction T; simpl; intros; split_facts;
    try solve [f_equal; eauto 4 using safety_open_q_identity_tu_t, safety_open_q_identity_tu_u, safety_open_q_identity_q with safety_depth];
    repeat match goal with |- context [if ?d then _ else _] => destruct d end; subst; try reflexivity; lia.
Qed.

Lemma safety_open_t_identity_tu :
  (forall (T : typ) k j U, safety_depth_typ k T -> (k <= j)%nat -> open_tt_rec j U T = T) /\
  (forall (T : qtyp) k j U, safety_depth_qtyp k T -> (k <= j)%nat -> open_tqt_rec j U T = T).
Proof.
  apply safety_types_syntax; simpl; intros; split_facts;
    try solve [f_equal; eauto 4 with safety_depth];
    repeat match goal with |- context [if ?d then _ else _] => destruct d end; subst; try reflexivity; lia.
Qed.
Definition safety_open_t_identity_tu_t := proj1 safety_open_t_identity_tu.
Definition safety_open_t_identity_tu_u := proj2 safety_open_t_identity_tu.

Lemma safety_open_t_identity_e :
  (forall (T : exp) k j U, safety_depth_exp k T -> (k <= j)%nat -> open_te_rec j U T = T).
Proof.
  induction T; simpl; intros; split_facts;
    try solve [f_equal; eauto 4 using safety_open_t_identity_tu_t, safety_open_t_identity_tu_u with safety_depth];
    repeat match goal with |- context [if ?d then _ else _] => destruct d end; subst; try reflexivity; lia.
Qed.

Lemma safety_open_e_identity_e :
  (forall (T : exp) k j U, safety_depth_exp k T -> (k <= j)%nat -> open_ee_rec j U T = T).
Proof.
  induction T; simpl; intros; split_facts;
    try solve [f_equal; eauto 4 with safety_depth];
    repeat match goal with |- context [if ?d then _ else _] => destruct d end; subst; try reflexivity; lia.
Qed.

Lemma safety_open_q_depth_q :
  (forall (T : qua) k X, safety_depth_qua k (open_qq_rec k (qua_fvar X) T) -> safety_depth_qua (S k) T).
Proof.
  induction T; simpl; intros; split_facts;
    try solve [repeat split; eauto 4 with safety_depth];
    repeat match goal with H : context [if ?d then _ else _] |- _ => destruct d end; subst; simpl in *; lia.
Qed.

Lemma safety_open_q_depth_tu :
  (forall (T : typ) k X, safety_depth_typ k (open_qt_rec k (qua_fvar X) T) -> safety_depth_typ (S k) T) /\
  (forall (T : qtyp) k X, safety_depth_qtyp k (open_qqt_rec k (qua_fvar X) T) -> safety_depth_qtyp (S k) T).
Proof.
  apply safety_types_syntax; simpl; intros; split_facts;
    try solve [repeat split; eauto 4 using safety_open_q_depth_q with safety_depth];
    repeat match goal with H : context [if ?d then _ else _] |- _ => destruct d end; subst; simpl in *; lia.
Qed.
Definition safety_open_q_depth_tu_t := proj1 safety_open_q_depth_tu.
Definition safety_open_q_depth_tu_u := proj2 safety_open_q_depth_tu.

Lemma safety_open_q_depth_e :
  (forall (T : exp) k X, safety_depth_exp k (open_qe_rec k (qua_fvar X) T) -> safety_depth_exp (S k) T).
Proof.
  induction T; simpl; intros; split_facts;
    try solve [repeat split; eauto 4 using safety_open_q_depth_tu_t, safety_open_q_depth_tu_u, safety_open_q_depth_q with safety_depth];
    repeat match goal with H : context [if ?d then _ else _] |- _ => destruct d end; subst; simpl in *; lia.
Qed.

Lemma safety_open_t_depth_tu :
  (forall (T : typ) k X, safety_depth_typ k (open_tt_rec k (typ_fvar X) T) -> safety_depth_typ (S k) T) /\
  (forall (T : qtyp) k X, safety_depth_qtyp k (open_tqt_rec k (typ_fvar X) T) -> safety_depth_qtyp (S k) T).
Proof.
  apply safety_types_syntax; simpl; intros; split_facts;
    try solve [repeat split; eauto 4 with safety_depth];
    repeat match goal with H : context [if ?d then _ else _] |- _ => destruct d end; subst; simpl in *; lia.
Qed.
Definition safety_open_t_depth_tu_t := proj1 safety_open_t_depth_tu.
Definition safety_open_t_depth_tu_u := proj2 safety_open_t_depth_tu.

Lemma safety_open_t_depth_e :
  (forall (T : exp) k X, safety_depth_exp k (open_te_rec k (typ_fvar X) T) -> safety_depth_exp (S k) T).
Proof.
  induction T; simpl; intros; split_facts;
    try solve [repeat split; eauto 4 using safety_open_t_depth_tu_t, safety_open_t_depth_tu_u with safety_depth];
    repeat match goal with H : context [if ?d then _ else _] |- _ => destruct d end; subst; simpl in *; lia.
Qed.

Lemma safety_open_e_depth_e :
  (forall (T : exp) k X, safety_depth_exp k (open_ee_rec k (exp_fvar X) T) -> safety_depth_exp (S k) T).
Proof.
  induction T; simpl; intros; split_facts;
    try solve [repeat split; eauto 4 with safety_depth];
    repeat match goal with H : context [if ?d then _ else _] |- _ => destruct d end; subst; simpl in *; lia.
Qed.

Lemma safety_qual_depth : forall Q, qual Q -> safety_depth_qua 0 Q.
Proof. induction 1; simpl; auto. Qed.
Lemma safety_type_depth :
  (forall T, type T -> safety_depth_typ 0 T) /\
  (forall T, qtype T -> safety_depth_qtyp 0 T).
Proof.
  apply types_ind; simpl; intros; eauto using safety_qual_depth with safety_depth.
  - split; [assumption|].
    fresh_atom X L. apply (safety_open_t_depth_tu_u _ 0 X). apply H0; assumption.
  - split; [auto using safety_qual_depth|].
    fresh_atom X L. apply (safety_open_q_depth_tu_u _ 0 X). apply H; assumption.
Qed.

Definition safety_typ_depth := proj1 safety_type_depth.

Lemma safety_expr_depth : forall e, expr e -> safety_depth_exp 0 e.
Proof.
  pose proof (proj1 safety_type_depth) as HT.
  pose proof (proj2 safety_type_depth) as HU.
  induction 1; simpl; repeat split; eauto using safety_qual_depth with safety_depth;
    match goal with
    | H : forall x : atom, x `notin` ?A -> safety_depth_exp 0 _ |- _ =>
      let x := fresh "x" in fresh_atom x A;
      let HO := fresh in pose proof (H x ltac:(assumption)) as HO;
      unfold open_ee, open_te, open_qe in HO;
      first [eapply safety_open_e_depth_e; exact HO
            |eapply safety_open_t_depth_e; exact HO
            |eapply safety_open_q_depth_e; exact HO]
    end.
Qed.

(* Parallel substitution for free variables of the three binding kinds. *)
Record safety_images := {
  safety_qua_image : atom -> qua;
  safety_typ_image : atom -> typ;
  safety_exp_image : atom -> exp
}.

Definition safety_fixed (m : safety_images) (x : atom) :=
  safety_qua_image m x = qua_fvar x /\
  safety_typ_image m x = typ_fvar x /\
  safety_exp_image m x = exp_fvar x.

Definition safety_images_closed (m : safety_images) :=
  forall x, safety_depth_qua 0 (safety_qua_image m x) /\
  safety_depth_typ 0 (safety_typ_image m x) /\
  safety_depth_exp 0 (safety_exp_image m x).

Fixpoint safety_map_qua (m : safety_images) (T : qua) {struct T} : qua :=
  match T with
  | qua_base x1 => qua_base x1
  | qua_bvar x1 => qua_bvar x1
  | qua_fvar x1 => safety_qua_image m x1
  | qua_meet x1 x2 => qua_meet (safety_map_qua m x1) (safety_map_qua m x2)
  | qua_join x1 x2 => qua_join (safety_map_qua m x1) (safety_map_qua m x2)
  | qua_negate x1 => qua_negate (safety_map_qua m x1)
  end.
Fixpoint safety_map_typ (m : safety_images) (T : typ) {struct T} : typ :=
  match T with
  | typ_top => typ_top
  | typ_int => typ_int
  | typ_bvar x1 => typ_bvar x1
  | typ_fvar x1 => safety_typ_image m x1
  | typ_arrow x1 x2 => typ_arrow (safety_map_qtyp m x1) (safety_map_qtyp m x2)
  | typ_all x1 x2 => typ_all (safety_map_typ m x1) (safety_map_qtyp m x2)
  | typ_qall x1 x2 => typ_qall (safety_map_qua m x1) (safety_map_qtyp m x2)
  | typ_sum x1 x2 => typ_sum (safety_map_qtyp m x1) (safety_map_qtyp m x2)
  | typ_pair x1 x2 => typ_pair (safety_map_qtyp m x1) (safety_map_qtyp m x2)
  | typ_ref x1 => typ_ref (safety_map_qtyp m x1)
  end
with safety_map_qtyp (m : safety_images) (T : qtyp) {struct T} : qtyp :=
  match T with
  | qtyp_qtyp x1 x2 => qtyp_qtyp (safety_map_qua m x1) (safety_map_typ m x2)
  end.
Fixpoint safety_map_exp (m : safety_images) (T : exp) {struct T} : exp :=
  match T with
  | exp_int x1 x2 => exp_int (safety_map_qua m x1) x2
  | exp_bvar x1 => exp_bvar x1
  | exp_fvar x1 => safety_exp_image m x1
  | exp_abs x1 x2 x3 => exp_abs (safety_map_qua m x1) (safety_map_qtyp m x2) (safety_map_exp m x3)
  | exp_app x1 x2 => exp_app (safety_map_exp m x1) (safety_map_exp m x2)
  | exp_tabs x1 x2 x3 => exp_tabs (safety_map_qua m x1) (safety_map_typ m x2) (safety_map_exp m x3)
  | exp_tapp x1 x2 => exp_tapp (safety_map_exp m x1) (safety_map_typ m x2)
  | exp_qabs x1 x2 x3 => exp_qabs (safety_map_qua m x1) (safety_map_qua m x2) (safety_map_exp m x3)
  | exp_qapp x1 x2 => exp_qapp (safety_map_exp m x1) (safety_map_qua m x2)
  | exp_let x1 x2 => exp_let (safety_map_exp m x1) (safety_map_exp m x2)
  | exp_inl x1 x2 => exp_inl (safety_map_qua m x1) (safety_map_exp m x2)
  | exp_inr x1 x2 => exp_inr (safety_map_qua m x1) (safety_map_exp m x2)
  | exp_case x1 x2 x3 => exp_case (safety_map_exp m x1) (safety_map_exp m x2) (safety_map_exp m x3)
  | exp_pair x1 x2 x3 => exp_pair (safety_map_qua m x1) (safety_map_exp m x2) (safety_map_exp m x3)
  | exp_first x1 => exp_first (safety_map_exp m x1)
  | exp_second x1 => exp_second (safety_map_exp m x1)
  | exp_ref x1 x2 => exp_ref (safety_map_qua m x1) (safety_map_exp m x2)
  | exp_ref_label x1 x2 => exp_ref_label (safety_map_qua m x1) x2
  | exp_deref x1 => exp_deref (safety_map_exp m x1)
  | exp_set_ref x1 x2 => exp_set_ref (safety_map_exp m x1) (safety_map_exp m x2)
  | exp_upqual x1 x2 => exp_upqual (safety_map_qua m x1) (safety_map_exp m x2)
  | exp_check x1 x2 => exp_check (safety_map_qua m x1) (safety_map_exp m x2)
  | exp_without x1 x2 => exp_without (safety_map_qua m x1) (safety_map_exp m x2)
  | exp_do x1 => exp_do x1
  | exp_if0 x1 x2 x3 => exp_if0 (safety_map_exp m x1) (safety_map_exp m x2) (safety_map_exp m x3)
  end.

Local Ltac destruct_tests := repeat match goal with |- context [if ?d then _ else _] => destruct d end.
Lemma safety_map_open_q_q :
  (forall (T : qua) m k U, safety_images_closed m ->
    safety_map_qua m (open_qq_rec k U T) =
    open_qq_rec k (safety_map_qua m U) (safety_map_qua m T)).
Proof.
  induction T; intros; simpl; destruct_tests; try reflexivity;
    try solve [f_equal; eauto 3 using safety_open_q_identity_q];
    symmetry; match goal with
    | HC : safety_images_closed ?m |- context [safety_qua_image ?m ?x] => destruct (HC x) as [? [? ?]]
    | HC : safety_images_closed ?m |- context [safety_typ_image ?m ?x] => destruct (HC x) as [? [? ?]]
    | HC : safety_images_closed ?m |- context [safety_exp_image ?m ?x] => destruct (HC x) as [? [? ?]]
    end; eauto 3 using safety_open_q_identity_q with safety_depth.
Qed.

Lemma safety_map_open_q_tu :
  (forall (T : typ) m k U, safety_images_closed m ->
    safety_map_typ m (open_qt_rec k U T) =
    open_qt_rec k (safety_map_qua m U) (safety_map_typ m T)) /\
  (forall (T : qtyp) m k U, safety_images_closed m ->
    safety_map_qtyp m (open_qqt_rec k U T) =
    open_qqt_rec k (safety_map_qua m U) (safety_map_qtyp m T)).
Proof.
  apply safety_types_syntax; intros; simpl; destruct_tests; try reflexivity;
    try solve [f_equal; eauto 3 using safety_map_open_q_q, safety_open_q_identity_tu_t];
    symmetry; match goal with
    | HC : safety_images_closed ?m |- context [safety_qua_image ?m ?x] => destruct (HC x) as [? [? ?]]
    | HC : safety_images_closed ?m |- context [safety_typ_image ?m ?x] => destruct (HC x) as [? [? ?]]
    | HC : safety_images_closed ?m |- context [safety_exp_image ?m ?x] => destruct (HC x) as [? [? ?]]
    end; eauto 3 using safety_map_open_q_q, safety_open_q_identity_tu_t with safety_depth.
Qed.
Definition safety_map_open_q_tu_t := proj1 safety_map_open_q_tu.
Definition safety_map_open_q_tu_u := proj2 safety_map_open_q_tu.

Lemma safety_map_open_q_e :
  (forall (T : exp) m k U, safety_images_closed m ->
    safety_map_exp m (open_qe_rec k U T) =
    open_qe_rec k (safety_map_qua m U) (safety_map_exp m T)).
Proof.
  induction T; intros; simpl; destruct_tests; try reflexivity;
    try solve [f_equal; eauto 3 using safety_map_open_q_tu_t, safety_map_open_q_tu_u, safety_map_open_q_q, safety_open_q_identity_e];
    symmetry; match goal with
    | HC : safety_images_closed ?m |- context [safety_qua_image ?m ?x] => destruct (HC x) as [? [? ?]]
    | HC : safety_images_closed ?m |- context [safety_typ_image ?m ?x] => destruct (HC x) as [? [? ?]]
    | HC : safety_images_closed ?m |- context [safety_exp_image ?m ?x] => destruct (HC x) as [? [? ?]]
    end; eauto 3 using safety_map_open_q_tu_t, safety_map_open_q_tu_u, safety_map_open_q_q, safety_open_q_identity_e with safety_depth.
Qed.

Lemma safety_map_open_t_tu :
  (forall (T : typ) m k U, safety_images_closed m ->
    safety_map_typ m (open_tt_rec k U T) =
    open_tt_rec k (safety_map_typ m U) (safety_map_typ m T)) /\
  (forall (T : qtyp) m k U, safety_images_closed m ->
    safety_map_qtyp m (open_tqt_rec k U T) =
    open_tqt_rec k (safety_map_typ m U) (safety_map_qtyp m T)).
Proof.
  apply safety_types_syntax; intros; simpl; destruct_tests; try reflexivity;
    try solve [f_equal; eauto 3 using safety_open_t_identity_tu_t];
    symmetry; match goal with
    | HC : safety_images_closed ?m |- context [safety_qua_image ?m ?x] => destruct (HC x) as [? [? ?]]
    | HC : safety_images_closed ?m |- context [safety_typ_image ?m ?x] => destruct (HC x) as [? [? ?]]
    | HC : safety_images_closed ?m |- context [safety_exp_image ?m ?x] => destruct (HC x) as [? [? ?]]
    end; eauto 3 using safety_open_t_identity_tu_t with safety_depth.
Qed.
Definition safety_map_open_t_tu_t := proj1 safety_map_open_t_tu.
Definition safety_map_open_t_tu_u := proj2 safety_map_open_t_tu.

Lemma safety_map_open_t_e :
  (forall (T : exp) m k U, safety_images_closed m ->
    safety_map_exp m (open_te_rec k U T) =
    open_te_rec k (safety_map_typ m U) (safety_map_exp m T)).
Proof.
  induction T; intros; simpl; destruct_tests; try reflexivity;
    try solve [f_equal; eauto 3 using safety_map_open_t_tu_t, safety_map_open_t_tu_u, safety_open_t_identity_e];
    symmetry; match goal with
    | HC : safety_images_closed ?m |- context [safety_qua_image ?m ?x] => destruct (HC x) as [? [? ?]]
    | HC : safety_images_closed ?m |- context [safety_typ_image ?m ?x] => destruct (HC x) as [? [? ?]]
    | HC : safety_images_closed ?m |- context [safety_exp_image ?m ?x] => destruct (HC x) as [? [? ?]]
    end; eauto 3 using safety_map_open_t_tu_t, safety_map_open_t_tu_u, safety_open_t_identity_e with safety_depth.
Qed.

Lemma safety_map_open_e_e :
  (forall (T : exp) m k U, safety_images_closed m ->
    safety_map_exp m (open_ee_rec k U T) =
    open_ee_rec k (safety_map_exp m U) (safety_map_exp m T)).
Proof.
  induction T; intros; simpl; destruct_tests; try reflexivity;
    try solve [f_equal; eauto 3 using safety_open_e_identity_e];
    symmetry; match goal with
    | HC : safety_images_closed ?m |- context [safety_qua_image ?m ?x] => destruct (HC x) as [? [? ?]]
    | HC : safety_images_closed ?m |- context [safety_typ_image ?m ?x] => destruct (HC x) as [? [? ?]]
    | HC : safety_images_closed ?m |- context [safety_exp_image ?m ?x] => destruct (HC x) as [? [? ?]]
    end; eauto 3 using safety_open_e_identity_e with safety_depth.
Qed.

Fixpoint safety_atoms_qua (T : qua) {struct T} : atoms :=
  match T with
  | qua_base _ => {}
  | qua_bvar _ => {}
  | qua_fvar x1 => {{ x1 }}
  | qua_meet x1 x2 => safety_atoms_qua x1 `union` safety_atoms_qua x2
  | qua_join x1 x2 => safety_atoms_qua x1 `union` safety_atoms_qua x2
  | qua_negate x1 => safety_atoms_qua x1
  end.
Fixpoint safety_atoms_typ (T : typ) {struct T} : atoms :=
  match T with
  | typ_top => {}
  | typ_int => {}
  | typ_bvar _ => {}
  | typ_fvar x1 => {{ x1 }}
  | typ_arrow x1 x2 => safety_atoms_qtyp x1 `union` safety_atoms_qtyp x2
  | typ_all x1 x2 => safety_atoms_typ x1 `union` safety_atoms_qtyp x2
  | typ_qall x1 x2 => safety_atoms_qua x1 `union` safety_atoms_qtyp x2
  | typ_sum x1 x2 => safety_atoms_qtyp x1 `union` safety_atoms_qtyp x2
  | typ_pair x1 x2 => safety_atoms_qtyp x1 `union` safety_atoms_qtyp x2
  | typ_ref x1 => safety_atoms_qtyp x1
  end
with safety_atoms_qtyp (T : qtyp) {struct T} : atoms :=
  match T with
  | qtyp_qtyp x1 x2 => safety_atoms_qua x1 `union` safety_atoms_typ x2
  end.
Fixpoint safety_atoms_exp (T : exp) {struct T} : atoms :=
  match T with
  | exp_int x1 _ => safety_atoms_qua x1
  | exp_bvar _ => {}
  | exp_fvar x1 => {{ x1 }}
  | exp_abs x1 x2 x3 => safety_atoms_qua x1 `union` safety_atoms_qtyp x2 `union` safety_atoms_exp x3
  | exp_app x1 x2 => safety_atoms_exp x1 `union` safety_atoms_exp x2
  | exp_tabs x1 x2 x3 => safety_atoms_qua x1 `union` safety_atoms_typ x2 `union` safety_atoms_exp x3
  | exp_tapp x1 x2 => safety_atoms_exp x1 `union` safety_atoms_typ x2
  | exp_qabs x1 x2 x3 => safety_atoms_qua x1 `union` safety_atoms_qua x2 `union` safety_atoms_exp x3
  | exp_qapp x1 x2 => safety_atoms_exp x1 `union` safety_atoms_qua x2
  | exp_let x1 x2 => safety_atoms_exp x1 `union` safety_atoms_exp x2
  | exp_inl x1 x2 => safety_atoms_qua x1 `union` safety_atoms_exp x2
  | exp_inr x1 x2 => safety_atoms_qua x1 `union` safety_atoms_exp x2
  | exp_case x1 x2 x3 => safety_atoms_exp x1 `union` safety_atoms_exp x2 `union` safety_atoms_exp x3
  | exp_pair x1 x2 x3 => safety_atoms_qua x1 `union` safety_atoms_exp x2 `union` safety_atoms_exp x3
  | exp_first x1 => safety_atoms_exp x1
  | exp_second x1 => safety_atoms_exp x1
  | exp_ref x1 x2 => safety_atoms_qua x1 `union` safety_atoms_exp x2
  | exp_ref_label x1 _ => safety_atoms_qua x1
  | exp_deref x1 => safety_atoms_exp x1
  | exp_set_ref x1 x2 => safety_atoms_exp x1 `union` safety_atoms_exp x2
  | exp_upqual x1 x2 => safety_atoms_qua x1 `union` safety_atoms_exp x2
  | exp_check x1 x2 => safety_atoms_qua x1 `union` safety_atoms_exp x2
  | exp_without x1 x2 => safety_atoms_qua x1 `union` safety_atoms_exp x2
  | exp_do _ => {}
  | exp_if0 x1 x2 x3 => safety_atoms_exp x1 `union` safety_atoms_exp x2 `union` safety_atoms_exp x3
  end.

Definition safety_agrees (m : safety_images) (A : atoms) :=
  forall x, x `in` A -> safety_fixed m x.

Local Ltac use_agrees :=
  lazymatch goal with
  | H : safety_agrees ?m _ |- safety_qua_image ?m ?x = _ =>
      exact (proj1 (H x ltac:(fsetdec)))
  | H : safety_agrees ?m _ |- safety_typ_image ?m ?x = _ =>
      exact (proj1 (proj2 (H x ltac:(fsetdec))))
  | H : safety_agrees ?m _ |- safety_exp_image ?m ?x = _ =>
      exact (proj2 (proj2 (H x ltac:(fsetdec))))
  end.

Lemma safety_map_fixed_q :
  (forall (T : qua) m, safety_agrees m (safety_atoms_qua T) -> safety_map_qua m T = T).
Proof.
  induction T; intros; simpl in *; try reflexivity; try solve [use_agrees];
    f_equal; (eapply H || eapply H0 || eapply H1 || eapply IHT || eapply IHT1 || eapply IHT2 || eapply IHT3);
    unfold safety_agrees in *; intros; eapply H0 || eapply H1 || eapply H2 || eapply H3 || eapply H; fsetdec.
Qed.

Lemma safety_map_fixed_tu :
  (forall (T : typ) m, safety_agrees m (safety_atoms_typ T) -> safety_map_typ m T = T) /\
  (forall (T : qtyp) m, safety_agrees m (safety_atoms_qtyp T) -> safety_map_qtyp m T = T).
Proof.
  apply safety_types_syntax; intros; simpl in *; try reflexivity; try solve [use_agrees];
    f_equal; (eapply H || eapply H0 || eapply H1 || eapply IHT || eapply IHT1 || eapply IHT2 || eapply IHT3 || eapply safety_map_fixed_q);
    unfold safety_agrees in *; intros; eapply H0 || eapply H1 || eapply H2 || eapply H3 || eapply H; fsetdec.
Qed.
Definition safety_map_fixed_tu_t := proj1 safety_map_fixed_tu.
Definition safety_map_fixed_tu_u := proj2 safety_map_fixed_tu.

Lemma safety_map_fixed_e :
  (forall (T : exp) m, safety_agrees m (safety_atoms_exp T) -> safety_map_exp m T = T).
Proof.
  induction T; intros; simpl in *; try reflexivity; try solve [use_agrees];
    f_equal; (eapply H || eapply H0 || eapply H1 || eapply IHT || eapply IHT1 || eapply IHT2 || eapply IHT3 || eapply safety_map_fixed_q || eapply safety_map_fixed_tu_t || eapply safety_map_fixed_tu_u);
    unfold safety_agrees in *; intros; eapply H0 || eapply H1 || eapply H2 || eapply H3 || eapply H; fsetdec.
Qed.

Lemma safety_map_concretize : forall Q b, concretize Q = Some b ->
  forall m, safety_map_qua m Q = Q.
Proof.
  induction Q; simpl; intros b' Hb m; try discriminate; try reflexivity.
  - destruct (concretize Q1), (concretize Q2); try discriminate.
    f_equal; eauto.
  - destruct (concretize Q1), (concretize Q2); try discriminate.
    f_equal; eauto.
  - destruct (concretize Q); try discriminate. f_equal; eauto.
Qed.

Definition safety_map_binding m b :=
  match b with
  | bind_sub T => bind_sub (safety_map_typ m T)
  | bind_qua Q => bind_qua (safety_map_qua m Q)
  | bind_typ T => bind_typ (safety_map_qtyp m T)
  end.

(* The image of each binding remains valid in well-formed extensions. *)
Definition safety_entry (m : safety_images) (F : env) x b :=
  match b with
  | bind_sub V =>
      wf_typ F (safety_typ_image m x) /\
      (forall A, sub F (safety_map_typ m V) A -> sub F (safety_typ_image m x) A)
  | bind_qua R =>
      wf_qua F (safety_qua_image m x) /\
      (forall Q, subqual F (safety_map_qua m R) Q -> subqual F (safety_qua_image m x) Q)
  | bind_typ V =>
      typing F `pure (safety_exp_image m x) (safety_map_qtyp m V)
  end.

Definition safety_morphism m E F :=
  forall G, safety_includes F G -> wf_env G ->
    forall x b, binds x b E -> safety_entry m G x b.

Lemma safety_entry_exact : forall m F x b,
  safety_fixed m x -> wf_env F -> binds x (safety_map_binding m b) F ->
  safety_entry m F x b.
Proof.
  intros m F x b [HQ [HT HE]] HW HB.
  destruct b; simpl in *; rewrite ?HT, ?HQ, ?HE; split || idtac;
    intros; eauto 2 with core_safety.
Qed.

Lemma safety_morphism_extend : forall m E F x b,
  safety_morphism m E F -> safety_fixed m x ->
  safety_morphism m ((x,b)::E) ((x,safety_map_binding m b)::F).
Proof.
  intros m E F x b HM HX G HI HW y a HB.
  destruct HB as [HB|HB].
  - inversion HB; subst. apply safety_entry_exact; auto.
  - eapply HM; [|exact HW|exact HB].
    intros z c HC. apply HI. right; assumption.
Qed.

Lemma safety_morphism_here : forall m E F, safety_morphism m E F -> wf_env F ->
  forall x b, binds x b E -> safety_entry m F x b.
Proof. intros; apply H; eauto; intros y a Hy; exact Hy. Qed.

Local Ltac map_bound :=
  match goal with
  | HM : safety_morphism _ _ _, HW : wf_env _,
    HB : binds _ _ _ |- _ =>
      let H := fresh "Entry" in pose proof (safety_morphism_here _ _ _ HM HW _ _ HB) as H;
      simpl in H; lazymatch type of H with and _ _ => destruct H | _ => idtac end
  end.

Lemma safety_wf_qua_map : forall E Q, wf_qua E Q ->
  forall m F, safety_morphism m E F -> wf_env F -> wf_qua F (safety_map_qua m Q).
Proof.
  induction 1; simpl; intros.
  - constructor.
  - map_bound; assumption.
  - constructor; auto.
  - constructor; auto.
  - constructor; auto.
Qed.

Local Hint Resolve safety_wf_qua_map : core_safety.

Section SafetyTransport.
  Context (m : safety_images) (D : atoms).
  Hypotheses (Hclosed : safety_images_closed m)
    (Hfixed : forall x, x `notin` D -> safety_fixed m x).

  Local Ltac translated_binder A :=
    let x := fresh "x" in let Hx := fresh "Fresh" in
    intros x Hx;
    let Fx := fresh "Fixed" in
    pose proof (Hfixed x ltac:(solve_notin)) as Fx;
    let Hq := fresh "Qname" in let Ht := fresh "Tname" in let He := fresh "Ename" in
    destruct Fx as [Hq [Ht He]];
    unfold open_ee, open_te, open_qe, open_tqt, open_qqt in *;
    let commute lemma var Hname :=
      let Eq := fresh "Open" in
      pose proof (fun T => lemma T m 0 var Hclosed) as Eq;
      cbn in Eq; rewrite Hname in Eq; rewrite <- Eq; clear Eq in
    repeat first [
      commute safety_map_open_e_e (exp_fvar x) He
    | commute safety_map_open_t_e (typ_fvar x) Ht
    | commute safety_map_open_q_e (qua_fvar x) Hq
    | commute safety_map_open_t_tu_u (typ_fvar x) Ht
    | commute safety_map_open_q_tu_u (qua_fvar x) Hq ].

  Lemma safety_wf_type_map :
    (forall E T, wf_typ E T -> forall F, safety_morphism m E F -> wf_env F ->
      wf_typ F (safety_map_typ m T)) /\
    (forall E T, wf_qtyp E T -> forall F, safety_morphism m E F -> wf_env F ->
      wf_qtyp F (safety_map_qtyp m T)).
  Proof.
    apply wf_types_ind; simpl; intros; try solve [constructor; eauto 2 using safety_wf_qua_map].
    - map_bound; assumption.
    - eapply wf_typ_all with (L := L `union` D `union` dom F); [auto|].
      translated_binder L.
      eapply H0; [solve_notin| |].
      + apply safety_morphism_extend; [assumption|apply Hfixed; solve_notin].
      + apply wf_env_sub; auto; solve_notin.
    - eapply wf_typ_qall with (L := L `union` D `union` dom F); [eauto 2 with core_safety|].
      translated_binder L.
      eapply H; [solve_notin| |].
      + apply safety_morphism_extend; [assumption|apply Hfixed; solve_notin].
      + apply wf_env_qua; eauto 2 with core_safety; solve_notin.
  Qed.
  Definition safety_wf_typ_map := proj1 safety_wf_type_map.
  Definition safety_wf_qtyp_map := proj2 safety_wf_type_map.
  Local Hint Resolve safety_wf_typ_map safety_wf_qtyp_map : core_safety.

  Lemma safety_sq_map : forall E Q R, subqual E Q R ->
    forall F, safety_morphism m E F -> wf_env F ->
      subqual F (safety_map_qua m Q) (safety_map_qua m R).
  Proof.
    induction 1; simpl; intros F HM HW.
    - apply subqual_top; try assumption; try solve [eapply IHsubqual; eassumption];
      eapply safety_wf_qua_map; eassumption.
    - apply subqual_bot; try assumption; try solve [eapply IHsubqual; eassumption];
      eapply safety_wf_qua_map; eassumption.
    - eapply subqual_eval_elim with (Q' := safety_map_qua m Q'); eauto.
      now rewrite (safety_map_concretize _ _ H0).
    - eapply subqual_eval_intro with (Q' := safety_map_qua m Q'); eauto.
      now rewrite (safety_map_concretize _ _ H0).
    - apply subqual_lift_elem; auto.
    - apply safety_sq_refl; [|assumption]. change (wf_qua F (safety_map_qua m (qua_fvar X))).
      eapply safety_wf_qua_map; eassumption.
    - map_bound; auto.
    - apply subqual_join_inl; try assumption; try solve [eapply IHsubqual; eassumption];
      eapply safety_wf_qua_map; eassumption.
    - apply subqual_join_inr; try assumption; try solve [eapply IHsubqual; eassumption];
      eapply safety_wf_qua_map; eassumption.
    - apply subqual_join_elim; auto.
    - apply subqual_meet_eliml; try assumption; try solve [eapply IHsubqual; eassumption];
      eapply safety_wf_qua_map; eassumption.
    - apply subqual_meet_elimr; try assumption; try solve [eapply IHsubqual; eassumption];
      eapply safety_wf_qua_map; eassumption.
    - apply subqual_meet_intro; auto.
    - apply subqual_dist; try assumption; try solve [eapply IHsubqual; eassumption];
      eapply safety_wf_qua_map; eassumption.
    - eapply subqual_trans; [eapply IHsubqual1|eapply IHsubqual2]; eauto.
    - apply subqual_negate_intro; try assumption; try solve [eapply IHsubqual; eassumption];
      eapply safety_wf_qua_map; eassumption.
    - apply subqual_negate_elim; try assumption; try solve [eapply IHsubqual; eassumption];
      eapply safety_wf_qua_map; eassumption.
    - apply subqual_refl_negate; try assumption; try solve [eapply IHsubqual; eassumption];
      eapply safety_wf_qua_map; eassumption.
  Qed.
  Local Hint Resolve safety_sq_map : core_safety.

  Lemma safety_sub_map :
    (forall E S T, sub E S T -> forall F, safety_morphism m E F -> wf_env F ->
      sub F (safety_map_typ m S) (safety_map_typ m T)) /\
    (forall E S T, subqtype E S T -> forall F, safety_morphism m E F -> wf_env F ->
      subqtype F (safety_map_qtyp m S) (safety_map_qtyp m T)).
  Proof.
    apply sub_types_ind; simpl; intros; try solve [constructor; eauto 3 with core_safety].
    - apply safety_sub_refl_typ; [|assumption].
      change (wf_typ F (safety_map_typ m (typ_fvar X))).
      eapply safety_wf_typ_map; eassumption.
    - map_bound; auto.
    - eapply sub_all with (L := L `union` D `union` dom F); [auto|].
      translated_binder L.
      eapply H0; [solve_notin| |].
      + apply safety_morphism_extend; [assumption|apply Hfixed; solve_notin].
      + apply wf_env_sub; [assumption| |solve_notin].
        eapply safety_sub_left. eauto.
    - eapply sub_qall with (L := L `union` D `union` dom F); [eauto 2 with core_safety|].
      translated_binder L.
      eapply H; [solve_notin| |].
      + apply safety_morphism_extend; [assumption|apply Hfixed; solve_notin].
      + apply wf_env_qua; [assumption| |solve_notin].
        eapply safety_sq_left. eapply safety_sq_map; eassumption.
  Qed.
  Definition safety_sub_map_typ := proj1 safety_sub_map.
  Definition safety_sub_map_qtyp := proj2 safety_sub_map.
  Local Hint Resolve safety_sub_map_typ safety_sub_map_qtyp : core_safety.

  Local Ltac translate_env Hbind :=
    apply safety_morphism_extend; [assumption|apply Hfixed; solve_notin] ||
    (econstructor; [assumption| |solve_notin];
     (eapply safety_wf_typ_map || eapply safety_wf_qtyp_map || eapply safety_wf_qua_map);
     [exact Hbind|assumption|assumption]).

  Lemma safety_typing_map : forall E Q e T, typing E Q e T ->
    forall F, safety_morphism m E F -> wf_env F ->
      typing F (safety_map_qua m Q) (safety_map_exp m e) (safety_map_qtyp m T).
  Proof.
    induction 1; intros F HM HW; cbn in *; try solve [eauto 3 with core_safety].
    all: try solve [eapply typing_app; [exact (IHtyping1 F HM HW)|exact (IHtyping2 F HM HW)]].
    all: try solve [eapply typing_sub; [exact (IHtyping F HM HW)|eapply safety_sub_map_qtyp; eassumption]].
    all: try solve [eapply typing_subqual; [exact (IHtyping F HM HW)|eapply safety_sq_map; eassumption]].
    all: try solve [eapply typing_if0; eauto 3].
    all: try solve [apply typing_inl; [eapply safety_wf_qua_map; eassumption|exact (IHtyping F HM HW)|eapply safety_wf_qtyp_map; eassumption]].
    all: try solve [apply typing_inr; [eapply safety_wf_qua_map; eassumption|exact (IHtyping F HM HW)|eapply safety_wf_qtyp_map; eassumption]].
    all: try solve [apply typing_pair; [eapply safety_wf_qua_map; eassumption|exact (IHtyping1 F HM HW)|exact (IHtyping2 F HM HW)]].
    all: try solve [eapply typing_upqual; [exact (IHtyping F HM HW)|eapply safety_sq_map; eassumption]].
    all: try solve [eapply typing_check; [exact (IHtyping F HM HW)|eapply safety_sq_map; eassumption]].
    all: try solve [eapply typing_without; [exact (IHtyping F HM HW)|eapply (safety_sq_map _ _ _ H0 F HM HW)]].
    - map_bound; assumption.
    - body_environment.
      eapply typing_abs with (L := L `union` D `union` dom F).
      translated_binder L.
      eapply H0; [solve_notin| |]; translate_env H3.
    - body_environment.
      eapply typing_tabs with (L := L `union` D `union` dom F).
      translated_binder L.
      eapply H0; [solve_notin| |]; translate_env H3.
    - unfold open_tqt. rewrite safety_map_open_t_tu_u by assumption.
      eapply typing_tapp; eauto 3 with core_safety.
    - body_environment.
      eapply typing_qabs with (L := L `union` D `union` dom F).
      + eauto 2 with core_safety.
      + translated_binder L.
        eapply H1; [solve_notin| |]; translate_env H4.
    - unfold open_qqt. rewrite safety_map_open_q_tu_u by assumption.
      eapply typing_qapp; eauto 3 with core_safety.
    - eapply typing_let with (L := L `union` D `union` dom F); [eauto|].
      body_environment.
      translated_binder L.
      eapply H1; [solve_notin| |]; translate_env H4.
    - eapply typing_case with (L := L `union` D `union` dom F); [eauto| |].
      + fresh_atom y L.
        destruct (safety_wf_cons _ _ _ (safety_typing_env _ _ _ _ (H0 y ltac:(assumption)))) as [_ [_ Hbind]].
        translated_binder L.
        eapply H1; [solve_notin| |]; translate_env Hbind.
      + body_environment.
        translated_binder L.
        eapply H3; [solve_notin| |]; translate_env H6.
  Qed.
End SafetyTransport.

Definition safety_identity : safety_images :=
  {| safety_qua_image := qua_fvar; safety_typ_image := typ_fvar;
     safety_exp_image := exp_fvar |}.

Lemma safety_identity_fixed : forall x, safety_fixed safety_identity x.
Proof. intros; repeat split. Qed.

Lemma safety_identity_closed : safety_images_closed safety_identity.
Proof. intros x; repeat split. Qed.

Lemma safety_identity_agrees : forall A, safety_agrees safety_identity A.
Proof. intros A x _; apply safety_identity_fixed. Qed.

Local Hint Resolve safety_identity_agrees : core_safety.

Lemma safety_identity_typ : forall T, safety_map_typ safety_identity T = T.
Proof. intros; apply safety_map_fixed_tu_t, safety_identity_agrees. Qed.
Lemma safety_identity_qua : forall Q, safety_map_qua safety_identity Q = Q.
Proof. intros; apply safety_map_fixed_q, safety_identity_agrees. Qed.
Lemma safety_identity_qtyp : forall T, safety_map_qtyp safety_identity T = T.
Proof. intros; apply safety_map_fixed_tu_u, safety_identity_agrees. Qed.
Lemma safety_identity_binding : forall b, safety_map_binding safety_identity b = b.
Proof.
  destruct b; simpl; rewrite ?safety_identity_typ, ?safety_identity_qua, ?safety_identity_qtyp;
    reflexivity.
Qed.

Lemma safety_narrowing_morphism : forall E x b a,
  (forall G, safety_includes ((x,a)::E) G -> wf_env G ->
    safety_entry safety_identity G x b) ->
  safety_morphism safety_identity ((x,b)::E) ((x,a)::E).
Proof.
  intros E x b a H G HG HW y d [HB|HB].
  - inversion HB; subst; auto.
  - apply safety_entry_exact; [apply safety_identity_fixed|assumption|].
    rewrite safety_identity_binding. apply HG; right; assumption.
Qed.

Lemma safety_narrow_subq : forall E x Q P S T,
  subqual E P Q -> x `notin` dom E ->
  subqtype ((x,bind_qua Q)::E) S T ->
  subqtype ((x,bind_qua P)::E) S T.
Proof.
  intros E x Q P S T HQ Hx HT.
  pose proof (safety_sub_map_qtyp safety_identity {} safety_identity_closed
    (fun x _ => safety_identity_fixed x) _ _ _ HT ((x,bind_qua P)::E)) as HM.
  rewrite !safety_identity_qtyp in HM. apply HM.
  - apply safety_narrowing_morphism; intros G HG HW; simpl.
    assert (HB : binds x (bind_qua P) G) by (apply HG; left; reflexivity).
    rewrite safety_identity_qua. split; [eapply wf_qua_fvar; eassumption|].
    intros R H. eapply subqual_trans_qvar; [eassumption|].
    eapply subqual_trans; [|exact H].
    eapply safety_sq_weaken; [eassumption| |eassumption].
    intros y b Hy. apply HG. right; assumption.
  - apply wf_env_qua; eauto 2 with core_safety.
Qed.

Lemma safety_narrow_subt : forall E x Q P S T,
  transitivity_on_sub Q ->
  sub E P Q -> x `notin` dom E ->
  subqtype ((x,bind_sub Q)::E) S T ->
  subqtype ((x,bind_sub P)::E) S T.
Proof.
  intros E x Q P S T Htrans HQ Hx HT.
  pose proof (safety_sub_map_qtyp safety_identity {} safety_identity_closed
    (fun x _ => safety_identity_fixed x) _ _ _ HT ((x,bind_sub P)::E)) as HM.
  rewrite !safety_identity_qtyp in HM. apply HM.
  - apply safety_narrowing_morphism; intros G HG HW; simpl.
    assert (HB : binds x (bind_sub P) G) by (apply HG; left; reflexivity).
    rewrite safety_identity_typ. split; [eapply wf_typ_var; eassumption|].
    intros R H. eapply sub_trans_tvar; [eassumption|].
    eapply Htrans; [|exact H].
    eapply safety_sub_weaken_typ; [eassumption| |eassumption].
    intros y b Hy. apply HG. right; assumption.
  - apply wf_env_sub; eauto 2 with core_safety.
Qed.

Fixpoint safety_size_typ (T : typ) : nat :=
  match T with
  | typ_arrow U V | typ_sum U V | typ_pair U V => S (safety_size_qtyp U + safety_size_qtyp V)
  | typ_all U V => S (safety_size_typ U + safety_size_qtyp V)
  | typ_qall _ V | typ_ref V => S (safety_size_qtyp V)
  | _ => 0
  end
with safety_size_qtyp (U : qtyp) : nat :=
  match U with qtyp_qtyp _ T => safety_size_typ T end.

Lemma safety_size_open_t :
  (forall T k X, safety_size_typ (open_tt_rec k (typ_fvar X) T) = safety_size_typ T) /\
  (forall T k X, safety_size_qtyp (open_tqt_rec k (typ_fvar X) T) = safety_size_qtyp T).
Proof. apply safety_types_syntax; intros; simpl; destruct_tests; auto; congruence. Qed.
Lemma safety_size_open_q :
  (forall T k Q, safety_size_typ (open_qt_rec k Q T) = safety_size_typ T) /\
  (forall T k Q, safety_size_qtyp (open_qqt_rec k Q T) = safety_size_qtyp T).
Proof. apply safety_types_syntax; intros; simpl; auto; congruence. Qed.

Lemma safety_qtype_trans_from : forall Q,
  transitivity_on_sub (match Q with qtyp_qtyp _ T => T end) ->
  transitivity_on_subqtype Q.
Proof.
  intros [P Q] Htrans E S T HS HT.
  inversion HS; inversion HT; subst.
  constructor; [eapply subqual_trans; eassumption|eapply Htrans; eassumption].
Qed.

Local Ltac smaller_type smaller :=
  lazymatch goal with
  | |- transitivity_on_sub ?T =>
      apply (smaller (safety_size_typ T)); [|reflexivity]
  end.

Lemma safety_sub_trans : forall Q, transitivity_on_sub Q.
Proof.
  assert (Bound : forall n Q, safety_size_typ Q = n -> transitivity_on_sub Q).
  {
    induction n as [n Smaller] using lt_wf_ind.
    intros Q Hsize E S T HS HT.
    revert T HT Hsize.
    induction HS; intros Y HY Hsize;
      try solve [inversion HY; subst; eauto 4 with core_safety].
    all: try solve [eapply sub_trans_tvar; [eassumption|eapply IHHS; eassumption]].
    all: try solve [inversion HY; subst; apply sub_top; eauto 3 with core_safety].
    - inversion HY; subst.
      + apply sub_top; eauto 3 with core_safety.
      + apply sub_arrow.
        * eapply safety_qtype_trans_from with (Q := T1); [|eassumption|eassumption].
          smaller_type Smaller. destruct T1, T2; simpl in *; lia.
        * eapply safety_qtype_trans_from with (Q := T2); [|eassumption|eassumption].
          smaller_type Smaller. destruct T1, T2; simpl in *; lia.
    - inversion HY; subst.
      + apply sub_top; eauto 3 with core_safety.
      + eapply sub_all with (L := L `union` L0 `union` dom E).
        * assert (Hbound : transitivity_on_sub T1) by (smaller_type Smaller; simpl in *; lia).
          eapply Hbound; eassumption.
        * intros X HX.
          eapply safety_qtype_trans_from with (Q := open_tqt T2 X).
          -- smaller_type Smaller.
             destruct T2; change (safety_size_qtyp (open_tqt (qtyp_qtyp q t) X) <
               safety_size_typ (typ_all T1 (qtyp_qtyp q t)))%nat.
             unfold open_tqt. rewrite (proj2 safety_size_open_t). simpl; lia.
          -- eapply safety_narrow_subt with (Q := T1).
             ++ smaller_type Smaller; simpl in *; lia.
             ++ eassumption.
             ++ solve_notin.
             ++ apply H; solve_notin.
          -- match goal with Hbody : forall x : atom, _ -> subqtype _ _ _ |- _ =>
               solve [apply (Hbody X); solve_notin] end.
    - inversion HY; subst.
      + apply sub_top; eauto 3 with core_safety.
      + eapply sub_qall with (L := L `union` L0 `union` dom E).
        * eapply subqual_trans; eassumption.
        * intros X HX.
          eapply safety_qtype_trans_from with (Q := open_qqt T2 X).
          -- smaller_type Smaller.
             destruct T2; change (safety_size_qtyp (open_qqt (qtyp_qtyp q t) X) <
               safety_size_typ (typ_qall T1 (qtyp_qtyp q t)))%nat.
             unfold open_qqt. rewrite (proj2 safety_size_open_q). simpl; lia.
          -- eapply safety_narrow_subq with (Q := T1); [eassumption|solve_notin|].
             apply H0; solve_notin.
          -- match goal with Hbody : forall x : atom, _ -> subqtype _ _ _ |- _ =>
               solve [apply (Hbody X); solve_notin] end.
    - inversion HY; subst.
      + apply sub_top; eauto 3 with core_safety.
      + apply sub_sum.
        * eapply safety_qtype_trans_from with (Q := T1); [|eassumption|eassumption].
          smaller_type Smaller. destruct T1, T2; simpl in *; lia.
        * eapply safety_qtype_trans_from with (Q := T2); [|eassumption|eassumption].
          smaller_type Smaller. destruct T1, T2; simpl in *; lia.
    - inversion HY; subst.
      + apply sub_top; eauto 3 with core_safety.
      + apply sub_pair.
        * eapply safety_qtype_trans_from with (Q := T1); [|eassumption|eassumption].
          smaller_type Smaller. destruct T1, T2; simpl in *; lia.
        * eapply safety_qtype_trans_from with (Q := T2); [|eassumption|eassumption].
          smaller_type Smaller. destruct T1, T2; simpl in *; lia.
  }
  intro Q. eapply Bound; reflexivity.
Qed.

Definition safety_one_term (x : atom) u : safety_images :=
  {| safety_qua_image := qua_fvar; safety_typ_image := typ_fvar;
     safety_exp_image := fun y => if y == x then u else exp_fvar y |}.
Definition safety_one_type (x : atom) U : safety_images :=
  {| safety_qua_image := qua_fvar; safety_exp_image := exp_fvar;
     safety_typ_image := fun y => if y == x then U else typ_fvar y |}.
Definition safety_one_qua (x : atom) R : safety_images :=
  {| safety_typ_image := typ_fvar; safety_exp_image := exp_fvar;
     safety_qua_image := fun y => if y == x then R else qua_fvar y |}.

Lemma safety_one_term_fixed : forall x u y, y <> x -> safety_fixed (safety_one_term x u) y.
Proof. unfold safety_fixed; simpl; intros; destruct_tests; tauto. Qed.
Lemma safety_one_type_fixed : forall x U y, y <> x -> safety_fixed (safety_one_type x U) y.
Proof. unfold safety_fixed; simpl; intros; destruct_tests; tauto. Qed.
Lemma safety_one_qua_fixed : forall x R y, y <> x -> safety_fixed (safety_one_qua x R) y.
Proof. unfold safety_fixed; simpl; intros; destruct_tests; tauto. Qed.

Lemma safety_one_term_closed : forall x u, expr u -> safety_images_closed (safety_one_term x u).
Proof. unfold safety_images_closed; simpl; intros; destruct_tests; simpl; repeat split; auto using safety_expr_depth. Qed.
Lemma safety_one_type_closed : forall x U, type U -> safety_images_closed (safety_one_type x U).
Proof. unfold safety_images_closed; simpl; intros; destruct_tests; simpl; repeat split; auto using safety_typ_depth. Qed.
Lemma safety_one_qua_closed : forall x R, qual R -> safety_images_closed (safety_one_qua x R).
Proof. unfold safety_images_closed; simpl; intros; destruct_tests; simpl; repeat split; auto using safety_qual_depth. Qed.

Definition safety_atoms_binding b :=
  match b with
  | bind_sub T => safety_atoms_typ T
  | bind_typ T => safety_atoms_qtyp T
  | bind_qua Q => safety_atoms_qua Q
  end.
Fixpoint safety_atoms_env (E : env) : atoms :=
  match E with
  | nil => {}
  | (x,b)::F => {{x}} `union` safety_atoms_binding b `union` safety_atoms_env F
  end.

Lemma safety_atoms_bound : forall E x b, binds x b E ->
  forall y, y `notin` safety_atoms_env E -> y <> x /\ y `notin` safety_atoms_binding b.
Proof.
  induction E as [|[z c] E IH]; intros x b Hb y Hf; simpl in *.
  - inversion Hb.
  - destruct Hb as [Hb|Hb].
    + inversion Hb; subst. split; solve_notin.
    + eapply IH; [eassumption|solve_notin].
Qed.

Lemma safety_morphism_single : forall m E x b,
  (forall y, y <> x -> safety_fixed m y) ->
  x `notin` safety_atoms_env E ->
  (forall G, safety_includes E G -> wf_env G -> safety_entry m G x b) ->
  safety_morphism m ((x,b)::E) E.
Proof.
  intros m E x b Hf Hx H G HI HW y d [HB|HB].
  - inversion HB; subst; auto.
  - destruct (safety_atoms_bound _ _ _ HB _ Hx) as [Hneq Hfresh].
    apply safety_entry_exact; [apply Hf; congruence|assumption|].
    assert (HA : safety_agrees m (safety_atoms_binding d)).
    { intros z Hz; apply Hf; congruence. }
    assert (Hd : safety_map_binding m d = d).
    { destruct d; simpl in *; f_equal;
        eauto using safety_map_fixed_q, safety_map_fixed_tu_t, safety_map_fixed_tu_u. }
    rewrite Hd. apply HI; assumption.
Qed.

Local Ltac use_fresh_map :=
  (apply safety_map_fixed_q || apply safety_map_fixed_tu_t || apply safety_map_fixed_tu_u ||
    apply safety_map_fixed_e);
  intros y Hy; (apply safety_one_term_fixed || apply safety_one_type_fixed ||
    apply safety_one_qua_fixed); intro; subst; solve_notin.

Local Ltac single_name :=
  cbn; destruct_tests; try contradiction; reflexivity.

Lemma safety_open_ee_typing : forall E Q e U V v A,
  typing E `pure v V ->
  (forall x, x `notin` A -> typing ((x,bind_typ V)::E) Q (open_ee e x) U) ->
  typing E Q (open_ee e v) U.
Proof.
  intros E Q e U V v A Hv H.
  fresh_atom x (A `union` safety_atoms_env E `union` safety_atoms_exp e `union`
    safety_atoms_qua Q `union` safety_atoms_qtyp U `union` safety_atoms_qtyp V).
  set (m := safety_one_term x v).
  assert (HC : safety_images_closed m) by (apply safety_one_term_closed; eapply safety_typing_expr; eassumption).
  assert (HF : forall y, y `notin` {{x}} -> safety_fixed m y)
    by (intros; apply safety_one_term_fixed; solve_notin).
  assert (HM : safety_morphism m ((x,bind_typ V)::E) E).
  { apply safety_morphism_single; [apply safety_one_term_fixed|solve_notin|].
    intros G HI HW. simpl.
    assert (HV : safety_map_qtyp m V = V) by (unfold m; use_fresh_map).
    rewrite HV. destruct (x == x) as [_|Hneq]; [|contradiction].
    eapply safety_typing_weaken; [exact Hv|exact HI|exact HW]. }
  pose proof (safety_typing_map m {{x}} HC HF _ _ _ _ (H x ltac:(solve_notin))
    E HM (safety_typing_env _ _ _ _ Hv)) as HT.
  assert (HQ : safety_map_qua m Q = Q) by (unfold m; use_fresh_map).
  assert (HU : safety_map_qtyp m U = U) by (unfold m; use_fresh_map).
  assert (He : safety_map_exp m e = e) by (unfold m; use_fresh_map).
  unfold open_ee in HT. rewrite safety_map_open_e_e, HQ, HU, He in HT by assumption.
  change (typing E Q (open_ee e (safety_exp_image m x)) U) in HT.
  replace (safety_exp_image m x) with v in HT by (unfold m; single_name).
  exact HT.
Qed.

Lemma safety_one_type_morphism : forall E x A V,
  x `notin` (safety_atoms_env E `union` safety_atoms_typ A) ->
  sub E V A ->
  safety_morphism (safety_one_type x V) ((x,bind_sub A)::E) E.
Proof.
  intros E x A V Hx HV.
  apply safety_morphism_single; [apply safety_one_type_fixed|solve_notin|].
  intros G HI HW. simpl.
  assert (HA : safety_map_typ (safety_one_type x V) A = A) by use_fresh_map.
  rewrite HA. replace (if x == x then V else typ_fvar x) with V by single_name.
  assert (HS : sub G V A) by (eapply safety_sub_weaken_typ; eassumption).
  split; [eapply safety_sub_left; eassumption|].
  intros; eapply safety_sub_trans; eassumption.
Qed.

Lemma safety_one_qua_morphism : forall E x A R,
  x `notin` (safety_atoms_env E `union` safety_atoms_qua A) ->
  subqual E R A ->
  safety_morphism (safety_one_qua x R) ((x,bind_qua A)::E) E.
Proof.
  intros E x A V Hx HV.
  apply safety_morphism_single; [apply safety_one_qua_fixed|solve_notin|].
  intros G HI HW. simpl.
  assert (HA : safety_map_qua (safety_one_qua x V) A = A) by use_fresh_map.
  rewrite HA. replace (if x == x then V else qua_fvar x) with V by single_name.
  assert (HS : subqual G V A) by (eapply safety_sq_weaken; eassumption).
  split; [eapply safety_sq_left; eassumption|].
  intros; eapply subqual_trans; eassumption.
Qed.

Local Ltac instantiation_setup dim x A E V B :=
  let m := fresh "m" in let HC := fresh "Closed" in let HF := fresh "Fixed" in
  let HM := fresh "Morphism" in
  lazymatch dim with
  | true =>
    set (m := safety_one_type x V);
    assert (HC : safety_images_closed m) by
      (apply safety_one_type_closed; eapply safety_wf_typ_lc, safety_sub_left; eassumption);
    assert (HF : forall y, y `notin` {{x}} -> safety_fixed m y) by
      (intros; apply safety_one_type_fixed; solve_notin);
    assert (HM : safety_morphism m ((x,bind_sub B)::E) E) by
      (apply safety_one_type_morphism; [solve_notin|eassumption])
  | false =>
    set (m := safety_one_qua x V);
    assert (HC : safety_images_closed m) by
      (apply safety_one_qua_closed; eapply safety_wf_qua_lc, safety_sq_left; eassumption);
    assert (HF : forall y, y `notin` {{x}} -> safety_fixed m y) by
      (intros; apply safety_one_qua_fixed; solve_notin);
    assert (HM : safety_morphism m ((x,bind_qua B)::E) E) by
      (apply safety_one_qua_morphism; [solve_notin|eassumption])
  end.

Local Ltac instantiate_rewrite HC H :=
  unfold open_te, open_qe, open_tqt, open_qqt in H;
  repeat first [
    rewrite safety_map_open_t_e in H by exact HC
  | rewrite safety_map_open_q_e in H by exact HC
  | rewrite safety_map_open_t_tu_u in H by exact HC
  | rewrite safety_map_open_q_tu_u in H by exact HC ];
  repeat match type of H with
  | context [safety_map_typ ?m (typ_fvar ?x)] => change (safety_map_typ m (typ_fvar x)) with (safety_typ_image m x) in H
  | context [safety_map_qua ?m (qua_fvar ?x)] => change (safety_map_qua m (qua_fvar x)) with (safety_qua_image m x) in H
  end.

Lemma safety_open_te_typing : forall E Q e U V B A,
  sub E V B ->
  (forall x, x `notin` A -> typing ((x,bind_sub B)::E) Q (open_te e x) (open_tqt U x)) ->
  typing E Q (open_te e V) (open_tqt U V).
Proof.
  intros E Q e U V B A HV H.
  fresh_atom x (A `union` safety_atoms_env E `union` safety_atoms_exp e `union`
    safety_atoms_qua Q `union` safety_atoms_qtyp U `union` safety_atoms_typ B).
  instantiation_setup true x A E V B.
  pose proof (safety_typing_map m {{x}} Closed Fixed _ _ _ _ (H x ltac:(solve_notin))
    E Morphism (safety_sub_env _ _ _ HV)) as HT.
  instantiate_rewrite Closed HT.
  assert (HQ : safety_map_qua m Q = Q) by (unfold m; use_fresh_map).
  assert (HU : safety_map_qtyp m U = U) by (unfold m; use_fresh_map).
  assert (He : safety_map_exp m e = e) by (unfold m; use_fresh_map).
  assert (Hx : safety_typ_image m x = V) by (unfold m; single_name).
  rewrite HQ, HU, He, Hx in HT. exact HT.
Qed.

Lemma safety_open_qe_typing : forall E Q e U V B A,
  subqual E V B ->
  (forall x, x `notin` A -> typing ((x,bind_qua B)::E) Q (open_qe e x) (open_qqt U x)) ->
  typing E Q (open_qe e V) (open_qqt U V).
Proof.
  intros E Q e U V B A HV H.
  fresh_atom x (A `union` safety_atoms_env E `union` safety_atoms_exp e `union`
    safety_atoms_qua Q `union` safety_atoms_qtyp U `union` safety_atoms_qua B).
  instantiation_setup false x A E V B.
  pose proof (safety_typing_map m {{x}} Closed Fixed _ _ _ _ (H x ltac:(solve_notin))
    E Morphism (safety_sq_env _ _ _ HV)) as HT.
  instantiate_rewrite Closed HT.
  assert (HQ : safety_map_qua m Q = Q) by (unfold m; use_fresh_map).
  assert (HU : safety_map_qtyp m U = U) by (unfold m; use_fresh_map).
  assert (He : safety_map_exp m e = e) by (unfold m; use_fresh_map).
  assert (Hx : safety_qua_image m x = V) by (unfold m; single_name).
  rewrite HQ, HU, He, Hx in HT. exact HT.
Qed.

Lemma safety_open_tqt_sub : forall E S T V B A,
  sub E V B ->
  (forall x, x `notin` A -> subqtype ((x,bind_sub B)::E) (open_tqt S x) (open_tqt T x)) ->
  subqtype E (open_tqt S V) (open_tqt T V).
Proof.
  intros E S T V B A HV H.
  fresh_atom x (A `union` safety_atoms_env E `union` safety_atoms_qtyp S `union`
    safety_atoms_qtyp T `union` safety_atoms_typ B).
  instantiation_setup true x A E V B.
  pose proof (safety_sub_map_qtyp m {{x}} Closed Fixed _ _ _ (H x ltac:(solve_notin))
    E Morphism (safety_sub_env _ _ _ HV)) as HT.
  instantiate_rewrite Closed HT.
  assert (HS : safety_map_qtyp m S = S) by (unfold m; use_fresh_map).
  assert (HU : safety_map_qtyp m T = T) by (unfold m; use_fresh_map).
  assert (Hx : safety_typ_image m x = V) by (unfold m; single_name).
  rewrite HS, HU, Hx in HT. exact HT.
Qed.

Lemma safety_open_qqt_sub : forall E S T V B A,
  subqual E V B ->
  (forall x, x `notin` A -> subqtype ((x,bind_qua B)::E) (open_qqt S x) (open_qqt T x)) ->
  subqtype E (open_qqt S V) (open_qqt T V).
Proof.
  intros E S T V B A HV H.
  fresh_atom x (A `union` safety_atoms_env E `union` safety_atoms_qtyp S `union`
    safety_atoms_qtyp T `union` safety_atoms_qua B).
  instantiation_setup false x A E V B.
  pose proof (safety_sub_map_qtyp m {{x}} Closed Fixed _ _ _ (H x ltac:(solve_notin))
    E Morphism (safety_sq_env _ _ _ HV)) as HT.
  instantiate_rewrite Closed HT.
  assert (HS : safety_map_qtyp m S = S) by (unfold m; use_fresh_map).
  assert (HU : safety_map_qtyp m T = T) by (unfold m; use_fresh_map).
  assert (Hx : safety_qua_image m x = V) by (unfold m; single_name).
  rewrite HS, HU, Hx in HT. exact HT.
Qed.

Lemma safety_open_tqt_wf : forall E T V B A,
  sub E V B ->
  (forall x, x `notin` A -> wf_qtyp ((x,bind_sub B)::E) (open_tqt T x)) ->
  wf_qtyp E (open_tqt T V).
Proof.
  intros E T V B A HV H.
  eapply safety_sqt_left.
  eapply safety_open_tqt_sub with (A := A `union` dom E); [exact HV|].
  intros; apply safety_sub_refl_qtyp.
  - apply H; solve_notin.
  - apply wf_env_sub; eauto 2 with core_safety; solve_notin.
Qed.

Lemma safety_open_qqt_wf : forall E T V B A,
  subqual E V B ->
  (forall x, x `notin` A -> wf_qtyp ((x,bind_qua B)::E) (open_qqt T x)) ->
  wf_qtyp E (open_qqt T V).
Proof.
  intros E T V B A HV H.
  eapply safety_sqt_left.
  eapply safety_open_qqt_sub with (A := A `union` dom E); [exact HV|].
  intros; apply safety_sub_refl_qtyp.
  - apply H; solve_notin.
  - apply wf_env_qua; eauto 2 with core_safety; solve_notin.
Qed.

Local Ltac invert_wf_type :=
  repeat match goal with
  | H : wf_qtyp _ (qtyp_qtyp _ _) |- _ => invert H
  | H : wf_typ _ (typ_arrow _ _) |- _ => invert H
  | H : wf_typ _ (typ_all _ _) |- _ => invert H
  | H : wf_typ _ (typ_qall _ _) |- _ => invert H
  | H : wf_typ _ (typ_sum _ _) |- _ => invert H
  | H : wf_typ _ (typ_pair _ _) |- _ => invert H
  end.

Lemma safety_scopes_drop_term : forall E x V, safety_scopes ((x,bind_typ V)::E) E.
Proof.
  intros E x V y b [HB|HB] Hkind.
  - inversion HB; subst. exfalso; apply Hkind; reflexivity.
  - exists b; auto.
Qed.

Lemma safety_wf_qtyp_unbind : forall E x V T,
  wf_qtyp ((x,bind_typ V)::E) T -> wf_qtyp E T.
Proof. intros; eapply safety_wf_qtyp_scope; [eassumption|apply safety_scopes_drop_term]. Qed.

Lemma safety_typing_result : forall E Q e T, typing E Q e T -> wf_qtyp E T.
Proof.
  induction 1; try solve [eauto 3 with core_safety];
    try solve [invert_wf_type; eauto using safety_open_tqt_wf, safety_open_qqt_wf with core_safety].
  - exact (safety_wf_binding _ H _ _ H0).
  - body_environment.
    assert (wf_qua E P) by
      (eapply safety_qua_unbind; [eapply safety_typing_effect; exact Body|intros; discriminate]).
    constructor; [assumption|constructor; [assumption|]].
    eapply safety_wf_qtyp_unbind; eapply H0; eassumption.
  - body_environment.
    assert (wf_qua E P) by
      (eapply safety_qua_unbind; [eapply safety_typing_effect; exact Body|intros; discriminate]).
    constructor; [assumption|]. eapply wf_typ_all with (L := L); eauto.
  - body_environment.
    constructor; [assumption|]. eapply wf_typ_qall with (L := L); eauto.
  - fresh_atom x L.
    eapply safety_wf_qtyp_unbind. exact (H1 x n).
  - fresh_atom x L. eapply safety_wf_qtyp_unbind. exact (H1 x n).
Qed.

Local Hint Resolve safety_typing_result : core_safety.

Lemma safety_ctx_regular : forall E Q c T U, typing_ctx E Q c T U ->
  wf_env E /\ wf_qua E Q /\ wf_qtyp E T /\ wf_qtyp E U.
Proof.
  induction 1; split_facts;
    try solve [repeat split; eauto 3 with core_safety];
    try solve [invert_wf_type; repeat split; eauto 3 with core_safety].
  try solve [match goal with HT : typing _ _ _ (qtyp_qtyp _ (typ_arrow _ _)) |- _ =>
    apply safety_typing_result in HT; invert_wf_type; repeat split; assumption end].
  - body_environment. auto.
  - fresh_atom x L.
    destruct (safety_wf_cons _ _ _ (safety_typing_env _ _ _ _ (H1 x ltac:(assumption)))) as [_ [_ HW1]].
    destruct (safety_wf_cons _ _ _ (safety_typing_env _ _ _ _ (H2 x ltac:(assumption)))) as [_ [_ HW2]].
    repeat split; eauto 4 with core_safety.
Qed.

Lemma safety_ctx_input : forall E Q c T U, typing_ctx E Q c T U -> wf_qtyp E T.
Proof. intros; apply safety_ctx_regular in H; tauto. Qed.
Lemma safety_ctx_effect : forall E Q c T U, typing_ctx E Q c T U -> wf_qua E Q.
Proof. intros; apply safety_ctx_regular in H; tauto. Qed.

Lemma safety_qual_widen : forall E R P e A,
  typing E R e (qtyp_qtyp P A) ->
  forall Q, subqual E P Q -> typing E R e (qtyp_qtyp Q A).
Proof.
  intros E R P e A HT Q HS.
  apply safety_typing_result in HT as HW; inversion HW; subst.
  eapply typing_sub; [exact HT|constructor; eauto 3 with core_safety].
Qed.

Lemma safety_qual_concrete : forall E P t, wf_env E -> wf_qua E P ->
  concretize P = Some t ->
  subqual E P (abstractize t) /\ subqual E (abstractize t) P.
Proof.
  intros E P t HE HW HC.
  assert (HP : subqual E P P) by (apply safety_sq_refl; assumption).
  assert (Ht : subqual E (abstractize t) (abstractize t))
    by (apply subqual_lift_elem; [assumption|apply reflexive]).
  split.
  - eapply subqual_eval_elim; [exact HP|exact HC|exact Ht].
  - eapply subqual_eval_intro; [exact HP|exact HC|exact Ht].
Qed.

(* Restrict the continuation to the concrete effect of the function body. *)
Lemma safety_push_barrier : forall E P Q e t c T U,
  typing E P e T -> typing_ctx E Q c T U ->
  subqual E P Q -> concretize P = Some t ->
  typing_state E 〈 e | frame_barrier t :: c 〉 U.
Proof.
  intros E P Q e t c T U HT HC HS HP.
  destruct (safety_qual_concrete E P t (safety_sq_env _ _ _ HS) (safety_sq_left _ _ _ HS) HP)
    as [HPT HTP].
  eapply typing_step with (Q := abstractize t).
  - eapply typing_subqual; eassumption.
  - eapply typing_ctx_barrier with (Q := abstractize t) (s := t).
    + eapply typing_ctx_subqual; [exact HC|eapply subqual_trans; eassumption].
    + reflexivity.
    + apply reflexive.
Qed.

Local Ltac invert_intro_sub :=
  match goal with
  | HT : typing _ _ ?v (qtyp_qtyp ?P ?S), HS : sub _ ?S _ |- _ =>
    let Shape := fresh "Shape" in
    pose proof (safety_intro_shape _ _ _ _ HT I P S eq_refl) as Shape;
    destruct S; simpl in Shape; try contradiction;
    try solve [repeat lazymatch type of Shape with ex _ => destruct Shape as [? Shape] end;
      first [discriminate Shape | destruct Shape; discriminate]];
    invert HS
  end.

Lemma safety_apply_abs : forall E R f T, typing E R f T ->
  forall P V e F A B v, f = exp_abs P V e -> T = qtyp_qtyp F (typ_arrow A B) ->
  typing E R v A -> value v ->
  typing E P (open_ee e v) B.
Proof.
  induction 1; intros Tag Dom Body Qual A Res v HF HT HV Hval;
    inversion HF; inversion HT; subst; try clear HF; try clear HT;
    try solve [eapply safety_open_ee_typing; [eapply safety_value_pure; eassumption|eassumption]].
  - destruct S as [X SX]. invert H0.
    invert_intro_sub.
    eapply typing_sub.
    + eapply IHtyping; [reflexivity|reflexivity|eapply typing_sub; eassumption|eassumption].
    + eassumption.
  - eapply IHtyping; [reflexivity|reflexivity| |eassumption].
    eapply typing_subqual; [eapply safety_value_pure; eassumption|].
    apply subqual_bot; eauto 2 with core_safety.
Qed.

Lemma safety_apply_tabs : forall E R f T, typing E R f T ->
  forall P V e F A B U, f = exp_tabs P V e -> T = qtyp_qtyp F (typ_all A B) ->
  sub E U A -> typing E P (open_te e U) (open_tqt B U).
Proof.
  induction 1; intros Tag Dom Body Qual A Res Arg HF HT HV;
    inversion HF; inversion HT; subst; try clear HF; try clear HT;
    try solve [eapply safety_open_te_typing; eassumption].
  - destruct S as [X SX]. invert H0.
    invert_intro_sub.
    eapply typing_sub.
    + eapply IHtyping; [reflexivity|reflexivity|eapply safety_sub_trans; eassumption].
    + eapply safety_open_tqt_sub; eassumption.
  - eapply IHtyping; [reflexivity|reflexivity|assumption].
Qed.

Lemma safety_apply_qabs : forall E R f T, typing E R f T ->
  forall P V e F A B U, f = exp_qabs P V e -> T = qtyp_qtyp F (typ_qall A B) ->
  subqual E U A -> typing E P (open_qe e U) (open_qqt B U).
Proof.
  induction 1; intros Tag Dom Body Qual A Res Arg HF HT HV;
    inversion HF; inversion HT; subst; try clear HF; try clear HT;
    try solve [eapply safety_open_qe_typing; eassumption].
  - destruct S as [X SX]. invert H0.
    invert_intro_sub.
    eapply typing_sub.
    + eapply IHtyping; [reflexivity|reflexivity|eapply subqual_trans; eassumption].
    + eapply safety_open_qqt_sub; eassumption.
  - eapply IHtyping; [reflexivity|reflexivity|assumption].
Qed.

Lemma safety_elim_inl : forall E Q e T, typing E Q e T ->
  forall Tag P v A B, e = exp_inl Tag v -> T = qtyp_qtyp P (typ_sum A B) -> typing E Q v A.
Proof.
  induction 1; intros Tag Qual v A B He HT; inversion He; inversion HT; subst; try clear He; try clear HT;
    try assumption.
  - destruct S as [X SX]. invert H0.
    invert_intro_sub.
    eapply typing_sub; [eapply IHtyping; reflexivity|eassumption].
  - eapply typing_subqual; [eapply IHtyping; reflexivity|eassumption].
Qed.

Lemma safety_elim_inr : forall E Q e T, typing E Q e T ->
  forall Tag P v A B, e = exp_inr Tag v -> T = qtyp_qtyp P (typ_sum A B) -> typing E Q v B.
Proof.
  induction 1; intros Tag Qual v A B He HT; inversion He; inversion HT; subst; try clear He; try clear HT;
    try assumption.
  - destruct S as [X SX]. invert H0.
    invert_intro_sub.
    eapply typing_sub; [eapply IHtyping; reflexivity|eassumption].
  - eapply typing_subqual; [eapply IHtyping; reflexivity|eassumption].
Qed.

Lemma safety_elim_fst : forall E Q e T, typing E Q e T ->
  forall Tag P v w A B, e = exp_pair Tag v w -> T = qtyp_qtyp P (typ_pair A B) -> typing E Q v A.
Proof.
  induction 1; intros Tag Qual v w A B He HT; inversion He; inversion HT; subst; try clear He; try clear HT;
    try assumption.
  - destruct S as [X SX]. invert H0.
    invert_intro_sub.
    eapply typing_sub; [eapply IHtyping; reflexivity|eassumption].
  - eapply typing_subqual; [eapply IHtyping; reflexivity|eassumption].
Qed.

Lemma safety_elim_snd : forall E Q e T, typing E Q e T ->
  forall Tag P v w A B, e = exp_pair Tag w v -> T = qtyp_qtyp P (typ_pair A B) -> typing E Q v B.
Proof.
  induction 1; intros Tag Qual v w A B He HT; inversion He; inversion HT; subst; try clear He; try clear HT;
    try assumption.
  - destruct S as [X SX]. invert H0.
    invert_intro_sub.
    eapply typing_sub; [eapply IHtyping; reflexivity|eassumption].
  - eapply typing_subqual; [eapply IHtyping; reflexivity|eassumption].
Qed.

Definition safety_retag (v : exp) (P : qua) : exp :=
  match v with
  | exp_int _ i => exp_int P i
  | exp_abs _ V e => exp_abs P V e
  | exp_tabs _ V e => exp_tabs P V e
  | exp_qabs _ R e => exp_qabs P R e
  | exp_inl _ e => exp_inl P e
  | exp_inr _ e => exp_inr P e
  | exp_pair _ e1 e2 => exp_pair P e1 e2
  | _ => v
  end.

Lemma safety_retag_typed : forall E Q v T, typing E Q v T -> value v ->
  forall P R A, T = qtyp_qtyp R A -> subqual E (safety_tag v) P ->
  typing E Q (safety_retag v P) (qtyp_qtyp P A).
Proof.
  induction 1; intros Hv Tag Qual A HT HS; inversion HT; subst; try clear HT;
    try solve [inversion Hv]; simpl in *;
    try solve [eauto 3 with core_safety].
  - eapply typing_abs with (L := L).
    intros x Hx. specialize (H x Hx).
    eapply typing_subqual; [exact H|].
    eapply safety_sq_weaken; [exact HS|apply safety_includes_tail|eapply safety_typing_env; eassumption].
  - eapply typing_tabs with (L := L).
    intros x Hx. specialize (H x Hx).
    eapply typing_subqual; [exact H|].
    eapply safety_sq_weaken; [exact HS|apply safety_includes_tail|eapply safety_typing_env; eassumption].
  - eapply typing_qabs with (L := L); [eapply safety_sq_right; eassumption|].
    intros x Hx. specialize (H0 x Hx).
    eapply typing_subqual; [exact H0|].
    eapply safety_sq_weaken; [exact HS|apply safety_includes_tail|eapply safety_typing_env; eassumption].
  - destruct S as [X SX]. invert H0.
    eapply typing_sub; [eapply IHtyping; [assumption|reflexivity|exact HS]|].
    constructor; [eapply safety_sq_refl; eauto 2 with core_safety|eassumption].
Qed.

Lemma safety_retag_preserves : forall E Q v P A, typing E Q v (qtyp_qtyp P A) -> value v ->
  typing E Q (safety_retag v P) (qtyp_qtyp P A).
Proof.
  intros. eapply safety_retag_typed; [eassumption|eassumption|reflexivity|].
  eapply safety_value_tag; [eassumption|eassumption|reflexivity].
Qed.

Local Hint Resolve safety_ctx_input safety_ctx_effect : core_safety.

(* Move subsumption across the state-typing boundary before inverting a rule. *)
Local Ltac peel_focus :=
  match goal with
  | HT : typing _ _ ?e _, HC : typing_ctx _ _ _ _ _ |- _ =>
    let Eq := fresh "Focus" in
    remember e as ee eqn:Eq in HT;
    revert HC Eq;
    induction HT; intros HC Eq; inversion Eq; subst; try clear Eq;
    try match goal with IH : context[typing_state _ _ _] |- _ =>
      first [solve [eapply IH; [eapply typing_ctx_sub; eassumption|reflexivity]]
            |solve [eapply IH; [eapply typing_ctx_subqual; eassumption|reflexivity]]]
    end
  end.

Local Ltac peel_frame :=
  match goal with
  | HT : typing _ _ _ _, HC : typing_ctx _ _ (?f :: ?c) _ _ |- _ =>
    let Eq := fresh "Frame" in
    remember (f :: c) as cc eqn:Eq in HC;
    revert HT Eq;
    induction HC; intros HT Eq; inversion Eq; subst; try clear Eq;
    try match goal with IH : context[typing_state _ _ _] |- _ =>
      first [solve [eapply IH; [eapply typing_sub; eassumption|reflexivity]]
            |solve [eapply IH; [eapply typing_subqual; eassumption|reflexivity]]]
    end
  end.

Local Ltac finish_retag v :=
  match goal with
  | HT : typing ?E ?Q v (qtyp_qtyp ?P ?A), HC : typing_ctx ?E ?Q _ (qtyp_qtyp ?P ?A) _ |- _ =>
    assert (HV : value v) by
      (first [assumption
             | let HE := fresh in pose proof (safety_typing_expr _ _ _ _ HT) as HE;
               inversion HE; subst; constructor; assumption
             | solve [eauto 3 using safety_typing_expr with core_safety]]);
    eapply typing_step; [exact (safety_retag_preserves E Q v P A HT HV)|exact HC]
  end.

Lemma safety_exit_check : forall E Q v P R T c U,
  typing E Q v (qtyp_qtyp (qua_meet P R) T) ->
  typing_ctx E Q c (qtyp_qtyp P T) U ->
  typing_state E 〈 v | c 〉 U.
Proof.
  intros E Q v P R T c U HT HC.
  apply safety_typing_result in HT as HW. invert_wf_type.
  repeat match goal with H : wf_qua _ (qua_meet _ _) |- _ => invert H end.
  eapply typing_step; [eapply safety_qual_widen; [exact HT|]|exact HC].
  apply subqual_meet_eliml; [apply safety_sq_refl; eauto 2 with core_safety|assumption].
Qed.

Theorem preservation : forall E s s' U,
  typing_state E s U ->
  s --> s' ->
  typing_state E s' U.
Proof.
  intros E s s' U HT HS.
  destruct HS; inversion HT as [Environment Effect Focus Continuation Input Output Hfocus Hctx]; subst; try clear HT;
    first [peel_frame | peel_focus];
    try solve [eauto 4 with core_safety].
  all: try match goal with HT : typing _ _ ?v _ |- _ => solve [finish_retag v] end.
  all: try solve [eapply safety_exit_check; eassumption].
  - eapply typing_step; [eapply typing_subqual; [eassumption|]|eassumption].
    match goal with
    | HC : typing_ctx E ?R _ _ _, Hr : concretize ?R = Some ?b, He : ?t ≤ ?b |- _ =>
      destruct (safety_qual_concrete E R b ltac:(eauto 2 with core_safety)
        (safety_ctx_effect _ _ _ _ _ HC) Hr) as [_ HB];
      eapply subqual_trans; [apply subqual_lift_elem; eauto 2 with core_safety|exact HB]
    end.
  - pose proof (safety_typing_result _ _ _ _ Hfocus) as WF.
    invert_wf_type.
    eapply typing_step; [exact Hfocus|].
    eapply typing_ctx_tabs with (L := L); eassumption.
  - pose proof (safety_typing_result _ _ _ _ Hfocus) as WF.
    invert_wf_type.
    eapply typing_step; [exact Hfocus|].
    eapply typing_ctx_qabs with (L := L); eassumption.
  - eapply typing_step; [eassumption|].
    eapply typing_ctx_case with (L := L); [|eassumption|eassumption|eassumption].
    match goal with
    | HT : typing _ _ _ (qtyp_qtyp _ (typ_sum _ _)) |- _ =>
      apply safety_typing_result in HT; invert_wf_type; assumption
    end.
  - eapply typing_step; [eassumption|].
    match goal with
    | HT : typing _ _ _ (qtyp_qtyp _ (typ_pair _ _)) |- _ =>
      apply safety_typing_result in HT; invert_wf_type
    end.
    apply typing_ctx_first; assumption.
  - eapply typing_step; [eassumption|].
    match goal with
    | HT : typing _ _ _ (qtyp_qtyp _ (typ_pair _ _)) |- _ =>
      apply safety_typing_result in HT; invert_wf_type
    end.
    apply typing_ctx_second; assumption.
  - eapply safety_push_barrier.
    + eapply safety_apply_abs with (f := exp_abs Q V e1); [exact H3|reflexivity|reflexivity|exact Hfocus|exact H].
    + exact Hctx.
    + exact (safety_value_tag _ _ _ _ H3 H2 _ _ eq_refl).
    + exact H0.
  - pose proof (value_tabs _ _ _ (safety_typing_expr _ _ _ _ Hfocus)) as HV.
    eapply safety_push_barrier.
    + eapply safety_apply_tabs; [exact Hfocus|reflexivity|reflexivity|eassumption].
    + exact Hctx.
    + exact (safety_value_tag _ _ _ _ Hfocus HV _ _ eq_refl).
    + eassumption.
  - pose proof (value_qabs _ _ _ (safety_typing_expr _ _ _ _ Hfocus)) as HV.
    eapply safety_push_barrier.
    + eapply safety_apply_qabs; [exact Hfocus|reflexivity|reflexivity|eassumption].
    + exact Hctx.
    + exact (safety_value_tag _ _ _ _ Hfocus HV _ _ eq_refl).
    + eassumption.
  - eapply typing_step; [eapply safety_open_ee_typing; [eapply safety_value_pure; eassumption|eassumption]|eassumption].
  - eapply typing_step; [eapply safety_open_ee_typing; [eapply safety_value_pure; [eassumption|eapply safety_elim_inl; [eassumption|reflexivity|reflexivity]]|eassumption]|eassumption].
  - eapply typing_step; [eapply safety_open_ee_typing; [eapply safety_value_pure; [eassumption|eapply safety_elim_inr; [eassumption|reflexivity|reflexivity]]|eassumption]|eassumption].
  - eapply typing_step; [eapply safety_elim_fst; [eassumption|reflexivity|reflexivity]|eassumption].
  - eapply typing_step; [eapply safety_elim_snd; [eassumption|reflexivity|reflexivity]|eassumption].
  - eapply typing_step; [|eassumption].
    match goal with
    | HC : typing_ctx _ _ _ (qtyp_qtyp _ (typ_sum _ _)) _ |- _ =>
      apply safety_ctx_input in HC; invert_wf_type
    end.
    apply typing_inl; assumption.
  - eapply typing_step; [|eassumption].
    match goal with
    | HC : typing_ctx _ _ _ (qtyp_qtyp _ (typ_sum _ _)) _ |- _ =>
      apply safety_ctx_input in HC; invert_wf_type
    end.
    apply typing_inr; assumption.
  - eapply typing_step; [eapply safety_qual_widen; eassumption|constructor; eassumption].
  - eapply typing_step; [eapply safety_qual_widen; [eassumption|apply subqual_meet_intro]|].
    + eapply safety_sq_refl; eauto 2 with core_safety.
    + eassumption.
    + apply typing_ctx_check; eauto 2 with core_safety.
  - match goal with
    | HS : subqual E ?Q (qua_negate ?P), Hc : concretize ?P = Some ?t |- _ =>
      let HCn := fresh in assert (HCn : concretize (qua_negate P) = Some (negate t))
        by (simpl; now rewrite Hc);
      destruct (safety_qual_concrete E (qua_negate P) (negate t)
        (safety_sq_env _ _ _ HS) (safety_sq_right _ _ _ HS) HCn) as [Hn _]
    end.
    eapply typing_step; [eapply typing_subqual; [eassumption|apply subqual_meet_intro]|apply typing_ctx_without; eassumption].
    + eapply subqual_trans; eassumption.
    + eapply safety_sq_refl; eauto 2 with core_safety.
  - eapply typing_step; [eapply typing_subqual; [eassumption|]|eassumption].
    apply subqual_meet_elimr; [constructor|].
    apply safety_sq_refl; eauto 2 with core_safety.
  - eapply typing_step; [|eassumption].
    eapply typing_subqual; [apply typing_int; eauto 2 with core_safety|apply subqual_bot; eauto 2 with core_safety].
  - eapply typing_step; [eassumption|].
    eapply typing_ctx_if0; eauto 3 with core_safety.
    match goal with
    | HT : typing _ _ _ (qtyp_qtyp _ typ_int) |- _ =>
      apply safety_typing_result in HT; invert_wf_type; assumption
    end.
Qed.

Theorem progress : forall s U,
  typing_state empty s U ->
  done_state s \/ exists s', s --> s'.
Proof.
  intros s U Hs. inversion Hs; subst.
  match goal with
  | HT : typing empty _ _ _, HC : typing_ctx empty _ _ _ _ |- _ =>
    destruct (safety_progress_focus _ _ _ _ HT eq_refl _ _ HC) as [Hv|Hs'];
    [eapply safety_progress_value; eauto | now right]
  end.
Qed.
