Set Implicit Arguments.

Require Import LibExtra AbstractSyntax TypingMode GeneralTyping.

Require Import OperationalSemantics ConfigTyping MethodCall ConfigNotations.

Require Import HeapUpdate HeapCorrespondence TFree Deref.
Require Import Equivalence Indep EnvCorrespondence InertContext RecordTypes ConfigVarkinds.
From Stdlib Require Import Arith.Wf_nat Lia.

Local Definition frame_result (base : stack) (c : config) : Prop :=
  config_stack c = base /\ exists x, config_trm c = trm_var (avar_f x).

Local Lemma stack_suffix_refl s : stack_suffix s s.
Proof. exists stack_nil. reflexivity. Qed.

Local Lemma stack_suffix_push s f s' :
  stack_suffix s s' -> stack_suffix s (stack_cons f s').
Proof.
  intros [p ->]. exists (stack_cons f p). reflexivity.
Qed.

Local Lemma stack_suffix_pop s f s' :
  stack_suffix s (stack_cons f s') ->
  s = stack_cons f s' \/ stack_suffix s s'.
Proof.
  intros [p Hp]. destruct p.
  - left. symmetry. exact Hp.
  - right. inversion Hp. now exists p.
Qed.

Local Lemma frame_step s c c' :
  c ↦ c' ->
  stack_suffix s (config_stack c) ->
  frame_result s c \/ stack_suffix s (config_stack c').
Proof.
  intros Hstep Hsuffix.
  destruct Hstep; simpl in *; try (right; exact Hsuffix).
  - destruct (stack_suffix_pop Hsuffix) as [Heq | Htail].
    + left. split; [symmetry; exact Heq | exists x; reflexivity].
    + right. exact Htail.
  - right. now apply stack_suffix_push.
Qed.

Local Lemma reduction_frame_prefix c0 k c :
  c0 ⊣ k ↦* c ->
  (exists j c', j < k /\ c0 ⊣ j ↦* c' /\ frame_result (config_stack c0) c') \/
  stack_suffix (config_stack c0) (config_stack c).
Proof.
  intros Hred. induction Hred as [c0 | c0 c1 c2 k Hred IH Hstep].
  - right. apply stack_suffix_refl.
  - destruct IH as [[j [c' [Hj [Hreach Hresult]]]] | Hsuffix].
    + left. exists j, c'. split; [lia | now split].
    + destruct (frame_step Hstep Hsuffix) as [Hresult | Hnew].
      * left. exists k, c1. split; [lia | now split].
      * right. exact Hnew.
Qed.

(* The earliest return over all traces witnesses the universal stack condition. *)
Local Lemma frame_end_of_first_result c0 k c :
  c0 ⊣ k ↦* c ->
  frame_result (config_stack c0) c ->
  (forall j c', j < k -> c0 ⊣ j ↦* c' -> ~ frame_result (config_stack c0) c') ->
  frame_end_in c0 k c.
Proof.
  intros Hred [Hstack Hvar] Hfirst.
  split; [exact Hred |].
  split; [| now split].
  intros n cn Hn Hreach.
  destruct (reduction_frame_prefix Hreach) as [[j [cj [Hj [Hjreach Hresult]]]] | Hsuffix].
  - exfalso. apply (Hfirst j cj); [lia | exact Hjreach | exact Hresult].
  - exact Hsuffix.
Qed.

Local Lemma earliest_frame_end c0 k :
  (exists j c, j < k /\ c0 ⊣ j ↦* c /\ frame_result (config_stack c0) c) ->
  exists j c, frame_end_in c0 j c /\ j < k.
Proof.
  intros [j [c [Hjk [Hred Hresult]]]].
  revert c Hjk Hred Hresult.
  induction j using (well_founded_induction lt_wf).
  intros c Hjk Hred Hresult.
  destruct (classic (exists i ci, i < j /\ c0 ⊣ i ↦* ci /\ frame_result (config_stack c0) ci))
    as [[i [ci [Hij [Hreach Hres]]]] | Hnone].
  - eapply H; [exact Hij | lia | exact Hreach | exact Hres].
  - exists j, c. split; [| exact Hjk].
    eapply frame_end_of_first_result; eauto.
    intros i ci Hil Hreach Hres.
    apply Hnone. exists i, ci. auto.
Qed.

Local Lemma frame_within_unless_ended c0 k :
  (forall j c, j < k -> ~ frame_end_in c0 j c) ->
  frame_within c0 k.
Proof.
  intros Hno n c Hn Hred.
  destruct (reduction_frame_prefix Hred) as [Hbefore | Hsuffix]; [| exact Hsuffix].
  exfalso.
  destruct (earliest_frame_end Hbefore) as [j [cj [Hend Hj]]].
  apply (Hno j cj); [lia | exact Hend].
Qed.

(* Allocation preserves old bindings because freshness includes the heap domain. *)
Local Lemma reduction_no_old_update original c c' :
  c ↦ c' ->
  subheap_unchanged original (config_heap c) ->
  subheap_unchanged original (config_heap c') \/
  exists w a v y itm,
    config_trm c = trm_write (avar_f w) a (avar_f v) /\
    binds w y (config_env c) /\ binds y itm original.
Proof.
  intros Hred Hsub.
  destruct Hred; simpl in *; try (left; exact Hsub).
  - destruct (classic (exists itm, binds yObj itm original)) as [[itm Hbind] | Hnot].
    + right. exists wObj, m, wArg, yObj, itm. auto.
    + left. intros y itm Hbind.
      destruct H as [_ [_ [_ [Hother _]]]].
      apply Hother.
      * intros ->. apply Hnot. now exists itm.
      * apply Hsub. exact Hbind.
  - left. intros x itm Hbind.
    apply binds_push_neq.
    + now apply Hsub.
    + intros ->. simpl in H. destruct H as [Hfresh _].
      apply Hfresh. repeat rewrite in_union.
      pose proof (get_some_inv (Hsub _ _ Hbind)). tauto.
  - left. intros x itm Hbind.
    apply binds_push_neq.
    + now apply Hsub.
    + intros ->. simpl in H. destruct H as [Hfresh _].
      apply Hfresh. repeat rewrite in_union.
      pose proof (get_some_inv (Hsub _ _ Hbind)). tauto.
Qed.

Local Lemma old_heap_preserved_without_old_writes c0 k c :
  c0 ⊣ k ↦* c ->
  (forall j d w a v y itm,
    j < k ->
    c0 ⊣ j ↦* d ->
    config_trm d = trm_write (avar_f w) a (avar_f v) ->
    binds w y (config_env d) ->
    binds y itm (config_heap c0) ->
    False) ->
  subheap_unchanged (config_heap c0) (config_heap c).
Proof.
  intros Hred. induction Hred as [c0 | c0 c1 c2 k Hred IH Hstep]; intros Hsafe.
  - auto.
  - assert (Hsub : subheap_unchanged (config_heap c0) (config_heap c1)).
    { apply IH. intros j d w a v y itm Hj.
      apply (Hsafe j d w a v y itm). lia. }
    destruct (reduction_no_old_update Hstep Hsub) as [Hsub' | Hwrite].
    + exact Hsub'.
    + destruct Hwrite as (w & a & v & y & itm & Htrm & Henv & Hobj).
      exfalso. apply (Hsafe k c1 w a v y itm); auto.
Qed.

Local Lemma tfree_open_forward :
  (forall v t, tfree_trm v t -> forall n x, tfree_trm v (open_rec n x t)) /\
  (forall v l, tfree_lit v l -> forall n x, tfree_lit v (open_rec n x l)) /\
  (forall v d, tfree_def v d -> forall n x, tfree_def v (open_rec n x d)) /\
  (forall v ds, tfree_defs v ds -> forall n x, tfree_defs v (open_rec n x ds)).
Proof.
  apply tfree_mutind; intros; simpl; solve [constructor; auto].
Qed.

Local Lemma visible_in_pushed_context x G v vk T :
  ctx_vis (G § v / vk ~ T) x -> x = v \/ ctx_vis G x.
Proof. inversion 1; auto. Qed.

Local Lemma visible_method_variable mode G Go z r TZ TC v :
  mode_has_visibility mode ->
  ctx_vis (ctx_obj_met mode G Go z TZ r TC) v ->
  v = z \/ v = r.
Proof.
  intro Hmode. destruct Go; unfold ctx_obj_met; rewrite Hmode; intro H.
  all: destruct (visible_in_pushed_context H) as [-> | H']; [now right |].
  all: destruct (visible_in_pushed_context H') as [-> | H'']; [now left | inversion H''].
Qed.

Local Lemma visible_typed_variables mode :
  mode_has_visibility mode ->
  (forall G Go e t T, @ty_trm mode G Go e t T -> forall v, tfree_trm v t -> ctx_vis (G §§& Go) v) /\
  (forall G Go e l T, @ty_lit mode G Go e l T -> forall v, tfree_lit v l -> ctx_vis (G §§& Go) v) /\
  (forall G Go e d D, @ty_def mode G Go e d D -> forall v, tfree_def v d -> ctx_vis (G §§& Go) v) /\
  (forall G Go e ds T, @ty_defs mode G Go e ds T -> forall v, tfree_defs v ds -> ctx_vis (G §§& Go) v).
Proof.
  intro Hmode.
  destruct tfree_open_forward as [Htrm [Hlit [Hdef Hdefs]]].
  apply rules_mutind; intros; simpl in *;
    match goal with
    | H : tfree_trm _ _ |- _ => inversion H; subst; clear H
    | H : tfree_lit _ _ |- _ => inversion H; subst; clear H
    | H : tfree_def _ _ |- _ => inversion H; subst; clear H
    | H : tfree_defs _ _ |- _ => inversion H; subst; clear H
    end;
    try solve [eauto].
  all: try match goal with
  | H : tfree_trm ?v ?t,
    IH : forall x, x \notin ?L -> forall v, tfree_trm v (open x ?t) -> _ |- _ =>
    destruct (var_fresh (L \u \{v})) as [x Hfresh];
    apply notin_union in Hfresh as [Hx Hne];
    apply notin_singleton in Hne;
    specialize (IH x Hx v (Htrm v t H 0 x));
    destruct (visible_in_pushed_context IH) as [Heq | Hvis];
    [congruence | exact Hvis]
  end.
  all: try match goal with
  | H : tfree_defs ?v ?ds,
    IH : forall x, x \notin ?L -> forall v, tfree_defs v (open x ?ds) -> _ |- _ =>
    destruct (var_fresh (L \u \{v})) as [x Hfresh];
    apply notin_union in Hfresh as [Hx Hne];
    apply notin_singleton in Hne;
    specialize (IH x Hx v (Hdefs v ds H 0 x));
    destruct (visible_in_pushed_context IH) as [Heq | Hvis];
    [congruence | exact Hvis]
  end.
  all: try solve [eauto using tfree_trm_var, tfree_trm_read,
    tfree_trm_apply_l, tfree_trm_apply_r, tfree_trm_let_l, tfree_trm_let_r,
    tfree_trm_lit_l, tfree_trm_lit_r, tfree_trm_write_l, tfree_trm_write_r,
    tfree_trm_call_l, tfree_trm_call_r, tfree_defs_cons_l, tfree_defs_cons_r].
  - destruct (var_fresh (L \u \{v})) as [z Hz].
    destruct (var_fresh ((L \u \{v}) \u \{z})) as [r Hr].
    apply notin_union in Hz as [HzL Hzn].
    apply notin_union in Hr as [Hr Hvz].
    apply notin_union in Hr as [HrL Hrn].
    apply notin_singleton in Hzn, Hrn, Hvz.
    specialize (H z HzL r Hvz HrL v (Htrm v _ (Htrm v t H3 1 r) 0 z)).
    destruct ((@visible_method_variable mode G Go z r TZ TC v Hmode H)); congruence.
  - inversion H3.
Qed.

Local Lemma typed_method_has_no_free_term_variables mode G Go e m t D :
  mode_has_visibility mode ->
  @ty_def mode G Go e (def_met m t) D ->
  forall v, ~ tfree_trm v t.
Proof.
  intros Hmode Htyped v Hfree.
  inversion Htyped; subst.
  destruct (var_fresh (L \u \{v})) as [z Hz].
  destruct (var_fresh ((L \u \{v}) \u \{z})) as [r Hr].
  apply notin_union in Hz as [HzL Hzn].
  apply notin_union in Hr as [Hr Hvz].
  apply notin_union in Hr as [HrL Hrn].
  apply notin_singleton in Hzn, Hrn, Hvz.
  destruct tfree_open_forward as [Htrm _].
  match goal with
  | H : forall _ : var, _ |- _ => specialize (H z HzL r Hvz HrL)
  end.
  assert (Hscope : ctx_vis (ctx_obj_met mode G Go z TZ r TC) v).
  { eapply (proj1 (@visible_typed_variables mode Hmode) (ctx_obj_met mode G Go z TZ r TC) objctx_empty e); [eassumption |].
    apply Htrm. apply Htrm. exact Hfree. }
  destruct (@visible_method_variable mode G Go z r TZ TC v Hmode Hscope); congruence.
Qed.

Local Lemma typed_defs_member mode G Go e ds T d :
  @ty_defs mode G Go e ds T ->
  defs_has ds d ->
  exists D, @ty_def mode G Go e d D.
Proof.
  intros Htyped. induction Htyped; unfold defs_has in *; simpl; intro Heq.
  all: case_if.
  - injection Heq as ->. eauto.
  - injection Heq as ->. eauto.
  - eauto.
Qed.

Local Lemma heap_method_has_no_free_term_variables mode G e h y ds m t :
  mode_has_visibility mode ->
  @heap_correspond mode G e h ->
  binds y (item_obj ds) h ->
  defs_has ds (def_met m t) ->
  forall v, ~ tfree_trm v t.
Proof.
  intros Hmode [_ [_ [_ [_ [_ [_ [_ Hitems]]]]]]] Hbind Hhas.
  pose proof (Hitems y (get_some_inv Hbind)) as Hitem.
  inversion Hitem; subst.
  - match goal with H : binds y (item_fun _) h |- _ =>
      discriminate (binds_functional Hbind H)
    end.
  - match goal with H : binds y (item_obj ?ds') h |- _ =>
      tryif constr_eq ds ds' then fail else
      let Heq := fresh in
      pose proof (binds_functional Hbind H) as Heq; injection Heq as <-
    end.
    destruct (@typed_defs_member mode G (objctx_heap y U) e ds
      (open y U) (def_met m t) H2 Hhas) as [D Hdef].
    eapply typed_method_has_no_free_term_variables; eauto.
Qed.

Local Lemma opened_avar_free n x a v :
  open_rec n x a = avar_f v -> v = x \/ a = avar_f v.
Proof.
  destruct a; simpl.
  - case_if; intro H; inversion H; auto.
  - intro H. inversion H. auto.
Qed.

Local Lemma tfree_open_backward :
  (forall v t n x, tfree_trm v (open_rec n x t) -> v = x \/ tfree_trm v t) /\
  (forall v l n x, tfree_lit v (open_rec n x l) -> v = x \/ tfree_lit v l) /\
  (forall v d n x, tfree_def v (open_rec n x d) -> v = x \/ tfree_def v d) /\
  (forall v ds n x, tfree_defs v (open_rec n x ds) -> v = x \/ tfree_defs v ds).
Proof.
  enough (
    (forall t v n x, tfree_trm v (open_rec n x t) -> v = x \/ tfree_trm v t) /\
    (forall l v n x, tfree_lit v (open_rec n x l) -> v = x \/ tfree_lit v l) /\
    (forall d v n x, tfree_def v (open_rec n x d) -> v = x \/ tfree_def v d) /\
    (forall ds v n x, tfree_defs v (open_rec n x ds) -> v = x \/ tfree_defs v ds))
    by firstorder.
  apply trm_mutind; intros; cbn -[AvarOpenable] in *;
    match goal with
    | H : tfree_trm _ _ |- _ => inversion H; clear H; subst
    | H : tfree_lit _ _ |- _ => inversion H; clear H; subst
    | H : tfree_def _ _ |- _ => inversion H; clear H; subst
    | H : tfree_defs _ _ |- _ => inversion H; clear H; subst
    end.
  all: first [
    match goal with E : open_rec ?n ?x ?a = avar_f ?v |- _ =>
      destruct (@opened_avar_free n x a v E) as [-> | ->]; [now left | right; constructor]
    end |
    match goal with E : avar_f ?v = open_rec ?n ?x ?a |- _ =>
      destruct (@opened_avar_free n x a v (eq_sym E)) as [-> | ->]; [now left | right; constructor]
    end |
    match goal with IH : forall v n x, _ -> v = x \/ _, H : tfree_trm _ _ |- _ =>
      destruct (IH _ _ _ H); [now left | right; now constructor]
    end |
    match goal with IH : forall v n x, _ -> v = x \/ _, H : tfree_lit _ _ |- _ =>
      destruct (IH _ _ _ H); [now left | right; now constructor]
    end |
    match goal with IH : forall v n x, _ -> v = x \/ _, H : tfree_def _ _ |- _ =>
      destruct (IH _ _ _ H); [now left | right; now constructor]
    end |
    match goal with IH : forall v n x, _ -> v = x \/ _, H : tfree_defs _ _ |- _ =>
      destruct (IH _ _ _ H); [now left | right; now constructor]
    end].
Qed.

Local Lemma sef_call_body_variables mode G c c' w1 w2 m U :
  mode_has_sef mode ->
  mode_has_mutability mode ->
  @ty_config mode G c U ->
  config_trm c = trm_call (avar_f w1) m (avar_f w2) ->
  c ↦ c' ->
  forall v, tfree_trm v (config_trm c') -> v = w1 \/ v = w2.
Proof.
  intros Hsef Hmut Htyped Htrm Hred v Hfree.
  assert (Hmode : mode_has_visibility mode).
  { destruct mode; cbn in *; try discriminate; reflexivity. }
  destruct c as [t stk h e L]. simpl in Htrm. subst t.
  inversion Htyped; subst.
  inversion Hred; subst; simpl in Hfree.
  pose proof (proj1 tfree_open_backward) as Hopen.
  destruct (Hopen _ _ _ _ Hfree) as [-> | Houter]; [now right |].
  destruct (Hopen _ _ _ _ Houter) as [-> | Hbody]; [now left |].
  exfalso. eapply heap_method_has_no_free_term_variables; eauto.
Qed.

Local Lemma initial_call_heap c c' w1 m w2 :
  config_trm c = trm_call (avar_f w1) m (avar_f w2) ->
  c ↦ c' ->
  config_heap c' = config_heap c.
Proof.
  destruct c as [t stk h e L]. cbn. intros -> Hred.
  inversion Hred. reflexivity.
Qed.

Local Lemma initial_call_heap_upto_one c c' w1 m w2 k :
  config_trm c = trm_call (avar_f w1) m (avar_f w2) ->
  c ⊣ k ↦* c' ->
  k <= 1 ->
  config_heap c' = config_heap c.
Proof.
  intros Hcall Hred Hk. inversion Hred; subst; [reflexivity |].
  assert (n = 0) by lia. subst n.
  match goal with H : _ ⊣ 0 ↦* _ |- _ => inversion H; subst end.
  eapply initial_call_heap; eassumption.
Qed.

Local Lemma initial_call_write_prefix c k c' w1 m w2 :
  config_trm c = trm_call (avar_f w1) m (avar_f w2) ->
  c ⊣ k ↦* c' ->
  (forall j d, j < k -> ~ frame_end_in c j d) ->
  ~ subheap_unchanged (config_heap c) (config_heap c') ->
  exists j d w a v y itm,
    0 < j /\ j < k /\
    c ⊣ j ↦* d /\ frame_within c j /\
    config_trm d = trm_write (avar_f w) a (avar_f v) /\
    binds w y (config_env d) /\ binds y itm (config_heap c).
Proof.
  intros Hcall Hred Hnoend Hchanged.
  destruct (classic
    (exists j d w a v y itm,
       j < k /\ c ⊣ j ↦* d /\
       config_trm d = trm_write (avar_f w) a (avar_f v) /\
       binds w y (config_env d) /\ binds y itm (config_heap c)))
    as [(j & d & w & a & v & y & itm & Hj & Hprefix & Htrm & Henv & Hbind)
       | Hnowrite].
  - exists j, d, w, a, v, y. exists itm.
    assert (Hpos : 0 < j).
    { destruct j as [|j]; [|lia]. inversion Hprefix; subst.
      rewrite Hcall in Htrm. discriminate. }
    assert (Hwithin : frame_within c j).
    { apply frame_within_unless_ended. intros i d' Hi.
      apply (Hnoend i d'). lia. }
    auto 8.
  - exfalso. apply Hchanged. eapply old_heap_preserved_without_old_writes.
    + exact Hred.
    + intros j d w a v y itm Hj Hprefix Htrm Henv Hbind.
      apply Hnowrite. exists j, d, w, a, v, y. exists itm. auto.
Qed.

Local Lemma typed_write_receiver mode G Go e t U :
  @ty_trm mode G Go e t U ->
  mode_has_mutability mode ->
  forall x a y,
    t = trm_write (avar_f x) a (avar_f y) ->
    @ty_var mode G objctx_empty e x (typ_mut_marker typ_bot).
Proof.
  intros Htyped Hmode.
  induction Htyped; intros receiver field value Heq; try discriminate.
  - inversion Heq; subst. now apply H1.
  - eauto.
Qed.

Local Lemma typed_configuration_write_receiver mode G c U x a y :
  mode_has_mutability mode ->
  @ty_config mode G c U ->
  config_trm c = trm_write (avar_f x) a (avar_f y) ->
  @ty_var mode G objctx_empty (config_env c) x (typ_mut_marker typ_bot).
Proof.
  intros Hmode Hconfig Htrm. destruct Hconfig.
  simpl in *. eapply typed_write_receiver; eassumption.
Qed.

Local Lemma call_heap_preserved_with_readonly_prefixes mode c c' k w1 w2 m :
  mode_has_mutability mode ->
  config_trm c = trm_call (avar_f w1) m (avar_f w2) ->
  c ⊣ k ↦* c' ->
  (forall j d, 0 < j -> j < k -> c ⊣ j ↦* d -> frame_within c j ->
    exists G U,
      @ty_config mode G d U /\
      forall w y itm, tfree_trm w (config_trm d) ->
        binds w y (config_env d) ->
        binds y itm (config_heap c) ->
        ~ @ty_var mode G objctx_empty (config_env d) w (typ_mut_marker typ_bot)) ->
  (exists j d, frame_end_in c j d /\ j < k) \/
  subheap_unchanged (config_heap c) (config_heap c').
Proof.
  intros Hmode Hcall Hred Hinv.
  destruct (classic (exists j d, frame_end_in c j d /\ j < k)) as [Hend | Hnoend].
  - now left.
  - assert (Hbefore : forall j d, j < k -> ~ frame_end_in c j d).
    { intros j d Hj Hend. apply Hnoend. exists j, d. auto. }
    right.
    destruct (classic (subheap_unchanged (config_heap c) (config_heap c')))
      as [Hsame | Hchanged]; [exact Hsame |].
    exfalso.
    destruct (initial_call_write_prefix Hcall Hred Hbefore Hchanged)
      as (j & d & w & a & v & y & itm & Hpos & Hsmall & Hprefix & Hwithin & Htrm & Href & Hobj).
    destruct (Hinv j d Hpos Hsmall Hprefix Hwithin) as (G & U & Htyped & Hreadonly).
    assert (Hfree : tfree_trm w (config_trm d)).
    { rewrite Htrm. apply tfree_trm_write_l. }
    apply (Hreadonly w y itm Hfree Href Hobj).
    eapply typed_configuration_write_receiver; eassumption.
Qed.

Local Definition preserves_ctx_binds (G H : ctx) :=
  forall x T, ctx_binds x T G -> ctx_binds x T H.

Local Lemma preserves_ctx_binds_push G H x vk T :
  preserves_ctx_binds G H ->
  preserves_ctx_binds (G § x / vk ~ T) (H § x / vk ~ T).
Proof.
  intros Hkeep z U Hbind. inversion Hbind; subst.
  - constructor.
  - apply ctx_binds_n; auto.
Qed.

Local Lemma var_equivalence_extend e e' x y :
  @tyq_var e x y ->
  env_binds_more e e' ->
  @tyq_var e' x y.
Proof.
  intros H. induction H as [e x | e x y Hbind | e x y Heq IH | e x y z Hxy IHxy Hyz IHyz]; intros Hmore.
  - apply tyq_var_refl.
  - apply tyq_var_binds. now apply Hmore.
  - exact (@tyq_var_sym e' x y (IH Hmore)).
  - exact (@tyq_var_trans e' x y z (IHxy Hmore) (IHyz Hmore)).
Qed.

Local Lemma typ_equivalence_extend e e' S T :
  @tyq_typ e S T ->
  env_binds_more e e' ->
  @tyq_typ e' S T.
Proof.
  intro H. induction H; intro Hmore.
  - now apply tyq_typ_nulary.
  - apply tyq_typ_andor; unfold typing_equiv in *; auto.
  - apply tyq_typ_fun; unfold typing_equiv in *; auto.
  - apply tyq_typ_fld; unfold typing_equiv in *; auto.
  - apply tyq_typ_typ; unfold typing_equiv in *; auto.
  - apply tyq_typ_sel_normal. eapply var_equivalence_extend; eassumption.
  - apply tyq_typ_sel.
  - apply tyq_typ_bnd; unfold typing_equiv in *; auto.
  - apply tyq_typ_met; unfold typing_equiv in *; auto.
Qed.

Local Lemma variable_judgments_extend mode :
  (forall G Go e x T, @ty_var mode G Go e x T ->
    forall H e', preserves_ctx_binds G H -> env_binds_more e e' ->
    @ty_var mode H Go e' x T) /\
  (forall G Go e S T, @subtyp mode G Go e S T ->
    forall H e', preserves_ctx_binds G H -> env_binds_more e e' ->
    @subtyp mode H Go e' S T) /\
  (forall G Go e S T, @ty_incap mode G Go e S T ->
    forall H e', preserves_ctx_binds G H -> env_binds_more e e' ->
    @ty_incap mode H Go e' S T).
Proof.
  let extend :=
    unfold obj_typing, subtyping, obj_ref_incap, typing_equiv in *;
    eauto 8 using preserves_ctx_binds_push, typ_equivalence_extend
  in
  apply ts_mutind; intros;
  first [solve [constructor; extend] |
         solve [eapply ty_var_sub; extend] |
         solve [eapply ty_var_mut_top; extend] |
         solve [eapply subtyp_trans; extend] |
         solve [eapply subtyp_sel1; extend] |
         solve [eapply subtyp_sel2; extend] |
         solve [eapply subtyp_tyq; extend] |
         solve [eapply ty_incap_sel; extend] |
         solve [eapply subtyp_fun; extend] |
         solve [eapply subtyp_met; extend]].
Qed.

Local Lemma incap_output_admits_nocap mode G Go e S T :
  @ty_incap mode G Go e S T ->
  @subtyp mode G Go e typ_nocap T.
Proof.
  intro H. induction H; try solve [constructor | assumption | apply subtyp_and2; assumption | apply subtyp_nocap_fun; assumption].
  - eapply subtyp_trans; [exact IHty_incap | apply subtyp_or11].
Qed.

Local Lemma nocap_or_and mode G e S T :
  @subtyp mode G objctx_empty e
    (typ_and (typ_or typ_nocap S) (typ_or typ_nocap T))
    (typ_or typ_nocap (typ_and S T)).
Proof.
  eapply subtyp_trans; [apply subtyp_dist |].
  apply subtyp_or2.
  - eapply subtyp_trans; [apply subtyp_and12 | apply subtyp_or11].
  - eapply subtyp_trans.
    + apply subtyp_and2; [apply subtyp_and12 | apply subtyp_and11].
    + eapply subtyp_trans; [apply subtyp_dist |].
      apply subtyp_or2.
      * eapply subtyp_trans; [apply subtyp_and12 | apply subtyp_or11].
      * eapply subtyp_trans.
        -- apply subtyp_and2; [apply subtyp_and12 | apply subtyp_and11].
        -- apply subtyp_or12.
Qed.

Local Lemma cap_or_structural mode G e R C :
  @subtyp mode G objctx_empty e typ_top (typ_or typ_nocap C) ->
  @subtyp mode G objctx_empty e (typ_bnd R)
    (typ_or typ_nocap (typ_and (typ_bnd R) C)).
Proof.
  intro Hsplit.
  eapply subtyp_trans.
  - apply subtyp_and2; [apply subtyp_refl |].
    eapply subtyp_trans; [apply subtyp_top | exact Hsplit].
  - eapply subtyp_trans; [apply subtyp_dist |].
    apply subtyp_or2.
    + eapply subtyp_trans; [apply subtyp_and12 | apply subtyp_or11].
    + apply subtyp_or12.
Qed.

(* Keep the structural typing of an alias by allowing the nocap branch. *)
Local Lemma alias_variable_type_join mode G e x T :
  @ty_var mode G objctx_empty e x T ->
  forall G' e' w,
    mode_incap' mode = mode_incap_nocap ->
    preserves_ctx_binds G G' ->
    env_binds_more e e' ->
    @ty_var mode G' objctx_empty e' w typ_top ->
    (forall B, ctx_binds x B G ->
      @ty_var mode G' objctx_empty e' w (typ_or typ_nocap B)) ->
    (forall B, typ_indep_b 0 B ->
      @tyq_typ e' (open x B) (open w B) /\
      @tyq_typ e' (open w B) (open x B)) ->
    @ty_var mode G' objctx_empty e' w (typ_or typ_nocap T).
Proof.
  intro Htyping.
  induction Htyping as
    [G e x T Hctx
    | G e x T Hvar IH Hind Hincap
    | G e x T Hvar IH Hind
    | G e x T U Hvar1 IH1 Hvar2 IH2
    | G e x T U Hvar IH Hsub
    | G e x T Hmut Hvar IH];
    intros G' e' w Hmode Hctxmore Henvmore Htop Hbind Hopen.
  - now apply Hbind.
  - assert (Hhas : mode_has_incap mode) by (unfold mode_has_incap'; now rewrite Hmode).
    assert (Hnocap : @subtyp mode G' objctx_empty e' typ_nocap (open x T)).
    { eapply (proj1 (proj2 (variable_judgments_extend mode))); try eassumption.
      eapply incap_output_admits_nocap. now apply Hincap. }
    destruct (Hopen T Hind) as [Hforward _].
    assert (Hconvert : @subtyp mode G' objctx_empty e' (open x T) (open w T))
      by now apply subtyp_tyq.
    eapply ty_var_sub; [| apply subtyp_or12].
    apply ty_rec_intro; [|exact Hind|].
    + eapply ty_var_sub; [|exact Hconvert].
      eapply ty_var_sub; [apply IH; eassumption |].
      apply subtyp_or2; [exact Hnocap | apply subtyp_refl].
    + intros _. apply ty_incap_nocap; [exact Hmode |].
      eapply subtyp_trans; eassumption.
  - destruct (Hopen T Hind) as [_ Hback].
    eapply ty_var_sub; [|apply subtyp_or12].
    eapply ty_var_sub with (T := open w T); [|apply subtyp_tyq; exact Hback].
    apply ty_rec_elim; [|exact Hind].
    eapply ty_var_sub; [apply IH; eassumption |].
    apply subtyp_or2; [apply subtyp_nocap_bnd | apply subtyp_refl].
  - eapply ty_var_sub; [|apply nocap_or_and].
    apply ty_var_and; [apply IH1 | apply IH2]; eassumption.
  - eapply ty_var_sub; [apply IH; eassumption |].
    apply subtyp_or2; [apply subtyp_or11 |].
    eapply subtyp_trans; [|apply subtyp_or12].
    eapply (proj1 (proj2 (variable_judgments_extend mode))); eassumption.
  - eapply ty_var_sub; [|apply subtyp_or12].
    eapply ty_var_mut_top; eassumption.
Qed.

Local Lemma typ_transform_shift :
  (forall T f d s, transform_typ f T (d+s) =
    transform_typ (fun a q => f a (q+s)) T d) /\
  (forall D f d s, transform_dec f D (d+s) =
    transform_dec (fun a q => f a (q+s)) D d).
Proof.
  apply typ_mutind; intros; cbn; try reflexivity; f_equal; auto.
  all: match goal with
  | IH : forall _ _ _, _ = transform_typ _ ?T _ |- _ = transform_typ _ ?T ?q =>
    exact (IH f q s)
  end.
Qed.

Local Lemma typ_transform_open :
  (forall T f d k x, open_rec_typ (d+k) x (transform_typ f T d) =
    transform_typ (fun a i => open_rec (i+k) x (f a i)) T d) /\
  (forall D f d k x, open_rec_dec (d+k) x (transform_dec f D d) =
    transform_dec (fun a i => open_rec (i+k) x (f a i)) D d).
Proof.
  apply typ_mutind; intros; cbn; try reflexivity; f_equal; auto.
  all: match goal with
  | IH : forall _ _ _ _, _ = transform_typ _ ?T _ |- _ = transform_typ _ ?T ?q =>
    exact (IH f q k x)
  end.
Qed.

(* The openings agree except at occurrences of the selected binder. *)
Local Definition opening_agreement e n (f g : avar -> nat -> avar) :=
  (forall a d, a <> avar_b (n+d) -> f a d = g a d) /\
  (forall a d, f a d = g a d \/
     exists x y, f a d = avar_f x /\ g a d = avar_f y /\ @tyq_var e x y).

Local Lemma opening_agreement_shift e n s f g :
  opening_agreement e n f g ->
  opening_agreement e (n+s) (fun a d => f a (d+s)) (fun a d => g a (d+s)).
Proof.
  intros [Hsame Heq]. split.
  - intros a d Hne. apply Hsame. replace (n+(d+s)) with (n+s+d) by lia. exact Hne.
  - intros a d. apply Heq.
Qed.

Local Lemma opening_agreement_open e n f g k x :
  opening_agreement e n f g ->
  opening_agreement e n
    (fun a d => open_rec (d+k) x (f a d))
    (fun a d => open_rec (d+k) x (g a d)).
Proof.
  intros [Hsame Heq]. split.
  - intros a d Hne. now rewrite Hsame.
  - intros a d. destruct (Heq a d) as [-> | (u & v & -> & -> & Hequiv)].
    + now left.
    + right. exists u, v. auto.
Qed.

Local Lemma independent_type_transform v T :
  typ_indep v T ->
  match v with
  | avar_f _ => True
  | avar_b n => forall e f g, opening_agreement e n f g ->
      @tyq_typ e (transform_typ f T 0) (transform_typ g T 0)
  end.
Proof.
  intro Hind.
  induction Hind as
    [v T Hbase | v S T HS IHS HT IHT | v S T HS IHS HT IHT
    |v a S T HS IHS HT IHT | v A S T HS IHS HT IHT
    |n A S T HS IHS HT IHT
    |v S T HS IHS HT IHT | n S T HS IHS HT IHT
    |v a1 a2 A H1 H2 |v a1 a2 A H2
    |v T HT IH |n T HT IH
    |v C Z R m HC IHC HZ IHZ HR IHR
    |n C Z R m HC IHC HZ IHZ HR IHR].
  all: try (destruct v as [n|v]; [|exact I]).
  all: try solve [exact I].
  all: cbn [transform_typ transform_dec]; intros e f g Hfg.
  - inversion Hbase; constructor; constructor.
  - apply tyq_typ_andor; [constructor | apply IHS | apply IHT]; exact Hfg.
  - apply tyq_typ_andor; [constructor | apply IHS | apply IHT]; exact Hfg.
  - apply tyq_typ_fld; [apply IHS | apply IHT]; exact Hfg.
  - apply tyq_typ_typ; intro z;
      cbn [typing_equiv open_rec TypOpenable];
      rewrite !(proj1 typ_transform_shift _ _ 0 1);
      rewrite !(proj1 typ_transform_open _ _ 0 0 z);
      first [apply IHS | apply IHT]; apply opening_agreement_open;
      replace (Datatypes.S n) with (n+1) by lia;
      now apply opening_agreement_shift.
  - apply tyq_typ_fun.
    + now apply IHS.
    + intro z. cbn [typing_equiv open_rec TypOpenable].
      rewrite !(proj1 typ_transform_shift _ _ 0 1).
      rewrite !(proj1 typ_transform_open _ _ 0 0 z).
      apply IHT. apply opening_agreement_open.
      replace (Datatypes.S n) with (n+1) by lia. now apply opening_agreement_shift.
  - destruct Hfg as [Hsame _].
    rewrite (Hsame a1 0), (Hsame a2 0) by (replace (n+0) with n by lia; congruence).
    apply tyq_typ_sel.
  - destruct Hfg as [Hsame Halias].
    rewrite (Hsame a2 0) by (replace (n+0) with n by lia; congruence).
    destruct (Halias a1 0) as [-> | (x & y & -> & -> & Heq)].
    + apply tyq_typ_sel.
    + now apply tyq_typ_sel_normal.
  - apply tyq_typ_bnd. intro z. cbn [typing_equiv open_rec TypOpenable].
    rewrite !(proj1 typ_transform_shift _ _ 0 1).
    rewrite !(proj1 typ_transform_open _ _ 0 0 z).
    apply IH. apply opening_agreement_open.
    replace (Datatypes.S n) with (n+1) by lia. now apply opening_agreement_shift.
  - apply tyq_typ_met.
    + intro z. cbn [typing_equiv open_rec TypOpenable].
      rewrite !(proj1 typ_transform_shift _ _ 0 1).
      rewrite !(proj1 typ_transform_open _ _ 0 0 z).
      apply IHC. apply opening_agreement_open.
      replace (Datatypes.S n) with (n+1) by lia. now apply opening_agreement_shift.
    + now apply IHZ.
    + intros z r. cbn [typing_equiv open_rec TypOpenable].
      rewrite !(proj1 typ_transform_shift _ _ 0 2).
      rewrite !(proj1 typ_transform_open _ _ 0 1 r).
      rewrite !(proj1 typ_transform_open _ _ 0 0 z).
      apply IHR. do 2 apply opening_agreement_open.
      replace (Datatypes.S (Datatypes.S n)) with (n+2) by lia. now apply opening_agreement_shift.
Qed.

Local Lemma typ_transform_identity :
  (forall T d, transform_typ (fun a _ => a) T d = T) /\
  (forall D d, transform_dec (fun a _ => a) D d = D).
Proof. apply typ_mutind; intros; cbn; f_equal; auto. Qed.

Local Lemma aliased_open_type e x w T n :
  @tyq_var e x w ->
  typ_indep_b n T ->
  @tyq_typ e (open_rec n x T) (open_rec n w T).
Proof.
  intros Halias Hind. change (@tyq_typ e (open_rec_typ n x T) (open_rec_typ n w T)).
  rewrite <- (proj1 typ_transform_identity T 0).
  change (@tyq_typ e
    (open_rec_typ (0+n) x (transform_typ (fun a _ => a) T 0))
    (open_rec_typ (0+n) w (transform_typ (fun a _ => a) T 0))).
  rewrite !(proj1 typ_transform_open _ _ 0 _ _).
  apply (independent_type_transform Hind).
  split.
  - intros [i|z] d Hne; [|reflexivity].
    change ((If d+n = i then avar_f x else avar_b i) =
            (If d+n = i then avar_f w else avar_b i)).
    replace (d+n) with (n+d) by lia.
    case_if. congruence.
  - intros [i|z] d; [|now left].
    cbn [open_rec AvarOpenable].
    case_if.
    + right. exists x, w. auto.
    + now left.
Qed.

Local Lemma ctx_binding_unique G x S T :
  ctx_binds x S G -> ctx_binds x T G -> S = T.
Proof.
  intros Hbind. revert T.
  induction Hbind; intros U Hother; inversion Hother; subst; eauto; congruence.
Qed.

Local Lemma sef_top_cap_split mode G e B :
  mode_has_sef mode ->
  mode_has_mutability mode ->
  @subtyp mode G objctx_empty e typ_top (typ_or typ_nocap (typ_mut_marker B)).
Proof.
  destruct mode; cbn; intros Hsef Hmut; try discriminate;
    try solve [now apply subtyp_nocap_mut_top_boundless].
  all: eapply subtyp_trans; [now apply subtyp_nocap_mut_top_complement |].
  all: apply subtyp_or2; [apply subtyp_or11 |].
  all: eapply subtyp_trans; [apply subtyp_typ; intro z; [apply subtyp_refl | apply subtyp_bot] |].
  all: apply subtyp_or12.
Qed.

Local Lemma copy_alias_type mode G G' e e' x w R B T :
  mode_has_sef mode ->
  mode_has_mutability mode ->
  preserves_ctx_binds G G' ->
  env_binds_more e e' ->
  @tyq_var e' x w ->
  ctx_binds x (typ_and (typ_bnd R) (typ_mut_marker B)) G ->
  @ty_var mode G' objctx_empty e' w (typ_bnd R) ->
  @ty_var mode G objctx_empty e x T ->
  @subtyp mode G objctx_empty e typ_nocap T ->
  @ty_var mode G' objctx_empty e' w T.
Proof.
  intros Hsef Hmut Hkeep Henv Halias Hbind Hstruct Htyped Hnocap.
  eapply ty_var_sub.
  2: { apply subtyp_or2; [|apply subtyp_refl].
       eapply (proj1 (proj2 (variable_judgments_extend mode))); eassumption. }
  eapply alias_variable_type_join; try eassumption.
  - destruct mode; discriminate || reflexivity.
  - eapply ty_var_sub; [exact Hstruct | apply subtyp_top].
  - intros U HU. rewrite (ctx_binding_unique HU Hbind).
    eapply ty_var_sub; [exact Hstruct |].
    apply cap_or_structural. now apply sef_top_cap_split.
  - intros U Hind. split; apply aliased_open_type; auto.
    apply tyq_var_sym. exact Halias.
Qed.

Local Lemma ctx_binding_in_dom G x T :
  ctx_binds x T G -> x \in ctx_dom G.
Proof.
  induction 1; simpl.
  - rewrite in_union. now left; apply in_singleton_self.
  - rewrite in_union. now right.
  - exact IHctx_binds.
Qed.

Local Lemma fresh_readonly_alias_type mode G e x y w R B T :
  mode_has_sef mode ->
  mode_has_mutability mode ->
  ctx_binds x (typ_and (typ_bnd R) (typ_mut_marker B)) G ->
  binds x y e ->
  w §# G ->
  w # e ->
  @ty_var mode G objctx_empty e x T ->
  @subtyp mode G objctx_empty e typ_nocap T ->
  @ty_var mode (G § w / v_ref ~ typ_and (typ_bnd R) (typ_mut_marker typ_top))
    objctx_empty (e & w ~ y) w T.
Proof.
  intros Hsef Hmut Htype Hbind Hctxfresh Henvfresh Hvar Hnocap.
  eapply copy_alias_type; try eassumption.
  - intros z U Hz. apply ctx_binds_n; [|exact Hz].
    intros ->. apply Hctxfresh. now apply ctx_binding_in_dom in Hz.
  - intros loc ref Href. apply binds_push_neq; [exact Href |].
    intros ->. apply Henvfresh. now apply get_some_inv in Href.
  - eapply tyq_var_trans with (v2 := y).
    + apply tyq_var_binds. apply binds_push_neq; [exact Hbind |].
      intros ->. apply Henvfresh. now apply get_some_inv in Hbind.
    + apply tyq_var_sym, tyq_var_binds, binds_push_eq.
  - eapply ty_var_sub; [apply ty_var_var; constructor | apply subtyp_and11].
Qed.

Local Lemma ctx_binding_kind_in_dom G G' x k T :
  ctx_binds_k_after x k T G G' ->
  x \in ctx_kdom k G.
Proof.
  induction 1; simpl; case_if.
  - rewrite in_union. left. apply in_singleton_self.
  - rewrite in_union. now right.
  - assumption.
Qed.

Local Lemma inert_ref_binding_shape mode G G' x T :
  mode_has_mutability mode ->
  @inert mode G ->
  ctx_binds_k_after x v_ref T G G' ->
  exists R B,
    T = typ_and (typ_bnd R) (typ_mut_marker B) /\ ctx_binds x T G.
Proof.
  intros Hmode Hinert Hlookup.
  remember v_ref as kind in Hlookup.
  induction Hlookup; inversion Hinert; subst.
  - match goal with HT : @inert_typ mode _ v_ref |- _ => inversion HT; subst end.
    + match goal with Hfun : mode_has_fun mode |- _ => destruct mode; discriminate end.
    + match goal with Hcap : @refcap_inert_type mode _ v_ref |- _ =>
        assert (Hmut : mode_refcaps' mode = mode_refcaps_mutability)
          by (destruct mode; discriminate || reflexivity);
        unfold refcap_inert_type in Hcap; rewrite Hmut in Hcap;
        inversion Hcap; subst
      end.
      eexists _, _. split; [reflexivity | constructor].
  - destruct (IHHlookup ltac:(assumption) eq_refl) as (R & B & Heq & Hbind).
    exists R, B. split; [exact Heq | now apply ctx_binds_n].
Qed.

Local Lemma typed_config_ref_binding mode G c U x :
  mode_has_mutability mode ->
  @ty_config mode G c U ->
  tfree_trm x (config_trm c) ->
  exists y R B,
    binds x y (config_env c) /\
    ctx_binds x (typ_and (typ_bnd R) (typ_mut_marker B)) G.
Proof.
  intros Hmode Htyped Hfree. destruct Htyped. simpl in *.
  match goal with H : all_tfree_k G t v_ref |- _ =>
    destruct (H x Hfree) as (W & G' & Hlookup)
  end.
  destruct (inert_ref_binding_shape Hmode ltac:(eassumption) Hlookup)
    as (R & B & -> & Hctx).
  match goal with H : @heap_correspond mode G e Sigma |- _ =>
    destruct H as [_ [_ [_ [_ [_ [Hdom _]]]]]]
  end.
  pose proof (ctx_binding_kind_in_dom Hlookup) as Hmember.
  rewrite Hdom in Hmember. destruct (get_some Hmember) as [y Hbind].
  now exists y, R, B.
Qed.

Local Lemma typed_config_copy_readonly_reference mode G c U x w T :
  mode_has_sef mode ->
  mode_has_mutability mode ->
  @ty_config mode G c U ->
  tfree_trm x (config_trm c) ->
  w §# G ->
  w # (config_env c) ->
  @ty_var mode G objctx_empty (config_env c) x T ->
  @subtyp mode G objctx_empty (config_env c) typ_nocap T ->
  exists y R,
    binds x y (config_env c) /\
    @ty_var mode (G § w / v_ref ~ typ_and (typ_bnd R) (typ_mut_marker typ_top))
      objctx_empty (config_env c & w ~ y) w T.
Proof.
  intros Hsef Hmut Hconfig Hfree Hctxfresh Henvfresh Hvar Hnocap.
  destruct (typed_config_ref_binding Hmut Hconfig Hfree)
    as (y & R & B & Hbind & Hctx).
  exists y, R. split; [exact Hbind |].
  eapply fresh_readonly_alias_type; eassumption.
Qed.

Local Definition includes_context_types mode e (G H : ctx) :=
  forall x T, ctx_binds x T G -> @ty_var mode H objctx_empty e x T.

Local Lemma binds_preserved_by_fresh_push G x k T :
  x §# G -> preserves_ctx_binds G (G § x / k ~ T).
Proof.
  intros Hfresh y U Hbind. apply ctx_binds_n; [|exact Hbind].
  intros ->. apply Hfresh. now apply ctx_binding_in_dom in Hbind.
Qed.

Local Lemma includes_context_types_push mode e G H x k T :
  x §# H ->
  @includes_context_types mode e G H ->
  @includes_context_types mode e (G § x / k ~ T) (H § x / k ~ T).
Proof.
  intros Hfresh Hinclude y U Hbind. inversion Hbind; subst.
  - apply ty_var_var. constructor.
  - eapply (proj1 (variable_judgments_extend mode)).
    + now apply Hinclude.
    + now apply binds_preserved_by_fresh_push.
    + auto.
Qed.

(* The new context may derive each old binding at its original type. *)
Local Lemma variable_judgments_narrow mode :
  (forall G Go e x T, @ty_var mode G Go e x T ->
    forall H e', @includes_context_types mode e' G H -> env_binds_more e e' ->
    @ty_var mode H Go e' x T) /\
  (forall G Go e S T, @subtyp mode G Go e S T ->
    forall H e', @includes_context_types mode e' G H -> env_binds_more e e' ->
    @subtyp mode H Go e' S T) /\
  (forall G Go e S T, @ty_incap mode G Go e S T ->
    forall H e', @includes_context_types mode e' G H -> env_binds_more e e' ->
    @ty_incap mode H Go e' S T).
Proof.
  let narrow :=
    unfold obj_typing, subtyping, obj_ref_incap, typing_equiv in *;
    eauto 8 using typ_equivalence_extend
  in
  apply ts_mutind; intros;
  try first [solve [eapply ty_var_sub; narrow] |
             solve [eapply ty_var_mut_top; narrow] |
             solve [eapply subtyp_trans; narrow] |
             solve [eapply subtyp_sel1; narrow] |
             solve [eapply subtyp_sel2; narrow] |
             solve [eapply subtyp_tyq; narrow] |
             solve [eapply ty_incap_sel; narrow] |
             solve [constructor; narrow]].
  - unfold includes_context_types in *. eauto.
  - eapply subtyp_fun with (L := L \u ctx_dom H1); try eassumption.
    + eapply H; eassumption.
    + intros x Hfresh. apply notin_union in Hfresh as [HxL Hx].
      eapply H0; [exact HxL | | eassumption].
      now apply includes_context_types_push.
  - eapply subtyp_met with (L := L \u ctx_dom H2); try eassumption.
    + eapply H; eassumption.
    + intros x Hfresh. apply notin_union in Hfresh as [HxL Hx].
      eapply H0; [exact HxL | | eassumption].
      now apply includes_context_types_push.
    + intros x Hxf y Hyx Hyf.
      apply notin_union in Hxf as [HxL Hx].
      apply notin_union in Hyf as [HyL Hy].
      eapply H1; try eassumption.
      apply includes_context_types_push.
      * simpl. apply notin_union. split; [now apply notin_singleton | exact Hy].
      * now apply includes_context_types_push.
Qed.

Local Definition context_narrows mode e G H :=
  @includes_context_types mode e G H /\
  forall x, ctx_vis G x -> ctx_vis H x.

Local Lemma context_narrows_push mode e G H x k T :
  x §# H ->
  @context_narrows mode e G H ->
  @context_narrows mode e (G § x / k ~ T) (H § x / k ~ T).
Proof.
  intros Hfresh [Htypes Hvis]. split.
  - now apply includes_context_types_push.
  - intros y Hy. inversion Hy; subst; constructor; auto.
Qed.

Local Lemma context_narrows_hide mode e G H :
  @context_narrows mode e G H ->
  @context_narrows mode e (ctx_hide G) (ctx_hide H).
Proof.
  intros [Hkeep Hvis]. split.
  - intros x T Hb. inversion Hb; subst.
    eapply (proj1 (variable_judgments_extend mode)).
    + eapply Hkeep; eassumption.
    + intros y U Hy. now apply ctx_binds_hide.
    + auto.
  - inversion 1.
Qed.

Local Definition objctx_fresh_for (H : ctx) (Go : objctx) :=
  match Go with
  | objctx_lit x _ => x §# H
  | _ => True
  end.

Local Lemma context_narrows_under_objctx mode e G H Go :
  @context_narrows mode e G H ->
  objctx_fresh_for H Go ->
  @context_narrows mode e (G §§& Go) (H §§& Go).
Proof.
  destruct Go; simpl; intros; auto. now apply context_narrows_push.
Qed.

Local Lemma context_narrows_under_method mode e G H Go z r TZ TC :
  @context_narrows mode e G H ->
  objctx_fresh_for H Go ->
  z §# (H §§& Go) ->
  r §# (H §§& Go) ->
  r <> z ->
  @context_narrows mode e (ctx_obj_met mode G Go z TZ r TC)
    (ctx_obj_met mode H Go z TZ r TC).
Proof.
  intros Hnarrow Hself Hz Hr Hneq.
  pose proof (context_narrows_under_objctx Go Hnarrow Hself) as Hobj.
  destruct Go; unfold ctx_obj_met; simpl in *; destruct (mode_visibility' mode).
  all: apply context_narrows_push;
    [simpl; apply notin_union; split; [now apply notin_singleton | exact Hr] |].
  all: apply context_narrows_push; [exact Hz |].
  all: auto using context_narrows_hide.
Qed.

Local Lemma cap_bound_narrows mode C G Go e S T :
  @ty_capbnd mode C G Go e S T ->
  forall H e', @includes_context_types mode e' G H -> env_binds_more e e' ->
  @ty_capbnd mode C H Go e' S T.
Proof.
  intro H. induction H; intros Hnew e' Hkeep Henv;
    try solve [constructor; unfold obj_cap_bnd in *; eauto].
  eapply ty_capbnd_sel.
  - eapply (proj1 (variable_judgments_narrow mode)); eassumption.
  - eapply IHty_capbnd; eassumption.
Qed.

Local Lemma viewpoint_narrows mode x G Go e S T :
  @viewpoint_adapt mode x G Go e S T ->
  forall H e', @includes_context_types mode e' G H -> env_binds_more e e' ->
  @viewpoint_adapt mode x H Go e' S T.
Proof.
  unfold viewpoint_adapt. destruct (mode_viewpoint_adaptation' mode); [auto |].
  intros Hv H e' Hkeep Henv. inversion Hv; subst.
  apply viewpoint_adapt_cap_strip_combine.
  - eapply (proj2 (proj2 (variable_judgments_narrow mode))); eassumption.
  - eapply cap_bound_narrows; eassumption.
Qed.

Local Lemma visible_variable_narrows mode e G H x :
  @context_narrows mode e G H ->
  vis_var mode G x ->
  vis_var mode H x.
Proof. intros [_ Hvis] Hx Hmode. auto. Qed.

Local Lemma type_binding_narrows mode G H e e' x T :
  @context_narrows mode e' G H ->
  env_binds_more e e' ->
  @ty_var mode G objctx_empty e x T ->
  @ty_var mode H objctx_empty e' x T.
Proof. intros [Hkeep _] Henv Hv. eapply (proj1 (variable_judgments_narrow mode)); eassumption. Qed.

Local Lemma subtype_narrows mode G H e e' S T :
  @context_narrows mode e' G H ->
  env_binds_more e e' ->
  @subtyp mode G objctx_empty e S T ->
  @subtyp mode H objctx_empty e' S T.
Proof.
  intros [Hkeep _] Henv Hsub.
  eapply (proj1 (proj2 (variable_judgments_narrow mode))); eassumption.
Qed.

Local Ltac finish_narrowing :=
  unfold obj_typing, obj_dec_typing, subtyping in *;
  eauto 6 using visible_variable_narrows, type_binding_narrows,
    subtype_narrows, context_narrows_under_objctx.

Local Lemma term_judgments_narrow mode :
  (forall G Go e t T, @ty_trm mode G Go e t T ->
    forall H e', @context_narrows mode e' G H ->
      objctx_fresh_for H Go -> env_binds_more e e' ->
      @ty_trm mode H Go e' t T) /\
  (forall G Go e l T, @ty_lit mode G Go e l T ->
    forall H e', @context_narrows mode e' G H ->
      objctx_fresh_for H Go -> env_binds_more e e' ->
      @ty_lit mode H Go e' l T) /\
  (forall G Go e d D, @ty_def mode G Go e d D ->
    forall H e', @context_narrows mode e' G H ->
      objctx_fresh_for H Go -> env_binds_more e e' ->
      @ty_def mode H Go e' d D) /\
  (forall G Go e ds T, @ty_defs mode G Go e ds T ->
    forall H e', @context_narrows mode e' G H ->
      objctx_fresh_for H Go -> env_binds_more e e' ->
      @ty_defs mode H Go e' ds T).
Proof.
  apply rules_mutind; intros;
    try first
      [ solve [eapply ty_trm_var; finish_narrowing]
      | solve [eapply ty_trm_apply; finish_narrowing]
      | solve [eapply ty_trm_write; finish_narrowing]
      | solve [eapply ty_trm_call; finish_narrowing]
      | solve [eapply ty_trm_sub; finish_narrowing]
      | solve [eapply ty_def_fld; finish_narrowing]
      | solve [eapply ty_defs_one; finish_narrowing]
      | solve [eapply ty_defs_cons; finish_narrowing] ].
  all: try match goal with
  | |- @ty_trm _ _ _ _ (trm_read _ _) _ =>
      eapply ty_trm_read; [finish_narrowing | finish_narrowing |];
      eapply viewpoint_narrows; try eassumption;
      match goal with Hn : context_narrows _ _ _ _ |- _ => exact (proj1 Hn) end
  end.
  all: try match goal with
  | |- @ty_def _ _ _ _ (def_typ _ _) _ =>
      eapply ty_def_typ with (L := L);
      intros z Hz; eapply typ_equivalence_extend; unfold typing_equiv in *; eauto
  end.
  all: try match goal with
  | |- @ty_trm _ ?Gnew _ _ (trm_let _ _) _ =>
      eapply ty_trm_let with (L := L \u ctx_dom Gnew); [finish_narrowing|]
  | |- @ty_trm _ ?Gnew _ _ (trm_lit _ _) _ =>
      eapply ty_trm_lit with (L := L \u ctx_dom Gnew); [finish_narrowing|]
  | |- @ty_lit _ ?Gnew _ _ (lit_fun _ _) _ =>
      eapply ty_lit_fun with (L := L \u ctx_dom Gnew); [assumption|]
  end.
  all: try (intros z Hfresh; apply notin_union in Hfresh as [HzL Hz];
            unfold obj_typing in *;
            eauto 8 using context_narrows_push, I).
  all: try match goal with
  | |- @ty_lit _ ?Gnew _ _ (lit_obj _ _) _ =>
      eapply ty_lit_obj with (L := L \u ctx_dom Gnew); [|assumption];
      intros z Hfresh; apply notin_union in Hfresh as [HzL Hz];
      unfold obj_typing in *; eauto
  end.
  all: try match goal with
  | |- @ty_def _ ?Gnew ?Go _ (def_met _ _) _ =>
      eapply ty_def_met with (L := L \u ctx_dom (Gnew §§& Go));
      intros z Hz r Hneq Hr;
      apply notin_union in Hz as [HzL Hz];
      apply notin_union in Hr as [HrL Hr];
      unfold obj_typing in *;
      eapply H; [exact HzL | exact Hneq | exact HrL | | exact I | assumption];
      apply context_narrows_under_method; assumption
  end.
Qed.

(* Retype the opened body with typed references for the two method binders. *)
Local Lemma opened_heap_method_typing mode G e y R m body TC TZ TR :
  mode_has_visibility mode ->
  typ_indep_b 0 R ->
  @ty_def mode G (objctx_heap y R) e (def_met m body) (dec_met m TC TZ TR) ->
  exists L,
    forall G' e' z r,
      z \notin L -> r \notin L -> r <> z ->
      preserves_ctx_binds G G' -> env_binds_more e e' ->
      ctx_vis G' z -> ctx_vis G' r ->
      @tyq_var e' r y ->
      @ty_var mode G' objctx_empty e' z TZ ->
      @ty_var mode G' objctx_empty e' r (open z TC) ->
      @ty_var mode G' objctx_empty e' r (typ_bnd R) ->
      @ty_trm mode G' objctx_empty e' (open_met z r body) (open_met z r TR).
Proof.
  intros Hmode Hind Hdef. inversion Hdef; subst.
  exists L.
  intros G' e' z r Hz Hr Hneq Hkeep Henv Hzvis Hrvis Halias Harg Hrecv Hstruct.
  assert (Hopened : @ty_var mode G' objctx_empty e' r (open r R)).
  { apply ty_rec_elim; assumption. }
  assert (Hreceiver : @ty_var mode G' objctx_empty e' r
    (typ_and (open z TC) (typ_and (open y R) (open r R)))).
  { apply ty_var_and; [exact Hrecv |].
    apply ty_var_and; [|exact Hopened].
    eapply ty_var_sub; [exact Hopened |].
    apply subtyp_tyq. now apply aliased_open_type. }
  eapply (proj1 (term_judgments_narrow mode)); [exact (H3 z Hz r Hneq Hr) | | exact I | exact Henv].
  split.
  - unfold ctx_obj_met. rewrite Hmode. simpl.
    intros x T Hbind.
    inversion Hbind; subst; [exact Hreceiver |].
    match goal with H : ctx_binds _ _ (_ § z / v_par ~ TZ) |- _ =>
      inversion H; subst
    end; [exact Harg |].
    apply ty_var_var. apply Hkeep.
    match goal with H : ctx_binds _ _ (ctx_hide G) |- _ => now inversion H end.
  - intros x Hvis.
    destruct (@visible_method_variable mode G (objctx_heap y R) z r TZ TC x Hmode Hvis)
      as [-> | ->]; assumption.
Qed.

Local Lemma include_context_types_narrow_top mode G H e x k T U :
  x §# H ->
  @includes_context_types mode e G H ->
  @subtyp mode H objctx_empty e U T ->
  @includes_context_types mode e (G § x / k ~ T) (H § x / k ~ U).
Proof.
  intros Hfresh Hinclude Hsub y B Hbind.
  pose proof (binds_preserved_by_fresh_push k U Hfresh) as Hextension.
  inversion Hbind; subst.
  - eapply ty_var_sub.
    + apply ty_var_var. constructor.
    + eapply (proj1 (proj2 (variable_judgments_extend mode))); eauto.
  - eapply (proj1 (variable_judgments_extend mode)).
    + apply Hinclude. eassumption.
    + exact Hextension.
    + auto.
Qed.

Local Definition method_subtype_components mode G e TC1 TZ1 TR1 TC2 TZ2 TR2 :=
  @subtyp mode G objctx_empty e TZ2 TZ1 /\
  (mode_has_sef mode -> typ_indep_b 0 TC2 -> typ_indep_b 0 TC1) /\
  exists L,
    (forall z, z \notin L ->
      @subtyp mode (G § z / v_par ~ TZ2) objctx_empty e
        (open z TC2) (open z TC1)) /\
    (forall z, z \notin L -> forall r, r <> z -> r \notin L ->
      @subtyp mode (ctx_met G z TZ2 r TC2) objctx_empty e
        (open_met z r TR1) (open_met z r TR2)).

Local Lemma method_subtype_components_trans
  mode G e C1 Z1 R1 C2 Z2 R2 C3 Z3 R3 :
  @method_subtype_components mode G e C1 Z1 R1 C2 Z2 R2 ->
  @method_subtype_components mode G e C2 Z2 R2 C3 Z3 R3 ->
  @method_subtype_components mode G e C1 Z1 R1 C3 Z3 R3.
Proof.
  intros [Hz21 [Hi21 (L1 & Hc21 & Hr12)]] [Hz32 [Hi32 (L2 & Hc32 & Hr23)]].
  split; [eapply subtyp_trans; eassumption |].
  split; [auto |].
  exists ((L1 \u L2) \u ctx_dom G).
  assert (Hpar : forall z, z §# G ->
    @includes_context_types mode e (G § z / v_par ~ Z2) (G § z / v_par ~ Z3)).
  { intros z Hfresh. apply include_context_types_narrow_top; [assumption | | assumption].
    intros x T Hbind. now apply ty_var_var. }
  split.
  - intros z Hz.
    apply notin_union in Hz as [Hz Hzdom].
    apply notin_union in Hz as [Hz1 Hz2].
    eapply subtyp_trans; [exact (Hc32 z Hz2) |].
    eapply (proj1 (proj2 (variable_judgments_narrow mode)));
      [exact (Hc21 z Hz1) | exact (Hpar z Hzdom) | auto].
  - intros z Hz r Hneq Hr.
    apply notin_union in Hz as [Hz Hzdom].
    apply notin_union in Hr as [Hr Hrdom].
    apply notin_union in Hz as [Hz1 Hz2].
    apply notin_union in Hr as [Hr1 Hr2].
    assert (Hrecv : @includes_context_types mode e
      (ctx_met G z Z2 r C2) (ctx_met G z Z3 r C3)).
    { apply include_context_types_narrow_top.
      - simpl. apply notin_union. split; [now apply notin_singleton | exact Hrdom].
      - exact (Hpar z Hzdom).
      - exact (Hc32 z Hz2). }
    eapply subtyp_trans; [|exact (Hr23 z Hz2 r Hneq Hr2)].
    eapply (proj1 (proj2 (variable_judgments_narrow mode)));
      [exact (Hr12 z Hz1 r Hneq Hr1) | exact Hrecv | auto].
Qed.

Local Lemma ctx_binds_k_lookup x k T G G0 :
  ctx_binds_k_after x k T G G0 ->
  ctx_binds x T G.
Proof. induction 1; [constructor | now apply ctx_binds_n]. Qed.

Local Lemma ctx_binds_k_preserves_prefix x k T G G0 :
  ctx_binds_k_after x k T G G0 ->
  ctx_ok G ->
  preserves_ctx_binds G0 G.
Proof.
  intro Hlookup. induction Hlookup; intro Hctx; inversion Hctx; subst.
  - now apply binds_preserved_by_fresh_push.
  - intros x U Hx. apply binds_preserved_by_fresh_push; [assumption |].
    apply IHHlookup; assumption.
Qed.

Local Lemma inert_lookup x T G mode :
  @inert mode G ->
  ctx_binds x T G ->
  exists k, inert_typ T k.
Proof.
  intros HG Hbind. induction HG; inversion Hbind; subst; eauto.
Qed.

Local Lemma reference_location_have_same_record mode G e x y :
  mode_has_mutability mode ->
  ctx_ok G ->
  @renv_corr mode G e ->
  binds x y e ->
  exists R B,
    ctx_binds x (typ_and (typ_bnd R) (typ_mut_marker B)) G /\
    ctx_binds y (typ_and (typ_bnd R) (typ_mut_marker typ_bot)) G.
Proof.
  intros Hmut Hctx Henv.
  induction Henv as [G | G G2 G3 e r loc Tr Tl Href Hloc Hcorr Henv IH].
  - intros Hb. contradiction (binds_empty_inv Hb).
  - intros Hbind.
    destruct (binds_push_inv Hbind) as [[-> ->] | [_ Htail]]; [|now apply IH].
    inversion Hcorr; subst.
    + match goal with H : context [mode_refcap_corr' mode] |- _ =>
        assert (Hmode : mode_refcap_corr' mode = mode_refcap_corr_ref_mutability)
          by (destruct mode; discriminate || reflexivity);
        rewrite Hmode in H; destruct H as (B & -> & ->)
      end.
      eexists _, _. split.
      * eapply ctx_binds_k_lookup; eassumption.
      * eapply ctx_binds_k_preserves_prefix; [exact Href | exact Hctx |].
        eapply ctx_binds_k_lookup; eassumption.
    + destruct mode; cbv in *; intuition discriminate.
Qed.

Local Lemma typed_defs_precise_member mode G Go e ds T d :
  @ty_defs mode G Go e ds T ->
  defs_has ds d ->
  exists D, @ty_def mode G Go e d D /\ record_has T D.
Proof.
  intro Htyped. induction Htyped; intro Hlookup; unfold defs_has in Hlookup;
    simpl in Hlookup; case_if.
  - injection Hlookup as <-. eexists. split; [eassumption | constructor].
  - injection Hlookup as <-. eexists. split; [eassumption | apply rh_andr; constructor].
  - destruct (IHHtyped Hlookup) as [Decl [Hdef Hdecl]].
    exists Decl. split; [exact Hdef | now apply rh_andl].
Qed.

Local Lemma heap_object_exact_typing mode G e h y ds T :
  @heap_correspond mode G e h ->
  binds y (item_obj ds) h ->
  ctx_binds y (typ_and (typ_bnd T) (typ_mut_marker typ_bot)) G ->
  @ty_defs mode G (objctx_heap y T) e ds (open y T) /\ defs_varkinds G ds.
Proof.
  intros [_ [_ [_ [_ [_ [_ [_ Hitems]]]]]]] Hbind Hty.
  pose proof (Hitems y (get_some_inv Hbind)) as Hitem.
  inversion Hitem; subst.
  - match goal with H : binds y (item_fun _) h |- _ =>
      discriminate (binds_functional Hbind H)
    end.
  - match goal with H : binds y (item_obj ?ds') h |- _ =>
      tryif constr_eq ds ds' then fail else
      let Heq := fresh in
      pose proof (binds_functional Hbind H) as Heq; injection Heq as <-
    end.
    match goal with H : ctx_binds y (typ_and (typ_bnd U) S) G |- _ =>
      pose proof (ctx_binding_unique Hty H) as Heq;
      injection Heq as <- _
    end.
    now split.
Qed.

Local Lemma record_has_member_subtype mode G e T D :
  record_has T D ->
  @subtyp mode G objctx_empty e T (typ_rcd D).
Proof.
  induction 1.
  - apply subtyp_refl.
  - eapply subtyp_trans; [apply subtyp_and11 | assumption].
  - eapply subtyp_trans; [apply subtyp_and12 | assumption].
Qed.

Local Lemma heap_reference_precise_definition mode G e h x y ds d :
  mode_has_mutability mode ->
  @inert mode G ->
  @heap_correspond mode G e h ->
  binds x y e ->
  binds y (item_obj ds) h ->
  defs_has ds d ->
  exists R B D,
    ctx_binds x (typ_and (typ_bnd R) (typ_mut_marker B)) G /\
    typ_indep_b 0 R /\
    @ty_def mode G (objctx_heap y R) e d D /\
    record_has (open y R) D /\
    @ty_var mode G objctx_empty e x (typ_rcd D).
Proof.
  intros Hmode Hinert Hheap Href Hitem Hhas.
  destruct Hheap as (Hctx & Hweak & Hh & He & Hy & Hx & Henv & Hitems).
  destruct (reference_location_have_same_record Hmode Hctx Henv Href)
    as (R & B & Hrefbind & Hlocbind).
  assert (Hshape : typ_indep_b 0 R).
  { destruct (inert_lookup Hinert Hrefbind) as [k Htype].
    inversion Htype; subst; assumption. }
  destruct (@heap_object_exact_typing mode G e h y ds R)
    as [Hdefs _]; [now repeat split | exact Hitem | exact Hlocbind |].
  destruct (typed_defs_precise_member Hdefs Hhas) as (D & Hdef & Hrecord).
  exists R, B, D.
  repeat split; try assumption.
  assert (HrefR : @ty_var mode G objctx_empty e x (open x R)).
  { apply ty_rec_elim; [|exact Hshape].
    eapply ty_var_sub; [apply ty_var_var; exact Hrefbind | apply subtyp_and11]. }
  eapply ty_var_sub; [exact HrefR |].
  eapply subtyp_trans with (T := open y R); [|now apply record_has_member_subtype].
  apply subtyp_tyq. apply aliased_open_type; [now apply tyq_var_binds | exact Hshape].
Qed.


Local Definition shift_avar v :=
  match v with avar_b n => avar_b (S n) | avar_f x => avar_f x end.

Local Fixpoint independent_of v T : Prop :=
  match T with
  | typ_top | typ_bot | typ_nocap => True
  | typ_rcd D => independent_of_dec v D
  | typ_and U V | typ_or U V => independent_of v U /\ independent_of v V
  | typ_sel a (typ_label_normal _) b => b <> v
  | typ_sel a (typ_label_refcap _) b => a <> v /\ b <> v
  | typ_bnd U => independent_of (shift_avar v) U
  | typ_fun U V => independent_of v U /\ independent_of (shift_avar v) V
  end
with independent_of_dec v D : Prop :=
  match D with
  | dec_typ _ T U => independent_of (shift_avar v) T /\ independent_of (shift_avar v) U
  | dec_fld _ T U => independent_of v T /\ independent_of v U
  | dec_met _ C Z R =>
      independent_of (shift_avar v) C /\ independent_of v Z /\
      independent_of (shift_avar (shift_avar v)) R
  end.

Local Lemma independent_of_spec :
  (forall T v, independent_of v T <-> typ_indep v T) /\
  (forall D v, independent_of_dec v D <-> typ_indep v (typ_rcd D)).
Proof.
  apply typ_mutind; intros; simpl.
  all: try solve [split; [intro; apply typ_indep_nulary; constructor | auto] | apply H].
  all: try solve [
    destruct v; (simpl;
    repeat (rewrite H || rewrite H0 || rewrite H1);
    split; intro Hbound;
    [ first [apply typ_indep_and | apply typ_indep_or | apply typ_indep_bnd_b |
             apply typ_indep_bnd_f | apply typ_indep_fun_b | apply typ_indep_fun_f |
             apply typ_indep_typ_b | apply typ_indep_typ_f | apply typ_indep_fld |
             apply typ_indep_met_b | apply typ_indep_met_f]; tauto
    | inversion Hbound; subst;
      try match goal with Hn : typ_nulary _ |- _ => inversion Hn end;
      tauto ])
  ].
  destruct t; split; intro Hbound.
  - apply typ_indep_sel_normal. congruence.
  - inversion Hbound; subst;
      try match goal with Hn : typ_nulary _ |- _ => inversion Hn end; congruence.
  - apply typ_indep_sel; destruct Hbound; congruence.
  - inversion Hbound; subst;
      try match goal with Hn : typ_nulary _ |- _ => inversion Hn end; (split; congruence).
Qed.

Local Lemma avar_open_preserves_forbidden a x k v :
  v <> avar_b k -> v <> avar_f x ->
  (open_rec k x a <> v <-> a <> v).
Proof.
  destruct a as [i|u]; intros Hk Hx; simpl; [case_if | reflexivity].
  - subst i. split; congruence.
  - reflexivity.
Qed.

Local Lemma independent_of_open :
  (forall T v k x, v <> avar_b k -> v <> avar_f x ->
    independent_of v (open_rec k x T) <-> independent_of v T) /\
  (forall D v k x, v <> avar_b k -> v <> avar_f x ->
    independent_of_dec v (open_rec k x D) <-> independent_of_dec v D).
Proof.
  apply typ_mutind; intros; cbn [open_rec TypOpenable DecOpenable open_rec_typ
    open_rec_dec independent_of independent_of_dec].
  all: try solve [reflexivity | eauto | destruct v; simpl in *; firstorder congruence].
  destruct t; simpl; repeat rewrite avar_open_preserves_forbidden by assumption; reflexivity.
Qed.

Local Lemma avar_open_reflects_free a z k :
  open_rec k z a <> avar_f z <-> a <> avar_f z /\ a <> avar_b k.
Proof.
  destruct a as [i|x]; simpl; [case_if |]; intuition congruence.
Qed.

Local Lemma independent_of_open_reflect :
  (forall T z k, independent_of (avar_f z) (open_rec k z T) <->
    independent_of (avar_f z) T /\ independent_of (avar_b k) T) /\
  (forall D z k, independent_of_dec (avar_f z) (open_rec k z D) <->
    independent_of_dec (avar_f z) D /\ independent_of_dec (avar_b k) D).
Proof.
  apply typ_mutind; intros; cbn [open_rec TypOpenable DecOpenable open_rec_typ
    open_rec_dec independent_of independent_of_dec shift_avar].
  all: try solve [firstorder].
  destruct t; simpl; repeat rewrite avar_open_reflects_free; tauto.
Qed.

Local Lemma free_fresh_independent :
  (forall T x, x \notin fv T -> independent_of (avar_f x) T) /\
  (forall D x, x \notin fv D -> independent_of_dec (avar_f x) D).
Proof.
  apply typ_mutind; intros; cbn [fv TypFreeVar DecFreeVar fv_typ fv_dec
    independent_of independent_of_dec shift_avar] in *.
  all: repeat match goal with
       | H : _ \notin _ \u _ |- _ => apply notin_union in H as [? ?]
       end.
  all: try solve [auto].
  destruct t; simpl; split || idtac.
  all: intro Heq; subst; solve [exfalso; eapply notin_singleton; eassumption |
                              exfalso; eauto using in_singleton_self].
Qed.

Local Lemma choose_var_away_from_av v : exists z, v <> avar_f z.
Proof.
  destruct v as [n|x].
  - destruct (var_fresh \{}) as [z _]. exists z. discriminate.
  - destruct (var_fresh \{x}) as [z H]. apply notin_singleton in H.
    exists z. congruence.
Qed.

Local Lemma independent_of_equiv_under_binder S T v :
  (forall z u, independent_of u (open z S) <-> independent_of u (open z T)) ->
  independent_of (shift_avar v) S <-> independent_of (shift_avar v) T.
Proof.
  intro H. destruct (choose_var_away_from_av (shift_avar v)) as [z Hz].
  specialize (H z (shift_avar v)).
  repeat rewrite (proj1 independent_of_open _ _ 0 z) in H
    by (assumption || (destruct v; discriminate)).
  exact H.
Qed.

Local Lemma independent_of_equiv_under_two_binders S T v :
  (forall z r u, independent_of u (open_met z r S) <-> independent_of u (open_met z r T)) ->
  independent_of (shift_avar (shift_avar v)) S <->
  independent_of (shift_avar (shift_avar v)) T.
Proof.
  intro H. destruct (choose_var_away_from_av (shift_avar (shift_avar v))) as [z Hz].
  specialize (H z z (shift_avar (shift_avar v))).
  repeat rewrite (proj1 independent_of_open _ _ 0 z) in H
    by (assumption || (destruct v; discriminate)).
  repeat rewrite (proj1 independent_of_open _ _ 1 z) in H
    by (assumption || (destruct v; discriminate)).
  exact H.
Qed.

Local Lemma equivalent_types_preserve_independence e T U :
  @tyq_typ e T U ->
  forall v, independent_of v T <-> independent_of v U.
Proof.
  intro Heq. induction Heq; intro v; simpl.
  - reflexivity.
  - inversion H; subst; simpl; firstorder.
  - pose proof (@independent_of_equiv_under_binder t12 t22 v ltac:(assumption)).
    firstorder.
  - firstorder.
  - pose proof (@independent_of_equiv_under_binder t11 t21 v ltac:(assumption)).
    pose proof (@independent_of_equiv_under_binder t12 t22 v ltac:(assumption)).
    firstorder.
  - reflexivity.
  - reflexivity.
  - now apply independent_of_equiv_under_binder.
  - pose proof (@independent_of_equiv_under_binder t11 t21 v ltac:(assumption)).
    pose proof (@independent_of_equiv_under_two_binders t13 t23 v ltac:(assumption)).
    firstorder.
Qed.

Local Lemma opened_equivalent_types_preserve_binder_indep e T U k :
  (forall z, @tyq_typ e (open_rec k z T) (open_rec k z U)) ->
  typ_indep_b k U ->
  typ_indep_b k T.
Proof.
  intros Heq HU. destruct (var_fresh (fv U)) as [z Hz].
  apply (proj1 (proj1 independent_of_spec T _)).
  apply (proj1 (proj1 independent_of_open_reflect T z k)).
  apply (proj2 (equivalent_types_preserve_independence (Heq z) (avar_f z))).
  apply (proj2 (proj1 independent_of_open_reflect U z k)).
  split.
  - now apply (proj1 free_fresh_independent).
  - now apply (proj2 (proj1 independent_of_spec U _)).
Qed.

Local Lemma type_equivalence_symmetric e T U :
  @tyq_typ e T U -> @tyq_typ e U T.
Proof.
  intro Heq. induction Heq; try solve [constructor; unfold typing_equiv in *; auto].
  apply tyq_typ_sel_normal. now apply tyq_var_sym.
Qed.

Local Lemma method_subtype_components_equivalence mode G e m C1 Z1 R1 C2 Z2 R2 :
  @tyq_typ e (typ_rcd (dec_met m C1 Z1 R1)) (typ_rcd (dec_met m C2 Z2 R2)) ->
  @method_subtype_components mode G e C1 Z1 R1 C2 Z2 R2.
Proof.
  intro Heq. inversion Heq; subst.
  all: try solve [match goal with H : typ_nulary _ |- _ => inversion H end].
  all: try solve [
    match goal with H : typ_andor _ |- _ => inversion H; subst; discriminate end
  ].
  split.
  - apply subtyp_tyq. apply type_equivalence_symmetric. unfold typing_equiv in *; eassumption.
  - split.
    + intros _ Hind. eapply opened_equivalent_types_preserve_binder_indep with (U := C2) (e := e);
        [unfold typing_equiv in *; eassumption | exact Hind].
    + exists (\{} : fset var). split.
      * intros z _. apply subtyp_tyq. apply type_equivalence_symmetric.
        unfold typing_equiv in *; auto.
      * intros z _ r _ _. apply subtyp_tyq. auto.
Qed.

Local Lemma initial_call_declared_method mode G c d U w1 w2 m :
  mode_has_mutability mode ->
  @ty_config mode G c U ->
  config_trm c = trm_call (avar_f w1) m (avar_f w2) ->
  c ↦ d ->
  exists y R B body TC TZ TR,
    config_trm d = open_met w2 w1 body /\
    binds w1 y (config_env c) /\
    ctx_binds w1 (typ_and (typ_bnd R) (typ_mut_marker B)) G /\
    typ_indep_b 0 R /\
    @ty_def mode G (objctx_heap y R) (config_env c)
      (def_met m body) (dec_met m TC TZ TR) /\
    @ty_var mode G objctx_empty (config_env c) w1 (typ_rcd (dec_met m TC TZ TR)).
Proof.
  intros Hmode Htyped Hcall Hred.
  destruct c as [t stack h e L]. simpl in Hcall. subst t.
  inversion Htyped; subst. inversion Hred; subst. simpl.
  match goal with
  | H1 : binds w1 ?loc e, H2 : binds ?loc (item_obj ?ds) h,
    H3 : defs_has ?ds (def_met m ?body) |- _ =>
      destruct (@heap_reference_precise_definition mode G e h w1 loc ds
        (def_met m body) Hmode ltac:(eassumption) ltac:(eassumption) H1 H2 H3)
        as (R & B & D & Hctx & Hind & Hdef & Hdecl & Hvar)
  end.
  inversion Hdef; subst.
  repeat eexists; eassumption.
Qed.

Local Lemma typed_call_application_parts mode G Go e t T :
  @ty_trm mode G Go e t T ->
  mode_has_sef mode ->
  forall r z m, t = trm_call (avar_f r) m (avar_f z) ->
  exists C Z R,
    typ_indep_b 0 C /\
    @ty_var mode G objctx_empty e r (typ_rcd (dec_met m C Z R)) /\
    @ty_var mode G objctx_empty e z Z /\
    @ty_var mode G objctx_empty e r (open z C).
Proof.
  intros Htyped Hsef.
  induction Htyped; intros receiver argument method Heq; try discriminate.
  - inversion Heq; subst. exists TC, TZ, TR. repeat split; auto.
  - auto.
Qed.

Local Lemma alias_variable_type_exact mode G e x T :
  @ty_var mode G objctx_empty e x T ->
  forall G' e' w,
    mode_incap' mode = mode_incap_nocap ->
    preserves_ctx_binds G G' ->
    env_binds_more e e' ->
    @tyq_var e' x w ->
    (forall B, ctx_binds x B G -> @ty_var mode G' objctx_empty e' w B) ->
    @ty_var mode G' objctx_empty e' w T.
Proof.
  intro Htyping.
  induction Htyping as
    [G e x T Hlookup
    | G e x T Hvar IH Hind Hincap
    | G e x T Hvar IH Hind
    | G e x T U Hvar1 IH1 Hvar2 IH2
    | G e x T U Hvar IH Hsub
    | G e x T Hmut Hvar IH];
    intros G' e' w Hmode Hkeep Henv Heq Hbase.
  - now apply Hbase.
  - assert (Hsub : @subtyp mode G' objctx_empty e' (open x T) (open w T)).
    { apply subtyp_tyq. now apply aliased_open_type. }
    apply ty_rec_intro; [|exact Hind|].
    + eapply ty_var_sub; [apply IH; eassumption | exact Hsub].
    + intro Hincapmode. apply ty_incap_nocap; [exact Hmode |].
      eapply subtyp_trans; [|exact Hsub].
      eapply (proj1 (proj2 (variable_judgments_extend mode))); try eassumption.
      eapply incap_output_admits_nocap. now apply Hincap.
  - eapply ty_var_sub with (T := open w T).
    + apply ty_rec_elim; [apply IH; eassumption | exact Hind].
    + apply subtyp_tyq. apply aliased_open_type; [now apply tyq_var_sym | exact Hind].
  - apply ty_var_and; [apply IH1 | apply IH2]; eassumption.
  - eapply ty_var_sub; [apply IH; eassumption |].
    eapply (proj1 (proj2 (variable_judgments_extend mode))); eassumption.
  - eapply ty_var_mut_top; [exact Hmut | apply IH; eassumption].
Qed.

Local Lemma alias_variable_same_binding mode G G' e e' x w B T :
  mode_incap' mode = mode_incap_nocap ->
  preserves_ctx_binds G G' ->
  env_binds_more e e' ->
  @tyq_var e' x w ->
  ctx_binds x B G ->
  ctx_binds w B G' ->
  @ty_var mode G objctx_empty e x T ->
  @ty_var mode G' objctx_empty e' w T.
Proof.
  intros Hmode Hkeep Henv Heq Hbind Hcopy Htyped.
  eapply alias_variable_type_exact; try eassumption.
  intros U HU. rewrite (ctx_binding_unique HU Hbind). now apply ty_var_var.
Qed.

Local Lemma includes_context_types_argument mode G G' e z Z :
  preserves_ctx_binds G G' ->
  @ty_var mode G' objctx_empty e z Z ->
  @includes_context_types mode e (G § z / v_par ~ Z) G'.
Proof.
  intros Hkeep Hz x U Hbind.
  inversion Hbind; subst; [exact Hz |].
  apply ty_var_var. apply Hkeep. assumption.
Qed.

(* Use the full-capability argument alias to check the actual application.
   Then transfer the admissible receiver type to the protected alias. *)
Local Lemma pure_opened_body_with_aliases mode G e y w1 w2 R B1 B2 m body
  C Z Ret Ca Za Ra Zv :
  mode_has_sef mode ->
  mode_has_mutability mode ->
  typ_indep_b 0 R ->
  typ_indep_b 0 Ca ->
  @ty_def mode G (objctx_heap y R) e (def_met m body) (dec_met m C Z Ret) ->
  @method_subtype_components mode G e C Z Ret Ca Za Ra ->
  @method_subtype_components mode G e C Z Ret typ_nocap Zv typ_top ->
  ctx_binds w1 (typ_and (typ_bnd R) (typ_mut_marker B1)) G ->
  ctx_binds w2 B2 G ->
  @ty_var mode G objctx_empty e w1 (open w2 Ca) ->
  @ty_var mode G objctx_empty e w2 Za ->
  exists L,
    forall G' e' z r z_orig,
      z \notin L -> r \notin L -> z_orig \notin L -> r <> z ->
      preserves_ctx_binds G G' -> env_binds_more e e' ->
      ctx_vis G' z -> ctx_vis G' r ->
      ctx_binds z_orig B2 G' ->
      @tyq_var e' w2 z_orig ->
      @tyq_var e' z_orig z ->
      @tyq_var e' w1 r ->
      @tyq_var e' r y ->
      @ty_var mode G' objctx_empty e' z Zv ->
      @ty_var mode G' objctx_empty e' r (typ_bnd R) ->
      @ty_trm mode G' objctx_empty e' (open_met z r body) (open_met z r Ret).
Proof.
  intros Hsef Hmut HindR HindCa Hdef
    [Harg_a [_ (La & Hrec_a & _)]] [Harg_p [HindC (Lp & Hrec_p & _)]]
    Hbind1 Hbind2 Hvar1 Hvar2.
  assert (Hvisible : mode_has_visibility mode)
    by (destruct mode; discriminate || reflexivity).
  assert (Hmode : mode_incap' mode = mode_incap_nocap)
    by (destruct mode; discriminate || reflexivity).
  specialize (HindC Hsef (typ_indep_nulary (avar_b 0) typ_nulary_nocap)).
  destruct (opened_heap_method_typing Hvisible HindR Hdef) as [L0 Hbody].
  exists ((La \u Lp) \u L0).
  intros G' e' z r z_orig Hz Hr Ho Hneq Hctx Henv Hzv Hrv Hobind
    Horig Halias2 Halias1 Hloc Harg Hstr.
  apply notin_union in Hz as [Hz Hp0].
  apply notin_union in Hz as [_ Hzp].
  apply notin_union in Hr as [_ Hr0].
  apply notin_union in Ho as [Ho _].
  apply notin_union in Ho as [Hoa _].
  assert (Horig_arg : @ty_var mode G' objctx_empty e' z_orig Za).
  { eapply alias_variable_same_binding; eassumption. }
  assert (Horig_receiver_bound :
    @subtyp mode G' objctx_empty e' (open z_orig Ca) (open z_orig C)).
  { eapply (proj1 (proj2 (variable_judgments_narrow mode))).
    - exact (Hrec_a z_orig Hoa).
    - now apply includes_context_types_argument.
    - exact Henv. }
  assert (Hpure_receiver_bound : @subtyp mode G' objctx_empty e' typ_nocap (open z C)).
  { eapply (proj1 (proj2 (variable_judgments_narrow mode))).
    - exact (Hrec_p z Hzp).
    - now apply includes_context_types_argument.
    - exact Henv. }
  assert (Horig_receiver : @ty_var mode G' objctx_empty e' w1 (open z C)).
  { eapply ty_var_sub with (T := open z_orig C).
    - eapply ty_var_sub with (T := open z_orig Ca); [|exact Horig_receiver_bound].
      eapply ty_var_sub with (T := open w2 Ca).
      + eapply (proj1 (variable_judgments_extend mode)); eassumption.
      + apply subtyp_tyq. now apply aliased_open_type.
    - apply subtyp_tyq. now apply aliased_open_type. }
  eapply Hbody; try eassumption.
  - eapply ty_var_sub; [exact Harg |].
    eapply (proj1 (proj2 (variable_judgments_extend mode))); eassumption.
  - eapply (@copy_alias_type mode G' G' e' e' w1 r R B1 (open z C));
      try assumption.
    + intros x T; auto.
    + auto.
    + now apply Hctx.
Qed.

Local Lemma ctx_visible_in_dom G x :
  ctx_vis G x -> x \in ctx_dom G.
Proof.
  induction 1; simpl; rewrite in_union.
  - left. apply in_singleton_self.
  - now right.
Qed.

Local Lemma fresh_context_push_narrows mode e G x k T :
  x §# G -> @context_narrows mode e G (G § x / k ~ T).
Proof.
  intro Hfresh. split.
  - intros y U Hy. apply ty_var_var.
    now apply binds_preserved_by_fresh_push.
  - intros y Hy. apply ctx_vis_n; [|exact Hy].
    intros ->. apply Hfresh. now apply ctx_visible_in_dom.
Qed.

Local Lemma fresh_push_preserves_kind_lookup G G0 w k T x kx U :
  x §# G ->
  ctx_binds_k_after w k T G G0 ->
  ctx_binds_k_after w k T (G § x / kx ~ U) G0.
Proof.
  intros Hfresh Hbind. apply ctx_binds_k_n; [|exact Hbind].
  intros ->. apply Hfresh. eapply ctx_binding_in_dom.
  eapply ctx_binds_k_lookup; exact Hbind.
Qed.

Local Lemma fresh_push_preserves_kind G w k x kx U :
  x §# G -> ctx_k G w k -> ctx_k (G § x / kx ~ U) w k.
Proof.
  intros Hfresh (T & G0 & Hbind).
  exists T, G0. now apply fresh_push_preserves_kind_lookup.
Qed.

Local Lemma fresh_push_defs_varkinds G ds x k T :
  x §# G ->
  defs_varkinds G ds ->
  defs_varkinds (G § x / k ~ T) ds.
Proof.
  intros Hfresh Hdefs. induction Hdefs as [G | G ds d Hdefs IH Hdef].
  - constructor.
  - apply defs_varkinds_cons; [exact (IH Hfresh) |].
    destruct Hdef.
    + apply def_varkinds_fld. now apply fresh_push_preserves_kind.
    + apply def_varkinds_typ.
    + apply def_varkinds_met. intros w Hw.
      apply fresh_push_preserves_kind; [exact Hfresh | now apply H].
Qed.

Local Lemma fresh_push_renv_corresponds mode G e x k T :
  x §# G ->
  @renv_corr mode G e ->
  @renv_corr mode (G § x / k ~ T) e.
Proof.
  intros Hfresh Hrenv.
  induction Hrenv as [G | G G2 G3 e w y Tw Ty Hw Hy Htype He IH].
  - apply renv_corr_empty.
  - eapply renv_corr_ref; [|exact Hy|exact Htype|exact (IH Hfresh)].
    now apply fresh_push_preserves_kind_lookup.
Qed.

Local Lemma fresh_alias_heap_corresponds mode G G0 e h y x R B :
  mode_has_mutability mode ->
  @heap_correspond mode G e h ->
  ctx_binds_k_after y v_loc (typ_and (typ_bnd R) (typ_mut_marker typ_bot)) G G0 ->
  x §# G ->
  x # e ->
  @heap_correspond mode (G § x / v_ref ~ typ_and (typ_bnd R) (typ_mut_marker B))
    (e & x ~ y) h.
Proof.
  intros Hmut (Hok & Hweak & Hheap & Henv & Hlocdom & Hrefdom & Hcorr & Hitems)
    Hloc Hfresh Hfreshenv.
  assert (Henvmore : env_binds_more e (e & x ~ y)).
  { intros l r Hr. apply binds_push_neq; [exact Hr |].
    intros ->. apply Hfreshenv. exact (get_some_inv Hr). }
  repeat split; try assumption.
  - now apply ctx_ok_push.
  - now apply ctx_weakens_push.
  - now apply ok_push.
  - simpl. now case_if.
  - simpl. case_if. now rewrite dom_push, Hrefdom.
  - eapply renv_corr_ref.
    + apply ctx_binds_k_e.
    + exact Hloc.
    + apply typ_corr_obj.
      assert (Hmode : mode_refcap_corr' mode = mode_refcap_corr_ref_mutability)
        by (destruct mode; discriminate || reflexivity).
      rewrite Hmode. now exists B.
    + now apply fresh_push_renv_corresponds.
  - intros l Hl. specialize (Hitems l Hl).
    inversion Hitems; subst.
    + destruct mode; discriminate.
    + eapply ty_item_obj_s with (U := U) (S := S).
      * eapply binds_preserved_by_fresh_push; eassumption.
      * eassumption.
      * reflexivity.
      * eapply (proj2 (proj2 (proj2 (term_judgments_narrow mode)))).
        -- eassumption.
        -- now apply fresh_context_push_narrows.
        -- exact I.
        -- exact Henvmore.
      * now apply fresh_push_defs_varkinds.
Qed.

Local Lemma kind_lookup_through_prefix x k T G P y l U P0 :
  ctx_binds_k_after x k T G P ->
  ctx_ok G ->
  ctx_binds_k_after y l U P P0 ->
  ctx_binds_k_after y l U G P0.
Proof.
  intros Hafter. induction Hafter; intros Hok Hy; inversion Hok; subst.
  - now apply fresh_push_preserves_kind_lookup.
  - apply fresh_push_preserves_kind_lookup; [assumption |].
    now apply IHHafter.
Qed.

Local Lemma reference_location_kind mode G e x y :
  mode_has_mutability mode ->
  ctx_ok G ->
  @renv_corr mode G e ->
  binds x y e ->
  exists R B G0,
    ctx_binds x (typ_and (typ_bnd R) (typ_mut_marker B)) G /\
    ctx_binds_k_after y v_loc (typ_and (typ_bnd R) (typ_mut_marker typ_bot)) G G0.
Proof.
  intros Hmut Hok Hcorr.
  induction Hcorr as [G | G G2 G3 e r loc Tr Tl Href Hloc Htype Hcorr IH].
  - intros Hb. contradiction (binds_empty_inv Hb).
  - intros Hb. destruct (binds_push_inv Hb) as [[-> ->] | [_ Htail]];
      [|now apply IH].
    inversion Htype; subst.
    + match goal with H : context [mode_refcap_corr' mode] |- _ =>
        assert (Hmode : mode_refcap_corr' mode = mode_refcap_corr_ref_mutability)
          by (destruct mode; discriminate || reflexivity);
        rewrite Hmode in H; destruct H as (B & -> & ->)
      end.
      eexists _, _, G3. split.
      * eapply ctx_binds_k_lookup; eassumption.
      * eapply kind_lookup_through_prefix; eassumption.
    + destruct mode; cbv in *; intuition discriminate.
Qed.

Local Lemma fresh_alias_inert mode G x w R B D :
  mode_has_mutability mode ->
  @inert mode G ->
  ctx_binds x (typ_and (typ_bnd R) (typ_mut_marker B)) G ->
  w §# G ->
  w \notin ctx_fv G ->
  w \notin fv (typ_and (typ_bnd R) (typ_mut_marker D)) ->
  @inert mode (G § w / v_ref ~ typ_and (typ_bnd R) (typ_mut_marker D)).
Proof.
  intros Hmode HG Hbind Hdom Hfv Htype.
  destruct (inert_lookup HG Hbind) as [k Hkind]. inversion Hkind; subst.
  apply inert_push; try assumption.
  - apply inert_vk_ref.
  - apply inert_typ_obj; try assumption.
    assert (Hmode' : mode_refcaps' mode = mode_refcaps_mutability)
      by (destruct mode; discriminate || reflexivity).
    unfold refcap_inert_type. rewrite Hmode'. constructor.
Qed.

Local Lemma ctx_bound_type_sealed G x T :
  ctx_binds x T G -> sealed G -> sealed T.
Proof.
  intros Hbind. induction Hbind; intro Hseal.
  - intro z. specialize (Hseal z).
    cbn [seal_rec CtxSealable ctx_seal_rec] in Hseal. now injection Hseal.
  - apply IHHbind. intro z. specialize (Hseal z).
    cbn [seal_rec CtxSealable ctx_seal_rec] in Hseal. now injection Hseal.
  - apply IHHbind. intro z. specialize (Hseal z).
    cbn [seal_rec CtxSealable ctx_seal_rec] in Hseal. now injection Hseal.
Qed.

Local Lemma readonly_marker_sealed R B :
  sealed (typ_and (typ_bnd R) (typ_mut_marker B)) ->
  sealed (typ_and (typ_bnd R) (typ_mut_marker typ_top)).
Proof.
  intros Hseal z. specialize (Hseal z).
  cbn [seal_rec TypSealable seal_rec_typ seal_rec_dec] in Hseal |- *.
  now injection Hseal as -> _.
Qed.

Local Lemma sealed_push_type G w k T :
  sealed G -> sealed T -> sealed (G § w / k ~ T).
Proof.
  intros HG HT z.
  change (ctx_push (seal z G) w k (seal z T) = ctx_push G w k T).
  now rewrite HG, HT.
Qed.

Local Lemma extend_typed_heap_with_alias mode G e h orig y R B D (L : fset var) :
  mode_has_mutability mode ->
  @inert mode G ->
  @heap_correspond mode G e h ->
  sealed G ->
  ctx_binds orig (typ_and (typ_bnd R) (typ_mut_marker B)) G ->
  binds orig y e ->
  (D = B \/ D = typ_top) ->
  exists w,
    let G' := G § w / v_ref ~ typ_and (typ_bnd R) (typ_mut_marker D) in
    let e' := e & w ~ y in
    w \notin L /\
    w §# G /\
    w # e /\
    @inert mode G' /\
    @heap_correspond mode G' e' h /\
    sealed G' /\
    preserves_ctx_binds G G' /\
    env_binds_more e e' /\
    @tyq_var e' orig w /\
    @context_narrows mode e' G G'.
Proof.
  intros Hmode Hinert Hheap Hsealed Hbind Horig Hmark.
  destruct Hheap as (Hok & Hw & Hh & He & Hdy & Hdx & Hcorr & Hitems).
  destruct (reference_location_kind Hmode Hok Hcorr Horig)
    as (R' & B' & G0 & Hbind' & Hloc).
  pose proof (ctx_binding_unique Hbind Hbind') as Heq.
  injection Heq as <- _.
  set (Tnew := typ_and (typ_bnd R) (typ_mut_marker D)).
  destruct (var_fresh ((((L \u ctx_dom G) \u ctx_fv G) \u dom e) \u fv Tnew))
    as [w Hfresh].
  apply notin_union in Hfresh as [Hfresh Htypenew].
  apply notin_union in Hfresh as [Hfresh Henvnew].
  apply notin_union in Hfresh as [Hfresh Hctxfv].
  apply notin_union in Hfresh as [HL Hctxnew].
  assert (Henvmore : env_binds_more e (e & w ~ y)).
  { intros loc u Hu. apply binds_push_neq; [exact Hu |].
    intros ->. apply Henvnew. exact (get_some_inv Hu). }
  exists w. cbv zeta.
  split; [exact HL |].
  split; [exact Hctxnew |].
  split; [exact Henvnew |].
  split.
  { eapply fresh_alias_inert; eassumption. }
  split.
  { eapply fresh_alias_heap_corresponds; try eassumption.
    now repeat split. }
  split.
  { apply sealed_push_type; [exact Hsealed |].
    pose proof (ctx_bound_type_sealed Hbind Hsealed) as HT.
    destruct Hmark as [-> | ->]; [exact HT | now apply readonly_marker_sealed in HT]. }
  split; [now apply binds_preserved_by_fresh_push |].
  split; [exact Henvmore |].
  split.
  { eapply tyq_var_trans with (v2 := y).
    - apply tyq_var_binds. now apply Henvmore.
    - apply tyq_var_sym, tyq_var_binds, binds_push_eq. }
  now apply fresh_context_push_narrows.
Qed.

Local Lemma prepare_pure_method_body mode G e h y1 y2 w1 w2 R1 R2 B1 B2 m body
  C Z Ret Ca Za Ra Zv (avoid : fset var) :
  mode_has_sef mode ->
  mode_has_mutability mode ->
  @inert mode G ->
  @heap_correspond mode G e h ->
  sealed G ->
  binds w1 y1 e ->
  binds w2 y2 e ->
  typ_indep_b 0 R1 ->
  typ_indep_b 0 Ca ->
  @ty_def mode G (objctx_heap y1 R1) e (def_met m body) (dec_met m C Z Ret) ->
  @method_subtype_components mode G e C Z Ret Ca Za Ra ->
  @method_subtype_components mode G e C Z Ret typ_nocap Zv typ_top ->
  ctx_binds w1 (typ_and (typ_bnd R1) (typ_mut_marker B1)) G ->
  ctx_binds w2 (typ_and (typ_bnd R2) (typ_mut_marker B2)) G ->
  @ty_var mode G objctx_empty e w1 (open w2 Ca) ->
  @ty_var mode G objctx_empty e w2 Za ->
  @ty_var mode G objctx_empty e w2 Zv ->
  @subtyp mode G objctx_empty e typ_nocap Zv ->
  exists G' e' z0 z r,
    z0 \notin avoid /\ z \notin avoid /\ r \notin avoid /\
    z <> r /\ z0 <> r /\ z0 <> z /\
    e' = e & z0 ~ y2 & z ~ y2 & r ~ y1 /\
    G' = (G § z0 / v_ref ~ typ_and (typ_bnd R2) (typ_mut_marker B2)
            § z / v_ref ~ typ_and (typ_bnd R2) (typ_mut_marker typ_top)
            § r / v_ref ~ typ_and (typ_bnd R1) (typ_mut_marker typ_top)) /\
    @inert mode G' /\ @heap_correspond mode G' e' h /\ sealed G' /\
    env_binds_more e e' /\
    binds z y2 e' /\ binds r y1 e' /\
    ctx_binds z (typ_and (typ_bnd R2) (typ_mut_marker typ_top)) G' /\
    ctx_binds r (typ_and (typ_bnd R1) (typ_mut_marker typ_top)) G' /\
    @ty_trm mode G' objctx_empty e' (open_met z r body) (open_met z r Ret).
Proof.
  intros Hsef Hmut Hiner Hheap Hseal Hy1 Hy2 HR Hind HC Hca Hp
    Hctx1 Hctx2 Hty1 Hty2 Harg Hnocap.
  destruct (pure_opened_body_with_aliases Hsef Hmut HR Hind HC Hca Hp
    Hctx1 Hctx2 Hty1 Hty2) as [L Hbody].
  destruct (@extend_typed_heap_with_alias mode G e h w2 y2 R2 B2 B2 (avoid \u L)
    Hmut Hiner Hheap Hseal Hctx2 Hy2 (or_introl eq_refl))
    as (z0 & Hz0 & _ & _ & HI0 & HH0 & HS0 & HK0 & HE0 & Hq0 & _).
  cbv zeta in *.
  set (G0 := G § z0 / v_ref ~ typ_and (typ_bnd R2) (typ_mut_marker B2)) in *.
  set (e0 := e & z0 ~ y2) in *.
  destruct (@extend_typed_heap_with_alias mode G0 e0 h w2 y2 R2 B2 typ_top
    (avoid \u L) Hmut HI0 HH0 HS0 (HK0 _ _ Hctx2) (HE0 _ _ Hy2) (or_intror eq_refl))
    as (z & Hz & HFz & HFze & HI1 & HH1 & HS1 & HK1 & HE1 & Hq1 & _).
  cbv zeta in *.
  set (G1 := G0 § z / v_ref ~ typ_and (typ_bnd R2) (typ_mut_marker typ_top)) in *.
  set (e1 := e0 & z ~ y2) in *.
  destruct (@extend_typed_heap_with_alias mode G1 e1 h w1 y1 R1 B1 typ_top
    (avoid \u L) Hmut HI1 HH1 HS1
    (HK1 _ _ (HK0 _ _ Hctx1)) (HE1 _ _ (HE0 _ _ Hy1)) (or_intror eq_refl))
    as (r & Hr & HFr & _ & HI2 & HH2 & HS2 & HK2 & HE2 & Hq2 & Hnar).
  cbv zeta in *.
  set (G2 := G1 § r / v_ref ~ typ_and (typ_bnd R1) (typ_mut_marker typ_top)) in *.
  set (e2 := e1 & r ~ y1) in *.
  exists G2, e2, z0, z, r.
  apply notin_union in Hz0 as [Hz0A Hz0L].
  apply notin_union in Hz as [HzA HzL].
  apply notin_union in Hr as [HrA HrL].
  assert (Hctxz : ctx_binds z (typ_and (typ_bnd R2) (typ_mut_marker typ_top)) G1)
    by (unfold G1; constructor).
  assert (Hctxr : ctx_binds r (typ_and (typ_bnd R1) (typ_mut_marker typ_top)) G2)
    by (unfold G2; constructor).
  assert (Hkeep : preserves_ctx_binds G G2)
    by (intros x U Hx; apply HK2, HK1, HK0, Hx).
  assert (Henvmore : env_binds_more e e2)
    by (intros a b Hb; apply HE2, HE1, HE0, Hb).
  assert (Hzr : z <> r).
  { intros ->. apply HFr. exact (ctx_binding_in_dom Hctxz). }
  assert (Hz0r : z0 <> r).
  { intros ->. apply HFr. unfold G1, G0. simpl.
    rewrite !in_union. auto using in_singleton_self. }
  assert (Hz0z : z0 <> z).
  { intros ->. apply HFz. unfold G0. simpl.
    rewrite in_union. auto using in_singleton_self. }
  assert (He2 : e2 = e & z0 ~ y2 & z ~ y2 & r ~ y1) by reflexivity.
  repeat (assumption || reflexivity || split).
  - apply HE2, binds_push_eq.
  - apply binds_push_eq.
  - now apply HK2.
  - assert (Harg0 : @ty_var mode G0 objctx_empty e0 w2 Zv).
    { eapply (proj1 (variable_judgments_extend mode)); eassumption. }
    assert (Hnocap0 : @subtyp mode G0 objctx_empty e0 typ_nocap Zv).
    { eapply (proj1 (proj2 (variable_judgments_extend mode))); eassumption. }
    assert (Hargz : @ty_var mode G1 objctx_empty e1 z Zv).
    { eapply fresh_readonly_alias_type with (x := w2) (B := B2); try eassumption.
      - now apply HK0.
      - now apply HE0. }
    apply (Hbody G2 e2 z r z0); try assumption.
    + intros ->. apply HFr. exact (ctx_binding_in_dom Hctxz).
    + apply (proj2 Hnar). unfold G1. constructor.
    + unfold G2. constructor.
    + apply HK2, HK1. unfold G0. constructor.
    + eapply var_equivalence_extend; [exact Hq0 |].
      intros u v Hv. now apply HE2, HE1.
    + eapply tyq_var_trans with (v2 := w2).
      * apply tyq_var_sym. eapply var_equivalence_extend; [exact Hq0 |].
        intros u v Hv. now apply HE2, HE1.
      * eapply var_equivalence_extend; eassumption.
    + apply tyq_var_binds. apply binds_push_eq.
    + eapply (proj1 (variable_judgments_extend mode)); eassumption.
    + eapply ty_var_sub; [apply ty_var_var; exact Hctxr | apply subtyp_and11].
Qed.

Local Lemma incapacitation_is_supertype mode G Go e S T :
  @ty_incap mode G Go e S T ->
  @subtyp mode G Go e S T.
Proof.
  intro H. induction H; try solve [apply subtyp_refl | apply subtyp_top | apply subtyp_bot].
  - eapply subtyp_trans; [eapply subtyp_sel1; eassumption | exact IHty_incap].
  - apply subtyp_and2.
    + eapply subtyp_trans; [apply subtyp_and11 | exact IHty_incap].
    + eapply subtyp_trans; [apply subtyp_and12 | exact IHty_incap0].
  - apply subtyp_or2.
    + eapply subtyp_trans; [exact IHty_incap | apply subtyp_or11].
    + eapply subtyp_trans; [exact IHty_incap0 | apply subtyp_or12].
Qed.

Local Lemma adapt_read_alias_type mode G e x loc w R T Tr :
  mode_has_sef mode ->
  mode_has_mutability mode ->
  ctx_binds loc (typ_and (typ_bnd R) (typ_mut_marker typ_bot)) G ->
  @ty_var mode G objctx_empty e loc T ->
  @viewpoint_adapt mode x G objctx_empty e T Tr ->
  w §# G ->
  w # e ->
  exists S B,
    Tr = typ_and S
      (typ_mut_marker (typ_or B (typ_sel (avar_f x) typ_label_mutability (avar_b 0)))) /\
    @ty_var mode
      (G § w / v_ref ~ typ_and (typ_bnd R)
        (typ_mut_marker (typ_or B (typ_sel (avar_f x) typ_label_mutability (avar_b 0)))))
      objctx_empty (e & w ~ loc) w Tr.
Proof.
  intros Hsef Hmut Hloc Hsource Hview Hctxfresh Henvfresh.
  assert (Hm : mode_viewpoint_adaptation' mode = mode_viewpoint_adapt_mutability)
    by (destruct mode; discriminate || reflexivity).
  unfold viewpoint_adapt in Hview. rewrite Hm in Hview.
  inversion Hview as [C v H Go E U S B Hinc Hcap]; subst.
  exists S, B. split; [reflexivity |].
  apply ty_var_and.
  - eapply copy_alias_type with (x := loc) (B := typ_bot); try eassumption.
    + now apply binds_preserved_by_fresh_push.
    + intros y r Hr. apply binds_push_neq; [exact Hr |].
      intros ->. apply Henvfresh. exact (get_some_inv Hr).
    + apply tyq_var_sym, tyq_var_binds, binds_push_eq.
    + eapply ty_var_sub; [apply ty_var_var; constructor | apply subtyp_and11].
    + eapply ty_var_sub; [exact Hsource | now apply incapacitation_is_supertype].
    + eapply incap_output_admits_nocap; eassumption.
  - eapply ty_var_sub; [apply ty_var_var; constructor | apply subtyp_and12].
Qed.

Local Lemma capability_markers_combine mode G e C B D :
  @subtyp mode G objctx_empty e
    (typ_and (typ_cap_marker C B) (typ_cap_marker C D))
    (typ_cap_marker C (typ_and B D)).
Proof.
  eapply subtyp_trans; [apply subtyp_typ_and |].
  apply subtyp_typ; intro z.
  - apply subtyp_bot.
  - apply subtyp_refl.
Qed.

Local Lemma cap_bound_from_type_and_marker mode C G Go e T B :
  @ty_capbnd mode C G Go e T B ->
  @subtyp mode G Go e (typ_and T (typ_cap_marker C typ_top)) (typ_cap_marker C B).
Proof.
  intro H. induction H; try solve [apply subtyp_and12].
  - eapply subtyp_trans; [apply subtyp_and11 | apply subtyp_bot].
  - eapply subtyp_trans; [apply subtyp_and11 |].
    apply subtyp_typ; intro z; [apply subtyp_bot | apply subtyp_refl].
  - eapply subtyp_trans; [|exact IHty_capbnd].
    apply subtyp_and2; [|apply subtyp_and12].
    eapply subtyp_trans; [apply subtyp_and11 |].
    eapply subtyp_sel1. eassumption.
  - eapply subtyp_trans; [|apply capability_markers_combine].
    apply subtyp_and2.
    + eapply subtyp_trans; [|exact IHty_capbnd].
      apply subtyp_and2; [|apply subtyp_and12].
      eapply subtyp_trans; [apply subtyp_and11 | apply subtyp_and11].
    + eapply subtyp_trans; [|exact IHty_capbnd0].
      apply subtyp_and2; [|apply subtyp_and12].
      eapply subtyp_trans; [apply subtyp_and11 | apply subtyp_and12].
  - eapply subtyp_trans.
    + apply subtyp_and2; [apply subtyp_and12 | apply subtyp_and11].
    + eapply subtyp_trans; [apply subtyp_dist |].
      apply subtyp_or2.
      * eapply subtyp_trans.
        -- eapply subtyp_trans; [|exact IHty_capbnd].
           apply subtyp_and2; [apply subtyp_and12 | apply subtyp_and11].
        -- apply subtyp_typ; intro z; [apply subtyp_refl | apply subtyp_or11].
      * eapply subtyp_trans.
        -- eapply subtyp_trans; [|exact IHty_capbnd0].
           apply subtyp_and2; [apply subtyp_and12 | apply subtyp_and11].
        -- apply subtyp_typ; intro z; [apply subtyp_refl | apply subtyp_or12].
Qed.

Local Lemma variable_has_apparent_capability mode G e x T B :
  mode_has_mutability mode ->
  @ty_var mode G objctx_empty e x T ->
  @ty_capbnd mode typ_refcap_mutability G objctx_empty e T B ->
  @ty_var mode G objctx_empty e x (typ_mut_marker B).
Proof.
  intros Hmode Hty Hcap.
  eapply ty_var_sub; [|exact (cap_bound_from_type_and_marker Hcap)].
  apply ty_var_and; [exact Hty |].
  eapply ty_var_mut_top; eassumption.
Qed.

Local Lemma location_has_reference_type mode G e h w y T :
  mode_has_sef mode ->
  mode_has_mutability mode ->
  @heap_correspond mode G e h ->
  binds w y e ->
  @ty_var mode G objctx_empty e w T ->
  @ty_var mode G objctx_empty e y T.
Proof.
  intros Hsef Hmut (Hok & _ & _ & _ & _ & _ & Hcorr & _) Hbind Hty.
  destruct (reference_location_have_same_record Hmut Hok Hcorr Hbind)
    as (R & B & Hw & Hy).
  eapply (@alias_variable_type_exact mode G e w T Hty G e y).
  - destruct mode; discriminate || reflexivity.
  - intros a S H; exact H.
  - intros a b H; exact H.
  - now apply tyq_var_binds.
  - intros S HS. rewrite (ctx_binding_unique HS Hw).
    apply ty_var_and.
    + eapply ty_var_sub; [apply ty_var_var; exact Hy | apply subtyp_and11].
    + eapply ty_var_sub.
      * eapply ty_var_sub; [apply ty_var_var; exact Hy | apply subtyp_and12].
      * apply subtyp_typ; intro z; [apply subtyp_refl | apply subtyp_bot].
Qed.

Local Lemma field_update_same_labels ds a y ds' :
  defs_update ds a y ds' ->
  forall l, defs_hasnt ds l <-> defs_hasnt ds' l.
Proof.
  intro H. induction H; intro l; unfold defs_hasnt in *; simpl; case_if.
  - split; discriminate.
  - reflexivity.
  - split; discriminate.
  - now apply IHdefs_update.
Qed.

Local Lemma typed_update_keeps_declarations mode G Go e ds ds' a v T :
  defs_update ds a v ds' ->
  @ty_defs mode G Go e ds T ->
  vis_var mode (G §§& Go) v ->
  (forall U, record_has T (dec_fld a U U) ->
    @ty_var mode (G §§& Go) objctx_empty e v U) ->
  @ty_defs mode G Go e ds' T.
Proof.
  intro Hupdate. revert T.
  induction Hupdate; intros U Htyped Hvisible Hfield; inversion Htyped; subst.
  - match goal with H : obj_dec_typing G Go e (def_fld a _) _ |- _ =>
      inversion H; subst
    end.
    apply ty_defs_one, ty_def_fld; [exact Hvisible |].
    apply Hfield. constructor.
  - match goal with H : obj_dec_typing G Go e (def_fld a _) _ |- _ =>
      inversion H; subst
    end.
    apply ty_defs_cons; try assumption.
    + apply ty_def_fld; [exact Hvisible |].
      apply Hfield. apply rh_andr. constructor.
  - inversion Hupdate.
  - eapply ty_defs_cons.
    + eapply IHHupdate; try eassumption.
      intros S Hmember. apply Hfield. now apply rh_andl.
    + eassumption.
    + apply (proj1 (field_update_same_labels Hupdate _)). eassumption.
Qed.

Local Definition rename_avar (rename : var -> var) (a : avar) : avar :=
  match a with avar_b n => avar_b n | avar_f x => avar_f (rename x) end.

Local Fixpoint rename_typ (rename : var -> var) T : typ :=
  match T with
  | typ_top => typ_top
  | typ_bot => typ_bot
  | typ_nocap => typ_nocap
  | typ_sel a label b => typ_sel (rename_avar rename a) label (rename_avar rename b)
  | typ_bnd U => typ_bnd (rename_typ rename U)
  | typ_and U V => typ_and (rename_typ rename U) (rename_typ rename V)
  | typ_or U V => typ_or (rename_typ rename U) (rename_typ rename V)
  | typ_fun U V => typ_fun (rename_typ rename U) (rename_typ rename V)
  | typ_rcd D => typ_rcd (rename_dec rename D)
  end
with rename_dec (rename : var -> var) D : dec :=
  match D with
  | dec_typ a U V => dec_typ a (rename_typ rename U) (rename_typ rename V)
  | dec_fld a U V => dec_fld a (rename_typ rename U) (rename_typ rename V)
  | dec_met m C Z R => dec_met m (rename_typ rename C) (rename_typ rename Z) (rename_typ rename R)
  end.

Local Fixpoint rename_trm (rename : var -> var) t : trm :=
  match t with
  | trm_var a => trm_var (rename_avar rename a)
  | trm_read a l => trm_read (rename_avar rename a) l
  | trm_write a l b => trm_write (rename_avar rename a) l (rename_avar rename b)
  | trm_call a l b => trm_call (rename_avar rename a) l (rename_avar rename b)
  | trm_apply a b => trm_apply (rename_avar rename a) (rename_avar rename b)
  | trm_let s u => trm_let (rename_trm rename s) (rename_trm rename u)
  | trm_lit l u => trm_lit (rename_lit rename l) (rename_trm rename u)
  end
with rename_lit (rename : var -> var) l : lit :=
  match l with
  | lit_fun T t => lit_fun (rename_typ rename T) (rename_trm rename t)
  | lit_obj T ds => lit_obj (rename_typ rename T) (rename_defs rename ds)
  end
with rename_def (rename : var -> var) d : def :=
  match d with
  | def_typ l T => def_typ l (rename_typ rename T)
  | def_fld l a => def_fld l (rename_avar rename a)
  | def_met l t => def_met l (rename_trm rename t)
  end
with rename_defs (rename : var -> var) ds : defs :=
  match ds with
  | defs_nil => defs_nil
  | defs_cons ds d => defs_cons (rename_defs rename ds) (rename_def rename d)
  end.

Local Fixpoint rename_stack (rename : var -> var) s : stack :=
  match s with
  | stack_nil => stack_nil
  | stack_cons (frame_let t) rest =>
      stack_cons (frame_let (rename_trm rename t)) (rename_stack rename rest)
  end.

Local Lemma rename_avar_open rename k x a :
  rename_avar rename (open_rec k x a) = open_rec k (rename x) (rename_avar rename a).
Proof. destruct a; simpl; [now case_if | reflexivity]. Qed.

Local Lemma rename_typ_open rename :
  (forall T k x, rename_typ rename (open_rec k x T) =
    open_rec k (rename x) (rename_typ rename T)) /\
  (forall D k x, rename_dec rename (open_rec k x D) =
    open_rec k (rename x) (rename_dec rename D)).
Proof.
  apply typ_mutind; intros; cbn [open_rec TypOpenable DecOpenable
    open_rec_typ open_rec_dec rename_typ rename_dec]; f_equal;
    auto using rename_avar_open.
Qed.

Local Lemma rename_trm_open rename :
  (forall t k x, rename_trm rename (open_rec k x t) =
    open_rec k (rename x) (rename_trm rename t)) /\
  (forall l k x, rename_lit rename (open_rec k x l) =
    open_rec k (rename x) (rename_lit rename l)) /\
  (forall d k x, rename_def rename (open_rec k x d) =
    open_rec k (rename x) (rename_def rename d)) /\
  (forall ds k x, rename_defs rename (open_rec k x ds) =
    open_rec k (rename x) (rename_defs rename ds)).
Proof.
  apply trm_mutind; intros;
    cbn [open_rec TrmOpenable LitOpenable DefOpenable DefsOpenable
      open_rec_trm open_rec_lit open_rec_def open_rec_defs
      rename_trm rename_lit rename_def rename_defs]; f_equal;
    auto using rename_avar_open.
  all: apply (proj1 (rename_typ_open rename)).
Qed.

Local Lemma rename_def_preserves_label rename d :
  label_of (rename_def rename d) = label_of d.
Proof. destruct d; reflexivity. Qed.

Local Lemma rename_defs_get rename ds label :
  get_def label (rename_defs rename ds) = option_map (rename_def rename) (get_def label ds).
Proof.
  induction ds; simpl; [reflexivity |].
  rewrite rename_def_preserves_label. case_if; auto.
Qed.

Local Lemma rename_defs_has_inv rename ds d :
  defs_has (rename_defs rename ds) d ->
  exists d', defs_has ds d' /\ rename_def rename d' = d.
Proof.
  unfold defs_has. rewrite rename_defs_get.
  destruct (get_def (label_of d) ds) as [d'|] eqn:Hd; [|discriminate].
  intro Heq. injection Heq as <-.
  exists d'. split; [|reflexivity].
  now rewrite rename_def_preserves_label in Hd.
Qed.

(* Stored fields contain locations, while stored methods still contain references. *)
Local Definition rename_stored_def (rename : var -> var) d :=
  match d with
  | def_fld field loc => def_fld field loc
  | _ => rename_def rename d
  end.

Local Fixpoint rename_stored_defs (rename : var -> var) ds :=
  match ds with
  | defs_nil => defs_nil
  | defs_cons ds d => defs_cons (rename_stored_defs rename ds) (rename_stored_def rename d)
  end.

Local Definition rename_item (rename : var -> var) i :=
  match i with
  | item_fun t => item_fun (rename_trm rename t)
  | item_obj ds => item_obj (rename_stored_defs rename ds)
  end.

Local Lemma rename_stored_def_label rename d :
  label_of (rename_stored_def rename d) = label_of d.
Proof. destruct d; reflexivity. Qed.

Local Lemma rename_stored_def_get rename ds l :
  get_def l (rename_stored_defs rename ds) =
    option_map (rename_stored_def rename) (get_def l ds).
Proof.
  induction ds; simpl; [reflexivity |].
  rewrite rename_stored_def_label. case_if; auto.
Qed.

Local Lemma rename_stored_defs_has_inv rename ds d :
  defs_has (rename_stored_defs rename ds) d ->
  exists d', defs_has ds d' /\ rename_stored_def rename d' = d.
Proof.
  unfold defs_has. rewrite rename_stored_def_get.
  destruct (get_def (label_of d) ds) as [d'|] eqn:Hd; [|discriminate].
  intro Heq. injection Heq as <-.
  exists d'. split; [|reflexivity].
  now rewrite rename_stored_def_label in Hd.
Qed.

Local Definition heap_projects rename (alias original : heap) :=
  ok alias /\ ok original /\
  forall y it, binds y it original <->
    exists i, binds y i alias /\ rename_item rename i = it.

Local Definition env_projects (rename : var -> var) (alias original : renv) :=
  forall x y, binds x y alias <-> binds (rename x) y original.

Local Definition name_fixed_by (rename : var -> var) (w : var) :=
  forall v, rename v = w <-> v = w.

Local Lemma name_fixed_by_eq rename w :
  name_fixed_by rename w -> rename w = w.
Proof. intro H. apply (proj2 (H w)). reflexivity. Qed.

Local Lemma env_projection_push rename ea e w y :
  env_projects rename ea e ->
  name_fixed_by rename w ->
  env_projects rename (ea & w ~ y) (e & w ~ y).
Proof.
  intros Henv Hfixed v q. split; intro Hbind; apply binds_push_inv in Hbind.
  - destruct Hbind as [[-> ->] | [Hne Htail]].
    + rewrite (name_fixed_by_eq Hfixed). apply binds_push_eq.
    + apply binds_push_neq; [now apply Henv |].
      intro Heq. apply Hne. now apply (proj1 (Hfixed v)).
  - destruct Hbind as [[Heq ->] | [Hne Htail]].
    + apply (proj1 (Hfixed v)) in Heq. subst v. apply binds_push_eq.
    + apply binds_push_neq; [now apply Henv |].
      intros ->. apply Hne. now apply name_fixed_by_eq.
Qed.

Local Lemma heap_projection_push rename ha h loc i :
  heap_projects rename ha h ->
  loc # ha -> loc # h ->
  heap_projects rename (ha & loc ~ i) (h & loc ~ rename_item rename i).
Proof.
  intros [Hoka [Hok Hproj]] Hfa Hf.
  split; [now apply ok_push |].
  split; [now apply ok_push |].
  intros y v. split.
  - intro Hb. apply binds_push_inv in Hb as [[-> ->] | [Hneq Hold]].
    + exists i. split; [apply binds_push_eq | reflexivity].
    + destruct (proj1 (Hproj _ _) Hold) as (j & Hj & Heq).
      exists j. split; [now apply binds_push_neq | exact Heq].
  - intros (j & Hb & <-).
    apply binds_push_inv in Hb as [[-> ->] | [Hneq Hold]].
    + apply binds_push_eq.
    + apply binds_push_neq; [now apply (proj2 (Hproj _ _)); exists j | assumption].
Qed.

Local Lemma env_replace_value (A : Type) (E : env A) y (v u : A) :
  ok E -> binds y v E ->
  exists E',
    ok E' /\ dom E' = dom E /\ binds y u E' /\
    forall z w, z <> y -> binds z w E -> binds z w E'.
Proof.
  induction E as [| E x q IH] using env_ind; intros Hok Hb.
  - contradiction (binds_empty_inv Hb).
  - destruct (ok_push_inv Hok) as [Hok0 Hx].
    apply binds_push_inv in Hb as [[-> ->] | [Hneq Hb]].
    + exists (E & x ~ u). split; [now apply ok_push |].
      split; [now rewrite !dom_push |].
      split; [apply binds_push_eq |].
      intros z w Hz Hw. apply binds_push_neq; [|assumption].
      eapply binds_push_neq_inv; eassumption.
    + destruct (IH Hok0 Hb) as (E' & Hok' & Hd & Hb' & Hrest).
      exists (E' & x ~ q). split.
      { apply ok_push; [exact Hok' |]. now rewrite Hd. }
      split; [now rewrite !dom_push, Hd |].
      split; [now apply binds_push_neq |].
      intros z w Hz Hw. apply binds_push_inv in Hw as [[-> ->] | [Hzx Hw]].
      * apply binds_push_eq.
      * apply binds_push_neq; [now apply Hrest | exact Hzx].
Qed.

Local Lemma rename_stored_defs_update_inv rename ds a y res :
  defs_update (rename_stored_defs rename ds) a y res ->
  exists ds', defs_update ds a y ds' /\ rename_stored_defs rename ds' = res.
Proof.
  revert res. induction ds as [|ds IH d]; intros res Hupdate; simpl in Hupdate.
  - inversion Hupdate.
  - inversion Hupdate; subst.
    + destruct d; simpl in *; try discriminate.
      match goal with H : def_fld _ _ = def_fld _ _ |- _ => inversion H; subst end.
      eexists. split; [apply defs_update_var | reflexivity].
    + match goal with H : defs_update (rename_stored_defs rename ds) _ _ _ |- _ =>
        destruct (IH _ H) as (tl & Htl & <-)
      end.
      exists (defs_cons tl d). split; [|reflexivity].
      apply defs_update_push; [exact Htl |].
      now rewrite <- rename_stored_def_label with (rename := rename).
Qed.

Local Lemma heap_projection_update rename ha h h' y a yArg :
  heap_projects rename ha h ->
  heap_update h y a yArg h' ->
  exists ha', heap_update ha y a yArg ha' /\ heap_projects rename ha' h'.
Proof.
  intros [Hoka [Hok Hproj]]
    (Hok0 & Hok' & Hdom & Hothers & ds & ds' & Hbind & Hupd & Hbind').
  destruct (proj1 (Hproj y (item_obj ds)) Hbind) as (ia & Hia & Heq).
  destruct ia as [da|t]; simpl in Heq; [|discriminate].
  injection Heq as <-.
  destruct (@rename_stored_defs_update_inv rename da a yArg ds' Hupd) as (da' & HupdA & <-).
  destruct (env_replace_value (item_obj da') Hoka Hia)
    as (ha' & Hoka' & HdomA & Hia' & HotherA).
  exists ha'. split.
  { unfold heap_update. split; [exact Hoka |].
    split; [exact Hoka' |].
    split; [now symmetry |].
    split; [exact HotherA |].
    exists da, da'. auto. }
  split; [exact Hoka' |]. split; [exact Hok' |].
  intros l it. destruct (classic (l = y)) as [-> | Hneq].
  - split.
    + intro Hb. rewrite (binds_functional Hb Hbind').
      now exists (item_obj da').
    + intros (i & Hi & <-). rewrite (binds_functional Hi Hia').
      exact Hbind'.
  - split.
    + intro Hb'.
      assert (Hl : l \in dom h) by (rewrite Hdom; now apply get_some_inv in Hb').
      destruct (get_some Hl) as [j Hj].
      rewrite <- (binds_functional (Hothers _ _ Hneq Hj) Hb').
      destruct (proj1 (Hproj _ _) Hj) as (j0 & Hj0 & <-).
      exists j0. split; [now apply HotherA | reflexivity].
    + intros (i & Hi & <-).
      assert (Hl : l \in dom ha) by (rewrite <- HdomA; now apply get_some_inv in Hi).
      destruct (get_some Hl) as [j Hj].
      rewrite <- (binds_functional (HotherA _ _ Hneq Hj) Hi).
      apply Hothers; [exact Hneq |].
      apply (proj2 (Hproj _ _)). now exists j.
Qed.

Local Lemma projected_heap_object rename ha h y ds :
  heap_projects rename ha h ->
  binds y (item_obj ds) h ->
  exists data,
    binds y (item_obj data) ha /\ rename_stored_defs rename data = ds.
Proof.
  intros [_ [_ Hproj]] Hb.
  destruct (proj1 (Hproj _ _) Hb) as (i & Hi & Heq).
  destruct i as [data|funbody]; simpl in Heq; [|discriminate].
  injection Heq as <-. now exists data.
Qed.

Local Lemma projected_heap_function rename ha h y t :
  heap_projects rename ha h ->
  binds y (item_fun t) h ->
  exists body,
    binds y (item_fun body) ha /\ rename_trm rename body = t.
Proof.
  intros [_ [_ Hproj]] Hb.
  destruct (proj1 (Hproj _ _) Hb) as (i & Hi & Heq).
  destruct i as [data|funbody]; simpl in Heq; [discriminate |].
  injection Heq as <-. now exists funbody.
Qed.

Local Lemma renamed_free_variable rename a x :
  rename_avar rename a = avar_f x ->
  exists v, a = avar_f v /\ rename v = x.
Proof.
  destruct a as [index | v]; simpl; [discriminate |].
  intro H. injection H as <-. now exists v.
Qed.

Local Definition config_projects rename alias original :=
  rename_trm rename (config_trm alias) = config_trm original /\
  rename_stack rename (config_stack alias) = config_stack original /\
  heap_projects rename (config_heap alias) (config_heap original) /\
  env_projects rename (config_env alias) (config_env original).

Local Definition projects_fresh_names rename alias original :=
  forall xs, fresh_in_config xs original ->
    fresh_in_config xs alias /\ List.Forall (name_fixed_by rename) xs.

Local Definition projects_deref rename ca c :=
  forall w y ds,
    name_fixed_by rename w ->
    fresh_in_config (y :: w :: nil) ca ->
    fresh_in_config (y :: w :: nil) c ->
    rename_stored_defs rename (deref_defs (config_env ca & w ~ y) ds) =
    deref_defs (config_env c & w ~ y) (rename_defs rename ds).

Local Lemma allocation_fresh_heap c y w :
  fresh_in_config (y :: w :: nil) c ->
  y # (config_heap c).
Proof.
  destruct c. cbn. intros [Hy _].
  repeat rewrite notin_union in Hy. tauto.
Qed.

Local Lemma fresh_pair_projection rename ca c y w :
  projects_fresh_names rename ca c ->
  fresh_in_config (y :: w :: nil) c ->
  fresh_in_config (y :: w :: nil) ca /\ name_fixed_by rename w.
Proof.
  intros Hf Hfresh. destruct (Hf _ Hfresh) as [Hfa Hnames].
  split; [exact Hfa |].
  exact (List.Forall_inv (List.Forall_inv_tail Hnames)).
Qed.

Local Lemma fresh_single_projection rename ca c w :
  projects_fresh_names rename ca c ->
  fresh_in_config (w :: nil) c ->
  fresh_in_config (w :: nil) ca /\ name_fixed_by rename w.
Proof.
  intros Hf Hfresh. destruct (Hf _ Hfresh) as [Hfa Hnames].
  split; [exact Hfa | exact (List.Forall_inv Hnames)].
Qed.

Local Lemma project_reduction_step rename ca c d :
  config_projects rename ca c ->
  projects_fresh_names rename ca c ->
  projects_deref rename ca c ->
  c ↦ d ->
  exists da, ca ↦ da /\ config_projects rename da d.
Proof.
  intros Hproj Hfresh Halloc Hred.
  destruct ca as [ta sa ha ea La].
  destruct Hred as
    [yObj wObj m h e L yVal wVal ds st HfreshO Href Hobj Hfield
    |yObj wObj m h e L yArg wArg h' st Hupdate Href Harg
    |yObj wObj m h e L wArg body ds st Hobj Hmeth Href
    |yFun wFun wArg h e L body st Hfun Href
    |T body t h e L y w st HfreshO Hneq
    |T ds t h e L y w st HfreshO Hneq
    |t h e L x st
    |s t st h e L];
    destruct Hproj as (Hterm & Hstack & Hheap & Henv);
    cbn [config_trm config_stack config_heap config_env] in *.
  all: destruct ta as [ap | ap fld | ap aq | ta1 ta2 | alit ta2 | ap fld aq | ap meth aq];
    simpl in Hterm; try discriminate.
  - inversion Hterm; subst fld.
    destruct (@renamed_free_variable rename ap wObj ltac:(eassumption)) as (p & -> & Hp).
    destruct (fresh_single_projection Hfresh HfreshO) as [HfreshA Hfixed].
    destruct (projected_heap_object Hheap Hobj) as (da & Hd & <-).
    destruct (@rename_stored_defs_has_inv rename da (def_fld m (avar_f yVal)) Hfield)
      as (f & Hf & Heq).
    destruct f; simpl in Heq; try discriminate. inversion Heq; subst m;
      match goal with H : ?a = avar_f yVal |- _ => subst a end.
    eexists. split.
    + eapply red_read; [exact HfreshA | | exact Hd | exact Hf].
      apply Henv. now rewrite Hp.
    + split; [simpl; now rewrite (name_fixed_by_eq Hfixed) |].
      split; [exact Hstack |]. split; [exact Hheap |].
      now apply env_projection_push.
  - inversion Hterm; subst fld.
    destruct (@renamed_free_variable rename ap wObj ltac:(eassumption)) as (p & -> & Hp).
    destruct (@renamed_free_variable rename aq wArg ltac:(eassumption)) as (q & -> & Hq).
    destruct (heap_projection_update Hheap Hupdate) as (ha' & Hup & Hhp).
    eexists. split.
    + eapply red_write; [exact Hup | apply Henv; now rewrite Hp | apply Henv; now rewrite Hq].
    + split; [simpl; now rewrite Hq |].
      split; [exact Hstack |]. split; assumption.
  - inversion Hterm; subst meth.
    destruct (@renamed_free_variable rename ap wObj ltac:(eassumption)) as (p & -> & Hp).
    destruct (@renamed_free_variable rename aq wArg ltac:(eassumption)) as (q & -> & Hq).
    destruct (projected_heap_object Hheap Hobj) as (da & Hd & <-).
    destruct (@rename_stored_defs_has_inv rename da (def_met m body) Hmeth) as (f & Hf & Heq).
    destruct f; simpl in Heq; try discriminate. inversion Heq; subst m body.
    eexists. split.
    + eapply red_call; [exact Hd | exact Hf |].
      apply Henv. now rewrite Hp.
    + split.
      * cbn [config_trm]. rewrite !(proj1 (rename_trm_open rename)), Hp, Hq. reflexivity.
      * split; [exact Hstack |]. split; assumption.
  - inversion Hterm.
    destruct (@renamed_free_variable rename ap wFun ltac:(eassumption)) as (p & -> & Hp).
    destruct (@renamed_free_variable rename aq wArg ltac:(eassumption)) as (q & -> & Hq).
    destruct (projected_heap_function Hheap Hfun) as (bodya & Hb & <-).
    eexists. split.
    + eapply red_apply; [exact Hb | apply Henv; now rewrite Hp].
    + split.
      * cbn [config_trm]. now rewrite (proj1 (rename_trm_open rename)), Hq.
      * split; [exact Hstack |]. split; assumption.
  - destruct alit as [Ta bodya | Ta dsa]; simpl in Hterm; try discriminate.
    inversion Hterm; subst T body t.
    destruct (fresh_pair_projection Hfresh HfreshO) as [HfreshA Hfixed].
    eexists. split.
    + eapply red_let_fun; eassumption.
    + split.
      * cbn [config_trm]. now rewrite (proj1 (rename_trm_open rename)), (name_fixed_by_eq Hfixed).
      * split; [exact Hstack |]. split.
        -- apply heap_projection_push; [exact Hheap | |].
           ++ destruct HfreshA as [Hy _]. repeat rewrite notin_union in Hy. tauto.
           ++ destruct HfreshO as [Hy _]. repeat rewrite notin_union in Hy. tauto.
        -- now apply env_projection_push.
  - destruct alit as [Ta bodya | Ta dsa]; simpl in Hterm; try discriminate.
    inversion Hterm; subst T ds t.
    destruct (fresh_pair_projection Hfresh HfreshO) as [HfreshA Hfixed].
    assert (Hrename_def :
      rename_item rename (item_obj (deref_defs (ea & w ~ y) (open w dsa))) =
      item_obj (deref_defs (e & w ~ y) (open w (rename_defs rename dsa)))).
    { simpl. f_equal. rewrite Halloc by assumption.
      rewrite (proj2 (proj2 (proj2 (rename_trm_open rename)))), (name_fixed_by_eq Hfixed).
      reflexivity. }
    eexists. split.
    + eapply red_let_obj; eassumption.
    + split.
      * cbn [config_trm]. now rewrite (proj1 (rename_trm_open rename)), (name_fixed_by_eq Hfixed).
      * split; [exact Hstack |]. split.
        -- cbn [config_heap]. rewrite <- Hrename_def.
           apply heap_projection_push; [exact Hheap | |].
           ++ destruct HfreshA as [Hy _]. repeat rewrite notin_union in Hy. tauto.
           ++ destruct HfreshO as [Hy _]. repeat rewrite notin_union in Hy. tauto.
        -- now apply env_projection_push.
  - destruct (@renamed_free_variable rename ap x ltac:(now injection Hterm)) as (p & -> & Hp).
    destruct sa as [|fa sta]; [discriminate |].
    destruct fa as [ta]. simpl in Hstack. inversion Hstack; subst t st.
    eexists. split.
    + apply red_let_var.
    + split.
      * cbn [config_trm]. now rewrite (proj1 (rename_trm_open rename)), Hp.
      * split; [reflexivity |]. split; assumption.
  - inversion Hterm; subst s t.
    eexists. split.
    + apply red_let_push.
    + split; [reflexivity |].
      split; [simpl; now rewrite Hstack |]. split; assumption.
Qed.

Local Definition env_targets_are_locations (e : renv) :=
  forall w y, binds w y e -> y # e.

Local Lemma deref_avar_push (e : renv) w y (a : avar) :
  deref (e & w ~ y) a = deref e (subst_var w y a).
Proof.
  change (deref_base AvarSubstVar (e & w ~ y) a =
    deref_base AvarSubstVar e (subst_var w y a)).
  rewrite <- cons_to_push. reflexivity.
Qed.

Local Lemma deref_avar_unbound_index e n :
  deref e (avar_b n) = avar_b n.
Proof.
  induction e using env_ind.
  - change (deref_base AvarSubstVar empty (avar_b n) = avar_b n). now rewrite empty_def.
  - rewrite deref_avar_push. exact IHe.
Qed.

Local Lemma deref_avar_lookup e w :
  ok e ->
  env_targets_are_locations e ->
  deref e (avar_f w) =
    match get w e with Some y => avar_f y | None => avar_f w end.
Proof.
  revert w. induction e as [|e u y IH] using env_ind; intros w Hok Htargets.
  - assert (Hfresh : w # (empty : renv)) by (rewrite dom_empty; apply notin_empty).
    rewrite (get_none Hfresh).
    change (deref_base AvarSubstVar empty (avar_f w) = avar_f w).
    now rewrite empty_def.
  - destruct (ok_push_inv Hok) as [Hok0 Hfresh].
    assert (Htail : env_targets_are_locations e).
    { intros a b Hb. assert (Hne : a <> u).
      { intros ->. apply Hfresh. exact (get_some_inv Hb). }
      pose proof (Htargets _ _ (@binds_push_neq var a u b y e Hb Hne)) as Hloc.
      rewrite dom_push in Hloc. apply notin_union in Hloc as [_ Hloc]. exact Hloc. }
    rewrite deref_avar_push, get_push.
    cbn [subst_var AvarSubstVar]. case_if.
    + rewrite IH; [|exact Hok0 | exact Htail].
      pose proof (Htargets _ _ (binds_push_eq (A:=var) u y e)) as Hloc.
      rewrite dom_push in Hloc. apply notin_union in Hloc as [_ Hloc].
      now rewrite (get_none Hloc).
    + now apply IH.
Qed.

Local Lemma deref_projection_under_aliases rename ea e ds :
  ok ea -> ok e ->
  env_targets_are_locations ea -> env_targets_are_locations e ->
  env_projects rename ea e ->
  (forall w, w # ea -> rename w = w) ->
  rename_stored_defs rename (deref_defs ea ds) =
  deref_defs e (rename_defs rename ds).
Proof.
  intros Hoka Hok Hta Ht Hproj Hfix.
  induction ds as [|ds IH d]; [reflexivity |].
  simpl. f_equal; [exact IH |].
  destruct d as [l T |l v|l t]; try reflexivity.
  change (def_fld l (deref ea v) = def_fld l (deref e (rename_avar rename v))). f_equal.
  destruct v as [k|w].
  - simpl. now rewrite !deref_avar_unbound_index.
  - simpl. rewrite (@deref_avar_lookup ea w Hoka Hta), (@deref_avar_lookup e (rename w) Hok Ht).
    destruct (get w ea) as [y|] eqn:Hw.
    + pose proof (proj1 (Hproj w y) Hw) as Hlookup.
      change (get (rename w) e = Some y) in Hlookup. now rewrite Hlookup.
    + assert (Hnone : get (rename w) e = None).
      { destruct (get (rename w) e) as [y|] eqn:He; [|reflexivity].
        pose proof (proj2 (Hproj w y) He) as Hlookup.
        change (get w ea = Some y) in Hlookup. congruence. }
      rewrite Hnone. now rewrite Hfix by (exact (get_none_inv Hw)).
Qed.

Local Lemma projected_reduction_trace rename ca c n d :
  c ⊣n↦* d ->
  config_projects rename ca c ->
  (forall k c0 ca0,
    c ⊣k↦* c0 ->
    ca ⊣k↦* ca0 ->
    config_projects rename ca0 c0 ->
    projects_fresh_names rename ca0 c0 /\
    projects_deref rename ca0 c0) ->
  exists da, ca ⊣n↦* da /\ config_projects rename da d.
Proof.
  intros Hred. induction Hred as [c | c c0 c1 k Hreach IH Hstep]; intros Hinit Hcompat.
  - exists ca. split; [apply red_refl | exact Hinit].
  - destruct (IH Hinit Hcompat) as (ca0 & HreachA & Hproj).
    destruct (Hcompat k c0 ca0 Hreach HreachA Hproj) as [Hfresh Hderef].
    destruct (project_reduction_step Hproj Hfresh Hderef Hstep) as (ca1 & HstepA & Hproj1).
    exists ca1. split; [eapply red_trans; eassumption | exact Hproj1].
Qed.

Local Lemma projected_subheap_unchanged rename initial initial_alias final final_alias :
  heap_projects rename initial_alias initial ->
  heap_projects rename final_alias final ->
  subheap_unchanged initial_alias final_alias ->
  subheap_unchanged initial final.
Proof.
  intros [_ [_ Hinit]] [_ [_ Hfinal]] Hsame y v Hb.
  destruct (proj1 (Hinit y v) Hb) as (i & Hi & Heq).
  apply (proj2 (Hfinal y v)). exists i. auto.
Qed.

Local Lemma projected_method_opening rename body z r w1 w2 :
  rename_trm rename body = body ->
  rename r = w1 ->
  rename z = w2 ->
  rename_trm rename (open_met z r body) = open_met w2 w1 body.
Proof.
  intros Hbody Hr Hz.
  now rewrite !(proj1 (rename_trm_open rename)), Hbody, Hr, Hz.
Qed.

Local Lemma ctx_kind_lookup_unique G x k1 k2 T1 T2 P1 P2 :
  ctx_binds_k_after x k1 T1 G P1 ->
  ctx_binds_k_after x k2 T2 G P2 ->
  k1 = k2.
Proof.
  intro H. revert k2 T2 P2.
  induction H; intros k2 T2 P2 H'; inversion H'; subst; try congruence; eauto.
Qed.

Local Lemma renv_key_has_reference_kind mode G e w y :
  @renv_corr mode G e ->
  binds w y e ->
  exists T G0, ctx_binds_k_after w v_ref T G G0.
Proof.
  intro Henv. induction Henv; intro Hb.
  - contradiction (binds_empty_inv Hb).
  - apply binds_push_inv in Hb as [[-> ->] | [_ Hb]].
    + now exists Tw, G2.
    + now apply IHHenv.
Qed.

Local Lemma typed_heap_env_location_targets mode G e h :
  mode_has_mutability mode ->
  @heap_correspond mode G e h ->
  env_targets_are_locations e.
Proof.
  intros Hmode (Hok & _ & _ & _ & _ & _ & Hcorr & _) w y Hbind Hy.
  destruct (reference_location_kind Hmode Hok Hcorr Hbind)
    as (R & B & G0 & _ & Hlookloc).
  destruct (get_some Hy) as [v Hv].
  destruct (renv_key_has_reference_kind Hcorr Hv) as (T & P & Hlookref).
  discriminate (ctx_kind_lookup_unique Hlookloc Hlookref).
Qed.

Local Lemma allocation_fresh_env c y w :
  fresh_in_config (y :: w :: nil) c ->
  y # (config_env c) /\ w # (config_env c) /\
  w \notin fv_env (config_env c) /\ y <> w.
Proof.
  destruct c. cbn. intros [Hy [Hw _]].
  repeat rewrite notin_union in Hy. repeat rewrite notin_union in Hw.
  repeat rewrite notin_singleton in Hw. intuition congruence.
Qed.

Local Lemma env_location_targets_push e w y :
  env_targets_are_locations e ->
  y # e -> w \notin fv_env e -> y <> w ->
  env_targets_are_locations (e & w ~ y).
Proof.
  intros Hloc Hy Hw Hne k v Hb.
  apply binds_push_inv in Hb as [[-> ->] | [_ Hb]].
  - rewrite dom_push. apply notin_union. split; [now apply notin_singleton | exact Hy].
  - rewrite dom_push. apply notin_union. split.
    + apply notin_singleton.
      pose proof (@fv_in_values_binds var w fv k v e Hb Hw) as H.
      change (w \notin \{v}) in H. apply notin_singleton in H. congruence.
    + eapply Hloc; eassumption.
Qed.

Local Lemma projected_deref_for_fresh_objects rename ca c :
  ok (config_env ca) -> ok (config_env c) ->
  env_targets_are_locations (config_env ca) ->
  env_targets_are_locations (config_env c) ->
  env_projects rename (config_env ca) (config_env c) ->
  (forall w, w # (config_env ca) -> rename w = w) ->
  projects_deref rename ca c.
Proof.
  intros Hoka Hok Hloca Hloc Hproj Hfix w y ds Hname Hfa Hf.
  destruct (@allocation_fresh_env ca y w Hfa) as (Hva & Hwa & Hfva & Hneq).
  destruct (@allocation_fresh_env c y w Hf) as (Hv & Hw & Hfv & _).
  apply deref_projection_under_aliases.
  - now apply ok_push.
  - now apply ok_push.
  - now apply env_location_targets_push.
  - now apply env_location_targets_push.
  - now apply env_projection_push.
  - intros x Hx. apply Hfix.
    rewrite dom_push in Hx. now apply notin_union in Hx as [_ ?].
Qed.

Local Lemma rename_avar_identity rename a :
  (forall x, x \in fv a -> rename x = x) ->
  rename_avar rename a = a.
Proof.
  destruct a as [n | x]; [reflexivity |].
  intro H. simpl. f_equal. apply H. apply in_singleton_self.
Qed.

Local Ltac solve_identity_of_renamed_child :=
  intros x Hx;
  match goal with
  | H : forall x, x \in _ -> _ = x |- _ =>
      apply H; cbn [fv TypFreeVar DecFreeVar TrmFreeVar LitFreeVar DefFreeVar DefsFreeVar StackFreeVar FrameFreeVar fv_typ fv_dec fv_trm fv_lit fv_def fv_defs stack_fv frame_fv]; repeat rewrite in_union; tauto
  end.

Local Lemma rename_typ_identity rename :
  (forall T, (forall x, x \in fv T -> rename x = x) -> rename_typ rename T = T) /\
  (forall D, (forall x, x \in fv D -> rename x = x) -> rename_dec rename D = D).
Proof.
  apply typ_mutind; intros; cbn [rename_typ rename_dec] in *; try reflexivity.
  all: f_equal;
    first [solve [apply H; solve_identity_of_renamed_child] |
           solve [apply H0; solve_identity_of_renamed_child] |
           solve [apply H1; solve_identity_of_renamed_child] |
           solve [apply rename_avar_identity; solve_identity_of_renamed_child]].
Qed.

Local Lemma rename_term_identity rename :
  (forall t, (forall x, x \in fv t -> rename x = x) -> rename_trm rename t = t) /\
  (forall l, (forall x, x \in fv l -> rename x = x) -> rename_lit rename l = l) /\
  (forall d, (forall x, x \in fv d -> rename x = x) -> rename_def rename d = d) /\
  (forall ds, (forall x, x \in fv ds -> rename x = x) -> rename_defs rename ds = ds).
Proof.
  apply trm_mutind; intros; cbn [rename_trm rename_lit rename_def rename_defs] in *;
    try reflexivity.
  all: f_equal;
    first [solve [apply H; solve_identity_of_renamed_child] |
           solve [apply H0; solve_identity_of_renamed_child] |
           solve [apply (proj1 (rename_typ_identity rename)); solve_identity_of_renamed_child] |
           solve [apply rename_avar_identity; solve_identity_of_renamed_child]].
Qed.

Local Lemma rename_stored_defs_identity rename ds :
  (forall x, x \in fv ds -> rename x = x) ->
  rename_stored_defs rename ds = ds.
Proof.
  induction ds as [|ds IH d]; intro H; simpl; [reflexivity |].
  f_equal.
  - apply IH; solve_identity_of_renamed_child.
  - destruct d; simpl; try reflexivity; f_equal.
    + apply (proj1 (rename_typ_identity rename)); solve_identity_of_renamed_child.
    + apply (proj1 (rename_term_identity rename)); solve_identity_of_renamed_child.
Qed.

Local Lemma rename_stack_identity rename st :
  (forall x, x \in fv st -> rename x = x) ->
  rename_stack rename st = st.
Proof.
  induction st as [|[t] st IH]; intro H; simpl; [reflexivity |].
  f_equal.
  - f_equal. apply (proj1 (rename_term_identity rename)); solve_identity_of_renamed_child.
  - apply IH; solve_identity_of_renamed_child.
Qed.

Local Lemma heap_projects_identity rename h :
  ok h ->
  (forall y i x, binds y i h -> x \in fv i -> rename x = x) ->
  heap_projects rename h h.
Proof.
  intros Hok Hfix. split; [exact Hok |]. split; [exact Hok |].
  assert (Hid : forall y i, binds y i h -> rename_item rename i = i).
  { intros y [ds | t] Hb; simpl; f_equal.
    - apply rename_stored_defs_identity. intros x Hx. eapply Hfix; eassumption.
    - apply (proj1 (rename_term_identity rename)). intros x Hx. eapply Hfix; eassumption. }
  intros y i. split.
  - intro Hb. exists i. eauto.
  - intros (other & Hb & <-). now rewrite (Hid _ _ Hb).
Qed.

Local Lemma project_new_alias rename ea e w orig loc :
  env_projects rename ea e ->
  binds orig loc e ->
  env_projects (fun x => If x = w then orig else rename x) (ea & w ~ loc) e.
Proof.
  intros Henv Hbind x y. case_if.
  - subst x. split; intro Hb.
    + apply binds_push_inv in Hb as [[_ ->] | [Hne _]]; [exact Hbind | congruence].
    + pose proof (binds_functional Hb Hbind) as ->. apply binds_push_eq.
  - split; intro Hb.
    + apply Henv. eapply binds_push_neq_inv; eassumption.
    + apply binds_push_neq; [now apply Henv | assumption].
Qed.

Local Lemma projected_initial_method_bodies rename body st h ea e La L z r w1 w2 :
  rename r = w1 ->
  rename z = w2 ->
  (forall x, x \in fv body -> rename x = x) ->
  (forall x, x \in fv st -> rename x = x) ->
  (forall y i x, binds y i h -> x \in fv i -> rename x = x) ->
  ok h ->
  env_projects rename ea e ->
  config_projects rename (open_met z r body ; st ; h ; ea ; La)
    (open_met w2 w1 body ; st ; h ; e ; L).
Proof.
  intros Hr Hz Hbody Hstack Hheap Hok Henv.
  split.
  - apply projected_method_opening; [|exact Hr |exact Hz].
    now apply (proj1 (rename_term_identity rename)).
  - split; [now apply rename_stack_identity |].
    split; [now apply heap_projects_identity |exact Henv].
Qed.


Local Lemma fv_in_values_push_eq (A : Type) (F : A -> vars) E x v :
  fv_in_values F (E & x ~ v) = F v \u fv_in_values F E.
Proof.
  unfold fv_in_values. rewrite values_def. rewrite <- cons_to_push. reflexivity.
Qed.

Local Lemma fv_of_env_value_binds A (F : A -> vars) x (E : env A) :
  ok E ->
  x \in fv_in_values F E ->
  exists k v, binds k v E /\ x \in F v.
Proof.
  induction E as [|E w v IH] using env_ind; intros Hok Hfv.
  - unfold fv_in_values in Hfv. rewrite values_def, empty_def in Hfv.
    simpl in Hfv. contradiction (notin_empty Hfv).
  - rewrite fv_in_values_push_eq, in_union in Hfv.
    destruct Hfv as [Hv | Hold].
    + exists w, v. split; [apply binds_push_eq | exact Hv].
    + destruct (ok_push_inv Hok) as [Hok' Hfresh].
      destruct (IH Hok' Hold) as (k & u & Hku & Hu).
      exists k, u. split; [|exact Hu].
      apply binds_push_neq; [exact Hku|].
      intros ->. apply Hfresh. exact (get_some_inv Hku).
Qed.

Local Lemma fv_of_binding_is_env_fv A (F : A -> vars) (E : env A) x y (v : A) :
  binds y v E ->
  x \in F v ->
  x \in fv_in_values F E.
Proof.
  intros Hbind Hfv.
  destruct (classic (x \in fv_in_values F E)) as [Hin | Hout]; [exact Hin |].
  exfalso. eapply (@fv_in_values_binds A x F y v E); eassumption.
Qed.

Local Lemma rename_avar_keeps_fixed_fv rename a x :
  rename x = x -> x \in fv a -> x \in fv (rename_avar rename a).
Proof.
  destruct a as [n | v]; simpl; intros Hfix Hmem.
  - exact Hmem.
  - rewrite in_singleton in Hmem. subst v. rewrite Hfix. apply in_singleton_self.
Qed.

Local Lemma rename_type_keeps_fixed_fv rename :
  (forall T x, rename x = x -> x \in fv T -> x \in fv (rename_typ rename T)) /\
  (forall D x, rename x = x -> x \in fv D -> x \in fv (rename_dec rename D)).
Proof.
  apply typ_mutind; intros;
    cbn [rename_typ rename_dec fv TypFreeVar DecFreeVar fv_typ fv_dec] in *;
    repeat rewrite in_union in *;
    firstorder using rename_avar_keeps_fixed_fv.
Qed.

Local Lemma rename_term_keeps_fixed_fv rename :
  (forall t x, rename x = x -> x \in fv t -> x \in fv (rename_trm rename t)) /\
  (forall l x, rename x = x -> x \in fv l -> x \in fv (rename_lit rename l)) /\
  (forall d x, rename x = x -> x \in fv d -> x \in fv (rename_def rename d)) /\
  (forall ds x, rename x = x -> x \in fv ds -> x \in fv (rename_defs rename ds)).
Proof.
  pose proof (proj1 (rename_type_keeps_fixed_fv rename)) as Htyp.
  apply trm_mutind; intros;
    cbn [rename_trm rename_lit rename_def rename_defs fv TrmFreeVar LitFreeVar
      DefFreeVar DefsFreeVar fv_trm fv_lit fv_def fv_defs] in *;
    repeat rewrite in_union in *;
    firstorder using rename_avar_keeps_fixed_fv.
Qed.

Local Lemma rename_stack_keeps_fixed_fv rename st x :
  rename x = x -> x \in fv st -> x \in fv (rename_stack rename st).
Proof.
  induction st as [|[t] st IH]; intros Hfix Hfv; [exact Hfv |].
  change (x \in fv t \u fv st) in Hfv.
  change (x \in fv (rename_trm rename t) \u fv (rename_stack rename st)).
  rewrite in_union in Hfv |- *.
  destruct Hfv as [Hfv | Hfv].
  - left. eapply (proj1 (rename_term_keeps_fixed_fv rename)); eassumption.
  - right. now apply IH.
Qed.

Local Lemma rename_stored_defs_keeps_fixed_fv rename ds x :
  rename x = x -> x \in fv ds -> x \in fv (rename_stored_defs rename ds).
Proof.
  induction ds as [|ds IH d]; intros Hfix Hfv; [exact Hfv |].
  change (x \in fv ds \u fv d) in Hfv.
  change (x \in fv (rename_stored_defs rename ds) \u fv (rename_stored_def rename d)).
  rewrite in_union in Hfv |- *.
  destruct Hfv as [Hfv | Hfv].
  - left. now apply IH.
  - right. destruct d; [|exact Hfv|];
      eapply (proj1 (proj2 (proj2 (rename_term_keeps_fixed_fv rename)))); eassumption.
Qed.

Local Lemma rename_item_keeps_fixed_fv rename i x :
  rename x = x -> x \in fv i -> x \in fv (rename_item rename i).
Proof.
  destruct i; simpl; intros Hfix Hfv.
  - now apply rename_stored_defs_keeps_fixed_fv.
  - eapply (proj1 (rename_term_keeps_fixed_fv rename)); eassumption.
Qed.

Local Lemma heap_projected_fv rename ha h x :
  heap_projects rename ha h ->
  rename x = x ->
  x \in fv_heap ha ->
  x \in fv_heap h.
Proof.
  intros [Hoka [_ Hproj]] Hfix Hin.
  rewrite in_union in Hin |- *.
  destruct Hin as [Hdom | Hfv].
  - left. destruct (get_some Hdom) as [i Hi].
    eapply get_some_inv.
    apply (proj2 (Hproj x (rename_item rename i))). now exists i.
  - right. destruct (fv_of_env_value_binds fv Hoka Hfv) as (y & i & Hi & Hxi).
    apply (@fv_of_binding_is_env_fv item fv h x y (rename_item rename i)).
    + apply (proj2 (Hproj y (rename_item rename i))). now exists i.
    + now apply rename_item_keeps_fixed_fv.
Qed.

Local Lemma env_projected_fv rename ea e x :
  ok ea ->
  env_projects rename ea e ->
  rename x = x ->
  x \in fv_renv ea ->
  x \in fv_renv e.
Proof.
  intros Hoka Hproj Hfix Hin.
  rewrite in_union in Hin |- *.
  destruct Hin as [Hdom | Hfv].
  - left. destruct (get_some Hdom) as [y Hy].
    pose proof (proj1 (Hproj x y) Hy) as Hb. rewrite Hfix in Hb.
    now apply get_some_inv in Hb.
  - right. destruct (fv_of_env_value_binds fv Hoka Hfv) as (w & y & Hy & Hxy).
    apply (@fv_of_binding_is_env_fv var fv e x (rename w) y).
    + now apply Hproj.
    + exact Hxy.
Qed.

Local Definition projected_reserved_vars rename ca c :=
  forall x, rename x = x -> x \in config_fv ca -> x \in config_fv c.

Local Lemma config_projected_fv rename ca c x :
  config_projects rename ca c ->
  projected_reserved_vars rename ca c ->
  ok (config_env ca) ->
  rename x = x ->
  x \in fv_config ca ->
  x \in fv_config c.
Proof.
  destruct ca as [ta sa ha ea La].
  destruct c as [t st h e L].
  intros (Ht & Hs & Hheap & Henv) Hlv Hok Hfix Hin.
  cbn [config_trm config_stack config_heap config_env] in *.
  pose proof (@heap_projected_fv rename ha h x Hheap Hfix) as Hhf.
  pose proof (@env_projected_fv rename ea e x Hok Henv Hfix) as Hef.
  assert (Htf : x \in fv ta -> x \in fv t).
  { rewrite <- Ht. now apply (proj1 (rename_term_keeps_fixed_fv rename)). }
  assert (Hsf : x \in fv sa -> x \in fv st).
  { rewrite <- Hs. now apply rename_stack_keeps_fixed_fv. }
  assert (Hlf : x \in La -> x \in L) by (exact (Hlv x Hfix)).
  repeat rewrite in_union in Hin |- *.
  repeat rewrite in_union in Hhf, Hef.
  tauto.
Qed.

Local Lemma fresh_list_names_notin (V : vars) xs x :
  fresh V (length xs) xs -> List.In x xs -> x \notin V.
Proof.
  revert V. induction xs as [|y ys IH]; simpl; intros V Hfresh Hin.
  - contradiction.
  - destruct Hfresh as [Hy Hys]. destruct Hin as [-> | Hin].
    + exact Hy.
    + pose proof (IH _ Hys Hin) as H. now apply notin_union in H as [? _].
Qed.

Local Lemma transfer_fresh_list (V Va : vars) xs :
  fresh V (length xs) xs ->
  (forall x, List.In x xs -> x \in Va -> x \in V) ->
  fresh Va (length xs) xs.
Proof.
  revert V Va. induction xs as [|y ys IH]; simpl; intros V Va Hfresh Htransfer.
  - exact I.
  - destruct Hfresh as [Hy Htail]. split.
    + intro Hay. apply Hy. apply Htransfer; [now left | exact Hay].
    + eapply IH; [exact Htail |].
      intros x Hin. rewrite !in_union.
      intros [Ha | Ha]; [left | now right].
      apply Htransfer; [now right | exact Ha].
Qed.

Local Definition all_fresh_names_fixed rename c :=
  forall x, x \notin fv_config c -> name_fixed_by rename x.

Local Lemma freshness_of_projected_config rename ca c :
  config_projects rename ca c ->
  projected_reserved_vars rename ca c ->
  ok (config_env ca) ->
  all_fresh_names_fixed rename c ->
  projects_fresh_names rename ca c.
Proof.
  intros Hproj Hlv Hok Hfixed xs Hfresh.
  assert (Hnames : forall x, List.In x xs -> name_fixed_by rename x).
  { intros x Hin. apply Hfixed. eapply fresh_list_names_notin; eassumption. }
  split.
  - eapply transfer_fresh_list; [exact Hfresh |].
    intros x Hin Hmem.
    eapply (@config_projected_fv rename ca c x); try eassumption.
    now apply (name_fixed_by_eq (Hnames x Hin)).
  - apply List.Forall_forall. exact Hnames.
Qed.

Local Definition reserve_config_vars (L : vars) c :=
  match c with t ; s ; h ; e ; V => (t ; s ; h ; e ; V \u L) end.

Local Lemma reserved_config_free_vars L c :
  fv_config (reserve_config_vars L c) = fv_config c \u L.
Proof.
  destruct c; cbn [reserve_config_vars]. now repeat rewrite <- union_assoc.
Qed.

Local Lemma fresh_with_reservation (V L : vars) xs :
  fresh V (length xs) xs ->
  (forall x, List.In x xs -> x \notin L) ->
  fresh (V \u L) (length xs) xs.
Proof.
  intros Hfresh Havoid. eapply transfer_fresh_list; [exact Hfresh |].
  intros x Hin. rewrite in_union. intros [Hv | Hl]; [exact Hv |].
  contradiction (Havoid x Hin Hl).
Qed.

Local Lemma fresh_in_reserved_config c L xs :
  fresh_in_config xs c ->
  (forall x, List.In x xs -> x \notin L) ->
  fresh_in_config xs (reserve_config_vars L c).
Proof.
  rewrite reserved_config_free_vars.
  apply fresh_with_reservation.
Qed.

Local Ltac rewrite_reserved_step_target :=
  cbn [reserve_config_vars];
  match goal with
  | |- red (config_mk ?t ?s ?h ?e (?V \u ?R)) _ =>
      rewrite <- (reserved_config_free_vars R (config_mk t s h e V))
  end.

Local Lemma red_avoids_reservation c d :
  c ↦ d ->
  exists allocated,
    forall L, (forall x, x \in allocated -> x \notin L) ->
      reserve_config_vars L c ↦ reserve_config_vars L d.
Proof.
  intro Hred. destruct Hred.
  - exists (\{wVal}). intros L' Havoid.
    rewrite_reserved_step_target.
    eapply red_read; try eassumption.
    assert (Hnames : forall x, List.In x (wVal :: nil) -> x \notin L').
    { intros x Hx. apply Havoid. simpl in Hx. destruct Hx as [-> | []].
      apply in_singleton_self. }
    exact (@fresh_in_reserved_config
      (trm_read (avar_f wObj) m ; fs ; Sigma ; e ; Lv) L' (wVal :: nil) H Hnames).
  - exists (\{} : vars). intros L' _.
    rewrite_reserved_step_target.
    eapply red_write; eassumption.
  - exists (\{} : vars). intros L' _.
    rewrite_reserved_step_target.
    eapply red_call; eassumption.
  - exists (\{} : vars). intros L' _.
    rewrite_reserved_step_target.
    eapply red_apply; eassumption.
  - exists (\{y} \u \{w}). intros L' Havoid.
    rewrite_reserved_step_target.
    apply red_let_fun; [|assumption].
    assert (Hnames : forall x, List.In x (y :: w :: nil) -> x \notin L').
    { intros x Hx. apply Havoid. rewrite in_union. simpl in Hx.
      destruct Hx as [-> | [-> | []]]; [left | right]; apply in_singleton_self. }
    exact (@fresh_in_reserved_config
      (trm_lit (lit_fun T t1) t2 ; fs ; Sigma ; e ; Lv) L' (y :: w :: nil) H Hnames).
  - exists (\{y} \u \{w}). intros L' Havoid.
    rewrite_reserved_step_target.
    apply red_let_obj; [|assumption].
    assert (Hnames : forall x, List.In x (y :: w :: nil) -> x \notin L').
    { intros x Hx. apply Havoid. rewrite in_union. simpl in Hx.
      destruct Hx as [-> | [-> | []]]; [left | right]; apply in_singleton_self. }
    exact (@fresh_in_reserved_config
      (trm_lit (lit_obj T ds) t ; fs ; Sigma ; e ; Lv) L' (y :: w :: nil) H Hnames).
  - exists (\{} : vars). intros L' _.
    rewrite_reserved_step_target.
    apply red_let_var.
  - exists (\{} : vars). intros L' _.
    rewrite_reserved_step_target.
    apply red_let_push.
Qed.

Local Lemma trace_avoids_reservation c n d :
  c ⊣n↦* d ->
  exists allocated,
    forall L, (forall x, x \in allocated -> x \notin L) ->
      reserve_config_vars L c ⊣n↦* reserve_config_vars L d.
Proof.
  intro H. induction H as [c | c c0 c1 n Hred IH Hstep].
  - exists (\{} : vars). intros L _. apply red_refl.
  - destruct IH as [L0 H0].
    destruct (red_avoids_reservation Hstep) as [L1 H1].
    exists (L0 \u L1). intros L Havoid.
    eapply red_trans.
    + apply H0. intros x Hx. apply Havoid. rewrite in_union. now left.
    + apply H1. intros x Hx. apply Havoid. rewrite in_union. now right.
Qed.

Local Lemma all_fresh_names_fixed_step rename c d :
  c ↦ d ->
  all_fresh_names_fixed rename c ->
  all_fresh_names_fixed rename d.
Proof.
  intros Hred Hfixed x Hx. apply Hfixed.
  destruct Hred; simpl in Hx |- *.
  all: repeat rewrite notin_union in Hx; repeat rewrite notin_union; tauto.
Qed.

Local Lemma projected_reserved_vars_step rename ca c da d :
  config_projects rename ca c ->
  projected_reserved_vars rename ca c ->
  ok (config_env ca) ->
  ca ↦ da ->
  c ↦ d ->
  projected_reserved_vars rename da d.
Proof.
  intros Hproj Hreserved Hok Ha Ho x Hfix Hx.
  assert (Hcurrent : x \in fv_config ca).
  { destruct Ha; exact Hx. }
  pose proof (@config_projected_fv rename ca c x Hproj Hreserved Hok Hfix Hcurrent)
    as Hprojected.
  destruct Ho; exact Hprojected.
Qed.

Local Lemma names_reserved_are_unavailable rename L c :
  (forall x, x \notin L -> name_fixed_by rename x) ->
  all_fresh_names_fixed rename (reserve_config_vars L c).
Proof.
  intros Hfixed x Hfresh.
  rewrite reserved_config_free_vars in Hfresh.
  apply notin_union in Hfresh as [_ Hfresh]. now apply Hfixed.
Qed.

Local Lemma step_keeps_ok_env c d :
  c ↦ d ->
  ok (config_env c) ->
  ok (config_env d).
Proof.
  intros Hstep Henv. destruct Hstep; simpl in *; try exact Henv.
  all: apply ok_push; [exact Henv |].
  - destruct H as [Hfresh _]. repeat rewrite notin_union in Hfresh. tauto.
  - destruct H as [_ [Hfresh _]]. repeat rewrite notin_union in Hfresh. tauto.
  - destruct H as [_ [Hfresh _]]. repeat rewrite notin_union in Hfresh. tauto.
Qed.

Local Lemma trace_keeps_ok_env c d n :
  c ⊣n↦* d ->
  ok (config_env c) ->
  ok (config_env d).
Proof. intro H. induction H; eauto using step_keeps_ok_env. Qed.

Local Lemma red_does_not_remove_env_keys c d :
  c ↦ d ->
  forall x, x \in dom (config_env c) -> x \in dom (config_env d).
Proof.
  intros Hstep x Hin. destruct Hstep; simpl in *; try exact Hin.
  all: rewrite dom_push, in_union; now right.
Qed.

Local Lemma trace_does_not_remove_env_keys c d n :
  c ⊣n↦* d ->
  forall x, x \in dom (config_env c) -> x \in dom (config_env d).
Proof. intro H. induction H; eauto using red_does_not_remove_env_keys. Qed.

Local Lemma replay_with_reserved_names rename ca c n d :
  c ⊣n↦* d ->
  config_projects rename ca c ->
  projected_reserved_vars rename ca c ->
  ok (config_env c) ->
  ok (config_env ca) ->
  all_fresh_names_fixed rename c ->
  (forall x, x # (config_env ca) -> rename x = x) ->
  (forall k c0 ca0,
    c ⊣k↦* c0 ->
    ca ⊣k↦* ca0 ->
    config_projects rename ca0 c0 ->
    env_targets_are_locations (config_env ca0) /\
    env_targets_are_locations (config_env c0)) ->
  exists da,
    ca ⊣n↦* da /\
    config_projects rename da d /\
    projected_reserved_vars rename da d /\
    all_fresh_names_fixed rename d.
Proof.
  intro Hred. induction Hred as [c | c c0 c1 k Hred IH Hstep].
  - intros Hproj Hlv Hok Hoka Hfixed Hsupport Htargets.
    exists ca. split; [apply red_refl | auto].
  - intros Hproj Hlv Hok Hoka Hfixed Hsupport Htargets.
    destruct (IH Hproj Hlv Hok Hoka Hfixed Hsupport Htargets)
      as (ca0 & HtraceA & Hproj0 & Hlv0 & Hfix0).
    pose proof (trace_keeps_ok_env HtraceA Hoka) as Hoka0.
    pose proof (trace_keeps_ok_env Hred Hok) as Hok0.
    assert (Hsupport0 : forall w, w # (config_env ca0) -> rename w = w).
    { intros w Hw. apply Hsupport.
      intro Hin. apply Hw. eapply trace_does_not_remove_env_keys; eassumption. }
    destruct (Htargets k c0 ca0 Hred HtraceA Hproj0) as [HtargetsA Htargets0].
    pose proof (freshness_of_projected_config Hproj0 Hlv0 Hoka0 Hfix0) as Hfresh0.
    assert (Hderef : projects_deref rename ca0 c0).
    { destruct Hproj0 as (_ & _ & _ & Henv0).
      now apply projected_deref_for_fresh_objects. }
    destruct (project_reduction_step Hproj0 Hfresh0 Hderef Hstep)
      as (ca1 & HstepA & Hproj1).
    exists ca1. split; [eapply red_trans; eassumption |].
    split; [exact Hproj1 |].
    split; [exact (@projected_reserved_vars_step rename ca0 c0 ca1 c1 Hproj0 Hlv0 Hoka0 HstepA Hstep) |].
    exact (@all_fresh_names_fixed_step rename c0 c1 Hstep Hfix0).
Qed.

Local Definition refs_in (V : vars) t :=
  forall x, tfree_trm x t -> x \in V.

Local Definition stack_refs_in (V : vars) s :=
  forall x, tfree_stack x s -> x \in V.

Local Definition locations_in (P : vars) (a : avar) :=
  match a with avar_f y => y \in P | avar_b _ => True end.

Local Definition stored_def_scoped (V P : vars) d :=
  match d with
  | def_fld _ a => locations_in P a
  | def_met _ t => refs_in V t
  | def_typ _ _ => True
  end.

Local Fixpoint stored_defs_scoped (V P : vars) ds :=
  match ds with
  | defs_nil => True
  | defs_cons ds d => stored_defs_scoped V P ds /\ stored_def_scoped V P d
  end.

Local Definition stored_item_scoped (V P : vars) i :=
  match i with
  | item_obj ds => stored_defs_scoped V P ds
  | item_fun t => refs_in V t
  end.

Local Definition env_heap_placement (e : renv) (h : heap) :=
  (forall r y, binds r y e -> y \in dom h) /\
  (forall y, y \in dom h -> y # e).

Local Definition config_has_scoped_locations c :=
  let e := config_env c in
  let h := config_heap c in
  ok e /\
  env_heap_placement e h /\
  refs_in (dom e) (config_trm c) /\
  stack_refs_in (dom e) (config_stack c) /\
  forall y i, binds y i h -> stored_item_scoped (dom e) (dom h) i.

Local Lemma refs_in_open V t k x :
  refs_in V t -> x \in V -> refs_in V (open_rec k x t).
Proof.
  intros Ht Hx v Hv.
  destruct ((proj1 tfree_open_backward) _ _ _ _ Hv) as [-> | Hfree]; auto.
Qed.

Local Lemma refs_in_push (Env : renv) w y t :
  refs_in (dom Env) t -> refs_in (dom (Env & w ~ y)) t.
Proof.
  intros Hscope x Hx. rewrite dom_push, in_union. now right; apply Hscope.
Qed.

Local Lemma stack_refs_in_push (Env : renv) w y s :
  stack_refs_in (dom Env) s -> stack_refs_in (dom (Env & w ~ y)) s.
Proof.
  intros Hscope x Hx. rewrite dom_push, in_union. now right; apply Hscope.
Qed.

Local Lemma env_binds_in_heap_after_read e h w y :
  env_heap_placement e h ->
  y \in dom h ->
  w # h ->
  env_heap_placement (e & w ~ y) h.
Proof.
  intros [Hloc Hdisjoint] Hy Hw. split.
  - intros x u Hb. apply binds_push_inv in Hb as [[_ ->] | [_ Hb]]; eauto.
  - intros x Hx. rewrite dom_push. apply notin_union. split.
    + apply notin_singleton. intros ->. contradiction.
    + now apply Hdisjoint.
Qed.

Local Lemma env_placement_alloc e h w y i :
  env_heap_placement e h ->
  w # h -> y # e -> w <> y ->
  env_heap_placement (e & w ~ y) (h & y ~ i).
Proof.
  intros [Hloc Hdisjoint] Hw Hy Hneq. split.
  - intros x z Hb. rewrite dom_push, in_union.
    apply binds_push_inv in Hb as [[_ ->] | [_ Hb]].
    + left. apply in_singleton_self.
    + right. eauto.
  - intros x Hx. rewrite dom_push, in_union, in_singleton in Hx.
    rewrite dom_push. apply notin_union. split.
    + apply notin_singleton. destruct Hx as [-> | Hx]; [congruence|].
      intros ->. contradiction.
    + destruct Hx as [-> | Hx]; [exact Hy | now apply Hdisjoint].
Qed.

Local Lemma stored_def_scope_mono V P V' P' d :
  (forall x, x \in V -> x \in V') ->
  (forall x, x \in P -> x \in P') ->
  stored_def_scoped V P d ->
  stored_def_scoped V' P' d.
Proof.
  destruct d; simpl; intros HV HP Hd; try exact I.
  - destruct a; simpl in *; auto.
  - intros x Hx. auto.
Qed.

Local Lemma stored_item_scope_mono V P V' P' i :
  (forall x, x \in V -> x \in V') ->
  (forall x, x \in P -> x \in P') ->
  stored_item_scoped V P i ->
  stored_item_scoped V' P' i.
Proof.
  intros HV HP. destruct i; simpl.
  - induction d; simpl; [auto |].
    intros [Hds Hd]. split; [auto | eapply stored_def_scope_mono; eassumption].
  - intros Ht x Hx. auto.
Qed.

Local Lemma stored_def_in_scope V P ds d :
  stored_defs_scoped V P ds ->
  defs_has ds d ->
  stored_def_scoped V P d.
Proof.
  induction ds; simpl; intros Hscope Hhas; unfold defs_has in Hhas; simpl in Hhas.
  - discriminate.
  - destruct Hscope as [Hds Hd].
    case_if.
    + inversion Hhas; subst. assumption.
    + now apply IHds.
Qed.

Local Lemma stored_scope_field_update V P ds a y ds' :
  defs_update ds a y ds' ->
  y \in P ->
  stored_defs_scoped V P ds ->
  stored_defs_scoped V P ds'.
Proof.
  induction 1; simpl; intuition.
Qed.

Local Lemma dereffed_def_scoped e P d :
  ok e ->
  env_targets_are_locations e ->
  (forall r y, binds r y e -> y \in P) ->
  (forall x, tfree_def x d -> x \in dom e) ->
  stored_def_scoped (dom e) P (deref_def e d).
Proof.
  intros Hok Hid Hloc Hrefs.
  destruct d; simpl; try exact I.
  - destruct a as [k|w].
    + rewrite deref_avar_unbound_index. exact I.
    + assert (Hw : w \in dom e) by (apply Hrefs; constructor).
      destruct (get_some Hw) as [y Hy].
      rewrite (@deref_avar_lookup e w Hok Hid), Hy.
      simpl. eauto.
  - intros v Hv. apply Hrefs. now constructor.
Qed.

Local Lemma dereffed_defs_scoped e P ds :
  ok e ->
  env_targets_are_locations e ->
  (forall r y, binds r y e -> y \in P) ->
  (forall x, tfree_defs x ds -> x \in dom e) ->
  stored_defs_scoped (dom e) P (deref_defs e ds).
Proof.
  induction ds; simpl; intros Hok Hid Hloc Hrefs; [exact I |].
  split.
  - apply IHds; try assumption. intros x Hx. apply Hrefs. now constructor.
  - apply dereffed_def_scoped; try assumption. intros x Hx.
    apply Hrefs. now apply tfree_defs_cons_r.
Qed.

Local Lemma ctx_kind_determined_by_domain G k y :
  ctx_ok G ->
  ctx_weakens G ->
  y \in ctx_kdom k G ->
  exists T G0, ctx_binds_k_after y k T G G0.
Proof.
  intros Hok Hweak. induction Hweak; intro Hy; simpl in Hy.
  - contradiction (notin_empty Hy).
  - inversion Hok; subst.
    case_if.
    + subst vk. rewrite in_union, in_singleton in Hy.
      destruct Hy as [-> | Hy].
      * eexists _, _. apply ctx_binds_k_e.
      * destruct (IHHweak ltac:(assumption) Hy) as (U & G0 & HU).
        exists U, G0. now apply fresh_push_preserves_kind_lookup.
    + destruct (IHHweak ltac:(assumption) Hy) as (U & G0 & HU).
      exists U, G0. now apply fresh_push_preserves_kind_lookup.
Qed.

Local Lemma typed_heap_places_refs_and_locations mode G e h :
  mode_has_mutability mode ->
  @heap_correspond mode G e h ->
  env_heap_placement e h.
Proof.
  intros Hmode (Hok & Hweak & _ & _ & Hlocdom & Hrefdom & Hcorr & _).
  split.
  - intros w y Hbind.
    destruct (reference_location_kind Hmode Hok Hcorr Hbind)
      as (R & B & G0 & _ & Hkind).
    rewrite <- Hlocdom. eapply ctx_binding_kind_in_dom. exact Hkind.
  - intros y Hy Hbad.
    apply get_some in Hbad as [z Hz].
    rewrite <- Hlocdom in Hy.
    destruct (ctx_kind_determined_by_domain v_loc Hok Hweak Hy) as (R & G0 & Hloc).
    destruct (renv_key_has_reference_kind Hcorr Hz) as (T & P & Href).
    discriminate (ctx_kind_lookup_unique Hloc Href).
Qed.

Local Lemma varkinds_scope_stored_defs G ds :
  defs_varkinds G ds ->
  stored_defs_scoped (ctx_kdom v_ref G) (ctx_kdom v_loc G) ds.
Proof.
  induction 1; simpl; [exact I |].
  split; [exact IHdefs_varkinds |].
  destruct H0 as [G x l Hloc|G T l|G t l Hrefs]; simpl; try exact I.
  - destruct Hloc as (T & G0 & Hloc). eapply ctx_binding_kind_in_dom; exact Hloc.
  - intros v Hfree. destruct (Hrefs v Hfree) as (T & G0 & Href).
    eapply ctx_binding_kind_in_dom; eassumption.
Qed.

Local Lemma typed_heap_items_are_scoped mode G e h :
  @heap_correspond mode G e h ->
  forall y i, binds y i h -> stored_item_scoped (dom e) (dom h) i.
Proof.
  intros (_ & _ & _ & _ & Hd & He & _ & Hitems) y i Hi.
  specialize (Hitems y (get_some_inv Hi)).
  destruct Hitems as [G e h y S t L T Hmode Hy Hb Ht Hrefs
    |G e h y R B ds T Hy Hb Heq Hds Hrefs].
  - rewrite (binds_functional Hi Hb). simpl. rewrite <- He. intros x Hx.
    destruct (Hrefs x Hx) as (U & G0 & Href).
    eapply ctx_binding_kind_in_dom. exact Href.
  - rewrite (binds_functional Hi Hb). simpl. rewrite <- He, <- Hd.
    now apply varkinds_scope_stored_defs.
Qed.

Local Lemma typed_config_has_placement mode G c U :
  mode_has_mutability mode ->
  @ty_config mode G c U ->
  config_has_scoped_locations c.
Proof.
  intros Hmode Htyped. destruct Htyped.
  cbv beta zeta in *.
  match goal with Hheap : @heap_correspond mode G e Sigma |- _ =>
    pose proof (typed_heap_places_refs_and_locations Hmode Hheap) as Hplace;
    pose proof (typed_heap_items_are_scoped Hheap) as Hitems0;
    destruct Hheap as (_ & _ & _ & Henvok & _ & Hdom & _)
  end.
  unfold config_has_scoped_locations. simpl.
  split; [exact Henvok |].
  split; [exact Hplace |].
  split.
  - intros x Hx. rewrite <- Hdom.
    match goal with H : all_tfree_k G t v_ref |- _ =>
      destruct (H x Hx) as (R & G0 & Href)
    end.
    eapply ctx_binding_kind_in_dom. exact Href.
  - split.
    + intros x Hx. rewrite <- Hdom.
      match goal with H : all_tfree_k_stack G s v_ref |- _ =>
        destruct (H x Hx) as (R & G0 & Href)
      end.
      eapply ctx_binding_kind_in_dom. exact Href.
    + exact Hitems0.
Qed.

Local Lemma fixed_name_outside_fresh_domains c xs x :
  fresh_in_config xs c ->
  List.In x xs ->
  x # (config_heap c) /\ x # (config_env c).
Proof.
  intros Hfresh Hx. pose proof (@fresh_list_names_notin (fv_config c) xs x Hfresh Hx) as Hnot.
  destruct c. simpl in Hnot |- *. repeat rewrite notin_union in Hnot. tauto.
Qed.

Local Lemma heap_scope_after_reference (e : renv) (h : heap) (w y : var) :
  (forall x i, binds x i h -> stored_item_scoped (dom e) (dom h) i) ->
  forall x i, binds x i h -> stored_item_scoped (dom (e & w ~ y)) (dom h) i.
Proof.
  intros Hscope x i Hi. apply (@stored_item_scope_mono (dom e) (dom h)).
  - intros v Hv. rewrite dom_push, in_union. now right.
  - auto.
  - now apply Hscope in Hi.
Qed.

Local Lemma heap_scope_after_object (e : renv) (h : heap) (w y : var) i0 :
  (forall x i, binds x i h -> stored_item_scoped (dom e) (dom h) i) ->
  stored_item_scoped (dom (e & w ~ y)) (dom (h & y ~ i0)) i0 ->
  forall x i, binds x i (h & y ~ i0) ->
    stored_item_scoped (dom (e & w ~ y)) (dom (h & y ~ i0)) i.
Proof.
  intros Hscope Hi0 x i Hi.
  apply binds_push_inv in Hi as [[_ ->] | [_ Hi]]; [exact Hi0 |].
  apply (@stored_item_scope_mono (dom e) (dom h)).
  - intros v Hv. rewrite dom_push, in_union; now right.
  - intros v Hv. rewrite dom_push, in_union; now right.
  - now apply Hscope in Hi.
Qed.

Local Lemma heap_scope_after_update (e : renv) h h' y a loc :
  loc \in dom h ->
  heap_update h y a loc h' ->
  (forall x i, binds x i h -> stored_item_scoped (dom e) (dom h) i) ->
  forall x i, binds x i h' -> stored_item_scoped (dom e) (dom h') i.
Proof.
  intros Hloc (_ & _ & Hdom & Hother & ds & ds' & Hb & Hupd & Hb') Hscope x i Hi.
  rewrite <- Hdom.
  destruct (classic (x = y)) as [-> | Hneq].
  - rewrite (binds_functional Hi Hb'). simpl.
    eapply stored_scope_field_update; [exact Hupd | exact Hloc | exact (Hscope _ _ Hb)].
  - assert (Hx : x \in dom h) by (rewrite Hdom; now apply get_some_inv in Hi).
    destruct (get_some Hx) as [j Hj].
    rewrite <- (binds_functional (Hother _ _ Hneq Hj) Hi).
    now apply Hscope in Hj.
Qed.

Local Lemma deref_scope_of_literal e h w y ds i :
  ok (e & w ~ y) ->
  env_heap_placement (e & w ~ y) (h & y ~ i) ->
  (forall v, tfree_defs v ds -> v \in dom e) ->
  stored_defs_scoped (dom (e & w ~ y)) (dom (h & y ~ i))
    (deref_defs (e & w ~ y) (open w ds)).
Proof.
  intros Hok [Hloc Hdisjoint] Hrefs.
  apply dereffed_defs_scoped; try assumption.
  - intros a b Hb. apply Hdisjoint. eauto.
  - intros x Hx. rewrite dom_push, in_union.
    destruct ((proj2 (proj2 (proj2 tfree_open_backward))) _ _ _ _ Hx)
      as [-> | Hx0].
    + left. apply in_singleton_self.
    + right. now apply Hrefs.
Qed.

Local Lemma scoped_locations_step c d :
  c ↦ d ->
  config_has_scoped_locations c ->
  config_has_scoped_locations d.
Proof.
  intros Hred (Hok & Hplace & Hterm & Hstack & Hheap).
  pose proof (step_keeps_ok_env Hred Hok) as Hok'.
  destruct Hred as
    [yObj wObj m h e L yVal wVal ds fs Hfresh Hobj Hb Hfield
    |yObj wObj m h e L yArg wArg h' fs Hupdate Hobj Harg
    |yObj wObj m h e L wArg t ds fs Hb Hmethod Hobj
    |yFun wFun wArg h e L t fs Hb Hfun
    |T t1 t2 h e L y w fs Hfresh Hne
    |T ds t h e L y w fs Hfresh Hne
    |t h e L x fs
    |s t fs h e L]; simpl in *; unfold config_has_scoped_locations; simpl;
    (split; [exact Hok' |]).
  - destruct (@fixed_name_outside_fresh_domains (trm_read (avar_f wObj) m ; fs ; h ; e ; L) (wVal :: nil) wVal Hfresh
        ltac:(now left)) as [Hwh _].
    split.
    + apply env_binds_in_heap_after_read; try assumption.
      exact (@stored_def_in_scope _ _ _ _ (Hheap _ _ Hb) Hfield).
    + split.
      * intros x Hx. inversion Hx; subst. rewrite dom_push, in_union.
        left. apply in_singleton_self.
      * split.
        -- now apply stack_refs_in_push.
        -- now apply heap_scope_after_reference.
  - destruct Hplace as [Hloc Hdisjoint].
    split.
    + destruct Hupdate as (_ & _ & Hdom & _). unfold env_heap_placement.
      now rewrite <- Hdom.
    + split.
      * intros x Hx. inversion Hx; subst. eapply get_some_inv. exact Harg.
      * split; [exact Hstack |].
        eapply heap_scope_after_update; [exact (Hloc _ _ Harg) | exact Hupdate | exact Hheap].
  - split; [exact Hplace |]. split; [| now split].
    apply refs_in_open.
    + apply refs_in_open.
      * exact (@stored_def_in_scope _ _ _ _ (Hheap _ _ Hb) Hmethod).
      * apply Hterm. apply tfree_trm_call_l.
    + apply Hterm. apply tfree_trm_call_r.
  - split; [exact Hplace |]. split; [| now split].
    apply refs_in_open.
    + exact (Hheap _ _ Hb).
    + apply Hterm. apply tfree_trm_apply_r.
  - destruct (@fixed_name_outside_fresh_domains (trm_lit (lit_fun T t1) t2 ; fs ; h ; e ; L) (y :: w :: nil) w Hfresh
        ltac:(right; now left)) as [Hwh _].
    destruct (@fixed_name_outside_fresh_domains (trm_lit (lit_fun T t1) t2 ; fs ; h ; e ; L) (y :: w :: nil) y Hfresh
        ltac:(now left)) as [_ Hye].
    split; [apply env_placement_alloc; auto |].
    split.
    + apply refs_in_open.
      * apply refs_in_push. intros x Hx. apply Hterm. now apply tfree_trm_lit_r.
      * rewrite dom_push, in_union. left. apply in_singleton_self.
    + split; [now apply stack_refs_in_push |].
      apply heap_scope_after_object; [exact Hheap |].
      simpl. apply refs_in_push. intros x Hx. apply Hterm.
      apply tfree_trm_lit_l. now apply tfree_lit_fun.
  - destruct (@fixed_name_outside_fresh_domains (trm_lit (lit_obj T ds) t ; fs ; h ; e ; L) (y :: w :: nil) w Hfresh
        ltac:(right; now left)) as [Hwh _].
    destruct (@fixed_name_outside_fresh_domains (trm_lit (lit_obj T ds) t ; fs ; h ; e ; L) (y :: w :: nil) y Hfresh
        ltac:(now left)) as [_ Hye].
    pose proof (@env_placement_alloc e h w y
      (item_obj (deref_defs (e & w ~ y) (open w ds))) Hplace Hwh Hye Hne) as Halloc.
    split; [exact Halloc |]. split.
    + apply refs_in_open.
      * apply refs_in_push. intros x Hx. apply Hterm. now apply tfree_trm_lit_r.
      * rewrite dom_push, in_union. left. apply in_singleton_self.
    + split; [now apply stack_refs_in_push |].
      apply heap_scope_after_object; [exact Hheap |].
      simpl. apply deref_scope_of_literal; try assumption.
      intros x Hx. apply Hterm. apply tfree_trm_lit_l. now apply tfree_lit_obj.
  - split; [exact Hplace |]. split.
    + apply refs_in_open.
      * intros v Hv. apply Hstack. now apply tfree_stack_cons_l.
      * apply Hterm. apply tfree_trm_var.
    + split; [| exact Hheap].
      intros v Hv. apply Hstack. now apply tfree_stack_cons_r.
  - split; [exact Hplace |]. split.
    + intros v Hv. apply Hterm. now apply tfree_trm_let_l.
    + split; [| exact Hheap].
      intros v Hv. inversion Hv; subst; auto using tfree_trm_let_r.
Qed.

Local Lemma scoped_locations_trace c n d :
  c ⊣n↦* d ->
  config_has_scoped_locations c ->
  config_has_scoped_locations d.
Proof.
  induction 1; eauto using scoped_locations_step.
Qed.

Local Lemma scoped_locations_env_targets c :
  config_has_scoped_locations c ->
  env_targets_are_locations (config_env c).
Proof.
  intros (_ & [Himage Hloc] & _). intros w y Hb.
  apply Hloc. eauto.
Qed.

Local Lemma scoped_replay_with_reserved_names rename ca c n d :
  c ⊣n↦* d ->
  config_projects rename ca c ->
  projected_reserved_vars rename ca c ->
  all_fresh_names_fixed rename c ->
  config_has_scoped_locations ca ->
  config_has_scoped_locations c ->
  (forall w, w # (config_env ca) -> rename w = w) ->
  exists da, ca ⊣n↦* da /\ config_projects rename da d.
Proof.
  intros Hred Hproj Hreserved Hfixed HscA Hsc Hsupport.
  assert (Htargets : forall k c0 ca0,
      c ⊣k↦* c0 ->
      ca ⊣k↦* ca0 ->
      config_projects rename ca0 c0 ->
      env_targets_are_locations (config_env ca0) /\
      env_targets_are_locations (config_env c0)).
  { intros k c0 ca0 Hr HrA _. split; apply scoped_locations_env_targets;
      eapply scoped_locations_trace; eassumption. }
  destruct HscA as (HokA & _). destruct Hsc as (Hok & _).
  destruct (replay_with_reserved_names Hred Hproj Hreserved Hok HokA Hfixed
    Hsupport Htargets) as (da & Htrace & Hproject & _).
  now exists da.
Qed.

Local Definition method_alias_name z0 z r w1 w2 (x : var) :=
  If x = r then w1 else If x = z then w2 else If x = z0 then w2 else x.

Local Definition method_alias_set (z0 z r : var) : vars := \{ r} \u \{ z} \u \{ z0}.

Local Lemma method_alias_fixes z0 z r w1 w2 x :
  x \notin method_alias_set z0 z r ->
  method_alias_name z0 z r w1 w2 x = x.
Proof.
  unfold method_alias_set, method_alias_name. intro H.
  repeat case_if; try reflexivity; subst x; exfalso; apply H;
    repeat rewrite in_union; auto using in_singleton_self.
Qed.

Local Lemma method_alias_fixes_uniquely z0 z r w1 w2 x :
  x \notin method_alias_set z0 z r ->
  x <> w1 -> x <> w2 ->
  name_fixed_by (method_alias_name z0 z r w1 w2) x.
Proof.
  intros Hx H1 H2 v. split; intro H.
  - unfold method_alias_name in H.
    repeat case_if; congruence.
  - subst v. now apply method_alias_fixes.
Qed.

Local Lemma method_alias_projection e z0 z r w1 w2 y1 y2 :
  binds w1 y1 e -> binds w2 y2 e ->
  env_projects (method_alias_name z0 z r w1 w2)
    (e & z0 ~ y2 & z ~ y2 & r ~ y1) e.
Proof.
  intros H1 H2. apply project_new_alias; [|exact H1].
  apply project_new_alias; [|exact H2].
  apply project_new_alias; [|exact H2].
  unfold env_projects. tauto.
Qed.

Local Lemma method_aliases_in_environment (e : renv) z0 z r (y1 y2 : var) :
  forall x, x \in method_alias_set z0 z r ->
  x \in dom (e & z0 ~ y2 & z ~ y2 & r ~ y1).
Proof.
  unfold method_alias_set.
  intros x Hx. repeat rewrite dom_push; repeat rewrite in_union in *; repeat rewrite in_singleton in *.
  tauto.
Qed.

Local Lemma scoped_method_aliases body st h e L w1 w2 z0 z r y1 y2 :
  let c := (open_met w2 w1 body ; st ; h ; e ; L) in
  config_has_scoped_locations c ->
  z0 \notin fv_config c -> z \notin fv_config c -> r \notin fv_config c ->
  z <> r -> z0 <> r -> z0 <> z ->
  binds w1 y1 e ->
  binds w2 y2 e ->
  config_has_scoped_locations
    (open_met z r body ; st ; h ; e & z0 ~ y2 & z ~ y2 & r ~ y1 ; L).
Proof.
  intros c (Hok & Hplace & Hterm & Hstack & Hitems)
    Hz0 Hz Hr Hzr Hz0r Hz0z H1 H2.
  unfold c in *. simpl in *.
  all: repeat rewrite notin_union in Hz0, Hz, Hr.
  destruct Hplace as [Hloc Hdis].
  pose proof (Hloc _ _ H1) as Hy1.
  pose proof (Hloc _ _ H2) as Hy2.
  unfold config_has_scoped_locations. simpl.
  split.
  - apply ok_push; [apply ok_push; [apply ok_push; [exact Hok | tauto] |] |].
    all: repeat rewrite dom_push; repeat rewrite notin_union;
      repeat split; try tauto; apply notin_singleton; congruence.
  - split.
    + apply env_binds_in_heap_after_read; [|exact Hy1|tauto].
      apply env_binds_in_heap_after_read; [|exact Hy2|tauto].
      apply env_binds_in_heap_after_read; [now split | exact Hy2 | tauto].
    + split.
      * apply refs_in_open.
        -- apply refs_in_open.
           ++ repeat apply refs_in_push. intros x Hx. apply Hterm.
              do 2 apply (proj1 tfree_open_forward). exact Hx.
           ++ rewrite dom_push, in_union. left. apply in_singleton_self.
        -- rewrite !dom_push. repeat rewrite in_union.
           right. left. apply in_singleton_self.
      * split.
        -- now do 3 apply stack_refs_in_push.
        -- now do 3 apply heap_scope_after_reference.
Qed.

Local Lemma fresh_method_alias_trace body st h e L w1 w2 n d :
  let c := (open_met w2 w1 body ; st ; h ; e ; L) in
  c ⊣n↦* d ->
  config_has_scoped_locations c ->
  ok h ->
  exists avoid : vars, forall z0 z r y1 y2,
    z0 \notin avoid -> z \notin avoid -> r \notin avoid ->
    z <> r -> z0 <> r -> z0 <> z ->
    binds w1 y1 e ->
    binds w2 y2 e ->
    let ca := (open_met z r body ; st ; h ; e & z0 ~ y2 & z ~ y2 & r ~ y1 ; L) in
    exists da,
      ca ⊣n↦* da /\
      config_projects (method_alias_name z0 z r w1 w2) da d.
Proof.
  intros c Hred Hscope Hok.
  destruct (trace_avoids_reservation Hred) as [allocated Htrace].
  exists (allocated \u (fv_config c \u fv body)).
  intros z0 z r y1 y2 Hz0 Hz Hr Hzr Hz0r Hz0z H1 H2 ca.
  assert (Hsca : config_has_scoped_locations ca).
  { unfold ca. apply (@scoped_method_aliases body st h e L w1 w2); try assumption.
    all: repeat rewrite notin_union in Hz0, Hz, Hr; tauto. }
  set (S := method_alias_set z0 z r).
  set (rename := method_alias_name z0 z r w1 w2).
  assert (Havoid : forall x, x \in S -> x \notin (allocated \u (fv_config c \u fv body))).
  { unfold S, method_alias_set. intros x H.
    repeat rewrite in_union in H; repeat rewrite in_singleton in H.
    assert (x = z0 \/ x = z \/ x = r) as [-> | [-> | ->]] by tauto; assumption. }
  assert (Hfix : forall x, x \in fv_config c \u fv body -> rename x = x).
  { intros x Hx. apply method_alias_fixes. intro Hx'.
    apply (Havoid x Hx'). rewrite in_union. now right. }
  assert (Hfixed : all_fresh_names_fixed rename (reserve_config_vars S c)).
  { intros x Hx. rewrite reserved_config_free_vars, notin_union in Hx.
    destruct Hx as [Hc HS]. apply method_alias_fixes_uniquely; [exact HS | |].
    all: intro Heq; subst x; apply Hc; unfold c; simpl;
      repeat rewrite in_union;
      pose proof (get_some_inv H1); pose proof (get_some_inv H2); tauto. }
  assert (Hproj : config_projects rename ca (reserve_config_vars S c)).
  { unfold c, ca. simpl. apply projected_initial_method_bodies.
    - unfold rename, method_alias_name. case_if; congruence.
    - unfold rename, method_alias_name. do 2 (case_if; try congruence).
    - intros x Hx. apply Hfix. rewrite in_union. now right.
    - intros x Hx. apply Hfix. rewrite in_union. left.
      unfold c. simpl. repeat rewrite in_union. tauto.
    - intros y i x Hb Hx. apply Hfix. rewrite in_union. left.
      unfold c. simpl. repeat rewrite in_union.
      pose proof (@fv_of_binding_is_env_fv item fv h x y i Hb Hx) as Hf.
      tauto.
    - exact Hok.
    - apply method_alias_projection; assumption. }
  assert (Hreserved : projected_reserved_vars rename ca (reserve_config_vars S c)).
  { unfold projected_reserved_vars, ca, c. simpl.
    intros x _ Hx. rewrite in_union. now left. }
  assert (HscopeR : config_has_scoped_locations (reserve_config_vars S c)).
  { destruct c; exact Hscope. }
  assert (Hsupport : forall w, w # (config_env ca) -> rename w = w).
  { intros w Hw. apply method_alias_fixes. intro Hsin.
    apply Hw. exact (@method_aliases_in_environment e z0 z r y1 y2 w Hsin). }
  specialize (Htrace S ltac:(intros x Hx Hs; apply (Havoid x Hs); rewrite in_union; now left)).
  destruct (scoped_replay_with_reserved_names Htrace Hproj Hreserved Hfixed Hsca HscopeR Hsupport)
    as (da & HredA & HprojA).
  exists da. split; [exact HredA |]. destruct d. exact HprojA.
Qed.

Local Definition extends_stack base inner outer :=
  config_trm inner = config_trm outer /\
  config_heap inner = config_heap outer /\
  config_env inner = config_env outer /\
  stack_append (config_stack inner) base = config_stack outer /\
  config_fv inner \c config_fv outer.

Local Lemma prefix_stack_free_vars prefix base :
  fv prefix \c fv (stack_append prefix base).
Proof.
  induction prefix; simpl.
  - intros x Hx. contradiction (notin_empty Hx).
  - intros x Hx. rewrite in_union in *. intuition.
Qed.

Local Lemma config_prefix_free_vars base inner outer :
  extends_stack base inner outer ->
  fv_config inner \c fv_config outer.
Proof.
  destruct inner as [ti si hi ei Li], outer as [to so ho eo Lo].
  intros (Ht & Hh & He & Hs & Hl).
  simpl in *. subst to ho eo so.
  pose proof (prefix_stack_free_vars si base) as Hprefix.
  intros x Hx. simpl in *. repeat rewrite in_union in *.
  all: intuition.
Qed.

Local Lemma config_prefix_fresh_names base inner outer xs :
  extends_stack base inner outer ->
  fresh_in_config xs outer ->
  fresh_in_config xs inner.
Proof.
  intros Hprefix Hfresh.
  eapply transfer_fresh_list; [exact Hfresh |].
  intros x _ Hx. exact (config_prefix_free_vars Hprefix Hx).
Qed.

Local Lemma step_inside_stack_prefix base inner outer outer' :
  extends_stack base inner outer ->
  ~ frame_result base outer ->
  outer ↦ outer' ->
  exists inner', inner ↦ inner' /\ extends_stack base inner' outer'.
Proof.
  intros Hpre Hinside Hred.
  pose proof (config_prefix_free_vars Hpre) as Hfv.
  assert (Hfresh : forall xs, fresh_in_config xs outer -> fresh_in_config xs inner).
  { intro xs. now apply (@config_prefix_fresh_names base inner outer xs). }
  destruct Hred; destruct inner as [ti si hi ei Li];
    destruct Hpre as (Ht & Hh & He & Hs & HL);
    simpl in Ht, Hh, He, Hs, HL; subst ti hi ei.
  - eexists. split.
    + eapply red_read; [apply Hfresh | | |]; eassumption.
    + repeat split; assumption.
  - eexists. split.
    + eapply red_write; eassumption.
    + repeat split; assumption.
  - eexists. split.
    + eapply red_call; eassumption.
    + repeat split; assumption.
  - eexists. split.
    + eapply red_apply; eassumption.
    + repeat split; assumption.
  - eexists. split.
    + eapply red_let_fun with (y := y) (w := w); [apply Hfresh |]; assumption.
    + repeat split; assumption.
  - eexists. split.
    + eapply red_let_obj with (y := y) (w := w); [apply Hfresh |]; assumption.
    + repeat split; assumption.
  - destruct si as [|fr si]; simpl in Hs.
    + exfalso. apply Hinside. split; [symmetry; exact Hs |].
      now exists x.
    + injection Hs as Hfr Hs. subst fr. eexists. split.
      * apply red_let_var.
      * repeat split; assumption.
  - eexists. split.
    + apply red_let_push.
    + repeat split; [simpl; now rewrite Hs | exact Hfv].
Qed.

Local Lemma trace_inside_stack_prefix base inner outer outer' n :
  outer ⊣n↦* outer' ->
  extends_stack base inner outer ->
  (forall j result, j < n -> outer ⊣j↦* result -> ~ frame_result base result) ->
  exists inner', inner ⊣n↦* inner' /\ extends_stack base inner' outer'.
Proof.
  intros Hred. induction Hred as [c | c d f k Hred IH Hstep]; intros Hpre Hinside.
  - exists inner. split; [apply red_refl | assumption].
  - destruct (IH Hpre) as [inner' [Htrace Hpre']].
    { intros j result Hj Hr. apply (Hinside j result); [lia | assumption]. }
    assert (Hclosed : ~ frame_result base d).
    { apply (Hinside k d); [lia | assumption]. }
    destruct (step_inside_stack_prefix Hpre' Hclosed Hstep) as (inner'' & Hst & Hpf).
    exists inner''. split; [eapply red_trans; eassumption | assumption].
Qed.

Local Lemma initial_method_as_standalone body st h e L w1 w2 n d :
  let c := (open_met w2 w1 body ; st ; h ; e ; L) in
  c ⊣n↦* d ->
  (forall j result, j < n -> c ⊣j↦* result -> ~ frame_result st result) ->
  exists d', (open_met w2 w1 body ; stack_nil ; h ; e ; L) ⊣n↦* d' /\
    extends_stack st d' d.
Proof.
  intros c Hred Hscope.
  eapply trace_inside_stack_prefix; [exact Hred | | exact Hscope].
  repeat split. intros x Hx. exact Hx.
Qed.

Local Lemma projected_write_receiver rename ca c x a v y :
  config_projects rename ca c ->
  config_trm c = trm_write (avar_f x) a (avar_f v) ->
  binds x y (config_env c) ->
  exists xa va,
    config_trm ca = trm_write (avar_f xa) a (avar_f va) /\
    binds xa y (config_env ca).
Proof.
  intros (Htrm & _ & _ & Henv) Hwrite Hbind.
  rewrite Hwrite in Htrm.
  destruct (config_trm ca); simpl in Htrm; try discriminate.
  injection Htrm as Hx <- Hv.
  destruct (@renamed_free_variable rename _ _ Hx) as (xa & -> & Hxa).
  destruct (@renamed_free_variable rename _ _ Hv) as (va & -> & _).
  exists xa, va. split; [reflexivity |].
  apply Henv. now rewrite Hxa.
Qed.

Local Lemma standalone_alias_write_trace body st h e L w1 w2 n d x a v y :
  let c := (open_met w2 w1 body ; st ; h ; e ; L) in
  c ⊣n↦* d ->
  config_has_scoped_locations c ->
  ok h ->
  (forall j result, j < n -> c ⊣j↦* result -> ~ frame_result st result) ->
  config_trm d = trm_write (avar_f x) a (avar_f v) ->
  binds x y (config_env d) ->
  exists avoid : vars, forall z0 z r y1 y2,
    z0 \notin avoid -> z \notin avoid -> r \notin avoid ->
    z <> r -> z0 <> r -> z0 <> z ->
    binds w1 y1 e ->
    binds w2 y2 e ->
    let ca := (open_met z r body ; stack_nil ; h ; e & z0 ~ y2 & z ~ y2 & r ~ y1 ; L) in
    exists da xa va,
      ca ⊣n↦* da /\
      config_trm da = trm_write (avar_f xa) a (avar_f va) /\
      binds xa y (config_env da).
Proof.
  intros c Hred Hsc Hok Hbefore Hwrite Hbind.
  destruct (@initial_method_as_standalone body st h e L w1 w2 n d Hred Hbefore)
    as (di & Htrace & Htrm & _ & Henv & _).
  assert (Hsc0 : config_has_scoped_locations
    (open_met w2 w1 body ; stack_nil ; h ; e ; L)).
  { destruct Hsc as (Hoke & Hp & Ht & _ & Hh).
    repeat split; try assumption.
    - exact (proj1 Hp).
    - exact (proj2 Hp).
    - intros w Hw. inversion Hw. }
  destruct (@fresh_method_alias_trace body stack_nil h e L w1 w2 n di
      Htrace Hsc0 Hok) as [avoid Hreplay].
  exists avoid. intros z0 z r y1 y2 Hz0 Hz Hr Hzr Hz0r Hz0z Hy1 Hy2 ca.
  destruct (Hreplay z0 z r y1 y2 Hz0 Hz Hr Hzr Hz0r Hz0z Hy1 Hy2)
    as (da & Hreda & Hpa).
  assert (Htrmi : config_trm di = trm_write (avar_f x) a (avar_f v)) by congruence.
  assert (Hbi : binds x y (config_env di)) by (now rewrite Henv).
  destruct (@projected_write_receiver _ da di x a v y Hpa Htrmi Hbi) as (xa & va & Hwa & Hba).
  exists da, xa, va. auto.
Qed.

Local Lemma initial_step_of_trace c n d :
  c ⊣n↦* d ->
  0 < n ->
  exists c0, c ↦ c0 /\ c0 ⊣(pred n)↦* d.
Proof.
  induction 1 as [c | c d f k Hr IH Hstep]; intro Hpos.
  - lia.
  - destruct k as [|k].
    + inversion Hr; subst. exists f. split; [assumption | apply red_refl].
    + destruct (IH ltac:(lia)) as (c0 & H0 & Hrest).
      exists c0. split; [exact H0 |]. simpl in *. eapply red_trans; eassumption.
Qed.

Local Lemma prepend_trace_step c0 c n d :
  c0 ↦ c ->
  c ⊣n↦* d ->
  c0 ⊣(S n)↦* d.
Proof.
  intros Hstep Htrace. induction Htrace.
  - eapply red_trans; [apply red_refl | eassumption].
  - eapply red_trans; [now apply IHHtrace | eassumption].
Qed.

Local Lemma avar_open_commute_at_distinct_depths (a : avar) k j x y :
  k <> j ->
  open_rec k x (open_rec j y a) = open_rec j y (open_rec k x a).
Proof.
  destruct a; simpl; intro Hneq; try reflexivity.
  repeat (case_if; cbn [open_rec AvarOpenable]); congruence.
Qed.

Local Lemma avar_open_twice_at_same_depth (a : avar) k x y :
  open_rec k x (open_rec k y a) = open_rec k y a.
Proof. destruct a; cbn [open_rec AvarOpenable]; repeat (case_if; cbn [open_rec AvarOpenable]); congruence. Qed.

Local Lemma type_open_commute_at_distinct_depths :
  (forall (T : typ) k j x y, k <> j ->
    open_rec k x (open_rec j y T) = open_rec j y (open_rec k x T)) /\
  (forall (D : dec) k j x y, k <> j ->
    open_rec k x (open_rec j y D) = open_rec j y (open_rec k x D)).
Proof.
  apply typ_mutind; intros;
    cbn [open_rec TypOpenable DecOpenable open_rec_typ open_rec_dec];
    f_equal; eauto using avar_open_commute_at_distinct_depths; congruence.
Qed.

Local Lemma type_open_twice_at_same_depth :
  (forall (T : typ) k x y, open_rec k x (open_rec k y T) = open_rec k y T) /\
  (forall (D : dec) k x y, open_rec k x (open_rec k y D) = open_rec k y D).
Proof.
  apply typ_mutind; intros;
    cbn [open_rec TypOpenable DecOpenable open_rec_typ open_rec_dec];
    f_equal; eauto using avar_open_twice_at_same_depth.
Qed.

Local Lemma term_open_commute_at_distinct_depths :
  (forall (t : trm) k j x y, k <> j ->
    open_rec k x (open_rec j y t) = open_rec j y (open_rec k x t)) /\
  (forall (l : lit) k j x y, k <> j ->
    open_rec k x (open_rec j y l) = open_rec j y (open_rec k x l)) /\
  (forall (d : def) k j x y, k <> j ->
    open_rec k x (open_rec j y d) = open_rec j y (open_rec k x d)) /\
  (forall (ds : defs) k j x y, k <> j ->
    open_rec k x (open_rec j y ds) = open_rec j y (open_rec k x ds)).
Proof.
  destruct type_open_commute_at_distinct_depths as [Htype Hdec].
  apply trm_mutind; intros;
    cbn [open_rec TrmOpenable LitOpenable DefOpenable DefsOpenable
      open_rec_trm open_rec_lit open_rec_def open_rec_defs];
    f_equal; eauto using avar_open_commute_at_distinct_depths; congruence.
Qed.

Local Lemma term_open_twice_at_same_depth :
  (forall (t : trm) k x y, open_rec k x (open_rec k y t) = open_rec k y t) /\
  (forall (l : lit) k x y, open_rec k x (open_rec k y l) = open_rec k y l) /\
  (forall (d : def) k x y, open_rec k x (open_rec k y d) = open_rec k y d) /\
  (forall (ds : defs) k x y, open_rec k x (open_rec k y ds) = open_rec k y ds).
Proof.
  destruct type_open_twice_at_same_depth as [Htype Hdec].
  apply trm_mutind; intros;
    cbn [open_rec TrmOpenable LitOpenable DefOpenable DefsOpenable
      open_rec_trm open_rec_lit open_rec_def open_rec_defs];
    f_equal; eauto using avar_open_twice_at_same_depth.
Qed.

Local Lemma method_opening_is_closed m body z r :
  closed (def_met m body) -> closed (open_met z r body).
Proof.
  intros Hclosed [|[|n]] x.
  - apply (proj1 term_open_twice_at_same_depth).
  - rewrite (proj1 term_open_commute_at_distinct_depths _ 1 0 x z) by discriminate.
    rewrite (proj1 term_open_twice_at_same_depth body 1 x r). reflexivity.
  - rewrite (proj1 term_open_commute_at_distinct_depths _ (S (S n)) 0 x z) by discriminate.
    rewrite (proj1 term_open_commute_at_distinct_depths _ (S (S n)) 1 x r) by discriminate.
    specialize (Hclosed n x).
    change (def_met m (open_rec (S (S n)) x body) = def_met m body) in Hclosed.
    now injection Hclosed as ->.
Qed.

Local Lemma closed_heap_binding h x i :
  heap_closed h -> binds x i h -> closed i.
Proof.
  induction 1 as [|h y j Hh IH Hj]; intro Hb.
  - exfalso. apply get_some_inv in Hb. rewrite dom_empty in Hb. exact (notin_empty Hb).
  - apply binds_push_inv in Hb as [[_ ->] | [_ Hb]]; auto.
Qed.

Local Lemma closed_defs_member ds d :
  closed ds ->
  defs_has ds d ->
  closed d.
Proof.
  induction ds as [|ds IH last]; intros Hclosed Hb.
  - unfold defs_has in Hb. discriminate.
  - unfold defs_has in *. simpl in Hb. case_if.
    + injection Hb as <-. intros k x.
      specialize (Hclosed k x).
      change (defs_cons (open_rec k x ds) (open_rec k x last) = defs_cons ds last)
        in Hclosed.
      now injection Hclosed.
    + apply IH; [|exact Hb].
      intros k x. specialize (Hclosed k x).
      change (defs_cons (open_rec k x ds) (open_rec k x last) = defs_cons ds last)
        in Hclosed.
      now injection Hclosed.
Qed.

Local Lemma closed_heap_method h y ds m body :
  heap_closed h ->
  binds y (item_obj ds) h ->
  defs_has ds (def_met m body) ->
  closed (def_met m body).
Proof.
  intros Hh Hb Hmethod. eapply closed_defs_member; [|exact Hmethod]. intros k x.
  pose proof (closed_heap_binding Hh Hb k x) as H.
  change (item_obj (open_rec k x ds) = item_obj ds) in H.
  now injection H.
Qed.

Local Lemma mode_has_hidden_method_bodies mode :
  mode_has_mutability mode -> mode_has_visibility mode.
Proof. destruct mode; cbn; discriminate || reflexivity. Qed.

Local Lemma opened_typed_method_free_scope mode G Go e m body D z r w :
  mode_has_mutability mode ->
  @ty_def mode G Go e (def_met m body) D ->
  tfree_trm w (open_met z r body) ->
  w = z \/ w = r.
Proof.
  intros Hmode Htyped Hw.
  apply (proj1 tfree_open_backward) in Hw as [-> | Hwithin]; [now left |].
  apply (proj1 tfree_open_backward) in Hwithin as [-> | Hbody]; [now right |].
  exfalso. exact (typed_method_has_no_free_term_variables
      (mode_has_hidden_method_bodies mode Hmode) Htyped Hbody).
Qed.

Local Lemma ctx_binding_free_variables G w T :
  ctx_binds w T G ->
  fv T \c ctx_fv G.
Proof.
  induction 1; intros x Hx; cbn [ctx_fv ctx_collect_values] in *.
  - rewrite in_union. now left.
  - rewrite in_union. right. now apply IHctx_binds.
  - now apply IHctx_binds.
Qed.

Local Lemma readonly_binding_free_variables R B :
  fv (typ_and (typ_bnd R) (typ_mut_marker typ_top)) \c
  fv (typ_and (typ_bnd R) (typ_mut_marker B)).
Proof.
  cbn [fv TypFreeVar fv_typ fv_dec]. intros x Hx.
  repeat rewrite in_union in *. pose proof (notin_empty (x := x)). tauto.
Qed.

Local Lemma typed_config_reserved_names mode G c T :
  @ty_config mode G c T ->
  ctx_dom G \c fv_config c /\
  ctx_fv G \c fv_config c /\
  has_null (fv_config c).
Proof.
  destruct 1 as [G e s h Lv t S T Hiner Hheap Hstack Hstackref Hterm Htermref
    [[Hdom Hfv] _] [x Hx] Hseal Hclosed Hresult].
  split; [exact Hdom |]. split; [exact Hfv |].
  exists x. repeat rewrite in_union. tauto.
Qed.

Local Lemma standalone_alias_config_is_typed mode G c U e' z0 z r y1 y2
    G' w1 w2 R1 B1 R2 B2 Go m body C Z Ret Tbody :
  mode_has_mutability mode ->
  @ty_config mode G c U ->
  ctx_binds w1 (typ_and (typ_bnd R1) (typ_mut_marker B1)) G ->
  ctx_binds w2 (typ_and (typ_bnd R2) (typ_mut_marker B2)) G ->
  e' = (config_env c & z0 ~ y2 & z ~ y2 & r ~ y1) ->
  G' = (G § z0 / v_ref ~ typ_and (typ_bnd R2) (typ_mut_marker B2)
          § z / v_ref ~ typ_and (typ_bnd R2) (typ_mut_marker typ_top)
          § r / v_ref ~ typ_and (typ_bnd R1) (typ_mut_marker typ_top)) ->
  @inert mode G' ->
  @heap_correspond mode G' e' (config_heap c) ->
  sealed G' ->
  closed (def_met m body) ->
  @ty_def mode G Go (config_env c) (def_met m body) (dec_met m C Z Ret) ->
  @ty_trm mode G' objctx_empty e' (open_met z r body) Tbody ->
  @ty_config mode G' (open_met z r body ; stack_nil ; config_heap c ; e' ; fv_config c)
    typ_top.
Proof.
  intros Hmode Htyped H1 H2 -> -> HG Hheap Hseal Hclosed Hdef Hterm.
  destruct (typed_config_reserved_names Htyped) as (Hdom & Hfv & Hnull).
  pose proof (ctx_binding_free_variables H1) as Htv1.
  pose proof (ctx_binding_free_variables H2) as Htv2.
  eapply ty_config_c with (T := Tbody); try eassumption.
  - apply ty_stack_nil, subtyp_top.
  - intros v Hv. inversion Hv.
  - intros v Hv.
    destruct (@opened_typed_method_free_scope mode G Go (config_env c) m body (dec_met m C Z Ret) z r v Hmode Hdef Hv) as [-> | ->].
    + repeat eexists. eapply ctx_binds_k_n.
      * intro Heq. subst z. inversion HG; subst.
        match goal with H : r §# _ |- _ => apply H end.
        simpl. rewrite in_union. left. apply in_singleton_self.
      * apply ctx_binds_k_e.
    + repeat eexists. apply ctx_binds_k_e.
  - split; [|intros x Hx; contradiction (notin_empty Hx)].
    split.
    + intros x Hx.
      cbn [ctx_dom] in Hx. repeat rewrite in_union in Hx. repeat rewrite in_singleton in Hx.
      cbn [config_fv]. repeat rewrite in_union.
      enough (x \in dom (config_env c & z0 ~ y2 & z ~ y2 & r ~ y1) \/ x \in fv_config c).
      { destruct H as [Hd | Hl]; auto. repeat rewrite in_union in Hl. tauto. }
      repeat rewrite dom_push. repeat rewrite in_union. repeat rewrite in_singleton.
      intuition.
    + intros x Hx. cbn [fv CtxFreeVar ctx_fv ctx_collect_values] in Hx.
      cbn [config_fv].
      repeat rewrite in_union.
      enough (x \in fv_config c) by (repeat rewrite in_union in H; tauto).
      repeat rewrite in_union in Hx.
      pose proof (@readonly_binding_free_variables R1 B1 x).
      pose proof (@readonly_binding_free_variables R2 B2 x).
      intuition eauto.
  - constructor.
    + exact (@method_opening_is_closed m body z r Hclosed).
    + intros j v. reflexivity.
    + destruct Htyped.
      match goal with H : config_closed _ |- _ => inversion H; assumption end.
  - intros j v. reflexivity.
Qed.
Local Lemma call_write_replays_through_aliases mode G c k d w1 m w2 U :
  mode_has_mutability mode ->
  @ty_config mode G c U ->
  config_trm c = trm_call (avar_f w1) m (avar_f w2) ->
  c ⊣k↦* d ->
  (forall j d0, j < k -> ~ frame_end_in c j d0) ->
  ~ subheap_unchanged (config_heap c) (config_heap d) ->
  exists n body L y1 y2 y it a avoid R B C Z Ret,
    S n < k /\
    binds y it (config_heap c) /\
    binds w1 y1 (config_env c) /\ binds w2 y2 (config_env c) /\
    ctx_binds w1 (typ_and (typ_bnd R) (typ_mut_marker B)) G /\
    typ_indep_b 0 R /\
    @ty_def mode G (objctx_heap y1 R) (config_env c)
      (def_met m body) (dec_met m C Z Ret) /\
    record_has (open y1 R) (dec_met m C Z Ret) /\
    L = fv_config c /\
    closed (def_met m body) /\
    (forall z0 z r,
      z0 \notin avoid -> z \notin avoid -> r \notin avoid ->
      z <> r -> z0 <> r -> z0 <> z ->
      let ca := (open_met z r body ; stack_nil ; config_heap c ;
        config_env c & z0 ~ y2 & z ~ y2 & r ~ y1 ; L) in
      exists da xa va, ca ⊣n↦* da /\
        config_trm da = trm_write (avar_f xa) a (avar_f va) /\
        binds xa y (config_env da)).
Proof.
  intros Hmut Htyped Hcall Hred Hnoend Hchanged.
  destruct (initial_call_write_prefix Hcall Hred Hnoend Hchanged)
    as (j & cj & x & a & v & y & it & Hpos & Hjk & Hj & Hinside & Hw & Hbind & Hit).
  destruct (initial_step_of_trace Hj Hpos) as (c0 & Hstep & Htail).
  assert (Hsc0 : config_has_scoped_locations c0).
  { apply (scoped_locations_step Hstep). now apply (typed_config_has_placement Hmut Htyped). }
  destruct c as [t st h e L]. simpl in Hcall. subst t.
  pose proof (typed_config_has_placement Hmut Htyped) as (_ & _ & Hrefs & _).
  cbn in Hrefs.
  destruct (get_some (Hrefs _ (tfree_trm_call_r (avar_f w1) w2 m))) as [y2 Hy2].
  assert (Hh : @heap_correspond mode G e h) by (inversion Htyped; assumption).
  pose proof (proj1 (proj2 (proj2 Hh))) as Hok.
  pose proof Hstep as Hstep0.
  inversion Hstep; subst; clear Hstep.
  lazymatch type of Htail with
  | red_closure ?cb _ _ =>
    assert (Hbefore : forall i result, i < pred j ->
      cb ⊣i↦* result -> ~ frame_result st result)
  end.
  { intros i result Hi Hireach Hres.
    pose proof (prepend_trace_step Hstep0 Hireach) as Hreach.
    assert (Hearly : exists p cp, p < S (S i) /\
      (trm_call (avar_f w1) m (avar_f w2) ; st ; h ; e ; L) ⊣p↦* cp /\
      frame_result st cp).
    { exists (S i), result. split; [lia | now split]. }
    destruct (earliest_frame_end Hearly) as (p & cp & Hend & Hp).
    apply (Hnoend p cp); [lia | exact Hend]. }
  lazymatch goal with
  | H1 : binds w1 ?loc e, H2 : binds ?loc (item_obj ?ds) h,
    H3 : defs_has ?ds (def_met m ?body) |- _ =>
      destruct (@heap_reference_precise_definition mode G e h w1 loc ds
        (def_met m body) Hmut ltac:(inversion Htyped; assumption) Hh H1 H2 H3)
        as (R & B & D & Hctx & Hind & Hdef & Hmember & _);
      destruct (@standalone_alias_write_trace body st h e
        (fv_config (trm_call (avar_f w1) m (avar_f w2) ; st ; h ; e ; L))
        w1 w2 (pred j) cj x a v y Htail Hsc0 Hok Hbefore Hw Hbind)
        as [avoid Hreplay];
      assert (Hclosed_h : heap_closed h) by (
        inversion Htyped; subst;
        lazymatch goal with Hclosed : config_closed _ |- _ =>
          inversion Hclosed; subst; assumption
        end);
      pose proof (closed_heap_method Hclosed_h H2 H3) as Hclosed_body;
      inversion Hdef; subst D;
      exists (pred j), body,
        (fv_config (trm_call (avar_f w1) m (avar_f w2) ; st ; h ; e ; L)),
        loc, y2, y;
      exists it, a, avoid, R, B;
      eexists _, _, _; repeat split; try eassumption; try lia;
      intros; eapply Hreplay; eassumption
  end.
Qed.


Local Definition precise_method_views mode :=
  forall G e h w y R B m C Z Ret Ca Za Ra,
    @inert mode G ->
    sealed G ->
    @heap_correspond mode G e h ->
    binds w y e ->
    ctx_binds w (typ_and (typ_bnd R) (typ_mut_marker B)) G ->
    record_has (open y R) (dec_met m C Z Ret) ->
    @ty_var mode G objctx_empty e w (typ_rcd (dec_met m Ca Za Ra)) ->
    @method_subtype_components mode G e C Z Ret Ca Za Ra.

Local Lemma typed_call_write_replays_through_aliases mode G c k d w1 m w2 U Zv :
  mode_has_sef mode ->
  mode_has_mutability mode ->
  @precise_method_views mode ->
  @ty_config mode G c U ->
  config_trm c = trm_call (avar_f w1) m (avar_f w2) ->
  @ty_var mode G objctx_empty (config_env c) w1
    (typ_rcd (dec_met m typ_nocap Zv typ_top)) ->
  @ty_var mode G objctx_empty (config_env c) w2 Zv ->
  @subtyp mode G objctx_empty (config_env c) typ_nocap Zv ->
  c ⊣k↦* d ->
  (forall j d0, j < k -> ~ frame_end_in c j d0) ->
  ~ subheap_unchanged (config_heap c) (config_heap d) ->
  exists G' ca z r R1 R2 n da xa a va y it,
    S n < k /\
    @ty_config mode G' ca typ_top /\
    config_stack ca = stack_nil /\
    ctx_binds z (typ_and (typ_bnd R2) (typ_mut_marker typ_top)) G' /\
    ctx_binds r (typ_and (typ_bnd R1) (typ_mut_marker typ_top)) G' /\
    (forall w, tfree_trm w (config_trm ca) -> w = z \/ w = r) /\
    ca ⊣n↦* da /\
    config_trm da = trm_write (avar_f xa) a (avar_f va) /\
    binds xa y (config_env da) /\
    binds y it (config_heap ca).
Proof.
  intros Hsef Hmut Hviews Htyped Hcall Hsefview Hzv Hnocap Hred Hnoend Hchanged.
  destruct (call_write_replays_through_aliases Hmut Htyped Hcall Hred Hnoend Hchanged)
    as (n & body & L & y1 & y2 & y & it & a & avoid & R1 & B1 & C & Z & Ret &
        Hbound & Hloc & Hrec & Harg & Hctx1 & Hind & Hdef & Hmember & -> & Hclosed & Hreplay).
  assert (Hfree : tfree_trm w2 (config_trm c)).
  { rewrite Hcall. apply tfree_trm_call_r. }
  destruct (typed_config_ref_binding Hmut Htyped Hfree)
    as (y2' & R2 & B2 & Hy2 & Hctx2).
  assert (y2' = y2) by exact (binds_functional Hy2 Harg). subst y2'.
  assert (Hiner : @inert mode G) by (inversion Htyped; assumption).
  assert (Hheap : @heap_correspond mode G (config_env c) (config_heap c)).
  { destruct Htyped. simpl. assumption. }
  assert (Hseal : sealed G) by (inversion Htyped; assumption).
  assert (Hcurrent : exists T, @ty_trm mode G objctx_empty (config_env c) (config_trm c) T).
  { destruct Htyped. simpl. eexists. eassumption. }
  destruct Hcurrent as [T Hterm].
  destruct (typed_call_application_parts Hterm Hsef Hcall)
    as (Ca & Za & Ra & HindCa & Hactualview & Hactualarg & Hactualrec).
  assert (Hactualcomponents : @method_subtype_components mode (G) (config_env c) C Z Ret Ca Za Ra).
  { exact (Hviews G (config_env c) (config_heap c) w1 y1 R1 B1 m C Z Ret
      Ca Za Ra Hiner Hseal Hheap Hrec Hctx1 Hmember Hactualview). }
  assert (Hsefcomponents : @method_subtype_components mode (G) (config_env c) C Z Ret
      typ_nocap Zv typ_top).
  { exact (Hviews G (config_env c) (config_heap c) w1 y1 R1 B1 m C Z Ret
      typ_nocap Zv typ_top Hiner Hseal Hheap Hrec Hctx1 Hmember Hsefview). }
  destruct (@prepare_pure_method_body mode G (config_env c) (config_heap c)
      y1 y2 w1 w2 R1 R2 B1 B2 m body C Z Ret Ca Za Ra Zv avoid
      Hsef Hmut Hiner Hheap Hseal Hrec Harg Hind HindCa Hdef
      Hactualcomponents Hsefcomponents Hctx1 Hctx2 Hactualrec Hactualarg Hzv Hnocap)
    as (G' & e' & z0 & z & r & Hz0 & Hz & Hr & Hzr & Hz0r & Hz0z & He' & HG' &
        Hiner' & Hheap' & Hseal' & _ & _ & _ & Hctxz & Hctxr & Hbody).
  destruct (Hreplay z0 z r Hz0 Hz Hr Hzr Hz0r Hz0z)
    as (da & xa & va & HredA & Hwrite & Href).
  pose proof (@standalone_alias_config_is_typed mode G c U e' z0 z r y1 y2
    G' w1 w2 R1 B1 R2 B2 (objctx_heap y1 R1) m body C Z Ret (open_met z r Ret)
    Hmut Htyped Hctx1 Hctx2 He' HG' Hiner' Hheap' Hseal' Hclosed Hdef Hbody) as HtypedA.
  exists G', (open_met z r body ; stack_nil ; config_heap c ; e' ; fv_config c), z, r, R1, R2.
  exists n, da, xa, a, va, y. exists it.
  split; [exact Hbound |].
  split; [exact HtypedA |]. split; [reflexivity |].
  split; [exact Hctxz |]. split; [exact Hctxr |]. simpl.
  split.
  - intros w Hw. exact (@opened_typed_method_free_scope mode G (objctx_heap y1 R1) (config_env c) m body (dec_met m C Z Ret) z r w Hmut Hdef Hw).
  - rewrite He'. auto.
Qed.

Local Definition standalone_readonly_execution_safe mode :=
  forall G c U z r Rz Rr n d x a v y it,
    @ty_config mode G c U ->
    config_stack c = stack_nil ->
    ctx_binds z (typ_and (typ_bnd Rz) (typ_mut_marker typ_top)) G ->
    ctx_binds r (typ_and (typ_bnd Rr) (typ_mut_marker typ_top)) G ->
    (forall w, tfree_trm w (config_trm c) -> w = z \/ w = r) ->
    c ⊣n↦* d ->
    config_trm d = trm_write (avar_f x) a (avar_f v) ->
    binds x y (config_env d) ->
    binds y it (config_heap c) ->
    False.

Local Lemma call_heap_preserved_from_method_and_write_invariants
    mode w1 m w2 Zv c G d k U :
  @precise_method_views mode ->
  @standalone_readonly_execution_safe mode ->
  mode_has_sef mode ->
  mode_has_mutability mode ->
  config_trm c = trm_call (avar_f w1) m (avar_f w2) ->
  @ty_var mode G objctx_empty (config_env c) w1
    (typ_rcd (dec_met m typ_nocap Zv typ_top)) ->
  @ty_var mode G objctx_empty (config_env c) w2 Zv ->
  @subtyp mode G objctx_empty (config_env c) typ_nocap Zv ->
  @ty_config mode G c U ->
  c ⊣k↦* d ->
  (exists j d0, frame_end_in c j d0 /\ j < k) \/
  subheap_unchanged (config_heap c) (config_heap d).
Proof.
  intros Hviews Hsafe Hsef Hmut Hcall Hrecv Harg Hnocap Htyped Hrun.
  destruct (classic (exists j d0, frame_end_in c j d0 /\ j < k)) as [Hended | Hnoend].
  - now left.
  - right. destruct (classic (subheap_unchanged (config_heap c) (config_heap d)))
      as [Hsame | Hchanged]; [exact Hsame |].
    exfalso.
    assert (Hbefore : forall j d0, j < k -> ~ frame_end_in c j d0).
    { intros j d0 Hj Hend. apply Hnoend. exists j, d0. auto. }
    destruct (typed_call_write_replays_through_aliases
        Hsef Hmut Hviews Htyped Hcall Hrecv Harg Hnocap Hrun Hbefore Hchanged)
      as (G' & ca & z & r & R1 & R2 & n & da & xa & a & va & y & it &
          _ & HtypedA & Hstack & Hctxz & Hctxr & Hscope & HredA & Hwrite & Href & Hloc).
    exact (Hsafe G' ca typ_top z r R2 R1 n da xa a va y it
      HtypedA Hstack Hctxz Hctxr Hscope HredA Hwrite Href Hloc).
Qed.

Local Lemma record_member_label_in_record T ls D :
  record_typ T ls ->
  record_has T D ->
  label_of D \in ls.
Proof.
  intro Hrecord. induction Hrecord; intros Hmember; subst l.
  - inversion Hmember; subst. apply in_singleton_self.
  - inversion Hmember; subst; rewrite in_union.
    + left. now apply IHHrecord.
    + match goal with H : record_has (typ_rcd _) _ |- _ => inversion H; subst end.
      right. apply in_singleton_self.
Qed.

Local Lemma record_member_unique_by_label T ls D E :
  record_typ T ls ->
  record_has T D ->
  record_has T E ->
  label_of D = label_of E ->
  D = E.
Proof.
  intro Hrecord. induction Hrecord as [F l Hdec Heq | T ls F l Hrec IH Hdec Heq Hfresh];
    intros HD HE Hl; subst l.
  - inversion HD; inversion HE; congruence.
  - inversion HD; inversion HE; subst.
    + eauto.
    + match goal with H : record_has (typ_rcd _) E |- _ => inversion H; subst end.
      exfalso. apply Hfresh. rewrite <- Hl. eapply record_member_label_in_record; eassumption.
    + match goal with H : record_has (typ_rcd _) _ |- _ => inversion H; subst end.
      exfalso. apply Hfresh. rewrite Hl. eapply record_member_label_in_record; eassumption.
    + repeat match goal with H : record_has (typ_rcd _) _ |- _ => inversion H; clear H; subst end.
      reflexivity.
Qed.

Local Lemma record_member_before_opening T x D :
  record_has (open x T) D ->
  exists E, record_has T E /\ D = open x E.
Proof.
  induction T; cbn [open_rec TypOpenable open_rec_typ]; intro H; inversion H; subst.
  - eexists. split; [apply rh_one | reflexivity].
  - edestruct IHT1 as (E & He & ->); [eassumption |].
    exists E. split; [now apply rh_andl | reflexivity].
  - edestruct IHT2 as (E & He & ->); [eassumption |].
    exists E. split; [now apply rh_andr | reflexivity].
Qed.

Local Definition reference_target (e : renv) (w : var) :=
  match get w e with Some y => y | None => w end.

Local Lemma alias_equivalence_has_same_target e w x :
  env_targets_are_locations e ->
  @tyq_var e w x ->
  reference_target e w = reference_target e x.
Proof.
  intros Hloc Heq.
  induction Heq as [e w | e w x Hb | e w x Heq IH | e w x y Hw IHw Hx IHx].
  - reflexivity.
  - unfold reference_target. change (get w e = Some x) in Hb.
    rewrite Hb, (get_none (Hloc w x Hb)). reflexivity.
  - symmetry; auto.
  - now rewrite (IHw Hloc), (IHx Hloc).
Qed.

Local Lemma target_keeps_structural_binding mode G e h w R B :
  mode_has_mutability mode ->
  @heap_correspond mode G e h ->
  ctx_binds w (typ_and (typ_bnd R) (typ_mut_marker B)) G ->
  exists D,
    ctx_binds (reference_target e w) (typ_and (typ_bnd R) (typ_mut_marker D)) G.
Proof.
  intros Hmut (Hok & _ & _ & _ & _ & _ & Hcorr & _) Hbind.
  unfold reference_target. destruct (get w e) as [y|] eqn:Hr.
  - destruct (reference_location_have_same_record Hmut Hok Hcorr Hr)
      as (R0 & B0 & Hw & Hy).
    pose proof (ctx_binding_unique Hw Hbind) as Heq.
    injection Heq as -> _. now exists typ_bot.
  - now exists B.
Qed.

Local Lemma alias_equivalence_has_same_record mode G e h w x Rw Rx Bw Bx :
  mode_has_mutability mode ->
  @heap_correspond mode G e h ->
  @tyq_var e w x ->
  ctx_binds w (typ_and (typ_bnd Rw) (typ_mut_marker Bw)) G ->
  ctx_binds x (typ_and (typ_bnd Rx) (typ_mut_marker Bx)) G ->
  Rw = Rx.
Proof.
  intros Hmut HH Heq Hw Hx.
  destruct (target_keeps_structural_binding Hmut HH Hw) as [Dw Hwt].
  destruct (target_keeps_structural_binding Hmut HH Hx) as [Dx Hxt].
  assert (Htarget : env_targets_are_locations e).
  { intros a b Hb. destruct (typed_heap_places_refs_and_locations Hmut HH) as [Hin Hdis].
    apply Hdis. eauto. }
  rewrite (alias_equivalence_has_same_target Htarget Heq) in Hwt.
  now injection (ctx_binding_unique Hwt Hxt).
Qed.

Local Lemma exact_opened_member_equivalence mode G e h w x R B S C D E :
  mode_has_mutability mode ->
  @inert mode G ->
  @heap_correspond mode G e h ->
  @tyq_var e w x ->
  ctx_binds w (typ_and (typ_bnd R) (typ_mut_marker B)) G ->
  ctx_binds x (typ_and (typ_bnd S) (typ_mut_marker C)) G ->
  record_has (open w R) D ->
  record_has (open x S) E ->
  label_of D = label_of E ->
  @tyq_typ e (typ_rcd D) (typ_rcd E).
Proof.
  intros Hmut HG Hheap Heq Hw Hx HD HE Hlabel.
  pose proof (alias_equivalence_has_same_record Hmut Hheap Heq Hw Hx) as <-.
  destruct (inert_lookup HG Hw) as [kind Htype].
  inversion Htype; subst.
  destruct (@record_member_before_opening R w D HD) as (D0 & HD0 & ->).
  destruct (@record_member_before_opening R x E HE) as (E0 & HE0 & ->).
  assert (Hlabels : label_of D0 = label_of E0).
  { destruct D0, E0; exact Hlabel. }
  match goal with H : record_type R |- _ =>
    destruct H as [ls Hrec];
    pose proof (record_member_unique_by_label Hrec HD0 HE0 Hlabels) as <-
  end.
  assert (Hind : typ_indep_b 0 (typ_rcd D0)).
  { match goal with H : typ_indep_b 0 R |- _ =>
      clear - HD0 H; revert H; induction HD0; intro HT; [exact HT | |];
      inversion HT; subst; try match goal with HH : typ_nulary (typ_and _ _) |- _ => inversion HH end; eauto
    end. }
  exact (aliased_open_type Heq Hind).
Qed.

Local Lemma typed_defs_record_member_lookup mode G Go e ds T D :
  @ty_defs mode G Go e ds T ->
  record_has T D ->
  exists d, defs_has ds d /\ @ty_def mode G Go e d D.
Proof.
  intro Htyped. induction Htyped; intro Hmember.
  - inversion Hmember; subst.
    exists d. split; [|assumption].
    unfold defs_has. simpl. case_if; congruence.
  - inversion Hmember; subst.
    + match goal with H : record_has T D |- _ =>
        destruct (IHHtyped H) as (d0 & Hlookup & Hdef)
      end.
      exists d0. split; [|assumption].
      unfold defs_has, defs_hasnt in *. simpl. case_if; congruence.
    + match goal with H : record_has (typ_rcd _) _ |- _ => inversion H; subst end.
      exists d. split; [|assumption].
      unfold defs_has. simpl. case_if; congruence.
Qed.

Local Lemma opened_heap_type_member_exact mode G e h y R A S T :
  @heap_correspond mode G e h ->
  ctx_binds y (typ_and (typ_bnd R) (typ_mut_marker typ_bot)) G ->
  y \in dom h ->
  record_has (open y R) (dec_typ (typ_label_normal A) S T) ->
  S = T.
Proof.
  intros (_ & _ & _ & _ & _ & _ & _ & Hitems) Hbind Hy Hmember.
  pose proof (Hitems y Hy) as Hitem.
  inversion Hitem; subst.
  - match goal with H : ctx_binds y (typ_fun _ _) G |- _ =>
      discriminate (ctx_binding_unique H Hbind)
    end.
  - match goal with H : ctx_binds y (typ_and (typ_bnd ?U) ?B) G |- _ =>
      pose proof (ctx_binding_unique Hbind H) as Heq;
      injection Heq as <- _
    end.
    match goal with H : obj_typing G (objctx_heap y R) e _ (open y R) |- _ =>
      destruct (typed_defs_record_member_lookup H Hmember) as (d & _ & Hdef);
      inversion Hdef; congruence
    end.
Qed.

(* Structural and capability observations use one fewer layer when they
   compare type-member bounds. Selection remains at the current layer. *)
Inductive type_observation :=
| observe_structure : var -> type_observation
| observe_capability : var -> type_observation.

Local Fixpoint context_type_at (G : ctx) (x : var) : option typ :=
  match G with
  | ctx_empty => None
  | ctx_push G y _ T => If x = y then Some T else context_type_at G x
  | ctx_stop G => context_type_at G x
  | ctx_hide G => context_type_at G x
  end.

Local Lemma context_type_at_binds G x T :
  ctx_binds x T G ->
  context_type_at G x = Some T.
Proof.
  induction 1; simpl; try assumption; case_if; congruence.
Qed.

Local Definition context_capability_upper G x :=
  match context_type_at G x with
  | Some (typ_and (typ_bnd _) (typ_rcd (dec_typ (typ_label_refcap _) _ U))) => U
  | _ => typ_top
  end.

Local Definition exact_object_member G e x D :=
  exists R B,
    ctx_binds (reference_target e x) (typ_and (typ_bnd R) (typ_mut_marker B)) G /\
    record_has (open (reference_target e x) R) D.

Local Definition semantic_bounds
    (earlier : type_observation -> typ -> Prop) Lower ExactLower ExactUpper Upper :=
  (forall p u, earlier p (open u Lower) -> earlier p (open u ExactLower)) /\
  (forall p u, earlier p (open u ExactUpper) -> earlier p (open u Upper)).

Local Definition nocap_observation mode G
    (earlier : type_observation -> typ -> Prop) x : Prop :=
  mode_has_top_nm_complement mode ->
  exists p u, earlier p (open u (context_capability_upper G x)).

Inductive observes_type mode G e (earlier : type_observation -> typ -> Prop)
  : type_observation -> typ -> Prop :=
| observes_top p : observes_type mode G e earlier p typ_top
| observes_nocap x :
    nocap_observation mode G earlier x ->
    observes_type mode G e earlier (observe_capability x) typ_nocap
| observes_and p S T :
    observes_type mode G e earlier p S ->
    observes_type mode G e earlier p T ->
    observes_type mode G e earlier p (typ_and S T)
| observes_or_l p S T :
    observes_type mode G e earlier p S ->
    observes_type mode G e earlier p (typ_or S T)
| observes_or_r p S T :
    observes_type mode G e earlier p T ->
    observes_type mode G e earlier p (typ_or S T)
| observes_struct_bnd x T :
    observes_type mode G e earlier (observe_structure x) (open x T) ->
    observes_type mode G e earlier (observe_capability x) (open x T) ->
    observes_type mode G e earlier (observe_structure x) (typ_bnd T)
| observes_cap_bnd x T :
    observes_type mode G e earlier (observe_capability x) (typ_bnd T)
| observes_fun p S T :
    observes_type mode G e earlier p (typ_fun S T)
| observes_struct_normal x A S T Q :
    exact_object_member G e x (dec_typ (typ_label_normal A) Q Q) ->
    semantic_bounds earlier S Q Q T ->
    observes_type mode G e earlier (observe_structure x) (typ_rcd (dec_typ (typ_label_normal A) S T))
| observes_cap_normal x A S T :
    observes_type mode G e earlier (observe_capability x) (typ_rcd (dec_typ (typ_label_normal A) S T))
| observes_struct_marker x M S T :
    observes_type mode G e earlier (observe_structure x) (typ_rcd (dec_typ (typ_label_refcap M) S T))
| observes_cap_marker x M S T :
    semantic_bounds earlier S typ_bot (context_capability_upper G x) T ->
    observes_type mode G e earlier (observe_capability x) (typ_rcd (dec_typ (typ_label_refcap M) S T))
| observes_struct_fld x a S T S0 T0 :
    exact_object_member G e x (dec_fld a S0 T0) ->
    @subtyp mode G objctx_empty e S S0 ->
    @subtyp mode G objctx_empty e T0 T ->
    observes_type mode G e earlier (observe_structure x) (typ_rcd (dec_fld a S T))
| observes_cap_fld x a S T :
    observes_type mode G e earlier (observe_capability x) (typ_rcd (dec_fld a S T))
| observes_struct_met x m C Z R C0 Z0 R0 :
    exact_object_member G e x (dec_met m C0 Z0 R0) ->
    @method_subtype_components mode G e C0 Z0 R0 C Z R ->
    observes_type mode G e earlier (observe_structure x) (typ_rcd (dec_met m C Z R))
| observes_cap_met x m C Z R :
    observes_type mode G e earlier (observe_capability x) (typ_rcd (dec_met m C Z R))
| observes_sel_normal p x A u T :
    exact_object_member G e x (dec_typ (typ_label_normal A) T T) ->
    observes_type mode G e earlier p (open u T) ->
    observes_type mode G e earlier p (typ_sel (avar_f x) (typ_label_normal A) (avar_f u))
| observes_sel_cap p x M u :
    observes_type mode G e earlier p (open u (context_capability_upper G x)) ->
    observes_type mode G e earlier p (typ_sel (avar_f x) (typ_label_refcap M) (avar_f u)).

Local Fixpoint layered_observation mode G e n : type_observation -> typ -> Prop :=
  match n with
  | O => observes_type mode G e (fun _ _ => False)
  | S k => observes_type mode G e (layered_observation mode G e k)
  end.

Local Lemma semantic_bounds_equivalent_view e earlier S1 S2 L U T1 T2 :
  (forall p S T, @tyq_typ e S T -> earlier p S -> earlier p T) ->
  (forall u, @tyq_typ e (open u S1) (open u S2)) ->
  (forall u, @tyq_typ e (open u T1) (open u T2)) ->
  semantic_bounds earlier S1 L U T1 ->
  semantic_bounds earlier S2 L U T2.
Proof.
  intros Hprev Hlower Hupper [Hl Hu]. split; intros p u Hobs.
  - apply Hl, (Hprev _ (open u S2)); [now apply type_equivalence_symmetric | exact Hobs].
  - apply (Hprev _ (open u T1)); auto.
Qed.

Local Lemma observation_layer_equivalence mode G e earlier :
  env_targets_are_locations e ->
  (forall p S T, @tyq_typ e S T -> earlier p S -> earlier p T) ->
  forall S T, @tyq_typ e S T ->
  forall p, observes_type mode G e earlier p S ->
    observes_type mode G e earlier p T.
Proof.
  intros Hloc Hprev S T Heq. revert Hloc Hprev.
  induction Heq; intros Hloc Hprev p Hobs.
  - exact Hobs.
  - inversion H; subst T.
    + inversion Hobs; subst. apply observes_and; eauto.
    + inversion Hobs; subst; eauto using observes_or_l, observes_or_r.
  - apply observes_fun.
  - inversion Hobs; subst.
    + eapply observes_struct_fld; [eassumption | |].
      * eapply subtyp_trans with (T := t11); [apply subtyp_tyq; now apply type_equivalence_symmetric | eassumption].
      * eapply subtyp_trans with (T := t12); [eassumption | now apply subtyp_tyq].
    + apply observes_cap_fld.
  - destruct B as [A|M]; inversion Hobs; subst.
    + eapply observes_struct_normal; [eassumption |].
      eapply semantic_bounds_equivalent_view; eassumption.
    + apply observes_cap_normal.
    + apply observes_struct_marker.
    + apply observes_cap_marker.
      eapply semantic_bounds_equivalent_view; eassumption.
  - inversion Hobs; subst.
    eapply observes_sel_normal; [|eassumption].
    unfold exact_object_member in *.
    rewrite <- (alias_equivalence_has_same_target Hloc H).
    eassumption.
  - exact Hobs.
  - inversion Hobs; subst.
    + apply observes_struct_bnd; eauto.
    + apply observes_cap_bnd.
  - inversion Hobs; subst.
    + eapply observes_struct_met; [eassumption |].
      eapply method_subtype_components_trans; [eassumption |].
      apply method_subtype_components_equivalence with (m := m).
      constructor; assumption.
    + apply observes_cap_met.
Qed.

Local Lemma layered_observation_equivalence mode G e :
  env_targets_are_locations e ->
  forall n p S T, @tyq_typ e S T ->
    layered_observation mode G e n p S ->
    layered_observation mode G e n p T.
Proof.
  intros Henv n. induction n; simpl; intros p S T Heq Hobs;
    eapply observation_layer_equivalence; eauto; contradiction.
Qed.

Local Lemma exact_object_members_unique mode G e x D E :
  @inert mode G ->
  exact_object_member G e x D ->
  exact_object_member G e x E ->
  label_of D = label_of E ->
  D = E.
Proof.
  intros Hiner (R & B & Hbind & HD) (R' & B' & Hbind' & HE) Hlabel.
  pose proof (ctx_binding_unique Hbind Hbind') as Heq.
  injection Heq as <- <-.
  destruct (@record_member_before_opening R (reference_target e x) D HD)
    as (D0 & HD0 & ->).
  destruct (@record_member_before_opening R (reference_target e x) E HE)
    as (E0 & HE0 & ->).
  assert (Hlabels : label_of D0 = label_of E0) by (destruct D0, E0; exact Hlabel).
  destruct (inert_lookup Hiner Hbind) as [k Hkind]. inversion Hkind; subst.
  match goal with H : record_type R |- _ =>
    destruct H as [ls Hrecord];
    now rewrite (record_member_unique_by_label Hrecord HD0 HE0 Hlabels)
  end.
Qed.

Local Lemma inert_binding_has_kind mode G x T :
  @inert mode G ->
  ctx_binds x T G ->
  exists k G0, inert_vk k /\ @inert_typ mode T k /\ ctx_binds_k_after x k T G G0.
Proof.
  intro HG. induction HG; intro Hb; inversion Hb; subst.
  - eexists _, _. repeat split; [eassumption | eassumption | constructor].
  - destruct (IHHG ltac:(eassumption)) as (k & G0 & Hk & HT & Hlook).
    exists k, G0. repeat split; try eassumption.
    now apply ctx_binds_k_n.
Qed.

Local Lemma bound_object_outside_environment mode G e h x R B :
  mode_has_mutability mode ->
  @inert mode G ->
  @heap_correspond mode G e h ->
  ctx_binds x (typ_and (typ_bnd R) (typ_mut_marker B)) G ->
  x # e ->
  x \in dom h /\ B = typ_bot.
Proof.
  intros Hmut HG (_ & _ & _ & _ & Hdomloc & Hdomref & _) HB Hnone.
  destruct (inert_binding_has_kind HG HB) as (k & G0 & Hk & HT & Hlook).
  inversion Hk; subst k.
  - split.
    + rewrite <- Hdomloc. exact (ctx_binding_kind_in_dom Hlook).
    + inversion HT; subst.
      match goal with H : @refcap_inert_type mode (typ_mut_marker B) v_loc |- _ =>
        unfold refcap_inert_type in H;
        assert (mode_refcaps' mode = mode_refcaps_mutability)
          as Hcaps by (destruct mode; discriminate || reflexivity);
        rewrite Hcaps in H; inversion H; reflexivity
      end.
  - exfalso. apply Hnone. rewrite <- Hdomref. exact (ctx_binding_kind_in_dom Hlook).
Qed.

Local Lemma reference_target_outside_env e x :
  env_targets_are_locations e ->
  reference_target e x # e.
Proof.
  intro Henv. unfold reference_target. destruct (get x e) as [y|] eqn:He.
  - exact (Henv x y He).
  - now apply get_none_inv.
Qed.

Local Lemma record_member_after_opening R D x :
  record_has R D -> record_has (open x R) (open x D).
Proof.
  induction 1; simpl; constructor; assumption.
Qed.

Local Lemma exact_object_normal_member_equal_bounds mode G e h x A S T :
  mode_has_mutability mode ->
  @inert mode G ->
  @heap_correspond mode G e h ->
  exact_object_member G e x (dec_typ (typ_label_normal A) S T) ->
  S = T.
Proof.
  intros Hmut HG HH (R & B & HB & Hdecl).
  pose proof (typed_heap_env_location_targets Hmut HH) as Henv.
  destruct (bound_object_outside_environment Hmut HG HH HB
      (reference_target_outside_env x Henv)) as [Hy ->].
  eapply opened_heap_type_member_exact; eassumption.
Qed.

Local Lemma method_components_reflexive mode G e C Z R :
  @method_subtype_components mode G e C Z R C Z R.
Proof.
  split; [apply subtyp_refl |]. split; [auto |].
  exists (\{} : vars). split; intros; apply subtyp_refl.
Qed.

Local Lemma exact_declaration_observed mode G e h earlier x M D :
  mode_has_mutability mode ->
  @inert mode G ->
  @heap_correspond mode G e h ->
  record_dec D ->
  exact_object_member G e x (open M D) ->
  observes_type mode G e earlier (observe_structure x) (typ_rcd (open M D)) /\
  observes_type mode G e earlier (observe_capability x) (typ_rcd (open M D)).
Proof.
  intros Hmut HG HH HD. destruct HD; simpl; intro Hdecl.
  - split; [|apply observes_cap_normal].
    eapply observes_struct_normal; [exact Hdecl | split; auto].
  - pose proof (@exact_object_normal_member_equal_bounds mode G e h x A _ _
      Hmut HG HH Hdecl) as He.
    simpl in He. rewrite <- He in *.
    split; [|apply observes_cap_normal].
    eapply observes_struct_normal; [exact Hdecl | split; auto].
  - split; [|apply observes_cap_fld].
    eapply observes_struct_fld; [exact Hdecl | apply subtyp_refl | apply subtyp_refl].
  - split; [|apply observes_cap_met].
    eapply observes_struct_met; [exact Hdecl |apply method_components_reflexive].
Qed.

Local Lemma exact_record_observed mode G e h earlier x y R ls :
  mode_has_mutability mode ->
  @inert mode G ->
  @heap_correspond mode G e h ->
  record_typ R ls ->
  (forall D, record_has R D -> exact_object_member G e x (open y D)) ->
  observes_type mode G e earlier (observe_structure x) (open y R) /\
  observes_type mode G e earlier (observe_capability x) (open y R).
Proof.
  intros Hmut HG HH HR. induction HR; intro Hmembers; simpl.
  - eapply exact_declaration_observed; try eassumption.
    apply Hmembers. apply rh_one.
  - destruct (IHHR ltac:(intros D0 HD; apply Hmembers; now apply rh_andl)) as [Hhead1 Hhead2].
    assert (Hexact : exact_object_member G e x (open y D))
      by (apply Hmembers; apply rh_andr, rh_one).
    destruct (@exact_declaration_observed mode G e h earlier x y D Hmut HG HH H Hexact) as [Hlast1 Hlast2].
    split; now apply observes_and.
Qed.

Local Lemma reference_target_equivalence e x :
  @tyq_var e (reference_target e x) x.
Proof.
  unfold reference_target. destruct (get x e) as [y|] eqn:He.
  - apply tyq_var_sym, tyq_var_binds. exact He.
  - apply tyq_var_refl.
Qed.

Local Lemma inert_mutable_binding_shape mode G x T :
  mode_has_mutability mode ->
  @inert mode G ->
  ctx_binds x T G ->
  exists R B ls, T = typ_and (typ_bnd R) (typ_mut_marker B) /\
    record_typ R ls /\ typ_indep_b 0 R.
Proof.
  intros Hmut HG Hb.
  destruct (inert_lookup HG Hb) as [k Hkind].
  inversion Hkind; subst.
  - destruct mode; discriminate.
  - match goal with
    | HR : record_type ?R, HM : @refcap_inert_type mode _ ?k |- _ =>
      destruct HR as [ls HR];
      unfold refcap_inert_type in HM;
      assert (mode_refcaps' mode = mode_refcaps_mutability)
        as Hcaps by (destruct mode; discriminate || reflexivity);
      rewrite Hcaps in HM; inversion HM; subst;
      repeat eexists; eassumption
    end.
Qed.

Local Lemma context_binding_observed mode G e h earlier x T :
  mode_has_mutability mode ->
  @inert mode G ->
  @heap_correspond mode G e h ->
  (forall p S U, @tyq_typ e S U -> earlier p S -> earlier p U) ->
  ctx_binds x T G ->
  observes_type mode G e earlier (observe_structure x) T /\
  observes_type mode G e earlier (observe_capability x) T.
Proof.
  intros Hmut HG HH Hprev Hb.
  destruct (inert_mutable_binding_shape Hmut HG Hb) as (R & B & ls & -> & Hrecord & Hind).
  assert (Henv : env_targets_are_locations e)
    by exact (typed_heap_env_location_targets Hmut HH).
  destruct (target_keeps_structural_binding Hmut HH Hb) as [U Htarget].
  assert (Hexact : forall D, record_has R D ->
      exact_object_member G e x (open (reference_target e x) D)).
  { intros D HD. exists R, U. split; [exact Htarget | now apply record_member_after_opening]. }
  destruct (@exact_record_observed mode G e h earlier x (reference_target e x) R ls Hmut HG HH Hrecord Hexact) as [HopenS HopenC].
  assert (Hequiv : @tyq_typ e (open (reference_target e x) R) (open x R)).
  { apply aliased_open_type; [apply reference_target_equivalence | exact Hind]. }
  split; apply observes_and.
  - apply observes_struct_bnd; eapply observation_layer_equivalence; eassumption.
  - apply observes_struct_marker.
  - apply observes_cap_bnd.
  - apply observes_cap_marker. unfold context_capability_upper.
    rewrite (context_type_at_binds Hb). split; auto.
Qed.

Local Lemma observed_type_member_sub mode G e earlier p A S1 T1 S2 T2 :
  (forall u q, earlier q (open u S2) -> earlier q (open u S1)) ->
  (forall u q, earlier q (open u T1) -> earlier q (open u T2)) ->
  observes_type mode G e earlier p (typ_rcd (dec_typ A S1 T1)) ->
  observes_type mode G e earlier p (typ_rcd (dec_typ A S2 T2)).
Proof.
  intros Hlow Hup Hobs. destruct A as [A|M]; inversion Hobs; subst.
  - eapply observes_struct_normal; [eassumption |].
    unfold semantic_bounds in *. intuition eauto.
  - apply observes_cap_normal.
  - apply observes_struct_marker.
  - apply observes_cap_marker. unfold semantic_bounds in *. intuition eauto.
Qed.

Local Lemma observed_selection_lower mode G e n p x A y S T :
  layered_observation mode G e (Datatypes.S n) (observe_structure x)
    (typ_rcd (dec_typ A S T)) ->
  layered_observation mode G e (Datatypes.S n) (observe_capability x)
    (typ_rcd (dec_typ A S T)) ->
  layered_observation mode G e n p (open y S) ->
  layered_observation mode G e n p (typ_sel (avar_f x) A (avar_f y)).
Proof.
  intros Hstruct Hcap Hobs.
  destruct A as [A|M].
  - simpl in Hstruct. inversion Hstruct; subst.
    match goal with H : semantic_bounds _ _ _ _ _ |- _ =>
      destruct H as [Hl _]; specialize (Hl p y Hobs)
    end.
    destruct n; simpl in *; eapply observes_sel_normal; eassumption.
  - simpl in Hcap. inversion Hcap; subst.
    match goal with H : semantic_bounds _ _ _ _ _ |- _ =>
      destruct H as [Hl _]; specialize (Hl p y Hobs)
    end.
    destruct n; simpl in Hl; inversion Hl.
Qed.

Local Lemma observed_selection_upper mode G e n p x A y S T :
  @inert mode G ->
  layered_observation mode G e (Datatypes.S n) (observe_structure x)
    (typ_rcd (dec_typ A S T)) ->
  layered_observation mode G e (Datatypes.S n) (observe_capability x)
    (typ_rcd (dec_typ A S T)) ->
  layered_observation mode G e n p (typ_sel (avar_f x) A (avar_f y)) ->
  layered_observation mode G e n p (open y T).
Proof.
  intros Hiner Hstruct Hcap Hobs. destruct A as [A|M].
  - simpl in Hstruct. inversion Hstruct; subst.
    match goal with H : semantic_bounds _ _ ?Q _ _ |- _ =>
      destruct H as [_ Hu]
    end.
    destruct n; simpl in Hobs; inversion Hobs; subst;
    match goal with
    | H1 : exact_object_member G e x (dec_typ _ ?U ?U),
      H2 : exact_object_member G e x (dec_typ _ ?V ?V) |- _ =>
        tryif constr_eq U V then fail else
          assert (Heq : U = V)
            by (pose proof (exact_object_members_unique Hiner H1 H2 eq_refl) as H; congruence);
          subst V; eapply Hu; eassumption
    end.
  - simpl in Hcap. inversion Hcap; subst.
    match goal with H : semantic_bounds _ _ _ _ _ |- _ =>
      destruct H as [_ Hu]
    end.
    destruct n; simpl in Hobs; inversion Hobs; subst; eapply Hu; eassumption.
Qed.

Local Lemma observed_type_member_merge mode G e n p A S1 T1 S2 T2 :
  @inert mode G ->
  layered_observation mode G e n p (typ_rcd (dec_typ A S1 T1)) ->
  layered_observation mode G e n p (typ_rcd (dec_typ A S2 T2)) ->
  layered_observation mode G e n p
    (typ_rcd (dec_typ A (typ_or S1 S2) (typ_and T1 T2))).
Proof.
  intros Hiner Hleft Hright.
  destruct A as [A|M]; destruct p as [x|x]; destruct n; simpl in *.
  all: try solve [apply observes_cap_normal | apply observes_struct_marker].
  - inversion Hleft; subst. eapply observes_struct_normal; [eassumption |].
    split; contradiction.
  - inversion Hleft; inversion Hright; subst.
    match goal with
    | H1 : exact_object_member G e x (dec_typ _ ?U ?U),
      H2 : exact_object_member G e x (dec_typ _ ?V ?V) |- _ =>
        tryif constr_eq U V then fail else
          assert (Heq : U = V)
            by (pose proof (exact_object_members_unique Hiner H1 H2 eq_refl) as H; congruence);
          subst V
    end.
    eapply observes_struct_normal; [eassumption |].
    match goal with
    | H1 : semantic_bounds _ S1 _ _ T1, H2 : semantic_bounds _ S2 _ _ T2 |- _ =>
      destruct H1 as [HL1 HU1]; destruct H2 as [HL2 HU2]
    end.
    split; simpl; intros q u Hobs; destruct n; simpl in *.
    all: try solve [inversion Hobs; subst; eauto].
    all: apply observes_and; eauto.
  - apply observes_cap_marker. split; contradiction.
  - inversion Hleft; inversion Hright; subst.
    apply observes_cap_marker.
    match goal with
    | H1 : semantic_bounds _ S1 _ _ T1, H2 : semantic_bounds _ S2 _ _ T2 |- _ =>
      destruct H1 as [HL1 HU1]; destruct H2 as [HL2 HU2]
    end.
    split; simpl; intros q u Hobs; destruct n; simpl in *.
    all: try solve [inversion Hobs; subst; eauto].
    all: apply observes_and; eauto.
Qed.

Local Lemma observed_top_split mode G e earlier p M S T :
  mode_has_top_nm_subtype_boundless mode ->
  observes_type mode G e earlier p
    (typ_or typ_nocap (typ_rcd (dec_typ (typ_label_refcap M) S T))).
Proof.
  intro Hboundless. destruct p as [x|x].
  - apply observes_or_r, observes_struct_marker.
  - apply observes_or_l, observes_nocap. unfold nocap_observation.
    intro Hcompl. congruence.
Qed.

Local Lemma observed_complement_split mode G e earlier p :
  mode_has_top_nm_complement mode ->
  observes_type mode G e earlier p (typ_or typ_nocap (typ_mut_marker typ_bot)).
Proof.
  intro Hcompl. destruct p as [x|x].
  - apply observes_or_r, observes_struct_marker.
  - destruct (classic (nocap_observation mode G earlier x)) as [Hnonempty | Hempty].
    + apply observes_or_l, observes_nocap. exact Hnonempty.
    + apply observes_or_r, observes_cap_marker. split; [auto |].
      intros q u HQ. exfalso. apply Hempty. intros _. now exists q, u.
Qed.

Local Lemma observed_complement_empty mode G e n p :
  mode_has_top_nm_complement mode ->
  ~ layered_observation mode G e n p (typ_and typ_nocap (typ_mut_marker typ_bot)).
Proof.
  intros Hcompl Hobs. destruct n; simpl in Hobs; inversion Hobs; subst;
  match goal with H : observes_type _ _ _ _ _ typ_nocap |- _ =>
    inversion H; subst
  end;
  match goal with
  | H : nocap_observation _ _ _ _ |- _ =>
    destruct (H Hcompl) as (q & u & Hpoint)
  end; [exact Hpoint |].
  match goal with H : observes_type _ _ _ _ _ (typ_mut_marker typ_bot) |- _ =>
    inversion H; subst
  end.
  match goal with H : semantic_bounds _ _ _ _ _ |- _ =>
    destruct H as [_ Hu]; specialize (Hu q u Hpoint)
  end.
  destruct n; simpl in Hu; inversion Hu.
Qed.

Local Lemma layered_context_binding_observed mode G e h x T n :
  mode_has_mutability mode ->
  @inert mode G ->
  @heap_correspond mode G e h ->
  ctx_binds x T G ->
  layered_observation mode G e n (observe_structure x) T /\
  layered_observation mode G e n (observe_capability x) T.
Proof.
  intros Hmut Hiner Hheap Hb. destruct n; simpl;
    eapply context_binding_observed; try eassumption; try contradiction.
  intros p S T' Heq Hobs.
  eapply layered_observation_equivalence; try eassumption.
  now apply (typed_heap_env_location_targets Hmut Hheap).
Qed.

Local Lemma observed_field_sub mode G e earlier p a S1 T1 S2 T2 :
  @subtyp mode G objctx_empty e S2 S1 ->
  @subtyp mode G objctx_empty e T1 T2 ->
  observes_type mode G e earlier p (typ_rcd (dec_fld a S1 T1)) ->
  observes_type mode G e earlier p (typ_rcd (dec_fld a S2 T2)).
Proof.
  intros Hs Ht Hobs. inversion Hobs; subst.
  - eapply observes_struct_fld; [eassumption | |];
      eapply subtyp_trans; eassumption.
  - apply observes_cap_fld.
Qed.

Local Lemma observed_method_sub mode G e earlier p m C Z R C' Z' R' :
  @method_subtype_components mode G e C Z R C' Z' R' ->
  observes_type mode G e earlier p (typ_rcd (dec_met m C Z R)) ->
  observes_type mode G e earlier p (typ_rcd (dec_met m C' Z' R')).
Proof.
  intros Hmethod Hobs. inversion Hobs; subst.
  - eapply observes_struct_met; [eassumption |].
    eapply method_subtype_components_trans; eassumption.
  - apply observes_cap_met.
Qed.

Local Lemma layered_marker_top mode G e n p :
  layered_observation mode G e n p (typ_mut_marker typ_top).
Proof.
  destruct p as [x|x]; destruct n; simpl; try apply observes_struct_marker.
  - apply observes_cap_marker. split; auto.
  - apply observes_cap_marker. split; intros; auto.
    destruct n; apply observes_top.
Qed.

Local Lemma observations_dist mode G e earlier p A B C :
  observes_type mode G e earlier p (typ_and A (typ_or B C)) ->
  observes_type mode G e earlier p (typ_or (typ_and A B) (typ_and A C)).
Proof.
  intro Hobs. inversion Hobs; subst.
  match goal with H : observes_type _ _ _ _ _ (typ_or _ _) |- _ => inversion H; subst end.
  - apply observes_or_l, observes_and; assumption.
  - apply observes_or_r, observes_and; assumption.
Qed.

Local Lemma layered_typing_sound mode G e h :
  mode_has_mutability mode ->
  @inert mode G ->
  @heap_correspond mode G e h ->
  (forall x T, @ty_var mode G objctx_empty e x T ->
    forall n, layered_observation mode G e n (observe_structure x) T /\
      layered_observation mode G e n (observe_capability x) T) /\
  (forall S T, @subtyp mode G objctx_empty e S T ->
    forall n p, layered_observation mode G e n p S ->
      layered_observation mode G e n p T).
Proof.
  intros Hmut Hiner Hheap.
  pose proof (typed_heap_env_location_targets Hmut Hheap) as Henv.
  assert (Hgeneral :
    (forall G' Go e' x T, @ty_var mode G' Go e' x T ->
      G' = G -> e' = e -> forall n,
      layered_observation mode G e n (observe_structure x) T /\
      layered_observation mode G e n (observe_capability x) T) /\
    (forall G' Go e' S T, @subtyp mode G' Go e' S T ->
      G' = G -> e' = e -> forall n p,
      layered_observation mode G e n p S -> layered_observation mode G e n p T) /\
    (forall G' Go e' S T, @ty_incap mode G' Go e' S T -> True)).
  {
    apply ts_mutind.
    all: try solve [intros; exact I].
    - intros G' e' x T Hb -> -> n. eapply layered_context_binding_observed; eassumption.
    - intros G' e' x T Hvar IH _ _ _ -> -> n.
      destruct (IH eq_refl eq_refl n) as [Hs Hc].
      destruct n; simpl in *; split; auto using observes_struct_bnd, observes_cap_bnd.
    - intros G' e' x T Hvar IH _ -> -> n.
      destruct (IH eq_refl eq_refl n) as [Hs _].
      destruct n; simpl in *; inversion Hs; subst; auto.
    - intros G' e' x S T _ IHs _ IHt -> -> n.
      destruct (IHs eq_refl eq_refl n) as [Hs Hsc].
      destruct (IHt eq_refl eq_refl n) as [Ht Htc].
      destruct n; split; apply observes_and; assumption.
    - intros G' e' x S T _ IHs _ IHt -> -> n.
      destruct (IHs eq_refl eq_refl n) as [Hs Hc].
      split; eapply IHt; eauto.
    - intros G' e' x T _ _ _ -> -> n. split; apply layered_marker_top.
    - intros G' e' T -> -> n p _. destruct n; apply observes_top.
    - intros G' e' T -> -> n p Hobs. destruct n; inversion Hobs.
    - intros; assumption.
    - intros G' e' S T U _ IHs _ IHt -> -> n p Hobs.
      exact (IHt eq_refl eq_refl n p (IHs eq_refl eq_refl n p Hobs)).
    - intros G' e' S T -> -> n p Hobs. destruct n; inversion Hobs; assumption.
    - intros G' e' S T -> -> n p Hobs. destruct n; inversion Hobs; assumption.
    - intros G' e' S T U _ IHs _ IHt -> -> n p Hobs.
      pose proof (IHs eq_refl eq_refl n p Hobs) as Hs.
      pose proof (IHt eq_refl eq_refl n p Hobs) as Ht.
      destruct n; apply observes_and; assumption.
    - intros G' e' S T -> -> n p Hobs. destruct n; now apply observes_or_l.
    - intros G' e' S T -> -> n p Hobs. destruct n; now apply observes_or_r.
    - intros G' e' S T U _ IHs _ IHt -> -> n p Hobs.
      specialize (IHs eq_refl eq_refl n p).
      specialize (IHt eq_refl eq_refl n p).
      destruct n; inversion Hobs; subst; eauto.
    - intros G' e' a S1 S2 T1 T2 Hs _ Ht _ -> -> n p Hobs.
      destruct n; apply observed_field_sub with (S1 := S2) (T1 := T1); assumption.
    - intros G' e' A S1 T1 S2 T2 _ IHs _ IHt -> -> n p Hobs.
      destruct n as [|n]; simpl in Hobs |- *; eapply observed_type_member_sub; try eassumption.
      + intros; contradiction.
      + intros; contradiction.
      + intros u q Hq. exact (IHs u eq_refl eq_refl n q Hq).
      + intros u q Hq. exact (IHt u eq_refl eq_refl n q Hq).
    - intros G' e' x A y S T _ IH -> -> n p Hobs.
      destruct (IH eq_refl eq_refl (Datatypes.S n)) as [Hs Hc].
      eapply observed_selection_lower; eassumption.
    - intros G' e' x A y S T _ IH -> -> n p Hobs.
      destruct (IH eq_refl eq_refl (Datatypes.S n)) as [Hs Hc].
      eapply observed_selection_upper; eassumption.
    - intros L G' e' S1 T1 S2 T2 _ _ _ _ _ -> -> n p Hobs.
      destruct n; apply observes_fun.
    - intros L G' e' m C Z R C' Z' R' Hz _ Hc _ Hind Hr _ -> -> n p Hobs.
      assert (Hmethod : @method_subtype_components mode G e C Z R C' Z' R').
      { split; [exact Hz |]. split; [exact Hind |]. now exists L. }
      destruct n; eapply observed_method_sub; eassumption.
    - intros G' e' S T Heq -> -> n p Hobs.
      eapply layered_observation_equivalence; eassumption.
    - intros G' e' A S1 T1 S2 T2 -> -> n p Hobs.
      assert (Hboth : layered_observation mode G e n p (typ_rcd (dec_typ A S1 T1)) /\
        layered_observation mode G e n p (typ_rcd (dec_typ A S2 T2))).
      { destruct n; inversion Hobs; subst; auto. }
      destruct Hboth. now apply observed_type_member_merge.
    - intros G' e' A B C -> -> n p Hobs. destruct n; now apply observations_dist.
    - intros G' e' T -> -> n p Hobs.
      destruct n; inversion Hobs; apply observes_cap_bnd.
    - intros G' e' A S T -> -> n p Hobs.
      destruct n; inversion Hobs; apply observes_cap_normal.
    - intros G' e' a S T -> -> n p Hobs.
      destruct n; inversion Hobs; apply observes_cap_fld.
    - intros G' e' m C Z R -> -> n p Hobs.
      destruct n; inversion Hobs; apply observes_cap_met.
    - intros G' e' Z R _ -> -> n p Hobs. destruct n; apply observes_fun.
    - intros G' e' S T Hmode -> -> n p _. destruct n; now apply observed_top_split.
    - intros G' e' Hmode -> -> n p _. destruct n; now apply observed_complement_split.
    - intros G' e' Hmode -> -> n p Hobs.
      exfalso. eapply observed_complement_empty; eassumption.
    - intros G' e' Hmode -> -> n p _. apply layered_marker_top.
  }
  destruct Hgeneral as [Hvar [Hsub _]].
  split.
  - intros x T HT. exact (Hvar G objctx_empty e x T HT eq_refl eq_refl).
  - intros S T HT. exact (Hsub G objctx_empty e S T HT eq_refl eq_refl).
Qed.

Local Lemma exact_member_from_heap_reference mode G e h w y R B D :
  mode_has_mutability mode ->
  @heap_correspond mode G e h ->
  binds w y e ->
  ctx_binds w (typ_and (typ_bnd R) (typ_mut_marker B)) G ->
  record_has (open y R) D ->
  exact_object_member G e w D.
Proof.
  intros Hmut HH Hw Hbind HD.
  destruct (target_keeps_structural_binding Hmut HH Hbind) as [U HU].
  exists R, U. split; [exact HU |].
  unfold reference_target. change (get w e = Some y) in Hw. now rewrite Hw.
Qed.

Local Lemma precise_method_views_sound mode :
  mode_has_mutability mode ->
  @precise_method_views mode.
Proof.
  intros Hmut G e h w y R B m C Z Ret Ca Za Ra HI _ HH Hw HB HD HT.
  pose proof (exact_member_from_heap_reference Hmut HH Hw HB HD) as Hdecl.
  pose proof (proj1 (proj1 (layered_typing_sound Hmut HI HH) _ _ HT 0)) as Hobs.
  simpl in Hobs. inversion Hobs; subst.
  match goal with HdeclA : exact_object_member G e w (dec_met m ?C0 ?Z0 ?R0) |- _ =>
    tryif constr_eq HdeclA Hdecl then fail else
      pose proof (exact_object_members_unique HI Hdecl HdeclA eq_refl) as Hsame
  end.
  inversion Hsame; subst. assumption.
Qed.

Local Lemma precise_field_views_sound mode G e h w y R B a S T Sa Ta :
  mode_has_mutability mode ->
  @inert mode G ->
  @heap_correspond mode G e h ->
  binds w y e ->
  ctx_binds w (typ_and (typ_bnd R) (typ_mut_marker B)) G ->
  record_has (open y R) (dec_fld a S T) ->
  @ty_var mode G objctx_empty e w (typ_rcd (dec_fld a Sa Ta)) ->
  @subtyp mode G objctx_empty e Sa S /\ @subtyp mode G objctx_empty e T Ta.
Proof.
  intros Hmut HI HH Hw HB HD HT.
  pose proof (exact_member_from_heap_reference Hmut HH Hw HB HD) as Hdecl.
  pose proof (proj1 (proj1 (layered_typing_sound Hmut HI HH) _ _ HT 0)) as Hobs.
  simpl in Hobs. inversion Hobs; subst.
  match goal with HdeclA : exact_object_member G e w (dec_fld a ?S0 ?T0) |- _ =>
    tryif constr_eq HdeclA Hdecl then fail else
      pose proof (exact_object_members_unique HI Hdecl HdeclA eq_refl) as Hsame
  end.
  inversion Hsame; subst. now split.
Qed.

Local Lemma apparent_capability_includes_declared_upper
    mode G e h x R B Upper :
  mode_has_mutability mode ->
  @inert mode G ->
  @heap_correspond mode G e h ->
  ctx_binds x (typ_and (typ_bnd R) (typ_mut_marker B)) G ->
  @ty_var mode G objctx_empty e x (typ_mut_marker Upper) ->
  forall n p u, layered_observation mode G e n p (open u B) ->
    layered_observation mode G e n p (open u Upper).
Proof.
  intros Hmut HI HH HB HT n p u Hinput.
  pose proof (proj2 (proj1 (layered_typing_sound Hmut HI HH)
    _ _ HT (Datatypes.S n))) as Hobs.
  simpl in Hobs. inversion Hobs; subst.
  match goal with H : semantic_bounds _ _ _ _ _ |- _ =>
    destruct H as [_ Hout];
    unfold context_capability_upper in Hout;
    rewrite (context_type_at_binds HB) in Hout;
    exact (Hout p u Hinput)
  end.
Qed.

Local Lemma read_only_binding_excludes_write mode G e h x R :
  mode_has_mutability mode ->
  @inert mode G ->
  @heap_correspond mode G e h ->
  ctx_binds x (typ_and (typ_bnd R) (typ_mut_marker typ_top)) G ->
  ~ @ty_var mode G objctx_empty e x (typ_mut_marker typ_bot).
Proof.
  intros Hmut HI HH HB HT.
  assert (Htop : layered_observation mode G e 0 (observe_structure x) typ_top)
    by apply observes_top.
  pose proof (apparent_capability_includes_declared_upper Hmut HI HH HB HT
      0 (observe_structure x) x Htop) as Hbot.
  inversion Hbot.
Qed.

Local Definition capability_upper_is_protected mode G e B :=
  forall G' e' h',
    preserves_ctx_binds G G' ->
    env_binds_more e e' ->
    @inert mode G' ->
    @heap_correspond mode G' e' h' ->
    exists n p u, layered_observation mode G' e' n p (open u B).

Local Lemma protected_upper_top mode G e :
  @capability_upper_is_protected mode G e typ_top.
Proof.
  intros G' e' h' _ _ _ _.
  destruct (var_fresh (\{} : vars)) as [u _].
  exists 0, (observe_structure u), u. apply observes_top.
Qed.

Local Lemma protected_upper_weakens mode G G' e e' B :
  preserves_ctx_binds G G' ->
  env_binds_more e e' ->
  @capability_upper_is_protected mode G e B ->
  @capability_upper_is_protected mode G' e' B.
Proof.
  intros Hkeep Henv Hprotected G'' e'' h'' Hkeep' Henv'.
  apply Hprotected.
  - intros v T Hv. now apply Hkeep', Hkeep.
  - intros y w Hw. now apply Henv', Henv.
Qed.

Local Lemma protected_upper_apparent_view mode G e x R B A :
  mode_has_mutability mode ->
  ctx_binds x (typ_and (typ_bnd R) (typ_mut_marker B)) G ->
  @ty_var mode G objctx_empty e x (typ_mut_marker A) ->
  @capability_upper_is_protected mode G e B ->
  @capability_upper_is_protected mode G e A.
Proof.
  intros Hmut HB Hty Hprotected G' e' h' Hkeep Henv HI HH.
  destruct (Hprotected G' e' h' Hkeep Henv HI HH) as (n & p & u & Hobs).
  assert (Hty' : @ty_var mode G' objctx_empty e' x (typ_mut_marker A)).
  { eapply (proj1 (variable_judgments_extend mode)); eassumption. }
  exists n, p, u.
  eapply (@apparent_capability_includes_declared_upper mode G' e' h' x R B A);
    eauto.
Qed.

Local Lemma protected_upper_from_receiver mode G e x R B A :
  ctx_binds x (typ_and (typ_bnd R) (typ_mut_marker B)) G ->
  @capability_upper_is_protected mode G e B ->
  @capability_upper_is_protected mode G e
    (typ_or A (typ_sel (avar_f x) typ_label_mutability (avar_b 0))).
Proof.
  intros HB Hprotected G' e' h' Hkeep Henv HI HH.
  destruct (Hprotected G' e' h' Hkeep Henv HI HH) as (n & p & u & Hobs).
  exists n, p, u.
  assert (Hcap : context_capability_upper G' x = B).
  { unfold context_capability_upper. now rewrite (context_type_at_binds (Hkeep _ _ HB)). }
  change (layered_observation mode G' e' n p
    (typ_or (open u A)
      (typ_sel (avar_f x) typ_label_mutability (open u (avar_b 0))))).
  replace (open u (avar_b 0)) with (avar_f u) by (simpl; case_if; congruence).
  destruct n; apply observes_or_r, observes_sel_cap; now rewrite Hcap.
Qed.

Local Lemma protected_upper_through_field mode G e x R B T A receiver :
  mode_has_mutability mode ->
  ctx_binds x (typ_and (typ_bnd R) (typ_mut_marker B)) G ->
  @ty_var mode G objctx_empty e x T ->
  @ty_capbnd mode typ_refcap_mutability G objctx_empty e T A ->
  @capability_upper_is_protected mode G e B ->
  @capability_upper_is_protected mode G e
    (typ_or A (typ_sel (avar_f receiver) typ_label_mutability (avar_b 0))).
Proof.
  intros Hmut HB HT Hcap Hprotected.
  pose proof (variable_has_apparent_capability Hmut HT Hcap) as Hty.
  pose proof (@protected_upper_apparent_view mode G e x R B A Hmut HB Hty Hprotected)
    as HA.
  intros G' e' h' Hkeep Henv HI HH.
  destruct (HA G' e' h' Hkeep Henv HI HH) as (n & p & u & Hobs).
  exists n, p, u. destruct n; now apply observes_or_l.
Qed.

Local Lemma protected_reference_excludes_write mode G e h x R B :
  mode_has_mutability mode ->
  @inert mode G ->
  @heap_correspond mode G e h ->
  ctx_binds x (typ_and (typ_bnd R) (typ_mut_marker B)) G ->
  @capability_upper_is_protected mode G e B ->
  ~ @ty_var mode G objctx_empty e x (typ_mut_marker typ_bot).
Proof.
  intros Hmut HI HH HB Hprotect HT.
  destruct (Hprotect G e h ltac:(intros ? ? H; exact H)
     ltac:(intros ? ? H; exact H) HI HH) as (n & p & u & Hobs).
  pose proof (@apparent_capability_includes_declared_upper mode G e h x R B typ_bot
    Hmut HI HH HB HT n p u Hobs) as Hbot.
  destruct n; inversion Hbot.
Qed.

Local Definition reference_is_protected mode G e w :=
  exists R B, ctx_binds w (typ_and (typ_bnd R) (typ_mut_marker B)) G /\
    @capability_upper_is_protected mode G e B.

Local Lemma top_marker_protects_reference mode G e w R :
  ctx_binds w (typ_and (typ_bnd R) (typ_mut_marker typ_top)) G ->
  @reference_is_protected mode G e w.
Proof. intro H. exists R, typ_top. split; [exact H | apply protected_upper_top]. Qed.

Local Lemma initial_readonly_stack_excludes_old_write mode G c U z r Rz Rr x a v :
  mode_has_mutability mode ->
  @ty_config mode G c U ->
  ctx_binds z (typ_and (typ_bnd Rz) (typ_mut_marker typ_top)) G ->
  ctx_binds r (typ_and (typ_bnd Rr) (typ_mut_marker typ_top)) G ->
  (forall w, tfree_trm w (config_trm c) -> w = z \/ w = r) ->
  config_trm c = trm_write (avar_f x) a (avar_f v) ->
  False.
Proof.
  intros Hmut Htyped Hz Hr Hscope Hwrite.
  pose proof (typed_configuration_write_receiver Hmut Htyped Hwrite) as HX.
  assert (Hiner : @inert mode G) by (inversion Htyped; assumption).
  assert (Hheap : @heap_correspond mode G (config_env c) (config_heap c))
    by (destruct Htyped; simpl; assumption).
  assert (Hfree : tfree_trm x (config_trm c))
    by (rewrite Hwrite; apply tfree_trm_write_l).
  destruct (Hscope _ Hfree) as [-> | ->].
  - exact (@read_only_binding_excludes_write mode G (config_env c)
      (config_heap c) z Rz Hmut Hiner Hheap Hz HX).
  - exact (@read_only_binding_excludes_write mode G (config_env c)
      (config_heap c) r Rr Hmut Hiner Hheap Hr HX).
Qed.

Local Lemma typed_read_view mode G Go e t U :
  @ty_trm mode G Go e t U ->
  forall w a, t = trm_read (avar_f w) a ->
  exists S T V, @ty_var mode G objctx_empty e w (typ_rcd (dec_fld a S T)) /\
    @viewpoint_adapt mode w G objctx_empty e T V /\
    @subtyp mode G objctx_empty e V U.
Proof.
  induction 1; intros w f Heq; try discriminate.
  - inversion Heq; subst. eexists _, _, _. repeat split; try eassumption.
    apply subtyp_refl.
  - destruct (IHty_trm w f Heq) as (S & V & W & Hx & Hv & Hs).
    exists S, V, W. repeat split; try assumption.
    eapply subtyp_trans; eassumption.
Qed.

Local Lemma typed_variable_context_entry mode G e w T :
  @ty_var mode G objctx_empty e w T ->
  exists U, ctx_binds w U G.
Proof. induction 1; eauto. Qed.

Local Lemma heap_location_binding_shape mode G e h y :
  mode_has_mutability mode ->
  @inert mode G ->
  @heap_correspond mode G e h ->
  y \in dom h ->
  exists R G0, ctx_binds_k_after y v_loc
    (typ_and (typ_bnd R) (typ_mut_marker typ_bot)) G G0.
Proof.
  intros Hmut Hiner HH Hy.
  destruct HH as (Hok & Hweak & Hh & He & Hloc & Href & Hcorr & Hitems).
  assert (Hk : y \in ctx_kdom v_loc G) by now rewrite Hloc.
  destruct (ctx_kind_determined_by_domain v_loc Hok Hweak Hk) as (T & G0 & HT).
  pose proof (ctx_binds_k_lookup HT) as Hb.
  destruct (inert_mutable_binding_shape Hmut Hiner Hb) as (R & B & ls & -> & _ & _).
  assert (HH : @heap_correspond mode G e h) by now repeat split.
  destruct (typed_heap_places_refs_and_locations Hmut HH) as [_ Htargets].
  destruct (bound_object_outside_environment Hmut Hiner HH Hb (Htargets y Hy))
    as [_ ->].
  now exists R, G0.
Qed.

Local Lemma prepare_typed_read mode G e h w y ds a loc U (avoid : vars) :
  mode_has_sef mode ->
  mode_has_mutability mode ->
  @inert mode G ->
  @heap_correspond mode G e h ->
  binds w y e ->
  binds y (item_obj ds) h ->
  defs_has ds (def_fld a (avar_f loc)) ->
  @ty_trm mode G objctx_empty e (trm_read (avar_f w) a) U ->
  exists r R B RO T,
    r \notin avoid /\
    record_has (open y RO) (dec_fld a T T) /\
    (let G' := G § r / v_ref ~ typ_and (typ_bnd R) (typ_mut_marker B) in
     let e' := e & r ~ loc in
     @inert mode G' /\
     @heap_correspond mode G' e' h /\
     preserves_ctx_binds G G' /\ env_binds_more e e' /\
     @ty_var mode G' objctx_empty e' r U /\
     (@reference_is_protected mode G e w \/
       (exists w0, @reference_is_protected mode G e w0 /\
         @ty_var mode G objctx_empty e w0 T) ->
       @reference_is_protected mode G' e' r)).
Proof.
  intros Hsef Hmut Hiner Hheap Hw Hy Hfield Htyped.
  destruct (typed_read_view Htyped eq_refl)
    as (Sa & Ta & V & Hview & Hadapt & Hup).
  destruct (@heap_reference_precise_definition mode G e h w y ds
    (def_fld a (avar_f loc)) Hmut Hiner Hheap Hw Hy Hfield)
    as (RO & BO & D & Hobj & _ & Hdef & Hdecl & _).
  inversion Hdef; subst. unfold ctx_obj in *.
  assert (HT : exists T,
    record_has (open y RO) (dec_fld a T T) /\ @ty_var mode G objctx_empty e loc T)
    by (eexists; split; eassumption).
  destruct HT as (Tf & HdeclT & HT).
  destruct (@precise_field_views_sound mode G e h w y RO BO a Tf Tf Sa Ta
    Hmut Hiner Hheap Hw Hobj HdeclT Hview) as [_ Hcov].
  assert (HlocTa : @ty_var mode G objctx_empty e loc Ta)
    by (eapply ty_var_sub; eassumption).
  assert (Hloc : loc \in dom h).
  { pose proof (@typed_heap_items_are_scoped mode G e h Hheap y (item_obj ds) Hy) as Hitems.
    exact (@stored_def_in_scope _ _ _ _ Hitems Hfield). }
  destruct (heap_location_binding_shape Hmut Hiner Hheap Hloc) as (R & G0 & Hlocshape).
  pose proof (ctx_binds_k_lookup Hlocshape) as Hlocbind.
  assert (Hmode : mode_viewpoint_adaptation' mode = mode_viewpoint_adapt_mutability)
    by (destruct mode; discriminate || reflexivity).
  pose proof Hadapt as Hadapt0. unfold viewpoint_adapt in Hadapt0. rewrite Hmode in Hadapt0.
  inversion Hadapt0 as [C x G1 Go e1 T1 S A Hinc Hcap]; subst.
  set (B := typ_or A (typ_sel (avar_f w) typ_label_mutability (avar_b 0))).
  set (Ty := typ_and (typ_bnd R) (typ_mut_marker B)).
  destruct (var_fresh ((((avoid \u ctx_dom G) \u dom e) \u ctx_fv G) \u fv Ty))
    as [r Hfresh].
  apply notin_union in Hfresh as [Hfresh Htype].
  apply notin_union in Hfresh as [Hfresh Hfv].
  apply notin_union in Hfresh as [Hfresh Henv].
  apply notin_union in Hfresh as [Havoid Hctx].
  assert (Hkeep : preserves_ctx_binds G (G § r / v_ref ~ Ty))
    by now apply binds_preserved_by_fresh_push.
  assert (Hmore : env_binds_more e (e & r ~ loc)).
  { intros v l Hb. apply binds_push_neq; [exact Hb |].
    intros ->. apply Henv. exact (get_some_inv Hb). }
  assert (Hresult : @ty_var mode (G § r / v_ref ~ Ty) objctx_empty (e & r ~ loc) r U).
  { destruct (@adapt_read_alias_type mode G e w loc r R Ta _
        Hsef Hmut Hlocbind HlocTa Hadapt Hctx Henv) as (S' & A' & Heq & Halias).
    injection Heq as <- <-.
    eapply ty_var_sub; [exact Halias |].
    eapply (proj1 (proj2 (variable_judgments_extend mode))); eassumption. }
  exists r, R, B, RO, Tf.
  split; [exact Havoid |]. split; [exact HdeclT |]. cbv beta zeta.
  split; [eapply fresh_alias_inert; eassumption |].
  split; [eapply fresh_alias_heap_corresponds; eassumption |].
  split; [exact Hkeep |]. split; [exact Hmore |]. split; [exact Hresult |].
  intros [Hrecv | (w0 & Hw0 & Htyped0)].
  all: exists R, B; split; [constructor |].
  all: eapply protected_upper_weakens; [exact Hkeep | exact Hmore |].
  - destruct Hrecv as (R' & B' & Hbind & Hprotect).
    eapply protected_upper_from_receiver; eassumption.
  - destruct Hw0 as (R' & B' & Hbind & Hprotect).
    eapply protected_upper_through_field; [exact Hmut | exact Hbind | | exact Hcap | exact Hprotect].
    eapply ty_var_sub; eassumption.
Qed.

Local Lemma typed_write_view mode G Go e t U :
  @ty_trm mode G Go e t U ->
  forall w a v, t = trm_write (avar_f w) a (avar_f v) ->
  exists S T,
    @ty_var mode G objctx_empty e w (typ_rcd (dec_fld a S T)) /\
    @ty_var mode G objctx_empty e v S /\
    @subtyp mode G objctx_empty e T U.
Proof.
  induction 1; intros w f v Heq; try discriminate.
  - inversion Heq; subst. eexists _, _. repeat split; try eassumption.
    apply subtyp_refl.
  - destruct (IHty_trm w f v Heq) as (S & T0 & Hx & Hv & Hsub).
    exists S, T0. repeat split; try assumption. eapply subtyp_trans; eassumption.
Qed.

Local Lemma updated_field_was_present ds a loc ds' :
  defs_update ds a loc ds' ->
  exists v, defs_has ds (def_fld a v).
Proof.
  induction 1.
  - exists t. unfold defs_has. simpl. case_if; congruence.
  - destruct IHdefs_update as [v Hv]. exists v.
    unfold defs_has in *. simpl in *. case_if; assumption || congruence.
Qed.

Local Lemma defs_update_preserves_location_kinds G ds a loc ds' :
  defs_update ds a loc ds' ->
  ctx_k G loc v_loc ->
  defs_varkinds G ds ->
  defs_varkinds G ds'.
Proof.
  induction 1; intros Hloc Hkinds; inversion Hkinds; subst;
    apply defs_varkinds_cons; eauto using def_varkinds_fld.
Qed.

Local Lemma kind_binding_visible G G0 x k T :
  ctx_binds_k_after x k T G G0 -> ctx_vis G x.
Proof. induction 1; [constructor | now apply ctx_vis_n]. Qed.

Local Lemma typed_write_updates_heap mode G e h h' w y v loc a U :
  mode_has_sef mode ->
  mode_has_mutability mode ->
  @inert mode G ->
  @heap_correspond mode G e h ->
  binds w y e ->
  binds v loc e ->
  @ty_trm mode G objctx_empty e (trm_write (avar_f w) a (avar_f v)) U ->
  heap_update h y a loc h' ->
  @heap_correspond mode G e h' /\
  @ty_var mode G objctx_empty e v U /\
  forall R B Tf,
    ctx_binds w (typ_and (typ_bnd R) (typ_mut_marker B)) G ->
    record_has (open y R) (dec_fld a Tf Tf) ->
    @ty_var mode G objctx_empty e v Tf.
Proof.
  intros Hsef Hmut Hiner Hheap Hw Hv Htyped Hupdate.
  destruct (typed_write_view Htyped eq_refl) as (Sa & Ta & Hwtype & Hvtype & Hup).
  destruct Hupdate as (_ & Hok' & Hdom & Hkeep & ds & ds' & Hy & Hupd & Hy').
  destruct (updated_field_was_present Hupd) as [av Hfield].
  destruct (@heap_reference_precise_definition mode G e h w y ds
      (def_fld a av) Hmut Hiner Hheap Hw Hy Hfield)
    as (R & B & D & Hobj & _ & Hdef & HD & _).
  inversion Hdef; subst.
  assert (Hresult : exists Tf,
    record_has (open y R) (dec_fld a Tf Tf) /\
    @subtyp mode G objctx_empty e Sa Tf /\
    @subtyp mode G objctx_empty e Tf Ta).
  { eexists. split; [exact HD |].
    eapply precise_field_views_sound; [exact Hmut | exact Hiner | exact Hheap
      | exact Hw | exact Hobj | exact HD | exact Hwtype]. }
  destruct Hresult as (Tf & Hdecl & Hcontra & Hcov).
  assert (HvTf : @ty_var mode G objctx_empty e v Tf) by (eapply ty_var_sub; eassumption).
  pose proof (exact_member_from_heap_reference Hmut Hheap Hw Hobj Hdecl) as Hdecl0.
  assert (HvEach : forall Tf',
      record_has (open y R) (dec_fld a Tf' Tf') ->
      @ty_var mode G objctx_empty e v Tf').
  { intros Tf' HD'.
    pose proof (exact_member_from_heap_reference Hmut Hheap Hw Hobj HD') as Hdecl'.
    pose proof (exact_object_members_unique Hiner Hdecl0 Hdecl' eq_refl) as Heq.
    injection Heq as <- _. exact HvTf. }
  destruct Hheap as (Hok & Hweak & Hheapok & Henvok & Hlocdom & Hrefdom & Hcorr & Hitems).
  assert (Hheap : @heap_correspond mode G e h) by now repeat split.
  destruct (reference_location_have_same_record Hmut Hok Hcorr Hw)
    as (R' & B' & Hwbase & Hybase).
  pose proof (ctx_binding_unique Hobj Hwbase) as Hsame.
  injection Hsame as <- _.
  destruct (heap_object_exact_typing Hheap Hy Hybase) as [Hds Hkinds].
  assert (Hloc : ctx_k G loc v_loc).
  { destruct (reference_location_kind Hmut Hok Hcorr Hv)
      as (Rl & Bl & P & _ & Hloc). unfold ctx_k; exists (typ_and (typ_bnd Rl) (typ_mut_marker typ_bot)), P; exact Hloc. }
  assert (Hds' : @ty_defs mode G (objctx_heap y R) e ds' (open y R)).
  { eapply typed_update_keeps_declarations; [exact Hupd | exact Hds | |].
    - intros _. destruct Hloc as (W & P & Hloc).
      now apply kind_binding_visible in Hloc.
    - intros Tf' Hd. eapply location_has_reference_type; [exact Hsef | exact Hmut
        | exact Hheap | exact Hv | now apply HvEach]. }
  split.
  - repeat split; try assumption.
    + congruence.
    + intros l Hl. rewrite <- Hdom in Hl.
      destruct (classic (l = y)) as [->|Hneq].
      * eapply ty_item_obj_s with (U := R) (S := typ_mut_marker typ_bot); [exact Hybase | exact Hy' | reflexivity | exact Hds' |].
        eapply defs_update_preserves_location_kinds; eassumption.
      * specialize (Hitems l Hl). destruct Hitems.
        -- eapply ty_item_fun_s; eauto.
        -- eapply ty_item_obj_s; eauto.
  - split.
    + eapply ty_var_sub; [exact HvTf | eapply subtyp_trans; eassumption].
    + intros R0 B0 T0 Hb Hf. pose proof (ctx_binding_unique Hb Hobj) as Heq.
      injection Heq as -> _. now apply HvEach.
Qed.

Local Lemma first_two_call_steps_preserve_heap mode w1 m w2 Zv c G d k U :
  mode_has_sef mode ->
  mode_has_mutability mode ->
  config_trm c = trm_call (avar_f w1) m (avar_f w2) ->
  @ty_var mode G objctx_empty (config_env c) w1
    (typ_rcd (dec_met m typ_nocap Zv typ_top)) ->
  @ty_var mode G objctx_empty (config_env c) w2 Zv ->
  @subtyp mode G objctx_empty (config_env c) typ_nocap Zv ->
  @ty_config mode G c U ->
  c ⊣k↦* d ->
  k <= 2 ->
  (exists j d0, frame_end_in c j d0 /\ j < k) \/
  subheap_unchanged (config_heap c) (config_heap d).
Proof.
  intros Hsef Hmut Hcall Hrecv Harg Hnocap Htyped Hrun Hsmall.
  destruct (classic (exists j d0, frame_end_in c j d0 /\ j < k)) as [Hend | Hnoend].
  - now left.
  - right.
    destruct (classic (subheap_unchanged (config_heap c) (config_heap d)))
      as [Hsame | Hchanged]; [exact Hsame |].
    exfalso.
    assert (Hbefore : forall j d0, j < k -> ~ frame_end_in c j d0).
    { intros j d0 Hj Hend. apply Hnoend. exists j, d0. auto. }
    destruct (typed_call_write_replays_through_aliases Hsef Hmut
      (@precise_method_views_sound mode Hmut) Htyped Hcall Hrecv Harg Hnocap Hrun Hbefore Hchanged)
      as (G' & ca & z & r & R1 & R2 & n & da & xa & a & va & y & it &
          Hbound & HtypedA & _ & Hctxz & Hctxr & Hscope & HredA & Hwrite & _ & _).
    assert (n = 0) by lia. subst n.
    inversion HredA; subst.
    exact (@initial_readonly_stack_excludes_old_write
      mode G' da typ_top z r R2 R1 xa a va Hmut HtypedA Hctxz Hctxr Hscope Hwrite).
Qed.

Local Lemma stack_typing_narrows mode G e S st T :
  @ty_stack mode G e S st T ->
  forall G' e', @context_narrows mode e' G G' ->
    env_binds_more e e' ->
    @ty_stack mode G' e' S st T.
Proof.
  induction 1 as [G e S T Hsub | L G e st body S U T Hst IH Hbody].
  - intros G' e' Hctx Henv. apply ty_stack_nil. eapply subtype_narrows; eassumption.
  - intros G' e' Hctx Henv. eapply ty_stack_let with (L := L \u ctx_dom G').
    + now apply IH.
    + intros x Hfresh. apply notin_union in Hfresh as [HxL HxG].
      eapply (proj1 (term_judgments_narrow mode)); [exact (Hbody x HxL) | | exact I | exact Henv].
      now apply context_narrows_push.
Qed.

Local Lemma stack_typing_accepts_subtype mode G e S T st U :
  @ty_stack mode G e T st U ->
  @subtyp mode G objctx_empty e S T ->
  @ty_stack mode G e S st U.
Proof.
  intros Hstack Hsub.
  destruct Hstack as [G e T U Hnil | L G e st t T V U Htail Hframe].
  - apply ty_stack_nil. eapply subtyp_trans; eassumption.
  - eapply ty_stack_let with (L := L \u ctx_dom G); [exact Htail |].
    intros x Hfresh. apply notin_union in Hfresh as [HxL HxG].
    eapply (proj1 (term_judgments_narrow mode)); [exact (Hframe x HxL) | | exact I | auto].
    split.
    + apply include_context_types_narrow_top; [exact HxG | | exact Hsub].
      intros y B Hy. now apply ty_var_var.
    + intros y Hy. inversion Hy; subst; [constructor |].
      apply ctx_vis_n; assumption.
Qed.

Local Lemma typed_let_push mode G e st s t U T :
  @ty_trm mode G objctx_empty e (trm_let s t) T ->
  @ty_stack mode G e T st U ->
  exists S,
    @ty_trm mode G objctx_empty e s S /\
    @ty_stack mode G e S (stack_cons (frame_let t) st) U.
Proof.
  intros Hlet.
  remember (trm_let s t) as whole eqn:Heq in Hlet.
  induction Hlet; inversion Heq; subst; try clear Heq; intro Hstack.
  - exists T. split; [assumption |]. eapply ty_stack_let; eassumption.
  - apply IHHlet; [reflexivity |].
    eapply stack_typing_accepts_subtype; eassumption.
Qed.

Local Definition new_object_fields_are_protected mode G e h (old : vars) :=
  forall w y ds a loc R B T,
    binds w y e ->
    y \notin old ->
    binds y (item_obj ds) h ->
    defs_has ds (def_fld a (avar_f loc)) ->
    loc \in old ->
    ctx_binds w (typ_and (typ_bnd R) (typ_mut_marker B)) G ->
    record_has (open y R) (dec_fld a T T) ->
    exists v, binds v loc e /\ @reference_is_protected mode G e v /\
      @ty_var mode G objctx_empty e v T.

Local Lemma field_update_lookup_new_value ds ds' a y :
  defs_update ds a y ds' ->
  get_def (label_fld a) ds' = Some (def_fld a (avar_f y)).
Proof. induction 1; simpl; case_if; assumption || congruence. Qed.

Local Lemma field_update_lookup_other ds ds' a y l :
  defs_update ds a y ds' ->
  l <> label_fld a ->
  get_def l ds' = get_def l ds.
Proof. induction 1; intro Hneq; simpl; case_if; auto; congruence. Qed.

Local Lemma write_preserves_protected_fields mode G e h h' w y v loc a U old :
  mode_has_sef mode ->
  mode_has_mutability mode ->
  @inert mode G ->
  @heap_correspond mode G e h ->
  binds w y e ->
  binds v loc e ->
  @ty_trm mode G objctx_empty e (trm_write (avar_f w) a (avar_f v)) U ->
  heap_update h y a loc h' ->
  (loc \in old -> @reference_is_protected mode G e v) ->
  @new_object_fields_are_protected mode G e h old ->
  @new_object_fields_are_protected mode G e h' old.
Proof.
  intros Hsef Hmut Hiner HH Hw Hv Htyped Hupdate Hsafe Hfields.
  pose proof (typed_write_updates_heap Hsef Hmut Hiner HH Hw Hv Htyped Hupdate)
    as (_ & _ & Hwrite).
  destruct Hupdate as (_ & _ & Hdom & Hkeep & ds & ds' & Hy & Hupd & Hy').
  intros w' y' item a' l R B T Hw' Hnew Hobj Hfield Hold Hctx HT.
  destruct (classic (y' = y)) as [-> | Hneq].
  - pose proof (binds_functional Hobj Hy') as Hsame.
    injection Hsame as ->.
    destruct (classic (a' = a)) as [-> | Hneq].
    + unfold defs_has in Hfield. simpl in Hfield.
      rewrite (field_update_lookup_new_value Hupd) in Hfield.
      injection Hfield as <-.
      exists v. split; [exact Hv |]. split; [now apply Hsafe |].
      destruct HH as (Hok & _ & _ & _ & _ & _ & Hcorr & _).
      destruct (reference_location_have_same_record Hmut Hok Hcorr Hw)
        as (R0 & B0 & Hctxw & Hy0).
      destruct (reference_location_have_same_record Hmut Hok Hcorr Hw')
        as (R1 & B1 & Hctxw' & Hy1).
      pose proof (ctx_binding_unique Hy0 Hy1) as Hsame.
      injection Hsame as <-.
      pose proof (ctx_binding_unique Hctx Hctxw') as Hsame.
      injection Hsame as -> _.
      eapply Hwrite; eassumption.
    + apply (Hfields w' y ds a' l R B T); try assumption.
      unfold defs_has in *. simpl in *. rewrite <- (field_update_lookup_other Hupd).
      * exact Hfield.
      * congruence.
  - assert (Hmem : y' \in dom h) by (rewrite Hdom; exact (get_some_inv Hobj)).
    destruct (get_some Hmem) as [source Hsource].
    rewrite (binds_functional (Hkeep _ _ Hneq Hsource) Hobj) in Hsource.
    eapply Hfields; eassumption.
Qed.

Local Lemma rename_avar_agree f g a :
  (forall x, x \in fv a -> f x = g x) ->
  rename_avar f a = rename_avar g a.
Proof.
  destruct a; [reflexivity |].
  intro H. simpl. f_equal. apply H, in_singleton_self.
Qed.

Local Ltac restrict_renaming_agreement :=
  intros x Hx;
  match goal with
  | H : forall x, x \in _ -> _ = _ |- _ =>
    apply H; cbn [fv TypFreeVar DecFreeVar TrmFreeVar LitFreeVar DefFreeVar DefsFreeVar
      fv_typ fv_dec fv_trm fv_lit fv_def fv_defs];
    repeat rewrite in_union; tauto
  end.

Local Lemma rename_types_agree f g :
  (forall T, (forall x, x \in fv T -> f x = g x) -> rename_typ f T = rename_typ g T) /\
  (forall D, (forall x, x \in fv D -> f x = g x) -> rename_dec f D = rename_dec g D).
Proof.
  apply typ_mutind; intros; simpl; try reflexivity;
    f_equal; first
      [ solve [apply H; restrict_renaming_agreement]
      | solve [apply H0; restrict_renaming_agreement]
      | solve [apply H1; restrict_renaming_agreement]
      | solve [apply rename_avar_agree; restrict_renaming_agreement]].
Qed.

Local Lemma rename_terms_agree f g :
  (forall t, (forall x, x \in fv t -> f x = g x) -> rename_trm f t = rename_trm g t) /\
  (forall l, (forall x, x \in fv l -> f x = g x) -> rename_lit f l = rename_lit g l) /\
  (forall d, (forall x, x \in fv d -> f x = g x) -> rename_def f d = rename_def g d) /\
  (forall ds, (forall x, x \in fv ds -> f x = g x) -> rename_defs f ds = rename_defs g ds).
Proof.
  apply trm_mutind; intros; simpl; try reflexivity;
    f_equal; first
      [ solve [apply H; restrict_renaming_agreement]
      | solve [apply H0; restrict_renaming_agreement]
      | solve [apply (proj1 (rename_types_agree f g)); restrict_renaming_agreement]
      | solve [apply rename_avar_agree; restrict_renaming_agreement]].
Qed.

Local Definition rename_override (rename : var -> var) (x y v : var) :=
  If v = x then y else rename v.

Local Lemma rename_override_here rename x y :
  rename_override rename x y x = y.
Proof. unfold rename_override. case_if; congruence. Qed.

Local Lemma rename_override_elsewhere rename x y v :
  v <> x -> rename_override rename x y v = rename v.
Proof. intro H. unfold rename_override. case_if; congruence. Qed.

Local Lemma rename_type_override_open rename x y k T :
  x \notin fv T ->
  rename_typ (rename_override rename x y) (open_rec k x T) =
  open_rec k y (rename_typ rename T).
Proof.
  intro Hx.
  rewrite (proj1 (rename_typ_open _)), rename_override_here.
  f_equal. apply (proj1 (rename_types_agree _ _)).
  intros v Hv. apply rename_override_elsewhere. intros ->. contradiction.
Qed.

Local Lemma rename_term_override_open rename x y k t :
  x \notin fv t ->
  rename_trm (rename_override rename x y) (open_rec k x t) =
  open_rec k y (rename_trm rename t).
Proof.
  intro Hx.
  rewrite (proj1 (rename_trm_open _)), rename_override_here.
  f_equal. apply (proj1 (rename_terms_agree _ _)).
  intros v Hv. apply rename_override_elsewhere. intros ->. contradiction.
Qed.

Local Definition renaming_respects_env (rename : var -> var) e e' :=
  forall x y, binds x y e -> @tyq_var e' (rename x) (rename y).

Local Lemma renaming_respects_env_override rename e e' x y :
  x \notin fv_renv e ->
  renaming_respects_env rename e e' ->
  renaming_respects_env (rename_override rename x y) e e'.
Proof.
  intros Hx Henv w l Hb.
  assert (Hw : w <> x).
  { intro Heq. subst x. apply Hx. rewrite in_union. left. exact (get_some_inv Hb). }
  assert (Hl : l <> x).
  { intro Heq. subst x. apply Hx. rewrite in_union. right.
    eapply (@fv_of_binding_is_env_fv var fv e l w l);
      [exact Hb | apply in_singleton_self]. }
  rewrite !rename_override_elsewhere by assumption. now apply Henv.
Qed.

Local Lemma renaming_variable_equivalence rename e e' x y :
  renaming_respects_env rename e e' ->
  @tyq_var e x y ->
  @tyq_var e' (rename x) (rename y).
Proof.
  intros Henv Heq.
  induction Heq as [e x | e x y Hb | e x y Hxy IH | e x y z Hxy IH1 Hyz IH2].
  - apply tyq_var_refl.
  - exact (Henv _ _ Hb).
  - apply tyq_var_sym. exact (IH Henv).
  - exact (@tyq_var_trans e' _ _ _ (IH1 Henv) (IH2 Henv)).
Qed.

Local Lemma fresh_override_for_two_types rename e e' (S T : typ) y :
  renaming_respects_env rename e e' ->
  exists x, x \notin fv S /\ x \notin fv T /\
    renaming_respects_env (rename_override rename x y) e e'.
Proof.
  intro Henv. destruct (var_fresh ((fv S \u fv T) \u fv_renv e)) as [x Hx].
  apply notin_union in Hx as [Hx He]. apply notin_union in Hx as [HS HT].
  exists x. split; [exact HS |]. split; [exact HT |].
  now apply renaming_respects_env_override.
Qed.

Local Lemma renaming_type_equivalence e S T :
  @tyq_typ e S T ->
  forall rename e', renaming_respects_env rename e e' ->
    @tyq_typ e' (rename_typ rename S) (rename_typ rename T).
Proof.
  intro Hq. induction Hq as
    [e T Hnul | F e S1 T1 S2 T2 Hando H1 IH1 H2 IH2
    | e S1 T1 S2 T2 H1 IH1 H2 IH2 | e a S1 T1 S2 T2 H1 IH1 H2 IH2
    | e A S1 T1 S2 T2 H1 IH1 H2 IH2 | e x y w A Hxy
    | e x y A | e S T H1 IH1
    | m e C1 Z1 R1 C2 Z2 R2 Hc IHc Hz IHz Hr IHr];
    intros rename e' Henv; simpl.
  - inversion Hnul; constructor; constructor.
  - destruct Hando; simpl.
    + apply (@tyq_typ_andor typ_and e' _ _ _ _); [constructor | now apply IH1 | now apply IH2].
    + apply (@tyq_typ_andor typ_or e' _ _ _ _); [constructor | now apply IH1 | now apply IH2].
  - apply tyq_typ_fun; [now apply IH1 |].
    intro y. destruct (@fresh_override_for_two_types rename e e' T1 T2 y Henv)
      as (x & Hx1 & Hx2 & HE).
    specialize (IH2 x _ e' HE).
    now rewrite !rename_type_override_open in IH2.
  - apply tyq_typ_fld; [now apply IH1 | now apply IH2].
  - apply tyq_typ_typ; intro y.
    + destruct (@fresh_override_for_two_types rename e e' S1 S2 y Henv)
        as (x & Hx1 & Hx2 & HE).
      specialize (IH1 x _ e' HE). now rewrite !rename_type_override_open in IH1.
    + destruct (@fresh_override_for_two_types rename e e' T1 T2 y Henv)
        as (x & Hx1 & Hx2 & HE).
      specialize (IH2 x _ e' HE). now rewrite !rename_type_override_open in IH2.
  - apply tyq_typ_sel_normal. eapply renaming_variable_equivalence; eassumption.
  - apply tyq_typ_sel.
  - apply tyq_typ_bnd. intro y.
    destruct (@fresh_override_for_two_types rename e e' S T y Henv)
      as (x & Hx1 & Hx2 & HE).
    specialize (IH1 x _ e' HE). now rewrite !rename_type_override_open in IH1.
  - apply tyq_typ_met.
    + intro y. destruct (@fresh_override_for_two_types rename e e' C1 C2 y Henv)
        as (x & Hx1 & Hx2 & HE).
      specialize (IHc x _ e' HE). now rewrite !rename_type_override_open in IHc.
    + now apply IHz.
    + intros z r.
      destruct (@fresh_override_for_two_types rename e e' R1 R2 r Henv)
        as (r0 & Hr1 & Hr2 & Henv0).
      destruct (@fresh_override_for_two_types (rename_override rename r0 r) e e'
          (open_rec 1 r0 R1) (open_rec 1 r0 R2) z Henv0)
        as (z0 & Hz1 & Hz2 & Henv1).
      specialize (IHr z0 r0 _ e' Henv1).
      rewrite (rename_type_override_open _ _ _ _ Hz1),
        (rename_type_override_open _ _ _ _ Hz2) in IHr.
      now rewrite !rename_type_override_open in IHr.
Qed.

Local Lemma rename_avar_preserves_bound_test rename a n :
  rename_avar rename a <> avar_b n <-> a <> avar_b n.
Proof. destruct a; simpl; intuition discriminate. Qed.

Local Lemma rename_bound_independence rename :
  (forall T n, independent_of (avar_b n) (rename_typ rename T) <->
    independent_of (avar_b n) T) /\
  (forall D n, independent_of_dec (avar_b n) (rename_dec rename D) <->
    independent_of_dec (avar_b n) D).
Proof.
  apply typ_mutind; intros; simpl; try solve [firstorder].
  destruct t; repeat rewrite rename_avar_preserves_bound_test; reflexivity.
Qed.

Local Lemma rename_independent_binder rename T n :
  typ_indep_b n (rename_typ rename T) <-> typ_indep_b n T.
Proof.
  now rewrite <- !(proj1 independent_of_spec), (proj1 (rename_bound_independence rename)).
Qed.

Local Definition renaming_fixes_outside (rename : var -> var) (avoid : vars) :=
  forall x, x \notin avoid -> name_fixed_by rename x.

Local Lemma renaming_fixes_outside_override rename L x y :
  renaming_fixes_outside rename L ->
  renaming_fixes_outside (rename_override rename x y) ((L \u \{x}) \u \{y}).
Proof.
  intros Hfix z Hz.
  repeat rewrite notin_union in Hz. destruct Hz as [[HzL Hzx] Hzy].
  apply notin_singleton in Hzx, Hzy.
  intros v. unfold rename_override. case_if.
  - subst v. intuition congruence.
  - now apply Hfix.
Qed.

Local Definition renaming_respects_types mode (rename : var -> var) G H e :=
  forall x T, ctx_binds x T G ->
    @ty_var mode H objctx_empty e (rename x) (rename_typ rename T).

Local Lemma renaming_respects_types_push mode rename G H e x k T :
  name_fixed_by rename x ->
  x §# H ->
  @renaming_respects_types mode rename G H e ->
  @renaming_respects_types mode rename (G § x / k ~ T)
    (H § x / k ~ rename_typ rename T) e.
Proof.
  intros Hfix Hfresh Htype y U Hb. inversion Hb; subst.
  - rewrite (name_fixed_by_eq Hfix). apply ty_var_var. constructor.
  - eapply (proj1 (variable_judgments_extend mode)).
    + now apply Htype.
    + now apply binds_preserved_by_fresh_push.
    + auto.
Qed.

Local Lemma renaming_respects_types_hide mode rename G H e :
  @renaming_respects_types mode rename G H e ->
  @renaming_respects_types mode rename (ctx_hide G) (ctx_hide H) e.
Proof.
  intros Htype x T Hb. inversion Hb; subst.
  eapply (proj1 (variable_judgments_extend mode)).
  - now apply Htype.
  - intros y U Hu. now apply ctx_binds_hide.
  - auto.
Qed.

Local Lemma renaming_respects_types_override mode rename G H e x y :
  x §# G ->
  x \notin ctx_fv G ->
  @renaming_respects_types mode rename G H e ->
  @renaming_respects_types mode (rename_override rename x y) G H e.
Proof.
  intros Hdom Hfv Htype v T Hb.
  rewrite rename_override_elsewhere by (intros ->; apply Hdom; exact (ctx_binding_in_dom Hb)).
  rewrite (proj1 (rename_types_agree (rename_override rename x y) rename)).
  - now apply Htype.
  - intros z Hz. apply rename_override_elsewhere. intro Heq. subst z.
    apply Hfv. exact (ctx_binding_free_variables Hb Hz).
Qed.

Local Lemma subtype_member_bound_renaming mode G e S T :
  (forall x rename L H e',
    renaming_fixes_outside rename L ->
    renaming_respects_env rename e e' ->
    @renaming_respects_types mode rename G H e' ->
    @subtyp mode H objctx_empty e' (rename_typ rename (open x S)) (rename_typ rename (open x T))) ->
  forall rename L H e' y,
    renaming_fixes_outside rename L ->
    renaming_respects_env rename e e' ->
    @renaming_respects_types mode rename G H e' ->
    @subtyp mode H objctx_empty e' (open y (rename_typ rename S)) (open y (rename_typ rename T)).
Proof.
  intros IH rename L H e' y Hfix Henv Htypes.
  destruct (var_fresh (((((fv S \u fv T) \u ctx_dom G) \u ctx_fv G) \u dom e) \u fv_env e))
    as [x Hfresh].
  apply notin_union in Hfresh as [Hfresh Hvalues].
  apply notin_union in Hfresh as [Hfresh Hkeys].
  apply notin_union in Hfresh as [Hfresh Hfv].
  apply notin_union in Hfresh as [Hfresh Hdom].
  apply notin_union in Hfresh as [HS HT].
  assert (Henv0 : renaming_respects_env (rename_override rename x y) e e').
  { apply renaming_respects_env_override; [now apply notin_union | exact Henv]. }
  pose proof (IH x (rename_override rename x y) ((L \u \{x}) \u \{y}) H e'
    (@renaming_fixes_outside_override rename L x y Hfix) Henv0
    (@renaming_respects_types_override mode rename G H e' x y Hdom Hfv Htypes)) as Hout.
  now rewrite !rename_type_override_open in Hout.
Qed.

Local Ltac use_renaming :=
  unfold obj_typing, subtyping, obj_ref_incap, typing_equiv, renaming_respects_types in *;
  eauto 6 using renaming_type_equivalence.

Local Lemma variable_judgments_rename mode :
  mode_has_mutability mode ->
  (forall G Go e x T, @ty_var mode G Go e x T ->
    forall rename L H e',
      renaming_fixes_outside rename L ->
      renaming_respects_env rename e e' ->
      @renaming_respects_types mode rename G H e' ->
      @ty_var mode H objctx_empty e' (rename x) (rename_typ rename T)) /\
  (forall G Go e S T, @subtyp mode G Go e S T ->
    forall rename L H e',
      renaming_fixes_outside rename L ->
      renaming_respects_env rename e e' ->
      @renaming_respects_types mode rename G H e' ->
      @subtyp mode H objctx_empty e' (rename_typ rename S) (rename_typ rename T)) /\
  (forall G Go e S T, @ty_incap mode G Go e S T ->
    forall rename L H e',
      renaming_fixes_outside rename L ->
      renaming_respects_env rename e e' ->
      @renaming_respects_types mode rename G H e' ->
      @ty_incap mode H objctx_empty e' (rename_typ rename S) (rename_typ rename T)).
Proof.
  intro Hmutable.
  apply ts_mutind; intros; cbn [rename_typ rename_dec rename_avar];
    try solve [use_renaming | constructor; use_renaming].
  all: try solve [
    first [solve [eapply ty_var_sub; use_renaming] | solve [eapply subtyp_trans; use_renaming]
      | solve [eapply subtyp_tyq; use_renaming] | solve [eapply ty_incap_nocap; use_renaming]]].
  - eapply ty_rec_intro.
    + rewrite <- (proj1 (rename_typ_open _)). use_renaming.
    + now apply rename_independent_binder.
    + intro Hmode. rewrite <- (proj1 (rename_typ_open _)). use_renaming.
  - rewrite (proj1 (rename_typ_open _)).
    eapply ty_rec_elim; [use_renaming | now apply rename_independent_binder].
  - eapply ty_var_mut_top with (T := rename_typ rename T); [exact Hmutable | use_renaming].
  - apply subtyp_typ; intro y.
    + exact (@subtype_member_bound_renaming mode G e S2 S1 H rename L H1 e' y H2 H3 H4).
    + exact (@subtype_member_bound_renaming mode G e T1 T2 H0 rename L H1 e' y H2 H3 H4).
  - rewrite (proj1 (rename_typ_open _)).
    eapply subtyp_sel2 with (T := rename_typ rename T). use_renaming.
  - rewrite (proj1 (rename_typ_open _)).
    eapply subtyp_sel1 with (S := rename_typ rename S). use_renaming.
  - destruct mode; discriminate.
  - eapply subtyp_met with (L := (L \u L0) \u ctx_dom H2); [use_renaming | | |].
    + intros z Hz. apply notin_union in Hz as [Hz HzG].
      apply notin_union in Hz as [HzL HzR].
      assert (Hfixed : name_fixed_by rename z) by eauto.
      assert (HT : @renaming_respects_types mode rename (G § z / v_par ~ TZ2)
          (H2 § z / v_par ~ rename_typ rename TZ2) e')
        by now apply renaming_respects_types_push.
      pose proof (H0 z HzL rename L0 (H2 § z / v_par ~ rename_typ rename TZ2) e'
        ltac:(assumption) ltac:(assumption) HT) as HR.
      rewrite !(proj1 (rename_typ_open _)), (name_fixed_by_eq Hfixed) in HR. exact HR.
    + intros Hsef Hindeps. apply rename_independent_binder.
      apply t; [exact Hsef | now apply rename_independent_binder in Hindeps].
    + intros z Hz r Hneq Hr.
      apply notin_union in Hz as [Hz HzG]. apply notin_union in Hz as [HzL HzR].
      apply notin_union in Hr as [Hr HrG]. apply notin_union in Hr as [HrL HrR].
      assert (Hfz : name_fixed_by rename z) by eauto.
      assert (Hfr : name_fixed_by rename r) by eauto.
      assert (HT : @renaming_respects_types mode rename (ctx_met G z TZ2 r TC2)
          (ctx_met H2 z (rename_typ rename TZ2) r (rename_typ rename TC2)) e').
      { assert (Heq : open z (rename_typ rename TC2) = rename_typ rename (open z TC2)).
        { rewrite (proj1 (rename_typ_open _)), (name_fixed_by_eq Hfz). reflexivity. }
        rewrite Heq. apply renaming_respects_types_push; [exact Hfr | |].
        - simpl. apply notin_union. split; [now apply notin_singleton | exact HrG].
        - now apply renaming_respects_types_push. }
      pose proof (H1 z HzL r Hneq HrL rename L0
        (ctx_met H2 z (rename_typ rename TZ2) r (rename_typ rename TC2)) e'
        ltac:(assumption) ltac:(assumption) HT) as HR.
      rewrite !(proj1 (rename_typ_open _)), (name_fixed_by_eq Hfz), (name_fixed_by_eq Hfr) in HR.
      exact HR.
  - eapply ty_incap_sel with (S := rename_typ rename S) (T := rename_typ rename T).
    + exact (H rename L H1 e' H2 H3 H4).
    + rewrite <- (proj1 (rename_typ_open _)).
      exact (H0 rename L H1 e' H2 H3 H4).
Qed.

Local Definition renaming_respects_context mode rename G H e :=
  @renaming_respects_types mode rename G H e /\
  forall x, ctx_vis G x -> ctx_vis H (rename x).

Local Lemma renaming_respects_context_push mode rename G H e x k T U :
  name_fixed_by rename x ->
  x §# H ->
  U = rename_typ rename T ->
  @renaming_respects_context mode rename G H e ->
  @renaming_respects_context mode rename (G § x / k ~ T) (H § x / k ~ U) e.
Proof.
  intros Hfix Hfresh -> [HT HV]. split.
  - now apply renaming_respects_types_push.
  - intros v Hvis. inversion Hvis; subst.
    + rewrite (name_fixed_by_eq Hfix). constructor.
    + apply ctx_vis_n; [|now apply HV].
      intro Hbad. apply (proj1 (Hfix v)) in Hbad. congruence.
Qed.

Local Lemma renaming_respects_context_hide mode rename G H e :
  @renaming_respects_context mode rename G H e ->
  @renaming_respects_context mode rename (ctx_hide G) (ctx_hide H) e.
Proof.
  intros [HT HV]. split.
  - now apply renaming_respects_types_hide.
  - intros x HVx. inversion HVx.
Qed.

Local Lemma renaming_respects_context_push_mapped mode rename G H e x k T :
  (forall v, rename v = rename x -> v = x) ->
  rename x §# H ->
  @renaming_respects_context mode rename G H e ->
  @renaming_respects_context mode rename (G § x / k ~ T)
    (H § rename x / k ~ rename_typ rename T) e.
Proof.
  intros Hunique Hfresh [HT HV]. split.
  - intros v U Hlookup. inversion Hlookup; subst.
    + apply ty_var_var. constructor.
    + eapply (proj1 (variable_judgments_extend mode)).
      * now apply HT.
      * now apply binds_preserved_by_fresh_push.
      * auto.
  - intros v Hv. inversion Hv; subst; [constructor |].
    apply ctx_vis_n; [|now apply HV].
    intro Heq. apply Hunique in Heq. contradiction.
Qed.

Local Definition rename_object_context rename Go :=
  match Go with
  | objctx_empty => objctx_empty
  | objctx_lit x T => objctx_lit (rename x) (rename_typ rename T)
  | objctx_heap y T => objctx_heap (rename y) (rename_typ rename T)
  end.

Local Definition object_context_can_be_renamed rename H Go :=
  match Go with
  | objctx_lit x T => (forall v, rename v = rename x -> v = x) /\ rename x §# H
  | _ => True
  end.

Local Lemma renaming_respects_object_context mode rename G H e Go :
  object_context_can_be_renamed rename H Go ->
  @renaming_respects_context mode rename G H e ->
  @renaming_respects_context mode rename (G §§& Go) (H §§& rename_object_context rename Go) e.
Proof.
  destruct Go as [|x T|y T]; cbn; auto.
  intros [Hx Hfresh] Hctx.
  rewrite <- (proj1 (rename_typ_open _)).
  now apply renaming_respects_context_push_mapped.
Qed.

Local Lemma renaming_respects_method_context mode rename G H e Go z r Z C :
  mode_has_mutability mode ->
  @renaming_respects_context mode rename G H e ->
  object_context_can_be_renamed rename H Go ->
  name_fixed_by rename z ->
  name_fixed_by rename r ->
  z §# (H §§& rename_object_context rename Go) ->
  r §# (H §§& rename_object_context rename Go) ->
  r <> z ->
  @renaming_respects_context mode rename
    (ctx_obj_met mode G Go z Z r C)
    (ctx_obj_met mode H (rename_object_context rename Go) z (rename_typ rename Z)
      r (rename_typ rename C)) e.
Proof.
  intros Hmutable HT HGo Hz Hr HzG HrG Hne.
  assert (Hmode : mode_has_visibility mode)
    by now apply mode_has_hidden_method_bodies.
  pose proof (@renaming_respects_object_context mode rename G H e Go HGo HT) as Hbase.
  assert (HrG' : r §# (H §§& rename_object_context rename Go § z / v_par ~ rename_typ rename Z)).
  { simpl. apply notin_union. split; [now apply notin_singleton | exact HrG]. }
  assert (HC : open z (rename_typ rename C) = rename_typ rename (open z C)).
  { now rewrite (proj1 (rename_typ_open _)), (name_fixed_by_eq Hz). }
  destruct Go as [|x A|y A]; unfold ctx_obj_met; rewrite Hmode; simpl in *.
  all: apply renaming_respects_context_push; [exact Hr | exact HrG' | |].
  all: try solve [exact HC | simpl; rewrite HC, !(proj1 (rename_typ_open _)),
       ?(name_fixed_by_eq Hr); reflexivity].
  all: apply renaming_respects_context_push; [exact Hz | exact HzG | reflexivity |].
  all: now apply renaming_respects_context_hide.
Qed.

Local Lemma cap_bound_renames mode C G Go e T B :
  mode_has_mutability mode ->
  @ty_capbnd mode C G Go e T B ->
  forall rename L H e',
    renaming_fixes_outside rename L ->
    renaming_respects_env rename e e' ->
    @renaming_respects_types mode rename G H e' ->
    @ty_capbnd mode C H objctx_empty e' (rename_typ rename T) (rename_typ rename B).
Proof.
  intros Hmutable Hb. induction Hb; intros; simpl;
    try solve [constructor; auto].
  - eapply ty_capbnd_sel with (S := rename_typ rename S) (T := rename_typ rename T).
    + exact (proj1 (@variable_judgments_rename mode Hmutable)
        G objctx_empty e x _ H rename L H1 e' H2 H3 H4).
    + rewrite <- (proj1 (rename_typ_open _)).
      exact (IHHb rename L H1 e' H2 H3 H4).
  - apply ty_capbnd_and;
    match goal with IH : forall _ : var -> var, _ |- _ =>
      exact (IH rename L H1 e' H2 H3 H4)
    end.
  - apply ty_capbnd_or;
    match goal with IH : forall _ : var -> var, _ |- _ =>
      exact (IH rename L H1 e' H2 H3 H4)
    end.
Qed.

Local Lemma viewpoint_renames mode G e x T U :
  mode_has_mutability mode ->
  @viewpoint_adapt mode x G objctx_empty e T U ->
  forall rename L H e',
    renaming_fixes_outside rename L ->
    renaming_respects_env rename e e' ->
    @renaming_respects_types mode rename G H e' ->
    @viewpoint_adapt mode (rename x) H objctx_empty e'
      (rename_typ rename T) (rename_typ rename U).
Proof.
  intros Hmutable. unfold viewpoint_adapt.
  destruct (mode_viewpoint_adaptation' mode); [intros ->; reflexivity |].
  inversion 1; subst. intros. simpl.
  apply viewpoint_adapt_cap_strip_combine.
  - eapply (proj2 (proj2 (@variable_judgments_rename mode Hmutable))); eassumption.
  - eapply cap_bound_renames; eassumption.
Qed.

Local Lemma rename_vis_var mode G H e rename x :
  @renaming_respects_context mode rename G H e ->
  vis_var mode G x ->
  vis_var mode H (rename x).
Proof. intros [_ Hvis] Hx Hmode. auto. Qed.

Local Lemma term_judgments_rename mode :
  mode_has_mutability mode ->
  (forall G Go e t T, @ty_trm mode G Go e t T ->
    forall rename L H e',
      renaming_fixes_outside rename L ->
      renaming_respects_env rename e e' ->
      @renaming_respects_context mode rename G H e' ->
      object_context_can_be_renamed rename H Go ->
      @ty_trm mode H (rename_object_context rename Go) e'
        (rename_trm rename t) (rename_typ rename T)) /\
  (forall G Go e l T, @ty_lit mode G Go e l T ->
    forall rename L H e',
      renaming_fixes_outside rename L ->
      renaming_respects_env rename e e' ->
      @renaming_respects_context mode rename G H e' ->
      object_context_can_be_renamed rename H Go ->
      @ty_lit mode H (rename_object_context rename Go) e'
        (rename_lit rename l) (rename_typ rename T)) /\
  (forall G Go e d D, @ty_def mode G Go e d D ->
    forall rename L H e',
      renaming_fixes_outside rename L ->
      renaming_respects_env rename e e' ->
      @renaming_respects_context mode rename G H e' ->
      object_context_can_be_renamed rename H Go ->
      @ty_def mode H (rename_object_context rename Go) e'
        (rename_def rename d) (rename_dec rename D)) /\
  (forall G Go e ds T, @ty_defs mode G Go e ds T ->
    forall rename L H e',
      renaming_fixes_outside rename L ->
      renaming_respects_env rename e e' ->
      @renaming_respects_context mode rename G H e' ->
      object_context_can_be_renamed rename H Go ->
      @ty_defs mode H (rename_object_context rename Go) e'
        (rename_defs rename ds) (rename_typ rename T)).
Proof.
  intro Hmutable.
  pose proof (proj1 (@variable_judgments_rename mode Hmutable)) as Hvar.
  pose proof (proj1 (proj2 (@variable_judgments_rename mode Hmutable))) as Hsub.
  apply rules_mutind.
  - intros G e x T Hvis Hv rename L H e' Hfix Henv Hctx _. simpl.
    apply ty_trm_var; [eapply rename_vis_var; eassumption |].
    eapply Hvar; [exact Hv | exact Hfix | exact Henv | exact (proj1 Hctx)].
  - intros G e x z S T Hfun. destruct mode; discriminate.
  - intros G e x a S T U Hvis Hv Hadapt rename L H e' Hfix Henv Hctx _. simpl.
    eapply ty_trm_read with (S := rename_typ rename S) (T := rename_typ rename T).
    + eapply rename_vis_var; eassumption.
    + exact (Hvar _ _ _ _ _ Hv rename L H e' Hfix Henv (proj1 Hctx)).
    + eapply viewpoint_renames; [exact Hmutable | exact Hadapt | exact Hfix | exact Henv | exact (proj1 Hctx)].
  - intros G e x y a S T Hvx Hvy Hwrite Hfld Hval rename L H e' Hfix Henv Hctx _. simpl.
    eapply ty_trm_write with (S := rename_typ rename S).
    + eapply rename_vis_var; eassumption.
    + eapply rename_vis_var; eassumption.
    + intro Hmut. exact (Hvar _ _ _ _ _ (Hwrite Hmut) rename L H e' Hfix Henv (proj1 Hctx)).
    + exact (Hvar _ _ _ _ _ Hfld rename L H e' Hfix Henv (proj1 Hctx)).
    + exact (Hvar _ _ _ _ _ Hval rename L H e' Hfix Henv (proj1 Hctx)).
  - intros G e x y m C Z R Hvx Hvy Hmet Harg Hind Hrecv rename L H e' Hfix Henv Hctx _.
    rewrite !(proj1 (rename_typ_open _)). simpl.
    eapply ty_trm_call with (TC := rename_typ rename C) (TZ := rename_typ rename Z).
    + eapply rename_vis_var; eassumption.
    + eapply rename_vis_var; eassumption.
    + exact (Hvar _ _ _ _ _ Hmet rename L H e' Hfix Henv (proj1 Hctx)).
    + exact (Hvar _ _ _ _ _ Harg rename L H e' Hfix Henv (proj1 Hctx)).
    + intro Hsef. apply rename_independent_binder. now apply Hind.
    + rewrite <- (proj1 (rename_typ_open _)).
      exact (Hvar _ _ _ _ _ Hrecv rename L H e' Hfix Henv (proj1 Hctx)).
  - intros L G e t u T U Ht IHt Hu IHu rename K H e' Hfix Henv Hctx _. simpl.
    eapply ty_trm_let with (L := (L \u K) \u ctx_dom H) (T := rename_typ rename T).
    + now apply (IHt rename K H e').
    + intros x Hx. apply notin_union in Hx as [Hx HxH].
      apply notin_union in Hx as [HxL HxK].
      pose proof (Hfix x HxK) as Hxf.
      assert (Hext : @renaming_respects_context mode rename
          (G § x / v_let ~ T) (H § x / v_let ~ rename_typ rename T) e')
        by now apply renaming_respects_context_push.
      pose proof (IHu x HxL rename K (H § x / v_let ~ rename_typ rename T)
        e' Hfix Henv Hext I) as Hu'.
      rewrite (proj1 (rename_trm_open _)), (name_fixed_by_eq Hxf) in Hu'. exact Hu'.
  - intros L G e l u T U Hl IHl Hu IHu rename K H e' Hfix Henv Hctx _. simpl.
    eapply ty_trm_lit with (L := (L \u K) \u ctx_dom H) (T := rename_typ rename T).
    + now apply (IHl rename K H e').
    + intros x Hx. apply notin_union in Hx as [Hx HxH].
      apply notin_union in Hx as [HxL HxK].
      pose proof (Hfix x HxK) as Hxf.
      assert (Hext : @renaming_respects_context mode rename
          (G § x / v_let ~ T) (H § x / v_let ~ rename_typ rename T) e')
        by now apply renaming_respects_context_push.
      pose proof (IHu x HxL rename K (H § x / v_let ~ rename_typ rename T)
        e' Hfix Henv Hext I) as Hu'.
      rewrite (proj1 (rename_trm_open _)), (name_fixed_by_eq Hxf) in Hu'. exact Hu'.
  - intros G e t T U Ht IH Hs rename K H e' Hfix Henv Hctx _. simpl.
    eapply ty_trm_sub with (T := rename_typ rename T).
    + now apply (IH rename K H e').
    + exact (Hsub _ _ _ _ _ Hs rename K H e' Hfix Henv (proj1 Hctx)).
  - intros L G e T t U Hfun. destruct mode; discriminate.
  - intros L G e T ds Hds IH Hind rename K H e' Hfix Henv Hctx _.
    assert (Heq : rename_typ rename (typ_objlit mode T) = typ_objlit mode (rename_typ rename T))
      by (destruct mode; reflexivity).
    rewrite Heq. simpl rename_lit. simpl rename_object_context.
    apply ty_lit_obj with (L := (L \u K) \u ctx_dom H).
    + intros x Hx. apply notin_union in Hx as [Hx HxH].
      apply notin_union in Hx as [HxL HxK].
      pose proof (Hfix x HxK) as Hxf.
      assert (HGo : object_context_can_be_renamed rename H (objctx_lit x T)).
      { simpl. rewrite (name_fixed_by_eq Hxf). split; [intros y; apply (proj1 (Hxf y)) | exact HxH]. }
      pose proof (IH x HxL rename K H e' Hfix Henv Hctx HGo) as Hout.
      rewrite (proj2 (proj2 (proj2 (rename_trm_open _)))),
        (proj1 (rename_typ_open _)) in Hout.
      simpl in Hout. now rewrite (name_fixed_by_eq Hxf) in Hout.
    + now apply rename_independent_binder.
  - intros L G Go e A T U Hq rename K H e' Hfix Henv Hctx HGo. simpl.
    apply ty_def_typ with (L := L \u K).
    intros x Hx. apply notin_union in Hx as [HxL HxK].
    pose proof (renaming_type_equivalence (Hq x HxL) Henv) as Hout.
    rewrite !(proj1 (rename_typ_open _)), (name_fixed_by_eq (Hfix x HxK)) in Hout.
    exact Hout.
  - intros G Go e a x T Hvis Hv rename L H e' Hfix Henv Hctx HGo. simpl.
    pose proof (@renaming_respects_object_context mode rename G H e' Go HGo Hctx) as Hobj.
    apply ty_def_fld.
    + eapply rename_vis_var; eassumption.
    + exact (Hvar _ _ _ _ _ Hv rename L _ e' Hfix Henv (proj1 Hobj)).
  - intros L G Go e m t C Z R Hb IH rename K H e' Hfix Henv Hctx HGo. simpl.
    apply ty_def_met with (L := ((L \u K) \u ctx_dom (H §§& rename_object_context rename Go))).
    intros z Hz r Hne Hr.
    apply notin_union in Hz as [Hz HzH]. apply notin_union in Hz as [HzL HzK].
    apply notin_union in Hr as [Hr HrH]. apply notin_union in Hr as [HrL HrK].
    pose proof (Hfix z HzK) as Hzf. pose proof (Hfix r HrK) as Hrf.
    pose proof (@renaming_respects_method_context mode rename G H e' Go z r Z C
      Hmutable Hctx HGo Hzf Hrf HzH HrH Hne) as Hmeth.
    pose proof (IH z HzL r Hne HrL rename K _ e' Hfix Henv Hmeth I) as Hbody.
    rewrite !(proj1 (rename_typ_open _)), !(proj1 (rename_trm_open _)),
      (name_fixed_by_eq Hzf), (name_fixed_by_eq Hrf) in Hbody.
    exact Hbody.
  - intros G Go e d D Hd IH rename K H e' Hfix Henv Hctx HGo. simpl.
    apply ty_defs_one. now apply (IH rename K H e').
  - intros G Go e ds d T D Hds IHs Hd IHd Hnot rename K H e' Hfix Henv Hctx HGo. simpl.
    apply ty_defs_cons.
    + now apply (IHs rename K H e').
    + now apply (IHd rename K H e').
    + unfold defs_hasnt in *. rewrite rename_def_preserves_label, rename_defs_get, Hnot.
      reflexivity.
Qed.

Local Lemma renaming_respects_types_discharge mode rename G H e x k T :
  @renaming_respects_types mode rename G H e ->
  @ty_var mode H objctx_empty e (rename x) (rename_typ rename T) ->
  @renaming_respects_types mode rename (G § x / k ~ T) H e.
Proof.
  intros Htypes Hvalue v U Hlookup. inversion Hlookup; subst; auto.
Qed.

Local Lemma renaming_respects_context_discharge mode rename G H e x k T :
  @renaming_respects_context mode rename G H e ->
  @ty_var mode H objctx_empty e (rename x) (rename_typ rename T) ->
  ctx_vis H (rename x) ->
  @renaming_respects_context mode rename (G § x / k ~ T) H e.
Proof.
  intros [Htypes Hvis] Hvalue Hx. split.
  - now apply renaming_respects_types_discharge.
  - intros v Hv. apply visible_in_pushed_context in Hv as [->|Hv]; auto.
Qed.

Local Lemma renaming_identity_fixes_outside :
  renaming_fixes_outside (fun x => x) (\{} : vars).
Proof. intros x _ y. tauto. Qed.

Local Lemma renaming_identity_respects_env e :
  renaming_respects_env (fun x => x) e e.
Proof. intros x y Hbind. now apply tyq_var_binds. Qed.

Local Lemma renaming_identity_types mode G e :
  @renaming_respects_types mode (fun x => x) G G e.
Proof.
  intros x T Hbind. rewrite (proj1 (rename_typ_identity _)) by reflexivity.
  now apply ty_var_var.
Qed.

Local Lemma rename_one_type_away x y T :
  x \notin fv T ->
  rename_typ (rename_override (fun z => z) x y) T = T.
Proof.
  intros Hx. apply (proj1 (rename_typ_identity _)).
  intros z Hz. apply rename_override_elsewhere. intro He. subst z. contradiction.
Qed.

Local Lemma rename_one_type_open x y n T :
  x \notin fv T ->
  rename_typ (rename_override (fun z => z) x y) (open_rec n x T) = open_rec n y T.
Proof.
  intros Hx. rewrite rename_type_override_open by exact Hx.
  now rewrite (proj1 (rename_typ_identity _)) by reflexivity.
Qed.

Local Lemma rename_one_term_open x y n t :
  x \notin fv t ->
  rename_trm (rename_override (fun z => z) x y) (open_rec n x t) = open_rec n y t.
Proof.
  intros Hx. rewrite rename_term_override_open by exact Hx.
  now rewrite (proj1 (rename_term_identity _)) by reflexivity.
Qed.

Local Lemma visible_name_in_ctx_dom G x :
  ctx_vis G x -> x \in ctx_dom G.
Proof. induction 1; simpl; rewrite in_union; auto using in_singleton_self. Qed.

Local Lemma renaming_one_binder_base mode G e x y :
  x §# G ->
  x \notin ctx_fv G ->
  @renaming_respects_context mode (rename_override (fun z => z) x y) G G e.
Proof.
  intros Hdom Hfv. split.
  - apply renaming_respects_types_override; try assumption.
    apply renaming_identity_types.
  - intros v Hv.
    rewrite rename_override_elsewhere; [exact Hv |].
    intro He. subst v. apply Hdom. exact (visible_name_in_ctx_dom Hv).
Qed.

Local Lemma renamed_argument_subtype mode G e L w A S T :
  mode_has_mutability mode ->
  @ty_var mode G objctx_empty e w A ->
  (forall z, z \notin L ->
    @subtyp mode (G § z / v_par ~ A) objctx_empty e (open z S) (open z T)) ->
  @subtyp mode G objctx_empty e (open w S) (open w T).
Proof.
  intros Hmutable Harg Hopen.
  destruct (var_fresh (((((L \u ctx_dom G) \u ctx_fv G) \u fv_renv e) \u fv A) \u (fv S \u fv T)))
    as [z Hz].
  repeat rewrite notin_union in Hz.
  destruct Hz as (((((HzL & HzD) & HzG) & [HzKeys HzVals]) & HzA) & [HzS HzT]).
  set (rename := rename_override (fun x => x) z w).
  assert (Hfinite : renaming_fixes_outside rename (((\{} : vars) \u \{z}) \u \{w}))
    by (apply renaming_fixes_outside_override, renaming_identity_fixes_outside).
  assert (Henv : renaming_respects_env rename e e).
  { apply renaming_respects_env_override; [rewrite notin_union; auto | apply renaming_identity_respects_env]. }
  assert (Htypes : @renaming_respects_types mode rename (G § z / v_par ~ A) G e).
  { apply renaming_respects_types_discharge.
    - apply (proj1 (@renaming_one_binder_base mode G e z w HzD HzG)).
    - unfold rename. rewrite rename_override_here, rename_one_type_away by exact HzA.
      exact Harg. }
  pose proof (proj1 (proj2 (@variable_judgments_rename mode Hmutable))
    _ _ _ _ _ (Hopen z HzL) rename _ G e Hfinite Henv Htypes) as Hout.
  unfold rename in Hout. now rewrite !rename_one_type_open in Hout.
Qed.

Local Lemma renamed_let_body mode G e L w A t T :
  mode_has_mutability mode ->
  @ty_var mode G objctx_empty e w A ->
  ctx_vis G w ->
  (forall z, z \notin L ->
    @ty_trm mode (G § z / v_let ~ A) objctx_empty e (open z t) T) ->
  @ty_trm mode G objctx_empty e (open w t) T.
Proof.
  intros Hmutable Harg Hvis Hopen.
  destruct (var_fresh (((((L \u ctx_dom G) \u ctx_fv G) \u fv_renv e) \u fv A) \u (fv t \u fv T)))
    as [z Hz].
  repeat rewrite notin_union in Hz.
  destruct Hz as (((((HzL & HzD) & HzG) & [HzKeys HzVals]) & HzA) & [Hzt HzT]).
  set (rename := rename_override (fun x => x) z w).
  assert (Hfinite : renaming_fixes_outside rename (((\{} : vars) \u \{z}) \u \{w}))
    by (apply renaming_fixes_outside_override, renaming_identity_fixes_outside).
  assert (Henv : renaming_respects_env rename e e).
  { apply renaming_respects_env_override; [rewrite notin_union; auto | apply renaming_identity_respects_env]. }
  assert (Hctx : @renaming_respects_context mode rename (G § z / v_let ~ A) G e).
  { apply renaming_respects_context_discharge.
    - now apply renaming_one_binder_base.
    - unfold rename. rewrite rename_override_here, rename_one_type_away by exact HzA. exact Harg.
    - unfold rename. now rewrite rename_override_here. }
  pose proof (proj1 (@term_judgments_rename mode Hmutable)
    _ _ _ _ _ (Hopen z HzL) rename _ G e Hfinite Henv Hctx I) as Hout.
  unfold rename in Hout. now rewrite rename_one_term_open, rename_one_type_away in Hout.
Qed.

Local Lemma invert_typed_value_term mode G Go e t T :
  @ty_trm mode G Go e t T ->
  forall w, t = trm_var (avar_f w) ->
  vis_var mode G w /\ @ty_var mode G objctx_empty e w T.
Proof.
  induction 1; intros w Hw; inversion Hw; subst; auto.
  specialize (IHty_trm _ eq_refl) as [Hvis Hvar].
  split; [exact Hvis | eapply ty_var_sub; eassumption].
Qed.

Local Lemma typed_let_pop mode G e w t st S U :
  mode_has_mutability mode ->
  @ty_trm mode G objctx_empty e (trm_var (avar_f w)) S ->
  @ty_stack mode G e S (stack_cons (frame_let t) st) U ->
  exists T, @ty_trm mode G objctx_empty e (open w t) T /\ @ty_stack mode G e T st U.
Proof.
  intros Hmutable Hv Hst. inversion Hst; subst.
  destruct (invert_typed_value_term Hv eq_refl) as [Hvis Hvar].
  eexists. split; [eapply renamed_let_body; try eassumption | eassumption].
  apply Hvis, mode_has_hidden_method_bodies, Hmutable.
Qed.

Local Lemma avar_opening_free_variables (a : avar) n x v :
  v \in fv (open_rec n x a) -> v = x \/ v \in fv a.
Proof.
  destruct a; simpl; [case_if |]; simpl; intro Hmem; try (now right).
  left. now rewrite in_singleton in Hmem.
Qed.

Local Lemma type_opening_free_variables :
  (forall (T : typ) n x v, v \in fv (open_rec n x T) -> v = x \/ v \in fv T) /\
  (forall (D : dec) n x v, v \in fv (open_rec n x D) -> v = x \/ v \in fv D).
Proof.
  apply typ_mutind; intros;
    cbn [open_rec TypOpenable DecOpenable open_rec_typ open_rec_dec fv
      TypFreeVar DecFreeVar fv_typ fv_dec] in *;
    repeat rewrite in_union in *; firstorder.
  all: match goal with H : ?v \in fv (@open_rec avar _ ?n ?x ?a) |- _ =>
    destruct (@avar_opening_free_variables a n x v H); tauto
  end.
Qed.

Local Lemma term_opening_free_variables :
  (forall (t : trm) n x v, v \in fv (open_rec n x t) -> v = x \/ v \in fv t) /\
  (forall (l : lit) n x v, v \in fv (open_rec n x l) -> v = x \/ v \in fv l) /\
  (forall (d : def) n x v, v \in fv (open_rec n x d) -> v = x \/ v \in fv d) /\
  (forall (ds : defs) n x v, v \in fv (open_rec n x ds) -> v = x \/ v \in fv ds).
Proof.
  destruct type_opening_free_variables as [HT _].
  apply trm_mutind; intros;
    cbn [open_rec TrmOpenable LitOpenable DefOpenable DefsOpenable
      open_rec_trm open_rec_lit open_rec_def open_rec_defs fv
      TypFreeVar TrmFreeVar LitFreeVar DefFreeVar DefsFreeVar
      fv_trm fv_lit fv_def fv_defs] in *;
    repeat rewrite in_union in *; firstorder.
  all: match goal with
  | H : ?v \in fv (@open_rec avar _ ?n ?x ?a) |- _ =>
    destruct (@avar_opening_free_variables a n x v H); tauto
  | H : ?v \in fv (@open_rec typ _ ?n ?x ?a) |- _ =>
    destruct (HT a n x v H); tauto
  end.
Qed.

Local Definition rename_method_parameters z r arg recv :=
  rename_override (rename_override (fun x => x) r recv) z arg.

Local Lemma rename_method_argument z r arg recv :
  rename_method_parameters z r arg recv z = arg.
Proof. apply rename_override_here. Qed.

Local Lemma rename_method_receiver z r arg recv :
  r <> z ->
  rename_method_parameters z r arg recv r = recv.
Proof.
  intro Hne. unfold rename_method_parameters.
  now rewrite rename_override_elsewhere, rename_override_here.
Qed.

Local Lemma rename_method_parameters_type z r arg recv T :
  z \notin fv T ->
  r \notin fv T ->
  rename_typ (rename_method_parameters z r arg recv) T = T.
Proof.
  intros Hz Hr. apply (proj1 (rename_typ_identity _)).
  intros x Hx. unfold rename_method_parameters.
  now rewrite !rename_override_elsewhere by congruence.
Qed.

Local Lemma rename_opened_method_type z r arg recv T :
  z <> r ->
  z \notin fv T ->
  r \notin fv T ->
  rename_typ (rename_method_parameters z r arg recv) (open_met z r T) =
  open_met arg recv T.
Proof.
  intros Hne Hz Hr. unfold rename_method_parameters.
  rewrite rename_type_override_open.
  - now rewrite rename_one_type_open.
  - intro Hbad. destruct ((proj1 type_opening_free_variables) _ _ _ _ Hbad); contradiction.
Qed.

Local Lemma rename_opened_method_term z r arg recv t :
  z <> r ->
  z \notin fv t ->
  r \notin fv t ->
  rename_trm (rename_method_parameters z r arg recv) (open_met z r t) =
  open_met arg recv t.
Proof.
  intros Hne Hz Hr. unfold rename_method_parameters.
  rewrite rename_term_override_open.
  - now rewrite rename_one_term_open.
  - intro Hbad. destruct ((proj1 term_opening_free_variables) _ _ _ _ Hbad); contradiction.
Qed.

Local Lemma fresh_method_parameter_renaming mode G e arg recv (V : vars) :
  exists z r K,
    z \notin V /\ r \notin V /\ r <> z /\
    let rename := rename_method_parameters z r arg recv in
    renaming_fixes_outside rename K /\
    renaming_respects_env rename e e /\
    @renaming_respects_context mode rename G G e.
Proof.
  set (avoid := ((V \u ctx_dom G) \u ctx_fv G) \u fv_renv e).
  destruct (var_fresh avoid) as [z Hz].
  destruct (var_fresh (avoid \u \{z})) as [r Hr].
  apply notin_union in Hr as [Hr Hne]. apply notin_singleton in Hne.
  unfold avoid in Hz, Hr.
  repeat rewrite notin_union in Hz, Hr.
  destruct Hz as [[[HzV HzD] HzG] [HzK HzE]].
  destruct Hr as [[[HrV HrD] HrG] [HrK HrE]].
  exists z, r, (((((\{} : vars) \u \{r}) \u \{recv}) \u \{z}) \u \{arg}).
  split; [exact HzV |]. split; [exact HrV |]. split; [exact Hne |]. cbv zeta.
  split.
  - unfold rename_method_parameters.
    do 2 apply renaming_fixes_outside_override. apply renaming_identity_fixes_outside.
  - split.
    + unfold rename_method_parameters.
      do 2 (apply renaming_respects_env_override; [rewrite notin_union; auto |]).
      apply renaming_identity_respects_env.
    + split.
      * unfold rename_method_parameters.
        do 2 (apply renaming_respects_types_override; [assumption | assumption |]).
        apply renaming_identity_types.
      * intros v Hvis.
        assert (Hvdom : v \in ctx_dom G).
        { exact (visible_name_in_ctx_dom Hvis). }
        unfold rename_method_parameters.
        now rewrite !rename_override_elsewhere by congruence.
Qed.

Local Lemma renamed_method_result_subtype mode G e L w z C Z S T :
  mode_has_mutability mode ->
  @ty_var mode G objctx_empty e z Z ->
  @ty_var mode G objctx_empty e w (open z C) ->
  (forall r, r \notin L -> forall q, q <> r -> q \notin L ->
    @subtyp mode (ctx_met G r Z q C) objctx_empty e
      (open_met r q S) (open_met r q T)) ->
  @subtyp mode G objctx_empty e (open_met z w S) (open_met z w T).
Proof.
  intros Hmutable Harg Hrecv Hopen.
  destruct (@fresh_method_parameter_renaming mode G e z w
     ((((L \u fv C) \u fv Z) \u fv S) \u fv T))
     as (zr & rr & K & Hz & Hr & Hne & Hfix & Henv & Hctx).
  repeat rewrite notin_union in Hz, Hr.
  destruct Hz as [[[[HzL HzC] HzZ] HzS] HzT].
  destruct Hr as [[[[HrL HrC] HrZ] HrS] HrT].
  set (f := rename_method_parameters zr rr z w) in *.
  assert (Hmap : @renaming_respects_types mode f (ctx_met G zr Z rr C) G e).
  { apply renaming_respects_types_discharge.
    - apply renaming_respects_types_discharge.
      + exact (proj1 Hctx).
      + unfold f. rewrite rename_method_argument, rename_method_parameters_type by assumption.
        exact Harg.
    - unfold f. rewrite rename_method_receiver by exact Hne.
      unfold rename_method_parameters.
      rewrite rename_type_override_open, rename_one_type_away by assumption. exact Hrecv. }
  pose proof (proj1 (proj2 (@variable_judgments_rename mode Hmutable))
    _ _ _ _ _ (Hopen zr HzL rr Hne HrL) f K G e Hfix Henv Hmap) as Hsub.
  unfold f in Hsub. now rewrite !rename_opened_method_type in Hsub.
Qed.

Local Lemma renamed_heap_method_body mode G e y Shape m body C Z R w v :
  mode_has_mutability mode ->
  @ty_def mode G (objctx_heap y Shape) e (def_met m body) (dec_met m C Z R) ->
  @ty_var mode G objctx_empty e v Z ->
  @ty_var mode G objctx_empty e w (open v C) ->
  @ty_var mode G objctx_empty e w (open y Shape) ->
  @ty_var mode G objctx_empty e w (open w Shape) ->
  ctx_vis G v -> ctx_vis G w ->
  @ty_trm mode G objctx_empty e (open_met v w body) (open_met v w R).
Proof.
  intros Hmutable Hmethod Harg Hrecv Hlocation Hself HvisV HvisW.
  assert (Hmode : mode_has_visibility mode) by now apply mode_has_hidden_method_bodies.
  assert (Hbody : exists L, forall z, z \notin L -> forall r, r <> z -> r \notin L ->
    @ty_trm mode (ctx_obj_met mode G (objctx_heap y Shape) z Z r C) objctx_empty e
      (open_met z r body) (open_met z r R)).
  { inversion Hmethod; subst. eexists. eassumption. }
  destruct Hbody as [L Hbody].
  destruct (@fresh_method_parameter_renaming mode G e v w
      ((((((L \u fv C) \u fv Z) \u fv R) \u fv Shape) \u fv body) \u \{y}))
      as (z & r & K & Hz & Hr & Hne & Hfix & Henv & Hctx).
  repeat rewrite notin_union in Hz, Hr.
  destruct Hz as [[[[[[HzL HzC] HzZ] HzR] HzS] Hzt] Hzy].
  destruct Hr as [[[[[[HrL HrC] HrZ] HrR] HrS] Hrt] Hry].
  apply notin_singleton in Hzy, Hry.
  set (f := rename_method_parameters z r v w) in *.
  assert (Hmap : @renaming_respects_context mode f
    (ctx_obj_met mode G (objctx_heap y Shape) z Z r C) G e).
  { unfold ctx_obj_met. rewrite Hmode. simpl.
    apply renaming_respects_context_discharge.
    - apply renaming_respects_context_discharge.
      + split.
        * intros x T Hbind. inversion Hbind; subst. eapply (proj1 Hctx); eassumption.
        * intros x Hvis. inversion Hvis.
      + unfold f. rewrite rename_method_argument, rename_method_parameters_type by assumption.
        exact Harg.
      + unfold f. now rewrite rename_method_argument.
    - unfold f. change (@ty_var mode G objctx_empty e
        (rename_method_parameters z r v w r)
        (typ_and (rename_typ (rename_method_parameters z r v w) (open z C))
          (typ_and (rename_typ (rename_method_parameters z r v w) (open y Shape))
            (rename_typ (rename_method_parameters z r v w) (open r Shape))))).
      rewrite !(proj1 (rename_typ_open _)), rename_method_argument, rename_method_receiver by assumption.
      rewrite !rename_method_parameters_type by assumption.
      replace (rename_method_parameters z r v w y) with y.
      + apply ty_var_and; [exact Hrecv | now apply ty_var_and].
      + unfold rename_method_parameters. now rewrite !rename_override_elsewhere by congruence.
    - unfold f. now rewrite rename_method_receiver by assumption. }
  pose proof (proj1 (@term_judgments_rename mode Hmutable)) as Htransfer.
  pose proof (Htransfer _ _ _ _ _ (Hbody z HzL r Hne HrL) f K G e Hfix Henv Hmap I)
    as Hout.
  unfold f in Hout. now rewrite rename_opened_method_term, rename_opened_method_type in Hout by congruence.
Qed.

Local Lemma typed_call_view mode G Go e t U :
  @ty_trm mode G Go e t U ->
  mode_has_sef mode ->
  forall w m z, t = trm_call (avar_f w) m (avar_f z) ->
  exists C Z R,
    vis_var mode G w /\ vis_var mode G z /\
    typ_indep_b 0 C /\
    @ty_var mode G objctx_empty e w (typ_rcd (dec_met m C Z R)) /\
    @ty_var mode G objctx_empty e z Z /\
    @ty_var mode G objctx_empty e w (open z C) /\
    @subtyp mode G objctx_empty e (open_met z w R) U.
Proof.
  induction 1; intros Hsef receiver method argument Heq; try discriminate.
  - inversion Heq; subst. exists TC, TZ, TR. repeat split; auto. apply subtyp_refl.
  - destruct (IHty_trm Hsef receiver method argument Heq)
      as (C & Z & R & Hw & Hz & Hi & Hv & Ha & Hr & Hs).
    exists C, Z, R. repeat split; try assumption.
    eapply subtyp_trans; eassumption.
Qed.

Local Lemma typed_nested_call mode G e h w z y ds m body U :
  mode_has_sef mode ->
  mode_has_mutability mode ->
  @inert mode G ->
  @heap_correspond mode G e h ->
  binds w y e ->
  binds y (item_obj ds) h ->
  defs_has ds (def_met m body) ->
  @ty_trm mode G objctx_empty e (trm_call (avar_f w) m (avar_f z)) U ->
  @ty_trm mode G objctx_empty e (open_met z w body) U.
Proof.
  intros Hsef Hmutable Hiner Hheap Hw Hy Hfield Htyped.
  destruct (typed_call_view Htyped Hsef eq_refl)
    as (Ca & Za & Ra & Hwvis & Hzvis & _ & Hlook & Harg & Hrecv & Hret).
  assert (Hmode : mode_has_visibility mode) by now apply mode_has_hidden_method_bodies.
  specialize (Hwvis Hmode). specialize (Hzvis Hmode).
  destruct (@heap_reference_precise_definition mode G e h w y ds
    (def_met m body) Hmutable Hiner Hheap Hw Hy Hfield)
    as (S & B & D & Hctx & Hshape & Hdef & Hdecl & _).
  assert (Hactual : exists C Z R,
    @ty_def mode G (objctx_heap y S) e (def_met m body) (dec_met m C Z R) /\
    record_has (open y S) (dec_met m C Z R)).
  { inversion Hdef; subst; repeat eexists; eassumption. }
  destruct Hactual as (C & Z & R & Hmethod & Hdeclaration).
  clear D Hdef Hdecl.
  assert (Hcomponents : @method_subtype_components mode G e C Z R Ca Za Ra).
  { pose proof (exact_member_from_heap_reference Hmutable Hheap Hw Hctx Hdeclaration) as Hprecise.
    pose proof (proj1 (proj1 (layered_typing_sound Hmutable Hiner Hheap) _ _ Hlook 0))
      as Hshapevar.
    simpl in Hshapevar. inversion Hshapevar; subst.
    match goal with H : exact_object_member G e w (dec_met m ?C0 ?Z0 ?R0) |- _ =>
      tryif constr_eq H Hprecise then fail else
      pose proof (exact_object_members_unique Hiner Hprecise H eq_refl) as Heq
    end.
    inversion Heq; subst. assumption. }
  destruct Hcomponents as (HargSub & _ & L & HreceiverSub & HresultSub).
  assert (Harg' : @ty_var mode G objctx_empty e z Z)
    by (eapply ty_var_sub; eassumption).
  assert (Hrecv' : @ty_var mode G objctx_empty e w (open z C)).
  { eapply ty_var_sub; [exact Hrecv |].
    exact (@renamed_argument_subtype mode G e L z Za Ca C Hmutable Harg HreceiverSub). }
  assert (Hself : @ty_var mode G objctx_empty e w (open w S)).
  { apply ty_rec_elim; [|exact Hshape]. eapply ty_var_sub.
    - apply ty_var_var. exact Hctx.
    - apply subtyp_and11. }
  assert (Hlocation : @ty_var mode G objctx_empty e w (open y S)).
  { eapply ty_var_sub; [exact Hself |]. apply subtyp_tyq.
    apply aliased_open_type; [now apply tyq_var_binds | exact Hshape]. }
  assert (Hbody : @ty_trm mode G objctx_empty e (open_met z w body) (open_met z w R)).
  { eapply renamed_heap_method_body; eassumption. }
  eapply ty_trm_sub; [exact Hbody |].
  eapply subtyp_trans; [|exact Hret].
  exact (@renamed_method_result_subtype mode G e L w z Ca Za R Ra Hmutable Harg Hrecv HresultSub).
Qed.

Local Definition swap_variable_names x y :=
  rename_method_parameters x y y x.

Local Lemma swap_variable_names_other x y v :
  v <> x -> v <> y -> swap_variable_names x y v = v.
Proof.
  intros Hx Hy. unfold swap_variable_names, rename_method_parameters.
  now rewrite !rename_override_elsewhere.
Qed.

Local Lemma swap_variable_names_involution x y v :
  x <> y ->
  swap_variable_names x y (swap_variable_names x y v) = v.
Proof.
  intros Hne. destruct (classic (v = x)) as [->|Hx].
  - unfold swap_variable_names. rewrite rename_method_argument.
    now rewrite rename_method_receiver by congruence.
  - destruct (classic (v = y)) as [->|Hy].
    + unfold swap_variable_names. rewrite rename_method_receiver by congruence.
      apply rename_method_argument.
    + pose proof (@swap_variable_names_other x y v Hx Hy) as Heq.
      rewrite Heq. exact Heq.
Qed.

Local Lemma opened_literal_definitions_at_fresh_name mode G e L w R ds :
  mode_has_mutability mode ->
  w §# G ->
  w \notin ctx_fv G ->
  w \notin fv_renv e ->
  w \notin fv R ->
  w \notin fv ds ->
  (forall x, x \notin L ->
    @ty_defs mode G (objctx_lit x R) e (open x ds) (open x R)) ->
  @ty_defs mode G (objctx_lit w R) e (open w ds) (open w R).
Proof.
  intros Hmutable HwG HwF HwE HwR HwD Hopen.
  destruct (var_fresh ((((((L \u ctx_dom G) \u ctx_fv G) \u fv_renv e)
    \u fv R) \u fv ds) \u \{w})) as [z Hz].
  repeat rewrite notin_union in Hz.
  destruct Hz as [[[[[[HzL HzG] HzF] [HzKey HzVal]] HzR] HzD] Hne].
  apply notin_singleton in Hne.
  set (f := swap_variable_names z w).
  assert (Hfix : renaming_fixes_outside f (((((\{} : vars) \u \{w}) \u \{z}) \u \{z}) \u \{w})).
  { unfold f, swap_variable_names, rename_method_parameters.
    do 2 apply renaming_fixes_outside_override. apply renaming_identity_fixes_outside. }
  assert (Henv : renaming_respects_env f e e).
  { unfold f, swap_variable_names, rename_method_parameters.
    apply renaming_respects_env_override; [rewrite notin_union; now split |].
    apply renaming_respects_env_override; [exact HwE | apply renaming_identity_respects_env]. }
  assert (Hctx : @renaming_respects_context mode f G G e).
  { split.
    - unfold f, swap_variable_names, rename_method_parameters.
      do 2 (apply renaming_respects_types_override; [assumption | assumption |]).
      apply renaming_identity_types.
    - intros u Hu.
      assert (Hdom : u \in ctx_dom G)
        by exact (visible_name_in_ctx_dom Hu).
      unfold f. now rewrite swap_variable_names_other by congruence. }
  assert (Hmap : f z = w) by apply rename_method_argument.
  assert (Hobj : object_context_can_be_renamed f G (objctx_lit z R)).
  { simpl. split; [|now rewrite Hmap].
    intros u Hu. unfold f in Hu. apply (f_equal (swap_variable_names z w)) in Hu.
    now rewrite !swap_variable_names_involution in Hu. }
  pose proof (proj2 (proj2 (proj2 (@term_judgments_rename mode Hmutable)))) as Htransfer.
  pose proof (Htransfer _ _ _ _ _ (Hopen z HzL) f _ G e Hfix Henv Hctx Hobj) as Hout.
  assert (HR : rename_typ f R = R).
  { apply (proj1 (rename_typ_identity _)).
    intros u Hu. unfold f. now rewrite swap_variable_names_other by congruence. }
  assert (HD : rename_defs f ds = ds).
  { apply (proj2 (proj2 (proj2 (rename_term_identity _)))).
    intros u Hu. unfold f. now rewrite swap_variable_names_other by congruence. }
  rewrite (proj1 (rename_typ_open _)),
    (proj2 (proj2 (proj2 (rename_trm_open _)))) in Hout.
  simpl in Hout. now rewrite HR, HD, Hmap in Hout.
Qed.

Local Definition live_references_are_protected mode G c (old : vars) :=
  forall w y,
    (tfree_trm w (config_trm c) \/ tfree_stack w (config_stack c)) ->
    binds w y (config_env c) ->
    y \in old ->
    @reference_is_protected mode G (config_env c) w.

Local Lemma standalone_aliases_protect_live_references mode G c z r Rz Rr old :
  config_stack c = stack_nil ->
  ctx_binds z (typ_and (typ_bnd Rz) (typ_mut_marker typ_top)) G ->
  ctx_binds r (typ_and (typ_bnd Rr) (typ_mut_marker typ_top)) G ->
  (forall w, tfree_trm w (config_trm c) -> w = z \/ w = r) ->
  @live_references_are_protected mode G c old.
Proof.
  intros Hstack Hz Hr Hscope w y [Hterm|Hst] _ _.
  - destruct (Hscope _ Hterm) as [-> | ->]; eapply top_marker_protects_reference; eassumption.
  - rewrite Hstack in Hst. inversion Hst.
Qed.

Local Lemma protected_receiver_forbids_old_write mode G c old x a v y U :
  mode_has_mutability mode ->
  @inert mode G ->
  @heap_correspond mode G (config_env c) (config_heap c) ->
  @ty_trm mode G objctx_empty (config_env c) (config_trm c) U ->
  @live_references_are_protected mode G c old ->
  config_trm c = trm_write (avar_f x) a (avar_f v) ->
  binds x y (config_env c) ->
  y \in old ->
  False.
Proof.
  intros Hmutable Hiner HH Htyped Hlive Hwrite Hbind Hold.
  assert (Hfree : tfree_trm x (config_trm c))
    by (rewrite Hwrite; apply tfree_trm_write_l).
  destruct (Hlive x y (or_introl Hfree) Hbind Hold) as (R & B & HB & Hprotected).
  pose proof (typed_write_receiver Htyped Hmutable Hwrite) as Hcap.
  exact (@protected_reference_excludes_write mode G (config_env c) (config_heap c)
    x R B Hmutable Hiner HH HB Hprotected Hcap).
Qed.

Local Definition runtime_typechecks mode G c U :=
  @inert mode G /\
  @heap_correspond mode G (config_env c) (config_heap c) /\
  exists T, @ty_trm mode G objctx_empty (config_env c) (config_trm c) T /\
    @ty_stack mode G (config_env c) T (config_stack c) U.

Local Lemma typed_config_runtime_typechecks mode G c U :
  @ty_config mode G c U -> @runtime_typechecks mode G c U.
Proof. destruct 1. split; [assumption |]. split; [assumption |]. simpl. eexists; split; eassumption. Qed.

Local Lemma fresh_binding_changes_renv (e : renv) w y :
  w # e -> e & w ~ y <> e.
Proof.
  intros Hfresh Heq. apply Hfresh. rewrite <- Heq, dom_push, in_union.
  left. apply in_singleton_self.
Qed.

Local Lemma allocation_free_reduction_preserves_live_protection mode G c d U old :
  mode_has_mutability mode ->
  mode_has_sef mode ->
  @runtime_typechecks mode G c U ->
  @live_references_are_protected mode G c old ->
  c ↦ d ->
  config_env d = config_env c ->
  @runtime_typechecks mode G d U /\
  @live_references_are_protected mode G d old /\
  config_heap d = config_heap c \/
  exists x a v y,
    config_trm c = trm_write (avar_f x) a (avar_f v) /\
    binds x y (config_env c) /\ y \notin old.
Proof.
  intros Hmutable Hsef (HI & HH & T & Htyped & Hstack) Hlive Hred Henv.
  destruct Hred as
    [yObj wObj a h e L yVal wVal ds st Hfresh Hrecv Hobj Hfield
    |yObj wObj a h e L yArg wArg h' st Hupd Hrecv Harg
    |yObj wObj m h e L wArg body ds st Hobj Hmethod Hrecv
    |yFun wFun wArg h e L body st Hobj Hrecv
    |X body t h e L y w st Hfresh Hneq
    |X ds t h e L y w st Hfresh Hneq
    |t h e L x st
    |s t st h e L]; simpl in *.
  - exfalso. apply (@fresh_binding_changes_renv e wVal yVal); [|exact Henv].
    destruct Hfresh as [Hf _]. repeat rewrite notin_union in Hf. tauto.
  - right. exists wObj, a, wArg, yObj. split; [reflexivity |].
    split; [exact Hrecv |].
    intro Hold. eapply (@protected_receiver_forbids_old_write mode G
      (trm_write (avar_f wObj) a (avar_f wArg) ; st ; h ; e ; L)
      old wObj a wArg yObj T); try eassumption; reflexivity.
  - left. split.
    + split; [exact HI |]. split; [exact HH |].
      exists T. split; [|exact Hstack].
      eapply typed_nested_call; eassumption.
    + split; [|auto].
      intros w y [Hterm | Hst] Hb Hold; apply (Hlive w y); try assumption.
      * left.
        destruct (@heap_reference_precise_definition mode G e h wObj yObj ds
          (def_met m body) Hmutable HI HH Hrecv Hobj Hmethod)
          as (R & B & D & Hbinding & _ & Hdef & _ & _).
        destruct (@opened_typed_method_free_scope mode G (objctx_heap yObj R) e m body D
          wArg wObj w Hmutable Hdef Hterm) as [-> | ->].
        -- apply tfree_trm_call_r.
        -- apply tfree_trm_call_l.
      * now right.
  - exfalso. clear Hstack Hlive Hobj Hrecv.
    match goal with H : ty_trm _ _ _ _ _ _ |- _ =>
      remember (trm_apply (avar_f wFun) (avar_f wArg)) as t eqn:Heq in H;
      induction H; try discriminate; eauto; destruct mode; discriminate
    end.
  - exfalso. apply (@fresh_binding_changes_renv e w y); [|exact Henv].
    destruct Hfresh as [_ [Hf _]]. repeat rewrite notin_union in Hf. tauto.
  - exfalso. apply (@fresh_binding_changes_renv e w y); [|exact Henv].
    destruct Hfresh as [_ [Hf _]]. repeat rewrite notin_union in Hf. tauto.
  - left. split.
    + split; [exact HI |]. split; [exact HH |].
      eapply typed_let_pop; eassumption.
    + split; [|auto].
      intros w y [Hterm | Hst] Hb Hold; apply (Hlive w y); try assumption.
      * destruct ((proj1 tfree_open_backward) _ _ _ _ Hterm) as [-> | Hfree].
        -- left. apply tfree_trm_var.
        -- right. now apply tfree_stack_cons_l.
      * right. now apply tfree_stack_cons_r.
  - left. split.
    + split; [exact HI |]. split; [exact HH |].
      eapply typed_let_push; eassumption.
    + split; [|auto].
      intros w y [Hterm | Hst] Hb Hold; apply (Hlive w y); try assumption.
      * left. now apply tfree_trm_let_l.
      * inversion Hst; subst; [left; now apply tfree_trm_let_r | now right].
Qed.

Local Lemma reduction_keeps_or_extends_renv c d :
  c ↦ d ->
  config_env d = config_env c \/
  exists w y, w # (config_env c) /\ config_env d = config_env c & w ~ y.
Proof.
  destruct 1; simpl; try (left; reflexivity).
  - right. exists wVal, yVal. split; [|reflexivity].
    destruct H as [Hfresh _]. repeat rewrite notin_union in Hfresh. tauto.
  - right. exists w, y. split; [|reflexivity].
    destruct H as [_ [Hfresh _]]. repeat rewrite notin_union in Hfresh. tauto.
  - right. exists w, y. split; [|reflexivity].
    destruct H as [_ [Hfresh _]]. repeat rewrite notin_union in Hfresh. tauto.
Qed.

Local Lemma prefix_renv_when_final_env_unchanged c d f n :
  c ⊣n↦* d ->
  d ↦ f ->
  config_env f = config_env c ->
  config_env d = config_env c /\ config_env f = config_env d.
Proof.
  intros Htrace Hstep Hequiv.
  destruct (reduction_keeps_or_extends_renv Hstep) as [Hsame | (w & y & Hfresh & Heq)].
  - split; [now rewrite <- Hsame | exact Hsame].
  - exfalso. apply Hfresh.
    eapply trace_does_not_remove_env_keys; [exact Htrace |].
    rewrite <- Hequiv, Heq, dom_push, in_union. left. apply in_singleton_self.
Qed.

Local Lemma allocation_free_trace_preserves_protected_state mode G c n d U old :
  mode_has_mutability mode ->
  mode_has_sef mode ->
  c ⊣n↦* d ->
  config_env d = config_env c ->
  @runtime_typechecks mode G c U ->
  @live_references_are_protected mode G c old ->
  dom (config_heap c) \c old ->
  @runtime_typechecks mode G d U /\
  @live_references_are_protected mode G d old /\
  config_heap d = config_heap c.
Proof.
  intros Hmutable Hsef Htrace.
  induction Htrace as [c | c q d n Htrace IH Hstep];
    intros Henv Htyped Hlive Hold.
  - auto.
  - destruct (prefix_renv_when_final_env_unchanged Htrace Hstep Henv)
      as [Hqenv Hdenv].
    destruct (IH Hqenv Htyped Hlive Hold) as (Hqty & Hqlive & Hqheap).
    destruct (@allocation_free_reduction_preserves_live_protection mode G q d U old
      Hmutable Hsef Hqty Hqlive Hstep Hdenv)
      as [(Hdty & Hdlive & Hdheap) | (x & a & v & y & Hwrite & Hbind & Houtside)].
    + rewrite <- Hqheap. auto.
    + exfalso. apply Houtside, Hold. rewrite <- Hqheap.
      destruct Hqty as (_ & HH & _).
      destruct (typed_heap_places_refs_and_locations Hmutable HH) as [Htargets _].
      eapply Htargets; eassumption.
Qed.

Local Lemma standalone_readonly_execution_no_allocations mode G c U z r Rz Rr n d x a v y it :
  mode_has_mutability mode ->
  mode_has_sef mode ->
  @ty_config mode G c U ->
  config_stack c = stack_nil ->
  ctx_binds z (typ_and (typ_bnd Rz) (typ_mut_marker typ_top)) G ->
  ctx_binds r (typ_and (typ_bnd Rr) (typ_mut_marker typ_top)) G ->
  (forall w, tfree_trm w (config_trm c) -> w = z \/ w = r) ->
  c ⊣n↦* d ->
  config_env d = config_env c ->
  config_trm d = trm_write (avar_f x) a (avar_f v) ->
  binds x y (config_env d) ->
  binds y it (config_heap c) ->
  False.
Proof.
  intros Hmutable Hsef Htyped Hstack Hz Hr Hscope Hrun Henv Hw Hb Hy.
  pose proof (typed_config_runtime_typechecks Htyped) as Htype.
  pose proof (@standalone_aliases_protect_live_references mode G c z r Rz Rr
    (dom (config_heap c)) Hstack Hz Hr Hscope) as Hlive.
  destruct (@allocation_free_trace_preserves_protected_state mode G c n d U
    (dom (config_heap c)) Hmutable Hsef Hrun Henv Htype Hlive ltac:(intros loc Hloc; exact Hloc))
    as ((HI & HH & T & Hterm & Hst) & Hprotected & Hheap).
  exact (@protected_receiver_forbids_old_write mode G d (dom (config_heap c))
    x a v y T Hmutable HI HH Hterm Hprotected Hw Hb (get_some_inv Hy)).
Qed.

Local Lemma avar_opening_injective_when_fresh x k (a b : avar) :
  x \notin fv a ->
  x \notin fv b ->
  open_rec k x a = open_rec k x b ->
  a = b.
Proof.
  destruct a as [i|u], b as [j|v]; simpl; intros Ha Hb Heq.
  - destruct (classic (k = i)) as [Hi|Hi], (classic (k = j)) as [Hj|Hj].
    + congruence.
    + replace (If k = i then avar_f x else avar_b i) with (avar_f x) in Heq by (case_if; congruence).
      replace (If k = j then avar_f x else avar_b j) with (avar_b j) in Heq by (case_if; congruence).
      discriminate.
    + replace (If k = i then avar_f x else avar_b i) with (avar_b i) in Heq by (case_if; congruence).
      replace (If k = j then avar_f x else avar_b j) with (avar_f x) in Heq by (case_if; congruence).
      discriminate.
    + replace (If k = i then avar_f x else avar_b i) with (avar_b i) in Heq by (case_if; congruence).
      replace (If k = j then avar_f x else avar_b j) with (avar_b j) in Heq by (case_if; congruence).
      exact Heq.
  - revert Heq. case_if; intro Heq; try discriminate.
    injection Heq as ->. contradiction (Hb (in_singleton_self _)).
  - revert Heq. case_if; intro Heq; try discriminate.
    injection Heq as ->. contradiction (Ha (in_singleton_self _)).
  - congruence.
Qed.

Local Lemma type_opening_injective_when_fresh :
  (forall (S : typ) k x (T : typ),
    x \notin fv S -> x \notin fv T ->
    open_rec k x S = open_rec k x T -> S = T) /\
  (forall (D : dec) k x (E : dec),
    x \notin fv D -> x \notin fv E ->
    open_rec k x D = open_rec k x E -> D = E).
Proof.
  apply typ_mutind; intros; destruct T || destruct E;
    cbn [open_rec TypOpenable DecOpenable open_rec_typ open_rec_dec fv
      TypFreeVar DecFreeVar fv_typ fv_dec] in *; try discriminate; try reflexivity.
  all: repeat match goal with
    | H : _ \notin _ \u _ |- _ => apply notin_union in H as [? ?]
    end.
  all: match goal with H : _ = _ |- _ => inversion H; subst end.
  all: f_equal; try congruence; eauto 6 using avar_opening_injective_when_fresh.
Qed.

Local Lemma open_unchanged_declaration_label (D : dec) k x :
  label_of (open_rec k x D) = label_of D.
Proof. destruct D; reflexivity. Qed.

Local Lemma record_dec_before_fresh_opening D x :
  x \notin fv D ->
  record_dec (open x D) ->
  record_dec D.
Proof.
  destruct D as [A S T | a S T | m C Z R]; simpl; intros Hfresh Hdec.
  all: inversion Hdec; subst; try solve [constructor].
  all: repeat match goal with
    | H : _ \notin _ \u _ |- _ => apply notin_union in H as [? ?]
    end.
  all: try solve [
    assert (S = T) by (eapply (proj1 type_opening_injective_when_fresh); eassumption);
    subst T; constructor].
  assert (S = typ_bot).
  { destruct S; simpl in *; congruence. }
  subst S. apply rd_typb.
Qed.

Local Lemma opened_record_typ_before_fresh_opening (R : typ) x ls :
  x \notin fv R ->
  record_typ (open x R) ls ->
  record_typ R ls.
Proof.
  intros Hfv Hrecord.
  remember (open x R) as U eqn:Heq in Hrecord.
  revert R Hfv Heq.
  induction Hrecord as [D l Hd Hlabel | T ls D l Hrecord IH Hd Hlabel Hnew];
    intros R Hfv Heq; destruct R; simpl in Heq; try discriminate.
  - injection Heq as ->.
    apply rt_one; [now apply (@record_dec_before_fresh_opening _ x) |].
    now rewrite <- (open_unchanged_declaration_label d 0 x).
  - injection Heq as HeqLeft HeqRight.
    destruct R2; simpl in HeqRight; try discriminate.
    injection HeqRight as ->.
    cbn [fv TypFreeVar fv_typ] in Hfv. apply notin_union in Hfv as [Hfv1 Hfv2].
    eapply rt_cons.
    + exact (IH R1 Hfv1 HeqLeft).
    + now apply (@record_dec_before_fresh_opening _ x).
    + now rewrite <- (open_unchanged_declaration_label d 0 x).
    + exact Hnew.
Qed.

Local Lemma typed_def_declares_record_member mode G Go e d D :
  @ty_def mode G Go e d D ->
  record_dec D /\ label_of d = label_of D.
Proof. destruct 1; split; constructor. Qed.

Local Lemma record_label_has_member R ls ls_member :
  record_typ R ls ->
  ls_member \in ls ->
  exists D, record_has R D /\ label_of D = ls_member.
Proof.
  intros Hrecord. induction Hrecord; intro Hls.
  - rewrite in_singleton in Hls. subst l. now exists D; split; [constructor |].
  - rewrite in_union, in_singleton in Hls.
    destruct Hls as [Hls | ->].
    + destruct (IHHrecord Hls) as (E & He & Hl).
      exists E. split; [now apply rh_andl | exact Hl].
    + exists D. split; [apply rh_andr, rh_one | congruence].
Qed.

Local Lemma typed_defs_yield_record mode G Go e ds T :
  @ty_defs mode G Go e ds T ->
  record_type T.
Proof.
  induction 1.
  - destruct (typed_def_declares_record_member H) as [HD _].
    exists (\{label_of D}). now apply rt_one.
  - destruct IHty_defs as [ls Hrec].
    destruct (typed_def_declares_record_member H0) as [HD Hlabel].
    exists (ls \u \{label_of D}). apply rt_cons; try assumption; try reflexivity.
    intro Hls.
    destruct (record_label_has_member Hrec Hls) as (E & He & Hel).
    destruct (typed_defs_record_member_lookup H He) as (d0 & Hlookup & Hdef).
    pose proof (typed_def_declares_record_member Hdef) as [_ Hlab0].
    unfold defs_has, defs_hasnt in *. congruence.
Qed.

Local Lemma type_equivalence_transitive e S T :
  @tyq_typ e S T ->
  forall U, @tyq_typ e T U -> @tyq_typ e S U.
Proof.
  induction 1; intros V HV; try solve [exact HV].
  all: repeat match goal with
    | H : typ_andor ?F |- _ => is_var F; destruct H
    end.
  all: inversion HV; subst; clear HV.
  all: repeat match goal with
    | H : typ_andor ?F |- _ => is_var F; destruct H; simpl in *
    | H : typ_nulary (typ_rcd _) |- _ => inversion H
    | H : typ_nulary (typ_and _ _) |- _ => inversion H
    | H : typ_nulary (typ_or _ _) |- _ => inversion H
    | H : typ_nulary (typ_sel _ _ _) |- _ => inversion H
    | H : typ_nulary (typ_bnd _) |- _ => inversion H
    | H : typ_nulary (typ_fun _ _) |- _ => inversion H
    end.
  all: repeat match goal with H : _ = _ |- _ => progress (inversion H; subst; try clear H) end.
  all: try discriminate.
  all: unfold typing_equiv in *.
  all: try first
    [ solve [eapply (@tyq_typ_andor typ_and); [constructor | |]; unfold typing_equiv; eauto]
    | solve [eapply (@tyq_typ_andor typ_or); [constructor | |]; unfold typing_equiv; eauto]
    | solve [apply tyq_typ_fun; unfold typing_equiv; eauto]
    | solve [apply tyq_typ_fld; unfold typing_equiv; eauto]
    | solve [apply tyq_typ_typ; unfold typing_equiv; eauto]
    | solve [apply tyq_typ_bnd; unfold typing_equiv; eauto]
    | solve [apply tyq_typ_met; unfold typing_equiv; eauto]
    | solve [apply tyq_typ_sel_normal; unfold typing_equiv; eauto using tyq_var_trans] ].
  eapply tyq_typ_sel_normal. eapply tyq_var_trans; eassumption.
Qed.

Local Lemma record_member_independent R D :
  record_has R D ->
  typ_indep_b 0 R ->
  typ_indep_b 0 (typ_rcd D).
Proof.
  induction 1; intro HR; [exact HR | |];
    inversion HR; subst;
    try match goal with H : typ_nulary (typ_and _ _) |- _ => inversion H end;
    eauto.
Qed.

Local Lemma location_alias_has_type mode G e w y T :
  mode_has_sef mode ->
  mode_has_mutability mode ->
  ctx_ok G ->
  @renv_corr mode G e ->
  binds w y e ->
  @ty_var mode G objctx_empty e w T ->
  @ty_var mode G objctx_empty e y T.
Proof.
  intros Hsef Hmutable Hok Hcorr Hbind Hty.
  destruct (reference_location_have_same_record Hmutable Hok Hcorr Hbind)
    as (R & B & Hw & Hy).
  eapply (@alias_variable_type_exact mode G e w T Hty G e y).
  - destruct mode; discriminate || reflexivity.
  - intros x V H; exact H.
  - intros x l H; exact H.
  - now apply tyq_var_binds.
  - intros V HV. rewrite (ctx_binding_unique HV Hw).
    apply ty_var_and.
    + eapply ty_var_sub; [apply ty_var_var; exact Hy | apply subtyp_and11].
    + eapply ty_var_sub.
      * eapply ty_var_sub; [apply ty_var_var; exact Hy | apply subtyp_and12].
      * apply subtyp_typ; intro z; [apply subtyp_refl | apply subtyp_bot].
Qed.


Local Lemma literal_self_context_narrows mode G H E w R :
  @context_narrows mode E G H ->
  ctx_vis H w ->
  @ty_var mode H objctx_empty E w (open w R) ->
  @context_narrows mode E (G § w / v_self ~ open w R) H.
Proof.
  intros [Htypes Hvis] Hw HV. split.
  - intros x T Hb. inversion Hb; subst; auto.
  - intros x Hv. apply visible_in_pushed_context in Hv as [-> | Hv]; auto.
Qed.

Local Lemma literal_method_context_narrows mode G H E w y Shape z r C1 Z1 C2 Z2 :
  mode_has_mutability mode ->
  @context_narrows mode E (G § w / v_self ~ open w Shape) H ->
  @tyq_typ E (open y Shape) (open w Shape) ->
  @tyq_typ E Z2 Z1 ->
  @tyq_typ E (open z C2) (open z C1) ->
  z §# H -> r §# H -> r <> z ->
  @context_narrows mode E (ctx_obj_met mode G (objctx_lit w Shape) z Z1 r C1)
    (ctx_obj_met mode H (objctx_heap y Shape) z Z2 r C2).
Proof.
  intros Hmutable Hbase Hself Harg Hrecv Hz Hr Hneq.
  assert (Hmode : mode_has_visibility mode) by now apply mode_has_hidden_method_bodies.
  split.
  - unfold ctx_obj_met. rewrite Hmode. simpl.
    apply include_context_types_narrow_top.
    + simpl. apply notin_union. split; [now apply notin_singleton | exact Hr].
    + apply include_context_types_narrow_top; [exact Hz | | now apply subtyp_tyq].
      exact (proj1 (context_narrows_hide Hbase)).
    + apply subtyp_and2.
      * eapply subtyp_trans; [apply subtyp_and11 | now apply subtyp_tyq].
      * eapply subtyp_trans; [apply subtyp_and12 |].
        apply subtyp_and2; [|apply subtyp_and12].
        eapply subtyp_trans; [apply subtyp_and11 | now apply subtyp_tyq].
  - intros x Hv.
    destruct (@visible_method_variable mode G (objctx_lit w Shape) z r Z1 C1 x Hmode Hv)
      as [-> | ->]; unfold ctx_obj_met; rewrite Hmode; simpl.
    + apply ctx_vis_n; [congruence | constructor].
    + constructor.
Qed.

Local Lemma equivalent_method_parts e m C1 Z1 R1 C2 Z2 R2 :
  @tyq_typ e (typ_rcd (dec_met m C1 Z1 R1)) (typ_rcd (dec_met m C2 Z2 R2)) ->
  @tyq_typ e Z1 Z2 /\
  (forall z, @tyq_typ e (open z C1) (open z C2)) /\
  (forall z r, @tyq_typ e (open_met z r R1) (open_met z r R2)).
Proof.
  inversion 1; subst.
  all: try solve [match goal with H : typ_nulary _ |- _ => inversion H end].
  all: try solve [match goal with H : typ_andor _ |- _ => inversion H; subst; discriminate end].
  unfold typing_equiv in *. auto.
Qed.

Local Lemma literal_method_definition_to_heap mode G e H E w y Shape m body C1 Z1 R1 C2 Z2 R2 :
  mode_has_mutability mode ->
  @context_narrows mode E (G § w / v_self ~ open w Shape) H ->
  env_binds_more e E ->
  @tyq_typ E (open y Shape) (open w Shape) ->
  @tyq_typ E (typ_rcd (dec_met m C1 Z1 R1)) (typ_rcd (dec_met m C2 Z2 R2)) ->
  @ty_def mode G (objctx_lit w Shape) e (def_met m body) (dec_met m C1 Z1 R1) ->
  @ty_def mode H (objctx_heap y Shape) E (def_met m body) (dec_met m C2 Z2 R2).
Proof.
  intros Hmutable Hbase Henv Hself Hsig Hmethod.
  destruct (equivalent_method_parts Hsig) as [HZ [HC HR]].
  assert (Hbody : exists L, forall z, z \notin L -> forall r, r <> z -> r \notin L ->
    @ty_trm mode (ctx_obj_met mode G (objctx_lit w Shape) z Z1 r C1) objctx_empty e
      (open_met z r body) (open_met z r R1)).
  { inversion Hmethod; subst. eexists. eassumption. }
  destruct Hbody as [L Hbody].
  apply ty_def_met with (L := L \u ctx_dom H).
  intros z Hz r Hneq Hr.
  apply notin_union in Hz as [HzL HzH]. apply notin_union in Hr as [HrL HrH].
  eapply ty_trm_sub with (T := open_met z r R1).
  - eapply (proj1 (term_judgments_narrow mode)); [exact (Hbody z HzL r Hneq HrL) | | exact I | exact Henv].
    eapply literal_method_context_narrows; try eassumption.
    + now apply type_equivalence_symmetric.
    + apply type_equivalence_symmetric, HC.
  - apply subtyp_tyq, HR.
Qed.

Local Lemma equivalent_type_member_upper e A S1 T1 S2 T2 :
  @tyq_typ e (typ_rcd (dec_typ A S1 T1)) (typ_rcd (dec_typ A S2 T2)) ->
  forall u, @tyq_typ e (open u T1) (open u T2).
Proof.
  inversion 1; subst.
  all: try solve [match goal with H : typ_nulary _ |- _ => inversion H end].
  all: try solve [match goal with H : typ_andor _ |- _ => inversion H; subst; discriminate end].
  unfold typing_equiv in *. auto.
Qed.

Local Lemma equivalent_field_upper e a S1 T1 S2 T2 :
  @tyq_typ e (typ_rcd (dec_fld a S1 T1)) (typ_rcd (dec_fld a S2 T2)) ->
  @tyq_typ e T1 T2.
Proof.
  inversion 1; subst.
  all: try solve [match goal with H : typ_nulary _ |- _ => inversion H end].
  all: try solve [match goal with H : typ_andor _ |- _ => inversion H; subst; discriminate end].
  unfold typing_equiv in *. assumption.
Qed.

Local Lemma typed_literal_type_member_is_exact mode G Go e d w A S T :
  w \notin fv S -> w \notin fv T ->
  @ty_def mode G Go e d (open w (dec_typ A S T)) ->
  S = T.
Proof.
  intros HS HT Hd.
  apply ((proj1 type_opening_injective_when_fresh) S 1 w T HS HT).
  inversion Hd. assumption.
Qed.

Local Lemma typed_literal_field_is_exact mode G Go e d w a S T :
  w \notin fv S -> w \notin fv T ->
  @ty_def mode G Go e d (open w (dec_fld a S T)) ->
  S = T.
Proof.
  intros HS HT Hd.
  apply ((proj1 type_opening_injective_when_fresh) S 0 w T HS HT).
  inversion Hd. assumption.
Qed.

Local Definition field_initializer mode H E d stored D :=
  forall a loc T,
    stored = def_fld a (avar_f loc) ->
    D = dec_fld a T T ->
    exists v, tfree_def v d /\ binds v loc E /\ @ty_var mode H objctx_empty E v T.

Local Lemma literal_definition_to_heap mode G e H E w y Shape d D :
  mode_has_sef mode ->
  mode_has_mutability mode ->
  @context_narrows mode E (G § w / v_self ~ open w Shape) H ->
  env_binds_more e E ->
  ctx_ok H ->
  ok E ->
  @renv_corr mode H E ->
  env_targets_are_locations E ->
  @tyq_var E w y ->
  typ_indep_b 0 Shape ->
  typ_indep_b 0 (typ_rcd D) ->
  w \notin fv D ->
  (forall v, tfree_def v d -> v \in dom E) ->
  @ty_def mode G (objctx_lit w Shape) e d (open w D) ->
  @ty_def mode H (objctx_heap y Shape) E (deref_def E d) (open y D) /\
  def_varkinds H (deref_def E d) /\
  @field_initializer mode H E d (deref_def E d) (open y D).
Proof.
  intros Hsef Hmutable Hbase Henv Hok HE Hcorr Htargets Heq HInd HMem Hfresh Hrefs Hd.
  assert (Hsig : @tyq_typ E (typ_rcd (open w D)) (typ_rcd (open y D)))
    by exact (aliased_open_type Heq HMem).
  destruct D as [A S T | a S T | m C Z R].
  - cbn [fv DecFreeVar fv_dec] in Hfresh. apply notin_union in Hfresh as [HS HT].
    pose proof (typed_literal_type_member_is_exact HS HT Hd) as ->.
    destruct d as [A0 AType|a0 av|m0 body]; try (inversion Hd; fail).
    inversion Hd; subst. simpl in *.
    split.
    + eapply ty_def_typ with (L := L).
      intros u Hu. eapply type_equivalence_transitive.
      * eapply typ_equivalence_extend; [ |exact Henv].
        unfold typing_equiv in *. eauto.
      * eapply equivalent_type_member_upper. exact Hsig.
    + split; [constructor |]. intros l loc U Hbad. discriminate.
  - cbn [fv DecFreeVar fv_dec] in Hfresh. apply notin_union in Hfresh as [HS HT].
    pose proof (typed_literal_field_is_exact HS HT Hd) as ->.
    destruct d as [A0 AType|a0 av|m0 body]; try (inversion Hd; fail).
    inversion Hd; subst. simpl in *.
    match goal with Hsrc : obj_typing _ _ _ ?src _ |- _ =>
      assert (Hmem : src \in dom E) by (apply Hrefs; constructor);
      destruct (get_some Hmem) as [loc Hbind];
      assert (HsrcT : @ty_var mode H objctx_empty E src (open y T))
    end.
    { eapply ty_var_sub with (T := open w T).
      - eapply type_binding_narrows; try (exact (proj1 Hbase) || exact Henv); eassumption.
      - apply subtyp_tyq. eapply equivalent_field_upper. exact Hsig. }
    rewrite (@deref_avar_lookup E t HE Htargets), Hbind.
    destruct (reference_location_kind Hmutable Hok Hcorr Hbind) as (P & B & H0 & _ & Hloc).
    split.
    + apply ty_def_fld.
      * intros _. exact (kind_binding_visible Hloc).
      * eapply location_alias_has_type; eassumption.
    + split.
      * apply def_varkinds_fld. unfold ctx_k. eexists _, _. exact Hloc.
      * intros a' loc' T' HeqF HeqT. inversion HeqF; inversion HeqT; subst.
        eexists. split; [constructor |]. split; eassumption.
  - destruct d as [A0 AType|a0 av|m0 body]; try (inversion Hd; fail).
    inversion Hd; subst. simpl in *.
    split.
    + eapply literal_method_definition_to_heap; try eassumption.
      apply aliased_open_type; [now apply tyq_var_sym | exact HInd].
    + split.
      * apply def_varkinds_met. intros v Hv. exfalso.
        eapply typed_method_has_no_free_term_variables;
          [exact (mode_has_hidden_method_bodies mode Hmutable) | exact Hd | exact Hv].
      * intros l loc U Hbad. discriminate.
Qed.

Local Lemma dereferenced_definition_label E d :
  label_of (deref_def E d) = label_of d.
Proof. destruct d; reflexivity. Qed.

Local Lemma dereferenced_definitions_lookup E ds l :
  get_def l (deref_defs E ds) = option_map (deref_def E) (get_def l ds).
Proof.
  induction ds; simpl; [reflexivity |].
  rewrite dereferenced_definition_label. case_if; auto.
Qed.

Local Lemma dereferenced_definitions_keep_absent_labels E ds l :
  defs_hasnt ds l -> defs_hasnt (deref_defs E ds) l.
Proof. unfold defs_hasnt. intro H. now rewrite dereferenced_definitions_lookup, H. Qed.

Local Definition field_initializers mode H E (ds stored : defs) T :=
  forall a loc F,
    defs_has stored (def_fld a (avar_f loc)) ->
    record_has T (dec_fld a F F) ->
    exists v, tfree_defs v ds /\ binds v loc E /\ @ty_var mode H objctx_empty E v F.

Local Lemma literal_definitions_to_heap mode G e H E w y Shape S ls ds :
  mode_has_sef mode ->
  mode_has_mutability mode ->
  @context_narrows mode E (G § w / v_self ~ open w Shape) H ->
  env_binds_more e E ->
  ctx_ok H ->
  ok E ->
  @renv_corr mode H E ->
  env_targets_are_locations E ->
  @tyq_var E w y ->
  typ_indep_b 0 Shape ->
  record_typ S ls ->
  typ_indep_b 0 S ->
  w \notin fv S ->
  (forall v, tfree_defs v ds -> v \in dom E) ->
  @ty_defs mode G (objctx_lit w Shape) e ds (open w S) ->
  @ty_defs mode H (objctx_heap y Shape) E (deref_defs E ds) (open y S) /\
  defs_varkinds H (deref_defs E ds) /\
  @field_initializers mode H E ds (deref_defs E ds) (open y S).
Proof.
  intros Hsef Hmutable Hbase Henv Hok HE Hcorr Htargets Halias Hshape Hrecord.
  revert ds. induction Hrecord as [D l HD Hl | S ls D l Hrec IH HD Hl Hnot];
    intros ds Hind Hfresh Hrefs Htyped; simpl in *.
  - inversion Htyped; subst.
    match goal with Hd : obj_dec_typing _ _ _ ?d (open_rec_dec 0 w D) |- _ =>
      assert (Hdrefs : forall v, tfree_def v d -> v \in dom E)
        by (intros x Hx; apply Hrefs; now apply tfree_defs_cons_r);
      destruct (@literal_definition_to_heap mode G e H E w y Shape d D
        Hsef Hmutable Hbase Henv Hok HE Hcorr Htargets Halias Hshape Hind Hfresh Hdrefs Hd)
        as (Hdty & Hdk & Hdsrc)
    end.
    split; [now apply ty_defs_one |]. split; [apply defs_varkinds_cons; [constructor | exact Hdk] |].
    intros a loc T Hfield Hdecl.
    assert (Hf : deref_def E d = def_fld a (avar_f loc)).
    { unfold defs_has in Hfield. simpl in Hfield. case_if; congruence. }
    assert (Ht : open y D = dec_fld a T T).
    { change (open_rec_dec 0 y D = dec_fld a T T). now inversion Hdecl. }
    destruct (Hdsrc _ _ _ Hf Ht) as (v & Hv & Hbind & Hty).
    exists v. split; [now apply tfree_defs_cons_r | now split].
  - inversion Htyped; subst.
    apply notin_union in Hfresh as [HsFresh HdFresh].
    assert (HsInd : typ_indep_b 0 S) by (
      inversion Hind; subst; try assumption;
      match goal with H : typ_nulary (typ_and _ _) |- _ => inversion H end).
    assert (HdInd : typ_indep_b 0 (typ_rcd D)).
    { eapply record_member_independent; [apply rh_andr, rh_one | exact Hind]. }
    match goal with Hs : obj_typing _ _ _ ?s (open_rec_typ 0 w S),
        Hd : obj_dec_typing _ _ _ ?d (open_rec_dec 0 w D) |- _ =>
      assert (HSrefs : forall v, tfree_defs v s -> v \in dom E)
        by (intros x Hx; apply Hrefs; now apply tfree_defs_cons_l);
      assert (HDrefs : forall v, tfree_def v d -> v \in dom E)
        by (intros x Hx; apply Hrefs; now apply tfree_defs_cons_r);
      destruct (IH s HsInd HsFresh HSrefs Hs) as (Hsty & Hsk & Hssrc);
      destruct (@literal_definition_to_heap mode G e H E w y Shape d D
        Hsef Hmutable Hbase Henv Hok HE Hcorr Htargets Halias Hshape HdInd HdFresh HDrefs Hd)
        as (Hdty & Hdk & Hdsrc)
    end.
    assert (Hnew : @ty_defs mode H (objctx_heap y Shape) E
      (deref_defs E (defs_cons ds0 d)) (open y (typ_and S (typ_rcd D)))).
    { apply ty_defs_cons; try assumption.
      rewrite dereferenced_definition_label. eapply dereferenced_definitions_keep_absent_labels; eassumption. }
    split; [exact Hnew |].
    split; [now apply defs_varkinds_cons |].
    intros a loc T Hfield Hdecl.
    unfold defs_has in Hfield. simpl in Hfield.
    destruct (classic (label_of (deref_def E d) = label_fld a)) as [Hlabel|Hlabel].
    + assert (Hnewd : deref_def E d = def_fld a (avar_f loc)) by (case_if; congruence).
      destruct (typed_defs_yield_record Hnew) as [labels Htyp].
      assert (HlabelD : label_of (open y D) = label_of (dec_fld a T T)).
      { destruct (typed_def_declares_record_member Hdty) as [_ Hlab].
        rewrite <- Hlab, Hnewd. reflexivity. }
      assert (HeqD : open y D = dec_fld a T T).
      { eapply record_member_unique_by_label; [exact Htyp | apply rh_andr, rh_one | exact Hdecl | exact HlabelD]. }
      destruct (Hdsrc _ _ _ Hnewd HeqD) as (v & Hfree & Hbind & Htype).
      exists v. split; [now apply tfree_defs_cons_r | now split].
    + assert (Htail : defs_has (deref_defs E ds0) (def_fld a (avar_f loc))) by (unfold defs_has; simpl; case_if; congruence).
      assert (Hdecl' : record_has (open y S) (dec_fld a T T)).
      { inversion Hdecl; subst; [assumption |].
        match goal with H : record_has (typ_rcd _) _ |- _ => inversion H; subst end.
        destruct (typed_def_declares_record_member Hdty) as [_ Hlab].
        exfalso. apply Hlabel. change (label_of (open_rec_dec 0 y D)) with (label_of (open y D)). rewrite Hlab. change (label_of (open_rec_dec 0 y D) = label_fld a). now rewrite H3. }
      destruct (Hssrc _ _ _ Htail Hdecl') as (v & Hfree & Hbind & Htype).
      exists v. split; [now apply tfree_defs_cons_l | now split].
Qed.

Local Lemma inert_context_keys mode G :
  @inert mode G -> ctx_dom G = ctx_kdom v_loc G \u ctx_kdom v_ref G.
Proof.
  induction 1 as [|G x k T HG IH Hk HT Hdom Hfv HTfv].
  - simpl. now rewrite union_empty_r.
  - destruct Hk; simpl; repeat case_if; try congruence;
      rewrite IH; apply fset_extens; intros v Hv; repeat rewrite in_union in *; tauto.
Qed.

Local Lemma context_extension_by_two_fresh_bindings mode E G x y k l S T :
  x §# G -> y §# (G § x / k ~ S) ->
  @context_narrows mode E G (G § x / k ~ S § y / l ~ T).
Proof.
  intros Hx Hy.
  destruct (@fresh_context_push_narrows mode E G x k S Hx) as [_ Hv1].
  destruct (@fresh_context_push_narrows mode E (G § x / k ~ S) y l T Hy)
    as [_ Hv2].
  split.
  - intros z U Hb. apply ty_var_var.
    exact (@binds_preserved_by_fresh_push (G § x / k ~ S) y l T Hy z U
      (@binds_preserved_by_fresh_push G x k S Hx z U Hb)).
  - auto.
Qed.

Local Lemma literal_object_view mode G e R ds t U :
  @ty_trm mode G objctx_empty e (trm_lit (lit_obj R ds) t) U ->
  exists Ld Lt V,
    (forall x, x \notin Ld ->
      @ty_defs mode G (objctx_lit x R) e (open x ds) (open x R)) /\
    typ_indep_b 0 R /\
    (forall x, x \notin Lt ->
      @ty_trm mode (G § x / v_let ~ typ_objlit mode R) objctx_empty e (open x t) V) /\
    @subtyp mode G objctx_empty e V U.
Proof.
  intro Hty. remember (trm_lit (lit_obj R ds) t) as all eqn:Heq in Hty.
  induction Hty; inversion Heq; subst; try clear Heq.
  - match goal with H : typing _ _ (lit_obj _ _) _ |- _ => inversion H; subst end.
    do 3 eexists. split; [eassumption |]. split; [assumption |].
    split; [eassumption | apply subtyp_refl].
  - destruct (IHHty eq_refl) as (Ld & Lt & V & Hd & HI & Ht & Hup).
    exists Ld, Lt, V. repeat split; try assumption.
    eapply subtyp_trans; eassumption.
Qed.

Local Lemma literal_function_impossible mode G e S body t U :
  mode_has_mutability mode ->
  @ty_trm mode G objctx_empty e (trm_lit (lit_fun S body) t) U -> False.
Proof.
  intros Hmut Hty. remember (trm_lit (lit_fun S body) t) as all eqn:Heq in Hty.
  induction Hty; inversion Heq; subst; eauto.
  match goal with H : typing _ _ (lit_fun _ _) _ |- _ => inversion H; subst end.
  destruct mode; discriminate.
Qed.

Local Lemma typed_extended_literal_object mode G h e R ds t st U y w L :
  let c := (trm_lit (lit_obj R ds) t ; st ; h ; e ; L) in
  let T := typ_and (typ_bnd R) (typ_mut_marker typ_bot) in
  let H := G § y / v_loc ~ T § w / v_ref ~ T in
  let E := e & w ~ y in
  let stored := deref_defs E (open w ds) in
  let d := (open w t ; st ; h & y ~ item_obj stored ; E ; fv_config c) in
  mode_has_sef mode -> mode_has_mutability mode ->
  @runtime_typechecks mode G c U ->
  config_has_scoped_locations c ->
  fresh_in_config (y :: w :: nil) c ->
  y \notin ctx_fv G -> w \notin ctx_fv G ->
  @runtime_typechecks mode H d U /\
  @field_initializers mode H E (open w ds) stored (open y R) /\
  preserves_ctx_binds G H /\ env_binds_more e E.
Proof.
  cbv beta zeta.
  intros Hsef Hmut (HI & HH & S & Hty & Hst) Hscope Hfresh HyG HwG.
  cbn [config_env config_heap config_trm config_stack] in *.
  set (T := typ_and (typ_bnd R) (typ_mut_marker typ_bot)).
  set (G0 := G § y / v_loc ~ T).
  set (G1 := G0 § w / v_ref ~ T).
  set (E := e & w ~ y).
  set (stored := deref_defs E (open w ds)).
  destruct Hfresh as [Hy [Hw _]].
  cbn [fv TrmFreeVar fv_trm fv_lit] in Hy, Hw.
  repeat rewrite notin_union in Hy. repeat rewrite notin_union in Hw.
  assert (Hyh : y # h) by tauto.
  assert (Hye : y # e) by tauto.
  assert (Hwe : w # e) by tauto.
  assert (Hwv : w \notin fv_env e) by tauto.
  assert (Hwh : w # h) by tauto.
  assert (Hneq : w <> y) by (apply notin_singleton; tauto).
  assert (HyR : y \notin fv R) by tauto.
  assert (HwR : w \notin fv R) by tauto.
  assert (Hwds : w \notin fv ds) by tauto.
  clear Hy Hw.
  destruct HH as (Hok & Hweak & Hheap & Henv & HkLoc & HkRef & Hcorr & Hitems).
  assert (Hyc : y §# G) by (rewrite (inert_context_keys HI), HkLoc, HkRef; now apply notin_union).
  assert (Hwc : w §# G) by (rewrite (inert_context_keys HI), HkLoc, HkRef; apply notin_union; tauto).
  assert (Hwc0 : w §# G0) by (unfold G0; simpl; apply notin_union; split; [now apply notin_singleton | exact Hwc]).
  assert (Hwyfv : w \notin ctx_fv G0) by
    (unfold G0, T; simpl; repeat rewrite notin_union; auto using notin_empty).
  assert (Hyt : y \notin fv T) by (unfold T; simpl; repeat rewrite notin_union; auto using notin_empty).
  assert (Hwt : w \notin fv T) by (unfold T; simpl; repeat rewrite notin_union; auto using notin_empty).
  assert (Hkeep : preserves_ctx_binds G G1).
  { intros x A Hb. exact (@binds_preserved_by_fresh_push G0 w v_ref T Hwc0 x A
      (@binds_preserved_by_fresh_push G y v_loc T Hyc x A Hb)). }
  assert (Henvmore : env_binds_more e E).
  { intros x l Hb. apply binds_push_neq; [exact Hb |].
    intros ->. apply Hwe. exact (get_some_inv Hb). }
  pose proof (@context_extension_by_two_fresh_bindings mode E G y w v_loc v_ref T T Hyc Hwc0) as Hext.
  assert (Hok1 : ctx_ok G1) by (unfold G1, G0; apply ctx_ok_push; [now apply ctx_ok_push | exact Hwc0]).
  assert (HokE : ok E) by now apply ok_push.
  assert (Htycorr : @typ_corr mode T T).
  { unfold T. apply typ_corr_obj. destruct mode; cbn; try discriminate; eauto. }
  assert (HCorr1 : @renv_corr mode G1 E).
  { eapply renv_corr_ref; [apply ctx_binds_k_e | | exact Htycorr |].
    - unfold G0. apply ctx_binds_k_e.
    - unfold G1, G0. apply fresh_push_renv_corresponds; [exact Hwc0 | now apply fresh_push_renv_corresponds]. }
  assert (Htargets : env_targets_are_locations E).
  { apply env_location_targets_push; try assumption; [|congruence].
    exact (scoped_locations_env_targets Hscope). }
  destruct (literal_object_view Hty) as (Ld & Lt & V & Hd & Hind & Ht & Hsub).
  assert (Hdefs : @ty_defs mode G (objctx_lit w R) e (open w ds) (open w R))
    by (eapply opened_literal_definitions_at_fresh_name; eauto).
  destruct (typed_defs_yield_record Hdefs) as (ls & Hls).
  pose proof (@opened_record_typ_before_fresh_opening R w ls HwR Hls) as HR.
  assert (Hrt : record_type R) by now exists ls.
  assert (Hcaps : mode_refcaps' mode = mode_refcaps_mutability)
    by (destruct mode; discriminate || reflexivity).
  assert (HI1 : @inert mode G1).
  { unfold G1, G0. apply inert_push; try assumption.
    - apply inert_push; try assumption.
      + constructor.
      + unfold T. apply inert_typ_obj; try assumption.
        unfold refcap_inert_type. rewrite Hcaps. constructor.
    - constructor.
    - unfold T. apply inert_typ_obj; try assumption.
      unfold refcap_inert_type. rewrite Hcaps. constructor. }
  assert (Hwty : @ty_var mode G1 objctx_empty E w T)
    by (apply ty_var_var; constructor).
  assert (Hself : @context_narrows mode E (G § w / v_self ~ open w R) G1).
  { apply literal_self_context_narrows; [exact Hext | constructor |].
    apply ty_rec_elim; [|exact Hind]. unfold T in Hwty. eapply ty_var_sub; [exact Hwty | apply subtyp_and11]. }
  assert (HopenRefs : forall x, tfree_defs x (open w ds) -> x \in dom E).
  { intros x Hx. apply (proj2 (proj2 (proj2 tfree_open_backward))) in Hx as [-> | Hx].
    - unfold E; rewrite dom_push, in_union. left. apply in_singleton_self.
    - unfold E; rewrite dom_push, in_union. right.
      destruct Hscope as (_ & _ & Htr & _).
      apply Htr. apply tfree_trm_lit_l, tfree_lit_obj. exact Hx. }
  destruct (@literal_definitions_to_heap mode G e G1 E w y R R ls (open w ds)
    Hsef Hmut Hself Henvmore Hok1 HokE HCorr1 Htargets
    (tyq_var_binds (binds_push_eq (A:=var) w y e)) Hind HR Hind HwR HopenRefs Hdefs)
    as (Hstored & Hvks & Hsrc).
  split; [|now split].
  split; [exact HI1 |]. split.
  - repeat split; try assumption.
    + unfold G1, G0. now do 2 apply ctx_weakens_push.
    + now apply ok_push.
    + unfold G1, G0. simpl. repeat case_if; try congruence; now rewrite dom_push, HkLoc.
    + unfold G1, G0, E. simpl. repeat case_if; try congruence; now rewrite dom_push, HkRef.
    + intros x Hx. cbn [config_heap] in Hx. rewrite dom_push, in_union, in_singleton in Hx. destruct Hx as [-> | Hx].
      * eapply ty_item_obj_s with (U := R) (S := typ_mut_marker typ_bot).
        -- apply ctx_binds_n; [congruence | constructor].
        -- apply binds_push_eq.
        -- reflexivity.
        -- exact Hstored.
        -- exact Hvks.
      * assert (Hxy : x <> y) by (intros ->; contradiction).
        specialize (Hitems x Hx). inversion Hitems; subst.
        -- destruct mode; discriminate.
        -- eapply ty_item_obj_s with (U := U0) (S := S0).
           ++ eapply Hkeep; eassumption.
           ++ cbn [config_heap]; apply binds_push_neq; [eassumption | assumption].
           ++ reflexivity.
           ++ eapply (proj2 (proj2 (proj2 (term_judgments_narrow mode)))); eassumption || exact I.
           ++ apply fresh_push_defs_varkinds; [exact Hwc0 | now apply fresh_push_defs_varkinds].
  - exists S. split; [|eapply stack_typing_narrows; eassumption].
    assert (HT : typ_objlit mode R = T) by (unfold T; destruct mode; discriminate || reflexivity).
    eapply ty_trm_sub with (T := V).
    + eapply renamed_let_body with (A := T) (L := Lt \u ctx_dom G1).
      * exact Hmut.
      * exact Hwty.
      * constructor.
      * intros x Hx. apply notin_union in Hx as [HxL HxG].
        eapply (proj1 (term_judgments_narrow mode)).
        -- specialize (Ht x HxL). rewrite HT in Ht. exact Ht.
        -- now apply context_narrows_push.
        -- exact I.
        -- exact Henvmore.
    + exact (@subtype_narrows mode G G1 e E V S Hext Henvmore Hsub).
Qed.

Local Definition vars_avoid (A B : vars) :=
  forall x, x \in A -> x \notin B.

Local Lemma vars_avoid_sym A B :
  vars_avoid A B -> vars_avoid B A.
Proof. unfold vars_avoid. firstorder. Qed.

Local Lemma vars_avoid_union A B C :
  vars_avoid (A \u B) C <-> vars_avoid A C /\ vars_avoid B C.
Proof. unfold vars_avoid. setoid_rewrite in_union. firstorder. Qed.

Local Definition avoid_variables (V : vars) (p x : var) :=
  If x \in V then p else x.

Local Lemma avoiding_variables_stay_outside V p :
  p \notin V -> forall x, avoid_variables V p x \notin V.
Proof. unfold avoid_variables. intros Hp x. case_if; assumption. Qed.

Local Lemma avoiding_variables_fix V p x :
  x \notin V -> avoid_variables V p x = x.
Proof. unfold avoid_variables. intro H. case_if; congruence. Qed.

Local Lemma avoiding_variables_have_finite_support V p :
  renaming_fixes_outside (avoid_variables V p) (V \u \{p}).
Proof.
  intros x Hx. rewrite notin_union, notin_singleton in Hx.
  destruct Hx as [Hx Hp]. intro y. unfold avoid_variables. case_if; intuition congruence.
Qed.

Local Lemma renamed_avar_fv_in_image f a x :
  x \in fv (rename_avar f a) -> exists y, y \in fv a /\ f y = x.
Proof.
  destruct a; simpl; intro H; [contradiction (notin_empty H) |].
  rewrite in_singleton in H. subst. eexists; split; [apply in_singleton_self | reflexivity].
Qed.

Local Lemma renamed_type_fv_in_image f :
  (forall T x, x \in fv (rename_typ f T) -> exists y, y \in fv T /\ f y = x) /\
  (forall D x, x \in fv (rename_dec f D) -> exists y, y \in fv D /\ f y = x).
Proof.
  apply typ_mutind; intros; simpl in *.
  all: try solve [exfalso; eapply notin_empty; eassumption].
  all: try solve [eauto].
  all: repeat rewrite in_union in *; setoid_rewrite in_union.
  all: eauto using renamed_avar_fv_in_image, in_union.
  all: firstorder using renamed_avar_fv_in_image.
  all: try solve [match goal with H : _ \in fv (rename_avar _ _) |- _ =>
    destruct (@renamed_avar_fv_in_image _ _ _ H) as (y & Hy & He); exists y; tauto end].
  all: try setoid_rewrite in_union; firstorder.
Qed.

Local Lemma renamed_types_avoid_variables f V T :
  (forall x, f x \notin V) ->
  vars_avoid (fv (rename_typ f T)) V.
Proof.
  intros Hf x Hx. destruct (proj1 (renamed_type_fv_in_image f) _ _ Hx) as (y & _ & <-).
  apply Hf.
Qed.

Local Lemma avoiding_variables_respects_env V p e :
  vars_avoid (fv_renv e) V ->
  renaming_respects_env (avoid_variables V p) e e.
Proof.
  intros HA x y Hxy. rewrite !avoiding_variables_fix; [now apply tyq_var_binds | |].
  - apply HA. rewrite in_union. right. eapply (@fv_of_binding_is_env_fv var fv e y x y);
      [exact Hxy | apply in_singleton_self].
  - apply HA. rewrite in_union. left. exact (get_some_inv Hxy).
Qed.

Local Lemma avoiding_variables_respects_context mode V p G e :
  vars_avoid (ctx_dom G) V -> vars_avoid (ctx_fv G) V ->
  @renaming_respects_context mode (avoid_variables V p) G G e.
Proof.
  intros Hdom Hfv. split.
  - intros x T Hb. rewrite avoiding_variables_fix by (apply Hdom; exact (ctx_binding_in_dom Hb)).
    rewrite (proj1 (rename_typ_identity (avoid_variables V p)) T).
    + now apply ty_var_var.
    + intros v Hv. apply avoiding_variables_fix, Hfv. exact (ctx_binding_free_variables Hb Hv).
  - intros x Hx. rewrite avoiding_variables_fix; [exact Hx |].
    apply Hdom. now apply ctx_visible_in_dom.
Qed.

Local Lemma stack_typing_renames mode G e S st U :
  mode_has_mutability mode ->
  @ty_stack mode G e S st U ->
  forall f V G' e', renaming_fixes_outside f V ->
    renaming_respects_env f e e' ->
    @renaming_respects_context mode f G G' e' ->
    @ty_stack mode G' e' (rename_typ f S) (rename_stack f st) (rename_typ f U).
Proof.
  intros Hmut Hst.
  induction Hst as [G e S U Hsub | L G e st t S W U Hst IH Hframe].
  - intros f V G' e' Hfinite Henv Hctx. simpl. apply ty_stack_nil.
    exact (proj1 (proj2 (@variable_judgments_rename mode Hmut)) _ _ _ _ _
      Hsub f V G' e' Hfinite Henv (proj1 Hctx)).
  - intros f V G' e' Hfinite Henv Hctx. simpl.
    apply ty_stack_let with (L := (L \u V) \u ctx_dom G') (T := rename_typ f W).
    + eapply IH; eassumption.
    + intros x Hx. repeat rewrite notin_union in Hx. destruct Hx as [[HxL HxV] HxG'].
      pose proof (@renaming_respects_context_push mode f G G' e' x v_let S
        (rename_typ f S) (Hfinite x HxV) HxG' eq_refl Hctx) as Hplus.
      pose proof (proj1 (@term_judgments_rename mode Hmut) _ _ _ _ _
        (Hframe x HxL) f V _ e' Hfinite Henv Hplus I) as Hout.
      rewrite (proj1 (rename_trm_open f)), (name_fixed_by_eq (Hfinite x HxV)) in Hout.
      exact Hout.
Qed.

Local Lemma step_config_free_variables_increase c d :
  c ↦ d -> fv_config c \c fv_config d.
Proof.
  intros Hred x Hx. destruct Hred; do 4 (rewrite in_union; right); exact Hx.
Qed.

Local Lemma trace_config_free_variables_increase c n d :
  c ⊣n↦* d -> fv_config c \c fv_config d.
Proof.
  induction 1 as [c | a b c k Hred IH Hstep]; intros x Hx; [exact Hx |].
  exact (step_config_free_variables_increase Hstep (IH x Hx)).
Qed.

Local Definition upcoming_names c final : vars :=
  fv_config final \- fv_config c.

Local Lemma current_names_avoid_upcoming c final :
  vars_avoid (fv_config c) (upcoming_names c final).
Proof. unfold vars_avoid, upcoming_names. intros x Hx Hfuture. rewrite in_remove in Hfuture. exact ((proj2 Hfuture) Hx). Qed.

Local Lemma upcoming_names_of_successor c d final :
  c ↦ d -> upcoming_names d final \c upcoming_names c final.
Proof.
  intros Hred x. unfold upcoming_names. rewrite !in_remove.
  intros [Hf Hd]. split; [exact Hf |].
  intro Hc. exact (Hd (step_config_free_variables_increase Hred Hc)).
Qed.

Local Lemma allocated_read_name_is_upcoming w a h e L loc r st n final :
  let c := (trm_read (avar_f w) a ; st ; h ; e ; L) in
  let d := (trm_var (avar_f r) ; st ; h ; e & r ~ loc ; fv_config c) in
  fresh_in_config (r :: nil) c ->
  d ⊣n↦* final ->
  r \in upcoming_names c final.
Proof.
  cbv beta zeta. intros [Hfresh _] Hred.
  unfold upcoming_names. rewrite in_remove. split; [|exact Hfresh].
  eapply trace_config_free_variables_increase; [exact Hred |].
  simpl. rewrite dom_push. repeat rewrite in_union. repeat rewrite in_singleton.
  tauto.
Qed.

Local Lemma allocated_object_names_are_upcoming R ds t st h e L y w n final :
  let c := (trm_lit (lit_obj R ds) t ; st ; h ; e ; L) in
  let d := (open w t ; st ; h & y ~ item_obj (deref_defs (e & w ~ y) (open w ds))
    ; e & w ~ y ; fv_config c) in
  fresh_in_config (y :: w :: nil) c ->
  d ⊣n↦* final ->
  y \in upcoming_names c final /\ w \in upcoming_names c final.
Proof.
  cbv beta zeta. intros [Hy [Hw _]] Hred.
  apply notin_union in Hw as [Hw _].
  unfold upcoming_names. rewrite !in_remove. split.
  - split; [|exact Hy]. eapply trace_config_free_variables_increase; [exact Hred |].
    simpl. rewrite !dom_push. repeat rewrite in_union. repeat rewrite in_singleton. tauto.
  - split; [|exact Hw]. eapply trace_config_free_variables_increase; [exact Hred |].
    simpl. rewrite !dom_push. repeat rewrite in_union. repeat rewrite in_singleton. tauto.
Qed.

Local Lemma heap_domain_extends_step c d :
  c ↦ d -> dom (config_heap c) \c dom (config_heap d).
Proof.
  intros Hred x Hx. destruct Hred; simpl in *; auto.
  - destruct H as (_ & _ & Hdom & _). now rewrite <- Hdom.
  - rewrite dom_push, in_union. now right.
  - rewrite dom_push, in_union. now right.
Qed.

Local Lemma typed_read_avoiding_future_names mode G e h w y ds a loc st L r V :
  let c := (trm_read (avar_f w) a ; st ; h ; e ; L) in
  let d := (trm_var (avar_f r) ; st ; h ; e & r ~ loc ; fv_config c) in
  mode_has_sef mode -> mode_has_mutability mode ->
  @runtime_typechecks mode G c typ_top ->
  binds w y e ->
  binds y (item_obj ds) h ->
  defs_has ds (def_fld a (avar_f loc)) ->
  fresh_in_config (r :: nil) c ->
  vars_avoid (ctx_fv G) V ->
  vars_avoid (fv_config c) V ->
  r \in V ->
  exists R B RO T,
    ctx_binds y (typ_and (typ_bnd RO) (typ_mut_marker typ_bot)) G /\
    record_has (open y RO) (dec_fld a T T) /\
    (let G' := G § r / v_ref ~ typ_and (typ_bnd R) (typ_mut_marker B) in
     let e' := e & r ~ loc in
     @runtime_typechecks mode G' d typ_top /\
     preserves_ctx_binds G G' /\ env_binds_more e e' /\
     vars_avoid (ctx_fv G') V /\
     (@reference_is_protected mode G e w \/
       (exists w0, @reference_is_protected mode G e w0 /\
         @ty_var mode G objctx_empty e w0 T) ->
       @reference_is_protected mode G' e' r)).
Proof.
  cbv beta zeta.
  intros Hsef Hmut (HI & HH & Actual & Hty & Hstack) Hw Hy Hfield Hfresh HavoidG HavoidC HrV.
  cbn [config_env config_heap config_trm config_stack] in *.
  destruct (typed_read_view Hty eq_refl) as (Sa & Ta & Result & Hview & Hadapt & Hup).
  assert (HavoidDom : vars_avoid (ctx_dom G) V).
  { rewrite (inert_context_keys HI).
    destruct HH as (_ & _ & _ & _ & Hdl & Hde & _).
    rewrite Hdl, Hde. intros z Hz. apply HavoidC.
    simpl. repeat rewrite in_union in *. tauto. }
  assert (HavoidE : vars_avoid (fv_renv e) V).
  { intros x Hx. apply HavoidC. simpl. repeat rewrite in_union in *. tauto. }
  assert (HavoidSt : vars_avoid (fv st) V).
  { intros x Hx. apply HavoidC. simpl. repeat rewrite in_union. tauto. }
  assert (HavoidW : w \notin V).
  { apply HavoidC. simpl. repeat rewrite in_union. repeat rewrite in_singleton. tauto. }
  destruct (var_fresh V) as [p Hp].
  set (f := avoid_variables V p).
  pose proof (@avoiding_variables_have_finite_support V p) as Hfin.
  pose proof (@avoiding_variables_respects_env V p e HavoidE) as HrenE.
  pose proof (@avoiding_variables_respects_context mode V p G e HavoidDom HavoidG) as HrenG.
  assert (Hfw : f w = w) by now apply avoiding_variables_fix.
  assert (Himage : forall x, f x \notin V) by now apply avoiding_variables_stay_outside.
  pose proof (proj1 (@variable_judgments_rename mode Hmut) _ _ _ _ _ Hview f _ G e Hfin HrenE (proj1 HrenG)) as Hview'.
  simpl in Hview'. rewrite Hfw in Hview'.
  pose proof (proj1 (proj2 (@variable_judgments_rename mode Hmut)) _ _ _ _ _ Hup f _ G e Hfin HrenE (proj1 HrenG)) as Hup'.
  pose proof (@stack_typing_renames mode G e Actual st typ_top Hmut Hstack f _ G e Hfin HrenE HrenG) as Hstack'.
  cbn [rename_typ] in Hstack'.
  rewrite (rename_stack_identity f st) in Hstack' by
    (intros x Hx; apply avoiding_variables_fix; exact (HavoidSt x Hx)).
  assert (Hmode : mode_viewpoint_adaptation' mode = mode_viewpoint_adapt_mutability)
    by (destruct mode; discriminate || reflexivity).
  pose proof Hadapt as Hadapt0. unfold viewpoint_adapt in Hadapt0. rewrite Hmode in Hadapt0.
  inversion Hadapt0 as [C x G1 Go e1 T1 S A Hinc Hcap]; subst.
  pose proof (@cap_bound_renames mode typ_refcap_mutability G objctx_empty e Ta A Hmut Hcap f _ G e Hfin HrenE (proj1 HrenG)) as Hcap'.
  pose proof (@viewpoint_renames mode G e w Ta _ Hmut Hadapt f _ G e Hfin HrenE (proj1 HrenG)) as Hadapt'.
  rewrite Hfw in Hadapt'. simpl in Hadapt', Hup'. rewrite Hfw in Hadapt', Hup'.
  destruct (@heap_reference_precise_definition mode G e h w y ds
    (def_fld a (avar_f loc)) Hmut HI HH Hw Hy Hfield)
    as (RO & BO & D & Hobj & _ & Hdef & Hdecl & _).
  pose proof HH as (Hok & _ & _ & _ & _ & _ & Hcorr & _).
  destruct (reference_location_have_same_record Hmut Hok Hcorr Hw) as (R0 & B0 & Hw0 & Hy0).
  pose proof (ctx_binding_unique Hobj Hw0) as Hsame. injection Hsame as <- _.
  inversion Hdef; subst. unfold ctx_obj in *.
  assert (HT : exists T,
    record_has (open y RO) (dec_fld a T T) /\ @ty_var mode G objctx_empty e loc T)
    by (eexists; split; eassumption).
  destruct HT as (Tf & HdeclT & HT).
  destruct (@precise_field_views_sound mode G e h w y RO BO a Tf Tf (rename_typ f Sa) (rename_typ f Ta)
    Hmut HI HH Hw Hobj HdeclT Hview') as [_ Hcov].
  assert (HlocTa : @ty_var mode G objctx_empty e loc (rename_typ f Ta))
    by (eapply ty_var_sub; eassumption).
  assert (Hloc : loc \in dom h).
  { pose proof (@typed_heap_items_are_scoped mode G e h HH y (item_obj ds) Hy) as Hitems.
    exact (@stored_def_in_scope _ _ _ _ Hitems Hfield). }
  destruct (heap_location_binding_shape Hmut HI HH Hloc) as (R & G0 & Hlocshape).
  pose proof (ctx_binds_k_lookup Hlocshape) as Hlocbind.
  set (B := typ_or (rename_typ f A) (typ_sel (avar_f w) typ_label_mutability (avar_b 0))).
  set (Ty := typ_and (typ_bnd R) (typ_mut_marker B)).
  assert (HavoidTy : vars_avoid (fv Ty) V).
  { assert (HR : vars_avoid (fv R) V).
    { intros z Hz. apply HavoidG. eapply ctx_binding_free_variables; [exact Hlocbind |].
      simpl. rewrite in_union. now left. }
    pose proof (@renamed_types_avoid_variables f V A Himage) as HA.
    unfold Ty, B. simpl. unfold vars_avoid in *. intros z Hz.
    repeat rewrite in_union in Hz. repeat rewrite in_singleton in Hz.
    destruct Hz as [Hz | [Hz | [Hz | [-> | Hz]]]].
    - exact (HR z Hz).
    - contradiction (notin_empty Hz).
    - exact (HA z Hz).
    - exact HavoidW.
    - contradiction (notin_empty Hz). }
  assert (Hctx : r §# G) by (intro H; exact (HavoidDom r H HrV)).
  assert (Henv : r # e).
  { destruct Hfresh as [Hfresh _]. repeat rewrite notin_union in Hfresh. tauto. }
  assert (Hkeep : preserves_ctx_binds G (G § r / v_ref ~ Ty))
    by now apply binds_preserved_by_fresh_push.
  assert (Hmore : env_binds_more e (e & r ~ loc)).
  { intros v l Hb. apply binds_push_neq; [exact Hb |].
    intros ->. apply Henv. exact (get_some_inv Hb). }
  assert (Hresult : @ty_var mode (G § r / v_ref ~ Ty) objctx_empty (e & r ~ loc) r (rename_typ f Actual)).
  { destruct (@adapt_read_alias_type mode G e w loc r R (rename_typ f Ta) _
        Hsef Hmut Hlocbind HlocTa Hadapt' Hctx Henv) as (S' & A' & Heq & Halias).
    injection Heq as <- <-.
    eapply ty_var_sub; [exact Halias |].
    eapply (proj1 (proj2 (variable_judgments_extend mode))); eassumption. }
  exists R, B, RO, Tf.
  split; [exact Hy0 |]. split; [exact HdeclT |]. cbv beta zeta.
  split.
  - split.
    + eapply fresh_alias_inert; try eassumption;
      intros Hin; [exact (HavoidG r Hin HrV) | exact (HavoidTy r Hin HrV)].
    + split; [eapply fresh_alias_heap_corresponds; eassumption |].
      exists (rename_typ f Actual). split.
      * apply ty_trm_var; [intros _; constructor | exact Hresult].
      * eapply stack_typing_narrows; [exact Hstack' | now apply fresh_context_push_narrows | exact Hmore].
  - split; [exact Hkeep |]. split; [exact Hmore |].
    split; [apply vars_avoid_union; now split |].
    intros [Hrecv | (w0 & Hw0' & Htyped0)].
    all: exists R, B; split; [constructor |].
    all: eapply protected_upper_weakens; [exact Hkeep | exact Hmore |].
    + destruct Hrecv as (R' & B' & Hbind & Hprotect).
      eapply protected_upper_from_receiver; eassumption.
    + destruct Hw0' as (R' & B' & Hbind & Hprotect).
      eapply protected_upper_through_field; [exact Hmut | exact Hbind | | exact Hcap' | exact Hprotect].
      eapply ty_var_sub; eassumption.
Qed.

Local Definition allocated_fields_are_protected mode G e h (old : vars) :=
  forall y ds a loc R T,
    y \notin old ->
    binds y (item_obj ds) h ->
    defs_has ds (def_fld a (avar_f loc)) ->
    loc \in old ->
    ctx_binds y (typ_and (typ_bnd R) (typ_mut_marker typ_bot)) G ->
    record_has (open y R) (dec_fld a T T) ->
    exists v, binds v loc e /\ @reference_is_protected mode G e v /\
      @ty_var mode G objctx_empty e v T.

Local Lemma protected_reference_extends mode G H e E w :
  preserves_ctx_binds G H -> env_binds_more e E ->
  @reference_is_protected mode G e w -> @reference_is_protected mode H E w.
Proof.
  intros Hkeep Henv (R & B & Hb & Hprotect).
  exists R, B. split; [now apply Hkeep | eapply protected_upper_weakens; eassumption].
Qed.

Local Lemma field_protection_extends mode G H e E h h' old :
  preserves_ctx_binds G H -> env_binds_more e E ->
  (forall y ds S, binds y (item_obj ds) h' -> ctx_binds y S H -> ctx_binds y S G) ->
  subheap_unchanged h' h ->
  @allocated_fields_are_protected mode G e h old ->
  @allocated_fields_are_protected mode H E h' old.
Proof.
  intros Hkeep Henv Hlookup Hsub Hfields y ds a loc R T Hy Hobj Hfield Hloc HyTy Hdecl.
  destruct (Hfields y ds a loc R T Hy (Hsub _ _ Hobj) Hfield Hloc (Hlookup _ _ _ Hobj HyTy) Hdecl)
    as (v & Hv & HvP & HvT).
  exists v. split; [now apply Henv |]. split.
  - eapply protected_reference_extends; eassumption.
  - eapply (proj1 (variable_judgments_extend mode)); eassumption.
Qed.

Local Lemma heap_write_preserves_allocated_fields mode G e h h' w y v loc a U old :
  mode_has_sef mode -> mode_has_mutability mode ->
  @inert mode G -> @heap_correspond mode G e h ->
  binds w y e -> binds v loc e ->
  @ty_trm mode G objctx_empty e (trm_write (avar_f w) a (avar_f v)) U ->
  heap_update h y a loc h' ->
  (loc \in old -> @reference_is_protected mode G e v) ->
  @allocated_fields_are_protected mode G e h old ->
  @allocated_fields_are_protected mode G e h' old.
Proof.
  intros Hsef Hmut HI HH Hw Hv Htyped Hupdate Hsafe Hfields.
  pose proof (typed_write_updates_heap Hsef Hmut HI HH Hw Hv Htyped Hupdate)
    as (_ & _ & Hwrite).
  destruct Hupdate as (_ & _ & Hdom & Hkeep & ds & ds' & Hy & Hupd & Hy').
  intros y' item a' l R T Hnew Hobj Hfield Hold Hctx HT.
  destruct (classic (y' = y)) as [-> | Hneq].
  - pose proof (binds_functional Hobj Hy') as Hsame. injection Hsame as ->.
    destruct (classic (a' = a)) as [-> | Hneq].
    + unfold defs_has in Hfield. simpl in Hfield.
      rewrite (field_update_lookup_new_value Hupd) in Hfield.
      injection Hfield as <-.
      exists v. split; [exact Hv |]. split; [now apply Hsafe |].
      destruct HH as (Hok & _ & _ & _ & _ & _ & Hcorr & _).
      destruct (reference_location_have_same_record Hmut Hok Hcorr Hw)
        as (R0 & B0 & Hctxw & Hy0).
      pose proof (ctx_binding_unique Hctx Hy0) as Hsame.
      injection Hsame as <-. eapply Hwrite; eassumption.
    + eapply (Hfields y ds a' l R T); try assumption.
      unfold defs_has in *. simpl in *. rewrite <- (field_update_lookup_other Hupd).
      * exact Hfield.
      * congruence.
  - assert (Hmem : y' \in dom h) by (rewrite Hdom; exact (get_some_inv Hobj)).
    destruct (get_some Hmem) as [source Hsource].
    rewrite (binds_functional (Hkeep _ _ Hneq Hsource) Hobj) in Hsource.
    eapply Hfields; eassumption.
Qed.

Local Lemma allocated_object_preserves_field_protection mode G h e R ds t st y w L old :
  let c := (trm_lit (lit_obj R ds) t ; st ; h ; e ; L) in
  let T := typ_and (typ_bnd R) (typ_mut_marker typ_bot) in
  let H := G § y / v_loc ~ T § w / v_ref ~ T in
  let E := e & w ~ y in
  let stored := deref_defs E (open w ds) in
  fresh_in_config (y :: w :: nil) c ->
  old \c dom h ->
  preserves_ctx_binds G H -> env_binds_more e E ->
  @field_initializers mode H E (open w ds) stored (open y R) ->
  @live_references_are_protected mode G c old ->
  @allocated_fields_are_protected mode G e h old ->
  @allocated_fields_are_protected mode H E (h & y ~ item_obj stored) old.
Proof.
  cbv beta zeta. intros Hfresh Hsub Hkeep Henv Hinit Hlive Hfields.
  pose proof (@fixed_name_outside_fresh_domains (trm_lit (lit_obj R ds) t ; st ; h ; e ; L) (y :: w :: nil) y Hfresh ltac:(now left)) as [Hyh Hye].
  pose proof (@fixed_name_outside_fresh_domains (trm_lit (lit_obj R ds) t ; st ; h ; e ; L) (y :: w :: nil) w Hfresh ltac:(right; now left)) as [Hwh Hwe].
  assert (Hne : w <> y) by (destruct Hfresh as [_ [Hf _]]; apply notin_union in Hf as [_ Hf]; now apply notin_singleton in Hf).
  assert (Hyold : y \notin old) by (intros Hin; apply Hyh; now apply Hsub).
  intros x data a loc R' T Hnew Hobj Hfield Hloc Hb Hdecl.
  apply binds_push_inv in Hobj as [[-> Hdata] | [Hxy Hobj]].
  - injection Hdata as HeqData. subst data.
    assert (Htop : ctx_binds y (typ_and (typ_bnd R) (typ_mut_marker typ_bot))
      (G § y / v_loc ~ typ_and (typ_bnd R) (typ_mut_marker typ_bot)
         § w / v_ref ~ typ_and (typ_bnd R) (typ_mut_marker typ_bot))).
    { apply ctx_binds_n; [congruence | constructor]. }
    pose proof (ctx_binding_unique Hb Htop) as Hshape. injection Hshape as ->.
    destruct (Hinit a loc T Hfield Hdecl) as (v & Hv & Hbind & Hty).
    assert (Hvw : v <> w).
    { intro Heq. subst v. apply binds_push_inv in Hbind as [[_ ->] | [Hneq _]];
        [contradiction | congruence]. }
    exists v. split; [exact Hbind |]. split; [|exact Hty].
    eapply protected_reference_extends; [exact Hkeep | exact Henv |].
    eapply (Hlive v loc); [|eapply binds_push_neq_inv; eassumption | exact Hloc].
    left. apply (proj2 (proj2 (proj2 tfree_open_backward))) in Hv as [Hcontra | Hfree].
    + contradiction.
    + apply tfree_trm_lit_l, tfree_lit_obj. exact Hfree.
  - assert (Hxw : x <> w) by (intros ->; apply Hwh; exact (get_some_inv Hobj)).
    assert (Hb0 : ctx_binds x (typ_and (typ_bnd R') (typ_mut_marker typ_bot)) G).
    { inversion Hb; subst; try congruence.
      match goal with Hb0 : ctx_binds x _ (ctx_push G y _ _) |- _ =>
        inversion Hb0; subst; try congruence; assumption end. }
    destruct (Hfields x data a loc R' T Hnew Hobj Hfield Hloc Hb0 Hdecl)
      as (v & Hv & HvP & HvT).
    exists v. split; [now apply Henv |]. split.
    + eapply protected_reference_extends; eassumption.
    + eapply (proj1 (variable_judgments_extend mode)); eassumption.
Qed.

Local Lemma allocated_object_preserves_live_protection mode G h e R ds t st y w L old :
  let c := (trm_lit (lit_obj R ds) t ; st ; h ; e ; L) in
  let T := typ_and (typ_bnd R) (typ_mut_marker typ_bot) in
  let H := G § y / v_loc ~ T § w / v_ref ~ T in
  let E := e & w ~ y in
  let stored := deref_defs E (open w ds) in
  let d := (open w t ; st ; h & y ~ item_obj stored ; E ; fv_config c) in
  y \notin old ->
  preserves_ctx_binds G H -> env_binds_more e E ->
  @live_references_are_protected mode G c old ->
  @live_references_are_protected mode H d old.
Proof.
  cbv beta zeta. intros Hy Hkeep Henv Hlive v loc Hfree Hbind Hold.
  cbn [config_env config_trm config_stack] in *.
  apply binds_push_inv in Hbind as [[_ ->] | [Hvw Hb]].
  - contradiction.
  - eapply protected_reference_extends; [exact Hkeep | exact Henv |].
    eapply (Hlive v loc); [|exact Hb | exact Hold].
    destruct Hfree as [Hterm | Hst]; [left | now right].
    apply (proj1 tfree_open_backward) in Hterm as [Hbad | Hfree]; [contradiction |].
    now apply tfree_trm_lit_r.
Qed.

Local Lemma protected_nonwrite_step mode G c d old :
  mode_has_sef mode -> mode_has_mutability mode ->
  c ↦ d -> config_env d = config_env c ->
  (forall w a v, config_trm c <> trm_write (avar_f w) a (avar_f v)) ->
  @runtime_typechecks mode G c typ_top ->
  @live_references_are_protected mode G c old ->
  @allocated_fields_are_protected mode G (config_env c) (config_heap c) old ->
  @runtime_typechecks mode G d typ_top /\
  @live_references_are_protected mode G d old /\
  @allocated_fields_are_protected mode G (config_env d) (config_heap d) old.
Proof.
  intros Hsef Hmut Hstep Henv Hnowrite HT HP HF.
  destruct (allocation_free_reduction_preserves_live_protection Hmut Hsef HT HP Hstep Henv)
    as [(HT' & HP' & Hheap) | (w & a & v & y & Hwrite & _)].
  - rewrite Henv, Hheap. auto.
  - exact (False_ind _ (Hnowrite w a v Hwrite)).
Qed.

Local Lemma write_preserves_runtime_and_protection mode G e h h' w y v loc a st L old :
  let c := (trm_write (avar_f w) a (avar_f v) ; st ; h ; e ; L) in
  let d := (trm_var (avar_f v) ; st ; h' ; e ; fv_config c) in
  mode_has_sef mode -> mode_has_mutability mode ->
  @runtime_typechecks mode G c typ_top ->
  @live_references_are_protected mode G c old ->
  @allocated_fields_are_protected mode G e h old ->
  heap_update h y a loc h' ->
  binds w y e -> binds v loc e ->
  @runtime_typechecks mode G d typ_top /\
  @live_references_are_protected mode G d old /\
  @allocated_fields_are_protected mode G e h' old.
Proof.
  cbv beta zeta.
  intros Hsef Hmut (HI & HH & T & Hty & Hst) Hlive Hfields Hupd Hw Hv.
  cbn [config_env config_heap config_trm config_stack] in *.
  destruct (typed_write_updates_heap Hsef Hmut HI HH Hw Hv Hty Hupd) as (HH' & Hret & _).
  split.
  - split; [exact HI |]. split; [exact HH' |]. exists T. split; [|exact Hst].
    apply ty_trm_var; [|exact Hret].
    intros _. pose proof HH as (_ & _ & _ & _ & _ & _ & Hcorr & _).
    destruct (renv_key_has_reference_kind Hcorr Hv) as (V & G0 & Hb).
    now apply kind_binding_visible in Hb.
  - split.
    + intros x l [Hfree | Hstfree] Hb Hold; apply (Hlive x l); try assumption.
      * left. inversion Hfree; subst. apply tfree_trm_write_r.
      * now right.
    + eapply (@heap_write_preserves_allocated_fields mode G e h h' w y v loc a T old
        Hsef Hmut HI HH Hw Hv Hty Hupd); [|exact Hfields].
      intro Hold. apply (Hlive v loc); [left; apply tfree_trm_write_r | exact Hv | exact Hold].
Qed.

Local Lemma read_preserves_field_and_live_protection mode G e h w y ds a loc st L r V old :
  let c := (trm_read (avar_f w) a ; st ; h ; e ; L) in
  let d := (trm_var (avar_f r) ; st ; h ; e & r ~ loc ; fv_config c) in
  mode_has_sef mode -> mode_has_mutability mode ->
  @runtime_typechecks mode G c typ_top ->
  @live_references_are_protected mode G c old ->
  @allocated_fields_are_protected mode G e h old ->
  binds w y e -> binds y (item_obj ds) h ->
  defs_has ds (def_fld a (avar_f loc)) ->
  fresh_in_config (r :: nil) c ->
  vars_avoid (ctx_fv G) V ->
  vars_avoid (fv_config c) V ->
  r \in V ->
  exists H, @runtime_typechecks mode H d typ_top /\
    @live_references_are_protected mode H d old /\
    @allocated_fields_are_protected mode H (e & r ~ loc) h old /\
    vars_avoid (ctx_fv H) V.
Proof.
  cbv beta zeta.
  intros Hsef Hmut HT Hlive Hfields Hw Hy Hfield Hfresh HavoidG HavoidC Hr.
  destruct (@typed_read_avoiding_future_names mode G e h w y ds a loc st L r V
    Hsef Hmut HT Hw Hy Hfield Hfresh HavoidG HavoidC Hr)
    as (R & B & RO & T & Hshape & Hdecl & HT' & Hkeep & Henv & Havoid' & Hprotect).
  exists (G § r / v_ref ~ typ_and (typ_bnd R) (typ_mut_marker B)).
  split; [exact HT' |]. split.
  - intros x l Hfree Hb Hold. cbn [config_env config_trm config_stack] in *.
    apply binds_push_inv in Hb as [[-> ->] | [Hne Hb]].
    + apply Hprotect.
      destruct (classic (y \in old)) as [Hy0 | Hy0].
      * left. apply (Hlive w y); [left; constructor | exact Hw | exact Hy0].
      * right. destruct (Hfields y ds a loc RO T Hy0 Hy Hfield Hold Hshape Hdecl)
          as (v & _ & Hv & HvT). now exists v.
    + eapply protected_reference_extends; [exact Hkeep | exact Henv |].
      apply (Hlive x l); [right | exact Hb | exact Hold].
      destruct Hfree as [Hterm | Hst]; [inversion Hterm; congruence | exact Hst].
  - split; [|exact Havoid'].
    eapply field_protection_extends; [exact Hkeep | exact Henv | | exact (fun _ _ Hb => Hb) | exact Hfields].
    intros x data S Hobj HB.
    assert (Hxr : x <> r).
    { intros ->. apply (HavoidC r); [|exact Hr].
      do 2 (rewrite in_union; right). rewrite in_union; left.
      rewrite in_union; left. exact (get_some_inv Hobj). }
    inversion HB; subst; congruence || assumption.
Qed.

Local Lemma protected_runtime_steps mode G c d final n old :
  mode_has_sef mode -> mode_has_mutability mode ->
  c ↦ d -> d ⊣n↦* final ->
  @runtime_typechecks mode G c typ_top ->
  @live_references_are_protected mode G c old ->
  @allocated_fields_are_protected mode G (config_env c) (config_heap c) old ->
  config_has_scoped_locations c ->
  old \c dom (config_heap c) ->
  vars_avoid (ctx_fv G) (upcoming_names c final) ->
  exists H, @runtime_typechecks mode H d typ_top /\
    @live_references_are_protected mode H d old /\
    @allocated_fields_are_protected mode H (config_env d) (config_heap d) old /\
    config_has_scoped_locations d /\
    old \c dom (config_heap d) /\
    vars_avoid (ctx_fv H) (upcoming_names d final).
Proof.
  intros Hsef Hmut Hstep Htail HT Hlive Hfields Hsc Hold HA.
  pose proof (scoped_locations_step Hstep Hsc) as Hsc'.
  assert (Hold' : old \c dom (config_heap d))
    by (intros x Hx; exact (heap_domain_extends_step Hstep (Hold x Hx))).
  pose proof (@upcoming_names_of_successor c d final Hstep) as Hsmaller.
  pose proof (@current_names_avoid_upcoming c final) as Hcurrent.
  cut (exists H, @runtime_typechecks mode H d typ_top /\
    @live_references_are_protected mode H d old /\
    @allocated_fields_are_protected mode H (config_env d) (config_heap d) old /\
    vars_avoid (ctx_fv H) (upcoming_names c final)).
  { intros (H & HT' & HP' & HF' & HA'). exists H. split; [exact HT' |]. split; [exact HP' |].
    split; [exact HF' |]. split; [exact Hsc' |]. split; [exact Hold' |].
    intros x Hx HF. exact (HA' x Hx (Hsmaller x HF)). }
  pose proof Hstep as Hred.
  destruct Hstep as
    [yObj wObj a h e L yVal wVal ds st Hfresh Hrecv Hobj Hfield
    |yObj wObj a h e L yArg wArg h' st Hupd Hrecv Harg
    |yObj wObj m h e L wArg body ds st Hobj Hmethod Hrecv
    |yFun wFun wArg h e L body st Hobj Hrecv
    |X body t h e L y w st Hfresh Hneq
    |X ds t h e L y w st Hfresh Hneq
    |t h e L x st
    |s t st h e L].
  all: try solve [
    lazymatch goal with
    | |- exists H, @runtime_typechecks _ H ?next _ /\ _ =>
      let K := fresh "Hnonwrite" in
      assert (K : @runtime_typechecks mode G next typ_top /\
        @live_references_are_protected mode G next old /\
        @allocated_fields_are_protected mode G (config_env next) (config_heap next) old)
        by (eapply (@protected_nonwrite_step mode G _ next old Hsef Hmut Hred);
          [reflexivity | intros; discriminate | exact HT | exact Hlive | exact Hfields]);
      destruct K as (? & ? & ?); exists G; auto
    end].
  - eapply read_preserves_field_and_live_protection; try eassumption.
    eapply allocated_read_name_is_upcoming; eassumption.
  - exists G. destruct (@write_preserves_runtime_and_protection mode G e h h' wObj yObj
      wArg yArg a st L old Hsef Hmut HT Hlive Hfields Hupd Hrecv Harg) as (HT' & HP' & HF').
    auto.
  - exfalso. destruct HT as (_ & _ & S & Hty & _).
    eapply literal_function_impossible; eassumption.
  - set (T := typ_and (typ_bnd X) (typ_mut_marker typ_bot)).
    set (H := G § y / v_loc ~ T § w / v_ref ~ T).
    destruct (@allocated_object_names_are_upcoming X ds t st h e L y w n final Hfresh Htail)
      as [Hy Hw].
    assert (HyG : y \notin ctx_fv G) by (intro HyG; exact (HA y HyG Hy)).
    assert (HwG : w \notin ctx_fv G) by (intro HwG; exact (HA w HwG Hw)).
    destruct (@typed_extended_literal_object mode G h e X ds t st typ_top y w L
      Hsef Hmut HT Hsc Hfresh HyG HwG) as (HT' & Hinit & Hkeep & Henv).
    assert (Hyold : y \notin old).
    { intros Hin. apply Hold in Hin. cbn [config_heap] in Hin.
      exact (proj1 (@fixed_name_outside_fresh_domains
        (trm_lit (lit_obj X ds) t ; st ; h ; e ; L) (y :: w :: nil) y Hfresh ltac:(now left)) Hin). }
    exists H. split; [exact HT' |]. split.
    + eapply allocated_object_preserves_live_protection; eassumption.
    + split.
      * eapply allocated_object_preserves_field_protection; eassumption.
      * unfold H, T. simpl. apply vars_avoid_union. split;
          [|apply vars_avoid_union; split; [|exact HA]].
        all: intros z Hz; apply Hcurrent;
          simpl in Hz; repeat rewrite in_union in Hz;
          destruct Hz as [Hz | [Hz | Hz]];
          try contradiction (notin_empty Hz);
          cbn [fv TrmFreeVar fv_trm fv_lit];
          repeat rewrite in_union; tauto.
Qed.

Local Lemma protected_runtime_trace mode n c final G old :
  mode_has_sef mode -> mode_has_mutability mode ->
  c ⊣n↦* final ->
  @runtime_typechecks mode G c typ_top ->
  @live_references_are_protected mode G c old ->
  @allocated_fields_are_protected mode G (config_env c) (config_heap c) old ->
  config_has_scoped_locations c ->
  old \c dom (config_heap c) ->
  vars_avoid (ctx_fv G) (upcoming_names c final) ->
  exists H, @runtime_typechecks mode H final typ_top /\
    @live_references_are_protected mode H final old.
Proof.
  intros Hsef Hmut. revert c G.
  induction n as [|n IH]; intros c G Hred HT HP HF Hsc Hold HA.
  - inversion Hred; subst. now exists G.
  - destruct (initial_step_of_trace Hred ltac:(lia)) as (d & Hstep & Htail).
    simpl in Htail.
    destruct (protected_runtime_steps Hsef Hmut Hstep Htail HT HP HF Hsc Hold HA)
      as (H & HT' & HP' & HF' & Hsc' & Hold' & HA').
    eapply IH; eassumption.
Qed.

Local Lemma standalone_readonly_execution_sound mode :
  mode_has_sef mode -> mode_has_mutability mode ->
  @standalone_readonly_execution_safe mode.
Proof.
  intros Hsef Hmut G c U z r Rz Rr n d x a v y it HT Hstack Hz Hr Hscope
    Hred Hwrite Hbind Hheap.
  set (old := dom (config_heap c)).
  assert (HT' : @runtime_typechecks mode G c typ_top).
  { destruct (typed_config_runtime_typechecks HT) as (HI & HH & T & Hty & Hst).
    split; [exact HI |]. split; [exact HH |]. exists T. split; [exact Hty |].
    rewrite Hstack. apply ty_stack_nil, subtyp_top. }
  assert (HP : @live_references_are_protected mode G c old).
  { exact (@standalone_aliases_protect_live_references mode G c z r Rz Rr old Hstack Hz Hr Hscope). }
  assert (HF : @allocated_fields_are_protected mode G (config_env c) (config_heap c) old).
  { intros l ds a' loc R F Hnew Hb. contradiction (Hnew (get_some_inv Hb)). }
  pose proof (typed_config_has_placement Hmut HT) as Hsc.
  destruct (typed_config_reserved_names HT) as [_ [HG _]].
  assert (HA : vars_avoid (ctx_fv G) (upcoming_names c d)).
  { intros w Hw. apply current_names_avoid_upcoming. now apply HG. }
  destruct (protected_runtime_trace Hsef Hmut Hred HT' HP HF Hsc (fun _ H => H) HA)
    as (G' & (HI & HH & T & Hty & Hst) & HP').
  exact (@protected_receiver_forbids_old_write mode G' d old x a v y T Hmut HI HH
    Hty HP' Hwrite Hbind (get_some_inv Hheap)).
Qed.

Theorem SefG_I :
  forall (typing_mode : Mode) (w1 : var) (m : met_label) (w2 : var)
         (TZv : typ) (c1 : config) (G : ctx) (c4 : config) (k : nat),
  mode_has_sef typing_mode ->
  mode_has_mutability typing_mode ->
  config_trm c1 = trm_call (avar_f w1) m (avar_f w2) ->
  (G ⁏ (config_env c1) ⊢ w1 ∶ typ_rcd (dec_met m typ_nocap TZv typ_top) /\
   G ⁏ (config_env c1) ⊢ w2 ∶ TZv /\
   G ⁏ (config_env c1) ⊢ typ_nocap <: TZv) ->
  (exists T1, ty_config G c1 T1) ->
  c1 ⊣k↦* c4 ->
  (exists j c3, frame_end_in c1 j c3 /\ j < k) \/
  subheap_unchanged (config_heap c1) (config_heap c4).

Proof.
  intros mode w1 m w2 Zv c G d k Hsef Hmut Hcall
    (Hreceiver & Hargument & Hnocap) (U & Htyped) Htrace.
  exact (@call_heap_preserved_from_method_and_write_invariants
    mode w1 m w2 Zv c G d k U
    (@precise_method_views_sound mode Hmut)
    (@standalone_readonly_execution_sound mode Hsef Hmut)
    Hsef Hmut Hcall Hreceiver Hargument Hnocap Htyped Htrace).
Qed.
