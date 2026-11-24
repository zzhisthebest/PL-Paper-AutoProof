From Stdlib Require Import List Arith.PeanoNat.

From Stdlib Require String.

Import ListNotations.

Require Import Syntax Notations Helpers Typing Subtyping Bigstep ViewpointAdaptation Reachability ConcreteState.

Local Lemma collect_fields_unique CT C fs gs :
  CollectFields CT C fs -> CollectFields CT C gs -> fs = gs.
Proof.
  intros Hfs. revert gs.
  induction Hfs; intros gs Hgs; inversion Hgs; subst; try congruence.
  assert (def = def0) by congruence. subst def0.
  assert (parent = parent0) by congruence. subst parent0.
  f_equal. now apply IHHfs.
Qed.

Local Lemma field_assignability_unique CT C f a1 a2 :
  sf_assignability_rel CT C f a1 -> sf_assignability_rel CT C f a2 -> a1 = a2.
Proof.
  intros [fd [Hfd Ha1]] [gd [Hgd Ha2]].
  destruct Hfd as [CT C fs f fd Hfs Hfd].
  inversion Hgd as [CT' C' gs f' gd' Hgs Hget]; subst.
  replace gs with fs in Hget by (eapply collect_fields_unique; eassumption).
  congruence.
Qed.

Local Lemma forall2_lookup {A B : Type} (P : A -> B -> Prop) xs ys n x y :
  Forall2 P xs ys -> nth_error xs n = Some x -> nth_error ys n = Some y -> P x y.
Proof.
  intros H. revert n.
  induction H; intros [|n] Hx Hy; cbn in Hx, Hy; try discriminate.
  - congruence.
  - now apply (IHForall2 n).
Qed.

Local Lemma immutable_field_target CT h l C vals f target qf :
  wf_heap CT h ->
  runtime_getObj h l = Some (mkObj (mkruntime_type Imm_r C) vals) ->
  nth_error vals f = Some (Iot target) ->
  sf_mutability_rel CT C f qf ->
  (qf = RDM_f \/ qf = Imm_f) ->
  exists D vs, runtime_getObj h target = Some (mkObj (mkruntime_type Imm_r D) vs).
Proof.
  intros Hheap Hobj Hfield [fd [Hlookup Hmut]] Hqf.
  assert (l < length h) as Hdom.
  { apply nth_error_Some. unfold runtime_getObj in Hobj. congruence. }
  specialize (Hheap l Hdom).
  unfold wf_obj in Hheap. rewrite Hobj in Hheap.
  destruct Hheap as [_ [fs [Hfs [_ Hvalues]]]].
  destruct Hlookup as [CT C gs f fd Hgs Hget].
  replace gs with fs in Hget by (eapply collect_fields_unique; eassumption).
  pose proof (forall2_lookup _ _ _ _ _ _ Hvalues Hfield Hget) as Htarget.
  cbn in Htarget.
  destruct (runtime_getObj h target) as [[[qr D] vs]|] eqn:Hget_target;
    [|contradiction].
  destruct Htarget as [rt [Hrt [_ Hqual]]].
  unfold r_type in Hrt. rewrite Hget_target in Hrt.
  injection Hrt as <-.
  cbn in Hqual. rewrite Hmut in Hqual.
  destruct qr.
  - destruct Hqf as [-> | ->]; contradiction.
  - eauto.
Qed.

Local Lemma abstract_reach_immutable CT h root target :
  wf_heap CT h ->
  reachable_abs CT h root target ->
  (exists C vals, runtime_getObj h root = Some (mkObj (mkruntime_type Imm_r C) vals)) ->
  exists C vals, runtime_getObj h target = Some (mkObj (mkruntime_type Imm_r C) vals).
Proof.
  intros Hheap Hreach.
  induction Hreach; intros [D [vs Himm]].
  - eauto.
  - rewrite Himm in Hobj. inversion Hobj; subst.
    destruct Hmut_abs; eapply immutable_field_target; eauto.
  - eauto.
Qed.

Local Lemma lookup_update_same {A : Type} (xs : list A) n x old :
  nth_error xs n = Some old -> nth_error (update n x xs) n = Some x.
Proof.
  revert xs. induction n; intros [|a xs] Hget; cbn in *; try discriminate.
  - reflexivity.
  - now apply IHn.
Qed.

Local Lemma lookup_update_other {A : Type} (xs : list A) i j x :
  i <> j -> nth_error (update i x xs) j = nth_error xs j.
Proof.
  revert i j. induction xs; intros [|i] [|j] Hneq; cbn; try reflexivity.
  - contradiction.
  - apply IHxs. congruence.
Qed.

Local Definition preserves_immutable_fields (CT : class_table) (h h' : heap) : Prop :=
  forall l C vals,
    runtime_getObj h l = Some (mkObj (mkruntime_type Imm_r C) vals) ->
    exists vals',
      runtime_getObj h' l = Some (mkObj (mkruntime_type Imm_r C) vals') /\
      forall f, sf_assignability_rel CT C f Final \/ sf_assignability_rel CT C f RDA ->
        nth_error vals f = nth_error vals' f.

Local Lemma preserves_immutable_fields_refl CT h :
  preserves_immutable_fields CT h h.
Proof.
  intros l C vals Hobj. exists vals. auto.
Qed.

Local Lemma preserves_immutable_fields_trans CT h h' h'' :
  preserves_immutable_fields CT h h' -> preserves_immutable_fields CT h' h'' ->
  preserves_immutable_fields CT h h''.
Proof.
  intros Hfirst Hsecond l C vals Hobj.
  destruct (Hfirst l C vals Hobj) as [vals' [Hobj' Hfields]].
  destruct (Hsecond l C vals' Hobj') as [vals'' [Hobj'' Hfields']].
  exists vals''. split; [exact Hobj'' |].
  intros f Hprotected. rewrite (Hfields f Hprotected). now apply Hfields'.
Qed.

Local Lemma preserves_immutable_fields_alloc CT h o :
  preserves_immutable_fields CT h (h ++ [o]).
Proof.
  intros l C vals Hobj. exists vals. split; [|reflexivity].
  unfold runtime_getObj in *.
  assert (l < length h) as Hdom by (apply nth_error_Some; congruence).
  now rewrite (nth_error_app1 h [o] Hdom).
Qed.

Local Lemma preserves_immutable_fields_write CT h x o k a v :
  runtime_getObj h x = Some o ->
  sf_assignability_rel CT (rctype (rt_type o)) k a ->
  runtime_vpa_assignability (rqtype (rt_type o)) a = Assignable ->
  preserves_immutable_fields CT h (update_field h x k v).
Proof.
  intros Hreceiver Hassign Hruntime l C vals Hobj.
  unfold update_field. rewrite Hreceiver.
  destruct (Nat.eq_dec x l) as [-> | Hneq].
  - rewrite Hobj in Hreceiver. injection Hreceiver as <-.
    exists (update k v vals). split.
    + unfold runtime_getObj in *. now apply lookup_update_same with
        (old := mkObj (mkruntime_type Imm_r C) vals).
    + intros f Hprotected. symmetry. apply lookup_update_other.
      intro Heq. subst f. cbn in Hassign, Hruntime.
      destruct Hprotected as [Hfinal | Hrda].
      * assert (a = Final) by (eapply field_assignability_unique; eassumption).
        subst a. discriminate.
      * assert (a = RDA) by (eapply field_assignability_unique; eassumption).
        subst a. discriminate.
  - exists vals. split; [|reflexivity].
    unfold runtime_getObj in *. now rewrite lookup_update_other.
Qed.

Local Lemma eval_preserves_immutable_fields CT rΓ h stmt result rΓ' h' :
  eval_stmt CT rΓ h stmt result rΓ' h' -> preserves_immutable_fields CT h h'.
Proof.
  intro Heval. induction Heval; subst;
    eauto using preserves_immutable_fields_refl, preserves_immutable_fields_trans,
      preserves_immutable_fields_alloc, preserves_immutable_fields_write.
Qed.

Theorem abstract_state_preservation :
  forall CT sΓ mt rΓ h stmt rΓ' h' sΓ' root C0 vals0 l C qr vals f
    (Himm_root : runtime_getObj h root = Some (mkObj (mkruntime_type Imm_r C0) vals0))
    (Hreach : reachable_abs CT h root l)
    (Hwf : wf_r_config CT sΓ rΓ h)
    (Htyping : stmt_typing CT sΓ mt stmt sΓ')
    (Heval : eval_stmt CT rΓ h stmt OK rΓ' h')
    (Hobj : runtime_getObj h l = Some (mkObj (mkruntime_type qr C) vals))
    (Hprotected : sf_assignability_rel CT C f Final \/
                  sf_assignability_rel CT C f RDA),
    exists vals',
      runtime_getObj h' l = Some (mkObj (mkruntime_type qr C) vals') /\
      nth_error vals f = nth_error vals' f.
Proof.
  intros CT sΓ mt rΓ h stmt rΓ' h' sΓ' root C0 vals0 l C qr vals f
    Himm_root Hreach Hwf Htyping Heval Hobj Hprotected.
  destruct Hwf as [_ [Hheap _]].
  assert (exists D vs, runtime_getObj h l = Some (mkObj (mkruntime_type Imm_r D) vs))
    as [D [vs Himm]].
  { eapply abstract_reach_immutable; eauto. }
  rewrite Hobj in Himm. inversion Himm; subst qr D vs.
  destruct (eval_preserves_immutable_fields _ _ _ _ _ _ _ Heval l C vals Hobj)
    as [vals' [Hobj' Hfields]].
  exists vals'. split; [exact Hobj' | now apply Hfields].
Qed.
