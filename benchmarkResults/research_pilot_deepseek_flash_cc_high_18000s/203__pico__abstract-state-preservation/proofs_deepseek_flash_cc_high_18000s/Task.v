From Stdlib Require Import List.

From Stdlib Require String.

Import ListNotations.

Require Import Syntax Notations Helpers Typing Subtyping Bigstep ViewpointAdaptation Reachability ConcreteState.

Lemma nth_error_update_neq :
  forall {X : Type} (l : list X) n v m,
    m <> n -> nth_error (update n v l) m = nth_error l m.
Proof.
  intros X l. induction l as [|x xs IH]; intros n v m Hneq.
  - destruct n; reflexivity.
  - destruct n as [|n']; destruct m as [|m'].
    + exfalso; apply Hneq; reflexivity.
    + reflexivity.
    + reflexivity.
    + simpl. apply IH. intros H; apply Hneq. now rewrite H.
Qed.

Lemma nth_error_update_eq :
  forall {X : Type} (l : list X) n v,
    n < length l -> nth_error (update n v l) n = Some v.
Proof.
  intros X l. induction l as [|x xs IH]; intros [|n] v Hlen.
  - simpl in Hlen. inversion Hlen.
  - simpl in Hlen. inversion Hlen.
  - reflexivity.
  - simpl. simpl in Hlen. apply IH. apply Nat.succ_lt_mono. exact Hlen.
Qed.

Lemma nth_error_app_l :
  forall {X : Type} (l1 l2 : list X) n x,
    nth_error l1 n = Some x -> nth_error (l1 ++ l2) n = Some x.
Proof.
  intros X l1. induction l1 as [|a l1 IH]; intros l2 n x H.
  - destruct n; simpl in *; discriminate.
  - destruct n as [|n']; simpl in *.
    + auto.
    + apply IH; auto.
Qed.

Lemma nth_error_Some_lt :
  forall {X : Type} (l : list X) n x,
    nth_error l n = Some x -> n < length l.
Proof.
  intros X l n x H. apply (proj1 (nth_error_Some l n)). rewrite H. discriminate.
Qed.

Lemma CollectFields_det :
  forall CT C fs1, CollectFields CT C fs1 ->
    forall fs2, CollectFields CT C fs2 -> fs1 = fs2.
Proof.
  intros CT C fs1 H1.
  induction H1; intros fs2 H2; inversion H2; subst.
  - reflexivity.
  - rewrite Hnone in Hfind. discriminate.
  - rewrite Hnone in Hfind. discriminate.
  - rewrite Hnone in Hfind. discriminate.
  - reflexivity.
  - rewrite Hfind in Hfind0. injection Hfind0 as ->. rewrite Hsuper in Hsuper0. discriminate.
  - rewrite Hnone in Hfind. discriminate.
  - rewrite Hfind in Hfind0. injection Hfind0 as ->. rewrite Hsuper in Hsuper0. discriminate.
  - rewrite Hfind in Hfind0. injection Hfind0 as ->.
    rewrite Hsuper in Hsuper0. injection Hsuper0 as ->.
    rewrite (IHCollectFields parent_fields0 Hparent_cf). reflexivity.
Qed.

Lemma FieldLookup_det :
  forall CT C f fd1 fd2,
    FieldLookup CT C f fd1 -> FieldLookup CT C f fd2 -> fd1 = fd2.
Proof.
  intros CT C f fd1 fd2 H1 H2.
  destruct H1 as [CT1 C1 fs1 f1 fd1' Hcf1 Hg1].
  destruct H2 as [CT2 C2 fs2 f2 fd2' Hcf2 Hg2].
  assert (fs1 = fs2) as -> by (eapply CollectFields_det; eauto).
  rewrite Hg1 in Hg2. injection Hg2 as ->. reflexivity.
Qed.

Lemma sf_assignability_rel_det :
  forall CT C f a1 a2,
    sf_assignability_rel CT C f a1 -> sf_assignability_rel CT C f a2 -> a1 = a2.
Proof.
  intros CT C f a1 a2 [d1 [Hl1 Ha1]] [d2 [Hl2 Ha2]].
  assert (d1 = d2) as -> by (eapply FieldLookup_det; eauto).
  rewrite Ha1 in Ha2. auto.
Qed.

Lemma Forall2_nth_error_Some :
  forall {A B : Type} (R : A -> B -> Prop) (l1 : list A) (l2 : list B) n x,
    Forall2 R l1 l2 -> nth_error l1 n = Some x ->
    exists y, nth_error l2 n = Some y /\ R x y.
Proof.
  intros A B R l1.
  induction l1 as [|a l1 IH]; intros l2 n x Hfa Hn.
  - destruct n; simpl in Hn; discriminate.
  - destruct l2 as [|b l2].
    + inversion Hfa.
    + destruct n as [|n']; simpl in *.
      * injection Hn as ->. inversion Hfa as [|? ? HR Hfa']; subst.
        exists b; split; auto.
      * inversion Hfa as [|? ? HR Hfa']; subst.
        eapply IH; eauto.
Qed.

Lemma r_type_Some :
  forall (h : heap) (l : Loc) (rt : runtime_type),
    r_type h l = Some rt ->
    exists o, runtime_getObj h l = Some o /\ rt_type o = rt.
Proof.
  intros h l rt H. unfold r_type in H.
  destruct (runtime_getObj h l) as [o|] eqn:E.
  - exists o; split; auto. injection H as Hrt. exact Hrt.
  - discriminate.
Qed.

Lemma reachable_abs_imm :
  forall CT h l0 l,
    wf_heap CT h ->
    reachable_abs CT h l0 l ->
    (exists C vals, runtime_getObj h l0 = Some (mkObj (mkruntime_type Imm_r C) vals)) ->
    exists C vals, runtime_getObj h l = Some (mkObj (mkruntime_type Imm_r C) vals).
Proof.
  intros CT h a b Hwf Hreach.
  induction Hreach; intros Himm.
  - exact Himm.
  - destruct Himm as [C0 [vals0 Himm0]].
    assert (Hsome : Some (mkObj (mkruntime_type any C) vals) =
                   Some (mkObj (mkruntime_type Imm_r C0) vals0)).
    { rewrite <- Hobj, <- Himm0. reflexivity. }
    injection Hsome as Hany HC Hvals.
    subst any. subst C. subst vals.
    assert (Hdom0 : l0 < dom h) by (eapply nth_error_Some_lt; eauto).
    pose proof (Hwf l0 Hdom0) as Hwfo.
    unfold wf_obj in Hwfo. rewrite Hobj in Hwfo. cbn in Hwfo.
    destruct Hwfo as (Hwfrt & field_defs & Hcf & Hlen & Hfa2).
    destruct (Forall2_nth_error_Some _ _ _ _ _ Hfa2 Hfield) as [fd [Hnth Hr]].
    destruct Hmut_abs as [[fd' [Hfl' Hmut']] | [fd' [Hfl' Hmut']]].
    + assert (Hfl_fd : FieldLookup CT C0 k fd).
      { apply (FL_Found CT C0 field_defs k fd Hcf). unfold gget. exact Hnth. }
      assert (Hfd_eq : fd = fd') by (eapply FieldLookup_det; eauto).
      subst fd'. rewrite Hmut' in Hr. cbn in Hr.
      destruct (runtime_getObj h l1) as [o1|] eqn:Eo1.
      * cbn in Hr. destruct Hr as [rqt [Hrtype [Hbsub Hqual]]].
        unfold r_type in Hrtype. rewrite Eo1 in Hrtype. injection Hrtype as Hrt_eq.
        destruct o1 as [rt fm]. cbn in Hrt_eq. subst rt.
        destruct rqt as [rq rc]. cbn in Hqual.
        destruct rq; cbn in Hqual.
        -- destruct Hqual.
        -- exists rc, fm. reflexivity.
      * cbn in Hr. destruct Hr.
    + assert (Hfl_fd2 : FieldLookup CT C0 k fd).
      { apply (FL_Found CT C0 field_defs k fd Hcf). unfold gget. exact Hnth. }
      assert (Hfd_eq2 : fd = fd') by (eapply FieldLookup_det; eauto).
      subst fd'. rewrite Hmut' in Hr. cbn in Hr.
      destruct (runtime_getObj h l1) as [o1|] eqn:Eo2.
      * cbn in Hr. destruct Hr as [rqt2 [Hrtype2 [Hbsub2 Hqual2]]].
        unfold r_type in Hrtype2. rewrite Eo2 in Hrtype2. injection Hrtype2 as Hrt_eq2.
        destruct o1 as [rt2 fm2]. cbn in Hrt_eq2. subst rt2.
        destruct rqt2 as [rq2 rc2]. cbn in Hqual2.
        destruct rq2; cbn in Hqual2.
        -- destruct Hqual2.
        -- exists rc2, fm2. reflexivity.
      * cbn in Hr. destruct Hr.
  - apply IHHreach2. apply IHHreach1. exact Himm.
Qed.

Definition abs_heaps_related (CT : class_table) (h h' : heap) : Prop :=
  forall l qr C vals,
    runtime_getObj h l = Some (mkObj (mkruntime_type qr C) vals) ->
    qr = Imm_r ->
    exists vals',
      runtime_getObj h' l = Some (mkObj (mkruntime_type qr C) vals') /\
      forall f,
        (sf_assignability_rel CT C f Final \/ sf_assignability_rel CT C f RDA) ->
        nth_error vals f = nth_error vals' f.

Lemma abs_heaps_related_refl : forall CT h, abs_heaps_related CT h h.
Proof. intros CT h l qr C vals Hobj Hqr. exists vals. split; auto. Qed.

Lemma abs_heaps_related_trans : forall CT h1 h2 h3,
  abs_heaps_related CT h1 h2 -> abs_heaps_related CT h2 h3 -> abs_heaps_related CT h1 h3.
Proof.
  intros CT h1 h2 h3 H12 H23 l qr C vals H1 Hqr.
  destruct (H12 l qr C vals H1 Hqr) as [vals2 [Hobj2 Hpre2]].
  destruct (H23 l qr C vals2 Hobj2 Hqr) as [vals3 [Hobj3 Hpre3]].
  exists vals3. split; auto.
  intros f Hprot. rewrite (Hpre2 f Hprot). apply Hpre3; auto.
Qed.

Lemma abs_heaps_related_app : forall CT h o, abs_heaps_related CT h (h ++ [o]).
Proof.
  intros CT h o l qr C vals H1 Hqr. exists vals. split; auto.
  eapply nth_error_app_l; eauto.
Qed.

Lemma update_field_other : forall h loc f v l,
  l <> loc -> runtime_getObj (update_field h loc f v) l = runtime_getObj h l.
Proof.
  intros. unfold update_field.
  destruct (runtime_getObj h loc) as [o|] eqn:E.
  - apply nth_error_update_neq. auto.
  - reflexivity.
Qed.

Lemma update_field_same : forall h loc f v o,
  runtime_getObj h loc = Some o ->
  runtime_getObj (update_field h loc f v) loc =
  Some (set_fields_map o (update f v (fields_map o))).
Proof.
  intros h loc f v o Hobj. unfold update_field. rewrite Hobj.
  apply nth_error_update_eq. eapply nth_error_Some_lt; eauto.
Qed.

Lemma abs_heaps_related_write :
  forall CT h loc fd val a o,
    runtime_getObj h loc = Some o ->
    sf_assignability_rel CT (rctype (rt_type o)) fd a ->
    runtime_vpa_assignability (rqtype (rt_type o)) a = Assignable ->
    abs_heaps_related CT h (update_field h loc fd val).
Proof.
  intros CT h loc fd val a o Hobj Hassign Hrt l qr C vals Hl Hqr.
  destruct (Nat.eq_dec l loc) as [Heq|Hne].
  - subst l.
    rewrite Hobj in Hl. injection Hl as Ho. subst o. subst qr.
    cbn in Hassign.
    assert (Ha : a = Assignable) by (destruct a; cbn in Hrt; try discriminate; reflexivity).
    subst a.
    exists (update fd val vals). split.
    + rewrite (update_field_same h loc fd val (mkObj (mkruntime_type Imm_r C) vals) Hobj).
      cbn. reflexivity.
    + intros g Hg.
      assert (Hneq : fd <> g).
      { intro Hfg. subst g.
        destruct Hg as [Hg|Hg].
        - pose proof (sf_assignability_rel_det CT C fd Assignable Final Hassign Hg). discriminate.
        - pose proof (sf_assignability_rel_det CT C fd Assignable RDA Hassign Hg). discriminate. }
      symmetry. apply nth_error_update_neq.
      intro H; apply Hneq; now symmetry.
  - exists vals. split.
    + rewrite (update_field_other h loc fd val l Hne). exact Hl.
    + auto.
Qed.

Lemma eval_stmt_abs_heaps_related :
  forall CT rΓ h stmt res rΓ' h',
    eval_stmt CT rΓ h stmt res rΓ' h' -> abs_heaps_related CT h h'.
Proof.
  intros CT rΓ h stmt res rΓ' h' Heval.
  induction Heval; try apply abs_heaps_related_refl.
  - rewrite Hupdate. eapply abs_heaps_related_write; eauto.
  - rewrite Hheap. apply abs_heaps_related_app.
  - exact IHHeval.
  - exact IHHeval.
  - exact IHHeval.
  - eapply abs_heaps_related_trans; eauto.
  - exact IHHeval.
  - eapply abs_heaps_related_trans; eauto.
  - exact IHHeval.
  - eapply abs_heaps_related_trans; eauto.
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
  destruct Hwf as (HwfCT & Hwfheap & _).
  assert (Himm_l : exists C1 vals1,
            runtime_getObj h l = Some (mkObj (mkruntime_type Imm_r C1) vals1)).
  { eapply reachable_abs_imm.
    - exact Hwfheap.
    - exact Hreach.
    - exists C0, vals0. exact Himm_root. }
  destruct Himm_l as [C1 [vals1 Hl]].
  rewrite Hobj in Hl. injection Hl as Hqr HC Hvals.
  pose proof (eval_stmt_abs_heaps_related CT rΓ h stmt OK rΓ' h' Heval) as Hrel.
  destruct (Hrel l qr C vals Hobj Hqr) as [vals' [Hobj' Hpre]].
  exists vals'. split.
  - exact Hobj'.
  - apply Hpre. exact Hprotected.
Qed.
