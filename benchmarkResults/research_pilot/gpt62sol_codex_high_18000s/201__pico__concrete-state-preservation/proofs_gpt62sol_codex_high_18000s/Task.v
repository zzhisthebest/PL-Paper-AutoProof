From Stdlib Require Import List.

From Stdlib Require String.

Import ListNotations.

Require Import Syntax Notations Helpers Typing Subtyping Bigstep ViewpointAdaptation Reachability ConcreteState.

Local Lemma cs_nth_update_same {A} (xs : list A) i old new :
  nth_error xs i = Some old -> nth_error (update i new xs) i = Some new.
Proof.
  revert xs. induction i; intros [|x xs] H; cbn in *; try discriminate; auto.
Qed.

Local Lemma cs_nth_update_other {A} (xs : list A) i j new :
  i <> j -> nth_error (update i new xs) j = nth_error xs j.
Proof.
  revert xs j. induction i; intros [|x xs] [|j] H; cbn; auto.
  - contradiction.
Qed.

Local Lemma cs_Forall2_nth {A B} (P : A -> B -> Prop) xs ys i x y :
  Forall2 P xs ys -> nth_error xs i = Some x -> nth_error ys i = Some y -> P x y.
Proof.
  intros H. revert i. induction H; intros [|i] Hx Hy; cbn in *;
    try discriminate; [now injection Hx as <-; injection Hy as <- | eauto].
Qed.

Local Lemma cs_Forall2_update {A B} (P : A -> B -> Prop) xs ys i y x :
  Forall2 P xs ys -> nth_error ys i = Some y -> P x y -> Forall2 P (update i x xs) ys.
Proof.
  intros H. revert i. induction H; intros [|i] Hy Hxy; cbn in *;
    try discriminate; [injection Hy as <- |]; constructor; auto.
Qed.

(* Runtime typing stated pointwise for variables and fields. *)
Local Definition cs_value_ok CT h ambient v T :=
  match v with
  | Null_a => True
  | Iot l => wf_r_typable CT h l T ambient
  end.

Local Definition cs_field_type f :=
  Build_qualified_type (qf2q (mutability (ftype f))) (f_base_type (ftype f)).

Local Definition cs_heap_ok CT h :=
  forall l o, runtime_getObj h l = Some o ->
  wf_rtypeuse CT (rqtype (rt_type o)) (rctype (rt_type o)) /\
  exists fs, CollectFields CT (rctype (rt_type o)) fs /\
    Forall2 (fun v f => cs_value_ok CT h (rqtype (rt_type o)) v (cs_field_type f))
      (fields_map o) fs.

Local Definition cs_env_ok CT h (rΓ : r_env) sΓ ambient :=
  (exists l C, runtime_getVal rΓ 0 = Some (Iot l) /\
              r_type h l = Some (mkruntime_type ambient C)) /\
  Forall2 (cs_value_ok CT h ambient) (vars rΓ) sΓ.

(* The frame condition preserves runtime types everywhere and all fields
   of already allocated immutable objects. *)
Local Definition cs_frame (h h' : heap) :=
  forall l o, runtime_getObj h l = Some o ->
  exists o', runtime_getObj h' l = Some o' /\ rt_type o' = rt_type o /\
    (rqtype (rt_type o) = Imm_r -> o' = o).

Local Lemma cs_frame_refl h : cs_frame h h.
Proof. intros l o H. exists o. auto. Qed.

Local Lemma cs_frame_trans h h' h'' :
  cs_frame h h' -> cs_frame h' h'' -> cs_frame h h''.
Proof.
  intros H1 H2 l o H.
  destruct (H1 _ _ H) as (o' & Ho' & Hty' & Himm').
  destruct (H2 _ _ Ho') as (o'' & Ho'' & Hty'' & Himm'').
  exists o''. split; [exact Ho''|]. split; [congruence|].
  intros Himm. rewrite Himm'' Himm'; congruence.
Qed.

Local Lemma cs_frame_type h h' l rt :
  cs_frame h h' -> r_type h l = Some rt -> r_type h' l = Some rt.
Proof.
  intros HF. unfold r_type.
  destruct (runtime_getObj h l) as [o|] eqn:H; [|discriminate].
  destruct (HF _ _ H) as (o' & -> & -> & _). trivial.
Qed.

Local Lemma cs_frame_value CT h h' ambient v T :
  cs_frame h h' -> cs_value_ok CT h ambient v T -> cs_value_ok CT h' ambient v T.
Proof.
  intros HF. destruct v as [|l]; [trivial|].
  cbn. unfold wf_r_typable.
  destruct (r_type h l) as [rt|] eqn:H; [|contradiction].
  rewrite (cs_frame_type _ _ _ _ HF H). trivial.
Qed.

Local Lemma cs_frame_values CT h h' ambient vs Ts :
  cs_frame h h' ->
  Forall2 (cs_value_ok CT h ambient) vs Ts ->
  Forall2 (cs_value_ok CT h' ambient) vs Ts.
Proof. intros HF H. induction H; constructor; eauto using cs_frame_value. Qed.

Local Lemma cs_frame_fields CT h h' ambient vs fs :
  cs_frame h h' ->
  Forall2 (fun v f => cs_value_ok CT h ambient v (cs_field_type f)) vs fs ->
  Forall2 (fun v f => cs_value_ok CT h' ambient v (cs_field_type f)) vs fs.
Proof. intros HF H. induction H; constructor; eauto using cs_frame_value. Qed.

Local Lemma cs_frame_receiver CT h h' rΓ sΓ ambient :
  cs_frame h h' -> cs_env_ok CT h rΓ sΓ ambient ->
  exists l C, runtime_getVal rΓ 0 = Some (Iot l) /\
              r_type h' l = Some (mkruntime_type ambient C).
Proof.
  intros HF [(l & C & Hv & Ht) _].
  exists l, C. eauto using cs_frame_type.
Qed.

Local Lemma cs_heap_from_wf CT h : wf_heap CT h -> cs_heap_ok CT h.
Proof.
  intros H l o Ho.
  assert (Hl : l < dom h).
  { apply nth_error_Some. unfold runtime_getObj in Ho. congruence. }
  specialize (H l Hl). unfold wf_obj in H. rewrite Ho in H.
  destruct H as (Htype & fs & Hfs & _ & Hvals).
  split; [exact Htype|]. exists fs. split; [exact Hfs|].
  clear Hfs. induction Hvals as [|v f vs fs Hv Hvs IH]; constructor; auto.
  destruct v as [|loc]; [exact I|].
  destruct (runtime_getObj h loc); [|contradiction].
  destruct Hv as (rt & Hrt & Hbase & Hqual).
  cbn. unfold wf_r_typable. rewrite Hrt.
  split; [exact Hbase|].
  unfold cs_field_type. cbn.
  destruct (rqtype rt), (rqtype (rt_type o)), (mutability (ftype f)); exact Hqual.
Qed.

Local Lemma cs_Forall2_from_nth {A B} (P : A -> B -> Prop) xs ys :
  length xs = length ys ->
  (forall i x y, nth_error xs i = Some x -> nth_error ys i = Some y -> P x y) ->
  Forall2 P xs ys.
Proof.
  revert ys. induction xs as [|x xs IH]; intros [|y ys] Hlen Hnth;
    try discriminate; constructor.
  - exact (Hnth 0 x y eq_refl eq_refl).
  - apply IH; [now injection Hlen|]. intros i. exact (Hnth (S i)).
Qed.

Local Lemma cs_config_from_wf CT sΓ rΓ h :
  wf_r_config CT sΓ rΓ h ->
  cs_heap_ok CT h /\ exists ambient, cs_env_ok CT h rΓ sΓ ambient.
Proof.
  intros (_ & Hheap & (_ & (l & Hthis & Hdom) & _) & _ & Hlen & Hvars).
  split; [now apply cs_heap_from_wf|].
  assert (Hobj : exists o, runtime_getObj h l = Some o).
  { unfold runtime_getObj. apply nth_error_Some in Hdom.
    destruct (nth_error h l); [eauto|contradiction]. }
  destruct Hobj as ([ [ambient C] vs ] & Hobj).
  assert (Hget : runtime_getVal rΓ 0 = Some (Iot l)).
  { unfold runtime_getVal. destruct (vars rΓ) as [|[|loc] vs']; cbn in *;
      congruence. }
  exists ambient. split.
  - exists l, C. split; [exact Hget|]. unfold r_type. now rewrite Hobj.
  - apply cs_Forall2_from_nth; [symmetry; exact Hlen|].
    intros i v T Hv HT. assert (Hi : i < length sΓ).
    { apply nth_error_Some. congruence. }
    specialize (Hvars l ambient Hthis).
    unfold r_muttype in Hvars. rewrite Hobj in Hvars.
    specialize (Hvars eq_refl i Hi T HT).
    change (runtime_getVal rΓ i = Some v) in Hv. now rewrite Hv in Hvars.
Qed.

(* Subtyping and viewpoint adaptation preserve runtime value typing. *)
Local Lemma cs_qsub_trans q1 q2 q3 :
  q_subtype q1 q2 -> q_subtype q2 q3 -> q_subtype q1 q3.
Proof.
  intros H12 H23. destruct H23; auto using q_rd, q_bot.
  inversion H12; subst; auto using q_bot.
Qed.

Local Lemma cs_sub_parts CT T U :
  qualified_type_subtype CT T U ->
  q_subtype (sqtype T) (sqtype U) /\ base_subtype CT (sctype T) (sctype U).
Proof.
  intros H. induction H; intuition eauto using cs_qsub_trans, base_trans, q_refl, base_refl.
Qed.

Local Lemma cs_accept_sub qr ambient q1 q2 :
  qualifier_typable_context qr q1 ambient -> q_subtype q1 q2 ->
  qualifier_typable_context qr q2 ambient.
Proof.
  intros H Hsub. destruct Hsub; auto.
  - destruct qr, ambient; exact I.
  - destruct qr, ambient; contradiction.
Qed.

Local Lemma cs_value_sub CT h ambient v T U :
  cs_value_ok CT h ambient v T -> qualified_type_subtype CT T U ->
  cs_value_ok CT h ambient v U.
Proof.
  intros Hv Hsub. destruct v as [|l]; [exact I|].
  apply cs_sub_parts in Hsub as [Hq Hb].
  cbn in *. unfold wf_r_typable in *.
  destruct (r_type h l); [|contradiction].
  destruct Hv. split; eauto using base_trans, cs_accept_sub.
Qed.

Local Definition cs_adapt mt :=
  match mt with
  | ReadonlyState | TransitiveState => vpa_mutability_tt_readonly_state
  | AbstractState | ConcreteState => vpa_mutability_tt_abstract_state
  end.

Local Lemma cs_adapt_base mt T U : sctype (cs_adapt mt T U) = sctype U.
Proof. now destruct mt. Qed.

Local Lemma cs_adapt_qual mt T U :
  sqtype (cs_adapt mt T U) =
  sqtype (cs_adapt mt (Build_qualified_type (sqtype T) 0)
                       (Build_qualified_type (sqtype U) 0)).
Proof. now destruct mt. Qed.

Local Lemma cs_accept_out mt ambient qr qreceiver qresult qvalue :
  qualifier_typable_context qr qreceiver ambient ->
  qualifier_typable_context qvalue qresult qr ->
  qualifier_typable_context qvalue
    (sqtype (cs_adapt mt (Build_qualified_type qreceiver 0)
                         (Build_qualified_type qresult 0))) ambient.
Proof.
  destruct mt, ambient, qr, qreceiver, qresult, qvalue; cbn; tauto.
Qed.

Local Lemma cs_accept_in mt ambient qr qreceiver qarg qparam qvalue :
  qualifier_typable_context qr qreceiver ambient ->
  qualifier_typable_context qvalue qarg ambient ->
  q_subtype qarg
    (sqtype (cs_adapt mt (Build_qualified_type qreceiver 0)
                         (Build_qualified_type qparam 0))) ->
  qualifier_typable_context qvalue qparam qr.
Proof.
  destruct mt, ambient, qr, qreceiver, qarg, qparam, qvalue; cbn;
    intros Hr Ha Hs; try contradiction; try exact I;
    inversion Hs; subst; auto; contradiction.
Qed.

Local Lemma cs_value_out CT h mt ambient qr receiver T v :
  qualifier_typable_context qr (sqtype receiver) ambient ->
  cs_value_ok CT h qr v T ->
  cs_value_ok CT h ambient v (cs_adapt mt receiver T).
Proof.
  intros Hr Hv. destruct v as [|l]; [exact I|].
  cbn in *. unfold wf_r_typable in *.
  destruct (r_type h l); [|contradiction].
  destruct Hv as [Hb Hq].
  rewrite cs_adapt_base cs_adapt_qual.
  split; eauto using cs_accept_out.
Qed.

Local Lemma cs_value_in CT h mt ambient qr receiver T U v :
  qualifier_typable_context qr (sqtype receiver) ambient ->
  cs_value_ok CT h ambient v T ->
  qualified_type_subtype CT T (cs_adapt mt receiver U) ->
  cs_value_ok CT h qr v U.
Proof.
  intros Hr Hv Hsub. destruct v as [|l]; [exact I|].
  apply cs_sub_parts in Hsub as [Hq Hb].
  cbn in *. unfold wf_r_typable in *.
  destruct (r_type h l); [|contradiction].
  rewrite cs_adapt_base in Hb. rewrite cs_adapt_qual in Hq.
  destruct Hv as [Hbase Hqual].
  split; eauto using base_trans, cs_accept_in.
Qed.
(* Inherited fields keep their indices, and dynamic method lookup refines
   the statically selected signature. *)
Local Lemma cs_class_at CT C def :
  wf_class_table CT -> find_class CT C = Some def ->
  wf_class CT def /\ cname (signature def) = C.
Proof.
  intros (Hclasses & _ & _ & Hnames) Hfind.
  split; [|eauto].
  rewrite Forall_forall in Hclasses. apply Hclasses.
  eapply nth_error_In. exact Hfind.
Qed.

Local Lemma cs_collect_exists CT C :
  wf_class_table CT -> C < dom CT -> exists fs, CollectFields CT C fs.
Proof.
  intros HCT HC.
  assert (Hsome : nth_error CT C <> None) by now apply nth_error_Some.
  destruct (find_class CT C) as [def|] eqn:Hfind; [|contradiction].
  destruct (cs_class_at _ _ _ HCT Hfind) as [Hclass Hname].
  inversion Hclass; subst.
  - exists []. eapply CF_Object; eauto.
  - destruct H as [(_ & _ & fs & Hfs & _) _].
    now exists fs.
Qed.

Local Lemma cs_collect_unique CT C fs gs :
  CollectFields CT C fs -> CollectFields CT C gs -> fs = gs.
Proof.
  intros H. revert gs.
  induction H; intros gs Hg; inversion Hg; subst; try congruence.
  assert (def = def0) by congruence. subst def0.
  assert (parent = parent0) by congruence. subst parent0.
  f_equal. auto.
Qed.

Local Lemma cs_field_extends CT C D fs f fd :
  parent_lookup CT C = Some D -> CollectFields CT C fs ->
  FieldLookup CT D f fd -> nth_error fs f = Some fd.
Proof.
  unfold parent_lookup. intros Hparent Hfs Hfield.
  inversion Hfs; subst.
  - rewrite Hnone in Hparent. discriminate.
  - rewrite Hfind Hsuper in Hparent. discriminate.
  - rewrite Hfind Hsuper in Hparent. injection Hparent as ->.
    inversion Hfield as [CT' D' gs f' fd' Hgs Hget]; subst.
    pose proof (cs_collect_unique _ _ _ _ Hparent_cf Hgs) as ->.
    unfold gget in Hget.
    rewrite nth_error_app1; [|exact Hget].
    apply nth_error_Some. congruence.
Qed.

Local Lemma cs_field_sub CT C D f fd :
  wf_class_table CT -> base_subtype CT C D ->
  FieldLookup CT D f fd -> FieldLookup CT C f fd.
Proof.
  intros HCT H. induction H; intros Hfield; auto.
  destruct (cs_collect_exists _ _ HCT Hdom_C) as [fs Hfs].
  eapply FL_Found; [exact Hfs|].
  eapply cs_field_extends; eassumption.
Qed.

Local Lemma cs_field_in_collection CT C fs f fd :
  CollectFields CT C fs -> FieldLookup CT C f fd -> nth_error fs f = Some fd.
Proof.
  intros Hfs Hfield. inversion Hfield as [CT' C' gs f' fd' Hgs Hget]; subst.
  now rewrite (cs_collect_unique _ _ _ _ Hfs Hgs).
Qed.

Local Lemma cs_bound_sub CT C D qr :
  wf_class_table CT -> base_subtype CT C D -> wf_rtypeuse CT qr C ->
  wf_rtypeuse CT qr D.
Proof.
  intros HCT Hsub. induction Hsub; auto.
  unfold parent_lookup in Hparent.
  destruct (find_class CT C) as [def|] eqn:Hfind; [|discriminate].
  intros Hr. unfold wf_rtypeuse, bound in Hr. rewrite Hfind in Hr.
  destruct Hr as [_ Hqual].
  destruct (cs_class_at _ _ _ HCT Hfind) as [Hclass Hname].
  inversion Hclass; subst.
  - congruence.
  - assert (superC = D) by congruence. subst superC.
    unfold wf_rtypeuse.
    destruct (bound CT D) as [qd|] eqn:Hbound.
    + destruct H as (_ & _ & _ & fs & _ & Hbounds & _).
      change (class_qualifier (signature def) = qd \/ qd = RDM_c) in Hbounds.
      split; [exact Hdom_D|].
      destruct Hbounds as [Heq| ->]; [now rewrite <- Heq|now destruct qr].
    + unfold bound in Hbound.
      unfold find_class, gget in Hbound.
      apply nth_error_Some in Hdom_D.
      destruct (nth_error CT D); [discriminate|contradiction].
Qed.

Local Lemma cs_found_name ms m md :
  gget_method ms m = Some md -> mname (msignature md) = m.
Proof.
  unfold gget_method. intros H.
  apply find_some in H as [_ Hname].
  now apply PeanoNat.Nat.eqb_eq in Hname.
Qed.

Local Lemma cs_method_wf CT C m md :
  wf_class_table CT -> FindMethodWithName CT C m md ->
  exists D, wf_method CT D md /\ sctype (mreceiver (msignature md)) = D /\
            base_subtype CT C D.
Proof.
  intros HCT H. induction H as
    [CT C def own_methods m md Hfind Hown Hget_method
    |CT C def parent m md own_methods Hfind Hown Hnot Hsuper Hparent_fmn IH].
  - subst own_methods.
    destruct (cs_class_at _ _ _ HCT Hfind) as [Hclass Hname].
    assert (HC : C < dom CT).
    { apply nth_error_Some. unfold find_class, gget in Hfind. congruence. }
    inversion Hclass; subst.
    + rewrite Hno_methods in Hget_method. discriminate.
    + destruct H as (_ & Hmethods & _ & _).
      apply find_some in Hget_method as [Hin _].
      rewrite Forall_forall in Hmethods. specialize (Hmethods _ Hin).
      exists (cname (signature def)). split; [exact Hmethods|].
      destruct Hmethods as (_ & ? & ? & _ & _ & _ & _ & _ & Heq & _).
      split; [exact Heq|]. now apply base_refl.
  - destruct (IH HCT) as (D & Hwf & Hrecv & Hsub).
    assert (Hdom_parent : parent < dom CT).
    { inversion Hparent_fmn; unfold find_class, gget in *;
        apply nth_error_Some; congruence. }
    exists D. split; [exact Hwf|]. split; [exact Hrecv|].
    eapply base_trans; [eapply base_extends with (D := parent)|exact Hsub].
    + apply nth_error_Some. unfold find_class, gget in Hfind. congruence.
    + exact Hdom_parent.
    + unfold parent_lookup. now rewrite Hfind.
Qed.

Local Lemma cs_method_unique CT C m md md' :
  FindMethodWithName CT C m md -> FindMethodWithName CT C m md' -> md = md'.
Proof.
  intros H. revert md'. induction H; intros md' H';
    inversion H'; subst; try congruence.
  assert (def = def0) by congruence. subst def0.
  assert (parent = parent0) by congruence. subst parent0.
  eauto.
Qed.

Local Lemma cs_method_refine CT C D m md :
  wf_class_table CT -> base_subtype CT C D -> FindMethodWithName CT D m md ->
  exists md', FindMethodWithName CT C m md' /\
    method_signature_refinement CT (msignature md') (msignature md).
Proof.
  intros HCT Hbase. revert md. induction Hbase; intros md Hmd.
  - exists md. split; auto using msr_refl.
  - destruct (IHHbase2 HCT md Hmd) as (middle & Hmid & HRmid).
    destruct (IHHbase1 HCT middle Hmid) as (child & Hchild & HRchild).
    exists child. split; eauto using msr_trans.
  - unfold parent_lookup in Hparent.
    destruct (find_class CT C) as [def|] eqn:Hfind; [|discriminate].
    destruct (gget_method (methods (body def)) m) as [child|] eqn:Hchild.
    + assert (Hlookup : FindMethodWithName CT C m child) by
          (eapply FOM_Here; eauto).
      exists child. split; [exact Hlookup|].
      destruct (cs_method_wf _ _ _ _ HCT Hmd) as (P & _ & HP & Hb).
      destruct (cs_class_at _ _ _ HCT Hfind) as [Hclass Hname].
      inversion Hclass; subst.
      * rewrite Hno_methods in Hchild. discriminate.
      * destruct H as (_ & Hmethods & _ & _).
        pose proof (cs_found_name _ _ _ Hchild) as Hm.
        apply find_some in Hchild as [Hin _].
        rewrite Forall_forall in Hmethods. specialize (Hmethods _ Hin).
        destruct Hmethods as (_ & sΓ' & T & Htyping & _ & _ & _ & Hover & Hrecv & _).
        assert (Hwf : wf_senv CT (mreceiver (msignature child) :: mparams (msignature child)))
          by (inversion Htyping; assumption).
        assert (Hqc : bound CT (cname (signature def)) = Some (class_qualifier (signature def))).
        { unfold bound. now rewrite Hfind. }
        eapply msr_override; [rewrite Hrecv; exact Hqc| |exact Hwf|].
        -- rewrite Hrecv. eapply base_trans; [|exact Hb].
           apply base_extends; try assumption.
           unfold parent_lookup. now rewrite Hfind.
        -- eapply Hover; [exact Hfind|exact Hparent|exact Hqc|].
           now rewrite Hm.
    + exists md. split; [eapply FOM_Super; eauto|constructor].
Qed.

Local Lemma cs_refinement_scope CT ms ms' :
  method_signature_refinement CT ms ms' -> mscope ms = mscope ms'.
Proof.
  intros H. induction H; [reflexivity| |congruence].
  destruct H2 as (_ & Hscope & _). exact Hscope.
Qed.

Local Lemma cs_refinement_ancestor CT C ms ms' :
  method_signature_refinement CT ms ms' ->
  base_subtype CT C (sctype (mreceiver ms)) ->
  base_subtype CT C (sctype (mreceiver ms')).
Proof.
  intros H. induction H; eauto using base_trans.
Qed.

Local Lemma cs_override_qual qr qc p q :
  vpa_mutability_runtime_bound_agree qr qc ->
  qualifier_typable_context p (vpa_mutability_qq_abstract_state (qc2q qc) q) qr
  <-> qualifier_typable_context p q qr.
Proof.
  destruct qr, qc, p, q; cbn; intuition discriminate.
Qed.

Local Lemma cs_override_value CT h qr qc T v :
  vpa_mutability_runtime_bound_agree qr qc ->
  cs_value_ok CT h qr v (vpa_mutability_override qc T) <->
  cs_value_ok CT h qr v T.
Proof.
  intros Hbound. destruct v as [|l]; [reflexivity|].
  cbn. unfold wf_r_typable, vpa_mutability_override.
  destruct (r_type h l) as [rt|]; [|reflexivity].
  cbn. rewrite (cs_override_qual qr qc (rqtype rt) (sqtype T) Hbound).
  reflexivity.
Qed.

Local Lemma cs_Forall2_chain {A B C} (P : A -> B -> Prop) (Q : B -> C -> Prop)
    (R : A -> C -> Prop) xs ys zs :
  (forall x y z, P x y -> Q y z -> R x z) ->
  Forall2 P xs ys -> Forall2 Q ys zs -> Forall2 R xs zs.
Proof.
  intros Hrel H. revert zs.
  induction H; intros zs Hz; inversion Hz; subst; constructor; eauto.
Qed.

(* Override compatibility transports arguments and the receiver into the
   overriding frame, and transports its return value back to the caller. *)
Local Lemma cs_refinement_values CT h C qr ms ms' :
  wf_class_table CT -> wf_rtypeuse CT qr C ->
  method_signature_refinement CT ms ms' ->
  base_subtype CT C (sctype (mreceiver ms)) ->
  (qualifier_typable_context qr (sqtype (mreceiver ms')) qr ->
   qualifier_typable_context qr (sqtype (mreceiver ms)) qr) /\
  (forall vs, Forall2 (cs_value_ok CT h qr) vs (mparams ms') ->
              Forall2 (cs_value_ok CT h qr) vs (mparams ms)) /\
  (forall v, cs_value_ok CT h qr v (mret ms) -> cs_value_ok CT h qr v (mret ms')).
Proof.
  intros HCT Hrt H. induction H; intros HC.
  - auto.
  - destruct H2 as (_ & _ & Hret & Hargs & Hrecv).
    pose proof (cs_bound_sub _ _ _ _ HCT HC Hrt) as Hbound.
    unfold wf_rtypeuse in Hbound. rewrite H in Hbound. destruct Hbound as [_ Hbound].
    split.
    + intros Hr. eapply cs_accept_sub; [|exact Hrecv].
      cbn. apply (proj2 (cs_override_qual qr qc qr _ Hbound)). exact Hr.
    + split.
      * intros vs Hvs. eapply cs_Forall2_chain; [|exact Hvs|exact Hargs].
        intros v T U Hv Hsub. eapply cs_value_sub; [|exact Hsub].
        now apply (proj2 (cs_override_value CT h qr qc T v Hbound)).
      * intros v Hv. apply (proj1 (cs_override_value CT h qr qc (mret overridden) v Hbound)).
        eauto using cs_value_sub.
  - destruct (IHmethod_signature_refinement1 HC) as (Hr1 & Ha1 & Hv1).
    destruct (IHmethod_signature_refinement2 (cs_refinement_ancestor _ _ _ _ H HC))
      as (Hr2 & Ha2 & Hv2).
    auto.
Qed.

Local Lemma cs_var_ok CT h rΓ sΓ qr x v T :
  cs_env_ok CT h rΓ sΓ qr ->
  runtime_getVal rΓ x = Some v -> static_getType sΓ x = Some T ->
  cs_value_ok CT h qr v T.
Proof.
  intros [_ H] Hv HT. eapply cs_Forall2_nth; eassumption.
Qed.

Local Lemma cs_args_ok CT h rΓ sΓ qr xs vs Ts :
  cs_env_ok CT h rΓ sΓ qr ->
  runtime_lookup_list rΓ xs = Some vs ->
  static_getType_list sΓ xs = Some Ts ->
  Forall2 (cs_value_ok CT h qr) vs Ts.
Proof.
  intros Henv. revert vs Ts.
  induction xs as [|x xs IH]; intros vs Ts Hv HT; cbn in *.
  - injection Hv as <-. injection HT as <-. constructor.
  - destruct (runtime_getVal rΓ x) as [v|] eqn:Hx; [|discriminate].
    destruct (static_getType sΓ x) as [T|] eqn:HTx; [|discriminate].
    change (match runtime_lookup_list rΓ xs with
            | Some tail => Some (v :: tail) | None => None end = Some vs) in Hv.
    change (match static_getType_list sΓ xs with
            | Some tail => Some (T :: tail) | None => None end = Some Ts) in HT.
    destruct (runtime_lookup_list rΓ xs) as [vs'|] eqn:Hvs; [|discriminate].
    destruct (static_getType_list sΓ xs) as [Ts'|] eqn:HTs; [|discriminate].
    injection Hv as <-. injection HT as <-. constructor; eauto using cs_var_ok.
Qed.

Local Lemma cs_args_in CT h mt ambient qr receiver vs Ts Us :
  qualifier_typable_context qr (sqtype receiver) ambient ->
  Forall2 (cs_value_ok CT h ambient) vs Ts ->
  Forall2 (fun T U => qualified_type_subtype CT T (cs_adapt mt receiver U)) Ts Us ->
  Forall2 (cs_value_ok CT h qr) vs Us.
Proof.
  intros Hrecv Hvs Hsub. eapply cs_Forall2_chain; [|exact Hvs|exact Hsub].
  intros v T U Hv Hs. eapply cs_value_in with (mt := mt) (receiver := receiver); eassumption.
Qed.

Local Lemma cs_receiver_in CT h mt ambient qr l C receiver U :
  r_type h l = Some (mkruntime_type qr C) ->
  cs_value_ok CT h ambient (Iot l) receiver ->
  (qualified_type_subtype CT receiver (cs_adapt mt receiver U) \/
   (sqtype receiver = RO /\ sqtype U = RDM /\
    base_subtype CT (sctype receiver) (sctype U))) ->
  qualifier_typable_context qr (sqtype U) qr.
Proof.
  intros Hrt Hr [Hsub | (_ & -> & _)].
  - pose proof (cs_value_in CT h mt ambient qr receiver receiver U (Iot l)) as Hin.
    assert (Hq : qualifier_typable_context qr (sqtype receiver) ambient).
    { cbn in Hr. unfold wf_r_typable in Hr. now rewrite Hrt in Hr. }
    specialize (Hin Hq Hr Hsub).
    cbn in Hin. unfold wf_r_typable in Hin. now rewrite Hrt in Hin.
  - now destruct qr.
Qed.

Local Lemma cs_type_obj h l o :
  runtime_getObj h l = Some o -> r_type h l = Some (rt_type o).
Proof. intros H. unfold r_type. now rewrite H. Qed.

Local Lemma cs_var_location CT h rΓ sΓ ambient x l T o :
  cs_env_ok CT h rΓ sΓ ambient ->
  runtime_getVal rΓ x = Some (Iot l) -> static_getType sΓ x = Some T ->
  runtime_getObj h l = Some o ->
  base_subtype CT (rctype (rt_type o)) (sctype T) /\
  qualifier_typable_context (rqtype (rt_type o)) (sqtype T) ambient.
Proof.
  intros Henv Hv HT Ho.
  pose proof (cs_var_ok _ _ _ _ _ _ _ _ Henv Hv HT) as H.
  cbn in H. unfold wf_r_typable in H. now rewrite (cs_type_obj _ _ _ Ho) in H.
Qed.

Local Lemma cs_field_type_adapt T fd :
  Build_qualified_type
    (vpa_mutability_stype_fld_abstract_state (sqtype T) (mutability (ftype fd)))
    (f_base_type (ftype fd)) = cs_adapt ConcreteState T (cs_field_type fd).
Proof.
  unfold cs_adapt, cs_field_type, vpa_mutability_tt_abstract_state,
    vpa_mutability_tt_readonly_state. cbn.
  destruct (sqtype T), (mutability (ftype fd)); reflexivity.
Qed.

Local Lemma cs_field_type_adapt_ro T fd :
  Build_qualified_type
    (vpa_mutability_stype_fld_readonly_state (sqtype T) (mutability (ftype fd)))
    (f_base_type (ftype fd)) = cs_adapt TransitiveState T (cs_field_type fd).
Proof.
  unfold cs_adapt, cs_field_type, vpa_mutability_tt_abstract_state,
    vpa_mutability_tt_readonly_state. cbn.
  destruct (sqtype T), (mutability (ftype fd)); reflexivity.
Qed.

Local Lemma cs_read_field CT h rΓ sΓ ambient mt x T f fd l o v :
  wf_class_table CT -> cs_heap_ok CT h -> cs_env_ok CT h rΓ sΓ ambient ->
  static_getType sΓ x = Some T -> FieldLookup CT (sctype T) f fd ->
  runtime_getVal rΓ x = Some (Iot l) -> runtime_getObj h l = Some o ->
  getVal (fields_map o) f = Some v ->
  cs_value_ok CT h ambient v (cs_adapt mt T (cs_field_type fd)).
Proof.
  intros HCT Hheap Henv HT Hfd Hv Ho Hf.
  destruct (cs_var_location _ _ _ _ _ _ _ _ _ Henv Hv HT Ho) as [Hb Hq].
  destruct (Hheap _ _ Ho) as (_ & fs & Hfs & Hvals).
  pose proof (cs_field_sub _ _ _ _ _ HCT Hb Hfd) as Hfd'.
  pose proof (cs_field_in_collection _ _ _ _ _ Hfs Hfd') as Hnth.
  eapply cs_value_out; [exact Hq|].
  exact (cs_Forall2_nth _ _ _ _ _ _ Hvals Hf Hnth).
Qed.

Local Lemma cs_expr_ok CT h rΓ sΓ ambient mt e v T :
  wf_class_table CT -> cs_heap_ok CT h -> cs_env_ok CT h rΓ sΓ ambient ->
  expr_has_type CT sΓ mt e T -> eval_expr CT rΓ h e v OK rΓ h ->
  cs_value_ok CT h ambient v T.
Proof.
  intros HCT Hheap Henv Htype Heval.
  inversion Htype; subst; inversion Heval; subst.
  - exact I.
  - eapply cs_var_ok; eassumption.
  - rewrite cs_field_type_adapt. eapply cs_read_field; eassumption.
  - rewrite cs_field_type_adapt_ro. eapply cs_read_field; eassumption.
Qed.

Local Lemma cs_env_update CT h h' rΓ sΓ qr x v T :
  cs_frame h h' -> cs_env_ok CT h rΓ sΓ qr ->
  x <> 0 -> static_getType sΓ x = Some T -> cs_value_ok CT h' qr v T ->
  cs_env_ok CT h' (set_vars rΓ (update x v (vars rΓ))) sΓ qr.
Proof.
  intros HF Henv Hx HT Hv. split.
  - destruct (cs_frame_receiver _ _ _ _ _ _ HF Henv) as (l & C & Hthis & Hrt).
    exists l, C. split; [|exact Hrt].
    change (nth_error (update x v (vars rΓ)) 0 = Some (Iot l)).
    now rewrite (cs_nth_update_other (vars rΓ) x 0 v Hx).
  - destruct Henv as [_ Hvars]. cbn.
    eapply cs_Forall2_update; eauto using cs_frame_values.
Qed.

Local Lemma cs_env_local CT h rΓ sΓ qr T :
  cs_env_ok CT h rΓ sΓ qr ->
  cs_env_ok CT h (set_vars rΓ (vars rΓ ++ [Null_a])) (sΓ ++ [T]) qr.
Proof.
  intros [(l & C & Hv & Hr) Hvars]. split.
  - exists l, C. split; [|exact Hr].
    unfold runtime_getVal in *. cbn.
    destruct (vars rΓ); cbn in *; congruence.
  - cbn. apply Forall2_app; [exact Hvars|].
    constructor; [exact I|constructor].
Qed.

(* Heap updates preserve object types, and allocation extends the heap
   at a fresh index. *)
Local Lemma cs_frame_update h l o f v :
  runtime_getObj h l = Some o -> rqtype (rt_type o) = Mut_r ->
  cs_frame h (update_field h l f v).
Proof.
  intros Ho Hmut k obj Hobj. unfold update_field. rewrite Ho.
  unfold runtime_getObj in *.
  destruct (PeanoNat.Nat.eq_dec l k) as [<-|Hneq].
  - assert (o = obj) by congruence. subst obj.
    eexists. split; [eapply cs_nth_update_same; exact Ho|].
    split; [reflexivity|congruence].
  - exists obj. rewrite cs_nth_update_other; auto.
Qed.

Local Lemma cs_heap_update CT h l o f fd v :
  cs_heap_ok CT h -> runtime_getObj h l = Some o -> rqtype (rt_type o) = Mut_r ->
  FieldLookup CT (rctype (rt_type o)) f fd ->
  cs_value_ok CT h Mut_r v (cs_field_type fd) ->
  cs_heap_ok CT (update_field h l f v).
Proof.
  intros Hheap Ho Hmut Hfd Hv.
  pose proof (cs_frame_update _ _ _ f v Ho Hmut) as HF.
  intros k obj Hobj. unfold update_field in Hobj. rewrite Ho in Hobj.
  unfold runtime_getObj in Hobj.
  destruct (PeanoNat.Nat.eq_dec l k) as [<-|Hneq].
  - pose proof (cs_nth_update_same h l _ (set_fields_map o (update f v (fields_map o))) Ho) as H.
    rewrite H in Hobj. injection Hobj as <-. cbn.
    destruct (Hheap _ _ Ho) as (Hrt & fs & Hfs & Hvals).
    split; [exact Hrt|]. exists fs. split; [exact Hfs|].
    eapply cs_Forall2_update.
    + eapply cs_frame_fields; eassumption.
    + eapply cs_field_in_collection; eassumption.
    + rewrite Hmut. eapply cs_frame_value; eassumption.
  - rewrite (cs_nth_update_other _ _ _ _ Hneq) in Hobj.
    destruct (Hheap _ _ Hobj) as (Hrt & fs & Hfs & Hvals).
    split; [exact Hrt|]. exists fs. split; [exact Hfs|].
    eapply cs_frame_fields; eassumption.
Qed.

Local Lemma cs_write_ok CT h rΓ sΓ ambient mt x y f l o fd T U a v :
  wf_class_table CT -> cs_heap_ok CT h -> cs_env_ok CT h rΓ sΓ ambient ->
  runtime_getVal rΓ x = Some (Iot l) -> runtime_getObj h l = Some o ->
  runtime_getVal rΓ y = Some v ->
  static_getType sΓ x = Some T -> static_getType sΓ y = Some U ->
  FieldLookup CT (sctype T) f fd ->
  vpa_assignability_cs_ts (sqtype T) a = Assignable ->
  qualified_type_subtype CT U (cs_adapt mt T (cs_field_type fd)) ->
  cs_frame h (update_field h l f v) /\ cs_heap_ok CT (update_field h l f v).
Proof.
  intros HCT Hheap Henv Hx Ho Hy HT HU Hfd Hassign Hsub.
  destruct (cs_var_location _ _ _ _ _ _ _ _ _ Henv Hx HT Ho) as [Hb Hq].
  assert (Hmut : rqtype (rt_type o) = Mut_r).
  { destruct ambient, (rqtype (rt_type o)), (sqtype T), a; cbn in *;
      try discriminate; try contradiction; reflexivity. }
  rewrite Hmut in Hq.
  split; [eauto using cs_frame_update|].
  eapply cs_heap_update; try eassumption.
  - eauto using cs_field_sub.
  - eapply cs_value_in with (mt := mt) (receiver := T); eauto using cs_var_ok.
Qed.

Local Lemma cs_frame_alloc h o : cs_frame h (h ++ [o]).
Proof.
  intros l obj Ho. exists obj. split; [|auto].
  unfold runtime_getObj in *.
  rewrite nth_error_app1; [|exact Ho].
  apply nth_error_Some. congruence.
Qed.

Local Lemma cs_alloc_lookup h o : runtime_getObj (h ++ [o]) (dom h) = Some o.
Proof.
  unfold runtime_getObj. rewrite (@nth_error_app2 _ h [o] (length h) (PeanoNat.Nat.le_refl _)).
  now rewrite PeanoNat.Nat.sub_diag.
Qed.

Local Lemma cs_heap_alloc CT h o fs :
  cs_heap_ok CT h ->
  wf_rtypeuse CT (rqtype (rt_type o)) (rctype (rt_type o)) ->
  CollectFields CT (rctype (rt_type o)) fs ->
  Forall2 (fun v f => cs_value_ok CT h (rqtype (rt_type o)) v (cs_field_type f))
    (fields_map o) fs ->
  cs_heap_ok CT (h ++ [o]).
Proof.
  intros Hheap Hty Hfs Hvals l obj Ho.
  destruct (PeanoNat.Nat.lt_ge_cases l (dom h)) as [Hl|Hl].
  - unfold runtime_getObj in Ho. rewrite (@nth_error_app1 _ h [o] l Hl) in Ho.
    destruct (Hheap _ _ Ho) as (Hrt & gs & Hgs & Hvs).
    split; [exact Hrt|]. exists gs. split; [exact Hgs|].
    eapply cs_frame_fields; eauto using cs_frame_alloc.
  - unfold runtime_getObj in Ho. rewrite (@nth_error_app2 _ h [o] l Hl) in Ho.
    destruct (l - dom h); cbn in Ho; try (destruct n; discriminate).
    injection Ho as <-.
    split; [exact Hty|]. exists fs. split; [exact Hfs|].
    eapply cs_frame_fields; eauto using cs_frame_alloc.
Qed.

Local Lemma cs_constructor_wf CT C ctor :
  wf_class_table CT -> constructor_sig_lookup CT C = Some ctor ->
  wf_constructor CT C ctor.
Proof.
  intros HCT Hctor. unfold constructor_sig_lookup, constructor_def_lookup in Hctor.
  destruct (find_class CT C) as [def|] eqn:Hfind; [|discriminate].
  injection Hctor as <-.
  destruct (cs_class_at _ _ _ HCT Hfind) as [Hclass Hname].
  inversion Hclass; subst.
  - destruct Hwf_ctor as (_ & _ & Hbound & Hparams & Hfields).
    unfold wf_constructor. split; [congruence|].
    rewrite Hparams. split; [constructor|].
    exists []. split; [exact Hfields|]. split; constructor.
  - destruct H as [Hwf _]. exact Hwf.
Qed.

Local Lemma cs_created_qual ambient qc :
  qualifier_typable_context (vpa_mutability_object_creation ambient qc)
    (qc2q qc) ambient.
Proof. destruct ambient, qc; exact I. Qed.

Local Lemma cs_created_bound ambient qc boundq :
  vpa_mutability_bound (qc2q qc) boundq = qc2q qc ->
  vpa_mutability_runtime_bound_agree (vpa_mutability_object_creation ambient qc) boundq.
Proof. destruct ambient, qc, boundq; cbn; congruence. Qed.

Local Lemma cs_constructor_field_adapt fd qc :
  Build_qualified_type (vpa_mutability_constructor_fld qc (mutability (ftype fd)))
    (f_base_type (ftype fd)) = vpa_mutability_override qc (cs_field_type fd).
Proof.
  unfold vpa_mutability_override, cs_field_type. cbn.
  destruct qc, (mutability (ftype fd)); reflexivity.
Qed.

Local Lemma cs_Forall2_map_right {A B C} (P : A -> C -> Prop) (g : B -> C) xs ys :
  Forall2 P xs (map g ys) <-> Forall2 (fun x y => P x (g y)) xs ys.
Proof.
  revert xs. induction ys as [|y ys IH]; intros xs; cbn; split; intros H;
    inversion H; subst; constructor; try assumption; apply IH; assumption.
Qed.

Local Lemma cs_sub_dom CT T U :
  qualified_type_subtype CT T U -> sctype T < dom CT.
Proof. intros H. induction H; assumption. Qed.

Local Lemma cs_new_ok CT h rΓ sΓ ambient x Tx qc C ys Ts ctor vs :
  wf_class_table CT -> cs_heap_ok CT h -> cs_env_ok CT h rΓ sΓ ambient ->
  static_getType sΓ x = Some Tx -> x <> 0 ->
  static_getType_list sΓ ys = Some Ts -> runtime_lookup_list rΓ ys = Some vs ->
  constructor_sig_lookup CT C = Some ctor ->
  vpa_mutability_bound (qc2q qc) (cqualifier ctor) = qc2q qc ->
  Forall2 (qualified_type_subtype CT) Ts
    (map (vpa_mutability_constructor_param qc) (cparams ctor)) ->
  qualified_type_subtype CT (Build_qualified_type (qc2q qc) C) Tx ->
  let qr := vpa_mutability_object_creation ambient qc in
  let h' := h ++ [mkObj (mkruntime_type qr C) vs] in
  cs_frame h h' /\ cs_heap_ok CT h' /\
  cs_env_ok CT h' (set_vars rΓ (update x (Iot (dom h)) (vars rΓ))) sΓ ambient.
Proof.
  intros HCT Hheap Henv HT Hx HTs Hvs Hctor Hqc Hargs Hresult qr h'.
  destruct (cs_constructor_wf _ _ _ HCT Hctor) as (Hbound & _ & fs & Hfs & _ & Hfields).
  pose proof (cs_created_bound ambient qc (cqualifier ctor) Hqc) as Hboundq.
  change (vpa_mutability_runtime_bound_agree qr (cqualifier ctor) = true) in Hboundq.
  assert (Hdom : C < dom CT).
  { exact (cs_sub_dom _ _ _ Hresult). }
  assert (Hparams : Forall2 (cs_value_ok CT h qr) vs (cparams ctor)).
  { apply (proj1 (cs_Forall2_map_right (qualified_type_subtype CT)
      (vpa_mutability_constructor_param qc) Ts (cparams ctor))) in Hargs.
    eapply cs_args_in with (mt := ConcreteState)
      (receiver := Build_qualified_type (qc2q qc) 0).
    - apply cs_created_qual.
    - eapply cs_args_ok; eassumption.
    - exact Hargs. }
  split; [apply cs_frame_alloc|]. split.
  - eapply cs_heap_alloc with (fs := fs); cbn; try eassumption.
    + unfold wf_rtypeuse. rewrite Hbound. auto.
    + eapply cs_Forall2_chain; [|exact Hparams|exact Hfields].
      intros v T fd Hv Hsub.
      rewrite cs_constructor_field_adapt in Hsub.
      apply (proj1 (cs_override_value CT h qr _ _ v Hboundq)).
      eapply cs_value_sub; [|exact Hsub].
      now apply (proj2 (cs_override_value CT h qr _ _ v Hboundq)).
  - eapply cs_env_update; eauto using cs_frame_alloc.
    eapply cs_value_sub; [|exact Hresult]. cbn [cs_value_ok].
    unfold wf_r_typable, r_type, h'.
    rewrite cs_alloc_lookup. cbn. split.
    + now apply base_refl.
    + apply cs_created_qual.
Qed.

Local Lemma cs_frame_env CT h h' rΓ sΓ qr :
  cs_frame h h' -> cs_env_ok CT h rΓ sΓ qr -> cs_env_ok CT h' rΓ sΓ qr.
Proof.
  intros HF Henv. split.
  - eapply cs_frame_receiver; eassumption.
  - destruct Henv as [_ Hvars]. eapply cs_frame_values; eassumption.
Qed.

Local Lemma cs_call_ok CT h h' rΓ rbody' sΓ ambient mt
    x y m zs ly C vs v Tx Ty Ts declared actual :
  wf_class_table CT -> cs_heap_ok CT h -> cs_env_ok CT h rΓ sΓ ambient ->
  runtime_getVal rΓ y = Some (Iot ly) -> r_basetype h ly = Some C ->
  runtime_lookup_list rΓ zs = Some vs ->
  runtime_getVal rbody' (mreturn (mbody actual)) = Some v ->
  static_getType sΓ x = Some Tx -> x <> 0 ->
  static_getType sΓ y = Some Ty -> static_getType_list sΓ zs = Some Ts ->
  FindMethodWithName CT (sctype Ty) m declared ->
  FindMethodWithName CT C m actual ->
  strict_assignability_method_scope (mscope (msignature declared)) ->
  (qualified_type_subtype CT Ty (cs_adapt mt Ty (mreceiver (msignature declared))) \/
   (sqtype Ty = RO /\ sqtype (mreceiver (msignature declared)) = RDM /\
    base_subtype CT (sctype Ty) (sctype (mreceiver (msignature declared))))) ->
  Forall2 (fun T U => qualified_type_subtype CT T (cs_adapt mt Ty U))
    Ts (mparams (msignature declared)) ->
  qualified_type_subtype CT (cs_adapt mt Ty (mret (msignature declared))) Tx ->
  (forall sbody sbody' qr,
    strict_assignability_method_scope (mscope (msignature actual)) ->
    stmt_typing CT sbody (mscope (msignature actual)) (mbody_stmt (mbody actual)) sbody' ->
    cs_heap_ok CT h -> cs_env_ok CT h (mkr_env (Iot ly :: vs)) sbody qr ->
    cs_frame h h' /\ cs_heap_ok CT h' /\ cs_env_ok CT h' rbody' sbody' qr) ->
  cs_frame h h' /\ cs_heap_ok CT h' /\
  cs_env_ok CT h' (set_vars rΓ (update x v (vars rΓ))) sΓ ambient.
Proof.
  intros HCT Hheap Henv Hy Hbase Hvs Hreturn HTx Hx HTy HTs Hdeclared Hactual
    Hstrict Hreceiver Hargs Hresult Hbody.
  unfold r_basetype in Hbase.
  destruct (runtime_getObj h ly) as [[[qr D] fields]|] eqn:Ho; [|discriminate].
  injection Hbase as <-.
  pose proof (cs_type_obj _ _ _ Ho) as Hrt. cbn in Hrt.
  destruct (cs_var_location _ _ _ _ _ _ _ _ _ Henv Hy HTy Ho) as [Hb Hq].
  cbn in Hb, Hq.
  destruct (cs_method_refine _ _ _ _ _ HCT Hb Hdeclared) as (child & Hchild & Hrefinement).
  assert (child = actual) by (eapply cs_method_unique; eassumption). subst child.
  destruct (cs_method_wf _ _ _ _ HCT Hactual) as (owner & Hwf & Howner & Hclass).
  rewrite <- Howner in Hclass.
  destruct (Hheap _ _ Ho) as [Hrtuse _]. cbn in Hrtuse.
  destruct (cs_refinement_values CT h _ qr _ _ HCT Hrtuse Hrefinement Hclass)
    as (Hq_in & Hargs_in & _).
  assert (Hargvals : Forall2 (cs_value_ok CT h qr) vs (mparams (msignature actual))).
  { apply Hargs_in.
    eapply cs_args_in with (mt := mt) (receiver := Ty); try eassumption.
    eapply cs_args_ok; eassumption. }
  assert (Hreceiverok : cs_value_ok CT h qr (Iot ly) (mreceiver (msignature actual))).
  { cbn. unfold wf_r_typable. rewrite Hrt. split; [exact Hclass|].
    apply Hq_in. eapply cs_receiver_in with (mt := mt) (receiver := Ty);
      try eassumption.
    eapply cs_var_ok; eassumption. }
  assert (Hstrict' : strict_assignability_method_scope (mscope (msignature actual))).
  { now rewrite (cs_refinement_scope _ _ _ Hrefinement). }
  destruct Hwf as (_ & sbody' & T & Htype & _ & HTret & Hsub & _).
  destruct (Hbody _ _ qr Hstrict' Htype Hheap) as (HF & Hheap' & Henv').
  { split; [exists ly, D; split; [reflexivity|exact Hrt]|].
    constructor; assumption. }
  split; [exact HF|]. split; [exact Hheap'|].
  eapply cs_env_update; try eassumption.
  eapply cs_value_sub; [|exact Hresult].
  eapply cs_value_out; [exact Hq|].
  destruct (cs_refinement_values CT h' _ qr _ _ HCT Hrtuse Hrefinement Hclass)
    as (_ & _ & Hresult_out).
  apply Hresult_out.
  eapply cs_value_sub; [|exact Hsub]. eapply cs_var_ok; eassumption.
Qed.

Local Lemma cs_strict_scope mt :
  method_scope_subtype mt ConcreteState \/ method_scope_subtype mt TransitiveState ->
  strict_assignability_method_scope mt.
Proof. intros [H|H]; inversion H; unfold strict_assignability_method_scope; auto. Qed.

(* Successful evaluations in the two strict scopes preserve the heap
   and frame typing invariants needed by later statements and calls. *)
Local Lemma cs_eval_preserves CT rΓ h s rΓ' h' :
  eval_stmt CT rΓ h s OK rΓ' h' ->
  forall sΓ sΓ' ambient mt,
    wf_class_table CT -> strict_assignability_method_scope mt ->
    stmt_typing CT sΓ mt s sΓ' ->
    cs_heap_ok CT h -> cs_env_ok CT h rΓ sΓ ambient ->
    cs_frame h h' /\ cs_heap_ok CT h' /\ cs_env_ok CT h' rΓ' sΓ' ambient.
Proof.
  intros Heval. remember OK as result eqn:Hresult in Heval.
  induction Heval; intros sΓ sΓ' ambient mt HCT Hstrict Htype HheapOk HenvOk;
    try discriminate.
  - inversion Htype; subst. auto using cs_frame_refl.
  - inversion Htype; subst. auto using cs_frame_refl, cs_env_local.
  - inversion Htype; subst. split; [apply cs_frame_refl|]. split; [exact HheapOk|].
    eapply cs_env_update; eauto using cs_frame_refl.
    eapply cs_value_sub; [|eassumption].
    eapply cs_expr_ok; eassumption.
  - inversion Htype; subst; try solve [destruct Hstrict; discriminate].
    + assert (Hwrite : cs_frame h (update_field h loc_x f val_y) /\
                       cs_heap_ok CT (update_field h loc_x f val_y)).
      { eapply cs_write_ok with (mt := ConcreteState); try eassumption.
        rewrite <- cs_field_type_adapt. eassumption. }
      destruct Hwrite as [HF HheapOk']. split; [exact HF|].
      split; [exact HheapOk'|]. eapply cs_frame_env; eassumption.
    + assert (Hwrite : cs_frame h (update_field h loc_x f val_y) /\
                       cs_heap_ok CT (update_field h loc_x f val_y)).
      { eapply cs_write_ok with (mt := TransitiveState); try eassumption.
        rewrite <- cs_field_type_adapt_ro. eassumption. }
      destruct Hwrite as [HF HheapOk']. split; [exact HF|].
      split; [exact HheapOk'|]. eapply cs_frame_env; eassumption.
  - inversion Htype; subst.
    assert (qthisr = ambient).
    { destruct HenvOk as [(l & D & Hthis' & Hrt) _].
      assert (l = l1) by congruence. subst l.
      unfold r_type in Hrt. unfold r_muttype in Hmut.
      destruct (runtime_getObj h l1) as [obj|]; [|discriminate].
      injection Hrt as Hty. rewrite Hty in Hmut. cbn in Hmut. congruence. }
    subst qthisr. eapply cs_new_ok; eassumption.
  - destruct Hfind as [Hfind Hbody].
    subst mbody mstmt mret rΓ' rΓ'''.
    inversion Htype; subst.
    + destruct Hscope as [Habs | [_ Hscope]].
      { subst mt. destruct Hstrict; discriminate. }
      eapply cs_call_ok with (mt := ConcreteState); try eassumption.
      * apply cs_strict_scope. now left.
      * intros. eapply IHHeval; eauto.
    + assert (mt = TransitiveState) by (destruct Hstrict; congruence).
      subst mt.
      eapply cs_call_ok with (mt := TransitiveState); try eassumption.
      * apply cs_strict_scope. now right.
      * intros. eapply IHHeval; eauto.
  - inversion Htype; subst.
    destruct (IHHeval1 eq_refl sΓ _ ambient mt HCT Hstrict Htype1 HheapOk HenvOk)
      as (HF1 & Hheap1 & Henv1).
    destruct (IHHeval2 eq_refl _ sΓ' ambient mt HCT Hstrict Htype2 Hheap1 Henv1)
      as (HF2 & Hheap2 & Henv2).
    split; [eauto using cs_frame_trans|auto].
Qed.

(* Abstract edges out of immutable objects carry immutable references. *)
Local Lemma cs_abstract_reachable_immutable CT h root l :
  cs_heap_ok CT h ->
  reachable_abs CT h root l ->
  (exists C vs, runtime_getObj h root = Some (mkObj (mkruntime_type Imm_r C) vs)) ->
  exists C vs, runtime_getObj h l = Some (mkObj (mkruntime_type Imm_r C) vs).
Proof.
  intros Hheap Hreach. induction Hreach.
  - trivial.
  - intros (D & vs & Himm). rewrite Himm in Hobj. injection Hobj as <- <- <-.
    destruct (Hheap _ _ Himm) as (_ & fs & Hfs & Hvals). cbn in *.
    destruct Hmut_abs as [(fd & Hfd & Hqf) | (fd & Hfd & Hqf)];
      pose proof (cs_field_in_collection _ _ _ _ _ Hfs Hfd) as Hnth;
      pose proof (cs_Forall2_nth _ _ _ _ _ _ Hvals Hfield Hnth) as Hv;
      unfold cs_field_type, cs_value_ok, wf_r_typable, r_type in Hv;
      destruct (runtime_getObj h l1) as [[[qr C] fields]|] eqn:Hloc;
      try contradiction;
      destruct Hv as [_ Hq]; cbn in Hq; rewrite Hqf in Hq;
      destruct qr; cbn in Hq; try contradiction; eauto.
  - eauto.
Qed.

Theorem concrete_state_preservation :
  forall CT sΓ rΓ h stmt rΓ' h' sΓ' root C0 vals0 l C qr vals f
    (Hroot_imm : runtime_getObj h root =
      Some (mkObj (mkruntime_type Imm_r C0) vals0))
    (Hreach : reachable_abs CT h root l)
    (Hwf : wf_r_config CT sΓ rΓ h)
    (Htyping : stmt_typing CT sΓ ConcreteState stmt sΓ')
    (Heval : eval_stmt CT rΓ h stmt OK rΓ' h')
    (Hobj_start : runtime_getObj h l =
      Some (mkObj (mkruntime_type qr C) vals)),
    exists vals',
      runtime_getObj h' l = Some (mkObj (mkruntime_type qr C) vals') /\
      nth_error vals f = nth_error vals' f.
Proof.
  intros CT sΓ rΓ h stmt rΓ' h' sΓ' root C0 vals0 l C qr vals f
    Hroot_imm Hreach Hwf Htyping Heval Hobj_start.
  pose proof (proj1 Hwf) as HCT.
  destruct (cs_config_from_wf _ _ _ _ Hwf) as (Hheap & ambient & Henv).
  assert (Hroot : exists D vs,
      runtime_getObj h root = Some (mkObj (mkruntime_type Imm_r D) vs)).
  { eauto. }
  destruct (cs_abstract_reachable_immutable _ _ _ _ Hheap Hreach Hroot)
    as (D & vs & Himm).
  assert (Hstrict : strict_assignability_method_scope ConcreteState) by now left.
  destruct (cs_eval_preserves _ _ _ _ _ _ Heval _ _ ambient _ HCT Hstrict Htyping Hheap Henv)
    as (HF & _).
  destruct (HF _ _ Hobj_start) as (o' & Ho' & _ & Hpreserved).
  assert (qr = Imm_r) by congruence.
  specialize (Hpreserved H). subst o'.
  exists vals. auto.
Qed.
