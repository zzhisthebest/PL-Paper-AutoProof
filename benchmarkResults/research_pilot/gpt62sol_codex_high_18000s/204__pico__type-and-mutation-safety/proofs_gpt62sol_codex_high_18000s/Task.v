Require Import Syntax Notations Helpers Typing Subtyping Bigstep ViewpointAdaptation.

From Stdlib Require Import List.

From Stdlib Require String.

Import ListNotations.

From Stdlib Require Import Lia Arith.PeanoNat.

Local Definition value_typed CT h ctx v T :=
  match v with
  | Null_a => True
  | Iot l => wf_r_typable CT h l T ctx
  end.

Local Definition field_typed CT h qr v fd :=
  match v with
  | Null_a => True
  | Iot l =>
      exists rt, r_type h l = Some rt /\
        base_subtype CT (rctype rt) (f_base_type (ftype fd)) /\
        qualifier_typable_heap (rqtype rt)
          (vpa_mutability_rec_fld qr (mutability (ftype fd)))
  end.

Local Definition types_preserved (h h' : heap) :=
  forall l rt, r_type h l = Some rt -> r_type h' l = Some rt.

Local Lemma type_at CT h l o T ctx :
  runtime_getObj h l = Some o ->
  wf_r_typable CT h l T ctx <->
  base_subtype CT (rctype (rt_type o)) (sctype T) /\
  qualifier_typable_context (rqtype (rt_type o)) (sqtype T) ctx.
Proof. unfold wf_r_typable, r_type; now intros ->. Qed.

Local Lemma rtype_exists h l rt :
  r_type h l = Some rt -> exists o, runtime_getObj h l = Some o /\ rt_type o = rt.
Proof.
  unfold r_type; destruct (runtime_getObj h l); inversion 1; eauto.
Qed.

Local Lemma type_at_loc CT h l T ctx :
  wf_r_typable CT h l T ctx ->
  exists rt, r_type h l = Some rt /\
    base_subtype CT (rctype rt) (sctype T) /\
    qualifier_typable_context (rqtype rt) (sqtype T) ctx.
Proof.
  unfold wf_r_typable; destruct (r_type h l); simpl; eauto; tauto.
Qed.

Local Lemma qualifier_trans a b c :
  q_subtype a b -> q_subtype b c -> q_subtype a c.
Proof.
  destruct 1; auto using q_subtype.
  inversion 1; subst; auto using q_subtype.
Qed.

Local Lemma qsub_parts CT T U :
  qualified_type_subtype CT T U ->
  base_subtype CT (sctype T) (sctype U) /\ q_subtype (sqtype T) (sqtype U).
Proof.
  induction 1.
  - auto.
  - destruct IHqualified_type_subtype1 as [Hb1 Hq1],
      IHqualified_type_subtype2 as [Hb2 Hq2].
    split; [eapply base_trans; eassumption|].
    eauto using qualifier_trans.
  - split; [apply base_refl|apply q_refl]; assumption.
Qed.

Local Lemma qualifier_sub qr ctx q1 q2 :
  q_subtype q1 q2 ->
  qualifier_typable_context qr q1 ctx ->
  qualifier_typable_context qr q2 ctx.
Proof. destruct 1; auto; destruct qr, ctx; simpl; tauto. Qed.

Local Lemma value_sub CT h ctx v T U :
  qualified_type_subtype CT T U ->
  value_typed CT h ctx v T ->
  value_typed CT h ctx v U.
Proof.
  intros Hsub; destruct (qsub_parts _ _ _ Hsub) as [Hb Hq]; destruct v; simpl; auto.
  unfold wf_r_typable; destruct (r_type h l) as [rt|]; try tauto.
  intros [Hbase Hqual]; split; eauto using base_trans, qualifier_sub.
Qed.

Local Lemma value_transport CT h h' ctx v T :
  types_preserved h h' -> value_typed CT h ctx v T ->
  value_typed CT h' ctx v T.
Proof.
  intros Hkeep; destruct v; simpl; auto.
  intros [rt [Hr Hty]]%type_at_loc; unfold wf_r_typable; now rewrite (Hkeep _ _ Hr).
Qed.

Local Lemma field_transport CT h h' qr v fd :
  types_preserved h h' -> field_typed CT h qr v fd ->
  field_typed CT h' qr v fd.
Proof. destruct v; simpl; firstorder. Qed.

Local Lemma raw_field_typed CT h qr v fd :
  (match v with
  | Null_a => True
  | Iot l =>
      match runtime_getObj h l with
      | Some _ => field_typed CT h qr (Iot l) fd
      | None => False
      end
  end) <-> field_typed CT h qr v fd.
Proof.
  destruct v as [|l]; [tauto|].
  simpl; unfold r_type; destruct (runtime_getObj h l); simpl; firstorder discriminate.
Qed.

Local Lemma obj_at CT h l o :
  runtime_getObj h l = Some o ->
  wf_obj CT h l <->
  wf_rtypeuse CT (rqtype (rt_type o)) (rctype (rt_type o)) /\
  exists fs, CollectFields CT (rctype (rt_type o)) fs /\
    length (fields_map o) = length fs /\
    Forall2 (field_typed CT h (rqtype (rt_type o))) (fields_map o) fs.
Proof.
  intros Ho; unfold wf_obj; rewrite Ho; split;
    intros [Htype [fs [Hfs [Hlen Hall]]]];
    split; [exact Htype|exists fs; split; [exact Hfs|split; [exact Hlen|]]
           |exact Htype|exists fs; split; [exact Hfs|split; [exact Hlen|]]];
    eapply Forall2_impl; [|exact Hall| |exact Hall]; intros v fd Hv.
  - exact (proj1 (raw_field_typed CT h _ v fd) Hv).
  - exact (proj2 (raw_field_typed CT h _ v fd) Hv).
Qed.

Local Lemma class_wf CT C def :
  wf_class_table CT -> find_class CT C = Some def ->
  wf_class CT def /\ cname (signature def) = C.
Proof.
  intros [Hall [_ [_ Hname]]] Hfind; split; eauto.
  eapply Forall_forall; [exact Hall|now apply (nth_error_In CT C)].
Qed.

Local Lemma class_agrees CT C D rt :
  wf_class_table CT ->
  base_subtype CT C D ->
  wf_rtypeuse CT rt C -> wf_rtypeuse CT rt D.
Proof.
  intros Hct Hsub; induction Hsub as [|CT C D E ? IH1 ? IH2|CT C D HC HD HP];
    auto.
  unfold parent_lookup in HP.
  destruct (find_class CT C) as [def|] eqn:HCf; try discriminate.
  destruct (class_wf _ _ _ Hct HCf) as [Hdef Hname].
  assert (Hagree :
    match bound CT D with
    | Some qc =>
        exists fs, CollectFields CT C fs /\
          (class_qualifier (signature def) = qc \/ qc = RDM_c) /\
          Forall (wf_field CT) fs
    | None => CollectFields CT C []
    end).
  { inversion Hdef; subst; try congruence.
    assert (superC = D) by congruence; subst superC; exact (proj2 (proj2 (proj2 H))). }
  unfold wf_rtypeuse, bound at 1; rewrite HCf.
  unfold wf_rtypeuse.
  destruct (bound CT D) as [qc|] eqn:HDf.
  - destruct Hagree as [fs [_ [[Heq|Heq] _]]]; rewrite Heq;
      destruct rt; simpl; intuition.
  - unfold bound in HDf; destruct (find_class CT D) eqn:Hfind; try discriminate.
    apply nth_error_None in Hfind; lia.
Qed.

Local Lemma fields_unique CT C fs gs :
  CollectFields CT C fs -> CollectFields CT C gs -> fs = gs.
Proof.
  intros H; revert gs; induction H; intros gs Hg; inversion Hg; subst;
    try congruence.
  assert (def = def0) by congruence; subst def0.
  assert (parent = parent0) by congruence; subst parent0.
  f_equal; eauto.
Qed.

Local Lemma fields_lookup_unique CT C f fd gd :
  FieldLookup CT C f fd -> FieldLookup CT C f gd -> fd = gd.
Proof.
  inversion 1; inversion 1; subst.
  assert (fields = fields0) by (eapply fields_unique; eassumption); congruence.
Qed.

Local Lemma fields_inherit CT C D f fd :
  base_subtype CT C D -> FieldLookup CT D f fd -> FieldLookup CT C f fd.
Proof.
  induction 1 as [|CT C D E ? IH1 ? IH2|CT C D HC HD HP]; auto.
  inversion 1 as [? ? fs ? ? Hfs Hget]; subst.
  unfold parent_lookup in HP.
  destruct (find_class CT C) as [def|] eqn:Hfind; try discriminate.
  eapply FL_Found with (fields := fs ++ Syntax.fields (body def)).
  - econstructor; eauto.
  - unfold gget in *; rewrite nth_error_app1; [apply nth_error_Some; congruence|exact Hget].
Qed.

Local Lemma forall2_at {A B} (P : A -> B -> Prop) xs ys i x y :
  Forall2 P xs ys -> nth_error xs i = Some x -> nth_error ys i = Some y -> P x y.
Proof.
  intros H; revert i; induction H; intros [|i]; simpl; try discriminate; eauto.
  intros Hx Hy; inversion Hx; inversion Hy; subst; assumption.
Qed.

Local Lemma forall2_build {A B} (P : A -> B -> Prop) xs ys :
  length xs = length ys ->
  (forall i x y, nth_error xs i = Some x -> nth_error ys i = Some y -> P x y) ->
  Forall2 P xs ys.
Proof.
  revert ys; induction xs; intros [|y ys] Hlen Hall; simpl in Hlen;
    try discriminate; constructor.
  - exact (Hall 0 _ _ eq_refl eq_refl).
  - apply IHxs; [lia|intros i; apply (Hall (S i))].
Qed.

Local Lemma forall2_size {A B} (P : A -> B -> Prop) xs ys :
  Forall2 P xs ys -> length xs = length ys.
Proof. induction 1; simpl; congruence. Qed.

Local Lemma update_size {A} (xs : list A) i x :
  length (update i x xs) = length xs.
Proof. revert i; induction xs; intros [|i]; simpl; congruence. Qed.

Local Lemma update_same {A} (xs : list A) i x :
  i < length xs -> nth_error (update i x xs) i = Some x.
Proof.
  revert i; induction xs; intros [|i]; simpl; try lia; auto.
  intros; apply IHxs; lia.
Qed.

Local Lemma update_other {A} (xs : list A) i j x :
  j <> i -> nth_error (update i x xs) j = nth_error xs j.
Proof.
  revert i j; induction xs; intros [|i] [|j]; simpl; auto.
  - contradiction.
Qed.

Local Lemma forall2_update {A B} (P : A -> B -> Prop) xs ys i x y :
  Forall2 P xs ys -> nth_error ys i = Some y -> P x y ->
  Forall2 P (update i x xs) ys.
Proof.
  intros H; revert i; induction H; intros [|i] Hy Hxy; simpl in *;
    try discriminate; constructor; eauto.
  now injection Hy as ->.
Qed.

Local Lemma wf_static_at CT s i T :
  wf_senv CT s -> static_getType s i = Some T -> wf_stypeuse CT (sqtype T) (sctype T).
Proof.
  intros [_ Hall] Hi; rewrite Forall_forall in Hall.
  apply (Hall T); now apply (nth_error_In s i).
Qed.

Local Lemma static_no_lost CT q C :
  wf_stypeuse CT q C -> q <> Lost.
Proof.
  intros H ->; unfold wf_stypeuse in H.
  destruct (bound CT C) as [[]|]; simpl in H; try tauto;
    destruct H as [H _]; inversion H; contradiction || discriminate.
Qed.

Local Lemma wf_typing_input CT s mt st s' :
  stmt_typing CT s mt st s' -> wf_senv CT s.
Proof. destruct 1; assumption. Qed.

(* A typed frame records the receiver's runtime qualifier and types each slot. *)
Local Definition frame_typed CT h s r l ctx :=
  runtime_getVal r 0 = Some (Iot l) /\
  r_muttype h l = Some ctx /\
  Forall2 (value_typed CT h ctx) (vars r) s.

Local Lemma receiver_lookup r : get_this_var_mapping (vars r) =
  match runtime_getVal r 0 with Some (Iot l) => Some l | _ => None end.
Proof. destruct r as [[|[] vs]]; reflexivity. Qed.

Local Lemma receiver_type h l ctx :
  r_muttype h l = Some ctx <->
  exists rt, r_type h l = Some rt /\ rqtype rt = ctx.
Proof.
  unfold r_muttype, r_type; destruct (runtime_getObj h l) as [o|].
  - split; [intros H; exists (rt_type o); split; congruence|intros [rt [Heq Hctx]]; congruence].
  - split; [discriminate|intros [rt [Heq _]]; discriminate].
Qed.

Local Lemma config_frame CT s r h :
  wf_r_config CT s r h ->
  wf_class_table CT /\ wf_heap CT h /\ wf_senv CT s /\
  exists l ctx, frame_typed CT h s r l ctx.
Proof.
  intros [Hct [Hheap [[_ [[l [Hthis Hloc]] _]] [Hs [Hlen Htyping]]]]].
  split; [exact Hct|split; [exact Hheap|split; [exact Hs|]]].
  pose proof Hthis as Hreceiver.
  rewrite receiver_lookup in Hthis.
    destruct (runtime_getVal r 0) as [[|l']|] eqn:Hr; try discriminate.
    inversion Hthis; subst l'.
    assert (Hex : runtime_getObj h l <> None) by (apply nth_error_Some; exact Hloc).
    destruct (runtime_getObj h l) as [o|] eqn:Ho; [|contradiction].
    assert (Hctx : r_muttype h l = Some (rqtype (rt_type o)))
      by (unfold r_muttype; rewrite Ho; reflexivity).
    exists l, (rqtype (rt_type o)); repeat split; try assumption.
    apply forall2_build; [symmetry; exact Hlen|].
    intros i v T Hv HT.
    assert (Hi : i < length s) by (apply nth_error_Some; congruence).
    specialize (Htyping l _ Hreceiver Hctx i Hi T HT).
    change (runtime_getVal r i = Some v) in Hv.
    rewrite Hv in Htyping; exact Htyping.
Qed.

Local Lemma typed_value_present CT h ctx v T :
  value_typed CT h ctx v T ->
  match v with
  | Null_a => True
  | Iot l => match runtime_getObj h l with Some _ => True | None => False end
  end.
Proof.
  destruct v; simpl; auto.
  intros [rt [Hrt _]]%type_at_loc.
  destruct (rtype_exists _ _ _ Hrt) as [o [-> _]]; exact I.
Qed.

Local Lemma frame_config CT s r h l ctx :
  wf_class_table CT -> wf_heap CT h -> wf_senv CT s ->
  frame_typed CT h s r l ctx -> wf_r_config CT s r h.
Proof.
  intros Hct Hheap Hs [Hr [Hctx Hall]].
  pose proof (forall2_size _ _ _ Hall) as Hlen.
  assert (Hthis : get_this_var_mapping (vars r) = Some l)
    by (rewrite receiver_lookup Hr; reflexivity).
  unfold wf_r_config; split; [exact Hct|split; [exact Hheap|]].
  split.
  - unfold wf_renv; split.
      assert (0 < length (vars r)) by
        (apply nth_error_Some; change (runtime_getVal r 0 <> None); congruence).
      lia.
    + split.
      * exists l; split; [exact Hthis|].
        destruct (proj1 (receiver_type _ _ _) Hctx) as [rt [Hrt _]].
        destruct (rtype_exists _ _ _ Hrt) as [o [Ho _]].
        apply nth_error_Some; change (runtime_getObj h l <> None); congruence.
      * clear Hr Hthis Hlen Hs; induction Hall.
        -- apply Forall_nil.
        -- apply Forall_cons; [exact (typed_value_present CT h ctx _ _ H)|assumption].
  - split; [exact Hs|split; [symmetry; exact Hlen|]].
    intros l' ctx' Hl' Hctx' i Hi T HT.
    assert (l' = l) by congruence; subst l'.
    assert (ctx' = ctx) by congruence; subst ctx'.
    assert (Hsome : nth_error (vars r) i <> None) by (apply nth_error_Some; lia).
    unfold runtime_getVal; destruct (nth_error (vars r) i) as [v|] eqn:Hv;
      [|contradiction].
    exact (forall2_at _ _ _ _ _ _ Hall Hv HT).
Qed.

Local Lemma frame_value CT h s r l ctx i v T :
  frame_typed CT h s r l ctx ->
  static_getType s i = Some T ->
  runtime_getVal r i = Some v ->
  value_typed CT h ctx v T.
Proof. intros [_ [_ Hall]] HT Hv; eapply forall2_at; eassumption. Qed.

Local Lemma frame_update CT h s r l ctx x v T :
  frame_typed CT h s r l ctx -> x <> 0 ->
  static_getType s x = Some T -> value_typed CT h ctx v T ->
  frame_typed CT h s (set_vars r (update x v (vars r))) l ctx.
Proof.
  intros [Hr [Hctx Hall]] Hx HT Hv.
  split.
  - change (nth_error (update x v (vars r)) 0 = Some (Iot l)).
    rewrite update_other; [congruence|exact Hr].
  - split; [exact Hctx|].
    change (Forall2 (value_typed CT h ctx) (update x v (vars r)) s).
    eapply forall2_update; eassumption.
Qed.

Local Lemma frame_transport CT h h' s r l ctx :
  types_preserved h h' ->
  frame_typed CT h s r l ctx -> frame_typed CT h' s r l ctx.
Proof.
  intros Hkeep [Hr [Hctx Hall]]; split; [exact Hr|split].
  - apply receiver_type in Hctx; apply receiver_type.
    destruct Hctx as [rt [Hrt Hq]]; exists rt; auto.
  - induction Hall; constructor; eauto using value_transport.
Qed.

Local Lemma frame_arguments CT h s r l ctx args vals Ts :
  frame_typed CT h s r l ctx ->
  runtime_lookup_list r args = Some vals ->
  static_getType_list s args = Some Ts ->
  Forall2 (value_typed CT h ctx) vals Ts.
Proof.
  intros Hframe; unfold runtime_lookup_list, static_getType_list.
  revert vals Ts; induction args as [|a args IH]; simpl; intros vals Ts Hv HT.
  - inversion Hv; inversion HT; constructor.
  - destruct (runtime_getVal r a) as [v|] eqn:Hva;
      destruct (static_getType s a) as [T|] eqn:HTa;
      destruct (mapM (runtime_getVal r) args) as [vs|] eqn:Hvs;
      destruct (mapM (static_getType s) args) as [ts|] eqn:Hts;
      try discriminate.
    inversion Hv; inversion HT; subst; constructor; eauto using frame_value.
Qed.

Local Lemma lookup_field_at CT C D fs f fd :
  base_subtype CT C D -> CollectFields CT C fs ->
  sf_def_rel CT D f fd -> nth_error fs f = Some fd.
Proof.
  intros Hsub Hfs Hfd.
  pose proof (fields_inherit _ _ _ _ _ Hsub Hfd) as Hget.
  inversion Hget as [? ? gs ? ? Hgs Hnth]; subst.
  now rewrite (fields_unique _ _ _ _ Hfs Hgs).
Qed.

Local Definition adapt_field (readonly : bool) :=
  if readonly then vpa_mutability_stype_fld_readonly_state
  else vpa_mutability_stype_fld_abstract_state.

Local Lemma read_qualifier ro ctx qr qv qs qf :
  qualifier_typable_context qr qs ctx ->
  qualifier_typable_heap qv (vpa_mutability_rec_fld qr qf) ->
  qualifier_typable_context qv (adapt_field ro qs qf) ctx.
Proof. destruct ro, ctx, qr, qv, qs, qf; simpl; tauto. Qed.

Local Lemma expr_field_value CT h s r l ctx x f lx o v T fd ro :
  wf_heap CT h -> frame_typed CT h s r l ctx ->
  static_getType s x = Some T -> sf_def_rel CT (sctype T) f fd ->
  runtime_getVal r x = Some (Iot lx) ->
  runtime_getObj h lx = Some o -> getVal (fields_map o) f = Some v ->
  value_typed CT h ctx v
    (Build_qualified_type (adapt_field ro (sqtype T) (mutability (ftype fd)))
       (f_base_type (ftype fd))).
Proof.
  intros Hheap Hframe HT Hfd Hx Ho Hv.
  pose proof (frame_value _ _ _ _ _ _ _ _ _ Hframe HT Hx) as Hrecv.
  apply (type_at CT h lx o T ctx Ho) in Hrecv as [Hb Hq].
  assert (Hdom : lx < length h) by (apply nth_error_Some; change (runtime_getObj h lx <> None); congruence).
  destruct (proj1 (obj_at _ _ _ _ Ho) (Hheap _ Hdom)) as [_ [fs [Hfs [_ Hall]]]].
  pose proof (lookup_field_at _ _ _ _ _ _ Hb Hfs Hfd) as Hlookup.
  pose proof (forall2_at _ _ _ _ _ _ Hall Hv Hlookup) as Htyped.
  destruct v; [exact I|].
  destruct Htyped as [rt [Hrt [Hbase Hqual]]].
  simpl; unfold wf_r_typable; rewrite Hrt; split; simpl; eauto using read_qualifier.
Qed.

Local Lemma expr_value CT h s r l ctx mt e v T :
  wf_heap CT h -> frame_typed CT h s r l ctx ->
  expr_has_type CT s mt e T -> eval_expr CT r h e v OK r h ->
  value_typed CT h ctx v T.
Proof.
  intros Hheap Hframe Htyping Heval.
  inversion Htyping; subst; inversion Heval; subst; try exact I.
  - eauto using frame_value.
  - eapply (expr_field_value CT h s r l ctx x f v0 o v T0 fDef false); eassumption.
  - eapply (expr_field_value CT h s r l ctx x f v0 o v T0 fDef true); eassumption.
Qed.

(* A field write uses the inherited declaration at the runtime receiver. *)
Local Lemma write_qualifier ro ctx qr qv qx qy qf :
  qualifier_typable_context qr qx ctx ->
  qualifier_typable_context qv qy ctx ->
  qy <> Lost ->
  q_subtype qy (adapt_field ro qx qf) ->
  qualifier_typable_heap qv (vpa_mutability_rec_fld qr qf).
Proof.
  destruct ro, ctx, qr, qv, qx, qy, qf; simpl; intros Hx Hy Hlost Hsub;
    try contradiction; try exact I; inversion Hsub; congruence.
Qed.

Local Lemma write_value CT h s r l ctx x y lx o v Tx Ty fd ro :
  frame_typed CT h s r l ctx -> wf_senv CT s ->
  static_getType s x = Some Tx -> static_getType s y = Some Ty ->
  runtime_getVal r x = Some (Iot lx) -> runtime_getVal r y = Some v ->
  runtime_getObj h lx = Some o ->
  qualified_type_subtype CT Ty
    (Build_qualified_type (adapt_field ro (sqtype Tx) (mutability (ftype fd)))
       (f_base_type (ftype fd))) ->
  field_typed CT h (rqtype (rt_type o)) v fd.
Proof.
  intros Hframe Hs HTx HTy Hx Hy Ho Hsub.
  destruct v as [|lv]; [exact I|].
  pose proof (frame_value _ _ _ _ _ _ _ _ _ Hframe HTx Hx) as Hrecv.
  pose proof (frame_value _ _ _ _ _ _ _ _ _ Hframe HTy Hy) as Hval.
  apply (type_at CT h lx o Tx ctx Ho) in Hrecv as [_ Hq].
  destruct (type_at_loc _ _ _ _ _ Hval) as [rt [Hrt [Hb Hqual]]].
  destruct (qsub_parts _ _ _ Hsub) as [Hbsub Hqsub]; simpl in Hbsub, Hqsub.
  exists rt; split; [exact Hrt|split; [eapply base_trans; eassumption|]].
  eapply write_qualifier; [exact Hq|exact Hqual| |exact Hqsub].
  eapply static_no_lost, wf_static_at; eassumption.
Qed.

Local Lemma update_object_lookup h l f v o i :
  runtime_getObj h l = Some o ->
  runtime_getObj (update_field h l f v) i =
  if Nat.eq_dec i l then Some (set_fields_map o (update f v (fields_map o)))
  else runtime_getObj h i.
Proof.
  intros Ho; unfold update_field; rewrite Ho; unfold runtime_getObj in *.
  destruct (Nat.eq_dec i l) as [->|Hneq].
  - apply update_same, nth_error_Some; congruence.
  - now apply update_other.
Qed.

Local Lemma update_field_types h l f v :
  types_preserved h (update_field h l f v).
Proof.
  intros i rt Hrt; destruct (runtime_getObj h l) as [o|] eqn:Ho.
  - unfold r_type in *; rewrite (update_object_lookup _ _ _ _ _ _ Ho).
    destruct (Nat.eq_dec i l) as [->|]; [rewrite Ho in Hrt|]; exact Hrt.
  - unfold update_field; now rewrite Ho.
Qed.

Local Lemma update_field_heap CT h l f v o C fd :
  wf_heap CT h -> runtime_getObj h l = Some o ->
  base_subtype CT (rctype (rt_type o)) C -> sf_def_rel CT C f fd ->
  field_typed CT h (rqtype (rt_type o)) v fd ->
  wf_heap CT (update_field h l f v).
Proof.
  intros Hheap Ho Hb Hlookup Hv i Hi.
  unfold update_field in Hi; rewrite Ho update_size in Hi.
  assert (Hex : runtime_getObj h i <> None) by (apply nth_error_Some; exact Hi).
  destruct (runtime_getObj h i) as [old|] eqn:Hold; [|contradiction].
  destruct (proj1 (obj_at _ _ _ _ Hold) (Hheap _ Hi))
    as [Hrt [fs [Hfs [Hlen Hall]]]].
  pose proof (update_field_types h l f v) as Hkeep.
  assert (Hall' : Forall2 (field_typed CT (update_field h l f v) (rqtype (rt_type old)))
    (fields_map old) fs).
  { eapply Forall2_impl; [|exact Hall].
    intros; eauto using field_transport. }
  pose proof (update_object_lookup h l f v o i Ho) as Hget.
  destruct (Nat.eq_dec i l) as [->|Hneq].
  - assert (old = o) by congruence; subst old.
    apply (proj2 (obj_at _ _ _ _ Hget)).
    split; [exact Hrt|exists fs; split; [exact Hfs|split]].
    + simpl; now rewrite update_size.
    + simpl; eapply forall2_update; [exact Hall'| |eapply field_transport; eassumption].
      exact (lookup_field_at _ _ _ _ _ _ Hb Hfs Hlookup).
  - rewrite Hold in Hget; apply (proj2 (obj_at _ _ _ _ Hget)).
    split; [exact Hrt|exists fs; auto].
Qed.

Local Lemma assignability_sound ctx qr qs a :
  qualifier_typable_context qr qs ctx ->
  (vpa_assignability qs a = Assignable \/ vpa_assignability_cs_ts qs a = Assignable) ->
  runtime_vpa_assignability qr a = Assignable.
Proof. destruct ctx, qr, qs, a; simpl; intuition discriminate. Qed.

Local Lemma typed_write_assignable CT h s r l ctx x f lx o Tx a a' :
  frame_typed CT h s r l ctx -> static_getType s x = Some Tx ->
  runtime_getVal r x = Some (Iot lx) -> runtime_getObj h lx = Some o ->
  sf_assignability_rel CT (sctype Tx) f a ->
  sf_assignability_rel CT (rctype (rt_type o)) f a' ->
  (vpa_assignability (sqtype Tx) a = Assignable \/
    vpa_assignability_cs_ts (sqtype Tx) a = Assignable) ->
  runtime_vpa_assignability (rqtype (rt_type o)) a' = Assignable.
Proof.
  intros Hframe HT Hx Ho [fd [Hfd <-]] [gd [Hgd <-]] Hassign.
  pose proof (frame_value _ _ _ _ _ _ _ _ _ Hframe HT Hx) as Hrecv.
  apply (type_at CT h lx o Tx ctx Ho) in Hrecv as [Hb Hq].
  pose proof (fields_inherit _ _ _ _ _ Hb Hfd) as Hfd'.
  assert (fd = gd) by (eapply fields_lookup_unique; eassumption); subst gd.
  eapply assignability_sound; eassumption.
Qed.

(* Allocation checks constructor arguments before extending the heap. *)
Local Lemma wf_constructor_lookup CT C sig :
  wf_class_table CT -> constructor_sig_lookup CT C = Some sig ->
  wf_constructor CT C sig.
Proof.
  intros Hct Hfind; unfold constructor_sig_lookup, constructor_def_lookup in Hfind.
  destruct (find_class CT C) as [def|] eqn:HC; try discriminate.
  injection Hfind as <-.
  destruct (class_wf _ _ _ Hct HC) as [Hwf Hname].
  inversion Hwf; subst.
  - destruct Hwf_ctor as [_ [_ [Hbound [Hparams Hfields]]]].
    unfold wf_constructor; rewrite Hparams; split; [symmetry; exact Hbound|].
    split; [constructor|]; exists []; auto using Forall2_nil.
  - apply (proj1 H).
Qed.

Local Lemma new_object_lookup h o :
  runtime_getObj (h ++ [o]) (length h) = Some o.
Proof. unfold runtime_getObj; rewrite nth_error_app2; [lia|now rewrite Nat.sub_diag]. Qed.

Local Lemma append_object_types h o :
  types_preserved h (h ++ [o]).
Proof.
  intros l rt Hrt; unfold r_type in *.
  destruct (runtime_getObj h l) as [old|] eqn:Ho; try discriminate.
  assert (Hdom : l < length h) by (apply nth_error_Some; change (runtime_getObj h l <> None); congruence).
  unfold runtime_getObj in *; rewrite nth_error_app1; [exact Hdom|now rewrite Ho].
Qed.

Local Lemma append_object_heap CT h o fs :
  wf_heap CT h ->
  wf_rtypeuse CT (rqtype (rt_type o)) (rctype (rt_type o)) ->
  CollectFields CT (rctype (rt_type o)) fs ->
  Forall2 (field_typed CT h (rqtype (rt_type o))) (fields_map o) fs ->
  wf_heap CT (h ++ [o]).
Proof.
  intros Hheap Hrt Hfs Hall i Hi.
  pose proof (append_object_types h o) as Hkeep.
  rewrite length_app in Hi; simpl in Hi.
  destruct (Nat.lt_ge_cases i (length h)) as [Hdom|Hdom].
  - assert (Hget : runtime_getObj (h ++ [o]) i = runtime_getObj h i).
    { unfold runtime_getObj; now apply nth_error_app1. }
    assert (Hex : runtime_getObj h i <> None) by (apply nth_error_Some; exact Hdom).
    destruct (runtime_getObj h i) as [old|] eqn:Hold; [|contradiction].
    destruct (proj1 (obj_at _ _ _ _ Hold) (Hheap _ Hdom))
      as [Htype [gs [Hgs [Hlen Hvals]]]].
    apply (proj2 (obj_at _ _ _ _ Hget)).
    split; [exact Htype|exists gs; split; [exact Hgs|split; [exact Hlen|]]].
    eapply Forall2_impl; [|exact Hvals]; intros; eauto using field_transport.
  - assert (i = length h) by lia; subst i.
    apply (proj2 (obj_at _ _ _ _ (new_object_lookup h o))).
    split; [exact Hrt|exists fs; split; [exact Hfs|split]].
    + eapply forall2_size; eassumption.
    + eapply Forall2_impl; [|exact Hall]; intros; eauto using field_transport.
Qed.

Local Lemma creation_qualifiers ctx qv req boundq qp qf :
  vpa_mutability_bound (qc2q req) boundq = qc2q req ->
  qualifier_typable_context qv (vpa_mutability_qq_abstract_state (qc2q req) qp) ctx ->
  q_subtype (vpa_mutability_qq_abstract_state (qc2q boundq) qp)
    (vpa_mutability_constructor_fld boundq qf) ->
  qualifier_typable_heap qv (vpa_mutability_rec_fld
    (vpa_mutability_object_creation ctx req) qf).
Proof.
  destruct ctx, qv, req, boundq, qp, qf; simpl; intros Ha Hq Hsub;
    try discriminate; try contradiction; try exact I;
    inversion Hsub; congruence.
Qed.

Local Lemma creation_fields CT h ctx req b vals ps fs :
  vpa_mutability_bound (qc2q req) b = qc2q req ->
  Forall2 (value_typed CT h ctx) vals (map (vpa_mutability_constructor_param req) ps) ->
  Forall2 (fun p fd => qualified_type_subtype CT
    (vpa_mutability_constructor_param b p)
    (Build_qualified_type (vpa_mutability_constructor_fld b (mutability (ftype fd)))
      (f_base_type (ftype fd)))) ps fs ->
  Forall2 (field_typed CT h (vpa_mutability_object_creation ctx req)) vals fs.
Proof.
  intros Ha Hv Hfs; revert vals Hv; induction Hfs; intros vals Hv.
  - inversion Hv; constructor.
  - simpl in Hv; inversion Hv as [|v p vs ps Hv' Htail]; subst.
    constructor; [|now apply IHHfs].
    destruct v; [exact I|].
    destruct (type_at_loc _ _ _ _ _ Hv') as [rt [Hrt [Hb Hq]]].
    destruct (qsub_parts _ _ _ H) as [Hbase Hqual]; simpl in *.
    exists rt; split; [exact Hrt|split; [eapply base_trans; eassumption|]].
    eapply creation_qualifiers; eassumption.
Qed.

Local Lemma value_list_sub CT h ctx vals Ts Us :
  Forall2 (value_typed CT h ctx) vals Ts ->
  Forall2 (qualified_type_subtype CT) Ts Us ->
  Forall2 (value_typed CT h ctx) vals Us.
Proof.
  intros Hv; revert Us; induction Hv; intros Us Hsub; inversion Hsub; subst;
    constructor; eauto using value_sub.
Qed.

Local Lemma creation CT h ctx req C sig vals argtypes :
  wf_class_table CT -> wf_heap CT h -> constructor_sig_lookup CT C = Some sig ->
  vpa_mutability_bound (qc2q req) (cqualifier sig) = qc2q req ->
  Forall2 (value_typed CT h ctx) vals argtypes ->
  Forall2 (qualified_type_subtype CT) argtypes
    (map (vpa_mutability_constructor_param req) (cparams sig)) ->
  let o := mkObj (mkruntime_type (vpa_mutability_object_creation ctx req) C) vals in
  wf_heap CT (h ++ [o]) /\
  value_typed CT (h ++ [o]) ctx (Iot (length h)) (Build_qualified_type (qc2q req) C).
Proof.
  intros Hct Hheap Hsig Hadapt Hvals Hsub o.
  destruct (wf_constructor_lookup _ _ _ Hct Hsig) as [Hb [_ [fs [Hfs [_ Hfields]]]]].
  assert (Hdom : C < length CT).
  { unfold bound in Hb; destruct (find_class CT C) eqn:HC; try discriminate.
    apply nth_error_Some; change (find_class CT C <> None); congruence. }
  split.
  - apply (append_object_heap _ _ _ fs); try assumption.
    + simpl; unfold wf_rtypeuse; rewrite Hb; split; [exact Hdom|].
      destruct ctx, req, (cqualifier sig); simpl in *; reflexivity || discriminate.
    + simpl; eapply creation_fields; [exact Hadapt|eapply value_list_sub; eassumption|exact Hfields].
  - simpl; apply (proj2 (type_at _ _ _ _ _ _ (new_object_lookup h o))).
    split; [now apply base_refl|destruct ctx, req; exact I].
Qed.

(* Dispatch respects the inherited signature in the actual receiver's context. *)
Local Lemma find_method_unique CT C m d e :
  FindMethodWithName CT C m d -> FindMethodWithName CT C m e -> d = e.
Proof.
  intros Hd; revert e; induction Hd; intros e He; inversion He; subst;
    assert (def = def0) by congruence; subst def0; try congruence.
  assert (parent = parent0) by congruence; subst parent0; auto.
Qed.

Local Lemma method_here_wf CT C def m md :
  wf_class_table CT ->
  find_class CT C = Some def ->
  gget_method (methods (body def)) m = Some md ->
  wf_method CT C md /\ mname (msignature md) = m.
Proof.
  intros Hct HC Hget; destruct (class_wf _ _ _ Hct HC) as [Hwf Hname].
  unfold gget_method in Hget.
  apply find_some in Hget as [Hin Hmatch].
  split.
  - inversion Hwf; subst.
    + rewrite Hno_methods in Hin; contradiction.
    + pose proof (proj1 (proj2 H)) as Hall; rewrite Forall_forall in Hall; now apply Hall.
  - now apply Nat.eqb_eq.
Qed.

Local Lemma subtype_domain CT C D :
  base_subtype CT C D -> C < length CT /\ D < length CT.
Proof. induction 1; intuition. Qed.

Local Lemma find_class_domain CT C def :
  find_class CT C = Some def -> C < length CT.
Proof. intros H; apply nth_error_Some; change (find_class CT C <> None); congruence. Qed.

Local Lemma method_found_wf CT C m md :
  wf_class_table CT -> FindMethodWithName CT C m md ->
  wf_method CT (sctype (mreceiver (msignature md))) md /\
  base_subtype CT C (sctype (mreceiver (msignature md))).
Proof.
  intros Hct Hfind; induction Hfind.
  - subst own_methods.
    destruct (method_here_wf _ _ _ _ _ Hct Hfind Hget_method) as [Hwf _].
    assert (Hclass : sctype (mreceiver (msignature mdef)) = C).
    { destruct Hwf as [_ [s' [T [_ [_ [_ [_ [_ [Hclass _]]]]]]]]]; exact Hclass. }
    rewrite Hclass; split; [exact Hwf|eauto using base_refl, find_class_domain].
  - destruct (IHHfind Hct) as [Hwf Hb]; split; [exact Hwf|].
    eapply base_trans; [|exact Hb].
    apply base_extends.
    + eauto using find_class_domain.
    + exact (proj1 (subtype_domain _ _ _ Hb)).
    + unfold parent_lookup; now rewrite Hfind.
Qed.

Local Definition method_context_sub CT ctx (child parent : method_sig) :=
  (forall h v, value_typed CT h ctx v (mret child) -> value_typed CT h ctx v (mret parent)) /\
  (forall h vs, Forall2 (value_typed CT h ctx) vs (mparams parent) ->
    Forall2 (value_typed CT h ctx) vs (mparams child)) /\
  (qualifier_typable_context ctx (sqtype (mreceiver parent)) ctx ->
    qualifier_typable_context ctx (sqtype (mreceiver child)) ctx).

Local Lemma override_qualifier ctx qr qc qs :
  vpa_mutability_runtime_bound_agree ctx qc ->
  (qualifier_typable_context qr (vpa_mutability_qq_abstract_state (qc2q qc) qs) ctx <->
   qualifier_typable_context qr qs ctx).
Proof. destruct ctx, qr, qc, qs; simpl; intuition discriminate. Qed.

Local Lemma override_value CT h ctx qc v T :
  vpa_mutability_runtime_bound_agree ctx qc ->
  value_typed CT h ctx v (vpa_mutability_override qc T) <->
  value_typed CT h ctx v T.
Proof.
  intros H; destruct v; [tauto|].
  simpl; unfold wf_r_typable; destruct (r_type h l) as [rt|]; simpl; [|tauto].
  rewrite (override_qualifier ctx (rqtype rt) qc (sqtype T) H); reflexivity.
Qed.

Local Lemma override_arguments CT h ctx qc vs ps cs :
  vpa_mutability_runtime_bound_agree ctx qc ->
  Forall2 (fun p c => qualified_type_subtype CT (vpa_mutability_override qc p) c) ps cs ->
  Forall2 (value_typed CT h ctx) vs ps ->
  Forall2 (value_typed CT h ctx) vs cs.
Proof.
  intros Hagree Hsub; revert vs; induction Hsub; intros vs Hv; inversion Hv; subst;
    constructor; auto.
  eapply value_sub; [exact H|].
  apply (proj2 (override_value _ _ _ _ _ _ Hagree)); assumption.
Qed.

Local Lemma override_context_sub CT ctx qc child parent :
  vpa_mutability_runtime_bound_agree ctx qc ->
  method_override_compatible CT qc child parent ->
  method_context_sub CT ctx child parent.
Proof.
  intros Hagree [_ [_ [Hret [Hparams Hrec]]]].
  split.
  - intros h v Hv; apply (proj1 (override_value _ _ _ _ _ _ Hagree)).
    eapply value_sub; eassumption.
  - split.
    + intros; eapply override_arguments; eassumption.
    + intros H; eapply qualifier_sub; [exact Hrec|].
      simpl; apply (proj2 (override_qualifier _ _ _ _ Hagree)); exact H.
Qed.

Local Lemma dispatch_signature CT C D m ctx md :
  wf_class_table CT -> base_subtype CT C D -> wf_rtypeuse CT ctx C ->
  FindMethodWithName CT D m md ->
  exists md', FindMethodWithName CT C m md' /\
    method_context_sub CT ctx (msignature md') (msignature md).
Proof.
  intros Hct Hb; revert md; induction Hb as [|CT C D E HCD IHCD HDE IHDE|CT C D HC HD HP];
    intros md Hrt Hfind.
  - exists md; split; [exact Hfind|unfold method_context_sub; auto].
  - destruct (IHDE Hct _ (class_agrees _ _ _ _ Hct HCD Hrt) Hfind) as [mid [Hmid Hsub1]].
    destruct (IHCD Hct _ Hrt Hmid) as [md' [Hmd' Hsub2]].
    exists md'; split; [exact Hmd'|].
    destruct Hsub1 as [Hr1 [Hp1 Hc1]], Hsub2 as [Hr2 [Hp2 Hc2]].
    split; [intros h v Hv; exact (Hr1 h v (Hr2 h v Hv))|].
    split; [intros h vs Hv; exact (Hp2 h vs (Hp1 h vs Hv))|auto].
  - unfold parent_lookup in HP.
    destruct (find_class CT C) as [def|] eqn:Hdef; try discriminate.
    destruct (gget_method (methods (body def)) m) as [md'|] eqn:Hown.
    + exists md'; split; [econstructor; eauto|].
      destruct (method_here_wf _ _ _ _ _ Hct Hdef Hown) as [Hwf Hname].
      destruct Hwf as [_ [s' [T [_ [_ [_ [_ [Hoverride _]]]]]]]].
      assert (Hbound : bound CT C = Some (class_qualifier (signature def)))
        by (unfold bound; now rewrite Hdef).
      unfold wf_rtypeuse in Hrt; rewrite Hbound in Hrt.
      eapply override_context_sub; [exact (proj2 Hrt)|].
      eapply Hoverride with (parent := D) (parent_def := def); try eassumption.
      now rewrite Hname.
    + exists md; split; [eapply FOM_Super; eauto|unfold method_context_sub; auto].
Qed.

(* Arguments and results cross between the caller and callee contexts. *)
Local Definition adapt_call (readonly : bool) :=
  if readonly then vpa_mutability_tt_readonly_state
  else vpa_mutability_tt_abstract_state.

Local Lemma call_qualifier_in ro outer inner qv qx qarg qp :
  qualifier_typable_context inner qx outer ->
  qualifier_typable_context qv qarg outer ->
  qarg <> Lost ->
  (ro = true -> qp <> Mut) ->
  q_subtype qarg (sqtype (adapt_call ro
    (Build_qualified_type qx 0) (Build_qualified_type qp 0))) ->
  qualifier_typable_context qv qp inner.
Proof.
  destruct ro, outer, inner, qv, qx, qarg, qp; simpl;
    intros Hrecv Hv Hlost Hmut Hsub; try contradiction; try exact I;
    try solve [exfalso; exact (Hmut eq_refl eq_refl)]; inversion Hsub; congruence.
Qed.

Local Lemma call_qualifier_out ro outer inner qv Ty T :
  qualifier_typable_context inner (sqtype Ty) outer ->
  qualifier_typable_context qv (sqtype T) inner ->
  qualifier_typable_context qv (sqtype (adapt_call ro Ty T)) outer.
Proof.
  destruct Ty as [qy Cy], T as [qt Ct].
  destruct ro, outer, inner, qv, qy, qt; simpl; tauto.
Qed.

Local Lemma call_argument CT h ro outer inner v Ty A P :
  qualifier_typable_context inner (sqtype Ty) outer ->
  value_typed CT h outer v A ->
  sqtype A <> Lost ->
  (ro = true -> sqtype P <> Mut) ->
  qualified_type_subtype CT A (adapt_call ro Ty P) ->
  value_typed CT h inner v P.
Proof.
  intros Hrecv Hv Hlost Hmut Hsub.
  destruct v as [|l]; [exact I|].
  destruct (type_at_loc _ _ _ _ _ Hv) as [rt [Hrt [Hb Hq]]].
  destruct (qsub_parts _ _ _ Hsub) as [Hbsub Hqsub].
  simpl; unfold wf_r_typable; rewrite Hrt.
  split.
  - eapply base_trans; [exact Hb|]; destruct ro; exact Hbsub.
  - eapply call_qualifier_in with (ro := ro) (qx := sqtype Ty);
      try eassumption.
    destruct ro; exact Hqsub.
Qed.

Local Lemma call_result CT h ro outer inner v Ty T Tx :
  qualifier_typable_context inner (sqtype Ty) outer ->
  qualified_type_subtype CT (adapt_call ro Ty T) Tx ->
  value_typed CT h inner v T ->
  value_typed CT h outer v Tx.
Proof.
  intros Hrecv Hsub Hv; eapply value_sub; [exact Hsub|].
  destruct v as [|l]; [exact I|].
  destruct (type_at_loc _ _ _ _ _ Hv) as [rt [Hrt [Hb Hq]]].
  simpl; unfold wf_r_typable; rewrite Hrt.
  split; [destruct ro; exact Hb|eauto using call_qualifier_out].
Qed.

Local Lemma static_arguments_no_lost CT s args Ts :
  wf_senv CT s -> static_getType_list s args = Some Ts ->
  Forall (fun T => sqtype T <> Lost) Ts.
Proof.
  intros Hs; unfold static_getType_list; revert Ts.
  induction args as [|a args IH]; intros Ts HT; simpl in HT.
  - inversion HT; constructor.
  - destruct (static_getType s a) as [T|] eqn:HTa;
      destruct (mapM (static_getType s) args) as [ts|] eqn:Hts;
      try discriminate.
    inversion HT; subst; constructor; auto.
    eapply static_no_lost, wf_static_at; eassumption.
Qed.

Local Lemma call_arguments CT h ro outer inner Ty vals Ts Ps :
  qualifier_typable_context inner (sqtype Ty) outer ->
  Forall (fun T => sqtype T <> Lost) Ts ->
  (ro = true -> Forall (fun P => sqtype P <> Mut) Ps) ->
  Forall2 (value_typed CT h outer) vals Ts ->
  Forall2 (fun T P => qualified_type_subtype CT T (adapt_call ro Ty P)) Ts Ps ->
  Forall2 (value_typed CT h inner) vals Ps.
Proof.
  intros Hrecv Hlost Hmut Hv Hsub.
  revert vals Hv Hlost Hmut; induction Hsub; intros vals Hv Hlost Hmut;
    inversion Hv; subst; constructor.
  - inversion Hlost; subst.
    eapply call_argument; [exact Hrecv|eassumption|assumption| |exact H].
    intros Hr; specialize (Hmut Hr); now inversion Hmut.
  - apply IHHsub; [assumption|now inversion Hlost|].
    intros Hr; specialize (Hmut Hr); now inversion Hmut.
Qed.

Local Lemma readonly_method_qualifiers CT C md :
  wf_method CT C md ->
  readonly_state_method_scope (mscope (msignature md)) ->
  sqtype (mreceiver (msignature md)) <> Mut /\
  Forall (fun P => sqtype P <> Mut) (mparams (msignature md)).
Proof.
  intros [_ [s [T [_ [_ [_ [_ [_ [_ Hno]]]]]]]]] Hro.
  destruct (Hno Hro) as [Hrecv Hargs].
  unfold is_nonmutable_qualifier in Hrecv.
  split.
  - destruct Hrecv as [H|[H|[H|H]]]; congruence.
  - induction Hargs; constructor; auto.
    destruct H as [H|[H|[H|H]]]; congruence.
Qed.

Local Lemma call_receiver_qualifier CT ro outer inner Ty R :
  qualifier_typable_context inner (sqtype Ty) outer ->
  sqtype Ty <> Lost ->
  (ro = true -> sqtype R <> Mut) ->
  (qualified_type_subtype CT Ty (adapt_call ro Ty R) \/
   (sqtype Ty = RO /\ sqtype R = RDM /\ base_subtype CT (sctype Ty) (sctype R))) ->
  qualifier_typable_context inner (sqtype R) inner.
Proof.
  intros Hrecv Hlost Hmut [Hsub|[_ [HR _]]].
  - destruct (qsub_parts _ _ _ Hsub) as [_ Hq].
    eapply call_qualifier_in with (ro := ro) (qx := sqtype Ty);
      try eassumption.
    destruct ro; exact Hq.
  - rewrite HR; destruct inner; exact I.
Qed.

Local Lemma call_frame CT h s r l ctx ly cy y m args vals Ty Tx Ts static_md dyn_md ro :
  wf_class_table CT -> wf_heap CT h -> wf_senv CT s -> frame_typed CT h s r l ctx ->
  static_getType s y = Some Ty -> static_getType_list s args = Some Ts ->
  FindMethodWithName CT (sctype Ty) m static_md ->
  runtime_getVal r y = Some (Iot ly) -> r_basetype h ly = Some cy ->
  FindMethodWithName CT cy m dyn_md -> runtime_lookup_list r args = Some vals ->
  (ro = true -> readonly_state_method_scope (mscope (msignature static_md))) ->
  (qualified_type_subtype CT Ty (adapt_call ro Ty (mreceiver (msignature static_md))) \/
   (sqtype Ty = RO /\ sqtype (mreceiver (msignature static_md)) = RDM /\
    base_subtype CT (sctype Ty) (sctype (mreceiver (msignature static_md))))) ->
  Forall2 (fun T P => qualified_type_subtype CT T (adapt_call ro Ty P))
    Ts (mparams (msignature static_md)) ->
  qualified_type_subtype CT (adapt_call ro Ty (mret (msignature static_md))) Tx ->
  exists inner,
    wf_method CT (sctype (mreceiver (msignature dyn_md))) dyn_md /\
    frame_typed CT h (mreceiver (msignature dyn_md) :: mparams (msignature dyn_md))
      (mkr_env (Iot ly :: vals)) ly inner /\
    forall h' v, value_typed CT h' inner v (mret (msignature dyn_md)) ->
      value_typed CT h' ctx v Tx.
Proof.
  intros Hct Hheap Hs Hframe HTy HTs Hstatic Hly Hbase Hdyn Hvals Hro Hrcv Hargs Hret.
  unfold r_basetype in Hbase.
  destruct (runtime_getObj h ly) as [o|] eqn:Ho; try discriminate.
  injection Hbase as <-.
  pose proof (frame_value _ _ _ _ _ _ _ _ _ Hframe HTy Hly) as Hrecv.
  apply (type_at CT h ly o Ty ctx Ho) in Hrecv as [Hb Hqual].
  assert (Hdom : ly < length h)
    by (apply nth_error_Some; change (runtime_getObj h ly <> None); congruence).
  destruct (proj1 (obj_at _ _ _ _ Ho) (Hheap _ Hdom)) as [Hrt _].
  destruct (dispatch_signature _ _ _ _ _ _ Hct Hb Hrt Hstatic) as [md [Hfind Href]].
  assert (md = dyn_md) by (eapply find_method_unique; eassumption); subst md.
  destruct Href as [Hret' [Hparams Hrecv']].
  destruct (method_found_wf _ _ _ _ Hct Hdyn) as [Hwf Hclass].
  destruct (method_found_wf _ _ _ _ Hct Hstatic) as [Hwf_static _].
  exists (rqtype (rt_type o)); split; [exact Hwf|split].
  - split; [reflexivity|split].
    + unfold r_muttype; now rewrite Ho.
    + constructor.
      * apply (proj2 (type_at _ _ _ _ _ _ Ho)).
        split; [exact Hclass|apply Hrecv'].
        eapply call_receiver_qualifier; [exact Hqual| | |exact Hrcv].
        -- eapply static_no_lost, wf_static_at; eassumption.
        -- intros Hr; exact (proj1 (readonly_method_qualifiers _ _ _ Hwf_static (Hro Hr))).
      * apply Hparams.
        eapply call_arguments; [exact Hqual| | | |exact Hargs].
        -- eauto using static_arguments_no_lost.
        -- intros Hr; exact (proj2 (readonly_method_qualifiers _ _ _ Hwf_static (Hro Hr))).
        -- eapply frame_arguments; eassumption.
  - intros h' v Hv; eapply call_result; [exact Hqual|exact Hret|now apply Hret'].
Qed.

Local Lemma call_setup CT h s r l ctx x y m args mt s' ly cy vals md :
  wf_class_table CT -> wf_heap CT h -> frame_typed CT h s r l ctx ->
  stmt_typing CT s mt (SCall x m y args) s' ->
  runtime_getVal r y = Some (Iot ly) -> r_basetype h ly = Some cy ->
  FindMethodWithName CT cy m md -> runtime_lookup_list r args = Some vals ->
  s' = s /\ x <> 0 /\
  exists inner Tx, static_getType s x = Some Tx /\
    wf_method CT (sctype (mreceiver (msignature md))) md /\
    frame_typed CT h (mreceiver (msignature md) :: mparams (msignature md))
      (mkr_env (Iot ly :: vals)) ly inner /\
    forall h' v, value_typed CT h' inner v (mret (msignature md)) ->
      value_typed CT h' ctx v Tx.
Proof.
  intros Hct Hheap Hframe Htype Hly Hbase Hdyn Hvals.
  inversion Htype; subst; split; [reflexivity|split; [assumption|]
                               |reflexivity|split; [assumption|]].
  - edestruct (call_frame CT h s' r l ctx ly cy y m args vals Ty Tx argtypes mdef md false)
      as [inner [Hwf' [Hframe' Hret']]]; try eassumption.
    + discriminate.
    + exists inner, Tx; auto.
  - edestruct (call_frame CT h s' r l ctx ly cy y m args vals Ty Tx argtypes mdef md true)
      as [inner [Hwf' [Hframe' Hret']]]; try eassumption.
    + intros _; unfold readonly_state_method_scope.
      destruct (mscope (msignature mdef)); auto; contradiction.
    + exists inner, Tx; auto.
Qed.

Local Lemma local_frame CT h s r l ctx T :
  frame_typed CT h s r l ctx ->
  frame_typed CT h (s ++ [T]) (set_vars r (vars r ++ [Null_a])) l ctx.
Proof.
  intros [Hr [Hctx Hall]]; split.
  - destruct r as [[|v vs]]; [discriminate|exact Hr].
  - split; [exact Hctx|].
    apply Forall2_app; [exact Hall|constructor; [exact I|constructor]].
Qed.

Local Lemma local_senv CT s T :
  wf_senv CT s -> wf_stypeuse CT (sqtype T) (sctype T) -> wf_senv CT (s ++ [T]).
Proof.
  intros [Hlen Hall] HT; split.
  - rewrite length_app; simpl; lia.
  - apply Forall_app; split; [exact Hall|constructor; [exact HT|constructor]].
Qed.

Local Lemma field_write_heap CT h s r l ctx x f y lx o v Tx Ty fd ro :
  wf_heap CT h -> frame_typed CT h s r l ctx -> wf_senv CT s ->
  static_getType s x = Some Tx -> static_getType s y = Some Ty ->
  runtime_getVal r x = Some (Iot lx) -> runtime_getVal r y = Some v ->
  runtime_getObj h lx = Some o -> sf_def_rel CT (sctype Tx) f fd ->
  qualified_type_subtype CT Ty
    (Build_qualified_type (adapt_field ro (sqtype Tx) (mutability (ftype fd)))
       (f_base_type (ftype fd))) ->
  wf_heap CT (update_field h lx f v).
Proof.
  intros Hheap Hframe Hs HTx HTy Hx Hy Ho Hfd Hsub.
  pose proof (frame_value _ _ _ _ _ _ _ _ _ Hframe HTx Hx) as Hrecv.
  apply (type_at CT h lx o Tx ctx Ho) in Hrecv as [Hb _].
  eapply update_field_heap; try eassumption.
  exact (write_value CT h s r l ctx x y lx o v Tx Ty fd ro Hframe Hs HTx HTy Hx Hy Ho Hsub).
Qed.

(* The induction also keeps old runtime types and the caller's receiver. *)
Local Lemma eval_sound CT r h st res r' h' :
  eval_stmt CT r h st res r' h' ->
  forall s mt s' l ctx,
    wf_class_table CT -> wf_heap CT h -> frame_typed CT h s r l ctx ->
    stmt_typing CT s mt st s' ->
    match res with
    | OK => wf_heap CT h' /\ wf_senv CT s' /\
        frame_typed CT h' s' r' l ctx /\ types_preserved h h'
    | MUTATIONEXP => False
    | NPE => True
    end.
Proof.
  intros Heval; induction Heval;
    intros s scope s' l ctx Hct Hheap0 Hframe0 Htyping; try exact I;
    pose proof (wf_typing_input _ _ _ _ _ Htyping) as Hs.
  - inversion Htyping; subst.
    split; [exact Hheap0|split; [exact Hs|split; [exact Hframe0|firstorder]]].
  - inversion Htyping; subst.
    split; [exact Hheap0|split; [now apply local_senv|split; [now apply local_frame|firstorder]]].
  - inversion Htyping; subst.
    split; [exact Hheap0|split; [exact Hs|split; [|firstorder]]].
    eapply frame_update; try eassumption.
    eapply value_sub; [exact Hsub|eapply expr_value; eassumption].
  - subst h'.
    pose proof (update_field_types h loc_x f val_y) as Hkeep.
    assert (Hheap' : wf_heap CT (update_field h loc_x f val_y)).
    { inversion Htyping; subst;
        first [exact (field_write_heap CT h s' rΓ l ctx x f y loc_x o val_y Tx Ty fieldT false
                        Hheap0 Hframe0 Hs Hget_x Hget_y Hval_x Hval_y Hobj Hfld_def Hsub)
              |exact (field_write_heap CT h s' rΓ l ctx x f y loc_x o val_y Tx Ty fieldT true
                        Hheap0 Hframe0 Hs Hget_x Hget_y Hval_x Hval_y Hobj Hfld_def Hsub)]. }
    inversion Htyping; subst;
      (split; [exact Hheap'|split; [exact Hs|split; [eapply frame_transport; eassumption|exact Hkeep]]]).
  - assert (Hassignable_runtime :
      runtime_vpa_assignability (rqtype (rt_type o)) a = Assignable).
    { inversion Htyping; subst;
        apply (typed_write_assignable CT h s' rΓ l ctx x f loc_x o Tx a0 a
          Hframe0 Hget_x Hval_x Hobj Hassign_rel Hassign); auto. }
    congruence.
  - subst qadapted o h' rΓ'.
    destruct Hframe0 as [Hr [Hctx Hall]].
    assert (l1 = l) by congruence; subst l1.
    assert (qthisr = ctx) by congruence; subst qthisr.
    assert (Hframe0 : frame_typed CT h s rΓ l ctx) by (split; [exact Hr|auto]).
    inversion Htyping; subst.
    pose proof (frame_arguments _ _ _ _ _ _ _ _ _ Hframe0 Hargs Hget_args) as Hvals.
    destruct (creation CT h ctx q_c c consig vals argtypes Hct Hheap0 Hconsig Hqc Hvals Harg_sub)
      as [Hnewheap Hnewval].
    split; [exact Hnewheap|split; [exact Hs|split; [|apply append_object_types]]].
    eapply frame_update; [eapply frame_transport; [apply append_object_types|exact Hframe0]
                         |exact Hnot_rcv|exact Hget_x|].
    eapply value_sub; eassumption.
  - destruct Hfind as [Hmethod ->].
    subst mstmt mret rΓ' rΓ'''.
    destruct (call_setup _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hct Hheap0 Hframe0 Htyping
      Hval_y Hbase Hmethod Hargs) as [-> [Hx [inner [Tx [HTx [Hwf [Hbody Hout]]]]]]].
    destruct Hwf as [_ [sbody [Tret [Htype [_ [HTret [Hretsub _]]]]]]].
    destruct (IHHeval _ _ _ _ _ Hct Hheap0 Hbody Htype) as [Hheap' [_ [Hframe' Hkeep]]].
    split; [exact Hheap'|split; [exact Hs|split; [|exact Hkeep]]].
    eapply frame_update; [eapply frame_transport; eassumption|exact Hx|exact HTx|].
    apply Hout; eapply value_sub; [exact Hretsub|eapply frame_value; eassumption].
  - destruct Hfind as [Hmethod ->].
    subst mstmt mret rΓ'.
    destruct (call_setup _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hct Hheap0 Hframe0 Htyping
      Hval_y Hbase Hmethod Hargs) as [_ [_ [inner [Tx [_ [Hwf [Hbody _]]]]]]].
    destruct Hwf as [_ [sbody [Tret [Htype _]]]].
    exact (IHHeval _ _ _ _ _ Hct Hheap0 Hbody Htype).
  - inversion Htyping; subst.
    destruct (IHHeval1 _ _ _ _ _ Hct Hheap0 Hframe0 Htype1) as [Hheap' [_ [Hframe' Hkeep1]]].
    destruct (IHHeval2 _ _ _ _ _ Hct Hheap' Hframe' Htype2) as [Hheap'' [Hs' [Hframe'' Hkeep2]]].
    split; [exact Hheap''|split; [exact Hs'|split; [exact Hframe''|firstorder]]].
  - inversion Htyping; subst.
    exact (IHHeval _ _ _ _ _ Hct Hheap0 Hframe0 Htype1).
  - inversion Htyping; subst.
    destruct (IHHeval1 _ _ _ _ _ Hct Hheap0 Hframe0 Htype1) as [Hheap' [_ [Hframe' _]]].
    exact (IHHeval2 _ _ _ _ _ Hct Hheap' Hframe' Htype2).
Qed.

Theorem preservation_pico :
  forall CT sΓ mt rΓ h stmt rΓ' h' sΓ'
    (Hwf     : wf_r_config CT sΓ rΓ h)
    (Htyping : stmt_typing CT sΓ mt stmt sΓ')
    (Heval   : eval_stmt CT rΓ h stmt OK rΓ' h'),
    wf_r_config CT sΓ' rΓ' h'.
Proof.
  intros CT sΓ mt rΓ h stmt rΓ' h' sΓ' Hwf Htyping Heval.
  destruct (config_frame _ _ _ _ Hwf) as [Hct [Hheap [_ [l [ctx Hframe]]]]].
  destruct (eval_sound _ _ _ _ _ _ _ Heval _ _ _ _ _ Hct Hheap Hframe Htyping)
    as [Hheap' [Hs' [Hframe' _]]].
  eapply frame_config; eassumption.
Qed.

Theorem well_typed_no_mutation_exp :
  forall CT sΓ mt rΓ h stmt rΓ' h' sΓ'
    (Hwf : wf_r_config CT sΓ rΓ h)
    (Htyping : stmt_typing CT sΓ mt stmt sΓ')
    (Heval : eval_stmt CT rΓ h stmt MUTATIONEXP rΓ' h'),
    False.
Proof.
  intros CT sΓ mt rΓ h stmt rΓ' h' sΓ' Hwf Htyping Heval.
  destruct (config_frame _ _ _ _ Hwf) as [Hct [Hheap [_ [l [ctx Hframe]]]]].
  exact (eval_sound _ _ _ _ _ _ _ Heval _ _ _ _ _ Hct Hheap Hframe Htyping).
Qed.
