From Stdlib Require Import List Lia PeanoNat Compare_dec.
From Stdlib Require Sets.Ensembles.
Import ListNotations.

Require Import Syntax Notations Helpers Typing Subtyping Bigstep ViewpointAdaptation Reachability.

Definition reachable_locations_from_vals
  (h : heap) (vals : list value) : Ensembles.Ensemble Loc :=
  fun l_target =>
    exists l_root,
      List.In (Iot l_root) vals /\
      reachable h l_root l_target.


Local Lemma pico_nth_forall2 {A B : Type} (R : A -> B -> Prop) xs ys :
  Forall2 R xs ys -> forall i x y,
  nth_error xs i = Some x -> nth_error ys i = Some y -> R x y.
Proof.
  intros H; induction H; intros [|i] a b Ha Hb; simpl in *;
    try discriminate; try (congruence); eauto.
Qed.

Local Lemma pico_forall2_mapM (s : s_env) r (R : qualified_type -> value -> Prop) :
  Forall2 R s (vars r) ->
  forall zs Ts vs, static_getType_list s zs = Some Ts ->
  runtime_lookup_list r zs = Some vs -> Forall2 R Ts vs.
Proof.
  intros H zs; induction zs as [|z zs IH]; intros Ts vs HT Hv;
    cbn [static_getType_list runtime_lookup_list mapM] in *.
  - inversion HT; inversion Hv; constructor.
  - destruct (static_getType s z) eqn:Hz; try discriminate.
    destruct (mapM (static_getType s) zs) eqn:Hs; try discriminate.
    destruct (runtime_getVal r z) eqn:Hr; try discriminate.
    destruct (mapM (runtime_getVal r) zs) eqn:Hrs; try discriminate.
    inversion HT; inversion Hv; subst. constructor.
    + eapply pico_nth_forall2; eauto.
    + eapply IH; eauto.
Qed.

Local Lemma pico_update_other {A : Type} (xs : list A) i j v :
  i <> j -> nth_error (update i v xs) j = nth_error xs j.
Proof. revert i j; induction xs; intros [|i] [|j] H; simpl; auto; congruence. Qed.

Local Lemma pico_update_same {A : Type} (xs : list A) i (v : A) :
  i < length xs -> nth_error (update i v xs) i = Some v.
Proof. revert i; induction xs; intros [|i] H; simpl in *; auto with arith; lia. Qed.

Local Lemma pico_forall2_update {A B : Type} (R : A -> B -> Prop) xs ys i x y :
  Forall2 R xs ys -> nth_error xs i = Some x -> R x y ->
  Forall2 R xs (update i y ys).
Proof.
  intros H; revert i; induction H; intros [|i] Hx HR; simpl in *;
    try discriminate; constructor; eauto; congruence.
Qed.

Local Lemma pico_forall2_impl {A B : Type} (R S : A -> B -> Prop) xs ys :
  (forall x y, R x y -> S x y) -> Forall2 R xs ys -> Forall2 S xs ys.
Proof. intros HR H; induction H; constructor; auto. Qed.

Local Lemma pico_forall2_comp {A B D : Type}
    (R : A -> B -> Prop) (S : B -> D -> Prop) (T : A -> D -> Prop) xs ys zs :
  (forall x y z, R x y -> S y z -> T x z) ->
  Forall2 R xs ys -> Forall2 S ys zs -> Forall2 T xs zs.
Proof.
  intros H Hxy; revert zs; induction Hxy; intros zs Hyz;
    inversion Hyz; subst; constructor; eauto.
Qed.

Local Lemma pico_q_sub_trans a b c :
  q_subtype a b -> q_subtype b c -> q_subtype a c.
Proof. intros H K; destruct K; auto using q_rd; inversion H; subst; auto using q_bot. Qed.

Local Lemma pico_sub_parts CT T U :
  qualified_type_subtype CT T U ->
  base_subtype CT (sctype T) (sctype U) /\ q_subtype (sqtype T) (sqtype U).
Proof.
  induction 1; intuition eauto using base_refl, base_trans, q_refl, pico_q_sub_trans.
Qed.

Local Lemma pico_fields_deterministic CT C fs :
  CollectFields CT C fs -> forall gs, CollectFields CT C gs -> fs = gs.
Proof.
  induction 1; intros gs Hgs; inversion Hgs; subst;
    try congruence.
  match goal with
  | A : find_class _ _ = Some ?d, B : find_class _ _ = Some ?e |- _ =>
      assert (d = e) by congruence; subst
  end.
  assert (parent = parent0) by congruence. subst.
  f_equal; eauto.
Qed.

Local Lemma pico_inherited_field CT C D f fd :
  base_subtype CT C D -> FieldLookup CT D f fd -> FieldLookup CT C f fd.
Proof.
  induction 1; intros HF; auto.
  destruct HF as [CT D fs f fd Hfs Hfd].
  unfold parent_lookup in Hparent.
  destruct (find_class CT C) as [def|] eqn:HC; try discriminate.
  apply FL_Found with (fields := fs ++ Syntax.fields (body def)).
  - eapply CF_Inherit; eauto.
  - unfold gget in *. rewrite nth_error_app1; auto. apply nth_error_Some; unfold find_class, gget in *; congruence.
Qed.

Local Lemma pico_field_unique CT C f fd gd :
  FieldLookup CT C f fd -> FieldLookup CT C f gd -> fd = gd.
Proof.
  intros H1 H; inversion H1; inversion H; subst.
  match goal with
  | A : CollectFields _ _ ?xs, B : CollectFields _ _ ?ys |- _ =>
      assert (xs = ys) by eauto using pico_fields_deterministic; subst
  end. congruence.
Qed.

Local Lemma pico_assign_inherit CT C D f a :
  base_subtype CT C D -> sf_assignability_rel CT D f a ->
  sf_assignability_rel CT C f a.
Proof. intros H [fd [HF HA]]; exists fd; eauto using pico_inherited_field. Qed.

Local Lemma pico_assign_unique CT C f a b :
  sf_assignability_rel CT C f a -> sf_assignability_rel CT C f b -> a = b.
Proof.
  intros [fd [Hf Ha]] [gd [Hg Hb]].
  assert (fd = gd) by eauto using pico_field_unique. congruence.
Qed.

Local Lemma pico_class_wf CT C d :
  wf_class_table CT -> find_class CT C = Some d -> wf_class CT d.
Proof.
  intros [H _] Hd. eapply Forall_forall; eauto.
  eapply nth_error_In; exact Hd.
Qed.

Local Lemma pico_method_name ds m d :
  gget_method ds m = Some d -> mname (msignature d) = m /\ List.In d ds.
Proof.
  unfold gget_method. intro H. apply find_some in H as [Hin Hname].
  apply Nat.eqb_eq in Hname. auto.
Qed.

Local Lemma pico_method_unique CT C m d :
  FindMethodWithName CT C m d ->
  forall e, FindMethodWithName CT C m e -> d = e.
Proof.
  induction 1; intros e He; inversion He; subst;
    assert (def = def0) by congruence; subst; try congruence.
  assert (parent = parent0) by congruence. subst. auto.
Qed.

Local Lemma pico_own_wf_method CT C d m md :
  wf_class_table CT -> find_class CT C = Some d ->
  gget_method (methods (body d)) m = Some md -> wf_method CT C md.
Proof.
  intros HCT Hd Hm. apply pico_method_name in Hm as [_ Hin].
  assert (Hc : cname (signature d) = C) by (apply HCT; exact Hd).
  pose proof (pico_class_wf _ _ _ HCT Hd) as Hw.
  destruct Hw as [CT d cn Hsuper Hrdm Hfields Hno_methods Hcn Hctor Hfs Hnodup
                |CT d parent cn Hsuper Hcn Hord sig bod c qc Hw].
  - rewrite Hno_methods in Hin. contradiction.
  - destruct Hw as (_ & Hms & _). unfold c, sig in Hms. rewrite Hc in Hms.
    rewrite Forall_forall in Hms. auto.
Qed.

Local Lemma pico_receiver_class CT C m d :
  wf_class_table CT -> FindMethodWithName CT C m d ->
  base_subtype CT C (sctype (mreceiver (msignature d))) /\
  wf_method CT (sctype (mreceiver (msignature d))) d.
Proof.
  intros HCT H; induction H; subst.
  - pose proof (pico_own_wf_method _ _ _ _ _ HCT Hfind Hget_method) as Hw.
    assert (Hrecv : sctype (mreceiver (msignature mdef)) = C)
      by (unfold wf_method in Hw; firstorder).
    rewrite Hrecv. split; auto.
    constructor. apply nth_error_Some. unfold find_class, gget in Hfind. congruence.
  - destruct (IHFindMethodWithName HCT) as [Hsub Hw]. split; auto.
    eapply base_trans; [eapply base_extends|exact Hsub].
    + apply nth_error_Some. unfold find_class, gget in Hfind. congruence.
    + inversion H; apply nth_error_Some; unfold find_class, gget in *; congruence.
    + unfold parent_lookup. now rewrite Hfind.
Qed.

Local Lemma pico_bound_step CT C D qr :
  wf_class_table CT -> parent_lookup CT C = Some D ->
  D < dom CT -> wf_rtypeuse CT qr C -> wf_rtypeuse CT qr D.
Proof.
  intros HCT HP HD HC.
  unfold parent_lookup in HP. destruct (find_class CT C) as [d|] eqn:Hd;
    try discriminate.
  unfold wf_rtypeuse, bound in *. rewrite Hd in HC.
  assert (exists e, find_class CT D = Some e) as [e He].
  { destruct (find_class CT D) eqn:He; eauto.
    apply nth_error_None in He; lia. }
  rewrite He.
  pose proof (pico_class_wf _ _ _ HCT Hd) as Hw.
  inversion Hw; subst; try congruence.
  assert (superC = D) by congruence. subst superC.
  destruct H as (_ & _ & _ & H).
  unfold bound in H. rewrite He in H.
  destruct H as (fs & Hfs & [Hq|Hq] & Hfields); split; auto.
  - rewrite <- Hq. tauto.
  - rewrite Hq. destruct qr; reflexivity.
Qed.

Local Lemma pico_bound_super CT C D qr :
  wf_class_table CT -> base_subtype CT C D ->
  wf_rtypeuse CT qr C -> wf_rtypeuse CT qr D.
Proof. intros HCT H; induction H; eauto using pico_bound_step. Qed.

(* A method's explicit Mut references use a separate region from its
   receiver-dependent references. The region assignment is proof-only. *)
Local Definition pico_cap (qr : q_r) (receiver mut : nat) (q : Syntax.q)
    (actual : q_r) (region : nat) : Prop :=
  match q with
  | Mut => actual = Mut_r /\ region = mut
  | Imm => actual = Imm_r
  | RDM => match qr with
           | Mut_r => actual = Mut_r /\ region = receiver
           | Imm_r => actual = Imm_r
           end
  | RO | Lost => True
  | Bot => False
  end.

Local Definition pico_value CT h (regions : Loc -> nat) C
    (cap : q_r -> nat -> Prop) v : Prop :=
  match v with
  | Null_a => True
  | Iot l => exists t, r_type h l = Some t /\
      base_subtype CT (rctype t) C /\ cap (rqtype t) (regions l)
  end.

Local Definition pico_typed CT h regions qr receiver mut (T : qualified_type) :=
  pico_value CT h regions (sctype T) (pico_cap qr receiver mut (sqtype T)).

Local Lemma pico_value_map CT h h' tags tags' C D P Q v (rename : nat -> nat) :
  (forall l t, r_type h l = Some t ->
     r_type h' l = Some t /\ tags' l = rename (tags l)) ->
  (forall c, base_subtype CT c C -> base_subtype CT c D) ->
  (forall qr n, P qr n -> Q qr (rename n)) ->
  pico_value CT h tags C P v -> pico_value CT h' tags' D Q v.
Proof.
  intros Hheap Hbase Hcap; destruct v; simpl; auto.
  intros (t & Ht & HC & HP). destruct (Hheap _ _ Ht) as [Ht' Htag].
  exists t. rewrite Htag. auto.
Qed.

Local Lemma pico_cap_sub ctx r p q1 q2 qr tag :
  q_subtype q1 q2 -> pico_cap ctx r p q1 qr tag -> pico_cap ctx r p q2 qr tag.
Proof. destruct 1; simpl; tauto. Qed.

Local Lemma pico_typed_sub CT h tags ctx r p T U v :
  qualified_type_subtype CT T U ->
  pico_typed CT h tags ctx r p T v -> pico_typed CT h tags ctx r p U v.
Proof.
  intros H; apply pico_sub_parts in H as [HB HQ].
  eapply pico_value_map with (rename := fun n => n); eauto using base_trans, pico_cap_sub.
Qed.

Local Lemma pico_nonmutable_change CT h tags ctx r p p' T v :
  is_nonmutable_qualifier (sqtype T) ->
  pico_typed CT h tags ctx r p T v -> pico_typed CT h tags ctx r p' T v.
Proof.
  intros H. eapply pico_value_map with (rename := fun n => n); eauto.
  unfold is_nonmutable_qualifier in H. intros qt n; destruct H as [Heq|[Heq|[Heq|Heq]]]; rewrite Heq; auto.
Qed.

Inductive pico_dispatch (CT : class_table) (qr : q_r) :
    method_sig -> method_sig -> Prop :=
  | pico_dispatch_refl : forall s, pico_dispatch CT qr s s
  | pico_dispatch_override : forall qc child parent,
      vpa_mutability_runtime_bound_agree qr qc ->
      method_override_compatible CT qc child parent ->
      pico_dispatch CT qr child parent
  | pico_dispatch_trans : forall a b c,
      pico_dispatch CT qr a b -> pico_dispatch CT qr b c -> pico_dispatch CT qr a c.

Local Lemma pico_dispatch_lookup CT C D qr m md :
  wf_class_table CT -> base_subtype CT C D ->
  wf_rtypeuse CT qr C -> FindMethodWithName CT D m md ->
  exists md', FindMethodWithName CT C m md' /\
    pico_dispatch CT qr (msignature md') (msignature md).
Proof.
  intros HCT HS; revert md. induction HS; intros md HW HM.
  - exists md. auto using pico_dispatch_refl.
  - destruct (IHHS2 HCT md (pico_bound_super _ _ _ _ HCT HS1 HW) HM) as (mid & Hmid & H2).
    destruct (IHHS1 HCT mid HW Hmid) as (child & Hchild & H1).
    eauto using pico_dispatch_trans.
  - unfold parent_lookup in Hparent.
    destruct (find_class CT C) as [d|] eqn:Hd; try discriminate.
    destruct (gget_method (methods (body d)) m) as [child|] eqn:Hget.
    + exists child. split; [eapply FOM_Here; eauto|].
      pose proof (pico_own_wf_method _ _ _ _ _ HCT Hd Hget) as Hchild.
      pose proof (pico_method_name _ _ _ Hget) as [Hname _].
      assert (Hb : bound CT C = Some (class_qualifier (signature d)))
        by (unfold bound; rewrite Hd; reflexivity).
      unfold wf_rtypeuse in HW. rewrite Hb in HW. destruct HW as [_ Hagree].
      unfold wf_method in Hchild.
      destruct Hchild as (_ & sg & T & _ & _ & _ & _ & Hoverride & _).
      eapply pico_dispatch_override; [exact Hagree|].
      eapply Hoverride; eauto. now rewrite Hname.
    + exists md. split; [eapply FOM_Super; eauto|constructor].
Qed.

Local Lemma pico_override_cap qr n qc T ql k :
  vpa_mutability_runtime_bound_agree qr qc ->
  (pico_cap qr n n (sqtype (vpa_mutability_override qc T)) ql k <->
   pico_cap qr n n (sqtype T) ql k).
Proof.
  destruct qr, qc, T as [q C], q; cbn; intuition congruence.
Qed.

Local Lemma pico_dispatch_scope CT qr child parent :
  pico_dispatch CT qr child parent -> mscope child = mscope parent.
Proof.
  induction 1 as [s|qc c p Ha (_ & H & _)|a b c _ H1 _ H2]; congruence.
Qed.

Local Lemma pico_dispatch_args CT h tags qr n child parent :
  pico_dispatch CT qr child parent -> forall vs,
  Forall2 (pico_typed CT h tags qr n n) (mparams parent) vs ->
  Forall2 (pico_typed CT h tags qr n n) (mparams child) vs.
Proof.
  induction 1 as [s|qc c p Ha (_ & _ & _ & Hparams & _)|a b c _ H1 _ H2];
    intros vs Hvs; auto.
  apply Forall2_flip in Hparams.
  eapply pico_forall2_comp; [|exact Hparams|exact Hvs].
  intros U T v Hsub Hv.
  apply pico_typed_sub with (T := vpa_mutability_override qc T); auto.
  unfold pico_typed in *. destruct v; simpl in *; auto.
  destruct Hv as (t & Ht & HC & HQ). exists t. repeat split; auto.
  apply (proj2 (pico_override_cap qr n qc T _ _ Ha)); auto.
Qed.

Local Lemma pico_dispatch_receiver CT qr n child parent ql k :
  pico_dispatch CT qr child parent ->
  pico_cap qr n n (sqtype (mreceiver parent)) ql k ->
  pico_cap qr n n (sqtype (mreceiver child)) ql k.
Proof.
  induction 1 as [s|qc c p Ha (_ & _ & _ & _ & Hrecv)|a b c _ H1 _ H2]; auto.
  intros H. eapply pico_cap_sub; [exact Hrecv|].
  apply (proj2 (pico_override_cap qr n qc _ ql k Ha)); auto.
Qed.

Local Lemma pico_dispatch_return CT h tags qr n child parent v :
  pico_dispatch CT qr child parent ->
  pico_typed CT h tags qr n n (mret child) v ->
  pico_typed CT h tags qr n n (mret parent) v.
Proof.
  induction 1 as [s|qc c p Ha (_ & _ & Hret & _)|a b c _ H1 _ H2]; auto.
  intros H. pose proof (pico_typed_sub _ _ _ _ _ _ _ _ _ Hret H) as Hv.
  unfold pico_typed in *. destruct v; simpl in *; auto.
  destruct Hv as (t & Ht & HC & HQ). exists t. repeat split; auto.
  apply (proj1 (pico_override_cap qr n qc (mret p) _ _ Ha)); auto.
Qed.

(* An RDM field of a mutable object stays in the owner's region. A Mut
   field can also follow an edge introduced by a call, for RDM allocations
   initialized with Mut references from the call body. *)
Local Definition pico_field_cap (E : nat -> nat -> Prop) (qr : q_r)
    (n : nat) (f : q_f) (ql : q_r) (k : nat) : Prop :=
  match f with
  | RO_f => True
  | Imm_f => ql = Imm_r
  | RDM_f => pico_cap qr n n RDM ql k
  | Mut_f => ql = Mut_r /\ (qr = Mut_r -> k = n \/ E n k)
  end.

Local Definition pico_heap CT h tags bound_n E :=
  forall l o, runtime_getObj h l = Some o ->
  tags l < bound_n /\ wf_rtypeuse CT (rqtype (rt_type o)) (rctype (rt_type o)) /\
  forall f fd v, FieldLookup CT (rctype (rt_type o)) f fd ->
    nth_error (fields_map o) f = Some v ->
    pico_value CT h tags (f_base_type (ftype fd))
      (pico_field_cap E (rqtype (rt_type o)) (tags l) (mutability (ftype fd))) v.

Local Definition pico_edges n (E : nat -> nat -> Prop) :=
  forall a b, E a b -> a < n /\ b < n.

Local Definition pico_extension h (tags : Loc -> nat) h' (tags' : Loc -> nat) :=
  forall l t, r_type h l = Some t -> r_type h' l = Some t /\ tags' l = tags l.

Local Lemma pico_r_type_get h l t :
  r_type h l = Some t <-> exists o, runtime_getObj h l = Some o /\ rt_type o = t.
Proof.
  unfold r_type. destruct (runtime_getObj h l); split; try discriminate;
    intros H; try destruct H as (o' & H & Ht); inversion H; subst; eauto.
Qed.

Local Lemma pico_extension_typed CT h tags h' tags' qr r p T v :
  pico_extension h tags h' tags' ->
  pico_typed CT h tags qr r p T v -> pico_typed CT h' tags' qr r p T v.
Proof. intros H; eapply pico_value_map with (rename := fun x => x); eauto. Qed.

Local Definition pico_frame CT h tags qr r p s env :=
  Forall2 (pico_typed CT h tags qr r p) s (vars env) /\
  exists l t, runtime_getVal env 0 = Some (Iot l) /\
    r_type h l = Some t /\ rqtype t = qr /\ tags l = r.

Local Lemma pico_frame_extend CT h tags h' tags' qr r p s env :
  pico_extension h tags h' tags' ->
  pico_frame CT h tags qr r p s env -> pico_frame CT h' tags' qr r p s env.
Proof.
  intros He [Hs (l & t & Hl & Ht & Hq & Hr)].
  destruct (He _ _ Ht) as [Ht' Hr'].
  split.
  - eapply pico_forall2_impl; [|exact Hs]. intros T v. eapply pico_extension_typed; exact He.
  - exists l, t. repeat split; auto. congruence.
Qed.

Local Lemma pico_frame_get CT h tags qr r p s env i T v :
  pico_frame CT h tags qr r p s env ->
  static_getType s i = Some T -> runtime_getVal env i = Some v ->
  pico_typed CT h tags qr r p T v.
Proof. intros [Hs _]; eapply pico_nth_forall2; eauto. Qed.

Local Lemma pico_frame_update CT h tags qr r p s env i T v :
  pico_frame CT h tags qr r p s env -> i <> 0 ->
  static_getType s i = Some T -> pico_typed CT h tags qr r p T v ->
  pico_frame CT h tags qr r p s (set_vars env (update i v (vars env))).
Proof.
  intros [Hs (l & t & Hl & Ht & Hq & Hr)] Hi HT Hv. split.
  - eapply pico_forall2_update; eauto.
  - exists l, t. unfold runtime_getVal, set_vars in *. cbn [vars].
    rewrite pico_update_other; auto.
Qed.

Local Lemma pico_call_arg_cap ctx r p recv arg formal actual n ql k :
  pico_cap ctx r p recv actual n ->
  q_subtype arg (vpa_mutability_qq_readonly_state recv formal) ->
  pico_cap ctx r p arg ql k ->
  pico_cap actual n n formal ql k.
Proof.
  intros Hrecv Hsub Hv.
  destruct recv, formal, ctx, actual; cbn in *; try tauto;
    inversion Hsub; subst; cbn in *; intuition congruence.
Qed.

Local Lemma pico_call_return_cap ctx r p recv ret actual n ql k :
  pico_cap ctx r p recv actual n ->
  pico_cap actual n n ret ql k ->
  pico_cap ctx r p (vpa_mutability_qq_readonly_state recv ret) ql k.
Proof. destruct recv, ret, ctx, actual; cbn; intuition congruence. Qed.

Local Lemma pico_receiver_cap CT ctx r p Ty md actual n :
  (qualified_type_subtype CT Ty
      (vpa_mutability_tt_readonly_state Ty (mreceiver (msignature md))) \/
   sqtype Ty = RO /\ sqtype (mreceiver (msignature md)) = RDM /\
      base_subtype CT (sctype Ty) (sctype (mreceiver (msignature md)))) ->
  pico_cap ctx r p (sqtype Ty) actual n ->
  pico_cap actual n n (sqtype (mreceiver (msignature md))) actual n.
Proof.
  intros [Hsub | (Hro & Hrdm & _)] Hcap.
  - apply pico_sub_parts in Hsub as [_ Hsub].
    eapply pico_call_arg_cap; eauto.
  - rewrite Hrdm. destruct actual; simpl; auto.
Qed.

Local Lemma pico_call_args CT h tags ctx r p Ty actual n argtypes params vals :
  pico_cap ctx r p (sqtype Ty) actual n ->
  Forall2 (fun arg T => qualified_type_subtype CT arg
             (vpa_mutability_tt_readonly_state Ty T)) argtypes params ->
  Forall2 (pico_typed CT h tags ctx r p) argtypes vals ->
  Forall2 (pico_typed CT h tags actual n n) params vals.
Proof.
  intros Hrecv Hsub Hv. apply Forall2_flip in Hsub.
  eapply pico_forall2_comp; [|exact Hsub|exact Hv].
  intros T U [|l] HS HH; simpl in *; auto.
  apply pico_sub_parts in HS as [HB HQ]. cbn in HB, HQ.
  destruct HH as (t & Ht & HC & HP). exists t. split; auto.
  split; eauto using base_trans, pico_call_arg_cap.
Qed.

Local Lemma pico_read_cap E ctx r p recv f actual n ql k :
  (forall j, E p j -> j = p) ->
  pico_cap ctx r p recv actual n ->
  pico_field_cap E actual n f ql k ->
  pico_cap ctx r p (vpa_mutability_stype_fld_readonly_state recv f) ql k.
Proof.
  destruct ctx, recv, f, actual; cbn; intros HE Hr Hf; try tauto;
    intuition subst; eauto; congruence.
Qed.

Local Lemma pico_write_cap E ctx r p recv f actual n ql k aq :
  pico_cap ctx r p recv actual n ->
  q_subtype aq (vpa_mutability_stype_fld_readonly_state recv f) ->
  pico_cap ctx r p aq ql k ->
  pico_field_cap E actual n f ql k.
Proof.
  intros Hr Hs Ha. destruct recv, f, ctx, actual; cbn in *; try tauto;
    inversion Hs; subst; cbn in *; intuition congruence.
Qed.

Local Lemma pico_create_field_cap E ctx r p qc f ql k :
  (r = p \/ E r p) ->
  pico_cap ctx r p (vpa_mutability_constructor_fld qc f) ql k ->
  pico_field_cap E (vpa_mutability_object_creation ctx qc)
    (match qc with RDM_c => r | _ => p end) f ql k.
Proof. destruct ctx, qc, f; cbn; intuition congruence. Qed.

Local Lemma pico_create_cap ctx r p qc :
  pico_cap ctx r p (qc2q qc) (vpa_mutability_object_creation ctx qc)
    (match qc with RDM_c => r | _ => p end).
Proof. destruct ctx, qc; simpl; auto. Qed.

Local Lemma pico_constructor_wf CT C sig :
  wf_class_table CT -> constructor_sig_lookup CT C = Some sig ->
  wf_constructor CT C sig.
Proof.
  intros HCT Hsig. unfold constructor_sig_lookup, constructor_def_lookup in Hsig.
  destruct (find_class CT C) as [d|] eqn:Hd; try discriminate.
  inversion Hsig; subst sig.
  assert (Hc : cname (signature d) = C) by (apply HCT; exact Hd).
  pose proof (pico_class_wf _ _ _ HCT Hd) as Hw.
  destruct Hw as [CT d cn Hsuper Hrdm Hfields Hno_methods Hcn Hctor Hfs Hnodup
                |CT d parent cn Hsuper Hcn Hord sig bod c qc Hw].
  - assert (cn = C) by congruence. subst cn.
    unfold wf_constructor_object in Hctor. destruct Hctor as (_ & _ & Hb & Hps & Hcf).
    unfold wf_constructor. rewrite Hps. repeat split; auto.
    + congruence.
    + exists []; rewrite <- Hc; repeat split; auto.
  - destruct Hw as (Hctor & _). unfold c, sig in Hctor. now rewrite Hc in Hctor.
Qed.

Local Lemma pico_expr CT s env h tags ctx r p n E mt e T v :
  readonly_state_method_scope mt ->
  (forall j, E p j -> j = p) ->
  pico_heap CT h tags n E ->
  pico_frame CT h tags ctx r p s env ->
  expr_has_type CT s mt e T -> eval_expr CT env h e v OK env h ->
  pico_typed CT h tags ctx r p T v.
Proof.
  intros Hmt HE Hheap Hframe Htyping Heval.
  inversion Htyping; subst; inversion Heval; subst; simpl; auto.
  - eapply pico_frame_get; eauto.
  - unfold readonly_state_method_scope in Hmt. intuition congruence.
  - pose proof (pico_frame_get _ _ _ _ _ _ _ _ _ _ _ Hframe Hget_x Hval)
      as (t & Ht & HC & Hcap).
    unfold r_type in Ht. rewrite Hobj in Ht. inversion Ht; subst t.
    destruct (Hheap _ _ Hobj) as (_ & _ & HF).
    eapply pico_inherited_field in Hfld_def; [|exact HC].
    specialize (HF _ _ _ Hfld_def Hfield).
    eapply pico_value_map with (rename := fun x => x); [| | |exact HF].
    + eauto.
    + auto.
    + eauto using pico_read_cap.
Qed.

Local Definition pico_observe h l f :=
  match runtime_getObj h l with
  | Some o => nth_error (fields_map o) f
  | None => None
  end.

Local Definition pico_protected CT mt C f :=
  mt = TransitiveState \/
  sf_assignability_rel CT C f Final \/ sf_assignability_rel CT C f RDA.

Local Definition pico_preserves CT mt (P : Loc -> Prop) h h' :=
  forall l t f, r_type h l = Some t -> P l ->
  pico_protected CT mt (rctype t) f ->
  pico_observe h l f = pico_observe h' l f.

Local Lemma pico_write_protected CT mt C f qa qs :
  readonly_state_method_scope mt ->
  sf_assignability_rel CT C f qa ->
  (match mt with
   | ReadonlyState => vpa_assignability qs qa
   | _ => vpa_assignability_cs_ts qs qa
   end) = Assignable ->
  pico_protected CT mt C f -> qs = Mut.
Proof.
  intros [->|Hmt] Ha HW HP; [|subst mt]; cbn in HW.
  - destruct HP as [H | [H|H]]; try discriminate.
    all: assert (qa = _) by (eapply pico_assign_unique; eassumption);
      subst qa; destruct qs; cbn in HW; congruence.
  - destruct qs, qa; cbn in HW; congruence.
Qed.

Local Lemma pico_write_heap CT h tags n E mt p l o f v a qrecv :
  pico_heap CT h tags n E ->
  readonly_state_method_scope mt ->
  runtime_getObj h l = Some o ->
  sf_assignability_rel CT (rctype (rt_type o)) f a ->
  (match mt with
   | ReadonlyState => vpa_assignability qrecv a
   | _ => vpa_assignability_cs_ts qrecv a
   end) = Assignable ->
  (qrecv = Mut -> tags l = p) ->
  (forall fd, FieldLookup CT (rctype (rt_type o)) f fd ->
    pico_value CT h tags (f_base_type (ftype fd))
      (pico_field_cap E (rqtype (rt_type o)) (tags l) (mutability (ftype fd))) v) ->
  pico_heap CT (update_field h l f v) tags n E /\
  pico_extension h tags (update_field h l f v) tags /\
  pico_preserves CT mt (fun k => tags k <> p) h (update_field h l f v).
Proof.
  intros Hheap Hmt Ho Ha HW Hp HV.
  set (h' := update_field h l f v).
  assert (Ha1 : runtime_getObj h' l = Some (set_fields_map o (update f v (fields_map o)))).
  { unfold h', update_field. rewrite Ho. apply pico_update_same.
    apply nth_error_Some; unfold runtime_getObj in Ho; congruence. }
  assert (Ha2 : forall k, k <> l -> runtime_getObj h' k = runtime_getObj h k).
  { intros k Hk. unfold h', update_field. rewrite Ho.
    apply pico_update_other. congruence. }
  assert (Hex : pico_extension h tags h' tags).
  { intros k t Ht. unfold r_type in *. destruct (Nat.eq_dec k l) as [->|Hk].
    - rewrite Ho in Ht. rewrite Ha1. auto.
    - rewrite Ha2; auto. }
  split; [|split; [exact Hex|]].
  - intros k obj Hobj.
    destruct (Nat.eq_dec k l) as [->|Hk].
    + rewrite Ha1 in Hobj. inversion Hobj; subst obj; clear Hobj.
      destruct (Hheap _ _ Ho) as (Hn & Hwf & HF). simpl.
      split; [exact Hn|split; [exact Hwf|]].
      intros j fd w Hfd Hw.
      assert (Htyped : pico_value CT h tags (f_base_type (ftype fd))
             (pico_field_cap E (rqtype (rt_type o)) (tags l) (mutability (ftype fd))) w).
      { destruct (Nat.eq_dec f j) as [->|Hne].
        - destruct (lt_dec j (length (fields_map o))) as [Hj|Hj].
          + rewrite (pico_update_same _ _ _ Hj) in Hw. inversion Hw; subst. auto.
          + assert (Hlength : forall (xs : list value) i w', length (update i w' xs) = length xs).
            { induction xs; intros [|i] ?; simpl; auto. }
            assert (j < length (update j v (fields_map o)))
              by (apply nth_error_Some; congruence).
            rewrite Hlength in H. lia.
        - rewrite (pico_update_other _ _ _ _ Hne) in Hw. eauto. }
      eapply pico_value_map with (rename := fun x => x); eauto.
    + rewrite (Ha2 _ Hk) in Hobj.
      destruct (Hheap _ _ Hobj) as (Hn & Hwf & HF).
      split; [exact Hn|split; [exact Hwf|]].
      intros j fd w Hfd Hw.
      specialize (HF _ _ _ Hfd Hw).
      eapply pico_value_map with (rename := fun x => x); eauto.
  - intros k t j Ht Hne Hprot. unfold pico_observe.
    destruct (Nat.eq_dec k l) as [->|Hk]; [|now rewrite Ha2].
    rewrite Ho Ha1. simpl. symmetry. apply pico_update_other.
    intro Heq. subst j. unfold r_type in Ht. rewrite Ho in Ht. inversion Ht; subst.
    apply Hne, Hp. eapply pico_write_protected; eauto.
Qed.

Local Lemma pico_sub_domains CT C D :
  base_subtype CT C D -> C < dom CT /\ D < dom CT.
Proof. induction 1; intuition. Qed.

Local Lemma pico_constructor_sub CT qc qb T fd :
  vpa_mutability_bound (qc2q qc) qb = qc2q qc ->
  qualified_type_subtype CT
    (vpa_mutability_constructor_param qb T)
    (Build_qualified_type (vpa_mutability_constructor_fld qb (mutability (ftype fd)))
       (f_base_type (ftype fd))) ->
  qualified_type_subtype CT
    (vpa_mutability_constructor_param qc T)
    (Build_qualified_type (vpa_mutability_constructor_fld qc (mutability (ftype fd)))
       (f_base_type (ftype fd))).
Proof.
  intros Hbound Hsub. apply pico_sub_parts in Hsub as [HB HQ].
  pose proof (pico_sub_domains _ _ _ HB) as [H1 H2].
  constructor; auto.
  destruct qc, qb, T as [q C], q, (mutability (ftype fd));
    cbn in *; try discriminate; try assumption;
    inversion HQ; subst; constructor; congruence.
Qed.

Local Lemma pico_forall2_constructor CT h tags qr r p E qc qb cs fs vs :
  r = p \/ E r p ->
  vpa_mutability_bound (qc2q qc) qb = qc2q qc ->
  Forall2 (fun T fd => qualified_type_subtype CT
    (vpa_mutability_constructor_param qb T)
    (Build_qualified_type (vpa_mutability_constructor_fld qb (mutability (ftype fd)))
       (f_base_type (ftype fd)))) cs fs ->
  Forall2 (pico_typed CT h tags qr r p)
    (map (vpa_mutability_constructor_param qc) cs) vs ->
  Forall2 (fun fd v => pico_value CT h tags (f_base_type (ftype fd))
    (pico_field_cap E (vpa_mutability_object_creation qr qc)
       (match qc with RDM_c => r | _ => p end) (mutability (ftype fd))) v) fs vs.
Proof.
  intros HE Hbound Hc; revert vs.
  induction Hc; intros vs Hv; simpl in Hv; inversion Hv; subst; constructor; auto.
  match goal with
  | HS : qualified_type_subtype _ _ _, HT : pico_typed _ _ _ _ _ _ _ _ |- _ =>
    pose proof (pico_typed_sub _ _ _ _ _ _ _ _ _
      (pico_constructor_sub _ _ _ _ _ Hbound HS) HT) as Htyped
  end.
  eapply pico_value_map with (rename := fun x => x); [| | |exact Htyped].
  - eauto.
  - simpl; auto.
  - eauto using pico_create_field_cap.
Qed.

Local Lemma pico_allocate CT h tags qr r p n E qc C vs fs :
  pico_heap CT h tags n E -> r < n -> p < n ->
  wf_rtypeuse CT (vpa_mutability_object_creation qr qc) C ->
  CollectFields CT C fs ->
  Forall2 (fun fd v => pico_value CT h tags (f_base_type (ftype fd))
    (pico_field_cap E (vpa_mutability_object_creation qr qc)
       (match qc with RDM_c => r | _ => p end) (mutability (ftype fd))) v) fs vs ->
  let new_tag := match qc with RDM_c => r | _ => p end in
  let tags' l := if Nat.eq_dec l (dom h) then new_tag else tags l in
  let t := mkruntime_type (vpa_mutability_object_creation qr qc) C in
  let h' := h ++ [mkObj t vs] in
  pico_heap CT h' tags' n E /\ pico_extension h tags h' tags' /\
  pico_typed CT h' tags' qr r p (Build_qualified_type (qc2q qc) C) (Iot (dom h)).
Proof.
  intros Hheap Hr Hp Hwf Hfs Hvs new_tag tags' t h'.
  assert (Hb : runtime_getObj h' (dom h) = Some (mkObj t vs)).
  { unfold runtime_getObj, h'. rewrite (nth_error_app2 h [mkObj t vs] (Nat.le_refl (dom h))).
    rewrite Nat.sub_diag. reflexivity. }
  assert (Ha : forall l o, runtime_getObj h l = Some o ->
               runtime_getObj h' l = Some o /\ tags' l = tags l).
  { intros l o Ho. unfold runtime_getObj in *. unfold h', tags'.
    assert (l < dom h) by (apply nth_error_Some; congruence).
    rewrite (nth_error_app1 _ _ H). destruct (Nat.eq_dec l (dom h)); [lia|auto]. }
  assert (Hex : pico_extension h tags h' tags').
  { intros l ty Ht. apply pico_r_type_get in Ht as (o & Ho & Hty). subst ty.
    destruct (Ha _ _ Ho) as [Ho' Htag]. unfold r_type. rewrite Ho'. auto. }
  assert (Hnew : tags' (dom h) = new_tag).
  { unfold tags'. destruct (Nat.eq_dec (dom h) (dom h)); reflexivity || contradiction. }
  split; [|split; [exact Hex|]].
  - intros l o Ho.
    destruct (lt_dec l (dom h)) as [Hl|Hl].
    + assert (runtime_getObj h l = Some o) as Hold.
      { unfold h', runtime_getObj in Ho. now rewrite nth_error_app1 in Ho. }
      destruct (Hheap _ _ Hold) as (Hn & Hwf' & Hfields).
      destruct (Ha _ _ Hold) as [_ Htag]. rewrite Htag.
      split; [exact Hn|split; [exact Hwf'|]].
      intros f fd v HF HV. specialize (Hfields _ _ _ HF HV).
      eapply pico_value_map with (rename := fun x => x); eauto.
    + assert (l = dom h).
      { unfold runtime_getObj, h' in Ho. assert (l < length (h ++ [mkObj t vs])) as Hlt
          by (apply nth_error_Some; congruence).
        rewrite length_app in Hlt. simpl in Hlt. lia. }
      subst l. rewrite Hb in Ho. inversion Ho; subst o.
      simpl. rewrite Hnew. split; [destruct qc; assumption|split; [exact Hwf|]].
      intros f fd v HF HV. inversion HF; subst.
      assert (fields = fs) by eauto using pico_fields_deterministic. subst fields.
      pose proof (pico_nth_forall2 _ _ _ Hvs _ _ _ Hget HV) as Hfield.
      eapply pico_value_map with (rename := fun x => x); eauto.
  - unfold pico_typed. simpl. exists t. unfold r_type. rewrite Hb Hnew.
    split; [reflexivity|]. split.
    + constructor. unfold wf_rtypeuse in Hwf. destruct (bound CT C); tauto.
    + apply pico_create_cap.
Qed.

(* Entering a call adds one edge from the receiver's region to a fresh
   region. Merging the two regions at return removes that edge. *)
Local Definition pico_add_edge (E : nat -> nat -> Prop) r p a b :=
  E a b \/ (a = r /\ b = p).

Local Definition pico_merge r p l := if Nat.eq_dec l p then r else l.

Local Lemma pico_enter n E r :
  r < n -> pico_edges n E ->
  pico_edges (S n) (pico_add_edge E r n) /\
  (forall j, pico_add_edge E r n n j -> j = n).
Proof.
  intros Hr HE. unfold pico_add_edge, pico_edges in *.
  split; intros ?; [intros ?|]; intros [H|[H1 H2]];
    try specialize (HE _ _ H); lia.
Qed.

Local Lemma pico_heap_enter CT h tags n E r :
  pico_heap CT h tags n E -> pico_heap CT h tags (S n) (pico_add_edge E r n).
Proof.
  intros H l o Ho. destruct (H _ _ Ho) as (Hn & Hwf & HF).
  split; [lia|split; [exact Hwf|]].
  intros f fd v Hfd Hv. specialize (HF _ _ _ Hfd Hv).
  eapply pico_value_map with (rename := fun x => x); [| | |exact HF]; eauto.
  intros ql k. destruct (mutability (ftype fd)); cbn; firstorder.
Qed.

Local Lemma pico_merge_old r p n : n < p -> pico_merge r p n = n.
Proof. intros Hlt. unfold pico_merge. destruct (Nat.eq_dec n p) as [Heq|Hne]; [lia|reflexivity]. Qed.

Local Lemma pico_heap_merge CT h tags n E r :
  r < n -> pico_edges n E ->
  pico_heap CT h tags (S n) (pico_add_edge E r n) ->
  pico_heap CT h (fun l => pico_merge r n (tags l)) n E.
Proof.
  intros Hr HE H l o Ho. destruct (H _ _ Ho) as (Hn & Hwf & HF).
  split.
  - change (pico_merge r n (tags l) < n). unfold pico_merge.
    destruct (Nat.eq_dec (tags l) n) as [Heq|Hne]; simpl; lia.
  - split; [exact Hwf|]. intros f fd v Hfd Hv.
    specialize (HF _ _ _ Hfd Hv).
    eapply pico_value_map with (rename := pico_merge r n); [| | |exact HF]; eauto.
    intros ql k. destruct (mutability (ftype fd)), (rqtype (rt_type o));
      cbn [pico_field_cap pico_cap]; try (intuition congruence).
    + intros [Hq Hk]. split; [exact Hq|]. intros _.
      destruct (Hk eq_refl) as [->|[Hedge|[Ha Hb]]]; auto.
      * right. destruct (HE _ _ Hedge) as [H1 H2].
        rewrite !pico_merge_old; auto.
      * left. rewrite Ha Hb. rewrite (pico_merge_old r n r Hr).
        unfold pico_merge. destruct (Nat.eq_dec n n); reflexivity || contradiction.
Qed.

Local Lemma pico_typed_merge CT h tags qr n r T v :
  r < n ->
  pico_typed CT h tags qr r n T v ->
  pico_typed CT h (fun l => pico_merge r n (tags l)) qr r r T v.
Proof.
  intros Hr HV.
  eapply pico_value_map with (rename := pico_merge r n); [| | |exact HV]; eauto.
  intros ql k. destruct (sqtype T), qr; cbn; try tauto;
    intros [Hq ->]; split; auto using pico_merge_old;
    unfold pico_merge; destruct (Nat.eq_dec n n); reflexivity || contradiction.
Qed.

Local Lemma pico_call_scope caller callee :
  readonly_state_method_scope caller ->
  method_scope_subtype callee caller ->
  readonly_state_method_scope callee /\
  (caller = TransitiveState -> callee = TransitiveState).
Proof.
  intros [H|H] HS; subst caller; inversion HS; subst;
    unfold readonly_state_method_scope; auto; congruence.
Qed.

Local Lemma pico_call_start CT h tags n E s env ctx r p mt y Ty zs argtypes
    m md ly vals cy md' :
  wf_class_table CT ->
  pico_heap CT h tags n E -> pico_frame CT h tags ctx r p s env ->
  readonly_state_method_scope mt ->
  static_getType s y = Some Ty ->
  static_getType_list s zs = Some argtypes ->
  FindMethodWithName CT (sctype Ty) m md ->
  (qualified_type_subtype CT Ty
      (vpa_mutability_tt_readonly_state Ty (mreceiver (msignature md))) \/
   sqtype Ty = RO /\ sqtype (mreceiver (msignature md)) = RDM /\
      base_subtype CT (sctype Ty) (sctype (mreceiver (msignature md)))) ->
  Forall2 (fun arg T => qualified_type_subtype CT arg
          (vpa_mutability_tt_readonly_state Ty T)) argtypes (mparams (msignature md)) ->
  method_scope_subtype (mscope (msignature md)) mt ->
  runtime_getVal env y = Some (Iot ly) -> runtime_lookup_list env zs = Some vals ->
  r_basetype h ly = Some cy -> FindMethodWithName CT cy m md' ->
  exists ty s',
    r_type h ly = Some ty /\ rctype ty = cy /\ tags ly < n /\
    pico_cap ctx r p (sqtype Ty) (rqtype ty) (tags ly) /\
    pico_dispatch CT (rqtype ty) (msignature md') (msignature md) /\
    readonly_state_method_scope (mscope (msignature md')) /\
    (mt = TransitiveState -> mscope (msignature md') = TransitiveState) /\
    pico_frame CT h tags (rqtype ty) (tags ly) n
       (mreceiver (msignature md') :: mparams (msignature md'))
       (mkr_env (Iot ly :: vals)) /\
    stmt_typing CT (mreceiver (msignature md') :: mparams (msignature md'))
      (mscope (msignature md')) (mbody_stmt (mbody md')) s' /\
    exists rt, static_getType s' (mreturn (mbody md')) = Some rt /\
      qualified_type_subtype CT rt (mret (msignature md')).
Proof.
  intros HCT Hheap Hframe Hmt Hy Hz Hmd Hrs Hargs Hscope Hly Hvals Hbase Hmd'.
  pose proof (pico_frame_get _ _ _ _ _ _ _ _ _ _ _ Hframe Hy Hly)
    as (ty & Hty & HB & HC).
  assert (Hcy : rctype ty = cy).
  { apply pico_r_type_get in Hty as (o & Ho & <-).
    unfold r_basetype in Hbase. rewrite Ho in Hbase. congruence. }
  destruct (proj1 (pico_r_type_get _ _ _) Hty) as (o & Ho & Hrt).
  destruct (Hheap _ _ Ho) as (Hn & HW & _). rewrite Hrt in HW.
  destruct (pico_dispatch_lookup _ _ _ _ _ _ HCT HB HW Hmd)
    as (dyn & Hdyn & HD).
  rewrite Hcy in Hdyn.
  assert (dyn = md') by eauto using pico_method_unique. subst dyn.
  pose proof (pico_dispatch_scope _ _ _ _ HD) as Hsc.
  rewrite <- Hsc in Hscope.
  destruct (pico_call_scope _ _ Hmt Hscope) as [Hread Hstrict].
  destruct (pico_receiver_class _ _ _ _ HCT Hmd') as [Hclass Hmethod].
  unfold wf_method in Hmethod.
  destruct Hmethod as (_ & s' & rt & Hbody & _ & Hret & Hretsub & _ & _ & Hnomut).
  destruct (Hnomut Hread) as [Hnonrecv Hnonargs].
  exists ty, s'. split; [exact Hty|]. split; [exact Hcy|].
  split; [exact Hn|]. split; [exact HC|]. split; [exact HD|].
  split; [exact Hread|]. split; [exact Hstrict|]. split; [|eauto].
  split.
  - cbn [vars]. constructor.
    + apply pico_nonmutable_change with (p := tags ly); auto.
      unfold pico_typed. simpl. exists ty. split; auto. split; [congruence|].
      eapply pico_dispatch_receiver; [exact HD|].
      eapply pico_receiver_cap; eauto.
    + assert (Hvs : Forall2 (pico_typed CT h tags (rqtype ty) (tags ly) (tags ly))
                         (mparams (msignature md')) vals).
      { eapply pico_dispatch_args; [exact HD|].
        eapply pico_call_args; [exact HC|exact Hargs|].
        destruct Hframe as [Hf _]. eapply pico_forall2_mapM; eauto. }
      clear -Hvs Hnonargs.
      induction Hvs; inversion Hnonargs; subst; constructor; eauto using pico_nonmutable_change.
  - exists ly, ty. repeat split; auto.
Qed.

Local Lemma pico_typed_write CT h tags n E mt ctx r p s env x y l o f v :
  pico_heap CT h tags n E ->
  pico_frame CT h tags ctx r p s env ->
  readonly_state_method_scope mt ->
  stmt_typing CT s mt (SFldWrite x f y) s ->
  runtime_getVal env x = Some (Iot l) -> runtime_getObj h l = Some o ->
  runtime_getVal env y = Some v ->
  pico_heap CT (update_field h l f v) tags n E /\
  pico_extension h tags (update_field h l f v) tags /\
  pico_preserves CT mt (fun k => tags k <> p) h (update_field h l f v).
Proof.
  intros Hheap Hframe Hmt Htyping Hx Ho Hy.
  inversion Htyping; subst;
    try (unfold readonly_state_method_scope in Hmt; solve [intuition congruence]).
  all: pose proof (pico_frame_get _ _ _ _ _ _ _ _ _ _ _ Hframe Hget_x Hx)
      as (ty & Hty & HB & HC);
    unfold r_type in Hty; rewrite Ho in Hty; inversion Hty; subst ty.
  all: apply (pico_inherited_field _ _ _ _ _ HB) in Hfld_def;
    apply (pico_assign_inherit _ _ _ _ _ HB) in Hassign_rel;
    eapply pico_write_heap; try eassumption.
  all: try (intros Hq; rewrite Hq in HC; exact (proj2 HC)).
  all: intros fd Hfd;
    assert (fd = fieldT) by eauto using pico_field_unique; subst fd;
    pose proof (pico_frame_get _ _ _ _ _ _ _ _ _ _ _ Hframe Hget_y Hy) as HV;
    apply pico_sub_parts in Hsub as [Hbase Hq];
    eapply pico_value_map with (rename := fun z => z); [| | |exact HV];
    [eauto|simpl; eauto using base_trans|simpl; eauto using pico_write_cap].
Qed.

Local Lemma pico_frame_new CT h tags n E ctx r p s env x qc C ys l a vs o h' env' mt s' :
  wf_class_table CT ->
  pico_heap CT h tags n E -> pico_frame CT h tags ctx r p s env ->
  r < n -> p < n -> r = p \/ E r p ->
  stmt_typing CT s mt (SNew x qc C ys) s' ->
  runtime_getVal env 0 = Some (Iot l) -> runtime_lookup_list env ys = Some vs ->
  r_muttype h l = Some a ->
  o = mkObj (mkruntime_type (vpa_mutability_object_creation a qc) C) vs ->
  h' = h ++ [o] -> env' = set_vars env (update x (Iot (dom h)) (vars env)) ->
  exists tags', pico_heap CT h' tags' n E /\ pico_extension h tags h' tags' /\
    pico_frame CT h' tags' ctx r p s' env' /\
    forall k f, k < dom h -> pico_observe h k f = pico_observe h' k f.
Proof.
  intros HCT Hheap Hframe Hr Hp HE HT Hthis Hvs Hmut Ho -> ->.
  inversion HT; subst.
  destruct Hframe as [Hvars (l0 & t & Hl & Ht & Hqr & Htag)].
  assert (l = l0) by congruence. subst l0.
  assert (a = ctx).
  { apply pico_r_type_get in Ht as (obj & Hobj & <-).
    unfold r_muttype in Hmut. rewrite Hobj in Hmut. congruence. }
  subst a.
  pose proof (pico_constructor_wf _ _ _ HCT Hconsig) as (Hb & _ & fs & Hfs & _ & HF).
  assert (Hrt : wf_rtypeuse CT (vpa_mutability_object_creation ctx qc) C).
  { unfold wf_rtypeuse. rewrite Hb.
    split.
    - unfold bound in Hb. destruct (find_class CT C) eqn:HC; try discriminate.
      apply nth_error_Some. unfold find_class, gget in HC. congruence.
    - destruct ctx, qc, (cqualifier consig); simpl in *; first [reflexivity|congruence]. }
  assert (Hargs : Forall2 (pico_typed CT h tags ctx r p)
        (map (vpa_mutability_constructor_param qc) (cparams consig)) vs).
  { pose proof (pico_forall2_mapM _ _ _ Hvars _ _ _ Hget_args Hvs) as Htyped.
    apply Forall2_flip in Harg_sub.
    eapply pico_forall2_comp; [|exact Harg_sub|exact Htyped].
    intros U T v HS HV. eapply pico_typed_sub; [exact HS|exact HV]. }
  pose proof (pico_forall2_constructor _ _ _ _ _ _ _ _ _ _ _ _ HE Hqc HF Hargs) as Hfields.
  pose proof (pico_allocate _ _ _ _ _ _ _ _ _ _ _ _ Hheap Hr Hp Hrt Hfs Hfields)
    as (Hheap' & Hex & Hnew).
  eexists. split; [exact Hheap'|]. split; [exact Hex|]. split.
  - eapply pico_frame_update; [|exact Hnot_rcv|exact Hget_x|].
    + eapply pico_frame_extend; [exact Hex|]. split; eauto 8.
    + eapply pico_typed_sub; eauto.
  - intros k f Hk. unfold pico_observe, runtime_getObj.
    now rewrite (nth_error_app1 _ _ Hk).
Qed.

Local Lemma pico_call_result CT h h' tags tags' ctx r p n E mt ty ly
    s env sbody envbody x Tx Ty md md' retv rt :
  pico_heap CT h tags n E -> pico_edges n E ->
  pico_frame CT h tags ctx r p s env ->
  tags ly < n ->
  pico_cap ctx r p (sqtype Ty) (rqtype ty) (tags ly) ->
  pico_dispatch CT (rqtype ty) (msignature md') (msignature md) ->
  (mt = TransitiveState -> mscope (msignature md') = TransitiveState) ->
  pico_heap CT h' tags' (S n) (pico_add_edge E (tags ly) n) ->
  pico_extension h tags h' tags' ->
  pico_frame CT h' tags' (rqtype ty) (tags ly) n sbody envbody ->
  pico_preserves CT (mscope (msignature md')) (fun l => tags l <> n) h h' ->
  static_getType sbody (mreturn (mbody md')) = Some rt ->
  qualified_type_subtype CT rt (mret (msignature md')) ->
  runtime_getVal envbody (mreturn (mbody md')) = Some retv ->
  x <> 0 -> static_getType s x = Some Tx ->
  qualified_type_subtype CT (vpa_mutability_tt_readonly_state Ty (mret (msignature md))) Tx ->
  exists final_tags,
    pico_heap CT h' final_tags n E /\ pico_extension h tags h' final_tags /\
    pico_frame CT h' final_tags ctx r p s (set_vars env (update x retv (vars env))) /\
    pico_preserves CT mt (fun _ => True) h h'.
Proof.
  intros Hheap HE Hframe Hly HC HD Hscope Hheap' Hex Hbody HP Hrt Hretsub Hret Hx HTx Hsub.
  set (final_tags := fun l => pico_merge (tags ly) n (tags' l)).
  assert (Hex' : pico_extension h tags h' final_tags).
  { intros l t Ht. destruct (Hex _ _ Ht) as [Ht' Htag].
    apply pico_r_type_get in Ht as (o & Ho & Hty).
    destruct (Hheap _ _ Ho) as (Hn & _ & _).
    unfold final_tags. rewrite Htag (pico_merge_old _ _ _ Hn). auto. }
  exists final_tags. split; [eauto using pico_heap_merge|]. split; [exact Hex'|]. split.
  - eapply pico_frame_update; [eapply pico_frame_extend; eauto|exact Hx|exact HTx|].
    apply pico_typed_sub with (T := vpa_mutability_tt_readonly_state Ty (mret (msignature md)));
      [exact Hsub|].
    assert (Hret' : pico_typed CT h' final_tags (rqtype ty) (tags ly) (tags ly)
                    (mret (msignature md)) retv).
    { eapply pico_dispatch_return; [exact HD|].
      eapply pico_typed_merge; [exact Hly|].
      eapply pico_typed_sub; [exact Hretsub|].
      eapply pico_frame_get; eauto. }
    eapply pico_value_map with (rename := fun z => z); [| | |exact Hret']; eauto.
    cbn. eauto using pico_call_return_cap.
  - intros l t f Ht _ Hprot.
    apply (HP _ _ _ Ht).
    + apply pico_r_type_get in Ht as (o & Ho & _).
      destruct (Hheap _ _ Ho) as (Hn & _ & _). lia.
    + unfold pico_protected in *. intuition auto.
Qed.

Local Definition pico_outside_writes (s : stmt) (region mut : nat) :=
  match s with
  | SCall _ _ _ _ => True
  | _ => region <> mut
  end.

(* Calls start with an unused Mut region, so even their caller's own Mut
   objects are protected. At return, the temporary region is merged with the
   receiver's region to account for viewpoint adaptation and overrides. *)
Local Lemma pico_eval CT env h stmt env' h' :
  eval_stmt CT env h stmt OK env' h' ->
  forall s s' mt tags ctx r p n E,
  wf_class_table CT ->
  stmt_typing CT s mt stmt s' -> readonly_state_method_scope mt ->
  pico_edges n E -> r < n -> p < n ->
  (r = p \/ E r p) -> (forall j, E p j -> j = p) ->
  pico_heap CT h tags n E -> pico_frame CT h tags ctx r p s env ->
  exists tags', pico_heap CT h' tags' n E /\
    pico_extension h tags h' tags' /\ pico_frame CT h' tags' ctx r p s' env' /\
    pico_preserves CT mt (fun l => pico_outside_writes stmt (tags l) p) h h'.
Proof.
  intro Heval. remember OK as result eqn:Hok.
  induction Heval; try discriminate; clear Hok;
    intros s s' mt tags ctx r p n E HCT Htyping Hmt HE Hr Hp Hrp Hout Hmodel Henv_model.
  - inversion Htyping; subst. exists tags.
    split; [exact Hmodel|]. split; [unfold pico_extension; intros; split; auto|].
    split; [exact Henv_model|unfold pico_preserves; intros; reflexivity].
  - inversion Htyping; subst.
    exists tags. split; [exact Hmodel|]. split; [unfold pico_extension; intros; split; auto|]. split.
    + destruct Henv_model as [Hs (l & t & Hl & Ht & Hq & Htag)]. split.
      * simpl. apply Forall2_app; [exact Hs|]. constructor; [exact I|constructor].
      * exists l, t. unfold runtime_getVal, set_vars in *. cbn [vars].
        destruct (vars rΓ) as [|v vs]; simpl in *; try discriminate. auto.
    + unfold pico_preserves; intros; reflexivity.
  - inversion Htyping; subst.
    exists tags. split; [exact Hmodel|]. split; [unfold pico_extension; intros; split; auto|]. split.
    + eapply pico_frame_update; [exact Henv_model|exact Hnot_rcv|exact Hget_x|].
      eapply pico_typed_sub; [exact Hsub|].
      eapply pico_expr; eauto.
    + unfold pico_preserves; intros; reflexivity.
  - subst h'. assert (s' = s) by (inversion Htyping; reflexivity). subst s'.
    destruct (pico_typed_write CT h tags n E mt ctx r p s rΓ x y loc_x o f val_y Hmodel Henv_model
        Hmt Htyping Hval_x Hobj Hval_y) as (HH & HX & HF).
    exists tags. split; [exact HH|]. split; [exact HX|]. split; auto.
    eapply pico_frame_extend; eauto.
  - destruct (pico_frame_new CT h tags n E ctx r p s rΓ x q_c c ys l1 qthisr vals o h' rΓ' mt s'
                HCT Hmodel Henv_model Hr Hp Hrp Htyping Hthis Hargs Hmut
                ltac:(rewrite Hadapt; exact Hobj) Hheap Henv)
      as (tags' & HH & HX & HF & HO).
    exists tags'. split; [exact HH|]. split; [exact HX|]. split; [exact HF|].
    intros k t f Ht _ _. apply HO.
    apply pico_r_type_get in Ht as (obj & Hobj' & _).
    apply nth_error_Some. unfold runtime_getObj in Hobj'. congruence.
  - inversion Htyping; subst.
    { unfold readonly_state_method_scope in Hmt. intuition congruence. }
    destruct Hfind as [Hdynamic ->].
    destruct (pico_call_start _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      HCT Hmodel Henv_model Hmt Hget_y Hget_args Hfind_m Hrcv_sub Harg_sub Hmt_sub
      Hval_y Hargs Hbase Hdynamic)
      as (ty & sb & Hty & Hcy & Hly & Hrecv & HD & Hm & Hscope & Hf & Hbody & rt & Hrt & Hretsub).
    destruct (pico_enter _ _ _ Hly HE) as [HE' Hout'].
    assert (Hedge : tags ly = n \/ pico_add_edge E (tags ly) n (tags ly) n).
    { right. unfold pico_add_edge. auto. }
    destruct (IHHeval eq_refl _ _ _ tags (rqtype ty) (tags ly) n (S n)
              (pico_add_edge E (tags ly) n) HCT Hbody Hm HE'
              (Nat.lt_lt_succ_r _ _ Hly) (Nat.lt_succ_diag_r n) Hedge Hout'
              (pico_heap_enter _ _ _ _ _ _ Hmodel) Hf)
      as (tags' & HH & HX & HF & HP).
    eapply pico_call_result; try eassumption.
    intros l t f Ht Hneq Hprot. apply (HP _ _ _ Ht); auto.
    destruct (mbody_stmt (mbody mdef)); simpl; auto.
  - inversion Htyping; subst.
    destruct (IHHeval1 eq_refl _ _ _ tags ctx r p n E HCT Htype1 Hmt HE Hr Hp Hrp Hout Hmodel Henv_model)
      as (tags1 & HH1 & HX1 & HF1 & HP1).
    destruct (IHHeval2 eq_refl _ _ _ tags1 ctx r p n E HCT Htype2 Hmt HE Hr Hp Hrp Hout HH1 HF1)
      as (tags2 & HH2 & HX2 & HF2 & HP2).
    exists tags2. split; [exact HH2|].
    split.
    + intros l t Ht. destruct (HX1 _ _ Ht) as [Ht1 Htag1].
      destruct (HX2 _ _ Ht1) as [Ht2 Htag2]. split; [exact Ht2|congruence].
    + split; [exact HF2|]. intros l t f Ht Hne Hpr.
      destruct (HX1 _ _ Ht) as [Ht1 Htag1].
      transitivity (pico_observe h' l f).
      * apply (HP1 _ _ _ Ht); auto. destruct s1; simpl; auto.
      * apply (HP2 _ _ _ Ht1); auto. destruct s2; simpl; congruence || auto.
Qed.

Local Lemma pico_forall2_from_lookup {A B : Type} (R : A -> B -> Prop) xs ys :
  length xs = length ys ->
  (forall i x y, nth_error xs i = Some x -> nth_error ys i = Some y -> R x y) ->
  Forall2 R xs ys.
Proof.
  revert ys. induction xs as [|x xs IH]; intros [|y ys] Hlen Hlookup;
    simpl in Hlen; try discriminate; constructor.
  - exact (Hlookup 0 x y eq_refl eq_refl).
  - apply IH; [congruence|]. intros i. exact (Hlookup (S i)).
Qed.

Local Lemma pico_initial_heap CT h :
  wf_heap CT h -> pico_heap CT h (fun _ => 0) 1 (fun _ _ => False).
Proof.
  intros Hheap l o Ho.
  assert (Hl : l < dom h).
  { apply nth_error_Some. unfold runtime_getObj in Ho. congruence. }
  specialize (Hheap _ Hl). unfold wf_obj in Hheap. rewrite Ho in Hheap.
  destruct Hheap as (Hw & fs & Hfs & _ & Hfields).
  split; [lia|split; [exact Hw|]].
  intros f fd v Hfd Hv. inversion Hfd; subst.
  assert (fs = fields) by eauto using pico_fields_deterministic. subst fields.
  pose proof (pico_nth_forall2 _ _ _ Hfields _ _ _ Hv Hget) as HF.
  destruct v; [exact I|]. simpl in HF |- *.
  destruct (runtime_getObj h l0); [|contradiction].
  destruct HF as (t & Ht & HB & HQ). exists t. split; auto. split; auto.
  destruct (rqtype (rt_type o)), (mutability (ftype fd)), (rqtype t); cbn in *;
    intuition congruence.
Qed.

Local Lemma pico_initial_frame CT s env h :
  wf_r_config CT s env h ->
  exists ctx, pico_frame CT h (fun _ => 0) ctx 0 0 s env.
Proof.
  intros (HCT & Hheap & (_ & (l & Hl & Hlt) & _) & Hs & Hlen & Htypes).
  assert (Hthis : runtime_getVal env 0 = Some (Iot l)).
  { unfold runtime_getVal. destruct (vars env) as [|[|l0] tail]; simpl in *;
      try discriminate; congruence. }
  assert (Hobj : exists o, runtime_getObj h l = Some o).
  { unfold runtime_getObj. destruct (nth_error h l) eqn:Ho; eauto.
    apply nth_error_None in Ho. lia. }
  destruct Hobj as [o Ho].
  exists (rqtype (rt_type o)). split.
  - apply pico_forall2_from_lookup; auto.
    intros i T v HT Hv.
    assert (Hi : i < length s) by (apply nth_error_Some; congruence).
    specialize (Htypes _ _ Hl ltac:(unfold r_muttype; now rewrite Ho) _ Hi _ HT).
    change (runtime_getVal env i = Some v) in Hv. rewrite Hv in Htypes.
    destruct v; [exact I|]. unfold wf_r_typable in Htypes.
    destruct (r_type h l0) eqn:Ht; [|contradiction].
    destruct Htypes as [HB HQ]. exists r. split; auto. split; auto.
    destruct (sqtype T), (rqtype r), (rqtype (rt_type o)); cbn in *; tauto.
  - exists l, (rt_type o). unfold r_type. rewrite Ho. auto.
Qed.

Local Lemma pico_preserve_call CT s env h x m y zs env' h' s' mt :
  wf_r_config CT s env h ->
  stmt_typing CT s mt (SCall x m y zs) s' ->
  readonly_state_method_scope mt ->
  eval_stmt CT env h (SCall x m y zs) OK env' h' ->
  forall l o f, runtime_getObj h l = Some o ->
  pico_protected CT mt (rctype (rt_type o)) f ->
  exists vs, runtime_getObj h' l = Some (mkObj (rt_type o) vs) /\
    nth_error (fields_map o) f = nth_error vs f.
Proof.
  intros Hwf Htyping Hscope Heval l o f Ho Hprot.
  destruct (pico_initial_frame _ _ _ _ Hwf) as [ctx Hframe].
  destruct Hwf as (HCT & Hheap & _).
  destruct (pico_eval _ _ _ _ _ _ Heval _ _ _ (fun _ => 0) ctx 0 0 1
    (fun _ _ => False) HCT Htyping Hscope
    ltac:(unfold pico_edges; intros a b H; contradiction) (Nat.lt_0_succ 0) (Nat.lt_0_succ 0)
    (or_introl eq_refl) ltac:(intros j H; contradiction) (pico_initial_heap _ _ Hheap) Hframe)
    as (tags' & _ & Hex & _ & Hpres).
  assert (Ht : r_type h l = Some (rt_type o)) by (unfold r_type; now rewrite Ho).
  destruct (Hex _ _ Ht) as [Ht' _].
  apply pico_r_type_get in Ht' as ([t vs] & Ho' & Heq). simpl in Heq. subst t.
  exists vs. split; auto.
  pose proof (Hpres _ _ f Ht I Hprot) as HF.
  unfold pico_observe in HF. rewrite Ho Ho' in HF. exact HF.
Qed.

Theorem readonly_state_preservation :
  forall CT sΓ mt rΓ h stmt rΓ' h' sΓ' x y mindex Ty mdef zs vals ly
         loc_arg C anyrq vals_arg f
    (Hstmt : stmt = (SCall x mindex y zs))
    (Hstatic_type : static_getType sΓ y = Some Ty)
    (Hmethod_lookup : FindMethodWithName CT (sctype Ty) mindex mdef)
    (Hwf : wf_r_config CT sΓ rΓ h)
    (Htyping : stmt_typing CT sΓ mt stmt sΓ')
    (Hreadonly_scope : readonly_state_method_scope mt)
    (Heval : eval_stmt CT rΓ h stmt OK rΓ' h')
    (Hget_y : runtime_getVal rΓ y = Some (Iot ly))
    (Hget_zs : runtime_lookup_list rΓ zs = Some vals)
    (HinP: Ensembles.In Loc (reachable_locations_from_vals h (Iot ly :: vals)) loc_arg)
    (Harg_obj : runtime_getObj h loc_arg = Some (mkObj (mkruntime_type anyrq C) vals_arg))
    (Hassign : sf_assignability_rel CT C f Final \/ sf_assignability_rel CT C f RDA),
    exists vals_arg',
      runtime_getObj h' loc_arg = Some (mkObj (mkruntime_type anyrq C) vals_arg') /\
      nth_error vals_arg f = nth_error vals_arg' f.
Proof.
  intros. subst stmt.
  exact (pico_preserve_call CT sΓ rΓ h x mindex y zs rΓ' h' sΓ' mt
    Hwf Htyping Hreadonly_scope Heval loc_arg
    (mkObj (mkruntime_type anyrq C) vals_arg) f Harg_obj (or_intror Hassign)).
Qed.

Theorem transitive_state_preservation :
  forall CT sΓ rΓ h stmt rΓ' h' sΓ' x y mindex Ty mdef zs vals ly
         loc_arg C anyrq vals_arg f
    (Hstmt : stmt = (SCall x mindex y zs))
    (Hstatic_type : static_getType sΓ y = Some Ty)
    (Hmethod_lookup : FindMethodWithName CT (sctype Ty) mindex mdef)
    (Hwf : wf_r_config CT sΓ rΓ h)
    (Htyping : stmt_typing CT sΓ TransitiveState stmt sΓ')
    (Heval : eval_stmt CT rΓ h stmt OK rΓ' h')
    (Hget_y : runtime_getVal rΓ y = Some (Iot ly))
    (Hget_zs : runtime_lookup_list rΓ zs = Some vals)
    (HinP: Ensembles.In Loc (reachable_locations_from_vals h (Iot ly :: vals)) loc_arg)
    (Harg_obj : runtime_getObj h loc_arg = Some (mkObj (mkruntime_type anyrq C) vals_arg)),
    exists vals_arg',
      runtime_getObj h' loc_arg = Some (mkObj (mkruntime_type anyrq C) vals_arg') /\
      nth_error vals_arg f = nth_error vals_arg' f.
Proof.
  intros. subst stmt.
  exact (pico_preserve_call CT sΓ rΓ h x mindex y zs rΓ' h' sΓ' TransitiveState
    Hwf Htyping (or_intror eq_refl) Heval loc_arg
    (mkObj (mkruntime_type anyrq C) vals_arg) f Harg_obj (or_introl eq_refl)).
Qed.
