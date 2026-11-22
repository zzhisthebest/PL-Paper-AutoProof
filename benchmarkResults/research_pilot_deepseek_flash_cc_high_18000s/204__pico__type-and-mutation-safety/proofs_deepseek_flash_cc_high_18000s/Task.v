Require Import Syntax Notations Helpers Typing Subtyping Bigstep ViewpointAdaptation.

From Stdlib Require Import List.

From Stdlib Require String.

Import ListNotations.

(* ===== reconstructed development: foundations ===== *)
From Stdlib Require Import List Lia PeanoNat Bool Arith.
Import ListNotations.

Lemma nth_error_Some_lt : forall (A:Type) (l:list A) i x,
  nth_error l i = Some x -> i < length l.
Proof. intros A l i x H. apply nth_error_Some. rewrite H. discriminate. Qed.

Lemma length_update : forall (A:Type) i (x:A) l, length (update i x l) = length l.
Proof. intros A i x l. revert i. induction l as [|h t IH]; intros [|i]; simpl; auto. Qed.

Lemma update_ge : forall (A:Type) i (x:A) l, length l <= i -> update i x l = l.
Proof.
  intros A i. induction i as [|i IH]; intros x l H; destruct l; simpl in *.
  - reflexivity.
  - exfalso; lia.
  - reflexivity.
  - f_equal. apply IH. lia.
Qed.

Lemma update_lt : forall (A:Type) i (x:A) l, i < length l ->
  update i x l = firstn i l ++ x :: skipn (S i) l.
Proof.
  intros A i. induction i as [|i IH]; intros x l H; destruct l; simpl in *.
  - exfalso; lia.
  - reflexivity.
  - exfalso; lia.
  - f_equal. apply IH. lia.
Qed.

Lemma nth_error_update_same : forall (A:Type) i (x:A) l, i < length l ->
  nth_error (update i x l) i = Some x.
Proof.
  intros A i x l H.
  assert (E : update i x l = firstn i l ++ x :: skipn (S i) l) by (apply update_lt; lia).
  rewrite E.
  assert (Hsplit : nth_error (firstn i l ++ x :: skipn (S i) l) i
                 = nth_error (x :: skipn (S i) l) (i - length (firstn i l))).
  { apply nth_error_app2. rewrite length_firstn. lia. }
  rewrite Hsplit.
  replace (length (firstn i l)) with i by (rewrite length_firstn; lia).
  replace (i - i) with 0 by lia.
  simpl. reflexivity.
Qed.

Lemma nth_error_update_diff : forall (A:Type) i j (x:A) l, i <> j ->
  nth_error (update i x l) j = nth_error l j.
Proof.
  intros A. induction i as [|i IH]; intros j x l H.
  - destruct j as [|j]; [exfalso; auto|].
    destruct l as [|h t]; simpl; auto.
  - destruct j as [|j].
    + destruct l as [|h t]; simpl; auto.
    + destruct l as [|h t]; simpl; auto.
Qed.

Lemma nth_error_update_ge : forall (A:Type) i j (x:A) l, length l <= i ->
  nth_error (update i x l) j = nth_error l j.
Proof. intros. assert (E: update i x l = l) by (apply update_ge; lia). rewrite E. reflexivity. Qed.

Lemma nth_error_app_single_lt : forall (A:Type) (l:list A) a i, i < length l ->
  nth_error (l++[a]) i = nth_error l i.
Proof. intros. apply nth_error_app1. lia. Qed.

Lemma nth_error_app_single_eq : forall (A:Type) (l:list A) a,
  nth_error (l++[a]) (length l) = Some a.
Proof.
  intros A l a. assert (E : nth_error (l++[a]) (length l) = nth_error [a] (length l - length l))
    by (apply nth_error_app2; lia).
  rewrite E. replace (length l - length l) with 0 by lia. simpl. reflexivity.
Qed.

Lemma In_update : forall (A:Type) (x:A) l i v, In x (update i v l) -> In x l \/ x = v.
Proof.
  intros A x l. induction l as [|a l' IH]; intros [|i] v H; simpl in *.
  - inversion H.
  - tauto.
  - destruct H as [->|H].
    + right; auto.
    + left; right; auto.
  - destruct H as [->|H].
    + auto.
    + destruct (IH i v H) as [Hl|Hv]; [left; right; auto|right; auto].
Qed.

Lemma Forall_update_general : forall (A:Type) (P:A->Prop) (l:list A) i (v:A),
  Forall P l -> P v -> Forall P (update i v l).
Proof.
  intros A P l. induction l as [|a l' IH]; intros [|i] v Hfa Hv; simpl.
  - apply Forall_nil.
  - apply Forall_nil.
  - apply Forall_cons; [exact Hv|]. inversion Hfa; subst; auto.
  - inversion Hfa as [|? ? Ha Htl]; subst. apply Forall_cons; [exact Ha|]. apply IH; auto.
Qed.

Lemma Forall2_nth_error : forall (A B:Type) (R:A->B->Prop) (l1:list A) (l2:list B),
  Forall2 R l1 l2 -> forall k a b, nth_error l1 k = Some a -> nth_error l2 k = Some b -> R a b.
Proof.
  intros A B R l1 l2 H.
  induction H as [| x y l1' l2' HR Hfa IH]; intros [|k] a b H1 H2; simpl in *; try discriminate.
  - injection H1 as <-. injection H2 as <-. exact HR.
  - eapply IH; eauto.
Qed.

Lemma Forall2_from_nth : forall (A B:Type) (R:A->B->Prop) (l1:list A) (l2:list B),
  length l1 = length l2 ->
  (forall k a b, k < length l1 -> nth_error l1 k = Some a -> nth_error l2 k = Some b -> R a b) ->
  Forall2 R l1 l2.
Proof.
  intros A B R l1. induction l1 as [|a l1' IH]; intros l2 Hlen Hk.
  - destruct l2; [apply Forall2_nil| simpl in Hlen; discriminate].
  - destruct l2 as [|b l2']; [simpl in Hlen; discriminate|].
    simpl in Hlen. assert (Hlen' : length l1' = length l2') by lia.
    apply Forall2_cons.
    + specialize (Hk 0 a b). apply Hk; simpl; auto. lia.
    + apply IH; auto. intros k a' b' Hklt H1 H2. specialize (Hk (S k) a' b').
      apply Hk; simpl; auto; lia.
Qed.

Lemma Forall2_update_general : forall (A B:Type) (P Q:A->B->Prop) (l1:list A) (l2:list B) j (v:A),
  Forall2 P l1 l2 ->
  (forall a b, P a b -> Q a b) ->
  (forall b, nth_error l2 j = Some b -> Q v b) ->
  Forall2 Q (update j v l1) l2.
Proof.
  intros A B P Q l1. induction l1 as [|a l1' IH]; intros l2 j v Hfa Htr Hj.
  - destruct l2 as [|b l2'].
    + inversion Hfa; subst. destruct j; simpl; apply Forall2_nil.
    + inversion Hfa.
  - destruct l2 as [|b l2'].
    + inversion Hfa.
    + inversion Hfa as [| ? ? ? ? Ha Htl]; subst.
      destruct j as [|j].
      * simpl. apply Forall2_cons.
        -- apply Hj. simpl. reflexivity.
        -- eapply Forall2_impl; [|exact Htl]. intros a' b' HP. apply Htr; auto.
      * simpl. apply Forall2_cons.
        -- apply Htr; auto.
        -- apply IH with (j:=j) (v:=v).
           ++ exact Htl.
           ++ exact Htr.
           ++ intros b' Hb'. apply Hj. simpl. exact Hb'.
Qed.

Lemma get_this_update_neq : forall (vars:var_mapping) x (v:value), x <> 0 ->
  get_this_var_mapping (update x v vars) = get_this_var_mapping vars.
Proof.
  intros vars x v Hx. destruct x as [|x]; [contradiction|].
  destruct vars as [|h t]; simpl; reflexivity.
Qed.

Lemma get_this_app_single : forall (vars:var_mapping),
  get_this_var_mapping (vars ++ [Null_a]) = get_this_var_mapping vars.
Proof. intros vars. destruct vars as [|h t]; simpl; reflexivity. Qed.

Lemma get_this_from_head : forall (rΓ:r_env) l,
  runtime_getVal rΓ 0 = Some (Iot l) -> get_this_var_mapping (vars rΓ) = Some l.
Proof.
  intros rΓ l H. unfold runtime_getVal, get_this_var_mapping in *.
  destruct (vars rΓ) as [|h t]; simpl in *; [discriminate|].
  destruct h as [|loc]; simpl in *; [discriminate|].
  injection H as E. subst. reflexivity.
Qed.

Lemma head_from_get_this : forall (rΓ:r_env) l,
  get_this_var_mapping (vars rΓ) = Some l -> runtime_getVal rΓ 0 = Some (Iot l).
Proof.
  intros rΓ l H. unfold runtime_getVal, get_this_var_mapping in *.
  destruct (vars rΓ) as [|h t]; simpl in *; [discriminate|].
  destruct h as [|loc]; simpl in *; [discriminate|].
  injection H as E. subst. reflexivity.
Qed.

(* ===== mapM ===== *)
Lemma mapM_nth_error : forall (A B:Type) (f:A->option B) l l',
  mapM f l = Some l' ->
  forall i, nth_error l' i = match nth_error l i with Some x => f x | None => None end.
Proof.
  intros A B f l. induction l as [|a t IH]; intros l' H i; simpl in *.
  - inversion H; subst. destruct i; reflexivity.
  - destruct (f a) as [b|] eqn:E; [|discriminate].
    destruct (mapM f t) as [tl|] eqn:E2; [|discriminate].
    inversion H; subst.
    destruct i; simpl.
    + rewrite E. reflexivity.
    + apply IH; auto.
Qed.

Lemma mapM_nth_Some : forall (A B:Type) (f:A->option B) l l',
  mapM f l = Some l' ->
  forall i x, nth_error l' i = Some x -> exists y, nth_error l i = Some y /\ f y = Some x.
Proof.
  intros A B f l l' H i x Hx.
  pose proof (mapM_nth_error _ _ _ _ _ H i) as E. rewrite E in Hx.
  destruct (nth_error l i) as [y|] eqn:Ey; [|discriminate].
  exists y. split; auto.
Qed.

Lemma mapM_length : forall (A B:Type) (f:A->option B) l l',
  mapM f l = Some l' -> length l' = length l.
Proof.
  intros A B f l. induction l as [|a t IH]; intros l' H; simpl in *.
  - inversion H; reflexivity.
  - destruct (f a) as [b|] eqn:E; [|discriminate].
    destruct (mapM f t) as [tl|] eqn:E2; [|discriminate].
    inversion H; subst. simpl. f_equal. apply IH; auto.
Qed.

Lemma mapM_In : forall (A B:Type) (f:A->option B) l l' (y:B),
  mapM f l = Some l' -> In y l' -> exists x, In x l /\ f x = Some y.
Proof.
  intros A B f l l' y H Hin.
  destruct (In_nth_error l' y Hin) as [k Hk].
  destruct (mapM_nth_Some _ _ f l l' H k y Hk) as [x [Hx Hfx]].
  exists x. split; [|exact Hfx]. eapply nth_error_In; eauto.
Qed.

(* ===== qualifier lemmas ===== *)
Lemma q_subtype_trans : forall a b c, q_subtype a b -> q_subtype b c -> q_subtype a c.
Proof. intros a b c H1. revert c. induction H1; intros c H2; inversion H2; subst; eauto using q_subtype. Qed.

Lemma q_subtype_char : forall a b, q_subtype a b -> b = RO \/ a = b \/ a = Bot.
Proof. intros a b H; inversion H; subst; auto. Qed.

Lemma qualified_type_subtype_q : forall CT a b,
  qualified_type_subtype CT a b -> q_subtype (sqtype a) (sqtype b).
Proof.
  intros CT a b H. induction H.
  - assumption.
  - eapply q_subtype_trans; eauto.
  - apply q_refl; auto.
Qed.

Lemma qualified_type_subtype_base : forall CT a b,
  qualified_type_subtype CT a b -> base_subtype CT (sctype a) (sctype b).
Proof.
  intros CT a b H. induction H.
  - assumption.
  - eapply base_trans; eauto.
  - apply base_refl; auto.
Qed.

Lemma base_subtype_dom_l : forall CT C D, base_subtype CT C D -> C < dom CT.
Proof. intros CT C D H. induction H; auto. Qed.
Lemma base_subtype_dom_r : forall CT C D, base_subtype CT C D -> D < dom CT.
Proof. intros CT C D H. induction H; auto. Qed.

Ltac qall :=
  intros;
  repeat match goal with
    | p : qualified_type |- _ => destruct p
    | q : q |- _ => destruct q
    | r : q_r |- _ => destruct r
    | c : q_c |- _ => destruct c
    | f : q_f |- _ => destruct f
    | aa : a |- _ => destruct aa
  end;
  cbn in *;
  repeat match goal with
    | H : q_subtype _ _ |- _ => inversion H; subst; clear H
  end;
  cbn in *;
  try discriminate;
  try tauto.


Ltac qsolve :=
  intros;
  repeat match goal with
    | p : qualified_type |- _ => destruct p
    | q : q |- _ => destruct q
    | r : q_r |- _ => destruct r
    | c : q_c |- _ => destruct c
    | f : q_f |- _ => destruct f
    | aa : a |- _ => destruct aa
    | H : _ \/ _ |- _ => destruct H
  end;
  cbn in *;
  repeat match goal with
    | H : q_subtype _ _ |- _ => inversion H; subst; clear H
  end;
  cbn in *;
  try discriminate;
  try congruence;
  try tauto;
  try (apply q_bot);
  try (apply q_rd);
  try (apply q_refl; discriminate);
  try assumption.

Lemma qualifier_typable_context_mono : forall (qr qc : q_r) (qs1 qs2 : q),
  q_subtype qs1 qs2 ->
  qualifier_typable_context qr qs1 qc -> qualifier_typable_context qr qs2 qc.
Proof. qall. Qed.

Lemma ctx_mut_mut_r : forall qr qc, qualifier_typable_context qr Mut qc -> qr = Mut_r.
Proof. qall. Qed.

Lemma vpa_assignable_char : forall q a, vpa_assignability q a = Assignable ->
  a = Assignable \/ (q = Mut /\ a = RDA).
Proof. qall. Qed.

Lemma vpa_assignable_cs_ts_char : forall q a, vpa_assignability_cs_ts q a = Assignable ->
  q = Mut /\ (a = Assignable \/ a = RDA).
Proof. qall. Qed.

Lemma runtime_assign_mut_rda : runtime_vpa_assignability Mut_r RDA = Assignable.
Proof. reflexivity. Qed.
Lemma runtime_assign_any_assignable : forall qr, runtime_vpa_assignability qr Assignable = Assignable.
Proof. intros []; reflexivity. Qed.

(* ===== transfer lemmas ===== *)
Lemma rcv_transfer : forall (qr qcC : q_r) (qsTy qsR : q),
  qualifier_typable_context qr qsTy qcC ->
  q_subtype qsTy (vpa_mutability_qq_abstract_state qsTy qsR) ->
  qualifier_typable_context qr qsR qr.
Proof. qall. Qed.

Lemma param_transfer : forall (qr qcR qcC : q_r) (qsArg qsTy qsParam : q),
  qualifier_typable_context qr qsArg qcC ->
  qualifier_typable_context qcR qsTy qcC ->
  q_subtype qsArg (vpa_mutability_qq_abstract_state qsTy qsParam) ->
  qualifier_typable_context qr qsParam qcR.
Proof. qall. Qed.

Lemma ret_transfer : forall (qr qcF qcC : q_r) (qsBody qsMret qsTy qsTx : q),
  q_subtype qsBody qsMret ->
  q_subtype (vpa_mutability_qq_abstract_state qsTy qsMret) qsTx ->
  qualifier_typable_context qcF qsTy qcC ->
  qualifier_typable_context qr qsBody qcF ->
  qualifier_typable_context qr qsTx qcC.
Proof. qall. Qed.

Lemma fldread_abstract : forall (qr qobj qc : q_r) (qR : q) (m : q_f),
  qualifier_typable_context qobj qR qc ->
  qualifier_typable_heap qr (vpa_mutability_rec_fld qobj m) ->
  qualifier_typable_context qr (vpa_mutability_stype_fld_abstract_state qR m) qc.
Proof. qall. Qed.

Lemma fldread_readonly : forall (qr qobj qc : q_r) (qR : q) (m : q_f),
  qualifier_typable_context qobj qR qc ->
  qualifier_typable_heap qr (vpa_mutability_rec_fld qobj m) ->
  qualifier_typable_context qr (vpa_mutability_stype_fld_readonly_state qR m) qc.
Proof. qall. Qed.

Lemma fldwrite_abstract : forall (qr qobj qc : q_r) (qv qR : q) (m : q_f),
  qualifier_typable_context qobj qR qc ->
  qualifier_typable_context qr qv qc ->
  q_subtype qv (vpa_mutability_stype_fld_abstract_state qR m) ->
  qualifier_typable_heap qr (vpa_mutability_rec_fld qobj m).
Proof. qall. Qed.

Lemma fldwrite_readonly : forall (qr qobj qc : q_r) (qv qR : q) (m : q_f),
  qualifier_typable_context qobj qR qc ->
  qualifier_typable_context qr qv qc ->
  q_subtype qv (vpa_mutability_stype_fld_readonly_state qR m) ->
  qualifier_typable_heap qr (vpa_mutability_rec_fld qobj m).
Proof. qall. Qed.

Lemma ctor_fit : forall (qc cq : q_c) (qthis : q_r) (param : qualified_type)
                        (A : qualified_type) (qr : q_r) (m : q_f),
  q_subtype (sqtype A) (vpa_mutability_qq_abstract_state (qc2q qc) (sqtype param)) ->
  q_subtype (vpa_mutability_qq_abstract_state (qc2q cq) (sqtype param))
            (vpa_mutability_constructor_fld cq m) ->
  vpa_mutability_bound (qc2q qc) cq = qc2q qc ->
  qualifier_typable_context qr (sqtype A) qthis ->
  qualifier_typable_heap qr (vpa_mutability_rec_fld (vpa_mutability_object_creation qthis qc) m).
Proof. qall. Qed.

Lemma ctor_agree : forall (qc cq : q_c) (qthis : q_r),
  vpa_mutability_bound (qc2q qc) cq = qc2q qc ->
  vpa_mutability_runtime_bound_agree (vpa_mutability_object_creation qthis qc) cq = true.
Proof. intros qc cq qthis. destruct qc, cq, qthis; cbn; intro H; try discriminate; auto. Qed.

Lemma new_result_ctx : forall (qc : q_c) (qthis : q_r) (Tx : qualified_type),
  q_subtype (qc2q qc) (sqtype Tx) ->
  qualifier_typable_context (vpa_mutability_object_creation qthis qc) (sqtype Tx) qthis.
Proof. qall. Qed.

Lemma rcv_transfer_ro : forall (qr qcC : q_r) (qsTy qsR : q),
  qualifier_typable_context qr qsTy qcC ->
  q_subtype qsTy (vpa_mutability_qq_readonly_state qsTy qsR) ->
  qualifier_typable_context qr qsR qr.
Proof. qall. Qed.

Lemma param_transfer_ro : forall (qr qcR qcC : q_r) (qsArg qsTy qsParam : q),
  qualifier_typable_context qr qsArg qcC ->
  qualifier_typable_context qcR qsTy qcC ->
  q_subtype qsArg (vpa_mutability_qq_readonly_state qsTy qsParam) ->
  qualifier_typable_context qr qsParam qcR.
Proof. qall. Qed.

Lemma ctx_override_step2 :
  forall (qr qcR : q_r) (qc qD qC : q),
    (qc = Mut \/ qc = Imm \/ qc = RDM) ->
    (qc = Mut -> qcR = Mut_r) ->
    (qc = Imm -> qcR = Imm_r) ->
    qualifier_typable_context qr qD qcR ->
    q_subtype (vpa_mutability_qq_abstract_state qc qD) qC ->
    qualifier_typable_context qr qC qcR.
Proof.
  intros qr qcR qc qD qC Hqc HM HI Hctx Hsub.
  destruct Hqc as [Hq|[Hq|Hq]].
  - subst qc. specialize (HM eq_refl). subst qcR. qsolve.
  - subst qc. specialize (HI eq_refl). subst qcR. qsolve.
  - subst qc. qsolve.
Qed.

Lemma ctx_rdm_self : forall qr, qualifier_typable_context qr RDM qr.
Proof. intros []; cbn; tauto. Qed.

Lemma ctx_override_step : forall (qr : q_r) (qc qD qC : q),
  (qc = Mut \/ qc = Imm \/ qc = RDM) ->
  (qc = Mut -> qr = Mut_r) ->
  (qc = Imm -> qr = Imm_r) ->
  qualifier_typable_context qr qD qr ->
  q_subtype (vpa_mutability_qq_abstract_state qc qD) qC ->
  qualifier_typable_context qr qC qr.
Proof.
  intros qr qc qD qC Hqc HM HI Hctx Hsub.
  destruct Hqc as [Hq|[Hq|Hq]].
  - subst qc. specialize (HM eq_refl). subst qr. qsolve.
  - subst qc. specialize (HI eq_refl). subst qr. qsolve.
  - subst qc. qsolve.
Qed.

Lemma agree_mut : forall qr qb,
  vpa_mutability_runtime_bound_agree qr qb = true -> qb = Mut_c -> qr = Mut_r.
Proof. intros qr qb H Hq. destruct qr, qb; cbn in *; try discriminate; auto. Qed.
Lemma agree_imm : forall qr qb,
  vpa_mutability_runtime_bound_agree qr qb = true -> qb = Imm_c -> qr = Imm_r.
Proof. intros qr qb H Hq. destruct qr, qb; cbn in *; try discriminate; auto. Qed.

(* ===== value / heap predicates ===== *)
Definition value_typable (CT : class_table) (h : heap) (qc : q_r) (v : value) (T : qualified_type) : Prop :=
  match v with
  | Null_a => True
  | Iot loc => wf_r_typable CT h loc T qc
  end.

Definition field_value_ok (CT : class_table) (h : heap) (qobj : q_r) (v : value) (fdef : field_def) : Prop :=
  match v with
  | Null_a => True
  | Iot loc =>
      match runtime_getObj h loc with
      | Some _ => exists rqt, r_type h loc = Some rqt /\
          base_subtype CT (rctype rqt) (f_base_type (ftype fdef)) /\
          qualifier_typable_heap (rqtype rqt) (vpa_mutability_rec_fld qobj (mutability (ftype fdef)))
      | None => False
      end
  end.

Definition value_wf_h (h : heap) (v : value) : Prop :=
  match v with
  | Null_a => True
  | Iot loc => match runtime_getObj h loc with Some _ => True | None => False end
  end.

Lemma r_type_Some_getObj : forall h loc rqt,
  r_type h loc = Some rqt -> exists o, runtime_getObj h loc = Some o.
Proof.
  intros h loc rqt H. unfold r_type, runtime_getObj in *.
  destruct (nth_error h loc) as [o|] eqn:E; [|discriminate]. exists o. reflexivity.
Qed.

Lemma runtime_getObj_Some_lt : forall h loc o,
  runtime_getObj h loc = Some o -> loc < length h.
Proof. intros h loc o H. unfold runtime_getObj in H. eapply nth_error_Some_lt; eauto. Qed.

Lemma wf_obj_iff : forall CT h ι o, runtime_getObj h ι = Some o ->
  (wf_obj CT h ι <->
   wf_rtypeuse CT (rqtype (rt_type o)) (rctype (rt_type o)) /\
   exists fdefs, CollectFields CT (rctype (rt_type o)) fdefs /\
     length (fields_map o) = length fdefs /\
     Forall2 (field_value_ok CT h (rqtype (rt_type o))) (fields_map o) fdefs).
Proof.
  intros CT h ι o H. unfold wf_obj. rewrite H.
  split; intros [Hrt [fd [H1 [H2 H3]]]]; split; auto; exists fd; split; auto.
Qed.

Lemma wf_r_typable_rtype_eq : forall CT h h' loc T qc,
  (forall l, r_type h' l = r_type h l) ->
  wf_r_typable CT h loc T qc -> wf_r_typable CT h' loc T qc.
Proof. intros CT h h' loc T qc Heq H. unfold wf_r_typable in *. rewrite Heq. exact H. Qed.

Lemma value_typable_rtype_eq : forall CT h h' qc v T,
  (forall l, r_type h' l = r_type h l) ->
  value_typable CT h qc v T -> value_typable CT h' qc v T.
Proof.
  intros CT h h' qc v T Heq H. destruct v; simpl in *; auto.
  eapply wf_r_typable_rtype_eq; eauto.
Qed.

Lemma field_value_ok_rtype_eq : forall CT h h' qobj v fdef,
  (forall l, r_type h' l = r_type h l) ->
  field_value_ok CT h qobj v fdef -> field_value_ok CT h' qobj v fdef.
Proof.
  intros CT h h' qobj v fdef Heq H.
  destruct v as [|loc]; simpl in *; auto.
  unfold field_value_ok in *.
  destruct (runtime_getObj h loc) as [o|] eqn:E; [|contradiction].
  destruct H as [rqt [Hr [Hb Hq]]].
  assert (Hr' : r_type h' loc = Some rqt) by (rewrite Heq; auto).
  destruct (runtime_getObj h' loc) as [o'|] eqn:E'.
  - exists rqt. split; auto.
  - unfold r_type in Hr'. rewrite E' in Hr'. discriminate.
Qed.

Lemma r_type_neq_lt : forall h l, r_type h l <> None -> l < length h.
Proof.
  intros h l H. destruct (r_type h l) as [rqt|] eqn:E; [|contradiction].
  destruct (r_type_Some_getObj _ _ _ E) as [o Ho]. eapply runtime_getObj_Some_lt; exact Ho.
Qed.

Lemma wf_obj_getObj : forall CT h ι, wf_obj CT h ι -> exists o, runtime_getObj h ι = Some o.
Proof.
  intros CT h ι H. unfold wf_obj in H.
  destruct (runtime_getObj h ι) as [o|] eqn:E; [eauto|contradiction].
Qed.

Lemma field_value_ok_rtype_eq_cond : forall CT h h' qobj v fdef,
  (forall l, r_type h l <> None -> r_type h' l = r_type h l) ->
  field_value_ok CT h qobj v fdef -> field_value_ok CT h' qobj v fdef.
Proof.
  intros CT h h' qobj v fdef Heq H.
  destruct v as [|loc]; simpl in *; auto.
  unfold field_value_ok in *.
  destruct (runtime_getObj h loc) as [o|] eqn:E; [|contradiction].
  destruct H as [rqt [Hr [Hb Hq]]].
  assert (Hne : r_type h loc <> None) by (rewrite Hr; discriminate).
  assert (Hr' : r_type h' loc = Some rqt) by (rewrite (Heq loc Hne); exact Hr).
  destruct (runtime_getObj h' loc) as [o'|] eqn:E'.
  - exists rqt. split; auto.
  - unfold r_type in Hr'. rewrite E' in Hr'. discriminate.
Qed.

Lemma wf_r_typable_rtype_eq_cond : forall CT h h' loc T qc,
  (r_type h loc <> None -> r_type h' loc = r_type h loc) ->
  wf_r_typable CT h loc T qc -> wf_r_typable CT h' loc T qc.
Proof.
  intros CT h h' loc T qc Heq H. unfold wf_r_typable in *.
  destruct (r_type h loc) as [rqt|] eqn:E; [|exfalso; exact H].
  assert (He : r_type h' loc = Some rqt) by (apply Heq; discriminate).
  rewrite He. exact H.
Qed.

Lemma value_typable_rtype_eq_cond : forall CT h h' qc v T,
  (forall l, r_type h l <> None -> r_type h' l = r_type h l) ->
  value_typable CT h qc v T -> value_typable CT h' qc v T.
Proof.
  intros CT h h' qc v T Heq H.
  destruct v as [|loc]; simpl in *; auto.
  eapply wf_r_typable_rtype_eq_cond; [|exact H]. intros; apply Heq; auto.
Qed.

(* ===== heap update lemmas ===== *)
Lemma nth_error_update : forall (A:Type) i (x:A) l j, i < length l ->
  nth_error (update i x l) j = if Nat.eqb i j then Some x else nth_error l j.
Proof.
  intros A i x l j H. destruct (Nat.eqb i j) eqn:E.
  - apply Nat.eqb_eq in E; subst j. rewrite nth_error_update_same; auto.
  - apply Nat.eqb_neq in E.
    assert (Hd : nth_error (update i x l) j = nth_error l j) by (apply nth_error_update_diff; auto).
    rewrite Hd. reflexivity.
Qed.

Lemma length_update_field : forall h ι f v, length (update_field h ι f v) = length h.
Proof.
  intros h ι f v. unfold update_field.
  destruct (runtime_getObj h ι) as [o|]; [|reflexivity]. simpl. apply length_update.
Qed.

Lemma r_type_update_field : forall h ι f v loc,
  r_type (update_field h ι f v) loc = r_type h loc.
Proof.
  intros h ι f v loc. unfold update_field.
  destruct (runtime_getObj h ι) as [o|] eqn:E; [|reflexivity].
  assert (Hlen : ι < length h) by (unfold runtime_getObj in E; eapply nth_error_Some_lt; eauto).
  unfold runtime_getObj in E.
  unfold r_type, runtime_getObj.
  assert (Hupd : nth_error (update ι (set_fields_map o (update f v (fields_map o))) h) loc
               = if Nat.eqb ι loc
                 then Some (set_fields_map o (update f v (fields_map o)))
                 else nth_error h loc) by (apply nth_error_update; lia).
  rewrite Hupd.
  destruct (Nat.eqb ι loc) eqn:E2.
  - apply Nat.eqb_eq in E2; subst loc. rewrite E. reflexivity.
  - reflexivity.
Qed.

Lemma runtime_getObj_update_field_Some : forall h ι f v loc,
  runtime_getObj h loc <> None -> runtime_getObj (update_field h ι f v) loc <> None.
Proof.
  intros h ι f v loc H. unfold update_field.
  destruct (runtime_getObj h ι) as [o|] eqn:E; [|auto].
  assert (Hlen : ι < length h) by (unfold runtime_getObj in E; eapply nth_error_Some_lt; eauto).
  unfold runtime_getObj in *.
  assert (Hupd : nth_error (update ι (set_fields_map o (update f v (fields_map o))) h) loc
               = if Nat.eqb ι loc
                 then Some (set_fields_map o (update f v (fields_map o)))
                 else nth_error h loc) by (apply nth_error_update; lia).
  rewrite Hupd.
  destruct (Nat.eqb ι loc); [discriminate|auto].
Qed.

Lemma runtime_getObj_update_field_other : forall h ι f v loc, loc <> ι ->
  runtime_getObj (update_field h ι f v) loc = runtime_getObj h loc.
Proof.
  intros h ι f v loc Hne. unfold update_field.
  destruct (runtime_getObj h ι) as [o|] eqn:E; [|reflexivity].
  assert (Hlen : ι < length h) by (unfold runtime_getObj in E; eapply nth_error_Some_lt; eauto).
  unfold runtime_getObj.
  assert (Hupd : nth_error (update ι (set_fields_map o (update f v (fields_map o))) h) loc
               = if Nat.eqb ι loc
                 then Some (set_fields_map o (update f v (fields_map o)))
                 else nth_error h loc) by (apply nth_error_update; lia).
  rewrite Hupd.
  destruct (Nat.eqb ι loc) eqn:E2.
  - apply Nat.eqb_eq in E2. exfalso. apply Hne; auto.
  - reflexivity.
Qed.

Lemma r_type_app_singleton : forall h o loc, loc < length h ->
  r_type (h++[o]) loc = r_type h loc.
Proof.
  intros h o loc H. unfold r_type, runtime_getObj.
  assert (E : nth_error (h++[o]) loc = nth_error h loc) by (apply nth_error_app1; lia).
  rewrite E. reflexivity.
Qed.

Lemma runtime_getObj_app_singleton : forall h o loc, loc < length h ->
  runtime_getObj (h++[o]) loc = runtime_getObj h loc.
Proof.
  intros h o loc H. unfold runtime_getObj.
  assert (E : nth_error (h++[o]) loc = nth_error h loc) by (apply nth_error_app1; lia).
  rewrite E. reflexivity.
Qed.

Lemma runtime_getObj_app_singleton_last : forall h o,
  runtime_getObj (h++[o]) (length h) = Some o.
Proof.
  intros h o. unfold runtime_getObj.
  assert (E : nth_error (h++[o]) (length h) = nth_error [o] (length h - length h))
    by (apply nth_error_app2; lia).
  rewrite E. replace (length h - length h) with 0 by lia. simpl. reflexivity.
Qed.

(* ===== CollectFields ===== *)
Lemma find_class_fun : forall CT C d1 d2,
  find_class CT C = Some d1 -> find_class CT C = Some d2 -> d1 = d2.
Proof. intros. rewrite H in H0. injection H0 as E. auto. Qed.

Lemma CollectFields_det : forall CT C fs1, CollectFields CT C fs1 ->
  forall fs2, CollectFields CT C fs2 -> fs1 = fs2.
Proof.
  intros CT C fs1 H.
  induction H as
    [ CT C Hnone
    | CT C def Hfind Hsuper
    | CT C def parent pfs ofs Hfind Hsuper Hpcf IH Hown ];
    intros fs2 H2.
  - inversion H2; subst; try congruence.
  - inversion H2; subst; try congruence.
  - inversion H2; subst; try congruence.
    assert (Hdef : def = def0) by (exact (find_class_fun CT C def def0 Hfind Hfind0)).
    subst def0. rewrite Hsuper in Hsuper0. injection Hsuper0 as Hpar. subst parent0.
    rewrite (IH parent_fields Hparent_cf). reflexivity.
Qed.

Lemma CollectFields_inv_inherit : forall CT C def parent fsC,
  find_class CT C = Some def ->
  super (signature def) = Some parent ->
  CollectFields CT C fsC ->
  exists pfs own, CollectFields CT parent pfs /\ fsC = pfs ++ own.
Proof.
  intros CT C def parent fsC Hf Hs Hc.
  inversion Hc; subst; try congruence.
  assert (Hdef : def = def0) by (exact (find_class_fun CT C def def0 Hf Hfind)).
  subst def0. rewrite Hs in Hsuper. injection Hsuper as Hpar. subst parent0.
  exists parent_fields, (fields (body def)). split; [exact Hparent_cf|reflexivity].
Qed.

Lemma parent_lookup_find : forall CT C D, parent_lookup CT C = Some D ->
  exists def, find_class CT C = Some def /\ super (signature def) = Some D.
Proof.
  intros CT C D H. unfold parent_lookup in H.
  destruct (find_class CT C) as [def|] eqn:E; [|discriminate].
  exists def. split; auto.
Qed.

Lemma wf_constructor_object_CollectFields : forall CT C ctor,
  wf_constructor_object CT C ctor -> CollectFields CT C [].
Proof. intros CT C ctor H. unfold wf_constructor_object in H. tauto. Qed.

Lemma wf_constructor_object_bound : forall CT C ctor,
  wf_constructor_object CT C ctor -> bound CT C = Some (cqualifier (csignature ctor)).
Proof.
  intros CT C ctor H. unfold wf_constructor_object in H. destruct H as [Hp [Hl [Hb _]]].
  symmetry. exact Hb.
Qed.

Lemma wf_constructor_object_cparams : forall CT C ctor,
  wf_constructor_object CT C ctor -> cparams (csignature ctor) = [].
Proof. intros CT C ctor H. unfold wf_constructor_object in H. tauto. Qed.

Lemma wf_class_table_cname : forall CT C def, wf_class_table CT -> find_class CT C = Some def -> cname (signature def) = C.
Proof.
  intros CT C def Hwf Hf.
  unfold wf_class_table in Hwf. cbn in Hwf.
  destruct Hwf as [Hall [Hobj [Hnon Hname]]]. apply Hname; auto.
Qed.

Lemma find_class_In : forall CT C def, find_class CT C = Some def -> In def CT.
Proof. intros CT C def H. unfold find_class, gget in H. eapply nth_error_In; eauto. Qed.

Lemma find_class_dom : forall CT C def, find_class CT C = Some def -> C < dom CT.
Proof. intros CT C def H. unfold find_class, gget in H. eapply nth_error_Some_lt; eauto. Qed.

Lemma find_class_wf_class : forall CT C def, wf_class_table CT -> find_class CT C = Some def -> wf_class CT def.
Proof.
  intros CT C def Hwf Hf.
  unfold wf_class_table in Hwf. cbn in Hwf. destruct Hwf as [Hall _].
  rewrite Forall_forall in Hall. apply Hall. eapply find_class_In; eauto.
Qed.

Lemma CollectFields_exists : forall CT C, wf_class_table CT -> C < dom CT -> exists fs, CollectFields CT C fs.
Proof.
  intros CT C Hwf Hdom.
  destruct (find_class CT C) as [def|] eqn:Ef.
  - pose proof (find_class_wf_class _ _ _ Hwf Ef) as Hwc.
    pose proof (wf_class_table_cname _ _ _ Hwf Ef) as Hcn.
    inversion Hwc; subst.
    + exists []. exact (wf_constructor_object_CollectFields CT (cname (signature def)) (constructor (body def)) Hwf_ctor).
    + cbn in H. destruct H as [Hctor [Hmeth [Hnodup Hmatch]]].
      destruct (bound CT superC) as [q_super|] eqn:Eb.
      * destruct Hmatch as [fs [Hcf _]]. exists fs. exact Hcf.
      * exists []. exact Hmatch.
  - exfalso.
    assert (Hne : nth_error CT C <> None) by (apply nth_error_Some; exact Hdom).
    unfold find_class, gget in Ef. rewrite Ef in Hne. exact (Hne eq_refl).
Qed.

Lemma CollectFields_prefix : forall CT C D,
  wf_class_table CT -> base_subtype CT C D ->
  forall fsC fsD, CollectFields CT C fsC -> CollectFields CT D fsD ->
  exists rest, fsC = fsD ++ rest.
Proof.
  intros CT C D Hwf Hsub.
  induction Hsub as [ CT C Hdom
                    | CT C D E H12 IH12 H23 IH23
                    | CT C D HdomC HdomD Hpar ]; intros fsC fsD Hc Hd.
  - exists []. rewrite (CollectFields_det CT C fsC Hc fsD Hd). rewrite app_nil_r. reflexivity.
  - destruct (CollectFields_exists CT D Hwf (base_subtype_dom_r _ _ _ H12)) as [fsD' HfsD'].
    destruct (IH12 Hwf fsC fsD' Hc HfsD') as [r1 E1].
    destruct (IH23 Hwf fsD' fsD HfsD' Hd) as [r2 E2].
    exists (r2 ++ r1). rewrite E1. rewrite E2. rewrite app_assoc. reflexivity.
  - destruct (parent_lookup_find _ _ _ Hpar) as [def [Hf Hs]].
    destruct (CollectFields_inv_inherit _ _ _ _ _ Hf Hs Hc) as [pfs [own [Hpfs HfsC]]].
    exists own. rewrite HfsC.
    assert (Hpeq : pfs = fsD) by (exact (CollectFields_det CT D pfs Hpfs fsD Hd)).
    rewrite Hpeq. reflexivity.
Qed.

Lemma FieldLookup_prefix : forall CT Cc Cs f fdef,
  wf_class_table CT -> base_subtype CT Cc Cs ->
  sf_def_rel CT Cs f fdef ->
  forall fsC, CollectFields CT Cc fsC -> gget fsC f = Some fdef.
Proof.
  intros CT Cc Cs f fdef Hwf Hsub Hfld fsC Hcf.
  unfold sf_def_rel in Hfld.
  inversion Hfld as [CT' Cs' fields f' fdef' HcfS Hget]; subst.
  destruct (CollectFields_prefix CT Cc Cs Hwf Hsub fsC fields Hcf HcfS) as [rest E].
  rewrite E. unfold gget in *.
  assert (Hflen : f < length fields) by (eapply nth_error_Some_lt; eauto).
  assert (Happ : nth_error (fields ++ rest) f = nth_error fields f) by (apply nth_error_app1; lia).
  rewrite Happ. exact Hget.
Qed.

(* ===== class / constructor / method ===== *)
Lemma bound_find : forall CT C def, find_class CT C = Some def ->
  bound CT C = Some (class_qualifier (signature def)).
Proof. intros CT C def H. unfold bound. rewrite H. reflexivity. Qed.

Lemma constructor_sig_lookup_find : forall CT C consig,
  constructor_sig_lookup CT C = Some consig ->
  exists def, find_class CT C = Some def /\ consig = csignature (constructor (body def)).
Proof.
  intros CT C consig H.
  unfold constructor_sig_lookup, constructor_def_lookup in H.
  destruct (find_class CT C) as [def|] eqn:E; [|discriminate].
  exists def. split; auto. injection H as Hc. symmetry. exact Hc.
Qed.

Lemma constructor_sig_bound : forall CT C consig,
  wf_class_table CT -> constructor_sig_lookup CT C = Some consig ->
  bound CT C = Some (cqualifier consig).
Proof.
  intros CT C consig Hwf Hlook.
  destruct (constructor_sig_lookup_find _ _ _ Hlook) as [def [Hf Hc]].
  subst consig.
  pose proof (find_class_wf_class _ _ _ Hwf Hf) as Hwc.
  pose proof (bound_find _ _ _ Hf) as Hb.
  pose proof (wf_class_table_cname _ _ _ Hwf Hf) as Hcn.
  inversion Hwc; subst; cbn in *.
  - exact (wf_constructor_object_bound CT (cname (signature def)) (constructor (body def)) Hwf_ctor).
  - destruct H as [Hctor _]. unfold wf_constructor in Hctor. destruct Hctor as [Hb' _]. exact Hb'.
Qed.

Lemma wf_class_constructor_props : forall CT C def,
  wf_class CT def -> find_class CT C = Some def -> cname (signature def) = C ->
  bound CT C = Some (cqualifier (csignature (constructor (body def)))) /\
  Forall (fun T => wf_stypeuse CT (sqtype T) (sctype T)) (cparams (csignature (constructor (body def)))) /\
  exists fs, CollectFields CT C fs /\
    length (cparams (csignature (constructor (body def)))) = length fs /\
    Forall2 (fun param fdef => qualified_type_subtype CT
       (vpa_mutability_constructor_param (cqualifier (csignature (constructor (body def)))) param)
       {| sqtype := vpa_mutability_constructor_fld (cqualifier (csignature (constructor (body def)))) (mutability (ftype fdef));
          sctype := f_base_type (ftype fdef) |})
      (cparams (csignature (constructor (body def)))) fs.
Proof.
  intros CT C def Hwc Hf Hcn.
  inversion Hwc; subst; cbn in *.
  - assert (Hcp : cparams (csignature (constructor (body def))) = [])
      by (exact (wf_constructor_object_cparams CT (cname (signature def)) (constructor (body def)) Hwf_ctor)).
    split.
    + exact (wf_constructor_object_bound CT (cname (signature def)) (constructor (body def)) Hwf_ctor).
    + split.
      * rewrite Hcp. apply Forall_nil.
      * exists []. rewrite Hcp. split.
        -- exact (wf_constructor_object_CollectFields CT (cname (signature def)) (constructor (body def)) Hwf_ctor).
        -- split; [reflexivity|apply Forall2_nil].
  - destruct H as [Hctor _]. unfold wf_constructor in Hctor.
    destruct Hctor as [Hb [Hfa Hfs]]. split; [exact Hb|]. split; [exact Hfa|exact Hfs].
Qed.

Lemma gget_method_In : forall ms m mdef, gget_method ms m = Some mdef -> In mdef ms.
Proof. intros ms m mdef H. unfold gget_method in H. apply find_some in H. tauto. Qed.

Lemma find_method_wf_method : forall CT C m mdef,
  wf_class_table CT -> FindMethodWithName CT C m mdef ->
  exists C', wf_method CT C' mdef.
Proof.
  intros CT C m mdef Hwf Hfm.
  induction Hfm as
    [ CT C def own_methods m mdef Hfind Hown Hget
    | CT C def parent m mdef own_methods Hfind Hown Hnot_here Hsuper Hparent IH ].
  - subst own_methods.
    pose proof (find_class_wf_class _ _ _ Hwf Hfind) as Hwc.
    pose proof (gget_method_In _ _ _ Hget) as Hin.
    inversion Hwc; subst; cbn in *.
    + rewrite Hno_methods in Hin. inversion Hin.
    + destruct H as [Hctor [Hmeth [Hnodup _]]].
      rewrite Forall_forall in Hmeth.
      exists (cname (signature def)). apply Hmeth. exact Hin.
  - exact (IH Hwf).
Qed.

Lemma wf_method_body_typing : forall CT C mdef,
  wf_method CT C mdef ->
  exists sΓ' mbodyrettype,
    stmt_typing CT (mreceiver (msignature mdef) :: mparams (msignature mdef))
      (mscope (msignature mdef)) (mbody_stmt (mbody mdef)) sΓ' /\
    mreturn (mbody mdef) < dom sΓ' /\
    nth_error sΓ' (mreturn (mbody mdef)) = Some mbodyrettype /\
    qualified_type_subtype CT mbodyrettype (mret (msignature mdef)).
Proof.
  intros CT C mdef H. unfold wf_method in H. cbn in H.
  destruct H as [Hret [sG' [rt [Hty [Hlt [Hnth [Hsub _]]]]]]].
  exists sG', rt. auto.
Qed.

Lemma stmt_typing_wf_senv : forall CT sΓ mt s sΓ',
  stmt_typing CT sΓ mt s sΓ' -> wf_senv CT sΓ.
Proof. intros CT sΓ mt s sΓ' H. induction H; auto. Qed.

(* ===== value / config support ===== *)
Lemma value_typable_wf : forall CT h qc v T,
  value_typable CT h qc v T -> value_wf_h h v.
Proof.
  intros CT h qc v T H. destruct v as [|loc]; simpl; auto.
  simpl in H. unfold wf_r_typable in H.
  destruct (r_type h loc) as [rqt|] eqn:E; [|contradiction].
  simpl in H.
  destruct (r_type_Some_getObj _ _ _ E) as [o Ho]. destruct (runtime_getObj h loc) as [o'|] eqn:E'; [auto|discriminate Ho].
Qed.

Lemma value_wf_mono : forall h h' v,
  (forall loc, runtime_getObj h loc <> None -> runtime_getObj h' loc <> None) ->
  value_wf_h h v -> value_wf_h h' v.
Proof.
  intros h h' v Hm H. destruct v as [|loc]; simpl in *; auto.
  destruct (runtime_getObj h loc) as [o|] eqn:E; [|contradiction].
  destruct (runtime_getObj h' loc) as [o'|] eqn:E'; [auto|].
  exfalso. apply (Hm loc); [rewrite E; discriminate|exact E'].
Qed.

Lemma vars_set_vars : forall (rΓ:r_env) l, vars (set_vars rΓ l) = l.
Proof. reflexivity. Qed.

Lemma runtime_getObj_app_singleton_other : forall h o loc, loc <> length h ->
  runtime_getObj (h++[o]) loc = runtime_getObj h loc.
Proof.
  intros h o loc Hne. unfold runtime_getObj.
  destruct (lt_eq_lt_dec loc (length h)) as [[Hlt|Heq]|Hgt].
  - assert (E : nth_error (h++[o]) loc = nth_error h loc) by (apply nth_error_app1; lia). rewrite E. reflexivity.
  - contradiction.
  - assert (E2 : nth_error (h++[o]) loc = None) by (apply nth_error_None; rewrite app_length; simpl; lia).
    assert (E1 : nth_error h loc = None) by (apply nth_error_None; lia).
    rewrite E2. rewrite E1. reflexivity.
Qed.

Lemma runtime_getObj_app_singleton_Some : forall h o loc,
  runtime_getObj h loc <> None -> runtime_getObj (h++[o]) loc <> None.
Proof.
  intros h o loc H. destruct (runtime_getObj h loc) as [ob|] eqn:E; [|contradiction].
  assert (Hlt : loc < length h) by (eapply runtime_getObj_Some_lt; eauto).
  assert (Heq : runtime_getObj (h++[o]) loc = runtime_getObj h loc)
    by (apply runtime_getObj_app_singleton_other; lia).
  rewrite Heq. rewrite E. discriminate.
Qed.

Lemma value_typable_iot : forall CT h qc loc T,
  value_typable CT h qc (Iot loc) T -> wf_r_typable CT h loc T qc.
Proof. intros. simpl in H. exact H. Qed.

Lemma value_typable_valid : forall CT h qc v T,
  value_typable CT h qc v T ->
  v = Null_a \/ (exists loc o, v = Iot loc /\ runtime_getObj h loc = Some o).
Proof.
  intros CT h qc v T H. destruct v as [|loc]; [left; auto|right].
  simpl in H. unfold wf_r_typable in H. destruct (r_type h loc) as [rqt|] eqn:E; [|contradiction].
  destruct (r_type_Some_getObj _ _ _ E) as [o Ho]. exists loc, o. split; auto.
Qed.

Lemma value_typable_sub : forall CT h qc v T1 T2,
  qualified_type_subtype CT T1 T2 ->
  value_typable CT h qc v T1 -> value_typable CT h qc v T2.
Proof.
  intros CT h qc v T1 T2 Hsub H.
  destruct v as [|loc]; simpl in *; auto.
  unfold wf_r_typable in *.
  destruct (r_type h loc) as [rqt|] eqn:E; [|contradiction].
  destruct H as [Hb Hc]. split.
  - exact (base_trans CT (rctype rqt) (sctype T1) (sctype T2) Hb (qualified_type_subtype_base CT T1 T2 Hsub)).
  - apply (qualifier_typable_context_mono (rqtype rqt) qc (sqtype T1) (sqtype T2)).
    + exact (qualified_type_subtype_q CT T1 T2 Hsub).
    + exact Hc.
Qed.

Lemma wf_renv_dom : forall CT rΓ h, wf_renv CT rΓ h -> dom (vars rΓ) > 0.
Proof. intros CT rΓ h H. unfold wf_renv in H. tauto. Qed.
Lemma wf_renv_this : forall CT rΓ h, wf_renv CT rΓ h ->
  exists iot, get_this_var_mapping (vars rΓ) = Some iot /\ iot < dom h.
Proof. intros CT rΓ h H. unfold wf_renv in H. tauto. Qed.
Lemma wf_renv_Forall : forall CT rΓ h, wf_renv CT rΓ h ->
  Forall (fun value => match value with
                       | Null_a => True
                       | Iot loc => match runtime_getObj h loc with None => False | Some _ => True end
                       end) (vars rΓ).
Proof. intros CT rΓ h H. unfold wf_renv in H. tauto. Qed.

Lemma wf_renv_valid : forall CT rΓ h, wf_renv CT rΓ h ->
  forall i v, runtime_getVal rΓ i = Some v ->
  (v = Null_a) \/ (exists loc o, v = Iot loc /\ runtime_getObj h loc = Some o).
Proof.
  intros CT rΓ h Hrenv i v Hval.
  pose proof (wf_renv_Forall _ _ _ Hrenv) as Hfa.
  rewrite Forall_forall in Hfa.
  unfold runtime_getVal in Hval.
  pose proof (Hfa v (@nth_error_In value (vars rΓ) i v Hval)) as Hv.
  destruct v as [|loc]; [left; auto|right].
  destruct (runtime_getObj h loc) as [o|] eqn:E; [exists loc, o; split; auto|contradiction].
Qed.

Lemma wf_senv_app_single : forall CT sΓ T,
  wf_senv CT sΓ -> wf_stypeuse CT (sqtype T) (sctype T) -> wf_senv CT (sΓ++[T]).
Proof.
  intros CT sΓ T [Hdom Hfa] HT. unfold wf_senv. split.
  - rewrite app_length. simpl. lia.
  - apply Forall_app. split; [exact Hfa|]. apply Forall_cons; [exact HT|apply Forall_nil].
Qed.

Lemma wf_r_config_ct : forall CT sΓ rΓ h, wf_r_config CT sΓ rΓ h -> wf_class_table CT.
Proof. intros. unfold wf_r_config in H. tauto. Qed.
Lemma wf_r_config_heap : forall CT sΓ rΓ h, wf_r_config CT sΓ rΓ h -> wf_heap CT h.
Proof. intros. unfold wf_r_config in H. tauto. Qed.
Lemma wf_r_config_renv : forall CT sΓ rΓ h, wf_r_config CT sΓ rΓ h -> wf_renv CT rΓ h.
Proof. intros. unfold wf_r_config in H. tauto. Qed.
Lemma wf_r_config_senv : forall CT sΓ rΓ h, wf_r_config CT sΓ rΓ h -> wf_senv CT sΓ.
Proof. intros. unfold wf_r_config in H. tauto. Qed.
Lemma wf_r_config_len : forall CT sΓ rΓ h, wf_r_config CT sΓ rΓ h -> length sΓ = length (vars rΓ).
Proof. intros. unfold wf_r_config in H. tauto. Qed.

Lemma wf_r_config_corr_raw : forall CT sΓ rΓ h, wf_r_config CT sΓ rΓ h ->
  forall iot qcontext,
    get_this_var_mapping (vars rΓ) = Some iot -> r_muttype h iot = Some qcontext ->
    forall i, i < length sΓ -> forall sqt, nth_error sΓ i = Some sqt ->
      match runtime_getVal rΓ i with
      | Some (Iot loc) => wf_r_typable CT h loc sqt qcontext
      | Some Null_a => True
      | None => False
      end.
Proof.
  intros CT sΓ rΓ h Hwf iot qcontext Hgt Hmut i Hi sqt Hnth.
  unfold wf_r_config in Hwf. destruct Hwf as [_ [_ [_ [_ [_ Hcorr]]]]].
  exact (Hcorr iot qcontext Hgt Hmut i Hi sqt Hnth).
Qed.

Lemma wf_r_config_corr : forall CT sΓ rΓ h, wf_r_config CT sΓ rΓ h ->
  forall iot qcontext,
    get_this_var_mapping (vars rΓ) = Some iot -> r_muttype h iot = Some qcontext ->
    forall i v T, i < length sΓ -> nth_error sΓ i = Some T ->
      runtime_getVal rΓ i = Some v -> value_typable CT h qcontext v T.
Proof.
  intros CT sΓ rΓ h Hwf iot qcontext Hgt Hmut i v T Hi Hnth Hval.
  pose proof (wf_r_config_corr_raw _ _ _ _ Hwf iot qcontext Hgt Hmut i Hi T Hnth) as Hc.
  destruct v as [|loc].
  - rewrite Hval in Hc. simpl in Hc. exact Hc.
  - rewrite Hval in Hc. simpl in Hc. exact Hc.
Qed.

Lemma wf_r_config_ctx : forall CT sΓ rΓ h, wf_r_config CT sΓ rΓ h ->
  exists iot qcontext, get_this_var_mapping (vars rΓ) = Some iot /\ r_muttype h iot = Some qcontext.
Proof.
  intros CT sΓ rΓ h Hwf.
  pose proof (wf_r_config_renv _ _ _ _ Hwf) as Hrenv.
  destruct (wf_renv_this _ _ _ Hrenv) as [iot [Hgt Hlt]].
  destruct (wf_obj_getObj _ _ _ ((wf_r_config_heap _ _ _ _ Hwf) iot Hlt)) as [o Ho].
  exists iot, (rqtype (rt_type o)). split; [exact Hgt|].
  unfold r_muttype. rewrite Ho. reflexivity.
Qed.

Lemma wf_obj_update_field_other : forall CT h ι f v loc,
  wf_obj CT h loc -> loc <> ι -> wf_obj CT (update_field h ι f v) loc.
Proof.
  intros CT h ι f v loc H Hne.
  unfold wf_obj in *.
  destruct (runtime_getObj h loc) as [o|] eqn:E; [|contradiction].
  assert (Hge : runtime_getObj (update_field h ι f v) loc = Some o)
    by (rewrite runtime_getObj_update_field_other; auto).
  rewrite Hge. simpl in *.
  destruct H as [Hrt [fds [Hcf [Hlen Hfa]]]].
  split; [exact Hrt|]. exists fds. split; [exact Hcf|]. split; [exact Hlen|].
  eapply Forall2_impl; [|exact Hfa].
  intros a b Ha. eapply field_value_ok_rtype_eq; [|exact Ha]. intros ll. apply r_type_update_field.
Qed.



Lemma wf_obj_app_singleton : forall CT h o loc, loc < length h ->
  wf_obj CT h loc -> wf_obj CT (h++[o]) loc.
Proof.
  intros CT h o loc Hlt H.
  unfold wf_obj in *.
  destruct (runtime_getObj h loc) as [obj|] eqn:E; [|contradiction].
  assert (Hge : runtime_getObj (h++[o]) loc = Some obj).
  { unfold runtime_getObj. assert (Eapp : nth_error (h++[o]) loc = nth_error h loc) by (apply nth_error_app1; lia).
    rewrite Eapp. exact E. }
  rewrite Hge. simpl in *.
  destruct H as [Hrt [fds [Hcf [Hlen Hfa]]]].
  split; [exact Hrt|]. exists fds. split; [exact Hcf|]. split; [exact Hlen|].
  eapply Forall2_impl; [|exact Hfa].
  intros a b Ha. eapply field_value_ok_rtype_eq_cond; [|exact Ha].
  intros ll Hne. apply r_type_app_singleton. apply r_type_neq_lt; auto.
Qed.

(* ===== expression value typability ===== *)
Lemma eval_expr_value_typable :
  forall CT sΓ mt e Te,
    expr_has_type CT sΓ mt e Te ->
    forall rΓ h iot qcontext v,
      wf_r_config CT sΓ rΓ h ->
      get_this_var_mapping (vars rΓ) = Some iot ->
      r_muttype h iot = Some qcontext ->
      eval_expr CT rΓ h e v OK rΓ h ->
      value_typable CT h qcontext v Te.
Proof.
  intros CT sΓ mt e Te Hty.
  induction Hty as
    [ CT sΓ mt q cn Hwf_s Hdom
    | CT sΓ mt x T Hwf_s Hget
    | CT sΓ mt x T fDef f Hwf_s Hget_x Hfld Hmt
    | CT sΓ mt x T fDef f Hwf_s Hget_x Hfld Hmt ];
    intros rΓ h iot qcontext v Hwf Hgt Hmut Hev.
  - inversion Hev; subst. simpl. auto.
  - inversion Hev; subst.
    eapply wf_r_config_corr; eauto.
    unfold static_getType in Hget. eapply nth_error_Some_lt; eauto.
  - inversion Hev; subst.
    assert (Hi : x < length sΓ) by (unfold static_getType in Hget_x; eapply nth_error_Some_lt; eauto).
    pose proof (wf_r_config_corr CT sΓ rΓ h Hwf iot qcontext Hgt Hmut x (Iot v0) T Hi Hget_x Hval) as Hx.
    assert (Er : r_type h v0 = Some (rt_type o)) by (unfold r_type; rewrite Hobj; reflexivity).
    pose proof (value_typable_iot _ _ _ _ _ Hx) as Hxw.
    unfold wf_r_typable in Hxw. rewrite Er in Hxw. simpl in Hxw.
    destruct Hxw as [HbT HcT].
    assert (Hlt : v0 < length h) by (eapply runtime_getObj_Some_lt; eauto).
    assert (Hwfobj : wf_obj CT h v0) by (apply (wf_r_config_heap _ _ _ _ Hwf); exact Hlt).
    destruct (wf_obj_iff CT h v0 o Hobj) as [Hiff _].
    destruct (Hiff Hwfobj) as [Hrtuse [fds [Hcf [Hlen Hfa]]]].
    assert (Hgget : gget fds f = Some fDef).
    { exact (FieldLookup_prefix CT (rctype (rt_type o)) (sctype T) f fDef
               (wf_r_config_ct _ _ _ _ Hwf) HbT Hfld fds Hcf). }
    assert (HfLen : f < length (fields_map o)) by (unfold getVal in Hfield; eapply nth_error_Some_lt; eauto).
    assert (HfLen' : f < length fds) by lia.
    assert (HfdSome : nth_error fds f <> None) by (apply nth_error_Some; lia).
    destruct (nth_error fds f) as [fdx|] eqn:Efd; [|contradiction].
    unfold gget in Hgget. rewrite Efd in Hgget. injection Hgget as Hfx. subst fdx.
    assert (Hvf : field_value_ok CT h (rqtype (rt_type o)) v fDef).
    { eapply (Forall2_nth_error value field_def (field_value_ok CT h (rqtype (rt_type o))) (fields_map o) fds Hfa f v fDef).
      - unfold getVal in Hfield. exact Hfield.
      - exact Efd. }
    destruct v as [|loc].
    + simpl. auto.
    + simpl. unfold field_value_ok in Hvf.
      destruct (runtime_getObj h loc) as [o2|] eqn:E2; [|contradiction].
      destruct Hvf as [rqt [Hr [Hb Hq]]].
      unfold wf_r_typable. rewrite Hr. split; [exact Hb|].
      eapply fldread_abstract; [exact HcT|exact Hq].
  - inversion Hev; subst.
    assert (Hi : x < length sΓ) by (unfold static_getType in Hget_x; eapply nth_error_Some_lt; eauto).
    pose proof (wf_r_config_corr CT sΓ rΓ h Hwf iot qcontext Hgt Hmut x (Iot v0) T Hi Hget_x Hval) as Hx.
    assert (Er : r_type h v0 = Some (rt_type o)) by (unfold r_type; rewrite Hobj; reflexivity).
    pose proof (value_typable_iot _ _ _ _ _ Hx) as Hxw.
    unfold wf_r_typable in Hxw. rewrite Er in Hxw. simpl in Hxw.
    destruct Hxw as [HbT HcT].
    assert (Hlt : v0 < length h) by (eapply runtime_getObj_Some_lt; eauto).
    assert (Hwfobj : wf_obj CT h v0) by (apply (wf_r_config_heap _ _ _ _ Hwf); exact Hlt).
    destruct (wf_obj_iff CT h v0 o Hobj) as [Hiff _].
    destruct (Hiff Hwfobj) as [Hrtuse [fds [Hcf [Hlen Hfa]]]].
    assert (Hgget : gget fds f = Some fDef).
    { exact (FieldLookup_prefix CT (rctype (rt_type o)) (sctype T) f fDef
               (wf_r_config_ct _ _ _ _ Hwf) HbT Hfld fds Hcf). }
    assert (HfLen : f < length (fields_map o)) by (unfold getVal in Hfield; eapply nth_error_Some_lt; eauto).
    assert (HfLen' : f < length fds) by lia.
    assert (HfdSome : nth_error fds f <> None) by (apply nth_error_Some; lia).
    destruct (nth_error fds f) as [fdx|] eqn:Efd; [|contradiction].
    unfold gget in Hgget. rewrite Efd in Hgget. injection Hgget as Hfx. subst fdx.
    assert (Hvf : field_value_ok CT h (rqtype (rt_type o)) v fDef).
    { eapply (Forall2_nth_error value field_def (field_value_ok CT h (rqtype (rt_type o))) (fields_map o) fds Hfa f v fDef).
      - unfold getVal in Hfield. exact Hfield.
      - exact Efd. }
    destruct v as [|loc].
    + simpl. auto.
    + simpl. unfold field_value_ok in Hvf.
      destruct (runtime_getObj h loc) as [o2|] eqn:E2; [|contradiction].
      destruct Hvf as [rqt [Hr [Hb Hq]]].
      unfold wf_r_typable. rewrite Hr. split; [exact Hb|].
      eapply fldread_readonly; [exact HcT|exact Hq].
Qed.

(* ===== method ancestry / dispatch support ===== *)
Lemma wf_method_rcv_class : forall CT C mdef,
  wf_method CT C mdef -> sctype (mreceiver (msignature mdef)) = C.
Proof.
  intros CT C mdef H. unfold wf_method in H. cbn in H.
  destruct H as [_ [sG' [rt Hbody]]].
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  assumption.
Qed.

Lemma find_method_class_dom : forall CT C m mdef,
  FindMethodWithName CT C m mdef -> C < dom CT.
Proof.
  intros CT C m mdef H. induction H.
  - eapply find_class_dom; eauto.
  - eapply find_class_dom; eauto.
Qed.

Lemma find_method_base : forall CT C m mdef,
  wf_class_table CT -> FindMethodWithName CT C m mdef ->
  base_subtype CT C (sctype (mreceiver (msignature mdef))).
Proof.
  intros CT C m mdef Hwf Hfm. induction Hfm as
    [ CT C def own_methods m mdef Hfind Hown Hget
    | CT C def parent m mdef own_methods Hfind Hown Hnot_here Hsuper Hparent IH ].
  - subst own_methods.
    pose proof (find_class_wf_class _ _ _ Hwf Hfind) as Hwc.
    pose proof (wf_class_table_cname _ _ _ Hwf Hfind) as Hcn.
    pose proof (gget_method_In _ _ _ Hget) as Hin.
    inversion Hwc; subst; cbn in *.
    + rewrite Hno_methods in Hin. inversion Hin.
    + destruct H as [Hctor [Hmeth [Hnodup _]]].
      rewrite Forall_forall in Hmeth.
      pose proof (Hmeth mdef Hin) as Hwfm.
      rewrite (wf_method_rcv_class _ _ _ Hwfm).
      apply base_refl. eapply find_class_dom; eauto.
  - apply (base_trans CT C parent (sctype (mreceiver (msignature mdef)))).
    + apply base_extends.
      * eapply find_class_dom; eauto.
      * eapply find_method_class_dom; eauto.
      * unfold parent_lookup. rewrite Hfind. simpl. exact Hsuper.
    + exact (IH Hwf).
Qed.

Lemma wf_stypeuse_dom : forall CT q c, wf_stypeuse CT q c -> c < dom CT.
Proof. intros CT q c H. unfold wf_stypeuse in H. destruct (bound CT c); tauto. Qed.

Lemma wf_method_wf_senv : forall CT C mdef,
  wf_method CT C mdef -> wf_senv CT (mreceiver (msignature mdef) :: mparams (msignature mdef)).
Proof.
  intros CT C mdef H.
  destruct (wf_method_body_typing _ _ _ H) as [sG' [rt [Hty _]]].
  eapply stmt_typing_wf_senv; eauto.
Qed.

Lemma wf_method_type_dom : forall CT C mdef T,
  wf_method CT C mdef -> In T (mreceiver (msignature mdef) :: mparams (msignature mdef)) ->
  sctype T < dom CT.
Proof.
  intros CT C mdef T H Hin.
  pose proof (wf_method_wf_senv _ _ _ H) as Hsenv.
  unfold wf_senv in Hsenv. destruct Hsenv as [Hdom Hfa].
  rewrite Forall_forall in Hfa.
  apply wf_stypeuse_dom with (q := sqtype T). apply Hfa. exact Hin.
Qed.

Lemma find_method_det : forall CT C m d1,
  FindMethodWithName CT C m d1 ->
  forall d2, FindMethodWithName CT C m d2 -> d1 = d2.
Proof.
  intros CT C m d1 H. induction H as
    [ CT C def own_methods m d1 Hfind Hown Hget
    | CT C def parent m d1 own_methods Hfind Hown Hnot_here Hsuper Hparent IH ];
    intros d2 H2.
  - inversion H2; subst; try congruence.
  - inversion H2; subst; try congruence.
    assert (Hdef : def0 = def) by (exact (find_class_fun CT C def0 def Hfind0 Hfind)).
    subst def0. rewrite Hsuper in Hsuper0. injection Hsuper0 as Hp. subst parent0.
    exact (IH d2 Hparent_fmn).
Qed.

Lemma find_method_exists_ancestor : forall CT P D m,
  wf_class_table CT -> base_subtype CT P D ->
  forall mdef0, FindMethodWithName CT D m mdef0 ->
  exists mdefP, FindMethodWithName CT P m mdefP.
Proof.
  intros CT P D m Hwf Hsub. induction Hsub as
    [ CT P Hdom
    | CT P D1 D H1 IH1 H2 IH2
    | CT P D HdomP HdomD Hpar ];
    intros mdef0 Hfind0.
  - exists mdef0. exact Hfind0.
  - destruct (IH2 Hwf mdef0 Hfind0) as [mdef1 Hfind1].
    exact (IH1 Hwf mdef1 Hfind1).
  - destruct (parent_lookup_find _ _ _ Hpar) as [defP [Hf Hsuper]].
    destruct (gget_method (methods (body defP)) m) as [mdefP|] eqn:Eget.
    + exists mdefP. exact (FOM_Here CT P defP (methods (body defP)) m mdefP Hf eq_refl Eget).
    + exists mdef0. exact (FOM_Super CT P defP D m mdef0 (methods (body defP)) Hf eq_refl Eget Hsuper Hfind0).
Qed.

(* ===== dispatch support ===== *)
Lemma gget_method_mname : forall ms m mdef,
  gget_method ms m = Some mdef -> mname (msignature mdef) = m.
Proof.
  intros ms m mdef H. unfold gget_method in H. apply find_some in H. destruct H as [_ Heq].
  unfold eq_method_name in Heq. apply Nat.eqb_eq in Heq. exact Heq.
Qed.

Lemma moc_parts : forall CT qc (o r : method_sig),
  method_override_compatible CT qc r o ->
  Forall2 (fun po pr => qualified_type_subtype CT (vpa_mutability_override qc po) pr) (mparams o) (mparams r) /\
  q_subtype (sqtype (vpa_mutability_override qc (mreceiver o))) (sqtype (mreceiver r)).
Proof. intros CT qc o r H. unfold method_override_compatible in H. tauto. Qed.

Lemma Forall2_trans_gen : forall (A:Type) (R S T:A->A->Prop) l1 l2 l3,
  (forall a b c, R a b -> S b c -> T a c) ->
  Forall2 R l1 l2 -> Forall2 S l2 l3 -> Forall2 T l1 l3.
Proof.
  intros A R S T l1. induction l1 as [|a l1' IH]; intros l2 l3 Hcomp H1 H2.
  - inversion H1; subst. inversion H2; subst. apply Forall2_nil.
  - inversion H1 as [| ? ? ? ? HR H1']; subst.
    inversion H2 as [| ? ? ? ? HS H2']; subst.
    apply Forall2_cons.
    + eapply Hcomp; eauto.
    + eapply IH; eauto.
Qed.

Lemma Forall2_impl_same : forall (A:Type) (P:A->Prop) l,
  Forall2 (fun a b => P a -> P b) l l.
Proof.
  intros A P l. induction l as [|a l' IH]; [apply Forall2_nil|].
  apply Forall2_cons; [intros H; exact H|exact IH].
Qed.

Lemma Forall2_base_refl : forall CT l,
  (forall T, In T l -> sctype T < dom CT) ->
  Forall2 (fun a b => base_subtype CT (sctype a) (sctype b)) l l.
Proof.
  intros CT l. induction l as [|a l' IH]; intros H.
  - apply Forall2_nil.
  - apply Forall2_cons.
    + apply base_refl. apply H. left. reflexivity.
    + apply IH. intros T HT. apply H. right. exact HT.
Qed.

Lemma qc2q_cases : forall (qb : q_c),
  qc2q qb = Mut \/ qc2q qb = Imm \/ qc2q qb = RDM.
Proof. intros []; cbn; auto. Qed.

(* dispatch between two methods resolved from classes C <: D *)
Definition sig_params_base (CT : class_table) (msigD msigC : method_sig) : Prop :=
  Forall2 (fun TD TC => base_subtype CT (sctype TD) (sctype TC))
    (mparams msigD) (mparams msigC).

Definition sig_params_ctx (qr qcR : q_r) (msigD msigC : method_sig) : Prop :=
  Forall2 (fun TD TC => qualifier_typable_context qr (sqtype TD) qcR ->
                         qualifier_typable_context qr (sqtype TC) qcR)
    (mparams msigD) (mparams msigC).

Definition sig_recv_ctx (qr qcR : q_r) (msigD msigC : method_sig) : Prop :=
  qualifier_typable_context qr (sqtype (mreceiver msigD)) qcR ->
  qualifier_typable_context qr (sqtype (mreceiver msigC)) qcR.

Lemma find_method_here_wf_method : forall CT C m mdef def,
  wf_class_table CT -> find_class CT C = Some def ->
  gget_method (methods (body def)) m = Some mdef ->
  wf_method CT C mdef.
Proof.
  intros CT C m mdef def Hwf Hf Hget.
  pose proof (find_class_wf_class _ _ _ Hwf Hf) as Hwc.
  pose proof (wf_class_table_cname _ _ _ Hwf Hf) as Hcn.
  pose proof (gget_method_In _ _ _ Hget) as Hin.
  inversion Hwc; subst; cbn in *.
  - rewrite Hno_methods in Hin. inversion Hin.
  - destruct H as [Hctor [Hmeth [Hnodup _]]].
    rewrite Forall_forall in Hmeth.
    apply Hmeth. exact Hin.
Qed.

Lemma wf_method_moc : forall CT C mdef parent_def parent qc mdefP,
  wf_method CT C mdef ->
  find_class CT C = Some parent_def ->
  super (signature parent_def) = Some parent ->
  bound CT C = Some qc ->
  FindMethodWithName CT parent (mname (msignature mdef)) mdefP ->
  method_override_compatible CT qc (msignature mdef) (msignature mdefP).
Proof.
  intros CT C mdef parent_def parent qc mdefP Hw Hf Hs Hb Hfm.
  unfold wf_method in Hw. cbn in Hw.
  destruct Hw as [_ [sG' [rt Hbody]]].
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  match goal with
  | Hf' : forall (pd : class_def) (p : class_name) (md : method_def) (q : q_c),
            _ -> _ -> _ -> _ -> method_override_compatible CT q (msignature mdef) (msignature md) |- _ =>
      exact (Hf' parent_def parent mdefP qc Hf Hs Hb Hfm)
  end.
Qed.

Lemma dispatch_sig : forall CT (C D : class_name) m,
  wf_class_table CT -> base_subtype CT C D ->
  forall mdefC mdefD qr qcR,
    FindMethodWithName CT C m mdefC ->
    FindMethodWithName CT D m mdefD ->
    (forall K qb, base_subtype CT C K -> bound CT K = Some qb ->
        (qc2q qb = Mut -> qcR = Mut_r) /\ (qc2q qb = Imm -> qcR = Imm_r)) ->
    sig_recv_ctx qr qcR (msignature mdefD) (msignature mdefC) /\
    sig_params_base CT (msignature mdefD) (msignature mdefC) /\
    sig_params_ctx qr qcR (msignature mdefD) (msignature mdefC).
Proof.
  intros CT C D m Hwf Hsub.
  induction Hsub as
    [ CT C Hdom
    | CT C D1 D H1 IH1 H2 IH2
    | CT C D HdomC HdomD Hpar ];
    intros mdefC mdefD qr qcR HfindC HfindD Hagree.
  - (* refl *)
    assert (Hmm : mdefC = mdefD) by (exact (find_method_det _ _ _ _ HfindC _ HfindD)).
    subst mdefD.
    destruct (find_method_wf_method _ _ _ _ Hwf HfindC) as [C' Hwfm].
    split.
    + intros H; exact H.
    + split.
      * apply Forall2_base_refl. intros T Hin.
        apply (wf_method_type_dom _ _ _ T Hwfm). right. exact Hin.
      * apply Forall2_impl_same.
  - (* trans *)
    destruct (find_method_exists_ancestor CT D1 D m Hwf H2 mdefD HfindD) as [mdef1 Hfind1].
    destruct (IH1 Hwf mdefC mdef1 qr qcR HfindC Hfind1 Hagree) as [Hr1 [Hb1 Hc1]].
    assert (Hagree1 : forall K qb, base_subtype CT D1 K -> bound CT K = Some qb ->
        (qc2q qb = Mut -> qcR = Mut_r) /\ (qc2q qb = Imm -> qcR = Imm_r)).
    { intros K qb Hanc Hb. exact (Hagree K qb (base_trans CT C D1 K H1 Hanc) Hb). }
    destruct (IH2 Hwf mdef1 mdefD qr qcR Hfind1 HfindD Hagree1) as [Hr2 [Hb2 Hc2]].
    split.
    + intros H. apply Hr1. apply Hr2. exact H.
    + split.
      * eapply Forall2_trans_gen; [|exact Hb2|exact Hb1].
        intros a b c Hab Hbc. exact (base_trans CT (sctype a) (sctype b) (sctype c) Hab Hbc).
      * eapply Forall2_trans_gen; [|exact Hc2|exact Hc1].
        intros a b c Hab Hbc. intros Ha. apply Hbc. apply Hab. exact Ha.
  - (* extends *)
    destruct (parent_lookup_find _ _ _ Hpar) as [defH [HfH HsH]].
    inversion HfindC; subst; clear HfindC.
    + (* FOM_Here *)
      assert (Hdefeq : def = defH) by (exact (find_class_fun CT C def defH Hfind HfH)).
      subst def.
      pose proof (find_method_here_wf_method CT C m mdefC defH Hwf Hfind Hget_method) as Hwfm.
      pose proof (gget_method_mname _ _ _ Hget_method) as Hmname.
      assert (HsD : super (signature defH) = Some D) by (rewrite HsH; reflexivity).
      assert (Hbnd : bound CT C = Some (class_qualifier (signature defH))) by (apply bound_find; exact Hfind).
      assert (HfmD : FindMethodWithName CT D (mname (msignature mdefC)) mdefD).
      { assert (Hcp := HfindD). rewrite <- Hmname in Hcp. exact Hcp. }
      pose proof (wf_method_moc CT C mdefC defH D (class_qualifier (signature defH)) mdefD
                    Hwfm Hfind HsD Hbnd HfmD) as Hmoc.
      destruct (moc_parts _ _ _ _ Hmoc) as [Hpfa Hqrcv].
      split.
      * intros HctxD.
        eapply ctx_override_step2 with (qc := qc2q (class_qualifier (signature defH)))
               (qD := sqtype (mreceiver (msignature mdefD)))
               (qC := sqtype (mreceiver (msignature mdefC))).
        -- apply qc2q_cases.
        -- intros Hq. destruct (Hagree C (class_qualifier (signature defH))
                         (base_refl CT C HdomC) Hbnd) as [Hm Hi]. exact (Hm Hq).
        -- intros Hq. destruct (Hagree C (class_qualifier (signature defH))
                         (base_refl CT C HdomC) Hbnd) as [Hm Hi]. exact (Hi Hq).
        -- exact HctxD.
        -- exact Hqrcv.
      * split.
        -- eapply Forall2_impl; [|exact Hpfa]. intros pd pc Hsubq.
           apply qualified_type_subtype_base in Hsubq. exact Hsubq.
        -- eapply Forall2_impl; [|exact Hpfa]. intros pd pc Hsubq HctxPD.
           eapply ctx_override_step2 with (qc := qc2q (class_qualifier (signature defH)))
                  (qD := sqtype pd) (qC := sqtype pc).
           ++ apply qc2q_cases.
           ++ intros Hq. destruct (Hagree C (class_qualifier (signature defH))
                            (base_refl CT C HdomC) Hbnd) as [Hm Hi]. exact (Hm Hq).
           ++ intros Hq. destruct (Hagree C (class_qualifier (signature defH))
                            (base_refl CT C HdomC) Hbnd) as [Hm Hi]. exact (Hi Hq).
           ++ exact HctxPD.
           ++ exact (qualified_type_subtype_q CT (vpa_mutability_override (class_qualifier (signature defH)) pd) pc Hsubq).
    + (* FOM_Super *)
      assert (Hdefeq : def = defH) by (exact (find_class_fun CT C def defH Hfind HfH)).
      subst def.
      assert (HparD : parent = D).
      { rewrite HsH in Hsuper. injection Hsuper as Hp. symmetry. exact Hp. }
      subst parent.
      assert (Hmm : mdefC = mdefD) by (exact (find_method_det _ _ _ _ Hparent_fmn _ HfindD)).
      subst mdefD.
      destruct (find_method_wf_method _ _ _ _ Hwf HfindD) as [C' Hwfm].
      split.
      * intros H; exact H.
      * split.
        -- apply Forall2_base_refl. intros T Hin.
           apply (wf_method_type_dom _ _ _ T Hwfm). right. exact Hin.
        -- apply Forall2_impl_same.
Qed.

Lemma wf_r_config_call_frame_dispatch :
  forall CT sΓ rΓ h y Ty zs argtypes vals ly mdef,
    wf_r_config CT sΓ rΓ h ->
    runtime_getVal rΓ y = Some (Iot ly) ->
    static_getType sΓ y = Some Ty ->
    runtime_lookup_list rΓ zs = Some vals ->
    static_getType_list sΓ zs = Some argtypes ->
    wf_senv CT (mreceiver (msignature mdef) :: mparams (msignature mdef)) ->
    (forall rqty, r_type h ly = Some rqty ->
        base_subtype CT (rctype rqty) (sctype (mreceiver (msignature mdef)))) ->
    (forall qr, r_muttype h ly = Some qr ->
        qualifier_typable_context qr (sqtype (mreceiver (msignature mdef))) qr) ->
    Forall2 (fun aT T => base_subtype CT (sctype aT) (sctype T)) argtypes (mparams (msignature mdef)) ->
    (forall i aT T, nth_error argtypes i = Some aT -> nth_error (mparams (msignature mdef)) i = Some T ->
        forall qr qcC qcR, r_muttype h ly = Some qcR ->
          qualifier_typable_context qr (sqtype aT) qcC ->
          qualifier_typable_context qcR (sqtype Ty) qcC ->
          qualifier_typable_context qr (sqtype T) qcR) ->
    wf_r_config CT (mreceiver (msignature mdef) :: mparams (msignature mdef))
      (mkr_env (Iot ly :: vals)) h.
Proof.
  intros CT sΓ rΓ h y Ty zs argtypes vals ly mdef Hwf Hvaly Hgety Hargs Hgetargs Hwfsenv
         Hrecv_base Hrecv_qual Hpar_base Hpar_qual.
  destruct (wf_r_config_ctx CT sΓ rΓ h Hwf) as [iot0 [qcC [Hgt0 Hmut0]]].
  assert (HyLen : y < length sΓ) by (unfold static_getType in Hgety; eapply nth_error_Some_lt; eauto).
  pose proof (wf_r_config_corr CT sΓ rΓ h Hwf iot0 qcC Hgt0 Hmut0 y (Iot ly) Ty HyLen Hgety Hvaly) as Hyval.
  pose proof (value_typable_iot _ _ _ _ _ Hyval) as Hyw.
  unfold wf_r_typable in Hyw.
  destruct (r_type h ly) as [rqty|] eqn:Ery; [|contradiction].
  destruct Hyw as [HbaseTy HctxTy].
  assert (Hmut_ly : r_muttype h ly = Some (rqtype rqty)).
  { unfold r_muttype. unfold r_type in Ery. destruct (runtime_getObj h ly) as [oo|] eqn:Eoo; [|discriminate].
    injection Ery as ->. reflexivity. }
  assert (HargLen : length argtypes = length (mparams (msignature mdef)))
    by (exact (Forall2_length Hpar_base)).
  assert (HzsLen : length zs = length argtypes)
    by (symmetry; exact (mapM_length _ _ (fun z => static_getType sΓ z) zs argtypes Hgetargs)).
  assert (HvalsLen : length vals = length zs)
    by (exact (mapM_length _ _ (fun z => runtime_getVal rΓ z) zs vals Hargs)).
  split; [apply (wf_r_config_ct _ _ _ _ Hwf)|].
  split; [apply (wf_r_config_heap _ _ _ _ Hwf)|].
  split.
  { unfold wf_renv. split.
    - simpl; lia.
    - split.
      + exists ly; split; [reflexivity|].
        destruct (wf_renv_valid CT rΓ h (wf_r_config_renv _ _ _ _ Hwf) y (Iot ly) Hvaly) as [Hn|Hio].
        * discriminate Hn.
        * destruct Hio as [l0 [o0 [Heq Ho]]]. injection Heq as ->. eapply runtime_getObj_Some_lt; eauto.
      + apply Forall_cons.
        * destruct (wf_renv_valid CT rΓ h (wf_r_config_renv _ _ _ _ Hwf) y (Iot ly) Hvaly) as [Hn|Hio].
          -- discriminate Hn.
          -- destruct Hio as [l0 [o0 [Heq Ho]]]. injection Heq as ->. simpl. rewrite Ho. auto.
        * rewrite Forall_forall. intros v Hv.
          destruct (mapM_In _ _ (fun z => runtime_getVal rΓ z) zs vals v Hargs Hv) as [z [Hzs Hrz]].
          pose proof (wf_renv_valid CT rΓ h (wf_r_config_renv _ _ _ _ Hwf) z v Hrz) as Hvv.
          destruct v as [|loc].
          -- simpl; auto.
          -- destruct Hvv as [Hn|Hio]; [discriminate Hn|].
             destruct Hio as [l0 [o0 [Heq Ho]]]. injection Heq as ->. simpl. rewrite Ho. auto.
  }
  split.
  { exact Hwfsenv. }
  split.
  { simpl. rewrite HvalsLen. rewrite HzsLen. rewrite HargLen. reflexivity. }
  intros ι qcontext Hgt Hmutc i Hi sqt Hnth.
  simpl in Hgt. injection Hgt as Hgt. subst ι.
  rewrite Hmut_ly in Hmutc. injection Hmutc as Hmutc. subst qcontext.
  destruct i as [|k].
  - simpl in Hnth. injection Hnth as Hnth. subst sqt.
    pose proof (Hrecv_base rqty eq_refl) as Hrb.
    pose proof (Hrecv_qual (rqtype rqty) Hmut_ly) as Hrq.
    simpl. unfold wf_r_typable. rewrite Ery. split.
    + exact Hrb.
    + exact Hrq.
  - simpl in Hnth. unfold runtime_getVal. cbn.
    assert (Hk : k < length (mparams (msignature mdef))).
    { simpl in Hi. lia. }
    assert (Hkz : k < length zs) by lia.
    assert (Hka : k < length argtypes) by lia.
    assert (Hkv : k < length vals) by lia.
    assert (HargSomeN : nth_error argtypes k <> None) by (apply nth_error_Some; lia).
    destruct (nth_error argtypes k) as [argT|] eqn:HargT; [|contradiction].
    destruct (mapM_nth_Some _ _ (fun z => static_getType sΓ z) zs argtypes Hgetargs k argT HargT) as [z [Hzs Hstat]].
    assert (HvSomeN : nth_error vals k <> None) by (apply nth_error_Some; lia).
    destruct (nth_error vals k) as [vv|] eqn:Hvv; [|contradiction].
    destruct (mapM_nth_Some _ _ (fun z => runtime_getVal rΓ z) zs vals Hargs k vv Hvv) as [z2 [Hzs2 Hrt]].
    assert (Hz2 : z2 = z) by (rewrite Hzs in Hzs2; injection Hzs2 as ->; reflexivity). subst z2.
    assert (Hzlen : z < length sΓ) by (unfold static_getType in Hstat; eapply nth_error_Some_lt; eauto).
    pose proof (wf_r_config_corr CT sΓ rΓ h Hwf iot0 qcC Hgt0 Hmut0 z vv argT Hzlen Hstat Hrt) as Haval.
    assert (HbaseArg : base_subtype CT (sctype argT) (sctype sqt)).
    { exact (Forall2_nth_error qualified_type qualified_type
               (fun aT T => base_subtype CT (sctype aT) (sctype T)) argtypes
               (mparams (msignature mdef)) Hpar_base k argT sqt HargT Hnth). }
    destruct vv as [|loc]; simpl.
    + auto.
    + pose proof (value_typable_iot _ _ _ _ _ Haval) as Hvvalw.
      unfold wf_r_typable in Hvvalw.
      destruct (r_type h loc) as [rqt|] eqn:Eloc; [|contradiction].
      destruct Hvvalw as [HbaseRuntime HctxArg].
      unfold wf_r_typable. rewrite Eloc. split.
      * exact (base_trans CT (rctype rqt) (sctype argT) (sctype sqt) HbaseRuntime HbaseArg).
      * apply (Hpar_qual k argT sqt HargT Hnth (rqtype rqt) qcC (rqtype rqty) Hmut_ly HctxArg HctxTy).
Qed.

Lemma r_basetype_eq_rtype : forall h l, r_basetype h l = option_map rctype (r_type h l).
Proof. intros. unfold r_basetype, r_type, runtime_getObj. destruct (nth_error h l); reflexivity. Qed.

Lemma r_muttype_eq_rtype : forall h loc, r_muttype h loc = option_map rqtype (r_type h loc).
Proof. intros. unfold r_muttype, r_type, runtime_getObj. destruct (nth_error h loc); reflexivity. Qed.

Lemma r_muttype_update_field : forall h ι f v loc,
  r_muttype (update_field h ι f v) loc = r_muttype h loc.
Proof.
  intros. rewrite r_muttype_eq_rtype. rewrite r_muttype_eq_rtype. rewrite r_type_update_field. reflexivity.
Qed.

Lemma r_muttype_app_singleton : forall h o loc, loc < length h ->
  r_muttype (h++[o]) loc = r_muttype h loc.
Proof.
  intros. rewrite r_muttype_eq_rtype. rewrite r_muttype_eq_rtype.
  assert (E : r_type (h++[o]) loc = r_type h loc) by (apply r_type_app_singleton; lia).
  rewrite E. reflexivity.
Qed.

Lemma fldwrite_core :
  forall CT sΓ rΓ h x f y loc_x o vf val_y Tx Ty fieldT (fldq : q -> q_f -> q),
    wf_r_config CT sΓ rΓ h ->
    runtime_getVal rΓ x = Some (Iot loc_x) ->
    runtime_getObj h loc_x = Some o ->
    getVal (fields_map o) f = Some vf ->
    runtime_getVal rΓ y = Some val_y ->
    static_getType sΓ x = Some Tx ->
    static_getType sΓ y = Some Ty ->
    sf_def_rel CT (sctype Tx) f fieldT ->
    qualified_type_subtype CT Ty
      (Build_qualified_type (fldq (sqtype Tx) (mutability (ftype fieldT))) (f_base_type (ftype fieldT))) ->
    (forall qr qobj qc qv qR m,
       qualifier_typable_context qobj qR qc ->
       qualifier_typable_context qr qv qc ->
       q_subtype qv (fldq qR m) ->
       qualifier_typable_heap qr (vpa_mutability_rec_fld qobj m)) ->
    wf_r_config CT sΓ rΓ (update_field h loc_x f val_y) /\
    length h <= length (update_field h loc_x f val_y) /\
    (forall loc, loc < length h -> r_type (update_field h loc_x f val_y) loc = r_type h loc).
Proof.
  intros CT sΓ rΓ h x f y loc_x o vf val_y Tx Ty fieldT fldq Hwf Hvalx Hobj Hfield Hvaly
         Hgetx Hgety Hfld Hsub Hfldw.
  destruct (wf_r_config_ctx CT sΓ rΓ h Hwf) as [iot0 [qcC [Hgt0 Hmut0]]].
  assert (Hlocx : loc_x < length h) by (eapply runtime_getObj_Some_lt; eauto).
  assert (Hxlen : x < length sΓ) by (unfold static_getType in Hgetx; eapply nth_error_Some_lt; eauto).
  pose proof (wf_r_config_corr CT sΓ rΓ h Hwf iot0 qcC Hgt0 Hmut0 x (Iot loc_x) Tx Hxlen Hgetx Hvalx) as Hxval.
  assert (Er : r_type h loc_x = Some (rt_type o)) by (unfold r_type; rewrite Hobj; reflexivity).
  pose proof (value_typable_iot _ _ _ _ _ Hxval) as Hxw.
  unfold wf_r_typable in Hxw. rewrite Er in Hxw. simpl in Hxw.
  destruct Hxw as [HbaseTx HctxTx].
  assert (Hwfobj : wf_obj CT h loc_x) by (apply (wf_r_config_heap _ _ _ _ Hwf); exact Hlocx).
  destruct (wf_obj_iff CT h loc_x o Hobj) as [Hiff _].
  destruct (Hiff Hwfobj) as [Hrtuse [fds [Hcf [Hlen Hfa]]]].
  assert (Hgget : gget fds f = Some fieldT).
  { exact (FieldLookup_prefix CT (rctype (rt_type o)) (sctype Tx) f fieldT
             (wf_r_config_ct _ _ _ _ Hwf) HbaseTx Hfld fds Hcf). }
  assert (HfLen : f < length (fields_map o)) by (unfold getVal in Hfield; eapply nth_error_Some_lt; eauto).
  assert (HfLen' : f < length fds) by lia.
  assert (HfdSome : nth_error fds f <> None) by (apply nth_error_Some; lia).
  destruct (nth_error fds f) as [fdx|] eqn:Efd; [|contradiction].
  unfold gget in Hgget. rewrite Efd in Hgget. injection Hgget as Hfx. subst fdx.
  assert (Hvalok : field_value_ok CT (update_field h loc_x f val_y) (rqtype (rt_type o)) val_y fieldT).
  { destruct val_y as [|loc_y]; simpl; auto.
    assert (Hylen : y < length sΓ) by (unfold static_getType in Hgety; eapply nth_error_Some_lt; eauto).
    pose proof (wf_r_config_corr CT sΓ rΓ h Hwf iot0 qcC Hgt0 Hmut0 y (Iot loc_y) Ty Hylen Hgety Hvaly) as Hyval.
    pose proof (value_typable_iot _ _ _ _ _ Hyval) as Hyw.
    unfold wf_r_typable in Hyw.
    destruct (r_type h loc_y) as [rqty|] eqn:Ery; [|contradiction].
    destruct Hyw as [HbaseTy HctxTy].
    unfold field_value_ok.
    destruct (runtime_getObj (update_field h loc_x f (Iot loc_y)) loc_y) as [o2|] eqn:Eo2.
    - exists rqty. split.
      + rewrite r_type_update_field. exact Ery.
      + split.
        * exact (base_trans CT (rctype rqty) (sctype Ty) (f_base_type (ftype fieldT)) HbaseTy
                   (qualified_type_subtype_base CT Ty
                      (Build_qualified_type (fldq (sqtype Tx) (mutability (ftype fieldT)))
                         (f_base_type (ftype fieldT))) Hsub)).
        * apply (Hfldw (rqtype rqty) (rqtype (rt_type o)) qcC (sqtype Ty) (sqtype Tx) (mutability (ftype fieldT))).
          -- exact HctxTx.
          -- exact HctxTy.
          -- exact (qualified_type_subtype_q CT Ty
                      (Build_qualified_type (fldq (sqtype Tx) (mutability (ftype fieldT)))
                         (f_base_type (ftype fieldT))) Hsub).
    - exfalso.
      destruct (r_type_Some_getObj _ _ _ Ery) as [o0 Ho0].
      assert (Hne : runtime_getObj h loc_y <> None) by (rewrite Ho0; discriminate).
      exact (runtime_getObj_update_field_Some h loc_x f (Iot loc_y) loc_y Hne Eo2). }
  set (o' := set_fields_map o (update f val_y (fields_map o))).
  assert (Ho' : runtime_getObj (update_field h loc_x f val_y) loc_x = Some o').
  { unfold update_field. rewrite Hobj. unfold runtime_getObj, o'. apply nth_error_update_same. exact Hlocx. }
  assert (Hheap' : wf_heap CT (update_field h loc_x f val_y)).
  { intros loc Hlocs. unfold wf_heap in *. destruct (Nat.eq_dec loc loc_x) as [Heql|Hne].
    - subst loc. unfold wf_obj. rewrite Ho'. simpl.
      split.
      + exact Hrtuse.
      + exists fds. split; [exact Hcf|]. split.
        * rewrite length_update. exact Hlen.
        * apply (Forall2_update_general value field_def
                   (field_value_ok CT h (rqtype (rt_type o)))
                   (field_value_ok CT (update_field h loc_x f val_y) (rqtype (rt_type o)))
                   (fields_map o) fds f val_y).
          -- exact Hfa.
          -- intros aa bb Ha. eapply field_value_ok_rtype_eq; [|exact Ha].
             intros ll. apply r_type_update_field.
          -- intros bb Hb. rewrite Efd in Hb. injection Hb as ->. exact Hvalok.
    - apply (wf_obj_update_field_other CT h loc_x f val_y loc).
      + apply (wf_r_config_heap _ _ _ _ Hwf). 
        rewrite length_update_field in Hlocs. exact Hlocs.
      + exact Hne.
  }
  split.
  - split; [apply (wf_r_config_ct _ _ _ _ Hwf)|].
    split; [exact Hheap'|].
    split.
    + unfold wf_renv. split.
      * apply (wf_renv_dom _ _ _ (wf_r_config_renv _ _ _ _ Hwf)).
      * split.
        -- destruct (wf_renv_this _ _ _ (wf_r_config_renv _ _ _ _ Hwf)) as [iot [Hg Hlt]].
           exists iot. split; [exact Hg|]. rewrite length_update_field. exact Hlt.
        -- rewrite Forall_forall. intros v Hv.
           apply (value_wf_mono h (update_field h loc_x f val_y) v).
           ++ intros loc Hne. exact (runtime_getObj_update_field_Some h loc_x f val_y loc Hne).
           ++ exact (proj1 (Forall_forall _ _) (wf_renv_Forall _ _ _ (wf_r_config_renv _ _ _ _ Hwf)) v Hv).
    + split.
      * apply (wf_r_config_senv _ _ _ _ Hwf).
      * split.
        -- exact (wf_r_config_len _ _ _ _ Hwf).
        -- intros ι qcontext Hgt Hmut i Hi sqt Hnth.
           assert (Hmut_h : r_muttype h ι = Some qcontext).
           { rewrite <- (r_muttype_update_field h loc_x f val_y ι). exact Hmut. }
           destruct (runtime_getVal rΓ i) as [v|] eqn:Hv.
           ++ pose proof (wf_r_config_corr CT sΓ rΓ h Hwf iot0 qcC Hgt0 Hmut0 i v sqt Hi Hnth Hv) as Hc.
              destruct v as [|loc]; simpl in *.
              ** exact I.
              ** assert (Hq : qcontext = qcC).
                 { rewrite Hgt0 in Hgt. injection Hgt as Hι. subst ι.
                   rewrite Hmut0 in Hmut_h. injection Hmut_h as Hq'. subst qcontext. reflexivity. }
                 subst qcontext.
                 exact (wf_r_typable_rtype_eq_cond CT h (update_field h loc_x f val_y) loc sqt qcC
                          (fun Hne => r_type_update_field h loc_x f val_y loc) Hc).
           ++ pose proof (wf_r_config_corr_raw CT sΓ rΓ h Hwf ι qcontext Hgt Hmut_h i Hi sqt Hnth) as Hc.
              rewrite Hv in Hc. exact Hc.
  - split.
    + rewrite length_update_field. lia.
    + intros loc Hloc. apply r_type_update_field.
Qed.

Lemma new_core :
  forall CT sΓ rΓ h x q_c c ys l1 qthisr vals Tx argtypes consig,
    wf_r_config CT sΓ rΓ h ->
    runtime_getVal rΓ 0 = Some (Iot l1) ->
    runtime_lookup_list rΓ ys = Some vals ->
    r_muttype h l1 = Some qthisr ->
    static_getType sΓ x = Some Tx ->
    static_getType_list sΓ ys = Some argtypes ->
    constructor_sig_lookup CT c = Some consig ->
    x <> 0 ->
    vpa_mutability_bound (qc2q q_c) (cqualifier consig) = qc2q q_c ->
    Forall2 (fun arg T => qualified_type_subtype CT arg T) argtypes
      (map (vpa_mutability_constructor_param q_c) (cparams consig)) ->
    qualified_type_subtype CT (Build_qualified_type (qc2q q_c) c) Tx ->
    wf_r_config CT sΓ (set_vars rΓ (update x (Iot (dom h)) (vars rΓ)))
      (h ++ [mkObj (mkruntime_type (vpa_mutability_object_creation qthisr q_c) c) vals]) /\
    length h <= length (h ++ [mkObj (mkruntime_type (vpa_mutability_object_creation qthisr q_c) c) vals]) /\
    (forall loc, loc < length h ->
       r_type (h ++ [mkObj (mkruntime_type (vpa_mutability_object_creation qthisr q_c) c) vals]) loc = r_type h loc).
Proof.
  intros CT sΓ rΓ h x q_c c ys l1 qthisr vals Tx argtypes consig
         Hwf Hthis Hargs Hmut Hgetx Hgetargs Hconsig Hnotrcv Hqc Hargsub Hresultsub.
  set (o := mkObj (mkruntime_type (vpa_mutability_object_creation qthisr q_c) c) vals).
  destruct (wf_r_config_ctx CT sΓ rΓ h Hwf) as [iot0 [qcC [Hgt0 Hmut0]]].
  assert (Hl1gt : get_this_var_mapping (vars rΓ) = Some l1) by (apply get_this_from_head; exact Hthis).
  destruct (wf_renv_this _ _ _ (wf_r_config_renv _ _ _ _ Hwf)) as [it [Hgtit Hltit]].
  assert (Hl1lt : l1 < dom h) by (rewrite Hl1gt in Hgtit; injection Hgtit as ->; exact Hltit).
  assert (Hthisr : qthisr = qcC).
  { assert (Hl1iot : l1 = iot0) by (rewrite Hgt0 in Hl1gt; injection Hl1gt as ->; reflexivity).
    rewrite Hl1iot in Hmut. rewrite Hmut0 in Hmut. injection Hmut as ->. reflexivity. }
  subst qthisr.
  assert (Hlen_v_fs : length vals = length (cparams consig)).
  { assert (H1 : length vals = length ys) by (exact (mapM_length _ _ (fun z => runtime_getVal rΓ z) ys vals Hargs)).
    assert (H2 : length argtypes = length ys) by (exact (mapM_length _ _ (fun z => static_getType sΓ z) ys argtypes Hgetargs)).
    assert (H3 : length argtypes = length (map (vpa_mutability_constructor_param q_c) (cparams consig)))
      by (exact (Forall2_length Hargsub)).
    rewrite length_map in H3. lia. }
  assert (HargLen2 : length argtypes = length (cparams consig)).
  { assert (H3 : length argtypes = length (map (vpa_mutability_constructor_param q_c) (cparams consig)))
      by (exact (Forall2_length Hargsub)).
    rewrite length_map in H3. exact H3. }
  destruct (constructor_sig_lookup_find CT c consig Hconsig) as [def [Hfind Hceq]].
  pose proof (find_class_wf_class _ _ _ (wf_r_config_ct _ _ _ _ Hwf) Hfind) as Hwc.
  pose proof (wf_class_table_cname _ _ _ (wf_r_config_ct _ _ _ _ Hwf) Hfind) as Hcn.
  destruct (wf_class_constructor_props CT c def Hwc Hfind Hcn) as [Hbound [Hforallcp [fs [Hcf [Hcplen Hctorfa]]]]].
  rewrite <- Hceq in Hbound. rewrite <- Hceq in Hforallcp. rewrite <- Hceq in Hcplen. rewrite <- Hceq in Hctorfa.
  assert (Hcdom : c < dom CT) by (eapply find_class_dom; eauto).
  assert (Hobjwf : wf_obj CT (h++[o]) (length h)).
  { unfold wf_obj. rewrite (runtime_getObj_app_singleton_last h o). simpl.
    split.
    - unfold wf_rtypeuse. rewrite Hbound. split; [exact Hcdom|].
      apply ctor_agree. exact Hqc.
    - exists fs. split; [exact Hcf|]. split.
      + change (length vals = length fs). lia.
      + apply (Forall2_from_nth value field_def
                 (field_value_ok CT (h++[o]) (vpa_mutability_object_creation qcC q_c)) vals fs).
        * change (length vals = length fs). lia.
        * intros k a b Hk Ha Hb.
          assert (Hkcp : k < length (cparams consig)) by lia.
          assert (Hkarg : k < length argtypes) by lia.
          assert (HargSomeN : nth_error argtypes k <> None) by (apply nth_error_Some; lia).
          destruct (nth_error argtypes k) as [argT|] eqn:HargT; [|contradiction].
          assert (HcpSomeN : nth_error (cparams consig) k <> None) by (apply nth_error_Some; lia).
          destruct (nth_error (cparams consig) k) as [param|] eqn:Hcp; [|contradiction].
          assert (Hmapnth : nth_error (map (vpa_mutability_constructor_param q_c) (cparams consig)) k
                            = Some (vpa_mutability_constructor_param q_c param)).
          { rewrite nth_error_map. rewrite Hcp. reflexivity. }
          assert (HargTsub : qualified_type_subtype CT argT (vpa_mutability_constructor_param q_c param)).
          { exact (Forall2_nth_error qualified_type qualified_type
                     (fun arg T => qualified_type_subtype CT arg T) argtypes
                     (map (vpa_mutability_constructor_param q_c) (cparams consig)) Hargsub k argT
                     (vpa_mutability_constructor_param q_c param) HargT Hmapnth). }
          assert (HctorSub : qualified_type_subtype CT (vpa_mutability_constructor_param (cqualifier consig) param)
                     (Build_qualified_type (vpa_mutability_constructor_fld (cqualifier consig) (mutability (ftype b)))
                        (f_base_type (ftype b)))).
          { exact (Forall2_nth_error qualified_type field_def
                     (fun param fdef => qualified_type_subtype CT (vpa_mutability_constructor_param (cqualifier consig) param)
                        (Build_qualified_type (vpa_mutability_constructor_fld (cqualifier consig) (mutability (ftype fdef)))
                           (f_base_type (ftype fdef)))) (cparams consig) fs Hctorfa k param b Hcp Hb). }
          destruct (mapM_nth_Some _ _ (fun z => static_getType sΓ z) ys argtypes Hgetargs k argT HargT) as [z1 [Hz1 Hstat]].
          destruct (mapM_nth_Some _ _ (fun z => runtime_getVal rΓ z) ys vals Hargs k a Ha) as [z2 [Hz2 Hrt]].
          assert (Hz12 : z1 = z2) by (rewrite Hz1 in Hz2; injection Hz2 as ->; reflexivity). subst z1.
          assert (Hzlen : z2 < length sΓ) by (unfold static_getType in Hstat; eapply nth_error_Some_lt; eauto).
          pose proof (wf_r_config_corr CT sΓ rΓ h Hwf iot0 qcC Hgt0 Hmut0 z2 a argT Hzlen Hstat Hrt) as Haval.
          destruct a as [|loc]; simpl; auto.
          pose proof (value_typable_iot _ _ _ _ _ Haval) as Haw.
          unfold wf_r_typable in Haw.
          destruct (r_type h loc) as [rqt|] eqn:Eloc; [|contradiction].
          destruct Haw as [HbaseA HctxA].
          unfold field_value_ok.
          destruct (runtime_getObj (h++[o]) loc) as [o2|] eqn:Eo2.
          -- exists rqt. split.
             ++ assert (Ell : loc < length h) by (apply r_type_neq_lt; rewrite Eloc; discriminate).
                assert (Eapp : r_type (h++[o]) loc = r_type h loc) by (apply r_type_app_singleton; exact Ell).
                rewrite Eapp. exact Eloc.
             ++ split.
                ** exact (base_trans CT (rctype rqt) (sctype argT) (f_base_type (ftype b)) HbaseA
                           (base_trans CT (sctype argT) (sctype param) (f_base_type (ftype b))
                              (qualified_type_subtype_base CT argT (vpa_mutability_constructor_param q_c param) HargTsub)
                              (qualified_type_subtype_base CT (vpa_mutability_constructor_param (cqualifier consig) param)
                                 (Build_qualified_type (vpa_mutability_constructor_fld (cqualifier consig) (mutability (ftype b)))
                                    (f_base_type (ftype b))) HctorSub))).
                ** apply (ctor_fit q_c (cqualifier consig) qcC param argT (rqtype rqt) (mutability (ftype b))).
                   --- exact (qualified_type_subtype_q CT argT (vpa_mutability_constructor_param q_c param) HargTsub).
                   --- exact (qualified_type_subtype_q CT (vpa_mutability_constructor_param (cqualifier consig) param)
                              (Build_qualified_type (vpa_mutability_constructor_fld (cqualifier consig) (mutability (ftype b)))
                                 (f_base_type (ftype b))) HctorSub).
                   --- exact Hqc.
                   --- exact HctxA.
          -- exfalso. destruct (r_type_Some_getObj _ _ _ Eloc) as [o3 Ho3].
             assert (Hne : runtime_getObj h loc <> None) by (rewrite Ho3; discriminate).
             exact (runtime_getObj_app_singleton_Some h o loc Hne Eo2). }
  split.
  { split.
    { apply (wf_r_config_ct _ _ _ _ Hwf). }
    split.
    { intros loc Hlocs.
      destruct (Nat.eq_dec loc (length h)) as [Heql|Hne].
      - subst loc. exact Hobjwf.
      - apply (wf_obj_app_singleton CT h o loc).
        + rewrite app_length in Hlocs. simpl in Hlocs. lia.
        + assert (Hlt : loc < length h) by (rewrite app_length in Hlocs; simpl in Hlocs; lia).
          apply (wf_r_config_heap _ _ _ _ Hwf). exact Hlt.
    }
    split.
    { unfold wf_renv. simpl. split.
      - rewrite length_update. apply (wf_renv_dom _ _ _ (wf_r_config_renv _ _ _ _ Hwf)).
      - split.
        + destruct (wf_renv_this _ _ _ (wf_r_config_renv _ _ _ _ Hwf)) as [it2 [Hg Hlt]].
          exists it2. split.
          * assert (Heqg : get_this_var_mapping (update x (Iot (dom h)) (vars rΓ)) = get_this_var_mapping (vars rΓ))
              by (apply get_this_update_neq; exact Hnotrcv).
            rewrite Heqg. exact Hg.
          * rewrite app_length. simpl. lia.
        + apply (Forall_update_general value (value_wf_h (h++[o])) (vars rΓ) x (Iot (dom h))).
          * rewrite Forall_forall. intros v Hv.
            apply (value_wf_mono h (h++[o]) v).
            -- intros l Hne. exact (runtime_getObj_app_singleton_Some h o l Hne).
            -- exact (proj1 (Forall_forall _ _) (wf_renv_Forall _ _ _ (wf_r_config_renv _ _ _ _ Hwf)) v Hv).
          * simpl. rewrite runtime_getObj_app_singleton_last. auto.
    }
    split.
    { apply (wf_r_config_senv _ _ _ _ Hwf). }
    split.
    { rewrite length_update. exact (wf_r_config_len _ _ _ _ Hwf). }
    { intros ι qcontext Hgt Hmutc i Hi sqt Hnth.
      assert (Hgt2 : get_this_var_mapping (update x (Iot (dom h)) (vars rΓ)) = Some ι).
      { simpl in Hgt. exact Hgt. }
      assert (Hgtc : get_this_var_mapping (vars rΓ) = Some ι).
      { rewrite (get_this_update_neq (vars rΓ) x (Iot (dom h)) Hnotrcv) in Hgt2. exact Hgt2. }
      assert (Hι : ι = l1) by (rewrite Hl1gt in Hgtc; injection Hgtc as ->; reflexivity).
      subst ι.
      assert (HqcC : qcontext = qcC).
      { assert (Eapp : r_muttype (h++[o]) l1 = r_muttype h l1) by (apply r_muttype_app_singleton; exact Hl1lt).
        rewrite Eapp in Hmutc. rewrite Hmut in Hmutc. injection Hmutc as Htmp. symmetry. exact Htmp. }
      destruct (Nat.eq_dec i x) as [Heqix|Hneqix].
      { subst i.
        assert (Hsq : sqt = Tx).
        { unfold static_getType in Hgetx. rewrite Hgetx in Hnth. injection Hnth as Htmp. symmetry. exact Htmp. }
        subst sqt.
        assert (Hxlen : x < length (vars rΓ)).
        { unfold static_getType in Hgetx. pose proof (wf_r_config_len CT sΓ rΓ h Hwf). lia. }
        assert (Hrv : runtime_getVal (set_vars rΓ (update x (Iot (dom h)) (vars rΓ))) x = Some (Iot (dom h))).
        { unfold runtime_getVal. simpl. apply nth_error_update_same. exact Hxlen. }
        rewrite Hrv. simpl. subst qcontext.
        unfold wf_r_typable.
        assert (Ert : r_type (h++[o]) (length h) = Some (mkruntime_type (vpa_mutability_object_creation qcC q_c) c)).
        { unfold r_type. rewrite runtime_getObj_app_singleton_last. simpl. unfold o. reflexivity. }
        rewrite Ert. split.
        - exact (qualified_type_subtype_base CT (Build_qualified_type (qc2q q_c) c) Tx Hresultsub).
        - exact (new_result_ctx q_c qcC Tx (qualified_type_subtype_q CT (Build_qualified_type (qc2q q_c) c) Tx Hresultsub)).
      }
      { assert (Hrv : runtime_getVal (set_vars rΓ (update x (Iot (dom h)) (vars rΓ))) i = runtime_getVal rΓ i).
        { unfold runtime_getVal. simpl. apply nth_error_update_diff. congruence. }
        rewrite Hrv.
        destruct (runtime_getVal rΓ i) as [v|] eqn:Hv.
        - pose proof (wf_r_config_corr CT sΓ rΓ h Hwf iot0 qcC Hgt0 Hmut0 i v sqt Hi Hnth Hv) as Hc.
          destruct v as [|loc]; simpl in *.
          + exact I.
          + subst qcontext.
            exact (wf_r_typable_rtype_eq_cond CT h (h++[o]) loc sqt qcC
                     (fun Hne => r_type_app_singleton h o loc (r_type_neq_lt h loc Hne)) Hc).
        - pose proof (wf_r_config_corr_raw CT sΓ rΓ h Hwf iot0 qcC Hgt0 Hmut0 i Hi sqt Hnth) as Hc.
          rewrite Hv in Hc. exact Hc. }
    }
  }
  { split.
    { rewrite app_length. simpl. lia. }
    { intros loc Hloc. apply r_type_app_singleton. exact Hloc. } }
Qed.

Lemma wf_class_bound_super : forall CT C def D qC qD,
  wf_class CT def ->
  find_class CT C = Some def ->
  cname (signature def) = C ->
  super (signature def) = Some D ->
  bound CT C = Some qC ->
  bound CT D = Some qD ->
  qC = qD \/ qD = RDM_c.
Proof.
  intros CT C def D qC qD Hwc Hf Hcn Hsup HbC HbD.
  inversion Hwc; subst.
  - rewrite Hno_super in Hsup. discriminate.
  - cbn in H. destruct H as [_ [_ [_ Hmatch]]].
    match goal with
    | Hs : super (signature ?d) = Some ?S |- _ =>
        assert (Hsc : S = D) by (rewrite Hsup in Hs; injection Hs as Hh; symmetry; exact Hh);
        subst S
    end.
    rewrite HbD in Hmatch.
    destruct Hmatch as [fs [Hcf [Hq _]]].
    rewrite (bound_find _ _ _ Hf) in HbC. injection HbC as HbC'.
    destruct Hq as [Hq|Hq].
    + left. rewrite <- HbC'. exact Hq.
    + right. exact Hq.
Qed.

Lemma bound_propagates : forall CT A B,
  wf_class_table CT -> base_subtype CT A B ->
  forall qbc, bound CT B = Some qbc -> qbc <> RDM_c -> bound CT A = Some qbc.
Proof.
  intros CT A B Hwf Hsub. induction Hsub as
    [ CT A Hdom
    | CT A D E H1 IH1 H2 IH2
    | CT A D HdomA HdomD Hpar ]; intros qbc Hb Hne.
  - exact Hb.
  - apply (IH1 Hwf qbc). apply (IH2 Hwf qbc); assumption. assumption.
  - destruct (parent_lookup_find _ _ _ Hpar) as [def [Hf Hsup]].
    pose proof (find_class_wf_class _ _ _ Hwf Hf) as Hwc.
    pose proof (wf_class_table_cname _ _ _ Hwf Hf) as Hcn.
    pose proof (bound_find _ _ _ Hf) as HbA.
    destruct (wf_class_bound_super _ _ _ _ _ _ Hwc Hf Hcn Hsup HbA Hb) as [Hq|Hq].
    + rewrite Hq in HbA. exact HbA.
    + exfalso. apply Hne. exact Hq.
Qed.

Lemma wf_rtypeuse_some : forall CT q c qb, bound CT c = Some qb -> wf_rtypeuse CT q c ->
  c < dom CT /\ vpa_mutability_runtime_bound_agree q qb = true.
Proof. intros. unfold wf_rtypeuse in H0. rewrite H in H0. exact H0. Qed.
Lemma wf_rtypeuse_none : forall CT q c, bound CT c = None -> wf_rtypeuse CT q c -> False.
Proof. intros. unfold wf_rtypeuse in H0. rewrite H in H0. exact H0. Qed.

Lemma call_frame_facts :
  forall CT sΓ rΓ h y Ty m zs argtypes vals ly cy mdef mdef0 (g : q -> q -> q),
    (forall qr qcC qsTy qsR, q_subtype qsTy (g qsTy qsR) ->
       qualifier_typable_context qr qsTy qcC -> qualifier_typable_context qr qsR qr) ->
    (forall qr qcR qcC qsArg qsTy qsParam, q_subtype qsArg (g qsTy qsParam) ->
       qualifier_typable_context qr qsArg qcC ->
       qualifier_typable_context qcR qsTy qcC -> qualifier_typable_context qr qsParam qcR) ->
    wf_r_config CT sΓ rΓ h ->
    runtime_getVal rΓ y = Some (Iot ly) ->
    static_getType sΓ y = Some Ty ->
    runtime_lookup_list rΓ zs = Some vals ->
    static_getType_list sΓ zs = Some argtypes ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy m mdef ->
    FindMethodWithName CT (sctype Ty) m mdef0 ->
    wf_senv CT (mreceiver (msignature mdef) :: mparams (msignature mdef)) ->
    (qualified_type_subtype CT Ty
       (Build_qualified_type (g (sqtype Ty) (sqtype (mreceiver (msignature mdef0))))
          (sctype (mreceiver (msignature mdef0))))
     \/ (sqtype Ty = RO /\ sqtype (mreceiver (msignature mdef0)) = RDM /\
         base_subtype CT (sctype Ty) (sctype (mreceiver (msignature mdef0))))) ->
    Forall2 (fun arg T => qualified_type_subtype CT arg (Build_qualified_type (g (sqtype Ty) (sqtype T)) (sctype T)))
      argtypes (mparams (msignature mdef0)) ->
    wf_r_config CT (mreceiver (msignature mdef) :: mparams (msignature mdef))
      (mkr_env (Iot ly :: vals)) h.
Proof.
  intros CT sΓ rΓ h y Ty m zs argtypes vals ly cy mdef mdef0 g Hrcvtr Hargtr Hwf Hvaly Hgety Hargs Hgetargs
         Hbase HfindC HfindD Hwfsenv Hrcv_sub Harg_sub.
  pose proof (wf_r_config_ct _ _ _ _ Hwf) as Hct.
  destruct (wf_r_config_ctx CT sΓ rΓ h Hwf) as [iot0 [qcC [Hgt0 Hmut0]]].
  assert (HyLen : y < length sΓ) by (unfold static_getType in Hgety; eapply nth_error_Some_lt; eauto).
  pose proof (wf_r_config_corr CT sΓ rΓ h Hwf iot0 qcC Hgt0 Hmut0 y (Iot ly) Ty HyLen Hgety Hvaly) as Hyval.
  pose proof (value_typable_iot _ _ _ _ _ Hyval) as Hyw.
  unfold wf_r_typable in Hyw.
  destruct (r_type h ly) as [rqty|] eqn:Ery; [|contradiction].
  destruct Hyw as [HbaseTy HctxTy].
  assert (Hrcy : rctype rqty = cy).
  { assert (Eb : r_basetype h ly = Some (rctype rqty)).
    { rewrite r_basetype_eq_rtype. rewrite Ery. reflexivity. }
    rewrite Eb in Hbase. injection Hbase as Hrc. exact Hrc. }
  assert (Hanc : base_subtype CT cy (sctype Ty)).
  { rewrite <- Hrcy. exact HbaseTy. }
  assert (Hrm : r_muttype h ly = Some (rqtype rqty)).
  { unfold r_muttype. unfold r_type in Ery. destruct (runtime_getObj h ly) as [oo|] eqn:Eoo; [|discriminate].
    injection Ery as ->. reflexivity. }
  assert (Hrecv_base : forall rqty0, r_type h ly = Some rqty0 ->
      base_subtype CT (rctype rqty0) (sctype (mreceiver (msignature mdef)))).
  { intros rqty0 Er0. assert (Hq : rqty0 = rqty) by (rewrite Ery in Er0; injection Er0 as ->; reflexivity).
    subst rqty0. rewrite Hrcy. exact (find_method_base CT cy m mdef Hct HfindC). }
  (* runtime use of the receiver object *)
  assert (Hruse : wf_rtypeuse CT (rqtype rqty) (rctype rqty)).
  { destruct (wf_renv_valid CT rΓ h (wf_r_config_renv _ _ _ _ Hwf) y (Iot ly) Hvaly) as [Hn|Hio].
    - discriminate Hn.
    - destruct Hio as [l0 [o0 [Heq Ho]]]. injection Heq as Hlyeq. rewrite <- Hlyeq in Ho.
      assert (Hly_lt : ly < dom h) by (eapply runtime_getObj_Some_lt; eauto).
      assert (Hwo : wf_obj CT h ly) by (apply (wf_r_config_heap _ _ _ _ Hwf); exact Hly_lt).
      destruct (wf_obj_iff CT h ly o0 Ho) as [Hiff _].
      destruct (Hiff Hwo) as [Hru _].
      assert (Hrt : r_type h ly = Some (rt_type o0)) by (unfold r_type; rewrite Ho; reflexivity).
      rewrite Ery in Hrt. injection Hrt as Heq2. rewrite <- Heq2 in Hru. exact Hru. }
  rewrite Hrcy in Hruse.
  assert (Hbex : exists qbcy, bound CT cy = Some qbcy).
  { destruct (bound CT cy) as [qbcy|] eqn:Eb.
    - exists qbcy. reflexivity.
    - exfalso. exact (wf_rtypeuse_none _ _ _ Eb Hruse). }
  destruct Hbex as [qbcy Ebcy].
  assert (Hdomcy : cy < dom CT) by (exact (proj1 (wf_rtypeuse_some _ _ _ _ Ebcy Hruse))).
  assert (Hagcy : vpa_mutability_runtime_bound_agree (rqtype rqty) qbcy = true)
    by (exact (proj2 (wf_rtypeuse_some _ _ _ _ Ebcy Hruse))).
  assert (Hagr_gen : forall qcR, r_muttype h ly = Some qcR ->
      forall qb0, bound CT cy = Some qb0 -> vpa_mutability_runtime_bound_agree qcR qb0 = true).
  { intros qcR Hq qb0 Hb0. rewrite Hrm in Hq. injection Hq as Hqeq.
    rewrite Ebcy in Hb0. injection Hb0 as Hbeq.
    rewrite <- Hqeq. rewrite <- Hbeq. exact Hagcy. }
  assert (Hagree_from : forall (qcR : q_r),
      (forall qb0, bound CT cy = Some qb0 -> vpa_mutability_runtime_bound_agree qcR qb0 = true) ->
      forall K qb, base_subtype CT cy K -> bound CT K = Some qb ->
        (qc2q qb = Mut -> qcR = Mut_r) /\ (qc2q qb = Imm -> qcR = Imm_r)).
  { intros qcR Hagr K qb HancK Hbq. split.
    - intros Hq. assert (Hqb : qb = Mut_c) by (destruct qb; cbn in Hq; try discriminate; reflexivity).
      subst qb. assert (Hne : Mut_c <> RDM_c) by discriminate.
      assert (Hcy : bound CT cy = Some Mut_c) by (exact (bound_propagates CT cy K Hct HancK Mut_c Hbq Hne)).
      rewrite Hcy in Ebcy. injection Ebcy as Hqq. subst qbcy.
      exact (agree_mut qcR Mut_c (Hagr Mut_c Hcy) eq_refl).
    - intros Hq. assert (Hqb : qb = Imm_c) by (destruct qb; cbn in Hq; try discriminate; reflexivity).
      subst qb. assert (Hne : Imm_c <> RDM_c) by discriminate.
      assert (Hcy : bound CT cy = Some Imm_c) by (exact (bound_propagates CT cy K Hct HancK Imm_c Hbq Hne)).
      rewrite Hcy in Ebcy. injection Ebcy as Hqq. subst qbcy.
      exact (agree_imm qcR Imm_c (Hagr Imm_c Hcy) eq_refl). }
  assert (Hrecv_qual : forall qr, r_muttype h ly = Some qr ->
      qualifier_typable_context qr (sqtype (mreceiver (msignature mdef))) qr).
  { intros qr Hqr.
    assert (Hqreq : qr = rqtype rqty) by (rewrite Hrm in Hqr; injection Hqr as ->; reflexivity).
    subst qr.
    assert (Hmid : qualifier_typable_context (rqtype rqty) (sqtype (mreceiver (msignature mdef0))) (rqtype rqty)).
    { destruct Hrcv_sub as [Hs|Hs].
      - exact (Hrcvtr (rqtype rqty) qcC (sqtype Ty) (sqtype (mreceiver (msignature mdef0)))
                 (qualified_type_subtype_q CT Ty
                    (Build_qualified_type (g (sqtype Ty) (sqtype (mreceiver (msignature mdef0))))
                       (sctype (mreceiver (msignature mdef0)))) Hs) HctxTy).
      - destruct Hs as [Hro [Hrdm _]]. rewrite Hrdm. apply ctx_rdm_self. }
    destruct (dispatch_sig CT cy (sctype Ty) m Hct Hanc mdef mdef0 (rqtype rqty) (rqtype rqty)
               HfindC HfindD (Hagree_from (rqtype rqty) (Hagr_gen (rqtype rqty) Hrm))) as [Hr _].
    exact (Hr Hmid). }
  assert (Hpar_base : Forall2 (fun aT T => base_subtype CT (sctype aT) (sctype T)) argtypes (mparams (msignature mdef))).
  { assert (Hab : Forall2 (fun aT T => base_subtype CT (sctype aT) (sctype T)) argtypes (mparams (msignature mdef0))).
    { eapply Forall2_impl; [|exact Harg_sub]. intros aa bb Hsubq.
      exact (qualified_type_subtype_base CT aa (Build_qualified_type (g (sqtype Ty) (sqtype bb)) (sctype bb)) Hsubq). }
    destruct (dispatch_sig CT cy (sctype Ty) m Hct Hanc mdef mdef0 (rqtype rqty) (rqtype rqty)
               HfindC HfindD (Hagree_from (rqtype rqty) (Hagr_gen (rqtype rqty) Hrm))) as [_ [Hb _]].
    eapply Forall2_trans_gen; [|exact Hab|exact Hb].
    intros a b c Habc Hbac. exact (base_trans CT (sctype a) (sctype b) (sctype c) Habc Hbac). }
  assert (Hpar_qual : forall i aT T, nth_error argtypes i = Some aT ->
      nth_error (mparams (msignature mdef)) i = Some T ->
      forall qr qcC0 qcR, r_muttype h ly = Some qcR ->
        qualifier_typable_context qr (sqtype aT) qcC0 ->
        qualifier_typable_context qcR (sqtype Ty) qcC0 ->
        qualifier_typable_context qr (sqtype T) qcR).
  { intros i aT T HargT Hnth qr qcC0 qcR HqcR HctxA HctxTy0.
    assert (Hi : i < length (mparams (msignature mdef0))).
    { pose proof (Forall2_length Harg_sub) as Hlen.
      assert (Hia : i < length argtypes) by (eapply nth_error_Some_lt; eauto). lia. }
    assert (HPDN : nth_error (mparams (msignature mdef0)) i <> None) by (apply nth_error_Some; lia).
    destruct (nth_error (mparams (msignature mdef0)) i) as [PD|] eqn:HPD; [|contradiction].
    assert (HsubPD : qualified_type_subtype CT aT (Build_qualified_type (g (sqtype Ty) (sqtype PD)) (sctype PD))).
    { exact (Forall2_nth_error qualified_type qualified_type
               (fun arg T => qualified_type_subtype CT arg (Build_qualified_type (g (sqtype Ty) (sqtype T)) (sctype T)))
               argtypes (mparams (msignature mdef0)) Harg_sub i aT PD HargT HPD). }
    assert (HctxPD : qualifier_typable_context qr (sqtype PD) qcR).
    { exact (Hargtr qr qcR qcC0 (sqtype aT) (sqtype Ty) (sqtype PD)
               (qualified_type_subtype_q CT aT (Build_qualified_type (g (sqtype Ty) (sqtype PD)) (sctype PD)) HsubPD)
               HctxA HctxTy0). }
    destruct (dispatch_sig CT cy (sctype Ty) m Hct Hanc mdef mdef0 qr qcR
               HfindC HfindD (Hagree_from qcR (Hagr_gen qcR HqcR))) as [_ [_ Hc]].
    exact (Forall2_nth_error qualified_type qualified_type
             (fun TD TC => qualifier_typable_context qr (sqtype TD) qcR ->
                           qualifier_typable_context qr (sqtype TC) qcR)
             (mparams (msignature mdef0)) (mparams (msignature mdef)) Hc i PD T HPD Hnth HctxPD). }
  exact (wf_r_config_call_frame_dispatch CT sΓ rΓ h y Ty zs argtypes vals ly mdef
           Hwf Hvaly Hgety Hargs Hgetargs Hwfsenv Hrecv_base Hrecv_qual Hpar_base Hpar_qual).
Qed.

Lemma wf_r_config_env_update :
  forall CT sΓ rΓ h h' x v Tx,
    wf_r_config CT sΓ rΓ h ->
    wf_heap CT h' ->
    length h <= length h' ->
    x <> 0 ->
    (forall loc, loc < length h -> r_type h' loc = r_type h loc) ->
    (forall iot qcontext, get_this_var_mapping (vars rΓ) = Some iot ->
       r_muttype h iot = Some qcontext -> value_typable CT h' qcontext v Tx) ->
    static_getType sΓ x = Some Tx ->
    wf_r_config CT sΓ (set_vars rΓ (update x v (vars rΓ))) h'.
Proof.
  intros CT sΓ rΓ h h' x v Tx Hwf Hheap' Hlenh Hnotrcv Hrt Htyp Hgetx.
  pose proof (wf_r_config_ct _ _ _ _ Hwf) as Hct.
  pose proof (wf_r_config_renv _ _ _ _ Hwf) as Hrenv.
  pose proof (wf_r_config_senv _ _ _ _ Hwf) as Hsenv.
  pose proof (wf_r_config_len _ _ _ _ Hwf) as Hlen.
  split; [exact Hct|].
  split; [exact Hheap'|].
  split.
  { unfold wf_renv. simpl. split.
    - rewrite length_update. apply (wf_renv_dom _ _ _ Hrenv).
    - split.
      + destruct (wf_renv_this _ _ _ Hrenv) as [iot [Hg Hlt]].
        exists iot. split.
        * assert (Heqg : get_this_var_mapping (update x v (vars rΓ)) = get_this_var_mapping (vars rΓ))
            by (apply get_this_update_neq; exact Hnotrcv).
          rewrite Heqg. exact Hg.
        * lia.
      + apply (Forall_update_general value (value_wf_h h') (vars rΓ) x v).
        * rewrite Forall_forall. intros vv Hv.
          apply (value_wf_mono h h' vv).
          -- intros loc Hne. destruct (runtime_getObj h loc) as [o|] eqn:E; [|contradiction].
             assert (Hloc : loc < length h) by (eapply runtime_getObj_Some_lt; eauto).
             assert (Hr : r_type h loc = Some (rt_type o)) by (unfold r_type; rewrite E; reflexivity).
             assert (Hr' : r_type h' loc = Some (rt_type o)) by (rewrite (Hrt loc Hloc); exact Hr).
             destruct (runtime_getObj h' loc) as [o'|] eqn:E'; [discriminate|].
             exfalso. unfold r_type in Hr'. rewrite E' in Hr'. discriminate.
          -- exact (proj1 (Forall_forall _ _) (wf_renv_Forall _ _ _ Hrenv) vv Hv).
        * destruct (wf_r_config_ctx CT sΓ rΓ h Hwf) as [iot0 [qcC [Hgt0 Hmut0]]].
          exact (value_typable_wf _ _ _ _ _ (Htyp iot0 qcC Hgt0 Hmut0)).
  }
  split; [exact Hsenv|].
  split.
  { rewrite length_update. exact Hlen. }
  intros ι qcontext Hgt Hmut i Hi sqt Hnth.
  assert (Hgtc : get_this_var_mapping (vars rΓ) = Some ι).
  { assert (Hgt2 : get_this_var_mapping (update x v (vars rΓ)) = Some ι) by (simpl in Hgt; exact Hgt).
    rewrite (get_this_update_neq (vars rΓ) x v Hnotrcv) in Hgt2. exact Hgt2. }
  assert (Hmut_h : r_muttype h ι = Some qcontext).
  { destruct (wf_renv_this _ _ _ Hrenv) as [it [Hgit Hltit]].
    assert (Hι : ι = it) by (rewrite Hgit in Hgtc; injection Hgtc as ->; reflexivity). subst ι.
    rewrite r_muttype_eq_rtype.
    rewrite r_muttype_eq_rtype in Hmut.
    assert (Hrt' : r_type h' it = r_type h it) by (exact (Hrt it Hltit)).
    rewrite Hrt' in Hmut. exact Hmut. }
  destruct (Nat.eq_dec i x) as [Heqix|Hneqix].
  - subst i.
    assert (Hsq : sqt = Tx) by (unfold static_getType in Hgetx; rewrite Hgetx in Hnth; injection Hnth as Ht; symmetry; exact Ht).
    subst sqt.
    assert (Hxlen : x < length (vars rΓ)) by (unfold static_getType in Hgetx; lia).
    assert (Hrv : runtime_getVal (set_vars rΓ (update x v (vars rΓ))) x = Some v).
    { unfold runtime_getVal. simpl. apply nth_error_update_same. exact Hxlen. }
    rewrite Hrv. simpl. exact (Htyp ι qcontext Hgtc Hmut_h).
  - assert (Hrv : runtime_getVal (set_vars rΓ (update x v (vars rΓ))) i = runtime_getVal rΓ i).
    { unfold runtime_getVal. simpl. apply nth_error_update_diff. congruence. }
    rewrite Hrv.
    destruct (runtime_getVal rΓ i) as [vv|] eqn:Hv.
    + pose proof (wf_r_config_corr CT sΓ rΓ h Hwf ι qcontext Hgtc Hmut_h i vv sqt Hi Hnth Hv) as Hc.
      destruct vv as [|loc]; simpl in *.
      * exact I.
      * exact (wf_r_typable_rtype_eq_cond CT h h' loc sqt qcontext
                 (fun Hne => Hrt loc (r_type_neq_lt h loc Hne)) Hc).
    + pose proof (wf_r_config_corr_raw CT sΓ rΓ h Hwf ι qcontext Hgtc Hmut_h i Hi sqt Hnth) as Hc.
      rewrite Hv in Hc. exact Hc.
Qed.

(* ===== return-type dispatch helpers ===== *)
Lemma ctx_ro : forall qr qc, qualifier_typable_context qr RO qc.
Proof. intros [] []; cbn; tauto. Qed.

Lemma ctx_imm_imm_r : forall qr qc, qualifier_typable_context qr Imm qc -> qr = Imm_r.
Proof. intros qr qc H. destruct qr, qc; cbn in *; try discriminate; try tauto; reflexivity. Qed.

Lemma vpa_qq_abstract_rdm : forall q, vpa_mutability_qq_abstract_state RDM q = q.
Proof. intros q. destruct q; reflexivity. Qed.

Lemma vpa_qq_abstract_lost : forall q1, vpa_mutability_qq_abstract_state q1 Lost = Lost.
Proof. destruct q1; reflexivity. Qed.

Lemma ret_bridge2 : forall (qr qcF qcC : q_r) (qBody qRetR qRetS qc qTy qTx : q),
  (qc = Mut \/ qc = Imm \/ qc = RDM) ->
  (qc = Mut -> qcF = Mut_r) ->
  (qc = Imm -> qcF = Imm_r) ->
  qualifier_typable_context qr qBody qcF ->
  q_subtype qBody qRetR ->
  q_subtype qRetR (vpa_mutability_qq_abstract_state qc qRetS) ->
  q_subtype (vpa_mutability_qq_abstract_state qTy qRetS) qTx ->
  qualifier_typable_context qcF qTy qcC ->
  qualifier_typable_context qr qTx qcC.
Proof.
  intros qr qcF qcC qBody qRetR qRetS qc qTy qTx Hqc HM HI Hctx Hbr Hc Hd He.
  assert (HctxR : qualifier_typable_context qr (vpa_mutability_qq_abstract_state qc qRetS) qcF).
  { eapply qualifier_typable_context_mono; [|exact Hctx]. eapply q_subtype_trans; [exact Hbr|exact Hc]. }
  destruct Hqc as [Hq|[Hq|Hq]].
  - subst qc. destruct qRetS.
    + cbn in HctxR, Hd.
      eapply (ret_transfer qr qcF qcC Mut Mut qTy qTx).
      * apply q_refl. discriminate.
      * exact Hd. * exact He. * exact HctxR.
    + cbn in HctxR, Hd.
      eapply (ret_transfer qr qcF qcC Imm Imm qTy qTx).
      * apply q_refl. discriminate.
      * exact Hd. * exact He. * exact HctxR.
    + cbn in HctxR, Hd. specialize (HM eq_refl). subst qcF.
      assert (Hqr : qr = Mut_r) by (apply ctx_mut_mut_r with (qc:=Mut_r); exact HctxR). subst qr.
      destruct qTy; cbn in Hd; destruct qTx; cbn in *; destruct qcC; cbn in *;
        repeat match goal with H : q_subtype _ _ |- _ => inversion H; subst; clear H end;
        cbn in *; try discriminate; try congruence; try tauto.
    + cbn in HctxR, Hd.
      eapply (ret_transfer qr qcF qcC RO RO qTy qTx).
      * apply q_refl. discriminate.
      * exact Hd. * exact He. * exact HctxR.
    + rewrite vpa_qq_abstract_lost in Hd. inversion Hd; subst; cbn in *.
      * exfalso. exact (Hnot_lost eq_refl).
      * exact (ctx_ro qr qcC).
    + cbn in HctxR, Hd.
      eapply (ret_transfer qr qcF qcC Bot Bot qTy qTx).
      * apply q_refl. discriminate.
      * exact Hd. * exact He. * exact HctxR.
  - subst qc. destruct qRetS.
    + cbn in HctxR, Hd.
      eapply (ret_transfer qr qcF qcC Mut Mut qTy qTx).
      * apply q_refl. discriminate.
      * exact Hd. * exact He. * exact HctxR.
    + cbn in HctxR, Hd.
      eapply (ret_transfer qr qcF qcC Imm Imm qTy qTx).
      * apply q_refl. discriminate.
      * exact Hd. * exact He. * exact HctxR.
    + cbn in HctxR, Hd. specialize (HI eq_refl). subst qcF.
      assert (Hqr : qr = Imm_r) by (exact (ctx_imm_imm_r qr Imm_r HctxR)). subst qr.
      destruct qTy; cbn in Hd; destruct qTx; cbn in *; destruct qcC; cbn in *;
        repeat match goal with H : q_subtype _ _ |- _ => inversion H; subst; clear H end;
        cbn in *; try discriminate; try congruence; try tauto.
    + cbn in HctxR, Hd.
      eapply (ret_transfer qr qcF qcC RO RO qTy qTx).
      * apply q_refl. discriminate.
      * exact Hd. * exact He. * exact HctxR.
    + rewrite vpa_qq_abstract_lost in Hd. inversion Hd; subst; cbn in *.
      * exfalso. exact (Hnot_lost eq_refl).
      * exact (ctx_ro qr qcC).
    + cbn in HctxR, Hd.
      eapply (ret_transfer qr qcF qcC Bot Bot qTy qTx).
      * apply q_refl. discriminate.
      * exact Hd. * exact He. * exact HctxR.
  - subst qc. rewrite vpa_qq_abstract_rdm in HctxR.
    destruct qRetS.
    + cbn in HctxR, Hd.
      eapply (ret_transfer qr qcF qcC Mut Mut qTy qTx).
      * apply q_refl. discriminate.
      * exact Hd. * exact He. * exact HctxR.
    + cbn in HctxR, Hd.
      eapply (ret_transfer qr qcF qcC Imm Imm qTy qTx).
      * apply q_refl. discriminate.
      * exact Hd. * exact He. * exact HctxR.
    + cbn in HctxR, Hd.
      eapply (ret_transfer qr qcF qcC RDM RDM qTy qTx).
      * apply q_refl. discriminate.
      * exact Hd. * exact He. * exact HctxR.
    + cbn in HctxR, Hd.
      eapply (ret_transfer qr qcF qcC RO RO qTy qTx).
      * apply q_refl. discriminate.
      * exact Hd. * exact He. * exact HctxR.
    + rewrite vpa_qq_abstract_lost in Hd. inversion Hd; subst; cbn in *.
      * exfalso. exact (Hnot_lost eq_refl).
      * exact (ctx_ro qr qcC).
    + cbn in HctxR, Hd.
      eapply (ret_transfer qr qcF qcC Bot Bot qTy qTx).
      * apply q_refl. discriminate.
      * exact Hd. * exact He. * exact HctxR.
Qed.

Lemma ctx_deadapt : forall (qr qcF : q_r) (qc qM : q),
  (qc = Mut \/ qc = Imm \/ qc = RDM) ->
  (qc = Mut -> qcF = Mut_r) ->
  (qc = Imm -> qcF = Imm_r) ->
  qualifier_typable_context qr (vpa_mutability_qq_abstract_state qc qM) qcF ->
  qualifier_typable_context qr qM qcF.
Proof.
  intros qr qcF qc qM Hqc HM HI H.
  destruct Hqc as [Hq|[Hq|Hq]].
  - subst qc. destruct qM; cbn in *.
    + exact H. + exact H.
    + specialize (HM eq_refl). subst qcF.
      assert (Hqr : qr = Mut_r) by (exact (ctx_mut_mut_r qr Mut_r H)).
      subst qr. apply ctx_rdm_self.
    + exact H. + exact H. + exact H.
  - subst qc. destruct qM; cbn in *.
    + exact H. + exact H.
    + specialize (HI eq_refl). subst qcF.
      assert (Hqr : qr = Imm_r) by (exact (ctx_imm_imm_r qr Imm_r H)).
      subst qr. apply ctx_rdm_self.
    + exact H. + exact H. + exact H.
  - subst qc. rewrite vpa_qq_abstract_rdm in H. destruct qM; cbn in *; exact H.
Qed.

Lemma moc_ret : forall CT qc (o r : method_sig),
  method_override_compatible CT qc r o ->
  qualified_type_subtype CT (mret r) (vpa_mutability_override qc (mret o)).
Proof. intros CT qc o r H. unfold method_override_compatible in H. tauto. Qed.

Lemma dispatch_ret :
  forall CT (C D : class_name) m,
    wf_class_table CT -> base_subtype CT C D ->
    forall mdefC mdefD qr qcF,
      FindMethodWithName CT C m mdefC ->
      FindMethodWithName CT D m mdefD ->
      (forall K qb, base_subtype CT C K -> bound CT K = Some qb ->
          (qc2q qb = Mut -> qcF = Mut_r) /\ (qc2q qb = Imm -> qcF = Imm_r)) ->
      qualifier_typable_context qr (sqtype (mret (msignature mdefC))) qcF ->
      qualifier_typable_context qr (sqtype (mret (msignature mdefD))) qcF.
Proof.
  intros CT C D m Hwf Hsub.
  induction Hsub as
    [ CT C Hdom
    | CT C D1 D H1 IH1 H2 IH2
    | CT C D HdomC HdomD Hpar ];
    intros mdefC mdefD qr qcF HfindC HfindD Hagree Hctx.
  - assert (Hmm : mdefC = mdefD) by (exact (find_method_det _ _ _ _ HfindC _ HfindD)).
    subst mdefD. exact Hctx.
  - destruct (find_method_exists_ancestor CT D1 D m Hwf H2 mdefD HfindD) as [mdef1 Hfind1].
    assert (Hagree1 : forall K qb, base_subtype CT D1 K -> bound CT K = Some qb ->
        (qc2q qb = Mut -> qcF = Mut_r) /\ (qc2q qb = Imm -> qcF = Imm_r)).
    { intros K qb Hanc Hb. exact (Hagree K qb (base_trans CT C D1 K H1 Hanc) Hb). }
    exact (IH2 Hwf mdef1 mdefD qr qcF Hfind1 HfindD Hagree1
             (IH1 Hwf mdefC mdef1 qr qcF HfindC Hfind1 Hagree Hctx)).
  - destruct (parent_lookup_find _ _ _ Hpar) as [defH [HfH HsH]].
    inversion HfindC; subst; clear HfindC.
    + assert (Hdefeq : def = defH) by (exact (find_class_fun CT C def defH Hfind HfH)).
      subst def.
      pose proof (find_method_here_wf_method CT C m mdefC defH Hwf Hfind Hget_method) as Hwfm.
      pose proof (gget_method_mname _ _ _ Hget_method) as Hmname.
      assert (HsD : super (signature defH) = Some D) by (rewrite HsH; reflexivity).
      assert (Hbnd : bound CT C = Some (class_qualifier (signature defH))) by (apply bound_find; exact Hfind).
      assert (HfmD : FindMethodWithName CT D (mname (msignature mdefC)) mdefD).
      { assert (Hcp := HfindD). rewrite <- Hmname in Hcp. exact Hcp. }
      pose proof (wf_method_moc CT C mdefC defH D (class_qualifier (signature defH)) mdefD
                    Hwfm Hfind HsD Hbnd HfmD) as Hmoc.
      pose proof (moc_ret _ _ _ _ Hmoc) as Hretsub.
      pose proof (qualified_type_subtype_q _ _ _ Hretsub) as Hq.
      eapply ctx_deadapt with (qc := qc2q (class_qualifier (signature defH)))
             (qM := sqtype (mret (msignature mdefD))) (qcF := qcF).
      * apply qc2q_cases.
      * intros Hq'. destruct (Hagree C (class_qualifier (signature defH))
                       (base_refl CT C HdomC) Hbnd) as [Hm Hi]. exact (Hm Hq').
      * intros Hq'. destruct (Hagree C (class_qualifier (signature defH))
                       (base_refl CT C HdomC) Hbnd) as [Hm Hi]. exact (Hi Hq').
      * eapply qualifier_typable_context_mono; [exact Hq|exact Hctx].
    + assert (Hdefeq : def = defH) by (exact (find_class_fun CT C def defH Hfind HfH)).
      subst def.
      assert (HparD : parent = D).
      { rewrite HsH in Hsuper. injection Hsuper as Hp. symmetry. exact Hp. }
      subst parent.
      assert (Hmm : mdefC = mdefD) by (exact (find_method_det _ _ _ _ Hparent_fmn _ HfindD)).
      subst mdefD. exact Hctx.
Qed.

Lemma wf_method_ret_wf : forall CT C mdef,
  wf_method CT C mdef ->
  wf_stypeuse CT (sqtype (mret (msignature mdef))) (sctype (mret (msignature mdef))).
Proof. intros CT C mdef H. unfold wf_method in H. cbn in H. destruct H as [Hret _]. exact Hret. Qed.

Lemma dispatch_ret_base : forall CT (C D : class_name) m,
  wf_class_table CT -> base_subtype CT C D ->
  forall mdefC mdefD,
    FindMethodWithName CT C m mdefC ->
    FindMethodWithName CT D m mdefD ->
    base_subtype CT (sctype (mret (msignature mdefC))) (sctype (mret (msignature mdefD))).
Proof.
  intros CT C D m Hwf Hsub.
  induction Hsub as
    [ CT C Hdom
    | CT C D1 D H1 IH1 H2 IH2
    | CT C D HdomC HdomD Hpar ];
    intros mdefC mdefD HfindC HfindD.
  - assert (Hmm : mdefC = mdefD) by (exact (find_method_det _ _ _ _ HfindC _ HfindD)).
    subst mdefD.
    destruct (find_method_wf_method _ _ _ _ Hwf HfindC) as [C' Hwfm].
    apply base_refl. apply wf_stypeuse_dom with (q := sqtype (mret (msignature mdefC))).
    exact (wf_method_ret_wf CT C' mdefC Hwfm).
  - destruct (find_method_exists_ancestor CT D1 D m Hwf H2 mdefD HfindD) as [mdef1 Hfind1].
    exact (base_trans CT (sctype (mret (msignature mdefC))) (sctype (mret (msignature mdef1)))
             (sctype (mret (msignature mdefD)))
             (IH1 Hwf mdefC mdef1 HfindC Hfind1) (IH2 Hwf mdef1 mdefD Hfind1 HfindD)).
  - destruct (parent_lookup_find _ _ _ Hpar) as [defH [HfH HsH]].
    inversion HfindC; subst; clear HfindC.
    + assert (Hdefeq : def = defH) by (exact (find_class_fun CT C def defH Hfind HfH)).
      subst def.
      pose proof (find_method_here_wf_method CT C m mdefC defH Hwf Hfind Hget_method) as Hwfm.
      pose proof (gget_method_mname _ _ _ Hget_method) as Hmname.
      assert (HsD : super (signature defH) = Some D) by (rewrite HsH; reflexivity).
      assert (Hbnd : bound CT C = Some (class_qualifier (signature defH))) by (apply bound_find; exact Hfind).
      assert (HfmD : FindMethodWithName CT D (mname (msignature mdefC)) mdefD).
      { assert (Hcp := HfindD). rewrite <- Hmname in Hcp. exact Hcp. }
      pose proof (wf_method_moc CT C mdefC defH D (class_qualifier (signature defH)) mdefD
                    Hwfm Hfind HsD Hbnd HfmD) as Hmoc.
      pose proof (moc_ret _ _ _ _ Hmoc) as Hretsub.
      exact (qualified_type_subtype_base _ _ _ Hretsub).
    + assert (Hdefeq : def = defH) by (exact (find_class_fun CT C def defH Hfind HfH)).
      subst def.
      assert (HparD : parent = D).
      { rewrite HsH in Hsuper. injection Hsuper as Hp. symmetry. exact Hp. }
      subst parent.
      assert (Hmm : mdefC = mdefD) by (exact (find_method_det _ _ _ _ Hparent_fmn _ HfindD)).
      subst mdefD.
      destruct (find_method_wf_method _ _ _ _ Hwf HfindD) as [C' Hwfm].
      apply base_refl. apply wf_stypeuse_dom with (q := sqtype (mret (msignature mdefC))).
      exact (wf_method_ret_wf CT C' mdefC Hwfm).
Qed.

Lemma cy_bound_agree : forall CT sΓ rΓ h y ly cy qc2,
  wf_r_config CT sΓ rΓ h -> runtime_getVal rΓ y = Some (Iot ly) ->
  r_basetype h ly = Some cy -> r_muttype h ly = Some qc2 ->
  forall K qb, base_subtype CT cy K -> bound CT K = Some qb ->
    (qc2q qb = Mut -> qc2 = Mut_r) /\ (qc2q qb = Imm -> qc2 = Imm_r).
Proof.
  intros CT sΓ rΓ h y ly cy qc2 Hwf Hvaly Hbase Hmut K qb Hanc Hb.
  pose proof (wf_r_config_ct _ _ _ _ Hwf) as Hct.
  (* wf_rtypeuse CT qc2 cy *)
  assert (Hruse : wf_rtypeuse CT qc2 cy).
  { destruct (wf_renv_valid CT rΓ h (wf_r_config_renv _ _ _ _ Hwf) y (Iot ly) Hvaly) as [Hn|Hio].
    - discriminate Hn.
    - destruct Hio as [l0 [o0 [Heq Ho]]]. injection Heq as Hly. rewrite <- Hly in Ho.
      assert (Hly_lt : ly < dom h) by (eapply runtime_getObj_Some_lt; eauto).
      assert (Hwo : wf_obj CT h ly) by (apply (wf_r_config_heap _ _ _ _ Hwf); exact Hly_lt).
      destruct (wf_obj_iff CT h ly o0 Ho) as [Hiff _].
      destruct (Hiff Hwo) as [Hru _].
      assert (Hrt : r_type h ly = Some (rt_type o0)) by (unfold r_type; rewrite Ho; reflexivity).
      assert (Hcy : rctype (rt_type o0) = cy).
      { assert (Eb : r_basetype h ly = Some (rctype (rt_type o0))).
        { rewrite r_basetype_eq_rtype. rewrite Hrt. reflexivity. }
        rewrite Eb in Hbase. injection Hbase as Hc. exact Hc. }
      assert (Hmq : rqtype (rt_type o0) = qc2).
      { assert (Em : r_muttype h ly = Some (rqtype (rt_type o0))).
        { rewrite r_muttype_eq_rtype. rewrite Hrt. reflexivity. }
        rewrite Em in Hmut. injection Hmut as Hm. exact Hm. }
      rewrite <- Hcy. rewrite <- Hmq. exact Hru. }
  assert (Hbex : exists qbcy, bound CT cy = Some qbcy).
  { destruct (bound CT cy) as [qbcy|] eqn:Eb.
    - exists qbcy. reflexivity.
    - exfalso. exact (wf_rtypeuse_none _ _ _ Eb Hruse). }
  destruct Hbex as [qbcy Ebcy].
  assert (Hagcy : vpa_mutability_runtime_bound_agree qc2 qbcy = true)
    by (exact (proj2 (wf_rtypeuse_some _ _ _ _ Ebcy Hruse))).
  split.
  - intros Hq. assert (Hqb : qb = Mut_c) by (destruct qb; cbn in Hq; try discriminate; reflexivity).
    subst qb. assert (Hne : Mut_c <> RDM_c) by discriminate.
    assert (Hcy2 : bound CT cy = Some Mut_c) by (exact (bound_propagates CT cy K Hct Hanc Mut_c Hb Hne)).
    rewrite Hcy2 in Ebcy. injection Ebcy as Hqq. subst qbcy.
    exact (agree_mut qc2 Mut_c Hagcy eq_refl).
  - intros Hq. assert (Hqb : qb = Imm_c) by (destruct qb; cbn in Hq; try discriminate; reflexivity).
    subst qb. assert (Hne : Imm_c <> RDM_c) by discriminate.
    assert (Hcy2 : bound CT cy = Some Imm_c) by (exact (bound_propagates CT cy K Hct Hanc Imm_c Hb Hne)).
    rewrite Hcy2 in Ebcy. injection Ebcy as Hqq. subst qbcy.
    exact (agree_imm qc2 Imm_c Hagcy eq_refl).
Qed.

Lemma ret_finish : forall (qr qc2 qcC:q_r) (qs qsTy qsTx:q),
  qualifier_typable_context qr qs qc2 ->
  q_subtype (vpa_mutability_qq_abstract_state qsTy qs) qsTx ->
  qualifier_typable_context qc2 qsTy qcC ->
  qualifier_typable_context qr qsTx qcC.
Proof. qsolve. Qed.

Lemma env_update_strong : forall CT sΓ rΓ h h' x v Tx,
  wf_r_config CT sΓ rΓ h ->
  wf_heap CT h' ->
  length h <= length h' ->
  (forall loc, loc < length h -> r_type h' loc = r_type h loc) ->
  x <> 0 ->
  (forall iot qcontext, get_this_var_mapping (vars rΓ) = Some iot ->
     r_muttype h iot = Some qcontext -> value_typable CT h' qcontext v Tx) ->
  static_getType sΓ x = Some Tx ->
  wf_r_config CT sΓ (set_vars rΓ (update x v (vars rΓ))) h' /\
  get_this_var_mapping (vars (set_vars rΓ (update x v (vars rΓ)))) =
  get_this_var_mapping (vars rΓ) /\
  length h <= length h' /\
  (forall loc, loc < length h -> r_type h' loc = r_type h loc).
Proof.
  intros CT sΓ rΓ h h' x v Tx Hwf Hheap Hlenh Hrt Hnotrcv Htyp Hgetx.
  split.
  - eapply wf_r_config_env_update; eauto.
  - split.
    + assert (Heqg : get_this_var_mapping (update x v (vars rΓ)) = get_this_var_mapping (vars rΓ))
        by (apply get_this_update_neq; exact Hnotrcv).
      simpl. exact Heqg.
    + split; [exact Hlenh|exact Hrt].
Qed.

Lemma ret_finish_ro : forall (qr qc2 qcC:q_r) (qs qsTy qsTx:q),
  qualifier_typable_context qr qs qc2 ->
  q_subtype (vpa_mutability_qq_readonly_state qsTy qs) qsTx ->
  qualifier_typable_context qc2 qsTy qcC ->
  qualifier_typable_context qr qsTx qcC.
Proof. qsolve. Qed.

Lemma preservation_strong :
  forall CT rΓ h stmt res rΓ' h',
    eval_stmt CT rΓ h stmt res rΓ' h' ->
    forall sΓ mt sΓ',
      wf_r_config CT sΓ rΓ h ->
      stmt_typing CT sΓ mt stmt sΓ' ->
      res = OK ->
      wf_r_config CT sΓ' rΓ' h' /\
      get_this_var_mapping (vars rΓ') = get_this_var_mapping (vars rΓ) /\
      length h <= length h' /\
      (forall loc, loc < length h -> r_type h' loc = r_type h loc).
Proof.
  intros CT rΓ h stmt res rΓ' h' Hev.
  induction Hev; intros sΓ mt sΓ' Hwf Hty Heq; try (discriminate Heq).
  - (* Skip *) inversion Hty; subst. split; [exact Hwf|]. split; [reflexivity|]. split; [lia|]. intros; reflexivity.
  - (* Local *)
    inversion Hty; subst.
    split.
    + split; [apply (wf_r_config_ct _ _ _ _ Hwf)|].
      split; [apply (wf_r_config_heap _ _ _ _ Hwf)|].
      split.
      { unfold wf_renv. simpl. split.
        - rewrite app_length. simpl. lia.
        - split.
          + destruct (wf_renv_this _ _ _ (wf_r_config_renv _ _ _ _ Hwf)) as [iot [Hgt Hlt]].
            exists iot. split.
            * rewrite get_this_app_single. exact Hgt.
            * exact Hlt.
          + apply Forall_app. split.
            * apply (wf_renv_Forall _ _ _ (wf_r_config_renv _ _ _ _ Hwf)).
            * apply Forall_cons; [simpl; auto|apply Forall_nil].
      }
      split.
      { apply wf_senv_app_single.
        - apply (wf_r_config_senv _ _ _ _ Hwf).
        - exact Hwf_T. }
      split.
      { simpl. rewrite app_length. rewrite app_length. simpl.
        assert (Hl := wf_r_config_len CT sΓ rΓ h Hwf). lia. }
      intros ι qcontext Hgt Hmut i Hi sqt Hnth.
      assert (Hthis : get_this_var_mapping (vars rΓ) = Some ι).
      { assert (Hvars : vars (set_vars rΓ (vars rΓ ++ [Null_a])) = vars rΓ ++ [Null_a]) by reflexivity.
        rewrite Hvars in Hgt. rewrite get_this_app_single in Hgt. exact Hgt. }
      destruct (lt_eq_lt_dec i (length sΓ)) as [[Hlt|Heqi]|Hgi].
      * assert (Hrv : runtime_getVal (set_vars rΓ (vars rΓ ++ [Null_a])) i = runtime_getVal rΓ i).
        { unfold runtime_getVal. simpl. apply nth_error_app_single_lt.
          pose proof (wf_r_config_len CT sΓ rΓ h Hwf). lia. }
        assert (Hnth' : nth_error sΓ i = Some sqt).
        { rewrite (nth_error_app_single_lt _ sΓ T i Hlt) in Hnth. exact Hnth. }
        rewrite Hrv.
        exact (wf_r_config_corr_raw CT sΓ rΓ h Hwf ι qcontext Hthis Hmut i Hlt sqt Hnth').
      * subst i.
        assert (Hrv : runtime_getVal (set_vars rΓ (vars rΓ ++ [Null_a])) (length sΓ) = Some Null_a).
        { unfold runtime_getVal. simpl.
          assert (Hlen : length (vars rΓ) = length sΓ) by (symmetry; apply (wf_r_config_len _ _ _ _ Hwf)).
          rewrite <- Hlen. apply nth_error_app_single_eq. }
        rewrite Hrv. simpl. exact I.
      * exfalso. rewrite app_length in Hi. simpl in Hi. lia.
    + split.
      * assert (Hvars : vars (set_vars rΓ (vars rΓ ++ [Null_a])) = vars rΓ ++ [Null_a]) by reflexivity.
        rewrite Hvars. apply get_this_app_single.
      * split; [lia|]. intros loc Hloc. reflexivity.
  - (* Assign *)
    inversion Hty; subst.
    destruct (wf_r_config_ctx CT sΓ' rΓ h Hwf) as [iot0 [qcC [Hgt0 Hmut0]]].
    pose proof (eval_expr_value_typable CT sΓ' mt e Te Htype_e rΓ h iot0 qcC v2 Hwf Hgt0 Hmut0 Heval) as Hv2.
    eapply env_update_strong.
    + exact Hwf.
    + apply (wf_r_config_heap _ _ _ _ Hwf).
    + lia.
    + intros loc Hloc. reflexivity.
    + exact Hnot_rcv.
    + intros iot qcontext Hgt Hmut.
      assert (Hι : iot = iot0) by (rewrite Hgt0 in Hgt; injection Hgt as ->; reflexivity). subst iot.
      assert (Hq : qcontext = qcC) by (rewrite Hmut0 in Hmut; injection Hmut as ->; reflexivity). subst qcontext.
      exact (value_typable_sub CT h qcC v2 Te Tx Hsub Hv2).
    + exact Hget_x.
  - (* Field write *)
    inversion Hty; subst.
    + destruct (fldwrite_core CT sΓ' rΓ h x f y loc_x o vf val_y Tx Ty fieldT
                  vpa_mutability_stype_fld_abstract_state Hwf Hval_x Hobj Hfield Hval_y
                  Hget_x Hget_y Hfld_def Hsub fldwrite_abstract) as [Hc [Hlen Hrt]].
      split; [exact Hc|]. split; [reflexivity|]. split; [exact Hlen|exact Hrt].
    + destruct (fldwrite_core CT sΓ' rΓ h x f y loc_x o vf val_y Tx Ty fieldT
                  vpa_mutability_stype_fld_abstract_state Hwf Hval_x Hobj Hfield Hval_y
                  Hget_x Hget_y Hfld_def Hsub fldwrite_abstract) as [Hc [Hlen Hrt]].
      split; [exact Hc|]. split; [reflexivity|]. split; [exact Hlen|exact Hrt].
    + destruct (fldwrite_core CT sΓ' rΓ h x f y loc_x o vf val_y Tx Ty fieldT
                  vpa_mutability_stype_fld_readonly_state Hwf Hval_x Hobj Hfield Hval_y
                  Hget_x Hget_y Hfld_def Hsub fldwrite_readonly) as [Hc [Hlen Hrt]].
      split; [exact Hc|]. split; [reflexivity|]. split; [exact Hlen|exact Hrt].
    + destruct (fldwrite_core CT sΓ' rΓ h x f y loc_x o vf val_y Tx Ty fieldT
                  vpa_mutability_stype_fld_readonly_state Hwf Hval_x Hobj Hfield Hval_y
                  Hget_x Hget_y Hfld_def Hsub fldwrite_readonly) as [Hc [Hlen Hrt]].
      split; [exact Hc|]. split; [reflexivity|]. split; [exact Hlen|exact Hrt].
  - (* New *)
    inversion Hty; subst.
    destruct (new_core CT sΓ' rΓ h x q_c c ys l1 qthisr vals Tx argtypes consig
                Hwf Hthis Hargs Hmut Hget_x Hget_args Hconsig Hnot_rcv Hqc Harg_sub Hresult_sub)
      as [Hc [Hlen Hrt]].
    split; [exact Hc|].
    split.
    { assert (Heqg : get_this_var_mapping (update x (Iot (dom h)) (vars rΓ)) = get_this_var_mapping (vars rΓ))
        by (apply get_this_update_neq; exact Hnot_rcv).
      simpl. exact Heqg. }
    split; [exact Hlen|exact Hrt].
  - (* Call *)
    inversion Hty; subst.
    { (* abstract state *)
    destruct Hfind as [Hfind_meth Hmbody].
    pose proof (wf_r_config_ct _ _ _ _ Hwf) as Hct.
    destruct (find_method_wf_method CT cy m mdef Hct Hfind_meth) as [Cw Hwfm].
    destruct (wf_method_body_typing _ _ _ Hwfm) as [sGb [mbrt [Htyb [Hretlt [Hretnth Hretsub]]]]].
    pose proof (stmt_typing_wf_senv _ _ _ _ _ Htyb) as Hwfsenv.
    pose proof (call_frame_facts CT sΓ' rΓ h y Ty m zs argtypes vals ly cy mdef mdef0
                  vpa_mutability_qq_abstract_state
                  (fun qr qcC qsTy qsR Hs Hc => rcv_transfer qr qcC qsTy qsR Hc Hs)
                  (fun qr qcR qcC qsArg qsTy qsParam Hs Hc1 Hc2 =>
                     param_transfer qr qcR qcC qsArg qsTy qsParam Hc1 Hc2 Hs)
                  Hwf Hval_y Hget_y Hargs Hget_args Hbase Hfind_meth Hfind_m Hwfsenv Hrcv_sub Harg_sub) as Hframe.
    rewrite Hmbody in Hev. rewrite Hmbody in Hretval. rewrite Hmbody in IHHev.
    destruct (IHHev (mreceiver (msignature mdef) :: mparams (msignature mdef))
                (mscope (msignature mdef)) sGb Hframe Htyb eq_refl) as [Hcfg [Hthisb [Hlenb Hrtb]]].
    destruct (wf_r_config_ctx CT sΓ' rΓ h Hwf) as [iot0 [qcC [Hgt0 Hmut0]]].
    destruct (wf_r_config_ctx CT sGb rΓ'' h' Hcfg) as [it2 [qc2 [Hgt2 Hmut2]]].
    assert (Hthisb' : get_this_var_mapping (vars rΓ'') = Some ly).
    { assert (Hfr : get_this_var_mapping (vars (mkr_env (Iot ly :: vals))) = Some ly) by reflexivity.
      rewrite Hfr in Hthisb. exact Hthisb. }
    assert (Hit2 : it2 = ly) by (rewrite Hthisb' in Hgt2; injection Hgt2 as ->; reflexivity). subst it2.
    assert (HyLen : y < length sΓ') by (unfold static_getType in Hget_y; eapply nth_error_Some_lt; eauto).
    pose proof (wf_r_config_corr CT sΓ' rΓ h Hwf iot0 qcC Hgt0 Hmut0 y (Iot ly) Ty HyLen Hget_y Hval_y) as Hyval.
    pose proof (value_typable_iot CT h qcC ly Ty Hyval) as Hyw.
    unfold wf_r_typable in Hyw.
    destruct (r_type h ly) as [rqty0|] eqn:Ery0; [|contradiction].
    destruct Hyw as [HbaseTy HctxTy].
    assert (Hrcy : rctype rqty0 = cy).
    { assert (Eb : r_basetype h ly = Some (rctype rqty0)) by (rewrite r_basetype_eq_rtype; rewrite Ery0; reflexivity).
      rewrite Eb in Hbase. injection Hbase as Hc. exact Hc. }
    assert (Hanc : base_subtype CT cy (sctype Ty)) by (rewrite <- Hrcy; exact HbaseTy).
    assert (Hly_lt : ly < dom h) by (apply r_type_neq_lt; rewrite Ery0; discriminate).
    assert (Erm : r_muttype h ly = Some (rqtype rqty0)).
    { rewrite r_muttype_eq_rtype. rewrite Ery0. reflexivity. }
    assert (Hqc2 : qc2 = rqtype rqty0).
    { assert (Erm' : r_muttype h' ly = Some (rqtype rqty0)).
      { rewrite r_muttype_eq_rtype. rewrite r_muttype_eq_rtype in Erm. rewrite (Hrtb ly Hly_lt). exact Erm. }
      rewrite Erm' in Hmut2. injection Hmut2 as Hq. symmetry. exact Hq. }
    assert (Hmut_ly : r_muttype h ly = Some qc2) by (rewrite Erm; rewrite Hqc2; reflexivity).
    pose proof (cy_bound_agree CT sΓ' rΓ h y ly cy qc2 Hwf Hval_y Hbase Hmut_ly) as Hagree.
    pose proof (wf_r_config_corr CT sGb rΓ'' h' Hcfg ly qc2 Hgt2 Hmut2 (mreturn (Syntax.mbody mdef)) retval mbrt Hretlt Hretnth Hretval) as Hretval_t.
    pose proof (qualified_type_subtype_base _ _ _ Hretsub) as HbaseRet.
    pose proof (dispatch_ret_base CT cy (sctype Ty) m Hct Hanc mdef mdef0 Hfind_meth Hfind_m) as HbaseChain.
    pose proof (qualified_type_subtype_base _ _ _ Hret_sub) as HbaseStatic.
    assert (He : qualifier_typable_context qc2 (sqtype Ty) qcC).
    { rewrite Hqc2. exact HctxTy. }
    assert (Htyp : forall iot qcontext, get_this_var_mapping (vars rΓ) = Some iot ->
                   r_muttype h iot = Some qcontext -> value_typable CT h' qcontext retval Tx).
    { intros iot qcontext Hgt Hmut.
      assert (Hι : iot = iot0) by (rewrite Hgt0 in Hgt; injection Hgt as ->; reflexivity). subst iot.
      assert (Hq : qcontext = qcC) by (rewrite Hmut0 in Hmut; injection Hmut as ->; reflexivity). subst qcontext.
      destruct retval as [|loc].
      - simpl. auto.
      - pose proof (value_typable_iot CT h' qc2 loc mbrt Hretval_t) as Hvt.
        unfold wf_r_typable in Hvt.
        destruct (r_type h' loc) as [rqt|] eqn:Er; [|contradiction].
        destruct Hvt as [HbaseBody HctxBody].
        simpl. unfold wf_r_typable. rewrite Er. split.
        + exact (base_trans CT (rctype rqt) (sctype mbrt) (sctype Tx) HbaseBody
                   (base_trans CT (sctype mbrt) (sctype (mret (msignature mdef))) (sctype Tx) HbaseRet
                      (base_trans CT (sctype (mret (msignature mdef))) (sctype (mret (msignature mdef0))) (sctype Tx)
                         HbaseChain HbaseStatic))).
        + assert (HctxMret : qualifier_typable_context (rqtype rqt) (sqtype (mret (msignature mdef))) qc2).
          { eapply qualifier_typable_context_mono; [|exact HctxBody].
            exact (qualified_type_subtype_q CT mbrt (mret (msignature mdef)) Hretsub). }
          assert (HctxStatic : qualifier_typable_context (rqtype rqt) (sqtype (mret (msignature mdef0))) qc2).
          { exact (dispatch_ret CT cy (sctype Ty) m Hct Hanc mdef mdef0 (rqtype rqt) qc2
                     Hfind_meth Hfind_m Hagree HctxMret). }
          exact (ret_finish (rqtype rqt) qc2 qcC (sqtype (mret (msignature mdef0))) (sqtype Ty) (sqtype Tx)
                   HctxStatic (qualified_type_subtype_q CT (vpa_mutability_tt_abstract_state Ty (mret (msignature mdef0))) Tx Hret_sub) He). }
    eapply env_update_strong.
    + exact Hwf.
    + apply (wf_r_config_heap _ _ _ _ Hcfg).
    + exact Hlenb.
    + exact Hrtb.
    + exact Hnot_rcv.
    + exact Htyp.
    + exact Hget_x.
    }
    { (* read-only state *)
    destruct Hfind as [Hfind_meth Hmbody].
    pose proof (wf_r_config_ct _ _ _ _ Hwf) as Hct.
    destruct (find_method_wf_method CT cy m mdef Hct Hfind_meth) as [Cw Hwfm].
    destruct (wf_method_body_typing _ _ _ Hwfm) as [sGb [mbrt [Htyb [Hretlt [Hretnth Hretsub]]]]].
    pose proof (stmt_typing_wf_senv _ _ _ _ _ Htyb) as Hwfsenv.
    pose proof (call_frame_facts CT sΓ' rΓ h y Ty m zs argtypes vals ly cy mdef mdef0
                  vpa_mutability_qq_readonly_state
                  (fun qr qcC qsTy qsR Hs Hc => rcv_transfer_ro qr qcC qsTy qsR Hc Hs)
                  (fun qr qcR qcC qsArg qsTy qsParam Hs Hc1 Hc2 =>
                     param_transfer_ro qr qcR qcC qsArg qsTy qsParam Hc1 Hc2 Hs)
                  Hwf Hval_y Hget_y Hargs Hget_args Hbase Hfind_meth Hfind_m Hwfsenv Hrcv_sub Harg_sub) as Hframe.
    rewrite Hmbody in Hev. rewrite Hmbody in Hretval. rewrite Hmbody in IHHev.
    destruct (IHHev (mreceiver (msignature mdef) :: mparams (msignature mdef))
                (mscope (msignature mdef)) sGb Hframe Htyb eq_refl) as [Hcfg [Hthisb [Hlenb Hrtb]]].
    destruct (wf_r_config_ctx CT sΓ' rΓ h Hwf) as [iot0 [qcC [Hgt0 Hmut0]]].
    destruct (wf_r_config_ctx CT sGb rΓ'' h' Hcfg) as [it2 [qc2 [Hgt2 Hmut2]]].
    assert (Hthisb' : get_this_var_mapping (vars rΓ'') = Some ly).
    { assert (Hfr : get_this_var_mapping (vars (mkr_env (Iot ly :: vals))) = Some ly) by reflexivity.
      rewrite Hfr in Hthisb. exact Hthisb. }
    assert (Hit2 : it2 = ly) by (rewrite Hthisb' in Hgt2; injection Hgt2 as ->; reflexivity). subst it2.
    assert (HyLen : y < length sΓ') by (unfold static_getType in Hget_y; eapply nth_error_Some_lt; eauto).
    pose proof (wf_r_config_corr CT sΓ' rΓ h Hwf iot0 qcC Hgt0 Hmut0 y (Iot ly) Ty HyLen Hget_y Hval_y) as Hyval.
    pose proof (value_typable_iot CT h qcC ly Ty Hyval) as Hyw.
    unfold wf_r_typable in Hyw.
    destruct (r_type h ly) as [rqty0|] eqn:Ery0; [|contradiction].
    destruct Hyw as [HbaseTy HctxTy].
    assert (Hrcy : rctype rqty0 = cy).
    { assert (Eb : r_basetype h ly = Some (rctype rqty0)) by (rewrite r_basetype_eq_rtype; rewrite Ery0; reflexivity).
      rewrite Eb in Hbase. injection Hbase as Hc. exact Hc. }
    assert (Hanc : base_subtype CT cy (sctype Ty)) by (rewrite <- Hrcy; exact HbaseTy).
    assert (Hly_lt : ly < dom h) by (apply r_type_neq_lt; rewrite Ery0; discriminate).
    assert (Erm : r_muttype h ly = Some (rqtype rqty0)).
    { rewrite r_muttype_eq_rtype. rewrite Ery0. reflexivity. }
    assert (Hqc2 : qc2 = rqtype rqty0).
    { assert (Erm' : r_muttype h' ly = Some (rqtype rqty0)).
      { rewrite r_muttype_eq_rtype. rewrite r_muttype_eq_rtype in Erm. rewrite (Hrtb ly Hly_lt). exact Erm. }
      rewrite Erm' in Hmut2. injection Hmut2 as Hq. symmetry. exact Hq. }
    assert (Hmut_ly : r_muttype h ly = Some qc2) by (rewrite Erm; rewrite Hqc2; reflexivity).
    pose proof (cy_bound_agree CT sΓ' rΓ h y ly cy qc2 Hwf Hval_y Hbase Hmut_ly) as Hagree.
    pose proof (wf_r_config_corr CT sGb rΓ'' h' Hcfg ly qc2 Hgt2 Hmut2 (mreturn (Syntax.mbody mdef)) retval mbrt Hretlt Hretnth Hretval) as Hretval_t.
    pose proof (qualified_type_subtype_base _ _ _ Hretsub) as HbaseRet.
    pose proof (dispatch_ret_base CT cy (sctype Ty) m Hct Hanc mdef mdef0 Hfind_meth Hfind_m) as HbaseChain.
    pose proof (qualified_type_subtype_base _ _ _ Hret_sub) as HbaseStatic.
    assert (He : qualifier_typable_context qc2 (sqtype Ty) qcC).
    { rewrite Hqc2. exact HctxTy. }
    assert (Htyp : forall iot qcontext, get_this_var_mapping (vars rΓ) = Some iot ->
                   r_muttype h iot = Some qcontext -> value_typable CT h' qcontext retval Tx).
    { intros iot qcontext Hgt Hmut.
      assert (Hι : iot = iot0) by (rewrite Hgt0 in Hgt; injection Hgt as ->; reflexivity). subst iot.
      assert (Hq : qcontext = qcC) by (rewrite Hmut0 in Hmut; injection Hmut as ->; reflexivity). subst qcontext.
      destruct retval as [|loc].
      - simpl. auto.
      - pose proof (value_typable_iot CT h' qc2 loc mbrt Hretval_t) as Hvt.
        unfold wf_r_typable in Hvt.
        destruct (r_type h' loc) as [rqt|] eqn:Er; [|contradiction].
        destruct Hvt as [HbaseBody HctxBody].
        simpl. unfold wf_r_typable. rewrite Er. split.
        + exact (base_trans CT (rctype rqt) (sctype mbrt) (sctype Tx) HbaseBody
                   (base_trans CT (sctype mbrt) (sctype (mret (msignature mdef))) (sctype Tx) HbaseRet
                      (base_trans CT (sctype (mret (msignature mdef))) (sctype (mret (msignature mdef0))) (sctype Tx)
                         HbaseChain HbaseStatic))).
        + assert (HctxMret : qualifier_typable_context (rqtype rqt) (sqtype (mret (msignature mdef))) qc2).
          { eapply qualifier_typable_context_mono; [|exact HctxBody].
            exact (qualified_type_subtype_q CT mbrt (mret (msignature mdef)) Hretsub). }
          assert (HctxStatic : qualifier_typable_context (rqtype rqt) (sqtype (mret (msignature mdef0))) qc2).
          { exact (dispatch_ret CT cy (sctype Ty) m Hct Hanc mdef mdef0 (rqtype rqt) qc2
                     Hfind_meth Hfind_m Hagree HctxMret). }
          exact (ret_finish_ro (rqtype rqt) qc2 qcC (sqtype (mret (msignature mdef0))) (sqtype Ty) (sqtype Tx)
                   HctxStatic (qualified_type_subtype_q CT (vpa_mutability_tt_readonly_state Ty (mret (msignature mdef0))) Tx Hret_sub) He). }
    eapply env_update_strong.
    + exact Hwf.
    + apply (wf_r_config_heap _ _ _ _ Hcfg).
    + exact Hlenb.
    + exact Hrtb.
    + exact Hnot_rcv.
    + exact Htyp.
    + exact Hget_x.
    }
  - (* Seq *)
    inversion Hty; subst.
    destruct (IHHev1 sΓ mt sΓ'0 Hwf Htype1 eq_refl) as [Hcfg1 [Hthis1 [Hlen1 Hrt1]]].
    destruct (IHHev2 sΓ'0 mt sΓ' Hcfg1 Htype2 eq_refl) as [Hcfg2 [Hthis2 [Hlen2 Hrt2]]].
    split; [exact Hcfg2|].
    split; [rewrite Hthis2; exact Hthis1|].
    split; [lia|].
    intros loc Hloc.
    assert (Hloc' : loc < length h') by lia.
    rewrite (Hrt2 loc Hloc'). exact (Hrt1 loc Hloc).
Qed.

Theorem preservation_pico :
  forall CT sΓ mt rΓ h stmt rΓ' h' sΓ'
    (Hwf     : wf_r_config CT sΓ rΓ h)
    (Htyping : stmt_typing CT sΓ mt stmt sΓ')
    (Heval   : eval_stmt CT rΓ h stmt OK rΓ' h'),
    wf_r_config CT sΓ' rΓ' h'.
Proof.
  intros CT sΓ mt rΓ h stmt rΓ' h' sΓ' Hwf Htyping Heval.
  exact (proj1 (preservation_strong CT rΓ h stmt OK rΓ' h' Heval sΓ mt sΓ' Hwf Htyping eq_refl)).
Qed.



Lemma sf_def_rel_det : forall CT C f d1 d2,
  sf_def_rel CT C f d1 -> sf_def_rel CT C f d2 -> d1 = d2.
Proof.
  intros CT C f d1 d2 H1 H2. unfold sf_def_rel in *.
  inversion H1 as [CT1 C1 fs1 f1 d1' Hcf1 Hg1]; subst.
  inversion H2 as [CT2 C2 fs2 f2 d2' Hcf2 Hg2]; subst.
  assert (Hfs : fs1 = fs2) by (exact (CollectFields_det CT C fs1 Hcf1 fs2 Hcf2)).
  subst fs2. unfold gget in *. rewrite Hg1 in Hg2. injection Hg2 as ->. reflexivity.
Qed.

Lemma sf_assign_eq_field : forall CT C f a fd,
  sf_def_rel CT C f fd -> sf_assignability_rel CT C f a -> a = assignability (ftype fd).
Proof.
  intros CT C f a fd Hd Ha. unfold sf_assignability_rel in Ha.
  destruct Ha as [fd' [Hd' Ha']].
  assert (Hfd : fd' = fd) by (eapply sf_def_rel_det; eauto).
  subst fd'. rewrite <- Ha'. reflexivity.
Qed.

Lemma field_def_runtime_eq_static : forall CT Cc Cs f fd_static,
  wf_class_table CT -> base_subtype CT Cc Cs ->
  sf_def_rel CT Cs f fd_static ->
  forall fd_r, sf_def_rel CT Cc f fd_r -> fd_r = fd_static.
Proof.
  intros CT Cc Cs f fd_static Hwf Hsub Hst fd_r Hrt.
  unfold sf_def_rel in *.
  inversion Hrt as [CTr Cr fsr fr fdr Hcfr Hgr]; subst.
  assert (Hg : gget fsr f = Some fd_static)
    by (eapply FieldLookup_prefix; eauto).
  rewrite Hg in Hgr. injection Hgr as ->. reflexivity.
Qed.

Lemma assignable_not_final : forall qTx (a : Syntax.a) (qobj qcontext : q_r),
  (vpa_assignability qTx a = Assignable \/ vpa_assignability_cs_ts qTx a = Assignable) ->
  qualifier_typable_context qobj qTx qcontext ->
  runtime_vpa_assignability qobj a = Assignable.
Proof.
  intros qTx a qobj qcontext [H1|H1] Hctx.
  - apply vpa_assignable_char in H1. destruct H1 as [Ha|[Hq Ha]].
    + subst a. rewrite runtime_assign_any_assignable. reflexivity.
    + subst a. subst qTx.
      assert (Hqr : qobj = Mut_r) by (exact (ctx_mut_mut_r qobj qcontext Hctx)).
      subst qobj. rewrite runtime_assign_mut_rda. reflexivity.
  - apply vpa_assignable_cs_ts_char in H1. destruct H1 as [Hq Ha]. subst qTx.
    destruct Ha as [Ha|Ha]; subst a.
    + rewrite runtime_assign_any_assignable. reflexivity.
    + assert (Hqr : qobj = Mut_r) by (exact (ctx_mut_mut_r qobj qcontext Hctx)).
      subst qobj. rewrite runtime_assign_mut_rda. reflexivity.
Qed.



Lemma no_mutation :
  forall CT rΓ h stmt res rΓ' h',
    eval_stmt CT rΓ h stmt res rΓ' h' ->
    forall sΓ mt sΓ',
      wf_r_config CT sΓ rΓ h ->
      stmt_typing CT sΓ mt stmt sΓ' ->
      res = MUTATIONEXP -> False.
Proof.
  intros CT rΓ h stmt res rΓ' h' Hev.
  induction Hev; intros sΓ mt sΓ' Hwf Hty Heq; try (discriminate Heq).
  - (* Field write mutation *)
    inversion Hty; subst.
    all: (exfalso;
      pose proof (wf_r_config_ct _ _ _ _ Hwf) as Hct;
      destruct (wf_r_config_ctx CT sΓ' rΓ h Hwf) as [iot0 [qcC [Hgt0 Hmut0]]];
      assert (Hi : x < length sΓ') by (unfold static_getType in Hget_x; eapply nth_error_Some_lt; eauto);
      pose proof (wf_r_config_corr CT sΓ' rΓ h Hwf iot0 qcC Hgt0 Hmut0 x (Iot loc_x) Tx Hi Hget_x Hval_x) as Hxv;
      pose proof (value_typable_iot CT h qcC loc_x Tx Hxv) as Hxw;
      unfold wf_r_typable in Hxw;
      destruct (r_type h loc_x) as [rqt|] eqn:Er; [|contradiction];
      destruct Hxw as [HbaseTx HctxTx];
      assert (Er2 : r_type h loc_x = Some (rt_type o)) by (unfold r_type; rewrite Hobj; reflexivity);
      assert (Hqobj : rctype rqt = rctype (rt_type o)) by (rewrite Er2 in Er; injection Er as ->; reflexivity);
      assert (Hqobjq : rqtype rqt = rqtype (rt_type o)) by (rewrite Er2 in Er; injection Er as ->; reflexivity);
      assert (Hctx : qualifier_typable_context (rqtype (rt_type o)) (sqtype Tx) qcC)
        by (rewrite <- Hqobjq; exact HctxTx);
      assert (Hbase : base_subtype CT (rctype (rt_type o)) (sctype Tx)) by (rewrite <- Hqobj; exact HbaseTx);
      destruct Hassign as [fdr [Hfld_r Ha_r]];
      destruct Hassign_rel as [fds0 [Hfld_s Ha_s]];
      assert (Hfd1 : fdr = fieldT) by (eapply field_def_runtime_eq_static; eauto);
      assert (Hfd2 : fds0 = fieldT) by (eapply sf_def_rel_det; eauto);
      rewrite Hfd1 in Ha_r; rewrite Hfd2 in Ha_s;
      rewrite <- Ha_s in Hassignable;
      rewrite <- Ha_r in Hfinal;
      pose proof (assignable_not_final (sqtype Tx) (assignability (ftype fieldT))
                    (rqtype (rt_type o)) qcC) as HAF;
      assert (Hres0 : runtime_vpa_assignability (rqtype (rt_type o)) (assignability (ftype fieldT)) = Assignable);
      [ apply HAF; [ try (left; exact Hassignable); try (right; exact Hassignable) | exact Hctx ] | ];
      rewrite Hfinal in Hres0; discriminate Hres0).
  - (* Call mutation in body *)
    inversion Hty; subst.
    { (* abstract state *)
      destruct Hfind as [Hfind_meth Hmbody].
      pose proof (wf_r_config_ct _ _ _ _ Hwf) as Hct.
      destruct (find_method_wf_method CT cy m mdef Hct Hfind_meth) as [Cw Hwfm].
      destruct (wf_method_body_typing _ _ _ Hwfm) as [sGb [mbrt [Htyb [Hretlt [Hretnth Hretsub]]]]].
      pose proof (stmt_typing_wf_senv _ _ _ _ _ Htyb) as Hwfsenv.
      pose proof (call_frame_facts CT sΓ' rΓ h y Ty m zs argtypes vals ly cy mdef mdef0
                    vpa_mutability_qq_abstract_state
                    (fun qr qcC qsTy qsR Hs Hc => rcv_transfer qr qcC qsTy qsR Hc Hs)
                    (fun qr qcR qcC qsArg qsTy qsParam Hs Hc1 Hc2 =>
                       param_transfer qr qcR qcC qsArg qsTy qsParam Hc1 Hc2 Hs)
                    Hwf Hval_y Hget_y Hargs Hget_args Hbase Hfind_meth Hfind_m Hwfsenv Hrcv_sub Harg_sub) as Hframe.
      rewrite Hmbody in Hev. rewrite Hmbody in IHHev.
      exact (IHHev (mreceiver (msignature mdef) :: mparams (msignature mdef))
                (mscope (msignature mdef)) sGb Hframe Htyb eq_refl). }
    { (* read-only state *)
      destruct Hfind as [Hfind_meth Hmbody].
      pose proof (wf_r_config_ct _ _ _ _ Hwf) as Hct.
      destruct (find_method_wf_method CT cy m mdef Hct Hfind_meth) as [Cw Hwfm].
      destruct (wf_method_body_typing _ _ _ Hwfm) as [sGb [mbrt [Htyb [Hretlt [Hretnth Hretsub]]]]].
      pose proof (stmt_typing_wf_senv _ _ _ _ _ Htyb) as Hwfsenv.
      pose proof (call_frame_facts CT sΓ' rΓ h y Ty m zs argtypes vals ly cy mdef mdef0
                    vpa_mutability_qq_readonly_state
                    (fun qr qcC qsTy qsR Hs Hc => rcv_transfer_ro qr qcC qsTy qsR Hc Hs)
                    (fun qr qcR qcC qsArg qsTy qsParam Hs Hc1 Hc2 =>
                       param_transfer_ro qr qcR qcC qsArg qsTy qsParam Hc1 Hc2 Hs)
                    Hwf Hval_y Hget_y Hargs Hget_args Hbase Hfind_meth Hfind_m Hwfsenv Hrcv_sub Harg_sub) as Hframe.
      rewrite Hmbody in Hev. rewrite Hmbody in IHHev.
      exact (IHHev (mreceiver (msignature mdef) :: mparams (msignature mdef))
                (mscope (msignature mdef)) sGb Hframe Htyb eq_refl). }
  - (* Seq mutation first *)
    inversion Hty; subst.
    exact (IHHev sΓ mt sΓ'0 Hwf Htype1 eq_refl).
  - (* Seq mutation second *)
    inversion Hty; subst.
    destruct (preservation_strong CT rΓ h s1 OK rΓ' h' Hev1 sΓ mt sΓ'0 Hwf Htype1 eq_refl)
      as [Hcfg [_ [_ _]]].
    exact (IHHev2 sΓ'0 mt sΓ' Hcfg Htype2 eq_refl).
Qed.

Theorem well_typed_no_mutation_exp :
  forall CT sΓ mt rΓ h stmt rΓ' h' sΓ'
    (Hwf : wf_r_config CT sΓ rΓ h)
    (Htyping : stmt_typing CT sΓ mt stmt sΓ')
    (Heval : eval_stmt CT rΓ h stmt MUTATIONEXP rΓ' h'),
    False.
Proof.
  intros CT sΓ mt rΓ h stmt rΓ' h' sΓ' Hwf Htyping Heval.
  exact (no_mutation CT rΓ h stmt MUTATIONEXP rΓ' h' Heval sΓ mt sΓ' Hwf Htyping eq_refl).
Qed.
