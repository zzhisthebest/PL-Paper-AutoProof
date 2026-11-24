From cgraphs.multiparty Require Import definitions.

From cgraphs.multiparty Require Import langdef.
From Stdlib Require Import Logic.Eqdep_dec.

Lemma full_reachability_implies_deadlock_freedom es h :
  fully_reachable es h -> deadlock_free es h.
Proof.
  intros Hfull s Hdeadlock.
  assert (∀ x, reachable es h x -> x ∉ s) as Houtside.
  {
    intros x Hreach.
    induction Hreach as
      [i Hstep | i c Hreach IH Hblocked | c x Href Hreach IH].
    - intros Hi. exact (dl_threadb _ _ _ Hdeadlock i Hi Hstep).
    - intros Hi. apply IH. exact (dl_threadw _ _ _ Hdeadlock i c Hi Hblocked).
    - intros Hc. apply IH. exact (dl_chan _ _ _ Hdeadlock c x Hc Href).
  }
  apply (dl_nonempty _ _ _ Hdeadlock).
  apply set_eq. intros x. rewrite elem_of_empty. split; [|contradiction].
  intros Hx. apply (Houtside x); [apply Hfull; eapply dl_active; eauto|exact Hx].
Qed.

Lemma empty_heap_full_reachability_iff_progress es :
  fully_reachable es ∅ <->
  ∀ i, active es ∅ (Thread i) -> can_stepi i es ∅.
Proof.
  assert (∀ ep : endpoint, (∅ : heap) !! ep = None) as Hlookup.
  {
    intros ep.
    change ((∅ : gmap endpoint (gmap participant (list entryT))) !! ep = None).
    apply lookup_empty.
  }
  split.
  - intros Hfull i Hactive.
    pose proof (Hfull (Thread i) Hactive) as Hreach.
    inversion Hreach as [j Hstep | j c Hchan Hblocked |]; subst.
    + exact Hstep.
    + destruct Hblocked as (p & q & k & π & Hk & He & [bs Hbs] & Hpop).
      rewrite Hlookup in Hbs. discriminate.
  - intros Hprogress [i|c] Hactive.
    + apply Thread_step_reachable, Hprogress, Hactive.
    + destruct Hactive as (p & bs & Hbs).
      rewrite Hlookup in Hbs. discriminate.
Qed.

Lemma elem_of_fin_list_iff {A} n (f : fin n → A) (x : A) :
  x ∈ fin_list n f ↔ ∃ i, x = f i.
Proof.
  revert f.
  induction n as [|n IH]; intros f.
  - change (x ∈ [] ↔ ∃ i : fin 0, x = f i).
    split.
    + rewrite elem_of_nil. contradiction.
    + intros [i _]. exact (fin_0_inv (λ _, x ∈ []) i).
  - change (x ∈ f 0%fin :: fin_list n (f ∘ FS) ↔ ∃ i, x = f i).
    rewrite elem_of_cons, IH. split.
    + intros [Hx|(i & Hx)].
      * now exists 0%fin.
      * now exists (FS i).
    + intros (i & Hi). revert Hi.
      apply (fin_S_inv (λ i, x = f i →
        x = f 0%fin ∨ (∃ j : fin n, x = (f ∘ FS) j))).
      * now left.
      * intros j Hj. right. now exists j.
Qed.

Lemma elem_of_big_union_iff `{Countable A} (ss : gset (gset A)) (x : A) :
  x ∈ big_union ss ↔ ∃ s, s ∈ ss ∧ x ∈ s.
Proof.
  unfold big_union.
  refine (set_fold_ind
    (λ (r : gset A) (X : gset (gset A)), x ∈ r ↔ ∃ s, s ∈ X ∧ x ∈ s)
    (∪) ∅ _ _ _ ss); try typeclasses eauto.
  - intros r X Y HXY Hr. set_solver.
  - set_solver.
  - intros s X r Hnot IH. rewrite elem_of_union, IH. set_solver.
Qed.

Lemma elem_of_fin_union_iff `{Countable A} n (f : fin n → gset A) (x : A) :
  x ∈ fin_union n f ↔ ∃ i, x ∈ f i.
Proof.
  unfold fin_union, fin_gset. rewrite elem_of_big_union_iff.
  split.
  - intros (s & Hs & Hx).
    apply elem_of_list_to_set, elem_of_fin_list_iff in Hs.
    destruct Hs as (i & ->). now exists i.
  - intros (i & Hi). exists (f i). split; [|exact Hi].
    apply elem_of_list_to_set, elem_of_fin_list_iff. now exists i.
Qed.

Lemma ctx1_reference_split k e :
  ctx1 k → expr_refs (k e) = expr_refs e ∪ expr_refs (k (Val UnitV)).
Proof.
  intros Hctx. destruct Hctx; cbn [expr_refs val_refs]; try set_solver.
  apply set_eq. intros x.
  rewrite elem_of_union. rewrite !elem_of_fin_union_iff.
  split.
  - intros (q & Hq). cbn [compose] in Hq.
    destruct (decide (p = q)) as [Heq|Hne].
    + now left.
    + right. exists q. cbn [compose]. now rewrite decide_False by exact Hne.
  - intros [He|(q & Hq)].
    + exists p. cbn [compose]. now rewrite decide_True by reflexivity.
    + cbn [compose] in Hq.
      destruct (decide (p = q)) as [Heq|Hne].
      * simpl in Hq. set_solver.
      * exists q. cbn [compose]. now rewrite decide_False by exact Hne.
Qed.

Lemma ctx_reference_split k e :
  ctx k → expr_refs (k e) = expr_refs e ∪ expr_refs (k (Val UnitV)).
Proof.
  intros Hctx. induction Hctx as [|k1 k2 H1 H2 IH].
  - simpl. set_solver.
  - rewrite (ctx1_reference_split k1 (k2 e) H1), IH.
    rewrite (ctx1_reference_split k1 (k2 (Val UnitV)) H1).
    set_solver.
Qed.

Lemma fin_union_reference_bounds `{Countable B} n (f g : fin n → gset B) refs :
  (∀ i, f i ⊆ g i ∧ g i ⊆ f i ∪ refs) →
  fin_union n f ⊆ fin_union n g ∧ fin_union n g ⊆ fin_union n f ∪ refs.
Proof.
  intros Hbounds. split.
  - intros c Hc. apply elem_of_fin_union_iff in Hc as (i & Hci).
    apply elem_of_fin_union_iff. exists i. exact (proj1 (Hbounds i) c Hci).
  - intros c Hc. apply elem_of_fin_union_iff in Hc as (i & Hci).
    apply (proj2 (Hbounds i)) in Hci.
    apply elem_of_union in Hci as [Hci|Hci].
    + apply elem_of_union_l, elem_of_fin_union_iff. now exists i.
    + now apply elem_of_union_r.
Qed.

Lemma subst_reference_bounds x a e :
  expr_refs e ⊆ expr_refs (subst x a e) ∧
  expr_refs (subst x a e) ⊆ expr_refs e ∪ val_refs a.
Proof.
  induction e; cbn [subst expr_refs]; repeat case_decide;
    cbn [expr_refs].
  all: try match goal with
  | H : ∀ i : fin ?n, expr_refs (?f i) ⊆ expr_refs (subst ?u ?v (?f i)) ∧ _ |- _ =>
      pose proof (fin_union_reference_bounds n (expr_refs ∘ f)
        (λ i, expr_refs (subst u v (f i))) (val_refs v) H) as Hbranches;
      clear H
  end.
  all: cbn [compose] in *; set_solver.
Qed.

Lemma reference_subset_in_context k e e' :
  ctx k → expr_refs e' ⊆ expr_refs e →
  expr_refs (k e') ⊆ expr_refs (k e).
Proof.
  intros Hctx Hrefs.
  rewrite (ctx_reference_split k e Hctx), (ctx_reference_split k e' Hctx).
  set_solver.
Qed.

(* The false branch of If is omitted from expr_refs. *)
Lemma pure_step_reference_subset e e' :
  pure_step e e' →
  (∀ e1 e2, e = If (Val (NatV 0)) e1 e2 → expr_refs e2 ⊆ expr_refs e1) →
  expr_refs e' ⊆ expr_refs e.
Proof.
  intros Hstep Hbranches. destruct Hstep; cbn [expr_refs val_refs];
    try solve [set_solver].
  - exact (proj2 (subst_reference_bounds x a e)).
  - exact (proj2 (subst_reference_bounds x a e)).
  - destruct b; cbn.
    + pose proof (proj2 (subst_reference_bounds x v eL)). set_solver.
    + pose proof (proj2 (subst_reference_bounds x v eR)). set_solver.
  - assert (expr_refs (f i) ⊆ fin_union n (expr_refs ∘ f)) as Hselected.
    { intros c Hc. apply elem_of_fin_union_iff. now exists i. }
    set_solver.
  - pose proof (proj2 (subst_reference_bounds x v e)). set_solver.
  - pose proof (proj2 (subst_reference_bounds x1 v1 (subst x2 v2 e))).
    pose proof (proj2 (subst_reference_bounds x2 v2 e)).
    set_solver.
Qed.

Lemma typed_expression_has_no_references Γ e t :
  typed Γ e t → expr_refs e = ∅.
Proof.
  induction 1; cbn [expr_refs val_refs].
  all: try match goal with
  | H : ∀ i : fin ?n, expr_refs (?f i) = ∅ |- _ =>
      assert (fin_union n (expr_refs ∘ f) = ∅) as Hworkers by
        (apply set_eq; intro c;
         rewrite elem_of_fin_union_iff, elem_of_empty; split;
         [intros (i & Hi); cbn [compose] in Hi; rewrite H in Hi; set_solver|contradiction])
  end.
  all: set_solver.
Qed.

Lemma typed_if_false_branch_has_no_references Γ cond e1 e2 t :
  typed Γ (If cond e1 e2) t → expr_refs e2 = ∅.
Proof.
  intros Htyped.
  remember (If cond e1 e2) as e eqn:He.
  induction Htyped; try discriminate.
  - inversion He; subst. eapply typed_expression_has_no_references; eassumption.
  - now apply IHHtyped.
Qed.

Lemma typed_expression_pure_step_has_no_references Γ e t e' :
  typed Γ e t → pure_step e e' → expr_refs e' = ∅.
Proof.
  intros Htyped Hstep.
  assert (expr_refs e' ⊆ expr_refs e) as Hrefs.
  {
    apply pure_step_reference_subset; [exact Hstep|].
    intros e1 e2 ->.
    rewrite (typed_if_false_branch_has_no_references _ _ _ _ _ Htyped).
    set_solver.
  }
  rewrite (typed_expression_has_no_references _ _ _ Htyped) in Hrefs.
  set_solver.
Qed.

Lemma pure_thread_update_reference_subset es h i k e e' :
  es !! i = Some (k e) →
  ctx k →
  pure_step e e' →
  (∀ e1 e2, e = If (Val (NatV 0)) e1 e2 → expr_refs e2 ⊆ expr_refs e1) →
  ∀ x, obj_refs (<[i := k e']> es) h x ⊆ obj_refs es h x.
Proof.
  intros Hlookup Hctx Hstep Hbranches [j|c]; unfold obj_refs.
  - destruct (decide (i = j)) as [->|Hne].
    + assert (j < length es) as Hbound.
      { apply lookup_lt_is_Some. now exists (k e). }
      rewrite list_lookup_insert_eq by exact Hbound.
      rewrite Hlookup. cbn [from_option].
      apply reference_subset_in_context; [exact Hctx|].
      now apply pure_step_reference_subset.
    + now rewrite list_lookup_insert_ne.
  - reflexivity.
Qed.

Lemma blocked_thread_references_channel es h i c :
  thread_blocked es h i c → Chan c ∈ obj_refs es h (Thread i).
Proof.
  intros (p & q & k & π & Hk & Hlookup & _ & _).
  unfold obj_refs. rewrite Hlookup. simpl from_option.
  rewrite (ctx_reference_split _ _ Hk).
  apply elem_of_union_l. simpl. set_solver.
Qed.

Lemma ctx_cannot_create_value k e :
  ctx k → (∀ v, e ≠ Val v) → ∀ v, k e ≠ Val v.
Proof.
  intros Hctx Hnonval. induction Hctx as [|k1 k2 H1 H2 IH].
  - exact Hnonval.
  - intros v. destruct H1; discriminate.
Qed.

Lemma blocked_thread_and_channel_active es h i c :
  thread_blocked es h i c → active es h (Thread i) ∧ active es h (Chan c).
Proof.
  intros (p & q & k & π & Hk & Hlookup & Hpresent & Hpop). split.
  - exists (k (Recv p (Val (ChanV (c,q) π)))). split; [exact Hlookup|].
    apply (ctx_cannot_create_value _ _ Hk); discriminate.
  - now exists q.
Qed.


Lemma elem_of_map_union_iff `{Countable K, Countable B} {A} (f : A → gset B)
    (m : gmap K A) (x : B) :
  x ∈ map_union f m ↔ ∃ i y, m !! i = Some y ∧ x ∈ f y.
Proof.
  induction m as [|i y m Hfresh IH] using map_ind.
  - unfold map_union. rewrite map_fold_empty, elem_of_empty.
    split; [contradiction|]. intros (j & z & Hlook & _).
    rewrite lookup_empty in Hlook. discriminate.
  - unfold map_union in *. rewrite map_fold_insert_L.
    + rewrite elem_of_union, IH. split.
      * intros [Hx|(j & z & Hj & Hx)].
        -- exists i, y. split; [apply lookup_insert_eq|exact Hx].
        -- assert (i ≠ j) as Hneq by (intros <-; congruence).
           exists j, z. rewrite lookup_insert_ne by exact Hneq. auto.
      * intros (j & z & Hz & Hx).
        apply lookup_insert_Some in Hz as [[<- <-]|[Hne Hz]].
        -- now left.
        -- right. now exists j, z.
    + intros. set_solver.
    + exact Hfresh.
Qed.

Definition value_buffer_refs `{Countable B} (f : val → gset B) (buf : list entryT) : gset B :=
  foldr (λ '(_,v) refs, f v ∪ refs) ∅ buf.

Lemma elem_of_value_buffer_refs_iff `{Countable B} (f : val → gset B) xs x :
  x ∈ value_buffer_refs f xs ↔ ∃ i v, (i,v) ∈ xs ∧ x ∈ f v.
Proof.
  induction xs as [|[i v] xs IH]; cbn [value_buffer_refs foldr].
  - set_solver.
  - rewrite elem_of_union, IH. split.
    + intros [Hv|(j & w & Hw & Hx)].
      * exists i, v. split; [apply elem_of_cons; left; reflexivity|exact Hv].
      * exists j, w. split; [apply elem_of_cons; now right|exact Hx].
    + intros (j & w & Hw & Hx).
      apply elem_of_cons in Hw as [Heq|Hw].
      * inversion Heq; subst. now left.
      * right. now exists j, w.
Qed.

Lemma elem_of_buf_refs_iff xs x :
  x ∈ buf_refs xs ↔ ∃ i v, (i,v) ∈ xs ∧ x ∈ val_refs v.
Proof.
  exact (elem_of_value_buffer_refs_iff val_refs xs x).
Qed.

Lemma lookup_heap_slice (h : heap) c q :
  gmap_slice h c !! q =
    (h : gmap endpoint (gmap participant (list entryT))) !! (c,q).
Proof.
  unfold gmap_slice.
  assert (∀ r : option (gmap participant (gmap participant (list entryT))),
    default ∅ r !! q = r ≫= lookup q) as Hdefault.
  { intros [bs|]; [reflexivity|apply lookup_empty]. }
  rewrite Hdefault. apply lookup_map_curry.
Qed.

Definition buffer_at (h : heap) (ep : endpoint) (p : participant) :
    option (list entryT) :=
  (h : gmap endpoint (gmap participant (list entryT))) !! ep ≫= lookup p.

Definition queued_entry (h : heap) (ep : endpoint) (p : participant) (entry : entryT) :=
  ∃ buf, buffer_at h ep p = Some buf ∧ entry ∈ buf.

Definition heap_value_refs `{Countable B} (f : val → gset B) (h : heap) c : gset B :=
  map_union (map_union (value_buffer_refs f)) (gmap_slice h c).

Lemma elem_of_heap_value_refs_iff `{Countable B} (f : val → gset B) h c x :
  x ∈ heap_value_refs f h c ↔
  ∃ q p i v, queued_entry h (c,q) p (i,v) ∧ x ∈ f v.
Proof.
  unfold heap_value_refs. rewrite elem_of_map_union_iff.
  split.
  - intros (q & inner & Hq & Hinner).
    apply elem_of_map_union_iff in Hinner as (p & buf & Hp & Hbuf).
    apply elem_of_value_buffer_refs_iff in Hbuf as (i & v & Hv & Hx).
    exists q, p, i, v. split; [|exact Hx].
    exists buf. split; [|exact Hv].
    unfold buffer_at. now rewrite <- lookup_heap_slice, Hq.
  - intros (q & p & i & v & (buf & Hbuf & Hentry) & Hx).
    unfold buffer_at in Hbuf. rewrite <- lookup_heap_slice in Hbuf.
    destruct (gmap_slice h c !! q) as [inner|] eqn:Hq; [|discriminate].
    exists q, inner. split; [exact Hq|].
    apply elem_of_map_union_iff. exists p, buf. split; [exact Hbuf|].
    apply elem_of_value_buffer_refs_iff. now exists i, v.
Qed.

Lemma elem_of_channel_references_iff es h c x :
  x ∈ obj_refs es h (Chan c) ↔
  ∃ q p i v, queued_entry h (c,q) p (i,v) ∧ x ∈ val_refs v.
Proof.
  exact (elem_of_heap_value_refs_iff val_refs h c x).
Qed.


Lemma queue_push_lookup `{Countable Kp, Countable Kq} {A}
    (bufs : bufsT Kp Kq A) p q (a : A) p' q' :
  push p q a bufs !! q' ≫= lookup p' =
  if decide (q = q' ∧ p = p')
  then (λ xs, xs ++ [a]) <$> (bufs !! q' ≫= lookup p')
  else bufs !! q' ≫= lookup p'.
Proof.
  unfold push.
  destruct (decide (q = q')) as [->|Hnq].
  - rewrite lookup_alter_eq.
    destruct (decide (p = p')) as [->|Hnp].
    + rewrite decide_True by auto.
      destruct (bufs !! q') as [bs|]; [apply lookup_alter_eq|reflexivity].
    + rewrite decide_False by tauto.
      destruct (bufs !! q') as [bs|]; [now apply lookup_alter_ne|reflexivity].
  - rewrite decide_False by tauto.
    now rewrite lookup_alter_ne.
Qed.

Lemma buffer_at_push (h : heap) p ep entry ep' p' :
  buffer_at (push p ep entry h) ep' p' =
  if decide (ep = ep' ∧ p = p')
  then (λ buf, buf ++ [entry]) <$> buffer_at h ep' p'
  else buffer_at h ep' p'.
Proof.
  exact (queue_push_lookup h p ep entry p' ep').
Qed.

Lemma queued_entry_push_iff h p ep entry ep' p' other :
  queued_entry (push p ep entry h) ep' p' other ↔
  queued_entry h ep' p' other ∨
  (ep = ep' ∧ p = p' ∧ is_Some (buffer_at h ep p) ∧ other = entry).
Proof.
  unfold queued_entry. rewrite buffer_at_push.
  destruct (decide (ep = ep' ∧ p = p')) as [[-> ->]|Hne].
  - destruct (buffer_at h ep' p') as [buf|] eqn:Hbuf; cbn.
    + unfold is_Some. split.
      * intros (xs & Hxs & Hother). injection Hxs as <-.
        apply elem_of_app in Hother as [Hother|Hother].
        -- left. now exists buf.
        -- apply elem_of_cons in Hother as [Hother|Hnil].
           ++ right. split; [reflexivity|]. split; [reflexivity|]. split; eauto.
           ++ apply elem_of_nil in Hnil. contradiction.
      * intros [(xs & Hxs & Hother)|(_ & _ & _ & ->)].
        -- injection Hxs as <-. exists (buf ++ [entry]). split; [reflexivity|].
           apply elem_of_app. now left.
        -- exists (buf ++ [entry]). split; [reflexivity|].
           apply elem_of_app. right. apply elem_of_cons. now left.
    + unfold is_Some. split.
      * intros (xs & Hbad & _). discriminate.
      * intros [(xs & Hbad & _)|(_ & _ & (xs & Hbad) & _)]; discriminate.
  - split; [now left|].
    intros [Hold|(Heq & Hp & _ & _)]; [exact Hold|].
    exfalso. exact (Hne (conj Heq Hp)).
Qed.

Lemma queue_pop_updates `{Countable Kp, Countable Kq} {A}
    (bufs : bufsT Kp Kq A) p q (a : A) bufs' :
  pop p q bufs = Some (a,bufs') →
  ∃ tail, bufs !! q ≫= lookup p = Some (a :: tail) ∧
    (∀ q', is_Some (bufs' !! q') ↔ is_Some (bufs !! q')) ∧
    (∀ p' q', bufs' !! q' ≫= lookup p' =
      if decide (q = q' ∧ p = p') then Some tail else bufs !! q' ≫= lookup p').
Proof.
  unfold pop.
  destruct (bufs !! q) as [bs|] eqn:Hbs; [|discriminate].
  destruct (bs !! p) as [[|head tail]|] eqn:Hinner; try discriminate.
  intros Hpop. inversion Hpop; subst a bufs'.
  exists tail. split; [exact Hinner|]. split.
  - intros q'.
    destruct (decide (q = q')) as [->|Hnq].
    + rewrite lookup_insert_eq, Hbs. split; intros _; eauto.
    + now rewrite lookup_insert_ne.
  - intros p' q'. destruct (decide (q = q')) as [->|Hnq].
    + rewrite lookup_insert_eq, Hbs. simpl.
      destruct (decide (p = p')) as [->|Hnp].
      * rewrite decide_True by auto. apply lookup_insert_eq.
      * rewrite decide_False by tauto. now apply lookup_insert_ne.
    + rewrite decide_False by tauto. now rewrite lookup_insert_ne.
Qed.

Lemma buffer_at_pop h p ep entry h' :
  pop p ep h = Some (entry,h') →
  ∃ tail,
    buffer_at h ep p = Some (entry :: tail) ∧
    ∀ ep' p', buffer_at h' ep' p' =
      if decide (ep = ep' ∧ p = p')
      then Some tail
      else buffer_at h ep' p'.
Proof.
  intros Hpop.
  destruct (queue_pop_updates h p ep entry h' Hpop) as (tail & Hhead & _ & Hlookup).
  exists tail. split; [exact Hhead|].
  intros ep' p'. exact (Hlookup p' ep').
Qed.

Lemma queued_entry_pop_iff h p ep entry h' ep' p' other :
  pop p ep h = Some (entry,h') →
  queued_entry h ep' p' other ↔
  queued_entry h' ep' p' other ∨ (ep = ep' ∧ p = p' ∧ other = entry).
Proof.
  intros Hpop. apply buffer_at_pop in Hpop as (tail & Hold & Hnew).
  unfold queued_entry. rewrite Hnew.
  destruct (decide (ep = ep' ∧ p = p')) as [[-> ->]|Hne].
  - rewrite Hold. split.
    + intros (xs & Hxs & Hother). injection Hxs as <-.
      apply elem_of_cons in Hother as [Hother|Hother].
      * right. auto.
      * left. now exists tail.
    + intros [(xs & Hxs & Hother)|(_ & _ & ->)].
      * injection Hxs as <-. exists (entry :: tail). split; [reflexivity|].
        apply elem_of_cons. now right.
      * exists (entry :: tail). split; [reflexivity|].
        apply elem_of_cons. now left.
  - split; [now left|].
    intros [Hold'|(Heq & Hp & _)]; [exact Hold'|].
    exfalso. exact (Hne (conj Heq Hp)).
Qed.

Lemma buffer_at_present h ep p :
  is_present p ep h ↔ is_Some (buffer_at h ep p).
Proof.
  unfold is_present, buffer_at.
  destruct ((h : gmap endpoint (gmap participant (list entryT))) !! ep) as [bs|].
  - change ((match bs !! p with Some _ => True | None => False end) ↔ is_Some (bs !! p)).
    destruct (bs !! p) as [buf|].
    + split; [intros _; now exists buf|intros _; exact I].
    + split; [contradiction|intros (buf & Hbuf); discriminate].
  - split; [contradiction|intros (buf & Hbuf); discriminate].
Qed.

Lemma heap_value_refs_push `{Countable B} (f : val → gset B) h c q p i v d x :
  x ∈ heap_value_refs f (push p (c,q) (i,v) h) d ↔
  x ∈ heap_value_refs f h d ∨
  (c = d ∧ is_present p (c,q) h ∧ x ∈ f v).
Proof.
  rewrite !elem_of_heap_value_refs_iff, buffer_at_present. split.
  - intros (q' & p' & i' & v' & Hqueued & Hx).
    apply queued_entry_push_iff in Hqueued as [Hqueued| (Hep & Hp & Hbuf & He)].
    + left. now exists q', p', i', v'.
    + injection Hep as -> ->. injection He as -> ->.
      now right.
  - intros [(q' & p' & i' & v' & Hqueued & Hx)|(-> & Hbuf & Hx)].
    + exists q', p', i', v'. split; [|exact Hx].
      apply queued_entry_push_iff. now left.
    + exists q, p, i, v. split; [|exact Hx].
      apply queued_entry_push_iff. right. auto.
Qed.

Lemma channel_references_push es h c q p i v d x :
  x ∈ obj_refs es (push p (c,q) (i,v) h) (Chan d) ↔
  x ∈ obj_refs es h (Chan d) ∨
  (c = d ∧ is_present p (c,q) h ∧ x ∈ val_refs v).
Proof.
  exact (heap_value_refs_push val_refs h c q p i v d x).
Qed.

Lemma heap_value_refs_pop `{Countable B} (f : val → gset B) h c q p i v h' d x :
  pop p (c,q) h = Some ((i,v), h') →
  x ∈ heap_value_refs f h d ↔
  x ∈ heap_value_refs f h' d ∨ (c = d ∧ x ∈ f v).
Proof.
  intros Hpop. rewrite !elem_of_heap_value_refs_iff. split.
  - intros (q' & p' & i' & v' & Hqueued & Hx).
    apply (queued_entry_pop_iff _ _ _ _ _ _ _ _ Hpop) in Hqueued
      as [Hqueued| (Hep & Hp & He)].
    + left. now exists q', p', i', v'.
    + injection Hep as -> ->. injection He as -> ->.
      now right.
  - intros [(q' & p' & i' & v' & Hqueued & Hx)|(-> & Hx)].
    + exists q', p', i', v'. split; [|exact Hx].
      eapply queued_entry_pop_iff; [exact Hpop|now left].
    + exists q, p, i, v. split; [|exact Hx].
      eapply queued_entry_pop_iff; [exact Hpop|right; auto].
Qed.

Lemma channel_references_pop es h c q p i v h' d x :
  pop p (c,q) h = Some ((i,v), h') →
  x ∈ obj_refs es h (Chan d) ↔
  x ∈ obj_refs es h' (Chan d) ∨ (c = d ∧ x ∈ val_refs v).
Proof.
  exact (heap_value_refs_pop val_refs h c q p i v h' d x).
Qed.


Lemma heap_value_refs_delete_empty_endpoint `{Countable B} (f : val → gset B) h c q d x :
  (∀ p buf, buffer_at h (c,q) p = Some buf → buf = []) →
  x ∈ heap_value_refs f (delete (c,q) (h : gmap endpoint (gmap participant (list entryT)))) d ↔
  x ∈ heap_value_refs f h d.
Proof.
  intros Hempty. rewrite !elem_of_heap_value_refs_iff.
  assert (∀ q' p entry,
    queued_entry (delete (c,q) (h : gmap endpoint (gmap participant (list entryT)))) (d,q') p entry ↔ queued_entry h (d,q') p entry)
    as Hqueued.
  {
    intros q' p entry.
    destruct (decide ((c,q) = (d,q'))) as [Heq|Hne].
    - rewrite <- Heq. split.
      + intros (buf & Hbuf & _).
        unfold buffer_at in Hbuf. rewrite lookup_delete_eq in Hbuf. discriminate.
      + intros (buf & Hbuf & Hin).
        specialize (Hempty p buf Hbuf) as ->.
        apply elem_of_nil in Hin. contradiction.
    - unfold queued_entry, buffer_at. now rewrite lookup_delete_ne.
  }
  setoid_rewrite Hqueued. reflexivity.
Qed.

Lemma channel_references_delete_empty_endpoint es h c q d x :
  (∀ p buf, buffer_at h (c,q) p = Some buf → buf = []) →
  x ∈ obj_refs es (delete (c,q) (h : gmap endpoint (gmap participant (list entryT)))) (Chan d) ↔
  x ∈ obj_refs es h (Chan d).
Proof.
  exact (heap_value_refs_delete_empty_endpoint val_refs h c q d x).
Qed.


Lemma send_transfers_references es h k c p q i π v :
  ctx k →
  is_present p (c,π q) h →
  expr_refs (k (Send q (Val (ChanV (c,p) π)) i (Val v))) ∪
    obj_refs es h (Chan c) =
  expr_refs (k (Val (ChanV (c,p) π))) ∪
    obj_refs es (push p (c,π q) (i,v) h) (Chan c).
Proof.
  intros Hctx Hpresent.
  rewrite (ctx_reference_split k (Send q (Val (ChanV (c,p) π)) i (Val v)) Hctx),
    (ctx_reference_split k (Val (ChanV (c,p) π)) Hctx).
  cbn [expr_refs val_refs].
  apply set_eq. intros x.
  rewrite !elem_of_union, channel_references_push.
  set_solver.
Qed.

Lemma receive_transfers_references es h k c p q i π v h' :
  ctx k →
  pop (π p) (c,q) h = Some ((i,v),h') →
  expr_refs (k (Recv p (Val (ChanV (c,q) π)))) ∪
    obj_refs es h (Chan c) =
  expr_refs (k (Val (InjNV i (PairV (ChanV (c,q) π) v)))) ∪
    obj_refs es h' (Chan c).
Proof.
  intros Hctx Hpop.
  rewrite (ctx_reference_split k (Recv p (Val (ChanV (c,q) π))) Hctx),
    (ctx_reference_split k (Val (InjNV i (PairV (ChanV (c,q) π) v))) Hctx).
  cbn [expr_refs val_refs].
  apply set_eq. intros x.
  rewrite !elem_of_union, (channel_references_pop es h c q (π p) i v h' c x Hpop).
  set_solver.
Qed.

Lemma lookup_numbered_list {A} (xs : list A) base i :
  list_to_mapi' xs base !! (base + i) = xs !! i.
Proof.
  revert base i.
  induction xs as [|x xs IH]; intros base i.
  - cbn [list_to_mapi']. rewrite lookup_empty, lookup_nil. reflexivity.
  - destruct i as [|i].
    + replace (base + 0) with base by lia. simpl list_to_mapi'.
      rewrite lookup_insert_eq. reflexivity.
    + simpl list_to_mapi'. rewrite lookup_insert_ne by lia.
      replace (base + S i) with (S base + i) by lia. apply IH.
Qed.

Lemma lookup_finite_map {A} n (f : fin n → A) i :
  fin_gmap n f !! i = fin_list n f !! i.
Proof. exact (lookup_numbered_list (fin_list n f) 0 i). Qed.

Lemma finite_list_constant {A} n (x : A) :
  fin_list n (λ _, x) = replicate n x.
Proof.
  induction n as [|n IH]; [reflexivity|].
  change (x :: fin_list n (λ _, x) = x :: replicate n x).
  now rewrite IH.
Qed.

Lemma lookup_finite_constant {A} n (x : A) i y :
  fin_gmap n (λ _, x) !! i = Some y ↔ y = x ∧ i < n.
Proof. now rewrite lookup_finite_map, finite_list_constant, lookup_replicate. Qed.

Lemma lookup_gmap_unslice_some {A} (m : gmap participant A) (c d : session) q v :
  gmap_unslice m c !! (d,q) = Some v ↔ d = c ∧ m !! q = Some v.
Proof.
  unfold gmap_unslice, map_kmap.
  assert (NoDup ((prod_map (λ p : participant, (c,p)) id <$> map_to_list m).*1))
    as Hkeys.
  {
    assert ((prod_map (λ p : participant, (c,p)) id <$> map_to_list m).*1 =
      (λ p, (c,p)) <$> (map_to_list m).*1) as Hkey_map.
    { rewrite <- !list_fmap_compose. reflexivity. }
    rewrite Hkey_map.
    apply NoDup_fmap_2; [intros p q' Heq; now injection Heq|].
    apply NoDup_fst_map_to_list.
  }
  rewrite <- elem_of_list_to_map by exact Hkeys.
  rewrite list_elem_of_fmap.
  split.
  - intros ([p v'] & Heq & Hp). simpl in Heq.
    inversion Heq; subst. split; [reflexivity|].
    now apply elem_of_map_to_list.
  - intros (-> & Hlookup).
    exists (q,v). split; [reflexivity|].
    now apply elem_of_map_to_list.
Qed.

Lemma init_chans_empty_queue n q p (bs : gmap participant (list entryT)) buf :
  init_chans n !! q = Some bs →
  bs !! p = Some buf →
  buf = [].
Proof.
  unfold init_chans. intros Hbs Hp.
  apply lookup_finite_constant in Hbs as [-> _].
  now apply lookup_finite_constant in Hp as [-> _].
Qed.

Lemma allocation_preserves_queued_entries (h : heap) c n d q p entry :
  (∀ p, (h : gmap endpoint (gmap participant (list entryT))) !! (c,p) = None) →
  queued_entry (gmap_unslice (init_chans n) c ∪ h) (d,q) p entry ↔
  queued_entry h (d,q) p entry.
Proof.
  intros Hfresh.
  set (new := gmap_unslice (init_chans n : bufsT participant participant entryT) c).
  unfold queued_entry, buffer_at.
  change ((∃ buf, ((new ∪ (h : gmap endpoint (gmap participant (list entryT)))) !!
      (d,q) ≫= lookup p) = Some buf ∧ entry ∈ buf) ↔
    (∃ buf, ((h : gmap endpoint (gmap participant (list entryT))) !!
      (d,q) ≫= lookup p) = Some buf ∧ entry ∈ buf)).
  rewrite lookup_union.
  destruct (new !! (d,q)) as [bs|] eqn:Hnew.
  - unfold new in Hnew. apply lookup_gmap_unslice_some in Hnew as [-> Hbs].
    rewrite Hfresh. simpl.
    split.
    + intros (buf & Hbuf & Hin).
      apply (init_chans_empty_queue n q p bs buf Hbs) in Hbuf. subst buf.
      apply elem_of_nil in Hin. contradiction.
    + intros (buf & Hbad & _).
      change (((h : gmap endpoint (gmap participant (list entryT))) !!
        ((c,q) : endpoint)) ≫= lookup p = Some buf) in Hbad.
      assert ((h : gmap endpoint (gmap participant (list entryT))) !!
        ((c,q) : endpoint) = None) as Hnone by apply Hfresh.
      rewrite Hnone in Hbad. discriminate.
  - now rewrite option_union_left_id.
Qed.

Lemma allocation_preserves_heap_references es (h : heap) c n d x :
  (∀ p, (h : gmap endpoint (gmap participant (list entryT))) !! (c,p) = None) →
  x ∈ obj_refs es (gmap_unslice (init_chans n) c ∪ h) (Chan d) ↔
  x ∈ obj_refs es h (Chan d).
Proof.
  intros Hfresh. rewrite !elem_of_channel_references_iff.
  setoid_rewrite (allocation_preserves_queued_entries h c n d _ _ _ Hfresh).
  reflexivity.
Qed.


Lemma fin_list_lookup_at_index {A} n (f : fin n → A) p :
  fin_list n f !! fin_to_nat p = Some (f p).
Proof.
  revert f p.
  induction n as [|n IH]; intros f p.
  - exact (fin_0_inv (λ p, fin_list 0 f !! fin_to_nat p = Some (f p)) p).
  - refine (fin_S_inv (λ p, fin_list (S n) f !! fin_to_nat p = Some (f p)) _ _ p).
    + reflexivity.
    + intros q. change (fin_list n (f ∘ FS) !! fin_to_nat q = Some ((f ∘ FS) q)).
      apply IH.
Qed.

Lemma allocated_worker_lookup es c n fv (p : fin n) :
  (es ++ init_threads c n fv) !! (length es + fin_to_nat p) =
  Some (App (Val (fv p)) (Val (ChanV (c,S (fin_to_nat p)) id))).
Proof.
  rewrite lookup_app_r by lia.
  replace (length es + fin_to_nat p - length es) with (fin_to_nat p) by lia.
  unfold init_threads. now rewrite fin_list_lookup_at_index.
Qed.

Lemma allocated_worker_references es h c n fv (p : fin n) :
  obj_refs (es ++ init_threads c n fv) h (Thread (length es + fin_to_nat p)) =
  val_refs (fv p) ∪ {[Chan c]}.
Proof.
  unfold obj_refs. rewrite allocated_worker_lookup. reflexivity.
Qed.

Lemma allocated_worker_can_step es h c n fv (p : fin n) x body :
  fv p = FunV x body →
  can_stepi (length es + fin_to_nat p) (es ++ init_threads c n fv) h.
Proof.
  intros Hfun.
  eexists _, _. eapply Head_step.
  - eapply (Ctx_step (λ e, e)); [exact Ctx_nil|].
    apply Pure_step, App_step.
  - rewrite allocated_worker_lookup, Hfun. reflexivity.
Qed.

Lemma allocated_channel_reachable_from_worker es h c n fv (p : fin n) x body :
  fv p = FunV x body →
  reachable (es ++ init_threads c n fv) h (Chan c).
Proof.
  intros Hfun.
  apply (Chan_ref_reachable _ _ c (Thread (length es + fin_to_nat p))).
  - rewrite allocated_worker_references. set_solver.
  - apply Thread_step_reachable. exact (allocated_worker_can_step es h c n fv p x body Hfun).
Qed.

Definition thread_list_refs (ts : list expr) : gset object :=
  foldr (λ e refs, expr_refs e ∪ refs) ∅ ts.

Lemma elem_of_thread_list_refs_iff ts x :
  x ∈ thread_list_refs ts ↔ ∃ e, e ∈ ts ∧ x ∈ expr_refs e.
Proof.
  induction ts as [|e ts IH]; cbn [thread_list_refs foldr].
  - rewrite elem_of_empty. split; [contradiction|].
    intros (e & Hnil & _). now apply elem_of_nil in Hnil.
  - rewrite elem_of_union, IH. split.
    + intros [He|(e' & Hts & Hrefs)].
      * exists e. split; [apply elem_of_cons; now left|exact He].
      * exists e'. split; [apply elem_of_cons; now right|exact Hrefs].
    + intros (e' & Hts & Hrefs).
      apply elem_of_cons in Hts as [->|Hts]; [now left|].
      right. now exists e'.
Qed.

Lemma init_threads_reference_membership c n fv x :
  x ∈ thread_list_refs (init_threads c n fv) ↔
  ∃ p, x ∈ val_refs (fv p) ∨ x = Chan c.
Proof.
  rewrite elem_of_thread_list_refs_iff. unfold init_threads.
  split.
  - intros (e & He & Hrefs). apply elem_of_fin_list_iff in He as (p & ->).
    exists p. cbn [expr_refs val_refs] in Hrefs. set_solver.
  - intros (p & Hrefs).
    exists (App (Val (fv p)) (Val (ChanV (c,S (fin_to_nat p)) id))).
    split.
    + apply elem_of_fin_list_iff. now exists p.
    + cbn [expr_refs val_refs]. set_solver.
Qed.

Lemma spawn_transfers_worker_references k c n f fv :
  ctx k →
  (∀ p, f p = Val (fv p)) →
  expr_refs (k (Val (ChanV (c,0) id))) ∪ thread_list_refs (init_threads c n fv) =
  expr_refs (k (Spawn n f)) ∪ {[Chan c]}.
Proof.
  intros Hctx Hworkers.
  rewrite (ctx_reference_split k (Val (ChanV (c,0) id)) Hctx),
    (ctx_reference_split k (Spawn n f) Hctx).
  cbn [expr_refs val_refs].
  assert (∀ x, x ∈ fin_union n (expr_refs ∘ f) ↔ ∃ p, x ∈ val_refs (fv p))
    as Hwork.
  {
    intros x. rewrite elem_of_fin_union_iff.
    split; intros (p & Hp); exists p; cbn [compose] in *.
    - now rewrite Hworkers in Hp.
    - now rewrite Hworkers.
  }
  apply set_eq. intros x.
  rewrite !elem_of_union, !elem_of_singleton, init_threads_reference_membership, Hwork.
  split.
  - intros [[Hc|Hctxref]|(p & [Hval|Hc])].
    + now right.
    + left. now right.
    + left. left. now exists p.
    + now right.
  - intros [[(p & Hval)|Hctxref]|Hc].
    + right. exists p. now left.
    + left. now right.
    + left. now left.
Qed.

Lemma pop_queue_head_iff `{Countable Kp, Countable Kq} {A}
    (bufs : bufsT Kp Kq A) p q a :
  (∃ bufs', pop p q bufs = Some (a,bufs')) ↔
  (∃ tail, bufs !! q ≫= lookup p = Some (a :: tail)).
Proof.
  unfold pop.
  destruct (bufs !! q) as [bs|]; simpl.
  - destruct (bs !! p) as [[|head tail]|]; split; intros (out & Hout);
      try discriminate; inversion Hout; subst; eauto.
  - split; intros (out & Hout); discriminate.
Qed.

Definition typed_buffer_at (bufs : sbufsT) (q p : participant) : option (list sentryT) :=
  (bufs : gmap participant (gmap participant (list sentryT))) !! q ≫= lookup p.

Definition queued_entry_typed (value_typed : val → type → Prop)
    (entry : entryT) (type_entry : sentryT) : Prop :=
  entry.1 = type_entry.1 ∧ value_typed entry.2 type_entry.2.

Record session_queues_typed (value_typed : val → type → Prop)
    (h : heap) (c : session) (bufs : sbufsT) : Prop := {
  session_queues_domain q :
    is_Some ((bufs : gmap participant (gmap participant (list sentryT))) !! q) ↔
    is_Some ((h : gmap endpoint (gmap participant (list entryT))) !! (c,q));
  session_queues_contents q p :
    option_Forall2 (Forall2 (queued_entry_typed value_typed))
      (buffer_at h (c,q) p) (typed_buffer_at bufs q p)
}.

Lemma typed_buffer_matching_concrete value_typed h c bufs q p entries :
  session_queues_typed value_typed h c bufs →
  buffer_at h (c,q) p = Some entries →
  ∃ tags, typed_buffer_at bufs q p = Some tags ∧
    Forall2 (queued_entry_typed value_typed) entries tags.
Proof.
  intros Htyped Hentry.
  pose proof (session_queues_contents _ _ _ _ Htyped q p) as Hqueues.
  rewrite Hentry in Hqueues. inversion Hqueues; subst. eauto.
Qed.

Lemma concrete_buffer_matching_typed value_typed h c bufs q p tags :
  session_queues_typed value_typed h c bufs →
  typed_buffer_at bufs q p = Some tags →
  ∃ entries, buffer_at h (c,q) p = Some entries ∧
    Forall2 (queued_entry_typed value_typed) entries tags.
Proof.
  intros Htyped Htag.
  pose proof (session_queues_contents _ _ _ _ Htyped q p) as Hqueues.
  rewrite Htag in Hqueues. inversion Hqueues; subst. eauto.
Qed.

Lemma abstract_pop_has_concrete_match value_typed h c bufs p q i t bufs' :
  session_queues_typed value_typed h c bufs →
  pop p q bufs = Some ((i,t),bufs') →
  ∃ v h', pop p (c,q) h = Some ((i,v),h') ∧ value_typed v t.
Proof.
  intros Htyped Hpop.
  assert (∃ tags, typed_buffer_at bufs q p = Some ((i,t) :: tags)) as Hhead.
  { apply (proj1 (pop_queue_head_iff bufs p q (i,t))). now exists bufs'. }
  destruct Hhead as (tags & Hhead).
  destruct (concrete_buffer_matching_typed _ _ _ _ _ _ _ Htyped Hhead)
    as (entries & Hentries & Hmatch).
  apply Forall2_cons_inv_r in Hmatch as ([j v] & tail & [Hlabel Hv] & _ & ->).
  simpl in Hlabel. subst j.
  assert (∃ h', pop p (c,q) h = Some ((i,v),h')) as Hreal.
  { apply (proj2 (pop_queue_head_iff h p (c,q) (i,v))). now exists tail. }
  destruct Hreal as (h' & Hreal). now exists v, h'.
Qed.

Lemma concrete_pop_has_abstract_match value_typed h c bufs p q i v h' :
  session_queues_typed value_typed h c bufs →
  pop p (c,q) h = Some ((i,v),h') →
  ∃ t bufs', pop p q bufs = Some ((i,t),bufs') ∧ value_typed v t.
Proof.
  intros Htyped Hpop.
  assert (∃ entries, buffer_at h (c,q) p = Some ((i,v) :: entries)) as Hhead.
  { apply (proj1 (pop_queue_head_iff h p (c,q) (i,v))). now exists h'. }
  destruct Hhead as (entries & Hhead).
  destruct (typed_buffer_matching_concrete _ _ _ _ _ _ _ Htyped Hhead)
    as (tags & Htags & Hmatch).
  apply Forall2_cons_inv_l in Hmatch as ([j t] & tail & [Hlabel Hv] & _ & ->).
  simpl in Hlabel. subst j.
  assert (∃ bufs', pop p q bufs = Some ((i,t),bufs')) as Habstract.
  { apply (proj2 (pop_queue_head_iff bufs p q (i,t))). now exists tail. }
  destruct Habstract as (bufs' & Habstract). now exists t, bufs'.
Qed.

Lemma typed_queues_allow_receive value_typed h c bufs σs p q i v h'
    n (ts : fin n → type) rs :
  session_queues_typed value_typed h c bufs →
  sbufs_typed bufs σs →
  σs !! q = Some (RecvT n p ts rs) →
  pop p (c,q) h = Some ((i,v),h') →
  ∃ (j : fin n) bufs',
    pop p q bufs = Some ((i,ts j),bufs') ∧
    i = fin_to_nat j ∧ value_typed v (ts j) ∧
    sbufs_typed bufs' (<[q := rs j]> σs).
Proof.
  intros Htyped Hsafe Hsession Hpop.
  destruct (concrete_pop_has_abstract_match _ _ _ _ _ _ _ _ _ Htyped Hpop)
    as (t & bufs' & Habstract & Hv).
  destruct (sbufs_typed_recv _ _ Hsafe bufs' n p q t i ts rs Hsession Habstract)
    as (j & Hi & Ht & Hsafe').
  subst t. eauto 8.
Qed.

Lemma typed_queues_close_empty value_typed h c bufs σs q :
  session_queues_typed value_typed h c bufs →
  sbufs_typed bufs σs →
  σs !! q = Some EndT →
  ∀ p entries, buffer_at h (c,q) p = Some entries → entries = [].
Proof.
  intros Htyped Hsafe Hsession p entries Hentries.
  destruct (sbufs_typed_end _ _ Hsafe q Hsession) as [Hempty _].
  destruct (typed_buffer_matching_concrete _ _ _ _ _ _ _ Htyped Hentries)
    as (tags & Htags & Hmatch).
  unfold typed_buffer_at in Htags.
  destruct ((bufs : gmap participant (gmap participant (list sentryT))) !! q)
    as [bs|] eqn:Hlook; [|discriminate].
  assert (tags = []) as -> by (eapply Hempty; [exact Hlook|exact Htags]).
  now apply Forall2_nil_inv_r in Hmatch.
Qed.

Definition ready_session_action (h : heap) (c : session) (q : participant)
    (σ : session_type) : Prop :=
  match σ with
  | RecvT _ p _ _ => ∃ entry h', pop p (c,q) h = Some (entry,h')
  | _ => True
  end.

Lemma active_session_has_ready_endpoint es h c value_typed bufs σs :
  active es h (Chan c) →
  session_queues_typed value_typed h c bufs →
  sbufs_typed bufs σs →
  ∃ q σ, σs !! q = Some σ ∧ is_Some (h !! (c,q)) ∧ ready_session_action h c q σ.
Proof.
  intros (p & Hp) Htyped Hsafe.
  destruct (sbufs_typed_progress _ _ Hsafe) as [Hempty|(q & σ & Hσ & Hready)].
  - assert (is_Some ((bufs : gmap participant (gmap participant (list sentryT))) !! p))
      as (bs & Hbs).
    { apply (proj2 (session_queues_domain _ _ _ _ Htyped p)). exact Hp. }
    rewrite Hempty, lookup_empty in Hbs. discriminate.
  - exists q, σ. split; [exact Hσ|]. split.
    + apply (proj1 (session_queues_domain _ _ _ _ Htyped q)).
      apply elem_of_dom.
      rewrite (sbufs_typed_dom _ _ Hsafe).
      apply elem_of_dom. now exists σ.
    + destruct σ; cbn [ready_session_action] in *; try exact I.
      destruct Hready as ([i τ] & bufs' & Hpop).
      destruct (abstract_pop_has_concrete_match _ _ _ _ _ _ _ _ _ Htyped Hpop)
        as (v & h' & Hreal & _).
      now exists (i,v), h'.
Qed.


Lemma queue_push_endpoint_present `{Countable Kp, Countable Kq} {A}
    (bufs : bufsT Kp Kq A) p q (a : A) q' :
  is_Some (push p q a bufs !! q') ↔ is_Some (bufs !! q').
Proof.
  unfold push.
  destruct (decide (q = q')) as [->|Hne].
  - rewrite lookup_alter_eq. destruct (bufs !! q'); simpl; naive_solver.
  - now rewrite lookup_alter_ne.
Qed.

Lemma session_queues_push_matched value_typed h c bufs p q i v t :
  session_queues_typed value_typed h c bufs →
  value_typed v t →
  session_queues_typed value_typed (push p (c,q) (i,v) h) c (push p q (i,t) bufs).
Proof.
  intros Htyped Hv. constructor.
  - intros r.
    rewrite (queue_push_endpoint_present bufs p q (i,t) r),
      (queue_push_endpoint_present h p (c,q) (i,v) (c,r)).
    exact (session_queues_domain _ _ _ _ Htyped r).
  - intros r s.
    assert (typed_buffer_at (push p q (i,t) bufs) r s =
      if decide (q = r ∧ p = s)
      then (λ entries, entries ++ [(i,t)]) <$> typed_buffer_at bufs r s
      else typed_buffer_at bufs r s) as Habstract.
    { exact (queue_push_lookup bufs p q (i,t) s r). }
    rewrite Habstract, buffer_at_push.
    destruct (decide (q = r ∧ p = s)) as [[-> ->]|Hne].
    + rewrite !decide_True by auto.
      pose proof (session_queues_contents _ _ _ _ Htyped r s) as Hcontents.
      destruct Hcontents as [xs ts Hmatch|]; cbn [fmap]; constructor.
      apply Forall2_app; [exact Hmatch|].
      constructor; [split; [reflexivity|exact Hv]|constructor].
    + rewrite decide_False by (intros [Heq Hp]; apply Hne; split; [congruence|exact Hp]).
      exact (session_queues_contents _ _ _ _ Htyped r s).
Qed.

Lemma session_queues_pop_matched value_typed h c bufs p q i v t h' bufs' :
  session_queues_typed value_typed h c bufs →
  pop p (c,q) h = Some ((i,v),h') →
  pop p q bufs = Some ((i,t),bufs') →
  session_queues_typed value_typed h' c bufs'.
Proof.
  intros Htyped Hpop HpopT.
  destruct (queue_pop_updates (h : gmap endpoint (gmap participant (list entryT)))
    p (c,q) (i,v) h' Hpop) as (xs & Hxs & Hdom & Hlookup).
  destruct (queue_pop_updates (bufs : gmap participant (gmap participant (list sentryT)))
    p q (i,t) bufs' HpopT)
    as (ts & Hts & HdomT & HlookupT).
  constructor.
  - intros r. rewrite (Hdom (c,r)), (HdomT r).
    exact (session_queues_domain _ _ _ _ Htyped r).
  - intros r s.
    pose proof (Hlookup s (c,r)) as Hreal.
    change (buffer_at h' (c,r) s =
      if decide ((c,q) = (c,r) ∧ p = s) then Some xs else buffer_at h (c,r) s)
      in Hreal.
    pose proof (HlookupT s r) as Habstract.
    change (typed_buffer_at bufs' r s =
      if decide (q = r ∧ p = s) then Some ts else typed_buffer_at bufs r s)
      in Habstract.
    rewrite Hreal, Habstract.
    destruct (decide (q = r ∧ p = s)) as [[-> ->]|Hne].
    + rewrite decide_True by auto.
      pose proof (session_queues_contents _ _ _ _ Htyped r s) as Hcontents.
      change (buffer_at h (c,r) s = Some ((i,v) :: xs)) in Hxs.
      change (typed_buffer_at bufs r s = Some ((i,t) :: ts)) in Hts.
      rewrite Hxs, Hts in Hcontents.
      inversion Hcontents as [a b Hmatch|]; subst a b.
      apply Forall2_cons in Hmatch as [_ Htail].
      now constructor.
    + rewrite decide_False by (intros [Heq Hp]; apply Hne; split; [congruence|exact Hp]).
      exact (session_queues_contents _ _ _ _ Htyped r s).
Qed.


Lemma typed_queues_allow_send value_typed h c bufs σs n p q ts rs (j : fin n) v :
  session_queues_typed value_typed h c bufs →
  sbufs_typed bufs σs →
  σs !! p = Some (SendT n q ts rs) →
  value_typed v (ts j) →
  is_present p (c,q) h ∧
  session_queues_typed value_typed (push p (c,q) (fin_to_nat j,v) h) c
    (push p q (fin_to_nat j,ts j) bufs) ∧
  sbufs_typed (push p q (fin_to_nat j,ts j) bufs) (<[p := rs j]> σs).
Proof.
  intros Htyped Hsafe Hσ Hv.
  destruct (sbufs_typed_send _ _ Hsafe n p q ts rs j Hσ) as [Hpresent Hsafe'].
  split; [|split; [now apply session_queues_push_matched|exact Hsafe']].
  apply buffer_at_present. unfold is_present in Hpresent.
  destruct ((bufs : gmap participant (gmap participant (list sentryT))) !! q)
    as [bs|] eqn:Hbs; [|contradiction].
  destruct (bs !! p) as [tags|] eqn:Htags; [|contradiction].
  assert (typed_buffer_at bufs q p = Some tags) as Hlook.
  { unfold typed_buffer_at. now rewrite Hbs. }
  destruct (concrete_buffer_matching_typed _ _ _ _ _ _ _ Htyped Hlook)
    as (entries & Hentries & _).
  now exists entries.
Qed.

Lemma typed_queues_receive_updates value_typed h c bufs σs p q i v h'
    n (ts : fin n → type) rs :
  session_queues_typed value_typed h c bufs →
  sbufs_typed bufs σs →
  σs !! q = Some (RecvT n p ts rs) →
  pop p (c,q) h = Some ((i,v),h') →
  ∃ (j : fin n) bufs',
    i = fin_to_nat j ∧ value_typed v (ts j) ∧
    session_queues_typed value_typed h' c bufs' ∧
    sbufs_typed bufs' (<[q := rs j]> σs).
Proof.
  intros Htyped Hsafe Hσ Hpop.
  destruct (typed_queues_allow_receive _ _ _ _ _ _ _ _ _ _ _ _ _ Htyped Hsafe Hσ Hpop)
    as (j & bufs' & Habstract & Hj & Hv & Hsafe').
  exists j, bufs'. split; [exact Hj|]. split; [exact Hv|].
  split; [|exact Hsafe'].
  exact (session_queues_pop_matched value_typed h c bufs p q i v (ts j)
    h' bufs' Htyped Hpop Habstract).
Qed.

Lemma session_queues_delete_matched value_typed (h : heap) c bufs q :
  session_queues_typed value_typed h c bufs →
  session_queues_typed value_typed
    (delete ((c,q) : endpoint) (h : gmap endpoint (gmap participant (list entryT)))) c
    (delete q (bufs : gmap participant (gmap participant (list sentryT)))).
Proof.
  intros Htyped. constructor.
  - intros r. destruct (decide (q = r)) as [->|Hne].
    + rewrite !lookup_delete_eq. split; intros (bs & Hbs); discriminate.
    + rewrite !lookup_delete_ne by congruence.
      exact (session_queues_domain _ _ _ _ Htyped r).
  - intros r s. unfold buffer_at, typed_buffer_at.
    destruct (decide (q = r)) as [->|Hne].
    + rewrite !lookup_delete_eq. constructor.
    + rewrite !lookup_delete_ne by congruence.
      exact (session_queues_contents _ _ _ _ Htyped r s).
Qed.

Lemma session_queues_preserved_outside_endpoint_updates value_typed (h h' : heap) c bufs :
  session_queues_typed value_typed h c bufs →
  (∀ q, (h : gmap endpoint (gmap participant (list entryT))) !! (c,q) =
        (h' : gmap endpoint (gmap participant (list entryT))) !! (c,q)) →
  session_queues_typed value_typed h' c bufs.
Proof.
  intros Htyped Hlook. constructor.
  - intros q. rewrite <- Hlook. exact (session_queues_domain _ _ _ _ Htyped q).
  - intros q p. unfold buffer_at. rewrite <- Hlook.
    exact (session_queues_contents _ _ _ _ Htyped q p).
Qed.


Lemma lookup_finite_constant_option {A} n (x : A) i :
  fin_gmap n (λ _, x) !! i = if decide (i < n) then Some x else None.
Proof.
  destruct (decide (i < n)) as [Hi|Hi].
  - apply lookup_finite_constant. now split.
  - destruct (fin_gmap n (λ _, x) !! i) as [v|] eqn:Hlook; [|reflexivity].
    apply lookup_finite_constant in Hlook as [_ Hlt]. contradiction.
Qed.

Lemma allocated_session_endpoint_lookup (h : heap) c n q :
  (∀ r, (h : gmap endpoint (gmap participant (list entryT))) !! (c,r) = None) →
  (gmap_unslice (init_chans n : bufsT participant participant entryT) c ∪
    (h : gmap endpoint (gmap participant (list entryT)))) !! ((c,q) : endpoint) =
  (init_chans n : bufsT participant participant entryT) !! q.
Proof.
  intros Hfresh.
  assert ((h : gmap endpoint (gmap participant (list entryT))) !!
      ((c,q) : endpoint) = None) as Hnone by apply Hfresh.
  set (new := gmap_unslice (init_chans n : bufsT participant participant entryT) c).
  transitivity (new !! ((c,q) : endpoint) ∪
    (h : gmap endpoint (gmap participant (list entryT))) !! ((c,q) : endpoint)).
  { apply lookup_union. }
  rewrite Hnone.
  destruct (new !! ((c,q) : endpoint)) as [bs|] eqn:Halloc.
  - unfold new in Halloc.
    apply lookup_gmap_unslice_some in Halloc as [_ Halloc].
    exact (eq_sym Halloc).
  - destruct ((init_chans n : bufsT participant participant entryT) !! q)
      as [bs|] eqn:Hinit; [|reflexivity].
    assert (gmap_unslice (init_chans n : bufsT participant participant entryT) c !!
      ((c,q) : endpoint) = Some bs) as Hbad.
    { apply lookup_gmap_unslice_some. now split. }
    unfold new in Halloc. congruence.
Qed.

Lemma initialized_session_queues_typed value_typed (h : heap) c n :
  (∀ q, (h : gmap endpoint (gmap participant (list entryT))) !! (c,q) = None) →
  session_queues_typed value_typed
    (gmap_unslice (init_chans n : bufsT participant participant entryT) c ∪
      (h : gmap endpoint (gmap participant (list entryT)))) c
    (init_chans n).
Proof.
  intros Hfresh.
  pose proof (λ q, allocated_session_endpoint_lookup h c n q Hfresh) as Halloc.
  constructor.
  - intros q.
    change (is_Some ((init_chans n : bufsT participant participant sentryT) !! q) ↔
      is_Some ((gmap_unslice (init_chans n : bufsT participant participant entryT) c ∪
        (h : gmap endpoint (gmap participant (list entryT)))) !! ((c,q) : endpoint))).
    rewrite (Halloc q).
    change (is_Some (fin_gmap n (λ _, fin_gmap n (λ _, [] : list sentryT)) !! q) ↔
      is_Some (fin_gmap n (λ _, fin_gmap n (λ _, [] : list entryT)) !! q)).
    rewrite !lookup_finite_constant_option.
    destruct (decide (q < n)); split; intros [bs Hbs]; try discriminate; eauto.
  - intros q p.
    assert (buffer_at
      (gmap_unslice (init_chans n : bufsT participant participant entryT) c ∪
        (h : gmap endpoint (gmap participant (list entryT)))) (c,q) p =
      (init_chans n : bufsT participant participant entryT) !! q ≫= lookup p) as Hbuffer.
    { exact (f_equal (λ bs, bs ≫= lookup p) (Halloc q)). }
    rewrite Hbuffer. unfold typed_buffer_at.
    change (option_Forall2 (Forall2 (queued_entry_typed value_typed))
      (fin_gmap n (λ _, fin_gmap n (λ _, [] : list entryT)) !! q ≫= lookup p)
      (fin_gmap n (λ _, fin_gmap n (λ _, [] : list sentryT)) !! q ≫= lookup p)).
    rewrite !lookup_finite_constant_option.
    destruct (decide (q < n)); [|constructor].
    change (option_Forall2 (Forall2 (queued_entry_typed value_typed))
      (fin_gmap n (λ _, [] : list entryT) !! p)
      (fin_gmap n (λ _, [] : list sentryT) !! p)).
    rewrite !lookup_finite_constant_option.
    destruct (decide (p < n)); constructor; constructor.
Qed.

Lemma channel_reference_has_active_owner es h x c :
  Chan c ∈ obj_refs es h x → active es h x.
Proof.
  destruct x as [i|d].
  - unfold obj_refs, active.
    destruct (es !! i) as [e|] eqn:Hlookup; intros Href; cbn [from_option] in Href.
    + exists e. split; [reflexivity|].
      intros ->. simpl in Href. set_solver.
    + set_solver.
  - intros Href.
    assert (gmap_slice h d ≠ ∅) as Hslice.
    { intros Hempty. unfold obj_refs in Href. rewrite Hempty in Href.
      unfold bufs_refs, map_union in Href. rewrite map_fold_empty in Href. set_solver. }
    destruct (map_choose (gmap_slice h d) Hslice) as (p & b & Hp).
    exists p, b.
    change ((h : gmap (session * participant) (gmap participant (list entryT))) !!
      (d,p) = Some b).
    unfold gmap_slice in Hp.
    assert (∀ r : option (gmap participant (gmap participant (list entryT))),
      default ∅ r !! p = r ≫= lookup p) as Hdefault.
    { intros [bs|]; [reflexivity|apply lookup_empty]. }
    rewrite Hdefault in Hp.
    pose proof (lookup_map_curry (h : gmap (session * participant)
      (gmap participant (list entryT))) d p) as Hlookup.
    rewrite <- Hlookup. exact Hp.
Qed.

Definition state_objects (es : list expr) (h : heap) : gset object :=
  list_to_set (Thread <$> seq 0 (length es)) ∪
  set_map (λ ep : endpoint, Chan (fst ep)) (dom h : gset endpoint).

Lemma active_in_state_objects es h x :
  active es h x → x ∈ state_objects es h.
Proof.
  destruct x as [i|c]; simpl.
  - intros (e & Hlookup & _).
    unfold state_objects. apply elem_of_union_l, elem_of_list_to_set.
    apply list_elem_of_fmap_2.
    apply elem_of_seq. split; [lia|].
    apply lookup_lt_is_Some. now exists e.
  - intros (p & Hlookup).
    unfold state_objects. apply elem_of_union_r, elem_of_map.
    exists (c,p). split; [reflexivity|].
    change ((c,p) ∈ dom (h : gmap endpoint (gmap participant (list entryT)))).
    apply elem_of_dom. exact Hlookup.
Qed.

Lemma finite_predecessors_acyclic_wf (R : object → object → Prop) (V : gset object) :
  (∀ x y, R x y → x ∈ V) →
  (∀ x, ¬ tc R x x) →
  well_founded R.
Proof.
  intros Hcarrier Hacyclic.
  assert (∀ W : gset object, ∀ x,
    (∀ y, tc R y x → y ∈ W) → Acc R x) as Haccessible.
  {
    refine (@well_founded_ind (gset object) (strict subseteq) set_wf
      (λ W, ∀ x, (∀ y, tc R y x → y ∈ W) → Acc R x) _).
    intros W IH x Hpredecessors.
    constructor. intros y Hy.
    assert (y ∈ W) as HyW by (apply Hpredecessors, tc_once, Hy).
    apply (IH (W ∖ {[y]})).
    - split; set_solver.
    - intros z Hz. apply elem_of_difference. split.
      + apply Hpredecessors. eapply tc_r; eauto.
      + intros Hzy. apply elem_of_singleton in Hzy. subst z.
        exact (Hacyclic y Hz).
  }
  intros x. apply (Haccessible V).
  intros y Hy. destruct Hy; eauto.
Qed.

Inductive reachability_dependency es h : object → object → Prop :=
  | Dependency_wait i c :
      thread_blocked es h i c → reachability_dependency es h (Chan c) (Thread i)
  | Dependency_reference x c :
      Chan c ∈ obj_refs es h x → reachability_dependency es h x (Chan c).

Lemma dependency_has_active_source es h x y :
  reachability_dependency es h x y → active es h x.
Proof.
  intros Hdependency. destruct Hdependency as [i c Hblocked|x c Hreference].
  - exact (proj2 (blocked_thread_and_channel_active _ _ _ _ Hblocked)).
  - eapply channel_reference_has_active_owner. exact Hreference.
Qed.

Lemma full_reachability_from_acyclic_dependencies es h (R : object → object → Prop) :
  (∀ x, ¬ tc R x x) →
  (∀ x y, R x y → reachability_dependency es h x y) →
  (∀ x, active es h x →
    (∃ i, x = Thread i ∧ can_stepi i es h) ∨ (∃ y, R y x)) →
  fully_reachable es h.
Proof.
  intros Hacyclic Hedges Hprogress.
  assert (well_founded R) as Hwf.
  { eapply (finite_predecessors_acyclic_wf R (state_objects es h)).
    - intros x y Hxy. apply active_in_state_objects.
      eapply dependency_has_active_source. exact (Hedges x y Hxy).
    - exact Hacyclic. }
  intros x. induction (Hwf x) as [x Hpred IH]. intros Hactive.
  destruct (Hprogress x Hactive) as [(i & -> & Hstep)|(y & Hy)].
  - apply Thread_step_reachable. exact Hstep.
  - pose proof (Hedges y x Hy) as Hdep.
    pose proof (IH y Hy (dependency_has_active_source _ _ _ _ Hdep)) as Hreach.
    destruct Hdep; eauto using Thread_blocked_reachable, Chan_ref_reachable.
Qed.

(* The labels distinguish endpoints that connect the same objects. *)
Definition ownership_edge (owns : object → endpoint → Prop)
    (ep : endpoint) (x y : object) : Prop :=
  (y = Chan (fst ep) ∧ owns x ep) ∨ (x = Chan (fst ep) ∧ owns y ep).

Inductive nonbacktracking_ownership_walk (edge : endpoint → object → object → Prop) :
    object → endpoint → object → Prop :=
  | Ownership_walk_single ep x y :
      edge ep x y → nonbacktracking_ownership_walk edge x ep y
  | Ownership_walk_extend ep next x y z :
      edge ep x y → ep ≠ next → nonbacktracking_ownership_walk edge y next z →
      nonbacktracking_ownership_walk edge x ep z.

Lemma dependency_walk_is_nonbacktracking (edge directed : endpoint → object → object → Prop) :
  (∀ ep x y, directed ep x y → edge ep x y) →
  (∀ ep x y z, directed ep x y → directed ep y z → False) →
  ∀ x y, tc (λ x y, ∃ ep, directed ep x y) x y →
    ∃ ep next, directed ep x next ∧ nonbacktracking_ownership_walk edge x ep y.
Proof.
  intros Hsub Hno_repeat x y Hpath.
  induction Hpath as [x y [ep Hxy]|x y z [ep Hxy] Hpath IH].
  - exists ep, y. split; [exact Hxy|].
    apply Ownership_walk_single. now apply Hsub.
  - destruct IH as (next & v & Hyv & Hwalk).
    exists ep, y. split; [exact Hxy|].
    eapply (Ownership_walk_extend edge ep next x y z).
    + now apply Hsub.
    + intros ->. exact (Hno_repeat _ _ _ _ Hxy Hyv).
    + exact Hwalk.
Qed.

Inductive protocol_dependency (es : list expr) (h : heap)
    (σs : session → gmap participant session_type)
    (owns : object → endpoint → Prop) : endpoint → object → object → Prop :=
  | Protocol_dependency_wait i c q σ :
      thread_blocked es h i c →
      owns (Thread i) (c,q) →
      σs c !! q = Some σ →
      ¬ ready_session_action h c q σ →
      protocol_dependency es h σs owns (c,q) (Chan c) (Thread i)
  | Protocol_dependency_ready x c q σ :
      owns x (c,q) →
      σs c !! q = Some σ →
      ready_session_action h c q σ →
      protocol_dependency es h σs owns (c,q) x (Chan c).

Lemma protocol_dependency_uses_ownership_edge es h σs owns ep x y :
  protocol_dependency es h σs owns ep x y → ownership_edge owns ep x y.
Proof.
  intros Hd. destruct Hd; unfold ownership_edge; cbn [fst]; auto.
Qed.

Lemma protocol_dependency_cannot_repeat_edge es h σs owns :
  (∀ x ep, ¬ nonbacktracking_ownership_walk (ownership_edge owns) x ep x) →
  ∀ ep x y z,
    protocol_dependency es h σs owns ep x y →
    protocol_dependency es h σs owns ep y z →
    False.
Proof.
  intros Hforest.
  assert (∀ c q, ¬ owns (Chan c) (c,q)) as Hno_self.
  {
    intros c q Hown. apply (Hforest (Chan c) (c,q)).
    apply Ownership_walk_single. left. split; [reflexivity|exact Hown].
  }
  intros ep x y z Hxy Hyz.
  destruct Hxy as [i c q σ Hblocked Hown Hσ Hnot|x c q σ Hown Hσ Hready];
    inversion Hyz; subst.
  all: try match goal with
  | Hs : ?ss !! ?p = Some ?s, Ht : ?ss !! ?p = Some ?t,
    Hno : ¬ ready_session_action ?h ?c ?p ?s,
    Hyes : ready_session_action ?h ?c ?p ?t |- False =>
      assert (t = s) as -> by congruence; contradiction
  end.
  eapply Hno_self. eassumption.
Qed.

Lemma full_reachability_from_protocol_ownership es h value_typed
    (σs : session → gmap participant session_type) (owns : object → endpoint → Prop) :
  (∀ i, active es h (Thread i) →
    can_stepi i es h ∨ ∃ c q σ, thread_blocked es h i c ∧ owns (Thread i) (c,q) ∧
      σs c !! q = Some σ ∧ ¬ ready_session_action h c q σ) →
  (∀ c, active es h (Chan c) →
    ∃ bufs, session_queues_typed value_typed h c bufs ∧ sbufs_typed bufs (σs c)) →
  (∀ c q, is_Some (h !! (c,q)) → ∃ x, owns x (c,q)) →
  (∀ x c q, owns x (c,q) → Chan c ∈ obj_refs es h x) →
  (∀ x ep, ¬ nonbacktracking_ownership_walk (ownership_edge owns) x ep x) →
  fully_reachable es h.
Proof.
  intros Hthread Hprotocol Hlive Hreference Hforest.
  apply (full_reachability_from_acyclic_dependencies es h
    (λ x y, ∃ ep, protocol_dependency es h σs owns ep x y)).
  - intros x Hcycle.
    destruct (dependency_walk_is_nonbacktracking (ownership_edge owns)
      (protocol_dependency es h σs owns)
      (protocol_dependency_uses_ownership_edge es h σs owns)
      (protocol_dependency_cannot_repeat_edge es h σs owns Hforest)
      x x Hcycle) as (ep & y & Hfirst & Hwalk).
    exact (Hforest x ep Hwalk).
  - intros x y (ep & Hdep).
    destruct Hdep as [i c q σ Hblocked _ _ _|x c q σ Hown _ _].
    + constructor. exact Hblocked.
    + apply Dependency_reference. exact (Hreference x c q Hown).
  - intros [i|c] Hactive.
    + destruct (Hthread i Hactive) as [Hstep|(c & q & σ & Hblocked & Hown & Hσ & Hno)].
      * left. now exists i.
      * right. exists (Chan c).
        exists (c,q). exact (Protocol_dependency_wait es h σs owns i c q σ
          Hblocked Hown Hσ Hno).
    + right. destruct (Hprotocol c Hactive) as (bufs & Hqueues & Htyped).
      destruct (active_session_has_ready_endpoint es h c value_typed bufs (σs c)
        Hactive Hqueues Htyped) as (q & σ & Hσ & Hpresent & Hready).
      destruct (Hlive c q Hpresent) as (x & Hown).
      exists x, (c,q). exact (Protocol_dependency_ready es h σs owns x c q σ
        Hown Hσ Hready).
Qed.

Lemma ownership_walk_mono (E F : endpoint → object → object → Prop) :
  (∀ ep x y, E ep x y → F ep x y) →
  ∀ x ep y, nonbacktracking_ownership_walk E x ep y →
    nonbacktracking_ownership_walk F x ep y.
Proof.
  intros Hsub x ep y Hwalk.
  induction Hwalk; eauto using Ownership_walk_single, Ownership_walk_extend.
Qed.

Lemma ownership_walk_first_edge E x ep y :
  nonbacktracking_ownership_walk E x ep y → ∃ z, E ep x z.
Proof. intros Hwalk; destruct Hwalk; eauto. Qed.

(* Contraction identifies the two vertices of the retained edge. *)
Definition contract_vertex (u v x : object) : object :=
  if decide (x = u) then v else x.

Definition contracted_ownership_edge (E : endpoint → object → object → Prop)
    (u v : object) (pivot ep : endpoint) (x y : object) : Prop :=
  ep ≠ pivot ∧ ∃ a b, E ep a b ∧
    contract_vertex u v a = x ∧ contract_vertex u v b = y.

Lemma contract_pivot_endpoints u v :
  contract_vertex u v u = contract_vertex u v v.
Proof.
  unfold contract_vertex. rewrite decide_True by reflexivity.
  destruct (decide (v = u)); reflexivity.
Qed.

Lemma contract_vertex_identifies_distinct u v x y :
  contract_vertex u v x = contract_vertex u v y →
  x ≠ y →
  (x = u ∧ y = v) ∨ (x = v ∧ y = u).
Proof.
  unfold contract_vertex.
  destruct (decide (x = u)), (decide (y = u)); intros Hxy Hne; subst;
    intuition congruence.
Qed.

Lemma pivot_connects_distinct_representatives
    (E : endpoint → object → object → Prop) u v pivot x y :
  E pivot u v → E pivot v u →
  contract_vertex u v x = contract_vertex u v y → x ≠ y →
  E pivot x y.
Proof.
  intros Huv Hvu Hxy Hne.
  destruct (contract_vertex_identifies_distinct u v x y Hxy Hne)
    as [[-> ->]|[-> ->]]; assumption.
Qed.

Lemma lift_contracted_ownership_walk E u v pivot x ep z :
  E pivot u v → E pivot v u →
  nonbacktracking_ownership_walk (contracted_ownership_edge E u v pivot) x ep z →
  ∃ a, contract_vertex u v a = x ∧
    ∀ b, contract_vertex u v b = z → nonbacktracking_ownership_walk E a ep b.
Proof.
  intros Huv Hvu Hwalk.
  induction Hwalk as [ep x y Hedge|ep next x y z Hedge Hne Htail IH].
  - destruct Hedge as (Hnot & a & a' & Horig & Ha & Ha').
    exists a. split; [exact Ha|].
    intros b Hb. destruct (decide (a' = b)) as [->|Hneq].
    + now apply Ownership_walk_single.
    + eapply (Ownership_walk_extend E ep pivot a a' b); [exact Horig|exact Hnot|].
      apply Ownership_walk_single.
      apply (pivot_connects_distinct_representatives E u v pivot a' b Huv Hvu);
        [congruence|exact Hneq].
  - destruct Hedge as (Hnot & a & a' & Horig & Ha & Ha').
    destruct IH as (mid & Hmid & Hlift).
    exists a. split; [exact Ha|].
    intros b Hb. specialize (Hlift b Hb).
    destruct (decide (a' = mid)) as [->|Hneq].
    + exact (Ownership_walk_extend E ep next a mid b Horig Hne Hlift).
    + eapply (Ownership_walk_extend E ep pivot a a' b); [exact Horig|exact Hnot|].
      eapply (Ownership_walk_extend E pivot next a' mid b).
      * apply (pivot_connects_distinct_representatives E u v pivot a' mid Huv Hvu);
          [congruence|exact Hneq].
      * destruct (ownership_walk_first_edge _ _ _ _ Htail) as (w & Hfirst).
        exact (λ Heq, proj1 Hfirst (eq_sym Heq)).
      * exact Hlift.
Qed.

Lemma contraction_preserves_ownership_forest E u v pivot :
  E pivot u v → E pivot v u →
  (∀ x ep, ¬ nonbacktracking_ownership_walk E x ep x) →
  ∀ x ep, ¬ nonbacktracking_ownership_walk (contracted_ownership_edge E u v pivot) x ep x.
Proof.
  intros Huv Hvu Hforest x ep Hcycle.
  destruct (lift_contracted_ownership_walk E u v pivot x ep x Huv Hvu Hcycle)
    as (a & Ha & Hlift).
  exact (Hforest a ep (Hlift a Ha)).
Qed.

Lemma project_ownership_walk E u v pivot :
  u ≠ v →
  (∀ x y, E pivot x y → (x = u ∧ y = v) ∨ (x = v ∧ y = u)) →
  (∀ ep x y a b, E ep x y → E ep a b →
    (x = a ∧ y = b) ∨ (x = b ∧ y = a)) →
  (∀ x ep, ¬ nonbacktracking_ownership_walk (contracted_ownership_edge E u v pivot) x ep x) →
  ∀ x ep z, nonbacktracking_ownership_walk E x ep z →
    (ep = pivot ∧ E pivot x z) ∨
    (∃ first, nonbacktracking_ownership_walk (contracted_ownership_edge E u v pivot)
        (contract_vertex u v x) first (contract_vertex u v z) ∧
      (first = ep ∨ (ep = pivot ∧ ∃ a b, E pivot x a ∧ E first a b))).
Proof.
  intros Hne Hpivot Hunique Hforest.
  assert (∀ x y, E pivot x y → contract_vertex u v x = contract_vertex u v y)
    as Hcontract.
  { intros x y Hxy. destruct (Hpivot _ _ Hxy) as [[-> ->]|[-> ->]].
    - apply contract_pivot_endpoints.
    - symmetry. apply contract_pivot_endpoints. }
  assert (∀ ep x y, ep ≠ pivot → E ep x y →
    contracted_ownership_edge E u v pivot ep (contract_vertex u v x) (contract_vertex u v y))
    as Hedge.
  { intros ep x y Hnot Hxy. split; [exact Hnot|]. now exists x, y. }
  assert (∀ ep x y a b, ep ≠ pivot → E ep x y → E pivot y a → E ep a b → False)
    as Hno_repeat.
  {
    intros ep x y a b Hnot Hxy Hya Hab.
    destruct (Hunique _ _ _ _ _ Hxy Hab) as [[<- _]|[_ <-]].
    - apply (Hforest (contract_vertex u v x) ep). apply Ownership_walk_single.
      split; [exact Hnot|].
      exists x, y. exact (conj Hxy (conj eq_refl (Hcontract y x Hya))).
    - destruct (Hpivot _ _ Hya) as [[Heq1 Heq2]|[Heq1 Heq2]]; congruence.
  }
  intros x ep z Hwalk.
  induction Hwalk as [ep x y Hxy|ep next x y z Hxy Hdistinct Htail IH].
  - destruct (decide (ep = pivot)) as [->|Hnot].
    + left. now split.
    + right. exists ep. split; [|now left].
      apply Ownership_walk_single. now apply Hedge.
  - destruct IH as [(Hnext & Hyz)|(first & Hprojected & Hfirst)].
    + subst next. right. exists ep. split; [|now left].
      rewrite <- (Hcontract y z Hyz). apply Ownership_walk_single. now apply Hedge.
    + destruct (decide (ep = pivot)) as [->|Hnot].
      * destruct Hfirst as [-> | (Heq & _)]; [|exfalso; apply Hdistinct; symmetry; exact Heq].
        right. exists next. split.
        -- now rewrite (Hcontract x y Hxy).
        -- right. split; [reflexivity|].
           destruct (ownership_walk_first_edge _ _ _ _ Htail) as (b & Hb).
           now exists y, b.
      * assert (ep ≠ first) as Hfirst_ne.
        {
          destruct Hfirst as [-> | (_ & a & b & Hya & Hab)]; [exact Hdistinct|].
          intros <-. exact (Hno_repeat _ _ _ _ _ Hnot Hxy Hya Hab).
        }
        right. exists ep. split; [|now left].
        exact (Ownership_walk_extend (contracted_ownership_edge E u v pivot)
          ep first (contract_vertex u v x) (contract_vertex u v y) (contract_vertex u v z)
          (Hedge ep x y Hnot Hxy) Hfirst_ne Hprojected).
Qed.

Lemma ownership_forest_from_contraction E u v pivot :
  u ≠ v →
  (∀ x y, E pivot x y → (x = u ∧ y = v) ∨ (x = v ∧ y = u)) →
  (∀ ep x y a b, E ep x y → E ep a b →
    (x = a ∧ y = b) ∨ (x = b ∧ y = a)) →
  (∀ x ep, ¬ nonbacktracking_ownership_walk (contracted_ownership_edge E u v pivot) x ep x) →
  ∀ x ep, ¬ nonbacktracking_ownership_walk E x ep x.
Proof.
  intros Hne Hpivot Hunique Hforest x ep Hcycle.
  destruct (project_ownership_walk E u v pivot Hne Hpivot Hunique Hforest x ep x Hcycle)
    as [(_ & Hloop)|(first & Hprojected & _)].
  - destruct (Hpivot _ _ Hloop) as [[Heq1 Heq2]|[Heq1 Heq2]]; congruence.
  - exact (Hforest (contract_vertex u v x) first Hprojected).
Qed.

Lemma unique_owner_determines_edge_vertices owns :
  (∀ a b ep, owns a ep → owns b ep → a = b) →
  ∀ ep x y a b, ownership_edge owns ep x y → ownership_edge owns ep a b →
    (x = a ∧ y = b) ∨ (x = b ∧ y = a).
Proof.
  unfold ownership_edge.
  intros Hunique ep x y a b [[-> Hx]|[-> Hy]] [[-> Ha]|[-> Hb]]; eauto.
Qed.

Lemma ownership_transfer_preserves_forest owns owns' source target pivot :
  ownership_edge owns pivot source target →
  ownership_edge owns' pivot source target →
  (∀ a b ep, owns' a ep → owns' b ep → a = b) →
  (∀ x ep, owns' x ep → owns x ep ∨ (x = target ∧ owns source ep)) →
  (∀ x ep, ¬ nonbacktracking_ownership_walk (ownership_edge owns) x ep x) →
  ∀ x ep, ¬ nonbacktracking_ownership_walk (ownership_edge owns') x ep x.
Proof.
  intros Hpivot Hpivot' Hunique Hmove Hforest.
  assert (source ≠ target) as Hne.
  { intros ->. apply (Hforest target pivot). now constructor. }
  pose proof (unique_owner_determines_edge_vertices _ Hunique) as Hvertices.
  apply (ownership_forest_from_contraction (ownership_edge owns') source target pivot Hne).
  - intros a b Hab. exact (Hvertices pivot a b source target Hab Hpivot').
  - exact Hvertices.
  - assert (∀ x ep, owns' x ep →
      ∃ y, owns y ep ∧ contract_vertex source target y = contract_vertex source target x)
      as Howner.
    {
      intros x ep Howns. destruct (Hmove x ep Howns) as [Hold|(-> & Hold)].
      - exists x. now split.
      - exists source. split; [exact Hold|apply contract_pivot_endpoints].
    }
    assert (ownership_edge owns pivot target source) as Hback by (unfold ownership_edge in *; tauto).
    pose proof (contraction_preserves_ownership_forest _ _ _ _ Hpivot Hback Hforest)
      as Hcontracted_forest.
    intros x ep Hcycle. apply (Hcontracted_forest x ep).
    eapply ownership_walk_mono; [|exact Hcycle].
    intros e a b (Hnot & u & v & Huv & Hu & Hv). split; [exact Hnot|].
    destruct Huv as [[-> Hown]|[-> Hown]].
    + destruct (Howner u e Hown) as (w & Hw & Hcontract).
      exists w, (Chan (fst e)). split; [left; now split|].
      split; [congruence|exact Hv].
    + destruct (Howner v e Hown) as (w & Hw & Hcontract).
      exists (Chan (fst e)), w. split; [right; now split|].
      split; [exact Hu|congruence].
Qed.


Lemma contract_vertex_away u v x :
  x ≠ u → contract_vertex u v x = x.
Proof. unfold contract_vertex. intros Hne. now rewrite decide_False. Qed.

Lemma split_owner_onto_fresh_vertex_preserves_forest owns owns' root fresh pivot :
  fresh ≠ root →
  ownership_edge owns' pivot fresh root →
  (∀ a b ep, owns' a ep → owns' b ep → a = b) →
  (∀ x ep, ep ≠ pivot → owns' x ep →
    owns x ep ∨ (x = fresh ∧ owns root ep)) →
  (∀ ep x y, ownership_edge owns ep x y → x ≠ fresh ∧ y ≠ fresh) →
  (∀ x ep, ¬ nonbacktracking_ownership_walk (ownership_edge owns) x ep x) →
  ∀ x ep, ¬ nonbacktracking_ownership_walk (ownership_edge owns') x ep x.
Proof.
  intros Hne Hpivot Hunique Hmove Haway Hforest.
  pose proof (unique_owner_determines_edge_vertices _ Hunique) as Hvertices.
  apply (ownership_forest_from_contraction (ownership_edge owns') fresh root pivot Hne).
  - intros a b Hab. exact (Hvertices pivot a b fresh root Hab Hpivot).
  - exact Hvertices.
  - assert (∀ x ep, ep ≠ pivot → owns' x ep → owns (contract_vertex fresh root x) ep)
      as Howner.
    {
      intros x ep Hnot Hown. destruct (Hmove x ep Hnot Hown) as [Hold|(-> & Hold)].
      - assert (ownership_edge owns ep x (Chan (fst ep))) as Hx by (left; now split).
        rewrite contract_vertex_away; [exact Hold|].
        exact (proj1 (Haway _ _ _ Hx)).
      - unfold contract_vertex. now rewrite decide_True by reflexivity.
    }
    intros x ep Hcycle. apply (Hforest x ep).
    eapply ownership_walk_mono; [|exact Hcycle].
    intros e a b (Hnot & u & v & Huv & <- & <-).
    destruct Huv as [[-> Hown]|[-> Hown]].
    + pose proof (Howner u e Hnot Hown) as Hlift.
      assert (ownership_edge owns e (contract_vertex fresh root u) (Chan (fst e)))
        as Horig by (left; now split).
      destruct (Haway _ _ _ Horig) as [_ Hchan].
      now rewrite (contract_vertex_away _ _ _ Hchan).
    + pose proof (Howner v e Hnot Hown) as Hlift.
      assert (ownership_edge owns e (Chan (fst e)) (contract_vertex fresh root v))
        as Horig by (right; now split).
      destruct (Haway _ _ _ Horig) as [Hchan _].
      now rewrite (contract_vertex_away _ _ _ Hchan).
Qed.

Lemma ownership_subgraph_preserves_forest owns owns' :
  (∀ x ep, owns' x ep → owns x ep) →
  (∀ x ep, ¬ nonbacktracking_ownership_walk (ownership_edge owns) x ep x) →
  ∀ x ep, ¬ nonbacktracking_ownership_walk (ownership_edge owns') x ep x.
Proof.
  intros Hsub Hforest x ep Hcycle.
  apply (Hforest x ep). eapply ownership_walk_mono; [|exact Hcycle].
  unfold ownership_edge. firstorder.
Qed.


(* Track the endpoint labels behind the session references in expr_refs. *)
Fixpoint expr_endpoints (e : expr) : gset endpoint :=
  match e with
  | Val v => val_endpoints v
  | Var _ => ∅
  | Pair a b | App a b | UApp a b | Send _ a _ b | Let _ a b
  | LetUnit a b | LetProd _ _ a b | If a b _ => expr_endpoints a ∪ expr_endpoints b
  | Inj _ a | InjN _ a | Lam _ a | ULam _ a | Recv _ a | MatchVoid a
  | Close a | Relabel _ a => expr_endpoints a
  | MatchSum a _ b c => expr_endpoints a ∪ expr_endpoints b ∪ expr_endpoints c
  | MatchSumN n a f => expr_endpoints a ∪ fin_union n (expr_endpoints ∘ f)
  | Spawn n f => fin_union n (expr_endpoints ∘ f)
  end
with val_endpoints (v : val) : gset endpoint :=
  match v with
  | UnitV | NatV _ => ∅
  | PairV a b => val_endpoints a ∪ val_endpoints b
  | InjV _ a | InjNV _ a => val_endpoints a
  | FunV _ a | UFunV _ a => expr_endpoints a
  | ChanV ep _ => {[ep]}
  end.

Definition endpoint_sessions (ends : gset endpoint) : gset object :=
  set_map (λ ep, Chan (fst ep)) ends.

Lemma endpoint_sessions_empty : endpoint_sessions ∅ = ∅.
Proof. apply set_map_empty. Qed.

Lemma endpoint_sessions_singleton ep : endpoint_sessions {[ep]} = {[Chan (fst ep)]}.
Proof.
  unfold endpoint_sessions. apply leibniz_equiv.
  exact (set_map_singleton (λ ep : endpoint, Chan (fst ep)) ep).
Qed.

Lemma endpoint_sessions_union a b :
  endpoint_sessions (a ∪ b) = endpoint_sessions a ∪ endpoint_sessions b.
Proof.
  unfold endpoint_sessions. apply leibniz_equiv.
  exact (set_map_union (λ ep : endpoint, Chan (fst ep)) a b).
Qed.

Lemma endpoint_sessions_fin_union n (f : fin n → gset endpoint) :
  endpoint_sessions (fin_union n f) = fin_union n (endpoint_sessions ∘ f).
Proof.
  apply set_eq. intros x. unfold endpoint_sessions at 1.
  rewrite elem_of_map, elem_of_fin_union_iff. split.
  - intros (ep & Heq & Hin).
    apply elem_of_fin_union_iff in Hin as (i & Hin).
    exists i. apply elem_of_map. now exists ep.
  - intros (i & Hin). apply elem_of_map in Hin as (ep & Heq & Hin).
    exists ep. split; [exact Heq|]. apply elem_of_fin_union_iff. now exists i.
Qed.

Lemma fin_union_pointwise_eq `{Countable A} n (f g : fin n → gset A) :
  (∀ i, f i = g i) → fin_union n f = fin_union n g.
Proof.
  intros Hfg. apply set_eq. intros x. rewrite !elem_of_fin_union_iff.
  split; intros (i & Hi); exists i.
  - now rewrite <- Hfg.
  - now rewrite Hfg.
Qed.

Scheme val_endpoint_ind := Induction for val Sort Prop
with expr_endpoint_ind := Induction for expr Sort Prop.
Combined Scheme syntax_endpoint_ind from val_endpoint_ind, expr_endpoint_ind.

Lemma syntax_endpoint_projection :
  (∀ v, endpoint_sessions (val_endpoints v) = val_refs v) ∧
  (∀ e, endpoint_sessions (expr_endpoints e) = expr_refs e).
Proof.
  apply syntax_endpoint_ind; intros; cbn [expr_endpoints val_endpoints expr_refs val_refs].
  all: repeat rewrite endpoint_sessions_union.
  all: try rewrite endpoint_sessions_empty.
  all: repeat match goal with H : endpoint_sessions _ = _ |- _ =>
    progress rewrite H
  end.
  all: try reflexivity.
  - match goal with ep : endpoint |- _ => destruct ep end.
    apply endpoint_sessions_singleton.
  - rewrite endpoint_sessions_fin_union. f_equal.
    apply fin_union_pointwise_eq. intro i; cbn [compose]; eauto.
  - rewrite endpoint_sessions_fin_union.
    apply fin_union_pointwise_eq. intro i; cbn [compose]; eauto.
Qed.

Definition queue_endpoint_set (buf : list entryT) : gset endpoint :=
  value_buffer_refs val_endpoints buf.

Definition object_endpoints (es : list expr) (h : heap) (x : object) : gset endpoint :=
  match x with
  | Thread i => from_option expr_endpoints ∅ (es !! i)
  | Chan c => heap_value_refs val_endpoints h c
  end.

Definition owns_endpoint es h x ep := ep ∈ object_endpoints es h x.

Lemma queue_endpoint_projection buf :
  endpoint_sessions (queue_endpoint_set buf) = buf_refs buf.
Proof.
  induction buf as [|[i v] buf IH]; cbn [queue_endpoint_set buf_refs foldr].
  - apply endpoint_sessions_empty.
  - change (endpoint_sessions (val_endpoints v ∪ queue_endpoint_set buf) =
      val_refs v ∪ buf_refs buf).
    now rewrite endpoint_sessions_union, (proj1 syntax_endpoint_projection), IH.
Qed.

Lemma endpoint_sessions_map_union `{Countable K} {A}
    (f : A → gset endpoint) (m : gmap K A) :
  endpoint_sessions (map_union f m) = map_union (endpoint_sessions ∘ f) m.
Proof.
  apply set_eq. intros x. unfold endpoint_sessions at 1.
  rewrite elem_of_map, elem_of_map_union_iff. split.
  - intros (ep & Heq & Hmem).
    apply elem_of_map_union_iff in Hmem as (i & a & Hlookup & Hin).
    exists i, a. split; [exact Hlookup|].
    apply elem_of_map. now exists ep.
  - intros (i & a & Hlookup & Hin).
    apply elem_of_map in Hin as (ep & Heq & Hin).
    exists ep. split; [exact Heq|].
    apply elem_of_map_union_iff. now exists i, a.
Qed.

Lemma map_union_pointwise_eq `{Countable K, Countable B} {A}
    (f g : A → gset B) (m : gmap K A) :
  (∀ a, f a = g a) → map_union f m = map_union g m.
Proof.
  intros Hfg. apply set_eq. intro x. rewrite !elem_of_map_union_iff.
  split; intros (i & a & Hi & Hx); exists i, a; split; [exact Hi| |exact Hi|].
  - now rewrite <- Hfg.
  - now rewrite Hfg.
Qed.

Lemma object_endpoint_projection es h x :
  endpoint_sessions (object_endpoints es h x) = obj_refs es h x.
Proof.
  destruct x as [i|c]; unfold object_endpoints, obj_refs.
  - destruct (es !! i) as [e|]; cbn [from_option].
    + apply (proj2 syntax_endpoint_projection).
    + apply endpoint_sessions_empty.
  - unfold heap_value_refs. rewrite endpoint_sessions_map_union.
    unfold bufs_refs. apply map_union_pointwise_eq. intros inner.
    unfold compose. rewrite endpoint_sessions_map_union.
    apply map_union_pointwise_eq. apply queue_endpoint_projection.
Qed.

Lemma channel_ref_iff_owned_endpoint es h x c :
  Chan c ∈ obj_refs es h x ↔ ∃ p, owns_endpoint es h x (c,p).
Proof.
  rewrite <- object_endpoint_projection. unfold endpoint_sessions, owns_endpoint.
  rewrite elem_of_map. split.
  - intros ([d p] & Heq & Hin). simpl in Heq. injection Heq as ->. now exists p.
  - intros (p & Hp). exists (c,p). now split.
Qed.



Lemma ctx1_endpoint_split k e :
  ctx1 k → expr_endpoints (k e) = expr_endpoints e ∪ expr_endpoints (k (Val UnitV)).
Proof.
  intros Hctx. destruct Hctx; cbn [expr_endpoints val_endpoints]; try set_solver.
  apply set_eq. intros x.
  rewrite elem_of_union. rewrite !elem_of_fin_union_iff.
  split.
  - intros (q & Hq). cbn [compose] in Hq.
    destruct (decide (p = q)) as [Heq|Hne].
    + now left.
    + right. exists q. cbn [compose]. now rewrite decide_False by exact Hne.
  - intros [He|(q & Hq)].
    + exists p. cbn [compose]. now rewrite decide_True by reflexivity.
    + cbn [compose] in Hq.
      destruct (decide (p = q)) as [Heq|Hne].
      * simpl in Hq. set_solver.
      * exists q. cbn [compose]. now rewrite decide_False by exact Hne.
Qed.


Lemma ctx_endpoint_split k e :
  ctx k → expr_endpoints (k e) = expr_endpoints e ∪ expr_endpoints (k (Val UnitV)).
Proof.
  intros Hctx. induction Hctx as [|k1 k2 H1 H2 IH].
  - simpl. set_solver.
  - rewrite (ctx1_endpoint_split k1 (k2 e) H1), IH.
    rewrite (ctx1_endpoint_split k1 (k2 (Val UnitV)) H1).
    set_solver.
Qed.

Lemma thread_endpoint_lookup es h i e ep :
  es !! i = Some e →
  (owns_endpoint es h (Thread i) ep ↔ ep ∈ expr_endpoints e).
Proof.
  intros Hlookup. unfold owns_endpoint, object_endpoints.
  now rewrite Hlookup.
Qed.

Lemma update_thread_lookup (es : list expr) i old new :
  es !! i = Some old → <[i := new]> es !! i = Some new.
Proof.
  intros Hlookup. apply list_lookup_insert_eq, lookup_lt_is_Some.
  now exists old.
Qed.

Lemma blocked_thread_owns_endpoint es h i c :
  thread_blocked es h i c → ∃ q, owns_endpoint es h (Thread i) (c,q).
Proof.
  intros (p & q & k & π & Hctx & Hlook & _ & _).
  exists q. apply (proj2 (thread_endpoint_lookup _ _ _ _ _ Hlook)).
  rewrite (ctx_endpoint_split _ _ Hctx). cbn [expr_endpoints val_endpoints].
  set_solver.
Qed.

Lemma send_preserves_endpoint_forest es h i k c p q label π v :
  ctx k →
  es !! i = Some (k (Send q (Val (ChanV (c,p) π)) label (Val v))) →
  let es' := <[i := k (Val (ChanV (c,p) π))]> es in
  let h' := push p (c,π q) (label,v) h in
  (∀ x y ep, owns_endpoint es' h' x ep → owns_endpoint es' h' y ep → x = y) →
  (∀ x ep, ¬ nonbacktracking_ownership_walk (ownership_edge (owns_endpoint es h)) x ep x) →
  ∀ x ep, ¬ nonbacktracking_ownership_walk (ownership_edge (owns_endpoint es' h')) x ep x.
Proof.
  intros Hctx Hlookup. cbn zeta.
  set (request := Send q (Val (ChanV (c,p) π)) label (Val v)) in Hlookup.
  set (reply := Val (ChanV (c,p) π)).
  set (es' := <[i := k reply]> es).
  set (h' := push p (c,π q) (label,v) h).
  intros Hunique Hforest.
  assert (es' !! i = Some (k reply)) as Hreply.
  { unfold es'. exact (update_thread_lookup es i _ _ Hlookup). }
  apply (ownership_transfer_preserves_forest (owns_endpoint es h) (owns_endpoint es' h')
    (Thread i) (Chan c) (c,p)); [| |exact Hunique| |exact Hforest].
  - left. split; [reflexivity|].
    apply (proj2 (thread_endpoint_lookup _ _ _ _ _ Hlookup)).
    rewrite (ctx_endpoint_split k request Hctx).
    cbn [request expr_endpoints val_endpoints]. set_solver.
  - left. split; [reflexivity|].
    apply (proj2 (thread_endpoint_lookup _ _ _ _ _ Hreply)).
    rewrite (ctx_endpoint_split k reply Hctx).
    cbn [reply expr_endpoints val_endpoints]. set_solver.
  - intros [j|d] ep Hown.
    + left. destruct (decide (i = j)) as [<-|Hne].
      * apply (proj1 (thread_endpoint_lookup _ _ _ _ _ Hreply)) in Hown.
        apply (proj2 (thread_endpoint_lookup _ _ _ _ _ Hlookup)).
        rewrite (ctx_endpoint_split k reply Hctx) in Hown.
        rewrite (ctx_endpoint_split k request Hctx).
        cbn [request reply expr_endpoints val_endpoints] in *. set_solver.
      * unfold owns_endpoint, object_endpoints, es' in Hown.
        rewrite list_lookup_insert_ne in Hown by exact Hne. exact Hown.
    + change (ep ∈ heap_value_refs val_endpoints (push p (c,π q) (label,v) h) d) in Hown.
      apply heap_value_refs_push in Hown as [Hold|(-> & _ & Hval)].
      * now left.
      * right. split; [reflexivity|].
        apply (proj2 (thread_endpoint_lookup _ _ _ _ _ Hlookup)).
        rewrite (ctx_endpoint_split k request Hctx).
        cbn [request expr_endpoints val_endpoints]. set_solver.
Qed.

Lemma receive_preserves_endpoint_forest es h h' i k c p q label π v :
  ctx k →
  es !! i = Some (k (Recv p (Val (ChanV (c,q) π)))) →
  pop (π p) (c,q) h = Some ((label,v),h') →
  let es' := <[i := k (Val (InjNV label (PairV (ChanV (c,q) π) v)))]> es in
  (∀ x y ep, owns_endpoint es' h' x ep → owns_endpoint es' h' y ep → x = y) →
  (∀ x ep, ¬ nonbacktracking_ownership_walk (ownership_edge (owns_endpoint es h)) x ep x) →
  ∀ x ep, ¬ nonbacktracking_ownership_walk (ownership_edge (owns_endpoint es' h')) x ep x.
Proof.
  intros Hctx Hlookup Hpop. cbn zeta.
  set (request := Recv p (Val (ChanV (c,q) π))) in Hlookup.
  set (reply := Val (InjNV label (PairV (ChanV (c,q) π) v))).
  set (es' := <[i := k reply]> es).
  intros Hunique Hforest.
  assert (es' !! i = Some (k reply)) as Hreply.
  { unfold es'. exact (update_thread_lookup es i _ _ Hlookup). }
  apply (ownership_transfer_preserves_forest (owns_endpoint es h) (owns_endpoint es' h')
    (Chan c) (Thread i) (c,q)); [| |exact Hunique| |exact Hforest].
  - right. split; [reflexivity|].
    apply (proj2 (thread_endpoint_lookup _ _ _ _ _ Hlookup)).
    rewrite (ctx_endpoint_split k request Hctx).
    cbn [request expr_endpoints val_endpoints]. set_solver.
  - right. split; [reflexivity|].
    apply (proj2 (thread_endpoint_lookup _ _ _ _ _ Hreply)).
    rewrite (ctx_endpoint_split k reply Hctx).
    cbn [reply expr_endpoints val_endpoints]. set_solver.
  - intros [j|d] ep Hown.
    + destruct (decide (i = j)) as [<-|Hne].
      * apply (proj1 (thread_endpoint_lookup _ _ _ _ _ Hreply)) in Hown.
        rewrite (ctx_endpoint_split k reply Hctx) in Hown.
        cbn [reply expr_endpoints val_endpoints] in Hown.
        apply elem_of_union in Hown as [Hendpoint|Hctxref].
        -- apply elem_of_union in Hendpoint as [Hchannel|Hval].
           ++ left. apply (proj2 (thread_endpoint_lookup _ _ _ _ _ Hlookup)).
              rewrite (ctx_endpoint_split k request Hctx).
              cbn [request expr_endpoints val_endpoints]. set_solver.
           ++ right. split; [reflexivity|].
              change (ep ∈ heap_value_refs val_endpoints h c).
              apply (proj2 (heap_value_refs_pop val_endpoints h c q (π p) label v h' c ep Hpop)).
              right. now split.
        -- left. apply (proj2 (thread_endpoint_lookup _ _ _ _ _ Hlookup)).
           rewrite (ctx_endpoint_split k request Hctx). now apply elem_of_union_r.
      * left. unfold owns_endpoint, object_endpoints, es' in Hown.
        rewrite list_lookup_insert_ne in Hown by exact Hne. exact Hown.
    + left. change (ep ∈ heap_value_refs val_endpoints h d).
      apply (proj2 (heap_value_refs_pop val_endpoints h c q (π p) label v h' d ep Hpop)).
      now left.
Qed.


Lemma close_preserves_endpoint_forest es (h : heap) i k c p π :
  ctx k →
  es !! i = Some (k (Close (Val (ChanV (c,p) π)))) →
  (∀ q buf, buffer_at h (c,p) q = Some buf → buf = []) →
  (∀ x ep, ¬ nonbacktracking_ownership_walk (ownership_edge (owns_endpoint es h)) x ep x) →
  ∀ x ep, ¬ nonbacktracking_ownership_walk (ownership_edge
    (owns_endpoint (<[i := k (Val UnitV)]> es)
      (delete (c,p) (h : gmap endpoint (gmap participant (list entryT)))))) x ep x.
Proof.
  intros Hctx Hlookup Hempty Hforest.
  apply (ownership_subgraph_preserves_forest (owns_endpoint es h)); [|exact Hforest].
  intros [j|d] ep Hown.
  - destruct (decide (i = j)) as [<-|Hne].
    + pose proof (update_thread_lookup es i _ (k (Val UnitV)) Hlookup) as Hreply.
      apply (proj1 (thread_endpoint_lookup _ _ _ _ _ Hreply)) in Hown.
      apply (proj2 (thread_endpoint_lookup _ _ _ _ _ Hlookup)).
      rewrite (ctx_endpoint_split k (Val UnitV) Hctx) in Hown.
      rewrite (ctx_endpoint_split k (Close (Val (ChanV (c,p) π))) Hctx).
      cbn [expr_endpoints val_endpoints] in *. set_solver.
    + unfold owns_endpoint, object_endpoints in Hown.
      rewrite list_lookup_insert_ne in Hown by exact Hne. exact Hown.
  - exact (proj1 (heap_value_refs_delete_empty_endpoint val_endpoints h c p d ep Hempty) Hown).
Qed.


Lemma subst_endpoint_bounds x a e :
  expr_endpoints e ⊆ expr_endpoints (subst x a e) ∧
  expr_endpoints (subst x a e) ⊆ expr_endpoints e ∪ val_endpoints a.
Proof.
  induction e; cbn [subst expr_endpoints]; repeat case_decide;
    cbn [expr_endpoints].
  all: try match goal with
  | H : ∀ i : fin ?n, expr_endpoints (?f i) ⊆ expr_endpoints (subst ?u ?v (?f i)) ∧ _ |- _ =>
      pose proof (fin_union_reference_bounds n (expr_endpoints ∘ f)
        (λ i, expr_endpoints (subst u v (f i))) (val_endpoints v) H) as Hbranches;
      clear H
  end.
  all: cbn [compose] in *; set_solver.
Qed.

Lemma pure_step_endpoint_subset e e' :
  pure_step e e' →
  (∀ e1 e2, e = If (Val (NatV 0)) e1 e2 → expr_endpoints e2 ⊆ expr_endpoints e1) →
  expr_endpoints e' ⊆ expr_endpoints e.
Proof.
  intros Hstep Hbranches. destruct Hstep; cbn [expr_endpoints val_endpoints];
    try solve [set_solver].
  - exact (proj2 (subst_endpoint_bounds x a e)).
  - exact (proj2 (subst_endpoint_bounds x a e)).
  - destruct b; cbn.
    + pose proof (proj2 (subst_endpoint_bounds x v eL)). set_solver.
    + pose proof (proj2 (subst_endpoint_bounds x v eR)). set_solver.
  - assert (expr_endpoints (f i) ⊆ fin_union n (expr_endpoints ∘ f)) as Hselected.
    { intros c Hc. apply elem_of_fin_union_iff. now exists i. }
    set_solver.
  - pose proof (proj2 (subst_endpoint_bounds x v e)). set_solver.
  - pose proof (proj2 (subst_endpoint_bounds x1 v1 (subst x2 v2 e))).
    pose proof (proj2 (subst_endpoint_bounds x2 v2 e)).
    set_solver.
Qed.

Lemma pure_step_preserves_endpoint_forest es h i k e e' :
  es !! i = Some (k e) →
  ctx k →
  pure_step e e' →
  (∀ e1 e2, e = If (Val (NatV 0)) e1 e2 → expr_endpoints e2 ⊆ expr_endpoints e1) →
  (∀ x ep, ¬ nonbacktracking_ownership_walk (ownership_edge (owns_endpoint es h)) x ep x) →
  ∀ x ep, ¬ nonbacktracking_ownership_walk
    (ownership_edge (owns_endpoint (<[i := k e']> es) h)) x ep x.
Proof.
  intros Hlookup Hctx Hstep Hbranches Hforest.
  apply (ownership_subgraph_preserves_forest (owns_endpoint es h)); [|exact Hforest].
  intros [j|d] ep Hown; [|exact Hown].
  destruct (decide (i = j)) as [<-|Hne].
  - pose proof (update_thread_lookup es i _ (k e') Hlookup) as Hreply.
    apply (proj1 (thread_endpoint_lookup _ _ _ _ _ Hreply)) in Hown.
    apply (proj2 (thread_endpoint_lookup _ _ _ _ _ Hlookup)).
    rewrite (ctx_endpoint_split k e' Hctx) in Hown.
    rewrite (ctx_endpoint_split k e Hctx).
    pose proof (pure_step_endpoint_subset e e' Hstep Hbranches) as Hsubset.
    set_solver.
  - unfold owns_endpoint, object_endpoints in Hown.
    rewrite list_lookup_insert_ne in Hown by exact Hne. exact Hown.
Qed.


(* Runtime typing records endpoint separation and types values produced by reduction. *)
Inductive runtime_typed (Σ : session → gmap participant session_type) : envT -> expr -> type -> Prop :=
  | Runtime_Unit Γ :
    Γunrestricted Γ ->
    runtime_typed Σ Γ (Val UnitV) UnitT
  | Runtime_Nat : ∀ Γ n,
    Γunrestricted Γ ->
    runtime_typed Σ Γ (Val (NatV n)) NatT
  | Runtime_Var : ∀ Γ x t t',
    Γ !! x = None ->
    Γunrestricted Γ ->
    t ≡ t' ->
    runtime_typed Σ (Γ ∪ {[ x := t ]}) (Var x) t'
  | Runtime_Pair : ∀ Γ1 Γ2 e1 e2 t1 t2,
    expr_endpoints e1 ## expr_endpoints e2 →
    disj Γ1 Γ2 ->
    runtime_typed Σ Γ1 e1 t1 ->
    runtime_typed Σ Γ2 e2 t2 ->
    runtime_typed Σ (Γ1 ∪ Γ2) (Pair e1 e2) (PairT t1 t2)
  | Runtime_App : ∀ Γ1 Γ2 e1 e2 t1 t2,
    expr_endpoints e1 ## expr_endpoints e2 →
    disj Γ1 Γ2 ->
    runtime_typed Σ Γ1 e1 (FunT t1 t2) ->
    runtime_typed Σ Γ2 e2 t1 ->
    runtime_typed Σ (Γ1 ∪ Γ2) (App e1 e2) t2
  | Runtime_UApp : ∀ Γ1 Γ2 e1 e2 t1 t2,
    expr_endpoints e1 ## expr_endpoints e2 →
    disj Γ1 Γ2 ->
    runtime_typed Σ Γ1 e1 (UFunT t1 t2) ->
    runtime_typed Σ Γ2 e2 t1 ->
    runtime_typed Σ (Γ1 ∪ Γ2) (UApp e1 e2) t2
  | Runtime_Lam : ∀ Γ x e t1 t2,
    Γ !! x = None ->
    runtime_typed Σ (Γ ∪ {[ x := t1 ]}) e t2 ->
    runtime_typed Σ Γ (Lam x e) (FunT t1 t2)
  | Runtime_ULam : ∀ Γ x e t1 t2,
    expr_endpoints e = ∅ →
    Γ !! x = None ->
    Γunrestricted Γ ->
    runtime_typed Σ (Γ ∪ {[ x := t1 ]}) e t2 ->
    runtime_typed Σ Γ (ULam x e) (UFunT t1 t2)
  | Runtime_Send : ∀ Γ1 Γ2 e1 e2 n t r p i,
    expr_endpoints e1 ## expr_endpoints e2 →
    disj Γ1 Γ2 ->
    runtime_typed Σ Γ1 e1 (ChanT (SendT n p t r)) ->
    runtime_typed Σ Γ2 e2 (t i) ->
    runtime_typed Σ (Γ1 ∪ Γ2) (Send p e1 (fin_to_nat i) e2) (ChanT (r i))
  | Runtime_Recv : ∀ Γ e n t r p,
    runtime_typed Σ Γ e (ChanT (RecvT n p t r)) ->
    runtime_typed Σ Γ (Recv p e) (SumNT n (λ i, PairT (ChanT (r i)) (t i)))
  | Runtime_Let : ∀ Γ1 Γ2 e1 e2 t1 t2 x,
    expr_endpoints e1 ## expr_endpoints e2 →
    disj Γ1 Γ2 ->
    Γ2 !! x = None ->
    runtime_typed Σ Γ1 e1 t1 ->
    runtime_typed Σ (Γ2 ∪ {[ x := t1 ]}) e2 t2 ->
    runtime_typed Σ (Γ1 ∪ Γ2) (Let x e1 e2) t2
  | Runtime_LetUnit : ∀ Γ1 Γ2 e1 e2 t,
    expr_endpoints e1 ## expr_endpoints e2 →
    disj Γ1 Γ2 ->
    runtime_typed Σ Γ1 e1 UnitT ->
    runtime_typed Σ Γ2 e2 t ->
    runtime_typed Σ (Γ1 ∪ Γ2) (LetUnit e1 e2) t
  | Runtime_LetProd : ∀ Γ1 Γ2 e1 e2 t11 t12 t2 x1 x2,
    expr_endpoints e1 ## expr_endpoints e2 →
    disj Γ1 Γ2 ->
    x1 ≠ x2 ->
    Γ2 !! x1 = None ->
    Γ2 !! x2 = None ->
    runtime_typed Σ Γ1 e1 (PairT t11 t12) ->
    runtime_typed Σ (Γ2 ∪ {[ x1 := t11 ]} ∪ {[ x2 := t12 ]}) e2 t2 ->
    runtime_typed Σ (Γ1 ∪ Γ2) (LetProd x1 x2 e1 e2) t2
  | Runtime_MatchVoid : ∀ Γ e t,
    runtime_typed Σ Γ e VoidT ->
    runtime_typed Σ Γ (MatchVoid e) t
  | Runtime_MatchSum : ∀ Γ1 Γ2 e1 eL eR tL tR t x,
    expr_endpoints eL = expr_endpoints eR →
    expr_endpoints e1 ## expr_endpoints eL →
    disj Γ1 Γ2 ->
    Γ2 !! x = None ->
    runtime_typed Σ Γ1 e1 (SumT tL tR) ->
    runtime_typed Σ (Γ2 ∪ {[ x := tL ]}) eL t ->
    runtime_typed Σ (Γ2 ∪ {[ x := tR ]}) eR t ->
    runtime_typed Σ (Γ1 ∪ Γ2) (MatchSum e1 x eL eR) t
  | Runtime_InjN : ∀ Γ n f i e,
    runtime_typed Σ Γ e (f i) ->
    runtime_typed Σ Γ (InjN (fin_to_nat i) e) (SumNT n f)
  | Runtime_MatchSumN : ∀ n Γ1 Γ2 t (f : fin n -> type) fc e,
    (∀ i j, expr_endpoints (fc i) = expr_endpoints (fc j)) →
    (∀ i, expr_endpoints e ## expr_endpoints (fc i)) →
    disj Γ1 Γ2 ->
    (n = 0 -> Γ2 = ∅) ->
    runtime_typed Σ Γ1 e (SumNT n f) ->
    (∀ i, runtime_typed Σ Γ2 (fc i) (FunT (f i) t)) ->
    runtime_typed Σ (Γ1 ∪ Γ2) (MatchSumN n e fc) t
  | Runtime_If : ∀ Γ1 Γ2 e1 e2 e3 t,
    expr_endpoints e2 = expr_endpoints e3 →
    expr_endpoints e1 ## expr_endpoints e2 →
    disj Γ1 Γ2 ->
    runtime_typed Σ Γ1 e1 NatT ->
    runtime_typed Σ Γ2 e2 t ->
    runtime_typed Σ Γ2 e3 t ->
    runtime_typed Σ (Γ1 ∪ Γ2) (If e1 e2 e3) t
  | Runtime_Spawn : ∀ n Γ (fΓ : fin n -> envT) (f : fin n -> expr) (σs : fin (S n) -> session_type),
    (∀ p q, p ≠ q → expr_endpoints (f p) ## expr_endpoints (f q)) →
    consistent (S n) σs ->
    disj_union n Γ fΓ ->
    (∀ p, runtime_typed Σ (fΓ p) (f p) (FunT (ChanT (σs (FS p))) UnitT)) ->
    runtime_typed Σ Γ (Spawn n f) (ChanT (σs 0%fin))
  | Runtime_Close : ∀ Γ e,
    runtime_typed Σ Γ e (ChanT EndT) ->
    runtime_typed Σ Γ (Close e) UnitT
  | Runtime_Relabel : ∀ Γ π e σ,
    runtime_typed Σ Γ e (ChanT (relabelT π σ)) ->
    runtime_typed Σ Γ (Relabel π e) (ChanT σ)
  | Runtime_Iso : ∀ Γ t t' e,
    t ≡ t' ->
    runtime_typed Σ Γ e t ->
    runtime_typed Σ Γ e t'
  | Runtime_PairV Γ v w t u :
    Γunrestricted Γ →
    val_endpoints v ## val_endpoints w →
    runtime_typed Σ ∅ (Val v) t →
    runtime_typed Σ ∅ (Val w) u →
    runtime_typed Σ Γ (Val (PairV v w)) (PairT t u)
  | Runtime_InjV Γ (b : bool) v t u :
    Γunrestricted Γ →
    runtime_typed Σ ∅ (Val v) (if b then t else u) →
    runtime_typed Σ Γ (Val (InjV b v)) (SumT t u)
  | Runtime_InjNV Γ n (f : fin n → type) i v :
    Γunrestricted Γ →
    runtime_typed Σ ∅ (Val v) (f i) →
    runtime_typed Σ Γ (Val (InjNV (fin_to_nat i) v)) (SumNT n f)
  | Runtime_FunV Γ x e t u :
    Γunrestricted Γ →
    runtime_typed Σ {[x := t]} e u →
    runtime_typed Σ Γ (Val (FunV x e)) (FunT t u)
  | Runtime_UFunV Γ x e t u :
    Γunrestricted Γ →
    expr_endpoints e = ∅ →
    runtime_typed Σ {[x := t]} e u →
    runtime_typed Σ Γ (Val (UFunV x e)) (UFunT t u)
  | Runtime_ChanV Γ c q π σ τ :
    Γunrestricted Γ →
    Σ c !! q = Some σ →
    σ ≡ relabelT π τ →
    runtime_typed Σ Γ (Val (ChanV (c,q) π)) (ChanT τ).


Lemma source_typing_has_no_endpoints Γ e t :
  typed Γ e t → expr_endpoints e = ∅.
Proof.
  intros Htyped. apply set_eq. intros [c p].
  rewrite elem_of_empty. split; [|contradiction].
  intros Hmem.
  assert (Chan c ∈ endpoint_sessions (expr_endpoints e)) as Hchannel.
  { unfold endpoint_sessions. apply elem_of_map. now exists (c,p). }
  rewrite (proj2 syntax_endpoint_projection),
    (typed_expression_has_no_references _ _ _ Htyped) in Hchannel.
  set_solver.
Qed.

Lemma source_typing_is_runtime_typed Σ Γ e t :
  typed Γ e t → runtime_typed Σ Γ e t.
Proof.
  induction 1.
  - constructor. assumption.
  - constructor. assumption.
  - eapply Runtime_Var; eassumption.
  - eapply Runtime_Pair; try eassumption.
    rewrite (source_typing_has_no_endpoints _ _ _ H0). set_solver.
  - eapply Runtime_App; try eassumption.
    rewrite (source_typing_has_no_endpoints _ _ _ H0). set_solver.
  - eapply Runtime_UApp; try eassumption.
    rewrite (source_typing_has_no_endpoints _ _ _ H0). set_solver.
  - eapply Runtime_Lam; eassumption.
  - eapply Runtime_ULam; try eassumption.
    eapply source_typing_has_no_endpoints; eassumption.
  - eapply Runtime_Send; try eassumption.
    rewrite (source_typing_has_no_endpoints _ _ _ H0). set_solver.
  - eapply Runtime_Recv; eassumption.
  - eapply Runtime_Let; try eassumption.
    rewrite (source_typing_has_no_endpoints _ _ _ H1). set_solver.
  - eapply Runtime_LetUnit; try eassumption.
    rewrite (source_typing_has_no_endpoints _ _ _ H0). set_solver.
  - eapply Runtime_LetProd; try eassumption.
    rewrite (source_typing_has_no_endpoints _ _ _ H3). set_solver.
  - eapply Runtime_MatchVoid; eassumption.
  - eapply Runtime_MatchSum; try eassumption.
    + now rewrite (source_typing_has_no_endpoints _ _ _ H2),
        (source_typing_has_no_endpoints _ _ _ H3).
    + rewrite (source_typing_has_no_endpoints _ _ _ H1). set_solver.
  - eapply Runtime_InjN; eassumption.
  - eapply Runtime_MatchSumN; try eassumption.
    + intros i j. now rewrite (source_typing_has_no_endpoints _ _ _ (H2 i)),
        (source_typing_has_no_endpoints _ _ _ (H2 j)).
    + intros i. rewrite (source_typing_has_no_endpoints _ _ _ H1). set_solver.
  - eapply Runtime_If; try eassumption.
    + now rewrite (source_typing_has_no_endpoints _ _ _ H1),
        (source_typing_has_no_endpoints _ _ _ H2).
    + rewrite (source_typing_has_no_endpoints _ _ _ H0). set_solver.
  - eapply Runtime_Spawn; try eassumption.
    intros p q _. rewrite (source_typing_has_no_endpoints _ _ _ (H1 p)). set_solver.
  - eapply Runtime_Close; eassumption.
  - eapply Runtime_Relabel; eassumption.
  - eapply Runtime_Iso; eassumption.
Qed.

Definition session_head_matches (π : participant → participant)
    (σ τ : session_type) : Prop :=
  match σ, τ with
  | SendT _ p _ _, SendT _ q _ _ => p = π q
  | RecvT _ p _ _, RecvT _ q _ _ => p = π q
  | EndT, EndT => True
  | _, _ => False
  end.

Lemma session_head_matches_equiv π σ τ τ' :
  τ ≡ τ' → session_head_matches π σ τ → session_head_matches π σ τ'.
Proof.
  intros Hequiv Hmatch. destruct Hequiv; destruct σ; exact Hmatch.
Qed.

Lemma observe_session_type (s : session_type) : s = session_type_id s.
Proof. destruct s; reflexivity. Qed.

Lemma relabelled_session_head_matches π σ τ :
  σ ≡ relabelT π τ → session_head_matches π σ τ.
Proof.
  intros Hequiv. rewrite (observe_session_type (relabelT π τ)) in Hequiv.
  destruct τ; cbn [session_type_id] in Hequiv;
    inversion Hequiv; reflexivity || exact I.
Qed.

Definition runtime_value_shape (Σ : session → gmap participant session_type)
    (v : val) (t : type) : Prop :=
  match t with
  | UnitT => v = UnitV
  | NatT => ∃ n, v = NatV n
  | VoidT => False
  | PairT _ _ => ∃ v1 v2, v = PairV v1 v2
  | SumT _ _ => ∃ b w, v = InjV b w
  | SumNT n _ => ∃ (i : fin n) w, v = InjNV (fin_to_nat i) w
  | FunT _ _ => ∃ x e, v = FunV x e
  | UFunT _ _ => ∃ x e, v = UFunV x e
  | ChanT τ => ∃ c q π σ, v = ChanV (c,q) π ∧
      Σ c !! q = Some σ ∧ session_head_matches π σ τ
  end.

Lemma runtime_value_shape_equiv Σ v t t' :
  t ≡ t' → runtime_value_shape Σ v t → runtime_value_shape Σ v t'.
Proof.
  intros Hequiv Hshape; destruct Hequiv; try exact Hshape.
  destruct Hshape as (c & q & π & σ & Hv & Hlook & Hhead).
  exists c, q, π, σ. split; [exact Hv|]. split; [exact Hlook|].
  exact (session_head_matches_equiv _ _ _ _ H Hhead).
Qed.

Lemma runtime_typed_value_shape Σ Γ e t :
  runtime_typed Σ Γ e t →
  ∀ v, e = Val v → runtime_value_shape Σ v t.
Proof.
  induction 1; intros candidate Hvalue; try discriminate;
    try solve [injection Hvalue as <-; cbn [runtime_value_shape]; eauto].
  - eapply runtime_value_shape_equiv; [eassumption|].
    match goal with
    | IH : ∀ v, _ = Val v → runtime_value_shape _ v _ |- _ => exact (IH candidate Hvalue)
    end.
  - injection Hvalue as <-. cbn [runtime_value_shape].
    exists c, q, π, σ. split; [reflexivity|]. split; [exact H0|].
    now apply relabelled_session_head_matches.
Qed.


CoFixpoint runtime_type_equiv_refl (t : type) : t ≡ t.
Proof.
  destruct t; constructor; try apply runtime_type_equiv_refl.
  - intros i. apply runtime_type_equiv_refl.
  - revert s. cofix Hs. intro s. destruct s; constructor; intros i;
      first [apply runtime_type_equiv_refl | apply Hs].
Qed.

Lemma runtime_union_empty_env (Γ1 Γ2 : envT) :
  Γ1 ∪ Γ2 = ∅ → Γ1 = ∅ ∧ Γ2 = ∅.
Proof.
  intros H. assert (Γ1 = ∅) as -> by (eapply map_positive_l; exact H).
  rewrite map_empty_union in H. auto.
Qed.

Lemma runtime_spawn_empty_env n fΓ :
  disj_union n ∅ fΓ → ∀ p, fΓ p = ∅.
Proof.
  intros Hsplit p. apply map_empty. intros x.
  destruct (fΓ p !! x) as [t|] eqn:Hx; [|reflexivity].
  assert (fΓ p !! x ≡ Some t) as Ht.
  { rewrite Hx. constructor. apply runtime_type_equiv_refl. }
  pose proof (du_left _ _ _ Hsplit p x t Ht) as Hbad.
  rewrite lookup_empty in Hbad. inversion Hbad.
Qed.

Lemma runtime_heap_has_fresh_session (h : heap) :
  ∃ c, ∀ q, h !! (c,q) = None.
Proof.
  set (used := set_map fst (dom h : gset endpoint) : gset session).
  exists (fresh used). intros q.
  change ((h : gmap endpoint (gmap participant (list entryT))) !!
    ((fresh used,q) : endpoint) = None).
  destruct ((h : gmap endpoint (gmap participant (list entryT))) !!
    ((fresh used,q) : endpoint)) as [bs|] eqn:Hlookup; [|reflexivity].
  exfalso. apply (is_fresh used).
  unfold used. apply elem_of_map. exists (fresh used,q). split; [reflexivity|].
  apply elem_of_dom. now exists bs.
Qed.

Lemma all_indices_pass_or_one_fails n (P : fin n → Prop) :
  (∀ i, Decision (P i)) → (∀ i, P i) ∨ (∃ i, ¬ P i).
Proof.
  revert P. induction n as [|n IH]; intros P Hdec.
  - left. intros i. exact (fin_0_inv P i).
  - destruct (Hdec 0%fin) as [H0|H0]; [|right; now exists 0%fin].
    destruct (IH (P ∘ FS) (λ i, Hdec (FS i))) as [Hall|(i & Hi)].
    + left. exact (fin_S_inv P H0 Hall).
    + right. now exists (FS i).
Qed.

Lemma value_expression_decision e : Decision (∃ v, e = Val v).
Proof.
  destruct e; try (right; intros [v Hbad]; discriminate).
  left. eauto.
Defined.

(* Ctx_Spawn requires the worker function to match the reconstructed function. *)
Definition spawn_worker_context_decomposition : Prop :=
  ∀ n (f : fin n → expr) p,
    (∀ v, f p ≠ Val v) →
    ∃ fallback, f = (λ q, if decide (p = q) then f p else fallback q).

Definition protocol_endpoints_allocated
    (Σ : session → gmap participant session_type) (h : heap) : Prop :=
  ∀ c q σ, Σ c !! q = Some σ → is_Some (h !! (c,q)).

Definition waiting_receive_expression
    (Σ : session → gmap participant session_type) (h : heap) (e : expr) : Prop :=
  ∃ c q p k π n (ts : fin n → type) rs,
    ctx k ∧ e = k (Recv p (Val (ChanV (c,q) π))) ∧
    Σ c !! q = Some (RecvT n (π p) ts rs) ∧
    is_Some (h !! (c,q)) ∧ pop (π p) (c,q) h = None.

Definition runtime_expression_can_progress Σ h e :=
  (∃ e' h' ts, ctx_step e h e' h' ts) ∨ waiting_receive_expression Σ h e.

Lemma runtime_head_progress Σ e h e' h' ts :
  head_step e h e' h' ts → runtime_expression_can_progress Σ h e.
Proof.
  intros Hhead. left. exists e', h', ts.
  exact (Ctx_step (λ x, x) _ _ _ _ _ Ctx_nil Hhead).
Qed.

Lemma runtime_pure_progress Σ h e e' :
  pure_step e e' → runtime_expression_can_progress Σ h e.
Proof. intros Hstep. eapply runtime_head_progress, Pure_step, Hstep. Qed.

Lemma runtime_progress_under_context Σ h k e :
  ctx1 k → runtime_expression_can_progress Σ h e →
  runtime_expression_can_progress Σ h (k e).
Proof.
  intros Hctx [(e' & h' & ts & Hstep)|Hwait].
  - inversion Hstep as [k' a ? b ? ? Hk Hhead He]; subst.
    left. exists (k (k' b)), h', ts.
    eapply (Ctx_step (λ e, k (k' e))); [eapply Ctx_cons; eassumption|exact Hhead].
  - destruct Hwait as (c & q & p & k' & π & n & ts & rs & Hk & -> & Hσ & Hlive & Hpop).
    right. exists c, q, p, (λ e, k (k' e)), π, n, ts, rs.
    split; [eapply Ctx_cons; eassumption|].
    split; [reflexivity|]. split; [exact Hσ|]. now split.
Qed.

Local Ltac runtime_inspect IH closed k :=
  let w := fresh "w" in
  let Hnext := fresh "Hnext" in
  destruct (IH closed) as [(w & ->)|Hnext];
  [ | eapply (runtime_progress_under_context _ _ k); [constructor|exact Hnext] ].

Local Ltac runtime_shape Htyped :=
  pose proof (runtime_typed_value_shape _ _ _ _ Htyped _ eq_refl) as Hvshape;
  cbn [runtime_value_shape] in Hvshape.

Lemma closed_runtime_expression_progress Σ h :
  spawn_worker_context_decomposition →
  protocol_endpoints_allocated Σ h →
  ∀ Γ e t, runtime_typed Σ Γ e t → Γ = ∅ →
    (∃ v, e = Val v) ∨ runtime_expression_can_progress Σ h e.
Proof.
  intros Hspawn Hallocated Γ e t Htyped.
  induction Htyped; intros Hclosed.
  all: try match type of Hclosed with
    | ?Γ1 ∪ ?Γ2 = ∅ =>
      destruct (runtime_union_empty_env Γ1 Γ2 Hclosed) as [Hleft Hright]
    end.
  - left. eauto.
  - left. eauto.
  - exfalso.
    apply (f_equal (λ Γ : envT, Γ !! x)) in Hclosed.
    simpl in Hclosed. rewrite lookup_union, H, lookup_singleton, lookup_empty in Hclosed.
    discriminate.
  - right. runtime_inspect IHHtyped1 Hleft (λ e, Pair e e2).
    runtime_inspect IHHtyped2 Hright (λ e, Pair (Val w) e).
    eapply runtime_pure_progress, Pair_step.
  - right. runtime_inspect IHHtyped1 Hleft (λ e, App e e2).
    runtime_shape Htyped1. destruct Hvshape as (arg & body & ->).
    runtime_inspect IHHtyped2 Hright (λ e, App (Val (FunV arg body)) e).
    eapply runtime_pure_progress, App_step.
  - right. runtime_inspect IHHtyped1 Hleft (λ e, UApp e e2).
    runtime_shape Htyped1. destruct Hvshape as (arg & body & ->).
    runtime_inspect IHHtyped2 Hright (λ e, UApp (Val (UFunV arg body)) e).
    eapply runtime_pure_progress, UApp_step.
  - right. eapply runtime_pure_progress, Lam_step.
  - right. eapply runtime_pure_progress, ULam_step.
  - right. runtime_inspect IHHtyped1 Hleft (λ e, Send p e (fin_to_nat i) e2).
    runtime_shape Htyped1. destruct Hvshape as (c & q & π & σ & -> & Hσ & _).
    runtime_inspect IHHtyped2 Hright (λ e, Send p (Val (ChanV (c,q) π)) (fin_to_nat i) e).
    eapply runtime_head_progress, Send_step.
  - right. runtime_inspect IHHtyped Hclosed (λ e, Recv p e).
    runtime_shape Htyped. destruct Hvshape as (c & q & π & σ & -> & Hσ & Hhead).
    destruct σ as [n' p' ts rs | n' p' ts rs |]; cbn [session_head_matches] in Hhead;
      try contradiction.
    subst p'. pose proof (Hallocated c q _ Hσ) as Hlive.
    destruct (pop (π p) (c,q) h) as [[[label payload] h']|] eqn:Hpop.
    + eapply runtime_head_progress, Recv_step. exact Hpop.
    + right. exists c, q, p, (λ e, e), π, n', ts, rs.
      split; [constructor|]. split; [reflexivity|].
      split; [exact Hσ|]. now split.
  - right. runtime_inspect IHHtyped1 Hleft (λ e, Let x e e2).
    eapply runtime_pure_progress, Let_step.
  - right. runtime_inspect IHHtyped1 Hleft (λ e, LetUnit e e2).
    runtime_shape Htyped1. subst w. eapply runtime_pure_progress, LetUnit_step.
  - right. runtime_inspect IHHtyped1 Hleft (λ e, LetProd x1 x2 e e2).
    runtime_shape Htyped1. destruct Hvshape as (v1 & v2 & ->).
    eapply runtime_pure_progress, LetProd_step.
  - right. runtime_inspect IHHtyped Hclosed MatchVoid.
    runtime_shape Htyped. contradiction.
  - right. runtime_inspect IHHtyped1 Hleft (λ e, MatchSum e x eL eR).
    runtime_shape Htyped1. destruct Hvshape as (b & v & ->).
    eapply runtime_pure_progress, MatchSum_step.
  - right. runtime_inspect IHHtyped Hclosed (λ e, InjN (fin_to_nat i) e).
    eapply runtime_pure_progress, InjN_step.
  - right. runtime_inspect IHHtyped Hleft (λ e, MatchSumN n e fc).
    runtime_shape Htyped. destruct Hvshape as (i & v & ->).
    eapply runtime_pure_progress, MatchSumN_step.
  - right. runtime_inspect IHHtyped1 Hleft (λ e, If e e2 e3).
    runtime_shape Htyped1. destruct Hvshape as (m & ->).
    destruct m as [|m]; [eapply runtime_pure_progress, If_step2|].
    eapply runtime_pure_progress, If_step1. discriminate.
  - subst Γ. right.
    destruct (all_indices_pass_or_one_fails n
      (λ p, ∃ w, f p = Val w) (λ p, value_expression_decision (f p)))
      as [Hvalues|(p & Hnonvalue)].
    + destruct (finite_choice (λ p v, f p = Val v) Hvalues) as (fv & Hfv).
      destruct (runtime_heap_has_fresh_session h) as (c & Hfresh).
      eapply runtime_head_progress. exact (Spawn_step h c n f fv Hfresh Hfv).
    + assert (fΓ p = ∅) as Hempty by (eapply runtime_spawn_empty_env; eauto).
      match goal with
      | IH : ∀ q, fΓ q = ∅ → _ |- _ =>
        destruct (IH p Hempty) as [Hvalue|Hnext]
      end.
      * contradiction.
      * destruct (Hspawn n f p) as (fallback & Hf).
        { intros v Hv. apply Hnonvalue. now exists v. }
        rewrite Hf.
        eapply (runtime_progress_under_context _ _ (λ e, Spawn n
          (λ q, if decide (p = q) then e else fallback q)));
          [constructor|exact Hnext].
  - right. runtime_inspect IHHtyped Hclosed (λ e, Close e).
    runtime_shape Htyped. destruct Hvshape as (c & q & π & σ & -> & Hσ & _).
    eapply runtime_head_progress, Close_step.
  - right. runtime_inspect IHHtyped Hclosed (λ e, Relabel π e).
    runtime_shape Htyped. destruct Hvshape as (c & q & π' & σ' & -> & Hσ & _).
    eapply runtime_pure_progress, Relabel_step.
  - now apply IHHtyped.
  - left. eauto.
  - left. eauto.
  - left. eauto.
  - left. eauto.
  - left. eauto.
  - left. eauto.
Qed.


Lemma runtime_thread_progress Σ es h i :
  spawn_worker_context_decomposition →
  protocol_endpoints_allocated Σ h →
  (∀ e, es !! i = Some e → runtime_typed Σ ∅ e UnitT) →
  active es h (Thread i) →
  can_stepi i es h ∨
  ∃ c q σ, thread_blocked es h i c ∧ owns_endpoint es h (Thread i) (c,q) ∧
    Σ c !! q = Some σ ∧ ¬ ready_session_action h c q σ.
Proof.
  intros Hspawn Hallocated Htyped (e & Hlook & Hactive).
  pose proof (Htyped e Hlook) as He.
  destruct (closed_runtime_expression_progress Σ h Hspawn Hallocated _ _ _ He eq_refl)
    as [(v & Hv)|[(e' & h' & ts & Hstep)|Hwait]].
  - pose proof (runtime_typed_value_shape _ _ _ _ He v Hv) as Hshape.
    cbn [runtime_value_shape] in Hshape. exfalso. apply Hactive.
    now rewrite Hv, Hshape.
  - left. do 2 eexists. eapply Head_step; [exact Hstep|exact Hlook].
  - destruct Hwait as (c & q & p & k & π & n & ts & rs & Hctx & -> & Hσ & Hlive & Hpop).
    right. exists c, q, (RecvT n (π p) ts rs).
    split.
    + exists p, q, k, π. split; [exact Hctx|]. split; [exact Hlook|]. now split.
    + split.
      * apply (proj2 (thread_endpoint_lookup _ _ _ _ _ Hlook)).
        rewrite (ctx_endpoint_split _ _ Hctx).
        cbn [expr_endpoints val_endpoints]. set_solver.
      * split; [exact Hσ|].
        intros (entry & h' & Hready). rewrite Hpop in Hready. discriminate.
Qed.

Lemma runtime_typed_state_is_fully_reachable Σ es h :
  spawn_worker_context_decomposition →
  protocol_endpoints_allocated Σ h →
  (∀ i e, es !! i = Some e → runtime_typed Σ ∅ e UnitT) →
  (∀ c, active es h (Chan c) →
    ∃ bufs, session_queues_typed (λ v t, runtime_typed Σ ∅ (Val v) t) h c bufs ∧
      sbufs_typed bufs (Σ c)) →
  (∀ c q, is_Some (h !! (c,q)) → ∃ x, owns_endpoint es h x (c,q)) →
  (∀ x ep, ¬ nonbacktracking_ownership_walk (ownership_edge (owns_endpoint es h)) x ep x) →
  fully_reachable es h.
Proof.
  intros Hspawn Hallocated Hthreads Hqueues Hlive Hforest.
  apply (full_reachability_from_protocol_ownership es h
    (λ v t, runtime_typed Σ ∅ (Val v) t) Σ (owns_endpoint es h)).
  - intros i. exact (runtime_thread_progress Σ es h i Hspawn Hallocated (Hthreads i)).
  - exact Hqueues.
  - exact Hlive.
  - intros x c q Hown. apply channel_ref_iff_owned_endpoint. now exists q.
  - exact Hforest.
Qed.


Lemma typed_initial_state_has_full_reachability e :
  spawn_worker_context_decomposition →
  typed ∅ e UnitT →
  fully_reachable [e] ∅.
Proof.
  intros Hspawn Htyped.
  apply empty_heap_full_reachability_iff_progress.
  intros i Hactive.
  set (Σ := λ _ : session, (∅ : gmap participant session_type)).
  assert (protocol_endpoints_allocated Σ ∅) as Hallocated.
  { intros c q σ Hσ. unfold Σ in Hσ. rewrite lookup_empty in Hσ. discriminate. }
  assert (∀ e', [e] !! i = Some e' → runtime_typed Σ ∅ e' UnitT) as Hthread.
  {
    intros e' Hlookup. destruct i as [|j].
    - change (Some e = Some e') in Hlookup. injection Hlookup as <-.
      now apply source_typing_is_runtime_typed.
    - change ([] !! j = Some e') in Hlookup. rewrite lookup_nil in Hlookup. discriminate.
  }
  destruct (runtime_thread_progress Σ [e] ∅ i Hspawn Hallocated Hthread Hactive)
    as [Hstep|(c & q & σ & _ & _ & Hσ & _)].
  - exact Hstep.
  - unfold Σ in Hσ. rewrite lookup_empty in Hσ. discriminate.
Qed.

Definition protocols_agree_on
    (Σ Σ' : session → gmap participant session_type) (ends : gset endpoint) :=
  ∀ ep, ep ∈ ends → Σ (fst ep) !! snd ep = Σ' (fst ep) !! snd ep.

Lemma protocols_agree_on_subset Σ Σ' a b :
  a ⊆ b → protocols_agree_on Σ Σ' b → protocols_agree_on Σ Σ' a.
Proof. intros Hsub Hagree ep Hep. apply Hagree, Hsub, Hep. Qed.

Local Ltac runtime_reuse_typing :=
  match goal with
  | IH : protocols_agree_on ?S ?S' (expr_endpoints ?e) → runtime_typed ?S' _ ?e _,
    Ha : protocols_agree_on ?S ?S' ?ends |- runtime_typed ?S' _ ?e _ =>
    apply IH; eapply protocols_agree_on_subset; [|exact Ha];
    cbn [expr_endpoints val_endpoints]; set_solver
  end.

Lemma runtime_typed_change_protocols Σ Σ' Γ e t :
  runtime_typed Σ Γ e t →
  protocols_agree_on Σ Σ' (expr_endpoints e) →
  runtime_typed Σ' Γ e t.
Proof.
  intros Htyped. induction Htyped; intros Hagree; cbn [expr_endpoints val_endpoints] in Hagree.
  - now constructor.
  - now constructor.
  - eapply Runtime_Var; eassumption.
  - eapply Runtime_Pair; try eassumption; runtime_reuse_typing.
  - eapply Runtime_App; try eassumption; runtime_reuse_typing.
  - eapply Runtime_UApp; try eassumption; runtime_reuse_typing.
  - eapply Runtime_Lam; try eassumption; runtime_reuse_typing.
  - eapply Runtime_ULam; try eassumption; runtime_reuse_typing.
  - eapply Runtime_Send; try eassumption; runtime_reuse_typing.
  - eapply Runtime_Recv; runtime_reuse_typing.
  - eapply Runtime_Let; try eassumption; runtime_reuse_typing.
  - eapply Runtime_LetUnit; try eassumption; runtime_reuse_typing.
  - eapply Runtime_LetProd; try eassumption; runtime_reuse_typing.
  - eapply Runtime_MatchVoid; runtime_reuse_typing.
  - eapply Runtime_MatchSum; try eassumption; runtime_reuse_typing.
  - eapply Runtime_InjN; runtime_reuse_typing.
  - eapply Runtime_MatchSumN; try eassumption.
    + runtime_reuse_typing.
    + intros j.
      match goal with IH : ∀ j, protocols_agree_on _ _ (expr_endpoints (fc j)) → _ |- _ =>
        apply IH
      end.
      eapply protocols_agree_on_subset; [|exact Hagree].
      intros ep Hep. apply elem_of_union_r, elem_of_fin_union_iff. now exists j.
  - eapply Runtime_If; try eassumption.
    + runtime_reuse_typing.
    + runtime_reuse_typing.
    + apply IHHtyped3. rewrite <- H. eapply protocols_agree_on_subset; [|exact Hagree].
      set_solver.
  - eapply Runtime_Spawn; try eassumption.
    intros p.
    match goal with IH : ∀ p, protocols_agree_on _ _ (expr_endpoints (f p)) → _ |- _ =>
      apply IH
    end.
    eapply protocols_agree_on_subset; [|exact Hagree].
    intros ep Hep. apply elem_of_fin_union_iff. now exists p.
  - eapply Runtime_Close; runtime_reuse_typing.
  - eapply Runtime_Relabel; runtime_reuse_typing.
  - eapply Runtime_Iso; try eassumption; runtime_reuse_typing.
  - eapply Runtime_PairV; try eassumption; runtime_reuse_typing.
  - eapply Runtime_InjV; try eassumption; runtime_reuse_typing.
  - eapply Runtime_InjNV; try eassumption; runtime_reuse_typing.
  - eapply Runtime_FunV; try eassumption; runtime_reuse_typing.
  - eapply Runtime_UFunV; try eassumption; runtime_reuse_typing.
  - eapply Runtime_ChanV with (σ := σ); try eassumption.
    assert ((c,q) ∈ ({[(c,q)]} : gset endpoint)) as Hmem by set_solver.
    specialize (Hagree (c,q) Hmem). cbn [fst snd] in Hagree.
    now rewrite <- Hagree.
Qed.


(* The frame endpoints are those present with a unit value in the hole. *)
Definition runtime_context_frame Σ Γ (k : expr → expr) hole t : Prop :=
  ∃ Γhole τ,
    runtime_typed Σ Γhole hole τ ∧
    (Γ = ∅ → Γhole = ∅) ∧
    expr_endpoints hole ## expr_endpoints (k (Val UnitV)) ∧
    ∀ Σ' replacement,
      protocols_agree_on Σ Σ' (expr_endpoints (k (Val UnitV))) →
      expr_endpoints replacement ## expr_endpoints (k (Val UnitV)) →
      runtime_typed Σ' Γhole replacement τ →
      runtime_typed Σ' Γ (k replacement) t.

Lemma disjoint_from_fin_union n (f : fin n → gset endpoint) refs :
  refs ## fin_union n f ↔ ∀ i, refs ## f i.
Proof.
  split.
  - intros Hdis i. apply elem_of_disjoint. intros ep HR Hi.
    eapply (proj1 (elem_of_disjoint _ _) Hdis ep HR).
    apply elem_of_fin_union_iff. now exists i.
  - intros Hdis. apply elem_of_disjoint. intros ep HR Hi.
    apply elem_of_fin_union_iff in Hi as [i Hi].
    exact (proj1 (elem_of_disjoint _ _) (Hdis i) ep HR Hi).
Qed.

Lemma spawn_worker_refs_in_frame n (f : fin n → expr) p q :
  p ≠ q →
  expr_endpoints (f q) ⊆
  expr_endpoints (Spawn n (λ r, if decide (p = r) then Val UnitV else f r)).
Proof.
  intros Hne ep Hep. cbn [expr_endpoints].
  apply elem_of_fin_union_iff. exists q.
  cbn [compose]. now rewrite decide_False by exact Hne.
Qed.

Local Ltac invert_runtime_context Hctx Heq :=
  destruct Hctx; inversion Heq; subst; clear Heq;
  try match goal with
  | Hpair : existT ?n ?f = existT ?n ?g |- _ =>
      apply (inj_pair2_eq_dec nat Nat.eq_dec) in Hpair; (subst f || subst g)
  end.

Local Ltac choose_runtime_frame Hhole :=
  lazymatch type of Hhole with
  | runtime_typed _ ?Γhole _ ?τ => exists Γhole, τ; split; [exact Hhole|]
  end.

Local Ltac frame_closed_env :=
  first [tauto | intros Hempty; apply runtime_union_empty_env in Hempty; tauto].

Local Ltac frame_retype_subterm :=
  match goal with
  | Hsub : runtime_typed ?S ?G ?e ?t,
    Hagree : protocols_agree_on ?S ?S' ?set |- runtime_typed ?S' ?G ?e ?t =>
      eapply (runtime_typed_change_protocols _ _ _ _ _ Hsub);
      eapply protocols_agree_on_subset; [|exact Hagree];
      cbn [expr_endpoints val_endpoints]; set_solver
  end.

Local Ltac simple_runtime_frame Hhole make :=
  choose_runtime_frame Hhole;
  split; [frame_closed_env|];
  split; [cbn [expr_endpoints val_endpoints]; set_solver|];
  intros Σnew replacement Hagree Hsep Hnew;
  cbn [expr_endpoints val_endpoints] in Hsep;
  eapply make; try eassumption;
  first [solve [frame_retype_subterm] | set_solver].

Lemma runtime_typing_ctx1_frame Σ Γ e t :
  runtime_typed Σ Γ e t →
  ∀ k hole, ctx1 k → e = k hole → runtime_context_frame Σ Γ k hole t.
Proof.
  intros Htyped. induction Htyped; intros k hole Hctx Hplug;
    try solve [destruct Hctx; discriminate].
  - invert_runtime_context Hctx Hplug.
    + simple_runtime_frame Htyped1 Runtime_Pair.
    + simple_runtime_frame Htyped2 Runtime_Pair.
  - invert_runtime_context Hctx Hplug.
    + simple_runtime_frame Htyped1 Runtime_App.
    + simple_runtime_frame Htyped2 Runtime_App.
  - invert_runtime_context Hctx Hplug.
    + simple_runtime_frame Htyped1 Runtime_UApp.
    + simple_runtime_frame Htyped2 Runtime_UApp.
  - invert_runtime_context Hctx Hplug.
    + simple_runtime_frame Htyped1 Runtime_Send.
    + simple_runtime_frame Htyped2 Runtime_Send.
  - invert_runtime_context Hctx Hplug. simple_runtime_frame Htyped Runtime_Recv.
  - invert_runtime_context Hctx Hplug. simple_runtime_frame Htyped1 Runtime_Let.
  - invert_runtime_context Hctx Hplug. simple_runtime_frame Htyped1 Runtime_LetUnit.
  - invert_runtime_context Hctx Hplug. simple_runtime_frame Htyped1 Runtime_LetProd.
  - invert_runtime_context Hctx Hplug. simple_runtime_frame Htyped Runtime_MatchVoid.
  - invert_runtime_context Hctx Hplug. simple_runtime_frame Htyped1 Runtime_MatchSum.
  - invert_runtime_context Hctx Hplug. simple_runtime_frame Htyped Runtime_InjN.
  - invert_runtime_context Hctx Hplug.
    choose_runtime_frame Htyped.
    split; [frame_closed_env|]. split.
    + cbn [expr_endpoints val_endpoints].
      pose proof (proj2 (disjoint_from_fin_union _ _ _) H0) as Hf. set_solver.
    + intros Σnew replacement Hagree Hsep Hnew.
      cbn [expr_endpoints val_endpoints] in Hsep.
      eapply Runtime_MatchSumN; try eassumption.
      * apply (proj1 (disjoint_from_fin_union _ _ _)). set_solver.
      * intros j. eapply runtime_typed_change_protocols; [eauto|].
        eapply protocols_agree_on_subset; [|exact Hagree].
        intros ep Hep. cbn [expr_endpoints val_endpoints].
        apply elem_of_union_r, elem_of_fin_union_iff. now exists j.
  - invert_runtime_context Hctx Hplug.
    choose_runtime_frame Htyped1.
    split; [frame_closed_env|].
    split; [cbn [expr_endpoints val_endpoints]; set_solver|].
    intros Σnew replacement Hagree Hsep Hnew.
    cbn [expr_endpoints val_endpoints] in Hagree, Hsep.
    eapply Runtime_If; try eassumption.
    + set_solver.
    + frame_retype_subterm.
    + eapply runtime_typed_change_protocols; [exact Htyped3|].
      eapply protocols_agree_on_subset; [|exact Hagree]. set_solver.
  - invert_runtime_context Hctx Hplug.
    match goal with
    | Hworkers : ∀ i, runtime_typed Σ (fΓ i) _ _ |- _ =>
      pose proof (Hworkers p) as Hfocus
    end.
    cbn [compose] in Hfocus. rewrite decide_True in Hfocus by reflexivity.
    choose_runtime_frame Hfocus.
    split.
    { intros ->. now eapply runtime_spawn_empty_env. }
    split.
    + apply elem_of_disjoint. intros ep Hin Hframe.
      cbn [expr_endpoints] in Hframe.
      apply elem_of_fin_union_iff in Hframe as (q & Hq).
      cbn [compose] in Hq.
      destruct (decide (p = q)) as [Heq|Hne].
      * cbn [expr_endpoints val_endpoints] in Hq. set_solver.
      * pose proof (H p q Hne) as Hpq.
        cbn [compose] in Hpq.
        rewrite decide_True in Hpq by reflexivity.
        rewrite decide_False in Hpq by exact Hne.
        exact (proj1 (elem_of_disjoint _ _) Hpq ep Hin Hq).
    + intros Σnew replacement Hagree Hsep Hnew.
      eapply (Runtime_Spawn Σnew _ Γ fΓ _ σs); try eassumption.
      * intros a b Hab.
        destruct (decide (p = a)) as [<-|Hpa], (decide (p = b)) as [<-|Hpb].
        -- contradiction.
        -- apply elem_of_disjoint. intros ep Hrep Hbranch.
           eapply (proj1 (elem_of_disjoint _ _) Hsep ep Hrep).
           eapply spawn_worker_refs_in_frame; eassumption.
        -- apply elem_of_disjoint. intros ep Hbranch Hrep.
           eapply (proj1 (elem_of_disjoint _ _) Hsep ep Hrep).
           eapply spawn_worker_refs_in_frame; eassumption.
        -- pose proof (H a b Hab) as Hstatic.
           cbn [compose] in Hstatic. now rewrite !decide_False in Hstatic by assumption.
      * intros q. destruct (decide (p = q)) as [<-|Hne].
        -- exact Hnew.
        -- eapply (runtime_typed_change_protocols Σ Σnew).
           ++ match goal with
              | Hworkers : ∀ i, runtime_typed Σ (fΓ i) _ _ |- _ =>
                  pose proof (Hworkers q) as Hstatic
              end.
              cbn [compose] in Hstatic. rewrite decide_False in Hstatic by exact Hne. exact Hstatic.
           ++ eapply protocols_agree_on_subset; [|exact Hagree].
              now apply spawn_worker_refs_in_frame.
  - invert_runtime_context Hctx Hplug. simple_runtime_frame Htyped Runtime_Close.
  - invert_runtime_context Hctx Hplug. simple_runtime_frame Htyped Runtime_Relabel.
  - destruct (IHHtyped k hole Hctx Hplug) as (Γhole & τ & Hhole & Hclosed & Hsep & Hframe).
    exists Γhole, τ. split; [exact Hhole|]. split; [exact Hclosed|]. split; [exact Hsep|].
    intros Σnew replacement Hagree Hdis Hnew.
    eapply Runtime_Iso; [eassumption|]. now apply Hframe.
Qed.


Lemma runtime_typing_context_frame Σ Γ k e t :
  ctx k →
  runtime_typed Σ Γ (k e) t →
  runtime_context_frame Σ Γ k e t.
Proof.
  intros Hctx. revert Γ e t.
  induction Hctx as [|k1 k2 Hctx1 Hctx2 IH]; intros Γ e t Htyped.
  - exists Γ, t. split; [exact Htyped|].
    split; [tauto|]. split; [cbn [expr_endpoints val_endpoints]; set_solver|].
    intros Σnew replacement Hagree Hsep Hnew. exact Hnew.
  - destruct (runtime_typing_ctx1_frame _ _ _ _ Htyped k1 (k2 e) Hctx1 eq_refl)
      as (Γmid & τmid & Hmid & Hclosed1 & Hsep1 & Hframe1).
    destruct (IH Γmid e τmid Hmid)
      as (Γhole & τ & Hhole & Hclosed2 & Hsep2 & Hframe2).
    assert (expr_endpoints (k1 (k2 (Val UnitV))) =
      expr_endpoints (k2 (Val UnitV)) ∪ expr_endpoints (k1 (Val UnitV))) as Hsplit.
    { now apply ctx1_endpoint_split. }
    rewrite (ctx_endpoint_split k2 e Hctx2) in Hsep1.
    exists Γhole, τ. split; [exact Hhole|].
    split; [intros Hempty; exact (Hclosed2 (Hclosed1 Hempty))|].
    split.
    + cbn beta. rewrite Hsplit. set_solver.
    + intros Σnew replacement Hagree Hsep Hnew.
      cbn beta in Hagree, Hsep |- *. rewrite Hsplit in Hagree, Hsep.
      apply (Hframe1 Σnew (k2 replacement)).
      * eapply protocols_agree_on_subset; [|exact Hagree]. set_solver.
      * rewrite (ctx_endpoint_split k2 replacement Hctx2). set_solver.
      * apply Hframe2; [|set_solver|exact Hnew].
        eapply protocols_agree_on_subset; [|exact Hagree]. set_solver.
Qed.


Definition replace_session_protocol_map
    (Σ : session → gmap participant session_type) (c : session)
    (locals : gmap participant session_type) : session → gmap participant session_type :=
  λ d, if decide (d = c) then locals else Σ d.

Lemma replace_session_protocols_agree Σ c locals endpoints :
  (∀ p, (c,p) ∈ endpoints → Σ c !! p = locals !! p) →
  protocols_agree_on Σ (replace_session_protocol_map Σ c locals) endpoints.
Proof.
  intros Hmatch [d p] Hin. cbn [fst snd]. unfold replace_session_protocol_map.
  destruct (decide (d = c)) as [->|Hne]; [now apply Hmatch|reflexivity].
Qed.

Lemma changed_endpoint_protocol_agrees_on_frame Σ c q σ endpoints :
  (c,q) ∉ endpoints →
  protocols_agree_on Σ (replace_session_protocol_map Σ c (<[q := σ]> (Σ c))) endpoints.
Proof.
  intros Hnot. apply replace_session_protocols_agree.
  intros p Hin.
  assert (q ≠ p) as Hne by (intros <-; contradiction).
  now rewrite lookup_insert_ne.
Qed.

Lemma removed_endpoint_protocol_agrees_on_frame Σ c q endpoints :
  (c,q) ∉ endpoints →
  protocols_agree_on Σ (replace_session_protocol_map Σ c (delete q (Σ c))) endpoints.
Proof.
  intros Hnot. apply replace_session_protocols_agree.
  intros p Hin.
  assert (q ≠ p) as Hne by (intros <-; contradiction).
  now rewrite lookup_delete_ne.
Qed.


Lemma replace_closed_runtime_subexpression Σ Σ' k e e' t :
  ctx k →
  runtime_typed Σ ∅ (k e) t →
  protocols_agree_on Σ Σ' (expr_endpoints (k (Val UnitV))) →
  expr_endpoints e' ## expr_endpoints (k (Val UnitV)) →
  (∀ τ, runtime_typed Σ ∅ e τ → runtime_typed Σ' ∅ e' τ) →
  runtime_typed Σ' ∅ (k e') t.
Proof.
  intros Hctx Htyped Hagree Hsep Hreplace.
  destruct (runtime_typing_context_frame Σ ∅ k e t Hctx Htyped)
    as (Γhole & τ & Hhole & Hempty & _ & Hframe).
  specialize (Hempty eq_refl). subst Γhole.
  apply (Hframe Σ' e' Hagree Hsep). now apply Hreplace.
Qed.

Definition type_equiv_view (t u : type) : Prop :=
  match t with
  | UnitT => u = UnitT
  | VoidT => u = VoidT
  | NatT => u = NatT
  | PairT a b => ∃ c d, u = PairT c d ∧ a ≡ c ∧ b ≡ d
  | SumT a b => ∃ c d, u = SumT c d ∧ a ≡ c ∧ b ≡ d
  | SumNT n f => ∃ g : fin n → type, u = SumNT n g ∧ ∀ i, f i ≡ g i
  | FunT a b => ∃ c d, u = FunT c d ∧ a ≡ c ∧ b ≡ d
  | UFunT a b => ∃ c d, u = UFunT c d ∧ a ≡ c ∧ b ≡ d
  | ChanT a => ∃ b, u = ChanT b ∧ a ≡ b
  end.

Lemma type_equiv_observe t u : t ≡ u → type_equiv_view t u.
Proof. intros H. destruct H; cbn [type_equiv_view]; eauto 8. Qed.

Definition session_equiv_view (s r : session_type) : Prop :=
  match s with
  | EndT => r = EndT
  | SendT n p ts ss => ∃ us rs, r = SendT n p us rs ∧
      (∀ i, ts i ≡ us i) ∧ (∀ i, ss i ≡ rs i)
  | RecvT n p ts ss => ∃ us rs, r = RecvT n p us rs ∧
      (∀ i, ts i ≡ us i) ∧ (∀ i, ss i ≡ rs i)
  end.

Lemma session_equiv_observe s r : s ≡ r → session_equiv_view s r.
Proof. intros H. destruct H; cbn [session_equiv_view]; eauto 8. Qed.

CoFixpoint runtime_type_equiv_sym (t u : type) (Htu : t ≡ u) : u ≡ t.
Proof.
  destruct Htu; constructor; try (eapply runtime_type_equiv_sym; eassumption).
  - intros i. exact (runtime_type_equiv_sym _ _ (H i)).
  - revert s1 s2 H. cofix IH. intros a b Hab.
    destruct Hab; constructor; intros i;
      first [exact (runtime_type_equiv_sym _ _ (H i))|exact (IH _ _ (H0 i))].
Qed.

Lemma runtime_session_equiv_sym (s r : session_type) : s ≡ r → r ≡ s.
Proof.
  revert s r. cofix IH. intros a b Hab.
  destruct Hab; constructor; intros i;
    first [exact (runtime_type_equiv_sym _ _ (H i))|exact (IH _ _ (H0 i))].
Qed.

CoFixpoint runtime_type_equiv_trans (t u v : type) (Htu : t ≡ u) (Huv : u ≡ v) : t ≡ v.
Proof.
  destruct Htu; pose proof (type_equiv_observe _ _ Huv) as Hview;
    cbn [type_equiv_view] in Hview.
  all: try solve [subst v; constructor].
  all: try solve [destruct Hview as (a & b & -> & Ha & Hb); constructor;
    eapply runtime_type_equiv_trans; eassumption].
  - destruct Hview as (g & -> & Hg). constructor. intros i.
    exact (runtime_type_equiv_trans _ _ _ (H i) (Hg i)).
  - destruct Hview as (s3 & -> & H23). constructor.
    clear Huv.
    revert s1 s2 s3 H H23. cofix IH. intros a b c Hab Hbc.
    destruct Hab; pose proof (session_equiv_observe _ _ Hbc) as Hview;
      cbn [session_equiv_view] in Hview.
    + subst c. constructor.
    + destruct Hview as (us & rs & -> & Hts & Hrs). constructor.
      * intros i. exact (runtime_type_equiv_trans _ _ _ (H i) (Hts i)).
      * intros i. exact (IH _ _ _ (H0 i) (Hrs i)).
    + destruct Hview as (us & rs & -> & Hts & Hrs). constructor.
      * intros i. exact (runtime_type_equiv_trans _ _ _ (H i) (Hts i)).
      * intros i. exact (IH _ _ _ (H0 i) (Hrs i)).
Qed.

Lemma runtime_session_equiv_trans (s r t : session_type) :
  s ≡ r → r ≡ t → s ≡ t.
Proof.
  revert s r t. cofix IH. intros a b c Hab Hbc.
  destruct Hab; pose proof (session_equiv_observe _ _ Hbc) as Hview;
    cbn [session_equiv_view] in Hview.
  - subst c. constructor.
  - destruct Hview as (us & rs & -> & Hts & Hrs). constructor.
    + intros i. exact (runtime_type_equiv_trans _ _ _ (H i) (Hts i)).
    + intros i. exact (IH _ _ _ (H0 i) (Hrs i)).
  - destruct Hview as (us & rs & -> & Hts & Hrs). constructor.
    + intros i. exact (runtime_type_equiv_trans _ _ _ (H i) (Hts i)).
    + intros i. exact (IH _ _ _ (H0 i) (Hrs i)).
Qed.

Lemma relabel_matches_equivalent_sessions π (s r : session_type) :
  s ≡ r → relabelT π s ≡ relabelT π r.
Proof.
  revert s r. cofix IH. intros s r Hsr.
  rewrite (observe_session_type (relabelT π s)), (observe_session_type (relabelT π r)).
  destruct Hsr; cbn [session_type_id]; constructor.
  - exact H.
  - intros i. exact (IH _ _ (H0 i)).
  - exact H.
  - intros i. exact (IH _ _ (H0 i)).
Qed.

Lemma relabel_identity_session (s : session_type) : s ≡ relabelT id s.
Proof.
  revert s. cofix IH. intros s.
  rewrite (observe_session_type (relabelT id s)).
  destruct s; cbn [session_type_id]; constructor;
    intros i; first [apply runtime_type_equiv_refl|apply IH].
Qed.

Lemma relabel_compose_sessions π ρ (s : session_type) :
  relabelT π (relabelT ρ s) ≡ relabelT (π ∘ ρ) s.
Proof.
  revert s. cofix IH. intros s.
  rewrite (observe_session_type (relabelT π (relabelT ρ s))),
    (observe_session_type (relabelT (π ∘ ρ) s)).
  destruct s; cbn [session_type_id]; constructor;
    intros i; first [apply runtime_type_equiv_refl|apply IH].
Qed.


Lemma relabel_end_observation π : relabelT π EndT = EndT.
Proof. exact (observe_session_type (relabelT π EndT)). Qed.

Lemma relabel_send_observation π n p (ts : fin n → type) rs :
  relabelT π (SendT n p ts rs) = SendT n (π p) ts (relabelT π ∘ rs).
Proof. exact (observe_session_type (relabelT π (SendT n p ts rs))). Qed.

Lemma relabel_receive_observation π n p (ts : fin n → type) rs :
  relabelT π (RecvT n p ts rs) = RecvT n (π p) ts (relabelT π ∘ rs).
Proof. exact (observe_session_type (relabelT π (RecvT n p ts rs))). Qed.

Lemma runtime_empty_context_unrestricted : Γunrestricted ∅.
Proof. intros x t Hlookup. rewrite lookup_empty in Hlookup. discriminate. Qed.

Lemma runtime_pointer_protocol Σ Γ e t :
  runtime_typed Σ Γ e t →
  ∀ c q π τ, e = Val (ChanV (c,q) π) → t = ChanT τ →
    ∃ σ, Σ c !! q = Some σ ∧ σ ≡ relabelT π τ.
Proof.
  intros Htyped.
  induction Htyped; intros target_c target_q labels wanted He Ht; try discriminate.
  - subst t'.
    pose proof (type_equiv_observe _ _ (runtime_type_equiv_sym _ _ H)) as Hchan.
    cbn [type_equiv_view] in Hchan.
    destruct Hchan as (τ & -> & Hθτ).
    destruct (IHHtyped target_c target_q labels τ He eq_refl) as (σ & Hσ & Hmatch).
    exists σ. split; [exact Hσ|].
    eapply runtime_session_equiv_trans; [exact Hmatch|].
    apply relabel_matches_equivalent_sessions, runtime_session_equiv_sym, Hθτ.
  - inversion He; inversion Ht; subst. now exists σ.
Qed.

Lemma runtime_send_pointer_view Σ c q π n p (ts : fin n → type) rs :
  runtime_typed Σ ∅ (Val (ChanV (c,q) π)) (ChanT (SendT n p ts rs)) →
  ∃ us vs,
    Σ c !! q = Some (SendT n (π p) us vs) ∧
    (∀ j, ts j ≡ us j) ∧
    (∀ j, vs j ≡ relabelT π (rs j)).
Proof.
  intros Htyped.
  destruct (runtime_pointer_protocol _ _ _ _ Htyped c q π _ eq_refl eq_refl)
    as (σ & Hσ & Hequiv).
  apply runtime_session_equiv_sym in Hequiv.
  rewrite relabel_send_observation in Hequiv.
  apply session_equiv_observe in Hequiv.
  destruct Hequiv as (us & vs & -> & Hts & Hrs).
  exists us, vs. split; [exact Hσ|]. split; [exact Hts|].
  intros j. apply runtime_session_equiv_sym. exact (Hrs j).
Qed.

Lemma runtime_receive_pointer_view Σ c q π n p (ts : fin n → type) rs :
  runtime_typed Σ ∅ (Val (ChanV (c,q) π)) (ChanT (RecvT n p ts rs)) →
  ∃ us vs,
    Σ c !! q = Some (RecvT n (π p) us vs) ∧
    (∀ j, us j ≡ ts j) ∧
    (∀ j, vs j ≡ relabelT π (rs j)).
Proof.
  intros Htyped.
  destruct (runtime_pointer_protocol _ _ _ _ Htyped c q π _ eq_refl eq_refl)
    as (σ & Hσ & Hequiv).
  apply runtime_session_equiv_sym in Hequiv.
  rewrite relabel_receive_observation in Hequiv.
  apply session_equiv_observe in Hequiv.
  destruct Hequiv as (us & vs & -> & Hts & Hrs).
  exists us, vs. split; [exact Hσ|]. split.
  - intros j. exact (runtime_type_equiv_sym _ _ (Hts j)).
  - intros j. apply runtime_session_equiv_sym. exact (Hrs j).
Qed.

Lemma runtime_close_pointer_lookup Σ c q π :
  runtime_typed Σ ∅ (Val (ChanV (c,q) π)) (ChanT EndT) →
  Σ c !! q = Some EndT.
Proof.
  intros Htyped.
  destruct (runtime_pointer_protocol _ _ _ _ Htyped c q π _ eq_refl eq_refl)
    as (σ & Hσ & Hequiv).
  apply runtime_session_equiv_sym in Hequiv.
  rewrite relabel_end_observation in Hequiv.
  apply session_equiv_observe in Hequiv.
  cbn [session_equiv_view] in Hequiv. now subst σ.
Qed.

Lemma replaced_session_protocol_lookup Σ c local q :
  replace_session_protocol_map Σ c local c !! q = local !! q.
Proof. unfold replace_session_protocol_map. now rewrite decide_True by reflexivity. Qed.

Lemma typed_pointer_with_updated_protocol Σ c q π σ τ :
  σ ≡ relabelT π τ →
  runtime_typed (replace_session_protocol_map Σ c (<[q := σ]> (Σ c))) ∅
    (Val (ChanV (c,q) π)) (ChanT τ).
Proof.
  intros Hmatch. eapply Runtime_ChanV.
  - exact runtime_empty_context_unrestricted.
  - rewrite replaced_session_protocol_lookup, lookup_insert_eq. reflexivity.
  - exact Hmatch.
Qed.

Definition runtime_communication_typing_view Σ Γ e t : Prop :=
  match e with
  | Send p a i b =>
    ∃ Γ1 Γ2 n (ts : fin n → type) rs (j : fin n),
      Γ = Γ1 ∪ Γ2 ∧ i = fin_to_nat j ∧
      expr_endpoints a ## expr_endpoints b ∧
      runtime_typed Σ Γ1 a (ChanT (SendT n p ts rs)) ∧
      runtime_typed Σ Γ2 b (ts j) ∧ ChanT (rs j) ≡ t
  | Recv p a =>
    ∃ n (ts : fin n → type) rs,
      runtime_typed Σ Γ a (ChanT (RecvT n p ts rs)) ∧
      SumNT n (λ i, PairT (ChanT (rs i)) (ts i)) ≡ t
  | Close a => runtime_typed Σ Γ a (ChanT EndT) ∧ UnitT ≡ t
  | Relabel π a =>
    ∃ σ, runtime_typed Σ Γ a (ChanT (relabelT π σ)) ∧ ChanT σ ≡ t
  | _ => True
  end.

Lemma runtime_communication_typing_weaken Σ Γ e t t' :
  runtime_communication_typing_view Σ Γ e t → t ≡ t' →
  runtime_communication_typing_view Σ Γ e t'.
Proof.
  intros Hview Heq. destruct e; cbn [runtime_communication_typing_view] in *; try exact I.
  - destruct Hview as (Γ1 & Γ2 & arity & ts & rs & j & HΓ & Hi & Hsep & Ha & Hb & Ht).
    exists Γ1, Γ2, arity, ts, rs, j. split; [exact HΓ|]. split; [exact Hi|].
    split; [exact Hsep|]. split; [exact Ha|]. split; [exact Hb|].
    exact (runtime_type_equiv_trans _ _ _ Ht Heq).
  - destruct Hview as (n & ts & rs & Ha & Ht). exists n, ts, rs.
    split; [exact Ha|exact (runtime_type_equiv_trans _ _ _ Ht Heq)].
  - destruct Hview as [Ha Ht].
    split; [exact Ha|exact (runtime_type_equiv_trans _ _ _ Ht Heq)].
  - destruct Hview as (σ & Ha & Ht). exists σ.
    split; [exact Ha|exact (runtime_type_equiv_trans _ _ _ Ht Heq)].
Qed.

Lemma runtime_communication_typing_observe Σ Γ e t :
  runtime_typed Σ Γ e t → runtime_communication_typing_view Σ Γ e t.
Proof.
  intros Htyped. induction Htyped; cbn [runtime_communication_typing_view]; try exact I.
  - exists Γ1, Γ2, n, t, r, i. split; [reflexivity|]. split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    apply runtime_type_equiv_refl.
  - exists n, t, r. split; [eassumption|apply runtime_type_equiv_refl].
  - split; [eassumption|apply runtime_type_equiv_refl].
  - exists σ. split; [eassumption|apply runtime_type_equiv_refl].
  - exact (runtime_communication_typing_weaken _ _ _ _ _ IHHtyped H).
Qed.

Lemma runtime_relabel_head_preservation Σ c q π1 π2 t :
  runtime_typed Σ ∅ (Relabel π1 (Val (ChanV (c,q) π2))) t →
  runtime_typed Σ ∅ (Val (ChanV (c,q) (π2 ∘ π1))) t.
Proof.
  intros Htyped.
  destruct (runtime_communication_typing_observe _ _ _ _ Htyped)
    as (s & Hchannel & Ht).
  destruct (runtime_pointer_protocol _ _ _ _ Hchannel c q π2 _ eq_refl eq_refl)
    as (σ & Hσ & Hequiv).
  eapply Runtime_Iso; [exact Ht|].
  eapply Runtime_ChanV; [exact runtime_empty_context_unrestricted|exact Hσ|].
  eapply runtime_session_equiv_trans; [exact Hequiv|].
  apply relabel_compose_sessions.
Qed.

Lemma runtime_queued_values_change_protocols Σ Σ' entries tags :
  Forall2 (queued_entry_typed (λ v t, runtime_typed Σ ∅ (Val v) t)) entries tags →
  (∀ i v, (i,v) ∈ entries → protocols_agree_on Σ Σ' (val_endpoints v)) →
  Forall2 (queued_entry_typed (λ v t, runtime_typed Σ' ∅ (Val v) t)) entries tags.
Proof.
  intros Htyped. induction Htyped as [|[i v] [j t] entries tags Hv Htyped IH]; intros Hagree.
  - constructor.
  - constructor.
    + destruct Hv as [Hlabel Hvalue]. split; [exact Hlabel|].
      eapply runtime_typed_change_protocols; [exact Hvalue|].
      apply (Hagree i v). apply elem_of_cons. now left.
    + apply IH. intros k w Hin. apply (Hagree k w). apply elem_of_cons. now right.
Qed.

Lemma runtime_queue_typing_change_protocols Σ Σ' h c bufs :
  session_queues_typed (λ v t, runtime_typed Σ ∅ (Val v) t) h c bufs →
  protocols_agree_on Σ Σ' (heap_value_refs val_endpoints h c) →
  session_queues_typed (λ v t, runtime_typed Σ' ∅ (Val v) t) h c bufs.
Proof.
  intros Htyped Hagree. constructor.
  - exact (session_queues_domain _ _ _ _ Htyped).
  - intros q p.
    pose proof (session_queues_contents _ _ _ _ Htyped q p) as Hcontents.
    destruct (buffer_at h (c,q) p) as [entries|] eqn:Hentries;
      destruct (typed_buffer_at bufs q p) as [tags|]; try solve [inversion Hcontents].
    + inversion Hcontents; subst. constructor.
      eapply runtime_queued_values_change_protocols; [eassumption|].
      intros i v Hin. eapply protocols_agree_on_subset; [|exact Hagree].
      intros ep Hep. apply elem_of_heap_value_refs_iff.
      exists q, p, i, v. split; [|exact Hep]. now exists entries.
    + constructor.
Qed.

Lemma runtime_send_head_preservation Σ h c q π p label v t bufs :
  runtime_typed Σ ∅ (Send p (Val (ChanV (c,q) π)) label (Val v)) t →
  session_queues_typed (λ w τ, runtime_typed Σ ∅ (Val w) τ) h c bufs →
  sbufs_typed bufs (Σ c) →
  (c,q) ∉ heap_value_refs val_endpoints h c →
  ∃ σ bufs',
    let locals := <[q := σ]> (Σ c) in
    let Σ' := replace_session_protocol_map Σ c locals in
    is_present q (c,π p) h ∧
    runtime_typed Σ' ∅ (Val (ChanV (c,q) π)) t ∧
    session_queues_typed (λ w τ, runtime_typed Σ' ∅ (Val w) τ)
      (push q (c,π p) (label,v) h) c bufs' ∧
    sbufs_typed bufs' locals.
Proof.
  intros Htyped Hqueues Hsafe Hnoheap.
  destruct (runtime_communication_typing_observe _ _ _ _ Htyped)
    as (Γ1 & Γ2 & n & ts & rs & j & HΓ & Htag & Hsep & Hchannel & Hv & Ht).
  destruct (runtime_union_empty_env _ _ (eq_sym HΓ)) as [-> ->].
  subst label.
  destruct (runtime_send_pointer_view _ _ _ _ _ _ _ _ Hchannel)
    as (us & vs & Hprotocol & Hpayload & Hnext).
  assert (runtime_typed Σ ∅ (Val v) (us j)) as Hvalue.
  { eapply Runtime_Iso; [exact (Hpayload j)|exact Hv]. }
  destruct (typed_queues_allow_send (λ w τ, runtime_typed Σ ∅ (Val w) τ)
    h c bufs (Σ c) n q (π p) us vs j v Hqueues Hsafe Hprotocol Hvalue)
    as (Hpresent & Hqueues' & Hsafe').
  exists (vs j), (push q (π p) (fin_to_nat j,us j) bufs). cbn zeta.
  split; [exact Hpresent|]. split.
  - eapply Runtime_Iso; [exact Ht|].
    exact (typed_pointer_with_updated_protocol _ _ _ _ _ _ (Hnext j)).
  - split; [|exact Hsafe'].
    eapply runtime_queue_typing_change_protocols; [exact Hqueues'|].
    apply changed_endpoint_protocol_agrees_on_frame.
    intros Hnew.
    apply heap_value_refs_push in Hnew as [Hold|(_ & _ & Hvrefs)].
    + exact (Hnoheap Hold).
    + cbn [expr_endpoints val_endpoints] in Hsep. set_solver.
Qed.

Lemma runtime_receive_head_preservation Σ h c q π p label v h' t bufs :
  runtime_typed Σ ∅ (Recv p (Val (ChanV (c,q) π))) t →
  session_queues_typed (λ w τ, runtime_typed Σ ∅ (Val w) τ) h c bufs →
  sbufs_typed bufs (Σ c) →
  (c,q) ∉ heap_value_refs val_endpoints h c →
  pop (π p) (c,q) h = Some ((label,v),h') →
  ∃ σ bufs',
    let locals := <[q := σ]> (Σ c) in
    let Σ' := replace_session_protocol_map Σ c locals in
    runtime_typed Σ' ∅ (Val (InjNV label (PairV (ChanV (c,q) π) v))) t ∧
    session_queues_typed (λ w τ, runtime_typed Σ' ∅ (Val w) τ) h' c bufs' ∧
    sbufs_typed bufs' locals.
Proof.
  intros Htyped Hqueues Hsafe Hnoheap Hpop.
  destruct (runtime_communication_typing_observe _ _ _ _ Htyped)
    as (n & ts & rs & Hchannel & Ht).
  destruct (runtime_receive_pointer_view _ _ _ _ _ _ _ _ Hchannel)
    as (us & vs & Hprotocol & Hpayload & Hnext).
  destruct (typed_queues_receive_updates (λ w τ, runtime_typed Σ ∅ (Val w) τ)
    h c bufs (Σ c) (π p) q label v h' n us vs Hqueues Hsafe Hprotocol Hpop)
    as (j & bufs' & Hlabel & Hv & Hqueues' & Hsafe').
  pose proof (heap_value_refs_pop val_endpoints h c q (π p) label v h' c (c,q) Hpop) as Hrefs.
  assert ((c,q) ∉ val_endpoints v) as Hnosep.
  { intros Hin. apply Hnoheap, (proj2 Hrefs). right. now split. }
  assert ((c,q) ∉ heap_value_refs val_endpoints h' c) as Hnoheap'.
  { intros Hin. apply Hnoheap, (proj2 Hrefs). now left. }
  subst label.
  exists (vs j), bufs'. cbn zeta. split.
  - eapply Runtime_Iso; [exact Ht|].
    eapply (Runtime_InjNV _ ∅ n (λ i, PairT (ChanT (rs i)) (ts i)) j).
    + exact runtime_empty_context_unrestricted.
    + eapply Runtime_PairV.
      * exact runtime_empty_context_unrestricted.
      * cbn [val_endpoints]. set_solver.
      * exact (typed_pointer_with_updated_protocol _ _ _ _ _ _ (Hnext j)).
      * eapply Runtime_Iso; [exact (Hpayload j)|].
        eapply runtime_typed_change_protocols; [exact Hv|].
        apply changed_endpoint_protocol_agrees_on_frame. exact Hnosep.
  - split; [|exact Hsafe'].
    eapply runtime_queue_typing_change_protocols; [exact Hqueues'|].
    now apply changed_endpoint_protocol_agrees_on_frame.
Qed.

Lemma runtime_close_head_preservation Σ (h : heap) c q π t bufs :
  runtime_typed Σ ∅ (Close (Val (ChanV (c,q) π))) t →
  session_queues_typed (λ w τ, runtime_typed Σ ∅ (Val w) τ) h c bufs →
  sbufs_typed bufs (Σ c) →
  (c,q) ∉ heap_value_refs val_endpoints h c →
  let locals := delete q (Σ c) in
  let Σ' := replace_session_protocol_map Σ c locals in
  runtime_typed Σ' ∅ (Val UnitV) t ∧
  (∀ p entries, buffer_at h (c,q) p = Some entries → entries = []) ∧
  session_queues_typed (λ w τ, runtime_typed Σ' ∅ (Val w) τ)
    (delete ((c,q) : endpoint) (h : gmap endpoint (gmap participant (list entryT)))) c
    (delete q (bufs : gmap participant (gmap participant (list sentryT)))) ∧
  sbufs_typed (delete q bufs) locals.
Proof.
  intros Htyped Hqueues Hsafe Hnoheap. cbn zeta.
  destruct (runtime_communication_typing_observe _ _ _ _ Htyped) as [Hchannel Ht].
  pose proof (runtime_close_pointer_lookup _ _ _ _ Hchannel) as Hlookup.
  split.
  { eapply Runtime_Iso; [exact Ht|].
    apply Runtime_Unit, runtime_empty_context_unrestricted. }
  pose proof (typed_queues_close_empty _ _ _ _ _ _ Hqueues Hsafe Hlookup) as Hempty.
  split; [exact Hempty|]. split.
  - eapply runtime_queue_typing_change_protocols.
    + exact (session_queues_delete_matched (λ w τ, runtime_typed Σ ∅ (Val w) τ)
        h c bufs q Hqueues).
    + apply removed_endpoint_protocol_agrees_on_frame.
      intros Hchanged.
      apply Hnoheap.
      exact (proj1 (heap_value_refs_delete_empty_endpoint val_endpoints h c q c (c,q) Hempty)
        Hchanged).
  - exact (proj2 (sbufs_typed_end _ _ Hsafe q Hlookup)).
Qed.

Lemma runtime_typed_endpoints_have_protocols Σ Γ e t :
  runtime_typed Σ Γ e t →
  ∀ sid pid, (sid,pid) ∈ expr_endpoints e → is_Some (Σ sid !! pid).
Proof.
  intros Htyped. induction Htyped; intros sid pid Hmember;
    cbn [expr_endpoints val_endpoints] in Hmember.
  all: repeat match type of Hmember with
  | _ ∈ _ ∪ _ => apply elem_of_union in Hmember as [Hmember|Hmember]
  end.
  all: try solve [eauto | rewrite elem_of_empty in Hmember; contradiction].
  - apply elem_of_fin_union_iff in Hmember as (j & Hj). eauto.
  - apply elem_of_fin_union_iff in Hmember as (j & Hj). eauto.
  - apply elem_of_singleton in Hmember. inversion Hmember; subst. now exists σ.
Qed.

Lemma fresh_endpoint_protocol_map_is_empty Σ h c :
  protocol_endpoints_allocated Σ h →
  (∀ p, h !! (c,p) = None) →
  ∀ p, Σ c !! p = None.
Proof.
  intros Hallocated Hfresh p.
  destruct (Σ c !! p) as [σ|] eqn:Hσ; [|reflexivity].
  destruct (Hallocated c p σ Hσ) as (bs & Hlookup).
  rewrite Hfresh in Hlookup. discriminate.
Qed.

Lemma fresh_session_protocol_map_agrees Σ Γ e t c locals :
  runtime_typed Σ Γ e t →
  (∀ p, Σ c !! p = None) →
  protocols_agree_on Σ (replace_session_protocol_map Σ c locals) (expr_endpoints e).
Proof.
  intros Htyped Hfresh. apply replace_session_protocols_agree.
  intros p Hmember.
  destruct (runtime_typed_endpoints_have_protocols _ _ _ _ Htyped c p Hmember)
    as (σ & Hlookup).
  rewrite Hfresh in Hlookup. discriminate.
Qed.

Lemma runtime_spawn_typing_observe Σ Γ e t :
  runtime_typed Σ Γ e t →
  Γ = ∅ →
  ∀ n (f : fin n → expr), e = Spawn n f →
  ∃ σs : fin (S n) → session_type,
    consistent (S n) σs ∧
    (∀ p, runtime_typed Σ ∅ (f p) (FunT (ChanT (σs (FS p))) UnitT)) ∧
    ChanT (σs 0%fin) ≡ t.
Proof.
  intros Htyped.
  induction Htyped; intros Hempty arity workers Hspawn; try discriminate.
  - inversion Hspawn; subst.
    match goal with Heq : existT ?m ?f = existT ?m ?g |- _ =>
      apply (inj_pair2_eq_dec nat Nat.eq_dec) in Heq; (subst f || subst g)
    end.
    exists σs. split; [assumption|]. split; [|apply runtime_type_equiv_refl].
    intros p. rewrite <- (runtime_spawn_empty_env _ _ H1 p). eauto.
  - destruct (IHHtyped Hempty arity workers Hspawn) as (σs & Hconsistent & Hworkers & Ht).
    exists σs. split; [exact Hconsistent|]. split; [exact Hworkers|].
    exact (runtime_type_equiv_trans _ _ _ Ht H).
Qed.

Lemma allocated_endpoint_runtime_typing Σ c n (σs : fin n → session_type) (i : fin n) :
  runtime_typed (replace_session_protocol_map Σ c (fin_gmap n σs)) ∅
    (Val (ChanV (c,fin_to_nat i) id)) (ChanT (σs i)).
Proof.
  eapply Runtime_ChanV with (σ := σs i).
  - exact runtime_empty_context_unrestricted.
  - rewrite replaced_session_protocol_lookup, lookup_finite_map.
    now rewrite fin_list_lookup_at_index.
  - apply relabel_identity_session.
Qed.

Lemma runtime_spawn_head_preservation Σ (h : heap) c n
    (f : fin n → expr) (fv : fin n → val) t :
  runtime_typed Σ ∅ (Spawn n f) t →
  protocol_endpoints_allocated Σ h →
  (∀ p, h !! (c,p) = None) →
  (∀ p, f p = Val (fv p)) →
  ∃ σs : fin (S n) → session_type,
    let locals := fin_gmap (S n) σs in
    let Σ' := replace_session_protocol_map Σ c locals in
    runtime_typed Σ' ∅ (Val (ChanV (c,0) id)) t ∧
    (∀ e, e ∈ init_threads c n fv → runtime_typed Σ' ∅ e UnitT) ∧
    session_queues_typed (λ v τ, runtime_typed Σ' ∅ (Val v) τ)
      (gmap_unslice (init_chans (S n) : bufsT participant participant entryT) c ∪
        (h : gmap endpoint (gmap participant (list entryT)))) c
      (init_chans (S n)) ∧
    sbufs_typed (init_chans (S n)) locals.
Proof.
  intros Htyped Hallocated Hfresh Hvalues.
  destruct (runtime_spawn_typing_observe _ _ _ _ Htyped eq_refl n f eq_refl)
    as (σs & Hconsistent & Hworkers & Ht).
  pose proof (fresh_endpoint_protocol_map_is_empty Σ h c Hallocated Hfresh) as Hprotocols.
  exists σs. cbn zeta. split.
  { eapply Runtime_Iso; [exact Ht|].
    exact (allocated_endpoint_runtime_typing Σ c (S n) σs 0%fin). }
  split.
  - intros worker Hworker. unfold init_threads in Hworker.
    apply elem_of_fin_list_iff in Hworker as (p & ->).
    pose proof (Hworkers p) as Hvalue. rewrite (Hvalues p) in Hvalue.
    replace (∅ : envT) with ((∅ : envT) ∪ ∅) by apply map_empty_union.
    eapply Runtime_App.
    + cbn [expr_endpoints val_endpoints].
      apply elem_of_disjoint. intros [sid pid] Hmember Hnew.
      apply elem_of_singleton in Hnew. inversion Hnew; subst.
      destruct (runtime_typed_endpoints_have_protocols _ _ _ _ Hvalue
        c (S (fin_to_nat p)) Hmember) as (σ & Hlookup).
      rewrite Hprotocols in Hlookup. discriminate.
    + intros x t1 t2 Hlookup. rewrite lookup_empty in Hlookup. discriminate.
    + eapply runtime_typed_change_protocols; [exact Hvalue|].
      exact (fresh_session_protocol_map_agrees Σ ∅ (Val (fv p)) _ c (fin_gmap (S n) σs) Hvalue Hprotocols).
    + exact (allocated_endpoint_runtime_typing Σ c (S n) σs (FS p)).
  - split.
    + now apply initialized_session_queues_typed.
    + exact Hconsistent.
Qed.

From Stdlib Require Import Strings.String.

Definition unrestricted_type_view (t : type) : Prop :=
  match t with
  | UnitT | VoidT | NatT | UFunT _ _ => True
  | PairT a b | SumT a b => unrestricted a ∧ unrestricted b
  | SumNT _ f => ∀ i, unrestricted (f i)
  | FunT _ _ | ChanT _ => False
  end.

Lemma unrestricted_type_observe t : unrestricted t → unrestricted_type_view t.
Proof. intros Hfree; destruct Hfree; cbn [unrestricted_type_view]; auto. Qed.

Lemma unrestricted_runtime_type_equiv t u :
  unrestricted t → t ≡ u → unrestricted u.
Proof.
  revert t u. cofix IH. intros t u Hfree Heq.
  destruct Hfree; pose proof (type_equiv_observe _ _ Heq) as Hshape;
    cbn [type_equiv_view] in Hshape.
  all: try solve [subst u; constructor].
  - destruct Hshape as (a & b & -> & _ & _). constructor.
  - destruct Hshape as (a & b & -> & Ha & Hb). constructor.
    + exact (IH _ _ Hfree1 Ha).
    + exact (IH _ _ Hfree2 Hb).
  - destruct Hshape as (a & b & -> & Ha & Hb). constructor.
    + exact (IH _ _ Hfree1 Ha).
    + exact (IH _ _ Hfree2 Hb).
  - destruct Hshape as (g & -> & Hg). constructor. intros i.
    exact (IH _ _ (H i) (Hg i)).
Qed.

Lemma unrestricted_runtime_values_have_no_endpoints Σ Γ e t :
  runtime_typed Σ Γ e t →
  ∀ v, e = Val v → unrestricted t → val_endpoints v = ∅.
Proof.
  intros Htyped.
  induction Htyped; intros candidate Hval Hfree; try discriminate;
    try solve [injection Hval as <-; reflexivity].
  - apply (IHHtyped candidate Hval).
    exact (unrestricted_runtime_type_equiv _ _ Hfree (runtime_type_equiv_sym _ _ H)).
  - injection Hval as <-. cbn [val_endpoints].
    pose proof (unrestricted_type_observe _ Hfree) as [Hu Hv].
    rewrite (IHHtyped1 _ eq_refl Hu), (IHHtyped2 _ eq_refl Hv). set_solver.
  - injection Hval as <-. cbn [val_endpoints].
    pose proof (unrestricted_type_observe _ Hfree) as [Hu Hv].
    apply IHHtyped; [reflexivity|]. destruct b; assumption.
  - injection Hval as <-. cbn [val_endpoints].
    apply IHHtyped; [reflexivity|exact (unrestricted_type_observe _ Hfree i)].
  - exact (False_rect _ (unrestricted_type_observe _ Hfree)).
  - injection Hval as <-. exact H0.
  - exact (False_rect _ (unrestricted_type_observe _ Hfree)).
Qed.

Lemma runtime_value_contexts_unrestricted Σ Γ e t :
  runtime_typed Σ Γ e t →
  ∀ v, e = Val v → Γunrestricted Γ ∧
    ∀ Δ, Γunrestricted Δ → runtime_typed Σ Δ (Val v) t.
Proof.
  intros Htyped.
  induction Htyped; intros candidate Hval; try discriminate;
    try solve [injection Hval as <-; split; [eassumption|intros Δ HΔ; econstructor; eassumption]].
  destruct (IHHtyped candidate Hval) as [HΓ Hweaken].
  split; [exact HΓ|]. intros Δ HΔ.
  eapply Runtime_Iso; [exact H|now apply Hweaken].
Qed.

Lemma runtime_weaken_value_to_unrestricted_context Σ Γ v t :
  runtime_typed Σ ∅ (Val v) t →
  Γunrestricted Γ →
  runtime_typed Σ Γ (Val v) t.
Proof.
  intros Htyped.
  exact (proj2 (runtime_value_contexts_unrestricted _ _ _ _ Htyped v eq_refl) Γ).
Qed.

Definition substitution_value_matches Σ (Γ : envT) (x : string) (a : val) :=
  ∀ t, Γ !! x = Some t → runtime_typed Σ ∅ (Val a) t.

Definition substitution_endpoints (Γ : envT) (x : string) (a : val) : gset endpoint :=
  from_option (λ _, val_endpoints a) ∅ (Γ !! x).

Lemma substitution_matches_union_left Σ Γ1 Γ2 x a :
  substitution_value_matches Σ (Γ1 ∪ Γ2) x a →
  substitution_value_matches Σ Γ1 x a.
Proof.
  intros Hmatch t Hlookup. apply Hmatch.
  rewrite lookup_union, Hlookup. now destruct (Γ2 !! x).
Qed.

Lemma substitution_matches_union_right Σ Γ1 Γ2 x a :
  disj Γ1 Γ2 →
  substitution_value_matches Σ (Γ1 ∪ Γ2) x a →
  substitution_value_matches Σ Γ2 x a.
Proof.
  intros Hdis Hmatch t Hlookup.
  destruct (Γ1 !! x) as [t1|] eqn:Hleft.
  - destruct (Hdis x t1 t Hleft Hlookup) as [Htype _].
    eapply Runtime_Iso; [exact Htype|].
    exact (substitution_matches_union_left _ _ _ _ _ Hmatch _ Hleft).
  - apply Hmatch. now rewrite lookup_union_r.
Qed.

Lemma substitution_matches_other_binder Σ Γ x a y t :
  x ≠ y →
  substitution_value_matches Σ Γ x a →
  substitution_value_matches Σ (Γ ∪ {[y := t]}) x a.
Proof.
  intros Hne Hmatch τ Hlookup. apply Hmatch.
  rewrite lookup_union_l in Hlookup; [exact Hlookup|].
  apply lookup_singleton_ne. congruence.
Qed.

Lemma substitution_endpoints_unrestricted Σ Γ x a :
  Γunrestricted Γ →
  substitution_value_matches Σ Γ x a →
  substitution_endpoints Γ x a = ∅.
Proof.
  intros Hfree Hmatch. unfold substitution_endpoints.
  destruct (Γ !! x) as [t|] eqn:Hlookup; [|reflexivity].
  cbn [from_option]. eapply unrestricted_runtime_values_have_no_endpoints.
  - exact (Hmatch t Hlookup).
  - reflexivity.
  - exact (Hfree x t Hlookup).
Qed.

Lemma substitution_endpoints_union (Γ1 Γ2 : envT) x a :
  substitution_endpoints (Γ1 ∪ Γ2) x a =
  substitution_endpoints Γ1 x a ∪ substitution_endpoints Γ2 x a.
Proof.
  unfold substitution_endpoints. rewrite lookup_union.
  destruct (Γ1 !! x), (Γ2 !! x); cbn [from_option]; set_solver.
Qed.

Lemma substitution_endpoints_binder Γ x a y t :
  substitution_endpoints (Γ ∪ {[y := t]}) x a =
  if decide (x = y) then val_endpoints a else substitution_endpoints Γ x a.
Proof.
  unfold substitution_endpoints. destruct (decide (x = y)) as [->|Hne].
  - rewrite lookup_union, lookup_singleton_eq. now destruct (Γ !! y).
  - rewrite lookup_union_l; [reflexivity|].
    apply lookup_singleton_ne. congruence.
Qed.

Lemma substitution_matches_spawn_worker Σ n Γ fΓ x a :
  disj_union n Γ fΓ →
  substitution_value_matches Σ Γ x a →
  ∀ p, substitution_value_matches Σ (fΓ p) x a.
Proof.
  intros Hsplit Hmatch p t Hlookup.
  assert (fΓ p !! x ≡ Some t) as Hoptions.
  { rewrite Hlookup. constructor. apply runtime_type_equiv_refl. }
  pose proof (du_left _ _ _ Hsplit p x t Hoptions) as HΓ.
  change (option_Forall2 type_equiv (Γ !! x) (Some t)) in HΓ.
  destruct (Γ !! x) as [ty|] eqn:Hlook; inversion HΓ; subst.
  eapply Runtime_Iso; [eassumption|exact (Hmatch ty Hlook)].
Qed.

Lemma elem_of_substitution_endpoints Γ x a ep :
  ep ∈ substitution_endpoints Γ x a ↔ is_Some (Γ !! x) ∧ ep ∈ val_endpoints a.
Proof.
  unfold substitution_endpoints.
  destruct (Γ !! x) as [t|]; cbn [from_option].
  - split; [intros H; split; [now exists t|exact H]|intros [_ H]; exact H].
  - rewrite elem_of_empty. split; [contradiction|intros [(? & H) _]; discriminate].
Qed.

Lemma substitution_endpoints_spawn n Γ fΓ x a :
  disj_union n Γ fΓ →
  substitution_endpoints Γ x a = fin_union n (λ p, substitution_endpoints (fΓ p) x a).
Proof.
  intros Hsplit. apply set_eq. intro ep.
  rewrite elem_of_fin_union_iff, elem_of_substitution_endpoints. split.
  - intros ((t & Ht) & Hin).
    assert (Γ !! x ≡ Some t) as Hoptions.
    { rewrite Ht. constructor. apply runtime_type_equiv_refl. }
    destruct (du_right _ _ _ Hsplit x t Hoptions) as (p & Hp).
    change (option_Forall2 type_equiv (fΓ p !! x) (Some t)) in Hp.
    destruct (fΓ p !! x) as [u|] eqn:Hworker; inversion Hp; subst.
    exists p. apply elem_of_substitution_endpoints. split; [now exists u|exact Hin].
  - intros (p & Hp). apply elem_of_substitution_endpoints in Hp as ((t & Ht) & Hin).
    assert (fΓ p !! x ≡ Some t) as Hoptions.
    { rewrite Ht. constructor. apply runtime_type_equiv_refl. }
    pose proof (du_left _ _ _ Hsplit p x t Hoptions) as HΓ.
    change (option_Forall2 type_equiv (Γ !! x) (Some t)) in HΓ.
    destruct (Γ !! x) as [u|]; inversion HΓ; subst.
    split; [now exists u|exact Hin].
Qed.

Lemma fin_union_distributes_pointwise_union n (f g : fin n → gset endpoint) :
  fin_union n (λ p, f p ∪ g p) = fin_union n f ∪ fin_union n g.
Proof.
  apply set_eq. intros ep.
  rewrite elem_of_union, !elem_of_fin_union_iff.
  split.
  - intros (p & Hp). apply elem_of_union in Hp as [Hp|Hp]; [left|right]; now exists p.
  - intros [(p & Hp)|(p & Hp)]; exists p; apply elem_of_union; auto.
Qed.

Lemma fin_union_expand_constant n (f : fin n → gset endpoint) refs :
  (n = 0 → refs = ∅) →
  fin_union n (λ p, f p ∪ refs) = fin_union n f ∪ refs.
Proof.
  intros Hzero. rewrite fin_union_distributes_pointwise_union.
  f_equal. apply set_eq. intro ep. rewrite elem_of_fin_union_iff. split.
  - intros (p & Hin). exact Hin.
  - intros Hin. destruct n as [|n].
    + rewrite (Hzero eq_refl) in Hin. apply elem_of_empty in Hin. contradiction.
    + now exists 0%fin.
Qed.


Lemma absent_variable_adds_no_endpoints (Γ : envT) x a :
  Γ !! x = None → substitution_endpoints Γ x a = ∅.
Proof. intros Hnone. unfold substitution_endpoints. now rewrite Hnone. Qed.

Local Ltac split_substitution_context Hleft Hright :=
  match goal with
  | Hmatch : substitution_value_matches ?W (?G1 ∪ ?G2) ?x ?a,
    Hdis : disj ?G1 ?G2 |- _ =>
      pose proof (substitution_matches_union_left W G1 G2 x a Hmatch) as Hleft;
      pose proof (substitution_matches_union_right W G1 G2 x a Hdis Hmatch) as Hright
  end.

Local Ltac substitution_binary_endpoints IH1 IH2 :=
  let Hl := fresh "Hleft" in
  let Hr := fresh "Hright" in
  split_substitution_context Hl Hr;
  rewrite (IH1 Hl), (IH2 Hr), substitution_endpoints_union;
  set_solver.

Local Ltac substitution_unrestricted_endpoints :=
  match goal with
  | Hmatch : substitution_value_matches ?W ?G ?x ?a,
    Hfree : Γunrestricted ?G |- _ =>
      rewrite (substitution_endpoints_unrestricted W G x a Hfree Hmatch);
      set_solver
  end.

Lemma substitution_endpoints_exact Σ Γ e t vname vval :
  runtime_typed Σ Γ e t →
  substitution_value_matches Σ Γ vname vval →
  expr_endpoints (subst vname vval e) =
    expr_endpoints e ∪ substitution_endpoints Γ vname vval.
Proof.
  intros Htyped. induction Htyped; intros Hmatch;
    cbn [subst expr_endpoints val_endpoints].
  all: try solve [substitution_unrestricted_endpoints].
  - rewrite substitution_endpoints_binder.
    destruct (decide (vname = x)) as [Heq|Hne]; cbn [expr_endpoints val_endpoints].
    + set_solver.
    + assert (substitution_value_matches Σ Γ vname vval) as Hbase
        by (eapply substitution_matches_union_left; exact Hmatch).
      rewrite (substitution_endpoints_unrestricted _ _ _ _ H0 Hbase).
      set_solver.
  - substitution_binary_endpoints IHHtyped1 IHHtyped2.
  - substitution_binary_endpoints IHHtyped1 IHHtyped2.
  - substitution_binary_endpoints IHHtyped1 IHHtyped2.
  - destruct (decide (vname = x)) as [->|Hne]; cbn [expr_endpoints].
    + rewrite (absent_variable_adds_no_endpoints _ _ _ H). set_solver.
    + rewrite IHHtyped.
      * rewrite substitution_endpoints_binder. now rewrite decide_False.
      * now apply substitution_matches_other_binder.
  - destruct (decide (vname = x)) as [->|Hne]; cbn [expr_endpoints].
    + rewrite (absent_variable_adds_no_endpoints _ _ _ H0). set_solver.
    + rewrite IHHtyped.
      * rewrite substitution_endpoints_binder. now rewrite decide_False.
      * now apply substitution_matches_other_binder.
  - substitution_binary_endpoints IHHtyped1 IHHtyped2.
  - now apply IHHtyped.
  - split_substitution_context Hleft Hright.
    rewrite (IHHtyped1 Hleft), substitution_endpoints_union.
    destruct (decide (vname = x)) as [->|Hne].
    + rewrite (absent_variable_adds_no_endpoints _ _ _ H1). set_solver.
    + rewrite IHHtyped2 by now apply substitution_matches_other_binder.
      rewrite substitution_endpoints_binder, decide_False by exact Hne. set_solver.
  - substitution_binary_endpoints IHHtyped1 IHHtyped2.
  - split_substitution_context Hleft Hright.
    rewrite (IHHtyped1 Hleft), substitution_endpoints_union.
    destruct (decide (vname = x1 ∨ vname = x2)) as [Hshadow|Hne].
    + destruct Hshadow as [Heq|Heq]; subst vname.
      * rewrite (absent_variable_adds_no_endpoints _ _ _ H2). set_solver.
      * rewrite (absent_variable_adds_no_endpoints _ _ _ H3). set_solver.
    + assert (vname ≠ x1) as Hne1 by tauto.
      assert (vname ≠ x2) as Hne2 by tauto.
      rewrite IHHtyped2 by (apply substitution_matches_other_binder; [exact Hne2|];
        now apply substitution_matches_other_binder).
      rewrite !substitution_endpoints_binder.
      rewrite !decide_False by assumption.
      set_solver.
  - now apply IHHtyped.
  - split_substitution_context Hleft Hright.
    rewrite (IHHtyped1 Hleft), substitution_endpoints_union.
    destruct (decide (vname = x)) as [->|Hne].
    + rewrite (absent_variable_adds_no_endpoints _ _ _ H2). set_solver.
    + rewrite IHHtyped2, IHHtyped3 by now apply substitution_matches_other_binder.
      rewrite !substitution_endpoints_binder, decide_False by exact Hne.
      set_solver.
  - now apply IHHtyped.
  - split_substitution_context Hleft Hright. rewrite (IHHtyped Hleft), substitution_endpoints_union.
    assert (fin_union n (expr_endpoints ∘ (λ i, subst vname vval (fc i))) =
      fin_union n (λ i, expr_endpoints (fc i) ∪ substitution_endpoints Γ2 vname vval)) as Hcases.
    {
      apply fin_union_pointwise_eq. intro i. cbn [compose].
      match goal with IH : ∀ j, substitution_value_matches _ Γ2 _ _ → _ |- _ =>
        exact (IH i Hright)
      end.
    }
    rewrite Hcases, (fin_union_expand_constant n (expr_endpoints ∘ fc)).
    + set_solver.
    + intros Hzero. apply absent_variable_adds_no_endpoints.
      rewrite (H2 Hzero). apply lookup_empty.
  - substitution_binary_endpoints IHHtyped1 IHHtyped2.
  - assert (fin_union n (expr_endpoints ∘ (λ i, subst vname vval (f i))) =
      fin_union n (λ i, expr_endpoints (f i) ∪ substitution_endpoints (fΓ i) vname vval)) as Hworkers.
    {
      apply fin_union_pointwise_eq. intro i. cbn [compose].
      match goal with IH : ∀ j, substitution_value_matches _ (fΓ j) _ _ → _ |- _ =>
        apply IH
      end.
      eapply substitution_matches_spawn_worker; eassumption.
    }
    rewrite Hworkers, fin_union_distributes_pointwise_union.
    now rewrite <- (substitution_endpoints_spawn _ _ _ _ _ H1).
  - now apply IHHtyped.
  - now apply IHHtyped.
  - now apply IHHtyped.
Qed.

Lemma runtime_disj_delete (Γ1 Γ2 : envT) x :
  disj Γ1 Γ2 → disj (delete x Γ1) (delete x Γ2).
Proof.
  intros Hdis y t1 t2 H1 H2.
  apply lookup_delete_Some in H1 as [_ H1].
  apply lookup_delete_Some in H2 as [_ H2].
  exact (Hdis y t1 t2 H1 H2).
Qed.

Lemma runtime_unrestricted_delete (Γ : envT) x :
  Γunrestricted Γ → Γunrestricted (delete x Γ).
Proof.
  intros Hfree y t Hlookup. apply lookup_delete_Some in Hlookup as [_ Hlookup].
  exact (Hfree y t Hlookup).
Qed.

Lemma runtime_delete_binding (Γ : envT) x ty :
  Γ !! x = None → delete x (Γ ∪ {[x := ty]}) = Γ.
Proof.
  intros Hnone. rewrite delete_union, delete_singleton, (delete_id _ _ Hnone).
  now rewrite decide_True, map_union_empty.
Qed.

Lemma runtime_delete_other_binding (Γ : envT) x y ty :
  x ≠ y → delete x (Γ ∪ {[y := ty]}) = delete x Γ ∪ {[y := ty]}.
Proof.
  intros Hne. rewrite delete_union, delete_singleton_ne; congruence.
Qed.

Lemma runtime_delete_preserves_absence (Γ : envT) x y :
  Γ !! y = None → delete x Γ !! y = None.
Proof.
  intros Hnone. destruct (decide (x = y)) as [->|Hne].
  - apply lookup_delete_eq.
  - now rewrite lookup_delete_ne by congruence.
Qed.

Lemma runtime_disj_union_delete n (Γ : envT) fΓ x :
  disj_union n Γ fΓ → disj_union n (delete x Γ) (λ p, delete x (fΓ p)).
Proof.
  intros Hsplit. constructor.
  - intros p q Hne. apply runtime_disj_delete.
    exact (du_disj _ _ _ Hsplit p q Hne).
  - intros p y t Hopt. cbn in Hopt.
    destruct (decide (x = y)) as [->|Hne].
    + rewrite lookup_delete_eq in Hopt. inversion Hopt.
    + rewrite lookup_delete_ne in Hopt |- * by congruence.
      eapply du_left; eassumption.
  - intros y t Hopt.
    destruct (decide (x = y)) as [->|Hne].
    + rewrite lookup_delete_eq in Hopt. inversion Hopt.
    + rewrite lookup_delete_ne in Hopt by congruence.
      destruct (du_right _ _ _ Hsplit y t Hopt) as (p & Hp).
      exists p. cbn. now rewrite lookup_delete_ne by congruence.
Qed.

Lemma substitution_endpoints_subset_value Γ x a :
  substitution_endpoints Γ x a ⊆ val_endpoints a.
Proof.
  intros ep Hep. apply elem_of_substitution_endpoints in Hep as [_ Hep]. exact Hep.
Qed.

Lemma substitution_endpoints_separated Σ Γ1 Γ2 x a :
  disj Γ1 Γ2 →
  substitution_value_matches Σ Γ1 x a →
  substitution_endpoints Γ1 x a ## substitution_endpoints Γ2 x a.
Proof.
  intros Hdis Hmatches. apply elem_of_disjoint. intros ep H1 H2.
  apply elem_of_substitution_endpoints in H1 as [(t1 & Ht1) Hep].
  apply elem_of_substitution_endpoints in H2 as [(t2 & Ht2) _].
  destruct (Hdis x t1 t2 Ht1 Ht2) as [_ Hfree].
  pose proof (unrestricted_runtime_values_have_no_endpoints _ _ _ _
    (Hmatches t1 Ht1) a eq_refl Hfree) as Hnone.
  rewrite Hnone in Hep. now apply elem_of_empty in Hep.
Qed.

Lemma replacement_endpoints_disjoint Σ Γ1 Γ2 e1 e2 t1 t2 x a :
  runtime_typed Σ Γ1 e1 t1 →
  runtime_typed Σ Γ2 e2 t2 →
  disj Γ1 Γ2 →
  substitution_value_matches Σ Γ1 x a →
  substitution_value_matches Σ Γ2 x a →
  expr_endpoints e1 ## expr_endpoints e2 →
  val_endpoints a ## (expr_endpoints e1 ∪ expr_endpoints e2) →
  expr_endpoints (subst x a e1) ## expr_endpoints (subst x a e2).
Proof.
  intros Htyped1 Htyped2 Hdis Hmatch1 Hmatch2 Heps Hvalue.
  rewrite (substitution_endpoints_exact _ _ _ _ _ _ Htyped1 Hmatch1),
    (substitution_endpoints_exact _ _ _ _ _ _ Htyped2 Hmatch2).
  pose proof (substitution_endpoints_subset_value Γ1 x a).
  pose proof (substitution_endpoints_subset_value Γ2 x a).
  pose proof (substitution_endpoints_separated _ _ _ _ _ Hdis Hmatch1).
  set_solver.
Qed.

Lemma substitution_preserves_absent_binding Σ Γ e t x a y u :
  Γ !! y = None →
  substitution_value_matches Σ Γ x a →
  (substitution_value_matches Σ (Γ ∪ {[y := u]}) x a →
    runtime_typed Σ (delete x (Γ ∪ {[y := u]})) (subst x a e) t) →
  runtime_typed Σ (Γ ∪ {[y := u]}) e t →
  runtime_typed Σ (delete x Γ ∪ {[y := u]})
    (if decide (x = y) then e else subst x a e) t.
Proof.
  intros Hnone Hmatches IH Htyped.
  destruct (decide (x = y)) as [->|Hne].
  - now rewrite delete_id by exact Hnone.
  - rewrite <- runtime_delete_other_binding by exact Hne.
    apply IH. now apply substitution_matches_other_binder.
Qed.

Lemma substitution_closed_under_binding_endpoints Σ Γ e t x a y u :
  Γ !! y = None →
  substitution_value_matches Σ Γ x a →
  runtime_typed Σ (Γ ∪ {[y := u]}) e t →
  expr_endpoints (if decide (x = y) then e else subst x a e) =
    expr_endpoints e ∪ substitution_endpoints Γ x a.
Proof.
  intros Hnone Hmatches Htyped.
  destruct (decide (x = y)) as [->|Hne].
  - rewrite (absent_variable_adds_no_endpoints _ _ _ Hnone). set_solver.
  - rewrite (substitution_endpoints_exact _ _ _ _ _ _ Htyped)
      by now apply substitution_matches_other_binder.
    rewrite substitution_endpoints_binder. now rewrite decide_False.
Qed.

Lemma substitution_closed_under_two_bindings Σ Γ e t x a y z u w :
  Γ !! y = None → Γ !! z = None → y ≠ z →
  substitution_value_matches Σ Γ x a →
  (substitution_value_matches Σ (Γ ∪ {[y := u]} ∪ {[z := w]}) x a →
    runtime_typed Σ (delete x (Γ ∪ {[y := u]} ∪ {[z := w]})) (subst x a e) t) →
  runtime_typed Σ (Γ ∪ {[y := u]} ∪ {[z := w]}) e t →
  let body := if decide (x = y ∨ x = z) then e else subst x a e in
  runtime_typed Σ (delete x Γ ∪ {[y := u]} ∪ {[z := w]}) body t ∧
  expr_endpoints body = expr_endpoints e ∪ substitution_endpoints Γ x a.
Proof.
  intros Hy Hz Hneq Hmatches IH Htyped. cbn zeta.
  destruct (decide (x = y ∨ x = z)) as [[Heq|Heq]|Hne]; try subst x.
  - rewrite (delete_id _ _ Hy), (absent_variable_adds_no_endpoints _ _ _ Hy).
    split; [exact Htyped|set_solver].
  - rewrite (delete_id _ _ Hz), (absent_variable_adds_no_endpoints _ _ _ Hz).
    split; [exact Htyped|set_solver].
  - assert (x ≠ y) as Hny by tauto. assert (x ≠ z) as Hnz by tauto.
    assert (substitution_value_matches Σ (Γ ∪ {[y := u]} ∪ {[z := w]}) x a)
      as Hmatch2 by (apply substitution_matches_other_binder; [exact Hnz|];
        now apply substitution_matches_other_binder).
    split.
    + specialize (IH Hmatch2). rewrite !runtime_delete_other_binding in IH by assumption.
      exact IH.
    + rewrite (substitution_endpoints_exact _ _ _ _ _ _ Htyped Hmatch2),
        !substitution_endpoints_binder, !decide_False by assumption.
      reflexivity.
Qed.

Lemma combined_replacement_endpoints_disjoint Σ Γ1 Γ2 endpoints1 endpoints2 x a :
  disj Γ1 Γ2 →
  substitution_value_matches Σ Γ1 x a →
  endpoints1 ## endpoints2 →
  val_endpoints a ## (endpoints1 ∪ endpoints2) →
  (endpoints1 ∪ substitution_endpoints Γ1 x a) ##
    (endpoints2 ∪ substitution_endpoints Γ2 x a).
Proof.
  intros Hdis Hmatch Heps Hvalue.
  pose proof (substitution_endpoints_subset_value Γ1 x a).
  pose proof (substitution_endpoints_subset_value Γ2 x a).
  pose proof (substitution_endpoints_separated _ _ _ _ _ Hdis Hmatch).
  set_solver.
Qed.

Local Ltac substitution_simple_binary rule IH1 IH2 :=
  let Hl := fresh "Hleft" in
  let Hr := fresh "Hright" in
  split_substitution_context Hl Hr;
  rewrite delete_union;
  eapply rule;
    [eapply replacement_endpoints_disjoint; eassumption
    |now apply runtime_disj_delete
    |apply IH1; [exact Hl|set_solver]
    |apply IH2; [exact Hr|set_solver]].

Lemma runtime_substitution_preserves_typing Σ Γ e t x a :
  runtime_typed Σ Γ e t →
  substitution_value_matches Σ Γ x a →
  val_endpoints a ## expr_endpoints e →
  runtime_typed Σ (delete x Γ) (subst x a e) t.
Proof.
  intros Htyped. induction Htyped; intros Hmatch Hvalue;
    cbn [subst expr_endpoints val_endpoints] in *.
  all: try solve [econstructor; try eassumption; now apply runtime_unrestricted_delete].
  - destruct (decide (x = x0)) as [->|Hne].
    + rewrite runtime_delete_binding by exact H.
      apply runtime_weaken_value_to_unrestricted_context; [|exact H0].
      eapply Runtime_Iso; [exact H1|].
      apply Hmatch. rewrite lookup_union_r by exact H. apply lookup_singleton_eq.
    + rewrite runtime_delete_other_binding by exact Hne.
      apply Runtime_Var.
      * now apply runtime_delete_preserves_absence.
      * now apply runtime_unrestricted_delete.
      * exact H1.
  - substitution_simple_binary Runtime_Pair IHHtyped1 IHHtyped2.
  - substitution_simple_binary Runtime_App IHHtyped1 IHHtyped2.
  - substitution_simple_binary Runtime_UApp IHHtyped1 IHHtyped2.
  - destruct (decide (x = x0)) as [->|Hne].
    + rewrite delete_id by exact H. now apply Runtime_Lam.
    + apply Runtime_Lam; [now apply runtime_delete_preserves_absence|].
      rewrite <- runtime_delete_other_binding by exact Hne.
      apply IHHtyped; [now apply substitution_matches_other_binder|exact Hvalue].
  - destruct (decide (x = x0)) as [->|Hne].
    + rewrite delete_id by exact H0. now apply Runtime_ULam.
    + apply Runtime_ULam.
      * assert (substitution_value_matches Σ (Γ ∪ {[x0 := t1]}) x a) as Hbody
          by now apply substitution_matches_other_binder.
        rewrite (substitution_endpoints_exact _ _ _ _ _ _ Htyped Hbody),
          substitution_endpoints_binder, decide_False by exact Hne.
        rewrite (substitution_endpoints_unrestricted _ _ _ _ H1 Hmatch), H.
        set_solver.
      * now apply runtime_delete_preserves_absence.
      * now apply runtime_unrestricted_delete.
      * rewrite <- runtime_delete_other_binding by exact Hne.
        apply IHHtyped; [now apply substitution_matches_other_binder|exact Hvalue].
  - substitution_simple_binary Runtime_Send IHHtyped1 IHHtyped2.
  - now apply Runtime_Recv, IHHtyped.
  - split_substitution_context Hleft Hright.
    assert (runtime_typed Σ (delete x Γ2 ∪ {[x0 := t1]})
      (if decide (x = x0) then e2 else subst x a e2) t2) as Hbody.
    { eapply substitution_preserves_absent_binding; try eassumption.
      intros Hmatches. apply IHHtyped2; [exact Hmatches|set_solver]. }
    rewrite delete_union. eapply Runtime_Let.
    + rewrite (substitution_endpoints_exact _ _ _ _ _ _ Htyped1 Hleft),
        (substitution_closed_under_binding_endpoints _ _ _ _ _ _ _ _ H1 Hright Htyped2).
      eapply combined_replacement_endpoints_disjoint; eassumption.
    + now apply runtime_disj_delete.
    + now apply runtime_delete_preserves_absence.
    + apply IHHtyped1; [exact Hleft|set_solver].
    + exact Hbody.
  - substitution_simple_binary Runtime_LetUnit IHHtyped1 IHHtyped2.
  - split_substitution_context Hleft Hright.
    destruct (substitution_closed_under_two_bindings Σ Γ2 e2 t2 x a x1 x2 t11 t12
      H2 H3 H1 Hright) as [Hbody Hendpoints].
    { intros Hmatches. apply IHHtyped2; [exact Hmatches|set_solver]. }
    { exact Htyped2. }
    rewrite delete_union. eapply Runtime_LetProd.
    + rewrite (substitution_endpoints_exact _ _ _ _ _ _ Htyped1 Hleft), Hendpoints.
      eapply combined_replacement_endpoints_disjoint; eassumption.
    + now apply runtime_disj_delete.
    + exact H1.
    + now apply runtime_delete_preserves_absence.
    + now apply runtime_delete_preserves_absence.
    + apply IHHtyped1; [exact Hleft|set_solver].
    + exact Hbody.
  - now apply Runtime_MatchVoid, IHHtyped.
  - split_substitution_context Hleft Hright.
    pose proof (substitution_closed_under_binding_endpoints _ _ _ _ _ _ _ _ H2 Hright Htyped2)
      as HepL.
    pose proof (substitution_closed_under_binding_endpoints _ _ _ _ _ _ _ _ H2 Hright Htyped3)
      as HepR.
    rewrite delete_union. eapply Runtime_MatchSum.
    + now rewrite HepL, HepR, H.
    + rewrite (substitution_endpoints_exact _ _ _ _ _ _ Htyped1 Hleft), HepL.
      eapply combined_replacement_endpoints_disjoint; try eassumption. set_solver.
    + now apply runtime_disj_delete.
    + now apply runtime_delete_preserves_absence.
    + apply IHHtyped1; [exact Hleft|set_solver].
    + eapply substitution_preserves_absent_binding; try eassumption.
      intros Hmatches. apply IHHtyped2; [exact Hmatches|set_solver].
    + eapply substitution_preserves_absent_binding; try eassumption.
      intros Hmatches. apply IHHtyped3; [exact Hmatches|set_solver].
  - now apply Runtime_InjN, IHHtyped.
  - split_substitution_context Hleft Hright.
    assert (∀ i, val_endpoints a ## expr_endpoints (fc i)) as Hcase.
    {
      intros i. apply elem_of_disjoint. intros ep Hep Hin.
      rewrite elem_of_disjoint in Hvalue. apply (Hvalue ep Hep).
      apply elem_of_union_r, elem_of_fin_union_iff. now exists i.
    }
    rewrite delete_union. eapply Runtime_MatchSumN with (f := f).
    + intros i j.
      match goal with
      | Hbranches : ∀ p, runtime_typed _ Γ2 (fc p) _ |- _ =>
          rewrite (substitution_endpoints_exact _ _ _ _ _ _ (Hbranches i) Hright),
            (substitution_endpoints_exact _ _ _ _ _ _ (Hbranches j) Hright)
      end.
      now rewrite (H i j).
    + intros i. eapply replacement_endpoints_disjoint; try solve [eauto].
      pose proof (Hcase i).
      assert (val_endpoints a ## expr_endpoints e) by set_solver.
      set_solver.
    + now apply runtime_disj_delete.
    + intros Hzero. rewrite (H2 Hzero). apply delete_empty.
    + apply IHHtyped; [exact Hleft|set_solver].
    + intros i. eauto.
  - split_substitution_context Hleft Hright.
    rewrite delete_union. eapply Runtime_If.
    + rewrite (substitution_endpoints_exact _ _ _ _ _ _ Htyped2 Hright),
        (substitution_endpoints_exact _ _ _ _ _ _ Htyped3 Hright).
      now rewrite H.
    + eapply replacement_endpoints_disjoint; eassumption.
    + now apply runtime_disj_delete.
    + apply IHHtyped1; [exact Hleft|set_solver].
    + apply IHHtyped2; [exact Hright|set_solver].
    + apply IHHtyped3; [exact Hright|set_solver].
  - pose proof (substitution_matches_spawn_worker _ _ _ _ _ _ H1 Hmatch) as Hworker.
    assert (∀ p, val_endpoints a ## expr_endpoints (f p)) as Hworker_disj.
    {
      intros p. apply elem_of_disjoint. intros ep Hep Hin.
      rewrite elem_of_disjoint in Hvalue. apply (Hvalue ep Hep).
      apply elem_of_fin_union_iff. now exists p.
    }
    eapply Runtime_Spawn with (fΓ := λ p, delete x (fΓ p)).
    + intros p q Hne.
      match goal with
      | Htyped_workers : ∀ j, runtime_typed _ (fΓ j) (f j) _ |- _ =>
          rewrite (substitution_endpoints_exact _ _ _ _ _ _ (Htyped_workers p) (Hworker p)),
            (substitution_endpoints_exact _ _ _ _ _ _ (Htyped_workers q) (Hworker q))
      end.
      eapply combined_replacement_endpoints_disjoint.
      * exact (du_disj _ _ _ H1 p q Hne).
      * apply Hworker.
      * now apply H.
      * pose proof (Hworker_disj p). pose proof (Hworker_disj q). set_solver.
    + exact H0.
    + now apply runtime_disj_union_delete.
    + intros p. eauto.
  - now apply Runtime_Close, IHHtyped.
  - now apply Runtime_Relabel, IHHtyped.
  - eapply Runtime_Iso; [exact H|now apply IHHtyped].
Qed.

Definition spawn_source_has_context n (f : fin n → expr) :=
  ∃ p fallback e, f = (λ q, if decide (p = q) then e else fallback q).

Lemma spawn_source_head_or_context n (f : fin n → expr) k e h e' h' ts :
  Spawn n f = k e →
  ctx k →
  head_step e h e' h' ts →
  (∀ p, ∃ v, f p = Val v) ∨ spawn_source_has_context n f.
Proof.
  intros Hsrc Hctx Hhead.
  destruct Hctx as [|k1 k2 Hframe Hctx]; cbn beta in Hsrc.
  - subst e. left.
    inversion Hhead; subst.
    + match goal with Hpure : pure_step (Spawn _ _) _ |- _ => inversion Hpure end.
    + apply (inj_pair2_eq_dec _ Nat.eq_dec) in H0. subst f1.
      intros p. eauto.
  - destruct Hframe; cbn beta in Hsrc; try discriminate.
    right. unfold spawn_source_has_context.
    injection Hsrc as -> Heq.
    apply (inj_pair2_eq_dec _ Nat.eq_dec) in Heq.
    eauto.
Qed.

Lemma closed_spawn_progress_requires_context n (f : fin n → expr) :
  fully_reachable [Close (Spawn n f)] ∅ →
  (∀ p, ∃ v, f p = Val v) ∨ spawn_source_has_context n f.
Proof.
  intros Hreach.
  assert (active [Close (Spawn n f)] ∅ (Thread 0)) as Hactive.
  { exists (Close (Spawn n f)). split; [reflexivity|discriminate]. }
  destruct (proj1 (empty_heap_full_reachability_iff_progress _) Hreach 0 Hactive)
    as (es' & h' & Hstep).
  inversion Hstep as [src dst heap0 heap1 i ts es Hctx_step Hlookup]; subst.
  change (Some (Close (Spawn n f)) = Some src) in Hlookup.
  injection Hlookup as <-.
  inversion Hctx_step as [k e heap0 e' heap1 ts0 Hctx Hhead Hsource]; subst.
  destruct Hctx as [|k1 k2 Hframe Hctx]; cbn beta in Hsource.
  - subst e. inversion Hhead; subst.
    + match goal with Hpure : pure_step (Close _) _ |- _ => inversion Hpure end.
  - destruct Hframe; cbn beta in Hsource; try discriminate.
    injection Hsource as Hsource.
    eapply spawn_source_head_or_context; [symmetry; exact Hsource|exact Hctx|exact Hhead].
Qed.


Lemma terminated_session_empty_queues bufs (locals : gmap participant session_type) :
  (∀ p σ, locals !! p = Some σ → σ = EndT) →
  (∀ p, buf_empty bufs p) →
  (dom bufs : gset participant) = dom locals →
  sbufs_typed bufs locals.
Proof.
  revert bufs locals. cofix IH. intros bufs locals Hend Hempty Hdom.
  constructor.
  - intros n p q ts ss i Hlookup.
    specialize (Hend _ _ Hlookup). discriminate.
  - intros bufs' n p q t i ts ss Hlookup Hpop.
    specialize (Hend _ _ Hlookup). discriminate.
  - intros p Hlookup. split; [apply Hempty|].
    apply IH.
    + intros q σ Hsome. apply lookup_delete_Some in Hsome as [_ Hsome].
      eapply Hend; exact Hsome.
    + intros q bs Hsome. apply lookup_delete_Some in Hsome as [_ Hsome].
      exact (Hempty q bs Hsome).
    + now rewrite !dom_delete_L, Hdom.
  - destruct (decide (bufs = ∅)) as [Heq|Hne]; [now left|right].
    destruct (map_choose bufs Hne) as (q & bs & Hlookup).
    assert (q ∈ (dom locals : gset participant)) as Hmember.
    { rewrite <- Hdom. apply elem_of_dom. now exists bs. }
    apply elem_of_dom in Hmember as (σ & Hσ).
    rewrite (Hend _ _ Hσ) in Hσ. exists q, EndT. auto.
  - exact Hdom.
Qed.

Lemma all_end_protocol_consistent n : consistent n (λ _, EndT).
Proof.
  apply terminated_session_empty_queues.
  - intros p σ Hsome. apply lookup_finite_constant in Hsome as [-> _]. reflexivity.
  - unfold init_chans, buf_empty. intros p bs Hlook q buf Hbuf.
    apply lookup_finite_constant in Hlook as [-> _].
    now apply lookup_finite_constant in Hbuf as [-> _].
  - apply set_eq. intro p. rewrite !elem_of_dom.
    change (is_Some (fin_gmap n (λ _, fin_gmap n (λ _, [] : list sentryT)) !! p) ↔
      is_Some (fin_gmap n (λ _, EndT : session_type) !! p)).
    rewrite !lookup_finite_constant_option.
    destruct (decide (p < n)); split; intros [value Hvalue]; try discriminate; eauto.
Qed.


Definition closing_spawn_worker : expr :=
  Lam "channel"%string (Close (Var "channel"%string)).

Lemma closing_spawn_worker_typed :
  typed ∅ closing_spawn_worker (FunT (ChanT EndT) UnitT).
Proof.
  unfold closing_spawn_worker. apply Lam_typed; [apply lookup_empty|].
  apply Close_typed, Var_typed; try apply lookup_empty.
  - intros x t Hsome. rewrite lookup_empty in Hsome. discriminate.
  - apply runtime_type_equiv_refl.
Qed.

Lemma singleton_closing_spawn_typed :
  typed ∅ (Close (Spawn 1 (λ _, closing_spawn_worker))) UnitT.
Proof.
  apply Close_typed.
  eapply Spawn_typed with (σs := λ _, EndT) (fΓ := λ _, ∅).
  - apply all_end_protocol_consistent.
  - constructor.
    + intros p q Hneq x t1 t2 Hlook. rewrite lookup_empty in Hlook. discriminate.
    + intros p x t Hlook. exact Hlook.
    + intros x t Hlook. exists 0%fin. exact Hlook.
  - intros p. apply closing_spawn_worker_typed.
Qed.

Lemma initial_singleton_spawn_requires_function_equality :
  (∀ e es h, typed ∅ e UnitT → steps [e] ∅ es h →
    deadlock_free es h ∧ fully_reachable es h) →
  ∃ p (fallback : fin 1 → expr),
    (λ _ : fin 1, closing_spawn_worker) =
    (λ q, if decide (p = q) then closing_spawn_worker else fallback q).
Proof.
  intros Hmain.
  destruct (Hmain _ _ _ singleton_closing_spawn_typed (Empty_step _ _)) as [_ Hfull].
  destruct (closed_spawn_progress_requires_context _ _ Hfull) as [Hvalue|Hctx].
  - destruct (Hvalue 0%fin) as [v Hv]. discriminate.
  - destruct Hctx as (p & fallback & e & Heq).
    pose proof (f_equal (λ f : fin 1 → expr, f p) Heq) as Hfocus.
    cbn beta in Hfocus. rewrite decide_True in Hfocus by reflexivity.
    subst e. now exists p, fallback.
Qed.

Definition runtime_function_body Σ (x : string) e input result : Prop :=
  ∃ binder, input ≡ binder ∧ runtime_typed Σ {[x := binder]} e result.

Definition runtime_pure_value_view Σ (v : val) (t : type) : Prop :=
  match v, t with
  | PairV a b, PairT u w =>
      val_endpoints a ## val_endpoints b ∧
      runtime_typed Σ ∅ (Val a) u ∧ runtime_typed Σ ∅ (Val b) w
  | InjV b v, SumT u w =>
      runtime_typed Σ ∅ (Val v) (if b then u else w)
  | InjNV label v, SumNT n f =>
      ∃ i : fin n, label = fin_to_nat i ∧ runtime_typed Σ ∅ (Val v) (f i)
  | FunV x e, FunT input result => runtime_function_body Σ x e input result
  | UFunV x e, UFunT input result => runtime_function_body Σ x e input result
  | _, _ => True
  end.

Lemma runtime_function_body_equiv Σ x e a b u w :
  a ≡ b → u ≡ w →
  runtime_function_body Σ x e a u → runtime_function_body Σ x e b w.
Proof.
  intros Hab Huw (binder & Hbinder & Hbody).
  exists binder. split.
  - eapply runtime_type_equiv_trans; [exact (runtime_type_equiv_sym _ _ Hab)|exact Hbinder].
  - eapply Runtime_Iso; eassumption.
Qed.

Lemma runtime_pure_value_view_equiv Σ v t u :
  t ≡ u → runtime_pure_value_view Σ v t → runtime_pure_value_view Σ v u.
Proof.
  intros Htype Hvalue. destruct Htype; destruct v; cbn [runtime_pure_value_view] in *; try exact I.
  - destruct Hvalue as [Hsep [Hleft Hright]].
    split; [exact Hsep|]. split; eapply Runtime_Iso; eassumption.
  - destruct b; eapply Runtime_Iso; eassumption.
  - destruct Hvalue as (i & Hi & Hv). exists i. split; [exact Hi|].
    eapply Runtime_Iso; [exact (H i)|exact Hv].
  - eapply runtime_function_body_equiv; eassumption.
  - eapply runtime_function_body_equiv; eassumption.
Qed.

Lemma runtime_pure_value_observe Σ Γ e t :
  runtime_typed Σ Γ e t →
  ∀ v, e = Val v → runtime_pure_value_view Σ v t.
Proof.
  intros Htyped. induction Htyped; intros candidate Hval; try discriminate;
    try solve [injection Hval as <-; cbn [runtime_pure_value_view]; eauto].
  - eapply runtime_pure_value_view_equiv; [exact H|now apply IHHtyped].
  - injection Hval as <-. exists t. split; [apply runtime_type_equiv_refl|exact Htyped].
  - injection Hval as <-. exists t. split; [apply runtime_type_equiv_refl|exact Htyped].
Qed.

Lemma runtime_substitution_under_singleton Σ x t e u a :
  runtime_typed Σ {[x := t]} e u →
  runtime_typed Σ ∅ (Val a) t →
  val_endpoints a ## expr_endpoints e →
  runtime_typed Σ ∅ (subst x a e) u.
Proof.
  intros Hbody Ha Hsep.
  assert (substitution_value_matches Σ {[x := t]} x a) as Hmatch.
  { intros ty Hty. rewrite lookup_singleton_eq in Hty. injection Hty as <-. exact Ha. }
  pose proof (runtime_substitution_preserves_typing _ _ _ _ _ _ Hbody Hmatch Hsep) as Htyped.
  rewrite delete_singleton, decide_True in Htyped by reflexivity. exact Htyped.
Qed.

Lemma closed_runtime_apply_function_body Σ x e input result a :
  runtime_function_body Σ x e input result →
  runtime_typed Σ ∅ (Val a) input →
  expr_endpoints e ## val_endpoints a →
  runtime_typed Σ ∅ (subst x a e) result.
Proof.
  intros (binder & Hequiv & Hbody) Hvalue Hdis.
  eapply runtime_substitution_under_singleton; [exact Hbody| |set_solver].
  eapply Runtime_Iso; eassumption.
Qed.

Lemma runtime_substitute_two_closed_values Σ x y a b t u e result :
  x ≠ y →
  runtime_typed Σ ({[x := t]} ∪ {[y := u]}) e result →
  runtime_typed Σ ∅ (Val a) t →
  runtime_typed Σ ∅ (Val b) u →
  val_endpoints a ## val_endpoints b →
  (val_endpoints a ∪ val_endpoints b) ## expr_endpoints e →
  runtime_typed Σ ∅ (subst x a (subst y b e)) result.
Proof.
  intros Hne Hbody Ha Hb Hsep Hdis.
  assert (substitution_value_matches Σ ({[x := t]} ∪ {[y := u]}) y b) as Hmatch.
  {
    intros ty Hlook.
    rewrite lookup_union_r in Hlook by (apply lookup_singleton_ne; congruence).
    rewrite lookup_singleton_eq in Hlook. injection Hlook as <-. exact Hb.
  }
  eapply runtime_substitution_under_singleton; [|exact Ha|].
  - pose proof (runtime_substitution_preserves_typing _ _ _ _ _ _
      Hbody Hmatch ltac:(set_solver)) as Hinner.
    rewrite runtime_delete_binding in Hinner by (apply lookup_singleton_ne; congruence).
    exact Hinner.
  - pose proof (proj2 (subst_endpoint_bounds y b e)). set_solver.
Qed.

Local Ltac close_runtime_binary_environments :=
  match goal with
  | Hclosed : ?Γ1 ∪ ?Γ2 = ∅ |- _ =>
      destruct (runtime_union_empty_env Γ1 Γ2 Hclosed) as [-> ->]
  end.

Local Ltac observe_runtime_value Htyped Hview :=
  pose proof (runtime_pure_value_observe _ _ _ _ Htyped _ eq_refl) as Hview;
  cbn [runtime_pure_value_view] in Hview.

Lemma closed_runtime_pure_head_preservation Σ Γ e t :
  runtime_typed Σ Γ e t →
  Γ = ∅ →
  ∀ e', pure_step e e' → runtime_typed Σ ∅ e' t.
Proof.
  intros Htyped. induction Htyped; intros Hclosed e' Hstep.
  all: try solve [inversion Hstep].
  - close_runtime_binary_environments. inversion Hstep; subst.
    eapply Runtime_PairV; try eassumption.
    exact runtime_empty_context_unrestricted.
  - close_runtime_binary_environments. inversion Hstep; subst.
    observe_runtime_value Htyped1 Hbody.
    eapply closed_runtime_apply_function_body; eassumption.
  - close_runtime_binary_environments. inversion Hstep; subst.
    observe_runtime_value Htyped1 Hbody.
    eapply closed_runtime_apply_function_body; eassumption.
  - subst Γ. inversion Hstep; subst.
    rewrite map_empty_union in Htyped.
    eapply Runtime_FunV; [exact runtime_empty_context_unrestricted|exact Htyped].
  - subst Γ. inversion Hstep; subst.
    rewrite map_empty_union in Htyped.
    eapply Runtime_UFunV; [exact runtime_empty_context_unrestricted|exact H|exact Htyped].
  - close_runtime_binary_environments. inversion Hstep; subst.
    rewrite map_empty_union in Htyped2.
    eapply runtime_substitution_under_singleton; eassumption.
  - close_runtime_binary_environments. inversion Hstep; subst.
    exact Htyped2.
  - close_runtime_binary_environments. inversion Hstep; subst.
    rewrite map_empty_union in Htyped2.
    observe_runtime_value Htyped1 Hpair.
    destruct Hpair as [HpairSep [Hv1 Hv2]].
    eapply runtime_substitute_two_closed_values; eassumption.
  - close_runtime_binary_environments. inversion Hstep; subst.
    rewrite map_empty_union in Htyped2, Htyped3.
    observe_runtime_value Htyped1 Hsum.
    destruct b.
    + eapply runtime_substitution_under_singleton; eassumption.
    + eapply runtime_substitution_under_singleton; try eassumption.
      now rewrite <- H.
  - subst Γ. inversion Hstep; subst.
    eapply Runtime_InjNV; [exact runtime_empty_context_unrestricted|exact Htyped].
  - close_runtime_binary_environments. inversion Hstep; subst.
    match goal with
    | Hworkers : existT ?n ?left = existT ?n ?right |- _ =>
        apply (inj_pair2_eq_dec nat Nat.eq_dec) in Hworkers; subst left
    end.
    observe_runtime_value Htyped Hsum.
    destruct Hsum as (j & Hj & Hv).
    apply fin_to_nat_inj in Hj. subst j.
    rewrite <- (map_empty_union (∅ : envT)).
    eapply Runtime_App; try eassumption.
    + match goal with
      | |- expr_endpoints (_ ?idx) ## _ => specialize (H0 idx)
      end. cbn [expr_endpoints val_endpoints] in *. set_solver.
    + eauto.
  - close_runtime_binary_environments. inversion Hstep; subst; assumption.
  - subst Γ. inversion Hstep; subst.
    eapply runtime_relabel_head_preservation. apply Runtime_Relabel. exact Htyped.
  - eapply Runtime_Iso; [exact H|]. now apply IHHtyped.
Qed.

Lemma runtime_substitution_singleton_endpoints Σ x t body u a :
  runtime_typed Σ {[x := t]} body u →
  runtime_typed Σ ∅ (Val a) t →
  expr_endpoints (subst x a body) = expr_endpoints body ∪ val_endpoints a.
Proof.
  intros Hbody Hvalue.
  rewrite (substitution_endpoints_exact _ _ _ _ _ _ Hbody).
  - unfold substitution_endpoints. now rewrite lookup_singleton_eq.
  - intros ty Hty. rewrite lookup_singleton_eq in Hty. now injection Hty as <-.
Qed.

Lemma runtime_application_endpoints Σ x body input result a :
  runtime_function_body Σ x body input result →
  runtime_typed Σ ∅ (Val a) input →
  expr_endpoints (subst x a body) = expr_endpoints body ∪ val_endpoints a.
Proof.
  intros (binder & Htype & Hbody) Hvalue.
  eapply runtime_substitution_singleton_endpoints; [exact Hbody|].
  eapply Runtime_Iso; eassumption.
Qed.

Lemma runtime_two_substitutions_endpoints Σ x y a b t u body result :
  x ≠ y →
  runtime_typed Σ ({[x := t]} ∪ {[y := u]}) body result →
  runtime_typed Σ ∅ (Val a) t →
  runtime_typed Σ ∅ (Val b) u →
  val_endpoints b ## expr_endpoints body →
  expr_endpoints (subst x a (subst y b body)) =
    expr_endpoints body ∪ val_endpoints a ∪ val_endpoints b.
Proof.
  intros Hne Hbody Ha Hb Hsep.
  assert (substitution_value_matches Σ ({[x := t]} ∪ {[y := u]}) y b) as Hmatch.
  {
    intros ty Hlook.
    rewrite lookup_union_r in Hlook by (apply lookup_singleton_ne; congruence).
    rewrite lookup_singleton_eq in Hlook. now injection Hlook as <-.
  }
  pose proof (runtime_substitution_preserves_typing _ _ _ _ _ _
    Hbody Hmatch Hsep) as Hinner.
  rewrite runtime_delete_binding in Hinner by (apply lookup_singleton_ne; congruence).
  rewrite (runtime_substitution_singleton_endpoints _ _ _ _ _ _ Hinner Ha),
    (substitution_endpoints_exact _ _ _ _ _ _ Hbody Hmatch).
  unfold substitution_endpoints.
  rewrite lookup_union_r by (apply lookup_singleton_ne; congruence).
  rewrite lookup_singleton_eq. cbn [from_option]. set_solver.
Qed.

Local Ltac simplify_pure_endpoint_step Hstep :=
  inversion Hstep; subst; cbn [expr_endpoints val_endpoints]; reflexivity.

Lemma closed_runtime_pure_exact_endpoints Σ Γ e t :
  runtime_typed Σ Γ e t →
  Γ = ∅ →
  ∀ e', pure_step e e' → expr_endpoints e' = expr_endpoints e.
Proof.
  intros Htyped. induction Htyped; intros Hclosed e' Hstep.
  all: try solve [simplify_pure_endpoint_step Hstep].
  - close_runtime_binary_environments. inversion Hstep; subst.
    observe_runtime_value Htyped1 Hbody.
    cbn [expr_endpoints val_endpoints].
    eapply runtime_application_endpoints; eassumption.
  - close_runtime_binary_environments. inversion Hstep; subst.
    observe_runtime_value Htyped1 Hbody.
    cbn [expr_endpoints val_endpoints].
    eapply runtime_application_endpoints; eassumption.
  - close_runtime_binary_environments. inversion Hstep; subst.
    rewrite map_empty_union in Htyped2.
    rewrite (runtime_substitution_singleton_endpoints _ _ _ _ _ _ Htyped2 Htyped1).
    cbn [expr_endpoints val_endpoints]. set_solver.
  - inversion Hstep; subst. cbn [expr_endpoints val_endpoints]. set_solver.
  - close_runtime_binary_environments. inversion Hstep; subst.
    rewrite map_empty_union in Htyped2.
    observe_runtime_value Htyped1 Hpair.
    destruct Hpair as [_ [Hv1 Hv2]].
    rewrite (runtime_two_substitutions_endpoints _ _ _ _ _ _ _ _ _ H1 Htyped2 Hv1 Hv2)
      by (cbn [expr_endpoints val_endpoints] in H; set_solver).
    cbn [expr_endpoints val_endpoints]. set_solver.
  - close_runtime_binary_environments. inversion Hstep; subst.
    rewrite map_empty_union in Htyped2, Htyped3.
    observe_runtime_value Htyped1 Hsum.
    destruct b; cbn [expr_endpoints val_endpoints] in *.
    + rewrite (runtime_substitution_singleton_endpoints _ _ _ _ _ _ Htyped2 Hsum).
      set_solver.
    + rewrite (runtime_substitution_singleton_endpoints _ _ _ _ _ _ Htyped3 Hsum).
      set_solver.
  - inversion Hstep; subst.
    match goal with
    | Hworkers : existT ?n ?left = existT ?n ?right |- _ =>
        apply (inj_pair2_eq_dec nat Nat.eq_dec) in Hworkers; subst left
    end.
    cbn [expr_endpoints val_endpoints].
    match goal with
    | |- expr_endpoints (?branches ?idx) ∪ _ = _ =>
        replace (fin_union n (expr_endpoints ∘ branches))
          with (expr_endpoints (branches idx))
    end.
    + set_solver.
    + apply set_eq. intros ep. rewrite elem_of_fin_union_iff. cbn [compose].
      split.
      * intros Hin. eauto.
      * intros (j & Hj). erewrite H; exact Hj.
  - inversion Hstep; subst; cbn [expr_endpoints val_endpoints]; set_solver.
  - now apply IHHtyped.
Qed.


Lemma closed_runtime_context_pure_preservation Σ k e e' t :
  ctx k →
  runtime_typed Σ ∅ (k e) t →
  pure_step e e' →
  runtime_typed Σ ∅ (k e') t ∧ expr_endpoints (k e') = expr_endpoints (k e).
Proof.
  intros Hctx Htyped Hstep.
  destruct (runtime_typing_context_frame _ _ _ _ _ Hctx Htyped)
    as (Γ & τ & Hhole & Hclosed & Hsep & Hframe).
  specialize (Hclosed eq_refl). subst Γ.
  pose proof (closed_runtime_pure_exact_endpoints _ _ _ _ Hhole eq_refl _ Hstep) as Hrefs.
  split.
  - apply Hframe.
    + intros ep Hep. reflexivity.
    + now rewrite Hrefs.
    + exact (closed_runtime_pure_head_preservation _ _ _ _ Hhole eq_refl _ Hstep).
  - now rewrite (ctx_endpoint_split k e' Hctx), (ctx_endpoint_split k e Hctx), Hrefs.
Qed.

Lemma pure_thread_reduction_preserves_typing_and_ownership Σ es h i k e e' :
  ctx k →
  es !! i = Some (k e) →
  pure_step e e' →
  (∀ j a, es !! j = Some a → runtime_typed Σ ∅ a UnitT) →
  let es' := <[i := k e']> es in
  (∀ j a, es' !! j = Some a → runtime_typed Σ ∅ a UnitT) ∧
  (∀ x, object_endpoints es' h x = object_endpoints es h x).
Proof.
  intros Hctx Hlook Hstep Hthreads. cbn zeta.
  destruct (closed_runtime_context_pure_preservation _ _ _ _ _ Hctx
    (Hthreads i _ Hlook) Hstep) as [Htyped Hrefs].
  pose proof (update_thread_lookup es i _ (k e') Hlook) as Hupdated.
  split.
  - intros j a Hlookup. destruct (decide (i = j)) as [<-|Hne].
    + rewrite Hupdated in Hlookup. now injection Hlookup as <-.
    + apply (Hthreads j a). now rewrite list_lookup_insert_ne in Hlookup.
  - intros [j|c]; [|reflexivity]. unfold object_endpoints.
    destruct (decide (i = j)) as [<-|Hne].
    + now rewrite Hupdated, Hlook.
    + now rewrite list_lookup_insert_ne.
Qed.


Lemma closing_spawn_full_reachability_iff_worker_context :
  fully_reachable [Close (Spawn 1 (λ _, closing_spawn_worker))] ∅ ↔
  spawn_source_has_context 1 (λ _, closing_spawn_worker).
Proof.
  split.
  - intros Hfull.
    destruct (closed_spawn_progress_requires_context _ _ Hfull) as [Hvalue|Hctx].
    + destruct (Hvalue 0%fin) as [v Hv]. discriminate.
    + exact Hctx.
  - intros (p & fallback & focus & Hworkers).
    pose proof (f_equal (λ f : fin 1 → expr, f p) Hworkers) as Hfocus.
    cbn beta in Hfocus. rewrite decide_True in Hfocus by reflexivity.
    subst focus.
    apply empty_heap_full_reachability_iff_progress.
    intros i (current & Hlookup & Hactive).
    destruct i as [|i].
    + set (frame := λ x, Close (Spawn 1
        (λ q, if decide (p = q) then x else fallback q))).
      assert (ctx frame) as Hctx.
      {
        unfold frame.
        apply Ctx_cons with (k1 := Close) (k2 := λ x, Spawn 1
          (λ q, if decide (p = q) then x else fallback q)).
        - exact Ctx_Close.
        - apply Ctx_cons with (k1 := λ x, Spawn 1
            (λ q, if decide (p = q) then x else fallback q)) (k2 := λ x, x);
          constructor.
      }
      assert (ctx_step (frame closing_spawn_worker) ∅
        (frame (Val (FunV "channel"%string (Close (Var "channel"%string))))) ∅ [])
        as Hstep.
      { apply Ctx_step; [exact Hctx|]. apply Pure_step, Lam_step. }
      do 2 eexists. eapply Head_step; [exact Hstep|].
      change (Some (Close (Spawn 1 (λ _, closing_spawn_worker))) =
        Some (frame closing_spawn_worker)).
      unfold frame. now rewrite <- Hworkers.
    + change (([] : list expr) !! i = Some current) in Hlookup.
      rewrite lookup_nil in Hlookup. discriminate.
Qed.

Definition marked_closing_worker (marker : nat) : expr :=
  Lam "channel"%string
    (If (Val (NatV marker))
      (Close (Var "channel"%string))
      (Close (Var "channel"%string))).

Lemma marked_closing_worker_typed marker :
  typed ∅ (marked_closing_worker marker) (FunT (ChanT EndT) UnitT).
Proof.
  unfold marked_closing_worker. apply Lam_typed; [apply lookup_empty|].
  assert (typed (∅ ∪ {["channel"%string := ChanT EndT]})
    (Close (Var "channel"%string)) UnitT) as Hclose.
  {
    apply Close_typed, Var_typed.
    - apply lookup_empty.
    - exact runtime_empty_context_unrestricted.
    - apply runtime_type_equiv_refl.
  }
  replace (∅ ∪ {["channel"%string := ChanT EndT]} : envT)
    with ((∅ : envT) ∪ (∅ ∪ {["channel"%string := ChanT EndT]}))
    by apply map_empty_union.
  apply If_typed.
  - intros x t u Hlookup. rewrite lookup_empty in Hlookup. discriminate.
  - apply Nat_typed, runtime_empty_context_unrestricted.
  - exact Hclose.
  - exact Hclose.
Qed.

Lemma marked_spawns_typed n (markers : fin n → nat) :
  typed ∅ (Close (Spawn n (λ q, marked_closing_worker (markers q)))) UnitT.
Proof.
  apply Close_typed.
  eapply Spawn_typed with (σs := λ _, EndT) (fΓ := λ _, ∅).
  - apply all_end_protocol_consistent.
  - constructor.
    + intros p q Hneq x t u Hlookup. rewrite lookup_empty in Hlookup. discriminate.
    + intros p x t Hlookup. exact Hlookup.
    + intros x t Hlookup. rewrite lookup_empty in Hlookup. inversion Hlookup.
  - intros p. apply marked_closing_worker_typed.
Qed.

Lemma finite_one_index (q : fin 1) : q = 0%fin.
Proof.
  refine (fin_S_inv (λ i : fin 1, i = 0%fin) eq_refl _ q).
  intro i. exact (fin_0_inv (λ j, FS j = 0%fin) i).
Qed.

Lemma initial_singleton_marker_functions_decompose :
  (∀ e es h, typed ∅ e UnitT → steps [e] ∅ es h →
    deadlock_free es h ∧ fully_reachable es h) →
  ∀ markers : fin 1 → nat, ∃ fallback : fin 1 → expr,
    (λ q, marked_closing_worker (markers q)) =
    (λ q, if decide ((0%fin : fin 1) = q)
          then marked_closing_worker (markers 0%fin) else fallback q).
Proof.
  intros Hmain markers.
  destruct (Hmain _ _ _ (marked_spawns_typed 1 markers) (Empty_step _ _))
    as [_ Hfull].
  destruct (closed_spawn_progress_requires_context _ _ Hfull)
    as [Hvalue|(p & fallback & focus & Hworkers)].
  - destruct (Hvalue 0%fin) as [v Hv]. discriminate.
  - rewrite (finite_one_index p) in Hworkers.
    pose proof (f_equal (λ f : fin 1 → expr, f 0%fin) Hworkers) as Hfocus.
    cbn beta in Hfocus. rewrite decide_True in Hfocus by reflexivity.
    subst focus. now exists fallback.
Qed.

Definition singleton_worker_tail := { q : fin 1 | (0%fin : fin 1) ≠ q }.

Lemma singleton_worker_tail_empty : singleton_worker_tail → False.
Proof.
  intros [q Hneq]. apply Hneq. symmetry. exact (finite_one_index q).
Qed.

Definition reconstruct_singleton_worker (head : expr)
    (tail : singleton_worker_tail → expr) : fin 1 → expr :=
  λ q, match decide ((0%fin : fin 1) = q) with
        | left _ => head
        | right Hneq => tail (exist _ q Hneq)
        end.

Definition read_worker_marker (e : expr) : nat :=
  match e with
  | Lam _ (If (Val (NatV n)) _ _) => n
  | _ => 0
  end.

Lemma deadlock_theorem_implies_singleton_extensionality_over_empty_tail :
  (∀ e es h, typed ∅ e UnitT → steps [e] ∅ es h →
    deadlock_free es h ∧ fully_reachable es h) →
  (∀ k1 k2 : singleton_worker_tail → expr, k1 = k2) →
  ∀ f g : fin 1 → nat, (∀ p, f p = g p) → f = g.
Proof.
  intros Hmain Htail f g Hagree.
  destruct (initial_singleton_marker_functions_decompose Hmain f) as [kf Hf].
  destruct (initial_singleton_marker_functions_decompose Hmain g) as [kg Hg].
  change ((λ q, marked_closing_worker (f q)) =
    reconstruct_singleton_worker (marked_closing_worker (f 0%fin))
      (λ tail, kf (proj1_sig tail))) in Hf.
  change ((λ q, marked_closing_worker (g q)) =
    reconstruct_singleton_worker (marked_closing_worker (g 0%fin))
      (λ tail, kg (proj1_sig tail))) in Hg.
  assert ((λ q, marked_closing_worker (f q)) =
    (λ q, marked_closing_worker (g q))) as Hworkers.
  {
    rewrite Hf, Hg, (Hagree 0%fin).
    f_equal. apply Htail.
  }
  exact (f_equal (λ workers q, read_worker_marker (workers q)) Hworkers).
Qed.

Lemma closed_runtime_frame Σ k e t :
  ctx k →
  runtime_typed Σ ∅ (k e) t →
  ∃ τ,
    runtime_typed Σ ∅ e τ ∧
    expr_endpoints e ## expr_endpoints (k (Val UnitV)) ∧
    ∀ Σ' e',
      protocols_agree_on Σ Σ' (expr_endpoints (k (Val UnitV))) →
      expr_endpoints e' ## expr_endpoints (k (Val UnitV)) →
      runtime_typed Σ' ∅ e' τ →
      runtime_typed Σ' ∅ (k e') t.
Proof.
  intros Hctx Htyped.
  destruct (runtime_typing_context_frame Σ ∅ k e t Hctx Htyped)
    as (Γ & τ & Hhole & Hclosed & Hsep & Hframe).
  specialize (Hclosed eq_refl). subst Γ.
  exists τ. auto.
Qed.

Lemma runtime_send_context_preservation Σ h k c q π p label v t bufs :
  ctx k →
  runtime_typed Σ ∅ (k (Send p (Val (ChanV (c,q) π)) label (Val v))) t →
  session_queues_typed (λ w τ, runtime_typed Σ ∅ (Val w) τ) h c bufs →
  sbufs_typed bufs (Σ c) →
  (c,q) ∉ heap_value_refs val_endpoints h c →
  ∃ σ bufs',
    let locals := <[q := σ]> (Σ c) in
    let Σ' := replace_session_protocol_map Σ c locals in
    is_present q (c,π p) h ∧
    runtime_typed Σ' ∅ (k (Val (ChanV (c,q) π))) t ∧
    session_queues_typed (λ w τ, runtime_typed Σ' ∅ (Val w) τ)
      (push q (c,π p) (label,v) h) c bufs' ∧
    sbufs_typed bufs' locals.
Proof.
  intros Hctx Htyped Hqueues Hsafe Hnoheap.
  destruct (closed_runtime_frame _ _ _ _ Hctx Htyped)
    as (τ & Hhole & Hsep & Hplug).
  destruct (runtime_send_head_preservation _ _ _ _ _ _ _ _ _ _
    Hhole Hqueues Hsafe Hnoheap) as (σ & bufs' & Hpresent & Hnext & Hqueues' & Hsafe').
  exists σ, bufs'. cbn zeta in *. split; [exact Hpresent|]. split.
  - apply Hplug; [| |exact Hnext].
    + apply changed_endpoint_protocol_agrees_on_frame.
      cbn [expr_endpoints val_endpoints] in Hsep. set_solver.
    + cbn [expr_endpoints val_endpoints] in *. set_solver.
  - now split.
Qed.

Lemma runtime_receive_context_preservation Σ h k c q π p label v h' t bufs :
  ctx k →
  runtime_typed Σ ∅ (k (Recv p (Val (ChanV (c,q) π)))) t →
  session_queues_typed (λ w τ, runtime_typed Σ ∅ (Val w) τ) h c bufs →
  sbufs_typed bufs (Σ c) →
  (c,q) ∉ heap_value_refs val_endpoints h c →
  val_endpoints v ## expr_endpoints (k (Val UnitV)) →
  pop (π p) (c,q) h = Some ((label,v),h') →
  ∃ σ bufs',
    let locals := <[q := σ]> (Σ c) in
    let Σ' := replace_session_protocol_map Σ c locals in
    runtime_typed Σ' ∅ (k (Val (InjNV label (PairV (ChanV (c,q) π) v)))) t ∧
    session_queues_typed (λ w τ, runtime_typed Σ' ∅ (Val w) τ) h' c bufs' ∧
    sbufs_typed bufs' locals.
Proof.
  intros Hctx Htyped Hqueues Hsafe Hnoheap Hval Hpop.
  destruct (closed_runtime_frame _ _ _ _ Hctx Htyped)
    as (τ & Hhole & Hsep & Hplug).
  destruct (runtime_receive_head_preservation _ _ _ _ _ _ _ _ _ _ _
    Hhole Hqueues Hsafe Hnoheap Hpop) as (σ & bufs' & Hnext & Hqueues' & Hsafe').
  exists σ, bufs'. cbn zeta in *. split; [|now split].
  apply Hplug; [| |exact Hnext].
  - apply changed_endpoint_protocol_agrees_on_frame.
    cbn [expr_endpoints val_endpoints] in Hsep. set_solver.
  - cbn [expr_endpoints val_endpoints] in *. set_solver.
Qed.

Lemma runtime_close_context_preservation Σ (h : heap) k c q π t bufs :
  ctx k →
  runtime_typed Σ ∅ (k (Close (Val (ChanV (c,q) π)))) t →
  session_queues_typed (λ w τ, runtime_typed Σ ∅ (Val w) τ) h c bufs →
  sbufs_typed bufs (Σ c) →
  (c,q) ∉ heap_value_refs val_endpoints h c →
  let locals := delete q (Σ c) in
  let Σ' := replace_session_protocol_map Σ c locals in
  runtime_typed Σ' ∅ (k (Val UnitV)) t ∧
  (∀ p entries, buffer_at h (c,q) p = Some entries → entries = []) ∧
  session_queues_typed (λ w τ, runtime_typed Σ' ∅ (Val w) τ)
    (delete ((c,q) : endpoint) (h : gmap endpoint (gmap participant (list entryT)))) c
    (delete q (bufs : gmap participant (gmap participant (list sentryT)))) ∧
  sbufs_typed (delete q bufs) locals.
Proof.
  intros Hctx Htyped Hqueues Hsafe Hnoheap. cbn zeta.
  destruct (closed_runtime_frame _ _ _ _ Hctx Htyped)
    as (τ & Hhole & Hsep & Hplug).
  destruct (runtime_close_head_preservation _ _ _ _ _ _ _
    Hhole Hqueues Hsafe Hnoheap) as (Hnext & Hempty & Hqueues' & Hsafe').
  cbn zeta in Hnext, Hqueues', Hsafe'. split; [|auto].
  apply Hplug; [| |exact Hnext].
  - apply removed_endpoint_protocol_agrees_on_frame.
    cbn [expr_endpoints val_endpoints] in Hsep. set_solver.
  - cbn [expr_endpoints val_endpoints]. set_solver.
Qed.

Lemma runtime_spawn_context_preservation Σ (h : heap) k c n
    (f : fin n → expr) (fv : fin n → val) t :
  ctx k →
  runtime_typed Σ ∅ (k (Spawn n f)) t →
  protocol_endpoints_allocated Σ h →
  (∀ p, h !! (c,p) = None) →
  (∀ p, f p = Val (fv p)) →
  ∃ σs : fin (S n) → session_type,
    let locals := fin_gmap (S n) σs in
    let Σ' := replace_session_protocol_map Σ c locals in
    runtime_typed Σ' ∅ (k (Val (ChanV (c,0) id))) t ∧
    (∀ e, e ∈ init_threads c n fv → runtime_typed Σ' ∅ e UnitT) ∧
    session_queues_typed (λ v τ, runtime_typed Σ' ∅ (Val v) τ)
      (gmap_unslice (init_chans (S n) : bufsT participant participant entryT) c ∪
        (h : gmap endpoint (gmap participant (list entryT)))) c
      (init_chans (S n)) ∧
    sbufs_typed (init_chans (S n)) locals.
Proof.
  intros Hctx Htyped Hallocated Hfresh Hvalues.
  destruct (closed_runtime_frame _ _ _ _ Hctx Htyped)
    as (τ & Hhole & Hsep & Hplug).
  destruct (runtime_spawn_head_preservation _ _ _ _ _ _ _
    Hhole Hallocated Hfresh Hvalues) as (σs & Hnext & Hworkers & Hqueues & Hsafe).
  exists σs. cbn zeta in *. split; [|auto].
  pose proof (fresh_endpoint_protocol_map_is_empty Σ h c Hallocated Hfresh) as Hempty.
  pose proof (ctx_endpoint_split k (Spawn n f) Hctx) as Hsplit.
  apply Hplug; [| |exact Hnext].
  - eapply protocols_agree_on_subset; [|exact
      (fresh_session_protocol_map_agrees _ _ _ _ c _ Htyped Hempty)].
    rewrite Hsplit. set_solver.
  - cbn [expr_endpoints val_endpoints]. apply elem_of_disjoint.
    intros ep Heq Hin. apply elem_of_singleton in Heq. subst ep.
    assert ((c,0) ∈ expr_endpoints (k (Spawn n f))) as Hmember.
    { rewrite Hsplit. now apply elem_of_union_r. }
    destruct (runtime_typed_endpoints_have_protocols _ _ _ _ Htyped c 0 Hmember)
      as (σ & Hlook).
    rewrite Hempty in Hlook. discriminate.
Qed.

Definition allocation_owner_stage {n} (old : object → endpoint → Prop)
    (i offset c : nat) (captures : fin n → gset endpoint) (done : gset (fin n))
    (x : object) (ep : endpoint) : Prop :=
  (old x ep ∧ (x ≠ Thread i ∨ ∀ p, ep ∉ captures p)) ∨
  (x = Thread i ∧ ep = (c,0)) ∨
  (x = Chan c ∧ ∃ p, p ∉ done ∧ ep ∈ captures p) ∨
  (∃ p, p ∈ done ∧ x = Thread (offset + fin_to_nat p) ∧
    (ep = (c,S (fin_to_nat p)) ∨ ep ∈ captures p)).

Lemma allocation_owner_stage_unique n (old : object → endpoint → Prop) (i offset c : nat)
    (captures : fin n → gset endpoint) (done : gset (fin n)) :
  (∀ x y ep, old x ep → old y ep → x = y) →
  (∀ x ep, old x ep → fst ep ≠ c) →
  (∀ p ep, ep ∈ captures p → old (Thread i) ep) →
  (∀ p q, p ≠ q → captures p ## captures q) →
  ∀ x y ep, allocation_owner_stage old i offset c captures done x ep →
    allocation_owner_stage old i offset c captures done y ep → x = y.
Proof.
  intros Hunique Hfresh Hcaptured Hseparated x y ep Hx Hy.
  assert (∀ p q, ep ∈ captures p → ep ∈ captures q → p = q) as Hindex.
  {
    intros p q Hp Hq. destruct (decide (p = q)) as [Heq|Hne]; [exact Heq|].
    exfalso. exact (proj1 (elem_of_disjoint _ _) (Hseparated p q Hne) ep Hp Hq).
  }
  assert (∀ z p, old z ep → ep ∈ captures p → z = Thread i) as Hroot.
  { intros z p Hz Hp. exact (Hunique _ _ _ Hz (Hcaptured p ep Hp)). }
  assert (∀ p, ep ∈ captures p → fst ep ≠ c) as Hcapture_fresh.
  { intros p Hp. exact (Hfresh (Thread i) ep (Hcaptured p ep Hp)). }
  assert (∀ p q : fin n, (c,S (fin_to_nat p)) = (c,S (fin_to_nat q)) → p = q) as Hworker.
  { intros p q Heq. apply fin_to_nat_inj. congruence. }
  unfold allocation_owner_stage in Hx, Hy.
  destruct Hx as [(Hx & Hxrest)|[(-> & Hep)|[(-> & p & Hp & Hpx)|(p & Hp & -> & [Hpx|Hpx])]]];
  destruct Hy as [(Hy & Hyrest)|[(-> & Hey)|[(-> & q & Hq & Hqy)|(q & Hq & -> & [Hqy|Hqy])]]];
  try reflexivity;
  try subst ep; cbn in *;
  try solve [eapply Hunique; eassumption];
  try solve [exfalso; match goal with
    | Hold : old ?z (?cs,?port) |- _ =>
        exact (Hfresh z (cs,port) Hold eq_refl)
    end];
  try solve [exfalso; eapply Hcapture_fresh; [eassumption|congruence]];
  try solve [exfalso; congruence];
  try solve [exfalso; first [destruct Hxrest as [Hne|Hnone]|destruct Hyrest as [Hne|Hnone]];
    [apply Hne; eapply Hroot; eassumption|eapply Hnone; eassumption]];
  try solve [exfalso; assert (p = q) by (eapply Hindex; eassumption); subst; contradiction];
  try solve [assert (p = q) by (apply Hworker; congruence); now subst];
  try solve [assert (p = q) by (eapply Hindex; eassumption); now subst].
Qed.

Lemma allocation_owner_stages_preserve_forest n (old : object → endpoint → Prop) (i offset c : nat)
    (captures : fin n → gset endpoint) :
  i < offset →
  (∀ x y ep, old x ep → old y ep → x = y) →
  (∀ x ep, old x ep → fst ep ≠ c) →
  (∀ ep, ¬ old (Chan c) ep) →
  (∀ j ep, offset ≤ j → ¬ old (Thread j) ep) →
  (∀ p ep, ep ∈ captures p → old (Thread i) ep) →
  (∀ p q, p ≠ q → captures p ## captures q) →
  (∀ x ep, ¬ nonbacktracking_ownership_walk (ownership_edge old) x ep x) →
  ∀ done x ep, ¬ nonbacktracking_ownership_walk
    (ownership_edge (allocation_owner_stage old i offset c captures done)) x ep x.
Proof.
  intros Hi Hunique Hfresh Hnochan Hnothread Hcaptured Hseparated Hforest.
  assert (∀ done x y ep, allocation_owner_stage old i offset c captures done x ep →
    allocation_owner_stage old i offset c captures done y ep → x = y) as Hstage_unique.
  { intros done. eapply allocation_owner_stage_unique; eassumption. }
  apply (set_ind_L (λ done : gset (fin n), ∀ x ep,
    ¬ nonbacktracking_ownership_walk
      (ownership_edge (allocation_owner_stage old i offset c captures done)) x ep x)).
  - eapply (split_owner_onto_fresh_vertex_preserves_forest old _ (Thread i) (Chan c) (c,0)).
    + discriminate.
    + right. cbn. split; [reflexivity|]. unfold allocation_owner_stage. auto.
    + apply Hstage_unique.
    + intros x ep Hnot Hown.
      destruct Hown as [(Hown & _)|[(_ & Heq)|[(-> & p & _ & Hin)|(p & Hin & _)]]].
      * now left.
      * contradiction.
      * right. split; [reflexivity|exact (Hcaptured p ep Hin)].
      * apply elem_of_empty in Hin. contradiction.
    + intros [d q] x y Hlink.
      destruct Hlink as [[-> Hown]|[-> Hown]]; cbn in *.
      * split.
        -- intros ->. exact (Hnochan _ Hown).
        -- intros Heq. injection Heq as ->. exact (Hfresh _ _ Hown eq_refl).
      * split.
        -- intros Heq. injection Heq as ->. exact (Hfresh _ _ Hown eq_refl).
        -- intros ->. exact (Hnochan _ Hown).
    + exact Hforest.
  - intros p done Hnew IH.
    set (j := offset + fin_to_nat p).
    set (pivot := (c,S (fin_to_nat p))).
    eapply (split_owner_onto_fresh_vertex_preserves_forest
      (allocation_owner_stage old i offset c captures done) _ (Chan c) (Thread j) pivot).
    + discriminate.
    + left. cbn. split; [reflexivity|].
      unfold allocation_owner_stage. right. right. right. exists p.
      split; [set_solver|]. now split; [|left].
    + apply Hstage_unique.
    + intros x ep Hnot Hown.
      destruct Hown as [(Hown & Hrest)|[(Hx & Heq)|[(Hx & q & Hq & Hin)|
        (q & Hq & Hx & Hrefs)]]].
      * left. unfold allocation_owner_stage. now left.
      * left. unfold allocation_owner_stage. auto.
      * left. right. right. left. split; [exact Hx|].
        exists q. split; [set_solver|exact Hin].
      * apply elem_of_union in Hq as [Hq|Hq].
        -- apply elem_of_singleton in Hq. subst q.
           destruct Hrefs as [Heq|Hin]; [contradiction|].
           right. split; [exact Hx|]. right. right. left.
           split; [reflexivity|]. now exists p.
        -- left. right. right. right. now exists q.
    + intros ep x y Hlink.
      assert (¬ allocation_owner_stage old i offset c captures done (Thread j) ep) as Hnone.
      {
        unfold allocation_owner_stage. intros [(Hown & _)|[(Heq & _)|[(Heq & _)|
          (q & Hq & Heq & _)]]].
        - exact (Hnothread j ep ltac:(unfold j; lia) Hown).
        - injection Heq as Heq. unfold j in Heq. lia.
        - discriminate.
        - apply Hnew. assert (q = p) as ->; [|exact Hq].
          apply fin_to_nat_inj. injection Heq as Heq. unfold j in Heq. lia.
      }
      destruct Hlink as [[-> Hown]|[-> Hown]]; split; intros Heq;
        first [discriminate | subst; exact (Hnone Hown)].
    + exact IH.
Qed.


Lemma allocation_has_old_queued_endpoint_references (h : heap) c n d ep :
  (∀ p, h !! (c,p) = None) →
  ep ∈ heap_value_refs val_endpoints
    (gmap_unslice (init_chans (S n) : bufsT participant participant entryT) c ∪ h) d ↔
  ep ∈ heap_value_refs val_endpoints h d.
Proof.
  intros Hfresh. rewrite !elem_of_heap_value_refs_iff.
  split; intros (q & p & label & v & Hqueued & Hmember); exists q, p, label, v;
    split; [|exact Hmember| |exact Hmember].
  - exact (proj1 (allocation_preserves_queued_entries h c (S n) d q p (label,v) Hfresh) Hqueued).
  - exact (proj2 (allocation_preserves_queued_entries h c (S n) d q p (label,v) Hfresh) Hqueued).
Qed.

Lemma fresh_heap_session_has_no_endpoint_references (h : heap) c ep :
  (∀ p, h !! (c,p) = None) →
  ep ∉ heap_value_refs val_endpoints h c.
Proof.
  intros Hfresh Hmember. apply elem_of_heap_value_refs_iff in Hmember.
  destruct Hmember as (q & p & label & v & (entries & Hlookup & _) & _).
  unfold buffer_at in Hlookup. rewrite Hfresh in Hlookup. discriminate.
Qed.

Lemma initialized_worker_list_length c n fv :
  List.length (init_threads c n fv) = n.
Proof.
  unfold init_threads, fin_list. apply length_vec_to_list.
Qed.

Lemma allocated_worker_is_at_finite_index es c n fv j e :
  List.length es ≤ j →
  (es ++ init_threads c n fv) !! j = Some e →
  ∃ p : fin n, j = List.length es + fin_to_nat p ∧
    e = App (Val (fv p)) (Val (ChanV (c,S (fin_to_nat p)) id)).
Proof.
  intros Hj Hlook.
  assert (j - List.length es < n) as Hlt.
  {
    assert (j < List.length (es ++ init_threads c n fv)) as Htotal.
    { apply lookup_lt_is_Some. now exists e. }
    rewrite length_app, initialized_worker_list_length in Htotal. lia.
  }
  exists (nat_to_fin Hlt).
  assert (j = List.length es + fin_to_nat (nat_to_fin Hlt)) as Heq by
    (rewrite fin_to_nat_to_fin; lia).
  split; [exact Heq|].
  rewrite Heq, allocated_worker_lookup in Hlook. now injection Hlook as <-.
Qed.

Lemma spawn_preserves_endpoint_forest es (h : heap) i k c n
    (f : fin n → expr) (fv : fin n → val) :
  ctx k →
  es !! i = Some (k (Spawn n f)) →
  (∀ p, f p = Val (fv p)) →
  (∀ p, h !! (c,p) = None) →
  (∀ p q, p ≠ q → val_endpoints (fv p) ## val_endpoints (fv q)) →
  expr_endpoints (Spawn n f) ## expr_endpoints (k (Val UnitV)) →
  (∀ x y ep, owns_endpoint es h x ep → owns_endpoint es h y ep → x = y) →
  (∀ x ep, owns_endpoint es h x ep → is_Some (h !! ep)) →
  (∀ x ep, ¬ nonbacktracking_ownership_walk (ownership_edge (owns_endpoint es h)) x ep x) →
  let es' := <[i := k (Val (ChanV (c,0) id))]> es ++ init_threads c n fv in
  let h' := gmap_unslice (init_chans (S n) : bufsT participant participant entryT) c ∪ h in
  ∀ x ep, ¬ nonbacktracking_ownership_walk (ownership_edge (owns_endpoint es' h')) x ep x.
Proof.
  intros Hctx Hlookup Hvalues Hfresh Hdis Hsep Hunique Hlive Hforest. cbn zeta.
  set (captures := λ p, val_endpoints (fv p)).
  set (done := fin_gset n (λ p, p)).
  set (owners := allocation_owner_stage (owns_endpoint es h) i (List.length es) c captures done).
  assert (i < List.length es) as Hi by (apply lookup_lt_is_Some; now exists (k (Spawn n f))).
  assert (∀ p : fin n, p ∈ done) as Hdone.
  {
    unfold done, fin_gset. intros p. apply elem_of_list_to_set, elem_of_fin_list_iff.
    now exists p.
  }
  assert (∀ p ep, ep ∈ captures p → ep ∈ expr_endpoints (Spawn n f)) as Hmoved.
  {
    intros p ep Hin. cbn [expr_endpoints]. apply elem_of_fin_union_iff.
    exists p. cbn [compose]. rewrite Hvalues. exact Hin.
  }
  assert (∀ ep, ep ∈ expr_endpoints (k (Val UnitV)) → ∀ p, ep ∉ captures p) as Hframe.
  {
    intros ep Hin p Hcaptured.
    exact (proj1 (elem_of_disjoint _ _) Hsep ep (Hmoved p ep Hcaptured) Hin).
  }
  assert (∀ x ep, ¬ nonbacktracking_ownership_walk (ownership_edge owners) x ep x)
    as Hstage.
  {
    unfold owners. apply allocation_owner_stages_preserve_forest.
    - exact Hi.
    - exact Hunique.
    - intros x [d q] Hown. cbn. intros ->.
      destruct (Hlive _ _ Hown) as [bs Hbs]. rewrite Hfresh in Hbs. discriminate.
    - intros ep. exact (fresh_heap_session_has_no_endpoint_references h c ep Hfresh).
    - intros j ep Hj. unfold owns_endpoint, object_endpoints.
      rewrite lookup_ge_None_2 by exact Hj. apply not_elem_of_empty.
    - intros p ep Hcap. apply (proj2 (thread_endpoint_lookup _ _ _ _ _ Hlookup)).
      rewrite (ctx_endpoint_split _ _ Hctx). apply elem_of_union_l, (Hmoved p). exact Hcap.
    - exact Hdis.
    - exact Hforest.
  }
  eapply (ownership_subgraph_preserves_forest owners); [|exact Hstage].
  intros [j|d] ep Hown.
  - set (main := <[i := k (Val (ChanV (c,0) id))]> es) in *.
    assert (List.length main = List.length es) as Hsize by (unfold main; apply length_insert).
    destruct (decide (j < List.length es)) as [Hj|Hj].
    + unfold owns_endpoint, object_endpoints in Hown.
      rewrite lookup_app_l in Hown by lia.
      destruct (decide (i = j)) as [<-|Hne].
      * unfold main in Hown.
        rewrite (update_thread_lookup es i _ _ Hlookup) in Hown. cbn in Hown.
        rewrite (ctx_endpoint_split k (Val (ChanV (c,0) id)) Hctx) in Hown.
        apply elem_of_union in Hown as [Hnew|Hold].
        -- right. left. split; [reflexivity|exact (proj1 (elem_of_singleton _ _) Hnew)].
        -- left. split.
           ++ apply (proj2 (thread_endpoint_lookup _ _ _ _ _ Hlookup)).
              rewrite (ctx_endpoint_split _ _ Hctx). now apply elem_of_union_r.
           ++ right. now apply Hframe.
      * unfold main in Hown. rewrite list_lookup_insert_ne in Hown by exact Hne.
        left. split; [exact Hown|left; congruence].
    + unfold owns_endpoint, object_endpoints in Hown.
      destruct ((main ++ init_threads c n fv) !! j) as [worker|] eqn:Hlook;
        cbn in Hown; [|now apply elem_of_empty in Hown].
      destruct (allocated_worker_is_at_finite_index main c n fv j worker ltac:(lia) Hlook)
        as (p & -> & ->).
      right. right. right. exists p. rewrite Hsize.
      split; [apply Hdone|]. split; [reflexivity|].
      cbn [expr_endpoints val_endpoints] in Hown.
      rewrite elem_of_union, elem_of_singleton in Hown. tauto.
  - unfold owns_endpoint, object_endpoints in Hown.
    left. split; [|left; discriminate].
    exact (proj1 (allocation_has_old_queued_endpoint_references h c n d ep Hfresh) Hown).
Qed.


Definition runtime_sessions_typed Σ h : Prop :=
  ∀ c, ∃ bufs,
    session_queues_typed (λ v t, runtime_typed Σ ∅ (Val v) t) h c bufs ∧
    sbufs_typed bufs (Σ c).

Lemma runtime_typed_sessions_have_allocated_endpoints Σ h :
  runtime_sessions_typed Σ h → protocol_endpoints_allocated Σ h.
Proof.
  intros Hall c q σ Hlookup. destruct (Hall c) as (bufs & Hqueues & Hsafe).
  apply (proj1 (session_queues_domain _ _ _ _ Hqueues q)).
  apply elem_of_dom.
  rewrite (sbufs_typed_dom _ _ Hsafe). apply elem_of_dom. now exists σ.
Qed.

Lemma session_queued_value_is_runtime_typed Σ h c bufs q p label v :
  session_queues_typed (λ w t, runtime_typed Σ ∅ (Val w) t) h c bufs →
  queued_entry h (c,q) p (label,v) →
  ∃ t, runtime_typed Σ ∅ (Val v) t.
Proof.
  intros Hqueues (entries & Hlookup & Hmember).
  destruct (typed_buffer_matching_concrete _ _ _ _ _ _ _ Hqueues Hlookup)
    as (tags & _ & Htyped).
  clear Hlookup.
  induction Htyped as [|[j w] [j' t] entries tags [_ Hw] Htyped IH].
  - now apply elem_of_nil in Hmember.
  - apply elem_of_cons in Hmember as [Heq|Hrest].
    + injection Heq as _ <-. now exists t.
    + now apply IH.
Qed.

Lemma runtime_state_owners_have_allocated_endpoints Σ es h :
  (∀ i e, es !! i = Some e → runtime_typed Σ ∅ e UnitT) →
  runtime_sessions_typed Σ h →
  ∀ x ep, owns_endpoint es h x ep → is_Some (h !! ep).
Proof.
  intros Hthreads Hall [i|c] [d r] Howns.
  - unfold owns_endpoint, object_endpoints in Howns.
    destruct (es !! i) as [e|] eqn:Hlookup; cbn in Howns; [|set_solver].
    destruct (runtime_typed_endpoints_have_protocols _ _ _ _
      (Hthreads _ _ Hlookup) d r Howns) as (σ & Hσ).
    exact (runtime_typed_sessions_have_allocated_endpoints _ _ Hall d r σ Hσ).
  - unfold owns_endpoint, object_endpoints in Howns.
    apply elem_of_heap_value_refs_iff in Howns as (q & p & label & v & Hentry & Hrefs).
    destruct (Hall c) as (bufs & Hqueues & _).
    destruct (session_queued_value_is_runtime_typed _ _ _ _ _ _ _ _ Hqueues Hentry)
      as (t & Hv).
    destruct (runtime_typed_endpoints_have_protocols _ _ _ _ Hv d r Hrefs)
      as (σ & Hσ).
    exact (runtime_typed_sessions_have_allocated_endpoints _ _ Hall d r σ Hσ).
Qed.

Lemma runtime_spawn_workers_separated Σ Γ e t :
  runtime_typed Σ Γ e t →
  ∀ n (f : fin n → expr), e = Spawn n f →
    ∀ p q, p ≠ q → expr_endpoints (f p) ## expr_endpoints (f q).
Proof.
  intros Htyped. induction Htyped; intros arity workers Hspawn; try discriminate.
  - inversion Hspawn; subst.
    match goal with Heq : existT ?n ?f = existT ?n ?g |- _ =>
      apply (inj_pair2_eq_dec nat Nat.eq_dec) in Heq; (subst f || subst g)
    end.
    exact H.
  - now eapply IHHtyped.
Qed.

Lemma typed_spawn_preserves_endpoint_forest Σ es (h : heap) i k c n
    (f : fin n → expr) (fv : fin n → val) :
  ctx k →
  es !! i = Some (k (Spawn n f)) →
  (∀ p, f p = Val (fv p)) →
  (∀ p, h !! (c,p) = None) →
  (∀ j e, es !! j = Some e → runtime_typed Σ ∅ e UnitT) →
  runtime_sessions_typed Σ h →
  (∀ x y ep, owns_endpoint es h x ep → owns_endpoint es h y ep → x = y) →
  (∀ x ep, ¬ nonbacktracking_ownership_walk (ownership_edge (owns_endpoint es h)) x ep x) →
  let es' := <[i := k (Val (ChanV (c,0) id))]> es ++ init_threads c n fv in
  let h' := gmap_unslice (init_chans (S n) : bufsT participant participant entryT) c ∪ h in
  ∀ x ep, ¬ nonbacktracking_ownership_walk (ownership_edge (owns_endpoint es' h')) x ep x.
Proof.
  intros Hctx Hlookup Hvalues Hfresh Hthreads Hqueues Hunique Hforest.
  destruct (runtime_typing_context_frame _ _ _ _ _ Hctx (Hthreads _ _ Hlookup))
    as (Γ & τ & Hhole & _ & Hsep & _).
  apply (spawn_preserves_endpoint_forest es h i k c n f fv); try assumption.
  - intros p q Hne.
    pose proof (runtime_spawn_workers_separated _ _ _ _ Hhole n f eq_refl p q Hne)
      as Hworker. now rewrite !Hvalues in Hworker.
  - exact (runtime_state_owners_have_allocated_endpoints _ _ _ Hthreads Hqueues).
Qed.

Record runtime_state_typed Σ (es : list expr) (h : heap) : Prop := {
  runtime_state_threads i e : es !! i = Some e → runtime_typed Σ ∅ e UnitT;
  runtime_state_sessions : runtime_sessions_typed Σ h
}.

Definition runtime_owners_unique es h : Prop :=
  ∀ x y ep, owns_endpoint es h x ep → owns_endpoint es h y ep → x = y.

Lemma runtime_owned_endpoint_excluded_from_other_objects es h x ep :
  runtime_owners_unique es h →
  owns_endpoint es h x ep →
  ∀ y, y ≠ x → ep ∉ object_endpoints es h y.
Proof.
  intros Hunique Hown y Hne Hother.
  apply Hne. exact (Hunique y x ep Hother Hown).
Qed.

Lemma runtime_protocol_update_agrees_outside_owner Σ es h i c q locals :
  runtime_owners_unique es h →
  owns_endpoint es h (Thread i) (c,q) →
  (∀ p, p ≠ q → Σ c !! p = locals !! p) →
  ∀ x, x ≠ Thread i →
  protocols_agree_on Σ (replace_session_protocol_map Σ c locals)
    (object_endpoints es h x).
Proof.
  intros Hunique Hown Hlocals x Hother.
  apply replace_session_protocols_agree. intros p Hmember.
  apply Hlocals. intros ->.
  exact (runtime_owned_endpoint_excluded_from_other_objects es h (Thread i) (c,q)
    Hunique Hown x Hother Hmember).
Qed.

Lemma runtime_fresh_protocols_agree_on_owners Σ es h c locals :
  runtime_state_typed Σ es h →
  (∀ p, h !! (c,p) = None) →
  ∀ x, protocols_agree_on Σ (replace_session_protocol_map Σ c locals)
    (object_endpoints es h x).
Proof.
  intros [Hthreads Hsessions] Hfresh x.
  apply replace_session_protocols_agree. intros p Hmember.
  destruct (runtime_state_owners_have_allocated_endpoints _ _ _ Hthreads Hsessions
    x (c,p) Hmember) as (bs & Hlookup).
  rewrite Hfresh in Hlookup. discriminate.
Qed.

Lemma runtime_replace_thread_and_local_session Σ es h i a b ws (h' : heap) c locals :
  runtime_state_typed Σ es h →
  es !! i = Some a →
  let Σ' := replace_session_protocol_map Σ c locals in
  runtime_typed Σ' ∅ b UnitT →
  (∀ e, e ∈ ws → runtime_typed Σ' ∅ e UnitT) →
  (∀ x, x ≠ Thread i → protocols_agree_on Σ Σ' (object_endpoints es h x)) →
  (∀ d q, d ≠ c →
    (h : gmap endpoint (gmap participant (list entryT))) !! (d,q) =
    (h' : gmap endpoint (gmap participant (list entryT))) !! (d,q)) →
  (∃ bufs, session_queues_typed (λ v t, runtime_typed Σ' ∅ (Val v) t) h' c bufs ∧
    sbufs_typed bufs locals) →
  runtime_state_typed Σ' (<[i := b]> es ++ ws) h'.
Proof.
  intros [Hthreads Hsessions] Hlookup Σ' Hb Hspawned Hagree Hheap Hsession.
  constructor.
  - intros j e Hlook. apply lookup_app_Some in Hlook as [Hlook|[_ Hlook]].
    + destruct (decide (i = j)) as [<-|Hne].
      * rewrite (update_thread_lookup _ _ _ _ Hlookup) in Hlook.
        now injection Hlook as <-.
      * rewrite list_lookup_insert_ne in Hlook by exact Hne.
        eapply runtime_typed_change_protocols; [exact (Hthreads j e Hlook)|].
        specialize (Hagree (Thread j) ltac:(congruence)).
        unfold object_endpoints in Hagree. now rewrite Hlook in Hagree.
    + apply Hspawned. eapply list_elem_of_lookup_2. exact Hlook.
  - intros d. destruct (decide (d = c)) as [->|Hother].
    + unfold Σ', replace_session_protocol_map. rewrite decide_True by reflexivity. exact Hsession.
    + destruct (Hsessions d) as (bufs & Hqueues & Hsafe).
      exists bufs. split.
      * apply session_queues_preserved_outside_endpoint_updates with (h := h);
          [|now intros q; apply Hheap].
        apply (runtime_queue_typing_change_protocols _ _ _ _ _ Hqueues).
        apply (Hagree (Chan d)). discriminate.
      * unfold Σ', replace_session_protocol_map.
        now rewrite decide_False by exact Hother.
Qed.

Lemma heap_push_lookup_outside_session (h : heap) p c q entry d r :
  d ≠ c →
  h !! (d,r) = push p (c,q) entry h !! (d,r).
Proof.
  intros Hne. unfold push. now rewrite lookup_alter_ne by congruence.
Qed.

Lemma heap_pop_lookup_outside_session (h h' : heap) p c q entry d r :
  pop p (c,q) h = Some (entry,h') →
  d ≠ c →
  h !! (d,r) = h' !! (d,r).
Proof.
  intros Hpop Hne. unfold pop in Hpop.
  repeat match type of Hpop with
  | context [match ?value with _ => _ end] => destruct value
  end; try discriminate.
  inversion Hpop; subst. symmetry. apply stdpp.fin_maps.lookup_insert_ne. congruence.
Qed.

Lemma heap_close_lookup_outside_session (h : heap) c q d r :
  d ≠ c →
  (h : gmap endpoint (gmap participant (list entryT))) !! (d,r) =
  delete ((c,q) : endpoint) (h : gmap endpoint (gmap participant (list entryT))) !! (d,r).
Proof. intros Hne. now rewrite lookup_delete_ne by congruence. Qed.

Lemma heap_spawn_lookup_outside_session (h : heap) c n d r :
  d ≠ c →
  (h : gmap endpoint (gmap participant (list entryT))) !! (d,r) =
  (gmap_unslice (init_chans n : bufsT participant participant entryT) c ∪
    (h : gmap endpoint (gmap participant (list entryT)))) !! (d,r).
Proof.
  intros Hne. rewrite lookup_union_r; [reflexivity|].
  apply eq_None_not_Some. intros (bs & Hlookup).
  apply lookup_gmap_unslice_some in Hlookup. tauto.
Qed.

Lemma context_endpoint_is_owned es h i k e ep :
  ctx k →
  es !! i = Some (k e) →
  ep ∈ expr_endpoints e →
  owns_endpoint es h (Thread i) ep.
Proof.
  intros Hctx Hlookup Hep. apply (proj2 (thread_endpoint_lookup _ _ _ _ _ Hlookup)).
  rewrite (ctx_endpoint_split k e Hctx). now apply elem_of_union_l.
Qed.

Lemma received_payload_is_disjoint_from_frame es h i k c q p π label v h' :
  runtime_owners_unique es h →
  ctx k →
  es !! i = Some (k (Recv p (Val (ChanV (c,q) π)))) →
  pop (π p) (c,q) h = Some ((label,v),h') →
  val_endpoints v ## expr_endpoints (k (Val UnitV)).
Proof.
  intros Hunique Hctx Hlookup Hpop. apply elem_of_disjoint.
  intros ep Hval Hframe.
  assert (owns_endpoint es h (Thread i) ep) as Hthread.
  {
    apply (proj2 (thread_endpoint_lookup _ _ _ _ _ Hlookup)).
    rewrite (ctx_endpoint_split _ _ Hctx). now apply elem_of_union_r.
  }
  assert (owns_endpoint es h (Chan c) ep) as Hqueue.
  {
    unfold owns_endpoint, object_endpoints.
    apply (proj2 (heap_value_refs_pop val_endpoints h c q (π p) label v h' c ep Hpop)).
    right. now split.
  }
  discriminate (Hunique _ _ _ Hthread Hqueue).
Qed.

Local Ltac find_reducing_thread_endpoint c q :=
  eapply context_endpoint_is_owned;
  [eassumption|eassumption|cbn [expr_endpoints val_endpoints]; set_solver].

Lemma runtime_typed_head_step_in_state Σ es h i k e e' h' ws :
  runtime_state_typed Σ es h →
  runtime_owners_unique es h →
  ctx k →
  es !! i = Some (k e) →
  head_step e h e' h' ws →
  ∃ Σ', runtime_state_typed Σ' (<[i := k e']> es ++ ws) h'.
Proof.
  intros Hstate Hunique Hctx Hlookup Hstep.
  pose proof (runtime_state_threads _ _ _ Hstate) as Hthreads.
  pose proof (runtime_state_sessions _ _ _ Hstate) as Hsessions.
  destruct Hstep as [e e' h Hpure | h c p q v label π | h c p q label v h' π Hpop |
    c q h π | h c n f fv Hfresh Hvalues].
  - exists Σ. rewrite app_nil_r.
    destruct (pure_thread_reduction_preserves_typing_and_ownership Σ es h i k e e'
      Hctx Hlookup Hpure Hthreads) as [Hnew _].
    now constructor.
  - assert (owns_endpoint es h (Thread i) (c,p)) as Hown
      by find_reducing_thread_endpoint c p.
    assert ((c,p) ∉ heap_value_refs val_endpoints h c) as Hnoheap.
    {
      apply (runtime_owned_endpoint_excluded_from_other_objects _ _ _ _
        Hunique Hown (Chan c)). discriminate.
    }
    destruct (Hsessions c) as (bufs & Hqueues & Hsafe).
    destruct (runtime_send_context_preservation _ _ _ _ _ _ _ _ _ _ _
      Hctx (Hthreads _ _ Hlookup) Hqueues Hsafe Hnoheap)
      as (σ & bufs' & _ & Hnext & Hqueues' & Hsafe').
    eexists. eapply (runtime_replace_thread_and_local_session _ _ _ _ _ _ _ _ c (<[p := σ]> (Σ c)));
      try eassumption.
    + intros ? Hnil. now apply elem_of_nil in Hnil.
    + eapply runtime_protocol_update_agrees_outside_owner; [exact Hunique|exact Hown|].
      intros peer Hne. symmetry. apply stdpp.fin_maps.lookup_insert_ne. congruence.
    + intros d r Hne. now apply heap_push_lookup_outside_session.
    + now exists bufs'.
  - assert (owns_endpoint es h (Thread i) (c,q)) as Hown
      by find_reducing_thread_endpoint c q.
    assert ((c,q) ∉ heap_value_refs val_endpoints h c) as Hnoheap.
    {
      apply (runtime_owned_endpoint_excluded_from_other_objects _ _ _ _
        Hunique Hown (Chan c)). discriminate.
    }
    pose proof (received_payload_is_disjoint_from_frame _ _ _ _ _ _ _ _ _ _ _
      Hunique Hctx Hlookup Hpop) as Hpayload.
    destruct (Hsessions c) as (bufs & Hqueues & Hsafe).
    destruct (runtime_receive_context_preservation _ _ _ _ _ _ _ _ _ _ _ _
      Hctx (Hthreads _ _ Hlookup) Hqueues Hsafe Hnoheap Hpayload Hpop)
      as (σ & bufs' & Hnext & Hqueues' & Hsafe').
    eexists. eapply (runtime_replace_thread_and_local_session _ _ _ _ _ _ _ _ c (<[q := σ]> (Σ c)));
      try eassumption.
    + intros ? Hnil. now apply elem_of_nil in Hnil.
    + eapply runtime_protocol_update_agrees_outside_owner; [exact Hunique|exact Hown|].
      intros peer Hne. symmetry. apply stdpp.fin_maps.lookup_insert_ne. congruence.
    + intros d r Hne. eapply heap_pop_lookup_outside_session; eassumption.
    + now exists bufs'.
  - assert (owns_endpoint es h (Thread i) (c,q)) as Hown
      by find_reducing_thread_endpoint c q.
    assert ((c,q) ∉ heap_value_refs val_endpoints h c) as Hnoheap.
    {
      apply (runtime_owned_endpoint_excluded_from_other_objects _ _ _ _
        Hunique Hown (Chan c)). discriminate.
    }
    destruct (Hsessions c) as (bufs & Hqueues & Hsafe).
    destruct (runtime_close_context_preservation _ _ _ _ _ _ _ _
      Hctx (Hthreads _ _ Hlookup) Hqueues Hsafe Hnoheap) as (Hnext & _ & Hqueues' & Hsafe').
    eexists. eapply (runtime_replace_thread_and_local_session _ _ _ _ _ _ _ _ c (delete q (Σ c)));
      try eassumption.
    + intros ? Hnil. now apply elem_of_nil in Hnil.
    + eapply runtime_protocol_update_agrees_outside_owner; [exact Hunique|exact Hown|].
      intros peer Hne. symmetry. apply stdpp.fin_maps.lookup_delete_ne. congruence.
    + intros d r Hne. now apply heap_close_lookup_outside_session.
    + now exists (delete q (bufs : gmap participant (gmap participant (list sentryT)))).
  - pose proof (runtime_typed_sessions_have_allocated_endpoints _ _ Hsessions) as Halloc.
    destruct (runtime_spawn_context_preservation _ _ _ _ _ _ _ _
      Hctx (Hthreads _ _ Hlookup) Halloc Hfresh Hvalues)
      as (σs & Hnext & Hworkers & Hqueues & Hsafe).
    eexists. eapply (runtime_replace_thread_and_local_session _ _ _ _ _ _ _ _ c (fin_gmap (S n) σs));
      try eassumption.
    + intros x _. now apply runtime_fresh_protocols_agree_on_owners.
    + intros d r Hne. now apply heap_spawn_lookup_outside_session.
    + now exists (init_chans (S n)).
Qed.

Lemma runtime_step_preserves_state_typing Σ es h es' h' :
  runtime_state_typed Σ es h →
  runtime_owners_unique es h →
  step es h es' h' →
  ∃ Σ', runtime_state_typed Σ' es' h'.
Proof.
  intros Hstate Hunique (i & Hstep).
  destruct Hstep as [e e' h h' i ws es Hcontext Hlookup].
  destruct Hcontext as [k e h e' h' ws Hctx Hhead].
  eapply runtime_typed_head_step_in_state; eassumption.
Qed.

Lemma runtime_initial_state_typed e :
  typed ∅ e UnitT →
  runtime_state_typed (λ _, ∅) [e] ∅.
Proof.
  intros Htyped. constructor.
  - intros [|i] a Hlook.
    + change (Some e = Some a) in Hlook. injection Hlook as <-.
      now apply source_typing_is_runtime_typed.
    + change ([] !! i = Some a) in Hlook. rewrite lookup_nil in Hlook. discriminate.
  - intros c. exists ∅. split.
    + constructor.
      * intros q.
        change (is_Some ((∅ : gmap participant (gmap participant (list sentryT))) !! q) ↔
          is_Some ((∅ : gmap endpoint (gmap participant (list entryT))) !! ((c,q) : endpoint))).
        rewrite !lookup_empty. split; intros [row Hrow]; discriminate.
      * intros q p. constructor.
    + apply terminated_session_empty_queues.
      * intros p σ Hsome. discriminate.
      * intros p bs Hsome. discriminate.
      * rewrite !dom_empty_L. reflexivity.
Qed.

Definition endpoint_stored_at (h : heap) (dest : endpoint)
    (sender : participant) (index : nat) (ep : endpoint) : Prop :=
  ∃ entries entry, buffer_at h dest sender = Some entries ∧
    entries !! index = Some entry ∧ ep ∈ val_endpoints entry.2.

Definition runtime_unique_queue_positions h : Prop :=
  ∀ dest sender index dest' sender' index' ep,
    endpoint_stored_at h dest sender index ep →
    endpoint_stored_at h dest' sender' index' ep →
    (dest,sender,index) = (dest',sender',index').

Lemma heap_endpoint_refs_have_queue_positions h c ep :
  ep ∈ heap_value_refs val_endpoints h c ↔
  ∃ q p index, endpoint_stored_at h (c,q) p index ep.
Proof.
  rewrite elem_of_heap_value_refs_iff. unfold endpoint_stored_at. split.
  - intros (q & p & label & v & (entries & Hqueue & Hmember) & Hv).
    apply list_elem_of_lookup in Hmember as (index & Hindex).
    exists q, p, index, entries, (label,v). now split.
  - intros (q & p & index & entries & [label v] & Hqueue & Hindex & Hv).
    exists q, p, label, v. split; [|exact Hv].
    exists entries. split; [exact Hqueue|].
    eapply list_elem_of_lookup_2. exact Hindex.
Qed.

Lemma queue_pop_endpoint_positions h h' dest sender entry other_dest other_sender index ep :
  pop sender dest h = Some (entry,h') →
  endpoint_stored_at h' other_dest other_sender index ep ↔
  endpoint_stored_at h other_dest other_sender
    (if decide (dest = other_dest ∧ sender = other_sender) then S index else index) ep.
Proof.
  intros Hpop.
  destruct (buffer_at_pop h sender dest entry h' Hpop) as (tail & Hold & Hnew).
  unfold endpoint_stored_at. rewrite Hnew.
  destruct (decide (dest = other_dest ∧ sender = other_sender)) as [[-> ->]|Hother];
    [|reflexivity].
  rewrite Hold. split.
  - intros (entries & a & Htail & Hlook & Howned). injection Htail as <-.
    exists (entry :: tail), a. split; [reflexivity|]. now split.
  - intros (entries & a & Htail & Hlook & Howned). injection Htail as <-.
    exists tail, a. split; [reflexivity|]. now split.
Qed.

Lemma queue_pop_preserves_position_uniqueness h h' dest sender entry :
  pop sender dest h = Some (entry,h') →
  runtime_unique_queue_positions h →
  runtime_unique_queue_positions h'.
Proof.
  intros Hpop Hunique dest1 sender1 idx1 dest2 sender2 idx2 ep H1 H2.
  apply (proj1 (queue_pop_endpoint_positions _ _ _ _ _ _ _ _ _ Hpop)) in H1, H2.
  pose proof (Hunique _ _ _ _ _ _ _ H1 H2) as Heq.
  inversion Heq; subst dest2 sender2.
  destruct (decide (dest = dest1 ∧ sender = sender1)); congruence.
Qed.

Lemma popped_payload_disjoint_from_remaining_queue_endpoints h h' c q p label v :
  runtime_unique_queue_positions h →
  pop p (c,q) h = Some ((label,v),h') →
  ∀ d, val_endpoints v ## heap_value_refs val_endpoints h' d.
Proof.
  intros Hunique Hpop d. apply elem_of_disjoint. intros ep Hv Hqueue.
  apply heap_endpoint_refs_have_queue_positions in Hqueue as (r & s & index & Hposition).
  apply (proj1 (queue_pop_endpoint_positions _ _ _ _ _ _ _ _ _ Hpop)) in Hposition.
  destruct (buffer_at_pop _ _ _ _ _ Hpop) as (tail & Hhead & _).
  assert (endpoint_stored_at h (c,q) p 0 ep) as Hstored.
  { exists ((label,v) :: tail), (label,v). split; [exact Hhead|]. now split. }
  pose proof (Hunique _ _ _ _ _ _ _ Hstored Hposition) as Heq.
  assert ((c,q) = (d,r) ∧ p = s) as Hloc by (inversion Heq; auto).
  rewrite decide_True in Heq by exact Hloc. discriminate.
Qed.


Lemma queue_push_endpoint_position_cases h dest sender entry other_dest other_sender index ep :
  endpoint_stored_at (push sender dest entry h) other_dest other_sender index ep →
  endpoint_stored_at h other_dest other_sender index ep ∨
  (other_dest = dest ∧ other_sender = sender ∧
    (∃ entries, buffer_at h dest sender = Some entries ∧ index = List.length entries) ∧
    ep ∈ val_endpoints entry.2).
Proof.
  intros (entries' & stored & Hqueue & Hindex & Howned).
  rewrite buffer_at_push in Hqueue.
  destruct (decide (dest = other_dest ∧ sender = other_sender)) as [[-> ->]|Hother].
  - destruct (buffer_at h other_dest other_sender) as [entries|] eqn:Hbefore; [|discriminate].
    injection Hqueue as <-.
    apply lookup_app_Some in Hindex as [Hindex|[Hlen Hindex]].
    + left. now exists entries, stored.
    + lazymatch type of Hindex with
      | _ !! ?offset = _ => destruct offset as [|j] eqn:Hi
      end.
      * change (Some entry = Some stored) in Hindex. injection Hindex as <-.
        right. split; [reflexivity|]. split; [reflexivity|].
        split; [exists entries; split; [reflexivity|]|exact Howned].
        apply Nat.le_antisymm; [now apply Nat.sub_0_le|exact Hlen].
      * change (([] : list entryT) !! j = Some stored) in Hindex.
        rewrite lookup_nil in Hindex. discriminate.
  - left. now exists entries', stored.
Qed.

Lemma queue_position_is_heap_reference h dest sender index ep :
  endpoint_stored_at h dest sender index ep →
  ep ∈ heap_value_refs val_endpoints h (fst dest).
Proof.
  destruct dest as [c q]. intros Hpos. apply heap_endpoint_refs_have_queue_positions.
  now exists q, sender, index.
Qed.

Lemma queue_push_preserves_position_uniqueness h dest sender entry :
  runtime_unique_queue_positions h →
  (∀ c, val_endpoints entry.2 ## heap_value_refs val_endpoints h c) →
  runtime_unique_queue_positions (push sender dest entry h).
Proof.
  intros Hunique Hdis dest1 sender1 idx1 dest2 sender2 idx2 ep H1 H2.
  apply queue_push_endpoint_position_cases in H1, H2.
  destruct H1 as [Hold1|(-> & -> & (entries1 & Hbuf1 & Hi1) & Hvalue1)];
    destruct H2 as [Hold2|(-> & -> & (entries2 & Hbuf2 & Hi2) & Hvalue2)].
  - exact (Hunique _ _ _ _ _ _ _ Hold1 Hold2).
  - exfalso. exact (proj1 (elem_of_disjoint _ _) (Hdis (fst dest1))
      ep Hvalue2 (queue_position_is_heap_reference _ _ _ _ _ Hold1)).
  - exfalso. exact (proj1 (elem_of_disjoint _ _) (Hdis (fst dest2))
      ep Hvalue1 (queue_position_is_heap_reference _ _ _ _ _ Hold2)).
  - congruence.
Qed.

Lemma retained_queue_positions_preserve_uniqueness h h' :
  runtime_unique_queue_positions h →
  (∀ dest sender index ep,
    endpoint_stored_at h' dest sender index ep → endpoint_stored_at h dest sender index ep) →
  runtime_unique_queue_positions h'.
Proof.
  intros Hunique Hretain d1 p1 i1 d2 p2 i2 ep H1 H2.
  exact (Hunique _ _ _ _ _ _ _ (Hretain _ _ _ _ H1) (Hretain _ _ _ _ H2)).
Qed.

Lemma queue_close_preserves_position_uniqueness (h : heap) c q :
  runtime_unique_queue_positions h →
  runtime_unique_queue_positions
    (delete ((c,q) : endpoint) (h : gmap endpoint (gmap participant (list entryT)))).
Proof.
  intros Hunique. eapply retained_queue_positions_preserve_uniqueness; [exact Hunique|].
  intros dest sender index ep (entries & entry & Hqueue & Hlookup & Howned).
  exists entries, entry. split; [|now split].
  unfold buffer_at in Hqueue |- *.
  destruct (decide (((c,q) : endpoint) = dest)) as [<-|Hne].
  - rewrite lookup_delete_eq in Hqueue. discriminate.
  - now rewrite lookup_delete_ne in Hqueue by exact Hne.
Qed.

Lemma queue_allocation_preserves_position_uniqueness (h : heap) c n :
  (∀ p, h !! (c,p) = None) →
  runtime_unique_queue_positions h →
  runtime_unique_queue_positions (gmap_unslice (init_chans n) c ∪ h).
Proof.
  intros Hfresh Hunique. eapply retained_queue_positions_preserve_uniqueness; [exact Hunique|].
  intros [d q] sender index ep (entries & entry & Hqueue & Hlookup & Howned).
  assert (queued_entry h (d,q) sender entry) as Hold.
  {
    apply (proj1 (allocation_preserves_queued_entries h c n d q sender entry Hfresh)).
    exists entries. split; [exact Hqueue|].
    eapply list_elem_of_lookup_2. exact Hlookup.
  }
  destruct (decide (d = c)) as [->|Hne].
  - destruct Hold as (old_entries & Hold & _).
    unfold buffer_at in Hold. rewrite Hfresh in Hold. discriminate.
  - exists entries, entry. split; [|now split].
    unfold buffer_at in Hqueue |- *.
    pose proof (heap_spawn_lookup_outside_session h c n d q Hne) as Hsame.
    etransitivity; [|exact Hqueue].
    exact (f_equal (λ row : option (gmap participant (list entryT)), row ≫= lookup sender) Hsame).
Qed.


Lemma runtime_step_preserves_queue_positions es h es' h' :
  runtime_owners_unique es h →
  runtime_unique_queue_positions h →
  step es h es' h' →
  runtime_unique_queue_positions h'.
Proof.
  intros Howners Hposition (i & Hstep).
  destruct Hstep as [e e' h h' i ws es Hcontext Hlookup].
  destruct Hcontext as [k e h e' h' ws Hctx Hhead].
  destruct Hhead as [e e' h Hpure | h c p q v label π | h c p q label v h' π Hpop |
    c q h π | h c n f fv Hfresh Hvalues].
  - exact Hposition.
  - apply queue_push_preserves_position_uniqueness; [exact Hposition|].
    intros d. apply elem_of_disjoint. intros ep Hval Hheap.
    assert (owns_endpoint es h (Thread i) ep) as Hthread.
    {
      eapply context_endpoint_is_owned; [exact Hctx|exact Hlookup|].
      cbn [expr_endpoints val_endpoints]. now apply elem_of_union_r.
    }
    apply (runtime_owned_endpoint_excluded_from_other_objects _ _ _ _ Howners Hthread
      (Chan d)); [discriminate|exact Hheap].
  - eapply queue_pop_preserves_position_uniqueness; eassumption.
  - now apply queue_close_preserves_position_uniqueness.
  - now apply queue_allocation_preserves_position_uniqueness.
Qed.

Lemma empty_heap_has_unique_queue_positions : runtime_unique_queue_positions ∅.
Proof.
  intros dest sender index dest' sender' index' ep (entries & entry & Hempty & _) _.
  discriminate.
Qed.

Definition runtime_live_endpoints_owned es (h : heap) : Prop :=
  ∀ ep, is_Some (h !! ep) → ∃ x, owns_endpoint es h x ep.

Definition relocated_endpoint_owner (own : object → endpoint → Prop)
    (target : object) (moved : gset endpoint) (x : object) (ep : endpoint) : Prop :=
  if decide (ep ∈ moved) then x = target else own x ep.

Lemma relocation_preserves_endpoint_ownership es h es' h' target moved :
  runtime_owners_unique es h →
  runtime_live_endpoints_owned es h →
  (∀ ep, is_Some (h' !! ep) → is_Some (h !! ep)) →
  (∀ x ep, owns_endpoint es' h' x ep ↔
    relocated_endpoint_owner (owns_endpoint es h) target moved x ep) →
  runtime_owners_unique es' h' ∧ runtime_live_endpoints_owned es' h'.
Proof.
  intros Hunique Hlive Hallocated Howners. split.
  - intros x y ep Hx Hy. apply Howners in Hx, Hy.
    unfold relocated_endpoint_owner in *. destruct (decide (ep ∈ moved)).
    + congruence.
    + eapply Hunique; eassumption.
  - intros ep Hvalid.
    destruct (Hlive ep (Hallocated ep Hvalid)) as (x & Hx).
    destruct (decide (ep ∈ moved)) as [Hmoved|Hretained].
    + exists target. apply Howners. unfold relocated_endpoint_owner.
      now rewrite decide_True.
    + exists x. apply Howners. unfold relocated_endpoint_owner.
      now rewrite decide_False.
Qed.

Lemma other_thread_endpoint_ownership es h h' i j e ep :
  i ≠ j →
  owns_endpoint (<[i := e]> es) h' (Thread j) ep ↔
    owns_endpoint es h (Thread j) ep.
Proof.
  intros Hne. unfold owns_endpoint, object_endpoints.
  now rewrite list_lookup_insert_ne.
Qed.

Lemma sent_payload_ownership_relocation Σ es (h : heap) i k c p q label π v :
  runtime_owners_unique es h →
  ctx k →
  es !! i = Some (k (Send q (Val (ChanV (c,p) π)) label (Val v))) →
  runtime_typed Σ ∅ (k (Send q (Val (ChanV (c,p) π)) label (Val v))) UnitT →
  is_present p (c,π q) h →
  let out := <[i := k (Val (ChanV (c,p) π))]> es in
  let h' := push p (c,π q) (label,v) h in
  ∀ x ep, owns_endpoint out h' x ep ↔
    relocated_endpoint_owner (owns_endpoint es h) (Chan c) (val_endpoints v) x ep.
Proof.
  intros Hunique Hctx Hlookup Htyped Hpresent. cbn zeta.
  set (request := Send q (Val (ChanV (c,p) π)) label (Val v)) in *.
  set (reply := Val (ChanV (c,p) π)) in *.
  destruct (closed_runtime_frame _ _ _ _ Hctx Htyped) as (τ & Hhead & Hframe & _).
  pose proof (runtime_communication_typing_observe _ _ _ _ Hhead) as Hview.
  cbn [request runtime_communication_typing_view] in Hview.
  destruct Hview as (Γ1 & Γ2 & n & ts & rs & tag & _ & _ & Hhead_sep & _).
  pose proof (update_thread_lookup es i (k request) (k reply) Hlookup) as Hreply.
  assert (∀ ep, ep ∈ val_endpoints v → owns_endpoint es h (Thread i) ep) as Hsent.
  {
    intros ep Hmem. eapply context_endpoint_is_owned; [exact Hctx|exact Hlookup|].
    cbn [request expr_endpoints val_endpoints]. now apply elem_of_union_r.
  }
  assert (∀ ep, ep ∈ val_endpoints v → ∀ y, y ≠ Thread i → ¬ owns_endpoint es h y ep)
    as Honly.
  {
    intros ep Hmem y Hne Hy. apply Hne. exact (Hunique _ _ _ Hy (Hsent ep Hmem)).
  }
  assert (is_Some (buffer_at h (c,π q) p)) as Hbuffer
    by (apply buffer_at_present; exact Hpresent).
  intros [j|d] ep; unfold relocated_endpoint_owner;
    destruct (decide (ep ∈ val_endpoints v)) as [Hmove|Hkeep].
  - destruct (decide (i = j)) as [<-|Hne].
    + rewrite (thread_endpoint_lookup _ _ _ _ _ Hreply), (ctx_endpoint_split k reply Hctx).
      cbn [reply expr_endpoints val_endpoints].
      cbn [request expr_endpoints val_endpoints] in Hframe, Hhead_sep.
      split; [|discriminate]. intros Hmem. exfalso. set_solver.
    + rewrite other_thread_endpoint_ownership by exact Hne.
      split; [|discriminate]. intros Hmem. exfalso.
      exact (Honly ep Hmove (Thread j) ltac:(congruence) Hmem).
  - destruct (decide (i = j)) as [<-|Hne].
    + rewrite (thread_endpoint_lookup _ _ _ _ _ Hreply),
        (thread_endpoint_lookup _ _ _ _ _ Hlookup),
        (ctx_endpoint_split k reply Hctx), (ctx_endpoint_split k request Hctx).
      cbn [request reply expr_endpoints val_endpoints]. set_solver.
    + now apply other_thread_endpoint_ownership.
  - unfold owns_endpoint, object_endpoints. rewrite heap_value_refs_push.
    split.
    + intros [Hold|(-> & _ & _)]; [|reflexivity].
      exfalso. exact (Honly ep Hmove (Chan d) ltac:(discriminate) Hold).
    + intros Heq. injection Heq as ->. right. now split.
  - unfold owns_endpoint, object_endpoints. rewrite heap_value_refs_push.
    split; [intros [Hold|(_ & _ & Hmem)]; contradiction || exact Hold|auto].
Qed.

Lemma received_payload_ownership_relocation es h h' i k c p q label π v :
  runtime_owners_unique es h →
  runtime_unique_queue_positions h →
  ctx k →
  es !! i = Some (k (Recv p (Val (ChanV (c,q) π)))) →
  pop (π p) (c,q) h = Some ((label,v),h') →
  let out := <[i := k (Val (InjNV label (PairV (ChanV (c,q) π) v)))]> es in
  ∀ x ep, owns_endpoint out h' x ep ↔
    relocated_endpoint_owner (owns_endpoint es h) (Thread i) (val_endpoints v) x ep.
Proof.
  intros Hunique Hqueues Hctx Hlookup Hpop. cbn zeta.
  set (request := Recv p (Val (ChanV (c,q) π))) in *.
  set (reply := Val (InjNV label (PairV (ChanV (c,q) π) v))) in *.
  pose proof (update_thread_lookup es i (k request) (k reply) Hlookup) as Hreply.
  pose proof (popped_payload_disjoint_from_remaining_queue_endpoints _ _ _ _ _ _ _
    Hqueues Hpop) as Hdisjoint.
  assert (∀ ep, ep ∈ val_endpoints v → owns_endpoint es h (Chan c) ep) as Hreceived.
  {
    intros ep Hin. unfold owns_endpoint, object_endpoints.
    apply (proj2 (heap_value_refs_pop val_endpoints h c q (π p) label v h' c ep Hpop)).
    right. now split.
  }
  intros [j|d] ep; unfold relocated_endpoint_owner;
    destruct (decide (ep ∈ val_endpoints v)) as [Hmove|Hkeep].
  - destruct (decide (i = j)) as [<-|Hne].
    + rewrite (thread_endpoint_lookup _ _ _ _ _ Hreply), (ctx_endpoint_split k reply Hctx).
      cbn [reply expr_endpoints val_endpoints]. split; [reflexivity|].
      intros _. set_solver.
    + rewrite other_thread_endpoint_ownership by exact Hne. split; [|congruence].
      intros Hother. discriminate (Hunique _ _ _ Hother (Hreceived ep Hmove)).
  - destruct (decide (i = j)) as [<-|Hne].
    + rewrite (thread_endpoint_lookup _ _ _ _ _ Hreply),
        (thread_endpoint_lookup _ _ _ _ _ Hlookup),
        (ctx_endpoint_split k reply Hctx), (ctx_endpoint_split k request Hctx).
      cbn [request reply expr_endpoints val_endpoints]. set_solver.
    + now apply other_thread_endpoint_ownership.
  - unfold owns_endpoint, object_endpoints. split; [|discriminate].
    intros Hmem. exfalso. exact (proj1 (elem_of_disjoint _ _) (Hdisjoint d) ep Hmove Hmem).
  - unfold owns_endpoint, object_endpoints.
    rewrite (heap_value_refs_pop val_endpoints h c q (π p) label v h' d ep Hpop).
    split; [auto|intros [Hmem|(_ & ?)]; contradiction || exact Hmem].
Qed.


Lemma dropped_endpoint_ownership Σ es (h : heap) i k c q π :
  runtime_owners_unique es h →
  ctx k →
  es !! i = Some (k (Close (Val (ChanV (c,q) π)))) →
  runtime_typed Σ ∅ (k (Close (Val (ChanV (c,q) π)))) UnitT →
  (∀ p entries, buffer_at h (c,q) p = Some entries → entries = []) →
  let out := <[i := k (Val UnitV)]> es in
  let h' := delete ((c,q) : endpoint) (h : gmap endpoint (gmap participant (list entryT))) in
  ∀ x ep, owns_endpoint out h' x ep ↔ owns_endpoint es h x ep ∧ ep ≠ (c,q).
Proof.
  intros Hunique Hctx Hlookup Htyped Hempty. cbn zeta.
  set (request := Close (Val (ChanV (c,q) π))) in *.
  pose proof (update_thread_lookup es i (k request) (k (Val UnitV)) Hlookup) as Hreply.
  destruct (closed_runtime_frame _ _ _ _ Hctx Htyped) as (τ & Hhole & Hframe & _).
  assert (owns_endpoint es h (Thread i) (c,q)) as Hown.
  { eapply context_endpoint_is_owned; [exact Hctx|exact Hlookup|].
    cbn [request expr_endpoints val_endpoints]. set_solver. }
  assert (∀ x, x ≠ Thread i → owns_endpoint es h x (c,q) → False) as Hothers.
  { intros x Hne Hx. apply Hne. exact (Hunique _ _ _ Hx Hown). }
  intros [j|d] ep.
  - destruct (decide (i = j)) as [<-|Hne].
    + rewrite (thread_endpoint_lookup _ _ _ _ _ Hreply),
        (thread_endpoint_lookup _ _ _ _ _ Hlookup),
        (ctx_endpoint_split k (Val UnitV) Hctx), (ctx_endpoint_split k request Hctx).
      cbn [request expr_endpoints val_endpoints] in *. set_solver.
    + rewrite other_thread_endpoint_ownership by exact Hne. split; [|tauto].
      intros Hkeep. split; [exact Hkeep|].
      intros ->. exact (Hothers (Thread j) ltac:(congruence) Hkeep).
  - unfold owns_endpoint, object_endpoints.
    rewrite (heap_value_refs_delete_empty_endpoint val_endpoints h c q d ep Hempty).
    split; [|tauto].
    intros Hkeep. split; [exact Hkeep|].
    intros ->. exact (Hothers (Chan d) ltac:(discriminate) Hkeep).
Qed.

Lemma heap_push_keeps_allocated_endpoints (h : heap) sender dest entry ep :
  is_Some (push sender dest entry h !! ep) → is_Some (h !! ep).
Proof.
  unfold push. destruct (decide (dest = ep)) as [->|Hne].
  - rewrite lookup_alter_eq. apply fmap_is_Some.
  - now rewrite lookup_alter_ne.
Qed.

Lemma allocated_workers_preserve_endpoint_ownership es (h : heap) i k c n
    (f : fin n → expr) (fv : fin n → val) :
  ctx k →
  es !! i = Some (k (Spawn n f)) →
  (∀ p, f p = Val (fv p)) →
  (∀ p, h !! (c,p) = None) →
  expr_endpoints (Spawn n f) ## expr_endpoints (k (Val UnitV)) →
  let out := <[i := k (Val (ChanV (c,0) id))]> es ++ init_threads c n fv in
  let h' := gmap_unslice (init_chans (S n) : bufsT participant participant entryT) c ∪ h in
  ∀ x ep, owns_endpoint out h' x ep ↔
    allocation_owner_stage (owns_endpoint es h) i (List.length es) c
      (λ p, val_endpoints (fv p)) (fin_gset n (λ p, p)) x ep.
Proof.
  intros Hctx Hlookup Hvalues Hfresh Hsep. cbn zeta.
  set (main := <[i := k (Val (ChanV (c,0) id))]> es).
  set (init := gmap_unslice (init_chans (S n) : bufsT participant participant entryT) c ∪ h).
  set (done := fin_gset n (λ p, p)).
  assert (List.length main = List.length es) as Hsize by (unfold main; apply length_insert).
  assert (i < List.length es) as Hi by (apply lookup_lt_is_Some; now exists (k (Spawn n f))).
  assert (∀ p : fin n, p ∈ done) as Hdone.
  { unfold done, fin_gset. intros p. apply elem_of_list_to_set, elem_of_fin_list_iff. now exists p. }
  assert (∀ ep, ep ∈ expr_endpoints (Spawn n f) ↔ ∃ p, ep ∈ val_endpoints (fv p)) as Hcaptured.
  {
    intro ep. cbn [expr_endpoints]. rewrite elem_of_fin_union_iff.
    cbn [compose]. split; intros (p & Hp); exists p;
      [now rewrite Hvalues in Hp|now rewrite Hvalues].
  }
  assert (∀ ep, ep ∈ expr_endpoints (k (Val UnitV)) → ∀ p, ep ∉ val_endpoints (fv p)) as Hframe.
  {
    intros ep Hin p Hmem.
    apply (proj1 (elem_of_disjoint _ _) Hsep ep); [|exact Hin].
    apply Hcaptured. now exists p.
  }
  assert ((main ++ init_threads c n fv) !! i = Some (k (Val (ChanV (c,0) id)))) as Hreply.
  { apply lookup_app_l_Some. unfold main. exact (update_thread_lookup _ _ _ _ Hlookup). }
  intros x ep. split.
  - intros Hown. destruct x as [j|d].
    + destruct (decide (j < List.length es)) as [Hj|Hj].
      * destruct (decide (i = j)) as [<-|Hne].
        -- apply (proj1 (thread_endpoint_lookup _ _ _ _ _ Hreply)) in Hown.
           rewrite (ctx_endpoint_split k (Val (ChanV (c,0) id)) Hctx) in Hown.
           apply elem_of_union in Hown as [Hnew|Hold].
           ++ right. left. split; [reflexivity|exact (proj1 (elem_of_singleton _ _) Hnew)].
           ++ left. split.
              ** apply (proj2 (thread_endpoint_lookup _ _ _ _ _ Hlookup)).
                 rewrite (ctx_endpoint_split _ _ Hctx). now apply elem_of_union_r.
              ** right. now apply Hframe.
        -- unfold owns_endpoint, object_endpoints in Hown.
           rewrite lookup_app_l in Hown by lia.
           unfold main in Hown. rewrite list_lookup_insert_ne in Hown by exact Hne.
           left. split; [exact Hown|left; congruence].
      * unfold owns_endpoint, object_endpoints in Hown.
        destruct ((main ++ init_threads c n fv) !! j) as [worker|] eqn:Hlook;
          cbn in Hown; [|now apply elem_of_empty in Hown].
        destruct (allocated_worker_is_at_finite_index main c n fv j worker ltac:(lia) Hlook)
          as (p & -> & ->).
        right. right. right. exists p. rewrite Hsize.
        split; [apply Hdone|]. split; [reflexivity|].
        cbn [expr_endpoints val_endpoints] in Hown.
        rewrite elem_of_union, elem_of_singleton in Hown. tauto.
    + unfold owns_endpoint, object_endpoints in Hown.
      left. split; [|left; discriminate].
      exact (proj1 (allocation_has_old_queued_endpoint_references h c n d ep Hfresh) Hown).
  - intros [(Hown & Hnotcaptured)|[(-> & ->)|[(_ & p & Hnot & _)|(p & Hp & -> & Hep)]]].
    + destruct x as [j|d].
      * destruct (decide (i = j)) as [<-|Hne].
        -- apply (proj1 (thread_endpoint_lookup _ _ _ _ _ Hlookup)) in Hown.
           rewrite (ctx_endpoint_split k (Spawn n f) Hctx) in Hown.
           apply elem_of_union in Hown as [Hmove|Hown].
           ++ destruct Hnotcaptured as [Hne|Hnot]; [contradiction|].
              apply Hcaptured in Hmove as (p & Hmove). contradiction (Hnot p Hmove).
           ++ apply (proj2 (thread_endpoint_lookup _ _ _ _ _ Hreply)).
              rewrite (ctx_endpoint_split k (Val (ChanV (c,0) id)) Hctx).
              now apply elem_of_union_r.
        -- unfold owns_endpoint, object_endpoints in Hown |- *.
           destruct (es !! j) as [src|] eqn:Hsrc; cbn in Hown; [|set_solver].
           assert (main !! j = Some src) as Hmain.
           { unfold main. now rewrite list_lookup_insert_ne. }
           rewrite (lookup_app_l_Some _ _ _ _ Hmain). exact Hown.
      * exact (proj2 (allocation_has_old_queued_endpoint_references h c n d ep Hfresh) Hown).
    + apply (proj2 (thread_endpoint_lookup _ _ _ _ _ Hreply)).
      rewrite (ctx_endpoint_split k (Val (ChanV (c,0) id)) Hctx).
      cbn [expr_endpoints val_endpoints]. set_solver.
    + contradiction (Hnot (Hdone p)).
    + rewrite <- Hsize. apply (proj2 (thread_endpoint_lookup _ _ _ _ _
        (allocated_worker_lookup main c n fv p))).
      cbn [expr_endpoints val_endpoints]. rewrite elem_of_union, elem_of_singleton. tauto.
Qed.


Lemma spawn_preserves_live_and_unique_ownership Σ es (h : heap) i k c n
    (f : fin n → expr) (fv : fin n → val) :
  runtime_state_typed Σ es h →
  runtime_owners_unique es h →
  runtime_live_endpoints_owned es h →
  ctx k →
  es !! i = Some (k (Spawn n f)) →
  (∀ p, f p = Val (fv p)) →
  (∀ p, h !! (c,p) = None) →
  let out := <[i := k (Val (ChanV (c,0) id))]> es ++ init_threads c n fv in
  let h' := gmap_unslice (init_chans (S n) : bufsT participant participant entryT) c ∪ h in
  runtime_owners_unique out h' ∧ runtime_live_endpoints_owned out h'.
Proof.
  intros Hstate Hunique Hlive Hctx Hlookup Hvalues Hfresh. cbn zeta.
  destruct Hstate as [Hthreads Hsessions].
  destruct (closed_runtime_frame _ _ _ _ Hctx (Hthreads _ _ Hlookup))
    as (τ & Hhead & Hsep & _).
  pose proof (allocated_workers_preserve_endpoint_ownership _ _ _ _ _ _ _ _ Hctx
    Hlookup Hvalues Hfresh Hsep) as Hmatches.
  cbn zeta in Hmatches.
  assert (∀ p : fin n, p ∈ fin_gset n (λ p, p)) as Hdone.
  { unfold fin_gset. intro p. apply elem_of_list_to_set, elem_of_fin_list_iff. now exists p. }
  split.
  - intros x y ep Hx Hy. apply Hmatches in Hx, Hy.
    eapply allocation_owner_stage_unique; [exact Hunique| | | |exact Hx|exact Hy].
    + intros z [d q] Howns Heq. cbn in Heq. subst d.
      destruct (runtime_state_owners_have_allocated_endpoints _ _ _ Hthreads Hsessions
        _ _ Howns) as [bs Hbs]. rewrite Hfresh in Hbs. discriminate.
    + intros p epend Hep.
      eapply context_endpoint_is_owned; [exact Hctx|exact Hlookup|].
      cbn [expr_endpoints]. apply elem_of_fin_union_iff.
      exists p. cbn [compose]. now rewrite Hvalues.
    + intros p q Hne.
      pose proof (runtime_spawn_workers_separated _ _ _ _ Hhead n f eq_refl p q Hne) as Hworkers.
      now rewrite !Hvalues in Hworkers.
  - intros [d q] Hvalid.
    destruct (decide (d = c)) as [->|Hne].
    + assert (q < S n) as Hq.
      {
        destruct Hvalid as [bs Hbs].
        assert ((init_chans (S n) : bufsT participant participant entryT) !! q = Some bs)
          as Hinit by (etransitivity; [symmetry; exact
            (allocated_session_endpoint_lookup h c (S n) q Hfresh)|exact Hbs]).
        unfold init_chans in Hinit.
        apply lookup_finite_constant in Hinit as [_ Hlt]. exact Hlt.
      }
      destruct q as [|q].
      * exists (Thread i). apply Hmatches. right. left. now split.
      * assert (q < n) as Hlt by lia.
        set (p := nat_to_fin Hlt).
        exists (Thread (List.length es + fin_to_nat p)). apply Hmatches.
        right. right. right. exists p.
        split; [apply Hdone|]. split; [reflexivity|].
        left. unfold p. now rewrite fin_to_nat_to_fin.
    + assert (is_Some (h !! (d,q))) as Hold.
      {
        destruct Hvalid as [bs Hbs]. exists bs.
        etransitivity; [exact (heap_spawn_lookup_outside_session h c (S n) d q Hne)|exact Hbs].
      }
      destruct (decide ((d,q) ∈ fin_union n (λ p, val_endpoints (fv p)))) as [Hmember|Hnone].
      * apply elem_of_fin_union_iff in Hmember as (p & Hp).
        exists (Thread (List.length es + fin_to_nat p)). apply Hmatches.
        right. right. right. exists p. split; [exact (Hdone p)|].
        split; [reflexivity|now right].
      * destruct (Hlive (d,q) Hold) as (x & Hx).
        exists x. apply Hmatches. left. split; [exact Hx|].
        right. intros p Hp. apply Hnone, elem_of_fin_union_iff. now exists p.
Qed.

Definition runtime_endpoint_forest es h : Prop :=
  ∀ x ep, ¬ nonbacktracking_ownership_walk (ownership_edge (owns_endpoint es h)) x ep x.

Lemma runtime_head_preserves_ownership Σ es h i k e e' h' ws :
  runtime_state_typed Σ es h →
  runtime_owners_unique es h →
  runtime_live_endpoints_owned es h →
  runtime_unique_queue_positions h →
  runtime_endpoint_forest es h →
  ctx k →
  es !! i = Some (k e) →
  head_step e h e' h' ws →
  let out := <[i := k e']> es ++ ws in
  runtime_owners_unique out h' ∧
  runtime_live_endpoints_owned out h' ∧ runtime_endpoint_forest out h'.
Proof.
  intros Hstate Hunique Hlive Hpositions Hforest Hctx Hlookup Hstep.
  unfold runtime_endpoint_forest in *.
  pose proof (runtime_state_threads _ _ _ Hstate) as Hthreads.
  pose proof (runtime_state_sessions _ _ _ Hstate) as Hsessions.
  destruct Hstep as [e e' h Hpure | h c p q v label π | h c p q label v h' π Hpop |
    c q h π | h c n f fv Hfresh Hvalues]; cbn zeta; try rewrite app_nil_r.
  - destruct (pure_thread_reduction_preserves_typing_and_ownership Σ es h i k e e'
      Hctx Hlookup Hpure Hthreads) as [_ Hrefs].
    assert (∀ x ep, owns_endpoint (<[i := k e']> es) h x ep ↔ owns_endpoint es h x ep)
      as Hsame by (intros x ep; unfold owns_endpoint; now rewrite Hrefs).
    split.
    + intros x y ep Hx Hy. apply Hsame in Hx, Hy. eauto.
    + split.
      * intros ep Halloc. destruct (Hlive ep Halloc) as (x & Hx).
        exists x. now apply Hsame.
      * eapply ownership_subgraph_preserves_forest; [|exact Hforest].
        intros x ep. apply Hsame.
  - assert (owns_endpoint es h (Thread i) (c,p)) as Hport.
    { eapply context_endpoint_is_owned; [exact Hctx|exact Hlookup|].
      cbn [expr_endpoints val_endpoints]. set_solver. }
    assert ((c,p) ∉ heap_value_refs val_endpoints h c) as Hnoheap.
    {
      apply (runtime_owned_endpoint_excluded_from_other_objects _ _ _ _
        Hunique Hport (Chan c)). discriminate.
    }
    destruct (Hsessions c) as (bufs & Hqueues & Hsafe).
    destruct (runtime_send_context_preservation _ _ _ _ _ _ _ _ _ _ _
      Hctx (Hthreads _ _ Hlookup) Hqueues Hsafe Hnoheap) as (σ & bufs' & Hpresent & _).
    pose proof (sent_payload_ownership_relocation _ _ _ _ _ _ _ _ _ _ _
      Hunique Hctx Hlookup (Hthreads _ _ Hlookup) Hpresent) as Hmove.
    destruct (relocation_preserves_endpoint_ownership _ _ _ _ _ _ Hunique Hlive
      (heap_push_keeps_allocated_endpoints h p (c,π q) (label,v)) Hmove)
      as [Hnew Hnewlive].
    split; [exact Hnew|]. split; [exact Hnewlive|].
    eapply send_preserves_endpoint_forest; eassumption.
  - pose proof (received_payload_ownership_relocation _ _ _ _ _ _ _ _ _ _ _
      Hunique Hpositions Hctx Hlookup Hpop) as Hmove.
    destruct (queue_pop_updates h (π p) (c,q) (label,v) h' Hpop)
      as (tail & Hhead & Hallocated & Hbuffers).
    destruct (relocation_preserves_endpoint_ownership _ _ _ _ _ _ Hunique Hlive
      (λ ep, proj1 (Hallocated ep)) Hmove) as [Hnew Hnewlive].
    split; [exact Hnew|]. split; [exact Hnewlive|].
    eapply receive_preserves_endpoint_forest; eassumption.
  - assert (owns_endpoint es h (Thread i) (c,q)) as Hport.
    { eapply context_endpoint_is_owned; [exact Hctx|exact Hlookup|].
      cbn [expr_endpoints val_endpoints]. set_solver. }
    assert ((c,q) ∉ heap_value_refs val_endpoints h c) as Hnoheap.
    {
      apply (runtime_owned_endpoint_excluded_from_other_objects _ _ _ _
        Hunique Hport (Chan c)). discriminate.
    }
    destruct (Hsessions c) as (bufs & Hqueues & Hsafe).
    destruct (runtime_close_context_preservation _ _ _ _ _ _ _ _
      Hctx (Hthreads _ _ Hlookup) Hqueues Hsafe Hnoheap) as (_ & Hempty & _).
    pose proof (dropped_endpoint_ownership _ _ _ _ _ _ _ _
      Hunique Hctx Hlookup (Hthreads _ _ Hlookup) Hempty) as Hdrop.
    split.
    + intros x y ep Hx Hy. apply Hdrop in Hx as [Hx _], Hy as [Hy _].
      eapply Hunique; eassumption.
    + split.
      * intros ep [bs Hbs].
        apply lookup_delete_Some in Hbs as [Hne Hbs].
        destruct (Hlive ep ltac:(now exists bs)) as (x & Hx).
        exists x. apply Hdrop. split; [exact Hx|congruence].
      * eapply close_preserves_endpoint_forest; eassumption.
  - destruct (spawn_preserves_live_and_unique_ownership _ _ _ _ _ _ _ _ _
      Hstate Hunique Hlive Hctx Hlookup Hvalues Hfresh) as [Hnew Hnewlive].
    split; [exact Hnew|]. split; [exact Hnewlive|].
    eapply typed_spawn_preserves_endpoint_forest; eassumption.
Qed.

Record runtime_state_invariant Σ es h : Prop := {
  invariant_state_typing : runtime_state_typed Σ es h;
  invariant_unique_endpoint_owners : runtime_owners_unique es h;
  invariant_live_endpoint_owners : runtime_live_endpoints_owned es h;
  invariant_unique_queue_positions : runtime_unique_queue_positions h;
  invariant_endpoint_forest : runtime_endpoint_forest es h
}.

Lemma runtime_step_preserves_invariant Σ es h es' h' :
  runtime_state_invariant Σ es h →
  step es h es' h' →
  ∃ Σ', runtime_state_invariant Σ' es' h'.
Proof.
  intros [Hstate Hunique Hlive Hqueues Hforest] Hstep.
  destruct (runtime_step_preserves_state_typing _ _ _ _ _ Hstate Hunique Hstep)
    as (Σ' & Hstate').
  pose proof (runtime_step_preserves_queue_positions _ _ _ _ Hunique Hqueues Hstep)
    as Hqueues'.
  destruct Hstep as (i & Hstep).
  destruct Hstep as [e e' h h' i ws es Hcontext Hlookup].
  destruct Hcontext as [k e h e' h' ws Hctx Hhead].
  destruct (runtime_head_preserves_ownership _ _ _ _ _ _ _ _ _
    Hstate Hunique Hlive Hqueues Hforest Hctx Hlookup Hhead) as (Hunique' & Hlive' & Hforest').
  exists Σ'. now constructor.
Qed.

Lemma closed_typed_initial_state_has_no_ownership e :
  typed ∅ e UnitT → ∀ x ep, ¬ owns_endpoint [e] ∅ x ep.
Proof.
  intros Htyped [i|c] ep Howner.
  - unfold owns_endpoint, object_endpoints in Howner. destruct i as [|i].
    + change (ep ∈ expr_endpoints e) in Howner.
      rewrite (source_typing_has_no_endpoints _ _ _ Htyped) in Howner. set_solver.
    + change (ep ∈ from_option expr_endpoints ∅ (([] : list expr) !! i)) in Howner.
      rewrite lookup_nil in Howner. cbn in Howner. set_solver.
  - apply (fresh_heap_session_has_no_endpoint_references ∅ c ep); [|exact Howner].
    intros p. change ((∅ : gmap endpoint (gmap participant (list entryT))) !! (c,p) = None).
    apply lookup_empty.
Qed.

Lemma runtime_initial_state_invariant e :
  typed ∅ e UnitT → runtime_state_invariant (λ _, ∅) [e] ∅.
Proof.
  intros Htyped.
  pose proof (closed_typed_initial_state_has_no_ownership e Htyped) as Hnone.
  constructor.
  - now apply runtime_initial_state_typed.
  - intros x y ep Hx Hy. exfalso. exact (Hnone x ep Hx).
  - intros ep (bs & Hlookup). discriminate.
  - exact empty_heap_has_unique_queue_positions.
  - intros x ep Hwalk.
    destruct (ownership_walk_first_edge _ _ _ _ Hwalk) as (y & Hlink).
    destruct Hlink as [(_ & Hown)|(_ & Hown)]; eapply Hnone; exact Hown.
Qed.

Lemma runtime_steps_preserve_invariant Σ es h es' h' :
  runtime_state_invariant Σ es h →
  steps es h es' h' →
  ∃ Σ', runtime_state_invariant Σ' es' h'.
Proof.
  intros Hinv Hsteps. revert Σ Hinv.
  induction Hsteps as [es1 es2 es3 h1 h2 h3 Hstep Hsteps IH|es h];
    intros Σ Hinv.
  - destruct (runtime_step_preserves_invariant _ _ _ _ _ Hinv Hstep) as (Σ' & Hinv').
    exact (IH Σ' Hinv').
  - now exists Σ.
Qed.

Lemma reachable_state_properties_given_spawn_contexts e es h :
  spawn_worker_context_decomposition →
  typed ∅ e UnitT → steps [e] ∅ es h →
  deadlock_free es h ∧ fully_reachable es h.
Proof.
  intros Hspawn Htyped Hsteps.
  destruct (runtime_steps_preserve_invariant _ _ _ _ _
    (runtime_initial_state_invariant e Htyped) Hsteps) as (Σ & Hinv).
  destruct Hinv as [[Hthreads Hsessions] Hunique Hlive Hpositions Hforest].
  assert (fully_reachable es h) as Hfull.
  {
    eapply (runtime_typed_state_is_fully_reachable Σ); try eassumption.
    - exact (runtime_typed_sessions_have_allocated_endpoints _ _ Hsessions).
    - intros c _. apply Hsessions.
    - intros c q. apply (Hlive (c,q)).
  }
  split; [now apply full_reachability_implies_deadlock_freedom|exact Hfull].
Qed.

Lemma empty_heap_deadlock_freedom_iff_stable_progress es :
  deadlock_free es ∅ ↔
  ∀ i, active es ∅ (Thread i) → ¬ ¬ can_stepi i es ∅.
Proof.
  assert (∀ ep : endpoint, (∅ : heap) !! ep = None) as Hempty.
  {
    intros ep. change ((∅ : gmap endpoint (gmap participant (list entryT))) !! ep = None).
    apply lookup_empty.
  }
  split.
  - intros Hfree i Hactive Hstuck.
    apply (Hfree ({[Thread i]} : gset object)). constructor.
    + set_solver.
    + intros x Hmem. apply elem_of_singleton in Hmem as ->. exact Hactive.
    + intros j Hmem. apply elem_of_singleton in Hmem. injection Hmem as ->. exact Hstuck.
    + intros j c Hmem (p & q & k & π & _ & _ & [bs Hlookup] & _).
      rewrite Hempty in Hlookup. discriminate.
    + intros c x Hmem. apply elem_of_singleton in Hmem. discriminate.
  - intros Hprogress s Hdeadlock.
    apply (dl_nonempty _ _ _ Hdeadlock). apply set_eq. intro x.
    rewrite elem_of_empty. split; [|contradiction].
    intros Hmem. pose proof (dl_active _ _ _ Hdeadlock x Hmem) as Hactive.
    destruct x as [i|c].
    + exact (Hprogress i Hactive (dl_threadb _ _ _ Hdeadlock i Hmem)).
    + destruct Hactive as (p & bs & Hlookup).
      rewrite Hempty in Hlookup. discriminate.
Qed.

Lemma singleton_source_active_thread_index e i :
  active [e] ∅ (Thread i) → i = 0.
Proof.
  intros (current & Hlookup & _).
  destruct i as [|i]; [reflexivity|].
  change (([] : list expr) !! i = Some current) in Hlookup.
  rewrite lookup_nil in Hlookup. discriminate.
Qed.

Lemma closing_spawn_can_step_iff_worker_context :
  can_stepi 0 [Close (Spawn 1 (λ _, closing_spawn_worker))] ∅ ↔
  spawn_source_has_context 1 (λ _, closing_spawn_worker).
Proof.
  rewrite <- closing_spawn_full_reachability_iff_worker_context.
  rewrite empty_heap_full_reachability_iff_progress.
  split.
  - intros Hstep i Hactive.
    rewrite (singleton_source_active_thread_index _ _ Hactive).
    exact Hstep.
  - intros Hprogress. apply Hprogress.
    exists (Close (Spawn 1 (λ _, closing_spawn_worker))).
    split; [reflexivity|discriminate].
Qed.

Lemma closing_spawn_deadlock_freedom_iff_stable_worker_context :
  deadlock_free [Close (Spawn 1 (λ _, closing_spawn_worker))] ∅ ↔
  ¬ ¬ spawn_source_has_context 1 (λ _, closing_spawn_worker).
Proof.
  rewrite empty_heap_deadlock_freedom_iff_stable_progress.
  rewrite <- closing_spawn_can_step_iff_worker_context.
  split.
  - intros Hprogress. apply Hprogress.
    exists (Close (Spawn 1 (λ _, closing_spawn_worker))).
    split; [reflexivity|discriminate].
  - intros Hstable i Hactive.
    rewrite (singleton_source_active_thread_index _ _ Hactive).
    exact Hstable.
Qed.

Lemma finite_worker_function_equality_gives_spawn_contexts :
  (∀ n (f g : fin n → expr), (∀ p, f p = g p) → f = g) →
  spawn_worker_context_decomposition.
Proof.
  intros Hext n f p _. exists f. apply Hext.
  intros q. destruct (decide (p = q)) as [->|Hne]; reflexivity.
Qed.

Lemma runtime_blocked_thread_has_waiting_protocol Σ es h i c :
  runtime_state_typed Σ es h →
  thread_blocked es h i c →
  ∃ q σ, owns_endpoint es h (Thread i) (c,q) ∧
    Σ c !! q = Some σ ∧ ¬ ready_session_action h c q σ.
Proof.
  intros Hstate (p & q & k & π & Hctx & Hlookup & _ & Hpop).
  destruct (closed_runtime_frame _ _ _ _ Hctx
    (runtime_state_threads _ _ _ Hstate _ _ Hlookup))
    as (τ & Hhead & _ & _).
  destruct (runtime_communication_typing_observe _ _ _ _ Hhead)
    as (n & ts & rs & Hchan & _).
  destruct (runtime_receive_pointer_view _ _ _ _ _ _ _ _ Hchan)
    as (us & vs & Hσ & _ & _).
  exists q, (RecvT n (π p) us vs). split.
  - eapply context_endpoint_is_owned; [exact Hctx|exact Hlookup|].
    cbn [expr_endpoints val_endpoints]. set_solver.
  - split; [exact Hσ|].
    intros (entry & h' & Hready). discriminate (eq_trans (eq_sym Hpop) Hready).
Qed.

Lemma reachable_thread_steps_or_waits es h i :
  reachable es h (Thread i) →
  can_stepi i es h ∨ ∃ c, thread_blocked es h i c.
Proof.
  intros Hreachable. inversion Hreachable; subst; eauto.
Qed.

Lemma runtime_full_reachability_iff_active_thread_progress Σ es h :
  runtime_state_invariant Σ es h →
  (fully_reachable es h ↔
    ∀ i, active es h (Thread i) →
      can_stepi i es h ∨ ∃ c, thread_blocked es h i c).
Proof.
  intros [Htyping Hunique Hlive Hqueues Hforest]. split.
  - intros Hfull i Hactive. apply reachable_thread_steps_or_waits.
    now apply Hfull.
  - intros Hprogress.
    apply (full_reachability_from_protocol_ownership es h
      (λ v t, runtime_typed Σ ∅ (Val v) t) Σ (owns_endpoint es h)).
    + intros i Hactive.
      destruct (Hprogress i Hactive) as [Hstep|(c & Hblocked)].
      * now left.
      * destruct (runtime_blocked_thread_has_waiting_protocol _ _ _ _ _ Htyping Hblocked)
          as (q & σ & Hown & Hσ & Hnot).
        right. exists c, q, σ. auto.
    + intros c _. exact (runtime_state_sessions _ _ _ Htyping c).
    + intros c q. apply (Hlive (c,q)).
    + intros x c q Hown. apply channel_ref_iff_owned_endpoint. now exists q.
    + exact Hforest.
Qed.

Lemma reachable_state_properties_iff_active_thread_progress :
  (∀ e es h, typed ∅ e UnitT → steps [e] ∅ es h →
    deadlock_free es h ∧ fully_reachable es h) ↔
  (∀ e es h i, typed ∅ e UnitT → steps [e] ∅ es h → active es h (Thread i) →
    can_stepi i es h ∨ ∃ c, thread_blocked es h i c).
Proof.
  split.
  - intros Htarget e es h i Htyped Hsteps Hactive.
    destruct (Htarget e es h Htyped Hsteps) as [_ Hfull].
    apply reachable_thread_steps_or_waits, Hfull, Hactive.
  - intros Hprogress e es h Htyped Hsteps.
    destruct (runtime_steps_preserve_invariant _ _ _ _ _
      (runtime_initial_state_invariant e Htyped) Hsteps) as (Σ & Hinv).
    assert (fully_reachable es h) as Hfull.
    {
      apply (proj2 (runtime_full_reachability_iff_active_thread_progress _ _ _ Hinv)).
      intro i. exact (Hprogress e es h i Htyped Hsteps).
    }
    split; [now apply full_reachability_implies_deadlock_freedom|exact Hfull].
Qed.

Theorem deadlock_freedom_and_full_reachability e es h :
  typed ∅ e UnitT -> steps [e] ∅ es h ->
  deadlock_free es h ∧ fully_reachable es h.
