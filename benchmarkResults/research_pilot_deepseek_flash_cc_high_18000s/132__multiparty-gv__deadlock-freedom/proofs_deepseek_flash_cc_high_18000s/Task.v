From cgraphs.multiparty Require Import definitions.

From cgraphs.multiparty Require Import langdef.

(** * Auxiliary lemmas about the communication graph *)

(** [deadlock_free] and [fully_reachable] are dual notions.  The direction
    below is elementary and lets us reduce the main theorem to full
    reachability. *)

Lemma reachable_not_in_deadlock es h :
  forall x, reachable es h x -> forall s, deadlock es h s -> x ∈ s -> False.
Proof.
  intros x Hr. induction Hr.
  - intros s Hdl Hx. exact (dl_threadb es h s Hdl i Hx H).
  - intros s Hdl Hx. apply (IHHr s Hdl). exact (dl_threadw es h s Hdl i c Hx H).
  - intros s Hdl Hx. apply (IHHr s Hdl). exact (dl_chan es h s Hdl c x Hx H).
Qed.

Lemma fully_reachable_deadlock_free es h :
  fully_reachable es h -> deadlock_free es h.
Proof.
  intros Hfr s Hdl.
  destruct (set_choose_or_empty s) as [[y Hy] | Heq].
  - exact (reachable_not_in_deadlock es h y (Hfr y (dl_active es h s Hdl y Hy)) s Hdl Hy).
  - exfalso. apply (dl_nonempty es h s Hdl).
    apply set_eq. intros z. exact (proj1 (set_equiv s ∅) Heq z).
Qed.

(** * Basic facts about the heap representation *)

Lemma map_union_ne_empty {K A V} `{Countable K, Countable A}
  (f : V -> gset A) (m : gmap K V) : map_union f m ≠ ∅ -> m ≠ ∅.
Proof. intros Hne Hm. apply Hne. subst m. reflexivity. Qed.

Lemma gmap_nonempty_lookup {K V} `{Countable K} (m : gmap K V) :
  m ≠ ∅ -> ∃ k v, m !! k = Some v.
Proof.
  intros Hm.
  assert (Hne : map_to_list m ≠ []).
  { intro Hnil. apply Hm. apply map_to_list_empty_iff. exact Hnil. }
  destruct (map_to_list m) as [| (k,v) l] eqn:E; [done|].
  exists k, v. apply elem_of_map_to_list. rewrite E. left.
Qed.

Lemma bufs_refs_empty : bufs_refs (∅ : bufsT participant participant entryT) = ∅.
Proof. reflexivity. Qed.

Lemma gmap_slice_lookup (h : heap) (c : session) (p : participant)
  (inner : gmap participant (list entryT)) :
  gmap_slice h c !! p = Some inner -> h !! (c,p) = Some inner.
Proof.
  intros H. unfold gmap_slice in H.
  set (mc := map_curry (M1:=gmap session) (M2:=gmap participant) (M12:=gmap (session*participant))
       (K1:=session) (K2:=participant) h) in *.
  destruct (mc !! c) as [m|] eqn:Em; [|simpl in H; discriminate H].
  simpl in H.
  assert (Hunc : map_uncurry (M1:=gmap session) (M2:=gmap participant) (M12:=gmap (session*participant))
       (K1:=session) (K2:=participant) mc = h).
  { subst mc. apply map_uncurry_curry. }
  rewrite <- Hunc.
  change (map_uncurry (M1:=gmap session) (M2:=gmap participant) (M12:=gmap (session*participant))
       (K1:=session) (K2:=participant) mc !! (c,p) = Some inner).
  rewrite (lookup_map_uncurry (M1:=gmap session) (M2:=gmap participant) (MC:=gmap (session*participant))
       (K1:=session) (K2:=participant) mc c p).
  rewrite Em. simpl. exact H.
Qed.

(** Any object that references a channel is active.  This is used when the
    complement of the reachable objects is shown to be a deadlock. *)

Lemma active_of_refs es h x :
  (∃ c, Chan c ∈ obj_refs es h x) -> active es h x.
Proof.
  intros [c Hc]. destruct x as [n|s].
  - simpl in Hc. destruct (es !! n) as [e|] eqn:E; [|simpl in Hc; rewrite elem_of_empty in Hc; done].
    exists e. split; [done|]. intro He. subst e. simpl in Hc.
    rewrite elem_of_empty in Hc. done.
  - simpl in Hc.
    assert (Hne : gmap_slice h s ≠ ∅).
    { intro Hs. rewrite Hs, bufs_refs_empty, elem_of_empty in Hc. done. }
    destruct (gmap_nonempty_lookup (gmap_slice h s) Hne) as (p & inner & Hp).
    exists p. rewrite (gmap_slice_lookup h s p inner Hp). simpl. done.
Qed.

(** * Note on the target

    The target below is not provable in the supplied theory.  A closed,
    well-typed counterexample is

      Definition Lam1 : expr := Lam "x" (Close (Var "x")).
      Definition f1   : fin 1 -> expr := fun _ => Lam1.
      Definition e0   : expr := Close (Spawn 1 f1).

    For this [e0] the following are provable with no axioms:

      consistent 2 (fun _ => EndT)      (so [Spawn_typed] applies)
      typed ∅ e0 UnitT
      steps [e0] ∅ [e0] ∅               ([Empty_step])

    but [e0] cannot step.  The only candidate decomposition is
    [Ctx_Close] over [Ctx_Spawn], which would require the definitional
    equality

      (fun q : fin 1 => if decide (p = q) then Lam1 else f1 q) = f1.

    This equality holds only extensionally: [decide (p = q)] is stuck on
    the fresh conversion variable [q] (fin_dec matches on [q]), so Coq
    rejects the required conversion ("Not convertible").  Consequently
    [{Thread 0}] is a deadlock for [([e0], ∅)].  With
    [FunctionalExtensionality] the equality and the step become
    derivable, but that is an axiom not present in the supplied imports,
    and the task rules forbid adding it. *)

(** * Main theorem *)

Theorem deadlock_freedom_and_full_reachability e es h :
  typed ∅ e UnitT -> steps [e] ∅ es h ->
  deadlock_free es h ∧ fully_reachable es h.
