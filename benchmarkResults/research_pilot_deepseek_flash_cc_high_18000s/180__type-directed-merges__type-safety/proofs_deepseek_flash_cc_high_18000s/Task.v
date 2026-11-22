Require Import Metalib.Metatheory.
Require Import syntax_ott.
From Stdlib Require Import Lia.
From Stdlib Require Import Program.Equality.

(* ============================================================ *)
(* Locally-closedness machinery                                  *)
(* ============================================================ *)

(* Depth-annotated locally closed relation.  [lc_at d e] means that [e]
   has no free bound variables when placed under [d] binders. *)
Inductive lc_at : nat -> exp -> Prop :=
  | lc_at_var_f : forall d x, lc_at d (e_var_f x)
  | lc_at_var_b : forall d n, n < d -> lc_at d (e_var_b n)
  | lc_at_top : forall d, lc_at d e_top
  | lc_at_lit : forall d i5, lc_at d (e_lit i5)
  | lc_at_abs : forall d A e B, lc_at (S d) e -> lc_at d (e_abs A e B)
  | lc_at_fix : forall d e A, lc_at (S d) e -> lc_at d (e_fixpoint e A)
  | lc_at_app : forall d e1 e2, lc_at d e1 -> lc_at d e2 -> lc_at d (e_app e1 e2)
  | lc_at_merge : forall d e1 e2, lc_at d e1 -> lc_at d e2 -> lc_at d (e_merge e1 e2)
  | lc_at_anno : forall d e A, lc_at d e -> lc_at d (e_anno e A).

Lemma lc_at_weaken : forall d e, lc_at d e -> forall d', d <= d' -> lc_at d' e.
Proof.
  intros d e H. induction H; intros d' Hle.
  - constructor.
  - apply lc_at_var_b. lia.
  - constructor.
  - constructor.
  - constructor. apply IHlc_at. lia.
  - constructor. apply IHlc_at. lia.
  - constructor; auto.
  - constructor; auto.
  - constructor. auto.
Qed.

Lemma lc_at_var_b_inv : forall d n, lc_at d (e_var_b n) -> n < d.
Proof. intros d n H. inversion H. assumption. Qed.

Lemma lc_at_abs_inv : forall d A e B, lc_at d (e_abs A e B) -> lc_at (S d) e.
Proof. intros d A e B H. inversion H. assumption. Qed.

Lemma lc_at_fix_inv : forall d e A, lc_at d (e_fixpoint e A) -> lc_at (S d) e.
Proof. intros d e A H. inversion H. assumption. Qed.

Lemma lc_at_app_inv : forall d e1 e2, lc_at d (e_app e1 e2) -> lc_at d e1 /\ lc_at d e2.
Proof. intros d e1 e2 H. inversion H. auto. Qed.

Lemma lc_at_merge_inv : forall d e1 e2, lc_at d (e_merge e1 e2) -> lc_at d e1 /\ lc_at d e2.
Proof. intros d e1 e2 H. inversion H. auto. Qed.

Lemma lc_at_anno_inv : forall d e A, lc_at d (e_anno e A) -> lc_at d e.
Proof. intros d e A H. inversion H. assumption. Qed.

Lemma open_rec_var_lt : forall d u n,
    n < d -> open_exp_wrt_exp_rec d u (e_var_b n) = e_var_b n.
Proof.
  intros. simpl. destruct (lt_eq_lt_dec n d) as [[H1|H2]|H3]; try reflexivity; lia.
Qed.

Lemma open_rec_var_eq : forall d u,
    open_exp_wrt_exp_rec d u (e_var_b d) = u.
Proof.
  intros. simpl. destruct (lt_eq_lt_dec d d) as [[H1|H2]|H3]; try reflexivity; lia.
Qed.

Lemma open_rec_var_gt : forall d u n,
    d < n -> open_exp_wrt_exp_rec d u (e_var_b n) = e_var_b (n - 1).
Proof.
  intros. simpl. destruct (lt_eq_lt_dec n d) as [[H1|H2]|H3]; try reflexivity; lia.
Qed.

(* Opening a variable at level [d] preserves [lc_at] at depth [d]. *)
Lemma lc_at_open : forall e d u,
    lc_at (S d) e -> lc_at 0 u -> lc_at d (open_exp_wrt_exp_rec d u e).
Proof.
  induction e; intros d u Hl Hu.
  - (* var_b *)
    inversion Hl as [| d' n' Hlt0 | | | | | | | ]; subst.
    destruct (lt_eq_lt_dec n d) as [[Hlt|Heq]|Hgt].
    + rewrite open_rec_var_lt by lia. apply lc_at_var_b. assumption.
    + subst n. rewrite open_rec_var_eq. exact (lc_at_weaken 0 u Hu d (Nat.le_0_l d)).
    + rewrite open_rec_var_gt by lia. apply lc_at_var_b. lia.
  - (* var_f *) simpl. constructor.
  - (* top *) simpl. constructor.
  - (* lit *) simpl. constructor.
  - (* abs *)
    simpl. inversion Hl as [| | | | d' A' e' B' Hbody | | | | ]; subst.
    apply lc_at_abs. eapply IHe. apply Hbody. apply Hu.
  - (* fixpoint *)
    simpl. inversion Hl as [| | | | | d' e' A' Hbody | | | ]; subst.
    apply lc_at_fix. eapply IHe. apply Hbody. apply Hu.
  - (* app *)
    simpl. inversion Hl as [| | | | | | d' e1' e2' H1 H2 | | ]; subst.
    apply lc_at_app.
    + eapply IHe1; eauto.
    + eapply IHe2; eauto.
  - (* merge *)
    simpl. inversion Hl as [| | | | | | | d' e1' e2' H1 H2 | ]; subst.
    apply lc_at_merge.
    + eapply IHe1; eauto.
    + eapply IHe2; eauto.
  - (* anno *)
    simpl. inversion Hl as [| | | | | | | | d' e' A' H1]; subst.
    apply lc_at_anno. eapply IHe; eauto.
Qed.

(* Converse: if the opened term is locally closed at depth [d], then the
   original is locally closed at depth [S d]. *)
Lemma lc_at_open_inv : forall e d u,
    lc_at d (open_exp_wrt_exp_rec d u e) -> lc_at (S d) e.
Proof.
  induction e; intros d u Hl.
  - (* var_b *)
    destruct (lt_eq_lt_dec n d) as [[Hlt|Heq]|Hgt].
    + rewrite open_rec_var_lt in Hl by lia. apply lc_at_var_b. apply lc_at_var_b_inv in Hl. lia.
    + subst n. rewrite open_rec_var_eq in Hl. apply lc_at_var_b. lia.
    + rewrite open_rec_var_gt in Hl by lia. apply lc_at_var_b. apply lc_at_var_b_inv in Hl. lia.
  - (* var_f *) simpl. constructor.
  - (* top *) simpl. constructor.
  - (* lit *) simpl. constructor.
  - (* abs *)
    simpl. apply lc_at_abs. eapply IHe. eapply lc_at_abs_inv. apply Hl.
  - (* fixpoint *)
    simpl. apply lc_at_fix. eapply IHe. eapply lc_at_fix_inv. apply Hl.
  - (* app *)
    simpl. apply lc_at_app_inv in Hl. destruct Hl.
    apply lc_at_app; [eapply IHe1 | eapply IHe2]; eauto.
  - (* merge *)
    simpl. apply lc_at_merge_inv in Hl. destruct Hl.
    apply lc_at_merge; [eapply IHe1 | eapply IHe2]; eauto.
  - (* anno *)
    simpl. apply lc_at_anno_inv in Hl. apply lc_at_anno.
    eapply IHe. apply Hl.
Qed.

(* Opening at a level at or above all free variables does nothing. *)
Lemma lc_at_open_id : forall e d,
    lc_at d e -> forall k u, open_exp_wrt_exp_rec (d + k) u e = e.
Proof.
  induction e; intros d Hl k u; simpl; auto.
  - apply lc_at_var_b_inv in Hl.
    destruct (lt_eq_lt_dec n (d + k)) as [[Hlt|Heq]|Hgt].
    + reflexivity.
    + lia.
    + lia.
  - apply lc_at_abs_inv in Hl. f_equal.
    replace (S (d + k)) with (S d + k) by lia. exact (IHe (S d) Hl k u).
  - apply lc_at_fix_inv in Hl. f_equal.
    replace (S (d + k)) with (S d + k) by lia. exact (IHe (S d) Hl k u).
  - apply lc_at_app_inv in Hl. destruct Hl. f_equal; eauto.
  - apply lc_at_merge_inv in Hl. destruct Hl. f_equal; eauto.
  - apply lc_at_anno_inv in Hl. f_equal. eauto.
Qed.

(* ============================================================ *)
(* Sequential opening with free atoms                            *)
(* ============================================================ *)

Fixpoint open_seq_from (k : nat) (xs : list atom) (e : exp) : exp :=
  match xs with
  | nil => e
  | x :: xs' => open_exp_wrt_exp_rec k (e_var_f x) (open_seq_from (S k) xs' e)
  end.

Definition open_seq (xs : list atom) (e : exp) : exp := open_seq_from 0 xs e.

Lemma open_seq_from_abs : forall xs k A e B,
    open_seq_from k xs (e_abs A e B) =
    e_abs A (open_seq_from (S k) xs e) B.
Proof.
  induction xs as [| a xs']; intros k A e B; simpl.
  - reflexivity.
  - rewrite IHxs'. reflexivity.
Qed.

Lemma open_seq_from_fix : forall xs k e A,
    open_seq_from k xs (e_fixpoint e A) =
    e_fixpoint (open_seq_from (S k) xs e) A.
Proof.
  induction xs as [| a xs']; intros k e A; simpl.
  - reflexivity.
  - rewrite IHxs'. reflexivity.
Qed.

Lemma open_seq_from_app : forall xs k e1 e2,
    open_seq_from k xs (e_app e1 e2) =
    e_app (open_seq_from k xs e1) (open_seq_from k xs e2).
Proof.
  induction xs as [| a xs']; intros k e1 e2; simpl.
  - reflexivity.
  - rewrite IHxs'. reflexivity.
Qed.

Lemma open_seq_from_merge : forall xs k e1 e2,
    open_seq_from k xs (e_merge e1 e2) =
    e_merge (open_seq_from k xs e1) (open_seq_from k xs e2).
Proof.
  induction xs as [| a xs']; intros k e1 e2; simpl.
  - reflexivity.
  - rewrite IHxs'. reflexivity.
Qed.

Lemma open_seq_from_anno : forall xs k e A,
    open_seq_from k xs (e_anno e A) =
    e_anno (open_seq_from k xs e) A.
Proof.
  induction xs as [| a xs']; intros k e A; simpl.
  - reflexivity.
  - rewrite IHxs'. reflexivity.
Qed.

Lemma open_seq_from_var_lt : forall xs k n,
    n < k -> open_seq_from k xs (e_var_b n) = e_var_b n.
Proof.
  induction xs as [| a xs']; intros k n H; simpl.
  - reflexivity.
  - rewrite (IHxs' (S k) n) by lia.
    rewrite open_rec_var_lt by lia. reflexivity.
Qed.

Lemma open_seq_from_var_mid : forall xs k n,
    k <= n < k + length xs ->
    exists y, open_seq_from k xs (e_var_b n) = e_var_f y.
Proof.
  induction xs as [| a xs']; intros k n H; simpl.
  - simpl in H. lia.
  - simpl in H. destruct (lt_eq_lt_dec n (S k)) as [[Hlt|Heq]|Hgt].
    + (* n < S k, and k <= n, so n = k *)
      assert (n = k) by lia. subst n.
      rewrite open_seq_from_var_lt by lia.
      rewrite open_rec_var_eq. eexists; reflexivity.
    + (* n = S k *)
      subst n.
      assert (Hxs : exists a' xs'', xs' = a' :: xs'').
      { destruct xs' as [| a' xs'']; [exfalso; simpl in H; lia | exists a', xs''; reflexivity]. }
      destruct Hxs as [a' [xs'' Hxs]]; subst xs'.
      simpl. rewrite (open_seq_from_var_lt xs'' (S (S k)) (S k)) by lia.
      rewrite open_rec_var_eq. simpl. eexists; reflexivity.
    + (* n > S k : use IH *)
      assert (Hin : S k <= n < S k + length xs') by lia.
      destruct (IHxs' (S k) n Hin) as [y Hy].
      rewrite Hy. simpl. eexists; reflexivity.
Qed.

Lemma open_seq_from_var_ge : forall xs k n,
    k + length xs <= n ->
    open_seq_from k xs (e_var_b n) = e_var_b (n - length xs).
Proof.
  induction xs as [| a xs']; intros k n H; simpl in H; simpl.
  - rewrite Nat.sub_0_r. reflexivity.
  - assert (Hin : S k + length xs' <= n) by lia.
    rewrite (IHxs' (S k) n Hin).
    assert (Hkn : k < n - length xs') by lia.
    rewrite open_rec_var_gt by exact Hkn.
    replace (n - length xs' - 1) with (n - S (length xs')) by lia. reflexivity.
Qed.


Lemma open_seq_from_var_f : forall xs k x,
    open_seq_from k xs (e_var_f x) = e_var_f x.
Proof.
  induction xs as [| a xs']; intros k x; simpl.
  - reflexivity.
  - rewrite IHxs'. reflexivity.
Qed.

Lemma open_seq_from_top : forall xs k,
    open_seq_from k xs e_top = e_top.
Proof.
  induction xs as [| a xs']; intros k; simpl.
  - reflexivity.
  - rewrite IHxs'. reflexivity.
Qed.

Lemma open_seq_from_lit : forall xs k i5,
    open_seq_from k xs (e_lit i5) = e_lit i5.
Proof.
  induction xs as [| a xs']; intros k i5; simpl.
  - reflexivity.
  - rewrite IHxs'. reflexivity.
Qed.

Lemma lc_var_b_false : forall n, lc_exp (e_var_b n) -> False.
Proof. intros n H. inversion H. Qed.

Lemma lc_abs_iff : forall A e B,
    lc_exp (e_abs A e B) <-> (forall x, lc_exp (open_exp_wrt_exp e (e_var_f x))).
Proof. intros. split; intros H; [inversion H | constructor]; auto. Qed.

Lemma lc_fix_iff : forall e A,
    lc_exp (e_fixpoint e A) <-> (forall x, lc_exp (open_exp_wrt_exp e (e_var_f x))).
Proof. intros. split; intros H; [inversion H | constructor]; auto. Qed.

Lemma lc_app_iff : forall e1 e2,
    lc_exp (e_app e1 e2) <-> lc_exp e1 /\ lc_exp e2.
Proof. intros. split; intros H; [inversion H | destruct H; constructor]; auto. Qed.

Lemma lc_merge_iff : forall e1 e2,
    lc_exp (e_merge e1 e2) <-> lc_exp e1 /\ lc_exp e2.
Proof. intros. split; intros H; [inversion H | destruct H; constructor]; auto. Qed.

Lemma lc_anno_iff : forall e A, lc_exp (e_anno e A) <-> lc_exp e.
Proof. intros. split; intros H; [inversion H | constructor]; auto. Qed.

Lemma lc_open_seq_var_b : forall xs n,
    lc_exp (open_seq xs (e_var_b n)) -> n < length xs.
Proof.
  intros xs n H.
  destruct (lt_dec n (length xs)) as [Hlt|Hge]; auto.
  exfalso. apply Nat.nlt_ge in Hge.
  assert (Heq : open_seq xs (e_var_b n) = e_var_b (n - length xs)).
  { unfold open_seq. apply open_seq_from_var_ge. lia. }
  rewrite Heq in H. apply lc_var_b_false in H. auto.
Qed.

Lemma lc_at_seq : forall e d,
    lc_at d e <->
    (forall xs, length xs = d -> lc_exp (open_seq xs e)).
Proof.
  induction e; intros d; split; intros H.
  - (* var_b -> *)
    apply lc_at_var_b_inv in H. intros xs Hl.
    assert (Hin : 0 <= n < 0 + length xs) by lia.
    destruct (open_seq_from_var_mid xs 0 n Hin) as [y Hy].
    unfold open_seq. rewrite Hy. constructor.
  - (* var_b <- *)
    apply lc_at_var_b.
    destruct d as [| d'].
    + specialize (H nil eq_refl). simpl in H. exfalso. apply lc_var_b_false in H. auto.
    + assert (Hlen : length (repeat (fresh nil) (S d')) = S d') by apply repeat_length.
      specialize (H (repeat (fresh nil) (S d')) Hlen).
      apply lc_open_seq_var_b in H. rewrite repeat_length in H. exact H.
  - (* var_f -> *) intros xs Hl. unfold open_seq. rewrite open_seq_from_var_f. constructor.
  - (* var_f <- *) constructor.
  - (* top -> *) intros xs Hl. unfold open_seq. rewrite open_seq_from_top. constructor.
  - (* top <- *) constructor.
  - (* lit -> *) intros xs Hl. unfold open_seq. rewrite open_seq_from_lit. constructor.
  - (* lit <- *) constructor.
  - (* abs -> *)
    apply lc_at_abs_inv in H.
    intros xs Hl. unfold open_seq. rewrite open_seq_from_abs. constructor.
    pose proof (proj1 (IHe (S d)) H) as Hbody.
    intros z. change (lc_exp (open_seq (z :: xs) e)). apply Hbody. simpl. lia.
  - (* abs <- *)
    apply lc_at_abs. apply (proj2 (IHe (S d))). intros ys Hylen.
    destruct ys as [| z xs].
    + simpl in Hylen. lia.
    + simpl in Hylen. assert (Hlen : length xs = d) by lia.
      specialize (H xs Hlen). unfold open_seq in H. rewrite open_seq_from_abs in H.
      pose proof (proj1 (lc_abs_iff A (open_seq_from 1 xs e) B) H) as Hz.
      specialize (Hz z). simpl in Hz.
      change (lc_exp (open_exp_wrt_exp (open_seq_from 1 xs e) (e_var_f z))). apply Hz.
  - (* fixpoint -> *)
    apply lc_at_fix_inv in H.
    intros xs Hl. unfold open_seq. rewrite open_seq_from_fix. constructor.
    pose proof (proj1 (IHe (S d)) H) as Hbody.
    intros z. change (lc_exp (open_seq (z :: xs) e)). apply Hbody. simpl. lia.
  - (* fixpoint <- *)
    apply lc_at_fix. apply (proj2 (IHe (S d))). intros ys Hylen.
    destruct ys as [| z xs].
    + simpl in Hylen. lia.
    + simpl in Hylen. assert (Hlen : length xs = d) by lia.
      specialize (H xs Hlen). unfold open_seq in H. rewrite open_seq_from_fix in H.
      pose proof (proj1 (lc_fix_iff (open_seq_from 1 xs e) A) H) as Hz.
      specialize (Hz z). simpl in Hz.
      change (lc_exp (open_exp_wrt_exp (open_seq_from 1 xs e) (e_var_f z))). apply Hz.
  - (* app -> *)
    apply lc_at_app_inv in H as [H1 H2].
    intros xs Hl. unfold open_seq. rewrite open_seq_from_app. apply lc_app_iff. split.
    + apply (proj1 (IHe1 d)); auto.
    + apply (proj1 (IHe2 d)); auto.
  - (* app <- *)
    apply lc_at_app.
    + apply (proj2 (IHe1 d)). intros xs Hl.
      specialize (H xs Hl). unfold open_seq in H. rewrite open_seq_from_app in H.
      apply lc_app_iff in H. apply (proj1 H).
    + apply (proj2 (IHe2 d)). intros xs Hl.
      specialize (H xs Hl). unfold open_seq in H. rewrite open_seq_from_app in H.
      apply lc_app_iff in H. apply (proj2 H).
  - (* merge -> *)
    apply lc_at_merge_inv in H as [H1 H2].
    intros xs Hl. unfold open_seq. rewrite open_seq_from_merge. apply lc_merge_iff. split.
    + apply (proj1 (IHe1 d)); auto.
    + apply (proj1 (IHe2 d)); auto.
  - (* merge <- *)
    apply lc_at_merge.
    + apply (proj2 (IHe1 d)). intros xs Hl.
      specialize (H xs Hl). unfold open_seq in H. rewrite open_seq_from_merge in H.
      apply lc_merge_iff in H. apply (proj1 H).
    + apply (proj2 (IHe2 d)). intros xs Hl.
      specialize (H xs Hl). unfold open_seq in H. rewrite open_seq_from_merge in H.
      apply lc_merge_iff in H. apply (proj2 H).
  - (* anno -> *)
    apply lc_at_anno_inv in H.
    intros xs Hl. unfold open_seq. rewrite open_seq_from_anno. apply lc_anno_iff.
    apply (proj1 (IHe d)); auto.
  - (* anno <- *)
    apply lc_at_anno. apply (proj2 (IHe d)). intros xs Hl.
    specialize (H xs Hl). unfold open_seq in H. rewrite open_seq_from_anno in H.
    apply lc_anno_iff in H. apply H.
Qed.

Corollary lc_exp_lc_at : forall e, lc_exp e <-> lc_at 0 e.
Proof.
  intros e. split.
  - intros H. apply (proj2 (lc_at_seq e 0)). intros xs Hl. destruct xs; simpl in *. exact H. discriminate.
  - intros H. apply (proj1 (lc_at_seq e 0) H nil eq_refl).
Qed.

Corollary lc_exp_open_id : forall v, lc_exp v -> forall k u, open_exp_wrt_exp_rec k u v = v.
Proof.
  intros v H k u.
  apply lc_exp_lc_at in H.
  exact (lc_at_open_id v 0 H k u).
Qed.

(* ============================================================ *)
(* Free variables and substitution                               *)
(* ============================================================ *)

Lemma fv_open_rec : forall e k u x,
    x \in fv_exp e -> x \in fv_exp (open_exp_wrt_exp_rec k u e).
Proof.
  intros e. induction e; intros k u xx Hx; simpl in *.
  - (* var_b *) apply AtomSetImpl.empty_1 in Hx. inversion Hx.
  - (* var_f *) simpl. apply AtomSetImpl.singleton_1 in Hx. subst. apply AtomSetImpl.singleton_2. auto.
  - (* top *) apply AtomSetImpl.empty_1 in Hx. inversion Hx.
  - (* lit *) apply AtomSetImpl.empty_1 in Hx. inversion Hx.
  - (* abs *) simpl. apply IHe. auto.
  - (* fix *) simpl. apply IHe. auto.
  - (* app *) simpl in Hx. apply AtomSetImpl.union_1 in Hx. destruct Hx as [Hx|Hx].
    + simpl. apply AtomSetImpl.union_2. apply IHe1. auto.
    + simpl. apply AtomSetImpl.union_3. apply IHe2. auto.
  - (* merge *) simpl in Hx. apply AtomSetImpl.union_1 in Hx. destruct Hx as [Hx|Hx].
    + simpl. apply AtomSetImpl.union_2. apply IHe1. auto.
    + simpl. apply AtomSetImpl.union_3. apply IHe2. auto.
  - (* anno *) simpl. apply IHe. auto.
Qed.

Lemma fv_open_seq_from : forall xs k e x,
    x \in fv_exp e -> x \in fv_exp (open_seq_from k xs e).
Proof.
  induction xs as [| a xs']; intros k e x Hx; simpl.
  - exact Hx.
  - apply fv_open_rec. apply IHxs'. exact Hx.
Qed.

Lemma fv_open_seq : forall xs e x,
    x \in fv_exp e -> x \in fv_exp (open_seq xs e).
Proof. intros. unfold open_seq. apply fv_open_seq_from. auto. Qed.

Lemma subst_exp_notin : forall v x e,
    x \notin fv_exp e -> subst_exp v x e = e.
Proof.
  intros v x e. induction e; intros Hx; simpl.
  - reflexivity.
  - (* var_f *)
    destruct (eq_var x0 x) as [Heq|Hne].
    + subst x0. exfalso. apply Hx. apply AtomSetImpl.singleton_2. auto.
    + reflexivity.
  - reflexivity.
  - reflexivity.
  - (* abs *) rewrite IHe; auto.
  - (* fix *) rewrite IHe; auto.
  - (* app *)
    rewrite IHe1 by (intros Hc; apply Hx; apply AtomSetImpl.union_2; exact Hc).
    rewrite IHe2 by (intros Hc; apply Hx; apply AtomSetImpl.union_3; exact Hc).
    reflexivity.
  - (* merge *)
    rewrite IHe1 by (intros Hc; apply Hx; apply AtomSetImpl.union_2; exact Hc).
    rewrite IHe2 by (intros Hc; apply Hx; apply AtomSetImpl.union_3; exact Hc).
    reflexivity.
  - (* anno *) rewrite IHe; auto.
Qed.

(* Substitution commutes with opening, provided the substituted term is
   locally closed and the opening atom is different from the replaced one. *)
Lemma subst_open_comm : forall e v z y k,
    y <> z -> lc_exp v ->
    subst_exp v z (open_exp_wrt_exp_rec k (e_var_f y) e) =
    open_exp_wrt_exp_rec k (e_var_f y) (subst_exp v z e).
Proof.
  induction e; intros v z y k Hne Hlc; simpl.
  - (* var_b *)
    destruct (lt_eq_lt_dec n k) as [[Hlt|Heq]|Hgt].
    + reflexivity.
    + subst n. simpl. destruct (eq_var y z) as [Heq'|Hne'].
      * exfalso. apply Hne. auto.
      * reflexivity.
    + reflexivity.
  - (* var_f *)
    destruct (eq_var x z) as [Heq|Hne'].
    + subst x. rewrite lc_exp_open_id by auto. reflexivity.
    + reflexivity.
  - reflexivity.
  - reflexivity.
  - (* abs *) rewrite IHe; auto.
  - (* fix *) rewrite IHe; auto.
  - (* app *) rewrite IHe1; auto. rewrite IHe2; auto.
  - (* merge *) rewrite IHe1; auto. rewrite IHe2; auto.
  - (* anno *) rewrite IHe; auto.
Qed.

Lemma subst_open_self : forall e v z k,
    z \notin fv_exp e ->
    subst_exp v z (open_exp_wrt_exp_rec k (e_var_f z) e) =
    open_exp_wrt_exp_rec k v e.
Proof.
  induction e; intros v z k Hx; simpl.
  - (* var_b *)
    destruct (lt_eq_lt_dec n k) as [[Hlt|Heq]|Hgt].
    + reflexivity.
    + subst n. simpl. destruct (eq_var z z) as [|Hne]; [reflexivity | exfalso; apply Hne; reflexivity].
    + reflexivity.
  - (* var_f *)
    destruct (eq_var x z) as [Heq|Hne].
    + subst x. exfalso. apply Hx. apply AtomSetImpl.singleton_2. auto.
    + reflexivity.
  - reflexivity.
  - reflexivity.
  - (* abs *) rewrite IHe; auto.
  - (* fix *) rewrite IHe; auto.
  - (* app *)
    rewrite IHe1 by (intros Hc; apply Hx; apply AtomSetImpl.union_2; exact Hc).
    rewrite IHe2 by (intros Hc; apply Hx; apply AtomSetImpl.union_3; exact Hc).
    reflexivity.
  - (* merge *)
    rewrite IHe1 by (intros Hc; apply Hx; apply AtomSetImpl.union_2; exact Hc).
    rewrite IHe2 by (intros Hc; apply Hx; apply AtomSetImpl.union_3; exact Hc).
    reflexivity.
  - (* anno *) rewrite IHe; auto.
Qed.

(* ============================================================ *)
(* Context lemmas                                                *)
(* ============================================================ *)

Lemma in_empty_elim : forall x, x \in ({} : atoms) -> False.
Proof. intros x H. exact (notin_empty_1 x H). Qed.

Lemma binds_dom : forall (G:ctx) x A, binds x A G -> x \in dom G.
Proof.
  induction G as [| [y B] G IH]; intros x A Hb.
  - inversion Hb.
  - apply binds_cons_iff in Hb. destruct Hb as [[Heq HB]|Hb].
    + subst x. subst B. rewrite dom_cons.
      apply AtomSetImpl.union_2. apply AtomSetImpl.singleton_2. auto.
    + rewrite dom_cons. apply AtomSetImpl.union_3. exact (IH x A Hb).
Qed.

Lemma binds_unique : forall (G:ctx) x A B,
    uniq G -> binds x A G -> binds x B G -> A = B.
Proof.
  induction G as [| [y C] G IH]; intros x A B Hu H1 H2.
  - inversion H1.
  - apply uniq_cons_iff in Hu. destruct Hu as [HuG Hnd].
    apply binds_cons_iff in H1. apply binds_cons_iff in H2.
    destruct H1 as [[Heq1 HA]|H1]; destruct H2 as [[Heq2 HB]|H2].
    + subst. auto.
    + subst. exfalso. apply Hnd. apply binds_dom in H2. exact H2.
    + subst. exfalso. apply Hnd. apply binds_dom in H1. exact H1.
    + exact (IH x A B HuG H1 H2).
Qed.

Lemma binds_cons_perm : forall (G:ctx) x A y B,
    x <> y -> forall z C,
    binds z C (cons (x,A) (cons (y,B) G)) <-> binds z C (cons (y,B) (cons (x,A) G)).
Proof.
  intros G x A y B Hne z C. split.
  - intros Hb. apply binds_cons_iff in Hb. destruct Hb as [[HzC HW]|Hb].
    + subst z. subst C. apply binds_cons_iff. right. apply binds_cons_iff. left; auto.
    + apply binds_cons_iff in Hb. destruct Hb as [[HzC HW]|Hb].
      * subst z. subst C. apply binds_cons_iff. left; auto.
      * apply binds_cons_iff. right. apply binds_cons_iff. right; auto.
  - intros Hb. apply binds_cons_iff in Hb. destruct Hb as [[HzC HW]|Hb].
    + subst z. subst C. apply binds_cons_iff. right. apply binds_cons_iff. left; auto.
    + apply binds_cons_iff in Hb. destruct Hb as [[HzC HW]|Hb].
      * subst z. subst C. apply binds_cons_iff. left; auto.
      * apply binds_cons_iff. right. apply binds_cons_iff. right; auto.
Qed.

(* Two uniq contexts with the same set of bindings type the same terms. *)
Lemma typing_binds_congr : forall G G' e A,
    uniq G -> uniq G' ->
    (forall x B, binds x B G <-> binds x B G') ->
    Etyping G e A -> Etyping G' e A.
Proof.
  intros G G' e A HuG HuG' Hb E.
  revert G' HuG' Hb.
  induction E as
    [ G0 u0
    | G0 i0 u0
    | G0 x0 A0 u0 b0
    | L G0 A0 e0 D0 C0 B0 Hpre IHpre sCA sBD
    | G0 e1 e2 B0 A0 H2 IH2 H1 IH1
    | G0 e1 e2 A0 B0 H1 IH1 H2 IH2 dsp
    | G0 e0 A0 B0 H1 IH1 sBA
    | L G0 e0 A0 Hpre IHpre
    | G0 v1 v2 A0 B0 u0 v0 H1 IH1 H2 IH2 c0 ];
  intros G' HuG' Hb.
  - (* top *) constructor. auto.
  - (* lit *) constructor. auto.
  - (* var *) apply Etyp_var; auto. apply (proj1 (Hb x0 A0)). auto.
  - (* abs *)
    eapply Etyp_abs with (L := L \u dom G0 \u dom G').
    + intros x Hx.
      apply notin_union_1 in Hx as HxL. apply notin_union_2 in Hx as HxG'.
      apply notin_union_1 in HxG' as HxG.
      specialize (IHpre x HxL).
      assert (HuGx : uniq (cons (x, A0) G0)) by (apply uniq_cons; auto).
      assert (Huniqx : uniq (cons (x, A0) G')) by (apply uniq_cons; auto).
      assert (Hbx : forall z C, binds z C (cons (x, A0) G0) <-> binds z C (cons (x, A0) G')).
      { intros z C. split.
        - intros Hbc. apply binds_cons_iff in Hbc. destruct Hbc as [[HzC HW]|Hbc].
          + apply binds_cons_iff. left; auto.
          + apply binds_cons_iff. right. apply (proj1 (Hb z C)); auto.
        - intros Hbc. apply binds_cons_iff in Hbc. destruct Hbc as [[HzC HW]|Hbc].
          + apply binds_cons_iff. left; auto.
          + apply binds_cons_iff. right. apply (proj2 (Hb z C)); auto. }
      exact (IHpre HuGx (cons (x, A0) G') Huniqx Hbx).
    + auto.
    + auto.
  - (* app *) apply Etyp_app with (A := A0); auto.
  - (* merge *) apply Etyp_merge with (A := A0) (B := B0); auto.
  - (* anno *) apply Etyp_anno with (B := B0); auto.
  - (* fix *)
    eapply Etyp_fix with (L := L \u dom G0 \u dom G').
    + intros x Hx.
      apply notin_union_1 in Hx as HxL. apply notin_union_2 in Hx as HxG'.
      apply notin_union_1 in HxG' as HxG.
      specialize (IHpre x HxL).
      assert (HuGx : uniq (cons (x, A0) G0)) by (apply uniq_cons; auto).
      assert (Huniqx : uniq (cons (x, A0) G')) by (apply uniq_cons; auto).
      assert (Hbx : forall z C, binds z C (cons (x, A0) G0) <-> binds z C (cons (x, A0) G')).
      { intros z C. split.
        - intros Hbc. apply binds_cons_iff in Hbc. destruct Hbc as [[HzC HW]|Hbc].
          + apply binds_cons_iff. left; auto.
          + apply binds_cons_iff. right. apply (proj1 (Hb z C)); auto.
        - intros Hbc. apply binds_cons_iff in Hbc. destruct Hbc as [[HzC HW]|Hbc].
          + apply binds_cons_iff. left; auto.
          + apply binds_cons_iff. right. apply (proj2 (Hb z C)); auto. }
      exact (IHpre HuGx (cons (x, A0) G') Huniqx Hbx).
  - (* mergev *) eapply Etyp_mergev; eauto.
Qed.

Lemma typing_weaken_cons : forall G e A,
    Etyping G e A -> forall y B0, uniq G -> y \notin dom G ->
    Etyping (cons (y, B0) G) e A.
Proof.
  intros G e A E.
  induction E as
    [ G0 u0
    | G0 i0 u0
    | G0 x0 A0 u0 b0
    | L G0 A0 e0 D0 C0 B0 Hpre IHpre sCA sBD
    | G0 e1 e2 B0 A0 H2 IH2 H1 IH1
    | G0 e1 e2 A0 B0 H1 IH1 H2 IH2 dsp
    | G0 e0 A0 B0 H1 IH1 sBA
    | L G0 e0 A0 Hpre IHpre
    | G0 v1 v2 A0 B0 u0 v0 H1 IH1 H2 IH2 c0 ];
  intros y0 B00 HuG Hy.
  - (* top *) constructor. apply uniq_cons; auto.
  - (* lit *) constructor. apply uniq_cons; auto.
  - (* var *)
    apply Etyp_var. apply uniq_cons; auto.
    apply binds_cons_iff. right. auto.
  - (* abs *)
    eapply Etyp_abs with (L := L \u {{y0}} \u dom G0).
    + intros x Hx.
      apply notin_union_1 in Hx as HxL. apply notin_union_2 in Hx as HxR.
      apply notin_union_1 in HxR as Hxy. apply notin_union_2 in HxR as HxG.
      apply notin_singleton_1 in Hxy. (* y0 <> x *)
      specialize (IHpre x HxL).
      assert (Huniq_x : uniq (cons (x, A0) G0)) by (apply uniq_cons; auto).
      assert (Hy' : y0 \notin dom (cons (x, A0) G0)).
      { rewrite dom_cons. apply notin_union_3.
        - apply notin_singleton_2. intros Heq. apply Hxy. auto.
        - exact Hy. }
      specialize (IHpre y0 B00 Huniq_x Hy').
      eapply typing_binds_congr.
      * apply uniq_cons. exact Huniq_x. exact Hy'.
      * apply uniq_cons.
        -- apply uniq_cons; auto.
        -- rewrite dom_cons. apply notin_union_3.
           ++ apply notin_singleton_2. intros Heq. apply Hxy. auto.
           ++ exact HxG.
      * apply binds_cons_perm. intros Heq. apply Hxy. auto.
      * apply IHpre.
    + auto.
    + auto.
  - (* app *) apply Etyp_app with (A := A0); auto.
  - (* merge *) apply Etyp_merge with (A := A0) (B := B0); auto.
  - (* anno *) apply Etyp_anno with (B := B0); auto.
  - (* fix *)
    eapply Etyp_fix with (L := L \u {{y0}} \u dom G0).
    + intros x Hx.
      apply notin_union_1 in Hx as HxL. apply notin_union_2 in Hx as HxR.
      apply notin_union_1 in HxR as Hxy. apply notin_union_2 in HxR as HxG.
      apply notin_singleton_1 in Hxy. (* y0 <> x *)
      specialize (IHpre x HxL).
      assert (Huniq_x : uniq (cons (x, A0) G0)) by (apply uniq_cons; auto).
      assert (Hy' : y0 \notin dom (cons (x, A0) G0)).
      { rewrite dom_cons. apply notin_union_3.
        - apply notin_singleton_2. intros Heq. apply Hxy. auto.
        - exact Hy. }
      specialize (IHpre y0 B00 Huniq_x Hy').
      eapply typing_binds_congr.
      * apply uniq_cons. exact Huniq_x. exact Hy'.
      * apply uniq_cons.
        -- apply uniq_cons; auto.
        -- rewrite dom_cons. apply notin_union_3.
           ++ apply notin_singleton_2. intros Heq. apply Hxy. auto.
           ++ exact HxG.
      * apply binds_cons_perm. intros Heq. apply Hxy. auto.
      * apply IHpre.
  - (* mergev *) eapply Etyp_mergev; eauto.
Qed.

Lemma in_dom_cons : forall (G:ctx) x A z,
    z \in dom (cons (x,A) G) -> z = x \/ z \in dom G.
Proof.
  intros. rewrite dom_cons in H. apply AtomSetImpl.union_1 in H.
  destruct H as [H|H].
  - left. apply AtomSetImpl.singleton_1 in H. auto.
  - right. auto.
Qed.

Lemma in_dom_nil : forall z, z \in dom (nil : ctx) -> False.
Proof.
  intros z H. rewrite dom_nil in H. apply in_empty_elim in H. auto.
Qed.

Lemma Etyping_fv : forall G e A,
    Etyping G e A -> forall z, z \in fv_exp e -> z \in dom G.
Proof.
  intros G e A E.
  induction E as
    [ G0 u0
    | G0 i0 u0
    | G0 x0 A0 u0 b0
    | L G0 A0 e0 D0 C0 B0 Hpre IHpre sCA sBD
    | G0 e1 e2 B0 A0 H2 IH2 H1 IH1
    | G0 e1 e2 A0 B0 H1 IH1 H2 IH2 dsp
    | G0 e0 A0 B0 H1 IH1 sBA
    | L G0 e0 A0 Hpre IHpre
    | G0 v1 v2 A0 B0 u0 v0 H1 IH1 H2 IH2 c0 ];
    intros z0 Hz.
  - (* top *) simpl in Hz. exfalso. exact (in_empty_elim z0 Hz).
  - (* lit *) simpl in Hz. exfalso. exact (in_empty_elim z0 Hz).
  - (* var *) simpl in Hz. apply AtomSetImpl.singleton_1 in Hz. subst z0.
    apply binds_dom in b0. auto.
  - (* abs *)
    simpl in Hz.
    destruct (atom_fresh (L \u dom G0 \u {{z0}})) as [x Hx].
    apply notin_union_1 in Hx as HxL. apply notin_union_2 in Hx as HxR.
    apply notin_union_1 in HxR as Hxd. apply notin_union_2 in HxR as Hxz.
    apply notin_singleton_1 in Hxz. (* z0 <> x *)
    specialize (IHpre x HxL).
    assert (Hf : z0 \in fv_exp (open_exp_wrt_exp e0 (e_var_f x))).
    { unfold open_exp_wrt_exp. apply fv_open_rec. auto. }
    specialize (IHpre z0 Hf).
    apply in_dom_cons in IHpre. destruct IHpre as [Heq|Hin].
    + exfalso. apply Hxz. exact Heq.
    + auto.
  - (* app *)
    simpl in Hz. apply AtomSetImpl.union_1 in Hz. destruct Hz as [Hz|Hz].
    + apply IH1; auto.
    + apply IH2; auto.
  - (* merge *)
    simpl in Hz. apply AtomSetImpl.union_1 in Hz. destruct Hz as [Hz|Hz].
    + apply IH1; auto.
    + apply IH2; auto.
  - (* anno *) simpl in Hz. apply IH1; auto.
  - (* fix *)
    simpl in Hz.
    destruct (atom_fresh (L \u dom G0 \u {{z0}})) as [x Hx].
    apply notin_union_1 in Hx as HxL. apply notin_union_2 in Hx as HxR.
    apply notin_union_1 in HxR as Hxd. apply notin_union_2 in HxR as Hxz.
    apply notin_singleton_1 in Hxz.
    specialize (IHpre x HxL).
    assert (Hf : z0 \in fv_exp (open_exp_wrt_exp e0 (e_var_f x))).
    { unfold open_exp_wrt_exp. apply fv_open_rec. auto. }
    specialize (IHpre z0 Hf).
    apply in_dom_cons in IHpre. destruct IHpre as [Heq|Hin].
    + exfalso. apply Hxz. exact Heq.
    + auto.
  - (* mergev *)
    simpl in Hz. apply AtomSetImpl.union_1 in Hz. destruct Hz as [Hz|Hz].
    + exfalso. exact (in_dom_nil z0 (IH1 z0 Hz)).
    + exfalso. exact (in_dom_nil z0 (IH2 z0 Hz)).
Qed.

(* Substitution lemma for typing (variable kept in the context). *)
Lemma typing_subst_gen : forall G e B,
    Etyping G e B ->
    forall x A v, uniq G -> lc_exp v -> binds x A G -> Etyping G v A ->
    Etyping G (subst_exp v x e) B.
Proof.
  intros G e B E.
  induction E as
    [ G0 u0
    | G0 i0 u0
    | G0 y0 A0 u0 b0
    | L G0 A0 e0 D0 C0 B0 Hpre IHpre sCA sBD
    | G0 e1 e2 B0 A0 H2 IH2 H1 IH1
    | G0 e1 e2 A0 B0 H1 IH1 H2 IH2 dsp
    | G0 e0 A0 B0 H1 IH1 sBA
    | L G0 e0 A0 Hpre IHpre
    | G0 v1 v2 A0 B0 u0 hval H1 IH1 H2 IH2 c0 ];
    intros x0 A1 v0 HuG Hlc Hb Hv.
  - (* top *) constructor. auto.
  - (* lit *) constructor. auto.
  - (* var *)
    simpl. destruct (eq_var y0 x0) as [Heq|Hne].
    + subst y0. pose proof (binds_unique G0 x0 A1 A0 HuG Hb b0) as ->.
      auto.
    + apply Etyp_var; auto.
  - (* abs *)
    eapply Etyp_abs with (L := L \u {{x0}} \u dom G0) (A := A0) (e := subst_exp v0 x0 e0) (D := D0) (C := C0) (B := B0).
    + intros y Hy.
      apply notin_union_1 in Hy as HyL. apply notin_union_2 in Hy as HyR.
      apply notin_union_1 in HyR as HyX. apply notin_union_2 in HyR as HyG.
      apply notin_singleton_1 in HyX. (* x0 <> y *)
      specialize (IHpre y HyL).
      assert (Hyx : y <> x0) by (intros Heq; apply HyX; symmetry; exact Heq).
      unfold open_exp_wrt_exp.
      rewrite <- (subst_open_comm e0 v0 x0 y 0 Hyx Hlc).
      eapply IHpre.
      * apply uniq_cons; auto.
      * exact Hlc.
      * apply binds_cons_iff. right. exact Hb.
      * apply typing_weaken_cons; auto.
    + auto.
    + auto.
  - (* app *) simpl. eapply Etyp_app.
    + eapply IH2; eauto.
    + eapply IH1; eauto.
  - (* merge *) simpl. eapply Etyp_merge.
    + eapply IH1; eauto.
    + eapply IH2; eauto.
    + auto.
  - (* anno *) simpl. eapply Etyp_anno.
    + eapply IH1; eauto.
    + auto.
  - (* fix *)
    eapply Etyp_fix with (L := L \u {{x0}} \u dom G0) (e := subst_exp v0 x0 e0) (A := A0).
    + intros y Hy.
      apply notin_union_1 in Hy as HyL. apply notin_union_2 in Hy as HyR.
      apply notin_union_1 in HyR as HyX. apply notin_union_2 in HyR as HyG.
      apply notin_singleton_1 in HyX.
      specialize (IHpre y HyL).
      assert (Hyx : y <> x0) by (intros Heq; apply HyX; symmetry; exact Heq).
      unfold open_exp_wrt_exp.
      rewrite <- (subst_open_comm e0 v0 x0 y 0 Hyx Hlc).
      eapply IHpre.
      * apply uniq_cons; auto.
      * exact Hlc.
      * apply binds_cons_iff. right. exact Hb.
      * apply typing_weaken_cons; auto.
  - (* mergev *)
    simpl.
    assert (Heq1 : subst_exp v0 x0 v1 = v1).
    { apply subst_exp_notin. intros Hc. apply (Etyping_fv nil v1 A0 H1 x0) in Hc.
      exact (in_dom_nil x0 Hc). }
    assert (Heq2 : subst_exp v0 x0 v2 = v2).
    { apply subst_exp_notin. intros Hc. apply (Etyping_fv nil v2 B0 H2 x0) in Hc.
      exact (in_dom_nil x0 Hc). }
    rewrite Heq1, Heq2.
    eapply Etyp_mergev; eauto.
Qed.

Lemma fv_open_rec_sub : forall e k u z,
    z \in fv_exp (open_exp_wrt_exp_rec k u e) ->
    z \in fv_exp e \/ z \in fv_exp u.
Proof.
  induction e; intros k u z Hz; simpl in *.
  - (* var_b *)
    destruct (lt_eq_lt_dec n k) as [[Hlt|Heq]|Hgt]; simpl in *.
    + exfalso. exact (in_empty_elim z Hz).
    + right. exact Hz.
    + exfalso. exact (in_empty_elim z Hz).
  - (* var_f *) left. apply AtomSetImpl.singleton_1 in Hz.
    apply AtomSetImpl.singleton_2. auto.
  - (* top *) exfalso. exact (in_empty_elim z Hz).
  - (* lit *) exfalso. exact (in_empty_elim z Hz).
  - (* abs *) apply IHe in Hz. destruct Hz as [Hz|Hz]; auto.
  - (* fix *) apply IHe in Hz. destruct Hz as [Hz|Hz]; auto.
  - (* app *) apply AtomSetImpl.union_1 in Hz. destruct Hz as [Hz|Hz].
    + apply IHe1 in Hz. destruct Hz as [Hz|Hz]; auto.
    + apply IHe2 in Hz. destruct Hz as [Hz|Hz]; auto.
  - (* merge *) apply AtomSetImpl.union_1 in Hz. destruct Hz as [Hz|Hz].
    + apply IHe1 in Hz. destruct Hz as [Hz|Hz]; auto.
    + apply IHe2 in Hz. destruct Hz as [Hz|Hz]; auto.
  - (* anno *) apply IHe in Hz. destruct Hz as [Hz|Hz]; auto.
Qed.

Lemma fv_open_rec_var_inv : forall e k y z,
    z \in fv_exp (open_exp_wrt_exp_rec k (e_var_f y) e) ->
    z = y \/ z \in fv_exp e.
Proof.
  induction e; intros k y z Hz; simpl in *.
  - (* var_b *)
    destruct (lt_eq_lt_dec n k) as [[Hlt|Heq]|Hgt]; simpl in *.
    + exfalso. exact (in_empty_elim z Hz).
    + apply AtomSetImpl.singleton_1 in Hz. left. auto.
    + exfalso. exact (in_empty_elim z Hz).
  - (* var_f *) apply AtomSetImpl.singleton_1 in Hz. right.
    apply AtomSetImpl.singleton_2. auto.
  - (* top *) exfalso. exact (in_empty_elim z Hz).
  - (* lit *) exfalso. exact (in_empty_elim z Hz).
  - (* abs *) apply IHe in Hz. auto.
  - (* fix *) apply IHe in Hz. auto.
  - (* app *) apply AtomSetImpl.union_1 in Hz. destruct Hz as [Hz|Hz].
    + apply IHe1 in Hz. destruct Hz as [->|Hz]; auto.
    + apply IHe2 in Hz. destruct Hz as [->|Hz]; auto.
  - (* merge *) apply AtomSetImpl.union_1 in Hz. destruct Hz as [Hz|Hz].
    + apply IHe1 in Hz. destruct Hz as [->|Hz]; auto.
    + apply IHe2 in Hz. destruct Hz as [->|Hz]; auto.
  - (* anno *) apply IHe in Hz. auto.
Qed.

Lemma typing_binds_congr_fv : forall G G' e A,
    uniq G -> uniq G' ->
    (forall x B, x \in fv_exp e -> (binds x B G <-> binds x B G')) ->
    Etyping G e A -> Etyping G' e A.
Proof.
  intros G G' e A HuG HuG' Hb E.
  revert G' HuG' Hb.
  induction E as
    [ G0 u0
    | G0 i0 u0
    | G0 x0 A0 u0 b0
    | L G0 A0 e0 D0 C0 B0 Hpre IHpre sCA sBD
    | G0 e1 e2 B0 A0 H2 IH2 H1 IH1
    | G0 e1 e2 A0 B0 H1 IH1 H2 IH2 dsp
    | G0 e0 A0 B0 H1 IH1 sBA
    | L G0 e0 A0 Hpre IHpre
    | G0 v1 v2 A0 B0 u0 hval H1 IH1 H2 IH2 c0 ];
  intros G' HuG' Hb.
  - (* top *) constructor. auto.
  - (* lit *) constructor. auto.
  - (* var *)
    eapply Etyp_var.
    + auto.
    + exact (proj1 (Hb x0 A0 (@AtomSetImpl.singleton_2 x0 x0 eq_refl)) b0).
  - (* abs *)
    eapply Etyp_abs with (L := L \u dom G0 \u dom G').
    + intros x Hx.
      apply notin_union_1 in Hx as HxL. apply notin_union_2 in Hx as HxR.
      apply notin_union_1 in HxR as HxG. apply notin_union_2 in HxR as HxG'.
      assert (HuGx : uniq (cons (x, A0) G0)) by (apply uniq_cons; auto).
      assert (HuG'x : uniq (cons (x, A0) G')) by (apply uniq_cons; auto).
      assert (Hbx : forall z C, z \in fv_exp (open_exp_wrt_exp e0 (e_var_f x)) ->
                   (binds z C (cons (x, A0) G0) <-> binds z C (cons (x, A0) G'))).
      { intros z C Hz. apply fv_open_rec_var_inv in Hz. destruct Hz as [Heq|Hz].
        - subst z. split.
          + intros Hbz. apply binds_cons_iff in Hbz. destruct Hbz as [[H1 H2]|Hbz].
            * apply binds_cons_iff. left; split; auto.
            * exfalso. apply uniq_cons_iff in HuGx. destruct HuGx as [_ Hnd].
              apply Hnd. apply binds_dom in Hbz. auto.
          + intros Hbz. apply binds_cons_iff in Hbz. destruct Hbz as [[H1 H2]|Hbz].
            * apply binds_cons_iff. left; split; auto.
            * exfalso. apply uniq_cons_iff in HuG'x. destruct HuG'x as [_ Hnd].
              apply Hnd. apply binds_dom in Hbz. auto.
        - split.
          + intros Hbz. apply binds_cons_iff in Hbz. destruct Hbz as [[H1 H2]|Hbz].
            * apply binds_cons_iff. left; split; auto.
            * apply binds_cons_iff. right. apply (proj1 (Hb z C Hz)); auto.
          + intros Hbz. apply binds_cons_iff in Hbz. destruct Hbz as [[H1 H2]|Hbz].
            * apply binds_cons_iff. left; split; auto.
            * apply binds_cons_iff. right. apply (proj2 (Hb z C Hz)); auto. }
      exact (IHpre x HxL HuGx (cons (x, A0) G') HuG'x Hbx).
    + auto.
    + auto.
  - (* app *) eapply Etyp_app.
    + apply (IH2 HuG G' HuG'). intros x B Hx. apply Hb.
      apply AtomSetImpl.union_3. auto.
    + apply (IH1 HuG G' HuG'). intros x B Hx. apply Hb.
      apply AtomSetImpl.union_2. auto.
  - (* merge *) eapply Etyp_merge.
    + apply (IH1 HuG G' HuG'). intros x B Hx. apply Hb.
      apply AtomSetImpl.union_2. auto.
    + apply (IH2 HuG G' HuG'). intros x B Hx. apply Hb.
      apply AtomSetImpl.union_3. auto.
    + auto.
  - (* anno *) eapply Etyp_anno.
    + apply (IH1 HuG G' HuG'). intros x B Hx. apply Hb. auto.
    + auto.
  - (* fix *)
    eapply Etyp_fix with (L := L \u dom G0 \u dom G').
    + intros x Hx.
      apply notin_union_1 in Hx as HxL. apply notin_union_2 in Hx as HxR.
      apply notin_union_1 in HxR as HxG. apply notin_union_2 in HxR as HxG'.
      assert (HuGx : uniq (cons (x, A0) G0)) by (apply uniq_cons; auto).
      assert (HuG'x : uniq (cons (x, A0) G')) by (apply uniq_cons; auto).
      assert (Hbx : forall z C, z \in fv_exp (open_exp_wrt_exp e0 (e_var_f x)) ->
                   (binds z C (cons (x, A0) G0) <-> binds z C (cons (x, A0) G'))).
      { intros z C Hz. apply fv_open_rec_var_inv in Hz. destruct Hz as [Heq|Hz].
        - subst z. split.
          + intros Hbz. apply binds_cons_iff in Hbz. destruct Hbz as [[H1 H2]|Hbz].
            * apply binds_cons_iff. left; split; auto.
            * exfalso. apply uniq_cons_iff in HuGx. destruct HuGx as [_ Hnd].
              apply Hnd. apply binds_dom in Hbz. auto.
          + intros Hbz. apply binds_cons_iff in Hbz. destruct Hbz as [[H1 H2]|Hbz].
            * apply binds_cons_iff. left; split; auto.
            * exfalso. apply uniq_cons_iff in HuG'x. destruct HuG'x as [_ Hnd].
              apply Hnd. apply binds_dom in Hbz. auto.
        - split.
          + intros Hbz. apply binds_cons_iff in Hbz. destruct Hbz as [[H1 H2]|Hbz].
            * apply binds_cons_iff. left; split; auto.
            * apply binds_cons_iff. right. apply (proj1 (Hb z C Hz)); auto.
          + intros Hbz. apply binds_cons_iff in Hbz. destruct Hbz as [[H1 H2]|Hbz].
            * apply binds_cons_iff. left; split; auto.
            * apply binds_cons_iff. right. apply (proj2 (Hb z C Hz)); auto. }
      exact (IHpre x HxL HuGx (cons (x, A0) G') HuG'x Hbx).
  - (* mergev *) eapply Etyp_mergev; eauto.
Qed.

(* Main opening/substitution lemma for typing. *)
Lemma typing_open : forall A e B L v,
    (forall x, x \notin L ->
       Etyping (cons (x, A) nil) (open_exp_wrt_exp e (e_var_f x)) B) ->
    lc_exp v -> Etyping nil v A ->
    Etyping nil (open_exp_wrt_exp e v) B.
Proof.
  intros A e B L v Hpre Hlc Hv.
  destruct (atom_fresh (L \u fv_exp e)) as [x Hx].
  apply notin_union_1 in Hx as HxL.
  apply notin_union_2 in Hx as Hxfv.
  pose proof (Hpre x HxL) as Htx.
  assert (Hu : uniq (cons (x, A) (nil : ctx))) by (apply uniq_cons; auto).
  assert (Hb : binds x A (cons (x, A) (nil : ctx))).
  { apply binds_cons_iff. left. auto. }
  assert (Hxdomnil : x \notin dom (nil : ctx)).
  { rewrite dom_nil. apply notin_empty_1. }
  pose proof (typing_weaken_cons nil v A Hv x A (uniq_nil _) Hxdomnil) as Hv'.
  pose proof (typing_subst_gen (cons (x, A) nil) (open_exp_wrt_exp e (e_var_f x)) B
                Htx x A v Hu Hlc Hb Hv') as Hsub.
  unfold open_exp_wrt_exp in Hsub.
  rewrite subst_open_self in Hsub by auto.
  (* now remove the unused binding of x *)
  assert (Hxnotinv : x \notin fv_exp v).
  { intros Hc. exact (in_dom_nil x (Etyping_fv nil v A Hv x Hc)). }
  assert (Hxnotin : x \notin fv_exp (open_exp_wrt_exp e v)).
  { intros Hc. apply fv_open_rec_sub in Hc. destruct Hc as [Hc|Hc]; auto. }
  eapply typing_binds_congr_fv.
  - exact Hu.
  - apply uniq_nil.
  - intros z C Hz. split; intros Hbz.
    + apply binds_cons_iff in Hbz. destruct Hbz as [[HzC HW]|Hbz]; auto.
      exfalso. apply Hxnotin. subst z. auto.
    + apply binds_cons_iff. right. auto.
  - exact Hsub.
Qed.

(* Typing implies local closedness. *)
Lemma typing_lc_at : forall G e A, Etyping G e A -> lc_at 0 e.
Proof.
  intros G e A E. induction E as
    [ G0 u0 | G0 i0 u0 | G0 x0 A0 u0 b0
    | L G0 A0 e0 D0 C0 B0 Hpre IHpre sCA sBD
    | G0 e1 e2 B0 A0 H2 IH2 H1 IH1
    | G0 e1 e2 A0 B0 H1 IH1 H2 IH2 dsp
    | G0 e0 A0 B0 H1 IH1 sBA
    | L G0 e0 A0 Hpre IHpre
    | G0 v1 v2 A0 B0 u0 hval H1 IH1 H2 IH2 c0 ].
  - constructor.
  - constructor.
  - constructor.
  - (* abs *)
    apply lc_at_abs.
    destruct (atom_fresh L) as [x Hx].
    apply lc_at_open_inv with (u := e_var_f x).
    apply (IHpre x Hx).
  - constructor; auto.
  - constructor; auto.
  - constructor; auto.
  - (* fix *)
    apply lc_at_fix.
    destruct (atom_fresh L) as [x Hx].
    apply lc_at_open_inv with (u := e_var_f x).
    apply (IHpre x Hx).
  - constructor; auto.
Qed.

Lemma typing_lc : forall G e A, Etyping G e A -> lc_exp e.
Proof.
  intros G e A H. apply (proj2 (lc_exp_lc_at e)). exact (typing_lc_at G e A H).
Qed.

(* ============================================================ *)
(* Subtyping lemmas                                              *)
(* ============================================================ *)

(* A size-annotated version of subtyping, used to prove transitivity. *)
Inductive sub_sz : typ -> typ -> nat -> Prop :=
  | sz_int : sub_sz t_int t_int 1
  | sz_top : forall A, sub_sz A t_top 1
  | sz_toparr : forall A B1 B2 n,
      sub_sz t_top B2 n -> sub_sz A (t_arrow B1 B2) (S n)
  | sz_arr : forall A1 A2 B1 B2 n1 n2,
      sub_sz B1 A1 n1 -> sub_sz A2 B2 n2 ->
      sub_sz (t_arrow A1 A2) (t_arrow B1 B2) (S (n1 + n2))
  | sz_andl1 : forall A1 A2 A3 n,
      sub_sz A1 A3 n -> sub_sz (t_and A1 A2) A3 (S n)
  | sz_andl2 : forall A1 A2 A3 n,
      sub_sz A2 A3 n -> sub_sz (t_and A1 A2) A3 (S n)
  | sz_andr : forall A1 A2 A3 n1 n2,
      sub_sz A1 A2 n1 -> sub_sz A1 A3 n2 ->
      sub_sz A1 (t_and A2 A3) (S (n1 + n2)).

Lemma sub_sz_sub : forall A B n, sub_sz A B n -> sub A B.
Proof.
  intros A B n H. induction H.
  - constructor.
  - constructor.
  - apply S_toparr. auto.
  - apply S_arr; auto.
  - apply S_andl1. auto.
  - apply S_andl2. auto.
  - apply S_andr; auto.
Qed.

Lemma sub_sub_sz : forall A B, sub A B -> exists n, sub_sz A B n.
Proof.
  intros A B H. induction H.
  - exists 1. apply sz_int.
  - exists 1. apply sz_top.
  - destruct IHsub as [n Hn]. exists (S n). apply sz_toparr. auto.
  - destruct IHsub1 as [n1 Hn1]. destruct IHsub2 as [n2 Hn2].
    exists (S (n1 + n2)). apply sz_arr; auto.
  - destruct IHsub as [n Hn]. exists (S n). apply sz_andl1. auto.
  - destruct IHsub as [n Hn]. exists (S n). apply sz_andl2. auto.
  - destruct IHsub1 as [n1 Hn1]. destruct IHsub2 as [n2 Hn2].
    exists (S (n1 + n2)). apply sz_andr; auto.
Qed.

Lemma sub_sz_pos : forall A B n, sub_sz A B n -> 1 <= n.
Proof. intros A B n H. destruct H; simpl; lia. Qed.

Ltac use_sub_IH IH :=
  first [ match goal with
          | H1 : sub_sz ?A ?B ?n, H2 : sub_sz ?B ?C ?m |- sub ?A ?C =>
              apply (IH n m A B C); [lia | exact H1 | exact H2] end
        | match goal with
          | H2 : sub_sz ?B ?C ?m |- sub ?A ?C =>
              apply (IH 1 m A t_top C); [lia | apply sz_top | exact H2] end
        | match goal with
          | H1 : sub_sz ?A ?B ?n |- sub ?A ?C =>
              apply (IH n 1 A B t_top); [lia | exact H1 | apply sz_top] end ].

Ltac solve_sub IH :=
  first [ apply S_top
        | apply S_z
        | apply S_toparr; solve_sub IH
        | apply S_arr; [solve_sub IH | solve_sub IH]
        | apply S_andl1; solve_sub IH
        | apply S_andl2; solve_sub IH
        | apply S_andr; [solve_sub IH | solve_sub IH]
        | use_sub_IH IH ].

Lemma sub_sz_trans : forall k, forall n m A B C,
    n + m <= k -> sub_sz A B n -> sub_sz B C m -> sub A C.
Proof.
  intros k. induction k as [| k IH]; intros n m A B C Hle H1 H2.
  - destruct H1; simpl in *; lia.
  - pose proof H1 as H1c. pose proof H2 as H2c.
    dependent destruction H1.
    pose proof H2c as H2w.
    all: try (dependent destruction H2c).
    all: try solve [ solve_sub IH ].
Qed.

Lemma sub_trans : forall A B C, sub A B -> sub B C -> sub A C.
Proof.
  intros A B C H1 H2.
  destruct (sub_sub_sz A B H1) as [n Hn].
  destruct (sub_sub_sz B C H2) as [m Hm].
  exact (sub_sz_trans (n + m) n m A B C (Nat.le_refl (n + m)) Hn Hm).
Qed.

Lemma sub_refl : forall A, sub A A.
Proof.
  intros A. induction A.
  - apply S_z.
  - apply S_top.
  - apply S_arr; [apply IHA1 | apply IHA2].
  - apply S_andr.
    + apply S_andl1. apply IHA1.
    + apply S_andl2. apply IHA2.
Qed.

Lemma topLike_and_inv : forall A B, topLike (t_and A B) -> topLike A /\ topLike B.
Proof. intros A B H. inversion H; auto. Qed.

Lemma topLike_arrow_inv : forall A B, topLike (t_arrow A B) -> topLike B.
Proof. intros A B H. inversion H; auto. Qed.

Lemma topLike_int_absurd : topLike t_int -> False.
Proof. intros H. inversion H. Qed.

Lemma sub_preserves_topLike : forall A B, sub A B -> topLike A -> topLike B.
Proof.
  intros A B H. induction H; intros Htl.
  - inversion Htl.
  - constructor.
  - apply TL_arr. apply IHsub. constructor.
  - apply TL_arr. apply IHsub2. apply topLike_arrow_inv in Htl. auto.
  - apply IHsub. apply topLike_and_inv in Htl. tauto.
  - apply IHsub. apply topLike_and_inv in Htl. tauto.
  - apply TL_and; auto.
Qed.

Lemma topLike_sub : forall A, topLike A -> sub t_top A.
Proof.
  intros A H. induction H.
  - apply S_top.
  - apply S_andr; auto.
  - apply S_toparr. auto.
Qed.

Lemma sub_top_iff : forall A, sub t_top A <-> topLike A.
Proof.
  intros A. split.
  - intros H. apply (sub_preserves_topLike t_top A H). constructor.
  - apply topLike_sub.
Qed.

Lemma disjointSpec_mono : forall A B A' B',
    disjointSpec A B -> sub A A' -> sub B B' -> disjointSpec A' B'.
Proof.
  intros A B A' B' D HsA HsB C H1 H2.
  apply D.
  - apply (sub_trans A A' C); auto.
  - apply (sub_trans B B' C); auto.
Qed.

Lemma disjointSpec_int_int_absurd : disjointSpec t_int t_int -> False.
Proof.
  intros D. pose proof (D t_int S_z S_z) as H. inversion H.
Qed.

(* ============================================================ *)
(* Basic properties of type-directed reduction                   *)
(* ============================================================ *)

Lemma TypedReduce_lc_at : forall v A v', TypedReduce v A v' -> lc_at 0 v'.
Proof.
  intros v A v' H. induction H.
  - apply lc_at_lit.
  - apply lc_at_top.
  - apply lc_at_abs. apply lc_at_top.
  - apply lc_at_abs. apply (proj1 (lc_exp_lc_at (e_abs A e B))) in H. inversion H. assumption.
  - assumption.
  - assumption.
  - apply lc_at_merge; assumption.
Qed.

Lemma TypedReduce_lc : forall v A v', TypedReduce v A v' -> lc_exp v'.
Proof.
  intros. apply (proj2 (lc_exp_lc_at v')). exact (TypedReduce_lc_at v A v' H).
Qed.

Lemma TypedReduce_value : forall v A v', TypedReduce v A v' -> value v'.
Proof.
  intros v A v' H. induction H.
  - apply value_lit.
  - apply value_unit.
  - apply value_anno. apply (proj2 (lc_exp_lc_at (e_abs t_top e_top B))). apply lc_at_abs. apply lc_at_top.
  - apply value_anno. apply (lc_abs_iff A e D). apply (proj1 (lc_abs_iff A e B)). exact H.
  - assumption.
  - assumption.
  - apply value_merge; assumption.
Qed.

(* ============================================================ *)
(* Canonical forms for top-like types                            *)
(* ============================================================ *)

Fixpoint canon (A:typ) : exp :=
  match A with
  | t_int => e_top
  | t_top => e_top
  | t_arrow A B => e_abs t_top e_top B
  | t_and A B => e_merge (canon A) (canon B)
  end.

Inductive topCanon : exp -> Prop :=
  | tc_top : topCanon e_top
  | tc_abs : forall B, topLike B -> topCanon (e_abs t_top e_top B)
  | tc_merge : forall u1 u2, topCanon u1 -> topCanon u2 -> topCanon (e_merge u1 u2).

Lemma topCanon_lc : forall u, topCanon u -> lc_exp u.
Proof.
  intros u H. induction H.
  - constructor.
  - apply lc_abs_iff. intros x. constructor.
  - apply lc_merge_iff. auto.
Qed.

Lemma canon_topCanon : forall A, topLike A -> topCanon (canon A).
Proof.
  intros A H. induction H.
  - simpl. constructor.
  - simpl. constructor; auto.
  - simpl. apply tc_abs. auto.
Qed.

Lemma canon_lc : forall A, topLike A -> lc_exp (canon A).
Proof. intros. apply topCanon_lc. apply canon_topCanon. auto. Qed.

Lemma reduce_topCanon_topLike : forall u C w,
    topCanon u -> TypedReduce u C w -> topLike C.
Proof.
  intros u C w Hu H. revert Hu. induction H; intros Hu.
  - (* lit *) inversion Hu.
  - (* top *) constructor.
  - (* toparr *) apply TL_arr. auto.
  - (* arrow *) inversion Hu; subst.
    apply TL_arr. exfalso. apply H0. apply (sub_preserves_topLike B D H2 H4).
  - (* mergevl *) inversion Hu; subst. auto.
  - (* mergevr *) inversion Hu; subst. auto.
  - (* tag *) apply TL_and; auto.
Qed.

Lemma reduce_topLike_canon : forall v A v',
    TypedReduce v A v' -> topLike A -> v' = canon A.
Proof.
  intros v A v' H. induction H; intros Htl.
  - inversion Htl.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - apply topLike_arrow_inv in Htl. contradiction.
  - auto.
  - auto.
  - apply topLike_and_inv in Htl. destruct Htl as [H1' H2'].
    simpl. rewrite (IHTypedReduce1 H1'). rewrite (IHTypedReduce2 H2'). reflexivity.
Qed.

Lemma reduce_total : forall A, topLike A -> forall v, lc_exp v -> TypedReduce v A (canon A).
Proof.
  intros A H. induction H; intros v0 Hlc.
  - simpl. apply TReduce_top. auto.
  - simpl. apply TReduce_and; auto.
  - simpl. apply TReduce_toparr; auto.
Qed.

Lemma reduce_top_unique : forall v w, TypedReduce v t_top w -> w = e_top.
Proof.
  intros v w H. pose proof (reduce_topLike_canon v t_top w H (TL_top)) as E.
  simpl in E. auto.
Qed.

Lemma value_lc : forall v, value v -> lc_exp v.
Proof.
  intros v H. induction H.
  - constructor.
  - constructor.
  - auto.
  - apply lc_merge_iff. auto.
Qed.

Fixpoint size_exp (e:exp) : nat :=
  match e with
  | e_var_b _ => 1
  | e_var_f _ => 1
  | e_top => 1
  | e_lit _ => 1
  | e_abs _ e _ => S (size_exp e)
  | e_fixpoint e _ => S (size_exp e)
  | e_app e1 e2 => S (size_exp e1 + size_exp e2)
  | e_merge e1 e2 => S (size_exp e1 + size_exp e2)
  | e_anno e _ => S (size_exp e)
  end.

Fixpoint size_typ (A:typ) : nat :=
  match A with
  | t_int => 1
  | t_top => 1
  | t_arrow A B => S (size_typ A + size_typ B)
  | t_and A B => S (size_typ A + size_typ B)
  end.

Lemma size_exp_pos : forall e, 1 <= size_exp e.
Proof. intros e. destruct e; simpl; lia. Qed.

Lemma size_typ_pos : forall A, 1 <= size_typ A.
Proof. intros A. destruct A; simpl; lia. Qed.

Lemma size_exp_lt_abs : forall A e B, size_exp e < size_exp (e_abs A e B).
Proof. intros. simpl. lia. Qed.

Lemma size_typ_lt_and1 : forall A B, size_typ A < size_typ (t_and A B).
Proof. intros. simpl. lia. Qed.

Lemma size_typ_lt_and2 : forall A B, size_typ B < size_typ (t_and A B).
Proof. intros. simpl. lia. Qed.

Lemma size_typ_lt_arrow1 : forall A B, size_typ A < size_typ (t_arrow A B).
Proof. intros. simpl. lia. Qed.

Lemma size_typ_lt_arrow2 : forall A B, size_typ B < size_typ (t_arrow A B).
Proof. intros. simpl. lia. Qed.

Lemma sub_and_proj : forall X A B, sub X (t_and A B) -> sub X A /\ sub X B.
Proof.
  intros X A B H. remember (t_and A B) as Y eqn:Heq.
  revert A B Heq.
  induction H; intros A0 B0 Heq.
  - inversion Heq.
  - inversion Heq.
  - inversion Heq.
  - inversion Heq.
  - (* andl1 *) inversion Heq; subst.
    destruct (IHsub A0 B0 eq_refl) as [H1' H2'].
    split; [apply S_andl1 | apply S_andl1]; auto.
  - (* andl2 *) inversion Heq; subst.
    destruct (IHsub A0 B0 eq_refl) as [H1' H2'].
    split; [apply S_andl2 | apply S_andl2]; auto.
  - (* andr *) inversion Heq; subst. auto.
Qed.

Lemma size_exp_lt_merge1 : forall e1 e2, size_exp e1 < size_exp (e_merge e1 e2).
Proof. intros. simpl. lia. Qed.
Lemma size_exp_lt_merge2 : forall e1 e2, size_exp e2 < size_exp (e_merge e1 e2).
Proof. intros. simpl. lia. Qed.

Lemma Etyping_merge_inv : forall e1 e2 B,
    Etyping nil (e_merge e1 e2) B ->
    exists A1 A2, B = t_and A1 A2 /\ Etyping nil e1 A1 /\ Etyping nil e2 A2.
Proof.
  intros e1 e2 B H. inversion H; subst.
  - exists A, B0. split; [reflexivity | split; assumption].
  - exists A, B0. split; [reflexivity | split; assumption].
Qed.

Lemma Etyping_lit_inv : forall i B, Etyping nil (e_lit i) B -> B = t_int.
Proof. intros i B H. inversion H. reflexivity. Qed.

Lemma Etyping_top_inv : forall B, Etyping nil e_top B -> B = t_top.
Proof. intros B H. inversion H. reflexivity. Qed.

Lemma Etyping_abs_inv : forall A e D B,
    Etyping nil (e_abs A e D) B -> exists C, B = t_arrow C D /\ sub C A.
Proof. intros A e D B H. inversion H; subst. exists C. auto. Qed.

Lemma value_merge_inv : forall v1 v2, value (e_merge v1 v2) -> value v1 /\ value v2.
Proof. intros v1 v2 H. inversion H. auto. Qed.

Lemma value_abs_lc : forall A e B, value (e_abs A e B) -> lc_exp (e_abs A e B).
Proof. intros A e B H. inversion H. auto. Qed.

Lemma value_app_false : forall e1 e2, value (e_app e1 e2) -> False.
Proof. intros e1 e2 H. inversion H. Qed.

Lemma value_anno_false : forall e A, value (e_anno e A) -> False.
Proof. intros e A H. inversion H. Qed.

Lemma value_fix_false : forall e A, value (e_fixpoint e A) -> False.
Proof. intros e A H. inversion H. Qed.

Lemma value_var_b_false : forall n, value (e_var_b n) -> False.
Proof. intros n H. inversion H. Qed.

Lemma value_var_f_false : forall x, value (e_var_f x) -> False.
Proof. intros x H. inversion H. Qed.

Lemma disjointSpec_and_l1 : forall A B C,
    disjointSpec (t_and A B) C -> disjointSpec A C.
Proof.
  intros. eapply disjointSpec_mono; [exact H | apply S_andl1; apply sub_refl | apply sub_refl].
Qed.
Lemma disjointSpec_and_l2 : forall A B C,
    disjointSpec (t_and A B) C -> disjointSpec B C.
Proof.
  intros. eapply disjointSpec_mono; [exact H | apply S_andl2; apply sub_refl | apply sub_refl].
Qed.
Lemma disjointSpec_and_r1 : forall A B C,
    disjointSpec A (t_and B C) -> disjointSpec A B.
Proof.
  intros. eapply disjointSpec_mono; [exact H | apply sub_refl | apply S_andl1; apply sub_refl].
Qed.
Lemma disjointSpec_and_r2 : forall A B C,
    disjointSpec A (t_and B C) -> disjointSpec A C.
Proof.
  intros. eapply disjointSpec_mono; [exact H | apply sub_refl | apply S_andl2; apply sub_refl].
Qed.

Lemma topLike_dec : forall A, topLike A \/ ~ topLike A.
Proof.
  intros A. induction A.
  - right. intros H. inversion H.
  - left. constructor.
  - destruct IHA2 as [H|H].
    + left. apply TL_arr. auto.
    + right. intros Ht. apply H. apply topLike_arrow_inv in Ht. auto.
  - destruct IHA1 as [H1|H1]; destruct IHA2 as [H2|H2].
    + left. apply TL_and; auto.
    + right. intros Ht. apply H2. apply topLike_and_inv in Ht. tauto.
    + right. intros Ht. apply H1. apply topLike_and_inv in Ht. tauto.
    + right. intros Ht. apply H1. apply topLike_and_inv in Ht. tauto.
Qed.

Lemma ord_dec : forall A, ord A \/ ~ ord A.
Proof.
  intros A. induction A.
  - left. constructor.
  - left. constructor.
  - left. constructor.
  - right. intros H. inversion H.
Qed.

(* ============================================================ *)
(* Coherence for disjointly typed values                         *)
(* ============================================================ *)

Ltac dih_facts :=
  try (repeat match goal with
    | H : value (e_merge ?u1 ?u2) |- _ =>
        let H1 := fresh "Hvv" in let H2 := fresh "Hvv" in
        destruct (value_merge_inv u1 u2 H) as [H1 H2]; clear H
    end);
  try (repeat match goal with
    | H : Etyping nil (e_merge ?u1 ?u2) ?B |- _ =>
        let A1 := fresh "Aaa" in let A2 := fresh "Abb" in
        let H1 := fresh "Htt" in let H2 := fresh "Htt" in let He := fresh "Hee" in
        destruct (Etyping_merge_inv u1 u2 B H) as [A1 [A2 [He [H1 H2]]]];
        try (subst B); clear H
    end).

Ltac derive_disj :=
  match goal with
  | Hd : disjointSpec (t_and ?A1 ?A2) (t_and ?B1 ?B2) |- _ =>
      pose proof (disjointSpec_and_l1 A1 A2 (t_and B1 B2) Hd);
      pose proof (disjointSpec_and_l2 A1 A2 (t_and B1 B2) Hd);
      pose proof (disjointSpec_and_r1 (t_and A1 A2) B1 B2 Hd);
      pose proof (disjointSpec_and_r2 (t_and A1 A2) B1 B2 Hd);
      clear Hd
  | Hd : disjointSpec (t_and ?A1 ?A2) ?B |- _ =>
      pose proof (disjointSpec_and_l1 A1 A2 B Hd);
      pose proof (disjointSpec_and_l2 A1 A2 B Hd);
      clear Hd
  | Hd : disjointSpec ?A (t_and ?B1 ?B2) |- _ =>
      pose proof (disjointSpec_and_r1 A B1 B2 Hd);
      pose proof (disjointSpec_and_r2 A B1 B2 Hd);
      clear Hd
  | |- _ => idtac
  end.

Ltac solve_disj :=
  match goal with
  | H : disjointSpec ?A ?B |- disjointSpec ?A ?B => exact H
  end.

Ltac solve_dih IH Hle :=
  match goal with
  | Hv1 : value ?w1, Ht1 : Etyping nil ?w1 ?A1,
    HR1 : TypedReduce ?w1 ?C1 ?x1,
    Hv2 : value ?w2, Ht2 : Etyping nil ?w2 ?A2,
    HR2 : TypedReduce ?w2 ?C2 ?x2
    |- ?x1 = ?x2 =>
      unify C1 C2;
      refine (IH w1 A1 w2 A2 C1 x1 x2 _ Hv1 Ht1 Hv2 Ht2 _ HR1 HR2);
      [ simpl in Hle; simpl; lia | solve_disj ]
  end.
Ltac solve_top_eq :=
  first [ match goal with
          | H1 : TypedReduce ?u1 t_top ?x1, H2 : TypedReduce ?u2 t_top ?x2 |- ?x1 = ?x2 =>
              rewrite (reduce_top_unique u1 x1 H1), (reduce_top_unique u2 x2 H2); reflexivity end
        | match goal with
          | H1 : TypedReduce ?u1 t_top ?x1 |- ?x1 = _ =>
              rewrite (reduce_top_unique u1 x1 H1); reflexivity end
        | match goal with
          | H2 : TypedReduce ?u2 t_top ?x2 |- _ = ?x2 =>
              rewrite (reduce_top_unique u2 x2 H2); reflexivity end
        | reflexivity ].

Ltac arrow_contradiction :=
  exfalso;
  match goal with
  | Hd : disjointSpec (t_arrow ?C01 ?B) (t_arrow ?C02 ?B'),
    Hs2 : sub ?B ?C2, Hs4 : sub ?B' ?C2, Hnt : ~ topLike ?C2 |- _ =>
      let Hsub1 := fresh "Hs" in let Hsub2 := fresh "Hs" in
      assert (Hsub1 : sub (t_arrow C01 B) (t_arrow (t_and C01 C02) C2))
        by (apply S_arr; [apply S_andl1; apply sub_refl | exact Hs2]);
      assert (Hsub2 : sub (t_arrow C02 B') (t_arrow (t_and C01 C02) C2))
        by (apply S_arr; [apply S_andl2; apply sub_refl | exact Hs4]);
      pose proof (Hd (t_arrow (t_and C01 C02) C2) Hsub1 Hsub2) as Htop;
      apply topLike_arrow_inv in Htop; exact (Hnt Htop)
  end.

Ltac prep_abs_typing H :=
  match type of H with
  | Etyping nil (e_abs ?A ?e ?B) ?Bty =>
      let C0 := fresh "C0" in let He := fresh "He" in let Hs := fresh "Hs" in
      destruct (Etyping_abs_inv A e B Bty H) as [C0 [He Hs]]; try (subst Bty)
  end.

Ltac prep_merge :=
  try (match goal with Hv : value (e_merge ?u1 ?u2) |- _ =>
        let H1 := fresh "Hvv" in let H2 := fresh "Hvv" in
        destruct (value_merge_inv u1 u2 Hv) as [H1 H2]; clear Hv end);
  try (match goal with Ht : Etyping nil (e_merge ?u1 ?u2) ?B |- _ =>
        let A1 := fresh "Aaa" in let A2 := fresh "Abb" in
        let H1 := fresh "Htt" in let H2 := fresh "Htt" in let He := fresh "Hee" in
        destruct (Etyping_merge_inv u1 u2 B Ht) as [A1 [A2 [He [H1 H2]]]];
        try (rewrite He in *); try (subst B); clear Ht end).

Ltac recon_abs :=
  try (match goal with
       | Hlc : lc_exp (e_abs ?A ?e ?B), Hn : ~ topLike ?Cc,
         Hs1 : sub ?Cd ?A, Hs2 : sub ?B ?Cc |- _ =>
           pose proof (TReduce_arrow A e B Cd Cc Hlc Hn Hs1 Hs2) as HRabs
       end).

Ltac recon_abs_left :=
  match goal with
  | Hother : TypedReduce ?u (t_arrow ?Cd ?Cc) ?x |- e_abs ?A ?e ?Cc = ?x =>
      match goal with
      | Hlc : lc_exp (e_abs A e ?B), Hn : ~ topLike Cc,
        Hs1 : sub Cd A, Hs2 : sub ?B Cc |- _ =>
          pose proof (TReduce_arrow A e B Cd Cc Hlc Hn Hs1 Hs2) as HRabs
      end
  end.

Ltac recon_abs_right :=
  match goal with
  | Hother : TypedReduce ?u (t_arrow ?Cd ?Cc) ?x |- ?x = e_abs ?A ?e ?Cc =>
      match goal with
      | Hlc : lc_exp (e_abs A e ?B), Hn : ~ topLike Cc,
        Hs1 : sub Cd A, Hs2 : sub ?B Cc |- _ =>
          pose proof (TReduce_arrow A e B Cd Cc Hlc Hn Hs1 Hs2) as HRabs
      end
  end.

Ltac contra_top C :=
  exfalso; apply C; eassumption.

Lemma disjoint_coh_n : forall n w1 A1 w2 A2 C x1 x2,
    size_exp w1 + size_exp w2 + size_typ C <= n ->
    value w1 -> Etyping nil w1 A1 ->
    value w2 -> Etyping nil w2 A2 ->
    disjointSpec A1 A2 ->
    TypedReduce w1 C x1 -> TypedReduce w2 C x2 -> x1 = x2.
Proof.
  intros n. induction n as [| n IH]; intros w1 A1 w2 A2 C x1 x2 Hle Hv1 Ht1 Hv2 Ht2 Hdis HR1 HR2.
  - exfalso. pose (size_exp_pos w1). pose (size_exp_pos w2). pose (size_typ_pos C). lia.
  - destruct C as [| | C1 C2 | C1 C2].
    + (* int *)
      dependent destruction HR1; dependent destruction HR2.
      (* lit/lit contradiction *)
      all: try solve [ exfalso; apply disjointSpec_int_int_absurd;
        match goal with
        | Ht1' : Etyping nil (e_lit ?i) ?X, Ht2' : Etyping nil (e_lit ?j) ?Y,
          Hd : disjointSpec ?X ?Y |- _ =>
            rewrite (Etyping_lit_inv i X Ht1') in Hd;
            rewrite (Etyping_lit_inv j Y Ht2') in Hd; exact Hd
        end ].
      all: try dih_facts.
      all: try derive_disj.
      all: try (match goal with |- e_lit ?i = _ => pose proof (TReduce_lit i) as HRlit end).
      all: try (match goal with |- _ = e_lit ?i => pose proof (TReduce_lit i) as HRlit end).
      all: try solve [ solve_dih IH Hle ].
      all: try derive_disj.
      all: try (match goal with |- e_lit ?i = _ => pose proof (TReduce_lit i) as HRlit end).
      all: try (match goal with |- _ = e_lit ?i => pose proof (TReduce_lit i) as HRlit end).
      all: try solve [ solve_dih IH Hle ].
      all: try derive_disj.
      all: try solve [ solve_dih IH Hle ].
      all: try derive_disj.
      all: try solve [ solve_dih IH Hle ].
      all: try derive_disj.
      all: try solve [ solve_dih IH Hle ].
      all: try derive_disj.
      all: try solve [ solve_dih IH Hle ].
    + (* top *)
      dependent destruction HR1; dependent destruction HR2.
      all: try solve [ solve_top_eq ].
    + (* arrow *)
      destruct (topLike_dec C2) as [Htl2|Hntl2].
      * assert (Htl : topLike (t_arrow C1 C2)) by (apply TL_arr; auto).
        rewrite (reduce_topLike_canon w1 (t_arrow C1 C2) x1 HR1 Htl).
        rewrite (reduce_topLike_canon w2 (t_arrow C1 C2) x2 HR2 Htl).
        reflexivity.
      * dependent destruction HR1; dependent destruction HR2.
        1: reflexivity.
        1: exfalso; apply Hntl2; eassumption.
        1: exfalso; apply Hntl2; eassumption.
        1: exfalso; apply Hntl2; eassumption.
        1: exfalso; apply Hntl2; eassumption.
        1: prep_abs_typing Ht1; prep_abs_typing Ht2; arrow_contradiction.
        1: prep_abs_typing Ht1; prep_merge; recon_abs_left;
           try derive_disj; try derive_disj; try derive_disj; solve_dih IH Hle.
        1: prep_abs_typing Ht1; prep_merge; recon_abs_left;
           try derive_disj; try derive_disj; try derive_disj; solve_dih IH Hle.
        1: exfalso; apply Hntl2; eassumption.
        1: prep_abs_typing Ht2; prep_merge; recon_abs_right;
           try derive_disj; try derive_disj; try derive_disj; solve_dih IH Hle.
        1: prep_merge; prep_merge; try derive_disj; try derive_disj; try derive_disj;
           try derive_disj;

           solve_dih IH Hle.
        1: prep_merge; prep_merge; try derive_disj; try derive_disj; try derive_disj;
           try derive_disj; solve_dih IH Hle.
        1: exfalso; apply Hntl2; eassumption.
        1: prep_abs_typing Ht2; prep_merge; recon_abs_right;
           try derive_disj; try derive_disj; try derive_disj; solve_dih IH Hle.
        1: prep_merge; prep_merge; try derive_disj; try derive_disj; try derive_disj;
           try derive_disj; solve_dih IH Hle.
        1: prep_merge; prep_merge; try derive_disj; try derive_disj; try derive_disj;
           try derive_disj; solve_dih IH Hle.
    + (* and *)
      dependent destruction HR1; dependent destruction HR2.
      all: try solve [ exfalso; match goal with Ho : ord (t_and _ _) |- _ => inversion Ho end ].
      all: try solve [ f_equal; [ solve_dih IH Hle | solve_dih IH Hle ] ].
Qed.

Lemma Etyping_merge_inv2 : forall e1 e2 B,
    Etyping nil (e_merge e1 e2) B ->
    exists A1 A2, B = t_and A1 A2 /\ Etyping nil e1 A1 /\ Etyping nil e2 A2 /\
      (disjointSpec A1 A2 \/ consistencySpec e1 e2).
Proof.
  intros e1 e2 B H. inversion H; subst.
  - exists A, B0. split; [reflexivity|]. split; [assumption|]. split; [assumption|].
    left; assumption.
  - exists A, B0. split; [reflexivity|]. split; [assumption|]. split; [assumption|].
    right; assumption.
Qed.

Ltac prep_merge_det :=
  try (match goal with Hv : value (e_merge ?u1 ?u2) |- _ =>
        let H1 := fresh "Hvv" in let H2 := fresh "Hvv" in
        destruct (value_merge_inv u1 u2 Hv) as [H1 H2]; clear Hv end);
  try (match goal with Ht : Etyping nil (e_merge ?u1 ?u2) ?B |- _ =>
        let A1 := fresh "Aaa" in let A2 := fresh "Abb" in
        let H1 := fresh "Htt" in let H2 := fresh "Htt" in let He := fresh "Hee" in
        let Hdc := fresh "Hdc" in
        destruct (Etyping_merge_inv2 u1 u2 B Ht) as [A1 [A2 [He [H1 [H2 Hdc]]]]];
        try (rewrite He in *); try (subst B); clear Ht end).

(* ============================================================ *)
(* Determinism of reduction for typable values                   *)
(* ============================================================ *)

Ltac det_same_type IH Hsz :=
  match goal with
  | Hv : value ?v, Ht : Etyping nil ?v ?B,
    HR1 : TypedReduce ?v ?A ?x1, HR2 : TypedReduce ?v ?A ?x2 |- ?x1 = ?x2 =>
      exact (IH v B Hv Ht A ltac:(simpl in Hsz; simpl; lia) x1 x2 HR1 HR2)
  | Hv : value ?v, Ht : Etyping nil ?v ?B,
    HR1 : TypedReduce ?v ?A ?x1, HR2 : TypedReduce ?v ?A ?x2 |- ?x2 = ?x1 =>
      symmetry; exact (IH v B Hv Ht A ltac:(simpl in Hsz; simpl; lia) x1 x2 HR1 HR2)
  end.

Ltac det_cross IH Hsz nn :=
  first [
  match goal with
  | Hv1 : value ?w1, Ht1 : Etyping nil ?w1 ?A1,
    HR1 : TypedReduce ?w1 ?A ?x1,
    Hv2 : value ?w2, Ht2 : Etyping nil ?w2 ?A2,
    HR2 : TypedReduce ?w2 ?A ?x2,
    Hdc : disjointSpec ?A1 ?A2 \/ consistencySpec ?w1 ?w2 |- ?x1 = ?x2 =>
      destruct Hdc as [Hd|Hc];
      [ exact (disjoint_coh_n nn w1 A1 w2 A2 A x1 x2 ltac:(simpl in Hsz; simpl; lia)
                 Hv1 Ht1 Hv2 Ht2 Hd HR1 HR2)
      | exact (Hc A x1 x2 HR1 HR2) ]
  end
  |
  match goal with
  | Hv1 : value ?w1, Ht1 : Etyping nil ?w1 ?A1,
    HR1 : TypedReduce ?w1 ?A ?x2,
    Hv2 : value ?w2, Ht2 : Etyping nil ?w2 ?A2,
    HR2 : TypedReduce ?w2 ?A ?x1,
    Hdc : disjointSpec ?A1 ?A2 \/ consistencySpec ?w1 ?w2 |- ?x1 = ?x2 =>
      destruct Hdc as [Hd|Hc];
      [ symmetry; exact (disjoint_coh_n nn w1 A1 w2 A2 A x2 x1 ltac:(simpl in Hsz; simpl; lia)
                 Hv1 Ht1 Hv2 Ht2 Hd HR1 HR2)
      | symmetry; exact (Hc A x2 x1 HR1 HR2) ]
  end ].

Lemma reduce_det_n : forall n v B,
    value v -> Etyping nil v B ->
    forall A, size_exp v + size_typ A <= n ->
    forall v1 v2, TypedReduce v A v1 -> TypedReduce v A v2 -> v1 = v2.
Proof.
  intros n. induction n as [|n IH]; intros v B Hv Ht A Hsz v1 v2 HR1 HR2.
  - exfalso. pose (size_exp_pos v). pose (size_typ_pos A). lia.
  - destruct A as [| | C1 C2 | C1 C2].
    + (* int *)
      dependent destruction HR1; dependent destruction HR2.
      all: try reflexivity.
      all: try prep_merge_det.
      all: try (det_same_type IH Hsz).
      all: try (det_cross IH Hsz n).
    + (* top *)
      dependent destruction HR1; dependent destruction HR2.
      all: try solve [ solve_top_eq ].
      all: try prep_merge_det.
      all: try (det_same_type IH Hsz).
      all: try (det_cross IH Hsz n).
    + (* arrow *)
      destruct (topLike_dec C2) as [Htl2|Hntl2].
      * assert (Htl : topLike (t_arrow C1 C2)) by (apply TL_arr; auto).
        rewrite (reduce_topLike_canon v (t_arrow C1 C2) v1 HR1 Htl).
        rewrite (reduce_topLike_canon v (t_arrow C1 C2) v2 HR2 Htl).
        reflexivity.
      * dependent destruction HR1; dependent destruction HR2.
        all: try solve [ exfalso; apply Hntl2; eassumption ].
        all: try reflexivity.
        all: try prep_merge_det.
        all: try (det_same_type IH Hsz).
        all: try (det_cross IH Hsz n).
    + (* and *)
      dependent destruction HR1; dependent destruction HR2.
      all: try solve [ exfalso; match goal with Ho : ord (t_and _ _) |- _ => inversion Ho end ].
      all: try solve [ f_equal; [ det_same_type IH Hsz | det_same_type IH Hsz ] ].
Qed.

(* ============================================================ *)
(* Projection: reducing a reduct yields a reduct of the original  *)
(* ============================================================ *)

Ltac proj_IH_same IH Hsz :=
  match goal with
  | Hv : value ?v, Ht : Etyping nil ?v ?B, HR1 : TypedReduce ?v ?A ?v',
    HR2 : TypedReduce ?v' ?C ?w |- TypedReduce ?v ?C ?w =>
      exact (IH v B Hv Ht A v' HR1 C w HR2 ltac:(simpl in Hsz; simpl; lia))
  end.

Ltac proj_IH_comp IH Hsz :=
  match goal with
  | Hv : value ?u, Ht : Etyping nil ?u ?Bu,
    HR : TypedReduce ?u ?Au ?u', HR2 : TypedReduce ?u' ?C ?w
    |- TypedReduce ?u ?C ?w =>
      exact (IH u Bu Hv Ht Au u' HR C w HR2 ltac:(simpl in Hsz; simpl; lia))
  end.

Lemma reduce_proj_n : forall n v B,
    value v -> Etyping nil v B ->
    forall A v', TypedReduce v A v' ->
    forall C w, TypedReduce v' C w ->
    size_exp v + size_exp v' + size_typ C <= n -> TypedReduce v C w.
Proof.
  intros n. induction n as [|n IH]; intros v B Hv Ht A v' HR1 C w HR2 Hsz.
  - exfalso. pose (size_exp_pos v). pose (size_exp_pos v'). pose (size_typ_pos C). lia.
  - pose proof HR2 as HR2c.
    dependent destruction HR2.
    + (* lit *)
      dependent destruction HR1.
      * apply TReduce_lit.
      * prep_merge. apply TReduce_mergevl; [eassumption | proj_IH_comp IH Hsz | first [eassumption | constructor]].
      * prep_merge. apply TReduce_mergevr; [eassumption | proj_IH_comp IH Hsz | first [eassumption | constructor]].
    + (* top *)
      apply TReduce_top. apply value_lc. exact Hv.
    + (* toparr *)
      apply reduce_total. apply TL_arr. eassumption. apply value_lc. exact Hv.
    + (* arrow *)
      dependent destruction HR1.
      * (* toparr *) exfalso.
        match goal with
        | Hnt : ~ topLike ?D', Hs : sub ?B0' ?D', Htl : topLike ?B0' |- _ =>
            exact (Hnt (sub_preserves_topLike B0' D' Hs Htl))
        end.
      * (* arrow *)
        apply TReduce_arrow.
        -- eassumption.
        -- eassumption.
        -- eassumption.
        -- eapply sub_trans; eassumption.
      * prep_merge. apply TReduce_mergevl; [eassumption | proj_IH_comp IH Hsz | first [eassumption | constructor]].
      * prep_merge. apply TReduce_mergevr; [eassumption | proj_IH_comp IH Hsz | first [eassumption | constructor]].
    + (* mergevl *)
      dependent destruction HR1.
      * prep_merge. apply TReduce_mergevl; [eassumption | proj_IH_comp IH Hsz | first [eassumption | constructor]].
      * prep_merge. apply TReduce_mergevr; [eassumption | proj_IH_comp IH Hsz | first [eassumption | constructor]].
      * (* and *) proj_IH_same IH Hsz.
    + (* mergevr *)
      dependent destruction HR1.
      * prep_merge. apply TReduce_mergevl; [eassumption | proj_IH_comp IH Hsz | first [eassumption | constructor]].
      * prep_merge. apply TReduce_mergevr; [eassumption | proj_IH_comp IH Hsz | first [eassumption | constructor]].
      * (* and *) proj_IH_same IH Hsz.
    + (* and *)
      apply TReduce_and.
      * proj_IH_same IH Hsz.
      * proj_IH_same IH Hsz.
Qed.

(* ============================================================ *)
(* Coherence of reductions of a typable value                    *)
(* ============================================================ *)

Lemma reduce_coh : forall v B, value v -> Etyping nil v B ->
    forall A1 v1 A2 v2, TypedReduce v A1 v1 -> TypedReduce v A2 v2 ->
    consistencySpec v1 v2.
Proof.
  intros v B Hv Ht A1 v1 A2 v2 HR1 HR2 C x1 x2 Hx1 Hx2.
  assert (Hp1 : TypedReduce v C x1).
  { exact (reduce_proj_n (size_exp v + size_exp v1 + size_typ C) v B Hv Ht
             A1 v1 HR1 C x1 Hx1 (Nat.le_refl _)). }
  assert (Hp2 : TypedReduce v C x2).
  { exact (reduce_proj_n (size_exp v + size_exp v2 + size_typ C) v B Hv Ht
             A2 v2 HR2 C x2 Hx2 (Nat.le_refl _)). }
  exact (reduce_det_n (size_exp v + size_typ C) v B Hv Ht C (Nat.le_refl _) x1 x2 Hp1 Hp2).
Qed.

(* Reduction preserves typing. *)
Lemma reduce_typing : forall v A v',
    TypedReduce v A v' -> value v -> forall B, Etyping nil v B -> Etyping nil v' A.
Proof.
  intros v A v' H. induction H; intros Hv Bt Ht.
  - (* lit *) apply Etyp_lit. apply uniq_nil.
  - (* top *) apply Etyp_top. apply uniq_nil.
  - (* toparr *)
    apply Etyp_abs with (L := {}) (B := t_top).
    + intros x Hx. apply Etyp_top. apply uniq_cons; [apply uniq_nil | rewrite dom_nil; apply notin_empty_1].
    + apply S_top.
    + apply topLike_sub. auto.
  - (* arrow *)
    inversion Ht; subst.
    match goal with
    | Hpre : forall x : atom, x \notin ?L -> Etyping ((x, ?Aann) :: nil) (open_exp_wrt_exp ?e (e_var_f x)) ?Bbody,
      HsC : sub ?C0 ?Aann, HsB : sub ?Bbody ?B0 |- _ =>
        eapply Etyp_abs with (L := L) (B := Bbody);
        [ intros x Hx; exact (Hpre x Hx)
        | eassumption
        | eapply sub_trans; eassumption ]
    end.
  - (* mergevl *)
    destruct (value_merge_inv v1 v2 Hv) as [Hva Hvb].
    destruct (Etyping_merge_inv v1 v2 Bt Ht) as [B1 [B2 [He [Ht1 Ht2]]]].
    subst Bt. eapply IHTypedReduce. exact Hva. exact Ht1.
  - (* mergevr *)
    destruct (value_merge_inv v1 v2 Hv) as [Hva Hvb].
    destruct (Etyping_merge_inv v1 v2 Bt Ht) as [B1 [B2 [He [Ht1 Ht2]]]].
    subst Bt. eapply IHTypedReduce. exact Hvb. exact Ht2.
  - (* and *)
    eapply Etyp_mergev.
    + apply uniq_nil.
    + apply value_merge; [exact (TypedReduce_value v A v1 H) | exact (TypedReduce_value v B v2 H0)].
    + eapply IHTypedReduce1. exact Hv. exact Ht.
    + eapply IHTypedReduce2. exact Hv. exact Ht.
    + exact (reduce_coh v Bt Hv Ht A v1 B v2 H H0).
Qed.

(* ============================================================ *)
(* Totality: a typable value reduces at every supertype of its type *)
(* ============================================================ *)

Lemma total_lit : forall i A, sub t_int A -> exists v', TypedReduce (e_lit i) A v'.
Proof.
  intros i A H. remember t_int as S eqn:ES. revert i ES.
  induction H; intros i0 ES.
  - exists (e_lit i0). apply TReduce_lit.
  - exists e_top. apply TReduce_top. constructor.
  - exists (e_abs t_top e_top B2). apply TReduce_toparr. constructor.
    apply sub_top_iff. auto.
  - inversion ES.
  - inversion ES.
  - inversion ES.
  - destruct (IHsub1 i0 ES) as [v1 H1].
    destruct (IHsub2 i0 ES) as [v2 H2].
    exists (e_merge v1 v2). apply TReduce_and; auto.
Qed.

Lemma total_top : forall A, sub t_top A -> exists v', TypedReduce e_top A v'.
Proof.
  intros A H. apply sub_top_iff in H.
  exists (canon A). apply reduce_total; [exact H | constructor].
Qed.

Lemma total_abs : forall A0 e D,
    lc_exp (e_abs A0 e D) -> forall C0, sub C0 A0 ->
    forall A, sub (t_arrow C0 D) A -> exists v', TypedReduce (e_abs A0 e D) A v'.
Proof.
  intros A0 e D Hlc C0 HsC A Hsub. revert C0 HsC Hsub.
  induction A; intros C0 HsC Hsub.
  - (* int *) dependent destruction Hsub.
  - (* top *) exists e_top. apply TReduce_top; auto.
  - (* arrow A1 A2 *)
    destruct (topLike_dec A2) as [Htl|Hntl].
    + exists (e_abs t_top e_top A2). apply TReduce_toparr; auto.
    + dependent destruction Hsub.
      * exfalso. apply Hntl. apply sub_top_iff. eassumption.
      * exists (e_abs A0 e A2).
        eapply TReduce_arrow; [exact Hlc | exact Hntl | eapply sub_trans; eassumption | eassumption].
  - (* and A1 A2 *)
    dependent destruction Hsub.
    assert (Hp1 : sub (t_arrow C0 D) A1) by eassumption.
    assert (Hp2 : sub (t_arrow C0 D) A2) by eassumption.
    destruct (IHA1 C0 HsC Hp1) as [v1 H1].
    destruct (IHA2 C0 HsC Hp2) as [v2 H2].
    exists (e_merge v1 v2). apply TReduce_and; auto.
Qed.

Lemma reduce_total_sub : forall n v B,
    value v -> Etyping nil v B ->
    forall A, sub B A -> size_exp v + size_typ A <= n -> exists v', TypedReduce v A v'.
Proof.
  intros n. induction n as [|n IH]; intros v B Hv Ht A Hsub Hsz.
  - exfalso. pose (size_exp_pos v). pose (size_typ_pos A). lia.
  - destruct Hv as [| i | A0 e D0 Hlc | v1 v2 Hv1 Hv2].
    + (* top *) apply Etyping_top_inv in Ht. subst B. apply total_top. exact Hsub.
    + (* lit *) apply Etyping_lit_inv in Ht. subst B. apply total_lit. exact Hsub.
    + (* abs *)
      destruct (Etyping_abs_inv A0 e D0 B Ht) as [C0 [He HsC0]].
      subst B. eapply total_abs; [exact Hlc | exact HsC0 | exact Hsub].
    + (* merge *)
      destruct (Etyping_merge_inv v1 v2 B Ht) as [B1 [B2 [He [Ht1 Ht2]]]].
      subst B.
      destruct A as [| | A1 A2 | A1 A2].
      * (* int *)
        dependent destruction Hsub.
        { (* S_andl1 *)
           assert (Hpa : sub B1 t_int) by eassumption.
           destruct (IH v1 B1 Hv1 Ht1 t_int Hpa ltac:(simpl in Hsz; simpl; lia)) as [v' Hr].
           exists v'. apply TReduce_mergevl; [apply value_lc; exact Hv2 | exact Hr | constructor]. }
        { (* S_andl2 *)
           assert (Hpa : sub B2 t_int) by eassumption.
           destruct (IH v2 B2 Hv2 Ht2 t_int Hpa ltac:(simpl in Hsz; simpl; lia)) as [v' Hr].
           exists v'. apply TReduce_mergevr; [apply value_lc; exact Hv1 | exact Hr | constructor]. }
      * (* top *)
        dependent destruction Hsub.
        all: exists (canon t_top); apply reduce_total; [constructor | apply value_lc; apply value_merge; auto].
      * (* arrow *)
        destruct (topLike_dec A2) as [Htl|Hntl].
        -- exists (canon (t_arrow A1 A2)). apply reduce_total.
           ++ apply TL_arr. auto.
           ++ apply value_lc. apply value_merge; auto.
        -- dependent destruction Hsub.
           ++ (* S_toparr *) exfalso. apply Hntl. apply sub_top_iff. eassumption.
           ++ (* S_andl1 *)
              assert (Hpa : sub B1 (t_arrow A1 A2)) by eassumption.
              destruct (IH v1 B1 Hv1 Ht1 (t_arrow A1 A2) Hpa ltac:(simpl in Hsz; simpl; lia)) as [v' Hr].
              exists v'. apply TReduce_mergevl; [apply value_lc; exact Hv2 | exact Hr | constructor].
           ++ (* S_andl2 *)
              assert (Hpa : sub B2 (t_arrow A1 A2)) by eassumption.
              destruct (IH v2 B2 Hv2 Ht2 (t_arrow A1 A2) Hpa ltac:(simpl in Hsz; simpl; lia)) as [v' Hr].
              exists v'. apply TReduce_mergevr; [apply value_lc; exact Hv1 | exact Hr | constructor].
      * (* and *)
        dependent destruction Hsub.
        -- (* S_andl1 *)
           assert (Hp : sub B1 (t_and A1 A2)) by eassumption.
           apply sub_and_proj in Hp. destruct Hp as [Hpa Hpb].
           destruct (IH (e_merge v1 v2) (t_and B1 B2) (value_merge v1 v2 Hv1 Hv2) Ht A1
                       (S_andl1 B1 B2 A1 Hpa) ltac:(simpl in Hsz; simpl; lia)) as [u1 Hu1].
           destruct (IH (e_merge v1 v2) (t_and B1 B2) (value_merge v1 v2 Hv1 Hv2) Ht A2
                       (S_andl1 B1 B2 A2 Hpb) ltac:(simpl in Hsz; simpl; lia)) as [u2 Hu2].
           exists (e_merge u1 u2). apply TReduce_and; auto.
        -- (* S_andl2 *)
           assert (Hp : sub B2 (t_and A1 A2)) by eassumption.
           apply sub_and_proj in Hp. destruct Hp as [Hpa Hpb].
           destruct (IH (e_merge v1 v2) (t_and B1 B2) (value_merge v1 v2 Hv1 Hv2) Ht A1
                       (S_andl2 B1 B2 A1 Hpa) ltac:(simpl in Hsz; simpl; lia)) as [u1 Hu1].
           destruct (IH (e_merge v1 v2) (t_and B1 B2) (value_merge v1 v2 Hv1 Hv2) Ht A2
                       (S_andl2 B1 B2 A2 Hpb) ltac:(simpl in Hsz; simpl; lia)) as [u2 Hu2].
           exists (e_merge u1 u2). apply TReduce_and; auto.
        -- (* S_andr *)
           assert (Hpa : sub (t_and B1 B2) A1) by eassumption.
           assert (Hpb : sub (t_and B1 B2) A2) by eassumption.
           destruct (IH (e_merge v1 v2) (t_and B1 B2) (value_merge v1 v2 Hv1 Hv2) Ht A1 Hpa
                       ltac:(simpl in Hsz; simpl; lia)) as [v1' Hr1].
           destruct (IH (e_merge v1 v2) (t_and B1 B2) (value_merge v1 v2 Hv1 Hv2) Ht A2 Hpb
                       ltac:(simpl in Hsz; simpl; lia)) as [v2' Hr2].
           exists (e_merge v1' v2'). apply TReduce_and; auto.
Qed.

(* ============================================================ *)
(* No-step for values, and progress                              *)
(* ============================================================ *)

Lemma value_no_step : forall v v', value v -> step v v' -> False.
Proof.
  intros v v' Hv. revert v'.
  induction Hv as [| i | A e B Hlc | v1 v2 Hv1 IH1 Hv2 IH2]; intros v' Hs.
  - inversion Hs.
  - inversion Hs.
  - inversion Hs.
  - inversion Hs; subst.
    + eapply IH1. eassumption.
    + eapply IH2. eassumption.
Qed.

Lemma value_typing_abs : forall v A B,
    value v -> Etyping nil v (t_arrow A B) -> exists A0 e D, v = e_abs A0 e D.
Proof.
  intros v A B Hv Ht.
  destruct Hv as [| i | A0 e0 D0 Hlc | v1 v2 Hv1 Hv2].
  - inversion Ht.
  - inversion Ht.
  - exists A0, e0, D0. reflexivity.
  - inversion Ht.
Qed.

Lemma Etyping_var_inv : forall x A, Etyping nil (e_var_f x) A -> False.
Proof.
  intros x A H. inversion H; subst.
  apply (in_dom_nil x). eapply binds_dom. eassumption.
Qed.

Lemma Etyping_app_inv : forall e1 e2 A,
    Etyping nil (e_app e1 e2) A ->
    exists T, Etyping nil e2 T /\ Etyping nil e1 (t_arrow T A).
Proof.
  intros e1 e2 A H. inversion H; subst. eauto.
Qed.

Lemma Etyping_anno_inv : forall e At B,
    Etyping nil (e_anno e At) B ->
    B = At /\ exists C, Etyping nil e C /\ sub C At.
Proof.
  intros e At B H. inversion H; subst. split; [reflexivity|]. eauto.
Qed.

Lemma Etyping_fix_inv : forall e At B,
    Etyping nil (e_fixpoint e At) B ->
    B = At /\ exists L, forall x, x \notin L ->
      Etyping (cons (x, At) nil) (open_exp_wrt_exp e (e_var_f x)) At.
Proof.
  intros e At B H. inversion H; subst. split; [reflexivity|]. eauto.
Qed.

Lemma Etyping_abs_inv_full : forall A e D B,
    Etyping nil (e_abs A e D) B ->
    exists L C Body,
      B = t_arrow C D /\ sub C A /\
      (forall x, x \notin L -> Etyping (cons (x, A) nil) (open_exp_wrt_exp e (e_var_f x)) Body) /\
      sub Body D.
Proof.
  intros A e D B H. inversion H; subst.
  eexists. eexists. eexists. repeat split; eauto.
Qed.



(* ============================================================ *)
(* Inversion lemmas for step                                     *)
(* ============================================================ *)

Lemma step_app_inv : forall e1 e2 e',
    step (e_app e1 e2) e' ->
    (exists A0 e0 D v v', e1 = e_abs A0 e0 D /\ e2 = v /\
       e' = e_anno (open_exp_wrt_exp e0 v') D /\
       lc_exp (e_abs A0 e0 D) /\ value v /\ TypedReduce v A0 v')
    \/ (exists e1', lc_exp e2 /\ step e1 e1' /\ e' = e_app e1' e2)
    \/ (value e1 /\ exists e2', step e2 e2' /\ e' = e_app e1 e2').
Proof.
  intros e1 e2 e' H. inversion H; subst.
  - left. eauto 20.
  - right; left. eauto.
  - right; right. eauto.
Qed.

Lemma step_merge_inv : forall e1 e2 e',
    step (e_merge e1 e2) e' ->
    (lc_exp e2 /\ exists e1', step e1 e1' /\ e' = e_merge e1' e2)
    \/ (value e1 /\ exists e2', step e2 e2' /\ e' = e_merge e1 e2').
Proof.
  intros e1 e2 e' H. inversion H; subst.
  - left. eauto.
  - right. eauto.
Qed.

Lemma step_anno_inv : forall e At e',
    step (e_anno e At) e' ->
    (value e /\ exists v', TypedReduce e At v' /\ e' = v')
    \/ (exists e0, step e e0 /\ e' = e_anno e0 At).
Proof.
  intros e At e' H. inversion H; subst.
  - left. eauto.
  - right. eauto.
Qed.

Lemma step_fix_inv : forall e At e',
    step (e_fixpoint e At) e' ->
    lc_exp (e_fixpoint e At) /\ e' = open_exp_wrt_exp e (e_fixpoint e At).
Proof.
  intros e At e' H. inversion H; subst. auto.
Qed.

Lemma step_top_false : forall e', step e_top e' -> False.
Proof. intros e' H. inversion H. Qed.

Lemma step_lit_false : forall i e', step (e_lit i) e' -> False.
Proof. intros i e' H. inversion H. Qed.

Lemma step_abs_false : forall A e D e', step (e_abs A e D) e' -> False.
Proof. intros A e D e' H. inversion H. Qed.

Lemma step_var_b_false : forall n e', step (e_var_b n) e' -> False.
Proof. intros n e' H. inversion H. Qed.

Lemma step_var_f_false : forall x e', step (e_var_f x) e' -> False.
Proof. intros x e' H. inversion H. Qed.

Lemma Etyping_merge_inv3 : forall e1 e2 B,
    Etyping nil (e_merge e1 e2) B ->
    exists A1 A2, B = t_and A1 A2 /\ Etyping nil e1 A1 /\ Etyping nil e2 A2 /\
      (disjointSpec A1 A2 \/ (value (e_merge e1 e2) /\ consistencySpec e1 e2)).
Proof.
  intros e1 e2 B H. inversion H; subst.
  - exists A, B0. repeat split; eauto.
  - exists A, B0. repeat split; eauto.
Qed.

Theorem preservation : forall e e' A,
    Etyping nil e A ->
    step e e' ->
    Etyping nil e' A.
Proof.
  intros e e' A Ht Hs. revert e' A Ht Hs.
  induction e as [n | x | | i | Aa ea IHab Db | ef IHeb Af
                  | e1 IHe1 e2 IHe2 | e1 IHe1 e2 IHe2 | en IHen An];
    intros e' A Ht Hs.
  - (* e_var_b *) inversion Ht.
  - (* e_var_f *) exfalso. eapply Etyping_var_inv. exact Ht.
  - (* e_top *) exfalso. eapply step_top_false. exact Hs.
  - (* e_lit *) exfalso. eapply step_lit_false. exact Hs.
  - (* e_abs *) exfalso. eapply step_abs_false. exact Hs.
  - (* e_fixpoint *)
    destruct (Etyping_fix_inv ef Af A Ht) as [Heq [L Hpre]].
    subst A.
    destruct (step_fix_inv ef Af e' Hs) as [Hlc Heq'].
    subst e'.
    assert (Hfix : Etyping nil (e_fixpoint ef Af) Af).
    { eapply Etyp_fix. exact Hpre. }
    eapply typing_open.
    + exact Hpre.
    + exact (typing_lc nil (e_fixpoint ef Af) Af Hfix).
    + exact Hfix.
  - (* e_app *)
    destruct (Etyping_app_inv e1 e2 A Ht) as [T [H2 H1]].
    destruct (step_app_inv e1 e2 e' Hs) as
      [[A0 [e0 [D [v [v' [Heq1 [Heq2 [Heq' [Hlc [Hval Hred]]]]]]]]]]
      | [[e1' [Hlc2 [Hs1 Heq']]] | [Hv1 [e2' [Hs2 Heq']]]]].
    + (* beta *)
      subst e1. subst e2. subst e'.
      destruct (Etyping_abs_inv_full A0 e0 D (t_arrow T A) H1) as
        [L [C [Body [Heq3 [HsubCA0 [Hpre HsubBodyD]]]]]].
      injection Heq3 as HT HD. subst T. subst A.
      assert (Hv' : Etyping nil v' A0).
      { exact (reduce_typing v A0 v' Hred Hval C H2). }
      assert (Hopen : Etyping nil (open_exp_wrt_exp e0 v') Body).
      { eapply typing_open.
        - exact Hpre.
        - exact (TypedReduce_lc v A0 v' Hred).
        - exact Hv'. }
      eapply Etyp_anno.
      * exact Hopen.
      * exact HsubBodyD.
    + (* appl *)
      subst e'.
      eapply Etyp_app.
      * exact H2.
      * exact (IHe1 e1' (t_arrow T A) H1 Hs1).
    + (* appr *)
      subst e'.
      eapply Etyp_app.
      * exact (IHe2 e2' T H2 Hs2).
      * exact H1.
  - (* e_merge *)
    destruct (Etyping_merge_inv3 e1 e2 A Ht) as
      [T1 [T2 [Heq [H1 [H2 Hcase]]]]].
    subst A.
    destruct (step_merge_inv e1 e2 e' Hs) as
      [[Hlc2 [e1' [Hs1 Heq']]] | [Hv1 [e2' [Hs2 Heq']]]].
    + (* mergel *)
      subst e'.
      destruct Hcase as [Hdisj | [Hval Hcons]].
      * eapply Etyp_merge.
        -- exact (IHe1 e1' T1 H1 Hs1).
        -- exact H2.
        -- exact Hdisj.
      * destruct (value_merge_inv e1 e2 Hval) as [Hv1' Hv2'].
        exfalso. eapply value_no_step; [exact Hv1' | exact Hs1].
    + (* merger *)
      subst e'.
      destruct Hcase as [Hdisj | [Hval Hcons]].
      * eapply Etyp_merge.
        -- exact H1.
        -- exact (IHe2 e2' T2 H2 Hs2).
        -- exact Hdisj.
      * destruct (value_merge_inv e1 e2 Hval) as [Hv1' Hv2'].
        exfalso. eapply value_no_step; [exact Hv2' | exact Hs2].
  - (* e_anno *)
    destruct (Etyping_anno_inv en An A Ht) as [Heq [B [H0 HsubBA]]].
    subst A.
    destruct (step_anno_inv en An e' Hs) as
      [[Hv [v' [Hred Heq']]] | [e0' [Hs0 Heq']]].
    + subst e'. exact (reduce_typing en An v' Hred Hv B H0).
    + subst e'.
      eapply Etyp_anno.
      * exact (IHen e0' B H0 Hs0).
      * exact HsubBA.
Qed.

Theorem progress : forall e A,
    Etyping nil e A ->
    value e \/ exists e', step e e'.
Proof.
  intros e A Ht. revert A Ht.
  induction e as [n | x | | i | Aa ea IHab Db | ef IHeb Af
                  | e1 IHe1 e2 IHe2 | e1 IHe1 e2 IHe2 | en IHen An];
    intros A Ht.
  - (* e_var_b *) inversion Ht.
  - (* e_var_f *) exfalso. eapply Etyping_var_inv. exact Ht.
  - (* e_top *) left. constructor.
  - (* e_lit *) left. constructor.
  - (* e_abs *) left. apply value_anno. apply typing_lc in Ht. exact Ht.
  - (* e_fixpoint *) right. exists (open_exp_wrt_exp ef (e_fixpoint ef Af)).
    apply Step_fix. apply typing_lc in Ht. exact Ht.
  - (* e_app *)
    destruct (Etyping_app_inv e1 e2 A Ht) as [T [H2 H1]].
    destruct (IHe1 (t_arrow T A) H1) as [Hv1 | [e1' Hs1]].
    + destruct (IHe2 T H2) as [Hv2 | [e2' Hs2]].
      * (* both values: beta *)
        destruct (value_typing_abs e1 T A Hv1 H1) as [A1 [e1b [D1 Heq]]].
        subst e1.
        destruct (Etyping_abs_inv A1 e1b D1 (t_arrow T A) H1) as [C [Heq2 HsubTA1]].
        injection Heq2 as HT HD. subst T. subst A.
        destruct (reduce_total_sub (size_exp e2 + size_typ A1) e2 C Hv2 H2 A1 HsubTA1
                    ltac:(lia)) as [v' Hred].
        right. exists (e_anno (open_exp_wrt_exp e1b v') D1).
        eapply Step_beta.
        -- apply value_abs_lc in Hv1. exact Hv1.
        -- exact Hv2.
        -- exact Hred.
      * (* e2 steps *) right. exists (e_app e1 e2').
        apply Step_appr; [exact Hv1 | exact Hs2].
    + (* e1 steps *) right. exists (e_app e1' e2).
      apply Step_appl; [exact (typing_lc nil e2 T H2) | exact Hs1].
  - (* e_merge *)
    destruct (Etyping_merge_inv2 e1 e2 A Ht) as [T1 [T2 [Heq [H1 [H2 _]]]]].
    subst A.
    destruct (IHe1 T1 H1) as [Hv1 | [e1' Hs1]].
    + destruct (IHe2 T2 H2) as [Hv2 | [e2' Hs2]].
      * left. apply value_merge; assumption.
      * right. exists (e_merge e1 e2'). apply Step_merger; assumption.
    + right. exists (e_merge e1' e2).
      apply Step_mergel; [exact (typing_lc nil e2 T2 H2) | exact Hs1].
  - (* e_anno *)
    destruct (Etyping_anno_inv en An A Ht) as [Heq [T [H0 Hsub]]].
    subst A.
    destruct (IHen T H0) as [Hv | [e' Hs]].
    + destruct (reduce_total_sub (size_exp en + size_typ An) en T Hv H0 An Hsub
                  ltac:(lia)) as [v' Hred].
      right. exists v'. apply Step_annov; assumption.
    + right. exists (e_anno e' An). apply Step_anno; assumption.
Qed.
