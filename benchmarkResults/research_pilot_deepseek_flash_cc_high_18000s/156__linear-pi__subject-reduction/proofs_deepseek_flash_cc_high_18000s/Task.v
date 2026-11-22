Require Import Bool List Lia PeanoNat.
From Stdlib Require Import Sorting.Permutation.
Require Import pairEq operations header.
Require Import pi_syntax type_system type_system_rules semantics.

Section Utilities.

Lemma pair_eq_true : forall (a b : name * name), pair_eq a b = true <-> a = b.
Proof.
  intros [a1 a2] [b1 b2]. unfold pair_eq. simpl.
  rewrite andb_true_iff, !Nat.eqb_eq. intuition congruence.
Qed.

Lemma pair_eq_false : forall (a b : name * name), pair_eq a b = false <-> a <> b.
Proof.
  intros a b. destruct (pair_eq a b) eqn:E.
  - split; [discriminate|]. intro H; exfalso; apply H; apply pair_eq_true; exact E.
  - split.
    + intros _ Heq. apply pair_eq_true in Heq. rewrite Heq in E. discriminate.
    + intros _; reflexivity.
Qed.

Lemma pair_eq_refl : forall a, pair_eq a a = true.
Proof. intros []; unfold pair_eq; simpl; rewrite !Nat.eqb_refl; auto. Qed.

Lemma pair_eq_neq : forall a b, a <> b -> pair_eq a b = false.
Proof. intros a b H. apply pair_eq_false. auto. Qed.

Lemma in_dom_entry : forall g n f t, In ((n,f),t) g -> In n (domain g).
Proof.
  intros g. induction g as [|h tl IH].
  - simpl. auto.
  - destruct h as [[x fx] tx]. intros n f t H. simpl in *.
    destruct H as [Heq|Hin].
    + inversion Heq; subst. simpl. left; auto.
    + simpl. right. exact (IH n f t Hin).
Qed.

Lemma removeEntry_notin : forall y g, ~ In y (domain g) -> removeEntry y g = g.
Proof.
  intros y g. induction g as [|h tl IH].
  - simpl. reflexivity.
  - destruct h as [[x f] t]. simpl. intro H.
    destruct (pair_eq x y) eqn:E.
    + apply pair_eq_true in E; subst. exfalso; apply H. simpl. left; auto.
    + f_equal. apply IH. intro Hc. apply H. simpl; auto.
Qed.

Lemma in_removeEntry_elim : forall y g n f t,
    In ((n,f),t) (removeEntry y g) -> In ((n,f),t) g.
Proof.
  intros y g. induction g as [|h tl IH].
  - simpl. intros n f t H. exact H.
  - destruct h as [[z fz] tz]. simpl. intros n f t H.
    destruct (pair_eq z y) eqn:E.
    + simpl. right; exact H.
    + simpl in H. destruct H as [Heq|Hin].
      * left; exact Heq.
      * right; apply IH; exact Hin.
Qed.

Lemma in_removeEntry_intro : forall y g n f t,
    y <> n -> In ((n,f),t) g -> In ((n,f),t) (removeEntry y g).
Proof.
  intros y g. induction g as [|h tl IH].
  - simpl. auto.
  - destruct h as [[z fz] tz]. simpl. intros n f t Hne Hin.
    destruct Hin as [Heq|Hin].
    + inversion Heq; subst. destruct (pair_eq n y) eqn:E.
      * apply pair_eq_true in E. exfalso. apply Hne. symmetry. exact E.
      * simpl. left; reflexivity.
    + destruct (pair_eq z y) eqn:E.
      * exact Hin.
      * simpl. right. apply IH; auto.
Qed.

Lemma removeEntry_cons_eq : forall y f t tl,
    removeEntry y (((y,f),t) :: tl) = tl.
Proof. intros. simpl. rewrite pair_eq_refl. reflexivity. Qed.

Lemma removeEntry_cons_neq : forall z y f t tl, z <> y ->
    removeEntry y (((z,f),t) :: tl) = ((z,f),t) :: removeEntry y tl.
Proof.
  intros. simpl. rewrite (pair_eq_neq z y); [reflexivity|auto].
Qed.

Lemma removeEntry_removeEntry_other : forall x y g, x <> y ->
    removeEntry x (removeEntry y g) = removeEntry y (removeEntry x g).
Proof.
  intros x y g Hne. induction g as [|h tl IH].
  - reflexivity.
  - destruct h as [[z f] t].
    destruct (pair_eq z y) eqn:Ey.
    + apply pair_eq_true in Ey. subst z.
      rewrite removeEntry_cons_eq.
      rewrite (removeEntry_cons_neq y x f t tl (fun H => Hne (eq_sym H))).
      rewrite removeEntry_cons_eq. reflexivity.
    + assert (Hzy : z <> y) by (apply pair_eq_false; exact Ey).
      destruct (pair_eq z x) eqn:Ex.
      * apply pair_eq_true in Ex. subst z.
        rewrite (removeEntry_cons_neq x y f t tl Hne).
        rewrite removeEntry_cons_eq.
        rewrite removeEntry_cons_eq. reflexivity.
      * assert (Hzx : z <> x) by (apply pair_eq_false; exact Ex).
        rewrite (removeEntry_cons_neq z y f t tl Hzy).
        rewrite (removeEntry_cons_neq z x f t tl Hzx).
        rewrite (removeEntry_cons_neq z x f t (removeEntry y tl) Hzx).
        rewrite (removeEntry_cons_neq z y f t (removeEntry x tl) Hzy).
        f_equal. apply IH; auto.
Qed.

Lemma domain_removeEntry_sub : forall y g x,
    In x (domain (removeEntry y g)) -> In x (domain g).
Proof.
  intros y g. induction g as [|h tl IH].
  - simpl. auto.
  - destruct h as [[z fz] tz]. simpl. intros x H.
    destruct (pair_eq z y) eqn:E; simpl in *.
    + auto.
    + destruct H as [->|H]; [left|right]; auto.
Qed.

Lemma domain_removeEntry_neq : forall y g x,
    x <> y -> In x (domain g) -> In x (domain (removeEntry y g)).
Proof.
  intros y g. induction g as [|h tl IH].
  - simpl. auto.
  - destruct h as [[z fz] tz]. simpl. intros x Hne Hin.
    destruct Hin as [Heq|Hin].
    + destruct (pair_eq z y) eqn:E.
      * apply pair_eq_true in E. exfalso. apply Hne. rewrite <- Heq. exact E.
      * simpl. left. exact Heq.
    + destruct (pair_eq z y) eqn:E.
      * exact Hin.
      * simpl. destruct (nat_pair_eq_dec z x) as [Heq2|Hne2].
        -- left; exact Heq2.
        -- right. apply IH; auto.
Qed.

Lemma NoDup_domain_removeEntry : forall y g,
    NoDup (domain g) -> NoDup (domain (removeEntry y g)).
Proof.
  intros y g. induction g as [|h tl IH].
  - simpl. auto.
  - destruct h as [[z fz] tz]. simpl. intro Hnd.
    apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnot Hnd].
    destruct (pair_eq z y) eqn:E.
    + apply pair_eq_true in E; subst; auto.
    + apply NoDup_cons_iff. split.
      * intro Hc. apply Hnot. eapply domain_removeEntry_sub; eauto.
      * apply IH; auto.
Qed.

Lemma NoDup_removeEntry_still : forall y g,
    NoDup (domain g) -> In y (domain g) -> ~ In y (domain (removeEntry y g)).
Proof.
  intros y g. induction g as [|h tl IH].
  - simpl. auto.
  - destruct h as [[z fz] tz]. simpl. intros Hnd Hin.
    apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnot Hnd].
    destruct Hin as [Heq|Hin].
    + subst. simpl. rewrite pair_eq_refl. intro Hc; exact (Hnot Hc).
    + simpl. destruct (pair_eq z y) eqn:E.
      * apply pair_eq_true in E; subst. intro Hc; exact (Hnot Hc).
      * intro Hc. simpl in Hc. destruct Hc as [Heq|Hc].
        -- apply pair_eq_false in E; contradiction.
        -- exact (IH Hnd Hin Hc).
Qed.

Lemma nodup_entry_unique : forall g n1 f1 t1 n2 f2 t2,
    NoDup (domain g) ->
    In ((n1,f1),t1) g -> In ((n2,f2),t2) g -> n1 = n2 ->
    ((n1,f1),t1) = ((n2,f2),t2).
Proof.
  intros g. induction g as [|h tl IH].
  - simpl. intros; contradiction.
  - destruct h as [[a fa] ta]. simpl. intros n1 f1 t1 n2 f2 t2 Hnd H1 H2 Hn.
    apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnot Hnd].
    destruct H1 as [E1|I1]; destruct H2 as [E2|I2].
    + rewrite <- E1, <- E2. reflexivity.
    + exfalso. apply Hnot.
      assert (Ha : a = n2) by congruence.
      rewrite Ha. exact (in_dom_entry tl n2 f2 t2 I2).
    + exfalso. apply Hnot.
      assert (Ha : a = n1) by congruence.
      rewrite Ha. exact (in_dom_entry tl n1 f1 t1 I1).
    + apply (IH n1 f1 t1 n2 f2 t2); auto.
Qed.

Lemma isMap_nodup : forall g, NoDup (domain g) -> isMap g.
Proof.
  intros g Hnd. unfold isMap. intros x f1 t1 f2 t2 [H1 H2].
  assert (H := nodup_entry_unique g x f1 t1 x f2 t2 Hnd H1 H2 eq_refl).
  inversion H. auto.
Qed.

Lemma isMap_removeEntry : forall y g, isMap g -> isMap (removeEntry y g).
Proof.
  intros y g Hm. unfold isMap in *. intros x f1 t1 f2 t2 [H1 H2].
  apply (Hm x f1 t1 f2 t2). split.
  - exact (in_removeEntry_elim y g x f1 t1 H1).
  - exact (in_removeEntry_elim y g x f2 t2 H2).
Qed.

Lemma isMap_sub : forall g1 g2, isMap g2 ->
    (forall x f t, In ((x,f),t) g1 -> In ((x,f),t) g2) -> isMap g1.
Proof.
  intros g1 g2 Hm Hsub. unfold isMap in *. intros x f1 t1 f2 t2 [H1 H2].
  apply (Hm x f1 t1 f2 t2). split; auto.
Qed.

Fixpoint lookup (n : name * name) (g : typeEnv) : option (flag * piType) :=
  match g with
  | nil => None
  | (x,f,t) :: tl => if pair_eq x n then Some (f,t) else lookup n tl
  end.

Lemma lookup_Some_In : forall n g f t, lookup n g = Some (f,t) -> In ((n,f),t) g.
Proof.
  intros n g. induction g as [|h tl IH].
  - simpl. intros f t H; discriminate.
  - destruct h as [[x fx] tx]. simpl. intros f t H.
    destruct (pair_eq x n) eqn:E.
    + inversion H; subst. apply pair_eq_true in E; subst. simpl. left; auto.
    + simpl. right. apply IH; exact H.
Qed.

Lemma lookup_None_notin : forall n g, lookup n g = None -> ~ In n (domain g).
Proof.
  intros n g. induction g as [|h tl IH].
  - simpl. auto.
  - destruct h as [[x fx] tx]. simpl. intro H.
    destruct (pair_eq x n) eqn:E.
    + discriminate.
    + simpl. intros [Heq|Hin].
      * apply pair_eq_false in E; contradiction.
      * apply IH; auto.
Qed.

Lemma In_lookup_Some : forall n g, In n (domain g) -> exists f t, lookup n g = Some (f,t).
Proof.
  intros n g. induction g as [|h tl IH].
  - intros H. simpl in H. exfalso; exact H.
  - destruct h as [[x fx] tx]. simpl. intros [Heq|Hin].
    + rewrite <- Heq. simpl. rewrite pair_eq_refl. eauto.
    + destruct (pair_eq x n) eqn:E.
      * exists fx, tx; auto.
      * apply IH; auto.
Qed.

Lemma lookup_isMap : forall g, isMap g -> forall n f1 t1 f2 t2,
    lookup n g = Some (f1,t1) -> lookup n g = Some (f2,t2) -> f1=f2 /\ t1=t2.
Proof.
  intros g Him n f1 t1 f2 t2 H1 H2.
  apply (Him n f1 t1 f2 t2). split.
  - apply lookup_Some_In in H1; exact H1.
  - apply lookup_Some_In in H2; exact H2.
Qed.

Lemma length_removeEntry : forall n g, In n (domain g) -> length (removeEntry n g) = length g - 1.
Proof.
  intros n g. induction g as [|h tl IH].
  - simpl. intros H; destruct H.
  - destruct h as [[x f] t]. simpl. intros H.
    destruct (pair_eq x n) eqn:E.
    + simpl. lia.
    + simpl in H. destruct H as [Heq|Hin].
      * apply pair_eq_false in E. contradiction.
      * assert (Hpos : length tl >= 1) by (destruct tl as [|h2 tl2]; simpl in *; [contradiction| simpl; lia]).
        specialize (IH Hin). simpl. rewrite IH. lia.
Qed.

End Utilities.

Section ConsSpec.

Definition consumable (t : piType) : Prop :=
  t = Top \/ (exists p t', t = Chan un p t') \/ (exists t', t = Chan lin empty t').

Lemma consumable_top : consumable Top.
Proof. left; auto. Qed.

Lemma consumable_un : forall p t, consumable (Chan un p t).
Proof. intros; right; left; eauto. Qed.

Lemma consumable_lin_empty : forall t, consumable (Chan lin empty t).
Proof. intros; right; right; eauto. Qed.

Lemma typeOf_inv : forall g n t, typeOf g n t -> exists f, In ((n,f),t) g.
Proof. intros g n t H. destruct H as [g' n' f t' Hin]. exists f. exact Hin. Qed.

Lemma flagOf_inv : forall g n f, flagOf g n f -> exists t, In ((n,f),t) g.
Proof. intros g n f H. destruct H as [g' n' f' t' Hin]. exists t'. exact Hin. Qed.

Lemma cons_entry : forall g pf, cons g pf ->
    forall n f t, In ((n,f),t) g -> consumable t.
Proof.
  intros g pf H.
  induction H as [g pf Eg | g pf n pf' Ht Hc IH | g pf n p t pf' Ht Hc IH | g pf n t pf' Ht Hc IH].
  - subst; intros; contradiction.
  - intros n0 f t0 Hin.
    destruct (pair_eq n0 n) eqn:E.
    + apply pair_eq_true in E; subst n0.
      destruct (typeOf_inv g n Top Ht) as [f0 Htop].
      assert (Him : isMap g) by exact pf.
      unfold isMap in Him.
      destruct (Him n f0 Top f t0 (conj Htop Hin)) as [_ Ht'].
      subst t0. apply consumable_top.
    + apply (IH n0 f t0). apply (in_removeEntry_intro n g n0 f t0).
      * intro Heq. apply pair_eq_false in E. apply E. symmetry. exact Heq.
      * exact Hin.
  - intros n0 f t0 Hin.
    destruct (pair_eq n0 n) eqn:E.
    + apply pair_eq_true in E; subst n0.
      destruct (typeOf_inv g n (Chan un p t) Ht) as [f0 Htop].
      assert (Him : isMap g) by exact pf.
      unfold isMap in Him.
      destruct (Him n f0 (Chan un p t) f t0 (conj Htop Hin)) as [_ Ht'].
      subst t0. apply consumable_un.
    + apply (IH n0 f t0). apply (in_removeEntry_intro n g n0 f t0).
      * intro Heq. apply pair_eq_false in E. apply E. symmetry. exact Heq.
      * exact Hin.
  - intros n0 f t0 Hin.
    destruct (pair_eq n0 n) eqn:E.
    + apply pair_eq_true in E; subst n0.
      destruct (typeOf_inv g n (Chan lin empty t) Ht) as [f0 Htop].
      assert (Him : isMap g) by exact pf.
      unfold isMap in Him.
      destruct (Him n f0 (Chan lin empty t) f t0 (conj Htop Hin)) as [_ Ht'].
      subst t0. apply consumable_lin_empty.
    + apply (IH n0 f t0). apply (in_removeEntry_intro n g n0 f t0).
      * intro Heq. apply pair_eq_false in E. apply E. symmetry. exact Heq.
      * exact Hin.
Qed.

Lemma entry_cons : forall g pf,
    (forall n f t, In ((n,f),t) g -> consumable t) -> cons g pf.
Proof.
  intros g. remember (length g) as k eqn:Ek. revert g Ek.
  induction k as [|k IH]; intros g Ek pf Hall.
  - destruct g as [|h tl].
    + apply Co_nil; auto.
    + simpl in Ek. discriminate.
  - destruct g as [|h tl].
    + apply Co_nil; auto.
    + destruct h as [[n f] t].
      pose proof (Hall n f t (or_introl eq_refl)) as Hc.
      assert (Hin : In n (domain (((n,f),t)::tl))) by (simpl; left; auto).
      assert (Hpf' : isMap (removeEntry n (((n,f),t)::tl))) by (apply isMap_removeEntry; exact pf).
      assert (Hlen : length (removeEntry n (((n,f),t)::tl)) = k).
      { rewrite length_removeEntry; [|exact Hin]. simpl in Ek. simpl. lia. }
      assert (Hall' : forall n0 f0 t0, In ((n0,f0),t0) (removeEntry n (((n,f),t)::tl)) -> consumable t0).
      { intros n0 f0 t0 H0. apply (Hall n0 f0 t0). apply in_removeEntry_elim with (y:=n). exact H0. }
      assert (Hrec : cons (removeEntry n (((n,f),t)::tl)) Hpf').
      { apply (IH (removeEntry n (((n,f),t)::tl)) (eq_sym Hlen) Hpf' Hall'). }
      destruct Hc as [Ht | [[p [t' Ht]] | [t' Ht]]].
      * subst t.
        assert (HTy : typeOf (((n,f),Top)::tl) n Top).
        { apply (T_Entry (((n,f),Top)::tl) n f Top). simpl; left; reflexivity. }
        exact (Co_top (((n,f),Top)::tl) pf n Hpf' HTy Hrec).
      * subst t.
        assert (HTy : typeOf (((n,f),Chan un p t')::tl) n (Chan un p t')).
        { apply (T_Entry (((n,f),Chan un p t')::tl) n f (Chan un p t')). simpl; left; reflexivity. }
        exact (Co_un (((n,f),Chan un p t')::tl) pf n p t' Hpf' HTy Hrec).
      * subst t.
        assert (HTy : typeOf (((n,f),Chan lin empty t')::tl) n (Chan lin empty t')).
        { apply (T_Entry (((n,f),Chan lin empty t')::tl) n f (Chan lin empty t')). simpl; left; reflexivity. }
        exact (Co_lin (((n,f),Chan lin empty t')::tl) pf n t' Hpf' HTy Hrec).
Qed.

Lemma cons_spec : forall g pf, cons g pf <-> (forall n f t, In ((n,f),t) g -> consumable t).
Proof.
  intros g pf. split.
  - apply cons_entry.
  - apply entry_cons.
Qed.


Lemma consumable_plus : forall t1 t t2, consumable t1 -> consumable t -> type_plus t1 t t2 -> consumable t2.
Proof.
  intros t1 t t2 H1 H2 Hp.
  destruct H1 as [-> | [[p1 [u1 ->]] | [u1 ->]]];
  destruct H2 as [-> | [[p2 [u2 ->]] | [u2 ->]]];
  inversion Hp; subst; simpl; auto using consumable_top, consumable_un, consumable_lin_empty.
  all: try (inversion H4; subst; auto using consumable_lin_empty).
Qed.

End ConsSpec.
Section Algebra.

Lemma pol_plus_det : forall p q r1 r2, pol_plus p q r1 -> pol_plus p q r2 -> r1=r2.
Proof. intros p q r1 r2 H1 H2. inversion H1; subst; inversion H2; subst; auto. Qed.

Lemma flag_plus_det : forall f g h1 h2, flag_plus f g h1 -> flag_plus f g h2 -> h1=h2.
Proof. intros f g h1 h2 H1 H2. inversion H1; subst; inversion H2; subst; auto. Qed.

Lemma pol_plus_sym : forall p q r, pol_plus p q r -> pol_plus q p r.
Proof. intros p q r H. inversion H; subst; eauto using pol_plus. Qed.

Lemma flag_plus_sym : forall f g h, flag_plus f g h -> flag_plus g f h.
Proof. intros f g h H. inversion H; subst; eauto using flag_plus. Qed.

Lemma pol_plus_assoc : forall a b c d e, pol_plus a b c -> pol_plus c d e ->
  exists f, pol_plus b d f /\ pol_plus a f e.
Proof. intros a b c d e H1 H2. inversion H1; subst; inversion H2; subst; eauto using pol_plus. Qed.

Lemma flag_plus_assoc : forall a b c d e, flag_plus a b c -> flag_plus c d e ->
  exists f, flag_plus b d f /\ flag_plus a f e.
Proof. intros a b c d e H1 H2. inversion H1; subst; inversion H2; subst; eauto using flag_plus. Qed.

Inductive ecomb : (flag*piType) -> (flag*piType) -> (flag*piType) -> Prop :=
| ec_top : forall f1 f2 f, flag_plus f1 f2 f -> ecomb (f1,Top) (f2,Top) (f,Top)
| ec_un : forall f1 f2 f p t, flag_plus f1 f2 f -> ecomb (f1,Chan un p t) (f2,Chan un p t) (f,Chan un p t)
| ec_lin : forall f1 f2 f p1 p2 p t, flag_plus f1 f2 f -> pol_plus p1 p2 p ->
      ecomb (f1,Chan lin p1 t) (f2,Chan lin p2 t) (f,Chan lin p t).

Lemma ecomb_det : forall a b c1 c2, ecomb a b c1 -> ecomb a b c2 -> c1=c2.
Proof.
  intros a b c1 c2 H1 H2.
  destruct a as [fa ta], b as [fb tb], c1 as [fc tc], c2 as [fd td].
  inversion H1; subst; inversion H2; subst; simpl; f_equal;
    eauto using flag_plus_det, pol_plus_det.
  try (f_equal; eauto using pol_plus_det).
Qed.

Lemma ecomb_sym : forall a b c, ecomb a b c -> ecomb b a c.
Proof.
  intros a b c H. destruct a as [fa ta], b as [fb tb], c as [fc tc].
  inversion H; subst; simpl; eauto using ecomb, pol_plus_sym, flag_plus_sym.
Qed.

Lemma ecomb_assoc : forall a b c d e, ecomb a b c -> ecomb c d e ->
  exists f, ecomb b d f /\ ecomb a f e.
Proof.
  intros a b c d e H1 H2.
  destruct a as [fa ta], b as [fb tb], c as [fc tc], d as [fd td], e as [fe te].
  inversion H1 as [fa' fb' fc' Hfab | fa' fb' fc' p t Hfab | fa' fb' fc' p1 p2 p t Hfab Hp]; subst.
  - inversion H2 as [fc2 fd' fe' Hfcd | fc2 fd' fe' pu tu Hfcd | fc2 fd' fe' q1 q2 q tq Hfcd Hpq]; subst; try discriminate.
    destruct (flag_plus_assoc fa fb fc fd fe Hfab Hfcd) as [fg [H5 H6]].
    exists (fg, Top). split; apply ec_top; assumption.
  - inversion H2 as [fc2 fd' fe' Hfcd | fc2 fd' fe' pu tu Hfcd | fc2 fd' fe' q1 q2 q tq Hfcd Hpq]; subst; try discriminate.
    destruct (flag_plus_assoc fa fb fc fd fe Hfab Hfcd) as [fg [H5 H6]].
    exists (fg, Chan un p t). split; apply ec_un; assumption.
  - inversion H2 as [fc2 fd' fe' Hfcd | fc2 fd' fe' pu tu Hfcd | fc2 fd' fe' q1 q2 q tq Hfcd Hpq]; subst; try discriminate.
    destruct (flag_plus_assoc fa fb fc fd fe Hfab Hfcd) as [fg [H5 H6]].
    destruct (pol_plus_assoc p1 p2 p q2 q Hp Hpq) as [pg [H7 H8]].
    exists (fg, Chan lin pg t). split; apply ec_lin; assumption.
Qed.

Lemma pol_cup_comm : forall p q, pol_cup p q = pol_cup q p.
Proof. intros p; destruct p; destruct q; simpl; auto. Qed.
Lemma pol_cup_assoc : forall p q r, pol_cup (pol_cup p q) r = pol_cup p (pol_cup q r).
Proof. intros p; destruct p; destruct q; destruct r; simpl; auto. Qed.
Lemma pol_cup_swap : forall a b c d,
  pol_cup (pol_cup a b) (pol_cup c d) = pol_cup (pol_cup a c) (pol_cup b d).
Proof. intros a; destruct a; destruct b; destruct c; destruct d; simpl; auto. Qed.
Lemma pol_plus_swap : forall a b ab c d cd ac bd t,
  pol_plus a b ab -> pol_plus c d cd -> pol_plus a c ac -> pol_plus b d bd -> pol_plus ac bd t ->
  pol_plus ab cd t.
Proof.
  intros a b ab c d cd ac bd t H1 H2 H3 H4 H5.
  inversion H1; subst; inversion H2; subst; inversion H3; subst; inversion H4; subst; inversion H5; subst;
    eauto using pol_plus.
Qed.
Lemma type_plus_swap : forall a b x y ab xy ax byc t2,
  type_plus a b ab -> type_plus x y xy ->
  type_plus ab xy t2 -> type_plus a x ax -> type_plus b y byc ->
  type_plus ax byc t2.
Proof.
  intros a b x y ab xy ax byc t2 H1 H2 H3 H4 H5.
  inversion H1; subst; inversion H2; subst; inversion H3; subst; inversion H4; subst; inversion H5; subst;
    eauto using type_plus, pol_plus_swap.
  rewrite pol_cup_swap. apply Tp_UnPlus.
Qed.

Lemma ecomb_third_top : forall f1 t1 f2 t2 f, ecomb (f1,t1) (f2,t2) (f,Top) -> t1=Top /\ t2=Top.
Proof. intros. inversion H; subst; auto. Qed.
Lemma ecomb_third_un : forall f1 t1 f2 t2 f p t,
  ecomb (f1,t1) (f2,t2) (f,Chan un p t) -> t1=Chan un p t /\ t2=Chan un p t.
Proof. intros. inversion H; subst; auto. Qed.
Lemma ecomb_third_lin : forall f1 t1 f2 t2 f p t,
  ecomb (f1,t1) (f2,t2) (f,Chan lin p t) ->
  exists p1 p2, t1=Chan lin p1 t /\ t2=Chan lin p2 t /\ pol_plus p1 p2 p.
Proof. intros. inversion H; subst. exists p1, p2. auto. Qed.
Lemma flag_plus_vis_result : forall f1 f2, flag_plus f1 f2 vis -> f1=vis /\ f2=vis.
Proof. intros. inversion H; auto. Qed.

Lemma pol_plus_exchange : forall q1 q2 q p1 p2 p r,
  pol_plus q1 q2 q -> pol_plus p1 p2 p -> pol_plus q p r ->
  exists r1 r2, pol_plus q1 p1 r1 /\ pol_plus q2 p2 r2 /\ pol_plus r1 r2 r.
Proof.
  intros q1 q2 q p1 p2 p r H1 H2 H3.
  inversion H1; subst; inversion H2; subst; inversion H3; subst;
    eauto using pol_plus.
Qed.
Lemma pol_cup_idem : forall p, pol_cup p p = p.
Proof. intros p; destruct p; simpl; auto. Qed.
Lemma type_plus_second_lin : forall t1 p t0 t2,
  type_plus t1 (Chan lin p t0) t2 ->
  exists p0 p4, t1 = Chan lin p0 t0 /\ t2 = Chan lin p4 t0 /\ pol_plus p0 p p4.
Proof. intros. inversion H; subst; eauto. Qed.
Lemma type_plus_second_un : forall t1 p t0 t2,
  type_plus t1 (Chan un p t0) t2 ->
  exists p0, t1 = Chan un p0 t0 /\ t2 = Chan un (pol_cup p0 p) t0.
Proof. intros. inversion H; subst; eauto. Qed.
Lemma type_plus_second_top : forall t1 t2, type_plus t1 Top t2 -> t1 = Top /\ t2 = Top.
Proof. intros. inversion H; subst; auto. Qed.

Lemma ecomb_flag_plus : forall f1 t1 f2 t2 f t, ecomb (f1,t1) (f2,t2) (f,t) -> flag_plus f1 f2 f.
Proof. intros. inversion H; subst; auto. Qed.
Lemma flag_plus_not_hid_l : forall f1 f2 f, flag_plus f1 f2 f -> f <> hid -> f1 <> hid.
Proof. intros. inversion H; subst; congruence. Qed.
Lemma flag_plus_not_hid_r : forall f1 f2 f, flag_plus f1 f2 f -> f <> hid -> f2 <> hid.
Proof. intros. inversion H; subst; congruence. Qed.
Lemma mv_eq : forall u x b, pair_eq u x = true -> mv u x b = b.
Proof.
  intros u x b H. destruct u as [u1 u2], x as [x1 x2], b as [b1 b2].
  unfold mv, pair_eq in *. simpl in *.
  rewrite andb_true_iff in H. destruct H as [H1 H2]. rewrite H1, H2. reflexivity.
Qed.
Lemma mv_neq : forall u x b, pair_eq u x = false -> mv u x b = u.
Proof.
  intros u x b H. destruct u as [u1 u2], x as [x1 x2], b as [b1 b2].
  unfold mv, pair_eq in *. simpl in *.
  rewrite andb_false_iff in H. destruct H as [H|H]; rewrite H.
  - reflexivity.
  - rewrite andb_false_r. reflexivity.
Qed.
Lemma pol_cup_io_inp : forall p q, p = io \/ p = inp -> pol_cup p q = io \/ pol_cup p q = inp.
Proof.
  intros p q Hp. destruct Hp as [Heq|Heq]; subst p; destruct q; simpl; auto.
Qed.

End Algebra.
Lemma NoDup_perm_list : forall (A:Type) (l l':list A), Permutation l l' -> NoDup l -> NoDup l'.
Proof.
  intros A l l' Hp. induction Hp as [|x l l' Hp IH | x y l | l l' l'' Hp1 IH1 Hp2 IH2]; intro Hnd.
  - constructor.
  - simpl in Hnd. apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnot Hnd].
    apply NoDup_cons_iff. split.
    + intro Hin. apply Hnot. exact (Permutation_in x (Permutation_sym Hp) Hin).
    + apply IH; exact Hnd.
  - simpl in Hnd. apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnoty Hnd'].
    apply NoDup_cons_iff in Hnd'. destruct Hnd' as [Hnotx Hndl].
    apply NoDup_cons_iff. split.
    + intro Hin. simpl in Hin. destruct Hin as [Heq|Hin].
      * apply Hnoty. simpl. left. symmetry. exact Heq.
      * exact (Hnotx Hin).
    + apply NoDup_cons_iff. split.
      * intro HY. apply Hnoty. simpl. right; exact HY.
      * exact Hndl.
  - apply IH2. apply IH1; exact Hnd.
Qed.

Lemma domain_map : forall g, domain g = map (fun e => fst (fst e)) g.
Proof.
  intros g. induction g as [|h tl IH].
  - reflexivity.
  - destruct h as [[x f] t]. simpl. rewrite IH. reflexivity.
Qed.

Lemma Permutation_domain : forall g g', Permutation g g' -> Permutation (domain g) (domain g').
Proof.
  intros g g' Hp. rewrite !domain_map. apply Permutation_map. exact Hp.
Qed.

Lemma NoDup_domain_perm : forall g g', Permutation g g' -> NoDup (domain g) -> NoDup (domain g').
Proof.
  intros g g' H Hnd. exact (NoDup_perm_list (name*name) (domain g) (domain g') (Permutation_domain g g' H) Hnd).
Qed.

Lemma Permutation_cons_removeEntry : forall g n f t,
  In ((n,f),t) g -> NoDup (domain g) ->
  Permutation (((n,f),t) :: removeEntry n g) g.
Proof.
  intros g. induction g as [|h tl IH]; intros n f t Hin Hnd.
  - simpl in Hin; destruct Hin.
  - destruct h as [[m fm] tm]. simpl in Hin.
    destruct (pair_eq m n) eqn:E.
    + apply pair_eq_true in E; subst m.
      destruct Hin as [Heq|Hin].
      * inversion Heq; subst. rewrite removeEntry_cons_eq. apply Permutation_refl.
      * exfalso.
        assert (Hing : In n (domain (((n,fm),tm)::tl))) by (simpl; left; auto).
        assert (Hinr : In n (domain (removeEntry n (((n,fm),tm)::tl)))).
        { rewrite removeEntry_cons_eq. apply in_dom_entry with (f:=f) (t:=t); exact Hin. }
        exact (NoDup_removeEntry_still n (((n,fm),tm)::tl) Hnd Hing Hinr).
    + simpl in Hnd. apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnot Hnd].
      destruct Hin as [Heq|Hin].
      * inversion Heq; subst. exfalso. apply pair_eq_false in E; apply E; reflexivity.
      * simpl. rewrite E. simpl.
        eapply perm_trans.
        -- apply perm_swap.
        -- apply perm_skip. apply (IH n f t); auto.
Qed.

Lemma Permutation_reinsert2 : forall g x b tx tb fx fb,
  In ((x,fx),tx) g -> In ((b,fb),tb) g -> x <> b -> NoDup (domain g) ->
  Permutation ((x,fx,tx)::(b,fb,tb)::removeEntry b (removeEntry x g)) g.
Proof.
  intros g x b tx tb fx fb Hx Hb Hxb Hnd.
  assert (Hndx : NoDup (domain (removeEntry x g))) by (apply NoDup_domain_removeEntry; auto).
  assert (Hbx : In ((b,fb),tb) (removeEntry x g)).
  { apply (in_removeEntry_intro x g b fb tb); [exact Hxb | exact Hb]. }
  assert (P2 : Permutation ((b,fb,tb)::removeEntry b (removeEntry x g)) (removeEntry x g))
    by (apply Permutation_cons_removeEntry; auto).
  assert (P1 : Permutation ((x,fx,tx)::removeEntry x g) g)
    by (apply Permutation_cons_removeEntry; auto).
  eapply perm_trans with (l' := (x,fx,tx)::removeEntry x g).
  - apply perm_skip. exact P2.
  - exact P1.
Qed.

Lemma ecomb_redistribute :
  forall (f1 f2 f : flag) ta ta' tb1 tb2 t t1 t2,
    ecomb (vis,ta) (vis,ta') (vis,t) ->
    ecomb (f1,tb1) (f2,tb2) (f,t1) ->
    type_plus t1 t t2 ->
    exists t21 t22, type_plus tb1 ta t21 /\ type_plus tb2 ta' t22 /\ type_plus t21 t22 t2 /\ ecomb (vis,t21) (vis,t22) (vis,t2).
Proof.
  intros f1 f2 f ta ta' tb1 tb2 t t1 t2 Hx Hb Htp.
  destruct t as [m p t0 | ].
  - destruct m.
    + (* lin *)
      destruct (ecomb_third_lin vis ta vis ta' vis p t0 Hx) as [p1 [p2 [Eta [Eta' Hpp]]]].
      subst ta ta'.
      destruct (type_plus_second_lin t1 p t0 t2 Htp) as [p0 [p4 [Et1 [Et2 H3]]]].
      subst t1 t2.
      destruct (ecomb_third_lin f1 tb1 f2 tb2 f p0 t0 Hb) as [q1 [q2 [Etb1 [Etb2 Hqq]]]].
      subst tb1 tb2.
      destruct (pol_plus_exchange q1 q2 p0 p1 p2 p p4 Hqq Hpp H3) as (r1 & r2 & Hr1 & Hr2 & Hr).
      exists (Chan lin r1 t0), (Chan lin r2 t0). split.
      * apply Tp_LinPlus; exact Hr1.
      * split.
        -- apply Tp_LinPlus; exact Hr2.
        -- split.
           ++ apply Tp_LinPlus; exact Hr.
           ++ apply ec_lin; [exact Fp_vv | exact Hr].
    + (* un *)
      destruct (ecomb_third_un vis ta vis ta' vis p t0 Hx) as [Eta Eta'].
      subst ta ta'.
      destruct (type_plus_second_un t1 p t0 t2 Htp) as [p0 [Et1 Et2]].
      subst t1 t2.
      destruct (ecomb_third_un f1 tb1 f2 tb2 f p0 t0 Hb) as [Etb1 Etb2].
      subst tb1 tb2.
      exists (Chan un (pol_cup p0 p) t0), (Chan un (pol_cup p0 p) t0). split.
      * apply Tp_UnPlus.
      * split.
        -- apply Tp_UnPlus.
        -- split.
           ++ pose proof (Tp_UnPlus (pol_cup p0 p) (pol_cup p0 p) t0) as Hself.
              rewrite pol_cup_idem in Hself. exact Hself.
           ++ apply ec_un; exact Fp_vv.
  - (* Top *)
    destruct (ecomb_third_top vis ta vis ta' vis Hx) as [Eta Eta'].
    subst ta ta'.
    destruct (type_plus_second_top t1 t2 Htp) as [Et1 Et2].
    subst t1 t2.
    destruct (ecomb_third_top f1 tb1 f2 tb2 f Hb) as [Etb1 Etb2].
    subst tb1 tb2.
    exists Top, Top. split; [apply Tp_Base | split; [apply Tp_Base | split; [apply Tp_Base | apply ec_top; exact Fp_vv]]].
Qed.



Lemma removeEntry_perm : forall n g g', Permutation g g' -> NoDup (domain g) ->
  Permutation (removeEntry n g) (removeEntry n g').
Proof.
  intros n g g' Hp. induction Hp as [|x l l' Hp IH | x y l | l l' l'' Hp1 IH1 Hp2 IH2]; intro Hnd.
  - apply perm_nil.
  - destruct x as [[a f] t]. cbn [removeEntry].
    destruct (pair_eq a n) eqn:E.
    + exact Hp.
    + apply perm_skip. apply IH. simpl in Hnd. apply NoDup_cons_iff in Hnd; exact (proj2 Hnd).
  - destruct x as [[ax fx] tx], y as [[ay fy] ty]. cbn [removeEntry].
    simpl in Hnd. apply NoDup_cons_iff in Hnd; destruct Hnd as [Hnoty Hnd].
    apply NoDup_cons_iff in Hnd; destruct Hnd as [Hnotx Hndl].
    destruct (pair_eq ay n) eqn:Ey; destruct (pair_eq ax n) eqn:Ex; simpl.
    + exfalso. apply Hnoty. simpl. left.
      apply pair_eq_true in Ey. apply pair_eq_true in Ex.
      rewrite Ex, <- Ey. reflexivity.
    + apply perm_skip. apply Permutation_refl.
    + apply perm_skip. apply Permutation_refl.
    + apply perm_swap.
  - apply perm_trans with (l' := removeEntry n l').
    + apply IH1; exact Hnd.
    + apply IH2. apply (NoDup_domain_perm l l' Hp1 Hnd).
Qed.


Lemma removeEntry_self_domain : forall n f t tl,
  domain (removeEntry n (((n,f),t)::tl)) = domain tl.
Proof. intros. rewrite removeEntry_cons_eq. reflexivity. Qed.

Lemma domain_removeEntry_perm : forall n g, In n (domain g) ->
  Permutation (domain g) (n :: domain (removeEntry n g)).
Proof.
  intros n g. induction g as [|h tl IH].
  - simpl. intros H; destruct H.
  - destruct h as [[x f] t]. simpl. intros H.
    destruct (pair_eq x n) eqn:E.
    + apply pair_eq_true in E; subst x. apply Permutation_refl.
    + assert (Hxn : x <> n) by (apply pair_eq_false; exact E).
      simpl in H. destruct H as [Heq|Hin].
      * subst x. exfalso. apply Hxn. reflexivity.
      * apply perm_trans with (l' := x :: n :: domain (removeEntry n tl)).
        -- apply perm_skip. apply IH; exact Hin.
        -- apply Permutation_sym. apply perm_swap.
Qed.

Lemma max_le_spec : forall l m, max l <= m <-> (forall a x, In (a,x) l -> x <= m).
Proof.
  intros l. induction l as [|h t IH]; intros m.
  - simpl. split; intros HH. { intros a x Hin; simpl in Hin; destruct Hin. } lia.
  - destruct h as [a x]. simpl.
    remember (max t) as mt eqn:E.
    destruct (x <? mt) eqn:Elt.
    + apply Nat.ltb_lt in Elt.
      split.
      * intros Hm a0 x0 [Heq|Hin].
        -- inversion Heq; subst. lia.
        -- assert (Hle : mt <= m) by lia.
           exact (proj1 (IH m) Hle a0 x0 Hin).
      * intros H. apply (proj2 (IH m)). intros a0 x0 Hin. apply (H a0 x0). right; exact Hin.
    + apply Nat.ltb_ge in Elt.
      split.
      * intros Hm a0 x0 [Heq|Hin].
        -- inversion Heq; subst. lia.
        -- assert (Hle : mt <= m) by lia.
           exact (proj1 (IH m) Hle a0 x0 Hin).
      * intros H. apply (H a x). left; reflexivity.
Qed.
Lemma max_perm : forall l l', Permutation l l' -> max l = max l'.
Proof.
  intros l l' Hp. apply Nat.le_antisymm.
  - apply (proj2 (max_le_spec l (max l'))). intros a x Hin.
    exact (proj1 (max_le_spec l' (max l')) (le_n (max l')) a x (Permutation_in (a,x) Hp Hin)).
  - apply (proj2 (max_le_spec l' (max l))). intros a x Hin.
    exact (proj1 (max_le_spec l (max l)) (le_n (max l)) a x (Permutation_in (a,x) (Permutation_sym Hp) Hin)).
Qed.

Lemma max_cons_lt : forall (x:name*name) l, snd x < max l -> max (x :: l) = max l.
Proof.
  intros [x1 x2] l H. cbn in H. cbn [max].
  destruct (x2 <? max l) eqn:E.
  - reflexivity.
  - apply Nat.ltb_ge in E. exfalso. lia.
Qed.

Lemma max_le_of_in : forall (l l':list (name*name)),
  (forall x, In x l -> In x l') -> max l <= max l'.
Proof.
  intros l l' H. apply (proj2 (max_le_spec l (max l'))). intros a x Hin.
  exact (proj1 (max_le_spec l' (max l')) (le_n (max l')) a x (H (a,x) Hin)).
Qed.

Section SplitChar.

Lemma In_dom_entry_rev : forall g n, In n (domain g) -> exists f t, In ((n,f),t) g.
Proof.
  intros g. induction g as [|h tl IH].
  - intros n H. simpl in H. exfalso; exact H.
  - destruct h as [[x fx] tx]. simpl. intros n [Heq|Hin].
    + subst. exists fx, tx. simpl. left; reflexivity.
    + destruct (IH n Hin) as [f [t H]]. exists f, t. simpl. right; exact H.
Qed.

Lemma In_dom_removeEntry_iff : forall n g, In n (domain g) ->
    forall x, In x (domain g) <-> x = n \/ In x (domain (removeEntry n g)).
Proof.
  intros n g Hn x. split.
  - intros Hx. destruct (nat_pair_eq_dec x n) as [->|Hne].
    + left; reflexivity.
    + right. apply domain_removeEntry_neq; auto.
  - intros [->|H].
    + exact Hn.
    + apply domain_removeEntry_sub with (y:=n); exact H.
Qed.

Lemma In_dom_removeEntry_iff2 : forall n g, NoDup (domain g) -> In n (domain g) ->
    forall x, In x (domain (removeEntry n g)) <-> In x (domain g) /\ x <> n.
Proof.
  intros n g Hnd Hn x. split.
  - intro H. split.
    + apply domain_removeEntry_sub with (y:=n); exact H.
    + intro Hxn; subst x. exact (NoDup_removeEntry_still n g Hnd Hn H).
  - intros [Hg Hxn]. apply domain_removeEntry_neq; auto.
Qed.


Lemma ecomb_top_inv : forall f1 f2 f3 t2 t3, ecomb (f1,Top) (f2,t2) (f3,t3) ->
  t2=Top /\ t3=Top /\ flag_plus f1 f2 f3.
Proof. intros. inversion H. subst. auto. Qed.
Lemma ecomb_un_inv : forall f1 f2 f3 p t t2 t3, ecomb (f1,Chan un p t) (f2,t2) (f3,t3) ->
  t2=Chan un p t /\ t3=Chan un p t /\ flag_plus f1 f2 f3.
Proof. intros. inversion H. subst. auto. Qed.
Lemma ecomb_lin_inv : forall f1 f2 f3 p t t2 t3, ecomb (f1,Chan lin p t) (f2,t2) (f3,t3) ->
  exists q r, t2=Chan lin q t /\ t3=Chan lin r t /\ flag_plus f1 f2 f3 /\ pol_plus p q r.
Proof. intros. inversion H. subst. exists p2, p0. auto. Qed.



Lemma tEnv_split_pf_irrel : forall g1 g2 g3 pf1 pf2 pf3,
  tEnv_split g1 g2 g3 pf1 pf2 pf3 -> forall pf1' pf2' pf3',
  tEnv_split g1 g2 g3 pf1' pf2' pf3'.
Proof.
  intros g1 g2 g3 pf1 pf2 pf3 H. induction H; intros pf1' pf2' pf3'.
  - apply SpNil; auto.
  - eapply SpLin; eauto.
  - eapply SpUn; eauto.
  - eapply SpTop; eauto.
Qed.

Lemma tEnv_split_env1 : forall g1 g1' g2 g3 pf1 pf2 pf3, g1' = g1 ->
  tEnv_split g1 g2 g3 pf1 pf2 pf3 -> forall pf1', tEnv_split g1' g2 g3 pf1' pf2 pf3.
Proof.
  intros g1 g1' g2 g3 pf1 pf2 pf3 E H pf1'. subst.
  apply (tEnv_split_pf_irrel g1 g2 g3 pf1 pf2 pf3 H pf1' pf2 pf3).
Qed.

Lemma In_dom_remove2 : forall g x b, NoDup (domain g) -> In x (domain g) -> In b (domain g) -> x <> b ->
  forall x0, In x0 (domain (removeEntry b (removeEntry x g))) <-> In x0 (domain g) /\ x0 <> x /\ x0 <> b.
Proof.
  intros g x b Hnd Hx Hb Hxb x0.
  assert (Hndx : NoDup (domain (removeEntry x g))) by (apply NoDup_domain_removeEntry; auto).
  assert (Hbx : In b (domain (removeEntry x g))) by (apply domain_removeEntry_neq; auto).
  rewrite (In_dom_removeEntry_iff2 b (removeEntry x g) Hndx Hbx x0).
  rewrite (In_dom_removeEntry_iff2 x g Hnd Hx x0).
  tauto.
Qed.

Definition esplit (g1 g2 g3 : typeEnv) : Prop :=
  (forall n, In n (domain g1) <-> In n (domain g2)) /\
  (forall n, In n (domain g2) <-> In n (domain g3)) /\
  (forall n f1 t1 f2 t2, In ((n,f1),t1) g1 -> In ((n,f2),t2) g2 ->
      exists f t, In ((n,f),t) g3 /\ ecomb (f1,t1) (f2,t2) (f,t)).


Lemma tEnv_split_esplit : forall g1 g2 g3 pf1 pf2 pf3,
    tEnv_split g1 g2 g3 pf1 pf2 pf3 -> esplit g1 g2 g3.
Proof.
  intros g1 g2 g3 pf1 pf2 pf3 H. induction H.
  - (* SpNil *)
    subst. unfold esplit. split.
    + intros x; simpl; split; intros HH; auto; destruct HH.
    + split.
      * intros x; simpl; split; intros HH; auto; destruct HH.
      * intros x f1 t1 f2 t2 HH; simpl in HH; destruct HH.
  - (* SpLin *)
    assert (Hn1 : In n (domain g1)) by (apply in_dom_entry with (f:=f) (t:=Chan lin p t); exact H1).
    assert (Hn2 : In n (domain g2)) by (apply in_dom_entry with (f:=g) (t:=Chan lin q t); exact H2).
    assert (Hn3 : In n (domain g3)) by (destruct (typeOf_inv g3 n (Chan lin p' t) H6) as [fz Hz]; apply in_dom_entry with (f:=fz) (t:=Chan lin p' t); exact Hz).
    unfold esplit. split.
    + intros x; split; intro Hx.
      * destruct (proj1 (In_dom_removeEntry_iff n g1 Hn1 x) Hx) as [->|Hx'].
        -- exact Hn2.
        -- apply domain_removeEntry_sub with (y:=n).
           exact (proj1 (proj1 IHtEnv_split x) Hx').
      * destruct (proj1 (In_dom_removeEntry_iff n g2 Hn2 x) Hx) as [->|Hx'].
        -- exact Hn1.
        -- apply domain_removeEntry_sub with (y:=n).
           exact (proj2 (proj1 IHtEnv_split x) Hx').
    + split.
      * intros x; split; intro Hx.
        -- destruct (proj1 (In_dom_removeEntry_iff n g2 Hn2 x) Hx) as [->|Hx'].
           ++ exact Hn3.
           ++ apply domain_removeEntry_sub with (y:=n).
              rewrite H4.
              exact (proj1 (proj1 (proj2 IHtEnv_split) x) Hx').
        -- destruct (proj1 (In_dom_removeEntry_iff n g3 Hn3 x) Hx) as [->|Hx'].
           ++ exact Hn2.
           ++ rewrite H4 in Hx'. apply domain_removeEntry_sub with (y:=n).
              exact (proj2 (proj1 (proj2 IHtEnv_split) x) Hx').
      * intros x f1 t1 f2 t2 He1 He2.
        destruct (nat_pair_eq_dec x n) as [->|Hne].
        -- assert (Hf1 : f = f1) by (exact (proj1 (pf1 n f (Chan lin p t) f1 t1 (conj H1 He1)))).
           assert (Ht1 : Chan lin p t = t1) by (exact (proj2 (pf1 n f (Chan lin p t) f1 t1 (conj H1 He1)))).
           assert (Hf2 : g = f2) by (exact (proj1 (pf2 n g (Chan lin q t) f2 t2 (conj H2 He2)))).
           assert (Ht2 : Chan lin q t = t2) by (exact (proj2 (pf2 n g (Chan lin q t) f2 t2 (conj H2 He2)))).
           subst f1 t1 f2 t2.
           destruct (typeOf_inv g3 n (Chan lin p' t) H6) as [f0 Hf0].
           destruct (flagOf_inv g3 n f' H5) as [t0 Ht0].
           destruct (pf3 n f0 (Chan lin p' t) f' t0 (conj Hf0 Ht0)) as [Hfeq Hteq].
           subst f0. exists f', (Chan lin p' t). split; auto.
           apply ec_lin; auto.
        -- assert (He1' : In ((x,f1),t1) (removeEntry n g1))
             by (apply in_removeEntry_intro with (y:=n); auto).
           assert (He2' : In ((x,f2),t2) (removeEntry n g2))
             by (apply in_removeEntry_intro with (y:=n); auto).
           destruct (proj2 (proj2 IHtEnv_split) x f1 t1 f2 t2 He1' He2') as [ff [tt [Hg Hec]]].
           exists ff, tt. split; [|exact Hec].
           rewrite <- H4 in Hg. exact (in_removeEntry_elim n g3 x ff tt Hg).
  - (* SpUn *)
    assert (Hn1 : In n (domain g1)) by (apply in_dom_entry with (f:=f) (t:=Chan un p t); exact H0).
    assert (Hn2 : In n (domain g2)) by (apply in_dom_entry with (f:=g) (t:=Chan un p t); exact H1).
    assert (Hn3 : In n (domain g3)) by (destruct (typeOf_inv g3 n (Chan un p t) H5) as [fz Hz]; apply in_dom_entry with (f:=fz) (t:=Chan un p t); exact Hz).
    unfold esplit. split.
    + intros x; split; intro Hx.
      * destruct (proj1 (In_dom_removeEntry_iff n g1 Hn1 x) Hx) as [->|Hx'].
        -- exact Hn2.
        -- apply domain_removeEntry_sub with (y:=n).
           exact (proj1 (proj1 IHtEnv_split x) Hx').
      * destruct (proj1 (In_dom_removeEntry_iff n g2 Hn2 x) Hx) as [->|Hx'].
        -- exact Hn1.
        -- apply domain_removeEntry_sub with (y:=n).
           exact (proj2 (proj1 IHtEnv_split x) Hx').
    + split.
      * intros x; split; intro Hx.
        -- destruct (proj1 (In_dom_removeEntry_iff n g2 Hn2 x) Hx) as [->|Hx'].
           ++ exact Hn3.
           ++ apply domain_removeEntry_sub with (y:=n).
              rewrite H3.
              exact (proj1 (proj1 (proj2 IHtEnv_split) x) Hx').
        -- destruct (proj1 (In_dom_removeEntry_iff n g3 Hn3 x) Hx) as [->|Hx'].
           ++ exact Hn2.
           ++ rewrite H3 in Hx'. apply domain_removeEntry_sub with (y:=n).
              exact (proj2 (proj1 (proj2 IHtEnv_split) x) Hx').
      * intros x f1 t1 f2 t2 He1 He2.
        destruct (nat_pair_eq_dec x n) as [->|Hne].
        -- assert (Hf1 : f = f1) by (exact (proj1 (pf1 n f (Chan un p t) f1 t1 (conj H0 He1)))).
           assert (Ht1 : Chan un p t = t1) by (exact (proj2 (pf1 n f (Chan un p t) f1 t1 (conj H0 He1)))).
           assert (Hf2 : g = f2) by (exact (proj1 (pf2 n g (Chan un p t) f2 t2 (conj H1 He2)))).
           assert (Ht2 : Chan un p t = t2) by (exact (proj2 (pf2 n g (Chan un p t) f2 t2 (conj H1 He2)))).
           subst f1 t1 f2 t2.
           destruct (typeOf_inv g3 n (Chan un p t) H5) as [f0 Hf0].
           destruct (flagOf_inv g3 n f' H4) as [t0 Ht0].
           destruct (pf3 n f0 (Chan un p t) f' t0 (conj Hf0 Ht0)) as [Hfeq Hteq].
           subst f0. exists f', (Chan un p t). split; auto.
           apply ec_un; auto.
        -- assert (He1' : In ((x,f1),t1) (removeEntry n g1))
             by (apply in_removeEntry_intro with (y:=n); auto).
           assert (He2' : In ((x,f2),t2) (removeEntry n g2))
             by (apply in_removeEntry_intro with (y:=n); auto).
           destruct (proj2 (proj2 IHtEnv_split) x f1 t1 f2 t2 He1' He2') as [ff [tt [Hg Hec]]].
           exists ff, tt. split; [|exact Hec].
           rewrite <- H3 in Hg. exact (in_removeEntry_elim n g3 x ff tt Hg).
  - (* SpTop *)
    assert (Hn1 : In n (domain g1)) by (apply in_dom_entry with (f:=f) (t:=Top); exact H0).
    assert (Hn2 : In n (domain g2)) by (apply in_dom_entry with (f:=g) (t:=Top); exact H1).
    assert (Hn3 : In n (domain g3)) by (destruct (typeOf_inv g3 n Top H5) as [fz Hz]; apply in_dom_entry with (f:=fz) (t:=Top); exact Hz).
    unfold esplit. split.
    + intros x; split; intro Hx.
      * destruct (proj1 (In_dom_removeEntry_iff n g1 Hn1 x) Hx) as [->|Hx'].
        -- exact Hn2.
        -- apply domain_removeEntry_sub with (y:=n).
           exact (proj1 (proj1 IHtEnv_split x) Hx').
      * destruct (proj1 (In_dom_removeEntry_iff n g2 Hn2 x) Hx) as [->|Hx'].
        -- exact Hn1.
        -- apply domain_removeEntry_sub with (y:=n).
           exact (proj2 (proj1 IHtEnv_split x) Hx').
    + split.
      * intros x; split; intro Hx.
        -- destruct (proj1 (In_dom_removeEntry_iff n g2 Hn2 x) Hx) as [->|Hx'].
           ++ exact Hn3.
           ++ apply domain_removeEntry_sub with (y:=n).
              rewrite H3.
              exact (proj1 (proj1 (proj2 IHtEnv_split) x) Hx').
        -- destruct (proj1 (In_dom_removeEntry_iff n g3 Hn3 x) Hx) as [->|Hx'].
           ++ exact Hn2.
           ++ rewrite H3 in Hx'. apply domain_removeEntry_sub with (y:=n).
              exact (proj2 (proj1 (proj2 IHtEnv_split) x) Hx').
      * intros x f1 t1 f2 t2 He1 He2.
        destruct (nat_pair_eq_dec x n) as [->|Hne].
        -- assert (Hf1 : f = f1) by (exact (proj1 (pf1 n f Top f1 t1 (conj H0 He1)))).
           assert (Ht1 : Top = t1) by (exact (proj2 (pf1 n f Top f1 t1 (conj H0 He1)))).
           assert (Hf2 : g = f2) by (exact (proj1 (pf2 n g Top f2 t2 (conj H1 He2)))).
           assert (Ht2 : Top = t2) by (exact (proj2 (pf2 n g Top f2 t2 (conj H1 He2)))).
           subst f1 t1 f2 t2.
           destruct (typeOf_inv g3 n Top H5) as [f0 Hf0].
           destruct (flagOf_inv g3 n f' H4) as [t0 Ht0].
           destruct (pf3 n f0 Top f' t0 (conj Hf0 Ht0)) as [Hfeq Hteq].
           subst f0. exists f', Top. split; auto.
           apply ec_top; auto.
        -- assert (He1' : In ((x,f1),t1) (removeEntry n g1))
             by (apply in_removeEntry_intro with (y:=n); auto).
           assert (He2' : In ((x,f2),t2) (removeEntry n g2))
             by (apply in_removeEntry_intro with (y:=n); auto).
           destruct (proj2 (proj2 IHtEnv_split) x f1 t1 f2 t2 He1' He2') as [ff [tt [Hg Hec]]].
           exists ff, tt. split; [|exact Hec].
           rewrite <- H3 in Hg. exact (in_removeEntry_elim n g3 x ff tt Hg).
Qed.


Lemma esplit_tEnv_split : forall g1 g2 g3 pf1 pf2 pf3,
    NoDup (domain g1) -> NoDup (domain g2) -> NoDup (domain g3) ->
    esplit g1 g2 g3 -> tEnv_split g1 g2 g3 pf1 pf2 pf3.
Proof.
  intros g1. induction g1 as [|e tl IH]; intros g2 g3 pf1 pf2 pf3 nd1 nd2 nd3 Hes.
  - (* g1 = nil *)
    destruct Hes as [HA [HB HC]].
    destruct g2 as [|h2 t2].
    + destruct g3 as [|h3 t3].
      * apply SpNil; auto.
      * exfalso. destruct h3 as [[x fx] tx]. simpl in HB.
        assert (Hin : In x (domain (((x,fx),tx)::t3))) by (simpl; left; auto).
        assert (Hin0 : In x (domain nil)) by (apply (proj2 (HB x)); exact Hin).
        simpl in Hin0. exact Hin0.
    + exfalso. destruct h2 as [[x fx] tx].
      assert (Hin : In x (domain (((x,fx),tx)::t2))) by (simpl; left; auto).
      assert (Hin0 : In x (domain nil)) by (apply (proj2 (HA x)); exact Hin).
      simpl in Hin0. exact Hin0.
  - (* g1 = e :: tl *)
    destruct e as [[n f] t].
    simpl in nd1. apply NoDup_cons_iff in nd1. destruct nd1 as [Hnotn Hndtl].
    destruct Hes as [HA [HB HC]].
    assert (Hn1 : In n (domain (((n,f),t)::tl))) by (simpl; left; auto).
    assert (Hn2 : In n (domain g2)) by (apply (proj1 (HA n)); exact Hn1).
    assert (Hn3 : In n (domain g3)) by (apply (proj1 (HB n)); exact Hn2).
    destruct (In_dom_entry_rev g2 n Hn2) as [f2 [t2 H2]].
    destruct (HC n f t f2 t2 (or_introl eq_refl) H2) as [f3 [t3 [H3 Hcomb]]].
    (* restricted esplit *)
    assert (Hes' : esplit tl (removeEntry n g2) (removeEntry n g3)).
    { unfold esplit. split.
      - intros x; split; intro Hx.
        + assert (Hx1 : In x (domain (((n,f),t)::tl))) by (simpl; right; exact Hx).
          assert (Hxn : x <> n) by (intro Hxn; subst x; exact (Hnotn Hx)).
          assert (Hx2 : In x (domain g2)) by (apply (proj1 (HA x)); exact Hx1).
          apply (proj2 (In_dom_removeEntry_iff2 n g2 nd2 Hn2 x)). split; auto.
        + assert (Hx2 : In x (domain g2)) by (apply domain_removeEntry_sub with (y:=n); exact Hx).
          assert (Hxn : x <> n) by (intro Hxn; subst x; exact (NoDup_removeEntry_still n g2 nd2 Hn2 Hx)).
          assert (Hx1 : In x (domain (((n,f),t)::tl))) by (apply (proj2 (HA x)); exact Hx2).
          simpl in Hx1. destruct Hx1 as [Hxn'|Hxt]; [exfalso; apply Hxn; symmetry; exact Hxn'|exact Hxt].
      - split.
        + intros x; split; intro Hx.
          * assert (Hx2 : In x (domain g2)) by (apply domain_removeEntry_sub with (y:=n); exact Hx).
            assert (Hxn : x <> n) by (intro Hxn; subst x; exact (NoDup_removeEntry_still n g2 nd2 Hn2 Hx)).
            assert (Hx3 : In x (domain g3)) by (apply (proj1 (HB x)); exact Hx2).
            apply (proj2 (In_dom_removeEntry_iff2 n g3 nd3 Hn3 x)). split; auto.
          * assert (Hx3 : In x (domain g3)) by (apply domain_removeEntry_sub with (y:=n); exact Hx).
            assert (Hxn : x <> n) by (intro Hxn; subst x; exact (NoDup_removeEntry_still n g3 nd3 Hn3 Hx)).
            assert (Hx2 : In x (domain g2)) by (apply (proj2 (HB x)); exact Hx3).
            apply (proj2 (In_dom_removeEntry_iff2 n g2 nd2 Hn2 x)). split; auto.
        + intros x a1 b1 a2 b2 He1 He2.
          assert (He1' : In ((x,a1),b1) (((n,f),t)::tl)) by (simpl; right; exact He1).
          assert (He2' : In ((x,a2),b2) g2) by (eapply in_removeEntry_elim; eauto).
          destruct (HC x a1 b1 a2 b2 He1' He2') as [ff [tt [Hg Hec]]].
          assert (Hxn : x <> n) by (intro Hxn; subst x; apply Hnotn; apply in_dom_entry with (f:=a1) (t:=b1); exact He1).
          exists ff, tt. split; [|exact Hec].
          apply (in_removeEntry_intro n g3 x ff tt); [|exact Hg].
          intro H; apply Hxn; symmetry; exact H.
    }
    assert (Hpf1' : isMap tl).
    { pose proof (isMap_removeEntry n (((n,f),t)::tl) pf1) as H; rewrite removeEntry_cons_eq in H; exact H. }
    assert (Hpf2' : isMap (removeEntry n g2)) by (apply isMap_removeEntry; exact pf2).
    assert (Hpf3' : isMap (removeEntry n g3)) by (apply isMap_removeEntry; exact pf3).
    assert (Hnd2' : NoDup (domain (removeEntry n g2))) by (apply NoDup_domain_removeEntry; exact nd2).
    assert (Hnd3' : NoDup (domain (removeEntry n g3))) by (apply NoDup_domain_removeEntry; exact nd3).
    assert (Hrec : tEnv_split tl (removeEntry n g2) (removeEntry n g3)
                               Hpf1' Hpf2' Hpf3').
    { apply (IH (removeEntry n g2) (removeEntry n g3) Hpf1' Hpf2' Hpf3'); auto. }
    destruct t as [m p0 t0 | ].
    + destruct m.
      * (* Chan lin p0 t0 *)
        destruct (ecomb_lin_inv f f2 f3 p0 t0 t2 t3 Hcomb) as [q [r [Ht2 [Ht3 [Hfp Hpp]]]]].
        subst t2 t3.
        eapply SpLin with (n:=n) (f:=f) (f':=f3) (g:=f2) (p:=p0) (q:=q) (p':=r) (t:=t0)
                          (g''':=removeEntry n g3).
        -- exact Hfp.
        -- exact Hpp.
        -- simpl; left; reflexivity.
        -- exact H2.
        -- apply (tEnv_split_env1 tl (removeEntry n (((n,f),Chan lin p0 t0)::tl)) (removeEntry n g2) (removeEntry n g3) Hpf1' Hpf2' Hpf3' (removeEntry_cons_eq n f (Chan lin p0 t0) tl) Hrec (isMap_removeEntry n (((n,f),Chan lin p0 t0)::tl) pf1)).
        -- reflexivity.
        -- apply (F_Entry g3 n f3 (Chan lin r t0)); exact H3.
        -- apply (T_Entry g3 n f3 (Chan lin r t0)); exact H3.
      * (* Chan un p0 t0 *)
        destruct (ecomb_un_inv f f2 f3 p0 t0 t2 t3 Hcomb) as [Ht2 [Ht3 Hfp]].
        subst t2 t3.
        eapply SpUn with (n:=n) (f:=f) (f':=f3) (g:=f2) (p:=p0) (t:=t0)
                         (g''':=removeEntry n g3).
        -- exact Hfp.
        -- simpl; left; reflexivity.
        -- exact H2.
        -- apply (tEnv_split_env1 tl (removeEntry n (((n,f),Chan un p0 t0)::tl)) (removeEntry n g2) (removeEntry n g3) Hpf1' Hpf2' Hpf3' (removeEntry_cons_eq n f (Chan un p0 t0) tl) Hrec (isMap_removeEntry n (((n,f),Chan un p0 t0)::tl) pf1)).
        -- reflexivity.
        -- apply (F_Entry g3 n f3 (Chan un p0 t0)); exact H3.
        -- apply (T_Entry g3 n f3 (Chan un p0 t0)); exact H3.
    + (* Top *)
      destruct (ecomb_top_inv f f2 f3 t2 t3 Hcomb) as [Ht2 [Ht3 Hfp]].
      subst t2 t3.
      eapply SpTop with (n:=n) (f:=f) (f':=f3) (g:=f2) (g''':=removeEntry n g3).
      * exact Hfp.
      * simpl; left; reflexivity.
      * exact H2.
      * apply (tEnv_split_env1 tl (removeEntry n (((n,f),Top)::tl)) (removeEntry n g2) (removeEntry n g3) Hpf1' Hpf2' Hpf3' (removeEntry_cons_eq n f Top tl) Hrec (isMap_removeEntry n (((n,f),Top)::tl) pf1)).
      * reflexivity.
      * apply (F_Entry g3 n f3 Top); exact H3.
      * apply (T_Entry g3 n f3 Top); exact H3.
Qed.

End SplitChar.

Lemma nodup_cons_step : forall n g1 g2 g3 g''' pf1 pf2 pf3,
  NoDup (domain g3) ->
  In n (domain g1) -> In n (domain g2) -> In n (domain g3) ->
  NoDup (domain (removeEntry n g1)) -> NoDup (domain (removeEntry n g2)) ->
  tEnv_split (removeEntry n g1) (removeEntry n g2) g''' pf1 pf2 pf3 ->
  removeEntry n g3 = g''' ->
  NoDup (domain g1) /\ NoDup (domain g2).
Proof.
  intros n g1 g2 g3 g''' pf1 pf2 pf3 Hnd3 Hn1 Hn2 Hn3 Hndr1 Hndr2 Hspl Hrem.
  assert (Hnd3' : NoDup (domain g''')) by (rewrite <- Hrem; apply NoDup_domain_removeEntry; exact Hnd3).
  assert (Hnotin3 : ~ In n (domain g''')) by (rewrite <- Hrem; apply NoDup_removeEntry_still; auto).
  pose proof (tEnv_split_esplit _ _ _ _ _ _ Hspl) as Hes.
  destruct Hes as [HA [HB HC]].
  assert (Hnot1 : ~ In n (domain (removeEntry n g1))).
  { intro Hc. apply Hnotin3. apply (proj1 (HB n)). apply (proj1 (HA n) Hc). }
  assert (Hnot2 : ~ In n (domain (removeEntry n g2))).
  { intro Hc. apply Hnotin3. apply (proj1 (HB n)). exact Hc. }
  split.
  - apply (NoDup_perm_list (name*name) (n :: domain (removeEntry n g1)) (domain g1)).
    + apply Permutation_sym. apply domain_removeEntry_perm; exact Hn1.
    + apply NoDup_cons_iff. split; auto.
  - apply (NoDup_perm_list (name*name) (n :: domain (removeEntry n g2)) (domain g2)).
    + apply Permutation_sym. apply domain_removeEntry_perm; exact Hn2.
    + apply NoDup_cons_iff. split; auto.
Qed.

Lemma tEnv_split_nodup : forall g1 g2 g3 pf1 pf2 pf3,
  tEnv_split g1 g2 g3 pf1 pf2 pf3 -> NoDup (domain g3) ->
  NoDup (domain g1) /\ NoDup (domain g2).
Proof.
  intros g1 g2 g3 pf1 pf2 pf3 H.
  induction H as [g1 g2 g3 pf1 pf2 pf3 Eg1 Eg2 Eg3
                  | g1 g2 g3 pf1 pf2 pf3 n f f' g p q p' t g''' pf' pf'' pf''' Hfp Hpq Hi1 Hi2 Hrec IH Hrem Hfo Hty
                  | g1 g2 g3 pf1 pf2 pf3 n f f' g p t g''' pf' pf'' pf''' Hfp Hi1 Hi2 Hrec IH Hrem Hfo Hty
                  | g1 g2 g3 pf1 pf2 pf3 n f f' g g''' pf' pf'' pf''' Hfp Hi1 Hi2 Hrec IH Hrem Hfo Hty]; intro Hnd3.
  - subst. split; constructor.
  - (* SpLin *) 
    apply (nodup_cons_step n g1 g2 g3 g''' pf' pf'' pf''' Hnd3).
    + apply in_dom_entry with (f:=f) (t:=Chan lin p t); exact Hi1.
    + apply in_dom_entry with (f:=g) (t:=Chan lin q t); exact Hi2.
    + destruct (typeOf_inv g3 n (Chan lin p' t) Hty) as [fz Hz]; apply in_dom_entry with (f:=fz) (t:=Chan lin p' t); exact Hz.
    + apply IH. rewrite <- Hrem. apply NoDup_domain_removeEntry; exact Hnd3.
    + apply IH. rewrite <- Hrem. apply NoDup_domain_removeEntry; exact Hnd3.
    + exact Hrec.
    + exact Hrem.
  - (* SpUn *)
    apply (nodup_cons_step n g1 g2 g3 g''' pf' pf'' pf''' Hnd3).
    + apply in_dom_entry with (f:=f) (t:=Chan un p t); exact Hi1.
    + apply in_dom_entry with (f:=g) (t:=Chan un p t); exact Hi2.
    + destruct (typeOf_inv g3 n (Chan un p t) Hty) as [fz Hz]; apply in_dom_entry with (f:=fz) (t:=Chan un p t); exact Hz.
    + apply IH. rewrite <- Hrem. apply NoDup_domain_removeEntry; exact Hnd3.
    + apply IH. rewrite <- Hrem. apply NoDup_domain_removeEntry; exact Hnd3.
    + exact Hrec.
    + exact Hrem.
  - (* SpTop *)
    apply (nodup_cons_step n g1 g2 g3 g''' pf' pf'' pf''' Hnd3).
    + apply in_dom_entry with (f:=f) (t:=Top); exact Hi1.
    + apply in_dom_entry with (f:=g) (t:=Top); exact Hi2.
    + destruct (typeOf_inv g3 n Top Hty) as [fz Hz]; apply in_dom_entry with (f:=fz) (t:=Top); exact Hz.
    + apply IH. rewrite <- Hrem. apply NoDup_domain_removeEntry; exact Hnd3.
    + apply IH. rewrite <- Hrem. apply NoDup_domain_removeEntry; exact Hnd3.
    + exact Hrec.
    + exact Hrem.
Qed.




Lemma In_vis_proj : forall g n f t,
  In ((n,f),t) (vis_proj g) <-> In ((n,f),t) g /\ f = vis.
Proof.
  intros g. induction g as [|h tl IH]; intros n f t.
  - simpl. split.
    + intros H; simpl in H; destruct H.
    + intros [H1 H2]; simpl in H1; destruct H1.
  - destruct h as [[[x1 x2] fx] tx]. simpl.
    destruct fx.
    + (* hid *) simpl. rewrite IH. split.
      * intros [Hin Hf]. split; [right; exact Hin | exact Hf].
      * intros [[Heq|Hin] Hf]. inversion Heq; subst; discriminate. split; auto.
    + (* ill *) simpl. rewrite IH. split.
      * intros [Hin Hf]. split; [right; exact Hin | exact Hf].
      * intros [[Heq|Hin] Hf]. inversion Heq; subst; discriminate. split; auto.
    + (* vis *) simpl. rewrite IH.
      split.
      * intros [Heq | [Hin Hf]].
        -- split; [left; exact Heq |]. inversion Heq; reflexivity.
        -- split; [right; exact Hin | exact Hf].
      * intros [[Heq|Hin] Hf].
        -- left; exact Heq.
        -- right; split; auto.
Qed.
Lemma In_ill_proj : forall g n f t,
  In ((n,f),t) (ill_proj g) <-> In ((n,f),t) g /\ f = ill.
Proof.
  intros g. induction g as [|h tl IH]; intros n f t.
  - simpl. split.
    + intros H; simpl in H; destruct H.
    + intros [H1 H2]; simpl in H1; destruct H1.
  - destruct h as [[[x1 x2] fx] tx]. simpl.
    destruct fx.
    + (* hid *) simpl. rewrite IH. split.
      * intros [Hin Hf]. split; [right; exact Hin | exact Hf].
      * intros [[Heq|Hin] Hf]. inversion Heq; subst; discriminate. split; auto.
    + (* ill *) simpl. rewrite IH.
      split.
      * intros [Heq | [Hin Hf]].
        -- split; [left; exact Heq |]. inversion Heq; reflexivity.
        -- split; [right; exact Hin | exact Hf].
      * intros [[Heq|Hin] Hf].
        -- left; exact Heq.
        -- right; split; auto.
    + (* vis *) simpl. rewrite IH. split.
      * intros [Hin Hf]. split; [right; exact Hin | exact Hf].
      * intros [[Heq|Hin] Hf]. inversion Heq; subst; discriminate. split; auto.
Qed.

Lemma isMap_proj : forall g, isMap g -> isMap (vis_proj g ++ ill_proj g).
Proof.
  intros g Hm. unfold isMap. intros x f1 t1 f2 t2 [H1 H2].
  apply (Hm x f1 t1 f2 t2). split.
  - apply in_app_or in H1. destruct H1 as [H|H].
    + exact (proj1 (proj1 (In_vis_proj g x f1 t1) H)).
    + exact (proj1 (proj1 (In_ill_proj g x f1 t1) H)).
  - apply in_app_or in H2. destruct H2 as [H|H].
    + exact (proj1 (proj1 (In_vis_proj g x f2 t2) H)).
    + exact (proj1 (proj1 (In_ill_proj g x f2 t2) H)).
Qed.

Lemma cons_proj_perm : forall g g' pf pf', Permutation g g' ->
  cons (vis_proj g ++ ill_proj g) pf -> cons (vis_proj g' ++ ill_proj g') pf'.
Proof.
  intros g g' pf pf' Hp Hc.
  apply cons_spec. intros n f t Hin.
  apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  - apply In_vis_proj in Hin. destruct Hin as [Hing Hf].
    assert (Hing' : In ((n,f),t) g) by (exact (Permutation_in ((n,f),t) (Permutation_sym Hp) Hing)).
    assert (Hproj : In ((n,f),t) (vis_proj g ++ ill_proj g)).
    { subst f. apply in_or_app. left. apply In_vis_proj. split; auto. }
    exact (proj1 (cons_spec (vis_proj g ++ ill_proj g) pf) Hc n f t Hproj).
  - apply In_ill_proj in Hin. destruct Hin as [Hing Hf].
    assert (Hing' : In ((n,f),t) g) by (exact (Permutation_in ((n,f),t) (Permutation_sym Hp) Hing)).
    assert (Hproj : In ((n,f),t) (vis_proj g ++ ill_proj g)).
    { subst f. apply in_or_app. right. apply In_ill_proj. split; auto. }
    exact (proj1 (cons_spec (vis_proj g ++ ill_proj g) pf) Hc n f t Hproj).
Qed.


Lemma cons_perm : forall g g' pf pf', Permutation g g' -> cons g pf -> cons g' pf'.
Proof.
  intros g g' pf pf' Hp Hc. apply cons_spec. intros n f t Hin.
  apply (proj1 (cons_spec g pf) Hc n f t).
  exact (Permutation_in ((n,f),t) (Permutation_sym Hp) Hin).
Qed.

Lemma tEnv_split_perm : forall g1 g2 g3 pf1 pf2 pf3 g',
  tEnv_split g1 g2 g3 pf1 pf2 pf3 -> Permutation g3 g' ->
  NoDup (domain g3) -> NoDup (domain g1) -> NoDup (domain g2) ->
  forall pf3', tEnv_split g1 g2 g' pf1 pf2 pf3'.
Proof.
  intros g1 g2 g3 pf1 pf2 pf3 g' Hs Hp Hnd3 nd1 nd2 pf3'.
  destruct (tEnv_split_esplit _ _ _ _ _ _ Hs) as [HA [HB HC]].
  assert (Hpdom : Permutation (domain g3) (domain g')) by (apply Permutation_domain; exact Hp).
  assert (Hndg' : NoDup (domain g')) by (apply (NoDup_domain_perm g3 g' Hp); exact Hnd3).
  assert (Hes' : esplit g1 g2 g').
  { unfold esplit. split; [exact HA|]. split.
    - intros x; split; intro Hx.
      + apply (Permutation_in x Hpdom). apply (proj1 (HB x)). exact Hx.
      + apply (proj2 (HB x)). exact (Permutation_in x (Permutation_sym Hpdom) Hx).
    - intros x f1 t1 f2 t2 He1 He2.
      destruct (HC x f1 t1 f2 t2 He1 He2) as [f [t [Hg Hec]]].
      exists f, t. split; [|exact Hec].
      exact (Permutation_in ((x,f),t) Hp Hg). }
  exact (tEnv_split_pf_irrel g1 g2 g' (isMap_nodup g1 nd1) (isMap_nodup g2 nd2)
           (isMap_nodup g' Hndg') (esplit_tEnv_split g1 g2 g' (isMap_nodup g1 nd1) (isMap_nodup g2 nd2) (isMap_nodup g' Hndg') nd1 nd2 Hndg' Hes') pf1 pf2 pf3').
Qed.


Fixpoint psize (t : piType) : nat :=
  match t with Top => 1 | Chan _ _ u => S (psize u) end.

Lemma no_sub_into_self : forall t m p, ~ type_sub t (Chan m p t).
Proof.
  intros t. induction t as [m' q t0 IH | ]; intros m p H.
  - inversion H; subst.
    + assert (Hsz := f_equal psize H4); simpl in Hsz; lia.
    + assert (Hsz := f_equal psize H6); simpl in Hsz; lia.
    + assert (Hsz := f_equal psize H6); simpl in Hsz; lia.
    + assert (Hsz := f_equal psize H6); simpl in Hsz; lia.
  - inversion H.
Qed.

Lemma NoDup_domain_cons_reuse : forall n f t f' t' g,
  NoDup (domain g) -> In ((n,f),t) g ->
  NoDup (domain (((n,f'),t') :: removeEntry n g)) /\
  (forall x, In x (domain (((n,f'),t') :: removeEntry n g)) <-> In x (domain g)).
Proof.
  intros n f t f' t' g Hnd Hin. split.
  - simpl. apply NoDup_cons_iff. split.
    + apply NoDup_removeEntry_still.
      * exact Hnd.
      * apply in_dom_entry with (f:=f) (t:=t); exact Hin.
    + apply NoDup_domain_removeEntry; auto.
  - intros x. simpl. split.
    + intros [->|H]. apply in_dom_entry with (f:=f) (t:=t); exact Hin.
      apply domain_removeEntry_sub with (y:=n); exact H.
    + intro Hx. destruct (nat_pair_eq_dec x n) as [->|Hne].
      * left; reflexivity.
      * right. apply domain_removeEntry_neq; auto.
Qed.


Lemma TOutL_neq : forall g u p t t1 v t' t2,
  isMap g ->
  type_remove (Chan lin p t) (Chan lin out t) t1 ->
  type_remove t' t t2 ->
  In ((u,vis),Chan lin p t) g -> In ((v,vis),t') g ->
  u <> v.
Proof.
  intros g u p t t1 v t' t2 Hm Hr1 Hr2 Hu Hv Heq. subst v.
  assert (Ht' : t' = Chan lin p t) by
    (symmetry; exact (proj2 (Hm u vis (Chan lin p t) vis t' (conj Hu Hv)))).
  subst t'. destruct Hr2 as [Hsub _]. exact (no_sub_into_self t lin p Hsub).
Qed.

Lemma domain_out_env : forall u v g, u <> v -> In u (domain g) -> In v (domain g) ->
  Permutation (u :: v :: domain (removeEntry v (removeEntry u g))) (domain g).
Proof.
  intros u v g Hne Hu Hv.
  assert (Hvu : In v (domain (removeEntry u g))) by (apply domain_removeEntry_neq; auto).
  apply Permutation_sym. eapply perm_trans.
  - apply domain_removeEntry_perm; exact Hu.
  - apply perm_skip. apply domain_removeEntry_perm; exact Hvu.
Qed.

Lemma domain_un_env : forall v g, In v (domain g) ->
  Permutation (v :: domain (removeEntry v g)) (domain g).
Proof.
  intros. apply Permutation_sym. apply domain_removeEntry_perm; auto.
Qed.

Lemma domain_inl_env : forall u x g, u <> x -> ~ In x (domain g) -> In u (domain g) ->
  Permutation (u :: x :: domain (removeEntry u g)) (x :: domain g).
Proof.
  intros u x g Hux Hx Hu.
  eapply perm_trans.
  - apply perm_swap.
  - apply Permutation_sym. apply perm_skip. apply domain_removeEntry_perm; exact Hu.
Qed.


Lemma typeCheck_perm : forall g g' p pf pf',
  NoDup (domain g) -> Permutation g g' -> typeCheck g pf p -> typeCheck g' pf' p.
Proof.
  intros g g' p pf pf' Hnd Hp Hty. revert g' pf' Hnd Hp.
  induction Hty as [g pf Hc
    | g pf pb n t pf1 Hi Hbody IHb
    | g pf g1 g2 p1 p2 pf1 pf2 Hspl Hty1 IH1 Hty2 IH2
    | g pf u p0 t v t' q t1 t2 pf1 Hr1 Hr2 Hu Hv Hbody IHb
    | g pf u p0 t v t' q t2 pf1 Hpol Hr Hu Hv Hbody IHb
    | g pf u p0 t x q t1 pf1 Hr Hu Hfresh Hmax Hbody IHb
    | g pf u p0 t x q pf1 Hpol Hu Hfresh Hmax Hbody IHb
    | g pf u p0 t x q pf1 pf2 Hpol Hu Hfresh Hmax Hcons Hbody IHb];
    intros g' pf' Hnd Hp.
  - (* TNil *) apply TNil. apply (cons_perm g g' pf pf' Hp Hc).
  - (* TNew *)
    assert (HndE : NoDup (domain ((n,vis,t) :: removeEntry n g)))
      by exact (proj1 (NoDup_domain_cons_reuse n hid t vis t g Hnd Hi)).
    assert (HpermE : Permutation ((n,vis,t) :: removeEntry n g) ((n,vis,t) :: removeEntry n g'))
      by (apply perm_skip; apply removeEntry_perm; auto).
    assert (HndE' : NoDup (domain ((n,vis,t) :: removeEntry n g')))
      by (apply (NoDup_domain_perm _ _ HpermE); exact HndE).
    apply TNew with (n:=n) (t:=t) (pf1 := isMap_nodup ((n,vis,t)::removeEntry n g') HndE').
    + exact (Permutation_in ((n,hid),t) Hp Hi).
    + apply (IHb ((n,vis,t) :: removeEntry n g') (isMap_nodup _ HndE')).
      * exact HndE.
      * exact HpermE.
  - (* TPar *)
    destruct (tEnv_split_nodup _ _ _ _ _ _ Hspl Hnd) as [nd1 nd2].
    eapply TPar with (g1:=g1) (g2:=g2) (pf1:=pf1) (pf2:=pf2).
    + apply (tEnv_split_perm g1 g2 g pf1 pf2 pf g' Hspl Hp Hnd nd1 nd2 pf').
    + exact Hty1.
    + exact Hty2.
  - (* TOutL *)
    assert (Huin : In u (domain g)) by (apply in_dom_entry with (f:=vis) (t:=Chan lin p0 t); exact Hu).
    assert (Hvin : In v (domain g)) by (apply in_dom_entry with (f:=vis) (t:=t'); exact Hv).
    assert (Hux : u <> v) by (apply (TOutL_neq g u p0 t t1 v t' t2 pf Hr1 Hr2 Hu Hv)).
    assert (HndE : NoDup (domain ((u,vis,t1)::(v,vis,t2)::removeEntry v (removeEntry u g))))
      by (simpl; apply (NoDup_perm_list (name*name) (domain g)
            (u :: v :: domain (removeEntry v (removeEntry u g)))
            (Permutation_sym (domain_out_env u v g Hux Huin Hvin)) Hnd)).
    assert (HpermE : Permutation ((u,vis,t1)::(v,vis,t2)::removeEntry v (removeEntry u g)) ((u,vis,t1)::(v,vis,t2)::removeEntry v (removeEntry u g'))).
    { apply perm_skip. apply perm_skip. apply removeEntry_perm.
      - apply removeEntry_perm; auto.
      - apply NoDup_domain_removeEntry; auto. }
    assert (HndE' : NoDup (domain ((u,vis,t1)::(v,vis,t2)::removeEntry v (removeEntry u g'))))
      by (apply (NoDup_domain_perm _ _ HpermE); exact HndE).
    eapply TOutL with (u:=u) (p:=p0) (t:=t) (v:=v) (t':=t') (t1:=t1) (t2:=t2).
    + exact Hr1.
    + exact Hr2.
    + exact (Permutation_in ((u,vis),Chan lin p0 t) Hp Hu).
    + exact (Permutation_in ((v,vis),t') Hp Hv).
    + apply (IHb ((u,vis,t1)::(v,vis,t2)::removeEntry v (removeEntry u g')) (isMap_nodup _ HndE')).
      * exact HndE.
      * exact HpermE.
  - (* TOutUn *)
    assert (Hvin : In v (domain g)) by (apply in_dom_entry with (f:=vis) (t:=t'); exact Hv).
    assert (HndE : NoDup (domain ((v,vis,t2)::removeEntry v g)))
      by (simpl; apply (NoDup_perm_list (name*name) (domain g) (v :: domain (removeEntry v g))
            (Permutation_sym (domain_un_env v g Hvin)) Hnd)).
    assert (HpermE : Permutation ((v,vis,t2)::removeEntry v g) ((v,vis,t2)::removeEntry v g'))
      by (apply perm_skip; apply removeEntry_perm; auto).
    assert (HndE' : NoDup (domain ((v,vis,t2)::removeEntry v g')))
      by (apply (NoDup_domain_perm _ _ HpermE); exact HndE).
    eapply TOutUn with (u:=u) (p:=p0) (t:=t) (v:=v) (t':=t') (t2:=t2).
    + exact Hpol.
    + exact Hr.
    + exact (Permutation_in ((u,vis),Chan un p0 t) Hp Hu).
    + exact (Permutation_in ((v,vis),t') Hp Hv).
    + apply (IHb ((v,vis,t2)::removeEntry v g') (isMap_nodup _ HndE')).
      * exact HndE.
      * exact HpermE.
  - (* TInL *)
    assert (Huin : In u (domain g)) by (apply in_dom_entry with (f:=vis) (t:=Chan lin p0 t); exact Hu).
    assert (Hux : u <> x) by (intro H; apply Hfresh; rewrite <- H; exact Huin).
    assert (Hx' : ~ In x (domain g')) by
      (intro Hc; apply Hfresh; exact (Permutation_in x (Permutation_sym (Permutation_domain g g' Hp)) Hc)).
    assert (Hmax' : snd x < max (domain g')) by
      (rewrite <- (max_perm _ _ (Permutation_domain g g' Hp)); exact Hmax).
    assert (HndE : NoDup (domain ((u,vis,t1)::(x,vis,t)::removeEntry u g))).
    { simpl. apply (NoDup_perm_list (name*name) (x :: domain g) (u :: x :: domain (removeEntry u g))
        (Permutation_sym (domain_inl_env u x g Hux Hfresh Huin))).
      apply NoDup_cons_iff; split; auto. }
    assert (HpermE : Permutation ((u,vis,t1)::(x,vis,t)::removeEntry u g)
                               ((u,vis,t1)::(x,vis,t)::removeEntry u g'))
      by (apply perm_skip; apply perm_skip; apply removeEntry_perm; auto).
    assert (HndE' : NoDup (domain ((u,vis,t1)::(x,vis,t)::removeEntry u g')))
      by (apply (NoDup_domain_perm _ _ HpermE); exact HndE).
    eapply TInL with (u:=u) (p:=p0) (t:=t) (x:=x) (t1:=t1).
    + exact Hr.
    + exact (Permutation_in ((u,vis),Chan lin p0 t) Hp Hu).
    + exact Hx'.
    + exact Hmax'.
    + apply (IHb ((u,vis,t1)::(x,vis,t)::removeEntry u g') (isMap_nodup _ HndE')).
      * exact HndE.
      * exact HpermE.
  - (* TInUn *)
    assert (Hx' : ~ In x (domain g')) by
      (intro Hc; apply Hfresh; exact (Permutation_in x (Permutation_sym (Permutation_domain g g' Hp)) Hc)).
    assert (Hmax' : snd x < max (domain g')) by
      (rewrite <- (max_perm _ _ (Permutation_domain g g' Hp)); exact Hmax).
    assert (HndE : NoDup (domain ((x,vis,t)::g))) by (apply NoDup_cons_iff; split; auto).
    assert (HpermE : Permutation ((x,vis,t)::g) ((x,vis,t)::g')) by (apply perm_skip; exact Hp).
    assert (HndE' : NoDup (domain ((x,vis,t)::g'))) by (apply (NoDup_domain_perm _ _ HpermE); exact HndE).
    eapply TInUn with (u:=u) (p:=p0) (t:=t) (x:=x).
    + exact Hpol.
    + exact (Permutation_in ((u,vis),Chan un p0 t) Hp Hu).
    + exact Hx'.
    + exact Hmax'.
    + apply (IHb ((x,vis,t)::g') (isMap_nodup _ HndE')).
      * exact HndE.
      * exact HpermE.
  - (* TInU *)
    assert (Hx' : ~ In x (domain g')) by
      (intro Hc; apply Hfresh; exact (Permutation_in x (Permutation_sym (Permutation_domain g g' Hp)) Hc)).
    assert (Hmax' : snd x < max (domain g')) by
      (rewrite <- (max_perm _ _ (Permutation_domain g g' Hp)); exact Hmax).
    assert (HndE : NoDup (domain ((x,vis,t)::g))) by (apply NoDup_cons_iff; split; auto).
    assert (HpermE : Permutation ((x,vis,t)::g) ((x,vis,t)::g')) by (apply perm_skip; exact Hp).
    assert (HndE' : NoDup (domain ((x,vis,t)::g'))) by (apply (NoDup_domain_perm _ _ HpermE); exact HndE).
    assert (Hndg' : NoDup (domain g')) by (apply (NoDup_domain_perm g g' Hp); exact Hnd).
    eapply TInU with (u:=u) (p:=p0) (t:=t) (x:=x).
    + exact Hpol.
    + exact (Permutation_in ((u,vis),Chan un p0 t) Hp Hu).
    + exact Hx'.
    + exact Hmax'.
    + apply (cons_proj_perm g g' pf2 (isMap_proj g' (isMap_nodup g' Hndg')) Hp Hcons).
    + apply (IHb ((x,vis,t)::g') (isMap_nodup _ HndE')).
      * exact HndE.
      * exact HpermE.
Qed.

Theorem sr :
  forall g p a g' p' nd_pf pf pf',
    sl_pos p ->
    typeCheck g pf p ->
    lts g p a g' p' nd_pf ->
    typeCheck g' pf' p'.
Proof.
  admit.
Admitted.
