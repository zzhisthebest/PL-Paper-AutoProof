From Stdlib Require Import List CRelationClasses.
From Stdlib Require Import Lia.
Import ListNotations.

Set Implicit Arguments.

Notation "l · a" := (l ++ a :: nil) (at level 56, left associativity) : list_scope.
Infix "<=>" := iffT (at level 95, no associativity).

Fixpoint InT {A : Type} (a : A) (l : list A) : Type :=
  match l with
  | nil => False
  | b :: m => sum (b = a) (InT a m)
  end.

Definition Atom : Type := nat.

Inductive form := var (_ : Atom) | omega | inter (_ _ : form) | arrow (_ _ : form).

Notation Ω := omega.
Infix "∩" := inter (at level 35).
Infix "→" := arrow (right associativity, at level 39).

Reserved Notation "a ≤ b" (at level 70).

Inductive bcd_sub {lax : list (Atom -> form * form)} : crelation form :=
| bcd_identity a : a ≤ a
| bcd_trans a b c : a ≤ b -> b ≤ c -> a ≤ c
| bcd_omega_right a : a ≤ Ω
| bcd_inter_left1 a b : a ∩ b ≤ a
| bcd_inter_left2 a b : a ∩ b ≤ b
| bcd_inter_right a : a ≤ a ∩ a
| bcd_inter a b c d : a ≤ c -> b ≤ d -> a ∩ b ≤ c ∩ d
| bcd_arrow a b c d : c ≤ a -> b ≤ d -> a → b ≤ c → d
| bcd_arrow_inter a b c : (a → b) ∩ (a → c) ≤ a → b ∩ c
| bcd_arrow_omega : Ω ≤ Ω → Ω
| bcd_axiom ax x : InT ax lax -> fst (ax x) ≤ snd (ax x)
where "a ≤ b" := (bcd_sub a b).

Reserved Notation "a ❘ l ⊦ b" (at level 65, l at next level, b at next level).
Reserved Notation "a ❘ ⊦ b" (at level 65, b at next level).

Inductive sub : list form -> crelation form :=
| identity a : a ❘ ⊦ a
| omega_right a l : a ❘ l ⊦ Ω
| inter_left1 b a c l : a ❘ l ⊦ c -> a ∩ b ❘ l ⊦ c
| inter_left2 b a c l : a ❘ l ⊦ c -> b ∩ a ❘ l ⊦ c
| inter_right a b c l : c ❘ l ⊦ a -> c ❘ l ⊦ b -> c ❘ l ⊦ a ∩ b
| arrow_left a b c d l : c ❘ ⊦ a -> b ❘ l ⊦ d -> a → b ❘ c :: l ⊦ d
| arrow_right a b c l : c ❘ l · a ⊦ b -> c ❘ l ⊦ a → b
where "a ❘ l ⊦ b" := (sub l a b)
  and "a ❘ ⊦ b" := (sub nil a b).

Notation "a ⩽ b " := (@bcd_sub [] a b) (at level 70).

(* ============================================================ *)
(* Helper definitions and lemmas                                *)
(* ============================================================ *)

(* Right-associated arrow chain interpreting the sequent context *)
Fixpoint ar (l : list form) (b : form) : form :=
  match l with
  | nil => b
  | a :: l' => a → ar l' b
  end.

Lemma ar_app : forall l1 l2 b, ar (l1 ++ l2) b = ar l1 (ar l2 b).
Proof.
  induction l1; intros; simpl; auto.
  rewrite IHl1. reflexivity.
Qed.

(* Size of a type, for the well-founded induction used in cut elimination *)
Fixpoint fsize (t : form) : nat :=
  match t with
  | var _ => 1
  | omega => 1
  | inter a b => S (fsize a + fsize b)
  | arrow a b => S (fsize a + fsize b)
  end.

Lemma fsize_pos : forall t, 1 <= fsize t.
Proof. destruct t; simpl; lia. Qed.

Lemma fsize_inter_l : forall a b, fsize a < fsize (a ∩ b).
Proof. intros; simpl; lia. Qed.
Lemma fsize_inter_r : forall a b, fsize b < fsize (a ∩ b).
Proof. intros; simpl; lia. Qed.
Lemma fsize_arrow_l : forall a b, fsize a < fsize (a → b).
Proof. intros; simpl; lia. Qed.
Lemma fsize_arrow_r : forall a b, fsize b < fsize (a → b).
Proof. intros; simpl; lia. Qed.

(* A context of the shape l1 ++ [T] ++ l2 is never empty *)
Lemma app_single_cons_length : forall (l1 l2 : list form) (T : form),
  length (l1 ++ [T] ++ l2) = length l1 + 1 + length l2.
Proof. intros; rewrite length_app, length_app; simpl; lia. Qed.

Lemma app_single_not_nil : forall (l1 l2 : list form) (T : form),
  l1 ++ [T] ++ l2 <> nil.
Proof.
  intros l1 l2 T H.
  pose proof (app_single_cons_length l1 l2 T) as Hlen.
  rewrite H in Hlen. simpl in Hlen. lia.
Qed.

(* Inversion of an intersection on the right-hand side (cut-free) *)
Lemma sub_inter_r_inv : forall l x a b,
  sub l x (a ∩ b) -> sub l x a * sub l x b.
Proof.
  intros l x a b H.
  remember (a ∩ b) as T eqn:Heq.
  revert Heq.
  induction H; intros Heq.
  - (* identity *) subst. split.
    + apply inter_left1 with (b:=b). apply identity.
    + apply inter_left2 with (b:=a). apply identity.
  - (* omega_right *) discriminate Heq.
  - (* inter_left1 *) destruct (IHsub Heq) as [H1 H2]. split.
    + apply inter_left1 with (b:=b0). exact H1.
    + apply inter_left1 with (b:=b0). exact H2.
  - (* inter_left2 *) destruct (IHsub Heq) as [H1 H2]. split.
    + apply inter_left2 with (b:=b0). exact H1.
    + apply inter_left2 with (b:=b0). exact H2.
  - (* inter_right *) injection Heq as Ha Hb. subst. split; assumption.
  - (* arrow_left *) destruct (IHsub2 Heq) as [H1 H2]. split.
    + apply arrow_left with (a:=a0) (b:=b0); assumption.
    + apply arrow_left with (a:=a0) (b:=b0); assumption.
  - (* arrow_right *) discriminate Heq.
Qed.

(* Inversion of an arrow on the right-hand side (cut-free) *)
Lemma sub_arrow_r_inv : forall l x a b,
  sub l x (a → b) -> sub (l · a) x b.
Proof.
  intros l x a b H.
  remember (a → b) as T eqn:Heq.
  revert Heq.
  induction H; intros Heq.
  - (* identity *) subst. simpl.
    apply arrow_left with (a:=a) (b:=b); apply identity.
  - (* omega_right *) discriminate Heq.
  - (* inter_left1 *) apply inter_left1 with (b:=b0). apply IHsub. exact Heq.
  - (* inter_left2 *) apply inter_left2 with (b:=b0). apply IHsub. exact Heq.
  - (* inter_right *) discriminate Heq.
  - (* arrow_left *) apply arrow_left with (a:=a0) (b:=b0).
    + assumption.
    + apply IHsub2. exact Heq.
  - (* arrow_right *) injection Heq as Ha Hb. subst. assumption.
Qed.

(* If the sequent has Ω on the left, then any type may replace it
   (cut-free). *)
Lemma sub_omega_lhs : forall l2 c,
  sub l2 Ω c -> forall l1 a, sub (l1 ++ l2) a c.
Proof.
  intros l2 c H.
  remember Ω as T eqn:Heq.
  revert Heq.
  induction H; intros Heq l1' a'.
  - (* identity *) subst. rewrite app_nil_r. apply omega_right.
  - (* omega_right *) apply omega_right.
  - (* inter_left1 *) discriminate Heq.
  - (* inter_left2 *) discriminate Heq.
  - (* inter_right *) apply inter_right.
    + apply IHsub1. exact Heq.
    + apply IHsub2. exact Heq.
  - (* arrow_left *) discriminate Heq.
  - (* arrow_right *) apply arrow_right. rewrite <- app_assoc.
    apply IHsub. exact Heq.
Qed.

(* Statement of cut at a fixed type *)
Definition cut_stmt (T : form) : Type :=
  forall (l1 l2 : list form) (a c : form),
    sub l1 a T -> sub l2 T c -> sub (l1 ++ l2) a c.

(* Statement of context replacement at a fixed type *)
Definition ctx_stmt (T : form) : Type :=
  forall (l1 l2 : list form) (x a c : form),
    sub nil x T -> sub (l1 ++ [T] ++ l2) a c -> sub (l1 ++ [x] ++ l2) a c.

(* Intersection on the left of the second derivation, using cuts at the
   two components (which are strictly smaller types). *)
Lemma sub_inter_lhs : forall x y,
  cut_stmt x -> cut_stmt y ->
  forall l2 c, sub l2 (x ∩ y) c ->
  forall l1 a, sub l1 a x -> sub l1 a y -> sub (l1 ++ l2) a c.
Proof.
  intros x y CUTx CUTy l2 c H.
  remember (x ∩ y) as T eqn:Heq.
  revert Heq.
  induction H; intros Heq l1' a' Hx Hy.
  - (* identity *) subst. rewrite app_nil_r. apply inter_right; assumption.
  - (* omega_right *) apply omega_right.
  - (* inter_left1 *) injection Heq as Ha Hb. subst.
    eapply CUTx; [ exact Hx | exact H ].
  - (* inter_left2 *) injection Heq as Ha Hb. subst.
    eapply CUTy; [ exact Hy | exact H ].
  - (* inter_right *) subst.
    apply inter_right.
    + apply IHsub1. reflexivity. assumption. assumption.
    + apply IHsub2. reflexivity. assumption. assumption.
  - (* arrow_left *) discriminate Heq.
  - (* arrow_right *) subst. apply arrow_right. rewrite <- app_assoc.
    apply IHsub. reflexivity. assumption. assumption.
Qed.

(* Auxiliary form of context replacement, convenient for induction *)
Lemma ctx_aux : forall T, cut_stmt T ->
  forall l a c, sub l a c ->
  forall l1 l2 x, l = l1 ++ [T] ++ l2 -> sub nil x T -> sub (l1 ++ [x] ++ l2) a c.
Proof.
  intros T CUT l a c H.
  induction H; intros l1 l2 x Heq Hxy.
  - (* identity *) destruct (app_single_not_nil l1 l2 T (eq_sym Heq)).
  - (* omega_right *) apply omega_right.
  - (* inter_left1 *) apply inter_left1 with (b:=b). apply IHsub; assumption.
  - (* inter_left2 *) apply inter_left2 with (b:=b). apply IHsub; assumption.
  - (* inter_right *) apply inter_right.
    + apply IHsub1; assumption.
    + apply IHsub2; assumption.
  - (* arrow_left *) destruct l1 as [|c0 l1'].
    + simpl in Heq. injection Heq as Hc Hl. subst.
      apply arrow_left with (a:=a) (b:=b).
      * apply CUT with (l1:=nil) (l2:=nil) (a:=x) (c:=a).
        -- exact Hxy.
        -- exact H.
      * exact H0.
    + simpl in Heq. injection Heq as Hc Hl. subst.
      apply arrow_left with (a:=a) (b:=b).
      * exact H.
      * apply IHsub2. reflexivity. exact Hxy.
  - (* arrow_right *) apply arrow_right.
    repeat rewrite <- app_assoc.
    apply (IHsub l1 (l2 · a) x).
    + rewrite Heq. repeat rewrite <- app_assoc. reflexivity.
    + exact Hxy.
Qed.

Lemma ctx_of_cut : forall T, cut_stmt T -> ctx_stmt T.
Proof.
  intros T CUT l1 l2 x a c Hxy H.
  apply (@ctx_aux T CUT (l1 ++ [T] ++ l2) a c H l1 l2 x eq_refl Hxy).
Qed.

(* Cut at an arrow type, using cut at the codomain and context
   replacement at the domain. *)
Lemma cut_arrow_aux : forall u v, cut_stmt v -> ctx_stmt u ->
  forall l2 T y, sub l2 T y -> T = (u → v) ->
  forall l1 x, sub l1 x (u → v) -> sub (l1 ++ l2) x y.
Proof.
  intros u v CUTv CTXu l2 T y H2.
  induction H2; intros Heq l1 x H1.
  - (* identity *) subst. rewrite app_nil_r. exact H1.
  - (* omega_right *) apply omega_right.
  - (* inter_left1 *) discriminate Heq.
  - (* inter_left2 *) discriminate Heq.
  - (* inter_right *) subst. apply inter_right.
    + apply IHsub1. reflexivity. exact H1.
    + apply IHsub2. reflexivity. exact H1.
  - (* arrow_left *) injection Heq as Ha Hb. subst.
    pose proof (sub_arrow_r_inv H1) as Hinv.
    pose proof (CUTv _ _ _ _ Hinv H2_0) as Hcut.
    rewrite <- app_assoc in Hcut.
    change (sub (l1 ++ [c] ++ l) x d).
    eapply CTXu.
    + exact H2_.
    + apply Hcut.
  - (* arrow_right *) subst. apply arrow_right. rewrite <- app_assoc.
    apply IHsub. reflexivity. exact H1.
Qed.

(* The main cut-elimination result: cut at any type, established together
   with context replacement at the same type, by induction on type size. *)
Lemma cut_ctx_all : forall T, cut_stmt T * ctx_stmt T.
Proof.
  assert (Hall : forall n T, fsize T <= n -> cut_stmt T * ctx_stmt T).
  { intros n. induction n as [|n IHn]; intros T Hle.
  - exfalso. pose proof (fsize_pos T). lia.
  - destruct T as [i | | u v | u v].
    + (* T = var i *)
      assert (CUT : cut_stmt (var i)).
      { intros l1 l2 x y H1 H2. revert l2 y H2.
        remember (var i) as Teq eqn:Heq.
        induction H1; intros l2 y H2.
        - (* identity *) subst. simpl. exact H2.
        - (* omega_right *) discriminate Heq.
        - (* inter_left1 *) apply inter_left1 with (b:=b). apply IHsub; assumption.
        - (* inter_left2 *) apply inter_left2 with (b:=b). apply IHsub; assumption.
        - (* inter_right *) discriminate Heq.
        - (* arrow_left *) apply arrow_left with (a:=a) (b:=b).
          * exact H1_.
          * apply IHsub2; assumption.
        - (* arrow_right *) discriminate Heq. }
      split; [exact CUT | apply ctx_of_cut; exact CUT].
    + (* T = omega *)
      assert (CUT : cut_stmt Ω).
      { intros l1 l2 x y H1 H2. revert l2 y H2.
        remember Ω as Teq eqn:Heq.
        induction H1; intros l2 y H2.
        - (* identity *) subst. simpl. exact H2.
        - (* omega_right *) apply (sub_omega_lhs H2).
        - (* inter_left1 *) apply inter_left1 with (b:=b). apply IHsub; assumption.
        - (* inter_left2 *) apply inter_left2 with (b:=b). apply IHsub; assumption.
        - (* inter_right *) discriminate Heq.
        - (* arrow_left *) apply arrow_left with (a:=a) (b:=b).
          * exact H1_.
          * apply IHsub2; assumption.
        - (* arrow_right *) discriminate Heq. }
      split; [exact CUT | apply ctx_of_cut; exact CUT].
    + (* T = u ∩ v *)
      assert (Hsu : fsize u <= n) by (cbn [fsize] in Hle; lia).
      assert (Hsv : fsize v <= n) by (cbn [fsize] in Hle; lia).
      assert (CUT : cut_stmt (u ∩ v)).
      { intros l1 l2 x y H1 H2. revert l2 y H2.
        remember (u ∩ v) as Teq eqn:Heq.
        induction H1; intros l2 y H2.
        - (* identity *) subst. simpl. exact H2.
        - (* omega_right *) discriminate Heq.
        - (* inter_left1 *) apply inter_left1 with (b:=b). apply IHsub; assumption.
        - (* inter_left2 *) apply inter_left2 with (b:=b). apply IHsub; assumption.
        - (* inter_right *) injection Heq as Ha Hb. subst.
          exact (@sub_inter_lhs u v (fst (IHn u Hsu)) (fst (IHn v Hsv))
                   l2 y H2 l c H1_ H1_0).
        - (* arrow_left *) apply arrow_left with (a:=a) (b:=b).
          * exact H1_.
          * apply IHsub2; assumption.
        - (* arrow_right *) discriminate Heq. }
      split; [exact CUT | apply ctx_of_cut; exact CUT].
    + (* T = u → v *)
      assert (Hsu : fsize u <= n) by (cbn [fsize] in Hle; lia).
      assert (Hsv : fsize v <= n) by (cbn [fsize] in Hle; lia).
      assert (CUT : cut_stmt (u → v)).
      { intros l1 l2 x y H1 H2.
        apply (@cut_arrow_aux u v (fst (IHn v Hsv)) (snd (IHn u Hsu))
                 l2 (u → v) y H2 eq_refl l1 x H1). }
      split; [exact CUT | apply ctx_of_cut; exact CUT]. }
  intros T. apply (Hall (fsize T) T). lia.
Qed.


(* Cut, obtained from the well-founded development above *)
Lemma sub_cut : forall (l1 l2 : list form) (a b c : form),
  sub l1 a b -> sub l2 b c -> sub (l1 ++ l2) a c.
Proof.
  intros l1 l2 a b c H1 H2.
  exact (fst (cut_ctx_all b) l1 l2 a c H1 H2).
Qed.

(* Corollary: transitivity of the sequent judgment at empty context *)
Lemma sub_nil_trans : forall a b c, sub nil a b -> sub nil b c -> sub nil a c.
Proof.
  intros a b c H1 H2.
  apply (@sub_cut nil nil a b c H1 H2).
Qed.

(* ============================================================ *)
(* Soundness: sequent derivations yield BCD subtyping           *)
(* ============================================================ *)

Lemma bcd_ar_mono : forall l a b, a ⩽ b -> ar l a ⩽ ar l b.
Proof.
  induction l as [|c l IHl]; intros a b Hab; simpl.
  - exact Hab.
  - apply bcd_arrow.
    + apply bcd_identity.
    + apply IHl. exact Hab.
Qed.

Lemma bcd_omega_ar : forall l a, a ⩽ ar l Ω.
Proof.
  induction l as [|c l IHl]; intros a; simpl.
  - apply bcd_omega_right.
  - apply bcd_trans with (b := Ω → Ω).
    + apply bcd_trans with (b := Ω).
      * apply bcd_omega_right.
      * apply bcd_arrow_omega.
    + apply bcd_arrow.
      * apply bcd_omega_right.
      * apply IHl.
Qed.

Lemma bcd_inter_ar : forall l a b, (ar l a) ∩ (ar l b) ⩽ ar l (a ∩ b).
Proof.
  induction l as [|c l IHl]; intros a b; simpl.
  - apply bcd_identity.
  - apply bcd_trans with (b := c → ar l a ∩ ar l b).
    + apply bcd_arrow_inter.
    + apply bcd_arrow.
      * apply bcd_identity.
      * apply IHl.
Qed.

Lemma sub_to_bcd_gen : forall (l : list form) (a b : form),
  sub l a b -> a ⩽ ar l b.
Proof.
  intros l a b H.
  induction H; simpl.
  - (* identity *) apply bcd_identity.
  - (* omega_right *) apply bcd_omega_ar.
  - (* inter_left1 *) apply bcd_trans with (b := a).
    + apply bcd_inter_left1.
    + assumption.
  - (* inter_left2 *) apply bcd_trans with (b := a).
    + apply bcd_inter_left2.
    + assumption.
  - (* inter_right *)
    apply bcd_trans with (b := c ∩ c).
    + apply bcd_inter_right.
    + apply bcd_trans with (b := (ar l a) ∩ (ar l b)).
      * apply bcd_inter; assumption.
      * apply bcd_inter_ar.
  - (* arrow_left *) apply bcd_arrow.
    + assumption.
    + assumption.
  - (* arrow_right *) rewrite ar_app in IHsub. exact IHsub.
Qed.

(* ============================================================ *)
(* Completeness: BCD subtyping yields sequent derivations       *)
(* ============================================================ *)

Lemma bcd_to_sub : forall a b, a ⩽ b -> sub nil a b.
Proof.
  intros a b H.
  induction H.
  - (* bcd_identity *) apply identity.
  - (* bcd_trans *) apply sub_nil_trans with (b := b); assumption.
  - (* bcd_omega_right *) apply omega_right.
  - (* bcd_inter_left1 *) apply inter_left1 with (b := b). apply identity.
  - (* bcd_inter_left2 *) apply inter_left2 with (b := a). apply identity.
  - (* bcd_inter_right *) apply inter_right; apply identity.
  - (* bcd_inter *) apply inter_right.
    + apply inter_left1 with (b := b). assumption.
    + apply inter_left2 with (b := a). assumption.
  - (* bcd_arrow *) apply arrow_right with (a := c).
    apply arrow_left with (c := c) (d := d); assumption.
  - (* bcd_arrow_inter *) apply arrow_right with (a := a).
    apply inter_right.
    + apply inter_left1 with (b := a → c).
      apply arrow_left with (a := a) (b := b) (c := a) (d := b); apply identity.
    + apply inter_left2 with (b := a → b).
      apply arrow_left with (a := a) (b := c) (c := a) (d := c); apply identity.
  - (* bcd_arrow_omega *) apply arrow_right with (a := Ω).
    apply omega_right.
  - (* bcd_axiom *) cbn in i. destruct i.
Qed.

(* The target theorem *)
Theorem is_bcd_equiv a b : a ⩽ b <=> a ❘ ⊦ b.
Proof.
  split.
  - apply bcd_to_sub.
  - intros H. apply (sub_to_bcd_gen H).
Qed.

