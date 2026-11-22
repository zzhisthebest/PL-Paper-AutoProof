Require Export Qual.typing.

Require Import Lia.
Require Import Program.Equality.

Set Implicit Arguments.

Open Scope grade_scope.

Fixpoint erasure (phi : grade) (a:tm)  : tm :=
  match a with
  | a_TyUnit => a_TyUnit
  | a_TmUnit => a_TmUnit
  | (a_Pi psi A B) => a_Pi psi (erasure phi A) (erasure phi B)
  | (a_Abs psi A a) =>
      if q_leb q_Top phi then
        a_Abs psi (erasure phi A) (erasure phi a)
      else
        a_Abs psi a_TmUnit (erasure phi a)
  | (a_App a psi b) =>
      if q_leb psi phi then
        a_App (erasure phi a) psi (erasure phi b)
      else
        a_App (erasure phi a) psi a_TmUnit
  | (a_Type s) => a_Type s
  | (a_Var_b nat) => a_Var_b nat
  | (a_Var_f x) => a_Var_f x
  | (a_Sum A1 A2) => a_Sum (erasure phi A1) (erasure phi A2)
  | (a_Inj1 a) => a_Inj1 (erasure phi a)
  | (a_Inj2 a) => a_Inj2 (erasure phi a)
  | (a_Case psi a b1 b2) => a_Case psi (erasure phi a) (erasure phi b1) (erasure phi b2)
  | (a_WSigma psi A B) => a_WSigma psi (erasure phi A) (erasure phi B)
  | (a_WPair a psi b) =>
      if q_leb psi phi then
        a_WPair (erasure phi a) psi (erasure phi b)
      else
        a_WPair a_TmUnit psi (erasure phi b)
  | (a_LetPair psi a b) => a_LetPair psi (erasure phi a) (erasure phi b)
  | (a_SSigma psi A B) => a_SSigma psi (erasure phi A) (erasure phi B)
  | (a_SPair a psi b) =>
      if q_leb psi phi then
        a_SPair (erasure phi a) psi (erasure phi b)
      else
        a_SPair a_TmUnit psi (erasure phi b)
  | (a_Proj1 psi a) => a_Proj1 psi (erasure phi a)
  | (a_Proj2 psi a) => a_Proj2 psi (erasure phi a)
end.

(* ================================================================ *)
(* Auxiliary facts about the grade order                            *)
(* ================================================================ *)

Lemma leq_Bot_l : forall a, q_Bot <= a.
Proof.
  intro a. unfold le.
  apply (leq_meet q_Bot a).
  rewrite (meet_comm q_Bot a). apply (meet_Bot_r a).
Qed.

Lemma leq_refl_g : forall a, a <= a.
Proof.
  intro a. unfold le.
  apply (leq_join a a). apply join_idem.
Qed.

Lemma leb_true_le : forall a b, (a <=? b) = true -> a <= b.
Proof. intros a b H. apply (proj1 (leb_leq a b)); assumption. Qed.

Lemma leb_false_nle : forall a b, (a <=? b) = false -> ~ (a <= b).
Proof.
  intros a b H Hle. apply (proj2 (leb_leq a b)) in Hle.
  rewrite Hle in H. discriminate.
Qed.

(* ================================================================ *)
(* Opening a term simultaneously at several de Bruijn indices       *)
(* ================================================================ *)

(* [open_atoms p xs a] replaces, successively, the variable of index [p]
   by the atoms in [xs]; the n-th opening targets the original index [p+n]
   because opening shifts the higher indices down. *)
Fixpoint open_atoms (p:nat) (xs:list atom) (a:tm) : tm :=
  match xs with
  | nil => a
  | x :: xs' => open_atoms p xs' (open_tm_wrt_tm_rec p (a_Var_f x) a)
  end.

Lemma open_atoms_var_f : forall p xs x,
  open_atoms p xs (a_Var_f x) = a_Var_f x.
Proof.
  intros p xs. induction xs as [|y ys IH]; intro x; simpl.
  - reflexivity.
  - apply IH.
Qed.

Lemma open_atoms_tyunit : forall p xs,
  open_atoms p xs a_TyUnit = a_TyUnit.
Proof.
  intros p xs. induction xs as [|y ys IH]; simpl; [reflexivity|assumption].
Qed.

Lemma open_atoms_tmunit : forall p xs,
  open_atoms p xs a_TmUnit = a_TmUnit.
Proof.
  intros p xs. induction xs as [|y ys IH]; simpl; [reflexivity|assumption].
Qed.

Lemma open_atoms_type : forall p xs s,
  open_atoms p xs (a_Type s) = a_Type s.
Proof.
  intros p xs s. induction xs as [|y ys IH]; simpl; [reflexivity|apply IH].
Qed.

Lemma open_atoms_app : forall p xs g a b,
  open_atoms p xs (a_App a g b) =
  a_App (open_atoms p xs a) g (open_atoms p xs b).
Proof.
  intros p xs. induction xs as [|y ys IH]; intros g a b; simpl.
  - reflexivity.
  - rewrite (IH g (open_tm_wrt_tm_rec p (a_Var_f y) a)
                (open_tm_wrt_tm_rec p (a_Var_f y) b)).
    reflexivity.
Qed.

Lemma open_atoms_sum : forall p xs A1 A2,
  open_atoms p xs (a_Sum A1 A2) =
  a_Sum (open_atoms p xs A1) (open_atoms p xs A2).
Proof.
  intros p xs. induction xs as [|y ys IH]; intros A1 A2; simpl.
  - reflexivity.
  - rewrite (IH (open_tm_wrt_tm_rec p (a_Var_f y) A1)
                (open_tm_wrt_tm_rec p (a_Var_f y) A2)).
    reflexivity.
Qed.

Lemma open_atoms_inj1 : forall p xs a,
  open_atoms p xs (a_Inj1 a) = a_Inj1 (open_atoms p xs a).
Proof.
  intros p xs. induction xs as [|y ys IH]; intro a; simpl.
  - reflexivity.
  - rewrite (IH (open_tm_wrt_tm_rec p (a_Var_f y) a)). reflexivity.
Qed.

Lemma open_atoms_inj2 : forall p xs a,
  open_atoms p xs (a_Inj2 a) = a_Inj2 (open_atoms p xs a).
Proof.
  intros p xs. induction xs as [|y ys IH]; intro a; simpl.
  - reflexivity.
  - rewrite (IH (open_tm_wrt_tm_rec p (a_Var_f y) a)). reflexivity.
Qed.

Lemma open_atoms_case : forall p xs g a b1 b2,
  open_atoms p xs (a_Case g a b1 b2) =
  a_Case g (open_atoms p xs a) (open_atoms p xs b1) (open_atoms p xs b2).
Proof.
  intros p xs. induction xs as [|y ys IH]; intros g a b1 b2; simpl.
  - reflexivity.
  - rewrite (IH g (open_tm_wrt_tm_rec p (a_Var_f y) a)
                 (open_tm_wrt_tm_rec p (a_Var_f y) b1)
                 (open_tm_wrt_tm_rec p (a_Var_f y) b2)).
    reflexivity.
Qed.

Lemma open_atoms_wpair : forall p xs a g b,
  open_atoms p xs (a_WPair a g b) =
  a_WPair (open_atoms p xs a) g (open_atoms p xs b).
Proof.
  intros p xs. induction xs as [|y ys IH]; intros a g b; simpl.
  - reflexivity.
  - rewrite (IH (open_tm_wrt_tm_rec p (a_Var_f y) a) g
                (open_tm_wrt_tm_rec p (a_Var_f y) b)).
    reflexivity.
Qed.

Lemma open_atoms_spair : forall p xs a g b,
  open_atoms p xs (a_SPair a g b) =
  a_SPair (open_atoms p xs a) g (open_atoms p xs b).
Proof.
  intros p xs. induction xs as [|y ys IH]; intros a g b; simpl.
  - reflexivity.
  - rewrite (IH (open_tm_wrt_tm_rec p (a_Var_f y) a) g
                (open_tm_wrt_tm_rec p (a_Var_f y) b)).
    reflexivity.
Qed.

Lemma open_atoms_proj1 : forall p xs g a,
  open_atoms p xs (a_Proj1 g a) = a_Proj1 g (open_atoms p xs a).
Proof.
  intros p xs. induction xs as [|y ys IH]; intros g a; simpl.
  - reflexivity.
  - rewrite (IH g (open_tm_wrt_tm_rec p (a_Var_f y) a)). reflexivity.
Qed.

Lemma open_atoms_proj2 : forall p xs g a,
  open_atoms p xs (a_Proj2 g a) = a_Proj2 g (open_atoms p xs a).
Proof.
  intros p xs. induction xs as [|y ys IH]; intros g a; simpl.
  - reflexivity.
  - rewrite (IH g (open_tm_wrt_tm_rec p (a_Var_f y) a)). reflexivity.
Qed.

Lemma open_atoms_pi : forall p xs g A B,
  open_atoms p xs (a_Pi g A B) =
  a_Pi g (open_atoms p xs A) (open_atoms (S p) xs B).
Proof.
  intros p xs. induction xs as [|y ys IH]; intros g A B; simpl.
  - reflexivity.
  - rewrite (IH g (open_tm_wrt_tm_rec p (a_Var_f y) A)
                 (open_tm_wrt_tm_rec (S p) (a_Var_f y) B)).
    reflexivity.
Qed.

Lemma open_atoms_abs : forall p xs g A b,
  open_atoms p xs (a_Abs g A b) =
  a_Abs g (open_atoms p xs A) (open_atoms (S p) xs b).
Proof.
  intros p xs. induction xs as [|y ys IH]; intros g A b; simpl.
  - reflexivity.
  - rewrite (IH g (open_tm_wrt_tm_rec p (a_Var_f y) A)
                 (open_tm_wrt_tm_rec (S p) (a_Var_f y) b)).
    reflexivity.
Qed.

Lemma open_atoms_wsigma : forall p xs g A B,
  open_atoms p xs (a_WSigma g A B) =
  a_WSigma g (open_atoms p xs A) (open_atoms (S p) xs B).
Proof.
  intros p xs. induction xs as [|y ys IH]; intros g A B; simpl.
  - reflexivity.
  - rewrite (IH g (open_tm_wrt_tm_rec p (a_Var_f y) A)
                 (open_tm_wrt_tm_rec (S p) (a_Var_f y) B)).
    reflexivity.
Qed.

Lemma open_atoms_ssigma : forall p xs g A B,
  open_atoms p xs (a_SSigma g A B) =
  a_SSigma g (open_atoms p xs A) (open_atoms (S p) xs B).
Proof.
  intros p xs. induction xs as [|y ys IH]; intros g A B; simpl.
  - reflexivity.
  - rewrite (IH g (open_tm_wrt_tm_rec p (a_Var_f y) A)
                 (open_tm_wrt_tm_rec (S p) (a_Var_f y) B)).
    reflexivity.
Qed.

Lemma open_atoms_letpair : forall p xs g a b,
  open_atoms p xs (a_LetPair g a b) =
  a_LetPair g (open_atoms p xs a) (open_atoms (S p) xs b).
Proof.
  intros p xs. induction xs as [|y ys IH]; intros g a b; simpl.
  - reflexivity.
  - rewrite (IH g (open_tm_wrt_tm_rec p (a_Var_f y) a)
                 (open_tm_wrt_tm_rec (S p) (a_Var_f y) b)).
    reflexivity.
Qed.

Lemma open_rec_var_b_lt : forall (k:nat) (v:tm) (n:nat), (n < k)%nat ->
  open_tm_wrt_tm_rec k v (a_Var_b n) = a_Var_b n.
Proof.
  intros k v n H. simpl.
  destruct (lt_eq_lt_dec n k) as [[Hlt|Heq]|Hgt]; try lia; reflexivity.
Qed.

Lemma open_rec_var_b_eq : forall (k:nat) (v:tm),
  open_tm_wrt_tm_rec k v (a_Var_b k) = v.
Proof.
  intros k v. simpl.
  destruct (lt_eq_lt_dec k k) as [[Hlt|Heq]|Hgt]; try lia; reflexivity.
Qed.

Lemma open_rec_var_b_gt : forall (k:nat) (v:tm) (n:nat), (n > k)%nat ->
  open_tm_wrt_tm_rec k v (a_Var_b n) = a_Var_b (n-1).
Proof.
  intros k v n H. simpl.
  destruct (lt_eq_lt_dec n k) as [[Hlt|Heq]|Hgt]; try lia; reflexivity.
Qed.

Lemma open_rec_rec_comm : forall (k:nat) (v w:atom) (B:tm),
  open_tm_wrt_tm_rec k (a_Var_f v) (open_tm_wrt_tm_rec (S k) (a_Var_f w) B) =
  open_tm_wrt_tm_rec k (a_Var_f w) (open_tm_wrt_tm_rec k (a_Var_f v) B).
Proof.
  intros k v w B. revert k.
  induction B; intros k.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. f_equal. apply IHB1. apply IHB2.
  - simpl. f_equal. apply IHB1. apply IHB2.
  - simpl. f_equal. apply IHB1. apply IHB2.
  - simpl. reflexivity.
  - (* a_Var_b n *)
    destruct (lt_eq_lt_dec n k) as [[Hlt|Heq]|Hgt].
    + assert (E1 : open_tm_wrt_tm_rec (S k) (a_Var_f w) (a_Var_b n) = a_Var_b n)
        by (apply open_rec_var_b_lt; lia).
      assert (E2 : open_tm_wrt_tm_rec k (a_Var_f v) (a_Var_b n) = a_Var_b n)
        by (apply open_rec_var_b_lt; lia).
      assert (E3 : open_tm_wrt_tm_rec k (a_Var_f w) (a_Var_b n) = a_Var_b n)
        by (apply open_rec_var_b_lt; lia).
      rewrite E1, E2, E3. reflexivity.
    + subst n.
      assert (E1 : open_tm_wrt_tm_rec (S k) (a_Var_f w) (a_Var_b k) = a_Var_b k)
        by (apply open_rec_var_b_lt; lia).
      assert (E2 : open_tm_wrt_tm_rec k (a_Var_f v) (a_Var_b k) = a_Var_f v)
        by (apply open_rec_var_b_eq).
      assert (E3 : open_tm_wrt_tm_rec k (a_Var_f w) (a_Var_f v) = a_Var_f v)
        by reflexivity.
      rewrite E1, E2, E3. reflexivity.
    + destruct (lt_eq_lt_dec n (S k)) as [[Hlt2|Heq2]|Hgt2].
      * lia.
      * subst n.
        assert (E1 : open_tm_wrt_tm_rec (S k) (a_Var_f w) (a_Var_b (S k)) = a_Var_f w)
          by (apply open_rec_var_b_eq).
        assert (E2 : open_tm_wrt_tm_rec k (a_Var_f v) (a_Var_b (S k)) = a_Var_b (S k - 1))
          by (apply open_rec_var_b_gt; lia).
        assert (E3 : open_tm_wrt_tm_rec k (a_Var_f w) (a_Var_b (S k - 1)) = a_Var_f w).
        { replace (S k - 1) with k by (lia). apply open_rec_var_b_eq. }
        assert (E4 : open_tm_wrt_tm_rec k (a_Var_f v) (a_Var_f w) = a_Var_f w)
          by reflexivity.
        rewrite E1, E4, E2, E3. reflexivity.
      * assert (E1 : open_tm_wrt_tm_rec (S k) (a_Var_f w) (a_Var_b n) = a_Var_b (n-1))
          by (apply open_rec_var_b_gt; lia).
        assert (E2 : open_tm_wrt_tm_rec k (a_Var_f v) (a_Var_b n) = a_Var_b (n-1))
          by (apply open_rec_var_b_gt; lia).
        assert (E3 : open_tm_wrt_tm_rec k (a_Var_f v) (a_Var_b (n-1)) = a_Var_b (n-1-1))
          by (apply open_rec_var_b_gt; lia).
        assert (E4 : open_tm_wrt_tm_rec k (a_Var_f w) (a_Var_b (n-1)) = a_Var_b (n-1-1))
          by (apply open_rec_var_b_gt; lia).
        rewrite E1, E2, E3, E4. reflexivity.
  - simpl. reflexivity.
  - simpl. f_equal. apply IHB1. apply IHB2.
  - simpl. f_equal. apply IHB.
  - simpl. f_equal. apply IHB.
  - simpl. f_equal. apply IHB1. apply IHB2. apply IHB3.
  - simpl. f_equal. apply IHB1. apply IHB2.
  - simpl. f_equal. apply IHB1. apply IHB2.
  - simpl. f_equal. apply IHB1. apply IHB2.
  - simpl. f_equal. apply IHB1. apply IHB2.
  - simpl. f_equal. apply IHB1. apply IHB2.
  - simpl. f_equal. apply IHB.
  - simpl. f_equal. apply IHB.
Qed.

Lemma open_rec_open_atoms : forall (k:nat) (v:atom) xs B,
  open_tm_wrt_tm_rec k (a_Var_f v) (open_atoms (S k) xs B) =
  open_atoms k (v :: xs) B.
Proof.
  intros k v xs. induction xs as [|x xs IH]; intro B; simpl.
  - reflexivity.
  - rewrite IH. simpl. rewrite (open_rec_rec_comm k v x B). reflexivity.
Qed.


Lemma open_var_open_atoms : forall (v:atom) xs (B:tm),
  open_tm_wrt_tm (open_atoms (S 0) xs B) (a_Var_f v) = open_atoms 0 (v::xs) B.
Proof.
  intros. unfold open_tm_wrt_tm. apply open_rec_open_atoms.
Qed.

Lemma open_atoms_var_b_ge : forall (p:nat) (xs:list atom) (n:nat),
  (p + length xs <= n)%nat ->
  open_atoms p xs (a_Var_b n) = a_Var_b (n - length xs).
Proof.
  intros p xs. induction xs as [|x xs IH]; intros n Hge.
  - simpl. f_equal. lia.
  - simpl in Hge.
    assert (Hgt : (p < n)%nat) by (lia).
    change (open_atoms p xs (open_tm_wrt_tm_rec p (a_Var_f x) (a_Var_b n)) =
            a_Var_b (n - S (length xs))).
    rewrite (@open_rec_var_b_gt p (a_Var_f x) n Hgt).
    assert (HIH : open_atoms p xs (a_Var_b (n-1)) = a_Var_b ((n-1) - length xs)).
    { apply IH. lia. }
    rewrite HIH. f_equal. lia.
Qed.

Lemma open_atoms_var_b_mid : forall (p:nat) (xs:list atom) (n:nat),
  (p <= n)%nat -> (n < p + length xs)%nat ->
  exists x, open_atoms p xs (a_Var_b n) = a_Var_f x.
Proof.
  intros p xs. induction xs as [|x xs IH]; intros n Hle Hlt.
  - simpl in Hlt. lia.
  - simpl in Hlt.
    change (exists x0, open_atoms p xs (open_tm_wrt_tm_rec p (a_Var_f x) (a_Var_b n)) = a_Var_f x0).
    destruct (lt_eq_lt_dec n p) as [[Hlt2|Heq]|Hgt].
    + lia.
    + subst n.
      exists x. rewrite (@open_rec_var_b_eq p (a_Var_f x)).
      apply open_atoms_var_f.
    + assert (Hgt' : (p < n)%nat) by (lia).
      rewrite (@open_rec_var_b_gt p (a_Var_f x) n Hgt').
      destruct (IH (n-1)) as [y Hy]; [lia|lia|].
      exists y. rewrite Hy. reflexivity.
Qed.

(* Inversion lemmas for local closure, one per binder/compound constructor *)
Lemma lc_tm_Pi_inv : forall g A B, lc_tm (a_Pi g A B) ->
  lc_tm A /\ (forall x, lc_tm (open_tm_wrt_tm B (a_Var_f x))).
Proof. intros g A B H. inversion H. split; assumption. Qed.

Lemma lc_tm_Abs_inv : forall g A b, lc_tm (a_Abs g A b) ->
  lc_tm A /\ (forall x, lc_tm (open_tm_wrt_tm b (a_Var_f x))).
Proof. intros g A b H. inversion H. split; assumption. Qed.

Lemma lc_tm_App_inv : forall a g b, lc_tm (a_App a g b) -> lc_tm a /\ lc_tm b.
Proof. intros a g b H. inversion H. split; assumption. Qed.

Lemma lc_tm_Sum_inv : forall A1 A2, lc_tm (a_Sum A1 A2) -> lc_tm A1 /\ lc_tm A2.
Proof. intros A1 A2 H. inversion H. split; assumption. Qed.

Lemma lc_tm_Inj1_inv : forall a, lc_tm (a_Inj1 a) -> lc_tm a.
Proof. intros a H. inversion H. assumption. Qed.

Lemma lc_tm_Inj2_inv : forall a, lc_tm (a_Inj2 a) -> lc_tm a.
Proof. intros a H. inversion H. assumption. Qed.

Lemma lc_tm_Case_inv : forall g a b1 b2,
  lc_tm (a_Case g a b1 b2) -> lc_tm a /\ lc_tm b1 /\ lc_tm b2.
Proof. intros g a b1 b2 H. inversion H. split; [assumption|split; assumption]. Qed.

Lemma lc_tm_WSigma_inv : forall g A B, lc_tm (a_WSigma g A B) ->
  lc_tm A /\ (forall x, lc_tm (open_tm_wrt_tm B (a_Var_f x))).
Proof. intros g A B H. inversion H. split; assumption. Qed.

Lemma lc_tm_WPair_inv : forall a g b, lc_tm (a_WPair a g b) -> lc_tm a /\ lc_tm b.
Proof. intros a g b H. inversion H. split; assumption. Qed.

Lemma lc_tm_LetPair_inv : forall g a b, lc_tm (a_LetPair g a b) ->
  lc_tm a /\ (forall x, lc_tm (open_tm_wrt_tm b (a_Var_f x))).
Proof. intros g a b H. inversion H. split; assumption. Qed.

Lemma lc_tm_SSigma_inv : forall g A B, lc_tm (a_SSigma g A B) ->
  lc_tm A /\ (forall x, lc_tm (open_tm_wrt_tm B (a_Var_f x))).
Proof. intros g A B H. inversion H. split; assumption. Qed.

Lemma lc_tm_SPair_inv : forall a g b, lc_tm (a_SPair a g b) -> lc_tm a /\ lc_tm b.
Proof. intros a g b H. inversion H. split; assumption. Qed.

Lemma lc_tm_Proj1_inv : forall g a, lc_tm (a_Proj1 g a) -> lc_tm a.
Proof. intros g a H. inversion H. assumption. Qed.

Lemma lc_tm_Proj2_inv : forall g a, lc_tm (a_Proj2 g a) -> lc_tm a.
Proof. intros g a H. inversion H. assumption. Qed.

(* A structurally defined local-closure predicate, indexed by the number
   of enclosing binders. *)
Inductive lc_alt : nat -> tm -> Prop :=
| Lc_f : forall k x, lc_alt k (a_Var_f x)
| Lc_b : forall k n, (n < k)%nat -> lc_alt k (a_Var_b n)
| Lc_TyUnit : forall k, lc_alt k a_TyUnit
| Lc_TmUnit : forall k, lc_alt k a_TmUnit
| Lc_Type : forall k s, lc_alt k (a_Type s)
| Lc_Pi : forall k g A B, lc_alt k A -> lc_alt (S k) B -> lc_alt k (a_Pi g A B)
| Lc_Abs : forall k g A b, lc_alt k A -> lc_alt (S k) b -> lc_alt k (a_Abs g A b)
| Lc_App : forall k a g b, lc_alt k a -> lc_alt k b -> lc_alt k (a_App a g b)
| Lc_Sum : forall k A1 A2, lc_alt k A1 -> lc_alt k A2 -> lc_alt k (a_Sum A1 A2)
| Lc_Inj1 : forall k a, lc_alt k a -> lc_alt k (a_Inj1 a)
| Lc_Inj2 : forall k a, lc_alt k a -> lc_alt k (a_Inj2 a)
| Lc_Case : forall k g a b1 b2, lc_alt k a -> lc_alt k b1 -> lc_alt k b2 ->
    lc_alt k (a_Case g a b1 b2)
| Lc_WSigma : forall k g A B, lc_alt k A -> lc_alt (S k) B -> lc_alt k (a_WSigma g A B)
| Lc_WPair : forall k a g b, lc_alt k a -> lc_alt k b -> lc_alt k (a_WPair a g b)
| Lc_LetPair : forall k g a b, lc_alt k a -> lc_alt (S k) b -> lc_alt k (a_LetPair g a b)
| Lc_SSigma : forall k g A B, lc_alt k A -> lc_alt (S k) B -> lc_alt k (a_SSigma g A B)
| Lc_SPair : forall k a g b, lc_alt k a -> lc_alt k b -> lc_alt k (a_SPair a g b)
| Lc_Proj1 : forall k g a, lc_alt k a -> lc_alt k (a_Proj1 g a)
| Lc_Proj2 : forall k g a, lc_alt k a -> lc_alt k (a_Proj2 g a).

Lemma lc_alt_var_b_inv : forall k n, lc_alt k (a_Var_b n) -> (n < k)%nat.
Proof. intros k n H. inversion H. assumption. Qed.

Lemma lc_alt_Pi_inv : forall k g A B, lc_alt k (a_Pi g A B) ->
  lc_alt k A /\ lc_alt (S k) B.
Proof. intros k g A B H. inversion H. split; assumption. Qed.

Lemma lc_alt_Abs_inv : forall k g A b, lc_alt k (a_Abs g A b) ->
  lc_alt k A /\ lc_alt (S k) b.
Proof. intros k g A b H. inversion H. split; assumption. Qed.

Lemma lc_alt_App_inv : forall k a g b, lc_alt k (a_App a g b) ->
  lc_alt k a /\ lc_alt k b.
Proof. intros k a g b H. inversion H. split; assumption. Qed.

Lemma lc_alt_Sum_inv : forall k A1 A2, lc_alt k (a_Sum A1 A2) ->
  lc_alt k A1 /\ lc_alt k A2.
Proof. intros k A1 A2 H. inversion H. split; assumption. Qed.

Lemma lc_alt_Inj1_inv : forall k a, lc_alt k (a_Inj1 a) -> lc_alt k a.
Proof. intros k a H. inversion H. assumption. Qed.

Lemma lc_alt_Inj2_inv : forall k a, lc_alt k (a_Inj2 a) -> lc_alt k a.
Proof. intros k a H. inversion H. assumption. Qed.

Lemma lc_alt_Case_inv : forall k g a b1 b2, lc_alt k (a_Case g a b1 b2) ->
  lc_alt k a /\ lc_alt k b1 /\ lc_alt k b2.
Proof. intros k g a b1 b2 H. inversion H. split; [assumption|split; assumption]. Qed.

Lemma lc_alt_WSigma_inv : forall k g A B, lc_alt k (a_WSigma g A B) ->
  lc_alt k A /\ lc_alt (S k) B.
Proof. intros k g A B H. inversion H. split; assumption. Qed.

Lemma lc_alt_WPair_inv : forall k a g b, lc_alt k (a_WPair a g b) ->
  lc_alt k a /\ lc_alt k b.
Proof. intros k a g b H. inversion H. split; assumption. Qed.

Lemma lc_alt_LetPair_inv : forall k g a b, lc_alt k (a_LetPair g a b) ->
  lc_alt k a /\ lc_alt (S k) b.
Proof. intros k g a b H. inversion H. split; assumption. Qed.

Lemma lc_alt_SSigma_inv : forall k g A B, lc_alt k (a_SSigma g A B) ->
  lc_alt k A /\ lc_alt (S k) B.
Proof. intros k g A B H. inversion H. split; assumption. Qed.

Lemma lc_alt_SPair_inv : forall k a g b, lc_alt k (a_SPair a g b) ->
  lc_alt k a /\ lc_alt k b.
Proof. intros k a g b H. inversion H. split; assumption. Qed.

Lemma lc_alt_Proj1_inv : forall k g a, lc_alt k (a_Proj1 g a) -> lc_alt k a.
Proof. intros k g a H. inversion H. assumption. Qed.

Lemma lc_alt_Proj2_inv : forall k g a, lc_alt k (a_Proj2 g a) -> lc_alt k a.
Proof. intros k g a H. inversion H. assumption. Qed.

Lemma lc_alt_mono : forall (a:tm) k k', (k <= k')%nat -> lc_alt k a -> lc_alt k' a.
Proof.
  intros a. induction a as
    [| | psi A IHA B IHB | psi A IHA b IHb | a IHA psi b IHb | s | n | x
    | A1 IHA1 A2 IHA2 | a IHA | a IHA | psi a IHA b1 IHb1 b2 IHb2
    | psi A IHA B IHB | a IHA psi b IHb | psi a IHA b IHb
    | psi A IHA B IHB | a IHA psi b IHb | psi a IHA | psi a IHA];
    intros k k' Hle H.
  - constructor.
  - constructor.
  - apply lc_alt_Pi_inv in H. destruct H as [HA HB]. apply Lc_Pi.
    + apply IHA with (k:=k) (k':=k'); [exact Hle|exact HA].
    + apply IHB with (k:=S k) (k':=S k'); [lia|exact HB].
  - apply lc_alt_Abs_inv in H. destruct H as [HA Hb]. apply Lc_Abs.
    + apply IHA with (k:=k) (k':=k'); [exact Hle|exact HA].
    + apply IHb with (k:=S k) (k':=S k'); [lia|exact Hb].
  - apply lc_alt_App_inv in H. destruct H as [Ha Hb]. apply Lc_App.
    + apply IHA with (k:=k) (k':=k'); [exact Hle|exact Ha].
    + apply IHb with (k:=k) (k':=k'); [exact Hle|exact Hb].
  - constructor.
  - apply lc_alt_var_b_inv in H. apply Lc_b. lia.
  - constructor.
  - apply lc_alt_Sum_inv in H. destruct H as [HA HB]. apply Lc_Sum.
    + apply IHA1 with (k:=k) (k':=k'); [exact Hle|exact HA].
    + apply IHA2 with (k:=k) (k':=k'); [exact Hle|exact HB].
  - apply lc_alt_Inj1_inv in H. apply Lc_Inj1.
    apply IHA with (k:=k) (k':=k'); [exact Hle|exact H].
  - apply lc_alt_Inj2_inv in H. apply Lc_Inj2.
    apply IHA with (k:=k) (k':=k'); [exact Hle|exact H].
  - apply lc_alt_Case_inv in H. destruct H as [Ha [Hb1 Hb2]]. apply Lc_Case.
    + apply IHA with (k:=k) (k':=k'); [exact Hle|exact Ha].
    + apply IHb1 with (k:=k) (k':=k'); [exact Hle|exact Hb1].
    + apply IHb2 with (k:=k) (k':=k'); [exact Hle|exact Hb2].
  - apply lc_alt_WSigma_inv in H. destruct H as [HA HB]. apply Lc_WSigma.
    + apply IHA with (k:=k) (k':=k'); [exact Hle|exact HA].
    + apply IHB with (k:=S k) (k':=S k'); [lia|exact HB].
  - apply lc_alt_WPair_inv in H. destruct H as [Ha Hb]. apply Lc_WPair.
    + apply IHA with (k:=k) (k':=k'); [exact Hle|exact Ha].
    + apply IHb with (k:=k) (k':=k'); [exact Hle|exact Hb].
  - apply lc_alt_LetPair_inv in H. destruct H as [Ha Hb]. apply Lc_LetPair.
    + apply IHA with (k:=k) (k':=k'); [exact Hle|exact Ha].
    + apply IHb with (k:=S k) (k':=S k'); [lia|exact Hb].
  - apply lc_alt_SSigma_inv in H. destruct H as [HA HB]. apply Lc_SSigma.
    + apply IHA with (k:=k) (k':=k'); [exact Hle|exact HA].
    + apply IHB with (k:=S k) (k':=S k'); [lia|exact HB].
  - apply lc_alt_SPair_inv in H. destruct H as [Ha Hb]. apply Lc_SPair.
    + apply IHA with (k:=k) (k':=k'); [exact Hle|exact Ha].
    + apply IHb with (k:=k) (k':=k'); [exact Hle|exact Hb].
  - apply lc_alt_Proj1_inv in H. apply Lc_Proj1.
    apply IHA with (k:=k) (k':=k'); [exact Hle|exact H].
  - apply lc_alt_Proj2_inv in H. apply Lc_Proj2.
    apply IHA with (k:=k) (k':=k'); [exact Hle|exact H].
Qed.

Lemma lc_alt_open_fwd : forall (k:nat) (b:tm) x,
  lc_alt (S k) b -> lc_alt k (open_tm_wrt_tm_rec k (a_Var_f x) b).
Proof.
  intros k b. revert k. induction b as
    [| | psi A IHA B IHB | psi A IHA b IHb | a IHA psi b IHb | s | n | y
    | A1 IHA1 A2 IHA2 | a IHA | a IHA | psi a IHA b1 IHb1 b2 IHb2
    | psi A IHA B IHB | a IHA psi b IHb | psi a IHA b IHb
    | psi A IHA B IHB | a IHA psi b IHb | psi a IHA | psi a IHA];
    intros k x H.
  - simpl. constructor.
  - simpl. constructor.
  - simpl. apply lc_alt_Pi_inv in H. destruct H as [HA HB]. apply Lc_Pi.
    + apply IHA. exact HA.
    + apply IHB. exact HB.
  - simpl. apply lc_alt_Abs_inv in H. destruct H as [HA Hb]. apply Lc_Abs.
    + apply IHA. exact HA.
    + apply IHb. exact Hb.
  - simpl. apply lc_alt_App_inv in H. destruct H as [Ha Hb]. apply Lc_App.
    + apply IHA. exact Ha.
    + apply IHb. exact Hb.
  - simpl. constructor.
  - apply lc_alt_var_b_inv in H.
    destruct (lt_eq_lt_dec n k) as [[Hlt|Heq]|Hgt].
    + rewrite (@open_rec_var_b_lt k (a_Var_f x) n Hlt). apply Lc_b. lia.
    + subst n. rewrite (@open_rec_var_b_eq k (a_Var_f x)). constructor.
    + rewrite (@open_rec_var_b_gt k (a_Var_f x) n Hgt). apply Lc_b. lia.
  - simpl. constructor.
  - simpl. apply lc_alt_Sum_inv in H. destruct H as [HA HB]. apply Lc_Sum.
    + apply IHA1. exact HA.
    + apply IHA2. exact HB.
  - simpl. apply lc_alt_Inj1_inv in H. apply Lc_Inj1. apply IHA. exact H.
  - simpl. apply lc_alt_Inj2_inv in H. apply Lc_Inj2. apply IHA. exact H.
  - simpl. apply lc_alt_Case_inv in H. destruct H as [Ha [Hb1 Hb2]]. apply Lc_Case.
    + apply IHA. exact Ha.
    + apply IHb1. exact Hb1.
    + apply IHb2. exact Hb2.
  - simpl. apply lc_alt_WSigma_inv in H. destruct H as [HA HB]. apply Lc_WSigma.
    + apply IHA. exact HA.
    + apply IHB. exact HB.
  - simpl. apply lc_alt_WPair_inv in H. destruct H as [Ha Hb]. apply Lc_WPair.
    + apply IHA. exact Ha.
    + apply IHb. exact Hb.
  - simpl. apply lc_alt_LetPair_inv in H. destruct H as [Ha Hb]. apply Lc_LetPair.
    + apply IHA. exact Ha.
    + apply IHb. exact Hb.
  - simpl. apply lc_alt_SSigma_inv in H. destruct H as [HA HB]. apply Lc_SSigma.
    + apply IHA. exact HA.
    + apply IHB. exact HB.
  - simpl. apply lc_alt_SPair_inv in H. destruct H as [Ha Hb]. apply Lc_SPair.
    + apply IHA. exact Ha.
    + apply IHb. exact Hb.
  - simpl. apply lc_alt_Proj1_inv in H. apply Lc_Proj1. apply IHA. exact H.
  - simpl. apply lc_alt_Proj2_inv in H. apply Lc_Proj2. apply IHA. exact H.
Qed.

Lemma lc_alt_open_bwd : forall (k:nat) (b:tm) x,
  lc_alt k (open_tm_wrt_tm_rec k (a_Var_f x) b) -> lc_alt (S k) b.
Proof.
  intros k b. revert k. induction b as
    [| | psi A IHA B IHB | psi A IHA b IHb | a IHA psi b IHb | s | n | y
    | A1 IHA1 A2 IHA2 | a IHA | a IHA | psi a IHA b1 IHb1 b2 IHb2
    | psi A IHA B IHB | a IHA psi b IHb | psi a IHA b IHb
    | psi A IHA B IHB | a IHA psi b IHb | psi a IHA | psi a IHA];
    intros k x H.
  - simpl in H. constructor.
  - simpl in H. constructor.
  - simpl in H. apply lc_alt_Pi_inv in H. destruct H as [HA HB]. apply Lc_Pi.
    + apply IHA with (k:=k) (x:=x); exact HA.
    + apply IHB with (k:=S k) (x:=x); exact HB.
  - simpl in H. apply lc_alt_Abs_inv in H. destruct H as [HA Hb]. apply Lc_Abs.
    + apply IHA with (k:=k) (x:=x); exact HA.
    + apply IHb with (k:=S k) (x:=x); exact Hb.
  - simpl in H. apply lc_alt_App_inv in H. destruct H as [Ha Hb]. apply Lc_App.
    + apply IHA with (k:=k) (x:=x); exact Ha.
    + apply IHb with (k:=k) (x:=x); exact Hb.
  - simpl in H. constructor.
  - destruct (lt_eq_lt_dec n k) as [[Hlt|Heq]|Hgt].
    + rewrite (@open_rec_var_b_lt k (a_Var_f x) n Hlt) in H.
      apply lc_alt_var_b_inv in H. apply Lc_b. lia.
    + subst n. rewrite (@open_rec_var_b_eq k (a_Var_f x)) in H. apply Lc_b. lia.
    + rewrite (@open_rec_var_b_gt k (a_Var_f x) n Hgt) in H.
      apply lc_alt_var_b_inv in H. apply Lc_b. lia.
  - simpl in H. constructor.
  - simpl in H. apply lc_alt_Sum_inv in H. destruct H as [HA HB]. apply Lc_Sum.
    + apply IHA1 with (k:=k) (x:=x); exact HA.
    + apply IHA2 with (k:=k) (x:=x); exact HB.
  - simpl in H. apply lc_alt_Inj1_inv in H. apply Lc_Inj1. apply IHA with (k:=k) (x:=x); exact H.
  - simpl in H. apply lc_alt_Inj2_inv in H. apply Lc_Inj2. apply IHA with (k:=k) (x:=x); exact H.
  - simpl in H. apply lc_alt_Case_inv in H. destruct H as [Ha [Hb1 Hb2]]. apply Lc_Case.
    + apply IHA with (k:=k) (x:=x); exact Ha.
    + apply IHb1 with (k:=k) (x:=x); exact Hb1.
    + apply IHb2 with (k:=k) (x:=x); exact Hb2.
  - simpl in H. apply lc_alt_WSigma_inv in H. destruct H as [HA HB]. apply Lc_WSigma.
    + apply IHA with (k:=k) (x:=x); exact HA.
    + apply IHB with (k:=S k) (x:=x); exact HB.
  - simpl in H. apply lc_alt_WPair_inv in H. destruct H as [Ha Hb]. apply Lc_WPair.
    + apply IHA with (k:=k) (x:=x); exact Ha.
    + apply IHb with (k:=k) (x:=x); exact Hb.
  - simpl in H. apply lc_alt_LetPair_inv in H. destruct H as [Ha Hb]. apply Lc_LetPair.
    + apply IHA with (k:=k) (x:=x); exact Ha.
    + apply IHb with (k:=S k) (x:=x); exact Hb.
  - simpl in H. apply lc_alt_SSigma_inv in H. destruct H as [HA HB]. apply Lc_SSigma.
    + apply IHA with (k:=k) (x:=x); exact HA.
    + apply IHB with (k:=S k) (x:=x); exact HB.
  - simpl in H. apply lc_alt_SPair_inv in H. destruct H as [Ha Hb]. apply Lc_SPair.
    + apply IHA with (k:=k) (x:=x); exact Ha.
    + apply IHb with (k:=k) (x:=x); exact Hb.
  - simpl in H. apply lc_alt_Proj1_inv in H. apply Lc_Proj1. apply IHA with (k:=k) (x:=x); exact H.
  - simpl in H. apply lc_alt_Proj2_inv in H. apply Lc_Proj2. apply IHA with (k:=k) (x:=x); exact H.
Qed.

Lemma lc_alt_open : forall (k:nat) (b:tm) x,
  lc_alt (S k) b <-> lc_alt k (open_tm_wrt_tm_rec k (a_Var_f x) b).
Proof.
  intros. split; [apply lc_alt_open_fwd|apply lc_alt_open_bwd].
Qed.

Lemma lc_alt_open_body : forall (k:nat) (t b:tm),
  lc_alt k t -> lc_alt (S k) b -> lc_alt k (open_tm_wrt_tm_rec k t b).
Proof.
  intros k t b Ha Hb. revert k t Ha Hb.
  induction b as
    [| | psi A IHA B IHB | psi A IHA b IHb | a IHA psi b IHb | s | n | y
    | A1 IHA1 A2 IHA2 | a IHA | a IHA | psi a IHA b1 IHb1 b2 IHb2
    | psi A IHA B IHB | a IHA psi b IHb | psi a IHA b IHb
    | psi A IHA B IHB | a IHA psi b IHb | psi a IHA | psi a IHA];
    intros k t Ha Hb.
  - simpl. constructor.
  - simpl. constructor.
  - simpl. apply lc_alt_Pi_inv in Hb. destruct Hb as [HA HB]. apply Lc_Pi.
    + apply IHA; [exact Ha|exact HA].
    + apply IHB with (k:=S k) (t:=t); [apply lc_alt_mono with (k:=k) (a:=t); [lia|exact Ha]|exact HB].
  - simpl. apply lc_alt_Abs_inv in Hb. destruct Hb as [HA Hb']. apply Lc_Abs.
    + apply IHA; [exact Ha|exact HA].
    + apply IHb with (k:=S k) (t:=t); [apply lc_alt_mono with (k:=k) (a:=t); [lia|exact Ha]|exact Hb'].
  - simpl. apply lc_alt_App_inv in Hb. destruct Hb as [HA HB]. apply Lc_App.
    + apply IHA; [exact Ha|exact HA].
    + apply IHb; [exact Ha|exact HB].
  - simpl. constructor.
  - apply lc_alt_var_b_inv in Hb.
    destruct (lt_eq_lt_dec n k) as [[Hlt|Heq]|Hgt].
    + rewrite (@open_rec_var_b_lt k t n Hlt). apply Lc_b. lia.
    + subst n. rewrite (@open_rec_var_b_eq k t). exact Ha.
    + rewrite (@open_rec_var_b_gt k t n Hgt) in *. apply Lc_b. lia.
  - simpl. constructor.
  - simpl. apply lc_alt_Sum_inv in Hb. destruct Hb as [HA HB]. apply Lc_Sum.
    + apply IHA1; [exact Ha|exact HA].
    + apply IHA2; [exact Ha|exact HB].
  - simpl. apply lc_alt_Inj1_inv in Hb. apply Lc_Inj1. apply IHA; [exact Ha|exact Hb].
  - simpl. apply lc_alt_Inj2_inv in Hb. apply Lc_Inj2. apply IHA; [exact Ha|exact Hb].
  - simpl. apply lc_alt_Case_inv in Hb. destruct Hb as [HA [HB1 HB2]]. apply Lc_Case.
    + apply IHA; [exact Ha|exact HA].
    + apply IHb1; [exact Ha|exact HB1].
    + apply IHb2; [exact Ha|exact HB2].
  - simpl. apply lc_alt_WSigma_inv in Hb. destruct Hb as [HA HB]. apply Lc_WSigma.
    + apply IHA; [exact Ha|exact HA].
    + apply IHB with (k:=S k) (t:=t); [apply lc_alt_mono with (k:=k) (a:=t); [lia|exact Ha]|exact HB].
  - simpl. apply lc_alt_WPair_inv in Hb. destruct Hb as [HA HB]. apply Lc_WPair.
    + apply IHA; [exact Ha|exact HA].
    + apply IHb; [exact Ha|exact HB].
  - simpl. apply lc_alt_LetPair_inv in Hb. destruct Hb as [HA HB]. apply Lc_LetPair.
    + apply IHA; [exact Ha|exact HA].
    + apply IHb with (k:=S k) (t:=t); [apply lc_alt_mono with (k:=k) (a:=t); [lia|exact Ha]|exact HB].
  - simpl. apply lc_alt_SSigma_inv in Hb. destruct Hb as [HA HB]. apply Lc_SSigma.
    + apply IHA; [exact Ha|exact HA].
    + apply IHB with (k:=S k) (t:=t); [apply lc_alt_mono with (k:=k) (a:=t); [lia|exact Ha]|exact HB].
  - simpl. apply lc_alt_SPair_inv in Hb. destruct Hb as [HA HB]. apply Lc_SPair.
    + apply IHA; [exact Ha|exact HA].
    + apply IHb; [exact Ha|exact HB].
  - simpl. apply lc_alt_Proj1_inv in Hb. apply Lc_Proj1. apply IHA; [exact Ha|exact Hb].
  - simpl. apply lc_alt_Proj2_inv in Hb. apply Lc_Proj2. apply IHA; [exact Ha|exact Hb].
Qed.

Lemma lc_alt_subst : forall (k:nat) (s:tm) x (b:tm),
  lc_alt k s -> lc_alt k b -> lc_alt k (subst_tm_tm s x b).
Proof.
  intros k s x b Ha Hb. revert k s Ha Hb.
  induction b as
    [| | psi A IHA B IHB | psi A IHA b IHb | a IHA psi b IHb | s0 | n | y
    | A1 IHA1 A2 IHA2 | a IHA | a IHA | psi a IHA b1 IHb1 b2 IHb2
    | psi A IHA B IHB | a IHA psi b IHb | psi a IHA b IHb
    | psi A IHA B IHB | a IHA psi b IHb | psi a IHA | psi a IHA];
    intros k s Ha Hb.
  - simpl. constructor.
  - simpl. constructor.
  - simpl. apply lc_alt_Pi_inv in Hb. destruct Hb as [HA HB]. apply Lc_Pi.
    + apply IHA; [exact Ha|exact HA].
    + apply IHB with (k:=S k) (s:=s);
        [apply lc_alt_mono with (k:=k) (a:=s); [lia|exact Ha]|exact HB].
  - simpl. apply lc_alt_Abs_inv in Hb. destruct Hb as [HA Hb']. apply Lc_Abs.
    + apply IHA; [exact Ha|exact HA].
    + apply IHb with (k:=S k) (s:=s);
        [apply lc_alt_mono with (k:=k) (a:=s); [lia|exact Ha]|exact Hb'].
  - simpl. apply lc_alt_App_inv in Hb. destruct Hb as [HA HB]. apply Lc_App.
    + apply IHA; [exact Ha|exact HA].
    + apply IHb; [exact Ha|exact HB].
  - simpl. constructor.
  - simpl. exact Hb.
  - simpl. destruct (eq_var y x) as [e|n0].
    + exact Ha.
    + constructor.
  - simpl. apply lc_alt_Sum_inv in Hb. destruct Hb as [HA HB]. apply Lc_Sum.
    + apply IHA1; [exact Ha|exact HA].
    + apply IHA2; [exact Ha|exact HB].
  - simpl. apply lc_alt_Inj1_inv in Hb. apply Lc_Inj1. apply IHA; [exact Ha|exact Hb].
  - simpl. apply lc_alt_Inj2_inv in Hb. apply Lc_Inj2. apply IHA; [exact Ha|exact Hb].
  - simpl. apply lc_alt_Case_inv in Hb. destruct Hb as [HA [HB1 HB2]]. apply Lc_Case.
    + apply IHA; [exact Ha|exact HA].
    + apply IHb1; [exact Ha|exact HB1].
    + apply IHb2; [exact Ha|exact HB2].
  - simpl. apply lc_alt_WSigma_inv in Hb. destruct Hb as [HA HB]. apply Lc_WSigma.
    + apply IHA; [exact Ha|exact HA].
    + apply IHB with (k:=S k) (s:=s);
        [apply lc_alt_mono with (k:=k) (a:=s); [lia|exact Ha]|exact HB].
  - simpl. apply lc_alt_WPair_inv in Hb. destruct Hb as [HA HB]. apply Lc_WPair.
    + apply IHA; [exact Ha|exact HA].
    + apply IHb; [exact Ha|exact HB].
  - simpl. apply lc_alt_LetPair_inv in Hb. destruct Hb as [HA HB]. apply Lc_LetPair.
    + apply IHA; [exact Ha|exact HA].
    + apply IHb with (k:=S k) (s:=s);
        [apply lc_alt_mono with (k:=k) (a:=s); [lia|exact Ha]|exact HB].
  - simpl. apply lc_alt_SSigma_inv in Hb. destruct Hb as [HA HB]. apply Lc_SSigma.
    + apply IHA; [exact Ha|exact HA].
    + apply IHB with (k:=S k) (s:=s);
        [apply lc_alt_mono with (k:=k) (a:=s); [lia|exact Ha]|exact HB].
  - simpl. apply lc_alt_SPair_inv in Hb. destruct Hb as [HA HB]. apply Lc_SPair.
    + apply IHA; [exact Ha|exact HA].
    + apply IHb; [exact Ha|exact HB].
  - simpl. apply lc_alt_Proj1_inv in Hb. apply Lc_Proj1. apply IHA; [exact Ha|exact Hb].
  - simpl. apply lc_alt_Proj2_inv in Hb. apply Lc_Proj2. apply IHA; [exact Ha|exact Hb].
Qed.

Lemma lc_alt_open_stable : forall (k:nat) (a:tm),
  lc_alt k a -> forall (p:nat) (v:tm), (k <= p)%nat -> open_tm_wrt_tm_rec p v a = a.
Proof.
  intros k a H. revert k H.
  induction a as
    [| | psi A IHA B IHB | psi A IHA b IHb | a IHA psi b IHb | s | n | y
    | A1 IHA1 A2 IHA2 | a IHA | a IHA | psi a IHA b1 IHb1 b2 IHb2
    | psi A IHA B IHB | a IHA psi b IHb | psi a IHA b IHb
    | psi A IHA B IHB | a IHA psi b IHb | psi a IHA | psi a IHA];
    intros k H p v Hle.
  - reflexivity.
  - reflexivity.
  - apply lc_alt_Pi_inv in H. destruct H as [HA HB]. simpl. f_equal.
    + apply IHA with (k:=k); [exact HA|exact Hle].
    + apply IHB with (k:=S k); [exact HB|lia].
  - apply lc_alt_Abs_inv in H. destruct H as [HA Hb]. simpl. f_equal.
    + apply IHA with (k:=k); [exact HA|exact Hle].
    + apply IHb with (k:=S k); [exact Hb|lia].
  - apply lc_alt_App_inv in H. destruct H as [Ha Hb]. simpl. f_equal.
    + apply IHA with (k:=k); [exact Ha|exact Hle].
    + apply IHb with (k:=k); [exact Hb|exact Hle].
  - reflexivity.
  - apply lc_alt_var_b_inv in H.
    assert (Hlt : (n < p)%nat) by (lia).
    rewrite (@open_rec_var_b_lt p v n Hlt). reflexivity.
  - reflexivity.
  - apply lc_alt_Sum_inv in H. destruct H as [HA HB]. simpl. f_equal.
    + apply IHA1 with (k:=k); [exact HA|exact Hle].
    + apply IHA2 with (k:=k); [exact HB|exact Hle].
  - apply lc_alt_Inj1_inv in H. simpl. f_equal. apply IHA with (k:=k); [exact H|exact Hle].
  - apply lc_alt_Inj2_inv in H. simpl. f_equal. apply IHA with (k:=k); [exact H|exact Hle].
  - apply lc_alt_Case_inv in H. destruct H as [Ha [Hb1 Hb2]]. simpl. f_equal.
    + apply IHA with (k:=k); [exact Ha|exact Hle].
    + apply IHb1 with (k:=k); [exact Hb1|exact Hle].
    + apply IHb2 with (k:=k); [exact Hb2|exact Hle].
  - apply lc_alt_WSigma_inv in H. destruct H as [HA HB]. simpl. f_equal.
    + apply IHA with (k:=k); [exact HA|exact Hle].
    + apply IHB with (k:=S k); [exact HB|lia].
  - apply lc_alt_WPair_inv in H. destruct H as [Ha Hb]. simpl. f_equal.
    + apply IHA with (k:=k); [exact Ha|exact Hle].
    + apply IHb with (k:=k); [exact Hb|exact Hle].
  - apply lc_alt_LetPair_inv in H. destruct H as [Ha Hb]. simpl. f_equal.
    + apply IHA with (k:=k); [exact Ha|exact Hle].
    + apply IHb with (k:=S k); [exact Hb|lia].
  - apply lc_alt_SSigma_inv in H. destruct H as [HA HB]. simpl. f_equal.
    + apply IHA with (k:=k); [exact HA|exact Hle].
    + apply IHB with (k:=S k); [exact HB|lia].
  - apply lc_alt_SPair_inv in H. destruct H as [Ha Hb]. simpl. f_equal.
    + apply IHA with (k:=k); [exact Ha|exact Hle].
    + apply IHb with (k:=k); [exact Hb|exact Hle].
  - apply lc_alt_Proj1_inv in H. simpl. f_equal. apply IHA with (k:=k); [exact H|exact Hle].
  - apply lc_alt_Proj2_inv in H. simpl. f_equal. apply IHA with (k:=k); [exact H|exact Hle].
Qed.

Lemma lc_alt_open_nop : forall (k:nat) (a:tm),
  lc_alt 0 a -> forall (p:nat) (v:tm), open_tm_wrt_tm_rec p v a = a.
Proof.
  intros k a H p v. apply lc_alt_open_stable with (k:=0); [exact H|lia].
Qed.

Lemma lc_alt_iff_lc_tm_open : forall (a:tm) (k:nat) (xs:list atom),
  length xs = k -> (lc_alt k a <-> lc_tm (open_atoms 0 xs a)).
Proof.
  intros a. induction a as
    [| | psi A IHA B IHB | psi A IHA b IHb | a IHA psi b IHb | s | n | y
    | A1 IHA1 A2 IHA2 | a IHA | a IHA | psi a IHA b1 IHb1 b2 IHb2
    | psi A IHA B IHB | a IHA psi b IHb | psi a IHA b IHb
    | psi A IHA B IHB | a IHA psi b IHb | psi a IHA | psi a IHA];
    intros k xs Hlen; split; intro H.
  - rewrite (open_atoms_tyunit 0 xs). constructor.
  - constructor.
  - rewrite (open_atoms_tmunit 0 xs). constructor.
  - constructor.
  - rewrite (open_atoms_pi 0 xs psi A B).
    apply lc_alt_Pi_inv in H. destruct H as [HA HB].
    apply lc_a_Pi.
    + apply (proj1 (IHA k xs Hlen) HA).
    + intro z. rewrite (open_var_open_atoms z xs B).
      assert (Len : length (z::xs) = S k) by (simpl; f_equal; exact Hlen).
      apply (proj1 (IHB (S k) (z::xs) Len)). exact HB.
  - rewrite (open_atoms_pi 0 xs psi A B) in H.
    apply lc_tm_Pi_inv in H. destruct H as [HA HB].
    apply Lc_Pi.
    + apply (proj2 (IHA k xs Hlen) HA).
    + destruct (atom_fresh (empty:atoms)) as [z Hz].
      specialize (HB z).
      rewrite (open_var_open_atoms z xs B) in HB.
      assert (Len : length (z::xs) = S k) by (simpl; f_equal; exact Hlen).
      apply (proj2 (IHB (S k) (z::xs) Len)). exact HB.
  - rewrite (open_atoms_abs 0 xs psi A b).
    apply lc_alt_Abs_inv in H. destruct H as [HA Hb].
    apply lc_a_Abs.
    + apply (proj1 (IHA k xs Hlen) HA).
    + intro z. rewrite (open_var_open_atoms z xs b).
      assert (Len : length (z::xs) = S k) by (simpl; f_equal; exact Hlen).
      apply (proj1 (IHb (S k) (z::xs) Len)). exact Hb.
  - rewrite (open_atoms_abs 0 xs psi A b) in H.
    apply lc_tm_Abs_inv in H. destruct H as [HA Hb].
    apply Lc_Abs.
    + apply (proj2 (IHA k xs Hlen) HA).
    + destruct (atom_fresh (empty:atoms)) as [z Hz].
      specialize (Hb z).
      rewrite (open_var_open_atoms z xs b) in Hb.
      assert (Len : length (z::xs) = S k) by (simpl; f_equal; exact Hlen).
      apply (proj2 (IHb (S k) (z::xs) Len)). exact Hb.
  - rewrite (open_atoms_app 0 xs psi a b).
    apply lc_alt_App_inv in H. destruct H as [Ha Hb].
    apply lc_a_App.
    + apply (proj1 (IHA k xs Hlen) Ha).
    + apply (proj1 (IHb k xs Hlen) Hb).
  - rewrite (open_atoms_app 0 xs psi a b) in H.
    apply lc_tm_App_inv in H. destruct H as [Ha Hb].
    apply Lc_App.
    + apply (proj2 (IHA k xs Hlen) Ha).
    + apply (proj2 (IHb k xs Hlen) Hb).
  - rewrite (open_atoms_type 0 xs s).
    constructor.
  - constructor.
  - apply lc_alt_var_b_inv in H.
    destruct (@open_atoms_var_b_mid 0 xs n) as [z Hz]; [lia|lia|].
    rewrite Hz. constructor.
  - destruct (lt_ge_dec n (length xs)) as [Hlt|Hge].
    + apply Lc_b. lia.
    + assert (HG : open_atoms 0 xs (a_Var_b n) = a_Var_b (n - length xs))
        by (apply (@open_atoms_var_b_ge 0 xs n); lia).
      rewrite HG in H. inversion H.
  - rewrite (open_atoms_var_f 0 xs y). constructor.
  - constructor.
  - rewrite (open_atoms_sum 0 xs A1 A2).
    apply lc_alt_Sum_inv in H. destruct H as [HA HB]. apply lc_a_Sum;
      [apply (proj1 (IHA1 k xs Hlen) HA)|apply (proj1 (IHA2 k xs Hlen) HB)].
  - rewrite (open_atoms_sum 0 xs A1 A2) in H.
    apply lc_tm_Sum_inv in H. destruct H as [HA HB]. apply Lc_Sum;
      [apply (proj2 (IHA1 k xs Hlen) HA)|apply (proj2 (IHA2 k xs Hlen) HB)].
  - rewrite (open_atoms_inj1 0 xs a).
    apply lc_alt_Inj1_inv in H. apply lc_a_Inj1. apply (proj1 (IHA k xs Hlen) H).
  - rewrite (open_atoms_inj1 0 xs a) in H.
    apply lc_tm_Inj1_inv in H. apply Lc_Inj1. apply (proj2 (IHA k xs Hlen) H).
  - rewrite (open_atoms_inj2 0 xs a).
    apply lc_alt_Inj2_inv in H. apply lc_a_Inj2. apply (proj1 (IHA k xs Hlen) H).
  - rewrite (open_atoms_inj2 0 xs a) in H.
    apply lc_tm_Inj2_inv in H. apply Lc_Inj2. apply (proj2 (IHA k xs Hlen) H).
  - rewrite (open_atoms_case 0 xs psi a b1 b2).
    apply lc_alt_Case_inv in H. destruct H as [Ha [Hb1 Hb2]]. apply lc_a_Case.
    + apply (proj1 (IHA k xs Hlen) Ha).
    + apply (proj1 (IHb1 k xs Hlen) Hb1).
    + apply (proj1 (IHb2 k xs Hlen) Hb2).
  - rewrite (open_atoms_case 0 xs psi a b1 b2) in H.
    apply lc_tm_Case_inv in H. destruct H as [Ha [Hb1 Hb2]]. apply Lc_Case.
    + apply (proj2 (IHA k xs Hlen) Ha).
    + apply (proj2 (IHb1 k xs Hlen) Hb1).
    + apply (proj2 (IHb2 k xs Hlen) Hb2).
  - rewrite (open_atoms_wsigma 0 xs psi A B).
    apply lc_alt_WSigma_inv in H. destruct H as [HA HB]. apply lc_a_WSigma.
    + apply (proj1 (IHA k xs Hlen) HA).
    + intro z. rewrite (open_var_open_atoms z xs B).
      assert (Len : length (z::xs) = S k) by (simpl; f_equal; exact Hlen).
      apply (proj1 (IHB (S k) (z::xs) Len)). exact HB.
  - rewrite (open_atoms_wsigma 0 xs psi A B) in H.
    apply lc_tm_WSigma_inv in H. destruct H as [HA HB]. apply Lc_WSigma.
    + apply (proj2 (IHA k xs Hlen) HA).
    + destruct (atom_fresh (empty:atoms)) as [z Hz].
      specialize (HB z).
      rewrite (open_var_open_atoms z xs B) in HB.
      assert (Len : length (z::xs) = S k) by (simpl; f_equal; exact Hlen).
      apply (proj2 (IHB (S k) (z::xs) Len)). exact HB.
  - rewrite (open_atoms_wpair 0 xs a psi b).
    apply lc_alt_WPair_inv in H. destruct H as [Ha Hb]. apply lc_a_WPair.
    + apply (proj1 (IHA k xs Hlen) Ha).
    + apply (proj1 (IHb k xs Hlen) Hb).
  - rewrite (open_atoms_wpair 0 xs a psi b) in H.
    apply lc_tm_WPair_inv in H. destruct H as [Ha Hb]. apply Lc_WPair.
    + apply (proj2 (IHA k xs Hlen) Ha).
    + apply (proj2 (IHb k xs Hlen) Hb).
  - rewrite (open_atoms_letpair 0 xs psi a b).
    apply lc_alt_LetPair_inv in H. destruct H as [Ha Hb]. apply lc_a_LetPair.
    + apply (proj1 (IHA k xs Hlen) Ha).
    + intro z. rewrite (open_var_open_atoms z xs b).
      assert (Len : length (z::xs) = S k) by (simpl; f_equal; exact Hlen).
      apply (proj1 (IHb (S k) (z::xs) Len)). exact Hb.
  - rewrite (open_atoms_letpair 0 xs psi a b) in H.
    apply lc_tm_LetPair_inv in H. destruct H as [Ha Hb]. apply Lc_LetPair.
    + apply (proj2 (IHA k xs Hlen) Ha).
    + destruct (atom_fresh (empty:atoms)) as [z Hz].
      specialize (Hb z).
      rewrite (open_var_open_atoms z xs b) in Hb.
      assert (Len : length (z::xs) = S k) by (simpl; f_equal; exact Hlen).
      apply (proj2 (IHb (S k) (z::xs) Len)). exact Hb.
  - rewrite (open_atoms_ssigma 0 xs psi A B).
    apply lc_alt_SSigma_inv in H. destruct H as [HA HB]. apply lc_a_SSigma.
    + apply (proj1 (IHA k xs Hlen) HA).
    + intro z. rewrite (open_var_open_atoms z xs B).
      assert (Len : length (z::xs) = S k) by (simpl; f_equal; exact Hlen).
      apply (proj1 (IHB (S k) (z::xs) Len)). exact HB.
  - rewrite (open_atoms_ssigma 0 xs psi A B) in H.
    apply lc_tm_SSigma_inv in H. destruct H as [HA HB]. apply Lc_SSigma.
    + apply (proj2 (IHA k xs Hlen) HA).
    + destruct (atom_fresh (empty:atoms)) as [z Hz].
      specialize (HB z).
      rewrite (open_var_open_atoms z xs B) in HB.
      assert (Len : length (z::xs) = S k) by (simpl; f_equal; exact Hlen).
      apply (proj2 (IHB (S k) (z::xs) Len)). exact HB.
  - rewrite (open_atoms_spair 0 xs a psi b).
    apply lc_alt_SPair_inv in H. destruct H as [Ha Hb]. apply lc_a_SPair.
    + apply (proj1 (IHA k xs Hlen) Ha).
    + apply (proj1 (IHb k xs Hlen) Hb).
  - rewrite (open_atoms_spair 0 xs a psi b) in H.
    apply lc_tm_SPair_inv in H. destruct H as [Ha Hb]. apply Lc_SPair.
    + apply (proj2 (IHA k xs Hlen) Ha).
    + apply (proj2 (IHb k xs Hlen) Hb).
  - rewrite (open_atoms_proj1 0 xs psi a).
    apply lc_alt_Proj1_inv in H. apply lc_a_Proj1. apply (proj1 (IHA k xs Hlen) H).
  - rewrite (open_atoms_proj1 0 xs psi a) in H.
    apply lc_tm_Proj1_inv in H. apply Lc_Proj1. apply (proj2 (IHA k xs Hlen) H).
  - rewrite (open_atoms_proj2 0 xs psi a).
    apply lc_alt_Proj2_inv in H. apply lc_a_Proj2. apply (proj1 (IHA k xs Hlen) H).
  - rewrite (open_atoms_proj2 0 xs psi a) in H.
    apply lc_tm_Proj2_inv in H. apply Lc_Proj2. apply (proj2 (IHA k xs Hlen) H).
Qed.

Lemma lc_tm_iff_lc_alt : forall a, lc_tm a <-> lc_alt 0 a.
Proof.
  intro a.
  assert (H0 : length (@nil atom) = 0) by reflexivity.
  pose proof (@lc_alt_iff_lc_tm_open a 0 nil H0) as H.
  simpl in H. split.
  - intro Ht. apply (proj2 H). exact Ht.
  - intro Ha. apply (proj1 H). exact Ha.
Qed.

Lemma subst_notin : forall (a:tm) (s:tm) x,
  x \notin fv_tm_tm a -> subst_tm_tm s x a = a.
Proof.
  intros a. induction a as
    [| | psi A IHA B IHB | psi A IHA b IHb | a IHA psi b IHb | s0 | n | z
    | A1 IHA1 A2 IHA2 | a IHA | a IHA | psi a IHA b1 IHb1 b2 IHb2
    | psi A IHA B IHB | a IHA psi b IHb | psi a IHA b IHb
    | psi A IHA B IHB | a IHA psi b IHb | psi a IHA | psi a IHA];
    intros s x Hfv.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. f_equal; [apply IHA; apply notin_union_1 in Hfv; exact Hfv
                    | apply IHB; apply notin_union_2 in Hfv; exact Hfv].
  - simpl. f_equal; [apply IHA; apply notin_union_1 in Hfv; exact Hfv
                    | apply IHb; apply notin_union_2 in Hfv; exact Hfv].
  - simpl. f_equal; [apply IHA; apply notin_union_1 in Hfv; exact Hfv
                    | apply IHb; apply notin_union_2 in Hfv; exact Hfv].
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. apply notin_singleton_1 in Hfv.
    destruct (eq_var z x) as [e|ne].
    + exfalso. apply (Hfv e).
    + reflexivity.
  - simpl. f_equal.
    + apply IHA1. apply notin_union_1 in Hfv; exact Hfv.
    + apply IHA2. apply notin_union_2 in Hfv; exact Hfv.
  - simpl. f_equal. apply IHA. exact Hfv.
  - simpl. f_equal. apply IHA. exact Hfv.
  - simpl. f_equal.
    + apply IHA. apply notin_union_1 in Hfv; exact Hfv.
    + apply IHb1. apply notin_union_2 in Hfv; apply notin_union_1 in Hfv; exact Hfv.
    + apply IHb2. apply notin_union_2 in Hfv; apply notin_union_2 in Hfv; exact Hfv.
  - simpl. f_equal; [apply IHA; apply notin_union_1 in Hfv; exact Hfv
                    | apply IHB; apply notin_union_2 in Hfv; exact Hfv].
  - simpl. f_equal; [apply IHA; apply notin_union_1 in Hfv; exact Hfv
                    | apply IHb; apply notin_union_2 in Hfv; exact Hfv].
  - simpl. f_equal; [apply IHA; apply notin_union_1 in Hfv; exact Hfv
                    | apply IHb; apply notin_union_2 in Hfv; exact Hfv].
  - simpl. f_equal; [apply IHA; apply notin_union_1 in Hfv; exact Hfv
                    | apply IHB; apply notin_union_2 in Hfv; exact Hfv].
  - simpl. f_equal; [apply IHA; apply notin_union_1 in Hfv; exact Hfv
                    | apply IHb; apply notin_union_2 in Hfv; exact Hfv].
  - simpl. f_equal. apply IHA. exact Hfv.
  - simpl. f_equal. apply IHA. exact Hfv.
Qed.

Lemma subst_open_comm : forall (k:nat) (s:tm) x (y:atom) (b:tm),
  y <> x -> lc_alt 0 s ->
  subst_tm_tm s x (open_tm_wrt_tm_rec k (a_Var_f y) b) =
  open_tm_wrt_tm_rec k (a_Var_f y) (subst_tm_tm s x b).
Proof.
  intros k s x y b Hy Hlc. revert k s Hlc.
  induction b as
    [| | psi A IHA B IHB | psi A IHA b IHb | a IHA psi b IHb | s0 | n | z
    | A1 IHA1 A2 IHA2 | a IHA | a IHA | psi a IHA b1 IHb1 b2 IHb2
    | psi A IHA B IHB | a IHA psi b IHb | psi a IHA b IHb
    | psi A IHA B IHB | a IHA psi b IHb | psi a IHA | psi a IHA];
    intros k s Hlc.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. f_equal; [apply IHA; exact Hlc | apply IHB; exact Hlc].
  - simpl. f_equal; [apply IHA; exact Hlc | apply IHb; exact Hlc].
  - simpl. f_equal; [apply IHA; exact Hlc | apply IHb; exact Hlc].
  - simpl. reflexivity.
  - destruct (lt_eq_lt_dec n k) as [[Hlt|Heq]|Hgt].
    + rewrite (@open_rec_var_b_lt k (a_Var_f y) n Hlt).
      rewrite (@subst_notin (a_Var_b n) s x) by (apply notin_empty_1).
      rewrite (@open_rec_var_b_lt k (a_Var_f y) n Hlt).
      reflexivity.
    + subst n.
      rewrite (@open_rec_var_b_eq k (a_Var_f y)).
      replace (subst_tm_tm s x (a_Var_b k)) with (a_Var_b k) by reflexivity.
      rewrite (@subst_notin (a_Var_f y) s x) by (apply notin_singleton_2; exact Hy).
      rewrite (@open_rec_var_b_eq k (a_Var_f y)).
      reflexivity.
    + rewrite (@open_rec_var_b_gt k (a_Var_f y) n Hgt).
      replace (subst_tm_tm s x (a_Var_b n)) with (a_Var_b n) by reflexivity.
      rewrite (@subst_notin (a_Var_b (n-1)) s x) by (apply notin_empty_1).
      rewrite (@open_rec_var_b_gt k (a_Var_f y) n Hgt).
      reflexivity.
  - simpl. destruct (eq_var z x) as [e|ne].
    + subst z. rewrite (@lc_alt_open_nop 0 s Hlc k (a_Var_f y)). reflexivity.
    + reflexivity.
  - simpl. f_equal; [apply IHA1; exact Hlc | apply IHA2; exact Hlc].
  - simpl. f_equal. apply IHA; exact Hlc.
  - simpl. f_equal. apply IHA; exact Hlc.
  - simpl. f_equal; [apply IHA; exact Hlc | apply IHb1; exact Hlc | apply IHb2; exact Hlc].
  - simpl. f_equal; [apply IHA; exact Hlc | apply IHB; exact Hlc].
  - simpl. f_equal; [apply IHA; exact Hlc | apply IHb; exact Hlc].
  - simpl. f_equal; [apply IHA; exact Hlc | apply IHb; exact Hlc].
  - simpl. f_equal; [apply IHA; exact Hlc | apply IHB; exact Hlc].
  - simpl. f_equal; [apply IHA; exact Hlc | apply IHb; exact Hlc].
  - simpl. f_equal. apply IHA; exact Hlc.
  - simpl. f_equal. apply IHA; exact Hlc.
Qed.

Lemma open_subst_samevar : forall (k:nat) (s:tm) x (b:tm),
  x \notin fv_tm_tm b ->
  open_tm_wrt_tm_rec k s b = subst_tm_tm s x (open_tm_wrt_tm_rec k (a_Var_f x) b).
Proof.
  intros k s x b Hfv. revert k s Hfv.
  induction b as
    [| | psi A IHA B IHB | psi A IHA b IHb | a IHA psi b IHb | s0 | n | z
    | A1 IHA1 A2 IHA2 | a IHA | a IHA | psi a IHA b1 IHb1 b2 IHb2
    | psi A IHA B IHB | a IHA psi b IHb | psi a IHA b IHb
    | psi A IHA B IHB | a IHA psi b IHb | psi a IHA | psi a IHA];
    intros k s Hfv.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. f_equal; [apply IHA; apply notin_union_1 in Hfv; exact Hfv
                    | apply IHB; apply notin_union_2 in Hfv; exact Hfv].
  - simpl. f_equal; [apply IHA; apply notin_union_1 in Hfv; exact Hfv
                    | apply IHb; apply notin_union_2 in Hfv; exact Hfv].
  - simpl. f_equal; [apply IHA; apply notin_union_1 in Hfv; exact Hfv
                    | apply IHb; apply notin_union_2 in Hfv; exact Hfv].
  - simpl. reflexivity.
  - destruct (lt_eq_lt_dec n k) as [[Hlt|Heq]|Hgt].
    + rewrite (@open_rec_var_b_lt k s n Hlt).
      rewrite (@open_rec_var_b_lt k (a_Var_f x) n Hlt).
      rewrite (@subst_notin (a_Var_b n) s x) by (apply notin_empty_1).
      reflexivity.
    + subst n.
      rewrite (@open_rec_var_b_eq k s).
      rewrite (@open_rec_var_b_eq k (a_Var_f x)).
      simpl. rewrite (eq_dec_refl x). reflexivity.
    + rewrite (@open_rec_var_b_gt k s n Hgt).
      rewrite (@open_rec_var_b_gt k (a_Var_f x) n Hgt).
      rewrite (@subst_notin (a_Var_b (n-1)) s x) by (apply notin_empty_1).
      reflexivity.
  - simpl. apply notin_singleton_1 in Hfv.
    destruct (eq_var z x) as [e|ne].
    + exfalso. apply (Hfv e).
    + reflexivity.
  - simpl. f_equal.
    + apply IHA1. apply notin_union_1 in Hfv; exact Hfv.
    + apply IHA2. apply notin_union_2 in Hfv; exact Hfv.
  - simpl. f_equal. apply IHA. exact Hfv.
  - simpl. f_equal. apply IHA. exact Hfv.
  - simpl. f_equal.
    + apply IHA. apply notin_union_1 in Hfv; exact Hfv.
    + apply IHb1. apply notin_union_2 in Hfv; apply notin_union_1 in Hfv; exact Hfv.
    + apply IHb2. apply notin_union_2 in Hfv; apply notin_union_2 in Hfv; exact Hfv.
  - simpl. f_equal; [apply IHA; apply notin_union_1 in Hfv; exact Hfv
                    | apply IHB; apply notin_union_2 in Hfv; exact Hfv].
  - simpl. f_equal; [apply IHA; apply notin_union_1 in Hfv; exact Hfv
                    | apply IHb; apply notin_union_2 in Hfv; exact Hfv].
  - simpl. f_equal; [apply IHA; apply notin_union_1 in Hfv; exact Hfv
                    | apply IHb; apply notin_union_2 in Hfv; exact Hfv].
  - simpl. f_equal; [apply IHA; apply notin_union_1 in Hfv; exact Hfv
                    | apply IHB; apply notin_union_2 in Hfv; exact Hfv].
  - simpl. f_equal; [apply IHA; apply notin_union_1 in Hfv; exact Hfv
                    | apply IHb; apply notin_union_2 in Hfv; exact Hfv].
  - simpl. f_equal. apply IHA. exact Hfv.
  - simpl. f_equal. apply IHA. exact Hfv.
Qed.

Lemma erasure_open : forall (phi:grade) (k:nat) (r b:tm),
  erasure phi (open_tm_wrt_tm_rec k r b) =
  open_tm_wrt_tm_rec k (erasure phi r) (erasure phi b).
Proof.
  intros phi k r b. revert k r.
  induction b as
    [| | psi A IHA B IHB | psi A IHA b IHb | a IHA psi b IHb | s | n | z
    | A1 IHA1 A2 IHA2 | a IHA | a IHA | psi a IHA b1 IHb1 b2 IHb2
    | psi A IHA B IHB | a IHA psi b IHb | psi a IHA b IHb
    | psi A IHA B IHB | a IHA psi b IHb | psi a IHA | psi a IHA];
    intros k r.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. f_equal.
    + apply IHA.
    + apply IHB.
  - simpl. destruct (q_leb q_Top phi) eqn:E; simpl.
    + f_equal.
      * apply IHA.
      * apply IHb.
    + f_equal. apply IHb.
  - simpl. destruct (q_leb psi phi) eqn:E; simpl.
    + f_equal.
      * apply IHA.
      * apply IHb.
    + f_equal. apply IHA.
  - simpl. reflexivity.
  - destruct (lt_eq_lt_dec n k) as [[Hlt|Heq]|Hgt].
    + rewrite (@open_rec_var_b_lt k r n Hlt).
      replace (erasure phi (a_Var_b n)) with (a_Var_b n) by reflexivity.
      rewrite (@open_rec_var_b_lt k (erasure phi r) n Hlt). reflexivity.
    + subst n. rewrite (@open_rec_var_b_eq k r).
      replace (erasure phi (a_Var_b k)) with (a_Var_b k) by reflexivity.
      rewrite (@open_rec_var_b_eq k (erasure phi r)). reflexivity.
    + rewrite (@open_rec_var_b_gt k r n Hgt).
      replace (erasure phi (a_Var_b (n-1))) with (a_Var_b (n-1)) by reflexivity.
      replace (erasure phi (a_Var_b n)) with (a_Var_b n) by reflexivity.
      rewrite (@open_rec_var_b_gt k (erasure phi r) n Hgt). reflexivity.
  - simpl. reflexivity.
  - simpl. f_equal.
    + apply IHA1.
    + apply IHA2.
  - simpl. f_equal. apply IHA.
  - simpl. f_equal. apply IHA.
  - simpl. f_equal.
    + apply IHA.
    + apply IHb1.
    + apply IHb2.
  - simpl. f_equal.
    + apply IHA.
    + apply IHB.
  - simpl. destruct (q_leb psi phi) eqn:E; simpl.
    + f_equal.
      * apply IHA.
      * apply IHb.
    + f_equal. apply IHb.
  - simpl. f_equal.
    + apply IHA.
    + apply IHb.
  - simpl. f_equal.
    + apply IHA.
    + apply IHB.
  - simpl. destruct (q_leb psi phi) eqn:E; simpl.
    + f_equal.
      * apply IHA.
      * apply IHb.
    + f_equal. apply IHb.
  - simpl. f_equal. apply IHA.
  - simpl. f_equal. apply IHA.
Qed.

Lemma erasure_lc_alt : forall (a:tm) (phi:grade) k,
  lc_alt k a -> lc_alt k (erasure phi a).
Proof.
  intros a. induction a as
    [| | psi A IHA B IHB | psi A IHA b IHb | a IHA psi b IHb | s | n | z
    | A1 IHA1 A2 IHA2 | a IHA | a IHA | psi a IHA b1 IHb1 b2 IHb2
    | psi A IHA B IHB | a IHA psi b IHb | psi a IHA b IHb
    | psi A IHA B IHB | a IHA psi b IHb | psi a IHA | psi a IHA];
    intros phi k H.
  - constructor.
  - constructor.
  - apply lc_alt_Pi_inv in H. destruct H as [HA HB]. simpl. apply Lc_Pi.
    + apply IHA; exact HA.
    + apply IHB; exact HB.
  - simpl. destruct (q_leb q_Top phi) eqn:E; simpl; apply Lc_Abs.
    + apply IHA; apply lc_alt_Abs_inv in H; apply (proj1 H).
    + apply IHb; apply lc_alt_Abs_inv in H; apply (proj2 H).
    + constructor.
    + apply IHb; apply lc_alt_Abs_inv in H; apply (proj2 H).
  - simpl. destruct (q_leb psi phi) eqn:E; simpl; apply Lc_App.
    + apply IHA; apply lc_alt_App_inv in H; apply (proj1 H).
    + apply IHb; apply lc_alt_App_inv in H; apply (proj2 H).
    + apply IHA; apply lc_alt_App_inv in H; apply (proj1 H).
    + constructor.
  - constructor.
  - apply lc_alt_var_b_inv in H. simpl. apply Lc_b. exact H.
  - constructor.
  - apply lc_alt_Sum_inv in H. destruct H as [HA HB]. simpl. apply Lc_Sum.
    + apply IHA1; exact HA.
    + apply IHA2; exact HB.
  - apply lc_alt_Inj1_inv in H. simpl. apply Lc_Inj1. apply IHA; exact H.
  - apply lc_alt_Inj2_inv in H. simpl. apply Lc_Inj2. apply IHA; exact H.
  - apply lc_alt_Case_inv in H. destruct H as [HA [HB1 HB2]]. simpl. apply Lc_Case.
    + apply IHA; exact HA.
    + apply IHb1; exact HB1.
    + apply IHb2; exact HB2.
  - apply lc_alt_WSigma_inv in H. destruct H as [HA HB]. simpl. apply Lc_WSigma.
    + apply IHA; exact HA.
    + apply IHB; exact HB.
  - simpl. destruct (q_leb psi phi) eqn:E; simpl; apply Lc_WPair.
    + apply IHA; apply lc_alt_WPair_inv in H; apply (proj1 H).
    + apply IHb; apply lc_alt_WPair_inv in H; apply (proj2 H).
    + constructor.
    + apply IHb; apply lc_alt_WPair_inv in H; apply (proj2 H).
  - apply lc_alt_LetPair_inv in H. destruct H as [HA HB]. simpl. apply Lc_LetPair.
    + apply IHA; exact HA.
    + apply IHb; exact HB.
  - apply lc_alt_SSigma_inv in H. destruct H as [HA HB]. simpl. apply Lc_SSigma.
    + apply IHA; exact HA.
    + apply IHB; exact HB.
  - simpl. destruct (q_leb psi phi) eqn:E; simpl; apply Lc_SPair.
    + apply IHA; apply lc_alt_SPair_inv in H; apply (proj1 H).
    + apply IHb; apply lc_alt_SPair_inv in H; apply (proj2 H).
    + constructor.
    + apply IHb; apply lc_alt_SPair_inv in H; apply (proj2 H).
  - apply lc_alt_Proj1_inv in H. simpl. apply Lc_Proj1. apply IHA; exact H.
  - apply lc_alt_Proj2_inv in H. simpl. apply Lc_Proj2. apply IHA; exact H.
Qed.

Lemma erasure_lc : forall (phi:grade) (a:tm),
  lc_tm a -> lc_tm (erasure phi a).
Proof.
  intros phi a H. apply lc_tm_iff_lc_alt. apply erasure_lc_alt.
  apply lc_tm_iff_lc_alt. exact H.
Qed.

(* Mutual induction principles for the two families of relations *)
Scheme GEq_mut := Induction for GEq Sort Prop
  with CEq_mut := Induction for CEq Sort Prop.
Combined Scheme GEqCEq_ind from GEq_mut, CEq_mut.
Scheme CGrade_mut := Induction for CGrade Sort Prop
  with Grade_mut := Induction for Grade Sort Prop.
Combined Scheme CGradeGrade_ind from CGrade_mut, Grade_mut.

Lemma GEq_uniq : forall P psi a b, GEq P psi a b -> uniq P.
Proof.
  intros P psi a b H. induction H.
  - assumption.
  - assumption.
  - assumption.
  - match goal with
    | H : forall zz, zz \notin L -> uniq _ |- uniq P =>
        destruct (atom_fresh L) as [z Hz]; specialize (H z Hz);
        apply uniq_cons_1 in H; exact H
    end.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
Qed.

Lemma CEq_uniq : forall P psi psi0 a b, CEq P psi psi0 a b -> uniq P.
Proof.
  intros P psi psi0 a b H. induction H.
  - eapply GEq_uniq; eassumption.
  - assumption.
Qed.

Lemma lc_alt_body_of_open : forall (L:vars) (b:tm),
  (forall x, x \notin L -> lc_tm (open_tm_wrt_tm_rec 0 (a_Var_f x) b)) ->
  lc_alt 1 b.
Proof.
  intros L b H.
  destruct (atom_fresh L) as [z Hz].
  apply (@lc_alt_open_bwd 0 b z).
  apply (proj1 (lc_tm_iff_lc_alt _)). apply H. exact Hz.
Qed.

Lemma GEq_CEq_lc :
  (forall P psi a b, GEq P psi a b -> lc_tm a /\ lc_tm b) /\
  (forall P psi psi0 a b, CEq P psi psi0 a b -> lc_tm a /\ lc_tm b).
Proof.
  apply GEqCEq_ind with
    (P := fun P psi a b (_:GEq P psi a b) => lc_tm a /\ lc_tm b)
    (P0 := fun P psi psi0 a b (_:CEq P psi psi0 a b) => lc_tm a /\ lc_tm b).
  - (* GEq_Var *) intros. split; apply lc_a_Var_f.
  - (* GEq_Type *) intros. split; apply lc_a_Type.
  - (* GEq_Pi *) intros L P psi psi0 A1 B1 A2 B2 g IHg body IHbody.
    destruct IHg as [HA1 HA2]. split.
    + apply lc_tm_iff_lc_alt. apply Lc_Pi.
      * apply lc_tm_iff_lc_alt. exact HA1.
      * apply lc_alt_body_of_open with (L:=L).
        intros z Hz. apply (proj1 (IHbody z Hz)).
    + apply lc_tm_iff_lc_alt. apply Lc_Pi.
      * apply lc_tm_iff_lc_alt. exact HA2.
      * apply lc_alt_body_of_open with (L:=L).
        intros z Hz. apply (proj2 (IHbody z Hz)).
  - (* GEq_Abs *) intros L P psi psi0 A1 b1 A2 b2 g IHbody c IHc.
    destruct IHc as [HA1 HA2]. split.
    + apply lc_tm_iff_lc_alt. apply Lc_Abs.
      * apply lc_tm_iff_lc_alt. exact HA1.
      * apply lc_alt_body_of_open with (L:=L).
        intros z Hz. apply (proj1 (IHbody z Hz)).
    + apply lc_tm_iff_lc_alt. apply Lc_Abs.
      * apply lc_tm_iff_lc_alt. exact HA2.
      * apply lc_alt_body_of_open with (L:=L).
        intros z Hz. apply (proj2 (IHbody z Hz)).
  - (* GEq_App *) intros P psi b1 psi0 a1 b2 a2 g IHg c IHc.
    destruct IHg as [H1 H2]. destruct IHc as [H3 H4]. split; apply lc_a_App; assumption.
  - (* GEq_WSigma *) intros L P psi psi0 A1 B1 A2 B2 g IHg body IHbody.
    destruct IHg as [HA1 HA2]. split.
    + apply lc_tm_iff_lc_alt. apply Lc_WSigma.
      * apply lc_tm_iff_lc_alt. exact HA1.
      * apply lc_alt_body_of_open with (L:=L).
        intros z Hz. apply (proj1 (IHbody z Hz)).
    + apply lc_tm_iff_lc_alt. apply Lc_WSigma.
      * apply lc_tm_iff_lc_alt. exact HA2.
      * apply lc_alt_body_of_open with (L:=L).
        intros z Hz. apply (proj2 (IHbody z Hz)).
  - (* GEq_WPair *) intros P psi a1 psi0 b1 a2 b2 c IHc g IHg.
    destruct IHc as [H1 H2]. destruct IHg as [H3 H4]. split; apply lc_a_WPair; assumption.
  - (* GEq_LetPair *) intros L P psi psi0 a1 b1 a2 b2 g IHg body IHbody.
    destruct IHg as [HA1 HA2]. split.
    + apply lc_tm_iff_lc_alt. apply Lc_LetPair.
      * apply lc_tm_iff_lc_alt. exact HA1.
      * apply lc_alt_body_of_open with (L:=L).
        intros z Hz. apply (proj1 (IHbody z Hz)).
    + apply lc_tm_iff_lc_alt. apply Lc_LetPair.
      * apply lc_tm_iff_lc_alt. exact HA2.
      * apply lc_alt_body_of_open with (L:=L).
        intros z Hz. apply (proj2 (IHbody z Hz)).
  - (* GEq_SSigma *) intros L P psi psi0 A1 B1 A2 B2 g IHg body IHbody.
    destruct IHg as [HA1 HA2]. split.
    + apply lc_tm_iff_lc_alt. apply Lc_SSigma.
      * apply lc_tm_iff_lc_alt. exact HA1.
      * apply lc_alt_body_of_open with (L:=L).
        intros z Hz. apply (proj1 (IHbody z Hz)).
    + apply lc_tm_iff_lc_alt. apply Lc_SSigma.
      * apply lc_tm_iff_lc_alt. exact HA2.
      * apply lc_alt_body_of_open with (L:=L).
        intros z Hz. apply (proj2 (IHbody z Hz)).
  - (* GEq_SPair *) intros P psi a1 psi0 b1 a2 b2 c IHc g IHg.
    destruct IHc as [H1 H2]. destruct IHg as [H3 H4]. split; apply lc_a_SPair; assumption.
  - (* GEq_Proj1 *) intros P psi psi0 a1 a2 g IHg i. destruct IHg as [H1 H2].
    split; apply lc_a_Proj1; assumption.
  - (* GEq_Proj2 *) intros P psi psi0 a1 a2 g IHg. destruct IHg as [H1 H2].
    split; apply lc_a_Proj2; assumption.
  - (* GEq_Sum *) intros P psi A1 A2 A1' A2' g IHg g0 IHg0.
    destruct IHg as [H1 H2]. destruct IHg0 as [H3 H4]. split; apply lc_a_Sum; assumption.
  - (* GEq_Inj1 *) intros P psi a1 a1' g IHg. destruct IHg as [H1 H2].
    split; apply lc_a_Inj1; assumption.
  - (* GEq_Inj2 *) intros P psi a2 a2' g IHg. destruct IHg as [H1 H2].
    split; apply lc_a_Inj2; assumption.
  - (* GEq_Case *) intros P psi psi0 a b1 b2 a' b1' b2' g IHg g0 IHg0 g1 IHg1 i.
    destruct IHg as [H1 H2]. destruct IHg0 as [H3 H4]. destruct IHg1 as [H5 H6].
    split; apply lc_a_Case; assumption.
  - (* GEq_TyUnit *) intros. split; apply lc_a_TyUnit.
  - (* GEq_TmUnit *) intros. split; apply lc_a_TmUnit.
  - (* CEq_Leq *) intros P psi psi0 a1 a2 i g IHg. exact IHg.
  - (* CEq_Nleq *) intros P psi psi0 a1 a2 l1 l2 n u. split; assumption.
Qed.

Lemma GEq_lc : forall P psi a b, GEq P psi a b -> lc_tm a /\ lc_tm b.
Proof. intros P psi a b H. exact (proj1 GEq_CEq_lc P psi a b H). Qed.

Lemma CEq_lc : forall P psi psi0 a b, CEq P psi psi0 a b -> lc_tm a /\ lc_tm b.
Proof. intros P psi psi0 a b H. exact (proj2 GEq_CEq_lc P psi psi0 a b H). Qed.

Lemma Step_lc : forall a b, Step a b -> lc_tm a -> lc_tm b.
Proof.
  intros a b H. induction H; intros Hlc.
  - apply lc_tm_App_inv in Hlc. destruct Hlc as [Ha Hb].
    apply lc_a_App.
    + apply IHStep. exact Ha.
    + exact Hb.
  - apply lc_tm_App_inv in Hlc. destruct Hlc as [HAbs Hb].
    apply lc_tm_Abs_inv in HAbs. destruct HAbs as [HA Hbody].
    apply lc_tm_iff_lc_alt.
    apply (@lc_alt_open_body 0 b a).
    + apply lc_tm_iff_lc_alt. exact Hb.
    + apply lc_alt_body_of_open with (L:=empty). intros x Hx. apply Hbody.
  - apply lc_tm_Case_inv in Hlc. destruct Hlc as [Ha [Hb1 Hb2]].
    apply lc_a_Case.
    + apply IHStep. exact Ha.
    + exact Hb1.
    + exact Hb2.
  - apply lc_tm_Case_inv in Hlc. destruct Hlc as [Hinj [Hb1 Hb2]].
    apply lc_tm_Inj1_inv in Hinj.
    apply lc_a_App.
    + exact Hb1.
    + exact Hinj.
  - apply lc_tm_Case_inv in Hlc. destruct Hlc as [Hinj [Hb1 Hb2]].
    apply lc_tm_Inj2_inv in Hinj.
    apply lc_a_App.
    + exact Hb2.
    + exact Hinj.
  - apply lc_tm_Proj1_inv in Hlc. apply lc_a_Proj1. apply IHStep. exact Hlc.
  - apply lc_tm_Proj2_inv in Hlc. apply lc_a_Proj2. apply IHStep. exact Hlc.
  - apply lc_tm_Proj1_inv in Hlc. apply lc_tm_SPair_inv in Hlc.
    apply (proj1 Hlc).
  - apply lc_tm_Proj2_inv in Hlc. apply lc_tm_SPair_inv in Hlc.
    apply (proj2 Hlc).
  - apply lc_tm_LetPair_inv in Hlc. destruct Hlc as [Ha Hbody].
    apply lc_a_LetPair.
    + apply IHStep. exact Ha.
    + exact Hbody.
  - apply lc_tm_LetPair_inv in Hlc. destruct Hlc as [HWP Hbody].
    apply lc_tm_WPair_inv in HWP. destruct HWP as [Ha1 Ha2].
    apply lc_a_App.
    + apply lc_tm_iff_lc_alt.
      apply (@lc_alt_open_body 0 a1 b).
      * apply lc_tm_iff_lc_alt. exact Ha1.
      * apply lc_alt_body_of_open with (L:=empty). intros x Hx. apply Hbody.
    + exact Ha2.
Qed.

(* ================================================================ *)
(* Removing one binding from an evaluation context                  *)
(* ================================================================ *)

Fixpoint Crm (x:atom) (C:econtext) : econtext :=
  match C with
  | nil => nil
  | (y,g) :: C' => if eq_var y x then Crm x C' else (y,g) :: Crm x C'
  end.

Lemma Crm_cons_eq : forall x g C,
  Crm x ((x,g)::C) = Crm x C.
Proof.
  intros x g C. simpl.
  destruct (eq_var x x) as [e|n].
  - reflexivity.
  - exfalso. apply n. reflexivity.
Qed.

Lemma Crm_cons_neq : forall y x g C,
  y <> x -> Crm x ((y,g)::C) = (y,g)::Crm x C.
Proof.
  intros y x g C Hne. simpl.
  destruct (eq_var y x) as [e|n]; [exfalso; apply (Hne e)|reflexivity].
Qed.

Lemma Crm_cons_neq_list : forall z x g (C:econtext),
  z <> x -> Crm x ((z~g)++C) = (z~g)++Crm x C.
Proof.
  intros z x g C H. change (Crm x ((z,g)::C) = (z,g)::Crm x C).
  apply (@Crm_cons_neq z x g C H).
Qed.

Lemma Crm_binds_inv : forall y g x C,
  binds y g (Crm x C) -> y <> x /\ binds y g C.
Proof.
  intros y g x C. induction C as [|(z,h) C IH]; intro Hb.
  - simpl in Hb. apply binds_nil_iff in Hb. destruct Hb.
  - destruct (eq_var z x) as [e|ne].
    + subst z. rewrite Crm_cons_eq in Hb.
      apply IH in Hb. destruct Hb as [Hne HC]. split; [exact Hne|].
      apply binds_cons_3. exact HC.
    + rewrite (@Crm_cons_neq z x h C ne) in Hb.
      apply binds_cons_1 in Hb. destruct Hb as [[Heq Hg]|HC].
      * subst y. subst g. split; [exact ne|apply binds_cons_2; [reflexivity|reflexivity]].
      * apply IH in HC. destruct HC as [Hne HC]. split; [exact Hne|apply binds_cons_3; exact HC].
Qed.

Lemma Crm_binds : forall y g x C,
  y <> x -> binds y g C -> binds y g (Crm x C).
Proof.
  intros y g x C Hne. induction C as [|(z,h) C IH]; intro Hb.
  - simpl. exact Hb.
  - destruct (eq_var z x) as [e|ne].
    + subst z. rewrite Crm_cons_eq.
      apply binds_cons_1 in Hb. destruct Hb as [[Heq Hg]|HC].
      * exfalso. apply (Hne Heq).
      * apply IH. exact HC.
    + rewrite (@Crm_cons_neq z x h C ne).
      apply binds_cons_1 in Hb. destruct Hb as [[Heq Hg]|HC].
      * subst y. subst g. apply binds_cons_2; [reflexivity|reflexivity].
      * apply binds_cons_3. apply IH. exact HC.
Qed.

Lemma Crm_notin_dom : forall z x C,
  z <> x -> (z \notin dom (Crm x C) <-> z \notin dom C).
Proof.
  intros z x C Hne. split.
  - intro Hnot. intro Hin.
    destruct (@binds_In_inv _ _ _ Hin) as [g Hb].
    apply Hnot. apply (@binds_In _ z g (Crm x C)). apply Crm_binds; assumption.
  - intro Hnot. intro Hin.
    destruct (@binds_In_inv _ _ _ Hin) as [g Hb].
    apply Crm_binds_inv in Hb. destruct Hb as [Hne' HC].
    apply Hnot. apply (@binds_In _ z g C). exact HC.
Qed.

Lemma Crm_uniq : forall x C, uniq C -> uniq (Crm x C).
Proof.
  intros x C. induction C as [|(y,g) C IH]; intro Hu.
  - simpl. apply uniq_nil.
  - destruct (eq_var y x) as [e|ne].
    + subst y. rewrite Crm_cons_eq. apply IH. apply uniq_cons_1 in Hu. exact Hu.
    + rewrite (@Crm_cons_neq y x g C ne).
      apply uniq_cons_3.
      * apply IH. apply uniq_cons_1 in Hu. exact Hu.
      * apply Crm_notin_dom. exact ne. apply uniq_cons_2 in Hu. exact Hu.
Qed.

Lemma notin_dom_tail : forall y z g (P:econtext),
  y \notin dom ((z~g)++P) -> y \notin dom P.
Proof.
  intros y z g P Hnot Hin.
  destruct (@binds_In_inv _ _ _ Hin) as [g' Hb].
  apply Hnot. apply (@binds_In _ y g' ((z~g)++P)). apply binds_cons_3. exact Hb.
Qed.

Lemma notin_dom_head : forall y z g (P:econtext),
  y \notin dom P -> y <> z -> y \notin dom ((z~g)++P).
Proof.
  intros y z g P Hnot Hneq Hin.
  destruct (@binds_In_inv _ _ _ Hin) as [g' Hb].
  apply binds_cons_1 in Hb. destruct Hb as [[Heq _]|Hb].
  - apply (Hneq Heq).
  - apply Hnot. apply (@binds_In _ y g' P). exact Hb.
Qed.

Lemma notin_dom_insert : forall z y g (P1 P2:econtext),
  z \notin dom (P1++P2) -> z <> y -> z \notin dom (P1++(y~g)++P2).
Proof.
  intros z y g P1 P2 Hnot Hneq Hin.
  destruct (@binds_In_inv _ _ _ Hin) as [g' Hb].
  apply binds_app_iff in Hb. destruct Hb as [Hb|Hb].
  - apply Hnot. apply (@binds_In _ z g' (P1++P2)). apply binds_app_2. exact Hb.
  - apply binds_cons_1 in Hb. destruct Hb as [[Heq _]|Hb].
    + apply (Hneq Heq).
    + apply Hnot. apply (@binds_In _ z g' (P1++P2)). apply binds_app_3. exact Hb.
Qed.

Lemma uniq_insert_mid : forall (P1 P2:econtext) y g,
  uniq (P1++P2) -> y \notin dom (P1++P2) -> uniq (P1++(y~g)++P2).
Proof.
  intros P1. induction P1 as [|(z,h) P1 IH]; intros P2 y g Hu Hnot.
  - change (uniq ((y,g)::P2)). apply uniq_cons_3.
    + simpl in Hu. exact Hu.
    + simpl in Hnot. exact Hnot.
  - change (uniq ((z,h) :: (P1 ++ (y~g) ++ P2))). apply uniq_cons_3.
    + apply IH.
      * apply uniq_cons_1 in Hu. exact Hu.
      * apply notin_dom_tail in Hnot. exact Hnot.
    + apply notin_dom_insert.
      * apply uniq_cons_2 in Hu. exact Hu.
      * intro Heq. subst z. exfalso.
        apply Hnot.
        apply (@binds_In _ y h ((y,h)::(P1++P2))).
        apply binds_cons_2; [reflexivity|reflexivity].
Qed.

Lemma GEq_CEq_weaken :
  (forall P psi a b, GEq P psi a b ->
     forall y g P1 P2, P = P1++P2 -> y \notin dom P ->
       GEq (P1++(y~g)++P2) psi a b) /\
  (forall P psi psi0 a b, CEq P psi psi0 a b ->
     forall y g P1 P2, P = P1++P2 -> y \notin dom P ->
       CEq (P1++(y~g)++P2) psi psi0 a b).
Proof.
  apply GEqCEq_ind with
    (P := fun P psi a b (_:GEq P psi a b) =>
       forall y g P1 P2, P = P1++P2 -> y \notin dom P ->
         GEq (P1++(y~g)++P2) psi a b)
    (P0 := fun P psi psi0 a b (_:CEq P psi psi0 a b) =>
       forall y g P1 P2, P = P1++P2 -> y \notin dom P ->
         CEq (P1++(y~g)++P2) psi psi0 a b).
  - (* Var *) intros P psi x psi0 u b i. intros y g P1 P2 Heq Hy. subst P.
    apply GEq_Var with (psi0:=psi0).
    + apply uniq_insert_mid; assumption.
    + apply binds_weaken. exact b.
    + exact i.
  - (* Type *) intros P psi s u. intros y g P1 P2 Heq Hy. subst P.
    apply GEq_Type. apply uniq_insert_mid; assumption.
  - (* Pi *) intros L P psi psi0 A1 B1 A2 B2 gd IHg body IHbody.
    intros y g P1 P2 Heq Hy. subst P.
    apply (@GEq_Pi (L \u {{y}}) (P1++(y~g)++P2) psi psi0 A1 B1 A2 B2).
    + apply IHg. reflexivity. exact Hy.
    + intros z Hz.
      assert (HzL : z \notin L) by (exact (@notin_union_1 z L {{y}} Hz)).
      assert (HzY : z \notin {{y}}) by (exact (@notin_union_2 z L {{y}} Hz)).
      apply notin_singleton_1 in HzY.
      apply (IHbody z HzL y g ((z~psi)++P1) P2). reflexivity.
      apply notin_dom_head; [exact Hy|exact HzY].
  - (* Abs *) intros L P psi psi0 A1 b1 A2 b2 gd IHbody c IHc.
    intros y g P1 P2 Heq Hy. subst P.
    apply (@GEq_Abs (L \u {{y}}) (P1++(y~g)++P2) psi psi0 A1 b1 A2 b2).
    + intros z Hz.
      assert (HzL : z \notin L) by (exact (@notin_union_1 z L {{y}} Hz)).
      assert (HzY : z \notin {{y}}) by (exact (@notin_union_2 z L {{y}} Hz)).
      apply notin_singleton_1 in HzY.
      apply (IHbody z HzL y g ((z~psi0)++P1) P2). reflexivity.
      apply notin_dom_head; [exact Hy|exact HzY].
    + apply IHc. reflexivity. exact Hy.
  - (* App *) intros P psi b1 psi0 a1 b2 a2 gd IHg c IHc.
    intros y g P1 P2 Heq Hy. subst P.
    apply GEq_App.
    + apply IHg. reflexivity. exact Hy.
    + apply IHc. reflexivity. exact Hy.
  - (* WSigma *) intros L P psi psi0 A1 B1 A2 B2 gd IHg body IHbody.
    intros y g P1 P2 Heq Hy. subst P.
    apply (@GEq_WSigma (L \u {{y}}) (P1++(y~g)++P2) psi psi0 A1 B1 A2 B2).
    + apply IHg. reflexivity. exact Hy.
    + intros z Hz.
      assert (HzL : z \notin L) by (exact (@notin_union_1 z L {{y}} Hz)).
      assert (HzY : z \notin {{y}}) by (exact (@notin_union_2 z L {{y}} Hz)).
      apply notin_singleton_1 in HzY.
      apply (IHbody z HzL y g ((z~psi)++P1) P2). reflexivity.
      apply notin_dom_head; [exact Hy|exact HzY].
  - (* WPair *) intros P psi a1 psi0 b1 a2 b2 c IHc gd IHg.
    intros y g P1 P2 Heq Hy. subst P.
    apply GEq_WPair.
    + apply IHc. reflexivity. exact Hy.
    + apply IHg. reflexivity. exact Hy.
  - (* LetPair *) intros L P psi psi0 a1 b1 a2 b2 gd IHg body IHbody.
    intros y g P1 P2 Heq Hy. subst P.
    apply (@GEq_LetPair (L \u {{y}}) (P1++(y~g)++P2) psi psi0 a1 b1 a2 b2).
    + apply IHg. reflexivity. exact Hy.
    + intros z Hz.
      assert (HzL : z \notin L) by (exact (@notin_union_1 z L {{y}} Hz)).
      assert (HzY : z \notin {{y}}) by (exact (@notin_union_2 z L {{y}} Hz)).
      apply notin_singleton_1 in HzY.
      apply (IHbody z HzL y g ((z~psi0)++P1) P2). reflexivity.
      apply notin_dom_head; [exact Hy|exact HzY].
  - (* SSigma *) intros L P psi psi0 A1 B1 A2 B2 gd IHg body IHbody.
    intros y g P1 P2 Heq Hy. subst P.
    apply (@GEq_SSigma (L \u {{y}}) (P1++(y~g)++P2) psi psi0 A1 B1 A2 B2).
    + apply IHg. reflexivity. exact Hy.
    + intros z Hz.
      assert (HzL : z \notin L) by (exact (@notin_union_1 z L {{y}} Hz)).
      assert (HzY : z \notin {{y}}) by (exact (@notin_union_2 z L {{y}} Hz)).
      apply notin_singleton_1 in HzY.
      apply (IHbody z HzL y g ((z~psi)++P1) P2). reflexivity.
      apply notin_dom_head; [exact Hy|exact HzY].
  - (* SPair *) intros P psi a1 psi0 b1 a2 b2 c IHc gd IHg.
    intros y g P1 P2 Heq Hy. subst P.
    apply GEq_SPair.
    + apply IHc. reflexivity. exact Hy.
    + apply IHg. reflexivity. exact Hy.
  - (* Proj1 *) intros P psi psi0 a1 a2 gd IHg i.
    intros y g P1 P2 Heq Hy. subst P.
    apply GEq_Proj1; [apply IHg; [reflexivity|exact Hy]|exact i].
  - (* Proj2 *) intros P psi psi0 a1 a2 gd IHg.
    intros y g P1 P2 Heq Hy. subst P.
    apply GEq_Proj2. apply IHg. reflexivity. exact Hy.
  - (* Sum *) intros P psi A1 A2 A1' A2' gd IHg gd0 IHg0.
    intros y g P1 P2 Heq Hy. subst P.
    apply GEq_Sum.
    + apply IHg. reflexivity. exact Hy.
    + apply IHg0. reflexivity. exact Hy.
  - (* Inj1 *) intros P psi a1 a1' gd IHg.
    intros y g P1 P2 Heq Hy. subst P.
    apply GEq_Inj1. apply IHg. reflexivity. exact Hy.
  - (* Inj2 *) intros P psi a2 a2' gd IHg.
    intros y g P1 P2 Heq Hy. subst P.
    apply GEq_Inj2. apply IHg. reflexivity. exact Hy.
  - (* Case *) intros P psi psi0 a b1 b2 a' b1' b2' gd IHg gd0 IHg0 gd1 IHg1 i.
    intros y g P1 P2 Heq Hy. subst P.
    apply GEq_Case.
    + apply IHg. reflexivity. exact Hy.
    + apply IHg0. reflexivity. exact Hy.
    + apply IHg1. reflexivity. exact Hy.
    + exact i.
  - (* TyUnit *) intros P psi u. intros y g P1 P2 Heq Hy. subst P.
    apply GEq_TyUnit. apply uniq_insert_mid; assumption.
  - (* TmUnit *) intros P psi u. intros y g P1 P2 Heq Hy. subst P.
    apply GEq_TmUnit. apply uniq_insert_mid; assumption.
  - (* CEq_Leq *) intros P psi psi0 a1 a2 i gd IHg.
    intros y g P1 P2 Heq Hy. subst P.
    apply CEq_Leq.
    + exact i.
    + apply IHg. reflexivity. exact Hy.
  - (* CEq_Nleq *) intros P psi psi0 a1 a2 l1 l2 n u.
    intros y g P1 P2 Heq Hy. subst P.
    apply CEq_Nleq.
    + exact l1.
    + exact l2.
    + exact n.
    + apply uniq_insert_mid; assumption.
Qed.

Lemma subst_lc : forall (a:tm) x (b:tm),
  lc_tm a -> lc_tm b -> lc_tm (subst_tm_tm a x b).
Proof.
  intros a x b Ha Hb.
  apply lc_tm_iff_lc_alt.
  apply (@lc_alt_subst 0 a x b).
  - apply lc_tm_iff_lc_alt. exact Ha.
  - apply lc_tm_iff_lc_alt. exact Hb.
Qed.

Lemma notin_triple : forall (L:vars) (x z:atom) (D:vars),
  z \notin (L \u {{x}}) \u D -> z \notin L /\ z <> x /\ z \notin D.
Proof.
  intros L x z D Hz.
  assert (H1 : z \notin L \u {{x}})
    by (exact (@notin_union_1 z (L \u {{x}}) D Hz)).
  assert (H2 : z \notin D)
    by (exact (@notin_union_2 z (L \u {{x}}) D Hz)).
  assert (HL : z \notin L)
    by (exact (@notin_union_1 z L {{x}} H1)).
  assert (HX : z \notin {{x}})
    by (exact (@notin_union_2 z L {{x}} H1)).
  apply notin_singleton_1 in HX.
  split; [exact HL|split; [intro Heq; symmetry in Heq; exact (HX Heq)|exact H2]].
Qed.

Lemma CEq_weaken_head : forall (C:econtext) psi psi0 (a1 a2:tm) y g,
  CEq C psi psi0 a1 a2 -> y \notin dom C -> CEq ((y~g)++C) psi psi0 a1 a2.
Proof.
  intros C psi psi0 a1 a2 y g Hc Hy.
  assert (Heq : C = nil ++ C) by reflexivity.
  exact (proj2 GEq_CEq_weaken C psi psi0 a1 a2 Hc y g nil C Heq Hy).
Qed.

Lemma subst_open_comm_TM : forall (s:tm) x (y:atom) (b:tm),
  y <> x -> lc_alt 0 s ->
  subst_tm_tm s x (open_tm_wrt_tm b (a_Var_f y)) =
  open_tm_wrt_tm (subst_tm_tm s x b) (a_Var_f y).
Proof.
  intros s x y b Hne Hlc. unfold open_tm_wrt_tm.
  apply (@subst_open_comm 0 s x y b Hne Hlc).
Qed.

Lemma subst_same : forall (a:tm) x,
  subst_tm_tm a x (a_Var_f x) = a.
Proof.
  intros a x. simpl. rewrite (eq_dec_refl x). reflexivity.
Qed.

Lemma subst_var_neq : forall (a:tm) x y,
  y <> x -> subst_tm_tm a x (a_Var_f y) = a_Var_f y.
Proof.
  intros a x y Hne. simpl.
  destruct (eq_var y x) as [e|ne]; [exfalso; apply (Hne e)|reflexivity].
Qed.

Lemma CEq_leq_GEq : forall P psi psi0 a b,
  psi0 <= psi -> CEq P psi psi0 a b -> GEq P psi a b.
Proof.
  intros P psi psi0 a b Hle Hc.
  destruct Hc as [C0 ps0 psq0 a0 b0 i0 gq|C0 ps0 psq0 a0 b0 l1 l2 n0 u0].
  - exact gq.
  - exfalso. apply n0. exact Hle.
Qed.

Lemma Crm_cons_eq_list : forall x g (C:econtext),
  Crm x ((x~g)++C) = Crm x C.
Proof.
  intros x g C. change (Crm x ((x,g)::C) = Crm x C). apply Crm_cons_eq.
Qed.

Lemma Crm_notin_eq : forall x (C:econtext),
  x \notin dom C -> Crm x C = C.
Proof.
  intros x C. induction C as [|(y,g) C IH]; intro Hnot.
  - reflexivity.
  - destruct (eq_var y x) as [e|ne].
    + subst y. exfalso. apply Hnot.
      apply (@binds_In _ x g ((x,g)::C)). apply binds_cons_2; reflexivity.
    + rewrite (@Crm_cons_neq y x g C ne).
      rewrite IH by (apply notin_dom_tail in Hnot; exact Hnot).
      reflexivity.
Qed.

Lemma GEq_CEq_subst :
  (forall C psi b1 b2, GEq C psi b1 b2 ->
     forall x psi0 a1 a2, binds x psi0 C ->
       CEq (Crm x C) psi psi0 a1 a2 ->
       GEq (Crm x C) psi (subst_tm_tm a1 x b1) (subst_tm_tm a2 x b2)) /\
  (forall C psi psi0 b1 b2, CEq C psi psi0 b1 b2 ->
     forall x psiX a1 a2, binds x psiX C ->
       CEq (Crm x C) psi psiX a1 a2 ->
       CEq (Crm x C) psi psi0 (subst_tm_tm a1 x b1) (subst_tm_tm a2 x b2)).
Proof.
  apply GEqCEq_ind with
    (P := fun C psi b1 b2 (_:GEq C psi b1 b2) =>
       forall x psi0 a1 a2, binds x psi0 C ->
         CEq (Crm x C) psi psi0 a1 a2 ->
         GEq (Crm x C) psi (subst_tm_tm a1 x b1) (subst_tm_tm a2 x b2))
    (P0 := fun C psi psi0 b1 b2 (_:CEq C psi psi0 b1 b2) =>
       forall x psiX a1 a2, binds x psiX C ->
         CEq (Crm x C) psi psiX a1 a2 ->
         CEq (Crm x C) psi psi0 (subst_tm_tm a1 x b1) (subst_tm_tm a2 x b2)).
  - (* GEq_Var *) intros C psi z psi1 u bd i. intros x psi0 a1 a2 Hb Hc.
    destruct (eq_var z x) as [e|ne].
    + subst z.
      rewrite (subst_same a1 x). rewrite (subst_same a2 x).
      apply CEq_leq_GEq with (psi0:=psi0).
      * assert (Heq : psi1 = psi0) by (eapply binds_unique; [exact bd|exact Hb|exact u]).
        rewrite <- Heq. exact i.
      * exact Hc.
    + rewrite (@subst_var_neq a1 x z ne). rewrite (@subst_var_neq a2 x z ne).
      apply GEq_Var with (psi0:=psi1).
      * apply Crm_uniq. exact u.
      * apply Crm_binds; assumption.
      * exact i.
  - (* GEq_Type *) intros C psi s u. intros x psi0 a1 a2 Hb Hc. simpl.
    apply GEq_Type. apply Crm_uniq. exact u.
  - (* GEq_Pi *) intros L C psi psi1 A1 B1 A2 B2 gd IHg body IHbody.
    intros x psi0 a1 a2 Hb Hc. simpl.
    apply (@GEq_Pi ((L \u {{x}}) \u dom (Crm x C)) (Crm x C) psi psi1 (subst_tm_tm a1 x A1) (subst_tm_tm a1 x B1) (subst_tm_tm a2 x A2) (subst_tm_tm a2 x B2)).
    + apply (IHg x psi0 a1 a2 Hb Hc).
    + intros z Hz.
      destruct (@notin_triple L x z (dom (Crm x C)) Hz) as [HzL [Hzx HzD]].
      assert (Hlc1 : lc_alt 0 a1) by (apply lc_tm_iff_lc_alt; apply (proj1 (CEq_lc Hc))).
      assert (Hlc2 : lc_alt 0 a2) by (apply lc_tm_iff_lc_alt; apply (proj2 (CEq_lc Hc))).
      rewrite <- (@subst_open_comm_TM a1 x z B1 Hzx Hlc1).
      rewrite <- (@subst_open_comm_TM a2 x z B2 Hzx Hlc2).
      rewrite <- (@Crm_cons_neq_list z x psi C Hzx).
      assert (Hc' : CEq (Crm x ((z~psi)++C)) psi psi0 a1 a2).
      { rewrite (@Crm_cons_neq_list z x psi C Hzx).
        apply CEq_weaken_head with (y:=z) (g:=psi); assumption. }
      apply (IHbody z HzL x psi0 a1 a2 (@binds_cons_3 grade x z psi0 psi C Hb) Hc').
  - (* GEq_Abs *) intros L C psi psi1 A1 b1 A2 b2 gd IHbody c IHc.
    intros x psi0 a1 a2 Hb Hc. simpl.
    apply (@GEq_Abs ((L \u {{x}}) \u dom (Crm x C)) (Crm x C) psi psi1 (subst_tm_tm a1 x A1) (subst_tm_tm a1 x b1) (subst_tm_tm a2 x A2) (subst_tm_tm a2 x b2)).
    + intros z Hz.
      destruct (@notin_triple L x z (dom (Crm x C)) Hz) as [HzL [Hzx HzD]].
      assert (Hlc1 : lc_alt 0 a1) by (apply lc_tm_iff_lc_alt; apply (proj1 (CEq_lc Hc))).
      assert (Hlc2 : lc_alt 0 a2) by (apply lc_tm_iff_lc_alt; apply (proj2 (CEq_lc Hc))).
      rewrite <- (@subst_open_comm_TM a1 x z b1 Hzx Hlc1).
      rewrite <- (@subst_open_comm_TM a2 x z b2 Hzx Hlc2).
      rewrite <- (@Crm_cons_neq_list z x psi1 C Hzx).
      assert (Hc' : CEq (Crm x ((z~psi1)++C)) psi psi0 a1 a2).
      { rewrite (@Crm_cons_neq_list z x psi1 C Hzx).
        apply CEq_weaken_head with (y:=z) (g:=psi1); assumption. }
      apply (IHbody z HzL x psi0 a1 a2 (@binds_cons_3 grade x z psi0 psi1 C Hb) Hc').
    + apply (IHc x psi0 a1 a2 Hb Hc).
  - (* GEq_App *) intros C psi b1 psi1 a1 b2 a2 gd IHg c IHc.
    intros x psi0 u1 u2 Hb Hc. simpl.
    apply GEq_App.
    + apply (IHg x psi0 u1 u2 Hb Hc).
    + apply (IHc x psi0 u1 u2 Hb Hc).
  - (* GEq_WSigma *) intros L C psi psi1 A1 B1 A2 B2 gd IHg body IHbody.
    intros x psi0 a1 a2 Hb Hc. simpl.
    apply (@GEq_WSigma ((L \u {{x}}) \u dom (Crm x C)) (Crm x C) psi psi1 (subst_tm_tm a1 x A1) (subst_tm_tm a1 x B1) (subst_tm_tm a2 x A2) (subst_tm_tm a2 x B2)).
    + apply (IHg x psi0 a1 a2 Hb Hc).
    + intros z Hz.
      destruct (@notin_triple L x z (dom (Crm x C)) Hz) as [HzL [Hzx HzD]].
      assert (Hlc1 : lc_alt 0 a1) by (apply lc_tm_iff_lc_alt; apply (proj1 (CEq_lc Hc))).
      assert (Hlc2 : lc_alt 0 a2) by (apply lc_tm_iff_lc_alt; apply (proj2 (CEq_lc Hc))).
      rewrite <- (@subst_open_comm_TM a1 x z B1 Hzx Hlc1).
      rewrite <- (@subst_open_comm_TM a2 x z B2 Hzx Hlc2).
      rewrite <- (@Crm_cons_neq_list z x psi C Hzx).
      assert (Hc' : CEq (Crm x ((z~psi)++C)) psi psi0 a1 a2).
      { rewrite (@Crm_cons_neq_list z x psi C Hzx).
        apply CEq_weaken_head with (y:=z) (g:=psi); assumption. }
      apply (IHbody z HzL x psi0 a1 a2 (@binds_cons_3 grade x z psi0 psi C Hb) Hc').
  - (* GEq_WPair *) intros C psi a1 psi1 b1 a2 b2 c IHc gd IHg.
    intros x psi0 u1 u2 Hb Hc. simpl.
    apply GEq_WPair.
    + apply (IHc x psi0 u1 u2 Hb Hc).
    + apply (IHg x psi0 u1 u2 Hb Hc).
  - (* GEq_LetPair *) intros L C psi psi1 a1 b1 a2 b2 gd IHg body IHbody.
    intros x psi0 u1 u2 Hb Hc. simpl.
    apply (@GEq_LetPair ((L \u {{x}}) \u dom (Crm x C)) (Crm x C) psi psi1 (subst_tm_tm u1 x a1) (subst_tm_tm u1 x b1) (subst_tm_tm u2 x a2) (subst_tm_tm u2 x b2)).
    + apply (IHg x psi0 u1 u2 Hb Hc).
    + intros z Hz.
      destruct (@notin_triple L x z (dom (Crm x C)) Hz) as [HzL [Hzx HzD]].
      assert (Hlc1 : lc_alt 0 u1) by (apply lc_tm_iff_lc_alt; apply (proj1 (CEq_lc Hc))).
      assert (Hlc2 : lc_alt 0 u2) by (apply lc_tm_iff_lc_alt; apply (proj2 (CEq_lc Hc))).
      rewrite <- (@subst_open_comm_TM u1 x z b1 Hzx Hlc1).
      rewrite <- (@subst_open_comm_TM u2 x z b2 Hzx Hlc2).
      rewrite <- (@Crm_cons_neq_list z x psi1 C Hzx).
      assert (Hc' : CEq (Crm x ((z~psi1)++C)) psi psi0 u1 u2).
      { rewrite (@Crm_cons_neq_list z x psi1 C Hzx).
        apply CEq_weaken_head with (y:=z) (g:=psi1); assumption. }
      apply (IHbody z HzL x psi0 u1 u2 (@binds_cons_3 grade x z psi0 psi1 C Hb) Hc').
  - (* GEq_SSigma *) intros L C psi psi1 A1 B1 A2 B2 gd IHg body IHbody.
    intros x psi0 a1 a2 Hb Hc. simpl.
    apply (@GEq_SSigma ((L \u {{x}}) \u dom (Crm x C)) (Crm x C) psi psi1 (subst_tm_tm a1 x A1) (subst_tm_tm a1 x B1) (subst_tm_tm a2 x A2) (subst_tm_tm a2 x B2)).
    + apply (IHg x psi0 a1 a2 Hb Hc).
    + intros z Hz.
      destruct (@notin_triple L x z (dom (Crm x C)) Hz) as [HzL [Hzx HzD]].
      assert (Hlc1 : lc_alt 0 a1) by (apply lc_tm_iff_lc_alt; apply (proj1 (CEq_lc Hc))).
      assert (Hlc2 : lc_alt 0 a2) by (apply lc_tm_iff_lc_alt; apply (proj2 (CEq_lc Hc))).
      rewrite <- (@subst_open_comm_TM a1 x z B1 Hzx Hlc1).
      rewrite <- (@subst_open_comm_TM a2 x z B2 Hzx Hlc2).
      rewrite <- (@Crm_cons_neq_list z x psi C Hzx).
      assert (Hc' : CEq (Crm x ((z~psi)++C)) psi psi0 a1 a2).
      { rewrite (@Crm_cons_neq_list z x psi C Hzx).
        apply CEq_weaken_head with (y:=z) (g:=psi); assumption. }
      apply (IHbody z HzL x psi0 a1 a2 (@binds_cons_3 grade x z psi0 psi C Hb) Hc').
  - (* GEq_SPair *) intros C psi a1 psi1 b1 a2 b2 c IHc gd IHg.
    intros x psi0 u1 u2 Hb Hc. simpl.
    apply GEq_SPair.
    + apply (IHc x psi0 u1 u2 Hb Hc).
    + apply (IHg x psi0 u1 u2 Hb Hc).
  - (* GEq_Proj1 *) intros C psi psi1 a1 a2 gd IHg i.
    intros x psi0 u1 u2 Hb Hc. simpl.
    apply GEq_Proj1.
    + apply (IHg x psi0 u1 u2 Hb Hc).
    + exact i.
  - (* GEq_Proj2 *) intros C psi psi1 a1 a2 gd IHg.
    intros x psi0 u1 u2 Hb Hc. simpl.
    apply GEq_Proj2. apply (IHg x psi0 u1 u2 Hb Hc).
  - (* GEq_Sum *) intros C psi A1 A2 A1' A2' gd IHg gd0 IHg0.
    intros x psi0 u1 u2 Hb Hc. simpl.
    apply GEq_Sum.
    + apply (IHg x psi0 u1 u2 Hb Hc).
    + apply (IHg0 x psi0 u1 u2 Hb Hc).
  - (* GEq_Inj1 *) intros C psi a1 a1' gd IHg.
    intros x psi0 u1 u2 Hb Hc. simpl.
    apply GEq_Inj1. apply (IHg x psi0 u1 u2 Hb Hc).
  - (* GEq_Inj2 *) intros C psi a2 a2' gd IHg.
    intros x psi0 u1 u2 Hb Hc. simpl.
    apply GEq_Inj2. apply (IHg x psi0 u1 u2 Hb Hc).
  - (* GEq_Case *) intros C psi psi1 a b1 b2 a' b1' b2' gd IHg gd0 IHg0 gd1 IHg1 i.
    intros x psi0 u1 u2 Hb Hc. simpl.
    apply GEq_Case.
    + apply (IHg x psi0 u1 u2 Hb Hc).
    + apply (IHg0 x psi0 u1 u2 Hb Hc).
    + apply (IHg1 x psi0 u1 u2 Hb Hc).
    + exact i.
  - (* GEq_TyUnit *) intros C psi u. intros x psi0 a1 a2 Hb Hc. simpl.
    apply GEq_TyUnit. apply Crm_uniq. exact u.
  - (* GEq_TmUnit *) intros C psi u. intros x psi0 a1 a2 Hb Hc. simpl.
    apply GEq_TmUnit. apply Crm_uniq. exact u.
  - (* CEq_Leq *) intros C psi psi1 b1 b2 i gd IHg.
    intros x psiX a1 a2 Hb Hc. simpl.
    apply CEq_Leq.
    + exact i.
    + apply (IHg x psiX a1 a2 Hb Hc).
  - (* CEq_Nleq *) intros C psi psi1 b1 b2 l1 l2 n u.
    intros x psiX a1 a2 Hb Hc. simpl.
    apply CEq_Nleq.
    + apply subst_lc; [apply (proj1 (CEq_lc Hc))|exact l1].
    + apply subst_lc; [apply (proj2 (CEq_lc Hc))|exact l2].
    + exact n.
    + apply Crm_uniq. exact u.
Qed.

Lemma open_subst_samevar_TM : forall (s:tm) x (b:tm),
  x \notin fv_tm_tm b ->
  open_tm_wrt_tm b s = subst_tm_tm s x (open_tm_wrt_tm b (a_Var_f x)).
Proof.
  intros s x b Hfv. unfold open_tm_wrt_tm.
  apply (@open_subst_samevar 0 s x b Hfv).
Qed.

Lemma GEq_open : forall (L:vars) P psi psi0 (b1 b2 a1 a2:tm),
  (forall x, x \notin L ->
     GEq ((x~psi0)++P) psi (open_tm_wrt_tm b1 (a_Var_f x))
       (open_tm_wrt_tm b2 (a_Var_f x))) ->
  CEq P psi psi0 a1 a2 ->
  GEq P psi (open_tm_wrt_tm b1 a1) (open_tm_wrt_tm b2 a2).
Proof.
  intros L P psi psi0 b1 b2 a1 a2 Hbody Harg.
  destruct (atom_fresh (((L \u fv_tm_tm b1) \u fv_tm_tm b2) \u dom P)) as [x Hz].
  assert (Hz12 : x \notin (L \u fv_tm_tm b1) \u fv_tm_tm b2)
    by (exact (@notin_union_1 x ((L \u fv_tm_tm b1) \u fv_tm_tm b2) (dom P) Hz)).
  assert (HxP : x \notin dom P)
    by (exact (@notin_union_2 x ((L \u fv_tm_tm b1) \u fv_tm_tm b2) (dom P) Hz)).
  assert (HxLb1 : x \notin L \u fv_tm_tm b1)
    by (exact (@notin_union_1 x (L \u fv_tm_tm b1) (fv_tm_tm b2) Hz12)).
  assert (Hxb2 : x \notin fv_tm_tm b2)
    by (exact (@notin_union_2 x (L \u fv_tm_tm b1) (fv_tm_tm b2) Hz12)).
  assert (HxL : x \notin L)
    by (exact (@notin_union_1 x L (fv_tm_tm b1) HxLb1)).
  assert (Hxb1 : x \notin fv_tm_tm b1)
    by (exact (@notin_union_2 x L (fv_tm_tm b1) HxLb1)).
  assert (Hb : binds x psi0 ((x~psi0)++P)).
  { apply binds_cons_2; reflexivity. }
  assert (Harg' : CEq (Crm x ((x~psi0)++P)) psi psi0 a1 a2).
  { rewrite (@Crm_cons_eq_list x psi0 P).
    rewrite (@Crm_notin_eq x P HxP). exact Harg. }
  assert (Hres : GEq (Crm x ((x~psi0)++P)) psi
      (subst_tm_tm a1 x (open_tm_wrt_tm b1 (a_Var_f x)))
      (subst_tm_tm a2 x (open_tm_wrt_tm b2 (a_Var_f x)))).
  { exact (proj1 GEq_CEq_subst ((x~psi0)++P) psi
             (open_tm_wrt_tm b1 (a_Var_f x)) (open_tm_wrt_tm b2 (a_Var_f x))
             (Hbody x HxL) x psi0 a1 a2 Hb Harg'). }
  rewrite (@Crm_cons_eq_list x psi0 P) in Hres.
  rewrite (@Crm_notin_eq x P HxP) in Hres.
  rewrite <- (@open_subst_samevar_TM a1 x b1 Hxb1) in Hres.
  rewrite <- (@open_subst_samevar_TM a2 x b2 Hxb2) in Hres.
  exact Hres.
Qed.

(* Inversion principles for the reduction relation at the active heads *)
Lemma Step_App_inv : forall (f:tm) psi (a t:tm), Step (a_App f psi a) t ->
  (exists f', lc_tm a /\ Step f f' /\ t = a_App f' psi a) \/
  (exists A a0, f = a_Abs psi A a0 /\ lc_tm A /\
      lc_tm (a_Abs psi A a0) /\ lc_tm a /\ t = open_tm_wrt_tm a0 a).
Proof. intros. inversion H; subst; eauto 10. Qed.

Lemma Step_Case_inv : forall psi (a b1 b2 t:tm), Step (a_Case psi a b1 b2) t ->
  (exists a', lc_tm b1 /\ lc_tm b2 /\ Step a a' /\ t = a_Case psi a' b1 b2) \/
  (exists x, a = a_Inj1 x /\ lc_tm b2 /\ lc_tm b1 /\ lc_tm x /\
      t = a_App b1 psi x) \/
  (exists x, a = a_Inj2 x /\ lc_tm b1 /\ lc_tm b2 /\ lc_tm x /\
      t = a_App b2 psi x).
Proof. intros. inversion H; subst; eauto 10. Qed.

Lemma Step_LetPair_inv : forall psi (a b t:tm), Step (a_LetPair psi a b) t ->
  (exists a', lc_tm (a_LetPair psi a b) /\ Step a a' /\ t = a_LetPair psi a' b) \/
  (exists a1 a2, a = a_WPair a1 psi a2 /\
      lc_tm (a_LetPair psi (a_WPair a1 psi a2) b) /\ lc_tm a1 /\ lc_tm a2 /\
      t = a_App (open_tm_wrt_tm b a1) q_Bot a2).
Proof. intros. inversion H; subst; eauto 10. Qed.

Lemma Step_Proj1_inv : forall psi (a t:tm), Step (a_Proj1 psi a) t ->
  (exists a', Step a a' /\ t = a_Proj1 psi a') \/
  (exists a1 a2, a = a_SPair a1 psi a2 /\ lc_tm a2 /\ lc_tm a1 /\ t = a1).
Proof. intros. inversion H; subst; eauto 10. Qed.

Lemma Step_Proj2_inv : forall psi (a t:tm), Step (a_Proj2 psi a) t ->
  (exists a', Step a a' /\ t = a_Proj2 psi a') \/
  (exists a1 a2, a = a_SPair a1 psi a2 /\ lc_tm a1 /\ lc_tm a2 /\ t = a2).
Proof. intros. inversion H; subst; eauto 10. Qed.

Lemma GEq_Abs_inv : forall P phi psi0 A1 b1 A2 b2,
  GEq P phi (a_Abs psi0 A1 b1) (a_Abs psi0 A2 b2) ->
  exists L, (forall x, x \notin L ->
               GEq ((x~psi0)++P) phi (open_tm_wrt_tm b1 (a_Var_f x))
                 (open_tm_wrt_tm b2 (a_Var_f x))) /\
            CEq P phi q_Top A1 A2.
Proof. intros. inversion H; subst; eauto. Qed.

Lemma GEq_WPair_inv : forall P phi a1 psi0 b1 y,
  GEq P phi (a_WPair a1 psi0 b1) y ->
  exists a2 b2, y = a_WPair a2 psi0 b2 /\ CEq P phi psi0 a1 a2 /\ GEq P phi b1 b2.
Proof. intros. inversion H; subst; eauto. Qed.

Lemma GEq_SPair_inv : forall P phi a1 psi0 b1 y,
  GEq P phi (a_SPair a1 psi0 b1) y ->
  exists a2 b2, y = a_SPair a2 psi0 b2 /\ CEq P phi psi0 a1 a2 /\ GEq P phi b1 b2.
Proof. intros. inversion H; subst; eauto. Qed.

Lemma GEq_Inj1_inv : forall P phi x y,
  GEq P phi (a_Inj1 x) (a_Inj1 y) -> GEq P phi x y.
Proof. intros. inversion H; subst; assumption. Qed.

Lemma GEq_Inj2_inv : forall P phi x y,
  GEq P phi (a_Inj2 x) (a_Inj2 y) -> GEq P phi x y.
Proof. intros. inversion H; subst; assumption. Qed.

Lemma GEq_Abs_inv_y : forall P phi psi0 A1 b1 y,
  GEq P phi (a_Abs psi0 A1 b1) y ->
  exists A2 b2 L, y = a_Abs psi0 A2 b2 /\
    (forall x, x \notin L ->
       GEq ((x~psi0)++P) phi (open_tm_wrt_tm b1 (a_Var_f x))
         (open_tm_wrt_tm b2 (a_Var_f x))) /\
    CEq P phi q_Top A1 A2.
Proof.
  intros. inversion H; subst.
  eexists; eexists; eexists; split; [reflexivity|split; eassumption].
Qed.

Lemma GEq_Inj1_inv_y : forall P phi x y,
  GEq P phi (a_Inj1 x) y -> exists y', y = a_Inj1 y' /\ GEq P phi x y'.
Proof. intros. inversion H; subst; eauto. Qed.

Lemma GEq_Inj2_inv_y : forall P phi x y,
  GEq P phi (a_Inj2 x) y -> exists y', y = a_Inj2 y' /\ GEq P phi x y'.
Proof. intros. inversion H; subst; eauto. Qed.

Lemma lc_abs_of_body : forall (L:vars) psi (A b:tm),
  lc_tm A -> (forall x, x \notin L -> lc_tm (open_tm_wrt_tm b (a_Var_f x))) ->
  lc_tm (a_Abs psi A b).
Proof.
  intros L psi A b HA Hbody.
  apply lc_tm_iff_lc_alt. apply Lc_Abs.
  - apply lc_tm_iff_lc_alt. exact HA.
  - apply lc_alt_body_of_open with (L:=L). exact Hbody.
Qed.

Lemma lc_letpair_of_body : forall (L:vars) psi (a b:tm),
  lc_tm a -> (forall x, x \notin L -> lc_tm (open_tm_wrt_tm b (a_Var_f x))) ->
  lc_tm (a_LetPair psi a b).
Proof.
  intros L psi a b HA Hbody.
  apply lc_tm_iff_lc_alt. apply Lc_LetPair.
  - apply lc_tm_iff_lc_alt. exact HA.
  - apply lc_alt_body_of_open with (L:=L). exact Hbody.
Qed.

Theorem CEq_GEq_respects_Step :
  (forall P phi phi0 b1 b1',
  CEq P phi phi0 b1 b1' ->  forall b2, Step b1 b2 ->
       exists b2', (phi0 <= phi -> Step b1' b2') /\ CEq P phi phi0 b2 b2') /\
  (forall P phi b1 b1',
  GEq P phi b1 b1' -> forall b2, Step b1 b2 ->
       exists b2', Step b1' b2' /\ GEq P phi b2 b2').
Proof.
  assert (Hmain :
    (forall P phi b1 b1', GEq P phi b1 b1' -> forall b2, Step b1 b2 ->
       exists b2', Step b1' b2' /\ GEq P phi b2 b2') /\
    (forall P phi phi0 b1 b1', CEq P phi phi0 b1 b1' -> forall b2, Step b1 b2 ->
       exists b2', (phi0 <= phi -> Step b1' b2') /\ CEq P phi phi0 b2 b2')).
  { apply GEqCEq_ind with
    (P := fun P phi b1 b1' (_:GEq P phi b1 b1') =>
       forall b2, Step b1 b2 ->
         exists b2', Step b1' b2' /\ GEq P phi b2 b2')
    (P0 := fun P phi phi0 b1 b1' (_:CEq P phi phi0 b1 b1') =>
       forall b2, Step b1 b2 ->
         exists b2', (phi0 <= phi -> Step b1' b2') /\ CEq P phi phi0 b2 b2').
  - (* Var *) intros. match goal with H : Step _ _ |- _ => inversion H end.
  - (* Type *) intros. match goal with H : Step _ _ |- _ => inversion H end.
  - (* Pi *) intros. match goal with H : Step _ _ |- _ => inversion H end.
  - (* Abs *) intros. match goal with H : Step _ _ |- _ => inversion H end.
  - (* App *) intros P phi f psi0 arg f' arg' g IHg c IHc t Hs.
    destruct (@Step_App_inv f psi0 arg t Hs) as
      [[f0 [lcarg [Hsf Heq]]]|[A [a0 [Heqf [lcA [lcAbs [lcarg Heq]]]]]]].
    + subst t. destruct (IHg f0 Hsf) as [f0' [Hsf' HGf]].
      exists (a_App f0' psi0 arg'). split.
      * apply S_AppCong; [exact (proj2 (CEq_lc c))|exact Hsf'].
      * apply GEq_App; [exact HGf|exact c].
    + subst f. subst t.
      destruct (@GEq_Abs_inv_y P phi psi0 A a0 f' g) as
        [A2 [b2 [L [Hy [Hbody Hdom]]]]]. subst f'.
      exists (open_tm_wrt_tm b2 arg'). split.
      * apply S_Beta with (A:=A2).
        -- exact (proj2 (CEq_lc Hdom)).
        -- apply lc_abs_of_body with (L:=L) (b:=b2).
           ++ exact (proj2 (CEq_lc Hdom)).
           ++ intros x Hx. exact (proj2 (GEq_lc (Hbody x Hx))).
        -- exact (proj2 (CEq_lc c)).
      * apply (@GEq_open L P phi psi0 a0 b2 arg arg' Hbody c).
  - (* WSigma *) intros. match goal with H : Step _ _ |- _ => inversion H end.
  - (* WPair *) intros. match goal with H : Step _ _ |- _ => inversion H end.
  - (* LetPair *) intros L P phi psi0 s b s' b' gscrut IHg Hbody IHbody t Hs.
    destruct (@Step_LetPair_inv psi0 s b t Hs) as
      [[s0 [lcLet [Hss Heq]]]|[a1 [a2 [Heq [lcLet [lc1 [lc2 Heq']]]]]]].
    + subst t. destruct (IHg s0 Hss) as [s0' [Hss' HGs]].
      exists (a_LetPair psi0 s0' b'). split.
      * apply S_LetPairCong.
        -- apply lc_letpair_of_body with (L:=L) (a:=s') (b:=b').
           ++ exact (proj2 (GEq_lc gscrut)).
           ++ intros x Hx. exact (proj2 (GEq_lc (Hbody x Hx))).
        -- exact Hss'.
      * apply (@GEq_LetPair L P phi psi0 s0 b s0' b'); [exact HGs|exact Hbody].
    + subst s. subst t.
      destruct (@GEq_WPair_inv P phi a1 psi0 a2 s' gscrut) as
        [a1' [a2' [Hy [Hc Hg]]]]. subst s'.
      exists (a_App (open_tm_wrt_tm b' a1') q_Bot a2'). split.
      * apply S_LetPairBeta.
        -- apply lc_letpair_of_body with (L:=L) (a:=a_WPair a1' psi0 a2') (b:=b').
           ++ exact (proj2 (GEq_lc gscrut)).
           ++ intros x Hx. exact (proj2 (GEq_lc (Hbody x Hx))).
        -- exact (proj2 (CEq_lc Hc)).
        -- exact (proj2 (GEq_lc Hg)).
      * apply GEq_App.
        -- apply (@GEq_open L P phi psi0 b b' a1 a1' Hbody Hc).
        -- apply CEq_Leq; [apply leq_Bot_l|exact Hg].
  - (* SSigma *) intros. match goal with H : Step _ _ |- _ => inversion H end.
  - (* SPair *) intros. match goal with H : Step _ _ |- _ => inversion H end.
  - (* Proj1 *) intros P phi psi0 s s' g IHg i t Hs.
    destruct (@Step_Proj1_inv psi0 s t Hs) as
      [[s0 [Hss Heq]]|[a1 [a2 [Heq [lc2 [lc1 Heq']]]]]].
    + subst t. destruct (IHg s0 Hss) as [s0' [Hss' HGs]].
      exists (a_Proj1 psi0 s0'). split.
      * apply S_Proj1Cong. exact Hss'.
      * apply GEq_Proj1; [exact HGs|exact i].
    + subst s. subst t.
      destruct (@GEq_SPair_inv P phi a1 psi0 a2 s' g) as
        [a1' [a2' [Hy [Hc Hg]]]]. subst s'.
      exists a1'. split.
      * apply S_Proj1Beta; [exact (proj2 (GEq_lc Hg))|exact (proj2 (CEq_lc Hc))].
      * apply CEq_leq_GEq with (psi0:=psi0); [exact i|exact Hc].
  - (* Proj2 *) intros P phi psi0 s s' g IHg t Hs.
    destruct (@Step_Proj2_inv psi0 s t Hs) as
      [[s0 [Hss Heq]]|[a1 [a2 [Heq [lc1 [lc2 Heq']]]]]].
    + subst t. destruct (IHg s0 Hss) as [s0' [Hss' HGs]].
      exists (a_Proj2 psi0 s0'). split.
      * apply S_Proj2Cong. exact Hss'.
      * apply GEq_Proj2. exact HGs.
    + subst s. subst t.
      destruct (@GEq_SPair_inv P phi a1 psi0 a2 s' g) as
        [a1' [a2' [Hy [Hc Hg]]]]. subst s'.
      exists a2'. split.
      * apply S_Proj2Beta; [exact (proj2 (CEq_lc Hc))|exact (proj2 (GEq_lc Hg))].
      * exact Hg.
  - (* Sum *) intros. match goal with H : Step _ _ |- _ => inversion H end.
  - (* Inj1 *) intros. match goal with H : Step _ _ |- _ => inversion H end.
  - (* Inj2 *) intros. match goal with H : Step _ _ |- _ => inversion H end.
  - (* Case *) intros P phi psi0 s b1 b2 s' b1' b2' gscrut IHg gb1 IHg0 gb2 IHg1 i t Hs.
    destruct (@Step_Case_inv psi0 s b1 b2 t Hs) as
      [[s0 [lcb1 [lcb2 [Hss Heq]]]]
      |[[x [Heq [lcb2 [lcb1 [lcx Heq']]]]]
        |[x [Heq [lcb1 [lcb2 [lcx Heq']]]]]]].
    + subst t. destruct (IHg s0 Hss) as [s0' [Hss' HGs]].
      exists (a_Case psi0 s0' b1' b2'). split.
      * apply S_CaseCong; [exact (proj2 (GEq_lc gb1))|exact (proj2 (GEq_lc gb2))|exact Hss'].
      * apply GEq_Case; [exact HGs|exact gb1|exact gb2|exact i].
    + subst s. subst t.
      destruct (@GEq_Inj1_inv_y P phi x s' gscrut) as [x' [Hy Hgx]]. subst s'.
      exists (a_App b1' psi0 x'). split.
      * apply S_Case1Beta; [exact (proj2 (GEq_lc gb2))|exact (proj2 (GEq_lc gb1))|exact (proj2 (GEq_lc Hgx))].
      * apply GEq_App; [exact gb1|apply CEq_Leq; [exact i|exact Hgx]].
    + subst s. subst t.
      destruct (@GEq_Inj2_inv_y P phi x s' gscrut) as [x' [Hy Hgx]]. subst s'.
      exists (a_App b2' psi0 x'). split.
      * apply S_Case2Beta; [exact (proj2 (GEq_lc gb1))|exact (proj2 (GEq_lc gb2))|exact (proj2 (GEq_lc Hgx))].
      * apply GEq_App; [exact gb2|apply CEq_Leq; [exact i|exact Hgx]].
  - (* TyUnit *) intros. match goal with H : Step _ _ |- _ => inversion H end.
  - (* TmUnit *) intros. match goal with H : Step _ _ |- _ => inversion H end.
  - (* CEq_Leq *) intros P phi phi0 a1 a2 i g IHg t Hs.
    destruct (IHg t Hs) as [t' [Hst HG]]. exists t'. split.
    + intros Hle. exact Hst.
    + apply CEq_Leq; [exact i|exact HG].
  - (* CEq_Nleq *) intros P phi phi0 a1 a2 l1 l2 n u t Hs.
    exists t. split.
    + intros Hle. exfalso. apply n. exact Hle.
    + apply CEq_Nleq.
      * exact (@Step_lc a1 t Hs l1).
      * exact (@Step_lc a1 t Hs l1).
      * exact n.
      * exact u.
  }
  destruct Hmain as [HG HC]. split; [exact HC|exact HG].
Qed.

Lemma CGrade_nleq_inv : forall P phi psi a,
  ~ (psi <= phi) -> CGrade P phi psi a -> lc_tm a /\ uniq P.
Proof.
  intros P phi psi a Hn c.
  destruct c as [P0 phi0 ps0 a0 i0 g0|P0 phi0 ps0 a0 l0 n0 u0].
  - exfalso. apply Hn. exact i0.
  - split; [exact l0|exact u0].
Qed.

Lemma erasure_open_var : forall (phi:grade) x (b:tm),
  erasure phi (open_tm_wrt_tm b (a_Var_f x)) =
  open_tm_wrt_tm (erasure phi b) (a_Var_f x).
Proof.
  intros. unfold open_tm_wrt_tm.
  rewrite (@erasure_open phi 0 (a_Var_f x) b). simpl. reflexivity.
Qed.

Theorem Erasure_Indistinguishability :
  (forall P phi psi a, CGrade P phi psi a -> CEq P phi psi a (erasure phi a)) /\
  (forall P phi a, Grade P phi a -> GEq P phi a (erasure phi a)).
Proof.
  apply CGradeGrade_ind with
    (P := fun P phi psi a (_:CGrade P phi psi a) => CEq P phi psi a (erasure phi a))
    (P0 := fun P phi a (_:Grade P phi a) => GEq P phi a (erasure phi a)).
  - (* CG_Leq *) intros P phi phi0 a i g IHg.
    apply CEq_Leq; [exact i|exact IHg].
  - (* CG_Nleq *) intros P phi phi0 a l n u.
    apply CEq_Nleq.
    + exact l.
    + apply erasure_lc. exact l.
    + exact n.
    + exact u.
  - (* G_Type *) intros P psi s u. simpl. apply GEq_Type. exact u.
  - (* G_Var *) intros P psi x psi0 u b i. simpl. apply GEq_Var with (psi0:=psi0); assumption.
  - (* G_Pi *) intros L P psi psi0 A B g IHg body IHbody. simpl.
    apply (@GEq_Pi L P psi psi0 A B (erasure psi A) (erasure psi B)).
    + exact IHg.
    + intros x Hx. specialize (IHbody x Hx).
      rewrite (erasure_open_var psi x B) in IHbody. exact IHbody.
  - (* G_Abs *) intros L P psi psi0 A b gbody IHbody c IHc. simpl.
    destruct (q_leb q_Top psi) eqn:E.
    + apply (@GEq_Abs L P psi psi0 A b (erasure psi A) (erasure psi b)).
      * intros x Hx. specialize (IHbody x Hx).
        rewrite (erasure_open_var psi x b) in IHbody. exact IHbody.
      * exact IHc.
    + assert (Hn : ~ (q_Top <= psi)) by (apply leb_false_nle; exact E).
      destruct (CGrade_nleq_inv Hn c) as [Hlc Hu].
      apply (@GEq_Abs L P psi psi0 A b a_TmUnit (erasure psi b)).
      * intros x Hx. specialize (IHbody x Hx).
        rewrite (erasure_open_var psi x b) in IHbody. exact IHbody.
      * apply CEq_Nleq.
        -- exact Hlc.
        -- apply lc_a_TmUnit.
        -- exact Hn.
        -- exact Hu.
  - (* G_App *) intros P psi b psi0 a gb IHb c IHc. simpl.
    destruct (q_leb psi0 psi) eqn:E.
    + apply GEq_App; [exact IHb|exact IHc].
    + assert (Hn : ~ (psi0 <= psi)) by (apply leb_false_nle; exact E).
      destruct (CGrade_nleq_inv Hn c) as [Hlc Hu].
      apply GEq_App.
      * exact IHb.
      * apply CEq_Nleq.
        -- exact Hlc.
        -- apply lc_a_TmUnit.
        -- exact Hn.
        -- exact Hu.
  - (* G_WSigma *) intros L P psi psi0 A B g IHg body IHbody. simpl.
    apply (@GEq_WSigma L P psi psi0 A B (erasure psi A) (erasure psi B)).
    + exact IHg.
    + intros x Hx. specialize (IHbody x Hx).
      rewrite (erasure_open_var psi x B) in IHbody. exact IHbody.
  - (* G_WPair *) intros P psi a psi0 b c IHc gb IHb. simpl.
    destruct (q_leb psi0 psi) eqn:E.
    + apply GEq_WPair; [exact IHc|exact IHb].
    + assert (Hn : ~ (psi0 <= psi)) by (apply leb_false_nle; exact E).
      destruct (CGrade_nleq_inv Hn c) as [Hlc Hu].
      apply GEq_WPair.
      * apply CEq_Nleq.
        -- exact Hlc.
        -- apply lc_a_TmUnit.
        -- exact Hn.
        -- exact Hu.
      * exact IHb.
  - (* G_LetPair *) intros L P psi psi0 a c g IHg body IHbody. simpl.
    apply (@GEq_LetPair L P psi psi0 a c (erasure psi a) (erasure psi c)).
    + exact IHg.
    + intros x Hx. specialize (IHbody x Hx).
      rewrite (erasure_open_var psi x c) in IHbody. exact IHbody.
  - (* G_SSigma *) intros L P psi psi0 A B g IHg body IHbody. simpl.
    apply (@GEq_SSigma L P psi psi0 A B (erasure psi A) (erasure psi B)).
    + exact IHg.
    + intros x Hx. specialize (IHbody x Hx).
      rewrite (erasure_open_var psi x B) in IHbody. exact IHbody.
  - (* G_SPair *) intros P psi a psi0 b c IHc gb IHb. simpl.
    destruct (q_leb psi0 psi) eqn:E.
    + apply GEq_SPair; [exact IHc|exact IHb].
    + assert (Hn : ~ (psi0 <= psi)) by (apply leb_false_nle; exact E).
      destruct (CGrade_nleq_inv Hn c) as [Hlc Hu].
      apply GEq_SPair.
      * apply CEq_Nleq.
        -- exact Hlc.
        -- apply lc_a_TmUnit.
        -- exact Hn.
        -- exact Hu.
      * exact IHb.
  - (* G_Proj1 *) intros P psi psi0 a g IHg i. simpl.
    apply GEq_Proj1; [exact IHg|exact i].
  - (* G_Proj2 *) intros P psi psi0 a g IHg. simpl.
    apply GEq_Proj2. exact IHg.
  - (* G_Sum *) intros P psi A B gA IHA gB IHB. simpl.
    apply GEq_Sum; assumption.
  - (* G_Inj1 *) intros P psi a1 g IHg. simpl.
    apply GEq_Inj1. exact IHg.
  - (* G_Inj2 *) intros P psi a2 g IHg. simpl.
    apply GEq_Inj2. exact IHg.
  - (* G_Case *) intros P psi psi0 a b1 b2 ga IHA gb1 IHB1 gb2 IHB2 i. simpl.
    apply GEq_Case; [exact IHA|exact IHB1|exact IHB2|exact i].
  - (* G_TyUnit *) intros P psi u. simpl. apply GEq_TyUnit. exact u.
  - (* G_TmUnit *) intros P psi u. simpl. apply GEq_TmUnit. exact u.
Qed.
