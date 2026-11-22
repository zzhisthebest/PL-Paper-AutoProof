From strictness.cbpv Require Import strict_semtyping.
From Stdlib Require Import Eqdep_dec Arith.Peano_dec Lia FunctionalExtensionality.
Require Import Coq.Program.Equality.

(* ===== generic environment algebra ===== *)

Lemma eq_rect_r_app : forall {A} {n k} (e : n = k) (f : fin n -> A) (a : fin k),
  eq_rect_r (fun n0 => fin n0 -> A) f (eq_sym e) a = f (eq_rec_r (fun n0 => fin n0) a e).
Proof. intros. destruct e. reflexivity. Qed.

Lemma down_env_until_up : forall {A n} (γ : fin n -> A) m (H : m <= n) (i : fin m),
  down_env_until γ m H i = γ (up_fin_until n H i).
Proof. intros. unfold down_env_until, up_fin_until, down_env_until', ren_env. cbn. apply eq_rect_r_app. Qed.

Lemma eq_rec_r_fin_Some : forall {n k} (e : n = k) (y : fin k),
  @eq_rec_r nat (S k) (fun j => fin j) (Some y) (S n) (f_equal S e)
   = Some (@eq_rec_r nat k (fun j => fin j) y n e).
Proof. intros. destruct e. reflexivity. Qed.

Lemma eq_rec_r_self : forall {n} (Q : nat -> Set) (a : Q n) (e : n = n), eq_rec_r Q a e = a.
Proof. intros. dependent destruction e. reflexivity. Qed.

Lemma up_fin_until_self : forall n (H : n <= n) x, @up_fin_until n n H x = x.
Proof.
  intros n. induction n as [|n IH]; intros H x.
  - destruct x.
  - destruct x as [x|].
    all: unfold up_fin_until.
    all: assert (Hs : S n - S n = 0) by apply Nat.sub_diag.
    all: generalize (le_minus_plus (S n) (S n) H).
    all: rewrite Hs. all: cbn. all: intros e.
    all: rewrite (eq_rec_r_self (fun n0 => fin n0) _ e).
    all: reflexivity.
Qed.

Lemma down_env_until_self : forall {A n} (γ : fin n -> A) (H : n <= n) x, down_env_until γ n H x = γ x.
Proof. intros. rewrite down_env_until_up. rewrite up_fin_until_self. reflexivity. Qed.

Lemma down_env_self_fun : forall {A n} (γ : fin n -> A) (H : n <= n), down_env_until γ n H = γ.
Proof. intros. apply functional_extensionality. intro i. apply down_env_until_self. Qed.

Lemma up_fin_until_succ : forall {n} m (H : m <= n) (H' : m <= S n) (i : fin m),
  @up_fin_until m (S n) H' i = Some (@up_fin_until m n H i).
Proof.
  intros n m H H' i. unfold up_fin_until.
  generalize (le_minus_plus m (S n) H') as e1.
  generalize (le_minus_plus m n H) as e2.
  rewrite (Nat.sub_succ_l m n H). cbn. intros e2 e1.
  assert (E : e1 = f_equal S e2) by apply (UIP_dec Nat.eq_dec).
  rewrite E. rewrite eq_rec_r_fin_Some. reflexivity.
Qed.

Lemma down_env_cons : forall {A n} q (γ : fin n -> A) m (H : m <= n) (H' : m <= S n) i,
  down_env_until (q .: γ) m H' i = down_env_until γ m H i.
Proof. intros. rewrite !down_env_until_up.
  assert (E : @up_fin_until m (S n) H' i = Some (@up_fin_until m n H i)) by (apply up_fin_until_succ).
  rewrite E. reflexivity. Qed.

Lemma down_env_cons_fun : forall {A n} q (γ : fin n -> A) m (H : m <= n) (H' : m <= S n),
  down_env_until (q .: γ) m H' = down_env_until γ m H.
Proof. intros. apply functional_extensionality. intro i. apply down_env_cons. Qed.

Lemma down_env_add : forall {n} (γ1 γ2 : attrs n) m (H : m <= n) i,
  down_env_until (γ1 γ+ γ2) m H i = (down_env_until γ1 m H i) C+ (down_env_until γ2 m H i).
Proof. intros. rewrite !down_env_until_up. reflexivity. Qed.

Lemma attr_add_strict_l : forall a b, a C+ b = Strict -> a = Strict \/ b = Strict.
Proof. intros a b. destruct a, b; cbn; try discriminate; auto. Qed.

Lemma attr_le_strict : forall a b, a C<= b -> a = Strict -> b = Strict.
Proof. intros a b H. destruct a,b; cbn in *; try discriminate; auto; try contradiction. Qed.

Fixpoint f2n (n : nat) : fin n -> nat :=
  match n as n0 return (fin n0 -> nat) with
  | 0 => fun x => match x with end
  | S m => fun x => match x with None => 0 | Some y => S (f2n m y) end
  end.

Lemma f2n_shift : forall p {n} (i : fin n), f2n (p+n) (shift_p p i) = p + f2n n i.
Proof. intros p. induction p as [|p IH]; intros n i. - cbn. reflexivity. - cbn. rewrite IH. reflexivity. Qed.

Lemma f2n_transport : forall {n k} (e : n = k) (x : fin k),
  f2n n (@eq_rec_r nat k (fun j => fin j) x n e) = f2n k x.
Proof. intros. destruct e. reflexivity. Qed.

Lemma f2n_inj : forall {n} (x y : fin n), f2n n x = f2n n y -> x = y.
Proof.
  intros n. induction n as [|n IH]; intros x y H.
  - destruct x.
  - destruct x as [x|], y as [y|]; cbn in *.
    + f_equal. apply IH. injection H. auto.
    + discriminate. + discriminate. + reflexivity.
Qed.

Lemma up_fin_until_comp : forall {a} b c (H1 : a <= b) (H2 : b <= c) (i : fin a),
  @up_fin_until b c H2 (@up_fin_until a b H1 i) = @up_fin_until a c (Nat.le_trans a b c H1 H2) i.
Proof.
  intros a b c H1 H2 i. apply f2n_inj. unfold up_fin_until.
  rewrite f2n_transport. rewrite f2n_shift.
  rewrite f2n_transport. rewrite f2n_shift.
  rewrite f2n_transport. rewrite f2n_shift.
  assert (Hsub : (c - b) + (b - a) = c - a) by lia.
  rewrite Nat.add_assoc. rewrite Hsub. reflexivity.
Qed.

Lemma down_env_comp : forall {A n} (γ : fin n -> A) m1 m2 (H2 : m2 <= n) (H1 : m1 <= m2) i,
  down_env_until (down_env_until γ m2 H2) m1 H1 i = down_env_until γ m1 (Nat.le_trans m1 m2 n H1 H2) i.
Proof. intros. rewrite !down_env_until_up. rewrite up_fin_until_comp. reflexivity. Qed.

Lemma down_env_comp_fun : forall {A n} (γ : fin n -> A) m1 m2 (H2 : m2 <= n) (H1 : m1 <= m2),
  down_env_until (down_env_until γ m2 H2) m1 H1 = down_env_until γ m1 (Nat.le_trans m1 m2 n H1 H2).
Proof. intros. apply functional_extensionality. intro i. apply down_env_comp. Qed.

Lemma up_fin_until_irrel : forall {m} n (H1 H2 : m <= n) x,
  @up_fin_until m n H1 x = @up_fin_until m n H2 x.
Proof.
  intros m n H1 H2 x. unfold up_fin_until.
  generalize (le_minus_plus m n H1) as e1.
  generalize (le_minus_plus m n H2) as e2.
  intros e2 e1.
  assert (E : e1 = e2) by apply (UIP_dec Nat.eq_dec).
  rewrite E. reflexivity.
Qed.

Lemma down_env_until_irrel : forall {A n} (γ : fin n -> A) m (H1 H2 : m <= n),
  down_env_until γ m H1 = down_env_until γ m H2.
Proof. intros. apply functional_extensionality. intro i.
  rewrite !down_env_until_up. apply (f_equal γ). apply up_fin_until_irrel. Qed.

(* ===== closure reindexing ===== *)


(* ===== arithmetic helpers ===== *)
Lemma min_self_l : forall a b, Nat.min (Nat.min a b) b = Nat.min a b.
Proof. intros. rewrite <- Nat.min_assoc. rewrite Nat.min_id. reflexivity. Qed.
Lemma min_le_l : forall a b c, b <= c -> Nat.min (Nat.min a b) c = Nat.min a b.
Proof. intros. rewrite <- Nat.min_assoc. rewrite (Nat.min_l b c H). reflexivity. Qed.
Lemma min_le_a : forall a b, Nat.min a b <= a.
Proof. intros a. induction a as [|a IH]; intros b. - cbn; lia. - destruct b. + cbn; lia. + cbn. apply le_n_S. apply IH. Qed.
Lemma min_le_b : forall a b, Nat.min a b <= b.
Proof. intros a. induction a as [|a IH]; intros b. - cbn; lia. - destruct b. + cbn; lia. + cbn. apply le_n_S. apply IH. Qed.
Lemma le_min : forall n m p, p <= n -> p <= m -> p <= Nat.min n m.
Proof.
  intros n. induction n as [|n IH]; intros m p H1 H2.
  - cbn. lia.
  - destruct m as [|m]. + cbn. lia. + destruct p as [|p]. * cbn; lia. * cbn. apply le_n_S.
    apply IH. -- apply le_S_n; exact H1. -- apply le_S_n; exact H2.
Qed.
Lemma le_succ_r : forall n, n <= S n.
Proof. intro n. apply le_S. apply le_n. Qed.
Lemma min_mono : forall c a b, a <= b -> Nat.min c a <= Nat.min c b.
Proof. intros c a b H. destruct c, a, b; cbn in *; lia. Qed.
Lemma min_comp2 : forall a b c, a <= b -> Nat.min (Nat.min c b) a = Nat.min c a.
Proof. intros. rewrite <- Nat.min_assoc. rewrite (Nat.min_r b a H). reflexivity. Qed.
Lemma min_min_swap : forall a b c, Nat.min (Nat.min a b) c = Nat.min a (Nat.min b c).
Proof. intros. rewrite Nat.min_assoc. reflexivity. Qed.

Lemma Thunk_eq : forall m1 m2 mI (g1 : attrs m1) (g2 : attrs m2) (ρ : env mI) (M : Comp mI) (E : m1 = m2),
  eq_rect m1 (fun k => attrs k) g1 m2 E = g2 -> Thunk m1 mI g1 ρ M = Thunk m2 mI g2 ρ M.
Proof. intros. destruct E. cbn in H. subst g2. reflexivity. Qed.

Lemma Closure_eq : forall m1 m2 mI (g1 : attrs m1) (g2 : attrs m2) (ρ : env mI) (M : Comp (S mI)) (E : m1 = m2),
  eq_rect m1 (fun k => attrs k) g1 m2 E = g2 -> Closure m1 mI g1 ρ M = Closure m2 mI g2 ρ M.
Proof. intros. destruct E. cbn in H. subst g2. reflexivity. Qed.

Lemma down_transport_self_inv : forall {A} n1 n2 (E : n1 = n2) (f : fin n2 -> A) (H : n1 <= n2),
  eq_rect n1 (fun k => fin k -> A) (down_env_until f n1 H) n2 E = f.
Proof. intros. destruct E. cbn. apply down_env_self_fun. Qed.

Lemma down_env_transport_forward_attr : forall nA n1 n2 (E : n1 = n2) (γ : attrs nA)
  (H1 : n1 <= nA) (H2 : n2 <= nA),
  @eq_rect nat n1 (fun k => attrs k) (@down_env_until attr nA γ n1 H1) n2 E = @down_env_until attr nA γ n2 H2.
Proof. intros. destruct E. cbn. apply down_env_until_irrel. Qed.

Lemma down_clos_idem : forall {k} s (C : Clos k), down_clos s (down_clos s C) = down_clos s C.
Proof.
  intros k s C.
  induction C as [| |mO mI g r IHE M|W1 IH1 W2 IH2|W IH|W IH|W IH|mO mI g r IHE M]; cbn.
  - reflexivity. - reflexivity.
  - apply Thunk_eq with (E := min_self_l mO s). cbn. apply down_transport_self_inv.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH. reflexivity. - rewrite IH. reflexivity. - rewrite IH. reflexivity.
  - apply Closure_eq with (E := min_self_l mO s). cbn. apply down_transport_self_inv.
Qed.

Lemma down_clos_le : forall {k} a b (C : Clos k), b <= a ->
  down_clos a (down_clos b C) = down_clos b C.
Proof.
  intros k a b C H.
  induction C as [| |mO mI g r IHE M|W1 IH1 W2 IH2|W IH|W IH|W IH|mO mI g r IHE M]; cbn.
  - reflexivity. - reflexivity.
  - apply Thunk_eq with (E := min_le_l mO b a H). cbn. apply down_transport_self_inv.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH. reflexivity. - rewrite IH. reflexivity. - rewrite IH. reflexivity.
  - apply Closure_eq with (E := min_le_l mO b a H). cbn. apply down_transport_self_inv.
Qed.

Lemma down_clos_comp2 : forall {k} a b (C : Clos k), a <= b ->
  down_clos a (down_clos b C) = down_clos a C.
Proof.
  intros k a b C H.
  induction C as [| |mO mI g r IHE M|W1 IH1 W2 IH2|W IH|W IH|W IH|mO mI g r IHE M]; cbn.
  - reflexivity. - reflexivity.
  - apply Thunk_eq with (E := min_comp2 a b mO H).
    rewrite (@down_env_transport_forward_attr (Nat.min mO b) (Nat.min (Nat.min mO b) a) (Nat.min mO a)
               (min_comp2 a b mO H) (down_env_until g (Nat.min mO b) (min_le mO b))
               (min_le (Nat.min mO b) a) (min_mono mO a b H)).
    rewrite (@down_env_comp_fun attr mO g (Nat.min mO a) (Nat.min mO b) (min_le mO b) (min_mono mO a b H)).
    apply down_env_until_irrel.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH. reflexivity. - rewrite IH. reflexivity. - rewrite IH. reflexivity.
  - apply Closure_eq with (E := min_comp2 a b mO H).
    rewrite (@down_env_transport_forward_attr (Nat.min mO b) (Nat.min (Nat.min mO b) a) (Nat.min mO a)
               (min_comp2 a b mO H) (down_env_until g (Nat.min mO b) (min_le mO b))
               (min_le (Nat.min mO b) a) (min_mono mO a b H)).
    rewrite (@down_env_comp_fun attr mO g (Nat.min mO a) (Nat.min mO b) (min_le mO b) (min_mono mO a b H)).
    apply down_env_until_irrel.
Qed.

Lemma down_clos_min : forall {k} a b (C : Clos k),
  down_clos a (down_clos b C) = down_clos (Nat.min b a) C.
Proof.
  intros k a b C.
  induction C as [| |mO mI g r IHE M|W1 IH1 W2 IH2|W IH|W IH|W IH|mO mI g r IHE M]; cbn.
  - reflexivity. - reflexivity.
  - apply Thunk_eq with (E := min_min_swap mO b a).
    rewrite (@down_env_transport_forward_attr (Nat.min mO b) (Nat.min (Nat.min mO b) a) (Nat.min mO (Nat.min b a))
               (min_min_swap mO b a) (down_env_until g (Nat.min mO b) (min_le mO b))
               (min_le (Nat.min mO b) a) (min_mono mO (Nat.min b a) b (min_le_a b a))).
    rewrite (@down_env_comp_fun attr mO g (Nat.min mO (Nat.min b a)) (Nat.min mO b)
               (min_le mO b) (min_mono mO (Nat.min b a) b (min_le_a b a))).
    apply down_env_until_irrel.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH. reflexivity. - rewrite IH. reflexivity. - rewrite IH. reflexivity.
  - apply Closure_eq with (E := min_min_swap mO b a).
    rewrite (@down_env_transport_forward_attr (Nat.min mO b) (Nat.min (Nat.min mO b) a) (Nat.min mO (Nat.min b a))
               (min_min_swap mO b a) (down_env_until g (Nat.min mO b) (min_le mO b))
               (min_le (Nat.min mO b) a) (min_mono mO (Nat.min b a) b (min_le_a b a))).
    rewrite (@down_env_comp_fun attr mO g (Nat.min mO (Nat.min b a)) (Nat.min mO b)
               (min_le mO b) (min_mono mO (Nat.min b a) b (min_le_a b a))).
    apply down_env_until_irrel.
Qed.

Lemma eq_clos_refl : forall k (C : Clos k), eq_up_to_attrs C C.
Proof.
  intros k C. induction C as [| |mO mI g r IHE M|W1 IH1 W2 IH2|W IH|W IH|W IH|mO mI g r IHE M].
  - constructor. - constructor.
  - constructor. exact IHE.
  - constructor; assumption. - constructor; assumption. - constructor; assumption.
  - constructor; assumption.
  - constructor. exact IHE.
Qed.

Lemma eq_env_refl : forall {n} (ρ : env n), eq_env_up_to_attrs ρ ρ.
Proof. intros n ρ i. apply eq_clos_refl. Qed.

Lemma eq_down_clos : forall {k} s (C C' : Clos k), eq_up_to_attrs C C' ->
  eq_up_to_attrs (down_clos s C) (down_clos s C').
Proof.
  intros k s C C' H. induction H; cbn.
  - constructor. - constructor.
  - constructor. exact H.
  - constructor; assumption. - constructor; assumption.
  - constructor; assumption. - constructor; assumption.
  - constructor. exact H.
Qed.

(* ===== logical-relation weakening infrastructure ===== *)

Lemma non_func_up : forall {n} q (B : Ty n CompFlag), non_func (up_Ty q B) <-> non_func B.
Proof.
  intros n q B. dependent destruction B; cbn; unfold non_func.
  - split; intros H; exfalso;
      [ apply (H q0 (map_Ty (fun γ => q .: γ) B1) (map_Ty (fun γ => q .: γ) B2))
      | apply (H q0 B1 B2) ]; reflexivity.
  - split; intros H q1 A1 B1 E; discriminate E.
Qed.

Lemma LRM_up : forall {n} q (B : Ty n CompFlag) mInner (γ : attrs mInner) mO mLower (x : fin mLower)
  (Hnlower : mLower <= mInner) (ρ : env mInner) (M : Comp mInner),
  (forall C, LR_maybe B C mLower x -> LR_maybe (up_Ty q B) C mLower x) ->
  (forall C, LR_no B C mLower x -> LR_no (up_Ty q B) C mLower x) ->
  LRM B LR_maybe LR_no mInner γ mO mLower x Hnlower ρ M ->
  LRM (up_Ty q B) LR_maybe LR_no mInner γ mO mLower x Hnlower ρ M.
Proof.
  intros n q B mInner γ mO mLower x Hnlower ρ M Hmay Hno HLRM.
  unfold LRM in *. destruct HLRM as [H1 H2]. split.
  - intro Hstrict. destruct (H1 Hstrict) as [E1 E2]. split.
    + intro bnf. apply E1. apply (proj1 (non_func_up q B)). exact bnf.
    + intro nb.
      destruct (E2 (fun h => nb (proj2 (non_func_up q B) h))) as [f | (T & ev & lr)].
      * left; exact f.
      * right. exists T. split; [exact ev | apply Hno; exact lr].
  - intro Hns. destruct (H2 Hns) as [f | (T & ev & lr)].
    + left; exact f.
    + right. exists T. split; [exact ev | apply Hmay; exact lr].
Qed.

Lemma LRM_down : forall {n} (B : Ty n CompFlag) mInner (γ : attrs mInner) mO mO' mLower (x : fin mLower)
  (Hnlower : mLower <= mInner) (ρ : env mInner) (M : Comp mInner),
  mLower <= mO' -> mO' <= mO ->
  (forall C, LR_no B C mLower x -> LR_no B (down_clos mO' C) mLower x) ->
  (forall C, LR_maybe B C mLower x -> LR_maybe B (down_clos mO' C) mLower x) ->
  LRM B LR_maybe LR_no mInner γ mO mLower x Hnlower ρ M ->
  LRM B LR_maybe LR_no mInner γ mO' mLower x Hnlower ρ M.
Proof.
  intros n B mInner γ mO mO' mLower x Hnlower ρ M Hle1 Hle2 Hno Hmay HLRM.
  unfold LRM in *. destruct HLRM as [H1 H2]. split.
  - intro Hstrict. destruct (H1 Hstrict) as [E1 E2]. split; [exact E1 |].
    intro nb. destruct (E2 nb) as [f | (T & ev & lr)].
    + left; exact f.
    + right. exists T. split; [exact ev |].
      assert (Heq : down_clos mO' (mO T↓ T) = (mO' T↓ T)) by (apply @down_clos_comp2; exact Hle2).
      rewrite <- Heq. apply Hno; exact lr.
  - intro Hns. destruct (H2 Hns) as [f | (T & ev & lr)].
    + left; exact f.
    + right. exists T. split; [exact ev |].
      assert (Heq : down_clos mO' (mO T↓ T) = (mO' T↓ T)) by (apply @down_clos_comp2; exact Hle2).
      rewrite <- Heq. apply Hmay; exact lr.
Qed.

Lemma LRM_ud : forall {n} q (B : Ty n CompFlag) mInner (γ : attrs mInner) mO mLower (x : fin mLower)
  (Hnlower : mLower <= mInner) (ρ : env mInner) (M : Comp mInner),
  mO <= n ->
  (forall C, LR_no (up_Ty q B) C mLower x -> LR_no B (down_clos mO C) mLower x) ->
  (forall C, LR_maybe (up_Ty q B) C mLower x -> LR_maybe B (down_clos mO C) mLower x) ->
  LRM (up_Ty q B) LR_maybe LR_no mInner γ mO mLower x Hnlower ρ M ->
  LRM B LR_maybe LR_no mInner γ mO mLower x Hnlower ρ M.
Proof.
  intros n q B mInner γ mO mLower x Hnlower ρ M Hle Hno Hmay HLRM.
  unfold LRM in *. destruct HLRM as [H1 H2]. split.
  - intro Hstrict. destruct (H1 Hstrict) as [E1 E2]. split.
    + intro bnf. apply E1. apply (proj2 (non_func_up q B)). exact bnf.
    + intro nb.
      destruct (E2 (fun h => nb (proj1 (non_func_up q B) h))) as [f | (T & ev & lr)].
      * left; exact f.
      * right. exists T. split; [exact ev |].
        assert (Heq : down_clos mO (mO T↓ T) = (mO T↓ T)) by (apply @down_clos_idem).
        rewrite <- Heq. apply Hno; exact lr.
  - intro Hns. destruct (H2 Hns) as [f | (T & ev & lr)].
    + left; exact f.
    + right. exists T. split; [exact ev |].
      assert (Heq : down_clos mO (mO T↓ T) = (mO T↓ T)) by (apply @down_clos_idem).
      rewrite <- Heq. apply Hmay; exact lr.
Qed.

Definition LRprops {n k} (q : attr) (A : Ty n k) : Prop :=
  (forall C mLower x, LR_maybe A C mLower x -> LR_maybe (up_Ty q A) C mLower x)
  /\ (forall C mLower x, LR_no A C mLower x -> LR_no (up_Ty q A) C mLower x)
  /\ (forall C mLower x s, mLower <= s -> LR_maybe A C mLower x -> LR_maybe A (down_clos s C) mLower x)
  /\ (forall C mLower x s, mLower <= s -> LR_no A C mLower x -> LR_no A (down_clos s C) mLower x)
  /\ (forall C mLower x s, mLower <= s -> s <= n -> LR_maybe (up_Ty q A) C mLower x -> LR_maybe A (down_clos s C) mLower x)
  /\ (forall C mLower x s, mLower <= s -> s <= n -> LR_no (up_Ty q A) C mLower x -> LR_no A (down_clos s C) mLower x)
  /\ (forall C mLower x s, mLower <= s -> LR_maybe (up_Ty q A) C mLower x -> LR_maybe (up_Ty q A) (down_clos s C) mLower x)
  /\ (forall C mLower x s, mLower <= s -> LR_no (up_Ty q A) C mLower x -> LR_no (up_Ty q A) (down_clos s C) mLower x).

Lemma LR_shift_main : forall {n k} q (A : Ty n k), LRprops q A.
Proof.
  intros n k q A. induction A as [ | γ B IHB | A1 IHA1 A2 IHA2 | A1 IHA1 A2 IHA2 | q0 A1 IHA1 B1 IHB1 | A1 IHA1 ].
  - (* VUnit *)
    unfold LRprops; cbn. repeat split.
    + intros C mL x H. cbn in *. exact H.
    + intros C mL x H. cbn in *. exact H.
    + intros C mL x s Hs H. cbn in *. rewrite H. reflexivity.
    + intros C mL x s Hs H. cbn in *. exact H.
    + intros C mL x s Hs Hsn H. cbn in *. rewrite H. reflexivity.
    + intros C mL x s Hs Hsn H. cbn in *. exact H.
    + intros C mL x s Hs H. cbn in *. rewrite H. reflexivity.
    + intros C mL x s Hs H. cbn in *. exact H.
  - (* VThunk *)
    destruct IHB as [UmB [UnB [DmB [DnB [UDmB [UDnB [DupmB DupnB]]]]]]].
    unfold LRprops; cbn. repeat split.
    + intros C mL x H. destruct H as (mO & mI & γS & γInner & r0 & M0 & HInner & Hn & HLower & Hnlower & Hd1 & Hd2 & HC & HLRM).
      exists mO, mI, γS, γInner, r0, M0, HInner, (Nat.le_trans mO n (S n) Hn (le_succ_r n)), HLower, Hnlower.
      split.
      * rewrite (down_env_cons_fun q γ mO Hn (Nat.le_trans mO n (S n) Hn (le_succ_r n))). exact Hd1.
      * split; [exact Hd2 | split; [exact HC | apply (LRM_up q B mI γInner mO mL x Hnlower r0 M0 (fun C0 HC0 => UmB C0 mL x HC0) (fun C0 HC0 => UnB C0 mL x HC0) HLRM)]].
    + intros C mL x H. cbn in H. destruct H.
    + intros C mL x s Hs H. destruct H as (mO & mI & γS & γInner & r0 & M0 & HInner & Hn & HLower & Hnlower & Hd1 & Hd2 & HC & HLRM).
      rewrite HC. cbn. set (mO' := Nat.min mO s).
      exists mO', mI, (down_env_until γS mO' (min_le mO s)), γInner, r0, M0.
      exists (Nat.le_trans mO' mO mI (min_le_a mO s) HInner), (Nat.le_trans mO' mO n (min_le_a mO s) Hn), (le_min mO s mL HLower Hs), Hnlower.
      split.
      * rewrite <- Hd1. rewrite (down_env_comp_fun γ mO' mO Hn (min_le mO s)). apply down_env_until_irrel.
      * split.
        -- rewrite <- Hd2. rewrite (down_env_comp_fun γInner mO' mO HInner (min_le mO s)). apply down_env_until_irrel.
        -- split.
           ++ reflexivity.
           ++ apply (LRM_down B mI γInner mO mO' mL x Hnlower r0 M0 (le_min mO s mL HLower Hs) (min_le_a mO s)
                        (fun C0 HC0 => DnB C0 mL x mO' (le_min mO s mL HLower Hs) HC0)
                        (fun C0 HC0 => DmB C0 mL x mO' (le_min mO s mL HLower Hs) HC0) HLRM).
    + intros C mL x s Hs H. cbn in H. destruct H.
    + intros C mL x s Hs Hsn H. destruct H as (mO & mI & γS & γInner & r0 & M0 & HInner & Hn & HLower & Hnlower & Hd1 & Hd2 & HC & HLRM).
      rewrite HC. cbn. set (mO' := Nat.min mO s).
      set (Hn' := Nat.le_trans mO' s n (min_le_b mO s) Hsn).
      set (HnS := Nat.le_trans mO' n (S n) Hn' (le_succ_r n)).
      exists mO', mI, (down_env_until γS mO' (min_le mO s)), γInner, r0, M0.
      exists (Nat.le_trans mO' mO mI (min_le_a mO s) HInner), Hn', (le_min mO s mL HLower Hs), Hnlower.
      split.
      * transitivity (down_env_until (q .: γ) mO' HnS).
        -- symmetry. apply (down_env_cons_fun q γ mO' Hn' HnS).
        -- transitivity (down_env_until (down_env_until (q .: γ) mO Hn) mO' (min_le mO s)).
           ++ transitivity (down_env_until (q .: γ) mO' (Nat.le_trans mO' mO (S n) (min_le mO s) Hn)).
              ** apply down_env_until_irrel.
              ** symmetry. apply (down_env_comp_fun (q .: γ) mO' mO Hn (min_le mO s)).
           ++ rewrite Hd1. apply down_env_until_irrel.
      * split.
        -- rewrite <- Hd2. rewrite (down_env_comp_fun γInner mO' mO HInner (min_le mO s)). apply down_env_until_irrel.
        -- split.
           ++ reflexivity.
           ++ apply (LRM_ud q B mI γInner mO' mL x Hnlower r0 M0 Hn'
                        (fun C0 HC0 => UDnB C0 mL x mO' (le_min mO s mL HLower Hs) Hn' HC0)
                        (fun C0 HC0 => UDmB C0 mL x mO' (le_min mO s mL HLower Hs) Hn' HC0)).
              apply (LRM_down (up_Ty q B) mI γInner mO mO' mL x Hnlower r0 M0
                        (le_min mO s mL HLower Hs) (min_le_a mO s)
                        (fun C0 HC0 => DupnB C0 mL x mO' (le_min mO s mL HLower Hs) HC0)
                        (fun C0 HC0 => DupmB C0 mL x mO' (le_min mO s mL HLower Hs) HC0) HLRM).
    + intros C mL x s Hs Hsn H. cbn in H. destruct H.
    + intros C mL x s Hs H. destruct H as (mO & mI & γS & γInner & r0 & M0 & HInner & Hn & HLower & Hnlower & Hd1 & Hd2 & HC & HLRM).
      rewrite HC. cbn. set (mO' := Nat.min mO s).
      exists mO', mI, (down_env_until γS mO' (min_le mO s)), γInner, r0, M0.
      exists (Nat.le_trans mO' mO mI (min_le_a mO s) HInner), (Nat.le_trans mO' mO (S n) (min_le_a mO s) Hn), (le_min mO s mL HLower Hs), Hnlower.
      split.
      * rewrite <- Hd1. rewrite (down_env_comp_fun (q .: γ) mO' mO Hn (min_le mO s)). apply down_env_until_irrel.
      * split.
        -- rewrite <- Hd2. rewrite (down_env_comp_fun γInner mO' mO HInner (min_le mO s)). apply down_env_until_irrel.
        -- split.
           ++ reflexivity.
           ++ apply (LRM_down (up_Ty q B) mI γInner mO mO' mL x Hnlower r0 M0 (le_min mO s mL HLower Hs) (min_le_a mO s)
                        (fun C0 HC0 => DupnB C0 mL x mO' (le_min mO s mL HLower Hs) HC0)
                        (fun C0 HC0 => DupmB C0 mL x mO' (le_min mO s mL HLower Hs) HC0) HLRM).
    + intros C mL x s Hs H. cbn in H. destruct H.
  - (* VProd *)
    destruct IHA1 as [Um1 [Un1 [Dm1 [Dn1 [UDm1 [UDn1 [Dupm1 Dupn1]]]]]]].
    destruct IHA2 as [Um2 [Un2 [Dm2 [Dn2 [UDm2 [UDn2 [Dupm2 Dupn2]]]]]]].
    unfold LRprops; cbn. repeat split.
    + intros C mL x H. destruct H as (W1 & W2 & HC & H1 & H2). cbn. exists W1, W2.
      split; [exact HC | split; [exact (Um1 W1 mL x H1) | exact (Um2 W2 mL x H2)]].
    + intros C mL x H. cbn in H. destruct H.
    + intros C mL x s Hs H. destruct H as (W1 & W2 & HC & H1 & H2). cbn.
      exists (down_clos s W1), (down_clos s W2). split.
      * rewrite HC. reflexivity.
      * split; [exact (Dm1 W1 mL x s Hs H1) | exact (Dm2 W2 mL x s Hs H2)].
    + intros C mL x s Hs H. cbn in H. destruct H.
    + intros C mL x s Hs Hsn H. destruct H as (W1 & W2 & HC & H1 & H2). cbn.
      exists (down_clos s W1), (down_clos s W2). split.
      * rewrite HC. reflexivity.
      * split; [exact (UDm1 W1 mL x s Hs Hsn H1) | exact (UDm2 W2 mL x s Hs Hsn H2)].
    + intros C mL x s Hs Hsn H. cbn in H. destruct H.
    + intros C mL x s Hs H. destruct H as (W1 & W2 & HC & H1 & H2). cbn.
      exists (down_clos s W1), (down_clos s W2). split.
      * rewrite HC. reflexivity.
      * split; [exact (Dupm1 W1 mL x s Hs H1) | exact (Dupm2 W2 mL x s Hs H2)].
    + intros C mL x s Hs H. cbn in H. destruct H.
  - (* VSum *)
    destruct IHA1 as [Um1 [Un1 [Dm1 [Dn1 [UDm1 [UDn1 [Dupm1 Dupn1]]]]]]].
    destruct IHA2 as [Um2 [Un2 [Dm2 [Dn2 [UDm2 [UDn2 [Dupm2 Dupn2]]]]]]].
    unfold LRprops; cbn. repeat split.
    + intros C mL x H. destruct H as (W & Hd). cbn. exists W.
      destruct Hd as [ (HC & H1) | (HC & H2) ].
      * left. split; [exact HC | exact (Um1 W mL x H1)].
      * right. split; [exact HC | exact (Um2 W mL x H2)].
    + intros C mL x H. cbn in H. destruct H.
    + intros C mL x s Hs H. destruct H as (W & Hd).
      destruct Hd as [ (HC & H1) | (HC & H2) ].
      * exists (down_clos s W). left. split; [rewrite HC; reflexivity | exact (Dm1 W mL x s Hs H1)].
      * exists (down_clos s W). right. split; [rewrite HC; reflexivity | exact (Dm2 W mL x s Hs H2)].
    + intros C mL x s Hs H. cbn in H. destruct H.
    + intros C mL x s Hs Hsn H. destruct H as (W & Hd).
      destruct Hd as [ (HC & H1) | (HC & H2) ].
      * exists (down_clos s W). left. split; [rewrite HC; reflexivity | exact (UDm1 W mL x s Hs Hsn H1)].
      * exists (down_clos s W). right. split; [rewrite HC; reflexivity | exact (UDm2 W mL x s Hs Hsn H2)].
    + intros C mL x s Hs Hsn H. cbn in H. destruct H.
    + intros C mL x s Hs H. destruct H as (W & Hd).
      destruct Hd as [ (HC & H1) | (HC & H2) ].
      * exists (down_clos s W). left. split; [rewrite HC; reflexivity | exact (Dupm1 W mL x s Hs H1)].
      * exists (down_clos s W). right. split; [rewrite HC; reflexivity | exact (Dupm2 W mL x s Hs H2)].
    + intros C mL x s Hs H. cbn in H. destruct H.
  - (* CAbs *)
    destruct IHA1 as [Um1 [Un1 [Dm1 [Dn1 [UDm1 [UDn1 [Dupm1 Dupn1]]]]]]].
    destruct IHB1 as [UmB [UnB [DmB [DnB [UDmB [UDnB [DupmB DupnB]]]]]]].
    unfold LRprops; cbn. repeat split.
    + intros C mL x H. destruct H as (mO & mI & γS & γInner & r0 & M0 & Hn & HInner & HLower & Hnlower & Hd & HC & Hbody).
      cbn. exists mO, mI, γS, γInner, r0, M0, (Nat.le_trans mO n (S n) Hn (le_succ_r n)), HInner, HLower, Hnlower.
      split; [exact Hd | split; [exact HC |]].
      intros W HWA.
      assert (Heq : down_value mO (@down_clos ValFlag mO W) = down_value mO W) by (apply down_clos_idem).
      destruct (Hbody (@down_clos ValFlag mO W) (UDm1 W mL x mO HLower Hn HWA)) as [f | (T & ev & lr)].
      * left. rewrite Heq in f. exact f.
      * right. exists T. split. -- rewrite Heq in ev. exact ev. -- exact (UmB (mO T↓ T) mL x lr).
    + intros C mL x H. destruct H as (mO & mI & γS & γInner & r0 & M0 & Hn & HInner & HLower & Hnlower & Hd & HC & Hbody).
      cbn. exists mO, mI, γS, γInner, r0, M0, (Nat.le_trans mO n (S n) Hn (le_succ_r n)), HInner, HLower, Hnlower.
      split; [exact Hd | split; [exact HC |]].
      intros W HWA.
      assert (Heq : down_value mO (@down_clos ValFlag mO W) = down_value mO W) by (apply down_clos_idem).
      destruct (Hbody (@down_clos ValFlag mO W) (UDm1 W mL x mO HLower Hn HWA)) as [E1 E2]. split.
      * intro bnf. pose proof (E1 (proj1 (non_func_up q B1) bnf)) as h. rewrite Heq in h. exact h.
      * intro nb. destruct (E2 (fun h => nb (proj2 (non_func_up q B1) h))) as [f | (T & ev & lr)].
        -- left. rewrite Heq in f. exact f.
        -- right. exists T. split. ++ rewrite Heq in ev. exact ev. ++ exact (UnB (mO T↓ T) mL x lr).
    + intros C mL x s Hs H. destruct H as (mO & mI & γS & γInner & r0 & M0 & Hn & HInner & HLower & Hnlower & Hd & HC & Hbody).
      rewrite HC. cbn. set (mO' := Nat.min mO s).
      exists mO', mI, (down_env_until γS mO' (min_le mO s)), γInner, r0, M0.
      exists (Nat.le_trans mO' mO n (min_le_a mO s) Hn), (Nat.le_trans mO' mO mI (min_le_a mO s) HInner), (le_min mO s mL HLower Hs), Hnlower.
      split.
      * rewrite <- Hd. rewrite (down_env_comp_fun γInner mO' mO HInner (min_le mO s)). apply down_env_until_irrel.
      * split.
        -- reflexivity.
        -- intros W HWA.
           assert (Heq : down_value mO (@down_clos ValFlag mO' W) = down_value mO' W) by (apply down_clos_le; apply min_le_a).
           destruct (Hbody (@down_clos ValFlag mO' W) (Dm1 W mL x mO' (le_min mO s mL HLower Hs) HWA)) as [f | (T & ev & lr)].
           ++ left. rewrite Heq in f. exact f.
           ++ right. exists T. split.
              ** rewrite Heq in ev. exact ev.
              ** assert (H1 : LR_maybe B1 (@down_clos CompFlag mO' (mO T↓ T)) mL x) by (apply (DmB (mO T↓ T) mL x mO' (le_min mO s mL HLower Hs)); exact lr).
                 assert (Heq2 : @down_clos CompFlag mO' (mO T↓ T) = (mO' T↓ T)) by (apply @down_clos_comp2; apply min_le_a).
                 rewrite Heq2 in H1. exact H1.
    + intros C mL x s Hs H. destruct H as (mO & mI & γS & γInner & r0 & M0 & Hn & HInner & HLower & Hnlower & Hd & HC & Hbody).
      rewrite HC. cbn. set (mO' := Nat.min mO s).
      exists mO', mI, (down_env_until γS mO' (min_le mO s)), γInner, r0, M0.
      exists (Nat.le_trans mO' mO n (min_le_a mO s) Hn), (Nat.le_trans mO' mO mI (min_le_a mO s) HInner), (le_min mO s mL HLower Hs), Hnlower.
      split.
      * rewrite <- Hd. rewrite (down_env_comp_fun γInner mO' mO HInner (min_le mO s)). apply down_env_until_irrel.
      * split.
        -- reflexivity.
        -- intros W HWA.
           assert (Heq : down_value mO (@down_clos ValFlag mO' W) = down_value mO' W) by (apply down_clos_le; apply min_le_a).
           destruct (Hbody (@down_clos ValFlag mO' W) (Dm1 W mL x mO' (le_min mO s mL HLower Hs) HWA)) as [E1 E2]. split.
           ++ intro bnf. pose proof (E1 bnf) as h. rewrite Heq in h. exact h.
           ++ intro nb. destruct (E2 nb) as [f | (T & ev & lr)].
              ** left. rewrite Heq in f. exact f.
              ** right. exists T. split.
                 --- rewrite Heq in ev. exact ev.
                 --- assert (H1 : LR_no B1 (@down_clos CompFlag mO' (mO T↓ T)) mL x) by (apply (DnB (mO T↓ T) mL x mO' (le_min mO s mL HLower Hs)); exact lr).
                     assert (Heq2 : @down_clos CompFlag mO' (mO T↓ T) = (mO' T↓ T)) by (apply @down_clos_comp2; apply min_le_a).
                     rewrite Heq2 in H1. exact H1.
    + intros C mL x s Hs Hsn H. destruct H as (mO & mI & γS & γInner & r0 & M0 & Hn & HInner & HLower & Hnlower & Hd & HC & Hbody).
      rewrite HC. cbn. set (mO' := Nat.min mO s).
      set (Hn' := Nat.le_trans mO' s n (min_le_b mO s) Hsn).
      exists mO', mI, (down_env_until γS mO' (min_le mO s)), γInner, r0, M0.
      exists Hn', (Nat.le_trans mO' mO mI (min_le_a mO s) HInner), (le_min mO s mL HLower Hs), Hnlower.
      split.
      * rewrite <- Hd. rewrite (down_env_comp_fun γInner mO' mO HInner (min_le mO s)). apply down_env_until_irrel.
      * split.
        -- reflexivity.
        -- intros W HWA.
           assert (Heq : down_value mO (@down_clos ValFlag mO' W) = down_value mO' W) by (apply down_clos_le; apply min_le_a).
           assert (HWA' : LR_maybe (up_Ty q A1) (@down_clos ValFlag mO' W) mL x) by (apply (Dupm1 W mL x mO' (le_min mO s mL HLower Hs)); apply (Um1 W mL x HWA)).
           destruct (Hbody (@down_clos ValFlag mO' W) HWA') as [f | (T & ev & lr)].
           ++ left. rewrite Heq in f. exact f.
           ++ right. exists T. split.
              ** rewrite Heq in ev. exact ev.
              ** assert (H1 : LR_maybe (up_Ty q B1) (@down_clos CompFlag mO' (mO T↓ T)) mL x) by (apply (DupmB (mO T↓ T) mL x mO' (le_min mO s mL HLower Hs)); exact lr).
                 assert (Heq2 : @down_clos CompFlag mO' (mO T↓ T) = (mO' T↓ T)) by (apply @down_clos_comp2; apply min_le_a).
                 rewrite Heq2 in H1.
                 assert (Heq3 : @down_clos CompFlag mO' (mO' T↓ T) = (mO' T↓ T)) by (apply @down_clos_idem).
                 rewrite <- Heq3. exact (UDmB (mO' T↓ T) mL x mO' (le_min mO s mL HLower Hs) Hn' H1).
    + intros C mL x s Hs Hsn H. destruct H as (mO & mI & γS & γInner & r0 & M0 & Hn & HInner & HLower & Hnlower & Hd & HC & Hbody).
      rewrite HC. cbn. set (mO' := Nat.min mO s).
      set (Hn' := Nat.le_trans mO' s n (min_le_b mO s) Hsn).
      exists mO', mI, (down_env_until γS mO' (min_le mO s)), γInner, r0, M0.
      exists Hn', (Nat.le_trans mO' mO mI (min_le_a mO s) HInner), (le_min mO s mL HLower Hs), Hnlower.
      split.
      * rewrite <- Hd. rewrite (down_env_comp_fun γInner mO' mO HInner (min_le mO s)). apply down_env_until_irrel.
      * split.
        -- reflexivity.
        -- intros W HWA.
           assert (Heq : down_value mO (@down_clos ValFlag mO' W) = down_value mO' W) by (apply down_clos_le; apply min_le_a).
           assert (HWA' : LR_maybe (up_Ty q A1) (@down_clos ValFlag mO' W) mL x) by (apply (Dupm1 W mL x mO' (le_min mO s mL HLower Hs)); apply (Um1 W mL x HWA)).
           destruct (Hbody (@down_clos ValFlag mO' W) HWA') as [E1 E2]. split.
           ++ intro bnf. pose proof (E1 (proj2 (non_func_up q B1) bnf)) as h. rewrite Heq in h. exact h.
           ++ intro nb. destruct (E2 (fun h => nb (proj1 (non_func_up q B1) h))) as [f | (T & ev & lr)].
              ** left. rewrite Heq in f. exact f.
              ** right. exists T. split.
                 --- rewrite Heq in ev. exact ev.
                 --- assert (H1 : LR_no (up_Ty q B1) (@down_clos CompFlag mO' (mO T↓ T)) mL x) by (apply (DupnB (mO T↓ T) mL x mO' (le_min mO s mL HLower Hs)); exact lr).
                     assert (Heq2 : @down_clos CompFlag mO' (mO T↓ T) = (mO' T↓ T)) by (apply @down_clos_comp2; apply min_le_a).
                     rewrite Heq2 in H1.
                     assert (Heq3 : @down_clos CompFlag mO' (mO' T↓ T) = (mO' T↓ T)) by (apply @down_clos_idem).
                     rewrite <- Heq3. exact (UDnB (mO' T↓ T) mL x mO' (le_min mO s mL HLower Hs) Hn' H1).
    + intros C mL x s Hs H. destruct H as (mO & mI & γS & γInner & r0 & M0 & Hn & HInner & HLower & Hnlower & Hd & HC & Hbody).
      rewrite HC. cbn. set (mO' := Nat.min mO s).
      exists mO', mI, (down_env_until γS mO' (min_le mO s)), γInner, r0, M0.
      exists (Nat.le_trans mO' mO (S n) (min_le_a mO s) Hn), (Nat.le_trans mO' mO mI (min_le_a mO s) HInner), (le_min mO s mL HLower Hs), Hnlower.
      split.
      * rewrite <- Hd. rewrite (down_env_comp_fun γInner mO' mO HInner (min_le mO s)). apply down_env_until_irrel.
      * split.
        -- reflexivity.
        -- intros W HWA.
           assert (Heq : down_value mO (@down_clos ValFlag mO' W) = down_value mO' W) by (apply down_clos_le; apply min_le_a).
           destruct (Hbody (@down_clos ValFlag mO' W) (Dupm1 W mL x mO' (le_min mO s mL HLower Hs) HWA)) as [f | (T & ev & lr)].
           ++ left. rewrite Heq in f. exact f.
           ++ right. exists T. split.
              ** rewrite Heq in ev. exact ev.
              ** assert (H1 : LR_maybe (up_Ty q B1) (@down_clos CompFlag mO' (mO T↓ T)) mL x) by (apply (DupmB (mO T↓ T) mL x mO' (le_min mO s mL HLower Hs)); exact lr).
                 assert (Heq2 : @down_clos CompFlag mO' (mO T↓ T) = (mO' T↓ T)) by (apply @down_clos_comp2; apply min_le_a).
                 rewrite Heq2 in H1. exact H1.
    + intros C mL x s Hs H. destruct H as (mO & mI & γS & γInner & r0 & M0 & Hn & HInner & HLower & Hnlower & Hd & HC & Hbody).
      rewrite HC. cbn. set (mO' := Nat.min mO s).
      exists mO', mI, (down_env_until γS mO' (min_le mO s)), γInner, r0, M0.
      exists (Nat.le_trans mO' mO (S n) (min_le_a mO s) Hn), (Nat.le_trans mO' mO mI (min_le_a mO s) HInner), (le_min mO s mL HLower Hs), Hnlower.
      split.
      * rewrite <- Hd. rewrite (down_env_comp_fun γInner mO' mO HInner (min_le mO s)). apply down_env_until_irrel.
      * split.
        -- reflexivity.
        -- intros W HWA.
           assert (Heq : down_value mO (@down_clos ValFlag mO' W) = down_value mO' W) by (apply down_clos_le; apply min_le_a).
           destruct (Hbody (@down_clos ValFlag mO' W) (Dupm1 W mL x mO' (le_min mO s mL HLower Hs) HWA)) as [E1 E2]. split.
           ++ intro bnf. pose proof (E1 bnf) as h. rewrite Heq in h. exact h.
           ++ intro nb. destruct (E2 nb) as [f | (T & ev & lr)].
              ** left. rewrite Heq in f. exact f.
              ** right. exists T. split.
                 --- rewrite Heq in ev. exact ev.
                 --- assert (H1 : LR_no (up_Ty q B1) (@down_clos CompFlag mO' (mO T↓ T)) mL x) by (apply (DupnB (mO T↓ T) mL x mO' (le_min mO s mL HLower Hs)); exact lr).
                     assert (Heq2 : @down_clos CompFlag mO' (mO T↓ T) = (mO' T↓ T)) by (apply @down_clos_comp2; apply min_le_a).
                     rewrite Heq2 in H1. exact H1.
  - (* CF *)
    destruct IHA1 as [Um1 [Un1 [Dm1 [Dn1 [UDm1 [UDn1 [Dupm1 Dupn1]]]]]]].
    unfold LRprops; cbn. repeat split.
    + intros C mL x H. destruct H as (W & HC & H1). cbn. exists W. split; [exact HC | exact (Um1 W mL x H1)].
    + intros C mL x H. cbn in H. destruct H.
    + intros C mL x s Hs H. destruct H as (W & HC & H1). cbn. exists (down_clos s W). split; [rewrite HC; reflexivity | exact (Dm1 W mL x s Hs H1)].
    + intros C mL x s Hs H. cbn in H. destruct H.
    + intros C mL x s Hs Hsn H. destruct H as (W & HC & H1). cbn. exists (down_clos s W). split; [rewrite HC; reflexivity | exact (UDm1 W mL x s Hs Hsn H1)].
    + intros C mL x s Hs Hsn H. cbn in H. destruct H.
    + intros C mL x s Hs H. destruct H as (W & HC & H1). cbn. exists (down_clos s W). split; [rewrite HC; reflexivity | exact (Dupm1 W mL x s Hs H1)].
    + intros C mL x s Hs H. cbn in H. destruct H.
Qed.


Lemma LRprops_Um : forall {n k} (q : attr) (A : Ty n k) C mL x,
  LR_maybe A C mL x -> LR_maybe (up_Ty q A) C mL x.
Proof. intros. destruct (LR_shift_main q A) as [U _]. exact (U C mL x H). Qed.
Lemma LRprops_Dm : forall {n k} (q : attr) (A : Ty n k) C mL x s, mL <= s ->
  LR_maybe A C mL x -> LR_maybe A (down_clos s C) mL x.
Proof. intros. destruct (LR_shift_main q A) as [_ [_ [D _]]]. exact (D C mL x s H H0). Qed.
Lemma LRprops_Dn : forall {n k} (q : attr) (A : Ty n k) C mL x s, mL <= s ->
  LR_no A C mL x -> LR_no A (down_clos s C) mL x.
Proof. intros. destruct (LR_shift_main q A) as [_ [_ [_ [Dn _]]]]. exact (Dn C mL x s H H0). Qed.
Lemma LRprops_UDm : forall {n k} (q : attr) (A : Ty n k) C mL x s, mL <= s -> s <= n ->
  LR_maybe (up_Ty q A) C mL x -> LR_maybe A (down_clos s C) mL x.
Proof. intros. destruct (LR_shift_main q A) as [_ [_ [_ [_ [UD _]]]]]. exact (UD C mL x s H H0 H1). Qed.
Lemma LRprops_Dupm : forall {n k} (q : attr) (A : Ty n k) C mL x s, mL <= s ->
  LR_maybe (up_Ty q A) C mL x -> LR_maybe (up_Ty q A) (down_clos s C) mL x.
Proof. intros. destruct (LR_shift_main q A) as [_ [_ [_ [_ [_ [_ [Dup _]]]]]]]. exact (Dup C mL x s H H0). Qed.

(* ===== down-type transfer ===== *)

Lemma non_func_down_ty : forall {N} (B : Ty N CompFlag) n (Hn : n <= N),
  non_func (down_ty_until B n Hn) <-> non_func B.
Proof.
  intros N B n Hn. dependent destruction B; cbn; unfold non_func.
  - split; intros H; exfalso;
      [ apply (H q (down_ty_until B1 n Hn) (down_ty_until B2 n Hn))
      | apply (H q B1 B2) ]; reflexivity.
  - split; intros H q1 A1 B1 E; discriminate E.
Qed.

Lemma LRM_down_ty : forall {N} (B : Ty N CompFlag) n (Hn : n <= N) mInner (γ : attrs mInner) mO mLower (x : fin mLower)
  (Hnlower : mLower <= mInner) (ρ : env mInner) (M : Comp mInner),
  (forall C, LR_no B C mLower x -> LR_no (down_ty_until B n Hn) (down_clos n C) mLower x) ->
  (forall C, LR_maybe B C mLower x -> LR_maybe (down_ty_until B n Hn) (down_clos n C) mLower x) ->
  LRM B LR_maybe LR_no mInner γ mO mLower x Hnlower ρ M ->
  LRM (down_ty_until B n Hn) LR_maybe LR_no mInner γ (Nat.min mO n) mLower x Hnlower ρ M.
Proof.
  intros N B n Hn mInner γ mO mLower x Hnlower ρ M Hno Hmay HLRM.
  unfold LRM in *. destruct HLRM as [H1 H2]. split.
  - intro Hstrict. destruct (H1 Hstrict) as [E1 E2]. split.
    + intro bnf. apply E1. apply (proj1 (non_func_down_ty B n Hn)). exact bnf.
    + intro nb. destruct (E2 (fun h => nb (proj2 (non_func_down_ty B n Hn) h))) as [f | (T & ev & lr)].
      * left; exact f.
      * right. exists T. split; [exact ev |].
        assert (Heq : @down_comp (Nat.min mO n) T = @down_comp n (mO T↓ T)) by (symmetry; apply @down_clos_min).
        rewrite Heq. apply Hno; exact lr.
  - intro Hns. destruct (H2 Hns) as [f | (T & ev & lr)].
    + left; exact f.
    + right. exists T. split; [exact ev |].
      assert (Heq : @down_comp (Nat.min mO n) T = @down_comp n (mO T↓ T)) by (symmetry; apply @down_clos_min).
      rewrite Heq. apply Hmay; exact lr.
Qed.

Lemma LRM_conv : forall {N} (B : Ty N CompFlag) n (Hn : n <= N) mInner (γ : attrs mInner) mO mLower (x : fin mLower)
  (Hnlower : mLower <= mInner) (ρ : env mInner) (M : Comp mInner),
  (forall C, LR_no (down_ty_until B n Hn) C mLower x -> LR_no B C mLower x) ->
  (forall C, LR_maybe (down_ty_until B n Hn) C mLower x -> LR_maybe B C mLower x) ->
  LRM (down_ty_until B n Hn) LR_maybe LR_no mInner γ mO mLower x Hnlower ρ M ->
  LRM B LR_maybe LR_no mInner γ mO mLower x Hnlower ρ M.
Proof.
  intros N B n Hn mInner γ mO mLower x Hnlower ρ M Hno Hmay HLRM.
  unfold LRM in *. destruct HLRM as [H1 H2]. split.
  - intro Hstrict. destruct (H1 Hstrict) as [E1 E2]. split.
    + intro bnf. apply E1. apply (proj2 (non_func_down_ty B n Hn)). exact bnf.
    + intro nb. destruct (E2 (fun h => nb (proj1 (non_func_down_ty B n Hn) h))) as [f | (T & ev & lr)].
      * left; exact f.
      * right. exists T. split; [exact ev | exact (Hno (mO T↓ T) lr)].
  - intro Hns. destruct (H2 Hns) as [f | (T & ev & lr)].
    + left; exact f.
    + right. exists T. split; [exact ev | exact (Hmay (mO T↓ T) lr)].
Qed.

Definition DRprops {N} (n : nat) (Hn : n <= N) {k} (A : Ty N k) : Prop :=
  (forall C mLower x, mLower <= n -> LR_maybe A C mLower x -> LR_maybe (down_ty_until A n Hn) (down_clos n C) mLower x)
  /\ (forall C mLower x, mLower <= n -> LR_no A C mLower x -> LR_no (down_ty_until A n Hn) (down_clos n C) mLower x)
  /\ (forall C mLower x, mLower <= n -> LR_maybe (down_ty_until A n Hn) C mLower x -> LR_maybe A C mLower x)
  /\ (forall C mLower x, mLower <= n -> LR_no (down_ty_until A n Hn) C mLower x -> LR_no A C mLower x).

Lemma DR_main : forall {N} n (Hn : n <= N) {k} (A : Ty N k), DRprops n Hn A.
Proof.
  intros N n HD k A. induction A as [ | γ B IHB | A1 IHA1 A2 IHA2 | A1 IHA1 A2 IHA2 | q0 A1 IHA1 B1 IHB1 | A1 IHA1 ].
  - unfold DRprops; cbn. repeat split.
    + intros C mL x Hml H. cbn in *. rewrite H. reflexivity.
    + intros C mL x Hml H. cbn in *. exact H.
    + intros C mL x Hml H. cbn in *. exact H.
    + intros C mL x Hml H. cbn in *. exact H.
  - destruct IHB as [DownM [DownN [ConvM ConvN]]].
    unfold DRprops; cbn. repeat split.
    + intros C mL x Hml H.
      destruct H as (mO & mI & γS & γInner & r0 & M0 & HInner & Hn & HLower & Hnlower & Hd1 & Hd2 & HC & HLRM).
      rewrite HC. cbn. set (mO' := Nat.min mO n).
      exists mO', mI, (down_env_until γS mO' (min_le mO n)), γInner, r0, M0.
      exists (Nat.le_trans mO' mO mI (min_le_a mO n) HInner), (min_le_b mO n), (le_min mO n mL HLower Hml), Hnlower.
      split.
      * rewrite <- Hd1. rewrite (@down_env_comp_fun attr N γ mO' mO Hn (min_le mO n)).
        rewrite (@down_env_comp_fun attr N γ mO' n HD (min_le_b mO n)). apply down_env_until_irrel.
      * split.
        -- rewrite <- Hd2. rewrite (@down_env_comp_fun attr mI γInner mO' mO HInner (min_le mO n)). apply down_env_until_irrel.
        -- split.
           ++ reflexivity.
           ++ apply (LRM_down_ty B n HD mI γInner mO mL x Hnlower r0 M0
                    (fun C0 HC0 => DownN C0 mL x Hml HC0)
                    (fun C0 HC0 => DownM C0 mL x Hml HC0) HLRM).
    + intros C mL x Hml H. cbn in H. destruct H.
    + intros C mL x Hml H.
      destruct H as (mO & mI & γS & γInner & r0 & M0 & HInner & Hn & HLower & Hnlower & Hd1 & Hd2 & HC & HLRM).
      exists mO, mI, γS, γInner, r0, M0, HInner, (Nat.le_trans mO n N Hn HD), HLower, Hnlower.
      split.
      * rewrite <- Hd1. symmetry. apply (@down_env_comp_fun attr N γ mO n HD Hn).
      * split; [exact Hd2 | split; [exact HC |]].
        apply (LRM_conv B n HD mI γInner mO mL x Hnlower r0 M0
                 (fun C0 HC0 => ConvN C0 mL x Hml HC0)
                 (fun C0 HC0 => ConvM C0 mL x Hml HC0) HLRM).
    + intros C mL x Hml H. cbn in H. destruct H.
  - destruct IHA1 as [DM1 [DN1 [CM1 CN1]]]. destruct IHA2 as [DM2 [DN2 [CM2 CN2]]].
    unfold DRprops; cbn. repeat split.
    + intros C mL x Hml H. destruct H as (W1 & W2 & HC & H1 & H2). cbn.
      exists (down_clos n W1), (down_clos n W2). split.
      * rewrite HC. reflexivity.
      * split; [exact (DM1 W1 mL x Hml H1) | exact (DM2 W2 mL x Hml H2)].
    + intros C mL x Hml H. cbn in H. destruct H.
    + intros C mL x Hml H. destruct H as (W1 & W2 & HC & H1 & H2). cbn.
      exists W1, W2. split; [exact HC | split; [exact (CM1 W1 mL x Hml H1) | exact (CM2 W2 mL x Hml H2)]].
    + intros C mL x Hml H. cbn in H. destruct H.
  - destruct IHA1 as [DM1 [DN1 [CM1 CN1]]]. destruct IHA2 as [DM2 [DN2 [CM2 CN2]]].
    unfold DRprops; cbn. repeat split.
    + intros C mL x Hml H. destruct H as (W & Hd). cbn.
      destruct Hd as [ (HC & H1) | (HC & H2) ].
      * exists (down_clos n W). left. split; [rewrite HC; reflexivity | exact (DM1 W mL x Hml H1)].
      * exists (down_clos n W). right. split; [rewrite HC; reflexivity | exact (DM2 W mL x Hml H2)].
    + intros C mL x Hml H. cbn in H. destruct H.
    + intros C mL x Hml H. destruct H as (W & Hd).
      destruct Hd as [ (HC & H1) | (HC & H2) ].
      * exists W. left. split; [exact HC | exact (CM1 W mL x Hml H1)].
      * exists W. right. split; [exact HC | exact (CM2 W mL x Hml H2)].
    + intros C mL x Hml H. cbn in H. destruct H.
  - destruct IHA1 as [DM1 [DN1 [CM1 CN1]]]. destruct IHB1 as [DMB [DNB [CMB CNB]]].
    unfold DRprops; cbn. repeat split.
    + intros C mL x Hml H.
      destruct H as (mO & mI & γS & γInner & r0 & M0 & Hn & HInner & HLower & Hnlower & Hd & HC & Hbody).
      rewrite HC. cbn. set (mO' := Nat.min mO n).
      exists mO', mI, (down_env_until γS mO' (min_le mO n)), γInner, r0, M0.
      exists (min_le_b mO n), (Nat.le_trans mO' mO mI (min_le_a mO n) HInner), (le_min mO n mL HLower Hml), Hnlower.
      split.
      * rewrite <- Hd. rewrite (@down_env_comp_fun attr mI γInner mO' mO HInner (min_le mO n)). apply down_env_until_irrel.
      * split.
        -- reflexivity.
        -- intros W HWA.
           assert (Heq : down_value mO (@down_clos ValFlag mO' W) = down_value mO' W) by (apply down_clos_le; apply min_le_a).
           assert (HWA0 : LR_maybe A1 (@down_clos ValFlag mO' W) mL x) by (apply (LRprops_Dm Lazy A1 W mL x mO' (le_min mO n mL HLower Hml)); apply (CM1 W mL x Hml HWA)).
           destruct (Hbody (@down_clos ValFlag mO' W) HWA0) as [f | (T & ev & lr)].
           ++ left. rewrite Heq in f. exact f.
           ++ right. exists T. split.
              ** rewrite Heq in ev. exact ev.
              ** assert (H1 : LR_maybe (down_ty_until B1 n HD) (@down_clos CompFlag n (mO T↓ T)) mL x) by (apply (DMB (mO T↓ T) mL x Hml); exact lr).
                 assert (Heq2 : @down_clos CompFlag n (mO T↓ T) = (mO' T↓ T)) by (apply down_clos_min).
                 rewrite Heq2 in H1. exact H1.
    + intros C mL x Hml H.
      destruct H as (mO & mI & γS & γInner & r0 & M0 & Hn & HInner & HLower & Hnlower & Hd & HC & Hbody).
      rewrite HC. cbn. set (mO' := Nat.min mO n).
      exists mO', mI, (down_env_until γS mO' (min_le mO n)), γInner, r0, M0.
      exists (min_le_b mO n), (Nat.le_trans mO' mO mI (min_le_a mO n) HInner), (le_min mO n mL HLower Hml), Hnlower.
      split.
      * rewrite <- Hd. rewrite (@down_env_comp_fun attr mI γInner mO' mO HInner (min_le mO n)). apply down_env_until_irrel.
      * split.
        -- reflexivity.
        -- intros W HWA.
           assert (Heq : down_value mO (@down_clos ValFlag mO' W) = down_value mO' W) by (apply down_clos_le; apply min_le_a).
           assert (HWA0 : LR_maybe A1 (@down_clos ValFlag mO' W) mL x) by (apply (LRprops_Dm Lazy A1 W mL x mO' (le_min mO n mL HLower Hml)); apply (CM1 W mL x Hml HWA)).
           destruct (Hbody (@down_clos ValFlag mO' W) HWA0) as [E1 E2]. split.
           ++ intro bnf. pose proof (E1 (proj1 (non_func_down_ty B1 n HD) bnf)) as h. rewrite Heq in h. exact h.
           ++ intro nb. destruct (E2 (fun h => nb (proj2 (non_func_down_ty B1 n HD) h))) as [f | (T & ev & lr)].
              ** left. rewrite Heq in f. exact f.
              ** right. exists T. split.
                 --- rewrite Heq in ev. exact ev.
                 --- assert (H1 : LR_no (down_ty_until B1 n HD) (@down_clos CompFlag n (mO T↓ T)) mL x) by (apply (DNB (mO T↓ T) mL x Hml); exact lr).
                     assert (Heq2 : @down_clos CompFlag n (mO T↓ T) = (mO' T↓ T)) by (apply down_clos_min).
                     rewrite Heq2 in H1. exact H1.
    + intros C mL x Hml H.
      destruct H as (mO & mI & γS & γInner & r0 & M0 & Hn & HInner & HLower & Hnlower & Hd & HC & Hbody).
      exists mO, mI, γS, γInner, r0, M0, (Nat.le_trans mO n N Hn HD), HInner, HLower, Hnlower.
      split.
      * exact Hd.
      * split; [exact HC |].
        intros W HWA.
        assert (Heq : down_value mO (@down_clos ValFlag n W) = down_value mO W).
        { change (@down_clos ValFlag mO (@down_clos ValFlag n W) = @down_clos ValFlag mO W).
          rewrite down_clos_min. f_equal. apply Nat.min_r. exact Hn. }
        assert (HWA0 : LR_maybe (down_ty_until A1 n HD) (@down_clos ValFlag n W) mL x) by (apply (DM1 W mL x Hml); exact HWA).
        destruct (Hbody (@down_clos ValFlag n W) HWA0) as [f | (T & ev & lr)].
        -- left. rewrite Heq in f. exact f.
        -- right. exists T. split. ++ rewrite Heq in ev. exact ev. ++ exact (CMB (mO T↓ T) mL x Hml lr).
    + intros C mL x Hml H.
      destruct H as (mO & mI & γS & γInner & r0 & M0 & Hn & HInner & HLower & Hnlower & Hd & HC & Hbody).
      exists mO, mI, γS, γInner, r0, M0, (Nat.le_trans mO n N Hn HD), HInner, HLower, Hnlower.
      split.
      * exact Hd.
      * split; [exact HC |].
        intros W HWA.
        assert (Heq : down_value mO (@down_clos ValFlag n W) = down_value mO W).
        { change (@down_clos ValFlag mO (@down_clos ValFlag n W) = @down_clos ValFlag mO W).
          rewrite down_clos_min. f_equal. apply Nat.min_r. exact Hn. }
        assert (HWA0 : LR_maybe (down_ty_until A1 n HD) (@down_clos ValFlag n W) mL x) by (apply (DM1 W mL x Hml); exact HWA).
        destruct (Hbody (@down_clos ValFlag n W) HWA0) as [E1 E2]. split.
        -- intro bnf. pose proof (E1 (proj2 (non_func_down_ty B1 n HD) bnf)) as h. rewrite Heq in h. exact h.
        -- intro nb. destruct (E2 (fun h => nb (proj1 (non_func_down_ty B1 n HD) h))) as [f | (T & ev & lr)].
           ++ left. rewrite Heq in f. exact f.
           ++ right. exists T. split.
              ** rewrite Heq in ev. exact ev.
              ** exact (CNB (mO T↓ T) mL x Hml lr).
  - destruct IHA1 as [DM1 [DN1 [CM1 CN1]]]. unfold DRprops; cbn. repeat split.
    + intros C mL x Hml H. destruct H as (W & HC & H1). cbn.
      exists (down_clos n W). split; [rewrite HC; reflexivity | exact (DM1 W mL x Hml H1)].
    + intros C mL x Hml H. cbn in H. destruct H.
    + intros C mL x Hml H. destruct H as (W & HC & H1). cbn.
      exists W. split; [exact HC | exact (CM1 W mL x Hml H1)].
    + intros C mL x Hml H. cbn in H. destruct H.
Qed.

(* ===== eq_up_to_attrs algebra ===== *)
Lemma eq_clos_sym : forall k (C C' : Clos k), eq_up_to_attrs C C' -> eq_up_to_attrs C' C.
Proof. intros k C C' H. induction H; constructor; auto. Qed.

Lemma eq_clos_trans : forall k (C1 C2 C3 : Clos k),
  eq_up_to_attrs C1 C2 -> eq_up_to_attrs C2 C3 -> eq_up_to_attrs C1 C3.
Proof.
  intros k C1 C2 C3 H12. revert C3.
  induction H12 as
    [ | | n m g g' r r' M Hr IHr | W1 W2 W1' W2' HW1 IH1 HW2 IH2
    | W W' HW IHw | W W' HW IHw | W W' HW IHw | n m g g' r r' M Hr IHr ];
    intros C3 H23.
  - dependent destruction H23. constructor.
  - dependent destruction H23. constructor.
  - dependent destruction H23. constructor. intro i. eauto.
  - dependent destruction H23. constructor; eauto.
  - dependent destruction H23. constructor; eauto.
  - dependent destruction H23. constructor; eauto.
  - dependent destruction H23. constructor; eauto.
  - dependent destruction H23. constructor. intro i. eauto.
Qed.

Lemma eq_env_sym : forall {n} (ρ ρ' : env n), eq_env_up_to_attrs ρ ρ' -> eq_env_up_to_attrs ρ' ρ.
Proof. intros n ρ ρ' H i. apply eq_clos_sym. apply H. Qed.

Lemma eq_env_trans : forall {n} (ρ1 ρ2 ρ3 : env n),
  eq_env_up_to_attrs ρ1 ρ2 -> eq_env_up_to_attrs ρ2 ρ3 -> eq_env_up_to_attrs ρ1 ρ3.
Proof. intros n ρ1 ρ2 ρ3 H12 H23 i. eapply eq_clos_trans; [apply H12 | apply H23]. Qed.

Lemma eq_env_cons : forall {n} (W W' : ClosValue) (ρ ρ' : env n),
  eq_up_to_attrs W W' -> eq_env_up_to_attrs ρ ρ' -> eq_env_up_to_attrs (W .: ρ) (W' .: ρ').
Proof. intros n W W' ρ ρ' HW Hρ [j|]; cbn; auto. Qed.

Lemma eq_absent_l : forall (C : ClosValue), eq_up_to_attrs C Absent -> C = Absent.
Proof. intros C H. dependent destruction H. reflexivity. Qed.

Lemma eq_absent_r : forall (C : ClosValue), eq_up_to_attrs Absent C -> C = Absent.
Proof. intros C H. dependent destruction H. reflexivity. Qed.

(* ===== fin_eqb and env_set ===== *)
Lemma fin_eqb_refl : forall {n} (i : fin n), fin_eqb i i = true.
Proof.
  induction n as [|n IH]; intros i.
  - destruct i.
  - destruct i as [i|]; simpl.
    + destruct (fin_eqb i i) eqn:E.
      * reflexivity.
      * exfalso. specialize (IH i). rewrite E in IH. discriminate IH.
    + reflexivity.
Qed.

Lemma fin_eqb_eq : forall {n} (i j : fin n), fin_eqb i j = true -> i = j.
Proof.
  induction n as [|n IH]; intros i j H.
  - destruct i.
  - destruct i as [i|]; destruct j as [j|]; simpl in H.
    + f_equal. apply IH. destruct (fin_eqb i j) eqn:E in H |- *.
      * reflexivity.
      * exfalso. cbn in H. discriminate H.
    + discriminate H.
    + discriminate H.
    + reflexivity.
Qed.

Lemma fin_eqb_neq : forall {n} (i j : fin n), fin_eqb i j = false -> i <> j.
Proof. intros n i j H E. subst j. rewrite fin_eqb_refl in H. discriminate. Qed.

Lemma env_set_self : forall {n A} (ϕ : fin n -> A) i a, (ϕ <- a @ i) i = a.
Proof. intros. unfold env_set. rewrite fin_eqb_refl. reflexivity. Qed.

Lemma env_set_other : forall {n A} (ϕ : fin n -> A) i j a, i <> j -> (ϕ <- a @ i) j = ϕ j.
Proof.
  intros. unfold env_set. destruct (fin_eqb i j) eqn:E.
  - exfalso. apply H. apply fin_eqb_eq. exact E.
  - reflexivity.
Qed.

Lemma down_env_set_strict : forall {n} (ϕ : attrs n) i mL (H : mL <= n) x,
  up_fin_until n H x = i ->
  down_env_until (ϕ <- Strict @ i) mL H x = Strict.
Proof.
  intros. rewrite down_env_until_up. rewrite H0. unfold env_set. rewrite fin_eqb_refl. reflexivity.
Qed.

Definition not_absent {k} (C : Clos k) : Prop :=
  match k as k0 return Clos k0 -> Prop with
  | ValFlag => fun C => C <> Absent
  | CompFlag => fun _ => True
  end C.

Lemma LR_maybe_not_absent_gen : forall {n k} (A : Ty n k) (C : Clos k) mL x,
  LR_maybe A C mL x -> not_absent C.
Proof.
  intros n k A. induction A as [ | g B IHB | A1 IH1 A2 IH2 | A1 IH1 A2 IH2 | q A1 IH1 B1 IHB1 | A1 IH1 ]; cbn; intros C mL x H.
  - subst C. discriminate.
  - destruct H as (mO & mI & gS & gI & r & M & HI & Hn & HL & Hnl & Hd1 & Hd2 & HC & HLRM). subst C. discriminate.
  - destruct H as (W1 & W2 & HC & _). subst C. discriminate.
  - destruct H as (W & [ (HC & _) | (HC & _) ]); subst C; discriminate.
  - exact I.
  - exact I.
Qed.

Lemma LR_maybe_not_absent : forall {n} (A : Ty n ValFlag) (C : Clos ValFlag) mL x,
  LR_maybe A C mL x -> C <> Absent.
Proof. intros n A C mL x H. change (not_absent C). apply (@LR_maybe_not_absent_gen n ValFlag A C mL x H). Qed.


Lemma EvalVal_det_gen : forall {n} (γ1 : attrs n) (ρ1 : env n) V W1,
  EvalVal γ1 ρ1 V W1 ->
  forall (γ2 : attrs n) (ρ2 : env n) W2,
    eq_env_up_to_attrs ρ1 ρ2 -> EvalVal γ2 ρ2 V W2 -> eq_up_to_attrs W1 W2.
Proof.
  intros n γ1 ρ1 V W1 H1. induction H1 as
    [ i W Hdef Hγ Hneq | | M g' Hγ
    | g1 g2 V1 V2 W1a W2a ev1 IH1 ev2 IH2 Hadd
    | V0 W0 ev0 IH0 | V0 W0 ev0 IH0 ];
    intros γ2 ρ2 W2 Heq H2.
  - inversion H2; subst. exact (Heq _).
  - inversion H2; subst. constructor.
  - inversion H2; subst. constructor. exact Heq.
  - inversion H2; subst. constructor; eauto.
  - inversion H2; subst. constructor; eauto.
  - inversion H2; subst. constructor; eauto.
Qed.

Lemma eq_clos_return_inv : forall (W1 W2 : Clos ValFlag),
  eq_up_to_attrs (Return W1) (Return W2) -> eq_up_to_attrs W1 W2.
Proof. intros W1 W2 H. dependent destruction H. exact H. Qed.

Lemma eq_clos_pair_inv : forall (W1 W2 W1' W2' : ClosValue),
  eq_up_to_attrs (Pair W1 W2) (Pair W1' W2') ->
  eq_up_to_attrs W1 W1' /\ eq_up_to_attrs W2 W2'.
Proof. intros. dependent destruction H. split; assumption. Qed.

Lemma eq_clos_inl_inv : forall (W W' : ClosValue),
  eq_up_to_attrs (Inl W) (Inl W') -> eq_up_to_attrs W W'.
Proof. intros. dependent destruction H. exact H. Qed.

Lemma eq_clos_inr_inv : forall (W W' : ClosValue),
  eq_up_to_attrs (Inr W) (Inr W') -> eq_up_to_attrs W W'.
Proof. intros. dependent destruction H. exact H. Qed.

Lemma eq_clos_inl_inr_false : forall (W W' : ClosValue), eq_up_to_attrs (Inl W) (Inr W') -> False.
Proof. intros. dependent destruction H. Qed.

Lemma eq_clos_inr_inl_false : forall (W W' : ClosValue), eq_up_to_attrs (Inr W) (Inl W') -> False.
Proof. intros. dependent destruction H. Qed.



Lemma EvalComp_det_gen : forall {n} (γ1 : attrs n) (ρ1 : env n) M T1,
  EvalComp γ1 ρ1 M T1 ->
  forall (γ2 : attrs n) (ρ2 : env n) T2,
    eq_env_up_to_attrs ρ1 ρ2 -> EvalComp γ2 ρ2 M T2 -> eq_up_to_attrs T1 T2.
Proof.
  intros n γ1 ρ1 M T1 H1. induction H1 as
    [ nf gf rf M0
    | nf gf rf na ma qa g1a g2a gpa gUpa Hna M1 M1' V1 Ta Ta' Wa rpa evM IHm evV HdH evBody IHb Hadd HTeq
    | nf gf rf q1 q2 ga1 ga2 Va N W1a W2a Ta Ta' evV evN IHN Hadd HTeq
    | nf gf rf Va Wa evV
    | nf gf rf ga1 ga2 qa M1 Na Wa Ta Ta' evM IHm evN IHN Hadd HTeq
    | nf gf rf mI mO g2pp ga1 ga2 g2p Va M1 Ta Ta' rpa Hn HInner evV evM IHM Hd1 Hd2 Hadd HTeq
    | nf gf rf ga1 ga2 Va Na Ta evV evN IHN Hadd
    | nf gf rf ga1 ga2 qa Va M1 M2a Wa Ta Ta' evV evM IHM Hadd HTeq
    | nf gf rf ga1 ga2 qa Va M1 M2a Wa Ta Ta' evV evM IHM Hadd HTeq
    | nf gf rf M1 gp B evM IHM Hle ];
    intros γe ρe Te Heqe H2e.
  - inversion H2e; subst; clear H2e. constructor. exact Heqe.
  - inversion H2e; subst; clear H2e.
    pose proof (IHm γ1 ρe _ Heqe H2) as Hclos.
    dependent destruction Hclos.
    pose proof (EvalVal_det_gen g2a rf V1 Wa evV γ2 ρe W Heqe H3) as Hval.
    assert (Henv : eq_env_up_to_attrs ((n' W↓ Wa) .: rpa) ((n' W↓ W) .: ρ')).
    { apply eq_env_cons.
      - apply eq_down_clos. exact Hval.
      - intros i. apply H0. }
    pose proof (IHb (q .: γUp) ((n' W↓ W) .: ρ') T' Henv H5) as Hbody.
    apply eq_down_clos. exact Hbody.
  - inversion H2e; subst; clear H2e.
    pose proof (EvalVal_det_gen ga1 rf Va (Pair W1a W2a) evV γ1 ρe (Pair W1 W2) Heqe H1) as Hval.
    apply eq_clos_pair_inv in Hval. destruct Hval as [HW1 HW2].
    assert (Henv : eq_env_up_to_attrs (W1a .: (W2a .: rf)) (W1 .: (W2 .: ρe)))
      by (apply eq_env_cons; [exact HW1 | apply eq_env_cons; [exact HW2 | exact Heqe]]).
    pose proof (IHN (q0 .: (q3 .: γ2)) (W1 .: (W2 .: ρe)) T' Henv H2) as Hbody.
    apply eq_down_clos. exact Hbody.
  - inversion H2e; subst; clear H2e.
    apply Eq_Return. exact (EvalVal_det_gen gf rf Va Wa evV γe ρe W Heqe H0).
  - inversion H2e; subst; clear H2e.
    pose proof (IHm γ1 ρe (Return W) Heqe H1) as Hret.
    apply eq_clos_return_inv in Hret.
    assert (Henv : eq_env_up_to_attrs (Wa .: rf) (W .: ρe)) by (apply eq_env_cons; [exact Hret | exact Heqe]).
    pose proof (IHN (q .: γ2) (W .: ρe) T' Henv H2) as Hbody.
    apply eq_down_clos. exact Hbody.
  - inversion H2e; subst; clear H2e.
    pose proof (EvalVal_det_gen ga1 rf Va _ evV γ1 ρe _ Heqe H0) as Hth.
    dependent destruction Hth.
    pose proof (IHM γ2' ρ' T' H H1) as Hbody.
    apply eq_down_clos. exact Hbody.
  - inversion H2e; subst; clear H2e.
    exact (IHN γ2 ρe Te Heqe H2).
  - inversion H2e; subst; clear H2e.
    + pose proof (EvalVal_det_gen ga1 rf Va (Inl Wa) evV γ1 ρe (Inl W) Heqe H2) as Hval.
      apply eq_clos_inl_inv in Hval.
      assert (Henv : eq_env_up_to_attrs (Wa .: rf) (W .: ρe)) by (apply eq_env_cons; [exact Hval | exact Heqe]).
      pose proof (IHM (q .: γ2) (W .: ρe) T' Henv H3) as Hbody.
      apply eq_down_clos. exact Hbody.
    + exfalso.
      exact (eq_clos_inl_inr_false _ _ (EvalVal_det_gen ga1 rf Va (Inl Wa) evV γ1 ρe (Inr W) Heqe H2)).
  - inversion H2e; subst; clear H2e.
    + exfalso.
      exact (eq_clos_inr_inl_false _ _ (EvalVal_det_gen ga1 rf Va (Inr Wa) evV γ1 ρe (Inl W) Heqe H2)).
    + pose proof (EvalVal_det_gen ga1 rf Va (Inr Wa) evV γ1 ρe (Inr W) Heqe H2) as Hval.
      apply eq_clos_inr_inv in Hval.
      assert (Henv : eq_env_up_to_attrs (Wa .: rf) (W .: ρe)) by (apply eq_env_cons; [exact Hval | exact Heqe]).
      pose proof (IHM (q .: γ2) (W .: ρe) T' Henv H3) as Hbody.
      apply eq_down_clos. exact Hbody.
  - inversion H2e; subst; clear H2e.
    exact (IHM γ' ρe Te Heqe H0).
Qed.

(* ===== small helpers ===== *)
Lemma non_func_CF : forall {n} (A : Ty n ValFlag), non_func (CF A).
Proof. intros n A q A' B' E. discriminate E. Qed.



Lemma not_non_func_CAbs : forall {n} q (A : Ty n ValFlag) (B : Ty n CompFlag),
  ~ non_func (CAbs q A B).
Proof. intros n q A B H. unfold non_func in H. exact (H q A B eq_refl). Qed.

Lemma attr_add_nstrict_l : forall a b, a C+ b <> Strict -> a <> Strict.
Proof. intros a b H E. apply H. rewrite E. destruct b; reflexivity. Qed.

Lemma attr_add_nstrict_r : forall a b, a C+ b <> Strict -> b <> Strict.
Proof. intros a b H E. apply H. rewrite E. destruct a; reflexivity. Qed.

Lemma down_env_add_strict : forall {n} (γ1 γ2 : attrs n) mL (H : mL <= n) x,
  down_env_until (γ1 γ+ γ2) mL H x = Strict ->
  down_env_until γ1 mL H x = Strict \/ down_env_until γ2 mL H x = Strict.
Proof.
  intros n γ1 γ2 mL H x Hs. rewrite down_env_add in Hs.
  apply attr_add_strict_l. exact Hs.
Qed.

Lemma down_env_add_nstrict_l : forall {n} (γ1 γ2 : attrs n) mL (H : mL <= n) x,
  down_env_until (γ1 γ+ γ2) mL H x <> Strict ->
  down_env_until γ1 mL H x <> Strict.
Proof.
  intros n γ1 γ2 mL H x Hns E. apply Hns. rewrite down_env_add, E.
  destruct (down_env_until γ2 mL H x); reflexivity.
Qed.

Lemma down_env_add_nstrict_r : forall {n} (γ1 γ2 : attrs n) mL (H : mL <= n) x,
  down_env_until (γ1 γ+ γ2) mL H x <> Strict ->
  down_env_until γ2 mL H x <> Strict.
Proof.
  intros n γ1 γ2 mL H x Hns E. apply Hns. rewrite down_env_add, E.
  destruct (down_env_until γ1 mL H x); reflexivity.
Qed.

Lemma down_env_cons_strict : forall {n} (γ : attrs n) q mL (H : mL <= n) (H' : mL <= S n) x,
  down_env_until (q .: γ) mL H' x = down_env_until γ mL H x.
Proof. intros. apply down_env_cons. Qed.

(* ===== cond: context extension ===== *)
Lemma rho_not_ok_cons : forall {n} (γ : attrs n) (ρ : env n) (Γ : context n)
  mL x (H : mL <= n) (H' : mL <= S n) q (A : ValTy n) (W : ClosValue),
  ρ_not_ok γ ρ Γ mL x H ->
  LR_maybe A W mL x ->
  ρ_not_ok (q .: γ) (W .: ρ) (ctx_insert A Γ) mL x H'.
Proof.
  intros n γ ρ Γ mL x H H' q A W [Hs [Ha Hc]] HW. unfold ρ_not_ok. split; [| split].
  - rewrite (@down_env_cons attr n q γ mL H H' x). exact Hs.
  - rewrite (@down_env_cons ClosValue n W ρ mL H H' x). exact Ha.
  - intros [j'|] Hj.
    + cbn. apply LRprops_Um. apply Hc.
      intro E. apply Hj. rewrite (@up_fin_until_succ n mL H H' x). rewrite E. reflexivity.
    + cbn. apply LRprops_Um. exact HW.
Qed.

Lemma rho_maybe_ok_cons : forall {n} (γ : attrs n) (ρ : env n) (Γ : context n)
  mL x (H : mL <= n) (H' : mL <= S n) q (A : ValTy n) (W : ClosValue),
  ρ_maybe_ok γ ρ Γ mL x H ->
  LR_maybe A W mL x ->
  ρ_maybe_ok (q .: γ) (W .: ρ) (ctx_insert A Γ) mL x H'.
Proof.
  intros n γ ρ Γ mL x H H' q A W [Hs [Ha Hc]] HW. unfold ρ_maybe_ok. split; [| split].
  - rewrite (@down_env_cons attr n q γ mL H H' x). exact Hs.
  - rewrite (@down_env_cons ClosValue n W ρ mL H H' x). exact Ha.
  - intros [j'|] Hj.
    + cbn. apply LRprops_Um. apply Hc.
      intro E. apply Hj. rewrite (@up_fin_until_succ n mL H H' x). rewrite E. reflexivity.
    + cbn. apply LRprops_Um. exact HW.
Qed.

(* ===== cond: double context extension (for split) ===== *)
Lemma up_fin_until_ss : forall {n} m (H : m <= n) (H'' : m <= S (S n)) (i : fin m),
  @up_fin_until m (S (S n)) H'' i = Some (Some (@up_fin_until m n H i)).
Proof.
  intros n m H H'' i.
  set (H' := Nat.le_trans m n (S n) H (le_succ_r n)).
  rewrite (@up_fin_until_succ (S n) m H' H'' i).
  rewrite (@up_fin_until_succ n m H H' i). reflexivity.
Qed.

Lemma rho_not_ok_double : forall {n} (γ : attrs n) (ρ : env n) (Γ : context n)
  mL x (H : mL <= n) (H'' : mL <= S (S n)) q1 q2
  (A1 A2 : Ty n ValFlag) (W1 W2 : ClosValue),
  ρ_not_ok γ ρ Γ mL x H ->
  LR_maybe A1 W1 mL x -> LR_maybe A2 W2 mL x ->
  ρ_not_ok (q1 .: (q2 .: γ)) (W1 .: (W2 .: ρ))
    (ctx_insert (Lazy A↑ A1) (ctx_insert A2 Γ)) mL x H''.
Proof.
  intros n γ ρ Γ mL x H H'' q1 q2 A1 A2 W1 W2 [Hs [Ha Hc]] HW1 HW2.
  unfold ρ_not_ok. split; [| split].
  - set (Hmid := Nat.le_trans mL n (S n) H (le_succ_r n)).
    rewrite (@down_env_cons attr (S n) q1 (q2 .: γ) mL Hmid H'' x).
    rewrite (@down_env_cons attr n q2 γ mL H Hmid x). exact Hs.
  - set (Hmid := Nat.le_trans mL n (S n) H (le_succ_r n)).
    rewrite (@down_env_cons ClosValue (S n) W1 (W2 .: ρ) mL Hmid H'' x).
    rewrite (@down_env_cons ClosValue n W2 ρ mL H Hmid x). exact Ha.
  - intros [ [j'|] | ] Hj.
    + cbn. apply LRprops_Um. apply LRprops_Um. apply Hc.
      intro E. apply Hj. rewrite (@up_fin_until_ss n mL H H'' x). rewrite E. reflexivity.
    + cbn. apply LRprops_Um. apply LRprops_Um. exact HW2.
    + cbn. apply LRprops_Um. apply LRprops_Um. exact HW1.
Qed.

Lemma rho_maybe_ok_double : forall {n} (γ : attrs n) (ρ : env n) (Γ : context n)
  mL x (H : mL <= n) (H'' : mL <= S (S n)) q1 q2
  (A1 A2 : Ty n ValFlag) (W1 W2 : ClosValue),
  ρ_maybe_ok γ ρ Γ mL x H ->
  LR_maybe A1 W1 mL x -> LR_maybe A2 W2 mL x ->
  ρ_maybe_ok (q1 .: (q2 .: γ)) (W1 .: (W2 .: ρ))
    (ctx_insert (Lazy A↑ A1) (ctx_insert A2 Γ)) mL x H''.
Proof.
  intros n γ ρ Γ mL x H H'' q1 q2 A1 A2 W1 W2 [Hs [Ha Hc]] HW1 HW2.
  unfold ρ_maybe_ok. split; [| split].
  - set (Hmid := Nat.le_trans mL n (S n) H (le_succ_r n)).
    rewrite (@down_env_cons attr (S n) q1 (q2 .: γ) mL Hmid H'' x).
    rewrite (@down_env_cons attr n q2 γ mL H Hmid x). exact Hs.
  - set (Hmid := Nat.le_trans mL n (S n) H (le_succ_r n)).
    rewrite (@down_env_cons ClosValue (S n) W1 (W2 .: ρ) mL Hmid H'' x).
    rewrite (@down_env_cons ClosValue n W2 ρ mL H Hmid x). exact Ha.
  - intros [ [j'|] | ] Hj.
    + cbn. apply LRprops_Um. apply LRprops_Um. apply Hc.
      intro E. apply Hj. rewrite (@up_fin_until_ss n mL H H'' x). rewrite E. reflexivity.
    + cbn. apply LRprops_Um. apply LRprops_Um. exact HW2.
    + cbn. apply LRprops_Um. apply LRprops_Um. exact HW1.
Qed.

Lemma down_env_to_common : forall {nA mO mL} (γA : attrs nA) (γS : attrs mO)
  (HInner : mO <= nA) (HAl : mL <= nA) (Hml : mL <= mO) x,
  down_env_until γA mO HInner = γS ->
  down_env_until γA mL HAl x = down_env_until γS mL Hml x.
Proof.
  intros. transitivity (down_env_until γA mL (Nat.le_trans mL mO nA Hml HInner) x).
  - rewrite (down_env_until_irrel γA mL HAl (Nat.le_trans mL mO nA Hml HInner)). reflexivity.
  - rewrite <- (@down_env_comp_fun attr nA γA mL mO HInner Hml). rewrite H. reflexivity.
Qed.

Lemma LR_thunk_inv : forall {n} (g : attrs n) (B : Ty n CompFlag) (C : Clos ValFlag) mL x,
  LR_maybe (VThunk g B) C mL x ->
  exists mO mI gS gI ρ M (HInner : mO <= mI) (Hn : mO <= n)
    (HLower : mL <= mO) (Hnlower : mL <= mI),
    down_env_until g mO Hn = gS /\
    down_env_until gI mO HInner = gS /\
    C = Thunk mO mI gS ρ M /\
    LRM B LR_maybe LR_no mI gI mO mL x Hnlower ρ M.
Proof. intros. unfold LR_maybe in H. cbn in H. exact H. Qed.

Lemma LR_abs_maybe_inv : forall {n} q (A : Ty n ValFlag) (B : Ty n CompFlag) (C : Clos CompFlag) mL x,
  LR_maybe (CAbs q A B) C mL x ->
  exists mO mI gS gI ρ M (Hn : mO <= n) (HInner : mO <= mI)
    (HLower : mL <= mO) (Hnlower : mL <= mI),
    down_env_until gI mO HInner = gS /\
    C = Closure mO mI gS ρ M /\
    (forall W, LR_maybe A W mL x ->
       EvalCompFail ((mO W↓ W) .: ρ) M \/
       exists T, EvalComp (q .: gI) ((mO W↓ W) .: ρ) M T /\
         LR_maybe B (mO T↓ T) mL x).
Proof. intros. unfold LR_maybe in H. cbn in H. exact H. Qed.

Lemma LR_abs_no_inv : forall {n} q (A : Ty n ValFlag) (B : Ty n CompFlag) (C : Clos CompFlag) mL x,
  LR_no (CAbs q A B) C mL x ->
  exists mO mI gS gI ρ M (Hn : mO <= n) (HInner : mO <= mI)
    (HLower : mL <= mO) (Hnlower : mL <= mI),
    down_env_until gI mO HInner = gS /\
    C = Closure mO mI gS ρ M /\
    (forall W, LR_maybe A W mL x ->
       (non_func B -> EvalCompFail ((mO W↓ W) .: ρ) M) /\
       (~ non_func B -> EvalCompFail ((mO W↓ W) .: ρ) M \/
         exists T, EvalComp (q .: gI) ((mO W↓ W) .: ρ) M T /\
           LR_no B (mO T↓ T) mL x)).
Proof. intros. unfold LR_no in H. cbn in H. exact H. Qed.

Lemma LR_no_maybe : forall {n} (B : Ty n CompFlag) C mL x, LR_no B C mL x -> LR_maybe B C mL x.
Proof.
  intros n B. induction B as [| | | | q A IHA B IHB | A IHA]; intros C mL x H; cbn in *;
    try (destruct H); try (destruct H as (mO & mI & gS & gI & r & M & Hn & HI & HL & Hnl & Hd & HC & Hbody)).
  destruct H as (mO & mI & gS & gI & r & Mc & Hn & HInner & HLower & Hnlower & Hbody).
  destruct Hbody as [HC Hbody'].
  exists x0, mO, mI, gS, gI, r, Mc, Hn, HInner, HLower.
  split; [exact Hnlower | split; [exact HC |]].
  intros W HWA.
  destruct (Hbody' W HWA) as [Hnf Hnnf].
  dependent destruction B.
  - destruct (Hnnf (not_non_func_CAbs q0 B1 B2)) as [Hf | (T & ev & lr)].
    + left. exact Hf.
    + right. exists T. split; [exact ev | exact (IHB (x0 T↓ T) mL x lr)].
  - left. apply Hnf. apply non_func_CF.
Qed.

Lemma EvalCompFail_sub_m : forall {n} ρ (M : Comp n), EvalCompFail ρ M -> EvalCompFail ρ (cSub M).
Proof.
  intros n ρ M F γe Te ρe Heqe H2. inversion H2; subst; clear H2.
  match goal with Hpre : EvalComp ?g ρe M ?t |- False => exact (F g t ρe Heqe Hpre) end.
Qed.

Lemma EvalCompFail_seq_v : forall {n} ρ (V : Val n) M, EvalValFail ρ V -> EvalCompFail ρ (cSeq V M).
Proof.
  intros n ρ V M F γe Te ρe Heqe H2. inversion H2; subst; clear H2.
  match goal with Hpre : EvalVal ?g ρe V Unit |- False => exact (F g Unit ρe Heqe Hpre) end.
Qed.

Lemma EvalCompFail_seq_m : forall {n} ρ (V : Val n) M, EvalCompFail ρ M -> EvalCompFail ρ (cSeq V M).
Proof.
  intros n ρ V M F γe Te ρe Heqe H2. inversion H2; subst; clear H2.
  match goal with Hpre : EvalComp ?g ρe M ?t |- False => exact (F g t ρe Heqe Hpre) end.
Qed.

Lemma EvalCompFail_force_v : forall {n} ρ (V : Val n), EvalValFail ρ V -> EvalCompFail ρ (cForce V).
Proof.
  intros n ρ V F γe Te ρe Heqe H2. inversion H2; subst; clear H2.
  match goal with Hpre : EvalVal ?g ρe V (Thunk ?mO ?mI ?gS ?r ?M) |- False =>
    exact (F g (Thunk mO mI gS r M) ρe Heqe Hpre) end.
Qed.

Lemma EvalCompFail_app_m : forall {n} ρ (M : Comp n) V, EvalCompFail ρ M -> EvalCompFail ρ (cApp M V).
Proof.
  intros n ρ M V F γe Te ρe Heqe H2. inversion H2; subst; clear H2.
  match goal with Hpre : EvalComp ?g ρe M (Closure ?a ?b ?c ?d ?e) |- False =>
    exact (F g (Closure a b c d e) ρe Heqe Hpre) end.
Qed.

Lemma EvalCompFail_app_v : forall {n} ρ (M : Comp n) V, EvalValFail ρ V -> EvalCompFail ρ (cApp M V).
Proof.
  intros n ρ M V F γe Te ρe Heqe H2. inversion H2; subst; clear H2.
  match goal with Hpre : EvalVal ?g ρe V ?w |- False => exact (F g w ρe Heqe Hpre) end.
Qed.

Lemma EvalCompFail_split_v : forall {n} ρ (V : Val n) N, EvalValFail ρ V -> EvalCompFail ρ (cSplit V N).
Proof.
  intros n ρ V N F γe Te ρe Heqe H2. inversion H2; subst; clear H2.
  match goal with Hpre : EvalVal ?g ρe V (Pair ?w1 ?w2) |- False =>
    exact (F g (Pair w1 w2) ρe Heqe Hpre) end.
Qed.

Lemma EvalCompFail_case_v : forall {n} ρ (V : Val n) M1 M2, EvalValFail ρ V -> EvalCompFail ρ (cCase V M1 M2).
Proof.
  intros n ρ V M1 M2 F γe Te ρe Heqe H2. inversion H2; subst; clear H2.
  match goal with Hpre : EvalVal ?g ρe V (Inl ?w) |- False => exact (F g (Inl w) ρe Heqe Hpre) end.
  match goal with Hpre : EvalVal ?g ρe V (Inr ?w) |- False => exact (F g (Inr w) ρe Heqe Hpre) end.
Qed.

Lemma eq_env_double : forall {n} (W1 W1' W2 W2' : ClosValue) (ρ ρ' : env n),
  eq_up_to_attrs W1 W1' -> eq_up_to_attrs W2 W2' -> eq_env_up_to_attrs ρ ρ' ->
  eq_env_up_to_attrs (W1 .: (W2 .: ρ)) (W1' .: (W2' .: ρ')).
Proof. intros. apply eq_env_cons; [assumption | apply eq_env_cons; assumption]. Qed.

Lemma EvalCompFail_app_elim : forall {n} (γ1 γ2 : attrs n) (ρ : env n) (M : Comp n) (q : attr) (V : Val n)
  mO mI (gS : attrs mO) (gI : attrs mI) (rcap : env mI) (Mbody : Comp (S mI))
  (W0 : ClosValue) (HInner : mO <= mI),
  EvalComp γ1 ρ M (Closure mO mI gS rcap Mbody) ->
  EvalVal γ2 ρ V W0 ->
  EvalCompFail ((@down_clos ValFlag mO W0) .: rcap) Mbody ->
  EvalCompFail ρ (cApp M V).
Proof.
  intros n γ1 γ2 ρ M q V mO mI gS gI rcap Mbody W0 HInner evM evW0 HbodyFail γe Te ρe Heqe H2.
  inversion H2; subst; clear H2.
  pose proof (EvalComp_det_gen γ1 ρ M (Closure mO mI gS rcap Mbody) evM γ0 ρe (Closure n' m (down_env_until γUp n' H) ρ' M') Heqe H3) as Hcl.
  dependent destruction Hcl.
  pose proof (EvalVal_det_gen γ2 ρ V W0 evW0 γ3 ρe W Heqe H4) as Hwv.
  exact (HbodyFail (q0 .: γUp) T' ((@down_clos ValFlag n' W) .: ρ')
          (eq_env_cons (@down_clos ValFlag n' W0) (@down_clos ValFlag n' W) rcap ρ'
             (eq_down_clos n' W0 W Hwv) H0) H6).
Qed.

Definition non_func_dec {n k} (B : Ty n k) : Prop :=
  match k as k0 return Ty n k0 -> Prop with
  | CompFlag => fun B0 => non_func B0 \/ ~ non_func B0
  | ValFlag => fun _ => True
  end B.

Lemma non_func_or_not : forall {n k} (B : Ty n k), non_func_dec B.
Proof.
  intros n k B. induction B; cbn.
  - exact I. - exact I. - exact I. - exact I.
  - right. apply not_non_func_CAbs.
  - left. apply non_func_CF.
Qed.

(* ===== fundamental semantic typing ===== *)
Lemma Sem_typing : forall n (γ : attrs n) (Γ : context n),
  (forall V A, VWt γ Γ V A -> SemVWt γ Γ V A) /\
  (forall M B, CWt γ Γ M B -> SemCWt γ Γ M B).
Proof.
  intros n γ Γ.
  apply (Wt_mutual
    (fun n γ Γ V A _ => SemVWt γ Γ V A)
    (fun n γ Γ M B _ => SemCWt γ Γ M B)).
  - (* T_Var *)
    intros n0 γ0 Γ0 i A e e0. subst A. subst γ0.
    intros ρ mL x Hnl. unfold SemVWt. split.
    + intros [Hs [Ha Hc]]. intros γe W ρe Heqe H2.
      unfold env_set in Hs. rewrite down_env_until_up in Hs.
      rewrite down_env_until_up in Ha.
      destruct (fin_eqb i (up_fin_until n0 Hnl x)) eqn:E in Hs.
      * cbn in Hs. apply fin_eqb_eq in E. rewrite <- E in Ha.
        inversion H2; subst; clear H2.
        apply H3. apply eq_absent_r. rewrite <- Ha. exact (Heqe (up_fin_until n0 Hnl x)).
      * cbn in Hs. discriminate Hs.
    + intros [Hns [Ha Hc]].
      assert (Ei : i <> up_fin_until n0 Hnl x).
      { intro E. apply Hns. unfold env_set. rewrite down_env_until_up.
        rewrite <- E. rewrite fin_eqb_refl. reflexivity. }
      right. exists (ρ i). split.
      * apply E_Var.
        -- reflexivity.
        -- reflexivity.
        -- exact (LR_maybe_not_absent (Γ0 i) (ρ i) mL x (Hc i Ei)).
      * apply Hc. exact Ei.
  - (* T_Unit *)
    intros n0 γ0 Γ0 e. subst γ0.
    intros ρ mL x Hnl. unfold SemVWt. split.
    + intros [Hs _]. intros γe W ρe Heqe H2.
      assert (Hl : down_env_until (lazyvector : attrs n0) mL Hnl x = Lazy)
        by (rewrite down_env_until_up; reflexivity).
      rewrite Hl in Hs. discriminate Hs.
    + intros [Hns _]. right. exists Unit. split.
      * apply E_Unit. reflexivity.
      * cbn. reflexivity.
  - (* T_Thunk *)
    intros n0 γ0 Γ0 g' M B c IH e. subst γ0.
    intros ρ mL x Hnl. unfold SemVWt. split.
    + intros [Hs _]. intros γe W ρe Heqe H2.
      assert (Hl : down_env_until (lazyvector : attrs n0) mL Hnl x = Lazy)
        by (rewrite down_env_until_up; reflexivity).
      rewrite Hl in Hs. discriminate Hs.
    + intros [Hns [Ha Hc]]. right.
      exists (Thunk n0 n0 g' ρ M). split.
      * apply E_Thunk. reflexivity.
      * unfold LR_maybe. cbn.
        exists n0, n0, g', g', ρ, M, (le_n n0), (le_n n0), Hnl, Hnl.
        split; [apply down_env_self_fun | split; [apply down_env_self_fun | split; [reflexivity |]]].
        unfold LRM. split.
        -- intro Hstrict.
           destruct (IH ρ mL x Hnl) as [IHs IHm].
           destruct (IHs (conj Hstrict (conj Ha Hc))) as [Hnf Hnnf]. split.
           ++ exact Hnf.
           ++ intro nb. destruct (Hnnf nb) as [Hf | (T & ev & lr)].
              ** left. exact Hf.
              ** right. exists T. split; [exact ev |].
                 exact (LRprops_Dn Lazy B T mL x n0 Hnl lr).
        -- intro Hns'. 
           destruct (IH ρ mL x Hnl) as [IHs IHm].
           destruct (IHm (conj Hns' (conj Ha Hc))) as [Hf | (T & ev & lr)].
           ++ left. exact Hf.
           ++ right. exists T. split; [exact ev |].
              exact (LRprops_Dm Lazy B T mL x n0 Hnl lr).
  - (* T_Pair *)
    intros n0 γ0 Γ0 γ1 γ2 V1 V2 A1 A2 v1 IH1 v2 IH2 e. subst γ0.
    intros ρ mL x Hnl. unfold SemVWt. split.
    + intros [Hs [Ha Hc]]. intros γe W ρe Heqe H2.
      destruct (down_env_add_strict γ1 γ2 mL Hnl x Hs) as [Hs1 | Hs2].
      * inversion H2; subst; clear H2.
        exact (proj1 (IH1 ρ mL x Hnl) (conj Hs1 (conj Ha Hc)) γ0 W1 ρe Heqe H1).
      * inversion H2; subst; clear H2.
        exact (proj1 (IH2 ρ mL x Hnl) (conj Hs2 (conj Ha Hc)) γ3 W2 ρe Heqe H3).
    + intros [Hns [Ha Hc]].
      destruct (proj2 (IH1 ρ mL x Hnl) (conj (down_env_add_nstrict_l γ1 γ2 mL Hnl x Hns) (conj Ha Hc))) as [F1 | (W1 & ev1 & lr1)].
      * left. intros γe W ρe Heqe H2. inversion H2; subst; clear H2.
        exact (F1 γ0 W1 ρe Heqe H1).
      * destruct (proj2 (IH2 ρ mL x Hnl) (conj (down_env_add_nstrict_r γ1 γ2 mL Hnl x Hns) (conj Ha Hc))) as [F2 | (W2 & ev2 & lr2)].
        -- left. intros γe W ρe Heqe H2. inversion H2; subst; clear H2.
           exact (F2 γ3 W2 ρe Heqe H3).
        -- right. exists (Pair W1 W2). split.
           ++ apply (E_VPair _ _ γ1 γ2 V1 V2 W1 W2).
              ** exact ev1.
              ** exact ev2.
              ** reflexivity.
           ++ unfold LR_maybe. cbn. exists W1, W2. split; [reflexivity | split; assumption].
  - (* T_Inl *)
    intros n0 γ0 Γ0 V1 A1 A2 v IH.
    intros ρ mL x Hnl. unfold SemVWt. split.
    + intros Hok. intros γe W ρe Heqe H2.
      inversion H2; subst; clear H2.
      match goal with
      | Hpre : EvalVal ?g ?r ?v ?w |- False =>
          exact (proj1 (IH ρ mL x Hnl) Hok g w r Heqe Hpre)
      end.
    + intros Hok. destruct (proj2 (IH ρ mL x Hnl) Hok) as [F | (W1 & ev1 & lr1)].
      * left. intros γe W ρe Heqe H2. inversion H2; subst; clear H2.
        match goal with
        | Hpre : EvalVal ?g ?r ?v ?w |- False => exact (F g w r Heqe Hpre)
        end.
      * right. exists (Inl W1). split.
        -- apply E_Inl. exact ev1.
        -- unfold LR_maybe. cbn. exists W1. left. split; [reflexivity | exact lr1].
  - (* T_Inr *)
    intros n0 γ0 Γ0 V2 A1 A2 v IH.
    intros ρ mL x Hnl. unfold SemVWt. split.
    + intros Hok. intros γe W ρe Heqe H2.
      inversion H2; subst; clear H2.
      match goal with
      | Hpre : EvalVal ?g ?r ?v ?w |- False =>
          exact (proj1 (IH ρ mL x Hnl) Hok g w r Heqe Hpre)
      end.
    + intros Hok. destruct (proj2 (IH ρ mL x Hnl) Hok) as [F | (W2 & ev2 & lr2)].
      * left. intros γe W ρe Heqe H2. inversion H2; subst; clear H2.
        match goal with
        | Hpre : EvalVal ?g ?r ?v ?w |- False => exact (F g w r Heqe Hpre)
        end.
      * right. exists (Inr W2). split.
        -- apply E_Inr. exact ev2.
        -- unfold LR_maybe. cbn. exists W2. right. split; [reflexivity | exact lr2].
  - (* T_Ret *)
    intros n0 γ0 Γ0 V A v IH.
    intros ρ mL x Hnl. unfold SemCWt. split.
    + intros [Hs [Ha Hc]]. split.
      * intro Hnf. intros γe Te ρe Heqe H2. inversion H2; subst; clear H2.
        match goal with
        | Hpre : EvalVal ?g ?r ?vv ?w |- False =>
            exact (proj1 (IH ρ mL x Hnl) (conj Hs (conj Ha Hc)) g w r Heqe Hpre)
        end.
      * intro Hnnf. exfalso. exact (Hnnf (non_func_CF A)).
    + intros [Hns [Ha Hc]].
      destruct (proj2 (IH ρ mL x Hnl) (conj Hns (conj Ha Hc))) as [F | (W & ev & lr)].
      * left. intros γe Te ρe Heqe H2. inversion H2; subst; clear H2.
        match goal with
        | Hpre : EvalVal ?g ?r ?vv ?w |- False => exact (F g w r Heqe Hpre)
        end.
      * right. exists (Return W). split.
        -- apply E_Ret. exact ev.
        -- unfold LR_maybe. cbn. exists W. split; [reflexivity | exact lr].
  - (* T_Let *)
    intros n0 γ0 Γ0 q M M' A B B' γ1 γ2 c IH1 c0 IH2 e e0. subst γ0. subst B.
    intros ρ mL x Hnl. unfold SemCWt. split.
    + intros [Hs [Ha Hc]]. split.
      * intro Hnf.
        set (H' := Nat.le_trans mL n0 (S n0) Hnl (le_succ_r n0)).
        destruct (down_env_until γ1 mL Hnl x) eqn:E1.
        -- assert (E1ns : down_env_until γ1 mL Hnl x <> Strict) by (rewrite E1; discriminate).
           assert (Hs2 : down_env_until γ2 mL Hnl x = Strict).
           { destruct (down_env_add_strict γ1 γ2 mL Hnl x Hs) as [Hc1 | Hc2]; [| exact Hc2].
             rewrite E1 in Hc1. discriminate Hc1. }
           destruct (proj2 (IH1 ρ mL x Hnl) (conj E1ns (conj Ha Hc))) as [HMfail | (W0 & evM & lrM)].
           ++ intros γe Te ρe Heqe H2. inversion H2; subst; clear H2.
              match goal with
              | Hpre : EvalComp ?g ρe M (Return ?w) |- False =>
                  exact (HMfail g (Return w) ρe Heqe Hpre)
              end.
           ++ destruct lrM as (W & HeqW & lrW). subst W0.
              assert (HnfB' : non_func B')
                by (apply (proj1 (non_func_down_ty B' n0 (Nat.le_succ_diag_r n0))); exact Hnf).
              pose proof (proj1 (proj1 (IH2 (W .: ρ) mL x H')
                    (rho_not_ok_cons γ2 ρ Γ0 mL x Hnl H' q A W (conj Hs2 (conj Ha Hc)) lrW)) HnfB') as HbodyFail.
              intros γe Te ρe Heqe H2. inversion H2; subst; clear H2.
              pose proof (eq_clos_return_inv _ _ (EvalComp_det_gen γ1 ρ M (Return W) evM γ0 ρe (Return W0) Heqe H1)) as Hval.
              exact (HbodyFail (q0 .: γ3) T' (W0 .: ρe) (eq_env_cons W W0 ρ ρe Hval Heqe) H3).
        -- destruct (proj1 (IH1 ρ mL x Hnl) (conj E1 (conj Ha Hc))) as [H1f _].
           pose proof (H1f (non_func_CF A)) as HMfail.
           intros γe Te ρe Heqe H2. inversion H2; subst; clear H2.
           match goal with
           | Hpre : EvalComp ?g ρe M (Return ?w) |- False =>
               exact (HMfail g (Return w) ρe Heqe Hpre)
           end.
        -- assert (E1ns : down_env_until γ1 mL Hnl x <> Strict) by (rewrite E1; discriminate).
           assert (Hs2 : down_env_until γ2 mL Hnl x = Strict).
           { destruct (down_env_add_strict γ1 γ2 mL Hnl x Hs) as [Hc1 | Hc2]; [| exact Hc2].
             rewrite E1 in Hc1. discriminate Hc1. }
           destruct (proj2 (IH1 ρ mL x Hnl) (conj E1ns (conj Ha Hc))) as [HMfail | (W0 & evM & lrM)].
           ++ intros γe Te ρe Heqe H2. inversion H2; subst; clear H2.
              match goal with
              | Hpre : EvalComp ?g ρe M (Return ?w) |- False =>
                  exact (HMfail g (Return w) ρe Heqe Hpre)
              end.
           ++ destruct lrM as (W & HeqW & lrW). subst W0.
              assert (HnfB' : non_func B')
                by (apply (proj1 (non_func_down_ty B' n0 (Nat.le_succ_diag_r n0))); exact Hnf).
              pose proof (proj1 (proj1 (IH2 (W .: ρ) mL x H')
                    (rho_not_ok_cons γ2 ρ Γ0 mL x Hnl H' q A W (conj Hs2 (conj Ha Hc)) lrW)) HnfB') as HbodyFail.
              intros γe Te ρe Heqe H2. inversion H2; subst; clear H2.
              pose proof (eq_clos_return_inv _ _ (EvalComp_det_gen γ1 ρ M (Return W) evM γ0 ρe (Return W0) Heqe H1)) as Hval.
              exact (HbodyFail (q0 .: γ3) T' (W0 .: ρe) (eq_env_cons W W0 ρ ρe Hval Heqe) H3).
      * intro Hnnf.
        set (H' := Nat.le_trans mL n0 (S n0) Hnl (le_succ_r n0)).
        destruct (down_env_until γ1 mL Hnl x) eqn:E1.
        -- assert (E1ns : down_env_until γ1 mL Hnl x <> Strict) by (rewrite E1; discriminate).
           assert (Hs2 : down_env_until γ2 mL Hnl x = Strict).
           { destruct (down_env_add_strict γ1 γ2 mL Hnl x Hs) as [Hc1 | Hc2]; [| exact Hc2].
             rewrite E1 in Hc1. discriminate Hc1. }
           destruct (proj2 (IH1 ρ mL x Hnl) (conj E1ns (conj Ha Hc))) as [HMfail | (W0 & evM & lrM)].
           ++ left. intros γe Te ρe Heqe H2. inversion H2; subst; clear H2.
              match goal with
              | Hpre : EvalComp ?g ρe M (Return ?w) |- False =>
                  exact (HMfail g (Return w) ρe Heqe Hpre)
              end.
           ++ destruct lrM as (W & HeqW & lrW). subst W0.
              assert (HnnfB' : ~ non_func B').
              { intro h. apply Hnnf. apply (proj2 (non_func_down_ty B' n0 (Nat.le_succ_diag_r n0))). exact h. }
              pose proof (proj2 (proj1 (IH2 (W .: ρ) mL x H')
                    (rho_not_ok_cons γ2 ρ Γ0 mL x Hnl H' q A W (conj Hs2 (conj Ha Hc)) lrW)) HnnfB') as Hbody.
              destruct Hbody as [HbodyFail | (T' & evB & lrNo)].
              ** left. intros γe Te ρe Heqe H2. inversion H2; subst; clear H2.
                 pose proof (eq_clos_return_inv _ _ (EvalComp_det_gen γ1 ρ M (Return W) evM γ0 ρe (Return W0) Heqe H1)) as Hval.
                 exact (HbodyFail (q0 .: γ3) T' (W0 .: ρe) (eq_env_cons W W0 ρ ρe Hval Heqe) H3).
              ** right. exists (@down_comp n0 T'). split.
                 --- eapply E_LetRet.
                     +++ exact evM.
                     +++ exact evB.
                     +++ reflexivity.
                     +++ reflexivity.
                 --- exact (proj1 (proj2 (DR_main n0 (Nat.le_succ_diag_r n0) B')) T' mL x Hnl lrNo).
        -- destruct (proj1 (IH1 ρ mL x Hnl) (conj E1 (conj Ha Hc))) as [H1f _].
           pose proof (H1f (non_func_CF A)) as HMfail.
           left. intros γe Te ρe Heqe H2. inversion H2; subst; clear H2.
           match goal with
           | Hpre : EvalComp ?g ρe M (Return ?w) |- False =>
               exact (HMfail g (Return w) ρe Heqe Hpre)
           end.
        -- assert (E1ns : down_env_until γ1 mL Hnl x <> Strict) by (rewrite E1; discriminate).
           assert (Hs2 : down_env_until γ2 mL Hnl x = Strict).
           { destruct (down_env_add_strict γ1 γ2 mL Hnl x Hs) as [Hc1 | Hc2]; [| exact Hc2].
             rewrite E1 in Hc1. discriminate Hc1. }
           destruct (proj2 (IH1 ρ mL x Hnl) (conj E1ns (conj Ha Hc))) as [HMfail | (W0 & evM & lrM)].
           ++ left. intros γe Te ρe Heqe H2. inversion H2; subst; clear H2.
              match goal with
              | Hpre : EvalComp ?g ρe M (Return ?w) |- False =>
                  exact (HMfail g (Return w) ρe Heqe Hpre)
              end.
           ++ destruct lrM as (W & HeqW & lrW). subst W0.
              assert (HnnfB' : ~ non_func B').
              { intro h. apply Hnnf. apply (proj2 (non_func_down_ty B' n0 (Nat.le_succ_diag_r n0))). exact h. }
              pose proof (proj2 (proj1 (IH2 (W .: ρ) mL x H')
                    (rho_not_ok_cons γ2 ρ Γ0 mL x Hnl H' q A W (conj Hs2 (conj Ha Hc)) lrW)) HnnfB') as Hbody.
              destruct Hbody as [HbodyFail | (T' & evB & lrNo)].
              ** left. intros γe Te ρe Heqe H2. inversion H2; subst; clear H2.
                 pose proof (eq_clos_return_inv _ _ (EvalComp_det_gen γ1 ρ M (Return W) evM γ0 ρe (Return W0) Heqe H1)) as Hval.
                 exact (HbodyFail (q0 .: γ3) T' (W0 .: ρe) (eq_env_cons W W0 ρ ρe Hval Heqe) H3).
              ** right. exists (@down_comp n0 T'). split.
                 --- eapply E_LetRet.
                     +++ exact evM.
                     +++ exact evB.
                     +++ reflexivity.
                     +++ reflexivity.
                 --- exact (proj1 (proj2 (DR_main n0 (Nat.le_succ_diag_r n0) B')) T' mL x Hnl lrNo).
    + intros [Hns [Ha Hc]].
      set (H' := Nat.le_trans mL n0 (S n0) Hnl (le_succ_r n0)).
      assert (E1ns : down_env_until γ1 mL Hnl x <> Strict).
      { rewrite down_env_add in Hns. apply attr_add_nstrict_l in Hns. exact Hns. }
      assert (E2ns : down_env_until γ2 mL Hnl x <> Strict).
      { rewrite down_env_add in Hns. apply attr_add_nstrict_r in Hns. exact Hns. }
      destruct (proj2 (IH1 ρ mL x Hnl) (conj E1ns (conj Ha Hc))) as [HMfail | (W0 & evM & lrM)].
      * left. intros γe Te ρe Heqe H2. inversion H2; subst; clear H2.
        match goal with
        | Hpre : EvalComp ?g ρe M (Return ?w) |- False =>
            exact (HMfail g (Return w) ρe Heqe Hpre)
        end.
      * destruct lrM as (W & HeqW & lrW). subst W0.
        destruct (proj2 (IH2 (W .: ρ) mL x H') (rho_maybe_ok_cons γ2 ρ Γ0 mL x Hnl H' q A W (conj E2ns (conj Ha Hc)) lrW)) as [HbodyFail | (T' & evB & lrB)].
        -- left. intros γe Te ρe Heqe H2. inversion H2; subst; clear H2.
           pose proof (eq_clos_return_inv _ _ (EvalComp_det_gen γ1 ρ M (Return W) evM γ0 ρe (Return W0) Heqe H1)) as Hval.
           exact (HbodyFail (q0 .: γ3) T' (W0 .: ρe) (eq_env_cons W W0 ρ ρe Hval Heqe) H3).
        -- right. exists (@down_comp n0 T'). split.
           ++ eapply E_LetRet.
              ** exact evM.
              ** exact evB.
              ** reflexivity.
              ** reflexivity.
           ++ exact (proj1 (DR_main n0 (Nat.le_succ_diag_r n0) B') T' mL x Hnl lrB).
  - (* T_Force *)
    intros n0 γ0 Γ0 V B γ1 γ2 v IH e. subst γ0.
    intros ρ mL x Hnl. unfold SemCWt. split.
    + intros [Hs [Ha Hc]]. split.
      * intro Hnf.
        destruct (down_env_until γ1 mL Hnl x) eqn:E1.
        -- assert (Hs2 : down_env_until γ2 mL Hnl x = Strict).
           { destruct (down_env_add_strict γ1 γ2 mL Hnl x Hs) as [Hc1 | Hc2]; [| exact Hc2].
             rewrite E1 in Hc1. discriminate Hc1. }
           assert (E1ns : down_env_until γ1 mL Hnl x <> Strict) by (rewrite E1; discriminate).
           destruct (proj2 (IH ρ mL x Hnl) (conj E1ns (conj Ha Hc))) as [FV | (W & evW & lrW)].
           ++ intros γe Te ρe Heqe H2. inversion H2; subst; clear H2.
              match goal with
              | HevV : EvalVal ?gV ρe V (Thunk ?mO2 ?mI2 ?g2_2 ?r2 ?M2) |- False =>
                  exact (FV gV (Thunk mO2 mI2 g2_2 r2 M2) ρe Heqe HevV)
              end.
           ++ destruct (LR_thunk_inv γ2 B W mL x lrW) as
                (mO & mI & gS & gI & rcap & M0 & HInner & Hn & HLower & Hnlower & Hd1 & Hd2 & HC & HLRM).
              try rewrite HC in evW. try rewrite <- Hd1 in evW.
               assert (Hd2' : down_env_until gI mO HInner = down_env_until γ2 mO Hn).
               { first [exact Hd2 | rewrite Hd2; rewrite <- Hd1; reflexivity]. }
              assert (HstrictI : down_env_until gI mL Hnlower x = Strict).
              { rewrite (down_env_to_common gI gS HInner Hnlower HLower x Hd2).
                rewrite <- (down_env_to_common γ2 gS Hn Hnl HLower x Hd1). exact Hs2. }
              destruct (proj1 HLRM HstrictI) as [Hbfail _].
              pose proof (Hbfail Hnf) as HbodyFail.
              intros γe Te ρe Heqe H2. inversion H2; subst; clear H2.
              pose proof (EvalVal_det_gen γ1 ρ V (Thunk mO mI (down_env_until γ2 mO Hn) rcap M0) evW γ0 ρe (Thunk mOuter mInner (down_env_until γ2' mOuter HInner0) ρ' M) Heqe H0) as Hth.
              dependent destruction Hth.
              exact (HbodyFail γ2' T' ρ' H H1).
        -- (* gamma1 strict *) 
           pose proof (proj1 (IH ρ mL x Hnl) (conj E1 (conj Ha Hc))) as FV.
           intros γe Te ρe Heqe H2. inversion H2; subst; clear H2.
           match goal with
           | HevV : EvalVal ?gV ρe V (Thunk ?mO2 ?mI2 ?g2_2 ?r2 ?M2) |- False =>
               exact (FV gV (Thunk mO2 mI2 g2_2 r2 M2) ρe Heqe HevV)
           end.
        -- assert (Hs2 : down_env_until γ2 mL Hnl x = Strict).
           { destruct (down_env_add_strict γ1 γ2 mL Hnl x Hs) as [Hc1 | Hc2]; [| exact Hc2].
             rewrite E1 in Hc1. discriminate Hc1. }
           assert (E1ns : down_env_until γ1 mL Hnl x <> Strict) by (rewrite E1; discriminate).
           destruct (proj2 (IH ρ mL x Hnl) (conj E1ns (conj Ha Hc))) as [FV | (W & evW & lrW)].
           ++ intros γe Te ρe Heqe H2. inversion H2; subst; clear H2.
              match goal with
              | HevV : EvalVal ?gV ρe V (Thunk ?mO2 ?mI2 ?g2_2 ?r2 ?M2) |- False =>
                  exact (FV gV (Thunk mO2 mI2 g2_2 r2 M2) ρe Heqe HevV)
              end.
           ++ destruct (LR_thunk_inv γ2 B W mL x lrW) as
                (mO & mI & gS & gI & rcap & M0 & HInner & Hn & HLower & Hnlower & Hd1 & Hd2 & HC & HLRM).
              try rewrite HC in evW. try rewrite <- Hd1 in evW.
               assert (Hd2' : down_env_until gI mO HInner = down_env_until γ2 mO Hn).
               { first [exact Hd2 | rewrite Hd2; rewrite <- Hd1; reflexivity]. }
              assert (HstrictI : down_env_until gI mL Hnlower x = Strict).
              { rewrite (down_env_to_common gI gS HInner Hnlower HLower x Hd2).
                rewrite <- (down_env_to_common γ2 gS Hn Hnl HLower x Hd1). exact Hs2. }
              destruct (proj1 HLRM HstrictI) as [Hbfail _].
              pose proof (Hbfail Hnf) as HbodyFail.
              intros γe Te ρe Heqe H2. inversion H2; subst; clear H2.
              pose proof (EvalVal_det_gen γ1 ρ V (Thunk mO mI (down_env_until γ2 mO Hn) rcap M0) evW γ0 ρe (Thunk mOuter mInner (down_env_until γ2' mOuter HInner0) ρ' M) Heqe H0) as Hth.
              dependent destruction Hth.
              exact (HbodyFail γ2' T' ρ' H H1).
      * intro Hnnf.
        destruct (down_env_until γ1 mL Hnl x) eqn:E1.
        -- assert (E1ns : down_env_until γ1 mL Hnl x <> Strict) by (rewrite E1; discriminate).
           assert (Hs2 : down_env_until γ2 mL Hnl x = Strict).
           { destruct (down_env_add_strict γ1 γ2 mL Hnl x Hs) as [Hc1 | Hc2]; [| exact Hc2].
             rewrite E1 in Hc1. discriminate Hc1. }
           destruct (proj2 (IH ρ mL x Hnl) (conj E1ns (conj Ha Hc))) as [FV | (W & evW & lrW)].
           ++ left. intros γe Te ρe Heqe H2. inversion H2; subst; clear H2.
              match goal with
              | HevV : EvalVal ?gV ρe V (Thunk ?mO2 ?mI2 ?g2_2 ?r2 ?M2) |- False =>
                  exact (FV gV (Thunk mO2 mI2 g2_2 r2 M2) ρe Heqe HevV)
              end.
           ++ destruct (LR_thunk_inv γ2 B W mL x lrW) as
                (mO & mI & gS & gI & rcap & M0 & HInner & Hn & HLower & Hnlower & Hd1 & Hd2 & HC & HLRM).
              try rewrite HC in evW. try rewrite <- Hd1 in evW.
               assert (Hd2' : down_env_until gI mO HInner = down_env_until γ2 mO Hn).
               { first [exact Hd2 | rewrite Hd2; rewrite <- Hd1; reflexivity]. }
              assert (HstrictI : down_env_until gI mL Hnlower x = Strict).
              { rewrite (down_env_to_common gI gS HInner Hnlower HLower x Hd2).
                rewrite <- (down_env_to_common γ2 gS Hn Hnl HLower x Hd1). exact Hs2. }
              destruct (proj2 (proj1 HLRM HstrictI) Hnnf) as [HbodyFail | (T' & evB & lrNo)].
              ** left. intros γe Te ρe Heqe H2. inversion H2; subst; clear H2.
                 pose proof (EvalVal_det_gen γ1 ρ V (Thunk mO mI (down_env_until γ2 mO Hn) rcap M0) evW γ0 ρe (Thunk mOuter mInner (down_env_until γ2' mOuter HInner0) ρ' M) Heqe H0) as Hth.
dependent destruction Hth.
exact (HbodyFail γ2' T' ρ' H H1).
              ** right. exists (@down_comp mO T'). split.
                 --- apply (E_Force (γ1 γ+ γ2) ρ mI mO γ2 γ1 (down_env_until γ2 mO Hn) gI V M0 (@down_comp mO T') T' rcap Hn HInner).
                     +++ exact evW.
                     +++ exact evB.
                     +++ exact Hd2'.
                     +++ apply down_env_until_irrel.
                     +++ reflexivity.
                     +++ reflexivity.
                 --- exact lrNo.
        -- pose proof (proj1 (IH ρ mL x Hnl) (conj E1 (conj Ha Hc))) as FV.
           left. intros γe Te ρe Heqe H2. inversion H2; subst; clear H2.
           match goal with
           | HevV : EvalVal ?gV ρe V (Thunk ?mO2 ?mI2 ?g2_2 ?r2 ?M2) |- False =>
               exact (FV gV (Thunk mO2 mI2 g2_2 r2 M2) ρe Heqe HevV)
           end.
        -- assert (E1ns : down_env_until γ1 mL Hnl x <> Strict) by (rewrite E1; discriminate).
           assert (Hs2 : down_env_until γ2 mL Hnl x = Strict).
           { destruct (down_env_add_strict γ1 γ2 mL Hnl x Hs) as [Hc1 | Hc2]; [| exact Hc2].
             rewrite E1 in Hc1. discriminate Hc1. }
           destruct (proj2 (IH ρ mL x Hnl) (conj E1ns (conj Ha Hc))) as [FV | (W & evW & lrW)].
           ++ left. intros γe Te ρe Heqe H2. inversion H2; subst; clear H2.
              match goal with
              | HevV : EvalVal ?gV ρe V (Thunk ?mO2 ?mI2 ?g2_2 ?r2 ?M2) |- False =>
                  exact (FV gV (Thunk mO2 mI2 g2_2 r2 M2) ρe Heqe HevV)
              end.
           ++ destruct (LR_thunk_inv γ2 B W mL x lrW) as
                (mO & mI & gS & gI & rcap & M0 & HInner & Hn & HLower & Hnlower & Hd1 & Hd2 & HC & HLRM).
              try rewrite HC in evW. try rewrite <- Hd1 in evW.
               assert (Hd2' : down_env_until gI mO HInner = down_env_until γ2 mO Hn).
               { first [exact Hd2 | rewrite Hd2; rewrite <- Hd1; reflexivity]. }
              assert (HstrictI : down_env_until gI mL Hnlower x = Strict).
              { rewrite (down_env_to_common gI gS HInner Hnlower HLower x Hd2).
                rewrite <- (down_env_to_common γ2 gS Hn Hnl HLower x Hd1). exact Hs2. }
              destruct (proj2 (proj1 HLRM HstrictI) Hnnf) as [HbodyFail | (T' & evB & lrNo)].
              ** left. intros γe Te ρe Heqe H2. inversion H2; subst; clear H2.
                 pose proof (EvalVal_det_gen γ1 ρ V (Thunk mO mI (down_env_until γ2 mO Hn) rcap M0) evW γ0 ρe (Thunk mOuter mInner (down_env_until γ2' mOuter HInner0) ρ' M) Heqe H0) as Hth.
dependent destruction Hth.
exact (HbodyFail γ2' T' ρ' H H1).
              ** right. exists (@down_comp mO T'). split.
                 --- apply (E_Force (γ1 γ+ γ2) ρ mI mO γ2 γ1 (down_env_until γ2 mO Hn) gI V M0 (@down_comp mO T') T' rcap Hn HInner).
                     +++ exact evW.
                     +++ exact evB.
                     +++ exact Hd2'.
                     +++ apply down_env_until_irrel.
                     +++ reflexivity.
                     +++ reflexivity.
                 --- exact lrNo.
    + intros [Hns [Ha Hc]].
      assert (E1ns : down_env_until γ1 mL Hnl x <> Strict) by
        (apply down_env_add_nstrict_l with (γ2 := γ2) (H := Hnl); exact Hns).
      assert (E2ns : down_env_until γ2 mL Hnl x <> Strict) by
        (apply down_env_add_nstrict_r with (γ1 := γ1) (H := Hnl); exact Hns).
      destruct (proj2 (IH ρ mL x Hnl) (conj E1ns (conj Ha Hc))) as [FV | (W & evW & lrW)].
      * left. intros γe Te ρe Heqe H2. inversion H2; subst; clear H2.
        match goal with
        | HevV : EvalVal ?gV ρe V (Thunk ?mO2 ?mI2 ?g2_2 ?r2 ?M2) |- False =>
            exact (FV gV (Thunk mO2 mI2 g2_2 r2 M2) ρe Heqe HevV)
        end.
      * destruct (LR_thunk_inv γ2 B W mL x lrW) as
          (mO & mI & gS & gI & rcap & M0 & HInner & Hn & HLower & Hnlower & Hd1 & Hd2 & HC & HLRM).
        try rewrite HC in evW. try rewrite <- Hd1 in evW.
               assert (Hd2' : down_env_until gI mO HInner = down_env_until γ2 mO Hn).
               { first [exact Hd2 | rewrite Hd2; rewrite <- Hd1; reflexivity]. }
        assert (HnsI : down_env_until gI mL Hnlower x <> Strict).
        { intro HsI. apply E2ns.
          rewrite (down_env_to_common γ2 (down_env_until γ2 mO Hn) Hn Hnl HLower x eq_refl).
          rewrite <- (down_env_to_common gI (down_env_until γ2 mO Hn) HInner Hnlower HLower x Hd2'). exact HsI. }
        destruct (proj2 HLRM HnsI) as [HbodyFail | (T' & evB & lrB)].
        -- left. intros γe Te ρe Heqe H2. inversion H2; subst; clear H2.
           pose proof (EvalVal_det_gen γ1 ρ V (Thunk mO mI (down_env_until γ2 mO Hn) rcap M0) evW γ0 ρe (Thunk mOuter mInner (down_env_until γ2' mOuter HInner0) ρ' M) Heqe H0) as Hth.
dependent destruction Hth.
exact (HbodyFail γ2' T' ρ' H H1).
        -- right. exists (@down_comp mO T'). split.
           ++ apply (E_Force (γ1 γ+ γ2) ρ mI mO γ2 γ1 (down_env_until γ2 mO Hn) gI V M0 (@down_comp mO T') T' rcap Hn HInner).
              ** exact evW.
              ** exact evB.
              ** exact Hd2'.
              ** apply down_env_until_irrel.
              ** reflexivity.
              ** reflexivity.
           ++ exact lrB.
  - (* T_Seq *)
    intros n0 γ0 Γ0 V M B γ1 γ2 v IH1 c IH2 e. subst γ0.
    intros ρ mL x Hnl. unfold SemCWt. split.
    + intros [Hs [Ha Hc]]. split.
      * intro Hnf.
        destruct (down_env_until γ1 mL Hnl x) eqn:E1.
        -- assert (E1ns : down_env_until γ1 mL Hnl x <> Strict) by (rewrite E1; discriminate).
           assert (Hs2 : down_env_until γ2 mL Hnl x = Strict).
           { destruct (down_env_add_strict γ1 γ2 mL Hnl x Hs) as [Hc1 | Hc2]; [| exact Hc2].
             rewrite E1 in Hc1. discriminate Hc1. }
           destruct (proj2 (IH1 ρ mL x Hnl) (conj E1ns (conj Ha Hc))) as [FV | (Wv & evV & lrV)].
           ++ apply EvalCompFail_seq_v. exact FV.
           ++ destruct (proj1 (IH2 ρ mL x Hnl) (conj Hs2 (conj Ha Hc))) as [HMf2 _].
              apply EvalCompFail_seq_m. apply HMf2. exact Hnf.
        -- pose proof (proj1 (IH1 ρ mL x Hnl) (conj E1 (conj Ha Hc))) as FV.
           apply EvalCompFail_seq_v. exact FV.
        -- assert (E1ns : down_env_until γ1 mL Hnl x <> Strict) by (rewrite E1; discriminate).
           assert (Hs2 : down_env_until γ2 mL Hnl x = Strict).
           { destruct (down_env_add_strict γ1 γ2 mL Hnl x Hs) as [Hc1 | Hc2]; [| exact Hc2].
             rewrite E1 in Hc1. discriminate Hc1. }
           destruct (proj2 (IH1 ρ mL x Hnl) (conj E1ns (conj Ha Hc))) as [FV | (Wv & evV & lrV)].
           ++ apply EvalCompFail_seq_v. exact FV.
           ++ destruct (proj1 (IH2 ρ mL x Hnl) (conj Hs2 (conj Ha Hc))) as [HMf2 _].
              apply EvalCompFail_seq_m. apply HMf2. exact Hnf.
      * intro Hnnf.
        destruct (down_env_until γ1 mL Hnl x) eqn:E1.
        -- assert (E1ns : down_env_until γ1 mL Hnl x <> Strict) by (rewrite E1; discriminate).
           assert (Hs2 : down_env_until γ2 mL Hnl x = Strict).
           { destruct (down_env_add_strict γ1 γ2 mL Hnl x Hs) as [Hc1 | Hc2]; [| exact Hc2].
             rewrite E1 in Hc1. discriminate Hc1. }
           destruct (proj2 (IH1 ρ mL x Hnl) (conj E1ns (conj Ha Hc))) as [FV | (Wv & evV & lrV)].
           ++ left. apply EvalCompFail_seq_v. exact FV.
           ++ cbn in lrV. subst Wv.
              destruct (proj2 (proj1 (IH2 ρ mL x Hnl) (conj Hs2 (conj Ha Hc))) Hnnf) as [HMf | (T & evM & lrNo)].
              ** left. apply EvalCompFail_seq_m. exact HMf.
              ** right. exists T. split.
                 --- eapply E_Seq.
                     +++ exact evV.
                     +++ exact evM.
                     +++ reflexivity.
                 --- exact lrNo.
        -- pose proof (proj1 (IH1 ρ mL x Hnl) (conj E1 (conj Ha Hc))) as FV.
           left. apply EvalCompFail_seq_v. exact FV.
        -- assert (E1ns : down_env_until γ1 mL Hnl x <> Strict) by (rewrite E1; discriminate).
           assert (Hs2 : down_env_until γ2 mL Hnl x = Strict).
           { destruct (down_env_add_strict γ1 γ2 mL Hnl x Hs) as [Hc1 | Hc2]; [| exact Hc2].
             rewrite E1 in Hc1. discriminate Hc1. }
           destruct (proj2 (IH1 ρ mL x Hnl) (conj E1ns (conj Ha Hc))) as [FV | (Wv & evV & lrV)].
           ++ left. apply EvalCompFail_seq_v. exact FV.
           ++ cbn in lrV. subst Wv.
              destruct (proj2 (proj1 (IH2 ρ mL x Hnl) (conj Hs2 (conj Ha Hc))) Hnnf) as [HMf | (T & evM & lrNo)].
              ** left. apply EvalCompFail_seq_m. exact HMf.
              ** right. exists T. split.
                 --- eapply E_Seq.
                     +++ exact evV.
                     +++ exact evM.
                     +++ reflexivity.
                 --- exact lrNo.
    + intros [Hns [Ha Hc]].
      assert (E1ns : down_env_until γ1 mL Hnl x <> Strict).
      { rewrite down_env_add in Hns. apply attr_add_nstrict_l in Hns. exact Hns. }
      assert (E2ns : down_env_until γ2 mL Hnl x <> Strict).
      { rewrite down_env_add in Hns. apply attr_add_nstrict_r in Hns. exact Hns. }
      destruct (proj2 (IH1 ρ mL x Hnl) (conj E1ns (conj Ha Hc))) as [FV | (Wv & evV & lrV)].
      * left. apply EvalCompFail_seq_v. exact FV.
      * cbn in lrV. subst Wv.
        destruct (proj2 (IH2 ρ mL x Hnl) (conj E2ns (conj Ha Hc))) as [HMf | (T & evM & lrM)].
        -- left. apply EvalCompFail_seq_m. exact HMf.
        -- right. exists T. split.
           ++ eapply E_Seq.
              ** exact evV.
              ** exact evM.
              ** reflexivity.
           ++ exact lrM.
  - (* T_Split *)
    intros n0 γ0 Γ0 q1 q2 V M γ1 γ2 A1 A2 B B' v IH1 c IH2 e e0. subst γ0. subst B.
    intros ρ mL x Hnl. unfold SemCWt. split.
    + intros [Hs [Ha Hc]]. split.
      * intro Hnf.
        set (H' := Nat.le_trans mL n0 (S (S n0)) Hnl (le_succ_succ_diag_r n0)).
        destruct (down_env_until γ1 mL Hnl x) eqn:E1.
        -- assert (E1ns : down_env_until γ1 mL Hnl x <> Strict) by (rewrite E1; discriminate).
           assert (Hs2 : down_env_until γ2 mL Hnl x = Strict).
           { destruct (down_env_add_strict γ1 γ2 mL Hnl x Hs) as [Hc1 | Hc2]; [| exact Hc2].
             rewrite E1 in Hc1. discriminate Hc1. }
           destruct (proj2 (IH1 ρ mL x Hnl) (conj E1ns (conj Ha Hc))) as [FV | (Wv & evV & lrV)].
           ++ apply EvalCompFail_split_v. exact FV.
           ++ destruct lrV as (W1 & W2 & Hv & lr1 & lr2). subst Wv.
              assert (HnfB' : non_func B') by (apply (proj1 (non_func_down_ty B' n0 (le_succ_succ_diag_r n0))); exact Hnf).
              pose proof (proj1 (proj1 (IH2 (W1 .: (W2 .: ρ)) mL x H')
                    (rho_not_ok_double γ2 ρ Γ0 mL x Hnl H' q1 q2 A1 A2 W1 W2 (conj Hs2 (conj Ha Hc)) lr1 lr2)) HnfB') as HbodyFail.
              intros γe Te ρe Heqe H2. inversion H2; subst; clear H2.
              pose proof (EvalVal_det_gen γ1 ρ V (Pair W1 W2) evV γ0 ρe (Pair W0 W3) Heqe H1) as Hpair.
              apply eq_clos_pair_inv in Hpair. destruct Hpair as [Hw1 Hw2].
              exact (HbodyFail (q0 .: (q3 .: γ3)) T' (W0 .: (W3 .: ρe)) (eq_env_double W1 W0 W2 W3 ρ ρe Hw1 Hw2 Heqe) H3).
        -- pose proof (proj1 (IH1 ρ mL x Hnl) (conj E1 (conj Ha Hc))) as FV.
           apply EvalCompFail_split_v. exact FV.
        -- assert (E1ns : down_env_until γ1 mL Hnl x <> Strict) by (rewrite E1; discriminate).
           assert (Hs2 : down_env_until γ2 mL Hnl x = Strict).
           { destruct (down_env_add_strict γ1 γ2 mL Hnl x Hs) as [Hc1 | Hc2]; [| exact Hc2].
             rewrite E1 in Hc1. discriminate Hc1. }
           destruct (proj2 (IH1 ρ mL x Hnl) (conj E1ns (conj Ha Hc))) as [FV | (Wv & evV & lrV)].
           ++ apply EvalCompFail_split_v. exact FV.
           ++ destruct lrV as (W1 & W2 & Hv & lr1 & lr2). subst Wv.
              assert (HnfB' : non_func B') by (apply (proj1 (non_func_down_ty B' n0 (le_succ_succ_diag_r n0))); exact Hnf).
              pose proof (proj1 (proj1 (IH2 (W1 .: (W2 .: ρ)) mL x H')
                    (rho_not_ok_double γ2 ρ Γ0 mL x Hnl H' q1 q2 A1 A2 W1 W2 (conj Hs2 (conj Ha Hc)) lr1 lr2)) HnfB') as HbodyFail.
              intros γe Te ρe Heqe H2. inversion H2; subst; clear H2.
              pose proof (EvalVal_det_gen γ1 ρ V (Pair W1 W2) evV γ0 ρe (Pair W0 W3) Heqe H1) as Hpair.
              apply eq_clos_pair_inv in Hpair. destruct Hpair as [Hw1 Hw2].
              exact (HbodyFail (q0 .: (q3 .: γ3)) T' (W0 .: (W3 .: ρe)) (eq_env_double W1 W0 W2 W3 ρ ρe Hw1 Hw2 Heqe) H3).
      * intro Hnnf.
        set (H' := Nat.le_trans mL n0 (S (S n0)) Hnl (le_succ_succ_diag_r n0)).
        destruct (down_env_until γ1 mL Hnl x) eqn:E1.
        -- assert (E1ns : down_env_until γ1 mL Hnl x <> Strict) by (rewrite E1; discriminate).
           assert (Hs2 : down_env_until γ2 mL Hnl x = Strict).
           { destruct (down_env_add_strict γ1 γ2 mL Hnl x Hs) as [Hc1 | Hc2]; [| exact Hc2].
             rewrite E1 in Hc1. discriminate Hc1. }
           destruct (proj2 (IH1 ρ mL x Hnl) (conj E1ns (conj Ha Hc))) as [FV | (Wv & evV & lrV)].
           ++ left. apply EvalCompFail_split_v. exact FV.
           ++ destruct lrV as (W1 & W2 & Hv & lr1 & lr2). subst Wv.
              assert (HnnfB' : ~ non_func B').
              { intro h. apply Hnnf. apply (proj2 (non_func_down_ty B' n0 (le_succ_succ_diag_r n0))). exact h. }
              destruct (proj2 (proj1 (IH2 (W1 .: (W2 .: ρ)) mL x H')
                    (rho_not_ok_double γ2 ρ Γ0 mL x Hnl H' q1 q2 A1 A2 W1 W2 (conj Hs2 (conj Ha Hc)) lr1 lr2)) HnnfB') as [HbodyFail | (T' & evB & lrNo)].
              ** left. intros γe Te ρe Heqe H2. inversion H2; subst; clear H2.
                 pose proof (EvalVal_det_gen γ1 ρ V (Pair W1 W2) evV γ0 ρe (Pair W0 W3) Heqe H1) as Hpair.
                 apply eq_clos_pair_inv in Hpair. destruct Hpair as [Hw1 Hw2].
                 exact (HbodyFail (q0 .: (q3 .: γ3)) T' (W0 .: (W3 .: ρe)) (eq_env_double W1 W0 W2 W3 ρ ρe Hw1 Hw2 Heqe) H3).
              ** right. exists (@down_comp n0 T'). split.
                 --- apply (E_Split (γ1 γ+ γ2) ρ q1 q2 γ1 γ2 V M W1 W2 (@down_comp n0 T') T').
                     +++ exact evV.
                     +++ exact evB.
                     +++ reflexivity.
                     +++ reflexivity.
                 --- exact (proj1 (proj2 (DR_main n0 (le_succ_succ_diag_r n0) B')) T' mL x Hnl lrNo).
        -- pose proof (proj1 (IH1 ρ mL x Hnl) (conj E1 (conj Ha Hc))) as FV.
           left. apply EvalCompFail_split_v. exact FV.
        -- assert (E1ns : down_env_until γ1 mL Hnl x <> Strict) by (rewrite E1; discriminate).
           assert (Hs2 : down_env_until γ2 mL Hnl x = Strict).
           { destruct (down_env_add_strict γ1 γ2 mL Hnl x Hs) as [Hc1 | Hc2]; [| exact Hc2].
             rewrite E1 in Hc1. discriminate Hc1. }
           destruct (proj2 (IH1 ρ mL x Hnl) (conj E1ns (conj Ha Hc))) as [FV | (Wv & evV & lrV)].
           ++ left. apply EvalCompFail_split_v. exact FV.
           ++ destruct lrV as (W1 & W2 & Hv & lr1 & lr2). subst Wv.
              assert (HnnfB' : ~ non_func B').
              { intro h. apply Hnnf. apply (proj2 (non_func_down_ty B' n0 (le_succ_succ_diag_r n0))). exact h. }
              destruct (proj2 (proj1 (IH2 (W1 .: (W2 .: ρ)) mL x H')
                    (rho_not_ok_double γ2 ρ Γ0 mL x Hnl H' q1 q2 A1 A2 W1 W2 (conj Hs2 (conj Ha Hc)) lr1 lr2)) HnnfB') as [HbodyFail | (T' & evB & lrNo)].
              ** left. intros γe Te ρe Heqe H2. inversion H2; subst; clear H2.
                 pose proof (EvalVal_det_gen γ1 ρ V (Pair W1 W2) evV γ0 ρe (Pair W0 W3) Heqe H1) as Hpair.
                 apply eq_clos_pair_inv in Hpair. destruct Hpair as [Hw1 Hw2].
                 exact (HbodyFail (q0 .: (q3 .: γ3)) T' (W0 .: (W3 .: ρe)) (eq_env_double W1 W0 W2 W3 ρ ρe Hw1 Hw2 Heqe) H3).
              ** right. exists (@down_comp n0 T'). split.
                 --- apply (E_Split (γ1 γ+ γ2) ρ q1 q2 γ1 γ2 V M W1 W2 (@down_comp n0 T') T').
                     +++ exact evV.
                     +++ exact evB.
                     +++ reflexivity.
                     +++ reflexivity.
                 --- exact (proj1 (proj2 (DR_main n0 (le_succ_succ_diag_r n0) B')) T' mL x Hnl lrNo).
    + intros [Hns [Ha Hc]].
      set (H' := Nat.le_trans mL n0 (S (S n0)) Hnl (le_succ_succ_diag_r n0)).
      assert (E1ns : down_env_until γ1 mL Hnl x <> Strict).
      { rewrite down_env_add in Hns. apply attr_add_nstrict_l in Hns. exact Hns. }
      assert (E2ns : down_env_until γ2 mL Hnl x <> Strict).
      { rewrite down_env_add in Hns. apply attr_add_nstrict_r in Hns. exact Hns. }
      destruct (proj2 (IH1 ρ mL x Hnl) (conj E1ns (conj Ha Hc))) as [FV | (Wv & evV & lrV)].
      * left. apply EvalCompFail_split_v. exact FV.
      * destruct lrV as (W1 & W2 & Hv & lr1 & lr2). subst Wv.
        destruct (proj2 (IH2 (W1 .: (W2 .: ρ)) mL x H')
              (rho_maybe_ok_double γ2 ρ Γ0 mL x Hnl H' q1 q2 A1 A2 W1 W2 (conj E2ns (conj Ha Hc)) lr1 lr2)) as [HbodyFail | (T' & evB & lrB)].
        -- left. intros γe Te ρe Heqe H2. inversion H2; subst; clear H2.
           pose proof (EvalVal_det_gen γ1 ρ V (Pair W1 W2) evV γ0 ρe (Pair W0 W3) Heqe H1) as Hpair.
           apply eq_clos_pair_inv in Hpair. destruct Hpair as [Hw1 Hw2].
           exact (HbodyFail (q0 .: (q3 .: γ3)) T' (W0 .: (W3 .: ρe)) (eq_env_double W1 W0 W2 W3 ρ ρe Hw1 Hw2 Heqe) H3).
        -- right. exists (@down_comp n0 T'). split.
           ++ apply (E_Split (γ1 γ+ γ2) ρ q1 q2 γ1 γ2 V M W1 W2 (@down_comp n0 T') T').
              ** exact evV.
              ** exact evB.
              ** reflexivity.
              ** reflexivity.
           ++ exact (proj1 (DR_main n0 (le_succ_succ_diag_r n0) B') T' mL x Hnl lrB).
  - (* T_Case *)
    intros n0 γ0 Γ0 q1 q2 V M1 M2 γ1 γ2 A1 A2 B B1 B2 v IH1 c IH2 c0 IH3 e e0 e1. subst γ0. subst B.
    intros ρ mL x Hnl. unfold SemCWt. split.
    + intros [Hs [Ha Hc]]. split.
      * intro Hnf.
        destruct (down_env_until γ1 mL Hnl x) eqn:E1.
        -- assert (E1ns : down_env_until γ1 mL Hnl x <> Strict) by (rewrite E1; discriminate).
           assert (Hs2 : down_env_until γ2 mL Hnl x = Strict).
           { destruct (down_env_add_strict γ1 γ2 mL Hnl x Hs) as [Hc1 | Hc2]; [| exact Hc2].
             rewrite E1 in Hc1. discriminate Hc1. }
           destruct (proj2 (IH1 ρ mL x Hnl) (conj E1ns (conj Ha Hc))) as [FV | (Wr & evV & lrV)].
           ++ apply EvalCompFail_case_v. exact FV.
           ++ destruct lrV as (Wv & [ (Hv & lrW) | (Hv & lrW) ]); subst Wr.
              ** assert (HnfB1 : non_func B1) by (apply (proj1 (non_func_down_ty B1 n0 (Nat.le_succ_diag_r n0))); exact Hnf).
                 pose proof (proj1 (proj1 (IH2 (Wv .: ρ) mL x (Nat.le_trans mL n0 (S n0) Hnl (le_succ_r n0)))
                       (rho_not_ok_cons γ2 ρ Γ0 mL x Hnl (Nat.le_trans mL n0 (S n0) Hnl (le_succ_r n0)) q1 A1 Wv (conj Hs2 (conj Ha Hc)) lrW)) HnfB1) as HbodyFail.
                 intros γe Te ρe Heqe H2. inversion H2; subst; clear H2.
                 all: match goal with
                 | H3 : EvalVal ?g ?re ?vv (Inl ?w), H4 : EvalComp (?q0 .: ?g2) (?w .: ?re) ?mm ?T2 |- False =>
                     pose proof (eq_clos_inl_inv _ _ (EvalVal_det_gen γ1 ρ vv (Inl Wv) evV g re (Inl w) Heqe H3)) as Hw;
                     exact (HbodyFail (q0 .: g2) T2 (w .: re) (eq_env_cons Wv w ρ re Hw Heqe) H4)
                 | H3 : EvalVal ?g ?re ?vv (Inr ?w) |- False =>
                     exact (eq_clos_inl_inr_false _ _ (EvalVal_det_gen γ1 ρ vv (Inl Wv) evV g re (Inr w) Heqe H3))
                 end.
              ** assert (HnfB2 : non_func B2).
                 { rewrite e1 in Hnf. apply (proj1 (non_func_down_ty B2 n0 (Nat.le_succ_diag_r n0))). exact Hnf. }
                 pose proof (proj1 (proj1 (IH3 (Wv .: ρ) mL x (Nat.le_trans mL n0 (S n0) Hnl (le_succ_r n0)))
                       (rho_not_ok_cons γ2 ρ Γ0 mL x Hnl (Nat.le_trans mL n0 (S n0) Hnl (le_succ_r n0)) q2 A2 Wv (conj Hs2 (conj Ha Hc)) lrW)) HnfB2) as HbodyFail.
                 intros γe Te ρe Heqe H2. inversion H2; subst; clear H2.
                 all: match goal with
                 | H3 : EvalVal ?g ?re ?vv (Inr ?w), H4 : EvalComp (?q0 .: ?g2) (?w .: ?re) ?mm ?T2 |- False =>
                     pose proof (eq_clos_inr_inv _ _ (EvalVal_det_gen γ1 ρ vv (Inr Wv) evV g re (Inr w) Heqe H3)) as Hw;
                     exact (HbodyFail (q0 .: g2) T2 (w .: re) (eq_env_cons Wv w ρ re Hw Heqe) H4)
                 | H3 : EvalVal ?g ?re ?vv (Inl ?w) |- False =>
                     exact (eq_clos_inr_inl_false _ _ (EvalVal_det_gen γ1 ρ vv (Inr Wv) evV g re (Inl w) Heqe H3))
                 end.
        -- pose proof (proj1 (IH1 ρ mL x Hnl) (conj E1 (conj Ha Hc))) as FV.
           apply EvalCompFail_case_v. exact FV.
        -- assert (E1ns : down_env_until γ1 mL Hnl x <> Strict) by (rewrite E1; discriminate).
           assert (Hs2 : down_env_until γ2 mL Hnl x = Strict).
           { destruct (down_env_add_strict γ1 γ2 mL Hnl x Hs) as [Hc1 | Hc2]; [| exact Hc2].
             rewrite E1 in Hc1. discriminate Hc1. }
           destruct (proj2 (IH1 ρ mL x Hnl) (conj E1ns (conj Ha Hc))) as [FV | (Wr & evV & lrV)].
           ++ apply EvalCompFail_case_v. exact FV.
           ++ destruct lrV as (Wv & [ (Hv & lrW) | (Hv & lrW) ]); subst Wr.
              ** assert (HnfB1 : non_func B1) by (apply (proj1 (non_func_down_ty B1 n0 (Nat.le_succ_diag_r n0))); exact Hnf).
                 pose proof (proj1 (proj1 (IH2 (Wv .: ρ) mL x (Nat.le_trans mL n0 (S n0) Hnl (le_succ_r n0)))
                       (rho_not_ok_cons γ2 ρ Γ0 mL x Hnl (Nat.le_trans mL n0 (S n0) Hnl (le_succ_r n0)) q1 A1 Wv (conj Hs2 (conj Ha Hc)) lrW)) HnfB1) as HbodyFail.
                 intros γe Te ρe Heqe H2. inversion H2; subst; clear H2.
                 all: match goal with
                 | H3 : EvalVal ?g ?re ?vv (Inl ?w), H4 : EvalComp (?q0 .: ?g2) (?w .: ?re) ?mm ?T2 |- False =>
                     pose proof (eq_clos_inl_inv _ _ (EvalVal_det_gen γ1 ρ vv (Inl Wv) evV g re (Inl w) Heqe H3)) as Hw;
                     exact (HbodyFail (q0 .: g2) T2 (w .: re) (eq_env_cons Wv w ρ re Hw Heqe) H4)
                 | H3 : EvalVal ?g ?re ?vv (Inr ?w) |- False =>
                     exact (eq_clos_inl_inr_false _ _ (EvalVal_det_gen γ1 ρ vv (Inl Wv) evV g re (Inr w) Heqe H3))
                 end.
              ** assert (HnfB2 : non_func B2).
                 { rewrite e1 in Hnf. apply (proj1 (non_func_down_ty B2 n0 (Nat.le_succ_diag_r n0))). exact Hnf. }
                 pose proof (proj1 (proj1 (IH3 (Wv .: ρ) mL x (Nat.le_trans mL n0 (S n0) Hnl (le_succ_r n0)))
                       (rho_not_ok_cons γ2 ρ Γ0 mL x Hnl (Nat.le_trans mL n0 (S n0) Hnl (le_succ_r n0)) q2 A2 Wv (conj Hs2 (conj Ha Hc)) lrW)) HnfB2) as HbodyFail.
                 intros γe Te ρe Heqe H2. inversion H2; subst; clear H2.
                 all: match goal with
                 | H3 : EvalVal ?g ?re ?vv (Inr ?w), H4 : EvalComp (?q0 .: ?g2) (?w .: ?re) ?mm ?T2 |- False =>
                     pose proof (eq_clos_inr_inv _ _ (EvalVal_det_gen γ1 ρ vv (Inr Wv) evV g re (Inr w) Heqe H3)) as Hw;
                     exact (HbodyFail (q0 .: g2) T2 (w .: re) (eq_env_cons Wv w ρ re Hw Heqe) H4)
                 | H3 : EvalVal ?g ?re ?vv (Inl ?w) |- False =>
                     exact (eq_clos_inr_inl_false _ _ (EvalVal_det_gen γ1 ρ vv (Inr Wv) evV g re (Inl w) Heqe H3))
                 end.
      * intro Hnnf.
        destruct (down_env_until γ1 mL Hnl x) eqn:E1.
        -- assert (E1ns : down_env_until γ1 mL Hnl x <> Strict) by (rewrite E1; discriminate).
           assert (Hs2 : down_env_until γ2 mL Hnl x = Strict).
           { destruct (down_env_add_strict γ1 γ2 mL Hnl x Hs) as [Hc1 | Hc2]; [| exact Hc2].
             rewrite E1 in Hc1. discriminate Hc1. }
           destruct (proj2 (IH1 ρ mL x Hnl) (conj E1ns (conj Ha Hc))) as [FV | (Wr & evV & lrV)].
           ++ left. apply EvalCompFail_case_v. exact FV.
           ++ destruct lrV as (Wv & [ (Hv & lrW) | (Hv & lrW) ]); subst Wr.
              ** assert (HnnfB1 : ~ non_func B1).
                 { intro h. apply Hnnf. apply (proj2 (non_func_down_ty B1 n0 (Nat.le_succ_diag_r n0))). exact h. }
                 destruct (proj2 (proj1 (IH2 (Wv .: ρ) mL x (Nat.le_trans mL n0 (S n0) Hnl (le_succ_r n0)))
                       (rho_not_ok_cons γ2 ρ Γ0 mL x Hnl (Nat.le_trans mL n0 (S n0) Hnl (le_succ_r n0)) q1 A1 Wv (conj Hs2 (conj Ha Hc)) lrW)) HnnfB1) as [HbodyFail | (T' & evB & lrNo)].
                 --- left. intros γe Te ρe Heqe H2. inversion H2; subst; clear H2.
                     all: match goal with
                     | H3 : EvalVal ?g ?re ?vv (Inl ?w), H4 : EvalComp (?q0 .: ?g2) (?w .: ?re) ?mm ?T2 |- False =>
                         pose proof (eq_clos_inl_inv _ _ (EvalVal_det_gen γ1 ρ vv (Inl Wv) evV g re (Inl w) Heqe H3)) as Hw;
                         exact (HbodyFail (q0 .: g2) T2 (w .: re) (eq_env_cons Wv w ρ re Hw Heqe) H4)
                     | H3 : EvalVal ?g ?re ?vv (Inr ?w) |- False =>
                         exact (eq_clos_inl_inr_false _ _ (EvalVal_det_gen γ1 ρ vv (Inl Wv) evV g re (Inr w) Heqe H3))
                     end.
                 --- right. exists (@down_comp n0 T'). split.
                     +++ apply (E_Casel (γ1 γ+ γ2) ρ γ1 γ2 q1 V M1 M2 Wv (@down_comp n0 T') T').
                         *** exact evV.
                         *** exact evB.
                         *** reflexivity.
                         *** reflexivity.
                     +++ exact (proj1 (proj2 (DR_main n0 (Nat.le_succ_diag_r n0) B1)) T' mL x Hnl lrNo).
              ** assert (HnnfB2 : ~ non_func B2).
                 { intro h. apply Hnnf. rewrite e1. apply (proj2 (non_func_down_ty B2 n0 (Nat.le_succ_diag_r n0))). exact h. }
                 destruct (proj2 (proj1 (IH3 (Wv .: ρ) mL x (Nat.le_trans mL n0 (S n0) Hnl (le_succ_r n0)))
                       (rho_not_ok_cons γ2 ρ Γ0 mL x Hnl (Nat.le_trans mL n0 (S n0) Hnl (le_succ_r n0)) q2 A2 Wv (conj Hs2 (conj Ha Hc)) lrW)) HnnfB2) as [HbodyFail | (T' & evB & lrNo)].
                 --- left. intros γe Te ρe Heqe H2. inversion H2; subst; clear H2.
                     all: match goal with
                     | H3 : EvalVal ?g ?re ?vv (Inr ?w), H4 : EvalComp (?q0 .: ?g2) (?w .: ?re) ?mm ?T2 |- False =>
                         pose proof (eq_clos_inr_inv _ _ (EvalVal_det_gen γ1 ρ vv (Inr Wv) evV g re (Inr w) Heqe H3)) as Hw;
                         exact (HbodyFail (q0 .: g2) T2 (w .: re) (eq_env_cons Wv w ρ re Hw Heqe) H4)
                     | H3 : EvalVal ?g ?re ?vv (Inl ?w) |- False =>
                         exact (eq_clos_inr_inl_false _ _ (EvalVal_det_gen γ1 ρ vv (Inr Wv) evV g re (Inl w) Heqe H3))
                     end.
                 --- right. exists (@down_comp n0 T'). split.
                     +++ apply (E_Caser (γ1 γ+ γ2) ρ γ1 γ2 q2 V M1 M2 Wv (@down_comp n0 T') T').
                         *** exact evV.
                         *** exact evB.
                         *** reflexivity.
                         *** reflexivity.
                     +++ rewrite e1. exact (proj1 (proj2 (DR_main n0 (Nat.le_succ_diag_r n0) B2)) T' mL x Hnl lrNo).
        -- pose proof (proj1 (IH1 ρ mL x Hnl) (conj E1 (conj Ha Hc))) as FV.
           left. apply EvalCompFail_case_v. exact FV.
        -- assert (E1ns : down_env_until γ1 mL Hnl x <> Strict) by (rewrite E1; discriminate).
           assert (Hs2 : down_env_until γ2 mL Hnl x = Strict).
           { destruct (down_env_add_strict γ1 γ2 mL Hnl x Hs) as [Hc1 | Hc2]; [| exact Hc2].
             rewrite E1 in Hc1. discriminate Hc1. }
           destruct (proj2 (IH1 ρ mL x Hnl) (conj E1ns (conj Ha Hc))) as [FV | (Wr & evV & lrV)].
           ++ left. apply EvalCompFail_case_v. exact FV.
           ++ destruct lrV as (Wv & [ (Hv & lrW) | (Hv & lrW) ]); subst Wr.
              ** assert (HnnfB1 : ~ non_func B1).
                 { intro h. apply Hnnf. apply (proj2 (non_func_down_ty B1 n0 (Nat.le_succ_diag_r n0))). exact h. }
                 destruct (proj2 (proj1 (IH2 (Wv .: ρ) mL x (Nat.le_trans mL n0 (S n0) Hnl (le_succ_r n0)))
                       (rho_not_ok_cons γ2 ρ Γ0 mL x Hnl (Nat.le_trans mL n0 (S n0) Hnl (le_succ_r n0)) q1 A1 Wv (conj Hs2 (conj Ha Hc)) lrW)) HnnfB1) as [HbodyFail | (T' & evB & lrNo)].
                 --- left. intros γe Te ρe Heqe H2. inversion H2; subst; clear H2.
                     all: match goal with
                     | H3 : EvalVal ?g ?re ?vv (Inl ?w), H4 : EvalComp (?q0 .: ?g2) (?w .: ?re) ?mm ?T2 |- False =>
                         pose proof (eq_clos_inl_inv _ _ (EvalVal_det_gen γ1 ρ vv (Inl Wv) evV g re (Inl w) Heqe H3)) as Hw;
                         exact (HbodyFail (q0 .: g2) T2 (w .: re) (eq_env_cons Wv w ρ re Hw Heqe) H4)
                     | H3 : EvalVal ?g ?re ?vv (Inr ?w) |- False =>
                         exact (eq_clos_inl_inr_false _ _ (EvalVal_det_gen γ1 ρ vv (Inl Wv) evV g re (Inr w) Heqe H3))
                     end.
                 --- right. exists (@down_comp n0 T'). split.
                     +++ apply (E_Casel (γ1 γ+ γ2) ρ γ1 γ2 q1 V M1 M2 Wv (@down_comp n0 T') T').
                         *** exact evV.
                         *** exact evB.
                         *** reflexivity.
                         *** reflexivity.
                     +++ exact (proj1 (proj2 (DR_main n0 (Nat.le_succ_diag_r n0) B1)) T' mL x Hnl lrNo).
              ** assert (HnnfB2 : ~ non_func B2).
                 { intro h. apply Hnnf. rewrite e1. apply (proj2 (non_func_down_ty B2 n0 (Nat.le_succ_diag_r n0))). exact h. }
                 destruct (proj2 (proj1 (IH3 (Wv .: ρ) mL x (Nat.le_trans mL n0 (S n0) Hnl (le_succ_r n0)))
                       (rho_not_ok_cons γ2 ρ Γ0 mL x Hnl (Nat.le_trans mL n0 (S n0) Hnl (le_succ_r n0)) q2 A2 Wv (conj Hs2 (conj Ha Hc)) lrW)) HnnfB2) as [HbodyFail | (T' & evB & lrNo)].
                 --- left. intros γe Te ρe Heqe H2. inversion H2; subst; clear H2.
                     all: match goal with
                     | H3 : EvalVal ?g ?re ?vv (Inr ?w), H4 : EvalComp (?q0 .: ?g2) (?w .: ?re) ?mm ?T2 |- False =>
                         pose proof (eq_clos_inr_inv _ _ (EvalVal_det_gen γ1 ρ vv (Inr Wv) evV g re (Inr w) Heqe H3)) as Hw;
                         exact (HbodyFail (q0 .: g2) T2 (w .: re) (eq_env_cons Wv w ρ re Hw Heqe) H4)
                     | H3 : EvalVal ?g ?re ?vv (Inl ?w) |- False =>
                         exact (eq_clos_inr_inl_false _ _ (EvalVal_det_gen γ1 ρ vv (Inr Wv) evV g re (Inl w) Heqe H3))
                     end.
                 --- right. exists (@down_comp n0 T'). split.
                     +++ apply (E_Caser (γ1 γ+ γ2) ρ γ1 γ2 q2 V M1 M2 Wv (@down_comp n0 T') T').
                         *** exact evV.
                         *** exact evB.
                         *** reflexivity.
                         *** reflexivity.
                     +++ rewrite e1. exact (proj1 (proj2 (DR_main n0 (Nat.le_succ_diag_r n0) B2)) T' mL x Hnl lrNo).
    + intros [Hns [Ha Hc]].
      assert (E1ns : down_env_until γ1 mL Hnl x <> Strict).
      { rewrite down_env_add in Hns. apply attr_add_nstrict_l in Hns. exact Hns. }
      assert (E2ns : down_env_until γ2 mL Hnl x <> Strict).
      { rewrite down_env_add in Hns. apply attr_add_nstrict_r in Hns. exact Hns. }
      destruct (proj2 (IH1 ρ mL x Hnl) (conj E1ns (conj Ha Hc))) as [FV | (Wr & evV & lrV)].
      * left. apply EvalCompFail_case_v. exact FV.
      * destruct lrV as (Wv & [ (Hv & lrW) | (Hv & lrW) ]); subst Wr.
        -- destruct (proj2 (IH2 (Wv .: ρ) mL x (Nat.le_trans mL n0 (S n0) Hnl (le_succ_r n0)))
              (rho_maybe_ok_cons γ2 ρ Γ0 mL x Hnl (Nat.le_trans mL n0 (S n0) Hnl (le_succ_r n0)) q1 A1 Wv (conj E2ns (conj Ha Hc)) lrW)) as [HbodyFail | (T' & evB & lrB)].
           ++ left. intros γe Te ρe Heqe H2. inversion H2; subst; clear H2.
              all: match goal with
              | H3 : EvalVal ?g ?re ?vv (Inl ?w), H4 : EvalComp (?q0 .: ?g2) (?w .: ?re) ?mm ?T2 |- False =>
                  pose proof (eq_clos_inl_inv _ _ (EvalVal_det_gen γ1 ρ vv (Inl Wv) evV g re (Inl w) Heqe H3)) as Hw;
                  exact (HbodyFail (q0 .: g2) T2 (w .: re) (eq_env_cons Wv w ρ re Hw Heqe) H4)
              | H3 : EvalVal ?g ?re ?vv (Inr ?w) |- False =>
                  exact (eq_clos_inl_inr_false _ _ (EvalVal_det_gen γ1 ρ vv (Inl Wv) evV g re (Inr w) Heqe H3))
              end.
           ++ right. exists (@down_comp n0 T'). split.
              ** apply (E_Casel (γ1 γ+ γ2) ρ γ1 γ2 q1 V M1 M2 Wv (@down_comp n0 T') T').
                 --- exact evV.
                 --- exact evB.
                 --- reflexivity.
                 --- reflexivity.
              ** exact (proj1 (DR_main n0 (Nat.le_succ_diag_r n0) B1) T' mL x Hnl lrB).
        -- destruct (proj2 (IH3 (Wv .: ρ) mL x (Nat.le_trans mL n0 (S n0) Hnl (le_succ_r n0)))
              (rho_maybe_ok_cons γ2 ρ Γ0 mL x Hnl (Nat.le_trans mL n0 (S n0) Hnl (le_succ_r n0)) q2 A2 Wv (conj E2ns (conj Ha Hc)) lrW)) as [HbodyFail | (T' & evB & lrB)].
           ++ left. intros γe Te ρe Heqe H2. inversion H2; subst; clear H2.
              all: match goal with
              | H3 : EvalVal ?g ?re ?vv (Inr ?w), H4 : EvalComp (?q0 .: ?g2) (?w .: ?re) ?mm ?T2 |- False =>
                  pose proof (eq_clos_inr_inv _ _ (EvalVal_det_gen γ1 ρ vv (Inr Wv) evV g re (Inr w) Heqe H3)) as Hw;
                  exact (HbodyFail (q0 .: g2) T2 (w .: re) (eq_env_cons Wv w ρ re Hw Heqe) H4)
              | H3 : EvalVal ?g ?re ?vv (Inl ?w) |- False =>
                  exact (eq_clos_inr_inl_false _ _ (EvalVal_det_gen γ1 ρ vv (Inr Wv) evV g re (Inl w) Heqe H3))
              end.
           ++ right. exists (@down_comp n0 T'). split.
              ** apply (E_Caser (γ1 γ+ γ2) ρ γ1 γ2 q2 V M1 M2 Wv (@down_comp n0 T') T').
                 --- exact evV.
                 --- exact evB.
                 --- reflexivity.
                 --- reflexivity.
              ** rewrite e1. exact (proj1 (DR_main n0 (Nat.le_succ_diag_r n0) B2) T' mL x Hnl lrB).
  - (* T_Abs *)
    intros n0 γ0 Γ0 q M A B B' c IH e. subst B.
    intros ρ mL x Hnl. unfold SemCWt. split.
    + intros [Hs [Ha Hc]]. split.
      * intro Hnf.
        exfalso. exact (Hnf q A (down_compTy_until B' n0 (Nat.le_succ_diag_r n0)) eq_refl).
      * intro Hnnf.
        right. exists (Closure n0 n0 γ0 ρ M). split.
        -- apply E_Abs.
        -- unfold LR_no. cbn.
           exists n0, n0, γ0, γ0, ρ, M, (le_n n0), (le_n n0), Hnl, Hnl.
           split; [apply down_env_self_fun | split; [reflexivity |]].
           intros W HWA.
           set (W' := (n0 W↓ W)).
           assert (HWA' : LR_maybe A W' mL x).
           { unfold W'. apply (LRprops_Dm Lazy A W mL x n0 Hnl). exact HWA. }
           set (H' := Nat.le_trans mL n0 (S n0) Hnl (le_succ_r n0)).
           split.
           ++ intro HnfB.
              apply (proj1 (proj1 (IH (W' .: ρ) mL x H')
                    (rho_not_ok_cons γ0 ρ Γ0 mL x Hnl H' q A W' (conj Hs (conj Ha Hc)) HWA'))).
              apply (proj1 (non_func_down_ty B' n0 (Nat.le_succ_diag_r n0))). exact HnfB.
           ++ intro HnnfB.
              assert (HnnfB' : ~ non_func B').
              { intro h. apply HnnfB. apply (proj2 (non_func_down_ty B' n0 (Nat.le_succ_diag_r n0))). exact h. }
              destruct (proj2 (proj1 (IH (W' .: ρ) mL x H')
                    (rho_not_ok_cons γ0 ρ Γ0 mL x Hnl H' q A W' (conj Hs (conj Ha Hc)) HWA')) HnnfB') as [Hf | (T & ev & lr)].
              ** left. exact Hf.
              ** right. exists T. split; [exact ev |].
                 exact (proj1 (proj2 (DR_main n0 (Nat.le_succ_diag_r n0) B')) T mL x Hnl lr).
    + intros [Hns [Ha Hc]].
      right. exists (Closure n0 n0 γ0 ρ M). split.
      * apply E_Abs.
      * unfold LR_maybe. cbn.
        exists n0, n0, γ0, γ0, ρ, M, (le_n n0), (le_n n0), Hnl, Hnl.
        split; [apply down_env_self_fun | split; [reflexivity |]].
        intros W HWA.
        set (W' := (n0 W↓ W)).
        assert (HWA' : LR_maybe A W' mL x).
        { unfold W'. apply (LRprops_Dm Lazy A W mL x n0 Hnl). exact HWA. }
        set (H' := Nat.le_trans mL n0 (S n0) Hnl (le_succ_r n0)).
        destruct (proj2 (IH (W' .: ρ) mL x H')
              (rho_maybe_ok_cons γ0 ρ Γ0 mL x Hnl H' q A W' (conj Hns (conj Ha Hc)) HWA')) as [Hf | (T & ev & lr)].
        -- left. exact Hf.
        -- right. exists T. split; [exact ev |].
           exact (proj1 (DR_main n0 (Nat.le_succ_diag_r n0) B') T mL x Hnl lr).
  - (* T_App *)
    intros n0 γ0 Γ0 M q V γ1 γ2 A B c IH1 v IH2 e. subst γ0.
    intros ρ mL x Hnl. unfold SemCWt. split.
    + intros [Hs [Ha Hc]]. split.
      * intro Hnf.
        destruct (down_env_until γ1 mL Hnl x) eqn:E1.
        -- assert (Hs2 : down_env_until γ2 mL Hnl x = Strict).
           { destruct (down_env_add_strict γ1 γ2 mL Hnl x Hs) as [Hc1 | Hc2]; [| exact Hc2].
             rewrite E1 in Hc1. discriminate Hc1. }
           apply EvalCompFail_app_v. exact (proj1 (IH2 ρ mL x Hnl) (conj Hs2 (conj Ha Hc))).
        -- destruct (down_env_until γ2 mL Hnl x) eqn:E2.
           ++ assert (E2ns : down_env_until γ2 mL Hnl x <> Strict) by (rewrite E2; discriminate).
              destruct (proj2 (proj1 (IH1 ρ mL x Hnl) (conj E1 (conj Ha Hc))) (not_non_func_CAbs q A B)) as [HMfail | (T1 & evM & lrNo)].
              ** apply EvalCompFail_app_m. exact HMfail.
              ** destruct (LR_abs_no_inv q A B T1 mL x lrNo) as (mO & mI & gS & gI & rcap & Mbody & Hn & HInner & HLower & Hnlower & Hd & HC & Hbody).
                 subst T1. try rewrite <- Hd in evM. try subst gS.
                 destruct (proj2 (IH2 ρ mL x Hnl) (conj E2ns (conj Ha Hc))) as [FV2 | (W0 & evW0 & lrW0)].
                 --- apply EvalCompFail_app_v. exact FV2.
                 --- pose proof (proj1 (Hbody W0 lrW0) Hnf) as HbodyFail.
                     exact (EvalCompFail_app_elim γ1 γ2 ρ M q V mO mI _ gI rcap Mbody W0 HInner evM evW0 HbodyFail).
           ++ apply EvalCompFail_app_v. exact (proj1 (IH2 ρ mL x Hnl) (conj E2 (conj Ha Hc))).
           ++ assert (E2ns : down_env_until γ2 mL Hnl x <> Strict) by (rewrite E2; discriminate).
              destruct (proj2 (proj1 (IH1 ρ mL x Hnl) (conj E1 (conj Ha Hc))) (not_non_func_CAbs q A B)) as [HMfail | (T1 & evM & lrNo)].
              ** apply EvalCompFail_app_m. exact HMfail.
              ** destruct (LR_abs_no_inv q A B T1 mL x lrNo) as (mO & mI & gS & gI & rcap & Mbody & Hn & HInner & HLower & Hnlower & Hd & HC & Hbody).
                 subst T1. try rewrite <- Hd in evM. try subst gS.
                 destruct (proj2 (IH2 ρ mL x Hnl) (conj E2ns (conj Ha Hc))) as [FV2 | (W0 & evW0 & lrW0)].
                 --- apply EvalCompFail_app_v. exact FV2.
                 --- pose proof (proj1 (Hbody W0 lrW0) Hnf) as HbodyFail.
                     exact (EvalCompFail_app_elim γ1 γ2 ρ M q V mO mI _ gI rcap Mbody W0 HInner evM evW0 HbodyFail).
        -- assert (Hs2 : down_env_until γ2 mL Hnl x = Strict).
           { destruct (down_env_add_strict γ1 γ2 mL Hnl x Hs) as [Hc1 | Hc2]; [| exact Hc2].
             rewrite E1 in Hc1. discriminate Hc1. }
           apply EvalCompFail_app_v. exact (proj1 (IH2 ρ mL x Hnl) (conj Hs2 (conj Ha Hc))).
      * intro Hnnf.
        destruct (down_env_until γ1 mL Hnl x) eqn:E1.
        -- assert (Hs2 : down_env_until γ2 mL Hnl x = Strict).
           { destruct (down_env_add_strict γ1 γ2 mL Hnl x Hs) as [Hc1 | Hc2]; [| exact Hc2].
             rewrite E1 in Hc1. discriminate Hc1. }
           left. apply EvalCompFail_app_v. exact (proj1 (IH2 ρ mL x Hnl) (conj Hs2 (conj Ha Hc))).
        -- destruct (down_env_until γ2 mL Hnl x) eqn:E2.
           ++ assert (E2ns : down_env_until γ2 mL Hnl x <> Strict) by (rewrite E2; discriminate).
              destruct (proj2 (proj1 (IH1 ρ mL x Hnl) (conj E1 (conj Ha Hc))) (not_non_func_CAbs q A B)) as [HMfail | (T1 & evM & lrNo)].
              ** left. apply EvalCompFail_app_m. exact HMfail.
              ** destruct (LR_abs_no_inv q A B T1 mL x lrNo) as (mO & mI & gS & gI & rcap & Mbody & Hn & HInner & HLower & Hnlower & Hd & HC & Hbody).
                 subst T1. try rewrite <- Hd in evM. try subst gS.
                 destruct (proj2 (IH2 ρ mL x Hnl) (conj E2ns (conj Ha Hc))) as [FV2 | (W0 & evW0 & lrW0)].
                 --- left. apply EvalCompFail_app_v. exact FV2.
                 --- destruct (proj2 (Hbody W0 lrW0) Hnnf) as [HbodyFail | (Tb & evB & lrNoB)].
                     ++++ left. exact (EvalCompFail_app_elim γ1 γ2 ρ M q V mO mI _ gI rcap Mbody W0 HInner evM evW0 HbodyFail).
                     ++++ right. exists (@down_comp mO Tb). split.
                     +++++ apply (E_AppAbs (γ1 γ+ γ2) ρ mO mI q γ1 γ2 (down_env_until gI mO HInner) gI HInner M Mbody V (@down_comp mO Tb) Tb W0 rcap); [ exact evM | exact evW0 | reflexivity | exact evB | reflexivity | reflexivity ].
                     +++++ exact lrNoB.
           ++ left. apply EvalCompFail_app_v. exact (proj1 (IH2 ρ mL x Hnl) (conj E2 (conj Ha Hc))).
           ++ assert (E2ns : down_env_until γ2 mL Hnl x <> Strict) by (rewrite E2; discriminate).
              destruct (proj2 (proj1 (IH1 ρ mL x Hnl) (conj E1 (conj Ha Hc))) (not_non_func_CAbs q A B)) as [HMfail | (T1 & evM & lrNo)].
              ** left. apply EvalCompFail_app_m. exact HMfail.
              ** destruct (LR_abs_no_inv q A B T1 mL x lrNo) as (mO & mI & gS & gI & rcap & Mbody & Hn & HInner & HLower & Hnlower & Hd & HC & Hbody).
                 subst T1. try rewrite <- Hd in evM. try subst gS.
                 destruct (proj2 (IH2 ρ mL x Hnl) (conj E2ns (conj Ha Hc))) as [FV2 | (W0 & evW0 & lrW0)].
                 --- left. apply EvalCompFail_app_v. exact FV2.
                 --- destruct (proj2 (Hbody W0 lrW0) Hnnf) as [HbodyFail | (Tb & evB & lrNoB)].
                     ++++ left. exact (EvalCompFail_app_elim γ1 γ2 ρ M q V mO mI _ gI rcap Mbody W0 HInner evM evW0 HbodyFail).
                     ++++ right. exists (@down_comp mO Tb). split.
                     +++++ apply (E_AppAbs (γ1 γ+ γ2) ρ mO mI q γ1 γ2 (down_env_until gI mO HInner) gI HInner M Mbody V (@down_comp mO Tb) Tb W0 rcap); [ exact evM | exact evW0 | reflexivity | exact evB | reflexivity | reflexivity ].
                     +++++ exact lrNoB.
        -- assert (Hs2 : down_env_until γ2 mL Hnl x = Strict).
           { destruct (down_env_add_strict γ1 γ2 mL Hnl x Hs) as [Hc1 | Hc2]; [| exact Hc2].
             rewrite E1 in Hc1. discriminate Hc1. }
           left. apply EvalCompFail_app_v. exact (proj1 (IH2 ρ mL x Hnl) (conj Hs2 (conj Ha Hc))).
    + intros [Hns [Ha Hc]].
      assert (E1ns : down_env_until γ1 mL Hnl x <> Strict).
      { rewrite down_env_add in Hns. apply attr_add_nstrict_l in Hns. exact Hns. }
      assert (E2ns : down_env_until γ2 mL Hnl x <> Strict).
      { rewrite down_env_add in Hns. apply attr_add_nstrict_r in Hns. exact Hns. }
      destruct (proj2 (IH1 ρ mL x Hnl) (conj E1ns (conj Ha Hc))) as [HMfail | (T1 & evM & lrM)].
      * left. apply EvalCompFail_app_m. exact HMfail.
      * destruct (LR_abs_maybe_inv q A B T1 mL x lrM) as (mO & mI & gS & gI & rcap & Mbody & Hn & HInner & HLower & Hnlower & Hd & HC & Hbody).
        subst T1. try rewrite <- Hd in evM. try subst gS.
        destruct (proj2 (IH2 ρ mL x Hnl) (conj E2ns (conj Ha Hc))) as [FV2 | (W0 & evW0 & lrW0)].
        -- left. apply EvalCompFail_app_v. exact FV2.
        -- destruct (Hbody W0 lrW0) as [HbodyFail | (Tb & evB & lrB)].
           ++ left. exact (EvalCompFail_app_elim γ1 γ2 ρ M q V mO mI _ gI rcap Mbody W0 HInner evM evW0 HbodyFail).
           ++ right. exists (@down_comp mO Tb). split.
              ** apply (E_AppAbs (γ1 γ+ γ2) ρ mO mI q γ1 γ2 (down_env_until gI mO HInner) gI HInner M Mbody V (@down_comp mO Tb) Tb W0 rcap).
                 --- exact evM.
                 --- exact evW0.
                 --- reflexivity.
                 --- exact evB.
                 --- reflexivity.
                 --- reflexivity.
              ** exact lrB.
  - (* T_CSub *)
    intros n0 γ0 Γ0 M g' B c IH a.
    intros ρ mL x Hnl. unfold SemCWt. split.
    + intros [Hs [Ha Hc]].
      assert (Hs' : down_env_until g' mL Hnl x = Strict).
      { rewrite down_env_until_up. rewrite down_env_until_up in Hs.
        exact (attr_le_strict (γ0 (up_fin_until n0 Hnl x)) (g' (up_fin_until n0 Hnl x)) (a (up_fin_until n0 Hnl x)) Hs). }
      split.
      * intro Hnf.
        apply EvalCompFail_sub_m.
        exact (proj1 (proj1 (IH ρ mL x Hnl) (conj Hs' (conj Ha Hc))) Hnf).
      * intro Hnnf.
        destruct (proj2 (proj1 (IH ρ mL x Hnl) (conj Hs' (conj Ha Hc))) Hnnf) as [HMf | (T & ev & lr)].
        -- left. apply EvalCompFail_sub_m. exact HMf.
        -- right. exists T. split.
           ++ apply (E_CSub _ _ M g' T); [exact ev | exact a].
           ++ exact lr.
    + intros [Hns [Ha Hc]].
      destruct (down_env_until g' mL Hnl x) eqn:E'.
      * assert (E'ns : down_env_until g' mL Hnl x <> Strict) by (rewrite E'; discriminate).
        destruct (proj2 (IH ρ mL x Hnl) (conj E'ns (conj Ha Hc))) as [HMf | (T & ev & lr)].
        -- left. apply EvalCompFail_sub_m. exact HMf.
        -- right. exists T. split.
           ++ apply (E_CSub _ _ M g' T); [exact ev | exact a].
           ++ exact lr.
      * destruct (proj1 (IH ρ mL x Hnl) (conj E' (conj Ha Hc))) as [HnfPre HnnfPre].
        destruct (non_func_or_not B) as [HnfB | HnnfB].
        -- left. apply EvalCompFail_sub_m. apply HnfPre. exact HnfB.
        -- destruct (HnnfPre HnnfB) as [HMf | (T & ev & lr)].
           ++ left. apply EvalCompFail_sub_m. exact HMf.
           ++ right. exists T. split.
              ** apply (E_CSub _ _ M g' T); [exact ev | exact a].
              ** apply LR_no_maybe. exact lr.
      * assert (E'ns : down_env_until g' mL Hnl x <> Strict) by (rewrite E'; discriminate).
        destruct (proj2 (IH ρ mL x Hnl) (conj E'ns (conj Ha Hc))) as [HMf | (T & ev & lr)].
        -- left. apply EvalCompFail_sub_m. exact HMf.
        -- right. exists T. split.
           ++ apply (E_CSub _ _ M g' T); [exact ev | exact a].
           ++ exact lr.
Qed.

Theorem strict_explosion : forall n (γ : attrs n) (Γ : context n) (ρ : env n) i,
  ρ_not_ok γ ρ Γ n i ltac:(auto) ->
  (forall V A, VWt γ Γ V A -> EvalValFail ρ V) /\
  (forall M A, CWt γ Γ M (CF A) -> EvalCompFail ρ M).
Proof.
  intros n γ Γ ρ i Hok. split.
  - intros V A HV.
    exact (proj1 (((proj1 (Sem_typing n γ Γ)) V A HV) ρ n i _) Hok).
  - intros M A HM.
    exact (proj1 (proj1 (((proj2 (Sem_typing n γ Γ)) M (CF A) HM) ρ n i _) Hok) (non_func_CF A)).
Qed.
