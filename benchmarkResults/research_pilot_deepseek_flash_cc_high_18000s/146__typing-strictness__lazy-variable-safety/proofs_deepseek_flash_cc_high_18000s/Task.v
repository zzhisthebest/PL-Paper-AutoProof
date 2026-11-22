From strictness.cbpv Require Import lazy_semtyping.
From Coq Require Import FunctionalExtensionality.
Require Import Psatz.
Require Import Coq.Logic.Eqdep_dec.
From Stdlib Require Import Arith.

Definition castf {a b} (e : a = b) (x : fin a) : fin b := eq_rect a (fun t => fin t) x b e.

Lemma castf_refl : forall {a} (x : fin a), castf eq_refl x = x.
Proof. reflexivity. Qed.

Lemma castf_trans : forall {a b c} (e1 : a = b) (e2 : b = c) (x : fin a),
  castf e2 (castf e1 x) = castf (eq_trans e1 e2) x.
Proof. intros. destruct e1, e2. reflexivity. Qed.

Lemma castf_sym : forall {a b} (e : a = b) (x : fin a), castf (eq_sym e) (castf e x) = x.
Proof. intros. destruct e. reflexivity. Qed.

Lemma castf_eq_rect_r : forall {a b} (e : a = b) (x : fin a),
  castf e x = eq_rect_r (fun t => fin t) x (eq_sym e).
Proof. intros. unfold castf. destruct e. reflexivity. Qed.

Lemma shift_p_castf : forall {a b} p (e : a = b) (x : fin a),
  shift_p p (castf e x) = castf (f_equal (fun t => p + t) e) (shift_p p x).
Proof. intros. destruct e. reflexivity. Qed.

Lemma shift_p_ext : forall {p1 p2 q} (E : p1 = p2) (j : fin q),
  castf (f_equal (fun t => t + q) E) (shift_p p1 j) = shift_p p2 j.
Proof. intros. destruct E. reflexivity. Qed.

Lemma eq_rect_r_fun : forall {A B} {P : A -> Type} {x y} (e : y = x) (f : P x -> B) (z : P y),
  eq_rect_r (fun t => P t -> B) f e z = f (eq_rect_r P z (eq_sym e)).
Proof. intros. destruct e. cbn. reflexivity. Qed.

Lemma cast_fin_S' : forall {a b} (e : b = a) (x : fin a),
  eq_rect_r (fun t => fin t) (Some x : fin (S a)) (f_equal S e) = Some (eq_rect_r (fun t => fin t) x e).
Proof. intros. destruct e. reflexivity. Qed.

Lemma shift_p_add : forall {p q} (a : nat) (j : fin q),
  shift_p a (shift_p p j) = eq_rect_r (fun t => fin t) (shift_p (a + p) j) (Nat.add_assoc a p q).
Proof.
  intros p q a. induction a as [|a IH]; intros j.
  - cbn.
    rewrite (UIP_dec Nat.eq_dec (Nat.add_assoc 0 p q) eq_refl).
    cbn. reflexivity.
  - cbn.
    rewrite IH.
    change (Some (eq_rect_r (fun t => fin t) (shift_p (a + p) j) (Nat.add_assoc a p q))
          = eq_rect_r (fun t => fin t) (Some (shift_p (a + p) j) : fin (S (a + p + q))) (Nat.add_assoc (S a) p q)).
    erewrite (UIP_dec Nat.eq_dec (Nat.add_assoc (S a) p q) (f_equal S (Nat.add_assoc a p q))).
    symmetry. apply cast_fin_S'.
Qed.

(* shift_p_add in castf form *)
Lemma shift_p_add' : forall {p q} (a : nat) (j : fin q),
  shift_p a (shift_p p j) = castf (eq_sym (Nat.add_assoc a p q)) (shift_p (a + p) j).
Proof.
  intros. rewrite shift_p_add. rewrite castf_eq_rect_r. rewrite eq_sym_involutive. reflexivity.
Qed.

Lemma down_env_until_apply : forall {A} {n m} (H : m <= n) (g : fin n -> A) (j : fin m),
  down_env_until g m H j = g (eq_rect_r (fun t => fin t) (shift_p (n - m) j) (le_minus_plus m n H)).
Proof.
  intros A n m H g j.
  unfold down_env_until. unfold down_env_until'. unfold ren_env.
  set (z := shift_p (n - m) j).
  change (eq_rect_r (fun t : nat => fin t -> A) g (eq_sym (le_minus_plus m n H)) z
          = g (eq_rect_r (fun t => fin t) z (le_minus_plus m n H))).
  rewrite eq_rect_r_fun.
  rewrite (eq_sym_involutive (le_minus_plus m n H)).
  reflexivity.
Qed.

Definition dmap {m n} (H : m <= n) (j : fin m) : fin n :=
  castf (Nat.sub_add m n H) (shift_p (n - m) j).

Lemma down_env_until_apply' : forall {A} {n m} (H : m <= n) (g : fin n -> A) (j : fin m),
  down_env_until g m H j = g (dmap H j).
Proof.
  intros A n m H g j.
  rewrite down_env_until_apply.
  unfold dmap.
  rewrite castf_eq_rect_r.
  rewrite (UIP_dec Nat.eq_dec (le_minus_plus m n H) (eq_sym (Nat.sub_add m n H))).
  reflexivity.
Qed.

Lemma dmap_comp : forall {n m k} (Hk : k <= m) (Hm : m <= n) (j : fin k),
  dmap Hm (dmap Hk j) = dmap (Nat.le_trans k m n Hk Hm) j.
Proof.
  intros n m k Hk Hm j.
  unfold dmap.
  rewrite shift_p_castf.
  rewrite castf_trans.
  rewrite shift_p_add'.
  rewrite castf_trans.
  assert (E : n - m + (m - k) = n - k) by lia.
  rewrite <- (castf_sym (f_equal (fun t => t + k) E) (shift_p (n - m + (m - k)) j)).
  rewrite (shift_p_ext E).
  rewrite castf_trans.
  match goal with
  | |- castf ?e1 (shift_p (n - k) j) = castf ?e2 (shift_p (n - k) j) =>
      rewrite (UIP_dec Nat.eq_dec e1 e2); reflexivity
  end.
Qed.

Lemma down_env_until_apply_fun : forall {A} {n m} (H : m <= n) (g : fin n -> A),
  down_env_until g m H = (fun j => g (dmap H j)).
Proof.
  intros. apply functional_extensionality. intros j. apply down_env_until_apply'.
Qed.

Lemma down_env_until_comp : forall {A} {n m k} (Hk : k <= m) (Hm : m <= n) (g : fin n -> A),
  down_env_until (down_env_until g m Hm) k Hk
  = down_env_until g k (Nat.le_trans k m n Hk Hm).
Proof.
  intros A n m k Hk Hm g.
  rewrite (down_env_until_apply_fun Hm g).
  rewrite (down_env_until_apply_fun Hk (fun j => g (dmap Hm j))).
  apply functional_extensionality. intros j.
  rewrite (@down_env_until_apply' A n k (Nat.le_trans k m n Hk Hm) g j).
  rewrite dmap_comp. reflexivity.
Qed.

Lemma down_env_until_add : forall {n m} (H : m <= n) (g1 g2 : attrs n),
  down_env_until (g1 γ+ g2) m H = (down_env_until g1 m H) γ+ (down_env_until g2 m H).
Proof.
  intros n m H g1 g2.
  apply functional_extensionality. intros j.
  rewrite down_env_until_apply'.
  change ((g1 γ+ g2) (dmap H j) = down_env_until g1 m H j C+ down_env_until g2 m H j).
  rewrite down_env_until_apply'.
  rewrite down_env_until_apply'.
  reflexivity.
Qed.

Lemma castf_S : forall {a b} (e : a = b) (x : fin a),
  castf (f_equal S e) (Some x : fin (S a)) = Some (castf e x).
Proof. intros. destruct e. reflexivity. Qed.

Lemma dmap_cons_gen : forall {n m} (E : S (n - m) + m = S n) (Hn : m <= n) (j : fin m),
  castf E (shift_p (S (n - m)) j) = Some (dmap Hn j).
Proof.
  intros n m E Hn j.
  unfold dmap.
  erewrite (UIP_dec Nat.eq_dec E (f_equal S (Nat.sub_add m n Hn))).
  change (castf (f_equal S (Nat.sub_add m n Hn))
            (Some (shift_p (n - m) j) : fin (S (n - m + m)))
          = Some (castf (Nat.sub_add m n Hn) (shift_p (n - m) j))).
  rewrite castf_S.
  reflexivity.
Qed.

Lemma dmap_cons : forall {n m} (Hsn : m <= S n) (Hn : m <= n) (j : fin m),
  dmap Hsn j = Some (dmap Hn j).
Proof.
  intros n m Hsn Hn j.
  unfold dmap.
  assert (Esub : S n - m = S (n - m)) by lia.
  rewrite <- (castf_sym (f_equal (fun t => t + m) Esub) (shift_p (S n - m) j)).
  rewrite (shift_p_ext Esub).
  rewrite castf_trans.
  exact (@dmap_cons_gen n m
           (eq_trans (eq_sym (f_equal (fun t => t + m) Esub)) (Nat.sub_add m (S n) Hsn))
           Hn j).
Qed.

Lemma down_env_until_cons : forall {n m} (q : attr) (g : attrs n) (Hsn : m <= S n) (Hn : m <= n),
  down_env_until (q .: g) m Hsn = down_env_until g m Hn.
Proof.
  intros n m q g Hsn Hn.
  apply functional_extensionality. intros j.
  rewrite down_env_until_apply'.
  rewrite down_env_until_apply'.
  rewrite (@dmap_cons n m Hsn Hn j).
  reflexivity.
Qed.

Lemma dmap_zero : forall {k n} (E : k + n = n) (j : fin n), k = 0 -> castf E (shift_p k j) = j.
Proof.
  intros k n E j Hk.
  subst k.
  cbn.
  rewrite (UIP_dec Nat.eq_dec E eq_refl).
  cbn. reflexivity.
Qed.

(* ---------- PadTo: Strict-prefixed contexts ---------- *)
Inductive PadTo : forall {N}, attrs N -> forall {K}, attrs K -> Prop :=
  | pad_to_refl : forall {K} (v : attrs K), PadTo v v
  | pad_to_cons : forall {N K} (v : attrs N) (w : attrs K), K <= N -> PadTo v w -> PadTo (Strict .: v) w.
Arguments pad_to_refl {K} v.
Arguments pad_to_cons {N K} v w _ _.

Lemma down_env_until_full : forall {A} {n} (g : fin n -> A) (H : n <= n), down_env_until g n H = g.
Proof.
  intros A n g H.
  apply functional_extensionality. intros j.
  rewrite down_env_until_apply'.
  unfold dmap.
  (* castf (Nat.sub_add n n H) (shift_p (n-n) j) = j *)
  assert (E0 : n - n = 0) by apply Nat.sub_diag.
  assert (Hz : castf (Nat.sub_add n n H) (shift_p (n - n) j) = j).
  { apply (@dmap_zero (n-n) n (Nat.sub_add n n H) j E0). }
  rewrite Hz. reflexivity.
Qed.

Lemma PadTo_size : forall {N} (g : attrs N) {K} (gK : attrs K), PadTo g gK -> K <= N.
Proof.
  intros N g K gK Hp. induction Hp.
  - apply Nat.le_refl.
  - lia.
Qed.

Lemma PadTo_down : forall {N} (g : attrs N) {K} (gK : attrs K) (HK : K <= N),
  PadTo g gK -> gK = down_env_until g K HK.
Proof.
  intros N g K gK HK Hp. induction Hp.
  - symmetry. apply down_env_until_full.
  - rewrite (@down_env_until_cons N K Strict v HK H).
    apply IHHp.
Qed.

Lemma dmap_id : forall {n} (H : n <= n) (j : fin n), dmap H j = j.
Proof.
  intros n H j. unfold dmap.
  apply (@dmap_zero (n - n) n (Nat.sub_add n n H) j (Nat.sub_diag n)).
Qed.

Lemma PadTo_decomp : forall {N} (g : attrs N) {K} (gK : attrs K) (HK : K <= N),
  PadTo g gK -> forall i : fin N, (exists j : fin K, i = dmap HK j) \/ g i = Strict.
Proof.
  intros N g K gK HK Hp. induction Hp.
  - intros i. left. exists i. symmetry. apply dmap_id.
  - intros i. destruct i as [i'|].
    + specialize (IHHp H i'). destruct IHHp as [[j Hj] | Hv].
      * left. exists j. rewrite Hj. rewrite (@dmap_cons N K HK H j). reflexivity.
      * right. exact Hv.
    + right. reflexivity.
Qed.

Lemma le_proof_irrel : forall {m n} (H1 H2 : m <= n), H1 = H2.
Proof. intros. apply le_unique. Qed.

Lemma down_env_until_H_irrel : forall {A} {n m} (H1 H2 : m <= n) (g : fin n -> A),
  down_env_until g m H1 = down_env_until g m H2.
Proof. intros. rewrite (le_proof_irrel H1 H2). reflexivity. Qed.

Lemma dmap_H_irrel : forall {m n} (H1 H2 : m <= n) (j : fin m), dmap H1 j = dmap H2 j.
Proof.
  intros. rewrite (le_proof_irrel H1 H2). reflexivity.
Qed.

Lemma dmap_cast : forall {m1 m2 n} (Heq : m1 = m2) (H1 : m1 <= n) (H2 : m2 <= n) (j : fin m2),
  dmap H1 (eq_rect_r (fun t => fin t) j Heq) = dmap H2 j.
Proof.
  intros. destruct Heq. cbn. apply dmap_H_irrel.
Qed.

Lemma eq_rect_r_fun_attrs : forall {x y} (e : y = x) (f : attrs x) (j : fin y),
  eq_rect_r (fun t => attrs t) f e j = f (eq_rect_r (fun t => fin t) j (eq_sym e)).
Proof. intros. destruct e. cbn. reflexivity. Qed.

Lemma dep_constr_eq : forall {A X} (P : A -> Type) (F : forall t, P t -> X) {x y} (e : x = y) (p : P x) (q : P y),
  eq_rect_r P q e = p -> F x p = F y q.
Proof.
  intros A X P F x y e.
  destruct e.
  cbn.
  intros p q H.
  rewrite H. reflexivity.
Qed.

Lemma down_clos_comp : forall {k} (C : Clos k) j1 j2,
  down_clos j2 (down_clos j1 C) = down_clos (Nat.min j1 j2) C.
Proof.
  intros k C.
  induction C as [| |mo mi g' rho Mb|W1 IH1 W2 IH2|W IH|W IH|W IH|mo mi g' rho Mb];
    intros j1 j2; cbn.
  - reflexivity.
  - reflexivity.
  - apply (@dep_constr_eq nat (Clos ValFlag) attrs
             (fun t a => Thunk t mi a rho M)
             (Nat.min (Nat.min mo j1) j2) (Nat.min mo (Nat.min j1 j2))
             (eq_sym (Nat.min_assoc mo j1 j2))
             (down_env_until (down_env_until g' (Nat.min mo j1) (min_le mo j1))
                (Nat.min (Nat.min mo j1) j2) (min_le (Nat.min mo j1) j2))
             (down_env_until g' (Nat.min mo (Nat.min j1 j2)) (min_le mo (Nat.min j1 j2)))).
    apply functional_extensionality. intros j.
    erewrite eq_rect_r_fun_attrs.
    rewrite down_env_until_apply'.
    rewrite down_env_until_apply'.
    rewrite down_env_until_apply'.
    rewrite (eq_sym_involutive (Nat.min_assoc mo j1 j2)).
    rewrite (@dmap_cast (Nat.min mo (Nat.min j1 j2)) (Nat.min (Nat.min mo j1) j2) mo
               (Nat.min_assoc mo j1 j2) (min_le mo (Nat.min j1 j2))
               (Nat.le_trans _ _ _ (min_le (Nat.min mo j1) j2) (min_le mo j1)) j).
    rewrite dmap_comp.
    reflexivity.
  - rewrite IH1. rewrite IH2. reflexivity.
  - rewrite IH. reflexivity.
  - rewrite IH. reflexivity.
  - rewrite IH. reflexivity.
  - apply (@dep_constr_eq nat (Clos CompFlag) attrs
             (fun t a => Closure t mi a rho M)
             (Nat.min (Nat.min mo j1) j2) (Nat.min mo (Nat.min j1 j2))
             (eq_sym (Nat.min_assoc mo j1 j2))
             (down_env_until (down_env_until g' (Nat.min mo j1) (min_le mo j1))
                (Nat.min (Nat.min mo j1) j2) (min_le (Nat.min mo j1) j2))
             (down_env_until g' (Nat.min mo (Nat.min j1 j2)) (min_le mo (Nat.min j1 j2)))).
    apply functional_extensionality. intros j.
    erewrite eq_rect_r_fun_attrs.
    rewrite down_env_until_apply'.
    rewrite down_env_until_apply'.
    rewrite down_env_until_apply'.
    rewrite (eq_sym_involutive (Nat.min_assoc mo j1 j2)).
    rewrite (@dmap_cast (Nat.min mo (Nat.min j1 j2)) (Nat.min (Nat.min mo j1) j2) mo
               (Nat.min_assoc mo j1 j2) (min_le mo (Nat.min j1 j2))
               (Nat.le_trans _ _ _ (min_le (Nat.min mo j1) j2) (min_le mo j1)) j).
    rewrite dmap_comp.
    reflexivity.
Qed.


Lemma down_clos_small : forall {k} (C : Clos k) m n, m <= n ->
  down_clos m (down_clos n C) = down_clos m C.
Proof.
  intros k C m n Hmn.
  rewrite down_clos_comp.
  rewrite (Nat.min_r n m Hmn).
  reflexivity.
Qed.

Lemma down_clos_same : forall {k} (C : Clos k) n, down_clos n (down_clos n C) = down_clos n C.
Proof.
  intros. rewrite down_clos_comp. rewrite (Nat.min_r n n (Nat.le_refl n)). reflexivity.
Qed.

Lemma down_clos_scope_eq : forall {k} (C : Clos k) j1 j2, j1 = j2 -> down_clos j1 C = down_clos j2 C.
Proof. intros. subst. reflexivity. Qed.

Lemma LR_ws : forall {n k} (T : Ty n k) (C : Clos k) (mLower : nat) (gCtx : attrs n),
  LR T C mLower gCtx -> down_clos n C = C.
Proof.
  intros n k T. induction T as [|g0 B IHB|A1 IH1 A2 IH2|A1 IH1 A2 IH2|q A0 IH0 B IHB|A IHA];
    intros C mLower gCtx Hlr; cbn in *.
  - (* VUnit *) subst C. cbn. reflexivity.
  - (* VThunk *)
    destruct Hlr as (mo & mi & gsc & gInner & rho & M & HInner & Hn & HLow & Hd1 & Hd2 & HC & Hcl).
    subst C. cbn.
    apply (@dep_constr_eq nat (Clos ValFlag) attrs (fun t a => Thunk t mi a rho M)
             (Nat.min mo n) mo (Nat.min_l mo n Hn)
             (down_env_until gsc (Nat.min mo n) (min_le mo n)) gsc).
    apply functional_extensionality. intros j.
    erewrite eq_rect_r_fun_attrs.
    rewrite down_env_until_apply'.
    symmetry.
    rewrite <- (@dmap_cast mo (Nat.min mo n) mo (eq_sym (Nat.min_l mo n Hn))
               (Nat.le_refl mo) (min_le mo n) j).
    rewrite dmap_id. reflexivity.
  - (* VProd *)
    destruct Hlr as (W1 & W2 & HC & H1 & H2). subst C.
    cbn. rewrite (IH1 W1 mLower gCtx H1). rewrite (IH2 W2 mLower gCtx H2). reflexivity.
  - (* VSum *)
    destruct Hlr as (W & [ (HC & H1) | (HC & H2) ]); subst C; cbn;
      [ rewrite (IH1 W mLower gCtx H1); reflexivity | rewrite (IH2 W mLower gCtx H2); reflexivity ].
  - (* CAbs *)
    destruct Hlr as (mo & mi & gsc & gInner & rho & M & Hn & HInner & HLow & Hd2 & HC & Hcl).
    subst C. cbn.
    apply (@dep_constr_eq nat (Clos CompFlag) attrs (fun t a => Closure t mi a rho M)
             (Nat.min mo n) mo (Nat.min_l mo n Hn)
             (down_env_until gsc (Nat.min mo n) (min_le mo n)) gsc).
    apply functional_extensionality. intros j.
    erewrite eq_rect_r_fun_attrs.
    rewrite down_env_until_apply'.
    symmetry.
    rewrite <- (@dmap_cast mo (Nat.min mo n) mo (eq_sym (Nat.min_l mo n Hn))
               (Nat.le_refl mo) (min_le mo n) j).
    rewrite dmap_id. reflexivity.
  - (* CF *)
    destruct Hlr as (W & HC & HW). subst C.
    cbn. rewrite (IHA W mLower gCtx HW). reflexivity.
Qed.

Definition LR_up_prop {n k} (T : Ty n k) : Prop :=
  forall (C : Clos k) (mLower : nat) (gCtx : attrs n) (q : attr),
    LR T C mLower gCtx -> LR (up_Ty q T) C mLower (Strict .: gCtx).

Definition LR_down_prop {n k} (T : Ty n k) : Prop :=
  forall (K : nat) (HK : K <= n) (mLower : nat) (Hml : mLower <= K)
         (C : Clos k) (gCtx : attrs n) (gK : attrs K),
    gK = down_env_until gCtx K HK ->
    LR T C mLower gCtx -> LR (down_ty_until T K HK) (down_clos K C) mLower gK.

Definition LR_lift_prop {n k} (T : Ty n k) : Prop :=
  forall (K : nat) (HK : K <= n) (mLower : nat)
         (C : Clos k) (gCtx : attrs n) (gK : attrs K),
    gK = down_env_until gCtx K HK ->
    LR (down_ty_until T K HK) C mLower gK -> LR T C mLower gCtx.

Definition LR_downup_prop {n k} (T : Ty n k) : Prop :=
  forall (C : Clos k) (mLower : nat) (Hml : mLower <= n) (gCtx : attrs n) (q : attr),
    LR (up_Ty q T) C mLower (Strict .: gCtx) -> LR T (down_clos n C) mLower gCtx.

Definition LR_props {n k} (T : Ty n k) : Prop :=
  LR_up_prop T /\ LR_down_prop T /\ LR_lift_prop T /\ LR_downup_prop T.

Lemma LR_all : forall {n k} (T : Ty n k), LR_props T.
Proof.
  intros n k T.
  induction T as [|g0 B IHB|A1 IH1 A2 IH2|A1 IH1 A2 IH2|q0 A0 IH0 B IHB|A IHA].
  - (* VUnit *)
    split; [|split;[|split]].
    + intros C mLower gCtx q Hlr. cbn in Hlr. subst C. cbn. reflexivity.
    + intros K HK mLower Hml C gCtx gK Hctx Hlr. cbn in Hlr. subst C. cbn. reflexivity.
    + intros K HK mLower C gCtx gK Hctx Hlr. cbn in Hlr. subst C. cbn. reflexivity.
    + intros C mLower Hml gCtx q Hlr. cbn in Hlr. subst C. cbn. reflexivity.
  - (* VThunk *)
    destruct IHB as (upB & dnB & lfB & duB).
    split; [|split;[|split]].
    + (* up *)
      intros C mLower gCtx q Hlr. cbn in Hlr.
      destruct Hlr as (mo & mi & gsc & gInner & rho & M & HInner & Hn & HLow & Hd1 & Hd2 & HC & Hcl).
      cbn.
      assert (HleSn : mo <= S n) by lia.
      assert (HmlN : mLower <= n) by lia.
      eexists mo, mi, gsc, gInner, rho, M.
      exists HInner, HleSn, HLow.
      split; [ rewrite (@down_env_until_cons n mo q g0 HleSn Hn); exact Hd1 |].
      split; [ exact Hd2 |].
      split; [ exact HC |].
      intros Hnl Hstr.
      assert (Hstr0 : down_env_until gCtx mLower HmlN γS<= down_env_until g0 mLower HmlN).
      { intro j.
        rewrite <- (@down_env_until_cons n mLower Strict gCtx Hnl HmlN).
        rewrite <- (@down_env_until_cons n mLower q g0 Hnl HmlN).
        apply Hstr. }
      destruct (Hcl HmlN Hstr0) as (T & Hev & HlrB).
      exists T. split; [ exact Hev | apply upB; exact HlrB ].
    + (* down *)
      intros K HK mLower Hml C gCtx gK Hctx Hlr. cbn in Hlr.
      destruct Hlr as (mo & mi & gsc & gInner & rho & M & HInner & Hn & HLow & Hd1 & Hd2 & HC & Hcl).
      subst C. cbn.
      assert (HleKm : min mo K <= mi) by lia.
      assert (HleKk : min mo K <= K) by lia.
      assert (Hml' : mLower <= min mo K) by lia.
      assert (HmN : mLower <= n) by lia.
      eexists (min mo K), mi, (down_env_until gsc (min mo K) (min_le mo K)), gInner, rho, M.
      exists HleKm, HleKk, Hml'.
      split.
      { rewrite <- Hd1.
        rewrite (@down_env_until_comp attr n K (min mo K) HleKk HK g0).
        rewrite (@down_env_until_comp attr n mo (min mo K) (min_le mo K) Hn g0).
        erewrite down_env_until_H_irrel. reflexivity. }
      split.
      { rewrite <- Hd2.
        rewrite (@down_env_until_comp attr mi mo (min mo K) (min_le mo K) HInner gInner).
        erewrite down_env_until_H_irrel. reflexivity. }
      split; [reflexivity|].
      intros Hnl Hstr.
      assert (Hstr0 : down_env_until gCtx mLower HmN γS<= down_env_until g0 mLower HmN).
      { intro j.
        erewrite (@down_env_until_H_irrel attr n mLower HmN
                    (Nat.le_trans mLower K n Hml HK) gCtx).
        erewrite (@down_env_until_H_irrel attr n mLower HmN
                    (Nat.le_trans mLower K n Hml HK) g0).
        rewrite <- (@down_env_until_comp attr n K mLower Hml HK gCtx).
        rewrite <- Hctx.
        rewrite <- (@down_env_until_comp attr n K mLower Hml HK g0).
        rewrite (@down_env_until_H_irrel attr K mLower Hml Hnl gK).
        rewrite (@down_env_until_H_irrel attr K mLower Hml Hnl (down_env_until g0 K HK)).
        apply Hstr. }
      destruct (Hcl HmN Hstr0) as (T & Hev & HlrB).
      exists T. split; [ exact Hev |].
      assert (Hd := dnB K HK mLower Hml (mo T↓ T) gCtx gK Hctx HlrB).
      unfold down_comp in Hd.
      rewrite down_clos_comp in Hd. exact Hd.
    + (* lift *)
      intros K HK mLower C gCtx gK Hctx Hlr. cbn in Hlr.
      destruct Hlr as (mo & mi & gsc & gInner & rho & M & HInner & Hn & HLow & Hd1 & Hd2 & HC & Hcl).
      assert (HnN : mo <= n) by lia.
      assert (HmlK : mLower <= K) by lia.
      eexists mo, mi, gsc, gInner, rho, M.
      exists HInner, HnN, HLow.
      split.
      { rewrite <- Hd1.
        rewrite (@down_env_until_comp attr n K mo Hn HK g0).
        erewrite down_env_until_H_irrel. reflexivity. }
      split; [ exact Hd2 |].
      split; [ exact HC |].
      intros Hnl Hstr.
      assert (Hstr0 : down_env_until gK mLower HmlK γS<= down_env_until (down_env_until g0 K HK) mLower HmlK).
      { intro j.
        rewrite Hctx.
        rewrite (@down_env_until_comp attr n K mLower HmlK HK gCtx).
        rewrite (@down_env_until_comp attr n K mLower HmlK HK g0).
        rewrite (@down_env_until_H_irrel attr n mLower
                   (Nat.le_trans mLower K n HmlK HK) Hnl gCtx).
        rewrite (@down_env_until_H_irrel attr n mLower
                   (Nat.le_trans mLower K n HmlK HK) Hnl g0).
        apply Hstr. }
      destruct (Hcl HmlK Hstr0) as (T & Hev & HlrB).
      exists T. split; [ exact Hev | exact (lfB K HK mLower (mo T↓ T) gCtx gK Hctx HlrB) ].
    + (* downup *)
      intros C mLower Hml gCtx q Hlr. cbn in Hlr.
      destruct Hlr as (mo & mi & gsc & gInner & rho & M & HInner & Hn & HLow & Hd1 & Hd2 & HC & Hcl).
      subst C. cbn.
      assert (Hle : min mo n <= mi) by lia.
      assert (Hlen : min mo n <= n) by lia.
      assert (Hml' : mLower <= min mo n) by lia.
      assert (HleS : mLower <= S n) by lia.
      eexists (min mo n), mi, (down_env_until gsc (min mo n) (min_le mo n)), gInner, rho, M.
      exists Hle, Hlen, Hml'.
      split.
      { rewrite <- Hd1.
        rewrite (@down_env_until_comp attr (S n) mo (min mo n) (min_le mo n) Hn (q .: g0)).
        rewrite (@down_env_until_cons n (min mo n) q g0 (Nat.le_trans (Nat.min mo n) mo (S n) (min_le mo n) Hn) Hlen).
        erewrite down_env_until_H_irrel. reflexivity. }
      split.
      { rewrite <- Hd2.
        rewrite (@down_env_until_comp attr mi mo (min mo n) (min_le mo n) HInner gInner).
        erewrite down_env_until_H_irrel. reflexivity. }
      split; [reflexivity|].
      intros Hnl Hstr.
      assert (Hstr0 : down_env_until (Strict .: gCtx) mLower HleS γS<= down_env_until (q .: g0) mLower HleS).
      { intro j.
        rewrite (@down_env_until_cons n mLower Strict gCtx HleS Hml).
        rewrite (@down_env_until_cons n mLower q g0 HleS Hml).
        rewrite (@down_env_until_H_irrel attr n mLower Hml Hnl gCtx).
        rewrite (@down_env_until_H_irrel attr n mLower Hml Hnl g0).
        apply Hstr. }
      destruct (Hcl HleS Hstr0) as (T & Hev & HlrB).
      exists T. split; [ exact Hev |].
      assert (Hd := duB (mo T↓ T) mLower Hml gCtx q HlrB).
      unfold down_comp in Hd.
      rewrite down_clos_comp in Hd. exact Hd.
  - (* VProd *)
    destruct IH1 as (up1 & dn1 & lf1 & du1).
    destruct IH2 as (up2 & dn2 & lf2 & du2).
    split; [|split;[|split]].
    + intros C mLower gCtx q Hlr. cbn in Hlr.
      destruct Hlr as (W1 & W2 & HC & H1 & H2). subst C. cbn.
      exists W1, W2. split; [reflexivity|split]; [apply up1; assumption | apply up2; assumption].
    + intros K HK mLower Hml C gCtx gK Hctx Hlr. cbn in Hlr.
      destruct Hlr as (W1 & W2 & HC & H1 & H2). subst C. cbn.
      exists (down_clos K W1), (down_clos K W2). split; [reflexivity|split].
      * apply (dn1 K HK mLower Hml W1 gCtx gK Hctx H1).
      * apply (dn2 K HK mLower Hml W2 gCtx gK Hctx H2).
    + intros K HK mLower C gCtx gK Hctx Hlr. cbn in Hlr.
      destruct Hlr as (W1 & W2 & HC & H1 & H2). subst C. cbn.
      exists W1, W2. split; [reflexivity|split].
      * apply (lf1 K HK mLower W1 gCtx gK Hctx H1).
      * apply (lf2 K HK mLower W2 gCtx gK Hctx H2).
    + intros C mLower Hml gCtx q Hlr. cbn in Hlr.
      destruct Hlr as (W1 & W2 & HC & H1 & H2). subst C. cbn.
      exists (down_clos n W1), (down_clos n W2). split; [reflexivity|split].
      * apply (du1 W1 mLower Hml gCtx q H1).
      * apply (du2 W2 mLower Hml gCtx q H2).
  - (* VSum *)
    destruct IH1 as (up1 & dn1 & lf1 & du1).
    destruct IH2 as (up2 & dn2 & lf2 & du2).
    split; [|split;[|split]].
    + intros C mLower gCtx q Hlr. cbn in Hlr.
      destruct Hlr as (W & [ (HC & H1) | (HC & H2) ]); subst C; cbn.
      * exists W; left; split; [reflexivity | apply up1; assumption].
      * exists W; right; split; [reflexivity | apply up2; assumption].
    + intros K HK mLower Hml C gCtx gK Hctx Hlr. cbn in Hlr.
      destruct Hlr as (W & [ (HC & H1) | (HC & H2) ]); subst C; cbn.
      * exists (down_clos K W); left; split; [reflexivity | apply (dn1 K HK mLower Hml W gCtx gK Hctx H1)].
      * exists (down_clos K W); right; split; [reflexivity | apply (dn2 K HK mLower Hml W gCtx gK Hctx H2)].
    + intros K HK mLower C gCtx gK Hctx Hlr. cbn in Hlr.
      destruct Hlr as (W & [ (HC & H1) | (HC & H2) ]); subst C; cbn.
      * exists W; left; split; [reflexivity | apply (lf1 K HK mLower W gCtx gK Hctx H1)].
      * exists W; right; split; [reflexivity | apply (lf2 K HK mLower W gCtx gK Hctx H2)].
    + intros C mLower Hml gCtx q Hlr. cbn in Hlr.
      destruct Hlr as (W & [ (HC & H1) | (HC & H2) ]); subst C; cbn.
      * exists (down_clos n W); left; split; [reflexivity | apply (du1 W mLower Hml gCtx q H1)].
      * exists (down_clos n W); right; split; [reflexivity | apply (du2 W mLower Hml gCtx q H2)].
  - (* CAbs *)
    destruct IH0 as (up0 & dn0 & lf0 & du0).
    destruct IHB as (upB & dnB & lfB & duB).
    split; [|split;[|split]].
    + (* up *)
      intros C mLower gCtx q Hlr. cbn in Hlr.
      destruct Hlr as (mo & mi & gsc & gInner & rho & M & Hn & HInner & HLow & Hd2 & HC & Hcl).
      subst C. cbn.
      assert (HnS : mo <= S n) by lia.
      assert (HmlN : mLower <= n) by lia.
      eexists mo, mi, gsc, gInner, rho, M.
      exists HnS, HInner, HLow.
      split; [ exact Hd2 |].
      split; [reflexivity|].
      intros W HWu.
      pose proof (du0 W mLower HmlN gCtx q HWu) as HWa.
      destruct (Hcl (down_clos n W) HWa) as (T & Hev & HlrB).
      exists T. split; [ | exact (upB (mo T↓ T) mLower gCtx q HlrB) ].
      unfold down_value in Hev. unfold down_value.
      rewrite (down_clos_small W mo n Hn) in Hev.
      exact Hev.
    + (* down *)
      intros K HK mLower Hml C gCtx gK Hctx Hlr. cbn in Hlr.
      destruct Hlr as (mo & mi & gsc & gInner & rho & M & Hn & HInner & HLow & Hd2 & HC & Hcl).
      subst C. cbn.
      assert (HleKm : min mo K <= mi) by lia.
      assert (HleKk : min mo K <= K) by lia.
      assert (Hml' : mLower <= min mo K) by lia.
      eexists (min mo K), mi, (down_env_until gsc (min mo K) (min_le mo K)), gInner, rho, M.
      exists HleKk, HleKm, Hml'.
      split.
      { rewrite <- Hd2.
        rewrite (@down_env_until_comp attr mi mo (min mo K) (min_le mo K) HInner gInner).
        erewrite down_env_until_H_irrel. reflexivity. }
      split; [reflexivity|].
      intros W HWd.
      pose proof (lf0 K HK mLower W gCtx gK Hctx HWd) as HWa.
      destruct (Hcl W HWa) as (T & Hev & HlrB).
      exists T. split; [ | ].
      * unfold down_value in Hev. unfold down_value.
        pose proof (LR_ws (down_ty_until A0 K HK) W mLower gK HWd) as HWws.
        rewrite <- HWws in Hev.
        rewrite down_clos_comp in Hev.
        rewrite Nat.min_comm in Hev.
        exact Hev.
      * assert (Hd := dnB K HK mLower Hml (mo T↓ T) gCtx gK Hctx HlrB).
        unfold down_comp in Hd. rewrite down_clos_comp in Hd. exact Hd.
    + (* lift *)
      intros K HK mLower C gCtx gK Hctx Hlr. cbn in Hlr.
      destruct Hlr as (mo & mi & gsc & gInner & rho & M & Hn & HInner & HLow & Hd2 & HC & Hcl).
      subst C.
      assert (HnN : mo <= n) by lia.
      assert (HmlK : mLower <= K) by lia.
      eexists mo, mi, gsc, gInner, rho, M.
      exists HnN, HInner, HLow.
      split; [ exact Hd2 |].
      split; [reflexivity|].
      intros W HWa.
      pose proof (dn0 K HK mLower HmlK W gCtx gK Hctx HWa) as HWd.
      destruct (Hcl (down_clos K W) HWd) as (T & Hev & HlrB).
      exists T. split; [ | exact (lfB K HK mLower (mo T↓ T) gCtx gK Hctx HlrB) ].
      unfold down_value in Hev. unfold down_value.
      rewrite (down_clos_small W mo K Hn) in Hev.
      exact Hev.
    + (* downup *)
      intros C mLower Hml gCtx q Hlr. cbn in Hlr.
      destruct Hlr as (mo & mi & gsc & gInner & rho & M & Hn & HInner & HLow & Hd2 & HC & Hcl).
      subst C. cbn.
      assert (Hle : min mo n <= mi) by lia.
      assert (Hlen : min mo n <= n) by lia.
      assert (Hml' : mLower <= min mo n) by lia.
      eexists (min mo n), mi, (down_env_until gsc (min mo n) (min_le mo n)), gInner, rho, M.
      exists Hlen, Hle, Hml'.
      split.
      { rewrite <- Hd2.
        rewrite (@down_env_until_comp attr mi mo (min mo n) (min_le mo n) HInner gInner).
        erewrite down_env_until_H_irrel. reflexivity. }
      split; [reflexivity|].
      intros W HWa.
      pose proof (up0 W mLower gCtx q HWa) as HWu.
      destruct (Hcl W HWu) as (T & Hev & HlrB).
      exists T. split; [ | ].
      * unfold down_value in Hev. unfold down_value.
        pose proof (LR_ws A0 W mLower gCtx HWa) as HWws.
        rewrite <- HWws in Hev.
        rewrite down_clos_comp in Hev.
        rewrite Nat.min_comm in Hev.
        exact Hev.
      * assert (Hd := duB (mo T↓ T) mLower Hml gCtx q HlrB).
        unfold down_comp in Hd. rewrite down_clos_comp in Hd. exact Hd.
  - (* CF *)
    destruct IHA as (upA & dnA & lfA & duA).
    split; [|split;[|split]].
    + intros C mLower gCtx q Hlr. cbn in Hlr. destruct Hlr as (W & HC & HW). subst C. cbn. exists W. split; [reflexivity | apply upA; assumption].
    + intros K HK mLower Hml C gCtx gK Hctx Hlr. cbn in Hlr. destruct Hlr as (W & HC & HW). subst C. cbn.
      exists (down_clos K W). split; [reflexivity | apply (dnA K HK mLower Hml W gCtx gK Hctx HW)].
    + intros K HK mLower C gCtx gK Hctx Hlr. cbn in Hlr. destruct Hlr as (W & HC & HW). subst C. cbn.
      exists W. split; [reflexivity | apply (lfA K HK mLower W gCtx gK Hctx HW)].
    + intros C mLower Hml gCtx q Hlr. cbn in Hlr. destruct Hlr as (W & HC & HW). subst C. cbn.
      exists (down_clos n W). split; [reflexivity | apply (duA W mLower Hml gCtx q HW)].
Unshelve.
all: try lia.
all: try (match goal with |- ?G => fail 1 "REMAINS:" G end).
Qed.

(* ---------- attribute helper lemmas ---------- *)
Lemma attr_stricter_lazy : forall a b, a S<= b -> a = Lazy -> b = Lazy.
Proof.
  intros a b H E. subst a. destruct b; cbn in *; try discriminate; try contradiction; reflexivity.
Qed.

Lemma attr_stricter_of_lazy : forall a b, a = Lazy -> b = Lazy -> a S<= b.
Proof. intros. subst. reflexivity. Qed.

Lemma attr_add_lazy_l : forall a b, a C+ b = Lazy -> a = Lazy.
Proof. intros a b E. destruct a, b; cbn in *; try discriminate; try contradiction; reflexivity. Qed.

Lemma attr_add_lazy_r : forall a b, a C+ b = Lazy -> b = Lazy.
Proof. intros a b E. destruct a, b; cbn in *; try discriminate; try contradiction; reflexivity. Qed.

Lemma attr_le_lazy : forall a b, a C<= b -> a = Lazy -> b = Lazy.
Proof. intros a b H E. subst a. destruct b; cbn in *; try discriminate; try contradiction; reflexivity. Qed.

Lemma attr_stricter_add_l : forall a b c, a S<= (b C+ c) -> a = Lazy -> b = Lazy.
Proof. intros a b c H E. subst a. destruct b, c; cbn in *; try discriminate; try contradiction; reflexivity. Qed.

Lemma attr_stricter_add_r : forall a b c, a S<= (b C+ c) -> a = Lazy -> c = Lazy.
Proof. intros a b c H E. subst a. destruct b, c; cbn in *; try discriminate; try contradiction; reflexivity. Qed.

Lemma attr_stricter_add_l_pt : forall a b c, a S<= (b C+ c) -> a S<= b.
Proof.
  intros a b c H. destruct a, b, c; cbn in *; try (exfalso; assumption); reflexivity.
Qed.

Lemma attr_stricter_add_r_pt : forall a b c, a S<= (b C+ c) -> a S<= c.
Proof.
  intros a b c H. destruct a, b, c; cbn in *; try (exfalso; assumption); reflexivity.
Qed.

Lemma attr_stricter_le_pt : forall a b b', a S<= b -> b C<= b' -> a S<= b'.
Proof.
  intros a b b' H1 H2. destruct a, b, b'; cbn in *; try (exfalso; assumption); reflexivity.
Qed.

Lemma stricter_add_l : forall {n} (gCtx g1 g2 : attrs n) mLower (Hnl : mLower <= n),
  (down_env_until gCtx mLower Hnl) γS<= (down_env_until (g1 γ+ g2) mLower Hnl) ->
  (down_env_until gCtx mLower Hnl) γS<= (down_env_until g1 mLower Hnl).
Proof.
  intros n gCtx g1 g2 mLower Hnl Hstr j.
  specialize (Hstr j).
  rewrite down_env_until_add in Hstr.
  exact (attr_stricter_add_l_pt _ _ _ Hstr).
Qed.

Lemma stricter_add_r : forall {n} (gCtx g1 g2 : attrs n) mLower (Hnl : mLower <= n),
  (down_env_until gCtx mLower Hnl) γS<= (down_env_until (g1 γ+ g2) mLower Hnl) ->
  (down_env_until gCtx mLower Hnl) γS<= (down_env_until g2 mLower Hnl).
Proof.
  intros n gCtx g1 g2 mLower Hnl Hstr j.
  specialize (Hstr j).
  rewrite down_env_until_add in Hstr.
  exact (attr_stricter_add_r_pt _ _ _ Hstr).
Qed.

Lemma stricter_sub : forall {n} (gCtx g g' : attrs n) mLower (Hnl : mLower <= n),
  (down_env_until gCtx mLower Hnl) γS<= (down_env_until g mLower Hnl) ->
  g γ<= g' ->
  (down_env_until gCtx mLower Hnl) γS<= (down_env_until g' mLower Hnl).
Proof.
  intros n gCtx g g' mLower Hnl Hstr Hle j.
  specialize (Hstr j).
  apply (attr_stricter_le_pt _ _ _ Hstr).
  rewrite down_env_until_apply'. rewrite down_env_until_apply'.
  apply Hle.
Qed.

Lemma pad_liveness : forall {n} (gCtx g : attrs n) mLower (Hnl : mLower <= n) v,
  PadTo gCtx v ->
  down_env_until gCtx mLower Hnl = v ->
  (down_env_until gCtx mLower Hnl) γS<= (down_env_until g mLower Hnl) ->
  forall i, g i <> Lazy -> gCtx i <> Lazy.
Proof.
  intros n gCtx g mLower Hnl v Hpad Hdown Hstr i Hgi.
  destruct (@PadTo_decomp n gCtx mLower v Hnl Hpad i) as [[j Hj] | Hst].
  - rewrite Hj. intro Hc.
    assert (Hgl : down_env_until gCtx mLower Hnl j = Lazy).
    { rewrite down_env_until_apply'. rewrite Hc. reflexivity. }
    assert (Hg2 : down_env_until g mLower Hnl j = Lazy).
    { exact (attr_stricter_lazy _ _ (Hstr j) Hgl). }
    rewrite down_env_until_apply' in Hg2.
    apply Hgi. rewrite Hj. exact Hg2.
  - rewrite Hst. intro Hc. discriminate Hc.
Qed.

Definition NonAbs {k : Kind} (W : Clos k) : Prop :=
  match k as k0 return Clos k0 -> Prop with
  | ValFlag => fun W => W <> Absent
  | CompFlag => fun _ => True
  end W.

Lemma LR_nonabs_all : forall {n k} (A : Ty n k) (W : Clos k) mLower gCtx,
  LR A W mLower gCtx -> NonAbs W.
Proof.
  intros n k A. induction A as [|g0 B IHB|A1 IH1 A2 IH2|A1 IH1 A2 IH2|q0 A0 IH0 B IHB|A IHA];
    intros W mLower gCtx Hlr; cbn in Hlr.
  - subst W. intro Hc. discriminate Hc.
  - destruct Hlr as (mo & mi & gsc & gInner & rho & M & HInner & Hn & HLow & Hd1 & Hd2 & HC & Hcl).
    subst W. intro Hc. discriminate Hc.
  - destruct Hlr as (W1 & W2 & HC & H1 & H2). subst W. intro Hc. discriminate Hc.
  - intro Hc. destruct Hlr as (W0 & Hd). destruct Hd as [ (HC & H1) | (HC & H2) ]; subst W; discriminate Hc.
  - exact I.
  - exact I.
Qed.

Lemma down_comp_is : forall (T : ClosComp) n, (n T↓ T) = down_clos n T.
Proof. reflexivity. Qed.
Lemma down_value_is : forall (W : ClosValue) n, (n W↓ W) = down_clos n W.
Proof. reflexivity. Qed.
Lemma LR_nonabs : forall {n} (A : Ty n ValFlag) (W : ClosValue) mLower gCtx,
  LR A W mLower gCtx -> W <> Absent.
Proof.
  intros. exact (LR_nonabs_all A W mLower gCtx H).
Qed.
Lemma if_bool_id : forall b : bool,
  (if b as b0 return (b = b0 -> bool) then (fun _ => true) else (fun _ => false)) eq_refl = b.
Proof. intros b. destruct b; reflexivity. Qed.
Lemma fin_eqb_Some : forall {n} (i j : fin n), fin_eqb (Some i : fin (S n)) (Some j : fin (S n)) = fin_eqb i j.
Proof.
  intros. cbn.
  change ((if fin_eqb i j as b0 return (fin_eqb i j = b0 -> bool)
           then (fun _ => true) else (fun _ => false)) eq_refl = fin_eqb i j).
  apply if_bool_id.
Qed.
Lemma fin_eqb_None : forall {n}, fin_eqb (None : fin (S n)) (None : fin (S n)) = true.
Proof. intros. cbn. reflexivity. Qed.
Lemma fin_eqb_Some_None : forall {n} (i : fin n), fin_eqb (Some i : fin (S n)) (None : fin (S n)) = false.
Proof. intros. cbn. reflexivity. Qed.
Lemma fin_eqb_None_Some : forall {n} (j : fin n), fin_eqb (None : fin (S n)) (Some j : fin (S n)) = false.
Proof. intros. cbn. reflexivity. Qed.
Lemma fin_eqb_refl : forall {n} (i : fin n), fin_eqb i i = true.
Proof.
  induction n as [|n IH]; intros i.
  - destruct i.
  - destruct i as [i'|].
    + rewrite fin_eqb_Some. apply IH.
    + apply fin_eqb_None.
Qed.
Lemma fin_eqb_true_iff : forall {n} (i j : fin n), fin_eqb i j = true <-> i = j.
Proof.
  induction n as [|n IH]; intros i j.
  - destruct i.
  - destruct i as [i'|], j as [j'|].
    + rewrite fin_eqb_Some. split; intro H.
      * f_equal. apply (proj1 (IH i' j')). exact H.
      * injection H as H. apply (proj2 (IH i' j')). exact H.
    + rewrite fin_eqb_Some_None. split; intro H; discriminate H.
    + rewrite fin_eqb_None_Some. split; intro H; discriminate H.
    + rewrite fin_eqb_None. split; intro H; reflexivity.
Qed.
Lemma fin_eqb_neq : forall {n} (i j : fin n), i <> j -> fin_eqb i j = false.
Proof.
  intros n i j H. destruct (fin_eqb i j) eqn:E.
  - exfalso. apply H. apply (proj1 (fin_eqb_true_iff i j)). exact E.
  - reflexivity.
Qed.
Lemma env_set_same : forall {n A} (f : fin n -> A) i a, (f <- a @ i) i = a.
Proof. intros. unfold env_set. rewrite fin_eqb_refl. reflexivity. Qed.
Lemma env_set_neq : forall {n A} (f : fin n -> A) i j a, i <> j -> (f <- a @ i) j = f j.
Proof. intros. unfold env_set. rewrite (@fin_eqb_neq n i j H). reflexivity. Qed.

Section SemTyping.
Context {n : nat} (γ : attrs n) (Γ : context n).

End SemTyping.

Definition SemV {n : nat} (γ : attrs n) (Γ : context n) (V : Val n) (A : ValTy n) : Prop :=
  forall (ρ : env n) (gCtx : attrs n) (mLower : nat) (Hnl : mLower <= n) (v : attrs mLower),
    ρ_ok gCtx ρ Γ mLower gCtx ->
    PadTo gCtx v ->
    down_env_until gCtx mLower Hnl = v ->
    (down_env_until gCtx mLower Hnl) γS<= (down_env_until γ mLower Hnl) ->
    exists W, EvalVal γ ρ V W /\ LR A W mLower gCtx.

Definition SemC {n : nat} (γ : attrs n) (Γ : context n) (M : Comp n) (B : CompTy n) : Prop :=
  forall (ρ : env n) (gCtx : attrs n) (mLower : nat) (Hnl : mLower <= n) (v : attrs mLower),
    ρ_ok gCtx ρ Γ mLower gCtx ->
    PadTo gCtx v ->
    down_env_until gCtx mLower Hnl = v ->
    (down_env_until gCtx mLower Hnl) γS<= (down_env_until γ mLower Hnl) ->
    exists T, EvalComp γ ρ M T /\ LR B T mLower gCtx.

Lemma SemWt_core : forall n (γ : attrs n) (Γ : context n),
  (forall (V : Val n) (A : ValTy n), VWt γ Γ V A -> SemV γ Γ V A) /\
  (forall (M : Comp n) (B : CompTy n), CWt γ Γ M B -> SemC γ Γ M B).
Proof.
  intros n γ Γ.
  apply Wt_mutual with
    (P := fun n γ Γ V A _ => @SemV n γ Γ V A)
    (P0 := fun n γ Γ M B _ => @SemC n γ Γ M B).
  - (* T_Var *)
    intros n0 g0 G i A e e0. subst A. subst g0.
    intros ρ gCtx mLower Hnl v Hok Hpad Hdown Hstr.
    assert (Hlive : gCtx i <> Lazy).
    { apply (@pad_liveness n0 gCtx (lazyvector <- Strict @ i) mLower Hnl v Hpad Hdown Hstr i).
      rewrite env_set_same. discriminate. }
    assert (Hlr : LR (G i) (ρ i) mLower gCtx) by (apply Hok; exact Hlive).
    exists (ρ i). split.
    + eapply E_Var; [reflexivity | reflexivity | ].
      apply (@LR_nonabs n0 (G i) (ρ i) mLower gCtx Hlr).
    + exact Hlr.
  - (* T_Unit *)
    intros n0 g0 G e. subst g0.
    intros ρ gCtx mLower Hnl v Hok Hpad Hdown Hstr.
    exists Unit. split.
    + eapply E_Unit. reflexivity.
    + cbn. reflexivity.
  - (* T_Thunk *)
    intros n0 g0 G g' M B0 c IHc e. subst g0.
    intros ρ gCtx mLower Hnl v Hok Hpad Hdown Hstr.
    exists (Thunk n0 n0 g' ρ M). split.
    + eapply E_Thunk. reflexivity.
    + cbn.
      eexists n0, n0, g', g', ρ, M.
      exists (Nat.le_refl n0), (Nat.le_refl n0), Hnl.
      split; [ apply down_env_until_full |].
      split; [ apply down_env_until_full |].
      split; [reflexivity|].
      intros Hnl2 Hstr2.
      assert (Hdown2 : down_env_until gCtx mLower Hnl2 = v).
      { rewrite (down_env_until_H_irrel Hnl2 Hnl). exact Hdown. }
      destruct (IHc ρ gCtx mLower Hnl2 v Hok Hpad Hdown2 Hstr2) as (T & Hev & HlrB).
      exists T. split; [ exact Hev | ].
      rewrite down_comp_is. rewrite (LR_ws B0 T mLower gCtx HlrB). exact HlrB.
  - (* T_Pair *)
    intros n0 g0 G g1 g2 V1 V2 A1 A2 c1 IH1 c2 IH2 e. subst g0.
    intros ρ gCtx mLower Hnl v Hok Hpad Hdown Hstr.
    assert (Hstr1 := @stricter_add_l n0 gCtx g1 g2 mLower Hnl Hstr).
    assert (Hstr2 := @stricter_add_r n0 gCtx g1 g2 mLower Hnl Hstr).
    destruct (IH1 ρ gCtx mLower Hnl v Hok Hpad Hdown Hstr1) as (W1 & Hev1 & Hlr1).
    destruct (IH2 ρ gCtx mLower Hnl v Hok Hpad Hdown Hstr2) as (W2 & Hev2 & Hlr2).
    exists (Pair W1 W2). split.
    + eapply E_VPair; [ exact Hev1 | exact Hev2 | reflexivity ].
    + cbn. exists W1, W2. split; [reflexivity|split]; assumption.
  - (* T_Inl *)
    intros n0 g0 G V1 A1 A2 c IH.
    intros ρ gCtx mLower Hnl v Hok Hpad Hdown Hstr.
    destruct (IH ρ gCtx mLower Hnl v Hok Hpad Hdown Hstr) as (W & Hev & Hlr).
    exists (Inl W). split.
    + eapply E_Inl; exact Hev.
    + cbn. exists W. left. split; [reflexivity | exact Hlr].
  - (* T_Inr *)
    intros n0 g0 G V2 A1 A2 c IH.
    intros ρ gCtx mLower Hnl v Hok Hpad Hdown Hstr.
    destruct (IH ρ gCtx mLower Hnl v Hok Hpad Hdown Hstr) as (W & Hev & Hlr).
    exists (Inr W). split.
    + eapply E_Inr; exact Hev.
    + cbn. exists W. right. split; [reflexivity | exact Hlr].
  - (* T_Ret *)
    intros n0 g0 G V A c IH.
    intros ρ gCtx mLower Hnl v Hok Hpad Hdown Hstr.
    destruct (IH ρ gCtx mLower Hnl v Hok Hpad Hdown Hstr) as (W & Hev & Hlr).
    exists (Return W). split.
    + eapply E_Ret; exact Hev.
    + cbn. exists W. split; [reflexivity | exact Hlr].
  - (* T_Let *)
    intros n0 g0 G q M M' A B B' g1 g2 c IH1 c0 IH2 e e0. subst g0. subst B.
    intros ρ gCtx mLower Hnl v Hok Hpad Hdown Hstr.
    assert (Hstr1 := @stricter_add_l n0 gCtx g1 g2 mLower Hnl Hstr).
    destruct (IH1 ρ gCtx mLower Hnl v Hok Hpad Hdown Hstr1) as (T0 & Hev0 & Hlr0).
    cbn in Hlr0. destruct Hlr0 as (W & HT0 & HlrW). subst T0.
    assert (Hnl' : mLower <= S n0) by (apply (le_S mLower n0 Hnl)).
    assert (Hok' : ρ_ok (Strict .: gCtx) (W .: ρ) (ctx_insert A G) mLower (Strict .: gCtx)).
    { intros j. destruct j as [k|].
      - intro Hlive. cbn. exact (proj1 (LR_all (G k)) (ρ k) mLower gCtx Lazy (Hok k Hlive)).
      - intro. cbn. exact (proj1 (LR_all A) W mLower gCtx Lazy HlrW). }
    assert (Hpad' : PadTo (Strict .: gCtx) v).
    { apply (pad_to_cons gCtx v Hnl Hpad). }
    assert (Hdown' : down_env_until (Strict .: gCtx) mLower Hnl' = v).
    { rewrite (@down_env_until_cons n0 mLower Strict gCtx Hnl' Hnl). exact Hdown. }
    assert (Hstr' : down_env_until (Strict .: gCtx) mLower Hnl' γS<= down_env_until (q .: g2) mLower Hnl').
    { intros j. specialize (Hstr j). rewrite down_env_until_add in Hstr.
      rewrite (@down_env_until_cons n0 mLower Strict gCtx Hnl' Hnl).
      rewrite (@down_env_until_cons n0 mLower q g2 Hnl' Hnl).
      exact (attr_stricter_add_r_pt _ _ _ Hstr). }
    destruct (IH2 (W .: ρ) (Strict .: gCtx) mLower Hnl' v Hok' Hpad' Hdown' Hstr') as (T & Hev & HlrB').
    exists (n0 T↓ T). split.
    + eapply E_LetRet; [ exact Hev0 | exact Hev | reflexivity | reflexivity ].
    + destruct (LR_all B') as (upB' & dnB' & lfB' & duB').
      apply (dnB' n0 (Nat.le_succ_diag_r n0) mLower Hnl T (Strict .: gCtx) gCtx).
      * rewrite (@down_env_until_cons n0 n0 Strict gCtx (Nat.le_succ_diag_r n0) (Nat.le_refl n0)).
        symmetry. apply down_env_until_full.
      * exact HlrB'.
  - (* T_Force *)
    intros n0 g0 G V B g1 g2 c IH e. subst g0.
    intros ρ gCtx mLower Hnl v Hok Hpad Hdown Hstr.
    assert (Hstr1 := @stricter_add_l n0 gCtx g1 g2 mLower Hnl Hstr).
    destruct (IH ρ gCtx mLower Hnl v Hok Hpad Hdown Hstr1) as (W & Hev & Hlr).
    cbn in Hlr.
    destruct Hlr as (mo & mi & gsc & gInner & rho & M0 & HInner & Hn & HLow & Hd1 & Hd2 & HC & Hcl).
    subst W.
    assert (Hstr2 : down_env_until gCtx mLower Hnl γS<= down_env_until g2 mLower Hnl).
    { intros j. specialize (Hstr j). rewrite down_env_until_add in Hstr.
      exact (attr_stricter_add_r_pt _ _ _ Hstr). }
    destruct (Hcl Hnl Hstr2) as (T' & Hev' & HlrB).
    exists (down_comp mo T'). split.
    + eapply E_Force; [ exact Hev | exact Hev' | exact Hd2 | exact Hd1 | reflexivity | reflexivity ].
    + exact HlrB.
  - (* T_Seq *)
    intros n0 g0 G V M B g1 g2 c1 IH1 c2 IH2 e. subst g0.
    intros ρ gCtx mLower Hnl v Hok Hpad Hdown Hstr.
    assert (Hstr1 := @stricter_add_l n0 gCtx g1 g2 mLower Hnl Hstr).
    assert (Hstr2 := @stricter_add_r n0 gCtx g1 g2 mLower Hnl Hstr).
    destruct (IH1 ρ gCtx mLower Hnl v Hok Hpad Hdown Hstr1) as (W & Hev & Hlr).
    cbn in Hlr. subst W.
    destruct (IH2 ρ gCtx mLower Hnl v Hok Hpad Hdown Hstr2) as (T & Hev2 & Hlr2).
    exists T. split.
    + eapply E_Seq; [ exact Hev | exact Hev2 | reflexivity ].
    + exact Hlr2.
  - (* T_Split *)
    intros n0 g0 G q1 q2 V M g1 g2 A1 A2 B B' c IH1 c0 IH2 e e0. subst g0. subst B.
    intros ρ gCtx mLower Hnl v Hok Hpad Hdown Hstr.
    assert (Hstr1 := @stricter_add_l n0 gCtx g1 g2 mLower Hnl Hstr).
    destruct (IH1 ρ gCtx mLower Hnl v Hok Hpad Hdown Hstr1) as (W & HevV & HlrV).
    cbn in HlrV. destruct HlrV as (W1 & W2 & HPair & Hlr1 & Hlr2). subst W.
    assert (Hnl1 : mLower <= S n0) by (apply (le_S mLower n0 Hnl)).
    assert (Hnl2 : mLower <= S (S n0)) by (apply (le_S mLower (S n0) Hnl1)).
    assert (Hok'' : ρ_ok (Strict .: (Strict .: gCtx)) (W1 .: (W2 .: ρ))
                     (ctx_insert (up_Ty Lazy A1) (ctx_insert A2 G)) mLower (Strict .: (Strict .: gCtx))).
    { intros j. destruct j as [k|].
      - intro Hlive. destruct k as [k'|].
        + cbn. exact (proj1 (LR_all (up_Ty Lazy (G k'))) (ρ k') mLower (Strict .: gCtx) Lazy
                        (proj1 (LR_all (G k')) (ρ k') mLower gCtx Lazy (Hok k' Hlive))).
        + cbn. exact (proj1 (LR_all (up_Ty Lazy A2)) W2 mLower (Strict .: gCtx) Lazy
                        (proj1 (LR_all A2) W2 mLower gCtx Lazy Hlr2)).
      - intro. cbn. exact (proj1 (LR_all (up_Ty Lazy A1)) W1 mLower (Strict .: gCtx) Lazy
                             (proj1 (LR_all A1) W1 mLower gCtx Lazy Hlr1)). }
    assert (Hpad'' : PadTo (Strict .: (Strict .: gCtx)) v).
    { apply (pad_to_cons (Strict .: gCtx) v Hnl1 (pad_to_cons gCtx v Hnl Hpad)). }
    assert (Hdown'' : down_env_until (Strict .: (Strict .: gCtx)) mLower Hnl2 = v).
    { rewrite (@down_env_until_cons (S n0) mLower Strict (Strict .: gCtx) Hnl2 Hnl1).
      rewrite (@down_env_until_cons n0 mLower Strict gCtx Hnl1 Hnl).
      exact Hdown. }
    assert (Hstr'' : down_env_until (Strict .: (Strict .: gCtx)) mLower Hnl2
                      γS<= down_env_until (q1 .: (q2 .: g2)) mLower Hnl2).
    { intros j. specialize (Hstr j). rewrite down_env_until_add in Hstr.
      rewrite (@down_env_until_cons (S n0) mLower Strict (Strict .: gCtx) Hnl2 Hnl1).
      rewrite (@down_env_until_cons n0 mLower Strict gCtx Hnl1 Hnl).
      rewrite (@down_env_until_cons (S n0) mLower q1 (q2 .: g2) Hnl2 Hnl1).
      rewrite (@down_env_until_cons n0 mLower q2 g2 Hnl1 Hnl).
      exact (attr_stricter_add_r_pt _ _ _ Hstr). }
    destruct (IH2 (W1 .: (W2 .: ρ)) (Strict .: (Strict .: gCtx)) mLower Hnl2 v Hok'' Hpad'' Hdown'' Hstr'')
      as (T & Hev & HlrB').
    exists (n0 T↓ T). split.
    + eapply E_Split; [ exact HevV | exact Hev | reflexivity | reflexivity ].
    + destruct (LR_all B') as (upB' & dnB' & lfB' & duB').
      apply (dnB' n0 (le_succ_succ_diag_r n0) mLower Hnl T (Strict .: (Strict .: gCtx)) gCtx).
      * rewrite (@down_env_until_cons (S n0) n0 Strict (Strict .: gCtx)
                   (le_succ_succ_diag_r n0) (le_S n0 n0 (Nat.le_refl n0))).
        rewrite (@down_env_until_cons n0 n0 Strict gCtx (le_S n0 n0 (Nat.le_refl n0)) (Nat.le_refl n0)).
        symmetry. apply down_env_until_full.
      * exact HlrB'.
  - (* T_Case *)
    intros n0 g0 G q1 q2 V M1 M2 g1 g2 A1 A2 B B1 B2 c IH1 c0 IH2 c1 IH3 e e0 e1.
    subst g0. subst B.
    intros ρ gCtx mLower Hnl v Hok Hpad Hdown Hstr.
    assert (Hstr1 := @stricter_add_l n0 gCtx g1 g2 mLower Hnl Hstr).
    assert (Hnl' : mLower <= S n0) by (apply (le_S mLower n0 Hnl)).
    destruct (IH1 ρ gCtx mLower Hnl v Hok Hpad Hdown Hstr1) as (W & HevV & HlrV).
    cbn in HlrV. destruct HlrV as (W' & [ (HInl & HlrA) | (HInr & HlrA) ]).
    + (* Inl *)
      subst W.
      assert (Hok' : ρ_ok (Strict .: gCtx) (W' .: ρ) (ctx_insert A1 G) mLower (Strict .: gCtx)).
      { intros j. destruct j as [k|].
        - intro Hlive. cbn. exact (proj1 (LR_all (G k)) (ρ k) mLower gCtx Lazy (Hok k Hlive)).
        - intro. cbn. exact (proj1 (LR_all A1) W' mLower gCtx Lazy HlrA). }
      assert (Hpad' : PadTo (Strict .: gCtx) v).
      { apply (pad_to_cons gCtx v Hnl Hpad). }
      assert (Hdown' : down_env_until (Strict .: gCtx) mLower Hnl' = v).
      { rewrite (@down_env_until_cons n0 mLower Strict gCtx Hnl' Hnl). exact Hdown. }
      assert (Hstr' : down_env_until (Strict .: gCtx) mLower Hnl' γS<= down_env_until (q1 .: g2) mLower Hnl').
      { intros j. specialize (Hstr j). rewrite down_env_until_add in Hstr.
        rewrite (@down_env_until_cons n0 mLower Strict gCtx Hnl' Hnl).
        rewrite (@down_env_until_cons n0 mLower q1 g2 Hnl' Hnl).
        exact (attr_stricter_add_r_pt _ _ _ Hstr). }
      destruct (IH2 (W' .: ρ) (Strict .: gCtx) mLower Hnl' v Hok' Hpad' Hdown' Hstr') as (T & Hev & HlrB1).
      exists (n0 T↓ T). split.
      * eapply E_Casel; [ exact HevV | exact Hev | reflexivity | reflexivity ].
      * destruct (LR_all B1) as (upB1 & dnB1 & lfB1 & duB1).
        apply (dnB1 n0 (Nat.le_succ_diag_r n0) mLower Hnl T (Strict .: gCtx) gCtx).
        -- rewrite (@down_env_until_cons n0 n0 Strict gCtx (Nat.le_succ_diag_r n0) (Nat.le_refl n0)).
           symmetry. apply down_env_until_full.
        -- exact HlrB1.
    + (* Inr *)
      subst W.
      assert (Hok' : ρ_ok (Strict .: gCtx) (W' .: ρ) (ctx_insert A2 G) mLower (Strict .: gCtx)).
      { intros j. destruct j as [k|].
        - intro Hlive. cbn. exact (proj1 (LR_all (G k)) (ρ k) mLower gCtx Lazy (Hok k Hlive)).
        - intro. cbn. exact (proj1 (LR_all A2) W' mLower gCtx Lazy HlrA). }
      assert (Hpad' : PadTo (Strict .: gCtx) v).
      { apply (pad_to_cons gCtx v Hnl Hpad). }
      assert (Hdown' : down_env_until (Strict .: gCtx) mLower Hnl' = v).
      { rewrite (@down_env_until_cons n0 mLower Strict gCtx Hnl' Hnl). exact Hdown. }
      assert (Hstr' : down_env_until (Strict .: gCtx) mLower Hnl' γS<= down_env_until (q2 .: g2) mLower Hnl').
      { intros j. specialize (Hstr j). rewrite down_env_until_add in Hstr.
        rewrite (@down_env_until_cons n0 mLower Strict gCtx Hnl' Hnl).
        rewrite (@down_env_until_cons n0 mLower q2 g2 Hnl' Hnl).
        exact (attr_stricter_add_r_pt _ _ _ Hstr). }
      destruct (IH3 (W' .: ρ) (Strict .: gCtx) mLower Hnl' v Hok' Hpad' Hdown' Hstr') as (T & Hev & HlrB2).
      exists (n0 T↓ T). split.
      * eapply E_Caser; [ exact HevV | exact Hev | reflexivity | reflexivity ].
      * destruct (LR_all B2) as (upB2 & dnB2 & lfB2 & duB2).
        rewrite e1.
        apply (dnB2 n0 (Nat.le_succ_diag_r n0) mLower Hnl T (Strict .: gCtx) gCtx).
        -- rewrite (@down_env_until_cons n0 n0 Strict gCtx (Nat.le_succ_diag_r n0) (Nat.le_refl n0)).
           symmetry. apply down_env_until_full.
        -- exact HlrB2.
  - (* T_Abs *)
    intros n0 g0 G q M A B B' c IH e. subst B.
    intros ρ gCtx mLower Hnl v Hok Hpad Hdown Hstr.
    exists (Closure n0 n0 g0 ρ M). split.
    + eapply E_Abs.
    + cbn.
      eexists n0, n0, g0, g0, ρ, M.
      exists (Nat.le_refl n0), (Nat.le_refl n0), Hnl.
      split; [ apply down_env_until_full |].
      split; [reflexivity|].
      intros W HlrW.
      assert (Hnl' : mLower <= S n0) by (apply (le_S mLower n0 Hnl)).
      assert (Hok' : ρ_ok (Strict .: gCtx) ((down_value n0 W) .: ρ) (ctx_insert A G) mLower (Strict .: gCtx)).
      { intros j. destruct j as [k|].
        - intro Hlive. cbn. exact (proj1 (LR_all (G k)) (ρ k) mLower gCtx Lazy (Hok k Hlive)).
        - intro. cbn.
          change (LR (up_Ty Lazy A) (down_clos n0 W) mLower (Strict .: gCtx)).
          rewrite (LR_ws A W mLower gCtx HlrW).
          exact (proj1 (LR_all A) W mLower gCtx Lazy HlrW). }
      assert (Hpad' : PadTo (Strict .: gCtx) v).
      { apply (pad_to_cons gCtx v Hnl Hpad). }
      assert (Hdown' : down_env_until (Strict .: gCtx) mLower Hnl' = v).
      { rewrite (@down_env_until_cons n0 mLower Strict gCtx Hnl' Hnl). exact Hdown. }
      assert (Hstr' : down_env_until (Strict .: gCtx) mLower Hnl' γS<= down_env_until (q .: g0) mLower Hnl').
      { intros j. specialize (Hstr j).
        rewrite (@down_env_until_cons n0 mLower Strict gCtx Hnl' Hnl).
        rewrite (@down_env_until_cons n0 mLower q g0 Hnl' Hnl).
        exact Hstr. }
      destruct (IH (down_value n0 W .: ρ) (Strict .: gCtx) mLower Hnl' v Hok' Hpad' Hdown' Hstr') as (T & Hev & HlrB').
      exists T. split; [ exact Hev |].
      destruct (LR_all B') as (upB' & dnB' & lfB' & duB').
      apply (dnB' n0 (Nat.le_succ_diag_r n0) mLower Hnl T (Strict .: gCtx) gCtx).
      * rewrite (@down_env_until_cons n0 n0 Strict gCtx (Nat.le_succ_diag_r n0) (Nat.le_refl n0)).
        symmetry. apply down_env_until_full.
      * exact HlrB'.
  - (* T_App *)
    intros n0 g0 G M q V g1 g2 A B c IH1 c0 IH2 e. subst g0.
    intros ρ gCtx mLower Hnl v Hok Hpad Hdown Hstr.
    assert (Hstr1 := @stricter_add_l n0 gCtx g1 g2 mLower Hnl Hstr).
    assert (Hstr2 := @stricter_add_r n0 gCtx g1 g2 mLower Hnl Hstr).
    destruct (IH1 ρ gCtx mLower Hnl v Hok Hpad Hdown Hstr1) as (T & Hev & Hlr).
    cbn in Hlr.
    destruct Hlr as (mo & mi & gsc & gInner & rho & M0 & Hn & HInner & HLow & Hd2 & HC & Hcl).
    subst T.
    destruct (IH2 ρ gCtx mLower Hnl v Hok Hpad Hdown Hstr2) as (W & HevV & HlrW).
    destruct (Hcl W HlrW) as (T' & Hev' & HlrB).
    exists (down_comp mo T'). split.
    + eapply E_AppAbs; [ exact Hev | exact HevV | exact (eq_sym Hd2) | exact Hev' | reflexivity | reflexivity ].
    + exact HlrB.
  - (* T_CSub *)
    intros n0 g0 G M g1 B c IH a.
    intros ρ gCtx mLower Hnl v Hok Hpad Hdown Hstr.
    assert (Hstr' := @stricter_sub n0 gCtx g0 g1 mLower Hnl Hstr a).
    destruct (IH ρ gCtx mLower Hnl v Hok Hpad Hdown Hstr') as (T & Hev & Hlr).
    exists T. split.
    + eapply E_CSub; [ exact Hev | exact a ].
    + exact Hlr.
Qed.

Lemma attr_stricter_self : forall a, a S<= a.
Proof. intros a. destruct a; cbn; reflexivity. Qed.

Theorem lazy_soundness : forall n (γ : attrs n) (Γ : context n) (ρ : env n),
  ρ_ok γ ρ Γ n γ ->
  forall i, γ i = Lazy ->
  (forall V A, VWt γ Γ V A ->
    exists W, EvalVal γ (ρ <- Absent @ i) V W) /\
  (forall M B, CWt γ Γ M B ->
    exists T, EvalComp γ (ρ <- Absent @ i) M T).
Proof.
  intros n γ Γ ρ Hok i Hi.
  assert (Hok' : ρ_ok γ (ρ <- Absent @ i) Γ n γ).
  { intros j Hj.
    assert (Hne : j <> i).
    { intro E. subst j. rewrite Hi in Hj. apply Hj. reflexivity. }
    rewrite (@env_set_neq n ClosValue ρ i j Absent (fun E => Hne (eq_sym E))).
    apply Hok. exact Hj. }
  assert (Hpad : PadTo γ γ) by (apply pad_to_refl).
  assert (Hdown : down_env_until γ n (Nat.le_refl n) = γ) by (apply down_env_until_full).
  assert (Hstr : (down_env_until γ n (Nat.le_refl n)) γS<= (down_env_until γ n (Nat.le_refl n))).
  { intros j. rewrite Hdown. apply attr_stricter_self. }
  destruct (SemWt_core n γ Γ) as (HV & HC).
  split.
  - intros V A HVW.
    destruct (HV V A HVW (ρ <- Absent @ i) γ n (Nat.le_refl n) γ Hok' Hpad Hdown Hstr) as (W & Hev & Hlr).
    exists W. exact Hev.
  - intros M B HMW.
    destruct (HC M B HMW (ρ <- Absent @ i) γ n (Nat.le_refl n) γ Hok' Hpad Hdown Hstr) as (T & Hev & Hlr).
    exists T. exact Hev.
Qed.

