From strictness.cbpv Require Import semtyping.
From Stdlib Require Import Lia Logic.Eqdep_dec.

Local Lemma down_env_offset {X n m} (f : fin n -> X) (H : m <= n)
    d (E : d + m = n) :
  down_env_until f m H =
    down_env_until' d (eq_rect_r (fun j => fin j -> X) f E).
Proof.
  unfold down_env_until.
  generalize (eq_sym (le_minus_plus m n H)).
  generalize (n - m).
  intros d' E'.
  assert (d' = d) by lia. subst d'.
  now replace E' with E by (apply UIP_dec; exact Nat.eq_dec).
Qed.

Local Lemma down_env_refl {X n} (f : fin n -> X) (H : n <= n) :
  down_env_until f n H = f.
Proof.
  rewrite (down_env_offset f H 0 eq_refl). reflexivity.
Qed.

Local Lemma down_env_succ {X n m} (f : fin (S n) -> X)
    (H : m <= n) (HS : m <= S n) :
  down_env_until f m HS = down_env_until (fun i => f (Some i)) m H.
Proof.
  pose proof (eq_sym (le_minus_plus m n H)) as E.
  rewrite (down_env_offset f HS (S (n - m)) (f_equal S E)).
  rewrite (down_env_offset (fun i => f (Some i)) H (n - m) E).
  generalize dependent f.
  generalize dependent E.
  generalize (n - m). clear HS H.
  intros d E f. destruct E. reflexivity.
Qed.

Local Lemma down_env_proof {X n m} (f : fin n -> X) (H H' : m <= n) :
  down_env_until f m H = down_env_until f m H'.
Proof.
  rewrite (down_env_offset f H (n - m) (eq_sym (le_minus_plus m n H))).
  rewrite (down_env_offset f H' (n - m) (eq_sym (le_minus_plus m n H))).
  reflexivity.
Qed.

Scheme le_scope_ind := Induction for le Sort Prop.

Local Lemma down_env_compose {X n m s} (f : fin n -> X)
    (Hmn : m <= n) (Hsm : s <= m) (Hsn : s <= n) :
  down_env_until (down_env_until f m Hmn) s Hsm = down_env_until f s Hsn.
Proof.
  revert f Hsn.
  induction Hmn as [|n Hmn IH] using le_scope_ind; intros f Hsn.
  - rewrite down_env_refl. apply down_env_proof.
  - rewrite (down_env_succ f Hmn), (down_env_succ f (Nat.le_trans _ _ _ Hsm Hmn)).
    apply IH.
Qed.

Local Lemma down_env_congr {X Y n} (f : fin n -> X)
    (build : forall m, (fin m -> X) -> Y) a b (Ha : a <= n) (Hb : b <= n) :
  a = b -> build a (down_env_until f a Ha) = build b (down_env_until f b Hb).
Proof.
  intros ->. now rewrite (down_env_proof f Ha Hb).
Qed.

Local Lemma down_clos_compose {k} (C : Clos k) r s :
  down_clos r (down_clos s C) = down_clos (Nat.min s r) C.
Proof.
  induction C as [| |n m γ ρ IHρ M|W1 IH1 W2 IH2|W IH|W IH|W IH|n m γ ρ IHρ M];
    cbn [down_clos]; try reflexivity; try solve [f_equal; auto].
  - rewrite down_env_compose with (Hsn := Nat.le_trans _ _ _ (min_le _ _) (min_le _ _)).
    apply (down_env_congr γ (fun j δ => Thunk j m δ ρ M)).
    symmetry. apply Nat.min_assoc.
  - rewrite down_env_compose with (Hsn := Nat.le_trans _ _ _ (min_le _ _) (min_le _ _)).
    apply (down_env_congr γ (fun j δ => Closure j m δ ρ M)).
    symmetry. apply Nat.min_assoc.
Qed.

Local Lemma down_clos_scoped {k} (C : Clos k) s :
  well_scoped_clos C s -> down_clos s C = C.
Proof.
  induction C as [| |n m γ ρ IHρ M|W1 IH1 W2 IH2|W IH|W IH|W IH|n m γ ρ IHρ M];
    cbn [well_scoped_clos down_clos]; intros H;
    try reflexivity; try solve [f_equal; intuition].
  - transitivity (Thunk n m (down_env_until γ n (Nat.le_refl n)) ρ M).
    + apply (down_env_congr γ (fun j δ => Thunk j m δ ρ M)).
      now apply Nat.min_l.
    + now rewrite down_env_refl.
  - transitivity (Closure n m (down_env_until γ n (Nat.le_refl n)) ρ M).
    + apply (down_env_congr γ (fun j δ => Closure j m δ ρ M)).
      now apply Nat.min_l.
    + now rewrite down_env_refl.
Qed.

Local Lemma LR_scoped {n k} (A : Ty n k) C : LR A C -> well_scoped_clos C n.
Proof.
  revert C.
  induction A as [|γ B IH|A1 IH1 A2 IH2|A1 IH1 A2 IH2|q A IH1 B IH2|A IH];
    intros C HC; cbn [LR] in HC.
  - now subst C.
  - destruct HC as (o & i & δ & γ' & ρ & M & Hi & Hn & _ & _ & -> & _).
    exact Hn.
  - destruct HC as (W1 & W2 & -> & H1 & H2). split; auto.
  - destruct HC as (W & [[-> H] | [-> H]]); cbn [well_scoped_clos]; auto.
  - destruct HC as (o & i & δ & γ' & ρ & M & Hn & Hi & _ & -> & _).
    exact Hn.
  - destruct HC as (W & -> & H). cbn [well_scoped_clos]. auto.
Qed.

Local Lemma down_clos_smaller {k} (C : Clos k) a b (H : a <= b) :
  down_clos a (down_clos b C) = down_clos a C /\
  down_clos b (down_clos a C) = down_clos a C.
Proof.
  split; rewrite down_clos_compose;
    now rewrite (Nat.min_r b a H) || rewrite (Nat.min_l a b H).
Qed.

(* Types agree at a shared scope when their thunk attributes agree there. *)
Inductive type_prefix {n m} s (Hn : s <= n) (Hm : s <= m) :
    forall k, Ty n k -> Ty m k -> Prop :=
| prefix_unit : type_prefix s Hn Hm ValFlag VUnit VUnit
| prefix_thunk γ δ B B' :
    down_env_until γ s Hn = down_env_until δ s Hm ->
    type_prefix s Hn Hm CompFlag B B' ->
    type_prefix s Hn Hm ValFlag (VThunk γ B) (VThunk δ B')
| prefix_prod A A' B B' :
    type_prefix s Hn Hm ValFlag A A' -> type_prefix s Hn Hm ValFlag B B' ->
    type_prefix s Hn Hm ValFlag (VProd A B) (VProd A' B')
| prefix_sum A A' B B' :
    type_prefix s Hn Hm ValFlag A A' -> type_prefix s Hn Hm ValFlag B B' ->
    type_prefix s Hn Hm ValFlag (VSum A B) (VSum A' B')
| prefix_abs q A A' B B' :
    type_prefix s Hn Hm ValFlag A A' -> type_prefix s Hn Hm CompFlag B B' ->
    type_prefix s Hn Hm CompFlag (CAbs q A B) (CAbs q A' B')
| prefix_return A A' :
    type_prefix s Hn Hm ValFlag A A' ->
    type_prefix s Hn Hm CompFlag (CF A) (CF A').

Local Lemma type_prefix_down {n m k} (A : Ty n k) (H : m <= n) :
  type_prefix m H (Nat.le_refl m) k A (down_ty_until A m H).
Proof.
  induction A; cbn [down_ty_until]; constructor; auto.
  now rewrite down_env_refl.
Qed.

Local Lemma type_prefix_up {n k} (A : Ty n k) q :
  type_prefix n (Nat.le_refl n) (Nat.le_succ_diag_r n) k A (up_Ty q A).
Proof.
  unfold up_Ty. induction A; cbn [map_Ty]; constructor; auto.
  rewrite (down_env_succ _ (Nat.le_refl n)). reflexivity.
Qed.

Local Lemma down_env_agree {X n m s o a} (γ : fin n -> X) (δ : fin m -> X)
    (θ : fin o -> X) (Hn : s <= n) (Hm : s <= m) (Hon : o <= n)
    (Has : a <= s) (Hao : a <= o) (Ham : a <= m) :
  down_env_until γ s Hn = down_env_until δ s Hm ->
  down_env_until γ o Hon = θ ->
  down_env_until δ a Ham = down_env_until θ a Hao.
Proof.
  intros Hagree <-.
  rewrite <- (down_env_compose δ Hm Has Ham), <- Hagree.
  pose proof (Nat.le_trans _ _ _ Has Hn) as Han.
  now rewrite (down_env_compose γ Hn Has Han), (down_env_compose γ Hon Hao Han).
Qed.

(* The argument of a closure transfers in the opposite direction to its result. *)
Local Lemma LR_prefix {n m s k} (Hn : s <= n) (Hm : s <= m)
    (A : Ty n k) (B : Ty m k) (H : type_prefix s Hn Hm k A B) :
  forall r, r <= s ->
    (forall C, LR A C -> LR B (down_clos r C)) /\
    (forall C, LR B C -> LR A (down_clos r C)).
Proof.
  induction H as
    [|γ δ B B' Hγ HB IH|A A' B B' HA IHA HB IHB|A A' B B' HA IHA HB IHB
     |q A A' B B' HA IHA HB IHB|A A' HA IH];
    intros r Hr; split; intros C HC; cbn [LR] in HC |- *;
    unfold down_value, down_comp in HC |- *.
  1,2: now subst C.
  1,2: (
    destruct HC as (o & i & θ & γi & ρ & M & Hi & Horig & Htype & Hinner & -> & T & HT & HBT);
    pose (Ho := min_le o r);
    pose proof (Nat.le_trans _ _ _ (Nat.le_min_r o r) Hr) as Hos;
    pose proof (Nat.le_trans _ _ _ Ho Hi) as Hoi;
    cbn [down_clos]).
  2: symmetry in Hγ.
  1: exists (Nat.min o r), i, (down_env_until θ _ Ho), γi, ρ, M, Hoi,
       (Nat.le_trans _ _ _ Hos Hm).
  2: exists (Nat.min o r), i, (down_env_until θ _ Ho), γi, ρ, M, Hoi,
       (Nat.le_trans _ _ _ Hos Hn).
  1: split; [exact (down_env_agree _ _ _ Hn Hm Horig Hos Ho _ Hγ Htype) |].
  2: split; [exact (down_env_agree _ _ _ Hm Hn Horig Hos Ho _ Hγ Htype) |].
  1,2: split; [rewrite <- Hinner; symmetry; apply down_env_compose |].
  1,2: (
    split; [reflexivity |];
    exists T; split; [exact HT |];
    rewrite <- (proj1 (down_clos_smaller T _ _ Ho));
    first [exact (proj1 (IH _ Hos) _ HBT) | exact (proj2 (IH _ Hos) _ HBT)]).
  1,2: (
    destruct HC as (W1 & W2 & -> & HW1 & HW2);
    exists (down_clos r W1), (down_clos r W2); split; [reflexivity |]; split;
    [first [exact (proj1 (IHA r Hr) _ HW1) | exact (proj2 (IHA r Hr) _ HW1)]
    |first [exact (proj1 (IHB r Hr) _ HW2) | exact (proj2 (IHB r Hr) _ HW2)]]).
  1,2: (
    destruct HC as (W & [[-> HW] | [-> HW]]); exists (down_clos r W);
    [left; split; [reflexivity |];
      first [exact (proj1 (IHA r Hr) _ HW) | exact (proj2 (IHA r Hr) _ HW)]
    |right; split; [reflexivity |];
      first [exact (proj1 (IHB r Hr) _ HW) | exact (proj2 (IHB r Hr) _ HW)]]).
  1,2: (
    destruct HC as (o & i & θ & γi & ρ & M & Horig & Hi & Hinner & -> & Hbody);
    pose (Ho := min_le o r);
    pose proof (Nat.le_trans _ _ _ (Nat.le_min_r o r) Hr) as Hos;
    pose proof (Nat.le_trans _ _ _ Ho Hi) as Hoi;
    cbn [down_clos]).
  1: exists (Nat.min o r), i, (down_env_until θ _ Ho), γi, ρ, M,
       (Nat.le_trans _ _ _ Hos Hm), Hoi.
  2: exists (Nat.min o r), i, (down_env_until θ _ Ho), γi, ρ, M,
       (Nat.le_trans _ _ _ Hos Hn), Hoi.
  1,2: split; [rewrite <- Hinner; symmetry; apply down_env_compose |].
  1,2: (
    split; [reflexivity |];
    intros W HW;
    let Harg := fresh "Harg" in
    first [pose proof (proj2 (IHA _ Hos) _ HW) as Harg
          |pose proof (proj1 (IHA _ Hos) _ HW) as Harg];
    destruct (Hbody _ Harg) as (T & HT & HBT);
    exists T; split;
    [now rewrite (proj2 (down_clos_smaller W _ _ Ho)) in HT
    |rewrite <- (proj1 (down_clos_smaller T _ _ Ho));
      first [exact (proj1 (IHB _ Hos) _ HBT) | exact (proj2 (IHB _ Hos) _ HBT)]]).
  1,2: (
    destruct HC as (W & -> & HW);
    exists (down_clos r W); split; [reflexivity |];
    first [exact (proj1 (IH r Hr) _ HW) | exact (proj2 (IH r Hr) _ HW)]).
Qed.

Local Lemma LR_down {n m k} (A : Ty n k) (H : m <= n) C :
  LR A C -> LR (down_ty_until A m H) (down_clos m C).
Proof.
  exact (proj1 (LR_prefix _ _ _ _ (type_prefix_down A H) m (Nat.le_refl m)) C).
Qed.

Local Lemma LR_up {n k} (A : Ty n k) q C : LR A C -> LR (up_Ty q A) C.
Proof.
  intros HC.
  pose proof (proj1 (LR_prefix _ _ _ _ (type_prefix_up A q) n (Nat.le_refl n)) C HC) as H.
  now rewrite (down_clos_scoped C n (LR_scoped A C HC)) in H.
Qed.

Local Lemma ρ_ok_insert {n} (Γ : context n) (ρ : env n) A W :
  ρ_ok ρ Γ -> LR A W -> ρ_ok (W .: ρ) (ctx_insert A Γ).
Proof.
  intros Hρ HW [i |]; cbn [ctx_insert scons]; apply LR_up; auto.
Qed.

Local Lemma LR_present {n k} (A : Ty n k) C :
  LR A C -> match C with Absent => False | _ => True end.
Proof.
  revert C. destruct A; intros C HC; cbn [LR] in HC.
  - now subst C.
  - now destruct HC as (o & i & θ & γi & ρ & M & Hi & Hn & _ & _ & -> & _).
  - now destruct HC as (W1 & W2 & -> & _).
  - now destruct HC as (W & [[-> _] | [-> _]]).
  - now destruct HC as (o & i & θ & γi & ρ & M & Hn & Hi & _ & -> & _).
  - now destruct HC as (W & -> & _).
Qed.

Local Lemma typing_sound : forall n (γ : attrs n) (Γ : context n),
  (forall V A, VWt γ Γ V A -> SemVWt γ Γ V A) /\
  (forall M B, CWt γ Γ M B -> SemCWt γ Γ M B).
Proof.
  apply (Wt_mutual (fun n γ Γ V A _ => SemVWt γ Γ V A)
                   (fun n γ Γ M B _ => SemCWt γ Γ M B));
    unfold SemVWt, SemCWt.
  - intros n γ Γ i A -> Hγ ρ Hρ.
    exists (ρ i). split; [|apply Hρ].
    apply E_Var; [reflexivity | exact Hγ |].
    intros Habs. pose proof (LR_present (Γ i) _ (Hρ i)) as H.
    now rewrite Habs in H.
  - intros n γ Γ Hγ ρ Hρ.
    exists Unit. split; [now apply E_Unit | reflexivity].
  - intros n γ Γ γ' M B Hwt IH Hγ ρ Hρ.
    destruct (IH ρ Hρ) as (T & HT & HBT).
    exists (Thunk n n γ' ρ M). split; [now apply E_Thunk |].
    exists n, n, γ', γ', ρ, M, (Nat.le_refl n), (Nat.le_refl n).
    rewrite down_env_refl. repeat split.
    exists T. split; [exact HT |].
    unfold down_comp. now rewrite (down_clos_scoped T n (LR_scoped B T HBT)).
  - intros n γ Γ γ1 γ2 V1 V2 A1 A2 Hwt1 IH1 Hwt2 IH2 Hγ ρ Hρ.
    destruct (IH1 ρ Hρ) as (W1 & HW1 & HA1).
    destruct (IH2 ρ Hρ) as (W2 & HW2 & HA2).
    exists (Pair W1 W2). split; [eapply E_VPair; eassumption |].
    exists W1, W2. auto.
  - intros n γ Γ V A1 A2 Hwt IH ρ Hρ.
    destruct (IH ρ Hρ) as (W & HW & HA).
    exists (Inl W). split; [now apply E_Inl |].
    exists W. auto.
  - intros n γ Γ V A1 A2 Hwt IH ρ Hρ.
    destruct (IH ρ Hρ) as (W & HW & HA).
    exists (Inr W). split; [now apply E_Inr |].
    exists W. auto.
  - intros n γ Γ V A Hwt IH ρ Hρ.
    destruct (IH ρ Hρ) as (W & HW & HA).
    exists (Return W). split; [now apply E_Ret |].
    exists W. auto.
  - intros n γ Γ q M N A B B' γ1 γ2 HwtM IHM HwtN IHN Hγ -> ρ Hρ.
    destruct (IHM ρ Hρ) as (R & HR & W & -> & HW).
    destruct (IHN (W .: ρ) (ρ_ok_insert Γ ρ A W Hρ HW)) as (T & HT & HBT).
    exists (n T↓ T). split.
    + eapply E_LetRet; [exact HR | exact HT | exact Hγ | reflexivity].
    + now apply LR_down.
  - intros n γ Γ V B γ1 γ2 Hwt IH Hγ ρ Hρ.
    destruct (IH ρ Hρ) as (W & HW & o & i & θ & γi & ρi & M & Hi & Hn &
                           Htype & Hinner & -> & T & HT & HBT).
    exists (o T↓ T). split; [|exact HBT].
    eapply E_Force; [exact HW | exact HT | exact Hinner | exact Htype | exact Hγ | reflexivity].
  - intros n γ Γ V M B γ1 γ2 HwtV IHV HwtM IHM Hγ ρ Hρ.
    destruct (IHV ρ Hρ) as (W & HW & ->).
    destruct (IHM ρ Hρ) as (T & HT & HBT).
    exists T. split; [eapply E_Seq; eassumption | exact HBT].
  - intros n γ Γ q1 q2 V M γ1 γ2 A1 A2 B B' HwtV IHV HwtM IHM Hγ -> ρ Hρ.
    destruct (IHV ρ Hρ) as (W & HW & W1 & W2 & -> & HA1 & HA2).
    assert (Hρ' : ρ_ok (W1 .: (W2 .: ρ)) (ctx_insert (Lazy A↑ A1) (ctx_insert A2 Γ))).
    { apply ρ_ok_insert; [now apply ρ_ok_insert | now apply LR_up]. }
    destruct (IHM _ Hρ') as (T & HT & HBT).
    exists (n T↓ T). split.
    + eapply E_Split; [exact HW | exact HT | exact Hγ | reflexivity].
    + now apply LR_down.
  - intros n γ Γ q1 q2 V M1 M2 γ1 γ2 A1 A2 B B1 B2
      HwtV IHV Hwt1 IH1 Hwt2 IH2 Hγ HB1 HB2 ρ Hρ.
    destruct (IHV ρ Hρ) as (W & HW & U & [[-> HU] | [-> HU]]).
    + destruct (IH1 _ (ρ_ok_insert Γ ρ A1 U Hρ HU)) as (T & HT & HBT).
      exists (n T↓ T). split.
      * eapply E_Casel; [exact HW | exact HT | exact Hγ | reflexivity].
      * rewrite HB1. now apply LR_down.
    + destruct (IH2 _ (ρ_ok_insert Γ ρ A2 U Hρ HU)) as (T & HT & HBT).
      exists (n T↓ T). split.
      * eapply E_Caser; [exact HW | exact HT | exact Hγ | reflexivity].
      * rewrite HB2. now apply LR_down.
  - intros n γ Γ q M A B B' Hwt IH -> ρ Hρ.
    exists (Closure n n γ ρ M). split; [apply E_Abs |].
    exists n, n, γ, γ, ρ, M, (Nat.le_refl n), (Nat.le_refl n).
    rewrite down_env_refl. repeat split.
    intros W HW. unfold down_value.
    rewrite (down_clos_scoped W n (LR_scoped A W HW)).
    destruct (IH (W .: ρ) (ρ_ok_insert Γ ρ A W Hρ HW)) as (T & HT & HBT).
    exists T. split; [exact HT | now apply LR_down].
  - intros n γ Γ M q V γ1 γ2 A B HwtM IHM HwtV IHV Hγ ρ Hρ.
    destruct (IHM ρ Hρ) as (F & HF & o & i & θ & γi & ρi & N & Hn & Hi & Hinner & -> & Hbody).
    destruct (IHV ρ Hρ) as (W & HW & HA).
    destruct (Hbody W HA) as (T & HT & HBT).
    exists (o T↓ T). split; [|exact HBT].
    eapply E_AppAbs; [exact HF | exact HW | symmetry; exact Hinner | exact HT | exact Hγ | reflexivity].
  - intros n γ Γ M γ' B Hwt IH Hle ρ Hρ.
    destruct (IH ρ Hρ) as (T & HT & HBT).
    exists T. split; [eapply E_CSub; eassumption | exact HBT].
Qed.

Theorem function_soundness : forall n (γ : attrs n) (Γ : context n) (ρ : env n) M A B q,
  semtyping.ρ_ok ρ Γ ->
  CWt γ Γ M (CAbs q A B) ->
  exists mOuter mInner γInner ρ' M' HInner,
  EvalComp γ ρ M (Closure mOuter mInner (down_env_until γInner mOuter HInner) ρ' M') /\
  forall W, semtyping.LR A W ->
  exists T, EvalComp (q .: γInner) ((mOuter W↓ W) .: ρ') M' T.
Proof.
  intros n γ Γ ρ M A B q Hρ Hwt.
  destruct (proj2 (typing_sound n γ Γ) M (CAbs q A B) Hwt ρ Hρ)
    as (F & HF & o & i & θ & γi & ρi & N & Hn & Hi & Hinner & -> & Hbody).
  exists o, i, γi, ρi, N, Hi. split.
  - now rewrite Hinner.
  - intros W HW. destruct (Hbody W HW) as (T & HT & _).
    now exists T.
Qed.
