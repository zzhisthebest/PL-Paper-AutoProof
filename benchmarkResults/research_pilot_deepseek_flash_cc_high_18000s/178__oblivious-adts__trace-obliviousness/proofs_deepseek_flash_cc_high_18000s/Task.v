From oadt Require Import lang_oadt.base.

From oadt Require Import lang_oadt.syntax.

From oadt Require Import lang_oadt.semantics.

From oadt Require Import lang_oadt.typing.

From stdpp Require Import stringmap.

Import syntax.notations.

Import semantics.notations.

Import typing.notations.

Implicit Types (b : bool) (x X y Y : atom) (L : aset).

Definition trace_indistinguishable Σ e1 e2 : Prop :=
  forall n e1',
    Σ ⊨ e1 -->{n} e1' ->
    (exists e2', Σ ⊨ e2 -->{n} e2') /\
    (forall e2', Σ ⊨ e2 -->{n} e2' -> e1' ≈ e2').

(* ================================================================ *)
(* Free variables                                                     *)
(* ================================================================ *)
Fixpoint fv (e : expr) : aset :=
  match e with
  | EBVar _ => ∅
  | EFVar x => {[x]}
  | EGVar _ => ∅
  | EUnitT => ∅
  | EUnitV => ∅
  | EBool _ => ∅
  | ELit _ => ∅
  | EProd τ1 τ2 => fv τ1 ∪ fv τ2
  | ESum _ τ1 τ2 => fv τ1 ∪ fv τ2
  | EPi _ τ1 τ2 => fv τ1 ∪ fv τ2
  | EAbs _ τ e => fv τ ∪ fv e
  | EApp e1 e2 => fv e1 ∪ fv e2
  | ELet e1 e2 => fv e1 ∪ fv e2
  | EIte _ e0 e1 e2 => fv e0 ∪ fv e1 ∪ fv e2
  | EPair e1 e2 => fv e1 ∪ fv e2
  | EProj _ e => fv e
  | EInj _ _ τ e => fv τ ∪ fv e
  | ECase _ e0 e1 e2 => fv e0 ∪ fv e1 ∪ fv e2
  | EFold _ e => fv e
  | EUnfold _ e => fv e
  | ESec e => fv e
  | ETape e => fv e
  | EMux e0 e1 e2 => fv e0 ∪ fv e1 ∪ fv e2
  | EBoxedLit _ => ∅
  | EBoxedInj _ τ e => fv τ ∪ fv e
  end.

Lemma fv_subst_le x s e : fv (subst x s e) ⊆ fv s ∪ fv e.
Proof.
  induction e; simpl; try set_solver.
  case_decide; simpl; set_solver.
Qed.

Lemma subst_not_fv x s e : x ∉ fv e -> subst x s e = e.
Proof.
  induction e; simpl; intros H; try done; try set_solver;
  try (repeat f_equal; try (apply IHe1; set_solver); try (apply IHe2; set_solver); try (apply IHe3; set_solver); set_solver).
  case_decide; [exfalso; apply H|]; simpl; set_solver.
Qed.

Lemma fv_open_le : forall (e:expr) (n:nat) (s:expr), fv (open_ n s e) ⊆ fv s ∪ fv e.
Proof.
  induction e; intros n s; simpl; try done; try set_solver;
  try (repeat f_equal; try (apply IHe1; set_solver); try (apply IHe2; set_solver); try (apply IHe3; set_solver); set_solver);
  try (case_decide; simpl; set_solver).
Qed.

(* ================================================================ *)
(* Locally closed (no free bvars) at depth n                          *)
(* ================================================================ *)
Fixpoint lc_n (n : nat) (e : expr) : Prop :=
  match e with
  | EBVar k => k < n
  | EFVar _ => True
  | EGVar _ => True
  | EUnitT => True
  | EUnitV => True
  | EBool _ => True
  | ELit _ => True
  | EProd τ1 τ2 => lc_n n τ1 /\ lc_n n τ2
  | ESum _ τ1 τ2 => lc_n n τ1 /\ lc_n n τ2
  | EPi _ τ1 τ2 => lc_n n τ1 /\ lc_n (S n) τ2
  | EAbs _ τ e => lc_n n τ /\ lc_n (S n) e
  | EApp e1 e2 => lc_n n e1 /\ lc_n n e2
  | ELet e1 e2 => lc_n n e1 /\ lc_n (S n) e2
  | EIte _ e0 e1 e2 => lc_n n e0 /\ lc_n n e1 /\ lc_n n e2
  | EPair e1 e2 => lc_n n e1 /\ lc_n n e2
  | EProj _ e => lc_n n e
  | EInj _ _ τ e => lc_n n τ /\ lc_n n e
  | ECase _ e0 e1 e2 => lc_n n e0 /\ lc_n (S n) e1 /\ lc_n (S n) e2
  | EFold _ e => lc_n n e
  | EUnfold _ e => lc_n n e
  | ESec e => lc_n n e
  | ETape e => lc_n n e
  | EMux e0 e1 e2 => lc_n n e0 /\ lc_n n e1 /\ lc_n n e2
  | EBoxedLit _ => True
  | EBoxedInj _ τ e => lc_n n τ /\ lc_n n e
  end.

Lemma open_lc_n : forall (e:expr) (nn:nat), lc_n nn e ->
  forall jj, nn <= jj -> forall ss, open_ jj ss e = e.
Proof.
  induction e; intros nn Hn jj Hj ss; simpl in *; try done;
  try (destruct Hn as [? [? ?]]); try (destruct Hn as [? ?]).
  all: try (repeat f_equal).
  all: try (eauto using le_n_S).
  all: try (case_decide; [exfalso; lia|done]).
Qed.

Lemma lc_n_mono : forall (e:expr) (nn mm:nat), lc_n nn e -> nn <= mm -> lc_n mm e.
Proof.
  induction e; intros nn mm H Hle; simpl in *; try done.
  all: try (destruct H as [? [? ?]]).
  all: try (destruct H as [? ?]).
  all: try (repeat split; eauto using le_n_S).
  all: lia.
Qed.

Lemma lc_n_open : forall (e:expr) (xx:atom) (nn:nat),
  lc_n nn (open_ nn <{ fvar xx }> e) -> lc_n (S nn) e.
Proof.
  induction e; intros xx nn H; simpl in *; try done.
  all: try (destruct (decide (nn = k)); simpl in *; lia).
  all: try (destruct H as [? [? ?]]).
  all: try (destruct H as [? ?]).
  all: try (repeat split; eauto using lc_n_mono).
Qed.

(* ================================================================ *)
(* Context substitution                                               *)
(* ================================================================ *)
Definition tctx_subst (x : atom) (s : expr) (Γ : tctx) : tctx :=
  (fun T : lexpr => (T.1, subst x s T.2)) <$> Γ.

Lemma tctx_subst_lookup x s Γ y :
  tctx_subst x s Γ !! y = option_map (fun T : lexpr => (T.1, subst x s T.2)) (Γ !! y).
Proof. by unfold tctx_subst; rewrite lookup_fmap. Qed.

Lemma tctx_subst_insert x s y T Γ :
  x ≠ y ->
  tctx_subst x s (<[y:=T]>Γ) = <[y:=(T.1, subst x s T.2)]>(tctx_subst x s Γ).
Proof. intros. by unfold tctx_subst; rewrite fmap_insert. Qed.

Lemma tctx_subst_insert2 xx vv y l τ Γ0 :
  xx ≠ y -> tctx_subst xx vv (<[y:=(l,τ)]>Γ0) = <[y:=(l, subst xx vv τ)]>(tctx_subst xx vv Γ0).
Proof. intros. by rewrite tctx_subst_insert. Qed.

Lemma tctx_subst_subseteq x s Γ Γ' : Γ ⊆ Γ' -> tctx_subst x s Γ ⊆ tctx_subst x s Γ'.
Proof.
  intros H. rewrite map_subseteq_spec in H. rewrite map_subseteq_spec.
  intros k w Hk. rewrite tctx_subst_lookup in Hk.
  rewrite fmap_Some in Hk. destruct Hk as (T & HT & Hw).
  specialize (H k T HT).
  rewrite tctx_subst_lookup.
  change ((fun T0 : lexpr => (T0.1, subst x s T0.2)) <$> (Γ' !! k) = Some w).
  rewrite H. cbn. by rewrite Hw.
Qed.

Lemma map_insert_subset_mono (Γ Γ' : tctx) x T :
  Γ ⊆ Γ' -> <[x:=T]>Γ ⊆ <[x:=T]>Γ'.
Proof.
  intros H. rewrite map_subseteq_spec in H. rewrite map_subseteq_spec.
  intros k w Hk.
  destruct (decide (x = k)) as [->|Hne].
  - rewrite lookup_insert_eq in Hk. simplify_eq. exact (lookup_insert_eq Γ' k w).
  - rewrite lookup_insert_ne in Hk by done. rewrite lookup_insert_ne by done.
    by apply (H k w Hk).
Qed.

Lemma map_subset_insert (Γ : tctx) x T : x ∉ dom Γ -> Γ ⊆ <[x:=T]>Γ.
Proof.
  intros Hx. rewrite map_subseteq_spec. intros i w Hi.
  destruct (decide (x = i)) as [->|Hne].
  - exfalso. apply Hx. by apply elem_of_dom_2 in Hi.
  - by rewrite lookup_insert_ne.
Qed.

Lemma dom_tctx_subst x s Γ : dom (tctx_subst x s Γ) ≡ dom Γ.
Proof. by unfold tctx_subst; rewrite dom_fmap. Qed.

Lemma not_elem_dom_tctx_subst x s Γ y : y ∉ dom Γ -> y ∉ dom (tctx_subst x s Γ).
Proof. intros H. by rewrite dom_tctx_subst. Qed.

Lemma tctx_subst_weaken_insert xx vv Γ0 y (T : lexpr) :
  y ∉ dom Γ0 ->
  tctx_subst xx vv Γ0 ⊆ <[y:=(T.1, subst xx vv T.2)]>(tctx_subst xx vv Γ0).
Proof. intros. apply map_subset_insert. by apply not_elem_dom_tctx_subst. Qed.

Lemma tctx_subst_subset_insert xx vv y l τ Γ0 :
  y ∉ dom Γ0 ->
  tctx_subst xx vv Γ0 ⊆ tctx_subst xx vv (<[y:=(l,τ)]>Γ0).
Proof.
  intros Hy. rewrite map_subseteq_spec. intros k w Hk.
  rewrite tctx_subst_lookup in Hk.
  rewrite tctx_subst_lookup.
  destruct (decide (y = k)) as [E|E].
  - subst k. destruct (Γ0 !! y) as [T|] eqn:E2.
    + simpl in Hk. exfalso. apply Hy. by apply elem_of_dom_2 in E2.
    + simpl in Hk. discriminate.
  - rewrite lookup_insert_ne by done. exact Hk.
Qed.

Lemma map_insert_swap (x y : atom) (T1 T2 : lexpr) (Γ : tctx) :
  x ≠ y -> <[x:=T1]>(<[y:=T2]>Γ) = <[y:=T2]>(<[x:=T1]>Γ).
Proof.
  intros Hxy. apply map_eq. intros k.
  destruct (decide (x = k)) as [->|Hxk]; destruct (decide (y = k)) as [->|Hyk];
    simplify_map_eq; auto.
Qed.

(* ================================================================ *)
(* Weakening                                                          *)
(* ================================================================ *)
Lemma typing_kinding_weaken Σ :
  (forall (Γ : tctx) e l τ, Σ; Γ ⊢ e :{l} τ ->
     forall Γ', Γ ⊆ Γ' -> Σ; Γ' ⊢ e :{l} τ) /\
  (forall (Γ : tctx) τ κ, Σ; Γ ⊢ τ :: κ ->
     forall Γ', Γ ⊆ Γ' -> Σ; Γ' ⊢ τ :: κ).
Proof.
  apply typing_kinding_mutind.
  - (* TFVar *) intros Γ x l τ κ Hlk Hk IH Γ' Hsub. econstructor.
    + rewrite map_subseteq_spec in Hsub. by apply (Hsub x (l,τ) Hlk).
    + by apply IH.
  - (* TUnit *) intros; econstructor.
  - (* TLit *) intros; econstructor.
  - (* TFun *) intros; econstructor; eauto.
  - (* TAbs *) intros Γ l1 l2 e τ1 τ2 κ L Hbody IHbody Hk IHk Γ' Hsub.
    econstructor; eauto using map_insert_subset_mono.
  - (* TLet *) intros Γ l1 l2 l e1 e2 τ1 τ2 L He1 IHe1 Hbody IHbody Hl Γ' Hsub.
    econstructor; eauto using map_insert_subset_mono.
  - (* TApp *) intros; econstructor; eauto.
  - (* TPair *) intros; econstructor; eauto.
  - (* TProj *) intros; econstructor; eauto.
  - (* TInj *) intros; econstructor; eauto.
  - (* TIf *) intros; econstructor; eauto.
  - (* TIfNoDep *) intros; econstructor; eauto.
  - (* TCase *) intros Γ l1 l2 l e0 e1 e2 τ1 τ2 τ κ L1 L2 H0 IH0 Hb1 IHb1 Hb2 IHb2 Hk IHk Hl Γ' Hsub.
    econstructor; eauto using map_insert_subset_mono.
  - (* TCaseNoDep *) intros Γ l0 l1 l2 l e0 e1 e2 τ1 τ2 τ κ L1 L2 H0 IH0 Hb1 IHb1 Hb2 IHb2 Hk IHk Hl Γ' Hsub.
    econstructor; eauto using map_insert_subset_mono.
  - (* TFold *) intros; econstructor; eauto.
  - (* TUnfold *) intros; econstructor; eauto.
  - (* TSec *) intros; econstructor; eauto.
  - (* TMux *) intros; econstructor; eauto.
  - (* TOInj *) intros; econstructor; eauto.
  - (* TOIf *) intros; econstructor; eauto.
  - (* TOCase *) intros Γ l1 l2 e0 e1 e2 τ1 τ2 τ κ L1 L2 H0 IH0 Hb1 IHb1 Hb2 IHb2 Hk IHk Γ' Hsub.
    econstructor; eauto using map_insert_subset_mono.
  - (* TTape *) intros; econstructor; eauto.
  - (* TBoxedLit *) intros; econstructor.
  - (* TBoxedInj *) intros; econstructor; eauto.
  - (* TConv *) intros Γ l l' e τ τ' κ He IHe Hpe Hk IHk Hle Γ' Hsub.
    econstructor; eauto.
  - (* KADT *) intros; econstructor; eauto.
  - (* KUnit *) intros; econstructor.
  - (* KBool *) intros; econstructor.
  - (* KPi *) intros Γ l τ1 τ2 κ1 κ2 L Hbody IHbody Hk IHk Γ' Hsub.
    econstructor; eauto using map_insert_subset_mono.
  - (* KProd *) intros; econstructor; eauto.
  - (* KSum *) intros; econstructor; eauto.
  - (* KOSum *) intros; econstructor; eauto.
  - (* KOADT *) intros; econstructor; eauto.
  - (* KIf *) intros; econstructor; eauto.
  - (* KCase *) intros Γ e0 τ1 τ2 τ1' τ2' L1 L2 H0 IH0 Hb1 IHb1 Hb2 IHb2.
    econstructor; eauto using map_insert_subset_mono.
  - (* KLet *) intros Γ e τ τ' L He IHe Hb IHb.
    econstructor; eauto using map_insert_subset_mono.
  - (* KSub *) intros; econstructor; eauto.
Qed.

Lemma typing_weaken Σ Γ e l τ (H : Σ; Γ ⊢ e :{l} τ) Γ' (Hsub : Γ ⊆ Γ') :
  Σ; Γ' ⊢ e :{l} τ.
Proof. exact (proj1 (typing_kinding_weaken Σ) Γ e l τ H Γ' Hsub). Qed.

Lemma kinding_weaken Σ Γ τ κ (H : Σ; Γ ⊢ τ :: κ) Γ' (Hsub : Γ ⊆ Γ') :
  Σ; Γ' ⊢ τ :: κ.
Proof. exact (proj2 (typing_kinding_weaken Σ) Γ τ κ H Γ' Hsub). Qed.

(* ================================================================ *)
(* Locally-closed lemmas, oval/otval, substitution                    *)
(* ================================================================ *)
Lemma otval_lc_n0 (w : expr) : otval w -> lc_n 0 w.
Proof. induction 1; simpl; auto; split; auto. Qed.

Lemma oval_lc_n0 (v : expr) : oval v -> lc_n 0 v.
Proof. induction 1; simpl; auto; try (split; auto). by apply otval_lc_n0. Qed.

Lemma lc_lc_n0 (e : expr) : lc e -> lc_n 0 e.
Proof.
  induction 1; simpl; try done.
  - split; [by apply IHlc|].
    apply (lc_n_open τ2 (fresh_string_of_set EmptyString L) 0). apply H0. apply fresh_string_of_set_fresh.
  - split; [by apply IHlc|].
    apply (lc_n_open e (fresh_string_of_set EmptyString L) 0). apply H0. apply fresh_string_of_set_fresh.
  - split; [by apply IHlc|].
    apply (lc_n_open e2 (fresh_string_of_set EmptyString L) 0). apply H0. apply fresh_string_of_set_fresh.
  - repeat split.
    + by apply IHlc.
    + apply (lc_n_open e1 (fresh_string_of_set EmptyString L1) 0). apply H0. apply fresh_string_of_set_fresh.
    + apply (lc_n_open e2 (fresh_string_of_set EmptyString L2) 0). apply H2. apply fresh_string_of_set_fresh.
  - split; [by apply otval_lc_n0|by apply oval_lc_n0].
Qed.

Lemma lc_n_subst : forall (e:expr) (nn:nat) (xx:atom) (vv:expr),
  lc_n nn e -> lc_n 0 vv -> lc_n nn (subst xx vv e).
Proof.
  induction e; intros nn xx vv H Hv; simpl in *; try done.
  all: try (destruct H as [? [? ?]]).
  all: try (destruct H as [? ?]).
  all: try (repeat split; auto).
  all: try (destruct (decide (xx = x)) as [->|Hne]; simpl; auto; apply (lc_n_mono vv 0 nn Hv); lia).
  all: try (destruct (decide (xx = a)) as [->|Hne]; simpl; auto; apply (lc_n_mono vv 0 nn Hv); lia).
Qed.

Lemma subst_fvar_neq xx vv y : xx <> y -> subst xx vv <{ fvar y }> = <{ fvar y }>.
Proof. intros H. simpl. by destruct (decide (xx = y)). Qed.

Lemma subst_fvar_eq xx vv : subst xx vv <{ fvar xx }> = vv.
Proof. simpl. by destruct (decide (xx = xx)). Qed.

Lemma subst_open_comm_lc : forall (e:expr) (xx:atom) (vv:expr) (nn:nat) (ss:expr),
  lc_n 0 vv -> subst xx vv (open_ nn ss e) = open_ nn (subst xx vv ss) (subst xx vv e).
Proof.
  induction e; intros xx vv nn ss Hv; simpl; auto;
  try (repeat f_equal; auto; fail).
  all: try (case_decide; simpl; auto;
            try (rewrite (open_lc_n vv 0 Hv nn (Nat.le_0_l nn) (subst xx vv ss)); reflexivity)).
Qed.

Lemma subst_open_open xx vv ss e : lc_n 0 vv ->
  subst xx vv (open ss e) = open (subst xx vv ss) (subst xx vv e).
Proof. intros. by apply subst_open_comm_lc. Qed.

Lemma subst_open_lit xx vv b e : lc_n 0 vv ->
  subst xx vv (open (ELit b) e) = open (ELit b) (subst xx vv e).
Proof. intros Hn. by rewrite (subst_open_open xx vv (ELit b) e Hn). Qed.

Lemma subst_open_fvar_lc2 xx vv y e : lc_n 0 vv -> xx ≠ y ->
  subst xx vv (open <{ fvar y }> e) = open <{ fvar y }> (subst xx vv e).
Proof. intros Hn Hxy. rewrite subst_open_open; auto. by rewrite (subst_fvar_neq xx vv y Hxy). Qed.

Lemma subst_open_fvar_lc xx vv y e :
  lc_n 0 vv -> xx ≠ y -> subst xx vv (open_ 0 <{ fvar y }> e) = open_ 0 <{ fvar y }> (subst xx vv e).
Proof.
  intros Hv Hxy. rewrite subst_open_comm_lc; auto.
  by rewrite subst_fvar_neq.
Qed.

Lemma lc_subst xx vv (Hv : lc vv) e : lc e -> lc (subst xx vv e).
Proof.
  intros He. revert xx vv Hv. induction He; intros xx vv Hv; simpl; try constructor; eauto.
  - (* EFVar *) case_decide; simpl; auto. constructor.
  - (* LCPi *) apply LCPi with (L := L ∪ {[xx]}).
    + intros y Hy. change (lc (open_ 0 <{ fvar y }> (subst xx vv τ2))).
      assert (Hlc : lc_n 0 vv) by (apply lc_lc_n0; auto).
      assert (Heq : open_ 0 <{ fvar y }> (subst xx vv τ2) = subst xx vv (open_ 0 <{ fvar y }> τ2)).
      { symmetry. apply (subst_open_fvar_lc xx vv y τ2); [exact Hlc|set_solver]. }
      rewrite Heq. apply H0; [set_solver|exact Hv].
    + by apply IHHe.
  - (* LCAbs *) apply LCAbs with (L := L ∪ {[xx]}).
    + intros y Hy. change (lc (open_ 0 <{ fvar y }> (subst xx vv e))).
      assert (Hlc : lc_n 0 vv) by (apply lc_lc_n0; auto).
      assert (Heq : open_ 0 <{ fvar y }> (subst xx vv e) = subst xx vv (open_ 0 <{ fvar y }> e)).
      { symmetry. apply (subst_open_fvar_lc xx vv y e); [exact Hlc|set_solver]. }
      rewrite Heq. apply H0; [set_solver|exact Hv].
    + by apply IHHe.
  - (* LCLet *) apply LCLet with (L := L ∪ {[xx]}).
    + intros y Hy. change (lc (open_ 0 <{ fvar y }> (subst xx vv e2))).
      assert (Hlc : lc_n 0 vv) by (apply lc_lc_n0; auto).
      assert (Heq : open_ 0 <{ fvar y }> (subst xx vv e2) = subst xx vv (open_ 0 <{ fvar y }> e2)).
      { symmetry. apply (subst_open_fvar_lc xx vv y e2); [exact Hlc|set_solver]. }
      rewrite Heq. apply H0; [set_solver|exact Hv].
    + by apply IHHe.
  - (* LCCase *) apply LCCase with (L1 := L1 ∪ {[xx]}) (L2 := L2 ∪ {[xx]}).
    + intros y Hy. change (lc (open_ 0 <{ fvar y }> (subst xx vv e1))).
      assert (Hlc : lc_n 0 vv) by (apply lc_lc_n0; auto).
      assert (Heq : open_ 0 <{ fvar y }> (subst xx vv e1) = subst xx vv (open_ 0 <{ fvar y }> e1)).
      { symmetry. apply (subst_open_fvar_lc xx vv y e1); [exact Hlc|set_solver]. }
      rewrite Heq. apply H0; [set_solver|exact Hv].
    + intros y Hy. change (lc (open_ 0 <{ fvar y }> (subst xx vv e2))).
      assert (Hlc : lc_n 0 vv) by (apply lc_lc_n0; auto).
      assert (Heq : open_ 0 <{ fvar y }> (subst xx vv e2) = subst xx vv (open_ 0 <{ fvar y }> e2)).
      { symmetry. apply (subst_open_fvar_lc xx vv y e2); [exact Hlc|set_solver]. }
      rewrite Heq. apply H2; [set_solver|exact Hv].
    + by apply IHHe.
Qed.

Lemma otval_subst x s w : otval w -> otval (subst x s w).
Proof. induction 1; simpl; constructor; auto. Qed.

Lemma otval_fv_empty w : otval w -> fv w = ∅.
Proof. induction 1; simpl; auto; rewrite empty_union_L; auto. Qed.

Lemma oval_fv_empty v : oval v -> fv v = ∅.
Proof.
  induction 1; simpl.
  - done. - done.
  - rewrite empty_union_L; split; auto.
  - rewrite empty_union_L; split; [by apply otval_fv_empty|done].
Qed.

Lemma woval_fv_empty v : woval v -> fv v = ∅.
Proof.
  induction 1; simpl.
  - done. - done.
  - rewrite empty_union_L; split; auto.
  - rewrite empty_union_L; split; [by apply otval_fv_empty|by apply oval_fv_empty].
  - rewrite empty_union_L. split.
    + rewrite IHwoval1, empty_union_L. done.
    + auto.
Qed.

Lemma oval_not_fv x v : oval v -> x ∉ fv v.
Proof. intros H. by rewrite (oval_fv_empty v H). Qed.

Lemma otval_not_fv x w : otval w -> x ∉ fv w.
Proof. intros H. by rewrite (otval_fv_empty w H). Qed.

Lemma oval_subst x s v : oval v -> oval (subst x s v).
Proof. induction 1; simpl; constructor; auto using otval_subst. Qed.

Lemma woval_subst x s v : woval v -> woval (subst x s v).
Proof. induction 1; simpl; constructor; auto using otval_subst, oval_subst. Qed.

Lemma ovalty_subst_val x s v w : ovalty v w -> ovalty (subst x s v) w.
Proof.
  induction 1; simpl.
  - apply OTUnit.
  - apply OTOBool.
  - apply OTProd; auto.
  - apply OTOSum; auto.
Qed.

Lemma ovalty_otval v w : ovalty v w -> otval w.
Proof.
  induction 1; simpl.
  - constructor.
  - constructor.
  - constructor; auto.
  - destruct b; simpl in *; apply OVOSum; auto.
Qed.

Lemma ovalty_oval v w : ovalty v w -> oval v.
Proof.
  induction 1; simpl.
  - constructor.
  - constructor.
  - constructor; auto.
  - destruct b; simpl in *.
    + apply OVBoxedInj.
      * apply OVOSum; [exact (ovalty_otval v ω1 H)|exact H0].
      * exact IHovalty.
    + apply OVBoxedInj.
      * apply OVOSum; [exact H0|exact (ovalty_otval v ω2 H)].
      * exact IHovalty.
Qed.

Lemma ovalty_inj_oval b ω v : ovalty <{ [inj@b<ω> v] }> ω -> oval v.
Proof.
  intros H. inversion H; subst. eapply ovalty_oval. eassumption.
Qed.

(* ================================================================ *)
(* Free variables of the global context                               *)
(* ================================================================ *)
Definition gdef_fv (D : gdef) : aset :=
  match D with
  | DADT τ => fv τ
  | DFun T e => fv (snd (A := llabel) T) ∪ fv e
  | DOADT τ e => fv τ ∪ fv e
  end.

Definition gctx_fv (Σ : gctx) : aset :=
  foldr (fun p acc => gdef_fv (p.2) ∪ acc) ∅ (map_to_list Σ).

Lemma elem_of_gctx_fv_aux (l : list (atom * gdef)) x :
  (exists p, p ∈ l /\ x ∈ gdef_fv (p.2)) ->
  x ∈ foldr (fun p acc => gdef_fv (p.2) ∪ acc) ∅ l.
Proof.
  induction l as [|p l IH]; simpl; intros [q [Hin Hx]].
  - inversion Hin.
  - apply elem_of_cons in Hin as [->|Hin].
    + by apply elem_of_union_l.
    + apply elem_of_union_r. by apply IH; exists q.
Qed.

Lemma gctx_fv_spec Σ y D x : Σ !! y = Some D -> x ∈ gdef_fv D -> x ∈ gctx_fv Σ.
Proof.
  intros H Hx. unfold gctx_fv.
  apply elem_of_gctx_fv_aux. exists (y,D). split; [|done].
  by apply elem_of_map_to_list.
Qed.

Lemma gctx_fv_notin Σ y D x : x ∉ gctx_fv Σ -> Σ !! y = Some D -> x ∉ gdef_fv D.
Proof. intros H1 H2 H3. by apply H1, (gctx_fv_spec Σ y D x). Qed.

(* ================================================================ *)
(* Parallel reduction is a congruence for substitution                *)
(* ================================================================ *)
Ltac pb xx vv Hn E E' IH L :=
  let y := fresh "y" in
  intros y Hy;
  let Hyx := fresh "Hyx" in assert (Hyx : xx ≠ y) by (intros ->; apply Hy; set_solver);
  let He1 := fresh "He1" in
  assert (He1 : open (EFVar y) (subst xx vv E) = subst xx vv (open (EFVar y) E))
    by (symmetry; rewrite (subst_open_open xx vv (EFVar y) E Hn);
        by rewrite (subst_fvar_neq xx vv y Hyx));
  let He2 := fresh "He2" in
  assert (He2 : open (EFVar y) (subst xx vv E') = subst xx vv (open (EFVar y) E'))
    by (symmetry; rewrite (subst_open_open xx vv (EFVar y) E' Hn);
        by rewrite (subst_fvar_neq xx vv y Hyx));
  rewrite He1, He2;
  apply (IH y); set_solver.

Lemma pared_subst Σ xx vv (Hv : lc vv) (HΣ : xx ∉ gctx_fv Σ) :
  forall e e', pared Σ e e' -> pared Σ (subst xx vv e) (subst xx vv e').
Proof.
  assert (Hn : lc_n 0 vv) by (apply lc_lc_n0; auto).
  intros e e' H. induction H.
  - (* RApp *) simpl. rewrite (subst_open_open xx vv e1' e2' Hn).
    eapply RApp with (L := L ∪ {[xx]}).
    + exact IHpared.
    + pb xx vv Hn e2 e2' H1 L.
    + apply lc_subst; auto.
  - (* RFun *) simpl.
    assert (Hx : xx ∉ gdef_fv (DFun T e)) by (apply (gctx_fv_notin Σ x (DFun T e) xx); auto).
    simpl in Hx. assert (Hfe : xx ∉ fv e) by set_solver.
    rewrite (subst_not_fv xx vv e Hfe). exact (RFun Σ x T e H).
  - (* ROADT *) simpl.
    assert (Hx : xx ∉ gdef_fv (DOADT τ' τ)) by (apply (gctx_fv_notin Σ X (DOADT τ' τ) xx); auto).
    simpl in Hx. assert (Hfτ : xx ∉ fv τ) by set_solver.
    rewrite (subst_open_open xx vv e' τ Hn).
    rewrite (subst_not_fv xx vv τ Hfτ).
    exact (ROADT Σ X τ' τ (subst xx vv e) (subst xx vv e') H IHpared).
  - (* RLet *) simpl. rewrite (subst_open_open xx vv e1' e2' Hn).
    eapply RLet with (L := L ∪ {[xx]}).
    + exact IHpared.
    + pb xx vv Hn e2 e2' H1 L.
  - (* RProj *) destruct b; simpl;
      [ eapply RProj with (b := true) | eapply RProj with (b := false) ]; eauto.
  - (* RFold *) simpl. eapply RFold. exact IHpared.
  - (* RIf *) destruct b; simpl;
      [ eapply RIf with (b := true) | eapply RIf with (b := false) ]; eauto.
  - (* RCase *) destruct b; simpl.
    + rewrite (subst_open_open xx vv e0' e1' Hn).
      eapply RCase with (b := true) (L1 := L1 ∪ {[xx]}) (L2 := L2 ∪ {[xx]}).
      * exact IHpared.
      * pb xx vv Hn e1 e1' H1 L1.
      * pb xx vv Hn e2 e2' H3 L2.
      * apply lc_subst; auto.
    + rewrite (subst_open_open xx vv e0' e2' Hn).
      eapply RCase with (b := false) (L1 := L1 ∪ {[xx]}) (L2 := L2 ∪ {[xx]}).
      * exact IHpared.
      * pb xx vv Hn e1 e1' H1 L1.
      * pb xx vv Hn e2 e2' H3 L2.
      * apply lc_subst; auto.
  - (* RMux *) destruct b; simpl;
      [ eapply RMux with (b := true) | eapply RMux with (b := false) ]; eauto.
  - (* RSec *) simpl. apply RSec.
  - (* ROInj *) simpl.
    rewrite (subst_not_fv xx vv ω (otval_not_fv xx ω H)).
    rewrite (subst_not_fv xx vv v (oval_not_fv xx v H0)).
    apply ROInj; auto.
  - (* ROIf *) destruct b; simpl;
      [ eapply ROIf with (b := true) | eapply ROIf with (b := false) ]; eauto.
  - (* ROCase *) destruct b; simpl.
    + rewrite (subst_open_open xx vv v e1' Hn).
      rewrite (subst_open_open xx vv v2 e2' Hn).
      rewrite (subst_not_fv xx vv v (oval_not_fv xx v H)).
      rewrite (subst_not_fv xx vv v2 (oval_not_fv xx v2 (ovalty_oval v2 ω2 H1))).
      eapply ROCase with (b := true) (v1 := v1) (v2 := v2) (e1 := subst xx vv e1) (e2 := subst xx vv e2) (e1' := subst xx vv e1') (e2' := subst xx vv e2') (L1 := L1 ∪ {[xx]}) (L2 := L2 ∪ {[xx]}).
      * exact H.
      * exact H0.
      * exact H1.
      * pb xx vv Hn e1 e1' H3 L1.
      * pb xx vv Hn e2 e2' H5 L2.
    + rewrite (subst_open_open xx vv v e2' Hn).
      rewrite (subst_open_open xx vv v1 e1' Hn).
      rewrite (subst_not_fv xx vv v (oval_not_fv xx v H)).
      rewrite (subst_not_fv xx vv v1 (oval_not_fv xx v1 (ovalty_oval v1 ω1 H0))).
      eapply ROCase with (b := false) (v1 := v1) (v2 := v2) (e1 := subst xx vv e1) (e2 := subst xx vv e2) (e1' := subst xx vv e1') (e2' := subst xx vv e2') (L1 := L1 ∪ {[xx]}) (L2 := L2 ∪ {[xx]}).
      * exact H.
      * exact H0.
      * exact H1.
      * pb xx vv Hn e1 e1' H3 L1.
      * pb xx vv Hn e2 e2' H5 L2.
  - (* ROIfApp *) simpl. eapply ROIfApp; eauto.
  - (* ROIfSec *) simpl. eapply ROIfSec; eauto.
  - (* ROIfIf *) simpl. eapply ROIfIf; eauto.
  - (* ROIfProj *) simpl. eapply ROIfProj; eauto.
  - (* ROIfCase *) simpl.
    eapply ROIfCase with (L1 := L1 ∪ {[xx]}) (L2 := L2 ∪ {[xx]}).
    + eauto.
    + eauto.
    + pb xx vv Hn e3 e3' H2 L1.
    + pb xx vv Hn e4 e4' H4 L2.
  - (* ROIfUnfold *) simpl. eapply ROIfUnfold; eauto.
  - (* RTapeOIf *) simpl. eapply RTapeOIf; eauto.
  - (* RTapePair *) simpl. eapply RTapePair; eauto using woval_subst.
  - (* RTapeUnitV *) simpl. apply RTapeUnitV.
  - (* RTapeBoxedLit *) simpl. apply RTapeBoxedLit.
  - (* RTapeBoxedInj *) simpl. apply RTapeBoxedInj; auto.
  - (* RCgrPi *) simpl. eapply RCgrPi with (L := L ∪ {[xx]}).
    + exact IHpared.
    + pb xx vv Hn τ2 τ2' H1 L.
  - (* RCgrAbs *) simpl. eapply RCgrAbs with (L := L ∪ {[xx]}).
    + exact IHpared.
    + pb xx vv Hn e e' H1 L.
  - (* RCgrApp *) simpl. eapply RCgrApp; eauto.
  - (* RCgrLet *) simpl. eapply RCgrLet with (L := L ∪ {[xx]}).
    + exact IHpared.
    + pb xx vv Hn e2 e2' H1 L.
  - (* RCgrSec *) simpl. eapply RCgrSec; eauto.
  - (* RCgrIf *) simpl. eapply RCgrIf; eauto.
  - (* RCgrProd *) simpl. eapply RCgrProd; eauto.
  - (* RCgrPair *) simpl. eapply RCgrPair; eauto.
  - (* RCgrProj *) simpl. eapply RCgrProj; eauto.
  - (* RCgrSum *) simpl. eapply RCgrSum; eauto.
  - (* RCgrInj *) simpl. eapply RCgrInj; eauto.
  - (* RCgrCase *) simpl.
    eapply RCgrCase with (L1 := L1 ∪ {[xx]}) (L2 := L2 ∪ {[xx]}).
    + eauto.
    + pb xx vv Hn e1 e1' H1 L1.
    + pb xx vv Hn e2 e2' H3 L2.
  - (* RCgrFold *) simpl. eapply RCgrFold; eauto.
  - (* RCgrUnfold *) simpl. eapply RCgrUnfold; eauto.
  - (* RCgrMux *) simpl. eapply RCgrMux; eauto.
  - (* RCgrTape *) simpl. eapply RCgrTape; eauto.
  - (* RRefl *) simpl. apply RRefl. apply lc_subst; auto.
Qed.

Lemma pared_equiv_subst Σ xx vv (Hv : lc vv) (HΣ : xx ∉ gctx_fv Σ) :
  forall e1 e2, pared_equiv Σ e1 e2 ->
    pared_equiv Σ (subst xx vv e1) (subst xx vv e2).
Proof.
  intros e1 e2 H. induction H.
  - apply QRRefl.
  - eapply QRRedL.
    + apply (pared_subst Σ xx vv Hv HΣ); eauto.
    + assumption.
  - eapply QRRedR.
    + apply (pared_subst Σ xx vv Hv HΣ); eauto.
    + assumption.
Qed.

(* ================================================================ *)
(* Typing/kinding substitution                                        *)
(* ================================================================ *)
Lemma subst_open_inj_l xx vv b w1 w2 y τ : lc_n 0 vv -> xx ≠ y ->
  subst xx vv (open (EInj false b (ESum false w1 w2) (EFVar y)) τ)
  = open (EInj false b (ESum false (subst xx vv w1) (subst xx vv w2)) (EFVar y)) (subst xx vv τ).
Proof.
  intros Hn Hxy. rewrite subst_open_open; auto.
  change (open (EInj false b (ESum false (subst xx vv w1) (subst xx vv w2)) (subst xx vv (EFVar y))) (subst xx vv τ)
          = open (EInj false b (ESum false (subst xx vv w1) (subst xx vv w2)) (EFVar y)) (subst xx vv τ)).
  by rewrite (subst_fvar_neq xx vv y Hxy).
Qed.

Lemma subst_open_inj_l0 xx vv b w1 w2 y τ : lc_n 0 vv -> xx ≠ y ->
  subst xx vv (open_ 0 (EInj false b (ESum false w1 w2) (EFVar y)) τ)
  = open_ 0 (EInj false b (ESum false (subst xx vv w1) (subst xx vv w2)) (EFVar y)) (subst xx vv τ).
Proof. intros Hn Hxy. by apply subst_open_inj_l. Qed.

Lemma tctx_subst_insert_self x s T (Γ : tctx) :
  tctx_subst x s (<[x:=T]>Γ) = <[x:=(T.1, subst x s T.2)]>(tctx_subst x s Γ).
Proof. intros. unfold tctx_subst. by rewrite fmap_insert. Qed.

Lemma subst_ite x s (b : bool) e1 e2 :
  subst x s (if b then e1 else e2) = (if b then subst x s e1 else subst x s e2).
Proof. intros. by destruct b. Qed.

(* Binder helper: dependent body and type. *)
Ltac tsub_bind_fvar Σ xx vv Hn Γ Γ0 lx τx Hvv Hdom Heq l T E Ety IHbody L :=
  let y := fresh "y" in intros y Hy;
  let Hyx := fresh "Hyx" in assert (Hyx : xx <> y) by (intros ->; apply Hy; set_solver);
  let HyL := fresh "HyL" in assert (HyL : y ∉ L) by set_solver;
  let Hydom := fresh "Hydom" in assert (Hydom : y ∉ dom Γ0) by set_solver;
  rewrite <- (subst_open_fvar_lc2 xx vv y E Hn Hyx);
  rewrite <- (subst_open_fvar_lc2 xx vv y Ety Hn Hyx);
  rewrite <- (tctx_subst_insert2 xx vv y l T Γ0 Hyx);
  set (Γ0' := <[y:=(l,T)]>Γ0);
  assert (Heq' : <[y:=(l,T)]>Γ = <[xx:=(lx,τx)]>Γ0')
    by (rewrite Heq; subst Γ0'; apply (map_insert_swap y xx (l,T) (lx,τx) Γ0);
        intros H; apply Hyx; symmetry; exact H);
  assert (Hdom' : xx ∉ dom Γ0') by (subst Γ0'; rewrite dom_insert; set_solver);
  assert (Hvv' : (Σ; (tctx_subst xx vv Γ0') ⊢ vv :{lx} <{ {xx ↦ vv} τx }>))
    by (subst Γ0'; eapply typing_weaken; [exact Hvv|];
        rewrite (tctx_subst_insert2 xx vv y l T Γ0 Hyx);
        apply map_subset_insert; apply not_elem_dom_tctx_subst; exact Hydom);
  apply (IHbody y HyL Γ0' lx τx Heq' Hdom' Hvv').

(* Binder helper: non-dependent type. *)
Ltac tsub_bind_fvar_nd Σ xx vv Hn Γ Γ0 lx τx Hvv Hdom Heq l T E IHbody L :=
  let y := fresh "y" in intros y Hy;
  let Hyx := fresh "Hyx" in assert (Hyx : xx <> y) by (intros ->; apply Hy; set_solver);
  let HyL := fresh "HyL" in assert (HyL : y ∉ L) by set_solver;
  let Hydom := fresh "Hydom" in assert (Hydom : y ∉ dom Γ0) by set_solver;
  rewrite <- (subst_open_fvar_lc2 xx vv y E Hn Hyx);
  rewrite <- (tctx_subst_insert2 xx vv y l T Γ0 Hyx);
  set (Γ0' := <[y:=(l,T)]>Γ0);
  assert (Heq' : <[y:=(l,T)]>Γ = <[xx:=(lx,τx)]>Γ0')
    by (rewrite Heq; subst Γ0'; apply (map_insert_swap y xx (l,T) (lx,τx) Γ0);
        intros H; apply Hyx; symmetry; exact H);
  assert (Hdom' : xx ∉ dom Γ0') by (subst Γ0'; rewrite dom_insert; set_solver);
  assert (Hvv' : (Σ; (tctx_subst xx vv Γ0') ⊢ vv :{lx} <{ {xx ↦ vv} τx }>))
    by (subst Γ0'; eapply typing_weaken; [exact Hvv|];
        rewrite (tctx_subst_insert2 xx vv y l T Γ0 Hyx);
        apply map_subset_insert; apply not_elem_dom_tctx_subst; exact Hydom);
  apply (IHbody y HyL Γ0' lx τx Heq' Hdom' Hvv').

(* Binder helper: dependent type of the form open (inj ... (fvar y)) tau. *)
Ltac tsub_bind_case Σ xx vv Hn Γ Γ0 lx τx Hvv Hdom Heq b w1 w2 l T E Ety IHbody L :=
  let y := fresh "y" in intros y Hy;
  let Hyx := fresh "Hyx" in assert (Hyx : xx <> y) by (intros ->; apply Hy; set_solver);
  let HyL := fresh "HyL" in assert (HyL : y ∉ L) by set_solver;
  let Hydom := fresh "Hydom" in assert (Hydom : y ∉ dom Γ0) by set_solver;
  rewrite <- (subst_open_fvar_lc2 xx vv y E Hn Hyx);
  rewrite <- (subst_open_inj_l xx vv b w1 w2 y Ety Hn Hyx);
  rewrite <- (tctx_subst_insert2 xx vv y l T Γ0 Hyx);
  set (Γ0' := <[y:=(l,T)]>Γ0);
  assert (Heq' : <[y:=(l,T)]>Γ = <[xx:=(lx,τx)]>Γ0')
    by (rewrite Heq; subst Γ0'; apply (map_insert_swap y xx (l,T) (lx,τx) Γ0);
        intros H; apply Hyx; symmetry; exact H);
  assert (Hdom' : xx ∉ dom Γ0') by (subst Γ0'; rewrite dom_insert; set_solver);
  assert (Hvv' : (Σ; (tctx_subst xx vv Γ0') ⊢ vv :{lx} <{ {xx ↦ vv} τx }>))
    by (subst Γ0'; eapply typing_weaken; [exact Hvv|];
        rewrite (tctx_subst_insert2 xx vv y l T Γ0 Hyx);
        apply map_subset_insert; apply not_elem_dom_tctx_subst; exact Hydom);
  apply (IHbody y HyL Γ0' lx τx Heq' Hdom' Hvv').

(* Binder helper for kinding. *)
Ltac tsub_bind_kind Σ xx vv Hn Γ Γ0 lx τx Hvv Hdom Heq l T E IHbody L :=
  let y := fresh "y" in intros y Hy;
  let Hyx := fresh "Hyx" in assert (Hyx : xx <> y) by (intros ->; apply Hy; set_solver);
  let HyL := fresh "HyL" in assert (HyL : y ∉ L) by set_solver;
  let Hydom := fresh "Hydom" in assert (Hydom : y ∉ dom Γ0) by set_solver;
  rewrite <- (subst_open_fvar_lc2 xx vv y E Hn Hyx);
  rewrite <- (tctx_subst_insert2 xx vv y l T Γ0 Hyx);
  set (Γ0' := <[y:=(l,T)]>Γ0);
  assert (Heq' : <[y:=(l,T)]>Γ = <[xx:=(lx,τx)]>Γ0')
    by (rewrite Heq; subst Γ0'; apply (map_insert_swap y xx (l,T) (lx,τx) Γ0);
        intros H; apply Hyx; symmetry; exact H);
  assert (Hdom' : xx ∉ dom Γ0') by (subst Γ0'; rewrite dom_insert; set_solver);
  assert (Hvv' : (Σ; (tctx_subst xx vv Γ0') ⊢ vv :{lx} <{ {xx ↦ vv} τx }>))
    by (subst Γ0'; eapply typing_weaken; [exact Hvv|];
        rewrite (tctx_subst_insert2 xx vv y l T Γ0 Hyx);
        apply map_subset_insert; apply not_elem_dom_tctx_subst; exact Hydom);
  apply (IHbody y HyL Γ0' lx τx Heq' Hdom' Hvv').

Lemma typing_kinding_subst Σ xx vv (Hv : lc vv) (HΣ : xx ∉ gctx_fv Σ) :
  (forall Γ e l τ, Σ; Γ ⊢ e :{l} τ ->
     forall Γ0 lx τx,
       Γ = <[xx:=(lx,τx)]>Γ0 ->
       xx ∉ dom Γ0 ->
       Σ; (tctx_subst xx vv Γ0) ⊢ vv :{lx} <{ {xx ↦ vv} τx }> ->
       Σ; (tctx_subst xx vv Γ0) ⊢ <{ {xx ↦ vv} e }> :{l} <{ {xx ↦ vv} τ }>) /\
  (forall Γ τ κ, Σ; Γ ⊢ τ :: κ ->
     forall Γ0 lx τx,
       Γ = <[xx:=(lx,τx)]>Γ0 ->
       xx ∉ dom Γ0 ->
       Σ; (tctx_subst xx vv Γ0) ⊢ vv :{lx} <{ {xx ↦ vv} τx }> ->
       Σ; (tctx_subst xx vv Γ0) ⊢ <{ {xx ↦ vv} τ }> :: κ).
Proof.
  assert (Hn : lc_n 0 vv) by (apply lc_lc_n0; auto).
  apply typing_kinding_mutind.
  - (* TFVar *)
    intros Γ x l τ κ Hlk Hk IHk Γ0 lx τx Heq Hdom Hvv.
    destruct (decide (x = xx)) as [Heqx|Hne].
    + subst x.
      rewrite Heq in Hlk. rewrite lookup_insert_eq in Hlk. simplify_eq.
      rewrite subst_fvar_eq. exact Hvv.
    + assert (Hne' : xx <> x) by (intros H; apply Hne; symmetry; exact H).
      rewrite (subst_fvar_neq xx vv x Hne').
      assert (Hlk0 : Γ0 !! x = Some (l, τ)).
      { rewrite Heq in Hlk.
        rewrite lookup_insert_ne in Hlk by (intro H; apply Hne; symmetry; exact H).
        exact Hlk. }
      apply (TFVar Σ (tctx_subst xx vv Γ0) x l (subst xx vv τ) κ).
      * rewrite tctx_subst_lookup.
        destruct (Γ0 !! x) as [[l' τ']|] eqn:E.
        -- inversion Hlk0; subst. cbn. reflexivity.
        -- discriminate.
      * apply (IHk Γ0 lx τx Heq Hdom Hvv).
  - (* TUnit *)
    intros Γ Γ0 lx τx Heq Hdom Hvv.
    apply (TUnit Σ (tctx_subst xx vv Γ0)).
  - (* TLit *)
    intros Γ b Γ0 lx τx Heq Hdom Hvv.
    apply (TLit Σ (tctx_subst xx vv Γ0) b).
  - (* TFun *)
    intros Γ x l τ e Hdef Γ0 lx τx Heq Hdom Hvv.
    assert (Hnot : xx ∉ fv τ) by
      (intros Hx; apply HΣ; apply (gctx_fv_spec Σ x (DFun (l,τ) e) xx Hdef); simpl; set_solver).
    rewrite (subst_not_fv xx vv τ Hnot).
    apply (TFun Σ (tctx_subst xx vv Γ0) x l τ e Hdef).
  - (* TAbs *)
    intros Γ l1 l2 e τ1 τ2 κ L Hbody IHbody Hk IHk Γ0 lx τx Heq Hdom Hvv.
    apply (TAbs Σ (tctx_subst xx vv Γ0) l1 l2 (subst xx vv e) (subst xx vv τ1) (subst xx vv τ2) κ (L ∪ dom Γ0 ∪ {[xx]})).
    + tsub_bind_fvar Σ xx vv Hn Γ Γ0 lx τx Hvv Hdom Heq l2 τ2 e τ1 IHbody L.
    + apply (IHk Γ0 lx τx Heq Hdom Hvv).
  - (* TLet *)
    intros Γ l1 l2 l e1 e2 τ1 τ2 L He1 IHe1 Hbody IHbody Hl Γ0 lx τx Heq Hdom Hvv.
    rewrite (subst_open_open xx vv e1 τ2 Hn).
    apply (TLet Σ (tctx_subst xx vv Γ0) l1 l2 l (subst xx vv e1) (subst xx vv e2) (subst xx vv τ1) (subst xx vv τ2) (L ∪ dom Γ0 ∪ {[xx]})).
    + apply (IHe1 Γ0 lx τx Heq Hdom Hvv).
    + tsub_bind_fvar Σ xx vv Hn Γ Γ0 lx τx Hvv Hdom Heq l1 τ1 e2 τ2 IHbody L.
    + exact Hl.
  - (* TApp *)
    intros Γ l1 l2 e1 e2 τ1 τ2 He1 IHe1 He2 IHe2 Γ0 lx τx Heq Hdom Hvv.
    rewrite (subst_open_open xx vv e2 τ1 Hn).
    apply (TApp Σ (tctx_subst xx vv Γ0) l1 l2 (subst xx vv e1) (subst xx vv e2) (subst xx vv τ1) (subst xx vv τ2)).
    + apply (IHe1 Γ0 lx τx Heq Hdom Hvv).
    + apply (IHe2 Γ0 lx τx Heq Hdom Hvv).
  - (* TPair *)
    intros Γ l1 l2 l e1 e2 τ1 τ2 He1 IHe1 He2 IHe2 Hl Γ0 lx τx Heq Hdom Hvv.
    apply (TPair Σ (tctx_subst xx vv Γ0) l1 l2 l (subst xx vv e1) (subst xx vv e2) (subst xx vv τ1) (subst xx vv τ2)).
    + apply (IHe1 Γ0 lx τx Heq Hdom Hvv).
    + apply (IHe2 Γ0 lx τx Heq Hdom Hvv).
    + exact Hl.
  - (* TProj *)
    intros Γ l b e τ1 τ2 He IHe Γ0 lx τx Heq Hdom Hvv.
    rewrite (subst_ite xx vv b τ1 τ2).
    apply (TProj Σ (tctx_subst xx vv Γ0) l b (subst xx vv e) (subst xx vv τ1) (subst xx vv τ2)).
    apply (IHe Γ0 lx τx Heq Hdom Hvv).
  - (* TInj *)
    intros Γ l b e τ1 τ2 κ He IHe Hk IHk Γ0 lx τx Heq Hdom Hvv.
    apply (TInj Σ (tctx_subst xx vv Γ0) l b (subst xx vv e) (subst xx vv τ1) (subst xx vv τ2) κ).
    + rewrite <- (subst_ite xx vv b τ1 τ2).
      apply (IHe Γ0 lx τx Heq Hdom Hvv).
    + apply (IHk Γ0 lx τx Heq Hdom Hvv).
  - (* TIf *)
    intros Γ l1 l2 l e0 e1 e2 τ κ He0 IHe0 He1 IHe1 He2 IHe2 Hk IHk Hl Γ0 lx τx Heq Hdom Hvv.
    rewrite (subst_open_open xx vv e0 τ Hn).
    apply (TIf Σ (tctx_subst xx vv Γ0) l1 l2 l (subst xx vv e0) (subst xx vv e1) (subst xx vv e2) (subst xx vv τ) κ).
    + apply (IHe0 Γ0 lx τx Heq Hdom Hvv).
    + rewrite <- (subst_open_lit xx vv true τ Hn).
      apply (IHe1 Γ0 lx τx Heq Hdom Hvv).
    + rewrite <- (subst_open_lit xx vv false τ Hn).
      apply (IHe2 Γ0 lx τx Heq Hdom Hvv).
    + rewrite <- (subst_open_open xx vv e0 τ Hn).
      apply (IHk Γ0 lx τx Heq Hdom Hvv).
    + exact Hl.
  - (* TIfNoDep *)
    intros Γ l0 l1 l2 l e0 e1 e2 τ He0 IHe0 He1 IHe1 He2 IHe2 Hl Γ0 lx τx Heq Hdom Hvv.
    apply (TIfNoDep Σ (tctx_subst xx vv Γ0) l0 l1 l2 l (subst xx vv e0) (subst xx vv e1) (subst xx vv e2) (subst xx vv τ)).
    + apply (IHe0 Γ0 lx τx Heq Hdom Hvv).
    + apply (IHe1 Γ0 lx τx Heq Hdom Hvv).
    + apply (IHe2 Γ0 lx τx Heq Hdom Hvv).
    + exact Hl.
  - (* TCase *)
    intros Γ l1 l2 l e0 e1 e2 τ1 τ2 τ κ L1 L2 H0 IH0 Hb1 IHb1 Hb2 IHb2 Hk IHk Hl Γ0 lx τx Heq Hdom Hvv.
    rewrite (subst_open_open xx vv e0 τ Hn).
    apply (TCase Σ (tctx_subst xx vv Γ0) l1 l2 l (subst xx vv e0) (subst xx vv e1) (subst xx vv e2) (subst xx vv τ1) (subst xx vv τ2) (subst xx vv τ) κ (L1 ∪ dom Γ0 ∪ {[xx]}) (L2 ∪ dom Γ0 ∪ {[xx]})).
    + apply (IH0 Γ0 lx τx Heq Hdom Hvv).
    + tsub_bind_case Σ xx vv Hn Γ Γ0 lx τx Hvv Hdom Heq true τ1 τ2 (⊥ : bool) τ1 e1 τ IHb1 L1.
    + tsub_bind_case Σ xx vv Hn Γ Γ0 lx τx Hvv Hdom Heq false τ1 τ2 (⊥ : bool) τ2 e2 τ IHb2 L2.
    + rewrite <- (subst_open_open xx vv e0 τ Hn).
      apply (IHk Γ0 lx τx Heq Hdom Hvv).
    + exact Hl.
  - (* TCaseNoDep *)
    intros Γ l0 l1 l2 l e0 e1 e2 τ1 τ2 τ κ L1 L2 H0 IH0 Hb1 IHb1 Hb2 IHb2 Hk IHk Hl Γ0 lx τx Heq Hdom Hvv.
    apply (TCaseNoDep Σ (tctx_subst xx vv Γ0) l0 l1 l2 l (subst xx vv e0) (subst xx vv e1) (subst xx vv e2) (subst xx vv τ1) (subst xx vv τ2) (subst xx vv τ) κ (L1 ∪ dom Γ0 ∪ {[xx]}) (L2 ∪ dom Γ0 ∪ {[xx]})).
    + apply (IH0 Γ0 lx τx Heq Hdom Hvv).
    + tsub_bind_fvar_nd Σ xx vv Hn Γ Γ0 lx τx Hvv Hdom Heq l0 τ1 e1 IHb1 L1.
    + tsub_bind_fvar_nd Σ xx vv Hn Γ Γ0 lx τx Hvv Hdom Heq l0 τ2 e2 IHb2 L2.
    + apply (IHk Γ0 lx τx Heq Hdom Hvv).
    + exact Hl.
  - (* TFold *)
    intros Γ l X e τ HX He IHe Γ0 lx τx Heq Hdom Hvv.
    assert (Hnot : xx ∉ fv τ) by
      (intros Hx; apply HΣ; apply (gctx_fv_spec Σ X (DADT τ) xx HX); simpl; set_solver).
    apply (TFold Σ (tctx_subst xx vv Γ0) l X (subst xx vv e) τ HX).
    rewrite <- (subst_not_fv xx vv τ Hnot).
    apply (IHe Γ0 lx τx Heq Hdom Hvv).
  - (* TUnfold *)
    intros Γ l X e τ HX He IHe Γ0 lx τx Heq Hdom Hvv.
    assert (Hnot : xx ∉ fv τ) by
      (intros Hx; apply HΣ; apply (gctx_fv_spec Σ X (DADT τ) xx HX); simpl; set_solver).
    rewrite (subst_not_fv xx vv τ Hnot).
    apply (TUnfold Σ (tctx_subst xx vv Γ0) l X (subst xx vv e) τ HX).
    apply (IHe Γ0 lx τx Heq Hdom Hvv).
  - (* TSec *)
    intros Γ l e He IHe Γ0 lx τx Heq Hdom Hvv.
    apply (TSec Σ (tctx_subst xx vv Γ0) l (subst xx vv e)).
    apply (IHe Γ0 lx τx Heq Hdom Hvv).
  - (* TMux *)
    intros Γ e0 e1 e2 τ He0 IHe0 He1 IHe1 He2 IHe2 Hk IHk Γ0 lx τx Heq Hdom Hvv.
    apply (TMux Σ (tctx_subst xx vv Γ0) (subst xx vv e0) (subst xx vv e1) (subst xx vv e2) (subst xx vv τ)).
    + apply (IHe0 Γ0 lx τx Heq Hdom Hvv).
    + apply (IHe1 Γ0 lx τx Heq Hdom Hvv).
    + apply (IHe2 Γ0 lx τx Heq Hdom Hvv).
    + apply (IHk Γ0 lx τx Heq Hdom Hvv).
  - (* TOInj *)
    intros Γ b e τ1 τ2 He IHe Hk IHk Γ0 lx τx Heq Hdom Hvv.
    apply (TOInj Σ (tctx_subst xx vv Γ0) b (subst xx vv e) (subst xx vv τ1) (subst xx vv τ2)).
    + rewrite <- (subst_ite xx vv b τ1 τ2).
      apply (IHe Γ0 lx τx Heq Hdom Hvv).
    + apply (IHk Γ0 lx τx Heq Hdom Hvv).
  - (* TOIf *)
    intros Γ l1 l2 e0 e1 e2 τ κ He0 IHe0 He1 IHe1 He2 IHe2 Hk IHk Γ0 lx τx Heq Hdom Hvv.
    apply (TOIf Σ (tctx_subst xx vv Γ0) l1 l2 (subst xx vv e0) (subst xx vv e1) (subst xx vv e2) (subst xx vv τ) κ).
    + apply (IHe0 Γ0 lx τx Heq Hdom Hvv).
    + apply (IHe1 Γ0 lx τx Heq Hdom Hvv).
    + apply (IHe2 Γ0 lx τx Heq Hdom Hvv).
    + apply (IHk Γ0 lx τx Heq Hdom Hvv).
  - (* TOCase *)
    intros Γ l1 l2 e0 e1 e2 τ1 τ2 τ κ L1 L2 H0 IH0 Hb1 IHb1 Hb2 IHb2 Hk IHk Γ0 lx τx Heq Hdom Hvv.
    apply (TOCase Σ (tctx_subst xx vv Γ0) l1 l2 (subst xx vv e0) (subst xx vv e1) (subst xx vv e2) (subst xx vv τ1) (subst xx vv τ2) (subst xx vv τ) κ (L1 ∪ dom Γ0 ∪ {[xx]}) (L2 ∪ dom Γ0 ∪ {[xx]})).
    + apply (IH0 Γ0 lx τx Heq Hdom Hvv).
    + tsub_bind_fvar_nd Σ xx vv Hn Γ Γ0 lx τx Hvv Hdom Heq (⊥ : bool) τ1 e1 IHb1 L1.
    + tsub_bind_fvar_nd Σ xx vv Hn Γ Γ0 lx τx Hvv Hdom Heq (⊥ : bool) τ2 e2 IHb2 L2.
    + apply (IHk Γ0 lx τx Heq Hdom Hvv).
  - (* TTape *)
    intros Γ l e τ He IHe Hk IHk Γ0 lx τx Heq Hdom Hvv.
    apply (TTape Σ (tctx_subst xx vv Γ0) l (subst xx vv e) (subst xx vv τ)).
    + apply (IHe Γ0 lx τx Heq Hdom Hvv).
    + apply (IHk Γ0 lx τx Heq Hdom Hvv).
  - (* TBoxedLit *)
    intros Γ b Γ0 lx τx Heq Hdom Hvv.
    apply (TBoxedLit Σ (tctx_subst xx vv Γ0) b).
  - (* TBoxedInj *)
    intros Γ b v ω Hov Γ0 lx τx Heq Hdom Hvv.
    assert (Hf : fv ω = ∅) by (apply otval_fv_empty; eapply ovalty_otval; exact Hov).
    assert (Hnot : xx ∉ fv ω) by (rewrite Hf; set_solver).
    rewrite (subst_not_fv xx vv ω Hnot).
    apply (TBoxedInj Σ (tctx_subst xx vv Γ0) b v ω).
    exact Hov.
  - (* TConv *)
    intros Γ l l' e τ τ' κ He IHe Hpe Hk IHk Hle Γ0 lx τx Heq Hdom Hvv.
    apply (TConv Σ (tctx_subst xx vv Γ0) l l' (subst xx vv e) (subst xx vv τ) (subst xx vv τ') κ).
    + apply (IHe Γ0 lx τx Heq Hdom Hvv).
    + apply (pared_equiv_subst Σ xx vv Hv HΣ τ' τ Hpe).
    + apply (IHk Γ0 lx τx Heq Hdom Hvv).
    + exact Hle.
  - (* KADT *)
    intros Γ X τ HX Γ0 lx τx Heq Hdom Hvv.
    apply (KADT Σ (tctx_subst xx vv Γ0) X τ HX).
  - (* KUnit *)
    intros Γ Γ0 lx τx Heq Hdom Hvv.
    apply (KUnit Σ (tctx_subst xx vv Γ0)).
  - (* KBool *)
    intros Γ l Γ0 lx τx Heq Hdom Hvv.
    apply (KBool Σ (tctx_subst xx vv Γ0) l).
  - (* KPi *)
    intros Γ l τ1 τ2 κ1 κ2 L Hbody IHbody Hk IHk Γ0 lx τx Heq Hdom Hvv.
    apply (KPi Σ (tctx_subst xx vv Γ0) l (subst xx vv τ1) (subst xx vv τ2) κ1 κ2 (L ∪ dom Γ0 ∪ {[xx]})).
    + tsub_bind_kind Σ xx vv Hn Γ Γ0 lx τx Hvv Hdom Heq l τ1 τ2 IHbody L.
    + apply (IHk Γ0 lx τx Heq Hdom Hvv).
  - (* KProd *)
    intros Γ τ1 τ2 κ H1 IH1 H2 IH2 Γ0 lx τx Heq Hdom Hvv.
    apply (KProd Σ (tctx_subst xx vv Γ0) (subst xx vv τ1) (subst xx vv τ2) κ).
    + apply (IH1 Γ0 lx τx Heq Hdom Hvv).
    + apply (IH2 Γ0 lx τx Heq Hdom Hvv).
  - (* KSum *)
    intros Γ τ1 τ2 κ H1 IH1 H2 IH2 Γ0 lx τx Heq Hdom Hvv.
    apply (KSum Σ (tctx_subst xx vv Γ0) (subst xx vv τ1) (subst xx vv τ2) κ).
    + apply (IH1 Γ0 lx τx Heq Hdom Hvv).
    + apply (IH2 Γ0 lx τx Heq Hdom Hvv).
  - (* KOSum *)
    intros Γ τ1 τ2 H1 IH1 H2 IH2 Γ0 lx τx Heq Hdom Hvv.
    apply (KOSum Σ (tctx_subst xx vv Γ0) (subst xx vv τ1) (subst xx vv τ2)).
    + apply (IH1 Γ0 lx τx Heq Hdom Hvv).
    + apply (IH2 Γ0 lx τx Heq Hdom Hvv).
  - (* KOADT *)
    intros Γ e' e τ X HX He IHe Γ0 lx τx Heq Hdom Hvv.
    assert (Hnot : xx ∉ fv τ) by
      (intros Hx; apply HΣ; apply (gctx_fv_spec Σ X (DOADT τ e') xx HX); simpl; set_solver).
    apply (KOADT Σ (tctx_subst xx vv Γ0) e' (subst xx vv e) τ X HX).
    rewrite <- (subst_not_fv xx vv τ Hnot).
    apply (IHe Γ0 lx τx Heq Hdom Hvv).
  - (* KIf *)
    intros Γ e0 τ1 τ2 He0 IHe0 H1 IH1 H2 IH2 Γ0 lx τx Heq Hdom Hvv.
    apply (KIf Σ (tctx_subst xx vv Γ0) (subst xx vv e0) (subst xx vv τ1) (subst xx vv τ2)).
    + apply (IHe0 Γ0 lx τx Heq Hdom Hvv).
    + apply (IH1 Γ0 lx τx Heq Hdom Hvv).
    + apply (IH2 Γ0 lx τx Heq Hdom Hvv).
  - (* KCase *)
    intros Γ e0 τ1 τ2 τ1' τ2' L1 L2 H0 IH0 Hb1 IHb1 Hb2 IHb2 Γ0 lx τx Heq Hdom Hvv.
    apply (KCase Σ (tctx_subst xx vv Γ0) (subst xx vv e0) (subst xx vv τ1) (subst xx vv τ2) (subst xx vv τ1') (subst xx vv τ2') (L1 ∪ dom Γ0 ∪ {[xx]}) (L2 ∪ dom Γ0 ∪ {[xx]})).
    + apply (IH0 Γ0 lx τx Heq Hdom Hvv).
    + tsub_bind_kind Σ xx vv Hn Γ Γ0 lx τx Hvv Hdom Heq (⊥ : bool) τ1' τ1 IHb1 L1.
    + tsub_bind_kind Σ xx vv Hn Γ Γ0 lx τx Hvv Hdom Heq (⊥ : bool) τ2' τ2 IHb2 L2.
  - (* KLet *)
    intros Γ e τ τ' L He IHe Hb IHb Γ0 lx τx Heq Hdom Hvv.
    apply (KLet Σ (tctx_subst xx vv Γ0) (subst xx vv e) (subst xx vv τ) (subst xx vv τ') (L ∪ dom Γ0 ∪ {[xx]})).
    + apply (IHe Γ0 lx τx Heq Hdom Hvv).
    + tsub_bind_kind Σ xx vv Hn Γ Γ0 lx τx Hvv Hdom Heq (⊥ : bool) τ' τ IHb L.
  - (* KSub *)
    intros Γ τ κ κ' He IHe Hle Γ0 lx τx Heq Hdom Hvv.
    apply (KSub Σ (tctx_subst xx vv Γ0) (subst xx vv τ) κ κ').
    + apply (IHe Γ0 lx τx Heq Hdom Hvv).
    + exact Hle.
Qed.

(* ================================================================ *)
(* Indistinguishability is an equivalence and a congruence            *)
(* ================================================================ *)
Lemma indistinguishable_refl e : e ≈ e.
Proof.
  induction e; try constructor; auto.
Qed.

Lemma indistinguishable_sym e e' : e ≈ e' -> e' ≈ e.
Proof.
  intros H. induction H; try constructor; auto.
Qed.

Lemma indistinguishable_trans e e' e'' : e ≈ e' -> e' ≈ e'' -> e ≈ e''.
Proof.
  intros H. revert e''. induction H; intros e'' H'; try (inversion H'; subst; try constructor; eauto).
Qed.

Lemma open_indistinguishable :
  forall e e', e ≈ e' ->
  forall k v v', v ≈ v' -> open_ k v e ≈ open_ k v' e'.
Proof.
  intros e e' H. induction H; intros kk v0 v0' Hvv; simpl.
  - (* IBVar *) case_decide; [exact Hvv|constructor].
  - (* IFVar *) constructor.
  - (* IGVar *) constructor.
  - (* IPi *) constructor; [apply IHindistinguishable1|apply IHindistinguishable2]; auto.
  - (* IAbs *) constructor; [apply IHindistinguishable1|apply IHindistinguishable2]; auto.
  - (* IApp *) constructor; [apply IHindistinguishable1|apply IHindistinguishable2]; auto.
  - (* ILet *) constructor; [apply IHindistinguishable1|apply IHindistinguishable2]; auto.
  - (* IUnitT *) constructor.
  - (* IUnitV *) constructor.
  - (* IBool *) constructor.
  - (* ILit *) constructor.
  - (* ISec *) constructor. apply IHindistinguishable. auto.
  - (* IIte *) constructor; [apply IHindistinguishable1|apply IHindistinguishable2|apply IHindistinguishable3]; auto.
  - (* IProd *) constructor; [apply IHindistinguishable1|apply IHindistinguishable2]; auto.
  - (* IPair *) constructor; [apply IHindistinguishable1|apply IHindistinguishable2]; auto.
  - (* IProj *) constructor. apply IHindistinguishable. auto.
  - (* ISum *) constructor; [apply IHindistinguishable1|apply IHindistinguishable2]; auto.
  - (* IInj *) constructor; [apply IHindistinguishable1|apply IHindistinguishable2]; auto.
  - (* ICase *) constructor; [apply IHindistinguishable1|apply IHindistinguishable2|apply IHindistinguishable3]; auto.
  - (* IFold *) constructor. apply IHindistinguishable. auto.
  - (* IUnfold *) constructor. apply IHindistinguishable. auto.
  - (* ITape *) constructor. apply IHindistinguishable. auto.
  - (* IMux *) constructor; [apply IHindistinguishable1|apply IHindistinguishable2|apply IHindistinguishable3]; auto.
  - (* IBoxedLit *) constructor.
  - (* IBoxedInj *) constructor.
Qed.

Lemma subst_indistinguishable x s s' e e' :
  e ≈ e' -> s ≈ s' -> subst x s e ≈ subst x s' e'.
Proof.
  intros H. revert s'. induction H; intros s0 Hss; simpl.
  - (* IBVar *) constructor.
  - (* IFVar *) case_decide; [exact Hss|constructor].
  - (* IGVar *) constructor.
  - (* IPi *) constructor; [apply IHindistinguishable1|apply IHindistinguishable2]; auto.
  - (* IAbs *) constructor; [apply IHindistinguishable1|apply IHindistinguishable2]; auto.
  - (* IApp *) constructor; [apply IHindistinguishable1|apply IHindistinguishable2]; auto.
  - (* ILet *) constructor; [apply IHindistinguishable1|apply IHindistinguishable2]; auto.
  - (* IUnitT *) constructor.
  - (* IUnitV *) constructor.
  - (* IBool *) constructor.
  - (* ILit *) constructor.
  - (* ISec *) constructor. apply IHindistinguishable. auto.
  - (* IIte *) constructor; [apply IHindistinguishable1|apply IHindistinguishable2|apply IHindistinguishable3]; auto.
  - (* IProd *) constructor; [apply IHindistinguishable1|apply IHindistinguishable2]; auto.
  - (* IPair *) constructor; [apply IHindistinguishable1|apply IHindistinguishable2]; auto.
  - (* IProj *) constructor. apply IHindistinguishable. auto.
  - (* ISum *) constructor; [apply IHindistinguishable1|apply IHindistinguishable2]; auto.
  - (* IInj *) constructor; [apply IHindistinguishable1|apply IHindistinguishable2]; auto.
  - (* ICase *) constructor; [apply IHindistinguishable1|apply IHindistinguishable2|apply IHindistinguishable3]; auto.
  - (* IFold *) constructor. apply IHindistinguishable. auto.
  - (* IUnfold *) constructor. apply IHindistinguishable. auto.
  - (* ITape *) constructor. apply IHindistinguishable. auto.
  - (* IMux *) constructor; [apply IHindistinguishable1|apply IHindistinguishable2|apply IHindistinguishable3]; auto.
  - (* IBoxedLit *) constructor.
  - (* IBoxedInj *) constructor.
Qed.

Lemma oval_indistinguishable v w ω : ovalty v ω -> ovalty w ω -> v ≈ w.
Proof.
  intros H. revert w. induction H; intros w0 Hw.
  - inversion Hw. constructor.
  - inversion Hw. constructor.
  - inversion Hw; subst. constructor.
    + apply IHovalty1. assumption.
    + apply IHovalty2. assumption.
  - inversion Hw; subst. constructor.
Qed.

(* ================================================================ *)
(* Typed terms and kinded types are locally closed                   *)
(* ================================================================ *)
Lemma typing_kinding_lc Σ :
  (forall Γ e l τ, Σ; Γ ⊢ e :{l} τ -> lc e) /\
  (forall Γ τ κ, Σ; Γ ⊢ τ :: κ -> lc τ).
Proof.
  apply typing_kinding_mutind.
  - (* TFVar *) intros. constructor.
  - (* TUnit *) intros. constructor.
  - (* TLit *) intros. constructor.
  - (* TFun *) intros. constructor.
  - (* TAbs *) intros Γ l1 l2 e τ1 τ2 κ L Hbody IHbody Hk IHk.
    apply LCAbs with (L := L). exact IHbody. exact IHk.
  - (* TLet *) intros Γ l1 l2 l e1 e2 τ1 τ2 L He1 IHe1 Hbody IHbody Hl.
    apply LCLet with (L := L). exact IHbody. exact IHe1.
  - (* TApp *) intros. constructor; assumption.
  - (* TPair *) intros. constructor; assumption.
  - (* TProj *) intros. constructor. assumption.
  - (* TInj *) intros Γ l b e τ1 τ2 κ He IHe Hk IHk.
    apply LCInj. exact IHk. exact IHe.
  - (* TIf *) intros. constructor; assumption.
  - (* TIfNoDep *) intros. constructor; assumption.
  - (* TCase *) intros Γ l1 l2 l e0 e1 e2 τ1 τ2 τ κ L1 L2 H0 IH0 Hb1 IHb1 Hb2 IHb2 Hk IHk Hl.
    apply LCCase with (L1 := L1) (L2 := L2); assumption.
  - (* TCaseNoDep *) intros Γ l0 l1 l2 l e0 e1 e2 τ1 τ2 τ κ L1 L2 H0 IH0 Hb1 IHb1 Hb2 IHb2 Hk IHk Hl.
    apply LCCase with (L1 := L1) (L2 := L2); assumption.
  - (* TFold *) intros. constructor. assumption.
  - (* TUnfold *) intros. constructor. assumption.
  - (* TSec *) intros. constructor. assumption.
  - (* TMux *) intros. constructor; assumption.
  - (* TOInj *) intros Γ b e τ1 τ2 He IHe Hk IHk.
    apply LCInj. exact IHk. exact IHe.
  - (* TOIf *) intros. constructor; assumption.
  - (* TOCase *) intros Γ l1 l2 e0 e1 e2 τ1 τ2 τ κ L1 L2 H0 IH0 Hb1 IHb1 Hb2 IHb2 Hk IHk.
    apply LCCase with (L1 := L1) (L2 := L2); assumption.
  - (* TTape *) intros. constructor. assumption.
  - (* TBoxedLit *) intros. constructor.
  - (* TBoxedInj *) intros Γ b v ω Hov.
    apply LCBoxedInj with (ω := ω).
    + exact (ovalty_otval _ _ Hov).
    + exact (ovalty_inj_oval b ω v Hov).
  - (* TConv *) intros. assumption.
  - (* KADT *) intros. constructor.
  - (* KUnit *) intros. constructor.
  - (* KBool *) intros. constructor.
  - (* KPi *) intros Γ l τ1 τ2 κ1 κ2 L Hbody IHbody Hk IHk.
    apply LCPi with (L := L). exact IHbody. exact IHk.
  - (* KProd *) intros. constructor; assumption.
  - (* KSum *) intros. constructor; assumption.
  - (* KOSum *) intros. constructor; assumption.
  - (* KOADT *) intros. apply LCApp. constructor. assumption.
  - (* KIf *) intros. constructor; assumption.
  - (* KCase *) intros Γ e0 τ1 τ2 τ1' τ2' L1 L2 H0 IH0 Hb1 IHb1 Hb2 IHb2.
    apply LCCase with (L1 := L1) (L2 := L2); assumption.
  - (* KLet *) intros Γ e τ τ' L He IHe Hb IHb.
    apply LCLet with (L := L); assumption.
  - (* KSub *) intros. assumption.
Qed.

Lemma typing_lc Σ Γ e l τ : Σ; Γ ⊢ e :{l} τ -> lc e.
Proof. exact (proj1 (typing_kinding_lc Σ) Γ e l τ). Qed.

Lemma kinding_lc Σ Γ τ κ : Σ; Γ ⊢ τ :: κ -> lc τ.
Proof. exact (proj2 (typing_kinding_lc Σ) Γ τ κ). Qed.

(* ================================================================ *)
(* Evaluation contexts preserve parallel reduction                    *)
(* ================================================================ *)
Lemma pared_ectx Σ ℇ : ectx ℇ ->
  forall e e', lc (ℇ e) -> pared Σ e e' -> pared Σ (ℇ e) (ℇ e').
Proof.
  intros He. destruct He; intros ee ee' Hlc Hstep; simpl in *.
  - inversion Hlc; subst. apply RCgrProd.
    + exact Hstep.
    + apply RRefl. assumption.
  - inversion Hlc; subst. apply RCgrProd.
    + apply RRefl. assumption.
    + exact Hstep.
  - inversion Hlc; subst. apply RCgrSum.
    + exact Hstep.
    + apply RRefl. assumption.
  - inversion Hlc; subst. apply RCgrSum.
    + apply RRefl. assumption.
    + exact Hstep.
  - inversion Hlc; subst. apply RCgrApp.
    + exact Hstep.
    + apply RRefl. assumption.
  - inversion Hlc; subst. apply RCgrApp.
    + apply RRefl. assumption.
    + exact Hstep.
  - inversion Hlc; subst. eapply RCgrLet.
    + exact Hstep.
    + intros y Hy. apply RRefl. eauto.
  - inversion Hlc; subst. apply RCgrSec. exact Hstep.
  - inversion Hlc; subst. apply RCgrIf.
    + exact Hstep.
    + apply RRefl. assumption.
    + apply RRefl. assumption.
  - inversion Hlc; subst. apply RCgrIf.
    + exact Hstep.
    + apply RRefl. assumption.
    + apply RRefl. assumption.
  - inversion Hlc; subst. apply RCgrIf.
    + apply RRefl. assumption.
    + exact Hstep.
    + apply RRefl. assumption.
  - inversion Hlc; subst. apply RCgrIf.
    + apply RRefl. assumption.
    + apply RRefl. assumption.
    + exact Hstep.
  - inversion Hlc; subst. apply RCgrPair.
    + exact Hstep.
    + apply RRefl. assumption.
  - inversion Hlc; subst. apply RCgrPair.
    + apply RRefl. assumption.
    + exact Hstep.
  - inversion Hlc; subst. apply RCgrProj. exact Hstep.
  - inversion Hlc; subst. apply RCgrInj.
    + exact Hstep.
    + apply RRefl. assumption.
  - inversion Hlc; subst. apply RCgrInj.
    + apply RRefl. assumption.
    + exact Hstep.
  - inversion Hlc; subst. apply RCgrInj.
    + exact Hstep.
    + apply RRefl. assumption.
  - inversion Hlc; subst. eapply RCgrCase.
    + exact Hstep.
    + intros y Hy. apply RRefl. eauto.
    + intros y Hy. apply RRefl. eauto.
  - inversion Hlc; subst. eapply RCgrCase.
    + exact Hstep.
    + intros y Hy. apply RRefl. eauto.
    + intros y Hy. apply RRefl. eauto.
  - inversion Hlc; subst. apply RCgrFold. exact Hstep.
  - inversion Hlc; subst. apply RCgrUnfold. exact Hstep.
  - inversion Hlc; subst. apply RCgrTape. exact Hstep.
  - inversion Hlc; subst. apply RCgrMux.
    + exact Hstep.
    + apply RRefl. assumption.
    + apply RRefl. assumption.
  - inversion Hlc; subst. apply RCgrMux.
    + apply RRefl. assumption.
    + exact Hstep.
    + apply RRefl. assumption.
  - inversion Hlc; subst. apply RCgrMux.
    + apply RRefl. assumption.
    + apply RRefl. assumption.
    + exact Hstep.
Qed.

Lemma lc_ectx ℇ : ectx ℇ -> forall e, lc (ℇ e) -> lc e.
Proof.
  intros He. destruct He; intros ee Hlc; simpl in *; inversion Hlc; subst; assumption.
Qed.


Lemma lc_app_inv e1 e2 : lc (EApp e1 e2) -> lc e1 /\ lc e2.
Proof. intros H. inversion H. auto. Qed.
Lemma lc_pair_inv e1 e2 : lc (EPair e1 e2) -> lc e1 /\ lc e2.
Proof. intros H. inversion H. auto. Qed.
Lemma lc_proj_inv b e : lc (EProj b e) -> lc e.
Proof. intros H. inversion H. assumption. Qed.
Lemma lc_inj_inv l b τ e : lc (EInj l b τ e) -> lc τ /\ lc e.
Proof. intros H. inversion H. auto. Qed.
Lemma lc_ite_inv l e0 e1 e2 : lc (EIte l e0 e1 e2) -> lc e0 /\ lc e1 /\ lc e2.
Proof. intros H. inversion H. auto. Qed.
Lemma lc_mux_inv e0 e1 e2 : lc (EMux e0 e1 e2) -> lc e0 /\ lc e1 /\ lc e2.
Proof. intros H. inversion H. auto. Qed.
Lemma lc_tape_inv e : lc (ETape e) -> lc e.
Proof. intros H. inversion H. assumption. Qed.
Lemma lc_sec_inv e : lc (ESec e) -> lc e.
Proof. intros H. inversion H. assumption. Qed.
Lemma lc_fold_inv X e : lc (EFold X e) -> lc e.
Proof. intros H. inversion H. assumption. Qed.
Lemma lc_unfold_inv X e : lc (EUnfold X e) -> lc e.
Proof. intros H. inversion H. assumption. Qed.
Lemma lc_abs_inv l τ e : lc (EAbs l τ e) -> lc τ /\ exists L, forall x, x ∉ L -> lc (open (EFVar x) e).
Proof. intros H. inversion H; subst. split; [assumption|eexists; eassumption]. Qed.
Lemma lc_let_inv e1 e2 : lc (ELet e1 e2) -> lc e1 /\ exists L, forall x, x ∉ L -> lc (open (EFVar x) e2).
Proof. intros H. inversion H; subst. split; [assumption|eexists; eassumption]. Qed.
Lemma lc_case_inv l e0 e1 e2 : lc (ECase l e0 e1 e2) ->
  lc e0 /\ (exists L1, forall x, x ∉ L1 -> lc (open (EFVar x) e1))
         /\ (exists L2, forall x, x ∉ L2 -> lc (open (EFVar x) e2)).
Proof. intros H. inversion H; subst. repeat split; try assumption; try (eexists; eassumption). Qed.

Lemma step_pared Σ : forall e e', lc e -> step Σ e e' -> pared Σ e e'.
Proof.
  intros e e' Hlc Hstep. induction Hstep.
  - (* SApp *) destruct (lc_app_inv _ _ Hlc) as [Hlcf Hlcv].
    destruct (lc_abs_inv _ _ _ Hlcf) as [Hltau [L Hbody]].
    apply (RApp Σ l τ v e v e L).
    + apply RRefl. exact Hlcv.
    + intros y Hy. apply RRefl. apply Hbody. exact Hy.
    + exact Hltau.
  - (* SLet *) destruct (lc_let_inv _ _ Hlc) as [Hlcv [L Hbody]].
    apply (RLet Σ v e v e L).
    + apply RRefl. exact Hlcv.
    + intros y Hy. apply RRefl. apply Hbody. exact Hy.
  - (* SIf *) destruct (lc_ite_inv _ _ _ _ Hlc) as [Hl0 [Hl1 Hl2]].
    apply (RIf Σ b e1 e2 e1 e2).
    + apply RRefl. exact Hl1.
    + apply RRefl. exact Hl2.
  - (* SCase *) destruct (lc_case_inv _ _ _ _ Hlc) as [Hl0 [[L1 Hb1] [L2 Hb2]]].
    destruct (lc_inj_inv _ _ _ _ Hl0) as [Hltau Hlcv].
    apply (RCase Σ b τ v e1 e2 v e1 e2 L1 L2).
    + apply RRefl. exact Hlcv.
    + intros y Hy. apply RRefl. apply Hb1. exact Hy.
    + intros y Hy. apply RRefl. apply Hb2. exact Hy.
    + exact Hltau.
  - (* SProj *) pose proof (lc_proj_inv _ _ Hlc) as Hlp.
    destruct (lc_pair_inv _ _ Hlp) as [Hl1 Hl2].
    apply (RProj Σ b v1 v2 v1 v2).
    + apply RRefl. exact Hl1.
    + apply RRefl. exact Hl2.
  - (* SUnfold *) pose proof (lc_unfold_inv _ _ Hlc) as Hlf.
    pose proof (lc_fold_inv _ _ Hlf) as Hlv.
    apply (RFold Σ X X' v v). apply RRefl. exact Hlv.
  - (* SFun *) apply (RFun Σ x T e H).
  - (* SOADT *) destruct (lc_app_inv _ _ Hlc) as [Hg Hlv].
    apply (ROADT Σ X τ' τ v v).
    + eassumption.
    + apply RRefl. exact Hlv.
  - (* SSec *) apply (RSec Σ b).
  - (* SOInj *) apply (ROInj Σ b ω v H H0).
  - (* SMux *) destruct (lc_mux_inv _ _ _ Hlc) as [Hl0 [Hl1 Hl2]].
    apply (RMux Σ b v1 v2 v1 v2).
    + apply RRefl. exact Hl1.
    + apply RRefl. exact Hl2.
  - (* SOCase *) destruct (lc_case_inv _ _ _ _ Hlc) as [Hl0 [[L1 Hb1] [L2 Hb2]]].
    apply (ROCase Σ b ω1 ω2 v v1 v2 e1 e2 e1 e2 L1 L2).
    + exact H.
    + exact H0.
    + exact H1.
    + intros y Hy. apply RRefl. apply Hb1. exact Hy.
    + intros y Hy. apply RRefl. apply Hb2. exact Hy.
  - (* STapeOIf *) pose proof (lc_tape_inv _ Hlc) as Hli.
    destruct (lc_ite_inv _ _ _ _ Hli) as [Hlb [Hl1 Hl2]].
    apply (RTapeOIf Σ b v1 v2 v1 v2).
    + apply RRefl. exact Hl1.
    + apply RRefl. exact Hl2.
  - (* STapePair *) pose proof (lc_tape_inv _ Hlc) as Hlp.
    destruct (lc_pair_inv _ _ Hlp) as [Hl1 Hl2].
    apply (RTapePair Σ v1 v2 v1 v2).
    + apply RRefl. exact Hl1.
    + apply RRefl. exact Hl2.
    + exact H.
    + exact H0.
  - (* STapeUnitV *) apply (RTapeUnitV Σ).
  - (* STapeBoxedLit *) apply (RTapeBoxedLit Σ b).
  - (* STapeBoxedInj *) apply (RTapeBoxedInj Σ b ω v H H0).
  - (* SOIf *) destruct H as [w2 Hw2 | | e3 e4 | b0 | e3 e4 | X]; simpl in *.
    + (* LCtxApp *) destruct (lc_app_inv _ _ Hlc) as [Hli Hlw].
      destruct (lc_ite_inv _ _ _ _ Hli) as [Hlb [Hl1 Hl2]].
      apply (ROIfApp Σ b v1 v2 w2 v1 v2 w2).
      * apply RRefl. exact Hl1.
      * apply RRefl. exact Hl2.
      * apply RRefl. exact Hlw.
    + (* LCtxSec *) pose proof (lc_sec_inv _ Hlc) as Hli.
      destruct (lc_ite_inv _ _ _ _ Hli) as [Hlb [Hl1 Hl2]].
      apply (ROIfSec Σ b v1 v2 v1 v2).
      * apply RRefl. exact Hl1.
      * apply RRefl. exact Hl2.
    + (* LCtxIf *) destruct (lc_ite_inv _ _ _ _ Hlc) as [Hli [Hl3 Hl4]].
      destruct (lc_ite_inv _ _ _ _ Hli) as [Hlb [Hl1 Hl2]].
      apply (ROIfIf Σ b v1 v2 e3 e4 v1 v2 e3 e4).
      * apply RRefl. exact Hl1.
      * apply RRefl. exact Hl2.
      * apply RRefl. exact Hl3.
      * apply RRefl. exact Hl4.
    + (* LCtxProj *) pose proof (lc_proj_inv _ _ Hlc) as Hli.
      destruct (lc_ite_inv _ _ _ _ Hli) as [Hlb [Hl1 Hl2]].
      apply (ROIfProj Σ b b0 v1 v2 v1 v2).
      * apply RRefl. exact Hl1.
      * apply RRefl. exact Hl2.
    + (* LCtxCase *) destruct (lc_case_inv _ _ _ _ Hlc) as [Hli [[L1 Hb1] [L2 Hb2]]].
      destruct (lc_ite_inv _ _ _ _ Hli) as [Hlb [Hl1 Hl2]].
      apply (ROIfCase Σ b v1 v2 e3 e4 v1 v2 e3 e4 L1 L2).
      * apply RRefl. exact Hl1.
      * apply RRefl. exact Hl2.
      * intros y Hy. apply RRefl. apply Hb1. exact Hy.
      * intros y Hy. apply RRefl. apply Hb2. exact Hy.
    + (* LCtxUnfold *) pose proof (lc_unfold_inv _ _ Hlc) as Hli.
      destruct (lc_ite_inv _ _ _ _ Hli) as [Hlb [Hl1 Hl2]].
      apply (ROIfUnfold Σ X b v1 v2 v1 v2).
      * apply RRefl. exact Hl1.
      * apply RRefl. exact Hl2.
  - (* SCtx *) apply (pared_ectx Σ ℇ H e e' Hlc).
    apply IHHstep. apply (lc_ectx ℇ H e Hlc).
Qed.

(* ================================================================ *)
(* Free variables of a typing context                                 *)
(* ================================================================ *)
Definition tctx_fv (Γ : tctx) : aset :=
  foldr (fun p acc => fv (snd (p.2)) ∪ acc) ∅ (map_to_list Γ).

Lemma elem_of_tctx_fv_aux (l : list (atom * lexpr)) x :
  (exists p, p ∈ l /\ x ∈ fv (snd (p.2))) ->
  x ∈ foldr (fun p acc => fv (snd (p.2)) ∪ acc) ∅ l.
Proof.
  induction l as [|p l IH]; simpl; intros [q [Hin Hx]].
  - inversion Hin.
  - apply elem_of_cons in Hin as [->|Hin].
    + by apply elem_of_union_l.
    + apply elem_of_union_r. by apply IH; exists q.
Qed.

Lemma tctx_fv_spec Γ y (T : lexpr) : Γ !! y = Some T -> fv (snd T) ⊆ tctx_fv Γ.
Proof.
  intros H x0 Hx. unfold tctx_fv.
  apply elem_of_tctx_fv_aux. exists (y,T). split; [|done].
  by apply elem_of_map_to_list.
Qed.

Lemma tctx_subst_id x s Γ : x ∉ tctx_fv Γ -> tctx_subst x s Γ = Γ.
Proof.
  intros H. apply map_eq. intros y.
  rewrite tctx_subst_lookup.
  destruct (Γ !! y) as [[l τ]|] eqn:E.
  - rewrite fmap_Some. exists (l,τ). split; [exact E|].
    simpl. f_equal. symmetry. apply subst_not_fv. intros Hx.
    apply H. exact ((tctx_fv_spec Γ y (l,τ) E) x Hx).
  - rewrite fmap_None. done.
Qed.

Lemma subst_open_same x v e : lc_n 0 v -> x ∉ fv e ->
  subst x v (open (EFVar x) e) = open v e.
Proof.
  intros Hv Hf.
  change (subst x v (open_ 0 (EFVar x) e) = open_ 0 v e).
  rewrite (subst_open_comm_lc e x v 0 (EFVar x) Hv).
  rewrite (subst_fvar_eq x v).
  by rewrite (subst_not_fv x v e Hf).
Qed.

(* ================================================================ *)
(* Oblivious type forms are kinded *@O                                *)
(* ================================================================ *)
Lemma otval_kinding Σ Γ w : otval w -> Σ; Γ ⊢ w :: *@O.
Proof.
  induction 1.
  - apply (KSub Σ Γ EUnitT KObliv KAny). apply KUnit. done.
  - apply (KBool Σ Γ true).
  - apply (KProd Σ Γ ω1 ω2 KObliv); assumption.
  - apply (KOSum Σ Γ ω1 ω2); assumption.
Qed.

Lemma ovalty_kinding Σ Γ v ω : ovalty v ω -> Σ; Γ ⊢ ω :: *@O.
Proof.
  induction 1.
  - apply (KSub Σ Γ EUnitT KObliv KAny). apply KUnit. done.
  - apply (KBool Σ Γ true).
  - apply (KProd Σ Γ ω1 ω2 KObliv).
    + apply otval_kinding. apply (ovalty_otval v1 ω1 H).
    + apply otval_kinding. apply (ovalty_otval v2 ω2 H0).
  - destruct b; apply (KOSum Σ Γ ω1 ω2).
    + apply otval_kinding. eapply ovalty_otval. exact H.
    + apply otval_kinding. exact H0.
    + apply otval_kinding. exact H0.
    + apply otval_kinding. eapply ovalty_otval. exact H.
Qed.

Lemma otval_ite_kinding Σ Γ b ω1 ω2 : otval ω1 -> otval ω2 ->
  kinding Σ Γ (if b then ω1 else ω2) KObliv.
Proof.
  intros H1 H2. destruct b; simpl.
  - apply otval_kinding; assumption.
  - apply otval_kinding; assumption.
Qed.

(* ================================================================ *)
(* Conversion has common reducts                                      *)
(* ================================================================ *)
Lemma pared_equiv_common Σ e e' : pared_equiv Σ e e' ->
  exists c, rtc (pared Σ) e c /\ rtc (pared Σ) e' c.
Proof.
  intros H. induction H.
  - exists e. split; apply rtc_refl.
  - destruct IHpared_equiv as [c [H1 H2]].
    exists c. split; [|exact H2].
    eapply rtc_trans; [|exact H1]. apply rtc_once. exact H.
  - destruct IHpared_equiv as [c [H1 H2]].
    exists c. split; [exact H1|].
    eapply rtc_trans; [|exact H2]. apply rtc_once. exact H.
Qed.

Inductive canonical : expr -> Prop :=
| CUnitT : canonical EUnitT
| CBool : canonical (EBool true)
| CProd (a b : expr) : canonical a -> canonical b -> canonical (EProd a b)
| CSum (a b : expr) : canonical a -> canonical b -> canonical (ESum true a b).

Lemma canonical_otval e : canonical e -> otval e.
Proof. induction 1; constructor; assumption. Qed.

Lemma canonical_pared Σ e : canonical e -> forall e', pared Σ e e' -> e' = e.
Proof.
  intros Hc. induction Hc; intros e' Hp; inversion Hp; subst.
  - reflexivity.
  - reflexivity.
  - f_equal; [apply IHHc1; assumption|apply IHHc2; assumption].
  - reflexivity.
  - f_equal; [apply IHHc1; assumption|apply IHHc2; assumption].
  - reflexivity.
Qed.

Lemma canonical_rtc Σ e e' : canonical e -> rtc (pared Σ) e e' -> e' = e.
Proof.
  intros Hc Hrtc.
  refine (rtc_ind_r (fun z => canonical e -> z = e) e _ _ e' Hrtc Hc).
  - intros _. reflexivity.
  - intros y z Hr Hyz IH Hce.
    rewrite (IH Hce) in Hyz.
    apply (canonical_pared Σ e Hce z Hyz).
Qed.

Lemma canonical_equiv Σ a b : canonical a -> canonical b -> pared_equiv Σ a b -> a = b.
Proof.
  intros Ha Hb H.
  destruct (pared_equiv_common Σ a b H) as [c [H1 H2]].
  transitivity c.
  - symmetry. apply (canonical_rtc Σ a c Ha H1).
  - apply (canonical_rtc Σ b c Hb H2).
Qed.

Lemma otval_canonical w : otval w -> canonical w.
Proof.
  induction 1.
  - apply CUnitT.
  - apply CBool.
  - apply CProd; assumption.
  - apply CSum; assumption.
Qed.

Lemma ovalty_canonical v ω : ovalty v ω -> canonical ω.
Proof.
  intros H. apply otval_canonical. eapply ovalty_otval. exact H.
Qed.

Lemma canonical_lc e : canonical e -> lc e.
Proof. induction 1; constructor; assumption. Qed.

Lemma canonical_kinding Σ Γ e : canonical e -> kinding Σ Γ e KObliv.
Proof.
  intros H. apply otval_kinding. apply canonical_otval. exact H.
Qed.

(* ================================================================ *)
(* Beta substitution (single-variable, closed value)                  *)
(* ================================================================ *)
Lemma typing_subst_beta Σ Γ x v l2 τ2 e l τ :
  x ∉ gctx_fv Σ -> lc v ->
  x ∉ dom Γ -> x ∉ tctx_fv Γ -> x ∉ fv τ2 -> x ∉ fv e -> x ∉ fv τ ->
  typing Σ Γ v l2 τ2 ->
  typing Σ (<[x:=(l2,τ2)]>Γ) (open (EFVar x) e) l (open (EFVar x) τ) ->
  typing Σ Γ (open v e) l (open v τ).
Proof.
  intros HΣ Hv Hdom Htfv Hτ2 He Hτ Htyv Hbody.
  assert (Hn : lc_n 0 v) by (apply lc_lc_n0; auto).
  assert (Hvv : typing Σ (tctx_subst x v Γ) v l2 (subst x v τ2)).
  { rewrite (tctx_subst_id x v Γ Htfv), (subst_not_fv x v τ2 Hτ2). exact Htyv. }
  pose proof (proj1 (typing_kinding_subst Σ x v Hv HΣ)
    (<[x:=(l2,τ2)]>Γ) (open (EFVar x) e) l (open (EFVar x) τ)
    Hbody Γ l2 τ2 eq_refl Hdom Hvv) as Hres.
  rewrite (tctx_subst_id x v Γ Htfv) in Hres.
  rewrite (subst_open_same x v e Hn He) in Hres.
  rewrite (subst_open_same x v τ Hn Hτ) in Hres.
  exact Hres.
Qed.

Lemma kinding_subst_beta Σ Γ x v l2 τ2 T κ :
  x ∉ gctx_fv Σ -> lc v ->
  x ∉ dom Γ -> x ∉ tctx_fv Γ -> x ∉ fv τ2 -> x ∉ fv T ->
  typing Σ Γ v l2 τ2 ->
  kinding Σ (<[x:=(l2,τ2)]>Γ) (open (EFVar x) T) κ ->
  kinding Σ Γ (open v T) κ.
Proof.
  intros HΣ Hv Hdom Htfv Hτ2 HT Htyv Hbody.
  assert (Hn : lc_n 0 v) by (apply lc_lc_n0; auto).
  assert (Hvv : typing Σ (tctx_subst x v Γ) v l2 (subst x v τ2)).
  { rewrite (tctx_subst_id x v Γ Htfv), (subst_not_fv x v τ2 Hτ2). exact Htyv. }
  pose proof (proj2 (typing_kinding_subst Σ x v Hv HΣ)
    (<[x:=(l2,τ2)]>Γ) (open (EFVar x) T) κ
    Hbody Γ l2 τ2 eq_refl Hdom Hvv) as Hres.
  rewrite (tctx_subst_id x v Γ Htfv) in Hres.
  rewrite (subst_open_same x v T Hn HT) in Hres.
  exact Hres.
Qed.

(* ================================================================ *)
(* Inversion for oblivious value types                                *)
(* ================================================================ *)
Lemma otval_prod_inv w1 w2 : otval (EProd w1 w2) -> otval w1 /\ otval w2.
Proof. intros H. inversion H. auto. Qed.

Lemma otval_osum_inv w1 w2 : otval (ESum true w1 w2) -> otval w1 /\ otval w2.
Proof. intros H. inversion H. auto. Qed.

Lemma ovalty_osum_inv b v ω1 ω2 :
  ovalty (EBoxedInj b (ESum true ω1 ω2) v) (ESum true ω1 ω2) ->
  ovalty v (if b then ω1 else ω2) /\ otval (if b then ω2 else ω1).
Proof. intros H. inversion H; subst. auto. Qed.

Lemma otval_indistinguishable_eq a b : otval a -> otval b -> a ≈ b -> a = b.
Proof.
  intros Ha Hb Hab. revert Ha Hb.
  induction Hab; intros Ha Hb; try (inversion Ha; subst).
  - reflexivity.
  - reflexivity.
  - inversion Hb; subst. f_equal.
    + apply IHHab1; assumption.
    + apply IHHab2; assumption.
  - inversion Hb; subst. f_equal.
    + apply IHHab1; assumption.
    + apply IHHab2; assumption.
Qed.

Lemma ectx_indistinguishable ℇ : ectx ℇ ->
  forall e e', e ≈ e' -> ℇ e ≈ ℇ e'.
Proof.
  intros He. destruct He; intros ee ee' Heq; simpl.
  - apply IProd; [exact Heq|apply indistinguishable_refl].
  - apply IProd; [apply indistinguishable_refl|exact Heq].
  - apply ISum; [exact Heq|apply indistinguishable_refl].
  - apply ISum; [apply indistinguishable_refl|exact Heq].
  - apply IApp; [exact Heq|apply indistinguishable_refl].
  - apply IApp; [apply indistinguishable_refl|exact Heq].
  - apply ILet; [exact Heq|apply indistinguishable_refl].
  - apply ISec. exact Heq.
  - apply IIte; [exact Heq|apply indistinguishable_refl|apply indistinguishable_refl].
  - apply IIte; [exact Heq|apply indistinguishable_refl|apply indistinguishable_refl].
  - apply IIte; [apply indistinguishable_refl|exact Heq|apply indistinguishable_refl].
  - apply IIte; [apply indistinguishable_refl|apply indistinguishable_refl|exact Heq].
  - apply IPair; [exact Heq|apply indistinguishable_refl].
  - apply IPair; [apply indistinguishable_refl|exact Heq].
  - apply IProj. exact Heq.
  - apply IInj; [apply indistinguishable_refl|exact Heq].
  - apply IInj; [exact Heq|apply indistinguishable_refl].
  - apply IInj; [apply indistinguishable_refl|exact Heq].
  - apply ICase; [exact Heq|apply indistinguishable_refl|apply indistinguishable_refl].
  - apply ICase; [exact Heq|apply indistinguishable_refl|apply indistinguishable_refl].
  - apply IFold. exact Heq.
  - apply IUnfold. exact Heq.
  - apply ITape. exact Heq.
  - apply IMux; [exact Heq|apply indistinguishable_refl|apply indistinguishable_refl].
  - apply IMux; [apply indistinguishable_refl|exact Heq|apply indistinguishable_refl].
  - apply IMux; [apply indistinguishable_refl|apply indistinguishable_refl|exact Heq].
Qed.

Lemma open_indistinguishable_arg v v' e : v ≈ v' -> open v e ≈ open v' e.
Proof.
  intros H. apply (open_indistinguishable e e (indistinguishable_refl e) 0 v v' H).
Qed.

Lemma subst_indistinguishable_arg x s s' e : s ≈ s' -> subst x s e ≈ subst x s' e.
Proof.
  intros H. apply (subst_indistinguishable x s s' e e (indistinguishable_refl e) H).
Qed.

(* ================================================================ *)
(* Oblivious values and types are locally closed                      *)
(* ================================================================ *)
Lemma otval_lc w : otval w -> lc w.
Proof.
  induction 1.
  - constructor.
  - constructor.
  - constructor; assumption.
  - constructor; assumption.
Qed.

Lemma oval_lc v : oval v -> lc v.
Proof.
  induction 1.
  - constructor.
  - constructor.
  - constructor; assumption.
  - constructor; assumption.
Qed.

Lemma woval_lc v : woval v -> lc v.
Proof.
  induction 1.
  - constructor.
  - constructor.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; [constructor|assumption|assumption].
Qed.

(* Sealed local closure: boxed values are kept closed, so opening is safe. *)
Fixpoint lc_s (n : nat) (e : expr) : Prop :=
  match e with
  | EBVar k => k < n
  | EFVar _ | EGVar _ | EUnitT | EUnitV | EBool _ | ELit _ | EBoxedLit _ => True
  | EProd a b | ESum _ a b | EApp a b | EPair a b => lc_s n a /\ lc_s n b
  | EPi _ a b | EAbs _ a b | ELet a b => lc_s n a /\ lc_s (S n) b
  | EIte _ e0 e1 e2 | EMux e0 e1 e2 => lc_s n e0 /\ lc_s n e1 /\ lc_s n e2
  | ECase _ e0 e1 e2 => lc_s n e0 /\ lc_s (S n) e1 /\ lc_s (S n) e2
  | EProj _ e | EFold _ e | EUnfold _ e | ESec e | ETape e => lc_s n e
  | EInj _ _ τ e => lc_s n τ /\ lc_s n e
  | EBoxedInj b τ v => lc (EBoxedInj b τ v)
  end.

Lemma lc_s_mono (e : expr) : forall n m, lc_s n e -> n <= m -> lc_s m e.
Proof.
  induction e; intros n m H Hle; simpl in *; try done;
    try (destruct H as [? [? ?]]); try (destruct H as [? ?]);
    try (repeat split; eauto using le_n_S); lia.
Qed.

Lemma lc_s_lc_n (e : expr) : forall n, lc_s n e -> lc_n n e.
Proof.
  induction e; intros n H; simpl in *; try done;
    try (destruct H as [? [? ?]]); try (destruct H as [? ?]);
    try (repeat split; eauto using le_n_S).
  all: try (apply (lc_n_mono _ 0 n); [apply lc_lc_n0; assumption|lia]).
  all: try lia.
  - inversion H; subst. apply (lc_n_mono e1 0 n).
    + apply lc_lc_n0. apply otval_lc. assumption.
    + lia.
  - inversion H; subst. apply (lc_n_mono e2 0 n).
    + apply lc_lc_n0. apply oval_lc. assumption.
    + lia.
Qed.

Lemma lc_s_open_fwd (e : expr) :
  forall n s, lc_s (S n) e -> lc_s 0 s -> lc_s n (open_ n s e).
Proof.
  induction e; intros n s He Hs; simpl in He; simpl.
  - destruct (decide (n = k)) as [E|E].
    + simpl. apply (lc_s_mono s 0 n Hs); lia.
    + simpl. lia.
  - done. - done. - done. - done.
  - (* EProd *) destruct He as [Ha Hb]. split.
    + apply IHe1; assumption. + apply IHe2; assumption.
  - (* ESum *) destruct He as [Ha Hb]. split.
    + apply IHe1; assumption. + apply IHe2; assumption.
  - (* EPi *) destruct He as [Ha Hb]. split.
    + apply IHe1; assumption. + apply IHe2; assumption.
  - (* EUnitV *) done.
  - (* ELit *) done.
  - (* EAbs *) destruct He as [Ha Hb]. split.
    + apply IHe1; assumption. + apply IHe2; assumption.
  - (* EApp *) destruct He as [Ha Hb]. split.
    + apply IHe1; assumption. + apply IHe2; assumption.
  - (* ELet *) destruct He as [Ha Hb]. split.
    + apply IHe1; assumption. + apply IHe2; assumption.
  - (* EIte *) destruct He as [Ha [Hb Hc]]. repeat split.
    + apply IHe1; assumption. + apply IHe2; assumption. + apply IHe3; assumption.
  - (* EPair *) destruct He as [Ha Hb]. split.
    + apply IHe1; assumption. + apply IHe2; assumption.
  - (* EProj *) apply IHe; assumption.
  - (* EInj *) destruct He as [Ha Hb]. split.
    + apply IHe1; assumption. + apply IHe2; assumption.
  - (* ECase *) destruct He as [Ha [Hb Hc]]. repeat split.
    + apply IHe1; assumption. + apply IHe2; assumption. + apply IHe3; assumption.
  - (* EFold *) apply IHe; assumption.
  - (* EUnfold *) apply IHe; assumption.
  - (* ESec *) apply IHe; assumption.
  - (* ETape *) apply IHe; assumption.
  - (* EMux *) destruct He as [Ha [Hb Hc]]. repeat split.
    + apply IHe1; assumption. + apply IHe2; assumption. + apply IHe3; assumption.
  - (* EBoxedLit *) done.
  - (* EBoxedInj *) exact He.
Qed.

Lemma lc_s_open_rev (e : expr) :
  forall n x, lc_s n (open_ n (EFVar x) e) -> lc_s (S n) e.
Proof.
  induction e; intros nn zz H; simpl in H; simpl.
  - destruct (decide (nn = k)) as [E|E].
    + simpl in H. simpl. lia.
    + simpl in H. simpl. lia.
  - done. - done. - done. - done.
  - (* EProd *) destruct H as [Ha Hb]. split.
    + apply (IHe1 nn zz); assumption. + apply (IHe2 nn zz); assumption.
  - (* ESum *) destruct H as [Ha Hb]. split.
    + apply (IHe1 nn zz); assumption. + apply (IHe2 nn zz); assumption.
  - (* EPi *) destruct H as [Ha Hb]. split.
    + apply (IHe1 nn zz); assumption. + apply (IHe2 (S nn) zz); assumption.
  - (* EUnitV *) done.
  - (* ELit *) done.
  - (* EAbs *) destruct H as [Ha Hb]. split.
    + apply (IHe1 nn zz); assumption. + apply (IHe2 (S nn) zz); assumption.
  - (* EApp *) destruct H as [Ha Hb]. split.
    + apply (IHe1 nn zz); assumption. + apply (IHe2 nn zz); assumption.
  - (* ELet *) destruct H as [Ha Hb]. split.
    + apply (IHe1 nn zz); assumption. + apply (IHe2 (S nn) zz); assumption.
  - (* EIte *) destruct H as [Ha [Hb Hc]]. repeat split.
    + apply (IHe1 nn zz); assumption. + apply (IHe2 nn zz); assumption. + apply (IHe3 nn zz); assumption.
  - (* EPair *) destruct H as [Ha Hb]. split.
    + apply (IHe1 nn zz); assumption. + apply (IHe2 nn zz); assumption.
  - (* EProj *) apply (IHe nn zz); assumption.
  - (* EInj *) destruct H as [Ha Hb]. split.
    + apply (IHe1 nn zz); assumption. + apply (IHe2 nn zz); assumption.
  - (* ECase *) destruct H as [Ha [Hb Hc]]. repeat split.
    + apply (IHe1 nn zz); assumption. + apply (IHe2 (S nn) zz); assumption. + apply (IHe3 (S nn) zz); assumption.
  - (* EFold *) apply (IHe nn zz); assumption.
  - (* EUnfold *) apply (IHe nn zz); assumption.
  - (* ESec *) apply (IHe nn zz); assumption.
  - (* ETape *) apply (IHe nn zz); assumption.
  - (* EMux *) destruct H as [Ha [Hb Hc]]. repeat split.
    + apply (IHe1 nn zz); assumption. + apply (IHe2 nn zz); assumption. + apply (IHe3 nn zz); assumption.
  - (* EBoxedLit *) done.
  - (* EBoxedInj *) exact H.
Qed.

(* ================================================================ *)
(* Typed terms and kinded types are sealed-closed                     *)
(* ================================================================ *)
Lemma typing_kinding_lc_s Σ :
  (forall Γ e l τ, typing Σ Γ e l τ -> lc_s 0 e) /\
  (forall Γ τ κ, kinding Σ Γ τ κ -> lc_s 0 τ).
Proof.
  apply typing_kinding_mutind.
  - (* TFVar *) intros. simpl. exact I.
  - (* TUnit *) intros. simpl. exact I.
  - (* TLit *) intros. simpl. exact I.
  - (* TFun *) intros. simpl. exact I.
  - (* TAbs *) intros Γ l1 l2 e τ1 τ2 κ L Hbody IHbody Hk IHk.
    simpl. split.
    + exact IHk.
    + apply (lc_s_open_rev e 0 (fresh_string_of_set EmptyString L)).
      exact (IHbody (fresh_string_of_set EmptyString L) (fresh_string_of_set_fresh L EmptyString)).
  - (* TLet *) intros Γ l1 l2 l e1 e2 τ1 τ2 L He1 IHe1 Hbody IHbody Hl.
    simpl. split.
    + exact IHe1.
    + apply (lc_s_open_rev e2 0 (fresh_string_of_set EmptyString L)).
      exact (IHbody (fresh_string_of_set EmptyString L) (fresh_string_of_set_fresh L EmptyString)).
  - (* TApp *) intros. simpl. split; assumption.
  - (* TPair *) intros. simpl. split; assumption.
  - (* TProj *) intros. simpl. assumption.
  - (* TInj *) intros Γ l b e τ1 τ2 κ He IHe Hk IHk.
    simpl. split; [exact IHk|exact IHe].
  - (* TIf *) intros. simpl. repeat split; assumption.
  - (* TIfNoDep *) intros. simpl. repeat split; assumption.
  - (* TCase *) intros Γ l1 l2 l e0 e1 e2 τ1 τ2 τ κ L1 L2 H0 IH0 Hb1 IHb1 Hb2 IHb2 Hk IHk Hl.
    simpl. repeat split.
    + exact IH0.
    + apply (lc_s_open_rev e1 0 (fresh_string_of_set EmptyString L1)).
      exact (IHb1 (fresh_string_of_set EmptyString L1) (fresh_string_of_set_fresh L1 EmptyString)).
    + apply (lc_s_open_rev e2 0 (fresh_string_of_set EmptyString L2)).
      exact (IHb2 (fresh_string_of_set EmptyString L2) (fresh_string_of_set_fresh L2 EmptyString)).
  - (* TCaseNoDep *) intros Γ l0 l1 l2 l e0 e1 e2 τ1 τ2 τ κ L1 L2 H0 IH0 Hb1 IHb1 Hb2 IHb2 Hk IHk Hl.
    simpl. repeat split.
    + exact IH0.
    + apply (lc_s_open_rev e1 0 (fresh_string_of_set EmptyString L1)).
      exact (IHb1 (fresh_string_of_set EmptyString L1) (fresh_string_of_set_fresh L1 EmptyString)).
    + apply (lc_s_open_rev e2 0 (fresh_string_of_set EmptyString L2)).
      exact (IHb2 (fresh_string_of_set EmptyString L2) (fresh_string_of_set_fresh L2 EmptyString)).
  - (* TFold *) intros. simpl. assumption.
  - (* TUnfold *) intros. simpl. assumption.
  - (* TSec *) intros. simpl. assumption.
  - (* TMux *) intros. simpl. repeat split; assumption.
  - (* TOInj *) intros Γ b e τ1 τ2 He IHe Hk IHk.
    simpl. split; [exact IHk|exact IHe].
  - (* TOIf *) intros. simpl. repeat split; assumption.
  - (* TOCase *) intros Γ l1 l2 e0 e1 e2 τ1 τ2 τ κ L1 L2 H0 IH0 Hb1 IHb1 Hb2 IHb2 Hk IHk.
    simpl. repeat split.
    + exact IH0.
    + apply (lc_s_open_rev e1 0 (fresh_string_of_set EmptyString L1)).
      exact (IHb1 (fresh_string_of_set EmptyString L1) (fresh_string_of_set_fresh L1 EmptyString)).
    + apply (lc_s_open_rev e2 0 (fresh_string_of_set EmptyString L2)).
      exact (IHb2 (fresh_string_of_set EmptyString L2) (fresh_string_of_set_fresh L2 EmptyString)).
  - (* TTape *) intros. simpl. assumption.
  - (* TBoxedLit *) intros. simpl. exact I.
  - (* TBoxedInj *) intros Γ b v ω Hov.
    simpl. apply LCBoxedInj.
    + exact (ovalty_otval _ _ Hov).
    + exact (ovalty_inj_oval b ω v Hov).
  - (* TConv *) intros. assumption.
  - (* KADT *) intros. simpl. exact I.
  - (* KUnit *) intros. simpl. exact I.
  - (* KBool *) intros. simpl. exact I.
  - (* KPi *) intros Γ l τ1 τ2 κ1 κ2 L Hbody IHbody Hk IHk.
    simpl. split.
    + exact IHk.
    + apply (lc_s_open_rev τ2 0 (fresh_string_of_set EmptyString L)).
      exact (IHbody (fresh_string_of_set EmptyString L) (fresh_string_of_set_fresh L EmptyString)).
  - (* KProd *) intros. simpl. split; assumption.
  - (* KSum *) intros. simpl. split; assumption.
  - (* KOSum *) intros. simpl. split; assumption.
  - (* KOADT *) intros. simpl. split; [exact I|assumption].
  - (* KIf *) intros. simpl. repeat split; assumption.
  - (* KCase *) intros Γ e0 τ1 τ2 τ1' τ2' L1 L2 H0 IH0 Hb1 IHb1 Hb2 IHb2.
    simpl. repeat split.
    + exact IH0.
    + apply (lc_s_open_rev τ1 0 (fresh_string_of_set EmptyString L1)).
      exact (IHb1 (fresh_string_of_set EmptyString L1) (fresh_string_of_set_fresh L1 EmptyString)).
    + apply (lc_s_open_rev τ2 0 (fresh_string_of_set EmptyString L2)).
      exact (IHb2 (fresh_string_of_set EmptyString L2) (fresh_string_of_set_fresh L2 EmptyString)).
  - (* KLet *) intros Γ e τ τ' L He IHe Hb IHb.
    simpl. split.
    + exact IHe.
    + apply (lc_s_open_rev τ 0 (fresh_string_of_set EmptyString L)).
      exact (IHb (fresh_string_of_set EmptyString L) (fresh_string_of_set_fresh L EmptyString)).
  - (* KSub *) intros. assumption.
Qed.

Lemma typing_lc_s Σ Γ e l τ : typing Σ Γ e l τ -> lc_s 0 e.
Proof. exact (proj1 (typing_kinding_lc_s Σ) Γ e l τ). Qed.

Lemma kinding_lc_s Σ Γ τ κ : kinding Σ Γ τ κ -> lc_s 0 τ.
Proof. exact (proj2 (typing_kinding_lc_s Σ) Γ τ κ). Qed.

Lemma kinding_pi_lc_s Σ Γ l a b κ : kinding Σ Γ (EPi l a b) κ -> lc_s 0 a /\ lc_s 1 b.
Proof.
  intros H. pose proof (kinding_lc_s Σ Γ (EPi l a b) κ H) as Hc.
  simpl in Hc. exact Hc.
Qed.

Lemma lc_s_open_id e : lc_s 0 e -> forall s, open_ 0 s e = e.
Proof.
  intros H s.
  exact (open_lc_n e 0 (lc_s_lc_n e 0 H) 0 (le_n 0) s).
Qed.

Lemma kinding_open_id Σ Γ τ κ : kinding Σ Γ τ κ -> forall s, open_ 0 s τ = τ.
Proof.
  intros H s. exact (lc_s_open_id τ (kinding_lc_s Σ Γ τ κ H) s).
Qed.

Lemma lc_lc_s (e : expr) : lc e -> lc_s 0 e.
Proof.
  induction 1.
  - simpl. exact I.
  - simpl. exact I.
  - (* LCPi *) simpl. split.
    + exact IHlc.
    + apply (lc_s_open_rev τ2 0 (fresh_string_of_set EmptyString L)).
      apply H0. apply (fresh_string_of_set_fresh L EmptyString).
  - (* LCAbs *) simpl. split.
    + exact IHlc.
    + apply (lc_s_open_rev e 0 (fresh_string_of_set EmptyString L)).
      apply H0. apply (fresh_string_of_set_fresh L EmptyString).
  - (* LCLet *) simpl. split.
    + exact IHlc.
    + apply (lc_s_open_rev e2 0 (fresh_string_of_set EmptyString L)).
      apply H0. apply (fresh_string_of_set_fresh L EmptyString).
  - (* LCCase *) simpl. repeat split.
    + exact IHlc.
    + apply (lc_s_open_rev e1 0 (fresh_string_of_set EmptyString L1)).
      apply H0. apply (fresh_string_of_set_fresh L1 EmptyString).
    + apply (lc_s_open_rev e2 0 (fresh_string_of_set EmptyString L2)).
      apply H2. apply (fresh_string_of_set_fresh L2 EmptyString).
  - simpl. exact I.
  - simpl. exact I.
  - simpl. exact I.
  - simpl. split; assumption.
  - simpl. exact I.
  - simpl. assumption.
  - simpl. repeat split; assumption.
  - simpl. split; assumption.
  - simpl. split; assumption.
  - simpl. assumption.
  - simpl. split; assumption.
  - simpl. split; assumption.
  - simpl. assumption.
  - simpl. assumption.
  - simpl. assumption.
  - simpl. repeat split; assumption.
  - simpl. exact I.
  - simpl. constructor; assumption.
Qed.

Lemma lc_s_open_lc e s : lc e -> lc_s 0 s -> lc_s 0 (open_ 0 s e).
Proof.
  intros He Hs.
  apply (lc_s_open_fwd e 0 s).
  - apply (lc_s_mono e 0 1); [apply lc_lc_s; exact He|lia].
  - exact Hs.
Qed.

Lemma open_open_comm (s t : expr) (Hs : lc_n 0 s) (Ht : lc_n 0 t) :
  forall e i j, i <= j ->
    open_ i s (open_ (S j) t e) = open_ (S j) t (open_ i s e).
Proof.
  induction e; intros i j Hij; simpl.
  - (* EBVar *)
    destruct (decide (S j = k)) as [A|A].
    + destruct (decide (i = k)) as [B|B].
      * exfalso; lia.
      * simpl. destruct (decide (S j = k)) as [A'|A']; [|exfalso; apply A'; exact A].
        simpl. rewrite (open_lc_n t 0 Ht i (Nat.le_0_l i) s). reflexivity.
    + destruct (decide (i = k)) as [B|B].
      * subst k. destruct (decide (S j = i)) as [A'|A']; [exfalso; lia|].
        simpl. destruct (decide (i = i)) as [E|E]; [|exfalso; apply E; reflexivity].
        simpl. rewrite (open_lc_n s 0 Hs (S j) (Nat.le_0_l (S j)) t). reflexivity.
      * simpl. destruct (decide (S j = k)) as [A'|A']; [exfalso; apply A; exact A'|].
        destruct (decide (i = k)) as [B'|B']; [exfalso; apply B; exact B'|].
        simpl. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - (* EProd *) simpl. f_equal; [apply IHe1|apply IHe2]; exact Hij.
  - (* ESum *) simpl. f_equal; [apply IHe1|apply IHe2]; exact Hij.
  - (* EPi *) simpl. f_equal.
    + apply IHe1; exact Hij.
    + apply IHe2; lia.
  - reflexivity.
  - reflexivity.
  - (* EAbs *) simpl. f_equal.
    + apply IHe1; exact Hij.
    + apply IHe2; lia.
  - (* EApp *) simpl. f_equal; [apply IHe1|apply IHe2]; exact Hij.
  - (* ELet *) simpl. f_equal.
    + apply IHe1; exact Hij.
    + apply IHe2; lia.
  - (* EIte *) simpl. f_equal; [apply IHe1|apply IHe2|apply IHe3]; exact Hij.
  - (* EPair *) simpl. f_equal; [apply IHe1|apply IHe2]; exact Hij.
  - (* EProj *) simpl. f_equal. apply IHe; exact Hij.
  - (* EInj *) simpl. f_equal; [apply IHe1|apply IHe2]; exact Hij.
  - (* ECase *) simpl. f_equal.
    + apply IHe1; exact Hij.
    + apply IHe2; lia.
    + apply IHe3; lia.
  - (* EFold *) simpl. f_equal. apply IHe; exact Hij.
  - (* EUnfold *) simpl. f_equal. apply IHe; exact Hij.
  - (* ESec *) simpl. f_equal. apply IHe; exact Hij.
  - (* ETape *) simpl. f_equal. apply IHe; exact Hij.
  - (* EMux *) simpl. f_equal; [apply IHe1|apply IHe2|apply IHe3]; exact Hij.
  - reflexivity.
  - reflexivity.
Qed.

Fixpoint size (e : expr) : nat :=
  match e with
  | EBVar _ | EFVar _ | EGVar _ | EUnitT | EUnitV | EBool _ | ELit _ | EBoxedLit _ => 1
  | EProd a b | ESum _ a b | EPi _ a b | EAbs _ a b | EApp a b | ELet a b
  | EPair a b | EInj _ _ a b | EBoxedInj _ a b => 1 + size a + size b
  | EProj _ e | EFold _ e | EUnfold _ e | ESec e | ETape e => 1 + size e
  | EIte _ e0 e1 e2 | ECase _ e0 e1 e2 | EMux e0 e1 e2 => 1 + size e0 + size e1 + size e2
  end.

Lemma size_open_fvar_le (e : expr) :
  forall i x, size (open_ i (EFVar x) e) <= size e.
Proof.
  induction e; intros i zz; simpl.
  - (* EBVar *) destruct (decide (i = k)); simpl; lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - (* EProd *) pose proof (IHe1 i zz). pose proof (IHe2 i zz). lia.
  - (* ESum *) pose proof (IHe1 i zz). pose proof (IHe2 i zz). lia.
  - (* EPi *) pose proof (IHe1 i zz). pose proof (IHe2 (S i) zz). lia.
  - lia.
  - lia.
  - (* EAbs *) pose proof (IHe1 i zz). pose proof (IHe2 (S i) zz). lia.
  - (* EApp *) pose proof (IHe1 i zz). pose proof (IHe2 i zz). lia.
  - (* ELet *) pose proof (IHe1 i zz). pose proof (IHe2 (S i) zz). lia.
  - (* EIte *) pose proof (IHe1 i zz). pose proof (IHe2 i zz). pose proof (IHe3 i zz). lia.
  - (* EPair *) pose proof (IHe1 i zz). pose proof (IHe2 i zz). lia.
  - (* EProj *) pose proof (IHe i zz). lia.
  - (* EInj *) pose proof (IHe1 i zz). pose proof (IHe2 i zz). lia.
  - (* ECase *) pose proof (IHe1 i zz). pose proof (IHe2 (S i) zz). pose proof (IHe3 (S i) zz). lia.
  - (* EFold *) pose proof (IHe i zz). lia.
  - (* EUnfold *) pose proof (IHe i zz). lia.
  - (* ESec *) pose proof (IHe i zz). lia.
  - (* ETape *) pose proof (IHe i zz). lia.
  - (* EMux *) pose proof (IHe1 i zz). pose proof (IHe2 i zz). pose proof (IHe3 i zz). lia.
  - lia.
  - (* EBoxedInj *) pose proof (IHe1 i zz). pose proof (IHe2 i zz). lia.
Qed.

Lemma lc_s_lc_gen : forall n e, size e < n -> lc_s 0 e -> lc e.
Proof.
  induction n as [|n IH]; intros e Hsz H.
  - lia.
  - destruct e; simpl in H; simpl in Hsz.
    + (* EBVar *) exfalso; lia.
    + (* EFVar *) constructor.
    + (* EGVar *) constructor.
    + (* EUnitT *) constructor.
    + (* EBool *) constructor.
    + (* EProd *) destruct H as [Ha Hb]. apply LCProd.
      * apply (IH e1); [lia|exact Ha].
      * apply (IH e2); [lia|exact Hb].
    + (* ESum *) destruct H as [Ha Hb]. apply LCSum.
      * apply (IH e1); [lia|exact Ha].
      * apply (IH e2); [lia|exact Hb].
    + (* EPi *) destruct H as [Ha Hb]. apply LCPi with (L := ∅).
      * intros x _. apply (IH (open_ 0 (EFVar x) e2)).
        -- pose proof (size_open_fvar_le e2 0 x). lia.
        -- apply (lc_s_open_fwd e2 0 (EFVar x)); [exact Hb|simpl; exact I].
      * apply (IH e1); [lia|exact Ha].
    + (* EUnitV *) constructor.
    + (* ELit *) constructor.
    + (* EAbs *) destruct H as [Ha Hb]. apply LCAbs with (L := ∅).
      * intros x _. apply (IH (open_ 0 (EFVar x) e2)).
        -- pose proof (size_open_fvar_le e2 0 x). lia.
        -- apply (lc_s_open_fwd e2 0 (EFVar x)); [exact Hb|simpl; exact I].
      * apply (IH e1); [lia|exact Ha].
    + (* EApp *) destruct H as [Ha Hb]. apply LCApp.
      * apply (IH e1); [lia|exact Ha].
      * apply (IH e2); [lia|exact Hb].
    + (* ELet *) destruct H as [Ha Hb]. apply LCLet with (L := ∅).
      * intros x _. apply (IH (open_ 0 (EFVar x) e2)).
        -- pose proof (size_open_fvar_le e2 0 x). lia.
        -- apply (lc_s_open_fwd e2 0 (EFVar x)); [exact Hb|simpl; exact I].
      * apply (IH e1); [lia|exact Ha].
    + (* EIte *) destruct H as [Ha [Hb Hc]]. apply LCIte.
      * apply (IH e1); [lia|exact Ha].
      * apply (IH e2); [lia|exact Hb].
      * apply (IH e3); [lia|exact Hc].
    + (* EPair *) destruct H as [Ha Hb]. apply LCPair.
      * apply (IH e1); [lia|exact Ha].
      * apply (IH e2); [lia|exact Hb].
    + (* EProj *) apply LCProj. apply (IH e); [lia|exact H].
    + (* EInj *) destruct H as [Ha Hb]. apply LCInj.
      * apply (IH e1); [lia|exact Ha].
      * apply (IH e2); [lia|exact Hb].
    + (* ECase *) destruct H as [Ha [Hb Hc]]. apply LCCase with (L1 := ∅) (L2 := ∅).
      * intros x _. apply (IH (open_ 0 (EFVar x) e2)).
        -- pose proof (size_open_fvar_le e2 0 x). lia.
        -- apply (lc_s_open_fwd e2 0 (EFVar x)); [exact Hb|simpl; exact I].
      * intros x _. apply (IH (open_ 0 (EFVar x) e3)).
        -- pose proof (size_open_fvar_le e3 0 x). lia.
        -- apply (lc_s_open_fwd e3 0 (EFVar x)); [exact Hc|simpl; exact I].
      * apply (IH e1); [lia|exact Ha].
    + (* EFold *) apply LCFold. apply (IH e); [lia|exact H].
    + (* EUnfold *) apply LCUnfold. apply (IH e); [lia|exact H].
    + (* ESec *) apply LCSec. apply (IH e); [lia|exact H].
    + (* ETape *) apply LCTape. apply (IH e); [lia|exact H].
    + (* EMux *) destruct H as [Ha [Hb Hc]]. apply LCMux.
      * apply (IH e1); [lia|exact Ha].
      * apply (IH e2); [lia|exact Hb].
      * apply (IH e3); [lia|exact Hc].
    + (* EBoxedLit *) constructor.
    + (* EBoxedInj *) exact H.
Qed.

Lemma lc_s_lc e : lc_s 0 e -> lc e.
Proof. intros H. exact (lc_s_lc_gen (S (size e)) e (Nat.lt_succ_diag_r _) H). Qed.

Lemma pared_subst_arg Σ xx s s' (Hs : lc s) (Hs' : lc s')
  (Hss : pared Σ s s') (HΣ : xx ∉ gctx_fv Σ) :
  forall e, lc e -> pared Σ (subst xx s e) (subst xx s' e).
Proof.
  intros e Hlc.
  assert (Hns : lc_n 0 s) by (apply lc_lc_n0; exact Hs).
  assert (Hns' : lc_n 0 s') by (apply lc_lc_n0; exact Hs').
  induction Hlc.
  - (* LCFVar *) simpl. destruct (decide (xx = x)) as [E|E].
    + rewrite (decide_True s (EFVar x) E).
      rewrite (decide_True s' (EFVar x) E). exact Hss.
    + rewrite (decide_False s (EFVar x) E).
      rewrite (decide_False s' (EFVar x) E).
      apply RRefl. constructor.
  - (* LCGVar *) simpl. apply RRefl. constructor.
  - (* LCPi *) simpl. apply RCgrPi with (L := L ∪ {[xx]}).
    + exact IHHlc.
    + intros y Hy. assert (Hyx : xx <> y) by set_solver.
      rewrite <- (subst_open_fvar_lc2 xx s y τ2 Hns Hyx).
      rewrite <- (subst_open_fvar_lc2 xx s' y τ2 Hns' Hyx).
      apply H0. set_solver.
  - (* LCAbs *) simpl. apply RCgrAbs with (L := L ∪ {[xx]}).
    + exact IHHlc.
    + intros y Hy. assert (Hyx : xx <> y) by set_solver.
      rewrite <- (subst_open_fvar_lc2 xx s y e Hns Hyx).
      rewrite <- (subst_open_fvar_lc2 xx s' y e Hns' Hyx).
      apply H0. set_solver.
  - (* LCLet *) simpl. apply RCgrLet with (L := L ∪ {[xx]}).
    + exact IHHlc.
    + intros y Hy. assert (Hyx : xx <> y) by set_solver.
      rewrite <- (subst_open_fvar_lc2 xx s y e2 Hns Hyx).
      rewrite <- (subst_open_fvar_lc2 xx s' y e2 Hns' Hyx).
      apply H0. set_solver.
  - (* LCCase *) simpl. apply RCgrCase with (L1 := L1 ∪ {[xx]}) (L2 := L2 ∪ {[xx]}).
    + exact IHHlc.
    + intros y Hy. assert (Hyx : xx <> y) by set_solver.
      rewrite <- (subst_open_fvar_lc2 xx s y e1 Hns Hyx).
      rewrite <- (subst_open_fvar_lc2 xx s' y e1 Hns' Hyx).
      apply H0. set_solver.
    + intros y Hy. assert (Hyx : xx <> y) by set_solver.
      rewrite <- (subst_open_fvar_lc2 xx s y e2 Hns Hyx).
      rewrite <- (subst_open_fvar_lc2 xx s' y e2 Hns' Hyx).
      apply H2. set_solver.
  - (* LCUnitT *) simpl. apply RRefl. constructor.
  - (* LCUnitV *) simpl. apply RRefl. constructor.
  - (* LCBool *) simpl. apply RRefl. constructor.
  - (* LCApp *) simpl. apply RCgrApp; assumption.
  - (* LCLit *) simpl. apply RRefl. constructor.
  - (* LCSec *) simpl. apply RCgrSec. assumption.
  - (* LCIte *) simpl. apply RCgrIf; assumption.
  - (* LCProd *) simpl. apply RCgrProd; assumption.
  - (* LCPair *) simpl. apply RCgrPair; assumption.
  - (* LCProj *) simpl. apply RCgrProj. assumption.
  - (* LCSum *) simpl. apply RCgrSum; assumption.
  - (* LCInj *) simpl. apply RCgrInj; assumption.
  - (* LCFold *) simpl. apply RCgrFold. assumption.
  - (* LCUnfold *) simpl. apply RCgrUnfold. assumption.
  - (* LCTape *) simpl. apply RCgrTape. assumption.
  - (* LCMux *) simpl. apply RCgrMux; assumption.
  - (* LCBoxedLit *) simpl. apply RRefl. constructor.
  - (* LCBoxedInj *) simpl. apply RRefl. apply LCBoxedInj; assumption.
Qed.

Ltac pb2 xx s s' Hns Hns' E E' IH L :=
  let y := fresh "y" in
  intros y Hy;
  let Hyx := fresh "Hyx" in assert (Hyx : xx <> y) by (intros ->; apply Hy; set_solver);
  let He1 := fresh "He1" in
  assert (He1 : open (EFVar y) (subst xx s E) = subst xx s (open (EFVar y) E))
    by (symmetry; rewrite (subst_open_open xx s (EFVar y) E Hns);
        by rewrite (subst_fvar_neq xx s y Hyx));
  let He2 := fresh "He2" in
  assert (He2 : open (EFVar y) (subst xx s' E') = subst xx s' (open (EFVar y) E'))
    by (symmetry; rewrite (subst_open_open xx s' (EFVar y) E' Hns');
        by rewrite (subst_fvar_neq xx s' y Hyx));
  rewrite He1, He2;
  apply (IH y); set_solver.

Lemma pared_subst2 Σ xx s s' (Hs : lc s) (Hs' : lc s')
  (Hss : pared Σ s s') (HΣ : xx ∉ gctx_fv Σ) :
  forall e e', pared Σ e e' ->
    pared Σ (subst xx s e) (subst xx s' e').
Proof.
  assert (Hns : lc_n 0 s) by (apply lc_lc_n0; auto).
  assert (Hns' : lc_n 0 s') by (apply lc_lc_n0; auto).
  intros e e' H. induction H.
  - (* RApp *) simpl. rewrite (subst_open_open xx s' e1' e2' Hns').
    eapply RApp with (L := L ∪ {[xx]}).
    + exact IHpared.
    + pb2 xx s s' Hns Hns' e2 e2' H1 L.
    + apply lc_subst; auto.
  - (* RFun *) simpl.
    assert (Hx : xx ∉ gdef_fv (DFun T e)) by (apply (gctx_fv_notin Σ x (DFun T e) xx); auto).
    simpl in Hx. assert (Hfe : xx ∉ fv e) by set_solver.
    rewrite (subst_not_fv xx s' e Hfe). exact (RFun Σ x T e H).
  - (* ROADT *) simpl.
    assert (Hx : xx ∉ gdef_fv (DOADT τ' τ)) by (apply (gctx_fv_notin Σ X (DOADT τ' τ) xx); auto).
    simpl in Hx. assert (Hfτ : xx ∉ fv τ) by set_solver.
    rewrite (subst_open_open xx s' e' τ Hns').
    rewrite (subst_not_fv xx s' τ Hfτ).
    exact (ROADT Σ X τ' τ (subst xx s e) (subst xx s' e') H IHpared).
  - (* RLet *) simpl. rewrite (subst_open_open xx s' e1' e2' Hns').
    eapply RLet with (L := L ∪ {[xx]}).
    + exact IHpared.
    + pb2 xx s s' Hns Hns' e2 e2' H1 L.
  - (* RProj *) destruct b; simpl;
      [ eapply RProj with (b := true) | eapply RProj with (b := false) ]; eauto.
  - (* RFold *) simpl. eapply RFold. exact IHpared.
  - (* RIf *) destruct b; simpl;
      [ eapply RIf with (b := true) | eapply RIf with (b := false) ]; eauto.
  - (* RCase *) destruct b; simpl.
    + rewrite (subst_open_open xx s' e0' e1' Hns').
      eapply RCase with (b := true) (L1 := L1 ∪ {[xx]}) (L2 := L2 ∪ {[xx]}).
      * exact IHpared.
      * pb2 xx s s' Hns Hns' e1 e1' H1 L1.
      * pb2 xx s s' Hns Hns' e2 e2' H3 L2.
      * apply lc_subst; auto.
    + rewrite (subst_open_open xx s' e0' e2' Hns').
      eapply RCase with (b := false) (L1 := L1 ∪ {[xx]}) (L2 := L2 ∪ {[xx]}).
      * exact IHpared.
      * pb2 xx s s' Hns Hns' e1 e1' H1 L1.
      * pb2 xx s s' Hns Hns' e2 e2' H3 L2.
      * apply lc_subst; auto.
  - (* RMux *) destruct b; simpl;
      [ eapply RMux with (b := true) | eapply RMux with (b := false) ]; eauto.
  - (* RSec *) simpl. apply RSec.
  - (* ROInj *) simpl.
    rewrite (subst_not_fv xx s ω (otval_not_fv xx ω H)).
    rewrite (subst_not_fv xx s v (oval_not_fv xx v H0)).
    apply ROInj; auto.
  - (* ROIf *) destruct b; simpl;
      [ eapply ROIf with (b := true) | eapply ROIf with (b := false) ]; eauto.
  - (* ROCase *) destruct b; simpl.
    + rewrite (subst_open_open xx s' v e1' Hns').
      rewrite (subst_open_open xx s' v2 e2' Hns').
      rewrite (subst_not_fv xx s' v (oval_not_fv xx v H)).
      rewrite (subst_not_fv xx s' v2 (oval_not_fv xx v2 (ovalty_oval v2 ω2 H1))).
      eapply ROCase with (b := true) (v1 := v1) (v2 := v2) (e1 := subst xx s e1) (e2 := subst xx s e2) (e1' := subst xx s' e1') (e2' := subst xx s' e2') (L1 := L1 ∪ {[xx]}) (L2 := L2 ∪ {[xx]}).
      * exact H.
      * exact H0.
      * exact H1.
      * pb2 xx s s' Hns Hns' e1 e1' H3 L1.
      * pb2 xx s s' Hns Hns' e2 e2' H5 L2.
    + rewrite (subst_open_open xx s' v e2' Hns').
      rewrite (subst_open_open xx s' v1 e1' Hns').
      rewrite (subst_not_fv xx s' v (oval_not_fv xx v H)).
      rewrite (subst_not_fv xx s' v1 (oval_not_fv xx v1 (ovalty_oval v1 ω1 H0))).
      eapply ROCase with (b := false) (v1 := v1) (v2 := v2) (e1 := subst xx s e1) (e2 := subst xx s e2) (e1' := subst xx s' e1') (e2' := subst xx s' e2') (L1 := L1 ∪ {[xx]}) (L2 := L2 ∪ {[xx]}).
      * exact H.
      * exact H0.
      * exact H1.
      * pb2 xx s s' Hns Hns' e1 e1' H3 L1.
      * pb2 xx s s' Hns Hns' e2 e2' H5 L2.
  - (* ROIfApp *) simpl. eapply ROIfApp; eauto.
  - (* ROIfSec *) simpl. eapply ROIfSec; eauto.
  - (* ROIfIf *) simpl. eapply ROIfIf; eauto.
  - (* ROIfProj *) simpl. eapply ROIfProj; eauto.
  - (* ROIfCase *) simpl.
    eapply ROIfCase with (L1 := L1 ∪ {[xx]}) (L2 := L2 ∪ {[xx]}).
    + eauto.
    + eauto.
    + pb2 xx s s' Hns Hns' e3 e3' H2 L1.
    + pb2 xx s s' Hns Hns' e4 e4' H4 L2.
  - (* ROIfUnfold *) simpl. eapply ROIfUnfold; eauto.
  - (* RTapeOIf *) simpl. eapply RTapeOIf; eauto.
  - (* RTapePair *) simpl. eapply RTapePair; eauto using woval_subst.
  - (* RTapeUnitV *) simpl. apply RTapeUnitV.
  - (* RTapeBoxedLit *) simpl. apply RTapeBoxedLit.
  - (* RTapeBoxedInj *) simpl. apply RTapeBoxedInj; auto.
  - (* RCgrPi *) simpl. eapply RCgrPi with (L := L ∪ {[xx]}).
    + exact IHpared.
    + pb2 xx s s' Hns Hns' τ2 τ2' H1 L.
  - (* RCgrAbs *) simpl. eapply RCgrAbs with (L := L ∪ {[xx]}).
    + exact IHpared.
    + pb2 xx s s' Hns Hns' e e' H1 L.
  - (* RCgrApp *) simpl. eapply RCgrApp; eauto.
  - (* RCgrLet *) simpl. eapply RCgrLet with (L := L ∪ {[xx]}).
    + exact IHpared.
    + pb2 xx s s' Hns Hns' e2 e2' H1 L.
  - (* RCgrSec *) simpl. eapply RCgrSec; eauto.
  - (* RCgrIf *) simpl. eapply RCgrIf; eauto.
  - (* RCgrProd *) simpl. eapply RCgrProd; eauto.
  - (* RCgrPair *) simpl. eapply RCgrPair; eauto.
  - (* RCgrProj *) simpl. eapply RCgrProj; eauto.
  - (* RCgrSum *) simpl. eapply RCgrSum; eauto.
  - (* RCgrInj *) simpl. eapply RCgrInj; eauto.
  - (* RCgrCase *) simpl.
    eapply RCgrCase with (L1 := L1 ∪ {[xx]}) (L2 := L2 ∪ {[xx]}).
    + eauto.
    + pb2 xx s s' Hns Hns' e1 e1' H1 L1.
    + pb2 xx s s' Hns Hns' e2 e2' H3 L2.
  - (* RCgrFold *) simpl. eapply RCgrFold; eauto.
  - (* RCgrUnfold *) simpl. eapply RCgrUnfold; eauto.
  - (* RCgrMux *) simpl. eapply RCgrMux; eauto.
  - (* RCgrTape *) simpl. eapply RCgrTape; eauto.
  - (* RRefl *) simpl. exact (pared_subst_arg Σ xx s s' Hs Hs' Hss HΣ e H).
Qed.

Lemma pared_open_arg Σ τ (Hτ : lc_s 1 τ) s s' (Hs : lc s) (Hs' : lc s')
  (Hss : pared Σ s s') :
  pared Σ (open s τ) (open s' τ).
Proof.
  pose (x := fresh_string_of_set EmptyString (fv τ ∪ gctx_fv Σ)).
  pose proof (fresh_string_of_set_fresh (fv τ ∪ gctx_fv Σ) EmptyString) as HxSS.
  assert (Hxτ : x ∉ fv τ) by set_solver.
  assert (HxΣ : x ∉ gctx_fv Σ) by set_solver.
  assert (Hlcx : lc (open (EFVar x) τ)).
  { apply lc_s_lc. apply (lc_s_open_fwd τ 0 (EFVar x)); [exact Hτ|simpl; exact I]. }
  pose proof (pared_subst2 Σ x s s' Hs Hs' Hss HxΣ
    (open (EFVar x) τ) (open (EFVar x) τ) (RRefl Σ _ Hlcx)) as Hres.
  rewrite (subst_open_same x s τ (lc_lc_n0 s Hs) Hxτ) in Hres.
  rewrite (subst_open_same x s' τ (lc_lc_n0 s' Hs') Hxτ) in Hres.
  exact Hres.
Qed.

Lemma pared_equiv_open_arg Σ τ (Hτ : lc_s 1 τ) s s' (Hs : lc s) (Hs' : lc s')
  (Hss : pared Σ s s') :
  pared_equiv Σ (open s τ) (open s' τ).
Proof.
  apply (QRRedL Σ (open s τ) (open s' τ) (open s' τ)).
  - apply (pared_open_arg Σ τ Hτ s s' Hs Hs' Hss).
  - apply (QRRefl Σ (open s' τ)).
Qed.

Lemma pared_equiv_pi_inv_gen Σ :
  forall τ σ, pared_equiv Σ τ σ ->
    forall (l : bool) (a : expr) (b : expr) (l2 : bool) (a2 : expr) (b2 : expr),
      τ = EPi l a b -> σ = EPi l2 a2 b2 ->
      l = l2 /\ pared_equiv Σ a a2 /\
        exists L, forall x, x ∉ L ->
          pared_equiv Σ (open (EFVar x) b) (open (EFVar x) b2).
Proof.
  intros τ σ H. induction H; intros l a b l2 a2 b2 E1 E2.
  - (* QRRefl *) rewrite E1 in E2. injection E2 as El Ea Eb. subst.
    split; [reflexivity|split; [apply QRRefl|exists ∅; intros x _; apply QRRefl]].
  - (* QRRedL *) rewrite E1 in H. inversion H; subst.
    + (* RCgrPi *)
      destruct (IHpared_equiv l τ1' τ2' l2 a2 b2 eq_refl eq_refl) as [El [Eaa [L' Hb]]].
      split; [exact El|split].
      * apply (QRRedL Σ a τ1' a2); assumption.
      * exists (L ∪ L'). intros x Hx.
        apply (QRRedL Σ (open (EFVar x) b) (open (EFVar x) τ2') (open (EFVar x) b2)).
        -- apply H6. set_solver.
        -- apply Hb. set_solver.
    + (* RRefl *) apply (IHpared_equiv l a b l2 a2 b2); [reflexivity|reflexivity].
  - (* QRRedR *) rewrite E2 in H. inversion H; subst.
    + (* RCgrPi *)
      destruct (IHpared_equiv l a b l2 τ1' τ2' eq_refl eq_refl) as [El [Eaa [L' Hb]]].
      split; [exact El|split].
      * apply (QRRedR Σ a a2 τ1'); assumption.
      * exists (L ∪ L'). intros x Hx.
        apply (QRRedR Σ (open (EFVar x) b) (open (EFVar x) b2) (open (EFVar x) τ2')).
        -- apply H6. set_solver.
        -- apply Hb. set_solver.
    + (* RRefl *) apply (IHpared_equiv l a b l2 a2 b2); [reflexivity|reflexivity].
Qed.

Lemma pared_equiv_pi_inv Σ (l l2 : bool) (a b a2 b2 : expr) :
  pared_equiv Σ (EPi l a b) (EPi l2 a2 b2) ->
  l = l2 /\ pared_equiv Σ a a2 /\
    exists L, forall x, x ∉ L ->
      pared_equiv Σ (open (EFVar x) b) (open (EFVar x) b2).
Proof.
  intros H.
  exact (pared_equiv_pi_inv_gen Σ (EPi l a b) (EPi l2 a2 b2) H
           l a b l2 a2 b2 eq_refl eq_refl).
Qed.

(* ================================================================ *)
(* Level preorder facts (labels)                                      *)
(* ================================================================ *)
Lemma llabel_sqsubseteq_refl (l : bool) : l ⊑ l.
Proof. destruct l; reflexivity. Qed.

Lemma llabel_sqsubseteq_trans (l1 l2 l3 : bool) :
  l1 ⊑ l2 -> l2 ⊑ l3 -> l1 ⊑ l3.
Proof.
  unfold sqsubseteq, bool_le. intros. destruct l1, l2, l3; simpl in *; auto.
Qed.

(* ================================================================ *)
(* Basic algebra of conversion                                        *)
(* ================================================================ *)
Lemma pared_equiv_sym Σ e e' : pared_equiv Σ e e' -> pared_equiv Σ e' e.
Proof.
  intros H. induction H.
  - apply QRRefl.
  - apply (QRRedR Σ e2 e1 e1'); [exact H|exact IHpared_equiv].
  - apply (QRRedL Σ e2 e2' e1); assumption.
Qed.

Lemma pared_rtc_equiv Σ e e' : rtc (pared Σ) e e' -> pared_equiv Σ e e'.
Proof.
  intros H. induction H as [|x y z Hxy Hyz IH].
  - apply QRRefl.
  - apply (QRRedL Σ x y z); assumption.
Qed.
