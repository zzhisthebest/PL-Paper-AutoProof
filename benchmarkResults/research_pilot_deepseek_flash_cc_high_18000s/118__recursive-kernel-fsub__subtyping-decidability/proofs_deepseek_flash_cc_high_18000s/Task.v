Require Import Rules.

Set Implicit Arguments.

Require Import Metalib.Metatheory.

Require Import Program.Equality.

Require Export Coq.micromega.Lia.

Notation empty_menv := (@nil (nat * nat)).

(* ===== Renaming / equivariance infrastructure (proved) ===== *)

Definition swp (x y : atom) (z : atom) : atom :=
  if z == x then y else if z == y then x else z.
Lemma swp_eq_l : forall x y, swp x y x = y.
Proof. intros. unfold swp. destruct (x == x) as [e|ne]; auto. exfalso; auto. Qed.
Lemma swp_eq_r : forall x y, swp x y y = x.
Proof. intros. unfold swp. destruct (y == x) as [e|ne]; [subst; auto|].
  destruct (y == y) as [e|ne2]; auto. exfalso; auto. Qed.
Lemma swp_other : forall x y z, z <> x -> z <> y -> swp x y z = z.
Proof. intros x y z Hx Hy. unfold swp.
  destruct (z == x) as [e|ne1]; [exfalso; auto|].
  destruct (z == y) as [e|ne2]; [exfalso; auto|auto]. Qed.
Lemma swp_invol : forall x y z, swp x y (swp x y z) = z.
Proof. intros. destruct (z == x) as [e|n1].
  - subst. rewrite swp_eq_l, swp_eq_r. auto.
  - destruct (z == y) as [e|n2].
    + subst. rewrite swp_eq_r, swp_eq_l. auto.
    + rewrite (@swp_other x y z n1 n2). rewrite (@swp_other x y z n1 n2). auto. Qed.

Fixpoint ren (pi : atom -> atom) (T : typ) : typ :=
  match T with
  | typ_nat => typ_nat | typ_top => typ_top | typ_bvar j => typ_bvar j
  | typ_fvar X => typ_fvar (pi X)
  | typ_arrow A B => typ_arrow (ren pi A) (ren pi B)
  | typ_all A B => typ_all (ren pi A) (ren pi B)
  | typ_mu A => typ_mu (ren pi A)
  | typ_label l A => typ_label (pi l) (ren pi A)
  | typ_rcd_nil => typ_rcd_nil
  | typ_rcd_cons i A B => typ_rcd_cons (pi i) (ren pi A) (ren pi B)
  end.

Lemma ren_invol : forall x y T, ren (swp x y) (ren (swp x y) T) = T.
Proof.
  intros x y T; induction T; simpl; try reflexivity; try (f_equal; auto);
    try (erewrite swp_invol; auto); try (f_equal; auto).
Qed.

Lemma ren_fix : forall pi T,
  (forall X, X \in fv_tt T -> pi X = X) ->
  (forall l, l \in fl_tt T -> pi l = l) ->
  ren pi T = T.
Proof.
  intros pi T; induction T; simpl; intros Hf Hl; try reflexivity.
  - (* fvar *) f_equal; apply Hf; simpl; fsetdec.
  - (* arrow *) f_equal.
    + apply IHT1; [intros Z HZ; apply Hf; simpl; fsetdec | intros l Hl'; apply Hl; simpl; fsetdec].
    + apply IHT2; [intros Z HZ; apply Hf; simpl; fsetdec | intros l Hl'; apply Hl; simpl; fsetdec].
  - (* all *) f_equal.
    + apply IHT1; [intros Z HZ; apply Hf; simpl; fsetdec | intros l Hl'; apply Hl; simpl; fsetdec].
    + apply IHT2; [intros Z HZ; apply Hf; simpl; fsetdec | intros l Hl'; apply Hl; simpl; fsetdec].
  - (* mu *) f_equal.
    apply IHT; [intros Z HZ; apply Hf; simpl; fsetdec | intros l Hl'; apply Hl; simpl; fsetdec].
  - (* label *) f_equal.
    + apply Hl; simpl; fsetdec.
    + apply IHT; [intros Z HZ; apply Hf; simpl; fsetdec | intros l Hl'; apply Hl; simpl; fsetdec].
  - (* rcd_cons *) f_equal.
    + apply Hl; simpl; fsetdec.
    + apply IHT1; [intros Z HZ; apply Hf; simpl; fsetdec | intros l Hl'; apply Hl; simpl; fsetdec].
    + apply IHT2; [intros Z HZ; apply Hf; simpl; fsetdec | intros l Hl'; apply Hl; simpl; fsetdec].
Qed.

Lemma ren_swap_fixes : forall x y T,
  x \notin fv_tt T -> y \notin fv_tt T -> x \notin fl_tt T -> y \notin fl_tt T ->
  ren (swp x y) T = T.
Proof.
  intros x y T Hfx Hfy Hgx Hgy. apply ren_fix.
  - intros X HX. assert (X <> x) by (intro E; subst; apply Hfx; auto).
    assert (X <> y) by (intro E; subst; apply Hfy; auto).
    apply swp_other; auto.
  - intros l Hl. assert (l <> x) by (intro E; subst; apply Hgx; auto).
    assert (l <> y) by (intro E; subst; apply Hgy; auto).
    apply swp_other; auto.
Qed.

(* commutation of renaming with opening *)
Lemma ren_open_gen : forall pi T,
  (forall K U, ren pi (open_tt_rec K U T) = open_tt_rec K (ren pi U) (ren pi T)).
Proof.
  intros pi T; induction T; intros K U; try reflexivity.
  - (* bvar *) simpl. destruct (K === n); simpl; auto.
  - (* arrow *) simpl. f_equal; [apply IHT1 | apply IHT2].
  - (* all *) simpl. f_equal; [apply IHT1 | apply IHT2].
  - (* mu *) simpl. f_equal; apply IHT.
  - (* label *) simpl. f_equal; apply IHT.
  - (* rcd_cons *) simpl. f_equal; [apply IHT1 | apply IHT2].
Qed.

Lemma ren_open : forall pi T U,
  ren pi (open_tt T U) = open_tt (ren pi T) (ren pi U).
Proof. intros; unfold open_tt; apply ren_open_gen. Qed.

(* ---------- renaming environments ---------- *)
Definition ren_b (pi : atom -> atom) (b : binding) : binding :=
  match b with
  | bind_sub T => bind_sub (ren pi T)
  | bind_typ T => bind_typ (ren pi T)
  end.

Definition ren_env (pi : atom -> atom) (E : env) : env :=
  List.map (fun p => match p with (x, b) => (pi x, ren_b pi b) end) E.

Lemma ren_env_cons : forall pi y c E,
  ren_env pi (y ~ c ++ E) = (pi y, ren_b pi c) :: ren_env pi E.
Proof. intros; simpl; auto. Qed.

Lemma ren_b_invol : forall x y b, ren_b (swp x y) (ren_b (swp x y) b) = b.
Proof. intros x y [T|T]; simpl; f_equal; apply ren_invol. Qed.

Lemma ren_env_invol : forall x y E, ren_env (swp x y) (ren_env (swp x y) E) = E.
Proof.
  intros x y E. induction E as [|[y0 c] E']; simpl; auto.
  f_equal.
  - apply pair_equal_spec; split; [apply swp_invol | apply ren_b_invol].
  - auto.
Qed.

Lemma binds_ren_fwd : forall pi X b E,
  binds X b E -> binds (pi X) (ren_b pi b) (ren_env pi E).
Proof.
  intros pi X b E H. induction E as [|[y c] E']; simpl in *; auto.
  destruct H as [Heq|Hin]; [left | right].
  - inversion Heq; subst; auto.
  - apply IHE'; auto.
Qed.

Lemma binds_ren_bwd : forall pi (Hpi : forall z, pi (pi z) = z)
  (Hb : forall b, ren_b pi (ren_b pi b) = b) X b E,
  binds (pi X) (ren_b pi b) (ren_env pi E) -> binds X b E.
Proof.
  intros pi Hpi Hb X b E. induction E as [|[y0 c] E']; simpl; auto.
  intros [Heq|Hin].
  - apply pair_equal_spec in Heq. destruct Heq as [H1 H2].
    left. apply pair_equal_spec. split.
    + apply (f_equal pi) in H1. rewrite !Hpi in H1. auto.
    + apply (f_equal (ren_b pi)) in H2. rewrite !Hb in H2. auto.
  - right. apply IHE'. auto.
Qed.

Lemma ren_b_invol_swp : forall x y b, ren_b (swp x y) (ren_b (swp x y) b) = b.
Proof. intros; apply ren_b_invol. Qed.

(* ---------- helpers for atom sets ---------- *)
Lemma in_add_iff : forall (s : atoms) x y, y \in AtomSetImpl.add x s <-> y = x \/ y \in s.
Proof.
  intros s x y. split.
  - intros H. destruct (KeySetFacts.eq_dec y x) as [e|ne].
    + left; auto.
    + right. revert H. apply AtomSetImpl.add_3; auto.
  - intros [->|H]; [apply AtomSetImpl.add_1; auto | apply AtomSetImpl.add_2; auto].
Qed.

Lemma in_dom_ren : forall pi E X,
  X \in dom (ren_env pi E) <-> (exists Y, Y \in dom E /\ pi Y = X).
Proof.
  intros pi E X. induction E as [|[y c] E']; simpl.
  - split; [fsetdec|]. intros [? [? ?]]; fsetdec.
  - rewrite in_add_iff, IHE'. split.
    + intros [->|[Y [HY HP]]].
      * exists y; split; [apply in_add_iff; left; auto | auto].
      * exists Y; split; [apply in_add_iff; right; auto | auto].
    + intros [Y [HY HP]]. apply in_add_iff in HY. destruct HY as [->|HY].
      * left. auto.
      * right. exists Y; auto.
Qed.

Lemma notin_dom_ren : forall x y E X,
  X \notin dom E -> swp x y X \notin dom (ren_env (swp x y) E).
Proof.
  intros x y E X Hx Hin. apply in_dom_ren in Hin.
  destruct Hin as [Y [HY HP]].
  assert (Y = X) by (apply (f_equal (swp x y)) in HP; rewrite !swp_invol in HP; auto).
  subst; auto.
Qed.

Lemma notin_add_1' : forall (s : atoms) x y, y \notin AtomSetImpl.add x s -> y <> x.
Proof. intros s x y H e. apply H. rewrite e. apply AtomSetImpl.add_1; auto. Qed.
Lemma notin_add_2' : forall (s : atoms) x y, y \notin AtomSetImpl.add x s -> y \notin s.
Proof. intros s x y H H2. apply H. apply AtomSetImpl.add_2; auto. Qed.

Lemma rt_type_ren : forall pi T, rt_type T -> rt_type (ren pi T).
Proof. intros pi T H. destruct H; simpl; constructor. Qed.

Lemma in_union_iff : forall (s t : atoms) x,
  x \in AtomSetImpl.union s t <-> x \in s \/ x \in t.
Proof. intros; split; intros; fsetdec. Qed.
Lemma in_singleton_iff : forall x y,
  x \in AtomSetImpl.singleton y <-> x = y.
Proof. intros; split; intros; fsetdec. Qed.

Lemma collectLabel_ren : forall pi T l,
  l \in collectLabel (ren pi T) <-> (exists l', l' \in collectLabel T /\ pi l' = l).
Proof.
  intros pi T. induction T; intros l; cbn [ren collectLabel];
    try (split; [intros H; fsetdec | intros [? [? ?]]; fsetdec]).
  (* rcd_cons *)
  rewrite in_union_iff, in_singleton_iff, IHT2. split.
  + intros [->|[l' [Hl' HP]]].
    * exists a; split; [rewrite in_union_iff; left; rewrite in_singleton_iff; auto | auto].
    * exists l'; split; [rewrite in_union_iff; right; auto | auto].
  + intros [l' [Hl' HP]]. rewrite in_union_iff in Hl'. destruct Hl' as [Hl'|Hl'].
    * rewrite in_singleton_iff in Hl'. subst. left. auto.
    * right. exists l'; auto.
Qed.

Lemma collectLabel_notin_ren : forall x y T i,
  i \notin collectLabel T -> swp x y i \notin collectLabel (ren (swp x y) T).
Proof.
  intros x y T i Hi Hc. apply collectLabel_ren in Hc.
  destruct Hc as [l' [Hl' Heq]].
  assert (l' = i) by (apply (f_equal (swp x y)) in Heq; rewrite !swp_invol in Heq; auto).
  subst; auto.
Qed.

(* ---------- equivariance of WF under swapping ---------- *)
Lemma WF_ren_fwd : forall x y E T,
  WF E T -> WF (ren_env (swp x y) E) (ren (swp x y) T).
Proof.
  intros x y E T H.
  induction H as [E | E | U E X Hb | E A B HA IHA HB IHB
    | L E T1 T2 HT1 IHT1 Hall IHall | L E A H1 IH1 H2 IH2
    | E A X HA IHA | E | E i T1 T2 H1 IH1 H2 IH2 Hrt Hi].
  - simpl; apply WF_top.
  - simpl; apply WF_nat.
  - simpl. eapply WF_var. eapply binds_ren_fwd with (b := bind_sub U). auto.
  - simpl. apply WF_arrow; auto.
  - (* all *) simpl. eapply WF_all with (L := AtomSetImpl.add x (AtomSetImpl.add y L)).
    + apply IHT1.
    + intros Y HY.
      assert (Hy' : Y \notin AtomSetImpl.add y L)
        by (intro Hc; apply HY; apply AtomSetImpl.add_2; auto).
      assert (Yx : Y <> x) by (intro e; apply HY; rewrite <- e; apply AtomSetImpl.add_1; auto).
      assert (Yy : Y <> y) by (intro e; apply Hy'; rewrite <- e; apply AtomSetImpl.add_1; auto).
      assert (HL : Y \notin L) by (intro Hc; apply Hy'; apply AtomSetImpl.add_2; auto).
      assert (Heq : swp x y Y = Y) by (apply (@swp_other x y Y Yx Yy)).
      specialize (IHall Y HL).
      rewrite ren_open in IHall. cbn [ren] in IHall.
      rewrite ren_env_cons in IHall. rewrite Heq in IHall.
      exact IHall.
  - (* rec *) simpl. eapply WF_rec with (L := AtomSetImpl.add x (AtomSetImpl.add y L)).
    + intros Y HY.
      assert (Hy' : Y \notin AtomSetImpl.add y L)
        by (intro Hc; apply HY; apply AtomSetImpl.add_2; auto).
      assert (Yx : Y <> x) by (intro e; apply HY; rewrite <- e; apply AtomSetImpl.add_1; auto).
      assert (Yy : Y <> y) by (intro e; apply Hy'; rewrite <- e; apply AtomSetImpl.add_1; auto).
      assert (HL : Y \notin L) by (intro Hc; apply Hy'; apply AtomSetImpl.add_2; auto).
      assert (Heq : swp x y Y = Y) by (apply (@swp_other x y Y Yx Yy)).
      specialize (IH1 Y HL). rewrite ren_open in IH1. cbn [ren] in IH1.
      rewrite ren_env_cons in IH1. rewrite Heq in IH1.
      exact IH1.
    + intros Y HY.
      assert (Hy' : Y \notin AtomSetImpl.add y L)
        by (intro Hc; apply HY; apply AtomSetImpl.add_2; auto).
      assert (Yx : Y <> x) by (intro e; apply HY; rewrite <- e; apply AtomSetImpl.add_1; auto).
      assert (Yy : Y <> y) by (intro e; apply Hy'; rewrite <- e; apply AtomSetImpl.add_1; auto).
      assert (HL : Y \notin L) by (intro Hc; apply Hy'; apply AtomSetImpl.add_2; auto).
      assert (Heq : swp x y Y = Y) by (apply (@swp_other x y Y Yx Yy)).
      specialize (IH2 Y HL).
      rewrite ren_open in IH2. cbn [ren] in IH2.
      rewrite ren_open in IH2. cbn [ren] in IH2.
      rewrite ren_env_cons in IH2. rewrite !Heq in IH2.
      exact IH2.
  - (* label *) simpl. apply WF_label; auto.
  - (* rcd_nil *) simpl; apply WF_rcd_nil.
  - (* rcd_cons *) simpl. eapply WF_rcd_cons.
    + apply IH1.
    + apply IH2.
    + apply rt_type_ren; auto.
    + apply collectLabel_notin_ren; auto.
Qed.
Lemma WF_ren_bwd : forall x y E T,
  WF (ren_env (swp x y) E) (ren (swp x y) T) -> WF E T.
Proof.
  intros x y E T H.
  pose proof (@WF_ren_fwd x y (ren_env (swp x y) E) (ren (swp x y) T) H) as H2.
  rewrite ren_env_invol in H2. rewrite ren_invol in H2. exact H2.
Qed.


(* ---------- equivariance of wf_env ---------- *)
Lemma wf_env_ren_fwd : forall x y E, wf_env E -> wf_env (ren_env (swp x y) E).
Proof.
  intros x y E H. induction H as [| E X T Hwf IH HWF Hnotin | E X T Hwf IH HWF Hnotin].
  - simpl. constructor.
  - rewrite ren_env_cons. eapply wf_env_sub.
    + apply IH.
    + apply WF_ren_fwd. auto.
    + apply notin_dom_ren. auto.
  - rewrite ren_env_cons. eapply wf_env_typ.
    + apply IH.
    + apply WF_ren_fwd. auto.
    + apply notin_dom_ren. auto.
Qed.
Lemma wf_env_ren_bwd : forall x y E,
  wf_env (ren_env (swp x y) E) -> wf_env E.
Proof.
  intros x y E H.
  pose proof (@wf_env_ren_fwd x y (ren_env (swp x y) E) H) as H2.
  rewrite ren_env_invol in H2. exact H2.
Qed.


Lemma swp_eq_iff : forall x y a b, swp x y a = swp x y b <-> a = b.
Proof.
  intros; split; intro e.
  - apply (f_equal (swp x y)) in e. rewrite !swp_invol in e. auto.
  - subst; auto.
Qed.

Lemma Tlookup_ren : forall x y i T,
  Tlookup (swp x y i) (ren (swp x y) T) = option_map (ren (swp x y)) (Tlookup i T).
Proof.
  intros x y i T. induction T; simpl; try reflexivity.
  (* rcd_cons *) destruct (a == i) as [e|ne].
  - subst i.
    destruct ((swp x y a) == (swp x y a)) as [e2|n2]; [|exfalso; auto].
    destruct (a == a) as [e1|n1]; [|exfalso; auto].
    simpl. reflexivity.
  - destruct ((swp x y a) == (swp x y i)) as [e2|n2].
    + exfalso. apply ne. exact (proj1 (@swp_eq_iff x y a i) e2).
    + simpl. apply IHT2.
Qed.

Lemma collectLabel_ren_subset : forall x y T1 T2,
  collectLabel T2 [<=] collectLabel T1 ->
  collectLabel (ren (swp x y) T2) [<=] collectLabel (ren (swp x y) T1).
Proof.
  intros x y T1 T2 H l Hl. apply collectLabel_ren in Hl.
  destruct Hl as [l' [Hl' HP]]. apply collectLabel_ren.
  exists l'; split; auto.
Qed.

Lemma fresh_add_extract : forall x y L Y,
  Y \notin AtomSetImpl.add x (AtomSetImpl.add y L) ->
  Y <> x /\ Y <> y /\ Y \notin L /\ swp x y Y = Y.
Proof.
  intros x y L Y H. split; [|split; [|split]].
  - intro e. apply H. rewrite <- e. apply AtomSetImpl.add_1; auto.
  - assert (Hy : Y \notin AtomSetImpl.add y L)
      by (intro Hc; apply H; apply AtomSetImpl.add_2; auto).
    intro e. apply Hy. rewrite <- e. apply AtomSetImpl.add_1; auto.
  - assert (Hy : Y \notin AtomSetImpl.add y L)
      by (intro Hc; apply H; apply AtomSetImpl.add_2; auto).
    intro Hc. apply Hy. apply AtomSetImpl.add_2; auto.
  - apply (@swp_other x y Y); auto.
Qed.

Lemma option_map_some_inv : forall (f : typ -> typ) o t,
  option_map f o = Some t -> exists s, o = Some s /\ f s = t.
Proof.
  intros f o t H. destruct o as [s|]; simpl in *.
  - exists s; split; auto. injection H as H; auto.
  - discriminate H.
Qed.

Lemma sub_ren_fwd : forall x y E A B,
  sub E A B -> sub (ren_env (swp x y) E) (ren (swp x y) A) (ren (swp x y) B).
Proof.
  intros x y E A B H.
  induction H as [E Hwf | E X Hwf HWF | E A Hwf HWF | U E T X Hb Hsub IHsub
    | E A1 A2 B1 B2 H12 IH12 H34 IH34
    | L E S1 S2 T1 T2 H12 IH12 H21 IH21 Hall IHall
    | L A1 A2 E Hwf1 Hwf2 Hsub IHallsub
    | E X A B Hsub IHsub
    | A1 A2 E Hwf Hrt1 Hrt2 HsubL HWF1 HWF2 Hlook IHlook].
  - simpl. apply sa_nat. apply wf_env_ren_fwd. auto.
  - simpl. apply sa_fvar. apply wf_env_ren_fwd; auto.
    exact (@WF_ren_fwd x y E (typ_fvar X) HWF).
  - simpl. apply sa_top. apply wf_env_ren_fwd; auto.
    exact (@WF_ren_fwd x y E A HWF).
  - simpl. eapply sa_trans_tvar.
    + eapply binds_ren_fwd with (b := bind_sub U); auto.
    + apply IHsub.
  - simpl. apply sa_arrow; auto.
  - simpl. eapply sa_all with (L := AtomSetImpl.add x (AtomSetImpl.add y L)).
    + apply IH12.
    + apply IH21.
    + intros Y HY. destruct (fresh_add_extract HY) as [Yx [Yy [HL Heq]]].
      specialize (IHall Y HL).
      rewrite !ren_open in IHall. cbn [ren] in IHall.
      rewrite ren_env_cons in IHall. rewrite Heq in IHall.
      exact IHall.
  - simpl. eapply sa_rec with (L := AtomSetImpl.add x (AtomSetImpl.add y L)).
    + intros Y HY. destruct (fresh_add_extract HY) as [Yx [Yy [HL Heq]]].
      specialize (Hwf1 Y HL).
      pose proof (@WF_ren_fwd x y (Y ~ bind_sub typ_top ++ E) (open_tt A1 Y) Hwf1) as H.
      rewrite !ren_open in H. cbn [ren] in H.
      rewrite ren_env_cons in H. rewrite Heq in H.
      exact H.
    + intros Y HY. destruct (fresh_add_extract HY) as [Yx [Yy [HL Heq]]].
      specialize (Hwf2 Y HL).
      pose proof (@WF_ren_fwd x y (Y ~ bind_sub typ_top ++ E) (open_tt A2 Y) Hwf2) as H.
      rewrite !ren_open in H. cbn [ren] in H.
      rewrite ren_env_cons in H. rewrite Heq in H.
      exact H.
    + intros Y HY. destruct (fresh_add_extract HY) as [Yx [Yy [HL Heq]]].
      specialize (IHallsub Y HL).
      rewrite !ren_open in IHallsub. cbn [ren] in IHallsub.
      rewrite !ren_open in IHallsub. cbn [ren] in IHallsub.
      rewrite ren_env_cons in IHallsub. rewrite !Heq in IHallsub.
      exact IHallsub.
  - simpl. apply sa_label; auto.
  - simpl. eapply sa_rcd.
    + apply wf_env_ren_fwd; auto.
    + apply rt_type_ren; auto.
    + apply rt_type_ren; auto.
    + apply collectLabel_ren_subset; auto.
    + exact (@WF_ren_fwd x y E A1 HWF1).
    + exact (@WF_ren_fwd x y E A2 HWF2).
    + intros i' t1' t2' H1 H2.
      assert (H1eq : option_map (ren (swp x y)) (Tlookup (swp x y i') A1) = Some t1').
      { rewrite <- Tlookup_ren. rewrite swp_invol. exact H1. }
      assert (H2eq : option_map (ren (swp x y)) (Tlookup (swp x y i') A2) = Some t2').
      { rewrite <- Tlookup_ren. rewrite swp_invol. exact H2. }
      destruct (@option_map_some_inv (ren (swp x y)) (Tlookup (swp x y i') A1) t1' H1eq) as [s1 [Hs1 Hr1]].
      destruct (@option_map_some_inv (ren (swp x y)) (Tlookup (swp x y i') A2) t2' H2eq) as [s2 [Hs2 Hr2]].
      specialize (IHlook (swp x y i') s1 s2 Hs1 Hs2).
      rewrite Hr1, Hr2 in IHlook. exact IHlook.
Qed.

(* backward direction via involution *)
Lemma sub_ren_bwd : forall x y E A B,
  sub (ren_env (swp x y) E) (ren (swp x y) A) (ren (swp x y) B) -> sub E A B.
Proof.
  intros x y E A B H.
  pose proof (@sub_ren_fwd x y (ren_env (swp x y) E) (ren (swp x y) A) (ren (swp x y) B) H) as H2.
  rewrite ren_env_invol in H2. rewrite ren_invol in H2. rewrite ren_invol in H2.
  exact H2.
Qed.






(* ===== Fresh canonical atoms ===== *)

Definition fresh_atom (S : atoms) : atom := Atom.fresh (AtomSetImpl.elements S).

Lemma fresh_atom_notin : forall S, fresh_atom S \notin S.
Proof.
  intros S Hmem.
  unfold fresh_atom in Hmem.
  apply AtomSetImpl.elements_1 in Hmem.
  apply InA_alt in Hmem. destruct Hmem as [y [Heq Hin]].
  apply Atom.fresh_not_in with (l := AtomSetImpl.elements S).
  subst y. exact Hin.
Qed.

Lemma wf_env_tail_sub : forall E X T,
  wf_env (X ~ bind_sub T ++ E) -> wf_env E.
Proof.
  intros E X T H.
  inversion H as [| E0 Y T0 Hwf HWF Hnot | E0 y T0 Hwf HWF Hnot]; subst; auto.
Qed.

Lemma wf_env_tail_typ : forall E x T,
  wf_env (x ~ bind_typ T ++ E) -> wf_env E.
Proof.
  intros E x T H.
  inversion H as [| E0 Y T0 Hwf HWF Hnot | E0 y T0 Hwf HWF Hnot]; subst; auto.
Qed.

(* Every sub derivation lives in a well-formed environment.  The only
   non-structural premise is sa_rec's; there the third premise at any fresh
   atom is a sub derivation, and inverting the environment extension yields
   wf_env E. *)
Lemma sub_wf_env : forall E A B, sub E A B -> wf_env E.
Proof.
  intros E A B H.
  induction H as [E Hwf | E X Hwf HWF | E A Hwf HWF | U E T X Hb Hsub IHsub
    | E A1 A2 B1 B2 H12 IH12 H34 IH34
    | L E S1 S2 T1 T2 H12 IH12 H21 IH21 Hall IHall
    | L A1 A2 E Hwf1 Hwf2 Hsub IHallsub
    | E X A B Hsub IHsub
    | A1 A2 E Hwf Hrt1 Hrt2 HsubL HWF1 HWF2 Hlook IHlook].
  - exact Hwf.
  - exact Hwf.
  - exact Hwf.
  - exact IHsub.
  - exact IH12.
  - exact IH12.
  - assert (Hf : fresh_atom L \notin L) by apply fresh_atom_notin.
    pose proof (IHallsub (fresh_atom L) Hf) as Hwe.
    apply wf_env_tail_sub in Hwe. exact Hwe.
  - exact IHsub.
  - exact Hwf.
Qed.



(* ===== De Bruijn closure, for opening inertness ===== *)

Fixpoint bvclosed (d : nat) (T : typ) : Prop :=
  match T with
  | typ_nat => True
  | typ_top => True
  | typ_bvar J => J < d
  | typ_fvar _ => True
  | typ_arrow A B => bvclosed d A /\ bvclosed d B
  | typ_all A B => bvclosed d A /\ bvclosed (S d) B
  | typ_mu A => bvclosed (S d) A
  | typ_label _ A => bvclosed d A
  | typ_rcd_nil => True
  | typ_rcd_cons _ A B => bvclosed d A /\ bvclosed d B
  end.

Lemma bvclosed_open_inert : forall T d K U,
  bvclosed d T -> d <= K -> open_tt_rec K U T = T.
Proof.
  intros T. induction T as [| | n | a | A IHA B IHB | A IHA B IHB | A IHA | l A IHA | | i A IHA B IHB];
    simpl; intros d K U H HK; auto.
  - (* bvar *) destruct (K === n) as [e|ne]; simpl.
    + exfalso; lia.
    + reflexivity.
  - (* arrow *) destruct H as [HA HB]. rewrite (IHA d K U HA HK), (IHB d K U HB HK); auto.
  - (* all *) destruct H as [HA HB]. assert (HSK : S d <= S K) by lia.
    rewrite (IHA d K U HA HK), (IHB (S d) (S K) U HB HSK); auto.
  - (* mu *) assert (HSK : S d <= S K) by lia.
    rewrite (IHA (S d) (S K) U H HSK); auto.
  - (* label *) rewrite (IHA d K U H HK); auto.
  - (* rcd_cons *) destruct H as [HA HB]. rewrite (IHA d K U HA HK), (IHB d K U HB HK); auto.
Qed.


Lemma bvclosed_open_pre : forall T d K X,
  bvclosed d (open_tt_rec K X T) -> K <= d -> bvclosed (S d) T.
Proof.
  intros T. induction T as [| | n | a | A IHA B IHB | A IHA B IHB | A IHA | l A IHA | | i A IHA B IHB];
    simpl; intros d K X H HK.
  - (* nat *) exact I.
  - (* top *) exact I.
  - (* bvar *) destruct (K === n) as [e|ne]; simpl in *.
    + subst n. lia.
    + lia.
  - (* fvar *) exact I.
  - (* arrow *) destruct H as [HA HB]. split; [apply (IHA d K X HA HK)|apply (IHB d K X HB HK)].
  - (* all *) destruct H as [HA HB]. split.
    + apply (IHA d K X HA HK).
    + apply (IHB (S d) (S K) X HB). lia.
  - (* mu *) apply (IHA (S d) (S K) X H). lia.
  - (* label *) apply (IHA d K X H HK).
  - (* rcd_nil *) exact I.
  - (* rcd_cons *) destruct H as [HA HB]. split;
      [apply (IHA d K X HA HK)|apply (IHB d K X HB HK)].
Qed.

Lemma WF_bvclosed : forall E T, WF E T -> bvclosed 0 T.
Proof.
  intros E T H. induction H as [E | E | U E X Hb | E A B HA IHA HB IHB
    | L E T1 T2 H1 IH1 Hbody IHbody
    | L E A Hplain IHplain Hlabel IHlabel
    | E A X HA IHA | E | E i T1 T2 H1 IH1 H2 IH2 Hrt Hnot].
  - exact I.
  - exact I.
  - simpl; auto.
  - simpl. split; auto.
  - simpl. split; auto.
    assert (Hf : fresh_atom L \notin L) by apply fresh_atom_notin.
    apply (@bvclosed_open_pre T2 0 0 (fresh_atom L) (IHbody (fresh_atom L) Hf)). lia.
  - simpl.
    assert (Hf : fresh_atom L \notin L) by apply fresh_atom_notin.
    apply (@bvclosed_open_pre A 0 0 (fresh_atom L) (IHplain (fresh_atom L) Hf)). lia.
  - simpl; auto.
  - exact I.
  - simpl. split; auto.
Qed.


Lemma WF_open_inert : forall E T, WF E T -> forall K U, open_tt_rec K U T = T.
Proof.
  intros E T H K U.
  apply (@bvclosed_open_inert T 0 K U).
  - exact (@WF_bvclosed E T H).
  - lia.
Qed.

Lemma subst_open_closed : forall E S, WF E S ->
  forall X T K Y,
    subst_tt X S (open_tt_rec K Y T) =
    open_tt_rec K (subst_tt X S Y) (subst_tt X S T).
Proof.
  intros E S HS X T. induction T as [| | n | a | A IHA B IHB | A IHA B IHB | A IHA | l A IHA | | i A IHA B IHB];
    simpl; intros K Y.
  - (* nat *) reflexivity.
  - (* top *) reflexivity.
  - (* bvar *) destruct (K === n) as [e|ne]; simpl.
    + destruct (X == X) as [e2|ne2]; [reflexivity|exfalso; auto].
    + reflexivity.
  - (* fvar *) destruct (a == X) as [e|ne]; simpl.
    + subst a. rewrite (@WF_open_inert E S HS K (subst_tt X S Y)). reflexivity.
    + reflexivity.
  - (* arrow *) rewrite IHA, IHB; reflexivity.
  - (* all *) rewrite IHA, IHB; reflexivity.
  - (* mu *) rewrite IHA; reflexivity.
  - (* label *) rewrite IHA; reflexivity.
  - (* rcd_nil *) reflexivity.
  - (* rcd_cons *) rewrite IHA, IHB; reflexivity.
Qed.

Lemma subst_open_self_rec : forall X S T,
  X \notin fv_tt T -> forall K,
    subst_tt X S (open_tt_rec K X T) = open_tt_rec K S T.
Proof.
  intros X S T. induction T as [| | n | a | A IHA B IHB | A IHA B IHB | A IHA | l A IHA | | i A IHA B IHB];
    simpl; intros H K.
  - (* nat *) reflexivity.
  - (* top *) reflexivity.
  - (* bvar *) destruct (K === n) as [e|ne]; simpl.
    + destruct (X == X) as [e2|ne2]; [reflexivity|exfalso; auto].
    + reflexivity.
  - (* fvar *) assert (a <> X) by (intro e; subst a; apply H; fsetdec).
    destruct (a == X) as [e|ne]; [exfalso; auto|reflexivity].
  - (* arrow *) assert (HA : X \notin fv_tt A) by fsetdec.
    assert (HB : X \notin fv_tt B) by fsetdec.
    simpl. f_equal; [apply IHA|apply IHB]; auto.
  - (* all *) assert (HA : X \notin fv_tt A) by fsetdec.
    assert (HB : X \notin fv_tt B) by fsetdec.
    simpl. f_equal; [apply IHA|apply IHB]; auto.
  - (* mu *) simpl. f_equal. apply IHA; auto.
  - (* label *) simpl. f_equal. apply IHA; auto.
  - (* rcd_nil *) reflexivity.
  - (* rcd_cons *) assert (HA : X \notin fv_tt A) by fsetdec.
    assert (HB : X \notin fv_tt B) by fsetdec.
    simpl. f_equal; [apply IHA|apply IHB]; auto.
Qed.

Lemma subst_open_self : forall X S T,
  X \notin fv_tt T -> subst_tt X S (open_tt T X) = open_tt T S.
Proof. intros; unfold open_tt; apply subst_open_self_rec; auto. Qed.


Lemma WF_weaken_prefix : forall E T, WF E T ->
  forall E', (forall X b, binds X b E -> binds X b E') -> WF E' T.
Proof.
  intros E T H. induction H as [E | E | U E X Hb | E A B HA IHA HB IHB
    | L E T1 T2 H1 IH1 Hbody IHbody
    | L E A Hplain IHplain Hlabel IHlabel
    | E A X HA IHA | E | E i T1 T2 H1 IH1 H2 IH2 Hrt Hnot];
    intros E' Hcond.
  - apply WF_top.
  - apply WF_nat.
  - eapply WF_var. exact (Hcond X (bind_sub U) Hb).
  - apply WF_arrow; [apply IHA|apply IHB]; auto.
  - apply WF_all with (L := L).
    + apply IH1; auto.
    + intros Y HY.
      apply (IHbody Y HY (Y ~ bind_sub T1 ++ E')).
      intros Z c HZ. simpl in HZ. destruct HZ as [Heq|Hin].
      * simpl. left; auto.
      * simpl. right. apply Hcond; auto.
  - apply WF_rec with (L := L).
    + intros Y HY.
      apply (IHplain Y HY (Y ~ bind_sub typ_top ++ E')).
      intros Z c HZ. simpl in HZ. destruct HZ as [Heq|Hin].
      * simpl. left; auto.
      * simpl. right. apply Hcond; auto.
    + intros Y HY.
      apply (IHlabel Y HY (Y ~ bind_sub typ_top ++ E')).
      intros Z c HZ. simpl in HZ. destruct HZ as [Heq|Hin].
      * simpl. left; auto.
      * simpl. right. apply Hcond; auto.
  - apply WF_label. apply IHA; auto.
  - apply WF_rcd_nil.
  - apply WF_rcd_cons; auto.
Qed.

Definition subbound (E : env) (X : atom) : Prop :=
  exists U, binds X (bind_sub U) E.

Lemma subbound_cons_iff : forall E E' Y b,
  (forall X, subbound E X <-> subbound E' X) ->
  forall X, subbound ((Y,b) :: E) X <-> subbound ((Y,b) :: E') X.
Proof.
  intros E E' Y b Hiff X. split.
  - intros [U1 Hb1]. simpl in Hb1. apply in_inv in Hb1.
    destruct Hb1 as [Heq1|Hin1].
    + inversion Heq1; subst. exists U1. simpl. left; reflexivity.
    + assert (Hsb1 : subbound E X) by (exists U1; exact Hin1).
      apply Hiff in Hsb1. destruct Hsb1 as [U1' Hin1']. exists U1'. simpl; right; auto.
  - intros [U2 Hb2]. simpl in Hb2. apply in_inv in Hb2.
    destruct Hb2 as [Heq2|Hin2].
    + inversion Heq2; subst. exists U2. simpl. left; reflexivity.
    + assert (Hsb2 : subbound E X)
        by (apply (proj2 (Hiff X)); exists U2; exact Hin2).
      destruct Hsb2 as [U2' Hin2']. exists U2'. simpl; right; auto.
Qed.

Lemma WF_subbound_congr : forall E T, WF E T ->
  forall E', (forall X, subbound E X <-> subbound E' X) -> WF E' T.
Proof.
  intros E T H. induction H as [E | E | U E X Hb | E A B HA IHA HB IHB
    | L E T1 T2 H1 IH1 Hbody IHbody
    | L E A Hplain IHplain Hlabel IHlabel
    | E A X HA IHA | E | E i T1 T2 H1 IH1 H2 IH2 Hrt Hnot];
    intros E' Hiff.
  - apply WF_top.
  - apply WF_nat.
  - assert (Hsb : subbound E X) by (exists U; auto).
    destruct (proj1 (Hiff X) Hsb) as [U' Hb'].
    eapply WF_var. exact Hb'.
  - apply WF_arrow; [apply IHA|apply IHB]; auto.
  - apply WF_all with (L := L).
    + apply IH1; auto.
    + intros Y HY.
      apply (IHbody Y HY (Y ~ bind_sub T1 ++ E')).
      apply subbound_cons_iff; auto.
  - apply WF_rec with (L := L).
    + intros Y HY.
      apply (IHplain Y HY (Y ~ bind_sub typ_top ++ E')).
      apply subbound_cons_iff; auto.
    + intros Y HY.
      apply (IHlabel Y HY (Y ~ bind_sub typ_top ++ E')).
      apply subbound_cons_iff; auto.
  - apply WF_label. apply IHA; auto.
  - apply WF_rcd_nil.
  - apply WF_rcd_cons; auto.
Qed.

Lemma subbound_head_congr : forall E X U V Y,
  subbound ((X, bind_sub U) :: E) Y <-> subbound ((X, bind_sub V) :: E) Y.
Proof.
  intros E X U V Y. split; intros [W Hb]; simpl in *.
  - destruct Hb as [Heq|Hin].
    + inversion Heq; subst. exists V. simpl; left; auto.
    + exists W. simpl; right; auto.
  - destruct Hb as [Heq|Hin].
    + inversion Heq; subst. exists U. simpl; left; auto.
    + exists W. simpl; right; auto.
Qed.

Lemma WF_bind_congr : forall E X U V T,
  WF ((X, bind_sub U) :: E) T -> WF ((X, bind_sub V) :: E) T.
Proof.
  intros E X U V T H.
  apply (WF_subbound_congr H (subbound_head_congr E X U V)).
Qed.


Lemma subst_tt_fvar_neq : forall X Y S, Y <> X -> subst_tt X S (typ_fvar Y) = typ_fvar Y.
Proof. intros. simpl. destruct (Y == X) as [e|ne]; [exfalso; auto|reflexivity]. Qed.



Lemma rt_type_subst : forall X S T, rt_type T -> rt_type (subst_tt X S T).
Proof.
  intros X S T H. inversion H; simpl; constructor.
Qed.

Lemma collectLabel_subst_rt : forall E T, WF E T -> rt_type T ->
  forall X S, collectLabel (subst_tt X S T) = collectLabel T.
Proof.
  intros E T H. induction H as [E | E | U E Y Hb | E A B HA IHA HB IHB
    | L E T1 T2 H1 IH1 Hbody IHbody
    | L E A Hplain IHplain Hlabel IHlabel
    | E A Y HA IHA | E | E i T1 T2 H1 IH1 H2 IH2 Hrt Hnot];
    intros HR X S.
  - inversion HR.
  - inversion HR.
  - inversion HR.
  - inversion HR.
  - inversion HR.
  - inversion HR.
  - inversion HR.
  - reflexivity.
  - simpl. rewrite (IH2 Hrt X S). reflexivity.
Qed.

Lemma WF_subst_tt : forall E T, WF E T ->
  forall X S, WF E S -> WF E (subst_tt X S T).
Proof.
  intros E T H. induction H as [E | E | U E Y Hb | E A B HA IHA HB IHB
    | L E T1 T2 H1 IH1 Hbody IHbody
    | L E A Hplain IHplain Hlabel IHlabel
    | E A Y HA IHA | E | E i T1 T2 H1 IH1 H2 IH2 Hrt Hnot];
    intros X S HS.
  - apply WF_top.
  - apply WF_nat.
  - simpl. destruct (Y == X) as [e|ne].
    + subst Y. exact HS.
    + eapply WF_var. simpl. exact Hb.
  - simpl. apply WF_arrow; [apply IHA|apply IHB]; auto.
  - simpl. apply WF_all with (L := AtomSetImpl.add X L).
    + apply IH1; auto.
    + intros Y HY.
      assert (HYL : Y \notin L) by fsetdec.
      assert (HYX : Y <> X) by (intro e; subst Y; apply HY; apply AtomSetImpl.add_1; auto).
      assert (HSw : WF (Y ~ bind_sub T1 ++ E) S).
      { apply (WF_weaken_prefix HS).
        intros Z c HZ. simpl. right; auto. }
      pose proof (IHbody Y HYL X S HSw) as Hsub.
      change (WF (Y ~ bind_sub T1 ++ E)
                (subst_tt X S (open_tt_rec 0 Y T2))) in Hsub.
      rewrite (@subst_open_closed (Y ~ bind_sub T1 ++ E) S HSw X T2 0 Y) in Hsub.
      rewrite (@subst_tt_fvar_neq X Y S HYX) in Hsub.
      change (WF (Y ~ bind_sub (subst_tt X S T1) ++ E)
                (open_tt (subst_tt X S T2) Y)).
      apply (@WF_bind_congr E Y T1 (subst_tt X S T1) (open_tt (subst_tt X S T2) Y)).
      change (WF (Y ~ bind_sub T1 ++ E) (open_tt (subst_tt X S T2) Y)).
      exact Hsub.
  - simpl. apply WF_rec with (L := AtomSetImpl.add X L).
    + intros Y HY.
      assert (HYL : Y \notin L) by fsetdec.
      assert (HYX : Y <> X) by (intro e; subst Y; apply HY; apply AtomSetImpl.add_1; auto).
      assert (HSw : WF (Y ~ bind_sub typ_top ++ E) S).
      { apply (WF_weaken_prefix HS). intros Z c HZ. simpl; right; auto. }
      pose proof (IHplain Y HYL X S HSw) as Hsub.
      change (WF (Y ~ bind_sub typ_top ++ E)
                (subst_tt X S (open_tt_rec 0 Y A))) in Hsub.
      rewrite (@subst_open_closed (Y ~ bind_sub typ_top ++ E) S HSw X A 0 Y) in Hsub.
      rewrite (@subst_tt_fvar_neq X Y S HYX) in Hsub.
      change (WF (Y ~ bind_sub typ_top ++ E) (open_tt (subst_tt X S A) Y)).
      exact Hsub.
    + intros Y HY.
      assert (HYL : Y \notin L) by fsetdec.
      assert (HYX : Y <> X) by (intro e; subst Y; apply HY; apply AtomSetImpl.add_1; auto).
      assert (HSw : WF (Y ~ bind_sub typ_top ++ E) S).
      { apply (WF_weaken_prefix HS). intros Z c HZ. simpl; right; auto. }
      pose proof (IHlabel Y HYL X S HSw) as Hsub.
      change (WF (Y ~ bind_sub typ_top ++ E)
                (subst_tt X S (open_tt_rec 0 (typ_label Y (open_tt A Y)) A))) in Hsub.
      rewrite (@subst_open_closed (Y ~ bind_sub typ_top ++ E) S HSw X A 0
                 (typ_label Y (open_tt A Y))) in Hsub.
      assert (Hopensub : subst_tt X S (open_tt A Y) =
                         open_tt (subst_tt X S A) Y).
      { unfold open_tt.
        rewrite (@subst_open_closed (Y ~ bind_sub typ_top ++ E) S HSw X A 0 Y).
        rewrite (@subst_tt_fvar_neq X Y S HYX). reflexivity. }
      simpl in Hsub.
      rewrite Hopensub in Hsub.
      change (WF (Y ~ bind_sub typ_top ++ E)
                (open_tt (subst_tt X S A) (typ_label Y (open_tt (subst_tt X S A) Y)))).
      exact Hsub.
  - simpl. apply WF_label. apply IHA; auto.
  - apply WF_rcd_nil.
  - simpl. apply WF_rcd_cons.
    + apply IH1; auto.
    + apply IH2; auto.
    + apply rt_type_subst; auto.
    + rewrite (@collectLabel_subst_rt E T2 H2 Hrt X S). auto.
Qed.


Lemma WF_open_label : forall E A X,
  X \notin fv_tt A ->
  WF (X ~ bind_sub typ_top ++ E) (open_tt A X) ->
  WF (X ~ bind_sub typ_top ++ E) (open_tt A (typ_label X (open_tt A X))).
Proof.
  intros E A X Hfv H.
  assert (HS : WF (X ~ bind_sub typ_top ++ E) (typ_label X (open_tt A X)))
    by (apply WF_label; auto).
  pose proof (@WF_subst_tt (X ~ bind_sub typ_top ++ E) (open_tt A X) H
                X (typ_label X (open_tt A X)) HS) as Hsub.
  rewrite (@subst_open_self X (typ_label X (open_tt A X)) A Hfv) in Hsub.
  exact Hsub.
Qed.


(* ===== Locally-closed characterisation of WF ===== *)

Fixpoint LC (d : nat) (E : env) (T : typ) : Prop :=
  match T with
  | typ_nat => True
  | typ_top => True
  | typ_bvar J => J < d
  | typ_fvar X => subbound E X
  | typ_arrow A B => LC d E A /\ LC d E B
  | typ_all A B => LC d E A /\ LC (S d) E B
  | typ_mu A => LC (S d) E A
  | typ_label _ A => LC d E A
  | typ_rcd_nil => True
  | typ_rcd_cons i A B => LC d E A /\ LC d E B /\ rt_type B /\ i \notin collectLabel B
  end.

Lemma subbound_cons_neq : forall E X U Y,
  Y <> X -> (subbound ((X, bind_sub U) :: E) Y <-> subbound E Y).
Proof.
  intros E X U Y Hne. split; intros [V HV].
  - simpl in HV. apply in_inv in HV. destruct HV as [Heq|Hin].
    + inversion Heq; subst. exfalso; auto.
    + exists V; auto.
  - exists V. simpl. right; auto.
Qed.

Lemma rt_type_open_fvar : forall T K (X:atom),
  rt_type (open_tt_rec K X T) <-> rt_type T.
Proof.
  intros T. induction T as [| | n | a | A IHA B IHB | A IHA B IHB | A IHA | l A IHA | | i A IHA B IHB];
    simpl; intros K X.
  - split; intro H; inversion H.
  - split; intro H; inversion H.
  - change (rt_type (if K === n then typ_fvar X else typ_bvar n) <->
            rt_type (typ_bvar n)).
    destruct (K === n) as [e|ne]; simpl; split; intro H; inversion H.
  - split; intro H; inversion H.
  - split; intro H; inversion H.
  - split; intro H; inversion H.
  - split; intro H; inversion H.
  - split; intro H; inversion H.
  - split; intro H; constructor.
  - split; intro H; constructor.
Qed.

Lemma collectLabel_open_fvar : forall T K (X:atom),
  collectLabel (open_tt_rec K X T) = collectLabel T.
Proof.
  intros T. induction T as [| | n | a | A IHA B IHB | A IHA B IHB | A IHA | l A IHA | | i A IHA B IHB];
    simpl; intros K X; auto.
  - (* bvar *) change (collectLabel (if K === n then typ_fvar X else typ_bvar n) = empty).
    destruct (K === n); simpl; reflexivity.
  - (* rcd_cons *) simpl. rewrite (IHB K X). reflexivity.
Qed.


Lemma LC_open_rec : forall T,
  forall d E U (X:atom),
    (X \notin fv_tt T \/ subbound E X) ->
    (LC (S d) E T <->
     LC d (X ~ bind_sub U ++ E) (open_tt_rec d X T)).
Proof.
  intros T. induction T as [| | n | a | A IHA B IHB | A IHA B IHB | A IHA | l A IHA | | i A IHA B IHB];
    simpl; intros d E U X Hside.
  - (* nat *) tauto.
  - (* top *) tauto.
  - (* bvar *)
    change (n < S d <->
            LC d (X ~ bind_sub U ++ E)
              (if d === n then typ_fvar X else typ_bvar n)).
    destruct (d === n) as [e|ne]; simpl.
    + split; intro H.
      * unfold LC, subbound; exists U; simpl; left; reflexivity.
      * lia.
    + split; intro H; lia.
  - (* fvar *)
    destruct (a == X) as [e|ne].
    + subst a.
      assert (HsbX : subbound E X)
        by (destruct Hside as [Hnf|Hsb]; [exfalso; apply Hnf; fsetdec|auto]).
      split.
      * intro H. unfold LC, subbound. exists U; simpl; left; reflexivity.
      * intro H. exact HsbX.
    + rewrite (@subbound_cons_neq E X U a ne). tauto.
  - (* arrow *)
    assert (HsideA : X \notin fv_tt A \/ subbound E X)
      by (destruct Hside as [Hnf|Hsb]; [left; fsetdec|right; auto]).
    assert (HsideB : X \notin fv_tt B \/ subbound E X)
      by (destruct Hside as [Hnf|Hsb]; [left; fsetdec|right; auto]).
    split; intro H; destruct H as [HA HB]; split.
    + apply (proj1 (@IHA d E U X HsideA)); auto.
    + apply (proj1 (@IHB d E U X HsideB)); auto.
    + apply (proj2 (@IHA d E U X HsideA)); auto.
    + apply (proj2 (@IHB d E U X HsideB)); auto.
  - (* all *)
    assert (HsideA : X \notin fv_tt A \/ subbound E X)
      by (destruct Hside as [Hnf|Hsb]; [left; fsetdec|right; auto]).
    assert (HsideB : X \notin fv_tt B \/ subbound E X)
      by (destruct Hside as [Hnf|Hsb]; [left; fsetdec|right; auto]).
    split; intro H; destruct H as [HA HB]; split.
    + apply (proj1 (@IHA d E U X HsideA)); auto.
    + apply (proj1 (@IHB (S d) E U X HsideB)); auto.
    + apply (proj2 (@IHA d E U X HsideA)); auto.
    + apply (proj2 (@IHB (S d) E U X HsideB)); auto.
  - (* mu *)
    split; intro H.
    + apply (proj1 (@IHA (S d) E U X Hside)); auto.
    + apply (proj2 (@IHA (S d) E U X Hside)); auto.
  - (* label *)
    split; intro H.
    + apply (proj1 (@IHA d E U X Hside)); auto.
    + apply (proj2 (@IHA d E U X Hside)); auto.
  - (* rcd_nil *) tauto.
  - (* rcd_cons *)
    assert (HsideA : X \notin fv_tt A \/ subbound E X)
      by (destruct Hside as [Hnf|Hsb]; [left; fsetdec|right; auto]).
    assert (HsideB : X \notin fv_tt B \/ subbound E X)
      by (destruct Hside as [Hnf|Hsb]; [left; fsetdec|right; auto]).
    split.
    + intro H. destruct H as [HA [HB [HRT Hnot]]].
      split; [ apply (proj1 (@IHA d E U X HsideA)); auto
             | split; [ apply (proj1 (@IHB d E U X HsideB)); auto
                      | split; [ apply (proj2 (rt_type_open_fvar B d X)); auto
                               | rewrite (collectLabel_open_fvar B d X); auto ] ] ].
    + intro H. destruct H as [HA [HB [HRT Hnot]]].
      split; [ apply (proj2 (@IHA d E U X HsideA)); auto
             | split; [ apply (proj2 (@IHB d E U X HsideB)); auto
                      | split; [ apply (proj1 (rt_type_open_fvar B d X)); auto
                               | rewrite <- (collectLabel_open_fvar B d X); auto ] ] ].
Qed.

(* ===== Free variables of well-formed types ===== *)

Lemma binds_in_dom : forall (E:env) (X:atom) b, binds X b E -> X \in dom E.
Proof.
  intros E X b H. induction E as [|[Y c] E']; simpl in *.
  - destruct H.
  - destruct H as [Heq|Hin].
    + inversion Heq; subst. rewrite in_add_iff; left; auto.
    + rewrite in_add_iff; right; apply IHE'; auto.
Qed.

Lemma fv_open_keep_rec : forall T K X Z,
  Z \in fv_tt T -> Z <> X -> Z \in fv_tt (open_tt_rec K X T).
Proof.
  intros T. induction T as [| | n | a | T1 IHT1 T2 IHT2 | T1 IHT1 T2 IHT2 | T1 IHT1 | a T1 IHT1 | | i T1 IHT1 T2 IHT2]; simpl; intros K X Z HZ Hne; auto; try fsetdec.
  - (* arrow *) apply in_union_iff in HZ. destruct HZ as [HZ|HZ].
    + apply in_union_iff; left; apply IHT1; auto.
    + apply in_union_iff; right; apply IHT2; auto.
  - (* all *) apply in_union_iff in HZ. destruct HZ as [HZ|HZ].
    + apply in_union_iff; left; apply IHT1; auto.
    + apply in_union_iff; right; apply IHT2; auto.
  - (* rcd_cons *) apply in_union_iff in HZ. destruct HZ as [HZ|HZ].
    + apply in_union_iff; left; apply IHT1; auto.
    + apply in_union_iff; right; apply IHT2; auto.
Qed.

Lemma fv_open_keep : forall T X Z,
  Z \in fv_tt T -> Z <> X -> Z \in fv_tt (open_tt T X).
Proof. intros; unfold open_tt; apply fv_open_keep_rec; auto. Qed.

Lemma WF_fv_dom : forall E T, WF E T -> fv_tt T [<=] dom E.
Proof.
  intros E T H. induction H as [E | E | U E X Hb | E A B HA IHA HB IHB
    | L E T1 T2 H1 IH1 Hbody IHbody
    | L E A Hplain IHplain Hlabel IHlabel
    | E A X HA IHA | E | E i T1 T2 H1 IH1 H2 IH2 Hrt Hnot].
  - simpl. fsetdec.
  - simpl. fsetdec.
  - simpl. intro Z. rewrite in_singleton_iff. intro e; subst.
    apply binds_in_dom in Hb. auto.
  - simpl. intros Z HZ. apply in_union_iff in HZ. destruct HZ as [HZ|HZ].
    + apply IHA; auto.
    + apply IHB; auto.
  - simpl. intros Z HZ. apply in_union_iff in HZ. destruct HZ as [HZ|HZ].
    + apply IH1; auto.
    + set (X := fresh_atom (AtomSetImpl.union L
         (AtomSetImpl.union (fv_tt T2) (dom E)))).
      assert (HXall : X \notin AtomSetImpl.union L
         (AtomSetImpl.union (fv_tt T2) (dom E))) by apply fresh_atom_notin.
      assert (HXL : X \notin L) by fsetdec.
      assert (HXfv : X \notin fv_tt T2) by fsetdec.
      assert (HXdom : X \notin dom E) by fsetdec.
      assert (HZopen : Z \in fv_tt (open_tt T2 X)).
      { apply fv_open_keep; auto. intro e; subst; auto. }
      pose proof (IHbody X HXL) as Hdom.
      specialize (Hdom Z HZopen).
      simpl in Hdom. rewrite in_add_iff in Hdom.
      destruct Hdom as [e|Hd].
      * subst Z. fsetdec.
      * assumption.
  - simpl. set (X := fresh_atom (AtomSetImpl.union L
         (AtomSetImpl.union (fv_tt A) (dom E)))).
    assert (HXall : X \notin AtomSetImpl.union L
         (AtomSetImpl.union (fv_tt A) (dom E))) by apply fresh_atom_notin.
    assert (HXL : X \notin L) by fsetdec.
    assert (HXfv : X \notin fv_tt A) by fsetdec.
    assert (HXdom : X \notin dom E) by fsetdec.
    intros Z HZ.
    assert (HZopen : Z \in fv_tt (open_tt A X)).
    { apply fv_open_keep; auto. intro e; subst; auto. }
    pose proof (IHplain X HXL) as Hdom.
    specialize (Hdom Z HZopen).
    simpl in Hdom. rewrite in_add_iff in Hdom.
    destruct Hdom as [e|Hd].
    + subst Z. fsetdec.
    + assumption.
  - simpl. apply IHA.
  - simpl. fsetdec.
  - simpl. intros Z HZ. apply in_union_iff in HZ. destruct HZ as [HZ|HZ].
    + apply IH1; auto.
    + apply IH2; auto.
Qed.



(* atoms occurring anywhere in a type / environment *)
Definition allT (T : typ) : atoms :=
  AtomSetImpl.union (fv_tt T) (fl_tt T).
Definition allE (E : env) : atoms :=
  AtomSetImpl.union (dom E) (AtomSetImpl.union (fv_env E) (fl_env E)).

Lemma mem_allE_head : forall Y b E, Y \in allE ((Y,b) :: E).
Proof.
  intros. unfold allE. simpl. repeat rewrite in_union_iff.
  left. rewrite in_add_iff. left. reflexivity.
Qed.

Lemma mem_allE_tail : forall Z Y b E,
  Z \in allE E -> Z \in allE ((Y,b) :: E).
Proof.
  intros Z Y b E H. destruct b; unfold allE in *; simpl in *;
    repeat rewrite in_union_iff in *; repeat rewrite in_add_iff in *; tauto.
Qed.

Lemma swp_fix_typ : forall x y T,
  x \notin allT T -> y \notin allT T -> ren (swp x y) T = T.
Proof.
  intros x y T Hx Hy. apply ren_fix.
  - intros Z HZ. apply (@swp_other x y Z).
    + intro e. subst Z. apply Hx. unfold allT.
      rewrite in_union_iff. left; auto.
    + intro e. subst Z. apply Hy. unfold allT.
      rewrite in_union_iff. left; auto.
  - intros l Hl. apply (@swp_other x y l).
    + intro e. subst l. apply Hx. unfold allT.
      rewrite in_union_iff. right; auto.
    + intro e. subst l. apply Hy. unfold allT.
      rewrite in_union_iff. right; auto.
Qed.


Lemma notin_allT_of_allE_cons : forall x Y b E T,
  (b = bind_sub T \/ b = bind_typ T) ->
  x \notin allE ((Y,b) :: E) -> x \notin allT T.
Proof.
  intros x Y b E T [->| ->] H Hm.
  - unfold allT, allE in *. simpl in *.
    repeat rewrite in_union_iff in *. repeat rewrite in_add_iff in *. tauto.
  - unfold allT, allE in *. simpl in *.
    repeat rewrite in_union_iff in *. repeat rewrite in_add_iff in *. tauto.
Qed.

Lemma swp_fix_env : forall x y E,
  x \notin allE E -> y \notin allE E -> ren_env (swp x y) E = E.
Proof.
  intros x y E. induction E as [|[Y b] E']; simpl; intros Hx Hy.
  - auto.
  - f_equal.
    + apply pair_equal_spec; split.
      * apply (@swp_other x y Y).
        -- intro e. subst Y. apply Hx. apply mem_allE_head.
        -- intro e. subst Y. apply Hy. apply mem_allE_head.
      * destruct b; simpl; f_equal; apply swp_fix_typ.
        -- apply (@notin_allT_of_allE_cons x Y (bind_sub t) E' t (or_introl eq_refl) Hx).
        -- apply (@notin_allT_of_allE_cons y Y (bind_sub t) E' t (or_introl eq_refl) Hy).
        -- apply (@notin_allT_of_allE_cons x Y (bind_typ t) E' t (or_intror eq_refl) Hx).
        -- apply (@notin_allT_of_allE_cons y Y (bind_typ t) E' t (or_intror eq_refl) Hy).
    + apply IHE'.
      * intro Hm. apply Hx. apply (@mem_allE_tail x Y b E'). exact Hm.
      * intro Hm. apply Hy. apply (@mem_allE_tail y Y b E'). exact Hm.
Qed.

Lemma sub_all_body_generalize : forall E S2 T1 T2 (X:atom),
  X \notin allE E -> X \notin allT S2 -> X \notin allT T1 -> X \notin allT T2 ->
  sub (X ~ bind_sub S2 ++ E) (open_tt T1 X) (open_tt T2 X) ->
  forall Y,
    Y \notin AtomSetImpl.add X
      (AtomSetImpl.union (allE E)
        (AtomSetImpl.union (allT S2)
          (AtomSetImpl.union (allT T1) (allT T2)))) ->
    sub (Y ~ bind_sub S2 ++ E) (open_tt T1 Y) (open_tt T2 Y).
Proof.
  intros E S2 T1 T2 X HXE HXS2 HXT1 HXT2 Hsub Y HY.
  assert (HYX : Y <> X) by (intro e; subst Y; apply HY; apply AtomSetImpl.add_1; auto).
  assert (HYE : Y \notin allE E) by fsetdec.
  assert (HYS2 : Y \notin allT S2) by fsetdec.
  assert (HYT1 : Y \notin allT T1) by fsetdec.
  assert (HYT2 : Y \notin allT T2) by fsetdec.
  pose proof (@sub_ren_fwd X Y (X ~ bind_sub S2 ++ E)
                (open_tt T1 X) (open_tt T2 X) Hsub) as Hr.
  rewrite ren_env_cons in Hr.
  cbn [ren_b] in Hr.
  rewrite (swp_eq_l X Y) in Hr.
  rewrite (@swp_fix_env X Y E HXE HYE) in Hr.
  rewrite (@swp_fix_typ X Y S2 HXS2 HYS2) in Hr.
  rewrite !ren_open in Hr.
  cbn [ren] in Hr.
  rewrite (swp_eq_l X Y) in Hr.
  rewrite (@swp_fix_typ X Y T1 HXT1 HYT1) in Hr.
  rewrite (@swp_fix_typ X Y T2 HXT2 HYT2) in Hr.
  exact Hr.
Qed.


Lemma sub_rec_body_generalize : forall E A1 A2 (X:atom),
  X \notin allE E -> X \notin allT A1 -> X \notin allT A2 ->
  sub (X ~ bind_sub typ_top ++ E)
      (open_tt A1 (typ_label X (open_tt A1 X)))
      (open_tt A2 (typ_label X (open_tt A2 X))) ->
  forall Y,
    Y \notin AtomSetImpl.add X
      (AtomSetImpl.union (allE E)
        (AtomSetImpl.union (allT A1) (allT A2))) ->
    sub (Y ~ bind_sub typ_top ++ E)
        (open_tt A1 (typ_label Y (open_tt A1 Y)))
        (open_tt A2 (typ_label Y (open_tt A2 Y))).
Proof.
  intros E A1 A2 X HXE HXA1 HXA2 Hsub Y HY.
  assert (HYX : Y <> X) by (intro e; subst Y; apply HY; apply AtomSetImpl.add_1; auto).
  assert (HYE : Y \notin allE E) by fsetdec.
  assert (HYA1 : Y \notin allT A1) by fsetdec.
  assert (HYA2 : Y \notin allT A2) by fsetdec.
  pose proof (@sub_ren_fwd X Y (X ~ bind_sub typ_top ++ E)
                (open_tt A1 (typ_label X (open_tt A1 X)))
                (open_tt A2 (typ_label X (open_tt A2 X))) Hsub) as Hr.
  rewrite ren_env_cons in Hr.
  cbn [ren_b] in Hr.
  rewrite (swp_eq_l X Y) in Hr.
  rewrite (@swp_fix_env X Y E HXE HYE) in Hr.
  rewrite !ren_open in Hr.
  cbn [ren] in Hr.
  rewrite !ren_open in Hr.
  cbn [ren] in Hr.
  rewrite (swp_eq_l X Y) in Hr.
  rewrite (@swp_fix_typ X Y A1 HXA1 HYA1) in Hr.
  rewrite (@swp_fix_typ X Y A2 HXA2 HYA2) in Hr.
  exact Hr.
Qed.



Fixpoint binds_sub_list (E : env) (X : atom) : list typ :=
  match E with
  | nil => nil
  | (Y, bind_sub U) :: E' =>
      if X == Y then U :: binds_sub_list E' X else binds_sub_list E' X
  | (Y, bind_typ U) :: E' => binds_sub_list E' X
  end.

Lemma binds_sub_list_spec : forall E X U,
  In U (binds_sub_list E X) <-> binds X (bind_sub U) E.
Proof.
  intros E X U. induction E as [|[Y b] E'].
  - simpl. tauto.
  - destruct b; simpl.
    + destruct (X == Y) as [e|ne].
      * subst Y. split; intros H.
        -- destruct H as [Heq|Hin]; [subst U; simpl; left; reflexivity|].
           apply IHE' in Hin. simpl; right; auto.
        -- simpl in H. destruct H as [Heq|Hin].
           ++ inversion Heq; subst; left; reflexivity.
           ++ right; apply IHE'; auto.
      * split.
        -- intro H. apply IHE' in H. simpl. right; auto.
        -- intro H. simpl in H. destruct H as [Heq|Hin]; [inversion Heq; subst; exfalso; auto|].
           apply IHE'; auto.
    + split.
      * intro H. apply IHE' in H. simpl. right; auto.
      * intro H. simpl in H. destruct H as [Heq|Hin]; [inversion Heq|].
        apply IHE'; auto.
Qed.


Lemma In_elements : forall (s:atoms) (x:atom), x \in s -> In x (AtomSetImpl.elements s).
Proof.
  intros s x H. apply AtomSetImpl.elements_1 in H.
  apply InA_alt in H. destruct H as [y [Heq Hin]].
  subst y. exact Hin.
Qed.
Lemma In_elements_bwd : forall (s:atoms) (x:atom),
  In x (AtomSetImpl.elements s) -> x \in s.
Proof.
  intros s x H. apply AtomSetImpl.elements_2.
  apply InA_alt. exists x; split; auto.
Qed.


Lemma Tlookup_collect : forall i T t,
  Tlookup i T = Some t -> i \in collectLabel T.
Proof.
  intros i T. induction T; simpl; intros t H; try discriminate.
  - (* rcd_cons *) destruct (a == i) as [Heq|Hne] eqn:Eeq.
    + injection H as Ht; subst t. apply in_union_iff; left. rewrite in_singleton_iff. symmetry; exact Heq.
    + apply in_union_iff; right. apply (IHT2 t); auto.
Qed.

Lemma collect_Tlookup : forall i T,
  i \in collectLabel T -> exists t, Tlookup i T = Some t.
Proof.
  intros i T. induction T; simpl; intros H.
  - fsetdec.
  - fsetdec.
  - fsetdec.
  - fsetdec.
  - fsetdec.
  - fsetdec.
  - fsetdec.
  - fsetdec.
  - fsetdec.
  - (* rcd_cons *) apply in_union_iff in H. destruct H as [H|H].
    + rewrite in_singleton_iff in H. subst i. exists T1. simpl.
      destruct (a==a) as [e2|ne2]; [reflexivity|exfalso; auto].
    + apply IHT2 in H. destruct H as [t Ht]. simpl.
      destruct (a == i) as [e2|ne2].
      * exists T1; reflexivity.
      * exists t; auto.
Qed.

Definition lookup_check (chk : env -> typ -> typ -> bool) (E : env) (A B : typ) : bool :=
  forallb
    (fun i =>
       match Tlookup i A with
       | Some t1 =>
           match Tlookup i B with
           | Some t2 => chk E t1 t2
           | None => false
           end
       | None => true
       end)
    (AtomSetImpl.elements (collectLabel B)).

Lemma lookup_check_sound : forall chk E A B,
  lookup_check chk E A B = true ->
  forall i t1 t2, Tlookup i A = Some t1 -> Tlookup i B = Some t2 -> chk E t1 t2 = true.
Proof.
  intros chk E A B H i t1 t2 H1 H2.
  unfold lookup_check in H. rewrite forallb_forall in H.
  assert (Hin : i \in collectLabel B) by (apply (@Tlookup_collect i B t2); auto).
  assert (HinList : In i (AtomSetImpl.elements (collectLabel B))) by (apply In_elements; auto).
  specialize (H i HinList). simpl in H.
  rewrite H1, H2 in H. exact H.
Qed.

Lemma lookup_check_complete : forall chk E A B,
  (forall i t1 t2, Tlookup i A = Some t1 -> Tlookup i B = Some t2 -> chk E t1 t2 = true) ->
  lookup_check chk E A B = true.
Proof.
  intros chk E A B H. unfold lookup_check. rewrite forallb_forall.
  intros i Hin. simpl.
  destruct (Tlookup i A) as [t1|] eqn:E1; [|reflexivity].
  destruct (Tlookup i B) as [t2|] eqn:E2; [|].
  - apply (H i t1 t2); auto.
  - assert (HinL : i \in collectLabel B) by (apply In_elements_bwd; auto).
    destruct (@collect_Tlookup i B HinL) as [t Ht]. rewrite Ht in E2. discriminate.
Qed.

Fixpoint lookup_all_chk (chk : env -> typ -> typ -> bool)
    (E : env) (A Bfull Bstruct : typ) {struct Bstruct} : bool :=
  match Bstruct with
  | typ_rcd_cons i _ B2 =>
      andb
        (match Tlookup i A with
         | Some t1 =>
             match Tlookup i Bfull with
             | Some t2 => chk E t1 t2
             | None => false
             end
         | None => true
         end)
        (lookup_all_chk chk E A Bfull B2)
  | _ => true
  end.

Definition fresh3 (E : env) (A B : typ) : atom :=
  fresh_atom (AtomSetImpl.union (allE E)
    (AtomSetImpl.union (allT A) (allT B))).

Lemma fresh3_E : forall E A B, fresh3 E A B \notin allE E.
Proof.
  intros. unfold fresh3.
  pose proof (@fresh_atom_notin (AtomSetImpl.union (allE E)
    (AtomSetImpl.union (allT A) (allT B)))).
  fsetdec.
Qed.
Lemma fresh3_A : forall E A B, fresh3 E A B \notin allT A.
Proof.
  intros. unfold fresh3.
  pose proof (@fresh_atom_notin (AtomSetImpl.union (allE E)
    (AtomSetImpl.union (allT A) (allT B)))).
  fsetdec.
Qed.
Lemma fresh3_B : forall E A B, fresh3 E A B \notin allT B.
Proof.
  intros. unfold fresh3.
  pose proof (@fresh_atom_notin (AtomSetImpl.union (allE E)
    (AtomSetImpl.union (allT A) (allT B)))).
  fsetdec.
Qed.






(* ===== Termination-measure size functions ===== *)

(* size with mu penalty 2n+2; labels opaque iff their atom is in Sig *)
Fixpoint we (Sig : atoms) (T : typ) : nat :=
  match T with
  | typ_nat => 1
  | typ_top => 1
  | typ_bvar _ => 1
  | typ_fvar _ => 1
  | typ_arrow A B => 1 + we Sig A + we Sig B
  | typ_all A B => 1 + we Sig A + we Sig B
  | typ_mu A => let n := we Sig A in 8 * n + 8
  | typ_label l P => if AtomSetImpl.mem l Sig then 1 else 1 + we Sig P
  | typ_rcd_nil => 1
  | typ_rcd_cons _ A B => 1 + we Sig A + we Sig B
  end.

(* recursive expansion weight *)
Fixpoint w (Sig : atoms) (E : env) (X : atom) {struct E} : nat :=
  match E with
  | nil => 1
  | (Y, b) :: E' =>
    if X == Y then
      match b with
      | bind_sub U =>
        let fix go (l : list atom) : nat :=
            match l with
            | nil => 0
            | Z :: l' => w Sig E' Z + go l'
            end
        in we Sig U + go (AtomSetImpl.elements (fv_tt U))
      | bind_typ _ => 1
      end
    else w Sig E' X
  end.



Lemma we_pos : forall Sig T, 1 <= we Sig T.
Proof.
  intros Sig T; induction T; simpl.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - pose proof IHT; lia.
  - destruct (AtomSetImpl.mem a Sig); simpl; lia.
  - lia.
  - lia.
Qed.

Lemma we_open_leaf : forall Sig T U K,
  we Sig U = 1 -> we Sig (open_tt_rec K U T) = we Sig T.
Proof.
  intros Sig T; induction T; intros U K HU; simpl.
  - auto.
  - auto.
  - destruct (K === n); simpl; [assumption|auto].
  - auto.
  - rewrite IHT1, IHT2; auto.
  - rewrite IHT1, IHT2; auto.
  - rewrite IHT; auto.
  - destruct (AtomSetImpl.mem a Sig); simpl.
    + auto.
    + rewrite IHT; auto.
  - auto.
  - rewrite IHT1, IHT2; auto.
Qed.

Lemma we_open_fvar : forall Sig T X,
  we Sig (open_tt T (typ_fvar X)) = we Sig T.
Proof. intros; unfold open_tt; apply we_open_leaf; simpl; auto. Qed.

Lemma we_open_opaque_label : forall Sig T l P,
  AtomSetImpl.mem l Sig = true ->
  we Sig (open_tt T (typ_label l P)) = we Sig T.
Proof. intros; unfold open_tt; apply we_open_leaf; simpl; rewrite H; auto. Qed.


(* ===== Candidate obligation/credit measure for sub termination ===== *)

Fixpoint sum_env_w (Sig : atoms) (E : env) (l : list atom) : nat :=
  match l with
  | nil => 0
  | X :: l' => w Sig E X + sum_env_w Sig E l'
  end.

Definition envw (Sig : atoms) (E : env) (A B : typ) : nat :=
  sum_env_w Sig E (AtomSetImpl.elements
    (AtomSetImpl.union (fv_tt A) (fv_tt B))).

Fixpoint credits_sum (Cr : list (atom * nat)) : nat :=
  match Cr with
  | nil => 0
  | (_, c) :: Cr' => c + credits_sum Cr'
  end.

Definition M (Sig : atoms) (Cr : list (atom * nat)) (E : env) (A B : typ) : nat :=
  we Sig A + we Sig B + envw Sig E A B + credits_sum Cr.


(* ===== Size measure for LC -> WF ===== *)

Definition sz (T : typ) : nat := we AtomSetImpl.empty T.

Lemma mem_atomset_empty : forall a, AtomSetImpl.mem a AtomSetImpl.empty = false.
Proof.
  intro a. apply Bool.not_true_iff_false. intro H.
  apply (@AtomSetImpl.empty_1 a). apply AtomSetImpl.mem_2; auto.
Qed.

Lemma sz_pos : forall T, 1 <= sz T.
Proof. intro; apply we_pos. Qed.

Lemma sz_open_fvar : forall T (X:atom), sz (open_tt T X) = sz T.
Proof. intros; apply we_open_fvar. Qed.

Lemma sz_arrow_l : forall A B, sz A < sz (typ_arrow A B).
Proof. intros. unfold sz; simpl. pose proof (we_pos AtomSetImpl.empty A). lia. Qed.
Lemma sz_arrow_r : forall A B, sz B < sz (typ_arrow A B).
Proof. intros. unfold sz; simpl. pose proof (we_pos AtomSetImpl.empty B). lia. Qed.
Lemma sz_all_l : forall A B, sz A < sz (typ_all A B).
Proof. intros. unfold sz; simpl. pose proof (we_pos AtomSetImpl.empty A). lia. Qed.
Lemma sz_all_r : forall A B, sz B < sz (typ_all A B).
Proof. intros. unfold sz; simpl. pose proof (we_pos AtomSetImpl.empty B). lia. Qed.
Lemma sz_mu : forall A, sz A < sz (typ_mu A).
Proof. intros. unfold sz; simpl. pose proof (we_pos AtomSetImpl.empty A). lia. Qed.
Lemma sz_label : forall l A, sz A < sz (typ_label l A).
Proof. intros. unfold sz; simpl. rewrite mem_atomset_empty. simpl.
  pose proof (we_pos AtomSetImpl.empty A). lia. Qed.
Lemma sz_rcd_l : forall i A B, sz A < sz (typ_rcd_cons i A B).
Proof. intros. unfold sz; simpl. pose proof (we_pos AtomSetImpl.empty A). lia. Qed.
Lemma sz_rcd_r : forall i A B, sz B < sz (typ_rcd_cons i A B).
Proof. intros. unfold sz; simpl. pose proof (we_pos AtomSetImpl.empty B). lia. Qed.

Lemma WF_to_LC : forall E T, WF E T -> LC 0 E T.
Proof.
  intros E T H. induction H as [E | E | U E X Hb | E A B HA IHA HB IHB
    | L E T1 T2 H1 IH1 Hbody IHbody
    | L E A Hplain IHplain Hlabel IHlabel
    | E A X HA IHA | E | E i T1 T2 H1 IH1 H2 IH2 Hrt Hnot].
  - simpl; exact I.
  - simpl; exact I.
  - simpl. unfold subbound. exists U; auto.
  - simpl; split; auto.
  - simpl; split; auto.
    set (X := fresh_atom (AtomSetImpl.union L (fv_tt T2))).
    assert (HXall : X \notin AtomSetImpl.union L (fv_tt T2)) by (unfold X; apply fresh_atom_notin).
    assert (HXL : X \notin L) by fsetdec.
    assert (HXfv : X \notin fv_tt T2) by fsetdec.
    apply (proj2 (@LC_open_rec T2 0 E T1 X (or_introl HXfv))).
    apply IHbody; auto.
  - simpl.
    set (X := fresh_atom (AtomSetImpl.union L (fv_tt A))).
    assert (HXall : X \notin AtomSetImpl.union L (fv_tt A)) by (unfold X; apply fresh_atom_notin).
    assert (HXL : X \notin L) by fsetdec.
    assert (HXfv : X \notin fv_tt A) by fsetdec.
    apply (proj2 (@LC_open_rec A 0 E typ_top X (or_introl HXfv))).
    apply IHplain; auto.
  - simpl; auto.
  - simpl; exact I.
  - simpl; split; [auto|split; [auto|split; auto]].
Qed.


Lemma LC_to_WF_aux : forall n E T,
  sz T <= n -> LC 0 E T -> WF E T.
Proof.
  induction n as [|n IH]; intros E T Hle HLC.
  - pose proof sz_pos T. lia.
  - destruct T as [| | j | a | A B | A B | A | l A | | i A B]; simpl in HLC.
    + apply WF_nat.
    + apply WF_top.
    + (* bvar *) lia.
    + (* fvar *) unfold subbound in HLC. destruct HLC as [U Hb].
      eapply WF_var. exact Hb.
    + (* arrow *) destruct HLC as [HA HB]. apply WF_arrow.
      * apply (IH E A); [pose proof sz_arrow_l A B; lia|auto].
      * apply (IH E B); [pose proof sz_arrow_r A B; lia|auto].
    + (* all *) destruct HLC as [HA HB]. apply WF_all with (L := allT B).
      * apply (IH E A); [pose proof sz_all_l A B; lia|auto].
      * intros Y HY.
        assert (HYfv : Y \notin fv_tt B) by (unfold allT in HY; fsetdec).
        apply (IH (Y ~ bind_sub A ++ E) (open_tt B Y)).
        -- rewrite sz_open_fvar. pose proof sz_all_r A B; lia.
        -- apply (proj1 (@LC_open_rec B 0 E A Y (or_introl HYfv))). auto.
    + (* mu *) apply WF_rec with (L := allT A).
      * intros Y HY.
        assert (HYfv : Y \notin fv_tt A) by (unfold allT in HY; fsetdec).
        apply (IH (Y ~ bind_sub typ_top ++ E) (open_tt A Y)).
        -- rewrite sz_open_fvar. pose proof sz_mu A; lia.
        -- apply (proj1 (@LC_open_rec A 0 E typ_top Y (or_introl HYfv))). auto.
      * intros Y HY.
        assert (HYfv : Y \notin fv_tt A) by (unfold allT in HY; fsetdec).
        assert (Hplain : WF (Y ~ bind_sub typ_top ++ E) (open_tt A Y)).
        { apply (IH (Y ~ bind_sub typ_top ++ E) (open_tt A Y)).
          - rewrite sz_open_fvar. pose proof sz_mu A; lia.
          - apply (proj1 (@LC_open_rec A 0 E typ_top Y (or_introl HYfv))). auto. }
        apply (@WF_open_label E A Y HYfv Hplain).
    + (* label *) apply WF_label.
      apply (IH E A); [pose proof sz_label l A; lia|auto].
    + (* rcd_nil *) apply WF_rcd_nil.
    + (* rcd_cons *) destruct HLC as [HA [HB [HRT Hnot]]]. apply WF_rcd_cons.
      * apply (IH E A); [pose proof sz_rcd_l i A B; lia|auto].
      * apply (IH E B); [pose proof sz_rcd_r i A B; lia|auto].
      * auto.
      * auto.
Qed.

Lemma LC_to_WF : forall E T, LC 0 E T -> WF E T.
Proof. intros E T H. apply (@LC_to_WF_aux (sz T) E T); auto; lia. Qed.




(* ===== Boolean deciders for LC / WF / wf_env ===== *)

Fixpoint subbound_b (E : env) (X : atom) : bool :=
  match E with
  | nil => false
  | (Y, bind_sub U) :: E' => if X == Y then true else subbound_b E' X
  | (Y, bind_typ U) :: E' => subbound_b E' X
  end.

Lemma subbound_b_spec : forall E X,
  subbound_b E X = true <-> subbound E X.
Proof.
  intros E X. induction E as [|[Y b] E'].
  - simpl. split.
    + intro H; discriminate.
    + intros [U H]; simpl in H; contradiction.
  - destruct b.
    + destruct (X == Y) as [e|ne].
      * subst Y. split.
        -- intro H. exists t; simpl; left; reflexivity.
        -- intro H. cbn [subbound_b]. destruct (X == X) as [e2|ne2]; [reflexivity|exfalso; auto].
      * split.
        -- intro H. unfold subbound_b in H.
           destruct (X == Y) as [e2|ne2]; [exfalso; auto|simpl in H].
           apply IHE' in H. destruct H as [U HU].
           exists U; simpl; right; auto.
        -- intro H. unfold subbound in H. destruct H as [U HU]; simpl in HU.
           destruct HU as [Heq|Hin]; [inversion Heq; subst; exfalso; auto|].
           unfold subbound_b. destruct (X == Y) as [e2|ne2]; [exfalso; auto|].
           apply IHE'. exists U; auto.
    + split.
      * intro H. unfold subbound_b in H. simpl in H. apply IHE' in H.
        destruct H as [U HU]. exists U; simpl; right; auto.
      * intro H. unfold subbound in H. destruct H as [U HU]; simpl in HU.
        destruct HU as [Heq|Hin]; [inversion Heq|].
        unfold subbound_b. simpl. apply IHE'. exists U; auto.
Qed.

Definition rt_type_b (T : typ) : bool :=
  match T with
  | typ_rcd_nil => true
  | typ_rcd_cons _ _ _ => true
  | _ => false
  end.

Lemma rt_type_b_spec : forall T, rt_type_b T = true <-> rt_type T.
Proof.
  intros T. destruct T as [| | j | a | A B | A B | A | l A | | i A B]; simpl.
  - split; intro H; [discriminate|inversion H].
  - split; intro H; [discriminate|inversion H].
  - split; intro H; [discriminate|inversion H].
  - split; intro H; [discriminate|inversion H].
  - split; intro H; [discriminate|inversion H].
  - split; intro H; [discriminate|inversion H].
  - split; intro H; [discriminate|inversion H].
  - split; intro H; [discriminate|inversion H].
  - split; intro H; constructor.
  - split; intro H; constructor.
Qed.

Fixpoint LC_b (d : nat) (E : env) (T : typ) : bool :=
  match T with
  | typ_nat => true
  | typ_top => true
  | typ_bvar J => Nat.ltb J d
  | typ_fvar X => subbound_b E X
  | typ_arrow A B => andb (LC_b d E A) (LC_b d E B)
  | typ_all A B => andb (LC_b d E A) (LC_b (S d) E B)
  | typ_mu A => LC_b (S d) E A
  | typ_label _ A => LC_b d E A
  | typ_rcd_nil => true
  | typ_rcd_cons i A B =>
      andb (LC_b d E A)
        (andb (LC_b d E B)
          (andb (rt_type_b B) (negb (AtomSetImpl.mem i (collectLabel B)))))
  end.

Lemma LC_b_spec : forall T d E, LC_b d E T = true <-> LC d E T.
Proof.
  induction T as [| | n | a | A IHA B IHB | A IHA B IHB | A IHA | l A IHA | | i A IHA B IHB];
    simpl; intros d E.
  - tauto.
  - tauto.
  - rewrite Nat.ltb_lt. tauto.
  - apply subbound_b_spec.
  - rewrite andb_true_iff, IHA, IHB. tauto.
  - rewrite andb_true_iff, IHA, IHB. tauto.
  - apply IHA.
  - apply IHA.
  - tauto.
  - rewrite andb_true_iff, IHA, andb_true_iff, IHB, andb_true_iff, rt_type_b_spec.
    rewrite negb_true_iff.
    assert (Hm : AtomSetImpl.mem i (collectLabel B) = false <-> i \notin collectLabel B).
    { split; intro H.
      - intro Hin. apply AtomSetImpl.mem_1 in Hin. rewrite H in Hin. discriminate.
      - destruct (AtomSetImpl.mem i (collectLabel B)) eqn:Em; auto.
        exfalso. apply H. apply AtomSetImpl.mem_2; auto. }
    rewrite Hm. tauto.
Qed.

Definition WF_dec (E : env) (T : typ) : bool := LC_b 0 E T.

Lemma WF_dec_spec : forall E T, WF_dec E T = true <-> WF E T.
Proof.
  intros. unfold WF_dec. rewrite LC_b_spec. split; [apply LC_to_WF|apply WF_to_LC].
Qed.

Definition binding_ty (b : binding) : typ :=
  match b with bind_sub T => T | bind_typ T => T end.

Fixpoint wf_env_b (E : env) : bool :=
  match E with
  | nil => true
  | (X, b) :: E' =>
      andb (wf_env_b E')
        (andb (WF_dec E' (binding_ty b))
              (negb (AtomSetImpl.mem X (dom E'))))
  end.

Lemma wf_env_b_spec : forall E, wf_env_b E = true <-> wf_env E.
Proof.
  induction E as [|[X b] E']; simpl.
  - split; intro H; [constructor|reflexivity].
  - rewrite andb_true_iff, andb_true_iff, negb_true_iff, IHE'.
    assert (Hm : AtomSetImpl.mem X (dom E') = false <-> X \notin dom E').
    { split; intro H.
      - intro Hin. apply AtomSetImpl.mem_1 in Hin. rewrite H in Hin. discriminate.
      - destruct (AtomSetImpl.mem X (dom E')) eqn:Em; auto.
        exfalso. apply H. apply AtomSetImpl.mem_2; auto. }
    rewrite Hm, WF_dec_spec.
    destruct b; simpl.
    + split.
      * intros [Hwf [HWF Hnot]]. eapply wf_env_sub; eauto.
      * intro H. inversion H as [| E0 Y T Hwf HWF Hnot | E0 y T Hwf HWF Hnot]; subst.
        repeat split; auto.
    + split.
      * intros [Hwf [HWF Hnot]]. eapply wf_env_typ; eauto.
      * intro H. inversion H as [| E0 Y T Hwf HWF Hnot | E0 y T Hwf HWF Hnot]; subst.
        repeat split; auto.
Qed.

(* atoms used as typ_label labels *)
Fixpoint tlabs (T : typ) : atoms :=
  match T with
  | typ_label l P => AtomSetImpl.add l (tlabs P)
  | typ_arrow A B => AtomSetImpl.union (tlabs A) (tlabs B)
  | typ_all A B => AtomSetImpl.union (tlabs A) (tlabs B)
  | typ_mu A => tlabs A
  | typ_rcd_cons _ A B => AtomSetImpl.union (tlabs A) (tlabs B)
  | _ => AtomSetImpl.empty
  end.

Lemma mem_add_iff : forall (s : atoms) x l,
  AtomSetImpl.mem x (AtomSetImpl.add l s) = true <-> x = l \/ AtomSetImpl.mem x s = true.
Proof.
  intros s x l. split; intro E.
  - apply AtomSetImpl.mem_2 in E. apply in_add_iff in E. destruct E as [->|H]; auto.
    right. apply AtomSetImpl.mem_1; auto.
  - destruct E as [->|H].
    + apply AtomSetImpl.mem_1. apply in_add_iff. left; auto.
    + apply AtomSetImpl.mem_1. apply in_add_iff. right. apply AtomSetImpl.mem_2; auto.
Qed.

Lemma tlabs_add_notin : forall l a P, l \notin tlabs (typ_label a P) -> l <> a.
Proof.
  intros l a P H. apply (@notin_add_1' (tlabs P) a l); auto.
Qed.
Lemma tlabs_add_rest : forall l a P, l \notin tlabs (typ_label a P) -> l \notin tlabs P.
Proof.
  intros l a P H. apply (@notin_add_2' (tlabs P) a l); auto.
Qed.

Lemma mem_add_neq : forall (s : atoms) a l,
  a <> l -> AtomSetImpl.mem a (AtomSetImpl.add l s) = AtomSetImpl.mem a s.
Proof.
  intros s a l Hne. destruct (AtomSetImpl.mem a s) eqn:E.
  - assert (Hadd : AtomSetImpl.mem a (AtomSetImpl.add l s) = true).
    { apply AtomSetImpl.mem_1. apply in_add_iff. right.
      apply AtomSetImpl.mem_2; auto. }
    exact Hadd.
  - destruct (AtomSetImpl.mem a (AtomSetImpl.add l s)) eqn:E2; auto.
    exfalso. apply AtomSetImpl.mem_2 in E2. apply in_add_iff in E2.
    destruct E2 as [e|Hin].
    + apply Hne; auto.
    + apply AtomSetImpl.mem_1 in Hin. rewrite E in Hin. discriminate.
Qed.

Lemma we_add_fresh : forall Sig l T,
  l \notin tlabs T -> we (AtomSetImpl.add l Sig) T = we Sig T.
Proof.
  intros Sig l T. induction T as [| | n | a | T1 IHT1 T2 IHT2 | T1 IHT1 T2 IHT2 | T1 IHT1 | a P IHT | | i T1 IHT1 T2 IHT2]; simpl; intros H.
  - (* nat *) reflexivity.
  - (* top *) reflexivity.
  - (* bvar *) reflexivity.
  - (* fvar *) reflexivity.
  - (* arrow *)
    assert (H1 : l \notin tlabs T1) by fsetdec.
    assert (H2 : l \notin tlabs T2) by fsetdec.
    rewrite (IHT1 H1), (IHT2 H2); auto.
  - (* all *)
    assert (H1 : l \notin tlabs T1) by fsetdec.
    assert (H2 : l \notin tlabs T2) by fsetdec.
    rewrite (IHT1 H1), (IHT2 H2); auto.
  - (* mu *)
    rewrite (IHT1 H); auto.
  - (* label *)
    assert (Hne : a <> l)
      by (intro e; subst; apply (@tlabs_add_notin l l P); auto).
    rewrite (@mem_add_neq Sig a l Hne).
    destruct (AtomSetImpl.mem a Sig); simpl.
    + reflexivity.
    + f_equal. apply IHT. apply tlabs_add_rest in H; auto.
  - (* rcd_nil *) reflexivity.
  - (* rcd_cons *)
    assert (H1 : l \notin tlabs T1) by fsetdec.
    assert (H2 : l \notin tlabs T2) by fsetdec.
    rewrite (IHT1 H1), (IHT2 H2); auto.
Qed.


(* ===== Fueled checked-obligation sub procedure (algorithm only) ===== *)

Definition Needs := list (atom * env * typ * typ)%type.
Definition BRes := (bool * Needs)%type.




Definition null_needs (n : Needs) : bool :=
  match n with nil => true | _ => false end.

Definition append_needs (n1 n2 : Needs) : Needs := n1 ++ n2.

Definition AllNeedsSub (n : Needs) : Prop :=
  forall X E C D, In (X,E,C,D) n -> sub E C D.

Lemma AllNeedsSub_app_l : forall n1 n2,
  AllNeedsSub (append_needs n1 n2) -> AllNeedsSub n1.
Proof.
  intros n1 n2 H X E C D Hin.
  apply (H X E C D). unfold append_needs. apply in_or_app. left; auto.
Qed.
Lemma AllNeedsSub_app_r : forall n1 n2,
  AllNeedsSub (append_needs n1 n2) -> AllNeedsSub n2.
Proof.
  intros n1 n2 H X E C D Hin.
  apply (H X E C D). unfold append_needs. apply in_or_app. right; auto.
Qed.
Lemma AllNeedsSub_single : forall X E C D,
  sub E C D -> AllNeedsSub ((X,E,C,D)::nil).
Proof.
  intros X E C D H X0 E0 C0 D0 Hin. simpl in Hin.
  destruct Hin as [Heq|Hin]; [inversion Heq; subst; auto|contradiction].
Qed.

Lemma AllNeedsSub_nil : AllNeedsSub nil.
Proof. intros X E C D Hin. simpl in Hin. contradiction. Qed.
Lemma AllNeedsSub_cons_inv : forall X E C D l,
  AllNeedsSub ((X,E,C,D)::l) -> sub E C D /\ AllNeedsSub l.
Proof.
  intros X E C D l H. split.
  - apply (H X E C D). simpl; left; auto.
  - intros X0 E0 C0 D0 Hin. apply (H X0 E0 C0 D0). simpl; right; auto.
Qed.



Definition combine2 (p q : BRes) : BRes :=
  match p with
  | (false, _) => (false, nil)
  | (true, n1) =>
      match q with
      | (false, _) => (false, nil)
      | (true, n2) => (true, append_needs n1 n2)
      end
  end.

Definition combine3 (p q r : BRes) : BRes :=
  combine2 (combine2 p q) r.


Lemma false_pair_contra : forall (n1 n2 : Needs) ok needs,
  (false, n1) = (ok, needs) -> ok = true -> False.
Proof.
  intros n1 n2 ok needs H Hok. injection H as Hv _. rewrite <- Hv in Hok. discriminate.
Qed.

Lemma combine2_true_inv : forall p q ok needs,
  combine2 p q = (ok, needs) -> ok = true ->
  exists n1 n2, p = (true, n1) /\ q = (true, n2) /\
                needs = append_needs n1 n2.
Proof.
  intros p q ok needs H Hok.
  destruct p as [b1 n1]. destruct b1; simpl in H.
  - destruct q as [b2 n2]. destruct b2; simpl in H.
    + injection H as Hv Hn. rewrite <- Hn. exists n1, n2. auto.
    + exfalso; eapply false_pair_contra; eauto.
  - exfalso; eapply false_pair_contra; eauto.
Qed.

Lemma combine3_true_inv : forall p q r ok needs,
  combine3 p q r = (ok, needs) -> ok = true ->
  exists n1 n2 n3, p = (true,n1) /\ q = (true,n2) /\ r = (true,n3) /\
                   needs = append_needs (append_needs n1 n2) n3.
Proof.
  intros p q r ok needs H Hok. unfold combine3 in H.
  destruct (combine2 p q) as [b12 n12] eqn:H12.
  destruct b12; simpl in H.
  - destruct r as [br nr]. destruct br; simpl in H.
    + injection H as Hv Hn3. rewrite <- Hn3.
      destruct (@combine2_true_inv p q true n12 H12 eq_refl)
        as [n1 [n2 [Hp [Hq Hn12]]]].
      destruct (@combine2_true_inv (true,n12) (true,nr) true
                  (append_needs n12 nr) eq_refl eq_refl)
        as [n12' [n2' [Heq [Hr Hn12r]]]].
      injection Heq as Hn12'. subst n12'.
      exists n1, n2, n2'. repeat split; auto.
      rewrite Hn12r, Hn12. auto.
    + exfalso; eapply false_pair_contra; eauto.
  - exfalso; eapply false_pair_contra; eauto.
Qed.

Fixpoint remove_credit (X : atom) (Cr : list (atom * nat)) : list (atom * nat) :=
  match Cr with
  | nil => nil
  | (Y,c) :: Cr' =>
      if X == Y then remove_credit X Cr'
      else (Y,c) :: remove_credit X Cr'
  end.

Fixpoint check_obl (chk : env -> typ -> typ -> bool) (X : atom)
    (l : Needs) {struct l} : bool * Needs :=
  match l with
  | nil => (true, nil)
  | (Y,E,C,D) :: l' =>
      let (okr, rest) := check_obl chk X l' in
      if Y == X then (andb (chk E C D) okr, rest)
      else (okr, (Y,E,C,D) :: rest)
  end.

Lemma check_obl_sound : forall chk (X:atom) l ok rest,
  check_obl chk X l = (ok, rest) ->
  ok = true ->
  (forall E C D, chk E C D = true -> sub E C D) ->
  AllNeedsSub rest ->
  AllNeedsSub l.
Proof.
  intros chk X l. induction l as [|h l'].
  - simpl. intros ok rest H _ _ _. inversion H; subst. apply AllNeedsSub_nil.
  - destruct h as [h0 D]. destruct h0 as [h1 C]. destruct h1 as [Y E].
    simpl. intros ok rest H Hok Hchk Hrest.
    destruct (check_obl chk X l') as [okr restr] eqn:Hr.
    destruct (Y == X) as [e|ne].
    + simpl in H. injection H as Hend HrestEq.
      assert (Hand : andb (chk E C D) okr = true) by (rewrite Hend; exact Hok).
      rewrite andb_true_iff in Hand. destruct Hand as [Hc Hokr].
      assert (HrestR : AllNeedsSub restr) by (rewrite HrestEq; auto).
      assert (HrestL : AllNeedsSub l') by (eapply IHl'; eauto).
      intros X0 E0 C0 D0 Hin. simpl in Hin. destruct Hin as [Heq|Hin].
      * injection Heq as HY HE HC HD. subst X0 E0 C0 D0. apply Hchk; auto.
      * apply (HrestL X0 E0 C0 D0); auto.
    + simpl in H. injection H as HokEq HconsEq.
      assert (Hokr : okr = true) by (rewrite HokEq; auto).
      assert (HrestCons : AllNeedsSub ((Y,E,C,D)::restr)) by (rewrite HconsEq; auto).
      destruct (@AllNeedsSub_cons_inv Y E C D restr HrestCons) as [Hhead Htail].
      assert (HrestL : AllNeedsSub l') by (eapply IHl'; eauto).
      intros X0 E0 C0 D0 Hin. simpl in Hin. destruct Hin as [Heq|Hin].
      * injection Heq as HY HE HC HD. subst X0 E0 C0 D0. auto.
      * apply (HrestL X0 E0 C0 D0); auto.
Qed.



Fixpoint check_labels (chk : env -> typ -> typ -> BRes)
    (E : env) (A B : typ) (labels : list atom) {struct labels} : BRes :=
  match labels with
  | nil => (true, nil)
  | i :: l =>
      match Tlookup i A with
      | None => check_labels chk E A B l
      | Some t1 =>
          match Tlookup i B with
          | None => (false, nil)
          | Some t2 =>
              let (ok1,n1) := chk E t1 t2 in
              if ok1 then
                let (ok2,n2) := check_labels chk E A B l in
                if ok2 then (true, append_needs n1 n2) else (false, nil)
              else (false, nil)
          end
      end
  end.

Lemma check_labels_sound : forall (chk : env -> typ -> typ -> BRes)
    (E : env) (A B : typ) labels ok needs,
  check_labels chk E A B labels = (ok, needs) ->
  ok = true ->
  (forall E0 t1 t2 n0,
      chk E0 t1 t2 = (true, n0) -> AllNeedsSub n0 -> sub E0 t1 t2) ->
  AllNeedsSub needs ->
  forall i, In i labels ->
    forall t1 t2, Tlookup i A = Some t1 -> Tlookup i B = Some t2 -> sub E t1 t2.
Proof.
  intros chk E A B labels. induction labels as [|a l].
  - simpl. intros ok needs H _ _ _ i Hin. contradiction.
  - simpl. intros ok needs H Hok Hchk Hneeds i Hin t1 t2 H1 H2.
    destruct (Tlookup a A) as [ta1|] eqn:EA.
    + destruct (Tlookup a B) as [ta2|] eqn:EB.
      * destruct (chk E ta1 ta2) as [ok1 n1] eqn:Hc.
        destruct ok1.
        -- destruct (check_labels chk E A B l) as [ok2 n2] eqn:Htail.
           destruct ok2.
           ++ injection H as Htrue HneedsEq.
              assert (Happ : AllNeedsSub (append_needs n1 n2))
                by (rewrite <- HneedsEq in Hneeds; exact Hneeds).
              assert (Hn1 : AllNeedsSub n1) by (apply (@AllNeedsSub_app_l n1 n2); auto).
              assert (Hn2 : AllNeedsSub n2) by (apply (@AllNeedsSub_app_r n1 n2); auto).
              simpl in Hin. destruct Hin as [Heq|Hin].
              ** subst a.
                 assert (Et1 : t1 = ta1) by (rewrite H1 in EA; injection EA; auto).
                 assert (Et2 : t2 = ta2) by (rewrite H2 in EB; injection EB; auto).
                 subst t1 t2. apply (Hchk E ta1 ta2 n1); auto.
              ** eapply IHl; eauto.
           ++ injection H as Hfalse _; rewrite <- Hfalse in Hok; discriminate Hok.
        -- injection H as Hfalse _; rewrite <- Hfalse in Hok; discriminate Hok.
      * injection H as Hfalse _; rewrite <- Hfalse in Hok; discriminate Hok.
    + simpl in Hin. destruct Hin as [Heq|Hin].
      * subst a. rewrite EA in H1. discriminate.
      * eapply IHl; eauto.
Qed.


Definition eq_fvar_b (X : atom) (B : typ) : bool :=
  match B with
  | typ_fvar Y => if X == Y then true else false
  | _ => false
  end.


Fixpoint try_trans (chk : env -> typ -> typ -> BRes) (E : env) (X : atom)
    (B : typ) (Us : list typ) {struct Us} : BRes :=
  match Us with
  | nil => (false, nil)
  | U :: Us' =>
      match chk E U B with
      | (true, n) => (true, n)
      | (false, _) => try_trans chk E X B Us'
      end
  end.


Lemma try_trans_sound : forall chk E X B Us ok needs,
  try_trans chk E X B Us = (ok, needs) ->
  ok = true ->
  AllNeedsSub needs ->
  (forall U n, chk E U B = (true, n) -> AllNeedsSub n -> sub E U B) ->
  (forall U, In U Us -> binds X (bind_sub U) E) ->
  sub E (typ_fvar X) B.
Proof.
  intros chk E X B Us. induction Us as [|a Us'].
  - simpl. intros ok needs H Hok _ _ _. injection H as Hv _.
    rewrite <- Hv in Hok. discriminate Hok.
  - simpl. intros ok needs H Hok Hneeds Hchk Hbinds.
    destruct (chk E a B) as [oka na] eqn:Ha.
    destruct oka.
    + injection H as Hv Hn. rewrite <- Hn in Hneeds.
      eapply sa_trans_tvar.
      * apply Hbinds. simpl; left; auto.
      * apply (Hchk a na); auto.
    + eapply IHUs'; eauto.
Qed.




Fixpoint sub_b (fuel : nat) (Sig : atoms) (Cr : list (atom * nat))
    (active : atoms) (E : env) (A B : typ) {struct fuel} : BRes :=
  match fuel with
  | 0 => (false, nil)
  | S f =>
      if wf_env_b E then
        match B with
        | typ_top =>
            if WF_dec E A then (true, nil) else (false, nil)
        | _ =>
            match A with
            | typ_nat =>
                match B with typ_nat => (true,nil) | _ => (false,nil) end
            | typ_fvar X =>
                if eq_fvar_b X B then
                  (if WF_dec E A then (true,nil) else (false,nil))
                else
                  try_trans (sub_b f Sig Cr active) E X B (binds_sub_list E X)
            | typ_arrow A1 A2 =>
                match B with
                | typ_arrow B1 B2 =>
                    combine2 (sub_b f Sig Cr active E B1 A1)
                             (sub_b f Sig Cr active E A2 B2)
                | _ => (false,nil)
                end
            | typ_all S1 T1 =>
                match B with
                | typ_all S2 T2 =>
                    let X := fresh3 E (typ_all S1 T1) (typ_all S2 T2) in
                    let E2 := X ~ bind_sub S2 ++ E in
                    combine3 (sub_b f Sig Cr active E S1 S2)
                             (sub_b f Sig Cr active E S2 S1)
                             (sub_b f Sig Cr active E2 (open_tt T1 X) (open_tt T2 X))
                | _ => (false,nil)
                end
            | typ_mu A1 =>
                match B with
                | typ_mu A2 =>
                    let X := fresh3 E (typ_mu A1) (typ_mu A2) in
                    let E2 := X ~ bind_sub typ_top ++ E in
                    let P1 := open_tt A1 X in
                    let P2 := open_tt A2 X in
                    let U1 := open_tt A1 (typ_label X P1) in
                    let U2 := open_tt A2 (typ_label X P2) in
                    if andb (WF_dec E (typ_mu A1))
                            (andb (WF_dec E (typ_mu A2))
                                  (andb (WF_dec E2 P1) (WF_dec E2 P2))) then
                      let Sig' := AtomSetImpl.add X Sig in
                      let C := 3 * (we Sig' P1 + we Sig' P2) in
                      let Cr' := (X, C) :: Cr in
                      let active' := AtomSetImpl.add X active in
                      match sub_b f Sig' Cr' active' E2 U1 U2 with
                      | (false, _) => (false,nil)
                      | (true, needs) =>
                          let (okc, rest) :=
                            check_obl (fun Eo C0 D0 =>
                                         let (ok,nn) :=
                                           sub_b f Sig' (remove_credit X Cr')
                                             AtomSetImpl.empty Eo C0 D0 in
                                         andb ok (null_needs nn)) X needs in
                          if okc then (true, rest) else (false,nil)
                      end
                    else (false,nil)
                | _ => (false,nil)
                end
            | typ_label l A0 =>
                match B with
                | typ_label l' B0 =>
                    if l == l' then
                      if AtomSetImpl.mem l active then
                        (true, (l,E,A0,B0) :: nil)
                      else sub_b f Sig Cr active E A0 B0
                    else (false,nil)
                | _ => (false,nil)
                end
            | typ_rcd_nil =>
                match B with
                | typ_rcd_nil => (true,nil)
                | _ => (false,nil)
                end
            | typ_rcd_cons i A1 A2 =>
                match B with
                | typ_rcd_cons j B1 B2 =>
                    if andb (AtomSetImpl.subset (collectLabel B) (collectLabel A))
                            (andb (WF_dec E A) (WF_dec E B)) then
                      let (ok,n) := check_labels
                        (fun E0 t1 t2 => sub_b f Sig Cr active E0 t1 t2)
                        E A B (AtomSetImpl.elements (collectLabel B)) in
                      if ok then (true,n) else (false,nil)
                    else (false,nil)
                | _ => (false,nil)
                end
            | typ_bvar _ => (false,nil)
            | typ_top => (false,nil) (* B top handled above *)
            end
        end
      else (false,nil)
  end.

Lemma sub_b_fvar_trans_sound : forall f Sig Cr active E (X:atom) B ok needs,
  try_trans (sub_b f Sig Cr active) E X B (binds_sub_list E X) = (ok,needs) ->
  ok = true ->
  AllNeedsSub needs ->
  (forall U n, sub_b f Sig Cr active E U B = (true,n) ->
               AllNeedsSub n -> sub E U B) ->
  sub E (typ_fvar X) B.
Proof.
  intros. eapply try_trans_sound with
    (chk := sub_b f Sig Cr active) (Us := binds_sub_list E X); eauto.
  intros U HU. apply binds_sub_list_spec; auto.
Qed.

Definition sub_top_b (fuel:nat) (Sig:atoms) (Cr:list (atom*nat))
    (E:env) (A B:typ) : bool :=
  let (ok,needs) := sub_b fuel Sig Cr AtomSetImpl.empty E A B in
  andb ok (null_needs needs).



Definition fuel0 (E : env) (A B : typ) : nat :=
  M AtomSetImpl.empty nil E A B.

Definition sub_dec (E : env) (A B : typ) : bool :=
  sub_top_b (fuel0 E A B) AtomSetImpl.empty nil E A B.



(* ===== Resolving bound fvar heads (trans preprocessing) ===== *)

Fixpoint lookup_sub (E : env) (X : atom) : option typ :=
  match E with
  | nil => None
  | (Y, bind_sub U) :: E' =>
      if X == Y then Some U else lookup_sub E' X
  | (Y, bind_typ _) :: E' =>
      if X == Y then None else lookup_sub E' X
  end.

Lemma lookup_sub_some_binds : forall E X U,
  lookup_sub E X = Some U -> binds X (bind_sub U) E.
Proof.
  intros E X U. induction E as [|[Y b] E']; simpl; intros H.
  - discriminate.
  - destruct b; simpl in H.
    + destruct (X == Y) as [e|ne].
      * subst Y. injection H as Ht. subst U. simpl; left; reflexivity.
      * apply IHE' in H. simpl; right; auto.
    + destruct (X == Y) as [e|ne]; [discriminate|].
      apply IHE' in H. simpl; right; auto.
Qed.

Fixpoint resolve (n : nat) (E : env) (A : typ) {struct n} : typ :=
  match n with
  | 0 => A
  | S k =>
      match A with
      | typ_fvar X =>
          match lookup_sub E X with
          | Some U => resolve k E U
          | None => A
          end
      | _ => A
      end
  end.

Lemma resolve_sound : forall n E A B,
  sub E (resolve n E A) B -> sub E A B.
Proof.
  induction n as [|k IH]; intros E A B H.
  - simpl in H. exact H.
  - destruct A; simpl in *; try exact H.
    destruct (lookup_sub E a) as [U|] eqn:Eo.
    + apply sa_trans_tvar with U; [apply lookup_sub_some_binds; auto|].
      apply IH; auto.
    + exact H.
Qed.



(* ===== Occurrence counts for the termination token scheme ===== *)

Fixpoint count_fvar (X : atom) (T : typ) : nat :=
  match T with
  | typ_nat => 0
  | typ_top => 0
  | typ_bvar _ => 0
  | typ_fvar Y => if X == Y then 1 else 0
  | typ_arrow A B => count_fvar X A + count_fvar X B
  | typ_all A B => count_fvar X A + count_fvar X B
  | typ_mu A => count_fvar X A
  | typ_label _ A => count_fvar X A
  | typ_rcd_nil => 0
  | typ_rcd_cons _ A B => count_fvar X A + count_fvar X B
  end.

Fixpoint occ_binder_aux (d : nat) (T : typ) : nat :=
  match T with
  | typ_nat => 0
  | typ_top => 0
  | typ_bvar J => if d === J then 1 else 0
  | typ_fvar _ => 0
  | typ_arrow A B => occ_binder_aux d A + occ_binder_aux d B
  | typ_all A B => occ_binder_aux d A + occ_binder_aux (S d) B
  | typ_mu A => occ_binder_aux (S d) A
  | typ_label _ A => occ_binder_aux d A
  | typ_rcd_nil => 0
  | typ_rcd_cons _ A B => occ_binder_aux d A + occ_binder_aux d B
  end.

Definition occ_binder (T : typ) : nat := occ_binder_aux 0 T.

Lemma count_fvar_open_rec : forall X T K,
  X \notin fv_tt T ->
  count_fvar X (open_tt_rec K X T) = occ_binder_aux K T.
Proof.
  intros X T. induction T as [| | n | a | A IHA B IHB | A IHA B IHB | A IHA | l A IHA | | i A IHA B IHB];
    simpl; intros K Hfv.
  - reflexivity.
  - reflexivity.
  - destruct (K === n) as [eK|neK]; simpl.
    + destruct (X == X) as [eX|neX]; [reflexivity|exfalso; auto].
    + reflexivity.
  - assert (a <> X) by (intro eAX; subst a; apply Hfv; simpl; fsetdec).
    destruct (X == a) as [eXa|neXa]; [exfalso; auto|reflexivity].
  - assert (HA : X \notin fv_tt A) by fsetdec.
    assert (HB : X \notin fv_tt B) by fsetdec.
    rewrite (IHA K HA), (IHB K HB). reflexivity.
  - assert (HA : X \notin fv_tt A) by fsetdec.
    assert (HB : X \notin fv_tt B) by fsetdec.
    rewrite (IHA K HA), (IHB (S K) HB). reflexivity.
  - assert (HA : X \notin fv_tt A) by fsetdec.
    rewrite (IHA (S K) HA). reflexivity.
  - assert (HA : X \notin fv_tt A) by fsetdec.
    rewrite (IHA K HA). reflexivity.
  - reflexivity.
  - assert (HA : X \notin fv_tt A) by fsetdec.
    assert (HB : X \notin fv_tt B) by fsetdec.
    rewrite (IHA K HA), (IHB K HB). reflexivity.
Qed.

Corollary count_fvar_open_self : forall X T,
  X \notin fv_tt T -> count_fvar X (open_tt T X) = occ_binder T.
Proof.
  intros X T H. unfold open_tt, occ_binder. apply count_fvar_open_rec; auto.
Qed.



(* ===== Environment ranks used by occurrence-token termination attempts ===== *)

Fixpoint index_of (E : env) (X : atom) : option nat :=
  match E with
  | nil => None
  | (Y, _) :: E' =>
      if X == Y then Some 0
      else match index_of E' X with
           | Some i => Some (S i)
           | None => None
           end
  end.

Definition rank (E : env) (X : atom) : option nat :=
  match index_of E X with
  | Some i => Some (length E - i)
  | None => None
  end.



Lemma sub_fvar_binds_step : forall E X U B,
  binds X (bind_sub U) E -> sub E U B -> sub E (typ_fvar X) B.
Proof. intros; eapply sa_trans_tvar; eauto. Qed.


Lemma resolve_step_sound : forall E X U B,
  lookup_sub E X = Some U -> sub E U B -> sub E (typ_fvar X) B.
Proof.
  intros E X U B Ho Hsub.
  apply sub_fvar_binds_step with U; auto.
  apply lookup_sub_some_binds; auto.
Qed.


(* ===== Simpler memo/cycle-free declarative search (fueled) ===== *)

Fixpoint try_trans_b (chk : env -> typ -> typ -> bool)
    (E : env) (Us : list typ) (B : typ) {struct Us} : bool :=
  match Us with
  | nil => false
  | U :: Us' => if chk E U B then true else try_trans_b chk E Us' B
  end.


Lemma try_trans_b_sound : forall (chk : env -> typ -> typ -> bool) E Us B,
  try_trans_b chk E Us B = true ->
  (forall U, In U Us -> chk E U B = true -> sub E U B) ->
  forall X, (forall U, In U Us -> binds X (bind_sub U) E) ->
  sub E (typ_fvar X) B.
Proof.
  intros chk E Us. induction Us as [|a Us']; intros B H Hchk X Hbinds.
  - simpl in H. discriminate.
  - simpl in H. destruct (chk E a B) eqn:Hc.
    + apply sa_trans_tvar with a.
      * apply (Hbinds a); simpl; left; auto.
      * apply (Hchk a); [simpl; left; auto|exact Hc].
    + eapply IHUs'.
      * exact H.
      * intros U HU HcU. apply (Hchk U); [simpl; right; auto|exact HcU].
      * intros U HU. apply (Hbinds U); simpl; right; auto.
Qed.

Fixpoint sub_plain (fuel : nat) (Sig : atoms) (E : env) (A B : typ)
    {struct fuel} : bool :=
  match fuel with
  | 0 => false
  | S f =>
      if wf_env_b E then
        match B with
        | typ_top => WF_dec E A
        | _ =>
            match A with
            | typ_nat => match B with typ_nat => true | _ => false end
            | typ_fvar X =>
                if eq_fvar_b X B then
                  if WF_dec E A then true
                  else try_trans_b (sub_plain f Sig) E (binds_sub_list E X) B
                else try_trans_b (sub_plain f Sig) E (binds_sub_list E X) B
            | typ_arrow A1 A2 =>
                match B with
                | typ_arrow B1 B2 =>
                    andb (sub_plain f Sig E B1 A1) (sub_plain f Sig E A2 B2)
                | _ => false
                end
            | typ_all S1 T1 =>
                match B with
                | typ_all S2 T2 =>
                    let X := fresh3 E (typ_all S1 T1) (typ_all S2 T2) in
                    andb (sub_plain f Sig E S1 S2)
                      (andb (sub_plain f Sig E S2 S1)
                            (sub_plain f Sig (X ~ bind_sub S2 ++ E)
                                      (open_tt T1 X) (open_tt T2 X)))
                | _ => false
                end
            | typ_mu A1 =>
                match B with
                | typ_mu A2 =>
                    let X := fresh3 E (typ_mu A1) (typ_mu A2) in
                    let E2 := X ~ bind_sub typ_top ++ E in
                    let P1 := open_tt A1 X in
                    let P2 := open_tt A2 X in
                    let U1 := open_tt A1 (typ_label X P1) in
                    let U2 := open_tt A2 (typ_label X P2) in
                    if andb (WF_dec E (typ_mu A1))
                            (andb (WF_dec E (typ_mu A2))
                                  (andb (WF_dec E2 P1) (WF_dec E2 P2))) then
                      sub_plain f (AtomSetImpl.add X Sig) E2 U1 U2
                    else false
                | _ => false
                end
            | typ_label l A0 =>
                match B with
                | typ_label l' B0 =>
                    if l == l' then sub_plain f Sig E A0 B0 else false
                | _ => false
                end
            | typ_rcd_nil =>
                match B with typ_rcd_nil => true | _ => false end
            | typ_rcd_cons i A1 A2 =>
                match B with
                | typ_rcd_cons j B1 B2 =>
                    if andb (AtomSetImpl.subset (collectLabel B) (collectLabel A))
                            (andb (WF_dec E A) (WF_dec E B)) then
                      lookup_check (fun E0 t1 t2 => sub_plain f Sig E0 t1 t2) E A B
                    else false
                | _ => false
                end
            | typ_top => false
            | typ_bvar _ => false
            end
        end
      else false
  end.



Definition sub_plain_dec (E : env) (A B : typ) : bool :=
  sub_plain (M AtomSetImpl.empty nil E A B) AtomSetImpl.empty E A B.

(* ============ Small helpers on the atom sets used by fresh3 ============ *)

Lemma notin_allT_all_l : forall (X:atom) A B,
  X \notin allT (typ_all A B) -> X \notin allT A.
Proof. intros X A B H. unfold allT in *. simpl in *. fsetdec. Qed.

Lemma notin_allT_all_r : forall (X:atom) A B,
  X \notin allT (typ_all A B) -> X \notin allT B.
Proof. intros X A B H. unfold allT in *. simpl in *. fsetdec. Qed.

Lemma notin_allT_mu : forall (X:atom) A,
  X \notin allT (typ_mu A) -> X \notin allT A.
Proof. intros X A H. unfold allT in *. simpl in *. exact H. Qed.

(* ============ Generalising the mu WF premise from a fresh variable ============ *)

Lemma WF_mu_body_generalize : forall E A (X:atom),
  X \notin allE E -> X \notin allT A ->
  WF (X ~ bind_sub typ_top ++ E) (open_tt A X) ->
  forall Y,
    Y \notin AtomSetImpl.add X
      (AtomSetImpl.union (allE E) (allT A)) ->
    WF (Y ~ bind_sub typ_top ++ E) (open_tt A Y).
Proof.
  intros E A X HXE HXA HW Y HY.
  assert (HYX : Y <> X) by (intro e; subst Y; apply HY; apply AtomSetImpl.add_1; auto).
  assert (HYE : Y \notin allE E) by fsetdec.
  assert (HYA : Y \notin allT A) by fsetdec.
  pose proof (@WF_ren_fwd X Y (X ~ bind_sub typ_top ++ E) (open_tt A X) HW) as Hr.
  rewrite ren_env_cons in Hr.
  cbn [ren_b] in Hr.
  rewrite (swp_eq_l X Y) in Hr.
  rewrite (@swp_fix_env X Y E HXE HYE) in Hr.
  rewrite !ren_open in Hr.
  cbn [ren] in Hr.
  rewrite (swp_eq_l X Y) in Hr.
  rewrite (@swp_fix_typ X Y A HXA HYA) in Hr.
  exact Hr.
Qed.

(* ============ Soundness of the boolean transposition search ============ *)

Lemma try_trans_b_plain_sound_gen : forall f Sig E (X:atom) Us B,
  try_trans_b (sub_plain f Sig) E Us B = true ->
  (forall U, In U Us -> binds X (bind_sub U) E) ->
  (forall U, In U Us -> sub_plain f Sig E U B = true -> sub E U B) ->
  sub E (typ_fvar X) B.
Proof.
  intros f Sig E X Us. induction Us as [|a Us']; intros B H Hb Hchk.
  - simpl in H. discriminate H.
  - simpl in H. destruct (sub_plain f Sig E a B) eqn:Ea; simpl in H.
    + eapply sa_trans_tvar.
      * apply Hb. left; auto.
      * apply Hchk; auto. left; auto.
    + apply (IHUs' B H).
      * intros U HU. apply Hb. right; auto.
      * intros U HU. apply Hchk. right; auto.
Qed.

Lemma try_trans_b_plain_sound : forall f Sig E (X:atom) B,
  try_trans_b (sub_plain f Sig) E (binds_sub_list E X) B = true ->
  (forall U, sub_plain f Sig E U B = true -> sub E U B) ->
  sub E (typ_fvar X) B.
Proof.
  intros f Sig E X B H Hchk.
  eapply try_trans_b_plain_sound_gen; eauto.
  intros U HU. apply binds_sub_list_spec; auto.
Qed.

(* ============ Auxiliary inversion for the trailing if-then-false ============ *)

Lemma if_true_inv : forall (c b : bool),
  (if c then b else false) = true -> c = true /\ b = true.
Proof.
  intros c b H. destruct c; simpl in H; [split; auto | discriminate H].
Qed.

(* ============ Main soundness theorem ============ *)

Lemma sub_plain_sound : forall fuel Sig E A B,
  sub_plain fuel Sig E A B = true -> sub E A B.
Proof.
  induction fuel as [|f IH]; intros Sig E A B H.
  - simpl in H. discriminate H.
  - simpl in H.
    destruct (wf_env_b E) eqn:Ewf; [|discriminate H].
    apply wf_env_b_spec in Ewf.
    destruct B as [| |n|Y|B1 B2|S2 T2|M2|l' B0| |j B1 B2].
    + (* B = typ_nat *)
      destruct A as [| |n'|X|A1 A2|S1 T1|A1|l A0| |i A1 A2]; simpl in H; try discriminate H.
      * apply sa_nat; auto.
      * eapply try_trans_b_plain_sound; eauto.
    + (* B = typ_top *)
      simpl in H. apply WF_dec_spec in H. apply sa_top; auto.
    + (* B = typ_bvar n *)
      destruct A as [| |n'|X|A1 A2|S1 T1|A1|l A0| |i A1 A2]; simpl in H; try discriminate H.
      eapply try_trans_b_plain_sound; eauto.
    + (* B = typ_fvar Y *)
      destruct A as [| |n'|X|A1 A2|S1 T1|A1|l A0| |i A1 A2]; simpl in H; try discriminate H.
      destruct (X == Y) as [eXY|neXY]; simpl in H.
      * subst Y. destruct (WF_dec E (typ_fvar X)) eqn:EWF; simpl in H.
        -- apply sa_fvar; auto. apply WF_dec_spec; auto.
        -- eapply try_trans_b_plain_sound; eauto.
      * eapply try_trans_b_plain_sound; eauto.
    + (* B = typ_arrow B1 B2 *)
      destruct A as [| |n'|X|A1 A2|S1 T1|A1|l A0| |i A1 A2]; simpl in H; try discriminate H.
      * eapply try_trans_b_plain_sound; eauto.
      * rewrite andb_true_iff in H. destruct H as [H1 H2].
        apply sa_arrow; [apply (IH Sig E B1 A1 H1) | apply (IH Sig E A2 B2 H2)].
    + (* B = typ_all S2 T2 *)
      destruct A as [| |n'|X|A1 A2|S1 T1|A1|l A0| |i A1 A2]; simpl in H; try discriminate H.
      * eapply try_trans_b_plain_sound; eauto.
      * rewrite andb_true_iff in H. destruct H as [H12 Hrest].
        rewrite andb_true_iff in Hrest. destruct Hrest as [H21 HB].
        set (X := fresh3 E (typ_all S1 T1) (typ_all S2 T2)) in *.
        eapply sa_all with
          (L := AtomSetImpl.add X
                  (AtomSetImpl.union (allE E)
                     (AtomSetImpl.union (allT S2)
                        (AtomSetImpl.union (allT T1) (allT T2))))).
        -- apply (IH Sig E S1 S2 H12).
        -- apply (IH Sig E S2 S1 H21).
        -- intros Z HZ.
           eapply sub_all_body_generalize with (X := X).
           ++ apply fresh3_E.
           ++ apply notin_allT_all_l with (A := S2) (B := T2). apply fresh3_B.
           ++ apply notin_allT_all_r with (A := S1) (B := T1). apply fresh3_A.
           ++ apply notin_allT_all_r with (A := S2) (B := T2). apply fresh3_B.
           ++ apply (IH Sig (X ~ bind_sub S2 ++ E) (open_tt T1 X) (open_tt T2 X) HB).
           ++ exact HZ.
    + (* B = typ_mu A2 *)
      destruct A as [| |n'|X|A1 A2|S1 T1|A1|l A0| |i A1 A2]; simpl in H; try discriminate H.
      * eapply try_trans_b_plain_sound; eauto.
      * set (X := fresh3 E (typ_mu A1) (typ_mu M2)) in *.
        set (E2 := X ~ bind_sub typ_top ++ E) in *.
        set (P1 := open_tt A1 X) in *.
        set (P2 := open_tt M2 X) in *.
        set (U1 := open_tt A1 (typ_label X P1)) in *.
        set (U2 := open_tt M2 (typ_label X P2)) in *.
        apply if_true_inv in H. destruct H as [Hc Hb].
        rewrite andb_true_iff in Hc. destruct Hc as [Hw1 Hc].
        rewrite andb_true_iff in Hc. destruct Hc as [Hw2 Hc].
        rewrite andb_true_iff in Hc. destruct Hc as [Hw3 Hw4].
        apply WF_dec_spec in Hw1. apply WF_dec_spec in Hw2.
        apply WF_dec_spec in Hw3. apply WF_dec_spec in Hw4.
        eapply sa_rec with
          (L := AtomSetImpl.add X
                  (AtomSetImpl.union (allE E)
                     (AtomSetImpl.union (allT A1) (allT M2)))).
        -- intros Z HZ.
           eapply WF_mu_body_generalize with (X := X).
           ++ apply fresh3_E.
           ++ apply notin_allT_mu. apply fresh3_A.
           ++ exact Hw3.
           ++ fsetdec.
        -- intros Z HZ.
           eapply WF_mu_body_generalize with (X := X).
           ++ apply fresh3_E.
           ++ apply notin_allT_mu. apply fresh3_B.
           ++ exact Hw4.
           ++ fsetdec.
        -- intros Z HZ.
           eapply sub_rec_body_generalize with (X := X).
           ++ apply fresh3_E.
           ++ apply notin_allT_mu. apply fresh3_A.
           ++ apply notin_allT_mu. apply fresh3_B.
           ++ apply (IH (AtomSetImpl.add X Sig) E2 U1 U2 Hb).
           ++ exact HZ.
    + (* B = typ_label l' B0 *)
      destruct A as [| |n'|X|A1 A2|S1 T1|A1|l A0| |i A1 A2]; simpl in H; try discriminate H.
      * eapply try_trans_b_plain_sound; eauto.
      * destruct (l == l') as [ell|nll]; simpl in H.
        -- subst l'. apply sa_label. apply (IH Sig E A0 B0 H).
        -- discriminate H.
    + (* B = typ_rcd_nil *)
      destruct A as [| |n'|X|A1 A2|S1 T1|A1|l A0| |i A1 A2]; simpl in H; try discriminate H.
      * eapply try_trans_b_plain_sound; eauto.
      * eapply sa_rcd with (A1 := typ_rcd_nil) (A2 := typ_rcd_nil).
        -- exact Ewf.
        -- apply rt_type_rcd_nil.
        -- apply rt_type_rcd_nil.
        -- intros z Hz. exact Hz.
        -- apply WF_rcd_nil.
        -- apply WF_rcd_nil.
        -- intros i0 t1 t2 Ht1 Ht2. simpl in Ht1. discriminate Ht1.
    + (* B = typ_rcd_cons j B1 B2 *)
      destruct A as [| |n'|X|A1 A2|S1 T1|A1|l A0| |i A1 A2]; simpl in H; try discriminate H.
      * eapply try_trans_b_plain_sound; eauto.
      * apply if_true_inv in H. destruct H as [Hc Hb].
        rewrite andb_true_iff in Hc. destruct Hc as [Hsub Hc].
        rewrite andb_true_iff in Hc. destruct Hc as [HWFA HWFB].
        apply WF_dec_spec in HWFA. apply WF_dec_spec in HWFB.
        eapply sa_rcd with
          (A1 := typ_rcd_cons i A1 A2) (A2 := typ_rcd_cons j B1 B2).
        -- exact Ewf.
        -- apply rt_type_rcd_cons.
        -- apply rt_type_rcd_cons.
        -- apply AtomSetImpl.subset_2. exact Hsub.
        -- exact HWFA.
        -- exact HWFB.
        -- intros i0 t1 t2 Ht1 Ht2.
           assert (Hchk : sub_plain f Sig E t1 t2 = true).
           { eapply lookup_check_sound; eauto. }
           apply (IH Sig E t1 t2 Hchk).
Qed.


Lemma Tlookup_same_label : forall (i:atom) T1 T2,
  Tlookup i (typ_rcd_cons i T1 T2) = Some T1.
Proof.
  intros i T1 T2. simpl. rewrite eq_dec_refl. reflexivity.
Qed.

Lemma Tlookup_other_label : forall (i i0:atom) T1 T2,
  i <> i0 -> Tlookup i0 (typ_rcd_cons i T1 T2) = Tlookup i0 T2.
Proof.
  intros i i0 T1 T2 Hne. simpl.
  destruct (i == i0) as [e|ne].
  - exfalso. apply Hne. exact e.
  - reflexivity.
Qed.

(* Reflexivity of subsumption for well-formed types in well-formed envs.

   We prove a slightly stronger auxiliary statement simultaneously: every
   type looked up inside A is also reflexive.  This is exactly what the
   [sa_rcd] rule needs for its componentwise premise.  The auxiliary is
   phrased with a redundant copy of the WF hypothesis, which lets us keep
   [WF E A -> ...] as the induction motive so that every constructor case
   still has access to its WF premises (notably in the [WF_all] and
   [WF_rec] cases). *)

Lemma sub_refl_aux : forall E A,
  WF E A -> wf_env E ->
  sub E A A /\
  (forall i t, Tlookup i A = Some t -> sub E t t).
Proof.
  intros E A H Hwf.
  assert (Hcopy : WF E A) by exact H.
  revert Hcopy Hwf.
  induction H.
  - (* WF_top *)
    intros Hw Hwf. split.
    + apply sa_top; auto.
    + intros i t Ht. simpl in Ht. discriminate Ht.
  - (* WF_nat *)
    intros Hw Hwf. split.
    + apply sa_nat; auto.
    + intros i t Ht. simpl in Ht. discriminate Ht.
  - (* WF_var *)
    intros Hw Hwf. split.
    + apply sa_fvar; auto.
    + intros i t Ht. simpl in Ht. discriminate Ht.
  - (* WF_arrow *)
    intros Hw Hwf. split.
    + apply sa_arrow.
      * destruct (IHWF1 H Hwf) as [Hs _]. exact Hs.
      * destruct (IHWF2 H0 Hwf) as [Hs _]. exact Hs.
    + intros i t Ht. simpl in Ht. discriminate Ht.
  - (* WF_all *)
    intros Hw Hwf. split.
    + eapply sa_all with (L := AtomSetImpl.union L (dom E)).
      * destruct (IHWF H Hwf) as [Hs _]. exact Hs.
      * destruct (IHWF H Hwf) as [Hs _]. exact Hs.
      * intros X HX.
        assert (HXL : X \notin L) by fsetdec.
        assert (HXdom : X \notin dom E) by fsetdec.
        assert (Hwfe : wf_env (X ~ bind_sub T1 ++ E)).
        { eapply wf_env_sub; eauto. }
        destruct (H1 X HXL (H0 X HXL) Hwfe) as [Hs _]. exact Hs.
    + intros i t Ht. simpl in Ht. discriminate Ht.
  - (* WF_rec *)
    intros Hw Hwf. split.
    + eapply sa_rec with (L := AtomSetImpl.union L (dom E)).
      * intros X HX. apply H. fsetdec.
      * intros X HX. apply H. fsetdec.
      * intros X HX.
        assert (HXL : X \notin L) by fsetdec.
        assert (HXdom : X \notin dom E) by fsetdec.
        assert (Hwfe : wf_env (X ~ bind_sub typ_top ++ E)).
        { eapply wf_env_sub.
          - exact Hwf.
          - apply WF_top.
          - exact HXdom. }
        destruct (H2 X HXL (H1 X HXL) Hwfe) as [Hs _]. exact Hs.
    + intros i t Ht. simpl in Ht. discriminate Ht.
  - (* WF_label *)
    intros Hw Hwf. split.
    + apply sa_label. destruct (IHWF H Hwf) as [Hs _]. exact Hs.
    + intros i t Ht. simpl in Ht. discriminate Ht.
  - (* WF_rcd_nil *)
    intros Hw Hwf. split.
    + eapply sa_rcd with (A1 := typ_rcd_nil) (A2 := typ_rcd_nil).
      * exact Hwf.
      * apply rt_type_rcd_nil.
      * apply rt_type_rcd_nil.
      * intros z Hz. exact Hz.
      * exact Hw.
      * exact Hw.
      * intros i0 t1 t2 Ht1 Ht2. simpl in Ht1. discriminate Ht1.
    + intros i t Ht. simpl in Ht. discriminate Ht.
  - (* WF_rcd_cons *)
    intros Hw Hwf.
    destruct (IHWF1 H Hwf) as [HsubT1 HQ1].
    destruct (IHWF2 H0 Hwf) as [HsubT2 HQ2].
    split.
    + eapply sa_rcd with
        (A1 := typ_rcd_cons i T1 T2) (A2 := typ_rcd_cons i T1 T2).
      * exact Hwf.
      * apply rt_type_rcd_cons.
      * apply rt_type_rcd_cons.
      * intros z Hz. exact Hz.
      * exact Hw.
      * exact Hw.
      * intros i0 t1 t2 Ht1 Ht2.
        assert (Heq : t1 = t2) by
          (rewrite Ht1 in Ht2; injection Ht2; auto).
        subst t2.
        destruct (i == i0) as [eii|neii] eqn:Eii.
        -- subst i0. rewrite Tlookup_same_label in Ht1.
           injection Ht1 as Ht1. subst t1. exact HsubT1.
        -- rewrite (@Tlookup_other_label i i0 T1 T2 neii) in Ht1.
           apply (HQ2 i0 t1 Ht1).
    + intros i0 t Ht.
      destruct (i == i0) as [eii|neii] eqn:Eii.
      * subst i0. rewrite Tlookup_same_label in Ht.
        injection Ht as Ht. subst t. exact HsubT1.
      * rewrite (@Tlookup_other_label i i0 T1 T2 neii) in Ht.
        apply (HQ2 i0 t Ht).
Qed.

Lemma sub_refl : forall E A, wf_env E -> WF E A -> sub E A A.
Proof.
  intros E A Hwf H.
  exact (proj1 (sub_refl_aux H Hwf)).
Qed.


Lemma try_trans_b_mono : forall chk chk',
  (forall E U B, chk E U B = true -> chk' E U B = true) ->
  forall E Us B,
    try_trans_b chk E Us B = true -> try_trans_b chk' E Us B = true.
Proof.
  intros chk chk' Hpt E Us.
  induction Us as [|a Us IH]; intros B H.
  - simpl in H. discriminate H.
  - simpl in H. simpl.
    destruct (chk E a B) eqn:Ea.
    + apply Hpt in Ea. rewrite Ea. reflexivity.
    + destruct (chk' E a B) eqn:Eb; [reflexivity|].
      apply IH. exact H.
Qed.

(* ======================= Monotonicity of lookup_check ================== *)

Lemma lookup_check_mono : forall chk chk',
  (forall E t1 t2, chk E t1 t2 = true -> chk' E t1 t2 = true) ->
  forall E A B,
    lookup_check chk E A B = true -> lookup_check chk' E A B = true.
Proof.
  intros chk chk' Hpt E A B H.
  apply lookup_check_complete.
  intros i t1 t2 H1 H2.
  apply Hpt.
  eapply lookup_check_sound; eauto.
Qed.

(* ======================= Fuel monotonicity of sub_plain ================ *)

Lemma eq_fvar_b_refl : forall X : atom,
  eq_fvar_b X (typ_fvar X) = true.
Proof.
  intros X. unfold eq_fvar_b.
  destruct (X == X) as [e|ne]; auto.
Qed.

Lemma eq_fvar_b_neq : forall (X Y : atom),
  X <> Y -> eq_fvar_b X (typ_fvar Y) = false.
Proof.
  intros X Y Hne. unfold eq_fvar_b.
  destruct (X == Y) as [e|ne]; [exfalso; auto|reflexivity].
Qed.

(* sub_plain's every recursive call is made at fuel f where the enclosing
   call is at fuel (S f).  Hence the result is monotone in the fuel. *)

Lemma sub_plain_mono : forall n m, n <= m ->
  forall Sig E A B,
    sub_plain n Sig E A B = true -> sub_plain m Sig E A B = true.
Proof.
  induction n as [|n IH]; intros m Hle Sig E A B H.
  - simpl in H. discriminate H.
  - destruct m as [|m]; [inversion Hle|].
    assert (Hle' : n <= m) by lia.
    simpl in H. simpl.
    destruct (wf_env_b E) eqn:Ewf; [|discriminate H].
    destruct B as [| |nB|Y|B1 B2|S2 T2|M2|l' B0| |j B1 B2].
    + (* B = typ_nat *)
      destruct A as [| |nA|X|A1 A2|S1 T1|M1|l A0| |i A1 A2];
        simpl in H; try discriminate H.
      * reflexivity.
      * (* A = typ_fvar X : transposition search *)
        eapply try_trans_b_mono; [|exact H].
        intros E0 U C Hc. exact (IH m Hle' Sig E0 U C Hc).
    + (* B = typ_top *)
      simpl in H. simpl. exact H.
    + (* B = typ_bvar nB *)
      destruct A as [| |nA|X|A1 A2|S1 T1|M1|l A0| |i A1 A2];
        simpl in H; try discriminate H.
      (* A = typ_fvar X *)
      eapply try_trans_b_mono; [|exact H].
      intros E0 U C Hc. exact (IH m Hle' Sig E0 U C Hc).
    + (* B = typ_fvar Y *)
      destruct A as [| |nA|X|A1 A2|S1 T1|M1|l A0| |i A1 A2];
        simpl in H; try discriminate H.
      (* A = typ_fvar X *)
      destruct (X == Y) as [eXY|neXY]; simpl in H.
      * subst Y. rewrite eq_fvar_b_refl. simpl.
        destruct (WF_dec E (typ_fvar X)) eqn:EWF; simpl in H; simpl.
        -- reflexivity.
        -- eapply try_trans_b_mono; [|exact H].
           intros E0 U C Hc. exact (IH m Hle' Sig E0 U C Hc).
      * rewrite (eq_fvar_b_neq neXY). simpl.
        eapply try_trans_b_mono; [|exact H].
        intros E0 U C Hc. exact (IH m Hle' Sig E0 U C Hc).
    + (* B = typ_arrow B1 B2 *)
      destruct A as [| |nA|X|A1 A2|S1 T1|M1|l A0| |i A1 A2];
        simpl in H; try discriminate H.
      * (* A = typ_fvar X *)
        eapply try_trans_b_mono; [|exact H].
        intros E0 U C Hc. exact (IH m Hle' Sig E0 U C Hc).
      * (* A = typ_arrow A1 A2 *)
        rewrite andb_true_iff in H. destruct H as [H1 H2].
        rewrite andb_true_iff. split.
        -- exact (IH m Hle' Sig E B1 A1 H1).
        -- exact (IH m Hle' Sig E A2 B2 H2).
    + (* B = typ_all S2 T2 *)
      destruct A as [| |nA|X|A1 A2|S1 T1|M1|l A0| |i A1 A2];
        simpl in H; try discriminate H.
      * (* A = typ_fvar X *)
        eapply try_trans_b_mono; [|exact H].
        intros E0 U C Hc. exact (IH m Hle' Sig E0 U C Hc).
      * (* A = typ_all S1 T1 *)
        rewrite andb_true_iff in H. destruct H as [H1 H2].
        rewrite andb_true_iff in H2. destruct H2 as [H2 H3].
        rewrite andb_true_iff. split.
        -- exact (IH m Hle' Sig E S1 S2 H1).
        -- rewrite andb_true_iff. split.
           ++ exact (IH m Hle' Sig E S2 S1 H2).
           ++ eapply IH; eauto.
    + (* B = typ_mu M2 *)
      destruct A as [| |nA|X|A1 A2|S1 T1|M1|l A0| |i A1 A2];
        simpl in H; try discriminate H.
      * (* A = typ_fvar X *)
        eapply try_trans_b_mono; [|exact H].
        intros E0 U C Hc. exact (IH m Hle' Sig E0 U C Hc).
      * (* A = typ_mu M1 *)
        simpl in H; simpl.
        match goal with
        | |- context[if ?c then _ else _] =>
            destruct c eqn:Ec; [simpl in * | simpl in H; discriminate H]
        end.
        eapply IH; eauto.
    + (* B = typ_label l' B0 *)
      destruct A as [| |nA|X|A1 A2|S1 T1|M1|l A0| |i A1 A2];
        simpl in H; try discriminate H.
      * (* A = typ_fvar X *)
        eapply try_trans_b_mono; [|exact H].
        intros E0 U C Hc. exact (IH m Hle' Sig E0 U C Hc).
      * (* A = typ_label l A0 *)
        destruct (l == l') as [ell|nll]; simpl in H; simpl.
        -- exact (IH m Hle' Sig E A0 B0 H).
        -- discriminate H.
    + (* B = typ_rcd_nil *)
      destruct A as [| |nA|X|A1 A2|S1 T1|M1|l A0| |i A1 A2];
        simpl in H; try discriminate H.
      * (* A = typ_fvar X *)
        eapply try_trans_b_mono; [|exact H].
        intros E0 U C Hc. exact (IH m Hle' Sig E0 U C Hc).
      * (* A = typ_rcd_nil *) reflexivity.
    + (* B = typ_rcd_cons j B1 B2 *)
      destruct A as [| |nA|X|A1 A2|S1 T1|M1|l A0| |i A1 A2];
        simpl in H; try discriminate H.
      * (* A = typ_fvar X *)
        eapply try_trans_b_mono; [|exact H].
        intros E0 U C Hc. exact (IH m Hle' Sig E0 U C Hc).
      * (* A = typ_rcd_cons i A1 A2 *)
        simpl in H; simpl.
        match goal with
        | |- context[if ?c then _ else _] =>
            destruct c eqn:Ec; [simpl in * | simpl in H; discriminate H]
        end.
        eapply lookup_check_mono; [|exact H].
        intros E0 t1 t2 Hc. exact (IH m Hle' Sig E0 t1 t2 Hc).
Qed.

(* The "for all sufficiently large fuel" form, convenient for combining
   several sub-search calls that must share one fuel. *)

Lemma sub_plain_mono_ge : forall n m, n <= m ->
  forall Sig E A B,
    sub_plain n Sig E A B = true -> sub_plain m Sig E A B = true.
Proof. intros; eapply sub_plain_mono; eauto. Qed.


Theorem decidability : forall A B E,
{sub E A B} + {~ sub E A B}.
