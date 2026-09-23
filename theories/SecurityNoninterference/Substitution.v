From AutoProof.SecurityNoninterference Require Export Metatheory.
Import ListNotations.

Definition term_substitution := atom -> tm.

Fixpoint instantiate (rho : term_substitution) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => rho x
  | tm_unit k => tm_unit k
  | tm_abs T body k => tm_abs T (instantiate rho body) k
  | tm_app t1 t2 r => tm_app (instantiate rho t1) (instantiate rho t2) r
  | tm_pair t1 t2 k => tm_pair (instantiate rho t1) (instantiate rho t2) k
  | tm_fst t r => tm_fst (instantiate rho t) r
  | tm_snd t r => tm_snd (instantiate rho t) r
  | tm_inl t k => tm_inl (instantiate rho t) k
  | tm_inr t k => tm_inr (instantiate rho t) k
  | tm_case t b1 b2 r => tm_case (instantiate rho t)
      (instantiate rho b1) (instantiate rho b2) r
  | tm_protect l t => tm_protect l (instantiate rho t)
  end.

Definition substitution_update (rho : term_substitution) (x : atom) (u : tm)
    : term_substitution := fun y => if Nat.eqb x y then u else rho y.

Lemma fv_open_includes : forall t k u x,
  In x (fv t) -> In x (fv (open_rec k u t)).
Proof.
  induction t; intros k u x H; simpl in *; try contradiction;
    repeat rewrite in_app_iff in *; intuition eauto.
Qed.

Lemma lookup_context_key : forall Gamma x T,
  lookup_context x Gamma = Some T -> In x (map fst Gamma).
Proof.
  induction Gamma as [|[y U] Gamma IH]; intros x T H; simpl in *; [discriminate |].
  destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E. auto.
  - right. eapply IH; exact H.
Qed.

Lemma context_included_fresh_update : forall Gamma x T,
  ~ In x (map fst Gamma) -> context_included Gamma (update Gamma x T).
Proof.
  intros Gamma x T Hfresh y U Hlookup.
  rewrite lookup_update_neq; [exact Hlookup |].
  intro E. subst y. apply Hfresh. eapply lookup_context_key; exact Hlookup.
Qed.

Lemma typing_substitution_update : forall Gamma Gamma' rho x A,
  (forall y U, lookup_context y Gamma = Some U -> has_type Gamma' (rho y) U) ->
  ~ In x (map fst Gamma') -> wf_ty A ->
  forall y U, lookup_context y (update Gamma x A) = Some U ->
  has_type (update Gamma' x A) (substitution_update rho x (tm_fvar x) y) U.
Proof.
  intros Gamma Gamma' rho x A Hmap Hfresh Hwf y U Hlookup.
  unfold substitution_update. destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E. subst y. rewrite lookup_update_eq in Hlookup.
    inversion Hlookup; subst U. apply T_Var; [apply lookup_update_eq | exact Hwf].
  - apply Nat.eqb_neq in E. rewrite lookup_update_neq in Hlookup by congruence.
    eapply typing_weaken; [apply Hmap; exact Hlookup |].
    apply context_included_fresh_update; exact Hfresh.
Qed.

Lemma typing_free_variable : forall Gamma t T,
  has_type Gamma t T -> forall x, In x (fv t) ->
  exists U, lookup_context x Gamma = Some U.
Proof.
  intros Gamma t T Ht. induction Ht; intros z Hz; simpl in Hz;
    repeat rewrite in_app_iff in Hz; try contradiction; try solve [intuition eauto].
  - destruct Hz as [<- | []]. eauto.
  - destruct (fresh_atom (z :: L)) as [x Hx].
    assert (x <> z /\ ~ In x L) as [Hneq Hfresh] by (simpl in Hx; intuition congruence).
    destruct (H2 x Hfresh z (fv_open_includes _ 0 _ _ Hz)) as [U HU].
    rewrite lookup_update_neq in HU by congruence. eauto.
  - destruct Hz as [Hz | [Hz | Hz]].
    + eauto.
    + destruct (fresh_atom (z :: L)) as [x Hx].
      assert (x <> z /\ ~ In x L) as [Hneq Hfresh] by (simpl in Hx; intuition congruence).
      destruct (H1 x Hfresh z (fv_open_includes _ 0 _ _ Hz)) as [U HU].
      rewrite lookup_update_neq in HU by congruence. eauto.
    + destruct (fresh_atom (z :: L)) as [x Hx].
      assert (x <> z /\ ~ In x L) as [Hneq Hfresh] by (simpl in Hx; intuition congruence).
      destruct (H3 x Hfresh z (fv_open_includes _ 0 _ _ Hz)) as [U HU].
      rewrite lookup_update_neq in HU by congruence. eauto.
Qed.

Lemma instantiate_ext : forall t rho sigma,
  (forall x, In x (fv t) -> rho x = sigma x) ->
  instantiate rho t = instantiate sigma t.
Proof.
  induction t; intros rho sigma H; simpl in *; try reflexivity;
    try (f_equal; apply IHt; exact H);
    try (f_equal; [apply IHt1 | apply IHt2]);
    try (f_equal; [apply IHt1 | apply IHt2 | apply IHt3]);
    try (intros x Hx; apply H; repeat rewrite in_app_iff; tauto).
  apply H. auto.
Qed.

Lemma instantiate_open : forall t rho k u,
  (forall x, In x (fv t) -> locally_closed (rho x)) ->
  instantiate rho (open_rec k u t) = open_rec k (instantiate rho u) (instantiate rho t).
Proof.
  induction t; intros rho k u H; simpl in *; try reflexivity.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. apply (open_rec_lc_at (rho a) 0 k (instantiate rho u)).
    + apply H. auto.
    + apply Nat.le_0_l.
  - f_equal. apply IHt; exact H.
  - f_equal; [apply IHt1 | apply IHt2]; intros x Hx;
      apply H; rewrite in_app_iff; tauto.
  - f_equal; [apply IHt1 | apply IHt2]; intros x Hx;
      apply H; rewrite in_app_iff; tauto.
  - f_equal. apply IHt; exact H.
  - f_equal. apply IHt; exact H.
  - f_equal. apply IHt; exact H.
  - f_equal. apply IHt; exact H.
  - f_equal; [apply IHt1 | apply IHt2 | apply IHt3]; intros x Hx;
      apply H; repeat rewrite in_app_iff; tauto.
  - f_equal. apply IHt; exact H.
Qed.

Lemma instantiate_open_update : forall body rho x u,
  ~ In x (fv body) ->
  (forall y, In y (fv body) -> locally_closed (rho y)) ->
  instantiate (substitution_update rho x u) (open body (tm_fvar x)) =
  open (instantiate rho body) u.
Proof.
  intros body rho x u Hfresh Hlc. unfold open.
  rewrite instantiate_open.
  - simpl. unfold substitution_update at 1. rewrite Nat.eqb_refl.
    f_equal. apply instantiate_ext. intros y Hy.
    unfold substitution_update. destruct (Nat.eqb x y) eqn:E; [|reflexivity].
    apply Nat.eqb_eq in E. subst y. contradiction.
  - intros y Hy. unfold substitution_update. destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. subst y. contradiction.
    + apply Hlc; exact Hy.
Qed.

Lemma typing_substitution_lc : forall Gamma t T Gamma' rho,
  has_type Gamma t T ->
  (forall x U, lookup_context x Gamma = Some U -> has_type Gamma' (rho x) U) ->
  forall x, In x (fv t) -> locally_closed (rho x).
Proof.
  intros Gamma t T Gamma' rho Ht Hmap x Hx.
  destruct (typing_free_variable _ _ _ Ht x Hx) as [U HU].
  exact (proj1 (typing_regular _ _ _ (Hmap x U HU))).
Qed.

Lemma typing_instantiate : forall Gamma t T,
  has_type Gamma t T -> forall Gamma' rho,
  (forall x U, lookup_context x Gamma = Some U -> has_type Gamma' (rho x) U) ->
  has_type Gamma' (instantiate rho t) T.
Proof.
  intros Gamma t T Ht. induction Ht; intros Gamma' rho Hmap; simpl.
  - apply Hmap; exact H.
  - apply T_Unit; exact H.
  - apply T_Abs with (L := L ++ fv body ++ map fst Gamma'); try assumption.
    intros x Hfresh. repeat rewrite in_app_iff in Hfresh.
    rewrite <- instantiate_open_update with (x := x) by
      (first [tauto | eapply typing_substitution_lc with
        (t := tm_abs T1 body kappa) (T := Ty_Arrow T1 T2 kappa);
        [eapply T_Abs; eassumption | exact Hmap]]).
    apply H2; [tauto |]. apply typing_substitution_update; tauto.
  - eapply T_App; eauto.
  - apply T_Pair; eauto.
  - eapply T_Fst; eauto.
  - eapply T_Snd; eauto.
  - apply T_Inl; eauto.
  - apply T_Inr; eauto.
  - eapply T_Case with (L := L ++ fv body1 ++ fv body2 ++ map fst Gamma');
      [eapply IHHt; exact Hmap | exact H | |].
    + intros x Hfresh. repeat rewrite in_app_iff in Hfresh.
      rewrite <- instantiate_open_update with (x := x) by
        (first [tauto | intros y Hy; eapply typing_substitution_lc with
          (t := tm_case t body1 body2 r) (T := ty_protect kappa.(indirect_reader) T);
          [eapply T_Case; eassumption | exact Hmap | simpl; repeat rewrite in_app_iff; tauto]]).
      apply H1; [tauto |]. apply typing_substitution_update; try tauto.
      exact (proj1 (proj2 (typing_regular _ _ _ Ht))).
    + intros x Hfresh. repeat rewrite in_app_iff in Hfresh.
      rewrite <- instantiate_open_update with (x := x) by
        (first [tauto | intros y Hy; eapply typing_substitution_lc with
          (t := tm_case t body1 body2 r) (T := ty_protect kappa.(indirect_reader) T);
          [eapply T_Case; eassumption | exact Hmap | simpl; repeat rewrite in_app_iff; tauto]]).
      apply H3; [tauto |]. apply typing_substitution_update; try tauto.
      exact (proj1 (proj2 (proj2 (typing_regular _ _ _ Ht)))).
  - apply T_Protect; eauto.
  - eapply T_Sub; eauto.
Qed.

Lemma erase_instantiate : forall t rho,
  erase_security (instantiate rho t) =
  instantiate (fun x => erase_security (rho x)) (erase_security t).
Proof. induction t; intros rho; simpl; f_equal; auto. Qed.

Lemma lookup_erase_context_inv : forall Gamma x U,
  lookup_context x (erase_context Gamma) = Some U ->
  exists T, lookup_context x Gamma = Some T /\ U = erase_type T.
Proof.
  induction Gamma as [|[y T] Gamma IH]; intros x U H; simpl in *; [discriminate |].
  destruct (Nat.eqb x y); [inversion H; subst; eauto | apply IH; exact H].
Qed.

Lemma typing_instantiate_erased : forall Gamma t T rho,
  has_type Gamma t T ->
  (forall x U, lookup_context x Gamma = Some U ->
    has_type empty (erase_security (rho x)) (erase_type U)) ->
  has_type empty (erase_security (instantiate rho t)) (erase_type T).
Proof.
  intros Gamma t T rho Ht Hmap. rewrite erase_instantiate.
  eapply typing_instantiate; [apply typing_erasure; exact Ht |].
  intros x U HU. destruct (lookup_erase_context_inv _ _ _ HU) as [V [HV ->]].
  apply Hmap; exact HV.
Qed.

Lemma erase_lc_inv : forall t k, lc_at k (erase_security t) -> lc_at k t.
Proof. induction t; intros k H; simpl in *; intuition eauto. Qed.

Lemma instantiate_identity : forall t, instantiate tm_fvar t = t.
Proof. induction t; simpl; f_equal; assumption. Qed.

Lemma instantiate_closed : forall t T rho,
  has_type empty t T -> instantiate rho t = t.
Proof.
  intros t T rho Ht. rewrite <- (instantiate_identity t) at 2.
  apply instantiate_ext. intros x Hx.
  destruct (typing_free_variable _ _ _ Ht x Hx) as [U HU]. discriminate HU.
Qed.

Lemma instantiate_single : forall t x u,
  instantiate (substitution_update tm_fvar x u) t = subst x u t.
Proof. induction t; intros x u; simpl; try reflexivity; f_equal; auto. Qed.
