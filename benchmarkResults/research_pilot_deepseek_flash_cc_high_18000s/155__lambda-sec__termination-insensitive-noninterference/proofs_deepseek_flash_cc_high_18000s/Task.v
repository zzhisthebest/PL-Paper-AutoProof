From stdpp Require Import relations.
From stdpp Require Import fin_maps.

From logrel_ifc.lambda_sec Require Export lang typing.

From logrel_ifc.lambda_sec Require Import lattice.

From Stdlib Require Import Arith.Wf_nat Lia.

Section soundness.

Context `{SecurityLattice label}.

(* ------------------------------------------------------------------ *)
(* Order facts for the security lattice.                               *)
(* ------------------------------------------------------------------ *)

Local Instance lat_equiv_refl : Reflexive (@equiv label lattice).
Proof. destruct lat_equiv_equiv as [R S T]. exact R. Qed.
Local Instance lat_equiv_sym : Symmetric (@equiv label lattice).
Proof. destruct lat_equiv_equiv as [R S T]. exact S. Qed.
Local Instance lat_equiv_trans : Transitive (@equiv label lattice).
Proof. destruct lat_equiv_equiv as [R S T]. exact T. Qed.

Lemma join_congr : forall a a' b b' : label, a ≡ a' -> b ≡ b' -> a ⊔ b ≡ a' ⊔ b'.
Proof. intros. eapply (@join_proper label _). eauto. eauto. Qed.

Lemma order_join_l : forall a b : label, a ⊑ a ⊔ b.
Proof.
  intros a b. unfold order.
  transitivity ((a ⊔ a) ⊔ b).
  - apply (@join_associative label _ a a b).
  - apply join_congr. apply (@join_idempotent label _ a). reflexivity.
Qed.

Lemma order_join_r : forall a b : label, b ⊑ a ⊔ b.
Proof.
  intros a b. unfold order.
  transitivity (b ⊔ (b ⊔ a)).
  - apply join_congr. reflexivity. apply (@join_commutative label _ a b).
  - transitivity ((b ⊔ b) ⊔ a).
    + apply (@join_associative label _ b b a).
    + transitivity (b ⊔ a).
      * apply join_congr. apply (@join_idempotent label _ b). reflexivity.
      * apply (@join_commutative label _ b a).
Qed.

Lemma order_refl : forall a : label, a ⊑ a.
Proof. intros a. unfold order. apply (@join_idempotent label _ a). Qed.

Lemma order_trans : forall a b c : label, a ⊑ b -> b ⊑ c -> a ⊑ c.
Proof.
  intros a b c Hab Hbc. unfold order in *.
  transitivity (a ⊔ (b ⊔ c)).
  - apply join_congr. reflexivity. symmetry. exact Hbc.
  - transitivity ((a ⊔ b) ⊔ c).
    + apply (@join_associative label _ a b c).
    + transitivity (b ⊔ c).
      * apply join_congr. exact Hab. reflexivity.
      * exact Hbc.
Qed.

Lemma order_join_lub : forall a b c : label, a ⊑ c -> b ⊑ c -> a ⊔ b ⊑ c.
Proof.
  intros a b c Ha Hb. unfold order in *.
  transitivity (a ⊔ (b ⊔ c)).
  - symmetry. apply (@join_associative label _ a b c).
  - transitivity (a ⊔ c).
    + apply join_congr. reflexivity. exact Hb.
    + exact Ha.
Qed.

Lemma order_bot : forall a : label, ⊥ ⊑ a.
Proof. intros a. unfold order. apply (@bot_left_id label _ a). Qed.

Lemma order_top : forall a : label, a ⊑ ⊤.
Proof. intros a. unfold order. apply (@top_right_absorb label _ a). Qed.

(* ------------------------------------------------------------------ *)
(* Label-term semantics and soundness of the syntactic flow relation.  *)
(* ------------------------------------------------------------------ *)

Fixpoint interp_label (rho : var -> label) (l : label_term) : label :=
  match l with
  | LVar x => rho x
  | LJoin a b => interp_label rho a ⊔ interp_label rho b
  | LLabel x => x
  end.

Lemma interp_label_subst (rho : var -> label) (sigma : var -> label_term)
    (l : label_term) :
  interp_label rho l.[sigma] = interp_label (fun x => interp_label rho (sigma x)) l.
Proof. induction l; simpl; f_equal; assumption. Qed.

Lemma interp_label_ren (rho : var -> label) (xi : var -> var) (l : label_term) :
  interp_label rho l.[ren xi] = interp_label (fun x => rho (xi x)) l.
Proof. induction l; simpl; f_equal; assumption. Qed.

Lemma flowsto_sound (rho : var -> label) (l1 l2 : label_term) :
  l1 ⊑ₛ l2 -> interp_label rho l1 ⊑ interp_label rho l2.
Proof.
  induction 1; simpl.
  - apply order_refl.
  - eapply order_trans; eauto.
  - apply order_bot.
  - apply order_top.
  - assumption.
  - apply order_join_lub; assumption.
Qed.

(* The observer-visible (low) labels. *)
Definition obs (l : label) : Prop := l ⊑ ζ.

Lemma obs_bot : obs ⊥.
Proof. unfold obs. apply order_bot. Qed.

Lemma obs_join : forall a b, obs a -> obs b -> obs (a ⊔ b).
Proof. intros a b Ha Hb. unfold obs in *. apply order_join_lub; assumption. Qed.

Lemma obs_of_low : forall a, a ⊑ ζ -> obs a.
Proof. intros a Ha. exact Ha. Qed.

Lemma obs_under_flow : forall a b, obs a -> a ⊑ b -> b ⊑ ζ -> obs b.
Proof. intros a b Ha Hab Hb. exact Hb. Qed.

Lemma high_not_below_low (a b : label) :
  a ⋢ ζ -> b ⊑ ζ -> a ⋢ b.
Proof.
  intros Ha Hb Hab.
  apply Ha. eapply order_trans; eauto.
Qed.

Definition sectype_label (tau : sectype) : label_term :=
  let: t @ l := tau in l.

Lemma sectype_label_hsubst_label (sigma : var -> label_term) (tau : sectype) :
  sectype_label (hsubst_label_sectype sigma tau) = (sectype_label tau).[sigma].
Proof. destruct tau. reflexivity. Qed.

Lemma sectype_label_hsubst_type (sigma : var -> type) (tau : sectype) :
  sectype_label (hsubst_sectype sigma tau) = sectype_label tau.
Proof. destruct tau. reflexivity. Qed.

Lemma sectype_label_rename (xi : var -> var) (tau : sectype) :
  sectype_label (rename_sectype xi tau) = sectype_label tau.
Proof. destruct tau. reflexivity. Qed.

Lemma type_flowsto_sound (rho : var -> label) (tau : sectype) (l : label_term) :
  tau ↘ l -> interp_label rho l ⊑ interp_label rho (sectype_label tau).
Proof.
  destruct tau as [t l0]. simpl. intro Hf.
  apply flowsto_sound. exact Hf.
Qed.

Lemma secsubtype_label_flow (t : type) (l : label_term) (t' : type) (l' : label_term) :
  secsubtype (t @ l) (t' @ l') -> l ⊑ₛ l'.
Proof.
  intro Hs. inversion Hs as [l0 l1 t0 t1 Hflow Hsub]; subst. exact Hflow.
Qed.

Lemma secsubtype_label_sound (rho : var -> label) (t : type) (l : label_term)
    (t' : type) (l' : label_term) :
  secsubtype (t @ l) (t' @ l') -> interp_label rho l ⊑ interp_label rho l'.
Proof. intros Hs. apply flowsto_sound. apply secsubtype_label_flow in Hs. exact Hs. Qed.

(* ------------------------------------------------------------------ *)
(* Inversion of subtyping at base types.                               *)
(* ------------------------------------------------------------------ *)

Lemma subtype_bool_source (t1 t2 : type) :
  subtype t1 t2 -> t2 = TBool -> t1 = TBool.
Proof.
  intros Hs. induction Hs; intros Heq; try discriminate; try exact Heq;
  try reflexivity; try (subst; eauto).
Qed.

Lemma subtype_bool_target (t1 t2 : type) :
  subtype t1 t2 -> t1 = TBool -> t2 = TBool.
Proof.
  intros Hs. induction Hs; intros Heq; try discriminate; try exact Heq;
  try reflexivity; try (subst; eauto).
Qed.

Lemma secsubtype_bool_target (t : type) (l l' : label_term) :
  secsubtype (t @ l) (TBool @ l') -> t = TBool.
Proof.
  intro Hs. inversion Hs as [l0 l1 t0 t1 Hflow Hsub]; subst.
  eapply subtype_bool_source; eauto.
Qed.

Lemma secsubtype_bool_source (t : type) (l l' : label_term) :
  secsubtype (TBool @ l) (t @ l') -> t = TBool.
Proof.
  intro Hs. inversion Hs as [l0 l1 t0 t1 Hflow Hsub]; subst.
  eapply subtype_bool_target; eauto.
Qed.

Lemma subtype_ref_source (t1 t2 : type) :
  subtype t1 t2 -> (exists τ, t2 = TRef τ) -> exists τ, t1 = TRef τ.
Proof. intros Hs. induction Hs; intros [a Heq]; subst; try discriminate.
  all: try (repeat eexists; reflexivity).
  all: eapply IHHs1; eapply IHHs2; repeat eexists; reflexivity. Qed.
Lemma subtype_arrow_source (t1 t2 : type) :
  subtype t1 t2 -> (exists l τ1 τ2, t2 = TArrow l τ1 τ2) ->
  exists l τ1 τ2, t1 = TArrow l τ1 τ2.
Proof. intros Hs. induction Hs; intros [l0 [a [b Heq]]]; subst; try discriminate.
  all: try (repeat eexists; reflexivity).
  all: eapply IHHs1; eapply IHHs2; repeat eexists; reflexivity. Qed.
Lemma subtype_prod_source (t1 t2 : type) :
  subtype t1 t2 -> (exists τ1 τ2, t2 = TProd τ1 τ2) ->
  exists τ1 τ2, t1 = TProd τ1 τ2.
Proof. intros Hs. induction Hs; intros [a [b Heq]]; subst; try discriminate.
  all: try (repeat eexists; reflexivity).
  all: eapply IHHs1; eapply IHHs2; repeat eexists; reflexivity. Qed.
Lemma subtype_sum_source (t1 t2 : type) :
  subtype t1 t2 -> (exists τ1 τ2, t2 = TSum τ1 τ2) ->
  exists τ1 τ2, t1 = TSum τ1 τ2.
Proof. intros Hs. induction Hs; intros [a [b Heq]]; subst; try discriminate.
  all: try (repeat eexists; reflexivity).
  all: eapply IHHs1; eapply IHHs2; repeat eexists; reflexivity. Qed.
Lemma subtype_forall_source (t1 t2 : type) :
  subtype t1 t2 -> (exists l τ, t2 = TForall l τ) ->
  exists l τ, t1 = TForall l τ.
Proof. intros Hs. induction Hs; intros [l0 [a Heq]]; subst; try discriminate.
  all: try (repeat eexists; reflexivity).
  all: eapply IHHs1; eapply IHHs2; repeat eexists; reflexivity. Qed.
Lemma subtype_lforall_source (t1 t2 : type) :
  subtype t1 t2 -> (exists l τ, t2 = TLForall l τ) ->
  exists l τ, t1 = TLForall l τ.
Proof. intros Hs. induction Hs; intros [l0 [a Heq]]; subst; try discriminate.
  all: try (repeat eexists; reflexivity).
  all: eapply IHHs1; eapply IHHs2; repeat eexists; reflexivity. Qed.
Lemma subtype_exist_source (t1 t2 : type) :
  subtype t1 t2 -> (exists τ, t2 = TExist τ) -> exists τ, t1 = TExist τ.
Proof. intros Hs. induction Hs; intros [a Heq]; subst; try discriminate.
  all: try (repeat eexists; reflexivity).
  all: eapply IHHs1; eapply IHHs2; repeat eexists; reflexivity. Qed.
Lemma subtype_rec_source (t1 t2 : type) :
  subtype t1 t2 -> (exists τ, t2 = TRec τ) -> exists τ, t1 = TRec τ.
Proof. intros Hs. induction Hs; intros [a Heq]; subst; try discriminate.
  all: try (repeat eexists; reflexivity).
  all: eapply IHHs1; eapply IHHs2; repeat eexists; reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Expression substitution lemmas (Autosubst).                         *)
(* ------------------------------------------------------------------ *)

Global Instance SubstLemmas_expr_inst : SubstLemmas expr := ltac:(derive).

Lemma expr_subst_comp (e : expr) (sigma tau : var -> expr) :
  e.[sigma].[tau] = e.[sigma >> tau].
Proof. apply subst_comp. Qed.

Lemma expr_subst_id (e : expr) : e.[ids] = e.
Proof. apply subst_id. Qed.

Fixpoint closed_under (n : nat) (e : expr) : Prop :=
  match e with
  | Var x => x < n
  | Lam b => closed_under (S n) b
  | App e1 e2 => closed_under n e1 /\ closed_under n e2
  | LetIn e1 e2 => closed_under n e1 /\ closed_under (S n) e2
  | Seq e1 e2 => closed_under n e1 /\ closed_under n e2
  | Unit => True
  | Bool _ => True
  | Nat _ => True
  | BinOp _ e1 e2 => closed_under n e1 /\ closed_under n e2
  | If e0 e1 e2 => closed_under n e0 /\ closed_under n e1 /\ closed_under n e2
  | Pair e1 e2 => closed_under n e1 /\ closed_under n e2
  | Proj1 e => closed_under n e
  | Proj2 e => closed_under n e
  | InjL e => closed_under n e
  | InjR e => closed_under n e
  | Case e0 e1 e2 => closed_under n e0 /\ closed_under (S n) e1 /\ closed_under (S n) e2
  | Loc _ => True
  | Alloc e => closed_under n e
  | Store e1 e2 => closed_under n e1 /\ closed_under n e2
  | Load e => closed_under n e
  | TLam e => closed_under n e
  | TApp e => closed_under n e
  | TLLam e => closed_under n e
  | TLApp e => closed_under n e
  | Pack e => closed_under n e
  | Unpack e1 e2 => closed_under n e1 /\ closed_under (S n) e2
  | Fold e => closed_under n e
  | Unfold e => closed_under n e
  end.

Definition closed_expr (e : expr) : Prop := closed_under 0 e.

Lemma closed_under_mono : forall n m e, n <= m -> closed_under n e -> closed_under m e.
Proof.
  intros n0 m0 e. revert n0 m0.
  induction e; intros n0 m0 Hle Hc; simpl in *.
  - lia.
  - apply (IHe (S n0) (S m0)); [lia|exact Hc].
  - destruct Hc as [H1 H2]. split;
      [apply (IHe1 n0 m0); auto|apply (IHe2 n0 m0); auto].
  - destruct Hc as [H1 H2]. split.
    + apply (IHe n0 m0); auto.
    + apply (IHe0 (S n0) (S m0)); [lia|exact H2].
  - destruct Hc as [H1 H2]. split;
      [apply (IHe1 n0 m0); auto|apply (IHe2 n0 m0); auto].
  - exact I.
  - exact I.
  - exact I.
  - destruct Hc as [H1 H2]. split;
      [apply (IHe1 n0 m0); auto|apply (IHe2 n0 m0); auto].
  - destruct Hc as [H0 [H1 H2]]. split.
    + apply (IHe1 n0 m0); auto.
    + split.
      * apply (IHe2 n0 m0); auto.
      * apply (IHe3 n0 m0); auto.
  - destruct Hc as [H1 H2]. split;
      [apply (IHe1 n0 m0); auto|apply (IHe2 n0 m0); auto].
  - apply (IHe n0 m0); auto.
  - apply (IHe n0 m0); auto.
  - apply (IHe n0 m0); auto.
  - apply (IHe n0 m0); auto.
  - destruct Hc as [H0 [H1 H2]]. split.
    + apply (IHe n0 m0); auto.
    + split.
      * apply (IHe0 (S n0) (S m0)); [lia|exact H1].
      * apply (IHe1 (S n0) (S m0)); [lia|exact H2].
  - exact I.
  - apply (IHe n0 m0); auto.
  - destruct Hc as [H1 H2]. split;
      [apply (IHe1 n0 m0); auto|apply (IHe2 n0 m0); auto].
  - apply (IHe n0 m0); auto.
  - apply (IHe n0 m0); auto.
  - apply (IHe n0 m0); auto.
  - apply (IHe n0 m0); auto.
  - apply (IHe n0 m0); auto.
  - apply (IHe n0 m0); auto.
  - destruct Hc as [H1 H2]. split.
    + apply (IHe n0 m0); auto.
    + apply (IHe0 (S n0) (S m0)); [lia|exact H2].
  - apply (IHe n0 m0); auto.
  - apply (IHe n0 m0); auto.
Qed.

Lemma closed_under_subst_agree : forall n e (s t : var -> expr),
  closed_under n e ->
  (forall x, x < n -> s x = t x) ->
  e.[s] = e.[t].
Proof.
  intros n0 e. revert n0.
  induction e; intros n0 s t Hc Hag; simpl in *.
  - apply Hag. exact Hc.
  - f_equal. apply (IHe (S n0) (up s) (up t)); auto.
    intros x Hx. destruct x; unfold up; simpl; auto.
    f_equal. apply Hag. lia.
  - destruct Hc as [H1 H2].
    assert (E1 : e1.[s] = e1.[t]) by (apply (IHe1 n0 s t); auto).
    assert (E2 : e2.[s] = e2.[t]) by (apply (IHe2 n0 s t); auto).
    now rewrite E1, E2.
  - destruct Hc as [H1 H2].
    assert (E1 : e.[s] = e.[t]) by (apply (IHe n0 s t); auto).
    assert (E2 : e2.[up s] = e2.[up t]).
    { apply (IHe0 (S n0) (up s) (up t)); auto.
      intros x Hx. destruct x; unfold up; simpl; auto. f_equal. apply Hag. lia. }
    now rewrite E1, E2.
  - destruct Hc as [H1 H2].
    assert (E1 : e1.[s] = e1.[t]) by (apply (IHe1 n0 s t); auto).
    assert (E2 : e2.[s] = e2.[t]) by (apply (IHe2 n0 s t); auto).
    now rewrite E1, E2.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - destruct Hc as [H1 H2].
    assert (E1 : e1.[s] = e1.[t]) by (apply (IHe1 n0 s t); auto).
    assert (E2 : e2.[s] = e2.[t]) by (apply (IHe2 n0 s t); auto).
    now rewrite E1, E2.
  - destruct Hc as [H1 [H2 H3]].
    assert (E1 : e1.[s] = e1.[t]) by (apply (IHe1 n0 s t); auto).
    assert (E2 : e2.[s] = e2.[t]) by (apply (IHe2 n0 s t); auto).
    assert (E3 : e3.[s] = e3.[t]) by (apply (IHe3 n0 s t); auto).
    now rewrite E1, E2, E3.
  - destruct Hc as [H1 H2].
    assert (E1 : e1.[s] = e1.[t]) by (apply (IHe1 n0 s t); auto).
    assert (E2 : e2.[s] = e2.[t]) by (apply (IHe2 n0 s t); auto).
    now rewrite E1, E2.
  - f_equal; apply (IHe n0 s t); auto.
  - f_equal; apply (IHe n0 s t); auto.
  - f_equal; apply (IHe n0 s t); auto.
  - f_equal; apply (IHe n0 s t); auto.
  - destruct Hc as [H0 [H1 H2]].
    assert (E0 : e.[s] = e.[t]) by (apply (IHe n0 s t); auto).
    assert (E1 : e1.[up s] = e1.[up t]).
    { apply (IHe0 (S n0) (up s) (up t)); auto.
      intros x Hx. destruct x; unfold up; simpl; auto. f_equal. apply Hag. lia. }
    assert (E2 : e2.[up s] = e2.[up t]).
    { apply (IHe1 (S n0) (up s) (up t)); auto.
      intros x Hx. destruct x; unfold up; simpl; auto. f_equal. apply Hag. lia. }
    now rewrite E0, E1, E2.
  - reflexivity.
  - f_equal; apply (IHe n0 s t); auto.
  - destruct Hc as [H1 H2].
    assert (E1 : e1.[s] = e1.[t]) by (apply (IHe1 n0 s t); auto).
    assert (E2 : e2.[s] = e2.[t]) by (apply (IHe2 n0 s t); auto).
    now rewrite E1, E2.
  - f_equal; apply (IHe n0 s t); auto.
  - f_equal; apply (IHe n0 s t); auto.
  - f_equal; apply (IHe n0 s t); auto.
  - f_equal; apply (IHe n0 s t); auto.
  - f_equal; apply (IHe n0 s t); auto.
  - f_equal; apply (IHe n0 s t); auto.
  - destruct Hc as [H1 H2].
    assert (E1 : e.[s] = e.[t]) by (apply (IHe n0 s t); auto).
    assert (E2 : e2.[up s] = e2.[up t]).
    { apply (IHe0 (S n0) (up s) (up t)); auto.
      intros x Hx. destruct x; unfold up; simpl; auto. f_equal. apply Hag. lia. }
    now rewrite E1, E2.
  - f_equal; apply (IHe n0 s t); auto.
  - f_equal; apply (IHe n0 s t); auto.
Qed.

Lemma closed_expr_any_subst : forall e (sigma : var -> expr),
  closed_expr e -> e.[sigma] = e.
Proof.
  intros e sigma Hc. unfold closed_expr in Hc.
  transitivity (e.[ids]).
  - symmetry. apply (closed_under_subst_agree 0 e ids sigma); auto.
    intros x Hx. lia.
  - apply subst_id.
Qed.

Lemma closed_under_subst_self : forall n e (sigma : var -> expr),
  closed_under n e ->
  (forall x, x < n -> sigma x = Var x) ->
  e.[sigma] = e.
Proof.
  intros n e sigma Hc Hag.
  transitivity (e.[ids]).
  - apply (closed_under_subst_agree n e sigma ids); auto.
  - apply subst_id.
Qed.

Lemma up_ext (s t : var -> expr) :
  (forall x, s x = t x) -> forall x, up s x = up t x.
Proof.
  intros Hs x. unfold up. destruct x; simpl; auto.
  rewrite Hs. reflexivity.
Qed.

Lemma subst_ext (e : expr) : forall (s t : var -> expr),
  (forall x, s x = t x) -> e.[s] = e.[t].
Proof.
  induction e; intros s t Hs; simpl; try reflexivity;
  try (erewrite IHe; eauto using up_ext);
  try (erewrite IHe1; eauto using up_ext);
  try (erewrite IHe2; eauto using up_ext);
  try (erewrite IHe3; eauto using up_ext);
  try (f_equal; eauto using up_ext);
  try (apply Hs).
Qed.

Lemma up_subst_beta (b : expr) (sigma : var -> expr) (w : expr) :
  (forall x, closed_expr (sigma x)) ->
  (b.[up sigma]).[w .: ids] = b.[w .: sigma].
Proof.
  intros Hs.
  rewrite (expr_subst_comp b (up sigma) (w .: ids)).
  apply subst_ext. intro x.
  destruct x as [|n].
  - unfold up. simpl. reflexivity.
  - unfold up. simpl.
    rewrite rename_subst.
    rewrite (closed_expr_any_subst (sigma n) (ren (+1)) (Hs n)).
    rewrite (closed_expr_any_subst (sigma n) (w .: ids) (Hs n)).
    reflexivity.
Qed.

Lemma closed_under_ren : forall n m (xi : var -> var) e,
  (forall x, x < n -> xi x < m) ->
  closed_under n e -> closed_under m (rename xi e).
Proof.
  intros n0 m0 xi e. revert n0 m0 xi.
  induction e; intros n0 m0 xi Hxi Hc; simpl in *.
  - apply Hxi. exact Hc.
  - apply (IHe (S n0) (S m0) (upren xi)).
    + intros x Hx. destruct x as [|y].
      * simpl. lia.
      * simpl. assert (Hy : y < n0) by lia. specialize (Hxi y Hy). lia.
    + exact Hc.
  - destruct Hc as [H1 H2]. split.
    + apply (IHe1 n0 m0 xi); auto.
    + apply (IHe2 n0 m0 xi); auto.
  - destruct Hc as [H1 H2]. split.
    + apply (IHe n0 m0 xi); auto.
    + apply (IHe0 (S n0) (S m0) (upren xi)).
      * intros x Hx. destruct x as [|y].
        -- simpl. lia.
        -- simpl. assert (Hy : y < n0) by lia. specialize (Hxi y Hy). lia.
      * exact H2.
  - destruct Hc as [H1 H2]. split.
    + apply (IHe1 n0 m0 xi); auto.
    + apply (IHe2 n0 m0 xi); auto.
  - exact I.
  - exact I.
  - exact I.
  - destruct Hc as [H1 H2]. split.
    + apply (IHe1 n0 m0 xi); auto.
    + apply (IHe2 n0 m0 xi); auto.
  - destruct Hc as [H1 [H2 H3]]. split.
    + apply (IHe1 n0 m0 xi); auto.
    + split.
      * apply (IHe2 n0 m0 xi); auto.
      * apply (IHe3 n0 m0 xi); auto.
  - destruct Hc as [H1 H2]. split.
    + apply (IHe1 n0 m0 xi); auto.
    + apply (IHe2 n0 m0 xi); auto.
  - apply (IHe n0 m0 xi); auto.
  - apply (IHe n0 m0 xi); auto.
  - apply (IHe n0 m0 xi); auto.
  - apply (IHe n0 m0 xi); auto.
  - destruct Hc as [H1 [H2 H3]]. split.
    + apply (IHe n0 m0 xi); auto.
    + split.
      * apply (IHe0 (S n0) (S m0) (upren xi)).
        { intros x Hx. destruct x as [|y].
          - simpl. lia.
          - simpl. assert (Hy : y < n0) by lia. specialize (Hxi y Hy). lia. }
        exact H2.
      * apply (IHe1 (S n0) (S m0) (upren xi)).
        { intros x Hx. destruct x as [|y].
          - simpl. lia.
          - simpl. assert (Hy : y < n0) by lia. specialize (Hxi y Hy). lia. }
        exact H3.
  - exact I.
  - apply (IHe n0 m0 xi); auto.
  - destruct Hc as [H1 H2]. split.
    + apply (IHe1 n0 m0 xi); auto.
    + apply (IHe2 n0 m0 xi); auto.
  - apply (IHe n0 m0 xi); auto.
  - apply (IHe n0 m0 xi); auto.
  - apply (IHe n0 m0 xi); auto.
  - apply (IHe n0 m0 xi); auto.
  - apply (IHe n0 m0 xi); auto.
  - apply (IHe n0 m0 xi); auto.
  - destruct Hc as [H1 H2]. split.
    + apply (IHe n0 m0 xi); auto.
    + apply (IHe0 (S n0) (S m0) (upren xi)).
      { intros x Hx. destruct x as [|y].
        - simpl. lia.
        - simpl. assert (Hy : y < n0) by lia. specialize (Hxi y Hy). lia. }
      exact H2.
  - apply (IHe n0 m0 xi); auto.
  - apply (IHe n0 m0 xi); auto.
Qed.

Lemma closed_under_subst_under : forall n e (s : var -> expr),
  closed_under n e ->
  (forall x, x < n -> closed_under n (s x)) ->
  closed_under n (e.[s]).
Proof.
  intros n0 e. revert n0. induction e; intros n0 s Hc Hs; simpl in *.
  - apply Hs. exact Hc.
  - apply (IHe (S n0) (up s)). exact Hc.
    intros x Hx. destruct x as [|y].
    + unfold up; simpl; lia.
    + unfold up; simpl. apply (closed_under_ren n0 (S n0) (fun x => S x) (s y)).
        { intros z Hz. lia. }
        { apply (Hs y); lia. }
  - destruct Hc as [H1 H2]. split.
    + apply (IHe1 n0 s); auto.
    + apply (IHe2 n0 s); auto.
  - destruct Hc as [H1 H2]. split.
    + apply (IHe n0 s); auto.
    + apply (IHe0 (S n0) (up s)). exact H2.
      intros x Hx. destruct x as [|y].
      * unfold up; simpl; lia.
      * unfold up; simpl. apply (closed_under_ren n0 (S n0) (fun x => S x) (s y)).
        { intros z Hz. lia. }
        { apply (Hs y); lia. }
  - destruct Hc as [H1 H2]. split.
    + apply (IHe1 n0 s); auto.
    + apply (IHe2 n0 s); auto.
  - exact I.
  - exact I.
  - exact I.
  - destruct Hc as [H1 H2]. split.
    + apply (IHe1 n0 s); auto.
    + apply (IHe2 n0 s); auto.
  - destruct Hc as [H1 [H2 H3]]. split.
    + apply (IHe1 n0 s); auto.
    + split.
      * apply (IHe2 n0 s); auto.
      * apply (IHe3 n0 s); auto.
  - destruct Hc as [H1 H2]. split.
    + apply (IHe1 n0 s); auto.
    + apply (IHe2 n0 s); auto.
  - apply (IHe n0 s); auto.
  - apply (IHe n0 s); auto.
  - apply (IHe n0 s); auto.
  - apply (IHe n0 s); auto.
  - destruct Hc as [H1 [H2 H3]]. split.
    + apply (IHe n0 s); auto.
    + split.
      * apply (IHe0 (S n0) (up s)). exact H2.
        intros x Hx. destruct x as [|y].
        -- unfold up; simpl; lia.
        -- unfold up; simpl. apply (closed_under_ren n0 (S n0) (fun x => S x) (s y)).
        { intros z Hz. lia. }
        { apply (Hs y); lia. }
      * apply (IHe1 (S n0) (up s)). exact H3.
        intros x Hx. destruct x as [|y].
        -- unfold up; simpl; lia.
        -- unfold up; simpl. apply (closed_under_ren n0 (S n0) (fun x => S x) (s y)).
        { intros z Hz. lia. }
        { apply (Hs y); lia. }
  - exact I.
  - apply (IHe n0 s); auto.
  - destruct Hc as [H1 H2]. split.
    + apply (IHe1 n0 s); auto.
    + apply (IHe2 n0 s); auto.
  - apply (IHe n0 s); auto.
  - apply (IHe n0 s); auto.
  - apply (IHe n0 s); auto.
  - apply (IHe n0 s); auto.
  - apply (IHe n0 s); auto.
  - apply (IHe n0 s); auto.
  - destruct Hc as [H1 H2]. split.
    + apply (IHe n0 s); auto.
    + apply (IHe0 (S n0) (up s)). exact H2.
      intros x Hx. destruct x as [|y].
      * unfold up; simpl; lia.
      * unfold up; simpl. apply (closed_under_ren n0 (S n0) (fun x => S x) (s y)).
        { intros z Hz. lia. }
        { apply (Hs y); lia. }
  - apply (IHe n0 s); auto.
  - apply (IHe n0 s); auto.
Qed.

Lemma closed_under_upn_cons : forall k a x,
  closed_under 0 a -> x < S k ->
  closed_under k (upn k (a .: ids) x).
Proof.
  induction k as [|k IH]; intros a x Ha Hx.
  - assert (x = 0) by lia. subst. simpl. exact Ha.
  - destruct x as [|y].
    + simpl. unfold up. simpl. lia.
    + simpl. unfold up. simpl.
      apply (closed_under_ren k (S k) (fun z => S z) (upn k (a .: ids) y)).
      * intros z Hz. lia.
      * apply IH; [exact Ha|lia].
Qed.

Lemma closed_under_beta_gen : forall k b a,
  closed_under (S k) b -> closed_under 0 a ->
  closed_under k (b.[upn k (a .: ids)]).
Proof.
  intros k0 b. revert k0. induction b; intros k0 a Hb Ha; simpl in *.
  - apply (closed_under_upn_cons k0 a x); [exact Ha|exact Hb].
  - change (closed_under (S k0) (e.[upn (S k0) (a .: ids)])).
    apply (IHb (S k0) a); [exact Hb|exact Ha].
  - destruct Hb as [H1 H2]. split.
    + apply (IHb1 k0 a); auto.
    + apply (IHb2 k0 a); auto.
  - destruct Hb as [H1 H2]. split.
    + apply (IHb k0 a); auto.
    + change (closed_under (S k0) (e2.[upn (S k0) (a .: ids)])).
      apply (IHb0 (S k0) a); auto.
  - destruct Hb as [H1 H2]. split.
    + apply (IHb1 k0 a); auto.
    + apply (IHb2 k0 a); auto.
  - exact I.
  - exact I.
  - exact I.
  - destruct Hb as [H1 H2]. split.
    + apply (IHb1 k0 a); auto.
    + apply (IHb2 k0 a); auto.
  - destruct Hb as [H1 [H2 H3]]. split.
    + apply (IHb1 k0 a); auto.
    + split.
      * apply (IHb2 k0 a); auto.
      * apply (IHb3 k0 a); auto.
  - destruct Hb as [H1 H2]. split.
    + apply (IHb1 k0 a); auto.
    + apply (IHb2 k0 a); auto.
  - apply (IHb k0 a); auto.
  - apply (IHb k0 a); auto.
  - apply (IHb k0 a); auto.
  - apply (IHb k0 a); auto.
  - destruct Hb as [H1 [H2 H3]]. split.
    + apply (IHb k0 a); auto.
    + split.
      * change (closed_under (S k0) (e1.[upn (S k0) (a .: ids)])).
        apply (IHb0 (S k0) a); auto.
      * change (closed_under (S k0) (e2.[upn (S k0) (a .: ids)])).
        apply (IHb1 (S k0) a); auto.
  - exact I.
  - apply (IHb k0 a); auto.
  - destruct Hb as [H1 H2]. split.
    + apply (IHb1 k0 a); auto.
    + apply (IHb2 k0 a); auto.
  - apply (IHb k0 a); auto.
  - apply (IHb k0 a); auto.
  - apply (IHb k0 a); auto.
  - apply (IHb k0 a); auto.
  - apply (IHb k0 a); auto.
  - apply (IHb k0 a); auto.
  - destruct Hb as [H1 H2]. split.
    + apply (IHb k0 a); auto.
    + change (closed_under (S k0) (e2.[upn (S k0) (a .: ids)])).
      apply (IHb0 (S k0) a); auto.
  - apply (IHb k0 a); auto.
  - apply (IHb k0 a); auto.
Qed.

Lemma closed_expr_beta : forall b a,
  closed_expr (Lam b) -> closed_expr a -> closed_expr (b.[a/]).
Proof.
  intros b a Hb Ha. unfold closed_expr in *.
  change (closed_under 0 (b.[upn 0 (a .: ids)])).
  apply (closed_under_beta_gen 0 b a); [exact Hb|exact Ha].
Qed.

(* ------------------------------------------------------------------ *)
(* Basic facts about values.                                           *)
(* ------------------------------------------------------------------ *)

Lemma to_val_of_val (v : val) : to_val (of_val v) = Some v.
Proof.
  induction v; simpl; auto;
  try (rewrite IHv; reflexivity);
  try (rewrite IHv1, IHv2; reflexivity).
Qed.

Lemma of_val_to_val (e : expr) (v : val) : to_val e = Some v -> of_val v = e.
Proof.
  revert v. induction e; intros w Ht; simpl in Ht; try discriminate;
  try (injection Ht as <-; reflexivity).
  - destruct (to_val e1) as [v1|] eqn:E1; try discriminate.
    destruct (to_val e2) as [v2|] eqn:E2; try discriminate.
    injection Ht as <-. simpl. f_equal.
    + apply (IHe1 v1 eq_refl).
    + apply (IHe2 v2 eq_refl).
  - destruct (to_val e) as [v0|] eqn:E; try discriminate.
    injection Ht as <-. simpl. f_equal. apply (IHe v0 eq_refl).
  - destruct (to_val e) as [v0|] eqn:E; try discriminate.
    injection Ht as <-. simpl. f_equal. apply (IHe v0 eq_refl).
  - destruct (to_val e) as [v0|] eqn:E; try discriminate.
    injection Ht as <-. simpl. f_equal. apply (IHe v0 eq_refl).
  - destruct (to_val e) as [v0|] eqn:E; try discriminate.
    injection Ht as <-. simpl. f_equal. apply (IHe v0 eq_refl).
Qed.

Lemma of_val_inj (v1 v2 : val) : of_val v1 = of_val v2 -> v1 = v2.
Proof.
  revert v2. induction v1; destruct v2; simpl; intros Heq; try discriminate;
  try reflexivity;
  try (injection Heq as <-; reflexivity);
  try (injection Heq as ? ?; subst; f_equal; eauto).
  all: (injection Heq as Hx; f_equal; apply IHv1; exact Hx).
Qed.

(* ------------------------------------------------------------------ *)
(* Filling evaluation contexts.                                        *)
(* ------------------------------------------------------------------ *)

Lemma fill_nil (e : expr) : fill [] e = e.
Proof. reflexivity. Qed.

Lemma fill_cons (Ki : ectx_item) (K : list ectx_item) (e : expr) :
  fill (Ki :: K) e = fill K (fill_item Ki e).
Proof. reflexivity. Qed.

Lemma fill_app (K1 K2 : list ectx_item) (e : expr) :
  fill (K1 ++ K2) e = fill K2 (fill K1 e).
Proof.
  revert e. induction K1; intros e; simpl.
  - reflexivity.
  - rewrite IHK1. reflexivity.
Qed.

(* Lifting steps through evaluation contexts. *)
Lemma prim_step_fill (K : list ectx_item) (e : expr) (σ : state)
    (κ : list Empty_set) (e' : expr) (σ' : state) (efs : list expr) :
  prim_step e σ κ e' σ' efs -> prim_step (fill K e) σ κ (fill K e') σ' efs.
Proof.
  intros Hstep. inversion Hstep.
  eapply Ectx_step with (K := K0 ++ K) (e1' := e1') (e2' := e2').
  - rewrite fill_app. rewrite H0. reflexivity.
  - rewrite fill_app. rewrite H1. reflexivity.
  - exact H2.
Qed.

Lemma pstep_fill (K : list ectx_item) (e : expr) (σ : state) (e' : expr) (σ' : state) :
  pstep (e, σ) (e', σ') -> pstep (fill K e, σ) (fill K e', σ').
Proof. intros Hstep. apply prim_step_fill. exact Hstep. Qed.

Lemma rtc_pstep_fill (K : list ectx_item) (e : expr) (σ : state) (e' : expr) (σ' : state) :
  rtc pstep (e, σ) (e', σ') -> rtc pstep (fill K e, σ) (fill K e', σ').
Proof.
  intros Hr. remember (e,σ) as x eqn:Ex. remember (e',σ') as y eqn:Ey.
  revert e σ e' σ' Ex Ey.
  induction Hr as [x0 | x0 z y0 Hstep Htail IH]; intros e0 σ0 e1 σ1 Ex Ey.
  - subst x0. injection Ey as He1 He2. subst. apply rtc_refl.
  - destruct z as [ez σz]. subst x0.
    eapply rtc_l.
    + apply pstep_fill. simpl. exact Hstep.
    + apply (IH ez σz e1 σ1 eq_refl Ey).
Qed.

(**********************************************************************)
(* A semantic model for the calculus: worlds, type-relation            *)
(* environments, and a fuel-indexed value relation.                    *)
(**********************************************************************)

Definition obs_bool (l : label) : bool :=
  match @lat_equiv_dec label lattice (l ⊔ ζ) ζ with
  | left _ => true
  | right _ => false
  end.
Definition obs_case (l : label) (P : Prop) : Prop :=
  if obs_bool l then P else True.

Definition World := (state * state * (loc -> option (loc * sectype)))%type.
Definition wst1 (W : World) : state := W.1.1.
Definition wst2 (W : World) : state := W.1.2.
Definition wmap (W : World) : loc -> option (loc * sectype) := W.2.

Inductive steps : nat -> (expr * state) -> (expr * state) -> Prop :=
| steps_0 : forall x, steps 0 x x
| steps_S : forall n x y z, pstep x y -> steps n y z -> steps (S n) x z.

Definition unfold_val (v : val) : val :=
  match v with FoldV v' => v' | v => v end.

Record TyRel := {
  tyrel : nat -> label -> World -> val -> val -> Prop;
  tyrel_mono : forall k' k, k' <= k ->
    forall l W v1 v2, tyrel k l W v1 v2 -> tyrel k' l W v1 v2;
  tyrel_mono_label : forall l l', l ⊑ l' ->
    forall k W v1 v2, tyrel k l W v1 v2 -> tyrel k l' W v1 v2
}.
Definition tenv := var -> TyRel.

Definition extend_tenv (R : TyRel) (Delta : tenv) : tenv :=
  fun x => match x with 0 => R | S n => Delta n end.
Definition extend_rho (l : label) (rho : var -> label) : var -> label :=
  fun x => match x with 0 => l | S n => rho n end.

Definition VF := (var -> label) -> tenv -> World -> sectype -> val -> val -> Prop.
Definition EF := (var -> label) -> tenv -> World -> sectype -> expr -> expr -> Prop.

Definition Vstep (K : nat) (Vlow : nat -> VF) (Elow : nat -> EF) : VF :=
  fun rho Delta W tau v1 v2 =>
  match K with
  | 0 => True
  | S k' =>
    match tau with
    | TSec l t =>
      obs_case (interp_label rho l) (match t with
        | TUnit => True
        | TBool => v1 = v2
        | TNat => v1 = v2
        | TVar x => (Delta x).(tyrel) (S k') (interp_label rho l) W v1 v2
        | TProd tau1 tau2 =>
            match v1, v2 with
            | PairV a1 b1, PairV a2 b2 =>
                Vlow k' rho Delta W tau1 a1 a2 /\
                Vlow k' rho Delta W tau2 b1 b2
            | _,_ => False
            end
        | TSum tau1 tau2 =>
            match v1, v2 with
            | InjLV a1, InjLV a2 => Vlow k' rho Delta W tau1 a1 a2
            | InjRV a1, InjRV a2 => Vlow k' rho Delta W tau2 a1 a2
            | _,_ => False
            end
        | TArrow _ tau1 tau2 =>
            match v1, v2 with
            | LamV b1, LamV b2 =>
                forall j, j < S k' ->
                  forall a1 a2,
                    closed_expr a1 -> closed_expr a2 ->
                    Elow j rho Delta W tau1 a1 a2 ->
                    Elow j rho Delta W tau2 (App (Lam b1) a1) (App (Lam b2) a2)
            | _,_ => False
            end
        | TRef tau0 =>
            match v1, v2 with
            | LocV l1, LocV l2 =>
                match wmap W l1 with
                | Some (l2', tau') =>
                    (l2' = l2) /\ (tau' = tau0) /\
                    match wst1 W !! l1, wst2 W !! l2 with
                    | Some x1, Some x2 => Vlow k' rho Delta W tau0 x1 x2
                    | _,_ => False
                    end
                | None => False
                end
            | _,_ => False
            end
        | TForall _ tau0 =>
            match v1, v2 with
            | TLamV b1, TLamV b2 =>
                forall j, j < S k' -> forall (R : TyRel),
                  Elow j rho (extend_tenv R Delta) W tau0
                    (TApp (TLam b1)) (TApp (TLam b2))
            | _,_ => False
            end
        | TLForall _ tau0 =>
            match v1, v2 with
            | TLLamV b1, TLLamV b2 =>
                forall j, j < S k' -> forall (l' : label),
                  Elow j (extend_rho l' rho) Delta W tau0
                    (TLApp (TLLam b1)) (TLApp (TLLam b2))
            | _,_ => False
            end
        | TExist tau0 =>
            match v1, v2 with
            | PackV a1, PackV a2 =>
                exists (R : TyRel),
                  Vlow k' rho (extend_tenv R Delta) W tau0 a1 a2
            | _,_ => False
            end
        | TRec tau0 =>
            Vlow k' rho Delta W
              (hsubst_sectype (TRec tau0 .: ids) tau0)
              (unfold_val v1) (unfold_val v2)
        end)
    end
  end.

Definition Frame (Vlow : nat -> VF) (r : nat) (W W' : World) : Prop :=
  forall j, j <= r -> forall rho Delta tau v1 v2,
    Vlow j rho Delta W tau v1 v2 -> Vlow j rho Delta W' tau v1 v2.

Definition Estep (K : nat) (Vlow : nat -> VF) : EF :=
  fun rho Delta W tau e1 e2 =>
  match K with
  | 0 => True
  | S k' =>
    forall (n1 n2 : nat) (v1 v2 : val) (s1 s2 : state),
      steps n1 (e1, wst1 W) (#v1, s1) ->
      steps n2 (e2, wst2 W) (#v2, s2) ->
      n1 + n2 <= S k' ->
      exists (wm' : loc -> option (loc * sectype)),
        (forall l l' tau0, wmap W l = Some (l', tau0) -> wm' l = Some (l', tau0)) /\
        Vlow (S k' - n1 - n2 - 1) rho Delta (s1, s2, wm') tau v1 v2 /\
        Frame Vlow (S k' - n1 - n2 - 1) W (s1, s2, wm')
  end.

Record LVL := { lvlV : VF; lvlE : EF }.

Definition base_lvl : LVL :=
  {| lvlV := fun _ _ _ _ _ _ => True; lvlE := fun _ _ _ _ _ _ => True |}.

Fixpoint fam (K : nat) : nat -> LVL :=
  match K with
  | 0 => fun _ => base_lvl
  | S k' =>
      let old := fam k' in
      let Vlow j := (old j).(lvlV) in
      let Elow j := (old j).(lvlE) in
      let newlvl :=
          {| lvlV := Vstep (S k') Vlow Elow;
             lvlE := Estep (S k') Vlow |} in
      fun j => if Nat.eqb j (S k') then newlvl else old j
  end.

Definition V (k : nat) : VF := (fam k k).(lvlV).
Definition E (k : nat) : EF := (fam k k).(lvlE).

Definition FrameV (r : nat) (W W' : World) : Prop :=
  forall j, j <= r -> forall rho Delta tau v1 v2,
    V j rho Delta W tau v1 v2 -> V j rho Delta W' tau v1 v2.

Lemma FrameV_refl : forall r W, FrameV r W W.
Proof. intros r W. unfold FrameV. auto. Qed.

Lemma FrameV_mono : forall r r' W W',
  r' <= r -> FrameV r W W' -> FrameV r' W W'.
Proof.
  intros r r' W W' Hle HF. unfold FrameV in *. intros j Hj.
  apply HF. lia.
Qed.

Lemma fam_agree : forall K j, j <= K -> fam K j = fam j j.
Proof.
  induction K as [|K IH]; intros j Hj.
  - assert (j = 0) by lia. subst j. reflexivity.
  - destruct j as [|j].
    + cbn [fam].
      destruct (Nat.eqb 0 (S K)) eqn:E.
      * apply Nat.eqb_eq in E. lia.
      * rewrite (IH 0). reflexivity. lia.
    + cbn [fam].
      destruct (Nat.eqb (S j) (S K)) eqn:E.
      * apply Nat.eqb_eq in E. inversion E; subst j. rewrite Nat.eqb_refl. reflexivity.
      * apply Nat.eqb_neq in E.
        assert (S j <= K) by lia.
        rewrite (IH (S j) H0). reflexivity.
Qed.

Lemma obs_case_iff : forall l (P Q : Prop), (P <-> Q) -> (obs_case l P <-> obs_case l Q).
Proof.
  intros. unfold obs_case. destruct (obs_bool l); simpl; tauto.
Qed.

Lemma Vlow_fam : forall k' j, j <= k' -> (fam k' j).(lvlV) = V j.
Proof. intros. unfold V. rewrite fam_agree; auto. Qed.
Lemma Elow_fam : forall k' j, j <= k' -> (fam k' j).(lvlE) = E j.
Proof. intros. unfold E. rewrite fam_agree; auto. Qed.

Lemma Frame_fam : forall k' r W W', r <= k' ->
  (Frame (fun j => (fam k' j).(lvlV)) r W W' <-> FrameV r W W').
Proof.
  intros k' r W W' Hr. unfold Frame, FrameV.
  split.
  - intros HF j Hj rho Delta tau v1 v2 HV.
    assert (Hjk : j <= k') by lia.
    assert (Hraw : (fam k' j).(lvlV) rho Delta W tau v1 v2).
    { rewrite (@Vlow_fam k' j Hjk). exact HV. }
    specialize (HF j Hj rho Delta tau v1 v2 Hraw).
    rewrite (@Vlow_fam k' j Hjk) in HF. exact HF.
  - intros HF j Hj rho Delta tau v1 v2 HV.
    assert (Hjk : j <= k') by lia.
    assert (Hclean : V j rho Delta W tau v1 v2).
    { rewrite (@Vlow_fam k' j Hjk) in HV. exact HV. }
    specialize (HF j Hj rho Delta tau v1 v2 Hclean).
    rewrite <- (@Vlow_fam k' j Hjk) in HF. exact HF.
Qed.

Lemma V_bool_eq : forall k' rho Delta W l (v1 v2 : val),
  V (S k') rho Delta W (TBool @ l) v1 v2 <->
  obs_case (interp_label rho l) (v1 = v2).
Proof.
  intros. unfold V. cbn [fam]. rewrite Nat.eqb_refl. cbn [Vstep].
  reflexivity.
Qed.

Lemma V_arrow_eq : forall k' rho Delta W l le tau1 tau2 (b1 b2 : expr),
  V (S k') rho Delta W (TArrow le tau1 tau2 @ l) (LamV b1) (LamV b2) <->
  obs_case (interp_label rho l)
    (forall j, j < S k' -> forall a1 a2,
        closed_expr a1 -> closed_expr a2 ->
        E j rho Delta W tau1 a1 a2 ->
        E j rho Delta W tau2 (App (Lam b1) a1) (App (Lam b2) a2)).
Proof.
  intros. unfold V. cbn [fam]. rewrite Nat.eqb_refl. cbn [Vstep].
  apply obs_case_iff. split; intros Hrel j Hj a1 a2 Hc1 Hc2 Harg.
  - assert (Hle : j <= k') by lia.
    specialize (Hrel j Hj a1 a2 Hc1 Hc2). rewrite <- (@Elow_fam k' j Hle) in Harg.
    apply Hrel in Harg. rewrite (@Elow_fam k' j Hle) in Harg. exact Harg.
  - assert (Hle : j <= k') by lia.
    specialize (Hrel j Hj a1 a2 Hc1 Hc2). rewrite (@Elow_fam k' j Hle) in Harg.
    apply Hrel in Harg. rewrite (@Elow_fam k' j Hle). exact Harg.
Qed.

Lemma V_unit_eq : forall k' rho Delta W l (v1 v2 : val),
  V (S k') rho Delta W (TUnit @ l) v1 v2 <-> obs_case (interp_label rho l) True.
Proof. intros. unfold V. cbn [fam]. rewrite Nat.eqb_refl. cbn [Vstep]. apply obs_case_iff. tauto. Qed.

Lemma V_nat_eq : forall k' rho Delta W l (v1 v2 : val),
  V (S k') rho Delta W (TNat @ l) v1 v2 <-> obs_case (interp_label rho l) (v1 = v2).
Proof. intros. unfold V. cbn [fam]. rewrite Nat.eqb_refl. cbn [Vstep]. reflexivity. Qed.

Lemma V_tvar_eq : forall k' rho Delta W l x (v1 v2 : val),
  V (S k') rho Delta W (TVar x @ l) v1 v2 <->
  obs_case (interp_label rho l) ((Delta x).(tyrel) (S k') (interp_label rho l) W v1 v2).
Proof. intros. unfold V. cbn [fam]. rewrite Nat.eqb_refl. cbn [Vstep]. reflexivity. Qed.

Lemma V_prod_eq : forall k' rho Delta W l tau1 tau2 (a1 b1 a2 b2 : val),
  V (S k') rho Delta W (TProd tau1 tau2 @ l) (PairV a1 b1) (PairV a2 b2) <->
  obs_case (interp_label rho l)
    (V k' rho Delta W tau1 a1 a2 /\ V k' rho Delta W tau2 b1 b2).
Proof.
  intros. unfold V. cbn [fam]. rewrite Nat.eqb_refl. cbn [Vstep].
  apply obs_case_iff. reflexivity.
Qed.

Lemma V_sum_eq_l : forall k' rho Delta W l tau1 tau2 (a1 a2 : val),
  V (S k') rho Delta W (TSum tau1 tau2 @ l) (InjLV a1) (InjLV a2) <->
  obs_case (interp_label rho l) (V k' rho Delta W tau1 a1 a2).
Proof.
  intros. unfold V. cbn [fam]. rewrite Nat.eqb_refl. cbn [Vstep].
  apply obs_case_iff. reflexivity.
Qed.

Lemma V_sum_eq_r : forall k' rho Delta W l tau1 tau2 (a1 a2 : val),
  V (S k') rho Delta W (TSum tau1 tau2 @ l) (InjRV a1) (InjRV a2) <->
  obs_case (interp_label rho l) (V k' rho Delta W tau2 a1 a2).
Proof.
  intros. unfold V. cbn [fam]. rewrite Nat.eqb_refl. cbn [Vstep].
  apply obs_case_iff. reflexivity.
Qed.

Lemma V_ref_eq : forall k' rho Delta W l tau0 l1 l2,
  V (S k') rho Delta W (TRef tau0 @ l) (LocV l1) (LocV l2) <->
  obs_case (interp_label rho l)
    (match wmap W l1 with
     | Some (l2', tau') =>
         (l2' = l2) /\ (tau' = tau0) /\
         match wst1 W !! l1, wst2 W !! l2 with
         | Some x1, Some x2 => V k' rho Delta W tau0 x1 x2
         | _,_ => False
         end
     | None => False
     end).
Proof.
  intros. unfold V. cbn [fam]. rewrite Nat.eqb_refl. cbn [Vstep].
  apply obs_case_iff. reflexivity.
Qed.

Lemma V_rec_eq : forall k' rho Delta W l tau0 (v1 v2 : val),
  V (S k') rho Delta W (TRec tau0 @ l) v1 v2 <->
  obs_case (interp_label rho l)
    (V k' rho Delta W (hsubst_sectype (TRec tau0 .: ids) tau0)
       (unfold_val v1) (unfold_val v2)).
Proof.
  intros. unfold V. cbn [fam]. rewrite Nat.eqb_refl. cbn [Vstep].
  apply obs_case_iff. reflexivity.
Qed.

Lemma V_forall_eq : forall k' rho Delta W l le tau0 (b1 b2 : expr),
  V (S k') rho Delta W (TForall le tau0 @ l) (TLamV b1) (TLamV b2) <->
  obs_case (interp_label rho l)
    (forall j, j < S k' -> forall (R : TyRel),
        E j rho (extend_tenv R Delta) W tau0 (TApp (TLam b1)) (TApp (TLam b2))).
Proof.
  intros. unfold V. cbn [fam]. rewrite Nat.eqb_refl. cbn [Vstep].
  apply obs_case_iff. split; intros Hrel j Hj R.
  - specialize (Hrel j Hj R). assert (Hle : j <= k') by lia.
    rewrite (@Elow_fam k' j Hle) in Hrel. exact Hrel.
  - specialize (Hrel j Hj R). assert (Hle : j <= k') by lia.
    rewrite <- (@Elow_fam k' j Hle) in Hrel. exact Hrel.
Qed.

Lemma V_lforall_eq : forall k' rho Delta W l le tau0 (b1 b2 : expr),
  V (S k') rho Delta W (TLForall le tau0 @ l) (TLLamV b1) (TLLamV b2) <->
  obs_case (interp_label rho l)
    (forall j, j < S k' -> forall (l' : label),
        E j (extend_rho l' rho) Delta W tau0 (TLApp (TLLam b1)) (TLApp (TLLam b2))).
Proof.
  intros. unfold V. cbn [fam]. rewrite Nat.eqb_refl. cbn [Vstep].
  apply obs_case_iff. split; intros Hrel j Hj l'.
  - specialize (Hrel j Hj l'). assert (Hle : j <= k') by lia.
    rewrite (@Elow_fam k' j Hle) in Hrel. exact Hrel.
  - specialize (Hrel j Hj l'). assert (Hle : j <= k') by lia.
    rewrite <- (@Elow_fam k' j Hle) in Hrel. exact Hrel.
Qed.

Lemma V_exist_eq : forall k' rho Delta W l tau0 (a1 a2 : val),
  V (S k') rho Delta W (TExist tau0 @ l) (PackV a1) (PackV a2) <->
  obs_case (interp_label rho l)
    (exists (R : TyRel), V k' rho (extend_tenv R Delta) W tau0 a1 a2).
Proof.
  intros. unfold V. cbn [fam]. rewrite Nat.eqb_refl. cbn [Vstep].
  apply obs_case_iff. reflexivity.
Qed.

Lemma E_S_eq : forall k' rho Delta W tau e1 e2,
  E (S k') rho Delta W tau e1 e2 <->
  (forall (n1 n2 : nat) (v1 v2 : val) (s1 s2 : state),
      steps n1 (e1, wst1 W) (#v1, s1) ->
      steps n2 (e2, wst2 W) (#v2, s2) ->
      n1 + n2 <= S k' ->
      exists (wm' : loc -> option (loc * sectype)),
        (forall l l' tau0, wmap W l = Some (l', tau0) -> wm' l = Some (l', tau0)) /\
        V (S k' - n1 - n2 - 1) rho Delta (s1, s2, wm') tau v1 v2 /\
        FrameV (S k' - n1 - n2 - 1) W (s1, s2, wm')).
Proof.
  intros. unfold E. cbn [fam]. rewrite Nat.eqb_refl. cbn [Estep].
  split; intros Hrel n1 n2 v1 v2 s1 s2 Hs1 Hs2 Hle.
  - destruct (Hrel n1 n2 v1 v2 s1 s2 Hs1 Hs2 Hle) as [wm' [Hext [HV HF]]].
    exists wm'. split; [exact Hext | split].
    + assert (Hr : S k' - n1 - n2 - 1 <= k') by lia.
      rewrite <- (@Vlow_fam k' (S k' - n1 - n2 - 1) Hr). exact HV.
    + assert (Hr : S k' - n1 - n2 - 1 <= k') by lia.
      apply (proj1 (Frame_fam k' (S k' - n1 - n2 - 1) W (s1, s2, wm') Hr)). exact HF.
  - destruct (Hrel n1 n2 v1 v2 s1 s2 Hs1 Hs2 Hle) as [wm' [Hext [HV HF]]].
    exists wm'. split; [exact Hext | split].
    + assert (Hr : S k' - n1 - n2 - 1 <= k') by lia.
      rewrite (@Vlow_fam k' (S k' - n1 - n2 - 1) Hr). exact HV.
    + assert (Hr : S k' - n1 - n2 - 1 <= k') by lia.
      apply (proj2 (Frame_fam k' (S k' - n1 - n2 - 1) W (s1, s2, wm') Hr)). exact HF.
Qed.



Lemma obs_bool_true : forall l : label, obs_bool l = true <-> l ⊑ ζ.
Proof.
  intros l. unfold obs_bool.
  destruct (@lat_equiv_dec label lattice (l ⊔ ζ) ζ) as [Hord|Hord].
  - simpl. split; intros _; [exact Hord | reflexivity].
  - simpl. split; intros HH; [discriminate HH | contradiction].
Qed.

Lemma obs_case_true : forall l (P : Prop), l ⊑ ζ -> (obs_case l P <-> P).
Proof.
  intros l P Hobs. unfold obs_case.
  rewrite (proj2 (obs_bool_true l) Hobs). tauto.
Qed.

Lemma obs_case_false : forall l (P : Prop), ~ (l ⊑ ζ) -> (obs_case l P <-> True).
Proof.
  intros l P Hobs. unfold obs_case.
  assert (obs_bool l = false) as Hb.
  { destruct (obs_bool l) eqn:E; auto. exfalso. apply Hobs. apply (proj1 (obs_bool_true l)). exact E. }
  rewrite Hb. tauto.
Qed.


Lemma fill_item_to_val (Ki : ectx_item) (e : expr) (w : val) :
  to_val (fill_item Ki e) = Some w -> exists v, to_val e = Some v.
Proof.
  destruct (to_val e) as [v|] eqn:E.
  - exists v; reflexivity.
  - destruct Ki; simpl; intro Hs;
    try (rewrite E in Hs);
    try (rewrite to_val_of_val in Hs);
    simpl in Hs; try discriminate Hs.
Qed.

Lemma fill_value_inv (K : list ectx_item) (e : expr) (v : val) :
  #v = fill K e -> exists w, to_val e = Some w.
Proof.
  revert e v. induction K as [|Ki K IH]; intros e v Hs.
  - simpl in Hs. exists v. rewrite <- Hs. apply to_val_of_val.
  - simpl in Hs. apply IH in Hs. destruct Hs as [w Hw].
    eapply fill_item_to_val; eauto.
Qed.

Lemma head_step_not_value (e : expr) (v : val) (σ : state)
    (e' : expr) (σ' : state) (efs : list expr) :
  to_val e = Some v -> ~ head_step e σ [] e' σ' efs.
Proof.
  intros Hv Hstep. destruct Hstep; cbn in Hv; discriminate.
Qed.

Lemma pstep_value (v : val) (σ : state) (e' : expr) (σ' : state) :
  ~ pstep (#v, σ) (e', σ').
Proof.
  intros Hp. inversion Hp as [K e1' e2' Hfill _ Hhead]; subst.
  simpl in Hfill.
  destruct (fill_value_inv K e1' v Hfill) as [w Hw].
  exact (@head_step_not_value e1' w σ e2' σ' [] Hw Hhead).
Qed.

Lemma steps_value_inv (n : nat) (v : val) (σ : state) (e' : expr) (σ' : state) :
  steps n (#v, σ) (e', σ') -> n = 0 /\ e' = #v /\ σ' = σ.
Proof.
  intros Hs. remember (#v, σ) as x eqn:Ex. remember (e', σ') as y eqn:Ey.
  revert v σ e' σ' Ex Ey.
  induction Hs as [x0 | n0 x0 y0 z Hstep Htail IH]; intros v σ e' σ' Ex Ey.
  - inversion Ex; subst. inversion Ey; subst. auto.
  - inversion Ex; subst. destruct y0 as [ey σy]. exfalso.
    eapply pstep_value; eauto.
Qed.

Lemma steps_0_inv : forall (x y : expr * state), steps 0 x y -> x = y.
Proof. intros x y Hs. inversion Hs. reflexivity. Qed.


Lemma V_zero : forall rho Delta W tau (v1 v2 : val), V 0 rho Delta W tau v1 v2.
Proof. intros. unfold V. cbn [fam]. reflexivity. Qed.

Lemma E_zero : forall rho Delta W tau (e1 e2 : expr), E 0 rho Delta W tau e1 e2.
Proof. intros. unfold E. cbn [fam]. reflexivity. Qed.

Lemma E_value : forall k' rho Delta W tau (v1 v2 : val),
  V k' rho Delta W tau v1 v2 ->
  E (S k') rho Delta W tau (#v1) (#v2).
Proof.
  intros k' rho Delta W tau v1 v2 HV.
  destruct W as [[s1 s2] wm]. simpl in *.
  apply E_S_eq. intros n1 n2 w1 w2 t1 t2 Hs1 Hs2 Hle.
  destruct (steps_value_inv n1 v1 s1 (#w1) t1 Hs1) as [Hn1 [He1 Hs1']].
  destruct (steps_value_inv n2 v2 s2 (#w2) t2 Hs2) as [Hn2 [He2 Hs2']].
  subst n1 n2. exists wm. split.
  - intros l l' tau0 Hm. exact Hm.
  - split.
    + subst t1 t2. apply of_val_inj in He1. apply of_val_inj in He2. subst w1 w2.
      replace (S k' - 0 - 0 - 1) with k' by lia. exact HV.
    + subst t1 t2. replace (S k' - 0 - 0 - 1) with k' by lia. apply FrameV_refl.
Qed.


Lemma V_high : forall k rho Delta W (tau : sectype) (v1 v2 : val),
  ~ (interp_label rho (sectype_label tau) ⊑ ζ) ->
  V k rho Delta W tau v1 v2.
Proof.
  intros k rho Delta W tau v1 v2 Hh.
  destruct k as [|k'].
  - apply V_zero.
  - destruct tau as [l t]. simpl in Hh.
    unfold V. cbn [fam]. rewrite Nat.eqb_refl. cbn [Vstep].
    apply (proj2 (obs_case_false (interp_label rho l) _ Hh)). exact I.
Qed.

Fixpoint EnvRel (k : nat) (rho : var -> label) (Delta : tenv) (W : World)
    (Gamma : list sectype) (d1 d2 : var -> val) {struct Gamma} : Prop :=
  match Gamma with
  | [] => True
  | tau :: Gamma' =>
      V k rho Delta W tau (d1 0) (d2 0) /\ EnvRel k rho Delta W Gamma' (fun n => d1 (S n)) (fun n => d2 (S n))
  end.

Definition EnvRelAll (rho : var -> label) (Delta : tenv) (W : World)
    (Gamma : list sectype) (d1 d2 : var -> val) : Prop :=
  forall k, EnvRel k rho Delta W Gamma d1 d2.

Definition env_subst_vals (d : var -> val) : var -> expr := fun x => #(d x).

Lemma EnvRel_nil : forall k rho Delta W d1 d2, EnvRel k rho Delta W [] d1 d2.
Proof. intros. simpl. exact I. Qed.

Lemma EnvRel_cons : forall k rho Delta W tau Gamma d1 d2 v1 v2,
  V k rho Delta W tau v1 v2 ->
  EnvRel k rho Delta W Gamma d1 d2 ->
  EnvRel k rho Delta W (tau :: Gamma)
    (fun x => match x with 0 => v1 | S n => d1 n end)
    (fun x => match x with 0 => v2 | S n => d2 n end).
Proof.
  intros k rho0 Delta0 W0 tau0 Gamma0 d1 d2 v1 v2 HV HEn. simpl. split; assumption.
Qed.



Lemma EnvRelAll_high : forall rho Delta W ℓ' (v1 v2 : val),
  ℓ' ⋢ ζ ->
  EnvRelAll rho Delta W [TBool @ (LLabel ℓ')]
    (fun x => match x with 0 => v1 | S n => v1 end)
    (fun x => match x with 0 => v2 | S n => v2 end).
Proof.
  intros rho Delta W l' v1 v2 Hh. intro k. simpl.
  split.
  - apply V_high. simpl. exact Hh.
  - exact I.
Qed.


Lemma V_bool_low_eq : forall k' rho Delta W l (v1 v2 : val),
  interp_label rho l ⊑ ζ ->
  V (S k') rho Delta W (TBool @ l) v1 v2 -> v1 = v2.
Proof.
  intros k' rho Delta W l v1 v2 Hobs HV.
  rewrite V_bool_eq in HV.
  apply (proj1 (obs_case_true (interp_label rho l) (v1 = v2) Hobs)) in HV.
  exact HV.
Qed.

Lemma V_nat_low_eq : forall k' rho Delta W l (v1 v2 : val),
  interp_label rho l ⊑ ζ ->
  V (S k') rho Delta W (TNat @ l) v1 v2 -> v1 = v2.
Proof.
  intros k' rho Delta W l v1 v2 Hobs HV.
  rewrite V_nat_eq in HV.
  apply (proj1 (obs_case_true (interp_label rho l) (v1 = v2) Hobs)) in HV.
  exact HV.
Qed.


Lemma V_arrow_obs : forall k' rho Delta W l le tau1 tau2 (b1 b2 : expr),
  interp_label rho l ⊑ ζ ->
  (V (S k') rho Delta W (TArrow le tau1 tau2 @ l) (LamV b1) (LamV b2) <->
   forall j, j < S k' -> forall a1 a2,
     closed_expr a1 -> closed_expr a2 ->
     E j rho Delta W tau1 a1 a2 ->
     E j rho Delta W tau2 (App (Lam b1) a1) (App (Lam b2) a2)).
Proof.
  intros k' rho Delta W l le tau1 tau2 b1 b2 Hobs.
  rewrite V_arrow_eq.
  apply obs_case_true. exact Hobs.
Qed.

Lemma V_prod_obs : forall k' rho Delta W l tau1 tau2 (a1 b1 a2 b2 : val),
  interp_label rho l ⊑ ζ ->
  (V (S k') rho Delta W (TProd tau1 tau2 @ l) (PairV a1 b1) (PairV a2 b2) <->
   V k' rho Delta W tau1 a1 a2 /\ V k' rho Delta W tau2 b1 b2).
Proof.
  intros k' rho Delta W l tau1 tau2 a1 b1 a2 b2 Hobs.
  rewrite V_prod_eq.
  apply obs_case_true. exact Hobs.
Qed.


Lemma EnvRelAll_nil : forall rho Delta W d1 d2,
  EnvRelAll rho Delta W [] d1 d2.
Proof. intros. intro k. apply EnvRel_nil. Qed.

Lemma EnvRelAll_cons : forall rho Delta W tau Gamma d1 d2 v1 v2,
  (forall k, V k rho Delta W tau v1 v2) ->
  EnvRelAll rho Delta W Gamma d1 d2 ->
  EnvRelAll rho Delta W (tau :: Gamma)
    (fun x => match x with 0 => v1 | S n => d1 n end)
    (fun x => match x with 0 => v2 | S n => d2 n end).
Proof.
  intros rho Delta W tau Gamma d1 d2 v1 v2 HV HGamma k.
  apply EnvRel_cons.
  - apply HV.
  - apply HGamma.
Qed.


Lemma E_value_high : forall k' rho Delta W (tau : sectype) (v1 v2 : val),
  ~ (interp_label rho (sectype_label tau) ⊑ ζ) ->
  E (S k') rho Delta W tau (#v1) (#v2).
Proof.
  intros k' rho Delta W tau v1 v2 Hh.
  apply E_value. apply V_high. exact Hh.
Qed.


Lemma V_bool_obs : forall k' rho Delta W l (v1 v2 : val),
  interp_label rho l ⊑ ζ ->
  (V (S k') rho Delta W (TBool @ l) v1 v2 <-> v1 = v2).
Proof.
  intros k' rho Delta W l v1 v2 Hobs.
  rewrite V_bool_eq. apply obs_case_true. exact Hobs.
Qed.

Lemma V_nat_obs : forall k' rho Delta W l (v1 v2 : val),
  interp_label rho l ⊑ ζ ->
  (V (S k') rho Delta W (TNat @ l) v1 v2 <-> v1 = v2).
Proof.
  intros k' rho Delta W l v1 v2 Hobs.
  rewrite V_nat_eq. apply obs_case_true. exact Hobs.
Qed.


Lemma obs_case_imp : forall l (P Q : Prop), (P -> Q) -> obs_case l P -> obs_case l Q.
Proof.
  intros l P Q HPQ Ho. unfold obs_case in *.
  destruct (obs_bool l); simpl in *; tauto.
Qed.

Lemma V_mono_bool : forall k rho Delta W l (v1 v2 : val),
  V (S k) rho Delta W (TBool @ l) v1 v2 ->
  V k rho Delta W (TBool @ l) v1 v2.
Proof.
  intros k rho Delta W l v1 v2 Hs.
  destruct k as [|k'].
  - apply V_zero.
  - rewrite V_bool_eq in Hs |- *. exact Hs.
Qed.


Lemma V_mono_unit : forall k rho Delta W l (v1 v2 : val),
  V (S k) rho Delta W (TUnit @ l) v1 v2 ->
  V k rho Delta W (TUnit @ l) v1 v2.
Proof.
  intros k rho Delta W l v1 v2 Hs. destruct k as [|k'].
  - apply V_zero.
  - rewrite V_unit_eq in Hs |- *. exact Hs.
Qed.

Lemma V_mono_nat : forall k rho Delta W l (v1 v2 : val),
  V (S k) rho Delta W (TNat @ l) v1 v2 ->
  V k rho Delta W (TNat @ l) v1 v2.
Proof.
  intros k rho Delta W l v1 v2 Hs. destruct k as [|k'].
  - apply V_zero.
  - rewrite V_nat_eq in Hs |- *. exact Hs.
Qed.

Lemma V_mono_tvar : forall k rho Delta W l x (v1 v2 : val),
  V (S k) rho Delta W (TVar x @ l) v1 v2 ->
  V k rho Delta W (TVar x @ l) v1 v2.
Proof.
  intros k rho Delta W l x v1 v2 Hs. destruct k as [|k'].
  - apply V_zero.
  - rewrite V_tvar_eq in Hs |- *.
    eapply obs_case_imp; [|exact Hs]. intro HR.
    eapply (tyrel_mono (Delta x)); [|exact HR]. lia.
Qed.


Lemma V_mono_prod_step :
  forall k' (IH : forall rho Delta W tau (v1 v2 : val),
      V (S k') rho Delta W tau v1 v2 -> V k' rho Delta W tau v1 v2)
    rho Delta W l tau1 tau2 (v1 v2 : val),
  V (S (S k')) rho Delta W (TProd tau1 tau2 @ l) v1 v2 ->
  V (S k') rho Delta W (TProd tau1 tau2 @ l) v1 v2.
Proof.
  intros k' IH rho Delta W l tau1 tau2 v1 v2 Hs.
  destruct v1; destruct v2;
  try (rewrite V_prod_eq in Hs |- *; eapply obs_case_imp; [|exact Hs];
       intro Hp; destruct Hp as [H1 H2]; split;
       [ apply IH; exact H1 | apply IH; exact H2 ]);
  try (unfold V in Hs |- *; cbn [fam] in Hs |- *;
       rewrite Nat.eqb_refl in Hs |- *; cbn [Vstep] in Hs |- *; exact Hs).
Qed.


Lemma V_mono_sum_step :
  forall k' (IH : forall rho Delta W tau (v1 v2 : val),
      V (S k') rho Delta W tau v1 v2 -> V k' rho Delta W tau v1 v2)
    rho Delta W l tau1 tau2 (v1 v2 : val),
  V (S (S k')) rho Delta W (TSum tau1 tau2 @ l) v1 v2 ->
  V (S k') rho Delta W (TSum tau1 tau2 @ l) v1 v2.
Proof.
  intros k' IH rho Delta W l tau1 tau2 v1 v2 Hs.
  destruct v1; destruct v2;
  try (rewrite V_sum_eq_l in Hs |- *; eapply obs_case_imp; [|exact Hs];
       intro Hp; apply IH; exact Hp);
  try (rewrite V_sum_eq_r in Hs |- *; eapply obs_case_imp; [|exact Hs];
       intro Hp; apply IH; exact Hp);
  try (unfold V in Hs |- *; cbn [fam] in Hs |- *;
       rewrite Nat.eqb_refl in Hs |- *; cbn [Vstep] in Hs |- *; exact Hs).
Qed.

Lemma V_mono_exist_step :
  forall k' (IH : forall rho Delta W tau (v1 v2 : val),
      V (S k') rho Delta W tau v1 v2 -> V k' rho Delta W tau v1 v2)
    rho Delta W l tau0 (v1 v2 : val),
  V (S (S k')) rho Delta W (TExist tau0 @ l) v1 v2 ->
  V (S k') rho Delta W (TExist tau0 @ l) v1 v2.
Proof.
  intros k' IH rho Delta W l tau0 v1 v2 Hs.
  destruct v1; destruct v2;
  try (rewrite V_exist_eq in Hs |- *; eapply obs_case_imp; [|exact Hs];
       intro Hp; destruct Hp as [R HR]; exists R; apply IH; exact HR);
  try (unfold V in Hs |- *; cbn [fam] in Hs |- *;
       rewrite Nat.eqb_refl in Hs |- *; cbn [Vstep] in Hs |- *; exact Hs).
Qed.

Lemma V_mono_rec_step :
  forall k' (IH : forall rho Delta W tau (v1 v2 : val),
      V (S k') rho Delta W tau v1 v2 -> V k' rho Delta W tau v1 v2)
    rho Delta W l tau0 (v1 v2 : val),
  V (S (S k')) rho Delta W (TRec tau0 @ l) v1 v2 ->
  V (S k') rho Delta W (TRec tau0 @ l) v1 v2.
Proof.
  intros k' IH rho Delta W l tau0 v1 v2 Hs.
  rewrite V_rec_eq in Hs |- *.
  eapply obs_case_imp; [|exact Hs]. intro Hp. apply IH. exact Hp.
Qed.

Lemma V_mono_arrow_step :
  forall k' rho Delta W l le tau1 tau2 (v1 v2 : val),
  V (S (S k')) rho Delta W (TArrow le tau1 tau2 @ l) v1 v2 ->
  V (S k') rho Delta W (TArrow le tau1 tau2 @ l) v1 v2.
Proof.
  intros k' rho Delta W l le tau1 tau2 v1 v2 Hs.
  destruct v1; destruct v2;
  try (rewrite V_arrow_eq in Hs |- *; eapply obs_case_imp; [|exact Hs];
       intros Hp j Hj a1 a2 Hc1 Hc2 Harg; apply Hp; [lia | exact Hc1 | exact Hc2 | exact Harg]);
  try (unfold V in Hs |- *; cbn [fam] in Hs |- *;
       rewrite Nat.eqb_refl in Hs |- *; cbn [Vstep] in Hs |- *; exact Hs).
Qed.

Lemma V_mono_forall_step :
  forall k' rho Delta W l le tau0 (v1 v2 : val),
  V (S (S k')) rho Delta W (TForall le tau0 @ l) v1 v2 ->
  V (S k') rho Delta W (TForall le tau0 @ l) v1 v2.
Proof.
  intros k' rho Delta W l le tau0 v1 v2 Hs.
  destruct v1; destruct v2;
  try (rewrite V_forall_eq in Hs |- *; eapply obs_case_imp; [|exact Hs];
       intros Hp j Hj R; apply (Hp j); lia);
  try (unfold V in Hs |- *; cbn [fam] in Hs |- *;
       rewrite Nat.eqb_refl in Hs |- *; cbn [Vstep] in Hs |- *; exact Hs).
Qed.

Lemma V_mono_lforall_step :
  forall k' rho Delta W l le tau0 (v1 v2 : val),
  V (S (S k')) rho Delta W (TLForall le tau0 @ l) v1 v2 ->
  V (S k') rho Delta W (TLForall le tau0 @ l) v1 v2.
Proof.
  intros k' rho Delta W l le tau0 v1 v2 Hs.
  destruct v1; destruct v2;
  try (rewrite V_lforall_eq in Hs |- *; eapply obs_case_imp; [|exact Hs];
       intros Hp j Hj l'; apply (Hp j); lia);
  try (unfold V in Hs |- *; cbn [fam] in Hs |- *;
       rewrite Nat.eqb_refl in Hs |- *; cbn [Vstep] in Hs |- *; exact Hs).
Qed.


Lemma V_mono_ref_step :
  forall k' (IH : forall rho Delta W tau (v1 v2 : val),
      V (S k') rho Delta W tau v1 v2 -> V k' rho Delta W tau v1 v2)
    rho Delta W l tau0 (v1 v2 : val),
  V (S (S k')) rho Delta W (TRef tau0 @ l) v1 v2 ->
  V (S k') rho Delta W (TRef tau0 @ l) v1 v2.
Proof.
  intros k' IH rho Delta W l tau0 v1 v2 Hs.
  destruct v1 as [| | | | | | | | | l1 | |];
  destruct v2 as [| | | | | | | | | l2 | |];
  try (rewrite V_ref_eq in Hs |- *; eapply obs_case_imp; [|exact Hs];
       intro Hp;
       destruct (wmap W l1) as [[l2' tau']|]; simpl in *; try tauto;
       destruct Hp as [H1 [H2 H3]];
       split; [exact H1 | split; [exact H2 |]];
       destruct (wst1 W !! l1); simpl in *; try tauto;
       destruct (wst2 W !! l2); simpl in *; try tauto;
       apply IH; exact H3);
  try (unfold V in Hs |- *; cbn [fam] in Hs |- *;
       rewrite Nat.eqb_refl in Hs |- *; cbn [Vstep] in Hs |- *; exact Hs).
Qed.


Lemma V_mono : forall k rho Delta W (tau : sectype) (v1 v2 : val),
  V (S k) rho Delta W tau v1 v2 -> V k rho Delta W tau v1 v2.
Proof.
  induction k as [|k' IH].
  - intros rho Delta W tau v1 v2 Hs. apply V_zero.
  - intros rho Delta W tau v1 v2 Hs.
    destruct tau as [l t]; destruct t.
    + apply V_mono_unit. exact Hs.
    + apply V_mono_bool. exact Hs.
    + apply V_mono_nat. exact Hs.
    + apply V_mono_tvar. exact Hs.
    + apply (V_mono_ref_step k' IH). exact Hs.
    + apply V_mono_arrow_step. exact Hs.
    + apply (V_mono_prod_step k' IH). exact Hs.
    + apply (V_mono_sum_step k' IH). exact Hs.
    + apply V_mono_forall_step. exact Hs.
    + apply V_mono_lforall_step. exact Hs.
    + apply (V_mono_exist_step k' IH). exact Hs.
    + apply (V_mono_rec_step k' IH). exact Hs.
Qed.


Lemma E_mono : forall k rho Delta W (tau : sectype) (e1 e2 : expr),
  E (S k) rho Delta W tau e1 e2 -> E k rho Delta W tau e1 e2.
Proof.
  induction k as [|k' IH].
  - intros rho Delta W tau e1 e2 Hs. apply E_zero.
  - intros rho Delta W tau e1 e2 Hs.
    rewrite E_S_eq in Hs |- *.
    intros n1 n2 v1 v2 s1 s2 H1 H2 Hle.
    destruct (Hs n1 n2 v1 v2 s1 s2 H1 H2 ltac:(lia)) as [wm' [Hext [HV HF]]].
    exists wm'; split; [exact Hext | split].
    + assert (Hcase : S (S k') - n1 - n2 - 1 = S k' - n1 - n2 - 1 \/
                      S (S k') - n1 - n2 - 1 = S (S k' - n1 - n2 - 1)) by lia.
      destruct Hcase as [Heq | Heq].
      * rewrite Heq in HV. exact HV.
      * rewrite Heq in HV. apply V_mono. exact HV.
    + apply FrameV_mono with (r := S (S k') - n1 - n2 - 1); [lia | exact HF].
Qed.


Lemma E_mono_n : forall k r rho Delta W (tau : sectype) e1 e2,
  r <= k -> E k rho Delta W tau e1 e2 -> E r rho Delta W tau e1 e2.
Proof.
  induction k as [|k IH]; intros r rho Delta W tau e1 e2 Hle HE.
  - assert (r = 0) by lia. subst. apply E_zero.
  - destruct r as [|r'].
    + apply E_zero.
    + destruct (Nat.eq_dec r' k) as [->|Hne].
      * exact HE.
      * assert (Hr : S r' <= k) by lia.
        apply (IH (S r') rho Delta W tau e1 e2 Hr). apply E_mono. exact HE.
Qed.

Lemma EnvRel_lookup : forall k rho Delta W Gamma d1 d2 x tau,
  EnvRel k rho Delta W Gamma d1 d2 ->
  Gamma !! x = Some tau ->
  V k rho Delta W tau (d1 x) (d2 x).
Proof.
  intros k rho Delta W Gamma.
  induction Gamma as [|tau0 Gamma IH]; intros d1 d2 x tau Hrel Hx.
  - simpl in Hx. discriminate.
  - destruct x as [|x].
    + simpl in Hx. injection Hx as Heq. subst tau0.
      simpl in Hrel. destruct Hrel as [HV _]. simpl. exact HV.
    + simpl in Hx. simpl in Hrel. destruct Hrel as [_ Htail].
      simpl. eapply (IH (fun n => d1 (S n)) (fun n => d2 (S n)) x tau);
        [exact Htail | exact Hx].
Qed.

Lemma fundamental_var : forall Gamma x tau,
  Gamma !! x = Some tau ->
  forall k rho Delta W d1 d2,
    EnvRel k rho Delta W Gamma d1 d2 ->
    E k rho Delta W tau (#(d1 x)) (#(d2 x)).
Proof.
  intros Gamma x tau Hx k rho Delta W d1 d2 Hrel.
  destruct k as [|k'].
  - apply E_zero.
  - apply E_value.
    apply V_mono with (k := k').
    exact (@EnvRel_lookup (S k') rho Delta W Gamma d1 d2 x tau Hrel Hx).
Qed.


Lemma V_unit_any : forall k rho Delta W (v1 v2 : val),
  V k rho Delta W (TUnit @ LLabel ⊥) v1 v2.
Proof.
  intros k rho Delta W v1 v2. destruct k as [|k'].
  - apply V_zero.
  - rewrite V_unit_eq. apply obs_case_true. apply obs_bot. exact I.
Qed.

Lemma V_bool_bot : forall k rho Delta W b,
  V k rho Delta W (TBool @ LLabel ⊥) (BoolV b) (BoolV b).
Proof.
  intros k rho Delta W b. destruct k as [|k'].
  - apply V_zero.
  - rewrite V_bool_eq. apply obs_case_true. apply obs_bot. reflexivity.
Qed.

Lemma V_nat_bot : forall k rho Delta W n,
  V k rho Delta W (TNat @ LLabel ⊥) (NatV n) (NatV n).
Proof.
  intros k rho Delta W n. destruct k as [|k'].
  - apply V_zero.
  - rewrite V_nat_eq. apply obs_case_true. apply obs_bot. reflexivity.
Qed.


Lemma fundamental_unit : forall k rho Delta W,
  E k rho Delta W (TUnit @ LLabel ⊥) Unit Unit.
Proof.
  intros k rho Delta W. destruct k as [|k'].
  - apply E_zero.
  - apply (E_value k' rho Delta W (TUnit @ LLabel ⊥) UnitV UnitV).
    apply V_unit_any.
Qed.

Lemma fundamental_bool : forall k rho Delta W b,
  E k rho Delta W (TBool @ LLabel ⊥) (Bool b) (Bool b).
Proof.
  intros k rho Delta W b. destruct k as [|k'].
  - apply E_zero.
  - apply (E_value k' rho Delta W (TBool @ LLabel ⊥) (BoolV b) (BoolV b)).
    apply V_bool_bot.
Qed.

Lemma fundamental_nat : forall k rho Delta W n,
  E k rho Delta W (TNat @ LLabel ⊥) (Nat n) (Nat n).
Proof.
  intros k rho Delta W n. destruct k as [|k'].
  - apply E_zero.
  - apply (E_value k' rho Delta W (TNat @ LLabel ⊥) (NatV n) (NatV n)).
    apply V_nat_bot.
Qed.



Lemma obs_case_label_mono : forall l l' (P : Prop),
  l ⊑ l' -> obs_case l P -> obs_case l' P.
Proof.
  intros l l' P Hle Ho. unfold obs_case in *.
  destruct (obs_bool l) eqn:El; destruct (obs_bool l') eqn:El'; simpl in *.
  - exact Ho.
  - exact I.
  - exfalso.
    assert (l ⊑ ζ) as Hlz.
    { eapply order_trans; [exact Hle | apply (proj1 (obs_bool_true l') El')]. }
    pose proof (proj2 (obs_bool_true l) Hlz) as Ht.
    rewrite El in Ht. discriminate.
  - exact I.
Qed.


Lemma V_label_mono : forall k rho Delta W (t : type) (l l' : label_term) (v1 v2 : val),
  interp_label rho l ⊑ interp_label rho l' ->
  V k rho Delta W (t @ l) v1 v2 ->
  V k rho Delta W (t @ l') v1 v2.
Proof.
  intros k rho Delta W t l l' v1 v2 Hll Hs.
  destruct k as [|k'].
  - apply V_zero.
  - destruct t.
    + rewrite V_unit_eq in Hs |- *. exact (@obs_case_label_mono (interp_label rho l) (interp_label rho l') _ Hll Hs).
    + rewrite V_bool_eq in Hs |- *. exact (@obs_case_label_mono (interp_label rho l) (interp_label rho l') _ Hll Hs).
    + rewrite V_nat_eq in Hs |- *. exact (@obs_case_label_mono (interp_label rho l) (interp_label rho l') _ Hll Hs).
    + rewrite V_tvar_eq in Hs |- *.
      destruct (obs_bool (interp_label rho l')) eqn:E'.
      * assert (Hlobs : interp_label rho l ⊑ ζ).
        { eapply order_trans; [exact Hll | apply (proj1 (obs_bool_true _) E')]. }
        assert (El : obs_bool (interp_label rho l) = true).
        { apply (proj2 (obs_bool_true _)). exact Hlobs. }
        unfold obs_case in Hs. rewrite El in Hs.
        unfold obs_case. rewrite E'.
        apply (@tyrel_mono_label (Delta x) (interp_label rho l) (interp_label rho l') Hll (S k') W v1 v2).
        exact Hs.
      * unfold obs_case. rewrite E'. exact I.
    + (* TRef *)
      destruct v1 as [| | | | | | | | | l1 | |];
      destruct v2 as [| | | | | | | | | l2 | |];
      try (rewrite V_ref_eq in Hs |- *; exact (@obs_case_label_mono (interp_label rho l) (interp_label rho l') _ Hll Hs));
      try (unfold V in Hs |- *; cbn [fam] in Hs |- *;
           rewrite Nat.eqb_refl in Hs |- *; cbn [Vstep] in Hs |- *;
           exact (@obs_case_label_mono (interp_label rho l) (interp_label rho l') _ Hll Hs)).
    + (* TArrow *)
      destruct v1; destruct v2;
      try (rewrite V_arrow_eq in Hs |- *; exact (@obs_case_label_mono (interp_label rho l) (interp_label rho l') _ Hll Hs));
      try (unfold V in Hs |- *; cbn [fam] in Hs |- *;
           rewrite Nat.eqb_refl in Hs |- *; cbn [Vstep] in Hs |- *;
           exact (@obs_case_label_mono (interp_label rho l) (interp_label rho l') _ Hll Hs)).
    + (* TProd *)
      destruct v1; destruct v2;
      try (rewrite V_prod_eq in Hs |- *; exact (@obs_case_label_mono (interp_label rho l) (interp_label rho l') _ Hll Hs));
      try (unfold V in Hs |- *; cbn [fam] in Hs |- *;
           rewrite Nat.eqb_refl in Hs |- *; cbn [Vstep] in Hs |- *;
           exact (@obs_case_label_mono (interp_label rho l) (interp_label rho l') _ Hll Hs)).
    + (* TSum *)
      destruct v1; destruct v2;
      try (rewrite V_sum_eq_l in Hs |- *; exact (@obs_case_label_mono (interp_label rho l) (interp_label rho l') _ Hll Hs));
      try (rewrite V_sum_eq_r in Hs |- *; exact (@obs_case_label_mono (interp_label rho l) (interp_label rho l') _ Hll Hs));
      try (unfold V in Hs |- *; cbn [fam] in Hs |- *;
           rewrite Nat.eqb_refl in Hs |- *; cbn [Vstep] in Hs |- *;
           exact (@obs_case_label_mono (interp_label rho l) (interp_label rho l') _ Hll Hs)).
    + (* TForall *)
      destruct v1; destruct v2;
      try (rewrite V_forall_eq in Hs |- *; exact (@obs_case_label_mono (interp_label rho l) (interp_label rho l') _ Hll Hs));
      try (unfold V in Hs |- *; cbn [fam] in Hs |- *;
           rewrite Nat.eqb_refl in Hs |- *; cbn [Vstep] in Hs |- *;
           exact (@obs_case_label_mono (interp_label rho l) (interp_label rho l') _ Hll Hs)).
    + (* TLForall *)
      destruct v1; destruct v2;
      try (rewrite V_lforall_eq in Hs |- *; exact (@obs_case_label_mono (interp_label rho l) (interp_label rho l') _ Hll Hs));
      try (unfold V in Hs |- *; cbn [fam] in Hs |- *;
           rewrite Nat.eqb_refl in Hs |- *; cbn [Vstep] in Hs |- *;
           exact (@obs_case_label_mono (interp_label rho l) (interp_label rho l') _ Hll Hs)).
    + (* TExist *)
      destruct v1; destruct v2;
      try (rewrite V_exist_eq in Hs |- *; exact (@obs_case_label_mono (interp_label rho l) (interp_label rho l') _ Hll Hs));
      try (unfold V in Hs |- *; cbn [fam] in Hs |- *;
           rewrite Nat.eqb_refl in Hs |- *; cbn [Vstep] in Hs |- *;
           exact (@obs_case_label_mono (interp_label rho l) (interp_label rho l') _ Hll Hs)).
    + (* TRec *)
      rewrite V_rec_eq in Hs |- *. exact (@obs_case_label_mono (interp_label rho l) (interp_label rho l') _ Hll Hs).
Qed.


Definition VsubP (t t' : type) (s : t <: t') : Prop :=
  forall k rho Delta W (l : label_term) (v1 v2 : val),
    V k rho Delta W (t @ l) v1 v2 -> V k rho Delta W (t' @ l) v1 v2.

Definition VsubS (tau tau' : sectype) (s : tau <:ₛ tau') : Prop :=
  forall k rho Delta W (v1 v2 : val),
    V k rho Delta W tau v1 v2 -> V k rho Delta W tau' v1 v2.

Lemma E_from_Vsub : forall (tau tau' : sectype),
  (forall k rho Delta W (v1 v2 : val),
      V k rho Delta W tau v1 v2 -> V k rho Delta W tau' v1 v2) ->
  forall k rho Delta W (e1 e2 : expr),
    E k rho Delta W tau e1 e2 -> E k rho Delta W tau' e1 e2.
Proof.
  intros tau tau' Vsub k. destruct k as [|k'].
  - intros rho Delta W e1 e2 HE. apply E_zero.
  - intros rho Delta W e1 e2 HE. rewrite E_S_eq in HE |- *.
    intros n1 n2 v1 v2 s1 s2 H1 H2 Hle.
    destruct (HE n1 n2 v1 v2 s1 s2 H1 H2 Hle) as [wm' [Hext [HV HF]]].
    exists wm'; split; [exact Hext | split].
    + apply (Vsub (S k' - n1 - n2 - 1) rho Delta (s1, s2, wm') v1 v2). exact HV.
    + exact HF.
Qed.

Lemma V_secsubtype : forall (tau tau' : sectype), tau <:ₛ tau' ->
  forall k rho Delta W (v1 v2 : val),
    V k rho Delta W tau v1 v2 -> V k rho Delta W tau' v1 v2.
Proof.
  intros tau tau' Hsub.
  apply (secsubtype_mut VsubP VsubS).
  - (* TSubRefl *) intros t k rho Delta W l v1 v2 HV. exact HV.
  - (* TSubTrans *) intros t1 t2 t3 s IHP1 s0 IHP2 k rho Delta W l v1 v2 HV.
    apply (IHP2 k rho Delta W l v1 v2). apply (IHP1 k rho Delta W l v1 v2). exact HV.
  - (* TArrowSub *) intros tau1 tau1' tau2 tau2' le1 le2 s IHP1 s0 IHP2 f k rho Delta W l v1 v2 HV.
    destruct k as [|k'].
    + apply V_zero.
    + destruct v1 as [| | | e1 | | | | | | | |];
      destruct v2 as [| | | e2 | | | | | | | |];
      try (rewrite V_arrow_eq in HV |- *; eapply obs_case_imp; [|exact HV];
           intros Hp j Hj a1 a2 Hc1 Hc2 Harg;
           apply (E_from_Vsub tau2 tau2' IHP2 j rho Delta W
                    (App (Lam e1) (a1)) (App (Lam e2) (a2)));
           apply (Hp j Hj a1 a2 Hc1 Hc2);
           apply (E_from_Vsub tau1' tau1 IHP1 j rho Delta W a1 a2);
           exact Harg);
      try (unfold V in HV |- *; cbn [fam] in HV |- *;
           rewrite Nat.eqb_refl in HV |- *; cbn [Vstep] in HV |- *; exact HV).
  - (* TForallSub *) intros tau1 tau2 le1 le2 f s IHP k rho Delta W l v1 v2 HV.
    destruct k as [|k'].
    + apply V_zero.
    + destruct v1 as [| | | | e1 | | | | | | |];
      destruct v2 as [| | | | e2 | | | | | | |];
      try (rewrite V_forall_eq in HV |- *; eapply obs_case_imp; [|exact HV];
           intros Hp j Hj R;
           apply (E_from_Vsub tau1 tau2 IHP j rho
                    (extend_tenv R Delta) W (TApp (TLam e1)) (TApp (TLam e2)));
           apply (Hp j Hj R));
      try (unfold V in HV |- *; cbn [fam] in HV |- *;
           rewrite Nat.eqb_refl in HV |- *; cbn [Vstep] in HV |- *; exact HV).
  - (* TLForallSub *) intros tau1 tau2 le1 le2 f s IHP k rho Delta W l v1 v2 HV.
    destruct k as [|k'].
    + apply V_zero.
    + destruct v1 as [| | | | | e1 | | | | | |];
      destruct v2 as [| | | | | e2 | | | | | |];
      try (rewrite V_lforall_eq in HV |- *; eapply obs_case_imp; [|exact HV];
           intros Hp j Hj l';
           apply (E_from_Vsub tau1 tau2 IHP j
                    (extend_rho l' rho) Delta W (TLApp (TLLam e1)) (TLApp (TLLam e2)));
           apply (Hp j Hj l'));
      try (unfold V in HV |- *; cbn [fam] in HV |- *;
           rewrite Nat.eqb_refl in HV |- *; cbn [Vstep] in HV |- *; exact HV).
  - (* TProdSub *) intros tau1 tau1' tau2 tau2' s IHP1 s0 IHP2 k rho Delta W l v1 v2 HV.
    destruct k as [|k'].
    + apply V_zero.
    + destruct v1; destruct v2;
      try (rewrite V_prod_eq in HV |- *; eapply obs_case_imp; [|exact HV];
           intro Hp; destruct Hp as [H1 H2]; split;
           [ apply (IHP1 k' rho Delta W); exact H1
           | apply (IHP2 k' rho Delta W); exact H2 ]);
      try (unfold V in HV |- *; cbn [fam] in HV |- *;
           rewrite Nat.eqb_refl in HV |- *; cbn [Vstep] in HV |- *; exact HV).
  - (* TSumSub *) intros tau1 tau1' tau2 tau2' s IHP1 s0 IHP2 k rho Delta W l v1 v2 HV.
    destruct k as [|k'].
    + apply V_zero.
    + destruct v1; destruct v2;
      try (rewrite V_sum_eq_l in HV |- *; eapply obs_case_imp; [|exact HV];
           intro Hp; apply (IHP1 k' rho Delta W); exact Hp);
      try (rewrite V_sum_eq_r in HV |- *; eapply obs_case_imp; [|exact HV];
           intro Hp; apply (IHP2 k' rho Delta W); exact Hp);
      try (unfold V in HV |- *; cbn [fam] in HV |- *;
           rewrite Nat.eqb_refl in HV |- *; cbn [Vstep] in HV |- *; exact HV).
  - (* TRecSub *) intros tau1 tau2 s IHP k rho Delta W l v1 v2 HV.
    destruct k as [|k'].
    + apply V_zero.
    + rewrite V_rec_eq in HV |- *.
      eapply obs_case_imp; [|exact HV]. intro Hp.
      apply (IHP k' rho Delta W (unfold_val v1) (unfold_val v2)). exact Hp.
  - (* TSubsec *) intros l l' t t' f s IHP k rho Delta W v1 v2 HV.
    apply (IHP k rho Delta W l' v1 v2).
    eapply V_label_mono; [apply flowsto_sound; exact f | exact HV].
  - exact Hsub.
Qed.


Lemma fundamental_sub : forall Gamma (e : expr) tau tau',
  (forall k rho Delta W d1 d2,
      EnvRel k rho Delta W Gamma d1 d2 ->
      E k rho Delta W tau' (e.[env_subst_vals d1]) (e.[env_subst_vals d2])) ->
  tau' <:ₛ tau ->
  forall k rho Delta W d1 d2,
    EnvRel k rho Delta W Gamma d1 d2 ->
    E k rho Delta W tau (e.[env_subst_vals d1]) (e.[env_subst_vals d2]).
Proof.
  intros Gamma e tau tau' IH Hsub k rho Delta W d1 d2 Hrel.
  apply (E_from_Vsub tau' tau
           (fun kk rr dd ww a b => @V_secsubtype tau' tau Hsub kk rr dd ww a b)).
  apply IH. exact Hrel.
Qed.


Lemma rev_cons' {A : Type} (a : A) (l : list A) : rev (a :: l) = rev l ++ [a].
Proof. induction l as [|b l IH]; simpl; reflexivity. Qed.

Lemma fill_rev_cons (Ki : ectx_item) (L : list ectx_item) (e : expr) :
  fill (rev (Ki :: L)) e = fill_item Ki (fill (rev L) e).
Proof.
  rewrite rev_cons'. rewrite fill_app. simpl. reflexivity.
Qed.

Lemma app_fill_inv_rev (L : list ectx_item) (h f1 f2 : expr) :
  App f1 f2 = fill (rev L) h ->
  (rev L = [] /\ h = App f1 f2) \/
  (exists K', rev L = K' ++ [AppLCtx f2] /\ f1 = fill K' h) \/
  (exists v1 K', to_val f1 = Some v1 /\
      rev L = K' ++ [AppRCtx v1] /\ f2 = fill K' h).
Proof.
  intros Heq.
  induction L as [|Ki L' IH].
  - simpl in Heq. left. split; [reflexivity | symmetry; exact Heq].
  - rewrite fill_rev_cons in Heq.
    destruct Ki; simpl in Heq; try discriminate Heq.
    + (* AppLCtx e *) injection Heq as HX Harg.
      right; left. exists (rev L'). split.
      * rewrite rev_cons'. rewrite Harg. reflexivity.
      * exact HX.
    + (* AppRCtx v *) injection Heq as HX Harg.
      right; right. exists v1, (rev L'). split.
      * rewrite HX. apply to_val_of_val.
      * split.
        -- rewrite rev_cons'. reflexivity.
        -- exact Harg.
Qed.

Lemma app_fill_inv (K : list ectx_item) (h f1 f2 : expr) :
  App f1 f2 = fill K h ->
  (K = [] /\ h = App f1 f2) \/
  (exists K', K = K' ++ [AppLCtx f2] /\ f1 = fill K' h) \/
  (exists v1 K', to_val f1 = Some v1 /\
      K = K' ++ [AppRCtx v1] /\ f2 = fill K' h).
Proof.
  intros Heq.
  pose proof (app_fill_inv_rev (rev K) h f1 f2) as Hinv.
  rewrite rev_involutive in Hinv.
  apply Hinv. exact Heq.
Qed.


Lemma head_step_app_inv (f1 f2 : expr) (σ : state) (e' : expr) (σ' : state) :
  head_step (App f1 f2) σ [] e' σ' [] ->
  exists body v2, f1 = Lam body /\ to_val f2 = Some v2 /\
    e' = body.[f2/] /\ σ' = σ.
Proof.
  intros Hs. inversion Hs; subst; try discriminate.
  exists e1, v2. repeat split; auto.
Qed.


Lemma pstep_app_inv (f1 f2 : expr) (σ : state) (e' : expr) (σ' : state) :
  pstep (App f1 f2, σ) (e', σ') ->
  (exists f1', e' = App f1' f2 /\ pstep (f1, σ) (f1', σ')) \/
  (exists v1, to_val f1 = Some v1 /\
     ((exists f2', e' = App (#v1) f2' /\ pstep (f2, σ) (f2', σ')) \/
      (exists body v2, f1 = Lam body /\ to_val f2 = Some v2 /\
          e' = body.[f2/] /\ σ' = σ))).
Proof.
  intros Hp. inversion Hp as [K h h' Hfill Heq Hhead]; subst. simpl in *.
  destruct (app_fill_inv K h f1 f2 Hfill) as
    [[HK Hh] | [[K' [HK Hf1]] | [v1 [K' [Hv1 [HK Hf2]]]]]]; subst.
  - (* K=[] *)
    destruct (head_step_app_inv f1 f2 σ h' σ' Hhead) as
      [body [v2 [Hf1 [Hv2 [He' Hs']]]]].
    right. exists (LamV body). split.
    + rewrite Hf1. exact (to_val_of_val (LamV body)).
    + right. exists body, v2. repeat split; auto.
  - (* AppLCtx *)
    left. exists (fill K' h'). split.
    + rewrite fill_app. simpl. reflexivity.
    + eapply Ectx_step; eauto.
  - (* AppRCtx *)
    right. exists v1. split.
    + exact Hv1.
    + left. exists (fill K' h'). split.
      * rewrite fill_app. simpl. reflexivity.
      * eapply Ectx_step; eauto.
Qed.


Lemma pstep_app_lam_inv (b1 a1 : expr) (σ : state) (e' : expr) (σ' : state) :
  pstep (App (Lam b1) a1, σ) (e', σ') ->
  (exists a1', e' = App (Lam b1) a1' /\ pstep (a1, σ) (a1', σ')) \/
  (exists w1, to_val a1 = Some w1 /\ e' = b1.[a1/] /\ σ' = σ).
Proof.
  intros Hp.
  destruct (pstep_app_inv (Lam b1) a1 σ e' σ' Hp) as
    [[f1' [He' Hstep]] |
     [v1 [Hval [[a1' [He' Hstep]] |
                [body [w2 [Hf1 [Hval2 [He' Hs']]]]]]]]].
  - exfalso. exact (pstep_value (LamV b1) σ f1' σ' Hstep).
  - assert (v1 = LamV b1) as Hv1.
    { inversion Hval. reflexivity. }
    subst v1. left. exists a1'. split; auto.
  - inversion Hf1 as [Hb]. subst body. right. exists w2. split; [exact Hval2 | split].
    + exact He'.
    + exact Hs'.
Qed.


Lemma steps_app_lam_value_inv (n : nat) (b1 a1 : expr) (σ : state) (v : val) (σ' : state) :
  steps n (App (Lam b1) a1, σ) (#v, σ') ->
  exists m m' w1 σ1,
    steps m (a1, σ) (#w1, σ1) /\
    steps m' (b1.[#w1/], σ1) (#v, σ') /\
    n = S (m + m').
Proof.
  revert b1 a1 σ v σ'.
  induction n as [|n IH]; intros b1 a1 σ v σ' Hs.
  - inversion Hs. destruct v; simpl in H0; discriminate H0.
  - inversion Hs; subst. simpl in H1. destruct y as [ey σy].
    destruct (pstep_app_lam_inv b1 a1 σ ey σy H1) as
      [[a1' [He' Hstepa]] | [w1 [Hval [He' Hs']]]].
    + subst ey. simpl in Hstepa.
      destruct (IH b1 a1' σy v σ' H2) as [m [m' [w1 [σ1 [Hrun1 [Hbody Hn]]]]]].
      exists (S m), m', w1, σ1. split.
      * apply (steps_S m (a1, σ) (a1', σy) (#w1, σ1) Hstepa Hrun1).
      * split.
        -- exact Hbody.
        -- rewrite Hn. reflexivity.
    + subst ey. subst σy.
      pose proof (@of_val_to_val a1 w1 Hval) as Ha1.
      exists 0, n, w1, σ. split.
      * rewrite <- Ha1. apply steps_0.
      * split.
        -- rewrite <- Ha1 in H2. exact H2.
        -- reflexivity.
Qed.


Lemma FrameV_trans : forall r W1 W2 W3,
  FrameV r W1 W2 -> FrameV r W2 W3 -> FrameV r W1 W3.
Proof.
  intros r W1 W2 W3 H12 H23. unfold FrameV in *.
  intros j Hj rho Delta tau v1 v2 HV.
  apply H23; [exact Hj | apply H12; [exact Hj | exact HV]].
Qed.



Lemma typed_bool_value_sub (e : expr) (tau tau' : sectype)
    (l0 : label_term) (v : val) :
  (forall (v0 : val) (l : label_term),
      e = #v0 -> tau' = TBool @ l -> exists b, v0 = BoolV b) ->
  tau' <:ₛ tau ->
  tau = TBool @ l0 ->
  e = #v ->
  exists b, v = BoolV b.
Proof.
  intros IH Hsub Htau He.
  destruct tau' as [l' t'].
  rewrite Htau in Hsub.
  assert (t' = TBool) as Ht' by (eapply secsubtype_bool_target; exact Hsub).
  subst t'.
  exact (IH v l' He eq_refl).
Qed.

Lemma typed_bool_value : forall (Gamma : list sectype) pc l (v : val),
  Gamma # pc ⊢ₜ #v : TBool @ l -> exists b, v = BoolV b.
Proof.
  intros Gamma pc l v Hty.
  remember (#v) as e eqn:He.
  remember (TBool @ l) as tau eqn:Htau.
  revert v l He Htau.
  induction Hty; intros v0 l0 He Htau; try discriminate Htau.
  all: try (destruct v0; simpl in He; try discriminate He).
  all: try (match goal with
            | He : Bool ?x = Bool ?y
              |- exists b', BoolV ?z = BoolV b' =>
                injection He as Hxy; subst; exists y; reflexivity
            end).
  all: try (eapply typed_bool_value_sub; eauto).
Qed.



Definition closed_val (v : val) : Prop := closed_expr (#v).

Lemma closed_val_bool : forall b, closed_val (BoolV b).
Proof. intros b. unfold closed_val, closed_expr. simpl. exact I. Qed.

Lemma closed_val_unit : closed_val UnitV.
Proof. unfold closed_val, closed_expr. simpl. exact I. Qed.

Lemma closed_val_nat : forall n, closed_val (NatV n).
Proof. intros n. unfold closed_val, closed_expr. simpl. exact I. Qed.

Lemma closed_val_of_typed_bool : forall Gamma pc l (v : val),
  Gamma # pc ⊢ₜ #v : TBool @ l -> closed_val v.
Proof.
  intros Gamma pc l v Hty.
  destruct (typed_bool_value Gamma pc l v Hty) as [b Hb]. subst v.
  apply closed_val_bool.
Qed.

Definition EnvRelClosed (d1 d2 : var -> val) : Prop :=
  forall x, closed_val (d1 x) /\ closed_val (d2 x).

Lemma EnvRelClosed_nil_like : forall (d1 d2 : var -> val),
  (forall x, closed_val (d1 x) /\ closed_val (d2 x)) ->
  EnvRelClosed d1 d2.
Proof. intros d1 d2 Hs. exact Hs. Qed.

Lemma EnvRelClosed_cons : forall (w1 w2 : val) (d1 d2 : var -> val),
  closed_val w1 -> closed_val w2 ->
  EnvRelClosed d1 d2 ->
  EnvRelClosed
    (fun x => match x with 0 => w1 | S n => d1 n end)
    (fun x => match x with 0 => w2 | S n => d2 n end).
Proof.
  intros w1 w2 d1 d2 Hw1 Hw2 Hd. unfold EnvRelClosed in *.
  intro x. destruct x as [|n].
  - split; assumption.
  - apply Hd.
Qed.


Lemma closed_lam_body : forall (b : expr),
  closed_expr (Lam b) -> forall sigma, b.[up sigma] = b.
Proof.
  intros b Hb sigma.
  apply (closed_under_subst_self 1 b (up sigma) Hb).
  intros x Hx. assert (x = 0) as -> by lia. unfold up. simpl. reflexivity.
Qed.


Lemma closed_under_0 : forall e, closed_under 0 e <-> closed_expr e.
Proof. intros e. unfold closed_expr. tauto. Qed.



Lemma fill_item_closed_inv : forall (Ki : ectx_item) e,
  closed_expr (fill_item Ki e) -> closed_expr e.
Proof.
  intros Ki e Hc. unfold closed_expr in *. destruct Ki; simpl in *; tauto.
Qed.

Lemma fill_closed_inv : forall (K : list ectx_item) e,
  closed_expr (fill K e) -> closed_expr e.
Proof.
  induction K as [|Ki K IH]; intros e Hc.
  - simpl in Hc. exact Hc.
  - simpl in Hc. apply (fill_item_closed_inv Ki). apply IH. exact Hc.
Qed.

Lemma fill_item_closed_replace : forall (Ki : ectx_item) e e',
  closed_expr (fill_item Ki e) -> closed_expr e' ->
  closed_expr (fill_item Ki e').
Proof.
  intros Ki e e' Hc He'. unfold closed_expr in *. destruct Ki; simpl in *; tauto.
Qed.

Lemma fill_closed_replace : forall (K : list ectx_item) e e',
  closed_expr (fill K e) -> closed_expr e' ->
  closed_expr (fill K e').
Proof.
  induction K as [|Ki K IH]; intros e e' Hc He'.
  - simpl in *. exact He'.
  - simpl in *. simpl. apply (IH (fill_item Ki e) (fill_item Ki e')).
    + exact Hc.
    + apply (fill_item_closed_replace Ki e e').
      * apply (fill_closed_inv K (fill_item Ki e)); exact Hc.
      * exact He'.
Qed.

Lemma to_val_closed : forall e v,
  closed_expr e -> to_val e = Some v -> closed_val v.
Proof.
  intros e v Hc Ht. unfold closed_val.
  rewrite <- (of_val_to_val e v Ht) in Hc. exact Hc.
Qed.

Definition closed_state (σ : state) : Prop :=
  forall l v, σ !! l = Some v -> closed_val v.

Lemma closed_state_update : forall σ l v,
  closed_state σ -> closed_val v -> closed_state (<[l := v]> σ).
Proof.
  intros σ l v Hs Hv l' w Hw.
  assert (Hlook : (<[l := v]> σ) !! l' = (if decide (l = l') then Some v else σ !! l'))
    by apply lookup_insert.
  rewrite Hlook in Hw.
  destruct (decide (l = l')) as [->|Hne].
  - injection Hw as Hw. subst. exact Hv.
  - exact (Hs l' w Hw).
Qed.

Lemma head_step_closed : forall e σ e' σ',
  head_step e σ [] e' σ' [] ->
  closed_expr e -> closed_state σ ->
  closed_expr e' /\ closed_state σ'.
Proof.
  intros e σ e' σ' Hstep Hc Hs.
  destruct Hstep; unfold closed_expr in *; simpl in *.
  - (* BetaS *)
    destruct Hc as [H1 H2]. split.
    + apply (closed_expr_beta e1 e2); assumption.
    + exact Hs.
  - (* TBeta *)
    split; [exact Hc|exact Hs].
  - (* LetInBetaS *)
    destruct Hc as [H1 H2]. split.
    + apply (closed_expr_beta e2 e1); assumption.
    + exact Hs.
  - (* SeqBetaS *)
    destruct Hc as [H1 H2]. split; [exact H2|exact Hs].
  - (* LBeta *)
    split; [exact Hc|exact Hs].
  - (* BinOpS *)
    split.
    + destruct op; simpl; exact I.
    + exact Hs.
  - (* IfFalseS *)
    destruct Hc as [H0 [H1 H2]]. split; [exact H2|exact Hs].
  - (* IfTrueS *)
    destruct Hc as [H0 [H1 H2]]. split; [exact H1|exact Hs].
  - (* Proj1S *)
    destruct Hc as [HA HB]. split.
    + eapply to_val_closed; [exact HA|eassumption].
    + exact Hs.
  - (* Proj2S *)
    destruct Hc as [HA HB]. split.
    + eapply to_val_closed; [exact HB|eassumption].
    + exact Hs.
  - (* CaseLS *)
    destruct Hc as [HA [HB HC]]. split.
    + apply (closed_expr_beta e1 e0); assumption.
    + exact Hs.
  - (* CaseRS *)
    destruct Hc as [HA [HB HC]]. split.
    + apply (closed_expr_beta e2 e0); assumption.
    + exact Hs.
  - (* AllocS *)
    split.
    + exact I.
    + apply closed_state_update; auto.
      eapply to_val_closed; [exact Hc|eassumption].
  - (* StoreS *)
    destruct Hc as [HA HB]. split.
    + exact I.
    + apply closed_state_update; auto.
      eapply to_val_closed; [exact HB|eassumption].
  - (* LoadS *)
    split.
    + exact (Hs l v H0).
    + exact Hs.
  - (* UnpackPackS *)
    destruct Hc as [H1 H2]. split.
    + apply (closed_expr_beta e2 e1); assumption.
    + exact Hs.
  - (* UnfoldFoldS *)
    split; [exact Hc|exact Hs].
Qed.

Lemma pstep_closed : forall e σ e' σ',
  closed_expr e -> closed_state σ -> pstep (e, σ) (e', σ') ->
  closed_expr e' /\ closed_state σ'.
Proof.
  intros e σ e' σ' Hc Hs Hp.
  inversion Hp as [K e1 e2 Hfill1 Hfill2 Hhead]; simpl in Hfill1, Hfill2, Hhead; subst.
  pose proof (fill_closed_inv K e1 Hc) as Hredex.
  destruct (head_step_closed e1 σ e2 σ' Hhead Hredex Hs) as [Hredex' Hs'].
  split.
  - apply (fill_closed_replace K e1 e2 Hc Hredex').
  - exact Hs'.
Qed.

Lemma steps_closed : forall n e σ e' σ',
  steps n (e, σ) (e', σ') ->
  closed_expr e -> closed_state σ ->
  closed_expr e' /\ closed_state σ'.
Proof.
  intros n e σ e' σ' Hs.
  remember (e, σ) as x eqn:Ex. remember (e', σ') as y eqn:Ey.
  revert e σ e' σ' Ex Ey.
  induction Hs as [z | n x0 y0 z Hp Hrest IH]; intros e σ e' σ' Ex Ey Hc Hst.
  - rewrite Ex in Ey. injection Ey as He' Hs'. subst.
    split; assumption.
  - inversion Ex; subst. destruct y0 as [ey sy]. simpl in *.
    destruct (pstep_closed e σ ey sy Hc Hst Hp) as [Hcy Hsy].
    apply (IH ey sy e' σ' eq_refl eq_refl Hcy Hsy).
Qed.

Lemma upn_closed_expr : forall k (s : var -> expr) x,
  (forall y, closed_expr (s y)) ->
  closed_under k (upn k s x).
Proof.
  induction k as [|k IH]; intros s x Hs.
  - change (closed_under 0 (s x)). exact (Hs x).
  - destruct x as [|y].
    + unfold up. simpl. lia.
    + unfold up. simpl.
      apply (closed_under_ren k (S k) (fun z => S z) (upn k s y)).
      * intros z Hz. lia.
      * apply IH. exact Hs.
Qed.

Lemma closed_under_subst_closed : forall k e (s : var -> expr),
  (forall x, closed_expr (s x)) ->
  closed_under k (e.[upn k s]).
Proof.
  intros k0 e. revert k0. induction e; intros k0 s Hs; simpl in *.
  - apply upn_closed_expr. exact Hs.
  - change (closed_under (S k0) (e.[upn (S k0) s])).
    apply (IHe (S k0) s). exact Hs.
  - split; [apply (IHe1 k0 s)|apply (IHe2 k0 s)]; exact Hs.
  - split.
    + apply (IHe k0 s). exact Hs.
    + change (closed_under (S k0) (e2.[upn (S k0) s])).
      apply (IHe0 (S k0) s). exact Hs.
  - split; [apply (IHe1 k0 s)|apply (IHe2 k0 s)]; exact Hs.
  - exact I.
  - exact I.
  - exact I.
  - split; [apply (IHe1 k0 s)|apply (IHe2 k0 s)]; exact Hs.
  - split.
    + apply (IHe1 k0 s). exact Hs.
    + split; [apply (IHe2 k0 s)|apply (IHe3 k0 s)]; exact Hs.
  - split; [apply (IHe1 k0 s)|apply (IHe2 k0 s)]; exact Hs.
  - apply (IHe k0 s). exact Hs.
  - apply (IHe k0 s). exact Hs.
  - apply (IHe k0 s). exact Hs.
  - apply (IHe k0 s). exact Hs.
  - split.
    + apply (IHe k0 s). exact Hs.
    + split.
      * change (closed_under (S k0) (e1.[upn (S k0) s])).
        apply (IHe0 (S k0) s). exact Hs.
      * change (closed_under (S k0) (e2.[upn (S k0) s])).
        apply (IHe1 (S k0) s). exact Hs.
  - exact I.
  - apply (IHe k0 s). exact Hs.
  - split; [apply (IHe1 k0 s)|apply (IHe2 k0 s)]; exact Hs.
  - apply (IHe k0 s). exact Hs.
  - apply (IHe k0 s). exact Hs.
  - apply (IHe k0 s). exact Hs.
  - apply (IHe k0 s). exact Hs.
  - apply (IHe k0 s). exact Hs.
  - apply (IHe k0 s). exact Hs.
  - split.
    + apply (IHe k0 s). exact Hs.
    + change (closed_under (S k0) (e2.[upn (S k0) s])).
      apply (IHe0 (S k0) s). exact Hs.
  - apply (IHe k0 s). exact Hs.
  - apply (IHe k0 s). exact Hs.
Qed.

Lemma closed_expr_env_subst : forall e (d : var -> val),
  (forall x, closed_val (d x)) ->
  closed_expr (e.[env_subst_vals d]).
Proof.
  intros e d Hd.
  change (closed_under 0 (e.[upn 0 (env_subst_vals d)])).
  apply closed_under_subst_closed. intros x.
  unfold env_subst_vals, closed_val. apply Hd.
Qed.

Lemma V_mono_n : forall k r rho Delta W tau (v1 v2 : val),
  r <= k -> V k rho Delta W tau v1 v2 -> V r rho Delta W tau v1 v2.
Proof.
  induction k as [|k IH]; intros r rho Delta W tau v1 v2 Hle HV.
  - assert (r = 0) by lia. subst. apply V_zero.
  - destruct r as [|r'].
    + apply V_zero.
    + destruct (Nat.eq_dec r' k) as [->|Hne].
      * exact HV.
      * assert (Hr : S r' <= k) by lia.
        apply (IH (S r') rho Delta W tau v1 v2 Hr). apply V_mono. exact HV.
Qed.

Lemma EnvRel_mono : forall k r rho Delta W Gamma d1 d2,
  r <= k ->
  EnvRel k rho Delta W Gamma d1 d2 ->
  EnvRel r rho Delta W Gamma d1 d2.
Proof.
  intros k r rho Delta W Gamma. revert k r.
  induction Gamma as [|tau Gamma IH]; intros k r d1 d2 Hle Hrel.
  - exact I.
  - destruct Hrel as [HV Htail]. split.
    + apply (V_mono_n k r rho Delta W tau (d1 0) (d2 0)); [exact Hle|exact HV].
    + apply (IH k r (fun n => d1 (S n)) (fun n => d2 (S n)) Hle Htail).
Qed.

Lemma EnvRel_frame : forall r W W' rho Delta Gamma d1 d2,
  FrameV r W W' ->
  EnvRel r rho Delta W Gamma d1 d2 ->
  EnvRel r rho Delta W' Gamma d1 d2.
Proof.
  intros r W W' rho Delta Gamma. revert r W W'.
  induction Gamma as [|tau Gamma IH]; intros r W W' d1 d2 HF Hrel.
  - exact I.
  - destruct Hrel as [HV Htail]. split.
    + assert (Hrr : r <= r) by lia.
      apply (HF r Hrr rho Delta tau (d1 0) (d2 0) HV).
    + apply (IH r W W' (fun n => d1 (S n)) (fun n => d2 (S n)) HF Htail).
Qed.

Lemma map_ext_trans : forall (wm1 wm2 wm3 : loc -> option (loc * sectype)),
  (forall l x, wm1 l = Some x -> wm2 l = Some x) ->
  (forall l x, wm2 l = Some x -> wm3 l = Some x) ->
  (forall l x, wm1 l = Some x -> wm3 l = Some x).
Proof. intros wm1 wm2 wm3 H12 H23 l x Hx. apply H23. apply H12. exact Hx. Qed.

Lemma map_ext_comp : forall W W' W'',
  (forall l l' tau0, wmap W l = Some (l', tau0) -> wmap W' l = Some (l', tau0)) ->
  (forall l l' tau0, wmap W' l = Some (l', tau0) -> wmap W'' l = Some (l', tau0)) ->
  (forall l l' tau0, wmap W l = Some (l', tau0) -> wmap W'' l = Some (l', tau0)).
Proof.
  intros W W' W'' H1 H2 l l' tau0 Hx.
  apply H2. apply H1. exact Hx.
Qed.

Lemma steps_app_nonlam : forall n (vf : val) a (σ : state) v (σ' : state),
  (forall b, vf <> LamV b) ->
  steps n (App (#vf) a, σ) (#v, σ') -> False.
Proof.
  induction n as [|n IH]; intros vf a σ v σ' Hnl Hs.
  - inversion Hs. destruct v; simpl in H0; discriminate H0.
  - inversion Hs; subst. simpl in H1. destruct y as [ey σy].
    destruct (pstep_app_inv (#vf) a σ ey σy H1) as
      [[f1' [Heq Hstep]] |
       [w [Hval [[a' [Heq Hstep]] |
                 [body [w2 [Hf [Hval2 [Heq Hs']]]]]]]]].
    + subst ey. exfalso. exact (pstep_value vf σ f1' σy Hstep).
    + subst ey.
      assert (Hwvf : w = vf).
      { rewrite (to_val_of_val vf) in Hval. injection Hval. auto. }
      subst w.
      exfalso. eapply (IH vf a' σy v σ' Hnl H2).
    + subst ey. exfalso.
      assert (Hvf : vf = LamV body).
      { apply (of_val_inj vf (LamV body)). exact Hf. }
      exact (Hnl body Hvf).
Qed.

Lemma steps_app_value_inv : forall n f a (σ : state) v (σ' : state),
  steps n (App f a, σ) (#v, σ') ->
  exists nf vf σf, steps nf (f, σ) (#vf, σf) /\
  exists b, vf = LamV b /\
  exists na w σa nb,
    steps na (a, σf) (#w, σa) /\
    steps nb (b.[#w/], σa) (#v, σ') /\
    n = nf + 1 + na + nb.
Proof.
  induction n as [|n IH]; intros f a σ v σ' Hs.
  - inversion Hs. destruct v; simpl in H0; discriminate H0.
  - inversion Hs; subst. simpl in H1. destruct y as [ey σy].
    destruct (pstep_app_inv f a σ ey σy H1) as
      [[f1' [Heq Hstep]] |
       [v1 [Hval [Ha_step | Hbeta]]]].
    + (* f steps *)
      subst ey.
      destruct (IH f1' a σy v σ' H2) as
        [nf [vf [σf [Hrunf [b [Hvf [na [w [σa [nb [Hruna [Hrunb Hn]]]]]]]]]]]].
      exists (S nf), vf, σf. split.
      * apply (steps_S nf (f, σ) (f1', σy) (#vf, σf) Hstep Hrunf).
      * exists b. split; [exact Hvf|].
        exists na, w, σa, nb. split; [exact Hruna|split; [exact Hrunb|]].
        lia.
    + (* f is a value and a steps *)
      destruct Ha_step as [a1' [Heq Hstep]]; subst ey.
      destruct v1 as [| | | b | | | | | | | |].
      * exfalso. refine (steps_app_nonlam n _ a1' σy v σ' _ H2).
        intros b' Hc. discriminate Hc.
      * exfalso. refine (steps_app_nonlam n _ a1' σy v σ' _ H2).
        intros b' Hc. discriminate Hc.
      * exfalso. refine (steps_app_nonlam n _ a1' σy v σ' _ H2).
        intros b' Hc. discriminate Hc.
      * (* LamV b *)
        assert (Hf : #(LamV b) = f) by (apply (of_val_to_val f (LamV b) Hval)).
        subst f.
        destruct (steps_app_lam_value_inv n b a1' σy v σ' H2) as
          [na [nb [w [σa [Hruna [Hrunb Htot]]]]]].
        exists 0, (LamV b), σ. split.
        -- apply steps_0.
        -- exists b. split; [reflexivity|].
          exists (S na), w, σa, nb. split.
          { apply (steps_S na (a, σ) (a1', σy) (#w, σa) Hstep Hruna). }
          { split; [exact Hrunb|]. lia. }
      * exfalso. refine (steps_app_nonlam n _ a1' σy v σ' _ H2).
        intros b' Hc. discriminate Hc.
      * exfalso. refine (steps_app_nonlam n _ a1' σy v σ' _ H2).
        intros b' Hc. discriminate Hc.
      * exfalso. refine (steps_app_nonlam n _ a1' σy v σ' _ H2).
        intros b' Hc. discriminate Hc.
      * exfalso. refine (steps_app_nonlam n _ a1' σy v σ' _ H2).
        intros b' Hc. discriminate Hc.
      * exfalso. refine (steps_app_nonlam n _ a1' σy v σ' _ H2).
        intros b' Hc. discriminate Hc.
      * exfalso. refine (steps_app_nonlam n _ a1' σy v σ' _ H2).
        intros b' Hc. discriminate Hc.
      * exfalso. refine (steps_app_nonlam n _ a1' σy v σ' _ H2).
        intros b' Hc. discriminate Hc.
      * exfalso. refine (steps_app_nonlam n _ a1' σy v σ' _ H2).
        intros b' Hc. discriminate Hc.
    + (* beta: f is a lambda and a is already a value *)
      destruct Hbeta as [body [w2 [Hf [Hval2 [Heq Hs']]]]]; subst ey; subst σy.
      subst f. simpl in Hval. injection Hval as Hv1. subst v1.
      assert (Ha : #w2 = a) by (apply (of_val_to_val a w2 Hval2)).
      subst a.
      exists 0, (LamV body), σ. split.
      * apply steps_0.
      * exists body. split; [reflexivity|].
        exists 0, w2, σ, n. split.
        -- apply steps_0.
        -- split; [exact H2|]. lia.
Qed.

Lemma steps_app_lam_combine : forall na nb (b a : expr) (σ : state)
    (w : val) (σa : state) (v : val) (σ' : state),
  steps na (a, σ) (#w, σa) ->
  steps nb (b.[#w/], σa) (#v, σ') ->
  steps (S (na + nb)) (App (Lam b) a, σ) (#v, σ').
Proof.
  induction na as [|na IH]; intros nb b a σ w σa v σ' Harg Hbody.
  - pose proof (steps_0_inv (a, σ) (#w, σa) Harg) as Heq.
    injection Heq as Ha Hσ. subst a. subst σa.
    assert (Hbeta : pstep (App (Lam b) (#w), σ) (b.[#w/], σ)).
    { eapply Ectx_step with (K := []) (e1' := App (Lam b) (#w))
        (e2' := b.[#w/]); simpl; try reflexivity.
      apply (BetaS b (#w) w σ (to_val_of_val w)). }
    simpl. eapply steps_S.
    + exact Hbeta.
    + exact Hbody.
  - inversion Harg as [| n0 x y z Hstep Htail]; subst.
    destruct y as [ay σy]. simpl in *.
    assert (Happ : pstep (App (Lam b) a, σ) (App (Lam b) ay, σy)).
    { change (pstep (fill [AppRCtx (LamV b)] a, σ)
                     (fill [AppRCtx (LamV b)] ay, σy)).
      apply pstep_fill. exact Hstep. }
    specialize (IH nb b ay σy w σa v σ' Htail Hbody).
    simpl. eapply steps_S.
    + exact Happ.
    + exact IH.
Qed.

Lemma fundamental_lam_rule :
  forall Gamma le tau1 tau2 b,
  typed (tau1 :: Gamma) le b tau2 ->
  (forall k rho Delta W d1 d2,
      EnvRel k rho Delta W (tau1 :: Gamma) d1 d2 ->
      EnvRelClosed d1 d2 ->
      E k rho Delta W tau2
        (b.[env_subst_vals d1]) (b.[env_subst_vals d2])) ->
  forall k rho Delta W d1 d2,
    EnvRel k rho Delta W Gamma d1 d2 ->
    EnvRelClosed d1 d2 ->
    closed_state (wst1 W) ->
    closed_state (wst2 W) ->
    E k rho Delta W (TArrow le tau1 tau2 @ LLabel ⊥)
      (Lam (b.[up (env_subst_vals d1)]))
      (Lam (b.[up (env_subst_vals d2)])).
Proof.
  intros Gamma le tau1 tau2 b Hty IHbody k rho Delta W d1 d2 Hrel HCl Hs1 Hs2.
  destruct k as [|k1].
  - apply E_zero.
  - change (E (S k1) rho Delta W (TArrow le tau1 tau2 @ LLabel ⊥)
      (# (LamV (b.[up (env_subst_vals d1)])))
      (# (LamV (b.[up (env_subst_vals d2)])))).
    apply E_value.
    destruct k1 as [|k2].
    + apply V_zero.
    + apply (proj2 (V_arrow_obs k2 rho Delta W (LLabel ⊥) le tau1 tau2
        (b.[up (env_subst_vals d1)]) (b.[up (env_subst_vals d2)])
        (ltac:(simpl; apply order_bot)))).
      intros j Hj a1 a2 Ha1_cl Ha2_cl HEarg.
        destruct j as [|j'].
        -- apply E_zero.
        -- apply E_S_eq.
           intros n1 n2 v1 v2 s1 s2 Hrun1 Hrun2 Hsum.
           destruct (steps_app_lam_value_inv n1 (b.[up (env_subst_vals d1)]) a1
                       (wst1 W) v1 s1 Hrun1)
             as [m1 [m1' [w1 [t1 [Harg1 [Hbody1 Hn1]]]]]].
           destruct (steps_app_lam_value_inv n2 (b.[up (env_subst_vals d2)]) a2
                       (wst2 W) v2 s2 Hrun2)
             as [m2 [m2' [w2 [t2 [Harg2 [Hbody2 Hn2]]]]]].
           assert (Hle_arg : m1 + m2 <= S j') by lia.
           rewrite E_S_eq in HEarg.
           specialize (HEarg m1 m2 w1 w2 t1 t2 Harg1 Harg2 Hle_arg).
           destruct HEarg as [wm1 [Hext1 [HVw HFarg]]].
           (* closedness of argument values *)
           destruct (steps_closed m1 a1 (wst1 W) (#w1) t1 Harg1 Ha1_cl Hs1)
             as [Hclw1_1 Hclstate1].
           destruct (steps_closed m2 a2 (wst2 W) (#w2) t2 Harg2 Ha2_cl Hs2)
             as [Hclw2_1 Hclstate2].
           remember (S j' - m1 - m2 - 1) as r eqn:Hrdef.
           assert (Hrpos : 0 < r) by lia.
           destruct r as [|r'].
           { lia. }
           (* body beta expression equalities *)
           assert (Hb1eq :
             (b.[up (env_subst_vals d1)]).[#w1/] =
             b.[env_subst_vals (w1 .: d1)]).
           { rewrite (up_subst_beta b (env_subst_vals d1) (#w1)).
             - apply (subst_ext b). intro x. destruct x; reflexivity.
             - intros x. unfold env_subst_vals, closed_val. exact (proj1 (HCl x)). }
           assert (Hb2eq :
             (b.[up (env_subst_vals d2)]).[#w2/] =
             b.[env_subst_vals (w2 .: d2)]).
           { rewrite (up_subst_beta b (env_subst_vals d2) (#w2)).
             - apply (subst_ext b). intro x. destruct x; reflexivity.
             - intros x. unfold env_subst_vals, closed_val. exact (proj2 (HCl x)). }
           rewrite Hb1eq in Hbody1.
           rewrite Hb2eq in Hbody2.
           (* environment relation at the intermediate world *)
           set (Warg := (t1, t2, wm1)).
           assert (Hrel_r : EnvRel (S r') rho Delta W Gamma d1 d2).
           { apply (EnvRel_mono (S (S k2)) (S r') rho Delta W Gamma d1 d2).
             - lia.
             - exact Hrel. }
           assert (Hrel_arg : EnvRel (S r') rho Delta Warg Gamma d1 d2).
           { apply (EnvRel_frame (S r') W Warg rho Delta Gamma d1 d2).
             - unfold Warg. exact HFarg.
             - exact Hrel_r. }
           assert (Hrel_body :
             EnvRel (S r') rho Delta Warg (tau1 :: Gamma)
               (w1 .: d1) (w2 .: d2)).
           { apply EnvRel_cons.
             - exact HVw.
             - exact Hrel_arg. }
           assert (HCl_body : EnvRelClosed (w1 .: d1) (w2 .: d2)).
           { apply EnvRelClosed_cons.
             - exact Hclw1_1.
             - exact Hclw2_1.
             - exact HCl. }
           assert (Hbody_run_sum : m1' + m2' <= S r').
           { lia. }
           assert (HbodyE : E (S r') rho Delta Warg tau2
               (b.[env_subst_vals (w1 .: d1)])
               (b.[env_subst_vals (w2 .: d2)])).
           { apply (IHbody (S r') rho Delta Warg (w1 .: d1) (w2 .: d2));
               [exact Hrel_body | exact HCl_body]. }
           destruct (proj1 (E_S_eq r' rho Delta Warg tau2
                       (b.[env_subst_vals (w1 .: d1)])
                       (b.[env_subst_vals (w2 .: d2)])) HbodyE
                       m1' m2' v1 v2 s1 s2 Hbody1 Hbody2 Hbody_run_sum)
             as [wm2 [Hext2 [HVbody HFbody]]].
           exists wm2. split.
           { apply (map_ext_comp W Warg (s1, s2, wm2)); [exact Hext1|exact Hext2]. }
           split.
           { (* value relation at the required lower fuel *)
             assert (Hlev : S j' - n1 - n2 - 1 = S r' - m1' - m2' - 2)
               by lia.
             rewrite Hlev.
             apply (V_mono_n (S r' - m1' - m2' - 1)
                    (S r' - m1' - m2' - 2) rho Delta (s1, s2, wm2)
                    tau2 v1 v2); [lia|exact HVbody]. }
           { (* frame at the required lower fuel *)
             assert (Hlevf : S j' - n1 - n2 - 1 = S r' - m1' - m2' - 2)
               by lia.
             rewrite Hlevf.
             assert (HFa : FrameV (S r' - m1' - m2' - 2) W (t1, t2, wm1)).
             { unfold Warg in HFarg.
               apply FrameV_mono with (r := S r'); [lia|exact HFarg]. }
             assert (HFb : FrameV (S r' - m1' - m2' - 2)
                            (t1, t2, wm1) (s1, s2, wm2)).
             { unfold Warg in HFbody.
               apply FrameV_mono with (r := S r' - m1' - m2' - 1);
                 [lia|exact HFbody]. }
             eapply FrameV_trans; [exact HFa|exact HFb]. }
Qed.


Lemma steps_trans : forall n m (x y z : expr * state),
  steps n x y -> steps m y z -> steps (n + m) x z.
Proof.
  intros n m x y z H1. revert m z.
  induction H1 as [x0 | n0 x0 y0 z0 Hp Hrest IH]; intros m z H2.
  - simpl. exact H2.
  - simpl. eapply steps_S; [exact Hp | apply (IH m z H2)].
Qed.

Lemma rtc_pstep_steps : forall (x y : expr * state),
  rtc pstep x y -> exists n, steps n x y.
Proof.
  intros x y Hr. induction Hr as [z | x0 y0 z Hstep Hrtc IH].
  - exists 0. apply steps_0.
  - destruct IH as [n Hs]. exists (S n).
    eapply steps_S; [exact Hstep | exact Hs].
Qed.

Lemma E_bool_low_extract : forall rho Delta (W : World) l e1 e2
    n1 n2 (v1' v2' : val) (s1 s2 : state),
  interp_label rho l ⊑ ζ ->
  (forall k, E k rho Delta W (TBool @ l) e1 e2) ->
  steps n1 (e1, wst1 W) (#v1', s1) ->
  steps n2 (e2, wst2 W) (#v2', s2) ->
  v1' = v2'.
Proof.
  intros rho Delta W l e1 e2 n1 n2 v1' v2' s1 s2 Hobs HE Hs1 Hs2.
  pose proof (HE (S (S (n1 + n2)))) as HEk.
  rewrite E_S_eq in HEk.
  destruct (HEk n1 n2 v1' v2' s1 s2 Hs1 Hs2 ltac:(lia))
    as [wm [Hext [HV HF]]].
  apply (V_bool_low_eq 0 rho Delta (s1, s2, wm) l v1' v2' Hobs).
  replace (S (S (n1 + n2)) - n1 - n2 - 1) with (S 0) in HV by lia.
  exact HV.
Qed.

Definition dummy_tyrel : TyRel :=
  {| tyrel := fun _ _ _ _ _ => True;
     tyrel_mono := fun k' k Hle l W v1 v2 Hv => Hv;
     tyrel_mono_label := fun l l' Hle k W v1 v2 Hv => Hv |}.

Definition dummy_tenv : tenv := fun _ => dummy_tyrel.

Lemma soundness_tini_from_all_fuel_E :
  forall (e : expr) v1 v2 v1' v2' ℓ ℓ',
  ℓ' ⋢ ζ ->
  ℓ ⊑ ζ ->
  [TBool @ (LLabel ℓ')] # (LLabel ℓ) ⊢ₜ e : TBool @ (LLabel ℓ) ->
  [] # (LLabel ℓ) ⊢ₜ #v1 : TBool @ (LLabel ℓ') ->
  [] # (LLabel ℓ) ⊢ₜ #v2 : TBool @ (LLabel ℓ') ->
  ((∃ σ1, rtc pstep (e.[# v1/], ∅) (# v1', σ1)) /\
   (∃ σ2, rtc pstep (e.[# v2/], ∅) (# v2', σ2))) ->
  (forall k, E k (fun _ => ⊥) dummy_tenv (∅, ∅, fun _ => None)
      (TBool @ LLabel ℓ) (e.[# v1/]) (e.[# v2/])) ->
  v1' = v2'.
Proof.
  intros e v1 v2 v1' v2' ℓ ℓ' Hhigh Hlow Hty Hv1 Hv2 Hruns HEall.
  destruct Hruns as [[σ1 Hr1] [σ2 Hr2]].
  destruct (rtc_pstep_steps _ _ Hr1) as [n1 Hs1].
  destruct (rtc_pstep_steps _ _ Hr2) as [n2 Hs2].
  simpl in Hs1, Hs2.
  eapply (E_bool_low_extract (fun _ => ⊥) dummy_tenv (∅, ∅, fun _ => None)
            (LLabel ℓ) (e.[# v1/]) (e.[# v2/]) n1 n2 v1' v2' σ1 σ2).
  - simpl. exact Hlow.
  - exact HEall.
  - exact Hs1.
  - exact Hs2.
Qed.

Lemma E_bool_low_extract_rtc : forall rho Delta (W : World) l e1 e2
    (v1' v2' : val) (s1 s2 : state),
  interp_label rho l ⊑ ζ ->
  (forall k, E k rho Delta W (TBool @ l) e1 e2) ->
  rtc pstep (e1, wst1 W) (#v1', s1) ->
  rtc pstep (e2, wst2 W) (#v2', s2) ->
  v1' = v2'.
Proof.
  intros rho Delta W l e1 e2 v1' v2' s1 s2 Hobs HE Hr1 Hr2.
  destruct (rtc_pstep_steps _ _ Hr1) as [n1 Hs1].
  destruct (rtc_pstep_steps _ _ Hr2) as [n2 Hs2].
  eapply (E_bool_low_extract rho Delta W l e1 e2 n1 n2 v1' v2' s1 s2);
    eauto.
Qed.

Theorem soundness_tini (e : expr) v1 v2 v1' v2' ℓ ℓ' :
    ℓ' ⋢ ζ →
    ℓ  ⊑ ζ →
    [TBool @ (LLabel ℓ')] # (LLabel ℓ) ⊢ₜ e : TBool @ (LLabel ℓ) →
    [] # (LLabel ℓ) ⊢ₜ #v1 : TBool @ (LLabel ℓ') →
    [] # (LLabel ℓ) ⊢ₜ #v2 : TBool @ (LLabel ℓ') →
    ((∃ σ1, rtc pstep (e.[# v1/], ∅) (# v1', σ1)) ∧
     (∃ σ2, rtc pstep (e.[# v2/], ∅) (# v2', σ2))) →
    v1' = v2'.

End soundness.
