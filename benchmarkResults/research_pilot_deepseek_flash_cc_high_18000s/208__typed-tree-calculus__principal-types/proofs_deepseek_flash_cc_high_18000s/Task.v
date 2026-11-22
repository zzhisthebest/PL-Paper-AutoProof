Require Import String Arith Lia Bool List Nat.

Require Import terms types subtypes derive.

Open Scope string_scope.
Open Scope nat_scope.
Open Scope tree_scope.

Set Default Proof Using "Type".

Create HintDb triage.
Hint Constructors subtype : triage.
Hint Constructors derive : triage.
Hint Constructors program : triage.

(* ------------------------------------------------------------------ *)
(* De Bruijn and subtype infrastructure (self-contained)              *)
(* ------------------------------------------------------------------ *)
Ltac crush_tests :=
  repeat match goal with
  | |- context[if ?c then _ else _] => destruct c
  | |- context[match ?c with left _ => _ | right _ => _ end] => destruct c
  | |- context[match compare ?a ?b with _ => _ end] => destruct (compare a b) as [[?|?]|?]
  end;
  try reflexivity; try (f_equal; lia); lia.

(* 1. relocate under two lifts *)
Lemma relocate_lift_gen : forall ii bb kk jj nn,
  bb <= jj -> jj <= bb + kk ->
  relocate (relocate ii bb kk) jj nn = relocate ii bb (kk+nn).
Proof. intros. unfold relocate. crush_tests. Qed.

(* 2. lift; lift with same cutoff *)
Lemma lift_rec_lift_rec_gen : forall ww bb kk jj nn,
  bb <= jj -> jj <= bb + kk ->
  lift_rec (lift_rec ww bb kk) jj nn = lift_rec ww bb (kk+nn).
Proof.
  induction ww; intros bb kk jj nn Hbj HbK; simpl.
  - f_equal. apply relocate_lift_gen; assumption.
  - f_equal. apply (IHww (S bb) kk (S jj) nn); lia.
  - f_equal; [ apply (IHww1 bb kk jj nn); assumption | apply (IHww2 bb kk jj nn); assumption ].
  - reflexivity.
  - f_equal. apply (IHww bb kk jj nn); assumption.
  - f_equal; [ apply (IHww1 bb kk jj nn); assumption | apply (IHww2 bb kk jj nn); assumption ].
  - f_equal. apply (IHww bb kk jj nn); assumption.
Qed.

Lemma lift_rec_lift_rec_0 : forall ww kk nn,
  lift_rec (lift_rec ww 0 kk) 0 nn = lift_rec ww 0 (kk+nn).
Proof. intros. apply lift_rec_lift_rec_gen; lia. Qed.

(* 3. lift by zero *)
Lemma lift_rec_zero : forall ww kk, lift_rec ww kk 0 = ww.
Proof.
  induction ww; intros kk; simpl.
  - unfold relocate. destruct (test kk n); reflexivity.
  - f_equal. apply IHww.
  - f_equal; [apply IHww1 | apply IHww2].
  - reflexivity.
  - f_equal. apply IHww.
  - f_equal; [apply IHww1 | apply IHww2].
  - f_equal. apply IHww.
Qed.

Lemma lift_zero : forall ww, lift 0 ww = ww.
Proof. intros. unfold lift. apply lift_rec_zero. Qed.

(* 4. insert under a lift *)
Lemma insert_lift_gen : forall ww ii jj kk nn,
  jj <= kk ->
  insert_Var ww (relocate ii jj nn) (kk+nn) =
  lift_rec (insert_Var ww ii kk) jj nn.
Proof.
  intros ww ii jj kk nn Hjk.
  unfold insert_Var, relocate.
  repeat match goal with
  | |- context[if ?c then _ else _] => destruct c
  | |- context[match ?c with left _ => _ | right _ => _ end] => destruct c
  | |- context[match compare ?a ?b with _ => _ end] => destruct (compare a b) as [[?|?]|?]
  end.
  all: try reflexivity.
  all: try (unfold lift; symmetry; apply lift_rec_lift_rec_gen; lia).
  all: try (rewrite !lift_zero; reflexivity).
  all: cbn [lift_rec]; unfold relocate; crush_tests.
Qed.

(* 5. generalized insert under lift (needed for lift-subst) *)
Lemma lift_lift_subst_gen : forall XX bb jj kk nn,
  jj <= kk ->
  lift_rec (lift_rec XX bb jj) (bb+kk) nn =
  lift_rec (lift_rec XX (bb+kk-jj) nn) bb jj.
Proof.
  induction XX; intros bb jj kk nn Hjk; simpl.
  - unfold relocate. crush_tests.
  - f_equal.
    replace (S (bb + kk)) with (S bb + kk) by lia.
    replace (S (bb + kk - jj)) with (S bb + kk - jj) by lia.
    apply (IHXX (S bb) jj kk nn); assumption.
  - f_equal; [ apply (IHXX1 bb jj kk nn); assumption | apply (IHXX2 bb jj kk nn); assumption ].
  - reflexivity.
  - f_equal. apply (IHXX bb jj kk nn); assumption.
  - f_equal; [ apply (IHXX1 bb jj kk nn); assumption | apply (IHXX2 bb jj kk nn); assumption ].
  - f_equal. apply (IHXX bb jj kk nn); assumption.
Qed.

Lemma lift_insert_gen : forall uu ii jj kk nn,
  jj <= kk ->
  lift_rec (insert_Var uu ii jj) kk nn =
  insert_Var (lift_rec uu (kk-jj) nn) (relocate ii (S kk) nn) jj.
Proof.
  intros uu ii jj kk nn Hjk.
  unfold insert_Var, relocate.
  repeat match goal with
  | |- context[if ?c then _ else _] => destruct c
  | |- context[match ?c with left _ => _ | right _ => _ end] => destruct c
  | |- context[match compare ?a ?b with _ => _ end] => destruct (compare a b) as [[?|?]|?]
  end.
  all: try reflexivity.
  all: try (rewrite !lift_zero; reflexivity).
  all: try (rewrite (lift_rec_zero uu 0); rewrite (lift_rec_zero (lift_rec uu (kk-jj) nn) 0); reflexivity).
  all: try (unfold lift; cbn [lift_rec relocate]; crush_tests).
  all: try (cbn [lift_rec]; unfold relocate; crush_tests).
  all: try (unfold lift; exact (lift_lift_subst_gen uu 0 jj kk nn Hjk)).
Qed.

(* 6. B_gen: substitution into a lifted term *)
Lemma subst_lift_gen : forall XX ww jj kk nn,
  jj <= kk ->
  subst_rec (lift_rec XX jj nn) ww (kk+nn) =
  lift_rec (subst_rec XX ww kk) jj nn.
Proof.
  induction XX; intros ww jj kk nn Hjk; simpl.
  - apply insert_lift_gen; assumption.
  - f_equal. apply (IHXX ww (S jj) (S kk) nn); lia.
  - f_equal; [ apply (IHXX1 ww jj kk nn); assumption | apply (IHXX2 ww jj kk nn); assumption ].
  - reflexivity.
  - f_equal. apply (IHXX ww jj kk nn); assumption.
  - f_equal; [ apply (IHXX1 ww jj kk nn); assumption | apply (IHXX2 ww jj kk nn); assumption ].
  - f_equal. apply (IHXX ww jj kk nn); assumption.
Qed.

(* 7. C_gen: swapping two lifts *)
Lemma lift_lift_gen : forall XX jj kk mm nn,
  jj <= kk ->
  lift_rec (lift_rec XX jj mm) (kk+mm) nn =
  lift_rec (lift_rec XX kk nn) jj mm.
Proof.
  induction XX; intros jj kk mm nn Hjk; simpl.
  - unfold relocate. crush_tests.
  - f_equal. apply (IHXX (S jj) (S kk) mm nn); lia.
  - f_equal; [ apply (IHXX1 jj kk mm nn); assumption | apply (IHXX2 jj kk mm nn); assumption ].
  - reflexivity.
  - f_equal. apply (IHXX jj kk mm nn); assumption.
  - f_equal; [ apply (IHXX1 jj kk mm nn); assumption | apply (IHXX2 jj kk mm nn); assumption ].
  - f_equal. apply (IHXX jj kk mm nn); assumption.
Qed.

(* 8. J: generalized lift of a substitution *)
Lemma lift_subst_gen : forall XX uu jj kk nn,
  jj <= kk ->
  lift_rec (subst_rec XX uu jj) kk nn =
  subst_rec (lift_rec XX (S kk) nn) (lift_rec uu (kk-jj) nn) jj.
Proof.
  induction XX; intros uu jj kk nn Hjk; simpl.
  - apply lift_insert_gen; assumption.
  - f_equal.
    replace ((S kk) - (S jj)) with (kk - jj) by lia.
    apply (IHXX uu (S jj) (S kk) nn); lia.
  - f_equal; [ apply (IHXX1 uu jj kk nn); assumption | apply (IHXX2 uu jj kk nn); assumption ].
  - reflexivity.
  - f_equal. apply (IHXX uu jj kk nn); assumption.
  - f_equal; [ apply (IHXX1 uu jj kk nn); assumption | apply (IHXX2 uu jj kk nn); assumption ].
  - f_equal. apply (IHXX uu jj kk nn); assumption.
Qed.

(* 9. substitution into a lift, below the lifted region *)
Lemma subst_lift_low : forall XX NN bb jj cc,
  bb <= jj -> jj < bb + cc ->
  subst_rec (lift_rec XX bb cc) NN jj = lift_rec XX bb (cc-1).
Proof.
  induction XX; intros NN bb jj cc Hbj HbC; simpl.
  - (* Var *) simpl. unfold relocate, insert_Var. crush_tests.
  - (* Quant *) f_equal. apply (IHXX NN (S bb) (S jj) cc); lia.
  - f_equal; [ apply (IHXX1 NN bb jj cc); assumption | apply (IHXX2 NN bb jj cc); assumption ].
  - reflexivity.
  - f_equal. apply (IHXX NN bb jj cc); assumption.
  - f_equal; [ apply (IHXX1 NN bb jj cc); assumption | apply (IHXX2 NN bb jj cc); assumption ].
  - f_equal. apply (IHXX NN bb jj cc); assumption.
Qed.

Lemma insert_Var_same : forall NN ii, insert_Var NN ii ii = lift ii NN.
Proof.
  intros NN ii. unfold insert_Var.
  destruct (compare ii ii) as [[h|h]|h]; try (exfalso; lia); reflexivity.
Qed.

Lemma insert_subst_gen : forall uu ww ii jj kk,
  jj <= kk ->
  subst_rec (insert_Var uu ii jj) ww kk =
  subst_rec (insert_Var ww ii (S kk)) (subst_rec uu ww (kk-jj)) jj.
Proof.
  intros uu ww ii jj kk Hjk.
  unfold insert_Var.
  repeat match goal with
  | |- context[if ?c then _ else _] => destruct c
  | |- context[match ?c with left _ => _ | right _ => _ end] => destruct c
  | |- context[match compare ?a ?b with _ => _ end] => destruct (compare a b) as [[?|?]|?]
  end.
  all: try reflexivity.
  all: try (subst ii; simpl; rewrite insert_Var_same; unfold lift;
            rewrite (subst_lift_low ww (subst_rec uu ww (kk-jj)) 0 jj (S kk)); [|lia|lia];
            replace (S kk - 1) with kk by lia; reflexivity).
  all: try (subst ii; simpl; rewrite insert_Var_same; unfold lift;
            replace kk with ((kk-jj)+jj) by lia;
            replace (((kk-jj)+jj)-jj) with (kk-jj) by lia;
            apply subst_lift_gen; lia).
  all: try (simpl; unfold insert_Var, relocate; crush_tests).
Qed.

Lemma subst_subst_gen : forall XX uu ww jj kk,
  jj <= kk ->
  subst_rec (subst_rec XX uu jj) ww kk =
  subst_rec (subst_rec XX ww (S kk)) (subst_rec uu ww (kk-jj)) jj.
Proof.
  induction XX; intros uu ww jj kk Hjk; simpl.
  - apply insert_subst_gen; assumption.
  - f_equal.
    replace ((S kk) - (S jj)) with (kk - jj) by lia.
    apply (IHXX uu ww (S jj) (S kk)); lia.
  - f_equal; [ apply (IHXX1 uu ww jj kk); assumption | apply (IHXX2 uu ww jj kk); assumption ].
  - reflexivity.
  - f_equal. apply (IHXX uu ww jj kk); assumption.
  - f_equal; [ apply (IHXX1 uu ww jj kk); assumption | apply (IHXX2 uu ww jj kk); assumption ].
  - f_equal. apply (IHXX uu ww jj kk); assumption.
Qed.

(* variant preservation infrastructure *)

Lemma variant_lift_rec_true : forall uu pos lev cut ee,
  lev < cut -> variant pos (lev+ee) (lift_rec uu ee cut) = true.
Proof.
  induction uu as [ n | uu IH | uu1 IH1 uu2 IH2 | | uu IH | uu1 IH1 uu2 IH2 | uu IH ];
    intros pos lev cut ee Hlt; simpl.
  - (* Var *) unfold relocate.
    destruct (test ee n) as [h|h].
    + destruct (lev+ee =? cut+n) eqn:E; [|reflexivity].
      apply Nat.eqb_eq in E. exfalso; lia.
    + destruct (lev+ee =? n) eqn:E; [|reflexivity].
      apply Nat.eqb_eq in E. exfalso; lia.
  - (* Quant *) replace (S (lev+ee)) with (lev + S ee) by lia.
    apply (IH pos lev cut (S ee)); lia.
  - (* Funty *) apply andb_true_intro; split.
    + apply (IH1 (negb pos) lev cut ee); assumption.
    + apply (IH2 pos lev cut ee); assumption.
  - reflexivity.
  - apply IH; assumption.
  - apply andb_true_intro; split.
    + apply (IH1 pos lev cut ee); assumption.
    + apply (IH2 pos lev cut ee); assumption.
  - apply IH; assumption.
Qed.

Lemma variant_lift_rec_pres : forall uu pos lev ee cut,
  lev < ee -> variant pos lev uu = true ->
  variant pos lev (lift_rec uu ee cut) = true.
Proof.
  induction uu as [ n | uu IH | uu1 IH1 uu2 IH2 | | uu IH | uu1 IH1 uu2 IH2 | uu IH ];
    intros pos lev ee cut Hlt Hv; simpl in *.
  - (* Var *) unfold relocate.
    destruct (test ee n) as [h|h].
    + (* ee <= n : index n+cut; lev<> n+cut *)
      destruct (lev =? (cut+n)) eqn:E; [|reflexivity].
      apply Nat.eqb_eq in E. exfalso; lia.
    + exact Hv.
  - (* Quant *) apply (IH pos (S lev) (S ee) cut); [lia | assumption].
  - (* Funty *) apply andb_true_iff in Hv. destruct Hv as [H1 H2].
    apply andb_true_intro; split.
    + apply (IH1 (negb pos) lev ee cut); assumption.
    + apply (IH2 pos lev ee cut); assumption.
  - reflexivity.
  - apply IH; assumption.
  - apply andb_true_iff in Hv. destruct Hv as [H1 H2].
    apply andb_true_intro; split.
    + apply (IH1 pos lev ee cut); assumption.
    + apply (IH2 pos lev ee cut); assumption.
  - apply IH; assumption.
Qed.

Lemma variant_subst_rec : forall ty pos lev uu cc,
  lev < cc -> variant pos lev ty = true ->
  variant pos lev (subst_rec ty uu cc) = true.
Proof.
  induction ty as [ n | ty IH | ty1 IH1 ty2 IH2 | | ty IH | ty1 IH1 ty2 IH2 | ty IH ];
    intros pos lev uu cc Hlt Hv; simpl in *.
  - (* Var *) unfold insert_Var.
    destruct (compare cc n) as [[hlt|heq]|hgt].
    + (* cc < n *) simpl.
      destruct (lev =? Nat.pred n) eqn:E; [|reflexivity].
      apply Nat.eqb_eq in E. exfalso; lia.
    + (* cc = n *) subst n.
      (* goal: variant pos lev (lift cc uu) = true; unfold lift *)
      unfold lift.
      assert (H := variant_lift_rec_true uu pos lev cc 0 ltac:(lia)).
      replace (lev + 0) with lev in H by lia.
      exact H.
    + exact Hv.
  - (* Quant *) apply (IH pos (S lev) uu (S cc)); [lia | assumption].
  - (* Funty *) apply andb_true_iff in Hv. destruct Hv as [H1 H2].
    apply andb_true_intro; split.
    + apply (IH1 (negb pos) lev uu cc); assumption.
    + apply (IH2 pos lev uu cc); assumption.
  - reflexivity.
  - apply IH; assumption.
  - apply andb_true_iff in Hv. destruct Hv as [H1 H2].
    apply andb_true_intro; split.
    + apply (IH1 pos lev uu cc); assumption.
    + apply (IH2 pos lev uu cc); assumption.
  - apply IH; assumption.
Qed.

Lemma covariant_subst_S : forall ty uu kk,
  covariant ty -> covariant (subst_rec ty uu (S kk)).
Proof.
  intros ty uu kk H. unfold covariant in *.
  apply (variant_subst_rec ty true 0 uu (S kk)); [lia | assumption].
Qed.

Lemma covariant_lift_S : forall ty kk mm,
  covariant ty -> covariant (lift_rec ty (S kk) mm).
Proof.
  intros ty kk mm H. unfold covariant in *.
  apply (variant_lift_rec_pres ty true 0 (S kk) mm); [lia | assumption].
Qed.

Definition tree_src (ty : dtype) : dtype :=
  Fork
    (Fork (subst ty Leaf)
          (quant 1 (Funty (Var 0) (subst (lift_rec ty 1 1) (Stem (Var 0))))))
    (quant 2
       (Funty (Var 1)
              (Funty (Var 0) (subst (lift_rec ty 1 2) (Fork (Var 1) (Var 0)))))).

Lemma insert_Var_lt : forall uu ii cc, ii < cc -> insert_Var uu ii cc = Var ii.
Proof.
  intros uu ii cc H. unfold insert_Var.
  destruct (compare cc ii) as [[h|h]|h]; try (exfalso; lia); reflexivity.
Qed.

Lemma tree_src_subst : forall ty uu kk,
  subst_rec (tree_src ty) uu kk = tree_src (subst_rec ty uu (S kk)).
Proof.
  intros ty uu kk. unfold tree_src. simpl.
  repeat rewrite insert_Var_lt by lia.
  unfold subst.
  rewrite (subst_subst_gen ty Leaf uu 0 kk); [|lia].
  replace (kk-0) with kk by lia.
  rewrite (subst_subst_gen (lift_rec ty 1 1) (Stem (Var 0)) uu 0 (S kk)); [|lia].
  replace ((S kk)-0) with (S kk) by lia.
  rewrite (subst_subst_gen (lift_rec ty 1 2) (Fork (Var 1) (Var 0)) uu 0 (S (S kk))); [|lia].
  replace ((S (S kk))-0) with (S (S kk)) by lia.
  assert (H2 : subst_rec (lift_rec ty 1 1) uu (S (S kk)) =
               lift_rec (subst_rec ty uu (S kk)) 1 1).
  { replace (S (S kk)) with ((S kk)+1) by lia.
    apply (subst_lift_gen ty uu 1 (S kk) 1); lia. }
  rewrite H2.
  assert (H3 : subst_rec (lift_rec ty 1 2) uu (S (S (S kk))) =
               lift_rec (subst_rec ty uu (S kk)) 1 2).
  { replace (S (S (S kk))) with ((S kk)+2) by lia.
    apply (subst_lift_gen ty uu 1 (S kk) 2); lia. }
  rewrite H3.
  simpl.
  repeat rewrite insert_Var_lt by lia.
  reflexivity.
Qed.

Lemma tree_src_lift : forall ty kk mm,
  lift_rec (tree_src ty) kk mm = tree_src (lift_rec ty (S kk) mm).
Proof.
  intros ty kk mm. unfold tree_src. simpl.
  unfold subst.
  rewrite (lift_subst_gen ty Leaf 0 kk mm); [|lia].
  replace (kk-0) with kk by lia.
  rewrite (lift_subst_gen (lift_rec ty 1 1) (Stem (Var 0)) 0 (S kk) mm); [|lia].
  replace ((S kk)-0) with (S kk) by lia.
  rewrite (lift_subst_gen (lift_rec ty 1 2) (Fork (Var 1) (Var 0)) 0 (S (S kk)) mm); [|lia].
  replace ((S (S kk))-0) with (S (S kk)) by lia.
  assert (H2 : lift_rec (lift_rec ty 1 1) (S (S kk)) mm =
               lift_rec (lift_rec ty (S kk) mm) 1 1).
  { replace (S (S kk)) with ((S kk)+1) by lia.
    apply (lift_lift_gen ty 1 (S kk) 1 mm); lia. }
  rewrite H2.
  assert (H3 : lift_rec (lift_rec ty 1 2) (S (S (S kk))) mm =
               lift_rec (lift_rec ty (S kk) mm) 1 2).
  { replace (S (S (S kk))) with ((S kk)+2) by lia.
    apply (lift_lift_gen ty 1 (S kk) 2 mm); lia. }
  rewrite H3.
  simpl.
  reflexivity.
Qed.

Lemma quant_subst_rec : forall nn ty uu kk,
  subst_rec (quant nn ty) uu kk = quant nn (subst_rec ty uu (nn+kk)).
Proof.
  induction nn; intros ty uu kk; simpl.
  - reflexivity.
  - simpl. rewrite (IHnn (Quant ty) uu kk). simpl. reflexivity.
Qed.

Lemma quant_lift_rec : forall nn ty kk mm,
  lift_rec (quant nn ty) kk mm = quant nn (lift_rec ty (nn+kk) mm).
Proof.
  induction nn; intros ty kk mm; simpl.
  - reflexivity.
  - simpl. rewrite (IHnn (Quant ty) kk mm). simpl. reflexivity.
Qed.

Lemma omega2_subst : forall uu kk, subst_rec omega2_ty uu kk = omega2_ty.
Proof. intros. reflexivity. Qed.

Lemma omega2_lift : forall kk mm, lift_rec omega2_ty kk mm = omega2_ty.
Proof. intros. reflexivity. Qed.

Lemma subtype_subst_rec : forall XX YY, subtype XX YY ->
  forall uu kk, subtype (subst_rec XX uu kk) (subst_rec YY uu kk).
Proof.
  intros XX YY H.
  induction H as
  [ ty
  | ty1 ty2 ty3 h1 IH1 h2 IH2
  | uty1 uty2 h IH
  | uty1 uty2 vty1 vty2 h1 IH1 h2 IH2
  | uty1 uty2 h IH
  | uty1 uty2 vty1 vty2 h1 IH1 h2 IH2
  | vty1 vty2 h IH
  | uty
  | uty vty
  | uty
  | uty vty
  | ty u0
  | ty
  | uty
  | uty vty
  | uty vty
  | uty vty wty
  | uty vty wty
  | uty vty1 vty2 wty
  | uty vty wty1 wty2 wty3
  | kR uty vty
  | ty uty Hcov
  | ty
  | uty vty
  | uty vty
  | uty vty wty
  ]; intros uu kk; simpl.
  - apply sub_zero.
  - eapply sub_trans; [ apply (IH1 uu kk) | apply (IH2 uu kk) ].
  - apply sub_stem. apply (IH uu kk).
  - apply sub_fork; [ apply (IH1 uu kk) | apply (IH2 uu kk) ].
  - apply sub_asf. apply (IH uu kk).
  - apply sub_funty; [ apply (IH1 uu kk) | apply (IH2 uu kk) ].
  - apply sub_quant. apply (IH uu (S kk)).
  - apply sub_quant_stem.
  - apply sub_quant_fork.
  - apply sub_quant_asf.
  - apply sub_dist.
  - eapply sub_trans with (subst_rec (subst_rec ty uu (S kk)) (subst_rec u0 uu (kk - 0)) 0).
    + apply (sub_inst (subst_rec ty uu (S kk)) (subst_rec u0 uu (kk - 0))).
    + unfold subst.
      rewrite (subst_subst_gen ty u0 uu 0 kk); [ apply sub_zero | lia ].
  - eapply sub_trans with (Quant (lift 1 (subst_rec ty uu kk))).
    + apply sub_lift.
    + apply sub_quant.
      unfold lift.
      assert (Heq : lift_rec (subst_rec ty uu kk) 0 1 =
                    subst_rec (lift_rec ty 0 1) uu (S kk)).
      { replace (S kk) with (kk + 1) by lia.
        symmetry. apply (subst_lift_gen ty uu 0 kk 1); lia. }
      rewrite Heq. apply sub_zero.
  - apply sub_leaf_fun.
  - apply sub_stem_fun.
  - apply sub_fork_leaf.
  - apply sub_fork_stem.
  - apply sub_fork_fork_leaf.
  - apply sub_fork_fork_stem.
  - apply sub_fork_fork_fork.
  - (* recursion *)
    try rewrite omega2_subst.
    rewrite !quant_subst_rec.
    simpl.
    apply sub_recursion.
  - (* tree *)
    change (subtype (subst_rec (tree_src ty) uu kk)
                    (subst_rec (Funty uty (subst ty uty)) uu kk)).
    rewrite tree_src_subst.
    unfold subst. simpl.
    rewrite (subst_subst_gen ty uty uu 0 kk); [|lia].
    replace (kk-0) with kk by lia.
    apply sub_tree.
    apply covariant_subst_S. assumption.
  - apply sub_to_asf.
  - apply sub_from_asf.
  - apply sub_bffs.
  - apply sub_bfff.
Qed.

Lemma subtype_lift_rec : forall XX YY, subtype XX YY ->
  forall kk mm, subtype (lift_rec XX kk mm) (lift_rec YY kk mm).
Proof.
  intros XX YY H.
  induction H as
  [ ty
  | ty1 ty2 ty3 h1 IH1 h2 IH2
  | uty1 uty2 h IH
  | uty1 uty2 vty1 vty2 h1 IH1 h2 IH2
  | uty1 uty2 h IH
  | uty1 uty2 vty1 vty2 h1 IH1 h2 IH2
  | vty1 vty2 h IH
  | uty
  | uty vty
  | uty
  | uty vty
  | ty u0
  | ty
  | uty
  | uty vty
  | uty vty
  | uty vty wty
  | uty vty wty
  | uty vty1 vty2 wty
  | uty vty wty1 wty2 wty3
  | kR uty vty
  | ty uty Hcov
  | ty
  | uty vty
  | uty vty
  | uty vty wty
  ]; intros kk mm; simpl.
  - apply sub_zero.
  - eapply sub_trans; [ apply (IH1 kk mm) | apply (IH2 kk mm) ].
  - apply sub_stem. apply (IH kk mm).
  - apply sub_fork; [ apply (IH1 kk mm) | apply (IH2 kk mm) ].
  - apply sub_asf. apply (IH kk mm).
  - apply sub_funty; [ apply (IH1 kk mm) | apply (IH2 kk mm) ].
  - apply sub_quant. apply (IH (S kk) mm).
  - apply sub_quant_stem.
  - apply sub_quant_fork.
  - apply sub_quant_asf.
  - apply sub_dist.
  - (* sub_inst *)
    eapply sub_trans with (subst_rec (lift_rec ty (S kk) mm) (lift_rec u0 (kk - 0) mm) 0).
    + apply sub_inst.
    + unfold subst. simpl.
      rewrite (lift_subst_gen ty u0 0 kk mm); [ apply sub_zero | lia ].
  - (* sub_lift *)
    eapply sub_trans with (Quant (lift 1 (lift_rec ty kk mm))).
    + apply sub_lift.
    + apply sub_quant.
      unfold lift.
      assert (Heq : lift_rec (lift_rec ty kk mm) 0 1 =
                    lift_rec (lift_rec ty 0 1) (S kk) mm).
      { replace (S kk) with (kk+1) by lia.
        symmetry. apply (lift_lift_gen ty 0 kk 1 mm); lia. }
      rewrite Heq. apply sub_zero.
  - apply sub_leaf_fun.
  - apply sub_stem_fun.
  - apply sub_fork_leaf.
  - apply sub_fork_stem.
  - apply sub_fork_fork_leaf.
  - apply sub_fork_fork_stem.
  - apply sub_fork_fork_fork.
  - (* recursion *)
    try rewrite omega2_lift.
    rewrite !quant_lift_rec.
    simpl.
    apply sub_recursion.
  - (* tree *)
    change (subtype (lift_rec (tree_src ty) kk mm)
                    (lift_rec (Funty uty (subst ty uty)) kk mm)).
    rewrite tree_src_lift.
    unfold subst. simpl.
    rewrite (lift_subst_gen ty uty 0 kk mm); [|lia].
    replace (kk-0) with kk by lia.
    apply sub_tree.
    apply covariant_lift_S. assumption.
  - apply sub_to_asf.
  - apply sub_from_asf.
  - apply sub_bffs.
  - apply sub_bfff.
Qed.

(* ---------- verified de Bruijn identities from exp7 ---------- *)
Lemma insert_relocate_k : forall u i k, insert_Var u (relocate i k 1) k = Var i.
Proof.
  intros. unfold insert_Var, relocate.
  destruct (test k i) as [h|h].
  - destruct (compare k (1+i)) as [[hlt|heq]|hgt]; cbn.
    + reflexivity.
    + exfalso. lia.
    + exfalso. lia.
  - destruct (compare k i) as [[hlt|heq]|hgt]; cbn.
    + exfalso. lia.
    + exfalso. lia.
    + reflexivity.
Qed.

Lemma insert_relocate_Sk : forall i k, insert_Var (Var 0) (relocate i (S k) 1) k = Var i.
Proof.
  intros. unfold insert_Var, relocate.
  destruct (test (S k) i) as [h|h].
  - destruct (compare k (1+i)) as [[hlt|heq]|hgt]; cbn.
    + reflexivity.
    + exfalso. lia.
    + exfalso. lia.
  - destruct (compare k i) as [[hlt|heq]|hgt]; cbn.
    + exfalso. lia.
    + subst. cbn. f_equal. lia.
    + reflexivity.
Qed.

Lemma subst_lift_rec : forall X k u, subst_rec (lift_rec X k 1) u k = X.
Proof.
  induction X; intros k u; simpl.
  - apply insert_relocate_k.
  - f_equal. apply IHX.
  - f_equal; [apply IHX1 | apply IHX2].
  - reflexivity.
  - f_equal. apply IHX.
  - f_equal; [apply IHX1 | apply IHX2].
  - f_equal. apply IHX.
Qed.

Lemma subst_lift_rec_S : forall X k, subst_rec (lift_rec X (S k) 1) (Var 0) k = X.
Proof.
  induction X; intros k; simpl.
  - apply insert_relocate_Sk.
  - f_equal. apply IHX.
  - f_equal; [apply IHX1 | apply IHX2].
  - reflexivity.
  - f_equal. apply IHX.
  - f_equal; [apply IHX1 | apply IHX2].
  - f_equal. apply IHX.
Qed.

Lemma subst_lift1 : forall X u, subst (lift 1 X) u = X.
Proof. intros. unfold subst, lift. apply subst_lift_rec. Qed.

Lemma subst_lift_rec11 : forall X, subst (lift_rec X 1 1) (Var 0) = X.
Proof. intros. unfold subst. apply subst_lift_rec_S. Qed.

Lemma quant_stem_comm : forall u, subtype (Stem (Quant u)) (Quant (Stem u)).
Proof.
  intros u. eapply sub_trans.
  - apply sub_lift.
  - change (subtype (Quant (Stem (Quant (lift_rec u 1 1)))) (Quant (Stem u))).
    apply sub_quant, sub_stem. eapply sub_trans.
    + apply (sub_inst (lift_rec u 1 1) (Var 0)).
    + rewrite subst_lift_rec11. apply sub_zero.
Qed.

Lemma fork_quant_comm : forall A a, subtype (Fork A (Quant a)) (Quant (Fork (lift 1 A) a)).
Proof.
  intros A a. eapply sub_trans.
  - apply sub_lift.
  - change (subtype (Quant (Fork (lift 1 A) (Quant (lift_rec a 1 1))))
                    (Quant (Fork (lift 1 A) a))).
    apply sub_quant, sub_fork.
    + apply sub_zero.
    + eapply sub_trans.
      * apply (sub_inst (lift_rec a 1 1) (Var 0)).
      * rewrite subst_lift_rec11. apply sub_zero.
Qed.

Lemma stem_quant_lift : forall a b, subtype (Stem a) b ->
                                   subtype (Stem (Quant a)) (Quant b).
Proof.
  intros a b H. eapply sub_trans.
  - apply quant_stem_comm.
  - apply sub_quant, H.
Qed.

Lemma fork_quant_lift : forall A a b, subtype (Fork (lift 1 A) a) b ->
                                      subtype (Fork A (Quant a)) (Quant b).
Proof.
  intros A a b H. eapply sub_trans.
  - apply fork_quant_comm.
  - apply sub_quant, H.
Qed.

(* ------------------------------------------------------------------ *)
(* D1 and D2 certificates                                             *)
(* ------------------------------------------------------------------ *)

(* ------------------------------------------------------------------ *)
(* D1 certificate                                                      *)
(* ------------------------------------------------------------------ *)

Fixpoint Good (S : dtype) : Prop :=
  match S with
  | Leaf => True
  | Funty a b => subtype (Stem a) b
  | Quant Z => Good Z
  | Asf Z => Good Z
  | Stem _ => False
  | Fork _ _ => False
  | Var _ => False
  end.

Lemma Good_stable :
  (forall S k n, Good S -> Good (lift_rec S k n)) ->
  (forall S w k, Good S -> Good (subst_rec S w k)) ->
  forall S T, Good S -> subtype S T -> Good T.
Proof.
  intros Hlift Hsubst S T H d. induction d; simpl in *.
  - (* sub_zero *) exact H.
  - (* sub_trans *) apply IHd2. apply IHd1. exact H.
  - (* sub_stem *) exact H.
  - (* sub_fork *) exact H.
  - (* sub_asf *) apply IHd. exact H.
  - (* sub_funty *) eapply sub_trans; [ | exact d2 ].
    eapply sub_trans; [ | exact H ].
    apply sub_stem. exact d1.
  - (* sub_quant *) apply IHd. exact H.
  - (* sub_quant_stem *) exact H.
  - (* sub_quant_fork *) exact H.
  - (* sub_quant_asf *) exact H.
  - (* sub_dist *) apply stem_quant_lift. exact H.
  - (* sub_inst *) unfold subst. apply Hsubst. exact H.
  - (* sub_lift *) unfold lift. apply Hlift. exact H.
  - (* sub_leaf_fun *) apply sub_zero.
  - (* sub_stem_fun *) exfalso. exact H.
  - (* sub_fork_leaf *) exfalso. exact H.
  - (* sub_fork_stem *) exfalso. exact H.
  - (* sub_fork_fork_leaf *) exfalso. exact H.
  - (* sub_fork_fork_stem *) exfalso. exact H.
  - (* sub_fork_fork_fork *) exfalso. exact H.
  - (* sub_recursion *) exfalso. exact H.
  - (* sub_tree *) exfalso. exact H.
  - (* sub_to_asf *) exact H.
  - (* sub_from_asf *) exact H.
  - (* sub_bffs *) exfalso. exact H.
  - (* sub_bfff *) exfalso. exact H.
Qed.

Lemma Good_lift : forall S k n, Good S -> Good (lift_rec S k n).
Proof.
  induction S as [ m | S1 IH | a IHa b IHb | | B IH | A1 IHA1 B1 IHB1 | Z IH ];
    intros k n H; simpl in *.
  - exact H.
  - apply IH. exact H.
  - exact (subtype_lift_rec (Stem a) b H k n).
  - exact Logic.I.
  - exact H.
  - exact H.
  - apply IH. exact H.
Qed.

Lemma Good_subst : forall S w k, Good S -> Good (subst_rec S w k).
Proof.
  induction S as [ m | S1 IH | a IHa b IHb | | B IH | A1 IHA1 B1 IHB1 | Z IH ];
    intros w k H; simpl in *.
  - exfalso. exact H.
  - apply IH. exact H.
  - exact (subtype_subst_rec (Stem a) b H w k).
  - exact Logic.I.
  - exact H.
  - exact H.
  - apply IH. exact H.
Qed.

Lemma D1_unconditional :
  forall u ty, subtype Leaf (Funty u ty) -> subtype (Stem u) ty.
Proof.
  intros u ty d.
  exact (Good_stable Good_lift Good_subst Leaf (Funty u ty) Logic.I d).
Qed.

(* ------------------------------------------------------------------ *)
(* D2 certificate (head shifted by lift 1 under Quant binders)         *)
(* ------------------------------------------------------------------ *)

Fixpoint Good2 (A S : dtype) : Prop :=
  match S with
  | Leaf => False
  | Funty a b => subtype (Fork A a) b
  | Quant Z => Good2 (lift 1 A) Z
  | Asf Z => Good2 A Z
  | Stem B => subtype A B
  | Fork _ _ => False
  | Var _ => False
  end.

Lemma Good2_stable :
  (forall (A S : dtype) (k n : nat),
      Good2 A S -> Good2 (lift_rec A k n) (lift_rec S k n)) ->
  (forall (A S w : dtype) (k : nat),
      Good2 A S -> Good2 (subst_rec A w k) (subst_rec S w k)) ->
  forall S T, subtype S T -> forall A, Good2 A S -> Good2 A T.
Proof.
  intros Hlift Hsubst S T d. induction d; intros A HG; simpl in *.
  - (* sub_zero *) exact HG.
  - (* sub_trans *) apply IHd2, IHd1, HG.
  - (* sub_stem *) eapply sub_trans; [ exact HG | exact d ].
  - (* sub_fork *) exfalso. exact HG.
  - (* sub_asf *) apply IHd. exact HG.
  - (* sub_funty *)
    eapply sub_trans; [ | exact d2 ].
    eapply sub_trans; [ | exact HG ].
    apply sub_fork; [ apply sub_zero | exact d1 ].
  - (* sub_quant *) apply (IHd (lift 1 A)). exact HG.
  - (* sub_quant_stem *)
    eapply sub_trans.
    + apply sub_lift.
    + apply sub_quant. exact HG.
  - (* sub_quant_fork *) exfalso. exact HG.
  - (* sub_quant_asf *) exact HG.
  - (* sub_dist *) apply fork_quant_lift. exact HG.
  - (* sub_inst *)
    pose proof (Hsubst (lift 1 A) ty u 0 HG) as X.
    change (Good2 (subst (lift 1 A) u) (subst ty u)) in X.
    rewrite subst_lift1 in X.
    exact X.
  - (* sub_lift *)
    pose proof (Hlift A ty 0 1 HG) as X.
    exact X.
  - (* sub_leaf_fun *) exfalso. exact HG.
  - (* sub_stem_fun *)
    apply sub_fork.
    + exact HG.
    + apply sub_zero.
  - (* sub_fork_leaf *) exfalso. exact HG.
  - (* sub_fork_stem *) exfalso. exact HG.
  - (* sub_fork_fork_leaf *) exfalso. exact HG.
  - (* sub_fork_fork_stem *) exfalso. exact HG.
  - (* sub_fork_fork_fork *) exfalso. exact HG.
  - (* sub_recursion *) exfalso. exact HG.
  - (* sub_tree *) exfalso. exact HG.
  - (* sub_to_asf *) exact HG.
  - (* sub_from_asf *) exact HG.
  - (* sub_bffs *) exfalso. exact HG.
  - (* sub_bfff *) exfalso. exact HG.
Qed.

Lemma Good2_lift :
  forall A S k n, Good2 A S -> Good2 (lift_rec A k n) (lift_rec S k n).
Proof.
  intros A S. revert A.
  induction S as [ m | S1 IH | a IHa b IHb | | B IH | A1 IHA1 B1 IHB1 | Z IH ];
    intros A k n H; simpl in *.
  - exact H.
  - (* Quant *)
    assert (E : lift_rec (lift 1 A) (S k) n = lift 1 (lift_rec A k n)).
    { unfold lift.
      pose proof (lift_lift_subst_gen A 0 1 (S k) n ltac:(lia)) as Hll.
      replace (0 + S k) with (S k) in Hll by lia.
      replace (S k - 1) with k in Hll by lia.
      exact Hll. }
    rewrite <- E. apply (IH (lift 1 A) (S k) n). exact H.
  - exact (subtype_lift_rec (Fork A a) b H k n).
  - exact H.
  - exact (subtype_lift_rec A B H k n).
  - exact H.
  - apply IH. exact H.
Qed.

Lemma Good2_subst :
  forall A S w k,
    Good2 A S -> Good2 (subst_rec A w k) (subst_rec S w k).
Proof.
  intros A S. revert A.
  induction S as [ m | S1 IH | a IHa b IHb | | B IH | A1 IHA1 B1 IHB1 | Z IH ];
    intros A w k H; simpl in *.
  - exfalso. exact H.
  - (* Quant: subst_rec (lift 1 A) w (S k) = lift 1 (subst_rec A w k) *)
    assert (E : subst_rec (lift 1 A) w (S k) = lift 1 (subst_rec A w k)).
    { unfold lift.
      pose proof (subst_lift_gen A w 0 k 1 ltac:(lia)) as Hs.
      replace (k + 1) with (S k) in Hs by lia.
      exact Hs. }
    rewrite <- E. apply (IH (lift 1 A) w (S k)). exact H.
  - exact (subtype_subst_rec (Fork A a) b H w k).
  - exact H.
  - exact (subtype_subst_rec A B H w k).
  - exact H.
  - apply IH. exact H.
Qed.

Lemma D2_unconditional :
  forall A u ty, subtype (Stem A) (Funty u ty) -> subtype (Fork A u) ty.
Proof.
  intros A u ty d.
  exact (Good2_stable Good2_lift Good2_subst (Stem A) (Funty u ty) d A (sub_zero A)).
Qed.

(* The two application lemmas used by Task.v, now unconditional. *)

Lemma subtype_leaf_app :
  forall A u ty,
    subtype Leaf (Funty u ty) ->
    subtype A u ->
    subtype (Stem A) ty.
Proof.
  intros A u ty Hleaf HAu.
  eapply sub_trans.
  - apply sub_stem. exact HAu.
  - apply D1_unconditional. exact Hleaf.
Qed.

Lemma subtype_stem_app :
  forall A B u ty,
    subtype (Stem A) (Funty u ty) ->
    subtype B u ->
    subtype (Fork A B) ty.
Proof.
  intros A B u ty Hstem HBu.
  eapply sub_trans.
  - apply sub_fork.
    + apply sub_zero.
    + exact HBu.
  - apply D2_unconditional. exact Hstem.
Qed.

(* ------------------------------------------------------------------ *)
(* Task lemmas and main theorems                                      *)
(* ------------------------------------------------------------------ *)

Lemma derive_node_inv: forall gamma ty,
  derive gamma Node ty -> subtype Leaf ty.
Proof.
  intros gamma ty H. inversion H; subst; assumption.
Qed.

Lemma derive_app_inv: forall gamma M N ty,
  derive gamma (M @ N) ty ->
  exists u, derive gamma M (Funty u ty) /\ derive gamma N u.
Proof.
  intros gamma M N ty H. inversion H; subst.
  eexists; split; eassumption.
Qed.

Lemma stem_fun_principal: forall M gamma u ty,
  program M ->
  (forall gamma ty, derive gamma M ty -> subtype (program_type M) ty) ->
  derive gamma (Node @ M) (Funty u ty) ->
  subtype (Stem (program_type M)) (Funty u ty).
Proof.
  intros M gamma u ty Hp IH Hd.
  destruct (derive_app_inv _ _ _ _ Hd) as [u0 [HdM HdN]].
  pose proof (derive_node_inv _ _ HdM) as HL.
  pose proof (IH _ _ HdN) as HA.
  eapply subtype_leaf_app; eassumption.
Qed.

Lemma leaf_fun2: forall A B : dtype, subtype Leaf (Funty A (Funty B (Fork A B))).
Proof.
  intros A B. eapply sub_trans.
  - apply sub_leaf_fun.
  - eapply sub_funty.
    + apply sub_zero.
    + apply sub_stem_fun.
Qed.

Theorem programs_have_types: forall p gamma, program p -> derive gamma p (program_type p).
Proof.
  intros p gamma Hp. induction Hp.
  - simpl. apply derive_node, sub_zero.
  - simpl. eapply derive_app.
    + apply derive_node. apply sub_leaf_fun.
    + exact IHHp.
  - simpl. eapply derive_app.
    + eapply derive_app.
      * apply derive_node. apply leaf_fun2.
      * exact IHHp1.
    + exact IHHp2.
Qed.

Theorem programs_have_principal_types:
  forall p, program p ->
            forall gamma ty, derive gamma p ty -> subtype (program_type p) ty.
Proof.
  intros p Hp. induction Hp; intros gamma ty Hd.
  - simpl. apply derive_node_inv with (gamma := gamma). exact Hd.
  - simpl.
    destruct (derive_app_inv _ _ _ _ Hd) as [u0 [HdM HdN]].
    pose proof (derive_node_inv _ _ HdM) as HL.
    pose proof (IHHp _ _ HdN) as HA.
    eapply subtype_leaf_app; eassumption.
  - simpl.
    destruct (derive_app_inv _ _ _ _ Hd) as [u0 [Hd1 HdN]].
    pose proof (stem_fun_principal M gamma u0 ty Hp1 IHHp1 Hd1) as HM.
    pose proof (IHHp2 _ _ HdN) as HN.
    eapply subtype_stem_app; eassumption.
Qed.
