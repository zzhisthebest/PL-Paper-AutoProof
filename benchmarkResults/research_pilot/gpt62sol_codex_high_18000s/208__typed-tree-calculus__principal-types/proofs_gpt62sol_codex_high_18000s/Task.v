Require Import String Arith Lia Bool List Nat.

Require Import terms types subtypes derive.

Open Scope string_scope.

Open Scope nat_scope.

Set Default Proof Using "Type".

Theorem programs_have_types: forall p gamma, program p -> derive gamma p (program_type p).
Proof.
  intros p gamma Hprogram.
  induction Hprogram as [| M HM IHM | M N HM IHM HN IHN]; simpl.
  - apply derive_node, sub_zero.
  - eapply derive_app; [apply derive_node, sub_leaf_fun | exact IHM].
  - eapply derive_app; [| exact IHN].
    eapply derive_app; [| exact IHM].
    apply derive_node.
    eapply sub_trans; [apply sub_leaf_fun |].
    apply sub_funty; [apply sub_zero | apply sub_stem_fun].
Qed.

(* Simultaneous substitution makes the interaction between instantiation
   and subtyping explicit, including when crossing a quantifier. *)
Local Definition under_renaming (rho : nat -> nat) (i : nat) : nat :=
  match i with 0 => 0 | S j => S (rho j) end.

Local Fixpoint rename_type (rho : nat -> nat) (ty : dtype) : dtype :=
  match ty with
  | Var i => Var (rho i)
  | Quant body => Quant (rename_type (under_renaming rho) body)
  | Funty a b => Funty (rename_type rho a) (rename_type rho b)
  | Leaf => Leaf
  | Stem a => Stem (rename_type rho a)
  | Fork a b => Fork (rename_type rho a) (rename_type rho b)
  | Asf a => Asf (rename_type rho a)
  end.

Local Definition cons_type (u : dtype) (sigma : nat -> dtype) (i : nat) : dtype :=
  match i with 0 => u | S j => sigma j end.

Local Definition under_substitution (sigma : nat -> dtype) : nat -> dtype :=
  cons_type (Var 0) (fun i => rename_type S (sigma i)).

Local Fixpoint substitute_type (sigma : nat -> dtype) (ty : dtype) : dtype :=
  match ty with
  | Var i => sigma i
  | Quant body => Quant (substitute_type (under_substitution sigma) body)
  | Funty a b => Funty (substitute_type sigma a) (substitute_type sigma b)
  | Leaf => Leaf
  | Stem a => Stem (substitute_type sigma a)
  | Fork a b => Fork (substitute_type sigma a) (substitute_type sigma b)
  | Asf a => Asf (substitute_type sigma a)
  end.

Local Lemma rename_type_ext : forall ty rho tau,
  (forall i, rho i = tau i) -> rename_type rho ty = rename_type tau ty.
Proof.
  induction ty; intros rho tau Heq; simpl; f_equal; auto.
  apply IHty. intros [|i]; simpl; auto.
Qed.

Local Lemma substitute_type_ext : forall ty sigma tau,
  (forall i, sigma i = tau i) ->
  substitute_type sigma ty = substitute_type tau ty.
Proof.
  induction ty; intros sigma tau Heq; simpl; f_equal; auto.
  apply IHty. intros [|i]; simpl; now rewrite ?Heq.
Qed.

Local Lemma substitute_type_identity : forall ty, substitute_type Var ty = ty.
Proof.
  induction ty; simpl; f_equal; auto.
  rewrite <- IHty at 2.
  apply substitute_type_ext. now intros [|i].
Qed.

Local Lemma rename_type_compose : forall ty rho tau,
  rename_type rho (rename_type tau ty) = rename_type (fun i => rho (tau i)) ty.
Proof.
  induction ty; intros rho tau; simpl; f_equal; auto.
  rewrite IHty. apply rename_type_ext. now intros [|i].
Qed.

Local Lemma rename_type_identity : forall ty, rename_type (fun i => i) ty = ty.
Proof.
  induction ty; simpl; f_equal; auto.
  rewrite <- IHty at 2. apply rename_type_ext. now intros [|i].
Qed.

Local Lemma substitute_type_rename : forall ty sigma rho,
  substitute_type sigma (rename_type rho ty) =
  substitute_type (fun i => sigma (rho i)) ty.
Proof.
  induction ty; intros sigma rho; simpl; f_equal; auto.
  rewrite IHty. apply substitute_type_ext. now intros [|i].
Qed.

Local Lemma rename_type_substitute : forall ty rho sigma,
  rename_type rho (substitute_type sigma ty) =
  substitute_type (fun i => rename_type rho (sigma i)) ty.
Proof.
  induction ty; intros rho sigma; simpl; f_equal; auto.
  rewrite IHty. apply substitute_type_ext. intros [|i]; simpl; auto.
  now rewrite !rename_type_compose.
Qed.

Local Lemma substitute_type_shift : forall ty sigma,
  substitute_type (under_substitution sigma) (rename_type S ty) =
  rename_type S (substitute_type sigma ty).
Proof.
  intros. rewrite substitute_type_rename, rename_type_substitute. reflexivity.
Qed.

Local Lemma substitute_type_compose : forall ty sigma tau,
  substitute_type sigma (substitute_type tau ty) =
  substitute_type (fun i => substitute_type sigma (tau i)) ty.
Proof.
  induction ty; intros sigma tau; simpl; f_equal; auto.
  rewrite IHty. apply substitute_type_ext. intros [|i]; simpl; auto.
  apply substitute_type_shift.
Qed.

Local Definition shift_index k n i := if k <=? i then n + i else i.

Local Lemma shift_index_under : forall k n i,
  under_renaming (shift_index k n) i = shift_index (S k) n i.
Proof.
  intros k n [|i]; [reflexivity |].
  unfold under_renaming, shift_index. simpl.
  destruct (k <=? i); lia.
Qed.

Local Lemma lift_rec_rename_type : forall ty k n,
  lift_rec ty k n = rename_type (shift_index k n) ty.
Proof.
  induction ty; intros k m; simpl; f_equal; auto.
  - unfold relocate, shift_index. destruct (test k n) as [Hle | Hgt].
    + now rewrite (proj2 (Nat.leb_le _ _) Hle).
    + now rewrite (proj2 (Nat.leb_gt _ _) Hgt).
  - rewrite IHty. apply rename_type_ext. intros i. symmetry. apply shift_index_under.
Qed.

Local Lemma lift_rename_type : forall ty n,
  lift n ty = rename_type (fun i => n + i) ty.
Proof. intros. apply lift_rec_rename_type. Qed.

Local Lemma insert_Var_below : forall u i k, i < k -> insert_Var u i k = Var i.
Proof.
  intros. unfold insert_Var. destruct (compare k i) as [[Hlt | Heq] | Hgt];
    try lia; reflexivity.
Qed.

Local Lemma insert_Var_at : forall u k, insert_Var u k k = lift k u.
Proof.
  intros. unfold insert_Var. destruct (compare k k) as [[Hlt | Heq] | Hgt];
    try lia; reflexivity.
Qed.

Local Lemma insert_Var_above : forall u i k,
  k < i -> insert_Var u i k = Var (Nat.pred i).
Proof.
  intros. unfold insert_Var. destruct (compare k i) as [[Hlt | Heq] | Hgt];
    try lia; reflexivity.
Qed.

Local Lemma insert_Var_under : forall u k i,
  insert_Var u i (S k) = under_substitution (fun j => insert_Var u j k) i.
Proof.
  intros u k [|i].
  - apply insert_Var_below. lia.
  - change (insert_Var u (S i) (S k) = rename_type S (insert_Var u i k)).
    destruct (Nat.lt_trichotomy i k) as [Hlt | [-> | Hgt]].
    + now rewrite !insert_Var_below by lia.
    + rewrite !insert_Var_at, !lift_rename_type, rename_type_compose. reflexivity.
    + rewrite !insert_Var_above by lia. destruct i; [lia | reflexivity].
Qed.

Local Lemma subst_rec_substitute_type : forall ty u k,
  subst_rec ty u k = substitute_type (fun i => insert_Var u i k) ty.
Proof.
  induction ty; intros u k; simpl; f_equal; auto.
  rewrite IHty. apply substitute_type_ext. apply insert_Var_under.
Qed.

Local Lemma subst_substitute_type : forall ty u,
  subst ty u = substitute_type (cons_type u Var) ty.
Proof.
  intros. unfold subst. rewrite subst_rec_substitute_type.
  apply substitute_type_ext. intros [|i].
  - rewrite insert_Var_at, lift_rename_type. apply rename_type_identity.
  - now rewrite insert_Var_above by lia.
Qed.

Local Fixpoint under_quantifiers n sigma :=
  match n with
  | 0 => sigma
  | S k => under_substitution (under_quantifiers k sigma)
  end.

Local Lemma substitute_type_quant : forall n ty sigma,
  substitute_type sigma (quant n ty) =
  quant n (substitute_type (under_quantifiers n sigma) ty).
Proof.
  induction n; intros; simpl; auto.
Qed.

Local Lemma under_quantifiers_shift : forall n sigma i,
  under_quantifiers n sigma (n + i) = rename_type (fun j => n + j) (sigma i).
Proof.
  induction n; intros; simpl.
  - symmetry. apply rename_type_identity.
  - rewrite IHn, rename_type_compose. reflexivity.
Qed.

Local Lemma substitute_type_lift_under : forall n ty sigma,
  substitute_type (under_substitution (under_quantifiers n sigma)) (lift_rec ty 1 n) =
  lift_rec (substitute_type (under_substitution sigma) ty) 1 n.
Proof.
  intros. rewrite !lift_rec_rename_type, substitute_type_rename, rename_type_substitute.
  apply substitute_type_ext. intros [|i]; simpl.
  - reflexivity.
  - unfold shift_index at 1. simpl. rewrite Nat.add_succ_r. simpl.
    rewrite under_quantifiers_shift, !rename_type_compose.
    apply rename_type_ext. intros j. unfold shift_index. simpl. lia.
Qed.

Local Lemma variant_rename_type : forall ty rho k j pos,
  (forall i, (k =? rho i) = (j =? i)) ->
  variant pos k (rename_type rho ty) = variant pos j ty.
Proof.
  induction ty; intros rho k j pos H; simpl; auto.
  - now rewrite H.
  - apply IHty. intros [|i]; [reflexivity | apply H].
  - now rewrite (IHty1 rho k j), (IHty2 rho k j) by exact H.
  - now rewrite (IHty1 rho k j), (IHty2 rho k j) by exact H.
Qed.

Local Lemma variant_rename_absent : forall ty rho k pos,
  (forall i, (k =? rho i) = false) ->
  variant pos k (rename_type rho ty) = true.
Proof.
  induction ty; intros rho k pos H; simpl; auto.
  - now rewrite H.
  - apply IHty. intros [|i]; [reflexivity | apply H].
  - now rewrite (IHty1 rho k), (IHty2 rho k) by exact H.
  - now rewrite (IHty1 rho k), (IHty2 rho k) by exact H.
Qed.

Local Lemma variant_substitute_type : forall ty sigma k,
  sigma k = Var k ->
  (forall i, i <> k -> forall pos, variant pos k (sigma i) = true) ->
  forall pos, variant pos k (substitute_type sigma ty) = variant pos k ty.
Proof.
  induction ty; intros sigma k Hvar Hother pos; simpl; auto.
  - destruct (Nat.eq_dec k n) as [-> | Hneq].
    + now rewrite Hvar.
    + rewrite (proj2 (Nat.eqb_neq _ _) Hneq). apply Hother. congruence.
  - apply IHty.
    + simpl. now rewrite Hvar.
    + intros [|i] Hneq sign; simpl; auto.
      rewrite (variant_rename_type (sigma i) S (S k) k sign) by reflexivity.
      apply Hother. congruence.
  - now rewrite (IHty1 sigma k), (IHty2 sigma k) by assumption.
  - now rewrite (IHty1 sigma k), (IHty2 sigma k) by assumption.
Qed.

Local Lemma covariant_substitute_type : forall ty sigma,
  covariant ty -> covariant (substitute_type (under_substitution sigma) ty).
Proof.
  intros ty sigma H. unfold covariant in *.
  rewrite (variant_substitute_type ty (under_substitution sigma) 0); auto.
  intros [|i] Hneq pos; [congruence |].
  apply variant_rename_absent. reflexivity.
Qed.

Local Lemma substitute_type_cons_shift : forall ty u sigma,
  substitute_type (cons_type u sigma) (rename_type S ty) = substitute_type sigma ty.
Proof. intros. rewrite substitute_type_rename. reflexivity. Qed.

Local Lemma substitute_type_inst : forall ty u sigma,
  substitute_type sigma (subst ty u) =
  subst (substitute_type (under_substitution sigma) ty) (substitute_type sigma u).
Proof.
  intros. rewrite !subst_substitute_type, !substitute_type_compose.
  apply substitute_type_ext. intros [|i]; simpl; auto.
  symmetry. rewrite substitute_type_cons_shift. apply substitute_type_identity.
Qed.

Local Lemma substitute_type_omega2 : forall sigma,
  substitute_type sigma omega2_ty = omega2_ty.
Proof. reflexivity. Qed.

Local Lemma substitute_type_bfff_aug : forall sigma ty,
  substitute_type sigma (bfff_aug ty) = bfff_aug (substitute_type sigma ty).
Proof. reflexivity. Qed.

Local Lemma substitute_type_bffs_aug : forall sigma ty,
  substitute_type sigma (bffs_aug ty) = bffs_aug (substitute_type sigma ty).
Proof. reflexivity. Qed.

Local Lemma subtype_substitute_type : forall a b,
  subtype a b -> forall sigma,
  subtype (substitute_type sigma a) (substitute_type sigma b).
Proof.
  intros a b Hsub.
  induction Hsub; intro sigma; cbn [substitute_type];
    try solve [eauto using sub_zero, sub_trans, sub_stem, sub_fork,
      sub_asf, sub_funty, sub_quant, sub_quant_stem, sub_quant_fork,
      sub_quant_asf, sub_dist, sub_leaf_fun, sub_stem_fun, sub_fork_leaf,
      sub_fork_stem, sub_fork_fork_leaf, sub_fork_fork_stem,
      sub_fork_fork_fork, sub_to_asf, sub_from_asf].
  - rewrite substitute_type_inst. apply sub_inst.
  - rewrite lift_rename_type, substitute_type_shift.
    rewrite <- (lift_rename_type _ 1). apply sub_lift.
  - rewrite substitute_type_omega2, !substitute_type_quant.
    apply sub_recursion.
  - cbn [quant substitute_type].
    rewrite !substitute_type_inst. cbn [substitute_type].
    pose proof (substitute_type_lift_under 1 ty sigma) as Hstem.
    pose proof (substitute_type_lift_under 2 ty sigma) as Hfork.
    cbn [under_quantifiers] in Hstem, Hfork.
    rewrite Hstem, Hfork.
    apply sub_tree. now apply covariant_substitute_type.
  - rewrite substitute_type_bffs_aug. apply sub_bffs.
  - rewrite substitute_type_bfff_aug. apply sub_bfff.
Qed.

Local Lemma substitute_type_as_rename : forall ty rho,
  substitute_type (fun i => Var (rho i)) ty = rename_type rho ty.
Proof.
  induction ty; intros rho; simpl; f_equal; auto.
  rewrite <- IHty. apply substitute_type_ext. now intros [|i].
Qed.

Local Lemma subtype_shift : forall a b,
  subtype a b -> subtype (rename_type S a) (rename_type S b).
Proof.
  intros a b H.
  rewrite <- !substitute_type_as_rename. now apply subtype_substitute_type.
Qed.

Local Definition constructor_result (payload : option dtype) (input : dtype) :=
  match payload with None => Stem input | Some a => Fork a input end.

Local Definition closed_payload (payload : option dtype) :=
  match payload with
  | None => True
  | Some a => forall sigma, substitute_type sigma a = a
  end.

Local Lemma closed_payload_shift : forall a,
  closed_payload (Some a) -> rename_type S a = a.
Proof.
  intros a H. rewrite <- substitute_type_as_rename. apply H.
Qed.

Local Lemma constructor_result_shift : forall payload u,
  closed_payload payload ->
  rename_type S (constructor_result payload u) =
  constructor_result payload (rename_type S u).
Proof.
  intros [a |] u H; simpl; [now rewrite (closed_payload_shift a H) | reflexivity].
Qed.

(* The payload distinguishes a leaf from a stem. In the function case the
   specification describes the result of applying that constructor.
   Under Quant it must hold for every instantiation of the bound variable. *)
Local Fixpoint constructor_spec
    (payload : option dtype) (sigma : nat -> dtype) (ty : dtype) : Prop :=
  match ty with
  | Leaf => match payload with None => True | Some _ => False end
  | Stem b =>
      match payload with
      | None => False
      | Some a => subtype a (substitute_type sigma b)
      end
  | Funty a b =>
      forall u, subtype u (substitute_type sigma a) ->
        subtype (constructor_result payload u) (substitute_type sigma b)
  | Quant body => forall u, constructor_spec payload (cons_type u sigma) body
  | Asf body => constructor_spec payload sigma body
  | Var _ | Fork _ _ => False
  end.

Local Lemma constructor_spec_ext : forall ty payload sigma tau,
  constructor_spec payload sigma ty ->
  (forall i, sigma i = tau i) -> constructor_spec payload tau ty.
Proof.
  induction ty; intros payload sigma tau H Heq;
    cbn [constructor_spec] in *; try tauto.
  - intro u. eapply IHty; [exact (H u) |].
    intros [|i]; simpl; auto.
  - now rewrite (substitute_type_ext ty1 sigma tau Heq),
      (substitute_type_ext ty2 sigma tau Heq) in H.
  - now rewrite (substitute_type_ext ty sigma tau Heq) in H.
  - eapply IHty; eassumption.
Qed.

Local Lemma constructor_spec_substitute : forall ty payload sigma tau,
  constructor_spec payload (fun i => substitute_type sigma (tau i)) ty ->
  constructor_spec payload sigma (substitute_type tau ty).
Proof.
  induction ty; intros payload sigma tau H; cbn [constructor_spec substitute_type] in *;
    try solve [exact H | contradiction].
  - intro u. apply IHty.
    eapply constructor_spec_ext; [exact (H u) |].
    intros [|i]; simpl; [reflexivity | symmetry; apply substitute_type_cons_shift].
  - now rewrite !substitute_type_compose.
  - destruct payload; simpl in *; [now rewrite substitute_type_compose | contradiction].
  - now apply IHty.
Qed.

Local Lemma subtype_generalize : forall a b,
  subtype (rename_type S a) b -> subtype a (Quant b).
Proof.
  intros a b H.
  eapply sub_trans; [apply sub_lift |].
  apply sub_quant. rewrite lift_rename_type. exact H.
Qed.

Local Lemma subtype_under_quantifier : forall u a,
  subtype u (Quant a) -> subtype (rename_type S u) a.
Proof.
  intros u a H.
  eapply sub_trans; [exact (subtype_shift _ _ H) |].
  change (subtype (Quant (rename_type (under_renaming S) a)) a).
  replace a with (subst (rename_type (under_renaming S) a) (Var 0)) at 2.
  - apply sub_inst.
  - rewrite subst_substitute_type, substitute_type_rename.
    rewrite <- (substitute_type_identity a) at 2.
    apply substitute_type_ext. now intros [|i].
Qed.

Local Lemma constructor_spec_subtype : forall a b,
  subtype a b -> forall payload,
  closed_payload payload ->
  (forall sigma, constructor_spec payload sigma a) ->
  forall sigma, constructor_spec payload sigma b.
Proof.
  intros a b Hsub.
  induction Hsub; intros payload Hclosed Hspec sigma;
    try solve [exfalso; exact (Hspec sigma)].
  - apply Hspec.
  - apply IHHsub2; [exact Hclosed | now apply IHHsub1].
  - specialize (Hspec sigma). destruct payload as [a |]; simpl in *; [| contradiction].
    eapply sub_trans; [exact Hspec | now apply subtype_substitute_type].
  - now apply IHHsub.
  - intros u Hu. specialize (Hspec sigma).
    eapply sub_trans.
    + apply Hspec. eapply sub_trans; [exact Hu | now apply subtype_substitute_type].
    + now apply subtype_substitute_type.
  - assert (Hbody : forall tau, constructor_spec payload tau vty1).
    { intro tau. eapply constructor_spec_ext.
      - exact (Hspec (fun i => tau (S i)) (tau 0)).
      - intros [|i]; reflexivity. }
    intro u. now apply IHHsub.
  - destruct payload as [a |]; [| exact (Hspec sigma Leaf)].
    apply subtype_generalize. rewrite (closed_payload_shift a Hclosed).
    exact (Hspec (fun i => rename_type S (sigma i)) (Var 0)).
  - exact (Hspec sigma Leaf).
  - exact (Hspec sigma).
  - intros u Hu. apply subtype_generalize.
    rewrite constructor_result_shift by exact Hclosed.
    apply (Hspec (fun i => rename_type S (sigma i)) (Var 0)).
    now apply subtype_under_quantifier.
  - rewrite subst_substitute_type. apply constructor_spec_substitute.
    eapply constructor_spec_ext.
    + exact (Hspec sigma (substitute_type sigma u)).
    + intros [|i]; reflexivity.
  - intro u. rewrite lift_rename_type, <- substitute_type_as_rename.
    apply constructor_spec_substitute. apply Hspec.
  - destruct payload; simpl in *; [contradiction (Hspec sigma) |].
    intros u Hu. now apply sub_stem.
  - destruct payload; simpl in *; [| contradiction (Hspec sigma)].
    intros u Hu. apply sub_fork; [exact (Hspec sigma) | exact Hu].
  - exact (Hspec sigma).
  - exact (Hspec sigma).
Qed.

Local Lemma leaf_function_result : forall a b u,
  subtype Leaf (Funty a b) -> subtype u a -> subtype (Stem u) b.
Proof.
  intros a b u Hfun Hu.
  pose proof (constructor_spec_subtype _ _ Hfun None
    Corelib.Init.Logic.I (fun _ => Corelib.Init.Logic.I) Var) as Hspec.
  simpl in Hspec. rewrite !substitute_type_identity in Hspec. now apply Hspec.
Qed.

Local Lemma stem_function_result : forall a b c u,
  closed_payload (Some a) ->
  subtype (Stem a) (Funty b c) -> subtype u b -> subtype (Fork a u) c.
Proof.
  intros a b c u Hclosed Hfun Hu.
  assert (Hstem : forall sigma, constructor_spec (Some a) sigma (Stem a)).
  { intro sigma. simpl. rewrite Hclosed. apply sub_zero. }
  pose proof (constructor_spec_subtype _ _ Hfun (Some a) Hclosed Hstem Var) as Hspec.
  simpl in Hspec. rewrite !substitute_type_identity in Hspec. now apply Hspec.
Qed.

Local Lemma program_type_closed : forall p,
  program p -> closed_payload (Some (program_type p)).
Proof.
  intros p Hprogram.
  induction Hprogram; intro sigma; simpl in *;
    now rewrite ?IHHprogram, ?IHHprogram1, ?IHHprogram2.
Qed.

Theorem programs_have_principal_types:
  forall p, program p ->
            forall gamma ty, derive gamma p ty -> subtype (program_type p) ty.
Proof.
  intros p Hprogram.
  induction Hprogram as [| M HM IHM | M N HM IHM HN IHN];
    intros gamma ty Hderive; simpl.
  - inversion Hderive; assumption.
  - inversion Hderive as [| | ? ? ? ? u Hfunction Hargument]; subst.
    inversion Hfunction as [| ? ? Hleaf |]; subst.
    eapply leaf_function_result; [exact Hleaf | exact (IHM _ _ Hargument)].
  - inversion Hderive as [| | ? ? ? ? u Hfunction Hargument]; subst.
    inversion Hfunction as [| | ? ? ? ? v Hnode Hleft]; subst.
    inversion Hnode as [| ? ? Hleaf |]; subst.
    eapply stem_function_result.
    + now apply program_type_closed.
    + eapply leaf_function_result; [exact Hleaf | exact (IHM _ _ Hleft)].
    + exact (IHN _ _ Hargument).
Qed.
