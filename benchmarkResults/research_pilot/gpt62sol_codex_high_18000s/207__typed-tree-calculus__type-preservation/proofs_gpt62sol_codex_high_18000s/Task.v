Require Import String Arith Lia Bool List Nat Datatypes.

Require Import terms types subtypes derive.

Set Default Proof Using "Type".

(* Simultaneous substitutions make instantiation under a quantifier explicit. *)
Definition up_ren (r : nat -> nat) n :=
  match n with 0 => 0 | S i => S (r i) end.

Fixpoint ren_type (r : nat -> nat) (t : dtype) : dtype :=
  match t with
  | Var i => Var (r i)
  | Quant a => Quant (ren_type (up_ren r) a)
  | Funty a b => Funty (ren_type r a) (ren_type r b)
  | Leaf => Leaf
  | Stem a => Stem (ren_type r a)
  | Fork a b => Fork (ren_type r a) (ren_type r b)
  | Asf a => Asf (ren_type r a)
  end.

Definition cons_type (u : dtype) (s : nat -> dtype) n :=
  match n with 0 => u | S i => s i end.

Definition up_sub (s : nat -> dtype) :=
  cons_type (Var 0) (fun i => ren_type S (s i)).

Fixpoint sub_type (s : nat -> dtype) (t : dtype) : dtype :=
  match t with
  | Var i => s i
  | Quant a => Quant (sub_type (up_sub s) a)
  | Funty a b => Funty (sub_type s a) (sub_type s b)
  | Leaf => Leaf
  | Stem a => Stem (sub_type s a)
  | Fork a b => Fork (sub_type s a) (sub_type s b)
  | Asf a => Asf (sub_type s a)
  end.

Lemma ren_type_ext r q t :
  (forall i, r i = q i) -> ren_type r t = ren_type q t.
Proof.
  revert r q. induction t; intros; simpl; f_equal; auto.
  apply IHt. intros [|i]; simpl; auto.
Qed.

Lemma ren_type_comp r q t :
  ren_type r (ren_type q t) = ren_type (fun i => r (q i)) t.
Proof.
  revert r q. induction t; intros; simpl; f_equal; auto.
  rewrite IHt. apply ren_type_ext. intros [|i]; reflexivity.
Qed.

Lemma sub_type_ext s q t :
  (forall i, s i = q i) -> sub_type s t = sub_type q t.
Proof.
  revert s q. induction t; intros; simpl; f_equal; auto.
  apply IHt. intros [|i]; simpl; auto. now rewrite H.
Qed.

Lemma sub_type_ren s r t :
  sub_type s (ren_type r t) = sub_type (fun i => s (r i)) t.
Proof.
  revert s r. induction t; intros; simpl; f_equal; auto.
  rewrite IHt. apply sub_type_ext. intros [|i]; reflexivity.
Qed.

Lemma ren_type_sub r s t :
  ren_type r (sub_type s t) = sub_type (fun i => ren_type r (s i)) t.
Proof.
  revert r s. induction t; intros; simpl; f_equal; auto.
  rewrite IHt. apply sub_type_ext. intros [|i]; simpl; auto.
  now rewrite !ren_type_comp.
Qed.

Lemma sub_type_comp s q t :
  sub_type s (sub_type q t) = sub_type (fun i => sub_type s (q i)) t.
Proof.
  revert s q. induction t; intros; simpl; f_equal; auto.
  rewrite IHt. apply sub_type_ext. intros [|i]; simpl; auto.
  now rewrite sub_type_ren, ren_type_sub.
Qed.

Lemma sub_type_id t : sub_type Var t = t.
Proof.
  induction t; simpl; f_equal; auto.
  now rewrite (sub_type_ext (up_sub Var) Var t) by (intros [|i]; reflexivity).
Qed.

Lemma lift_rec_ren t k n :
  lift_rec t k n = ren_type (fun i => relocate i k n) t.
Proof.
  revert k. induction t; intro k; simpl; f_equal; auto.
  rewrite IHt. apply ren_type_ext. intros [|i]; cbn [up_ren]; unfold relocate.
  - destruct (test (S k) 0); lia.
  - destruct (test (S k) (S i)), (test k i); lia.
Qed.

Lemma lift_ren t n : lift n t = ren_type (fun i => n + i) t.
Proof.
  unfold lift. rewrite lift_rec_ren.
  apply ren_type_ext. intro i. unfold relocate. destruct test; lia.
Qed.

Lemma lift_one t : lift 1 t = ren_type S t.
Proof. apply lift_ren. Qed.

Lemma ren_type_as_sub r t :
  ren_type r t = sub_type (fun i => Var (r i)) t.
Proof.
  revert r. induction t; intros; simpl; f_equal; auto.
  rewrite IHt. apply sub_type_ext. intros [|i]; reflexivity.
Qed.

Lemma lift_zero t : lift 0 t = t.
Proof.
  rewrite lift_ren, ren_type_as_sub. apply sub_type_id.
Qed.

Lemma lift_plus t n k : lift k (lift n t) = lift (k+n) t.
Proof.
  rewrite !lift_ren, ren_type_comp. apply ren_type_ext. intro i. lia.
Qed.

Lemma subst_rec_sub t u k :
  subst_rec t u k = sub_type (fun i => insert_Var u i k) t.
Proof.
  revert k. induction t; intro k; simpl; f_equal; auto.
  rewrite IHt. apply sub_type_ext. intros [|i]; cbn [up_sub cons_type]; unfold insert_Var.
  - destruct (compare (S k) 0) as [[?|?]|?]; try lia; reflexivity.
  - destruct (compare (S k) (S i)) as [[?|?]|?],
             (compare k i) as [[?|?]|?]; try lia; try reflexivity.
    { destruct i; [lia|reflexivity]. }
    now rewrite <- lift_one, lift_plus.
Qed.

Lemma subst_sub t u : subst t u = sub_type (cons_type u Var) t.
Proof.
  unfold subst. rewrite subst_rec_sub. apply sub_type_ext.
  intros [|i]; cbn [cons_type]; unfold insert_Var.
  - destruct (compare 0 0) as [[?|?]|?]; try lia. apply lift_zero.
  - destruct (compare 0 (S i)) as [[?|?]|?]; try lia; reflexivity.
Qed.

Lemma sub_type_instantiate s t u :
  sub_type s (subst t u) = subst (sub_type (up_sub s) t) (sub_type s u).
Proof.
  rewrite !subst_sub, !sub_type_comp.
  apply sub_type_ext. intros [|i]; simpl; auto.
  now rewrite sub_type_ren, sub_type_id.
Qed.

Lemma sub_type_shift s t u :
  sub_type (cons_type u s) (ren_type S t) = sub_type s t.
Proof. now rewrite sub_type_ren. Qed.

Lemma sub_type_lift s t :
  sub_type (up_sub s) (lift 1 t) = lift 1 (sub_type s t).
Proof. now rewrite !lift_one, sub_type_ren, ren_type_sub. Qed.

Lemma inst_lift_quant t : subst (ren_type (up_ren S) t) (Var 0) = t.
Proof.
  rewrite subst_sub, sub_type_ren.
  transitivity (sub_type Var t); [apply sub_type_ext; intros [|i]; reflexivity|apply sub_type_id].
Qed.

Lemma lift_quant_instantiate t : subtype (lift 1 (Quant t)) t.
Proof.
  rewrite lift_one. simpl.
  rewrite <- (inst_lift_quant t) at 2. apply sub_inst.
Qed.

Lemma variant_ren r t k j p :
  (forall i, (j =? r i)%nat = (k =? i)%nat) ->
  variant p j (ren_type r t) = variant p k t.
Proof.
  revert r k j p. induction t; intros; simpl; try reflexivity;
    try solve [now rewrite H | now rewrite (IHt r k j p H) |
               now rewrite (IHt1 r k j _ H), (IHt2 r k j _ H)].
  apply IHt. intros [|i]; simpl; auto.
Qed.

Lemma variant_fresh_ren r t k p :
  (forall i, (k =? r i)%nat = false) ->
  variant p k (ren_type r t) = true.
Proof.
  revert r k p. induction t; intros; simpl; try reflexivity;
    try solve [now rewrite H | now rewrite (IHt r k p H) |
               now rewrite (IHt1 r k _ H), (IHt2 r k _ H)].
  apply IHt. intros [|i]; simpl; auto.
Qed.

Lemma variant_sub s t k p :
  (forall i q, variant q k (s i) = if (k =? i)%nat then q else true) ->
  variant p k (sub_type s t) = variant p k t.
Proof.
  revert s k p. induction t; intros; simpl; try reflexivity;
    try solve [now rewrite H | now rewrite (IHt s k p H) |
               now rewrite (IHt1 s k _ H), (IHt2 s k _ H)].
  apply IHt. intros [|i] q; simpl; auto.
  rewrite <- H. apply variant_ren. reflexivity.
Qed.

Lemma covariant_sub s t :
  covariant t -> covariant (sub_type (up_sub s) t).
Proof.
  unfold covariant. rewrite variant_sub; auto.
  intros [|i] p; simpl; auto using variant_fresh_ren.
Qed.

Definition leaf_branch t := subst t Leaf.
Definition stem_branch t :=
  Quant (Funty (Var 0) (subst (lift_rec t 1 1) (Stem (Var 0)))).
Definition fork_branch t :=
  Quant (Quant (Funty (Var 1)
                      (Funty (Var 0) (subst (lift_rec t 1 2) (Fork (Var 1) (Var 0)))))).

Lemma subst_branch t u n :
  subst (lift_rec t 1 n) u =
  sub_type (cons_type u (fun i => Var (n+i))) t.
Proof.
  rewrite lift_rec_ren, subst_sub, sub_type_ren.
  apply sub_type_ext. intros [|i]; unfold relocate.
  - destruct (test 1 0); try lia; reflexivity.
  - destruct (test 1 (S i)); try lia.
    replace (n + S i) with (S (n+i)) by lia. reflexivity.
Qed.

Lemma sub_type_leaf_branch s t :
  sub_type s (leaf_branch t) = leaf_branch (sub_type (up_sub s) t).
Proof. unfold leaf_branch. apply sub_type_instantiate. Qed.

Lemma sub_type_stem_branch s t :
  sub_type s (stem_branch t) = stem_branch (sub_type (up_sub s) t).
Proof.
  unfold stem_branch. cbn [sub_type].
  rewrite !subst_branch, !sub_type_comp. f_equal. f_equal.
  apply sub_type_ext. intros [|i]; simpl; auto.
  rewrite sub_type_ren.
  change (ren_type S (s i) = sub_type (fun j => Var (S j)) (s i)).
  now rewrite <- (sub_type_ren Var S (s i)), sub_type_id.
Qed.

Lemma sub_type_fork_branch s t :
  sub_type s (fork_branch t) = fork_branch (sub_type (up_sub s) t).
Proof.
  unfold fork_branch. cbn [sub_type].
  rewrite !subst_branch, !sub_type_comp. do 4 f_equal.
  apply sub_type_ext. intros [|i]; simpl; auto.
  rewrite sub_type_ren, ren_type_comp.
  change (ren_type (fun j => S (S j)) (s i) = sub_type (fun j => Var (S (S j))) (s i)).
  now rewrite <- (sub_type_ren Var (fun j => S (S j)) (s i)), sub_type_id.
Qed.

Lemma sub_type_program s p :
  sub_type s (program_type p) = program_type p.
Proof.
  revert s. induction p as [x| |p1 IHp1 p2 IHp2]; intros s; simpl; auto.
  specialize (IHp1 s). destruct (program_type p1); simpl in *; try reflexivity.
  - now rewrite IHp2.
  - injection IHp1 as H. now rewrite H, IHp2.
Qed.

Lemma sub_type_omega s : sub_type s omega2_ty = omega2_ty.
Proof. unfold omega2_ty, omega21_ty, omega22_ty. cbn [sub_type]. now rewrite !sub_type_program. Qed.

Lemma sub_type_quant s k t : sub_type s (quant k t) =
  quant k (sub_type (Nat.iter k up_sub s) t).
Proof.
  revert s t. induction k; intros; simpl; auto.
Qed.



Lemma subtype_substitution a b :
  subtype a b -> forall s, subtype (sub_type s a) (sub_type s b).
Proof.
  intro H. induction H; intro s; cbn [sub_type];
    try solve [econstructor; eauto using sub_zero, sub_trans].
  - rewrite sub_type_instantiate. apply sub_inst.
  - rewrite sub_type_lift. apply sub_lift.
  - change (subtype (sub_type s omega2_ty)
            (Funty (sub_type s omega2_ty)
               (Funty (Funty (sub_type s (quant k (Funty uty vty)))
                             (sub_type s (quant k (Funty uty vty))))
                      (sub_type s (quant k (Funty uty vty)))))).
    rewrite sub_type_omega, !sub_type_quant. apply sub_recursion.
  - change (subtype (Fork (Fork (sub_type s (leaf_branch ty))
                               (sub_type s (stem_branch ty)))
                         (sub_type s (fork_branch ty)))
                    (Funty (sub_type s uty) (sub_type s (subst ty uty)))).
    rewrite sub_type_leaf_branch, sub_type_stem_branch, sub_type_fork_branch,
            sub_type_instantiate.
    apply sub_tree. now apply covariant_sub.
Qed.

Lemma subtype_lift a b n :
  subtype a b -> subtype (lift n a) (lift n b).
Proof.
  intro H. rewrite !lift_ren.
  rewrite !ren_type_as_sub. now apply subtype_substitution.
Qed.

Lemma subtype_subst_variance t k a b :
  subtype a b -> forall p, variant p k t = true ->
  if p then subtype (subst_rec t a k) (subst_rec t b k)
       else subtype (subst_rec t b k) (subst_rec t a k).
Proof.
  intro H. revert k. induction t; intros k [] Hv; simpl in *;
    try solve [apply sub_zero];
    try solve [apply sub_quant; eapply IHt with (p := true); eauto|
               apply sub_quant; eapply IHt with (p := false); eauto|
               apply sub_stem; eapply IHt with (p := true); eauto|
               apply sub_stem; eapply IHt with (p := false); eauto|
               apply sub_asf; eapply IHt with (p := true); eauto|
               apply sub_asf; eapply IHt with (p := false); eauto].
  all: try apply andb_true_iff in Hv as [H1 H2].
  all: try solve [apply sub_fork; [eapply IHt1 with (p := true)|eapply IHt2 with (p := true)]; eauto|
                  apply sub_fork; [eapply IHt1 with (p := false)|eapply IHt2 with (p := false)]; eauto|
                  apply sub_funty; [eapply IHt1 with (p := false)|eapply IHt2 with (p := true)]; eauto|
                  apply sub_funty; [eapply IHt1 with (p := true)|eapply IHt2 with (p := false)]; eauto].
  all: unfold insert_Var; destruct (compare k n) as [[?|E]|?]; try apply sub_zero.
  - now apply subtype_lift.
  - subst. now rewrite Nat.eqb_refl in Hv.
Qed.

Lemma subtype_subst_covariant t a b :
  covariant t -> subtype a b -> subtype (subst t a) (subst t b).
Proof. intros Hv H. apply (subtype_subst_variance t 0 a b H true Hv). Qed.

Lemma derive_subtype gamma m a b :
  derive gamma m a -> subtype a b -> derive gamma m b.
Proof.
  intro H. revert b. induction H; intros b Hb.
  - eapply derive_ref; eauto using sub_trans.
  - apply derive_node. eauto using sub_trans.
  - eapply derive_app; [apply IHderive1; apply sub_funty; [apply sub_zero|exact Hb]|eassumption].
Qed.

Lemma derive_app_inv gamma m n b :
  derive gamma (m @ n) b -> exists a, derive gamma m (Funty a b) /\ derive gamma n a.
Proof. intro H. inversion H; subst. eauto. Qed.

Lemma derive_node_inv gamma t : derive gamma Node t -> subtype Leaf t.
Proof. intro H. now inversion H. Qed.

Lemma get_lift_context gamma x n :
  get x (lift_context n gamma) = option_map (lift n) (get x gamma).
Proof.
  induction gamma as [|[y t] gamma IH]; simpl; auto.
  now destruct (String.eqb y x).
Qed.

Lemma lift_context_plus gamma n j :
  lift_context j (lift_context n gamma) = lift_context (j+n) gamma.
Proof.
  induction gamma as [|[x t] gamma IH]; simpl; auto.
  change ((x, lift j (lift n t)) :: lift_context j (lift_context n gamma) =
          (x, lift (j+n) t) :: lift_context (j+n) gamma)%list.
  now rewrite lift_plus, IH.
Qed.

Lemma lift_context_zero gamma : lift_context 0 gamma = gamma.
Proof.
  induction gamma as [|[x t] gamma IH]; simpl; auto.
  change ((x, lift 0 t) :: lift_context 0 gamma = (x,t) :: gamma)%list.
  now rewrite lift_zero, IH.
Qed.

Lemma derive_lift gamma m t n :
  derive gamma m t -> derive (lift_context n gamma) m (lift n t).
Proof.
  intro H. induction H.
  - eapply derive_ref; [rewrite get_lift_context, H; reflexivity|now apply subtype_lift].
  - apply derive_node. now apply (subtype_lift _ _ n) in H.
  - eapply derive_app; eassumption.
Qed.

Lemma derive_quant gamma m t :
  derive (lift_context 1 gamma) m t -> derive gamma m (Quant t).
Proof.
  remember (lift_context 1 gamma) as delta eqn:E. intro H.
  induction H; subst.
  - rewrite get_lift_context in H. destruct (get x gamma) as [a|] eqn:Ha;
      inversion H; subst.
    eapply derive_ref; [exact Ha|].
    eapply sub_trans; [apply sub_lift|now apply sub_quant].
  - apply derive_node. eapply sub_trans; [apply (sub_lift Leaf)|now apply sub_quant].
  - eapply derive_app; [|exact (IHderive2 eq_refl)].
    eapply derive_subtype; [exact (IHderive1 eq_refl)|apply sub_dist].
Qed.

Lemma subtype_quant_intro a b :
  subtype (lift 1 a) b -> subtype a (Quant b).
Proof. intro H. eapply sub_trans; [apply sub_lift|now apply sub_quant]. Qed.

Lemma subtype_k t a b :
  subtype t b -> subtype (Fork Leaf t) (Funty a b).
Proof.
  intro H. eapply sub_trans; [apply sub_fork_leaf|].
  apply sub_funty; [apply sub_zero|exact H].
Qed.

Lemma subtype_s x y a b c :
  subtype x (Funty a (Funty b c)) -> subtype y (Funty a b) ->
  subtype (Fork (Stem x) y) (Funty a c).
Proof.
  intros Hx Hy. eapply sub_trans; [apply sub_fork; [apply sub_stem; exact Hx|exact Hy]|].
  apply sub_fork_stem.
Qed.

Lemma bfff_coerce t a b c :
  subtype t (Funty a (Funty b c)) -> subtype (bfff_aug t) (Funty a (Funty b c)).
Proof.
  intro H. unfold bfff_aug. apply subtype_s with (b := Funty b c).
  - apply subtype_k. eapply sub_trans with (ty2 := Funty (Funty b c) (Asf (Funty b c))).
    + unfold eval_ty. change (subtype (Quant (Funty (Var 0) (Asf (Var 0)))) (Funty (Funty b c) (Asf (Funty b c)))).
      rewrite <- (lift_zero (Funty b c)) at 1 2.
      apply (sub_inst (Funty (Var 0) (Asf (Var 0))) (Funty b c)).
    + apply sub_funty; [apply sub_zero|apply sub_from_asf].
  - eapply sub_trans; [apply sub_asf; exact H|apply sub_from_asf].
Qed.

Lemma eager_coerce b c : subtype eager_ty (Funty (Funty b c) (Funty b c)).
Proof.
  pose proof (sub_inst (Quant (Funty (Funty (Var 0) (Var 1))
                                    (Funty (Var 0) (Var 1)))) c) as H.
  rewrite subst_sub in H. cbn [sub_type up_sub cons_type] in H.
  eapply sub_trans; [exact H|].
  pose proof (sub_inst (Funty (Funty (Var 0) (ren_type S c))
                             (Funty (Var 0) (ren_type S c))) b) as H'.
  rewrite subst_sub in H'. cbn [sub_type cons_type] in H'.
  rewrite !sub_type_shift, !sub_type_id in H'. exact H'.
Qed.

Lemma bffs_coerce t a b c :
  subtype t (Funty a (Funty b c)) -> subtype (bffs_aug t) (Funty a (Funty b c)).
Proof.
  intro H. unfold bffs_aug. eapply subtype_s.
  - apply subtype_k, eager_coerce.
  - now apply bfff_coerce.
Qed.

Lemma stem_branch_instance t a :
  subtype (stem_branch t) (Funty a (subst t (Stem a))).
Proof.
  unfold stem_branch.
  eapply sub_trans; [apply (sub_inst _ a)|].
  rewrite subst_branch, !subst_sub. cbn [sub_type cons_type].
  rewrite sub_type_comp. replace (sub_type _ t) with (sub_type (cons_type (Stem a) Var) t)
    by (apply sub_type_ext; intros [|i]; reflexivity).
  apply sub_zero.
Qed.

Lemma fork_branch_instance t a b :
  subtype (fork_branch t) (Funty a (Funty b (subst t (Fork a b)))).
Proof.
  unfold fork_branch.
  eapply sub_trans; [apply (sub_inst _ a)|].
  rewrite subst_branch, !subst_sub. cbn [sub_type up_sub cons_type].
  eapply sub_trans; [apply (sub_inst _ b)|].
  rewrite subst_sub. cbn [sub_type cons_type].
  rewrite sub_type_shift, sub_type_id, !sub_type_comp.
  apply sub_funty; [apply sub_zero|]. apply sub_funty; [apply sub_zero|].
  replace (sub_type _ t) with (sub_type (cons_type (Fork a b) Var) t)
    by (apply sub_type_ext; intros [|i]; simpl; try reflexivity;
        now rewrite sub_type_shift, sub_type_id).
  apply sub_zero.
Qed.

(* A branch used only as a function may carry one of the Asf encodings. *)
Inductive branch_typing gamma m : bool -> dtype -> Prop :=
| branch_plain : forall binary t, derive gamma m t -> branch_typing gamma m binary t
| branch_asf : forall binary t,
    branch_typing gamma m binary (Asf t) -> branch_typing gamma m binary t
| branch_bfff : forall t,
    branch_typing gamma m true (bfff_aug t) -> branch_typing gamma m true t
| branch_bffs : forall t,
    branch_typing gamma m true (bffs_aug t) -> branch_typing gamma m true t.

Lemma bfff_mono a b : subtype a b -> subtype (bfff_aug a) (bfff_aug b).
Proof. intro H. apply sub_fork; [apply sub_zero|now apply sub_asf]. Qed.

Lemma bffs_mono a b : subtype a b -> subtype (bffs_aug a) (bffs_aug b).
Proof. intro H. apply sub_fork; [apply sub_zero|now apply bfff_mono]. Qed.

Lemma branch_subtype gamma m binary t u :
  branch_typing gamma m binary t -> subtype t u -> branch_typing gamma m binary u.
Proof.
  intro H. revert u. induction H; intros u Hsub.
  - apply branch_plain. eauto using derive_subtype.
  - apply branch_asf. auto using sub_asf.
  - apply branch_bfff. auto using bfff_mono.
  - apply branch_bffs. auto using bffs_mono.
Qed.

Definition branch_arrow (binary : bool) (t : dtype) :=
  if binary then exists a b c, t = Funty a (Funty b c)
  else exists a b, t = Funty a b.

Lemma branch_eliminate gamma m binary t :
  branch_typing gamma m binary t ->
  forall u, branch_arrow binary u -> subtype t u -> derive gamma m u.
Proof.
  intro H. induction H; intros u Hu Hsub.
  - eauto using derive_subtype.
  - apply IHbranch_typing; [exact Hu|].
    destruct binary; simpl in Hu; [destruct Hu as (a & b & c & ->)|destruct Hu as (a & b & ->)].
    all: eapply sub_trans; [apply sub_asf; exact Hsub|apply sub_from_asf].
  - destruct Hu as (a & b & c & ->). apply IHbranch_typing; [now exists a, b, c|now apply bfff_coerce].
  - destruct Hu as (a & b & c & ->). apply IHbranch_typing; [now exists a, b, c|now apply bffs_coerce].
Qed.

Lemma branch_unary gamma m t a b :
  branch_typing gamma m false t -> subtype t (Funty a b) -> derive gamma m (Funty a b).
Proof. intros H Hsub. eapply branch_eliminate; eauto. exists a, b. reflexivity. Qed.

Lemma branch_binary gamma m t a b c :
  branch_typing gamma m true t -> subtype t (Funty a (Funty b c)) ->
  derive gamma m (Funty a (Funty b c)).
Proof. intros H Hsub. eapply branch_eliminate; eauto. exists a, b, c. reflexivity. Qed.

Lemma lift_bfff t n : lift n (bfff_aug t) = bfff_aug (lift n t).
Proof. reflexivity. Qed.

Lemma lift_bffs t n : lift n (bffs_aug t) = bffs_aug (lift n t).
Proof. reflexivity. Qed.

Lemma branch_lift gamma m binary t n :
  branch_typing gamma m binary t ->
  branch_typing (lift_context n gamma) m binary (lift n t).
Proof.
  intro H. induction H.
  - apply branch_plain. now apply derive_lift.
  - now apply branch_asf.
  - apply branch_bfff. now rewrite <- lift_bfff.
  - apply branch_bffs. now rewrite <- lift_bffs.
Qed.

Lemma quant_closed_eval : subtype (Quant (Stem (Fork Leaf eval_ty))) (Stem (Fork Leaf eval_ty)).
Proof.
  pose proof (sub_inst (Stem (Fork Leaf eval_ty)) Leaf) as H.
  rewrite subst_sub in H. exact H.
Qed.

Lemma quant_closed_eager : subtype (Quant (Stem (Fork Leaf eager_ty))) (Stem (Fork Leaf eager_ty)).
Proof.
  pose proof (sub_inst (Stem (Fork Leaf eager_ty)) Leaf) as H.
  rewrite subst_sub in H. exact H.
Qed.

Lemma quant_bfff t : subtype (Quant (bfff_aug t)) (bfff_aug (Quant t)).
Proof.
  unfold bfff_aug. eapply sub_trans; [apply sub_quant_fork|].
  apply sub_fork; [apply quant_closed_eval|apply sub_quant_asf].
Qed.

Lemma quant_bffs t : subtype (Quant (bffs_aug t)) (bffs_aug (Quant t)).
Proof.
  unfold bffs_aug. eapply sub_trans; [apply sub_quant_fork|].
  apply sub_fork; [apply quant_closed_eager|apply quant_bfff].
Qed.

Lemma branch_quant gamma m binary t :
  branch_typing (lift_context 1 gamma) m binary t ->
  branch_typing gamma m binary (Quant t).
Proof.
  intro H. induction H.
  - apply branch_plain. now apply derive_quant.
  - apply branch_asf. eauto using branch_subtype, sub_quant_asf.
  - apply branch_bfff. eauto using branch_subtype, quant_bfff.
  - apply branch_bffs. eauto using branch_subtype, quant_bffs.
Qed.

Inductive case_argument gamma : Tree -> dtype -> Prop :=
| case_arg_leaf : forall a, subtype Leaf a -> case_argument gamma Node a
| case_arg_stem : forall z a t, derive gamma z t -> subtype (Stem t) a ->
    case_argument gamma (Node @ z) a
| case_arg_fork : forall z1 z2 a t1 t2, derive gamma z1 t1 -> derive gamma z2 t2 ->
    subtype (Fork t1 t2) a -> case_argument gamma (Node @ z1 @ z2) a.

Lemma case_argument_subtype gamma z a b :
  case_argument gamma z a -> subtype a b -> case_argument gamma z b.
Proof.
  intros H Hsub. destruct H; econstructor; eauto using sub_trans.
Qed.

Lemma case_argument_lift gamma z a n :
  case_argument gamma z a -> case_argument (lift_context n gamma) z (lift n a).
Proof.
  intro H. destruct H.
  - apply case_arg_leaf. now apply (subtype_lift _ _ n) in H.
  - eapply case_arg_stem; [exact (derive_lift _ _ _ _ H)|apply (subtype_lift _ _ n) in H0; exact H0].
  - eapply case_arg_fork; [exact (derive_lift _ _ _ _ H)|exact (derive_lift _ _ _ _ H0)|].
    apply (subtype_lift _ _ n) in H1. exact H1.
Qed.

(* Each observation records the parts of a constructor typing that can be
   used by its computation rule.  Only a root observation can inspect an
   Asf type: an Asf at a nested position cannot enable a shape test there. *)
Inductive shape :=
| head_leaf
| head_stem (a : dtype)
| head_k (y : Tree)
| head_s (x y : Tree)
| head_case (w x y : Tree)
| nested_leaf
| nested_stem (x : Tree)
| nested_fork (w x : Tree)
| fork_bounds (a b : dtype).

Inductive observation :=
| inspect (p : shape)
| bound (a : dtype)
| term_type (m : Tree)
| branch_type (binary : bool) (m : Tree).

Definition leaf_view p :=
  match p with head_leaf | nested_leaf => True | _ => False end.

Definition stem_view p :=
  match p with
  | head_stem a => Some (bound a)
  | nested_stem x => Some (branch_type true x)
  | _ => None
  end.

Definition fork_view p :=
  match p with
  | head_k y => Some (inspect nested_leaf, term_type y)
  | head_s x y => Some (inspect (nested_stem x), branch_type false y)
  | head_case w x y => Some (inspect (nested_fork w x), branch_type true y)
  | nested_fork w x => Some (term_type w, branch_type false x)
  | fork_bounds a b => Some (bound a, bound b)
  | _ => None
  end.

Definition inspect_asf p :=
  match p with nested_leaf | nested_stem _ | nested_fork _ _ | fork_bounds _ _ => false | _ => true end.

Inductive computation : shape -> Tree -> Tree -> Prop :=
| compute_k : forall y z, computation (head_k y) z y
| compute_s : forall x y z, computation (head_s x y) z (x @ z @ (y @ z))
| compute_leaf : forall w x y, computation (head_case w x y) Node w
| compute_stem : forall w x y z, computation (head_case w x y) (Node @ z) (x @ z)
| compute_fork : forall w x y z1 z2, computation (head_case w x y) (Node @ z1 @ z2) (y @ z1 @ z2).

Definition omega22_types :=
  forall k u v, subtype omega22_ty
    (Funty omega2_ty (Funty (Funty (quant k (Funty u v)) (quant k (Funty u v)))
                            (quant k (Funty u v)))).

Definition input_type gamma p z a :=
  match p with head_case _ _ _ => case_argument gamma z a | _ => derive gamma z a end.

Definition constructor_tag t :=
  match t with Leaf => Some 0 | Stem _ => Some 1 | Fork _ _ => Some 2 | _ => None end.

(* Shape inversion and the recursive branch's typing are proved below.
   Keeping them as premises here allows subtype_observes to establish
   shape inversion before reasoning about any particular contraction. *)
Record computation_requirements : Prop := {
  recursion_types : omega22_types;
  stem_components : forall a b, subtype (Stem a) (Stem b) -> subtype a b;
  fork_components : forall a b c d, subtype (Fork a b) (Fork c d) ->
    subtype a c /\ subtype b d;
  matching_constructors : forall a b i j, subtype a b ->
    constructor_tag a = Some i -> constructor_tag b = Some j -> i = j
}.

Definition computation_types gamma p a b :=
  computation_requirements -> forall z r, computation p z r ->
    input_type gamma p z a -> derive gamma r b.

Definition application_view gamma p n a b :=
  match p with
  | head_leaf => subtype (Stem a) b
  | head_stem t => subtype (Fork (lift n t) a) b
  | head_k _ | head_s _ _ | head_case _ _ _ =>
      computation_types (lift_context n gamma) p a b
  | _ => True
  end.

Lemma input_type_subtype gamma p z a b :
  input_type gamma p z a -> subtype a b -> input_type gamma p z b.
Proof. destruct p; simpl; eauto using derive_subtype, case_argument_subtype. Qed.

Lemma input_type_lift gamma p z a n :
  input_type gamma p z a -> input_type (lift_context n gamma) p z (lift n a).
Proof. destruct p; simpl; auto using derive_lift, case_argument_lift. Qed.

Lemma application_view_mono gamma p n a a' b b' :
  subtype a' a -> subtype b b' ->
  application_view gamma p n a b -> application_view gamma p n a' b'.
Proof.
  intros Ha Hb. destruct p; simpl; auto.
  { intro H. eapply sub_trans; [apply sub_stem; exact Ha|]. eauto using sub_trans. }
  { intro H. eapply sub_trans; [apply sub_fork; [apply sub_zero|exact Ha]|].
    eauto using sub_trans. }
  all: unfold computation_types; intros H Homega z r Hstep Hz.
  all: eapply derive_subtype; [eapply H; eauto using input_type_subtype|exact Hb].
Qed.

Lemma application_view_quant gamma p n a b :
  application_view gamma p (S n) a b ->
  application_view gamma p n (Quant a) (Quant b).
Proof.
  destruct p; cbn [application_view]; auto.
  { intro H. apply subtype_quant_intro.
    eapply sub_trans; [apply sub_stem, lift_quant_instantiate|exact H]. }
  { intro H. apply subtype_quant_intro.
    change (subtype (Fork (lift 1 (lift n a0)) (lift 1 (Quant a))) b).
    rewrite lift_plus.
    eapply sub_trans; [apply sub_fork; [apply sub_zero|apply lift_quant_instantiate]|exact H]. }
  all: unfold computation_types; intros H Homega z r Hstep Hz.
  all: apply derive_quant; rewrite lift_context_plus.
  all: eapply H; eauto.
  all: match type of Hz with input_type _ ?p _ _ =>
    pose proof (input_type_lift _ p _ _ 1 Hz) as Hl;
    rewrite lift_context_plus in Hl;
    exact (input_type_subtype _ p _ _ _ Hl (lift_quant_instantiate a))
  end.
Qed.

Definition shift_env j (s : nat -> dtype) i := lift j (s i).
Definition extend_env j u s := cons_type u (shift_env j s).

Lemma shift_env_zero s i : shift_env 0 s i = s i.
Proof. apply lift_zero. Qed.

Lemma shift_env_plus j n s i :
  shift_env j (shift_env n s) i = shift_env (j+n) s i.
Proof. apply lift_plus. Qed.

Lemma sub_type_shift_env j s t :
  sub_type (shift_env j s) t = lift j (sub_type s t).
Proof. unfold shift_env. rewrite lift_ren, ren_type_sub. apply sub_type_ext. intro i. apply lift_ren. Qed.

(* The world index counts fresh type variables added to the context.
   Quantifiers can be instantiated in any later world, including a world
   with a fresh variable that can be generalized again. *)
Fixpoint observes gamma n (s : nat -> dtype) (o : observation) (t : dtype) : Prop :=
  match o with
  | bound a => subtype (lift n a) (sub_type s t)
  | term_type m => derive (lift_context n gamma) m (sub_type s t)
  | branch_type binary m => branch_typing (lift_context n gamma) m binary (sub_type s t)
  | inspect p =>
    match t with
    | Var _ => False
    | Leaf => leaf_view p
    | Stem a =>
        match stem_view p with Some oa => observes gamma n s oa a | None => False end
    | Fork a b =>
        match fork_view p with
        | Some (oa, ob) => observes gamma n s oa a /\ observes gamma n s ob b
        | None => False
        end
    | Funty a b =>
        forall j, application_view gamma p (j+n)
          (sub_type (shift_env j s) a) (sub_type (shift_env j s) b)
    | Quant a => forall j u, observes gamma (j+n) (extend_env j u s) o a
    | Asf a => if inspect_asf p then observes gamma n s o a else True
    end
  end.

Lemma observes_ext gamma n s q o t :
  (forall i, s i = q i) -> observes gamma n s o t -> observes gamma n q o t.
Proof.
  revert n s q o. induction t; intros d s q o E H;
    destruct o as [p|a|m|binary m]; cbn [observes] in *;
    try solve [exfalso; assumption | assumption |
               rewrite <- (sub_type_ext s q _ E); exact H].
  - intros j u. eapply IHt; [|apply H].
    intros [|i]; [reflexivity|unfold extend_env, cons_type, shift_env; now rewrite E].
  - intro j. assert (F : forall i, shift_env j s i = shift_env j q i)
      by (intro i; unfold shift_env; now rewrite E).
    rewrite <- !(sub_type_ext _ _ _ F). apply H.
  - destruct (stem_view p); eauto.
  - destruct (fork_view p) as [[oa ob]|]; [|contradiction].
    destruct H. split; eauto.
  - destruct (inspect_asf p); eauto.
Qed.

Lemma observes_later gamma n s o t :
  observes gamma n s o t ->
  forall j, observes gamma (j+n) (shift_env j s) o t.
Proof.
  revert n s o. induction t; intros d s o H j;
    destruct o as [p|a|m|binary m]; cbn [observes] in *;
    try solve [contradiction | assumption |
      rewrite sub_type_shift_env, <- lift_plus; now apply subtype_lift |
      rewrite sub_type_shift_env, <- lift_context_plus; now apply derive_lift |
      rewrite sub_type_shift_env, <- lift_context_plus; now apply branch_lift].
  - intros k u. replace (k + (j+d)) with ((k+j)+d) by lia.
    eapply observes_ext; [|apply H].
    intros [|i]; simpl; auto. symmetry. apply shift_env_plus.
  - intro k. replace (k+(j+d)) with ((k+j)+d) by lia.
    rewrite !(sub_type_ext _ _ _ (shift_env_plus k j s)). apply H.
  - destruct (stem_view p); eauto.
  - destruct (fork_view p) as [[oa ob]|]; [|contradiction].
    destruct H. split; eauto.
  - destruct (inspect_asf p); eauto.
Qed.

Lemma observe_sub_type gamma n s q o t :
  observes gamma n (fun i => sub_type s (q i)) o t ->
  observes gamma n s o (sub_type q t).
Proof.
  revert n s q o. induction t; intros d s q o H;
    destruct o as [p|a|m|binary m]; cbn [observes] in H;
    try solve [contradiction |
               destruct (sub_type q _) eqn:E; cbn [observes] in *;
               rewrite <- E, sub_type_comp; assumption].
  all: try solve [change (subtype _ (sub_type s (sub_type q _))); now rewrite sub_type_comp|
    change (derive _ _ (sub_type s (sub_type q _))); now rewrite sub_type_comp|
    change (branch_typing _ _ _ (sub_type s (sub_type q _))); now rewrite sub_type_comp].
  - cbn [sub_type observes]. intros j u. apply IHt.
    eapply observes_ext; [|apply H].
    intros [|i]; [reflexivity|].
    unfold extend_env. cbn [cons_type up_sub].
    rewrite sub_type_shift, sub_type_shift_env. reflexivity.
  - cbn [sub_type observes]. intro j. rewrite !sub_type_comp.
    assert (E : forall i, sub_type (shift_env j s) (q i) =
                           shift_env j (fun i => sub_type s (q i)) i)
      by (intro; apply sub_type_shift_env).
    rewrite !(sub_type_ext _ _ _ E). apply H.
  - exact H.
  - cbn [sub_type observes]. destruct (stem_view p); eauto.
  - cbn [sub_type observes]. destruct (fork_view p) as [[oa ob]|]; [|contradiction].
    destruct H. split; eauto.
  - cbn [sub_type observes]. destruct (inspect_asf p); eauto.
Qed.

Lemma extend_env_fresh j s i :
  extend_env (S j) (Var 0) s i = up_sub (shift_env j s) i.
Proof.
  destruct i; [reflexivity|].
  change (lift (S j) (s i) = ren_type S (lift j (s i))).
  now rewrite <- lift_one, lift_plus.
Qed.

Lemma observes_bound gamma n s a t :
  observes gamma n s (bound a) t = subtype (lift n a) (sub_type s t).
Proof. destruct t; reflexivity. Qed.

Lemma observes_term gamma n s m t :
  observes gamma n s (term_type m) t = derive (lift_context n gamma) m (sub_type s t).
Proof. destruct t; reflexivity. Qed.

Lemma observes_branch gamma n s binary m t :
  observes gamma n s (branch_type binary m) t =
  branch_typing (lift_context n gamma) m binary (sub_type s t).
Proof. destruct t; reflexivity. Qed.

Lemma observes_quant_intro gamma n s o t :
  (forall j u, observes gamma (j+n) (extend_env j u s) o t) ->
  observes gamma n s o (Quant t).
Proof.
  intro H. assert (E : forall i, extend_env 1 (Var 0) s i = up_sub s i).
  { intro i. rewrite (extend_env_fresh 0). destruct i; [reflexivity|].
    cbn [up_sub cons_type]. now rewrite shift_env_zero. }
  destruct o as [p|a|m|binary m]; [exact H|..];
    specialize (H 1 (Var 0));
    apply (observes_ext _ _ _ _ _ _ E) in H;
    rewrite ?observes_bound, ?observes_term, ?observes_branch in H |- *;
    cbn [sub_type].
  - apply subtype_quant_intro. now rewrite lift_plus.
  - apply derive_quant. rewrite lift_context_plus. exact H.
  - apply branch_quant. rewrite lift_context_plus. exact H.
Qed.

Lemma id_program_type a : subtype (program_type I) (Funty a a).
Proof.
  change (subtype (Fork (Stem (Stem Leaf)) (Stem Leaf)) (Funty a a)).
  apply subtype_s with (b := Fork Leaf a).
  - eapply sub_trans; [apply (sub_stem_fun Leaf a)|].
    apply sub_funty; [apply sub_zero|apply sub_fork_leaf].
  - apply sub_stem_fun.
Qed.

Lemma omega21_types a :
  subtype omega21_ty
    (Funty omega2_ty (Funty (Funty (Funty a a) a) (Funty (Funty a a) a))).
Proof.
  change (subtype (Fork Leaf (Stem (Stem (program_type I))))
    (Funty omega2_ty (Funty (Funty (Funty a a) a) (Funty (Funty a a) a)))).
  apply subtype_k. eapply sub_trans;
    [apply (sub_stem_fun (Stem (program_type I)) (Funty (Funty a a) a))|].
  apply sub_funty; [apply sub_zero|].
  apply subtype_s with (b := a); [apply id_program_type|apply sub_zero].
Qed.

Lemma case_branch_types gamma w x y t a :
  covariant t ->
  derive gamma w (leaf_branch t) ->
  branch_typing gamma x false (stem_branch t) ->
  branch_typing gamma y true (fork_branch t) ->
  computation_types gamma (head_case w x y) a (subst t a).
Proof.
  intros Hcov Hw Hx Hy _ z r Hstep Hz.
  inversion Hstep; subst; cbn [input_type] in Hz; inversion Hz; subst.
  - eapply derive_subtype; [exact Hw|]. now apply subtype_subst_covariant.
  - eapply derive_subtype; [|eapply subtype_subst_covariant; eassumption].
    eapply derive_app; [eapply branch_unary; [exact Hx|apply stem_branch_instance]|eassumption].
  - eapply derive_subtype; [|eapply subtype_subst_covariant; eassumption].
    eapply derive_app; [|eassumption].
    eapply derive_app; [eapply branch_binary; [exact Hy|apply fork_branch_instance]|eassumption].
Qed.

Local Ltac impossible_argument requirements :=
  match goal with
  | H : subtype ?a ?b |- _ =>
      let lhs := eval cbn [constructor_tag sub_type] in (constructor_tag a) in
      let rhs := eval cbn [constructor_tag sub_type] in (constructor_tag b) in
      lazymatch lhs with Some ?i =>
        lazymatch rhs with Some ?j =>
          discriminate (matching_constructors requirements a b i j H eq_refl eq_refl)
        end
      end
  end.

Lemma subtype_observes gamma a b :
  subtype a b -> forall n s o, observes gamma n s o a -> observes gamma n s o b.
Proof.
  intro H. pose proof H as Hsub.
  induction H; intros n s o Ho; destruct o as [p|a|m|binary m];
    try solve [rewrite observes_bound in Ho |- *;
                 eapply sub_trans; [exact Ho|now apply subtype_substitution] |
               rewrite observes_term in Ho |- *;
                 eapply derive_subtype; [exact Ho|now apply subtype_substitution] |
               rewrite observes_branch in Ho |- *;
                 eapply branch_subtype; [exact Ho|now apply subtype_substitution]].
  all: try solve [exact Ho].
  - eauto.
  - cbn [observes] in *. destruct (stem_view p); eauto.
  - cbn [observes] in *. destruct (fork_view p) as [[oa ob]|]; [|contradiction].
    destruct Ho. split; auto.
  - cbn [observes] in *. destruct (inspect_asf p); eauto.
  - cbn [observes] in *. intro j.
    eapply application_view_mono;
      [exact (subtype_substitution _ _ H (shift_env j s))
      |exact (subtype_substitution _ _ H0 (shift_env j s))|apply Ho].
  - cbn [observes] in *. intros j u. apply IHsubtype; [assumption|apply Ho].
  - cbn [observes] in *. destruct (stem_view p).
    + now apply observes_quant_intro.
    + exact (Ho 0 Leaf).
  - cbn [observes] in *. destruct (fork_view p) as [[oa ob]|].
    + split; apply observes_quant_intro; intros; apply (Ho j u).
    + exact (Ho 0 Leaf).
  - cbn [observes] in *. destruct (inspect_asf p); auto.
  - cbn [observes sub_type] in *. intro j. apply application_view_quant.
    specialize (Ho (S j) (Var 0) 0).
    rewrite !(sub_type_ext _ _ _ (shift_env_zero _)) in Ho.
    rewrite !(sub_type_ext _ _ _ (extend_env_fresh j s)) in Ho. exact Ho.
  - cbn [observes] in Ho. rewrite subst_sub. apply observe_sub_type.
    eapply observes_ext; [|exact (Ho 0 (sub_type s u))].
    intros [|i]; simpl; auto using shift_env_zero.
  - cbn [observes]. intros j u. rewrite lift_one, ren_type_as_sub. apply observe_sub_type.
    exact (observes_later _ _ _ _ _ Ho j).
  - cbn [observes] in *. destruct p; cbn [leaf_view] in Ho; try contradiction;
      intro j; cbn [application_view].
    + apply sub_zero.
    + constructor.
  - intro j. pose proof (observes_later _ _ _ _ _ Ho j) as Hl.
    destruct p; cbn [observes stem_view application_view] in Hl |- *; try contradiction.
    + rewrite observes_bound in Hl. apply sub_fork; [exact Hl|apply sub_zero].
    + constructor.
  - intro j. pose proof (observes_later _ _ _ _ _ Ho j) as Hl.
    destruct p; cbn [observes fork_view leaf_view application_view] in Hl |- *; try tauto.
    destruct Hl as [_ Hy]. rewrite observes_term in Hy.
    intros _ z r Hstep _. now inversion Hstep; subst.
  - intro j. pose proof (observes_later _ _ _ _ _ Ho j) as Hl.
    destruct p; cbn [observes fork_view stem_view application_view] in Hl |- *; try tauto.
    destruct Hl as [Hx Hy]. rewrite ?observes_branch in Hy.
    intros _ z r Hstep Hz. inversion Hstep; subst.
    eapply derive_app with (u := sub_type (shift_env j s) vty).
    + eapply derive_app; [eapply branch_binary; [exact Hx|apply sub_zero]|exact Hz].
    + eapply derive_app; [eapply branch_unary; [exact Hy|apply sub_zero]|exact Hz].
  - intro j. pose proof (observes_later _ _ _ _ _ Ho j) as Hl.
    destruct p; cbn [observes fork_view application_view] in Hl |- *; try tauto.
    destruct Hl as [[Hw Hx] Hy]. rewrite observes_term in Hw.
    intros Hreq z r Hstep Hz.
    inversion Hstep; subst; cbn [input_type] in Hz; inversion Hz; subst;
      try impossible_argument Hreq. exact Hw.
  - intro j. pose proof (observes_later _ _ _ _ _ Ho j) as Hl.
    destruct p; cbn [observes fork_view application_view] in Hl |- *; try tauto.
    destruct Hl as [[Hw Hx] Hy]. intros Hreq z r Hstep Hz.
    inversion Hstep; subst; cbn [input_type] in Hz; inversion Hz; subst;
      try impossible_argument Hreq.
    eapply derive_app; [|eassumption].
    eapply branch_unary; [exact Hx|].
    apply sub_funty; [eapply (stem_components Hreq); eassumption|apply sub_zero].
  - intro j. pose proof (observes_later _ _ _ _ _ Ho j) as Hl.
    destruct p; cbn [observes fork_view application_view] in Hl |- *; try tauto.
    destruct Hl as [[Hw Hx] Hy]. intros Hreq z r Hstep Hz.
    inversion Hstep; subst; cbn [input_type] in Hz; inversion Hz; subst;
      try impossible_argument Hreq.
    match goal with Hf : subtype (Fork _ _) (sub_type _ (Fork _ _)) |- _ =>
      destruct (fork_components Hreq _ _ _ _ Hf) as [Ha Hb]
    end.
    eapply derive_app; [eapply derive_app|eassumption].
    + eapply branch_binary; [exact Hy|].
      apply sub_funty; [exact Ha|apply sub_funty; [exact Hb|apply sub_zero]].
    + eassumption.
  - intro j. pose proof (observes_later _ _ _ _ _ Ho j) as Hl.
    destruct p; cbn [observes omega2_ty fork_view stem_view application_view] in Hl |- *;
      try tauto.
    destruct Hl as [Hx Hy]. rewrite observes_branch in Hx, Hy.
    unfold omega21_ty in Hx. unfold omega22_ty in Hy.
    rewrite sub_type_program in Hx, Hy. rewrite sub_type_omega.
    cbn [sub_type]. rewrite !sub_type_quant. cbn [sub_type].
    intros Hreq z r Hstep Hz. inversion Hstep; subst.
    eapply derive_app; [eapply derive_app|eapply derive_app].
    + eapply branch_binary; [exact Hx|apply omega21_types].
    + exact Hz.
    + eapply branch_unary; [exact Hy|apply (recursion_types Hreq)].
    + exact Hz.
  - change (observes gamma n s (inspect p)
      (Fork (Fork (leaf_branch ty) (stem_branch ty)) (fork_branch ty))) in Ho.
    intro j. pose proof (observes_later _ _ _ _ _ Ho j) as Hl.
    destruct p; cbn [observes fork_view application_view] in Hl |- *; try tauto.
    destruct Hl as [[Hw Hx] Hy].
    rewrite observes_term in Hw. rewrite !sub_type_leaf_branch in Hw.
    rewrite observes_branch in Hx, Hy.
    rewrite sub_type_stem_branch in Hx. rewrite sub_type_fork_branch in Hy.
    rewrite sub_type_instantiate.
    now apply case_branch_types; [apply covariant_sub| | |].
  - cbn [observes] in *. destruct (inspect_asf p); auto.
  - destruct p; cbn [observes inspect_asf application_view] in *; auto.
  - destruct p; cbn [observes fork_view stem_view application_view inspect_asf] in Ho |- *;
      try tauto.
    destruct Ho as [Hx Hy]. split.
    + rewrite observes_branch. apply branch_bffs. exact Hx.
    + rewrite observes_branch. apply branch_asf. exact Hy.
  - destruct p; cbn [observes fork_view application_view inspect_asf] in Ho |- *;
      try tauto.
    destruct Ho as [[Hw Hx] Hy]. repeat split; auto.
    + rewrite observes_branch. apply branch_asf. exact Hx.
    + rewrite observes_branch. apply branch_bfff. exact Hy.
Qed.


(* The identity environment and world zero recover ordinary typings. *)
Lemma observes_application gamma p a b :
  observes gamma 0 Var (inspect p) (Funty a b) ->
  application_view gamma p 0 a b.
Proof.
  cbn [observes]. intro H. specialize (H 0).
  now rewrite !sub_type_shift_env, !sub_type_id, !lift_zero in H.
Qed.

Lemma leaf_function a b : subtype Leaf (Funty a b) -> subtype (Stem a) b.
Proof.
  intro H.
  apply (observes_application nil head_leaf a b).
  eapply subtype_observes; [exact H|constructor].
Qed.

Lemma stem_function a b c : subtype (Stem a) (Funty b c) -> subtype (Fork a b) c.
Proof.
  intro H. assert (Hs : observes nil 0 Var (inspect (head_stem a)) (Stem a)).
  { cbn [observes stem_view]. rewrite observes_bound, sub_type_id, lift_zero. apply sub_zero. }
  pose proof (observes_application _ _ _ _ (subtype_observes _ _ _ H _ _ _ Hs)) as Hv.
  cbn [application_view] in Hv. now rewrite lift_zero in Hv.
Qed.

Lemma subtype_stem_components a b : subtype (Stem a) (Stem b) -> subtype a b.
Proof.
  intro H. assert (Hs : observes nil 0 Var (inspect (head_stem a)) (Stem a)).
  { cbn [observes stem_view]. rewrite observes_bound, sub_type_id, lift_zero. apply sub_zero. }
  pose proof (subtype_observes _ _ _ H _ _ _ Hs) as Hv.
  cbn [observes stem_view] in Hv. now rewrite observes_bound, sub_type_id, lift_zero in Hv.
Qed.

Lemma subtype_fork_components a b c d :
  subtype (Fork a b) (Fork c d) -> subtype a c /\ subtype b d.
Proof.
  intro H. assert (Hs : observes nil 0 Var (inspect (fork_bounds a b)) (Fork a b)).
  { cbn [observes fork_view]. rewrite !observes_bound, !sub_type_id, !lift_zero.
    split; apply sub_zero. }
  pose proof (subtype_observes _ _ _ H _ _ _ Hs) as Hv.
  cbn [observes fork_view] in Hv. now rewrite !observes_bound, !sub_type_id, !lift_zero in Hv.
Qed.

Lemma subtype_constructor_tag a b i j :
  subtype a b -> constructor_tag a = Some i -> constructor_tag b = Some j -> i = j.
Proof.
  intros H Ha Hb. destruct a; cbn [constructor_tag] in Ha; inversion Ha; subst; clear Ha.
  - assert (Hs : observes nil 0 Var (inspect head_leaf) Leaf) by constructor.
    pose proof (subtype_observes _ _ _ H _ _ _ Hs) as Hv.
    destruct b; cbn [constructor_tag] in Hb; inversion Hb; subst;
      cbn [observes stem_view fork_view] in Hv; tauto.
  - assert (Hs : observes nil 0 Var (inspect (head_stem a)) (Stem a)).
    { cbn [observes stem_view]. rewrite observes_bound, sub_type_id, lift_zero. apply sub_zero. }
    pose proof (subtype_observes _ _ _ H _ _ _ Hs) as Hv.
    destruct b; cbn [constructor_tag] in Hb; inversion Hb; subst;
      cbn [observes leaf_view fork_view] in Hv; tauto.
  - assert (Hs : observes nil 0 Var (inspect (fork_bounds a1 a2)) (Fork a1 a2)).
    { cbn [observes fork_view]. rewrite !observes_bound, !sub_type_id, !lift_zero.
      split; apply sub_zero. }
    pose proof (subtype_observes _ _ _ H _ _ _ Hs) as Hv.
    destruct b; cbn [constructor_tag] in Hb; inversion Hb; subst;
      cbn [observes leaf_view stem_view] in Hv; tauto.
Qed.

Lemma derive_stem_inv gamma x t :
  derive gamma (Node @ x) t ->
  exists a, derive gamma x a /\ subtype (Stem a) t.
Proof.
  intros H. apply derive_app_inv in H as (a & Hnode & Hx).
  exists a. split; [exact Hx|]. now apply leaf_function, (derive_node_inv gamma).
Qed.

Lemma derive_fork_inv gamma x y t :
  derive gamma (Node @ x @ y) t ->
  exists a b, derive gamma x a /\ derive gamma y b /\ subtype (Fork a b) t.
Proof.
  intros H. apply derive_app_inv in H as (b & Hstem & Hy).
  apply derive_stem_inv in Hstem as (a & Hx & Hfun).
  exists a, b. repeat split; auto using stem_function.
Qed.

Lemma derive_stem gamma x t : derive gamma x t -> derive gamma (Node @ x) (Stem t).
Proof. intro H. eapply derive_app; [apply derive_node, sub_leaf_fun|exact H]. Qed.

Lemma derive_fork gamma x y a b :
  derive gamma x a -> derive gamma y b -> derive gamma (Node @ x @ y) (Fork a b).
Proof.
  intros Hx Hy. eapply derive_app; [|exact Hy].
  eapply derive_subtype; [exact (derive_stem _ _ _ Hx)|apply sub_stem_fun].
Qed.

Lemma derive_K gamma x a b : derive gamma x b -> derive gamma (K @ x) (Funty a b).
Proof.
  intro H. eapply derive_subtype; [|apply sub_fork_leaf].
  apply derive_fork; [apply derive_node, sub_zero|exact H].
Qed.

Lemma derive_S gamma x y a b c :
  derive gamma x (Funty a (Funty b c)) -> derive gamma y (Funty a b) ->
  derive gamma (S1 x @ y) (Funty a c).
Proof.
  intros Hx Hy. unfold S1. eapply derive_subtype; [|apply sub_fork_stem].
  apply derive_fork; [exact (derive_stem _ _ _ Hx)|exact Hy].
Qed.

(* The closed recursion combinator is built entirely from these shapes.
   Its structural type is a subtype of each type derived for the term. *)
Inductive program_shape : Tree -> Prop :=
| program_leaf : program_shape Node
| program_stem : forall m, program_shape m -> program_shape (Node @ m)
| program_fork : forall m n, program_shape m -> program_shape n ->
    program_shape (Node @ m @ n).

Lemma derive_program gamma m : program_shape m -> derive gamma m (program_type m).
Proof.
  intro H. induction H; simpl.
  - apply derive_node, sub_zero.
  - now apply derive_stem.
  - now apply derive_fork.
Qed.

Lemma program_type_principal gamma m : program_shape m ->
  forall t, derive gamma m t -> subtype (program_type m) t.
Proof.
  intro H. induction H; intros t Ht; simpl.
  - now apply (derive_node_inv gamma).
  - apply derive_stem_inv in Ht as (a & Hm & Ha).
    eapply sub_trans; [apply sub_stem; exact (IHprogram_shape _ Hm)|exact Ha].
  - apply derive_fork_inv in Ht as (a & b & Hm & Hn & Hab).
    eapply sub_trans; [apply sub_fork; [exact (IHprogram_shape1 _ Hm)|exact (IHprogram_shape2 _ Hn)]|exact Hab].
Qed.

Lemma derive_I gamma a : derive gamma I (Funty a a).
Proof.
  eapply derive_subtype; [apply derive_program|apply id_program_type].
  unfold I, S1, K. repeat constructor.
Qed.

Lemma derive_ref_inv gamma x t :
  derive gamma (Ref x) t -> exists a, get x gamma = Some a /\ subtype a t.
Proof. intro H. inversion H; subst. eauto. Qed.

Lemma derive_unused gamma x a m t :
  occurs x m = false -> derive ((x,a) :: gamma) m t -> derive gamma m t.
Proof.
  revert t. induction m as [y| |m IHm n IHn]; intros t E H; cbn [occurs] in E.
  - apply derive_ref_inv in H as (b & Hb & Hsub).
    simpl in Hb. rewrite E in Hb. eapply derive_ref; eassumption.
  - apply derive_node. now apply derive_node_inv in H.
  - apply orb_false_iff in E as [Em En].
    apply derive_app_inv in H as (b & Hm & Hn).
    eapply derive_app; eauto.
Qed.

Lemma star_typing gamma x a m t :
  derive ((x,a) :: gamma) m t -> derive gamma (star x m) (Funty a t).
Proof.
  revert t. induction m as [y| |m IHm n IHn]; intros t H; cbn [star].
  - destruct (String.eqb x y) eqn:E.
    + apply derive_ref_inv in H as (b & Hb & Hsub).
      simpl in Hb. rewrite E in Hb. injection Hb as <-.
      eapply derive_subtype; [apply derive_I|apply sub_funty; [apply sub_zero|exact Hsub]].
    + apply derive_K. eapply derive_unused; [exact E|exact H].
  - apply derive_K. eapply derive_unused; [reflexivity|exact H].
  - destruct (occurs x (m @ n)) eqn:E.
    + apply derive_app_inv in H as (b & Hm & Hn).
      eapply derive_S; eauto.
    + apply derive_K. eapply derive_unused; eassumption.
Qed.

Inductive quantified_function : dtype -> Prop :=
| quantified_arrow : forall a b, quantified_function (Funty a b)
| quantified_more : forall t, quantified_function t -> quantified_function (Quant t).

Lemma quant_function k t : quantified_function t -> quantified_function (quant k t).
Proof. revert t. induction k; intros; simpl; auto using quantified_more. Qed.

Lemma wait2_typing t : quantified_function t ->
  forall gamma m n x a b,
    derive gamma m (Funty a (Funty b t)) ->
    derive gamma n a -> derive gamma x b ->
    derive gamma (wait2 m n x) t.
Proof.
  intro H. induction H as [d e|t H IH]; intros gamma m n x a b Hm Hn Hx.
  - unfold wait2. eapply derive_S; [|apply derive_I].
    eapply derive_S; [|apply derive_K; exact Hx].
    eapply derive_S; [apply derive_K; exact Hm|apply derive_K; exact Hn].
  - apply derive_quant. eapply IH with (a := lift 1 a) (b := lift 1 b);
      [|now apply derive_lift|now apply derive_lift].
    eapply derive_subtype; [exact (derive_lift _ _ _ 1 Hm)|].
    apply sub_funty; [apply sub_zero|].
    apply sub_funty; [apply sub_zero|apply lift_quant_instantiate].
Qed.

Lemma omega22_has_types : omega22_types.
Proof.
  unfold omega22_types. intros k u v.
  set (a := quant k (Funty u v)).
  unfold omega22_ty. eapply (program_type_principal nil).
  - vm_compute. repeat constructor.
  - unfold omega22. apply star_typing, star_typing.
    eapply wait2_typing with (a := omega2_ty) (b := Funty a a).
    + unfold a. apply quant_function, quantified_arrow.
    + eapply derive_ref; [reflexivity|apply sub_recursion].
    + eapply derive_ref; [reflexivity|apply sub_zero].
    + eapply derive_ref; [reflexivity|apply sub_zero].
Qed.

Lemma computation_requirements_hold : computation_requirements.
Proof.
  constructor; [apply omega22_has_types|apply subtype_stem_components|
                apply subtype_fork_components|apply subtype_constructor_tag].
Qed.


Lemma observes_typed gamma m t :
  derive gamma m t -> observes gamma 0 Var (term_type m) t.
Proof. rewrite observes_term, lift_context_zero, sub_type_id. auto. Qed.

Lemma observes_branch_typed gamma binary m t :
  derive gamma m t -> observes gamma 0 Var (branch_type binary m) t.
Proof.
  rewrite observes_branch, lift_context_zero, sub_type_id.
  apply branch_plain.
Qed.

Lemma observes_k gamma y t :
  derive gamma (Node @ Node @ y) t ->
  observes gamma 0 Var (inspect (head_k y)) t.
Proof.
  intro H. apply derive_fork_inv in H as (a & b & Hleaf & Hy & Hsub).
  eapply subtype_observes with (a := Fork Leaf b).
  - eapply sub_trans; [apply sub_fork; [exact (derive_node_inv _ _ Hleaf)|apply sub_zero]|exact Hsub].
  - cbn [observes fork_view leaf_view]. split; [constructor|now apply observes_typed].
Qed.

Lemma observes_s gamma x y t :
  derive gamma (Node @ (Node @ x) @ y) t ->
  observes gamma 0 Var (inspect (head_s x y)) t.
Proof.
  intro H. apply derive_fork_inv in H as (a & b & Hstem & Hy & Hsub).
  apply derive_stem_inv in Hstem as (c & Hx & Hc).
  eapply subtype_observes with (a := Fork (Stem c) b).
  - eapply sub_trans; [apply sub_fork; [exact Hc|apply sub_zero]|exact Hsub].
  - cbn [observes fork_view stem_view]. split; now apply observes_branch_typed.
Qed.

Lemma observes_case gamma w x y t :
  derive gamma (Node @ (Node @ w @ x) @ y) t ->
  observes gamma 0 Var (inspect (head_case w x y)) t.
Proof.
  intro H. apply derive_fork_inv in H as (a & b & Hfork & Hy & Hsub).
  apply derive_fork_inv in Hfork as (c & d & Hw & Hx & Hcd).
  eapply subtype_observes with (a := Fork (Fork c d) b).
  - eapply sub_trans; [apply sub_fork; [exact Hcd|apply sub_zero]|exact Hsub].
  - cbn [observes fork_view]. split.
    + split; [now apply observes_typed|now apply observes_branch_typed].
    + now apply observes_branch_typed.
Qed.

Lemma computation_preserves gamma p a b z r :
  observes gamma 0 Var (inspect p) (Funty a b) ->
  computation p z r -> input_type gamma p z a -> derive gamma r b.
Proof.
  intros H Hstep Hz. apply observes_application in H.
  assert (Htypes : computation_types (lift_context 0 gamma) p a b).
  { destruct Hstep; exact H. }
  rewrite lift_context_zero in Htypes.
  exact (Htypes computation_requirements_hold z r Hstep Hz).
Qed.

Theorem reduction_preserves_typing:
  forall gamma M ty, derive gamma M ty -> forall N, t_red1 M N -> derive gamma N ty.
Proof.
  intros gamma M ty H N Hstep. revert ty H.
  induction Hstep; intros ty H; apply derive_app_inv in H as (a & Hhead & Harg).
  - eapply computation_preserves; [exact (observes_k _ _ _ Hhead)|apply compute_k|exact Harg].
  - eapply computation_preserves; [exact (observes_s _ _ _ _ Hhead)|apply compute_s|exact Harg].
  - eapply computation_preserves; [exact (observes_case _ _ _ _ _ Hhead)|apply compute_leaf|].
    apply case_arg_leaf. exact (derive_node_inv _ _ Harg).
  - eapply computation_preserves; [exact (observes_case _ _ _ _ _ Hhead)|apply compute_stem|].
    apply derive_stem_inv in Harg as (t & Hz & Hsub).
    eapply case_arg_stem; eassumption.
  - eapply computation_preserves; [exact (observes_case _ _ _ _ _ Hhead)|apply compute_fork|].
    apply derive_fork_inv in Harg as (t1 & t2 & Hz1 & Hz2 & Hsub).
    eapply case_arg_fork; eassumption.
  - eapply derive_app; [apply IHHstep; exact Hhead|exact Harg].
  - eapply derive_app; [exact Hhead|apply IHHstep; exact Harg].
Qed.
