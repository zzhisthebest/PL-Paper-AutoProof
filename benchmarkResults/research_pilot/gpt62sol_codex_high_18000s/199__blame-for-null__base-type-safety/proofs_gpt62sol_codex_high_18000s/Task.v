From Stdlib Require Import Bool.
Require Import Definitions.
Require Import Metalib.Metatheory.
From Stdlib Require Import List Lia Arith.Wf_nat.

(* Opening removes a binder, so indices above the opened index decrease. *)
Fixpoint scoped_trm (k : nat) (t : trm) : Prop :=
  match t with
  | t_var_b n => n < k
  | t_var_f _ | t_null => True
  | t_abs _ s => scoped_trm (S k) s
  | t_app s u => scoped_trm k s /\ scoped_trm k u
  | t_app_safe f s u => scoped_trm k f /\ scoped_trm k s /\ scoped_trm k u
  | t_cast s _ _ _ => scoped_trm k s
  end.

Lemma scoped_trm_weaken : forall t k j,
  scoped_trm k t -> k <= j -> scoped_trm j t.
Proof.
  induction t; simpl; intros; try lia; intuition eauto with arith.
Qed.

Lemma scoped_open_var : forall t k x,
  scoped_trm k (open_trm_wrt_trm_rec k (t_var_f x) t) <->
  scoped_trm (S k) t.
Proof.
  induction t; intros; simpl.
  - destruct (lt_eq_lt_dec n k) as [[Hlt | Heq] | Hgt]; simpl; lia.
  - tauto.
  - tauto.
  - apply IHt.
  - rewrite IHt1, IHt2. tauto.
  - rewrite IHt1, IHt2, IHt3. tauto.
  - apply IHt.
Qed.

Lemma scoped_open_identity : forall t k u,
  scoped_trm k t -> open_trm_wrt_trm_rec k u t = t.
Proof.
  induction t; simpl; intros; try reflexivity.
  - destruct (lt_eq_lt_dec n k) as [[Hlt | Heq] | Hgt]; try lia.
    reflexivity.
  - f_equal. auto.
  - destruct H. f_equal; auto.
  - destruct H as [? [? ?]]. f_equal; auto.
  - f_equal. auto.
Qed.

Fixpoint trm_size (t : trm) : nat :=
  match t with
  | t_var_b _ | t_var_f _ | t_null => 1
  | t_abs _ s | t_cast s _ _ _ => S (trm_size s)
  | t_app s u => S (trm_size s + trm_size u)
  | t_app_safe f s u => S (trm_size f + trm_size s + trm_size u)
  end.

Lemma trm_size_open_var : forall t k x,
  trm_size (open_trm_wrt_trm_rec k (t_var_f x) t) = trm_size t.
Proof.
  induction t; intros; simpl; try (rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3; reflexivity).
  destruct (lt_eq_lt_dec n k) as [[? | ?] | ?]; reflexivity.
Qed.

Lemma scoped_trm_lc : forall t, scoped_trm 0 t -> lc_trm t.
Proof.
  cut (forall n t, trm_size t = n -> scoped_trm 0 t -> lc_trm t).
  { intros H t Hscope. eauto. }
  induction n using lt_wf_ind.
  intros t Hsize Hscope.
  destruct t as [i | x | | V s | s u | f s u | s V p T]; simpl in Hsize, Hscope.
  - lia.
  - constructor.
  - constructor.
  - constructor. intro x.
    unfold open_trm_wrt_trm.
    apply (H (trm_size (open_trm_wrt_trm_rec 0 (t_var_f x) s))).
    + rewrite trm_size_open_var. lia.
    + reflexivity.
    + now apply scoped_open_var.
  - destruct Hscope. constructor.
    + apply (H (trm_size s)); auto; lia.
    + apply (H (trm_size u)); auto; lia.
  - destruct Hscope as [? [? ?]].
    constructor.
    + apply (H (trm_size f)); auto; lia.
    + apply (H (trm_size s)); auto; lia.
    + apply (H (trm_size u)); auto; lia.
  - constructor. apply (H (trm_size s)); auto; lia.
Qed.

Lemma typing_scoped : forall G t T, typing G t T -> scoped_trm 0 t.
Proof.
  intros G t T Htyping. induction Htyping; simpl; try tauto.
  destruct (atom_fresh L) as [x Hfresh].
  apply (scoped_open_var s 0 x).
  change (scoped_trm 0 (open_trm_wrt_trm s (t_var_f x))). auto.
Qed.

Lemma typing_lc : forall G t T, typing G t T -> lc_trm t.
Proof.
  eauto using scoped_trm_lc, typing_scoped.
Qed.

Lemma typing_weaken_mid : forall G t T,
  typing G t T -> forall E F D,
  G = E ++ D -> uniq (E ++ F ++ D) -> typing (E ++ F ++ D) t T.
Proof.
  intros G t T Htyping. induction Htyping; intros E F D Heq Huniq;
    subst G; eauto using typing, binds_weaken.
  apply typing_abs with (L := L `union` dom (E ++ F ++ D)).
  intros x Hfresh. simpl_env.
  match goal with
  | IH : forall x, x `notin` L -> forall _ _ _, _ -> _ -> _ |- _ =>
      apply (IH x ltac:(solve_notin) ((x ~ V) ++ E) F D)
  end.
  - reflexivity.
  - simpl_env. apply uniq_cons; [assumption | solve_notin].
Qed.

Lemma typing_weaken_head : forall G t T,
  typing G t T -> forall F, uniq (F ++ G) -> typing (F ++ G) t T.
Proof.
  intros G t T Htyping F Huniq.
  exact (typing_weaken_mid G t T Htyping nil F G eq_refl Huniq).
Qed.

Fixpoint trm_fv (t : trm) : atoms :=
  match t with
  | t_var_b _ | t_null => empty
  | t_var_f x => singleton x
  | t_abs _ s | t_cast s _ _ _ => trm_fv s
  | t_app s u => trm_fv s `union` trm_fv u
  | t_app_safe f s u => trm_fv f `union` trm_fv s `union` trm_fv u
  end.

Fixpoint subst_fvar (x : atom) (v t : trm) : trm :=
  match t with
  | t_var_b n => t_var_b n
  | t_var_f y => if y == x then v else t_var_f y
  | t_null => t_null
  | t_abs V s => t_abs V (subst_fvar x v s)
  | t_app s u => t_app (subst_fvar x v s) (subst_fvar x v u)
  | t_app_safe f s u => t_app_safe (subst_fvar x v f) (subst_fvar x v s) (subst_fvar x v u)
  | t_cast s V p T => t_cast (subst_fvar x v s) V p T
  end.

Lemma subst_fvar_fresh : forall t x v,
  x `notin` trm_fv t -> subst_fvar x v t = t.
Proof.
  induction t; simpl; intros y v Hfresh; try reflexivity.
  - destruct (x == y) as [-> | Hneq]; [exfalso; fsetdec | reflexivity].
  - f_equal. auto.
  - f_equal; [apply IHt1 | apply IHt2]; solve_notin.
  - f_equal; [apply IHt1 | apply IHt2 | apply IHt3]; solve_notin.
  - f_equal. auto.
Qed.

Lemma subst_fvar_open_rec : forall t k x v u,
  scoped_trm 0 v ->
  subst_fvar x v (open_trm_wrt_trm_rec k u t) =
  open_trm_wrt_trm_rec k (subst_fvar x v u) (subst_fvar x v t).
Proof.
  induction t; intros k y v u Hscope; simpl.
  - destruct (lt_eq_lt_dec n k) as [[? | ?] | ?]; reflexivity.
  - destruct (x == y).
    + symmetry. apply scoped_open_identity.
      eapply scoped_trm_weaken; [eassumption | lia].
    + reflexivity.
  - reflexivity.
  - f_equal. auto.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal. auto.
Qed.

Lemma subst_fvar_intro : forall s x v,
  x `notin` trm_fv s -> scoped_trm 0 v ->
  subst_fvar x v (open_trm_wrt_trm s (t_var_f x)) = open_trm_wrt_trm s v.
Proof.
  intros s x v Hfresh Hscope. unfold open_trm_wrt_trm.
  rewrite subst_fvar_open_rec by assumption.
  rewrite (subst_fvar_fresh s x v) by assumption.
  simpl. destruct (x == x); congruence.
Qed.

Lemma typing_subst : forall G t T,
  typing G t T -> forall F x U E v,
  G = F ++ (x ~ U) ++ E -> typing E v U ->
  typing (F ++ E) (subst_fvar x v t) T.
Proof.
  intros G t T Htyping. induction Htyping; intros F y U E v Heq Hv;
    subst G; simpl; eauto using typing.
  - assert (Huniq : uniq (F ++ E)) by (eapply uniq_remove_mid; eassumption).
    destruct (x == y) as [-> | Hneq].
    + assert (Hbind : binds y U (F ++ (y ~ U) ++ E)).
      { apply binds_app_r, binds_app_l, binds_one; reflexivity. }
      assert (T = U) by (eapply binds_unique; eassumption).
      subst T. auto using typing_weaken_head.
    + apply typing_var; [assumption | eapply binds_remove_mid; eassumption].
  - apply typing_abs with (L := L `union` singleton y).
    intros x Hfresh.
    assert (Hneq : x <> y) by (intro Heq; subst x; fsetdec).
    unfold open_trm_wrt_trm.
    replace (t_var_f x) with (subst_fvar y v (t_var_f x)) by (simpl; destruct (x == y); congruence).
    rewrite <- (subst_fvar_open_rec s 0 y v (t_var_f x)) by (eauto using typing_scoped).
    change (typing ((x ~ V) ++ F ++ E) (subst_fvar y v (open_trm_wrt_trm s (t_var_f x))) T).
    match goal with
    | IH : forall x, x `notin` L -> forall _ _ _ _ _, _ -> _ -> _ |- _ =>
        exact (IH x ltac:(solve_notin) ((x ~ V) ++ F) y U E v eq_refl Hv)
    end.
Qed.

Lemma typing_open : forall L G V s T v,
  (forall x, x `notin` L -> typing ((x ~ V) ++ G) (open_trm_wrt_trm s (t_var_f x)) T) ->
  typing G v V -> typing G (open_trm_wrt_trm s v) T.
Proof.
  intros L G V s T v Hbody Hv.
  destruct (atom_fresh (L `union` trm_fv s)) as [x Hfresh].
  rewrite <- (subst_fvar_intro s x v) by (solve [solve_notin | eauto using typing_scoped]).
  exact (typing_subst _ _ _ (Hbody x ltac:(solve_notin)) nil x V G v eq_refl Hv).
Qed.

Lemma typing_norm : forall v w,
  norm v w -> forall G M V T,
  typing G v (typ_mod_arrow M V T) ->
  typing G w (typ_mod_arrow mod_non_nullable V T).
Proof.
  intros v w Hnorm. induction Hnorm; intros G M A B Htyping;
    inversion Htyping; subst.
  - exact Htyping.
  - match goal with
    | H : compat _ _ |- _ => inversion H; subst
    end.
    eauto using typing, compat.
Qed.

Lemma step_preserves_typing : forall t r,
  step t r -> forall G T, typing G t T ->
  match r with
  | r_term u => typing G u T
  | r_blame _ => True
  end.
Proof.
  intros t r Hstep. induction Hstep; intros G R Htyping; simpl; try exact I;
    inversion Htyping; subst; eauto using typing.
  - match goal with
    | H : typing _ (t_abs _ _) _ |- _ => inversion H; subst
    end.
    eauto using typing_open.
  - eapply typing_app; [eapply typing_norm; eassumption | discriminate | eassumption].
  - match goal with
    | H : typing _ (t_cast _ _ _ _) _ |- _ => inversion H; subst
    end.
    match goal with
    | H : compat _ _ |- _ => inversion H; subst
    end.
    eapply typing_cast; [ | eassumption].
    eapply typing_app; [eassumption | discriminate | eauto using typing_cast].
  - eapply typing_app; [eapply typing_norm; eassumption | discriminate | eassumption].
Qed.

Theorem preservation : forall G t r T,
  typing G t T ->
  step t r ->
  (exists p, r = r_blame p) \/
  (exists u, r = r_term u /\ typing G u T).
Proof.
  intros G t [u | p] T Htyping Hstep.
  - right. exists u. split; [reflexivity | exact (step_preserves_typing _ _ Hstep _ _ Htyping)].
  - left. exists p. reflexivity.
Qed.

Lemma value_cases : forall v,
  lc_trm v -> Is_true (is_val_of_trm v) -> isnull v \/ isabs v.
Proof.
  intros v Hlc. induction Hlc; simpl; intros Hval; try contradiction.
  - left. constructor.
  - right. constructor. now constructor.
  - destruct (IHHlc Hval); eauto using isnull, isabs.
Qed.

Lemma neglabel_exists : forall p, exists q, neglabel p q.
Proof.
  destruct p; eauto using neglabel.
Qed.

Lemma typed_abs_norm : forall v,
  isabs v -> forall G T, typing G v T ->
  exists M A B w, T = typ_mod_arrow M A B /\ norm v w.
Proof.
  intros v Habs. induction Habs; intros G R Htyping; inversion Htyping; subst.
  - do 4 eexists. split; [reflexivity | constructor; eassumption].
  - match goal with
    | Hsource : typing _ v _ |- _ =>
        destruct (IHHabs _ _ Hsource) as (M & A & B & w & -> & Hnorm)
    end.
    match goal with
    | H : compat _ _ |- _ => inversion H; subst
    end.
    do 4 eexists. split; [reflexivity | constructor; eassumption].
Qed.

Lemma norm_value : forall v w, norm v w -> Is_true (is_val_of_trm w).
Proof.
  intros v w Hnorm. induction Hnorm; simpl; auto.
Qed.

Lemma typed_null_unwrap : forall v,
  isnull v -> forall G M A B,
  typing G v (typ_mod_arrow M A B) -> M <> mod_safe ->
  exists p, unwrap v p.
Proof.
  intros v Hnull. induction Hnull; intros G M A B Htyping Hnot_safe;
    inversion Htyping; subst.
  match goal with
  | H : compat _ _ |- _ =>
      inversion H as [| N C D Hnonnull | N C D N' C' D' Hdom Hcod]; subst
  end.
  - destruct M; try contradiction.
    destruct (neglabel_exists p) as [q Hneg].
    exists q. eauto using unwrap, typing_lc.
  - destruct N.
    + destruct M; try contradiction.
      * destruct (IHHnull G mod_unsafe C D) as [q Hwrap]; [assumption | discriminate |].
        exists q. now apply unwrap_bang_bang.
      * eauto using unwrap_bang_hash, typing_lc.
    + destruct M; try contradiction.
      * destruct (neglabel_exists p) as [q Hneg].
        exists q. eauto using unwrap_question_bang, typing_lc.
      * eauto using unwrap_question_hash, typing_lc.
    + destruct (IHHnull G mod_non_nullable C D) as [q Hwrap]; [assumption | discriminate |].
      exists q. now apply unwrap_hash.
Qed.

Theorem progress : forall t T,
  typing nil t T ->
  (exists u, step t u) \/ Is_true (is_val_of_trm t).
Proof.
  intros t T Htyping.
  remember (nil : ctx) as G eqn:HG.
  induction Htyping; subst G.
  - match goal with H : binds _ _ nil |- _ => inversion H end.
  - right. exact I.
  - right. exact I.
  - left. destruct (IHHtyping1 eq_refl) as [[r Hstep] | Hs].
    + destruct r; eauto using step_app_ctxL, step_app_errL, typing_lc.
    + destruct (IHHtyping2 eq_refl) as [[r Hstep] | Ht].
      * destruct r; eauto using step_app_ctxR, step_app_errR, typing_lc.
      * assert (Hlc : lc_trm s) by eauto using typing_lc.
        destruct (value_cases s Hlc Hs) as [Hnull | Habs].
        -- destruct (typed_null_unwrap _ Hnull _ _ _ _ Htyping1 H) as [p Hwrap].
           exists (r_blame p). eauto using step_app_fail, typing_lc.
        -- destruct (typed_abs_norm _ Habs _ _ Htyping1) as (N & A & B & w & _ & Hnorm).
           exists (r_term (t_app w t)). eauto using step_app_norm, norm_value, typing_lc.
  - left. destruct (IHHtyping1 eq_refl) as [[r Hstep] | Hf].
    + destruct r; eauto using step_safe_app_ctxL, step_safe_app_errL, typing_lc.
    + assert (Hlc : lc_trm f) by eauto using typing_lc.
      destruct (value_cases f Hlc Hf) as [Hnull | Habs].
      * exists (r_term t). eauto using step_safe_app_null, typing_lc.
      * destruct (typed_abs_norm _ Habs _ _ Htyping1) as (N & A & B & w & _ & Hnorm).
        exists (r_term (t_app w s)). eauto using step_safe_app_norm, norm_value, typing_lc.
  - destruct (IHHtyping eq_refl) as [[r Hstep] | Hval].
    + left. destruct r; eauto using step_cast_ctx, step_cast_err.
    + right. exact Hval.
Qed.
