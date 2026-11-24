Require Import erasure.

Require Import Program.Equality.

Require Import Metalib.Metatheory.

Require Import Lia.

Require Import Relation_Operators.

Require Import Operators_Properties.

Definition terminate (e:exp) : Prop :=
  exists v, value v /\ e ==>* v.

Definition diverge (e:exp) : Prop :=
  ~ (exists v, value v /\ e ==>* v).

(* Opening removes one slot from a de Bruijn context. *)
Local Lemma behavior_lookup_before {X : Type} (P S : list X) a i :
  i < length P -> nth_error (P ++ a :: S) i = nth_error (P ++ S) i.
Proof.
  intro H. now rewrite !nth_error_app1.
Qed.

Local Lemma behavior_lookup_at {X : Type} (P S : list X) a :
  nth_error (P ++ a :: S) (length P) = Some a.
Proof.
  rewrite nth_error_app2 by lia. now rewrite Nat.sub_diag.
Qed.

Local Lemma behavior_lookup_after {X : Type} (P S : list X) a i :
  length P < i -> nth_error (P ++ a :: S) i = nth_error (P ++ S) (i - 1).
Proof.
  intro H. rewrite !nth_error_app2 by lia.
  replace (i - length P) with (Datatypes.S (i - 1 - length P)) by lia.
  reflexivity.
Qed.

Local Lemma behavior_lookup_lt {X : Type} (D : list X) i a :
  nth_error D i = Some a -> i < length D.
Proof.
  intro H. apply Nat.lt_nge. intro Hge. apply nth_error_None in Hge. congruence.
Qed.

Local Lemma behavior_lookup_weaken {X : Type} (P S : list X) i a :
  nth_error P i = Some a -> nth_error (P ++ S) i = Some a.
Proof.
  intro H. rewrite nth_error_app1; [exact H |].
  exact (behavior_lookup_lt P i a H).
Qed.

Fixpoint behavior_type_scope (n : nat) (A : typ) : Prop :=
  match A with
  | t_var_b i => i < n
  | t_arrow B C => behavior_type_scope n B /\ behavior_type_scope n C
  | t_mu B => behavior_type_scope (S n) B
  | _ => True
  end.

Local Lemma behavior_type_open A k X :
  behavior_type_scope k (open_typ_wrt_typ_rec k (t_var_f X) A) <->
  behavior_type_scope (S k) A.
Proof.
  revert k. induction A; intro k; cbn; try tauto.
  - destruct (lt_eq_lt_dec n k) as [[H | H] | H]; cbn; lia.
  - rewrite IHA1, IHA2. reflexivity.
  - apply IHA.
Qed.

Local Lemma behavior_type_size_open A k X :
  size_typ (open_typ_wrt_typ_rec k (t_var_f X) A) = size_typ A.
Proof.
  revert k. induction A; intro k; cbn; try reflexivity.
  - destruct (lt_eq_lt_dec n k) as [[] |]; reflexivity.
  - now rewrite IHA1, IHA2.
  - now rewrite IHA.
Qed.

Local Lemma behavior_wft_scope D A : WFT D A -> behavior_type_scope 0 A.
Proof.
  induction 1; cbn; try tauto.
  pick fresh X for L.
  apply (behavior_type_open A 0 X). eauto.
Qed.

Local Lemma behavior_type_lc A : behavior_type_scope 0 A -> lc_typ A.
Proof.
  remember (size_typ A) as n eqn:Hn.
  revert A Hn. induction n using lt_wf_ind; intros A Hn Hscope.
  destruct A; cbn in Hscope, Hn.
  - lia.
  - constructor.
  - constructor.
  - destruct Hscope. constructor; eapply H; eauto; lia.
  - constructor. intro X.
    unfold open_typ_wrt_typ.
    eapply (H (size_typ (open_typ_wrt_typ_rec 0 (t_var_f X) A))).
    + rewrite behavior_type_size_open. lia.
    + reflexivity.
    + now apply behavior_type_open.
Qed.

Local Lemma behavior_wft_lc D A : WFT D A -> lc_typ A.
Proof.
  intro H. apply behavior_type_lc. now apply behavior_wft_scope in H.
Qed.

(* Keep the cast types used by the operational rules, with an indexed
   context for the variables bound by recursive casts. *)
Inductive behavior_cast : cctx -> actx -> castop -> typ -> typ -> Prop :=
| BC_bound : forall E D i A B,
    nth_error D i = Some (A, B) -> behavior_cast E D (c_var_b i) A B
| BC_free : forall E D x A B,
    In (x, (A, B)) E -> behavior_cast E D (c_var_f x) A B
| BC_id : forall E D A, behavior_cast E D c_id A A
| BC_unfold : forall E D A,
    lc_typ (t_mu A) -> behavior_cast E D (c_unfold (t_mu A)) (t_mu A) (unfold_mu A)
| BC_fold : forall E D A,
    lc_typ (t_mu A) -> behavior_cast E D (c_fold (t_mu A)) (unfold_mu A) (t_mu A)
| BC_arrow : forall E D c d A B C F,
    behavior_cast E D c A B -> behavior_cast E D d C F ->
    behavior_cast E D (c_arrow c d) (t_arrow A C) (t_arrow B F)
| BC_seq : forall E D c d A B C,
    behavior_cast E D c A B -> behavior_cast E D d B C ->
    behavior_cast E D (c_seq c d) A C
| BC_fix : forall E D c d A B C F,
    behavior_cast E ((t_arrow A C, t_arrow B F) :: D) c A B ->
    behavior_cast E ((t_arrow A C, t_arrow B F) :: D) d C F ->
    behavior_cast E D (c_fixc (c_arrow c d)) (t_arrow A C) (t_arrow B F).

#[local] Hint Constructors behavior_cast : behavior.

Local Lemma behavior_cast_close c E P S x T A B :
  x \notin dom E -> x \notin castfv_castop c ->
  behavior_cast ((x, T) :: E) (P ++ S)
    (open_castop_wrt_castop_rec (length P) (c_var_f x) c) A B ->
  behavior_cast E (P ++ T :: S) c A B.
Proof.
  intro Hdom. revert P A B. induction c; intros P U V Hfresh Hc; cbn in Hc, Hfresh.
  - destruct (lt_eq_lt_dec n (length P)) as [[Hlt | Heq] | Hgt].
    + inversion Hc; subst. constructor. now rewrite behavior_lookup_before.
    + inversion Hc; subst.
      match goal with H : In _ (_ :: _) |- _ => destruct H as [Hpair | Hin] end.
      * inversion Hpair; subst. constructor. apply behavior_lookup_at.
      * exfalso. apply Hdom. eapply binds_In; exact Hin.
    + inversion Hc; subst. constructor. now rewrite behavior_lookup_after.
  - inversion Hc; subst. constructor.
    match goal with H : In _ (_ :: _) |- _ => destruct H as [Hpair | Hin] end; auto.
    inversion Hpair; subst. exfalso. fsetdec.
  - inversion Hc; subst. constructor.
  - inversion Hc; subst. now constructor.
  - inversion Hc; subst. now constructor.
  - inversion Hc; subst. constructor; [eapply IHc1 | eapply IHc2]; try fsetdec; eauto.
  - inversion Hc; subst. econstructor; [eapply IHc1 | eapply IHc2]; try fsetdec; eauto.
  - destruct c; cbn in Hc; try solve [inversion Hc].
    + destruct (lt_eq_lt_dec n (Datatypes.S (length P))) as [[] |]; inversion Hc.
    + inversion Hc; subst.
      assert (Harrow : behavior_cast E ((t_arrow A C, t_arrow B F) :: P ++ T :: S)
        (c_arrow c1 c2) (t_arrow A C) (t_arrow B F)).
      { apply (IHc ((t_arrow A C, t_arrow B F) :: P)); [exact Hfresh | now constructor]. }
      inversion Harrow; subst. now constructor.
Qed.

Local Lemma behavior_cast_typed D E A B c :
  TypCast D E A B c -> behavior_cast E nil c A B.
Proof.
  induction 1; eauto using behavior_wft_lc with behavior.
  pick fresh x for (L \u dom E \u castfv_castop c1 \u castfv_castop c2).
  apply BC_fix.
  - apply (behavior_cast_close c1 E nil nil x (t_arrow A1 B1, t_arrow A2 B2));
      try fsetdec. eauto.
  - apply (behavior_cast_close c2 E nil nil x (t_arrow A1 B1, t_arrow A2 B2));
      try fsetdec. eauto.
Qed.

Fixpoint behavior_cast_scope (n : nat) (c : castop) : Prop :=
  match c with
  | c_var_b i => i < n
  | c_unfold A | c_fold A => lc_typ A
  | c_arrow c d | c_seq c d => behavior_cast_scope n c /\ behavior_cast_scope n d
  | c_fixc c => behavior_cast_scope (S n) c
  | _ => True
  end.

Local Lemma behavior_cast_scoped E D c A B :
  behavior_cast E D c A B -> behavior_cast_scope (length D) c.
Proof.
  induction 1; cbn; eauto using behavior_lookup_lt.
Qed.

Local Lemma behavior_cast_open_scope c k x :
  behavior_cast_scope k (open_castop_wrt_castop_rec k (c_var_f x) c) <->
  behavior_cast_scope (S k) c.
Proof.
  revert k. induction c; intro k; cbn; try tauto.
  - destruct (lt_eq_lt_dec n k) as [[H | H] | H]; cbn; lia.
  - now rewrite IHc1, IHc2.
  - now rewrite IHc1, IHc2.
  - apply IHc.
Qed.

Local Lemma behavior_cast_size_open c k x :
  size_castop (open_castop_wrt_castop_rec k (c_var_f x) c) = size_castop c.
Proof.
  revert k. induction c; intro k; cbn; try reflexivity.
  - destruct (lt_eq_lt_dec n k) as [[] |]; reflexivity.
  - now rewrite IHc1, IHc2.
  - now rewrite IHc1, IHc2.
  - now rewrite IHc.
Qed.

Local Lemma behavior_cast_lc_scope c : behavior_cast_scope 0 c -> lc_castop c.
Proof.
  remember (size_castop c) as n eqn:Hn.
  revert c Hn. induction n using lt_wf_ind; intros c Hn Hscope.
  destruct c; cbn in Hscope, Hn.
  - lia.
  - constructor.
  - constructor.
  - now constructor.
  - now constructor.
  - destruct Hscope. constructor; eapply H; eauto; lia.
  - destruct Hscope. constructor; eapply H; eauto; lia.
  - constructor. intro x. unfold open_castop_wrt_castop.
    eapply (H (size_castop (open_castop_wrt_castop_rec 0 (c_var_f x) c))).
    + rewrite behavior_cast_size_open. lia.
    + reflexivity.
    + now apply behavior_cast_open_scope.
Qed.

Local Lemma behavior_cast_lc E c A B :
  behavior_cast E nil c A B -> lc_castop c.
Proof.
  intro H. apply behavior_cast_lc_scope. now apply behavior_cast_scoped in H.
Qed.

Local Lemma behavior_cast_weaken E D c A B :
  behavior_cast E D c A B -> forall S, behavior_cast E (D ++ S) c A B.
Proof.
  induction 1; intro S; cbn; eauto using behavior_lookup_weaken with behavior.
Qed.

Local Lemma behavior_cast_open E D c A B :
  behavior_cast E D c A B ->
  forall P S U V u, D = P ++ (U, V) :: S ->
  behavior_cast E nil u U V ->
  behavior_cast E (P ++ S) (open_castop_wrt_castop_rec (length P) u c) A B.
Proof.
  induction 1; intros P S U V u HD Hu; subst D; cbn.
  - destruct (lt_eq_lt_dec i (length P)) as [[Hlt | Heq] | Hgt].
    + constructor. now rewrite <- (behavior_lookup_before P S (U, V)).
    + subst i. rewrite behavior_lookup_at in H. injection H as <- <-.
      exact (behavior_cast_weaken _ _ _ _ _ Hu (P ++ S)).
    + constructor. now rewrite <- (behavior_lookup_after P S (U, V)).
  - now constructor.
  - constructor.
  - now constructor.
  - now constructor.
  - constructor; eauto.
  - econstructor; eauto.
  - constructor.
    + exact (IHbehavior_cast1 ((t_arrow A C, t_arrow B F) :: P) S U V u eq_refl Hu).
    + exact (IHbehavior_cast2 ((t_arrow A C, t_arrow B F) :: P) S U V u eq_refl Hu).
Qed.

Local Lemma behavior_cast_rev E D c A B :
  behavior_cast E D c A B ->
  behavior_cast (List.map (fun '(x, (U, V)) => (x, (V, U))) E)
    (List.map (fun '(U, V) => (V, U)) D) (rev_cast c) B A.
Proof.
  induction 1; cbn; eauto with behavior.
  - constructor. now rewrite nth_error_map, H.
  - constructor. exact (in_map (fun '(x, (U, V)) => (x, (V, U))) _ _ H).
Qed.

(* Retain the types and closure conditions needed to simulate a reduction
   after erasure. Bound term variables use the indexed context. *)
Inductive behavior_typing : ctx -> list typ -> exp -> typ -> Prop :=
| BT_bound : forall G D i A,
    nth_error D i = Some A -> behavior_typing G D (e_var_b i) A
| BT_free : forall G D x A,
    binds x A G -> behavior_typing G D (e_var_f x) A
| BT_lit : forall G D i, behavior_typing G D (e_lit i) t_int
| BT_abs : forall G D A e B,
    lc_typ A -> behavior_typing G (A :: D) e B ->
    behavior_typing G D (e_abs A e) (t_arrow A B)
| BT_app : forall G D f e A B,
    behavior_typing G D f (t_arrow A B) -> behavior_typing G D e A ->
    behavior_typing G D (e_app f e) B
| BT_cast : forall G D c e A B,
    behavior_typing G D e A -> behavior_cast nil nil c A B ->
    behavior_typing G D (e_cast c e) B.

#[local] Hint Constructors behavior_typing : behavior.

Local Lemma behavior_expr_close e G P S x A B :
  x \notin dom G -> x \notin termfv_exp e ->
  behavior_typing ((x, A) :: G) (P ++ S)
    (open_exp_wrt_exp_rec (length P) (e_var_f x) e) B ->
  behavior_typing G (P ++ A :: S) e B.
Proof.
  intro Hdom. revert P B. induction e; intros P B Hfresh He; cbn in He, Hfresh.
  - destruct (lt_eq_lt_dec n (length P)) as [[Hlt | Heq] | Hgt].
    + inversion He; subst. constructor. now rewrite behavior_lookup_before.
    + inversion He; subst.
      unfold binds in *.
      match goal with H : In _ (_ :: _) |- _ => destruct H as [Hpair | Hin] end.
      * inversion Hpair; subst. constructor. apply behavior_lookup_at.
      * exfalso. apply Hdom. eapply binds_In; exact Hin.
    + inversion He; subst. constructor. now rewrite behavior_lookup_after.
  - inversion He; subst. constructor.
    unfold binds in *.
    match goal with H : In _ (_ :: _) |- _ => destruct H as [Hpair | Hin] end.
    + inversion Hpair; subst. exfalso. fsetdec.
    + exact Hin.
  - inversion He; subst; constructor.
  - inversion He; subst. constructor; [assumption |].
    apply (IHe (t :: P)); assumption.
  - inversion He; subst. econstructor; [eapply IHe1 | eapply IHe2]; try fsetdec; eauto.
  - inversion He; subst. econstructor; eauto.
Qed.

Local Lemma behavior_expr_weaken G D e A :
  behavior_typing G D e A -> forall S, behavior_typing G (D ++ S) e A.
Proof.
  induction 1; intro S; cbn; eauto using behavior_lookup_weaken with behavior.
Qed.

Local Lemma behavior_expr_open G D e A :
  behavior_typing G D e A ->
  forall P S U u, D = P ++ U :: S ->
  behavior_typing G nil u U ->
  behavior_typing G (P ++ S) (open_exp_wrt_exp_rec (length P) u e) A.
Proof.
  induction 1; intros P S U u HD Hu; subst D; cbn.
  - destruct (lt_eq_lt_dec i (length P)) as [[Hlt | Heq] | Hgt].
    + constructor. now rewrite <- (behavior_lookup_before P S U).
    + subst i. rewrite behavior_lookup_at in H. injection H as <-.
      exact (behavior_expr_weaken _ _ _ _ Hu (P ++ S)).
    + constructor. now rewrite <- (behavior_lookup_after P S U).
  - now constructor.
  - constructor.
  - constructor; [assumption | exact (IHbehavior_typing (A :: P) S U u eq_refl Hu)].
  - econstructor; eauto.
  - econstructor; eauto.
Qed.

Fixpoint behavior_expr_scope (n : nat) (e : exp) : Prop :=
  match e with
  | e_var_b i => i < n
  | e_abs A e => lc_typ A /\ behavior_expr_scope (S n) e
  | e_app f e => behavior_expr_scope n f /\ behavior_expr_scope n e
  | e_cast c e => lc_castop c /\ behavior_expr_scope n e
  | _ => True
  end.

Local Lemma behavior_expr_scoped G D e A :
  behavior_typing G D e A -> behavior_expr_scope (length D) e.
Proof.
  induction 1; cbn; eauto using behavior_lookup_lt, behavior_cast_lc.
Qed.

Local Lemma behavior_expr_open_scope e k x :
  behavior_expr_scope k (open_exp_wrt_exp_rec k (e_var_f x) e) <->
  behavior_expr_scope (S k) e.
Proof.
  revert k. induction e; intro k; cbn; try tauto.
  - destruct (lt_eq_lt_dec n k) as [[H | H] | H]; cbn; lia.
  - now rewrite IHe.
  - now rewrite IHe1, IHe2.
  - now rewrite IHe.
Qed.

Local Lemma behavior_expr_size_open e k x :
  size_exp (open_exp_wrt_exp_rec k (e_var_f x) e) = size_exp e.
Proof.
  revert k. induction e; intro k; cbn; try reflexivity.
  - destruct (lt_eq_lt_dec n k) as [[] |]; reflexivity.
  - now rewrite IHe.
  - now rewrite IHe1, IHe2.
  - now rewrite IHe.
Qed.

Local Lemma behavior_expr_lc_scope e : behavior_expr_scope 0 e -> lc_exp e.
Proof.
  remember (size_exp e) as n eqn:Hn.
  revert e Hn. induction n using lt_wf_ind; intros e Hn Hscope.
  destruct e; cbn in Hscope, Hn.
  - lia.
  - constructor.
  - constructor.
  - destruct Hscope. constructor; [assumption |]. intro x. unfold open_exp_wrt_exp.
    eapply (H (size_exp (open_exp_wrt_exp_rec 0 (e_var_f x) e))).
    + rewrite behavior_expr_size_open. lia.
    + reflexivity.
    + now apply behavior_expr_open_scope.
  - destruct Hscope. constructor; eapply H; eauto; lia.
  - destruct Hscope. constructor; auto. eapply H; eauto; lia.
Qed.

Local Lemma behavior_expr_lc G e A : behavior_typing G nil e A -> lc_exp e.
Proof.
  intro H. apply behavior_expr_lc_scope. now apply behavior_expr_scoped in H.
Qed.

Local Lemma behavior_elaboration_context G e A e' :
  EquiTypingC G e A e' -> WFTmE G.
Proof.
  induction 1; auto.
  pick fresh x for L. specialize (H0 x ltac:(fsetdec)).
  now inversion H0.
Qed.

Local Lemma behavior_elaboration_typing G e A e' :
  EquiTypingC G e A e' -> behavior_typing G nil e' A.
Proof.
  induction 1; eauto using behavior_cast_typed with behavior.
  pick fresh x for (L \u dom G \u termfv_exp e').
  apply BT_abs.
  - pose proof (behavior_elaboration_context _ _ _ _ (H x ltac:(fsetdec))) as Hctx.
    inversion Hctx; subst. eauto using behavior_wft_lc.
  - apply (behavior_expr_close e' G nil nil x A1); try fsetdec. eauto.
Qed.

Local Lemma behavior_erase_open e u k :
  erase (open_exp_wrt_exp_rec k u e) =
  open_exp_wrt_exp_rec k (erase u) (erase e).
Proof.
  revert k. induction e; intro k; cbn; try reflexivity.
  - destruct (lt_eq_lt_dec n k) as [[] |]; reflexivity.
  - now rewrite IHe.
  - now rewrite IHe1, IHe2.
  - apply IHe.
Qed.

Local Lemma behavior_close_open e k x :
  x \notin termfv_exp e ->
  close_exp_wrt_exp_rec k x (open_exp_wrt_exp_rec k (e_var_f x) e) = e.
Proof.
  revert k. induction e; intros k Hfresh; cbn in *; try reflexivity.
  - destruct (lt_eq_lt_dec n k) as [[Hlt | Heq] | Hgt]; cbn.
    + destruct (lt_dec n k); [reflexivity | lia].
    + destruct (x === x); [now subst | contradiction].
    + destruct (lt_dec (n - 1) k); [lia | f_equal; lia].
  - destruct (x === t); [subst; exfalso; fsetdec | reflexivity].
  - now rewrite IHe.
  - rewrite IHe1, IHe2 by fsetdec. reflexivity.
  - now rewrite IHe.
Qed.

Local Lemma behavior_elaboration_erase G e A e' :
  EquiTypingC G e A e' -> erase e' = e.
Proof.
  induction 1; cbn; try congruence.
  pick fresh x for (L \u termfv_exp e \u termfv_exp (erase e')).
  assert (Hopen : open_exp_wrt_exp_rec 0 (e_var_f x) (erase e') =
                  open_exp_wrt_exp_rec 0 (e_var_f x) e).
  { change (e_var_f x) with (erase (e_var_f x)) at 1.
    rewrite <- behavior_erase_open. apply H0. fsetdec. }
  apply (f_equal (close_exp_wrt_exp_rec 0 x)) in Hopen.
  rewrite !behavior_close_open in Hopen by fsetdec. now f_equal.
Qed.

Local Lemma behavior_erase_lc e : lc_exp e -> lc_exp (erase e).
Proof.
  induction 1; cbn; eauto using lc_exp.
  constructor; [assumption |]. intro x.
  unfold open_exp_wrt_exp in *.
  change (e_var_f x) with (erase (e_var_f x)).
  rewrite <- behavior_erase_open. auto.
Qed.

Local Lemma behavior_erase_value v : value v -> value (erase v).
Proof.
  induction 1; cbn; auto using V_lit.
  apply V_abs; [assumption |].
  match goal with H : lc_exp (e_abs _ _) |- _ => exact (behavior_erase_lc _ H) end.
Qed.

Local Lemma behavior_erase_no_cast e c v : erase e <> e_cast c v.
Proof.
  induction e; cbn; congruence.
Qed.

#[local] Hint Constructors Reduction clos_refl_trans : behavior.

Local Lemma behavior_steps_appl f f' e :
  lc_exp e -> f ==>* f' -> e_app f e ==>* e_app f' e.
Proof.
  intros Hlc H. induction H; eauto with behavior.
Qed.

Local Lemma behavior_steps_appr f e e' :
  value f -> e ==>* e' -> e_app f e ==>* e_app f e'.
Proof.
  intros Hv H. induction H; eauto with behavior.
Qed.

Local Lemma behavior_steps_cast c e e' :
  lc_castop c -> e ==>* e' -> e_cast c e ==>* e_cast c e'.
Proof.
  intros Hlc H. induction H; eauto with behavior.
Qed.

Local Lemma behavior_erase_step e e' :
  Reduction e e' -> erase e ==>* erase e'.
Proof.
  induction 1; cbn; try apply rt_refl; try assumption.
  - unfold open_exp_wrt_exp. rewrite behavior_erase_open.
    apply rt_step, Red_beta.
    + assumption.
    + change (lc_exp (erase (e_abs A e))). now apply behavior_erase_lc.
    + now apply behavior_erase_value.
  - apply behavior_steps_appl; auto using behavior_erase_lc.
  - apply behavior_steps_appr; auto using behavior_erase_value.
Qed.

Local Lemma behavior_erase_steps e e' :
  e ==>* e' -> erase e ==>* erase e'.
Proof.
  induction 1; eauto using behavior_erase_step with behavior.
Qed.

(* A recursive cast unfolds directly to an arrow cast, which is already
   a value when its operand is a value. Sequence casts may normalize both
   components, and an unfold cast eliminates a matching fold. *)
Local Lemma behavior_cast_value E D c A B :
  behavior_cast E D c A B ->
  E = nil -> D = nil ->
  forall v, value v -> behavior_typing nil nil v A ->
  exists w, e_cast c v ==>* w /\ value w /\
    behavior_typing nil nil w B /\ erase w = erase v.
Proof.
  induction 1; intros HE HD v Hv Hty; subst E D.
  - destruct i; discriminate.
  - contradiction.
  - exists v. repeat apply conj; eauto with behavior.
  - inversion Hv; subst; inversion Hty; subst;
      match goal with H : behavior_cast _ _ _ _ (t_mu _) |- _ =>
        inversion H; subst
      end.
    exists e. cbn. repeat apply conj; eauto with behavior.
  - exists (e_cast (c_fold (t_mu A)) v). cbn.
    repeat apply conj; eauto using V_fold with behavior.
  - exists (e_cast (c_arrow c d) v). cbn.
    repeat apply conj; eauto using V_arrow, behavior_cast_lc with behavior.
  - destruct (IHbehavior_cast1 eq_refl eq_refl v Hv Hty) as (u & Hvu & Hu & Htu & Heu).
    destruct (IHbehavior_cast2 eq_refl eq_refl u Hu Htu) as (w & Huw & Hw & Htw & Hew).
    exists w. repeat split; auto.
    + eapply rt_trans.
      * apply rt_step. apply Red_cast_seq; eauto using behavior_cast_lc.
      * eapply rt_trans; [apply behavior_steps_cast; eauto using behavior_cast_lc | exact Huw].
    + now rewrite Hew, Heu.
  - set (fixcast := c_fixc (c_arrow c d)).
    assert (Hfix : behavior_cast nil nil fixcast (t_arrow A C) (t_arrow B F))
      by (unfold fixcast; now constructor).
    assert (Hc : behavior_cast nil nil (open_castop_wrt_castop c fixcast) A B).
    { exact (behavior_cast_open nil _ c A B H nil nil
        (t_arrow A C) (t_arrow B F) fixcast eq_refl Hfix). }
    assert (Hd : behavior_cast nil nil (open_castop_wrt_castop d fixcast) C F).
    { exact (behavior_cast_open nil _ d C F H0 nil nil
        (t_arrow A C) (t_arrow B F) fixcast eq_refl Hfix). }
    exists (e_cast (c_arrow (open_castop_wrt_castop c fixcast)
                           (open_castop_wrt_castop d fixcast)) v).
    cbn [erase]. repeat apply conj.
    + apply rt_step. apply Red_castfix; eauto using behavior_cast_lc.
    + apply V_arrow; eauto using behavior_cast_lc.
    + eauto with behavior.
    + reflexivity.
Qed.

Local Lemma behavior_lift_value e A :
  behavior_typing nil nil e A -> value (erase e) ->
  exists v, e ==>* v /\ value v /\
    behavior_typing nil nil v A /\ erase v = erase e.
Proof.
  revert A. induction e; intros A Hty Hv; cbn in Hv; try solve [inversion Hv].
  - exists (e_lit i). repeat apply conj; eauto using V_lit with behavior.
  - exists (e_abs t e). inversion Hty; subst.
    repeat apply conj; eauto using V_abs, behavior_expr_lc with behavior.
  - inversion Hty as [| | | | | ? ? ? ? ? ? Hinner Hcast]; subst.
    destruct (IHe _ Hinner Hv) as (v & Hev & Hval & Htv & Her).
    destruct (behavior_cast_value _ _ _ _ _ Hcast eq_refl eq_refl v Hval Htv)
      as (w & Hvw & Hw & Htw & Hew).
    exists w. repeat split; eauto.
    + eapply rt_trans; [apply behavior_steps_cast; eauto using behavior_cast_lc | exact Hvw].
    + cbn. now rewrite Hew, Her.
Qed.

(* To simulate a beta step through an arrow cast, normalize its argument
   cast and recurse on the underlying function value. The result cast
   can stay around the beta reduct. *)
Local Lemma behavior_lift_beta f :
  value f ->
  forall T b A B v, behavior_typing nil nil f (t_arrow A B) ->
  erase f = e_abs T b -> value v -> behavior_typing nil nil v A ->
  exists w, e_app f v ==>* w /\ behavior_typing nil nil w B /\
    erase w = open_exp_wrt_exp b (erase v).
Proof.
  induction 1 as [i | U body Hlc Habs | U f Hlc Hval IH |
                  c d f Hlc1 Hlc2 Hval IH];
    intros T b A B v Htf Hef Hv Htv.
  - discriminate.
  - cbn in Hef. inversion Hef; subst.
    inversion Htf; subst.
    exists (open_exp_wrt_exp body v). repeat split.
    + apply rt_step. now constructor.
    + match goal with H : behavior_typing nil (?X :: nil) ?e ?Y |- _ =>
        exact (behavior_expr_open nil (X :: nil) e Y H nil nil X v eq_refl Htv)
      end.
    + apply behavior_erase_open.
  - inversion Htf; subst.
    match goal with H : behavior_cast _ _ (c_fold _) _ _ |- _ => inversion H end.
  - inversion Htf as [| | | | | ? ? ? ? ? ? Hunder Hcast]; subst.
    inversion Hcast as [| | | | | ? ? ? ? ? ? ? ? Hcontra Hco | |]; subst.
    pose proof (behavior_cast_rev _ _ _ _ _ Hcontra) as Hrev. cbn in Hrev.
    destruct (behavior_cast_value _ _ _ _ _ Hrev eq_refl eq_refl v Hv Htv)
      as (u & Hvu & Hu & Htu & Heu).
    destruct (IH T b _ _ u Hunder Hef Hu Htu) as (w & Hstep & Htw & Hew).
    exists (e_cast d w). repeat split.
    + eapply rt_trans; [apply rt_step; now apply Red_cast_arr |].
      apply behavior_steps_cast; [exact Hlc2 |].
      eapply rt_trans with (y := e_app f u).
      * exact (behavior_steps_appr f _ _ Hval Hvu).
      * exact Hstep.
    + eauto with behavior.
    + cbn. now rewrite Hew, Heu.
Qed.

Local Lemma behavior_app_step f a p :
  Reduction (e_app f a) p ->
  (exists T b, f = e_abs T b /\ value f /\ value a /\ p = open_exp_wrt_exp b a) \/
  (exists f', Reduction f f' /\ p = e_app f' a) \/
  (value f /\ exists a', Reduction a a' /\ p = e_app f a') \/
  (exists c d g, f = e_cast (c_arrow c d) g).
Proof.
  inversion 1; subst; eauto 9 using V_abs.
Qed.

Local Lemma behavior_lift_step e A p :
  behavior_typing nil nil e A -> Reduction (erase e) p ->
  exists w, e ==>* w /\ behavior_typing nil nil w A /\ erase w = p.
Proof.
  revert A p. induction e; intros A p Hty Hred; cbn in Hred;
    try solve [inversion Hred].
  - inversion Hty as [| | | | ? ? ? ? X ? Hfun Harg |]; subst.
    destruct (behavior_app_step _ _ _ Hred) as
      [(T & b & Hef & Hvf & Hva & ->) |
       [(f' & Hf & ->) | [(Hvf & a' & Ha & ->) | (c & d & g & Hcast)]]].
    + destruct (behavior_lift_value _ _ Hfun Hvf) as (f & Hff & Hvf' & Htf & Herf).
      destruct (behavior_lift_value _ _ Harg Hva) as (a & Haa & Hva' & Hta & Hera).
      destruct (behavior_lift_beta f Hvf' T b X A a Htf
        (eq_trans Herf Hef) Hva' Hta) as (w & Hbeta & Htw & Herw).
      exists w. repeat split; auto.
      * eapply rt_trans with (y := e_app f e2).
        -- apply behavior_steps_appl; eauto using behavior_expr_lc.
        -- eapply rt_trans with (y := e_app f a).
           ++ exact (behavior_steps_appr f _ _ Hvf' Haa).
           ++ exact Hbeta.
      * now rewrite Herw, Hera.
    + destruct (IHe1 _ _ Hfun Hf) as (w & Hww & Htw & Her).
      exists (e_app w e2). repeat apply conj.
      * apply behavior_steps_appl; eauto using behavior_expr_lc.
      * eauto with behavior.
      * cbn. now rewrite Her.
    + destruct (behavior_lift_value _ _ Hfun Hvf) as (f & Hff & Hvf' & Htf & Herf).
      destruct (IHe2 _ _ Harg Ha) as (a & Haa & Hta & Hera).
      exists (e_app f a). repeat apply conj.
      * eapply rt_trans with (y := e_app f e2).
        -- apply behavior_steps_appl; eauto using behavior_expr_lc.
        -- exact (behavior_steps_appr f _ _ Hvf' Haa).
      * eauto with behavior.
      * cbn. now rewrite Herf, Hera.
    + exfalso. eapply behavior_erase_no_cast. exact Hcast.
  - inversion Hty as [| | | | | ? ? ? ? ? ? Hinner Hcast]; subst.
    destruct (IHe _ _ Hinner Hred) as (w & Hew & Htw & Her).
    exists (e_cast c w). repeat apply conj.
    + apply behavior_steps_cast; eauto using behavior_cast_lc.
    + eauto with behavior.
    + exact Her.
Qed.

Local Lemma behavior_lift_steps p q :
  p ==>* q ->
  forall e A, behavior_typing nil nil e A -> erase e = p ->
  exists w, e ==>* w /\ behavior_typing nil nil w A /\ erase w = q.
Proof.
  induction 1; intros e A Hty Her.
  - subst x. eauto using behavior_lift_step.
  - exists e. eauto with behavior.
  - destruct (IHclos_refl_trans1 _ _ Hty Her) as (v & Hev & Htv & Herv).
    destruct (IHclos_refl_trans2 _ _ Htv Herv) as (w & Hvw & Htw & Herw).
    exists w. eauto with behavior.
Qed.

Theorem behavior_equiv: forall e t e',
  EquiTypingC nil e t e' ->
  (terminate e <-> terminate e') /\
  (diverge e <-> diverge e').
Proof.
  intros e t e' Helab.
  pose proof (behavior_elaboration_erase _ _ _ _ Helab) as Her.
  pose proof (behavior_elaboration_typing _ _ _ _ Helab) as Hty.
  assert (Hterm : terminate e <-> terminate e').
  { split.
    - intros (v & Hv & Hsteps).
      destruct (behavior_lift_steps _ _ Hsteps _ _ Hty Her) as
        (w & Hew & Htw & Herw).
      destruct (behavior_lift_value _ _ Htw) as (u & Hwu & Hu & _).
      { now rewrite Herw. }
      exists u. split; eauto with behavior.
    - intros (v & Hv & Hsteps).
      exists (erase v). split; [now apply behavior_erase_value |].
      rewrite <- Her. now apply behavior_erase_steps. }
  split; [exact Hterm |].
  change (~ terminate e <-> ~ terminate e').
  tauto.
Qed.
