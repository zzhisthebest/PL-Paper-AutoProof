Require Import Qual.typing.

Set Implicit Arguments.
Open Scope grade_scope.

From Stdlib Require Import Lia.

(* Opening and closing remove and insert one de Bruijn index, respectively. *)
Fixpoint scoped (k : nat) (t : tm) : Prop :=
  match t with
  | a_Var_b n => (n < k)%nat
  | a_Pi _ a b | a_Abs _ a b | a_WSigma _ a b
  | a_SSigma _ a b | a_LetPair _ a b => scoped k a /\ scoped (S k) b
  | a_App a _ b | a_WPair a _ b | a_SPair a _ b
  | a_Sum a b => scoped k a /\ scoped k b
  | a_Case _ a b c => scoped k a /\ scoped k b /\ scoped k c
  | a_Inj1 a | a_Inj2 a | a_Proj1 _ a | a_Proj2 _ a => scoped k a
  | _ => True
  end.

Local Ltac indices :=
  repeat match goal with
  | |- context [lt_eq_lt_dec ?n ?k] => destruct (lt_eq_lt_dec n k) as [[?|?]|?]
  | H : context [lt_eq_lt_dec ?n ?k] |- _ =>
      destruct (lt_eq_lt_dec n k) as [[?|?]|?]
  | |- context [lt_ge_dec ?n ?k] => destruct (lt_ge_dec n k)
  | H : context [lt_ge_dec ?n ?k] |- _ => destruct (lt_ge_dec n k)
  end.

Lemma scoped_mono : forall t k j, scoped k t -> (k <= j)%nat -> scoped j t.
Proof.
  intro t; induction t; simpl; intros; intuition (eauto; try lia).
  all: eapply IHt2; eauto; lia.
Qed.

Lemma open_scoped_id : forall t k u, scoped k t -> open_tm_wrt_tm_rec k u t = t.
Proof.
  intro t; induction t; simpl; intros; intuition; try (f_equal; eauto).
  indices; try lia; reflexivity.
Qed.

Lemma scoped_open_var : forall t k x,
  scoped k (open_tm_wrt_tm_rec k (a_Var_f x) t) <-> scoped (S k) t.
Proof.
  intro t; induction t; simpl; intros; try (rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3; tauto).
  indices; simpl; lia.
Qed.

Lemma scoped_open : forall t u k, scoped (S k) t -> scoped 0 u ->
  scoped k (open_tm_wrt_tm_rec k u t).
Proof.
  intro t; induction t; simpl; intros; intuition eauto.
  indices; simpl; eauto using scoped_mono, Nat.le_0_l; lia.
Qed.

Lemma lc_scoped : forall t, lc_tm t -> scoped 0 t.
Proof.
  induction 1; simpl; intuition.
  all: match goal with H : forall x, scoped 0 (open_tm_wrt_tm ?b (a_Var_f x)) |- _ =>
    exact (proj1 (@scoped_open_var b 0 (fresh nil)) (H (fresh nil)))
  end.
Qed.


Fixpoint tm_size (t : tm) : nat :=
  S (match t with
  | a_Pi _ a b | a_Abs _ a b | a_WSigma _ a b
  | a_SSigma _ a b | a_LetPair _ a b
  | a_App a _ b | a_WPair a _ b | a_SPair a _ b
  | a_Sum a b => (tm_size a + tm_size b)%nat
  | a_Case _ a b c => (tm_size a + tm_size b + tm_size c)%nat
  | a_Inj1 a | a_Inj2 a | a_Proj1 _ a | a_Proj2 _ a => tm_size a
  | _ => 0
  end).

Lemma tm_size_open_var : forall t k x,
  tm_size (open_tm_wrt_tm_rec k (a_Var_f x) t) = tm_size t.
Proof.
  intro t; induction t; simpl; intros; rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3;
    try reflexivity; indices; reflexivity.
Qed.

Lemma scoped_lc : forall t, scoped 0 t -> lc_tm t.
Proof.
  assert (H : forall n t, (tm_size t < n)%nat -> scoped 0 t -> lc_tm t).
  { induction n as [|n IH]; intros t Hsize Hsc; [lia|].
    destruct t; simpl in *; try (exfalso; lia); constructor;
      repeat match goal with H : _ /\ _ |- _ => destruct H end;
      try solve [eapply IH; [lia|assumption]].
    all: intros x; eapply IH;
      [unfold open_tm_wrt_tm; rewrite tm_size_open_var; lia
      |apply (proj2 (scoped_open_var _ _ _)); assumption].
  }
  intros; eapply H; [apply Nat.lt_succ_diag_r|assumption].
Qed.

Lemma subst_scoped : forall t u x k, scoped 0 u -> scoped k t ->
  scoped k (subst_tm_tm u x t).
Proof.
  intro t; induction t; simpl; intros; intuition eauto.
  destruct (eq_var x x0); simpl; eauto using scoped_mono, Nat.le_0_l.
Qed.

Lemma subst_open_rec : forall t u v x k, scoped 0 u ->
  subst_tm_tm u x (open_tm_wrt_tm_rec k v t) =
  open_tm_wrt_tm_rec k (subst_tm_tm u x v) (subst_tm_tm u x t).
Proof.
  intro t; induction t; simpl; intros; try solve [f_equal; eauto].
  - indices; reflexivity.
  - destruct (eq_var x x0); simpl; auto.
    symmetry; eapply open_scoped_id; eauto using scoped_mono, Nat.le_0_l.
Qed.

Lemma subst_open : forall t u v x, lc_tm u ->
  subst_tm_tm u x (open_tm_wrt_tm t v) =
  open_tm_wrt_tm (subst_tm_tm u x t) (subst_tm_tm u x v).
Proof. intros; apply subst_open_rec; auto using lc_scoped. Qed.

Lemma subst_fresh : forall t u x, x \notin fv_tm_tm t -> subst_tm_tm u x t = t.
Proof.
  intro t; induction t; simpl; intros; try solve [f_equal; auto].
  destruct (eq_var x x0); subst; auto; fsetdec.
Qed.

Lemma open_subst_intro : forall t u x, x \notin fv_tm_tm t -> lc_tm u ->
  subst_tm_tm u x (open_tm_wrt_tm t (a_Var_f x)) = open_tm_wrt_tm t u.
Proof.
  intros t u x Hfresh Hlc; rewrite subst_open by exact Hlc.
  rewrite (@subst_fresh t u x Hfresh).
  simpl; match goal with |- context [if ?d then _ else _] => destruct d end; congruence.
Qed.

Lemma open_close_rec : forall t k x,
  open_tm_wrt_tm_rec k (a_Var_f x) (close_tm_wrt_tm_rec k x t) = t.
Proof.
  intro t; induction t; simpl; intros; try solve [f_equal; eauto].
  - indices; cbn -[lt_eq_lt_dec lt_ge_dec]; indices; try (exfalso; lia); f_equal; lia.
  - match goal with |- context [if ?d then _ else _] => destruct d end; subst;
      cbn -[lt_eq_lt_dec]; indices; try (exfalso; lia); reflexivity.
Qed.

Lemma subst_close_rec : forall t u k x y, scoped 0 u -> x <> y ->
  y \notin fv_tm_tm u ->
  subst_tm_tm u x (close_tm_wrt_tm_rec k y t) =
  close_tm_wrt_tm_rec k y (subst_tm_tm u x t).
Proof.
  assert (Hclose : forall t k y, scoped k t -> y \notin fv_tm_tm t ->
    close_tm_wrt_tm_rec k y t = t).
  { intro t; induction t; simpl; intros; intuition; try solve [f_equal; eauto].
    - indices; f_equal; lia.
    - match goal with |- context [if ?d then _ else _] => destruct d end; subst; try reflexivity; exfalso; fsetdec.
  }
  intro t; induction t; simpl; intros; try solve [f_equal; eauto].
  - indices; reflexivity.
  - repeat match goal with |- context [if ?d then _ else _] =>
      destruct d; subst; cbn
    end; try congruence.
    symmetry; apply Hclose; eauto using scoped_mono, Nat.le_0_l.
Qed.

Lemma cofinite_scoped : forall L b,
  (forall x, x \notin L -> scoped 0 (open_tm_wrt_tm b (a_Var_f x))) ->
  scoped 1 b.
Proof.
  intros L b H; pick fresh x for L; exact (proj1 (@scoped_open_var b 0 x) (H x Fr)).
Qed.


Lemma typing_scoped : forall W p a A, Typing W p a A -> scoped 0 a.
Proof.
  induction 1; simpl; intuition eauto.
  - exact (@cofinite_scoped L B H1).
  - exact (proj1 IHTyping).
  - exact (@cofinite_scoped L b H0).
  - eapply (@cofinite_scoped L B); eassumption.
  - apply (@cofinite_scoped L c); intros x Fx.
    pick fresh y for (L \u {{x}}); exact (H3 x Fx y Fr).
  - eapply (@cofinite_scoped L B); eassumption.
Qed.

Lemma typing_lc : forall W p a A, Typing W p a A -> lc_tm a.
Proof. eauto using scoped_lc, typing_scoped. Qed.

Lemma grade_refl : forall p, p <= p.
Proof. intro; apply leq_join, join_idem. Qed.
Lemma grade_trans : forall p q r, p <= q -> q <= r -> p <= r.
Proof.
  intros p q r H J; apply leq_join; rewrite <- (join_leq _ _ J), join_assoc,
    (join_leq _ _ H); now rewrite (join_leq _ _ J).
Qed.
Lemma join_left : forall p q, p <= p * q.
Proof. intros; apply leq_join; rewrite join_assoc, join_idem; reflexivity. Qed.
Lemma join_right : forall p q, q <= p * q.
Proof. intros; rewrite join_comm; apply join_left. Qed.
Lemma join_bound : forall p q r, p <= r -> q <= r -> p * q <= r.
Proof.
  intros p q r H J; apply leq_join; rewrite <- join_assoc,
    (join_leq _ _ J), (join_leq _ _ H); reflexivity.
Qed.
Lemma meet_right : forall p q, p + q <= q.
Proof. intros; apply leq_meet; rewrite <- meet_assoc, meet_idem; reflexivity. Qed.
Lemma meet_left : forall p q, p + q <= p.
Proof. intros; rewrite meet_comm; apply meet_right. Qed.
Lemma meet_bound : forall p q r, p <= q -> p <= r -> p <= q + r.
Proof.
  intros p q r H J; apply leq_meet; rewrite meet_assoc,
    (meet_leq _ _ H), (meet_leq _ _ J); reflexivity.
Qed.
Lemma meet_cap : forall p, p <= q_C -> q_C + p = p.
Proof. intros; rewrite meet_comm; now apply meet_leq. Qed.
Lemma bot_le : forall p, q_Bot <= p.
Proof. intros; apply leq_meet; rewrite meet_comm; apply meet_Bot_r. Qed.
Local Hint Resolve grade_refl grade_trans join_left join_right join_bound
  meet_left meet_right meet_bound bot_le typing_lc : ddc.
Lemma typing_bound : forall W p a A, Typing W p a A -> p <= q_C.
Proof.
  induction 1; auto.
  pick fresh x for L; eauto.
Qed.

(* A lambda calculus with inert constants, used to distinguish type heads. *)
Inductive head :=
| h_Type (s : sort) | h_Unit | h_Pi (g : grade)
| h_WSigma (g : grade) | h_SSigma (g : grade) | h_Sum | h_Dummy.

Inductive raw :=
| rBound (n : nat) | rFree (x : atom) | rHead (h : head)
| rLam (b : raw) | rApp (f a : raw).

Definition lift_ren (f : nat -> nat) n :=
  match n with 0 => 0 | S n => S (f n) end.

Fixpoint ren (f : nat -> nat) (t : raw) : raw :=
  match t with
  | rBound n => rBound (f n)
  | rLam b => rLam (ren (lift_ren f) b)
  | rApp a b => rApp (ren f a) (ren f b)
  | _ => t
  end.

Definition lift_inst (f : (nat + atom)%type -> raw) (x : (nat + atom)%type) : raw :=
  match x with
  | inl 0 => rBound 0
  | inl (S n) => ren S (f (inl n))
  | inr a => ren S (f (inr a))
  end.

Fixpoint inst (f : (nat + atom)%type -> raw) (t : raw) : raw :=
  match t with
  | rBound n => f (inl n)
  | rFree a => f (inr a)
  | rLam b => rLam (inst (lift_inst f) b)
  | rApp a b => rApp (inst f a) (inst f b)
  | rHead _ => t
  end.

Definition rid (x : (nat + atom)%type) :=
  match x with inl n => rBound n | inr a => rFree a end.
Definition slot (u : raw) (x : (nat + atom)%type) :=
  match x with inl 0 => u | inl (S n) => rBound n | inr a => rFree a end.
Definition rb (t u : raw) := inst (slot u) t.

Lemma ren_ext : forall t f g, (forall n, f n = g n) -> ren f t = ren g t.
Proof. intro t; induction t; cbn; intros; f_equal; eauto.
  apply IHt; intros []; cbn; congruence.
Qed.

Lemma ren_comp : forall t f g, ren g (ren f t) = ren (fun n => g (f n)) t.
Proof.
  intro t; induction t; cbn; intros; rewrite ?IHt, ?IHt1, ?IHt2; try reflexivity.
  f_equal; apply ren_ext; intros []; reflexivity.
Qed.

Lemma inst_ext : forall t f g, (forall x, f x = g x) -> inst f t = inst g t.
Proof.
  intro t; induction t; cbn; intros; f_equal; eauto.
  apply IHt; intros [[|n]|x]; cbn; congruence.
Qed.

Definition on_bound (f : nat -> nat) (x : (nat + atom)%type) :=
  match x with inl n => inl (f n) | inr a => inr a end.

Lemma inst_ren : forall t f g, inst g (ren f t) = inst (fun x => g (on_bound f x)) t.
Proof.
  intro t; induction t; cbn; intros; rewrite ?IHt, ?IHt1, ?IHt2; try reflexivity.
  f_equal; apply inst_ext; intros [[|n]|x]; reflexivity.
Qed.

Lemma ren_inst : forall t f g, ren g (inst f t) = inst (fun x => ren g (f x)) t.
Proof.
  intro t; induction t; cbn; intros; rewrite ?IHt, ?IHt1, ?IHt2; try reflexivity.
  f_equal; apply inst_ext; intros [[|n]|x]; cbn; rewrite ?ren_comp; reflexivity.
Qed.

Lemma inst_comp : forall t f g, inst g (inst f t) = inst (fun x => inst g (f x)) t.
Proof.
  intro t; induction t; cbn; intros; rewrite ?IHt, ?IHt1, ?IHt2; try reflexivity.
  f_equal; apply inst_ext; intros [[|n]|x]; cbn; try reflexivity;
    rewrite inst_ren, ren_inst; apply inst_ext; intros [i|y]; reflexivity.
Qed.

Lemma inst_id : forall t, inst rid t = t.
Proof.
  intro t; induction t; cbn; rewrite ?IHt1, ?IHt2; try reflexivity.
  f_equal; rewrite <- IHt at 2; apply inst_ext; intros [[|n]|x]; reflexivity.
Qed.

Lemma rb_inst : forall t u f, inst f (rb t u) = rb (inst (lift_inst f) t) (inst f u).
Proof.
  intros; unfold rb; rewrite !inst_comp; apply inst_ext.
  intros [[|n]|x]; cbn; try reflexivity.
  all: rewrite inst_ren; symmetry; etransitivity;
    [apply inst_ext with (g := rid); intros [i|y]; reflexivity|apply inst_id].
Qed.

Inductive rpar : raw -> raw -> Prop :=
| rp_bound : forall n, rpar (rBound n) (rBound n)
| rp_free : forall x, rpar (rFree x) (rFree x)
| rp_head : forall h, rpar (rHead h) (rHead h)
| rp_lam : forall a b, rpar a b -> rpar (rLam a) (rLam b)
| rp_app : forall a b c d, rpar a c -> rpar b d -> rpar (rApp a b) (rApp c d)
| rp_beta : forall a b c d, rpar a c -> rpar b d -> rpar (rApp (rLam a) b) (rb c d).

Local Hint Constructors rpar : raw.
Lemma rpar_refl : forall a, rpar a a.
Proof. intro a; induction a; auto with raw. Qed.
Local Hint Resolve rpar_refl : raw.

Lemma rpar_ren : forall a b, rpar a b -> forall f, rpar (ren f a) (ren f b).
Proof.
  induction 1; simpl; intros; auto with raw.
  unfold rb; rewrite ren_inst.
  replace (inst (fun x => ren f (slot d x)) c) with
    (rb (ren (lift_ren f) c) (ren f d)).
  - auto with raw.
  - unfold rb; rewrite inst_ren; apply inst_ext; intros [[|n]|x]; reflexivity.
Qed.

Lemma rpar_inst : forall a b, rpar a b -> forall f g,
  (forall x, rpar (f x) (g x)) -> rpar (inst f a) (inst g b).
Proof.
  induction 1; cbn; intros; auto with raw.
  - apply rp_lam, IHrpar. intros [[|n]|x]; cbn; auto using rpar_ren with raw.
  - rewrite rb_inst; apply rp_beta;
      auto with raw.
    apply IHrpar1; intros [[|n]|x]; cbn; auto using rpar_ren with raw.
Qed.

Lemma rpar_rb : forall a b c d, rpar a b -> rpar c d -> rpar (rb a c) (rb b d).
Proof.
  unfold rb; intros; apply rpar_inst; auto;
    intros [[|n]|x]; cbn; auto with raw.
Qed.

Fixpoint develop (t : raw) : raw :=
  match t with
  | rLam a => rLam (develop a)
  | rApp a b =>
      match a with
      | rLam a => rb (develop a) (develop b)
      | _ => rApp (develop a) (develop b)
      end
  | _ => t
  end.

Lemma rpar_develop : forall a b, rpar a b -> rpar b (develop a).
Proof.
  induction 1; simpl; auto using rpar_rb with raw.
  destruct a; simpl in *; auto with raw.
  inversion H; subst; inversion IHrpar1; subst; auto with raw.
Qed.

Inductive rpath : raw -> raw -> Prop :=
| rpath_refl : forall t, rpath t t
| rpath_step : forall a b c, rpar a b -> rpath b c -> rpath a c.
Local Hint Constructors rpath : raw.

Lemma rpath_trans : forall a b c, rpath a b -> rpath b c -> rpath a c.
Proof. induction 1; eauto with raw. Qed.

Lemma rpath_strip : forall a b c, rpath a b -> rpar a c ->
  exists d, rpar b d /\ rpath c d.
Proof.
  intros a b c H; revert c; induction H; intros t J.
  - eauto with raw.
  - destruct (IHrpath _ (rpar_develop H)) as [d [Hd Jd]].
    exists d; split; [exact Hd|eapply rpath_step; [apply rpar_develop; exact J|exact Jd]].
Qed.

Lemma rpath_join : forall a b c, rpath a b -> rpath a c ->
  exists d, rpath b d /\ rpath c d.
Proof.
  intros a b c H; revert c; induction H; intros t J.
  - eauto with raw.
  - destruct (rpath_strip J H) as [d [Hd Jd]].
    destruct (IHrpath _ Jd) as [e [He Je]]; eauto with raw.
Qed.

Definition rconv a b := exists c, rpath a c /\ rpath b c.

Lemma rconv_refl : forall a, rconv a a.
Proof. unfold rconv; eauto with raw. Qed.
Lemma rconv_sym : forall a b, rconv a b -> rconv b a.
Proof. unfold rconv; firstorder. Qed.
Lemma rconv_trans : forall a b c, rconv a b -> rconv b c -> rconv a c.
Proof.
  intros a b c [d [J K]] [e [H I]].
  destruct (rpath_join K H) as [f [D E]].
  exists f; split; eauto using rpath_trans.
Qed.
Lemma rconv_par : forall a b, rpar a b -> rconv a b.
Proof. unfold rconv; eauto with raw. Qed.
Lemma rpath_lam : forall a b, rpath a b -> rpath (rLam a) (rLam b).
Proof. induction 1; eauto with raw. Qed.
Lemma rpath_app : forall a b c d, rpath a b -> rpath c d -> rpath (rApp a c) (rApp b d).
Proof.
  intros a b c d H J; induction H.
  - induction J; eauto with raw.
  - eauto with raw.
Qed.
Lemma rconv_lam : forall a b, rconv a b -> rconv (rLam a) (rLam b).
Proof. unfold rconv; intros ? ? [? [? ?]]; eauto using rpath_lam. Qed.
Lemma rconv_app : forall a b c d, rconv a b -> rconv c d -> rconv (rApp a c) (rApp b d).
Proof. unfold rconv; intros ? ? ? ? [? [? ?]] [? [? ?]]; eauto using rpath_app. Qed.
Lemma rconv_inst : forall a b f, rconv a b -> rconv (inst f a) (inst f b).
Proof.
  assert (H : forall a b, rpath a b -> forall f, rpath (inst f a) (inst f b)).
  { induction 1; eauto using rpar_inst with raw. }
  unfold rconv; intros ? ? ? [? [? ?]]; eauto.
Qed.
Local Hint Resolve rconv_refl rconv_lam rconv_app rconv_par : raw.

Definition rnode h a b := rApp (rApp (rHead h) a) b.

Lemma rpar_node : forall h a b t, rpar (rnode h a b) t ->
  exists a' b', t = rnode h a' b' /\ rpar a a' /\ rpar b b'.
Proof.
  unfold rnode; intros; inversion H; subst.
  match goal with H : rpar (rApp (rHead _) _) _ |- _ => inversion H; subst end.
  match goal with H : rpar (rHead _) _ |- _ => inversion H; subst end.
  eauto 8.
Qed.

Lemma rpath_node : forall h a b t, rpath (rnode h a b) t ->
  exists a' b', t = rnode h a' b' /\ rpath a a' /\ rpath b b'.
Proof.
  intros h a b t H; remember (rnode h a b) as k eqn:E; revert a b E.
  induction H; intros; subst.
  - eauto 8 with raw.
  - destruct (rpar_node H) as [d [e [-> [J K]]]].
    destruct (IHrpath _ _ (@Logic.eq_refl _ _)) as [f [g [-> [M N]]]].
    eauto 8 with raw.
Qed.

Lemma rconv_node : forall h a b k c d, rconv (rnode h a b) (rnode k c d) ->
  h = k /\ rconv a c /\ rconv b d.
Proof.
  intros h a b k c d [t [H J]].
  destruct (rpath_node H) as [a' [b' [E [A B]]]].
  destruct (rpath_node J) as [c' [d' [F [C D]]]].
  unfold rnode in *; rewrite E in F; inversion F; subst.
  repeat split; try reflexivity; unfold rconv; eauto.
Qed.

Lemma rpath_head : forall h t, rpath (rHead h) t -> t = rHead h.
Proof.
  intros h t H; remember (rHead h) as a; induction H; subst; auto.
  inversion H; subst; auto.
Qed.

Definition rdummy := rHead h_Dummy.
Definition rpair := rLam (rLam (rLam (rApp (rApp (rBound 0) (rBound 2)) (rBound 1)))).
Definition rinj1 := rLam (rLam (rLam (rApp (rBound 1) (rBound 2)))).
Definition rinj2 := rLam (rLam (rLam (rApp (rBound 0) (rBound 2)))).
Definition rfst := rLam (rLam (rBound 1)).
Definition rsnd := rLam (rLam (rBound 0)).
Definition visible (p q : grade) (a : raw) := if q <=? p then a else rdummy.

Fixpoint encode (p : grade) (t : tm) : raw :=
  match t with
  | a_Var_b n => rBound n
  | a_Var_f x => rFree x
  | a_Type s => rHead (h_Type s)
  | a_TyUnit => rHead h_Unit
  | a_TmUnit => rdummy
  | a_Abs _ _ b => rLam (encode p b)
  | a_App f q a => rApp (encode p f) (visible p q (encode p a))
  | a_WPair a q b | a_SPair a q b =>
      rApp (rApp rpair (visible p q (encode p a))) (encode p b)
  | a_Proj1 _ a => rApp (encode p a) rfst
  | a_Proj2 _ a => rApp (encode p a) rsnd
  | a_LetPair _ a b => rApp (encode p a) (rLam (encode p b))
  | a_Inj1 a => rApp rinj1 (encode p a)
  | a_Inj2 a => rApp rinj2 (encode p a)
  | a_Case _ a b c => rApp (rApp (encode p a) (encode p b)) (encode p c)
  | a_Sum a b => rnode h_Sum (encode p a) (encode p b)
  | a_Pi q a b => rnode (h_Pi q) (encode p a) (rLam (encode p b))
  | a_WSigma q a b => rnode (h_WSigma q) (encode p a) (rLam (encode p b))
  | a_SSigma q a b => rnode (h_SSigma q) (encode p a) (rLam (encode p b))
  end.

Definition under (P : (nat + atom)%type -> Prop) (x : (nat + atom)%type) :=
  match x with inl 0 => True | inl (S n) => P (inl n) | inr a => P (inr a) end.

Fixpoint support (P : (nat + atom)%type -> Prop) (a : raw) : Prop :=
  match a with
  | rBound n => P (inl n)
  | rFree x => P (inr x)
  | rLam b => support (under P) b
  | rApp b c => support P b /\ support P c
  | _ => True
  end.

Lemma support_mono : forall a P Q, support P a ->
  (forall x, P x -> Q x) -> support Q a.
Proof.
  intro a; induction a; simpl; intros; intuition eauto.
  eapply IHa; [eassumption|intros [[|n]|x]; simpl; eauto].
Qed.

Lemma support_inst : forall a P f g, support P a ->
  (forall x, P x -> f x = g x) -> inst f a = inst g a.
Proof.
  intro a; induction a; cbn; intros; try tauto; try solve [f_equal; intuition eauto].
  f_equal; eapply IHa; [eassumption|].
  intros [[|n]|x]; cbn; intros; f_equal; auto.
Qed.

Lemma support_ren : forall a P Q f, support P a ->
  (forall x, P x -> Q (on_bound f x)) -> support Q (ren f a).
Proof.
  intro a; induction a; simpl; intros; intuition eauto.
  - exact (H0 (inl n) H).
  - exact (H0 (inr x) H).
  - eapply IHa; [eassumption|intros [[|n]|x] A; cbn in *; auto].
    + exact (H0 (inl n) A).
    + exact (H0 (inr x) A).
Qed.

Lemma support_substitution : forall a P Q f, support P a ->
  (forall x, P x -> support Q (f x)) -> support Q (inst f a).
Proof.
  intro a; induction a; simpl; intros; intuition eauto.
  eapply IHa; [eassumption|].
  intros [[|n]|x]; cbn; intros; auto.
  all: eapply support_ren with (P := Q); [auto|intros [i|y]; auto].
Qed.

Definition raw_scope k (x : (nat + atom)%type) :=
  match x with inl n => (n < k)%nat | _ => True end.
Definition raw_fresh (x : atom) (v : (nat + atom)%type) :=
  match v with inl _ => True | inr y => y <> x end.

Lemma support_scope_under : forall k x, raw_scope (S k) x -> under (raw_scope k) x.
Proof. intros ? [[|n]|x]; cbn; intuition lia. Qed.
Lemma support_fresh_under : forall a x, support (raw_fresh x) a -> support (under (raw_fresh x)) a.
Proof. intros; eapply support_mono; eauto; intros [[|n]|y]; cbn; auto. Qed.

Local Ltac visibility := repeat match goal with |- context [visible ?p ?q ?a] =>
  unfold visible; destruct (q <=? p)
end.

Lemma encode_scope : forall a p k, scoped k a -> support (raw_scope k) (encode p a).
Proof.
  intro a; induction a; simpl; intros; visibility; cbn in *;
    repeat split; intuition (eauto; try lia).
  all: eapply support_mono; [eauto|apply support_scope_under].
Qed.

Lemma encode_fresh : forall a p x, x \notin fv_tm_tm a -> support (raw_fresh x) (encode p a).
Proof.
  intro a; induction a; simpl; intros; visibility; cbn in *; repeat split.
  all: try apply support_fresh_under.
  all: first [apply IHa; fsetdec | apply IHa1; fsetdec | apply IHa2; fsetdec |
              apply IHa3; fsetdec | intro; subst; fsetdec].
Qed.

Lemma scoped_ren_S : forall a, support (raw_scope 0) a -> ren S a = a.
Proof.
  assert (H : forall a k (f : nat -> nat), support (raw_scope k) a ->
    (forall n, (n < k)%nat -> f n = n) -> ren f a = a).
  { intro a; induction a; simpl; intros; try solve [f_equal; intuition eauto].
    f_equal; eapply IHa with (k := S k).
    - eapply support_mono with (P := under (raw_scope k)); [eassumption|]. intros [[|n]|x]; cbn; intuition lia.
    - intros [|n]; cbn; intros; f_equal; auto with arith.
  }
  intros; eapply H; eauto; intros; lia.
Qed.

Fixpoint at_depth k u :=
  match k with 0 => slot u | S k => lift_inst (at_depth k u) end.

Lemma at_depth_free : forall k u x, at_depth k u (inr x) = rFree x.
Proof. induction k; simpl; intros; rewrite ?IHk; reflexivity. Qed.

Lemma at_depth_bound : forall k u n, support (raw_scope 0) u ->
  at_depth k u (inl n) =
  match lt_eq_lt_dec n k with
  | inleft (left _) => rBound n
  | inleft (right _) => u
  | inright _ => rBound (n - 1)
  end.
Proof.
  induction k as [|k IH]; intros u [|n] H; cbn -[lt_eq_lt_dec].
  - indices; try (exfalso; lia); reflexivity.
  - indices; try (exfalso; lia); f_equal; lia.
  - indices; try (exfalso; lia); reflexivity.
  - rewrite IH by auto; indices; try (exfalso; lia); simpl; auto.
    + now rewrite scoped_ren_S.
    + f_equal; lia.
Qed.

Lemma encode_open_rec : forall a p k u, scoped 0 u ->
  encode p (open_tm_wrt_tm_rec k u a) =
  inst (at_depth k (encode p u)) (encode p a).
Proof.
  intro a; induction a; simpl; intros; unfold rnode; visibility; cbn;
    rewrite ?IHa, ?IHa1, ?IHa2, ?IHa3 by auto;
    try solve [reflexivity].
  - rewrite at_depth_bound by auto using encode_scope.
    indices; reflexivity.
  - rewrite at_depth_free; reflexivity.
Qed.

Lemma encode_open : forall a p u, lc_tm u ->
  encode p (open_tm_wrt_tm a u) = rb (encode p a) (encode p u).
Proof. intros; apply encode_open_rec; auto using lc_scoped. Qed.

Definition unopen x (v : (nat + atom)%type) : raw :=
  match v with
  | inl n => rBound (S n)
  | inr y => if y == x then rBound 0 else rFree y
  end.

Lemma encode_unopen : forall a p x, x \notin fv_tm_tm a ->
  inst (unopen x) (encode p (open_tm_wrt_tm a (a_Var_f x))) = encode p a.
Proof.
  intros; rewrite encode_open by constructor; unfold rb; simpl; rewrite inst_comp.
  transitivity (inst rid (encode p a)); [|apply inst_id].
  eapply support_inst; [eauto using encode_fresh|].
  intros [[|n]|y]; cbn; intros; try reflexivity;
    repeat match goal with |- context [if ?d then _ else _] => destruct d end; congruence.
Qed.

Lemma encode_binder_conv : forall p L a b,
  (forall x, x \notin L ->
    rconv (encode p (open_tm_wrt_tm a (a_Var_f x)))
          (encode p (open_tm_wrt_tm b (a_Var_f x)))) ->
  rconv (encode p a) (encode p b).
Proof.
  intros; pick fresh x for (L \u fv_tm_tm a \u fv_tm_tm b).
  specialize (H x ltac:(fsetdec)).
  apply (rconv_inst (unopen x)) in H; rewrite !encode_unopen in H by fsetdec; exact H.
Qed.

Lemma visible_yes : forall p q a, q <= p -> visible p q a = a.
Proof. unfold visible; intros p q a H; change ((q <=? p) = true) in H; now rewrite H. Qed.
Lemma visible_no : forall p q a, ~ q <= p -> visible p q a = rdummy.
Proof. unfold visible; intros p q a H; destruct (q <=? p) eqn:E; auto; exfalso; auto. Qed.

Definition usable (P : econtext) p (v : (nat + atom)%type) :=
  match v with
  | inl _ => False
  | inr x => exists q, binds x q P /\ q <= p
  end.

Lemma support_unopen : forall P p q x a,
  x \notin dom P -> support (usable ((x,q)::P) p) a ->
  support (under (usable P p)) (inst (unopen x) a).
Proof.
  intros; eapply support_substitution; [eassumption|].
  intros [n|y] Hvar; cbn in *; [contradiction|].
  destruct Hvar as [g [J K]].
  destruct (y == x); cbn; auto.
  destruct J as [J|J]; [congruence|eauto].
Qed.

Lemma support_unopen_irrel : forall P p q x a,
  ~ q <= p -> x \notin dom P -> support (usable ((x,q)::P) p) a ->
  support (usable P p) (inst (unopen x) a).
Proof.
  intros; eapply support_substitution; [eassumption|].
  intros [n|y] Hvar; cbn in *; [contradiction|].
  destruct Hvar as [g [J K]].
  destruct J as [J|J].
  - inversion J; subst; contradiction.
  - destruct (y == x); subst; cbn; eauto.
Qed.

Lemma binder_support : forall P p q L a,
  (forall x, x \notin L ->
    support (usable ((x,q)::P) p) (encode p (open_tm_wrt_tm a (a_Var_f x)))) ->
  support (under (usable P p)) (encode p a).
Proof.
  intros; pick fresh x for (L \u dom P \u fv_tm_tm a).
  rewrite <- (@encode_unopen a p x) by fsetdec.
  eapply support_unopen; [fsetdec|apply H; fsetdec].
Qed.

Lemma binder_irrel : forall P p q L a,
  ~ q <= p ->
  (forall x, x \notin L ->
    support (usable ((x,q)::P) p) (encode p (open_tm_wrt_tm a (a_Var_f x)))) ->
  support (usable P p) (encode p a).
Proof.
  intros; pick fresh x for (L \u dom P \u fv_tm_tm a).
  rewrite <- (@encode_unopen a p x) by fsetdec.
  eapply support_unopen_irrel; [eassumption|fsetdec|apply H0; fsetdec].
Qed.

Lemma rb_irrel : forall P p a u, support (usable P p) a -> rb a u = a.
Proof.
  intros; unfold rb.
  transitivity (inst rid a); [|apply inst_id].
  eapply support_inst; [eassumption|intros [n|x]; cbn; intuition].
Qed.

Lemma rb_support : forall P p a u,
  support (under (usable P p)) a -> support (usable P p) u ->
  support (usable P p) (rb a u).
Proof.
  unfold rb; intros; eapply support_substitution; [eassumption|].
  intros [[|n]|x]; cbn; intuition.
Qed.

Scheme cg_ind := Induction for CGrade Sort Prop
with gr_ind := Induction for Grade Sort Prop.
Combined Scheme grading_ind from cg_ind, gr_ind.

Lemma grading_support :
  (forall P p q a, CGrade P p q a -> support (usable P p) (visible p q (encode p a))) /\
  (forall P p a, Grade P p a -> support (usable P p) (encode p a)).
Proof.
  apply grading_ind; intros;
    cbn [encode rnode rpair rinj1 rinj2 rfst rsnd rdummy support] in *;
    try rewrite visible_yes by assumption; try rewrite visible_no by assumption;
    cbn [support rdummy];
    repeat split; auto; try solve [eapply binder_support; eassumption].
  all: try solve [cbn; eauto]; first [exact (@binder_support P psi psi L _ H0) |
              exact (@binder_support P psi psi0 L _ H0) |
              exact (@binder_support P psi psi0 L _ H)].
Qed.
Lemma grade_support : forall P p a, Grade P p a -> support (usable P p) (encode p a).
Proof. exact (proj2 grading_support). Qed.

Lemma rconv_beta : forall a b, rconv (rApp (rLam a) b) (rb a b).
Proof. eauto with raw. Qed.

Lemma inst_slot_shift : forall a u, inst (slot u) (ren S a) = a.
Proof.
  intros; rewrite inst_ren; transitivity (inst rid a); [|apply inst_id].
  apply inst_ext; intros [n|x]; reflexivity.
Qed.

Lemma inst_under_shift : forall a f,
  inst (lift_inst f) (ren S a) = ren S (inst f a).
Proof.
  intros; rewrite inst_ren, ren_inst; apply inst_ext; intros [n|x]; reflexivity.
Qed.

Local Ltac raw_beta :=
  lazymatch goal with
  | |- rconv (rApp (rLam ?a) ?b) ?out =>
      eapply rconv_trans; [apply rconv_beta|];
      unfold rb; cbn [inst lift_inst slot];
      rewrite ?inst_under_shift, ?inst_slot_shift
  | |- rconv (rApp ?f ?a) ?out =>
      eapply rconv_trans;
      [apply rconv_app; [raw_beta; apply rconv_refl|apply rconv_refl]|]
  end.

Lemma church_pair : forall a b c,
  rconv (rApp (rApp (rApp rpair a) b) c) (rApp (rApp c a) b).
Proof.
  intros; unfold rpair; do 3 raw_beta; apply rconv_refl.
Qed.
Lemma church_inj1 : forall a b c,
  rconv (rApp (rApp (rApp rinj1 a) b) c) (rApp b a).
Proof. intros; unfold rinj1; do 3 raw_beta; apply rconv_refl. Qed.
Lemma church_inj2 : forall a b c,
  rconv (rApp (rApp (rApp rinj2 a) b) c) (rApp c a).
Proof. intros; unfold rinj2; do 3 raw_beta; apply rconv_refl. Qed.
Lemma church_proj1 : forall a b,
  rconv (rApp (rApp (rApp rpair a) b) rfst) a.
Proof.
  intros; eapply rconv_trans; [apply church_pair|].
  unfold rfst; do 2 raw_beta; apply rconv_refl.
Qed.
Lemma church_proj2 : forall a b,
  rconv (rApp (rApp (rApp rpair a) b) rsnd) b.
Proof.
  intros; eapply rconv_trans; [apply church_pair|].
  unfold rsnd; do 2 raw_beta; apply rconv_refl.
Qed.

Lemma grade_beta_argument : forall P p q L b u,
  lc_tm u ->
  (forall x, x \notin L -> Grade ((x,q)::P) p (open_tm_wrt_tm b (a_Var_f x))) ->
  rb (encode p b) (visible p q (encode p u)) = encode p (open_tm_wrt_tm b u).
Proof.
  intros; destruct (q <=? p) eqn:E.
  - rewrite visible_yes, encode_open; auto.
  - assert (hn : ~ q <= p) by (change (~ (q <=? p) = true); congruence).
    assert (support (usable P p) (encode p b)).
    { apply (@binder_irrel P p q L b hn); intros; eauto using grade_support. }
    rewrite encode_open by auto; now rewrite !(@rb_irrel P p).
Qed.

Lemma step_encode : forall a b, Step a b ->
  forall P p, Grade P p a -> rconv (encode p a) (encode p b).
Proof.
  induction 1; intros P p Hgrade; inversion Hgrade; subst; cbn [encode].
  - eauto with raw.
  - match goal with H : Grade _ _ (a_Abs _ _ _) |- _ => inversion H; subst end.
    rewrite <- (@grade_beta_argument P p psi L a b H1 H7); apply rconv_beta.
  - eauto with raw.
  - rewrite visible_yes by assumption; apply church_inj1.
  - rewrite visible_yes by assumption; apply church_inj2.
  - eauto with raw.
  - eauto with raw.
  - rewrite visible_yes by assumption; apply church_proj1.
  - apply church_proj2.
  - eauto with raw.
  - rewrite (@visible_yes p q_Bot _ (bot_le p)).
    eapply rconv_trans; [apply church_pair|].
    apply rconv_app; [|apply rconv_refl].
    match goal with J : forall x, x \notin L -> Grade _ _ (open_tm_wrt_tm b (a_Var_f x)) |- _ =>
      rewrite <- (@grade_beta_argument P p psi L b a1 H0 J); apply rconv_beta
    end.
Qed.

Scheme cde_ind := Induction for CDefEq Sort Prop
with de_ind := Induction for DefEq Sort Prop.
Combined Scheme defequality_ind from cde_ind, de_ind.

Local Ltac scoped_cofinite :=
  match goal with
  | H : forall x, x \notin ?L -> scoped 0 (open_tm_wrt_tm ?b (a_Var_f x))
    |- scoped 1 ?b => exact (@cofinite_scoped L b H)
  | H : forall x, x \notin ?L -> scoped 0 (open_tm_wrt_tm ?a (a_Var_f x)) /\
       scoped 0 (open_tm_wrt_tm ?b (a_Var_f x)) |- scoped 1 ?t =>
    apply (@cofinite_scoped L t); intros y Fy;
    first [exact (proj1 (H y Fy)) | exact (proj2 (H y Fy))]
  end.

Lemma grading_scoped :
  (forall P p q a, CGrade P p q a -> scoped 0 a) /\
  (forall P p a, Grade P p a -> scoped 0 a).
Proof.
  apply grading_ind; intros; cbn [scoped] in *;
    intuition eauto using lc_scoped; scoped_cofinite.
Qed.

Lemma grade_scoped : forall P p a, Grade P p a -> scoped 0 a.
Proof. exact (proj2 grading_scoped). Qed.

Lemma defequality_scoped :
  (forall P p q a b, CDefEq P p q a b -> scoped 0 a /\ scoped 0 b) /\
  (forall P p a b, DefEq P p a b -> scoped 0 a /\ scoped 0 b).
Proof.
  apply defequality_ind; intros; cbn [scoped] in *;
    intuition eauto using lc_scoped, grade_scoped;
    try scoped_cofinite;
    unfold open_tm_wrt_tm;
    apply scoped_open; eauto using lc_scoped, grade_scoped;
    scoped_cofinite.
Qed.

Lemma defeq_lc_l : forall P p a b, DefEq P p a b -> lc_tm a.
Proof. intros; apply scoped_lc; exact (proj1 (proj2 defequality_scoped _ _ _ _ H)). Qed.
Lemma defeq_lc_r : forall P p a b, DefEq P p a b -> lc_tm b.
Proof. intros; apply scoped_lc; exact (proj2 (proj2 defequality_scoped _ _ _ _ H)). Qed.
Lemma grade_lc : forall P p a, Grade P p a -> lc_tm a.
Proof. eauto using scoped_lc, grade_scoped. Qed.

Definition encoded_eq P p a b :=
  support (usable P p) a /\ support (usable P p) b /\ rconv a b.

Lemma encoded_eq_node : forall P p h k a b c d,
  encoded_eq P p (rnode h a b) (rnode k c d) ->
  encoded_eq P p a c /\ encoded_eq P p b d.
Proof.
  intros ? ? ? ? ? ? ? ? [H [J K]]; apply rconv_node in K.
  unfold encoded_eq, rnode in *; cbn in *; tauto.
Qed.

Lemma rconv_rb : forall a b u v, rconv (rLam a) (rLam b) ->
  rconv u v -> rconv (rb a u) (rb b v).
Proof.
  intros; eapply rconv_trans; [apply rconv_sym, rconv_beta|].
  eapply rconv_trans; [apply rconv_app; eassumption|apply rconv_beta].
Qed.

Lemma encoded_eq_open : forall P p a b u v,
  encoded_eq P p (rLam (encode p a)) (rLam (encode p b)) ->
  encoded_eq P p (encode p u) (encode p v) ->
  lc_tm u -> lc_tm v ->
  encoded_eq P p (encode p (open_tm_wrt_tm a u)) (encode p (open_tm_wrt_tm b v)).
Proof.
  intros ? ? ? ? ? ? [? [? ?]] [? [? ?]] ? ?.
  unfold encoded_eq; rewrite !encode_open by assumption;
    repeat split; auto using rb_support, rconv_rb.
Qed.

Lemma encoded_eq_binder : forall P p q L a b,
  (forall x, x \notin L -> encoded_eq ((x,q)::P) p
     (encode p (open_tm_wrt_tm a (a_Var_f x)))
     (encode p (open_tm_wrt_tm b (a_Var_f x)))) ->
  encoded_eq P p (rLam (encode p a)) (rLam (encode p b)).
Proof.
  unfold encoded_eq; intros; cbn [support]; repeat split.
  - apply (@binder_support P p q L); firstorder.
  - apply (@binder_support P p q L); firstorder.
  - apply rconv_lam, (@encode_binder_conv p L); firstorder.
Qed.

Lemma encoded_eq_refl : forall P p a, support (usable P p) a -> encoded_eq P p a a.
Proof. unfold encoded_eq; eauto with raw. Qed.
Lemma encoded_eq_app : forall P p a b c d, encoded_eq P p a c ->
  encoded_eq P p b d -> encoded_eq P p (rApp a b) (rApp c d).
Proof. unfold encoded_eq; cbn; intuition eauto with raw. Qed.
Local Hint Resolve encoded_eq_refl encoded_eq_app encoded_eq_binder : raw.

Lemma defequality_encode :
  (forall P p q a b, CDefEq P p q a b ->
     encoded_eq P p (visible p q (encode p a)) (visible p q (encode p b))) /\
  (forall P p a b, DefEq P p a b -> encoded_eq P p (encode p a) (encode p b)).
Proof.
  apply defequality_ind; intros; cbn [encode rnode];
    try rewrite !visible_yes by assumption; try rewrite !visible_no by assumption;
    try solve [eauto using grade_support with raw];
    try solve [repeat apply encoded_eq_app; eauto with raw;
       apply encoded_eq_refl; cbn [support rpair rinj1 rinj2 rfst rsnd rdummy under]; tauto].
  all: try solve [unfold encoded_eq in *; intuition eauto using rconv_trans, rconv_sym].
  all: try solve [unfold encoded_eq; repeat split; eauto using grade_support, step_encode].
  all: try solve
    [unfold rnode; repeat apply encoded_eq_app;
     first [assumption | apply encoded_eq_refl; exact I |
       match goal with
       | E : forall x, x \notin ?L -> encoded_eq ((x ~ ?q) ++ ?P) ?p
           (encode ?p (open_tm_wrt_tm ?a (a_Var_f x)))
           (encode ?p (open_tm_wrt_tm ?b (a_Var_f x)))
         |- encoded_eq ?P ?p (rLam (encode ?p ?a)) (rLam (encode ?p ?b)) =>
         exact (@encoded_eq_binder P p q L a b E)
       end]].
  all: try match goal with E : encoded_eq _ _ _ _ |- _ =>
    apply encoded_eq_node in E
  end.
  all: try solve [tauto | eapply encoded_eq_open;
    eauto using defeq_lc_l, defeq_lc_r, grade_support, grade_lc with raw;
    tauto].
  - (* Irrelevant substitution can put any locally closed term in the omitted slot. *)
    assert (Ea : support (usable P phi) (encode phi b1)).
    { eapply (@binder_irrel P phi psi L); [eassumption|].
      intros; match goal with H : forall x, _ -> encoded_eq _ _ _ _ |- _ =>
        exact (proj1 (H x ltac:(assumption))) end. }
    assert (Eb : support (usable P phi) (encode phi b2)).
    { eapply (@binder_irrel P phi psi L); [eassumption|].
      intros; match goal with H : forall x, _ -> encoded_eq _ _ _ _ |- _ =>
        exact (proj1 (proj2 (H x ltac:(assumption)))) end. }
    rewrite !encode_open by assumption; rewrite !(@rb_irrel P phi) by assumption.
    unfold encoded_eq; repeat split; auto.
    apply (@encode_binder_conv phi L); intros; match goal with
    | H : forall x, _ -> encoded_eq _ _ _ _ |- _ =>
        exact (proj2 (proj2 (H x ltac:(assumption))))
    end.
Qed.

Lemma defeq_encode : forall P p a b, DefEq P p a b ->
  rconv (encode p a) (encode p b).
Proof. intros; exact (proj2 (proj2 (proj2 defequality_encode _ _ _ _ H))). Qed.

Definition rigid_head a :=
  match a with
  | rHead h | rApp (rApp (rHead h) _) _ => Some h
  | _ => None
  end.

Lemma rigid_head_path : forall a b h, rpath a b ->
  rigid_head a = Some h -> rigid_head b = Some h.
Proof.
  intros a b h H J.
  destruct a; cbn in J; try discriminate.
  - apply rpath_head in H; subst; exact J.
  - destruct a1; try discriminate; destruct a1_1; try discriminate.
    destruct (rpath_node H) as [c [d [-> _]]]; exact J.
Qed.

Lemma rigid_head_conv : forall a b h k, rconv a b ->
  rigid_head a = Some h -> rigid_head b = Some k -> h = k.
Proof.
  intros a b h k [c [H J]] E F.
  pose proof (rigid_head_path H E); pose proof (rigid_head_path J F); congruence.
Qed.

Definition head_value (h : head) (a : tm) : Prop :=
  match h, a with
  | h_Type _, _ => ValueType a
  | h_Unit, a_TmUnit => True
  | h_Pi q, a_Abs r _ _ | h_WSigma q, a_WPair _ r _ | h_SSigma q, a_SPair _ r _ => q = r
  | h_Sum, a_Inj1 _ | h_Sum, a_Inj2 _ => True
  | _, _ => False
  end.

Lemma typed_value_origin : forall W p a A, Typing W p a A -> Value a ->
  exists B h, rigid_head (encode q_C B) = Some h /\
              head_value h a /\ rconv (encode q_C B) (encode q_C A).
Proof.
  induction 1; intro V.
  - exists (a_Type s2), (h_Type s2); cbn; eauto using ValueType_Type with raw.
  - destruct (IHTyping1 V) as [D [h [Hh [Ha He]]]].
    exists D, h; repeat split; auto.
    eapply rconv_trans; eauto using defeq_encode.
  - inversion V; subst; match goal with H : ValueType (a_Var_f _) |- _ => inversion H end.
  - exists (a_Type s3), (h_Type s3); cbn; repeat split; auto with raw.
    inversion V; assumption.
  - exists (a_Pi psi0 A B), (h_Pi psi0); cbn; auto with raw.
  - inversion V; subst; match goal with H : ValueType (a_App _ _ _) |- _ => inversion H end.
  - inversion V; subst; match goal with H : ValueType (a_App _ _ _) |- _ => inversion H end.
  - exists (a_Type s3), (h_Type s3); cbn; repeat split; auto with raw.
    inversion V; assumption.
  - exists (a_WSigma psi0 A B), (h_WSigma psi0); cbn; auto with raw.
  - exists (a_WSigma psi0 A B), (h_WSigma psi0); cbn; auto with raw.
  - inversion V; subst; match goal with H : ValueType (a_LetPair _ _ _) |- _ => inversion H end.
  - exists (a_Type s3), (h_Type s3); cbn; repeat split; auto with raw.
    inversion V; assumption.
  - exists (a_SSigma psi0 A B), (h_SSigma psi0); cbn; auto with raw.
  - inversion V; subst; match goal with H : ValueType (a_Proj1 _ _) |- _ => inversion H end.
  - inversion V; subst; match goal with H : ValueType (a_Proj2 _ _) |- _ => inversion H end.
  - exists (a_Type s), (h_Type s); cbn; repeat split; auto with raw.
    inversion V; assumption.
  - exists (a_Sum A1 A2), h_Sum; cbn; auto with raw.
  - exists (a_Sum A1 A2), h_Sum; cbn; auto with raw.
  - inversion V; subst; match goal with H : ValueType (a_Case _ _ _ _) |- _ => inversion H end.
  - exists (a_Type s), (h_Type s); cbn; eauto using ValueType_Unit with raw.
  - exists a_TyUnit, h_Unit; cbn; auto with raw.
Qed.

Lemma typed_value_head : forall W p a A h, Typing W p a A -> Value a ->
  rigid_head (encode q_C A) = Some h -> head_value h a.
Proof.
  intros W p a A h H V E.
  destruct (typed_value_origin H V) as [B [k [K [J F]]]].
  assert (k = h) by (eapply rigid_head_conv; eassumption); subst; assumption.
Qed.

Local Hint Constructors Step Value ValueType : progress.

Lemma typing_progress_closed : forall W p a A, Typing W p a A ->
  W = nil -> (exists a', Step a a') \/ Value a.
Proof.
  induction 1; intro E; subst W;
    try solve [right; eauto using typing_lc with progress];
    try solve [eauto].
  - inversion H1.
  - right; apply V_ValueType, ValueType_Pi; eauto using typing_lc.
    eapply typing_lc; eapply T_Pi; eassumption.
  - right; apply V_Abs.
    + apply scoped_lc.
      exact (proj1 (typing_scoped H1)).
    + eapply typing_lc; eapply T_Abs; eassumption.
  - destruct (IHTyping1 (Logic.eq_refl nil)) as [[f J]|V].
    + left; eauto using typing_lc with progress.
    + pose proof (typed_value_head H V (Logic.eq_refl (Some (h_Pi psi0)))) as K.
      destruct b; cbn in K; try contradiction; subst.
      inversion V; subst; try solve [match goal with V : ValueType (a_Abs _ _ _) |- _ => inversion V end].
      left; eauto using typing_lc with progress.
  - destruct (IHTyping1 (Logic.eq_refl nil)) as [[f J]|V].
    + left; eauto using typing_lc with progress.
    + pose proof (typed_value_head H V (Logic.eq_refl (Some (h_Pi psi0)))) as K.
      destruct b; cbn in K; try contradiction; subst.
      inversion V; subst; try solve [match goal with V : ValueType (a_Abs _ _ _) |- _ => inversion V end].
      left; eauto using typing_lc with progress.
  - right; apply V_ValueType, ValueType_WSigma; eauto using typing_lc.
    eapply typing_lc; eapply T_WSigma; eassumption.
  - assert (lc_tm (a_LetPair psi0 a c)).
    { eapply typing_lc; eapply T_LetPair; eassumption. }
    destruct (IHTyping (Logic.eq_refl nil)) as [[a' J]|V].
    + left; eauto with progress.
    + pose proof (typed_value_head H1 V (Logic.eq_refl (Some (h_WSigma psi0)))) as K.
      destruct a; cbn in K; try contradiction; subst.
      inversion V; subst; try solve [match goal with V : ValueType (a_WPair _ _ _) |- _ => inversion V end].
      left; eauto with progress.
  - right; apply V_ValueType, ValueType_SSigma; eauto using typing_lc.
    eapply typing_lc; eapply T_SSigma; eassumption.
  - destruct (IHTyping (Logic.eq_refl nil)) as [[a' J]|V].
    + left; eauto with progress.
    + pose proof (typed_value_head H V (Logic.eq_refl (Some (h_SSigma psi0)))) as K.
      destruct a; cbn in K; try contradiction; subst.
      inversion V; subst; try solve [match goal with V : ValueType (a_SPair _ _ _) |- _ => inversion V end].
      left; eauto with progress.
  - destruct (IHTyping (Logic.eq_refl nil)) as [[a' J]|V].
    + left; eauto with progress.
    + pose proof (typed_value_head H V (Logic.eq_refl (Some (h_SSigma psi0)))) as K.
      destruct a; cbn in K; try contradiction; subst.
      inversion V; subst; try solve [match goal with V : ValueType (a_SPair _ _ _) |- _ => inversion V end].
      left; eauto with progress.
  - destruct (IHTyping1 (Logic.eq_refl nil)) as [[a' J]|V].
    + left; eauto using typing_lc with progress.
    + pose proof (typed_value_head H1 V (Logic.eq_refl (Some h_Sum))) as K.
      destruct a; cbn in K; try contradiction.
      all: inversion V; subst;
        try solve [match goal with V : ValueType (a_Inj1 _) |- _ => inversion V end |
                   match goal with V : ValueType (a_Inj2 _) |- _ => inversion V end];
        left; eauto using typing_lc with progress.
Qed.

(* Context transport records exactly the variable lookups used by grading. *)
Local Hint Extern 2 (_ \notin _) => solve [fsetdec] : fsetdec.
Definition permits P Q p :=
  uniq Q /\ forall x q, binds x q P -> q <= p -> exists r, binds x r Q /\ r <= p.

Lemma permits_cons : forall P Q p x q, permits P Q p -> x \notin dom Q ->
  permits ((x,q)::P) ((x,q)::Q) p.
Proof.
  intros P Q p x q [H J] Fx; split; [apply uniq_cons; auto|].
  intros y r [E|E] K.
  - inversion E; subst; exists r; split; simpl; auto.
  - destruct (J _ _ E K) as [s [F G]]; exists s; split; simpl; auto.
Qed.

Lemma permits_bigger : forall P Q p,
  uniq Q -> (forall x q, binds x q P -> binds x q Q) -> permits P Q p.
Proof. unfold permits; eauto. Qed.

Local Ltac grading_transport_binder ctor L Q :=
  eapply ctor with (L := L \u dom Q);
  try solve [eauto 2];
  intros x Fx;
  match goal with IH : forall y, y \notin L -> forall Z, permits _ Z _ -> _ |- _ =>
    eapply IH; [fsetdec|apply permits_cons; [assumption|fsetdec]]
  end.

Lemma grading_transport :
  (forall P p q a, CGrade P p q a ->
    forall Q, permits P Q p -> CGrade Q p q a) /\
  (forall P p a, Grade P p a ->
    forall Q, permits P Q p -> Grade Q p a).
Proof.
  apply grading_ind; intros.
  - apply CG_Leq; auto.
  - apply CG_Nleq; auto; match goal with M : permits _ _ _ |- uniq _ => exact (proj1 M) end.
  - apply G_Type; match goal with M : permits _ _ _ |- uniq _ => exact (proj1 M) end.
  - match goal with H : permits _ _ _ |- _ =>
      destruct H as [Hu Hv]
    end.
    match goal with
    | E : binds ?x ?q _, G : ?q <= _ |- _ =>
        destruct (Hv _ _ E G) as [g [Hg Jg]]; eapply G_Var; eauto
    end.
  - grading_transport_binder G_Pi L Q.
  - grading_transport_binder G_Abs L Q.
  - apply G_App; auto.
  - grading_transport_binder G_WSigma L Q.
  - apply G_WPair; auto.
  - grading_transport_binder G_LetPair L Q.
  - grading_transport_binder G_SSigma L Q.
  - apply G_SPair; auto.
  - apply G_Proj1; auto.
  - apply G_Proj2; auto.
  - apply G_Sum; auto.
  - apply G_Inj1; auto.
  - apply G_Inj2; auto.
  - apply G_Case; auto.
  - apply G_TyUnit; match goal with M : permits _ _ _ |- uniq _ => exact (proj1 M) end.
  - apply G_TmUnit; match goal with M : permits _ _ _ |- uniq _ => exact (proj1 M) end.
Qed.

Lemma grade_transport : forall P Q p a, Grade P p a -> permits P Q p -> Grade Q p a.
Proof. intros; eapply (proj2 grading_transport); eauto. Qed.

Lemma defequality_transport :
  (forall P p q a b, CDefEq P p q a b ->
    forall Q, permits P Q p -> CDefEq Q p q a b) /\
  (forall P p a b, DefEq P p a b ->
    forall Q, permits P Q p -> DefEq Q p a b).
Proof.
  apply defequality_ind; intros.
  - eapply CDefEq_Leq; eauto.
  - eapply CDefEq_Nleq; eauto; match goal with M : permits _ _ _ |- uniq _ => exact (proj1 M) end.
  - apply Eq_Refl; eauto using grade_transport.
  - eapply Eq_Trans; eauto.
  - apply Eq_Sym; auto.
  - eapply Eq_Beta; eauto using grade_transport.
  - grading_transport_binder Eq_Pi L Q.
  - grading_transport_binder Eq_Abs L Q.
  - apply Eq_App; auto.
  - eapply Eq_PiFst; eauto.
  - eapply Eq_PiSnd; eauto.
  - grading_transport_binder Eq_WSigma L Q.
  - eapply Eq_WSigmaFst; eauto.
  - eapply Eq_WSigmaSnd; eauto using grade_transport.
  - apply Eq_WPair; auto.
  - grading_transport_binder Eq_LetPair L Q.
  - grading_transport_binder Eq_SSigma L Q.
  - eapply Eq_SSigmaFst; eauto.
  - eapply Eq_SSigmaSnd; eauto.
  - apply Eq_SPair; auto.
  - apply Eq_Proj1; auto.
  - apply Eq_Proj2; auto.
  - apply Eq_Sum; auto.
  - eapply Eq_SumFst; eauto.
  - eapply Eq_SumSnd; eauto.
  - apply Eq_Inj1; auto.
  - apply Eq_Inj2; auto.
  - apply Eq_Case; auto.
  - apply Eq_TyUnit; match goal with M : permits _ _ _ |- uniq _ => exact (proj1 M) end.
  - apply Eq_TmUnit; match goal with M : permits _ _ _ |- uniq _ => exact (proj1 M) end.
  - eapply Eq_SubstIrrel with (L := L \u dom Q) (psi := psi); eauto.
    intros x Fx; eapply H; [fsetdec|apply permits_cons; [eassumption|fsetdec]].
Qed.

Lemma defeq_transport : forall P Q p a b, DefEq P p a b -> permits P Q p -> DefEq Q p a b.
Proof. intros; eapply (proj2 defequality_transport); eauto. Qed.

Lemma join_bot : forall p, p * q_Bot = p.
Proof. intros; rewrite join_comm; apply join_leq, bot_le. Qed.

Lemma join_top : forall p, p <= q_Top.
Proof. intro; apply leq_join, join_Top_r. Qed.

Lemma grade_antisym : forall p q, p <= q -> q <= p -> p = q.
Proof.
  intros p q H J; rewrite <- (join_leq _ _ J), join_comm, (join_leq _ _ H); reflexivity.
Qed.

Lemma join_mono : forall a b c, a <= b -> a * c <= b * c.
Proof. intros; apply join_bound; eauto with ddc. Qed.

Lemma meet_id : forall W, meet_ctx_l q_C (meet_ctx_l q_C W) = meet_ctx_l q_C W.
Proof.
  intro W; induction W as [|[x [p A]] W IH]; cbn; auto.
  f_equal; [now rewrite meet_assoc, meet_idem|exact IH].
Qed.

Lemma meet_bind : forall W x p A, binds x (p,A) W ->
  binds x (q_C + p,A) (meet_ctx_l q_C W).
Proof.
  intros; apply (binds_map _ _ (fun '(p,A) => (q_C + p,A)) _ _ _ H).
Qed.

Lemma labels_bind : forall W x p A, binds x (p,A) W -> binds x p (labels W).
Proof.
  intros; apply (binds_map _ _ (fun '(p,A) => p) _ _ _ H).
Qed.

Lemma meet_bind_inv : forall W x r A, binds x (r,A) (meet_ctx_l q_C W) ->
  exists p, binds x (p,A) W /\ r = q_C + p.
Proof.
  induction W as [|[y [p B]] W IH]; cbn; intros x r A H.
  - contradiction.
  - destruct H as [H|H].
    + inversion H; subst; eauto.
    + destruct (IH _ _ _ H) as [q [Hq ->]]; eauto.
Qed.

Lemma labels_bind_inv : forall W x p, binds x p (labels W) ->
  exists A, binds x (p,A) W.
Proof.
  induction W as [|[y [q A]] W IH]; cbn; intros x p H.
  - contradiction.
  - destruct H as [H|H].
    + inversion H; subst; eauto.
    + destruct (IH _ _ H); eauto.
Qed.

Arguments meet_bind_inv [W x r A] _.
Arguments labels_bind_inv [W x p] _.

Lemma dom_meet : forall W, dom (meet_ctx_l q_C W) [=] dom W.
Proof. intro; apply dom_map. Qed.
Lemma dom_labels : forall W, dom (labels W) [=] dom W.
Proof. intro; apply dom_map. Qed.
Lemma uniq_meet : forall W, uniq W -> uniq (meet_ctx_l q_C W).
Proof. intros; apply uniq_map; assumption. Qed.
Lemma uniq_labels : forall W, uniq W -> uniq (labels W).
Proof. intros; apply uniq_map; assumption. Qed.
Lemma ctx_uniq : forall W, Ctx W -> uniq W.
Proof. induction 1; auto using uniq_nil, uniq_cons. Qed.

Definition ctx_map d (W V : context) :=
  uniq V /\ forall x p A, binds x (p,A) W ->
    exists q, binds x (q,A) V /\ q <= p * d.

Lemma ctx_map_cons : forall d W V x p q A, ctx_map d W V ->
  x \notin dom V -> q <= p * d -> ctx_map d ((x,(p,A))::W) ((x,(q,A))::V).
Proof.
  intros d W V x p q A [H J] Fx Hq; split; [apply uniq_cons; auto|].
  intros y r B [E|E].
  - inversion E; subst; exists q; split; simpl; auto.
  - destruct (J _ _ _ E) as [s [F G]]; exists s; split; simpl; auto.
Qed.

Lemma ctx_map_meet : forall d W V, ctx_map d W V ->
  ctx_map d (meet_ctx_l q_C W) (meet_ctx_l q_C V).
Proof.
  intros d W V [H J]; split; auto using uniq_meet.
  intros x p A E; destruct (meet_bind_inv E) as [r [F ->]].
  destruct (J _ _ _ F) as [q [G Hq]].
  exists (q_C + q); split; auto using meet_bind.
  destruct (order_q_C_dec r) as [R|[R _]].
  - rewrite (meet_cap R); eauto with ddc.
  - rewrite (meet_leq _ _ R); eauto with ddc.
Qed.

Lemma ctx_map_permits : forall d W V, ctx_map d W V ->
  permits (labels (meet_ctx_l q_C W)) (labels (meet_ctx_l q_C V)) q_C.
Proof.
  intros d W V [H J]; split; auto using uniq_meet, uniq_labels.
  intros x p E _.
  destruct (labels_bind_inv E) as [A F].
  destruct (meet_bind_inv F) as [r [G ->]].
  destruct (J _ _ _ G) as [q [B _]].
  exists (q_C + q); split; eauto using labels_bind, meet_bind, meet_left.
Qed.

Lemma meet_top_ctx : q_C = q_Top -> forall W, meet_ctx_l q_C W = W.
Proof.
  intros -> W; induction W as [|[x [p A]] W IH]; cbn; auto.
  f_equal; [rewrite meet_comm, meet_leq by apply join_top; reflexivity|exact IH].
Qed.

Lemma ctx_map_bound : forall d W V p x r A, ctx_map d W V -> binds x (r,A) W ->
  r <= p -> p * d <= q_C -> Typing V (p * d) (a_Var_f x) A.
Proof.
  intros d W V p x r A [J K] H Hr Hp.
  destruct (K _ _ _ H) as [s [Hs Hs']].
  eapply T_Var with (psi0 := s); eauto.
  eapply grade_trans; [exact Hs'|apply join_mono; exact Hr].
Qed.

Local Hint Resolve ctx_map_meet ctx_map_permits ctx_map_cons : ddc.

Local Ltac at_cap d Hd Hcap :=
  match goal with
  | |- Typing ?V q_C ?a ?A =>
    match goal with
    | IH : forall e Z, e <= q_C -> ctx_map e ?W Z -> Typing Z (q_C * e) a ?AA |- _ =>
      let M := fresh "map" in
      assert (M : ctx_map d W V) by (eauto with ddc);
      let J := fresh "cap" in
      pose proof (IH d V Hd M) as J; rewrite Hcap in J; exact J
    end
  end.

Lemma typing_transport : forall W p a A, Typing W p a A ->
  forall d V, d <= q_C -> ctx_map d W V -> Typing V (p * d) a A.
Proof.
  induction 1; intros d V Hd HV;
    assert (Hcap : q_C * d = q_C) by (rewrite join_comm; now apply join_leq).
  - apply T_Type; eauto with ddc; exact (proj1 HV).
  - eapply T_Conv; [eauto|eapply defeq_transport; eauto with ddc|].
    at_cap d Hd Hcap.
  - eapply ctx_map_bound; eauto with ddc.
  - eapply T_Pi with (L := L \u dom V); eauto.
    intros x Fx; eapply H1; [fsetdec|assumption|].
    apply ctx_map_cons; [assumption|fsetdec|apply grade_refl].
  - eapply T_Abs with (L := L \u dom V).
    + intros x Fx; eapply H0; [fsetdec|assumption|].
      apply ctx_map_cons; [assumption|fsetdec|].
      rewrite join_assoc; apply grade_refl.
    + at_cap d Hd Hcap.
  - eapply T_App; eauto; rewrite join_assoc; auto.
  - eapply T_AppIrrel; eauto; at_cap d Hd Hcap.
  - eapply T_WSigma with (L := L \u dom V); eauto.
    intros x Fx; eapply H1; [fsetdec|assumption|].
    apply ctx_map_cons; [assumption|fsetdec|apply grade_refl].
  - eapply T_WPair; eauto; [at_cap d Hd Hcap|rewrite join_assoc; auto].
  - eapply T_WPairIrrel; eauto; at_cap d Hd Hcap.
  - eapply T_LetPair with (L := L \u dom V); eauto.
    + intros x Fx.
      assert (F : x \notin L) by fsetdec.
      specialize (H0 x F).
      assert (Hm : ctx_map d ((x,(q_C,a_WSigma psi0 A B))::meet_ctx_l q_C W)
                            ((x,(q_C,a_WSigma psi0 A B))::meet_ctx_l q_C V)).
      { apply ctx_map_cons; auto with ddc.
        rewrite dom_meet; fsetdec. }
      pose proof (H0 d _ Hd Hm) as J; rewrite Hcap in J; exact J.
    + intros x Fx y Fy; eapply H3; [fsetdec|fsetdec|assumption|].
      apply ctx_map_cons; [assumption|fsetdec|].
      rewrite join_assoc; apply grade_refl.
  - eapply T_SSigma with (L := L \u dom V); eauto.
    intros x Fx; eapply H1; [fsetdec|assumption|].
    apply ctx_map_cons; [assumption|fsetdec|apply grade_refl].
  - eapply T_SPair; eauto; [at_cap d Hd Hcap|rewrite join_assoc; auto].
  - eapply T_Proj1; eauto with ddc.
  - eapply T_Proj2; eauto with ddc.
  - eapply T_Sum; auto.
  - eapply T_Inj1; eauto; at_cap d Hd Hcap.
  - eapply T_Inj2; eauto; at_cap d Hd Hcap.
  - eapply T_Case with (L := L \u dom V); eauto with ddc.
    + intros x Fx.
      assert (F : x \notin L) by fsetdec.
      specialize (H0 x F).
      assert (Hm : ctx_map d ((x,(q_C,a_Sum A1 A2))::meet_ctx_l q_C W)
                            ((x,(q_C,a_Sum A1 A2))::meet_ctx_l q_C V)).
      { apply ctx_map_cons; auto with ddc.
        rewrite dom_meet; fsetdec. }
      pose proof (H0 d _ Hd Hm) as J; rewrite Hcap in J; exact J.
  - eapply T_TmUnit; eauto with ddc; exact (proj1 HV).
  - eapply T_TyUnit; eauto with ddc; exact (proj1 HV).
Qed.

Lemma typing_weaken : forall W V p a A, Typing W p a A -> uniq V ->
  (forall x r B, binds x (r,B) W -> binds x (r,B) V) ->
  Typing V p a A.
Proof.
  intros; pose proof (@typing_transport W p a A H q_Bot V (bot_le _) ) as J.
  rewrite join_bot in J; apply J; split; auto.
  intros; eexists; split; eauto; rewrite join_bot; apply grade_refl.
Qed.

Lemma typing_raise : forall W p q a A, Typing W p a A -> uniq W ->
  p <= q -> q <= q_C -> Typing W q a A.
Proof.
  intros; pose proof (@typing_transport W p a A H q W H2) as J.
  rewrite (join_leq _ _ H1) in J; apply J; split; auto.
  intros; eauto with ddc.
Qed.

Lemma typing_meet : forall W p a A, Typing W p a A -> uniq W ->
  Typing (meet_ctx_l q_C W) q_C a A.
Proof.
  intros; pose proof (@typing_transport W p a A H q_C (meet_ctx_l q_C W) (grade_refl _)) as J.
  rewrite (join_leq _ _ (typing_bound H)) in J; apply J; split; auto using uniq_meet.
  intros; eexists; split; eauto using meet_bind.
  eauto with ddc.
Qed.

Lemma uniq_unmeet : forall W, uniq (meet_ctx_l q_C W) -> uniq W.
Proof. intros; eapply uniq_map_1; eassumption. Qed.

Lemma typing_uniq : forall W p a A, Typing W p a A -> uniq W.
Proof. induction 1; auto using uniq_unmeet. Qed.

Lemma grade_lower_binder : forall W p q r x a,
  Grade ((x,q)::labels W) p a -> uniq W -> x \notin dom W -> r <= q ->
  Grade ((x,r)::labels W) p a.
Proof.
  intros; eapply grade_transport; [eassumption|].
  split.
  - apply uniq_cons; [auto using uniq_labels|rewrite dom_labels; assumption].
  - intros y g [E|E] Hg.
    + inversion E; subst; exists r; split; simpl; eauto using grade_trans.
    + exists g; split; simpl; auto.
Qed.

Lemma typed_grade : forall W p a A, Typing W p a A -> Grade (labels W) p a.
Proof.
  induction 1; try solve [assumption | econstructor; eauto using uniq_labels, labels_bind].
  - assert (Hu : uniq W) by eauto using typing_uniq, uniq_unmeet.
    eapply G_Abs with (L := L \u dom W).
    + intros x Fx; eapply grade_lower_binder with (q := psi0 * psi).
      * apply H0; fsetdec.
      * exact Hu.
      * fsetdec.
      * apply join_left.
    + destruct (q_Top <=? psi) eqn:E.
      * change (q_Top <= psi) in E.
        assert (HC : psi <= q_C).
        { pick fresh x for L; eauto using typing_bound. }
        pose proof (grade_antisym E (join_top psi)) as J.
        pose proof (grade_antisym (grade_trans E HC) (join_top q_C)) as K.
        apply CG_Leq; auto.
        rewrite (meet_top_ctx (Logic.eq_sym K) W) in IHTyping.
        subst psi; rewrite K; inversion IHTyping; assumption.
      * apply CG_Nleq; auto using uniq_labels.
        -- apply scoped_lc; exact (proj1 (typing_scoped H1)).
        -- change (~ (q_Top <=? psi) = true); congruence.
  - apply G_App; auto.
    destruct (psi0 <=? psi) eqn:E.
    + change (psi0 <= psi) in E; apply CG_Leq; auto.
      rewrite (join_leq _ _ E) in IHTyping2; exact IHTyping2.
    + apply CG_Nleq; try solve [eauto using typing_lc, uniq_labels, typing_uniq].
      change (~ (psi0 <=? psi) = true); congruence.
  - apply G_App; auto.
    apply CG_Nleq; try solve [eauto using typing_lc, uniq_labels, typing_uniq].
    intros J; destruct H1 as [K N]; apply N, grade_antisym; auto.
    eauto using grade_trans, typing_bound.
  - apply G_WPair; auto.
    destruct (psi0 <=? psi) eqn:E.
    + change (psi0 <= psi) in E; apply CG_Leq; auto.
      rewrite (join_leq _ _ E) in IHTyping2; exact IHTyping2.
    + apply CG_Nleq; try solve [eauto using typing_lc, uniq_labels, typing_uniq].
      change (~ (psi0 <=? psi) = true); congruence.
  - apply G_WPair; auto.
    apply CG_Nleq; try solve [eauto using typing_lc, uniq_labels, typing_uniq].
    intros J; destruct H1 as [K N]; apply N, grade_antisym; auto.
    eauto using grade_trans, typing_bound.
  - eapply G_LetPair with (L := L \u dom W); auto;
      intros x Fx; pick fresh y for (L \u {{x}}).
    eapply grade_lower_binder with (q := psi0 * psi).
    + exact (H3 x ltac:(fsetdec) y Fr).
    + eauto using typing_uniq.
    + fsetdec.
    + apply join_left.
  - apply G_SPair; auto.
    destruct (psi0 <=? psi) eqn:E.
    + change (psi0 <= psi) in E; apply CG_Leq; auto.
      rewrite (join_leq _ _ E) in IHTyping2; exact IHTyping2.
    + apply CG_Nleq; try solve [eauto using typing_lc, uniq_labels, typing_uniq].
      change (~ (psi0 <=? psi) = true); congruence.
Qed.

Lemma cap_typing_grade : forall W p a A, Typing W p a A ->
  Grade (labels (meet_ctx_l q_C W)) q_C a.
Proof. eauto using typed_grade, typing_meet, typing_uniq. Qed.

Lemma subst_lc : forall t u x, lc_tm t -> lc_tm u -> lc_tm (subst_tm_tm u x t).
Proof. eauto using scoped_lc, subst_scoped, lc_scoped. Qed.

Lemma subst_open_var : forall b u z x, x <> z -> lc_tm u ->
  subst_tm_tm u z (open_tm_wrt_tm b (a_Var_f x)) =
  open_tm_wrt_tm (subst_tm_tm u z b) (a_Var_f x).
Proof.
  intros; rewrite subst_open by auto; cbn [subst_tm_tm].
  match goal with |- context [if ?d then _ else _] => destruct d end; congruence.
Qed.

Lemma step_subst : forall a b, Step a b -> forall u z, lc_tm u ->
  Step (subst_tm_tm u z a) (subst_tm_tm u z b).
Proof.
  induction 1; intros; cbn [subst_tm_tm]; rewrite ?subst_open by auto;
    eauto using subst_lc with progress.
  - apply S_Beta; eauto using subst_lc.
    exact (@subst_lc (a_Abs psi A a) u z H0 H2).
  - apply S_LetPairCong; eauto.
    exact (@subst_lc (a_LetPair psi a b) u z H H1).
  - apply S_LetPairBeta; eauto using subst_lc.
    exact (@subst_lc (a_LetPair psi (a_WPair a1 psi a2) b) u z H H2).
Qed.

Definition grade_subst_map (P Q : econtext) p z u :=
  uniq Q /\ forall x q, binds x q P -> q <= p ->
    Grade Q p (subst_tm_tm u z (a_Var_f x)).

Lemma grade_subst_map_cons : forall P Q p z u x q,
  grade_subst_map P Q p z u -> x <> z -> x \notin dom Q ->
  grade_subst_map ((x,q)::P) ((x,q)::Q) p z u.
Proof.
  intros P Q p z u x q [J K] N F.
  assert (U : uniq ((x,q)::Q)) by auto using uniq_cons.
  split; auto.
  intros y r [E|E] Hr.
  - inversion E; subst; cbn.
    match goal with |- context [if ?d then _ else _] => destruct d end; try congruence.
    eapply G_Var; eauto; simpl; auto.
  - eapply grade_transport; [eauto|apply permits_bigger; auto].
Qed.

Local Ltac subst_grade_body L :=
  intros y Fy;
  repeat rewrite <- subst_open_var by (auto; fsetdec);
  match goal with
  | IH : forall x, x \notin L -> forall Q z u, lc_tm u ->
       grade_subst_map _ Q _ z u -> _ |- _ =>
    eapply IH; [fsetdec|assumption|apply grade_subst_map_cons; [assumption|fsetdec|fsetdec]]
  end.

Local Ltac use_subst_binder ctor L Q z :=
  eapply ctor with (L := L \u dom Q \u {{z}});
  try solve [eauto 2]; subst_grade_body L.

Local Ltac subst_grade_uniq :=
  match goal with M : grade_subst_map _ _ _ _ _ |- uniq _ => exact (proj1 M) end.

Lemma grading_substitution :
  (forall P p q a, CGrade P p q a ->
    forall Q z u, lc_tm u -> grade_subst_map P Q p z u ->
    CGrade Q p q (subst_tm_tm u z a)) /\
  (forall P p a, Grade P p a ->
    forall Q z u, lc_tm u -> grade_subst_map P Q p z u ->
    Grade Q p (subst_tm_tm u z a)).
Proof.
  apply grading_ind; intros.
  - apply CG_Leq; eauto.
  - apply CG_Nleq; eauto using subst_lc; subst_grade_uniq.
  - apply G_Type; subst_grade_uniq.
  - match goal with M : grade_subst_map _ _ _ _ _, B : binds _ ?r _,
                    J : ?r <= _ |- _ => exact (proj2 M _ _ B J) end.
  - cbn [subst_tm_tm]; use_subst_binder G_Pi L Q z.
  - cbn [subst_tm_tm]; use_subst_binder G_Abs L Q z.
  - cbn; apply G_App; eauto.
  - cbn [subst_tm_tm]; use_subst_binder G_WSigma L Q z.
  - cbn; apply G_WPair; eauto.
  - cbn [subst_tm_tm]; use_subst_binder G_LetPair L Q z.
  - cbn [subst_tm_tm]; use_subst_binder G_SSigma L Q z.
  - cbn; apply G_SPair; eauto.
  - cbn; apply G_Proj1; eauto.
  - cbn; apply G_Proj2; eauto.
  - cbn; apply G_Sum; eauto.
  - cbn; apply G_Inj1; eauto.
  - cbn; apply G_Inj2; eauto.
  - cbn; apply G_Case; eauto.
  - cbn; apply G_TyUnit; subst_grade_uniq.
  - cbn; apply G_TmUnit; subst_grade_uniq.
Qed.

Lemma grade_substitute : forall P Q p a z u, Grade P p a -> lc_tm u ->
  grade_subst_map P Q p z u -> Grade Q p (subst_tm_tm u z a).
Proof. intros; eapply (proj2 grading_substitution); eauto. Qed.

Lemma defequality_substitution :
  (forall P p q a b, CDefEq P p q a b ->
    forall Q z u, lc_tm u -> grade_subst_map P Q p z u ->
    CDefEq Q p q (subst_tm_tm u z a) (subst_tm_tm u z b)) /\
  (forall P p a b, DefEq P p a b ->
    forall Q z u, lc_tm u -> grade_subst_map P Q p z u ->
    DefEq Q p (subst_tm_tm u z a) (subst_tm_tm u z b)).
Proof.
  apply defequality_ind; intros; rewrite ?subst_open by auto; cbn [subst_tm_tm].
  - eapply CDefEq_Leq; eauto.
  - eapply CDefEq_Nleq; eauto using subst_lc; subst_grade_uniq.
  - apply Eq_Refl; eauto using grade_substitute.
  - eapply Eq_Trans; eauto.
  - apply Eq_Sym; eauto.
  - apply Eq_Beta; eauto using grade_substitute, step_subst.
  - use_subst_binder Eq_Pi L Q z.
  - use_subst_binder Eq_Abs L Q z.
  - eapply Eq_App; eauto.
  - eapply Eq_PiFst; eauto.
  - eapply Eq_PiSnd; eauto.
  - use_subst_binder Eq_WSigma L Q z.
  - eapply Eq_WSigmaFst; eauto.
  - eapply Eq_WSigmaSnd; eauto using grade_substitute.
  - eapply Eq_WPair; eauto.
  - use_subst_binder Eq_LetPair L Q z.
  - use_subst_binder Eq_SSigma L Q z.
  - eapply Eq_SSigmaFst; eauto.
  - eapply Eq_SSigmaSnd; eauto.
  - eapply Eq_SPair; eauto.
  - eapply Eq_Proj1; eauto.
  - eapply Eq_Proj2; eauto.
  - eapply Eq_Sum; eauto.
  - eapply Eq_SumFst; eauto.
  - eapply Eq_SumSnd; eauto.
  - eapply Eq_Inj1; eauto.
  - eapply Eq_Inj2; eauto.
  - eapply Eq_Case; eauto.
  - apply Eq_TyUnit; subst_grade_uniq.
  - apply Eq_TmUnit; subst_grade_uniq.
  - eapply Eq_SubstIrrel with (L := L \u dom Q \u {{z}}) (psi := psi);
      eauto using subst_lc.
    subst_grade_body L.
Qed.

Lemma defeq_substitute : forall P Q p a b z u, DefEq P p a b -> lc_tm u ->
  grade_subst_map P Q p z u -> DefEq Q p (subst_tm_tm u z a) (subst_tm_tm u z b).
Proof. intros; eapply (proj2 defequality_substitution); eauto. Qed.

Lemma typing_demote : forall W p a A, Typing W p a A -> uniq W ->
  Typing (meet_ctx_l q_C W) p a A.
Proof.
  intros; pose proof (@typing_transport W p a A H q_Bot (meet_ctx_l q_C W) (bot_le _)) as J.
  rewrite join_bot in J; apply J; split; auto using uniq_meet.
  intros; eexists; split; eauto using meet_bind; rewrite join_bot; apply meet_right.
Qed.

(* Substitution must transport variable typings in both the original
   context and its meet with q_C, which is used for type conversion. *)
Record typing_subst_map (z : atom) (u : tm) (W V : context) : Prop := {
  tsm_uniq : uniq V;
  tsm_var : forall x r A p, binds x (r,A) W -> r <= p -> p <= q_C ->
    Typing V p (subst_tm_tm u z (a_Var_f x)) (subst_tm_tm u z A);
  tsm_cap : forall x r A p, binds x (r,A) W -> q_C + r <= p -> p <= q_C ->
    Typing (meet_ctx_l q_C V) p (subst_tm_tm u z (a_Var_f x)) (subst_tm_tm u z A)
}.

Lemma typing_subst_map_meet : forall z u W V, typing_subst_map z u W V ->
  typing_subst_map z u (meet_ctx_l q_C W) (meet_ctx_l q_C V).
Proof.
  intros z u W V [U F G]; constructor; auto using uniq_meet.
  - intros x r A p H R B; destruct (meet_bind_inv H) as [q [Hq ->]].
    eauto.
  - rewrite meet_id; intros x r A p H R B; destruct (meet_bind_inv H) as [q [Hq ->]].
    rewrite meet_assoc, meet_idem in R; eauto.
Qed.

Lemma typing_subst_map_grades : forall z u W V, typing_subst_map z u W V ->
  grade_subst_map (labels (meet_ctx_l q_C W)) (labels (meet_ctx_l q_C V)) q_C z u.
Proof.
  intros z u W V [U F G]; split; auto using uniq_meet, uniq_labels.
  intros x r H R.
  destruct (labels_bind_inv H) as [A H'].
  destruct (meet_bind_inv H') as [q [Hq ->]].
  eapply typed_grade; eauto using grade_refl.
Qed.

Lemma typing_subst_map_cons : forall z u W V x r A,
  typing_subst_map z u W V -> x <> z -> x \notin dom V ->
  typing_subst_map z u ((x,(r,A))::W) ((x,(r,subst_tm_tm u z A))::V).
Proof.
  intros z u W V x r A [U F G] Ne Fr.
  assert (Uv : uniq ((x,(r,subst_tm_tm u z A))::V)) by auto using uniq_cons.
  constructor; auto.
  - intros y q B p [E|E] Hq Hp.
    + inversion E; subst; cbn.
      match goal with |- context [if ?d then _ else _] => destruct d end; try congruence.
      eapply T_Var; eauto; simpl; auto.
    + eapply typing_weaken; eauto; simpl; auto.
  - intros y q B p [E|E] Hq Hp.
    + inversion E; subst; cbn.
      match goal with |- context [if ?d then _ else _] => destruct d end; try congruence.
      eapply T_Var; [exact (uniq_meet Uv)|exact Hq|left; reflexivity|exact Hp].
    + eapply typing_weaken with (W := meet_ctx_l q_C V).
      * eauto.
      * exact (uniq_meet Uv).
      * intros; right; assumption.
Qed.

Lemma notin_meet : forall x W, x \notin dom W -> x \notin dom (meet_ctx_l q_C W).
Proof. intros; rewrite dom_meet; assumption. Qed.

Local Hint Resolve typing_subst_map_meet typing_subst_map_grades notin_meet : ddc.

Local Ltac subst_renormalize H :=
  rewrite ?subst_open in H by assumption;
  cbn [subst_tm_tm] in H;
  repeat match type of H with context [if ?d then _ else _] => destruct d; try congruence end.

Local Ltac typing_subst_binder L V z :=
  intros x Fx;
  let F := fresh "F" in let Z := fresh "Z" in let Vx := fresh "Vx" in
  (assert (F : x \notin L) by fsetdec);
  (assert (Z : x <> z) by fsetdec);
  (assert (Vx : x \notin dom V) by fsetdec);
  repeat rewrite <- subst_open_var by assumption;
  match goal with
  | IH : forall y, y \notin L -> forall V z u, lc_tm u ->
       typing_subst_map z u _ V -> _ |- _ =>
       eapply (IH x F); [assumption|]
  end;
  apply typing_subst_map_cons; [eauto with ddc|exact Z|eauto with ddc].

Lemma typing_substitute : forall W p a A, Typing W p a A ->
  forall V z u, lc_tm u -> typing_subst_map z u W V ->
  Typing V p (subst_tm_tm u z a) (subst_tm_tm u z A).
Proof.
  induction 1; intros V z u Hlc M; rewrite ?subst_open by assumption; cbn [subst_tm_tm].
  - apply T_Type; eauto using tsm_uniq.
  - eapply T_Conv; eauto using defeq_substitute with ddc.
  - eapply tsm_var; eauto.
  - eapply T_Pi with (L := L \u dom V \u {{z}}); eauto.
    typing_subst_binder L V z.
  - eapply T_Abs with (L := L \u dom V \u {{z}}); eauto with ddc.
    typing_subst_binder L V z.
  - eapply T_App; eauto.
  - eapply T_AppIrrel; eauto with ddc.
  - eapply T_WSigma with (L := L \u dom V \u {{z}}); eauto.
    typing_subst_binder L V z.
  - eapply T_WPair; eauto with ddc.
    rewrite <- subst_open by assumption; eauto.
  - eapply T_WPairIrrel; eauto with ddc.
    rewrite <- subst_open by assumption; eauto.
  - eapply T_LetPair with (L := L \u dom V \u {{z}} \u fv_tm_tm u); eauto.
    + typing_subst_binder L V z.
    + intros x Fx y Fy.
      assert (F : x \notin L) by fsetdec.
      assert (G : y \notin L \u {{x}}) by fsetdec.
      assert (Zx : x <> z) by fsetdec.
      assert (Zy : z <> y) by fsetdec.
      assert (Uy : y \notin fv_tm_tm u) by fsetdec.
      assert (Vx : x \notin dom V) by fsetdec.
      pose proof (H3 x F y G _ _ _ Hlc (@typing_subst_map_cons z u W V x (psi0 * psi) A M Zx Vx)) as J.
      cbn [subst_tm_tm] in J.
      unfold close_tm_wrt_tm in *.
      rewrite subst_close_rec in J by (auto using lc_scoped).
      subst_renormalize J; exact J.
  - eapply T_SSigma with (L := L \u dom V \u {{z}}); eauto.
    typing_subst_binder L V z.
  - eapply T_SPair; eauto with ddc.
    rewrite <- subst_open by assumption; eauto.
  - eapply T_Proj1; eauto.
  - eapply T_Proj2; eauto.
  - eapply T_Sum; eauto.
  - eapply T_Inj1; eauto with ddc.
  - eapply T_Inj2; eauto with ddc.
  - eapply T_Case with (L := L \u dom V \u {{z}}); eauto.
    + typing_subst_binder L V z.
    + intros x Fx.
      pose proof (f_equal (subst_tm_tm u z) (H2 x ltac:(fsetdec))) as J.
      assert (x <> z) by fsetdec.
      subst_renormalize J; exact J.
    + intros x Fx.
      pose proof (f_equal (subst_tm_tm u z) (H3 x ltac:(fsetdec))) as J.
      assert (x <> z) by fsetdec.
      subst_renormalize J; exact J.
  - apply T_TmUnit; eauto using tsm_uniq.
  - apply T_TyUnit; eauto using tsm_uniq.
Qed.

Fixpoint context_fv (W : context) : vars :=
  match W with
  | nil => {}
  | (_,(_,A)) :: W => fv_tm_tm A \u context_fv W
  end.

Lemma context_fv_binds : forall W x r A z, binds x (r,A) W -> z \notin context_fv W ->
  z \notin fv_tm_tm A.
Proof.
  induction W as [|[y [q B]] W IH]; simpl; intros ? ? ? ? H F.
  - contradiction.
  - destruct H; [inversion H; subst; fsetdec|eapply IH; try eassumption; fsetdec].
Qed.

Definition suitable W r a A :=
  (forall p, r <= p -> p <= q_C -> Typing W p a A) /\
  (forall p, q_C + r <= p -> p <= q_C -> Typing (meet_ctx_l q_C W) p a A).

Lemma suitable_relevant : forall W r a A, Typing W r a A -> suitable W r a A.
Proof.
  intros W r a A T; split; intros p R C.
  - eapply typing_raise; [exact T|eauto using typing_uniq|exact R|exact C].
  - eapply typing_raise with (p := r).
    + eapply typing_demote; eauto using typing_uniq.
    + eauto using uniq_meet, typing_uniq.
    + rewrite (meet_cap (typing_bound T)) in R; exact R.
    + exact C.
Qed.

Lemma suitable_irrelevant : forall W r a A, q_C < r ->
  Typing (meet_ctx_l q_C W) q_C a A -> suitable W r a A.
Proof.
  intros W r a A [R N] H; split; intros p J Hp.
  - exfalso; apply N, grade_antisym; eauto with ddc.
  - rewrite (meet_leq _ _ R) in J.
    replace p with q_C by auto using grade_antisym; assumption.
Qed.

Lemma suitable_lc : forall W r a A, suitable W r a A -> lc_tm a.
Proof. intros; eapply typing_lc; apply (proj2 H q_C); eauto with ddc. Qed.

Lemma suitable_grade : forall W r a A, suitable W r a A ->
  Grade (labels (meet_ctx_l q_C W)) q_C a.
Proof. intros; eapply typed_grade; apply (proj2 H q_C); eauto with ddc. Qed.

Lemma top_subst_map : forall W x r a A, suitable W r a A -> uniq W ->
  x \notin (dom W \u context_fv W \u fv_tm_tm A) ->
  typing_subst_map x a ((x,(r,A))::W) W.
Proof.
  intros W x r a A [R I] U F; constructor; auto;
    intros y q B p [E|E] Hq Hp.
  - assert (J : y = x /\ q = r /\ B = A) by (inversion E; auto).
    destruct J as [-> [-> ->]].
    rewrite (@subst_fresh A a x) by fsetdec; cbn.
    match goal with |- context [if ?d then _ else _] => destruct d end; eauto; congruence.
  - rewrite (@subst_fresh B a x) by
      (eapply context_fv_binds; [eassumption|fsetdec]); cbn.
    match goal with |- context [if ?d then _ else _] => destruct d end; subst.
    + apply binds_In in E; exfalso; fsetdec.
    + eapply T_Var; eauto.
  - assert (J : y = x /\ q = r /\ B = A) by (inversion E; auto).
    destruct J as [-> [-> ->]].
    rewrite (@subst_fresh A a x) by fsetdec; cbn.
    match goal with |- context [if ?d then _ else _] => destruct d end; eauto; congruence.
  - rewrite (@subst_fresh B a x) by
      (eapply context_fv_binds; [eassumption|fsetdec]); cbn.
    match goal with |- context [if ?d then _ else _] => destruct d end; subst.
    + apply binds_In in E; exfalso; fsetdec.
    + eapply T_Var; eauto using uniq_meet, meet_bind.
Qed.

Lemma typing_instantiate : forall L W p r b B a A,
  uniq W -> suitable W r a A ->
  (forall x, x \notin L -> Typing ((x,(r,A))::W) p
     (open_tm_wrt_tm b (a_Var_f x)) (open_tm_wrt_tm B (a_Var_f x))) ->
  Typing W p (open_tm_wrt_tm b a) (open_tm_wrt_tm B a).
Proof.
  intros; pick fresh x for
    (L \u dom W \u context_fv W \u fv_tm_tm A \u fv_tm_tm b \u fv_tm_tm B).
  assert (M : typing_subst_map x a ((x,(r,A))::W) W) by
    (apply top_subst_map; auto; fsetdec).
  pose proof (typing_substitute (H1 x ltac:(fsetdec)) (suitable_lc H0) M) as J.
  rewrite !open_subst_intro in J by (eauto using suitable_lc; try fsetdec).
  exact J.
Qed.

(* Type validity supplies the well-formed target of each conversion. *)
Definition formed W p A := exists s, Typing W p A (a_Type s).

Lemma ctx_binding_formed : forall W, Ctx W -> forall x p A,
  binds x (p,A) W -> formed (meet_ctx_l q_C W) q_C A.
Proof.
  induction 1; intros y q B E; [inversion E|].
  assert (U : uniq (meet_ctx_l q_C ((x,(psi0,A))::W)))
    by (apply uniq_meet, uniq_cons; auto using ctx_uniq).
  destruct E as [E|E].
  - inversion E; subst; exists s; eapply typing_weaken; eauto; simpl; auto.
  - destruct (IHCtx _ _ _ E) as [t Ht].
    exists t; eapply typing_weaken; eauto; simpl; auto.
Qed.

Definition binder_formed W p A B :=
  formed W p A /\ exists L s, forall x, x \notin L ->
    Typing ((x,(p,A))::W) p (open_tm_wrt_tm B (a_Var_f x)) (a_Type s).

Lemma pi_formed : forall W p r A B T, Typing W p (a_Pi r A B) T -> binder_formed W p A B.
Proof.
  intros W p r A B T H; remember (a_Pi r A B) as t eqn:E;
    revert r A B E; induction H; intros; inversion E; subst.
  - eapply IHTyping1; reflexivity.
  - split; [unfold formed; eauto|exists L, s2; exact H0].
Qed.
Lemma wsigma_formed : forall W p r A B T, Typing W p (a_WSigma r A B) T -> binder_formed W p A B.
Proof.
  intros W p r A B T H; remember (a_WSigma r A B) as t eqn:E;
    revert r A B E; induction H; intros; inversion E; subst.
  - eapply IHTyping1; reflexivity.
  - split; [unfold formed; eauto|exists L, s2; exact H0].
Qed.
Lemma ssigma_formed : forall W p r A B T, Typing W p (a_SSigma r A B) T -> binder_formed W p A B.
Proof.
  intros W p r A B T H; remember (a_SSigma r A B) as t eqn:E;
    revert r A B E; induction H; intros; inversion E; subst.
  - eapply IHTyping1; reflexivity.
  - split; [unfold formed; eauto|exists L, s2; exact H0].
Qed.
Lemma sum_formed : forall W p A B T, Typing W p (a_Sum A B) T ->
  formed W p A /\ formed W p B.
Proof.
  intros W p A B T H; remember (a_Sum A B) as t eqn:E;
    revert A B E; induction H; intros; inversion E; subst.
  - eapply IHTyping1; reflexivity.
  - unfold formed; split; eauto.
Qed.

Lemma formed_open : forall L W p A B s a, suitable W p a A ->
  (forall x, x \notin L -> Typing ((x,(p,A))::W) p
    (open_tm_wrt_tm B (a_Var_f x)) (a_Type s)) ->
  Typing W p (open_tm_wrt_tm B a) (a_Type s).
Proof.
  intros L W p A B s a Harg Hbody.
  assert (Hbound : p <= q_C).
  { pick fresh x for L; exact (typing_bound (Hbody x Fr)). }
  assert (U : uniq W) by exact (typing_uniq (proj1 Harg p (grade_refl p) Hbound)).
  change (Typing W p (open_tm_wrt_tm B a) (open_tm_wrt_tm (a_Type s) a)).
  eapply typing_instantiate; eauto.
Qed.

Lemma binder_formed_open : forall W p A B a, binder_formed W p A B ->
  Typing W p a A -> formed W p (open_tm_wrt_tm B a).
Proof.
  intros ? ? ? ? ? [_ [L [s H]]] J.
  exists s; eapply formed_open; eauto using suitable_relevant.
Qed.

Lemma typing_formed : forall W p a A, Typing W p a A -> Ctx W ->
  formed (meet_ctx_l q_C W) q_C A.
Proof.
  induction 1; intro HC;
    try solve [unfold formed; eauto];
    try solve [unfold formed; destruct (sort_regularity s3) as [t J];
               eauto using T_Type, grade_refl, uniq_meet, ctx_uniq];
    try solve [unfold formed; destruct (sort_regularity s) as [t J];
               eauto using T_Type, grade_refl, uniq_meet, ctx_uniq].
  - destruct (sort_regularity s2) as [t J]; exists t;
      eauto using T_Type, grade_refl, uniq_meet, ctx_uniq.
  - eauto using ctx_binding_formed.
  - destruct (IHTyping1 HC) as [t J]; eapply binder_formed_open;
      eauto using pi_formed, typing_meet, ctx_uniq.
  - destruct (IHTyping1 HC) as [t J]; eapply binder_formed_open;
      eauto using pi_formed, typing_meet, ctx_uniq.
  - exists s; eapply formed_open; eauto using suitable_relevant, typing_meet, ctx_uniq.
  - destruct (IHTyping HC) as [t J]; exact (proj1 (ssigma_formed J)).
  - destruct (IHTyping HC) as [t J]; eapply binder_formed_open;
      eauto using ssigma_formed.
    eapply T_Proj1; eauto using typing_meet, ctx_uniq.
  - exists s; eapply formed_open; eauto using suitable_relevant, typing_meet, ctx_uniq.
  - exists star; eauto using T_TmUnit, grade_refl, uniq_meet, ctx_uniq.
Qed.

Definition cap_eq W := DefEq (labels (meet_ctx_l q_C W)) q_C.

Lemma formed_refl : forall W A, formed (meet_ctx_l q_C W) q_C A -> cap_eq W A A.
Proof. intros W A [s H]; apply Eq_Refl; eauto using typed_grade. Qed.

Lemma typing_convert : forall W p a A B, Typing W p a A -> cap_eq W A B ->
  formed (meet_ctx_l q_C W) q_C B -> Typing W p a B.
Proof. intros ? ? ? ? ? H E [s J]; eauto using T_Conv. Qed.

Lemma suitable_convert : forall W p a A B, suitable W p a A -> cap_eq W A B ->
  formed (meet_ctx_l q_C W) q_C B -> suitable W p a B.
Proof.
  intros W p a A B [R I] E Hf; split; intros.
  - eauto using typing_convert.
  - eapply typing_convert.
    + eapply I; eassumption.
    + unfold cap_eq in *; rewrite meet_id; exact E.
    + rewrite meet_id; exact Hf.
Qed.

Lemma cap_eq_step : forall W p a b A, Typing W p a A -> Typing W p b A ->
  Step a b -> cap_eq W a b.
Proof. unfold cap_eq; eauto using Eq_Beta, cap_typing_grade. Qed.

Lemma cap_eq_open : forall L W A B s a b,
  (forall x, x \notin L -> Typing ((x,(q_C,A))::meet_ctx_l q_C W) q_C
    (open_tm_wrt_tm B (a_Var_f x)) (a_Type s)) ->
  uniq W -> cap_eq W a b -> cap_eq W (open_tm_wrt_tm B a) (open_tm_wrt_tm B b).
Proof.
  intros; unfold cap_eq in *.
  eapply Eq_PiSnd with (psi0 := q_C) (A1 := a_TyUnit) (A2 := a_TyUnit); eauto.
  apply Eq_Refl; eapply G_Pi with (L := L).
  - apply G_TyUnit; auto using uniq_meet, uniq_labels.
  - intros x Fx; exact (typed_grade (H x Fx)).
Qed.

Lemma grade_high_join : forall r p, q_C < r -> q_C < r * p.
Proof.
  intros r p [R N]; split; eauto with ddc.
  intro E; apply N, grade_antisym; auto.
  rewrite E; apply join_left.
Qed.

Definition introduced W p a A : Prop :=
  match a, A with
  | a_Abs g D b, a_Pi r F B =>
      g = r /\ D = F /\ formed (meet_ctx_l q_C W) q_C A /\
      exists L, forall x, x \notin L ->
        Typing ((x,(g*p,D))::W) p (open_tm_wrt_tm b (a_Var_f x))
                                  (open_tm_wrt_tm B (a_Var_f x))
  | a_WPair u g v, a_WSigma r F B =>
      g = r /\ formed (meet_ctx_l q_C W) q_C A /\
      suitable W (g*p) u F /\ Typing W p v (open_tm_wrt_tm B u)
  | a_SPair u g v, a_SSigma r F B =>
      g = r /\ formed (meet_ctx_l q_C W) q_C A /\
      Typing W (g*p) u F /\ Typing W p v (open_tm_wrt_tm B u)
  | a_Inj1 u, a_Sum F B =>
      formed (meet_ctx_l q_C W) q_C A /\ Typing W p u F
  | a_Inj2 u, a_Sum F B =>
      formed (meet_ctx_l q_C W) q_C A /\ Typing W p u B
  | _, _ => False
  end.

Definition is_intro a :=
  match a with
  | a_Abs _ _ _ | a_WPair _ _ _ | a_SPair _ _ _ | a_Inj1 _ | a_Inj2 _ => True
  | _ => False
  end.

Lemma intro_generation : forall W p a A, Typing W p a A -> is_intro a ->
  exists B, introduced W p a B /\ cap_eq W B A.
Proof.
  induction 1; cbn [is_intro]; intro I; try contradiction.
  - destruct (IHTyping1 I) as [D [J E]]; exists D; split; auto.
    unfold cap_eq in *; eapply Eq_Trans; eassumption.
  - exists (a_Pi psi0 A B); split.
    + cbn [introduced]; repeat split; eauto; exists s; assumption.
    + apply formed_refl; exists s; assumption.
  - exists (a_WSigma psi0 A B); split.
    + cbn [introduced]; split; [reflexivity|]; split; [exists s; assumption|].
      split; eauto using suitable_relevant.
    + apply formed_refl; exists s; assumption.
  - exists (a_WSigma psi0 A B); split.
    + cbn [introduced]; split; [reflexivity|]; split; [exists s; assumption|].
      split; eauto using suitable_irrelevant, grade_high_join.
    + apply formed_refl; exists s; assumption.
  - exists (a_SSigma psi0 A B); split.
    + cbn [introduced]; repeat split; auto; exists s; assumption.
    + apply formed_refl; exists s; assumption.
  - exists (a_Sum A1 A2); split.
    + cbn [introduced]; split; [exists s; assumption|assumption].
    + apply formed_refl; exists s; assumption.
  - exists (a_Sum A1 A2); split.
    + cbn [introduced]; split; [exists s; assumption|assumption].
    + apply formed_refl; exists s; assumption.
Qed.

Lemma pi_beta_preservation : forall W p r D b a A B,
  Ctx W -> Typing W p (a_Abs r D b) (a_Pi r A B) -> suitable W (r*p) a A ->
  Typing W p (open_tm_wrt_tm b a) (open_tm_wrt_tm B a).
Proof.
  intros W p r D b a A B HC Hf Ha.
  destruct (intro_generation Hf I) as [F [J E]].
  destruct F; cbn [introduced] in J; try contradiction.
  destruct J as [Rg [Ed [[s Hs] [L Hb]]]]; subst psi F1.
  assert (HD : formed (meet_ctx_l q_C W) q_C D)
    by exact (proj1 (pi_formed Hs)).
  assert (HDarg : suitable W (r*p) a D).
  { eapply suitable_convert; eauto.
    apply Eq_Sym; eapply Eq_PiFst; exact E. }
  eapply typing_convert.
  - eapply typing_instantiate; eauto using ctx_uniq.
  - eapply Eq_PiSnd; [exact E|apply Eq_Refl; eauto using suitable_grade].
  - destruct (typing_formed Hf HC) as [s' Hs'].
    eapply binder_formed_open; [exact (pi_formed Hs')|].
    apply (proj2 Ha); eauto with ddc.
Qed.

Lemma wpair_components : forall W p r a b A B, Ctx W ->
  Typing W p (a_WPair a r b) (a_WSigma r A B) ->
  suitable W (r*p) a A /\ Typing W p b (open_tm_wrt_tm B a).
Proof.
  intros W p r a b A B HC H.
  destruct (intro_generation H I) as [F [J E]].
  destruct F; cbn [introduced] in J; try contradiction.
  destruct J as [J [V [S T]]]; subst psi.
  destruct (typing_formed H HC) as [s Hs].
  pose proof (wsigma_formed Hs) as Hform.
  assert (Sa : suitable W (r*p) a A).
  { eapply suitable_convert; [exact S|eapply Eq_WSigmaFst; exact E|exact (proj1 Hform)]. }
  split; [exact Sa|].
  eapply typing_convert; [exact T|eapply Eq_WSigmaSnd; [exact E|eauto using suitable_grade]|].
  eapply binder_formed_open; [exact Hform|].
  apply (proj2 Sa); eauto with ddc.
Qed.

Lemma spair_components : forall W p r a b A B, Ctx W ->
  Typing W p (a_SPair a r b) (a_SSigma r A B) ->
  Typing W (r*p) a A /\ Typing W p b (open_tm_wrt_tm B a).
Proof.
  intros W p r a b A B HC H.
  destruct (intro_generation H I) as [F [J E]].
  destruct F; cbn [introduced] in J; try contradiction.
  destruct J as [J [V [S T]]]; subst psi.
  destruct (typing_formed H HC) as [s Hs].
  pose proof (ssigma_formed Hs) as Hform.
  assert (U : Typing W (r*p) a A).
  { eapply typing_convert; [exact S|eapply Eq_SSigmaFst; exact E|exact (proj1 Hform)]. }
  split; auto.
  eapply typing_convert; [exact T| |].
  - eapply Eq_SSigmaSnd; [exact E|apply Eq_Refl; eauto using cap_typing_grade].
  - eapply binder_formed_open; eauto using typing_meet, ctx_uniq.
Qed.

Lemma inj1_component : forall W p a A B, Ctx W ->
  Typing W p (a_Inj1 a) (a_Sum A B) -> Typing W p a A.
Proof.
  intros W p a A B HC H.
  destruct (intro_generation H I) as [F [J E]].
  destruct F; cbn [introduced] in J; try contradiction.
  destruct J as [_ S].
  destruct (typing_formed H HC) as [s Hs].
  eapply typing_convert; [exact S|eapply Eq_SumFst; exact E|exact (proj1 (sum_formed Hs))].
Qed.

Lemma inj2_component : forall W p a A B, Ctx W ->
  Typing W p (a_Inj2 a) (a_Sum A B) -> Typing W p a B.
Proof.
  intros W p a A B HC H.
  destruct (intro_generation H I) as [F [J E]].
  destruct F; cbn [introduced] in J; try contradiction.
  destruct J as [_ S].
  destruct (typing_formed H HC) as [s Hs].
  eapply typing_convert; [exact S|eapply Eq_SumSnd; exact E|exact (proj2 (sum_formed Hs))].
Qed.

Lemma case_family_left : forall L B B1 a,
  (forall x, x \notin L -> open_tm_wrt_tm B1 (a_Var_f x) =
                           open_tm_wrt_tm B (a_Inj1 (a_Var_f x))) ->
  lc_tm a -> open_tm_wrt_tm B1 a = open_tm_wrt_tm B (a_Inj1 a).
Proof.
  intros; pick fresh x for (L \u fv_tm_tm B \u fv_tm_tm B1).
  pose proof (f_equal (subst_tm_tm a x) (H x ltac:(fsetdec))) as J.
  rewrite open_subst_intro in J by (auto; fsetdec).
  rewrite subst_open in J by auto.
  rewrite (@subst_fresh B a x) in J by fsetdec.
  cbn [subst_tm_tm] in J.
  match type of J with context [if ?d then _ else _] => destruct d end; congruence.
Qed.
Lemma case_family_right : forall L B B2 a,
  (forall x, x \notin L -> open_tm_wrt_tm B2 (a_Var_f x) =
                           open_tm_wrt_tm B (a_Inj2 (a_Var_f x))) ->
  lc_tm a -> open_tm_wrt_tm B2 a = open_tm_wrt_tm B (a_Inj2 a).
Proof.
  intros; pick fresh x for (L \u fv_tm_tm B \u fv_tm_tm B2).
  pose proof (f_equal (subst_tm_tm a x) (H x ltac:(fsetdec))) as J.
  rewrite open_subst_intro in J by (auto; fsetdec).
  rewrite subst_open in J by auto.
  rewrite (@subst_fresh B a x) in J by fsetdec.
  cbn [subst_tm_tm] in J.
  match type of J with context [if ?d then _ else _] => destruct d end; congruence.
Qed.

Lemma close_removes : forall a n y, y \notin fv_tm_tm (close_tm_wrt_tm_rec n y a).
Proof.
  intro a; induction a; cbn; intros;
    try solve [repeat apply notin_union; repeat split; auto; fsetdec].
  - indices; cbn; fsetdec.
  - match goal with |- context [if ?d then _ else _] => destruct d end; subst; cbn; fsetdec.
Qed.

Lemma open_close_subst : forall a b x, lc_tm b ->
  open_tm_wrt_tm (close_tm_wrt_tm x a) b = subst_tm_tm b x a.
Proof.
  intros a b x H.
  rewrite <- (@open_subst_intro (close_tm_wrt_tm x a) b x (@close_removes a 0 x) H).
  unfold open_tm_wrt_tm, close_tm_wrt_tm; now rewrite open_close_rec.
Qed.

Lemma letpair_beta_preservation : forall L W p r a b c C A B,
  Ctx W -> suitable W (r*p) a A -> Typing W p b (open_tm_wrt_tm B a) ->
  (forall x, x \notin L -> forall y, y \notin L \u {{x}} ->
      Typing ((x,(r*p,A))::W) p (open_tm_wrt_tm c (a_Var_f x))
        (a_Pi q_Bot (open_tm_wrt_tm B (a_Var_f x))
          (close_tm_wrt_tm y (open_tm_wrt_tm C (a_WPair (a_Var_f x) r (a_Var_f y)))))) ->
  Typing W p (a_App (open_tm_wrt_tm c a) q_Bot b)
    (open_tm_wrt_tm C (a_WPair a r b)).
Proof.
  intros L W p r a b c C A B HC Ha Hb Hk.
  pose proof (suitable_lc Ha) as La.
  pose proof (typing_lc Hb) as Lb.
  pick fresh y for (L \u fv_tm_tm a \u fv_tm_tm C).
  pick fresh x for
    (L \u dom W \u context_fv W \u fv_tm_tm A \u fv_tm_tm c \u fv_tm_tm B \u
     fv_tm_tm C \u {{y}}).
  assert (M : typing_subst_map x a ((x,(r*p,A))::W) W) by
    (apply top_subst_map; eauto using ctx_uniq; fsetdec).
  pose proof (typing_substitute (Hk x ltac:(fsetdec) y ltac:(fsetdec)) La M) as J.
  cbn [subst_tm_tm] in J.
  rewrite !open_subst_intro in J by (auto; fsetdec).
  unfold close_tm_wrt_tm in J.
  rewrite subst_close_rec, subst_open in J by (auto using lc_scoped; fsetdec).
  rewrite (@subst_fresh C a x) in J by fsetdec.
  assert (y <> x) by fsetdec.
  subst_renormalize J.
  let D := match type of J with Typing _ _ _ (a_Pi _ _ ?D) => D end in
  change (close_tm_wrt_tm y (open_tm_wrt_tm C (a_WPair a r (a_Var_f y)))) with D in J.
  pose proof (@T_App W p _ q_Bot b _ _ J ltac:(rewrite join_comm, join_bot; exact Hb) (bot_le _)) as R.
  rewrite open_close_subst, subst_open in R by auto.
  cbn [subst_tm_tm] in R.
  rewrite (@subst_fresh C b y), (@subst_fresh a b y) in R by fsetdec.
  cbn [subst_tm_tm] in R.
  (* The substitution in the pair's second component replaces its fresh variable. *)
  repeat match type of R with context [if ?d then _ else _] => destruct d; try congruence end.
Qed.

Lemma proj1_cap_eq : forall W p r a a' A B,
  Typing W p a (a_SSigma r A B) -> Typing W p a' (a_SSigma r A B) ->
  r <= q_C -> Step a a' -> cap_eq W (a_Proj1 r a) (a_Proj1 r a').
Proof.
  intros W p r a a' A B H J Hr S.
  apply Eq_Proj1; [exact (cap_eq_step H J S)|exact Hr].
Qed.

Lemma proj2_conversion : forall W p r a A B u,
  Ctx W -> Typing W p a (a_SSigma r A B) -> r <= q_C ->
  cap_eq W u (a_Proj1 r a) ->
  cap_eq W (open_tm_wrt_tm B u) (open_tm_wrt_tm B (a_Proj1 r a)).
Proof.
  intros W p r a A B u HC H Hr E.
  eapply Eq_SSigmaSnd with (psi0 := r) (A1 := A) (A2 := A); [|exact E].
  exact (@formed_refl W (a_SSigma r A B) (typing_formed H HC)).
Qed.

Lemma proj1_beta_eq : forall W p r a b A B,
  Typing W p (a_SPair a r b) (a_SSigma r A B) ->
  Typing W (r*p) a A -> r <= q_C ->
  lc_tm b -> cap_eq W (a_Proj1 r (a_SPair a r b)) a.
Proof.
  intros; apply Eq_Beta.
  - apply G_Proj1; eauto using cap_typing_grade.
  - apply S_Proj1Beta; eauto using typing_lc.
  - eauto using cap_typing_grade.
Qed.

Theorem Typing_preservation :
  forall W psi a A, Typing W psi a A -> Ctx W ->
  forall b, Step a b -> Typing W psi b A.
Proof.
  intros W p a A H; induction H; intros HC a' S;
    try solve [inversion S].
  - eapply T_Conv; eauto.
  - inversion S; subst.
    + eapply T_App; eauto.
    + eapply pi_beta_preservation; eauto using suitable_relevant.
  - inversion S; subst.
    + eapply T_AppIrrel; eauto.
    + eapply pi_beta_preservation; eauto using suitable_irrelevant, grade_high_join.
  - inversion S; subst.
    + assert (Ta' : Typing W psi a'0 (a_WSigma psi0 A B)) by eauto.
      eapply typing_convert.
      * eapply T_LetPair with (L := L); eauto.
      * refine (@cap_eq_open L W (a_WSigma psi0 A B) C s a'0 a H (ctx_uniq HC) _).
        apply Eq_Sym; eapply cap_eq_step; eassumption.
      * exists s; eapply (@formed_open L _ q_C (a_WSigma psi0 A B) C s a).
        -- apply suitable_relevant; eauto using typing_meet, ctx_uniq.
        -- exact H.
    + destruct (wpair_components HC H1) as [Ha Hb].
      eapply letpair_beta_preservation with (L := L); eauto.
  - inversion S; subst.
    + eapply T_Proj1; eauto.
    + destruct (spair_components HC H) as [Ha Hb].
      rewrite (join_leq _ _ H0) in Ha; exact Ha.
  - assert (V : formed (meet_ctx_l q_C W) q_C (open_tm_wrt_tm B (a_Proj1 psi0 a))).
    { eapply typing_formed; eauto using T_Proj2. }
    inversion S; subst.
    + assert (Ta' : Typing W psi a'0 (a_SSigma psi0 A B)) by eauto.
      eapply typing_convert; [eapply T_Proj2; eauto| |exact V].
      eapply proj2_conversion; [exact HC|exact H|eassumption|].
      apply Eq_Sym; eapply proj1_cap_eq; eassumption.
    + destruct (spair_components HC H) as [Ha Hb].
      eapply typing_convert; [exact Hb| |exact V].
      eapply proj2_conversion; [exact HC|exact H|eassumption|].
      apply Eq_Sym; eapply proj1_beta_eq; eassumption.
  - inversion S; subst.
    + assert (Ta' : Typing W psi a'0 (a_Sum A1 A2)) by eauto.
      eapply typing_convert.
      * eapply T_Case with (L := L); eauto.
      * refine (@cap_eq_open L W (a_Sum A1 A2) B s a'0 a H (ctx_uniq HC) _).
        apply Eq_Sym; eapply cap_eq_step; eassumption.
      * exists s; eapply (@formed_open L _ q_C (a_Sum A1 A2) B s a).
        -- apply suitable_relevant; eauto using typing_meet, ctx_uniq.
        -- exact H.
    + erewrite <- case_family_left by eassumption.
      eapply T_App; [eassumption| |eauto using typing_bound, grade_trans].
      match goal with Hle : psi0 <= psi |- _ => rewrite (join_leq _ _ Hle) end;
      eauto using inj1_component.
    + erewrite <- case_family_right by eassumption.
      eapply T_App; [eassumption| |eauto using typing_bound, grade_trans].
      match goal with Hle : psi0 <= psi |- _ => rewrite (join_leq _ _ Hle) end;
      eauto using inj2_component.
Qed.

Theorem Typing_progress :
  forall psi a A, Typing nil psi a A -> (exists a', Step a a') \/ Value a.
Proof. eauto using typing_progress_closed. Qed.
