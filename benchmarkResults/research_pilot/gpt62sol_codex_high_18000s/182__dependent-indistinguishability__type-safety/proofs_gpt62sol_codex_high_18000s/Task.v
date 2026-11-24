From Qual Require Import Qualitative_ott.
Require Import Metalib.Metatheory.
From mathcomp Require Import ssreflect ssrbool.
From Stdlib Require Import Lia.

Set Implicit Arguments.

Unset Strict Implicit.

Unset Printing Implicit Defensive.

Local Open Scope order_scope.
Local Close Scope bool_scope.

Local Hint Constructors lc_tm Par CPar : safety.
Local Hint Constructors Typing Ctx : typing_rules.
Local Hint Constructors Red : reduction_rules.
Local Hint Resolve Order.POrderTheory.lexx Order.POrderTheory.le_trans : safety.

(* Opening, substitution, and local closure. *)
Fixpoint scoped (k : nat) (a : tm) : Prop :=
  match a with
  | a_Var_b i => i < k
  | a_Pi _ A B | a_Abs _ A B | a_SSigma _ A B =>
      scoped k A /\ scoped (S k) B
  | a_App a _ b | a_SPair a _ b | a_Transp a b =>
      scoped k a /\ scoped k b
  | a_CEq _ a b _ A | a_If a b A =>
      scoped k a /\ scoped k b /\ scoped k A
  | a_T _ a | a_Box _ a | a_Unbox _ a | a_Proj1 _ a | a_Proj2 _ a =>
      scoped k a
  | _ => True
  end%nat.

Lemma scoped_mono : forall a k j, (k <= j)%nat -> scoped k a -> scoped j a.
Proof.
  induction a; simpl; intros;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat split; eauto with arith; try lia.
Qed.

Lemma scoped_open_inv : forall a k x,
  scoped k (open_tm_wrt_tm_rec k (a_Var_f x) a) -> scoped (S k) a.
Proof.
  induction a; simpl; intros;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat split; eauto.
  destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl in *; lia.
Qed.

Lemma scoped_open : forall a u k,
  scoped (S k) a -> scoped 0 u -> scoped k (open_tm_wrt_tm_rec k u a).
Proof.
  induction a; simpl; intros;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat split; eauto.
  destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl in *;
    try lia; eauto using scoped_mono with arith.
Qed.

Lemma scoped_open_id : forall a k u, scoped k a -> open_tm_wrt_tm_rec k u a = a.
Proof.
  induction a; simpl; intros;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    f_equal; eauto.
  destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl in *; auto; lia.
Qed.

Lemma lc_scoped : forall a, lc_tm a -> scoped 0 a.
Proof.
  induction 1; simpl; repeat split; eauto.
  all: destruct (atom_fresh AtomSetImpl.empty) as [z _];
    eapply (@scoped_open_inv _ 0 z); eauto.
Qed.

Fixpoint tm_size (a : tm) : nat :=
  match a with
  | a_Pi _ A B | a_Abs _ A B | a_SSigma _ A B
  | a_App A _ B | a_SPair A _ B | a_Transp A B => S (tm_size A + tm_size B)
  | a_CEq _ a b _ A | a_If a b A => S (tm_size a + tm_size b + tm_size A)
  | a_T _ a | a_Box _ a | a_Unbox _ a | a_Proj1 _ a | a_Proj2 _ a => S (tm_size a)
  | _ => 1
  end.

Lemma size_open_var : forall a k x,
  tm_size (open_tm_wrt_tm_rec k (a_Var_f x) a) = tm_size a.
Proof.
  induction a; simpl; intros; try rewrite IHa; try rewrite IHa1; try rewrite IHa2;
    try rewrite IHa3; auto.
  destruct (lt_eq_lt_dec n k) as [[?|?]|?]; auto.
Qed.

Lemma scoped_lc : forall a, scoped 0 a -> lc_tm a.
Proof.
  assert (H : forall n a, (tm_size a < n)%nat -> scoped 0 a -> lc_tm a).
  { induction n; [lia|].
    destruct a; simpl; intros Hsize Hscope;
      repeat match goal with H : _ /\ _ |- _ => destruct H end;
      try lia; try solve [eauto with safety].
    all: first [apply lc_a_Pi | apply lc_a_Abs | apply lc_a_SSigma |
      apply lc_a_App | apply lc_a_CEq | apply lc_a_Transp |
      apply lc_a_T | apply lc_a_Box | apply lc_a_Unbox |
      apply lc_a_SPair | apply lc_a_Proj1 | apply lc_a_Proj2 | apply lc_a_If].
    all: try solve [eapply IHn; simpl; [lia|assumption]].
    all: intros x; eapply IHn;
      [unfold open_tm_wrt_tm; rewrite size_open_var; lia|
       apply scoped_open; simpl; auto]. }
  eauto.
Qed.

Lemma scoped_subst : forall a u x k,
  scoped k a -> scoped 0 u -> scoped k (subst_tm u x a).
Proof.
  induction a; simpl; intros;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat split; eauto.
  destruct (eq_var x x0); simpl; eauto using scoped_mono with arith.
Qed.

Lemma subst_open_rec : forall a u v x k, scoped 0 u ->
  subst_tm u x (open_tm_wrt_tm_rec k v a) =
  open_tm_wrt_tm_rec k (subst_tm u x v) (subst_tm u x a).
Proof.
  induction a; simpl; intros;
    try rewrite IHa; try rewrite IHa1; try rewrite IHa2; try rewrite IHa3; auto.
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; auto.
  - destruct (eq_var x x0); simpl; [symmetry; apply scoped_open_id; eauto using scoped_mono with arith|reflexivity].
Qed.

Lemma subst_open : forall a u v x, lc_tm u ->
  subst_tm u x (open_tm_wrt_tm a v) =
  open_tm_wrt_tm (subst_tm u x a) (subst_tm u x v).
Proof. intros; apply subst_open_rec; auto using lc_scoped. Qed.

Lemma subst_fresh : forall a u x, x \notin fv_tm a -> subst_tm u x a = a.
Proof.
  induction a; simpl; intros; f_equal; eauto; try solve [eauto using notin_union_l, notin_union_r].
  all: try solve [eapply IHa1; fsetdec | eapply IHa2; fsetdec | eapply IHa3; fsetdec].
  destruct (eq_var x x0); subst; auto; fsetdec.
Qed.

Lemma open_subst_var : forall a u x, x \notin fv_tm a ->
  subst_tm u x (open_tm_wrt_tm a (a_Var_f x)) = open_tm_wrt_tm a u.
Proof.
  intros a u x H.
  unfold open_tm_wrt_tm.
  generalize 0%nat.
  induction a; simpl in *; intros k; try solve [f_equal; eauto; fsetdec].
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; auto.
    change ((if eq_var x x then u else a_Var_f x) = u).
    destruct (eq_var x x); simpl; congruence.
  - change ((if eq_var x0 x then u else a_Var_f x0) = a_Var_f x0).
    destruct (eq_var x0 x); subst; auto; fsetdec.
Qed.

Lemma lc_subst : forall a u x, lc_tm a -> lc_tm u -> lc_tm (subst_tm u x a).
Proof. eauto using scoped_lc, scoped_subst, lc_scoped. Qed.

Lemma lc_open : forall a u x, lc_tm (open_tm_wrt_tm a (a_Var_f x)) ->
  lc_tm u -> lc_tm (open_tm_wrt_tm a u).
Proof. intros; apply scoped_lc; apply scoped_open; eauto using scoped_open_inv, lc_scoped. Qed.

Ltac fresh_atom x L H := destruct (atom_fresh L) as [x H].

Lemma open_close : forall a x k,
  open_tm_wrt_tm_rec k (a_Var_f x) (close_tm_wrt_tm_rec k x a) = a.
Proof.
  induction a; simpl; intros;
    try rewrite IHa; try rewrite IHa1; try rewrite IHa2; try rewrite IHa3; auto.
  - destruct (lt_dec n k); cbn -[lt_eq_lt_dec].
    + destruct (lt_eq_lt_dec n k) as [[?|?]|?]; try lia; reflexivity.
    + change ((match lt_eq_lt_dec (S n) k with
              | inleft (left _) => a_Var_b (S n)
              | inleft (right _) => a_Var_f x
              | inright _ => a_Var_b (n-0)
              end) = a_Var_b n).
      destruct (lt_eq_lt_dec (S n) k) as [[?|?]|?]; try lia; f_equal; lia.
  - change (open_tm_wrt_tm_rec k (a_Var_f x0)
       (if eq_var x0 x then a_Var_b k else a_Var_f x) = a_Var_f x).
    destruct (eq_var x0 x) as [->|?]; [|reflexivity].
    simpl; destruct (lt_eq_lt_dec k k) as [[?|?]|?]; try reflexivity; lia.
Qed.

Lemma close_open : forall a x k, x \notin fv_tm a ->
  close_tm_wrt_tm_rec k x (open_tm_wrt_tm_rec k (a_Var_f x) a) = a.
Proof.
  induction a; simpl; intros; try solve [f_equal; eauto; fsetdec].
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl;
    repeat match goal with |- context [lt_dec ?i ?j] => destruct (lt_dec i j) end;
    repeat match goal with |- context [eq_var ?i ?j] => destruct (eq_var i j); simpl end;
    simpl; try congruence; try lia; f_equal; lia.
  - change ((if eq_var x0 x then a_Var_b k else a_Var_f x) = a_Var_f x).
    destruct (eq_var x0 x); simpl; subst; auto; fsetdec.
Qed.

(* Structural properties of parallel reduction and its graded arguments. *)
Scheme Par_mut := Induction for Par Sort Prop
with CPar_mut := Induction for CPar Sort Prop.
Combined Scheme parallel_ind from Par_mut, CPar_mut.

Lemma par_regular :
  (forall P p a b, Par P p a b -> uniq P /\ lc_tm a /\ lc_tm b) /\
  (forall P p q a b, CPar P p q a b -> uniq P /\ lc_tm a /\ lc_tm b).
Proof.
  apply parallel_ind; intros;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    try solve [repeat split; eauto with safety].
  all: try match goal with
    | H : lc_tm (a_Abs _ _ _) |- _ => inversion H; subst
    | H : lc_tm (a_Box _ _) |- _ => inversion H; subst
    | H : lc_tm (a_SPair _ _ _) |- _ => inversion H; subst
    end.
  all: try match goal with
    | H : forall x, lc_tm (open_tm_wrt_tm ?b (a_Var_f x)) |- _ =>
      fresh_atom z AtomSetImpl.empty F; pose proof (H z); clear H
    end.
  all: try solve [repeat split; eauto using lc_open with safety].
  all: match goal with
    | H : forall x, x \notin ?L -> uniq _ /\ _ |- _ =>
      let z := fresh "z" in let F := fresh "F" in
      fresh_atom z L F;
      destruct (H z F) as [U [S1 S2]]; inversion U; subst
    end.
  all: repeat split; try assumption.
  all: apply scoped_lc; simpl; split; eauto using lc_scoped;
    eapply (@scoped_open_inv _ 0 z); eauto using lc_scoped.
Qed.

Definition eincl (P Q : econtext) : Prop :=
  forall x q, binds x q P -> binds x q Q.

Lemma eincl_cons : forall P Q x q, eincl P Q -> eincl (x ~ q ++ P) (x ~ q ++ Q).
Proof.
  unfold eincl; intros; analyze_binds H0; eauto using binds_cons, binds_one, binds_app_l.
Qed.

Lemma eincl_extend : forall P x q, eincl P (x ~ q ++ P).
Proof. unfold eincl; intros; auto using binds_cons. Qed.

Lemma par_weaken :
  (forall P p a b, Par P p a b -> forall Q, uniq Q -> eincl P Q -> Par Q p a b) /\
  (forall P p q a b, CPar P p q a b -> forall Q, uniq Q -> eincl P Q -> CPar Q p q a b).
Proof.
  apply parallel_ind; intros; try solve [eauto 4 with safety].
  all: try solve [eapply Par_If; eauto | eapply Par_IfTrue; eauto | eapply Par_IfFalse; eauto].
  all: match goal with
    | IH : forall x, x \notin ?L -> forall Q, uniq Q -> eincl _ Q -> Par Q _ _ _,
      U : uniq ?Q |- _ =>
      first [eapply Par_Pi with (L := L \u dom Q) |
             eapply Par_Abs with (L := L \u dom Q) |
             eapply Par_SSigma with (L := L \u dom Q)];
      try solve [eauto with safety];
      intros x Fr; apply IH; [fsetdec|solve_uniq| apply eincl_cons; assumption]
    end.
Qed.

Definition ewithout (x : atom) (P Q : econtext) : Prop :=
  forall y q, y <> x -> binds y q P -> binds y q Q.

Lemma ewithout_cons : forall x P Q y q, ewithout x P Q ->
  ewithout x (y ~ q ++ P) (y ~ q ++ Q).
Proof.
  unfold ewithout; intros; analyze_binds H1; eauto using binds_cons, binds_one, binds_app_l.
Qed.

Lemma cpar_visible : forall P p q a b, q <= p -> CPar P p q a b -> Par P p a b.
Proof. intros; inversion H0; subst; tauto. Qed.

Lemma subst_open_distinct : forall a u x z, lc_tm u -> z <> x ->
  subst_tm u x (open_tm_wrt_tm a (a_Var_f z)) =
  open_tm_wrt_tm (subst_tm u x a) (a_Var_f z).
Proof.
  intros; rewrite subst_open; [|assumption].
  change (open_tm_wrt_tm (subst_tm u x a)
    (if eq_var z x then u else a_Var_f z) = open_tm_wrt_tm (subst_tm u x a) (a_Var_f z)).
  destruct (eq_var z x); simpl; congruence.
Qed.

Lemma par_substitution :
  (forall P p a b, Par P p a b -> forall Q q x u v,
    binds x q P -> ewithout x P Q -> CPar Q p q u v ->
    Par Q p (subst_tm u x a) (subst_tm v x b)) /\
  (forall P p r a b, CPar P p r a b -> forall Q q x u v,
    binds x q P -> ewithout x P Q -> CPar Q p q u v ->
    CPar Q p r (subst_tm u x a) (subst_tm v x b)).
Proof.
  apply parallel_ind; intros; simpl in *;
    match goal with H : CPar _ _ _ _ _ |- _ =>
      let R := fresh in pose proof (proj2 par_regular _ _ _ _ _ H) as R
    end;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    try solve [eauto 4 using lc_subst with safety].
  - destruct (eq_var x x0) as [->|?]; simpl.
    + eapply cpar_visible; [|eassumption].
      assert (psi0 = q) by (eapply binds_unique; eauto). subst; assumption.
    + eapply Par_Var; [assumption|eassumption|eapply H0; eauto].
  all: try solve [rewrite subst_open; [eapply Par_AppBeta; eauto|assumption]].
  all: try solve [eapply Par_If; eauto | eapply Par_IfTrue; eauto | eapply Par_IfFalse; eauto].
  all: try solve [eapply Par_CEq; eauto using lc_subst].
  all: lazymatch goal with
  | R : CPar ?Q ?p ?q ?u ?v, M : ewithout ?x ?P ?Q,
    U : lc_tm ?u, V : lc_tm ?v,
    IH : forall z, z \notin ?L -> forall _ _ _ _ _, _ ->
      ewithout _ _ _ -> CPar _ _ _ _ _ -> _ |- _ =>
    first [eapply Par_Pi with (L := L \u dom Q \u {{x}}) |
           eapply Par_Abs with (L := L \u dom Q \u {{x}}) |
           eapply Par_SSigma with (L := L \u dom Q \u {{x}})];
    try solve [eauto using lc_subst];
    let z := fresh "z" in let F := fresh "F" in intros z F;
    assert (D : z <> x) by fsetdec;
    erewrite <- (@subst_open_distinct _ u x z U D);
    erewrite <- (@subst_open_distinct _ v x z V D);
    eapply IH; [fsetdec|eauto using binds_cons|apply ewithout_cons; exact M|];
    eapply (proj2 par_weaken); [exact R|solve_uniq|apply eincl_extend]
  end.
Qed.

Lemma close_fresh : forall a x k, x \notin fv_tm (close_tm_wrt_tm_rec k x a).
Proof.
  induction a; simpl; intros; try solve [specialize_all; fsetdec].
  all: try solve [repeat match goal with
    | H : forall _ _, _ |- _ => specialize (H x k)
    end; fsetdec].
  - apply notin_union; eauto.
  - apply notin_union; eauto.
  - destruct (lt_dec n k); simpl; fsetdec.
  - change (x0 \notin fv_tm (if eq_var x0 x then a_Var_b k else a_Var_f x)).
    destruct (eq_var x0 x); simpl; fsetdec.
  - apply notin_union; eauto.
Qed.

Lemma ewithout_head : forall P x r Q, x \notin dom P -> eincl P Q ->
  ewithout x (x ~ r ++ P) Q.
Proof. unfold ewithout, eincl; intros; analyze_binds H2; eauto; congruence. Qed.

Lemma cpar_var : forall P p r x, uniq P -> binds x r P ->
  CPar P p r (a_Var_f x) (a_Var_f x).
Proof.
  intros; destruct (r <= p) eqn:E.
  - apply CPar_Leq; eauto with safety.
  - apply CPar_Nleq; eauto with safety; congruence.
Qed.

Lemma par_open : forall P p r A B L u v,
  (forall x, x \notin L -> Par (x ~ r ++ P) p
      (open_tm_wrt_tm A (a_Var_f x)) (open_tm_wrt_tm B (a_Var_f x))) ->
  CPar P p r u v ->
  Par P p (open_tm_wrt_tm A u) (open_tm_wrt_tm B v).
Proof.
  intros P p r A B L u v H R.
  fresh_atom x (L \u dom P \u fv_tm A \u fv_tm B) F.
  assert (N : x \notin L) by fsetdec.
  rewrite <- (@open_subst_var A u x) ; [|fsetdec].
  rewrite <- (@open_subst_var B v x) ; [|fsetdec].
  eapply (proj1 par_substitution _ _ _ _ (H x N));
    [apply binds_app_l; apply binds_one; reflexivity| |exact R].
  apply ewithout_head; [fsetdec|unfold eincl; auto].
Qed.

Lemma par_rename : forall P p r A B x,
  x \notin dom P -> x \notin fv_tm A -> x \notin fv_tm B ->
  Par (x ~ r ++ P) p (open_tm_wrt_tm A (a_Var_f x)) (open_tm_wrt_tm B (a_Var_f x)) ->
  forall y, y \notin dom P ->
  Par (y ~ r ++ P) p (open_tm_wrt_tm A (a_Var_f y)) (open_tm_wrt_tm B (a_Var_f y)).
Proof.
  intros P p r A B x D F G H y Y.
  destruct (proj1 par_regular _ _ _ _ H) as [U _]; inversion U; subst.
  rewrite <- (open_subst_var (a_Var_f y) F).
  rewrite <- (open_subst_var (a_Var_f y) G).
  eapply (proj1 par_substitution _ _ _ _ H).
  - apply binds_app_l; apply binds_one; reflexivity.
  - apply ewithout_head; auto using eincl_extend.
  - apply cpar_var; [solve_uniq|apply binds_app_l; apply binds_one; reflexivity].
Qed.

Lemma par_source : forall P p a b, Par P p a b -> Par P p a a.
Proof.
  assert (H : (forall P p a b, Par P p a b -> Par P p a a) /\
              (forall P p q a b, CPar P p q a b -> CPar P p q a a)).
  { apply parallel_ind; intros; solve [eauto 4 with safety]. }
  exact (proj1 H).
Qed.

Lemma par_target : forall P p a b, Par P p a b -> Par P p b b.
Proof.
  assert (H : (forall P p a b, Par P p a b -> Par P p b b) /\
              (forall P p q a b, CPar P p q a b -> CPar P p q b b)).
  { apply parallel_ind; intros; try solve [eauto 4 with safety].
    all: repeat match goal with
      | H : Par _ _ (a_Abs _ _ _) (a_Abs _ _ _) |- _ => inversion H; clear H; subst
      | H : Par _ _ (a_Box _ _) (a_Box _ _) |- _ => inversion H; clear H; subst
      | H : Par _ _ (a_SPair _ _ _) (a_SPair _ _ _) |- _ => inversion H; clear H; subst
      end.
    all: try solve [eauto using cpar_visible, par_open with safety].
  }
  exact (proj1 H).
Qed.

Lemma le_meet_l : forall p q : grade, p `&` q <= p.
Proof. intros; exact (Order.LatticeTheoryMeet.leIl _ _). Qed.
Lemma le_meet_r : forall p q : grade, p `&` q <= q.
Proof. intros; exact (Order.LatticeTheoryMeet.leIr q p). Qed.
Lemma le_meet : forall r p q : grade, r <= p -> r <= q -> r <= (p `&` q).
Proof. intros; rewrite Order.LatticeTheoryMeet.lexI; apply /andP; auto. Qed.

Local Hint Resolve le_meet_l le_meet_r le_meet : safety.

Lemma par_body_join : forall P p q r A B C L K,
  (forall x, x \notin L ->
    Par (x ~ r ++ P) q (open_tm_wrt_tm A (a_Var_f x)) (open_tm_wrt_tm C (a_Var_f x)) ->
    exists d,
      Par (x ~ r ++ P) (p `&` q) (open_tm_wrt_tm B (a_Var_f x)) d /\
      Par (x ~ r ++ P) (p `&` q) (open_tm_wrt_tm C (a_Var_f x)) d) ->
  (forall x, x \notin K ->
    Par (x ~ r ++ P) q (open_tm_wrt_tm A (a_Var_f x)) (open_tm_wrt_tm C (a_Var_f x))) ->
  exists D, forall x, x \notin dom P ->
    Par (x ~ r ++ P) (p `&` q) (open_tm_wrt_tm B (a_Var_f x)) (open_tm_wrt_tm D (a_Var_f x)) /\
    Par (x ~ r ++ P) (p `&` q) (open_tm_wrt_tm C (a_Var_f x)) (open_tm_wrt_tm D (a_Var_f x)).
Proof.
  intros P p q r A B C L K IH HC.
  fresh_atom z (L \u K \u dom P \u fv_tm B \u fv_tm C) F.
  assert (FL : z \notin L) by fsetdec.
  assert (FK : z \notin K) by fsetdec.
  destruct (IH z FL (HC z FK)) as [d [HB HD]].
  exists (close_tm_wrt_tm z d); intros x FX.
  assert (E : open_tm_wrt_tm (close_tm_wrt_tm z d) (a_Var_f z) = d).
  { apply open_close. }
  split; eapply par_rename with (x := z);
    try fsetdec; try apply close_fresh; rewrite E; assumption.
Qed.

Lemma cpar_meet_hidden : forall P p q r a b c,
  CPar P p r a b -> CPar P q r a c -> not (r <= p `&` q) ->
  exists d, CPar P (p `&` q) r b d /\ CPar P (p `&` q) r c d.
Proof.
  intros P p q r a b c HB HC E.
  destruct (proj2 par_regular _ _ _ _ _ HB) as [U [_ LB]].
  destruct (proj2 par_regular _ _ _ _ _ HC) as [_ [_ LC]].
  exists b; split; eauto with safety.
Qed.

Ltac parallel_subjoins :=
  repeat match goal with
  | IH : forall q c, Par ?P q ?a c -> exists d, _,
    H : Par ?P ?q ?a ?c |- exists d, Par _ (_ `&` ?q) _ _ /\ _ =>
    let d := fresh "d" in let L := fresh "left_step" in let R := fresh "right_step" in
    destruct (IH q c H) as [d [L R]]; clear IH
  | IH : forall q c, CPar ?P q ?r ?a c -> exists d, _,
    H : CPar ?P ?q ?r ?a ?c |- exists d, Par _ (_ `&` ?q) _ _ /\ _ =>
    let d := fresh "d" in let L := fresh "left_step" in let R := fresh "right_step" in
    destruct (IH q c H) as [d [L R]]; clear IH
  end.

(* A fork at two grades is joined at their meet. The argument is hidden
   at the meet if either step hides it. *)
Lemma par_diamond :
  (forall P p a b, Par P p a b -> forall q c, Par P q a c ->
    exists d, Par P (p `&` q) b d /\ Par P (p `&` q) c d) /\
  (forall P p r a b, CPar P p r a b -> forall q c, CPar P q r a c ->
    exists d, CPar P (p `&` q) r b d /\ CPar P (p `&` q) r c d).
Proof.
  apply parallel_ind; intros.
  all: tryif match goal with |- exists d, CPar _ _ _ _ _ /\ _ => idtac end then (
    lazymatch goal with
    | HC : CPar ?P ?q ?r ?a ?c |- exists d, CPar ?P (?p `&` ?q) ?r ?b d /\ _ =>
      let E := fresh "E" in
      destruct (r <= (p `&` q)) eqn:E;
      [ assert (L : r <= p) by exact (Order.POrderTheory.le_trans E (le_meet_l p q));
        assert (R : r <= q) by exact (Order.POrderTheory.le_trans E (le_meet_r p q));
        try contradiction;
        let H := fresh "H" in pose proof (cpar_visible R HC) as H;
        match goal with
        | IH : forall k t, Par ?P k ?a t -> exists d, _ |- _ =>
          let d := fresh "d" in destruct (IH q c H) as [d [? ?]];
          exists d; split; apply CPar_Leq; assumption
        end
      | eapply (@cpar_meet_hidden P p q r a b c);
        [eauto with safety|exact HC|congruence] ]
    end) else idtac.
  all: try match goal with H : Par _ _ _ _ |- exists d, Par _ _ _ _ /\ _ => inversion H; subst; clear H end.
  all: parallel_subjoins.
  all: try solve [eexists; split; first
    [eassumption | eapply Par_Var | eapply Par_Type | eapply Par_Refl |
     eapply Par_Bool | eapply Par_TyUnit | eapply Par_TmUnit | eapply Par_True |
     eapply Par_False | eapply Par_App | eapply Par_Transp | eapply Par_CEq |
     eapply Par_T | eapply Par_Box | eapply Par_Unbox | eapply Par_Proj1Cong |
     eapply Par_Proj2Cong | eapply Par_SPair | eapply Par_If];
    eauto 2 with safety].
  - assert (psi0 = psi2) by (eapply binds_unique; eauto); subst.
    exists (a_Var_f x); split; eapply Par_Var with (psi0 := psi2); eauto with safety.
  all: try solve [
    match goal with
    | IH : forall x, x \notin _ -> forall q c, Par _ q _ c -> exists d, _,
      H : forall x, x \notin _ -> Par _ ?q _ _ |- exists d, Par ?P (_ `&` ?q) _ _ /\ _ =>
      let J := fresh "J" in let D := fresh "D" in
      destruct (par_body_join ltac:(intros; eapply IH; eauto) H) as [D J];
      eexists; split;
      first [eapply Par_Pi with (L := dom P) | eapply Par_Abs with (L := dom P) |
             eapply Par_SSigma with (L := dom P)];
      try solve [eassumption];
      intros z F; destruct (J z F); eassumption
    end].
  all: repeat match goal with
    | H : Par _ (_ `&` _) (a_Abs _ _ _) _ |- _ => inversion H; clear H; subst
    | H : Par _ (_ `&` _) (a_Box _ _) _ |- _ => inversion H; clear H; subst
    | H : Par _ (_ `&` _) (a_SPair _ _ _) _ |- _ => inversion H; clear H; subst
    end.
  all: repeat match goal with
    | H : Par _ (_ `&` _) a_Refl ?d |- _ =>
      is_var d; assert (d = a_Refl) by (inversion H; reflexivity); subst d
    | H : Par _ (_ `&` _) a_True ?d |- _ =>
      is_var d; assert (d = a_True) by (inversion H; reflexivity); subst d
    | H : Par _ (_ `&` _) a_False ?d |- _ =>
      is_var d; assert (d = a_False) by (inversion H; reflexivity); subst d
    end.
  all: try solve [match goal with
    | H : Par _ _ a_True a_False |- _ => inversion H
    | H : Par _ _ a_False a_True |- _ => inversion H
    end].
  all: try solve [eexists; split;
    first [solve [eapply par_open; eassumption] | solve [eapply Par_AppBeta; eassumption]]].
  all: try solve [eexists; split;
    first [eassumption |
      solve [eapply Par_TranspRefl; eassumption] |
      solve [eapply Par_IfTrue; eassumption] |
      solve [eapply Par_IfFalse; eassumption] |
      solve [eapply Par_Proj2Beta; eassumption]]].
  all: try solve [
    match goal with H : CPar _ (_ `&` _) ?r _ _ |- _ =>
      let R := fresh "R" in
      assert (R : r <= (psi `&` q)) by (apply le_meet; assumption);
      pose proof (cpar_visible R H); clear H
    end;
    repeat match goal with H : CPar _ (_ `&` _) _ _ _,
      R : _ <= (_ `&` _) |- _ => pose proof (cpar_visible R H); clear H end;
    eexists; split;
    first [eassumption |
      solve [eapply Par_UnboxBox; eassumption] |
      solve [eapply Par_Proj1Beta; eassumption]]].
  all: eexists; split.
  all: eapply cpar_visible; [apply le_meet; eassumption | eassumption].
Qed.

(* Each graded equality is a sequence of forward and backward parallel steps. *)
Inductive Zig (P : econtext) (p : grade) : tm -> tm -> Prop :=
| zig_step a b : Par P p a b -> Zig P p a b
| zig_sym a b : Zig P p a b -> Zig P p b a
| zig_trans a b c : Zig P p a b -> Zig P p b c -> Zig P p a c.

Local Hint Resolve zig_step : safety.

Lemma zig_endpoints : forall P p a b, Zig P p a b -> Par P p a a /\ Par P p b b.
Proof.
  induction 1; intuition eauto using par_source, par_target.
Qed.

Lemma zig_map : forall P Q p q (f : tm -> tm),
  (forall a b, Par P p a b -> Par Q q (f a) (f b)) ->
  forall a b, Zig P p a b -> Zig Q q (f a) (f b).
Proof. intros P Q p q f M a b H; induction H; eauto using zig_step, zig_sym, zig_trans. Qed.

Lemma zig_congr2 : forall P p (f : tm -> tm -> tm) a b c d,
  (forall x y u v, Par P p x y -> Par P p u v -> Par P p (f x u) (f y v)) ->
  Zig P p a b -> Zig P p c d -> Zig P p (f a c) (f b d).
Proof.
  intros P p f a b c d H J K.
  destruct (zig_endpoints J) as [_ B]; destruct (zig_endpoints K) as [C _].
  eapply zig_trans with (b := f b c);
    [eapply (zig_map (f := fun t => f t c)) | eapply (zig_map (f := f b))];
    eauto.
Qed.

Lemma zig_cpar_congr : forall P p r (f : tm -> tm) a b,
  (forall u v, CPar P p r u v -> Par P p (f u) (f v)) ->
  (if r <= p then Zig P p a b else uniq P /\ lc_tm a /\ lc_tm b) ->
  Zig P p (f a) (f b).
Proof.
  intros P p r f a b H.
  destruct (r <= p) eqn:E; intros J.
  - eapply zig_map; [|exact J]; eauto with safety.
  - destruct J as [U [A B]]; apply zig_step; apply H.
    apply CPar_Nleq; try assumption; congruence.
Qed.

Lemma cpar_of_zig_l : forall P p r a b,
  (if r <= p then Zig P p a b else uniq P /\ lc_tm a /\ lc_tm b) ->
  CPar P p r a a.
Proof.
  intros P p r a b; destruct (r <= p) eqn:E; intro H.
  - apply CPar_Leq; [exact E|apply (proj1 (zig_endpoints H))].
  - destruct H as [U [A B]]; apply CPar_Nleq; try assumption; congruence.
Qed.

Lemma zig_cpar_congr2 : forall P p r (f : tm -> tm -> tm) a b c d,
  (forall x y u v, Par P p x y -> CPar P p r u v -> Par P p (f x u) (f y v)) ->
  Zig P p a b ->
  (if r <= p then Zig P p c d else uniq P /\ lc_tm c /\ lc_tm d) ->
  Zig P p (f a c) (f b d).
Proof.
  intros P p r f a b c d H J K.
  destruct (zig_endpoints J) as [_ B].
  pose proof (cpar_of_zig_l (a := c) (b := d) K) as C.
  eapply zig_trans with (b := f b c).
  - eapply (zig_map (f := fun t => f t c)); eauto.
  - eapply zig_cpar_congr; eauto.
Qed.

Lemma par_close_bodies : forall P p r x a b,
  x \notin dom P -> Par (x ~ r ++ P) p a b ->
  forall y, y \notin dom P ->
  Par (y ~ r ++ P) p
    (open_tm_wrt_tm (close_tm_wrt_tm x a) (a_Var_f y))
    (open_tm_wrt_tm (close_tm_wrt_tm x b) (a_Var_f y)).
Proof.
  intros; eapply par_rename with (x := x); try eassumption; try apply close_fresh.
  unfold open_tm_wrt_tm, close_tm_wrt_tm; rewrite !open_close; assumption.
Qed.

Lemma zig_binder_congr : forall P p r (f : tm -> tm) A B L,
  (forall a b, (forall x, x \notin dom P ->
    Par (x ~ r ++ P) p (open_tm_wrt_tm a (a_Var_f x)) (open_tm_wrt_tm b (a_Var_f x))) ->
    Par P p (f a) (f b)) ->
  (forall x, x \notin L -> Zig (x ~ r ++ P) p
    (open_tm_wrt_tm A (a_Var_f x)) (open_tm_wrt_tm B (a_Var_f x))) ->
  Zig P p (f A) (f B).
Proof.
  intros P p r f A B L M J.
  fresh_atom z (L \u dom P \u fv_tm A \u fv_tm B) F.
  assert (K : z \notin L) by fsetdec.
  pose proof (J z K) as H.
  pose proof (zig_map (f := fun t => f (close_tm_wrt_tm z t))
    (fun a b R => M _ _ (@par_close_bodies P p r z a b ltac:(fsetdec) R)) H) as E.
  unfold close_tm_wrt_tm, open_tm_wrt_tm in E.
  rewrite !close_open in E; try fsetdec; exact E.
Qed.

Lemma par_defeq :
  (forall P p a b, Par P p a b -> GDefEq P p a b) /\
  (forall P p r a b, CPar P p r a b -> CGDefEq P p r a b).
Proof.
  Local Hint Constructors GDefEq CGDefEq : ge_rules.
  apply parallel_ind; intros; try solve [eauto 3 with ge_rules].
  all: first [eapply GE_Pi | eapply GE_Abs | eapply GE_SSigma |
    eapply GE_If | eapply GE_IfTrue | eapply GE_IfFalse | eapply GE_CEq]; eassumption.
Qed.

Lemma par_to_gdefeq : forall P p a b, Par P p a b -> GDefEq P p a b.
Proof. exact (proj1 par_defeq). Qed.

Lemma zig_gdefeq : forall P p a b, Zig P p a b -> GDefEq P p a b.
Proof. induction 1; eauto using par_to_gdefeq, GE_Sym, GE_Trans. Qed.

Scheme GE_mut := Induction for GDefEq Sort Prop
with CGE_mut := Induction for CGDefEq Sort Prop.
Combined Scheme graded_eq_ind from GE_mut, CGE_mut.

Lemma gdefeq_zig :
  (forall P p a b, GDefEq P p a b -> Zig P p a b) /\
  (forall P p r a b, CGDefEq P p r a b ->
    if r <= p then Zig P p a b else uniq P /\ lc_tm a /\ lc_tm b).
Proof.
  apply graded_eq_ind; intros;
    try solve [eauto 3 using zig_sym, zig_trans with safety].
  all: try solve [eapply (zig_congr2 (f := a_Transp)); eauto using Par_Transp].
  all: try solve [eapply (zig_map (f := a_T _)); eauto using Par_T].
  all: try solve [eapply (zig_map (f := a_Unbox _)); eauto using Par_Unbox].
  all: try solve [eapply (zig_map (f := a_Proj1 _)); eauto using Par_Proj1Cong].
  all: try solve [eapply (zig_map (f := a_Proj2 _)); eauto using Par_Proj2Cong].
  all: try solve [eapply (zig_cpar_congr (f := a_Box _)); eauto using Par_Box].
  all: try solve [eapply (zig_cpar_congr2 (f := fun a b => a_App a _ b)); eauto using Par_App].
  all: try solve [eapply (zig_cpar_congr2 (f := fun a b => a_SPair b _ a)); eauto using Par_SPair].
  - eapply zig_trans with (b := a_Abs psi0 A1 b0).
    + apply zig_step; eapply Par_Abs with (L := L); try assumption.
      intros z F; exact (proj1 (zig_endpoints (H z F))).
    + eapply (zig_binder_congr (f := a_Abs psi0 A1)); [|exact H].
      intros; eapply Par_Abs with (L := dom P); assumption.
  - eapply zig_trans with (b := a_Pi psi0 A1 B0).
    + eapply (zig_map (f := fun t => a_Pi psi0 t B0)); [|eassumption].
      intros; eapply Par_Pi with (L := L); try assumption.
      intros z F; exact (proj1 (zig_endpoints (H0 z F))).
    + eapply (zig_binder_congr (f := a_Pi psi0 A1)); [|exact H0].
      intros; eapply Par_Pi with (L := dom P); [exact (proj2 (zig_endpoints H))|assumption].
  - eapply zig_trans with (b := a_App (a_Abs psi0 A a0) psi0 b0).
    + eapply (zig_map (f := fun t => a_App t psi0 b0)); [|eassumption].
      intros; eapply Par_App; [eassumption|eapply cpar_of_zig_l; eassumption].
    + eapply zig_trans with (b := a_App (a_Abs psi0 A a0) psi0 b1).
      * eapply (zig_cpar_congr (f := a_App (a_Abs psi0 A a0) psi0)); [|eassumption].
        intros; eapply Par_App; [exact (proj2 (zig_endpoints H))|assumption].
      * apply zig_step; eapply Par_AppBeta; [exact (proj2 (zig_endpoints H))|].
        eapply cpar_of_zig_l with (b := b0).
        destruct (psi0 <= psi); intuition eauto using zig_sym.
  - eapply zig_trans with (b := a_CEq psi0 a1 b1 psi1 A0).
    + eapply (zig_congr2 (f := fun a b => a_CEq psi0 a b psi1 A0));
        [intros; eapply Par_CEq; eassumption|assumption|assumption].
    + apply zig_step; apply Par_CEq; try assumption;
        [exact (proj2 (zig_endpoints H))|exact (proj2 (zig_endpoints H0))].
  - eapply zig_trans with (b := a_Transp a_Refl b1).
    + eapply (zig_congr2 (f := a_Transp)); eauto using Par_Transp.
    + apply zig_step; eapply Par_TranspRefl;
        [exact (proj2 (zig_endpoints H))|exact (proj2 (zig_endpoints H0))].
  - eapply zig_trans with (b := a_Unbox psi0 (a_Box psi0 b)).
    + eapply (zig_map (f := a_Unbox psi0)); eauto using Par_Unbox.
    + apply zig_step; eapply Par_UnboxBox; [exact (proj2 (zig_endpoints H))|assumption].
  - eapply zig_trans with (b := a_Proj1 psi0 (a_SPair a1 psi0 a2)).
    + eapply (zig_map (f := a_Proj1 psi0)); eauto using Par_Proj1Cong.
    + apply zig_step; eapply Par_Proj1Beta; [exact (proj2 (zig_endpoints H))|assumption].
  - eapply zig_trans with (b := a_Proj2 psi0 (a_SPair a1 psi0 a2)).
    + eapply (zig_map (f := a_Proj2 psi0)); eauto using Par_Proj2Cong.
    + apply zig_step; eapply Par_Proj2Beta; exact (proj2 (zig_endpoints H)).
  - eapply zig_trans with (b := a_SSigma psi0 A1 B0).
    + eapply (zig_map (f := fun t => a_SSigma psi0 t B0)); [|eassumption].
      intros; eapply Par_SSigma with (L := L); try assumption.
      intros z F; exact (proj1 (zig_endpoints (H0 z F))).
    + eapply (zig_binder_congr (f := a_SSigma psi0 A1)); [|exact H0].
      intros; eapply Par_SSigma with (L := dom P); [exact (proj2 (zig_endpoints H))|assumption].
  - assert (Z : Zig P psi (a_If a0 b0 b1) (a_If a1 b2 b1)).
    { eapply (zig_congr2 (f := fun x y => a_If x y b1)); try eassumption.
      intros; eapply Par_If; try eassumption; exact (proj1 (zig_endpoints H1)). }
    eapply zig_trans; [exact Z|].
    eapply (zig_map (f := a_If a1 b2)); [|eassumption].
    intros; eapply Par_If; try eassumption;
      [exact (proj2 (zig_endpoints H))|exact (proj2 (zig_endpoints H0))].
  - eapply zig_trans with (b := a_If a_True b2 b1).
    + eapply (zig_congr2 (f := fun x y => a_If x y b1)); try eassumption.
      intros; eapply Par_If; try eassumption; exact (proj1 (zig_endpoints H1)).
    + apply zig_step; eapply Par_IfTrue;
        [exact (proj2 (zig_endpoints H))|exact (proj2 (zig_endpoints H0))|
         exact (proj1 (zig_endpoints H1))].
  - eapply zig_trans with (b := a_If a_False b0 b3).
    + eapply (zig_congr2 (f := fun x y => a_If x b0 y)); try eassumption.
      intros; eapply Par_If; try eassumption; exact (proj1 (zig_endpoints H0)).
    + apply zig_step; eapply Par_IfFalse;
        [exact (proj2 (zig_endpoints H))|exact (proj1 (zig_endpoints H0))|
         exact (proj2 (zig_endpoints H1))].
  - destruct (psi0 <= psi); [assumption|congruence].
  - destruct (psi0 <= psi) eqn:E; [congruence|auto].
Qed.

Lemma gdefeq_to_zig : forall P p a b, GDefEq P p a b -> Zig P p a b.
Proof. exact (proj1 gdefeq_zig). Qed.

(* Forgetting the grade of each step gives a common reduct for conversions. *)
Inductive ParStar (P : econtext) : tm -> tm -> Prop :=
| star_refl a : ParStar P a a
| star_step p a b c : Par P p a b -> ParStar P b c -> ParStar P a c.

Lemma star_trans : forall P a b c, ParStar P a b -> ParStar P b c -> ParStar P a c.
Proof. induction 1; eauto using star_step. Qed.

Lemma star_strip : forall P a c, ParStar P a c ->
  forall p b, Par P p a b -> exists d, ParStar P b d /\ exists q, Par P q c d.
Proof.
  induction 1; intros q d R.
  - exists d; split; eauto using star_refl.
  - destruct (proj1 par_diamond _ _ _ _ H _ _ R) as [e [B D]].
    destruct (IHParStar _ _ B) as [f [F C]].
    exists f; split; eauto using star_step.
Qed.

Lemma star_confluent : forall P a b, ParStar P a b ->
  forall c, ParStar P a c -> exists d, ParStar P b d /\ ParStar P c d.
Proof.
  induction 1; intros y S.
  - exists y; eauto using star_refl.
  - destruct (star_strip S H) as [e [B [q Y]]].
    destruct (IHParStar _ B) as [d [C E]].
    exists d; split; eauto using star_step.
Qed.

Definition HasJoin P a b :=
  exists d, ParStar P a d /\ ParStar P b d.

Lemma has_join_trans : forall P a b c, HasJoin P a b -> HasJoin P b c -> HasJoin P a c.
Proof.
  intros P a b c [d [AD BD]] [e [BE CE]].
  destruct (star_confluent BD BE) as [f [D E]].
  exists f; eauto using star_trans.
Qed.

Lemma zig_join : forall P p a b, Zig P p a b -> HasJoin P a b.
Proof.
  induction 1; [exists b; eauto using star_refl, star_step|firstorder|eauto using has_join_trans].
Qed.

Lemma defeq_join : forall P a b, DefEq P a b -> HasJoin P a b.
Proof.
  induction 1; eauto using zig_join, gdefeq_to_zig, has_join_trans.
Qed.

Lemma defeq_sym : forall P a b, DefEq P a b -> DefEq P b a.
Proof. induction 1; eauto using E_One, E_Trans, GE_Sym. Qed.

Lemma star_eq : forall P a b, ParStar P a b -> a = b \/ DefEq P a b.
Proof.
  induction 1; [auto|].
  assert (D : DefEq P a b) by eauto using E_One, par_to_gdefeq.
  destruct IHParStar as [->|?]; eauto using E_Trans.
Qed.

Lemma par_head : forall P p a b, Par P p a b ->
  Value a -> tm_to_headform a = tm_to_headform b.
Proof. destruct 1; simpl; congruence. Qed.

Lemma star_head : forall P a b, ParStar P a b ->
  Value a -> tm_to_headform a = tm_to_headform b.
Proof.
  induction 1; intros V; [reflexivity|].
  pose proof (par_head H V) as E.
  rewrite E; apply IHParStar.
  destruct a, b; simpl in *; congruence.
Qed.

Lemma defeq_consistent : forall P a b,
  DefEq P a b -> Value a -> Value b -> tm_to_headform a = tm_to_headform b.
Proof.
  intros P a b H Va Vb; destruct (defeq_join H) as [c [A B]].
  rewrite (star_head A Va) (star_head B Vb); reflexivity.
Qed.

Lemma labels_dom : forall W, dom (labels W) = dom W.
Proof. induction W as [|[x [p A]] W IH]; simpl; [reflexivity|now rewrite IH]. Qed.

Lemma labels_uniq : forall W, uniq W -> uniq (labels W).
Proof. induction 1; simpl; constructor; auto; rewrite labels_dom; assumption. Qed.

Lemma labels_binds : forall W x p A, binds x (p,A) W -> binds x p (labels W).
Proof.
  induction W as [|[y [q B]] W IH]; simpl; intros; [assumption|].
  analyze_binds H.
  - inversion BindsTacVal; subst; left; reflexivity.
  - right; eapply IH; eassumption.
Qed.

Scheme typing_mut := Induction for Typing Sort Prop
with ctxt_mut := Induction for Ctx Sort Prop.
Combined Scheme typing_ctx_ind from typing_mut, ctxt_mut.

Lemma ctx_uniq : forall W, Ctx W -> uniq W.
Proof. induction 1; solve_uniq. Qed.

Lemma par_lc_l : forall P p a b, Par P p a b -> lc_tm a.
Proof. intros; exact (proj1 (proj2 (proj1 par_regular _ _ _ _ H))). Qed.

Lemma par_cond_refl : forall P p r a, uniq P -> lc_tm a ->
  (r <= p -> Par P p a a) -> CPar P p r a a.
Proof.
  intros; destruct (r <= p) eqn:E; eauto with safety.
  apply CPar_Nleq; try assumption; congruence.
Qed.

Ltac collect_term_closure :=
  repeat match goal with
  | H : forall q, is_true (@Order.le _ _ ?p q) -> Par _ q ?a ?a |- _ =>
    tryif match goal with _ : lc_tm a |- _ => idtac end then fail 0 else
      let L := fresh "closed" in pose proof (par_lc_l (H p (Order.POrderTheory.lexx _))) as L
  end.

Ltac local_type_inversions :=
  repeat match goal with
  | H : lc_tm (a_Pi _ _ _) |- _ => inversion H; clear H; subst
  | H : lc_tm (a_CEq _ _ _ _ _) |- _ => inversion H; clear H; subst
  | H : lc_tm (a_T _ _) |- _ => inversion H; clear H; subst
  | H : lc_tm (a_SSigma _ _ _) |- _ => inversion H; clear H; subst
  end.

(* Typing gives local closure and a reflexive parallel step at every
   grade that can observe the term. *)
Lemma typing_regular :
  (forall W p a A, Typing W p a A ->
    Ctx W /\ (forall q, p <= q -> Par (labels W) q a a) /\ lc_tm A) /\
  (forall W, Ctx W -> uniq W /\ forall x p A, binds x (p,A) W -> lc_tm A).
Proof.
  apply typing_ctx_ind; intros.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: collect_term_closure.
  all: repeat split; intros; try solve [assumption | solve_uniq].
  all: try solve [eapply Par_Var with (psi0 := psi0);
    eauto 3 using labels_uniq, labels_binds, ctx_uniq with safety].
  all: try solve [apply Par_App; [eauto|eapply par_cond_refl;
    eauto 3 using labels_uniq, ctx_uniq]].
  all: try solve [apply Par_Box; eapply par_cond_refl;
    eauto 3 using labels_uniq, ctx_uniq].
  all: try solve [apply Par_SPair; [eapply par_cond_refl;
    eauto 3 using labels_uniq, ctx_uniq|eauto]].
  all: try solve [eapply Par_CEq; eauto 4 with safety].
  all: try solve [eauto 4 using labels_uniq, ctx_uniq with safety].
  - apply Par_Var with (psi0 := psi0).
    + apply labels_uniq; assumption.
    + exact (Order.POrderTheory.le_trans i H1).
    + eapply labels_binds; exact b.
  all: try solve [
    first [eapply Par_Pi with (L := L) | eapply Par_Abs with (L := L) |
           eapply Par_SSigma with (L := L)];
    try solve [auto | inversion closed; assumption];
    let z := fresh "z" in let F := fresh "F" in intros z F;
    match goal with IH : forall x, x \notin _ -> Ctx _ /\ _ |- _ =>
      exact (proj1 (proj2 (IH z F)) q ltac:(assumption))
    end].
  all: try solve [
    first [apply Par_Unbox | apply Par_Proj1Cong];
    [eauto|eapply Order.POrderTheory.le_trans; eassumption]].
  all: try solve [apply Par_If; eauto].
  all: try solve [
    apply Par_CEq; try assumption;
      first [eapply Order.POrderTheory.le_trans; eassumption |
        match goal with H : forall k, is_true (@Order.le _ _ ?p k) -> Par _ k ?a ?a |- Par _ _ ?a ?a =>
          apply H; eapply Order.POrderTheory.le_trans;
          [eassumption | eapply Order.POrderTheory.le_trans; eassumption]
        end]].
  all: local_type_inversions.
  all: try solve [assumption | eauto using lc_a_Proj1].
  all: try solve [match goal with H : forall x, lc_tm (open_tm_wrt_tm ?B (a_Var_f x)) |- _ =>
    fresh_atom z AtomSetImpl.empty F;
    eapply (@lc_open B _ z); [exact (H z)|eauto with safety]
    end].
  all: try solve [match goal with IH : forall x, x \notin ?L -> Ctx _ /\ _ |- _ =>
    fresh_atom z L F;
    destruct (IH z F) as [_ [J _]];
    pose proof (par_lc_l (J _ (Order.POrderTheory.lexx _))) as Bclosed;
    eapply (@lc_open _ _ z); eassumption
    end].
  all: try solve [match goal with B : binds _ (_, _) (_ ++ _) |- _ =>
    analyze_binds B; [inversion BindsTacVal; subst; assumption|eauto]
    end].
Qed.

Lemma typed_readable : forall W p a A, Typing W p a A ->
  forall q, p <= q -> Par (labels W) q a a.
Proof. intros; exact (proj1 (proj2 (proj1 typing_regular _ _ _ _ H)) q H0). Qed.

Lemma typing_lc : forall W p a A, Typing W p a A -> lc_tm a.
Proof. intros; exact (par_lc_l (typed_readable H (Order.POrderTheory.lexx _))). Qed.

Lemma typing_ctx : forall W p a A, Typing W p a A -> Ctx W.
Proof. intros; exact (proj1 (proj1 typing_regular _ _ _ _ H)). Qed.

Lemma typed_cpar : forall W p a A, Typing W p a A ->
  forall q, CPar (labels W) q p a a.
Proof.
  intros; apply par_cond_refl;
    eauto using labels_uniq, ctx_uniq, typing_ctx, typing_lc, typed_readable.
Qed.

Definition Convertible P a b := a = b \/ DefEq P a b.

Lemma conv_sym : forall P a b, Convertible P a b -> Convertible P b a.
Proof. unfold Convertible; intuition eauto using defeq_sym. Qed.

Lemma conv_trans : forall P a b c, Convertible P a b -> Convertible P b c ->
  Convertible P a c.
Proof. unfold Convertible; intros ? ? ? ? [->|?] [->|?]; eauto using E_Trans. Qed.

Lemma conv_join : forall P a b, Convertible P a b -> HasJoin P a b.
Proof. intros P a b [->|R]; [exists b; auto using star_refl|now apply defeq_join]. Qed.

Lemma conv_consistent : forall P a b, Convertible P a b ->
  Value a -> Value b -> tm_to_headform a = tm_to_headform b.
Proof. intros P a b [->|R] V U; [reflexivity|exact (defeq_consistent R V U)]. Qed.

(* Canonical forms depend only on the outer constructor of the type. *)
Definition canonical (a A : tm) : Prop :=
  match a, A with
  | a_TyUnit, a_Type _ | a_TmUnit, a_TyUnit
  | a_Type _, a_Type _ | a_Bool, a_Type _
  | a_Pi _ _ _, a_Type _ | a_SSigma _ _ _, a_Type _
  | a_CEq _ _ _ _ _, a_Type _ | a_T _ _, a_Type _
  | a_Refl, a_CEq _ _ _ _ _
  | a_True, a_Bool | a_False, a_Bool => True
  | a_Abs p _ _, a_Pi q _ _ | a_SPair _ p _, a_SSigma q _ _
  | a_Box p _, a_T q _ => p = q
  | _, _ => False
  end.

Lemma canonical_typing : forall W p a A, Typing W p a A ->
  forall B, Value a -> Value B -> Convertible (labels W) A B -> canonical a B.
Proof.
  induction 1; intros C V U E; try discriminate.
  all: try solve [pose proof (conv_consistent E eq_refl U);
    destruct C; simpl in *; first [exact I|congruence]].
  eapply IHTyping1; [exact V|exact U|].
  eapply conv_trans; [right; eassumption|exact E].
Qed.

Ltac recognize_value T V :=
  lazymatch type of T with
  | Typing ?W ?p ?a ?A =>
    pose proof (@canonical_typing W p a A T A V eq_refl (or_introl eq_refl)) as K
  end.

Lemma closed_progress : forall W p a A, Typing W p a A ->
  W = nil -> Value a \/ exists b, Red a b.
Proof.
  induction 1; intros E; subst W; try solve [left; reflexivity].
  - match goal with B : binds _ _ nil |- _ => inversion B end.
  - destruct (IHTyping1 eq_refl) as [V|[c R]].
    + recognize_value H V.
      pose proof (typing_lc H) as Lb.
      destruct b; simpl in K; try contradiction; subst.
      inversion Lb; subst; right; eauto 4 using typing_lc with reduction_rules.
    + right; eauto 4 using typing_lc with reduction_rules.
  - eauto.
  - destruct (IHTyping1 eq_refl) as [V|[c R]].
    + match goal with T : Typing _ _ a (a_CEq _ _ _ _ _) |- _ => recognize_value T V end.
      destruct a; simpl in K; try contradiction.
      right; eauto 4 using typing_lc with reduction_rules.
    + right; eauto 4 using typing_lc with reduction_rules.
  - destruct (IHTyping eq_refl) as [V|[c R]].
    + recognize_value H V.
      pose proof (typing_lc H) as Lb.
      destruct a; simpl in K; try contradiction; subst.
      inversion Lb; subst; right; eauto with reduction_rules.
    + right; eauto with reduction_rules.
  - destruct (IHTyping eq_refl) as [V|[c R]].
    + recognize_value H V.
      pose proof (typing_lc H) as Lb.
      destruct a; simpl in K; try contradiction; subst.
      inversion Lb; subst; right; eauto with reduction_rules.
    + right; eauto with reduction_rules.
  - destruct (IHTyping1 eq_refl) as [V|[c R]].
    + recognize_value H V.
      pose proof (typing_lc H) as Lb.
      destruct a; simpl in K; try contradiction; subst.
      inversion Lb; subst; right; eauto with reduction_rules.
    + right; eauto with reduction_rules.
  - destruct (IHTyping1 eq_refl) as [V|[c R]].
    + recognize_value H V.
      destruct a; simpl in K; try contradiction; right.
      * exists b0; apply R_IfTrue; eauto using typing_lc.
      * exists b1; apply R_IfFalse; eauto using typing_lc.
    + right; exists (a_If c b0 b1); apply R_If; eauto using typing_lc.
Qed.

Lemma gdefeq_weaken : forall P p a b, GDefEq P p a b ->
  forall Q, uniq Q -> eincl P Q -> GDefEq Q p a b.
Proof.
  intros P p a b H Q U I; apply zig_gdefeq.
  eapply (zig_map (f := fun t => t)); [intros; eapply (proj1 par_weaken); eassumption|].
  exact (proj1 gdefeq_zig _ _ _ _ H).
Qed.

Lemma defeq_weaken : forall P a b, DefEq P a b -> forall Q,
  uniq Q -> eincl P Q -> DefEq Q a b.
Proof. induction 1; eauto using gdefeq_weaken, E_One, E_Trans. Qed.

Lemma defeq_subst : forall P a b, DefEq P a b -> forall Q x r u,
  binds x r P -> ewithout x P Q -> (forall p, CPar Q p r u u) ->
  DefEq Q (subst_tm u x a) (subst_tm u x b).
Proof.
  induction 1; intros Q x r u B W R; [|eauto using E_Trans].
  eapply E_One; apply zig_gdefeq.
  eapply (zig_map (f := subst_tm u x)); [intros; eapply (proj1 par_substitution); eauto|].
  exact (proj1 gdefeq_zig _ _ _ _ H).
Qed.

Lemma labels_app : forall E F, labels (E ++ F) = labels E ++ labels F.
Proof. intros; apply map_app. Qed.

Lemma binds_insert : forall (A : Type) (E D F : list (atom * A)) x a,
  binds x a (E ++ D) -> binds x a (E ++ F ++ D).
Proof. intros; apply binds_app_1 in H; destruct H; eauto using binds_app_l, binds_app_r. Qed.

Lemma labels_insert : forall E D F, eincl (labels (E ++ D)) (labels (E ++ F ++ D)).
Proof. unfold eincl; intros; rewrite !labels_app in H *; apply binds_insert; assumption. Qed.

(* Inserting a context fragment commutes with extending under a binder. *)
Lemma typing_weaken_mut :
  (forall W p a A, Typing W p a A -> forall E D F,
    W = E ++ D -> Ctx (F ++ D) -> uniq (E ++ F ++ D) ->
    Typing (E ++ F ++ D) p a A) /\
  (forall W, Ctx W -> forall E D F,
    W = E ++ D -> Ctx (F ++ D) -> uniq (E ++ F ++ D) -> Ctx (E ++ F ++ D)).
Proof.
  apply typing_ctx_ind; intros; subst.
  all: try solve [eauto 4 using binds_insert with typing_rules].
  all: try solve [
    eapply T_Conv;
    [ solve [eapply H; eauto] | solve [eapply H0; eauto] |
      eapply defeq_weaken; [eassumption|apply labels_uniq; assumption|apply labels_insert] ]].
  all: try solve [
    first [eapply T_Pi with (L := L \u dom (E ++ F ++ D)) |
           eapply T_Abs with (L := L \u dom (E ++ F ++ D)) |
           eapply T_SSigma with (L := L \u dom (E ++ F ++ D)) |
           eapply T_Transp with (L := L \u dom (E ++ F ++ D))];
    try solve [eauto];
    let z := fresh "z" in let Z := fresh "Z" in intros z Z;
    match goal with IH : forall x, x \notin _ -> forall _ _ _, _ -> _ -> _ -> Typing _ _ _ _
      |- Typing (?z ~ ?t ++ ?e ++ ?f ++ ?d) _ _ _ =>
      apply (IH z ltac:(fsetdec) (z ~ t ++ e) d f); [reflexivity|eassumption|solve_uniq]
    end].
  all: try solve [first [eapply T_CEq|eapply T_SPair|eapply T_If]; eauto].
  - destruct E; [exact H0|discriminate].
  - destruct E as [|[y [k T]] E]; [assumption|].
    simpl in *.
    match goal with Eq : (_ :: _) = (_ :: _) |- _ =>
      inversion Eq; subst
    end.
    eapply Ctx_Cons with (psi := psi) (s := s);
      [apply H|apply H0|]; try reflexivity; try assumption; solve_uniq.
Qed.

Lemma typing_prepend : forall W p a A, Typing W p a A -> forall E,
  Ctx (E ++ W) -> Typing (E ++ W) p a A.
Proof.
  intros W p a A T E C; exact (proj1 typing_weaken_mut _ _ _ _ T nil W E eq_refl C (ctx_uniq C)).
Qed.

Lemma fresh_open_l : forall a k x y,
  y \notin fv_tm (open_tm_wrt_tm_rec k (a_Var_f x) a) -> y \notin fv_tm a.
Proof.
  induction a; simpl; intros; try solve [assumption | fsetdec].
  all: try solve [repeat apply notin_union; eauto with lngen].
  all: try solve [
    repeat apply notin_union;
    first [eapply IHa1 | eapply IHa2 | eapply IHa3 | eapply IHa]; fsetdec].
Qed.

Lemma typing_fresh_mut :
  (forall W p a A, Typing W p a A -> forall x, x \notin dom W -> x \notin fv_tm a) /\
  (forall W, Ctx W -> forall x y p A, x \notin dom W -> binds y (p,A) W -> x \notin fv_tm A).
Proof.
  apply typing_ctx_ind; intros; simpl.
  all: try solve [fsetdec | auto | match goal with H : binds _ _ nil |- _ => inversion H end].
  all: try solve [
    match goal with H : binds ?y _ ?W, F : ?x \notin dom ?W |- _ =>
      pose proof (@binds_In _ _ _ _ H); fsetdec
    end].
  all: try solve [
    repeat apply notin_union; auto;
      match goal with IH : forall x, x \notin _ -> x \notin fv_tm (a_Pi _ _ _) |- _ =>
        specialize (IH _ ltac:(eassumption)); simpl in IH; fsetdec
      end].
  all: try solve [
    match goal with B : binds _ (_, _) (_ ++ _) |- _ =>
      analyze_binds B;
      [inversion BindsTacVal; subst; eauto 5 with lngen | eauto 5 with lngen]
    end].
  all: apply notin_union.
  all: try solve [auto].
  all: try solve [specialize (H0 _ ltac:(eassumption)); simpl in H0; fsetdec].
  all: lazymatch goal with
    | IH : forall z, z \notin ?L -> forall x, x \notin dom (_ ++ ?W) -> x \notin fv_tm (open_tm_wrt_tm ?b (a_Var_f z)),
      F : ?x \notin dom ?W |- ?x \notin fv_tm ?b =>
      let z := fresh "z" in let N := fresh "N" in fresh_atom z (L \u {{x}}) N;
      apply (@fresh_open_l b 0 z x);
      apply (IH z); [fsetdec|simpl; fsetdec]
    end.
Qed.

Lemma typing_raise : forall W p a A, Typing W p a A ->
  forall q, p <= q -> Typing W q a A.
Proof.
  induction 1; intros q M; try solve [eauto 4 with typing_rules].
  all: try solve [
    first [eapply T_Pi with (L := L) | eapply T_Abs with (L := L) |
           eapply T_SSigma with (L := L) | eapply T_Transp with (L := L)];
    eauto].
  all: try solve [eapply T_Var with (psi0 := psi0);
    try eassumption; eapply Order.POrderTheory.le_trans; eassumption].
  all: try solve [
    first [eapply T_CEq | eapply T_Unbox | eapply T_Proj1 | eapply T_If | eapply T_SPair];
    try solve [eauto]; eapply Order.POrderTheory.le_trans; eassumption].
Qed.

Lemma labels_subst : forall E x u, labels (subst_ctx u x E) = labels E.
Proof. induction E as [|[y [r A]] E IH]; simpl; intros; [reflexivity|now rewrite IH]. Qed.

Lemma dom_subst : forall E x u, dom (subst_ctx u x E) = dom E.
Proof. intros; rewrite <- !labels_dom; rewrite labels_subst; reflexivity. Qed.

Lemma labels_remove : forall E D x r U u,
  ewithout x (labels (E ++ x ~ (r,U) ++ D)) (labels (subst_ctx u x E ++ D)).
Proof.
  unfold ewithout; intros E D x r U u y q N H.
  rewrite !labels_app in H *.
  rewrite labels_subst.
  simpl in H; apply binds_app_1 in H; destruct H as [B|B].
  - apply binds_app_l; assumption.
  - apply binds_app_r; analyze_binds B; congruence.
Qed.

Lemma binds_subst_prefix : forall E x u y p A,
  binds y (p,A) E -> binds y (p,subst_tm u x A) (subst_ctx u x E).
Proof.
  induction E as [|[z [q B]] E IH]; simpl; intros; [contradiction|].
  analyze_binds H.
  - inversion BindsTacVal; subst; left; reflexivity.
Qed.

Lemma binds_subst_ctx : forall E D x r U u y p A,
  Ctx D -> x \notin dom D -> y <> x ->
  binds y (p,A) (E ++ x ~ (r,U) ++ D) ->
  binds y (p,subst_tm u x A) (subst_ctx u x E ++ D).
Proof.
  intros E D x r U u y p A C F N B; apply binds_app_1 in B; destruct B as [B|B].
  - apply binds_app_l; apply binds_subst_prefix; assumption.
  - analyze_binds B.
    apply binds_app_r.
    assert (S : subst_tm u x A = A).
    { apply subst_fresh; eapply (proj2 typing_fresh_mut); eassumption. }
    now rewrite S.
Qed.

Ltac substitute_opening :=
  repeat match goal with
  | C : lc_tm ?u |- context [subst_tm ?u ?x (open_tm_wrt_tm ?a ?v)] =>
    rewrite (@subst_open a u v x C)
  end.

Ltac substitute_binder :=
  repeat match goal with
  | C : lc_tm ?u, D : ?z <> ?x |- context [open_tm_wrt_tm (subst_tm ?u ?x ?a) (a_Var_f ?z)] =>
    rewrite <- (@subst_open_distinct a u x z C D)
  end.

(* Substitution acts on the term, its type, and the context prefix. *)
Lemma typing_subst_mut :
  (forall W p a A, Typing W p a A -> forall E D x r U u,
    W = E ++ x ~ (r,U) ++ D -> Typing D r u U ->
    Typing (subst_ctx u x E ++ D) p (subst_tm u x a) (subst_tm u x A)) /\
  (forall W, Ctx W -> forall E D x r U u,
    W = E ++ x ~ (r,U) ++ D -> Typing D r u U ->
    Ctx (subst_ctx u x E ++ D)).
Proof.
  apply typing_ctx_ind; intros; subst.
  all: match goal with T : Typing ?D ?r ?u ?U |- context [subst_ctx ?u _ _ ++ ?D] =>
    let K := fresh "closed" in pose proof (typing_lc T) as K
  end.
  all: substitute_opening.
  all: cbn [subst_tm].
  all: try solve [eauto 4 with typing_rules].
  - assert (C : Ctx (subst_ctx u x0 E ++ D)) by (apply H with (r := r) (U := U); auto).
    assert (F : x0 \notin dom D) by (pose proof (ctx_uniq c); solve_uniq).
    destruct (eq_var x x0) as [->|N]; simpl.
    + assert (K : binds x0 (r,U) (E ++ x0 ~ (r,U) ++ D)).
      { apply binds_app_r; apply binds_app_l; apply binds_one; reflexivity. }
      pose proof (@binds_unique _ _ _ _ _ b K (ctx_uniq c)) as S.
      inversion S; subst psi0 A.
      assert (R : exists k s, Typing D k U (a_Type s)).
      { pose proof c as C0.
        clear H b K c C.
        induction E as [|v E IH]; simpl in C0.
        - inversion C0; subst; eauto.
        - inversion C0; subst; eauto. }
      destruct R as [k [s T]].
      rewrite (subst_fresh u (proj1 typing_fresh_mut _ _ _ _ T x0 F)).
      eapply typing_raise; [exact (typing_prepend H1 C)|assumption].
    + eapply T_Var with (psi0 := psi0); try assumption.
      eapply binds_subst_ctx; eauto using typing_ctx.
  all: try solve [
    eapply T_Conv; [eapply H; eauto|eapply H0; eauto|];
    eapply defeq_subst;
    [eassumption|
     eapply labels_binds; apply binds_app_r; apply binds_app_l; apply binds_one; reflexivity|
     apply labels_remove|
     intro q; eapply typed_cpar; eapply typing_prepend; [eassumption|];
     eapply typing_ctx; eapply H; eauto] ].
  all: try solve [
    first [eapply T_CEq | eapply T_SPair | eapply T_If];
    try solve [eauto];
    repeat match goal with
    | IH : forall _ _ _ _ _ _, _ -> Typing _ _ _ _ -> Typing _ _ _ _,
      T : Typing ?D ?r ?u ?U |- Typing (subst_ctx ?u ?x ?E ++ ?D) _ _ _ =>
      let K := fresh "K" in pose proof (IH E D x r U u eq_refl T) as K; clear IH
    end;
    match goal with
    | C : lc_tm ?u, K : Typing _ _ _ (subst_tm ?u ?x (open_tm_wrt_tm ?B ?v)) |- _ =>
      rewrite (@subst_open B u v x C) in K
    end;
    eassumption].
  all: try solve [
    first [eapply T_Pi with (L := L \u {{x}}) |
           eapply T_Abs with (L := L \u {{x}}) |
           eapply T_SSigma with (L := L \u {{x}}) |
           eapply T_Transp with (L := L \u {{x}})];
    try solve [eauto];
    try solve [rewrite <- subst_open; [eauto|assumption]];
    let z := fresh "z" in let Z := fresh "Z" in intros z Z;
    assert (N : z <> x) by fsetdec;
    substitute_binder;
    match goal with
    | IH : forall z, z \notin _ -> forall _ _ _ _ _ _, _ -> Typing _ _ _ _ -> Typing _ _ _ _,
      T : Typing ?D ?r ?u ?U
      |- Typing (?z ~ (?k, subst_tm ?u ?x ?A) ++ subst_ctx ?u ?x ?E ++ ?D) _ _ _ =>
      apply (IH z ltac:(fsetdec) (z ~ (k,A) ++ E) D x r U u eq_refl T)
    end].
  all: try solve [destruct E; simpl in *; [eauto using typing_ctx|discriminate]].
  - eapply T_Transp with (L := L \u {{x}}) (psi0 := psi0) (psi1 := psi1)
      (A := subst_tm u x A) (a0 := subst_tm u x a0) (s := s) (psi2 := psi2) (s1 := s1).
    + intros z F; assert (N : z <> x) by fsetdec.
      substitute_binder.
      exact (H z ltac:(fsetdec) (z ~ (psi1,A) ++ E) D x r U u eq_refl H4).
    + exact (H0 E D x r U u eq_refl H4).
    + rewrite <- (subst_open B a0 x closed); exact (H1 E D x r U u eq_refl H4).
    + exact (H2 E D x r U u eq_refl H4).
  - destruct E as [|[y [k T]] E]; [simpl; eauto using typing_ctx|].
    simpl in *.
    match goal with Eq : (_ :: _) = (_ :: _) |- _ => inversion Eq; subst end.
    eapply Ctx_Cons with (psi := psi) (s := s).
    + eapply H; [reflexivity|eassumption].
    + eapply H0; [reflexivity|eassumption].
    + rewrite dom_app dom_subst.
      rewrite dom_app in n; simpl in n; fsetdec.
Qed.

Lemma typing_open : forall W p r U a A u L,
  (forall x, x \notin L -> Typing (x ~ (r,U) ++ W) p
     (open_tm_wrt_tm a (a_Var_f x)) (open_tm_wrt_tm A (a_Var_f x))) ->
  Typing W r u U -> Typing W p (open_tm_wrt_tm a u) (open_tm_wrt_tm A u).
Proof.
  intros W p r U a A u L H T.
  fresh_atom x (L \u fv_tm a \u fv_tm A) F.
  assert (N : x \notin L) by fsetdec.
  pose proof (proj1 typing_subst_mut _ _ _ _ (H x N) nil W x r U u eq_refl T) as S.
  rewrite !open_subst_var in S; try fsetdec; exact S.
Qed.

Lemma typing_open_sort : forall W p r U a s u L,
  (forall x, x \notin L -> Typing (x ~ (r,U) ++ W) p
     (open_tm_wrt_tm a (a_Var_f x)) (a_Type s)) ->
  Typing W r u U -> Typing W p (open_tm_wrt_tm a u) (a_Type s).
Proof.
  intros; eapply (@typing_open W p r U a (a_Type s) u L); eauto.
Qed.

Definition IsType W A := exists p s, Typing W p A (a_Type s).
Definition BinderType W r A B :=
  exists p s L, IsType W A /\
    (forall x, x \notin L ->
       Typing (x ~ (r,A) ++ W) p (open_tm_wrt_tm B (a_Var_f x)) (a_Type s)).

Lemma formation : forall W p a A, Typing W p a A ->
  match a with
  | a_Pi r U B | a_SSigma r U B => BinderType W r U B
  | a_T _ U => IsType W U
  | a_CEq _ a b r U => Typing W r a U /\ Typing W r b U
  | _ => True
  end.
Proof.
  induction 1; simpl; unfold BinderType, IsType in *; eauto 8.
Qed.

Lemma binding_is_type : forall W, Ctx W -> forall x r A,
  binds x (r,A) W -> IsType W A.
Proof.
  induction 1; intros y r B K; [inversion K|].
  analyze_binds K.
  - inversion BindsTacVal; subst.
    exists psi, s; eapply typing_prepend; [eassumption|eauto using Ctx_Cons].
  - destruct (IHCtx _ _ _ ltac:(eassumption)) as [p [s' T]].
    exists p, s'; eapply typing_prepend; [exact T|eauto using Ctx_Cons].
Qed.

Lemma opened_is_type : forall W r A B u, BinderType W r A B ->
  Typing W r u A -> IsType W (open_tm_wrt_tm B u).
Proof.
  intros W r A B u [p [s [L [_ K]]]] T.
  exists p, s; eapply typing_open_sort; eassumption.
Qed.

(* Every result type of a typing derivation has a sort. *)
Lemma type_correct : forall W p a A, Typing W p a A -> IsType W A.
Proof.
  induction 1; try solve [unfold IsType; eauto 5].
  all: try solve [eapply binding_is_type; eassumption].
  all: try solve [
    match goal with |- IsType ?W (a_Type ?s) =>
      destruct (sort_regularity s) as [s' K];
      exists psi, s'; apply T_Type; eauto using typing_ctx
    end].
  all: try solve [
    match goal with
    | H : IsType _ (a_Pi _ _ _) |- _ =>
      destruct H as [q [s' T]]; pose proof (formation T) as F;
      eapply opened_is_type; eassumption
    | H : IsType _ (a_SSigma _ _ _) |- _ =>
      destruct H as [q [s' T]]; pose proof (formation T) as F;
      first [eapply opened_is_type; eassumption|
             destruct F as [? [? [? [? _]]]]; assumption]
    | H : IsType _ (a_T _ _) |- _ =>
      destruct H as [q [s' T]]; exact (formation T)
    end].
  all: try solve [
    match goal with H : IsType _ (a_CEq _ _ _ _ _) |- _ =>
      destruct H as [q [s' T]]; destruct (formation T) as [_ V];
      unfold IsType; eexists; eexists; eapply typing_open_sort; eassumption
    end].
  - destruct IHTyping1 as [q [s T]]; exact (opened_is_type (formation T) H0).
  - destruct IHTyping1 as [q [s T]]; exact (opened_is_type (formation T) H0).
Qed.

Lemma conv_of_stars : forall P a b c, ParStar P a c -> ParStar P b c -> Convertible P a b.
Proof.
  intros; eapply conv_trans; [exact (star_eq H)|apply conv_sym; exact (star_eq H0)].
Qed.

Definition binder_type (sigma : bool) := if sigma then a_SSigma else a_Pi.

Lemma par_binder_parts : forall P p sigma r A B t,
  Par P p (binder_type sigma r A B) t ->
  exists A' B', t = binder_type sigma r A' B' /\ Par P p A A' /\
    forall u, CPar P p r u u -> Par P p (open_tm_wrt_tm B u) (open_tm_wrt_tm B' u).
Proof.
  intros; destruct sigma; inversion H; subst.
  all: do 2 eexists; (split; [reflexivity|split; [eassumption|]]).
  all: intros; eapply par_open; eassumption.
Qed.

Lemma star_binder_parts : forall P a t, ParStar P a t ->
  forall sigma r A B, a = binder_type sigma r A B ->
  exists A' B', t = binder_type sigma r A' B' /\ ParStar P A A' /\
    forall u, (forall p, CPar P p r u u) ->
      ParStar P (open_tm_wrt_tm B u) (open_tm_wrt_tm B' u).
Proof.
  induction 1; intros sigma r U B E; subst a.
  - exists U, B; eauto using star_refl.
  - destruct (par_binder_parts H) as [U' [B' [-> [A C]]]].
    destruct (IHParStar _ _ _ _ eq_refl) as [U'' [B'' [-> [D E]]]].
    exists U'', B''; split; [reflexivity|]; split; eauto using star_step.
Qed.

(* Projection of the common reduct gives injectivity of dependent types. *)
Lemma conv_binder : forall P sigma r A B A' B',
  Convertible P (binder_type sigma r A B) (binder_type sigma r A' B') ->
  Convertible P A A' /\ forall u, (forall p, CPar P p r u u) ->
    Convertible P (open_tm_wrt_tm B u) (open_tm_wrt_tm B' u).
Proof.
  intros P sigma r A B A' B' K.
  destruct (conv_join K) as [c [L R]].
  destruct (@star_binder_parts P _ _ L sigma r A B eq_refl) as [U [D [-> [F G]]]].
  destruct (@star_binder_parts P _ _ R sigma r A' B' eq_refl) as [U' [D' [E [F' G']]]].
  destruct sigma; simpl in E; inversion E; subst.
  all: split; [exact (conv_of_stars F F')|intros u C; exact (conv_of_stars (G u C) (G' u C))].
Qed.

Lemma star_t_parts : forall P a t, ParStar P a t ->
  forall r A, a = a_T r A -> exists A', t = a_T r A' /\ ParStar P A A'.
Proof.
  induction 1; intros r A E; subst a; [eauto using star_refl|].
  inversion H; subst.
  destruct (IHParStar _ _ eq_refl) as [U [-> R]].
  eauto using star_step.
Qed.

Lemma conv_t : forall P r A B, Convertible P (a_T r A) (a_T r B) -> Convertible P A B.
Proof.
  intros P r A B E.
  destruct (conv_join E) as [c [L R]].
  destruct (@star_t_parts P _ _ L r A eq_refl) as [D [-> K]].
  destruct (@star_t_parts P _ _ R r B eq_refl) as [D' [E' K']].
  inversion E'; subst; eauto using conv_of_stars.
Qed.

(* Regrade a step using a reflexive step at the lower grade. This is
   used for the endpoints of an internal equality. *)
Lemma zig_lower_step : forall P p r a b, r <= p ->
  Par P r a a -> Par P p a b -> Zig P r a b.
Proof.
  intros P p r a b E R S.
  destruct (proj1 par_diamond _ _ _ _ S _ _ R) as [c [B A]].
  rewrite (Order.LatticeTheoryMeet.meet_r E) in A B.
  eauto using zig_step, zig_sym, zig_trans.
Qed.

Lemma star_ceq_parts : forall P a t, ParStar P a t ->
  forall r u v q A, a = a_CEq r u v q A ->
  Par P r u u -> Par P r v v ->
  exists u' v' A', t = a_CEq r u' v' q A' /\ Zig P r u u' /\ Zig P r v v'.
Proof.
  induction 1; intros r u v q A E U V; subst a.
  - do 3 eexists; repeat split; eauto using zig_step.
  - inversion H; subst.
    assert (L : Zig P r u a1) by eauto using zig_lower_step.
    assert (R : Zig P r v b1) by eauto using zig_lower_step.
    destruct (IHParStar _ _ _ _ _ eq_refl
      (proj2 (zig_endpoints L)) (proj2 (zig_endpoints R))) as [u' [v' [A' [-> [L' R']]]]].
    exists u', v', A'; eauto using zig_trans.
Qed.

Lemma conv_ceq_refl : forall P r q u a b A B,
  Convertible P (a_CEq r u u q A) (a_CEq r a b q B) ->
  Par P r u u -> Par P r a a -> Par P r b b -> Zig P r a b.
Proof.
  intros P r q u a b A B E U R S.
  destruct (conv_join E) as [c [L K]].
  destruct (@star_ceq_parts P _ _ L r u u q A eq_refl U U) as [x [y [T [-> [X Y]]]]].
  destruct (@star_ceq_parts P _ _ K r a b q B eq_refl R S) as [x' [y' [T' [E' [J J']]]]].
  inversion E'; subst.
  eapply zig_trans; [exact J|].
  eapply zig_trans; [apply zig_sym; exact X|].
  eapply zig_trans; [exact Y|apply zig_sym; exact J'].
Qed.

Definition intro_view W p a A :=
  match a with
  | a_Abs r U b => exists B L,
      BinderType W r U B /\
      (forall x, x \notin L -> Typing (x ~ (r, U) ++ W) p
         (open_tm_wrt_tm b (a_Var_f x)) (open_tm_wrt_tm B (a_Var_f x))) /\
      Convertible (labels W) (a_Pi r U B) A
  | a_SPair a r b => exists U B, Typing W r a U /\
      Typing W p b (open_tm_wrt_tm B a) /\ Convertible (labels W) (a_SSigma r U B) A
  | a_Box r a => exists U, Typing W r a U /\ Convertible (labels W) (a_T r U) A
  | a_Refl => exists r q a U,
      Typing W q a U /\ Convertible (labels W) (a_CEq r a a q U) A /\ q <= r
  | _ => True
  end.

Lemma ceq_grades : forall W p a A, Typing W p a A ->
  match a with a_CEq r _ _ q _ => q <= r | _ => True end.
Proof. induction 1; simpl; eauto. Qed.

Lemma introduction : forall W p a A, Typing W p a A -> intro_view W p a A.
Proof.
  induction 1; simpl; try exact I.
  - exists B, L; repeat split; try assumption; [exact (formation H1)|left; reflexivity].
  - destruct a; cbn [intro_view] in *; try exact I.
    + destruct IHTyping1 as [D [K [F [G C]]]].
      exists D, K; split; [exact F|split; [exact G|]].
      eapply conv_trans; [exact C|right; eassumption].
    + destruct IHTyping1 as [r [q [u [U [F [C Le]]]]]].
      exists r, q, u, U; split; [exact F|split; [|exact Le]].
      eapply conv_trans; [exact C|right; eassumption].
    + destruct IHTyping1 as [U [F C]].
      exists U; split; [exact F|].
      eapply conv_trans; [exact C|right; eassumption].
    + destruct IHTyping1 as [U [D [F [G C]]]].
      exists U, D; split; [exact F|split; [exact G|]].
      eapply conv_trans; [exact C|right; eassumption].
  - exists psi0, psi1, a, A; repeat split; try solve [left; reflexivity].
    + exact (proj1 (formation H)).
    + exact (ceq_grades H).
  - exists A; split; [assumption|left; reflexivity].
  - exists A, B; repeat split; try assumption; left; reflexivity.
Qed.

Lemma typing_convert : forall W p a A B, Typing W p a A ->
  IsType W B -> Convertible (labels W) A B -> Typing W p a B.
Proof.
  intros W p a A B T [q [s F]] [->|E]; [exact T|eauto using T_Conv].
Qed.

Lemma cpar_source : forall P p r a b, CPar P p r a b -> CPar P p r a a.
Proof. inversion 1; subst; eauto using par_source with safety. Qed.

Lemma red_par : forall a b, Red a b ->
  forall P p c, Par P p a c -> Par P p a b.
Proof.
  induction 1; intros P p c V; inversion V; subst; clear V;
    try solve [
      first [eapply Par_App | eapply Par_AppBeta | eapply Par_Transp | eapply Par_TranspRefl |
        eapply Par_Unbox | eapply Par_UnboxBox | eapply Par_Proj1Cong |
        eapply Par_Proj2Cong | eapply Par_Proj1Beta | eapply Par_Proj2Beta |
        eapply Par_If | eapply Par_IfTrue | eapply Par_IfFalse];
      eauto 3 using par_source, cpar_source].
  all: eapply Par_IfFalse; eauto 3 using par_source.
Qed.

Lemma open_par_congr : forall W p r A B s L u v,
  (forall x, x \notin L -> Typing (x ~ (r,A) ++ W) p
    (open_tm_wrt_tm B (a_Var_f x)) (a_Type s)) ->
  CPar (labels W) p r u v ->
  Par (labels W) p (open_tm_wrt_tm B u) (open_tm_wrt_tm B v).
Proof.
  intros W p r A B s L u v T R.
  eapply (@par_open _ p r B B L); [|exact R].
  intros x F; exact (typed_readable (T x F) (Order.POrderTheory.lexx _)).
Qed.

Lemma open_red_conv : forall W r A B u v,
  BinderType W r A B -> Typing W r u A -> Typing W r v A ->
  Red u v -> Convertible (labels W) (open_tm_wrt_tm B u) (open_tm_wrt_tm B v).
Proof.
  intros W r A B u v [p [s [L [_ F]]]] U V R; right; eapply E_One.
  apply par_to_gdefeq; eapply open_par_congr; [exact F|].
  destruct (r <= p) eqn:E.
  - apply CPar_Leq; [exact E|eapply red_par; [exact R|exact (typed_readable U E)]].
  - apply CPar_Nleq; eauto using typing_lc, labels_uniq, ctx_uniq, typing_ctx; congruence.
Qed.

Lemma pi_type_correct : forall W p a r A B,
  Typing W p a (a_Pi r A B) -> BinderType W r A B.
Proof. intros; destruct (type_correct H) as [q [s T]]; exact (formation T). Qed.

Lemma sigma_type_correct : forall W p a r A B,
  Typing W p a (a_SSigma r A B) -> BinderType W r A B.
Proof. intros; destruct (type_correct H) as [q [s T]]; exact (formation T). Qed.

Lemma binder_domain : forall W r A B, BinderType W r A B -> IsType W A.
Proof. intros W r A B [? [? [? [? _]]]]; assumption. Qed.

(* The reduction rules that eliminate an introduction form need inversion
   through conversion. *)
Lemma app_beta_typing : forall W p r U b u A B,
  Typing W p (a_Abs r U b) (a_Pi r A B) -> Typing W r u A ->
  Typing W p (open_tm_wrt_tm b u) (open_tm_wrt_tm B u).
Proof.
  intros W p r U b u A B T V.
  destruct (introduction T) as [B' [L [WF [Body E]]]].
  destruct (@conv_binder _ false r U B' A B E) as [D K].
  assert (V' : Typing W r u U) by eauto using typing_convert, binder_domain, conv_sym.
  eapply typing_convert.
  - eapply typing_open; eassumption.
  - eapply opened_is_type; [exact (pi_type_correct T)|exact V].
  - apply K; exact (typed_cpar V).
Qed.

Lemma unbox_beta_typing : forall W p r a A,
  Typing W p (a_Box r a) (a_T r A) -> r <= p -> Typing W p a A.
Proof.
  intros W p r a A T H.
  destruct (introduction T) as [U [V E]].
  destruct (type_correct T) as [q [s WF]].
  eapply typing_convert; [exact (typing_raise V H)|exact (formation WF)|exact (conv_t E)].
Qed.

Lemma proj1_beta_typing : forall W p r a b A B,
  Typing W p (a_SPair a r b) (a_SSigma r A B) -> r <= p -> Typing W p a A.
Proof.
  intros W p r a b A B T H.
  destruct (introduction T) as [U [D [F [_ E]]]].
  destruct (@conv_binder _ true r U D A B E) as [J _].
  eapply typing_convert; [exact (typing_raise F H)| |exact J].
  exact (binder_domain (sigma_type_correct T)).
Qed.

Lemma proj2_beta_typing : forall W p r a b A B,
  Typing W p (a_SPair a r b) (a_SSigma r A B) ->
  Typing W r (a_Proj1 r (a_SPair a r b)) A ->
  Typing W p b (open_tm_wrt_tm B (a_Proj1 r (a_SPair a r b))).
Proof.
  intros W p r a b A B T V.
  destruct (introduction T) as [U [D [F [G E]]]].
  destruct (@conv_binder _ true r U D A B E) as [J K].
  pose proof (sigma_type_correct T) as WF.
  assert (F' : Typing W r a A) by eauto using typing_convert, binder_domain.
  eapply typing_convert; [exact G|exact (opened_is_type WF V)|].
  eapply conv_trans.
  - apply K; exact (typed_cpar F).
  - apply conv_sym; eapply open_red_conv; [exact WF|exact V|exact F'|].
    apply R_Proj1Beta; eauto using typing_lc.
Qed.

Lemma transp_beta_typing : forall W p r q a b A B t L s,
  (forall x, x \notin L -> Typing (x ~ (q,A) ++ W) r
    (open_tm_wrt_tm B (a_Var_f x)) (a_Type s)) ->
  Typing W p a_Refl (a_CEq r a b q A) ->
  Typing W p t (open_tm_wrt_tm B a) -> Typing W p t (open_tm_wrt_tm B b).
Proof.
  intros W p r q a b A B t L s Body T V.
  destruct (introduction T) as [r' [q' [u [U [F [E Le]]]]]].
  pose proof (conv_consistent E eq_refl eq_refl) as Tags.
  simpl in Tags; inversion Tags; subst r' q'.
  destruct (type_correct T) as [p' [s' WF]].
  destruct (formation WF) as [Ta Tb].
  assert (Z : Zig (labels W) r a b).
  { eapply conv_ceq_refl; [exact E|exact (typed_readable F Le)|
        exact (typed_readable Ta Le)|exact (typed_readable Tb Le)]. }
  eapply typing_convert; [exact V| |].
  - exists r, s; eapply typing_open_sort; eassumption.
  - right; eapply E_One; apply zig_gdefeq.
    eapply (zig_map (f := open_tm_wrt_tm B)); [|exact Z].
    intros u0 v R; eapply open_par_congr; [exact Body|].
    apply CPar_Leq; assumption.
Qed.

Theorem preservation :
    forall a b Γ ψ A,
      Typing Γ ψ a A ->
      Red a b ->
      Typing Γ ψ b A.
Proof.
  intros a b W p A T; revert b.
  induction T; intros t R.
  all: try solve [eapply T_Conv; [eapply IHT1; exact R|eassumption|eassumption]].
  all: inversion R; subst; clear R.
  all: try solve [first [eapply T_App | eapply T_Transp with (L := L) |
      eapply T_Unbox | eapply T_Proj1 | eapply T_If]; eauto].
  all: try solve [eapply app_beta_typing; eassumption].
  all: try solve [eapply unbox_beta_typing; eassumption].
  all: try solve [eapply proj1_beta_typing; eassumption].
  all: try solve [eapply proj2_beta_typing; eassumption].
  all: try solve [eapply transp_beta_typing; eassumption].
  - assert (R1 : Red (a_Proj1 psi0 a) (a_Proj1 psi0 a')) by (apply R_Proj1Cong; assumption).
    pose proof (IHT2 _ R1) as T1'.
    pose proof (sigma_type_correct T1) as WF.
    eapply typing_convert.
    + eapply T_Proj2; [exact (IHT1 _ H2)|exact T1'].
    + exact (opened_is_type WF T2).
    + apply conv_sym; exact (open_red_conv WF T2 T1' R1).
  all: assumption.
Qed.

Theorem progress : forall ψ a A,
  Typing nil ψ a A ->
  Value a \/ exists b, Red a b.
Proof. intros; eapply closed_progress; [eassumption|reflexivity]. Qed.
