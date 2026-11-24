From Qual Require Import Qualitative_ott.
Require Import Metalib.Metatheory.
From Stdlib Require Import Lia.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope order_scope.
Unset SsrRewrite.

(* Opening and substitution for the locally nameless syntax. *)
Local Hint Constructors lc_tm : ni.
Local Hint Resolve binds_cons : assoclist.

Fixpoint closed_at (k : nat) (a : tm) : Prop :=
  match a with
  | a_Var_b i => Nat.lt i k
  | a_Pi _ A B | a_Abs _ A B | a_SSigma _ A B =>
      closed_at k A /\ closed_at (S k) B
  | a_App a _ b | a_Transp a b | a_SPair a _ b =>
      closed_at k a /\ closed_at k b
  | a_CEq _ a b _ A | a_If a b A =>
      closed_at k a /\ closed_at k b /\ closed_at k A
  | a_T _ a | a_Box _ a | a_Unbox _ a | a_Proj1 _ a | a_Proj2 _ a =>
      closed_at k a
  | _ => True
  end.

Local Lemma closed_at_open_var a k x :
  closed_at k (open_tm_wrt_tm_rec k (a_Var_f x) a) <-> closed_at (S k) a.
Proof.
  revert k. induction a; intros k; simpl; try tauto;
    try (repeat match goal with
      | IH : forall k, closed_at k _ <-> _ |- _ => rewrite IH
      end; tauto).
  destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; lia.
Qed.

Local Lemma lc_closed_at a : lc_tm a -> closed_at 0 a.
Proof.
  induction 1; simpl; try tauto.
  all: split; [assumption|].
  all: pick fresh x; apply (closed_at_open_var _ 0 x), H1.
Qed.


Fixpoint tm_size (a : tm) : nat :=
  match a with
  | a_Pi _ A B | a_Abs _ A B | a_SSigma _ A B
  | a_App A _ B | a_Transp A B | a_SPair A _ B =>
      S (tm_size A + tm_size B)
  | a_CEq _ a b _ A | a_If a b A =>
      S (tm_size a + tm_size b + tm_size A)
  | a_T _ a | a_Box _ a | a_Unbox _ a | a_Proj1 _ a | a_Proj2 _ a =>
      S (tm_size a)
  | _ => 1
  end.

Local Lemma tm_size_open_var a k x :
  tm_size (open_tm_wrt_tm_rec k (a_Var_f x) a) = tm_size a.
Proof.
  revert k. induction a; intros k; simpl; try congruence.
  destruct (lt_eq_lt_dec n k) as [[?|?]|?]; reflexivity.
Qed.

Local Lemma closed_at_lc a : closed_at 0 a -> lc_tm a.
Proof.
  assert (H : forall n a, Nat.lt (tm_size a) n -> closed_at 0 a -> lc_tm a).
  { induction n as [|n IH]; intros b Hb Hc; [lia|].
    destruct b; simpl in *; try lia; eauto 1 with ni.
    all: constructor;
      try (apply IH; [lia|tauto]).
    all: intros x; apply IH;
      [unfold open_tm_wrt_tm; rewrite tm_size_open_var; lia
      |apply closed_at_open_var; tauto]. }
  apply (H (S (tm_size a))); lia.
Qed.

Local Lemma closed_at_weaken a k j :
  Nat.le k j -> closed_at k a -> closed_at j a.
Proof.
  revert k j. induction a; intros k j H; simpl; try lia; intuition eauto using le_n_S.
Qed.

Local Lemma open_closed_at a u k : closed_at k a -> open_tm_wrt_tm_rec k u a = a.
Proof.
  revert k. induction a; intros k H; simpl in *; try reflexivity;
    try (f_equal; intuition eauto).
  destruct (lt_eq_lt_dec n k) as [[?|?]|?]; try reflexivity; lia.
Qed.

Local Ltac decide_atoms :=
  repeat match goal with
  | |- context [is_left (@eq_dec ?T ?I ?u ?v)] => destruct (@eq_dec T I u v); simpl
  end.

Local Lemma subst_fresh a x u : x \notin fv_tm a -> subst_tm u x a = a.
Proof.
  induction a; simpl; intro H; try reflexivity;
    try (f_equal; eauto 8 with set).
  decide_atoms; [subst; fsetdec|reflexivity].
Qed.

Local Lemma subst_open_rec a x u b k :
  lc_tm u ->
  subst_tm u x (open_tm_wrt_tm_rec k b a) =
  open_tm_wrt_tm_rec k (subst_tm u x b) (subst_tm u x a).
Proof.
  intros Hu. revert k. induction a; intros k; simpl; try congruence.
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; reflexivity.
  - decide_atoms; [|reflexivity].
    symmetry. apply open_closed_at, (closed_at_weaken (k:=0)); auto using lc_closed_at with arith.
Qed.

Local Lemma subst_open a x u b :
  lc_tm u ->
  subst_tm u x (open_tm_wrt_tm a b) =
  open_tm_wrt_tm (subst_tm u x a) (subst_tm u x b).
Proof. apply subst_open_rec. Qed.

Local Lemma open_as_subst_rec a x b k :
  x \notin fv_tm a ->
  open_tm_wrt_tm_rec k b a =
  subst_tm b x (open_tm_wrt_tm_rec k (a_Var_f x) a).
Proof.
  revert k. induction a; intros k H; simpl in *; try reflexivity;
    try (f_equal; eauto 8 with set).
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; auto.
    decide_atoms; congruence.
  - decide_atoms; [subst; fsetdec|reflexivity].
Qed.

Local Lemma open_as_subst a x b :
  x \notin fv_tm a ->
  open_tm_wrt_tm a b = subst_tm b x (open_tm_wrt_tm a (a_Var_f x)).
Proof. apply open_as_subst_rec. Qed.

Local Lemma close_open_subst_rec a x b k :
  closed_at k a ->
  open_tm_wrt_tm_rec k b (close_tm_wrt_tm_rec k x a) = subst_tm b x a.
Proof.
  revert k. induction a; intros k H; simpl in *; try reflexivity;
    try (f_equal; intuition eauto).
  - destruct (lt_dec n k); [|lia].
    simpl. destruct (lt_eq_lt_dec n k) as [[?|?]|?]; try reflexivity; lia.
  - decide_atoms; try congruence.
    simpl. destruct (lt_eq_lt_dec k k) as [[?|?]|?]; try reflexivity; lia.
Qed.

Local Lemma close_open_subst a x b :
  lc_tm a ->
  open_tm_wrt_tm (close_tm_wrt_tm x a) b = subst_tm b x a.
Proof. intros H; apply close_open_subst_rec, lc_closed_at, H. Qed.

Local Lemma close_open_var_rec a x k :
  x \notin fv_tm a ->
  close_tm_wrt_tm_rec k x (open_tm_wrt_tm_rec k (a_Var_f x) a) = a.
Proof.
  revert k. induction a; intros k H; simpl in *; try reflexivity;
    try (f_equal; eauto 8 with set).
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl.
    + destruct (lt_dec n k); simpl; try reflexivity; lia.
    + decide_atoms; congruence.
    + destruct (lt_dec (n - 1) k); simpl; [lia|f_equal; lia].
  - decide_atoms; [subst; fsetdec|reflexivity].
Qed.

Local Lemma close_open_var a x :
  x \notin fv_tm a ->
  close_tm_wrt_tm x (open_tm_wrt_tm a (a_Var_f x)) = a.
Proof. apply close_open_var_rec. Qed.

Local Lemma closed_subst a u x k :
  closed_at k a -> lc_tm u -> closed_at k (subst_tm u x a).
Proof.
  intros H Hu; revert k H. induction a; intros k H; simpl in *; try solve [intuition eauto].
  - decide_atoms; simpl; auto.
    eapply closed_at_weaken with (k:=0); [lia|apply lc_closed_at; eauto].
  all: intuition eauto.
Qed.

Local Lemma lc_subst a u x : lc_tm a -> lc_tm u -> lc_tm (subst_tm u x a).
Proof. eauto using closed_at_lc, closed_subst, lc_closed_at. Qed.

Local Lemma lc_from_open a x :
  lc_tm (open_tm_wrt_tm a (a_Var_f x)) ->
  forall y, lc_tm (open_tm_wrt_tm a (a_Var_f y)).
Proof.
  intros H y. apply closed_at_lc, closed_at_open_var.
  apply (closed_at_open_var a 0 x). apply lc_closed_at; exact H.
Qed.

Local Lemma lc_open_with a u x :
  x \notin fv_tm a -> lc_tm (open_tm_wrt_tm a (a_Var_f x)) ->
  lc_tm u -> lc_tm (open_tm_wrt_tm a u).
Proof. intros H; rewrite (@open_as_subst a x u H); auto using lc_subst. Qed.

Local Hint Resolve lc_subst : ni.

(* Parallel reduction with unrestricted context weakening. *)
Inductive CStep : econtext -> grade -> grade -> tm -> tm -> Prop :=
 | CStep_Leq : forall (P:econtext) (psi psi0:grade) (a1 a2:tm),
      ( psi0  <=  psi )  ->
     PStep P psi a1 a2 ->
     CStep P psi psi0 a1 a2
 | CStep_Nleq : forall (P:econtext) (psi psi0:grade) (a1 a2:tm),
     lc_tm a1 ->
     lc_tm a2 ->
      not ( psi0  <=  psi )  ->
     CStep P psi psi0 a1 a2
with PStep : econtext -> grade -> tm -> tm -> Prop :=
 | PStep_Var : forall (P:econtext) (psi:grade) (x:tmvar) (psi0:grade),
      ( psi0  <=  psi )  ->
      binds  x   psi0   P  ->
     PStep P psi (a_Var_f x) (a_Var_f x)
 | PStep_Type : forall (P:econtext) (psi:grade) (s:Qual.sort_sig.sort),
     PStep P psi (a_Type s) (a_Type s)
 | PStep_Pi : forall (L:vars) (P:econtext) (psi psi1:grade) (A1 B1 A2 B2:tm),
     PStep P psi A1 A2 ->
      ( forall x , x \notin  L  -> PStep  (  ( x ~ psi1 )  ++ P )  psi  ( open_tm_wrt_tm B1 (a_Var_f x) )   ( open_tm_wrt_tm B2 (a_Var_f x) )  )  ->
     PStep P psi (a_Pi psi1 A1 B1) (a_Pi psi1 A2 B2)
 | PStep_AppBeta : forall (P:econtext) (psi:grade) (a:tm) (psi0:grade) (b a' b' A:tm),
     PStep P psi a  ( (a_Abs psi0 A a') )  ->
     CStep P psi psi0 b b' ->
     PStep P psi (a_App a psi0 b)  (open_tm_wrt_tm  a'   b' )
 | PStep_App : forall (P:econtext) (psi:grade) (a:tm) (psi0:grade) (b a' b':tm),
     PStep P psi a a' ->
     CStep P psi psi0 b b' ->
     PStep P psi (a_App a psi0 b) (a_App a' psi0 b')
 | PStep_Abs : forall (L:vars) (P:econtext) (psi psi0:grade) (A1 b1 A2 b2:tm),
     lc_tm A1 ->
     lc_tm A2 ->
      ( forall x , x \notin  L  -> PStep  (  ( x ~ psi0 )  ++ P )  psi  ( open_tm_wrt_tm b1 (a_Var_f x) )   ( open_tm_wrt_tm b2 (a_Var_f x) )  )  ->
     PStep P psi (a_Abs psi0 A1 b1) (a_Abs psi0 A2 b2)
 | PStep_Refl : forall (P:econtext) (psi:grade),
     PStep P psi a_Refl a_Refl
 | PStep_Transp : forall (P:econtext) (psi:grade) (a0 b0 a1 b1:tm),
     PStep P psi a0 a1 ->
     PStep P psi b0 b1 ->
     PStep P psi (a_Transp a0 b0) (a_Transp a1 b1)
 | PStep_CEq : forall (P:econtext) (psi psi0:grade) (a0 b0:tm) (psi1:grade) (A0 a1 b1 A1:tm),
     lc_tm A0 ->
     lc_tm A1 ->
     PStep P psi a0 a1 ->
     PStep P psi b0 b1 ->
      ( psi0  <=  psi )  ->
     PStep P psi (a_CEq psi0 a0 b0 psi1 A0) (a_CEq psi0 a1 b1 psi1 A1)
 | PStep_TranspRefl : forall (P:econtext) (psi:grade) (a0 b0 b1:tm),
     PStep P psi a0 a_Refl ->
     PStep P psi b0 b1 ->
     PStep P psi (a_Transp a0 b0) b1
 | PStep_T : forall (P:econtext) (psi psi0:grade) (A B:tm),
     PStep P psi A B ->
     PStep P psi (a_T psi0 A) (a_T psi0 B)
 | PStep_Box : forall (P:econtext) (psi psi0:grade) (a b:tm),
     CStep P psi psi0 a b ->
     PStep P psi (a_Box psi0 a) (a_Box psi0 b)
 | PStep_Unbox : forall (P:econtext) (psi psi0:grade) (a b:tm),
     PStep P psi a b ->
      ( psi0  <=  psi )  ->
     PStep P psi (a_Unbox psi0 a) (a_Unbox psi0 b)
 | PStep_UnboxBox : forall (P:econtext) (psi psi0:grade) (a b:tm),
     PStep P psi a (a_Box psi0 b) ->
      ( psi0  <=  psi )  ->
     PStep P psi (a_Unbox psi0 a) b
 | PStep_Proj1Cong : forall (P:econtext) (psi psi0:grade) (a0 a1:tm),
     PStep P psi a0 a1 ->
      ( psi0  <=  psi )  ->
     PStep P psi (a_Proj1 psi0 a0) (a_Proj1 psi0 a1)
 (* The second projection only observes the second component. *)
 | PStep_Proj2Cong : forall (P:econtext) (psi psi0:grade) (a0 a1:tm),
     PStep P psi a0 a1 ->
     PStep P psi (a_Proj2 psi0 a0) (a_Proj2 psi0 a1)
 | PStep_Proj1Beta : forall (P:econtext) (psi psi0:grade) (b a1 a2:tm),
     PStep P psi b (a_SPair a1 psi0 a2) ->
      ( psi0  <=  psi )  ->
     PStep P psi (a_Proj1 psi0 b) a1
 | PStep_Proj2Beta : forall (P:econtext) (psi psi0:grade) (b a2 a1:tm),
     PStep P psi b (a_SPair a1 psi0 a2) ->
     PStep P psi (a_Proj2 psi0 b) a2
 | PStep_SPair : forall (P:econtext) (psi:grade) (a0:tm) (psi0:grade) (b0 a1 b1:tm),
     CStep P psi psi0 a0 a1 ->
     PStep P psi b0 b1 ->
     PStep P psi (a_SPair a0 psi0 b0) (a_SPair a1 psi0 b1)
 | PStep_SSigma : forall (L:vars) (P:econtext) (psi psi0:grade) (A0 B0 A1 B1:tm),
     PStep P psi A0 A1 ->
      ( forall x , x \notin  L  -> PStep  (  ( x ~ psi0 )  ++ P )  psi  ( open_tm_wrt_tm B0 (a_Var_f x) )   ( open_tm_wrt_tm B1 (a_Var_f x) )  )  ->
     PStep P psi (a_SSigma psi0 A0 B0) (a_SSigma psi0 A1 B1)
 | PStep_TyUnit : forall (P:econtext) (psi:grade),
     PStep P psi a_TyUnit a_TyUnit
 | PStep_TmUnit : forall (P:econtext) (psi:grade),
     PStep P psi a_TmUnit a_TmUnit
 | PStep_Bool : forall (P:econtext) (psi:grade),
     PStep P psi a_Bool a_Bool
 | PStep_True : forall (P:econtext) (psi:grade),
     PStep P psi a_True a_True
 | PStep_False : forall (P:econtext) (psi:grade),
     PStep P psi a_False a_False
 | PStep_If : forall (P:econtext) (psi:grade) (a0 b0 b1 a1 b2 b3:tm),
     PStep P psi a0 a1 ->
     PStep P psi b0 b2 ->
     PStep P psi b1 b3 ->
     PStep P psi (a_If a0 b0 b1) (a_If a1 b2 b3)
 | PStep_IfTrue : forall (P:econtext) (psi:grade) (a0 b0 b1 b2 b3:tm),
     PStep P psi a0 a_True ->
     PStep P psi b0 b2 ->
     PStep P psi b1 b3 ->
     PStep P psi (a_If a0 b0 b1) b2
 | PStep_IfFalse : forall (P:econtext) (psi:grade) (a0 b0 b1 b3 b2:tm),
     PStep P psi a0 a_False ->
     PStep P psi b0 b2 ->
     PStep P psi b1 b3 ->
     PStep P psi (a_If a0 b0 b1) b3.


Scheme ps_ind := Induction for PStep Sort Prop
with cs_ind := Induction for CStep Sort Prop.
Combined Scheme pcs_ind from ps_ind, cs_ind.

Local Hint Constructors PStep CStep : ni.

Local Lemma meet_left (p q : grade) : p `&` q <= p.
Proof. exact: Order.LatticeTheoryMeet.leIl. Qed.
Local Lemma meet_right (p q : grade) : p `&` q <= q.
Proof. exact: Order.LatticeTheoryMeet.leIr. Qed.
Local Lemma meet_bound (p q g : grade) : g <= p -> g <= q -> g <= p `&` q.
Proof. intros; rewrite Order.LatticeTheoryMeet.lexI, H, H0; reflexivity. Qed.
Local Lemma meet_swap (p q : grade) : p `&` q = q `&` p.
Proof.
  apply Order.POrderTheory.le_anti. apply/andP; split;
    apply meet_bound; auto using meet_left, meet_right.
Qed.
Local Lemma below_trans (p q r : grade) : p <= q -> q <= r -> p <= r.
Proof. exact: Order.POrderTheory.le_trans. Qed.
Local Lemma grade_refl (p : grade) : p <= p.
Proof. exact: Order.POrderTheory.lexx. Qed.
Local Hint Resolve meet_left meet_right meet_bound grade_refl : ni.

Local Lemma pstep_lc :
  (forall P p a b, PStep P p a b -> lc_tm a /\ lc_tm b) /\
  (forall P p g a b, CStep P p g a b -> lc_tm a /\ lc_tm b).
Proof.
  apply pcs_ind; intros; repeat match goal with H : _ /\ _ |- _ => destruct H end;
    try solve [split; eauto 5 with ni];
    try solve [
      match goal with
      | H : lc_tm (a_Box _ _) |- _ => inversion H; eauto 5 with ni
      | H : lc_tm (a_SPair _ _ _) |- _ => inversion H; eauto 5 with ni
      end].
  - split; apply lc_a_Pi; auto; intros x;
      pick fresh z for L;
      apply (lc_from_open (x:=z)); edestruct H0; eauto.
  - split; [eauto with ni|].
    match goal with H : lc_tm (a_Abs _ _ ?a) |- lc_tm (open_tm_wrt_tm ?a _) =>
      inversion H; subst;
      pick fresh x for (fv_tm a); eapply lc_open_with; eauto
    end.
  - split; apply lc_a_Abs; auto; intros x;
      pick fresh z for L;
      apply (lc_from_open (x:=z)); edestruct H; eauto.
  - split; apply lc_a_SSigma; auto; intros x;
      pick fresh z for L;
      apply (lc_from_open (x:=z)); edestruct H0; eauto.
Qed.

Local Lemma ps_lc P p a b : PStep P p a b -> lc_tm a /\ lc_tm b.
Proof. apply pstep_lc. Qed.
Local Lemma cs_lc P p g a b : CStep P p g a b -> lc_tm a /\ lc_tm b.
Proof. apply pstep_lc. Qed.

Local Definition ctx_incl (P Q : econtext) :=
  forall x g, binds x g P -> binds x g Q.

Local Lemma ctx_incl_cons P Q x g :
  ctx_incl P Q -> ctx_incl ((x ~ g) ++ P) ((x ~ g) ++ Q).
Proof.
  intros H y j Hy. apply binds_app_iff in Hy.
  apply binds_app_iff. intuition.
Qed.

Local Lemma pstep_weaken :
  (forall P p a b, PStep P p a b -> forall Q, ctx_incl P Q -> PStep Q p a b) /\
  (forall P p g a b, CStep P p g a b -> forall Q, ctx_incl P Q -> CStep Q p g a b).
Proof.
  apply pcs_ind; unfold ctx_incl at 1; intros;
    eauto 5 using ctx_incl_cons with ni.
  eapply PStep_Abs with (L:=L); eauto.
  intros z Hz. apply (H z Hz). exact (@ctx_incl_cons P Q z psi0 H0).
Qed.

Local Lemma ps_weaken P p a b Q :
  PStep P p a b -> ctx_incl P Q -> PStep Q p a b.
Proof. intros H; eapply (proj1 pstep_weaken); eauto. Qed.

Local Lemma cs_visible P p g a b :
  CStep P p g a b -> g <= p -> PStep P p a b.
Proof. inversion 1; tauto. Qed.

Local Lemma cs_intro P p g a b :
  lc_tm a -> lc_tm b -> (g <= p -> PStep P p a b) -> CStep P p g a b.
Proof.
  intros Ha Hb H. destruct (g <= p) eqn:E.
  - apply CStep_Leq; auto.
  - apply CStep_Nleq; auto. unfold is_true. congruence.
Qed.

Local Definition remove_var (P Q : econtext) (x : tmvar) (g : grade) :=
  forall y j, binds y j P -> (y = x -> j = g) /\ (y <> x -> binds y j Q).

Local Lemma remove_var_cons P Q x g z k :
  remove_var P Q x g -> z <> x ->
  remove_var ((z ~ k) ++ P) ((z ~ k) ++ Q) x g.
Proof.
  intros H Hn y j Hy. apply binds_app_iff in Hy.
  destruct Hy as [Hy|Hy].
  - apply binds_one_iff in Hy. destruct Hy; subst.
    split; [congruence|auto with assoclist].
  - destruct (H _ _ Hy). split; eauto with assoclist.
Qed.

Local Lemma remove_var_head P x g :
  x \notin dom P -> remove_var ((x ~ g) ++ P) P x g.
Proof.
  intros H y j Hy. apply binds_app_iff in Hy.
  destruct Hy as [Hy|Hy].
  - apply binds_one_iff in Hy. destruct Hy; subst; intuition.
  - split; [intro; subst; exfalso; eauto using binds_In|auto].
Qed.

Local Lemma lc_ps_left P p a b : PStep P p a b -> lc_tm a.
Proof. intro H; exact (proj1 (ps_lc H)). Qed.
Local Lemma lc_ps_right P p a b : PStep P p a b -> lc_tm b.
Proof. intro H; exact (proj2 (ps_lc H)). Qed.
Local Lemma lc_cs_left P p g a b : CStep P p g a b -> lc_tm a.
Proof. intro H; exact (proj1 (cs_lc H)). Qed.
Local Lemma lc_cs_right P p g a b : CStep P p g a b -> lc_tm b.
Proof. intro H; exact (proj2 (cs_lc H)). Qed.
Local Hint Resolve lc_ps_left lc_ps_right lc_cs_left lc_cs_right : ni.

Local Lemma cs_weaken_cons P p k a b z j :
  CStep P p k a b -> CStep ((z ~ j) ++ P) p k a b.
Proof.
  intros H. eapply (proj2 pstep_weaken); [exact H|].
  intros ? ? ?; auto with assoclist.
Qed.

Local Lemma pstep_substitution :
  (forall P p a b, PStep P p a b -> forall Q x g s t,
    remove_var P Q x g -> CStep Q p g s t ->
    PStep Q p (subst_tm s x a) (subst_tm t x b)) /\
  (forall P p k a b, CStep P p k a b -> forall Q x g s t,
    remove_var P Q x g -> CStep Q p g s t ->
    CStep Q p k (subst_tm s x a) (subst_tm t x b)).
Proof.
  apply pcs_ind; intros; simpl;
    try solve [eauto 4 with ni].
  - decide_atoms; try congruence; subst;
      match goal with
      | H : remove_var _ _ _ _, Hb : binds _ _ _ |- _ =>
          destruct (H _ _ Hb) as [He Hr]
      end.
    + specialize (He eq_refl); subst; eauto using cs_visible.
    + econstructor; eauto.
  all: try solve [apply PStep_CEq; try (apply lc_subst; [assumption|eauto 2 with ni]); eauto 2].
  all: try solve [eapply PStep_If; eauto].
  all: try solve [eapply PStep_IfTrue; eauto].
  all: try solve [eapply PStep_IfFalse; eauto].
  all: try solve [apply CStep_Nleq; try (apply lc_subst; [assumption|eauto 2 with ni]); eauto 2].
  all: try match goal with
  | |- PStep _ _ (a_App _ _ _) (subst_tm _ _ (open_tm_wrt_tm _ _)) =>
      rewrite subst_open by (eauto 2 with ni);
      eapply PStep_AppBeta; [exact (H _ _ _ _ _ H1 H2)|eauto 2]
  end.
  all: first [eapply PStep_Pi with (L:=L \u {{x}})
             |eapply PStep_Abs with (L:=L \u {{x}})
             |eapply PStep_SSigma with (L:=L \u {{x}})];
       try solve [apply lc_subst; [assumption|eauto 2 with ni]]; try solve [eauto 2 with ni].
  all: intros z Hz;
    match goal with
    | |- PStep ?Q ?p (open_tm_wrt_tm (subst_tm ?s ?x ?A) _) (open_tm_wrt_tm (subst_tm ?t ?x ?B) _) =>
        assert (J : PStep Q p (subst_tm s x (open_tm_wrt_tm A (a_Var_f z)))
                              (subst_tm t x (open_tm_wrt_tm B (a_Var_f z))))
          by (first [eapply H0 | eapply H];
              [fsetdec|eapply remove_var_cons; [eassumption|fsetdec]
              |eapply cs_weaken_cons; eassumption]);
        rewrite (@subst_open A x s), (@subst_open B x t) in J by eauto 2 with ni;
        rewrite (@subst_fresh (a_Var_f z) x s), (@subst_fresh (a_Var_f z) x t) in J
          by (simpl; fsetdec);
        exact J
    end.
Qed.

Local Lemma ps_open P p g A B L s t :
  (forall x, x \notin L ->
     PStep ((x ~ g) ++ P) p (open_tm_wrt_tm A (a_Var_f x))
                             (open_tm_wrt_tm B (a_Var_f x))) ->
  CStep P p g s t ->
  PStep P p (open_tm_wrt_tm A s) (open_tm_wrt_tm B t).
Proof.
  intros H Hst. pick fresh x for (L \u dom P \u fv_tm A \u fv_tm B).
  rewrite (@open_as_subst A x s), (@open_as_subst B x t) by fsetdec.
  eapply (proj1 pstep_substitution); eauto using remove_var_head with set.
Qed.

Local Lemma ps_refl_both :
  (forall P p a b, PStep P p a b -> PStep P p a a /\ PStep P p b b) /\
  (forall P p g a b, CStep P p g a b -> CStep P p g a a /\ CStep P p g b b).
Proof.
  apply pcs_ind; intros; repeat match goal with H : _ /\ _ |- _ => destruct H end;
    try solve [split; eauto 3 with ni].
  all: try solve [
    split; first [eapply PStep_Pi with (L:=L) | eapply PStep_Abs with (L:=L)
                 | eapply PStep_SSigma with (L:=L)];
    try assumption;
    intros z Hz;
    match goal with J : forall x, x \notin ?Ls -> _ /\ _ |- _ =>
      first [exact (proj1 (J z Hz)) | exact (proj2 (J z Hz))]
    end].
  - split; [eauto with ni|].
    match goal with H : PStep _ _ (a_Abs _ _ _) (a_Abs _ _ _) |- _ =>
      inversion H; subst
    end.
    eapply ps_open; eauto.
  - split; [eauto with ni|].
    match goal with H : PStep _ _ (a_Box _ _) (a_Box _ _) |- _ =>
      inversion H; subst
    end.
    eauto using cs_visible.
  - split; [eauto with ni|].
    match goal with H : PStep _ _ (a_SPair _ _ _) (a_SPair _ _ _) |- _ =>
      inversion H; subst
    end.
    eauto using cs_visible.
  - split; [eauto with ni|].
    match goal with H : PStep _ _ (a_SPair _ _ _) (a_SPair _ _ _) |- _ =>
      inversion H; subst; assumption
    end.
Qed.

Local Lemma ps_refl_left P p a b : PStep P p a b -> PStep P p a a.
Proof. intro H; exact (proj1 (proj1 ps_refl_both _ _ _ _ H)). Qed.
Local Lemma ps_refl_right P p a b : PStep P p a b -> PStep P p b b.
Proof. intro H; exact (proj2 (proj1 ps_refl_both _ _ _ _ H)). Qed.
Local Hint Resolve ps_refl_left ps_refl_right : ni_refl.

Local Ltac invert_ps H := inversion H; subst; clear H.

Local Lemma ps_lower :
  (forall P p a b, PStep P p a b -> forall q c,
    uniq P -> PStep P q a c -> PStep P (p `&` q) a b) /\
  (forall P p g a b, CStep P p g a b -> forall q c,
    uniq P -> CStep P q g a c -> CStep P (p `&` q) g a b).
Proof.
  apply pcs_ind; intros.
  all: try solve [eauto 2 with ni].
  all: try match goal with
  | H : PStep ?P ?q ?a _ |- PStep ?P (_ `&` ?q) ?a _ => invert_ps H
  end.
  all: try solve [eauto 4 using meet_bound with ni].
  - match goal with
    | H : binds ?x ?g1 ?P, K : binds ?x ?g2 ?P, U : uniq ?P |- _ =>
        let E := fresh in assert (E : g1 = g2) by (eapply binds_unique; eauto);
        subst; eauto with ni
    end.
  all: try solve [
    match goal with
    | I : forall x, x \notin ?L -> forall q c, uniq _ -> PStep _ q _ c -> _,
      K : forall x, x \notin ?M -> PStep _ ?q _ _,
      U : uniq ?P |- PStep ?P (_ `&` ?q) _ _ =>
        let F := constr:(L \u M \u dom P) in
        first [eapply PStep_Pi with (L:=F) | eapply PStep_Abs with (L:=F)
              | eapply PStep_SSigma with (L:=F)];
        try solve [eauto 3];
        intros z Hz; eapply I; [fsetdec|constructor; [assumption|fsetdec]|apply K; fsetdec]
    end].
  all: try solve [apply PStep_CEq; eauto using meet_bound].
  all: try solve [apply PStep_If; eauto].
  all: try solve [eapply PStep_IfTrue; eauto].
  all: try solve [eapply PStep_IfFalse; eauto].
  all: try solve [apply CStep_Nleq; try assumption;
                  intro Hg; eauto using below_trans, meet_left].
  apply cs_intro; [exact (lc_ps_left p)|exact (lc_ps_right p)|].
  intro Hg. eapply H; [exact H0|].
  eapply cs_visible; [exact H1|exact (below_trans Hg (meet_right psi q))].
Qed.

Local Lemma ps_close P p g a b x z :
  x \notin dom P -> PStep ((x ~ g) ++ P) p a b ->
  PStep ((z ~ g) ++ P) p
    (open_tm_wrt_tm (close_tm_wrt_tm x a) (a_Var_f z))
    (open_tm_wrt_tm (close_tm_wrt_tm x b) (a_Var_f z)).
Proof.
  intros Hx H.
  rewrite (@close_open_subst a x (a_Var_f z) (lc_ps_left H)).
  rewrite (@close_open_subst b x (a_Var_f z) (lc_ps_right H)).
  eapply (proj1 pstep_substitution); [exact H| |].
  - intros y j Hy. destruct (remove_var_head Hx Hy).
    split; auto with assoclist.
  - apply cs_intro; [constructor|constructor|]. intro HG.
    eapply PStep_Var; [exact HG|].
    apply binds_app_iff; left; apply binds_one_iff; auto.
Qed.

Local Ltac subjoins :=
  repeat match goal with
  | IH : forall c, PStep ?P ?p ?a c -> exists d, _,
    K : PStep ?P ?p ?a ?c |- _ =>
      let z := fresh "joined" in let H1 := fresh in let H2 := fresh in
      destruct (IH c K) as [z [H1 H2]]; clear IH
  | IH : forall c, CStep ?P ?p ?g ?a c -> exists d, _,
    K : CStep ?P ?p ?g ?a ?c |- _ =>
      let z := fresh "joined" in let H1 := fresh in let H2 := fresh in
      destruct (IH c K) as [z [H1 H2]]; clear IH
  end.

Local Lemma join_bodies P p g R B C L M :
  (forall x, x \notin L -> forall c,
    PStep ((x ~ g) ++ P) p (open_tm_wrt_tm R (a_Var_f x)) c ->
    exists d, PStep ((x ~ g) ++ P) p (open_tm_wrt_tm B (a_Var_f x)) d /\
              PStep ((x ~ g) ++ P) p c d) ->
  (forall x, x \notin M ->
    PStep ((x ~ g) ++ P) p (open_tm_wrt_tm R (a_Var_f x))
                           (open_tm_wrt_tm C (a_Var_f x))) ->
  exists D, forall z,
    PStep ((z ~ g) ++ P) p (open_tm_wrt_tm B (a_Var_f z))
                           (open_tm_wrt_tm D (a_Var_f z)) /\
    PStep ((z ~ g) ++ P) p (open_tm_wrt_tm C (a_Var_f z))
                           (open_tm_wrt_tm D (a_Var_f z)).
Proof.
  intros HL HM. pick fresh x for (L \u M \u dom P \u fv_tm B \u fv_tm C).
  assert (Hx : x \notin dom P) by fsetdec.
  destruct (HL x ltac:(fsetdec) _ (HM x ltac:(fsetdec))) as [d [H1 H2]].
  exists (close_tm_wrt_tm x d). intro z.
  pose proof (ps_close z Hx H1) as J1.
  pose proof (ps_close z Hx H2) as J2.
  rewrite (@close_open_var B x) in J1 by fsetdec.
  rewrite (@close_open_var C x) in J2 by fsetdec.
  auto.
Qed.

Local Lemma pstep_diamond :
  (forall P p a b, PStep P p a b -> forall c, PStep P p a c ->
    exists d, PStep P p b d /\ PStep P p c d) /\
  (forall P p g a b, CStep P p g a b -> forall c, CStep P p g a c ->
    exists d, CStep P p g b d /\ CStep P p g c d).
Proof.
  apply pcs_ind; intros;
    match goal with
    | K : PStep ?P ?p _ ?c |- exists d, PStep ?P ?p _ d /\ PStep ?P ?p ?c d => invert_ps K
    | K : CStep ?P ?p ?g _ ?c |- exists d, CStep ?P ?p ?g _ d /\ CStep ?P ?p ?g ?c d => invert_ps K
    end;
    try contradiction;
    subjoins;
    try solve [eexists; split; eauto 3 with ni].
  all: try solve [
    match goal with
    | IH : forall x, x \notin ?LL -> forall c, PStep _ _ _ c -> exists d, _,
      K : forall x, x \notin ?MM -> PStep _ _ _ _ |- _ =>
        let D := fresh in let HD := fresh in
        destruct (join_bodies IH K) as [D HD];
        eexists; split;
        first [eapply PStep_Pi with (L:=empty) | eapply PStep_Abs with (L:=empty)
              |eapply PStep_SSigma with (L:=empty)];
        try eassumption;
        intros z _; first [exact (proj1 (HD z))|exact (proj2 (HD z))]
    end].
  all: repeat match goal with
    | K : PStep _ _ (a_Abs _ _ _) _ |- _ => invert_ps K
    | K : PStep _ _ (a_Box _ _) _ |- _ => invert_ps K
    | K : PStep _ _ (a_SPair _ _ _) _ |- _ => invert_ps K
    | K : PStep _ _ a_Refl _ |- _ => invert_ps K
    | K : PStep _ _ a_True _ |- _ => invert_ps K
    | K : PStep _ _ a_False _ |- _ => invert_ps K
    end.
  all: try solve [eexists; split;
    first [eassumption
    |solve [eapply ps_open; eassumption]
    |solve [eapply PStep_AppBeta; eassumption]
    |solve [eapply PStep_TranspRefl; eassumption]
    |solve [eapply PStep_UnboxBox; eassumption]
    |solve [eapply PStep_Proj1Beta; eassumption]
    |solve [eapply PStep_Proj2Beta; eassumption]
    |solve [eapply PStep_IfTrue; eassumption]
    |solve [eapply PStep_IfFalse; eassumption]
    |solve [eapply cs_visible; eassumption]]].

Qed.

(* Conversion is the equivalence closure of parallel reduction. *)
Inductive path (R : tm -> tm -> Prop) : tm -> tm -> Prop :=
| path_nil : forall a, path R a a
| path_cons : forall a b c, R a b -> path R b c -> path R a c.

Local Hint Constructors path : ni_path.

Local Lemma path_cat R a b c : path R a b -> path R b c -> path R a c.
Proof. induction 1; eauto with ni_path. Qed.

Local Lemma path_map R S (f : tm -> tm) :
  (forall a b, R a b -> S (f a) (f b)) ->
  forall a b, path R a b -> path S (f a) (f b).
Proof. intros H a b K; induction K; eauto with ni_path. Qed.

Local Definition either (R : tm -> tm -> Prop) a b := R a b \/ R b a.
Local Definition reachable_eq R := path (either R).

Local Lemma eq_edge R a b : R a b -> reachable_eq R a b.
Proof. intros H; eapply path_cons; [left; exact H|constructor]. Qed.

Local Lemma reachable_sym R a b : reachable_eq R a b -> reachable_eq R b a.
Proof.
  induction 1; [constructor|].
  eapply path_cat; [eassumption|].
  eapply path_cons with (b:=a); [unfold either in *; tauto|constructor].
Qed.

Local Lemma eq_map R S (f : tm -> tm) :
  (forall a b, R a b -> S (f a) (f b)) ->
  forall a b, reachable_eq R a b -> reachable_eq S (f a) (f b).
Proof. intro H; apply path_map; unfold either; intuition. Qed.

Local Definition stable_eq R a b := R a a /\ R b b /\ reachable_eq R a b.

Local Lemma stable_refl R a : R a a -> stable_eq R a a.
Proof. intros; repeat split; auto; constructor. Qed.
Local Lemma stable_sym R a b : stable_eq R a b -> stable_eq R b a.
Proof. unfold stable_eq; intuition eauto using reachable_sym. Qed.
Local Lemma stable_trans R a b c :
  stable_eq R a b -> stable_eq R b c -> stable_eq R a c.
Proof.
  intros (Ha & _ & Hab) (_ & Hc & Hbc).
  repeat split; try assumption. eapply path_cat; eassumption.
Qed.

Local Lemma stable_map R S (f : tm -> tm) a b :
  (forall a b, R a b -> S (f a) (f b)) ->
  stable_eq R a b -> stable_eq S (f a) (f b).
Proof.
  intros H (Ha & Hb & Hab). repeat split; auto.
  exact (eq_map H Hab).
Qed.

Local Lemma stable_map2 R S T (f : tm -> tm -> tm) a b c d :
  (forall a b c d, R a b -> S c d -> T (f a c) (f b d)) ->
  stable_eq R a b -> stable_eq S c d -> stable_eq T (f a c) (f b d).
Proof.
  intros H (Haa & Hbb & Hab) (Hcc & Hdd & Hcd).
  eapply stable_trans with (b:=f b c).
  - eapply (stable_map (f:=fun z => f z c)); [eauto|repeat split; assumption].
  - eapply (stable_map (f:=fun z => f b z)); [eauto|repeat split; assumption].
Qed.

Local Lemma stable_map3 R S T U (f : tm -> tm -> tm -> tm) a b c d e g :
  (forall a b c d e g, R a b -> S c d -> T e g -> U (f a c e) (f b d g)) ->
  stable_eq R a b -> stable_eq S c d -> stable_eq T e g ->
  stable_eq U (f a c e) (f b d g).
Proof.
  intros H Hab Hcd (He & Hg & Heg).
  eapply stable_trans with (b:=f b d e).
  - eapply (stable_map2 (f:=fun z w => f z w e)); eauto.
  - eapply (@stable_map T U (fun z => f b d z) e g).
    + intros x y Hxy. apply H; [exact (proj1 (proj2 Hab))|exact (proj1 (proj2 Hcd))|exact Hxy].
    + split; [exact He|]. split; assumption.
Qed.

Local Definition grade_step (allow : grade -> Prop) (P : econtext) a b :=
  exists p, allow p /\ PStep P p a b.
Local Definition conv (allow : grade -> Prop) (P : econtext) :=
  reachable_eq (grade_step allow P).
Local Definition conv_any := conv (fun _ => True).

Local Lemma join_path (R : tm -> tm -> Prop) :
  (forall a b c, R a b -> R a c -> exists d, R b d /\ R c d) ->
  forall a b c, path R a b -> path R a c -> exists d, path R b d /\ path R c d.
Proof.
  intros Diamond.
  assert (Strip : forall a b, path R a b -> forall c, R a c ->
    exists d, R b d /\ path R c d).
  { intros a b H; induction H; intros t Ht.
    - exists t; split; auto; constructor.
    - destruct (Diamond _ _ _ H Ht) as [u [Hbu Htu]].
      destruct (IHpath _ Hbu) as [v [Hcv Huv]].
      exists v; split; eauto with ni_path. }
  intros a b c Hab Hac. revert b Hab.
  induction Hac; intros t Ht.
  - exists t; split; auto; constructor.
  - destruct (Strip _ _ Ht _ H) as [u [Htu Hbu]].
    destruct (IHHac u Hbu) as [v [Huv Hcv]].
    exists v; split; eauto with ni_path.
Qed.

Local Lemma conv_common allow P :
  uniq P ->
  (forall p q, allow p -> allow q -> allow (p `&` q)) ->
  forall a b, conv allow P a b ->
    exists c, path (grade_step allow P) a c /\ path (grade_step allow P) b c.
Proof.
  intros HU HM a b H.
  assert (Diamond : forall a b c,
    grade_step allow P a b -> grade_step allow P a c ->
    exists d, grade_step allow P b d /\ grade_step allow P c d).
  { intros x y z [p [Hp Hxy]] [q [Hq Hxz]].
    assert (L : PStep P (p `&` q) x y)
      by (eapply (proj1 ps_lower); eauto).
    assert (R : PStep P (p `&` q) x z).
    { rewrite meet_swap.
      eapply (proj1 ps_lower); eauto. }
    destruct ((proj1 pstep_diamond) _ _ _ _ L _ R) as [t [Hyt Hzt]].
    exists t; split; exists (p `&` q); eauto. }
  induction H.
  - exists a; split; constructor.
  - destruct IHpath as [d [Hbd Hcd]].
    destruct H as [Hab|Hba].
    + exists d; split; eauto with ni_path.
    + assert (Hba' : path (grade_step allow P) b a) by eauto with ni_path.
      destruct (join_path Diamond Hbd Hba') as [e [Hde Hae]].
      exists e; split; eauto using path_cat.
Qed.

Local Definition grade_eq P p := stable_eq (PStep P p).
Local Definition conditional_eq P p g := stable_eq (CStep P p g).

Local Lemma grade_eq_step P p a b : PStep P p a b -> grade_eq P p a b.
Proof.
  intro H. split; [eauto using ps_refl_left|]. split; eauto using ps_refl_right, eq_edge.
Qed.

Local Lemma conditional_eq_step P p g a b : CStep P p g a b -> conditional_eq P p g a b.
Proof.
  intro H. destruct (proj2 ps_refl_both _ _ _ _ _ H).
  repeat split; eauto using eq_edge.
Qed.

Local Lemma grade_eq_c P p g a b :
  g <= p -> grade_eq P p a b -> conditional_eq P p g a b.
Proof.
  intros Hp H. eapply (@stable_map (PStep P p) (CStep P p g) (fun t=>t)); [|exact H].
  intros; apply CStep_Leq; assumption.
Qed.

Local Lemma grade_eq_app P p g a b c d :
  grade_eq P p a b -> conditional_eq P p g c d ->
  grade_eq P p (a_App a g c) (a_App b g d).
Proof.
  eapply (stable_map2 (f:=fun x y => a_App x g y)); eauto using PStep_App.
Qed.

Local Lemma grade_eq_if P p a a' b b' c c' :
  grade_eq P p a a' -> grade_eq P p b b' -> grade_eq P p c c' ->
  grade_eq P p (a_If a b c) (a_If a' b' c').
Proof. eapply (stable_map3 (f:=a_If)); eauto using PStep_If. Qed.

Local Lemma grade_eq_binder P p g L b b' :
  (forall x, x \notin L -> grade_eq ((x ~ g) ++ P) p
     (open_tm_wrt_tm b (a_Var_f x)) (open_tm_wrt_tm b' (a_Var_f x))) ->
  exists x, x \notin dom P /\ x \notin fv_tm b /\ x \notin fv_tm b' /\
    grade_eq ((x ~ g) ++ P) p (open_tm_wrt_tm b (a_Var_f x))
                                (open_tm_wrt_tm b' (a_Var_f x)).
Proof.
  intros H. pick fresh x for (L \u dom P \u fv_tm b \u fv_tm b').
  exists x; repeat split; try fsetdec; apply H; fsetdec.
Qed.

Scheme ge_ind := Induction for GDefEq Sort Prop
with cge_ind := Induction for CGDefEq Sort Prop.
Combined Scheme gcge_ind from ge_ind, cge_ind.

Local Lemma grade_eq_sound :
  (forall P p a b, GDefEq P p a b -> grade_eq P p a b) /\
  (forall P p g a b, CGDefEq P p g a b -> conditional_eq P p g a b).
Proof.
  apply gcge_ind; intros.
  all: try solve [apply stable_refl; eauto 2 with ni].
  all: try solve [eauto 2 using grade_eq_app, grade_eq_if, grade_eq_c, conditional_eq_step with ni].
  all: try solve [apply stable_sym; assumption].
  all: try solve [eapply stable_trans; eassumption].
  - destruct (grade_eq_binder H) as [x [Hx [Hb0 [Hb1 J]]]].
    eapply stable_trans with (b:=a_Abs psi0 A0 b1).
    + rewrite <- (@close_open_var b0 x Hb0), <- (@close_open_var b1 x Hb1).
      eapply (@stable_map (PStep ((x ~ psi0) ++ P) psi) (PStep P psi)
        (fun b => a_Abs psi0 A0 (close_tm_wrt_tm x b))); [|exact J].
      intros u v Huv. eapply PStep_Abs with (L:=empty); [exact l|exact l|].
      intros z _. exact (ps_close z Hx Huv).
    + apply grade_eq_step. eapply PStep_Abs with (L:=L); auto.
      intros y Hy; exact (proj1 (proj2 (H y Hy))).
  - destruct (grade_eq_binder H0) as [x [Hx [Hb0 [Hb1 J]]]].
    rewrite <- (@close_open_var B0 x Hb0), <- (@close_open_var B1 x Hb1).
    eapply (stable_map2 (f:=fun A B => a_Pi psi0 A (close_tm_wrt_tm x B)));
      [|exact H|exact J].
    intros; eapply PStep_Pi with (L:={{x}}); eauto using ps_close.
  - eapply stable_trans; [apply grade_eq_app; eassumption|].
    apply grade_eq_step. eapply PStep_AppBeta.
    + exact (proj1 (proj2 H)).
    + exact (proj1 (proj2 H0)).
  - eapply (stable_map2 (f:=a_Transp)); eauto using PStep_Transp.
  - eapply stable_trans with (b:=a_CEq psi0 a1 b1 psi1 A0).
    + eapply (stable_map2 (f:=fun a b => a_CEq psi0 a b psi1 A0));
        eauto using PStep_CEq.
    + apply grade_eq_step, PStep_CEq; auto.
      * exact (proj1 (proj2 H)).
      * exact (proj1 (proj2 H0)).
  - eapply stable_trans with (b:=a_Transp a_Refl b1).
    + eapply (stable_map2 (f:=a_Transp)); eauto using PStep_Transp.
    + apply grade_eq_step, PStep_TranspRefl; [constructor|exact (proj1 (proj2 H0))].
  - eapply (stable_map (f:=a_T psi0)); eauto using PStep_T.
  - eapply (stable_map (f:=a_Box psi0)); eauto using PStep_Box.
  - eapply (stable_map (f:=a_Unbox psi0)); eauto using PStep_Unbox.
  - eapply stable_trans with (b:=a_Unbox psi0 (a_Box psi0 b)).
    + eapply (stable_map (f:=a_Unbox psi0)); eauto using PStep_Unbox.
    + apply grade_eq_step, PStep_UnboxBox; auto. exact (proj1 (proj2 H)).
  - eapply (stable_map (f:=a_Proj1 psi0)); [intros; apply PStep_Proj1Cong; eassumption|exact H].
  - eapply (stable_map (f:=a_Proj2 psi0)); [intros; apply PStep_Proj2Cong; eassumption|exact H].
  - eapply stable_trans with (b:=a_Proj1 psi0 (a_SPair a1 psi0 a2)).
    + eapply (stable_map (f:=a_Proj1 psi0)); [intros; apply PStep_Proj1Cong; eassumption|exact H].
    + apply grade_eq_step, PStep_Proj1Beta with (a2:=a2); auto.
      exact (proj1 (proj2 H)).
  - eapply stable_trans with (b:=a_Proj2 psi0 (a_SPair a1 psi0 a2)).
    + eapply (stable_map (f:=a_Proj2 psi0)); [intros; apply PStep_Proj2Cong; eassumption|exact H].
    + apply grade_eq_step, PStep_Proj2Beta with (a1:=a1).
      exact (proj1 (proj2 H)).
  - eapply (stable_map2 (f:=fun a b => a_SPair a psi0 b)); eauto using PStep_SPair.
  - destruct (grade_eq_binder H0) as [x [Hx [Hb0 [Hb1 J]]]].
    rewrite <- (@close_open_var B0 x Hb0), <- (@close_open_var B1 x Hb1).
    eapply (stable_map2 (f:=fun A B => a_SSigma psi0 A (close_tm_wrt_tm x B)));
      [|exact H|exact J].
    intros; eapply PStep_SSigma with (L:={{x}}); eauto using ps_close.
  - eapply stable_trans with (b:=a_If a_True b2 b3); [apply grade_eq_if; assumption|].
    apply grade_eq_step, PStep_IfTrue with (b3:=b3).
    + constructor.
    + exact (proj1 (proj2 H0)).
    + exact (proj1 (proj2 H1)).
  - eapply stable_trans with (b:=a_If a_False b2 b3); [apply grade_eq_if; assumption|].
    apply grade_eq_step, PStep_IfFalse with (b2:=b2).
    + constructor.
    + exact (proj1 (proj2 H0)).
    + exact (proj1 (proj2 H1)).
  - apply conditional_eq_step, CStep_Nleq; assumption.
Qed.

(* A typed term can be observed at its own grade or any greater grade. *)
Inductive scoped : econtext -> grade -> tm -> Prop :=
| S_Var P p x g : g <= p -> binds x g P -> scoped P p (a_Var_f x)
| S_Type P p s : scoped P p (a_Type s)
| S_Pi L P p g A B : scoped P p A ->
    (forall x, x \notin L -> scoped ((x ~ g) ++ P) p (open_tm_wrt_tm B (a_Var_f x))) ->
    scoped P p (a_Pi g A B)
| S_Abs L P p g A b : lc_tm A ->
    (forall x, x \notin L -> scoped ((x ~ g) ++ P) p (open_tm_wrt_tm b (a_Var_f x))) ->
    scoped P p (a_Abs g A b)
| S_App P p g a b : scoped P p a -> scoped P g b -> scoped P p (a_App a g b)
| S_CEq P p h g a b A : h <= p -> g <= h ->
    scoped P g a -> scoped P g b -> lc_tm A -> scoped P p (a_CEq h a b g A)
| S_Refl P p : scoped P p a_Refl
| S_Transp P p a b : scoped P p a -> scoped P p b -> scoped P p (a_Transp a b)
| S_T P p g A : scoped P p A -> scoped P p (a_T g A)
| S_Box P p g a : scoped P g a -> scoped P p (a_Box g a)
| S_Unbox P p g a : g <= p -> scoped P p a -> scoped P p (a_Unbox g a)
| S_SSigma L P p g A B : scoped P p A ->
    (forall x, x \notin L -> scoped ((x ~ g) ++ P) p (open_tm_wrt_tm B (a_Var_f x))) ->
    scoped P p (a_SSigma g A B)
| S_SPair P p g a b : scoped P g a -> scoped P p b -> scoped P p (a_SPair a g b)
| S_Proj1 P p g a : g <= p -> scoped P p a -> scoped P p (a_Proj1 g a)
| S_Proj2 P p g a : scoped P p a -> scoped P p (a_Proj2 g a)
| S_TyUnit P p : scoped P p a_TyUnit
| S_TmUnit P p : scoped P p a_TmUnit
| S_Bool P p : scoped P p a_Bool
| S_True P p : scoped P p a_True
| S_False P p : scoped P p a_False
| S_If P p a b c : scoped P p a -> scoped P p b -> scoped P p c -> scoped P p (a_If a b c).

Local Hint Constructors scoped : ni_scope.

Local Lemma scoped_refl P p a :
  scoped P p a -> forall q, p <= q -> PStep P q a a.
Proof.
  induction 1; intros q Hq;
    try solve [eauto 3 using below_trans with ni].
  all: try solve [eapply PStep_Pi with (L:=L); eauto].
  all: try solve [eapply PStep_Abs with (L:=L); eauto].
  all: try solve [eapply PStep_SSigma with (L:=L); eauto].
  all: try solve [apply PStep_CEq; eauto 5 using below_trans].
  all: try solve [apply PStep_Transp; eauto].
  all: try solve [apply PStep_If; eauto].
  all: try solve [apply PStep_Unbox; eauto using below_trans].
  all: try solve [apply PStep_Proj1Cong; eauto using below_trans].
  all: first [apply PStep_App | apply PStep_Box | apply PStep_SPair]; try solve [eauto 2].
  all: apply cs_intro.
  all: try solve [eapply lc_ps_left; first
       [solve [apply IHscoped2; apply grade_refl]
       |solve [apply IHscoped1; apply grade_refl]
       |solve [apply IHscoped; apply grade_refl]]].
  all: intro Hq'; first [solve [apply IHscoped2; exact Hq']
                        |solve [apply IHscoped1; exact Hq']
                        |solve [apply IHscoped; exact Hq']].
Qed.

Local Lemma scoped_lc P p a : scoped P p a -> lc_tm a.
Proof. intros; eapply lc_ps_left, scoped_refl; eauto using grade_refl. Qed.

Local Lemma scoped_mono P p a :
  scoped P p a -> forall q, p <= q -> scoped P q a.
Proof.
  induction 1; intros q Hq; try solve [eauto 3 using below_trans with ni_scope].
  all: try solve [eapply S_Pi with (L:=L); eauto].
  all: try solve [eapply S_Abs with (L:=L); eauto].
  all: try solve [eapply S_SSigma with (L:=L); eauto].
  all: first [apply S_Transp | apply S_Unbox | apply S_Proj1 | apply S_If];
       eauto using below_trans.
Qed.

Local Lemma scoped_weaken P p a :
  scoped P p a -> forall Q, ctx_incl P Q -> scoped Q p a.
Proof.
  induction 1; intros Q HQ; try solve [eauto 4 using ctx_incl_cons with ni_scope].
  all: try solve [eapply S_Var; [eassumption|apply HQ; assumption]].
  all: try solve [eapply S_Abs with (L:=L); eauto using ctx_incl_cons].
  all: try solve [apply S_If; eauto].
  all: first [eapply S_Pi with (L:=L) | eapply S_SSigma with (L:=L)]; eauto.
  all: intros z Hz; apply (H1 z Hz); auto using ctx_incl_cons.
Qed.

Local Lemma scoped_weaken_cons P p a x g :
  scoped P p a -> scoped ((x ~ g) ++ P) p a.
Proof.
  intro H; eapply scoped_weaken; [exact H|].
  intros ? ? ?; auto using binds_cons.
Qed.

Local Lemma scoped_subst P p a :
  scoped P p a -> forall Q x g u,
  remove_var P Q x g -> scoped Q g u -> scoped Q p (subst_tm u x a).
Proof.
  induction 1; intros Q x0 j u Hr Hu; simpl;
    try solve [eauto 3 with ni_scope];
    try solve [eapply S_CEq; eauto 2 using lc_subst, scoped_lc].
  - decide_atoms; subst; destruct (Hr _ _ H0) as [E K].
    + specialize (E eq_refl); subst; eauto using scoped_mono.
    + eapply S_Var; eauto.
  all: try solve [
    first [apply S_App | apply S_CEq | apply S_Transp | apply S_SPair | apply S_If];
    try solve [eauto 3];
    apply lc_subst; eauto using scoped_lc].
  all: match goal with
  | |- scoped _ _ (a_Pi _ _ _) => eapply S_Pi with (L:=L \u {{x0}})
  | |- scoped _ _ (a_Abs _ _ _) => eapply S_Abs with (L:=L \u {{x0}})
  | |- scoped _ _ (a_SSigma _ _ _) => eapply S_SSigma with (L:=L \u {{x0}})
  end; try solve [eauto 3 using lc_subst, scoped_lc].
  all: intros z Hz;
    match goal with
    | |- scoped ?Q ?p (open_tm_wrt_tm (subst_tm ?u ?x ?B) (a_Var_f ?z)) =>
      assert (J : scoped Q p (subst_tm u x (open_tm_wrt_tm B (a_Var_f z))))
        by (first [eapply H1 | eapply H0];
          [fsetdec|eapply remove_var_cons; [eassumption|fsetdec]
                  |apply scoped_weaken_cons; assumption]);
      rewrite (@subst_open B x u) in J by eauto using scoped_lc;
      rewrite (@subst_fresh (a_Var_f z) x u) in J by (simpl; fsetdec);
      exact J
    end.
Qed.

Local Lemma scoped_open P p g B L u :
  (forall x, x \notin L -> scoped ((x ~ g) ++ P) p (open_tm_wrt_tm B (a_Var_f x))) ->
  scoped P g u -> scoped P p (open_tm_wrt_tm B u).
Proof.
  intros H Hu. pick fresh x for (L \u dom P \u fv_tm B).
  rewrite (@open_as_subst B x u) by fsetdec.
  eapply scoped_subst with (P:=(x ~ g) ++ P);
    eauto using remove_var_head with set.
Qed.

Local Lemma labels_binds W x g A :
  binds x (g, A) W -> binds x g (labels W).
Proof.
  intro H. exact (@binds_map (grade * tm) grade fst x (g,A) W H).
Qed.

Local Lemma labels_dom W : dom (labels W) = dom W.
Proof. induction W as [|[x [g A]] W IH]; simpl; congruence. Qed.

Local Lemma labels_uniq W : uniq W -> uniq (labels W).
Proof.
  induction 1 as [|x [g A] W H IH Hx]; simpl; constructor; auto.
  rewrite labels_dom; assumption.
Qed.

Scheme ctx_ind := Induction for Ctx Sort Prop
with ty_ind := Induction for Typing Sort Prop.
Combined Scheme ctx_ty_ind from ctx_ind, ty_ind.

Local Definition scoped_ctx (W : context) :=
  forall x g A, binds x (g, A) W -> exists p, scoped (labels W) p A.

Local Lemma scope_pi P p g A B :
  scoped P p (a_Pi g A B) ->
  scoped P p A /\ exists L, forall x, x \notin L ->
     scoped ((x ~ g) ++ P) p (open_tm_wrt_tm B (a_Var_f x)).
Proof. inversion 1; subst; eauto. Qed.

Local Lemma scope_sig P p g A B :
  scoped P p (a_SSigma g A B) ->
  scoped P p A /\ exists L, forall x, x \notin L ->
     scoped ((x ~ g) ++ P) p (open_tm_wrt_tm B (a_Var_f x)).
Proof. inversion 1; subst; eauto. Qed.

Local Lemma scope_ceq P p h g a b A :
  scoped P p (a_CEq h a b g A) -> g <= h /\ scoped P g a /\ scoped P g b.
Proof. inversion 1; subst; eauto. Qed.

Local Lemma typing_scoped :
  (forall W, Ctx W -> uniq W /\ scoped_ctx W) /\
  (forall W p a A, Typing W p a A ->
    uniq W /\ scoped (labels W) p a /\ exists q, scoped (labels W) q A).
Proof.
  apply ctx_ty_ind; intros.
  - split; [constructor|]. intros ? ? ? H; inversion H.
  - destruct H as [HU HC]. destruct H0 as [_ [Ha HT]].
    split; [constructor; auto|].
    intros y g B Hy. apply binds_app_iff in Hy. destruct Hy as [Hy|Hy]; simpl.
    + apply binds_one_iff in Hy; destruct Hy as [-> E]; inversion E; subst.
      exists psi; eapply scoped_weaken_cons; exact Ha.
    + destruct (HC _ _ _ Hy) as [q Hq]; exists q; eapply scoped_weaken_cons; exact Hq.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: try solve [split; [assumption|]; split; eauto 3 using scoped_lc, labels_binds with ni_scope].
  all: try solve [split; [assumption|]; split;
    [ first [eapply S_Pi with (L:=L) | eapply S_SSigma with (L:=L)];
      [assumption|intros x Hx; exact (proj1 (proj2 (H0 x Hx)))]
    | exists psi; apply S_Type ]].
  - split; [assumption|]. split.
    + eapply S_Abs with (L:=L); [|intros x Hx; specialize (H x Hx); tauto].
      destruct (scope_pi H1) as [HS _]; exact (scoped_lc HS).
    + exists psi1. exact H1.
  - split; [assumption|]. split; [eauto with ni_scope|].
    match goal with H : exists q, scoped _ q (a_Pi _ _ _) |- _ =>
      destruct H as [q H]; destruct (scope_pi H) as [_ [L HL]];
      exists q; eauto using scoped_open
    end.
  - split; [assumption|]. split; [eauto with ni_scope|].
    match goal with H : exists q, scoped _ q (a_CEq _ _ _ _ _) |- _ =>
      destruct H as [q H]; destruct (scope_ceq H) as [_ [_ Ha]];
      exists psi0; eapply scoped_open; [|exact Ha]; intros x Hx;
      match goal with I : forall x, x \notin ?Ls -> _ |- _ =>
        first [exact (proj1 (proj2 (I x Hx)))|fail]
      end
    end.
  - split; [assumption|]. split; [eauto with ni_scope|].
    match goal with H : exists q, scoped _ q (a_T _ _) |- _ =>
      destruct H as [q H]; inversion H; subst; eauto
    end.
  - split; [assumption|]. split; [eauto with ni_scope|].
    match goal with H : exists q, scoped _ q (a_SSigma _ _ _) |- _ =>
      destruct H as [q H]; destruct (scope_sig H); eauto
    end.
  - split; [assumption|]. split; [eauto with ni_scope|].
    match goal with H : exists q, scoped _ q (a_SSigma _ _ _) |- _ =>
      destruct H as [q H]; destruct (scope_sig H) as [_ [L HL]];
      exists q; eauto using scoped_open
    end.
  Unshelve. all: exact psi.
Qed.

Local Lemma scope_typed W p a A : Typing W p a A -> scoped (labels W) p a.
Proof. intros H; exact (proj1 (proj2 (proj2 typing_scoped _ _ _ _ H))). Qed.

Local Lemma scoped_ps P p a : scoped P p a -> PStep P p a a.
Proof. intros H; eauto using scoped_refl, grade_refl. Qed.

Local Lemma scoped_cs P p g a : scoped P g a -> CStep P p g a a.
Proof. intros H; apply cs_intro; eauto using scoped_lc, scoped_refl. Qed.

Local Lemma red_scoped P p a b : Red a b -> scoped P p a ->
  scoped P p b /\ PStep P p a b.
Proof.
  intros H; induction H; intro Hs; inversion Hs; subst;
    repeat match goal with
    | H : scoped _ _ (a_Abs _ _ _) |- _ => invert_ps H
    | H : scoped _ _ (a_SPair _ _ _) |- _ => invert_ps H
    | H : scoped _ _ (a_Box _ _) |- _ => invert_ps H
    end;
    repeat match goal with
    | IH : scoped ?P ?p ?a -> _, H : scoped ?P ?p ?a |- _ =>
      destruct (IH H); clear IH
    end;
    split;
    try solve [eauto 3 using scoped_open, scoped_mono with ni_scope];
    try solve [eauto 4 using scoped_ps, scoped_cs, scoped_refl with ni].
  all: try solve [eapply PStep_AppBeta with (A:=A);
    [eapply PStep_Abs with (L:=L); eauto using scoped_ps|apply scoped_cs; assumption]].
  all: try solve [apply PStep_UnboxBox; [apply PStep_Box; apply scoped_cs; assumption|assumption]].
  all: try solve [eapply PStep_Proj1Beta;
    [apply PStep_SPair; eauto using scoped_ps, scoped_cs|assumption]].
  all: try solve [eapply PStep_Proj2Beta; apply PStep_SPair; eauto using scoped_ps, scoped_cs].
Qed.

(* Common reducts preserve the heads and components of type constructors. *)
Local Lemma conv_step allow P p a b : allow p -> PStep P p a b -> conv allow P a b.
Proof. intros Hp H; apply eq_edge; exists p; auto. Qed.

Local Lemma conv_general P p a b :
  grade_eq P p a b -> conv_any P a b.
Proof.
  intros (_ & _ & H).
  exact (eq_map (f:=fun z=>z) (fun a b H => ex_intro _ p (conj I H)) H).
Qed.

Local Lemma defe_conv P a b : DefEq P a b -> conv_any P a b.
Proof.
  induction 1.
  - apply (conv_general (p:=psi)), (proj1 grade_eq_sound); assumption.
  - eapply path_cat; eassumption.
Qed.

Local Lemma conv_any_common P a b :
  uniq P -> conv_any P a b ->
  exists c, path (grade_step (fun _ => True) P) a c /\
            path (grade_step (fun _ => True) P) b c.
Proof. intros; eapply conv_common; eauto. Qed.

Local Lemma path_conv allow P a b :
  path (grade_step allow P) a b -> conv allow P a b.
Proof.
  intro H; exact (path_map (f:=fun z=>z) (fun _ _ H => or_introl H) H).
Qed.

Local Lemma ps_head P p a b h :
  PStep P p a b -> tm_to_headform a = Some h -> tm_to_headform b = Some h.
Proof. destruct 1; simpl; intro E; try discriminate; exact E. Qed.

Local Lemma path_head allow P a b h :
  path (grade_step allow P) a b ->
  tm_to_headform a = Some h -> tm_to_headform b = Some h.
Proof.
  induction 1; auto. destruct H as [p [_ H]].
  eauto using ps_head.
Qed.

Local Lemma conv_heads P a b h k :
  uniq P -> conv_any P a b ->
  tm_to_headform a = Some h -> tm_to_headform b = Some k -> h = k.
Proof.
  intros HU HC Ha Hb.
  destruct (conv_any_common HU HC) as [c [Hac Hbc]].
  pose proof (path_head Hac Ha). pose proof (path_head Hbc Hb). congruence.
Qed.

Local Definition entails (P : econtext) a b :=
  path (grade_step (fun _ => True) P) a b.

Local Definition bind_type (is_pi : bool) := if is_pi then a_Pi else a_SSigma.

Local Lemma binder_path P a b : entails P a b ->
  forall flag g A B, a = bind_type flag g A B ->
  exists A' B' L, b = bind_type flag g A' B' /\ entails P A A' /\
    (forall x, x \notin L -> entails ((x ~ g) ++ P)
      (open_tm_wrt_tm B (a_Var_f x)) (open_tm_wrt_tm B' (a_Var_f x))).
Proof.
  induction 1; intros f g A B E; subst.
  - exists A, B, empty. repeat split; constructor.
  - destruct H as [p [_ H]].
    destruct f; simpl in H; inversion H; subst.
    all: match goal with |- exists _ _ _, _ = bind_type ?f _ _ _ /\ _ =>
      destruct (IHpath f g _ _ eq_refl) as [U [V [M [E [D F]]]]]
    end.
    all: exists U,V,(L \u M); split; [exact E|]; split.
    all: try solve [eapply path_cons; [exists p; split; [exact I|eassumption]|exact D]].
    all: intros x Hx; eapply path_cons; [exists p; split; [exact I|apply H8; fsetdec]|apply F; fsetdec].
Qed.

Local Lemma conv_binder P f g j A B A' B' :
  uniq P -> conv_any P (bind_type f g A B) (bind_type f j A' B') ->
  g = j /\ conv_any P A A' /\ exists L, forall x, x \notin L ->
    conv_any ((x ~ g) ++ P) (open_tm_wrt_tm B (a_Var_f x))
                           (open_tm_wrt_tm B' (a_Var_f x)).
Proof.
  intros HU HC. destruct (conv_any_common HU HC) as [c [Ha Hb]].
  destruct (@binder_path P _ _ Ha f g A B eq_refl) as [U [V [L [E [D F]]]]].
  destruct (@binder_path P _ _ Hb f j A' B' eq_refl) as [U' [V' [M [E' [D' F']]]]].
  destruct f; simpl in *; assert (g = j /\ U=U' /\ V=V') by (repeat split; congruence);
    destruct H as [-> [-> ->]].
  all: split; [reflexivity|]; split.
  all: try solve [eapply path_cat; [exact (path_conv D)|apply reachable_sym; exact (path_conv D')]].
  all: exists (L \u M); intros x Hx; eapply path_cat;
    [apply path_conv, F; fsetdec|apply reachable_sym, path_conv, F'; fsetdec].
Qed.

Local Lemma t_path P a b : entails P a b ->
  forall g A, a = a_T g A -> exists A', b = a_T g A' /\ entails P A A'.
Proof.
  induction 1; intros g A E; subst.
  - exists A; split; [reflexivity|constructor].
  - destruct H as [p [_ H]]. inversion H; subst.
    match goal with J : PStep _ p A ?B |- _ =>
      destruct (IHpath g B eq_refl) as [D [E HD]];
      exists D; split; [exact E|eapply path_cons; [exists p; split; [exact I|exact J]|exact HD]]
    end.
Qed.

Local Lemma conv_t P g j A B :
  uniq P -> conv_any P (a_T g A) (a_T j B) -> g = j /\ conv_any P A B.
Proof.
  intros HU HC. destruct (conv_any_common HU HC) as [c [Ha Hb]].
  destruct (@t_path P _ _ Ha g A eq_refl) as [U [E D]].
  destruct (@t_path P _ _ Hb j B eq_refl) as [V [E' F]].
  assert (g=j /\ U=V) by (repeat split; congruence). destruct H as [-> ->].
  split; [reflexivity|eapply path_cat; [apply path_conv; exact D|apply reachable_sym, path_conv; exact F]].
Qed.

Local Lemma ceq_path P a b : entails P a b ->
  forall h g u v A, a = a_CEq h u v g A ->
  exists u' v' A', b = a_CEq h u' v' g A' /\
    path (grade_step (fun p => h <= p) P) u u' /\
    path (grade_step (fun p => h <= p) P) v v'.
Proof.
  induction 1; intros h g u v A E; subst.
  - exists u, v, A; repeat split; constructor.
  - destruct H as [p [_ H]]. inversion H; subst.
    destruct (IHpath h g a1 b1 A1 eq_refl) as [D [F [T [E [HD HF]]]]].
    exists D,F,T. split; [exact E|]; split.
    + eapply path_cons; [exists p; split; [exact H13|exact H11]|exact HD].
    + eapply path_cons; [exists p; split; [exact H13|exact H12]|exact HF].
Qed.

Local Lemma at_lower P h a b :
  uniq P -> PStep P h a a ->
  path (grade_step (fun p => h <= p) P) a b ->
  path (PStep P h) a b.
Proof.
  intros HU HS H. induction H; [constructor|].
  destruct H as [p [Hp H]].
  pose proof ((proj1 ps_lower) _ _ _ _ H _ _ HU HS) as HL.
  assert (E : p `&` h = h).
  { apply Order.LatticeTheoryMeet.meet_r; exact Hp. }
  rewrite E in HL.
  eapply path_cons; [exact HL|apply IHpath; eauto using ps_refl_right].
Qed.

Local Lemma conv_refl_endpoints P h g j k z u v A B :
  uniq P -> scoped P h u -> scoped P h v ->
  conv_any P (a_CEq j z z k A) (a_CEq h u v g B) ->
  grade_eq P h u v.
Proof.
  intros HU Hu Hv HC.
  destruct (conv_any_common HU HC) as [c [Ha Hb]].
  destruct (@ceq_path P _ _ Ha j k z z A eq_refl) as [U [V [T [E [HZU HZV]]]]].
  destruct (@ceq_path P _ _ Hb h g u v B eq_refl) as [U' [V' [T' [E' [HU' HV']]]]].
  assert (j=h /\ U=U' /\ V=V') by (repeat split; congruence).
  destruct H as [-> [-> ->]].
  assert (C : conv (fun p => h <= p) P u v).
  { eapply path_cat; [apply path_conv; exact HU'|].
    eapply path_cat; [apply reachable_sym, path_conv; exact HZU|].
    eapply path_cat; [apply path_conv; exact HZV|].
    apply reachable_sym, path_conv; exact HV'. }
  destruct (conv_common HU (fun p q => @meet_bound p q h) C) as [d [H1 H2]].
  apply scoped_ps in Hu; apply scoped_ps in Hv.
  split; [assumption|]; split; [assumption|].
  eapply path_cat.
  - exact (path_map (f:=fun z=>z) (fun _ _ H => or_introl H) (at_lower HU Hu H1)).
  - apply reachable_sym.
    exact (path_map (f:=fun z=>z) (fun _ _ H => or_introl H) (at_lower HU Hv H2)).
Qed.

(* Typing with the formation premises needed for weak-head preservation. *)
Local Definition type_value (a : tm) : Prop :=
  match a with
  | a_Type _ | a_Pi _ _ _ | a_CEq _ _ _ _ _ | a_T _ _
  | a_SSigma _ _ _ | a_TyUnit | a_Bool => True
  | _ => False
  end.

Inductive well_typed : context -> grade -> tm -> tm -> Prop :=
| W_Formation W p a s : type_value a -> scoped (labels W) p a ->
    well_typed W p a (a_Type s)
| W_Var W p x g A : g <= p -> binds x (g, A) W ->
    well_typed W p (a_Var_f x) A
| W_Abs W p g A b B L : lc_tm A ->
    (forall x, x \notin L -> well_typed ((x ~ (g,A)) ++ W) p
      (open_tm_wrt_tm b (a_Var_f x)) (open_tm_wrt_tm B (a_Var_f x))) ->
    well_typed W p (a_Abs g A b) (a_Pi g A B)
| W_App W p g a b A B : well_typed W p a (a_Pi g A B) ->
    well_typed W g b A -> well_typed W p (a_App a g b) (open_tm_wrt_tm B b)
| W_Conv W p a A B : well_typed W p a A -> conv_any (labels W) A B -> well_typed W p a B
| W_Refl W p h g a A : well_typed W p a_Refl (a_CEq h a a g A)
| W_Transp W p h g a b u v A B L :
    g <= h -> scoped (labels W) h u -> scoped (labels W) h v ->
    (forall x, x \notin L -> scoped ((x ~ g) ++ labels W) h
       (open_tm_wrt_tm B (a_Var_f x))) ->
    well_typed W p a (a_CEq h u v g A) ->
    well_typed W p b (open_tm_wrt_tm B u) ->
    well_typed W p (a_Transp a b) (open_tm_wrt_tm B v)
| W_Box W p g a A : well_typed W g a A -> well_typed W p (a_Box g a) (a_T g A)
| W_Unbox W p g a A : g <= p -> well_typed W p a (a_T g A) ->
    well_typed W p (a_Unbox g a) A
| W_SPair W p g a b A B : well_typed W g a A ->
    well_typed W p b (open_tm_wrt_tm B a) ->
    well_typed W p (a_SPair a g b) (a_SSigma g A B)
| W_Proj1 W p g a A B : g <= p -> well_typed W p a (a_SSigma g A B) ->
    well_typed W p (a_Proj1 g a) A
| W_Proj2 W p g a A B q L : scoped (labels W) g a ->
    (forall x, x \notin L -> scoped ((x ~ g) ++ labels W) q
      (open_tm_wrt_tm B (a_Var_f x))) ->
    well_typed W p a (a_SSigma g A B) ->
    well_typed W p (a_Proj2 g a) (open_tm_wrt_tm B (a_Proj1 g a))
| W_Unit W p : well_typed W p a_TmUnit a_TyUnit
| W_True W p : well_typed W p a_True a_Bool
| W_False W p : well_typed W p a_False a_Bool
| W_If W p a b c A : well_typed W p a a_Bool ->
    well_typed W p b A -> well_typed W p c A ->
    well_typed W p (a_If a b c) A.

Local Hint Constructors well_typed : ni_wt.

Local Lemma type_scope W p a A : Typing W p a A ->
  exists q, scoped (labels W) q A.
Proof. intro H; exact (proj2 (proj2 (proj2 typing_scoped _ _ _ _ H))). Qed.

Local Lemma typing_wt W p a A : Typing W p a A -> well_typed W p a A.
Proof.
  induction 1;
    try solve [eapply W_Formation; [exact I|eauto using scope_typed with ni_scope]];
    try solve [eauto 3 using defe_conv with ni_wt].
  all: try solve [eapply W_Formation; [exact I|eapply scope_typed; econstructor; eauto]].
  - eapply W_Abs with (L:=L); auto.
    eapply scoped_lc. eapply scope_pi, scope_typed. eassumption.
  - destruct (type_scope H1) as [q Hq].
    destruct (scope_ceq Hq) as [Hgh [Hu Hv]].
    eapply W_Transp with (L:=L) (u:=a0) (v:=a1) (h:=psi0) (g:=psi1) (A:=A) (B:=B);
      eauto using scoped_mono.
    intros x Hx; exact (scope_typed (H x Hx)).
  - destruct (type_scope H) as [q Hq].
    destruct (scope_sig Hq) as [_ [L HL]].
    eapply W_Proj2 with (q:=q) (L:=L); eauto.
    pose proof (scope_typed H0) as HS. inversion HS; assumption.
Qed.

Local Lemma wt_scoped W p a A : well_typed W p a A -> scoped (labels W) p a.
Proof.
  induction 1; try solve [eauto 3 using labels_binds with ni_scope].
  all: simpl in *; try solve [eapply S_Abs with (L:=L); eauto].
  all: try solve [apply S_If; assumption].
Qed.

Local Lemma wt_mono W p a A :
  well_typed W p a A -> forall q, p <= q -> well_typed W q a A.
Proof.
  induction 1; intros q' Hq;
    try solve [eauto 3 using scoped_mono, below_trans with ni_wt].
  all: try solve [eapply W_Abs with (L:=L); eauto].
  all: try solve [eapply W_Transp with (L:=L); eauto].
  all: try solve [eapply W_Proj2 with (L:=L); eauto].
  all: try solve [eapply W_If; eauto].
  - eapply W_Transp with (L:=L) (h:=h) (g:=g) (A:=A) (B:=B) (u:=u) (v:=v);
      try assumption; [exact (IHwell_typed1 _ Hq)|exact (IHwell_typed2 _ Hq)].
  - eapply W_Unbox; [eauto using below_trans|exact (IHwell_typed _ Hq)].
  - eapply W_Proj1; [eauto using below_trans|exact (IHwell_typed _ Hq)].
Qed.

Local Definition types_incl (W V : context) :=
  forall x A, binds x A W -> binds x A V.

Local Lemma types_incl_cons W V x A :
  types_incl W V -> types_incl ((x ~ A) ++ W) ((x ~ A) ++ V).
Proof.
  intros H y B Hy. apply binds_app_iff in Hy.
  apply binds_app_iff. intuition.
Qed.

Local Lemma from_label W x g : binds x g (labels W) ->
  exists A, binds x (g,A) W.
Proof.
  induction W as [|[y [j B]] W IH]; simpl; intros H; [inversion H|].
  change (binds x g ((y ~ j) ++ labels W)) in H.
  apply binds_app_iff in H; destruct H as [H|H].
  - apply binds_one_iff in H; destruct H; subst.
    exists B; left; reflexivity.
  - destruct (IH H) as [A HA]; exists A; auto using binds_cons.
Qed.

Local Lemma incl_labels W V : types_incl W V -> ctx_incl (labels W) (labels V).
Proof.
  intros H x g Hx; destruct (from_label Hx) as [A HA].
  eauto using labels_binds.
Qed.

Local Lemma conv_weaken P Q a b : ctx_incl P Q -> conv_any P a b -> conv_any Q a b.
Proof.
  intro H.
  apply (eq_map (f:=fun z=>z)).
  intros u v [p [_ Huv]]; exists p; split; eauto using ps_weaken.
Qed.

Local Lemma wt_weaken W p a A :
  well_typed W p a A -> forall V, types_incl W V -> well_typed V p a A.
Proof.
  induction 1; intros V HV;
    try solve [eauto 3 using scoped_weaken, incl_labels, conv_weaken with ni_wt].
  all: try solve [eapply W_Formation; [assumption|eapply scoped_weaken; [eassumption|apply incl_labels; exact HV]]].
  all: try solve [eapply W_Var; [eassumption|apply HV; assumption]].
  all: try solve [eapply W_Conv; [exact (IHwell_typed _ HV)|eapply conv_weaken; [apply incl_labels; exact HV|assumption]]].
  all: try solve [eapply W_Abs with (L:=L); [assumption|intros x Hx; eapply H1; [exact Hx|apply types_incl_cons, HV]]].
  all: try solve [eapply W_If; eauto].
  all: try solve [eapply W_App; [apply IHwell_typed1, HV|apply IHwell_typed2, HV]].
  all: try solve [eapply W_SPair; [apply IHwell_typed1, HV|apply IHwell_typed2, HV]].
  - eapply W_Transp with (L:=L) (h:=h) (g:=g) (A:=A) (B:=B) (u:=u) (v:=v);
      try assumption; try solve [eauto using scoped_weaken, incl_labels].
    intros x Hx. eapply scoped_weaken; [exact (H2 x Hx)|].
    apply ctx_incl_cons, incl_labels, HV.
  - eapply W_Proj2 with (L:=L) (q:=q);
      try solve [eauto using scoped_weaken, incl_labels].
    intros x Hx. eapply scoped_weaken; [exact (H0 x Hx)|].
    apply ctx_incl_cons, incl_labels, HV.
Qed.

Local Lemma wt_weaken_cons W p a A x U :
  well_typed W p a A -> well_typed ((x ~ U) ++ W) p a A.
Proof. intro H; eapply wt_weaken; [exact H|]. intros ? ? ?; auto using binds_cons. Qed.

Local Definition remove_type (W V : context) x g U u :=
  forall y j A, binds y (j,A) W ->
    (y = x -> j = g /\ A = U) /\ (y <> x -> binds y (j,subst_tm u x A) V).

Local Lemma remove_type_labels W V x g U u :
  remove_type W V x g U u -> remove_var (labels W) (labels V) x g.
Proof.
  intros H y j Hy. destruct (from_label Hy) as [A HA].
  destruct (H _ _ _ HA); split; eauto using labels_binds; tauto.
Qed.

Local Lemma remove_type_head W x g A u :
  x \notin dom W -> x \notin fv_tm A -> remove_type ((x ~ (g,A)) ++ W) (subst_ctx u x W) x g A u.
Proof.
  intros Hd Hf y j B Hy. apply binds_app_iff in Hy; destruct Hy as [Hy|Hy].
  - apply binds_one_iff in Hy. destruct Hy as [-> E]; inversion E; intuition.
  - split.
    + intros ->. exfalso. apply Hd. eauto using binds_In.
    + intros. change (binds y ((fun '(k,t) => (k, subst_tm u x t)) (j,B))
                           (map (fun '(k,t) => (k, subst_tm u x t)) W)).
      apply binds_map; assumption.
Qed.

Local Lemma remove_type_cons W V x g U u z j B :
  remove_type W V x g U u -> z <> x ->
  remove_type ((z ~ (j,B)) ++ W) ((z ~ (j,subst_tm u x B)) ++ V) x g U u.
Proof.
  intros H Hn y k A Hy. apply binds_app_iff in Hy; destruct Hy as [Hy|Hy].
  - apply binds_one_iff in Hy. destruct Hy as [-> E]; inversion E; subst.
    split; [congruence|intro; left; reflexivity].
  - destruct (H _ _ _ Hy); split; eauto using binds_cons.
Qed.

Local Lemma conv_subst P Q x g u a b :
  remove_var P Q x g -> scoped Q g u -> conv_any P a b ->
  conv_any Q (subst_tm u x a) (subst_tm u x b).
Proof.
  intros HR Hu. apply eq_map.
  intros c d [p [_ H]]. exists p; split; [exact I|].
  eapply (proj1 pstep_substitution); eauto using scoped_cs.
Qed.

Local Lemma subst_open_var a u x z :
  lc_tm u -> z <> x ->
  subst_tm u x (open_tm_wrt_tm a (a_Var_f z)) =
  open_tm_wrt_tm (subst_tm u x a) (a_Var_f z).
Proof.
  intros Hu Hn. rewrite subst_open by assumption.
  rewrite (@subst_fresh (a_Var_f z) x u) by (simpl; fsetdec).
  reflexivity.
Qed.

Local Lemma wt_subst W p a A :
  well_typed W p a A -> forall V x g U u,
  remove_type W V x g U u -> x \notin fv_tm U -> well_typed V g u U ->
  well_typed V p (subst_tm u x a) (subst_tm u x A).
Proof.
  induction 1; intros V x0 j U payload Hr Hf Hu;
    assert (HS := wt_scoped Hu);
    assert (HL := scoped_lc HS);
    simpl in *; repeat rewrite subst_open by exact HL.
  all: try solve [eapply W_Formation;
    [destruct a; simpl in *; tauto|eauto using scoped_subst, remove_type_labels]].
  all: try solve [eapply W_Conv; eauto using conv_subst, remove_type_labels].
  all: try solve [eapply W_App; eauto].
  all: try solve [apply W_Refl].
  all: try solve [eapply W_Box; eauto].
  all: try solve [eapply W_Unbox; eauto].
  all: try solve [eapply W_SPair; eauto].
  all: try solve [eapply W_Proj1; eauto].
  all: try solve [apply W_Unit || apply W_True || apply W_False].
  all: try solve [eapply W_If; eauto].
  - decide_atoms; subst;
      match goal with K : binds _ _ _ |- _ => destruct (Hr _ _ _ K) as [E D] end.
    + specialize (E eq_refl) as [-> ->].
      rewrite subst_fresh by assumption. eauto using wt_mono.
    + eapply W_Var; eauto.
  - eapply W_Abs with (L:=L \u {{x0}}).
    + auto using lc_subst.
    + intros z Hz.
      rewrite <- !(@subst_open_var _ payload x0 z) by (auto; fsetdec).
      eapply H1; [fsetdec|eapply remove_type_cons; [exact Hr|fsetdec]
                          |exact Hf|auto using wt_weaken_cons].
  - eapply W_Transp with (L:=L \u {{x0}}) (h:=h) (g:=g)
      (u:=subst_tm payload x0 u) (v:=subst_tm payload x0 v)
      (A:=subst_tm payload x0 A) (B:=subst_tm payload x0 B).
    + exact H.
    + eapply scoped_subst; [exact H0|exact (remove_type_labels Hr)|exact HS].
    + eapply scoped_subst; [exact H1|exact (remove_type_labels Hr)|exact HS].
    + intros z Hz. rewrite <- (@subst_open_var B payload x0 z) by (auto; fsetdec).
      eapply scoped_subst; [apply H2; fsetdec| |apply scoped_weaken_cons; exact HS].
      apply remove_var_cons; [exact (remove_type_labels Hr)|fsetdec].
    + exact (IHwell_typed1 _ _ _ _ _ Hr Hf Hu).
    + rewrite <- (@subst_open B x0 payload u HL).
      exact (IHwell_typed2 _ _ _ _ _ Hr Hf Hu).
  - eapply W_SPair.
    + exact (IHwell_typed1 _ _ _ _ _ Hr Hf Hu).
    + rewrite <- (@subst_open B x0 payload a HL).
      exact (IHwell_typed2 _ _ _ _ _ Hr Hf Hu).
  - eapply W_Proj2 with (L:=L \u {{x0}}) (q:=q) (A:=subst_tm payload x0 A).
    + eapply scoped_subst; [exact H|exact (remove_type_labels Hr)|exact HS].
    + intros z Hz. rewrite <- (@subst_open_var B payload x0 z) by (auto; fsetdec).
      eapply scoped_subst; [apply H0; fsetdec| |apply scoped_weaken_cons; exact HS].
      apply remove_var_cons; [exact (remove_type_labels Hr)|fsetdec].
    + exact (IHwell_typed _ _ _ _ _ Hr Hf Hu).
Qed.

Local Fixpoint context_fv (W : context) : vars :=
  match W with
  | nil => empty
  | (_,(_,A)) :: W => fv_tm A \u context_fv W
  end.

Local Lemma ctx_subst_fresh W x u :
  x \notin context_fv W -> subst_ctx u x W = W.
Proof.
  induction W as [|[y [g A]] W IH]; simpl; auto.
  intro H. rewrite subst_fresh, IH by fsetdec. reflexivity.
Qed.

Local Lemma wt_open W p g A b B L u :
  (forall x, x \notin L -> well_typed ((x ~ (g,A)) ++ W) p
    (open_tm_wrt_tm b (a_Var_f x)) (open_tm_wrt_tm B (a_Var_f x))) ->
  well_typed W g u A ->
  well_typed W p (open_tm_wrt_tm b u) (open_tm_wrt_tm B u).
Proof.
  intros H Hu.
  pick fresh x for (L \u dom W \u context_fv W \u fv_tm A \u fv_tm b \u fv_tm B).
  rewrite (@open_as_subst b x u), (@open_as_subst B x u) by fsetdec.
  assert (E : subst_ctx u x W = W) by (apply ctx_subst_fresh; fsetdec).
  rewrite <- E at 1.
  eapply wt_subst with (W:=(x ~ (g,A)) ++ W) (g:=g) (U:=A).
  - apply H; fsetdec.
  - apply remove_type_head; fsetdec.
  - fsetdec.
  - rewrite E; exact Hu.
Qed.

Local Lemma conv_open P g B D L u :
  (forall x, x \notin L -> conv_any ((x ~ g) ++ P)
    (open_tm_wrt_tm B (a_Var_f x)) (open_tm_wrt_tm D (a_Var_f x))) ->
  scoped P g u ->
  conv_any P (open_tm_wrt_tm B u) (open_tm_wrt_tm D u).
Proof.
  intros H Hu. pick fresh x for (L \u dom P \u fv_tm B \u fv_tm D).
  rewrite (@open_as_subst B x u), (@open_as_subst D x u) by fsetdec.
  eapply conv_subst; [apply remove_var_head; fsetdec|exact Hu|apply H; fsetdec].
Qed.

Local Lemma conv_open_red P g p B L u v :
  (forall x, x \notin L -> scoped ((x ~ g) ++ P) p (open_tm_wrt_tm B (a_Var_f x))) ->
  scoped P g u -> Red u v ->
  conv_any P (open_tm_wrt_tm B u) (open_tm_wrt_tm B v).
Proof.
  intros H Hu Hr. apply conv_step with (p:=p); [exact I|].
  eapply ps_open with (L:=L) (g:=g).
  - intros x Hx. apply scoped_ps, H, Hx.
  - destruct (red_scoped Hr Hu) as [Hv _].
    apply cs_intro; [eauto using scoped_lc|eauto using scoped_lc|].
    intro Hgp. apply (proj2 (red_scoped Hr (scoped_mono Hu Hgp))).
Qed.

Local Lemma conv_open_eq P g p B L u v :
  (forall x, x \notin L -> scoped ((x ~ g) ++ P) p (open_tm_wrt_tm B (a_Var_f x))) ->
  g <= p -> grade_eq P p u v ->
  conv_any P (open_tm_wrt_tm B u) (open_tm_wrt_tm B v).
Proof.
  intros H Hg (_ & _ & He).
  eapply (eq_map (f:=open_tm_wrt_tm B)); [|exact He].
  intros s t Hst. exists p; split; [exact I|].
  eapply ps_open with (L:=L) (g:=g).
  - intros x Hx. apply scoped_ps, H, Hx.
  - apply CStep_Leq; assumption.
Qed.

Local Lemma wt_inv_abs W p g A a T :
  well_typed W p (a_Abs g A a) T ->
  exists B L, (forall x, x \notin L -> well_typed ((x ~ (g,A)) ++ W) p
      (open_tm_wrt_tm a (a_Var_f x)) (open_tm_wrt_tm B (a_Var_f x))) /\
  conv_any (labels W) (a_Pi g A B) T.
Proof.
  intro H. remember (a_Abs g A a) as t eqn:E in H.
  revert E. induction H; intros;
    match goal with E : _ = _ |- _ => inversion E; subst; clear E end;
    try contradiction;
    try solve [repeat match goal with |- exists _, _ => eexists | |- _ /\ _ => split end; try eassumption; constructor].
  specialize (IHwell_typed eq_refl).
  repeat match goal with J : exists _, _ |- _ => destruct J end.
  repeat match goal with J : _ /\ _ |- _ => destruct J end.
  repeat match goal with |- exists _, _ => eexists | |- _ /\ _ => split end; try eassumption; eapply path_cat; eassumption.
Qed.

Local Lemma wt_inv_app W p g a b T :
  well_typed W p (a_App a g b) T ->
  exists A B, well_typed W p a (a_Pi g A B) /\ well_typed W g b A /\
  conv_any (labels W) (open_tm_wrt_tm B b) T.
Proof.
  intro H. remember (a_App a g b) as t eqn:E in H.
  revert E. induction H; intros;
    match goal with E : _ = _ |- _ => inversion E; subst; clear E end;
    try contradiction;
    try solve [repeat match goal with |- exists _, _ => eexists | |- _ /\ _ => split end; try eassumption; constructor].
  specialize (IHwell_typed eq_refl).
  repeat match goal with J : exists _, _ |- _ => destruct J end.
  repeat match goal with J : _ /\ _ |- _ => destruct J end.
  repeat match goal with |- exists _, _ => eexists | |- _ /\ _ => split end; try eassumption; eapply path_cat; eassumption.
Qed.

Local Lemma wt_inv_box W p g a T :
  well_typed W p (a_Box g a) T ->
  exists A, well_typed W g a A /\ conv_any (labels W) (a_T g A) T.
Proof.
  intro H. remember (a_Box g a) as t eqn:E in H.
  revert E. induction H; intros;
    match goal with E : _ = _ |- _ => inversion E; subst; clear E end;
    try contradiction;
    try solve [repeat match goal with |- exists _, _ => eexists | |- _ /\ _ => split end; try eassumption; constructor].
  specialize (IHwell_typed eq_refl).
  repeat match goal with J : exists _, _ |- _ => destruct J end.
  repeat match goal with J : _ /\ _ |- _ => destruct J end.
  repeat match goal with |- exists _, _ => eexists | |- _ /\ _ => split end; try eassumption; eapply path_cat; eassumption.
Qed.

Local Lemma wt_inv_unbox W p g a T :
  well_typed W p (a_Unbox g a) T ->
  exists A, g <= p /\ well_typed W p a (a_T g A) /\ conv_any (labels W) A T.
Proof.
  intro H. remember (a_Unbox g a) as t eqn:E in H.
  revert E. induction H; intros;
    match goal with E : _ = _ |- _ => inversion E; subst; clear E end;
    try contradiction;
    try solve [repeat match goal with |- exists _, _ => eexists | |- _ /\ _ => split end; try eassumption; constructor].
  specialize (IHwell_typed eq_refl).
  repeat match goal with J : exists _, _ |- _ => destruct J end.
  repeat match goal with J : _ /\ _ |- _ => destruct J end.
  repeat match goal with |- exists _, _ => eexists | |- _ /\ _ => split end; try eassumption; eapply path_cat; eassumption.
Qed.

Local Lemma wt_inv_pair W p g a b T :
  well_typed W p (a_SPair a g b) T ->
  exists A B, well_typed W g a A /\ well_typed W p b (open_tm_wrt_tm B a) /\
  conv_any (labels W) (a_SSigma g A B) T.
Proof.
  intro H. remember (a_SPair a g b) as t eqn:E in H.
  revert E. induction H; intros;
    match goal with E : _ = _ |- _ => inversion E; subst; clear E end;
    try contradiction;
    try solve [repeat match goal with |- exists _, _ => eexists | |- _ /\ _ => split end; try eassumption; constructor].
  specialize (IHwell_typed eq_refl).
  repeat match goal with J : exists _, _ |- _ => destruct J end.
  repeat match goal with J : _ /\ _ |- _ => destruct J end.
  repeat match goal with |- exists _, _ => eexists | |- _ /\ _ => split end; try eassumption; eapply path_cat; eassumption.
Qed.

Local Lemma wt_inv_proj1 W p g a T :
  well_typed W p (a_Proj1 g a) T ->
  exists A B, g <= p /\ well_typed W p a (a_SSigma g A B) /\ conv_any (labels W) A T.
Proof.
  intro H. remember (a_Proj1 g a) as t eqn:E in H.
  revert E. induction H; intros;
    match goal with E : _ = _ |- _ => inversion E; subst; clear E end;
    try contradiction;
    try solve [repeat match goal with |- exists _, _ => eexists | |- _ /\ _ => split end; try eassumption; constructor].
  specialize (IHwell_typed eq_refl).
  repeat match goal with J : exists _, _ |- _ => destruct J end.
  repeat match goal with J : _ /\ _ |- _ => destruct J end.
  repeat match goal with |- exists _, _ => eexists | |- _ /\ _ => split end; try eassumption; eapply path_cat; eassumption.
Qed.

Local Lemma wt_inv_proj2 W p g a T :
  well_typed W p (a_Proj2 g a) T ->
  exists A B q L, scoped (labels W) g a /\
  (forall x, x \notin L -> scoped ((x ~ g) ++ labels W) q (open_tm_wrt_tm B (a_Var_f x))) /\
  well_typed W p a (a_SSigma g A B) /\ conv_any (labels W) (open_tm_wrt_tm B (a_Proj1 g a)) T.
Proof.
  intro H. remember (a_Proj2 g a) as t eqn:E in H.
  revert E. induction H; intros;
    match goal with E : _ = _ |- _ => inversion E; subst; clear E end;
    try contradiction;
    try solve [repeat match goal with |- exists _, _ => eexists | |- _ /\ _ => split end; try eassumption; constructor].
  specialize (IHwell_typed eq_refl).
  repeat match goal with J : exists _, _ |- _ => destruct J end.
  repeat match goal with J : _ /\ _ |- _ => destruct J end.
  repeat match goal with |- exists _, _ => eexists | |- _ /\ _ => split end; try eassumption; eapply path_cat; eassumption.
Qed.

Local Lemma wt_inv_transp W p a b T :
  well_typed W p (a_Transp a b) T ->
  exists h g u v A B L, g <= h /\ scoped (labels W) h u /\ scoped (labels W) h v /\
  (forall x, x \notin L -> scoped ((x ~ g) ++ labels W) h (open_tm_wrt_tm B (a_Var_f x))) /\
  well_typed W p a (a_CEq h u v g A) /\ well_typed W p b (open_tm_wrt_tm B u) /\
  conv_any (labels W) (open_tm_wrt_tm B v) T.
Proof.
  intro H. remember (a_Transp a b) as t eqn:E in H.
  revert E. induction H; intros;
    match goal with E : _ = _ |- _ => inversion E; subst; clear E end;
    try contradiction;
    try solve [repeat match goal with |- exists _, _ => eexists | |- _ /\ _ => split end; try eassumption; constructor].
  destruct (IHwell_typed eq_refl) as (h & g & u & v & D & F & L & Hgh & Hu & Hv & HM & HA & HB & HC).
  exists h,g,u,v,D,F,L. repeat split; try assumption. eapply path_cat; eassumption.
  exists h,g,u,v,A,B,L. repeat split; try assumption. constructor.
Qed.

Local Lemma wt_inv_refl W p T :
  well_typed W p (a_Refl) T ->
  exists h g a A, conv_any (labels W) (a_CEq h a a g A) T.
Proof.
  intro H. remember (a_Refl) as t eqn:E in H.
  revert E. induction H; intros;
    match goal with E : _ = _ |- _ => inversion E; subst; clear E end;
    try contradiction;
    try solve [repeat match goal with |- exists _, _ => eexists | |- _ /\ _ => split end; try eassumption; constructor].
  specialize (IHwell_typed eq_refl).
  repeat match goal with J : exists _, _ |- _ => destruct J end.
  repeat match goal with J : _ /\ _ |- _ => destruct J end.
  repeat match goal with |- exists _, _ => eexists | |- _ /\ _ => split end; try eassumption; eapply path_cat; eassumption.
Qed.

Local Lemma wt_inv_if W p a b c T :
  well_typed W p (a_If a b c) T ->
  exists A, well_typed W p a a_Bool /\ well_typed W p b A /\ well_typed W p c A /\
  conv_any (labels W) A T.
Proof.
  intro H. remember (a_If a b c) as t eqn:E in H.
  revert E. induction H; intros;
    match goal with E : _ = _ |- _ => inversion E; subst; clear E end;
    try contradiction;
    try solve [repeat match goal with |- exists _, _ => eexists | |- _ /\ _ => split end; try eassumption; constructor].
  specialize (IHwell_typed eq_refl).
  repeat match goal with J : exists _, _ |- _ => destruct J end.
  repeat match goal with J : _ /\ _ |- _ => destruct J end.
  repeat match goal with |- exists _, _ => eexists | |- _ /\ _ => split end; try eassumption; eapply path_cat; eassumption.
Qed.

(* Weak-head reduction preserves the typing needed for Boolean canonicity. *)
Local Lemma wt_preservation W p a b T :
  uniq W -> Red a b -> well_typed W p a T -> well_typed W p b T.
Proof.
  intros HU HR. revert T. induction HR; intros T WT.
  - destruct (wt_inv_app WT) as [A [B [HF [HB HC]]]].
    eapply W_Conv; [|exact HC].
    eapply W_App with (A:=A) (B:=B); [exact (IHHR _ HF)|exact HB].
  - destruct (wt_inv_app WT) as (domain & codomain & function_typing & argument_typing & app_conversion).
    destruct (wt_inv_abs function_typing) as (body_type & forbidden & body_typing & function_conversion).
    destruct (conv_binder (f:=true) (labels_uniq HU) function_conversion)
      as (_ & domain_conversion & avoid & codomain_conversion).
    eapply W_Conv; [|exact app_conversion].
    eapply W_Conv.
    + eapply wt_open; [exact body_typing|].
      eapply W_Conv; [exact argument_typing|apply reachable_sym; exact domain_conversion].
    + eapply conv_open; [exact codomain_conversion|exact (wt_scoped argument_typing)].
  - destruct (wt_inv_transp WT) as (h & g & u & v & A & B & L & Hgh & Hu & Hv & HM & HA & HB & HC).
    eapply W_Conv; [|exact HC].
    eapply W_Transp with (L:=L) (h:=h) (g:=g) (A:=A) (B:=B) (u:=u) (v:=v);
      try assumption; exact (IHHR _ HA).
  - destruct (wt_inv_transp WT) as (h & g & u & v & A & B & L & Hgh & Hu & Hv & HM & HA & HB & HC).
    destruct (wt_inv_refl HA) as (j & k & z & D & HE).
    eapply W_Conv; [exact HB|]. eapply path_cat; [|exact HC].
    eapply conv_open_eq; [exact HM|exact Hgh|].
    eapply conv_refl_endpoints; eauto using labels_uniq.
  - destruct (wt_inv_unbox WT) as [A [HP [HA HC]]].
    eapply W_Conv; [eapply W_Unbox; [exact HP|exact (IHHR _ HA)]|exact HC].
  - destruct (wt_inv_unbox WT) as [A [HP [HA HC]]].
    destruct (wt_inv_box HA) as [B [HT HE]].
    destruct (conv_t (labels_uniq HU) HE) as [_ HB].
    eapply W_Conv.
    + eapply wt_mono; eauto.
    + eapply path_cat; eassumption.
  - destruct (wt_inv_proj1 WT) as [A [B [HG [HA HC]]]].
    eapply W_Conv; [eapply W_Proj1; [exact HG|exact (IHHR _ HA)]|exact HC].
  - destruct (wt_inv_proj2 WT) as (A & B & q & L & HS & HB & HA & HC).
    destruct (red_scoped HR HS) as [HS' _].
    eapply W_Conv.
    + eapply W_Proj2 with (L:=L); [exact HS'|exact HB|exact (IHHR _ HA)].
    + eapply path_cat; [|exact HC]. apply reachable_sym.
      eapply conv_open_red; [exact HB| |].
      * apply S_Proj1; eauto using grade_refl.
      * apply R_Proj1Cong; exact HR.
  - destruct (wt_inv_proj1 WT) as [A [B [HG [HA HC]]]].
    destruct (wt_inv_pair HA) as [D [C [HD [HB HE]]]].
    destruct (conv_binder (f:=false) (labels_uniq HU) HE) as [_ [HDA _]].
    eapply W_Conv.
    + eapply wt_mono; eauto.
    + eapply path_cat; eassumption.
  - destruct (wt_inv_proj2 WT) as (A & B & q & L & HS & HB & HA & HC).
    destruct (wt_inv_pair HA) as [D [C [HD [HT HE]]]].
    destruct (conv_binder (f:=false) (labels_uniq HU) HE) as [_ [_ [F HF]]].
    eapply W_Conv; [exact HT|].
    eapply path_cat; [|exact HC].
    eapply path_cat.
    + eapply conv_open; [exact HF|exact (wt_scoped HD)].
    + apply reachable_sym. eapply conv_open_red; [exact HB| |].
      * apply S_Proj1; eauto using grade_refl.
      * apply R_Proj1Beta; assumption.
  - destruct (wt_inv_if WT) as [A [HA [HB [HC HD]]]].
    eapply W_Conv; [apply W_If; [exact (IHHR _ HA)|exact HB|exact HC]|exact HD].
  - destruct (wt_inv_if WT) as [A [HA [HB [HC HD]]]].
    eapply W_Conv; eassumption.
  - destruct (wt_inv_if WT) as [A [HA [HB [HC HD]]]].
    eapply W_Conv; eassumption.
Qed.

Local Lemma wt_boolean W p a T :
  uniq W -> well_typed W p a T -> Value a -> conv_any (labels W) T a_Bool ->
  a = a_True \/ a = a_False.
Proof.
  intros HU HT; induction HT; simpl; intros HV HC;
    try discriminate; try tauto.
  all: try solve [eapply IHHT; [exact HU|exact HV|eapply path_cat; eassumption]].
  all: exfalso;
    let E := fresh in
    pose proof (conv_heads (labels_uniq HU) HC eq_refl eq_refl) as E;
    discriminate E.
Qed.

Local Lemma reds_wt W p a b T :
  uniq W -> Reds a b -> well_typed W p a T ->
  well_typed W p b T /\ conv_any (labels W) a b.
Proof.
  intros HU HR. induction HR; intro HT.
  - split; [exact HT|constructor].
  - destruct (IHHR (wt_preservation HU H HT)) as [HT' HC].
    split; [exact HT'|].
    eapply path_cat; [|exact HC].
    eapply conv_step with (p:=p); [exact I|].
    exact (proj2 (red_scoped H (wt_scoped HT))).
Qed.
Theorem non_interference
    ψ a0 b0 v0 v1
    (h0 : GDefEq nil ψ a0 b0)
    (h1 : Typing nil ψ a0 a_Bool)
    (h2 : Typing nil ψ b0 a_Bool)
    (h3 : Reds a0 v0)
    (h4 : Reds b0 v1)
    (hv0 : Value v0)
    (hv1 : Value v1) :
    v0 = v1.
Proof.
  assert (HU : uniq (@nil (atom * (grade * tm)))) by constructor.
  destruct (reds_wt HU h3 (typing_wt h1)) as [HT0 HE0].
  destruct (reds_wt HU h4 (typing_wt h2)) as [HT1 HE1].
  assert (HB : conv_any nil a_Bool a_Bool) by constructor.
  assert (HE : conv_any nil v0 v1).
  { eapply path_cat; [apply reachable_sym; exact HE0|].
    eapply path_cat; [|exact HE1].
    apply (conv_general (p:=ψ)), (proj1 grade_eq_sound); exact h0. }
  destruct (wt_boolean HU HT0 hv0 HB) as [Hv0 | Hv0];
    destruct (wt_boolean HU HT1 hv1 HB) as [Hv1 | Hv1]; subst v0; subst v1; try reflexivity;
    exfalso; pose proof (conv_heads (labels_uniq HU) HE eq_refl eq_refl) as H;
    discriminate H.
Qed.
