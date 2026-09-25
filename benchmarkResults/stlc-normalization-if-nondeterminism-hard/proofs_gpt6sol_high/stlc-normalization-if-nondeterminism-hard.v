(** STLC CBV strong-normalization benchmark, Hard variant.
    Features: if-nondeterminism. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Relations.Relation_Definitions Lia.
Import ListNotations.

Module STLCNormalizationIfNondeterminismHardTask.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
      R x y ->
      multi R y z ->
      multi R x z.

Definition atom := nat.

Inductive ty : Type :=
  | Ty_Bool : ty
  | Ty_Arrow : ty -> ty -> ty.

Inductive tm : Type :=
  | tm_bvar : nat -> tm
  | tm_fvar : atom -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : ty -> tm -> tm
  | tm_true : tm
  | tm_false : tm

  | tm_if : tm -> tm -> tm -> tm
  | tm_choice : tm -> tm -> tm.

Declare Scope stlc_scope.
Delimit Scope stlc_scope with stlc.
Open Scope stlc_scope.

Declare Custom Entry stlc_ty.
Declare Custom Entry stlc_tm.

Notation "<{{ x }}>" := x (x custom stlc_ty).
Notation "x" := x
  (in custom stlc_ty at level 0, x constr at level 0) : stlc_scope.
Notation "'Bool'" := Ty_Bool
  (in custom stlc_ty at level 0) : stlc_scope.
Notation "S -> T" := (Ty_Arrow S T)
  (in custom stlc_ty at level 99, right associativity) : stlc_scope.

Notation "$( t )" := t
  (in custom stlc_ty at level 0, t constr) : stlc_scope.
Notation "( T )" := T
  (in custom stlc_ty at level 0, T custom stlc_ty) : stlc_scope.

Notation "<{ e }>" := e
  (e custom stlc_tm at level 200) : stlc_scope.
Notation "$( x )" := x
  (in custom stlc_tm at level 0, x constr, only parsing) : stlc_scope.
Notation "x" := x
  (in custom stlc_tm at level 0, x constr at level 0) : stlc_scope.
Notation "'bvar' n" := (tm_bvar n)
  (in custom stlc_tm at level 0, n constr at level 0) : stlc_scope.
Notation "'fvar' x" := (tm_fvar x)
  (in custom stlc_tm at level 0, x constr at level 0) : stlc_scope.
Notation "'true'" := tm_true
  (in custom stlc_tm at level 0) : stlc_scope.
Notation "'false'" := tm_false
  (in custom stlc_tm at level 0) : stlc_scope.
Notation "( x )" := x
  (in custom stlc_tm at level 0, x custom stlc_tm) : stlc_scope.
Notation "x y" := (tm_app x y)
  (in custom stlc_tm at level 10, left associativity) : stlc_scope.
Notation "'lambda' ':' T ',' t" := (tm_abs T t)
  (in custom stlc_tm at level 200,
   T custom stlc_ty,
   t custom stlc_tm at level 200,
   left associativity) : stlc_scope.

Notation "'if' t1 'then' t2 'else' t3" := (tm_if t1 t2 t3)
  (in custom stlc_tm at level 200,
   t1 custom stlc_tm, t2 custom stlc_tm, t3 custom stlc_tm at level 200) : stlc_scope.
Notation "'choice' t1 'or' t2" := (tm_choice t1 t2)
  (in custom stlc_tm at level 200,
   t1 custom stlc_tm, t2 custom stlc_tm at level 200) : stlc_scope.

Fixpoint open_rec (k : nat) (u : tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => if Nat.eqb k i then u else tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_app t1 t2 => tm_app (open_rec k u t1) (open_rec k u t2)
  | tm_abs T t1 => tm_abs T (open_rec (S k) u t1)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (open_rec k u t1) (open_rec k u t2) (open_rec k u t3)
  | tm_choice t1 t2 => tm_choice (open_rec k u t1) (open_rec k u t2)
  end.

Definition open (t u : tm) : tm := open_rec 0 u t.

Inductive lc_at : nat -> tm -> Prop :=
  | lc_bvar : forall k i,
      i < k ->
      lc_at k (tm_bvar i)
  | lc_fvar : forall k x,
      lc_at k (tm_fvar x)
  | lc_app : forall k t1 t2,
      lc_at k t1 ->
      lc_at k t2 ->
      lc_at k (tm_app t1 t2)
  | lc_abs : forall k T t1,
      lc_at (S k) t1 ->
      lc_at k (tm_abs T t1)
  | lc_true : forall k,
      lc_at k tm_true
  | lc_false : forall k,
      lc_at k tm_false
    | lc_if : forall k t1 t2 t3,
      lc_at k t1 -> lc_at k t2 -> lc_at k t3 -> lc_at k (tm_if t1 t2 t3)
  | lc_choice : forall k t1 t2,
      lc_at k t1 -> lc_at k t2 -> lc_at k (tm_choice t1 t2).

Definition locally_closed (t : tm) : Prop := lc_at 0 t.

Hint Constructors lc_at : core.

Inductive value : tm -> Prop :=
  | v_abs : forall T t,
      locally_closed (tm_abs T t) ->
      value (tm_abs T t)
  | v_true :
      value tm_true
  | v_false :
      value tm_false.

Hint Constructors value : core.

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall T t v,
      locally_closed (tm_abs T t) ->
      value v ->
      tm_app (tm_abs T t) v --> open t v
  | ST_App1 : forall t1 t1' t2,
      t1 --> t1' ->
      locally_closed t2 ->
      tm_app t1 t2 --> tm_app t1' t2
  | ST_App2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      tm_app v1 t2 --> tm_app v1 t2'
  | ST_IfTrue : forall t1 t2,
      locally_closed t1 ->
      locally_closed t2 ->
      tm_if tm_true t1 t2 --> t1
  | ST_IfFalse : forall t1 t2,
      locally_closed t1 ->
      locally_closed t2 ->
      tm_if tm_false t1 t2 --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      locally_closed t2 ->
      locally_closed t3 ->
      tm_if t1 t2 t3 --> tm_if t1' t2 t3
  | ST_ChoiceLeft : forall t1 t2,
      locally_closed t1 ->
      locally_closed t2 ->
      tm_choice t1 t2 --> t1
  | ST_ChoiceRight : forall t1 t2,
      locally_closed t1 ->
      locally_closed t2 ->
      tm_choice t1 t2 --> t2
where "t '-->' t'" := (step t t').

Hint Constructors step : core.

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Definition context := atom -> option ty.

Definition empty : context := fun _ => None.

Definition update (Gamma : context) (x : atom) (T : ty) : context :=
  fun y => if Nat.eqb x y then Some T else Gamma y.

Notation "x '|->' v ';' m" := (update m x v)
  (in custom stlc_tm at level 0,
   x constr at level 0,
   v custom stlc_ty,
   right associativity) : stlc_scope.
Notation "x '|->' v" := (update empty x v)
  (in custom stlc_tm at level 0,
   x constr at level 0,
   v custom stlc_ty) : stlc_scope.
Notation "'empty'" := empty
  (in custom stlc_tm) : stlc_scope.

Reserved Notation "<{ Gamma '|--' t '\in' T }>"
  (at level 0,
   Gamma custom stlc_tm at level 200,
   t custom stlc_tm,
   T custom stlc_ty).

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      <{ Gamma |-- fvar x \in T }>
  | T_Abs : forall (L : list atom) Gamma T1 T2 t1,
      (forall x, ~ In x L ->
        <{ x |-> T1 ; Gamma |-- $(open t1 (tm_fvar x)) \in T2 }>) ->
      <{ Gamma |-- lambda : T1, $(t1) \in T1 -> T2 }>
  | T_App : forall Gamma t1 t2 T1 T2,
      <{ Gamma |-- $(t1) \in T1 -> T2 }> ->
      <{ Gamma |-- $(t2) \in T1 }> ->
      <{ Gamma |-- $(tm_app t1 t2) \in T2 }>
  | T_True : forall Gamma,
      <{ Gamma |-- true \in Bool }>
  | T_False : forall Gamma,
      <{ Gamma |-- false \in Bool }>
  | T_If : forall Gamma t1 t2 t3 T,
      <{ Gamma |-- $(t1) \in Bool }> ->
      <{ Gamma |-- $(t2) \in T }> ->
      <{ Gamma |-- $(t3) \in T }> ->
      <{ Gamma |-- $(tm_if t1 t2 t3) \in T }>
  | T_Choice : forall Gamma t1 t2 T,
      <{ Gamma |-- $(t1) \in T }> ->
      <{ Gamma |-- $(t2) \in T }> ->
      <{ Gamma |-- choice $(t1) or $(t2) \in T }>
where "<{ Gamma '|--' t '\in' T }>" := (has_type Gamma t T)
  : stlc_scope.

Hint Constructors has_type : core.

Inductive strongly_normalizing : tm -> Prop :=

  | SN_intro : forall t,
      (forall t', t --> t' -> strongly_normalizing t') ->
      strongly_normalizing t.

Fixpoint fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ => [] | tm_fvar x => [x]
  | tm_app a b | tm_choice a b => fv a ++ fv b
  | tm_abs _ b => fv b
  | tm_true | tm_false => []
  | tm_if a b c => fv a ++ fv b ++ fv c
  end.

Fixpoint subst (rho : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i | tm_fvar x => rho x
  | tm_app a b => tm_app (subst rho a) (subst rho b)
  | tm_abs T b => tm_abs T (subst rho b)
  | tm_true => tm_true | tm_false => tm_false
  | tm_if a b c => tm_if (subst rho a) (subst rho b) (subst rho c)
  | tm_choice a b => tm_choice (subst rho a) (subst rho b)
  end.

Definition fresh (L : list atom) :=
  fold_right (fun x n => S (Nat.max x n)) 0 L.

Lemma fresh_gt : forall L x, In x L -> x < fresh L.
Proof.
  induction L as [|a L IH]; simpl; intros x H; [contradiction|].
  destruct H as [<-|H]; [lia|].
  specialize (IH x H). lia.
Qed.

Lemma lc_weaken : forall k j t, k <= j -> lc_at k t -> lc_at j t.
Proof.
  intros k j t Hkj H; revert j Hkj.
  induction H; intros j Hkj.
  - constructor; lia.
  - constructor.
  - constructor; eauto.
  - constructor. apply IHlc_at. lia.
  - constructor.
  - constructor.
  - constructor; eauto.
  - constructor; eauto.
Qed.

Lemma lc_open_inv : forall t k u,
  lc_at k (open_rec k u t) -> lc_at (S k) t.
Proof.
  induction t; intros k u H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. constructor; lia.
    + inversion H; subst. constructor; lia.
  - constructor.
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor; eauto.
  - constructor.
  - constructor.
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor; eauto.
Qed.

Lemma lc_open : forall t k u,
  lc_at (S k) t -> lc_at k u -> lc_at k (open_rec k u t).
Proof.
  induction t; intros k u Ht Hu; simpl; inversion Ht; subst.
  - destruct (Nat.eqb k n) eqn:E; auto.
    apply Nat.eqb_neq in E. constructor. lia.
  - constructor.
  - constructor; eauto.
  - constructor. apply IHt; auto.
    apply lc_weaken with (k := k); [lia | exact Hu].
  - constructor.
  - constructor.
  - constructor; eauto.
  - constructor; eauto.
Qed.

Lemma typing_lc : forall Gamma t T, has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T H; unfold locally_closed; induction H; eauto using lc_at.
  - set (x := fresh L).
    assert (Hfresh : ~ In x L).
    { intro Hx. pose proof (fresh_gt L x Hx). unfold x in *. lia. }
    specialize (H0 x Hfresh).
    apply lc_abs. apply (lc_open_inv t1 0 (tm_fvar x)). exact H0.
Qed.

Lemma lc_subst : forall k t rho,
  lc_at k t -> (forall x, locally_closed (rho x)) -> lc_at k (subst rho t).
Proof.
  intros k t rho H; revert rho.
  induction H; intros rho Hr; simpl; eauto using lc_at.
  apply lc_weaken with (k := 0); [lia | apply Hr].
Qed.

Lemma open_rec_lc : forall t k u,
  lc_at k t -> open_rec k u t = t.
Proof.
  induction t; intros k u H; inversion H; subst; simpl; f_equal; eauto.
  - destruct (Nat.eqb k n) eqn:E; [apply Nat.eqb_eq in E; lia | reflexivity].
Qed.

Lemma subst_open_rec : forall t k rho x u,
  ~ In x (fv t) ->
  (forall y, locally_closed (rho y)) ->
  subst (fun y => if Nat.eqb x y then u else rho y)
        (open_rec k (tm_fvar x) t) =
  open_rec k u (subst rho t).
Proof.
  induction t; intros k rho x u Hfresh Hr; simpl in *; try reflexivity.
  - destruct (Nat.eqb k n); simpl; [rewrite Nat.eqb_refl |]; reflexivity.
  - assert (x <> a) by (intro E; subst; apply Hfresh; auto).
    assert (E : (x =? a) = false) by (apply Nat.eqb_neq; auto).
    rewrite E.
    symmetry. apply open_rec_lc.
    apply lc_weaken with (k := 0); [lia | apply Hr].
  - assert (H1 : ~ In x (fv t1)) by (intro H; apply Hfresh; apply in_or_app; auto).
    assert (H2 : ~ In x (fv t2)) by (intro H; apply Hfresh; apply in_or_app; auto).
    rewrite (IHt1 k rho x u H1 Hr), (IHt2 k rho x u H2 Hr). reflexivity.
  - rewrite (IHt (S k) rho x u Hfresh Hr). reflexivity.
  - repeat rewrite in_app_iff in Hfresh.
    assert (H1 : ~ In x (fv t1)) by (intro H; apply Hfresh; tauto).
    assert (H2 : ~ In x (fv t2)) by (intro H; apply Hfresh; tauto).
    assert (H3 : ~ In x (fv t3)) by (intro H; apply Hfresh; tauto).
    rewrite (IHt1 k rho x u H1 Hr), (IHt2 k rho x u H2 Hr),
      (IHt3 k rho x u H3 Hr). reflexivity.
  - assert (H1 : ~ In x (fv t1)) by (intro H; apply Hfresh; apply in_or_app; auto).
    assert (H2 : ~ In x (fv t2)) by (intro H; apply Hfresh; apply in_or_app; auto).
    rewrite (IHt1 k rho x u H1 Hr), (IHt2 k rho x u H2 Hr). reflexivity.
Qed.

Lemma value_no_step : forall v t, value v -> v --> t -> False.
Proof. intros v t Hv Hs; inversion Hv; subst; inversion Hs. Qed.

Lemma multi_value : forall v w, value v -> v -->* w -> w = v.
Proof.
  intros v w Hv Hm; inversion Hm; subst; auto.
  exfalso. eapply value_no_step; eauto.
Qed.

Fixpoint reducible (T : ty) (t : tm) : Prop :=
  locally_closed t /\ strongly_normalizing t /\
  match T with
  | Ty_Bool => forall v, t -->* v -> value v -> v = tm_true \/ v = tm_false
  | Ty_Arrow A B => forall v, t -->* v -> value v ->
      exists body, v = tm_abs A body /\
        forall u, reducible A u -> reducible B (open body u)
  end.

Lemma red_lc : forall T t, reducible T t -> locally_closed t.
Proof. intros T t H; destruct T; simpl in H; tauto. Qed.

Lemma red_sn : forall T t, reducible T t -> strongly_normalizing t.
Proof. intros T t H; destruct T; simpl in H; tauto. Qed.

Lemma step_lc : forall t t', t --> t' -> locally_closed t -> locally_closed t'.
Proof.
  intros t t' Hs; induction Hs; intro Hlc; unfold locally_closed in *;
    inversion Hlc; subst;
    eauto using lc_at.
  - inversion H; subst. eapply lc_open; eauto.
Qed.

Lemma red_step : forall T t t', reducible T t -> t --> t' -> reducible T t'.
Proof.
  intros T t t' H Hstep.
  destruct T; simpl in *; destruct H as [Hlc [Hsn Hval]].
  - split. eapply step_lc; [exact Hstep | exact Hlc].
    split.
    + inversion Hsn; subst; auto.
    + intros v Hm Hv. apply Hval with (v := v);
        [eapply multi_step; [exact Hstep | exact Hm] | exact Hv].
  - split. eapply step_lc; [exact Hstep | exact Hlc].
    split.
    + inversion Hsn; subst; auto.
    + intros v Hm Hv. apply Hval with (v := v);
        [eapply multi_step; [exact Hstep | exact Hm] | exact Hv].
Qed.

Lemma red_after : forall T t,
  locally_closed t -> ~ value t ->
  (forall t', t --> t' -> reducible T t') -> reducible T t.
Proof.
  intros T t Hlc Hnv Hnext.
  destruct T; simpl; split; [exact Hlc | | exact Hlc |].
  - split.
    + constructor. intros t' Hs. apply red_sn with (T := Ty_Bool). auto.
    + intros v Hm Hv. inversion Hm; subst.
      * contradiction.
      * specialize (Hnext _ H). destruct (Hnext) as [_ [_ Hcanon]].
        apply Hcanon with (v := v); auto.
  - split.
    + constructor. intros t' Hs. apply red_sn with (T := Ty_Arrow T1 T2). auto.
    + intros v Hm Hv. inversion Hm; subst.
      * contradiction.
      * specialize (Hnext _ H). destruct (Hnext) as [_ [_ Hcanon]].
        apply Hcanon with (v := v); auto.
Qed.

Lemma red_true : reducible Ty_Bool tm_true.
Proof.
  simpl. split; [constructor|]. split.
  - constructor. intros t H. exfalso. exact (value_no_step tm_true t v_true H).
  - intros v Hm Hv. left. exact (multi_value tm_true v v_true Hm).
Qed.

Lemma red_false : reducible Ty_Bool tm_false.
Proof.
  simpl. split; [constructor|]. split.
  - constructor. intros t H. exfalso. exact (value_no_step tm_false t v_false H).
  - intros v Hm Hv. right. exact (multi_value tm_false v v_false Hm).
Qed.

Lemma red_abs : forall A B body,
  locally_closed (tm_abs A body) ->
  (forall u, reducible A u -> reducible B (open body u)) ->
  reducible (Ty_Arrow A B) (tm_abs A body).
Proof.
  intros A B body Hlc Hbody. simpl. split; [exact Hlc|]. split.
  - constructor. intros t H. exfalso.
    exact (value_no_step _ _ (v_abs _ _ Hlc) H).
  - intros v Hm Hv. pose proof (multi_value _ _ (v_abs _ _ Hlc) Hm) as E.
    subst. exists body. split; auto.
Qed.

Lemma red_choice : forall T a b,
  reducible T a -> reducible T b -> reducible T (tm_choice a b).
Proof.
  intros T a b Ha Hb. apply red_after.
  - constructor; [apply (red_lc _ _ Ha) | apply (red_lc _ _ Hb)].
  - intro H; inversion H.
  - intros t Hs; inversion Hs; subst; assumption.
Qed.

Lemma red_if : forall T c a b,
  reducible Ty_Bool c -> reducible T a -> reducible T b ->
  reducible T (tm_if c a b).
Proof.
  intros T c a b Hc Ha Hb.
  pose proof (red_sn _ _ Hc) as Hsn.
  revert Hc. induction Hsn as [c Hsteps IH]; intros Hc.
  apply red_after.
  - constructor; [apply (red_lc _ _ Hc) | apply (red_lc _ _ Ha) | apply (red_lc _ _ Hb)].
  - intro H; inversion H.
  - intros t Hs. inversion Hs; subst; auto.
    apply IH; [assumption | eapply red_step; eauto].
Qed.

Lemma red_app : forall A B f a,
  reducible (Ty_Arrow A B) f -> reducible A a ->
  reducible B (tm_app f a).
Proof.
  intros A B f a Hf Ha.
  pose proof (red_sn _ _ Hf) as Hsnf.
  revert a Hf Ha. induction Hsnf as [f Hfs IHf]; intros a Hf Ha.
  pose proof (red_sn _ _ Ha) as Hsna.
  revert Ha. induction Hsna as [a Has IHa]; intros Ha.
  apply red_after.
  - constructor; [apply (red_lc _ _ Hf) | apply (red_lc _ _ Ha)].
  - intro H; inversion H.
  - intros t Hs. inversion Hs; subst.
    + destruct Hf as [_ [_ Hcanon]].
      specialize (Hcanon (tm_abs T t0) (multi_refl _ _) (v_abs _ _ H1)).
      destruct Hcanon as [body [E Hbody]]. inversion E; subst.
      apply Hbody. exact Ha.
    + apply IHf; [assumption | eapply red_step; eauto | exact Ha].
    + apply IHa; [assumption | eapply red_step; eauto].
Qed.

Theorem fundamental : forall Gamma t T,
  has_type Gamma t T -> forall rho,
  (forall x, locally_closed (rho x)) ->
  (forall x U, Gamma x = Some U -> reducible U (rho x)) ->
  reducible T (subst rho t).
Proof.
  intros Gamma t T Hty; induction Hty; intros rho Hlc Henv; simpl.
  - apply Henv. exact H.
  - apply red_abs.
    + change (lc_at 0 (subst rho (tm_abs T1 t1))).
      apply lc_subst; auto.
      eapply typing_lc. eapply T_Abs with (L := L). exact H.
    + intros u Hu.
      set (x := fresh (L ++ fv t1)).
      assert (HnotL : ~ In x L).
      { intro Hx. pose proof (fresh_gt (L ++ fv t1) x (in_or_app _ _ _ (or_introl Hx))).
        unfold x in *. lia. }
      assert (Hnotfv : ~ In x (fv t1)).
      { intro Hx. pose proof (fresh_gt (L ++ fv t1) x (in_or_app _ _ _ (or_intror Hx))).
        unfold x in *. lia. }
      specialize (H0 x HnotL (fun y => if Nat.eqb x y then u else rho y)).
      assert (Hlc' : forall y, locally_closed (if Nat.eqb x y then u else rho y)).
      { intro y. destruct (Nat.eqb x y); [apply (red_lc _ _ Hu) | apply Hlc]. }
      specialize (H0 Hlc').
      assert (Henv' : forall y U,
        update Gamma x T1 y = Some U ->
        reducible U (if Nat.eqb x y then u else rho y)).
      { intros y U Hy. unfold update in Hy.
        destruct (Nat.eqb x y) eqn:E.
        - inversion Hy; subst. exact Hu.
        - apply Henv. exact Hy. }
      specialize (H0 Henv').
      change (reducible T2 (open_rec 0 u (subst rho t1))).
      rewrite <- (subst_open_rec t1 0 rho x u Hnotfv Hlc).
      exact H0.
  - apply red_app with (A := T1); auto.
  - exact red_true.
  - exact red_false.
  - apply red_if; auto.
  - apply red_choice; auto.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Hty.
  apply red_sn with (T := T).
  pose proof (fundamental empty t T Hty (fun x => tm_fvar x)) as Hfund.
  assert (Hlc : forall x, locally_closed (tm_fvar x)) by (intro x; constructor).
  specialize (Hfund Hlc).
  assert (Henv : forall x U, empty x = Some U -> reducible U (tm_fvar x)).
  { intros x U H; discriminate H. }
  specialize (Hfund Henv).
  assert (Hsubst : subst (fun x => tm_fvar x) t = t).
  { clear Hfund Hty. induction t; simpl; f_equal; auto. }
  rewrite Hsubst in Hfund. exact Hfund.
Qed.

End STLCNormalizationIfNondeterminismHardTask.
