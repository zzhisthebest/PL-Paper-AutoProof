(** STLC CBV strong-normalization benchmark, Medium variant.
    Features: if-nondeterminism. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Relations.Relation_Definitions Lia.
Import ListNotations.

Module STLCNormalizationIfNondeterminismMediumTask.

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

Definition term_substitution := atom -> tm.

Definition id_substitution : term_substitution :=
  fun x => tm_fvar x.

Definition subst_update
    (rho : term_substitution) (x : atom) (v : tm) : term_substitution :=
  fun y => if Nat.eqb x y then v else rho y.

Fixpoint msubst (rho : term_substitution) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => rho x
  | tm_app t1 t2 => tm_app (msubst rho t1) (msubst rho t2)
  | tm_abs T t1 => tm_abs T (msubst rho t1)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (msubst rho t1) (msubst rho t2) (msubst rho t3)
  | tm_choice t1 t2 => tm_choice (msubst rho t1) (msubst rho t2)
  end.

Definition proper_substitution (rho : term_substitution) : Prop :=
  forall x, locally_closed (rho x).

Fixpoint strong_value_relation (T : ty) (v : tm) : Prop :=
  value v /\
  match T with
  | Ty_Bool =>
      v = tm_true \/ v = tm_false
  | Ty_Arrow T1 T2 =>
      exists body,
        v = tm_abs T1 body /\
        forall arg,
          strong_value_relation T1 arg ->
          locally_closed (open body arg) /\
          strongly_normalizing (open body arg) /\
          forall result,
            open body arg -->* result ->
            value result ->
            strong_value_relation T2 result
  end.

Definition strong_expression_relation (T : ty) (t : tm) : Prop :=
  locally_closed t /\
  strongly_normalizing t /\
  forall v,
    t -->* v ->
    value v ->
    strong_value_relation T v.

Definition strong_related_substitution
    (Gamma : context) (rho : term_substitution) : Prop :=
  forall x T,
    Gamma x = Some T ->
    strong_value_relation T (rho x).

Lemma lc_at_weaken : forall t k j,
  lc_at k t -> k <= j -> lc_at j t.
Proof.
  intros t k j H. revert j.
  induction H; intros j Hj; eauto using lc_at.
  apply lc_bvar. lia.
  apply lc_abs. apply IHlc_at. lia.
Qed.

Lemma lc_open_inv : forall t k x,
  lc_at k (open_rec k (tm_fvar x) t) -> lc_at (S k) t.
Proof.
  induction t; intros k x H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. constructor. lia.
    + inversion H; subst. constructor. lia.
  - inversion H; subst; constructor.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - constructor.
  - constructor.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
Qed.

Lemma list_max_bound : forall L x,
  In x L -> x <= fold_right Nat.max 0 L.
Proof.
  induction L as [|a L IH]; simpl; intros x Hx.
  - contradiction.
  - destruct Hx as [->|Hx]; [lia|]. specialize (IH _ Hx). lia.
Qed.

Lemma fresh_notin : forall L,
  ~ In (S (fold_right Nat.max 0 L)) L.
Proof.
  intros L Hin. pose proof (list_max_bound L _ Hin). lia.
Qed.

Lemma typing_lc : forall Gamma t T,
  has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T H. unfold locally_closed.
  induction H; eauto using lc_at.
  - apply lc_abs.
    eapply lc_open_inv with (x := S (fold_right Nat.max 0 L)).
    apply H0. apply fresh_notin.
Qed.

Lemma value_lc : forall v, value v -> locally_closed v.
Proof. intros v H; inversion H; subst; unfold locally_closed; eauto using lc_at. Qed.

Lemma lc_open_rec : forall t k u,
  lc_at (S k) t -> locally_closed u -> lc_at k (open_rec k u t).
Proof.
  induction t; intros k u Ht Hu; simpl.
  - inversion Ht; subst. destruct (Nat.eqb k n) eqn:E.
    + apply lc_at_weaken with (k := 0); auto. lia.
    + apply lc_bvar. apply Nat.eqb_neq in E. lia.
  - constructor.
  - inversion Ht; subst; constructor; eauto.
  - inversion Ht; subst; constructor; eauto.
  - constructor.
  - constructor.
  - inversion Ht; subst; constructor; eauto.
  - inversion Ht; subst; constructor; eauto.
Qed.

Lemma step_lc : forall t t',
  locally_closed t -> t --> t' -> locally_closed t'.
Proof.
  intros t t' Hlc Hstep. revert Hlc.
  induction Hstep; intros Hlc; unfold locally_closed in *;
    inversion Hlc; subst; eauto using lc_at.
  - inversion H; subst. eapply lc_open_rec; eauto using value_lc.
Qed.

Lemma expr_step : forall T t t',
  strong_expression_relation T t -> t --> t' ->
  strong_expression_relation T t'.
Proof.
  intros T t t' [Hlc [Hsn Hrel]] Hstep.
  split. eapply step_lc; eauto.
  split.
  - inversion Hsn; subst; eauto.
  - intros v Hmulti Hv. apply Hrel; auto.
    eapply multi_step; eauto.
Qed.

Lemma expr_value : forall T v,
  strong_value_relation T v -> strong_expression_relation T v.
Proof.
  intros T v Hsv.
  assert (Hv : value v) by (destruct T; exact (proj1 Hsv)).
  split; [apply value_lc; assumption|].
  split.
  - constructor. intros t' Hstep. inversion Hv; subst; inversion Hstep.
  - intros w Hmulti Hw. inversion Hmulti; subst; auto.
    inversion Hv; subst; inversion H.
Qed.

Lemma choice_compat : forall T a b,
  strong_expression_relation T a ->
  strong_expression_relation T b ->
  strong_expression_relation T (tm_choice a b).
Proof.
  intros T a b Ha Hb.
  destruct Ha as [Hla [Hsa Hra]].
  destruct Hb as [Hlb [Hsb Hrb]].
  assert (Hsucc : forall u, tm_choice a b --> u -> strong_expression_relation T u).
  { intros u Hstep. inversion Hstep; subst.
    - exact (conj Hla (conj Hsa Hra)).
    - exact (conj Hlb (conj Hsb Hrb)). }
  split; [constructor; assumption|].
  split.
  - constructor. intros u Hu. destruct (Hsucc u Hu) as [_ [Hsn _]]. exact Hsn.
  - intros v Hmulti Hv. inversion Hmulti; subst.
    + inversion Hv.
    + destruct (Hsucc _ H) as [_ [_ Hrel]]. apply Hrel; auto.
Qed.

Lemma if_compat : forall T c a b,
  strong_expression_relation Ty_Bool c ->
  strong_expression_relation T a ->
  strong_expression_relation T b ->
  strong_expression_relation T (tm_if c a b).
Proof.
  intros T c a b Hc Ha Hb.
  destruct Hc as [Hlc [Hsn Hrel]].
  revert Hlc Hrel.
  induction Hsn as [c Hsteps IH]; intros Hlc Hrel.
  assert (Hc : strong_expression_relation Ty_Bool c).
  { split; [exact Hlc|]. split; [constructor; exact Hsteps|exact Hrel]. }
  assert (Hsucc : forall u, tm_if c a b --> u -> strong_expression_relation T u).
  { intros u Hstep. inversion Hstep; subst; auto.
    destruct (expr_step _ _ _ Hc H2) as [Hl [_ Hr]].
    eapply IH; eauto.
  }
  split; [constructor; [exact Hlc|apply Ha|apply Hb]|].
  split.
  - constructor. intros u Hu. destruct (Hsucc u Hu) as [_ [Hsu _]]. exact Hsu.
  - intros v Hmulti Hv. inversion Hmulti; subst.
    + inversion Hv.
    + destruct (Hsucc _ H) as [_ [_ Hr]]. apply Hr; auto.
Qed.

Lemma app_compat : forall A B f a,
  strong_expression_relation (Ty_Arrow A B) f ->
  strong_expression_relation A a ->
  strong_expression_relation B (tm_app f a).
Proof.
  intros A B f a Hf Ha.
  destruct Hf as [Hlf [Hsnf Hrf]].
  revert a Hlf Hrf Ha.
  induction Hsnf as [f Hstepf IHf]; intros a Hlf Hrf Ha.
  destruct Ha as [Hla [Hsna Hra]].
  revert Hla Hra.
  induction Hsna as [a Hstepa IHa]; intros Hla Hra.
  assert (Hf : strong_expression_relation (Ty_Arrow A B) f).
  { split; [exact Hlf|]. split; [constructor; exact Hstepf|exact Hrf]. }
  assert (Ha : strong_expression_relation A a).
  { split; [exact Hla|]. split; [constructor; exact Hstepa|exact Hra]. }
  assert (Hsucc : forall u, tm_app f a --> u -> strong_expression_relation B u).
  { intros u Hstep. inversion Hstep; subst.
    - specialize (Hrf _ (multi_refl _ _) (v_abs _ _ H1)).
      simpl in Hrf. destruct Hrf as [_ [body [Heq Hfun]]].
      inversion Heq; subst.
      specialize (Hra _ (multi_refl _ _) H3).
      destruct (Hfun _ Hra) as [Hlc [Hsn Hrel]].
      exact (conj Hlc (conj Hsn Hrel)).
    - destruct (expr_step _ _ _ Hf H1) as [Hl [_ Hr]].
      eapply IHf; eauto.
    - destruct (expr_step _ _ _ Ha H3) as [Hl [_ Hr]].
      eapply IHa; eauto.
  }
  split; [constructor; assumption|].
  split.
  - constructor. intros u Hu. destruct (Hsucc u Hu) as [_ [Hsu _]]. exact Hsu.
  - intros v Hmulti Hv. inversion Hmulti; subst.
    + inversion Hv.
    + destruct (Hsucc _ H) as [_ [_ Hr]]. apply Hr; auto.
Qed.

Fixpoint fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_app t1 t2 => fv t1 ++ fv t2
  | tm_abs _ t1 => fv t1
  | tm_true | tm_false => []
  | tm_if t1 t2 t3 => fv t1 ++ fv t2 ++ fv t3
  | tm_choice t1 t2 => fv t1 ++ fv t2
  end.

Lemma msubst_lc_at : forall t k rho,
  lc_at k t -> proper_substitution rho -> lc_at k (msubst rho t).
Proof.
  intros t k rho Hlc. revert rho.
  induction Hlc; intros rho Hproper; simpl; eauto using lc_at.
  - apply lc_at_weaken with (k := 0); [apply Hproper|lia].
Qed.

Lemma open_rec_lc : forall t k u,
  lc_at k t -> open_rec k u t = t.
Proof.
  induction t; intros k u Hlc; simpl; inversion Hlc; subst;
    try (f_equal; eauto).
  - assert (E : k <> n) by lia.
    apply Nat.eqb_neq in E. rewrite E. reflexivity.
Qed.

Lemma msubst_open_fresh : forall t k rho x v,
  ~ In x (fv t) -> proper_substitution rho ->
  msubst (subst_update rho x v) (open_rec k (tm_fvar x) t) =
  open_rec k v (msubst rho t).
Proof.
  induction t; intros k rho x v Hfresh Hproper; simpl in *.
  - destruct (Nat.eqb k n); simpl.
    + unfold subst_update. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - unfold subst_update. simpl in Hfresh.
    assert (x <> a) by (intro Heq; subst; apply Hfresh; auto).
    assert (E : Nat.eqb x a = false) by (apply Nat.eqb_neq; assumption).
    rewrite E.
    symmetry. apply open_rec_lc.
    apply lc_at_weaken with (k := 0); [apply Hproper|lia].
  - rewrite in_app_iff in Hfresh.
    assert (H1 : ~ In x (fv t1)) by tauto.
    assert (H2 : ~ In x (fv t2)) by tauto.
    rewrite (IHt1 _ _ _ _ H1 Hproper), (IHt2 _ _ _ _ H2 Hproper).
    reflexivity.
  - rewrite IHt; auto.
  - reflexivity.
  - reflexivity.
  - rewrite !in_app_iff in Hfresh.
    assert (H1 : ~ In x (fv t1)) by tauto.
    assert (H2 : ~ In x (fv t2)) by tauto.
    assert (H3 : ~ In x (fv t3)) by tauto.
    rewrite (IHt1 _ _ _ _ H1 Hproper), (IHt2 _ _ _ _ H2 Hproper),
      (IHt3 _ _ _ _ H3 Hproper). reflexivity.
  - rewrite in_app_iff in Hfresh.
    assert (H1 : ~ In x (fv t1)) by tauto.
    assert (H2 : ~ In x (fv t2)) by tauto.
    rewrite (IHt1 _ _ _ _ H1 Hproper), (IHt2 _ _ _ _ H2 Hproper).
    reflexivity.
Qed.

Lemma msubst_id : forall t,
  msubst id_substitution t = t.
Proof. induction t; simpl; f_equal; auto. Qed.

Lemma id_proper : proper_substitution id_substitution.
Proof. intros x. constructor. Qed.

Theorem fundamental : forall Gamma t T,
  has_type Gamma t T -> forall rho,
  proper_substitution rho ->
  strong_related_substitution Gamma rho ->
  strong_expression_relation T (msubst rho t).
Proof.
  intros Gamma t T Hty.
  induction Hty as
    [Gamma x T Hget
    |L Gamma A B body Hbody IHbody
    |Gamma f a A B Hf IHf Ha IHa
    |Gamma
    |Gamma
    |Gamma c a b T Hc IHc Ha IHa Hb IHb
    |Gamma a b T Ha IHa Hb IHb];
    intros rho Hproper Hrelated; simpl.
  - apply expr_value. apply Hrelated. exact Hget.
  - apply expr_value. simpl.
    assert (Hlcbody : lc_at 1 body).
    { pose proof (typing_lc _ _ _ (T_Abs L Gamma A B body Hbody)) as Hl.
      inversion Hl; subst; assumption. }
    assert (Hlcabs : locally_closed (tm_abs A (msubst rho body))).
    { constructor. eapply msubst_lc_at; eauto. }
    split; [apply v_abs; exact Hlcabs|].
    exists (msubst rho body). split; [reflexivity|].
    intros arg Harg.
    set (x := S (fold_right Nat.max 0 (L ++ fv body))).
    assert (Hx : ~ In x (L ++ fv body)) by (unfold x; apply fresh_notin).
    assert (HxL : ~ In x L).
    { intro Hin. apply Hx. apply in_or_app. left. exact Hin. }
    assert (HxBody : ~ In x (fv body)).
    { intro Hin. apply Hx. apply in_or_app. right. exact Hin. }
    assert (Hargv : value arg) by (destruct A; exact (proj1 Harg)).
    assert (Hproper' : proper_substitution (subst_update rho x arg)).
    { intros y. unfold subst_update.
      destruct (Nat.eqb x y); [apply value_lc; exact Hargv|apply Hproper]. }
    assert (Hrelated' : strong_related_substitution (update Gamma x A)
      (subst_update rho x arg)).
    { intros y U Hget'. unfold update in Hget'.
      unfold subst_update. destruct (Nat.eqb x y) eqn:E.
      - inversion Hget'; subst. exact Harg.
      - apply Hrelated. exact Hget'. }
    specialize (IHbody x HxL (subst_update rho x arg) Hproper' Hrelated').
    unfold open in IHbody.
    rewrite (msubst_open_fresh body 0 rho x arg HxBody Hproper) in IHbody.
    exact IHbody.
  - eapply app_compat; [apply IHf|apply IHa]; assumption.
  - apply expr_value. simpl. split; [constructor|left; reflexivity].
  - apply expr_value. simpl. split; [constructor|right; reflexivity].
  - eapply if_compat; [apply IHc|apply IHa|apply IHb]; assumption.
  - eapply choice_compat; [apply IHa|apply IHb]; assumption.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Hty.
  pose proof (fundamental _ _ _ Hty id_substitution id_proper) as Hfund.
  assert (Hrel : strong_related_substitution empty id_substitution).
  { intros x U Hlookup. discriminate Hlookup. }
  specialize (Hfund Hrel).
  rewrite msubst_id in Hfund.
  destruct Hfund as [_ [Hsn _]]. exact Hsn.
Qed.

End STLCNormalizationIfNondeterminismMediumTask.
