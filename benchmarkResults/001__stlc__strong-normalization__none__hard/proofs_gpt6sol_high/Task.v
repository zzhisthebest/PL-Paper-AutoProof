(** STLC call-by-value strong-normalization benchmark.
    No if-then-else, non-determinism, or recursion is included. *)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Relations.Relation_Definitions.
From Stdlib Require Import Lia.

Module STLCNormalizationNoneHardTask.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
      R x y ->
      multi R y z ->
      multi R x z.

(** Language syntax, using locally nameless binders. *)

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
  | tm_false : tm.

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

(** Opening and local closure. *)

Fixpoint open_rec (k : nat) (u : tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => if Nat.eqb k i then u else tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_app t1 t2 => tm_app (open_rec k u t1) (open_rec k u t2)
  | tm_abs T t1 => tm_abs T (open_rec (S k) u t1)
  | tm_true => tm_true
  | tm_false => tm_false
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
      lc_at k tm_false.

Definition locally_closed (t : tm) : Prop := lc_at 0 t.

(** Call-by-value operational semantics. *)

Inductive value : tm -> Prop :=
  | v_abs : forall T t,
      locally_closed (tm_abs T t) ->
      value (tm_abs T t)
  | v_true :
      value tm_true
  | v_false :
      value tm_false.

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
where "t '-->' t'" := (step t t').

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

(** Typing rules. *)

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
where "<{ Gamma '|--' t '\in' T }>" := (has_type Gamma t T)
  : stlc_scope.

(** Target theorem: strong normalization for the supplied CBV relation. *)

Inductive strongly_normalizing : tm -> Prop :=
  | SN_intro : forall t,
      (forall t', t --> t' -> strongly_normalizing t') ->
      strongly_normalizing t.

(** Syntactic facts about opening and simultaneous substitution. *)

Fixpoint subst (rho : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => rho x
  | tm_app a b => tm_app (subst rho a) (subst rho b)
  | tm_abs T a => tm_abs T (subst rho a)
  | tm_true => tm_true
  | tm_false => tm_false
  end.

Fixpoint max_fv (t : tm) : nat :=
  match t with
  | tm_bvar _ => 0
  | tm_fvar x => x
  | tm_app a b => Nat.max (max_fv a) (max_fv b)
  | tm_abs _ a => max_fv a
  | _ => 0
  end.

Fixpoint fresh (x : atom) (t : tm) : Prop :=
  match t with
  | tm_bvar _ => True
  | tm_fvar y => x <> y
  | tm_app a b => fresh x a /\ fresh x b
  | tm_abs _ a => fresh x a
  | _ => True
  end.

Lemma fresh_above : forall t x, max_fv t < x -> fresh x t.
Proof.
  induction t; simpl; intros x H; try exact I.
  - lia.
  - split; [apply IHt1 | apply IHt2]; lia.
  - apply IHt; exact H.
Qed.

Lemma lc_mono : forall t k j, lc_at k t -> k <= j -> lc_at j t.
Proof.
  intros t k j H. revert j.
  induction H; intros j Hle.
  - apply lc_bvar. lia.
  - apply lc_fvar.
  - apply lc_app; eauto.
  - apply lc_abs. apply IHlc_at. lia.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma open_lc_at : forall t k u, lc_at k t -> open_rec k u t = t.
Proof.
  intros t k u H; induction H; simpl; try (f_equal; eauto); auto.
  assert (E : (k =? i) = false) by (apply Nat.eqb_neq; lia).
  rewrite E. reflexivity.
Qed.

Lemma subst_lc_at : forall t k rho,
  lc_at k t -> (forall x, locally_closed (rho x)) ->
  lc_at k (subst rho t).
Proof.
  intros t k rho H; revert rho.
  induction H; intros rho Hr; simpl.
  - apply lc_bvar; assumption.
  - apply lc_mono with (k := 0); [apply Hr | lia].
  - apply lc_app; auto.
  - apply lc_abs. auto.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma subst_lc : forall rho t,
  locally_closed t -> (forall x, locally_closed (rho x)) ->
  locally_closed (subst rho t).
Proof. intros rho t H Hr. eapply subst_lc_at; eauto. Qed.

Lemma open_inv : forall t k x,
  lc_at k (open_rec k (tm_fvar x) t) -> lc_at (S k) t.
Proof.
  induction t; intros k x H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply lc_bvar. apply Nat.eqb_eq in E. lia.
    + inversion H; subst. apply lc_bvar. lia.
  - apply lc_fvar.
  - inversion H; subst. apply lc_app; eauto.
  - inversion H; subst. apply lc_abs. eauto.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma not_in_above : forall (L : list nat) x,
  fold_right Nat.max 0 L < x -> ~ In x L.
Proof.
  induction L as [|a L IHL]; simpl; intros x H; intros Hin; simpl in Hin.
  - contradiction.
  - destruct Hin as [E | Hin].
    + subst x. pose proof (Nat.le_max_l a (fold_right Nat.max 0 L)). lia.
    + apply (IHL x); auto.
      pose proof (Nat.le_max_r a (fold_right Nat.max 0 L)). lia.
Qed.

Lemma typing_lc : forall Gamma t T,
  has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T H; induction H; simpl; try constructor; eauto.
  - apply open_inv with
      (x := S (fold_right Nat.max 0 L)).
    apply H0. apply not_in_above. lia.
Qed.

Definition put (rho : atom -> tm) (x : atom) (v : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then v else rho y.

Lemma subst_open_rec : forall t k rho x v,
  fresh x t -> (forall y, locally_closed (rho y)) ->
  subst (put rho x v) (open_rec k (tm_fvar x) t) =
  open_rec k v (subst rho t).
Proof.
  induction t; intros k rho x v Hf Hr; simpl in *; try reflexivity.
  - destruct (Nat.eqb k n); simpl; [unfold put; rewrite Nat.eqb_refl |];
      reflexivity.
  - unfold put. assert (E : (x =? a) = false)
      by (apply Nat.eqb_neq; exact Hf).
    rewrite E. symmetry. apply open_lc_at.
    apply lc_mono with (k := 0); [apply Hr | lia].
  - destruct Hf as [H1 H2].
    rewrite IHt1 by assumption. rewrite IHt2 by assumption.
    reflexivity.
  - rewrite IHt by assumption. reflexivity.
Qed.

Lemma subst_id : forall t, subst tm_fvar t = t.
Proof. induction t; simpl; try (f_equal; auto); reflexivity. Qed.

Lemma multi_trans : forall a b c,
  a -->* b -> b -->* c -> a -->* c.
Proof.
  intros a b c H. induction H; intros G; eauto using multi.
Qed.

Lemma multi_app1 : forall a b c,
  a -->* b -> locally_closed c -> tm_app a c -->* tm_app b c.
Proof.
  intros a b c H. induction H; intros Hc.
  - constructor.
  - eapply multi_step; [apply ST_App1; eauto | apply IHmulti; auto].
Qed.

Lemma multi_app2 : forall v a b,
  value v -> a -->* b -> tm_app v a -->* tm_app v b.
Proof.
  intros v a b Hv H. induction H.
  - constructor.
  - eapply multi_step; [apply ST_App2; eauto | exact IHmulti].
Qed.

Lemma value_lc : forall v, value v -> locally_closed v.
Proof.
  intros v H; inversion H; subst.
  - assumption.
  - apply lc_true.
  - apply lc_false.
Qed.

(** A type-indexed relation: each term reaches a semantic value. *)
Fixpoint interp (T : ty) (t : tm) : Prop :=
  match T with
  | Ty_Bool => locally_closed t /\
      exists v, t -->* v /\ value v
  | Ty_Arrow A B => locally_closed t /\
      exists v, t -->* v /\ value v /\
        (forall u, interp A u -> interp B (tm_app v u))
  end.

Lemma interp_lc : forall T t, interp T t -> locally_closed t.
Proof. destruct T; simpl; intros; tauto. Qed.

Lemma interp_back : forall T a b,
  locally_closed a -> a -->* b -> interp T b -> interp T a.
Proof.
  intros T a b Ha Hm. destruct T as [|A B]; simpl.
  - intros [_ [v [Hbv Hv]]]. split; auto.
    exists v. split; [eapply multi_trans; eauto | exact Hv].
  - intros [_ [v [Hbv [Hv Hsem]]]]. split; auto.
    exists v. repeat split; auto. eapply multi_trans; eauto.
Qed.

Lemma interp_witness : forall T t,
  interp T t -> exists v, t -->* v /\ value v /\ interp T v.
Proof.
  intros T t H. destruct T as [|A B]; simpl in *.
  - destruct H as [_ [v [Htv Hv]]].
    exists v. split; [exact Htv |]. split; [exact Hv |].
    split; [apply value_lc; auto | exists v; split; [constructor | exact Hv]].
  - destruct H as [_ [v [Htv [Hv Hsem]]]].
    exists v. split; [exact Htv |]. split; [exact Hv |].
    split; [apply value_lc; auto |].
    exists v. split; [constructor |]. split; assumption.
Qed.

Definition env_interp (Gamma : context) (rho : atom -> tm) : Prop :=
  (forall x, locally_closed (rho x)) /\
  (forall x T, Gamma x = Some T -> interp T (rho x)).

Lemma env_put : forall Gamma rho x A v,
  env_interp Gamma rho -> interp A v ->
  env_interp (update Gamma x A) (put rho x v).
Proof.
  intros Gamma rho x A v [Hlc Hsem] Hv. split.
  - intros y. unfold put. destruct (Nat.eqb x y) eqn:E.
    + apply interp_lc with (T := A). exact Hv.
    + apply Hlc.
  - intros y T Hy. unfold update in Hy. unfold put.
    destruct (Nat.eqb x y) eqn:E.
    + inversion Hy; subst. exact Hv.
    + apply Hsem. exact Hy.
Qed.

Theorem fundamental : forall Gamma t T,
  has_type Gamma t T ->
  forall rho, env_interp Gamma rho -> interp T (subst rho t).
Proof.
  intros Gamma t T Hty. induction Hty; intros rho Hr; simpl.
  - destruct Hr as [_ Hsem]. apply Hsem. exact H.
  - destruct Hr as [Hrho Hsem].
    assert (Habs : locally_closed (tm_abs T1 (subst rho t1))).
    { change (locally_closed (subst rho (tm_abs T1 t1))).
      apply subst_lc.
      - eapply typing_lc. apply T_Abs with (L := L). exact H.
      - exact Hrho. }
    simpl. split; [exact Habs |].
    exists (tm_abs T1 (subst rho t1)).
    split; [constructor |]. split; [apply v_abs; exact Habs |].
    intros u Hu.
    destruct (interp_witness T1 u Hu) as [v [Huv [Hvv Hvr]]].
    pose (x := S (Nat.max (fold_right Nat.max 0 L) (max_fv t1))).
    assert (HxL : ~ In x L).
    { apply not_in_above. unfold x.
      pose proof (Nat.le_max_l (fold_right Nat.max 0 L) (max_fv t1)). lia. }
    assert (Hxt : fresh x t1).
    { apply fresh_above. unfold x.
      pose proof (Nat.le_max_r (fold_right Nat.max 0 L) (max_fv t1)). lia. }
    assert (Hbody : interp T2 (open (subst rho t1) v)).
    { specialize (H0 x HxL (put rho x v)).
      assert (Henv : env_interp (update Gamma x T1) (put rho x v)).
      { apply env_put; [split; assumption | exact Hvr]. }
      specialize (H0 Henv).
      unfold open in *.
      rewrite subst_open_rec in H0 by assumption.
      exact H0. }
    eapply interp_back.
    + apply lc_app; [exact Habs | apply interp_lc with (T := T1); exact Hu].
    + eapply multi_trans.
      * apply multi_app2; [apply v_abs; exact Habs | exact Huv].
      * eapply multi_step; [apply ST_AppAbs; assumption | constructor].
    + exact Hbody.
  - specialize (IHHty1 rho Hr). specialize (IHHty2 rho Hr).
    simpl in IHHty1.
    destruct IHHty1 as [Hlc1 [v [Htv [Hv Hfun]]]].
    eapply interp_back.
    + apply lc_app; [exact Hlc1 | eapply interp_lc; eauto].
    + apply multi_app1; [exact Htv | eapply interp_lc; eauto].
    + apply Hfun. exact IHHty2.
  - split; [apply lc_true |].
    exists tm_true. split; [constructor | constructor].
  - split; [apply lc_false |].
    exists tm_false. split; [constructor | constructor].
Qed.

Lemma value_no_step : forall v t', value v -> v --> t' -> False.
Proof.
  intros v t' Hv Hs. inversion Hv; subst; inversion Hs.
Qed.

Lemma step_deterministic : forall t a b,
  t --> a -> t --> b -> a = b.
Proof.
  intros t a b H. generalize dependent b.
  induction H; intros b Hb; inversion Hb; subst;
    try reflexivity;
    try (exfalso; match goal with
         | Hlc : locally_closed (tm_abs ?T ?s),
           Hs : step (tm_abs ?T ?s) _ |- _ =>
             eapply (value_no_step (tm_abs T s));
             [apply v_abs; exact Hlc | exact Hs]
         end);
    try (exfalso; match goal with
         | Hv : value ?v, Hs : step ?v _ |- _ =>
             exact (value_no_step v _ Hv Hs)
         end);
    try solve [f_equal; eauto].
Qed.

Lemma multi_value_sn : forall t v,
  t -->* v -> value v -> strongly_normalizing t.
Proof.
  intros t v Hm. induction Hm; intros Hv.
  - constructor. intros t' Hs. exfalso. eapply value_no_step; eauto.
  - constructor. intros t' Hs.
    assert (y = t') by (eapply step_deterministic; eauto).
    subst. apply IHHm. exact Hv.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Hty.
  assert (Henv : env_interp empty tm_fvar).
  { split.
    - intros x. apply lc_fvar.
    - intros x U H. discriminate H. }
  pose proof (fundamental empty t T Hty tm_fvar Henv) as H.
  rewrite subst_id in H.
  destruct (interp_witness T t H) as [v [Htv [Hv _]]].
  eapply multi_value_sn; eauto.
Qed.

End STLCNormalizationNoneHardTask.
