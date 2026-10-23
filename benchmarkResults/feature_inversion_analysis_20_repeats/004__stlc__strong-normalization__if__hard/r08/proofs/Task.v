(** STLC call-by-value strong-normalization benchmark task. *)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Relations.Relation_Definitions.
From Stdlib Require Import Lia.

Module STLCCBVNormalizationTask.

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
  | tm_false : tm
  | tm_if : tm -> tm -> tm -> tm.

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
Notation "'if' t1 'then' t2 'else' t3" :=
  (tm_if t1 t2 t3)
  (in custom stlc_tm at level 200,
   t1 custom stlc_tm,
   t2 custom stlc_tm,
   t3 custom stlc_tm at level 200,
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
  | tm_if t1 t2 t3 =>
      tm_if (open_rec k u t1) (open_rec k u t2) (open_rec k u t3)
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
      lc_at k t1 ->
      lc_at k t2 ->
      lc_at k t3 ->
      lc_at k (tm_if t1 t2 t3).

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
  | T_If : forall Gamma t1 t2 t3 T,
      <{ Gamma |-- $(t1) \in Bool }> ->
      <{ Gamma |-- $(t2) \in T }> ->
      <{ Gamma |-- $(t3) \in T }> ->
      <{ Gamma |-- $(tm_if t1 t2 t3) \in T }>
where "<{ Gamma '|--' t '\in' T }>" := (has_type Gamma t T)
  : stlc_scope.

(** Target theorem: strong normalization for the supplied CBV relation. *)

Inductive strongly_normalizing : tm -> Prop :=
  | SN_intro : forall t,
      (forall t', t --> t' -> strongly_normalizing t') ->
      strongly_normalizing t.

(** * Auxiliary lemmas towards strong normalization *)

(* ------------------------------------------------------------------ *)
(* Fresh names                                                        *)
(* ------------------------------------------------------------------ *)

Fixpoint max_list (l : list nat) : nat :=
  match l with
  | nil => 0
  | x :: xs => Nat.max x (max_list xs)
  end.

Lemma max_list_ub : forall (l : list nat) (x : nat),
  In x l -> x <= max_list l.
Proof.
  induction l as [| a l IH]; intros x Hx; simpl in *.
  - destruct Hx.
  - destruct Hx as [-> | Hx].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; eauto | apply Nat.le_max_r].
Qed.

Lemma fresh_exists : forall (l : list atom), exists x, ~ In x l.
Proof.
  intros l. exists (S (max_list l)). intros Hx.
  pose proof (max_list_ub l (S (max_list l)) Hx) as Hle.
  exact (Nat.nle_succ_diag_l _ Hle).
Qed.

(* ------------------------------------------------------------------ *)
(* Free variables                                                     *)
(* ------------------------------------------------------------------ *)

Fixpoint fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ => nil
  | tm_fvar x => x :: nil
  | tm_app t1 t2 => fv t1 ++ fv t2
  | tm_abs _ t1 => fv t1
  | tm_true => nil
  | tm_false => nil
  | tm_if t1 t2 t3 => fv t1 ++ fv t2 ++ fv t3
  end.

(* ------------------------------------------------------------------ *)
(* Local closure lemmas                                               *)
(* ------------------------------------------------------------------ *)

Lemma lc_at_weaken : forall k k' t,
  k <= k' -> lc_at k t -> lc_at k' t.
Proof.
  intros k k' t Hle H. revert k' Hle.
  induction H; intros k' Hle.
  - apply lc_bvar. lia.
  - apply lc_fvar.
  - apply lc_app; auto.
  - apply lc_abs. apply IHlc_at. lia.
  - apply lc_true.
  - apply lc_false.
  - apply lc_if; auto.
Qed.

Lemma lc_at_app_inv : forall k t1 t2,
  lc_at k (tm_app t1 t2) -> lc_at k t1 /\ lc_at k t2.
Proof. intros k t1 t2 H. inversion H; auto. Qed.

Lemma lc_at_if_inv : forall k t1 t2 t3,
  lc_at k (tm_if t1 t2 t3) -> lc_at k t1 /\ lc_at k t2 /\ lc_at k t3.
Proof. intros k t1 t2 t3 H. inversion H; auto. Qed.

Lemma lc_at_abs_inv : forall k T t,
  lc_at k (tm_abs T t) -> lc_at (S k) t.
Proof. intros k T t H. inversion H; auto. Qed.

Lemma lc_at_bvar_inv : forall k n,
  lc_at k (tm_bvar n) -> n < k.
Proof. intros k n H. inversion H; auto. Qed.

Lemma lc_open_rec : forall k t u,
  lc_at (S k) t -> lc_at k u -> lc_at k (open_rec k u t).
Proof.
  intros k t. revert k. induction t; intros k u Ht Hu; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. exact Hu.
    + apply Nat.eqb_neq in E.
      apply lc_bvar. apply lc_at_bvar_inv in Ht. lia.
  - apply lc_fvar.
  - apply lc_at_app_inv in Ht as [H1 H2].
    apply lc_app; [apply IHt1; auto | apply IHt2; auto].
  - apply lc_abs. apply IHt with (k := S k) (u := u).
    + apply lc_at_abs_inv in Ht. exact Ht.
    + apply lc_at_weaken with (k := k); [lia | exact Hu].
  - apply lc_true.
  - apply lc_false.
  - apply lc_at_if_inv in Ht as [H1 [H2 H3]].
    apply lc_if; auto.
Qed.

Lemma lc_open_rec_inv : forall k j t u,
  j <= k -> lc_at k (open_rec j u t) -> lc_at k u -> lc_at (S k) t.
Proof.
  intros k j t. revert k j. induction t; intros k j u Hjk Hop Hu; simpl in *.
  - destruct (Nat.eqb j n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. apply lc_bvar. lia.
    + apply Nat.eqb_neq in E. apply lc_bvar.
      apply lc_at_bvar_inv in Hop. lia.
  - apply lc_fvar.
  - apply lc_at_app_inv in Hop as [H1 H2].
    apply lc_app.
    + apply IHt1 with (j := j) (u := u); [exact Hjk | exact H1 | exact Hu].
    + apply IHt2 with (j := j) (u := u); [exact Hjk | exact H2 | exact Hu].
  - apply lc_abs.
    apply IHt with (k := S k) (j := S j) (u := u).
    + lia.
    + apply lc_at_abs_inv in Hop. exact Hop.
    + apply lc_at_weaken with (k := k); [lia | exact Hu].
  - apply lc_true.
  - apply lc_false.
  - apply lc_at_if_inv in Hop as [H1 [H2 H3]].
    apply lc_if.
    + apply IHt1 with (j := j) (u := u); [exact Hjk | exact H1 | exact Hu].
    + apply IHt2 with (j := j) (u := u); [exact Hjk | exact H2 | exact Hu].
    + apply IHt3 with (j := j) (u := u); [exact Hjk | exact H3 | exact Hu].
Qed.

Lemma lc_open_rec_id : forall k u t,
  lc_at k t -> open_rec k u t = t.
Proof.
  intros k u t. revert k. induction t; intros k H; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E.
      apply lc_at_bvar_inv in H. lia.
    + reflexivity.
  - reflexivity.
  - apply lc_at_app_inv in H as [H1 H2].
    rewrite IHt1; auto. rewrite IHt2; auto.
  - f_equal. apply IHt. apply lc_at_abs_inv in H. exact H.
  - reflexivity.
  - reflexivity.
  - apply lc_at_if_inv in H as [H1 [H2 H3]].
    rewrite IHt1; auto. rewrite IHt2; auto. rewrite IHt3; auto.
Qed.

(* ------------------------------------------------------------------ *)
(* Free-variable substitution                                         *)
(* ------------------------------------------------------------------ *)

Fixpoint subst_tm (rho : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => rho x
  | tm_app t1 t2 => tm_app (subst_tm rho t1) (subst_tm rho t2)
  | tm_abs T t1 => tm_abs T (subst_tm rho t1)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 =>
      tm_if (subst_tm rho t1) (subst_tm rho t2) (subst_tm rho t3)
  end.

Definition extend_rho (rho : atom -> tm) (x : atom) (v : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then v else rho y.

Lemma extend_rho_same : forall rho x v,
  extend_rho rho x v x = v.
Proof. intros. unfold extend_rho. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma extend_rho_other : forall rho x v y,
  y <> x -> extend_rho rho x v y = rho y.
Proof.
  intros. unfold extend_rho.
  destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E. exfalso. auto.
  - reflexivity.
Qed.

Lemma extend_rho_lc : forall rho x v,
  (forall y, locally_closed (rho y)) ->
  locally_closed v ->
  forall y, locally_closed (extend_rho rho x v y).
Proof.
  intros rho x v Hrho Hv y. unfold extend_rho.
  destruct (Nat.eqb x y); auto.
Qed.

Lemma update_same : forall Gamma x T,
  update Gamma x T x = Some T.
Proof. intros. unfold update. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma update_other : forall Gamma x y T,
  y <> x -> update Gamma x T y = Gamma y.
Proof.
  intros. unfold update.
  destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E. exfalso. auto.
  - reflexivity.
Qed.

Lemma subst_lc_at : forall rho k t,
  lc_at k t ->
  (forall x, lc_at k (rho x)) ->
  lc_at k (subst_tm rho t).
Proof.
  intros rho k t. revert k. induction t; intros k Ht Hrho; simpl.
  - apply lc_at_bvar_inv in Ht. apply lc_bvar. exact Ht.
  - apply Hrho.
  - apply lc_at_app_inv in Ht as [H1 H2].
    apply lc_app; [apply IHt1; auto | apply IHt2; auto].
  - apply lc_abs. apply lc_at_abs_inv in Ht.
    apply IHt with (k := S k).
    + exact Ht.
    + intros x. apply lc_at_weaken with (k := k); [lia | apply Hrho].
  - apply lc_true.
  - apply lc_false.
  - apply lc_at_if_inv in Ht as [H1 [H2 H3]].
    apply lc_if; auto.
Qed.

Lemma subst_lc : forall rho t,
  locally_closed t ->
  (forall x, locally_closed (rho x)) ->
  locally_closed (subst_tm rho t).
Proof. intros. apply subst_lc_at with (k := 0); auto. Qed.

Lemma subst_ext : forall t rho1 rho2,
  (forall x, In x (fv t) -> rho1 x = rho2 x) ->
  subst_tm rho1 t = subst_tm rho2 t.
Proof.
  induction t; intros rho1 rho2 Hagree; simpl.
  - reflexivity.
  - apply Hagree. simpl. auto.
  - f_equal.
    + apply IHt1. intros x Hx. apply Hagree.
      apply in_app_iff. left. exact Hx.
    + apply IHt2. intros x Hx. apply Hagree.
      apply in_app_iff. right. exact Hx.
  - f_equal. apply IHt. intros x Hx. apply Hagree. exact Hx.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + apply IHt1. intros x Hx. apply Hagree.
      apply in_app_iff. left. exact Hx.
    + apply IHt2. intros x Hx. apply Hagree.
      apply in_app_iff. right. apply in_app_iff. left. exact Hx.
    + apply IHt3. intros x Hx. apply Hagree.
      apply in_app_iff. right. apply in_app_iff. right. exact Hx.
Qed.

Lemma subst_open_rec : forall rho,
  (forall x, locally_closed (rho x)) ->
  forall k u t,
    subst_tm rho (open_rec k u t) =
    open_rec k (subst_tm rho u) (subst_tm rho t).
Proof.
  intros rho Hrho k u t. revert k u. induction t; intros k u; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - rewrite lc_open_rec_id with (k := k) (u := subst_tm rho u).
    + reflexivity.
    + apply lc_at_weaken with (k := 0); [lia | apply Hrho].
  - f_equal; [apply IHt1 | apply IHt2].
  - f_equal. apply IHt.
  - reflexivity.
  - reflexivity.
  - f_equal; [apply IHt1 | apply IHt2 | apply IHt3].
Qed.

Lemma subst_open : forall rho,
  (forall x, locally_closed (rho x)) ->
  forall t u,
    subst_tm rho (open t u) = open (subst_tm rho t) (subst_tm rho u).
Proof. intros. apply subst_open_rec; auto. Qed.

Lemma subst_open_fvar : forall rho,
  (forall x, locally_closed (rho x)) ->
  forall t x,
    subst_tm rho (open t (tm_fvar x)) = open (subst_tm rho t) (rho x).
Proof.
  intros rho Hrho t x.
  rewrite (subst_open rho Hrho t (tm_fvar x)).
  reflexivity.
Qed.

Lemma subst_open_update : forall rho x v,
  (forall y, locally_closed (rho y)) ->
  locally_closed v ->
  forall t,
    ~ In x (fv t) ->
    subst_tm (extend_rho rho x v) (open t (tm_fvar x)) =
    open (subst_tm rho t) v.
Proof.
  intros rho x v Hrho Hv t Hfresh.
  rewrite subst_open_fvar.
  - rewrite extend_rho_same.
    assert (Hext : forall y, In y (fv t) -> extend_rho rho x v y = rho y).
    { intros y Hy. apply extend_rho_other. intro Heq. subst y.
      apply Hfresh. exact Hy. }
    rewrite (subst_ext t (extend_rho rho x v) rho Hext). reflexivity.
  - apply extend_rho_lc; auto.
Qed.

Lemma subst_identity : forall t,
  subst_tm tm_fvar t = t.
Proof.
  induction t; simpl; auto.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
Qed.

(* ------------------------------------------------------------------ *)
(* Values and steps                                                   *)
(* ------------------------------------------------------------------ *)

Lemma value_lc : forall t,
  value t -> locally_closed t.
Proof. intros t H. inversion H; subst; auto. apply lc_true. apply lc_false. Qed.

Lemma step_abs_inv : forall T t t',
  ~ step (tm_abs T t) t'.
Proof. intros T t t' H. inversion H. Qed.

Lemma step_true_inv : forall t',
  ~ step tm_true t'.
Proof. intros t' H. inversion H. Qed.

Lemma step_false_inv : forall t',
  ~ step tm_false t'.
Proof. intros t' H. inversion H. Qed.

Lemma value_SN : forall t,
  value t -> strongly_normalizing t.
Proof.
  intros t H. apply SN_intro. intros t' Hs.
  destruct H as [T body Hlc | |].
  - exfalso. eapply step_abs_inv; eauto.
  - exfalso. eapply step_true_inv; eauto.
  - exfalso. eapply step_false_inv; eauto.
Qed.

Lemma SN_step : forall t,
  strongly_normalizing t -> forall t', step t t' -> strongly_normalizing t'.
Proof.
  intros t H. induction H as [t Hsucc]. intros t' Hs.
  apply Hsucc. exact Hs.
Qed.

Lemma step_lc_fwd : forall t t',
  step t t' -> locally_closed t -> locally_closed t'.
Proof.
  intros t t' H.
  induction H as [T body v Hlcabs Hv
                 | a a' b Hstep IH1 Hlcb
                 | v1 b b' Hv1 Hstep IH2
                 | c1 c2 Hlc1 Hlc2
                 | c1 c2 Hlc1 Hlc2
                 | c1 c1' c2 c3 Hstep IH3 Hlc2 Hlc3];
    intros Hlc.
  - (* ST_AppAbs *) apply lc_open_rec with (k := 0).
    + apply lc_at_abs_inv in Hlcabs. exact Hlcabs.
    + apply value_lc; auto.
  - (* ST_App1 *) apply lc_at_app_inv in Hlc as [H1 H2].
    apply lc_app; [apply IH1; exact H1 | exact Hlcb].
  - (* ST_App2 *) apply lc_at_app_inv in Hlc as [H1 H2].
    apply lc_app; [apply value_lc; auto | apply IH2; exact H2].
  - (* ST_IfTrue *) apply lc_at_if_inv in Hlc as [H1 [H2 H3]]. exact H2.
  - (* ST_IfFalse *) apply lc_at_if_inv in Hlc as [H1 [H2 H3]]. exact H3.
  - (* ST_If *) apply lc_at_if_inv in Hlc as [H1 [H2 H3]].
    apply lc_if; [apply IH3; exact H1 | exact Hlc2 | exact Hlc3].
Qed.

Lemma step_lc_back : forall t t',
  step t t' -> locally_closed t' -> locally_closed t.
Proof.
  intros t t' H.
  induction H as [T body v Hlcabs Hv
                 | a a' b Hstep IH1 Hlcb
                 | v1 b b' Hv1 Hstep IH2
                 | c1 c2 Hlc1 Hlc2
                 | c1 c2 Hlc1 Hlc2
                 | c1 c1' c2 c3 Hstep IH3 Hlc2 Hlc3];
    intros Hlc.
  - (* ST_AppAbs *) apply lc_app; [exact Hlcabs | apply value_lc; auto].
  - (* ST_App1 *) apply lc_at_app_inv in Hlc as [H1 H2].
    apply lc_app; [apply IH1; exact H1 | exact Hlcb].
  - (* ST_App2 *) apply lc_at_app_inv in Hlc as [H1 H2].
    apply lc_app; [apply value_lc; auto | apply IH2; exact H2].
  - (* ST_IfTrue *) apply lc_if; [apply lc_true | exact Hlc1 | exact Hlc2].
  - (* ST_IfFalse *) apply lc_if; [apply lc_false | exact Hlc1 | exact Hlc2].
  - (* ST_If *) apply lc_at_if_inv in Hlc as [H1 [H2 H3]].
    apply lc_if; [apply IH3; exact H1 | exact Hlc2 | exact Hlc3].
Qed.

Lemma value_no_step : forall v,
  value v -> forall v', ~ step v v'.
Proof.
  intros v Hv. destruct Hv as [T body Hlc | |].
  - apply step_abs_inv.
  - apply step_true_inv.
  - apply step_false_inv.
Qed.

Lemma step_det : forall t t1,
  step t t1 -> forall u, step t u -> t1 = u.
Proof.
  intros t t1 H.
  induction H as [T body v Hlcabs Hv
                 | a a' b Hstep IH1 Hlcb
                 | v1 b b' Hv1 Hstep IH2
                 | c1 c2 Hlc1 Hlc2
                 | c1 c2 Hlc1 Hlc2
                 | c1 c1' c2 c3 Hstep IH3 Hlc2 Hlc3];
    intros u Hu; inversion Hu; subst.
  - reflexivity.
  - exfalso. exact (step_abs_inv T body t1' H1).
  - exfalso. exact (value_no_step v Hv t2' H3).
  - exfalso. exact (step_abs_inv T t a' Hstep).
  - f_equal. apply IH1. exact H1.
  - exfalso. exact (value_no_step a H1 a' Hstep).
  - exfalso. exact (value_no_step b H3 b' Hstep).
  - exfalso. exact (value_no_step v1 Hv1 t1' H1).
  - f_equal. apply IH2. exact H3.
  - reflexivity.
  - exfalso. exact (step_true_inv t1' H2).
  - reflexivity.
  - exfalso. exact (step_false_inv t1' H2).
  - exfalso. exact (step_true_inv c1' Hstep).
  - exfalso. exact (step_false_inv c1' Hstep).
  - f_equal. apply IH3. exact H2.
Qed.


(* ------------------------------------------------------------------ *)
(* A constructive trichotomy: a locally closed term is a value, steps, *)
(* or is stuck.                                                       *)
(* ------------------------------------------------------------------ *)

Lemma step_app_stuck_fun : forall a b t',
  ~ value a ->
  ~ (exists a', step a a') ->
  ~ step (tm_app a b) t'.
Proof.
  intros a b t' Hnva Hnsa Hs. inversion Hs; subst.
  - apply Hnva. apply v_abs. assumption.
  - exfalso. apply Hnsa. eexists. eassumption.
  - apply Hnva. assumption.
Qed.

Lemma step_app_abs_stuck : forall T body b t',
  locally_closed (tm_abs T body) ->
  ~ value b ->
  ~ (exists b', step b b') ->
  ~ step (tm_app (tm_abs T body) b) t'.
Proof.
  intros T body b t' Hlc Hnvb Hnsb Hs. inversion Hs; subst.
  - apply Hnvb. assumption.
  - exfalso. eapply step_abs_inv. eassumption.
  - exfalso. apply Hnsb. eexists. eassumption.
Qed.

Lemma step_app_val_stuck_arg : forall a b t',
  value a ->
  ~ value b ->
  ~ (exists b', step b b') ->
  ~ step (tm_app a b) t'.
Proof.
  intros a b t' Hva Hnvb Hnsb Hs. inversion Hs; subst.
  - apply Hnvb. assumption.
  - exfalso. eapply value_no_step; eassumption.
  - exfalso. apply Hnsb. eexists. eassumption.
Qed.

Lemma step_app_true_val_stuck : forall b t',
  value b -> ~ step (tm_app tm_true b) t'.
Proof.
  intros b t' Hvb Hs. inversion Hs; subst.
  - exfalso. eapply step_true_inv. eassumption.
  - exfalso. eapply value_no_step with (v := b); [exact Hvb | eassumption].
Qed.

Lemma step_app_false_val_stuck : forall b t',
  value b -> ~ step (tm_app tm_false b) t'.
Proof.
  intros b t' Hvb Hs. inversion Hs; subst.
  - exfalso. eapply step_false_inv. eassumption.
  - exfalso. eapply value_no_step with (v := b); [exact Hvb | eassumption].
Qed.

Lemma step_if_stuck_fun : forall a b c t',
  ~ value a ->
  ~ (exists a', step a a') ->
  ~ step (tm_if a b c) t'.
Proof.
  intros a b c t' Hnva Hnsa Hs. inversion Hs; subst.
  - apply Hnva. apply v_true.
  - apply Hnva. apply v_false.
  - exfalso. apply Hnsa. eexists. eassumption.
Qed.

Lemma step_if_abs_stuck : forall T body b c t',
  ~ step (tm_if (tm_abs T body) b c) t'.
Proof.
  intros T body b c t' Hs. inversion Hs; subst.
  - exfalso. eapply step_abs_inv. eassumption.
Qed.

Lemma step_trichotomy : forall t,
  locally_closed t ->
  value t \/ (exists t', step t t') \/ (~ value t /\ ~ (exists t', step t t')).
Proof.
  induction t as [n | x | a IHa b IHb | T body IHbody | | | c1 IHc1 c2 IHc2 c3 IHc3];
    intros Hlc.
  - (* bvar *) exfalso. apply lc_at_bvar_inv in Hlc. lia.
  - (* fvar *)
    right; right; split.
    + intros Hv; inversion Hv.
    + intros [t' Hs]; inversion Hs.
  - (* app *)
    apply lc_at_app_inv in Hlc as [Hla Hlb].
    destruct (IHa Hla) as [Hva | [[a' Hsa] | [Hnva Hnsa]]].
    + destruct a as [n0 | x0 | a1 a2 | T0 body0 | | | a1 a2 a3];
        try solve [exfalso; inversion Hva].
      * (* a = abs T0 body0 *)
        destruct (IHb Hlb) as [Hvb | [[b' Hsb] | [Hnvb Hnsb]]].
        -- right; left; exists (open body0 b). apply ST_AppAbs; assumption.
        -- right; left; exists (tm_app (tm_abs T0 body0) b').
           apply ST_App2; [apply v_abs; assumption | assumption].
        -- right; right; split.
           ++ intros Hv; inversion Hv.
           ++ intros [t' Hs]. exact (step_app_abs_stuck T0 body0 b t' Hla Hnvb Hnsb Hs).
      * (* a = true *)
        destruct (IHb Hlb) as [Hvb | [[b' Hsb] | [Hnvb Hnsb]]].
        -- right; right; split.
           ++ intros Hv; inversion Hv.
           ++ intros [t' Hs]. exact (step_app_true_val_stuck b t' Hvb Hs).
        -- right; left; exists (tm_app tm_true b'). apply ST_App2; [apply v_true | assumption].
        -- right; right; split.
           ++ intros Hv; inversion Hv.
           ++ intros [t' Hs]. exact (step_app_val_stuck_arg tm_true b t' v_true Hnvb Hnsb Hs).
      * (* a = false *)
        destruct (IHb Hlb) as [Hvb | [[b' Hsb] | [Hnvb Hnsb]]].
        -- right; right; split.
           ++ intros Hv; inversion Hv.
           ++ intros [t' Hs]. exact (step_app_false_val_stuck b t' Hvb Hs).
        -- right; left; exists (tm_app tm_false b'). apply ST_App2; [apply v_false | assumption].
        -- right; right; split.
           ++ intros Hv; inversion Hv.
           ++ intros [t' Hs]. exact (step_app_val_stuck_arg tm_false b t' v_false Hnvb Hnsb Hs).
    + (* a steps *)
      right; left; exists (tm_app a' b). apply ST_App1; assumption.
    + (* a stuck *)
      right; right; split.
      * intros Hv; inversion Hv.
      * intros [t' Hs]. exact (step_app_stuck_fun a b t' Hnva Hnsa Hs).
  - (* abs *) left. apply v_abs. assumption.
  - (* true *) left. apply v_true.
  - (* false *) left. apply v_false.
  - (* if *)
    apply lc_at_if_inv in Hlc as [Hl1 [Hl2 Hl3]].
    destruct (IHc1 Hl1) as [Hv1 | [[c1' Hs1] | [Hnv1 Hns1]]].
    + destruct c1 as [n0 | x0 | a1 a2 | T0 body0 | | | a1 a2 a3];
        try solve [exfalso; inversion Hv1].
      * (* abs *) right; right; split.
        -- intros Hv; inversion Hv.
        -- intros [t' Hs]. exact (step_if_abs_stuck T0 body0 c2 c3 t' Hs).
      * (* true *) right; left; exists c2. apply ST_IfTrue; assumption.
      * (* false *) right; left; exists c3. apply ST_IfFalse; assumption.
    + right; left; exists (tm_if c1' c2 c3). apply ST_If; assumption.
    + right; right; split.
      * intros Hv; inversion Hv.
      * intros [t' Hs]. exact (step_if_stuck_fun c1 c2 c3 t' Hnv1 Hns1 Hs).
Qed.


(* ------------------------------------------------------------------ *)
(* The type-indexed logical relation                                   *)
(* ------------------------------------------------------------------ *)

Fixpoint R (T : ty) : tm -> Prop :=
  match T with
  | Ty_Bool => fun t => locally_closed t /\ strongly_normalizing t
  | Ty_Arrow T1 T2 =>
      fun t => locally_closed t /\ strongly_normalizing t /\
               (forall t2, R T1 t2 -> R T2 (tm_app t t2))
  end.

Definition ctx_ok (Gamma : context) (rho : atom -> tm) : Prop :=
  (forall x T, Gamma x = Some T -> R T (rho x)) /\
  (forall x, locally_closed (rho x)).

Lemma R_lc : forall T t,
  R T t -> locally_closed t.
Proof.
  induction T as [| T1 IH1 T2 IH2]; intros t H; simpl in H; tauto.
Qed.

Lemma R_sn : forall T t,
  R T t -> strongly_normalizing t.
Proof.
  induction T as [| T1 IH1 T2 IH2]; intros t H; simpl in H; tauto.
Qed.

Lemma R_step : forall T t t',
  R T t -> step t t' -> R T t'.
Proof.
  induction T as [| T1 IH1 T2 IH2]; intros t t' HR Hstep.
  - simpl in HR. simpl. destruct HR as [Hlc Hsn]. split.
    + apply step_lc_fwd with (t := t); assumption.
    + apply SN_step with (t := t); assumption.
  - simpl in HR. simpl. destruct HR as [Hlc [Hsn Happ]]. split.
    + apply step_lc_fwd with (t := t); assumption.
    + split.
      * apply SN_step with (t := t); assumption.
      * intros t2 HR2.
        apply (IH2 (tm_app t t2) (tm_app t' t2)).
        -- apply Happ. assumption.
        -- apply ST_App1; [assumption | apply R_lc with (T := T1); assumption].
Qed.

Lemma R_expand : forall T t t',
  step t t' -> R T t' -> R T t.
Proof.
  induction T as [| T1 IH1 T2 IH2]; intros t t' Hstep HR.
  - simpl in HR. simpl. destruct HR as [Hlc Hsn]. split.
    + apply step_lc_back with (t' := t'); assumption.
    + apply SN_intro. intros u Hu.
      assert (Heq : t' = u) by (eapply step_det; eauto).
      rewrite <- Heq. assumption.
  - simpl in HR. simpl. destruct HR as [Hlc [Hsn Happ]]. split.
    + apply step_lc_back with (t' := t'); assumption.
    + split.
      * apply SN_intro. intros u Hu.
        assert (Heq : t' = u) by (eapply step_det; eauto).
        rewrite <- Heq. assumption.
      * intros t2 HR2.
        apply (IH2 (tm_app t t2) (tm_app t' t2)).
        -- apply ST_App1; [assumption | apply R_lc with (T := T1); assumption].
        -- apply Happ. assumption.
Qed.

(* Every locally closed, stuck, non-value term is in the relation. *)
Lemma R_stuck : forall T t,
  locally_closed t ->
  ~ (exists t', step t t') ->
  ~ value t ->
  R T t.
Proof.
  induction T as [| T1 IH1 T2 IH2]; intros t Hlc Hns Hnv.
  - simpl. split; [assumption |].
    apply SN_intro. intros t' Hs.
    exfalso. apply Hns. eexists. eassumption.
  - simpl. split; [assumption |]. split.
    + apply SN_intro. intros t' Hs.
      exfalso. apply Hns. eexists. eassumption.
    + intros t2 HR2.
      apply IH2.
      * apply lc_app; [assumption | apply R_lc with (T := T1); assumption].
      * intros [t' Hs]. inversion Hs; subst.
        -- exfalso. apply Hnv. apply v_abs. assumption.
        -- exfalso. apply Hns. eexists. eassumption.
        -- exfalso. apply Hnv. assumption.
      * intros Hv; inversion Hv.
Qed.

(* Beta-expansion: an application of an abstraction to any related
   argument is related.  The proof evaluates the argument (which is SN)
   and uses the value-level hypothesis supplied by the caller. *)
Lemma R_app_abs_aux : forall T1 T2 s,
  locally_closed (tm_abs T1 s) ->
  (forall v, value v -> R T1 v -> R T2 (open s v)) ->
  forall t2, strongly_normalizing t2 -> R T1 t2 -> R T2 (tm_app (tm_abs T1 s) t2).
Proof.
  intros T1 T2 s Hlcabs Hsub t2 Hsn.
  induction Hsn as [t2 Hstep IH].
  intros HR2.
  destruct (step_trichotomy t2 (R_lc T1 t2 HR2)) as [Hv | [[t2' Hs] | [Hnv Hns]]].
  - (* t2 is a value: beta step *)
    apply R_expand with (t' := open s t2).
    + apply ST_AppAbs; assumption.
    + apply Hsub; assumption.
  - (* t2 steps *)
    apply R_expand with (t' := tm_app (tm_abs T1 s) t2').
    + apply ST_App2; [apply v_abs; assumption | assumption].
    + apply (IH t2' Hs). apply R_step with (t := t2); assumption.
  - (* t2 is stuck *)
    apply R_stuck.
    + apply lc_app; [assumption | apply R_lc with (T := T1); assumption].
    + intros [t' Hs']. exact (step_app_abs_stuck T1 s t2 t' Hlcabs Hnv Hns Hs').
    + intros Hv; inversion Hv.
Qed.

Lemma R_app_abs : forall T1 T2 s,
  locally_closed (tm_abs T1 s) ->
  (forall v, value v -> R T1 v -> R T2 (open s v)) ->
  forall t2, R T1 t2 -> R T2 (tm_app (tm_abs T1 s) t2).
Proof.
  intros T1 T2 s Hlcabs Hsub t2 HR2.
  apply R_app_abs_aux; [exact Hlcabs | exact Hsub | apply R_sn with (T := T1) | exact HR2].
  exact HR2.
Qed.

Lemma R_if : forall T b,
  R Ty_Bool b ->
  forall t2 t3, R T t2 -> R T t3 ->
  R T (tm_if b t2 t3).
Proof.
  intros T b Hb t2 t3 HR2 HR3.
  assert (Haux : forall b, strongly_normalizing b -> R Ty_Bool b ->
                  forall t2 t3, R T t2 -> R T t3 -> R T (tm_if b t2 t3)).
  { intros b0 Hsn. induction Hsn as [b0 Hstep IHb].
    intros Hb0 t2' t3' HR2' HR3'.
    destruct (step_trichotomy b0 (R_lc Ty_Bool b0 Hb0)) as [Hv | [[b0' Hsb] | [Hnv Hns]]].
    - (* b0 is a value *)
      destruct b0 as [n0 | x0 | a1 a2 | T0 body0 | | | a1 a2 a3];
        try solve [exfalso; inversion Hv].
      * (* abs: stuck *)
        apply R_stuck.
        -- apply lc_if; [apply R_lc with (T := Ty_Bool); exact Hb0
                       | apply R_lc with (T := T); exact HR2'
                       | apply R_lc with (T := T); exact HR3'].
        -- intros [t' Hs]. exact (step_if_abs_stuck T0 body0 t2' t3' t' Hs).
        -- intros Hv'; inversion Hv'.
      * (* true *)
        apply R_expand with (t' := t2').
        -- apply ST_IfTrue; apply R_lc with (T := T); assumption.
        -- assumption.
      * (* false *)
        apply R_expand with (t' := t3').
        -- apply ST_IfFalse; apply R_lc with (T := T); assumption.
        -- assumption.
    - (* b0 steps *)
      apply R_expand with (t' := tm_if b0' t2' t3').
      + apply ST_If; [assumption
                     | apply R_lc with (T := T); assumption
                     | apply R_lc with (T := T); assumption].
      + apply (IHb b0' Hsb).
        * apply R_step with (t := b0); assumption.
        * exact HR2'.
        * exact HR3'.
    - (* b0 is stuck *)
      apply R_stuck.
      + apply lc_if; [apply R_lc with (T := Ty_Bool); exact Hb0
                     | apply R_lc with (T := T); exact HR2'
                     | apply R_lc with (T := T); exact HR3'].
      + intros [t' Hs]. exact (step_if_stuck_fun b0 t2' t3' t' Hnv Hns Hs).
      + intros Hv'; inversion Hv'. }
  apply Haux with (b := b).
  - apply R_sn with (T := Ty_Bool). exact Hb.
  - exact Hb.
  - exact HR2.
  - exact HR3.
Qed.

(* ------------------------------------------------------------------ *)
(* Well-typed terms are locally closed                                 *)
(* ------------------------------------------------------------------ *)

Lemma has_type_lc : forall Gamma t T,
  has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T Hty.
  induction Hty as [Gamma x T Hx
                 | L Gamma T1 T2 t1 Hbody IHbody
                 | Gamma t1 t2 T1 T2 Ht1 IH1 Ht2 IH2
                 | Gamma
                 | Gamma
                 | Gamma t1 t2 t3 T Ht1 IH1 Ht2 IH2 Ht3 IH3].
  - apply lc_fvar.
  - apply lc_abs.
    destruct (fresh_exists L) as [x Hx].
    pose proof (IHbody x Hx) as Hlc.
    apply (lc_open_rec_inv 0 0 t1 (tm_fvar x)); [lia | exact Hlc | apply lc_fvar].
  - apply lc_app; assumption.
  - apply lc_true.
  - apply lc_false.
  - apply lc_if; assumption.
Qed.

(* ------------------------------------------------------------------ *)
(* The fundamental theorem of the logical relation                     *)
(* ------------------------------------------------------------------ *)

Theorem fundamental : forall Gamma t T,
  has_type Gamma t T ->
  forall rho, ctx_ok Gamma rho -> R T (subst_tm rho t).
Proof.
  intros Gamma t T Hty.
  induction Hty as [Gamma x T Hx
                 | L Gamma T1 T2 t1 Hbody IHbody
                 | Gamma t1 t2 T1 T2 Ht1 IH1 Ht2 IH2
                 | Gamma
                 | Gamma
                 | Gamma t1 t2 t3 T Ht1 IH1 Ht2 IH2 Ht3 IH3];
    intros rho [HrhoR HrhoLc].
  - (* T_Var *) simpl. apply HrhoR. exact Hx.
  - (* T_Abs *) simpl.
    destruct (fresh_exists (L ++ fv t1)) as [x Hx].
    assert (HxL : ~ In x L).
    { intro H. apply Hx. apply in_app_iff. left. exact H. }
    assert (Hxfv : ~ In x (fv t1)).
    { intro H. apply Hx. apply in_app_iff. right. exact H. }
    assert (Hlc1 : lc_at 1 t1).
    { apply (lc_open_rec_inv 0 0 t1 (tm_fvar x)); [lia | | apply lc_fvar].
      apply has_type_lc with (Gamma := update Gamma x T1) (T := T2).
      apply Hbody. exact HxL. }
    assert (Hlcabs : locally_closed (tm_abs T1 (subst_tm rho t1))).
    { apply lc_abs. apply subst_lc_at with (k := 1).
      - exact Hlc1.
      - intros y. apply lc_at_weaken with (k := 0); [lia | apply HrhoLc]. }
    split.
    + exact Hlcabs.
    + split.
      * apply value_SN. apply v_abs. exact Hlcabs.
      * intros t2 HR2.
        apply R_app_abs with (T1 := T1) (T2 := T2) (s := subst_tm rho t1).
        -- exact Hlcabs.
        -- intros v Hv HRv.
           assert (Hok' : ctx_ok (update Gamma x T1) (extend_rho rho x v)).
           { split.
             - intros y U HyU.
               destruct (Nat.eqb x y) eqn:E.
               + apply Nat.eqb_eq in E. subst y.
                 rewrite update_same in HyU.
                 injection HyU as HU. subst U.
                 rewrite extend_rho_same. exact HRv.
               + apply Nat.eqb_neq in E.
                 rewrite update_other in HyU by (intro Heq; apply E; symmetry; exact Heq).
                 rewrite extend_rho_other by (intro Heq; apply E; symmetry; exact Heq).
                 apply HrhoR. exact HyU.
             - intros y. apply extend_rho_lc;
                 [exact HrhoLc | apply value_lc; exact Hv]. }
           pose proof (IHbody x HxL (extend_rho rho x v) Hok') as Hsem.
           rewrite (subst_open_update rho x v HrhoLc (value_lc v Hv) t1 Hxfv) in Hsem.
           exact Hsem.
        -- exact HR2.
  - (* T_App *) simpl.
    assert (H1 := IH1 rho (conj HrhoR HrhoLc)).
    simpl in H1.
    destruct H1 as [Hlc1 [Hsn1 Happ1]].
    apply Happ1.
    apply IH2. split; assumption.
  - (* T_True *) simpl. split.
    + apply lc_true.
    + apply value_SN. apply v_true.
  - (* T_False *) simpl. split.
    + apply lc_false.
    + apply value_SN. apply v_false.
  - (* T_If *) simpl.
    apply R_if.
    + apply IH1. split; assumption.
    + apply IH2. split; assumption.
    + apply IH3. split; assumption.
Qed.

(* ------------------------------------------------------------------ *)
(* Target theorem                                                      *)
(* ------------------------------------------------------------------ *)

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Hty.
  assert (Hok : ctx_ok empty tm_fvar).
  { split.
    - intros x U Hx. unfold empty in Hx. discriminate.
    - intros x. apply lc_fvar. }
  pose proof (fundamental empty t T Hty tm_fvar Hok) as HR.
  rewrite subst_identity in HR.
  apply R_sn with (T := T). exact HR.
Qed.

End STLCCBVNormalizationTask.


