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

(* ================================================================== *)
(* Development: strong normalization of CBV STLC via a logical relation *)
(* ================================================================== *)

(** ** Strong normalization as accessibility of the reverse step relation *)

Definition step_inv (t t' : tm) : Prop := step t' t.

Definition sn (t : tm) : Prop := Acc step_inv t.

Lemma sn_inv : forall t t', sn t -> step t t' -> sn t'.
Proof.
  intros t t' H Hs. destruct H as [Hf]. apply Hf. exact Hs.
Qed.

Lemma sn_intro : forall t, (forall t', step t t' -> sn t') -> sn t.
Proof.
  intros t H. apply Acc_intro. intros t' Ht'. apply H. exact Ht'.
Qed.

Lemma sn_multi : forall t t', multi step t t' -> sn t -> sn t'.
Proof.
  intros t t' H. induction H as [x | x y z Hxy Hyz IH].
  - intros Hx. exact Hx.
  - intros Hx. apply IH. apply sn_inv with (t := x); auto.
Qed.

(** ** Values *)

Lemma value_no_step : forall v, value v -> forall v', step v v' -> False.
Proof. intros v Hv. induction Hv; intros v' Hstep; inversion Hstep. Qed.

Lemma abs_no_step : forall T t s, step (tm_abs T t) s -> False.
Proof. intros T t s H. inversion H. Qed.

Lemma value_sn : forall v, value v -> sn v.
Proof.
  intros v Hv. apply sn_intro. intros v' Hs. exfalso. eapply value_no_step; eauto.
Qed.

Lemma value_lc : forall v, value v -> locally_closed v.
Proof. intros v Hv. destruct Hv. - assumption. - constructor. - constructor. Qed.

(** ** Inversion principles for local closure *)

Lemma lc_app_inv : forall k a b, lc_at k (tm_app a b) -> lc_at k a /\ lc_at k b.
Proof. intros k a b H. inversion H; subst; auto. Qed.

Lemma lc_abs_inv : forall k A t, lc_at k (tm_abs A t) -> lc_at (S k) t.
Proof. intros k A t H. inversion H; subst; auto. Qed.

Lemma lc_if_inv : forall k a b c, lc_at k (tm_if a b c) ->
  lc_at k a /\ lc_at k b /\ lc_at k c.
Proof. intros k a b c H. inversion H; subst; auto. Qed.

(** ** Local closure lemmas *)

Lemma lc_at_weaken : forall t k k', lc_at k t -> k <= k' -> lc_at k' t.
Proof.
  induction t as [n | x | t1 IH1 t2 IH2 | A t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3];
  intros k k' H Hle; inversion H; subst.
  - constructor. lia.
  - constructor.
  - constructor; [apply IH1 with (k := k) | apply IH2 with (k := k)]; auto.
  - constructor. apply IH1 with (k := S k); auto. lia.
  - constructor.
  - constructor.
  - constructor; [apply IH1 with (k := k) | apply IH2 with (k := k) | apply IH3 with (k := k)]; auto.
Qed.

Lemma lc_open_rec : forall t k u,
  lc_at (S k) t -> lc_at k u -> lc_at k (open_rec k u t).
Proof.
  induction t as [n | x | t1 IH1 t2 IH2 | A t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3];
  intros k u H Hu; simpl.
  - destruct (Nat.eqb k n) eqn:E; simpl.
    + apply Nat.eqb_eq in E. subst n. exact Hu.
    + apply Nat.eqb_neq in E. inversion H; subst. constructor. lia.
  - constructor.
  - inversion H; subst. constructor; auto.
  - inversion H; subst. constructor. apply IH1 with (k := S k); auto.
    apply lc_at_weaken with (k := k); auto.
  - constructor.
  - constructor.
  - inversion H; subst. constructor; auto.
Qed.

Lemma lc_open_inv_fvar : forall t k x,
  lc_at k (open_rec k (tm_fvar x) t) -> lc_at (S k) t.
Proof.
  induction t as [n | y | t1 IH1 t2 IH2 | A t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3];
  intros k x H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E; simpl in H.
    + apply Nat.eqb_eq in E. subst n. constructor. lia.
    + apply Nat.eqb_neq in E. inversion H; subst. constructor. lia.
  - constructor.
  - inversion H; subst. constructor.
    + apply IH1 with (k := k) (x := x); auto.
    + apply IH2 with (k := k) (x := x); auto.
  - inversion H; subst. constructor. apply IH1 with (k := S k) (x := x); auto.
  - constructor.
  - constructor.
  - inversion H; subst. constructor.
    + apply IH1 with (k := k) (x := x); auto.
    + apply IH2 with (k := k) (x := x); auto.
    + apply IH3 with (k := k) (x := x); auto.
Qed.

Lemma step_lc : forall t t', step t t' -> locally_closed t -> locally_closed t'.
Proof.
  intros t. induction t as [n | x | t1 IH1 t2 IH2 | A t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3];
  intros t' Hstep Hlc.
  - (* bvar *) inversion Hstep.
  - (* fvar *) inversion Hstep.
  - (* app *)
    apply lc_app_inv in Hlc. destruct Hlc as [H1 H2].
    inversion Hstep; subst.
    + (* ST_AppAbs *)
      apply lc_abs_inv in H1. simpl. apply lc_open_rec with (k := 0); auto.
    + (* ST_App1 *)
      simpl. constructor; auto. apply IH1; auto.
    + (* ST_App2 *)
      simpl. constructor; auto. apply IH2; auto.
  - (* abs *) inversion Hstep.
  - (* true *) inversion Hstep.
  - (* false *) inversion Hstep.
  - (* if *)
    apply lc_if_inv in Hlc. destruct Hlc as [H1 [H2 H3]].
    inversion Hstep; subst.
    + (* ST_IfTrue *) simpl. exact H2.
    + (* ST_IfFalse *) simpl. exact H3.
    + (* ST_If *) simpl. constructor; auto. apply IH1; auto.
Qed.

(** ** Free variables and substitution *)

Fixpoint fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ => nil
  | tm_fvar x => cons x nil
  | tm_app t1 t2 => app (fv t1) (fv t2)
  | tm_abs _ t1 => fv t1
  | tm_true => nil
  | tm_false => nil
  | tm_if t1 t2 t3 => app (fv t1) (app (fv t2) (fv t3))
  end.

Fixpoint subst_tm (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_app t1 t2 => tm_app (subst_tm sigma t1) (subst_tm sigma t2)
  | tm_abs T t1 => tm_abs T (subst_tm sigma t1)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 =>
      tm_if (subst_tm sigma t1) (subst_tm sigma t2) (subst_tm sigma t3)
  end.

Definition cons_tm (x : atom) (v : tm) (sigma : atom -> tm) : atom -> tm :=
  fun y => if Nat.eqb x y then v else sigma y.

Lemma open_rec_irrel : forall t k w, lc_at k t -> open_rec k w t = t.
Proof.
  induction t as [n | x | t1 IH1 t2 IH2 | A t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3];
  intros k w H; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. inversion H. lia.
    + auto.
  - auto.
  - inversion H; subst. rewrite IH1; auto. rewrite IH2; auto.
  - inversion H; subst. rewrite IH1 with (k := S k); auto.
  - auto.
  - auto.
  - inversion H; subst. rewrite IH1; auto. rewrite IH2; auto. rewrite IH3; auto.
Qed.

Lemma subst_open_rec : forall t k u sigma,
  (forall x, In x (fv t) -> lc_at k (sigma x)) ->
  subst_tm sigma (open_rec k u t) =
  open_rec k (subst_tm sigma u) (subst_tm sigma t).
Proof.
  induction t as [n | x | t1 IH1 t2 IH2 | A t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3];
  intros k u sigma Hlc; simpl.
  - destruct (Nat.eqb k n) eqn:E; simpl; auto.
  - assert (Hirr : open_rec k (subst_tm sigma u) (sigma x) = sigma x).
    { apply open_rec_irrel. apply Hlc. simpl. auto. }
    rewrite Hirr. auto.
  - assert (HA : subst_tm sigma (open_rec k u t1) =
                open_rec k (subst_tm sigma u) (subst_tm sigma t1)).
    { apply IH1. intros y Hy. apply Hlc. apply in_app_iff. left. exact Hy. }
    assert (HB : subst_tm sigma (open_rec k u t2) =
                open_rec k (subst_tm sigma u) (subst_tm sigma t2)).
    { apply IH2. intros y Hy. apply Hlc. apply in_app_iff. right. exact Hy. }
    rewrite HA, HB. auto.
  - assert (Habs : subst_tm sigma (open_rec (S k) u t1) =
                  open_rec (S k) (subst_tm sigma u) (subst_tm sigma t1)).
    { apply IH1. intros y Hy. apply lc_at_weaken with (k := k).
      - apply Hlc. exact Hy.
      - lia. }
    rewrite Habs. auto.
  - auto.
  - auto.
  - assert (HA : subst_tm sigma (open_rec k u t1) =
                open_rec k (subst_tm sigma u) (subst_tm sigma t1)).
    { apply IH1. intros y Hy. apply Hlc. apply in_app_iff. left. exact Hy. }
    assert (HB : subst_tm sigma (open_rec k u t2) =
                open_rec k (subst_tm sigma u) (subst_tm sigma t2)).
    { apply IH2. intros y Hy. apply Hlc. apply in_app_iff. right. apply in_app_iff. left. exact Hy. }
    assert (HC : subst_tm sigma (open_rec k u t3) =
                open_rec k (subst_tm sigma u) (subst_tm sigma t3)).
    { apply IH3. intros y Hy. apply Hlc. apply in_app_iff. right. apply in_app_iff. right. exact Hy. }
    rewrite HA, HB, HC. auto.
Qed.

Lemma subst_cons_irrel : forall t x v sigma,
  ~ In x (fv t) -> subst_tm (cons_tm x v sigma) t = subst_tm sigma t.
Proof.
  induction t as [n | y | t1 IH1 t2 IH2 | A t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3];
  intros x v sigma H; simpl in *.
  - auto.
  - unfold cons_tm. destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. subst y. exfalso. apply H. simpl. auto.
    + auto.
  - assert (HA : subst_tm (cons_tm x v sigma) t1 = subst_tm sigma t1).
    { apply IH1. intro Hc. apply H. apply in_app_iff. left. exact Hc. }
    assert (HB : subst_tm (cons_tm x v sigma) t2 = subst_tm sigma t2).
    { apply IH2. intro Hc. apply H. apply in_app_iff. right. exact Hc. }
    rewrite HA, HB. auto.
  - assert (HA : subst_tm (cons_tm x v sigma) t1 = subst_tm sigma t1).
    { apply IH1. intro Hc. apply H. exact Hc. }
    rewrite HA. auto.
  - auto.
  - auto.
  - assert (HA : subst_tm (cons_tm x v sigma) t1 = subst_tm sigma t1).
    { apply IH1. intro Hc. apply H. repeat rewrite in_app_iff. auto. }
    assert (HB : subst_tm (cons_tm x v sigma) t2 = subst_tm sigma t2).
    { apply IH2. intro Hc. apply H. repeat rewrite in_app_iff. auto. }
    assert (HC : subst_tm (cons_tm x v sigma) t3 = subst_tm sigma t3).
    { apply IH3. intro Hc. apply H. repeat rewrite in_app_iff. auto. }
    rewrite HA, HB, HC. auto.
Qed.

Lemma subst_id : forall t, subst_tm (fun x => tm_fvar x) t = t.
Proof.
  induction t as [n | x | t1 IH1 t2 IH2 | A t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3]; simpl.
  - auto.
  - auto.
  - rewrite IH1, IH2. auto.
  - rewrite IH1. auto.
  - auto.
  - auto.
  - rewrite IH1, IH2, IH3. auto.
Qed.

Lemma subst_open_fvar : forall t x v sigma,
  (forall y, In y (fv t) -> lc_at 0 (cons_tm x v sigma y)) ->
  ~ In x (fv t) ->
  subst_tm (cons_tm x v sigma) (open t (tm_fvar x)) = open (subst_tm sigma t) v.
Proof.
  intros t x v sigma Hlc Hx. unfold open.
  rewrite subst_open_rec.
  - simpl.
    assert (Hxx : cons_tm x v sigma x = v).
    { unfold cons_tm. rewrite Nat.eqb_refl. auto. }
    rewrite Hxx.
    rewrite subst_cons_irrel; auto.
  - exact Hlc.
Qed.

Lemma lc_at_subst : forall t k, lc_at k t ->
  forall sigma, (forall x, In x (fv t) -> lc_at k (sigma x)) ->
  lc_at k (subst_tm sigma t).
Proof.
  induction t as [n | y | t1 IH1 t2 IH2 | A t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3];
  intros k H sigma Hsigma; simpl in *.
  - auto.
  - apply Hsigma. simpl. auto.
  - apply lc_app_inv in H. destruct H as [H1 H2]. constructor.
    + apply IH1 with (k := k).
      * auto.
      * intros z Hz. apply Hsigma. apply in_app_iff. left. exact Hz.
    + apply IH2 with (k := k).
      * auto.
      * intros z Hz. apply Hsigma. apply in_app_iff. right. exact Hz.
  - apply lc_abs_inv in H. constructor. apply IH1 with (k := S k).
    + auto.
    + intros z Hz. apply lc_at_weaken with (k := k).
      * apply Hsigma. simpl. exact Hz.
      * lia.
  - constructor.
  - constructor.
  - apply lc_if_inv in H. destruct H as [H1 [H2 H3]]. constructor.
    + apply IH1 with (k := k).
      * auto.
      * intros z Hz. apply Hsigma. repeat rewrite in_app_iff. auto.
    + apply IH2 with (k := k).
      * auto.
      * intros z Hz. apply Hsigma. repeat rewrite in_app_iff. auto.
    + apply IH3 with (k := k).
      * auto.
      * intros z Hz. apply Hsigma. repeat rewrite in_app_iff. auto.
Qed.

Lemma incl_fv_open_rec : forall t k u x,
  In x (fv t) -> In x (fv (open_rec k u t)).
Proof.
  induction t as [n | y | t1 IH1 t2 IH2 | A t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3];
  intros k u x Hx; simpl in *.
  - destruct (Nat.eqb k n); simpl; tauto.
  - simpl in *. auto.
  - apply in_app_iff in Hx. apply in_app_iff. destruct Hx as [Hc | Hc].
    + left. apply IH1 with (k := k). exact Hc.
    + right. apply IH2 with (k := k). exact Hc.
  - apply IH1 with (k := S k). auto.
  - auto.
  - auto.
  - simpl in *. repeat rewrite in_app_iff in *.
    destruct Hx as [Hc | [Hc | Hc]].
    + left. apply IH1 with (k := k). exact Hc.
    + right. left. apply IH2 with (k := k). exact Hc.
    + right. right. apply IH3 with (k := k). exact Hc.
Qed.

(** ** Typing lemmas *)

Lemma update_eq : forall Gamma x T, update Gamma x T x = Some T.
Proof. intros. unfold update. rewrite Nat.eqb_refl. auto. Qed.

Lemma update_neq : forall Gamma x y T, x <> y -> update Gamma x T y = Gamma y.
Proof. intros. unfold update. apply Nat.eqb_neq in H. rewrite H. auto. Qed.

Fixpoint max_list (l : list atom) : nat :=
  match l with
  | nil => 0
  | cons a l' => Nat.max a (max_list l')
  end.

Lemma in_max_list : forall (l : list atom) a, In a l -> a <= max_list l.
Proof.
  intros l. induction l as [| b l IH]; intros a Ha.
  - destruct Ha.
  - simpl in Ha. destruct Ha as [-> | Ha].
    + apply Nat.le_max_l.
    + apply Nat.le_trans with (max_list l); auto. apply Nat.le_max_r.
Qed.

Lemma exists_fresh : forall l : list atom, exists x, ~ In x l.
Proof.
  intros l. exists (S (max_list l)). intro H.
  pose proof (in_max_list l (S (max_list l)) H) as H1.
  apply Nat.lt_irrefl with (S (max_list l)). lia.
Qed.

Lemma has_type_lc : forall Gamma t T, has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T H. induction H.
  - (* T_Var *) constructor.
  - (* T_Abs *) simpl. constructor.
    destruct (exists_fresh L) as [x Hx].
    apply lc_open_inv_fvar with (x := x).
    apply H0. auto.
  - (* T_App *) simpl. constructor; auto.
  - (* T_True *) constructor.
  - (* T_False *) constructor.
  - (* T_If *) simpl. constructor; auto.
Qed.

Lemma has_type_fv : forall Gamma t T, has_type Gamma t T ->
  forall z, In z (fv t) -> exists U, Gamma z = Some U.
Proof.
  intros Gamma t T H. induction H.
  - (* T_Var *) intros z Hz. simpl in Hz. destruct Hz as [-> | []]. exists T. auto.
  - (* T_Abs *) intros z Hz. simpl in Hz.
    destruct (exists_fresh (app L (fv t1))) as [y Hy].
    assert (HyL : ~ In y L).
    { intro Hc. apply Hy. apply in_app_iff. left. exact Hc. }
    assert (Hyfv : ~ In y (fv t1)).
    { intro Hc. apply Hy. apply in_app_iff. right. exact Hc. }
    assert (Hiny : In z (fv (open t1 (tm_fvar y)))).
    { apply incl_fv_open_rec with (k := 0) (u := tm_fvar y). exact Hz. }
    destruct (H0 y HyL z Hiny) as [U HU].
    exists U. unfold update in HU.
    destruct (Nat.eqb y z) eqn:E.
    + apply Nat.eqb_eq in E. subst y. exfalso. apply Hyfv. exact Hz.
    + exact HU.
  - (* T_App *) intros z Hz. simpl in Hz. apply in_app_iff in Hz.
    destruct Hz as [Hz | Hz].
    + apply IHhas_type1. exact Hz.
    + apply IHhas_type2. exact Hz.
  - (* T_True *) intros z Hz. simpl in Hz. destruct Hz.
  - (* T_False *) intros z Hz. simpl in Hz. destruct Hz.
  - (* T_If *) intros z Hz. simpl in Hz. repeat rewrite in_app_iff in Hz.
    destruct Hz as [Hz | [Hz | Hz]].
    + apply IHhas_type1. exact Hz.
    + apply IHhas_type2. exact Hz.
    + apply IHhas_type3. exact Hz.
Qed.

(** ** The logical relation *)

Definition non_abs (t : tm) : Prop :=
  match t with
  | tm_abs _ _ => False
  | _ => True
  end.

Lemma non_abs_neq : forall s A t0, non_abs s -> s = tm_abs A t0 -> False.
Proof.
  intros s A t0 H Heq. destruct s; simpl in *; try discriminate; tauto.
Qed.

Fixpoint rel (T : ty) (t : tm) : Prop :=
  locally_closed t /\
  sn t /\
  match T with
  | Ty_Bool => True
  | Ty_Arrow A B => forall v, value v -> rel A v -> rel B (tm_app t v)
  end.

Lemma rel_lc : forall T t, rel T t -> locally_closed t.
Proof. intros T. induction T as [| A IHA B IHB]; intros t H; simpl in H; tauto. Qed.

Lemma rel_sn : forall T t, rel T t -> sn t.
Proof. intros T. induction T as [| A IHA B IHB]; intros t H; simpl in H; tauto. Qed.

Lemma rel_app_clause : forall A B t, rel (Ty_Arrow A B) t ->
  forall v, value v -> rel A v -> rel B (tm_app t v).
Proof. intros A B t H. simpl in H. tauto. Qed.

Lemma rel_bool_inv : forall t, rel Ty_Bool t -> locally_closed t /\ sn t.
Proof. intros t H. simpl in H. tauto. Qed.

Lemma rel_cr2 : forall T t t', rel T t -> step t t' -> rel T t'.
Proof.
  intros T. induction T as [| A IHA B IHB]; intros t t' Hrel Hstep.
  - simpl in *. destruct Hrel as (Hlc & Hsn & _). simpl.
    split; [| split; [| exact I]].
    + eapply step_lc; eauto.
    + apply sn_inv with (t := t); auto.
  - simpl in *. destruct Hrel as (Hlc & Hsn & Happ). simpl.
    split; [| split].
    + eapply step_lc; eauto.
    + apply sn_inv with (t := t); auto.
    + intros v Hv Hrelv. apply IHB with (t := tm_app t v).
      * apply Happ; auto.
      * eapply ST_App1.
        -- exact Hstep.
        -- apply value_lc; auto.
Qed.

Lemma rel_beta : forall A B t, rel (Ty_Arrow A B) t ->
  forall T t0, t = tm_abs T t0 -> forall v, value v -> rel A v -> rel B (open t0 v).
Proof.
  intros A B t Hrel T t0 Heq v Hv Hrelv. subst t.
  apply rel_cr2 with (t := tm_app (tm_abs T t0) v).
  - apply rel_app_clause with (A := A); auto.
  - eapply ST_AppAbs.
    + pose proof (rel_lc _ _ Hrel) as Hlc. simpl in Hlc. exact Hlc.
    + exact Hv.
Qed.

Lemma rel_expand : forall T s,
  non_abs s -> locally_closed s -> sn s ->
  (forall s', step s s' -> rel T s') -> rel T s.
Proof.
  intros T. induction T as [| A IHA B IHB]; intros s Hna Hlc Hsn Hred.
  - simpl. split; [| split; [| exact I]]; auto.
  - simpl. split; [| split; [| idtac]]; auto.
    intros v Hv Hrelv.
    apply IHB.
    + simpl. exact I.
    + simpl. constructor.
      * exact Hlc.
      * exact (rel_lc _ _ Hrelv).
    + apply sn_intro. intros x Hx. inversion Hx; subst.
      * exfalso. eapply non_abs_neq; eauto.
      * apply rel_sn with (T := B). apply rel_app_clause with (A := A).
        -- apply Hred. assumption.
        -- exact Hv.
        -- exact Hrelv.
      * exfalso. eapply value_no_step with (v := v); eauto.
    + intros x Hx. inversion Hx; subst.
      * exfalso. eapply non_abs_neq; eauto.
      * apply rel_app_clause with (A := A).
        -- apply Hred. assumption.
        -- exact Hv.
        -- exact Hrelv.
      * exfalso. eapply value_no_step with (v := v); eauto.
Qed.

Lemma rel_app_aux : forall A B (s : tm), sn s -> rel (Ty_Arrow A B) s ->
  forall t, rel A t -> rel B (tm_app s t).
Proof.
  intros A B s Hsn.
  induction Hsn as [s HstepS IHS].
  intros HrelS t HrelT.
  pose proof (rel_sn _ _ HrelT) as Hsnt.
  revert HrelT.
  induction Hsnt as [t HstepT IHT].
  intros HrelT.
  apply (rel_expand B (tm_app s t)).
  - simpl. exact I.
  - simpl. constructor.
    + exact (rel_lc _ _ HrelS).
    + exact (rel_lc _ _ HrelT).
  - apply sn_intro. intros x Hx. inversion Hx; subst.
    + apply rel_sn with (T := B). eapply rel_beta; eauto.
    + apply rel_sn with (T := B). apply IHS.
      * assumption.
      * apply rel_cr2 with (t := s); auto.
      * exact HrelT.
    + apply rel_sn with (T := B). apply IHT.
      * assumption.
      * apply rel_cr2 with (t := t); auto.
  - intros x Hx. inversion Hx; subst.
    + eapply rel_beta; eauto.
    + apply IHS.
      * assumption.
      * apply rel_cr2 with (t := s); auto.
      * exact HrelT.
    + apply IHT.
      * assumption.
      * apply rel_cr2 with (t := t); auto.
Qed.

Lemma rel_if : forall T (a b c : tm),
  rel Ty_Bool a -> rel T b -> rel T c -> rel T (tm_if a b c).
Proof.
  intros T a b c HrelA HrelB HrelC.
  pose proof (rel_sn _ _ HrelA) as Hsna.
  revert HrelA HrelB HrelC.
  induction Hsna as [a HstepA IHA].
  intros HrelA HrelB HrelC.
  apply (rel_expand T (tm_if a b c)).
  - simpl. exact I.
  - simpl. constructor.
    + exact (rel_lc _ _ HrelA).
    + exact (rel_lc _ _ HrelB).
    + exact (rel_lc _ _ HrelC).
  - apply sn_intro. intros x Hx. inversion Hx; subst.
    + apply rel_sn with (T := T). exact HrelB.
    + apply rel_sn with (T := T). exact HrelC.
    + apply rel_sn with (T := T). apply IHA.
      * assumption.
      * apply rel_cr2 with (t := a); auto.
      * exact HrelB.
      * exact HrelC.
  - intros x Hx. inversion Hx; subst.
    + exact HrelB.
    + exact HrelC.
    + apply IHA.
      * assumption.
      * apply rel_cr2 with (t := a); auto.
      * exact HrelB.
      * exact HrelC.
Qed.

(** ** Fundamental theorem *)

Theorem fundamental : forall Gamma t T,
  has_type Gamma t T ->
  forall sigma, (forall x U, Gamma x = Some U -> rel U (sigma x)) ->
  rel T (subst_tm sigma t).
Proof.
  intros Gamma t T Hty.
  induction Hty; intros sigma Hsigma.
  - (* T_Var *) simpl. apply Hsigma. exact H.
  - (* T_Abs *) simpl.
    assert (Habs : has_type Gamma (tm_abs T1 t1) (Ty_Arrow T1 T2)).
    { eapply T_Abs. exact H. }
    assert (Hlc1 : lc_at 1 t1).
    { apply lc_abs_inv with (A := T1).
      apply has_type_lc with (Gamma := Gamma) (T := Ty_Arrow T1 T2). exact Habs. }
    assert (Hfv : forall z, In z (fv t1) -> exists U, Gamma z = Some U).
    { intros z Hz. apply (has_type_fv Gamma (tm_abs T1 t1) (Ty_Arrow T1 T2) Habs z).
      simpl. exact Hz. }
    assert (Hlcsub : locally_closed (tm_abs T1 (subst_tm sigma t1))).
    { simpl. constructor. apply lc_at_subst with (k := 1).
      - exact Hlc1.
      - intros z Hz. apply lc_at_weaken with (k := 0).
        + destruct (Hfv z Hz) as [U HU]. apply rel_lc with (T := U). apply Hsigma. exact HU.
        + lia. }
    split; [| split].
    + exact Hlcsub.
    + apply value_sn. apply v_abs. exact Hlcsub.
    + intros v Hv Hrelv.
      assert (Hbody : rel T2 (open (subst_tm sigma t1) v)).
      { destruct (exists_fresh (app L (fv t1))) as [x Hx].
        assert (HxL : ~ In x L).
        { intro Hc. apply Hx. apply in_app_iff. left. exact Hc. }
        assert (Hxfv : ~ In x (fv t1)).
        { intro Hc. apply Hx. apply in_app_iff. right. exact Hc. }
        assert (Hsigma' : forall z U, update Gamma x T1 z = Some U ->
                                     rel U (cons_tm x v sigma z)).
        { intros z U Hz. unfold cons_tm. destruct (Nat.eqb x z) eqn:E.
          - apply Nat.eqb_eq in E. subst z. rewrite update_eq in Hz.
            injection Hz as HU. subst U. exact Hrelv.
          - apply Nat.eqb_neq in E. rewrite update_neq in Hz by auto. apply Hsigma. exact Hz. }
        assert (Hopen : subst_tm (cons_tm x v sigma) (open t1 (tm_fvar x)) =
                        open (subst_tm sigma t1) v).
        { apply subst_open_fvar.
          - intros z Hz. unfold cons_tm. destruct (Nat.eqb x z) eqn:E.
            + apply Nat.eqb_eq in E. subst z. apply value_lc; auto.
            + destruct (Hfv z Hz) as [U HU]. apply rel_lc with (T := U). apply Hsigma. exact HU.
          - exact Hxfv. }
        rewrite <- Hopen.
        apply (H0 x HxL (cons_tm x v sigma) Hsigma'). }
      apply (rel_expand T2 (tm_app (tm_abs T1 (subst_tm sigma t1)) v)).
      * simpl. exact I.
      * simpl. constructor.
        -- exact Hlcsub.
        -- exact (rel_lc _ _ Hrelv).
      * apply sn_intro. intros y Hy. inversion Hy; subst.
        -- apply rel_sn with (T := T2). exact Hbody.
        -- exfalso. eapply abs_no_step; eassumption.
        -- exfalso. eapply value_no_step with (v := v); eassumption.
      * intros y Hy. inversion Hy; subst.
        -- exact Hbody.
        -- exfalso. eapply abs_no_step; eassumption.
        -- exfalso. eapply value_no_step with (v := v); eassumption.
  - (* T_App *) simpl. eapply rel_app_aux.
    + apply rel_sn with (T := Ty_Arrow T1 T2). apply IHHty1. exact Hsigma.
    + apply IHHty1. exact Hsigma.
    + apply IHHty2. exact Hsigma.
  - (* T_True *) simpl. split; [| split; [| exact I]].
    + constructor.
    + apply value_sn. constructor.
  - (* T_False *) simpl. split; [| split; [| exact I]].
    + constructor.
    + apply value_sn. constructor.
  - (* T_If *) simpl. apply rel_if.
    + apply IHHty1. exact Hsigma.
    + apply IHHty2. exact Hsigma.
    + apply IHHty3. exact Hsigma.
Qed.

Lemma acc_sn : forall t, sn t -> strongly_normalizing t.
Proof.
  intros t H. induction H as [t Hstep IH].
  apply SN_intro. intros t' Ht'. apply IH. exact Ht'.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Hty.
  apply acc_sn.
  assert (Hm : forall x U, empty x = Some U -> rel U ((fun z => tm_fvar z) x)).
  { intros x U Hx. unfold empty in Hx. discriminate. }
  pose proof (fundamental empty t T Hty (fun z => tm_fvar z) Hm) as Hrel.
  rewrite subst_id in Hrel.
  apply rel_sn with (T := T). exact Hrel.
Qed.

End STLCCBVNormalizationTask.
