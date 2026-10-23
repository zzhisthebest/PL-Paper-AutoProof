(** STLC call-by-value strong-normalization benchmark task. *)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Relations.Relation_Definitions.

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

(** Strong normalization, defined before the auxiliary development so that
    the logical relation can refer to it. *)

Inductive strongly_normalizing : tm -> Prop :=
  | SN_intro : forall t,
      (forall t', t --> t' -> strongly_normalizing t') ->
      strongly_normalizing t.


(** ============================================================ *)
(** Auxiliary development for the strong normalization proof.    *)
(** ============================================================ *)

(** ** Substitution for free variables *)

Fixpoint subst (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_app t1 t2 => tm_app (subst sigma t1) (subst sigma t2)
  | tm_abs T t1 => tm_abs T (subst sigma t1)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (subst sigma t1) (subst sigma t2) (subst sigma t3)
  end.

Definition ids (x : atom) : tm := tm_fvar x.

Definition env_lc (sigma : atom -> tm) : Prop :=
  forall x, locally_closed (sigma x).

Lemma subst_ids : forall t, subst ids t = t.
Proof. induction t; simpl; try reflexivity; congruence. Qed.

(** ** Free variables and freshness *)

Fixpoint fvs (t : tm) : list atom :=
  match t with
  | tm_bvar _ => (@nil atom)
  | tm_fvar x => (x :: nil)%list
  | tm_app t1 t2 => (fvs t1 ++ fvs t2)%list
  | tm_abs _ t1 => fvs t1
  | tm_true => (@nil atom)
  | tm_false => (@nil atom)
  | tm_if t1 t2 t3 => (fvs t1 ++ fvs t2 ++ fvs t3)%list
  end.

Fixpoint list_max (l : list atom) : atom :=
  match l with
  | nil => 0
  | x :: xs => Nat.max x (list_max xs)
  end.

Lemma list_max_upper : forall l x, In x l -> x <= list_max l.
Proof.
  induction l as [| y ys IH]; simpl; intros x Hin.
  - inversion Hin.
  - destruct Hin as [-> | Hin].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; eassumption | apply Nat.le_max_r].
Qed.

Lemma fresh : forall L : list atom, exists x, ~ In x L.
Proof.
  intros L. exists (S (list_max L)).
  intro Hin. apply list_max_upper in Hin.
  exact (Nat.nle_succ_diag_l (list_max L) Hin).
Qed.

Lemma fresh_two : forall L1 L2 : list atom, exists x, ~ In x L1 /\ ~ In x L2.
Proof.
  intros L1 L2. destruct (fresh (L1 ++ L2)) as [x Hx].
  exists x. split; intro Hin; apply Hx; apply in_or_app.
  - left; assumption.
  - right; assumption.
Qed.

(** ** Inversion lemmas for local closure *)

Lemma lc_app_inv : forall k t1 t2, lc_at k (tm_app t1 t2) -> lc_at k t1 /\ lc_at k t2.
Proof. intros k t1 t2 H. inversion H. split; assumption. Qed.

Lemma lc_abs_inv : forall k T t, lc_at k (tm_abs T t) -> lc_at (S k) t.
Proof. intros k T t H. inversion H. assumption. Qed.

Lemma lc_if_inv : forall k t1 t2 t3,
  lc_at k (tm_if t1 t2 t3) -> lc_at k t1 /\ lc_at k t2 /\ lc_at k t3.
Proof. intros k t1 t2 t3 H. inversion H. split; [assumption | split; assumption]. Qed.

Lemma lc_bvar_inv : forall k i, lc_at k (tm_bvar i) -> i < k.
Proof. intros k i H. inversion H. assumption. Qed.

Lemma lc_at_weaken : forall k k' t, lc_at k t -> k <= k' -> lc_at k' t.
Proof.
  intros k k' t H. revert k'. induction H; intros k' Hle.
  - apply lc_bvar. eapply Nat.lt_le_trans; eassumption.
  - apply lc_fvar.
  - apply lc_app; [apply IHlc_at1 | apply IHlc_at2]; assumption.
  - apply lc_abs. apply IHlc_at. apply le_n_S; assumption.
  - apply lc_true.
  - apply lc_false.
  - apply lc_if; [apply IHlc_at1 | apply IHlc_at2 | apply IHlc_at3]; assumption.
Qed.

(** Opening at exactly the bound index preserves / reflects local closure. *)

Lemma lc_open_rec : forall k v t, lc_at (S k) t -> lc_at k v -> lc_at k (open_rec k v t).
Proof.
  intros k v t Ht. revert k v Ht. induction t; intros k v Ht Hv; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. exact Hv.
    + apply lc_bvar. apply lc_bvar_inv in Ht. apply Nat.eqb_neq in E. lia.
  - apply lc_fvar.
  - apply lc_app.
    + apply IHt1 with (k := k) (v := v). apply lc_app_inv in Ht. apply Ht. assumption.
    + apply IHt2 with (k := k) (v := v). apply lc_app_inv in Ht. apply Ht. assumption.
  - apply lc_abs. apply IHt with (k := S k) (v := v).
    + apply lc_abs_inv in Ht. assumption.
    + apply lc_at_weaken with (k := k); [assumption | apply Nat.le_succ_diag_r].
  - apply lc_true.
  - apply lc_false.
  - apply lc_if.
    + apply IHt1 with (k := k) (v := v). apply lc_if_inv in Ht. apply Ht. assumption.
    + apply IHt2 with (k := k) (v := v). apply lc_if_inv in Ht. apply Ht. assumption.
    + apply IHt3 with (k := k) (v := v). apply lc_if_inv in Ht. apply Ht. assumption.
Qed.

Lemma lc_open_inv : forall k v t, lc_at k (open_rec k v t) -> lc_at k v -> lc_at (S k) t.
Proof.
  intros k v t Ht. revert k v Ht. induction t; intros k v Ht Hv; simpl in Ht.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. apply lc_bvar. lia.
    + apply lc_bvar. apply lc_bvar_inv in Ht. lia.
  - apply lc_fvar.
  - apply lc_app.
    + apply IHt1 with (k := k) (v := v). apply lc_app_inv in Ht. apply Ht. assumption.
    + apply IHt2 with (k := k) (v := v). apply lc_app_inv in Ht. apply Ht. assumption.
  - apply lc_abs. apply IHt with (k := S k) (v := v).
    + apply lc_abs_inv in Ht. assumption.
    + apply lc_at_weaken with (k := k); [assumption | apply Nat.le_succ_diag_r].
  - apply lc_true.
  - apply lc_false.
  - apply lc_if.
    + apply IHt1 with (k := k) (v := v). apply lc_if_inv in Ht. apply Ht. assumption.
    + apply IHt2 with (k := k) (v := v). apply lc_if_inv in Ht. apply Ht. assumption.
    + apply IHt3 with (k := k) (v := v). apply lc_if_inv in Ht. apply Ht. assumption.
Qed.

Lemma lc_at_open_id : forall k t, lc_at k t -> forall j u, k <= j -> open_rec j u t = t.
Proof.
  intros k t H. induction H; intros j u Hle; simpl.
  - destruct (Nat.eqb j i) eqn:E.
    + apply Nat.eqb_eq in E. subst j. edestruct Nat.lt_irrefl. eapply Nat.lt_le_trans; eassumption.
    + reflexivity.
  - reflexivity.
  - rewrite (IHlc_at1 j u Hle), (IHlc_at2 j u Hle). reflexivity.
  - rewrite (IHlc_at (S j) u). reflexivity. apply le_n_S; assumption.
  - reflexivity.
  - reflexivity.
  - rewrite (IHlc_at1 j u Hle), (IHlc_at2 j u Hle), (IHlc_at3 j u Hle). reflexivity.
Qed.

(** ** Substitution lemmas *)

Lemma subst_open_rec : forall sigma, env_lc sigma ->
  forall k v t,
  subst sigma (open_rec k v t) = open_rec k (subst sigma v) (subst sigma t).
Proof.
  intros sigma Henv k v t. revert k. induction t; intros k; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. apply lc_at_open_id with (k := 0). apply Henv. apply Nat.le_0_l.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IHt1, IHt2, IHt3. reflexivity.
Qed.

Definition env_update (sigma : atom -> tm) (x : atom) (u : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then u else sigma y.

Lemma env_update_eq : forall sigma x u, env_update sigma x u x = u.
Proof. intros. unfold env_update. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma env_update_neq : forall sigma x u y, x <> y -> env_update sigma x u y = sigma y.
Proof.
  intros. unfold env_update. apply Nat.eqb_neq in H. rewrite H. reflexivity.
Qed.

Lemma env_update_lc : forall sigma x u, env_lc sigma -> locally_closed u ->
  env_lc (env_update sigma x u).
Proof.
  intros sigma x u Hlc Hu y. unfold env_update.
  destruct (Nat.eqb x y) eqn:E.
  - apply Hu.
  - apply Hlc.
Qed.

Lemma subst_update_fresh : forall sigma x u t,
  ~ In x (fvs t) -> subst (env_update sigma x u) t = subst sigma t.
Proof.
  intros sigma x u t Hx. induction t; simpl in *.
  - reflexivity.
  - destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E. subst a. exfalso. apply Hx. left. reflexivity.
    + unfold env_update. rewrite E. reflexivity.
  - assert (Hx1 : ~ In x (fvs t1)) by (intro H; apply Hx; apply in_or_app; left; exact H).
    assert (Hx2 : ~ In x (fvs t2)) by (intro H; apply Hx; apply in_or_app; right; exact H).
    simpl. rewrite (IHt1 Hx1), (IHt2 Hx2). reflexivity.
  - rewrite (IHt Hx). reflexivity.
  - reflexivity.
  - reflexivity.
  - assert (Hx1 : ~ In x (fvs t1))
      by (intro H; apply Hx; apply in_or_app; left; exact H).
    assert (Hx2 : ~ In x (fvs t2))
      by (intro H; apply Hx; apply in_or_app; right; apply in_or_app; left; exact H).
    assert (Hx3 : ~ In x (fvs t3))
      by (intro H; apply Hx; apply in_or_app; right; apply in_or_app; right; exact H).
    simpl. rewrite (IHt1 Hx1), (IHt2 Hx2), (IHt3 Hx3). reflexivity.
Qed.

Lemma subst_open_env : forall sigma x v t,
  env_lc sigma -> locally_closed v -> ~ In x (fvs t) ->
  subst (env_update sigma x v) (open t (tm_fvar x)) = open (subst sigma t) v.
Proof.
  intros sigma x v t Henv Hv Hx.
  unfold open.
  rewrite (subst_open_rec (env_update sigma x v)).
  - simpl. rewrite env_update_eq. rewrite (subst_update_fresh sigma x v t Hx). reflexivity.
  - apply env_update_lc; assumption.
Qed.

Lemma lc_at_subst : forall sigma k t, lc_at k t -> env_lc sigma -> lc_at k (subst sigma t).
Proof.
  intros sigma k t Ht. revert k Ht. induction t; intros k Ht Henv; simpl.
  - apply lc_bvar. apply lc_bvar_inv in Ht. assumption.
  - apply lc_at_weaken with (k := 0). apply Henv. apply Nat.le_0_l.
  - apply lc_app.
    + apply IHt1 with (k := k). apply lc_app_inv in Ht. apply Ht. assumption.
    + apply IHt2 with (k := k). apply lc_app_inv in Ht. apply Ht. assumption.
  - apply lc_abs. apply IHt with (k := S k).
    + apply lc_abs_inv in Ht. assumption.
    + assumption.
  - apply lc_true.
  - apply lc_false.
  - apply lc_if.
    + apply IHt1 with (k := k). apply lc_if_inv in Ht. apply Ht. assumption.
    + apply IHt2 with (k := k). apply lc_if_inv in Ht. apply Ht. assumption.
    + apply IHt3 with (k := k). apply lc_if_inv in Ht. apply Ht. assumption.
Qed.

Lemma update_eq : forall Gamma x T, update Gamma x T x = Some T.
Proof. intros. unfold update. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma update_neq : forall Gamma x T y, x <> y -> update Gamma x T y = Gamma y.
Proof.
  intros. unfold update. apply Nat.eqb_neq in H. rewrite H. reflexivity.
Qed.

(** ** Basic properties of the step relation *)

Lemma SN_step : forall t, strongly_normalizing t -> forall t', t --> t' -> strongly_normalizing t'.
Proof.
  intros t HSN. induction HSN as [t Hred]. intros t' Hst. apply Hred. assumption.
Qed.

Lemma SN_multi : forall t t', strongly_normalizing t -> t -->* t' -> strongly_normalizing t'.
Proof.
  intros t t' HSN Hm. revert HSN. induction Hm; intros HSN.
  - assumption.
  - apply IHHm. apply SN_step with (t := x); assumption.
Qed.

Lemma value_nostep : forall t, value t -> forall t', ~ (t --> t').
Proof.
  intros t Hv t' Hst. inversion Hv; subst; inversion Hst.
Qed.

Lemma value_lc : forall t, value t -> locally_closed t.
Proof.
  intros t Hv. destruct Hv.
  - assumption.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma multi_abs : forall t t', t -->* t' -> forall T b, t = tm_abs T b -> t' = tm_abs T b.
Proof.
  intros t t' Hm. induction Hm; intros T b Heq.
  - subst. reflexivity.
  - subst. exfalso. inversion H.
Qed.

Lemma multi_step_inv : forall (t t' : tm), t -->* t' -> t = t' \/ (exists y, t --> y /\ y -->* t').
Proof.
  intros t t' Hm. destruct Hm as [x | x y z Hst Hrest].
  - left; reflexivity.
  - right. exists y. split; assumption.
Qed.

Lemma lc_step : forall t t', t --> t' -> locally_closed t -> locally_closed t'.
Proof.
  intros t t' Hst. induction Hst; intros Hlc.
  - (* ST_AppAbs *) simpl in Hlc. apply lc_app_inv in Hlc. destruct Hlc as [H1 H2].
    apply lc_abs_inv in H1. simpl. apply lc_open_rec with (k := 0); assumption.
  - (* ST_App1 *) simpl in Hlc. apply lc_app_inv in Hlc. destruct Hlc as [H1 H2].
    simpl. apply lc_app. apply IHHst. assumption. assumption.
  - (* ST_App2 *) simpl in Hlc. apply lc_app_inv in Hlc. destruct Hlc as [H1 H2].
    simpl. apply lc_app. assumption. apply IHHst. assumption.
  - (* ST_IfTrue *) simpl in Hlc. apply lc_if_inv in Hlc. destruct Hlc as [H1 [H2 H3]].
    assumption.
  - (* ST_IfFalse *) simpl in Hlc. apply lc_if_inv in Hlc. destruct Hlc as [H1 [H2 H3]].
    assumption.
  - (* ST_If *) simpl in Hlc. apply lc_if_inv in Hlc. destruct Hlc as [H1 [H2 H3]].
    simpl. apply lc_if. apply IHHst. assumption. assumption. assumption.
Qed.

Lemma multi_lc : forall t t', t -->* t' -> locally_closed t -> locally_closed t'.
Proof.
  intros t t' Hm. induction Hm; intros Hlc.
  - assumption.
  - apply IHHm. apply lc_step with (t := x); assumption.
Qed.

(** ** The logical relation

    [RR T t] is a type-indexed reducibility predicate, defined by recursion on
    the type.  At base type it is strong normalization.  At an arrow type it
    records strong normalization together with the hereditary condition that
    every multi-step reduct of [t] that is an abstraction, when opened with an
    argument of the domain type, lands back in the relation at the codomain
    type.  This "all value reducts" formulation (rather than an application
    condition) makes both the beta-expansion case and the application case
    go through without appeal to determinism of the step relation. *)

(** ** The logical relation *)

Fixpoint RR (T : ty) (t : tm) : Prop :=
  match T with
  | Ty_Bool => strongly_normalizing t /\ locally_closed t
  | Ty_Arrow T1 T2 =>
      strongly_normalizing t /\ locally_closed t /\
      (forall (T0 : ty) (b : tm),
          t -->* tm_abs T0 b ->
          forall u : tm, RR T1 u -> RR T2 (open b u))
  end.

Lemma RR_SN : forall T t, RR T t -> strongly_normalizing t.
Proof. intros T t H. destruct T; simpl in H; tauto. Qed.

Lemma RR_lc : forall T t, RR T t -> locally_closed t.
Proof. intros T t H. destruct T; simpl in H; tauto. Qed.

Lemma RR_arrow_clause : forall T1 T2 t, RR (Ty_Arrow T1 T2) t ->
  forall T0 b, t -->* tm_abs T0 b -> forall u, RR T1 u -> RR T2 (open b u).
Proof. intros T1 T2 t H. simpl in H. tauto. Qed.

Lemma RR_step : forall T t t', RR T t -> t --> t' -> RR T t'.
Proof.
  intros T. destruct T as [| T1 T2]; simpl; intros t t' HR Hst.
  - destruct HR as [HSN Hlc]. split.
    + apply SN_step with (t := t); assumption.
    + apply lc_step with (t := t); assumption.
  - destruct HR as [HSN [Hlc Hclos]]. split; [| split].
    + apply SN_step with (t := t); assumption.
    + apply lc_step with (t := t); assumption.
    + intros T0 b Hm u Hu. apply Hclos with (T0 := T0) (b := b).
      * apply multi_step with (y := t'); assumption.
      * assumption.
Qed.

Lemma RR_multi : forall T t t', RR T t -> t -->* t' -> RR T t'.
Proof.
  intros T t t' HR Hm. induction Hm.
  - assumption.
  - apply IHHm. apply RR_step with (t := x); assumption.
Qed.

Lemma RR_app : forall (t1 : tm), strongly_normalizing t1 ->
  forall T1 T2, RR (Ty_Arrow T1 T2) t1 ->
  forall t2, strongly_normalizing t2 -> RR T1 t2 -> RR T2 (tm_app t1 t2).
Proof.
  intros t1 HSN1. induction HSN1 as [t1 Hred1 IH1].
  intros T1 T2 HR1 t2 HSN2. induction HSN2 as [t2 Hred2 IH2].
  intros HR2.
  assert (Hclos1 : forall T0 b, t1 -->* tm_abs T0 b -> forall u, RR T1 u -> RR T2 (open b u)).
  { intros T0 b Hm u Hu. simpl in HR1.
    apply (proj2 (proj2 HR1)) with (T0 := T0) (b := b); assumption. }
  assert (Hreds : forall s, tm_app t1 t2 --> s -> RR T2 s).
  { intros s Hst. inversion Hst; subst.
    - apply Hclos1 with (T0 := T) (b := t). apply multi_refl. assumption.
    - apply IH1 with (T1 := T1) (T2 := T2) (t2 := t2).
      + assumption.
      + apply RR_step with (t := t1); assumption.
      + apply RR_SN with (T := T1). assumption.
      + assumption.
    - apply IH2.
      + assumption.
      + apply RR_step with (t := t2); assumption. }
  assert (HSNapp : strongly_normalizing (tm_app t1 t2)).
  { apply SN_intro. intros s Hst. apply RR_SN with (T := T2). apply Hreds. assumption. }
  assert (Hlcapp : locally_closed (tm_app t1 t2)).
  { simpl. apply lc_app. apply RR_lc with (T := Ty_Arrow T1 T2). assumption.
    apply RR_lc with (T := T1). assumption. }
  destruct T2 as [| T3 T4].
  - simpl. split; assumption.
  - simpl. split; [| split]; [assumption | assumption |].
    intros T0 c Hm w Hw.
    destruct (multi_step_inv _ _ Hm) as [Heq | [y [Hst Hrest]]].
    + discriminate Heq.
    + apply Hreds in Hst. simpl in Hst. destruct Hst as [_ [_ Hclosy]].
      apply Hclosy with (T0 := T0) (b := c); assumption.
Qed.

Lemma RR_if : forall T (c : tm), strongly_normalizing c ->
  forall a b, RR Ty_Bool c -> RR T a -> RR T b -> RR T (tm_if c a b).
Proof.
  intros T c HSN. induction HSN as [c Hred IH].
  intros a b HRc HRa HRb.
  assert (Hreds : forall s, tm_if c a b --> s -> RR T s).
  { intros s Hst. inversion Hst; subst.
    - assumption.
    - assumption.
    - apply IH.
      + assumption.
      + apply RR_step with (t := c); assumption.
      + assumption.
      + assumption. }
  assert (HSNif : strongly_normalizing (tm_if c a b)).
  { apply SN_intro. intros s Hst. apply RR_SN with (T := T). apply Hreds. assumption. }
  assert (Hlcif : locally_closed (tm_if c a b)).
  { simpl. apply lc_if. apply RR_lc with (T := Ty_Bool). assumption.
    apply RR_lc with (T := T). assumption. apply RR_lc with (T := T). assumption. }
  destruct T as [| T3 T4].
  - simpl. split; assumption.
  - simpl. split; [| split]; [assumption | assumption |].
    intros T0 d Hm w Hw.
    destruct (multi_step_inv _ _ Hm) as [Heq | [y [Hst Hrest]]].
    + discriminate Heq.
    + apply Hreds in Hst. simpl in Hst. destruct Hst as [_ [_ Hclosy]].
      apply Hclosy with (T0 := T0) (b := d); assumption.
Qed.

(** ** Semantic typing (fundamental theorem) *)

Definition env_sem (Gamma : context) (sigma : atom -> tm) : Prop :=
  forall x T, Gamma x = Some T -> RR T (sigma x).

Lemma has_type_lc : forall Gamma t T, has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T H.
  refine (has_type_ind (fun Gamma t T => locally_closed t)
    (fun Gamma x T Hx => lc_fvar 0 x)
    (fun L Gamma0 T1 T2 t1 Hprem IHbody => _)
    (fun Gamma0 t1 t2 T1 T2 Hprem1 IH1 Hprem2 IH2 => _)
    (fun Gamma0 => lc_true 0)
    (fun Gamma0 => lc_false 0)
    (fun Gamma0 t1 t2 t3 T Hprem1 IH1 Hprem2 IH2 Hprem3 IH3 => _)
    Gamma t T H).
  - (* T_Abs *) apply lc_abs.
    destruct (fresh L) as [x Hx].
    specialize (IHbody x Hx). simpl in IHbody.
    apply lc_open_inv with (k := 0) (v := tm_fvar x).
    + assumption.
    + apply lc_fvar.
  - (* T_App *) apply lc_app; assumption.
  - (* T_If *) apply lc_if; assumption.
Qed.

Theorem fundamental : forall Gamma t T,
  has_type Gamma t T ->
  locally_closed t ->
  forall sigma, env_lc sigma -> env_sem Gamma sigma -> RR T (subst sigma t).
Proof.
  intros Gamma t T H.
  refine (has_type_ind
    (fun Gamma t T => locally_closed t ->
       forall sigma, env_lc sigma -> env_sem Gamma sigma -> RR T (subst sigma t))
    (fun Gamma x T Hx => _)
    (fun L Gamma0 T1 T2 t1 Hprem IHbody => _)
    (fun Gamma0 t1 t2 T1 T2 Hprem1 IH1 Hprem2 IH2 => _)
    (fun Gamma0 => _)
    (fun Gamma0 => _)
    (fun Gamma0 t1 t2 t3 T Hprem1 IH1 Hprem2 IH2 Hprem3 IH3 => _)
    Gamma t T H).
  - (* T_Var *) intros Hlc sigma Henv Hsem. simpl. apply Hsem. assumption.
  - (* T_Abs *) intros Hlc sigma Henv Hsem. simpl.
    apply lc_abs_inv in Hlc.
    split.
    + (* strong normalization *) apply SN_intro. intros s Hst. inversion Hst.
    + split.
      * (* local closure *) apply lc_abs. apply lc_at_subst with (k := 1); assumption.
      * (* the abstraction clause *)
        assert (Hbeta : forall v, RR T1 v -> RR T2 (open (subst sigma t1) v)).
        { intros v Hv.
          destruct (fresh_two L (fvs t1)) as [x [HxL Hxf]].
          assert (Hsem' : env_sem (update Gamma0 x T1) (env_update sigma x v)).
          { intros y T' Hy. unfold update in Hy. unfold env_update.
            destruct (Nat.eqb x y) eqn:E.
            - apply Nat.eqb_eq in E. subst y. inversion Hy. subst T'. exact Hv.
            - apply (Hsem y T'). assumption. }
          assert (Henv' : env_lc (env_update sigma x v)).
          { apply env_update_lc; [assumption | apply RR_lc with (T := T1); assumption]. }
          assert (Hopenlc : locally_closed (open t1 (tm_fvar x))).
          { simpl. apply lc_open_rec with (k := 0); [assumption | apply lc_fvar]. }
          specialize (IHbody x HxL Hopenlc (env_update sigma x v) Henv' Hsem').
          rewrite (subst_open_env sigma x v t1 Henv (RR_lc _ _ Hv) Hxf) in IHbody.
          exact IHbody. }
        intros T0 b Hm u Hu.
        pose proof (multi_abs (tm_abs T1 (subst sigma t1)) (tm_abs T0 b) Hm
                      T1 (subst sigma t1) eq_refl) as Heq.
        inversion Heq. subst. apply Hbeta. assumption.
  - (* T_App *) intros Hlc sigma Henv Hsem. simpl.
    apply lc_app_inv in Hlc. destruct Hlc as [Hlc1 Hlc2].
    apply RR_app with (T1 := T1) (T2 := T2).
    + apply RR_SN with (T := Ty_Arrow T1 T2). apply IH1; assumption.
    + apply IH1; assumption.
    + apply RR_SN with (T := T1). apply IH2; assumption.
    + apply IH2; assumption.
  - (* T_True *) intros Hlc sigma Henv Hsem. simpl.
    split; [apply SN_intro; intros s Hst; inversion Hst | apply lc_true].
  - (* T_False *) intros Hlc sigma Henv Hsem. simpl.
    split; [apply SN_intro; intros s Hst; inversion Hst | apply lc_false].
  - (* T_If *) intros Hlc sigma Henv Hsem. simpl.
    apply lc_if_inv in Hlc. destruct Hlc as [Hlc1 [Hlc2 Hlc3]].
    apply RR_if with (T := T).
    + apply RR_SN with (T := Ty_Bool). apply IH1; assumption.
    + apply IH1; assumption.
    + apply IH2; assumption.
    + apply IH3; assumption.
Qed.

(** Target theorem: strong normalization for the supplied CBV relation. *)

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T H.
  assert (HR : RR T (subst ids t)).
  { eapply fundamental.
    - exact H.
    - exact (has_type_lc empty t T H).
    - intros x. apply lc_fvar.
    - intros x T' Hx. unfold empty in Hx. discriminate. }
  rewrite subst_ids in HR.
  apply RR_SN with (T := T). exact HR.
Qed.

End STLCCBVNormalizationTask.
