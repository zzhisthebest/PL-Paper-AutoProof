(** STLC call-by-value strong-normalization benchmark task. *)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Relations.Relation_Definitions.
From Stdlib Require Import micromega.Lia.

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
(** * Infrastructure for the strong normalization proof *)

(** ** Free variables and freshness *)

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

Fixpoint fresh (L : list atom) : atom :=
  match L with
  | nil => 0
  | a :: L' => Nat.max (S a) (fresh L')
  end.

Lemma fresh_not_In : forall (L : list atom) (x : atom), In x L -> x < fresh L.
Proof.
  intros L. induction L as [| a L' IH].
  - intros x Hx. inversion Hx.
  - intros x Hx. destruct Hx as [Heq | Hx].
    + subst a. apply Nat.lt_le_trans with (S x).
      * apply Nat.lt_succ_diag_r.
      * change (S x <= Nat.max (S x) (fresh L')). apply Nat.le_max_l.
    + apply Nat.lt_le_trans with (fresh L').
      * apply IH; assumption.
      * change (fresh L' <= Nat.max (S a) (fresh L')). apply Nat.le_max_r.
Qed.

Lemma fresh_spec : forall (L : list atom), ~ In (fresh L) L.
Proof.
  intros L Hx. pose proof (fresh_not_In L (fresh L) Hx). lia.
Qed.

Lemma fresh_not_In_app_l : forall (L M : list atom), ~ In (fresh (L ++ M)) L.
Proof.
  intros L M H. apply (fresh_spec (L ++ M)). apply in_or_app. left. exact H.
Qed.

Lemma fresh_not_In_app_r : forall (L M : list atom), ~ In (fresh (L ++ M)) M.
Proof.
  intros L M H. apply (fresh_spec (L ++ M)). apply in_or_app. right. exact H.
Qed.

(** ** Free-variable substitution *)

Definition upd (s : atom -> tm) (x : atom) (u : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then u else s y.

Fixpoint subst (s : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => s x
  | tm_app t1 t2 => tm_app (subst s t1) (subst s t2)
  | tm_abs T t1 => tm_abs T (subst s t1)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (subst s t1) (subst s t2) (subst s t3)
  end.

Lemma subst_id : forall (t : tm), subst (fun x => tm_fvar x) t = t.
Proof.
  induction t; simpl; try reflexivity; try congruence.
Qed.

Lemma upd_eq : forall (s : atom -> tm) (x : atom) (u : tm), upd s x u x = u.
Proof. intros. unfold upd. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma upd_neq : forall (s : atom -> tm) (x y : atom) (u : tm),
  y <> x -> upd s x u y = s y.
Proof.
  intros s x y u H. unfold upd. destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E. congruence.
  - reflexivity.
Qed.

Lemma update_eq : forall (Gamma : context) (x : atom) (T : ty),
  update Gamma x T x = Some T.
Proof. intros. unfold update. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma update_neq : forall (Gamma : context) (x y : atom) (T : ty),
  y <> x -> update Gamma x T y = Gamma y.
Proof.
  intros Gamma x y T H. unfold update. destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E. congruence.
  - reflexivity.
Qed.

(** ** Basic facts about [strongly_normalizing] *)

Lemma strong_norm_step : forall (t t' : tm),
  strongly_normalizing t -> t --> t' -> strongly_normalizing t'.
Proof.
  intros t t' Hsn. revert t'.
  induction Hsn as [t Hred IH].
  intros t' Hstep. apply Hred. exact Hstep.
Qed.

Lemma SN_abs : forall (T : ty) (t : tm), strongly_normalizing (tm_abs T t).
Proof.
  intros T t. apply SN_intro. intros t' Hstep.
  inversion Hstep.
Qed.

Lemma SN_true : strongly_normalizing tm_true.
Proof.
  apply SN_intro. intros t' Hstep. inversion Hstep.
Qed.

Lemma SN_false : strongly_normalizing tm_false.
Proof.
  apply SN_intro. intros t' Hstep. inversion Hstep.
Qed.

(** ** Inversion principles for the step relation and values *)

Lemma step_abs_inv : forall (T : ty) (t t' : tm), ~ (tm_abs T t --> t').
Proof. intros T t t' H. inversion H. Qed.

Lemma value_app_inv : forall (t1 t2 : tm), ~ value (tm_app t1 t2).
Proof. intros t1 t2 H. inversion H. Qed.

Lemma value_if_inv : forall (t1 t2 t3 : tm), ~ value (tm_if t1 t2 t3).
Proof. intros t1 t2 t3 H. inversion H. Qed.

Lemma step_app_inv : forall (t1 t2 r : tm),
  tm_app t1 t2 --> r ->
  (exists (T0 : ty) (t0 : tm),
      t1 = tm_abs T0 t0 /\ locally_closed (tm_abs T0 t0) /\
      value t2 /\ r = open t0 t2)
  \/ (exists t1', t1 --> t1' /\ locally_closed t2 /\ r = tm_app t1' t2)
  \/ (exists (v1 t2' : tm),
      t1 = v1 /\ value v1 /\ t2 --> t2' /\ r = tm_app v1 t2').
Proof.
  intros t1 t2 r H. inversion H; subst.
  - left. eexists. eexists. repeat split; eauto.
  - right. left. eexists. repeat split; eauto.
  - right. right. eexists. eexists. repeat split; eauto.
Qed.

Lemma step_if_inv : forall (t1 t2 t3 r : tm),
  tm_if t1 t2 t3 --> r ->
  (t1 = tm_true /\ locally_closed t2 /\ locally_closed t3 /\ r = t2)
  \/ (t1 = tm_false /\ locally_closed t2 /\ locally_closed t3 /\ r = t3)
  \/ (exists t1', t1 --> t1' /\ locally_closed t2 /\ locally_closed t3 /\
        r = tm_if t1' t2 t3).
Proof.
  intros t1 t2 t3 r H. inversion H; subst.
  - left. repeat split; eauto.
  - right. left. repeat split; eauto.
  - right. right. eexists. repeat split; eauto.
Qed.

Lemma multi_first : forall (t w : tm),
  multi step t w -> w = t \/ (exists z, step t z /\ multi step z w).
Proof.
  intros t w H. induction H as [x | x y z Hxy Hyz IH].
  - left. reflexivity.
  - right. exists y. split; assumption.
Qed.

(** ** Locally-closed terms *)

Lemma lc_bvar_inv : forall (k : nat) (i : nat), lc_at k (tm_bvar i) -> i < k.
Proof. intros k i H. inversion H; subst. assumption. Qed.

Lemma lc_app_inv : forall (k : nat) (t1 t2 : tm),
  lc_at k (tm_app t1 t2) -> lc_at k t1 /\ lc_at k t2.
Proof. intros k t1 t2 H. inversion H; subst. split; assumption. Qed.

Lemma lc_abs_inv : forall (k : nat) (T : ty) (t : tm),
  lc_at k (tm_abs T t) -> lc_at (S k) t.
Proof. intros k T t H. inversion H; subst. assumption. Qed.

Lemma lc_if_inv : forall (k : nat) (t1 t2 t3 : tm),
  lc_at k (tm_if t1 t2 t3) -> lc_at k t1 /\ lc_at k t2 /\ lc_at k t3.
Proof. intros k t1 t2 t3 H. inversion H; subst. split; [assumption | split; assumption]. Qed.

Lemma lc_at_mono : forall (t : tm) (k k' : nat),
  lc_at k t -> k <= k' -> lc_at k' t.
Proof.
  intros t. induction t; intros k k' H Hle.
  - (* bvar *) apply lc_bvar. apply lc_bvar_inv in H. lia.
  - (* fvar *) apply lc_fvar.
  - (* app *) apply lc_app_inv in H. destruct H as [H1 H2]. apply lc_app.
    + apply IHt1 with (k := k); assumption || lia.
    + apply IHt2 with (k := k); assumption || lia.
  - (* abs *) apply lc_abs_inv in H. apply lc_abs.
    apply IHt with (k := S k); [assumption | lia].
  - (* true *) apply lc_true.
  - (* false *) apply lc_false.
  - (* if *) apply lc_if_inv in H. destruct H as [H1 [H2 H3]]. apply lc_if.
    + apply IHt1 with (k := k); assumption || lia.
    + apply IHt2 with (k := k); assumption || lia.
    + apply IHt3 with (k := k); assumption || lia.
Qed.

Lemma lc_at_open_id : forall (t : tm) (j k : nat) (u : tm),
  lc_at k t -> k <= j -> open_rec j u t = t.
Proof.
  intros t. induction t; intros j k u Hlc Hle; simpl.
  - (* bvar *) destruct (Nat.eqb j n) eqn:E.
    + exfalso. apply Nat.eqb_eq in E. subst n. apply lc_bvar_inv in Hlc. lia.
    + reflexivity.
  - reflexivity.
  - (* app *) apply lc_app_inv in Hlc. destruct Hlc as [H1 H2].
    rewrite IHt1 with (j := j) (k := k); auto.
    rewrite IHt2 with (j := j) (k := k); auto.
  - (* abs *) apply lc_abs_inv in Hlc.
    rewrite IHt with (j := S j) (k := S k); auto. lia.
  - reflexivity.
  - reflexivity.
  - (* if *) apply lc_if_inv in Hlc. destruct Hlc as [H1 [H2 H3]].
    rewrite IHt1 with (j := j) (k := k); auto.
    rewrite IHt2 with (j := j) (k := k); auto.
    rewrite IHt3 with (j := j) (k := k); auto.
Qed.

Lemma lc_at_open : forall (t u : tm) (k : nat),
  lc_at (S k) t -> lc_at k u -> lc_at k (open_rec k u t).
Proof.
  intros t. induction t; intros u k Ht Hu; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. exact Hu.
    + apply Nat.eqb_neq in E. apply lc_bvar. apply lc_bvar_inv in Ht. lia.
  - apply lc_fvar.
  - apply lc_app_inv in Ht. destruct Ht as [H1 H2]. apply lc_app.
    + apply IHt1 with (u := u) (k := k); assumption.
    + apply IHt2 with (u := u) (k := k); assumption.
  - apply lc_abs_inv in Ht. apply lc_abs.
    apply IHt with (u := u) (k := S k).
    + assumption.
    + apply lc_at_mono with (k := k); [assumption | lia].
  - apply lc_true.
  - apply lc_false.
  - apply lc_if_inv in Ht. destruct Ht as [H1 [H2 H3]]. apply lc_if.
    + apply IHt1 with (u := u) (k := k); assumption.
    + apply IHt2 with (u := u) (k := k); assumption.
    + apply IHt3 with (u := u) (k := k); assumption.
Qed.

Lemma lc_at_open_fvar_inv : forall (j : nat) (x : atom) (t : tm),
  lc_at j (open_rec j (tm_fvar x) t) -> lc_at (S j) t.
Proof.
  intros j x t. revert j. induction t; intros j H; simpl in H.
  - destruct (Nat.eqb j n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. apply lc_bvar. lia.
    + apply Nat.eqb_neq in E. apply lc_bvar. apply lc_bvar_inv in H. lia.
  - apply lc_fvar.
  - apply lc_app_inv in H. destruct H as [H1 H2]. apply lc_app.
    + apply IHt1 with (j := j); assumption.
    + apply IHt2 with (j := j); assumption.
  - apply lc_abs_inv in H. apply lc_abs.
    apply IHt with (j := S j) in H. exact H.
  - apply lc_true.
  - apply lc_false.
  - apply lc_if_inv in H. destruct H as [H1 [H2 H3]]. apply lc_if.
    + apply IHt1 with (j := j); assumption.
    + apply IHt2 with (j := j); assumption.
    + apply IHt3 with (j := j); assumption.
Qed.

Lemma lc_at_subst : forall (t : tm) (k : nat) (s : atom -> tm),
  lc_at k t -> (forall x, lc_at k (s x)) -> lc_at k (subst s t).
Proof.
  induction t; intros k s Ht Hs; simpl.
  - apply lc_bvar. apply lc_bvar_inv in Ht. assumption.
  - apply Hs.
  - apply lc_app_inv in Ht. destruct Ht as [H1 H2]. apply lc_app.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
  - apply lc_abs_inv in Ht. apply lc_abs.
    apply IHt with (k := S k).
    + exact Ht.
    + intros x. apply lc_at_mono with (k := k); [apply Hs | lia].
  - apply lc_true.
  - apply lc_false.
  - apply lc_if_inv in Ht. destruct Ht as [H1 [H2 H3]].
    apply lc_if.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
    + apply IHt3; assumption.
Qed.

Lemma lc_step : forall (t t' : tm),
  t --> t' -> lc_at 0 t -> lc_at 0 t'.
Proof.
  intros t t' Hstep. induction Hstep; intros Hlc.
  - (* ST_AppAbs *) apply lc_app_inv in Hlc. destruct Hlc as [H1 H2].
    apply lc_abs_inv in H1.
    apply lc_at_open with (t := t) (u := v); assumption.
  - (* ST_App1 *) apply lc_app_inv in Hlc. destruct Hlc as [H1 H2].
    apply lc_app; [apply IHHstep | ]; assumption.
  - (* ST_App2 *) apply lc_app_inv in Hlc. destruct Hlc as [H1 H2].
    apply lc_app; [| apply IHHstep]; assumption.
  - (* ST_IfTrue *) apply lc_if_inv in Hlc. destruct Hlc as [H1 [H2 H3]]. exact H2.
  - (* ST_IfFalse *) apply lc_if_inv in Hlc. destruct Hlc as [H1 [H2 H3]]. exact H3.
  - (* ST_If *) apply lc_if_inv in Hlc. destruct Hlc as [H1 [H2 H3]].
    apply lc_if; [apply IHHstep | | ]; assumption.
Qed.

Lemma has_type_lc : forall (Gamma : context) (t : tm) (T : ty),
  has_type Gamma t T -> lc_at 0 t.
Proof.
  intros Gamma t T Hty.
  induction Hty as [Gamma0 x T0 Heq
                  | L Gamma0 T1 T2 t1 Hprem IH
                  | Gamma0 t1 t2 T1 T2 H1 H2 IH1 IH2
                  | Gamma0
                  | Gamma0
                  | Gamma0 t1 t2 t3 T0 H1 H2 H3 IH1 IH2 IH3].
  - (* T_Var *) apply lc_fvar.
  - (* T_Abs *) apply lc_abs.
    apply lc_at_open_fvar_inv with (x := fresh (L ++ fv t1)).
    apply (IH (fresh (L ++ fv t1)) (fresh_not_In_app_l L (fv t1))).
  - (* T_App *) apply lc_app; assumption.
  - (* T_True *) apply lc_true.
  - (* T_False *) apply lc_false.
  - (* T_If *) apply lc_if; assumption.
Qed.

(** ** The substitution/opening commutation lemma *)

Lemma subst_open_gen : forall (t : tm) (s : atom -> tm) (x : atom) (u : tm) (k : nat),
  ~ In x (fv t) ->
  (forall y, lc_at 0 (s y)) ->
  lc_at 0 u ->
  subst (upd s x u) (open_rec k (tm_fvar x) t) = open_rec k u (subst s t).
Proof.
  induction t; intros s x u k Hfv Hs Hu; simpl.
  - (* bvar *) destruct (Nat.eqb k n) eqn:E; simpl.
    + apply upd_eq.
    + reflexivity.
  - (* fvar *) destruct (Nat.eqb x a) eqn:E.
    + exfalso. apply Hfv. apply Nat.eqb_eq in E. subst a. left. reflexivity.
    + assert (Hneq : a <> x) by (apply Nat.eqb_neq in E; congruence).
      rewrite (upd_neq s x a u Hneq).
      symmetry. apply lc_at_open_id with (k := 0); [apply Hs | lia].
  - (* app *)
    assert (Hfv1 : ~ In x (fv t1))
      by (intro H; apply Hfv; apply in_or_app; left; exact H).
    assert (Hfv2 : ~ In x (fv t2))
      by (intro H; apply Hfv; apply in_or_app; right; exact H).
    rewrite (IHt1 s x u k Hfv1 Hs Hu).
    rewrite (IHt2 s x u k Hfv2 Hs Hu).
    reflexivity.
  - (* abs *)
    rewrite (IHt s x u (S k) Hfv Hs Hu). reflexivity.
  - reflexivity.
  - reflexivity.
  - (* if *)
    assert (Hfv1 : ~ In x (fv t1))
      by (intro H; apply Hfv; apply in_or_app; left; exact H).
    assert (Hfv2 : ~ In x (fv t2))
      by (intro H; apply Hfv; apply in_or_app; right; apply in_or_app; left; exact H).
    assert (Hfv3 : ~ In x (fv t3))
      by (intro H; apply Hfv; apply in_or_app; right; apply in_or_app; right; exact H).
    rewrite (IHt1 s x u k Hfv1 Hs Hu).
    rewrite (IHt2 s x u k Hfv2 Hs Hu).
    rewrite (IHt3 s x u k Hfv3 Hs Hu).
    reflexivity.
Qed.

Lemma subst_open : forall (t : tm) (s : atom -> tm) (x : atom) (u : tm),
  ~ In x (fv t) ->
  (forall y, lc_at 0 (s y)) ->
  lc_at 0 u ->
  subst (upd s x u) (open t (tm_fvar x)) = open (subst s t) u.
Proof.
  intros. unfold open. apply subst_open_gen; assumption.
Qed.

(** ** The logical relation *)

Fixpoint LR (T : ty) (t : tm) : Prop :=
  match T with
  | Ty_Bool => lc_at 0 t /\ strongly_normalizing t
  | Ty_Arrow T1 T2 =>
      lc_at 0 t /\ strongly_normalizing t /\
      (forall (t' : tm), multi step t t' -> value t' ->
        forall (u : tm), LR T1 u -> LR T2 (tm_app t' u))
  end.

Lemma LR_SN : forall (T : ty) (t : tm), LR T t -> strongly_normalizing t.
Proof.
  intros T t H. destruct T as [| T1 T2]; simpl in H.
  - destruct H as [_ H]. exact H.
  - destruct H as [_ [H _]]. exact H.
Qed.

Lemma LR_lc : forall (T : ty) (t : tm), LR T t -> lc_at 0 t.
Proof.
  intros T t H. destruct T as [| T1 T2]; simpl in H.
  - destruct H as [H _]. exact H.
  - destruct H as [H _]. exact H.
Qed.

Lemma LR_forward : forall (T : ty) (t t' : tm),
  LR T t -> t --> t' -> LR T t'.
Proof.
  intros T t t' HLR Hstep.
  destruct T as [| A B]; simpl in *.
  - destruct HLR as [Hlc Hsn]. split.
    + apply lc_step with (t := t); assumption.
    + apply strong_norm_step with (t := t); assumption.
  - destruct HLR as [Hlc [Hsn Hvr]]. split; [| split].
    + apply lc_step with (t := t); assumption.
    + apply strong_norm_step with (t := t); assumption.
    + intros t'' Hmulti Hval u HLRu.
      apply Hvr with (t' := t''); auto.
      apply multi_step with (y := t'); auto.
Qed.

(** ** Application of an abstraction to an argument in the relation *)

Lemma LR_app_abs : forall (T1 T2 : ty) (t' u : tm),
  lc_at 0 (tm_abs T1 t') ->
  (forall (w : tm), LR T1 w -> LR T2 (open t' w)) ->
  LR T1 u ->
  LR T2 (tm_app (tm_abs T1 t') u).
Proof.
  intros T1 T2 t' u Hlc Hsub HLRu.
  pose proof (LR_SN _ _ HLRu) as HSNu.
  revert T2 t' Hlc Hsub HLRu.
  induction HSNu as [u Hred IHu].
  intros T2 t' Hlc Hsub HLRu.
  assert (HLcu : lc_at 0 u) by (apply (LR_lc _ _ HLRu)).
  destruct T2 as [| C D]; simpl.
  - (* T2 = Bool *)
    split.
    + apply lc_app; assumption.
    + apply SN_intro. intros r Hstep.
      destruct (step_app_inv _ _ _ Hstep)
        as [[T0 [t0 [Heq [Hlc0 [Hval Hr]]]]]
           | [[t1' [Hstep1 [Hlc2 Hr]]]
           | [v1 [t2' [Heq [Hval1 [Hstep2 Hr]]]]]]].
      * injection Heq as HT Ht. subst T0 t0. subst r.
        destruct (Hsub u HLRu) as [_ Hsn]. exact Hsn.
      * exfalso. apply (step_abs_inv T1 t' t1'). exact Hstep1.
      * subst v1. subst r.
        destruct (IHu t2' Hstep2 Ty_Bool t' Hlc Hsub (LR_forward T1 u t2' HLRu Hstep2))
          as [_ Hsn].
        exact Hsn.
  - (* T2 = C -> D *)
    split; [| split].
    + apply lc_app; assumption.
    + apply SN_intro. intros r Hstep.
      destruct (step_app_inv _ _ _ Hstep)
        as [[T0 [t0 [Heq [Hlc0 [Hval Hr]]]]]
           | [[t1' [Hstep1 [Hlc2 Hr]]]
           | [v1 [t2' [Heq [Hval1 [Hstep2 Hr]]]]]]].
      * injection Heq as HT Ht. subst T0 t0. subst r.
        destruct (Hsub u HLRu) as [_ [Hsn _]]. exact Hsn.
      * exfalso. apply (step_abs_inv T1 t' t1'). exact Hstep1.
      * subst v1. subst r.
        destruct (IHu t2' Hstep2 (Ty_Arrow C D) t' Hlc Hsub (LR_forward T1 u t2' HLRu Hstep2))
          as [_ [Hsn _]].
        exact Hsn.
    + intros w Hmulti Hval v HLRv.
      destruct (multi_first _ _ Hmulti) as [Heq | [z [Hstep Hmulti']]].
      * subst w. exfalso. exact (value_app_inv (tm_abs T1 t') u Hval).
      * destruct (step_app_inv _ _ _ Hstep)
          as [[T0 [t0 [Heq [Hlc0 [Hval2 Hr]]]]]
             | [[t1' [Hstep1 [Hlc2 Hr]]]
             | [v1 [t2' [Heq [Hval1 [Hstep2 Hr]]]]]]].
        -- injection Heq as HT Ht. subst T0 t0. subst z.
           destruct (Hsub u HLRu) as [_ [_ Hvr]].
           apply (Hvr w); auto.
        -- exfalso. apply (step_abs_inv T1 t' t1'). exact Hstep1.
        -- subst v1. subst z.
           destruct (IHu t2' Hstep2 (Ty_Arrow C D) t' Hlc Hsub (LR_forward T1 u t2' HLRu Hstep2))
             as [_ [_ Hvr]].
           apply (Hvr w); auto.
Qed.

(** ** If-then-else in the relation *)

Lemma LR_if : forall (T : ty) (t1 t2 t3 : tm),
  LR Ty_Bool t1 -> LR T t2 -> LR T t3 -> LR T (tm_if t1 t2 t3).
Proof.
  intros T t1 t2 t3 HLR1 HLR2 HLR3.
  pose proof (LR_SN _ _ HLR1) as HSN1.
  revert T t2 t3 HLR2 HLR3.
  induction HSN1 as [t1 Hred IH].
  intros T t2 t3 HLR2 HLR3.
  assert (Hlc1 : lc_at 0 t1) by (apply (LR_lc _ _ HLR1)).
  destruct T as [| C D]; simpl.
  - (* T = Bool *)
    split.
    + apply lc_if; [assumption | apply (LR_lc _ _ HLR2) | apply (LR_lc _ _ HLR3)].
    + apply SN_intro. intros r Hstep.
      destruct (step_if_inv _ _ _ _ Hstep)
        as [[Heq [Hl2 [Hl3 Hr]]] | [[Heq [Hl2 [Hl3 Hr]]] | [t1' [Hstep1 [Hl2 [Hl3 Hr]]]]]].
      * subst t1. subst r. destruct HLR2 as [_ Hsn]. exact Hsn.
      * subst t1. subst r. destruct HLR3 as [_ Hsn]. exact Hsn.
      * subst r. destruct (IH t1' Hstep1 (LR_forward _ _ _ HLR1 Hstep1) Ty_Bool t2 t3 HLR2 HLR3) as [_ Hsn]. exact Hsn.
  - (* T = C -> D *)
    split; [| split].
    + apply lc_if; [assumption | apply (LR_lc _ _ HLR2) | apply (LR_lc _ _ HLR3)].
    + apply SN_intro. intros r Hstep.
      destruct (step_if_inv _ _ _ _ Hstep)
        as [[Heq [Hl2 [Hl3 Hr]]] | [[Heq [Hl2 [Hl3 Hr]]] | [t1' [Hstep1 [Hl2 [Hl3 Hr]]]]]].
      * subst t1. subst r. destruct HLR2 as [_ [Hsn _]]. exact Hsn.
      * subst t1. subst r. destruct HLR3 as [_ [Hsn _]]. exact Hsn.
      * subst r. destruct (IH t1' Hstep1 (LR_forward _ _ _ HLR1 Hstep1) (Ty_Arrow C D) t2 t3 HLR2 HLR3) as [_ [Hsn _]]. exact Hsn.
    + intros w Hmulti Hval v HLRv.
      destruct (multi_first _ _ Hmulti) as [Heq | [z [Hstep Hmulti']]].
      * subst w. exfalso. exact (value_if_inv t1 t2 t3 Hval).
      * destruct (step_if_inv _ _ _ _ Hstep)
          as [[Heq [Hl2 [Hl3 Hr]]] | [[Heq [Hl2 [Hl3 Hr]]] | [t1' [Hstep1 [Hl2 [Hl3 Hr]]]]]].
        -- subst t1. subst z. destruct HLR2 as [_ [_ Hvr]]. apply (Hvr w); auto.
        -- subst t1. subst z. destruct HLR3 as [_ [_ Hvr]]. apply (Hvr w); auto.
        -- subst z. destruct (IH t1' Hstep1 (LR_forward _ _ _ HLR1 Hstep1) (Ty_Arrow C D) t2 t3 HLR2 HLR3) as [_ [_ Hvr]].
           apply (Hvr w); auto.
Qed.

(** ** Application in the relation *)

Lemma LR_app_value : forall (A B : ty) (t u : tm),
  value t -> LR (Ty_Arrow A B) t -> LR A u -> LR B (tm_app t u).
Proof.
  intros A B t u Hval HLRt HLRu.
  destruct HLRt as [_ [_ Hvr]].
  apply (Hvr t); auto.
  apply multi_refl.
Qed.

Lemma LR_app : forall (A B : ty) (t u : tm),
  LR (Ty_Arrow A B) t -> LR A u -> LR B (tm_app t u).
Proof.
  intros A B t u HLRt HLRu.
  pose proof (LR_SN _ _ HLRt) as HSNt.
  revert A B u HLRt HLRu.
  induction HSNt as [t Hredt IHt].
  intros A B u HLRt HLRu.
  pose proof (LR_SN _ _ HLRu) as HSNu.
  revert A B HLRt HLRu.
  induction HSNu as [u Hredu IHu].
  intros A B HLRt HLRu.
  destruct B as [| C D]; simpl.
  - (* B = Bool *)
    split.
    + apply lc_app; [apply (LR_lc _ _ HLRt) | apply (LR_lc _ _ HLRu)].
    + apply SN_intro. intros r Hstep.
      destruct (step_app_inv _ _ _ Hstep)
        as [[T0 [t0 [Heq [Hlc0 [Hval Hr]]]]]
           | [[t1' [Hstep1 [Hlc2 Hr]]]
           | [v1 [t2' [Heq [Hval1 [Hstep2 Hr]]]]]]].
      * subst t. subst r.
        pose proof (LR_app_value A Ty_Bool (tm_abs T0 t0) u (v_abs T0 t0 Hlc0) HLRt HLRu)
          as HLRapp.
        apply strong_norm_step with (t := tm_app (tm_abs T0 t0) u).
        -- apply (LR_SN _ _ HLRapp).
        -- exact Hstep.
      * subst r.
        destruct (IHt t1' Hstep1 A Ty_Bool u (LR_forward _ _ _ HLRt Hstep1) HLRu) as [_ Hsn].
        exact Hsn.
      * subst r. subst v1.
        destruct (IHu t2' Hstep2 A Ty_Bool HLRt (LR_forward _ _ _ HLRu Hstep2)) as [_ Hsn].
        exact Hsn.
  - (* B = C -> D *)
    split; [| split].
    + apply lc_app; [apply (LR_lc _ _ HLRt) | apply (LR_lc _ _ HLRu)].
    + apply SN_intro. intros r Hstep.
      destruct (step_app_inv _ _ _ Hstep)
        as [[T0 [t0 [Heq [Hlc0 [Hval Hr]]]]]
           | [[t1' [Hstep1 [Hlc2 Hr]]]
           | [v1 [t2' [Heq [Hval1 [Hstep2 Hr]]]]]]].
      * subst t. subst r.
        pose proof (LR_app_value A (Ty_Arrow C D) (tm_abs T0 t0) u (v_abs T0 t0 Hlc0) HLRt HLRu)
          as HLRapp.
        apply strong_norm_step with (t := tm_app (tm_abs T0 t0) u).
        -- apply (LR_SN _ _ HLRapp).
        -- exact Hstep.
      * subst r.
        destruct (IHt t1' Hstep1 A (Ty_Arrow C D) u (LR_forward _ _ _ HLRt Hstep1) HLRu) as [_ [Hsn _]].
        exact Hsn.
      * subst r. subst v1.
        destruct (IHu t2' Hstep2 A (Ty_Arrow C D) HLRt (LR_forward _ _ _ HLRu Hstep2)) as [_ [Hsn _]].
        exact Hsn.
    + intros w Hmulti Hval v HLRv.
      destruct (multi_first _ _ Hmulti) as [Heq | [z [Hstep Hmulti']]].
      * subst w. exfalso. exact (value_app_inv t u Hval).
      * destruct (step_app_inv _ _ _ Hstep)
          as [[T0 [t0 [Heq [Hlc0 [Hval2 Hr]]]]]
             | [[t1' [Hstep1 [Hlc2 Hr]]]
             | [v1 [t2' [Heq [Hval1 [Hstep2 Hr]]]]]]].
        -- subst t. subst z.
           pose proof (LR_app_value A (Ty_Arrow C D) (tm_abs T0 t0) u (v_abs T0 t0 Hlc0) HLRt HLRu)
             as HLRapp.
           destruct HLRapp as [_ [_ Hvr2]].
           apply (Hvr2 w); auto.
        -- subst z.
           destruct (IHt t1' Hstep1 A (Ty_Arrow C D) u (LR_forward _ _ _ HLRt Hstep1) HLRu) as [_ [_ Hvr]].
           apply (Hvr w); auto.
        -- subst z. subst v1.
           destruct (IHu t2' Hstep2 A (Ty_Arrow C D) HLRt (LR_forward _ _ _ HLRu Hstep2)) as [_ [_ Hvr]].
           apply (Hvr w); auto.
Qed.

(** ** Semantic typing contexts and the fundamental theorem *)

Definition sem_ctx (Gamma : context) (sigma : atom -> tm) : Prop :=
  (forall (x : atom) (T : ty), Gamma x = Some T -> LR T (sigma x)) /\
  (forall (x : atom), lc_at 0 (sigma x)).

Theorem fundamental : forall (Gamma : context) (t : tm) (T : ty),
  has_type Gamma t T ->
  forall sigma, sem_ctx Gamma sigma -> LR T (subst sigma t).
Proof.
  intros Gamma t T Hty.
  induction Hty; intros sigma Hctx; simpl.
  - (* T_Var *) apply (proj1 Hctx). exact H.
  - (* T_Abs *)
    assert (Hlc1 : lc_at 1 t1).
    { pose proof (has_type_lc _ _ _ (T_Abs L Gamma T1 T2 t1 H)) as Hl.
      apply lc_abs_inv in Hl. exact Hl. }
    split.
    + (* locally closed *)
      apply lc_abs. apply lc_at_subst with (k := 1).
      * exact Hlc1.
      * intros y. apply lc_at_mono with (k := 0); [apply (proj2 Hctx) | lia].
    + split.
      * apply SN_abs.
      * intros t'' Hmulti Hval u HLRu.
        destruct (multi_first _ _ Hmulti) as [Heq | [z [Hstep _]]].
        -- subst t''.
           apply LR_app_abs with (t' := subst sigma t1).
           ++ apply lc_abs. apply lc_at_subst with (k := 1).
              ** exact Hlc1.
              ** intros y. apply lc_at_mono with (k := 0); [apply (proj2 Hctx) | lia].
           ++ intros w HLRw.
              (* pick a fresh variable *)
              pose (xff := fresh (L ++ fv t1)).
              assert (HxL : ~ In xff L).
              { subst xff. apply fresh_not_In_app_l. }
              assert (Hxfv : ~ In xff (fv t1)).
              { subst xff. apply fresh_not_In_app_r. }
              assert (Hsctx : sem_ctx (update Gamma xff T1) (upd sigma xff w)).
              { split.
                - intros y Ty Hy. simpl.
                  destruct (Nat.eqb xff y) eqn:E.
                  + apply Nat.eqb_eq in E. subst y.
                    rewrite update_eq in Hy. injection Hy as Hy. subst Ty.
                    rewrite upd_eq. exact HLRw.
                  + apply Nat.eqb_neq in E.
                    rewrite update_neq in Hy; [| congruence].
                    rewrite upd_neq; [| congruence].
                    apply (proj1 Hctx). exact Hy.
                - intros y. simpl.
                  destruct (Nat.eqb xff y) eqn:E.
                  + apply Nat.eqb_eq in E. subst y. rewrite upd_eq. apply (LR_lc _ _ HLRw).
                  + apply Nat.eqb_neq in E. rewrite upd_neq; [apply (proj2 Hctx) | congruence]. }
              pose proof (H0 xff HxL (upd sigma xff w) Hsctx) as Hres.
              rewrite (subst_open t1 sigma xff w Hxfv (proj2 Hctx) (LR_lc _ _ HLRw)) in Hres.
              exact Hres.
           ++ exact HLRu.
        -- exfalso. apply (step_abs_inv T1 (subst sigma t1) z). exact Hstep.
  - (* T_App *)
    apply LR_app with (A := T1).
    + apply IHHty1. exact Hctx.
    + apply IHHty2. exact Hctx.
  - (* T_True *) split; [apply lc_true | apply SN_true].
  - (* T_False *) split; [apply lc_false | apply SN_false].
  - (* T_If *)
    apply LR_if.
    + apply IHHty1. exact Hctx.
    + apply IHHty2. exact Hctx.
    + apply IHHty3. exact Hctx.
Qed.

(** ** The normalization theorem *)

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Hty.
  assert (Hsctx : sem_ctx empty (fun x => tm_fvar x)).
  { split.
    - intros x Ty Hx. unfold empty in Hx. discriminate.
    - intros x. apply lc_fvar. }
  pose proof (fundamental empty t T Hty (fun x => tm_fvar x) Hsctx) as HLR.
  rewrite subst_id in HLR.
  apply (LR_SN _ _ HLR).
Qed.

End STLCCBVNormalizationTask.
