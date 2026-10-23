(** STLC call-by-value strong-normalization benchmark task. *)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Relations.Relation_Definitions.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.

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

(** * Strong normalization proof infrastructure. *)

(** ** Fresh atoms *)

Fixpoint max_atom_list (L : list atom) : atom :=
  match L with
  | nil => 0
  | a :: L' => Nat.max a (max_atom_list L')
  end.

Lemma in_max_atom_list : forall L (x : atom), In x L -> x <= max_atom_list L.
Proof.
  induction L as [| a L IH]; intros x Hin; simpl in *.
  - destruct Hin.
  - destruct Hin as [Heq | Hin].
    + subst. apply Nat.le_max_l.
    + apply Nat.le_trans with (max_atom_list L).
      * apply IH. exact Hin.
      * apply Nat.le_max_r.
Qed.

Lemma exists_fresh : forall L : list atom, exists x : atom, ~ In x L.
Proof.
  intros L. exists (S (max_atom_list L)).
  intros Hin. pose proof (in_max_atom_list L _ Hin). lia.
Qed.

(** ** Free variables of a term *)

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

(** ** Substitution of free variables *)

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

Definition cons_env (sigma : atom -> tm) (x : atom) (u : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then u else sigma y.

Lemma cons_env_same : forall sigma x u, cons_env sigma x u x = u.
Proof. intros. unfold cons_env. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma cons_env_other : forall sigma x u y, x <> y -> cons_env sigma x u y = sigma y.
Proof.
  intros sigma x u y Hneq. unfold cons_env.
  destruct (Nat.eqb x y) eqn:E; auto.
  exfalso. apply Hneq. apply Nat.eqb_eq. exact E.
Qed.

Lemma subst_cons_notin : forall (sigma : atom -> tm) x u t,
  ~ In x (fv t) -> subst (cons_env sigma x u) t = subst sigma t.
Proof.
  intros sigma x u t. induction t as [i | y | t1 IHt1 t2 IHt2 | T b IHt | | | t1 IHt1 t2 IHt2 t3 IHt3]; simpl; intros H; auto.
  - (* tm_fvar *) apply cons_env_other. intro Heq. apply H. subst. left. reflexivity.
  - (* tm_app *)
    assert (H1 : ~ In x (fv t1)) by (intro Hin; apply H; apply List.in_app_iff; left; exact Hin).
    assert (H2 : ~ In x (fv t2)) by (intro Hin; apply H; apply List.in_app_iff; right; exact Hin).
    rewrite IHt1; auto. rewrite IHt2; auto.
  - (* tm_abs *)
    rewrite IHt; auto.
  - (* tm_if *)
    assert (H1 : ~ In x (fv t1)) by (intro Hin; apply H; apply List.in_app_iff; left; exact Hin).
    assert (H2 : ~ In x (fv t2)) by (intro Hin; apply H; apply List.in_app_iff; right; apply List.in_app_iff; left; exact Hin).
    assert (H3 : ~ In x (fv t3)) by (intro Hin; apply H; apply List.in_app_iff; right; apply List.in_app_iff; right; exact Hin).
    rewrite IHt1; auto. rewrite IHt2; auto. rewrite IHt3; auto.
Qed.

Lemma subst_id : forall t, subst (fun x => tm_fvar x) t = t.
Proof. induction t as [i | y | t1 IHt1 t2 IHt2 | T b IHt | | | t1 IHt1 t2 IHt2 t3 IHt3]; simpl; congruence. Qed.

(** ** Basic properties of local closure *)

Lemma lc_at_weaken : forall (t : tm) k1 k2, k1 <= k2 -> lc_at k1 t -> lc_at k2 t.
Proof.
  induction t as [i | y | t1 IHt1 t2 IHt2 | T b IHt | | | t1 IHt1 t2 IHt2 t3 IHt3]; intros k1 k2 Hle H; inversion H; subst.
  - apply lc_bvar. lia.
  - apply lc_fvar.
  - apply lc_app; eauto.
  - apply lc_abs. apply IHt with (k1 := S k1); [lia | assumption].
  - apply lc_true.
  - apply lc_false.
  - apply lc_if; eauto.
Qed.

Lemma lc_at_open_fvar : forall (t : tm) k x,
  lc_at k (open_rec k (tm_fvar x) t) <-> lc_at (S k) t.
Proof.
  induction t as [i | y | t1 IHt1 t2 IHt2 | T b IHt | | | t1 IHt1 t2 IHt2 t3 IHt3]; intros k x; simpl.
  - (* tm_bvar i *) destruct (Nat.eqb k i) eqn:E.
    + split; intros H.
      * apply lc_bvar. apply Nat.eqb_eq in E. lia.
      * apply lc_fvar.
    + assert (Hik : i <> k) by (intro Heq; rewrite Heq in E; rewrite Nat.eqb_refl in E; discriminate).
      split; intros H.
      * inversion H; subst. apply lc_bvar. lia.
      * inversion H; subst. apply lc_bvar. lia.
  - (* tm_fvar y *) split; intros H; apply lc_fvar.
  - (* tm_app t1 t2 *)
    split.
    + intros H. inversion H; subst. apply lc_app.
      * apply (proj1 (IHt1 k x)); assumption.
      * apply (proj1 (IHt2 k x)); assumption.
    + intros H. inversion H; subst. apply lc_app.
      * apply (proj2 (IHt1 k x)); assumption.
      * apply (proj2 (IHt2 k x)); assumption.
  - (* tm_abs T t *)
    split.
    + intros H. inversion H; subst. apply lc_abs.
      apply (proj1 (IHt (S k) x)); assumption.
    + intros H. inversion H; subst. apply lc_abs.
      apply (proj2 (IHt (S k) x)); assumption.
  - (* tm_true *) split; intros H; apply lc_true.
  - (* tm_false *) split; intros H; apply lc_false.
  - (* tm_if t1 t2 t3 *)
    split.
    + intros H. inversion H; subst. apply lc_if.
      * apply (proj1 (IHt1 k x)); assumption.
      * apply (proj1 (IHt2 k x)); assumption.
      * apply (proj1 (IHt3 k x)); assumption.
    + intros H. inversion H; subst. apply lc_if.
      * apply (proj2 (IHt1 k x)); assumption.
      * apply (proj2 (IHt2 k x)); assumption.
      * apply (proj2 (IHt3 k x)); assumption.
Qed.

Lemma lc_at_open : forall (t : tm) k u,
  lc_at (S k) t -> lc_at k u -> lc_at k (open_rec k u t).
Proof.
  induction t as [i | y | t1 IHt1 t2 IHt2 | T b IHt | | | t1 IHt1 t2 IHt2 t3 IHt3]; intros k u H Hu; simpl; inversion H; subst.
  - (* tm_bvar i *) destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst. exact Hu.
    + apply lc_bvar.
      assert (Hik : i <> k) by (intro Heq; rewrite Heq in E; rewrite Nat.eqb_refl in E; discriminate).
      lia.
  - (* tm_fvar *) apply lc_fvar.
  - (* tm_app *) apply lc_app; eauto.
  - (* tm_abs *) apply lc_abs. apply IHt with (k := S k).
    + assumption.
    + apply lc_at_weaken with (k1 := k); [lia | assumption].
  - (* tm_true *) apply lc_true.
  - (* tm_false *) apply lc_false.
  - (* tm_if *) apply lc_if; eauto.
Qed.

Lemma open_rec_lc : forall (t : tm) k u, lc_at k t -> open_rec k u t = t.
Proof.
  induction t as [i | y | t1 IHt1 t2 IHt2 | T b IHt | | | t1 IHt1 t2 IHt2 t3 IHt3]; intros k u H; simpl; inversion H; subst; auto.
  - (* tm_bvar i *) destruct (Nat.eqb k i) eqn:E; auto.
    apply Nat.eqb_eq in E. exfalso. lia.
  - (* tm_app *) rewrite IHt1; auto. rewrite IHt2; auto.
  - (* tm_abs *) rewrite IHt; auto.
  - (* tm_if *) rewrite IHt1; auto. rewrite IHt2; auto. rewrite IHt3; auto.
Qed.

Lemma lc_at_subst : forall (t : tm) k sigma,
  lc_at k t -> (forall x, lc_at k (sigma x)) -> lc_at k (subst sigma t).
Proof.
  induction t as [i | y | t1 IHt1 t2 IHt2 | T b IHt | | | t1 IHt1 t2 IHt2 t3 IHt3]; intros k sigma H Hsig; simpl; inversion H; subst.
  - (* tm_bvar *) apply lc_bvar. assumption.
  - (* tm_fvar *) apply Hsig.
  - (* tm_app *) apply lc_app; [apply IHt1 | apply IHt2]; assumption.
  - (* tm_abs *) apply lc_abs. apply IHt with (k := S k).
    + assumption.
    + intro x. apply lc_at_weaken with (k1 := k); [lia | apply Hsig].
  - (* tm_true *) apply lc_true.
  - (* tm_false *) apply lc_false.
  - (* tm_if *) apply lc_if; [apply IHt1 | apply IHt2 | apply IHt3]; assumption.
Qed.

Lemma lc_at_app_inv : forall k a b, lc_at k (tm_app a b) -> lc_at k a /\ lc_at k b.
Proof. intros k a b H; inversion H; auto. Qed.

Lemma lc_at_abs_inv : forall k T b, lc_at k (tm_abs T b) -> lc_at (S k) b.
Proof. intros k T b H; inversion H; auto. Qed.

Lemma lc_at_if_inv : forall k a b c, lc_at k (tm_if a b c) ->
  lc_at k a /\ lc_at k b /\ lc_at k c.
Proof. intros k a b c H; inversion H; auto. Qed.

(** ** Substitution commutes with opening *)

Lemma subst_open_rec : forall sigma k u t,
  (forall x, locally_closed (sigma x)) ->
  subst sigma (open_rec k u t) = open_rec k (subst sigma u) (subst sigma t).
Proof.
  intros sigma k u t Hsig. revert k u.
  induction t as [i | y | t1 IHt1 t2 IHt2 | T b IHt | | | t1 IHt1 t2 IHt2 t3 IHt3]; intros k u; simpl.
  - (* tm_bvar *) destruct (Nat.eqb k i) eqn:E; simpl; reflexivity.
  - (* tm_fvar *) simpl. symmetry. apply open_rec_lc.
    apply lc_at_weaken with (k1 := 0); [lia | apply Hsig].
  - (* tm_app *) rewrite IHt1; auto. rewrite IHt2; auto.
  - (* tm_abs *) rewrite IHt; auto.
  - (* tm_true *) reflexivity.
  - (* tm_false *) reflexivity.
  - (* tm_if *) rewrite IHt1; auto. rewrite IHt2; auto. rewrite IHt3; auto.
Qed.

(** ** Values *)

Lemma value_lc : forall t, value t -> locally_closed t.
Proof.
  intros t H. destruct H.
  - assumption.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma value_no_step : forall t, value t -> forall t', ~ step t t'.
Proof.
  intros t Hv t' Hs. destruct Hv.
  - inversion Hs.
  - inversion Hs.
  - inversion Hs.
Qed.

(** ** Local closure is preserved by stepping *)

Lemma step_lc_fwd : forall t t', step t t' -> locally_closed t -> locally_closed t'.
Proof.
  intros t t' H.
  induction H as [T t0 v Hlca Hval
                 | t1 t1' t2 Hs IHHs Hlc2
                 | v1 t2 t2' Hv Hs IHHs
                 | t1 t2 Hl1 Hl2
                 | t1 t2 Hl1 Hl2
                 | t1 t1' t2 t3 Hs IHHs Hl2 Hl3];
  intros Hlc; unfold locally_closed in *.
  - (* ST_AppAbs *)
    destruct (lc_at_app_inv _ _ _ Hlc) as [H1 H2].
    apply (lc_at_open t0 0 v).
    + apply lc_at_abs_inv in H1. exact H1.
    + exact H2.
  - (* ST_App1 *)
    destruct (lc_at_app_inv _ _ _ Hlc) as [H1 H2].
    apply lc_app.
    + apply IHHs. exact H1.
    + exact H2.
  - (* ST_App2 *)
    destruct (lc_at_app_inv _ _ _ Hlc) as [H1 H2].
    apply lc_app.
    + exact H1.
    + apply IHHs. exact H2.
  - (* ST_IfTrue *)
    destruct (lc_at_if_inv _ _ _ _ Hlc) as [H1 [H2 H3]].
    exact H2.
  - (* ST_IfFalse *)
    destruct (lc_at_if_inv _ _ _ _ Hlc) as [H1 [H2 H3]].
    exact H3.
  - (* ST_If *)
    destruct (lc_at_if_inv _ _ _ _ Hlc) as [H1 [H2 H3]].
    apply lc_if.
    + apply IHHs. exact H1.
    + exact H2.
    + exact H3.
Qed.

Lemma step_lc_back : forall t t', step t t' -> locally_closed t' -> locally_closed t.
Proof.
  intros t t' H.
  induction H as [T t0 v Hlca Hval
                 | t1 t1' t2 Hs IHHs Hlc2
                 | v1 t2 t2' Hv Hs IHHs
                 | t1 t2 Hl1 Hl2
                 | t1 t2 Hl1 Hl2
                 | t1 t1' t2 t3 Hs IHHs Hl2 Hl3];
  intros Hlc; unfold locally_closed in *.
  - (* ST_AppAbs *)
    apply lc_app.
    + apply lc_abs. apply lc_at_abs_inv in Hlca. exact Hlca.
    + apply value_lc. exact Hval.
  - (* ST_App1 *)
    apply lc_app.
    + apply IHHs. apply (proj1 (lc_at_app_inv _ _ _ Hlc)).
    + apply (proj2 (lc_at_app_inv _ _ _ Hlc)).
  - (* ST_App2 *)
    apply lc_app.
    + apply (proj1 (lc_at_app_inv _ _ _ Hlc)).
    + apply IHHs. apply (proj2 (lc_at_app_inv _ _ _ Hlc)).
  - (* ST_IfTrue *)
    apply lc_if.
    + apply lc_true.
    + exact Hlc.
    + exact Hl2.
  - (* ST_IfFalse *)
    apply lc_if.
    + apply lc_false.
    + exact Hl1.
    + exact Hlc.
  - (* ST_If *)
    destruct (lc_at_if_inv _ _ _ _ Hlc) as [H1 [H2 H3]].
    apply lc_if.
    + apply IHHs. exact H1.
    + exact H2.
    + exact H3.
Qed.

(** ** Decidability of value and local closure *)

Fixpoint lc_b (k : nat) (t : tm) : bool :=
  match t with
  | tm_bvar i => Nat.ltb i k
  | tm_fvar _ => true
  | tm_app a b => andb (lc_b k a) (lc_b k b)
  | tm_abs _ b => lc_b (S k) b
  | tm_true => true
  | tm_false => true
  | tm_if a b c => andb (lc_b k a) (andb (lc_b k b) (lc_b k c))
  end.

Lemma lc_b_iff : forall k (t : tm), lc_b k t = true <-> lc_at k t.
Proof.
  intros k t. revert k. induction t as [i | y | t1 IHt1 t2 IHt2 | T b IHt | | | t1 IHt1 t2 IHt2 t3 IHt3]; intros k; simpl.
  - (* tm_bvar *) split; intros H.
    + apply lc_bvar. apply Nat.ltb_lt. exact H.
    + apply Nat.ltb_lt. inversion H; subst. assumption.
  - (* tm_fvar *) split; intros _; [apply lc_fvar | reflexivity].
  - (* tm_app *) rewrite Bool.andb_true_iff. rewrite IHt1, IHt2.
    split.
    + intros [H1 H2]. apply lc_app; assumption.
    + intro H. inversion H; subst. split; assumption.
  - (* tm_abs *) rewrite IHt. split.
    + intros H. apply lc_abs. assumption.
    + intros H. inversion H; subst. assumption.
  - (* tm_true *) split; intros _; [apply lc_true | reflexivity].
  - (* tm_false *) split; intros _; [apply lc_false | reflexivity].
  - (* tm_if *) rewrite Bool.andb_true_iff, IHt1, Bool.andb_true_iff, IHt2, IHt3.
    split.
    + intros [H1 [H2 H3]]. apply lc_if; assumption.
    + intro H. inversion H; subst. split; [assumption | split; assumption].
Qed.

Definition value_dec : forall t : tm, {value t} + {~ value t}.
Proof.
  intros t. destruct t as [i | x | t1 t2 | T b | | | t1 t2 t3].
  - right. intro H. inversion H.
  - right. intro H. inversion H.
  - right. intro H. inversion H.
  - destruct (lc_b 0 (tm_abs T b)) eqn:E.
    + left. apply v_abs. apply lc_b_iff. exact E.
    + right. intro H. inversion H.
      apply lc_b_iff in H1. rewrite E in H1. discriminate H1.
  - left. apply v_true.
  - left. apply v_false.
  - right. intro H. inversion H.
Defined.

(** Target theorem: strong normalization for the supplied CBV relation. *)

Inductive strongly_normalizing : tm -> Prop :=
  | SN_intro : forall t,
      (forall t', t --> t' -> strongly_normalizing t') ->
      strongly_normalizing t.

(** ** Strong-normalization induction principle *)

Lemma SN_step : forall t t', strongly_normalizing t -> step t t' -> strongly_normalizing t'.
Proof.
  intros t t' Hsn Hs. inversion Hsn; subst. auto.
Qed.

Lemma SN_ind' : forall (P : tm -> Prop),
  (forall t, (forall t', step t t' -> P t') -> P t) ->
  forall t, strongly_normalizing t -> P t.
Proof.
  intros P Hstep t Hsn.
  induction Hsn.
  apply Hstep. intros t' Hs. eauto.
Qed.

(** ** The logical relation *)

Fixpoint R (T : ty) (t : tm) : Prop :=
  match T with
  | Ty_Bool => strongly_normalizing t /\ locally_closed t
  | Ty_Arrow T1 T2 =>
      strongly_normalizing t /\ locally_closed t /\
      (forall u, R T1 u -> R T2 (tm_app t u))
  end.

Definition env_ok (Gamma : context) (sigma : atom -> tm) : Prop :=
  (forall x T, Gamma x = Some T -> R T (sigma x)) /\
  (forall x, locally_closed (sigma x)).

Lemma R_sn : forall T t, R T t -> strongly_normalizing t.
Proof. intros T t H. destruct T; simpl in H; tauto. Qed.

Lemma R_lc : forall T t, R T t -> locally_closed t.
Proof. intros T t H. destruct T; simpl in H; tauto. Qed.

(** ** Forward closure of the relation under stepping *)

Lemma R_step : forall T t t', R T t -> step t t' -> R T t'.
Proof.
  induction T; intros t t' HR Hs; simpl in *.
  - destruct HR as [Hsn Hlc]. split.
    + eapply SN_step; eauto.
    + eapply step_lc_fwd; eauto.
  - destruct HR as [Hsn [Hlc Happ]]. split; [| split].
    + eapply SN_step; eauto.
    + eapply step_lc_fwd; eauto.
    + intros u Hu.
      apply (IHT2 (tm_app t u) (tm_app t' u)).
      * apply Happ. exact Hu.
      * apply ST_App1. exact Hs. apply (R_lc T1 u Hu).
Qed.

(** ** Expansion: a non-value term all of whose reducts are related is related *)

Lemma R_expand : forall (T : ty) (t : tm),
  locally_closed t ->
  ~ value t ->
  (forall t', step t t' -> R T t') ->
  R T t.
Proof.
  induction T; intros t Hlc Hnv Hstep.
  - (* Bool *) simpl. split.
    + apply SN_intro. intros t' Hs. apply R_sn with (T := Ty_Bool). apply Hstep. exact Hs.
    + exact Hlc.
  - (* Arrow *) simpl. split; [| split].
    + apply SN_intro. intros t' Hs. apply R_sn with (T := Ty_Arrow T1 T2). apply Hstep. exact Hs.
    + exact Hlc.
    + intros v Hv.
      apply IHT2 with (t := tm_app t v).
      * apply lc_app; [exact Hlc | apply (R_lc T1 v Hv)].
      * intro Hcontra. inversion Hcontra.
      * intros w Hw. inversion Hw; subst.
        -- (* ST_AppAbs *) exfalso. apply Hnv. apply v_abs. assumption.
        -- (* ST_App1 *)
           match goal with
           | Hst : step t ?x |- _ =>
               destruct (Hstep x Hst) as [Hsn' [Hlc' Happ']]; apply Happ'; exact Hv
           end.
        -- (* ST_App2 *)
           match goal with
           | Hv0 : value t |- _ => exfalso; apply Hnv; exact Hv0
           end.
Qed.

(** ** Stuck terms are related at every type *)

Lemma R_stuck : forall (T : ty) (t : tm),
  locally_closed t -> ~ value t -> (forall t', ~ step t t') -> R T t.
Proof.
  intros T t Hlc Hnv Hns.
  apply R_expand; auto.
  intros t' Hs. exfalso. apply (Hns t'). exact Hs.
Qed.

Lemma R_fvar : forall T x, R T (tm_fvar x).
Proof.
  intros T x.
  apply R_stuck.
  - apply lc_fvar.
  - intro H; inversion H.
  - intros t' H; inversion H.
Qed.

(** ** Auxiliary substitution facts for the environment *)

Lemma subst_cons_env_same : forall (sigma : atom -> tm) x u,
  subst (cons_env sigma x u) (tm_fvar x) = u.
Proof. intros. simpl. apply cons_env_same. Qed.

(** ** The application property for abstractions *)

Lemma R_app_abs : forall (T1 T2 : ty) (body u : tm),
  locally_closed (tm_abs T1 body) ->
  R T1 u ->
  (forall v, R T1 v -> value v -> R T2 (open body v)) ->
  R T2 (tm_app (tm_abs T1 body) u).
Proof.
  intros T1 T2 body u0 Hlc Hu0 Hval.
  assert (Hsn : strongly_normalizing u0) by (apply R_sn with (T := T1); exact Hu0).
  revert Hu0.
  refine (SN_ind' (fun u => R T1 u -> R T2 (tm_app (tm_abs T1 body) u)) _ u0 Hsn).
  intros u IH Hu.
  apply R_expand.
  - apply lc_app; [exact Hlc | apply (R_lc T1 u Hu)].
  - intro Hc; inversion Hc.
  - intros w Hw. inversion Hw; subst.
    + (* ST_AppAbs *) apply Hval; [exact Hu | assumption].
    + (* ST_App1 *)
      match goal with
      | Hst : step (tm_abs T1 body) _ |- _ => inversion Hst
      end.
    + (* ST_App2 *)
      apply IH.
      * match goal with
        | Hst : step u _ |- _ => exact Hst
        end.
      * match goal with
        | Hst : step u ?x |- _ => apply (R_step T1 u x Hu Hst)
        end.
Qed.

(** ** Abstractions are related at arrow types *)

Lemma R_abs : forall (T1 T2 : ty) (body : tm),
  locally_closed (tm_abs T1 body) ->
  (forall v, R T1 v -> value v -> R T2 (open body v)) ->
  R (Ty_Arrow T1 T2) (tm_abs T1 body).
Proof.
  intros T1 T2 body Hlc Hval. simpl. split; [| split].
  - apply SN_intro. intros t' Hs. inversion Hs.
  - exact Hlc.
  - intros u Hu. apply R_app_abs with (body := body); assumption.
Qed.

(** ** If-then-else preserves the relation *)

Lemma R_if_step : forall (T : ty) (e1 e2 e3 : tm),
  R Ty_Bool e1 -> R T e2 -> R T e3 ->
  (forall e1', step e1 e1' -> R T (tm_if e1' e2 e3)) ->
  R T (tm_if e1 e2 e3).
Proof.
  intros T e1 e2 e3 H1 H2 H3 Hrec.
  apply R_expand.
  - apply lc_if.
    + apply (R_lc Ty_Bool e1 H1).
    + apply (R_lc T e2 H2).
    + apply (R_lc T e3 H3).
  - intro Hc; inversion Hc.
  - intros w Hw. inversion Hw; subst.
    + (* ST_IfTrue *) exact H2.
    + (* ST_IfFalse *) exact H3.
    + (* ST_If *) apply Hrec. assumption.
Qed.

Lemma R_if : forall (T : ty) (e1 e2 e3 : tm),
  R Ty_Bool e1 -> R T e2 -> R T e3 -> R T (tm_if e1 e2 e3).
Proof.
  intros T e1 e2 e3 H1 H2 H3.
  assert (Hsn : strongly_normalizing e1) by (apply R_sn with (T := Ty_Bool); exact H1).
  revert H1 H2 H3.
  refine (SN_ind' (fun e1 => R Ty_Bool e1 -> R T e2 -> R T e3 -> R T (tm_if e1 e2 e3)) _ e1 Hsn).
  intros e0 IH H1 H2 H3.
  apply R_if_step; auto.
  intros e1' Hs.
  apply IH.
  - exact Hs.
  - apply R_step with (t := e0); assumption.
  - exact H2.
  - exact H3.
Qed.

(** ** The fundamental theorem *)


Theorem fundamental : forall (Gamma : context) (t : tm) (T : ty),
  has_type Gamma t T ->
  forall sigma, env_ok Gamma sigma -> R T (subst sigma t).
Proof.
  intros Gamma t T H.
  refine (has_type_ind
    (fun Gamma t T => forall sigma, env_ok Gamma sigma -> R T (subst sigma t))
    _ _ _ _ _ _ Gamma t T H).
  - (* T_Var *) intros Gamma0 x S Hvar sigma [Henv Hlcs]. simpl. apply (Henv x S Hvar).
  - (* T_Abs *) intros L Gamma0 T1 T2 t1 Hbody IHbody sigma [Henv Hlcs]. simpl.
    destruct (exists_fresh (L ++ fv t1)) as [x Hx].
    assert (HxL : ~ In x L) by (intro Hin; apply Hx; apply List.in_app_iff; left; exact Hin).
    assert (Hxfv : ~ In x (fv t1)) by (intro Hin; apply Hx; apply List.in_app_iff; right; exact Hin).
    apply R_abs.
    + (* local closure *)
      apply lc_abs.
      assert (Hlc1 : forall y, locally_closed (cons_env sigma x (tm_fvar x) y)).
      { intro y. unfold cons_env. destruct (Nat.eqb x y) eqn:E.
        - apply lc_fvar.
        - apply Hlcs. }
      assert (Henv1 : env_ok (update Gamma0 x T1) (cons_env sigma x (tm_fvar x))).
      { split.
        - intros y S Hy. destruct (Nat.eqb x y) eqn:E.
          + apply Nat.eqb_eq in E. subst.
            unfold update in Hy. rewrite Nat.eqb_refl in Hy.
            injection Hy as ->. rewrite cons_env_same. apply R_fvar.
          + assert (Hxy : x <> y) by (apply Nat.eqb_neq; exact E).
            replace (cons_env sigma x (tm_fvar x) y) with (sigma y) by (symmetry; apply cons_env_other; exact Hxy).
            apply Henv. unfold update in Hy. rewrite E in Hy. exact Hy.
        - exact Hlc1. }
      pose proof (IHbody x HxL (cons_env sigma x (tm_fvar x)) Henv1) as HR.
      unfold open in HR.
      rewrite (subst_open_rec _ 0 (tm_fvar x) t1 Hlc1) in HR.
      rewrite subst_cons_env_same in HR.
      rewrite subst_cons_notin in HR by exact Hxfv.
      apply (proj1 (lc_at_open_fvar (subst sigma t1) 0 x)).
      apply (R_lc T2 _ HR).
    + (* value arguments *)
      intros v HvR Hvval.
      assert (Hlc2 : forall y, locally_closed (cons_env sigma x v y)).
      { intro y. unfold cons_env. destruct (Nat.eqb x y) eqn:E.
        - apply (R_lc T1 v HvR).
        - apply Hlcs. }
      assert (Henv2 : env_ok (update Gamma0 x T1) (cons_env sigma x v)).
      { split.
        - intros y S Hy. destruct (Nat.eqb x y) eqn:E.
          + apply Nat.eqb_eq in E. subst.
            unfold update in Hy. rewrite Nat.eqb_refl in Hy.
            injection Hy as ->. rewrite cons_env_same. exact HvR.
          + assert (Hxy : x <> y) by (apply Nat.eqb_neq; exact E).
            replace (cons_env sigma x v y) with (sigma y) by (symmetry; apply cons_env_other; exact Hxy).
            apply Henv. unfold update in Hy. rewrite E in Hy. exact Hy.
        - exact Hlc2. }
      pose proof (IHbody x HxL (cons_env sigma x v) Henv2) as HRv.
      unfold open in HRv.
      rewrite (subst_open_rec _ 0 (tm_fvar x) t1 Hlc2) in HRv.
      rewrite subst_cons_env_same in HRv.
      rewrite subst_cons_notin in HRv by exact Hxfv.
      exact HRv.
  - (* T_App *) intros Gamma0 t1 t2 T1 T2 Hh IHh Ha IHa sigma [Henv Hlcs]. simpl.
    pose proof (IHh sigma (conj Henv Hlcs)) as HR.
    simpl in HR. destruct HR as [Hsn1 [Hlc1 Happ1]].
    apply Happ1. apply IHa. split; assumption.
  - (* T_True *) intros Gamma0 sigma [Henv Hlcs]. simpl. split.
    + apply SN_intro. intros t' Hs. inversion Hs.
    + apply lc_true.
  - (* T_False *) intros Gamma0 sigma [Henv Hlcs]. simpl. split.
    + apply SN_intro. intros t' Hs. inversion Hs.
    + apply lc_false.
  - (* T_If *) intros Gamma0 t1 t2 t3 S Hc IHc Hthen IHthen Helse IHelse sigma [Henv Hlcs]. simpl.
    apply R_if.
    + apply IHc. split; assumption.
    + apply IHthen. split; assumption.
    + apply IHelse. split; assumption.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T H.
  assert (Henv : env_ok empty (fun x => tm_fvar x)).
  { split.
    - intros x S Hx. unfold empty in Hx. discriminate Hx.
    - intros x. apply lc_fvar. }
  pose proof (fundamental empty t T H (fun x => tm_fvar x) Henv) as HR.
  rewrite subst_id in HR.
  exact (R_sn T t HR).
Qed.

End STLCCBVNormalizationTask.
