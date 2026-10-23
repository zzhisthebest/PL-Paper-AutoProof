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

(** * Support definitions and lemmas (added for the proof). *)

(** Free-variable occurrence. *)

Fixpoint occurs (x : atom) (t : tm) : Prop :=
  match t with
  | tm_bvar _ => False
  | tm_fvar y => x = y
  | tm_app t1 t2 => occurs x t1 \/ occurs x t2
  | tm_abs _ t1 => occurs x t1
  | tm_true => False
  | tm_false => False
  | tm_if t1 t2 t3 => occurs x t1 \/ occurs x t2 \/ occurs x t3
  end.

(** Free-variable substitution (leaves bound variables untouched). *)

Fixpoint subst (rho : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => rho x
  | tm_app t1 t2 => tm_app (subst rho t1) (subst rho t2)
  | tm_abs T t1 => tm_abs T (subst rho t1)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (subst rho t1) (subst rho t2) (subst rho t3)
  end.

Definition extend (rho : atom -> tm) (x : atom) (v : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then v else rho y.

(** Upper bounds on the atoms occurring in a term / a list, used to
    produce fresh atoms. *)

Fixpoint max_fvar (t : tm) : nat :=
  match t with
  | tm_bvar _ => 0
  | tm_fvar x => x
  | tm_app t1 t2 => Nat.max (max_fvar t1) (max_fvar t2)
  | tm_abs _ t1 => max_fvar t1
  | tm_true => 0
  | tm_false => 0
  | tm_if t1 t2 t3 =>
      Nat.max (max_fvar t1) (Nat.max (max_fvar t2) (max_fvar t3))
  end.

Fixpoint max_atom_list (L : list atom) : nat :=
  match L with
  | nil => 0
  | cons x L' => Nat.max x (max_atom_list L')
  end.

Lemma max_fvar_ub : forall t x, occurs x t -> x <= max_fvar t.
Proof.
  induction t; simpl; intros y H.
  - (* tm_bvar *) contradiction.
  - (* tm_fvar *) lia.
  - (* tm_app *) destruct H as [H | H];
      [specialize (IHt1 y H) | specialize (IHt2 y H)]; lia.
  - (* tm_abs *) auto.
  - (* tm_true *) contradiction.
  - (* tm_false *) contradiction.
  - (* tm_if *) destruct H as [H | [H | H]];
      [specialize (IHt1 y H) | specialize (IHt2 y H) | specialize (IHt3 y H)]; lia.
Qed.

Lemma max_atom_list_ub : forall L x, In x L -> x <= max_atom_list L.
Proof.
  induction L as [| y L' IH]; intros x H.
  - contradiction.
  - simpl. destruct H as [-> | H].
    + apply Nat.le_max_l.
    + pose proof (IH x H).
      apply Nat.le_trans with (max_atom_list L'); [exact H0 | apply Nat.le_max_r].
Qed.

Lemma fresh_atom : forall (L : list atom) (t : tm),
  exists x, ~ In x L /\ ~ occurs x t.
Proof.
  intros L t.
  exists (S (Nat.max (max_atom_list L) (max_fvar t))).
  split; intro H.
  - apply max_atom_list_ub in H.
    pose proof (Nat.le_max_l (max_atom_list L) (max_fvar t)). lia.
  - apply max_fvar_ub in H.
    pose proof (Nat.le_max_r (max_atom_list L) (max_fvar t)). lia.
Qed.

(** Monotonicity of local closure. *)

Lemma lc_at_mono : forall k k' t, k <= k' -> lc_at k t -> lc_at k' t.
Proof.
  intros k k' t Hle H. revert k' Hle.
  induction H as [k0 i Hi | k0 x | k0 a b Ha IHa Hb IHb | k0 T0 b Hb IHb
                 | k0 | k0 | k0 a b c Ha IHa Hb IHb Hc IHc];
    intros k' Hle.
  - apply lc_bvar. lia.
  - apply lc_fvar.
  - apply lc_app; [apply IHa | apply IHb]; exact Hle.
  - apply lc_abs. apply IHb. lia.
  - apply lc_true.
  - apply lc_false.
  - apply lc_if; [apply IHa | apply IHb | apply IHc]; exact Hle.
Qed.

(** Inversion lemmas for local closure. *)

Lemma lc_app_inv : forall k t1 t2, lc_at k (tm_app t1 t2) -> lc_at k t1 /\ lc_at k t2.
Proof. intros k t1 t2 H. inversion H. auto. Qed.

Lemma lc_abs_inv : forall k T t, lc_at k (tm_abs T t) -> lc_at (S k) t.
Proof. intros k T t H. inversion H. assumption. Qed.

Lemma lc_if_inv : forall k t1 t2 t3,
  lc_at k (tm_if t1 t2 t3) -> lc_at k t1 /\ lc_at k t2 /\ lc_at k t3.
Proof. intros k t1 t2 t3 H. inversion H. auto. Qed.

(** Values do not step, and are locally closed and strongly normalizing. *)

Lemma value_no_step : forall v, value v -> forall v', ~ (v --> v').
Proof.
  intros v Hv. induction Hv; intros v' Hstep; inversion Hstep.
Qed.

Lemma abs_no_step : forall A body s, ~ (tm_abs A body --> s).
Proof. intros A body s H. inversion H. Qed.

Lemma value_lc : forall v, value v -> locally_closed v.
Proof.
  intros v Hv. induction Hv.
  - assumption.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma value_SN : forall v, value v -> strongly_normalizing v.
Proof.
  intros v Hv. apply SN_intro. intros v' Hstep.
  exfalso. eapply value_no_step; eassumption.
Qed.

Lemma value_not_app : forall t1 t2, ~ value (tm_app t1 t2).
Proof. intros t1 t2 H. inversion H. Qed.

Lemma value_not_if : forall t1 t2 t3, ~ value (tm_if t1 t2 t3).
Proof. intros t1 t2 t3 H. inversion H. Qed.

Lemma value_not_bvar : forall i, ~ value (tm_bvar i).
Proof. intros i H. inversion H. Qed.

Lemma value_not_fvar : forall x, ~ value (tm_fvar x).
Proof. intros x H. inversion H. Qed.

Lemma SN_step : forall t t', strongly_normalizing t -> t --> t' -> strongly_normalizing t'.
Proof.
  intros t t' HSN Hstep. destruct HSN as [t0 Hsucc]. apply (Hsucc t' Hstep).
Qed.

(** Opening preserves local closure, and a locally closed term is unchanged
    by opening at a level at least its own. *)

Lemma lc_open_rec : forall t k u,
  lc_at (S k) t -> lc_at k u -> lc_at k (open_rec k u t).
Proof.
  induction t; intros k u Hlc Hu; simpl.
  - (* tm_bvar *) destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. exact Hu.
    + apply lc_bvar. apply Nat.eqb_neq in E. inversion Hlc. lia.
  - (* tm_fvar *) apply lc_fvar.
  - (* tm_app *) apply lc_app_inv in Hlc. destruct Hlc as [H1 H2].
    apply lc_app; [apply IHt1 | apply IHt2]; assumption.
  - (* tm_abs *) apply lc_abs. apply IHt.
    + apply lc_abs_inv in Hlc. exact Hlc.
    + apply lc_at_mono with (k := k); [lia | exact Hu].
  - apply lc_true.
  - apply lc_false.
  - (* tm_if *) apply lc_if_inv in Hlc. destruct Hlc as [H1 [H2 H3]].
    apply lc_if; [apply IHt1 | apply IHt2 | apply IHt3]; assumption.
Qed.

Lemma lc_open_rec_inv : forall t k u,
  lc_at k (open_rec k u t) -> lc_at (S k) t.
Proof.
  induction t; intros k u H; simpl in H.
  - (* tm_bvar *) destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. apply lc_bvar. lia.
    + apply lc_bvar. apply Nat.eqb_neq in E. inversion H. lia.
  - (* tm_fvar *) apply lc_fvar.
  - (* tm_app *) apply lc_app_inv in H. destruct H as [H1 H2].
    apply lc_app; [apply IHt1 with (k := k) (u := u) | apply IHt2 with (k := k) (u := u)];
    assumption.
  - (* tm_abs *) apply lc_abs. apply IHt with (k := S k) (u := u).
    apply lc_abs_inv in H. exact H.
  - apply lc_true.
  - apply lc_false.
  - (* tm_if *) apply lc_if_inv in H. destruct H as [H1 [H2 H3]].
    apply lc_if;
      [apply IHt1 with (k := k) (u := u) |
       apply IHt2 with (k := k) (u := u) |
       apply IHt3 with (k := k) (u := u)]; assumption.
Qed.

Lemma open_rec_lc : forall t j k v, lc_at k t -> k <= j -> open_rec j v t = t.
Proof.
  induction t; intros j k v Hlc Hle; simpl.
  - (* tm_bvar *) destruct (Nat.eqb j n) eqn:E.
    + apply Nat.eqb_eq in E. subst. inversion Hlc. lia.
    + reflexivity.
  - reflexivity.
  - (* tm_app *) apply lc_app_inv in Hlc. destruct Hlc as [H1 H2].
    rewrite (IHt1 j k v H1 Hle), (IHt2 j k v H2 Hle). reflexivity.
  - (* tm_abs *) f_equal. apply (IHt (S j) (S k) v).
    + apply lc_abs_inv in Hlc. exact Hlc.
    + lia.
  - reflexivity.
  - reflexivity.
  - (* tm_if *) apply lc_if_inv in Hlc. destruct Hlc as [H1 [H2 H3]].
    rewrite (IHt1 j k v H1 Hle), (IHt2 j k v H2 Hle), (IHt3 j k v H3 Hle).
    reflexivity.
Qed.

(** Substitution preserves local closure. *)

Lemma subst_lc : forall t rho k,
  (forall x, lc_at 0 (rho x)) -> lc_at k t -> lc_at k (subst rho t).
Proof.
  induction t; intros rho k Hrho Hlc; simpl.
  - apply lc_bvar. inversion Hlc. assumption.
  - apply lc_at_mono with (k := 0); [lia | apply Hrho].
  - apply lc_app_inv in Hlc. destruct Hlc as [H1 H2].
    apply lc_app; [apply IHt1 | apply IHt2]; assumption.
  - apply lc_abs. apply IHt.
    + exact Hrho.
    + apply lc_abs_inv in Hlc. exact Hlc.
  - apply lc_true.
  - apply lc_false.
  - apply lc_if_inv in Hlc. destruct Hlc as [H1 [H2 H3]].
    apply lc_if; [apply IHt1 | apply IHt2 | apply IHt3]; assumption.
Qed.

(** Step preserves local closure. *)

Lemma lc_step : forall t t', locally_closed t -> t --> t' -> locally_closed t'.
Proof.
  intros t t' Hlc Hstep. revert Hlc.
  induction Hstep; intros Hlc.
  - (* ST_AppAbs *) apply lc_app_inv in Hlc. destruct Hlc as [H1 H2].
    apply lc_open_rec with (k := 0).
    + apply lc_abs_inv in H1. exact H1.
    + exact H2.
  - (* ST_App1 *) apply lc_app_inv in Hlc. destruct Hlc as [H1 H2].
    apply lc_app; [apply IHHstep; exact H1 | exact H2].
  - (* ST_App2 *) apply lc_app_inv in Hlc. destruct Hlc as [H1 H2].
    apply lc_app; [exact H1 | apply IHHstep; exact H2].
  - (* ST_IfTrue *) apply lc_if_inv in Hlc. destruct Hlc as [H1 [H2 H3]]. exact H2.
  - (* ST_IfFalse *) apply lc_if_inv in Hlc. destruct Hlc as [H1 [H2 H3]]. exact H3.
  - (* ST_If *) apply lc_if_inv in Hlc. destruct Hlc as [H1 [H2 H3]].
    apply lc_if; [apply IHHstep; exact H1 | exact H2 | exact H3].
Qed.

(** Typing implies local closure. *)

Lemma typing_lc : forall Gamma t T, has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T Hty.
  induction Hty as [Gamma0 x T0 HVar
                 | L Gamma0 T1 T2 t1 Hprem IHAbs
                 | Gamma0 t1 t2 T1 T2 H1 IH1 H2 IH2
                 | Gamma0 | Gamma0
                 | Gamma0 t1 t2 t3 T0 H1 IH1 H2 IH2 H3 IH3].
  - (* T_Var *) apply lc_fvar.
  - (* T_Abs *) apply lc_abs.
    destruct (fresh_atom L t1) as [x [HxL _]].
    pose proof (IHAbs x HxL) as Hx.
    apply lc_open_rec_inv with (k := 0) (u := tm_fvar x) in Hx.
    exact Hx.
  - (* T_App *) apply lc_app; assumption.
  - apply lc_true.
  - apply lc_false.
  - (* T_If *) apply lc_if; assumption.
Qed.

(** Substitution commutes with opening, for a fresh variable. *)

Lemma subst_open_rec : forall t rho x v k,
  (forall y, locally_closed (rho y)) ->
  ~ occurs x t ->
  subst (extend rho x v) (open_rec k (tm_fvar x) t) =
  open_rec k v (subst rho t).
Proof.
  induction t; intros rho x v k Hrho Hocc; simpl.
  - (* tm_bvar *) destruct (Nat.eqb k n) eqn:E.
    + subst. simpl. unfold extend. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - (* tm_fvar *) unfold extend.
    destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply Hocc. reflexivity.
    + apply Nat.eqb_neq in E. symmetry. apply (open_rec_lc (rho a) k 0 v).
      * apply Hrho.
      * lia.
  - (* tm_app *)
    assert (H1 : ~ occurs x t1) by (intro Hc; apply Hocc; simpl; left; exact Hc).
    assert (H2 : ~ occurs x t2) by (intro Hc; apply Hocc; simpl; right; exact Hc).
    rewrite (IHt1 rho x v k Hrho H1), (IHt2 rho x v k Hrho H2). reflexivity.
  - (* tm_abs *) simpl in Hocc. f_equal.
    rewrite (IHt rho x v (S k) Hrho Hocc). reflexivity.
  - reflexivity.
  - reflexivity.
  - (* tm_if *)
    assert (H1 : ~ occurs x t1) by (intro Hc; apply Hocc; simpl; left; exact Hc).
    assert (H2 : ~ occurs x t2) by (intro Hc; apply Hocc; simpl; right; left; exact Hc).
    assert (H3 : ~ occurs x t3) by (intro Hc; apply Hocc; simpl; right; right; exact Hc).
    rewrite (IHt1 rho x v k Hrho H1), (IHt2 rho x v k Hrho H2),
            (IHt3 rho x v k Hrho H3).
    reflexivity.
Qed.

Lemma subst_open : forall t rho x v,
  (forall y, locally_closed (rho y)) ->
  ~ occurs x t ->
  subst (extend rho x v) (open t (tm_fvar x)) = open (subst rho t) v.
Proof.
  intros t rho x v Hrho Hocc. apply subst_open_rec; assumption.
Qed.

Lemma subst_id : forall t, subst (fun x => tm_fvar x) t = t.
Proof.
  induction t; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IHt1, IHt2, IHt3. reflexivity.
Qed.

(** ** Analysis of the possible steps. *)

Lemma step_app_abs_value : forall A body v s,
  value v -> tm_app (tm_abs A body) v --> s -> s = open body v.
Proof.
  intros A body v s Hv Hs.
  inversion Hs as [T0 t0 v0 Hlca Hva
                 | t1 t1' t2 Hs1 Hlc2
                 | v1 t2 t2' Hv1 Hs2
                 | a b Hc1 Hc2
                 | a b Hc1 Hc2
                 | a a' b c Hs1 Hc2 Hc3]; subst.
  - reflexivity.
  - exfalso. eapply abs_no_step. eexact Hs1.
  - exfalso. eapply value_no_step with (v := v) (v' := t2'). exact Hv. exact Hs2.
Qed.

Lemma step_app_abs_nonvalue : forall A body u s,
  ~ value u -> tm_app (tm_abs A body) u --> s ->
  exists u', u --> u' /\ s = tm_app (tm_abs A body) u'.
Proof.
  intros A body u s Hnv Hs.
  inversion Hs as [T0 t0 v0 Hlca Hva
                 | t1 t1' t2 Hs1 Hlc2
                 | v1 t2 t2' Hv1 Hs2
                 | a b Hc1 Hc2
                 | a b Hc1 Hc2
                 | a a' b c Hs1 Hc2 Hc3]; subst.
  - exfalso. apply Hnv. exact Hva.
  - exfalso. eapply abs_no_step. eexact Hs1.
  - exists t2'. split; [exact Hs2 | reflexivity].
Qed.

Lemma step_app_l : forall t u s,
  ~ value t -> tm_app t u --> s ->
  exists t', t --> t' /\ s = tm_app t' u.
Proof.
  intros t u s Hnv Hs.
  inversion Hs as [T0 t0 v0 Hlca Hva
                 | t1 t1' t2 Hs1 Hlc2
                 | v1 t2 t2' Hv1 Hs2
                 | a b Hc1 Hc2
                 | a b Hc1 Hc2
                 | a a' b c Hs1 Hc2 Hc3]; subst.
  - exfalso. apply Hnv. apply v_abs. exact Hlca.
  - exists t1'. split; [exact Hs1 | reflexivity].
  - exfalso. apply Hnv. exact Hv1.
Qed.

Lemma step_if_l : forall t1 t2 t3 s,
  ~ value t1 -> tm_if t1 t2 t3 --> s ->
  exists t1', t1 --> t1' /\ s = tm_if t1' t2 t3.
Proof.
  intros t1 t2 t3 s Hnv Hs.
  inversion Hs as [T0 t0 v0 Hlca Hva
                 | t1' t1'' t2' Hs1 Hlc2
                 | v1 t2' t2'' Hv1 Hs2
                 | a b Hc1 Hc2
                 | a b Hc1 Hc2
                 | a a' b c Hs1 Hc2 Hc3]; subst.
  - exfalso. apply Hnv. apply v_true.
  - exfalso. apply Hnv. apply v_false.
  - exists a'. split; [exact Hs1 | reflexivity].
Qed.

Lemma step_if_true : forall t2 t3 s, tm_if tm_true t2 t3 --> s -> s = t2.
Proof.
  intros t2 t3 s Hs.
  inversion Hs as [T0 t0 v0 Hlca Hva
                 | t1' t1'' t2' Hs1 Hlc2
                 | v1 t2' t2'' Hv1 Hs2
                 | a b Hc1 Hc2
                 | a b Hc1 Hc2
                 | a a' b c Hs1 Hc2 Hc3]; subst.
  - reflexivity.
  - exfalso. eapply value_no_step; [apply v_true | exact Hs1].
Qed.

Lemma step_if_false : forall t2 t3 s, tm_if tm_false t2 t3 --> s -> s = t3.
Proof.
  intros t2 t3 s Hs.
  inversion Hs as [T0 t0 v0 Hlca Hva
                 | t1' t1'' t2' Hs1 Hlc2
                 | v1 t2' t2'' Hv1 Hs2
                 | a b Hc1 Hc2
                 | a b Hc1 Hc2
                 | a a' b c Hs1 Hc2 Hc3]; subst.
  - reflexivity.
  - exfalso. eapply value_no_step; [apply v_false | exact Hs1].
Qed.

Lemma step_if_abs_absurd : forall A body t2 t3 s,
  tm_if (tm_abs A body) t2 t3 --> s -> False.
Proof.
  intros A body t2 t3 s Hs.
  inversion Hs as [T0 t0 v0 Hlca Hva
                 | t1' t1'' t2' Hs1 Hlc2
                 | v1 t2' t2'' Hv1 Hs2
                 | a b Hc1 Hc2
                 | a b Hc1 Hc2
                 | a a' b c Hs1 Hc2 Hc3]; subst.
  - eapply abs_no_step. eexact Hs1.
Qed.

(** ** The logical relation. *)

Fixpoint R (T : ty) (t : tm) : Prop :=
  match T with
  | Ty_Bool => strongly_normalizing t /\ locally_closed t
  | Ty_Arrow T1 T2 =>
      strongly_normalizing t /\ locally_closed t /\
      (forall u, R T1 u -> R T2 (tm_app t u))
  end.

Lemma R_SN : forall T t, R T t -> strongly_normalizing t.
Proof.
  intros T. destruct T; intros t H; exact (proj1 H).
Qed.

Lemma R_lc : forall T t, R T t -> locally_closed t.
Proof.
  intros T. destruct T as [| A B]; intros t H.
  - exact (proj2 H).
  - exact (proj1 (proj2 H)).
Qed.

Lemma R_app : forall A B t u, R (Ty_Arrow A B) t -> R A u -> R B (tm_app t u).
Proof.
  intros A B t u H1 H2. destruct H1 as [HSN [Hlc Hfun]]. apply Hfun. exact H2.
Qed.

(** R is closed under steps, and is closed under "expansion" along a step
    whose result is the unique successor. *)

Lemma R_step : forall T t t', R T t -> t --> t' -> R T t'.
Proof.
  induction T as [| A IHA B IHB]; intros t t' HR Hstep.
  - destruct HR as [HSN Hlc]. split.
    + apply SN_step with (t := t); assumption.
    + apply lc_step with (t := t); assumption.
  - destruct HR as [HSN [Hlc Hfun]]. split.
    + apply SN_step with (t := t); assumption.
    + split.
      * apply lc_step with (t := t); assumption.
      * intros u Hru. apply IHB with (t := tm_app t u).
        -- apply Hfun. exact Hru.
        -- apply ST_App1; [exact Hstep | apply R_lc with (T := A); exact Hru].
Qed.

(** If all successors of a (non-value) locally closed term satisfy R, then
    the term satisfies R. *)

Lemma R_intro_nonvalue : forall T,
  forall t, locally_closed t -> ~ value t ->
  (forall t', t --> t' -> R T t') -> R T t.
Proof.
  induction T as [| A IHA B IHB]; intros t Hlc Hnv Hall.
  - split.
    + apply SN_intro. intros t' Hs. apply R_SN with (T := Ty_Bool). apply Hall. exact Hs.
    + exact Hlc.
  - split.
    + apply SN_intro. intros t' Hs. apply R_SN with (T := Ty_Arrow A B). apply Hall. exact Hs.
    + split.
      * exact Hlc.
      * intros u Hru. apply IHB.
        -- apply lc_app; [exact Hlc | apply R_lc with (T := A); exact Hru].
        -- apply value_not_app.
        -- intros s Hs. destruct (step_app_l t u s Hnv Hs) as [t0 [Hs0 ->]].
           apply R_app with (A := A) (t := t0) (u := u).
           ++ apply Hall. exact Hs0.
           ++ exact Hru.
Qed.

(** A stuck non-value term satisfies R at every type. *)

Lemma R_stuck : forall T,
  forall t, locally_closed t -> ~ value t ->
  (forall t', t --> t' -> False) -> R T t.
Proof.
  induction T as [| A IHA B IHB]; intros t Hlc Hnv Hns.
  - split.
    + apply SN_intro. intros t' Hs. exfalso. apply (Hns t' Hs).
    + exact Hlc.
  - split.
    + apply SN_intro. intros t' Hs. exfalso. apply (Hns t' Hs).
    + split.
      * exact Hlc.
      * intros u Hru. apply IHB.
        -- apply lc_app; [exact Hlc | apply R_lc with (T := A); exact Hru].
        -- apply value_not_app.
        -- intros s Hs. exfalso.
           destruct (step_app_l t u s Hnv Hs) as [t0 [Hs0 _]].
           apply (Hns t0 Hs0).
Qed.

(** Expansion along a step with a unique successor. *)

Lemma R_back_step : forall T,
  forall t t', locally_closed t -> t --> t' ->
  (forall t'', t --> t'' -> t'' = t') -> R T t' -> R T t.
Proof.
  induction T as [| A IHA B IHB]; intros t t' Hlc Hstep Huniq HR.
  - destruct HR as [HSN Hlc']. split.
    + apply SN_intro. intros s Hs. rewrite (Huniq s Hs). exact HSN.
    + exact Hlc.
  - destruct HR as [HSN [Hlc' Hfun]]. split.
    + apply SN_intro. intros s Hs. rewrite (Huniq s Hs). exact HSN.
    + split.
      * exact Hlc.
      * intros u Hru. apply IHB with (t' := tm_app t' u).
        -- apply lc_app; [exact Hlc | apply R_lc with (T := A); exact Hru].
        -- apply ST_App1; [exact Hstep | apply R_lc with (T := A); exact Hru].
        -- intros s Hs.
           assert (Hnv : ~ value t).
           { intro Hv. eapply value_no_step with (v := t) (v' := t').
             - exact Hv.
             - exact Hstep. }
           destruct (step_app_l t u s Hnv Hs) as [t0 [Hs0 Heq]].
           subst s. rewrite (Huniq t0 Hs0). reflexivity.
        -- apply Hfun. exact Hru.
Qed.

(** An abstraction is reducible at an arrow type as soon as its body,
    opened with a reducible value, is reducible. *)

Lemma R_abs_app_any : forall A B body,
  locally_closed (tm_abs A body) ->
  (forall v, value v -> R A v -> R B (tm_app (tm_abs A body) v)) ->
  forall u, R A u -> R B (tm_app (tm_abs A body) u).
Proof.
  intros A B body Hlc Happ u Hru.
  assert (HSN : strongly_normalizing u) by (apply R_SN with (T := A); exact Hru).
  revert Hru Happ.
  induction HSN as [u Hsucc IH].
  intros Hru Happ.
  revert Hru IH Hsucc.
  destruct u as [i | x | u1 u2 | T0 body0 | | | u1 u2 u3];
    intros Hru IH Hsucc.
  - (* tm_bvar *)
    apply R_intro_nonvalue with (t := tm_app (tm_abs A body) (tm_bvar i)).
    + apply lc_app; [exact Hlc | apply R_lc with (T := A); exact Hru].
    + apply value_not_app.
    + intros s Hs.
      destruct (step_app_abs_nonvalue A body (tm_bvar i) s (value_not_bvar i) Hs)
        as [u' [Hs' ->]].
      exact (IH u' Hs' (R_step A (tm_bvar i) u' Hru Hs') Happ).
  - (* tm_fvar *)
    apply R_intro_nonvalue with (t := tm_app (tm_abs A body) (tm_fvar x)).
    + apply lc_app; [exact Hlc | apply R_lc with (T := A); exact Hru].
    + apply value_not_app.
    + intros s Hs.
      destruct (step_app_abs_nonvalue A body (tm_fvar x) s (value_not_fvar x) Hs)
        as [u' [Hs' ->]].
      exact (IH u' Hs' (R_step A (tm_fvar x) u' Hru Hs') Happ).
  - (* tm_app *)
    apply R_intro_nonvalue with (t := tm_app (tm_abs A body) (tm_app u1 u2)).
    + apply lc_app; [exact Hlc | apply R_lc with (T := A); exact Hru].
    + apply value_not_app.
    + intros s Hs.
      destruct (step_app_abs_nonvalue A body (tm_app u1 u2) s (value_not_app u1 u2) Hs)
        as [u' [Hs' ->]].
      exact (IH u' Hs' (R_step A (tm_app u1 u2) u' Hru Hs') Happ).
  - (* tm_abs *) apply Happ.
    + apply v_abs. apply R_lc with (T := A); exact Hru.
    + exact Hru.
  - (* tm_true *) apply Happ.
    + apply v_true.
    + exact Hru.
  - (* tm_false *) apply Happ.
    + apply v_false.
    + exact Hru.
  - (* tm_if *)
    apply R_intro_nonvalue with (t := tm_app (tm_abs A body) (tm_if u1 u2 u3)).
    + apply lc_app; [exact Hlc | apply R_lc with (T := A); exact Hru].
    + apply value_not_app.
    + intros s Hs.
      destruct (step_app_abs_nonvalue A body (tm_if u1 u2 u3) s (value_not_if u1 u2 u3) Hs)
        as [u' [Hs' ->]].
      exact (IH u' Hs' (R_step A (tm_if u1 u2 u3) u' Hru Hs') Happ).
Qed.

Lemma R_abs_intro : forall A B body,
  locally_closed (tm_abs A body) ->
  (forall v, value v -> R A v -> R B (open body v)) ->
  R (Ty_Arrow A B) (tm_abs A body).
Proof.
  intros A B body Hlc Hbody.
  assert (Happ : forall v, value v -> R A v -> R B (tm_app (tm_abs A body) v)).
  { intros v Hv Hrv. apply R_back_step with (t' := open body v).
    - apply lc_app; [exact Hlc | apply R_lc with (T := A); exact Hrv].
    - apply ST_AppAbs; assumption.
    - intros s Hs. exact (step_app_abs_value A body v s Hv Hs).
    - apply Hbody; assumption. }
  split.
  - apply value_SN. apply v_abs. exact Hlc.
  - split.
    + exact Hlc.
    + apply R_abs_app_any with (A := A) (B := B); assumption.
Qed.

(** Reducibility of conditional expressions. *)

Lemma R_if : forall T t1 t2 t3,
  R Ty_Bool t1 -> R T t2 -> R T t3 -> R T (tm_if t1 t2 t3).
Proof.
  intros T t1 t2 t3 H1 H2 H3.
  destruct H1 as [HSN Hlc1].
  revert T t2 t3 Hlc1 H2 H3.
  induction HSN as [t1 Hsucc IH].
  intros T t2 t3 Hlc1 H2 H3.
  revert T t2 t3 Hlc1 H2 H3 IH Hsucc.
  destruct t1 as [i | x | a b | T0 body0 | | | a b c];
    intros T t2 t3 Hlc1 H2 H3 IH Hsucc.
  - (* tm_bvar *)
    apply R_intro_nonvalue with (t := tm_if (tm_bvar i) t2 t3).
    + apply lc_if; [exact Hlc1 | apply R_lc with (T := T); exact H2
                   | apply R_lc with (T := T); exact H3].
    + apply value_not_if.
    + intros s Hs.
      destruct (step_if_l (tm_bvar i) t2 t3 s (value_not_bvar i) Hs) as [t1' [Hs' ->]].
      exact (IH t1' Hs' T t2 t3 (lc_step _ _ Hlc1 Hs') H2 H3).
  - (* tm_fvar *)
    apply R_intro_nonvalue with (t := tm_if (tm_fvar x) t2 t3).
    + apply lc_if; [exact Hlc1 | apply R_lc with (T := T); exact H2
                   | apply R_lc with (T := T); exact H3].
    + apply value_not_if.
    + intros s Hs.
      destruct (step_if_l (tm_fvar x) t2 t3 s (value_not_fvar x) Hs) as [t1' [Hs' ->]].
      exact (IH t1' Hs' T t2 t3 (lc_step _ _ Hlc1 Hs') H2 H3).
  - (* tm_app *)
    apply R_intro_nonvalue with (t := tm_if (tm_app a b) t2 t3).
    + apply lc_if; [exact Hlc1 | apply R_lc with (T := T); exact H2
                   | apply R_lc with (T := T); exact H3].
    + apply value_not_if.
    + intros s Hs.
      destruct (step_if_l (tm_app a b) t2 t3 s (value_not_app a b) Hs) as [t1' [Hs' ->]].
      exact (IH t1' Hs' T t2 t3 (lc_step _ _ Hlc1 Hs') H2 H3).
  - (* tm_abs *)
    apply R_stuck with (t := tm_if (tm_abs T0 body0) t2 t3).
    + apply lc_if; [exact Hlc1 | apply R_lc with (T := T); exact H2
                   | apply R_lc with (T := T); exact H3].
    + apply value_not_if.
    + intros s Hs. exact (step_if_abs_absurd T0 body0 t2 t3 s Hs).
  - (* tm_true *)
    apply R_back_step with (t' := t2).
    + apply lc_if; [exact Hlc1 | apply R_lc with (T := T); exact H2
                   | apply R_lc with (T := T); exact H3].
    + apply ST_IfTrue; [apply R_lc with (T := T); exact H2
                       | apply R_lc with (T := T); exact H3].
    + intros s Hs. exact (step_if_true t2 t3 s Hs).
    + exact H2.
  - (* tm_false *)
    apply R_back_step with (t' := t3).
    + apply lc_if; [exact Hlc1 | apply R_lc with (T := T); exact H2
                   | apply R_lc with (T := T); exact H3].
    + apply ST_IfFalse; [apply R_lc with (T := T); exact H2
                        | apply R_lc with (T := T); exact H3].
    + intros s Hs. exact (step_if_false t2 t3 s Hs).
    + exact H3.
  - (* tm_if *)
    apply R_intro_nonvalue with (t := tm_if (tm_if a b c) t2 t3).
    + apply lc_if; [exact Hlc1 | apply R_lc with (T := T); exact H2
                   | apply R_lc with (T := T); exact H3].
    + apply value_not_if.
    + intros s Hs.
      destruct (step_if_l (tm_if a b c) t2 t3 s (value_not_if a b c) Hs) as [t1' [Hs' ->]].
      exact (IH t1' Hs' T t2 t3 (lc_step _ _ Hlc1 Hs') H2 H3).
Qed.

(** ** The fundamental theorem. *)

Theorem fundamental : forall Gamma t T,
  has_type Gamma t T ->
  forall rho,
    (forall x, locally_closed (rho x)) ->
    (forall x S, Gamma x = Some S -> R S (rho x)) ->
    R T (subst rho t).
Proof.
  intros Gamma t T Hty.
  induction Hty as [Gamma0 x T0 HVar
                 | L Gamma0 T1 T2 t1 Hprem IHAbs
                 | Gamma0 t1 t2 T1 T2 H1 IH1 H2 IH2
                 | Gamma0 | Gamma0
                 | Gamma0 t1 t2 t3 T0 H1 IH1 H2 IH2 H3 IH3];
    intros rho Hrl Hrc.
  - (* T_Var *) simpl. apply Hrc. exact HVar.
  - (* T_Abs *) simpl. apply R_abs_intro.
    + (* local closure *) apply lc_abs. apply subst_lc.
      * exact Hrl.
      * destruct (fresh_atom L t1) as [xx [HxL _]].
        pose proof (typing_lc _ _ _ (Hprem xx HxL)) as Hp.
        apply lc_open_rec_inv with (k := 0) (u := tm_fvar xx) in Hp.
        exact Hp.
    + (* body property *) intros v Hv Hrv.
      destruct (fresh_atom L t1) as [xx [HxL Hxt]].
      assert (Hlce : forall y, locally_closed (extend rho xx v y)).
      { intros y. unfold extend. destruct (Nat.eqb xx y) eqn:E.
        - apply Nat.eqb_eq in E. subst. apply R_lc with (T := T1). exact Hrv.
        - apply Hrl. }
      assert (Hcte : forall y S,
                update Gamma0 xx T1 y = Some S -> R S (extend rho xx v y)).
      { intros y S Hy. unfold update in Hy. unfold extend.
        destruct (Nat.eqb xx y) eqn:E.
        - apply Nat.eqb_eq in E. subst. inversion Hy. subst. exact Hrv.
        - apply Hrc. exact Hy. }
      pose proof (IHAbs xx HxL (extend rho xx v) Hlce Hcte) as Hb.
      rewrite (subst_open t1 rho xx v Hrl Hxt) in Hb.
      exact Hb.
  - (* T_App *) simpl. apply R_app with (A := T1) (B := T2).
    + apply IH1; assumption.
    + apply IH2; assumption.
  - (* T_True *) simpl. split.
    + apply value_SN. apply v_true.
    + apply lc_true.
  - (* T_False *) simpl. split.
    + apply value_SN. apply v_false.
    + apply lc_false.
  - (* T_If *) simpl. apply R_if.
    + apply IH1; assumption.
    + apply IH2; assumption.
    + apply IH3; assumption.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Hty.
  pose proof (fundamental empty t T Hty (fun x => tm_fvar x)) as Hf.
  assert (Hrl : forall x, locally_closed ((fun x => tm_fvar x) x)).
  { intro x. apply lc_fvar. }
  assert (Hrc : forall x S, empty x = Some S -> R S ((fun x => tm_fvar x) x)).
  { intros x S Hx. unfold empty in Hx. discriminate. }
  specialize (Hf Hrl Hrc).
  rewrite subst_id in Hf.
  apply R_SN with (T := T). exact Hf.
Qed.

End STLCCBVNormalizationTask.
