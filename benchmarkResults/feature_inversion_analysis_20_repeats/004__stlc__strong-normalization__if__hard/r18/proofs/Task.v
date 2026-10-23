(** STLC call-by-value strong-normalization benchmark task. *)

From Stdlib Require Import Arith.PeanoNat.
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

(** Target theorem: strong normalization for the supplied CBV relation. *)

Inductive strongly_normalizing : tm -> Prop :=
  | SN_intro : forall t,
      (forall t', t --> t' -> strongly_normalizing t') ->
      strongly_normalizing t.

(** ** Logical-relation proof of strong normalization *)

(** Free-variable substitution.  Bound variables are untouched. *)
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

(** Free variables of a term. *)
Fixpoint fvars (t : tm) : list atom :=
  match t with
  | tm_bvar _ => nil
  | tm_fvar x => x :: nil
  | tm_app t1 t2 => fvars t1 ++ fvars t2
  | tm_abs _ t1 => fvars t1
  | tm_true => nil
  | tm_false => nil
  | tm_if t1 t2 t3 => fvars t1 ++ fvars t2 ++ fvars t3
  end.

(** Extension of a semantic substitution. *)
Definition extend (sigma : atom -> tm) (x : atom) (v : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then v else sigma y.

Definition is_abs (t : tm) : bool :=
  match t with
  | tm_abs _ _ => true
  | _ => false
  end.

Definition not_abs (t : tm) : Prop := is_abs t = false.

(** The unary, type-indexed logical relation.  For a function type we
    require strong normalization plus the usual application property. *)
Fixpoint LR (T : ty) (t : tm) : Prop :=
  match T with
  | Ty_Bool => strongly_normalizing t
  | Ty_Arrow T1 T2 =>
      strongly_normalizing t /\
      (forall v, value v -> LR T1 v -> LR T2 (tm_app t v))
  end.

(** Interpretation of typing contexts: [sigma] maps every atom to a
    locally closed term, and every variable of the context is mapped to
    a term in the relation at its type. *)
Definition sem_ctx (Gamma : context) (sigma : atom -> tm) : Prop :=
  (forall x, locally_closed (sigma x)) /\
  (forall x T, Gamma x = Some T -> LR T (sigma x)).

(** ** Basic facts about values and strong normalization *)

Lemma value_no_step : forall v t', value v -> v --> t' -> False.
Proof.
  intros v t' Hv. revert t'.
  induction Hv; intros t' Hstep; inversion Hstep.
Qed.

Lemma abs_no_step : forall A e t', tm_abs A e --> t' -> False.
Proof.
  intros A e t' Hstep. inversion Hstep.
Qed.

(** Tactics for closing impossible step cases. *)
Ltac contra_value_step :=
  exfalso;
  match goal with
  | Hst : ?a --> ?b, Hval : value ?a |- _ =>
      exact (value_no_step a b Hval Hst)
  end.

Ltac contra_abs_step :=
  exfalso;
  match goal with
  | Hst : tm_abs ?A ?e --> ?b |- _ => exact (abs_no_step A e b Hst)
  end.

Lemma value_lc : forall v, value v -> locally_closed v.
Proof.
  intros v Hv. induction Hv.
  - assumption.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma SN_step : forall t t',
  strongly_normalizing t -> t --> t' -> strongly_normalizing t'.
Proof.
  intros t t' HSN. destruct HSN as [t0 Hreds]. intros Hstep.
  apply Hreds. assumption.
Qed.

Lemma SN_true : strongly_normalizing tm_true.
Proof. apply SN_intro. intros t' Hstep. inversion Hstep. Qed.

Lemma SN_false : strongly_normalizing tm_false.
Proof. apply SN_intro. intros t' Hstep. inversion Hstep. Qed.

(** ** Properties of the logical relation *)

Lemma LR_SN : forall T t, LR T t -> strongly_normalizing t.
Proof.
  induction T as [| T1 IH1 T2 IH2]; intros t HLR; simpl in HLR.
  - exact HLR.
  - destruct HLR as [HSN _]. exact HSN.
Qed.

Lemma LR_step : forall T t t', LR T t -> t --> t' -> LR T t'.
Proof.
  induction T as [| T1 IH1 T2 IH2].
  - intros t t' HLR Hstep. simpl in HLR. simpl.
    apply SN_step with (t := t); assumption.
  - intros t t' HLR Hstep. simpl in HLR. simpl.
    destruct HLR as [HSN Harr]. split.
    + apply SN_step with (t := t); assumption.
    + intros v Hv HLRv. apply IH2 with (t := tm_app t v).
      * apply Harr; assumption.
      * apply ST_App1; [assumption | apply value_lc; assumption].
Qed.

(** Every one-step reduct of [t] being related implies [t] is related,
    provided [t] is not an abstraction (the only redex shape whose
    reduct is not of the form "function reduct applied to argument"). *)
Lemma LR_of_reducts : forall T t,
  not_abs t ->
  (forall t', t --> t' -> LR T t') ->
  LR T t.
Proof.
  induction T as [| T1 IH1 T2 IH2]; intros t Hna Hreds; simpl.
  - apply SN_intro. intros t' Hstep. apply Hreds in Hstep. simpl in Hstep.
    exact Hstep.
  - split.
    + apply SN_intro. intros t' Hstep.
      pose proof (Hreds t' Hstep) as HLR. simpl in HLR.
      destruct HLR as [HSN _]. exact HSN.
    + intros v Hv HLRv. apply IH2.
      * reflexivity.
      * intros w Hstep. inversion Hstep; subst.
        -- (* ST_AppAbs *) exfalso. unfold not_abs in Hna. simpl in Hna.
           discriminate Hna.
        -- (* ST_App1 *)
           match goal with
           | Hst : ?X --> ?u |- LR ?Ty (tm_app ?u ?b) =>
             pose proof (Hreds u Hst) as HLR; simpl in HLR;
             destruct HLR as [HSN Harr]; apply Harr; assumption
           end.
        -- (* ST_App2 *) contra_value_step.
Qed.

(** Abstractions are related whenever their bodies, opened with any
    related value, are related. *)
Lemma LR_abs : forall A B e,
  (forall v, value v -> LR A v -> LR B (open e v)) ->
  LR (Ty_Arrow A B) (tm_abs A e).
Proof.
  intros A B e Hbody. simpl. split.
  - apply SN_intro. intros t' Hstep. inversion Hstep.
  - intros v Hv HLRv. apply LR_of_reducts.
    + reflexivity.
    + intros w Hstep. inversion Hstep; subst.
      * apply Hbody; assumption.
      * contra_abs_step.
      * contra_value_step.
Qed.

(** Application of a related value to a related term. *)
Lemma LR_app_value : forall A B (v1 : tm),
  value v1 ->
  LR (Ty_Arrow A B) v1 ->
  forall t2, LR A t2 -> LR B (tm_app v1 t2).
Proof.
  intros A B v1 Hv1 HLR1.
  simpl in HLR1. destruct HLR1 as [HSN1 Harr].
  assert (Haux : forall t2,
    strongly_normalizing t2 -> LR A t2 -> LR B (tm_app v1 t2)).
  { intros t2 HSN2. induction HSN2 as [t2 Hreds IH]. intros H2.
    apply LR_of_reducts.
    - reflexivity.
    - intros w Hstep. inversion Hstep; subst.
      + (* ST_AppAbs *)
        match goal with
        | Hst : tm_app (tm_abs ?T0 ?body) ?arg --> ?w |- LR ?TyB ?w2 =>
            apply LR_step with (t := tm_app (tm_abs T0 body) arg)
        end.
        * apply Harr; assumption.
        * assumption.
      + (* ST_App1 *) contra_value_step.
      + (* ST_App2 *) apply IH.
        * assumption.
        * apply LR_step with (t := t2); assumption.
  }
  intros t2 H2. apply Haux.
  - apply (LR_SN A t2). assumption.
  - assumption.
Qed.

(** The application lemma for the logical relation. *)
Lemma LR_app : forall A B t1,
  LR (Ty_Arrow A B) t1 ->
  forall t2, LR A t2 -> LR B (tm_app t1 t2).
Proof.
  intros A B t1 HLR1.
  pose proof (LR_SN (Ty_Arrow A B) t1 HLR1) as HSN1.
  revert HLR1.
  induction HSN1 as [t1 Hreds IH].
  intros HLR1 t2 H2.
  apply LR_of_reducts.
  - reflexivity.
  - intros w Hstep. inversion Hstep; subst.
    + (* ST_AppAbs *) simpl in HLR1. destruct HLR1 as [HSN Harr].
      apply LR_step with (t := tm_app (tm_abs T t) t2).
      * apply Harr; assumption.
      * apply ST_AppAbs; assumption.
    + (* ST_App1 *) apply IH.
      * assumption.
      * apply LR_step with (t := t1); assumption.
      * assumption.
    + (* ST_App2 *) apply (LR_app_value A B t1).
      * assumption.
      * assumption.
      * apply LR_step with (t := t2); assumption.
Qed.

(** The [if] lemma for the logical relation. *)
Lemma LR_if : forall T t0 t1 t2,
  strongly_normalizing t0 -> LR T t1 -> LR T t2 -> LR T (tm_if t0 t1 t2).
Proof.
  intros T t0 t1 t2 HSN0. revert t1 t2.
  induction HSN0 as [t0 Hreds IH].
  intros t1 t2 H1 H2.
  apply LR_of_reducts.
  - reflexivity.
  - intros w Hstep. inversion Hstep; subst.
    + assumption.
    + assumption.
    + apply IH; assumption.
Qed.

(** ** Substitution lemmas *)

Lemma lc_at_mono : forall k t, lc_at k t -> forall k', k <= k' -> lc_at k' t.
Proof.
  intros k t H. induction H as
    [ k i Hlt | k x | k t1 t2 H1 IH1 H2 IH2 | k T t1 H1 IH1 | k | k |
      k t1 t2 t3 H1 IH1 H2 IH2 H3 IH3 ]; intros k' Hle.
  - apply lc_bvar. apply Nat.lt_le_trans with k; assumption.
  - apply lc_fvar.
  - apply lc_app; [apply IH1 | apply IH2]; assumption.
  - apply lc_abs. apply IH1.
    exact (proj1 (Nat.succ_le_mono k k') Hle).
  - apply lc_true.
  - apply lc_false.
  - apply lc_if; [apply IH1 | apply IH2 | apply IH3]; assumption.
Qed.

Lemma open_rec_lc : forall k t, lc_at k t -> forall u, open_rec k u t = t.
Proof.
  intros k t H. induction H as
    [ k i Hlt | k x | k t1 t2 H1 IH1 H2 IH2 | k T t1 H1 IH1 | k | k |
      k t1 t2 t3 H1 IH1 H2 IH2 H3 IH3 ]; intros u; simpl.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst i. exfalso.
      exact (Nat.lt_irrefl k Hlt).
    + reflexivity.
  - reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH1. reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IH1, IH2, IH3. reflexivity.
Qed.

Lemma open_rec_lc0 : forall t, locally_closed t -> forall u k, open_rec k u t = t.
Proof.
  intros t Hlc u k. apply open_rec_lc.
  apply lc_at_mono with (k := 0); [assumption | apply Nat.le_0_l].
Qed.

Lemma subst_open_rec : forall sigma u t k,
  (forall x, locally_closed (sigma x)) ->
  subst_tm sigma (open_rec k u t) =
  open_rec k (subst_tm sigma u) (subst_tm sigma t).
Proof.
  intros sigma u t.
  induction t as [i | x | t1 IH1 t2 IH2 | T t1 IH | | |
                  t1 IH1 t2 IH2 t3 IH3]; intros k Hlc; simpl.
  - destruct (Nat.eqb k i); reflexivity.
  - symmetry. apply open_rec_lc0. apply Hlc.
  - rewrite (IH1 k Hlc), (IH2 k Hlc). reflexivity.
  - rewrite (IH (S k) Hlc). reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite (IH1 k Hlc), (IH2 k Hlc), (IH3 k Hlc). reflexivity.
Qed.

Lemma not_in_app_l : forall (l1 l2 : list atom) x,
  ~ In x (l1 ++ l2) -> ~ In x l1.
Proof.
  intros l1 l2 x H Hin. apply H. apply in_or_app. left. assumption.
Qed.

Lemma not_in_app_r : forall (l1 l2 : list atom) x,
  ~ In x (l1 ++ l2) -> ~ In x l2.
Proof.
  intros l1 l2 x H Hin. apply H. apply in_or_app. right. assumption.
Qed.

Lemma subst_extend_neq : forall sigma x v t,
  ~ In x (fvars t) -> subst_tm (extend sigma x v) t = subst_tm sigma t.
Proof.
  intros sigma x v t.
  induction t as [i | y | t1 IH1 t2 IH2 | T t1 IH | | |
                  t1 IH1 t2 IH2 t3 IH3]; intros Hx; simpl.
  - reflexivity.
  - unfold extend. destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. subst y. exfalso. apply Hx. simpl. left. reflexivity.
    + reflexivity.
  - change (~ In x (fvars t1 ++ fvars t2)) in Hx.
    assert (H1 : ~ In x (fvars t1)).
    { intros Hc. apply Hx. apply in_or_app. left. assumption. }
    assert (H2 : ~ In x (fvars t2)).
    { intros Hc. apply Hx. apply in_or_app. right. assumption. }
    change (tm_app (subst_tm (extend sigma x v) t1) (subst_tm (extend sigma x v) t2) =
            tm_app (subst_tm sigma t1) (subst_tm sigma t2)).
    rewrite (IH1 H1), (IH2 H2). reflexivity.
  - change (tm_abs T (subst_tm (extend sigma x v) t1) =
            tm_abs T (subst_tm sigma t1)).
    rewrite (IH Hx). reflexivity.
  - reflexivity.
  - reflexivity.
  - change (~ In x (fvars t1 ++ fvars t2 ++ fvars t3)) in Hx.
    assert (H1 : ~ In x (fvars t1)).
    { intros Hc. apply Hx. apply in_or_app. left. assumption. }
    assert (H2 : ~ In x (fvars t2)).
    { intros Hc. apply Hx. apply in_or_app. right. apply in_or_app. left. assumption. }
    assert (H3 : ~ In x (fvars t3)).
    { intros Hc. apply Hx. apply in_or_app. right. apply in_or_app. right. assumption. }
    change (tm_if (subst_tm (extend sigma x v) t1) (subst_tm (extend sigma x v) t2)
                  (subst_tm (extend sigma x v) t3) =
            tm_if (subst_tm sigma t1) (subst_tm sigma t2) (subst_tm sigma t3)).
    rewrite (IH1 H1), (IH2 H2), (IH3 H3). reflexivity.
Qed.

Lemma in_le_fold_max : forall (L : list atom) x,
  In x L -> x <= fold_right Nat.max 0 L.
Proof.
  intros L. induction L as [| a L IH]; intros x Hx.
  - destruct Hx.
  - simpl in *. destruct Hx as [-> | Hx].
    + apply Nat.le_max_l.
    + apply Nat.le_trans with (fold_right Nat.max 0 L);
      [apply IH; assumption | apply Nat.le_max_r].
Qed.

Lemma exists_fresh : forall L : list atom, exists x, ~ In x L.
Proof.
  intros L. exists (S (fold_right Nat.max 0 L)).
  intros Hx. apply in_le_fold_max in Hx.
  exact (Nat.nle_succ_diag_l _ Hx).
Qed.

Lemma subst_identity : forall t, subst_tm (fun x => tm_fvar x) t = t.
Proof.
  induction t as [i | x | t1 IH1 t2 IH2 | T t1 IH | | |
                  t1 IH1 t2 IH2 t3 IH3]; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH. reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IH1, IH2, IH3. reflexivity.
Qed.

(** ** Context semantics *)

Lemma extend_eq : forall sigma x v, extend sigma x v x = v.
Proof. intros. unfold extend. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma extend_lc : forall sigma x v,
  (forall y, locally_closed (sigma y)) -> locally_closed v ->
  forall y, locally_closed (extend sigma x v y).
Proof.
  intros sigma x v Hlc Hv y. unfold extend.
  destruct (Nat.eqb x y) eqn:E.
  - assumption.
  - apply Hlc.
Qed.

Lemma sem_ctx_extend : forall Gamma sigma x T1 v,
  sem_ctx Gamma sigma -> value v -> LR T1 v ->
  sem_ctx (update Gamma x T1) (extend sigma x v).
Proof.
  intros Gamma sigma x T1 v [Hlc Hsem] Hval HLR. split.
  - apply extend_lc.
    + assumption.
    + apply value_lc; assumption.
  - intros y T Hy.
    unfold update in Hy. unfold extend.
    destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. subst y. injection Hy as Hy. subst T.
      assumption.
    + apply Hsem. assumption.
Qed.

(** ** Fundamental theorem *)

Lemma typing_LR : forall Gamma t T,
  <{ Gamma |-- t \in T }> ->
  forall sigma, sem_ctx Gamma sigma -> LR T (subst_tm sigma t).
Proof.
  intros Gamma t T Hty.
  induction Hty as
    [ Gamma x T Hx
    | L Gamma T1 T2 t1 Hbody IHbody
    | Gamma t1 t2 T1 T2 Ht1 IH1 Ht2 IH2
    | Gamma
    | Gamma
    | Gamma t1 t2 t3 T H1 IH1 H2 IH2 H3 IH3 ];
    intros sigma Hsem.
  - (* T_Var *) cbn [subst_tm]. apply (proj2 Hsem). assumption.
  - (* T_Abs *) cbn [subst_tm]. apply LR_abs.
    intros v Hv HLRv.
    destruct (exists_fresh (L ++ fvars t1)) as [x Hx].
    pose proof (not_in_app_l L (fvars t1) x Hx) as HxL.
    pose proof (not_in_app_r L (fvars t1) x Hx) as HxF.
    assert (Hlc : forall y, locally_closed (extend sigma x v y)).
    { apply extend_lc.
      - apply (proj1 Hsem).
      - apply value_lc; assumption. }
    pose proof (IHbody x HxL (extend sigma x v)
                  (sem_ctx_extend Gamma sigma x T1 v Hsem Hv HLRv)) as Hres.
    unfold open in Hres.
    rewrite (subst_open_rec (extend sigma x v) (tm_fvar x) t1 0 Hlc) in Hres.
    cbn [subst_tm] in Hres.
    rewrite extend_eq in Hres.
    rewrite (subst_extend_neq sigma x v t1 HxF) in Hres.
    exact Hres.
  - (* T_App *) cbn [subst_tm]. apply (LR_app T1 T2).
    + apply IH1; assumption.
    + apply IH2; assumption.
  - (* T_True *) cbn [subst_tm]. apply SN_true.
  - (* T_False *) cbn [subst_tm]. apply SN_false.
  - (* T_If *) cbn [subst_tm]. apply LR_if.
    + apply IH1; assumption.
    + apply IH2; assumption.
    + apply IH3; assumption.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Hty.
  assert (Hsem : sem_ctx empty (fun x => tm_fvar x)).
  { split.
    - intros x. apply lc_fvar.
    - intros x T0 Hx. unfold empty in Hx. discriminate Hx. }
  pose proof (typing_LR empty t T Hty (fun x => tm_fvar x) Hsem) as H.
  rewrite subst_identity in H.
  apply (LR_SN T t) in H.
  exact H.
Qed.

End STLCCBVNormalizationTask.
