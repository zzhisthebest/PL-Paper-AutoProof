(** STLC call-by-value strong-normalization benchmark.
    No if-then-else, non-determinism, or recursion is included. *)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Relations.Relation_Definitions.
From Stdlib Require Import Lia.
Import ListNotations.

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

(** Target theorem: strong normalization for the supplied CBV relation. *)

(** ** Auxiliary definitions and lemmas for the normalization proof. *)

(** *** Substitution of free variables *)

Definition extend (f : atom -> tm) (x : atom) (v : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then v else f y.

Fixpoint subst (f : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => f x
  | tm_app t1 t2 => tm_app (subst f t1) (subst f t2)
  | tm_abs T t1 => tm_abs T (subst f t1)
  | tm_true => tm_true
  | tm_false => tm_false
  end.

Fixpoint fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ => nil
  | tm_fvar x => [x]
  | tm_app t1 t2 => fv t1 ++ fv t2
  | tm_abs _ t1 => fv t1
  | tm_true => nil
  | tm_false => nil
  end.

Fixpoint max_list (l : list nat) : nat :=
  match l with
  | nil => 0
  | x :: xs => Nat.max x (max_list xs)
  end.

Definition fresh (l : list atom) : atom := S (max_list l).

Lemma max_list_spec : forall (l : list nat) (x : nat), In x l -> x <= max_list l.
Proof.
  induction l as [| a l IH]; intros x Hin; simpl in *.
  - destruct Hin.
  - destruct Hin as [-> | Hin].
    + apply Nat.le_max_l.
    + apply Nat.le_trans with (max_list l); [apply IH; assumption | apply Nat.le_max_r].
Qed.

Lemma fresh_spec : forall (l : list atom), ~ In (fresh l) l.
Proof.
  intros l Hin. unfold fresh in Hin. apply max_list_spec in Hin.
  pose proof (Nat.lt_succ_diag_r (max_list l)). lia.
Qed.

Lemma exists_fresh : forall (l : list atom), exists x, ~ In x l.
Proof. intros l. exists (fresh l). apply fresh_spec. Qed.

(** *** Local closure properties *)

Lemma lc_at_bvar_inv : forall k i, lc_at k (tm_bvar i) -> i < k.
Proof. intros k i H. inversion H. assumption. Qed.

Lemma lc_at_app_inv : forall k t1 t2,
  lc_at k (tm_app t1 t2) -> lc_at k t1 /\ lc_at k t2.
Proof. intros k t1 t2 H. inversion H. split; assumption. Qed.

Lemma lc_at_abs_inv : forall k T t,
  lc_at k (tm_abs T t) -> lc_at (S k) t.
Proof. intros k T t H. inversion H. assumption. Qed.

Lemma lc_at_mono : forall t k k', k <= k' -> lc_at k t -> lc_at k' t.
Proof.
  intros t. induction t; intros k k' Hle H.
  - apply lc_bvar. apply lc_at_bvar_inv in H. lia.
  - apply lc_fvar.
  - apply lc_at_app_inv in H as [H1 H2]. apply lc_app.
    + exact (IHt1 k k' Hle H1).
    + exact (IHt2 k k' Hle H2).
  - apply lc_abs. apply IHt with (k := S k); [lia | apply lc_at_abs_inv in H; assumption].
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma lc_at_open_rec : forall t k, lc_at (S k) t -> forall u,
  lc_at k u -> lc_at k (open_rec k u t).
Proof.
  induction t; intros k H u Hu; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. exact Hu.
    + apply Nat.eqb_neq in E. apply lc_bvar. apply lc_at_bvar_inv in H. lia.
  - apply lc_fvar.
  - apply lc_at_app_inv in H as [H1 H2]. apply lc_app; [apply IHt1 | apply IHt2]; assumption.
  - apply lc_abs. apply IHt with (k := S k).
    + apply lc_at_abs_inv in H. exact H.
    + apply lc_at_mono with (k := k); [lia | exact Hu].
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma open_rec_lc_gen : forall t j, lc_at j t -> forall k u, j <= k -> open_rec k u t = t.
Proof.
  induction t; intros j Hj k u Hjk; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. exfalso. apply lc_at_bvar_inv in Hj. lia.
    + reflexivity.
  - reflexivity.
  - apply lc_at_app_inv in Hj as [H1 H2].
    rewrite (IHt1 j H1 k u Hjk). rewrite (IHt2 j H2 k u Hjk). reflexivity.
  - apply lc_at_abs_inv in Hj. apply f_equal.
    apply (IHt (S j) Hj (S k) u). lia.
  - reflexivity.
  - reflexivity.
Qed.

Lemma open_rec_lc_inv : forall t k x,
  lc_at k (open_rec k (tm_fvar x) t) -> lc_at (S k) t.
Proof.
  induction t; intros k y H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E; simpl in H.
    + apply Nat.eqb_eq in E. subst n. apply lc_bvar. lia.
    + apply lc_bvar. apply lc_at_bvar_inv in H. lia.
  - apply lc_fvar.
  - apply lc_at_app_inv in H as [H1 H2]. apply lc_app.
    + exact (IHt1 k y H1).
    + exact (IHt2 k y H2).
  - apply lc_abs. apply (IHt (S k) y). apply lc_at_abs_inv in H. exact H.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma subst_open_rec : forall t f,
  (forall x, lc_at 0 (f x)) ->
  forall k u, subst f (open_rec k u t) = open_rec k (subst f u) (subst f t).
Proof.
  induction t; intros f Hf k u; simpl.
  - destruct (Nat.eqb k n) eqn:E; simpl; reflexivity.
  - symmetry. apply (open_rec_lc_gen (f a) 0). apply Hf. lia.
  - rewrite (IHt1 f Hf). rewrite (IHt2 f Hf). reflexivity.
  - rewrite (IHt f Hf). reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma subst_extend_fresh : forall t f x v,
  ~ In x (fv t) -> subst (extend f x v) t = subst f t.
Proof.
  induction t; intros f y w Hfresh; simpl in *.
  - reflexivity.
  - unfold extend. destruct (Nat.eqb y a) eqn:E.
    + apply Nat.eqb_eq in E. subst a. exfalso. apply Hfresh. simpl. auto.
    + reflexivity.
  - assert (H1 : ~ In y (fv t1)) by (intro H; apply Hfresh; apply in_or_app; now left).
    assert (H2 : ~ In y (fv t2)) by (intro H; apply Hfresh; apply in_or_app; now right).
    rewrite (IHt1 f y w H1). rewrite (IHt2 f y w H2). reflexivity.
  - rewrite (IHt f y w Hfresh). reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma lc_subst : forall t f k,
  (forall x, lc_at k (f x)) -> lc_at k t -> lc_at k (subst f t).
Proof.
  induction t; intros f k Hf H; simpl.
  - exact H.
  - apply Hf.
  - apply lc_at_app_inv in H as [H1 H2]. apply lc_app; [apply IHt1 | apply IHt2]; assumption.
  - apply lc_abs. apply IHt with (k := S k).
    + intros x. apply lc_at_mono with (k := k); [lia | apply Hf].
    + apply lc_at_abs_inv in H. exact H.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma subst_id : forall t, subst (fun x => tm_fvar x) t = t.
Proof.
  induction t; simpl; try reflexivity; [rewrite IHt1, IHt2 | rewrite IHt]; reflexivity.
Qed.

(** *** Values, steps, and local closure *)

Lemma value_lc : forall v, value v -> locally_closed v.
Proof.
  intros v Hv. induction Hv.
  - assumption.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma abs_no_step : forall (T : ty) (t t' : tm), ~ step (tm_abs T t) t'.
Proof. intros T t t' H. inversion H. Qed.

Lemma true_no_step : forall t', ~ step tm_true t'.
Proof. intros t' H. inversion H. Qed.

Lemma false_no_step : forall t', ~ step tm_false t'.
Proof. intros t' H. inversion H. Qed.

Lemma value_no_step : forall v t', value v -> ~ step v t'.
Proof. intros v t' Hv Hstep. destruct Hv; inversion Hstep. Qed.

Lemma step_lc_fwd : forall t t', step t t' -> locally_closed t -> locally_closed t'.
Proof.
  intros t t' H. induction H; intros Hlc.
  - apply lc_at_app_inv in Hlc as [Habs Hv].
    apply lc_at_open_rec with (k := 0).
    + apply lc_at_abs_inv in Habs. exact Habs.
    + apply value_lc. assumption.
  - apply lc_at_app_inv in Hlc as [Hlc1 Hlc2]. apply lc_app.
    + apply IHstep. assumption.
    + assumption.
  - apply lc_at_app_inv in Hlc as [Hv1 Hlc2]. apply lc_app.
    + apply value_lc. assumption.
    + apply IHstep. assumption.
Qed.

Lemma step_lc_back : forall t t', step t t' -> locally_closed t' -> locally_closed t.
Proof.
  intros t t' H. induction H; intros Hlc.
  - apply lc_app.
    + assumption.
    + apply value_lc. assumption.
  - apply lc_at_app_inv in Hlc as [H1 H2]. apply lc_app.
    + apply IHstep. assumption.
    + assumption.
  - apply lc_at_app_inv in Hlc as [H1 H2]. apply lc_app.
    + apply value_lc. assumption.
    + apply IHstep. assumption.
Qed.

Lemma step_app_inv : forall t1 t2 s,
  step (tm_app t1 t2) s ->
     (exists T body v, t1 = tm_abs T body /\ t2 = v /\ s = open body v
                       /\ locally_closed (tm_abs T body) /\ value v)
  \/ (exists t1', step t1 t1' /\ s = tm_app t1' t2 /\ locally_closed t2)
  \/ (exists v1 t2', t1 = v1 /\ value v1 /\ step t2 t2' /\ s = tm_app v1 t2').
Proof.
  intros t1 t2 s H. inversion H; subst; eauto 10.
Qed.

Lemma value_step_absurd : forall v t', value v -> step v t' -> False.
Proof. intros v t' Hv Hs. destruct Hv; inversion Hs. Qed.

Ltac solve_step_absurd :=
  exfalso;
  match goal with
  | Hs : step (tm_abs ?T ?b) ?t' |- _ => exact (abs_no_step T b t' Hs)
  | Hv : value ?v, Hs : step ?v ?t' |- _ => exact (value_step_absurd v t' Hv Hs)
  end.

Lemma step_det : forall t t1 t2, step t t1 -> step t t2 -> t1 = t2.
Proof.
  intros t t1 t2 H1 H2. revert H2. revert t2.
  induction H1; intros s H2.
  - inversion H2; subst.
    + reflexivity.
    + solve_step_absurd.
    + solve_step_absurd.
  - inversion H2; subst.
    + solve_step_absurd.
    + f_equal. apply IHstep. eassumption.
    + solve_step_absurd.
  - inversion H2; subst.
    + solve_step_absurd.
    + solve_step_absurd.
    + f_equal. apply IHstep. eassumption.
Qed.

(** *** Typing and local closure *)

Lemma has_type_lc : forall Gamma t T, has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T H. induction H.
  - apply lc_fvar.
  - destruct (exists_fresh L) as [y Hy].
    apply lc_abs. apply open_rec_lc_inv with (k := 0) (x := y).
    apply H0. assumption.
  - apply lc_app; assumption.
  - apply lc_true.
  - apply lc_false.
Qed.

(** *** The logical relation *)

(** [R T t] is a unary, type-indexed reducibility predicate: at [Bool]
    it requires local closure and strong normalization; at [T1 -> T2] it
    additionally requires that every reducible argument be mapped to a
    reducible result.  We prove that [R] implies local closure and strong
    normalization, that it is closed under both forward and backward
    reduction, and that abstractions whose bodies are reducible after
    opening with any reducible value are reducible. *)

Fixpoint R (T : ty) : tm -> Prop :=
  match T with
  | Ty_Bool => fun t => locally_closed t /\ strongly_normalizing t
  | Ty_Arrow T1 T2 => fun t =>
      locally_closed t /\ strongly_normalizing t /\
      (forall u, R T1 u -> R T2 (tm_app t u))
  end.

Definition is_abs (t : tm) : Prop := exists T body, t = tm_abs T body.

Lemma SN_step : forall t t', strongly_normalizing t -> step t t' -> strongly_normalizing t'.
Proof.
  intros t t' H Hstep. inversion H as [u Hpred]. apply Hpred. assumption.
Qed.

Lemma R_props : forall T,
  (forall t, R T t -> strongly_normalizing t) /\
  (forall t, R T t -> locally_closed t) /\
  (forall t t', R T t -> step t t' -> R T t') /\
  (forall t, locally_closed t -> ~ is_abs t ->
     (forall t', step t t' -> R T t') -> R T t).
Proof.
  induction T as [| T1 IH1 T2 IH2].
  - (* Bool *)
    simpl. split.
    + intros t [Hlc Hsn]. exact Hsn.
    + split.
      * intros t [Hlc Hsn]. exact Hlc.
      * split.
        -- intros t t' [Hlc Hsn] Hstep. split.
           ++ apply step_lc_fwd with (t := t); assumption.
           ++ apply SN_step with (t := t); assumption.
        -- intros t Hlc Hnonabs Hsucc. split; [assumption|].
           apply SN_intro. intros t' Hstep. destruct (Hsucc t' Hstep) as [Hlc' Hsn']. exact Hsn'.
  - (* Arrow *)
    destruct IH1 as [IH1_sn [IH1_lc [IH1_fwd IH1_exp]]].
    destruct IH2 as [IH2_sn [IH2_lc [IH2_fwd IH2_exp]]].
    split.
    + (* P1: R implies SN *) intros t HR. simpl in HR. destruct HR as [Hlc [Hsn Happ]]. exact Hsn.
    + split.
      * (* P2: R implies lc *) intros t HR. simpl in HR. destruct HR as [Hlc _]. exact Hlc.
      * split.
        -- (* P3: forward closure *)
           intros t t' HR Hstep. simpl in HR. destruct HR as [Hlc [Hsn Happ]].
           simpl. split.
           ++ apply step_lc_fwd with (t := t); assumption.
           ++ split.
              ** apply SN_step with (t := t); assumption.
              ** intros u Hu. apply IH2_fwd with (t := tm_app t u).
                 --- apply Happ. assumption.
                 --- apply ST_App1; [assumption | apply IH1_lc; assumption].
        -- (* P4: backward closure from all successors, non-abstractions *)
           intros t Hlc Hnonabs Hsucc. simpl. split; [assumption|]. split.
           ++ apply SN_intro. intros t' Hstep. destruct (Hsucc t' Hstep) as [_ [Hsn' _]]. exact Hsn'.
           ++ intros u Hu.
              assert (Haux : forall w, strongly_normalizing w -> R T1 w -> R T2 (tm_app t w)).
              { intros w Hsn. induction Hsn as [w Hsuccw IHw]. intros Hw.
                apply IH2_exp with (t := tm_app t w).
                - apply lc_app; [exact Hlc | apply IH1_lc; exact Hw].
                - intros [T' [body Heq]]. discriminate Heq.
                - intros s Hs. apply step_app_inv in Hs.
                  destruct Hs as [[T' [body [v [Heq_t [Heq_w [Heq_s [Hlcv Hval]]]]]]]
                               | [[t1' [Hstep1 [Heq_s Hlc2]]] | [v1 [w' [Heq_t [Hval [Hstepw Heq_s]]]]]]].
                  + exfalso. apply Hnonabs. exists T', body. exact Heq_t.
                  + subst s. destruct (Hsucc t1' Hstep1) as [_ [_ Happ']]. apply Happ'. exact Hw.
                  + subst s. subst v1. apply IHw.
                    * exact Hstepw.
                    * apply IH1_fwd with (t := w); assumption.
              }
              apply Haux; [apply IH1_sn; exact Hu | exact Hu].
Qed.

(** *** Extracting the closure properties *)

Lemma R_SN : forall T t, R T t -> strongly_normalizing t.
Proof. intros T. exact (proj1 (R_props T)). Qed.

Lemma R_lc : forall T t, R T t -> locally_closed t.
Proof. intros T. exact (proj1 (proj2 (R_props T))). Qed.

Lemma R_fwd : forall T t t', R T t -> step t t' -> R T t'.
Proof. intros T. exact (proj1 (proj2 (proj2 (R_props T)))). Qed.

Lemma R_expand : forall T t, locally_closed t -> ~ is_abs t ->
  (forall t', step t t' -> R T t') -> R T t.
Proof. intros T. exact (proj2 (proj2 (proj2 (R_props T)))). Qed.

Lemma R_step : forall T t t', R T t' -> step t t' -> R T t.
Proof.
  intros T t t' HR Hstep.
  apply R_expand.
  - apply step_lc_back with (t' := t').
    + exact Hstep.
    + exact (R_lc T t' HR).
  - intros [T' [body Heq]]. subst t. exact (abs_no_step T' body t' Hstep).
  - intros s Hs. rewrite (step_det t s t' Hs Hstep). exact HR.
Qed.

Lemma R_app : forall T1 T2 t1 t2,
  R (Ty_Arrow T1 T2) t1 -> R T1 t2 -> R T2 (tm_app t1 t2).
Proof.
  intros T1 T2 t1 t2 HR Hu. simpl in HR.
  destruct HR as [_ [_ Happ]]. apply Happ. exact Hu.
Qed.

(** *** Abstraction lemmas *)

Lemma R_abs_app_aux : forall u,
  strongly_normalizing u ->
  forall T1 T2 body,
    locally_closed (tm_abs T1 body) ->
    (forall v, value v -> R T1 v -> R T2 (open body v)) ->
    R T1 u ->
    R T2 (tm_app (tm_abs T1 body) u).
Proof.
  intros u Hsn. induction Hsn as [u Hsuccu IHu].
  intros T1 T2 body Hlc Hbeta Hu.
  apply R_expand with (t := tm_app (tm_abs T1 body) u).
  - apply lc_app; [exact Hlc | exact (R_lc T1 u Hu)].
  - intros [T' [body' Heq]]. discriminate Heq.
  - intros s Hs. apply step_app_inv in Hs.
    destruct Hs as [[T' [body' [v [Heq_t [Heq_u [Heq_s [Hlcv Hval]]]]]]]
                 | [[t1' [Hstep1 [Heq_s Hlc2]]] | [v1 [u' [Heq_t [Hval [Hstepu Heq_s]]]]]]].
    + subst s. subst v. injection Heq_t as HTeq Hbeq. subst body'. subst T'.
      apply Hbeta; [exact Hval | exact Hu].
    + subst s. exfalso. exact (abs_no_step T1 body t1' Hstep1).
    + subst s. subst v1.
      apply (IHu u' Hstepu T1 T2 body Hlc Hbeta).
      apply (R_fwd T1 u u' Hu Hstepu).
Qed.

Lemma R_abs : forall T1 T2 body,
  locally_closed (tm_abs T1 body) ->
  (forall v, value v -> R T1 v -> R T2 (open body v)) ->
  R (Ty_Arrow T1 T2) (tm_abs T1 body).
Proof.
  intros T1 T2 body Hlc Hbeta. simpl. split; [exact Hlc|]. split.
  - apply SN_intro. intros t' Hstep. exfalso. exact (abs_no_step T1 body t' Hstep).
  - intros u Hu. apply (R_abs_app_aux u).
    + apply (R_SN T1 u Hu).
    + exact Hlc.
    + exact Hbeta.
    + exact Hu.
Qed.

(** *** Opening with a fresh atom versus substitution *)

Lemma subst_open_fresh : forall f v y t,
  (forall x, lc_at 0 (f x)) ->
  lc_at 0 v ->
  ~ In y (fv t) ->
  subst (extend f y v) (open t (tm_fvar y)) = open (subst f t) v.
Proof.
  intros f v y t Hf Hv Hy.
  assert (Hf' : forall x, lc_at 0 (extend f y v x)).
  { intros x. unfold extend. destruct (Nat.eqb y x); [exact Hv | apply Hf]. }
  change (subst (extend f y v) (open_rec 0 (tm_fvar y) t) = open_rec 0 v (subst f t)).
  rewrite (subst_open_rec t (extend f y v) Hf' 0 (tm_fvar y)).
  change (open_rec 0 (if Nat.eqb y y then v else f y) (subst (extend f y v) t) = open_rec 0 v (subst f t)).
  rewrite Nat.eqb_refl. cbn.
  rewrite (subst_extend_fresh t f y v Hy). reflexivity.
Qed.

(** *** The fundamental theorem *)

Lemma fundamental : forall Gamma t T,
  has_type Gamma t T ->
  forall f,
    (forall x, lc_at 0 (f x)) ->
    (forall x T0, Gamma x = Some T0 -> R T0 (f x)) ->
    R T (subst f t).
Proof.
  intros Gamma t T H. induction H; intros f Hflc HfR.
  - (* T_Var *) apply HfR. exact H.
  - (* T_Abs *)
    apply R_abs.
    + (* local closure of the substituted abstraction *)
      destruct (exists_fresh (L ++ fv t1)) as [y Hy].
      assert (HyL : ~ In y L) by (intro Hc; apply Hy; apply in_or_app; now left).
      assert (Hyfv : ~ In y (fv t1)) by (intro Hc; apply Hy; apply in_or_app; now right).
      apply lc_abs.
      assert (Hty : has_type (update Gamma y T1) (open t1 (tm_fvar y)) T2) by (apply H; exact HyL).
      apply has_type_lc in Hty.
      apply open_rec_lc_inv with (k := 0) in Hty.
      apply lc_subst with (k := 1).
      * intros x. apply lc_at_mono with (k := 0); [lia | apply Hflc].
      * exact Hty.
    + (* the beta obligation *)
      intros v Hv HRv.
      destruct (exists_fresh (L ++ fv t1)) as [y Hy].
      assert (HyL : ~ In y L) by (intro Hc; apply Hy; apply in_or_app; now left).
      assert (Hyfv : ~ In y (fv t1)) by (intro Hc; apply Hy; apply in_or_app; now right).
      assert (Hf'lc : forall x, lc_at 0 (extend f y v x)).
      { intros x. unfold extend. destruct (Nat.eqb y x); [apply value_lc; exact Hv | apply Hflc]. }
      assert (Hf'R : forall x T0, update Gamma y T1 x = Some T0 -> R T0 (extend f y v x)).
      { intros x T0 Hctx. unfold update in Hctx.
        destruct (Nat.eqb y x) eqn:E.
        - apply Nat.eqb_eq in E. subst x. injection Hctx as HTeq. subst T0.
          unfold extend. rewrite Nat.eqb_refl. cbn. exact HRv.
        - unfold extend. rewrite E. cbn.
          apply HfR. exact Hctx. }
      pose proof (H0 y HyL (extend f y v) Hf'lc Hf'R) as Hres.
      assert (Heq : subst (extend f y v) (open t1 (tm_fvar y)) = open (subst f t1) v).
      { apply (subst_open_fresh f v y t1 Hflc (value_lc v Hv) Hyfv). }
      rewrite Heq in Hres.
      exact Hres.
  - (* T_App *)
    apply (R_app T1 T2 (subst f t1) (subst f t2)).
    + apply IHhas_type1; assumption.
    + apply IHhas_type2; assumption.
  - (* T_True *)
    split.
    + apply lc_true.
    + apply SN_intro. intros t' Hstep. inversion Hstep.
  - (* T_False *)
    split.
    + apply lc_false.
    + apply SN_intro. intros t' Hstep. inversion Hstep.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Hty.
  assert (HR : R T (subst (fun x => tm_fvar x) t)).
  { apply (fundamental empty t T Hty (fun x => tm_fvar x)).
    - intros x. apply lc_fvar.
    - intros x T0 Hctx. unfold empty in Hctx. discriminate Hctx. }
  rewrite subst_id in HR.
  apply (R_SN T t HR).
Qed.

End STLCNormalizationNoneHardTask.
