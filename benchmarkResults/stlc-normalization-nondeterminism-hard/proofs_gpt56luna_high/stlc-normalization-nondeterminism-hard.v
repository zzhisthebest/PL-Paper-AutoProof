(** STLC call-by-value strong-normalization benchmark.
    Non-deterministic choice is included; if-then-else and recursion are not. *)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Relations.Relation_Definitions.
From Stdlib Require Import Lia.

Module STLCNormalizationNondeterminismHardTask.

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
Notation "'choice' t1 'or' t2" := (tm_choice t1 t2)
  (in custom stlc_tm at level 200,
   t1 custom stlc_tm,
   t2 custom stlc_tm at level 200,
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
  | tm_choice t1 t2 =>
      tm_choice (open_rec k u t1) (open_rec k u t2)
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
  | lc_choice : forall k t1 t2,
      lc_at k t1 ->
      lc_at k t2 ->
      lc_at k (tm_choice t1 t2).

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
  | ST_ChoiceLeft : forall t1 t2,
      locally_closed t1 ->
      locally_closed t2 ->
      tm_choice t1 t2 --> t1
  | ST_ChoiceRight : forall t1 t2,
      locally_closed t1 ->
      locally_closed t2 ->
      tm_choice t1 t2 --> t2
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
  | T_Choice : forall Gamma t1 t2 T,
      <{ Gamma |-- $(t1) \in T }> ->
      <{ Gamma |-- $(t2) \in T }> ->
      <{ Gamma |-- choice $(t1) or $(t2) \in T }>
where "<{ Gamma '|--' t '\in' T }>" := (has_type Gamma t T)
  : stlc_scope.

(** Target theorem: strong normalization for the supplied CBV relation. *)

Inductive strongly_normalizing : tm -> Prop :=
  | SN_intro : forall t,
      (forall t', t --> t' -> strongly_normalizing t') ->
      strongly_normalizing t.

Fixpoint fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ => nil
  | tm_fvar x => x :: nil
  | tm_app t1 t2 => fv t1 ++ fv t2
  | tm_abs _ t1 => fv t1
  | tm_true => nil
  | tm_false => nil
  | tm_choice t1 t2 => fv t1 ++ fv t2
  end.

Fixpoint subst_tm (rho : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => rho x
  | tm_app t1 t2 => tm_app (subst_tm rho t1) (subst_tm rho t2)
  | tm_abs T t1 => tm_abs T (subst_tm rho t1)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_choice t1 t2 => tm_choice (subst_tm rho t1) (subst_tm rho t2)
  end.

Lemma fresh_gt : forall (l : list atom) x,
  In x l -> x < S (fold_right Nat.max 0 l).
Proof.
  induction l as [|a l IH]; intros x H; simpl in *.
  - contradiction.
  - destruct H as [->|H].
    + eapply Nat.lt_le_trans with (m := S x).
      * lia.
      * apply le_n_S. apply Nat.le_max_l.
    + eapply Nat.lt_le_trans with (m := S (fold_right Nat.max 0 l)).
      * apply IH. exact H.
      * apply le_n_S. apply Nat.le_max_r.
Qed.

Lemma fresh_not_in : forall l : list atom,
  exists x, ~ In x l.
Proof.
  intros l. exists (S (fold_right Nat.max 0 l)).
  intro H.
  pose proof (fresh_gt l _ H).
  lia.
Qed.

Lemma lc_weaken : forall k t, lc_at k t -> lc_at (S k) t.
Proof.
  intros k t H. revert k H.
  induction t as [i|x|t1 IH1 t2 IH2|T t IH| | |t1 IH1 t2 IH2];
    intros k H; inversion H; subst.
  - constructor. lia.
  - constructor.
  - constructor; [apply IH1; assumption | apply IH2; assumption].
  - constructor. apply IH. assumption.
  - constructor.
  - constructor.
  - constructor; [apply IH1; assumption | apply IH2; assumption].
Qed.

Lemma lc_open_rec : forall k t u,
  lc_at (S k) t -> lc_at k u -> lc_at k (open_rec k u t).
Proof.
  intros k t u Ht Hu. revert k u Ht Hu.
  induction t as [i|x|t1 IH1 t2 IH2|T t IH| | |t1 IH1 t2 IH2];
    intros k u Ht Hu; simpl.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst. exact Hu.
    + inversion Ht. constructor. apply Nat.eqb_neq in E. lia.
  - constructor.
  - inversion Ht. simpl. constructor.
    + apply IH1 with (u := u); assumption.
    + apply IH2 with (u := u); assumption.
  - inversion Ht. simpl. constructor.
    apply IH with (k := S k) (u := u); try assumption.
    apply lc_weaken. assumption.
  - constructor.
  - constructor.
  - inversion Ht. simpl. constructor.
    + apply IH1 with (u := u); assumption.
    + apply IH2 with (u := u); assumption.
Qed.

Lemma lc_open_fvar : forall k t x,
  lc_at k (open_rec k (tm_fvar x) t) -> lc_at (S k) t.
Proof.
  intros k t x H. revert k x H.
  induction t as [i|y|t1 IH1 t2 IH2|T t IH| | |t1 IH1 t2 IH2];
    intros k x H; simpl in H.
  - destruct (Nat.eqb k i) eqn:E.
    + constructor. apply Nat.eqb_eq in E. lia.
    + inversion H. constructor. apply Nat.eqb_neq in E. lia.
  - constructor.
  - inversion H. constructor.
    + apply IH1 with (k := k) (x := x); assumption.
    + apply IH2 with (k := k) (x := x); assumption.
  - inversion H. constructor.
    apply IH with (k := S k) (x := x); assumption.
  - constructor.
  - constructor.
  - inversion H. constructor.
    + apply IH1 with (k := k) (x := x); assumption.
    + apply IH2 with (k := k) (x := x); assumption.
Qed.

Lemma lc_at_any : forall k t, locally_closed t -> lc_at k t.
Proof.
  induction k as [|k IH]; intros t H; [exact H|].
  apply lc_weaken. apply IH. exact H.
Qed.

Lemma open_rec_lc : forall k u t,
  lc_at k t -> open_rec k u t = t.
Proof.
  intros k u t H. revert k u H.
  induction t as [i|x|t1 IH1 t2 IH2|T t IH| | |t1 IH1 t2 IH2];
    intros k u H; simpl.
  - inversion H. destruct (Nat.eqb k i) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
  - reflexivity.
  - inversion H. f_equal.
    + apply IH1. assumption.
    + apply IH2. assumption.
  - inversion H. f_equal. apply IH. assumption.
  - reflexivity.
  - reflexivity.
  - inversion H. f_equal.
    + apply IH1. assumption.
    + apply IH2. assumption.
Qed.

Lemma subst_open_rec : forall rho k t u,
  (forall x, locally_closed (rho x)) ->
  subst_tm rho (open_rec k u t) =
  open_rec k (subst_tm rho u) (subst_tm rho t).
Proof.
  intros rho k t u Hrho. revert rho k u Hrho.
  induction t as [i|x|t1 IH1 t2 IH2|T t IH| | |t1 IH1 t2 IH2];
    intros rho k u Hrho; simpl.
  - destruct (Nat.eqb k i); reflexivity.
  - rewrite (open_rec_lc k (subst_tm rho u) (rho x)). reflexivity.
    apply lc_at_any. apply Hrho.
  - rewrite (IH1 rho k u Hrho), (IH2 rho k u Hrho). reflexivity.
  - rewrite (IH rho (S k) u Hrho). reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite (IH1 rho k u Hrho), (IH2 rho k u Hrho). reflexivity.
Qed.

Lemma subst_fresh : forall rho x u t,
  ~ In x (fv t) ->
  subst_tm (fun y => if Nat.eqb x y then u else rho y) t = subst_tm rho t.
Proof.
  intros rho x u t. induction t as [i|y|t1 IH1 t2 IH2|T t IH| | |t1 IH1 t2 IH2];
    simpl; intro H.
  - reflexivity.
  - simpl in H. destruct (Nat.eqb x y) eqn:E.
    + exfalso. apply H. apply Nat.eqb_eq in E. subst. simpl. auto.
    + reflexivity.
  - assert (H1 : ~ In x (fv t1)) by
      (intro Hin; apply H; apply in_or_app; left; exact Hin).
    assert (H2 : ~ In x (fv t2)) by
      (intro Hin; apply H; apply in_or_app; right; exact Hin).
    simpl. rewrite (IH1 H1), (IH2 H2). reflexivity.
  - assert (H1 : ~ In x (fv t)) by (intro Hin; apply H; exact Hin).
    simpl. rewrite (IH H1). reflexivity.
  - reflexivity.
  - reflexivity.
  - assert (H1 : ~ In x (fv t1)) by
      (intro Hin; apply H; apply in_or_app; left; exact Hin).
    assert (H2 : ~ In x (fv t2)) by
      (intro Hin; apply H; apply in_or_app; right; exact Hin).
    simpl. rewrite (IH1 H1), (IH2 H2). reflexivity.
Qed.

Lemma typing_lc : forall Gamma t T,
  <{ Gamma |-- t \in T }> -> locally_closed t.
Proof.
  intros Gamma t T H.
  induction H as [Gamma x T Hx
                 | L Gamma T1 T2 t1 Hbody IH
                 | Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
                 | Gamma | Gamma
                 | Gamma t1 t2 T H1 IH1 H2 IH2].
  - constructor.
  - unfold locally_closed. constructor.
    destruct (fresh_not_in (L ++ fv t1)) as [x Hx].
    apply lc_open_fvar with (x := x).
    apply (IH x).
    intro Hin. apply Hx. apply in_or_app. left. exact Hin.
  - constructor; assumption.
  - constructor.
  - constructor.
  - constructor; assumption.
Qed.

Lemma value_lc : forall v, value v -> locally_closed v.
Proof.
  intros v H. inversion H; assumption || constructor.
Qed.

Lemma lc_app_left : forall k t1 t2, lc_at k (tm_app t1 t2) -> lc_at k t1.
Proof. intros k t1 t2 H; inversion H; assumption. Qed.

Lemma lc_app_right : forall k t1 t2, lc_at k (tm_app t1 t2) -> lc_at k t2.
Proof. intros k t1 t2 H; inversion H; assumption. Qed.

Lemma lc_abs_body : forall k T t, lc_at k (tm_abs T t) -> lc_at (S k) t.
Proof. intros k T t H; inversion H; assumption. Qed.

Lemma lc_choice_left : forall k t1 t2,
  lc_at k (tm_choice t1 t2) -> lc_at k t1.
Proof. intros k t1 t2 H; inversion H; assumption. Qed.

Lemma lc_choice_right : forall k t1 t2,
  lc_at k (tm_choice t1 t2) -> lc_at k t2.
Proof. intros k t1 t2 H; inversion H; assumption. Qed.

Lemma lc_step : forall t t', locally_closed t -> t --> t' ->
  locally_closed t'.
Proof.
  intros t t' Hlc Hs. unfold locally_closed in *.
  induction Hs as [T t v Hclosed Hv
                  | t1 t1' t2 Hstep IH Hlc2
                  | v1 t2 t2' Hv Hstep IH
                  | t1 t2 Hlc1 Hlc2
                  | t1 t2 Hlc1 Hlc2].
  - pose proof (lc_app_left 0 (tm_abs T t) v Hlc) as Habs2.
    apply lc_open_rec with (k := 0).
    + eapply lc_abs_body. exact Habs2.
    + apply value_lc. exact Hv.
  - constructor.
    + apply IH. apply lc_app_left with (t2 := t2). exact Hlc.
    + apply lc_app_right with (t1 := t1). exact Hlc.
  - constructor.
    + apply value_lc. exact Hv.
    + apply IH. apply lc_app_right with (t1 := v1). exact Hlc.
  - apply lc_choice_left with (k := 0) (t2 := t2). exact Hlc.
  - apply lc_choice_right with (k := 0) (t1 := t1). exact Hlc.
Qed.

Lemma sn_step : forall t t', strongly_normalizing t -> t --> t' ->
  strongly_normalizing t'.
Proof.
  intros t t' H Hs. inversion H. eauto.
Qed.

Fixpoint reducible (T : ty) (t : tm) : Prop :=
  match T with
  | Ty_Bool => locally_closed t /\ strongly_normalizing t
  | Ty_Arrow A B =>
      locally_closed t /\ strongly_normalizing t /\
      (forall u, reducible A u -> reducible B (tm_app t u))
  end.

Lemma reducible_lc : forall T t, reducible T t -> locally_closed t.
Proof.
  intros T t H. destruct T as [|A B].
  - simpl in H. exact (proj1 H).
  - simpl in H. exact (proj1 H).
Qed.

Lemma reducible_sn : forall T t, reducible T t -> strongly_normalizing t.
Proof.
  intros T t H. destruct T as [|A B].
  - simpl in H. exact (proj2 H).
  - simpl in H. exact (proj1 (proj2 H)).
Qed.


Theorem strong_normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  (* Construct a logical relation and prove the theorem. *)
Qed.

End STLCNormalizationNondeterminismHardTask.
