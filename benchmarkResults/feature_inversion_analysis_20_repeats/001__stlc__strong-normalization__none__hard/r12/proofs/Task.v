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

(* ================================================================== *)
(* Strong normalization proof.                                         *)
(* ================================================================== *)

Import ListNotations.

Definition SN : tm -> Prop := strongly_normalizing.

(* ---------------- locally closed: inversion and monotonicity -------- *)

Lemma lc_bvar_inv : forall k n, lc_at k (tm_bvar n) -> n < k.
Proof. intros k n H; inversion H; assumption. Qed.

Lemma lc_app_inv : forall k t1 t2,
  lc_at k (tm_app t1 t2) -> lc_at k t1 /\ lc_at k t2.
Proof. intros k t1 t2 H; inversion H; subst; auto. Qed.

Lemma lc_abs_inv : forall k T t, lc_at k (tm_abs T t) -> lc_at (S k) t.
Proof. intros k T t H; inversion H; assumption. Qed.

Lemma lc_at_mono : forall t k k', lc_at k t -> k <= k' -> lc_at k' t.
Proof.
  intros t. induction t; intros k k' H Hle; inversion H; subst.
  - apply lc_bvar. lia.
  - apply lc_fvar.
  - apply lc_app.
    + apply IHt1 with (k := k); assumption.
    + apply IHt2 with (k := k); assumption.
  - apply lc_abs. apply IHt with (k := S k); [assumption | lia].
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma lc_open_rec : forall t k u,
  lc_at (S k) t -> lc_at k u -> lc_at k (open_rec k u t).
Proof.
  intros t. induction t; intros k u Ht Hu; simpl; inversion Ht; subst.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. assumption.
    + apply lc_bvar. apply Nat.eqb_neq in E. lia.
  - apply lc_fvar.
  - apply lc_app.
    + apply IHt1 with (k := k); assumption.
    + apply IHt2 with (k := k); assumption.
  - apply lc_abs. apply IHt with (k := S k).
    + assumption.
    + apply lc_at_mono with (k := k); [assumption | lia].
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma lc_open_rec_inv : forall t k u,
  lc_at k (open_rec k u t) -> lc_at (S k) t.
Proof.
  intros t. induction t; intros k u H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. apply lc_bvar. lia.
    + apply lc_bvar. apply lc_bvar_inv in H. apply Nat.eqb_neq in E. lia.
  - inversion H; subst. apply lc_fvar.
  - inversion H; subst. apply lc_app.
    + apply IHt1 with (u := u). assumption.
    + apply IHt2 with (u := u). assumption.
  - inversion H; subst. apply lc_abs. apply IHt with (k := S k) (u := u). assumption.
  - inversion H; subst. apply lc_true.
  - inversion H; subst. apply lc_false.
Qed.

(* open_rec on a locally closed term is the identity, at any depth *)
Lemma lc_open_rec_id : forall t k, lc_at k t -> forall u, open_rec k u t = t.
Proof.
  intros t. induction t; intros k Hk u; simpl.
  - assert (Hlt : n < k) by (apply lc_bvar_inv in Hk; assumption).
    destruct (Nat.eqb k n) eqn:E. apply Nat.eqb_eq in E. lia. reflexivity.
  - reflexivity.
  - apply lc_app_inv in Hk. destruct Hk as [H1 H2]. rewrite IHt1, IHt2; auto.
  - apply lc_abs_inv in Hk. rewrite IHt; auto.
  - reflexivity.
  - reflexivity.
Qed.

(* ---------------- step: determinism and lc preservation ------------- *)

Lemma value_no_step : forall v, value v -> forall t', ~ step v t'.
Proof.
  intros v Hv. induction Hv; intros t' Hst; inversion Hst.
Qed.

Ltac contra_value :=
  exfalso;
  match goal with
  | Hv : value ?v, Hs : step ?v ?x |- _ => exact (value_no_step v Hv x Hs)
  | Hlc : locally_closed (tm_abs ?T ?b), Hs : step (tm_abs ?T ?b) ?x |- _ =>
      exact (value_no_step (tm_abs T b) (v_abs T b Hlc) x Hs)
  end.

Lemma step_det : forall t t1, step t t1 -> forall s, step t s -> t1 = s.
Proof.
  intros t t1 H. induction H; intros s H2.
  - (* ST_AppAbs *)
    inversion H2; subst.
    + reflexivity.
    + contra_value.
    + contra_value.
  - (* ST_App1 *)
    inversion H2; subst.
    + contra_value.
    + assert (t1' = t1'0) by (eapply IHstep; eassumption). subst. reflexivity.
    + contra_value.
  - (* ST_App2 *)
    inversion H2; subst.
    + contra_value.
    + contra_value.
    + assert (t2' = t2'0) by (eapply IHstep; eassumption). subst. reflexivity.
Qed.

Lemma lc_step : forall t t', step t t' -> locally_closed t -> locally_closed t'.
Proof.
  intros t t' H. induction H; intros Hlc.
  - (* ST_AppAbs *)
    apply lc_app_inv in Hlc. destruct Hlc as [H1 H2].
    apply lc_abs_inv in H1.
    apply lc_open_rec; assumption.
  - (* ST_App1 *)
    apply lc_app_inv in Hlc. destruct Hlc as [H1 H2].
    apply lc_app; [apply IHstep; assumption | assumption].
  - (* ST_App2 *)
    apply lc_app_inv in Hlc. destruct Hlc as [H1 H2].
    apply lc_app; [assumption | apply IHstep; assumption].
Qed.

(* ---------------- strong normalization: basic lemmas --------------- *)

Lemma SN_step : forall t t', SN t -> step t t' -> SN t'.
Proof.
  intros t t' Hsn Hst. induction Hsn as [t Hred]. eapply Hred; eassumption.
Qed.

Lemma SN_value : forall v, value v -> SN v.
Proof.
  intros v Hv. induction Hv.
  - apply SN_intro. intros t' Hst. exfalso.
    eapply value_no_step; [apply v_abs; eassumption | eassumption].
  - apply SN_intro. intros t' Hst. inversion Hst.
  - apply SN_intro. intros t' Hst. inversion Hst.
Qed.

(* ================================================================== *)
(* The logical relation                                                *)
(* ================================================================== *)

Fixpoint LR (T : ty) (t : tm) : Prop :=
  match T with
  | Ty_Bool => locally_closed t /\ SN t
  | Ty_Arrow T1 T2 =>
      locally_closed t /\ SN t /\
      (forall u, LR T1 u -> LR T2 (tm_app t u))
  end.

Lemma LR_lc : forall T t, LR T t -> locally_closed t.
Proof. intros T; induction T; intros t H; simpl in H; tauto. Qed.

Lemma LR_SN : forall T t, LR T t -> SN t.
Proof. intros T; induction T; intros t H; simpl in H; tauto. Qed.

(* forward closure under one step *)
Lemma LR_step_forward : forall T t t', LR T t -> step t t' -> LR T t'.
Proof.
  intros T. induction T; intros t t' H Hst.
  - simpl in H. destruct H as [Hlc Hsn]. simpl. split.
    + eapply lc_step; eassumption.
    + eapply SN_step; eassumption.
  - simpl in H. destruct H as [Hlc [Hsn Harr]]. simpl. split; [|split].
    + eapply lc_step; eassumption.
    + eapply SN_step; eassumption.
    + intros u Hu. apply IHT2 with (t := tm_app t u).
      * apply Harr; assumption.
      * eapply ST_App1; [exact Hst | apply LR_lc with (T := T1); assumption].
Qed.

Lemma step_app_cases : forall (t1 t2 t' : tm),
  step (tm_app t1 t2) t' ->
  (exists T body v, t1 = tm_abs T body /\ locally_closed (tm_abs T body) /\ value v /\ t2 = v /\ t' = open body v)
  \/ (exists t1', step t1 t1' /\ locally_closed t2 /\ t' = tm_app t1' t2)
  \/ (exists v1 t2', t1 = v1 /\ value v1 /\ step t2 t2' /\ t' = tm_app v1 t2').
Proof.
  intros t1 t2 t' H. inversion H; subst; eauto 10.
Qed.

(* If every one-step reduct of a locally closed non-abstraction is in LR T,
   then the term itself is in LR T. *)
Lemma LR_of_red_nonabs : forall T t,
  locally_closed t ->
  (forall T' body, t = tm_abs T' body -> False) ->
  SN t ->
  (forall t', step t t' -> LR T t') ->
  LR T t.
Proof.
  intros T. induction T; intros t Hlc Hna Hsn Hred.
  - simpl. split; [assumption|].
    apply SN_intro. intros t' Hst. apply LR_SN with (T := Ty_Bool). apply Hred; assumption.
  - simpl. split; [assumption|split].
    + apply SN_intro. intros t' Hst. apply LR_SN with (T := Ty_Arrow T1 T2). apply Hred; assumption.
    + intros w Hw.
      assert (Hgen : forall w0, SN w0 -> LR T1 w0 -> LR T2 (tm_app t w0)).
      { intros w0 Hsnw. induction Hsnw as [w1 Hstepw IHw]. intros Hw1.
        assert (Hreds : forall t', step (tm_app t w1) t' -> LR T2 t').
        { intros t' Hst.
          destruct (step_app_cases t w1 t' Hst)
            as [[T' [body [vv [Heq [Hlcabs [Hval [Heq2 Heq3]]]]]]]
               | [[t1' [Hst1 [Hlc2 Heq1]]]
                  | [v1 [t2' [Heq [Hval [Hst2 Heq2]]]]]]].
          - exfalso. exact (Hna T' body Heq).
          - rewrite Heq1. apply Hred in Hst1.
            simpl in Hst1. destruct Hst1 as [_ [_ Harr]]. apply Harr; assumption.
          - subst v1. rewrite Heq2. apply IHw.
            + assumption.
            + apply LR_step_forward with (t := w1); assumption.
        }
        apply IHT2.
        - apply lc_app; [assumption | apply LR_lc with (T := T1); assumption].
        - intros T' body Heq. discriminate Heq.
        - apply SN_intro. intros t' Hst. apply LR_SN with (T := T2). apply Hreds; assumption.
        - exact Hreds.
      }
      apply Hgen.
      * apply LR_SN with (T := T1). assumption.
      * assumption.
Qed.

(* Applying an abstraction (whose body is semantically well typed) to a
   reducible argument yields a reducible term. *)
Lemma LR_abs_app : forall A B body u,
  locally_closed (tm_abs A body) ->
  (forall u, LR A u -> LR B (open body u)) ->
  LR A u ->
  LR B (tm_app (tm_abs A body) u).
Proof.
  intros A B body u Hlc Hbody.
  assert (Hgen : forall w, SN w -> LR A w -> LR B (tm_app (tm_abs A body) w)).
  { intros w0 Hsnw. induction Hsnw as [w Hstepw IHw]. intros Hw.
    assert (Hreds : forall t', step (tm_app (tm_abs A body) w) t' -> LR B t').
    { intros t' Hst.
      destruct (step_app_cases (tm_abs A body) w t' Hst)
        as [[T' [body' [vv [Heq [Hlcabs [Hval [Heq2 Heq3]]]]]]]
           | [[t1' [Hst1 [Hlc2 Heq1]]]
              | [v1 [t2' [Heq [Hval [Hst2 Heq2]]]]]]].
      - (* ST_AppAbs *)
        injection Heq as HA Hb. subst T'. subst body'. subst vv.
        rewrite Heq3. apply Hbody. assumption.
      - (* ST_App1: impossible, the abstraction is a value *)
        exfalso. exact (value_no_step (tm_abs A body) (v_abs A body Hlc) t1' Hst1).
      - (* ST_App2 *)
        subst v1. rewrite Heq2. apply IHw.
        + assumption.
        + apply LR_step_forward with (t := w); assumption.
    }
    apply LR_of_red_nonabs with (T := B).
    - apply lc_app; [assumption | apply LR_lc with (T := A); assumption].
    - intros T' b Heq. discriminate Heq.
    - apply SN_intro. intros t' Hst. apply LR_SN with (T := B). apply Hreds; assumption.
    - exact Hreds.
  }
  intros Hu. apply Hgen; [apply LR_SN with (T := A) | ]; assumption.
Qed.

(* Semantic application: LR at an arrow type applied to an LR argument. *)
Lemma LR_app_aux : forall A B (f : tm),
  SN f -> LR (Ty_Arrow A B) f ->
  forall a, SN a -> LR A a -> LR B (tm_app f a).
Proof.
  intros A B f Hsnf. induction Hsnf as [f0 Hstepf IHf].
  intros HRf a Hsna. induction Hsna as [a0 Hstepa IHa].
  intros HRa.
  assert (Hreds : forall t', step (tm_app f0 a0) t' -> LR B t').
  { intros t' Hst.
    destruct (step_app_cases f0 a0 t' Hst)
      as [[T' [body [vv [Heq [Hlcabs [Hval [Heq2 Heq3]]]]]]]
         | [[f' [Hstf [Hlca Heq1]]]
            | [v1 [a' [Heq [Hval [Hsta Heq2]]]]]]].
    - (* ST_AppAbs *)
      subst f0. subst a0. rewrite Heq3.
      eapply LR_step_forward with (t := tm_app (tm_abs T' body) vv).
      + simpl in HRf. destruct HRf as [_ [_ Harr]]. apply Harr; assumption.
      + eapply ST_AppAbs; eassumption.
    - (* ST_App1 *)
      rewrite Heq1. eapply IHf.
      + eassumption.
      + apply LR_step_forward with (t := f0); assumption.
      + apply SN_intro; assumption.
      + assumption.
    - (* ST_App2 *)
      subst v1. rewrite Heq2. eapply IHa.
      + eassumption.
      + apply LR_step_forward with (t := a0); assumption.
  }
  apply LR_of_red_nonabs with (T := B).
  - apply lc_app; [apply LR_lc with (T := Ty_Arrow A B); assumption
                  | apply LR_lc with (T := A); assumption].
  - intros T' body Heq. discriminate Heq.
  - apply SN_intro. intros t' Hst. apply LR_SN with (T := B). apply Hreds; assumption.
  - exact Hreds.
Qed.

Lemma LR_app : forall A B t1 t2,
  LR (Ty_Arrow A B) t1 -> LR A t2 -> LR B (tm_app t1 t2).
Proof.
  intros A B t1 t2 H1 H2.
  eapply LR_app_aux with (A := A) (B := B) (f := t1) (a := t2).
  - apply LR_SN with (T := Ty_Arrow A B); assumption.
  - assumption.
  - apply LR_SN with (T := A); assumption.
  - assumption.
Qed.

(* ================================================================== *)
(* Free variables, environments, substitution                          *)
(* ================================================================== *)

Fixpoint fv_list (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_app t1 t2 => fv_list t1 ++ fv_list t2
  | tm_abs _ body => fv_list body
  | tm_true => []
  | tm_false => []
  end.

Definition env := list (atom * tm).

Fixpoint env_lookup (x : atom) (rho : env) : option tm :=
  match rho with
  | [] => None
  | (y, s) :: rho' => if Nat.eqb x y then Some s else env_lookup x rho'
  end.

Fixpoint substenv (rho : env) (t : tm) : tm :=
  match t with
  | tm_bvar n => tm_bvar n
  | tm_fvar x => match env_lookup x rho with Some s => s | None => tm_fvar x end
  | tm_app t1 t2 => tm_app (substenv rho t1) (substenv rho t2)
  | tm_abs T body => tm_abs T (substenv rho body)
  | tm_true => tm_true
  | tm_false => tm_false
  end.

Definition env_atoms (rho : env) : list atom :=
  flat_map (fun p => fst p :: fv_list (snd p)) rho.

Definition fresh (L : list atom) : atom := S (fold_right Nat.max 0 L).

Lemma in_le_fold_max : forall L x, In x L -> x <= fold_right Nat.max 0 L.
Proof.
  intros L. induction L as [| a L IH]; intros x H.
  - contradiction.
  - simpl in H. destruct H as [Heq | H].
    + subst a. apply Nat.le_max_l.
    + apply Nat.le_trans with (m := fold_right Nat.max 0 L);
        [apply IH; assumption | apply Nat.le_max_r].
Qed.

Lemma fresh_gt : forall L x, In x L -> x < fresh L.
Proof.
  intros L x H. unfold fresh. pose proof (in_le_fold_max L x H). lia.
Qed.

Lemma fresh_notin : forall L, ~ In (fresh L) L.
Proof.
  intros L H. apply fresh_gt in H. lia.
Qed.

Lemma fresh_in1 : forall L1 L2 L3, ~ In (fresh (L1 ++ L2 ++ L3)) L1.
Proof.
  intros L1 L2 L3 H. apply fresh_notin with (L := L1 ++ L2 ++ L3).
  apply in_or_app. left. exact H.
Qed.

Lemma fresh_in2 : forall L1 L2 L3, ~ In (fresh (L1 ++ L2 ++ L3)) L2.
Proof.
  intros L1 L2 L3 H. apply fresh_notin with (L := L1 ++ L2 ++ L3).
  apply in_or_app. right. apply in_or_app. left. exact H.
Qed.

Lemma fresh_in3 : forall L1 L2 L3, ~ In (fresh (L1 ++ L2 ++ L3)) L3.
Proof.
  intros L1 L2 L3 H. apply fresh_notin with (L := L1 ++ L2 ++ L3).
  apply in_or_app. right. apply in_or_app. right. exact H.
Qed.

(* ---------------- substitution lemmas ------------------------------ *)

Lemma substenv_nil : forall t, substenv [] t = t.
Proof.
  intros t. induction t; simpl; auto.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
Qed.

Lemma lc_substenv : forall t k, lc_at k t -> forall rho,
  (forall y s, env_lookup y rho = Some s -> locally_closed s) ->
  lc_at k (substenv rho t).
Proof.
  intros t. induction t; intros k Hk rho Himg; simpl.
  - apply lc_bvar. apply lc_bvar_inv in Hk. assumption.
  - destruct (env_lookup a rho) eqn:E.
    + apply Himg in E. apply lc_at_mono with (k := 0); [assumption | lia].
    + apply lc_fvar.
  - apply lc_app_inv in Hk. destruct Hk as [Hk1 Hk2].
    apply lc_app.
    + apply IHt1 with (k := k); assumption.
    + apply IHt2 with (k := k); assumption.
  - apply lc_abs_inv in Hk.
    apply lc_abs. apply IHt with (k := S k); assumption.
  - apply lc_true.
  - apply lc_false.
Qed.

(* Substituting a fresh variable, then a term, equals opening with the term. *)
Lemma substenv_open_rec : forall t rho x u k,
  ~ In x (fv_list t) ->
  ~ In x (env_atoms rho) ->
  (forall y s, env_lookup y rho = Some s -> locally_closed s) ->
  substenv ((x, u) :: rho) (open_rec k (tm_fvar x) t)
  = open_rec k u (substenv rho t).
Proof.
  intros t. induction t as [n | a | t1 IHt1 t2 IHt2 | T b IHb | | ];
    intros rho x u k Hfv Henv Himg; simpl.
  - (* bvar *) destruct (Nat.eqb k n) eqn:E.
    + simpl. rewrite Nat.eqb_refl. reflexivity.
    + simpl. reflexivity.
  - (* fvar *)
    assert (Hne : a <> x) by (intro Heq; subst; apply Hfv; simpl; auto).
    destruct (Nat.eqb a x) eqn:Ex.
    + apply Nat.eqb_eq in Ex. contradiction.
    + destruct (env_lookup a rho) as [s | ] eqn:E2.
      * assert (Hlcs : lc_at k s).
        { apply lc_at_mono with (k := 0); [apply Himg in E2; assumption | lia]. }
        rewrite (lc_open_rec_id s k Hlcs). reflexivity.
      * reflexivity.
  - (* app *)
    assert (Hfv1 : ~ In x (fv_list t1)) by (intro H; apply Hfv; apply in_or_app; left; exact H).
    assert (Hfv2 : ~ In x (fv_list t2)) by (intro H; apply Hfv; apply in_or_app; right; exact H).
    simpl. rewrite (IHt1 rho x u k Hfv1 Henv Himg).
    rewrite (IHt2 rho x u k Hfv2 Henv Himg). reflexivity.
  - (* abs *)
    assert (Hfvb : ~ In x (fv_list b)) by (intro H; apply Hfv; simpl; exact H).
    simpl. rewrite (IHb rho x u (S k) Hfvb Henv Himg). reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(* ================================================================== *)
(* Semantic contexts                                                   *)
(* ================================================================== *)

Definition env_sem (Gamma : context) (rho : env) : Prop :=
  (forall x s, env_lookup x rho = Some s -> locally_closed s) /\
  (forall x T, Gamma x = Some T -> exists s, env_lookup x rho = Some s /\ LR T s).

Lemma env_sem_cons : forall Gamma rho x T u,
  env_sem Gamma rho -> LR T u -> env_sem (update Gamma x T) ((x, u) :: rho).
Proof.
  intros Gamma rho x T u [Hlc Hty] Hu. split.
  - intros y s Hs. simpl in Hs.
    destruct (Nat.eqb y x) eqn:E.
    + apply Nat.eqb_eq in E. subst. injection Hs as ->. apply LR_lc with (T := T). assumption.
    + apply Hlc with y. assumption.
  - intros y T' Hy. simpl.
    destruct (Nat.eqb y x) eqn:E.
    + apply Nat.eqb_eq in E; subst.
      unfold update in Hy. rewrite Nat.eqb_refl in Hy. injection Hy as ->.
      exists u. split; [reflexivity | assumption].
    + apply Nat.eqb_neq in E.
      assert (E' : Nat.eqb x y = false) by (apply Nat.eqb_neq; auto).
      unfold update in Hy. rewrite E' in Hy.
      destruct (Hty y T' Hy) as [s [Hs HLR]]. exists s. split; assumption.
Qed.

Lemma env_sem_empty : env_sem empty [].
Proof.
  split; intros; simpl in *.
  - discriminate H.
  - discriminate H.
Qed.

(* ================================================================== *)
(* Typing implies local closure                                        *)
(* ================================================================== *)

Lemma has_type_lc : forall Gamma t T, has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T H. induction H.
  - apply lc_fvar.
  - apply lc_abs. apply lc_open_rec_inv with (k := 0) (u := tm_fvar (fresh L)).
    apply H0. apply fresh_notin.
  - apply lc_app; assumption.
  - apply lc_true.
  - apply lc_false.
Qed.

(* ================================================================== *)
(* The fundamental theorem                                             *)
(* ================================================================== *)

Lemma fundamental : forall Gamma t T,
  <{ Gamma |-- t \in T }> ->
  forall rho, env_sem Gamma rho -> LR T (substenv rho t).
Proof.
  intros Gamma t T H.
  induction H as [Gamma x T Hvar
                | L Gamma T1 T2 t1 Hbody IHAbs
                | Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
                | Gamma | Gamma];
    intros rho Hrho.
  - (* T_Var *)
    simpl. destruct (Hrho) as [Hlc Hty].
    destruct (Hty x T Hvar) as [s [Hs HLR]].
    rewrite Hs. assumption.
  - (* T_Abs *)
    simpl.
    assert (Hlc1 : lc_at 1 t1).
    { apply lc_open_rec_inv with (k := 0) (u := tm_fvar (fresh L)).
      apply has_type_lc with (Gamma := update Gamma (fresh L) T1) (T := T2).
      apply Hbody. apply fresh_notin. }
    assert (Hlcbody : locally_closed (tm_abs T1 (substenv rho t1))).
    { apply lc_abs. apply lc_substenv with (k := 1); [exact Hlc1 | exact (proj1 Hrho)]. }
    split.
    + exact Hlcbody.
    + split.
      * apply SN_value. apply v_abs. exact Hlcbody.
      * intros u Hu.
        apply LR_abs_app with (A := T1) (B := T2) (body := substenv rho t1).
        -- exact Hlcbody.
        -- intros u0 Hu0.
           pose proof (IHAbs (fresh (L ++ fv_list t1 ++ env_atoms rho))
                        (fresh_in1 L (fv_list t1) (env_atoms rho))
                        ((fresh (L ++ fv_list t1 ++ env_atoms rho), u0) :: rho)
                        (env_sem_cons Gamma rho (fresh (L ++ fv_list t1 ++ env_atoms rho)) T1 u0 Hrho Hu0))
             as HLR.
           unfold open in HLR.
           rewrite (substenv_open_rec t1 rho (fresh (L ++ fv_list t1 ++ env_atoms rho)) u0 0
                      (fresh_in2 L (fv_list t1) (env_atoms rho))
                      (fresh_in3 L (fv_list t1) (env_atoms rho))
                      (proj1 Hrho)) in HLR.
           simpl in HLR. exact HLR.
        -- exact Hu.
  - (* T_App *)
    simpl. eapply LR_app.
    + apply IH1. assumption.
    + apply IH2. assumption.
  - (* T_True *) simpl. split; [apply lc_true | apply SN_value; apply v_true].
  - (* T_False *) simpl. split; [apply lc_false | apply SN_value; apply v_false].
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T H.
  pose proof (fundamental empty t T H []) as HLR.
  assert (Hsem : env_sem empty []) by apply env_sem_empty.
  specialize (HLR Hsem).
  rewrite substenv_nil in HLR.
  apply LR_SN with (T := T). exact HLR.
Qed.


End STLCNormalizationNoneHardTask.
