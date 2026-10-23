(** STLC call-by-value strong-normalization benchmark, Hard variant.
    System T-style natural-number recursion; no if-then-else or choice. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Relations.Relation_Definitions Lia.
Import ListNotations.

Module STLCNormalizationRecursionHardTask.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
      R x y ->
      multi R y z ->
      multi R x z.

Definition atom := nat.

Inductive ty : Type :=
  | Ty_Bool : ty
  | Ty_Nat : ty
  | Ty_Arrow : ty -> ty -> ty.

Inductive tm : Type :=
  | tm_bvar : nat -> tm
  | tm_fvar : atom -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : ty -> tm -> tm
  | tm_true : tm
  | tm_false : tm
  | tm_zero : tm
  | tm_succ : tm -> tm

  | tm_natrec : tm -> tm -> tm -> tm.

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
Notation "'zero'" := tm_zero
  (in custom stlc_tm at level 0) : stlc_scope.
Notation "'succ' t" := (tm_succ t)
  (in custom stlc_tm at level 9, t custom stlc_tm at level 0) : stlc_scope.
Notation "'rec' n b s" := (tm_natrec n b s)
  (in custom stlc_tm at level 9,
   n custom stlc_tm at level 0, b custom stlc_tm at level 0,
   s custom stlc_tm at level 0) : stlc_scope.
Notation "'Nat'" := Ty_Nat
  (in custom stlc_ty at level 0) : stlc_scope.

Fixpoint open_rec (k : nat) (u : tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => if Nat.eqb k i then u else tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_app t1 t2 => tm_app (open_rec k u t1) (open_rec k u t2)
  | tm_abs T t1 => tm_abs T (open_rec (S k) u t1)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (open_rec k u t1)
  | tm_natrec n b s =>
      tm_natrec (open_rec k u n) (open_rec k u b) (open_rec k u s)
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
  | lc_zero : forall k, lc_at k tm_zero
  | lc_succ : forall k t, lc_at k t -> lc_at k (tm_succ t)
  | lc_rec : forall k n b s,
      lc_at k n -> lc_at k b -> lc_at k s ->
      lc_at k (tm_natrec n b s).

Definition locally_closed (t : tm) : Prop := lc_at 0 t.

Hint Constructors lc_at : core.

Inductive numeric_value : tm -> Prop :=
  | nv_zero : numeric_value tm_zero
  | nv_succ : forall (t : tm), numeric_value t -> numeric_value (tm_succ t).


Inductive value : tm -> Prop :=
  | v_abs : forall T t,
      locally_closed (tm_abs T t) ->
      value (tm_abs T t)
  | v_true :
      value tm_true
  | v_false :
      value tm_false
  | v_nat : forall n, numeric_value n -> value n.

Hint Constructors value : core.

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
  | ST_Succ : forall t t',
      t --> t' -> tm_succ t --> tm_succ t'
  | ST_RecArg : forall n n' b s,

      n --> n' -> locally_closed b -> locally_closed s ->
      tm_natrec n b s --> tm_natrec n' b s
  | ST_RecBase : forall n b b' s,

      numeric_value n -> b --> b' -> locally_closed s ->
      tm_natrec n b s --> tm_natrec n b' s
  | ST_RecStep : forall n b s s',

      numeric_value n -> value b -> s --> s' ->
      tm_natrec n b s --> tm_natrec n b s'
  | ST_RecZero : forall b s,

      value b -> value s -> tm_natrec tm_zero b s --> b
  | ST_RecSucc : forall n b s,

      numeric_value n -> value b -> value s ->
      tm_natrec (tm_succ n) b s -->
        tm_app (tm_app s n) (tm_natrec n b s)
where "t '-->' t'" := (step t t').

Hint Constructors step : core.

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

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
  | T_Zero : forall Gamma,
      <{ Gamma |-- zero \in Nat }>
  | T_Succ : forall Gamma n,
      <{ Gamma |-- $(n) \in Nat }> ->
      <{ Gamma |-- succ $(n) \in Nat }>
  | T_Rec : forall Gamma n b s T,
      <{ Gamma |-- $(n) \in Nat }> ->
      <{ Gamma |-- $(b) \in T }> ->
      <{ Gamma |-- $(s) \in Nat -> T -> T }> ->
      <{ Gamma |-- rec $(n) $(b) $(s) \in T }>
where "<{ Gamma '|--' t '\in' T }>" := (has_type Gamma t T)
  : stlc_scope.

Hint Constructors has_type : core.

Inductive strongly_normalizing : tm -> Prop :=
  | SN_intro : forall t,
      (forall t', t --> t' -> strongly_normalizing t') ->
      strongly_normalizing t.

Fixpoint fsubst (rho : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => rho x
  | tm_app t1 t2 => tm_app (fsubst rho t1) (fsubst rho t2)
  | tm_abs A t1 => tm_abs A (fsubst rho t1)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_zero => tm_zero
  | tm_succ n => tm_succ (fsubst rho n)
  | tm_natrec n b s =>
      tm_natrec (fsubst rho n) (fsubst rho b) (fsubst rho s)
  end.

Fixpoint fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_app t1 t2 => fv t1 ++ fv t2
  | tm_abs _ t1 => fv t1
  | tm_true | tm_false | tm_zero => []
  | tm_succ n => fv n
  | tm_natrec n b s => fv n ++ fv b ++ fv s
  end.

Definition env_update (rho : atom -> tm) (x : atom) (u : tm) :=
  fun y => if Nat.eqb x y then u else rho y.

Definition fresh (L : list atom) : atom :=
  S (fold_right Nat.max 0 L).

Lemma in_fold_max : forall L x,
  In x L -> x <= fold_right Nat.max 0 L.
Proof.
  induction L as [|a L IH]; simpl; intros x H; [contradiction|].
  destruct H as [->|H].
  - apply Nat.le_max_l.
  - eapply Nat.le_trans; [apply IH, H|apply Nat.le_max_r].
Qed.

Lemma fresh_not_in : forall L, ~ In (fresh L) L.
Proof.
  intros L H.
  apply in_fold_max in H. unfold fresh in H. lia.
Qed.

Lemma open_rec_lc_above : forall d t,
  lc_at d t -> forall k u, d <= k -> open_rec k u t = t.
Proof.
  intros d t Hlc. induction Hlc; intros j u Hj; simpl; try reflexivity.
  - destruct (Nat.eqb j i) eqn:E; auto.
    apply Nat.eqb_eq in E. lia.
  - rewrite IHHlc1, IHHlc2; auto.
  - rewrite IHHlc; auto. lia.
  - rewrite IHHlc; auto.
  - rewrite IHHlc1, IHHlc2, IHHlc3; auto.
Qed.

Lemma open_rec_closed : forall t,
  locally_closed t -> forall k u, open_rec k u t = t.
Proof.
  intros t H k u. eapply open_rec_lc_above; eauto. lia.
Qed.

Lemma fsubst_open_rec : forall rho k u t,
  (forall x, locally_closed (rho x)) ->
  fsubst rho (open_rec k u t) =
  open_rec k (fsubst rho u) (fsubst rho t).
Proof.
  intros rho k u t Hrho; revert k.
  induction t; intros k; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. apply open_rec_closed, Hrho.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2, IHt3. reflexivity.
Qed.

Lemma fsubst_agree : forall t rho sigma,
  (forall x, In x (fv t) -> rho x = sigma x) ->
  fsubst rho t = fsubst sigma t.
Proof.
  induction t; simpl; intros rho sigma H; try reflexivity.
  - apply H. now left.
  - f_equal; [apply IHt1|apply IHt2]; intros; apply H;
      apply in_or_app; auto.
  - f_equal. apply IHt. exact H.
  - f_equal. apply IHt. exact H.
  - f_equal.
    + apply IHt1. intros. apply H. apply in_or_app. auto.
    + apply IHt2. intros. apply H. apply in_or_app. right.
      apply in_or_app. auto.
    + apply IHt3. intros. apply H. apply in_or_app. right.
      apply in_or_app. auto.
Qed.

Lemma fsubst_fvar : forall t,
  fsubst (fun x => tm_fvar x) t = t.
Proof.
  induction t; simpl; f_equal; auto.
Qed.

Lemma fsubst_open_fresh : forall rho x u t,
  (forall y, locally_closed (rho y)) ->
  locally_closed u ->
  ~ In x (fv t) ->
  fsubst (env_update rho x u) (open t (tm_fvar x)) =
  open (fsubst rho t) u.
Proof.
  intros rho x u t Hrho Hu Hfresh.
  unfold open. rewrite fsubst_open_rec.
  2:{ intros y. unfold env_update. destruct (Nat.eqb x y); auto. }
  simpl.
  unfold env_update. rewrite Nat.eqb_refl.
  f_equal. apply fsubst_agree. intros y Hy.
  unfold env_update. destruct (Nat.eqb x y) eqn:E; auto.
  apply Nat.eqb_eq in E. subst. contradiction.
Qed.

Lemma lc_weaken : forall k t,
  lc_at k t -> forall j, k <= j -> lc_at j t.
Proof.
  intros k t H. induction H; intros j Hj.
  - constructor. lia.
  - constructor.
  - constructor; eauto.
  - constructor. apply IHlc_at. lia.
  - constructor.
  - constructor.
  - constructor.
  - constructor. auto.
  - constructor; auto.
Qed.

Lemma lc_open_rec : forall t k u,
  lc_at (S k) t -> lc_at k u -> lc_at k (open_rec k u t).
Proof.
  induction t; simpl; intros k u Ht Hu; inversion Ht; subst.
  - destruct (Nat.eqb k n) eqn:E.
    + exact Hu.
    + constructor. apply Nat.eqb_neq in E. lia.
  - constructor.
  - constructor; eauto.
  - constructor. eapply IHt; eauto.
    eapply lc_weaken; eauto.
  - constructor.
  - constructor.
  - constructor.
  - constructor. eauto.
  - constructor; eauto.
Qed.

Lemma lc_open_inv : forall t k u,
  lc_at k (open_rec k u t) -> lc_at (S k) t.
Proof.
  induction t; simpl; intros k u H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. constructor. lia.
    + inversion H; subst. constructor. lia.
  - constructor.
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor. eauto.
  - constructor.
  - constructor.
  - constructor.
  - inversion H; subst. constructor. eauto.
  - inversion H; subst. constructor; eauto.
Qed.

Lemma numeric_lc0 : forall n, numeric_value n -> locally_closed n.
Proof.
  intros n H; induction H; [constructor|constructor; assumption].
Qed.

Lemma numeric_no_step0 : forall n,
  numeric_value n -> forall q, ~ (n --> q).
Proof.
  intros n H; induction H; intros q Hq.
  - inversion Hq.
  - inversion Hq; subst. eapply IHnumeric_value; eauto.
Qed.

Lemma value_lc : forall v, value v -> locally_closed v.
Proof.
  intros v H. inversion H; subst.
  - assumption.
  - constructor.
  - constructor.
  - eapply numeric_lc0; eauto.
Qed.

Lemma value_no_step : forall v, value v -> forall t, ~ (v --> t).
Proof.
  intros v Hv q Hs. inversion Hv; subst; try solve [inversion Hs].
  eapply numeric_no_step0; eauto.
Qed.

Lemma step_preserves_lc : forall t t',
  t --> t' -> locally_closed t -> locally_closed t'.
Proof.
  intros t t' Hs; induction Hs; intros Hlc.
  - inversion Hlc; subst.
    match goal with Habs : lc_at 0 (tm_abs _ _) |- _ =>
      inversion Habs; subst; eapply lc_open_rec; eauto using value_lc
    end.
  - inversion Hlc; subst. constructor.
    + apply IHHs. assumption.
    + assumption.
  - inversion Hlc; subst. constructor.
    + assumption.
    + apply IHHs. assumption.
  - inversion Hlc; subst. constructor. apply IHHs. assumption.
  - inversion Hlc; subst. constructor.
    + apply IHHs. assumption.
    + assumption.
    + assumption.
  - inversion Hlc; subst. constructor.
    + assumption.
    + apply IHHs. assumption.
    + assumption.
  - inversion Hlc; subst. constructor.
    + assumption.
    + assumption.
    + apply IHHs. assumption.
  - inversion Hlc; subst. assumption.
  - inversion Hlc; subst. inversion H6; subst.
    apply lc_app.
    + apply lc_app; assumption.
    + apply lc_rec; assumption.
Qed.

Lemma has_type_lc : forall Gamma t T,
  <{ Gamma |-- t \in T }> -> locally_closed t.
Proof.
  intros Gamma t T Hty. induction Hty.
  - constructor.
  - apply lc_abs.
    set (x := fresh L).
    apply (lc_open_inv t1 0 (tm_fvar x)).
    apply H0. unfold x. apply fresh_not_in.
  - apply lc_app; assumption.
  - constructor.
  - constructor.
  - constructor.
  - constructor. assumption.
  - apply lc_rec; assumption.
Qed.

Lemma lc_fsubst : forall t k rho,
  lc_at k t ->
  (forall x, locally_closed (rho x)) ->
  lc_at k (fsubst rho t).
Proof.
  induction t; simpl; intros k rho Hlc Hrho; inversion Hlc; subst.
  - constructor. assumption.
  - eapply lc_weaken; [apply Hrho|lia].
  - apply lc_app; eauto.
  - apply lc_abs. eauto.
  - constructor.
  - constructor.
  - constructor.
  - constructor. eauto.
  - apply lc_rec; eauto.
Qed.

Lemma sn_step : forall t t',
  strongly_normalizing t -> t --> t' -> strongly_normalizing t'.
Proof.
  intros t t' Hsn Hs. inversion Hsn. auto.
Qed.

Fixpoint reducible (T : ty) (t : tm) : Prop :=
  match T with
  | Ty_Bool => locally_closed t /\ strongly_normalizing t
  | Ty_Nat => locally_closed t /\ strongly_normalizing t
  | Ty_Arrow A B =>
      locally_closed t /\ strongly_normalizing t /\
      forall u, reducible A u -> reducible B (tm_app t u)
  end.

Lemma reducible_lc : forall T t, reducible T t -> locally_closed t.
Proof. destruct T; simpl; intros; tauto. Qed.

Lemma reducible_sn : forall T t, reducible T t -> strongly_normalizing t.
Proof. destruct T; simpl; intros; tauto. Qed.

Lemma reducible_step : forall T t t',
  reducible T t -> t --> t' -> reducible T t'.
Proof.
  induction T; simpl; intros t t' Hr Hs.
  - destruct Hr as [Hlc Hsn]. split.
    + eapply step_preserves_lc; eauto.
    + eapply sn_step; eauto.
  - destruct Hr as [Hlc Hsn]. split.
    + eapply step_preserves_lc; eauto.
    + eapply sn_step; eauto.
  - destruct Hr as [Hlc [Hsn Hmap]].
    split; [eapply step_preserves_lc; eauto|].
    split; [eapply sn_step; eauto|].
    intros u Hu. apply (IHT2 (tm_app t u)).
    + apply Hmap, Hu.
    + apply ST_App1.
      * exact Hs.
      * exact (reducible_lc _ _ Hu).
Qed.

Lemma app_step_nonvalue : forall f a q,
  ~ value f -> tm_app f a --> q ->
  exists f', f --> f' /\ q = tm_app f' a.
Proof.
  intros f a q Hnv Hs. inversion Hs; subst.
  - exfalso. apply Hnv. constructor. assumption.
  - eauto.
  - exfalso. auto.
Qed.

Lemma app_not_value : forall f a, ~ value (tm_app f a).
Proof.
  intros f a H; inversion H; subst.
  match goal with Hn : numeric_value (tm_app _ _) |- _ => inversion Hn end.
Qed.

Lemma natrec_not_value : forall n b s, ~ value (tm_natrec n b s).
Proof.
  intros n b s H; inversion H; subst.
  match goal with Hn : numeric_value (tm_natrec _ _ _) |- _ => inversion Hn end.
Qed.

Lemma reducible_neutral : forall T t,
  locally_closed t ->
  ~ value t ->
  (forall t', t --> t' -> reducible T t') ->
  reducible T t.
Proof.
  induction T; simpl; intros t Hlc Hnv Hred.
  - split; [exact Hlc|]. constructor. intros q Hq.
    exact (reducible_sn Ty_Bool q (Hred q Hq)).
  - split; [exact Hlc|]. constructor. intros q Hq.
    exact (reducible_sn Ty_Nat q (Hred q Hq)).
  - split; [exact Hlc|]. split.
    + constructor. intros q Hq.
      exact (reducible_sn (Ty_Arrow T1 T2) q (Hred q Hq)).
    + intros u Hu. apply IHT2.
      * apply lc_app; [exact Hlc|exact (reducible_lc _ _ Hu)].
      * apply app_not_value.
      * intros q Hq. destruct (app_step_nonvalue t u q Hnv Hq)
          as [t' [Hs ->]].
        specialize (Hred t' Hs). simpl in Hred.
        apply Hred, Hu.
Qed.

Lemma sn_abs : forall A t, strongly_normalizing (tm_abs A t).
Proof. intros. constructor. intros q H. inversion H. Qed.

Lemma reducible_abs_app : forall A B body,
  locally_closed (tm_abs A body) ->
  (forall u, reducible A u -> reducible B (open body u)) ->
  forall u, reducible A u -> reducible B (tm_app (tm_abs A body) u).
Proof.
  intros A B body Hlc Hbody u Hu.
  pose proof (reducible_sn A u Hu) as Hsn.
  revert Hu. induction Hsn as [u Hsteps IH]; intros Hu.
  apply reducible_neutral.
  - apply lc_app; [exact Hlc|exact (reducible_lc _ _ Hu)].
  - apply app_not_value.
  - intros q Hq. inversion Hq; subst.
    + apply Hbody, Hu.
    + match goal with Hs : tm_abs _ _ --> _ |- _ => inversion Hs end.
    + apply IH; [assumption|]. eapply reducible_step; eauto.
Qed.

Lemma reducible_abs : forall A B body,
  locally_closed (tm_abs A body) ->
  (forall u, reducible A u -> reducible B (open body u)) ->
  reducible (Ty_Arrow A B) (tm_abs A body).
Proof.
  intros A B body Hlc Hbody. simpl. split; [exact Hlc|]. split.
  - apply sn_abs.
  - intros u Hu. eapply reducible_abs_app; eauto.
Qed.

Lemma sn_succ : forall n,
  strongly_normalizing n -> strongly_normalizing (tm_succ n).
Proof.
  intros n Hsn. induction Hsn as [n Hsteps IH].
  constructor. intros q Hq. inversion Hq; subst. auto.
Qed.

Lemma reducible_succ : forall n,
  reducible Ty_Nat n -> reducible Ty_Nat (tm_succ n).
Proof.
  simpl. intros n [Hlc Hsn]. split.
  - apply lc_succ. exact Hlc.
  - apply sn_succ. exact Hsn.
Qed.

Lemma numeric_lc : forall n, numeric_value n -> locally_closed n.
Proof. exact numeric_lc0. Qed.

Lemma numeric_sn : forall n, numeric_value n -> strongly_normalizing n.
Proof.
  intros n H; induction H.
  - constructor. intros q Hq. inversion Hq.
  - apply sn_succ. assumption.
Qed.

Lemma numeric_reducible : forall n,
  numeric_value n -> reducible Ty_Nat n.
Proof. intros; simpl; auto using numeric_lc, numeric_sn. Qed.

Lemma numeric_no_step : forall n,
  numeric_value n -> forall q, ~ (n --> q).
Proof. exact numeric_no_step0. Qed.

Lemma numeric_value_dec : forall n, {numeric_value n} + {~ numeric_value n}.
Proof.
  induction n.
  - right; intro H; inversion H.
  - right; intro H; inversion H.
  - right; intro H; inversion H.
  - right; intro H; inversion H.
  - right; intro H; inversion H.
  - right; intro H; inversion H.
  - left; constructor.
  - destruct IHn as [H|H].
    + left. constructor. exact H.
    + right. intro K. inversion K. contradiction.
  - right; intro H; inversion H.
Qed.

Lemma reducible_natrec_numeric : forall T n,
  numeric_value n -> forall b,
  reducible T b -> forall s,
  reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  reducible T (tm_natrec n b s).
Proof.
  intros T n Hnv. induction Hnv as [|n Hnv IHn].
  - intros b Hb s Hs.
    pose proof (reducible_sn T b Hb) as Hbsn. revert Hb s Hs.
    induction Hbsn as [b Hbsteps IHb]; intros Hb s Hs.
    pose proof (reducible_sn _ s Hs) as Hssn. revert Hs.
    induction Hssn as [s Hssteps IHs]; intros Hs.
    apply reducible_neutral.
    + apply lc_rec.
      * apply numeric_lc. constructor.
      * exact (reducible_lc _ _ Hb).
      * exact (reducible_lc _ _ Hs).
    + apply natrec_not_value.
    + intros q Hq. inversion Hq; subst.
      * match goal with Hz : tm_zero --> _ |- _ => inversion Hz end.
      * eapply IHb; [eassumption| |exact Hs].
        eapply reducible_step; eauto.
      * eapply IHs; [eassumption|]. eapply reducible_step; eauto.
      * exact Hb.
  - intros b Hb s Hs.
    pose proof (reducible_sn T b Hb) as Hbsn. revert Hb s Hs.
    induction Hbsn as [b Hbsteps IHb]; intros Hb s Hs.
    pose proof (reducible_sn _ s Hs) as Hssn. revert Hs.
    induction Hssn as [s Hssteps IHs]; intros Hs.
    apply reducible_neutral.
    + apply lc_rec.
      * apply numeric_lc. constructor. exact Hnv.
      * exact (reducible_lc _ _ Hb).
      * exact (reducible_lc _ _ Hs).
    + apply natrec_not_value.
    + intros q Hq. inversion Hq; subst.
      * exfalso.
        match goal with Hz : tm_succ n --> _ |- _ =>
          inversion Hz; subst; eapply numeric_no_step; eauto
        end.
      * eapply IHb; [eassumption| |exact Hs].
        eapply reducible_step; eauto.
      * eapply IHs; [eassumption|]. eapply reducible_step; eauto.
      * pose proof (numeric_reducible n Hnv) as Hrn.
        pose proof Hs as Hs0.
        simpl in Hs. destruct Hs as [_ [_ Hmap1]].
        specialize (Hmap1 n Hrn). simpl in Hmap1.
        destruct Hmap1 as [_ [_ Hmap2]].
        apply Hmap2. apply IHn; assumption.
Qed.

Lemma reducible_natrec : forall T n,
  reducible Ty_Nat n -> forall b,
  reducible T b -> forall s,
  reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  reducible T (tm_natrec n b s).
Proof.
  intros T n Hn.
  pose proof (reducible_sn Ty_Nat n Hn) as Hsn.
  revert Hn. induction Hsn as [n Hsteps IH]; intros Hn b Hb s Hs.
  destruct (numeric_value_dec n) as [Hnv|Hnv].
  - eapply reducible_natrec_numeric; eauto.
  - apply reducible_neutral.
    + apply lc_rec.
      * exact (reducible_lc _ _ Hn).
      * exact (reducible_lc _ _ Hb).
      * exact (reducible_lc _ _ Hs).
    + apply natrec_not_value.
    + intros q Hq. inversion Hq; subst.
      * eapply IH; [eassumption| |exact Hb|exact Hs].
        eapply reducible_step; eauto.
      * exfalso. apply Hnv. assumption.
      * exfalso. apply Hnv. assumption.
      * exfalso. apply Hnv. constructor.
      * exfalso. apply Hnv. constructor. assumption.
Qed.

Definition good_env (Gamma : context) (rho : atom -> tm) : Prop :=
  (forall x, locally_closed (rho x)) /\
  forall x T, Gamma x = Some T -> reducible T (rho x).

Lemma good_env_update : forall Gamma rho x A u,
  good_env Gamma rho -> reducible A u ->
  good_env (update Gamma x A) (env_update rho x u).
Proof.
  intros Gamma rho x A u [Hlc Hrel] Hu. split.
  - intros y. unfold env_update. destruct (Nat.eqb x y).
    + exact (reducible_lc _ _ Hu).
    + apply Hlc.
  - intros y T. unfold update, env_update.
    destruct (Nat.eqb x y) eqn:E; intros H.
    + inversion H; subst. exact Hu.
    + apply Hrel. exact H.
Qed.

Theorem fundamental : forall Gamma t T,
  <{ Gamma |-- t \in T }> ->
  forall rho, good_env Gamma rho -> reducible T (fsubst rho t).
Proof.
  intros Gamma t T Hty. induction Hty; intros rho Henv; simpl.
  - destruct Henv as [_ Henv]. eauto.
  - apply reducible_abs.
    + pose proof (has_type_lc Gamma (tm_abs T1 t1) (Ty_Arrow T1 T2)) as Htypedlc.
      assert (Habs : has_type Gamma (tm_abs T1 t1) (Ty_Arrow T1 T2)).
      { apply T_Abs with L. exact H. }
      specialize (Htypedlc Habs).
      pose proof (lc_fsubst (tm_abs T1 t1) 0 rho Htypedlc
                    (proj1 Henv)) as Hclosed.
      exact Hclosed.
    + intros u Hu.
      set (x := fresh (L ++ fv t1)).
      assert (HxL : ~ In x L).
      { intro Hin. apply (fresh_not_in (L ++ fv t1)).
        apply in_or_app. auto. }
      assert (Hxfv : ~ In x (fv t1)).
      { intro Hin. apply (fresh_not_in (L ++ fv t1)).
        apply in_or_app. auto. }
      specialize (H0 x HxL (env_update rho x u)).
      specialize (H0 (good_env_update _ _ _ _ _ Henv Hu)).
      rewrite (fsubst_open_fresh rho x u t1 (proj1 Henv)
                 (reducible_lc _ _ Hu) Hxfv) in H0.
      exact H0.
  - pose proof (IHHty1 rho Henv) as Hfun. simpl in Hfun.
    destruct Hfun as [_ [_ Hmap]]. apply Hmap. apply IHHty2; exact Henv.
  - split; [constructor|]. constructor. intros q Hq. inversion Hq.
  - split; [constructor|]. constructor. intros q Hq. inversion Hq.
  - split; [constructor|]. constructor. intros q Hq. inversion Hq.
  - apply reducible_succ. apply IHHty. exact Henv.
  - eapply reducible_natrec.
    + apply IHHty1. exact Henv.
    + apply IHHty2. exact Henv.
    + apply IHHty3. exact Henv.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> -> strongly_normalizing t.
Proof.
  intros t T Hty.
  set (rho := fun x : atom => tm_fvar x).
  assert (Henv : good_env empty rho).
  { split.
    - intros; constructor.
    - intros x A H. discriminate.
  }
  pose proof (fundamental _ _ _ Hty rho Henv) as Hr.
  unfold rho in Hr. rewrite fsubst_fvar in Hr.
  exact (reducible_sn _ _ Hr).
Qed.

End STLCNormalizationRecursionHardTask.
