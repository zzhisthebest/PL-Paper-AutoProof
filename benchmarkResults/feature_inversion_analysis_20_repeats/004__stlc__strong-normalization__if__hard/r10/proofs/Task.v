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

(* =================== BEGIN SOLUTION DEVELOPMENT =================== *)

(* ---------- Substitution ---------- *)

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

Definition subst_update (sigma : atom -> tm) (x : atom) (u : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then u else sigma y.

Definition lc_env (sigma : atom -> tm) : Prop :=
  forall x, locally_closed (sigma x).

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

Lemma subst_id : forall t, subst (fun x => tm_fvar x) t = t.
Proof. induction t; simpl; try reflexivity; try (f_equal; auto). Qed.

Lemma lc_at_mono : forall k k' t, k <= k' -> lc_at k t -> lc_at k' t.
Proof.
  intros k k' t Hle H. revert k' Hle.
  induction H; intros k' Hle.
  - apply lc_bvar. lia.
  - apply lc_fvar.
  - apply lc_app; auto.
  - apply lc_abs. apply IHlc_at. lia.
  - apply lc_true.
  - apply lc_false.
  - apply lc_if; auto.
Qed.

Lemma lc_at_open_rec_lc : forall k w t, lc_at k t -> open_rec k w t = t.
Proof.
  intros k w t H. induction H; simpl.
  - destruct (Nat.eqb k i) eqn:E. apply Nat.eqb_eq in E. subst. lia. reflexivity.
  - reflexivity.
  - rewrite IHlc_at1, IHlc_at2. reflexivity.
  - rewrite IHlc_at. reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IHlc_at1, IHlc_at2, IHlc_at3. reflexivity.
Qed.

Lemma lc_env_update : forall sigma x u,
  lc_env sigma -> locally_closed u -> lc_env (subst_update sigma x u).
Proof.
  intros sigma x u Hsig Hu y. unfold subst_update.
  destruct (Nat.eqb x y); auto.
Qed.

Lemma lc_at_subst : forall sigma k t,
  lc_at k t -> lc_env sigma -> lc_at k (subst sigma t).
Proof.
  intros sigma k t Ht.
  induction Ht as [k i Hi | k x | k a b Ha IHa Hb IHb | k T a Ha IHa | k | k | k a b c Ha IHa Hb IHb Hc IHc];
    intros Hsig; simpl.
  - apply lc_bvar. exact Hi.
  - apply lc_at_mono with (k := 0); [lia | apply Hsig].
  - apply lc_app; auto.
  - apply lc_abs. apply IHa. exact Hsig.
  - apply lc_true.
  - apply lc_false.
  - apply lc_if; auto.
Qed.

Lemma subst_open_rec : forall sigma,
  lc_env sigma ->
  forall k v t,
  subst sigma (open_rec k v t) = open_rec k (subst sigma v) (subst sigma t).
Proof.
  intros sigma Hsig k v t. revert k.
  induction t; intros k; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. apply lc_at_open_rec_lc. apply lc_at_mono with (k := 0); [lia | apply Hsig].
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IHt1, IHt2, IHt3. reflexivity.
Qed.

Lemma subst_update_irrel : forall sigma x u t,
  ~ In x (fv t) ->
  subst (subst_update sigma x u) t = subst sigma t.
Proof.
  intros sigma x u t. induction t; simpl; intros H; auto.
  - (* fvar *) unfold subst_update. destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply H. simpl. left. reflexivity.
    + reflexivity.
  - (* app *)
    assert (H1 : ~ In x (fv t1)) by (intro Hc; apply H; apply in_app_iff; left; exact Hc).
    assert (H2 : ~ In x (fv t2)) by (intro Hc; apply H; apply in_app_iff; right; exact Hc).
    rewrite IHt1, IHt2; auto.
  - (* abs *) rewrite IHt. reflexivity. exact H.
  - (* if *)
    assert (H1 : ~ In x (fv t1)) by (intro Hc; apply H; apply in_app_iff; left; exact Hc).
    assert (H2 : ~ In x (fv t2)) by (intro Hc; apply H; apply in_app_iff; right; apply in_app_iff; left; exact Hc).
    assert (H3 : ~ In x (fv t3)) by (intro Hc; apply H; apply in_app_iff; right; apply in_app_iff; right; exact Hc).
    rewrite IHt1, IHt2, IHt3; auto.
Qed.

Lemma subst_open_fvar_eq : forall sigma x u t,
  lc_env sigma ->
  lc_env (subst_update sigma x u) ->
  ~ In x (fv t) ->
  subst (subst_update sigma x u) (open t (tm_fvar x)) = open (subst sigma t) u.
Proof.
  intros sigma x u t Hsig Hsig' Hfresh.
  unfold open.
  rewrite subst_open_rec; auto.
  rewrite (subst_update_irrel sigma x u t); auto.
  simpl. unfold subst_update. simpl. rewrite Nat.eqb_refl. reflexivity.
Qed.


(* ---------- Basic facts about step, values, SN, and local closure ---------- *)

Lemma step_abs_false : forall T body t', ~ (tm_abs T body --> t').
Proof. intros T body t' H; inversion H. Qed.

Lemma value_no_step : forall v, value v -> forall v', ~ (v --> v').
Proof.
  intros v Hv. induction Hv; intros v' Hstep.
  - apply (step_abs_false _ _ _ Hstep).
  - inversion Hstep.
  - inversion Hstep.
Qed.

Lemma SN_no_step : forall t, (forall t', ~ (t --> t')) -> strongly_normalizing t.
Proof. intros t H. apply SN_intro. intros t' Hs. exfalso. apply (H t'). exact Hs. Qed.

Lemma SN_abs : forall T body, strongly_normalizing (tm_abs T body).
Proof. intros. apply SN_no_step. intros. apply step_abs_false. Qed.

Lemma SN_true : strongly_normalizing tm_true.
Proof. apply SN_no_step. intros t' H. inversion H. Qed.

Lemma SN_false : strongly_normalizing tm_false.
Proof. apply SN_no_step. intros t' H. inversion H. Qed.

Lemma SN_step : forall t t', strongly_normalizing t -> t --> t' -> strongly_normalizing t'.
Proof. intros t t' H Hs. destruct H as [t0 Hred]. apply Hred. exact Hs. Qed.

Lemma lc_at_open_rec : forall k u t, lc_at (S k) t -> lc_at k u -> lc_at k (open_rec k u t).
Proof.
  intros k u t. revert k.
  induction t; intros k Ht Hu; simpl.
  - inversion Ht; subst.
    destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. exact Hu.
    + apply lc_bvar. apply Nat.eqb_neq in E. lia.
  - apply lc_fvar.
  - inversion Ht; subst. apply lc_app; [apply IHt1 | apply IHt2]; auto.
  - inversion Ht; subst. apply lc_abs. apply IHt with (k := S k).
    + assumption.
    + apply lc_at_mono with (k := k); [lia | exact Hu].
  - apply lc_true.
  - apply lc_false.
  - inversion Ht; subst. apply lc_if; [apply IHt1 | apply IHt2 | apply IHt3]; auto.
Qed.

Lemma lc_at_open_fvar : forall k t x, lc_at k (open_rec k (tm_fvar x) t) -> lc_at (S k) t.
Proof.
  intros k t. revert k.
  induction t; intros k x H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. apply lc_bvar. lia.
    + inversion H; subst. apply lc_bvar. lia.
  - apply lc_fvar.
  - inversion H; subst. apply lc_app; [apply (IHt1 k x) | apply (IHt2 k x)]; auto.
  - inversion H; subst. apply lc_abs. apply (IHt (S k) x); auto.
  - apply lc_true.
  - apply lc_false.
  - inversion H; subst. apply lc_if; [apply (IHt1 k x) | apply (IHt2 k x) | apply (IHt3 k x)]; auto.
Qed.

Lemma lc_at_app_inv : forall k a b, lc_at k (tm_app a b) -> lc_at k a /\ lc_at k b.
Proof. intros k a b H. inversion H; auto. Qed.

Lemma lc_at_abs_inv : forall k T a, lc_at k (tm_abs T a) -> lc_at (S k) a.
Proof. intros k T a H. inversion H; auto. Qed.

Lemma lc_at_if_inv : forall k a b c, lc_at k (tm_if a b c) -> lc_at k a /\ lc_at k b /\ lc_at k c.
Proof. intros k a b c H. inversion H; auto. Qed.

Lemma lc_step : forall t t', t --> t' -> locally_closed t -> locally_closed t'.
Proof.
  intros t t' H. induction H; intros Hlc.
  - destruct (lc_at_app_inv 0 _ _ Hlc) as [H1 H2].
    apply lc_at_open_rec with (k := 0).
    + apply lc_at_abs_inv in H1. exact H1.
    + exact H2.
  - destruct (lc_at_app_inv 0 _ _ Hlc) as [H1 H2].
    apply lc_app; [apply IHstep; exact H1 | exact H2].
  - destruct (lc_at_app_inv 0 _ _ Hlc) as [H1 H2].
    apply lc_app; [exact H1 | apply IHstep; exact H2].
  - destruct (lc_at_if_inv 0 _ _ _ Hlc) as [HA [HB HC]]. exact HB.
  - destruct (lc_at_if_inv 0 _ _ _ Hlc) as [HA [HB HC]]. exact HC.
  - destruct (lc_at_if_inv 0 _ _ _ Hlc) as [HA [HB HC]].
    apply lc_if; [apply IHstep; exact HA | exact HB | exact HC].
Qed.


(* ---------- Step analysis lemmas ---------- *)

Definition not_val_form (t : tm) : Prop :=
  match t with
  | tm_abs _ _ => False
  | tm_true => False
  | tm_false => False
  | _ => True
  end.

Lemma not_val_form_not_value : forall t, not_val_form t -> value t -> False.
Proof. intros t H Hv. destruct t; simpl in H; try contradiction; inversion Hv. Qed.

Lemma step_app_abs_cases : forall A body u Y,
  tm_app (tm_abs A body) u --> Y ->
  (value u /\ Y = open body u) \/
  (exists u', u --> u' /\ Y = tm_app (tm_abs A body) u').
Proof.
  intros A body u Y H. inversion H; subst.
  - left. auto.
  - exfalso. eapply step_abs_false; eauto.
  - right. eauto.
Qed.

Lemma step_app_nav_cases : forall X u Y,
  not_val_form X ->
  tm_app X u --> Y ->
  exists X', X --> X' /\ Y = tm_app X' u.
Proof.
  intros X u Y Hnv Hstep. inversion Hstep; subst.
  - simpl in Hnv. destruct Hnv.
  - exists t1'. auto.
  - exfalso. eapply not_val_form_not_value; eauto.
Qed.

Lemma step_if_cases : forall a b c Y,
  tm_if a b c --> Y ->
  (a = tm_true /\ Y = b) \/ (a = tm_false /\ Y = c) \/
  (exists a', a --> a' /\ Y = tm_if a' b c).
Proof.
  intros a b c Y H. inversion H; subst; eauto 6.
Qed.

(* ---------- The logical relation (reducibility) ---------- *)

Fixpoint R (T : ty) : tm -> Prop :=
  match T with
  | Ty_Bool => fun t => locally_closed t /\ strongly_normalizing t
  | Ty_Arrow T1 T2 => fun t =>
      locally_closed t /\ strongly_normalizing t /\
      (forall u, R T1 u -> R T2 (tm_app t u))
  end.

Lemma R_lc : forall T t, R T t -> locally_closed t.
Proof. intros T; destruct T; simpl; intros t [H _]; exact H. Qed.

Lemma R_sn : forall T t, R T t -> strongly_normalizing t.
Proof. intros T; destruct T; simpl; intros t H; tauto. Qed.

Lemma R_arrow : forall T1 T2 t,
  R (Ty_Arrow T1 T2) t ->
  forall u, R T1 u -> R T2 (tm_app t u).
Proof. intros T1 T2 t H. simpl in H. tauto. Qed.

(* Closure of R under one step *)
Lemma R_step : forall T t t', R T t -> t --> t' -> R T t'.
Proof.
  induction T as [| T1 IH1 T2 IH2]; simpl; intros t t' H Hstep.
  - destruct H as [Hlc Hsn]. split.
    + apply (lc_step t t' Hstep Hlc).
    + apply (SN_step t t' Hsn Hstep).
  - destruct H as [Hlc [Hsn Hf]]. split.
    + apply (lc_step t t' Hstep Hlc).
    + split.
      * apply (SN_step t t' Hsn Hstep).
      * intros u Hu. apply IH2 with (t := tm_app t u).
        -- apply Hf. exact Hu.
        -- apply ST_App1; [exact Hstep | apply R_lc with T1; exact Hu].
Qed.

(* Strong normalization of stuck applications *)
Lemma SN_app_nav : forall X u,
  not_val_form X ->
  (forall X', X --> X' -> strongly_normalizing (tm_app X' u)) ->
  strongly_normalizing (tm_app X u).
Proof.
  intros X u Hnv Hred. apply SN_intro. intros Y HY.
  destruct (step_app_nav_cases X u Y Hnv HY) as [X' [Hs Heq]]. subst.
  apply Hred. exact Hs.
Qed.

(* R is closed under applications whose head never becomes a value *)
Lemma R_app_nav : forall T X u,
  not_val_form X ->
  locally_closed X ->
  locally_closed u ->
  (forall X', X --> X' -> R T (tm_app X' u)) ->
  R T (tm_app X u).
Proof.
  induction T as [| T1 IH1 T2 IH2]; simpl; intros X u Hnv HlcX Hlcu Hred.
  - split.
    + apply lc_app; assumption.
    + apply SN_app_nav with (X := X); auto.
      intros X' Hs. apply R_sn with Ty_Bool. apply Hred. exact Hs.
  - split.
    + apply lc_app; assumption.
    + split.
      * apply SN_app_nav with (X := X); auto.
        intros X' Hs. apply R_sn with (Ty_Arrow T1 T2). apply Hred. exact Hs.
      * intros u' Hu'. apply IH2 with (X := tm_app X u) (u := u').
        -- simpl. exact I.
        -- apply lc_app; assumption.
        -- apply R_lc with T1; exact Hu'.
        -- intros Y' HY'.
           destruct (step_app_nav_cases X u Y' Hnv HY') as [X' [Hs Heq]]; subst.
           exact (R_arrow T1 T2 (tm_app X' u) (Hred X' Hs) u' Hu').
Qed.


(* Application of a well-closed abstraction to a reducible argument *)
Lemma R_app_abs : forall T A body,
  lc_at 1 body ->
  (forall v, value v -> R A v -> R T (open body v)) ->
  forall u, R A u -> R T (tm_app (tm_abs A body) u).
Proof.
  induction T as [| B1 IH1 B2 IH2]; intros A body Hlc Hsub u.
  - (* Bool *)
    intros Hu.
    assert (Hsn : strongly_normalizing u) by (apply R_sn with A; exact Hu).
    revert Hsub Hu.
    induction Hsn as [u0 Hu0 IHu0].
    intros Hsub Hu. split.
    + apply lc_app. apply lc_abs; exact Hlc. apply R_lc with A; exact Hu.
    + apply SN_intro. intros Y HY.
      destruct (step_app_abs_cases A body u0 Y HY) as [[Hv Heq] | [u' [Hs Heq]]]; subst.
      * apply R_sn with Ty_Bool. apply Hsub; assumption.
      * apply R_sn with Ty_Bool. apply (IHu0 u' Hs Hsub). exact (R_step A u0 u' Hu Hs).
  - (* Arrow B1 -> B2 *)
    intros Hu.
    assert (Hsn : strongly_normalizing u) by (apply R_sn with A; exact Hu).
    revert Hsub Hu.
    induction Hsn as [u0 Hu0 IHu0].
    intros Hsub Hu. split.
    + apply lc_app. apply lc_abs; exact Hlc. apply R_lc with A; exact Hu.
    + split.
      * apply SN_intro. intros Y HY.
        destruct (step_app_abs_cases A body u0 Y HY) as [[Hv Heq] | [u' [Hs Heq]]]; subst.
        -- apply R_sn with (Ty_Arrow B1 B2). apply Hsub; assumption.
        -- apply R_sn with (Ty_Arrow B1 B2). apply (IHu0 u' Hs Hsub). exact (R_step A u0 u' Hu Hs).
      * intros u' Hu'.
        apply R_app_nav with (X := tm_app (tm_abs A body) u0) (u := u').
        -- simpl. exact I.
        -- apply lc_app. apply lc_abs; exact Hlc. apply R_lc with A; exact Hu.
        -- apply R_lc with B1; exact Hu'.
        -- intros Y' HY'.
           destruct (step_app_abs_cases A body u0 Y' HY') as [[Hv Heq] | [u'' [Hs Heq]]]; subst.
           ++ exact (R_arrow B1 B2 (open body u0) (Hsub u0 Hv Hu) u' Hu').
           ++ exact (R_arrow B1 B2 (tm_app (tm_abs A body) u'') (IHu0 u'' Hs Hsub (R_step A u0 u'' Hu Hs)) u' Hu').
Qed.

(* Strong normalization of if-then-else *)
Lemma SN_if : forall a b c,
  strongly_normalizing a -> strongly_normalizing b -> strongly_normalizing c ->
  strongly_normalizing (tm_if a b c).
Proof.
  intros a b c Hsn1 Hsn2 Hsn3.
  induction Hsn1 as [a0 Ha0 IHa0].
  apply SN_intro. intros Y HY.
  destruct (step_if_cases a0 b c Y HY) as [[Heq1 Heq2] | [[Heq1 Heq2] | [a' [Hs Heq]]]]; subst.
  - exact Hsn2.
  - exact Hsn3.
  - apply IHa0; auto.
Qed.

Lemma R_if : forall T a b c,
  locally_closed a -> strongly_normalizing a -> R T b -> R T c -> R T (tm_if a b c).
Proof.
  induction T as [| B1 IH1 B2 IH2]; intros a b c Hlca Hsna Hb Hc.
  - split.
    + apply lc_if; [exact Hlca | apply R_lc with Ty_Bool; exact Hb | apply R_lc with Ty_Bool; exact Hc].
    + apply SN_if; [exact Hsna | apply R_sn with Ty_Bool; exact Hb | apply R_sn with Ty_Bool; exact Hc].
  - split.
    + apply lc_if; [exact Hlca | apply R_lc with (Ty_Arrow B1 B2); exact Hb | apply R_lc with (Ty_Arrow B1 B2); exact Hc].
    + split.
      * apply SN_if; [exact Hsna | apply R_sn with (Ty_Arrow B1 B2); exact Hb | apply R_sn with (Ty_Arrow B1 B2); exact Hc].
      * assert (Haux : forall a0, locally_closed a0 -> strongly_normalizing a0 ->
                 forall u, R B1 u -> R B2 (tm_app (tm_if a0 b c) u)).
        { intros a0 Hlca0 Hsna0. revert Hlca0.
          induction Hsna0 as [a1 Ha1 IHa1].
          intros Hlca1 u Hu.
          apply R_app_nav with (X := tm_if a1 b c) (u := u).
          - simpl. exact I.
          - apply lc_if; [exact Hlca1 | apply R_lc with (Ty_Arrow B1 B2); exact Hb | apply R_lc with (Ty_Arrow B1 B2); exact Hc].
          - apply R_lc with B1; exact Hu.
          - intros Y HY.
            destruct (step_if_cases a1 b c Y HY) as [[Heq1 Heq2] | [[Heq1 Heq2] | [a2 [Hs Heq]]]]; subst.
            + exact (R_arrow B1 B2 b Hb u Hu).
            + exact (R_arrow B1 B2 c Hc u Hu).
            + exact (IHa1 a2 Hs (lc_step a1 a2 Hs Hlca1) u Hu). }
        exact (Haux a Hlca Hsna).
Qed.


(* ---------- Regularity: well-typed terms are locally closed ---------- *)

Lemma in_le_sum : forall (L : list atom) (x : atom), In x L -> x <= fold_right Nat.add 0 L.
Proof.
  induction L as [| a L IH]; simpl; intros x Hx.
  - inversion Hx.
  - destruct Hx as [-> | Hx].
    + apply Nat.le_add_r.
    + apply Nat.le_trans with (fold_right Nat.add 0 L); [apply IH; exact Hx | apply Nat.le_add_l].
Qed.

Lemma fresh_not_in : forall L : list atom, exists x, ~ In x L.
Proof.
  intros L. exists (S (fold_right Nat.add 0 L)).
  intro Hc. apply in_le_sum in Hc. lia.
Qed.

Lemma has_type_lc : forall Gamma t T, has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T H.
  induction H as [Gamma x T Hvar
                | L Gamma T1 T2 t1 Hprem IHprem
                | Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
                | Gamma
                | Gamma
                | Gamma t1 t2 t3 T H1 IH1 H2 IH2 H3 IH3].
  - apply lc_fvar.
  - (* T_Abs *)
    destruct (fresh_not_in (L ++ fv t1)) as [x Hx].
    assert (HxL : ~ In x L) by (intro Hc; apply Hx; apply in_app_iff; left; exact Hc).
    apply lc_abs. apply lc_at_open_fvar with (x := x).
    apply IHprem. exact HxL.
  - apply lc_app; assumption.
  - apply lc_true.
  - apply lc_false.
  - apply lc_if; assumption.
Qed.


(* ---------- Context interpretation and the fundamental lemma ---------- *)

Definition env_match (Gamma : context) (sigma : atom -> tm) : Prop :=
  lc_env sigma /\ (forall x T, Gamma x = Some T -> R T (sigma x)).

Lemma env_match_update : forall Gamma sigma x u T,
  env_match Gamma sigma -> R T u ->
  env_match (update Gamma x T) (subst_update sigma x u).
Proof.
  intros Gamma sigma x u T [Hlc Henv] Hu. split.
  - apply lc_env_update; [exact Hlc | apply R_lc with T; exact Hu].
  - intros y T' Hy. unfold update in Hy. unfold subst_update.
    destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. subst. injection Hy as Hy. subst. exact Hu.
    + apply Henv. exact Hy.
Qed.

Lemma fundamental : forall Gamma t T,
  has_type Gamma t T ->
  forall sigma, env_match Gamma sigma -> R T (subst sigma t).
Proof.
  intros Gamma t T H.
  induction H as [Gamma x T Hvar
                | L Gamma T1 T2 t1 Hprem IHprem
                | Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
                | Gamma
                | Gamma
                | Gamma t1 t2 t3 T H1 IH1 H2 IH2 H3 IH3];
    intros sigma Henv; simpl.
  - (* T_Var *) apply (proj2 Henv). exact Hvar.
  - (* T_Abs *)
    pose proof (T_Abs L Gamma T1 T2 t1 Hprem) as Habs.
    assert (Hlct1 : lc_at 1 t1) by
      (exact (lc_at_abs_inv 0 T1 t1 (has_type_lc Gamma (tm_abs T1 t1) (Ty_Arrow T1 T2) Habs))).
    destruct (fresh_not_in (L ++ fv t1)) as [x Hx].
    assert (HxL : ~ In x L) by (intro Hc; apply Hx; apply in_app_iff; left; exact Hc).
    assert (Hxl : ~ In x (fv t1)) by (intro Hc; apply Hx; apply in_app_iff; right; exact Hc).
    assert (Hlcsub : lc_at 1 (subst sigma t1)) by (apply (lc_at_subst sigma 1 t1 Hlct1); apply (proj1 Henv)).
    assert (Hlcenv : lc_env sigma) by (apply (proj1 Henv)).
    split.
    + (* local closure *) apply lc_abs. exact Hlcsub.
    + split.
      * apply SN_abs.
      * intros u Hu.
        apply R_app_abs with (A := T1) (body := subst sigma t1).
        -- exact Hlcsub.
        -- intros v Hv HRv.
           rewrite <- (subst_open_fvar_eq sigma x v t1 Hlcenv
                         (lc_env_update sigma x v Hlcenv (R_lc T1 v HRv)) Hxl).
           apply (IHprem x HxL (subst_update sigma x v)).
           apply env_match_update; assumption.
        -- exact Hu.
  - (* T_App *)
    apply (R_arrow T1 T2 (subst sigma t1)).
    + apply IH1. exact Henv.
    + apply IH2. exact Henv.
  - (* T_True *) split.
    + apply lc_true.
    + apply SN_true.
  - (* T_False *) split.
    + apply lc_false.
    + apply SN_false.
  - (* T_If *)
    apply R_if.
    + apply R_lc with Ty_Bool. apply IH1. exact Henv.
    + apply R_sn with Ty_Bool. apply IH1. exact Henv.
    + apply IH2. exact Henv.
    + apply IH3. exact Henv.
Qed.


Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T H.
  assert (Hr : R T (subst (fun x => tm_fvar x) t)).
  { apply (fundamental empty t T H (fun x => tm_fvar x)).
    split.
    - intros x. apply lc_fvar.
    - intros x T' Hc. unfold empty in Hc. discriminate. }
  rewrite subst_id in Hr.
  apply R_sn with T. exact Hr.
Qed.

End STLCCBVNormalizationTask.
