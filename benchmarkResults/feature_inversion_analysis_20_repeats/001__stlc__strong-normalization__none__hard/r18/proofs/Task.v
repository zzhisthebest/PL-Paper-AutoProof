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

(** ** Auxiliary lemmas about local closure *)

Lemma lc_at_mono : forall t k, lc_at k t -> forall k', k <= k' -> lc_at k' t.
Proof.
  intros t k H. induction H as [k i Hi | k x | k a b Ha IHa Hb IHb | k T t Ht IH | k | k];
    intros k' Hle.
  - apply lc_bvar. lia.
  - apply lc_fvar.
  - apply lc_app; auto.
  - apply lc_abs. apply IH. lia.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma lc_bvar_inv : forall k i, lc_at k (tm_bvar i) -> i < k.
Proof. intros k i H. inversion H. assumption. Qed.

Lemma lc_app_inv : forall k t1 t2, lc_at k (tm_app t1 t2) -> lc_at k t1 /\ lc_at k t2.
Proof. intros k t1 t2 H. inversion H. auto. Qed.

Lemma lc_abs_inv : forall k T t, lc_at k (tm_abs T t) -> lc_at (S k) t.
Proof. intros k T t H. inversion H. auto. Qed.

Lemma lc_open_rec : forall t k u,
  lc_at (S k) t -> lc_at k u -> lc_at k (open_rec k u t).
Proof.
  induction t as [i | x | t1 IH1 t2 IH2 | T t1 IH | |];
    intros k u Ht Hu; simpl.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst i. exact Hu.
    + apply lc_bvar. apply lc_bvar_inv in Ht.
      apply Nat.eqb_neq in E. lia.
  - apply lc_fvar.
  - destruct (lc_app_inv (S k) t1 t2 Ht) as [H1 H2].
    apply lc_app.
    + apply IH1 with (k := k) (u := u); assumption.
    + apply IH2 with (k := k) (u := u); assumption.
  - apply lc_abs.
    apply IH with (k := S k) (u := u).
    + apply lc_abs_inv in Ht. exact Ht.
    + apply lc_at_mono with (k := k); [exact Hu | lia].
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma lc_open_rec_id : forall t n k u,
  lc_at n t -> n <= k -> open_rec k u t = t.
Proof.
  induction t as [i | x | t1 IH1 t2 IH2 | T t1 IH | |];
    intros n k u Ht Hnk; simpl.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst i.
      exfalso. apply lc_bvar_inv in Ht. lia.
    + reflexivity.
  - reflexivity.
  - destruct (lc_app_inv n t1 t2 Ht) as [H1 H2]. f_equal.
    + apply IH1 with (n := n) (k := k) (u := u); assumption.
    + apply IH2 with (n := n) (k := k) (u := u); assumption.
  - f_equal. apply lc_abs_inv in Ht.
    apply IH with (n := S n) (k := S k) (u := u); [exact Ht | lia].
  - reflexivity.
  - reflexivity.
Qed.

Lemma lc_open_inv : forall t k u,
  locally_closed u -> lc_at k (open_rec k u t) -> lc_at (S k) t.
Proof.
  induction t as [i | x | t1 IH1 t2 IH2 | T t1 IH | |];
    intros k u Hu H; simpl in H.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst i. apply lc_bvar. lia.
    + apply lc_bvar. apply lc_bvar_inv in H. lia.
  - apply lc_fvar.
  - destruct (lc_app_inv k (open_rec k u t1) (open_rec k u t2) H) as [H1 H2].
    apply lc_app.
    + apply IH1 with (k := k) (u := u); assumption.
    + apply IH2 with (k := k) (u := u); assumption.
  - apply lc_abs. apply IH with (k := S k) (u := u).
    + apply lc_at_mono with (k := 0); [exact Hu | lia].
    + apply lc_abs_inv in H. exact H.
  - apply lc_true.
  - apply lc_false.
Qed.

(** ** Auxiliary lemmas about evaluation *)

Lemma value_no_step : forall t t', value t -> step t t' -> False.
Proof.
  intros t t' Hv Hst. revert Hv.
  induction Hst; intros Hv; inversion Hv.
Qed.

Lemma value_SN : forall t, value t -> strongly_normalizing t.
Proof.
  intros t Hv. apply SN_intro. intros t' Hst.
  exfalso. exact (value_no_step t t' Hv Hst).
Qed.

Lemma value_multi_self : forall t v, multi step t v -> value t -> v = t.
Proof.
  intros t v Hm. induction Hm as [x | x y z Hst Hm IH]; intros Hv.
  - reflexivity.
  - exfalso. exact (value_no_step x y Hv Hst).
Qed.

Lemma SN_step : forall t t', step t t' -> strongly_normalizing t -> strongly_normalizing t'.
Proof.
  intros t t' Hst Hsn. destruct Hsn as [t0 Hred].
  apply Hred. exact Hst.
Qed.

Lemma fvar_no_step : forall x t', ~ step (tm_fvar x) t'.
Proof. intros x t' H. inversion H. Qed.

Lemma multi_inv : forall t v,
  multi step t v -> t = v \/ exists y, step t y /\ multi step y v.
Proof.
  intros t v Hm. inversion Hm; subst.
  - left. reflexivity.
  - right. eexists. split; eauto.
Qed.

Lemma multi_fvar : forall x v, multi step (tm_fvar x) v -> v = tm_fvar x.
Proof.
  intros x v Hm. destruct (multi_inv _ _ Hm) as [Heq | [y [Hst _]]].
  - symmetry. exact Heq.
  - exfalso. exact (fvar_no_step x y Hst).
Qed.

Lemma step_lc : forall t t', step t t' -> locally_closed t -> locally_closed t'.
Proof.
  intros t t' Hst. induction Hst as [T body v Hlcabs Hvval | t1 t1' t2 Hst1 IH Hlc2 | v1 t2 t2' Hv1 Hst2 IH]; intros Hlc.
  - destruct (lc_app_inv 0 (tm_abs T body) v Hlc) as [Ha Hv].
    apply lc_abs_inv in Ha.
    apply lc_open_rec with (k := 0); assumption.
  - destruct (lc_app_inv 0 t1 t2 Hlc) as [H1 H2].
    apply lc_app; [apply IH; exact H1 | exact H2].
  - destruct (lc_app_inv 0 v1 t2 Hlc) as [H1 H2].
    apply lc_app; [exact H1 | apply IH; exact H2].
Qed.

(** ** Substitution of free variables *)

Fixpoint subst_tm (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_app t1 t2 => tm_app (subst_tm sigma t1) (subst_tm sigma t2)
  | tm_abs T t1 => tm_abs T (subst_tm sigma t1)
  | tm_true => tm_true
  | tm_false => tm_false
  end.

Definition extend (x : atom) (u : tm) (sigma : atom -> tm) : atom -> tm :=
  fun y => if Nat.eqb x y then u else sigma y.

Lemma extend_same : forall x u sigma, extend x u sigma x = u.
Proof. intros. unfold extend. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma extend_other : forall x y u sigma, x <> y -> extend x u sigma y = sigma y.
Proof.
  intros x y u sigma Hne. unfold extend.
  apply Nat.eqb_neq in Hne. rewrite Hne. reflexivity.
Qed.

Definition idenv : atom -> tm := fun x => tm_fvar x.

Lemma subst_tm_idenv : forall t, subst_tm idenv t = t.
Proof.
  induction t as [i | x | t1 IH1 t2 IH2 | T t1 IH | |]; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma subst_tm_lc_at : forall t sigma k,
  lc_at k t ->
  (forall x, locally_closed (sigma x)) ->
  lc_at k (subst_tm sigma t).
Proof.
  induction t as [i | x | t1 IH1 t2 IH2 | T t1 IH | |];
    intros sigma k Ht Hsigma; simpl.
  - apply lc_bvar. apply lc_bvar_inv in Ht. exact Ht.
  - apply lc_at_mono with (k := 0); [apply Hsigma | lia].
  - destruct (lc_app_inv k t1 t2 Ht) as [H1 H2].
    apply lc_app.
    + apply IH1 with (sigma := sigma) (k := k); assumption.
    + apply IH2 with (sigma := sigma) (k := k); assumption.
  - apply lc_abs. apply lc_abs_inv in Ht.
    apply IH with (sigma := sigma) (k := S k); assumption.
  - apply lc_true.
  - apply lc_false.
Qed.

Fixpoint fvs (t : tm) : list atom :=
  match t with
  | tm_bvar _ => nil
  | tm_fvar x => x :: nil
  | tm_app t1 t2 => fvs t1 ++ fvs t2
  | tm_abs _ t1 => fvs t1
  | tm_true => nil
  | tm_false => nil
  end.

Lemma list_bounded : forall l : list atom, exists n, forall a, In a l -> a < n.
Proof.
  induction l as [| a l [n Hn]].
  - exists 0. intros a Ha. inversion Ha.
  - exists (S (a + n)). intros b Hb. destruct Hb as [-> | Hb].
    + lia.
    + apply Hn in Hb. lia.
Qed.

Lemma fresh_exists : forall l : list atom, exists x, ~ In x l.
Proof.
  intros l. destruct (list_bounded l) as [n Hn].
  exists n. intro H. specialize (Hn n H). lia.
Qed.

Lemma subst_tm_open_fvar : forall t sigma x u k,
  (forall y, locally_closed (sigma y)) ->
  ~ In x (fvs t) ->
  subst_tm (extend x u sigma) (open_rec k (tm_fvar x) t)
  = open_rec k u (subst_tm sigma t).
Proof.
  induction t as [i | y | t1 IH1 t2 IH2 | T t1 IH | |];
    intros sigma x u k Hsigma Hfresh; simpl.
  - destruct (Nat.eqb k i) eqn:E; simpl.
    + rewrite extend_same. reflexivity.
    + reflexivity.
  - unfold extend. destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. subst y. exfalso. apply Hfresh. simpl. auto.
    + apply Nat.eqb_neq in E. symmetry. apply lc_open_rec_id with (n := 0) (u := u) (k := k).
      * apply Hsigma.
      * lia.
  - assert (Hf1 : ~ In x (fvs t1)).
    { intro H. apply Hfresh. apply in_app_iff. left. exact H. }
    assert (Hf2 : ~ In x (fvs t2)).
    { intro H. apply Hfresh. apply in_app_iff. right. exact H. }
    assert (E1 : subst_tm (extend x u sigma) (open_rec k (tm_fvar x) t1)
                 = open_rec k u (subst_tm sigma t1)).
    { apply IH1; assumption. }
    assert (E2 : subst_tm (extend x u sigma) (open_rec k (tm_fvar x) t2)
                 = open_rec k u (subst_tm sigma t2)).
    { apply IH2; assumption. }
    rewrite E1, E2. reflexivity.
  - apply f_equal. apply IH with (k := S k); assumption.
  - reflexivity.
  - reflexivity.
Qed.

(** ** The logical relation *)

Fixpoint R (T : ty) (t : tm) {struct T} : Prop :=
  locally_closed t /\ strongly_normalizing t /\
  match T with
  | Ty_Bool =>
      forall v, multi step t v -> value v -> (v = tm_true \/ v = tm_false)
  | Ty_Arrow A B =>
      forall v, multi step t v -> value v ->
        exists body, v = tm_abs A body /\ lc_at 1 body /\
          (forall u, R A u -> R B (open body u))
  end.

Definition V (T : ty) (v : tm) : Prop :=
  match T with
  | Ty_Bool => v = tm_true \/ v = tm_false
  | Ty_Arrow A B =>
      exists body, v = tm_abs A body /\ lc_at 1 body /\
        (forall u, R A u -> R B (open body u))
  end.

Lemma R_lc : forall T t, R T t -> locally_closed t.
Proof. intros T t H. destruct T; simpl in H; exact (proj1 H). Qed.

Lemma R_sn : forall T t, R T t -> strongly_normalizing t.
Proof. intros T t H. destruct T; simpl in H; exact (proj1 (proj2 H)). Qed.

Lemma R_V : forall T t v, R T t -> multi step t v -> value v -> V T v.
Proof.
  intros T t v H Hm Hv. destruct T as [| A B]; simpl in *.
  - exact (proj2 (proj2 H) v Hm Hv).
  - exact (proj2 (proj2 H) v Hm Hv).
Qed.

Lemma R_true : R Ty_Bool tm_true.
Proof.
  split; [apply lc_true | split; [apply value_SN, v_true |]].
  intros v Hm Hv. rewrite (value_multi_self tm_true v Hm v_true). left. reflexivity.
Qed.

Lemma R_false : R Ty_Bool tm_false.
Proof.
  split; [apply lc_false | split; [apply value_SN, v_false |]].
  intros v Hm Hv. rewrite (value_multi_self tm_false v Hm v_false). right. reflexivity.
Qed.

Lemma R_fvar : forall T x, R T (tm_fvar x).
Proof.
  intros T x. destruct T as [| A B]; simpl.
  - split; [apply lc_fvar | split].
    + apply SN_intro. intros t' Hst. exfalso. exact (fvar_no_step x t' Hst).
    + intros v Hm Hv. rewrite (multi_fvar x v Hm) in Hv. inversion Hv.
  - split; [apply lc_fvar | split].
    + apply SN_intro. intros t' Hst. exfalso. exact (fvar_no_step x t' Hst).
    + intros v Hm Hv. rewrite (multi_fvar x v Hm) in Hv. inversion Hv.
Qed.

Lemma R_step : forall T t t', R T t -> step t t' -> R T t'.
Proof.
  intros T t t' HR Hst. destruct T as [| A B]; simpl in *.
  - destruct HR as [Hlc [Hsn Hval]]. split; [apply step_lc with (t := t); assumption | split].
    + apply SN_step with (t := t); assumption.
    + intros v Hm Hv. apply (Hval v).
      * apply multi_step with (y := t'); assumption.
      * assumption.
  - destruct HR as [Hlc [Hsn Hval]]. split; [apply step_lc with (t := t); assumption | split].
    + apply SN_step with (t := t); assumption.
    + intros v Hm Hv. apply (Hval v).
      * apply multi_step with (y := t'); assumption.
      * assumption.
Qed.

Lemma SN_app_abs : forall (A : ty) (body u : tm),
  lc_at 1 body ->
  (forall w, R A w -> strongly_normalizing (open body w)) ->
  R A u ->
  strongly_normalizing (tm_app (tm_abs A body) u).
Proof.
  intros A body u Hlcbody HbodySN Hu.
  assert (Hsn : strongly_normalizing u) by apply (R_sn A u Hu).
  revert A body Hlcbody HbodySN Hu.
  induction Hsn as [u Hrec IH].
  intros A body Hlcbody HbodySN Hu.
  assert (Habsval : value (tm_abs A body)) by (apply v_abs, lc_abs; exact Hlcbody).
  apply SN_intro. intros s' Hst.
  inversion Hst as [T t0 v Hlc0 Hv0 | t1 t1' t2 Hst1 Hlct2 | v1 t2 t2' Hv1 Hst2]; subst.
  - apply HbodySN. exact Hu.
  - exfalso. eapply value_no_step; eauto.
  - apply (IH t2' Hst2 A body Hlcbody HbodySN). apply (R_step A u t2' Hu Hst2).
Qed.

Lemma R_app_abs_val : forall (A B : ty) (body u : tm),
  lc_at 1 body ->
  (forall w, R A w -> R B (open body w)) ->
  R A u ->
  (forall u', step u u' -> forall A0 B0 body0,
      lc_at 1 body0 ->
      (forall w, R A0 w -> R B0 (open body0 w)) ->
      R A0 u' -> R B0 (tm_app (tm_abs A0 body0) u')) ->
  forall v, multi step (tm_app (tm_abs A body) u) v -> value v -> V B v.
Proof.
  intros A B body u Hlcbody Hbody Hu IH v Hm Hvval.
  assert (Habsval : value (tm_abs A body)) by (apply v_abs, lc_abs; exact Hlcbody).
  destruct (multi_inv _ _ Hm) as [Heq | [y [Hst Hm']]].
  - subst v. inversion Hvval.
  - inversion Hst as [T t0 v0 Hlc0 Hv0 | t1 t1' t2 Hst1 Hlct2 | v1 t2 t2' Hv1 Hst2]; subst.
    + apply (R_V B (open body u) v).
      * apply Hbody. exact Hu.
      * exact Hm'.
      * exact Hvval.
    + exfalso. exact (value_no_step _ _ Habsval Hst1).
    + apply (R_V B (tm_app (tm_abs A body) t2') v).
      * apply (IH t2' Hst2 A B body Hlcbody Hbody). apply (R_step A u t2' Hu Hst2).
      * exact Hm'.
      * exact Hvval.
Qed.

Lemma R_app_abs : forall (A B : ty) (body u : tm),
  lc_at 1 body ->
  (forall w, R A w -> R B (open body w)) ->
  R A u ->
  R B (tm_app (tm_abs A body) u).
Proof.
  intros A B body u Hlcbody Hbody Hu.
  assert (Hsn : strongly_normalizing u) by apply (R_sn A u Hu).
  revert A B body Hlcbody Hbody Hu.
  induction Hsn as [u Hrec IH].
  intros A B body Hlcbody Hbody Hu.
  assert (Hlcapp : locally_closed (tm_app (tm_abs A body) u)).
  { apply lc_app; [apply lc_abs; exact Hlcbody | apply (R_lc A u Hu)]. }
  destruct B as [| B1 B2]; simpl;
    (split; [exact Hlcapp | split]).
  - apply (SN_app_abs A body u Hlcbody).
    intros w Hw. apply (R_sn Ty_Bool (open body w)). apply Hbody. exact Hw.
    exact Hu.
  - apply (R_app_abs_val A Ty_Bool body u Hlcbody Hbody Hu IH).
  - apply (SN_app_abs A body u Hlcbody).
    intros w Hw. apply (R_sn (Ty_Arrow B1 B2) (open body w)). apply Hbody. exact Hw.
    exact Hu.
  - apply (R_app_abs_val A (Ty_Arrow B1 B2) body u Hlcbody Hbody Hu IH).
Qed.

Lemma SN_app_of_R_arrow : forall (A B : ty) (t u : tm),
  R (Ty_Arrow A B) t -> R A u -> strongly_normalizing (tm_app t u).
Proof.
  intros A B t u HRt Hu.
  assert (Hsnt : strongly_normalizing t) by apply (R_sn (Ty_Arrow A B) t HRt).
  revert A B u HRt Hu.
  induction Hsnt as [t Hrec IH].
  intros A B u HRt Hu.
  apply SN_intro. intros s' Hst.
  inversion Hst as [T t0 v Hlc0 Hv0 | t1 t1' t2 Hst1 Hlct2 | v1 t2 t2' Hv1 Hst2]; subst.
  - assert (Habsval : value (tm_abs T t0)) by (apply v_abs; exact Hlc0).
    assert (HV : V (Ty_Arrow A B) (tm_abs T t0)).
    { apply (R_V (Ty_Arrow A B) (tm_abs T t0) (tm_abs T t0) HRt (multi_refl step (tm_abs T t0)) Habsval). }
    simpl in HV. destruct HV as [body [Heq [Hlcb Hbody]]].
    inversion Heq; subst.
    apply (R_sn B (open body u)). apply Hbody. exact Hu.
  - apply (IH t1' Hst1 A B u). apply (R_step (Ty_Arrow A B) t t1' HRt Hst1). exact Hu.
  - assert (HV : V (Ty_Arrow A B) t).
    { apply (R_V (Ty_Arrow A B) t t HRt (multi_refl step t) Hv1). }
    simpl in HV. destruct HV as [body [Heq [Hlcb Hbody]]].
    inversion Heq; subst.
    apply (SN_app_abs A body t2' Hlcb).
    * intros w Hw. apply (R_sn B (open body w)). apply Hbody. exact Hw.
    * apply (R_step A u t2' Hu Hst2).
Qed.

Lemma V_reducts_app_aux : forall (A B : ty) (t u : tm),
  R (Ty_Arrow A B) t -> R A u ->
  (forall t', step t t' -> forall A0 B0 u0,
      R (Ty_Arrow A0 B0) t' -> R A0 u0 -> R B0 (tm_app t' u0)) ->
  forall v, multi step (tm_app t u) v -> value v -> V B v.
Proof.
  intros A B t u HRt Hu IHapp v Hm Hvval.
  destruct (multi_inv _ _ Hm) as [Heq | [y [Hst Hm']]].
  - subst v. inversion Hvval.
  - inversion Hst as [T t0 v0 Hlc0 Hv0 | t1 t1' t2 Hst1 Hlct2 | v1 t2 t2' Hv1 Hst2]; subst.
    + assert (Habsval : value (tm_abs T t0)) by (apply v_abs; exact Hlc0).
      assert (HV : V (Ty_Arrow A B) (tm_abs T t0)).
      { apply (R_V (Ty_Arrow A B) (tm_abs T t0) (tm_abs T t0) HRt (multi_refl step (tm_abs T t0)) Habsval). }
      simpl in HV. destruct HV as [body [Heq' [Hlcb Hbody]]].
      inversion Heq'; subst.
      apply (R_V B (open body u) v).
      * apply Hbody. exact Hu.
      * exact Hm'.
      * exact Hvval.
    + apply (R_V B (tm_app t1' u) v).
      * apply (IHapp t1' Hst1 A B u). apply (R_step (Ty_Arrow A B) t t1' HRt Hst1). exact Hu.
      * exact Hm'.
      * exact Hvval.
    + assert (HV : V (Ty_Arrow A B) t).
      { apply (R_V (Ty_Arrow A B) t t HRt (multi_refl step t) Hv1). }
      simpl in HV. destruct HV as [body [Heq' [Hlcb Hbody]]].
      inversion Heq'; subst.
      apply (R_V B (tm_app (tm_abs A body) t2') v).
      * apply (R_app_abs A B body t2' Hlcb Hbody). apply (R_step A u t2' Hu Hst2).
      * exact Hm'.
      * exact Hvval.
Qed.

Lemma R_app : forall (A B : ty) (t u : tm),
  R (Ty_Arrow A B) t -> R A u -> R B (tm_app t u).
Proof.
  intros A B t u HRt Hu.
  assert (Hsnt : strongly_normalizing t) by apply (R_sn (Ty_Arrow A B) t HRt).
  revert A B u HRt Hu.
  induction Hsnt as [t Hrec IH].
  intros A B u HRt Hu.
  assert (Hlct : locally_closed t) by apply (R_lc (Ty_Arrow A B) t HRt).
  assert (Hlcapp : locally_closed (tm_app t u)).
  { apply lc_app; [exact Hlct | apply (R_lc A u Hu)]. }
  destruct B as [| B1 B2]; simpl.
  - split; [exact Hlcapp | split].
    + apply (SN_app_of_R_arrow A Ty_Bool t u); assumption.
    + apply (V_reducts_app_aux A Ty_Bool t u HRt Hu IH).
  - split; [exact Hlcapp | split].
    + apply (SN_app_of_R_arrow A (Ty_Arrow B1 B2) t u); assumption.
    + apply (V_reducts_app_aux A (Ty_Arrow B1 B2) t u HRt Hu IH).
Qed.

Definition env_good (Gamma : context) (sigma : atom -> tm) : Prop :=
  (forall x, locally_closed (sigma x)) /\
  (forall x T, Gamma x = Some T -> R T (sigma x)).

Lemma env_good_extend : forall Gamma sigma x u T1,
  env_good Gamma sigma ->
  locally_closed u ->
  R T1 u ->
  env_good (update Gamma x T1) (extend x u sigma).
Proof.
  intros Gamma sigma x u T1 [Hlc HR] Hlcu HRu.
  split.
  - intros y. unfold extend.
    destruct (Nat.eqb x y); [exact Hlcu | apply Hlc].
  - intros y U Hy. unfold extend, update in *.
    destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. subst y.
      injection Hy as HU. subst U. exact HRu.
    + apply Nat.eqb_neq in E. apply HR. exact Hy.
Qed.

Lemma fundamental : forall Gamma t T,
  has_type Gamma t T ->
  forall sigma, env_good Gamma sigma -> R T (subst_tm sigma t).
Proof.
  intros Gamma t T Hty.
  induction Hty as [Gamma x T Hx
                 | L Gamma T1 T2 t1 Hraw IH
                 | Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
                 | Gamma
                 | Gamma].
  - intros sigma [Hlc HR]. simpl. apply HR. exact Hx.
  - intros sigma [Hlc HR]. simpl.
    assert (Hbody : forall u, R T1 u -> R T2 (open (subst_tm sigma t1) u)).
    { intros u Hu.
      destruct (fresh_exists (L ++ fvs t1)) as [x Hx].
      assert (HxL : ~ In x L).
      { intro H. apply Hx. apply in_app_iff. left. exact H. }
      assert (Hxfvs : ~ In x (fvs t1)).
      { intro H. apply Hx. apply in_app_iff. right. exact H. }
      pose proof (IH x HxL (extend x u sigma)) as HRx.
      assert (Hg' : env_good (update Gamma x T1) (extend x u sigma)).
      { apply env_good_extend.
        - split; [exact Hlc | exact HR].
        - apply (R_lc T1 u Hu).
        - exact Hu. }
      specialize (HRx Hg').
      unfold open in HRx.
      rewrite (subst_tm_open_fvar t1 sigma x u 0 Hlc Hxfvs) in HRx.
      exact HRx. }
    assert (Hlcbody : lc_at 1 (subst_tm sigma t1)).
    { pose proof (Hbody (tm_fvar 0) (R_fvar T1 0)) as HR0.
      apply (R_lc T2 (open (subst_tm sigma t1) (tm_fvar 0))) in HR0.
      unfold open in HR0.
      apply (lc_open_inv (subst_tm sigma t1) 0 (tm_fvar 0) (lc_fvar 0 0)).
      exact HR0. }
    split; [apply lc_abs; exact Hlcbody | split].
    + apply value_SN, v_abs, lc_abs. exact Hlcbody.
    + intros v Hm Hvval.
      assert (Hveq : v = tm_abs T1 (subst_tm sigma t1)).
      { apply (value_multi_self (tm_abs T1 (subst_tm sigma t1)) v Hm).
        apply v_abs, lc_abs. exact Hlcbody. }
      exists (subst_tm sigma t1).
      split; [exact Hveq | split; [exact Hlcbody | exact Hbody]].
  - intros sigma Hg. simpl.
    apply (R_app T1 T2 (subst_tm sigma t1) (subst_tm sigma t2)).
    + apply IH1. exact Hg.
    + apply IH2. exact Hg.
  - intros sigma Hg. simpl. apply R_true.
  - intros sigma Hg. simpl. apply R_false.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Hty.
  assert (Hg : env_good empty idenv).
  { split; [intro x; apply lc_fvar | intros x U Hx; inversion Hx]. }
  pose proof (fundamental empty t T Hty idenv Hg) as HR.
  rewrite subst_tm_idenv in HR.
  exact (R_sn T t HR).
Qed.

End STLCNormalizationNoneHardTask.
