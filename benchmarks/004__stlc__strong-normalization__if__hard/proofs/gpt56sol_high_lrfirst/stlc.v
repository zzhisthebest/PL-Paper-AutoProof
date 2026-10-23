(** STLC call-by-value normalization benchmark task. *)

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

(** Target theorem. *)

Definition halts (t : tm) : Prop :=
  exists v, t -->* v /\ value v.

(** A closing substitution, represented as a total map.  Its values will be
    required to be locally closed, so it is harmless to pass underneath a
    locally-nameless binder. *)

Definition closing_subst := atom -> tm.

Definition extend_subst (rho : closing_subst) (x : atom) (u : tm) :
    closing_subst :=
  fun y => if Nat.eqb x y then u else rho y.

Fixpoint inst (rho : closing_subst) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => rho x
  | tm_app t1 t2 => tm_app (inst rho t1) (inst rho t2)
  | tm_abs T t1 => tm_abs T (inst rho t1)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (inst rho t1) (inst rho t2) (inst rho t3)
  end.

Fixpoint fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ => nil
  | tm_fvar x => x :: nil
  | tm_app t1 t2 => fv t1 ++ fv t2
  | tm_abs _ t1 => fv t1
  | tm_true | tm_false => nil
  | tm_if t1 t2 t3 => fv t1 ++ fv t2 ++ fv t3
  end.

Fixpoint list_max (xs : list nat) : nat :=
  match xs with
  | nil => 0
  | x :: xs' => Nat.max x (list_max xs')
  end.

Lemma in_list_max : forall x xs, In x xs -> x <= list_max xs.
Proof.
  intros x xs H. induction xs as [|a xs IH]; simpl in *.
  - contradiction.
  - destruct H as [-> | H].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; exact H | apply Nat.le_max_r].
Qed.

Lemma fresh_not_in : forall xs, ~ In (S (list_max xs)) xs.
Proof.
  intros xs H. pose proof (in_list_max _ _ H). lia.
Qed.

Lemma lc_at_monotone : forall k k' t,
  lc_at k t -> k <= k' -> lc_at k' t.
Proof.
  intros k k' t H. generalize dependent k'.
  induction H; intros k' Hle.
  - apply lc_bvar. lia.
  - apply lc_fvar.
  - apply lc_app; eauto.
  - apply lc_abs. apply IHlc_at. lia.
  - apply lc_true.
  - apply lc_false.
  - apply lc_if; eauto.
Qed.

Lemma open_rec_lc_at : forall k t u,
  lc_at k t -> open_rec k u t = t.
Proof.
  intros k t u H. induction H; simpl; try rewrite ?IHlc_at1, ?IHlc_at2,
    ?IHlc_at3; try reflexivity.
  - assert (Nat.eqb k i = false) as E by (apply Nat.eqb_neq; lia).
    rewrite E. reflexivity.
  - rewrite IHlc_at. reflexivity.
Qed.

Lemma open_rec_lc_at_inv : forall t k u,
  lc_at k (open_rec k u t) -> lc_at (S k) t.
Proof.
  induction t; intros k u H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + constructor. apply Nat.eqb_eq in E. lia.
    + inversion H; subst. constructor. lia.
  - constructor.
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor. eapply IHt; eauto.
  - constructor.
  - constructor.
  - inversion H; subst. constructor; eauto.
Qed.

Lemma typing_lc : forall Gamma t T,
  <{ Gamma |-- t \in T }> -> locally_closed t.
Proof.
  intros Gamma t T Hty. induction Hty.
  - constructor.
  - constructor.
    set (x := S (list_max L)).
    apply (open_rec_lc_at_inv t1 0 (tm_fvar x)).
    apply H0. subst x. apply fresh_not_in.
  - constructor; assumption.
  - constructor.
  - constructor.
  - constructor; assumption.
Qed.

Lemma inst_lc_at : forall k t rho,
  lc_at k t ->
  (forall x, locally_closed (rho x)) ->
  lc_at k (inst rho t).
Proof.
  intros k t rho H. induction H; intros Hrho; simpl; try constructor; eauto.
  eapply lc_at_monotone; [apply Hrho | lia].
Qed.

Lemma inst_open_fresh : forall t k rho x u,
  ~ In x (fv t) ->
  (forall y, locally_closed (rho y)) ->
  inst (extend_subst rho x u) (open_rec k (tm_fvar x) t) =
  open_rec k u (inst rho t).
Proof.
  induction t; intros k rho x u Hfresh Hrho; simpl in *.
  - destruct (Nat.eqb k n) eqn:E; simpl.
    + unfold extend_subst. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - assert (x <> a) by (intro; subst; apply Hfresh; auto).
    unfold extend_subst. destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E. contradiction.
    + symmetry. apply open_rec_lc_at.
      eapply lc_at_monotone; [apply Hrho | lia].
  - rewrite in_app_iff in Hfresh.
    assert (Hf1 : ~ In x (fv t1)).
    { intro Hin. apply Hfresh. left. exact Hin. }
    assert (Hf2 : ~ In x (fv t2)).
    { intro Hin. apply Hfresh. right. exact Hin. }
    rewrite (IHt1 k rho x u Hf1 Hrho), (IHt2 k rho x u Hf2 Hrho).
    reflexivity.
  - rewrite (IHt (S k) rho x u Hfresh Hrho). reflexivity.
  - reflexivity.
  - reflexivity.
  - repeat rewrite in_app_iff in Hfresh.
    assert (Hf1 : ~ In x (fv t1)) by intuition.
    assert (Hf2 : ~ In x (fv t2)) by intuition.
    assert (Hf3 : ~ In x (fv t3)) by intuition.
    rewrite (IHt1 k rho x u Hf1 Hrho), (IHt2 k rho x u Hf2 Hrho),
      (IHt3 k rho x u Hf3 Hrho). reflexivity.
Qed.

(** The logical relation is an expression relation.  At booleans it records
    which canonical boolean is reached.  At arrows it records the abstraction
    reached and its action on every reducible argument. *)

Fixpoint R (T : ty) (t : tm) : Prop :=
  match T with
  | Ty_Bool =>
      locally_closed t /\ (t -->* tm_true \/ t -->* tm_false)
  | Ty_Arrow A B =>
      locally_closed t /\
      exists U b,
        t -->* tm_abs U b /\
        value (tm_abs U b) /\
        forall u, R A u -> R B (open b u)
  end.

Definition subst_lc (rho : closing_subst) : Prop :=
  forall x, locally_closed (rho x).

Definition models (rho : closing_subst) (Gamma : context) : Prop :=
  forall x T, Gamma x = Some T -> R T (rho x).

Lemma multi_trans : forall t1 t2 t3,
  t1 -->* t2 -> t2 -->* t3 -> t1 -->* t3.
Proof.
  intros t1 t2 t3 H12 H23. induction H12; eauto using multi.
Qed.

Lemma multi_app1 : forall t1 t1' t2,
  t1 -->* t1' -> locally_closed t2 ->
  tm_app t1 t2 -->* tm_app t1' t2.
Proof.
  intros t1 t1' t2 H. induction H; intros Hlc.
  - constructor.
  - econstructor; eauto using step.
Qed.

Lemma multi_app2 : forall v t t',
  value v -> t -->* t' -> tm_app v t -->* tm_app v t'.
Proof.
  intros v t t' Hv H. induction H.
  - constructor.
  - econstructor; eauto using step.
Qed.

Lemma multi_if : forall t t' t2 t3,
  t -->* t' -> locally_closed t2 -> locally_closed t3 ->
  tm_if t t2 t3 -->* tm_if t' t2 t3.
Proof.
  intros t t' t2 t3 H. induction H; intros H2 H3.
  - constructor.
  - econstructor; eauto using step.
Qed.

Lemma R_lc : forall T t, R T t -> locally_closed t.
Proof.
  destruct T; simpl; intuition.
Qed.

Lemma R_backwards : forall T t t',
  t -->* t' -> locally_closed t -> R T t' -> R T t.
Proof.
  induction T as [|A IHA B IHB]; intros t t' Hsteps Hlc HR; simpl in *.
  - destruct HR as [_ Hred]. split.
    + exact Hlc.
    + destruct Hred as [Ht | Hf].
      * left. eapply multi_trans; eauto.
      * right. eapply multi_trans; eauto.
  - destruct HR as [_ [U [b [Hb [Hv Hmap]]]]].
    split.
    + exact Hlc.
    + exists U, b. split.
      * eapply multi_trans; eauto.
      * split; assumption.
Qed.

Lemma R_value : forall T t,
  R T t -> exists v, t -->* v /\ value v /\ R T v.
Proof.
  destruct T as [|A B]; intros t HR; simpl in HR.
  - destruct HR as [Hlc [Ht | Hf]].
    + exists tm_true. split; [exact Ht |]. split; [constructor |].
      simpl. split; [constructor | left; constructor].
    + exists tm_false. split; [exact Hf |]. split; [constructor |].
      simpl. split; [constructor | right; constructor].
  - destruct HR as [Hlc [U [b [Hs [Hv Hmap]]]]].
    exists (tm_abs U b). split; [exact Hs |]. split; [exact Hv |].
    simpl. split.
    + inversion Hv; assumption.
    + exists U, b. split; [constructor |]. split; assumption.
Qed.

Lemma extend_subst_lc : forall rho x u,
  subst_lc rho -> locally_closed u -> subst_lc (extend_subst rho x u).
Proof.
  intros rho x u Hr Hu y. unfold extend_subst.
  destruct (Nat.eqb x y); auto.
Qed.

Lemma extend_subst_models : forall rho Gamma x A u,
  models rho Gamma -> R A u -> models (extend_subst rho x u) (update Gamma x A).
Proof.
  intros rho Gamma x A u Hmodels Hu y T Hlookup.
  unfold update in Hlookup. unfold extend_subst.
  destruct (Nat.eqb x y) eqn:E.
  - inversion Hlookup; subst. exact Hu.
  - eapply Hmodels; eauto.
Qed.

Lemma R_app : forall A B t1 t2,
  R (Ty_Arrow A B) t1 -> R A t2 -> R B (tm_app t1 t2).
Proof.
  intros A B t1 t2 Hfun Harg.
  destruct Hfun as [Hlc1 [U [b [Hfun [Hvfun Hmap]]]]].
  destruct (R_value _ _ Harg) as [v [Hargsteps [Hv Hrv]]].
  apply (R_backwards B (tm_app t1 t2) (open b v)).
  - eapply multi_trans.
    + apply multi_app1; [exact Hfun | apply R_lc with A; exact Harg].
    + eapply multi_trans.
      * apply multi_app2; eauto.
      * econstructor.
        -- apply ST_AppAbs.
           ++ inversion Hvfun; assumption.
           ++ exact Hv.
        -- constructor.
  - apply lc_app.
    + exact Hlc1.
    + apply R_lc with A. exact Harg.
  - apply Hmap. exact Hrv.
Qed.

Lemma R_if : forall T t1 t2 t3,
  R Ty_Bool t1 -> R T t2 -> R T t3 -> R T (tm_if t1 t2 t3).
Proof.
  intros T t1 t2 t3 Htest Hthen Helse.
  destruct Htest as [Hlc1 [Htrue | Hfalse]].
  - apply (R_backwards T (tm_if t1 t2 t3) t2).
    + eapply multi_trans.
      * apply multi_if.
        -- exact Htrue.
        -- apply R_lc with T. exact Hthen.
        -- apply R_lc with T. exact Helse.
      * econstructor.
        -- apply ST_IfTrue.
           ++ apply R_lc with T. exact Hthen.
           ++ apply R_lc with T. exact Helse.
        -- constructor.
    + apply lc_if.
      * exact Hlc1.
      * apply R_lc with T. exact Hthen.
      * apply R_lc with T. exact Helse.
    + exact Hthen.
  - apply (R_backwards T (tm_if t1 t2 t3) t3).
    + eapply multi_trans.
      * apply multi_if.
        -- exact Hfalse.
        -- apply R_lc with T. exact Hthen.
        -- apply R_lc with T. exact Helse.
      * econstructor.
        -- apply ST_IfFalse.
           ++ apply R_lc with T. exact Hthen.
           ++ apply R_lc with T. exact Helse.
        -- constructor.
    + apply lc_if.
      * exact Hlc1.
      * apply R_lc with T. exact Hthen.
      * apply R_lc with T. exact Helse.
    + exact Helse.
Qed.

Theorem fundamental : forall Gamma t T,
  <{ Gamma |-- t \in T }> ->
  forall rho, subst_lc rho -> models rho Gamma -> R T (inst rho t).
Proof.
  intros Gamma t T Hty.
  induction Hty as
      [Gamma x T Hlookup
      |L Gamma A B body Hbody IHbody
      |Gamma t1 t2 A B Ht1 IH1 Ht2 IH2
      |Gamma
      |Gamma
      |Gamma t1 t2 t3 T Ht1 IH1 Ht2 IH2 Ht3 IH3];
    intros rho Hrlc Hmodels; simpl.
  - exact (Hmodels x T Hlookup).
  - assert (Habs_lc : locally_closed (tm_abs A (inst rho body))).
    { change (locally_closed (inst rho (tm_abs A body))).
      apply inst_lc_at.
      - apply typing_lc with (Gamma := Gamma) (T := Ty_Arrow A B).
        apply T_Abs with L. exact Hbody.
      - exact Hrlc. }
    split.
    + exact Habs_lc.
    + exists A, (inst rho body). repeat split.
      * constructor.
      * constructor. exact Habs_lc.
      * intros u Hu.
        set (x := S (list_max (L ++ fv body))).
        assert (Hxall : ~ In x (L ++ fv body)).
        { subst x. apply fresh_not_in. }
        assert (HxL : ~ In x L).
        { intro Hin. apply Hxall. apply in_or_app. left. exact Hin. }
        assert (Hxfv : ~ In x (fv body)).
        { intro Hin. apply Hxall. apply in_or_app. right. exact Hin. }
        specialize (IHbody x HxL (extend_subst rho x u)).
        unfold open.
        rewrite <- (inst_open_fresh body 0 rho x u Hxfv Hrlc).
        apply IHbody.
        -- apply extend_subst_lc; eauto using R_lc.
        -- apply extend_subst_models; assumption.
  - apply R_app with A; auto.
  - split; [constructor | left; constructor].
  - split; [constructor | right; constructor].
  - apply R_if; auto.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  halts t.
Proof.
  intros t T Hty.
  pose (rho := fun x : atom => tm_fvar x).
  assert (Hrho_lc : subst_lc rho).
  { intros x. constructor. }
  assert (Hmodels : models rho empty).
  { intros x U H. discriminate. }
  pose proof (fundamental empty t T Hty rho Hrho_lc Hmodels) as HR.
  destruct (R_value T (inst rho t) HR) as [v [Hsteps [Hv _]]].
  assert (Hinst : inst rho t = t).
  { clear Hty HR Hsteps Hv. induction t; simpl; try rewrite ?IHt1, ?IHt2, ?IHt3,
      ?IHt; reflexivity. }
  rewrite Hinst in Hsteps. exists v. auto.
Qed.

End STLCCBVNormalizationTask.
