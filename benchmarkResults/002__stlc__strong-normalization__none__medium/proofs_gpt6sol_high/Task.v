(** STLC call-by-value strong-normalization benchmark, Medium variant.
    No if-then-else, non-determinism, or recursion is included. *)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Relations.Relation_Definitions.
From Stdlib Require Import Lia.
Import ListNotations.

Module STLCNormalizationNoneMediumTask.

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

(** Provided logical relation. *)

Inductive strongly_normalizing : tm -> Prop :=
  | SN_intro : forall t,
      (forall t', t --> t' -> strongly_normalizing t') ->
      strongly_normalizing t.

Fixpoint value_relation (T : ty) (v : tm) : Prop :=
  value v /\
  match T with
  | Ty_Bool =>
      v = tm_true \/ v = tm_false
  | Ty_Arrow T1 T2 =>
      exists body,
        v = tm_abs T1 body /\
        forall arg,
          value_relation T1 arg ->
          locally_closed (open body arg) /\
          exists v',
            open body arg -->* v' /\
            value_relation T2 v'
  end.

Definition expression_relation (T : ty) (t : tm) : Prop :=
  locally_closed t /\
  exists v,
    t -->* v /\
    value_relation T v.

Definition term_substitution := atom -> tm.

Definition id_substitution : term_substitution :=
  fun x => tm_fvar x.

Definition subst_update
    (rho : term_substitution) (x : atom) (v : tm) : term_substitution :=
  fun y => if Nat.eqb x y then v else rho y.

Fixpoint msubst (rho : term_substitution) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => rho x
  | tm_app t1 t2 => tm_app (msubst rho t1) (msubst rho t2)
  | tm_abs T t1 => tm_abs T (msubst rho t1)
  | tm_true => tm_true
  | tm_false => tm_false
  end.

Definition proper_substitution (rho : term_substitution) : Prop :=
  forall x, locally_closed (rho x).

Definition related_substitution
    (Gamma : context) (rho : term_substitution) : Prop :=
  forall x T,
    Gamma x = Some T ->
    value_relation T (rho x).

Fixpoint free_vars (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_app t1 t2 => free_vars t1 ++ free_vars t2
  | tm_abs _ body => free_vars body
  | tm_true | tm_false => []
  end.

Definition fresh (xs : list atom) := S (fold_right Nat.max 0 xs).

Lemma fresh_not_in : forall xs, ~ In (fresh xs) xs.
Proof.
  intros xs. unfold fresh.
  assert (forall x, In x xs -> x <= fold_right Nat.max 0 xs) as Hbound.
  { induction xs as [| a xs IH]; simpl; intros x H; [contradiction|].
    destruct H as [<-|H]; [apply Nat.le_max_l|].
    eapply Nat.le_trans; [apply IH; exact H|apply Nat.le_max_r]. }
  intros Hin. specialize (Hbound _ Hin). lia.
Qed.

Lemma lc_at_mono : forall k t, lc_at k t ->
  forall j, k <= j -> lc_at j t.
Proof.
  intros k t H. induction H; intros j Hle; constructor;
    try (eauto); try lia; apply IHlc_at; lia.
Qed.

Lemma lc_at_weaken : forall k t, lc_at 0 t -> lc_at k t.
Proof.
  intros k t H. eapply lc_at_mono; [exact H|lia].
Qed.

Lemma value_lc : forall v, value v -> locally_closed v.
Proof. intros v H; inversion H; subst; try assumption; constructor. Qed.

Lemma open_rec_above : forall k t,
  lc_at k t -> forall j u, k <= j -> open_rec j u t = t.
Proof.
  intros k t H. induction H; intros j u Hle; simpl; try reflexivity.
  - assert (Hneq : j <> i) by lia.
    apply Nat.eqb_neq in Hneq. rewrite Hneq. reflexivity.
  - rewrite IHlc_at1, IHlc_at2 by lia. reflexivity.
  - rewrite IHlc_at by lia. reflexivity.
Qed.

Lemma open_rec_closed : forall k u t,
  locally_closed t -> open_rec k u t = t.
Proof.
  intros k u t H. eapply open_rec_above; [exact H|lia].
Qed.

Lemma lc_open_inv : forall k t x,
  lc_at k (open_rec k (tm_fvar x) t) -> lc_at (S k) t.
Proof.
  intros k t; revert k.
  induction t; intros k x H; simpl in H.
  - destruct (Nat.eqb k n) eqn:Heq; [apply Nat.eqb_eq in Heq; subst; constructor; lia|].
    inversion H; subst. apply Nat.eqb_neq in Heq. constructor. lia.
  - apply lc_fvar.
  - inversion H; subst. apply lc_app; [eapply IHt1|eapply IHt2]; eassumption.
  - inversion H; subst. apply lc_abs. eapply IHt; eassumption.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma msubst_lc_at : forall t k rho,
  lc_at k t -> proper_substitution rho -> lc_at k (msubst rho t).
Proof.
  intros t k rho H. revert rho.
  induction H; intros rho Hproper; simpl; try constructor; try (eauto).
  apply lc_at_weaken. apply Hproper.
Qed.

Lemma msubst_open_rec : forall t k u rho,
  proper_substitution rho ->
  msubst rho (open_rec k u t) =
  open_rec k (msubst rho u) (msubst rho t).
Proof.
  induction t; intros k u rho Hproper; simpl;
    try reflexivity;
    try (rewrite IHt1, IHt2 by assumption; reflexivity);
    try (rewrite IHt by assumption; reflexivity).
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. apply open_rec_closed. apply Hproper.
Qed.

Lemma msubst_irrelevant : forall t rho x v,
  ~ In x (free_vars t) ->
  msubst (subst_update rho x v) t = msubst rho t.
Proof.
  induction t; intros rho x v H; simpl in *; try reflexivity.
  - unfold subst_update. destruct (Nat.eqb x a) eqn:Heq; [|reflexivity].
    apply Nat.eqb_eq in Heq. subst. exfalso. apply H. auto.
  - assert (H1 : ~ In x (free_vars t1)) by (intro Hin; apply H; apply in_app_iff; auto).
    assert (H2 : ~ In x (free_vars t2)) by (intro Hin; apply H; apply in_app_iff; auto).
    rewrite IHt1 by exact H1. rewrite IHt2 by exact H2. reflexivity.
  - f_equal. apply IHt. exact H.
Qed.

Lemma free_vars_open : forall t k x y,
  x <> y -> In x (free_vars t) ->
  In x (free_vars (open_rec k (tm_fvar y) t)).
Proof.
  induction t; intros k x y Hneq Hin; simpl in *; try contradiction.
  - exact Hin.
  - apply in_app_iff in Hin. apply in_app_iff.
    destruct Hin as [Hin|Hin]; [left; eapply IHt1|right; eapply IHt2]; eauto.
  - eapply IHt; eauto.
Qed.

Lemma typing_lc : forall Gamma t T, has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T Hty. induction Hty; try constructor; eauto.
  - pose (x := fresh L).
    assert (Hfresh : ~ In x L) by (unfold x; apply fresh_not_in).
    specialize (H0 x Hfresh).
    specialize (H x Hfresh).
    eapply lc_open_inv. exact H0.
Qed.

Lemma typing_free_vars : forall Gamma t T x,
  has_type Gamma t T -> In x (free_vars t) -> exists U, Gamma x = Some U.
Proof.
  intros Gamma t T x Hty. induction Hty; simpl; intros Hin; try contradiction.
  - destruct Hin as [<-|[]]. eauto.
  - pose (y := fresh (x :: L)).
    assert (Hfresh : ~ In y (x :: L)) by (unfold y; apply fresh_not_in).
    assert (Hneq : x <> y) by (intro Heq; apply Hfresh; left; exact Heq).
    assert (Hnot : ~ In y L) by (intro HinY; apply Hfresh; right; exact HinY).
    assert (Hin' : In x (free_vars (open t1 (tm_fvar y)))).
    { unfold open. eapply free_vars_open; eauto. }
    specialize (H0 y Hnot Hin').
    destruct H0 as [U HU]. exists U. unfold update in HU.
    assert (Hneq' : y <> x) by (intro Heq; apply Hneq; symmetry; exact Heq).
    apply Nat.eqb_neq in Hneq'. rewrite Hneq' in HU. exact HU.
  - apply in_app_iff in Hin. destruct Hin as [Hin|Hin]; eauto.
Qed.

Lemma msubst_closed_typing : forall t T rho,
  has_type empty t T -> msubst rho t = t.
Proof.
  intros t T rho Hty.
  assert (forall x, ~ In x (free_vars t)) as Hfree.
  { intros x Hin. destruct (typing_free_vars _ _ _ _ Hty Hin) as [U HU].
    discriminate HU. }
  clear Hty. revert Hfree. induction t; intros Hfree; simpl in *; try reflexivity.
  - exfalso. apply (Hfree a). auto.
  - f_equal; [apply IHt1|apply IHt2]; intros x Hin;
      apply (Hfree x); simpl; apply in_app_iff; auto.
  - f_equal. apply IHt. exact Hfree.
Qed.

Lemma multi_trans : forall t u v,
  t -->* u -> u -->* v -> t -->* v.
Proof.
  intros t u v H. induction H; intros Htail; eauto using multi.
Qed.

Lemma multi_app1 : forall t1 v1 t2,
  t1 -->* v1 -> locally_closed t2 ->
  tm_app t1 t2 -->* tm_app v1 t2.
Proof.
  intros t1 v1 t2 H. induction H; intros Hlc.
  - constructor.
  - eapply multi_step; [eapply ST_App1; eassumption|auto].
Qed.

Lemma multi_app2 : forall v1 t2 v2,
  value v1 -> t2 -->* v2 ->
  tm_app v1 t2 -->* tm_app v1 v2.
Proof.
  intros v1 t2 v2 Hv H. induction H.
  - constructor.
  - eapply multi_step; [eapply ST_App2; eassumption|auto].
Qed.

Lemma value_relation_value : forall T v, value_relation T v -> value v.
Proof. destruct T; simpl; intros v H; exact (proj1 H). Qed.

Lemma expression_app : forall T1 T2 t1 t2,
  expression_relation (Ty_Arrow T1 T2) t1 ->
  expression_relation T1 t2 ->
  expression_relation T2 (tm_app t1 t2).
Proof.
  intros T1 T2 t1 t2 [Hlc1 [v1 [Hsteps1 [Hval1 Hfun]]]]
    [Hlc2 [v2 [Hsteps2 Hv2]]].
  destruct Hfun as [body [Heq Hfun]]. subst v1.
  destruct (Hfun v2 Hv2) as [Hopened [v3 [Hsteps3 Hv3]]].
  split; [apply lc_app; assumption|].
  exists v3. split; [|exact Hv3].
  eapply multi_trans.
  - eapply multi_app1; eassumption.
  - eapply multi_trans.
    + eapply multi_app2; [exact Hval1|exact Hsteps2].
    + eapply multi_step.
      * apply ST_AppAbs; [apply value_lc; exact Hval1|apply value_relation_value with T1; exact Hv2].
      * exact Hsteps3.
Qed.

Theorem fundamental : forall Gamma t T,
  has_type Gamma t T ->
  forall rho, proper_substitution rho -> related_substitution Gamma rho ->
  expression_relation T (msubst rho t).
Proof.
  intros Gamma t T Hty. induction Hty; intros rho Hproper Hrelated; simpl.
  - specialize (Hrelated x T H).
    split; [apply value_lc; apply value_relation_value with T; exact Hrelated|].
    exists (rho x). split; [constructor|exact Hrelated].
  - split.
    + change (locally_closed (msubst rho (tm_abs T1 t1))).
      eapply msubst_lc_at; [eapply typing_lc; apply T_Abs with (L := L); exact H|exact Hproper].
    + exists (tm_abs T1 (msubst rho t1)). split; [constructor|].
      split.
      * apply v_abs. change (locally_closed (msubst rho (tm_abs T1 t1))).
        eapply msubst_lc_at;
          [eapply typing_lc; apply T_Abs with (L := L); exact H|exact Hproper].
      * simpl. exists (msubst rho t1). split; [reflexivity|].
        intros arg Harg.
        pose (x := fresh (L ++ free_vars t1)).
        assert (Hfresh : ~ In x (L ++ free_vars t1))
          by (unfold x; apply fresh_not_in).
        assert (HnotL : ~ In x L).
        { intro Hin. apply Hfresh. apply in_app_iff. auto. }
        assert (HnotF : ~ In x (free_vars t1)).
        { intro Hin. apply Hfresh. apply in_app_iff. auto. }
        pose (rho' := subst_update rho x arg).
        assert (Hproper' : proper_substitution rho').
        { intros y. unfold rho', subst_update. destruct (Nat.eqb x y);
            [apply value_lc; apply value_relation_value with T1; exact Harg|apply Hproper]. }
        assert (Hrelated' : related_substitution (update Gamma x T1) rho').
        { intros y U Hy. unfold update in Hy; unfold rho', subst_update.
          destruct (Nat.eqb x y) eqn:Heq.
          - inversion Hy; subst. exact Harg.
          - apply Hrelated. exact Hy. }
        specialize (H0 x HnotL rho' Hproper' Hrelated').
        assert (Heq : msubst rho' (open t1 (tm_fvar x)) =
                      open (msubst rho t1) arg).
        { unfold open. rewrite msubst_open_rec by exact Hproper'.
          simpl. replace (rho' x) with arg
            by (unfold rho', subst_update; rewrite Nat.eqb_refl; reflexivity).
          change (msubst rho' t1) with (msubst (subst_update rho x arg) t1).
          rewrite msubst_irrelevant by exact HnotF. reflexivity. }
        rewrite Heq in H0. exact H0.
  - eapply expression_app; [apply IHHty1|apply IHHty2]; assumption.
  - split; [apply lc_true|]. exists tm_true. split; [constructor|].
    simpl. split; [constructor|left; reflexivity].
  - split; [apply lc_false|]. exists tm_false. split; [constructor|].
    simpl. split; [constructor|right; reflexivity].
Qed.

Lemma value_no_step : forall v t, value v -> v --> t -> False.
Proof.
  intros v t Hv Hstep. inversion Hv; subst; inversion Hstep.
Qed.

Lemma step_deterministic : forall t u v,
  t --> u -> t --> v -> u = v.
Proof.
  intros t u v Hstep. revert v.
  induction Hstep; intros result Hother; inversion Hother; subst;
    try reflexivity;
    try (exfalso; match goal with
         | Hs : tm_abs _ _ --> _ |- _ => inversion Hs
         | Hv : value ?term, Hs : ?term --> _ |- _ =>
             exact (value_no_step term _ Hv Hs)
         end);
    f_equal; eauto.
Qed.

Lemma sn_multistep_value : forall t v,
  t -->* v -> value v -> strongly_normalizing t.
Proof.
  intros t v Hsteps. induction Hsteps; intros Hv.
  - constructor. intros next Hstep.
    exfalso. eapply value_no_step; eassumption.
  - constructor. intros next Hstep.
    assert (next = y) by (eapply step_deterministic; eassumption).
    subst next. apply IHHsteps. exact Hv.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Hty.
  pose (rho := fun _ : atom => tm_true).
  assert (Hproper : proper_substitution rho).
  { intros x. apply lc_true. }
  assert (Hrelated : related_substitution empty rho).
  { intros x U Hlookup. discriminate Hlookup. }
  pose proof (fundamental _ _ _ Hty rho Hproper Hrelated) as Hexpr.
  rewrite (msubst_closed_typing t T rho Hty) in Hexpr.
  destruct Hexpr as [_ [v [Hsteps Hval]]].
  eapply sn_multistep_value; [exact Hsteps|].
  eapply value_relation_value. exact Hval.
Qed.

End STLCNormalizationNoneMediumTask.
