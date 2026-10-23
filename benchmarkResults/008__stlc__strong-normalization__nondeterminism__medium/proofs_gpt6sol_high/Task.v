(** STLC call-by-value strong-normalization benchmark, Medium variant.
    Non-deterministic choice is included; if-then-else and recursion are not. *)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Relations.Relation_Definitions.
From Stdlib Require Import Lia.

Module STLCNormalizationNondeterminismMediumTask.

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

(** Provided logical relation. *)

Fixpoint strong_value_relation (T : ty) (v : tm) : Prop :=
  value v /\
  match T with
  | Ty_Bool =>
      v = tm_true \/ v = tm_false
  | Ty_Arrow T1 T2 =>
      exists body,
        v = tm_abs T1 body /\
        forall arg,
          strong_value_relation T1 arg ->
          locally_closed (open body arg) /\
          strongly_normalizing (open body arg) /\
          forall result,
            open body arg -->* result ->
            value result ->
            strong_value_relation T2 result
  end.

Definition strong_expression_relation (T : ty) (t : tm) : Prop :=
  locally_closed t /\
  strongly_normalizing t /\
  forall v,
    t -->* v ->
    value v ->
    strong_value_relation T v.

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
  | tm_choice t1 t2 => tm_choice (msubst rho t1) (msubst rho t2)
  end.

Definition proper_substitution (rho : term_substitution) : Prop :=
  forall x, locally_closed (rho x).

Definition strong_related_substitution
    (Gamma : context) (rho : term_substitution) : Prop :=
  forall x T,
    Gamma x = Some T ->
    strong_value_relation T (rho x).

Lemma value_closed : forall v, value v -> locally_closed v.
Proof. intros v H; inversion H; subst; try assumption; constructor. Qed.

Lemma lc_weaken : forall t k j, lc_at k t -> k <= j -> lc_at j t.
Proof.
  intros t k j H; revert j; induction H; intros j Hle.
  - apply lc_bvar; lia.
  - apply lc_fvar.
  - apply lc_app; eauto.
  - apply lc_abs. apply IHlc_at; lia.
  - apply lc_true.
  - apply lc_false.
  - apply lc_choice; eauto.
Qed.

Lemma open_rec_lc : forall t k u,
  lc_at (S k) t -> locally_closed u -> lc_at k (open_rec k u t).
Proof.
  induction t; intros k u H Huc; inversion H; subst; simpl;
    try (constructor; eauto; fail).
  destruct (Nat.eqb k n) eqn:E.
  - eapply lc_weaken; eauto; lia.
  - apply Nat.eqb_neq in E. constructor. lia.
Qed.

Lemma lc_open_inverse : forall t k u,
  lc_at k (open_rec k u t) -> lc_at (S k) t.
Proof.
  induction t; intros k u H; simpl in H; try (inversion H; subst; constructor; eauto; fail).
  destruct (Nat.eqb k n) eqn:E.
  - apply Nat.eqb_eq in E; subst. constructor; lia.
  - inversion H; subst. constructor; lia.
Qed.

Lemma value_no_step : forall v t, value v -> v --> t -> False.
Proof. intros v t Hv Hs; inversion Hv; subst; inversion Hs. Qed.

Lemma closed_step : forall t u, locally_closed t -> t --> u -> locally_closed u.
Proof.
  intros t u Hlc Hs; induction Hs; inversion Hlc; subst.
  - inversion H; subst. eapply open_rec_lc; eauto using value_closed.
  - apply lc_app; [apply IHHs; assumption | assumption].
  - apply lc_app; [eapply value_closed; eauto | apply IHHs; assumption].
  - assumption.
  - assumption.
Qed.

Lemma expression_value : forall T v,
  strong_value_relation T v -> strong_expression_relation T v.
Proof.
  intros T v H. assert (Hv : value v).
  { destruct T; exact (proj1 H). }
  unfold strong_expression_relation. split; [eapply value_closed; eauto|].
  split; [constructor; intros u Hs; exfalso; eapply value_no_step; eauto|].
  intros w Hmulti Hw. inversion Hmulti; subst; auto.
  exfalso; exact (value_no_step _ _ Hv H0).
Qed.

Lemma expression_intro : forall T t,
  locally_closed t ->
  (forall u, t --> u -> strong_expression_relation T u) ->
  (forall v, t = v -> value v -> strong_value_relation T v) ->
  strong_expression_relation T t.
Proof.
  intros T t Hlc Hnext Hval. split; [assumption|].
  split.
  - constructor; intros u Hs. apply Hnext; assumption.
  - intros v Hmulti Hv. inversion Hmulti; subst; eauto.
    destruct (Hnext _ H) as (_ & _ & Hrel).
    apply Hrel; assumption.
Qed.

Lemma expression_choice : forall T a b,
  strong_expression_relation T a ->
  strong_expression_relation T b ->
  strong_expression_relation T (tm_choice a b).
Proof.
  intros T a b Ha Hb. destruct Ha as (Hla & Hsa & Hra).
  destruct Hb as (Hlb & Hsb & Hrb).
  eapply expression_intro; [constructor; eauto| |].
  - intros u Hs; inversion Hs; subst;
      unfold strong_expression_relation; auto.
  - intros v Heq Hv; subst; inversion Hv.
Qed.

Lemma expression_app : forall A B f a,
  strong_expression_relation (Ty_Arrow A B) f ->
  strong_expression_relation A a ->
  strong_expression_relation B (tm_app f a).
Proof.
  intros A B f a Hf Ha.
  destruct Hf as (Hlf & Hsf & Hrf).
  revert a Ha Hlf Hrf.
  induction Hsf as [f Hsf IHf]; intros a Ha Hlf Hrf.
  destruct Ha as (Hla & Hsa & Hra).
  revert Hla Hra.
  induction Hsa as [a Hsa IHa]; intros Hla Hra.
  eapply expression_intro; [constructor; eauto| |].
  - intros u Hstep; inversion Hstep; subst.
    + assert (Hfv : strong_value_relation (Ty_Arrow A B) (tm_abs T t)).
      { apply Hrf; [constructor|constructor; assumption]. }
      assert (Hav : strong_value_relation A a).
      { apply Hra; [constructor|assumption]. }
      destruct Hfv as (_ & body & Heq & Hbody); inversion Heq; subst.
      destruct (Hbody _ Hav) as (Hclosed & Hsn & Hresults).
      split; [assumption|]. split; [assumption|exact Hresults].
    + eapply IHf.
      * eassumption.
      * split; [exact Hla|]. split; [constructor; exact Hsa|exact Hra].
      * eapply closed_step; [exact Hlf|exact H1].
      * intros v Hmulti Hv. apply Hrf; auto.
        eapply multi_step; eauto.
    + eapply IHa.
      * eassumption.
      * eapply closed_step; [exact Hla|eassumption].
      * intros v Hmulti Hv. apply Hra; auto.
        eapply multi_step; eauto.
  - intros v Heq Hv; subst; inversion Hv.
Qed.

Lemma related_value_closed : forall T v,
  strong_value_relation T v -> locally_closed v.
Proof.
  intros T v H. apply value_closed. destruct T; exact (proj1 H).
Qed.

Lemma msubst_lc : forall t k rho,
  lc_at k t -> proper_substitution rho -> lc_at k (msubst rho t).
Proof.
  intros t k rho H; revert rho; induction H; intros rho Hprop; simpl.
  - apply lc_bvar; assumption.
  - eapply lc_weaken; [apply Hprop|lia].
  - apply lc_app; eauto.
  - apply lc_abs; eauto.
  - apply lc_true.
  - apply lc_false.
  - apply lc_choice; eauto.
Qed.

Lemma open_closed_any : forall t depth k u,
  lc_at depth t -> depth <= k -> open_rec k u t = t.
Proof.
  intros t depth k u H; revert k u; induction H; intros j u Hle; simpl.
  - destruct (Nat.eqb j i) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
  - reflexivity.
  - rewrite IHlc_at1, IHlc_at2 by lia; reflexivity.
  - rewrite IHlc_at by lia; reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IHlc_at1, IHlc_at2 by lia; reflexivity.
Qed.

Lemma msubst_open_rec : forall t k u rho,
  proper_substitution rho ->
  msubst rho (open_rec k u t) =
  open_rec k (msubst rho u) (msubst rho t).
Proof.
  induction t; intros k u rho Hprop; simpl;
    try (rewrite ?IHt, ?IHt1, ?IHt2; eauto; reflexivity).
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry; eapply open_closed_any; [apply Hprop|lia].
Qed.

Fixpoint free_atoms (t : tm) : list atom :=
  match t with
  | tm_bvar _ => nil
  | tm_fvar x => x :: nil
  | tm_app a b => free_atoms a ++ free_atoms b
  | tm_abs _ body => free_atoms body
  | tm_true | tm_false => nil
  | tm_choice a b => free_atoms a ++ free_atoms b
  end.

Lemma msubst_update_fresh : forall t rho x v,
  ~ In x (free_atoms t) ->
  msubst (subst_update rho x v) t = msubst rho t.
Proof.
  induction t; intros rho x v Hfresh; simpl in *; try reflexivity.
  - unfold subst_update. destruct (Nat.eqb x a) eqn:E; auto.
    apply Nat.eqb_eq in E; subst; exfalso; apply Hfresh; auto.
  - assert (Ha : ~ In x (free_atoms t1)).
    { intro Hin; apply Hfresh; apply in_or_app; left; exact Hin. }
    assert (Hb : ~ In x (free_atoms t2)).
    { intro Hin; apply Hfresh; apply in_or_app; right; exact Hin. }
    rewrite (IHt1 _ _ _ Ha), (IHt2 _ _ _ Hb); reflexivity.
  - rewrite (IHt _ _ _ Hfresh); reflexivity.
  - assert (Ha : ~ In x (free_atoms t1)).
    { intro Hin; apply Hfresh; apply in_or_app; left; exact Hin. }
    assert (Hb : ~ In x (free_atoms t2)).
    { intro Hin; apply Hfresh; apply in_or_app; right; exact Hin. }
    rewrite (IHt1 _ _ _ Ha), (IHt2 _ _ _ Hb); reflexivity.
Qed.

Definition fresh_atom (xs : list atom) : atom :=
  S (fold_right Nat.max 0 xs).

Lemma fresh_bound : forall xs x,
  In x xs -> x <= fold_right Nat.max 0 xs.
Proof.
  induction xs as [|a xs IH]; intros x H; simpl in *; [contradiction|].
  destruct H as [H|H]; [subst; lia|]. specialize (IH _ H); lia.
Qed.

Lemma fresh_not_in : forall xs, ~ In (fresh_atom xs) xs.
Proof.
  intros xs H; unfold fresh_atom in H.
  apply fresh_bound in H; lia.
Qed.

Lemma typing_closed : forall Gamma t T,
  has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T Htype; induction Htype; try (constructor; eauto; fail).
  apply lc_abs. pose (x := fresh_atom L).
  apply (lc_open_inverse t1 0 (tm_fvar x)).
  apply H0. unfold x; apply fresh_not_in.
Qed.

Theorem fundamental : forall Gamma t T rho,
  has_type Gamma t T ->
  proper_substitution rho ->
  strong_related_substitution Gamma rho ->
  strong_expression_relation T (msubst rho t).
Proof.
  intros Gamma t T rho Htype.
  revert rho; induction Htype; intros rho Hprop Hrel; simpl.
  - apply expression_value. apply Hrel; assumption.
  - apply expression_value. simpl. split.
    + apply v_abs. change (lc_at 0 (msubst rho (tm_abs T1 t1))).
      eapply msubst_lc; [eapply typing_closed; eapply T_Abs; exact H|exact Hprop].
    + exists (msubst rho t1). split; [reflexivity|].
      intros arg Harg.
      pose (x := fresh_atom (L ++ free_atoms t1)).
      assert (Hnot : ~ In x L /\ ~ In x (free_atoms t1)).
      { split; intro Hin; apply (fresh_not_in (L ++ free_atoms t1));
          apply in_or_app; [left|right]; assumption. }
      destruct Hnot as [HnotL HnotT].
      assert (Hprop' : proper_substitution (subst_update rho x arg)).
      { intros y. unfold subst_update. destruct (Nat.eqb x y);
          [apply related_value_closed with T1; assumption|apply Hprop]. }
      assert (Hrel' : strong_related_substitution (update Gamma x T1)
                                                   (subst_update rho x arg)).
      { intros y U Hy. unfold update in Hy; unfold subst_update.
        destruct (Nat.eqb x y) eqn:E; [inversion Hy; subst; exact Harg|].
        apply Hrel; assumption. }
      specialize (H0 x HnotL (subst_update rho x arg) Hprop' Hrel').
      assert (Heq : msubst (subst_update rho x arg)
                          (open t1 (tm_fvar x)) = open (msubst rho t1) arg).
      { unfold open. rewrite msubst_open_rec by exact Hprop'.
        rewrite (msubst_update_fresh t1 rho x arg HnotT).
        simpl. unfold subst_update. rewrite Nat.eqb_refl. reflexivity. }
      rewrite Heq in H0. exact H0.
  - eapply expression_app; eauto.
  - apply expression_value. simpl; split; [constructor|left; reflexivity].
  - apply expression_value. simpl; split; [constructor|right; reflexivity].
  - apply expression_choice; eauto.
Qed.

Theorem strong_normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Htype.
  pose proof (fundamental empty t T id_substitution Htype) as Hfund.
  assert (Hprop : proper_substitution id_substitution).
  { intros x; apply lc_fvar. }
  assert (Hrel : strong_related_substitution empty id_substitution).
  { intros x U H; discriminate H. }
  specialize (Hfund Hprop Hrel).
  assert (Hid : forall s, msubst id_substitution s = s).
  { induction s; simpl; f_equal; auto. }
  rewrite Hid in Hfund. exact (proj1 (proj2 Hfund)).
Qed.

End STLCNormalizationNondeterminismMediumTask.
