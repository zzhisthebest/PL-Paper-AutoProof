(** STLC CBV strong-normalization benchmark, Medium variant.
    Features: nondeterminism-recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Relations.Relation_Definitions Lia.
Import ListNotations.

Module STLCNormalizationNondeterminismRecursionMediumTask.

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

  | tm_natrec : tm -> tm -> tm -> tm
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

Notation "'choice' t1 'or' t2" := (tm_choice t1 t2)
  (in custom stlc_tm at level 200,
   t1 custom stlc_tm, t2 custom stlc_tm at level 200) : stlc_scope.

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
  | tm_choice t1 t2 => tm_choice (open_rec k u t1) (open_rec k u t2)
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
      lc_at k (tm_natrec n b s)
    | lc_choice : forall k t1 t2,
      lc_at k t1 -> lc_at k t2 -> lc_at k (tm_choice t1 t2).

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
  | ST_ChoiceLeft : forall t1 t2,
      locally_closed t1 ->
      locally_closed t2 ->
      tm_choice t1 t2 --> t1
  | ST_ChoiceRight : forall t1 t2,
      locally_closed t1 ->
      locally_closed t2 ->
      tm_choice t1 t2 --> t2
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
  | T_Choice : forall Gamma t1 t2 T,
      <{ Gamma |-- $(t1) \in T }> ->
      <{ Gamma |-- $(t2) \in T }> ->
      <{ Gamma |-- choice $(t1) or $(t2) \in T }>
where "<{ Gamma '|--' t '\in' T }>" := (has_type Gamma t T)
  : stlc_scope.

Hint Constructors has_type : core.

Inductive strongly_normalizing : tm -> Prop :=

  | SN_intro : forall t,
      (forall t', t --> t' -> strongly_normalizing t') ->
      strongly_normalizing t.

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
  | tm_zero => tm_zero
  | tm_succ t => tm_succ (msubst rho t)
  | tm_natrec n b s => tm_natrec (msubst rho n) (msubst rho b) (msubst rho s)
  | tm_choice t1 t2 => tm_choice (msubst rho t1) (msubst rho t2)
  end.

Definition proper_substitution (rho : term_substitution) : Prop :=
  forall x, locally_closed (rho x).

Fixpoint strong_value_relation (T : ty) (v : tm) : Prop :=
  value v /\
  match T with
  | Ty_Nat => numeric_value v
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

Definition strong_related_substitution
    (Gamma : context) (rho : term_substitution) : Prop :=
  forall x T,
    Gamma x = Some T ->
    strong_value_relation T (rho x).

Lemma lc_weaken : forall k t, lc_at k t -> forall j, k <= j -> lc_at j t.
Proof.
  intros k t H; induction H; intros j Hj; eauto using lc_at with arith; try lia.
Qed.

Lemma lc_open : forall k t u, lc_at (S k) t -> lc_at k u ->
  lc_at k (open_rec k u t).
Proof.
  intros k t; revert k; induction t; intros k u Ht Hu;
    inversion Ht; subst; simpl; eauto.
  - destruct (Nat.eqb k n) eqn:E; [assumption|].
    constructor. apply Nat.eqb_neq in E; lia.
  - constructor. apply IHt. assumption.
    eapply lc_weaken; eauto; lia.
Qed.

Lemma lc_open_var : forall k t x,
  lc_at (S k) t -> lc_at k (open_rec k (tm_fvar x) t).
Proof. intros; eapply lc_open; eauto. Qed.

Lemma lc_from_open : forall k t x,
  lc_at k (open_rec k (tm_fvar x) t) -> lc_at (S k) t.
Proof.
  intros k t; revert k; induction t; intros k x H; simpl in H;
    try (inversion H; subst; constructor; eauto; fail).
  - destruct (Nat.eqb k n) eqn:E; constructor.
    + apply Nat.eqb_eq in E; lia.
    + inversion H; subst; lia.
Qed.

Lemma fold_max_bound : forall L y, In y L -> y <= fold_right Nat.max 0 L.
Proof.
  induction L as [|a L IH]; simpl; intros y Hy.
  - contradiction.
  - destruct Hy as [->|Hy]; [lia|]. specialize (IH _ Hy); lia.
Qed.

Lemma fresh_not_in : forall L,
  ~ In (S (fold_right Nat.max 0 L)) L.
Proof.
  intros L Hin. apply fold_max_bound in Hin. lia.
Qed.

Lemma typing_lc : forall Gamma t T, has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T H; induction H; unfold locally_closed in *; eauto.
  - constructor. eapply lc_from_open.
    apply (H0 (S (fold_right Nat.max 0 L)) (fresh_not_in L)).
Qed.

Lemma numeric_lc : forall n, numeric_value n -> locally_closed n.
Proof. intros n H; induction H; unfold locally_closed in *; eauto using lc_at. Qed.

Lemma value_lc : forall v, value v -> locally_closed v.
Proof.
  intros v H; destruct H; eauto using numeric_lc; unfold locally_closed; auto.
Qed.

Lemma relation_lc : forall T v, strong_value_relation T v -> locally_closed v.
Proof. intros T v H; destruct T; apply value_lc; exact (proj1 H). Qed.

Lemma numeric_no_step : forall n n', numeric_value n -> ~ step n n'.
Proof.
  intros n n' Hn; revert n'; induction Hn; intros n' Hstep;
    inversion Hstep; subst; eauto.
  eapply IHHn; eauto.
Qed.

Lemma value_no_step : forall v v', value v -> ~ step v v'.
Proof.
  intros v v' Hv Hstep; destruct Hv;
    try solve [inversion Hstep];
    eapply numeric_no_step; eauto.
Qed.

Lemma sn_value : forall v, value v -> strongly_normalizing v.
Proof.
  intros v Hv; constructor; intros v' Hstep.
  exfalso; eapply value_no_step; eauto.
Qed.

Fixpoint fvars (t : tm) : list atom :=
  match t with
  | tm_bvar _ => [] | tm_fvar x => [x]
  | tm_app a b | tm_choice a b => fvars a ++ fvars b
  | tm_abs _ a | tm_succ a => fvars a
  | tm_natrec n b s => fvars n ++ fvars b ++ fvars s
  | _ => []
  end.

Lemma msubst_ext : forall t rho sigma,
  (forall x, In x (fvars t) -> rho x = sigma x) ->
  msubst rho t = msubst sigma t.
Proof.
  induction t; intros rho sigma H; simpl in *; try reflexivity.
  - apply H; auto.
  - f_equal; [apply IHt1|apply IHt2]; intros x Hx; apply H;
      apply in_app_iff; auto.
  - f_equal; apply IHt; auto.
  - f_equal; apply IHt; auto.
  - f_equal; [apply IHt1|apply IHt2|apply IHt3]; intros x Hx;
      apply H; repeat rewrite in_app_iff; tauto.
  - f_equal; [apply IHt1|apply IHt2]; intros x Hx; apply H;
      apply in_app_iff; auto.
Qed.

Lemma lc_open_rec_id : forall k t u, lc_at k t -> open_rec k u t = t.
Proof.
  intros k t; revert k; induction t; intros k u H; inversion H; subst;
    simpl; try reflexivity; try (f_equal; eauto; fail).
  - assert ((k =? n) = false) as E by (apply Nat.eqb_neq; lia).
    rewrite E; reflexivity.
Qed.

Lemma msubst_lc : forall k t rho,
  lc_at k t -> proper_substitution rho -> lc_at k (msubst rho t).
Proof.
  intros k t; revert k; induction t; intros k rho H Hproper;
    inversion H; subst; simpl; eauto using lc_at.
  eapply lc_weaken; [apply Hproper|lia].
Qed.

Lemma msubst_open_rec : forall t k u rho,
  proper_substitution rho ->
  msubst rho (open_rec k u t) =
  open_rec k (msubst rho u) (msubst rho t).
Proof.
  induction t; intros k u rho Hproper; simpl; try reflexivity;
    try (f_equal; eauto; fail).
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. apply lc_open_rec_id.
    eapply lc_weaken; [apply Hproper|lia].
Qed.

Lemma update_proper : forall rho x v,
  proper_substitution rho -> locally_closed v ->
  proper_substitution (subst_update rho x v).
Proof.
  intros rho x v Hr Hv y; unfold subst_update.
  destruct (Nat.eqb x y); auto.
Qed.

Lemma msubst_open_fresh : forall t rho x arg,
  ~ In x (fvars t) -> proper_substitution rho -> locally_closed arg ->
  msubst (subst_update rho x arg) (open t (tm_fvar x)) =
  open (msubst rho t) arg.
Proof.
  intros t rho x arg Hfresh Hr Ha.
  unfold open. rewrite msubst_open_rec by (eapply update_proper; eauto).
  simpl. unfold subst_update. rewrite Nat.eqb_refl.
  f_equal. apply msubst_ext. intros y Hy.
  unfold subst_update. destruct (Nat.eqb x y) eqn:E; auto.
  apply Nat.eqb_eq in E; subst; contradiction.
Qed.

Lemma step_lc : forall t u, t --> u -> locally_closed t -> locally_closed u.
Proof.
  intros t u H; induction H; intros Hlc; unfold locally_closed in *;
    inversion Hlc; subst; eauto using lc_at.
  - inversion H; subst. eapply lc_open; eauto using value_lc.
  - repeat constructor; eauto using lc_at.
    all: inversion H6; assumption.
Qed.

Lemma expr_reduct : forall T t u,
  strong_expression_relation T t -> t --> u ->
  strong_expression_relation T u.
Proof.
  intros T t u [Hlc [Hsn Hvalues]] Hstep.
  split; [eapply step_lc; eauto|].
  split.
  - inversion Hsn; subst; eauto.
  - intros v Hmulti Hv. apply Hvalues; auto.
    eapply multi_step; eauto.
Qed.

Lemma expr_nonvalue : forall T t,
  locally_closed t -> ~ value t ->
  (forall u, t --> u -> strong_expression_relation T u) ->
  strong_expression_relation T t.
Proof.
  intros T t Hlc Hnot Hsuccess.
  split; [exact Hlc|]. split.
  - constructor. intros u Hstep. exact (proj1 (proj2 (Hsuccess u Hstep))).
  - intros v Hmulti Hv. inversion Hmulti; subst.
    + contradiction.
    + destruct (Hsuccess _ H) as [_ [_ Hvals]]. eapply Hvals; eauto.
Qed.

Lemma expr_val : forall T v, strong_value_relation T v ->
  strong_expression_relation T v.
Proof.
  intros T v Hr. split; [eapply relation_lc; eauto|].
  split; [apply sn_value; destruct T; exact (proj1 Hr)|].
  intros w Hmulti Hw. inversion Hmulti; subst; auto.
  exfalso. destruct T; (eapply value_no_step; [exact (proj1 Hr)|exact H]).
Qed.

Lemma expr_choice : forall T a b,
  strong_expression_relation T a -> strong_expression_relation T b ->
  strong_expression_relation T (tm_choice a b).
Proof.
  intros T a b Ha Hb. apply expr_nonvalue.
  - destruct Ha as [Hla _], Hb as [Hlb _].
    unfold locally_closed in *; auto.
  - intros H; inversion H; subst; inversion H0.
  - intros u Hstep; inversion Hstep; subst; auto.
Qed.

Lemma expr_succ : forall t,
  strong_expression_relation Ty_Nat t ->
  strong_expression_relation Ty_Nat (tm_succ t).
Proof.
  intros t [Hlc [Hsn Hvalues]]. induction Hsn as [t Hstep IH].
  split; [unfold locally_closed in *; eauto|]. split.
  - constructor. intros u Hu. inversion Hu; subst.
    apply (proj1 (proj2 (IH _ H0 (step_lc _ _ H0 Hlc)
      (fun v Hm Hv => Hvalues v (multi_step _ _ _ _ H0 Hm) Hv)))).
  - intros v Hmulti Hv. inversion Hmulti; subst.
    + inversion Hv; subst; try solve [inversion H].
      inversion H; subst. split; [assumption|]. constructor.
      exact H1.
    + inversion H; subst.
      apply (proj2 (proj2 (IH _ H2 (step_lc _ _ H2 Hlc)
        (fun w Hm Hw => Hvalues w (multi_step _ _ _ _ H2 Hm) Hw))))
        with (v := v); assumption.
Qed.

Lemma expr_app : forall A B f a,
  strong_expression_relation (Ty_Arrow A B) f ->
  strong_expression_relation A a ->
  strong_expression_relation B (tm_app f a).
Proof.
  intros A B f a [Lf [Sf Rf]]. revert a Lf Rf.
  induction Sf as [f Hsf IHf]; intros a Lf Rf [La [Sa Ra]].
  revert La Ra. induction Sa as [a Hsa IHa]; intros La Ra.
  apply expr_nonvalue.
  - unfold locally_closed in *; auto.
  - intros Hv; inversion Hv; subst;
      match goal with Hn : numeric_value (tm_app _ _) |- _ => inversion Hn end.
  - intros u Hu; inversion Hu; subst.
    + specialize (Rf _ (multi_refl _ _) (v_abs _ _ H1)).
      destruct Rf as [_ [body [Heq Hbody]]].
      inversion Heq; subst.
      destruct (Hbody a (Ra _ (multi_refl _ _) H3)) as [Hlc [Hsn Hvals]].
      exact (conj Hlc (conj Hsn Hvals)).
    + destruct (expr_reduct _ _ _ (conj Lf (conj (SN_intro _ Hsf) Rf)) H1)
        as [Lf' [_ Rf']].
      apply IHf; auto. exact (conj La (conj (SN_intro _ Hsa) Ra)).
    + destruct (expr_reduct _ _ _ (conj La (conj (SN_intro _ Hsa) Ra)) H3)
        as [La' [_ Ra']].
      apply IHa; auto.
Qed.

Lemma expr_rec_value : forall T n, numeric_value n ->
  forall b s,
    strong_expression_relation T b ->
    strong_expression_relation (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
    strong_expression_relation T (tm_natrec n b s).
Proof.
  intros T n Hn. induction Hn as [|n Hn IH]; intros b s Eb Es;
    destruct Eb as [Lb [Sb Rb]]; revert s Lb Rb Es;
    induction Sb as [b Hsb IHb]; intros s Lb Rb [Ls [Ss Rs]];
    revert Ls Rs; induction Ss as [s Hss IHs]; intros Ls Rs.
  all: apply expr_nonvalue.
  all: try (unfold locally_closed in *; eauto using lc_at).
  all: try (intros Hv; inversion Hv; subst;
    match goal with Hnum : numeric_value (tm_natrec _ _ _) |- _ => inversion Hnum end).
  - intros u Hu; inversion Hu; subst.
    + exfalso; eapply numeric_no_step; [constructor|eassumption].
    + destruct (expr_reduct _ _ _ (conj Lb (conj (SN_intro _ Hsb) Rb)) H4)
        as [Lb' [_ Rb']]. apply IHb; auto.
      exact (conj Ls (conj (SN_intro _ Hss) Rs)).
    + destruct (expr_reduct _ _ _ (conj Ls (conj (SN_intro _ Hss) Rs)) H5)
        as [Ls' [_ Rs']]. apply IHs; auto.
    + exact (conj Lb (conj (SN_intro _ Hsb) Rb)).
  - unfold locally_closed in *. constructor; [constructor|exact Lb|exact Ls].
    exact (numeric_lc _ Hn).
  - intros u Hu; inversion Hu; subst.
    + exfalso; eapply numeric_no_step; [constructor; exact Hn|eassumption].
    + destruct (expr_reduct _ _ _ (conj Lb (conj (SN_intro _ Hsb) Rb)) H4)
        as [Lb' [_ Rb']]. apply IHb; auto.
      exact (conj Ls (conj (SN_intro _ Hss) Rs)).
    + destruct (expr_reduct _ _ _ (conj Ls (conj (SN_intro _ Hss) Rs)) H5)
        as [Ls' [_ Rs']]. apply IHs; auto.
    + apply (expr_app T T).
      * apply (expr_app Ty_Nat (Ty_Arrow T T)).
        -- exact (conj Ls (conj (SN_intro _ Hss) Rs)).
        -- apply expr_val. split; [constructor; exact Hn|exact Hn].
      * apply IH; auto.
        -- exact (conj Lb (conj (SN_intro _ Hsb) Rb)).
        -- exact (conj Ls (conj (SN_intro _ Hss) Rs)).
Qed.

Lemma expr_rec : forall T n b s,
  strong_expression_relation Ty_Nat n ->
  strong_expression_relation T b ->
  strong_expression_relation (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  strong_expression_relation T (tm_natrec n b s).
Proof.
  intros T n b s [Ln [Sn Rn]]. revert b s Ln Rn.
  induction Sn as [n Hsn IHn]; intros b s Ln Rn [Lb [Sb Rb]] Es.
  revert s Lb Rb Es.
  induction Sb as [b Hsb IHb]; intros s Lb Rb [Ls [Ss Rs]].
  revert Ls Rs. induction Ss as [s Hss IHs]; intros Ls Rs.
  apply expr_nonvalue.
  - unfold locally_closed in *; eauto using lc_at.
  - intros Hv; inversion Hv; subst;
      match goal with Hnum : numeric_value (tm_natrec _ _ _) |- _ => inversion Hnum end.
  - intros u Hu; inversion Hu; subst.
    + destruct (expr_reduct _ _ _ (conj Ln (conj (SN_intro _ Hsn) Rn)) H2)
        as [Ln' [_ Rn']]. apply IHn; auto.
      * exact (conj Lb (conj (SN_intro _ Hsb) Rb)).
      * exact (conj Ls (conj (SN_intro _ Hss) Rs)).
    + destruct (expr_reduct _ _ _ (conj Lb (conj (SN_intro _ Hsb) Rb)) H4)
        as [Lb' [_ Rb']]. apply IHb; auto.
      exact (conj Ls (conj (SN_intro _ Hss) Rs)).
    + destruct (expr_reduct _ _ _ (conj Ls (conj (SN_intro _ Hss) Rs)) H5)
        as [Ls' [_ Rs']]. apply IHs; auto.
    + exact (conj Lb (conj (SN_intro _ Hsb) Rb)).
    + apply (expr_app T T).
      * apply (expr_app Ty_Nat (Ty_Arrow T T)).
        -- exact (conj Ls (conj (SN_intro _ Hss) Rs)).
        -- apply expr_val. split; [constructor; assumption|assumption].
      * apply expr_rec_value; auto.
        -- exact (conj Lb (conj (SN_intro _ Hsb) Rb)).
        -- exact (conj Ls (conj (SN_intro _ Hss) Rs)).
Qed.

Theorem fundamental : forall Gamma t T,
  has_type Gamma t T ->
  forall rho, proper_substitution rho ->
    strong_related_substitution Gamma rho ->
    strong_expression_relation T (msubst rho t).
Proof.
  intros Gamma t T Htyping; induction Htyping; intros rho Hp Hr; simpl.
  - apply expr_val. apply Hr; assumption.
  - apply expr_val. split.
    + apply v_abs. change (locally_closed (msubst rho (tm_abs T1 t1))).
      eapply msubst_lc; [|exact Hp].
      eapply typing_lc. eapply T_Abs; eauto.
    + exists (msubst rho t1). split; [reflexivity|].
      intros arg Harg.
      pose (x := S (fold_right Nat.max 0 (L ++ fvars t1))).
      assert (HxL : ~ In x L).
      { intro Hin; apply (fresh_not_in (L ++ fvars t1)).
        apply in_app_iff; auto. }
      assert (HxT : ~ In x (fvars t1)).
      { intro Hin; apply (fresh_not_in (L ++ fvars t1)).
        apply in_app_iff; auto. }
      specialize (H0 x HxL (subst_update rho x arg)).
      assert (Harglc : locally_closed arg) by (eapply relation_lc; eauto).
      specialize (H0 (update_proper rho x arg Hp Harglc)).
      assert (Hrel : strong_related_substitution (update Gamma x T1)
        (subst_update rho x arg)).
      { intros y U Hlookup; unfold update, subst_update in *.
        destruct (Nat.eqb x y) eqn:Eq.
        - inversion Hlookup; subst. exact Harg.
        - eapply Hr; eauto. }
      specialize (H0 Hrel).
      rewrite (msubst_open_fresh t1 rho x arg HxT Hp Harglc) in H0.
      exact H0.
  - eapply expr_app; eauto.
  - apply expr_val. split; [constructor|left; reflexivity].
  - apply expr_val. split; [constructor|right; reflexivity].
  - apply expr_val. split; [apply v_nat; constructor|constructor].
  - apply expr_succ. auto.
  - eapply expr_rec; eauto.
  - eapply expr_choice; eauto.
Qed.

Lemma msubst_id : forall t, msubst id_substitution t = t.
Proof.
  induction t; simpl; unfold id_substitution in *;
    try reflexivity; f_equal; auto.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Htyping.
  pose proof (fundamental _ _ _ Htyping id_substitution) as Hfund.
  assert (proper_substitution id_substitution) as Hproper.
  { intros x; unfold id_substitution, locally_closed; auto. }
  assert (strong_related_substitution empty id_substitution) as Hrelated.
  { intros x U Hlookup; discriminate. }
  specialize (Hfund Hproper Hrelated).
  rewrite msubst_id in Hfund. exact (proj1 (proj2 Hfund)).
Qed.

End STLCNormalizationNondeterminismRecursionMediumTask.
