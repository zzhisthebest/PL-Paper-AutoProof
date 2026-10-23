(** STLC call-by-value strong-normalization benchmark, Hard variant.
    System T-style natural-number recursion; no if-then-else or choice. *)

From Stdlib Require Import Arith.PeanoNat Arith.Compare_dec Lists.List Relations.Relation_Definitions Lia.
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

Lemma lc_weaken : forall k t, lc_at k t -> lc_at (S k) t.
Proof.
  intros k t H. induction H; eauto using lc_at; lia.
Qed.

Lemma lc_at_mono : forall k j t, k <= j -> lc_at k t -> lc_at j t.
Proof.
  intros k j t Hkj H. induction Hkj; eauto using lc_weaken.
Qed.

Lemma open_rec_lc : forall k t, lc_at k t -> forall u, open_rec k u t = t.
Proof.
  intros k t H. induction H; intros u; simpl.
  - assert (Nat.eqb k i = false) as Heq by (apply Nat.eqb_neq; lia).
    rewrite Heq. reflexivity.
  - reflexivity.
  - now rewrite IHlc_at1, IHlc_at2.
  - now rewrite IHlc_at.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - now rewrite IHlc_at.
  - now rewrite IHlc_at1, IHlc_at2, IHlc_at3.
Qed.

Fixpoint lc_at_dec (k : nat) (t : tm) : {lc_at k t} + {~ lc_at k t}.
Proof.
  destruct t.
  - destruct (lt_dec n k); [left; constructor; assumption|right; intro H; inversion H; lia].
  - left; constructor.
  - destruct (lc_at_dec k t1), (lc_at_dec k t2).
    + left; eauto.
    + right; intro H; inversion H; contradiction.
    + right; intro H; inversion H; contradiction.
    + right; intro H; inversion H; contradiction.
  - destruct (lc_at_dec (S k) t0).
    + left; constructor; assumption.
    + right; intro H; inversion H; contradiction.
  - left; constructor.
  - left; constructor.
  - left; constructor.
  - destruct (lc_at_dec k t).
    + left; constructor; assumption.
    + right; intro H; inversion H; contradiction.
  - destruct (lc_at_dec k t1) as [H1|H1],
      (lc_at_dec k t2) as [H2|H2], (lc_at_dec k t3) as [H3|H3];
      try (left; constructor; assumption).
    all: right; intro H; inversion H; subst; intuition.
Defined.

Definition locally_closed_dec (t : tm) : {locally_closed t} + {~ locally_closed t} :=
  lc_at_dec 0 t.

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

Fixpoint numeric_value_dec (t : tm) : {numeric_value t} + {~ numeric_value t}.
Proof.
  destruct t.
  - right; intro H; inversion H.
  - right; intro H; inversion H.
  - right; intro H; inversion H.
  - right; intro H; inversion H.
  - right; intro H; inversion H.
  - right; intro H; inversion H.
  - left; constructor.
  - destruct (numeric_value_dec t).
    + left; constructor; assumption.
    + right; intro H; inversion H; contradiction.
  - right; intro H; inversion H.
Defined.

Definition value_dec (t : tm) : {value t} + {~ value t}.
Proof.
  destruct t.
  - right; intro H; inversion H; subst; match goal with Hn : numeric_value _ |- _ => inversion Hn end.
  - right; intro H; inversion H; subst; match goal with Hn : numeric_value _ |- _ => inversion Hn end.
  - right; intro H; inversion H; subst; match goal with Hn : numeric_value _ |- _ => inversion Hn end.
  - destruct (locally_closed_dec (tm_abs t t0)) as [Hlc|Hlc].
    + left; apply v_abs; exact Hlc.
    + right; intro H; inversion H; subst.
      all: try intuition.
      all: inversion H0.
  - left; constructor.
  - left; constructor.
  - left; apply v_nat. constructor.
  - destruct (numeric_value_dec (tm_succ t)); [left; apply v_nat; assumption|right; intro H; inversion H; contradiction].
  - right; intro H; inversion H; subst; inversion H0.
Defined.

Lemma value_lc : forall v, value v -> locally_closed v.
Proof.
  intros v Hv. inversion Hv; subst; try (unfold locally_closed; eauto).
  unfold locally_closed. match goal with
    | Hn : numeric_value _ |- _ => induction Hn; eauto
  end.
Qed.

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

Lemma value_no_step : forall v, value v -> forall v', ~ (v --> v').
Proof.
  intros v Hv. induction Hv; intros v' Hs.
  - inversion Hs.
  - inversion Hs.
  - inversion Hs.
  - revert v' Hs. induction H; intros w Hstep; inversion Hstep; subst; eauto.
Qed.

Lemma app_not_value : forall f a, ~ value (tm_app f a).
Proof.
  intros f a H. inversion H; subst. inversion H0.
Qed.

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

Fixpoint fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_app t1 t2 => fv t1 ++ fv t2
  | tm_abs _ t1 => fv t1
  | tm_true | tm_false | tm_zero => []
  | tm_succ t1 => fv t1
  | tm_natrec n b s => fv n ++ fv b ++ fv s
  end.

Definition term_env := atom -> tm.
Definition env_lc (rho : term_env) : Prop := forall x, locally_closed (rho x).
Definition term_update (rho : term_env) (x : atom) (v : tm) : term_env :=
  fun y => if Nat.eqb x y then v else rho y.

Fixpoint subst (rho : term_env) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => rho x
  | tm_app t1 t2 => tm_app (subst rho t1) (subst rho t2)
  | tm_abs T t1 => tm_abs T (subst rho t1)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (subst rho t1)
  | tm_natrec n b s => tm_natrec (subst rho n) (subst rho b) (subst rho s)
  end.

Lemma subst_open_rec : forall rho, env_lc rho -> forall k u t,
  subst rho (open_rec k u t) = open_rec k (subst rho u) (subst rho t).
Proof.
  intros rho Hlc k u t. revert k. induction t; intros k; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - unfold locally_closed, env_lc in *. rewrite (open_rec_lc k (rho a)).
    + reflexivity.
    + apply lc_at_mono with (k:=0); [lia|apply Hlc].
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2, IHt3. reflexivity.
Qed.

Lemma subst_fresh_update : forall rho x v t,
  ~ In x (fv t) -> subst (term_update rho x v) t = subst rho t.
Proof.
  intros rho x v t. induction t; simpl; intros Hfresh; try reflexivity.
  - unfold term_update. destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply Hfresh. simpl; auto.
    + reflexivity.
  - f_equal.
    + apply IHt1. intro Hin. apply Hfresh. apply in_or_app. left; exact Hin.
    + apply IHt2. intro Hin. apply Hfresh. apply in_or_app. right; exact Hin.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal.
    + apply IHt1. intro Hin. apply Hfresh. apply in_or_app. left; exact Hin.
    + apply IHt2. intro Hin. apply Hfresh. apply in_or_app. right. apply in_or_app. left; exact Hin.
    + apply IHt3. intro Hin. apply Hfresh. apply in_or_app. right. apply in_or_app. right; exact Hin.
Qed.

Fixpoint list_max (xs : list nat) : nat :=
  match xs with [] => 0 | x :: rest => Nat.max x (list_max rest) end.

Lemma in_le_list_max : forall x xs, In x xs -> x <= list_max xs.
Proof.
  intros x xs. induction xs as [|y ys IH]; simpl; intros Hin.
  - contradiction.
  - destruct Hin as [->|Hin]; [apply Nat.le_max_l|].
    eapply Nat.le_trans; [apply IH; exact Hin|apply Nat.le_max_r].
Qed.

Lemma fresh_notin : forall xs : list atom, exists x, ~ In x xs.
Proof.
  intros xs. exists (S (list_max xs)). intro Hin.
  pose proof (in_le_list_max _ _ Hin). lia.
Qed.

Fixpoint reducible (T : ty) : tm -> Prop :=
  match T with
  | Ty_Bool => strongly_normalizing
  | Ty_Nat => strongly_normalizing
  | Ty_Arrow A B => fun t => strongly_normalizing t /\
      forall v, value v -> reducible A v -> reducible B (tm_app t v)
  end.

Definition env_ok (Gamma : context) (rho : term_env) : Prop :=
  (forall x T, Gamma x = Some T -> reducible T (rho x)) /\ env_lc rho.

Lemma env_lc_update : forall rho x v, env_lc rho -> locally_closed v ->
  env_lc (term_update rho x v).
Proof.
  intros rho x v Hrho Hv y. unfold term_update. destruct (Nat.eqb x y).
  - exact Hv.
  - apply Hrho.
Qed.

Lemma env_ok_update : forall Gamma rho x T v,
  env_ok Gamma rho -> reducible T v -> locally_closed v ->
  env_ok (update Gamma x T) (term_update rho x v).
Proof.
  intros Gamma rho x T v [Hred Hlc] Hrv Hlv. split.
  - intros y U Hy. unfold update in Hy. unfold term_update.
    destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. subst y. simpl in Hy. inversion Hy; subst. exact Hrv.
    + eapply Hred; eauto.
  - apply env_lc_update; assumption.
Qed.

Lemma subst_open_fresh : forall rho x v t,
  env_lc rho -> locally_closed v -> ~ In x (fv t) ->
  subst (term_update rho x v) (open t (tm_fvar x)) = open (subst rho t) v.
Proof.
  intros rho x v t Hrho Hv Hfresh. unfold open.
  rewrite (subst_open_rec (term_update rho x v) (env_lc_update rho x v Hrho Hv)
    0 (tm_fvar x) t).
  simpl. rewrite subst_fresh_update; [|exact Hfresh].
  unfold term_update. rewrite Nat.eqb_refl. reflexivity.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> -> strongly_normalizing t.
Proof.
  (* Reducibility is defined on all terms, not just values.  This lets the
     recursive-call case use the induction hypothesis for the predecessor. *)
  set (Red := reducible).
  assert (Red_step : forall T t t', Red T t -> t --> t' -> Red T t').
  { intros T. induction T as [| | A IHA IHB]; simpl; intros t t' H Hs.
    - inversion H; subst; eauto using strongly_normalizing.
    - inversion H; subst; eauto using strongly_normalizing.
    - destruct H as [Hsn Happ]. split.
      + inversion Hsn; subst; eauto using strongly_normalizing.
      + intros v Hv Hr. specialize (Happ v Hv Hr).
        eapply IHIHB; [exact Happ|]. eapply ST_App1; eauto using value_lc.
  }
  assert (Red_SN : forall T t, Red T t -> strongly_normalizing t).
  { intros T; induction T; simpl; intros; tauto. }
  assert (SN_succ : forall t, strongly_normalizing t -> strongly_normalizing (tm_succ t)).
  { intros t Hsn. induction Hsn as [t Hsteps IH].
    apply SN_intro. intros z Hz. inversion Hz; subst. eapply IH; eauto. }
  assert (Red_expand : forall T t, (forall t', t --> t' -> Red T t') ->
      ~ value t -> Red T t).
  { intros T. induction T as [| | A IHA B IHB]; simpl; intros t Hred Hnv.
    - apply SN_intro. intros t' Hs. apply (Hred t' Hs).
    - apply SN_intro. intros t' Hs. apply (Hred t' Hs).
    - split.
      + apply SN_intro. intros t' Hs. destruct (Hred t' Hs) as [Hsn _]. exact Hsn.
      + intros v Hv Hrv.
        eapply IHB.
        * intros z Hz. inversion Hz; subst.
          -- exfalso. apply Hnv. eauto using value.
          -- destruct (Hred _ H1) as [_ Hfun].
             exact (Hfun v Hv Hrv).
          -- exfalso. eapply (value_no_step v Hv); eauto.
        * intro Hval. inversion Hval; subst; inversion H.
    all: try assumption.
  }
  assert (App_compat : forall A B f a, Red (Ty_Arrow A B) f -> Red A a -> Red B (tm_app f a)).
  { intros A B f a Hf Ha.
    cbn [Red reducible] in Hf, Ha.
    destruct Hf as [Hf Hfa].
    revert Hfa a Ha.
    induction Hf as [f Hf IHf]; intros Hfa a Ha.
    induction (Red_SN A a Ha) as [a Hsa IHa].
    destruct (value_dec f) as [Hfv|Hfnv].
    - destruct (value_dec a) as [Hav|Hanv].
      + exact (Hfa a Hav Ha).
      + eapply Red_expand.
        * intros z Hz. inversion Hz; subst.
          -- exfalso. apply Hanv. assumption.
          -- exfalso. eapply (value_no_step f Hfv); eauto.
          -- apply IHa; [assumption|]. eapply Red_step; eauto.
        * apply app_not_value.
    - eapply Red_expand.
      + intros z Hz. inversion Hz; subst.
        * exfalso. apply Hfnv. eauto.
        * apply IHf.
          -- exact H1.
          -- intros v Hv Hr.
             eapply Red_step with (t := tm_app f v) (t' := tm_app t1' v).
             ++ exact (Hfa v Hv Hr).
             ++ apply ST_App1; [exact H1|apply value_lc; exact Hv].
          -- exact Ha.
        * exfalso. apply Hfnv. assumption.
      + apply app_not_value.
  }
  assert (Num_SN : forall n, numeric_value n -> strongly_normalizing n).
  { intros n Hn. apply SN_intro. intros n' Hs.
    exfalso. eapply (value_no_step n (v_nat n Hn) n'); eauto. }
  assert (Rec_not_value : forall n b s, ~ value (tm_natrec n b s)).
  { intros n b s Hv. inversion Hv; subst.
    match goal with Hn : numeric_value (tm_natrec n b s) |- _ => inversion Hn end. }
  assert (Rec_value_red : forall T n b s, numeric_value n -> Red T b -> value b ->
      Red (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s -> value s -> Red T (tm_natrec n b s)).
  { intros T n b s Hn. induction Hn as [|n Hpred IHpred]; intros Hb Hbv Hs Hsv.
    - eapply Red_expand.
      + intros z Hz. inversion Hz; subst.
        * exfalso. eapply (value_no_step tm_zero (v_nat tm_zero nv_zero)); eauto.
        * exfalso. eapply (value_no_step b Hbv); eauto.
        * exfalso. eapply (value_no_step s Hsv); eauto.
        * exact Hb.
      + apply Rec_not_value.
    - eapply Red_expand.
      + intros z Hz. inversion Hz; subst.
        * exfalso. eapply (value_no_step (tm_succ n) (v_nat (tm_succ n) (nv_succ n Hpred))); eauto.
        * exfalso. eapply (value_no_step b Hbv); eauto.
        * exfalso. eapply (value_no_step s Hsv); eauto.
        * eapply App_compat.
          -- eapply App_compat; [exact Hs|apply Num_SN; assumption].
          -- apply IHpred; assumption.
      + apply Rec_not_value.
  }
  (* Reductions in each recursion argument lower its normalization proof.
     Once the arguments are values, the numeric induction above handles the
     primitive unrolling rule. *)
  assert (Rec_red : forall T n b s, Red Ty_Nat n -> Red T b ->
      Red (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s -> Red T (tm_natrec n b s)).
  { intros T n b s Hn.
    cbn [Red reducible] in Hn.
    revert b s.
    induction Hn as [n Hn IHn]; intros b s Hb Hs.
    revert s Hs.
    induction (Red_SN T b Hb) as [b Hbsteps IHb]; intros s Hs.
    induction (Red_SN (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s Hs) as [s Hssteps IHs].
    eapply Red_expand.
    - intros z Hz. inversion Hz; subst.
      + eapply IHn; eauto.
      + eapply IHb; eauto.
      + eapply IHs; eauto.
      + exact Hb.
      + eapply App_compat.
        * eapply App_compat; [exact Hs|apply Num_SN; exact H2].
        * eapply Rec_value_red; eauto.
    - apply Rec_not_value.
  }
  assert (Fund : forall Gamma t T, <{ Gamma |-- t \in T }> ->
      forall rho, env_ok Gamma rho -> Red T (subst rho t)).
  { intros Gamma t T Hty. induction Hty; intros rho Henv.
    - simpl. destruct Henv as [Hred _]. eapply Hred; eauto.
    - simpl. destruct Henv as [Hred Hlc]. split.
      + apply SN_intro. intros z Hz. inversion Hz.
      + intros v Hv Hrv.
        destruct (fresh_notin (L ++ fv t1)) as [x Hx].
        assert (HxL : ~ In x L).
        { intro Hin. apply Hx. apply in_or_app. left; exact Hin. }
        assert (HxF : ~ In x (fv t1)).
        { intro Hin. apply Hx. apply in_or_app. right; exact Hin. }
        pose proof (H0 x HxL (term_update rho x v)
          (env_ok_update Gamma rho x T1 v (conj Hred Hlc) Hrv (value_lc v Hv))) as Hbody.
        rewrite (subst_open_fresh rho x v t1 Hlc (value_lc v Hv) HxF) in Hbody.
        eapply Red_expand.
        * intros z Hz. inversion Hz; subst.
          -- exact Hbody.
          -- exfalso. match goal with Hs : tm_abs _ _ --> _ |- _ => inversion Hs end.
          -- exfalso. eapply (value_no_step v Hv); eauto.
        * apply app_not_value.
    - simpl. eapply App_compat; eauto.
    - simpl. apply SN_intro. intros z Hz. inversion Hz.
    - simpl. apply SN_intro. intros z Hz. inversion Hz.
    - simpl. apply SN_intro. intros z Hz. inversion Hz.
    - simpl. apply SN_succ. eapply Red_SN; eauto.
    - simpl. eapply Rec_red; eauto.
  }
  intros t T Hty.
  assert (Henv : env_ok empty (fun x => tm_fvar x)).
  { split.
    - intros x U Hx. unfold empty in Hx. discriminate.
    - intros x. unfold locally_closed. constructor. }
  pose proof (Fund empty t T Hty (fun x => tm_fvar x) Henv) as Hred.
  assert (Hid : subst (fun x => tm_fvar x) t = t).
  { clear Hty Hred. induction t; simpl; try rewrite IHt; try rewrite IHt1; try rewrite IHt2;
      try rewrite IHt3; reflexivity. }
  rewrite Hid in Hred. eapply Red_SN; exact Hred.
Qed.

End STLCNormalizationRecursionHardTask.
