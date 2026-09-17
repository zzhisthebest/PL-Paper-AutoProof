(** STLC CBV strong-normalization benchmark, Medium variant.
    Features: if-recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Relations.Relation_Definitions Lia.
Import ListNotations.

Module STLCNormalizationIfRecursionMediumTask.

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

Notation "'if' t1 'then' t2 'else' t3" := (tm_if t1 t2 t3)
  (in custom stlc_tm at level 200,
   t1 custom stlc_tm, t2 custom stlc_tm, t3 custom stlc_tm at level 200) : stlc_scope.

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
  | tm_if t1 t2 t3 => tm_if (open_rec k u t1) (open_rec k u t2) (open_rec k u t3)
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
  | lc_if : forall k t1 t2 t3,
      lc_at k t1 -> lc_at k t2 -> lc_at k t3 -> lc_at k (tm_if t1 t2 t3)
  .

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
  | T_If : forall Gamma t1 t2 t3 T,
      <{ Gamma |-- $(t1) \in Bool }> ->
      <{ Gamma |-- $(t2) \in T }> ->
      <{ Gamma |-- $(t3) \in T }> ->
      <{ Gamma |-- $(tm_if t1 t2 t3) \in T }>
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
  | tm_if t1 t2 t3 => tm_if (msubst rho t1) (msubst rho t2) (msubst rho t3)
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

(* Some elementary facts about the syntax. *)

Fixpoint fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_app t1 t2 => fv t1 ++ fv t2
  | tm_abs _ t1 => fv t1
  | tm_true | tm_false | tm_zero => []
  | tm_succ t1 => fv t1
  | tm_natrec n b s => fv n ++ fv b ++ fv s
  | tm_if t1 t2 t3 => fv t1 ++ fv t2 ++ fv t3
  end.

Lemma lc_weaken : forall k t, lc_at k t -> lc_at (S k) t.
Proof.
  intros k t H; induction H; try constructor; eauto; lia.
Qed.

Lemma lc_from_0 : forall k t, locally_closed t -> lc_at k t.
Proof.
  intros k t H; unfold locally_closed in H.
  induction k; [exact H | apply lc_weaken; exact IHk].
Qed.

Lemma open_rec_lc : forall k u t, lc_at k t -> open_rec k u t = t.
Proof.
  intros k u t H; induction H; simpl; try reflexivity.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E; lia.
    + reflexivity.
  - rewrite IHlc_at1, IHlc_at2; reflexivity.
  - rewrite IHlc_at; reflexivity.
  - rewrite IHlc_at; reflexivity.
  - rewrite IHlc_at1, IHlc_at2, IHlc_at3; reflexivity.
  - rewrite IHlc_at1, IHlc_at2, IHlc_at3; reflexivity.
Qed.

Lemma msubst_open_rec : forall rho,
    proper_substitution rho ->
    forall k u t, lc_at k (msubst rho u) ->
    msubst rho (open_rec k u t) = open_rec k (msubst rho u) (msubst rho t).
Proof.
  intros rho Hr k u t. revert k u.
  induction t as [n|x|t1 IH1 t2 IH2|T t IH| | | |t IH|n IHn b IHb s IHs|t1 IH1 t2 IH2 t3 IH3];
    intros k u Hu; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. apply open_rec_lc. apply lc_from_0. apply Hr.
  - rewrite IH1, IH2; [reflexivity | exact Hu | exact Hu].
  - rewrite IH; [reflexivity | apply lc_weaken; exact Hu].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IH; [reflexivity | exact Hu].
  - rewrite IHn, IHb, IHs; [reflexivity | exact Hu | exact Hu | exact Hu].
  - rewrite IH1, IH2, IH3; [reflexivity | exact Hu | exact Hu | exact Hu].
Qed.

Lemma msubst_update_fresh : forall rho x v t,
    ~ In x (fv t) -> msubst (subst_update rho x v) t = msubst rho t.
Proof.
  intros rho x v t.
  induction t as [n|y|t1 IH1 t2 IH2|T t IH| | | |t IH|n IHn b IHb s IHs|t1 IH1 t2 IH2 t3 IH3];
    simpl; intros H.
  - reflexivity.
  - unfold subst_update. destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E; exfalso; apply H; simpl; left; symmetry; exact E.
    + reflexivity.
  - f_equal.
    + apply IH1. intro Hi; apply H. apply in_or_app; left; exact Hi.
    + apply IH2. intro Hi; apply H. apply in_or_app; right; exact Hi.
  - apply f_equal, IH; exact H.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply f_equal, IH; exact H.
  - assert (Hn : ~ In x (fv n)). { intro Hi; apply H; apply in_or_app; left; exact Hi. }
    assert (Hb : ~ In x (fv b)). { intro Hi; apply H; apply in_or_app; right; apply in_or_app; left; exact Hi. }
    assert (Hs : ~ In x (fv s)). { intro Hi; apply H; apply in_or_app; right; apply in_or_app; right; exact Hi. }
    rewrite (IHn Hn), (IHb Hb), (IHs Hs); reflexivity.
  - assert (H1 : ~ In x (fv t1)). { intro Hi; apply H; apply in_or_app; left; exact Hi. }
    assert (H2 : ~ In x (fv t2)). { intro Hi; apply H; apply in_or_app; right; apply in_or_app; left; exact Hi. }
    assert (H3 : ~ In x (fv t3)). { intro Hi; apply H; apply in_or_app; right; apply in_or_app; right; exact Hi. }
    rewrite (IH1 H1), (IH2 H2), (IH3 H3); reflexivity.
Qed.

Lemma lc_at_open_rec_inv : forall k t u,
    lc_at k (open_rec k u t) -> lc_at (S k) t.
Proof.
  intros k t u. revert k.
  induction t; intros k H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst; constructor; lia.
    + inversion H; constructor; lia.
  - constructor.
  - inversion H; constructor; [apply IHt1 with (k:=k) | apply IHt2 with (k:=k)]; assumption.
  - inversion H; constructor; apply IHt with (k:=S k); assumption.
  - constructor.
  - constructor.
  - constructor.
  - inversion H; constructor; apply IHt with (k:=k); assumption.
  - inversion H; constructor; [apply IHt1 with (k:=k) | apply IHt2 with (k:=k) | apply IHt3 with (k:=k)]; assumption.
  - inversion H; constructor; [apply IHt1 with (k:=k) | apply IHt2 with (k:=k) | apply IHt3 with (k:=k)]; assumption.
Qed.

Lemma lc_open_inv : forall t u, locally_closed (open t u) -> lc_at 1 t.
Proof.
  intros; unfold locally_closed, open in H; eapply lc_at_open_rec_inv; eauto.
Qed.

Fixpoint list_max (xs : list nat) : nat :=
  match xs with
  | [] => 0
  | x :: xs => Nat.max x (list_max xs)
  end.

Lemma in_le_list_max : forall x xs, In x xs -> x <= list_max xs.
Proof.
  intros x xs H; induction xs as [|y ys IH]; simpl in *; [contradiction|].
  destruct H as [E|H]; [subst; apply Nat.le_max_l|].
  apply Nat.le_trans with (list_max ys); [apply IH; exact H|apply Nat.le_max_r].
Qed.

Lemma fresh_list : forall xs : list nat, exists x, ~ In x xs.
Proof.
  intros xs; exists (S (list_max xs)); intro H.
  pose proof (in_le_list_max _ _ H); lia.
Qed.

Lemma lc_at_open_lc : forall k t u,
    lc_at (S k) t -> lc_at k u -> lc_at k (open_rec k u t).
Proof.
  intros k t u. revert k u.
  induction t as [n|x|t1 IH1 t2 IH2|T t IH| | | |t IH|n IHn b IHb s IHs|t1 IH1 t2 IH2 t3 IH3];
    intros k u Ht Hu; simpl.
  - inversion Ht. destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst; exact Hu.
    + constructor; apply Nat.eqb_neq in E; lia.
  - constructor.
  - inversion Ht; constructor; [apply IH1 | apply IH2]; assumption.
  - inversion Ht; constructor; apply IH; [assumption | apply lc_weaken; assumption].
  - constructor.
  - constructor.
  - constructor.
  - inversion Ht; constructor; apply IH; assumption.
  - inversion Ht; constructor; [apply IHn | apply IHb | apply IHs]; assumption.
  - inversion Ht; constructor; [apply IH1 | apply IH2 | apply IH3]; assumption.
Qed.

Lemma typing_lc : forall Gamma t T, <{ Gamma |-- t \in T }> -> locally_closed t.
Proof.
  intros Gamma t T H.
  induction H as
    [ Gamma x T Heq
    | L Gamma T1 T2 t1 Hbody IHbody
    | Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
    | Gamma
    | Gamma
    | Gamma
    | Gamma n Hn IHn
    | Gamma n b s T Hn IHn Hb IHb Hs IHs
    | Gamma t1 t2 t3 T H1 IH1 H2 IH2 H3 IH3 ].
  - constructor.
  - apply lc_abs.
    destruct (fresh_list L) as [x Hx].
    apply (lc_open_inv t1 (tm_fvar x)). apply IHbody; exact Hx.
  - constructor; assumption.
  - constructor.
  - constructor.
  - constructor.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; assumption.
Qed.

Lemma numeric_lc : forall n, numeric_value n -> locally_closed n.
Proof. intros n H; induction H; constructor; assumption. Qed.

Lemma value_lc : forall v, value v -> locally_closed v.
Proof.
  intros v H; destruct H as [T t Hlc | | | n Hn].
  - exact Hlc.
  - constructor.
  - constructor.
  - apply numeric_lc; exact Hn.
Qed.

Lemma abs_open_lc : forall T t v,
    locally_closed (tm_abs T t) -> locally_closed v -> locally_closed (open t v).
Proof.
  intros T t v Habs Hv; unfold locally_closed, open in *.
  inversion Habs; eapply lc_at_open_lc; eauto.
Qed.

Lemma step_lc : forall t t', locally_closed t -> t --> t' -> locally_closed t'.
Proof.
  intros t t' Hlt S; unfold locally_closed in *.
  induction S; inversion Hlt; subst; eauto using abs_open_lc, value_lc, numeric_lc.
  - eapply abs_open_lc; [unfold locally_closed in H; inversion H; eauto | exact H5].
  - apply lc_app.
    + apply lc_app; [eapply value_lc; eauto | eapply numeric_lc; eauto].
    + apply lc_rec; eauto using value_lc, numeric_lc.
  all: unfold locally_closed; eapply numeric_lc; eauto.
Qed.

Lemma numeric_no_step : forall n, numeric_value n -> forall n', ~ n --> n'.
Proof.
  intros n H; induction H as [|n H IH].
  - intros n' S; inversion S.
  - intros n' S; inversion S; eapply IH; eauto.
Qed.

Lemma value_no_step : forall v, value v -> forall v', ~ v --> v'.
Proof.
  intros v H; destruct H as [T t Hlc | | | n Hn]; intros v' S.
  - inversion S.
  - inversion S.
  - inversion S.
  - apply (numeric_no_step n Hn v' S).
Qed.

Lemma value_sn : forall v, value v -> strongly_normalizing v.
Proof.
  intros v H; constructor; intros v' S.
  exfalso; exact (value_no_step v H v' S).
Qed.

Lemma no_value_app : forall f a, ~ value (tm_app f a).
Proof.
  intros f a H; inversion H; subst; try solve [inversion H0]; auto.
Qed.

Lemma sv_lc : forall T v, strong_value_relation T v -> locally_closed v.
Proof.
  intros T v H; destruct T; simpl in H; destruct H as [Hv _]; exact (value_lc v Hv).
Qed.

Lemma sv_sn : forall T v, strong_value_relation T v -> strongly_normalizing v.
Proof. intros T v H; destruct T; simpl in H; destruct H as [Hv _]; exact (value_sn v Hv). Qed.

Lemma sv_to_se : forall T v, strong_value_relation T v ->
    strong_expression_relation T v.
Proof.
  intros T v H; split; [eapply sv_lc; exact H | split; [eapply sv_sn; exact H |]].
  intros v' M Hv'.
  assert (Hv : value v). { destruct T; simpl in H; destruct H as [Hv _]; exact Hv. }
  inversion M as [x | x y z S M0]; subst.
  - exact H.
  - exfalso; exact (value_no_step v Hv y S).
Qed.

Lemma sn_app : forall T1 T2 f a,
    strongly_normalizing f -> strongly_normalizing a ->
    (forall v, f -->* v -> value v -> strong_value_relation (Ty_Arrow T1 T2) v) ->
    (forall v, a -->* v -> value v -> strong_value_relation T1 v) ->
    strongly_normalizing (tm_app f a).
Proof.
  intros T1 T2 f a Hf. revert a. induction Hf as [f Hstep IHf].
  intros a Ha. induction Ha as [a Hstepa IHa].
  intros F A. constructor. intros r R. inversion R; subst.
  - destruct (F _ (@multi_refl tm step _) (v_abs _ _ H1)) as [Hval Hex].
    destruct Hex as [body [Heq Hbody]]. subst.
    inversion Heq; subst.
    destruct (Hbody a (A _ (@multi_refl tm step _) H3)) as [_ [Hsn _]].
    exact Hsn.
  - eapply IHf.
    + exact H1.
    + constructor; exact Hstepa.
    + intros v M Hv; apply F; eauto using multi_step.
    + exact A.
  - eapply IHa.
    + exact H3.
    + exact F.
    + intros v M Hv; apply A; eauto using multi_step.
Qed.

Lemma app_reaches : forall T1 T2 f a,
    (forall v, f -->* v -> value v -> strong_value_relation (Ty_Arrow T1 T2) v) ->
    (forall v, a -->* v -> value v -> strong_value_relation T1 v) ->
    forall r, tm_app f a -->* r -> value r -> strong_value_relation T2 r.
Proof.
  intros T1 T2 f a F A r M Hr.
  remember (tm_app f a) as q eqn:Eq in M.
  revert f a F A Eq.
  induction M as [q | q q' r S M IH]; intros f a F A Eq.
  - subst q; exfalso; exact (no_value_app f a Hr).
  - inversion S; subst.
    + injection H1 as Hft Hav; subst f; subst a.
      assert (Hfv : value (tm_abs T t)). { exact (v_abs T t H). }
      destruct (F _ (@multi_refl tm step _) Hfv) as [Hvv Hex].
      destruct Hex as [body [Heq Hbody]].
      inversion Heq; subst.
      destruct (Hbody v (A _ (@multi_refl tm step _) H0)) as [_ [_ Hres]].
      eapply Hres; eauto.
    + injection H1 as Hft Hat; subst f; subst a.
      refine (IH Hr t1' t2 _ A eq_refl).
      intros w Mw Hw; apply F; eauto using multi_step.
    + injection H1 as Hft Hat; subst f; subst a.
      refine (IH Hr v1 t2' F _ eq_refl).
      intros w Mw Hw; apply A; eauto using multi_step.
Qed.

Lemma se_app : forall T1 T2 f a,
    strong_expression_relation (Ty_Arrow T1 T2) f ->
    strong_expression_relation T1 a ->
    strong_expression_relation T2 (tm_app f a).
Proof.
  intros T1 T2 f a [Hfl [Hfs Hfr]] [Hal [Has Har]].
  split; [constructor; assumption | split].
  - eapply sn_app; eauto.
  - intros v M Hv.
    eapply app_reaches; eauto.
Qed.

Lemma se_from_reducts : forall T t,
    locally_closed t ->
    (forall v, value t -> strong_value_relation T v) ->
    (forall t', t --> t' -> strong_expression_relation T t') ->
    strong_expression_relation T t.
Proof.
  intros T t Hlc Hbase Hred; split; [exact Hlc | split].
  - constructor; intros t' S; destruct (Hred t' S) as [_ [Hs _]]; exact Hs.
  - intros v M Hv.
    remember t as q eqn:Eq in M.
    revert t Hlc Hbase Hred Eq.
    induction M as [q | q q' r S M IH]; intros t Hlc Hbase Hred Eq.
    + subst q; apply Hbase; exact Hv.
    + subst q.
      destruct (Hred q' S) as [_ [_ Hr]].
      eapply Hr; eauto.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  (* Complete the proof of normalization. *)
Qed.

End STLCNormalizationIfRecursionMediumTask.
