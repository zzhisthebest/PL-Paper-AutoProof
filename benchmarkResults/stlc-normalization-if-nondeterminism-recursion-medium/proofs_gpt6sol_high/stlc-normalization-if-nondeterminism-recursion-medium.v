(** STLC CBV strong-normalization benchmark, Medium variant.
    Features: if-nondeterminism-recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Relations.Relation_Definitions Lia.
Import ListNotations.

Module STLCNormalizationIfNondeterminismRecursionMediumTask.

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
  | tm_if : tm -> tm -> tm -> tm
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

Notation "'if' t1 'then' t2 'else' t3" := (tm_if t1 t2 t3)
  (in custom stlc_tm at level 200,
   t1 custom stlc_tm, t2 custom stlc_tm, t3 custom stlc_tm at level 200) : stlc_scope.
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
  | tm_if t1 t2 t3 => tm_if (open_rec k u t1) (open_rec k u t2) (open_rec k u t3)
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
  | lc_if : forall k t1 t2 t3,
      lc_at k t1 -> lc_at k t2 -> lc_at k t3 -> lc_at k (tm_if t1 t2 t3)
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
  | T_If : forall Gamma t1 t2 t3 T,
      <{ Gamma |-- $(t1) \in Bool }> ->
      <{ Gamma |-- $(t2) \in T }> ->
      <{ Gamma |-- $(t3) \in T }> ->
      <{ Gamma |-- $(tm_if t1 t2 t3) \in T }>
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
  | tm_if t1 t2 t3 => tm_if (msubst rho t1) (msubst rho t2) (msubst rho t3)
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

Lemma lc_at_mono : forall t k j,
  lc_at k t -> k <= j -> lc_at j t.
Proof.
  intros t k j H. revert j. induction H; intros j Hj;
    try solve [econstructor; eauto; lia].
  constructor. apply IHlc_at. lia.
Qed.

Lemma value_lc : forall v, value v -> locally_closed v.
Proof.
  intros v Hv. destruct Hv as [T t Hlc | | | n Hn].
  - exact Hlc.
  - constructor.
  - constructor.
  - induction Hn; constructor; auto.
Qed.

Lemma open_lc_at : forall t k u,
  lc_at k t -> open_rec k u t = t.
Proof.
  intros t k u H. revert u. induction H; intros u; simpl; try (f_equal; eauto); auto.
  destruct (Nat.eqb k i) eqn:E; auto. apply Nat.eqb_eq in E. lia.
Qed.

Lemma open_lc : forall t u,
  locally_closed t -> open t u = t.
Proof. intros; apply open_lc_at; assumption. Qed.

Lemma lc_at_open : forall t k u,
  lc_at (S k) t -> locally_closed u -> lc_at k (open_rec k u t).
Proof.
  induction t; intros k u H Hu; inversion H; subst; simpl;
    try solve [econstructor; eauto].
  destruct (Nat.eqb k n) eqn:E.
  - apply lc_at_mono with (k:=0); auto; lia.
  - constructor. apply Nat.eqb_neq in E. lia.
Qed.

Lemma lc_at_from_open : forall t k u,
  lc_at k (open_rec k u t) -> lc_at (S k) t.
Proof.
  induction t; intros k u H; simpl in H;
    try solve [inversion H; subst; econstructor; eauto].
  destruct (Nat.eqb k n) eqn:E.
  - constructor. apply Nat.eqb_eq in E. lia.
  - inversion H; subst. constructor. lia.
Qed.

Definition fresh (L : list atom) := S (fold_right Nat.max 0 L).

Lemma fresh_notin : forall L, ~ In (fresh L) L.
Proof.
  assert (B : forall L x, In x L -> x <= fold_right Nat.max 0 L).
  { induction L as [|a L IH]; simpl; intros x E.
    - contradiction.
    - destruct E as [E|E]; [subst; lia | specialize (IH x E); lia]. }
  intros L E. unfold fresh in E. apply B in E. lia.
Qed.

Lemma typing_lc : forall Gamma t T,
  has_type Gamma t T -> locally_closed t.
Proof.
  unfold locally_closed. induction 1; try solve [econstructor; eauto].
  constructor. eapply lc_at_from_open with (u:=tm_fvar (fresh L)).
  apply H0. apply fresh_notin.
Qed.

Lemma sn_step : forall t t',
  strongly_normalizing t -> t --> t' -> strongly_normalizing t'.
Proof. intros t t' [t0 H] Hs. eauto. Qed.

Lemma numeric_no_step : forall n t,
  numeric_value n -> ~ n --> t.
Proof.
  intros n t Hn. revert t. induction Hn; intros u Hs;
    inversion Hs; subst; eauto.
  eapply IHHn; eauto.
Qed.

Lemma value_no_step : forall v t,
  value v -> ~ v --> t.
Proof.
  intros v t Hv Hs. destruct Hv as [T b Hlc | | | n Hn];
    try solve [inversion Hs].
  eapply numeric_no_step; eauto.
Qed.

Lemma value_sn : forall v, value v -> strongly_normalizing v.
Proof.
  intros v Hv. constructor. intros t Hs.
  exfalso. exact (value_no_step v t Hv Hs).
Qed.

Lemma step_lc : forall t t',
  locally_closed t -> t --> t' -> locally_closed t'.
Proof.
  intros t t' Hlc Hs. revert Hlc. unfold locally_closed in *.
  induction Hs; intros Hlc; inversion Hlc; subst;
    eauto 8 using lc_at_open, value_lc, lc_at.
  - inversion H4; subst. eapply lc_at_open; eauto.
  - repeat constructor; eauto; inversion H6; auto.
Qed.

Lemma expr_step : forall T t t',
  strong_expression_relation T t -> t --> t' ->
  strong_expression_relation T t'.
Proof.
  intros T t t' [Hlc [Hsn Hres]] Hs.
  split; [eapply step_lc; eauto|].
  split; [eapply sn_step; eauto|].
  intros v Hmulti Hv. apply Hres; auto.
  eapply multi_step; eauto.
Qed.

Lemma expr_value : forall T v,
  strong_value_relation T v -> strong_expression_relation T v.
Proof.
  intros T v H. assert (Hv : value v) by (destruct T; exact (proj1 H)).
  split; [apply value_lc; auto|].
  split; [apply value_sn; auto|].
  intros w Hmulti Hw. inversion Hmulti; subst; auto.
  exfalso. exact (value_no_step v y Hv H0).
Qed.

Lemma expr_from_steps : forall T t,
  locally_closed t -> ~ value t ->
  (forall t', t --> t' -> strong_expression_relation T t') ->
  strong_expression_relation T t.
Proof.
  intros T t Hlc Hnv Hnext. split; auto. split.
  - constructor. intros t' Hs. apply Hnext in Hs. exact (proj1 (proj2 Hs)).
  - intros v Hmulti Hv. inversion Hmulti; subst.
    + contradiction.
    + apply Hnext in H. destruct H as [_ [_ Hres]]. apply Hres; auto.
Qed.

Lemma vr_value : forall T v,
  strong_value_relation T v -> value v.
Proof. intros T v H. destruct T; exact (proj1 H). Qed.

Lemma vr_lc : forall T v,
  strong_value_relation T v -> locally_closed v.
Proof. intros T v H. apply value_lc, (vr_value _ _ H). Qed.

Lemma expr_result : forall T t v,
  strong_expression_relation T t -> t -->* v -> value v ->
  strong_value_relation T v.
Proof. intros T t v [_ [_ H]] Hm Hv. eauto. Qed.

Lemma msubst_lc_at : forall t k rho,
  lc_at k t -> proper_substitution rho -> lc_at k (msubst rho t).
Proof.
  induction t; intros k rho Hlc Hproper; inversion Hlc; subst; simpl;
    try solve [econstructor; eauto].
  apply lc_at_mono with (k:=0); auto. apply Hproper. lia.
Qed.

Lemma msubst_lc : forall t rho,
  locally_closed t -> proper_substitution rho ->
  locally_closed (msubst rho t).
Proof. intros; eapply msubst_lc_at; eauto. Qed.

Fixpoint free_atoms (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_app a b => free_atoms a ++ free_atoms b
  | tm_abs _ b => free_atoms b
  | tm_true | tm_false | tm_zero => []
  | tm_succ a => free_atoms a
  | tm_natrec a b c | tm_if a b c =>
      free_atoms a ++ free_atoms b ++ free_atoms c
  | tm_choice a b => free_atoms a ++ free_atoms b
  end.

Lemma msubst_open_rec : forall t k x rho v,
  proper_substitution rho ->
  ~ In x (free_atoms t) ->
  msubst (subst_update rho x v) (open_rec k (tm_fvar x) t) =
  open_rec k v (msubst rho t).
Proof.
  induction t; intros k x rho v Hproper Hfresh; simpl in *.
  - destruct (Nat.eqb k n); simpl; auto. unfold subst_update.
    rewrite Nat.eqb_refl. reflexivity.
  - unfold subst_update. destruct (Nat.eqb x a) eqn:E; auto.
    apply Nat.eqb_eq in E; subst. exfalso. apply Hfresh. auto.
    symmetry. apply open_lc_at. eapply lc_at_mono; [apply Hproper|lia].
  - rewrite IHt1, IHt2; auto; intro H;
      apply Hfresh; apply in_or_app; auto.
  - rewrite IHt; auto.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IHt; auto.
  - rewrite IHt1, IHt2, IHt3; auto; intro H;
      apply Hfresh; repeat rewrite in_app_iff; tauto.
  - rewrite IHt1, IHt2, IHt3; auto; intro H;
      apply Hfresh; repeat rewrite in_app_iff; tauto.
  - rewrite IHt1, IHt2; auto; intro H;
      apply Hfresh; apply in_or_app; auto.
Qed.

Lemma related_lc : forall Gamma rho x T,
  strong_related_substitution Gamma rho -> Gamma x = Some T ->
  locally_closed (rho x).
Proof. intros. eapply vr_lc. eapply H; eauto. Qed.

Lemma related_update : forall Gamma rho x T v,
  strong_related_substitution Gamma rho ->
  strong_value_relation T v ->
  strong_related_substitution (update Gamma x T) (subst_update rho x v).
Proof.
  intros Gamma rho x T v Hrel Hv y U Hlookup.
  unfold update in Hlookup; unfold subst_update.
  destruct (Nat.eqb x y) eqn:E; auto.
  inversion Hlookup; subst; auto.
Qed.

Lemma proper_update : forall rho x v,
  proper_substitution rho -> locally_closed v ->
  proper_substitution (subst_update rho x v).
Proof.
  intros rho x v Hproper Hlc y. unfold subst_update.
  destruct (Nat.eqb x y); auto.
Qed.

Lemma expr_from_steps_value : forall T t,
  locally_closed t ->
  (forall t', t --> t' -> strong_expression_relation T t') ->
  (value t -> strong_value_relation T t) ->
  strong_expression_relation T t.
Proof.
  intros T t Hlc Hnext Hvalue. split; auto. split.
  - constructor. intros t' Hs. apply Hnext in Hs. exact (proj1 (proj2 Hs)).
  - intros v Hmulti Hv. inversion Hmulti; subst.
    + apply Hvalue; auto.
    + apply Hnext in H. apply (expr_result T y v H); auto.
Qed.

Lemma expr_choice : forall T a b,
  strong_expression_relation T a -> strong_expression_relation T b ->
  strong_expression_relation T (tm_choice a b).
Proof.
  intros T a b Ha Hb. apply expr_from_steps with (T:=T).
  - destruct Ha as [H _], Hb as [H' _]. constructor; auto.
  - intros H. inversion H; subst; try discriminate.
    match goal with Hn : numeric_value _ |- _ => inversion Hn end.
  - intros t Hs. inversion Hs; subst; auto.
Qed.

Lemma expr_succ : forall n,
  strong_expression_relation Ty_Nat n ->
  strong_expression_relation Ty_Nat (tm_succ n).
Proof.
  intros n Hn. remember (proj1 (proj2 Hn)) as Hsn eqn:E.
  clear E. induction Hsn as [n Hstep IH] in Hn |- *.
  apply expr_from_steps_value.
  - constructor. exact (proj1 Hn).
  - intros t Hs. inversion Hs; subst.
    apply IH; [eauto | eapply expr_step; eauto].
  - intros Hv. split; auto. inversion Hv; subst; try discriminate.
    assumption.
Qed.

Lemma expr_if : forall T c a b,
  strong_expression_relation Ty_Bool c ->
  strong_expression_relation T a -> strong_expression_relation T b ->
  strong_expression_relation T (tm_if c a b).
Proof.
  intros T c a b Hc Ha Hb.
  remember (proj1 (proj2 Hc)) as Hsn eqn:E.
  clear E. induction Hsn as [c Hstep IH] in Hc |- *.
  apply expr_from_steps with (T:=T).
  - constructor; [exact (proj1 Hc) | exact (proj1 Ha) | exact (proj1 Hb)].
  - intros Hv. inversion Hv; subst; try discriminate.
    match goal with Hn : numeric_value _ |- _ => inversion Hn end.
  - intros t Hs. inversion Hs; subst; eauto.
    apply IH; [eauto | eapply expr_step; eauto].
Qed.

Lemma expr_app : forall A B f a,
  strong_expression_relation (Ty_Arrow A B) f ->
  strong_expression_relation A a ->
  strong_expression_relation B (tm_app f a).
Proof.
  intros A B f a Hf Ha.
  remember (proj1 (proj2 Hf)) as Hsnf eqn:Ef.
  clear Ef. induction Hsnf as [f Hstepf IHf] in a, Hf, Ha |- *.
  remember (proj1 (proj2 Ha)) as Hsna eqn:Ea.
  clear Ea. induction Hsna as [a Hstepa IHa] in Hf, Ha |- *.
  apply expr_from_steps with (T:=B).
  - constructor; [exact (proj1 Hf) | exact (proj1 Ha)].
  - intros Hv. inversion Hv; subst; try discriminate.
    match goal with Hn : numeric_value _ |- _ => inversion Hn end.
  - intros t Hs. inversion Hs; subst.
    + pose proof (expr_result (Ty_Arrow A B) (tm_abs T t0) (tm_abs T t0) Hf
        (multi_refl step (tm_abs T t0)) (v_abs T t0 H1)) as Hfun.
      pose proof (expr_result A a a Ha (multi_refl step a) H3) as Harg.
      simpl in Hfun. destruct Hfun as [_ [body [Heq Hbody]]].
      inversion Heq; subst. destruct (Hbody a Harg) as [Hlc [Hsn Hres]].
      exact (conj Hlc (conj Hsn Hres)).
    + apply IHf; [eauto | eapply expr_step; eauto | exact Ha].
    + apply IHa; [eauto | exact Hf | eapply expr_step; eauto].
Qed.

Lemma numeric_dec : forall n,
  {numeric_value n} + {~ numeric_value n}.
Proof.
  induction n; try (right; intro H; inversion H; fail).
  - left. constructor.
  - destruct IHn as [H|H].
    + left. constructor; auto.
    + right. intro Hv. inversion Hv; subst; auto.
  all: right; intro Hv; inversion Hv.
Qed.

Lemma expr_nat_value : forall n,
  numeric_value n -> strong_expression_relation Ty_Nat n.
Proof.
  intros n Hn. apply expr_value. simpl. split; [constructor|]; auto.
Qed.

Lemma expr_rec_values : forall T n b s,
  numeric_value n ->
  strong_expression_relation T b ->
  strong_expression_relation (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  strong_expression_relation T (tm_natrec n b s).
Proof.
  intros T n b s Hnum Hb Hs.
  induction Hnum as [|n Hnum IHn] in b, s, Hb, Hs |- *.
  - remember (proj1 (proj2 Hb)) as Hsnb eqn:Eb. clear Eb.
    induction Hsnb as [b Hstepb IHb] in Hb, s, Hs |- *.
    remember (proj1 (proj2 Hs)) as Hsns eqn:Es. clear Es.
    induction Hsns as [s Hsteps IHs] in Hb, Hs |- *.
    apply expr_from_steps with (T:=T).
    + constructor; [constructor | exact (proj1 Hb) | exact (proj1 Hs)].
    + intros Hv. inversion Hv; subst; try discriminate.
      match goal with Hn : numeric_value _ |- _ => inversion Hn end.
    + intros t Hr. inversion Hr; subst.
      * exfalso. eapply numeric_no_step with (n:=tm_zero); [constructor | eassumption].
      * apply IHb; [eauto | eapply expr_step; eauto | exact Hs].
      * apply IHs; [eauto | exact Hb | eapply expr_step; eauto].
      * exact Hb.
  - remember (proj1 (proj2 Hb)) as Hsnb eqn:Eb. clear Eb.
    induction Hsnb as [b Hstepb IHb] in Hb, s, Hs |- *.
    remember (proj1 (proj2 Hs)) as Hsns eqn:Es. clear Es.
    induction Hsns as [s Hsteps IHs] in Hb, Hs |- *.
    apply expr_from_steps with (T:=T).
    + constructor; [constructor; apply value_lc; constructor; auto |
        exact (proj1 Hb) | exact (proj1 Hs)].
    + intros Hv. inversion Hv; subst; try discriminate.
      match goal with Hn : numeric_value _ |- _ => inversion Hn end.
    + intros t Hr. inversion Hr; subst.
      * exfalso. eapply numeric_no_step with (n:=tm_succ n);
          [constructor; exact Hnum | eassumption].
      * apply IHb; [eauto | eapply expr_step; eauto | exact Hs].
      * apply IHs; [eauto | exact Hb | eapply expr_step; eauto].
      * apply expr_app with (A:=T).
        -- apply expr_app with (A:=Ty_Nat); auto.
           apply expr_nat_value; auto.
        -- apply IHn; auto.
Qed.

Lemma expr_rec : forall T n b s,
  strong_expression_relation Ty_Nat n ->
  strong_expression_relation T b ->
  strong_expression_relation (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  strong_expression_relation T (tm_natrec n b s).
Proof.
  intros T n b s Hn Hb Hs.
  remember (proj1 (proj2 Hn)) as Hsnn eqn:En. clear En.
  induction Hsnn as [n Hstepn IHn] in Hn |- *.
  destruct (numeric_dec n) as [Hnum|Hnum].
  - apply expr_rec_values; auto.
  - apply expr_from_steps with (T:=T).
    + constructor; [exact (proj1 Hn) | exact (proj1 Hb) | exact (proj1 Hs)].
    + intros Hv. inversion Hv; subst; try discriminate.
      match goal with Hnv : numeric_value _ |- _ => inversion Hnv end.
    + intros t Hr. inversion Hr; subst; try contradiction.
      apply IHn; [eauto | eapply expr_step; eauto].
      all: exfalso; apply Hnum; constructor; eauto.
Qed.

Theorem fundamental : forall Gamma t T,
  has_type Gamma t T ->
  forall rho,
    proper_substitution rho ->
    strong_related_substitution Gamma rho ->
    strong_expression_relation T (msubst rho t).
Proof.
  intros Gamma t T Hty. induction Hty; intros rho Hproper Hrel; simpl.
  - apply expr_value. apply Hrel; auto.
  - assert (Hlc : locally_closed (tm_abs T1 (msubst rho t1))).
    { change (locally_closed (msubst rho (tm_abs T1 t1))).
      apply msubst_lc; auto. eapply typing_lc. econstructor; eauto. }
    apply expr_value. simpl. split; [constructor; exact Hlc |].
    exists (msubst rho t1). split; [reflexivity|].
    intros arg Harg.
    set (x := fresh (L ++ free_atoms t1)).
    assert (HxL : ~ In x L).
    { intro Hin. unfold x in *. apply (fresh_notin (L ++ free_atoms t1)).
      apply in_or_app; auto. }
    assert (HxF : ~ In x (free_atoms t1)).
    { intro Hin. unfold x in *. apply (fresh_notin (L ++ free_atoms t1)).
      apply in_or_app; auto. }
    specialize (H0 x HxL (subst_update rho x arg)).
    assert (Hbody : strong_expression_relation T2
      (msubst (subst_update rho x arg) (open t1 (tm_fvar x)))).
    { apply H0.
      - apply proper_update; auto. apply vr_lc with (T:=T1); auto.
      - apply related_update; auto. }
    unfold open in Hbody. rewrite msubst_open_rec in Hbody; auto.
  - eapply expr_app; eauto.
  - apply expr_value. simpl. split; [constructor | auto].
  - apply expr_value. simpl. split; [constructor | auto].
  - apply expr_value. simpl. split; [constructor; constructor | constructor].
  - apply expr_succ; auto.
  - eapply expr_rec; eauto.
  - eapply expr_if; eauto.
  - eapply expr_choice; eauto.
Qed.

Lemma msubst_id : forall t, msubst id_substitution t = t.
Proof. induction t; simpl; f_equal; auto. Qed.

Lemma proper_id : proper_substitution id_substitution.
Proof. intros x. constructor. Qed.

Lemma related_empty : strong_related_substitution empty id_substitution.
Proof. intros x T H. discriminate. Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Hty.
  pose proof (fundamental empty t T Hty id_substitution proper_id related_empty)
    as Hrel.
  rewrite msubst_id in Hrel. exact (proj1 (proj2 Hrel)).
Qed.

End STLCNormalizationIfNondeterminismRecursionMediumTask.
