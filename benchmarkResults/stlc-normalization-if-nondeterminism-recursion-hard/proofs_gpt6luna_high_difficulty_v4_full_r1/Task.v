(** STLC CBV strong-normalization benchmark, Hard variant.
    Features: if-nondeterminism-recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Relations.Relation_Definitions Lia.
Import ListNotations.

Module STLCNormalizationIfNondeterminismRecursionHardTask.

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

(* A reducibility interpretation.  At function types it records the
   behavior of a term when supplied with a reducible argument. *)
Fixpoint reducible (T : ty) (t : tm) : Prop :=
  locally_closed t /\ strongly_normalizing t /\
  match T with
  | Ty_Bool => forall v, multistep t v -> value v -> v = tm_true \/ v = tm_false
  | Ty_Nat => forall v, multistep t v -> value v -> numeric_value v
  | Ty_Arrow A B => forall u, reducible A u -> reducible B (tm_app t u)
  end.

Lemma lc_at_mono : forall k t, lc_at k t -> forall j, k <= j -> lc_at j t.
Proof.
  intros k t H; induction H; intros j Hj.
  - apply lc_bvar; lia.
  - constructor.
  - econstructor; eauto.
  - apply lc_abs. eapply IHlc_at; lia.
  - constructor.
  - constructor.
  - constructor.
  - apply lc_succ. eauto.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
Qed.

Lemma lc_open_rec : forall k t u,
  lc_at (S k) t -> locally_closed u -> lc_at k (open_rec k u t).
Proof.
  intros k t u; revert k; induction t; intros k Hlc Hu;
    inversion Hlc; subst; simpl; eauto using lc_at.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst. eapply lc_at_mono; eauto; lia.
    + constructor. apply Nat.eqb_neq in E; lia.
Qed.

Lemma lc_open : forall t u, lc_at 1 t -> locally_closed u -> locally_closed (open t u).
Proof. intros; unfold locally_closed, open; eapply lc_open_rec; eauto. Qed.

Lemma lc_numeric : forall n, numeric_value n -> locally_closed n.
Proof. intros n N; unfold locally_closed; induction N; eauto. Qed.

Lemma value_lc : forall v, value v -> locally_closed v.
Proof.
  intros v V; inversion V; subst; eauto using lc_numeric.
  all: constructor.
Qed.

Lemma lc_step : forall t t', t --> t' -> locally_closed t -> locally_closed t'.
Proof.
  intros t t' H; induction H; intro L.
  - inversion L; subst. inversion H4; subst.
    eapply lc_open; [eassumption|eapply value_lc; eassumption].
  - inversion L; subst. constructor; [eapply IHstep; eassumption|assumption].
  - inversion L; subst. constructor; [eapply value_lc; eassumption|eapply IHstep; eassumption].
  - inversion L; subst. constructor; eapply IHstep; eassumption.
  - inversion L; subst. constructor; [eapply IHstep; eassumption|assumption|assumption].
  - inversion L; subst. constructor; [assumption|eapply IHstep; eassumption|assumption].
  - inversion L; subst. constructor; [assumption|assumption|eapply IHstep; eassumption].
  - inversion L; subst. assumption.
  - inversion L; subst.
    eapply lc_app.
    + eapply lc_app.
      * eapply value_lc; exact H1.
      * eapply lc_numeric; exact H.
    + eapply lc_rec.
      * eapply lc_numeric; exact H.
      * eapply value_lc; exact H0.
      * eapply value_lc; exact H1.
  - inversion L; subst. assumption.
  - inversion L; subst. assumption.
  - inversion L; subst. constructor; [eapply IHstep; eassumption|assumption|assumption].
  - inversion L; subst. assumption.
  - inversion L; subst. assumption.
Qed.

Definition environment := atom -> option (ty * tm).

Definition env_ok (rho : environment) : Prop :=
  forall x T u, rho x = Some (T,u) -> locally_closed u.

Definition env_satisfies (Gamma : context) (rho : environment) : Prop :=
  forall x T, Gamma x = Some T ->
    exists u, rho x = Some (T,u) /\ locally_closed u /\ reducible T u.

Definition env_update (rho : environment) (x : atom) (T : ty) (u : tm) : environment :=
  fun y => if Nat.eqb x y then Some (T,u) else rho y.

Lemma env_satisfies_update : forall Gamma rho x T u,
  env_satisfies Gamma rho -> locally_closed u -> reducible T u ->
  env_satisfies (update Gamma x T) (env_update rho x T u).
Proof.
  unfold env_satisfies, update, env_update.
  intros Gamma rho x T u Henv Hlc Hr y U Hty.
  destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E; subst. inversion Hty; subst.
    exists u; repeat split; assumption.
  - specialize (Henv y U).
    assert (HG : Gamma y = Some U).
    { exact Hty. }
    destruct (Henv HG) as [v [Ev [Lv Rv]]]. exists v; repeat split; assumption.
Qed.

Fixpoint substitute_env (rho : environment) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => match rho x with Some (_,u) => u | None => tm_fvar x end
  | tm_app t1 t2 => tm_app (substitute_env rho t1) (substitute_env rho t2)
  | tm_abs T t1 => tm_abs T (substitute_env rho t1)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (substitute_env rho t1)
  | tm_natrec n b s => tm_natrec (substitute_env rho n) (substitute_env rho b) (substitute_env rho s)
  | tm_if t1 t2 t3 => tm_if (substitute_env rho t1) (substitute_env rho t2) (substitute_env rho t3)
  | tm_choice t1 t2 => tm_choice (substitute_env rho t1) (substitute_env rho t2)
  end.

Fixpoint freevars (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_app t1 t2 => freevars t1 ++ freevars t2
  | tm_abs _ t1 => freevars t1
  | tm_true | tm_false | tm_zero => []
  | tm_succ t1 => freevars t1
  | tm_natrec n b s => freevars n ++ freevars b ++ freevars s
  | tm_if t1 t2 t3 => freevars t1 ++ freevars t2 ++ freevars t3
  | tm_choice t1 t2 => freevars t1 ++ freevars t2
  end.

Lemma notin_app_l : forall (x : atom) (xs ys : list atom), ~ In x (xs ++ ys) -> ~ In x xs.
Proof. intros x xs ys H Hin; apply H; apply in_or_app; left; exact Hin. Qed.
Lemma notin_app_r : forall (x : atom) (xs ys : list atom), ~ In x (xs ++ ys) -> ~ In x ys.
Proof. intros x xs ys H Hin; apply H; apply in_or_app; right; exact Hin. Qed.

Lemma open_rec_lc_identity : forall d t, lc_at d t -> forall k u,
  d <= k -> open_rec k u t = t.
Proof.
  intros d t H; induction H; intros j u Hle; simpl.
  - destruct (Nat.eqb j i) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
  - reflexivity.
  - f_equal; eauto.
  - f_equal; eauto.
    rewrite (IHlc_at (S j) u) by lia. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
Qed.

Lemma substitute_open_rec : forall k t u rho x T,
  env_ok rho -> locally_closed u -> ~ In x (freevars t) ->
  open_rec k u (substitute_env rho t) =
    substitute_env (env_update rho x T u) (open_rec k (tm_fvar x) t).
Proof.
  intros k t; revert k; induction t; intros k u rho x T Hok Hu Hfresh; simpl in *.
  - destruct (Nat.eqb k n); [unfold env_update; simpl; rewrite Nat.eqb_refl|]; reflexivity.
  - simpl in Hfresh. assert (x <> a) by (intro E; subst; apply Hfresh; simpl; auto).
    destruct (rho a) as [[U v]|] eqn:Erho.
    + unfold env_update. destruct (Nat.eqb x a) eqn:E; [apply Nat.eqb_eq in E; contradiction|].
      simpl. rewrite (open_rec_lc_identity 0 v).
      * rewrite Erho. reflexivity.
      * unfold env_ok in Hok. eapply Hok; exact Erho.
      * lia.
    + unfold env_update. destruct (Nat.eqb x a) eqn:E; [apply Nat.eqb_eq in E; contradiction|].
      rewrite Erho. reflexivity.
  - assert (Hfresh1 : ~ In x (freevars t1)) by (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
    assert (Hfresh2 : ~ In x (freevars t2)) by (intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
    rewrite (IHt1 k u rho x T Hok Hu Hfresh1).
    rewrite (IHt2 k u rho x T Hok Hu Hfresh2). reflexivity.
  - simpl. f_equal. eapply IHt; eauto.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - simpl in Hfresh. f_equal. eapply IHt; eauto.
  - assert (Hn : ~ In x (freevars t1)) by (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
    assert (Hb : ~ In x (freevars t2)) by (intro Hin; apply Hfresh; apply in_or_app; right; apply in_or_app; left; exact Hin).
    assert (Hs : ~ In x (freevars t3)) by (intro Hin; apply Hfresh; apply in_or_app; right; apply in_or_app; right; exact Hin).
    simpl. rewrite (IHt1 k u rho x T Hok Hu Hn), (IHt2 k u rho x T Hok Hu Hb), (IHt3 k u rho x T Hok Hu Hs). reflexivity.
  - assert (H1 : ~ In x (freevars t1)) by (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
    assert (H2 : ~ In x (freevars t2)) by (intro Hin; apply Hfresh; apply in_or_app; right; apply in_or_app; left; exact Hin).
    assert (H3 : ~ In x (freevars t3)) by (intro Hin; apply Hfresh; apply in_or_app; right; apply in_or_app; right; exact Hin).
    simpl. rewrite (IHt1 k u rho x T Hok Hu H1), (IHt2 k u rho x T Hok Hu H2), (IHt3 k u rho x T Hok Hu H3). reflexivity.
  - assert (Hn : ~ In x (freevars t1)) by (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
    assert (Hb : ~ In x (freevars t2)) by (intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
    simpl. rewrite (IHt1 k u rho x T Hok Hu Hn), (IHt2 k u rho x T Hok Hu Hb). reflexivity.
Qed.

Lemma substitute_open : forall t u rho x T,
  env_ok rho -> locally_closed u -> ~ In x (freevars t) ->
  open (substitute_env rho t) u =
    substitute_env (env_update rho x T u) (open t (tm_fvar x)).
Proof. intros; unfold open; apply substitute_open_rec; assumption. Qed.

Lemma env_ok_update : forall rho x T u,
  env_ok rho -> locally_closed u -> env_ok (env_update rho x T u).
Proof.
  unfold env_ok, env_update. intros rho x T u Hok Hu y U v H.
  destruct (Nat.eqb x y) eqn:E.
  - inversion H; subst; exact Hu.
  - eapply Hok; eauto.
Qed.

Lemma lc_substitute_env : forall k t rho,
  lc_at k t -> env_ok rho -> lc_at k (substitute_env rho t).
Proof.
  intros k t rho Hlc; induction Hlc; intros Hok; simpl.
  - constructor; assumption.
  - unfold env_ok in Hok. destruct (rho x) as [[T u]|] eqn:E; [eapply lc_at_mono; [apply Hok in E; exact E|lia]|constructor].
  - constructor; eauto.
  - constructor; eauto.
  - constructor.
  - constructor.
  - constructor.
  - constructor; eauto.
  - constructor; eauto.
  - constructor; eauto.
  - constructor; eauto.
Qed.

Lemma sn_of_step : forall t t', t --> t' -> strongly_normalizing t -> strongly_normalizing t'.
Proof. intros t t' H S. inversion S; eauto. Qed.

Lemma numeric_no_step : forall n n', numeric_value n -> ~ (n --> n').
Proof.
  intros n n' V; revert n'; induction V; intros n' H.
  - inversion H; subst; try congruence.
  - inversion H; subst; try congruence.
    all: try (exfalso; apply (IHV t'); assumption).
Qed.

Inductive rec_arg_rel : tm -> tm -> Prop :=
| rar_step : forall t t', t --> t' -> rec_arg_rel t' t
| rar_pred : forall n, numeric_value n -> rec_arg_rel n (tm_succ n).

Lemma acc_rec_arg_numeric : forall n, numeric_value n -> Acc rec_arg_rel n.
Proof.
  intros n N; induction N as [|m Nm IHm].
  - constructor; intros y Hrel; inversion Hrel; subst; try congruence.
    exfalso. exact (numeric_no_step tm_zero y nv_zero H).
  - constructor; intros y Hrel; inversion Hrel; subst; try congruence.
    all: try (exfalso; exact (numeric_no_step (tm_succ m) y (nv_succ m Nm) H)).
    all: eauto.
Qed.

Lemma acc_rec_arg_sn : forall t, strongly_normalizing t -> Acc rec_arg_rel t.
Proof.
  intros t Sn; induction Sn as [t Next IH].
  constructor; intros y Hrel; inversion Hrel; subst.
  - eapply IH; eauto.
  - eapply acc_rec_arg_numeric; eauto.
Qed.

Inductive rec_state_rel : (tm * tm * tm) -> (tm * tm * tm) -> Prop :=
| rs_n : forall n n' b s, rec_arg_rel n' n -> rec_state_rel (n',b,s) (n,b,s)
| rs_b : forall n b b' s, b --> b' -> rec_state_rel (n,b',s) (n,b,s)
| rs_s : forall n b s s', s --> s' -> rec_state_rel (n,b,s') (n,b,s).

Lemma acc_rec_state : forall n b s,
  Acc rec_arg_rel n -> strongly_normalizing b -> strongly_normalizing s ->
  Acc rec_state_rel (n,b,s).
Proof.
  intros n b s An; revert b s.
  induction An as [n Hn IHn]; intros b s Sb Ss.
  revert s Ss. induction Sb as [b Hb IHb]; intros s Ss.
  induction Ss as [s Hs IHs].
  constructor; intros [[n' b'] s'] Hrel; inversion Hrel; subst.
  - eapply (IHn n' H0 b s); [constructor; exact Hb|constructor; exact Hs].
  - eapply (IHb b' H0 s); [constructor; exact Hs].
  - eapply IHs; eauto.
Qed.

Lemma value_no_step : forall v v', value v -> ~ (v --> v').
Proof.
  intros v v' V H; inversion V; subst; try solve [inversion H].
  eapply numeric_no_step; eauto.
Qed.

Lemma sn_value : forall v, value v -> strongly_normalizing v.
Proof. intros v V; constructor; intros v' H; exfalso; eapply value_no_step; eauto. Qed.

Lemma multi_trans : forall x y z, multistep x y -> multistep y z -> multistep x z.
Proof. intros x y z H; induction H; intros Hz; eauto using multi. Qed.

Lemma multi_cons : forall x y z, x --> y -> multistep y z -> multistep x z.
Proof. intros; econstructor; eauto. Qed.

Lemma multi_no_step_eq : forall t v,
  (forall q, t --> q -> False) -> multistep t v -> v = t.
Proof.
  intros t v Hnone Hmv; induction Hmv; auto.
  exfalso; eapply Hnone; eauto.
Qed.

Lemma reducible_lc : forall T t, reducible T t -> locally_closed t.
Proof. intros T; induction T; intros t R; simpl in R; tauto. Qed.

Lemma reducible_numeral : forall n, numeric_value n -> reducible Ty_Nat n.
Proof.
  intros n N; split; [apply lc_numeric; exact N|].
  split; [apply sn_value; constructor; exact N|].
  intros v Hmv Hv. rewrite (multi_no_step_eq n v (fun q Hq => numeric_no_step n q N Hq) Hmv). exact N.
Qed.

Lemma reducible_true : reducible Ty_Bool tm_true.
Proof.
  split; [constructor; constructor|]. split; [constructor; intros t H; inversion H|].
  intros v Hmv Hv. rewrite (multi_no_step_eq tm_true v (fun q Hq => value_no_step tm_true q v_true Hq) Hmv). auto.
Qed.

Lemma reducible_false : reducible Ty_Bool tm_false.
Proof.
  split; [constructor; constructor|]. split; [constructor; intros t H; inversion H|].
  intros v Hmv Hv. rewrite (multi_no_step_eq tm_false v (fun q Hq => value_no_step tm_false q v_false Hq) Hmv). auto.
Qed.

Lemma sn_succ : forall t, strongly_normalizing t -> strongly_normalizing (tm_succ t).
Proof.
  intros t S; induction S as [t IH].
  constructor; intros t' ST; inversion ST; subst; eauto.
Qed.

Lemma multi_succ_inv : forall t v, multistep (tm_succ t) v ->
  exists u, v = tm_succ u /\ multistep t u.
Proof.
  intros t v H. remember (tm_succ t) as x eqn:Ex in H.
  revert t Ex; induction H; intros t Ex.
  - inversion Ex; subst. exists t; split; [reflexivity|constructor].
  - inversion Ex; subst. inversion H; subst.
    destruct (IHmulti t' eq_refl) as [u [E Hu]].
    exists u; split; [exact E|econstructor; eauto].
Qed.

Lemma reducible_succ : forall t, reducible Ty_Nat t -> reducible Ty_Nat (tm_succ t).
Proof.
  intros t [L [S Can]]. split; [constructor; exact L|].
  split; [apply sn_succ; exact S|].
  intros v Hmv Hv. destruct (multi_succ_inv _ _ Hmv) as [u [E Hu]]. subst.
  inversion Hv; subst. exact H.
Qed.

Lemma reducible_step : forall T t t', reducible T t -> t --> t' -> reducible T t'.
Proof.
  induction T; intros t t' R St.
  - destruct R as [Lc [Sn Can]]. split; [eapply lc_step; eauto|].
    split; [inversion Sn; eauto|].
    intros v Hmv Hv. eapply Can; eauto using multi_cons.
  - destruct R as [Lc [Sn Can]]. split; [eapply lc_step; eauto|].
    split; [inversion Sn; eauto|].
    intros v Hmv Hv. eapply Can; eauto using multi_cons.
  - destruct R as [Lc [Sn Hfun]]. split; [eapply lc_step; eauto|].
    split; [inversion Sn; eauto|].
    intros u Ru. specialize (Hfun u Ru).
    eapply IHT2; [exact Hfun|].
    eapply ST_App1; eauto using reducible_lc.
Qed.

Lemma reducible_sn : forall T t, reducible T t -> strongly_normalizing t.
Proof. intros T; induction T; intros t R; simpl in R; tauto. Qed.

Lemma reducible_nonvalue_expand : forall T t,
  locally_closed t -> ~ value t ->
  (forall t', t --> t' -> reducible T t') -> reducible T t.
Proof.
  induction T as [| |A IHA B IHB]; intros t L Hnv Hred; simpl.
  - split; [exact L|]. split.
    + constructor; intros t' St. specialize (Hred t' St). exact (proj1 (proj2 Hred)).
    + intros v Hmv Hv. destruct Hmv as [v|x y v Hst Htail].
      * exfalso; apply Hnv; subst; exact Hv.
      * exact (proj2 (proj2 (Hred y Hst)) v Htail Hv).
  - split; [exact L|]. split.
    + constructor; intros t' St. specialize (Hred t' St). exact (proj1 (proj2 Hred)).
    + intros v Hmv Hv. destruct Hmv as [v|x y v Hst Htail].
      * exfalso; apply Hnv; subst; exact Hv.
      * exact (proj2 (proj2 (Hred y Hst)) v Htail Hv).
  - split; [exact L|]. split.
    + constructor; intros t' St. specialize (Hred t' St). exact (proj1 (proj2 Hred)).
    + intros u Ru.
      assert (Lu : locally_closed u) by (eapply reducible_lc; exact Ru).
      assert (Lap : locally_closed (tm_app t u)) by (constructor; assumption).
      assert (Hchildren : forall q, tm_app t u --> q -> reducible B q).
      { intros q Sq. inversion Sq; subst.
        - exfalso. apply Hnv. econstructor; eassumption.
        - match goal with
          | Hstep : t --> ?r |- _ =>
              pose proof (Hred r Hstep) as Hr;
              exact (proj2 (proj2 Hr) u Ru)
          end.
        - exfalso. apply Hnv; assumption.
      }
      eapply IHB; [exact Lap| |exact Hchildren].
      intro V; inversion V; subst; try discriminate.
      match goal with Hn : numeric_value (tm_app _ _) |- _ => inversion Hn end.
Qed.

Lemma reducible_choice : forall T t1 t2,
  reducible T t1 -> reducible T t2 -> reducible T (tm_choice t1 t2).
Proof.
  intros T t1 t2 R1 R2.
  assert (L : locally_closed (tm_choice t1 t2)) by (constructor; eapply reducible_lc; eauto).
  apply reducible_nonvalue_expand; [exact L| |].
  - intro V; inversion V; subst; try discriminate.
    match goal with Hn : numeric_value (tm_choice _ _) |- _ => inversion Hn end.
  - intros q Hq. inversion Hq; subst; try (eapply reducible_lc; eauto).
    + exact R1.
    + exact R2.
Qed.

Lemma reducible_if : forall c a b T,
  reducible Ty_Bool c -> reducible T a -> reducible T b ->
  reducible T (tm_if c a b).
Proof.
  intros c a b T Rc Ra Rb.
  destruct Rc as [Lc [Sc Cc]].
  revert a b T Ra Rb Lc Cc.
  induction Sc as [c Next IH]; intros a b T Ra Rb Lc Cc.
  assert (L : locally_closed (tm_if c a b)) by
    (constructor; [exact Lc|eapply reducible_lc; eauto|eapply reducible_lc; eauto]).
  apply reducible_nonvalue_expand; [exact L| |].
  - intro V; inversion V; subst; try discriminate.
    match goal with Hn : numeric_value (tm_if _ _ _) |- _ => inversion Hn end.
  - intros q Hq. inversion Hq; subst.
    + exact Ra.
    + exact Rb.
    + assert (Rc0 : reducible Ty_Bool c) by
        (split; [exact Lc|split; [constructor; exact Next|exact Cc]]).
      pose proof (reducible_step _ _ _ Rc0 H2) as Rc'.
      eapply (IH t1' H2 a b T Ra Rb).
      * eapply reducible_lc; exact Rc'.
      * exact (proj2 (proj2 Rc')).
Qed.

Lemma reducible_abs_intro : forall A B body,
  lc_at 1 body ->
  (forall u, reducible A u -> reducible B (open body u)) ->
  reducible (Ty_Arrow A B) (tm_abs A body).
Proof.
  intros A B body Hbody Hsem.
  split.
  - unfold locally_closed. constructor. exact Hbody.
  - split.
    + constructor; intros q Hq; inversion Hq.
    + intros u Ru.
      assert (Happ : forall z, strongly_normalizing z -> reducible A z ->
          reducible B (tm_app (tm_abs A body) z)).
      { intros z Su Rz; revert Rz.
        induction Su as [z Next IH]; intros Rz.
        assert (Lap : locally_closed (tm_app (tm_abs A body) z)).
        { constructor; [unfold locally_closed; constructor; exact Hbody|eapply reducible_lc; exact Rz]. }
        eapply reducible_nonvalue_expand; [exact Lap| |].
        - intro V; inversion V; subst; try discriminate.
          match goal with Hn : numeric_value (tm_app _ _) |- _ => inversion Hn end.
        - intros q Hq. inversion Hq; subst.
          + apply Hsem; exact Rz.
          + exfalso. eapply value_no_step; [constructor; [unfold locally_closed; constructor; exact Hbody]|eassumption].
          + apply IH.
            * exact H3.
            * eapply reducible_step; eassumption.
      }
      eapply Happ; [apply reducible_sn with (T:=A); exact Ru|exact Ru].
Qed.

Lemma lc_open_fvar_inv : forall k t x,
  lc_at k (open_rec k (tm_fvar x) t) -> lc_at (S k) t.
Proof.
  intros k t x; revert k x; induction t; intros k x H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst. constructor; lia.
    + inversion H; subst. constructor. lia.
  - constructor.
  - inversion H; subst. constructor; [eapply IHt1|eapply IHt2]; eassumption.
  - inversion H; subst. constructor. eapply IHt; eassumption.
  - constructor.
  - constructor.
  - constructor.
  - inversion H; subst. constructor. eapply IHt; eassumption.
  - inversion H; subst. econstructor; [eapply IHt1|eapply IHt2|eapply IHt3]; eassumption.
  - inversion H; subst. econstructor; [eapply IHt1|eapply IHt2|eapply IHt3]; eassumption.
  - inversion H; subst. econstructor; [eapply IHt1|eapply IHt2]; eassumption.
Qed.

Definition fresh_atom (L : list atom) : atom := S (fold_right Nat.max 0 L).

Lemma in_le_fold_max : forall x L, In x L -> x <= fold_right Nat.max 0 L.
Proof.
  intros x L; induction L as [|a L IH]; simpl; intros H; [contradiction|].
  destruct H as [H|H]; subst; [apply Nat.le_max_l|eapply Nat.le_trans; [eapply IH; eauto|apply Nat.le_max_r]].
Qed.

Lemma fresh_atom_notin : forall L, ~ In (fresh_atom L) L.
Proof.
  intros L H. unfold fresh_atom in H. pose proof (in_le_fold_max _ _ H). lia.
Qed.

Lemma typing_locally_closed : forall Gamma t T,
  <{ Gamma |-- t \in T }> -> locally_closed t.
Proof.
  intros Gamma t T Hty; induction Hty.
  - constructor.
  - assert (Hx : ~ In (fresh_atom L) L) by apply fresh_atom_notin.
    pose proof (H0 (fresh_atom L) Hx) as Hopen.
    unfold locally_closed in Hopen.
    eapply lc_abs. eapply lc_open_fvar_inv. exact Hopen.
  - constructor; assumption.
  - constructor.
  - constructor.
  - constructor.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; assumption.
Qed.

Lemma reducible_rec_acc : forall st,
  Acc rec_state_rel st ->
  (forall n b s, st = (n,b,s) -> forall T,
    reducible Ty_Nat n -> reducible T b ->
    reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
    reducible T (tm_natrec n b s)).
Proof.
  intros st Hacc.
  induction Hacc as [st Hnext IH].
  intros n b s E T Rn Rb Rs. subst st.
  simpl.
  assert (L : locally_closed (tm_natrec n b s)).
  { constructor; eapply reducible_lc; eauto. }
  eapply reducible_nonvalue_expand; [exact L| |].
  - intro V; inversion V; subst; try discriminate.
    match goal with Hn : numeric_value (tm_natrec _ _ _) |- _ => inversion Hn end.
  - intros q Hq. inversion Hq; subst.
    + pose proof (rs_n n n' b s (rar_step _ _ H2)) as Hrel.
      exact (IH (n',b,s) Hrel n' b s eq_refl T (reducible_step _ _ _ Rn H2) Rb Rs).
    + match goal with Hstep : b --> ?bp |- _ =>
        pose proof (rs_b n b bp s Hstep) as Hrel;
        exact (IH (n,bp,s) Hrel n bp s eq_refl T Rn (reducible_step _ _ _ Rb Hstep) Rs)
      end.
    + match goal with Hstep : s --> ?sp |- _ =>
        pose proof (rs_s n b s sp Hstep) as Hrel;
        exact (IH (n,b,sp) Hrel n b sp eq_refl T Rn Rb (reducible_step _ _ _ Rs Hstep))
      end.
    + exact Rb.
    + match goal with Hnum : numeric_value n0 |- _ =>
      pose proof (reducible_numeral n0 Hnum) as Rn0;
      pose proof (rs_n (tm_succ n0) n0 b s (rar_pred n0 Hnum)) as Hrel;
      pose proof (IH (n0,b,s) Hrel n0 b s eq_refl T Rn0 Rb Rs) as Rrec;
      pose proof (proj2 (proj2 Rs) n0 Rn0) as Rs1;
      exact (proj2 (proj2 Rs1) (tm_natrec n0 b s) Rrec)
      end.
Qed.

Definition empty_env : environment := fun _ => None.

Lemma env_ok_empty : env_ok empty_env.
Proof. unfold env_ok, empty_env; intros; discriminate. Qed.

Lemma env_satisfies_empty : env_satisfies empty empty_env.
Proof. unfold env_satisfies, empty, empty_env; intros; discriminate. Qed.

Lemma substitute_empty_env : forall t, substitute_env empty_env t = t.
Proof. induction t; simpl; f_equal; eauto. Qed.

Lemma notin_fresh_app : forall L xs,
  ~ In (fresh_atom (L ++ xs)) L /\ ~ In (fresh_atom (L ++ xs)) xs.
Proof.
  intros; split; intro H; apply (fresh_atom_notin (L ++ xs)); apply in_or_app; [left|right]; exact H.
Qed.

Lemma fundamental : forall Gamma t T,
  <{ Gamma |-- t \in T }> -> forall rho,
  env_satisfies Gamma rho -> env_ok rho ->
  reducible T (substitute_env rho t).
Proof.
  intros Gamma t T Hty; induction Hty; intros rho Henv Hok; simpl.
  - destruct (Henv x T H) as [u [E [Lu Ru]]]. rewrite E; exact Ru.
  - pose (x0 := fresh_atom (L ++ freevars t1)).
    destruct (notin_fresh_app L (freevars t1)) as [HxL HxFV].
    assert (Hlcopen : locally_closed (open t1 (tm_fvar x0))).
    { eapply typing_locally_closed. apply H; exact HxL. }
    assert (Hlcbody : lc_at 1 t1).
    { unfold locally_closed in Hlcopen. eapply lc_open_fvar_inv. exact Hlcopen. }
    assert (Hlcsub : lc_at 1 (substitute_env rho t1)).
    { eapply lc_substitute_env; eauto. }
    eapply reducible_abs_intro; [exact Hlcsub|].
    intros u Ru.
    assert (Hsats : env_satisfies (update Gamma x0 T1) (env_update rho x0 T1 u)).
    { eapply env_satisfies_update; [exact Henv|eapply reducible_lc; exact Ru|exact Ru]. }
    assert (Hok' : env_ok (env_update rho x0 T1 u)).
    { eapply env_ok_update; [exact Hok|eapply reducible_lc; exact Ru]. }
    pose proof (H0 x0 HxL (env_update rho x0 T1 u) Hsats Hok') as HbodyR.
    rewrite (substitute_open t1 u rho x0 T1 Hok (reducible_lc T1 u Ru) HxFV).
    exact HbodyR.
  - specialize (IHHty1 rho Henv Hok) as R1.
    specialize (IHHty2 rho Henv Hok) as R2.
    exact (proj2 (proj2 R1) (substitute_env rho t2) R2).
  - apply reducible_true.
  - apply reducible_false.
  - apply reducible_numeral; constructor.
  - apply reducible_succ. apply IHHty; assumption.
  - specialize (IHHty1 rho Henv Hok) as Rn.
    specialize (IHHty2 rho Henv Hok) as Rb.
    specialize (IHHty3 rho Henv Hok) as Rs.
    exact (reducible_rec_acc
      (substitute_env rho n, substitute_env rho b, substitute_env rho s)
      (acc_rec_state _ _ _ (acc_rec_arg_sn _ (reducible_sn _ _ Rn))
        (reducible_sn _ _ Rb) (reducible_sn _ _ Rs))
      (substitute_env rho n) (substitute_env rho b) (substitute_env rho s)
      eq_refl T Rn Rb Rs).
  - eapply reducible_if; [apply IHHty1|apply IHHty2|apply IHHty3]; eauto.
  - apply reducible_choice; [apply IHHty1|apply IHHty2]; assumption.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Hty.
  pose proof (fundamental empty t T Hty empty_env env_satisfies_empty env_ok_empty) as R.
  rewrite substitute_empty_env in R.
  exact (reducible_sn T t R).
Qed.

End STLCNormalizationIfNondeterminismRecursionHardTask.
