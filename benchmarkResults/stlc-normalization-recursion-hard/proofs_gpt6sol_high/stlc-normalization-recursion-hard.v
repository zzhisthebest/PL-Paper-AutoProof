(** STLC call-by-value strong-normalization benchmark, Hard variant.
    System T-style natural-number recursion; no if-then-else or choice. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Relations.Relation_Definitions Lia.
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
where "<{ Gamma '|--' t '\in' T }>" := (has_type Gamma t T)
  : stlc_scope.

Hint Constructors has_type : core.

Inductive strongly_normalizing : tm -> Prop :=
  | SN_intro : forall t,
      (forall t', t --> t' -> strongly_normalizing t') ->
      strongly_normalizing t.

Fixpoint subst (rho : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => rho x
  | tm_app a b => tm_app (subst rho a) (subst rho b)
  | tm_abs T a => tm_abs T (subst rho a)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_zero => tm_zero
  | tm_succ a => tm_succ (subst rho a)
  | tm_natrec n b s => tm_natrec (subst rho n) (subst rho b) (subst rho s)
  end.

Fixpoint fresh (x : atom) (t : tm) : Prop :=
  match t with
  | tm_bvar _ => True
  | tm_fvar y => x <> y
  | tm_app a b => fresh x a /\ fresh x b
  | tm_abs _ a => fresh x a
  | tm_true | tm_false | tm_zero => True
  | tm_succ a => fresh x a
  | tm_natrec n b s => fresh x n /\ fresh x b /\ fresh x s
  end.

Fixpoint fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_app a b => fv a ++ fv b
  | tm_abs _ a => fv a
  | tm_true | tm_false | tm_zero => []
  | tm_succ a => fv a
  | tm_natrec n b s => fv n ++ fv b ++ fv s
  end.

Lemma fresh_fv : forall x t, ~ In x (fv t) -> fresh x t.
Proof.
  intros x t; induction t; simpl; intros H;
    repeat rewrite in_app_iff in *; firstorder congruence.
Qed.

Lemma lc_weaken : forall k k' t, k <= k' -> lc_at k t -> lc_at k' t.
Proof.
  intros k k' t Hle H; revert k' Hle; induction H; intros;
    eauto using lc_at with arith.
Qed.

Lemma open_closed : forall k u t, lc_at k t -> open_rec k u t = t.
Proof.
  intros k u t H; induction H; simpl; try (f_equal; auto); auto.
  destruct (Nat.eqb k i) eqn:E; [apply Nat.eqb_eq in E; lia | reflexivity].
Qed.

Lemma subst_open : forall t rho u k,
  (forall x, locally_closed (rho x)) ->
  subst rho (open_rec k u t) =
  open_rec k (subst rho u) (subst rho t).
Proof.
  induction t; intros rho u k Hr; simpl; try (f_equal; eauto); auto.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. apply open_closed. eapply (lc_weaken 0 k); [lia | apply Hr].
Qed.

Lemma subst_open_closed : forall t rho u,
  (forall x, locally_closed (rho x)) ->
  subst rho (open t u) = open (subst rho t) (subst rho u).
Proof. intros; apply subst_open; assumption. Qed.

Lemma lc_open_inv : forall t k u,
  lc_at k (open_rec k u t) -> lc_at (S k) t.
Proof.
  induction t; intros k u H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. constructor. lia.
    + inversion H; subst. constructor. lia.
  - constructor.
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor. eauto.
  - constructor.
  - constructor.
  - constructor.
  - inversion H; subst. constructor. eauto.
  - inversion H; subst. constructor; eauto.
Qed.

Lemma in_max : forall x l, In x l -> x <= fold_right Nat.max 0 l.
Proof.
  intros x l; induction l as [|a l IH]; simpl; intros H.
  - contradiction.
  - destruct H as [E|H]; subst; [lia | specialize (IH H); lia].
Qed.

Lemma typing_lc : forall Gamma t T, has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T H; unfold locally_closed; induction H; eauto using lc_at.
  - constructor. set (x := S (fold_right Nat.max 0 L)).
    apply lc_open_inv with (u:=tm_fvar x).
    apply H0. unfold x. intro K. pose proof (in_max _ _ K). lia.
Qed.

Lemma lc_subst : forall k t rho,
  lc_at k t ->
  (forall x, locally_closed (rho x)) ->
  lc_at k (subst rho t).
Proof.
  intros k t rho H; induction H; intros Hr; simpl;
    eauto using lc_at.
  eapply (lc_weaken 0 k); [lia | apply Hr].
Qed.

Lemma fresh_subst : forall x t rho v,
  fresh x t ->
  subst (fun y => if Nat.eqb x y then v else rho y) t = subst rho t.
Proof.
  intros x t; induction t; intros rho v H; simpl in *;
    try (f_equal; intuition eauto); auto.
  destruct (Nat.eqb x a) eqn:E; auto.
  apply Nat.eqb_eq in E. congruence.
Qed.

Lemma subst_open_fresh : forall x t rho v,
  fresh x t ->
  (forall y, locally_closed (rho y)) ->
  locally_closed v ->
  subst (fun y => if Nat.eqb x y then v else rho y)
    (open t (tm_fvar x)) = open (subst rho t) v.
Proof.
  intros x t rho v Hf Hr Hv.
  unfold open.
  rewrite subst_open by (intro y; destruct (Nat.eqb x y); auto).
  simpl. rewrite Nat.eqb_refl.
  rewrite fresh_subst by exact Hf. reflexivity.
Qed.

Lemma multi_trans : forall a b c, a -->* b -> b -->* c -> a -->* c.
Proof.
  intros a b c H; induction H; intros Hbc; eauto using multi.
Qed.

Lemma multi_app1 : forall a a' b,
  a -->* a' -> locally_closed b -> tm_app a b -->* tm_app a' b.
Proof.
  intros a a' b H; induction H; intros Hb; eauto using multi, step.
Qed.

Lemma multi_app2 : forall v b b',
  value v -> b -->* b' -> tm_app v b -->* tm_app v b'.
Proof.
  intros v b b' Hv H; induction H; eauto using multi, step.
Qed.

Lemma multi_succ : forall n n',
  n -->* n' -> tm_succ n -->* tm_succ n'.
Proof. intros n n' H; induction H; eauto using multi, step. Qed.

Lemma multi_rec_arg : forall n n' b s,
  n -->* n' -> locally_closed b -> locally_closed s ->
  tm_natrec n b s -->* tm_natrec n' b s.
Proof.
  intros n n' b s H; induction H; intros; eauto using multi, step.
Qed.

Lemma multi_rec_base : forall n b b' s,
  numeric_value n -> b -->* b' -> locally_closed s ->
  tm_natrec n b s -->* tm_natrec n b' s.
Proof.
  intros n b b' s Hn H; induction H; intros; eauto using multi, step.
Qed.

Lemma multi_rec_step : forall n b s s',
  numeric_value n -> value b -> s -->* s' ->
  tm_natrec n b s -->* tm_natrec n b s'.
Proof.
  intros n b s s' Hn Hb H; induction H; eauto using multi, step.
Qed.

Fixpoint reducible (T : ty) (t : tm) : Prop :=
  locally_closed t /\
  exists v, t -->* v /\ value v /\
    match T with
    | Ty_Bool => v = tm_true \/ v = tm_false
    | Ty_Nat => numeric_value v
    | Ty_Arrow A B =>
        forall u, reducible A u -> reducible B (tm_app v u)
    end.

Lemma red_lc : forall T t, reducible T t -> locally_closed t.
Proof. intros T t H; destruct T; simpl in H; tauto. Qed.

Lemma red_eval : forall T t, reducible T t ->
  exists v, t -->* v /\ value v /\
    match T with
    | Ty_Bool => v = tm_true \/ v = tm_false
    | Ty_Nat => numeric_value v
    | Ty_Arrow A B => forall u, reducible A u -> reducible B (tm_app v u)
    end.
Proof. intros T t H; destruct T; simpl in H; tauto. Qed.

Lemma red_expand : forall T t u,
  locally_closed t -> t -->* u -> reducible T u -> reducible T t.
Proof.
  intros T t u Hlc Hsteps Hred.
  destruct T; simpl in *;
    destruct Hred as [_ [v [Hu [Hv Hval]]]];
    split; auto; exists v; repeat split; eauto using multi_trans.
Qed.

Lemma numeric_lc : forall n, numeric_value n -> locally_closed n.
Proof. unfold locally_closed; induction 1; eauto using lc_at. Qed.

Lemma value_lc : forall v, value v -> locally_closed v.
Proof.
  intros v H; inversion H; subst; try assumption;
    try (apply numeric_lc; assumption); unfold locally_closed; eauto using lc_at.
Qed.

Lemma red_value : forall T v,
  value v ->
  (match T with
   | Ty_Bool => v = tm_true \/ v = tm_false
   | Ty_Nat => numeric_value v
   | Ty_Arrow A B => forall u, reducible A u -> reducible B (tm_app v u)
   end) ->
  reducible T v.
Proof.
  intros T v Hv Hsem. destruct T; simpl in *;
    (split; [apply value_lc; assumption |
      exists v; repeat split; eauto using multi]).
Qed.

Lemma red_app : forall A B f u,
  reducible (Ty_Arrow A B) f ->
  reducible A u ->
  reducible B (tm_app f u).
Proof.
  intros A B f u [Hf [v [Hsteps [Hv Hsem]]]] Hu.
  eapply red_expand with (u:=tm_app v u).
  - unfold locally_closed; apply lc_app; [exact Hf | exact (red_lc A u Hu)].
  - apply multi_app1; auto. exact (red_lc A u Hu).
  - apply Hsem; assumption.
Qed.

Lemma red_succ : forall n, reducible Ty_Nat n ->
  reducible Ty_Nat (tm_succ n).
Proof.
  intros n [Hlc [v [Hsteps [Hv Hnv]]]].
  split; [constructor; assumption|].
  exists (tm_succ v). repeat split.
  - apply multi_succ; assumption.
  - constructor. constructor. assumption.
  - constructor. assumption.
Qed.

Lemma red_nat_value : forall n,
  numeric_value n -> reducible Ty_Nat n.
Proof.
  intros n Hn. apply red_value; eauto using value.
Qed.

Lemma red_rec_values : forall T n b s,
  numeric_value n -> reducible T b ->
  reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  reducible T (tm_natrec n b s).
Proof.
  intros T n b s Hn; revert b s;
    induction Hn as [|n Hn IH]; intros b s Hb Hs.
  - pose proof (red_lc T b Hb) as Hbl.
    destruct (red_eval T b Hb) as [bv [Hbs [Hbv Hbsem]]].
    destruct Hs as [Hsl [sv [Hss [Hsv Hssem]]]].
    eapply red_expand with (u:=bv).
    + unfold locally_closed; apply lc_rec;
        [apply lc_zero | exact Hbl | exact Hsl].
    + eapply multi_trans.
      * apply multi_rec_base; eauto using numeric_value.
      * eapply multi_trans.
        -- apply multi_rec_step; eauto using numeric_value.
        -- eapply multi_step; [apply ST_RecZero; assumption|apply multi_refl].
    + apply red_value; assumption.
  - pose proof (red_lc T b Hb) as Hbl.
    destruct (red_eval T b Hb) as [bv [Hbs [Hbv Hbsem]]].
    destruct Hs as [Hsl [sv [Hss [Hsv Hssem]]]].
    assert (Hb' : reducible T bv) by (apply red_value; assumption).
    assert (Hs' : reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) sv)
      by (apply red_value; assumption).
    assert (Hr : reducible T (tm_natrec n bv sv))
      by (apply IH; assumption).
    assert (Happ : reducible T
      (tm_app (tm_app sv n) (tm_natrec n bv sv))).
    { apply red_app with (A:=T).
      - apply red_app with (A:=Ty_Nat); auto using red_nat_value.
      - exact Hr. }
    eapply red_expand with
      (u:=tm_app (tm_app sv n) (tm_natrec n bv sv)).
    + unfold locally_closed; apply lc_rec;
        [apply lc_succ; apply numeric_lc; exact Hn | exact Hbl | exact Hsl].
    + eapply multi_trans.
      * apply multi_rec_base; eauto using numeric_value.
      * eapply multi_trans.
        -- apply multi_rec_step; eauto using numeric_value, value.
        -- eapply multi_step;
             [apply ST_RecSucc; eauto using numeric_value|apply multi_refl].
    + exact Happ.
Qed.

Lemma red_rec : forall T n b s,
  reducible Ty_Nat n -> reducible T b ->
  reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  reducible T (tm_natrec n b s).
Proof.
  intros T n b s [Hnl [nv [Hns [Hnv Hnum]]]] Hb Hs.
  pose proof (red_lc T b Hb) as Hbl.
  destruct (red_eval T b Hb) as [bv [Hbs [Hbv Hbsem]]].
  destruct Hs as [Hsl [sv [Hss [Hsv Hssem]]]].
  eapply red_expand with (u:=tm_natrec nv bv sv).
  - unfold locally_closed; apply lc_rec; assumption.
  - eapply multi_trans with (b:=tm_natrec nv b s).
    + apply multi_rec_arg; auto.
    + eapply multi_trans with (b:=tm_natrec nv bv s).
      * apply multi_rec_base; auto.
      * apply multi_rec_step; auto.
  - apply red_rec_values; auto; apply red_value; assumption.
Qed.

Lemma not_in_max : forall x l,
  x = S (fold_right Nat.max 0 l) -> ~ In x l.
Proof.
  intros x l E H. subst x. pose proof (in_max _ _ H). lia.
Qed.

Lemma update_env : forall Gamma x T rho v,
  (forall y U, Gamma y = Some U -> reducible U (rho y)) ->
  reducible T v ->
  forall y U, update Gamma x T y = Some U ->
    reducible U (if Nat.eqb x y then v else rho y).
Proof.
  intros Gamma x T rho v Henv Hv y U H.
  unfold update in H. destruct (Nat.eqb x y) eqn:E.
  - inversion H; subst. exact Hv.
  - apply Henv. exact H.
Qed.

Theorem fundamental : forall Gamma t T,
  has_type Gamma t T ->
  forall rho,
    (forall x, locally_closed (rho x)) ->
    (forall x U, Gamma x = Some U -> reducible U (rho x)) ->
    reducible T (subst rho t).
Proof.
  intros Gamma t T Hty; induction Hty; intros rho Hcl Henv; simpl.
  - apply Henv. assumption.
  - set (a := S (fold_right Nat.max 0 (L ++ fv t1))).
    assert (HaL : ~ In a L).
    { unfold a. intro K. eapply not_in_max; [reflexivity|].
      apply in_or_app. left. exact K. }
    assert (Haf : fresh a t1).
    { apply fresh_fv. unfold a. intro K.
      eapply not_in_max; [reflexivity|].
      apply in_or_app. right. exact K. }
    assert (Habs : locally_closed (tm_abs T1 (subst rho t1))).
    { change (locally_closed (subst rho (tm_abs T1 t1))).
      apply lc_subst; auto.
      eapply typing_lc. apply T_Abs with (L:=L). exact H. }
    assert (Hval : value (tm_abs T1 (subst rho t1)))
      by (constructor; exact Habs).
    change (reducible (Ty_Arrow T1 T2) (tm_abs T1 (subst rho t1))).
    apply red_value; auto.
    intros u Hu.
    destruct (red_eval T1 u Hu) as [v [Huv [Hvv Hvsem]]].
    assert (Hv : reducible T1 v) by (apply red_value; assumption).
    set (rho' := fun y => if Nat.eqb a y then v else rho y).
    assert (Hcl' : forall y, locally_closed (rho' y)).
    { intro y. unfold rho'. destruct (Nat.eqb a y); auto using value_lc. }
    assert (Henv' : forall y U,
      update Gamma a T1 y = Some U -> reducible U (rho' y)).
    { intros y U Hy. unfold rho'. eapply update_env; eauto. }
    specialize (H0 a HaL rho' Hcl' Henv').
    unfold rho' in H0.
    erewrite subst_open_fresh in H0; eauto using value_lc.
    eapply red_expand with (u:=open (subst rho t1) v).
    + unfold locally_closed. apply lc_app; [exact Habs | exact (red_lc T1 u Hu)].
    + eapply multi_trans with (b:=tm_app (tm_abs T1 (subst rho t1)) v).
      * apply multi_app2; assumption.
      * eapply multi_step; [apply ST_AppAbs; assumption | apply multi_refl].
    + exact H0.
  - apply red_app with (A:=T1); eauto.
  - change (reducible Ty_Bool tm_true).
    apply red_value; eauto using value.
  - change (reducible Ty_Bool tm_false).
    apply red_value; eauto using value.
  - change (reducible Ty_Nat tm_zero).
    apply red_nat_value. constructor.
  - change (reducible Ty_Nat (tm_succ (subst rho n))).
    apply red_succ. eauto.
  - change (reducible T (tm_natrec (subst rho n) (subst rho b) (subst rho s))).
    apply red_rec; eauto.
Qed.

Lemma numeric_no_step : forall n t,
  numeric_value n -> n --> t -> False.
Proof.
  intros n z Hn; revert z; induction Hn; intros z Hs;
    inversion Hs; subst; eauto.
Qed.

Lemma value_no_step : forall v t,
  value v -> v --> t -> False.
Proof.
  intros v t Hv Hs. inversion Hv; subst; inversion Hs; subst;
    eauto using numeric_no_step.
Qed.

Lemma step_deterministic : forall t a b,
  t --> a -> t --> b -> a = b.
Proof.
  intros t a b H1; revert b; induction H1; intros b0 H2;
    inversion H2; subst; eauto;
    try solve [exfalso; eapply value_no_step; eauto];
    try solve [exfalso; eapply numeric_no_step; eauto];
    try solve [f_equal; eauto].
  all: try solve [
    exfalso;
    match goal with
    | Hs : step ?v _, Hv : value ?v |- _ =>
        eapply value_no_step; [exact Hv | exact Hs]
    | Hs : step (tm_abs ?T ?u) _, Hl : locally_closed (tm_abs ?T ?u) |- _ =>
        eapply value_no_step; [constructor; exact Hl | exact Hs]
    | Hs : step ?n _, Hn : numeric_value ?n |- _ =>
        eapply numeric_no_step; [exact Hn | exact Hs]
    | Hs : step tm_zero _ |- _ =>
        eapply numeric_no_step; [constructor | exact Hs]
    | Hs : step (tm_succ ?n) _, Hn : numeric_value ?n |- _ =>
        eapply numeric_no_step; [constructor; exact Hn | exact Hs]
    end].
Qed.

Lemma eval_SN : forall t v,
  t -->* v -> value v -> strongly_normalizing t.
Proof.
  intros t v Hsteps; induction Hsteps; intros Hv.
  - constructor. intros t' Hs. exfalso. eapply value_no_step; eauto.
  - constructor. intros t' Hs.
    assert (t' = y) by (eapply step_deterministic; eauto).
    subst. apply IHHsteps. exact Hv.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> -> strongly_normalizing t.
Proof.
  intros t T Hty.
  pose (rho := fun x : atom => tm_fvar x).
  assert (Hcl : forall x, locally_closed (rho x)).
  { intro x. unfold rho, locally_closed. constructor. }
  assert (Henv : forall x U, empty x = Some U -> reducible U (rho x)).
  { intros x U H. discriminate. }
  pose proof (fundamental empty t T Hty rho Hcl Henv) as Hred.
  assert (Heq : subst rho t = t).
  { clear Hty Hred. unfold rho. induction t; simpl; congruence. }
  rewrite Heq in Hred.
  destruct (red_eval T t Hred) as [v [Hsteps [Hv _]]].
  eapply eval_SN; eauto.
Qed.

End STLCNormalizationRecursionHardTask.
