(** STLC call-by-value strong-normalization benchmark, Medium variant.
    System T-style natural-number recursion; no if-then-else or choice. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Relations.Relation_Definitions Lia.
Import ListNotations.

Module STLCNormalizationRecursionMediumTask.

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
  end.

Definition proper_substitution (rho : term_substitution) : Prop :=
  forall x, locally_closed (rho x).

Fixpoint value_relation (T : ty) (v : tm) : Prop :=
  value v /\
  match T with
  | Ty_Nat => numeric_value v
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

Definition related_substitution
    (Gamma : context) (rho : term_substitution) : Prop :=
  forall x T, Gamma x = Some T -> value_relation T (rho x).

Fixpoint fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ => [] | tm_fvar x => [x]
  | tm_app a b => fv a ++ fv b
  | tm_abs _ b => fv b
  | tm_true | tm_false | tm_zero => []
  | tm_succ n => fv n
  | tm_natrec n b s => fv n ++ fv b ++ fv s
  end.

Lemma lc_weaken : forall t k j, lc_at k t -> k <= j -> lc_at j t.
Proof.
  induction t; intros k j H Hle; inversion H; subst; constructor; eauto; try lia.
  - eapply IHt; eauto; lia.
Qed.

Lemma lc_open_rec : forall t k u, lc_at (S k) t -> lc_at k u ->
  lc_at k (open_rec k u t).
Proof.
  induction t; intros k u H Hu; inversion H; subst; simpl; eauto.
  - destruct (Nat.eqb k n) eqn:E; auto. apply Nat.eqb_neq in E.
    constructor; lia.
  - constructor. eapply IHt; eauto. eapply lc_weaken; eauto; lia.
Qed.

Lemma lc_open : forall t u, lc_at 1 t -> locally_closed u ->
  locally_closed (open t u).
Proof. intros; eapply lc_open_rec; eauto. Qed.

Lemma numeric_lc : forall n, numeric_value n -> locally_closed n.
Proof. intros n H; induction H; constructor; auto. Qed.

Lemma value_lc : forall v, value v -> locally_closed v.
Proof.
  intros v H; inversion H; subst; auto; try constructor.
  eapply numeric_lc; eauto.
Qed.

Lemma in_max : forall (l : list nat) x, In x l -> x <= fold_right Nat.max 0 l.
Proof.
  induction l; intros x H; simpl in *; [contradiction|].
  destruct H as [H|H]; subst; [lia|].
  specialize (IHl x H); lia.
Qed.

Lemma fresh : forall l : list nat, ~ In (S (fold_right Nat.max 0 l)) l.
Proof. intros l H; pose proof (in_max l _ H); lia. Qed.

Lemma lc_from_open_rec : forall t k x,
  ~ In x (fv t) -> lc_at k (open_rec k (tm_fvar x) t) -> lc_at (S k) t.
Proof.
  induction t; intros k x Hfresh Hlc; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst; constructor; lia.
    + inversion Hlc; subst; constructor; lia.
  - constructor.
  - inversion Hlc; subst; constructor.
    + eapply IHt1; eauto. intro Hin; apply Hfresh; apply in_app_iff; auto.
    + eapply IHt2; eauto. intro Hin; apply Hfresh; apply in_app_iff; auto.
  - inversion Hlc; subst; constructor; eapply IHt; eauto.
  - constructor.
  - constructor.
  - constructor.
  - inversion Hlc; subst; constructor; eapply IHt; eauto.
  - inversion Hlc; subst; constructor.
    + eapply IHt1; eauto. intro Hin; apply Hfresh; apply in_app_iff; auto.
    + eapply IHt2; eauto. intro Hin; apply Hfresh; apply in_app_iff; right; apply in_app_iff; auto.
    + eapply IHt3; eauto. intro Hin; apply Hfresh; apply in_app_iff; right; apply in_app_iff; auto.
Qed.

Lemma typing_lc : forall Gamma t T, has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T H; induction H; unfold locally_closed in *; eauto.
  - set (x := S (fold_right Nat.max 0 (L ++ fv t1))).
    assert (Hx : ~ In x L). { intro Hin; apply (fresh (L ++ fv t1)); apply in_app_iff; auto. }
    assert (Hxf : ~ In x (fv t1)). { intro Hin; apply (fresh (L ++ fv t1)); apply in_app_iff; auto. }
    specialize (H0 x Hx). constructor.
    eapply lc_from_open_rec; eauto.
Qed.

Lemma msubst_lc : forall t k rho,
  lc_at k t -> proper_substitution rho -> lc_at k (msubst rho t).
Proof.
  induction t; intros k rho Hlc Hp; inversion Hlc; subst; simpl; eauto.
  - eapply lc_weaken; [apply Hp|lia].
Qed.

Lemma open_rec_closed : forall t k u, lc_at k t -> open_rec k u t = t.
Proof.
  induction t; intros k u Hlc; inversion Hlc; subst; simpl; auto.
  - destruct (Nat.eqb k n) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
  - rewrite IHt1, IHt2; auto.
  - rewrite IHt; auto.
  - rewrite IHt; auto.
  - rewrite IHt1, IHt2, IHt3; auto.
Qed.

Lemma msubst_open_fresh : forall t k x rho u,
  ~ In x (fv t) -> proper_substitution rho ->
  msubst (subst_update rho x u) (open_rec k (tm_fvar x) t) =
  open_rec k u (msubst rho t).
Proof.
  induction t; intros k x rho u Hfresh Hp; simpl in *; auto.
  - destruct (Nat.eqb k n); simpl; auto. unfold subst_update. now rewrite Nat.eqb_refl.
  - assert (x <> a) by (intro E; subst; apply Hfresh; auto).
    unfold subst_update. apply Nat.eqb_neq in H. rewrite H.
    symmetry. apply open_rec_closed. eapply lc_weaken; [apply Hp|lia].
  - rewrite IHt1, IHt2; auto; intro Hin; apply Hfresh; apply in_app_iff; auto.
  - rewrite IHt; auto.
  - rewrite IHt; auto.
  - rewrite IHt1, IHt2, IHt3; auto.
    + intro Hin; apply Hfresh; apply in_app_iff; right; apply in_app_iff; right; exact Hin.
    + intro Hin; apply Hfresh; apply in_app_iff; right; apply in_app_iff; left; exact Hin.
    + intro Hin; apply Hfresh; apply in_app_iff; left; exact Hin.
Qed.

Lemma multi_trans : forall a b c, a -->* b -> b -->* c -> a -->* c.
Proof. intros a b c H; induction H; intros Hbc; auto. econstructor; eauto. Qed.

Lemma multi_app1 : forall a a' b, a -->* a' -> locally_closed b ->
  tm_app a b -->* tm_app a' b.
Proof. intros a a' b H; induction H; intros Hb; [constructor|eapply multi_step; [apply ST_App1; eauto|eauto]]. Qed.

Lemma multi_app2 : forall a b b', value a -> b -->* b' ->
  tm_app a b -->* tm_app a b'.
Proof. intros a b b' Ha H; induction H; [constructor|eapply multi_step; [apply ST_App2; eauto|eauto]]. Qed.

Lemma multi_succ : forall a b, a -->* b -> tm_succ a -->* tm_succ b.
Proof. intros a b H; induction H; [constructor|eapply multi_step; [apply ST_Succ; eauto|eauto]]. Qed.

Lemma multi_rec_arg : forall n n' b s, n -->* n' ->
  locally_closed b -> locally_closed s ->
  tm_natrec n b s -->* tm_natrec n' b s.
Proof. intros n n' b s H; induction H; intros Hb Hs; [constructor|eapply multi_step; [apply ST_RecArg; eauto|eauto]]. Qed.

Lemma multi_rec_base : forall n b b' s, numeric_value n -> b -->* b' ->
  locally_closed s -> tm_natrec n b s -->* tm_natrec n b' s.
Proof. intros n b b' s Hn H; induction H; intros Hs; [constructor|eapply multi_step; [apply ST_RecBase; eauto|eauto]]. Qed.

Lemma multi_rec_step : forall n b s s', numeric_value n -> value b -> s -->* s' ->
  tm_natrec n b s -->* tm_natrec n b s'.
Proof. intros n b s s' Hn Hb H; induction H; [constructor|eapply multi_step; [apply ST_RecStep; eauto|eauto]]. Qed.

Lemma vr_value : forall T v, value_relation T v -> value v.
Proof. intros T v H; destruct T; simpl in H; tauto. Qed.

Lemma er_of_value : forall T v, value_relation T v -> expression_relation T v.
Proof.
  intros T v H. split; [apply value_lc; eapply vr_value; eauto|].
  exists v; split; [constructor|exact H].
Qed.

Lemma er_step_back : forall T t t', locally_closed t -> t --> t' ->
  expression_relation T t' -> expression_relation T t.
Proof.
  intros T t t' Hlc Hs [_ [v [Hm Hv]]]. split; auto.
  exists v; split; [econstructor; eauto|exact Hv].
Qed.

Lemma er_multi_back : forall T t t', locally_closed t -> t -->* t' ->
  expression_relation T t' -> expression_relation T t.
Proof.
  intros T t t' Hlc Hm [_ [v [Hm2 Hv]]]. split; auto.
  exists v; split; [eapply multi_trans; eauto|exact Hv].
Qed.

Lemma er_app : forall A B f a,
  expression_relation (Ty_Arrow A B) f -> expression_relation A a ->
  expression_relation B (tm_app f a).
Proof.
  intros A B f a [Hflc [vf [Hfm Hfv]]] [Halc [va [Ham Hav]]].
  simpl in Hfv. destruct Hfv as [Hfval [body [Heq Hbody]]]. subst vf.
  destruct (Hbody va Hav) as [Hopen [vr [Hrm Hrv]]].
  split; [constructor; auto|].
  exists vr; split; auto.
  eapply multi_trans. { apply multi_app1; eauto. }
  eapply multi_trans. { apply multi_app2; eauto. }
  eapply multi_step with (y:=open body va). { apply ST_AppAbs; [apply value_lc; exact Hfval|eapply vr_value; eauto]. }
  exact Hrm.
Qed.

Lemma er_succ : forall n, expression_relation Ty_Nat n ->
  expression_relation Ty_Nat (tm_succ n).
Proof.
  intros n [Hlc [v [Hm [Hv Hnv]]]].
  split; [constructor; auto|].
  exists (tm_succ v); split.
  - apply multi_succ; exact Hm.
  - split; [constructor; constructor; exact Hnv|constructor; exact Hnv].
Qed.

Lemma er_rec_values : forall T n b s,
  numeric_value n -> value_relation T b ->
  value_relation (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  expression_relation T (tm_natrec n b s).
Proof.
  intros T n b s Hn Hb Hs; revert b s Hb Hs; induction Hn; intros b s Hb Hs.
  - split. { constructor; [constructor|apply value_lc; eapply vr_value; eauto|apply value_lc; eapply vr_value; eauto]. }
    exists b; split; auto. eapply multi_step; [apply ST_RecZero; eapply vr_value; eauto|constructor].
  - assert (Hnat : value_relation Ty_Nat t).
    { split; [constructor; exact Hn|exact Hn]. }
    assert (Hrec := IHHn b s Hb Hs).
    assert (Happ := er_app _ _ _ _ (er_app _ _ _ _ (er_of_value _ _ Hs)
      (er_of_value _ _ Hnat)) Hrec).
    eapply er_step_back; [|apply ST_RecSucc; [exact Hn|eapply vr_value; eauto|eapply vr_value; eauto]|exact Happ].
    unfold locally_closed; apply lc_rec; [apply numeric_lc; constructor; exact Hn|apply value_lc; eapply vr_value; eauto|apply value_lc; eapply vr_value; eauto].
Qed.

Lemma er_rec : forall T n b s,
  expression_relation Ty_Nat n -> expression_relation T b ->
  expression_relation (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  expression_relation T (tm_natrec n b s).
Proof.
  intros T n b s [Hnlc [nv [Hnm [Hnval Hnum]]]]
    [Hblc [bv [Hbm Hbval]]] [Hslc [sv [Hsm Hsval]]].
  assert (Hr := er_rec_values T nv bv sv Hnum Hbval Hsval).
  destruct Hr as [_ [v [Hrm Hrv]]].
  split; [constructor; auto|]. exists v; split; auto.
  eapply multi_trans. { eapply multi_rec_arg; eauto. }
  eapply multi_trans. { eapply multi_rec_base; eauto. }
  eapply multi_trans. { eapply multi_rec_step; eauto. eapply vr_value; eauto. }
  exact Hrm.
Qed.

Lemma related_update : forall Gamma rho x A arg,
  related_substitution Gamma rho -> value_relation A arg ->
  related_substitution (update Gamma x A) (subst_update rho x arg).
Proof.
  intros Gamma rho x A arg Hr Ha y T Hlook.
  unfold update in Hlook; unfold subst_update.
  destruct (Nat.eqb x y) eqn:E.
  - inversion Hlook; subst; exact Ha.
  - eapply Hr; eauto.
Qed.

Lemma proper_update : forall rho x arg,
  proper_substitution rho -> value arg ->
  proper_substitution (subst_update rho x arg).
Proof.
  intros rho x arg Hp Hv y. unfold subst_update.
  destruct (Nat.eqb x y); [apply value_lc; exact Hv|apply Hp].
Qed.

Theorem fundamental : forall Gamma t T,
  has_type Gamma t T -> forall rho,
  proper_substitution rho -> related_substitution Gamma rho ->
  expression_relation T (msubst rho t).
Proof.
  intros Gamma t T Hty; induction Hty; intros rho Hp Hr; simpl.
  - eapply er_of_value. eapply Hr; eauto.
  - assert (Hlc : locally_closed (tm_abs T1 t1)).
    { eapply typing_lc. econstructor; exact H. }
    assert (Hvlc : locally_closed (tm_abs T1 (msubst rho t1))).
    { change (locally_closed (msubst rho (tm_abs T1 t1))). eapply msubst_lc; eauto. }
    apply er_of_value. simpl. split.
    + constructor; exact Hvlc.
    + exists (msubst rho t1). split; [reflexivity|].
      intros arg Harg.
      set (x := S (fold_right Nat.max 0 (L ++ fv t1))).
      assert (HxL : ~ In x L).
      { intro Hin; apply (fresh (L ++ fv t1)); apply in_app_iff; auto. }
      assert (Hxf : ~ In x (fv t1)).
      { intro Hin; apply (fresh (L ++ fv t1)); apply in_app_iff; auto. }
      specialize (H0 x HxL (subst_update rho x arg)).
      assert (He : msubst (subst_update rho x arg) (open t1 (tm_fvar x)) =
                   open (msubst rho t1) arg).
      { unfold open; apply msubst_open_fresh; auto. }
      rewrite <- He.
      apply H0.
      * apply proper_update; auto. eapply vr_value; eauto.
      * apply related_update; auto.
  - eapply er_app; eauto.
  - apply er_of_value. simpl; split; [constructor|left; reflexivity].
  - apply er_of_value. simpl; split; [constructor|right; reflexivity].
  - apply er_of_value. simpl; split; [constructor; constructor|constructor].
  - apply er_succ; auto.
  - eapply er_rec; eauto.
Qed.

Lemma numeric_no_step : forall n t, numeric_value n -> n --> t -> False.
Proof.
  intros n t Hn; revert t; induction Hn; intros t' Hs; inversion Hs; subst; eauto.
Qed.

Lemma value_no_step : forall v t, value v -> v --> t -> False.
Proof.
  intros v t Hv Hs; inversion Hv; subst; inversion Hs; subst; eauto using numeric_no_step.
Qed.

Ltac solve_no_step :=
  match goal with
  | Hv : value ?v, Hs : step ?v _ |- _ =>
      exfalso; exact (value_no_step v _ Hv Hs)
  | Hn : numeric_value ?n, Hs : step ?n _ |- _ =>
      exfalso; exact (numeric_no_step n _ Hn Hs)
  | Hlc : locally_closed (tm_abs ?T ?t), Hs : step (tm_abs ?T ?t) _ |- _ =>
      exfalso; eapply value_no_step; [constructor; exact Hlc|exact Hs]
  | Hn : numeric_value ?n, Hs : step (tm_succ ?n) _ |- _ =>
      exfalso; eapply numeric_no_step; [constructor; exact Hn|exact Hs]
  | Hs : step tm_zero _ |- _ => inversion Hs
  end.

Lemma step_deterministic : forall t a b, t --> a -> t --> b -> a = b.
Proof.
  intros t a b H1; revert b; induction H1; intros b0 H2; inversion H2; subst;
    try congruence; try solve [solve_no_step]; try solve [f_equal; eauto].
Qed.

Lemma value_sn : forall v, value v -> strongly_normalizing v.
Proof.
  intros v Hv; constructor; intros t Hs.
  exfalso; eapply value_no_step; eauto.
Qed.

Lemma multi_to_value_sn : forall t v, t -->* v -> value v -> strongly_normalizing t.
Proof.
  intros t v Hm Hv; induction Hm.
  - apply value_sn; exact Hv.
  - constructor; intros t' Hs.
    assert (t' = y) by (eapply step_deterministic; eauto).
    subst; apply IHHm; exact Hv.
Qed.

Lemma msubst_id : forall t, msubst id_substitution t = t.
Proof.
  induction t; simpl; try rewrite IHt; try rewrite IHt1; try rewrite IHt2;
    try rewrite IHt3; auto.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> -> strongly_normalizing t.
Proof.
  intros t T Hty.
  pose proof (fundamental empty t T Hty id_substitution) as Hrel.
  assert (Hp : proper_substitution id_substitution).
  { intros x; unfold id_substitution, locally_closed; constructor. }
  assert (Hr : related_substitution empty id_substitution).
  { intros x U H; discriminate. }
  specialize (Hrel Hp Hr).
  rewrite msubst_id in Hrel.
  destruct Hrel as [_ [v [Hm Hvr]]].
  eapply multi_to_value_sn; [exact Hm|eapply vr_value; eauto].
Qed.

End STLCNormalizationRecursionMediumTask.
