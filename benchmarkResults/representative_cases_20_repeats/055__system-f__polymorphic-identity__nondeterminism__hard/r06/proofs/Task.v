(** System F parametricity benchmark, Hard variant.
    Features: nondeterminism. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFParametricityNondeterminismHardTask.

Definition atom := nat.

Declare Scope systemf_scope.
Delimit Scope systemf_scope with systemf.
Open Scope systemf_scope.

Declare Custom Entry systemf_ty.
Declare Custom Entry systemf_tm.

Inductive ty : Type :=
  | Ty_BVar : nat -> ty
  | Ty_FVar : atom -> ty

  | Ty_Arrow : ty -> ty -> ty

  | Ty_All : ty -> ty.

Notation "T" := T
  (in custom systemf_ty at level 0, T constr at level 0) : systemf_scope.
Notation "<{{ T }}>" := T
  (T custom systemf_ty at level 200) : systemf_scope.
Notation "( T )" := T
  (in custom systemf_ty at level 0, T custom systemf_ty) : systemf_scope.
Notation "$( T )" := T
  (in custom systemf_ty at level 0, T constr) : systemf_scope.
Notation "'fvar' X" := (Ty_FVar X)
  (in custom systemf_ty at level 0, X constr at level 0) : systemf_scope.
Notation "T1 '->' T2" := (Ty_Arrow T1 T2)
  (in custom systemf_ty at level 99, right associativity) : systemf_scope.
Notation "'forall' ',' T" := (Ty_All T)
  (in custom systemf_ty at level 200,
   T custom systemf_ty at level 200,
   right associativity) : systemf_scope.

Inductive tm : Type :=
  | tm_bvar : nat -> tm
  | tm_fvar : atom -> tm
  | tm_abs : ty -> tm -> tm
  | tm_app : tm -> tm -> tm

  | tm_tabs : tm -> tm

  | tm_tapp : tm -> ty -> tm
  | tm_choice : tm -> tm -> tm.

Notation "t" := t
  (in custom systemf_tm at level 0, t constr at level 0) : systemf_scope.
Notation "<{ t }>" := t
  (t custom systemf_tm at level 200) : systemf_scope.
Notation "( t )" := t
  (in custom systemf_tm at level 0, t custom systemf_tm) : systemf_scope.
Notation "$( t )" := t
  (in custom systemf_tm at level 0, t constr, only parsing) : systemf_scope.
Notation "'bvar' n" := (tm_bvar n)
  (in custom systemf_tm at level 0, n constr at level 0) : systemf_scope.
Notation "'fvar' x" := (tm_fvar x)
  (in custom systemf_tm at level 0, x constr at level 0) : systemf_scope.
Notation "t1 t2" := (tm_app t1 t2)
  (in custom systemf_tm at level 10, left associativity) : systemf_scope.
Notation "'lambda' ':' T ',' t" := (tm_abs T t)
  (in custom systemf_tm at level 200,
   T custom systemf_ty,
   t custom systemf_tm at level 200,
   left associativity) : systemf_scope.
Notation "'Lambda' ',' t" := (tm_tabs t)
  (in custom systemf_tm at level 200,
   t custom systemf_tm at level 200,
   left associativity) : systemf_scope.
Notation "t '[' T ']'" := (tm_tapp t T)
  (in custom systemf_tm at level 10,
   t custom systemf_tm,
   T custom systemf_ty) : systemf_scope.

Notation "'choice' t1 'or' t2" := (tm_choice t1 t2)
  (in custom systemf_tm at level 200, t1 custom systemf_tm, t2 custom systemf_tm at level 200) : systemf_scope.

Fixpoint open_ty_rec (k : nat) (U T : ty) : ty :=
  match T with
  | Ty_BVar i => if Nat.eqb k i then U else Ty_BVar i
  | Ty_FVar X => Ty_FVar X
  | Ty_Arrow T1 T2 =>
      Ty_Arrow (open_ty_rec k U T1) (open_ty_rec k U T2)
  | Ty_All T1 => Ty_All (open_ty_rec (S k) U T1)
  end.

Definition open_ty (T U : ty) : ty := open_ty_rec 0 U T.

Fixpoint open_tm_rec (k : nat) (u t : tm) : tm :=
  match t with
  | tm_bvar i => if Nat.eqb k i then u else tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T t1 => tm_abs T (open_tm_rec (S k) u t1)
  | tm_app t1 t2 => tm_app (open_tm_rec k u t1) (open_tm_rec k u t2)
  | tm_tabs t1 => tm_tabs (open_tm_rec k u t1)
  | tm_tapp t1 T => tm_tapp (open_tm_rec k u t1) T
  | tm_choice t1 t2 => tm_choice (open_tm_rec k u t1) (open_tm_rec k u t2)
  end.

Definition open_tm (t u : tm) : tm := open_tm_rec 0 u t.

Fixpoint open_tm_ty_rec (k : nat) (U : ty) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T t1 =>
      tm_abs (open_ty_rec k U T) (open_tm_ty_rec k U t1)
  | tm_app t1 t2 =>
      tm_app (open_tm_ty_rec k U t1) (open_tm_ty_rec k U t2)
  | tm_tabs t1 => tm_tabs (open_tm_ty_rec (S k) U t1)
  | tm_tapp t1 T =>
      tm_tapp (open_tm_ty_rec k U t1) (open_ty_rec k U T)
  | tm_choice t1 t2 => tm_choice (open_tm_ty_rec k U t1) (open_tm_ty_rec k U t2)
  end.

Definition open_tm_ty (t : tm) (U : ty) : tm :=
  open_tm_ty_rec 0 U t.

Fixpoint ty_subst (X : atom) (U T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar Y => if Nat.eqb X Y then U else Ty_FVar Y
  | Ty_Arrow T1 T2 => Ty_Arrow (ty_subst X U T1) (ty_subst X U T2)
  | Ty_All T1 => Ty_All (ty_subst X U T1)
  end.

Fixpoint tm_ty_subst (X : atom) (U : ty) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T t1 => tm_abs (ty_subst X U T) (tm_ty_subst X U t1)
  | tm_app t1 t2 => tm_app (tm_ty_subst X U t1) (tm_ty_subst X U t2)
  | tm_tabs t1 => tm_tabs (tm_ty_subst X U t1)
  | tm_tapp t1 T => tm_tapp (tm_ty_subst X U t1) (ty_subst X U T)
  | tm_choice t1 t2 => tm_choice (tm_ty_subst X U t1) (tm_ty_subst X U t2)
  end.

Fixpoint tm_subst (x : atom) (s t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar y => if Nat.eqb x y then s else tm_fvar y
  | tm_abs T t1 => tm_abs T (tm_subst x s t1)
  | tm_app t1 t2 => tm_app (tm_subst x s t1) (tm_subst x s t2)
  | tm_tabs t1 => tm_tabs (tm_subst x s t1)
  | tm_tapp t1 T => tm_tapp (tm_subst x s t1) T
  | tm_choice t1 t2 => tm_choice (tm_subst x s t1) (tm_subst x s t2)
  end.

Inductive lc_ty_at : nat -> ty -> Prop :=
  | lc_ty_bvar : forall k i,
      i < k ->
      lc_ty_at k (Ty_BVar i)
  | lc_ty_fvar : forall k X,
      lc_ty_at k (Ty_FVar X)
  | lc_ty_arrow : forall k T1 T2,
      lc_ty_at k T1 ->
      lc_ty_at k T2 ->
      lc_ty_at k (Ty_Arrow T1 T2)
  | lc_ty_all : forall k T,
      lc_ty_at (S k) T ->
      lc_ty_at k (Ty_All T).

Definition locally_closed_ty (T : ty) : Prop := lc_ty_at 0 T.

Inductive lc_tm_at : nat -> nat -> tm -> Prop :=
  | lc_tm_bvar : forall K k i,
      i < k ->
      lc_tm_at K k (tm_bvar i)
  | lc_tm_fvar : forall K k x,
      lc_tm_at K k (tm_fvar x)
  | lc_tm_abs : forall K k T t,
      lc_ty_at K T ->
      lc_tm_at K (S k) t ->
      lc_tm_at K k (tm_abs T t)
  | lc_tm_app : forall K k t1 t2,
      lc_tm_at K k t1 ->
      lc_tm_at K k t2 ->
      lc_tm_at K k (tm_app t1 t2)
  | lc_tm_tabs : forall K k t,
      lc_tm_at (S K) k t ->
      lc_tm_at K k (tm_tabs t)
  | lc_tm_tapp : forall K k t T,
      lc_tm_at K k t ->
      lc_ty_at K T ->
      lc_tm_at K k (tm_tapp t T)
  | lc_tm_choice : forall K k t1 t2,
      lc_tm_at K k t1 -> lc_tm_at K k t2 -> lc_tm_at K k (tm_choice t1 t2).

Definition locally_closed_tm (t : tm) : Prop := lc_tm_at 0 0 t.

Inductive value : tm -> Prop :=
  | v_abs : forall T t,
      locally_closed_tm (tm_abs T t) ->
      value (tm_abs T t)
  | v_tabs : forall t,
      locally_closed_tm (tm_tabs t) ->
      value (tm_tabs t).

Reserved Notation "t1 '-->' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall T t v,
      locally_closed_tm (tm_abs T t) ->
      value v ->

      tm_app (tm_abs T t) v --> open_tm t v
  | ST_App1 : forall t1 t1' t2,
      t1 --> t1' ->
      locally_closed_tm t2 ->
      tm_app t1 t2 --> tm_app t1' t2

  | ST_App2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      tm_app v1 t2 --> tm_app v1 t2'
  | ST_TAppTabs :

      forall t T,
      locally_closed_tm (tm_tabs t) ->
      locally_closed_ty T ->
      tm_tapp (tm_tabs t) T --> open_tm_ty t T
  | ST_TApp : forall t t' T,
      t --> t' ->
      locally_closed_ty T ->
      tm_tapp t T --> tm_tapp t' T
  | ST_ChoiceLeft : forall t1 t2,
      locally_closed_tm t1 ->
      locally_closed_tm t2 ->
      tm_choice t1 t2 --> t1
  | ST_ChoiceRight : forall t1 t2,
      locally_closed_tm t1 ->
      locally_closed_tm t2 ->
      tm_choice t1 t2 --> t2
where "t1 '-->' t2" := (step t1 t2).

Definition ty_context := list atom.

Definition context := list (atom * ty).

Fixpoint lookup_context (x : atom) (Gamma : context) : option ty :=
  match Gamma with
  | [] => None
  | (y, T) :: Gamma' =>
      if Nat.eqb x y then Some T else lookup_context x Gamma'
  end.

Definition empty : context := [].

Definition update (Gamma : context) (x : atom) (T : ty) : context :=
  (x, T) :: Gamma.

Notation "x '|->' v ';' m" := (update m x v)
  (in custom systemf_tm at level 0,
   x constr at level 0,
   v custom systemf_ty,
   right associativity) : systemf_scope.
Notation "x '|->' v" := (update empty x v)
  (in custom systemf_tm at level 0,
   x constr at level 0,
   v custom systemf_ty) : systemf_scope.
Notation "'empty'" := empty
  (in custom systemf_tm) : systemf_scope.

Inductive wf_ty : ty_context -> ty -> Prop :=
  | WF_Var : forall Delta X,
      In X Delta ->
      wf_ty Delta (Ty_FVar X)
  | WF_Arrow : forall Delta T1 T2,
      wf_ty Delta T1 ->
      wf_ty Delta T2 ->
      wf_ty Delta (Ty_Arrow T1 T2)
  | WF_All :

      forall (L : list atom) Delta T,
      (forall X, ~ In X L ->
        wf_ty (X :: Delta) (open_ty T (Ty_FVar X))) ->
      wf_ty Delta (Ty_All T).

Inductive has_type : ty_context -> context -> tm -> ty -> Prop :=
  | T_Var : forall Delta Gamma x T,
      lookup_context x Gamma = Some T ->
      wf_ty Delta T ->
      has_type Delta Gamma (tm_fvar x) T
  | T_Abs : forall (L : list atom) Delta Gamma T1 t2 T2,
      wf_ty Delta T1 ->

      (forall x, ~ In x L ->
        has_type Delta <{ x |-> $(T1); Gamma }>
          (open_tm t2 (tm_fvar x)) T2) ->
      has_type Delta Gamma (tm_abs T1 t2) (Ty_Arrow T1 T2)
  | T_App : forall Delta Gamma t1 t2 T1 T2,
      has_type Delta Gamma t1 (Ty_Arrow T1 T2) ->
      has_type Delta Gamma t2 T1 ->
      has_type Delta Gamma (tm_app t1 t2) T2
  | T_TAbs : forall (L : list atom) Delta Gamma t T,
      (forall X, ~ In X L ->
        has_type (X :: Delta) Gamma
          (open_tm_ty t (Ty_FVar X))
          (open_ty T (Ty_FVar X))) ->
      has_type Delta Gamma (tm_tabs t) (Ty_All T)
  | T_TApp : forall Delta Gamma t T U,
      has_type Delta Gamma t (Ty_All T) ->
      wf_ty Delta U ->
      has_type Delta Gamma (tm_tapp t U) (open_ty T U)
  | T_Choice : forall Delta Gamma t1 t2 T,
      has_type Delta Gamma t1 T -> has_type Delta Gamma t2 T ->
      has_type Delta Gamma (tm_choice t1 t2) T.

Inductive multi : tm -> tm -> Prop :=
  | multi_refl : forall x, multi x x
  | multi_step : forall x y z, x --> y -> multi y z -> multi x z.
Notation "t '-->*' u" := (multi t u) (at level 40).


Hint Constructors lc_ty_at lc_tm_at value : core.

(* ============================================================ *)
(* Development: free variables and substitution infrastructure    *)
(* ============================================================ *)

Fixpoint fta_ty (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow A B => fta_ty A ++ fta_ty B
  | Ty_All A => fta_ty A
  end.

Fixpoint fta_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar _ => []
  | tm_abs T b => fta_ty T ++ fta_tm b
  | tm_app a b => fta_tm a ++ fta_tm b
  | tm_tabs b => fta_tm b
  | tm_tapp b T => fta_tm b ++ fta_ty T
  | tm_choice a b => fta_tm a ++ fta_tm b
  end.

Fixpoint ftv_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs _ b => ftv_tm b
  | tm_app a b => ftv_tm a ++ ftv_tm b
  | tm_tabs b => ftv_tm b
  | tm_tapp b _ => ftv_tm b
  | tm_choice a b => ftv_tm a ++ ftv_tm b
  end.

Fixpoint fbv_ty (T : ty) (i : nat) : Prop :=
  match T with
  | Ty_BVar j => i = j
  | Ty_FVar _ => False
  | Ty_Arrow A B => fbv_ty A i \/ fbv_ty B i
  | Ty_All A => fbv_ty A (S i)
  end.

Definition tyenv := atom -> ty.
Definition tmenv := atom -> tm.

Definition extend_ty (s : tyenv) (X : atom) (U : ty) : tyenv :=
  fun Y => if Nat.eqb Y X then U else s Y.

Definition extend_tm (g : tmenv) (x : atom) (u : tm) : tmenv :=
  fun y => if Nat.eqb y x then u else g y.

Fixpoint subst_ty_env (s : tyenv) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => s X
  | Ty_Arrow A B => Ty_Arrow (subst_ty_env s A) (subst_ty_env s B)
  | Ty_All A => Ty_All (subst_ty_env s A)
  end.

Fixpoint subst_tm_ty_env (s : tyenv) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T b => tm_abs (subst_ty_env s T) (subst_tm_ty_env s b)
  | tm_app a b => tm_app (subst_tm_ty_env s a) (subst_tm_ty_env s b)
  | tm_tabs b => tm_tabs (subst_tm_ty_env s b)
  | tm_tapp b T => tm_tapp (subst_tm_ty_env s b) (subst_ty_env s T)
  | tm_choice a b => tm_choice (subst_tm_ty_env s a) (subst_tm_ty_env s b)
  end.

Fixpoint subst_tm_env (g : tmenv) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => g x
  | tm_abs T b => tm_abs T (subst_tm_env g b)
  | tm_app a b => tm_app (subst_tm_env g a) (subst_tm_env g b)
  | tm_tabs b => tm_tabs (subst_tm_env g b)
  | tm_tapp b T => tm_tapp (subst_tm_env g b) T
  | tm_choice a b => tm_choice (subst_tm_env g a) (subst_tm_env g b)
  end.

Lemma extend_ty_same : forall s X U, extend_ty s X U X = U.
Proof. intros. unfold extend_ty. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma extend_ty_diff : forall s X U Y, Y <> X -> extend_ty s X U Y = s Y.
Proof. intros. unfold extend_ty. destruct (Nat.eqb Y X) eqn:E; auto.
  apply Nat.eqb_eq in E. contradiction. Qed.

Lemma extend_tm_same : forall g x u, extend_tm g x u x = u.
Proof. intros. unfold extend_tm. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma extend_tm_diff : forall g x u y, y <> x -> extend_tm g x u y = g y.
Proof. intros. unfold extend_tm. destruct (Nat.eqb y x) eqn:E; auto.
  apply Nat.eqb_eq in E. contradiction. Qed.

(* Locally closed types have no free BVar, hence opening does nothing below them *)
Lemma open_ty_rec_lc : forall T K, lc_ty_at K T -> forall k U, K <= k -> open_ty_rec k U T = T.
Proof.
  induction T; intros K H k U Hk; simpl in *; auto.
  - inversion H; subst. destruct (Nat.eqb k n) eqn:E; auto. apply Nat.eqb_eq in E. lia.
  - inversion H; subst.
    rewrite IHT1 with (K := K) (k := k) (U := U); try assumption.
    rewrite IHT2 with (K := K) (k := k) (U := U); try assumption; auto.
  - inversion H; subst.
    rewrite IHT with (K := S K) (k := S k) (U := U); try assumption; try lia; auto.
Qed.

Lemma open_tm_rec_lc : forall t K k, lc_tm_at K k t -> forall m u, k <= m -> open_tm_rec m u t = t.
Proof.
  induction t; intros K k H m u Hk; simpl in *; auto.
  - inversion H; subst. destruct (Nat.eqb m n) eqn:E; auto. apply Nat.eqb_eq in E. lia.
  - inversion H; subst.
    rewrite IHt with (K := K) (k := S k) (m := S m) (u := u); try assumption; try lia; auto.
  - inversion H; subst.
    rewrite IHt1 with (K := K) (k := k) (m := m) (u := u); try assumption.
    rewrite IHt2 with (K := K) (k := k) (m := m) (u := u); try assumption; auto.
  - inversion H; subst.
    rewrite IHt with (K := S K) (k := k) (m := m) (u := u); try assumption; auto.
  - inversion H; subst.
    rewrite IHt with (K := K) (k := k) (m := m) (u := u); try assumption; auto.
  - inversion H; subst.
    rewrite IHt1 with (K := K) (k := k) (m := m) (u := u); try assumption.
    rewrite IHt2 with (K := K) (k := k) (m := m) (u := u); try assumption; auto.
Qed.

(* Commutation: type substitution commutes with opening a type with a var *)
Lemma subst_ty_env_open_ty_rec : forall T s X U k,
  ~ In X (fta_ty T) ->
  (forall Y, lc_ty_at 0 (s Y)) ->
  lc_ty_at 0 U ->
  subst_ty_env (extend_ty s X U) (open_ty_rec k (Ty_FVar X) T)
  = open_ty_rec k U (subst_ty_env s T).
Proof.
  induction T; intros s X U k H Hsig HU; simpl in *.
  - (* BVar *)
    destruct (Nat.eqb k n); simpl; auto.
    unfold extend_ty. rewrite Nat.eqb_refl. auto.
  - (* FVar *)
    destruct (Nat.eqb a X) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply H. simpl. auto.
    + apply Nat.eqb_neq in E. rewrite extend_ty_diff by auto.
      rewrite open_ty_rec_lc with (K := 0) by (auto; lia). reflexivity.
  - (* Arrow *)
    transitivity (Ty_Arrow (open_ty_rec k U (subst_ty_env s T1))
                           (open_ty_rec k U (subst_ty_env s T2))).
    + f_equal.
      * apply IHT1; auto. intro; apply H; simpl; apply in_or_app; auto.
      * apply IHT2; auto. intro; apply H; simpl; apply in_or_app; auto.
    + reflexivity.
  - (* All *)
    transitivity (Ty_All (open_ty_rec (S k) U (subst_ty_env s T))).
    + f_equal. apply IHT; auto.
    + reflexivity.
Qed.

(* Commutation: type substitution commutes with opening a term's annotations *)
Lemma subst_tm_ty_env_open_tm_ty_rec : forall t s X U k,
  ~ In X (fta_tm t) ->
  (forall Y, lc_ty_at 0 (s Y)) ->
  lc_ty_at 0 U ->
  subst_tm_ty_env (extend_ty s X U) (open_tm_ty_rec k (Ty_FVar X) t)
  = open_tm_ty_rec k U (subst_tm_ty_env s t).
Proof.
  induction t; intros s X U k H Hsig HU; simpl in *.
  - (* bvar *) auto.
  - (* fvar *) auto.
  - (* abs *)
    transitivity (tm_abs (open_ty_rec k U (subst_ty_env s t))
                         (open_tm_ty_rec k U (subst_tm_ty_env s t0))).
    + f_equal.
      * apply subst_ty_env_open_ty_rec; auto.
        intro; apply H; simpl; apply in_or_app; auto.
      * apply IHt; auto. intro; apply H; simpl; apply in_or_app; auto.
    + reflexivity.
  - (* app *)
    transitivity (tm_app (open_tm_ty_rec k U (subst_tm_ty_env s t1))
                         (open_tm_ty_rec k U (subst_tm_ty_env s t2))).
    + f_equal.
      * apply IHt1; auto. intro; apply H; simpl; apply in_or_app; auto.
      * apply IHt2; auto. intro; apply H; simpl; apply in_or_app; auto.
    + reflexivity.
  - (* tabs *)
    transitivity (tm_tabs (open_tm_ty_rec (S k) U (subst_tm_ty_env s t))).
    + f_equal. apply IHt with (k := S k); auto.
    + reflexivity.
  - (* tapp *)
    transitivity (tm_tapp (open_tm_ty_rec k U (subst_tm_ty_env s t))
                          (open_ty_rec k U (subst_ty_env s t0))).
    + f_equal.
      * apply IHt; auto. intro; apply H; simpl; apply in_or_app; auto.
      * apply subst_ty_env_open_ty_rec; auto.
        intro; apply H; simpl; apply in_or_app; auto.
    + reflexivity.
  - (* choice *)
    transitivity (tm_choice (open_tm_ty_rec k U (subst_tm_ty_env s t1))
                            (open_tm_ty_rec k U (subst_tm_ty_env s t2))).
    + f_equal.
      * apply IHt1; auto. intro; apply H; simpl; apply in_or_app; auto.
      * apply IHt2; auto. intro; apply H; simpl; apply in_or_app; auto.
    + reflexivity.
Qed.

(* Commutation: term substitution and opening term variable *)
Lemma subst_tm_env_open_tm_rec : forall t g x u k,
  ~ In x (ftv_tm t) ->
  (forall y, lc_tm_at 0 0 (g y)) ->
  lc_tm_at 0 0 u ->
  subst_tm_env (extend_tm g x u) (open_tm_rec k (tm_fvar x) t)
  = open_tm_rec k u (subst_tm_env g t).
Proof.
  induction t; intros g x u k H Hg Hu; simpl in *.
  - (* bvar *)
    destruct (Nat.eqb k n); simpl; auto.
    unfold extend_tm. rewrite Nat.eqb_refl. auto.
  - (* fvar *)
    destruct (Nat.eqb a x) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply H. simpl. auto.
    + apply Nat.eqb_neq in E. rewrite extend_tm_diff by auto.
      rewrite open_tm_rec_lc with (K := 0) (k := 0) by (auto; lia). reflexivity.
  - (* abs *)
    transitivity (tm_abs t (open_tm_rec (S k) u (subst_tm_env g t0))).
    + f_equal. apply IHt; auto.
    + reflexivity.
  - (* app *)
    transitivity (tm_app (open_tm_rec k u (subst_tm_env g t1))
                         (open_tm_rec k u (subst_tm_env g t2))).
    + f_equal.
      * apply IHt1; auto. intro; apply H; simpl; apply in_or_app; auto.
      * apply IHt2; auto. intro; apply H; simpl; apply in_or_app; auto.
    + reflexivity.
  - (* tabs *)
    transitivity (tm_tabs (open_tm_rec k u (subst_tm_env g t))).
    + f_equal. apply IHt; auto.
    + reflexivity.
  - (* tapp *)
    transitivity (tm_tapp (open_tm_rec k u (subst_tm_env g t)) t0).
    + f_equal. apply IHt; auto.
    + reflexivity.
  - (* choice *)
    transitivity (tm_choice (open_tm_rec k u (subst_tm_env g t1))
                            (open_tm_rec k u (subst_tm_env g t2))).
    + f_equal.
      * apply IHt1; auto. intro; apply H; simpl; apply in_or_app; auto.
      * apply IHt2; auto. intro; apply H; simpl; apply in_or_app; auto.
    + reflexivity.
Qed.

(* Type substitution distributes over term opening (term substitution) *)
Lemma subst_tm_ty_env_open_tm_rec : forall t s u k,
  subst_tm_ty_env s (open_tm_rec k u t)
  = open_tm_rec k (subst_tm_ty_env s u) (subst_tm_ty_env s t).
Proof.
  induction t; intros s u k; simpl in *; auto.
  - destruct (Nat.eqb k n); auto.
  - rewrite IHt; auto.
  - rewrite IHt1, IHt2; auto.
  - rewrite IHt; auto.
  - rewrite IHt; auto.
  - rewrite IHt1, IHt2; auto.
Qed.

(* Opening type variables does nothing on locally closed terms *)
Lemma open_tm_ty_rec_lc : forall t K k, lc_tm_at K k t -> forall m U, K <= m ->
  open_tm_ty_rec m U t = t.
Proof.
  induction t; intros K k H m U Hm; simpl in *.
  - (* bvar *) auto.
  - (* fvar *) auto.
  - (* abs *) inversion H; subst.
    rewrite open_ty_rec_lc with (K := K) (k := m) by auto.
    rewrite IHt with (K := K) (k := S k) (m := m); try assumption; try lia. auto.
  - (* app *) inversion H; subst.
    rewrite IHt1 with (K := K) (k := k) (m := m); try assumption.
    rewrite IHt2 with (K := K) (k := k) (m := m); try assumption. auto.
  - (* tabs *) inversion H; subst.
    rewrite IHt with (K := S K) (k := k) (m := S m); try assumption; try lia. auto.
  - (* tapp *) inversion H; subst.
    rewrite open_ty_rec_lc with (K := K) (k := m) by auto.
    rewrite IHt with (K := K) (k := k) (m := m); try assumption. auto.
  - (* choice *) inversion H; subst.
    rewrite IHt1 with (K := K) (k := k) (m := m); try assumption.
    rewrite IHt2 with (K := K) (k := k) (m := m); try assumption. auto.
Qed.

(* Term substitution commutes with opening type variables *)
Lemma subst_tm_env_open_tm_ty_rec : forall t g U k,
  (forall y, lc_tm_at 0 0 (g y)) ->
  subst_tm_env g (open_tm_ty_rec k U t) = open_tm_ty_rec k U (subst_tm_env g t).
Proof.
  induction t; intros g U k Hg; simpl in *.
  - (* bvar *) auto.
  - (* fvar *)
    rewrite open_tm_ty_rec_lc with (K := 0) (k := 0) by (auto; lia). auto.
  - (* abs *) rewrite IHt; auto.
  - (* app *) rewrite IHt1, IHt2; auto.
  - (* tabs *)
    transitivity (tm_tabs (open_tm_ty_rec (S k) U (subst_tm_env g t))).
    + f_equal. apply IHt with (k := S k); auto.
    + reflexivity.
  - (* tapp *) rewrite IHt; auto.
  - (* choice *) rewrite IHt1, IHt2; auto.
Qed.

(* Identity substitutions *)
Lemma subst_ty_env_id : forall T, subst_ty_env (fun X => Ty_FVar X) T = T.
Proof.
  induction T; simpl.
  - (* BVar *) auto.
  - (* FVar *) auto.
  - (* Arrow *) rewrite IHT1, IHT2; auto.
  - (* All *) rewrite IHT; auto.
Qed.

Lemma subst_tm_ty_env_id : forall t, subst_tm_ty_env (fun X => Ty_FVar X) t = t.
Proof.
  induction t; simpl.
  - (* bvar *) auto.
  - (* fvar *) auto.
  - (* abs *) rewrite IHt, subst_ty_env_id; auto.
  - (* app *) rewrite IHt1, IHt2; auto.
  - (* tabs *) rewrite IHt; auto.
  - (* tapp *) rewrite IHt, subst_ty_env_id; auto.
  - (* choice *) rewrite IHt1, IHt2; auto.
Qed.

Lemma subst_tm_env_id : forall t, subst_tm_env (fun x => tm_fvar x) t = t.
Proof.
  induction t; simpl.
  - (* bvar *) auto.
  - (* fvar *) auto.
  - (* abs *) rewrite IHt; auto.
  - (* app *) rewrite IHt1, IHt2; auto.
  - (* tabs *) rewrite IHt; auto.
  - (* tapp *) rewrite IHt; auto.
  - (* choice *) rewrite IHt1, IHt2; auto.
Qed.

(* ============================================================ *)
(* Development: local closure lemmas                              *)
(* ============================================================ *)

Lemma in_fold_max : forall (l : list atom) X, In X l -> X <= fold_right max 0 l.
Proof.
  induction l as [| a l IH]; intros X H; simpl in *.
  - contradiction.
  - destruct H as [-> | H].
    + apply Nat.le_max_l.
    + apply Nat.le_trans with (fold_right max 0 l); auto. apply Nat.le_max_r.
Qed.

Lemma fresh_atom : forall l : list atom, exists X, ~ In X l.
Proof.
  intros l. exists (S (fold_right max 0 l)). intro H.
  apply in_fold_max in H. lia.
Qed.

Lemma max_S : forall a b, S (max a b) = max (S a) (S b).
Proof.
  intros. destruct (Nat.le_ge_cases a b).
  - rewrite Nat.max_r by auto. rewrite Nat.max_r by lia. auto.
  - rewrite Nat.max_l by auto. rewrite Nat.max_l by lia. auto.
Qed.

(* Monotonicity of local closure *)
Lemma lc_ty_mono : forall T K, lc_ty_at K T -> forall K', K <= K' -> lc_ty_at K' T.
Proof.
  induction T; intros K H K' HK; inversion H; subst; simpl.
  - (* BVar *) apply lc_ty_bvar. lia.
  - (* FVar *) apply lc_ty_fvar.
  - (* Arrow *) apply lc_ty_arrow.
    + apply IHT1 with (K := K); auto.
    + apply IHT2 with (K := K); auto.
  - (* All *) apply lc_ty_all. apply IHT with (K := S K); auto. lia.
Qed.

Lemma lc_tm_mono : forall t K k, lc_tm_at K k t -> forall K' k', K <= K' -> k <= k' -> lc_tm_at K' k' t.
Proof.
  induction t; intros K k H K' k' HK Hk; inversion H; subst; simpl.
  - (* bvar *) apply lc_tm_bvar. lia.
  - (* fvar *) apply lc_tm_fvar.
  - (* abs *) apply lc_tm_abs.
    + apply lc_ty_mono with (K := K); auto.
    + apply IHt with (K := K) (k := S k); auto. lia.
  - (* app *) apply lc_tm_app.
    + apply IHt1 with (K := K) (k := k); auto.
    + apply IHt2 with (K := K) (k := k); auto.
  - (* tabs *) apply lc_tm_tabs. apply IHt with (K := S K) (k := k); auto; lia.
  - (* tapp *) apply lc_tm_tapp.
    + apply IHt with (K := K) (k := k); auto.
    + apply lc_ty_mono with (K := K); auto.
  - (* choice *) apply lc_tm_choice.
    + apply IHt1 with (K := K) (k := k); auto.
    + apply IHt2 with (K := K) (k := k); auto.
Qed.

(* Restoring an opened (free) type variable *)
Lemma lc_ty_open_restore : forall T m U K,
  lc_ty_at K (open_ty_rec m U T) -> lc_ty_at (max K (S m)) T.
Proof.
  induction T; intros m U K H; simpl in *.
  - (* BVar *)
    destruct (Nat.eqb m n) eqn:E.
    + apply Nat.eqb_eq in E. subst. apply lc_ty_bvar. lia.
    + apply Nat.eqb_neq in E. apply lc_ty_bvar. inversion H; lia.
  - (* FVar *) apply lc_ty_fvar.
  - (* Arrow *) apply lc_ty_arrow.
    + apply IHT1 with (m := m) (U := U) (K := K). inversion H; auto.
    + apply IHT2 with (m := m) (U := U) (K := K). inversion H; auto.
  - (* All *)
    apply lc_ty_all. rewrite max_S.
    apply IHT with (m := S m) (U := U) (K := S K). inversion H; auto.
Qed.

(* Restoring an opened term variable *)
Lemma lc_tm_open_restore : forall t m u K k,
  lc_tm_at K k (open_tm_rec m u t) -> lc_tm_at K (max k (S m)) t.
Proof.
  induction t; intros m u K k H; simpl in *.
  - (* bvar *)
    destruct (Nat.eqb m n) eqn:E.
    + apply Nat.eqb_eq in E. subst. apply lc_tm_bvar. lia.
    + apply Nat.eqb_neq in E. apply lc_tm_bvar. inversion H; lia.
  - (* fvar *) apply lc_tm_fvar.
  - (* abs *) apply lc_tm_abs.
    + inversion H; auto.
    + rewrite max_S. apply IHt with (m := S m) (u := u) (K := K) (k := S k). inversion H; auto.
  - (* app *) apply lc_tm_app.
    + apply IHt1 with (m := m) (u := u) (K := K) (k := k). inversion H; auto.
    + apply IHt2 with (m := m) (u := u) (K := K) (k := k). inversion H; auto.
  - (* tabs *) apply lc_tm_tabs.
    apply IHt with (m := m) (u := u) (K := S K) (k := k). inversion H; auto.
  - (* tapp *) apply lc_tm_tapp.
    + apply IHt with (m := m) (u := u) (K := K) (k := k). inversion H; auto.
    + inversion H; auto.
  - (* choice *) apply lc_tm_choice.
    + apply IHt1 with (m := m) (u := u) (K := K) (k := k). inversion H; auto.
    + apply IHt2 with (m := m) (u := u) (K := K) (k := k). inversion H; auto.
Qed.

(* Restoring an opened type variable (appearing in term annotations) *)
Lemma lc_tm_ty_open_restore : forall t m U K k,
  lc_tm_at K k (open_tm_ty_rec m U t) -> lc_ty_at K U ->
  lc_tm_at (max K (S m)) k t.
Proof.
  induction t; intros m U K k H HU; simpl in *.
  - (* bvar *) apply lc_tm_bvar. inversion H; subst; lia.
  - (* fvar *) apply lc_tm_fvar.
  - (* abs *) apply lc_tm_abs.
    + apply lc_ty_open_restore with (m := m) (U := U) (K := K). inversion H; auto.
    + apply IHt with (m := m) (U := U) (K := K) (k := S k); auto.
      inversion H; auto.
  - (* app *) apply lc_tm_app.
    + apply IHt1 with (m := m) (U := U) (K := K) (k := k); auto. inversion H; auto.
    + apply IHt2 with (m := m) (U := U) (K := K) (k := k); auto. inversion H; auto.
  - (* tabs *)
    apply lc_tm_tabs. rewrite max_S.
    apply IHt with (m := S m) (U := U) (K := S K) (k := k); auto.
    + inversion H; auto.
    + apply lc_ty_mono with (K := K); auto; lia.
  - (* tapp *) apply lc_tm_tapp.
    + apply IHt with (m := m) (U := U) (K := K) (k := k); auto. inversion H; auto.
    + apply lc_ty_open_restore with (m := m) (U := U) (K := K). inversion H; auto.
  - (* choice *) apply lc_tm_choice.
    + apply IHt1 with (m := m) (U := U) (K := K) (k := k); auto. inversion H; auto.
    + apply IHt2 with (m := m) (U := U) (K := K) (k := k); auto. inversion H; auto.
Qed.

(* Type substitution preserves local closure *)
Lemma lc_ty_subst : forall T K K0 s, lc_ty_at K T -> K <= K0 ->
  (forall X, lc_ty_at K0 (s X)) -> lc_ty_at K0 (subst_ty_env s T).
Proof.
  induction T; intros K K0 s H HK Hsig; simpl in *.
  - (* BVar *) apply lc_ty_bvar. inversion H; subst; lia.
  - (* FVar *) apply Hsig.
  - (* Arrow *) apply lc_ty_arrow.
    + apply IHT1 with (K := K) (K0 := K0) (s := s); auto. inversion H; auto.
    + apply IHT2 with (K := K) (K0 := K0) (s := s); auto. inversion H; auto.
  - (* All *)
    apply lc_ty_all.
    inversion H; subst.
    apply IHT with (K := S K) (K0 := S K0) (s := s).
    + assumption.
    + lia.
    + intro X. apply lc_ty_mono with (K := K0); auto; lia.
Qed.

(* Term/type simultaneous local closure under instantiation *)
Lemma lc_tm_ty_subst : forall t K k K0 s, lc_tm_at K k t -> K <= K0 ->
  (forall X, lc_ty_at K0 (s X)) -> lc_tm_at K0 k (subst_tm_ty_env s t).
Proof.
  induction t; intros K k K0 s H HK Hsig; simpl in *.
  - (* bvar *) apply lc_tm_bvar. inversion H; subst; lia.
  - (* fvar *) apply lc_tm_fvar.
  - (* abs *) apply lc_tm_abs.
    + apply lc_ty_subst with (K := K) (K0 := K0) (s := s); auto. inversion H; auto.
    + apply IHt with (K := K) (K0 := K0) (s := s); auto. inversion H; auto.
  - (* app *) apply lc_tm_app.
    + apply IHt1 with (K := K) (K0 := K0) (s := s); auto. inversion H; auto.
    + apply IHt2 with (K := K) (K0 := K0) (s := s); auto. inversion H; auto.
  - (* tabs *)
    apply lc_tm_tabs.
    inversion H; subst.
    apply IHt with (K := S K) (K0 := S K0) (s := s).
    + assumption.
    + lia.
    + intro X. apply lc_ty_mono with (K := K0); auto; lia.
  - (* tapp *) apply lc_tm_tapp.
    + apply IHt with (K := K) (K0 := K0) (s := s); auto. inversion H; auto.
    + apply lc_ty_subst with (K := K) (K0 := K0) (s := s); auto. inversion H; auto.
  - (* choice *) apply lc_tm_choice.
    + apply IHt1 with (K := K) (K0 := K0) (s := s); auto. inversion H; auto.
    + apply IHt2 with (K := K) (K0 := K0) (s := s); auto. inversion H; auto.
Qed.

(* Well-formed types are locally closed *)
Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> lc_ty_at 0 T.
Proof.
  induction 1 as [Delta X Hin | Delta T1 T2 H1 IH1 H2 IH2 | L Delta T H IH].
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; auto.
  - apply lc_ty_all.
    destruct (fresh_atom (L ++ fta_ty T)) as [X HX].
    assert (HL : ~ In X L) by (intro Hin; apply HX; apply in_or_app; auto).
    pose proof (IH X HL) as Hlc.
    change (lc_ty_at (max 0 (S 0)) T).
    apply lc_ty_open_restore with (m := 0) (U := Ty_FVar X) (K := 0); auto.
Qed.

(* ============================================================ *)
(* Development: binary type-indexed logical relation              *)
(* ============================================================ *)

Definition rel := tm -> tm -> Prop.
Definition stack := nat -> rel.
Definition empty_stack : stack := fun _ => fun _ _ => False.
Definition push_stack (R : rel) (st : stack) : stack :=
  fun i => match i with 0 => R | S j => st j end.
Definition set_stack (st : stack) (m : nat) (R : rel) : stack :=
  fun i => if Nat.eqb i m then R else st i.
Definition empty_rho : atom -> rel := fun _ => fun _ _ => False.
Definition extend_rho (rho : atom -> rel) (X : atom) (R : rel) : atom -> rel :=
  fun Y => if Nat.eqb Y X then R else rho Y.

Lemma extend_rho_same : forall rho X R, extend_rho rho X R X = R.
Proof. intros. unfold extend_rho. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma extend_rho_diff : forall rho X R Y, Y <> X -> extend_rho rho X R Y = rho Y.
Proof. intros. unfold extend_rho. destruct (Nat.eqb Y X) eqn:E; auto.
  apply Nat.eqb_eq in E. contradiction. Qed.

Fixpoint V_ty (st : stack) (rho : atom -> rel) (T : ty) : rel :=
  match T with
  | Ty_BVar i => st i
  | Ty_FVar X => rho X
  | Ty_Arrow A B =>
      fun v1 v2 => forall u1 u2, value u1 -> value u2 -> V_ty st rho A u1 u2 ->
        (exists w1 w2, value w1 /\ value w2 /\
           tm_app v1 u1 -->* w1 /\ tm_app v2 u2 -->* w2 /\
           V_ty st rho B w1 w2)
  | Ty_All A =>
      fun v1 v2 => forall R U1 U2, lc_ty_at 0 U1 -> lc_ty_at 0 U2 ->
        (exists w1 w2, value w1 /\ value w2 /\
           tm_tapp v1 U1 -->* w1 /\ tm_tapp v2 U2 -->* w2 /\
           V_ty (push_stack R st) rho A w1 w2)
  end.

Definition E_ty (st : stack) (rho : atom -> rel) (T : ty) (t1 t2 : tm) : Prop :=
  exists w1 w2, value w1 /\ value w2 /\
    t1 -->* w1 /\ t2 -->* w2 /\ V_ty st rho T w1 w2.

(* Stack extensionality *)
Lemma V_ty_stack_ext : forall T st1 st2 rho,
  (forall i t1 t2, st1 i t1 t2 <-> st2 i t1 t2) ->
  forall t1 t2, V_ty st1 rho T t1 t2 <-> V_ty st2 rho T t1 t2.
Proof.
  induction T; intros st1 st2 rho Hst t1 t2; simpl in *.
  - (* BVar *) apply Hst.
  - (* FVar *) reflexivity.
  - (* Arrow *)
    split; intros H u1 u2 Hv1 Hv2 HA.
    + destruct (H u1 u2 Hv1 Hv2 (proj2 (IHT1 st1 st2 rho Hst u1 u2) HA))
        as (w1 & w2 & Vw1 & Vw2 & S1 & S2 & VB).
      exists w1, w2. split; auto. split; auto. split; auto. split; auto.
      apply (proj1 (IHT2 st1 st2 rho Hst w1 w2)); auto.
    + destruct (H u1 u2 Hv1 Hv2 (proj1 (IHT1 st1 st2 rho Hst u1 u2) HA))
        as (w1 & w2 & Vw1 & Vw2 & S1 & S2 & VB).
      exists w1, w2. split; auto. split; auto. split; auto. split; auto.
      apply (proj2 (IHT2 st1 st2 rho Hst w1 w2)); auto.
  - (* All *)
    split; intros H R U1 U2 HU1 HU2.
    + destruct (H R U1 U2 HU1 HU2) as (w1 & w2 & Vw1 & Vw2 & S1 & S2 & VB).
      exists w1, w2. split; auto. split; auto. split; auto. split; auto.
      assert (Hp : forall i a b, push_stack R st1 i a b <-> push_stack R st2 i a b).
      { intros i a b. destruct i; simpl. split; auto. apply Hst. }
      exact (proj1 (IHT (push_stack R st1) (push_stack R st2) rho Hp w1 w2) VB).
    + destruct (H R U1 U2 HU1 HU2) as (w1 & w2 & Vw1 & Vw2 & S1 & S2 & VB).
      exists w1, w2. split; auto. split; auto. split; auto. split; auto.
      assert (Hp : forall i a b, push_stack R st1 i a b <-> push_stack R st2 i a b).
      { intros i a b. destruct i; simpl. split; auto. apply Hst. }
      exact (proj2 (IHT (push_stack R st1) (push_stack R st2) rho Hp w1 w2) VB).
Qed.

Lemma E_ty_stack_ext : forall T st1 st2 rho,
  (forall i t1 t2, st1 i t1 t2 <-> st2 i t1 t2) ->
  forall t1 t2, E_ty st1 rho T t1 t2 <-> E_ty st2 rho T t1 t2.
Proof.
  intros T st1 st2 rho Hst t1 t2. unfold E_ty.
  split; intros (w1 & w2 & Vw1 & Vw2 & S1 & S2 & VB); exists w1, w2;
    repeat split; auto;
    apply (proj1 (V_ty_stack_ext T st1 st2 rho Hst w1 w2) VB) ||
    apply (proj2 (V_ty_stack_ext T st1 st2 rho Hst w1 w2) VB).
Qed.

(* Stack irrelevance for locally closed types *)
Lemma V_ty_lc_stack_indep : forall T K, lc_ty_at K T ->
  forall st1 st2 rho,
  (forall i, i < K -> forall t1 t2, st1 i t1 t2 <-> st2 i t1 t2) ->
  forall t1 t2, V_ty st1 rho T t1 t2 <-> V_ty st2 rho T t1 t2.
Proof.
  induction T; intros K Hlc st1 st2 rho Hst t1 t2; simpl in *.
  - (* BVar *) apply Hst. inversion Hlc; subst; lia.
  - (* FVar *) reflexivity.
  - (* Arrow *)
    split; intros H u1 u2 Hv1 Hv2 HA.
    + destruct (H u1 u2 Hv1 Hv2 (proj2 (IHT1 K (ltac:(inversion Hlc; auto)) st1 st2 rho Hst u1 u2) HA))
        as (w1 & w2 & Vw1 & Vw2 & S1 & S2 & VB).
      exists w1, w2. split; auto. split; auto. split; auto. split; auto.
      apply (proj1 (IHT2 K (ltac:(inversion Hlc; auto)) st1 st2 rho Hst w1 w2)); auto.
    + destruct (H u1 u2 Hv1 Hv2 (proj1 (IHT1 K (ltac:(inversion Hlc; auto)) st1 st2 rho Hst u1 u2) HA))
        as (w1 & w2 & Vw1 & Vw2 & S1 & S2 & VB).
      exists w1, w2. split; auto. split; auto. split; auto. split; auto.
      apply (proj2 (IHT2 K (ltac:(inversion Hlc; auto)) st1 st2 rho Hst w1 w2)); auto.
  - (* All *)
    split; intros H R U1 U2 HU1 HU2.
    + destruct (H R U1 U2 HU1 HU2) as (w1 & w2 & Vw1 & Vw2 & S1 & S2 & VB).
      exists w1, w2. split; auto. split; auto. split; auto. split; auto.
      assert (HlcA : lc_ty_at (S K) T) by (inversion Hlc; auto).
      assert (Hp : forall i, i < S K -> forall a b, push_stack R st1 i a b <-> push_stack R st2 i a b).
      { intros i Hi a b. destruct i; simpl. split; auto. apply Hst. lia. }
      exact (proj1 (IHT (S K) HlcA (push_stack R st1) (push_stack R st2) rho Hp w1 w2) VB).
    + destruct (H R U1 U2 HU1 HU2) as (w1 & w2 & Vw1 & Vw2 & S1 & S2 & VB).
      exists w1, w2. split; auto. split; auto. split; auto. split; auto.
      assert (HlcA : lc_ty_at (S K) T) by (inversion Hlc; auto).
      assert (Hp : forall i, i < S K -> forall a b, push_stack R st1 i a b <-> push_stack R st2 i a b).
      { intros i Hi a b. destruct i; simpl. split; auto. apply Hst. lia. }
      exact (proj2 (IHT (S K) HlcA (push_stack R st1) (push_stack R st2) rho Hp w1 w2) VB).
Qed.

Lemma in_app_l : forall (l1 l2 : list atom) X, In X l1 -> In X (l1 ++ l2).
Proof. intros. apply in_or_app. auto. Qed.

Lemma in_app_r : forall (l1 l2 : list atom) X, In X l2 -> In X (l1 ++ l2).
Proof. intros. apply in_or_app. auto. Qed.

Lemma V_ty_lc_stack_indep0 : forall T, lc_ty_at 0 T ->
  forall st1 st2 rho t1 t2, V_ty st1 rho T t1 t2 <-> V_ty st2 rho T t1 t2.
Proof.
  intros T Hlc st1 st2 rho t1 t2.
  apply (V_ty_lc_stack_indep T 0 Hlc st1 st2 rho).
  intros k Hk. exfalso. lia.
Qed.

(* rho extensionality on the free atoms of a type *)
Lemma V_ty_rho_ext : forall T st rho1 rho2,
  (forall X, In X (fta_ty T) -> forall t1 t2, rho1 X t1 t2 <-> rho2 X t1 t2) ->
  forall t1 t2, V_ty st rho1 T t1 t2 <-> V_ty st rho2 T t1 t2.
Proof.
  induction T; intros st rho1 rho2 Hrho t1 t2; simpl in *.
  - (* BVar *) reflexivity.
  - (* FVar *) apply Hrho. simpl. auto.
  - (* Arrow *)
    split; intros H u1 u2 Hv1 Hv2 HA.
    + destruct (H u1 u2 Hv1 Hv2 (proj2 (IHT1 st rho1 rho2 (fun X HX => Hrho X (in_app_l _ _ _ HX)) u1 u2) HA))
        as (w1 & w2 & Vw1 & Vw2 & S1 & S2 & VB).
      exists w1, w2. split; auto. split; auto. split; auto. split; auto.
      apply (proj1 (IHT2 st rho1 rho2 (fun X HX => Hrho X (in_app_r _ _ _ HX)) w1 w2)); auto.
    + destruct (H u1 u2 Hv1 Hv2 (proj1 (IHT1 st rho1 rho2 (fun X HX => Hrho X (in_app_l _ _ _ HX)) u1 u2) HA))
        as (w1 & w2 & Vw1 & Vw2 & S1 & S2 & VB).
      exists w1, w2. split; auto. split; auto. split; auto. split; auto.
      apply (proj2 (IHT2 st rho1 rho2 (fun X HX => Hrho X (in_app_r _ _ _ HX)) w1 w2)); auto.
  - (* All *)
    split; intros H R U1 U2 HU1 HU2.
    + destruct (H R U1 U2 HU1 HU2) as (w1 & w2 & Vw1 & Vw2 & S1 & S2 & VB).
      exists w1, w2. split; auto. split; auto. split; auto. split; auto.
      exact (proj1 (IHT (push_stack R st) rho1 rho2 Hrho w1 w2) VB).
    + destruct (H R U1 U2 HU1 HU2) as (w1 & w2 & Vw1 & Vw2 & S1 & S2 & VB).
      exists w1, w2. split; auto. split; auto. split; auto. split; auto.
      exact (proj2 (IHT (push_stack R st) rho1 rho2 Hrho w1 w2) VB).
Qed.

Lemma E_ty_rho_ext : forall T st rho1 rho2,
  (forall X, In X (fta_ty T) -> forall t1 t2, rho1 X t1 t2 <-> rho2 X t1 t2) ->
  forall t1 t2, E_ty st rho1 T t1 t2 <-> E_ty st rho2 T t1 t2.
Proof.
  intros T st rho1 rho2 Hrho t1 t2. unfold E_ty.
  split; intros (w1 & w2 & Vw1 & Vw2 & S1 & S2 & VB); exists w1, w2;
    repeat split; auto;
    apply (proj1 (V_ty_rho_ext T st rho1 rho2 Hrho w1 w2) VB) ||
    apply (proj2 (V_ty_rho_ext T st rho1 rho2 Hrho w1 w2) VB).
Qed.

(* Opening a type variable in a pre-type, semantically *)
Lemma V_ty_open_ty_rec : forall T st rho m U,
  lc_ty_at 0 U ->
  forall t1 t2, V_ty st rho (open_ty_rec m U T) t1 t2 <->
                V_ty (set_stack st m (V_ty st rho U)) rho T t1 t2.
Proof.
  induction T; intros st rho m U HU t1 t2; simpl.
  - (* BVar *)
    destruct (Nat.eqb m n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. simpl.
      unfold set_stack. rewrite Nat.eqb_refl. reflexivity.
    + apply Nat.eqb_neq in E. simpl. unfold set_stack.
      destruct (Nat.eqb n m) eqn:E2.
      * apply Nat.eqb_eq in E2. congruence.
      * reflexivity.
  - (* FVar *) reflexivity.
  - (* Arrow *)
    split; intros H u1 u2 Hv1 Hv2 HA.
    + destruct (H u1 u2 Hv1 Hv2 (proj2 (IHT1 st rho m U HU u1 u2) HA))
        as (w1 & w2 & Vw1 & Vw2 & S1 & S2 & VB).
      exists w1, w2. split; auto. split; auto. split; auto. split; auto.
      apply (proj1 (IHT2 st rho m U HU w1 w2)); auto.
    + destruct (H u1 u2 Hv1 Hv2 (proj1 (IHT1 st rho m U HU u1 u2) HA))
        as (w1 & w2 & Vw1 & Vw2 & S1 & S2 & VB).
      exists w1, w2. split; auto. split; auto. split; auto. split; auto.
      apply (proj2 (IHT2 st rho m U HU w1 w2)); auto.
  - (* All *)
    split; intros H R U1 U2 HU1 HU2.
    + destruct (H R U1 U2 HU1 HU2) as (w1 & w2 & Vw1 & Vw2 & S1 & S2 & VB).
      exists w1, w2. split; auto. split; auto. split; auto. split; auto.
      assert (Hp : forall i a b,
        set_stack (push_stack R st) (S m) (V_ty (push_stack R st) rho U) i a b <->
        push_stack R (set_stack st m (V_ty st rho U)) i a b).
      { intros i a b. destruct i as [| j]; simpl.
        - split; auto.
        - destruct (Nat.eqb j m) eqn:E.
          + apply Nat.eqb_eq in E. subst j.
            unfold set_stack. repeat rewrite Nat.eqb_refl. simpl.
            exact (V_ty_lc_stack_indep0 U HU (push_stack R st) st rho a b).
          + unfold set_stack, push_stack. simpl. rewrite E. simpl. reflexivity. }
      exact (proj1 (V_ty_stack_ext T
                      (set_stack (push_stack R st) (S m) (V_ty (push_stack R st) rho U))
                      (push_stack R (set_stack st m (V_ty st rho U))) rho Hp w1 w2)
               (proj1 (IHT (push_stack R st) rho (S m) U HU w1 w2) VB)).
    + destruct (H R U1 U2 HU1 HU2) as (w1 & w2 & Vw1 & Vw2 & S1 & S2 & VB).
      exists w1, w2. split; auto. split; auto. split; auto. split; auto.
      assert (Hp : forall i a b,
        set_stack (push_stack R st) (S m) (V_ty (push_stack R st) rho U) i a b <->
        push_stack R (set_stack st m (V_ty st rho U)) i a b).
      { intros i a b. destruct i as [| j]; simpl.
        - split; auto.
        - destruct (Nat.eqb j m) eqn:E.
          + apply Nat.eqb_eq in E. subst j.
            unfold set_stack. repeat rewrite Nat.eqb_refl. simpl.
            exact (V_ty_lc_stack_indep0 U HU (push_stack R st) st rho a b).
          + unfold set_stack, push_stack. simpl. rewrite E. simpl. reflexivity. }
      exact (proj2 (IHT (push_stack R st) rho (S m) U HU w1 w2)
               (proj2 (V_ty_stack_ext T
                         (set_stack (push_stack R st) (S m) (V_ty (push_stack R st) rho U))
                         (push_stack R (set_stack st m (V_ty st rho U))) rho Hp w1 w2) VB)).
Qed.

(* ============================================================ *)
(* Development: multistep lemmas and lc of instantiations         *)
(* ============================================================ *)

Lemma multi_trans : forall a b c, a -->* b -> b -->* c -> a -->* c.
Proof.
  intros a b c H. induction H as [x | x y z Hstep Hrest IH]; intros H2.
  - auto.
  - apply multi_step with (y := y); auto.
Qed.

Lemma multi_app_l : forall t1 t1' t2, t1 -->* t1' -> locally_closed_tm t2 ->
  tm_app t1 t2 -->* tm_app t1' t2.
Proof.
  intros t1 t1' t2 H. induction H as [x | x y z Hstep Hrest IH]; intros Hlc.
  - apply multi_refl.
  - apply multi_step with (y := tm_app y t2).
    + apply ST_App1; auto.
    + apply IH; auto.
Qed.

Lemma multi_app_r : forall v1 t2 t2', value v1 -> t2 -->* t2' ->
  tm_app v1 t2 -->* tm_app v1 t2'.
Proof.
  intros v1 t2 t2' Hv H. induction H as [x | x y z Hstep Hrest IH].
  - apply multi_refl.
  - apply multi_step with (y := tm_app v1 y).
    + apply ST_App2; auto.
    + apply IH; auto.
Qed.

Lemma multi_tapp : forall t t' T, t -->* t' -> locally_closed_ty T ->
  tm_tapp t T -->* tm_tapp t' T.
Proof.
  intros t t' T H. induction H as [x | x y z Hstep Hrest IH]; intros Hlc.
  - apply multi_refl.
  - apply multi_step with (y := tm_tapp y T).
    + apply ST_TApp; auto.
    + apply IH; auto.
Qed.

Lemma multi_tapp_tabs : forall b T, locally_closed_tm (tm_tabs b) -> locally_closed_ty T ->
  tm_tapp (tm_tabs b) T -->* open_tm_ty b T.
Proof.
  intros. apply multi_step with (y := open_tm_ty b T).
  - apply ST_TAppTabs; auto.
  - apply multi_refl.
Qed.

Lemma multi_app_abs : forall T b v, locally_closed_tm (tm_abs T b) -> value v ->
  tm_app (tm_abs T b) v -->* open_tm b v.
Proof.
  intros. apply multi_step with (y := open_tm b v).
  - apply ST_AppAbs; auto.
  - apply multi_refl.
Qed.

Lemma multi_choice_l : forall t1 t2, locally_closed_tm t1 -> locally_closed_tm t2 ->
  tm_choice t1 t2 -->* t1.
Proof.
  intros. apply multi_step with (y := t1).
  - apply ST_ChoiceLeft; auto.
  - apply multi_refl.
Qed.

Lemma value_lc : forall v, value v -> lc_tm_at 0 0 v.
Proof. intros v H. inversion H; auto. Qed.

Lemma ftv_tm_subst_ty : forall t s, ftv_tm (subst_tm_ty_env s t) = ftv_tm t.
Proof.
  induction t; intros s; simpl.
  - auto.
  - auto.
  - rewrite IHt; auto.
  - rewrite IHt1, IHt2; auto.
  - rewrite IHt; auto.
  - rewrite IHt; auto.
  - rewrite IHt1, IHt2; auto.
Qed.

(* Locally closed instantiations of well-typed terms *)
Lemma lc_inst : forall Delta Gamma t T, has_type Delta Gamma t T ->
  forall s g,
  (forall X, lc_ty_at 0 (s X)) ->
  (forall y, lc_tm_at 0 0 (g y)) ->
  lc_tm_at 0 0 (subst_tm_env g (subst_tm_ty_env s t)).
Proof.
  induction 1 as [Delta Gamma x T Hlook Hwf
                | L Delta Gamma T1 t2 T2 Hwf Hbody IHbody
                | Delta Gamma t1 t2 T1 T2 Hfun IHfun Harg IHarg
                | L Delta Gamma t T Hbody IHbody
                | Delta Gamma t T U Hfun IHfun Hwf
                | Delta Gamma t1 t2 T H1 IH1 H2 IH2];
    intros s g Hsig Hg; simpl.
  - (* T_Var *) apply Hg.
  - (* T_Abs *) apply lc_tm_abs.
    + apply lc_ty_subst with (K := 0) (K0 := 0) (s := s).
      * exact (wf_ty_lc Delta T1 Hwf).
      * lia.
      * assumption.
    + destruct (fresh_atom (L ++ ftv_tm t2)) as [x Hx].
      assert (HL : ~ In x L).
      { intro Hin. apply Hx. apply in_or_app. left. auto. }
      assert (Hfv : ~ In x (ftv_tm t2)).
      { intro Hin. apply Hx. apply in_or_app. right. auto. }
      assert (Hg' : forall y, lc_tm_at 0 0 (extend_tm g x (tm_fvar x) y)).
      { intro y. unfold extend_tm. destruct (Nat.eqb y x); auto. }
      pose proof (IHbody x HL s (extend_tm g x (tm_fvar x)) Hsig Hg') as Hbodylc.
      unfold open_tm in Hbodylc.
      rewrite subst_tm_ty_env_open_tm_rec in Hbodylc.
      simpl in Hbodylc.
      assert (Hfv' : ~ In x (ftv_tm (subst_tm_ty_env s t2))).
      { rewrite ftv_tm_subst_ty. auto. }
      rewrite subst_tm_env_open_tm_rec in Hbodylc; auto.
      pose proof (lc_tm_open_restore (subst_tm_env g (subst_tm_ty_env s t2)) 0
                    (tm_fvar x) 0 0) as Hr.
      simpl in Hr. apply Hr in Hbodylc.
      replace (max 0 (S 0)) with 1 in Hbodylc by lia. auto.
  - (* T_App *) apply lc_tm_app; auto.
  - (* T_TAbs *)
    apply lc_tm_tabs.
    destruct (fresh_atom (L ++ fta_tm t)) as [X HX].
    assert (HL : ~ In X L).
    { intro Hin. apply HX. apply in_or_app. left. auto. }
    assert (Hfta : ~ In X (fta_tm t)).
    { intro Hin. apply HX. apply in_or_app. right. auto. }
    assert (Hsig' : forall Y, lc_ty_at 0 (extend_ty s X (Ty_FVar X) Y)).
    { intro Y. unfold extend_ty. destruct (Nat.eqb Y X); auto. }
    pose proof (IHbody X HL (extend_ty s X (Ty_FVar X)) g Hsig' Hg) as Hbodylc.
    unfold open_tm_ty in Hbodylc.
    rewrite subst_tm_ty_env_open_tm_ty_rec in Hbodylc by auto.
    rewrite subst_tm_env_open_tm_ty_rec in Hbodylc by auto.
    pose proof (lc_tm_ty_open_restore (subst_tm_env g (subst_tm_ty_env s t)) 0
                  (Ty_FVar X) 0 0) as Hr.
    simpl in Hr. apply Hr in Hbodylc; auto.
  - (* T_TApp *) apply lc_tm_tapp.
    + auto.
    + apply lc_ty_subst with (K := 0) (K0 := 0) (s := s).
      * exact (wf_ty_lc Delta U Hwf).
      * lia.
      * assumption.
  - (* T_Choice *) apply lc_tm_choice; auto.
Qed.

(* ============================================================ *)
(* Development: E_ty conversions and the fundamental theorem      *)
(* ============================================================ *)

Lemma E_ty_of_V : forall st rho T v1 v2,
  value v1 -> value v2 -> V_ty st rho T v1 v2 -> E_ty st rho T v1 v2.
Proof.
  intros. exists v1, v2. repeat split; auto; apply multi_refl.
Qed.

Lemma E_ty_step_l : forall st rho T t1 t1' t2,
  t1 --> t1' -> E_ty st rho T t1' t2 -> E_ty st rho T t1 t2.
Proof.
  intros st rho T t1 t1' t2 Hstep (w1 & w2 & V1 & V2 & M1 & M2 & V).
  exists w1, w2. repeat split; auto.
  apply multi_step with (y := t1'); auto.
Qed.

Lemma E_ty_step_r : forall st rho T t1 t2 t2',
  t2 --> t2' -> E_ty st rho T t1 t2' -> E_ty st rho T t1 t2.
Proof.
  intros st rho T t1 t2 t2' Hstep (w1 & w2 & V1 & V2 & M1 & M2 & V).
  exists w1, w2. repeat split; auto.
  apply multi_step with (y := t2'); auto.
Qed.

Lemma E_ty_multi_l : forall st rho T t1 t1' t2,
  t1 -->* t1' -> E_ty st rho T t1' t2 -> E_ty st rho T t1 t2.
Proof.
  intros st rho T t1 t1' t2 H. induction H as [x | x y z Hstep Hrest IH]; intros HE.
  - auto.
  - apply E_ty_step_l with (t1' := y); auto.
Qed.

Lemma E_ty_multi_r : forall st rho T t1 t2 t2',
  t2 -->* t2' -> E_ty st rho T t1 t2' -> E_ty st rho T t1 t2.
Proof.
  intros st rho T t1 t2 t2' H. induction H as [x | x y z Hstep Hrest IH]; intros HE.
  - auto.
  - apply E_ty_step_r with (t2' := y); auto.
Qed.

Lemma E_ty_eq : forall T1 T2 st1 st2 rho1 rho2,
  (forall a b, V_ty st1 rho1 T1 a b <-> V_ty st2 rho2 T2 a b) ->
  forall t1 t2, E_ty st1 rho1 T1 t1 t2 <-> E_ty st2 rho2 T2 t1 t2.
Proof.
  intros T1 T2 st1 st2 rho1 rho2 HV t1 t2. unfold E_ty.
  split; intros (w1 & w2 & V1 & V2 & M1 & M2 & VB); exists w1, w2;
    repeat split; auto;
    apply (proj1 (HV w1 w2)) || apply (proj2 (HV w1 w2)); auto.
Qed.

Lemma E_ty_open_ty_rec : forall T st rho m U, lc_ty_at 0 U ->
  forall t1 t2, E_ty st rho (open_ty_rec m U T) t1 t2 <->
                E_ty (set_stack st m (V_ty st rho U)) rho T t1 t2.
Proof.
  intros T st rho m U HU t1 t2. apply E_ty_eq. intros a b.
  apply V_ty_open_ty_rec; auto.
Qed.

Lemma stack_set_push_empty : forall R i a b,
  set_stack empty_stack 0 R i a b <-> push_stack R empty_stack i a b.
Proof.
  intros R i a b. destruct i as [| j].
  - unfold set_stack, push_stack, empty_stack. simpl. tauto.
  - unfold set_stack, push_stack, empty_stack. simpl. tauto.
Qed.

Lemma E_ty_set_push_empty : forall T R rho t1 t2,
  E_ty (set_stack empty_stack 0 R) rho T t1 t2 <->
  E_ty (push_stack R empty_stack) rho T t1 t2.
Proof.
  intros T R rho t1 t2. apply E_ty_eq. intros a b.
  apply V_ty_stack_ext. intros i a' b'. apply stack_set_push_empty.
Qed.

Lemma E_ty_open_var : forall T X R rho rho',
  rho' X = R ->
  (forall Y, Y <> X -> rho' Y = rho Y) ->
  ~ In X (fta_ty T) ->
  forall t1 t2,
  E_ty empty_stack rho' (open_ty_rec 0 (Ty_FVar X) T) t1 t2 <->
  E_ty (push_stack R empty_stack) rho T t1 t2.
Proof.
  intros T X R rho rho' HX Hdiff Hfresh t1 t2.
  rewrite (E_ty_open_ty_rec T empty_stack rho' 0 (Ty_FVar X) (lc_ty_fvar 0 X) t1 t2).
  simpl. rewrite HX.
  rewrite (E_ty_set_push_empty T R rho' t1 t2).
  apply E_ty_rho_ext.
  intros Y HY a b.
  assert (YX : Y <> X) by (intro E; apply Hfresh; subst Y; auto).
  rewrite (Hdiff Y YX). tauto.
Qed.

Fixpoint fta_context (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (x, T) :: G => fta_ty T ++ fta_context G
  end.

Lemma in_fta_context : forall Gamma x T Y,
  lookup_context x Gamma = Some T -> In Y (fta_ty T) -> In Y (fta_context Gamma).
Proof.
  induction Gamma as [| [z T0] G IH]; intros x T Y Hlook Hin; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x z) eqn:E.
    + apply Nat.eqb_eq in E. subst z. inversion Hlook; subst T0.
      apply in_or_app. auto.
    + apply Nat.eqb_neq in E. apply in_or_app. right.
      simpl in Hlook. apply (IH x T Y); auto.
Qed.

Definition env_rel (Gamma : context) (rho : atom -> rel) (g1 g2 : tmenv) : Prop :=
  forall x T, lookup_context x Gamma = Some T -> E_ty empty_stack rho T (g1 x) (g2 x).

Lemma env_rel_rho_ext : forall Gamma rho rho' g1 g2,
  (forall X, In X (fta_context Gamma) -> forall a b, rho X a b <-> rho' X a b) ->
  env_rel Gamma rho g1 g2 -> env_rel Gamma rho' g1 g2.
Proof.
  intros Gamma rho rho' g1 g2 Hrho Henv x T Hlook.
  apply (proj1 (E_ty_rho_ext T empty_stack rho rho'
                  (fun Y HY a b => Hrho Y (in_fta_context Gamma x T Y Hlook HY) a b)
                  (g1 x) (g2 x))).
  apply Henv. auto.
Qed.

Lemma env_rel_update : forall Gamma rho g1 g2 x T1 u1 u2,
  env_rel Gamma rho g1 g2 -> E_ty empty_stack rho T1 u1 u2 ->
  env_rel (update Gamma x T1) rho (extend_tm g1 x u1) (extend_tm g2 x u2).
Proof.
  intros Gamma rho g1 g2 x T1 u1 u2 Henv HE y T0 Hlook.
  unfold update in Hlook. simpl in Hlook.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst y. inversion Hlook; subst T0.
    rewrite extend_tm_same, extend_tm_same. auto.
  - apply Nat.eqb_neq in E. rewrite extend_tm_diff by auto.
    rewrite extend_tm_diff by auto. apply Henv. auto.
Qed.

(* ============================================================ *)
(* Development: fundamental theorem of the logical relation       *)
(* ============================================================ *)

Lemma fundamental : forall Delta Gamma t T, has_type Delta Gamma t T ->
  forall s1 s2 rho g1 g2,
  (forall X, lc_ty_at 0 (s1 X)) ->
  (forall X, lc_ty_at 0 (s2 X)) ->
  (forall y, lc_tm_at 0 0 (g1 y)) ->
  (forall y, lc_tm_at 0 0 (g2 y)) ->
  env_rel Gamma rho g1 g2 ->
  E_ty empty_stack rho T (subst_tm_env g1 (subst_tm_ty_env s1 t))
                          (subst_tm_env g2 (subst_tm_ty_env s2 t)).
Proof.
  induction 1 as [Delta Gamma x T Hlook Hwf
                | L Delta Gamma T1 t2 T2 Hwf Hbody IHbody
                | Delta Gamma t1 t2 T1 T2 Hfun IHfun Harg IHarg
                | L Delta Gamma t T Hbody IHbody
                | Delta Gamma t T U Hfun IHfun Hwf
                | Delta Gamma t1 t2 T H1 IH1 H2 IH2];
    intros s1 s2 rho g1 g2 Hsig1 Hsig2 Hg1 Hg2 Henv; simpl.
  - (* T_Var *) apply Henv. auto.
  - (* T_Abs *)
    pose proof (T_Abs L Delta Gamma T1 t2 T2 Hwf Hbody) as Hconc.
    pose proof (lc_inst Delta Gamma (tm_abs T1 t2) (Ty_Arrow T1 T2) Hconc s1 g1 Hsig1 Hg1) as Hlc1.
    pose proof (lc_inst Delta Gamma (tm_abs T1 t2) (Ty_Arrow T1 T2) Hconc s2 g2 Hsig2 Hg2) as Hlc2.
    simpl in Hlc1, Hlc2.
    unfold E_ty.
    exists (tm_abs (subst_ty_env s1 T1) (subst_tm_env g1 (subst_tm_ty_env s1 t2))),
           (tm_abs (subst_ty_env s2 T1) (subst_tm_env g2 (subst_tm_ty_env s2 t2))).
    repeat split.
    + apply v_abs; auto.
    + apply v_abs; auto.
    + apply multi_refl.
    + apply multi_refl.
    + intros u1 u2 Hv1 Hv2 HV1.
      destruct (fresh_atom (L ++ ftv_tm t2)) as [x Hx].
      assert (HL : ~ In x L).
      { intro Hin. apply Hx. apply in_or_app. left. auto. }
      assert (Hfv : ~ In x (ftv_tm t2)).
      { intro Hin. apply Hx. apply in_or_app. right. auto. }
      assert (Hg1' : forall y, lc_tm_at 0 0 (extend_tm g1 x u1 y)).
      { intro y. unfold extend_tm. destruct (Nat.eqb y x); auto. apply value_lc; auto. }
      assert (Hg2' : forall y, lc_tm_at 0 0 (extend_tm g2 x u2 y)).
      { intro y. unfold extend_tm. destruct (Nat.eqb y x); auto. apply value_lc; auto. }
      assert (Henv' : env_rel (update Gamma x T1) rho (extend_tm g1 x u1) (extend_tm g2 x u2)).
      { apply env_rel_update.
        - exact Henv.
        - apply E_ty_of_V; auto. }
      pose proof (IHbody x HL s1 s2 rho (extend_tm g1 x u1) (extend_tm g2 x u2)
                    Hsig1 Hsig2 Hg1' Hg2' Henv') as HIH.
      unfold open_tm in HIH.
      rewrite (subst_tm_ty_env_open_tm_rec t2 s1 (tm_fvar x) 0) in HIH.
      rewrite (subst_tm_ty_env_open_tm_rec t2 s2 (tm_fvar x) 0) in HIH.
      simpl in HIH.
      assert (Hfv1 : ~ In x (ftv_tm (subst_tm_ty_env s1 t2))).
      { rewrite ftv_tm_subst_ty. auto. }
      assert (Hfv2 : ~ In x (ftv_tm (subst_tm_ty_env s2 t2))).
      { rewrite ftv_tm_subst_ty. auto. }
      rewrite (subst_tm_env_open_tm_rec (subst_tm_ty_env s1 t2) g1 x u1 0 Hfv1 Hg1 (value_lc u1 Hv1)) in HIH.
      rewrite (subst_tm_env_open_tm_rec (subst_tm_ty_env s2 t2) g2 x u2 0 Hfv2 Hg2 (value_lc u2 Hv2)) in HIH.
      eapply E_ty_multi_l.
      * apply multi_app_abs; auto.
      * eapply E_ty_multi_r.
        -- apply multi_app_abs; auto.
        -- exact HIH.
  - (* T_App *)
    pose proof (lc_inst Delta Gamma t2 T1 Harg s1 g1 Hsig1 Hg1) as Hlc2a.
    pose proof (lc_inst Delta Gamma t2 T1 Harg s2 g2 Hsig2 Hg2) as Hlc2b.
    destruct (IHfun s1 s2 rho g1 g2 Hsig1 Hsig2 Hg1 Hg2 Henv)
      as (w1 & w2 & Vw1 & Vw2 & M1 & M2 & VF).
    destruct (IHarg s1 s2 rho g1 g2 Hsig1 Hsig2 Hg1 Hg2 Henv)
      as (u1 & u2 & Vu1 & Vu2 & N1 & N2 & VA).
    destruct (VF u1 u2 Vu1 Vu2 VA) as (z1 & z2 & Vz1 & Vz2 & R1 & R2 & VZ).
    exists z1, z2. repeat split; auto.
    + eapply multi_trans.
      * eapply multi_app_l; eauto.
      * eapply multi_trans.
        -- eapply multi_app_r; eauto.
        -- auto.
    + eapply multi_trans.
      * eapply multi_app_l; eauto.
      * eapply multi_trans.
        -- eapply multi_app_r; eauto.
        -- auto.
  - (* T_TAbs *)
    pose proof (T_TAbs L Delta Gamma t T Hbody) as Hconc.
    pose proof (lc_inst Delta Gamma (tm_tabs t) (Ty_All T) Hconc s1 g1 Hsig1 Hg1) as Hlc1.
    pose proof (lc_inst Delta Gamma (tm_tabs t) (Ty_All T) Hconc s2 g2 Hsig2 Hg2) as Hlc2.
    simpl in Hlc1, Hlc2.
    unfold E_ty.
    exists (tm_tabs (subst_tm_env g1 (subst_tm_ty_env s1 t))),
           (tm_tabs (subst_tm_env g2 (subst_tm_ty_env s2 t))).
    repeat split.
    + apply v_tabs; auto.
    + apply v_tabs; auto.
    + apply multi_refl.
    + apply multi_refl.
    + intros R U1 U2 HU1 HU2.
      destruct (fresh_atom (L ++ fta_tm t ++ fta_ty T ++ fta_context Gamma)) as [X HX].
      assert (HL : ~ In X L).
      { intro Hin. apply HX. apply in_or_app. left. auto. }
      assert (Hfta : ~ In X (fta_tm t)).
      { intro Hin. apply HX. apply in_or_app. right. apply in_or_app. left. auto. }
      assert (HfT : ~ In X (fta_ty T)).
      { intro Hin. apply HX. apply in_or_app. right. apply in_or_app. right.
        apply in_or_app. left. auto. }
      assert (HfG : ~ In X (fta_context Gamma)).
      { intro Hin. apply HX. apply in_or_app. right. apply in_or_app. right.
        apply in_or_app. right. auto. }
      assert (Henv' : env_rel Gamma (extend_rho rho X R) g1 g2).
      { apply env_rel_rho_ext with (rho := rho).
        - intros Y HY a b. assert (YX : Y <> X) by (intro E; apply HfG; subst Y; auto).
          rewrite (extend_rho_diff rho X R Y YX). tauto.
        - exact Henv. }
      assert (Hsig1' : forall Y, lc_ty_at 0 (extend_ty s1 X U1 Y)).
      { intro Y. unfold extend_ty. destruct (Nat.eqb Y X); auto. }
      assert (Hsig2' : forall Y, lc_ty_at 0 (extend_ty s2 X U2 Y)).
      { intro Y. unfold extend_ty. destruct (Nat.eqb Y X); auto. }
      pose proof (IHbody X HL (extend_ty s1 X U1) (extend_ty s2 X U2) (extend_rho rho X R)
                    g1 g2 Hsig1' Hsig2' Hg1 Hg2 Henv') as HIH.
      unfold open_tm_ty in HIH.
      rewrite (subst_tm_ty_env_open_tm_ty_rec t s1 X U1 0 Hfta Hsig1 HU1) in HIH.
      rewrite (subst_tm_ty_env_open_tm_ty_rec t s2 X U2 0 Hfta Hsig2 HU2) in HIH.
      rewrite (subst_tm_env_open_tm_ty_rec (subst_tm_ty_env s1 t) g1 U1 0 Hg1) in HIH.
      rewrite (subst_tm_env_open_tm_ty_rec (subst_tm_ty_env s2 t) g2 U2 0 Hg2) in HIH.
      apply (proj1 (E_ty_open_var T X R rho (extend_rho rho X R)
                     (extend_rho_same rho X R)
                     (fun Y HY => extend_rho_diff rho X R Y HY) HfT
                     (open_tm_ty_rec 0 U1 (subst_tm_env g1 (subst_tm_ty_env s1 t)))
                     (open_tm_ty_rec 0 U2 (subst_tm_env g2 (subst_tm_ty_env s2 t))))) in HIH.
      eapply E_ty_multi_l.
      * apply multi_tapp_tabs; auto.
      * eapply E_ty_multi_r.
        -- apply multi_tapp_tabs; auto.
        -- exact HIH.
  - (* T_TApp *)
    pose proof (lc_inst Delta Gamma t (Ty_All T) Hfun s1 g1 Hsig1 Hg1) as Hlc1.
    pose proof (lc_inst Delta Gamma t (Ty_All T) Hfun s2 g2 Hsig2 Hg2) as Hlc2.
    destruct (IHfun s1 s2 rho g1 g2 Hsig1 Hsig2 Hg1 Hg2 Henv)
      as (w1 & w2 & Vw1 & Vw2 & M1 & M2 & VF).
    assert (HU : lc_ty_at 0 U) by (apply wf_ty_lc with (Delta := Delta); auto).
    assert (HU1 : lc_ty_at 0 (subst_ty_env s1 U)).
    { apply lc_ty_subst with (K := 0) (K0 := 0) (s := s1); auto; lia. }
    assert (HU2 : lc_ty_at 0 (subst_ty_env s2 U)).
    { apply lc_ty_subst with (K := 0) (K0 := 0) (s := s2); auto; lia. }
    destruct (VF (V_ty empty_stack rho U) (subst_ty_env s1 U) (subst_ty_env s2 U) HU1 HU2)
      as (z1 & z2 & Vz1 & Vz2 & R1 & R2 & VZ).
    assert (HZ : E_ty empty_stack rho (open_ty_rec 0 U T) z1 z2).
    { apply (proj2 (E_ty_open_ty_rec T empty_stack rho 0 U HU z1 z2)).
      apply (proj2 (E_ty_set_push_empty T (V_ty empty_stack rho U) rho z1 z2)).
      apply E_ty_of_V; auto. }
    eapply E_ty_multi_l.
    + apply multi_tapp; [exact M1 | exact HU1].
    + eapply E_ty_multi_r.
      * apply multi_tapp; [exact M2 | exact HU2].
      * eapply E_ty_multi_l.
        -- exact R1.
        -- eapply E_ty_multi_r.
           ++ exact R2.
           ++ exact HZ.
  - (* T_Choice *)
    pose proof (lc_inst Delta Gamma t1 T H1 s1 g1 Hsig1 Hg1) as Hlc1a.
    pose proof (lc_inst Delta Gamma t2 T H2 s1 g1 Hsig1 Hg1) as Hlc2a.
    pose proof (lc_inst Delta Gamma t1 T H1 s2 g2 Hsig2 Hg2) as Hlc1b.
    pose proof (lc_inst Delta Gamma t2 T H2 s2 g2 Hsig2 Hg2) as Hlc2b.
    destruct (IH1 s1 s2 rho g1 g2 Hsig1 Hsig2 Hg1 Hg2 Henv)
      as (w1 & w2 & Vw1 & Vw2 & M1 & M2 & V).
    exists w1, w2. repeat split; auto.
    + eapply multi_trans.
      * apply multi_choice_l; auto.
      * auto.
    + eapply multi_trans.
      * apply multi_choice_l; auto.
      * auto.
Qed.

(* ============================================================ *)
(* The target theorem                                            *)
(* ============================================================ *)

Theorem polymorphic_identity_theorem_for_free : forall t,
  has_type [] empty t
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) ->
  forall U v,
    wf_ty [] U ->
    value v ->
    has_type [] empty v U ->
    tm_app (tm_tapp t U) v -->* v.
Proof.
  intros t Ht U v HU Hv HvU.
  assert (Henv : env_rel empty empty_rho (fun x => tm_fvar x) (fun x => tm_fvar x)).
  { intros x T Hlook. simpl in Hlook. discriminate. }
  pose proof (fundamental [] empty t (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) Ht
                (fun X => Ty_FVar X) (fun X => Ty_FVar X) empty_rho
                (fun x => tm_fvar x) (fun x => tm_fvar x)
                (fun X => lc_ty_fvar 0 X) (fun X => lc_ty_fvar 0 X)
                (fun y => lc_tm_fvar 0 0 y) (fun y => lc_tm_fvar 0 0 y)
                Henv) as HF.
  rewrite subst_tm_env_id in HF.
  rewrite subst_tm_ty_env_id in HF.
  destruct HF as (w1 & w2 & Vw1 & Vw2 & M1 & M2 & VF).
  assert (HlcU : lc_ty_at 0 U) by (apply wf_ty_lc with (Delta := []); auto).
  assert (Hlcv : lc_tm_at 0 0 v) by (apply value_lc; auto).
  destruct (VF (fun a b => a -->* v /\ b -->* v) U U HlcU HlcU)
    as (z1 & z2 & Vz1 & Vz2 & R1 & R2 & VZ).
  assert (Hvv : (fun a b => a -->* v /\ b -->* v) v v).
  { split; apply multi_refl. }
  destruct (VZ v v Hv Hv Hvv) as (q1 & q2 & Vq1 & Vq2 & S1 & S2 & VQ).
  destruct VQ as [Q1 Q2].
  eapply multi_trans.
  - apply multi_app_l.
    + apply multi_tapp; [exact M1 | exact HlcU].
    + exact Hlcv.
  - eapply multi_trans.
    + apply multi_app_l; [exact R1 | exact Hlcv].
    + eapply multi_trans.
      * exact S1.
      * exact Q1.
Qed.

End SystemFParametricityNondeterminismHardTask.
