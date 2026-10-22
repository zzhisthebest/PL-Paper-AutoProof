From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
From Stdlib Require Import ZArith.BinInt.

Module SystemFRefinementIfNonDeterminism.

Import ListNotations.

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

  | Ty_All : ty -> ty
  | Ty_Int : ty
  | Ty_Bool : ty.

Notation "'Int'" := Ty_Int
  (in custom systemf_ty at level 0) : systemf_scope.

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

Inductive integer_operator : Type := Int_Add | Int_Sub | Int_Mul.

Definition eval_integer_operator (op : integer_operator) (n m : Z) : Z :=
  match op with
  | Int_Add => (n + m)%Z
  | Int_Sub => (n - m)%Z
  | Int_Mul => (n * m)%Z
  end.

Inductive tm : Type :=
  | tm_bvar : nat -> tm
  | tm_fvar : atom -> tm
  | tm_abs : ty -> tm -> tm
  | tm_app : tm -> tm -> tm

  | tm_tabs : tm -> tm

  | tm_tapp : tm -> ty -> tm
  | tm_int : Z -> tm
  | tm_div : tm -> tm -> tm
  | tm_arith : integer_operator -> tm -> tm -> tm
  | tm_choice : tm -> tm -> tm
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm -> tm -> tm -> tm.

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
Notation "t1 '/' t2" := (tm_div t1 t2)
  (in custom systemf_tm at level 20, left associativity) : systemf_scope.

Fixpoint open_ty_rec (k : nat) (U T : ty) : ty :=
  match T with
  | Ty_BVar i => if Nat.eqb k i then U else Ty_BVar i
  | Ty_FVar X => Ty_FVar X
  | Ty_Arrow T1 T2 =>
      Ty_Arrow (open_ty_rec k U T1) (open_ty_rec k U T2)
  | Ty_All T1 => Ty_All (open_ty_rec (S k) U T1)
  | Ty_Int => Ty_Int
  | Ty_Bool => Ty_Bool
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
  | tm_int n => tm_int n
  | tm_div t1 t2 => tm_div (open_tm_rec k u t1) (open_tm_rec k u t2)
  | tm_arith op t1 t2 => tm_arith op (open_tm_rec k u t1) (open_tm_rec k u t2)
  | tm_choice t1 t2 => tm_choice (open_tm_rec k u t1) (open_tm_rec k u t2)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (open_tm_rec k u t1) (open_tm_rec k u t2) (open_tm_rec k u t3)
  end.

Definition open_tm (t u : tm) : tm := open_tm_rec 0 u t.

Fixpoint fv_ty (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow T1 T2 => fv_ty T1 ++ fv_ty T2
  | Ty_All T1 => fv_ty T1
  | Ty_Int => []
  | Ty_Bool => []
  end.

Fixpoint fv_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs _ t1 => fv_tm t1
  | tm_app t1 t2 => fv_tm t1 ++ fv_tm t2
  | tm_tabs t1 => fv_tm t1
  | tm_tapp t1 _ => fv_tm t1
  | tm_int _ => []
  | tm_div t1 t2 => fv_tm t1 ++ fv_tm t2
  | tm_arith op t1 t2 => fv_tm t1 ++ fv_tm t2
  | tm_choice t1 t2 => fv_tm t1 ++ fv_tm t2
  | tm_true => []
  | tm_false => []
  | tm_if t1 t2 t3 => fv_tm t1 ++ fv_tm t2 ++ fv_tm t3
  end.

Fixpoint ftv_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_fvar _ => []
  | tm_abs T t1 => fv_ty T ++ ftv_tm t1
  | tm_app t1 t2 => ftv_tm t1 ++ ftv_tm t2
  | tm_tabs t1 => ftv_tm t1
  | tm_tapp t1 T => ftv_tm t1 ++ fv_ty T
  | tm_int _ => []
  | tm_div t1 t2 => ftv_tm t1 ++ ftv_tm t2
  | tm_arith op t1 t2 => ftv_tm t1 ++ ftv_tm t2
  | tm_choice t1 t2 => ftv_tm t1 ++ ftv_tm t2
  | tm_true => []
  | tm_false => []
  | tm_if t1 t2 t3 => ftv_tm t1 ++ ftv_tm t2 ++ ftv_tm t3
  end.

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
  | tm_int n => tm_int n
  | tm_div t1 t2 => tm_div (open_tm_ty_rec k U t1) (open_tm_ty_rec k U t2)
  | tm_arith op t1 t2 => tm_arith op (open_tm_ty_rec k U t1) (open_tm_ty_rec k U t2)
  | tm_choice t1 t2 => tm_choice (open_tm_ty_rec k U t1) (open_tm_ty_rec k U t2)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (open_tm_ty_rec k U t1) (open_tm_ty_rec k U t2) (open_tm_ty_rec k U t3)
  end.

Definition open_tm_ty (t : tm) (U : ty) : tm :=
  open_tm_ty_rec 0 U t.

Fixpoint ty_subst (X : atom) (U T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar Y => if Nat.eqb X Y then U else Ty_FVar Y
  | Ty_Arrow T1 T2 => Ty_Arrow (ty_subst X U T1) (ty_subst X U T2)
  | Ty_All T1 => Ty_All (ty_subst X U T1)
  | Ty_Int => Ty_Int
  | Ty_Bool => Ty_Bool
  end.

Fixpoint tm_ty_subst (X : atom) (U : ty) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T t1 => tm_abs (ty_subst X U T) (tm_ty_subst X U t1)
  | tm_app t1 t2 => tm_app (tm_ty_subst X U t1) (tm_ty_subst X U t2)
  | tm_tabs t1 => tm_tabs (tm_ty_subst X U t1)
  | tm_tapp t1 T => tm_tapp (tm_ty_subst X U t1) (ty_subst X U T)
  | tm_int n => tm_int n
  | tm_div t1 t2 => tm_div (tm_ty_subst X U t1) (tm_ty_subst X U t2)
  | tm_arith op t1 t2 => tm_arith op (tm_ty_subst X U t1) (tm_ty_subst X U t2)
  | tm_choice t1 t2 => tm_choice (tm_ty_subst X U t1) (tm_ty_subst X U t2)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (tm_ty_subst X U t1) (tm_ty_subst X U t2) (tm_ty_subst X U t3)
  end.

Fixpoint tm_subst (x : atom) (s t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar y => if Nat.eqb x y then s else tm_fvar y
  | tm_abs T t1 => tm_abs T (tm_subst x s t1)
  | tm_app t1 t2 => tm_app (tm_subst x s t1) (tm_subst x s t2)
  | tm_tabs t1 => tm_tabs (tm_subst x s t1)
  | tm_tapp t1 T => tm_tapp (tm_subst x s t1) T
  | tm_int n => tm_int n
  | tm_div t1 t2 => tm_div (tm_subst x s t1) (tm_subst x s t2)
  | tm_arith op t1 t2 => tm_arith op (tm_subst x s t1) (tm_subst x s t2)
  | tm_choice t1 t2 => tm_choice (tm_subst x s t1) (tm_subst x s t2)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (tm_subst x s t1) (tm_subst x s t2) (tm_subst x s t3)
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
      lc_ty_at k (Ty_All T)
  | lc_ty_int : forall k, lc_ty_at k Ty_Int
  | lc_ty_bool : forall k, lc_ty_at k Ty_Bool.

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
  | lc_tm_int : forall K k (n : Z), lc_tm_at K k (tm_int n)
  | lc_tm_div : forall K k t1 t2,
      lc_tm_at K k t1 ->
      lc_tm_at K k t2 ->
      lc_tm_at K k (tm_div t1 t2)
  | lc_tm_arith : forall K k op t1 t2,
      lc_tm_at K k t1 ->
      lc_tm_at K k t2 ->
      lc_tm_at K k (tm_arith op t1 t2)
  | lc_tm_choice : forall K k t1 t2,
      lc_tm_at K k t1 -> lc_tm_at K k t2 -> lc_tm_at K k (tm_choice t1 t2)
  | lc_tm_true : forall K k, lc_tm_at K k tm_true
  | lc_tm_false : forall K k, lc_tm_at K k tm_false
  | lc_tm_if : forall K k t1 t2 t3,
      lc_tm_at K k t1 -> lc_tm_at K k t2 -> lc_tm_at K k t3 ->
      lc_tm_at K k (tm_if t1 t2 t3).

Definition locally_closed_tm (t : tm) : Prop := lc_tm_at 0 0 t.

Inductive value : tm -> Prop :=
  | v_abs : forall T t,
      locally_closed_tm (tm_abs T t) ->
      value (tm_abs T t)
  | v_tabs : forall t,
      locally_closed_tm (tm_tabs t) ->
      value (tm_tabs t)
  | v_int : forall n : Z, value (tm_int n)
  | v_true : value tm_true
  | v_false : value tm_false.

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
  | ST_Div1 : forall t1 t1' t2,
      t1 --> t1' ->
      locally_closed_tm t2 ->
      tm_div t1 t2 --> tm_div t1' t2
  | ST_Div2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      tm_div v1 t2 --> tm_div v1 t2'
  | ST_DivInt : forall n m : Z,
      m <> 0%Z ->
      tm_div (tm_int n) (tm_int m) --> tm_int (Z.div n m)
  | ST_Arith1 : forall op t1 t1' t2,
      t1 --> t1' -> locally_closed_tm t2 ->
      tm_arith op t1 t2 --> tm_arith op t1' t2
  | ST_Arith2 : forall op v1 t2 t2',
      value v1 -> t2 --> t2' ->
      tm_arith op v1 t2 --> tm_arith op v1 t2'
  | ST_ArithInt : forall op n m,
      tm_arith op (tm_int n) (tm_int m) -->
      tm_int (eval_integer_operator op n m)
  | ST_ChoiceLeft : forall t1 t2,
      locally_closed_tm t1 -> locally_closed_tm t2 ->
      tm_choice t1 t2 --> t1
  | ST_ChoiceRight : forall t1 t2,
      locally_closed_tm t1 -> locally_closed_tm t2 ->
      tm_choice t1 t2 --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' -> locally_closed_tm t2 -> locally_closed_tm t3 ->
      tm_if t1 t2 t3 --> tm_if t1' t2 t3
  | ST_IfTrue : forall t2 t3,
      locally_closed_tm t2 -> locally_closed_tm t3 -> tm_if tm_true t2 t3 --> t2
  | ST_IfFalse : forall t2 t3,
      locally_closed_tm t2 -> locally_closed_tm t3 -> tm_if tm_false t2 t3 --> t3
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
      wf_ty Delta (Ty_All T)
  | WF_Int : forall Delta, wf_ty Delta Ty_Int
  | WF_Bool : forall Delta, wf_ty Delta Ty_Bool.

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
  | T_Int : forall Delta Gamma (n : Z),
      has_type Delta Gamma (tm_int n) Ty_Int
  | T_Div : forall Delta Gamma t1 t2,
      has_type Delta Gamma t1 Ty_Int ->
      has_type Delta Gamma t2 Ty_Int ->
      has_type Delta Gamma (tm_div t1 t2) Ty_Int
  | T_Arith : forall Delta Gamma op t1 t2,
      has_type Delta Gamma t1 Ty_Int ->
      has_type Delta Gamma t2 Ty_Int ->
      has_type Delta Gamma (tm_arith op t1 t2) Ty_Int
  | T_Choice : forall Delta Gamma t1 t2 T,
      has_type Delta Gamma t1 T -> has_type Delta Gamma t2 T ->
      has_type Delta Gamma (tm_choice t1 t2) T
  | T_True : forall Delta Gamma, has_type Delta Gamma tm_true Ty_Bool
  | T_False : forall Delta Gamma, has_type Delta Gamma tm_false Ty_Bool
  | T_If : forall Delta Gamma t1 t2 t3 T,
      has_type Delta Gamma t1 Ty_Bool -> has_type Delta Gamma t2 T ->
      has_type Delta Gamma t3 T -> has_type Delta Gamma (tm_if t1 t2 t3) T.

Fixpoint max_atom (L : list atom) : atom :=
  match L with
  | [] => 0
  | x :: L' => Nat.max x (max_atom L')
  end.

Definition fresh (L : list atom) : atom := S (max_atom L).

Lemma in_le_max_atom : forall x L,
  In x L -> x <= max_atom L.
Proof.
  induction L; simpl; intros.
  - contradiction.
  - destruct H as [H | H].
    + subst. lia.
    + specialize (IHL H). lia.
Qed.

Lemma fresh_notin : forall L,
  ~ In (fresh L) L.
Proof.
  unfold fresh. intros L H.
  pose proof (in_le_max_atom _ _ H). lia.
Qed.

End SystemFRefinementIfNonDeterminism.

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
Module SystemFRefinementIfNonDeterminismInfrastructure.
Import ListNotations.
Import SystemFRefinementIfNonDeterminism.

Fixpoint ftv_context (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (_, T) :: Gamma' => fv_ty T ++ ftv_context Gamma'
  end.

Fixpoint dom_context (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (x, _) :: Gamma' => x :: dom_context Gamma'
  end.

Lemma lookup_context_update_eq : forall Gamma x T,
  lookup_context x <{ x |-> $(T); Gamma }> = Some T.
Proof.
  intros. unfold update. simpl. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma lookup_context_update_neq : forall Gamma x y T,
  x <> y ->
  lookup_context y <{ x |-> $(T); Gamma }> = lookup_context y Gamma.
Proof.
  intros. unfold update. simpl.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. exfalso. apply H. symmetry. exact E.
  - reflexivity.
Qed.

Lemma lc_ty_at_monotone : forall k k' T,
  lc_ty_at k T ->
  k <= k' ->
  lc_ty_at k' T.
Proof.
  intros k k' T Hlc. generalize dependent k'.
  induction Hlc; intros k' Hle.
  - apply lc_ty_bvar. lia.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; eauto.
  - apply lc_ty_all. apply IHHlc. lia.
  - apply lc_ty_int.
  - constructor.
Qed.

Lemma lc_tm_at_monotone : forall K k K' k' t,
  lc_tm_at K k t ->
  K <= K' ->
  k <= k' ->
  lc_tm_at K' k' t.
Proof.
  intros K k K' k' t Hlc. generalize dependent K'. generalize dependent k'.
  induction Hlc; intros k' Hk K' HK.
  - apply lc_tm_bvar. lia.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + eapply lc_ty_at_monotone; eauto.
    + apply IHHlc; lia.
  - apply lc_tm_app; eauto.
  - apply lc_tm_tabs. apply IHHlc; lia.
  - apply lc_tm_tapp.
    + apply IHHlc; assumption.
    + eapply lc_ty_at_monotone; eauto.
  - apply lc_tm_int.
  - apply lc_tm_div; eauto.
  - apply lc_tm_arith; eauto.
  - try (inversion Hlc; subst). apply lc_tm_choice; eauto.
  - constructor.
  - constructor.
  - try (inversion Hlc; subst). apply lc_tm_if; eauto.
Qed.

Lemma open_ty_rec_lc_at : forall T k U,
  lc_ty_at k T ->
  open_ty_rec k U T = T.
Proof.
  intros T k U Hlc. induction Hlc; simpl; try rewrite ?IHHlc1, ?IHHlc2, ?IHHlc3;
    try reflexivity.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + reflexivity.
  - rewrite IHHlc. reflexivity.
Qed.

Lemma open_tm_rec_lc_at : forall t K k u,
  lc_tm_at K k t ->
  open_tm_rec k u t = t.
Proof.
  intros t K k u Hlc. induction Hlc; simpl;
    try rewrite ?IHHlc, ?IHHlc1, ?IHHlc2, ?IHHlc3; try reflexivity.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + reflexivity.
Qed.

Lemma open_tm_ty_rec_lc_at : forall t K k U,
  lc_tm_at K k t ->
  open_tm_ty_rec K U t = t.
Proof.
  intros t K k U Hlc. induction Hlc; simpl;
    try rewrite ?IHHlc1, ?IHHlc2, ?IHHlc3; try reflexivity.
  - erewrite open_ty_rec_lc_at; eauto. rewrite IHHlc. reflexivity.
  - rewrite IHHlc. reflexivity.
  - rewrite IHHlc. erewrite open_ty_rec_lc_at; eauto.
Qed.

Lemma lc_ty_at_open_inv : forall T k X,
  lc_ty_at k (open_ty_rec k (Ty_FVar X) T) ->
  lc_ty_at (S k) T.
Proof.
  induction T; intros k X Hlc; simpl in Hlc.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. apply lc_ty_bvar. lia.
    + inversion Hlc; subst. apply lc_ty_bvar. lia.
  - apply lc_ty_fvar.
  - inversion Hlc; subst. apply lc_ty_arrow.
    + eapply IHT1; eassumption.
    + eapply IHT2; eassumption.
  - inversion Hlc; subst. apply lc_ty_all. eapply IHT; eauto.
  - apply lc_ty_int.
  - constructor.
Qed.

Lemma lc_ty_at_open : forall T k U,
  lc_ty_at (S k) T ->
  lc_ty_at k U ->
  lc_ty_at k (open_ty_rec k U T).
Proof.
  induction T; intros k U HT HU; simpl.
  - inversion HT; subst.
    destruct (Nat.eqb k n) eqn:E.
    + exact HU.
    + apply lc_ty_bvar. apply Nat.eqb_neq in E. lia.
  - apply lc_ty_fvar.
  - inversion HT; subst. apply lc_ty_arrow; eauto.
  - inversion HT; subst. apply lc_ty_all.
    apply IHT.
    + assumption.
    + eapply lc_ty_at_monotone.
      * exact HU.
      * lia.
  - apply lc_ty_int.
  - constructor.
Qed.

Lemma lc_tm_at_open_tm_inv : forall t K k x,
  lc_tm_at K k (open_tm_rec k (tm_fvar x) t) ->
  lc_tm_at K (S k) t.
Proof.
  induction t; intros K k x Hlc; simpl in Hlc.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. apply lc_tm_bvar. lia.
    + inversion Hlc; subst. apply lc_tm_bvar. lia.
  - apply lc_tm_fvar.
  - inversion Hlc; subst. apply lc_tm_abs; eauto.
  - inversion Hlc; subst. apply lc_tm_app; eauto.
  - inversion Hlc; subst. apply lc_tm_tabs; eauto.
  - inversion Hlc; subst. apply lc_tm_tapp; eauto.
  - apply lc_tm_int.
  - inversion Hlc; subst. apply lc_tm_div; eauto.
  - inversion Hlc; subst. apply lc_tm_arith; eauto.
  - try (inversion Hlc; subst). apply lc_tm_choice; eauto.
  - constructor.
  - constructor.
  - try (inversion Hlc; subst). apply lc_tm_if; eauto.
Qed.

Lemma lc_tm_at_open_ty_inv : forall t K k X,
  lc_tm_at K k (open_tm_ty_rec K (Ty_FVar X) t) ->
  lc_tm_at (S K) k t.
Proof.
  induction t; intros K k X Hlc; simpl in Hlc.
  - inversion Hlc; subst. apply lc_tm_bvar. assumption.
  - apply lc_tm_fvar.
  - inversion Hlc; subst. apply lc_tm_abs.
    + eapply lc_ty_at_open_inv; eauto.
    + eapply IHt; eauto.
  - inversion Hlc; subst. apply lc_tm_app; eauto.
  - inversion Hlc; subst. apply lc_tm_tabs. eapply IHt; eauto.
  - inversion Hlc; subst. apply lc_tm_tapp.
    + eapply IHt; eauto.
    + eapply lc_ty_at_open_inv; eauto.
  - apply lc_tm_int.
  - inversion Hlc; subst. apply lc_tm_div; eauto.
  - inversion Hlc; subst. apply lc_tm_arith; eauto.
  - try (inversion Hlc; subst). apply lc_tm_choice; eauto.
  - constructor.
  - constructor.
  - try (inversion Hlc; subst). apply lc_tm_if; eauto.
Qed.

Definition type_substitution := atom -> ty.

Definition term_substitution := atom -> tm.

Definition type_subst_update
    (theta : type_substitution) (X : atom) (U : ty) : type_substitution :=
  fun Y => if Nat.eqb X Y then U else theta Y.

Definition term_subst_update
    (gamma : term_substitution) (x : atom) (u : tm) : term_substitution :=
  fun y => if Nat.eqb x y then u else gamma y.

Fixpoint instantiate_ty (theta : type_substitution) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => theta X
  | Ty_Arrow T1 T2 =>
      Ty_Arrow (instantiate_ty theta T1) (instantiate_ty theta T2)
  | Ty_All T1 => Ty_All (instantiate_ty theta T1)
  | Ty_Int => Ty_Int
  | Ty_Bool => Ty_Bool
  end.

Fixpoint instantiate
    (theta : type_substitution) (gamma : term_substitution) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => gamma x
  | tm_abs T t1 => tm_abs (instantiate_ty theta T) (instantiate theta gamma t1)
  | tm_app t1 t2 => tm_app (instantiate theta gamma t1) (instantiate theta gamma t2)
  | tm_tabs t1 => tm_tabs (instantiate theta gamma t1)
  | tm_tapp t1 T => tm_tapp (instantiate theta gamma t1) (instantiate_ty theta T)
  | tm_int n => tm_int n
  | tm_div t1 t2 => tm_div (instantiate theta gamma t1) (instantiate theta gamma t2)
  | tm_arith op t1 t2 => tm_arith op (instantiate theta gamma t1) (instantiate theta gamma t2)
  | tm_choice t1 t2 => tm_choice (instantiate theta gamma t1) (instantiate theta gamma t2)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (instantiate theta gamma t1) (instantiate theta gamma t2) (instantiate theta gamma t3)
  end.

Definition type_substitution_closed (theta : type_substitution) : Prop :=
  forall X : atom, locally_closed_ty (theta X).

Definition term_substitution_closed (gamma : term_substitution) : Prop :=
  forall x : atom, locally_closed_tm (gamma x).

Lemma type_subst_update_closed : forall theta X U,
  type_substitution_closed theta ->
  locally_closed_ty U ->
  type_substitution_closed (type_subst_update theta X U).
Proof.
  intros theta X U Htheta HU Y. unfold type_subst_update.
  destruct (Nat.eqb X Y); auto.
Qed.

Lemma term_subst_update_closed : forall gamma x u,
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  term_substitution_closed (term_subst_update gamma x u).
Proof.
  intros gamma x u Hgamma Hu y. unfold term_subst_update.
  destruct (Nat.eqb x y); auto.
Qed.

Definition identity_type_substitution : type_substitution :=
  fun X : atom => Ty_FVar X.

Definition identity_term_substitution : term_substitution :=
  fun x : atom => tm_fvar x.

Lemma identity_type_substitution_closed :
  type_substitution_closed identity_type_substitution.
Proof.
  intros X. apply lc_ty_fvar.
Qed.

Lemma identity_term_substitution_closed :
  term_substitution_closed identity_term_substitution.
Proof.
  intros x. apply lc_tm_fvar.
Qed.

End SystemFRefinementIfNonDeterminismInfrastructure.

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
Module SystemFRefinementIfNonDeterminismCoreTyping.
Import ListNotations.
Import SystemFRefinementIfNonDeterminism.
Import SystemFRefinementIfNonDeterminismInfrastructure.

Definition ty_context_included (Delta Delta' : ty_context) : Prop :=
  forall X, In X Delta -> In X Delta'.

Definition context_included (Gamma Gamma' : context) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    lookup_context x Gamma' = Some T.

Definition type_substitution_wf
    (Delta Delta' : ty_context) (theta : type_substitution) : Prop :=
  forall X, In X Delta -> wf_ty Delta' (theta X).

Definition context_wf (Delta : ty_context) (Gamma : context) : Prop :=
  forall x T, lookup_context x Gamma = Some T -> wf_ty Delta T.

Definition term_substitution_typed
    (Gamma : context) (Delta' : ty_context) (Gamma' : context)
    (theta : type_substitution) (gamma : term_substitution) : Prop :=
  forall x T,
    lookup_context x Gamma = Some T ->
    has_type Delta' Gamma' (gamma x) (instantiate_ty theta T).

Lemma notin_dom_lookup_none : forall x Gamma,
  ~ In x (dom_context Gamma) -> lookup_context x Gamma = None.
Proof.
  intros x Gamma. induction Gamma as [|[y T] Gamma IH]; intros Hfresh; simpl in *.
  - reflexivity.
  - assert (Hxy : x <> y) by intuition.
    rewrite (proj2 (Nat.eqb_neq x y)) by assumption.
    apply IH. intuition.
Qed.

End SystemFRefinementIfNonDeterminismCoreTyping.

From Stdlib Require Import Arith.PeanoNat Lists.List ZArith.BinInt.
Module SystemFRefinementIfNonDeterminismLogic.
Import ListNotations SystemFRefinementIfNonDeterminism.

Inductive qualifier : Type :=
  | Pred_True : qualifier
  | Pred_False : qualifier
  | Pred_Eq : tm -> tm -> qualifier
  | Pred_Lt : tm -> tm -> qualifier
  | Pred_Le : tm -> tm -> qualifier
  | Pred_And : qualifier -> qualifier -> qualifier
  | Pred_Or : qualifier -> qualifier -> qualifier
  | Pred_Not : qualifier -> qualifier.

Definition Pred_Ne (t1 t2 : tm) : qualifier := Pred_Not (Pred_Eq t1 t2).
Definition Pred_Gt (t1 t2 : tm) : qualifier := Pred_Lt t2 t1.
Definition Pred_Ge (t1 t2 : tm) : qualifier := Pred_Le t2 t1.

Definition Pred_Implies (p q : qualifier) : qualifier :=
  Pred_Or (Pred_Not p) q.

Fixpoint open_pred_tm_rec (k : nat) (u : tm) (p : qualifier) : qualifier :=
  match p with
  | Pred_True => Pred_True
  | Pred_False => Pred_False
  | Pred_Eq t1 t2 =>
      Pred_Eq (open_tm_rec k u t1) (open_tm_rec k u t2)
  | Pred_Lt t1 t2 =>
      Pred_Lt (open_tm_rec k u t1) (open_tm_rec k u t2)
  | Pred_Le t1 t2 =>
      Pred_Le (open_tm_rec k u t1) (open_tm_rec k u t2)
  | Pred_And p1 p2 =>
      Pred_And (open_pred_tm_rec k u p1) (open_pred_tm_rec k u p2)
  | Pred_Or p1 p2 =>
      Pred_Or (open_pred_tm_rec k u p1) (open_pred_tm_rec k u p2)
  | Pred_Not p1 => Pred_Not (open_pred_tm_rec k u p1)
  end.

Definition open_qualifier_tm_rec (k : nat) (u : tm) (q : qualifier) : qualifier :=
  open_pred_tm_rec k u q.

Definition open_pred_tm (p : qualifier) (u : tm) : qualifier :=
  open_pred_tm_rec 0 u p.

Definition open_qualifier_tm (ps : qualifier) (u : tm) : qualifier :=
  open_qualifier_tm_rec 0 u ps.

Fixpoint open_pred_ty_rec (k : nat) (U : ty) (p : qualifier) : qualifier :=
  match p with
  | Pred_True => Pred_True
  | Pred_False => Pred_False
  | Pred_Eq t1 t2 =>
      Pred_Eq (open_tm_ty_rec k U t1) (open_tm_ty_rec k U t2)
  | Pred_Lt t1 t2 =>
      Pred_Lt (open_tm_ty_rec k U t1) (open_tm_ty_rec k U t2)
  | Pred_Le t1 t2 =>
      Pred_Le (open_tm_ty_rec k U t1) (open_tm_ty_rec k U t2)
  | Pred_And p1 p2 =>
      Pred_And (open_pred_ty_rec k U p1) (open_pred_ty_rec k U p2)
  | Pred_Or p1 p2 =>
      Pred_Or (open_pred_ty_rec k U p1) (open_pred_ty_rec k U p2)
  | Pred_Not p1 => Pred_Not (open_pred_ty_rec k U p1)
  end.

Definition open_qualifier_ty_rec (k : nat) (U : ty) (q : qualifier) : qualifier :=
  open_pred_ty_rec k U q.

Fixpoint pred_subst (x : atom) (s : tm) (p : qualifier) : qualifier :=
  match p with
  | Pred_True => Pred_True
  | Pred_False => Pred_False
  | Pred_Eq t1 t2 => Pred_Eq (tm_subst x s t1) (tm_subst x s t2)
  | Pred_Lt t1 t2 => Pred_Lt (tm_subst x s t1) (tm_subst x s t2)
  | Pred_Le t1 t2 => Pred_Le (tm_subst x s t1) (tm_subst x s t2)
  | Pred_And p1 p2 => Pred_And (pred_subst x s p1) (pred_subst x s p2)
  | Pred_Or p1 p2 => Pred_Or (pred_subst x s p1) (pred_subst x s p2)
  | Pred_Not p1 => Pred_Not (pred_subst x s p1)
  end.

Definition qualifier_subst (x : atom) (s : tm) (q : qualifier) : qualifier :=
  pred_subst x s q.

Fixpoint pred_ty_subst (X : atom) (U : ty) (p : qualifier) : qualifier :=
  match p with
  | Pred_True => Pred_True
  | Pred_False => Pred_False
  | Pred_Eq t1 t2 =>
      Pred_Eq (tm_ty_subst X U t1) (tm_ty_subst X U t2)
  | Pred_Lt t1 t2 =>
      Pred_Lt (tm_ty_subst X U t1) (tm_ty_subst X U t2)
  | Pred_Le t1 t2 =>
      Pred_Le (tm_ty_subst X U t1) (tm_ty_subst X U t2)
  | Pred_And p1 p2 =>
      Pred_And (pred_ty_subst X U p1) (pred_ty_subst X U p2)
  | Pred_Or p1 p2 =>
      Pred_Or (pred_ty_subst X U p1) (pred_ty_subst X U p2)
  | Pred_Not p1 => Pred_Not (pred_ty_subst X U p1)
  end.

Definition qualifier_ty_subst (X : atom) (U : ty) (q : qualifier) : qualifier :=
  pred_ty_subst X U q.

Inductive lc_pred_at : nat -> nat -> qualifier -> Prop :=
  | LCP_True : forall K k, lc_pred_at K k Pred_True
  | LCP_False : forall K k, lc_pred_at K k Pred_False
  | LCP_Eq : forall K k t1 t2,
      lc_tm_at K k t1 ->
      lc_tm_at K k t2 ->
      lc_pred_at K k (Pred_Eq t1 t2)
  | LCP_Lt : forall K k t1 t2,
      lc_tm_at K k t1 ->
      lc_tm_at K k t2 ->
      lc_pred_at K k (Pred_Lt t1 t2)
  | LCP_Le : forall K k t1 t2,
      lc_tm_at K k t1 ->
      lc_tm_at K k t2 ->
      lc_pred_at K k (Pred_Le t1 t2)
  | LCP_And : forall K k p1 p2,
      lc_pred_at K k p1 ->
      lc_pred_at K k p2 ->
      lc_pred_at K k (Pred_And p1 p2)
  | LCP_Or : forall K k p1 p2,
      lc_pred_at K k p1 ->
      lc_pred_at K k p2 ->
      lc_pred_at K k (Pred_Or p1 p2)
  | LCP_Not : forall K k p,
      lc_pred_at K k p ->
      lc_pred_at K k (Pred_Not p).

Definition lc_qualifier_at (K k : nat) (q : qualifier) : Prop :=
  lc_pred_at K k q.

Inductive predicate_wf : ty_context -> context -> qualifier -> Prop :=
  | PWF_True : forall Delta Gamma,
      predicate_wf Delta Gamma Pred_True
  | PWF_False : forall Delta Gamma,
      predicate_wf Delta Gamma Pred_False
  | PWF_Eq : forall Delta Gamma t1 t2 T,
      has_type Delta Gamma t1 T ->
      has_type Delta Gamma t2 T ->
      predicate_wf Delta Gamma (Pred_Eq t1 t2)
  | PWF_Lt : forall Delta Gamma t1 t2,
      has_type Delta Gamma t1 Ty_Int ->
      has_type Delta Gamma t2 Ty_Int ->
      predicate_wf Delta Gamma (Pred_Lt t1 t2)
  | PWF_Le : forall Delta Gamma t1 t2,
      has_type Delta Gamma t1 Ty_Int ->
      has_type Delta Gamma t2 Ty_Int ->
      predicate_wf Delta Gamma (Pred_Le t1 t2)
  | PWF_And : forall Delta Gamma p1 p2,
      predicate_wf Delta Gamma p1 ->
      predicate_wf Delta Gamma p2 ->
      predicate_wf Delta Gamma (Pred_And p1 p2)
  | PWF_Or : forall Delta Gamma p1 p2,
      predicate_wf Delta Gamma p1 ->
      predicate_wf Delta Gamma p2 ->
      predicate_wf Delta Gamma (Pred_Or p1 p2)
  | PWF_Not : forall Delta Gamma p,
      predicate_wf Delta Gamma p ->
      predicate_wf Delta Gamma (Pred_Not p).

Definition qualifier_wf (Delta : ty_context) (Gamma : context)
    (q : qualifier) : Prop := predicate_wf Delta Gamma q.

Inductive predicate_multistep : tm -> tm -> Prop :=
  | PMS_Refl : forall t,
      predicate_multistep t t
  | PMS_Step : forall t1 t2 t3,
      t1 --> t2 ->
      predicate_multistep t2 t3 ->
      predicate_multistep t1 t3.

Record atom_interpretation := {
  interpret_eq : tm -> tm -> Prop;
  interpret_lt : tm -> tm -> Prop;
  interpret_le : tm -> tm -> Prop
}.

Fixpoint interpret_qualifier (atoms : atom_interpretation) (p : qualifier) : Prop :=
  match p with
  | Pred_True => True
  | Pred_False => False
  | Pred_Eq t1 t2 => atoms.(interpret_eq) t1 t2
  | Pred_Lt t1 t2 => atoms.(interpret_lt) t1 t2
  | Pred_Le t1 t2 => atoms.(interpret_le) t1 t2
  | Pred_And p1 p2 =>
      interpret_qualifier atoms p1 /\ interpret_qualifier atoms p2
  | Pred_Or p1 p2 =>
      interpret_qualifier atoms p1 \/ interpret_qualifier atoms p2
  | Pred_Not p1 => ~ interpret_qualifier atoms p1
  end.

Definition operational_atoms : atom_interpretation := {|
  interpret_eq := fun t1 t2 =>
    exists v, predicate_multistep t1 v /\
              predicate_multistep t2 v /\ value v;
  interpret_lt := fun t1 t2 =>
    exists n1 n2 : Z,
      predicate_multistep t1 (tm_int n1) /\
      predicate_multistep t2 (tm_int n2) /\ (n1 < n2)%Z /\
      (forall m1 m2 : Z,
        predicate_multistep t1 (tm_int m1) ->
        predicate_multistep t2 (tm_int m2) -> (m1 < m2)%Z);
  interpret_le := fun t1 t2 =>
    exists n1 n2 : Z,
      predicate_multistep t1 (tm_int n1) /\
      predicate_multistep t2 (tm_int n2) /\ (n1 <= n2)%Z
|}.

Definition predicate_holds (p : qualifier) : Prop :=
  interpret_qualifier operational_atoms p.

Definition qualifier_holds (q : qualifier) : Prop := predicate_holds q.

Fixpoint predicate_closed (p : qualifier) : Prop :=
  match p with
  | Pred_True | Pred_False => True
  | Pred_Eq t1 t2 | Pred_Lt t1 t2 | Pred_Le t1 t2 =>
      locally_closed_tm t1 /\ fv_tm t1 = [] /\ ftv_tm t1 = [] /\
      locally_closed_tm t2 /\ fv_tm t2 = [] /\ ftv_tm t2 = []
  | Pred_And p1 p2 | Pred_Or p1 p2 =>
      predicate_closed p1 /\ predicate_closed p2
  | Pred_Not p1 => predicate_closed p1
  end.

End SystemFRefinementIfNonDeterminismLogic.

From Stdlib Require Import Arith.PeanoNat Lists.List Lia ZArith.BinInt.
Module SystemFRefinementIfNonDeterminismTyping.
Import ListNotations.
Import SystemFRefinementIfNonDeterminism.
Export SystemFRefinementIfNonDeterminismLogic.

Inductive rty : Type :=
  | R_Refine : ty -> qualifier -> rty
  | R_Func : rty -> rty -> rty
  | R_Exists : rty -> rty -> rty
  | R_Poly : rty -> rty.

Fixpoint erase (R : rty) : ty :=
  match R with
  | R_Refine T _ => T
  | R_Func R1 R2 => Ty_Arrow (erase R1) (erase R2)
  | R_Exists _ R2 => erase R2
  | R_Poly R => Ty_All (erase R)
  end.

Fixpoint open_rty_tm_rec (k : nat) (u : tm) (R : rty) : rty :=
  match R with
  | R_Refine T ps => R_Refine T (open_qualifier_tm_rec (S k) u ps)
  | R_Func R1 R2 =>
      R_Func (open_rty_tm_rec k u R1) (open_rty_tm_rec (S k) u R2)
  | R_Exists R1 R2 =>
      R_Exists (open_rty_tm_rec k u R1) (open_rty_tm_rec (S k) u R2)
  | R_Poly R1 => R_Poly (open_rty_tm_rec k u R1)
  end.

Definition open_rty_tm (R : rty) (u : tm) : rty :=
  open_rty_tm_rec 0 u R.

Fixpoint open_rty_ty_rec (k : nat) (U : ty) (R : rty) : rty :=
  match R with
  | R_Refine T ps =>
      R_Refine (open_ty_rec k U T) (open_qualifier_ty_rec k U ps)
  | R_Func R1 R2 =>
      R_Func (open_rty_ty_rec k U R1) (open_rty_ty_rec k U R2)
  | R_Exists R1 R2 =>
      R_Exists (open_rty_ty_rec k U R1) (open_rty_ty_rec k U R2)
  | R_Poly R1 => R_Poly (open_rty_ty_rec (S k) U R1)
  end.

Definition open_rty_ty (R : rty) (U : ty) : rty :=
  open_rty_ty_rec 0 U R.

Fixpoint rty_subst (x : atom) (s : tm) (R : rty) : rty :=
  match R with
  | R_Refine T ps => R_Refine T (qualifier_subst x s ps)
  | R_Func R1 R2 => R_Func (rty_subst x s R1) (rty_subst x s R2)
  | R_Exists R1 R2 => R_Exists (rty_subst x s R1) (rty_subst x s R2)
  | R_Poly R1 => R_Poly (rty_subst x s R1)
  end.

Fixpoint rty_ty_subst (X : atom) (U : ty) (R : rty) : rty :=
  match R with
  | R_Refine T ps => R_Refine (ty_subst X U T) (qualifier_ty_subst X U ps)
  | R_Func R1 R2 =>
      R_Func (rty_ty_subst X U R1) (rty_ty_subst X U R2)
  | R_Exists R1 R2 =>
      R_Exists (rty_ty_subst X U R1) (rty_ty_subst X U R2)
  | R_Poly R1 => R_Poly (rty_ty_subst X U R1)
  end.

Inductive lc_rty_at : nat -> nat -> rty -> Prop :=
  | LCR_Refine : forall K k T ps,
      lc_ty_at K T ->
      lc_qualifier_at K (S k) ps ->
      lc_rty_at K k (R_Refine T ps)
  | LCR_Func : forall K k R1 R2,
      lc_rty_at K k R1 ->
      lc_rty_at K (S k) R2 ->
      lc_rty_at K k (R_Func R1 R2)
  | LCR_Exists : forall K k R1 R2,
      lc_rty_at K k R1 ->
      lc_rty_at K (S k) R2 ->
      lc_rty_at K k (R_Exists R1 R2)
  | LCR_Poly : forall K k R,
      lc_rty_at (S K) k R ->
      lc_rty_at K k (R_Poly R).

Definition locally_closed_rty (R : rty) : Prop := lc_rty_at 0 0 R.

Definition rcontext := list (atom * rty).

Fixpoint lookup_rcontext (x : atom) (RGamma : rcontext) : option rty :=
  match RGamma with
  | [] => None
  | (y, R) :: RGamma' =>
      if Nat.eqb x y then Some R else lookup_rcontext x RGamma'
  end.

Definition empty_rcontext : rcontext := [].
Definition update_rcontext (RGamma : rcontext) (x : atom) (R : rty) : rcontext :=
  (x, R) :: RGamma.

Fixpoint erase_context (RGamma : rcontext) : context :=
  match RGamma with
  | [] => empty
  | (x, R) :: RGamma' => update (erase_context RGamma') x (erase R)
  end.

Inductive wf_rty : ty_context -> rcontext -> rty -> Prop :=

  | RWF_Refine : forall (L : list atom) Delta RGamma T ps,
      wf_ty Delta T ->
      (forall x, ~ In x L ->
        qualifier_wf Delta
          (update (erase_context RGamma) x T)
          (open_qualifier_tm ps (tm_fvar x))) ->
      wf_rty Delta RGamma (R_Refine T ps)

  | RWF_Func : forall (L : list atom) Delta RGamma R1 R2,
      wf_rty Delta RGamma R1 ->
      (forall x, ~ In x L ->
        wf_rty Delta (update_rcontext RGamma x R1)
          (open_rty_tm R2 (tm_fvar x))) ->
      wf_rty Delta RGamma (R_Func R1 R2)

  | RWF_Exists : forall (L : list atom) Delta RGamma R1 R2,
      wf_rty Delta RGamma R1 ->
      (forall x, ~ In x L ->
        wf_rty Delta (update_rcontext RGamma x R1)
          (open_rty_tm R2 (tm_fvar x))) ->
      wf_rty Delta RGamma (R_Exists R1 R2)
  | RWF_Poly : forall (L : list atom) Delta RGamma R,
      (forall X, ~ In X L ->
        wf_rty (X :: Delta) RGamma (open_rty_ty R (Ty_FVar X))) ->
      wf_rty Delta RGamma (R_Poly R).

Inductive entails : ty_context -> rcontext -> qualifier -> qualifier -> Prop :=
  | Entails_Refl : forall Delta RGamma ps,
      entails Delta RGamma ps ps
  | Entails_True : forall Delta RGamma ps,
      entails Delta RGamma ps Pred_True
  | Entails_Trans : forall Delta RGamma ps qs rs,
      entails Delta RGamma ps qs ->
      entails Delta RGamma qs rs ->
      entails Delta RGamma ps rs
  | Entails_AndLeft : forall Delta RGamma p q,
      entails Delta RGamma (Pred_And p q) p
  | Entails_AndRight : forall Delta RGamma p q,
      entails Delta RGamma (Pred_And p q) q
  | Entails_AndIntro : forall Delta RGamma ps p qs,
      entails Delta RGamma ps p ->
      entails Delta RGamma ps qs ->
      entails Delta RGamma ps (Pred_And p qs)
  | Entails_OrLeft : forall Delta RGamma p q,
      entails Delta RGamma p (Pred_Or p q)
  | Entails_OrRight : forall Delta RGamma p q,
      entails Delta RGamma q (Pred_Or p q)
  | Entails_OrElim : forall Delta RGamma p q r,
      entails Delta RGamma p r ->
      entails Delta RGamma q r ->
      entails Delta RGamma (Pred_Or p q) r
  | Entails_NotIntro : forall Delta RGamma p q,
      entails Delta RGamma (Pred_And p q) Pred_False ->
      entails Delta RGamma p (Pred_Not q)
  | Entails_NotElim : forall Delta RGamma p,
      entails Delta RGamma (Pred_And p (Pred_Not p)) Pred_False
  | Entails_Context : forall Delta RGamma x T p q,
      lookup_rcontext x RGamma = Some (R_Refine T p) ->
      entails Delta RGamma q (open_qualifier_tm p (tm_fvar x))

  | Entails_False : forall Delta RGamma q,
      entails Delta RGamma Pred_False q.

Inductive has_rtype : ty_context -> rcontext -> tm -> rty -> Prop :=
  | RT_Var : forall Delta RGamma x R,
      lookup_rcontext x RGamma = Some R ->
      wf_rty Delta RGamma R ->
      has_rtype Delta RGamma (tm_fvar x) R

  | RT_Abs : forall (L : list atom) Delta RGamma R1 body R2,
      wf_rty Delta RGamma R1 ->
      (forall x, ~ In x L ->
        has_rtype Delta (update_rcontext RGamma x R1)
          (open_tm body (tm_fvar x))
          (open_rty_tm R2 (tm_fvar x))) ->
      has_rtype Delta RGamma (tm_abs (erase R1) body) (R_Func R1 R2)
  | RT_App : forall Delta RGamma t1 t2 R1 R2,
      has_rtype Delta RGamma t1 (R_Func R1 R2) ->
      has_rtype Delta RGamma t2 R1 ->
      has_rtype Delta RGamma (tm_app t1 t2) (R_Exists R1 R2)
  | RT_TAbs : forall (L : list atom) Delta RGamma body R,
      (forall X, ~ In X L ->
        has_rtype (X :: Delta) RGamma
          (open_tm_ty body (Ty_FVar X))
          (open_rty_ty R (Ty_FVar X))) ->
      has_rtype Delta RGamma (tm_tabs body) (R_Poly R)
  | RT_TApp : forall Delta RGamma t R U,
      has_rtype Delta RGamma t (R_Poly R) ->
      wf_ty Delta U ->
      has_rtype Delta RGamma (tm_tapp t U) (open_rty_ty R U)
  | RT_Int : forall Delta RGamma (n : Z),
      has_rtype Delta RGamma (tm_int n)
        (R_Refine Ty_Int (Pred_Eq (tm_bvar 0) (tm_int n)))
  | RT_Div : forall Delta RGamma t1 t2,
      has_rtype Delta RGamma t1 (R_Refine Ty_Int Pred_True) ->
      has_rtype Delta RGamma t2
        (R_Refine Ty_Int (Pred_Ne (tm_bvar 0) (tm_int 0%Z))) ->
      has_rtype Delta RGamma (tm_div t1 t2) (R_Refine Ty_Int Pred_True)
  | RT_Arith : forall Delta RGamma op t1 t2,
      has_rtype Delta RGamma t1 (R_Refine Ty_Int Pred_True) ->
      has_rtype Delta RGamma t2 (R_Refine Ty_Int Pred_True) ->
      has_rtype Delta RGamma (tm_arith op t1 t2)
        (R_Refine Ty_Int (Pred_Eq (tm_bvar 0) (tm_arith op t1 t2)))

  | RT_Choice : forall Delta RGamma t1 t2 R,
      has_rtype Delta RGamma t1 R ->
      has_rtype Delta RGamma t2 R ->
      has_rtype Delta RGamma (tm_choice t1 t2) R
  | RT_True : forall Delta RGamma,
      has_rtype Delta RGamma tm_true (R_Refine Ty_Bool Pred_True)
  | RT_False : forall Delta RGamma,
      has_rtype Delta RGamma tm_false (R_Refine Ty_Bool Pred_True)
  | RT_If : forall Delta RGamma t1 t2 t3 R,
      has_rtype Delta RGamma t1 (R_Refine Ty_Bool Pred_True) ->
      has_rtype Delta RGamma t2 R -> has_rtype Delta RGamma t3 R ->
      has_rtype Delta RGamma (tm_if t1 t2 t3) R
  | RT_RefineValue : forall Delta RGamma v T ps,
      has_type Delta (erase_context RGamma) v T ->
      value v ->
      wf_rty Delta RGamma (R_Refine T ps) ->
      predicate_closed (open_qualifier_tm ps v) ->
      qualifier_holds (open_qualifier_tm ps v) ->
      has_rtype Delta RGamma v (R_Refine T ps)

  | RT_Sub : forall Delta RGamma t R S,
      has_rtype Delta RGamma t R ->
      wf_rty Delta RGamma S ->
      subtype Delta RGamma R S ->
      has_rtype Delta RGamma t S

with subtype : ty_context -> rcontext -> rty -> rty -> Prop :=
  | S_Refl : forall Delta RGamma R,
      subtype Delta RGamma R R
  | S_Refine : forall (L : list atom) Delta RGamma T ps qs,
      (forall x, ~ In x L ->
        entails Delta
          (update_rcontext RGamma x (R_Refine T Pred_True))
          (open_qualifier_tm ps (tm_fvar x))
          (open_qualifier_tm qs (tm_fvar x))) ->
      subtype Delta RGamma (R_Refine T ps) (R_Refine T qs)
  | S_Func : forall (L : list atom) Delta RGamma R1 R2 S1 S2,
      subtype Delta RGamma S1 R1 ->
      (forall x, ~ In x L ->
        subtype Delta (update_rcontext RGamma x S1)
          (open_rty_tm R2 (tm_fvar x))
          (open_rty_tm S2 (tm_fvar x))) ->
      subtype Delta RGamma (R_Func R1 R2) (R_Func S1 S2)
  | S_Witness : forall Delta RGamma v R1 R2 S,
      value v ->
      has_rtype Delta RGamma v R1 ->
      subtype Delta RGamma S (open_rty_tm R2 v) ->
      subtype Delta RGamma S (R_Exists R1 R2)
  | S_Bind : forall (L : list atom) Delta RGamma R1 R2 S,

      wf_rty Delta RGamma R1 ->
      locally_closed_rty S ->
      (forall x, ~ In x L ->
        subtype Delta (update_rcontext RGamma x R1)
          (open_rty_tm R2 (tm_fvar x)) S) ->
      subtype Delta RGamma (R_Exists R1 R2) S
  | S_Poly : forall (L : list atom) Delta RGamma R S,
      (forall X, ~ In X L ->
        subtype (X :: Delta) RGamma
          (open_rty_ty R (Ty_FVar X))
          (open_rty_ty S (Ty_FVar X))) ->
      subtype Delta RGamma (R_Poly R) (R_Poly S)
  | S_Trans : forall Delta RGamma R S U,
      subtype Delta RGamma R S ->
      subtype Delta RGamma S U ->
      subtype Delta RGamma R U.

Fixpoint close_ty_rec (k : nat) (X : atom) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar Y => if Nat.eqb X Y then Ty_BVar k else Ty_FVar Y
  | Ty_Arrow T1 T2 =>
      Ty_Arrow (close_ty_rec k X T1) (close_ty_rec k X T2)
  | Ty_All T1 => Ty_All (close_ty_rec (S k) X T1)
  | Ty_Int => Ty_Int
  | Ty_Bool => Ty_Bool
  end.

End SystemFRefinementIfNonDeterminismTyping.

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Module SystemFRefinementIfNonDeterminismEvaluation.
Import ListNotations SystemFRefinementIfNonDeterminism SystemFRefinementIfNonDeterminismInfrastructure
  SystemFRefinementIfNonDeterminismCoreTyping.

Inductive multi : tm -> tm -> Prop :=
  | multi_refl : forall t, multi t t
  | multi_step : forall t1 t2 t3,
      t1 --> t2 -> multi t2 t3 -> multi t1 t3.
Notation "t '-->*' u" := (multi t u) (at level 40).

Definition halts (t : tm) : Prop :=
  exists v, multi t v /\ value v.

Inductive must_terminate : tm -> Prop :=
  | MT_intro : forall t,
      (value t \/ exists u, t --> u) ->
      (forall u, t --> u -> must_terminate u) ->
      must_terminate t.

Lemma open_tm_preserves_lc_at : forall t K k u,
  lc_tm_at K (S k) t -> locally_closed_tm u ->
  lc_tm_at K k (open_tm_rec k u t).
Proof.
  induction t; intros K k u Hlc Hu; simpl; inversion Hlc; subst;
    eauto 8 using lc_tm_at.
  destruct (Nat.eqb k n) eqn:E.
  - eapply lc_tm_at_monotone; [exact Hu|lia|lia].
  - apply Nat.eqb_neq in E. apply lc_tm_bvar. lia.
Qed.

Lemma open_tm_ty_preserves_lc_at : forall t K k U,
  lc_tm_at (S K) k t -> locally_closed_ty U ->
  lc_tm_at K k (open_tm_ty_rec K U t).
Proof.
  induction t; intros K k U Hlc HU; simpl; inversion Hlc; subst;
    eauto 8 using lc_tm_at.
  - apply lc_tm_abs.
    + apply lc_ty_at_open; [assumption|].
      eapply lc_ty_at_monotone; [exact HU|lia].
    + eapply IHt; eauto.
  - apply lc_tm_tapp.
    + eapply IHt; eauto.
    + apply lc_ty_at_open; [assumption|].
      eapply lc_ty_at_monotone; [exact HU|lia].
Qed.

Lemma value_regular : forall v, value v -> locally_closed_tm v.
Proof. intros v H. destruct H; try assumption; constructor. Qed.

Lemma value_no_step : forall v, value v -> forall t, ~ (v --> t).
Proof. intros v Hv t Hs. destruct Hv; inversion Hs. Qed.

Lemma value_multi_eq : forall v t,
  value v ->
  v -->* t ->
  t = v.
Proof.
  intros v t Hv Hmulti.
  inversion Hmulti; subst.
  - reflexivity.
  - exfalso. eapply value_no_step; eauto.
Qed.

Lemma multi_trans : forall t u v,
  multi t u -> multi u v -> multi t v.
Proof. intros t u v H. induction H; eauto using multi. Qed.

End SystemFRefinementIfNonDeterminismEvaluation.

From Stdlib Require Import Arith.PeanoNat Lists.List Lia Program.Wf.
From Stdlib Require Import Program.Equality.
From Stdlib Require Import Arith.Wf_nat.
From Stdlib Require Import Recdef.
From Equations Require Import Equations.
Module SystemFRefinementIfNonDeterminismSubstitution.
Import ListNotations.
Import SystemFRefinementIfNonDeterminism.
Import SystemFRefinementIfNonDeterminismInfrastructure.
Import SystemFRefinementIfNonDeterminismCoreTyping.
Import SystemFRefinementIfNonDeterminismTyping.
Import SystemFRefinementIfNonDeterminismEvaluation.

Fixpoint fv_pred (p : qualifier) : list atom :=
  match p with
  | Pred_True | Pred_False => []
  | Pred_Eq t1 t2 | Pred_Lt t1 t2 | Pred_Le t1 t2 => fv_tm t1 ++ fv_tm t2
  | Pred_And p1 p2 | Pred_Or p1 p2 => fv_pred p1 ++ fv_pred p2
  | Pred_Not p => fv_pred p
  end.

Definition fv_qualifier := fv_pred.

Fixpoint fv_rty (R : rty) : list atom :=
  match R with
  | R_Refine _ ps => fv_qualifier ps
  | R_Func R1 R2 | R_Exists R1 R2 => fv_rty R1 ++ fv_rty R2
  | R_Poly R1 => fv_rty R1
  end.

Fixpoint ftv_pred (p : qualifier) : list atom :=
  match p with
  | Pred_True | Pred_False => []
  | Pred_Eq t1 t2 | Pred_Lt t1 t2 | Pred_Le t1 t2 => ftv_tm t1 ++ ftv_tm t2
  | Pred_And p1 p2 | Pred_Or p1 p2 => ftv_pred p1 ++ ftv_pred p2
  | Pred_Not p => ftv_pred p
  end.

Definition ftv_qualifier := ftv_pred.

Fixpoint ftv_rty (R : rty) : list atom :=
  match R with
  | R_Refine T ps => fv_ty T ++ ftv_qualifier ps
  | R_Func R1 R2 | R_Exists R1 R2 => ftv_rty R1 ++ ftv_rty R2
  | R_Poly R1 => ftv_rty R1
  end.

Fixpoint fv_rcontext (RGamma : rcontext) : list atom :=
  match RGamma with
  | [] => []
  | (_, R) :: RGamma' => fv_rty R ++ fv_rcontext RGamma'
  end.

Fixpoint ftv_rcontext (RGamma : rcontext) : list atom :=
  match RGamma with
  | [] => []
  | (_, R) :: RGamma' => ftv_rty R ++ ftv_rcontext RGamma'
  end.

Fixpoint instantiate_pred
    (theta : type_substitution) (gamma : term_substitution)
    (p : qualifier) : qualifier :=
  match p with
  | Pred_True => Pred_True
  | Pred_False => Pred_False
  | Pred_Eq t1 t2 =>
      Pred_Eq (instantiate theta gamma t1) (instantiate theta gamma t2)
  | Pred_Lt t1 t2 => Pred_Lt (instantiate theta gamma t1) (instantiate theta gamma t2)
  | Pred_Le t1 t2 => Pred_Le (instantiate theta gamma t1) (instantiate theta gamma t2)
  | Pred_And p1 p2 => Pred_And (instantiate_pred theta gamma p1) (instantiate_pred theta gamma p2)
  | Pred_Not p => Pred_Not (instantiate_pred theta gamma p)
  | Pred_Or p1 p2 =>
      Pred_Or (instantiate_pred theta gamma p1)
        (instantiate_pred theta gamma p2)
  end.

Definition instantiate_qualifier := instantiate_pred.

Fixpoint instantiate_rty
    (theta : type_substitution) (gamma : term_substitution)
    (R : rty) : rty :=
  match R with
  | R_Refine T ps =>
      R_Refine (instantiate_ty theta T) (instantiate_qualifier theta gamma ps)
  | R_Func R1 R2 =>
      R_Func (instantiate_rty theta gamma R1)
        (instantiate_rty theta gamma R2)
  | R_Exists R1 R2 =>
      R_Exists (instantiate_rty theta gamma R1)
        (instantiate_rty theta gamma R2)
  | R_Poly R1 => R_Poly (instantiate_rty theta gamma R1)
  end.

Fixpoint rty_size (R : rty) : nat :=
  match R with
  | R_Refine _ _ => 1
  | R_Func R1 R2 => S (rty_size R1 + rty_size R2)
  | R_Exists R1 R2 => S (rty_size R1 + rty_size R2)
  | R_Poly R1 => S (rty_size R1)
  end.

Scheme has_rtype_mut_ind := Induction for has_rtype Sort Prop
with subtype_mut_ind := Induction for subtype Sort Prop.
Combined Scheme refinement_typing_mutind
  from has_rtype_mut_ind, subtype_mut_ind.
End SystemFRefinementIfNonDeterminismSubstitution.

Module SystemFRefinementIfNonDeterminismTask.
Import ListNotations SystemFRefinementIfNonDeterminism SystemFRefinementIfNonDeterminismInfrastructure SystemFRefinementIfNonDeterminismCoreTyping SystemFRefinementIfNonDeterminismLogic SystemFRefinementIfNonDeterminismTyping SystemFRefinementIfNonDeterminismEvaluation SystemFRefinementIfNonDeterminismSubstitution .

Definition reducible (t : tm) : Prop :=
  forall t', multi t t' -> value t' \/ exists u, t' --> u.

Lemma rty_size_open_tm_rec : forall R k u,
  rty_size (open_rty_tm_rec k u R) = rty_size R.
Proof.
  induction R; intros k u; simpl; try rewrite IHR; try rewrite IHR1, IHR2; reflexivity.
Qed.

Lemma rty_size_open_ty_rec : forall R k U,
  rty_size (open_rty_ty_rec k U R) = rty_size R.
Proof.
  induction R; intros k U; simpl; try rewrite IHR; try rewrite IHR1, IHR2; reflexivity.
Qed.

Lemma rty_size_pos : forall R, 0 < rty_size R.
Proof. induction R; simpl; lia. Qed.

Equations logical_value (R : rty) (v : tm) : Prop by wf (rty_size R) lt :=
logical_value (R_Refine T p) v :=
  value v /\ qualifier_holds (open_qualifier_tm p v);
logical_value (R_Func A B) v :=
  value v /\ forall w,
    logical_value A w -> forall t', multi (tm_app v w) t' ->
      logical_value (open_rty_tm B w) t' \/ exists u, t' --> u;
logical_value (R_Exists A B) v :=
  exists w, logical_value A w /\ value v /\ logical_value (open_rty_tm B w) v;
logical_value (R_Poly A) v :=
  value v /\ forall U, locally_closed_ty U ->
    forall t', multi (tm_tapp v U) t' ->
      logical_value (open_rty_ty A U) t' \/ exists u, t' --> u.
Next Obligation.
  simpl. pose proof (rty_size_pos B). lia.
Qed.
Next Obligation.
  unfold open_rty_tm. rewrite rty_size_open_tm_rec. simpl.
  pose proof (rty_size_pos A). lia.
Qed.
Next Obligation.
  simpl. pose proof (rty_size_pos B). lia.
Qed.
Next Obligation.
  unfold open_rty_tm. rewrite rty_size_open_tm_rec. simpl.
  pose proof (rty_size_pos A). lia.
Qed.
Next Obligation.
  unfold open_rty_ty. rewrite rty_size_open_ty_rec. simpl.
  pose proof (rty_size_pos A). lia.
Qed.

Definition logical_expr (R : rty) (t : tm) : Prop :=
  forall t', multi t t' -> logical_value R t' \/ exists u, t' --> u.

Definition context_interpretation (RG : rcontext)
    (theta : type_substitution) (gamma : term_substitution) : Prop :=
  forall x R, lookup_rcontext x RG = Some R ->
    logical_value (instantiate_rty theta gamma R) (gamma x).

Lemma instantiate_open_tm_rec : forall t k u theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  instantiate theta gamma (open_tm_rec k u t) =
  open_tm_rec k (instantiate theta gamma u) (instantiate theta gamma t).
Proof.
  induction t; intros k u theta gamma Htheta Hgamma; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - assert (Hlc : lc_tm_at 0 k (gamma a)).
    { eapply lc_tm_at_monotone.
      - apply Hgamma.
      - lia.
      - lia. }
    rewrite (open_tm_rec_lc_at (gamma a) 0 k
      (instantiate theta gamma u) Hlc). reflexivity.
  - f_equal. apply IHt; assumption.
  - f_equal.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
  - f_equal. apply IHt; assumption.
  - f_equal. apply IHt; assumption.
  - reflexivity.
  - f_equal; [apply IHt1 | apply IHt2]; assumption.
  - f_equal; [apply IHt1 | apply IHt2]; assumption.
  - f_equal; [apply IHt1 | apply IHt2]; assumption.
  - reflexivity.
  - reflexivity.
  - f_equal; [apply IHt1 | apply IHt2 | apply IHt3]; assumption.
Qed.

Lemma instantiate_open_tm : forall t u theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  instantiate theta gamma (open_tm t u) =
  open_tm (instantiate theta gamma t) (instantiate theta gamma u).
Proof.
  intros. apply instantiate_open_tm_rec; assumption.
Qed.

Lemma instantiate_open_qualifier_tm_rec : forall p k u theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  instantiate_qualifier theta gamma (open_qualifier_tm_rec k u p) =
  open_qualifier_tm_rec k (instantiate theta gamma u)
    (instantiate_qualifier theta gamma p).
Proof.
  induction p; intros k u theta gamma Htheta Hgamma; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal; [apply instantiate_open_tm_rec | apply instantiate_open_tm_rec];
      assumption.
  - f_equal; [apply instantiate_open_tm_rec | apply instantiate_open_tm_rec];
      assumption.
  - f_equal; [apply instantiate_open_tm_rec | apply instantiate_open_tm_rec];
      assumption.
  - f_equal; [apply IHp1 | apply IHp2]; assumption.
  - f_equal; [apply IHp1 | apply IHp2]; assumption.
  - f_equal. apply IHp; assumption.
Qed.

Lemma instantiate_open_qualifier_tm : forall p u theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  instantiate_qualifier theta gamma (open_qualifier_tm p u) =
  open_qualifier_tm (instantiate_qualifier theta gamma p)
    (instantiate theta gamma u).
Proof.
  intros. apply instantiate_open_qualifier_tm_rec; assumption.
Qed.

Lemma instantiate_open_rty_tm_rec : forall R k u theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  instantiate_rty theta gamma (open_rty_tm_rec k u R) =
  open_rty_tm_rec k (instantiate theta gamma u)
    (instantiate_rty theta gamma R).
Proof.
  induction R; intros k u theta gamma Htheta Hgamma; simpl.
  - f_equal. apply instantiate_open_qualifier_tm_rec; assumption.
  - f_equal.
    + apply IHR1; assumption.
    + apply IHR2; assumption.
  - f_equal.
    + apply IHR1; assumption.
    + apply IHR2; assumption.
  - f_equal. apply IHR; assumption.
Qed.

Lemma instantiate_open_rty_tm : forall R u theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  instantiate_rty theta gamma (open_rty_tm R u) =
  open_rty_tm (instantiate_rty theta gamma R) (instantiate theta gamma u).
Proof.
  intros. apply instantiate_open_rty_tm_rec; assumption.
Qed.

Lemma instantiate_tm_subst : forall t theta gamma x u,
  (forall y, tm_subst x u (gamma y) =
    term_subst_update gamma x u y) ->
  instantiate theta (term_subst_update gamma x u) t =
  tm_subst x u (instantiate theta gamma t).
Proof.
  induction t; intros theta gamma x u Hgamma; simpl.
  - reflexivity.
  - destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E. subst a.
      unfold term_subst_update. rewrite Nat.eqb_refl.
      symmetry. specialize (Hgamma x). unfold term_subst_update in Hgamma.
      rewrite Nat.eqb_refl in Hgamma. exact Hgamma.
    + apply Nat.eqb_neq in E.
      assert (E' : Nat.eqb a x = false) by (apply Nat.eqb_neq; congruence).
      specialize (Hgamma a). unfold term_subst_update in Hgamma.
      rewrite Nat.eqb_sym, E' in Hgamma.
      unfold term_subst_update. rewrite Nat.eqb_sym, E'. symmetry. exact Hgamma.
  - f_equal. apply IHt. exact Hgamma.
  - f_equal; [apply IHt1 | apply IHt2]; exact Hgamma.
  - f_equal. apply IHt. exact Hgamma.
  - f_equal. apply IHt. exact Hgamma.
  - reflexivity.
  - f_equal; [apply IHt1 | apply IHt2]; exact Hgamma.
  - f_equal; [apply IHt1 | apply IHt2]; exact Hgamma.
  - f_equal; [apply IHt1 | apply IHt2]; exact Hgamma.
  - reflexivity.
  - reflexivity.
  - f_equal; [apply IHt1 | apply IHt2 | apply IHt3]; exact Hgamma.
Qed.

Lemma instantiate_qualifier_subst : forall p theta gamma x u,
  (forall y, tm_subst x u (gamma y) = term_subst_update gamma x u y) ->
  instantiate_qualifier theta (term_subst_update gamma x u) p =
  qualifier_subst x u (instantiate_qualifier theta gamma p).
Proof.
  induction p; intros theta gamma x u Hgamma; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal; [apply instantiate_tm_subst | apply instantiate_tm_subst]; exact Hgamma.
  - f_equal; [apply instantiate_tm_subst | apply instantiate_tm_subst]; exact Hgamma.
  - f_equal; [apply instantiate_tm_subst | apply instantiate_tm_subst]; exact Hgamma.
  - f_equal; [apply IHp1 | apply IHp2]; exact Hgamma.
  - f_equal; [apply IHp1 | apply IHp2]; exact Hgamma.
  - f_equal. apply IHp. exact Hgamma.
Qed.

Lemma instantiate_rty_subst : forall R theta gamma x u,
  (forall y, tm_subst x u (gamma y) = term_subst_update gamma x u y) ->
  instantiate_rty theta (term_subst_update gamma x u) R =
  rty_subst x u (instantiate_rty theta gamma R).
Proof.
  induction R; intros theta gamma x u Hgamma; simpl.
  - f_equal. apply instantiate_qualifier_subst. exact Hgamma.
  - f_equal; [apply IHR1 | apply IHR2]; exact Hgamma.
  - f_equal; [apply IHR1 | apply IHR2]; exact Hgamma.
  - f_equal. apply IHR. exact Hgamma.
Qed.

Lemma instantiate_ty_subst : forall T theta X U,
  (forall Y, ty_subst X U (theta Y) = type_subst_update theta X U Y) ->
  instantiate_ty (type_subst_update theta X U) T =
  ty_subst X U (instantiate_ty theta T).
Proof.
  induction T; intros theta X U Htheta; simpl.
  - reflexivity.
  - symmetry. apply Htheta.
  - f_equal; [apply IHT1 | apply IHT2]; exact Htheta.
  - f_equal. apply IHT. exact Htheta.
  - reflexivity.
  - reflexivity.
Qed.

Lemma instantiate_tm_ty_subst : forall t theta gamma X U,
  (forall Y, ty_subst X U (theta Y) = type_subst_update theta X U Y) ->
  (forall y, tm_ty_subst X U (gamma y) = gamma y) ->
  instantiate (type_subst_update theta X U) gamma t =
  tm_ty_subst X U (instantiate theta gamma t).
Proof.
  induction t; intros theta gamma X U Htheta Hgamma; simpl.
  - reflexivity.
  - symmetry. apply Hgamma.
  - f_equal.
    + apply instantiate_ty_subst. exact Htheta.
    + apply IHt; assumption.
  - f_equal; [apply IHt1 | apply IHt2]; assumption.
  - f_equal. apply IHt; assumption.
  - f_equal.
    + apply IHt; assumption.
    + apply instantiate_ty_subst. exact Htheta.
  - reflexivity.
  - f_equal; [apply IHt1 | apply IHt2]; assumption.
  - f_equal; [apply IHt1 | apply IHt2]; assumption.
  - f_equal; [apply IHt1 | apply IHt2]; assumption.
  - reflexivity.
  - reflexivity.
  - f_equal; [apply IHt1 | apply IHt2 | apply IHt3]; assumption.
Qed.

Lemma instantiate_qualifier_ty_subst : forall p theta gamma X U,
  (forall Y, ty_subst X U (theta Y) = type_subst_update theta X U Y) ->
  (forall y, tm_ty_subst X U (gamma y) = gamma y) ->
  instantiate_qualifier (type_subst_update theta X U) gamma p =
  qualifier_ty_subst X U (instantiate_qualifier theta gamma p).
Proof.
  induction p; intros theta gamma X U Htheta Hgamma; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal; [apply instantiate_tm_ty_subst | apply instantiate_tm_ty_subst]; assumption.
  - f_equal; [apply instantiate_tm_ty_subst | apply instantiate_tm_ty_subst]; assumption.
  - f_equal; [apply instantiate_tm_ty_subst | apply instantiate_tm_ty_subst]; assumption.
  - f_equal; [apply IHp1 | apply IHp2]; assumption.
  - f_equal; [apply IHp1 | apply IHp2]; assumption.
  - f_equal. apply IHp; assumption.
Qed.

Lemma instantiate_rty_ty_subst : forall R theta gamma X U,
  (forall Y, ty_subst X U (theta Y) = type_subst_update theta X U Y) ->
  (forall y, tm_ty_subst X U (gamma y) = gamma y) ->
  instantiate_rty (type_subst_update theta X U) gamma R =
  rty_ty_subst X U (instantiate_rty theta gamma R).
Proof.
  induction R; intros theta gamma X U Htheta Hgamma; simpl.
  - f_equal.
    + apply instantiate_ty_subst. exact Htheta.
    + apply instantiate_qualifier_ty_subst; assumption.
  - f_equal; [apply IHR1 | apply IHR2]; assumption.
  - f_equal; [apply IHR1 | apply IHR2]; assumption.
  - f_equal. apply IHR; assumption.
Qed.


Lemma wf_ty_locally_closed : forall Delta T,
  wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T Hwf. induction Hwf.
  - unfold locally_closed_ty. constructor.
  - unfold locally_closed_ty in *. constructor; assumption.
  - unfold locally_closed_ty. constructor.
    pose proof (H0 (fresh L) (fresh_notin L)) as Hopen.
    exact (lc_ty_at_open_inv T 0 (fresh L) Hopen).
  - unfold locally_closed_ty. constructor.
  - unfold locally_closed_ty. constructor.
Qed.

Lemma has_type_locally_closed : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T Hty. induction Hty.
  - unfold locally_closed_tm. constructor.
  - unfold locally_closed_tm. apply lc_tm_abs.
    + eapply wf_ty_locally_closed; eauto.
    + eapply lc_tm_at_open_tm_inv.
      apply (H1 (fresh L) (fresh_notin L)).
  - unfold locally_closed_tm in *. econstructor; eauto.
  - unfold locally_closed_tm. apply lc_tm_tabs.
    eapply lc_tm_at_open_ty_inv.
    apply (H0 (fresh L) (fresh_notin L)).
  - unfold locally_closed_tm in *. apply lc_tm_tapp.
    + assumption.
    + eapply wf_ty_locally_closed; eassumption.
  - unfold locally_closed_tm. constructor.
  - unfold locally_closed_tm in *. econstructor; eauto.
  - unfold locally_closed_tm in *. econstructor; eauto.
  - unfold locally_closed_tm in *. econstructor; eauto.
  - unfold locally_closed_tm. constructor.
  - unfold locally_closed_tm. constructor.
  - unfold locally_closed_tm in *. apply lc_tm_if.
    + assumption.
    + assumption.
    + assumption.
Qed.

Lemma erase_open_rty_tm_rec : forall R k u,
  erase (open_rty_tm_rec k u R) = erase R.
Proof.
  induction R; intros k u; simpl; try rewrite ?IHR1, ?IHR2, ?IHR; reflexivity.
Qed.

Lemma erase_open_rty_tm : forall R u,
  erase (open_rty_tm R u) = erase R.
Proof.
  intros. apply erase_open_rty_tm_rec.
Qed.

Lemma erase_open_rty_ty_rec : forall R k U,
  erase (open_rty_ty_rec k U R) = open_ty_rec k U (erase R).
Proof.
  induction R; intros k U; simpl; try rewrite ?IHR1, ?IHR2, ?IHR; reflexivity.
Qed.

Lemma erase_open_rty_ty : forall R U,
  erase (open_rty_ty R U) = open_ty (erase R) U.
Proof.
  intros. apply erase_open_rty_ty_rec.
Qed.

Lemma close_open_ty_rec : forall T k X,
  ~ In X (fv_ty T) ->
  close_ty_rec k X (open_ty_rec k (Ty_FVar X) T) = T.
Proof.
  induction T; intros k X Hfresh; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. simpl. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E. subst a. exfalso. apply Hfresh. simpl. auto.
    + reflexivity.
  - f_equal.
    + apply IHT1. simpl in Hfresh. intuition.
    + apply IHT2. simpl in Hfresh. intuition.
  - f_equal. apply IHT with (k := S k) (X := X).
    simpl in Hfresh. exact Hfresh.
  - reflexivity.
  - reflexivity.
Qed.

Lemma open_ty_rec_injective : forall T S k X,
  ~ In X (fv_ty T ++ fv_ty S) ->
  open_ty_rec k (Ty_FVar X) T = open_ty_rec k (Ty_FVar X) S -> T = S.
Proof.
  intros T S k X Hfresh Heq.
  pose proof (f_equal (close_ty_rec k X) Heq) as Hclose.
  rewrite !close_open_ty_rec in Hclose.
  - exact Hclose.
  - intro Hin. apply Hfresh. apply in_or_app. right. exact Hin.
  - intro Hin. apply Hfresh. apply in_or_app. left. exact Hin.
Qed.

Lemma subtype_erase : forall Delta RG R S,
  subtype Delta RG R S -> erase R = erase S.
Proof.
  intros Delta RG R S Hsub. induction Hsub; simpl; try reflexivity.
  - f_equal.
    + symmetry. exact IHHsub.
    + specialize (H0 (fresh L) (fresh_notin L)).
      rewrite !erase_open_rty_tm in H0. exact H0.
  - rewrite erase_open_rty_tm in IHHsub. exact IHHsub.
  - specialize (H2 (fresh L) (fresh_notin L)).
    rewrite erase_open_rty_tm in H2. exact H2.
  - pose (X := fresh (L ++ fv_ty (erase R) ++ fv_ty (erase S))).
    assert (HX : ~ In X L).
    { unfold X. intro Hin. apply (fresh_notin (L ++ fv_ty (erase R) ++ fv_ty (erase S))).
      apply in_or_app. left. exact Hin. }
    specialize (H0 X HX).
    rewrite !erase_open_rty_ty in H0.
    f_equal. eapply open_ty_rec_injective.
    + unfold X. intro Hin. apply (fresh_notin (L ++ fv_ty (erase R) ++ fv_ty (erase S))).
      apply in_or_app. right. exact Hin.
    + exact H0.
  - rewrite IHHsub1, IHHsub2. reflexivity.
Qed.

Lemma lookup_erase_context : forall RG x,
  lookup_context x (erase_context RG) = option_map erase (lookup_rcontext x RG).
Proof.
  induction RG as [|[y R] RG IH]; intros x; simpl.
  - reflexivity.
  - destruct (Nat.eqb x y); simpl; auto.
Qed.

Lemma erase_context_update : forall RG x R,
  erase_context (update_rcontext RG x R) = update (erase_context RG) x (erase R).
Proof. reflexivity. Qed.

Lemma wf_rty_erasure_locally_closed : forall Delta RG R,
  wf_rty Delta RG R -> locally_closed_ty (erase R).
Proof.
  intros Delta RG R Hwf. induction Hwf; simpl.
  - eapply wf_ty_locally_closed; eassumption.
  - apply lc_ty_arrow.
    + assumption.
    + specialize (H0 (fresh L) (fresh_notin L)).
      rewrite erase_open_rty_tm in H0. exact H0.
  - specialize (H0 (fresh L) (fresh_notin L)).
    rewrite erase_open_rty_tm in H0. exact H0.
  - apply lc_ty_all. specialize (H0 (fresh L) (fresh_notin L)).
    rewrite erase_open_rty_ty in H0.
    eapply lc_ty_at_open_inv; eassumption.
Qed.

Lemma wf_rty_erases_to_wf_ty : forall Delta RG R,
  wf_rty Delta RG R -> wf_ty Delta (erase R).
Proof.
  intros Delta RG R Hwf. induction Hwf; simpl.
  - assumption.
  - apply WF_Arrow.
    + assumption.
    + specialize (H0 (fresh L) (fresh_notin L)).
      rewrite erase_open_rty_tm in H0. exact H0.
  - specialize (H0 (fresh L) (fresh_notin L)).
    rewrite erase_open_rty_tm in H0. exact H0.
  - apply WF_All with (L := L). intros X HX. specialize (H0 X HX).
    rewrite <- erase_open_rty_ty. exact H0.
Qed.

Lemma has_rtype_core : forall Delta RG t R,
  has_rtype Delta RG t R ->
  has_type Delta (erase_context RG) t (erase R).
Proof.
  intros Delta RG t R Hty. induction Hty.
  - econstructor.
    + rewrite lookup_erase_context. rewrite H. reflexivity.
    + eapply wf_rty_erases_to_wf_ty. eassumption.
  - eapply T_Abs with (L := L).
    + eapply wf_rty_erases_to_wf_ty. eassumption.
    + intros x Hx.
      specialize (H1 x Hx).
      rewrite erase_context_update in H1.
      rewrite erase_open_rty_tm in H1.
      exact H1.
  - eapply T_App; eassumption.
  - eapply T_TAbs with (L := L). intros X HX.
    specialize (H0 X HX). rewrite erase_open_rty_ty in H0. exact H0.
  - rewrite erase_open_rty_ty. eapply T_TApp; eauto.
  - constructor.
  - eapply T_Div; eassumption.
  - eapply T_Arith; eassumption.
  - eapply T_Choice; eassumption.
  - constructor.
  - constructor.
  - eapply T_If; eassumption.
  - exact H.
  - specialize (IHHty). rewrite <- (subtype_erase _ _ _ _ H0). exact IHHty.
Qed.

Lemma has_rtype_locally_closed : forall Delta RG t R,
  has_rtype Delta RG t R -> locally_closed_tm t.
Proof.
  intros Delta RG t R Hty. induction Hty.
  - unfold locally_closed_tm. constructor.
  - unfold locally_closed_tm. apply lc_tm_abs.
    + eapply wf_rty_erasure_locally_closed; eassumption.
    + eapply lc_tm_at_open_tm_inv.
      apply (H1 (fresh L) (fresh_notin L)).
  - unfold locally_closed_tm in *. apply lc_tm_app; assumption.
  - unfold locally_closed_tm. apply lc_tm_tabs.
    eapply lc_tm_at_open_ty_inv.
    apply (H0 (fresh L) (fresh_notin L)).
  - unfold locally_closed_tm in *. apply lc_tm_tapp.
    + assumption.
    + eapply wf_ty_locally_closed; eassumption.
  - unfold locally_closed_tm. constructor.
  - unfold locally_closed_tm in *. econstructor; eauto.
  - unfold locally_closed_tm in *. econstructor; eauto.
  - unfold locally_closed_tm in *. econstructor; eauto.
  - unfold locally_closed_tm. constructor.
  - unfold locally_closed_tm. constructor.
  - unfold locally_closed_tm in *. apply lc_tm_if; assumption.
  - eapply value_regular. eassumption.
  - assumption.
Qed.


Lemma logical_value_is_value : forall R v,
  logical_value R v -> value v.
Proof.
  intros R v H. destruct R.
  - rewrite logical_value_equation_1 in H. tauto.
  - rewrite logical_value_equation_2 in H. tauto.
  - rewrite logical_value_equation_3 in H. destruct H as [w [_ [Hv _]]]. exact Hv.
  - rewrite logical_value_equation_4 in H. tauto.
Qed.

Lemma logical_value_refinement : forall T p v,
  logical_value (R_Refine T p) v ->
  qualifier_holds (open_qualifier_tm p v).
Proof.
  intros T p v H. exact (proj2 H).
Qed.

Lemma logical_expr_one_safe : forall R t,
  logical_expr R t -> reducible t.
Proof.
  intros R t Hsafe. unfold reducible. intros t' Hmulti.
  destruct (Hsafe t' Hmulti) as [Hv|Hstep].
  - left. eapply logical_value_is_value. exact Hv.
  - right. exact Hstep.
Qed.

Lemma logical_expr_reduct : forall R t u,
  logical_expr R t -> multi t u -> logical_expr R u.
Proof.
  intros R t u Hexpr Htu v Huv. eapply Hexpr.
  eapply multi_trans; eassumption.
Qed.

Lemma logical_expr_of_value : forall R v,
  value v -> logical_value R v -> logical_expr R v.
Proof.
  intros R v Hv Hrel t' Hmulti.
  rewrite (value_multi_eq _ _ Hv Hmulti). left. exact Hrel.
Qed.

Lemma lookup_rcontext_update_eq : forall RG x R,
  lookup_rcontext x (update_rcontext RG x R) = Some R.
Proof. intros; simpl. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma lookup_rcontext_update_neq : forall RG x y R,
  x <> y -> lookup_rcontext y (update_rcontext RG x R) = lookup_rcontext y RG.
Proof.
  intros RG x y R Hneq. simpl. destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. congruence.
  - reflexivity.
Qed.

Lemma instantiate_tm_update_fresh : forall t theta gamma x u,
  ~ In x (fv_tm t) ->
  instantiate theta (term_subst_update gamma x u) t = instantiate theta gamma t.
Proof.
  induction t; intros theta gamma x u Hfresh; simpl in *; try reflexivity.
  - destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply Hfresh. simpl. auto.
    + unfold term_subst_update. rewrite E. reflexivity.
  - f_equal. eapply IHt. exact Hfresh.
  - f_equal; [eapply IHt1|eapply IHt2]; simpl in Hfresh; intuition.
  - f_equal. eapply IHt. exact Hfresh.
  - f_equal. eapply IHt. exact Hfresh.
  - f_equal; [eapply IHt1|eapply IHt2]; simpl in Hfresh; intuition.
  - f_equal; [eapply IHt1|eapply IHt2]; simpl in Hfresh; intuition.
  - f_equal; [eapply IHt1|eapply IHt2]; simpl in Hfresh; intuition.
  - f_equal.
    + eapply IHt1. intro Hin. apply Hfresh. apply in_or_app. left. exact Hin.
    + eapply IHt2. intro Hin. apply Hfresh. apply in_or_app. right.
      apply in_or_app. left. exact Hin.
    + eapply IHt3. intro Hin. apply Hfresh. apply in_or_app. right.
      apply in_or_app. right. exact Hin.
Qed.

Lemma instantiate_qualifier_update_fresh : forall p theta gamma x u,
  ~ In x (fv_qualifier p) ->
  instantiate_qualifier theta (term_subst_update gamma x u) p =
  instantiate_qualifier theta gamma p.
Proof.
  induction p; intros theta gamma x u Hfresh; simpl in *; try reflexivity.
  - f_equal; [eapply instantiate_tm_update_fresh|eapply instantiate_tm_update_fresh];
      simpl in Hfresh; intuition.
  - f_equal; [eapply instantiate_tm_update_fresh|eapply instantiate_tm_update_fresh];
      simpl in Hfresh; intuition.
  - f_equal; [eapply instantiate_tm_update_fresh|eapply instantiate_tm_update_fresh];
      simpl in Hfresh; intuition.
  - f_equal; [eapply IHp1|eapply IHp2]; simpl in Hfresh; intuition.
  - f_equal; [eapply IHp1|eapply IHp2]; simpl in Hfresh; intuition.
  - f_equal. eapply IHp. simpl in Hfresh. exact Hfresh.
Qed.

Lemma instantiate_rty_update_fresh : forall R theta gamma x u,
  ~ In x (fv_rty R) ->
  instantiate_rty theta (term_subst_update gamma x u) R =
  instantiate_rty theta gamma R.
Proof.
  induction R; intros theta gamma x u Hfresh; simpl in *.
  - f_equal. eapply instantiate_qualifier_update_fresh. exact Hfresh.
  - f_equal; [eapply IHR1|eapply IHR2]; simpl in Hfresh; intuition.
  - f_equal; [eapply IHR1|eapply IHR2]; simpl in Hfresh; intuition.
  - f_equal. eapply IHR. exact Hfresh.
Qed.

Lemma instantiate_ty_preserves_lc_at : forall T k theta,
  type_substitution_closed theta -> lc_ty_at k T ->
  lc_ty_at k (instantiate_ty theta T).
Proof.
  induction T; intros k theta Htheta Hlc; simpl in *.
  - inversion Hlc; subst. apply lc_ty_bvar. assumption.
  - eapply lc_ty_at_monotone. apply Htheta. lia.
  - inversion Hlc; subst. apply lc_ty_arrow.
    + eapply IHT1; eassumption.
    + eapply IHT2; eassumption.
  - inversion Hlc; subst. apply lc_ty_all. eapply IHT; eassumption.
  - constructor.
  - constructor.
Qed.

Lemma instantiate_ty_preserves_lc : forall T theta,
  type_substitution_closed theta -> locally_closed_ty T ->
  locally_closed_ty (instantiate_ty theta T).
Proof.
  intros T theta Htheta Hlc. eapply instantiate_ty_preserves_lc_at; eassumption.
Qed.

Lemma instantiate_preserves_lc_at : forall t K k theta gamma,
  type_substitution_closed theta -> term_substitution_closed gamma ->
  lc_tm_at K k t -> lc_tm_at K k (instantiate theta gamma t).
Proof.
  induction t; intros K k theta gamma Htheta Hgamma Hlc; simpl in *.
  - inversion Hlc; subst. apply lc_tm_bvar. assumption.
  - eapply lc_tm_at_monotone.
    + apply Hgamma.
    + lia.
    + lia.
  - inversion Hlc; subst. apply lc_tm_abs.
    + eapply instantiate_ty_preserves_lc_at; eassumption.
    + eapply IHt; eassumption.
  - inversion Hlc; subst. apply lc_tm_app.
    + eapply IHt1; eassumption.
    + eapply IHt2; eassumption.
  - inversion Hlc; subst. apply lc_tm_tabs. eapply IHt; eassumption.
  - inversion Hlc; subst. apply lc_tm_tapp.
    + eapply IHt; eassumption.
    + eapply instantiate_ty_preserves_lc_at; eassumption.
  - constructor.
  - inversion Hlc; subst. apply lc_tm_div; eauto.
  - inversion Hlc; subst. apply lc_tm_arith; eauto.
  - inversion Hlc; subst. apply lc_tm_choice; eauto.
  - constructor.
  - constructor.
  - inversion Hlc; subst. apply lc_tm_if; eauto.
Qed.

Lemma instantiate_preserves_lc : forall t theta gamma,
  type_substitution_closed theta -> term_substitution_closed gamma ->
  locally_closed_tm t -> locally_closed_tm (instantiate theta gamma t).
Proof.
  intros t theta gamma Htheta Hgamma Hlc.
  eapply instantiate_preserves_lc_at; eassumption.
Qed.

Lemma predicate_multistep_to_multi : forall t u,
  predicate_multistep t u -> multi t u.
Proof.
  intros t u H. induction H.
  - constructor.
  - econstructor; eauto.
Qed.

Lemma multi_to_predicate_multistep : forall t u,
  multi t u -> predicate_multistep t u.
Proof.
  intros t u H. induction H.
  - constructor.
  - econstructor; eauto.
Qed.

Lemma predicate_multistep_int_refl : forall n t,
  predicate_multistep (tm_int n) t -> t = tm_int n.
Proof.
  intros n t H. apply value_multi_eq with (v := tm_int n).
  - constructor.
  - apply predicate_multistep_to_multi. exact H.
Qed.

Lemma interpreted_ne_zero : forall n,
  qualifier_holds (Pred_Ne (tm_int n) (tm_int 0%Z)) -> n <> 0%Z.
Proof.
  intros n Hne E. subst n. apply Hne. unfold Pred_Ne, qualifier_holds,
    predicate_holds, interpret_qualifier, operational_atoms; simpl.
  exists (tm_int 0%Z). split; [constructor|]. split; [constructor|constructor].
Qed.

Definition qualifier_context_holds (RG : rcontext) (gamma : term_substitution) : Prop :=
  forall x T p,
    lookup_rcontext x RG = Some (R_Refine T p) ->
    qualifier_holds
      (instantiate_qualifier identity_type_substitution gamma
        (open_qualifier_tm p (tm_fvar x))).


Lemma entails_sound : forall Delta RG p q,
  entails Delta RG p q ->
  forall gamma,
    qualifier_context_holds RG gamma ->
    qualifier_holds (instantiate_qualifier identity_type_substitution gamma p) ->
    qualifier_holds (instantiate_qualifier identity_type_substitution gamma q).
Proof.
  intros Delta RG p q Hent. induction Hent; intros gamma Hctx Hp;
    unfold qualifier_holds, predicate_holds in *; simpl in *.
  - exact Hp.
  - exact I.
  - eapply IHHent2; [exact Hctx|]. eapply IHHent1; eassumption.
  - destruct Hp as [Hp _]. exact Hp.
  - destruct Hp as [_ Hq]. exact Hq.
  - split.
    + eapply IHHent1; eassumption.
    + eapply IHHent2; eassumption.
  - left. exact Hp.
  - right. exact Hp.
  - destruct Hp as [Hp|Hq].
    + eapply IHHent1; eassumption.
    + eapply IHHent2; eassumption.
  - intros Hq. apply (IHHent gamma Hctx).
    split; assumption.
  - destruct Hp as [Hp Hnot]. contradiction.
  - eapply Hctx. exact H.
  - contradiction.
Qed.

Lemma qualifier_context_holds_empty : forall gamma,
  qualifier_context_holds [] gamma.
Proof.
  intros gamma x T p Hlookup. discriminate.
Qed.

Lemma entails_sound_empty : forall Delta p q,
  entails Delta [] p q ->
  forall gamma,
    qualifier_holds (instantiate_qualifier identity_type_substitution gamma p) ->
    qualifier_holds (instantiate_qualifier identity_type_substitution gamma q).
Proof.
  intros Delta p q Hent gamma Hp.
  eapply entails_sound; [exact Hent|apply qualifier_context_holds_empty|exact Hp].
Qed.

Lemma reducible_of_all_steps : forall t,
  (value t \/ exists u, t --> u) ->
  (forall u, t --> u -> reducible u) -> reducible t.
Proof.
  intros t Hprogress Hsteps t' Hmulti.
  inversion Hmulti; subst.
  - exact Hprogress.
  - unfold reducible in Hsteps.
    eapply Hsteps; eassumption.
Qed.

Lemma canonical_fun : forall v A B,
  value v -> has_type [] [] v (Ty_Arrow A B) ->
  exists T b, v = tm_abs T b.
Proof.
  intros v A B Hv Hty. inversion Hv; subst; inversion Hty; subst; eauto.
Qed.

Lemma canonical_poly : forall v A,
  value v -> has_type [] [] v (Ty_All A) ->
  exists b, v = tm_tabs b.
Proof.
  intros v A Hv Hty. inversion Hv; subst; inversion Hty; subst; eauto.
Qed.

Lemma canonical_int : forall v,
  value v -> has_type [] [] v Ty_Int -> exists n, v = tm_int n.
Proof.
  intros v Hv Hty. inversion Hv; subst; inversion Hty; subst; eauto.
Qed.

Lemma canonical_bool : forall v,
  value v -> has_type [] [] v Ty_Bool -> v = tm_true \/ v = tm_false.
Proof.
  intros v Hv Hty. inversion Hv; subst; inversion Hty; subst; eauto.
Qed.

Definition fundamental_typing_property
    (Delta : ty_context) (RG : rcontext) (t : tm) (R : rty)
    (_ : has_rtype Delta RG t R) : Prop :=
  forall theta gamma,
    type_substitution_closed theta -> term_substitution_closed gamma ->
    context_interpretation RG theta gamma ->
    logical_expr (instantiate_rty theta gamma R)
      (instantiate theta gamma t).

Definition fundamental_subtype_property
    (Delta : ty_context) (RG : rcontext) (R S : rty)
    (_ : subtype Delta RG R S) : Prop :=
  forall theta gamma,
    type_substitution_closed theta -> term_substitution_closed gamma ->
    context_interpretation RG theta gamma ->
    forall v,
      logical_value (instantiate_rty theta gamma R) v ->
      logical_value (instantiate_rty theta gamma S) v.

Theorem fundamental :
  (forall Delta RG t R (H : has_rtype Delta RG t R),
    fundamental_typing_property Delta RG t R H) /\
  (forall Delta RG R S (H : subtype Delta RG R S),
    fundamental_subtype_property Delta RG R S H).
Proof.
  apply refinement_typing_mutind; unfold fundamental_typing_property,
    fundamental_subtype_property; intros.
  - unfold logical_expr. intros t' Hmulti.
    pose proof (H1 x R e) as Hvalrel.
    pose proof (logical_value_is_value _ _ Hvalrel) as Hv.
    rewrite (value_multi_eq _ _ Hv Hmulti). left. exact Hvalrel.
  - assert (Hlcbody : lc_tm_at 0 1 body).
    { eapply lc_tm_at_open_tm_inv.
      apply (has_rtype_locally_closed _ _ _ _ (h (fresh L) (fresh_notin L))). }
    assert (Hlcabs : locally_closed_tm (tm_abs (erase R1) body)).
    { unfold locally_closed_tm. apply lc_tm_abs.
      - eapply wf_rty_erasure_locally_closed. exact w.
      - exact Hlcbody. }
    set (x := fresh (L ++ fv_tm body ++ fv_rty R2 ++ fv_rcontext RGamma ++ fv_rty R1)).
    assert (HxL : ~ In x L).
    { unfold x. intro Hin. apply (fresh_notin (L ++ fv_tm body ++ fv_rty R2 ++ fv_rcontext RGamma ++ fv_rty R1)).
      apply in_or_app. left. exact Hin. }
    assert (Hxbody : ~ In x (fv_tm body)).
    { unfold x. intro Hin. apply (fresh_notin (L ++ fv_tm body ++ fv_rty R2 ++ fv_rcontext RGamma ++ fv_rty R1)).
      apply in_or_app. right. apply in_or_app. left. exact Hin. }
    assert (HxR2 : ~ In x (fv_rty R2)).
    { unfold x. intro Hin. apply (fresh_notin (L ++ fv_tm body ++ fv_rty R2 ++ fv_rcontext RGamma ++ fv_rty R1)).
      apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hin. }
    assert (HxRG : ~ In x (fv_rcontext RGamma)).
    { unfold x. intro Hin. apply (fresh_notin (L ++ fv_tm body ++ fv_rty R2 ++ fv_rcontext RGamma ++ fv_rty R1)).
      apply in_or_app. right. apply in_or_app. right. apply in_or_app. right.
      apply in_or_app. left. exact Hin. }
    assert (HxR1 : ~ In x (fv_rty R1)).
    { unfold x. intro Hin. apply (fresh_notin (L ++ fv_tm body ++ fv_rty R2 ++ fv_rcontext RGamma ++ fv_rty R1)).
      apply in_or_app. right. apply in_or_app. right. apply in_or_app. right.
      apply in_or_app. right. exact Hin. }
    assert (Hlcinst : locally_closed_tm
      (instantiate theta gamma (tm_abs (erase R1) body))).
    { eapply instantiate_preserves_lc; eauto. }
    change (logical_expr
      (R_Func (instantiate_rty theta gamma R1) (instantiate_rty theta gamma R2))
      (tm_abs (instantiate_ty theta (erase R1)) (instantiate theta gamma body))).
    apply logical_expr_of_value.
    + eapply v_abs. exact Hlcinst.
    + rewrite logical_value_equation_2. split.
      * eapply v_abs. exact Hlcinst.
      * intros arg Harg.
      set (gamma' := term_subst_update gamma x arg).
      assert (Harglc : locally_closed_tm arg).
      { eapply value_regular. eapply logical_value_is_value. exact Harg. }
      assert (Hgamma' : term_substitution_closed gamma').
      { unfold gamma'. eapply term_subst_update_closed; eauto. }
      assert (Hctx' : context_interpretation (update_rcontext RGamma x R1) theta gamma').
      { intros y S Hlookup. unfold update_rcontext in Hlookup. simpl in Hlookup.
        destruct (Nat.eqb y x) eqn:E.
        - apply Nat.eqb_eq in E. subst y. inversion Hlookup; subst S.
          Show.
          unfold gamma'. unfold term_subst_update. rewrite Nat.eqb_refl. exact Harg.
        - assert (Exy : Nat.eqb x y = false).
          { rewrite Nat.eqb_sym. exact E. }
          assert (Hbase : lookup_rcontext y RGamma = Some S) by exact Hlookup.
          pose proof (H2 y S Hbase) as Hold.
          unfold gamma'. unfold term_subst_update. rewrite Exy.
          rewrite (instantiate_rty_update_fresh S theta gamma x arg).
          + exact Hold.
          + intro Hin. apply HxRG. simpl. apply in_or_app. right. exact Hin. }
      pose proof (H x HxL theta gamma' H0 Hgamma' Hctx') as Hbody.
      assert (Hbody_tm : instantiate theta gamma'
          (open_tm body (tm_fvar x)) =
        open_tm (instantiate theta gamma body) arg).
      { rewrite instantiate_open_tm; auto.
        - unfold gamma'. simpl. rewrite Nat.eqb_refl. rewrite instantiate_tm_update_fresh.
          + reflexivity.
          + exact Hxbody.
        - exact H0.
        - exact Hgamma'. }
      assert (Hbody_ty : instantiate_rty theta gamma'
          (open_rty_tm R2 (tm_fvar x)) =
        open_rty_tm (instantiate_rty theta gamma R2) arg).
      { rewrite instantiate_open_rty_tm; auto.
        - unfold gamma'. simpl. rewrite Nat.eqb_refl.
          rewrite instantiate_rty_update_fresh.
          + reflexivity.
          + exact HxR2.
        - exact H0.
        - exact Hgamma'. }
      unfold logical_expr in Hbody. rewrite Hbody_tm, Hbody_ty in Hbody.
      intros t' Hmulti. inversion Hmulti; subst.
      * right. exists (open_tm (instantiate theta gamma body) arg).
        eapply ST_AppAbs; eauto.
      * inversion H; subst.
        -- eapply Hbody. exact H0.
        -- exfalso. eapply value_no_step; eauto using v_abs.
        -- exfalso. eapply value_no_step; eauto.
Qed.

Theorem never_stuck : forall (t t' : tm) (R : rty),
  has_rtype [] empty_rcontext t R ->
  multi t t' ->
  value t' \/ exists t'' : tm, t' --> t''.
Proof.
  (* Complete this proof. *)
Qed.

End SystemFRefinementIfNonDeterminismTask.
