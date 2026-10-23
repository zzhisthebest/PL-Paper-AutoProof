From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
From Stdlib Require Import ZArith.BinInt.

Module SystemFRefinementIfNonDeterminismRecursion.

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

  | tm_fix : ty -> ty -> tm -> tm -> tm
  | tm_ifzero : tm -> tm -> tm -> tm
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
  | tm_fix A B metric body =>
      tm_fix (A) (B)
        (open_tm_rec (S k) u metric) (open_tm_rec (S (S k)) u body)
  | tm_ifzero t t0 t1 =>
      tm_ifzero (open_tm_rec k u t) (open_tm_rec k u t0) (open_tm_rec k u t1)
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
  | tm_fix A B metric body => fv_tm metric ++ fv_tm body
  | tm_ifzero t t0 t1 => fv_tm t ++ fv_tm t0 ++ fv_tm t1
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
  | tm_fix A B metric body => fv_ty A ++ fv_ty B ++ ftv_tm metric ++ ftv_tm body
  | tm_ifzero t t0 t1 => ftv_tm t ++ ftv_tm t0 ++ ftv_tm t1
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
  | tm_fix A B metric body =>
      tm_fix (open_ty_rec k U A) (open_ty_rec k U B)
        (open_tm_ty_rec k U metric) (open_tm_ty_rec k U body)
  | tm_ifzero t t0 t1 =>
      tm_ifzero (open_tm_ty_rec k U t) (open_tm_ty_rec k U t0) (open_tm_ty_rec k U t1)
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
  | tm_fix A B metric body =>
      tm_fix (ty_subst X U A) (ty_subst X U B)
        (tm_ty_subst X U metric) (tm_ty_subst X U body)
  | tm_ifzero t t0 t1 =>
      tm_ifzero (tm_ty_subst X U t) (tm_ty_subst X U t0) (tm_ty_subst X U t1)
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
  | tm_fix A B metric body =>
      tm_fix (A) (B)
        (tm_subst x s metric) (tm_subst x s body)
  | tm_ifzero t t0 t1 =>
      tm_ifzero (tm_subst x s t) (tm_subst x s t0) (tm_subst x s t1)
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
      lc_tm_at K k t1 -> lc_tm_at K k t2 ->
      lc_tm_at K k (tm_arith op t1 t2)
  | lc_tm_fix : forall K k A B metric body,
      lc_ty_at K A -> lc_ty_at K B ->
      lc_tm_at K (S k) metric ->
      lc_tm_at K (S (S k)) body ->
      lc_tm_at K k (tm_fix A B metric body)
  | lc_tm_ifzero : forall K k t t0 t1,
      lc_tm_at K k t -> lc_tm_at K k t0 -> lc_tm_at K k t1 ->
      lc_tm_at K k (tm_ifzero t t0 t1)
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
  | v_fix : forall A B metric body,
      locally_closed_tm (tm_fix A B metric body) ->
      value (tm_fix A B metric body)
  | v_true : value tm_true
  | v_false : value tm_false.

Definition open_fix_body (body f x : tm) : tm :=
  open_tm (open_tm_rec 1 f body) x.

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
  | ST_AppFix : forall A B metric body v,
      locally_closed_tm (tm_fix A B metric body) ->
      value v ->
      tm_app (tm_fix A B metric body) v -->
        open_fix_body body (tm_fix A B metric body) v
  | ST_IfZeroArg : forall t t' t0 t1,
      t --> t' -> locally_closed_tm t0 -> locally_closed_tm t1 ->
      tm_ifzero t t0 t1 --> tm_ifzero t' t0 t1
  | ST_IfZero : forall t0 t1,
      locally_closed_tm t0 -> locally_closed_tm t1 ->
      tm_ifzero (tm_int 0%Z) t0 t1 --> t0
  | ST_IfNonzero : forall (n : Z) t0 t1,
      n <> 0%Z -> locally_closed_tm t0 -> locally_closed_tm t1 ->
      tm_ifzero (tm_int n) t0 t1 --> t1
  | ST_ChoiceLeft : forall t1 t2,
      locally_closed_tm t1 -> locally_closed_tm t2 -> tm_choice t1 t2 --> t1
  | ST_ChoiceRight : forall t1 t2,
      locally_closed_tm t1 -> locally_closed_tm t2 -> tm_choice t1 t2 --> t2
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
  | T_Fix : forall (L : list atom) Delta Gamma A B metric body,
      wf_ty Delta A -> wf_ty Delta B ->
      (forall x, ~ In x L ->
        has_type Delta (update Gamma x A)
          (open_tm metric (tm_fvar x)) Ty_Int) ->
      (forall f x, ~ In f L -> ~ In x (f :: L) ->
        has_type Delta (update (update Gamma x A) f (Ty_Arrow A B))
          (open_fix_body body (tm_fvar f) (tm_fvar x)) B) ->
      has_type Delta Gamma (tm_fix A B metric body) (Ty_Arrow A B)
  | T_IfZero : forall Delta Gamma t t0 t1 T,
      has_type Delta Gamma t Ty_Int ->
      has_type Delta Gamma t0 T -> has_type Delta Gamma t1 T ->
      has_type Delta Gamma (tm_ifzero t t0 t1) T
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

End SystemFRefinementIfNonDeterminismRecursion.

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
Module SystemFRefinementIfNonDeterminismRecursionInfrastructure.
Import ListNotations.
Import SystemFRefinementIfNonDeterminismRecursion.

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
  - apply lc_tm_fix; eauto using lc_ty_at_monotone; [apply IHHlc1|apply IHHlc2]; lia.
  - apply lc_tm_ifzero; eauto.
  - try (inversion Hlc; subst). apply lc_tm_choice; eauto.
  - constructor.
  - constructor.
  - try (inversion Hlc; subst). apply lc_tm_if; eauto.
Qed.

Lemma open_ty_rec_lc_at : forall T k U,
  lc_ty_at k T ->
  open_ty_rec k U T = T.
Proof.
  intros T k U Hlc. induction Hlc; simpl; try rewrite ?IHHlc1, ?IHHlc2, ?IHHlc3, ?IHHlc3;
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
    try rewrite ?IHHlc, ?IHHlc1, ?IHHlc2, ?IHHlc3, ?IHHlc3; try reflexivity.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + reflexivity.
Qed.

Lemma open_tm_ty_rec_lc_at : forall t K k U,
  lc_tm_at K k t ->
  open_tm_ty_rec K U t = t.
Proof.
  intros t K k U Hlc. induction Hlc; simpl;
    try rewrite ?IHHlc1, ?IHHlc2, ?IHHlc3, ?IHHlc3; try reflexivity.
  - erewrite open_ty_rec_lc_at; eauto. rewrite IHHlc. reflexivity.
  - rewrite IHHlc. reflexivity.
  - rewrite IHHlc. erewrite open_ty_rec_lc_at; eauto.
  - rewrite !open_ty_rec_lc_at by assumption. reflexivity.
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
  - inversion Hlc; subst. apply lc_ty_arrow; eauto.
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
  - inversion Hlc; subst. apply lc_tm_fix; eauto.
  - inversion Hlc; subst. apply lc_tm_ifzero; eauto.
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
  - inversion Hlc; subst. apply lc_tm_fix; eauto using lc_ty_at_open_inv.
  - inversion Hlc; subst. apply lc_tm_ifzero; eauto.
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
  | tm_fix A B metric body => tm_fix (instantiate_ty theta A) (instantiate_ty theta B)
      (instantiate theta gamma metric) (instantiate theta gamma body)
  | tm_ifzero t t0 t1 => tm_ifzero (instantiate theta gamma t)
      (instantiate theta gamma t0) (instantiate theta gamma t1)
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

End SystemFRefinementIfNonDeterminismRecursionInfrastructure.

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
Module SystemFRefinementIfNonDeterminismRecursionCoreTyping.
Import ListNotations.
Import SystemFRefinementIfNonDeterminismRecursion.
Import SystemFRefinementIfNonDeterminismRecursionInfrastructure.

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

End SystemFRefinementIfNonDeterminismRecursionCoreTyping.

From Stdlib Require Import Arith.PeanoNat Lists.List ZArith.BinInt.
Module SystemFRefinementIfNonDeterminismRecursionLogic.
Import ListNotations SystemFRefinementIfNonDeterminismRecursion.

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

End SystemFRefinementIfNonDeterminismRecursionLogic.

From Stdlib Require Import Arith.PeanoNat Lists.List Lia ZArith.BinInt.
Module SystemFRefinementIfNonDeterminismRecursionTyping.
Import ListNotations.
Import SystemFRefinementIfNonDeterminismRecursion.
Export SystemFRefinementIfNonDeterminismRecursionLogic.
Import SystemFRefinementIfNonDeterminismRecursionInfrastructure.

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
Fixpoint instantiate_formula
    (theta : type_substitution) (gamma : term_substitution)
    (p : qualifier) : qualifier :=
  match p with
  | Pred_True => Pred_True
  | Pred_False => Pred_False
  | Pred_Eq t1 t2 => Pred_Eq (instantiate theta gamma t1) (instantiate theta gamma t2)
  | Pred_Lt t1 t2 => Pred_Lt (instantiate theta gamma t1) (instantiate theta gamma t2)
  | Pred_Le t1 t2 => Pred_Le (instantiate theta gamma t1) (instantiate theta gamma t2)
  | Pred_And p q => Pred_And (instantiate_formula theta gamma p) (instantiate_formula theta gamma q)
  | Pred_Or p q => Pred_Or (instantiate_formula theta gamma p) (instantiate_formula theta gamma q)
  | Pred_Not p => Pred_Not (instantiate_formula theta gamma p)
  end.

Definition context_formulas_hold
    (theta : type_substitution) (gamma : term_substitution)
    (RGamma : rcontext) : Prop :=
  forall x T p,
    lookup_rcontext x RGamma = Some (R_Refine T p) ->
    qualifier_holds
      (instantiate_formula theta gamma (open_qualifier_tm p (tm_fvar x))).

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
      entails Delta RGamma Pred_False q

  | Entails_Valid : forall Delta RGamma p q,
      (forall (theta : type_substitution) (gamma : term_substitution),
        (forall x, value (gamma x)) ->
        context_formulas_hold theta gamma RGamma ->
        qualifier_holds (instantiate_formula theta gamma p) ->
        qualifier_holds (instantiate_formula theta gamma q)) ->
      entails Delta RGamma p q.

Definition measured_input (A : ty) (p : qualifier) (metric : tm) : rty :=
  R_Refine A (Pred_And p (Pred_Ge metric (tm_int 0%Z))).

Definition smaller_input
    (A : ty) (p : qualifier) (metric current_metric : tm) : rty :=
  R_Refine A
    (Pred_And p
      (Pred_And (Pred_Ge metric (tm_int 0%Z))
                (Pred_Lt metric current_metric))).

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
      has_rtype Delta RGamma (tm_div t1 t2)
        (R_Refine Ty_Int (Pred_Eq (tm_bvar 0) (tm_div t1 t2)))
  | RT_Arith : forall Delta RGamma op t1 t2,
      has_rtype Delta RGamma t1 (R_Refine Ty_Int Pred_True) ->
      has_rtype Delta RGamma t2 (R_Refine Ty_Int Pred_True) ->
      has_rtype Delta RGamma (tm_arith op t1 t2)
        (R_Refine Ty_Int (Pred_Eq (tm_bvar 0) (tm_arith op t1 t2)))

  | RT_Choice : forall Delta RGamma t1 t2 R,
      has_rtype Delta RGamma t1 R -> has_rtype Delta RGamma t2 R ->
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

  | RT_Fix : forall (L : list atom) Delta RGamma A p metric body R2,
      wf_rty Delta RGamma (R_Func (measured_input A p metric) R2) ->
      (forall x, ~ In x L ->
        has_type Delta (update (erase_context RGamma) x A)
          (open_tm metric (tm_fvar x)) Ty_Int) ->
      (forall f x, ~ In f L -> ~ In x (f :: L) ->
        has_rtype Delta
          (update_rcontext
            (update_rcontext RGamma x (measured_input A p metric))
            f (R_Func
                (smaller_input A p metric (open_tm metric (tm_fvar x))) R2))
          (open_fix_body body (tm_fvar f) (tm_fvar x))
          (open_rty_tm R2 (tm_fvar x))) ->
      has_rtype Delta RGamma (tm_fix A (erase R2) metric body)
        (R_Func (measured_input A p metric) R2)

  | RT_IfZero : forall Delta RGamma x p t0 t1 R,
      lookup_rcontext x RGamma = Some (R_Refine Ty_Int p) ->
      has_rtype Delta
        (update_rcontext RGamma x
          (R_Refine Ty_Int (Pred_And p (Pred_Eq (tm_bvar 0) (tm_int 0%Z))))) t0 R ->
      has_rtype Delta
        (update_rcontext RGamma x
          (R_Refine Ty_Int (Pred_And p (Pred_Ne (tm_bvar 0) (tm_int 0%Z))))) t1 R ->
      has_rtype Delta RGamma (tm_ifzero (tm_fvar x) t0 t1) R

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

End SystemFRefinementIfNonDeterminismRecursionTyping.

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Module SystemFRefinementIfNonDeterminismRecursionEvaluation.
Import ListNotations SystemFRefinementIfNonDeterminismRecursion SystemFRefinementIfNonDeterminismRecursionInfrastructure
  SystemFRefinementIfNonDeterminismRecursionCoreTyping.

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
  - apply lc_tm_fix.
    + apply lc_ty_at_open; [assumption |]. eapply lc_ty_at_monotone; [exact HU | lia].
    + apply lc_ty_at_open; [assumption |]. eapply lc_ty_at_monotone; [exact HU | lia].
    + eapply IHt1; eauto.
    + eapply IHt2; eauto.
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

End SystemFRefinementIfNonDeterminismRecursionEvaluation.

From Stdlib Require Import Arith.PeanoNat Lists.List Lia Program.Wf.
From Equations Require Import Equations.
Module SystemFRefinementIfNonDeterminismRecursionSubstitution.
Import ListNotations.
Import SystemFRefinementIfNonDeterminismRecursion.
Import SystemFRefinementIfNonDeterminismRecursionInfrastructure.
Import SystemFRefinementIfNonDeterminismRecursionCoreTyping.
Import SystemFRefinementIfNonDeterminismRecursionTyping.
Import SystemFRefinementIfNonDeterminismRecursionEvaluation.

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
End SystemFRefinementIfNonDeterminismRecursionSubstitution.

Module SystemFRefinementIfNonDeterminismRecursionTask.
Import ListNotations SystemFRefinementIfNonDeterminismRecursion SystemFRefinementIfNonDeterminismRecursionInfrastructure SystemFRefinementIfNonDeterminismRecursionCoreTyping SystemFRefinementIfNonDeterminismRecursionLogic SystemFRefinementIfNonDeterminismRecursionTyping SystemFRefinementIfNonDeterminismRecursionEvaluation SystemFRefinementIfNonDeterminismRecursionSubstitution .

Lemma erase_open_rty_tm_rec : forall k u R,
  erase (open_rty_tm_rec k u R) = erase R.
Proof.
  intros k u R; revert k u; induction R; intros k u; simpl; try rewrite IHR1; try rewrite IHR2;
    try rewrite IHR; reflexivity.
Qed.

Lemma erase_open_rty_tm : forall R u,
  erase (open_rty_tm R u) = erase R.
Proof. intros; apply erase_open_rty_tm_rec. Qed.

Lemma erase_open_rty_ty_rec : forall k U R,
  erase (open_rty_ty_rec k U R) = open_ty_rec k U (erase R).
Proof.
  intros k U R; revert k U; induction R; intros k U; simpl; try rewrite IHR1; try rewrite IHR2;
    try rewrite IHR; reflexivity.
Qed.

Lemma erase_open_rty_ty : forall R U,
  erase (open_rty_ty R U) = open_ty (erase R) U.
Proof. intros; apply erase_open_rty_ty_rec. Qed.

Lemma erase_context_update : forall RGamma x R,
  erase_context (update_rcontext RGamma x R) =
  update (erase_context RGamma) x (erase R).
Proof. reflexivity. Qed.

Lemma open_ty_rec_fresh_injective : forall k X T U,
  ~ In X (fv_ty T) -> ~ In X (fv_ty U) ->
  open_ty_rec k (Ty_FVar X) T = open_ty_rec k (Ty_FVar X) U -> T = U.
Proof.
  intros k X T; revert k X; induction T; intros k X U HX HU Heq; destruct U; simpl in *;
    try discriminate; try reflexivity.
  all: try solve [
    destruct (Nat.eqb k n) eqn:E1; destruct (Nat.eqb k n0) eqn:E2;
      simpl in Heq; try discriminate;
      [apply Nat.eqb_eq in E1; apply Nat.eqb_eq in E2; congruence
      | inversion Heq; reflexivity]
  ].
  all: try solve [
    destruct (Nat.eqb k n) eqn:E; simpl in Heq; try discriminate;
    inversion Heq; subst; exfalso; apply HU; simpl; left; reflexivity
  ].
  all: try solve [
    destruct (Nat.eqb k n) eqn:E; simpl in Heq; try discriminate;
    inversion Heq; subst; exfalso; apply HX; simpl; left; reflexivity
  ].
  all: try congruence.
  - inversion Heq; subst; f_equal.
    + apply (IHT1 k X U1).
      * intro Hin; apply HX; apply in_or_app; left; exact Hin.
      * intro Hin; apply HU; apply in_or_app; left; exact Hin.
      * exact H0.
    + apply (IHT2 k X U2).
      * intro Hin; apply HX; apply in_or_app; right; exact Hin.
      * intro Hin; apply HU; apply in_or_app; right; exact Hin.
      * exact H1.
  - inversion Heq; subst; f_equal.
    apply (IHT (S k) X U).
    + exact HX.
    + exact HU.
    + congruence.
Qed.

Lemma subtype_erases : forall Delta RGamma R S,
  subtype Delta RGamma R S -> erase R = erase S.
Proof.
  intros Delta RGamma R S Hsub; induction Hsub; simpl in *; try reflexivity.
  - f_equal.
    + symmetry; exact IHHsub.
    + specialize (H0 (fresh L) (fresh_notin L)).
      rewrite !erase_open_rty_tm in H0. exact H0.
  - rewrite erase_open_rty_tm in IHHsub. exact IHHsub.
  - specialize (H2 (fresh L) (fresh_notin L)).
    rewrite erase_open_rty_tm in H2. exact H2.
  - set (X := fresh (L ++ fv_ty (erase R) ++ fv_ty (erase S))).
    assert (HX : ~ In X (L ++ fv_ty (erase R) ++ fv_ty (erase S))).
    { unfold X. apply fresh_notin. }
    assert (HXL : ~ In X L).
    { intro HIn. apply HX. apply in_or_app. left; exact HIn. }
    assert (HXR : ~ In X (fv_ty (erase R))).
    { intro HIn. apply HX. apply in_or_app. right. apply in_or_app. left; exact HIn. }
    assert (HXS : ~ In X (fv_ty (erase S))).
    { intro HIn. apply HX. apply in_or_app. right. apply in_or_app. right; exact HIn. }
    specialize (H0 X HXL). rewrite !erase_open_rty_ty in H0.
    f_equal. eapply open_ty_rec_fresh_injective; eauto.
  - etransitivity; eauto.
Qed.

Lemma lookup_erased_rcontext : forall x RGamma R,
  lookup_rcontext x RGamma = Some R ->
  lookup_context x (erase_context RGamma) = Some (erase R).
Proof.
  intros x RGamma; induction RGamma as [|[y S] RGamma IH]; intros R H;
    simpl in *; try discriminate.
  unfold update_rcontext in *. simpl in *.
  destruct (Nat.eqb x y) eqn:E.
  - inversion H; subst. unfold update. simpl. reflexivity.
  - unfold update. simpl. eapply IH. exact H.
Qed.

Lemma wf_rty_erases : forall Delta RGamma R,
  wf_rty Delta RGamma R -> wf_ty Delta (erase R).
Proof.
  intros Delta RGamma R Hwf; induction Hwf; simpl.
  - assumption.
  - constructor; [exact IHHwf|].
    specialize (H0 (fresh L) (fresh_notin L)).
    rewrite erase_open_rty_tm in H0. exact H0.
  - specialize (H0 (fresh L) (fresh_notin L)).
    rewrite erase_open_rty_tm in H0. exact H0.
  - eapply WF_All. intros X HX. specialize (H0 X HX).
    rewrite erase_open_rty_ty in H0. exact H0.
Qed.

Lemma lookup_update_equiv : forall Gamma Gamma' x T y,
  lookup_context y Gamma = lookup_context y Gamma' ->
  lookup_context y (update Gamma x T) =
  lookup_context y (update Gamma' x T).
Proof.
  intros. unfold update. simpl. destruct (Nat.eqb y x); auto.
Qed.

Lemma has_type_context_equiv : forall Delta Gamma t T,
  has_type Delta Gamma t T -> forall Gamma',
  (forall x, lookup_context x Gamma = lookup_context x Gamma') ->
  has_type Delta Gamma' t T.
Proof.
  intros Delta Gamma t T Hty; induction Hty; intros Gamma' Heq.
  - eapply T_Var; [rewrite <- Heq; eassumption|assumption].
  - eapply T_Abs; [assumption|]. intros x Hx.
    eapply H1; [exact Hx|]. intro y. apply lookup_update_equiv. apply Heq.
  - eapply T_App; eauto.
  - eapply T_TAbs. intros X HX. eapply H0; eauto.
  - eapply T_TApp; eauto.
  - constructor.
  - eapply T_Div; eauto.
  - eapply T_Arith; eauto.
  - eapply T_Fix; try assumption.
    + intros x Hx. eapply H2; [exact Hx|].
      intro y. apply lookup_update_equiv. apply Heq.
    + intros f x Hf Hx. eapply H4; [exact Hf|exact Hx|].
      intro y. apply lookup_update_equiv. apply lookup_update_equiv. apply Heq.
  - eapply T_IfZero; eauto.
  - eapply T_Choice; eauto.
  - constructor.
  - constructor.
  - eapply T_If; eauto.
Qed.

Lemma context_included_update : forall Gamma Gamma' x T,
  context_included Gamma Gamma' ->
  context_included (update Gamma x T) (update Gamma' x T).
Proof.
  intros Gamma Gamma' x T H y U Hlookup. unfold update in *; simpl in *.
  destruct (Nat.eqb y x) eqn:E.
  - inversion Hlookup; subst. reflexivity.
  - eapply H; eauto.
Qed.

Lemma has_type_context_included : forall Delta Gamma t T,
  has_type Delta Gamma t T -> forall Gamma',
  context_included Gamma Gamma' -> has_type Delta Gamma' t T.
Proof.
  intros Delta Gamma t T Hty; induction Hty; intros Gamma' Hinc.
  - eapply T_Var; [eapply Hinc; eassumption|assumption].
  - eapply T_Abs; [assumption|]. intros x Hx.
    eapply H1; [exact Hx|]. apply context_included_update. exact Hinc.
  - eapply T_App; eauto.
  - eapply T_TAbs. intros X HX. eapply H0; eauto.
  - eapply T_TApp; eauto.
  - constructor.
  - eapply T_Div; eauto.
  - eapply T_Arith; eauto.
  - eapply T_Fix; try assumption.
    + intros x Hx. eapply H2; [exact Hx|]. apply context_included_update. exact Hinc.
    + intros f x Hf Hx. eapply H4; [exact Hf|exact Hx|].
      apply context_included_update. apply context_included_update. exact Hinc.
  - eapply T_IfZero; eauto.
  - eapply T_Choice; eauto.
  - constructor.
  - constructor.
  - eapply T_If; eauto.
Qed.

Lemma wf_ty_locally_closed : forall Delta T,
  wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T Hwf; induction Hwf; simpl.
  - constructor.
  - constructor; assumption.
  - constructor. eapply lc_ty_at_open_inv with (X := fresh L).
    apply H0. apply fresh_notin.
  - constructor.
  - constructor.
Qed.

Lemma has_type_locally_closed : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T Hty; induction Hty; simpl.
  - constructor.
  - apply lc_tm_abs.
    + eapply wf_ty_locally_closed; eauto.
    + eapply lc_tm_at_open_tm_inv with (x := fresh L).
      apply H1. apply fresh_notin.
  - apply lc_tm_app; assumption.
  - apply lc_tm_tabs. eapply lc_tm_at_open_ty_inv with (X := fresh L).
    apply H0. apply fresh_notin.
  - apply lc_tm_tapp; [assumption|eapply wf_ty_locally_closed; eauto].
  - constructor.
  - apply lc_tm_div; assumption.
  - apply lc_tm_arith; assumption.
  - apply lc_tm_fix.
    + eapply wf_ty_locally_closed; eauto.
    + eapply wf_ty_locally_closed; eauto.
    + eapply lc_tm_at_open_tm_inv with (x := fresh L).
      apply H2. apply fresh_notin.
    + pose (f := fresh L). pose (x := fresh (f :: L)).
      assert (Hf : ~ In f L) by (unfold f; apply fresh_notin).
      assert (Hx : ~ In x (f :: L)) by (unfold x; apply fresh_notin).
      specialize (H4 f x Hf Hx). unfold open_fix_body, open_tm in H4.
      eapply lc_tm_at_open_tm_inv with (x := x) in H4.
      eapply lc_tm_at_open_tm_inv with (k := 1) (x := f) in H4.
      exact H4.
  - apply lc_tm_ifzero; assumption.
  - apply lc_tm_choice; assumption.
  - constructor.
  - constructor.
  - apply lc_tm_if; assumption.
Qed.

Lemma canonical_int : forall Delta Gamma v,
  has_type Delta Gamma v Ty_Int -> value v -> exists n, v = tm_int n.
Proof. intros Delta Gamma v Hty Hv; inversion Hv; subst; inversion Hty; subst; eauto. Qed.

Lemma canonical_bool : forall Delta Gamma v,
  has_type Delta Gamma v Ty_Bool -> value v -> v = tm_true \/ v = tm_false.
Proof. intros Delta Gamma v Hty Hv; inversion Hv; subst; inversion Hty; subst; eauto. Qed.

Lemma canonical_arrow : forall Delta Gamma v A B,
  has_type Delta Gamma v (Ty_Arrow A B) -> value v ->
  (exists T body, v = tm_abs T body) \/
  (exists metric body, v = tm_fix A B metric body).
Proof. intros Delta Gamma v A B Hty Hv; inversion Hv; subst; inversion Hty; subst; eauto. Qed.

Lemma canonical_all : forall Delta Gamma v T,
  has_type Delta Gamma v (Ty_All T) -> value v -> exists body, v = tm_tabs body.
Proof. intros Delta Gamma v T Hty Hv; inversion Hv; subst; inversion Hty; subst; eauto. Qed.

Inductive blocked_div0 : tm -> Prop :=
  | BD_Div : forall n, blocked_div0 (tm_div (tm_int n) (tm_int 0%Z))
  | BD_App1 : forall t t2, blocked_div0 t -> blocked_div0 (tm_app t t2)
  | BD_App2 : forall v t2, value v -> blocked_div0 t2 -> blocked_div0 (tm_app v t2)
  | BD_TApp : forall t T, blocked_div0 t -> blocked_div0 (tm_tapp t T)
  | BD_Div1 : forall t t2, blocked_div0 t -> blocked_div0 (tm_div t t2)
  | BD_Div2 : forall v t2, value v -> blocked_div0 t2 -> blocked_div0 (tm_div v t2)
  | BD_Arith1 : forall op t t2, blocked_div0 t -> blocked_div0 (tm_arith op t t2)
  | BD_Arith2 : forall op v t2, value v -> blocked_div0 t2 -> blocked_div0 (tm_arith op v t2)
  | BD_IfZero : forall t t0 t1, blocked_div0 t -> blocked_div0 (tm_ifzero t t0 t1)
  | BD_If : forall t t2 t3, blocked_div0 t -> blocked_div0 (tm_if t t2 t3).

Lemma blocked_div0_not_value : forall t,
  blocked_div0 t -> ~ value t.
Proof. intros t Hblocked Hv; inversion Hblocked; inversion Hv; subst; try discriminate. Qed.

Theorem core_progress_or_blocked : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  (forall x, lookup_context x Gamma = None) ->
  value t \/ (exists t', t --> t') \/ blocked_div0 t.
Proof.
  intros Delta Gamma t T Hty; induction Hty; intros Hempty; simpl in *.
  - specialize (Hempty x). rewrite H in Hempty. discriminate.
  - left. apply v_abs. apply lc_tm_abs.
    + eapply wf_ty_locally_closed; eauto.
    + eapply lc_tm_at_open_tm_inv with (x := fresh L).
      eapply has_type_locally_closed. exact (H0 (fresh L) (fresh_notin L)).
  - destruct (IHHty1 Hempty) as [Hv1|[[t1' Hs1]|Hb1]].
    + destruct (IHHty2 Hempty) as [Hv2|[[t2' Hs2]|Hb2]].
      * destruct (canonical_arrow _ _ _ _ _ Hty1 Hv1)
          as [[A0 [body Heq]]|[metric [body Heq]]].
        { subst. right; left. eexists. eapply ST_AppAbs;
          [eapply has_type_locally_closed; exact Hty1|exact Hv2]. }
        { subst. right; left. eexists. eapply ST_AppFix;
          [eapply has_type_locally_closed; exact Hty1|exact Hv2]. }
      * right; left. eexists. eapply ST_App2; eauto.
      * right; right. eapply BD_App2; eauto.
    + right; left. eexists. eapply ST_App1; eauto using has_type_locally_closed.
    + right; right. eapply BD_App1; eauto.
  - left. apply v_tabs. apply lc_tm_tabs.
    eapply lc_tm_at_open_ty_inv with (X := fresh L).
    eapply has_type_locally_closed. exact (H (fresh L) (fresh_notin L)).
  - destruct (IHHty Hempty) as [Hv|[[t' Hs]|Hb]].
    + destruct (canonical_all _ _ _ _ Hty Hv) as [body ->]. right; left. eexists.
      eapply ST_TAppTabs; [eapply has_type_locally_closed; exact Hty|eapply wf_ty_locally_closed; eauto].
    + right; left. eexists. eapply ST_TApp; [exact Hs|eapply wf_ty_locally_closed; eauto].
    + right; right. eapply BD_TApp; eauto.
  - left. constructor.
  - destruct (IHHty1 Hempty) as [Hv1|[[t1' Hs1]|Hb1]].
    + destruct (IHHty2 Hempty) as [Hv2|[[t2' Hs2]|Hb2]].
      * destruct (canonical_int _ _ _ Hty1 Hv1) as [n ->].
        destruct (canonical_int _ _ _ Hty2 Hv2) as [m ->].
        destruct (Z.eq_dec m 0) as [Hzero|Hnonzero].
        -- subst m. right; right. constructor.
        -- right; left. eexists. eapply ST_DivInt. exact Hnonzero.
      * right; left. eexists. eapply ST_Div2; eauto.
      * right; right. eapply BD_Div2; eauto.
    + right; left. eexists. eapply ST_Div1; eauto using has_type_locally_closed.
    + right; right. eapply BD_Div1; eauto.
  - destruct (IHHty1 Hempty) as [Hv1|[[t1' Hs1]|Hb1]].
    + destruct (IHHty2 Hempty) as [Hv2|[[t2' Hs2]|Hb2]].
      * destruct (canonical_int _ _ _ Hty1 Hv1) as [n ->].
        destruct (canonical_int _ _ _ Hty2 Hv2) as [m ->].
        right; left. eexists. apply ST_ArithInt.
      * right; left. eexists. eapply ST_Arith2; eauto.
      * right; right. eapply BD_Arith2; eauto.
    + right; left. eexists. eapply ST_Arith1; eauto using has_type_locally_closed.
    + right; right. eapply BD_Arith1; eauto.
  - left. apply v_fix. apply lc_tm_fix.
    + eapply wf_ty_locally_closed; eauto.
    + eapply wf_ty_locally_closed; eauto.
    + eapply lc_tm_at_open_tm_inv with (x := fresh L).
      eapply has_type_locally_closed. exact (H1 (fresh L) (fresh_notin L)).
    + pose (f := fresh L). pose (x := fresh (f :: L)).
      assert (Hf : ~ In f L) by (unfold f; apply fresh_notin).
      assert (Hx : ~ In x (f :: L)) by (unfold x; apply fresh_notin).
      pose proof (has_type_locally_closed _ _ _ _ (H3 f x Hf Hx)) as Hlc.
      unfold open_fix_body, open_tm in Hlc.
      eapply lc_tm_at_open_tm_inv with (x := x) in Hlc.
      eapply lc_tm_at_open_tm_inv with (k := 1) (x := f) in Hlc.
      exact Hlc.
  - destruct (IHHty1 Hempty) as [Hv|[[t' Hs]|Hb]].
    + destruct (canonical_int _ _ _ Hty1 Hv) as [n ->]. destruct (Z.eq_dec n 0).
      * subst. right; left. eexists. eapply ST_IfZero; eauto using has_type_locally_closed.
      * right; left. eexists. eapply ST_IfNonzero; eauto using has_type_locally_closed.
    + right; left. eexists. eapply ST_IfZeroArg; eauto using has_type_locally_closed.
    + right; right. eapply BD_IfZero; eauto.
  - right; left. eexists. eapply ST_ChoiceLeft; eauto using has_type_locally_closed.
  - left. constructor.
  - left. constructor.
  - destruct (IHHty1 Hempty) as [Hv|[[t' Hs]|Hb]].
    + destruct (canonical_bool _ _ _ Hty1 Hv) as [Heq|Heq]; subst.
      * right; left. eexists. eapply ST_IfTrue; eauto using has_type_locally_closed.
      * right; left. eexists. eapply ST_IfFalse; eauto using has_type_locally_closed.
    + right; left. eexists. eapply ST_If; eauto using has_type_locally_closed.
    + right; right. eapply BD_If; eauto.
Qed.

Lemma rtype_erases : forall Delta RGamma t R,
  has_rtype Delta RGamma t R -> has_type Delta (erase_context RGamma) t (erase R).
Proof.
  intros Delta RGamma t R Hrt; induction Hrt; simpl in *.
  - eapply T_Var.
    + eapply lookup_erased_rcontext; eauto.
    + eapply wf_rty_erases; eauto.
  - eapply T_Abs.
    + eapply wf_rty_erases; eauto.
    + intros x Hx. specialize (H1 x Hx).
      rewrite erase_open_rty_tm in H1. exact H1.
  - eapply T_App; eauto.
  - eapply T_TAbs. intros X HX. specialize (H0 X HX).
    rewrite erase_open_rty_ty in H0. exact H0.
  - rewrite erase_open_rty_ty. eapply T_TApp; eauto.
  - constructor.
  - eapply T_Div; eauto.
  - eapply T_Arith; eauto.
  - eapply T_Choice; eauto.
  - constructor.
  - constructor.
  - eapply T_If; eauto.
  - eauto.
  - eapply T_Fix.
    + pose proof (wf_rty_erases _ _ _ H) as Hwf. inversion Hwf; assumption.
    + pose proof (wf_rty_erases _ _ _ H) as Hwf. inversion Hwf; assumption.
    + intros x Hx. specialize (H0 x Hx). exact H0.
    + intros f x Hf Hx. specialize (H2 f x Hf Hx).
      rewrite erase_open_rty_tm in H2. exact H2.
  - eapply T_IfZero.
    + eapply T_Var.
      * exact (lookup_erased_rcontext x RGamma (R_Refine Ty_Int p) H).
      * constructor.
    + eapply has_type_context_equiv; [exact IHHrt1|].
      intro y. unfold update. simpl. destruct (Nat.eqb y x) eqn:E.
      * apply Nat.eqb_eq in E; subst y. symmetry. exact (lookup_erased_rcontext x RGamma _ H).
      * reflexivity.
    + eapply has_type_context_equiv; [exact IHHrt2|].
      intro y. unfold update. simpl. destruct (Nat.eqb y x) eqn:E.
      * apply Nat.eqb_eq in E; subst y. symmetry. exact (lookup_erased_rcontext x RGamma _ H).
      * reflexivity.
  - rewrite <- (subtype_erases _ _ _ _ H0). exact IHHrt.
Qed.

Lemma refinement_progress_or_blocked : forall t R,
  has_rtype [] empty_rcontext t R ->
  value t \/ (exists t', t --> t') \/ blocked_div0 t.
Proof.
  intros t R Hrt. eapply core_progress_or_blocked.
  - eapply rtype_erases; eauto.
  - intros x. reflexivity.
Qed.


(* The semantic interpretation records both safety of all reducts and the
   refinement facts needed by eliminators (notably division). *)
Definition safe_computation (t : tm) : Prop :=
  forall t', multi t t' -> value t' \/ exists u, t' --> u.

Lemma rty_size_open_tm_rec : forall k R u,
  rty_size (open_rty_tm_rec k u R) = rty_size R.
Proof.
  intros k R; revert k; induction R; intros k u; simpl;
    try rewrite IHR1; try rewrite IHR2; try rewrite IHR; reflexivity.
Qed.
Lemma rty_size_open_tm : forall R u,
  rty_size (open_rty_tm R u) = rty_size R.
Proof. intros; apply rty_size_open_tm_rec. Qed.

Fixpoint related_value_fuel (fuel : nat) (R : rty) (v : tm) {struct fuel} : Prop :=
  match fuel with
  | 0 => True
  | S n =>
      match R with
      | R_Refine T p => has_type [] [] v T /\ value v /\
          qualifier_holds (open_qualifier_tm p v)
      | R_Func A B => has_type [] [] v (Ty_Arrow (erase A) (erase B)) /\ value v /\
          forall w, related_value_fuel n A w ->
            related_computation_fuel n (open_rty_tm B w) (tm_app v w)
      | R_Exists A B => has_type [] [] v (erase B) /\ value v /\
          exists w, related_value_fuel n A w /\
                    related_value_fuel n (open_rty_tm B w) v
      | R_Poly B => has_type [] [] v (Ty_All (erase B)) /\ value v /\
          forall U, wf_ty [] U ->
            related_computation_fuel n (open_rty_ty B U) (tm_tapp v U)
      end
  end
with related_computation_fuel (fuel : nat) (R : rty) (t : tm) {struct fuel} : Prop :=
  match fuel with
  | 0 => safe_computation t
  | S n => safe_computation t /\
      forall v, multi t v -> value v -> related_value_fuel n R v
  end.

Definition related_value (R : rty) (v : tm) : Prop :=
  forall fuel, related_value_fuel fuel R v.

Definition related_computation (R : rty) (t : tm) : Prop :=
  forall fuel, related_computation_fuel fuel R t.

Definition related_context
    (theta : type_substitution) (RGamma : rcontext)
    (gamma : term_substitution) : Prop :=
  forall x R, lookup_rcontext x RGamma = Some R ->
    related_value (instantiate_rty theta gamma R) (gamma x).

Definition logical_context
    (theta : type_substitution) (gamma : term_substitution)
    (RGamma : rcontext) : Prop :=
  (forall x, value (gamma x)) /\
  context_formulas_hold theta gamma RGamma /\
  related_context theta RGamma gamma.

Lemma instantiate_ty_closed : forall theta T,
  fv_ty T = [] -> instantiate_ty theta T = T.
Proof.
  intros theta T; induction T; simpl; intros H; try reflexivity.
  - discriminate.
  - apply app_eq_nil in H as [H1 H2]. rewrite (IHT1 H1), (IHT2 H2). reflexivity.
  - f_equal. apply IHT. exact H.
Qed.

Lemma instantiate_closed_tm : forall theta gamma t,
  fv_tm t = [] -> ftv_tm t = [] -> instantiate theta gamma t = t.
Proof.
  intros theta gamma t; induction t; simpl; intros Hfv Hftv; try reflexivity.
  - discriminate.
  - apply app_eq_nil in Hftv as [Hty Hbody].
    f_equal; [apply instantiate_ty_closed; exact Hty|apply IHt; simpl in *; auto].
  - apply app_eq_nil in Hfv as [H1 H2].
    apply app_eq_nil in Hftv as [H3 H4].
    rewrite (IHt1 H1 H3), (IHt2 H2 H4). reflexivity.
  - f_equal. apply IHt; assumption.
  - apply app_eq_nil in Hftv as [H1 H2].
    rewrite (IHt Hfv H1), (instantiate_ty_closed theta t0 H2). reflexivity.
  - apply app_eq_nil in Hfv as [H1 H2].
    apply app_eq_nil in Hftv as [H3 H4].
    rewrite (IHt1 H1 H3), (IHt2 H2 H4). reflexivity.
  - apply app_eq_nil in Hfv as [H1 H2].
    apply app_eq_nil in Hftv as [H3 H4].
    rewrite (IHt1 H1 H3), (IHt2 H2 H4). reflexivity.
  - apply app_eq_nil in Hfv as [H1 H2].
    apply app_eq_nil in Hftv as [HA Hrest].
    apply app_eq_nil in Hrest as [HB Hrest].
    apply app_eq_nil in Hrest as [HM HBdy].
    rewrite (instantiate_ty_closed theta t1 HA), (instantiate_ty_closed theta t2 HB),
      (IHt1 H1 HM), (IHt2 H2 HBdy). reflexivity.
  - apply app_eq_nil in Hfv as [H1 Hrest].
    apply app_eq_nil in Hrest as [H2 H3].
    apply app_eq_nil in Hftv as [H4 Hrest].
    apply app_eq_nil in Hrest as [H5 H6].
    rewrite (IHt1 H1 H4), (IHt2 H2 H5), (IHt3 H3 H6). reflexivity.
  - apply app_eq_nil in Hfv as [H1 H2].
    apply app_eq_nil in Hftv as [H3 H4].
    rewrite (IHt1 H1 H3), (IHt2 H2 H4). reflexivity.
  - apply app_eq_nil in Hfv as [H1 H2].
    apply app_eq_nil in H2 as [H2 H5].
    apply app_eq_nil in Hftv as [H3 H4].
    apply app_eq_nil in H4 as [H4 H6].
    rewrite (IHt1 H1 H3), (IHt2 H2 H4), (IHt3 H5 H6). reflexivity.
Qed.

Lemma instantiate_open_tm_rec : forall k theta gamma u t,
  term_substitution_closed gamma ->
  instantiate theta gamma (open_tm_rec k u t) =
  open_tm_rec k (instantiate theta gamma u) (instantiate theta gamma t).
Proof.
  intros k theta gamma u t Hgamma; revert k theta gamma u Hgamma.
  induction t; intros k theta gamma u Hgamma; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. eapply open_tm_rec_lc_at with (K := 0).
    + eapply lc_tm_at_monotone with (K' := 0) (k' := k).
      * apply Hgamma.
      * lia.
      * lia.
  - simpl. f_equal. apply IHt. exact Hgamma.
  - simpl. f_equal; [apply IHt1|apply IHt2]; exact Hgamma.
  - simpl. f_equal. apply IHt. exact Hgamma.
  - simpl. f_equal. apply IHt. exact Hgamma.
  - reflexivity.
  - simpl. f_equal; [apply IHt1|apply IHt2]; exact Hgamma.
  - simpl. f_equal; [apply IHt1|apply IHt2]; exact Hgamma.
  - simpl. f_equal; try reflexivity.
    + apply IHt1. exact Hgamma.
    + apply IHt2. exact Hgamma.
  - simpl. f_equal; [apply IHt1|apply IHt2|apply IHt3]; exact Hgamma.
  - simpl. f_equal; [apply IHt1|apply IHt2]; exact Hgamma.
  - reflexivity.
  - reflexivity.
  - simpl. f_equal; [apply IHt1|apply IHt2|apply IHt3]; exact Hgamma.
Qed.

Lemma instantiate_open_tm : forall theta gamma t u,
  term_substitution_closed gamma ->
  instantiate theta gamma (open_tm t u) =
  open_tm (instantiate theta gamma t) (instantiate theta gamma u).
Proof. intros; apply instantiate_open_tm_rec; assumption. Qed.

Lemma instantiate_ty_open_ty_rec : forall k theta U T,
  type_substitution_closed theta ->
  instantiate_ty theta (open_ty_rec k U T) =
  open_ty_rec k (instantiate_ty theta U) (instantiate_ty theta T).
Proof.
  intros k theta U T Htheta; revert k theta U Htheta.
  induction T as [n|X|T1 IH1 T2 IH2|T IH| |];
    intros k theta U Htheta.
  - simpl. destruct (Nat.eqb k n); reflexivity.
  - simpl. symmetry. eapply open_ty_rec_lc_at with (k := k).
    + eapply lc_ty_at_monotone with (k' := k).
      * apply Htheta.
      * lia.
  - simpl. rewrite (IH1 k theta U Htheta), (IH2 k theta U Htheta). reflexivity.
  - simpl. rewrite (IH (S k) theta U Htheta). reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma instantiate_tm_open_ty_rec : forall k theta gamma U t,
  term_substitution_closed gamma ->
  type_substitution_closed theta ->
  instantiate theta gamma (open_tm_ty_rec k U t) =
  open_tm_ty_rec k (instantiate_ty theta U) (instantiate theta gamma t).
Proof.
  intros k theta gamma U t Hgamma Htheta; revert k theta gamma U Hgamma Htheta.
  induction t; intros k theta gamma U Hgamma Htheta; simpl.
  - reflexivity.
  - symmetry. eapply open_tm_ty_rec_lc_at with (K := k).
    + eapply lc_tm_at_monotone with (K' := k) (k' := 0).
      * apply Hgamma.
      * lia.
      * lia.
  - simpl. f_equal.
    + apply instantiate_ty_open_ty_rec. exact Htheta.
    + apply IHt; assumption.
  - simpl. f_equal; [apply IHt1|apply IHt2]; [exact Hgamma|exact Htheta|exact Hgamma|exact Htheta].
  - simpl. f_equal. apply IHt; assumption.
  - simpl. f_equal.
    + apply IHt; assumption.
    + apply instantiate_ty_open_ty_rec. exact Htheta.
  - reflexivity.
  - simpl. f_equal; [apply IHt1|apply IHt2]; [exact Hgamma|exact Htheta|exact Hgamma|exact Htheta].
  - simpl. f_equal; [apply IHt1|apply IHt2]; [exact Hgamma|exact Htheta|exact Hgamma|exact Htheta].
  - simpl. f_equal; try (apply instantiate_ty_open_ty_rec; exact Htheta).
    + apply IHt1; assumption.
    + apply IHt2; assumption.
  - simpl. f_equal; [apply IHt1|apply IHt2|apply IHt3];
      [exact Hgamma|exact Htheta|exact Hgamma|exact Htheta|exact Hgamma|exact Htheta].
  - simpl. f_equal; [apply IHt1|apply IHt2];
      [exact Hgamma|exact Htheta|exact Hgamma|exact Htheta].
  - reflexivity.
  - reflexivity.
  - simpl. f_equal; [apply IHt1|apply IHt2|apply IHt3];
      [exact Hgamma|exact Htheta|exact Hgamma|exact Htheta|exact Hgamma|exact Htheta].
Qed.

Lemma notin_append_left : forall (A : Type) (x : A) l r,
  ~ In x (l ++ r) -> ~ In x l.
Proof. intros A x l r H Hin; apply H; apply in_or_app; auto. Qed.

Lemma notin_append_right : forall (A : Type) (x : A) l r,
  ~ In x (l ++ r) -> ~ In x r.
Proof. intros A x l r H Hin; apply H; apply in_or_app; auto. Qed.

Lemma instantiate_update_fresh : forall theta gamma x u t,
  ~ In x (fv_tm t) ->
  instantiate theta (term_subst_update gamma x u) t = instantiate theta gamma t.
Proof.
  intros theta gamma x u t; induction t; simpl; intros Hfresh.
  - reflexivity.
  - assert (Hneq : x <> a).
    { intro Heq. subst x. apply Hfresh. simpl. auto. }
    unfold term_subst_update. rewrite (proj2 (Nat.eqb_neq x a) Hneq). reflexivity.
  - f_equal. apply IHt. exact Hfresh.
  - assert (H1 : ~ In x (fv_tm t1)) by
        (intro Hin; apply Hfresh; simpl; apply in_or_app; left; exact Hin).
    assert (H2 : ~ In x (fv_tm t2)) by
        (intro Hin; apply Hfresh; simpl; apply in_or_app; right; exact Hin).
    f_equal; [apply IHt1|apply IHt2]; assumption.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal. apply IHt. exact Hfresh.
  - reflexivity.
  - assert (H1 : ~ In x (fv_tm t1)) by
        (intro Hin; apply Hfresh; simpl; apply in_or_app; left; exact Hin).
    assert (H2 : ~ In x (fv_tm t2)) by
        (intro Hin; apply Hfresh; simpl; apply in_or_app; right; exact Hin).
    f_equal; [apply IHt1|apply IHt2]; assumption.
  - assert (H1 : ~ In x (fv_tm t1)) by
        (intro Hin; apply Hfresh; simpl; apply in_or_app; left; exact Hin).
    assert (H2 : ~ In x (fv_tm t2)) by
        (intro Hin; apply Hfresh; simpl; apply in_or_app; right; exact Hin).
    f_equal; [apply IHt1|apply IHt2]; assumption.
  - assert (H1 : ~ In x (fv_tm t3)) by
        (intro Hin; apply Hfresh; simpl; apply in_or_app; left; exact Hin).
    assert (H2 : ~ In x (fv_tm t4)) by
        (intro Hin; apply Hfresh; simpl; apply in_or_app; right; exact Hin).
    f_equal; [apply IHt1|apply IHt2]; assumption.
  - assert (H1 : ~ In x (fv_tm t1)) by
        (apply notin_append_left with (r := fv_tm t2 ++ fv_tm t3); exact Hfresh).
    assert (Hrest : ~ In x (fv_tm t2 ++ fv_tm t3)) by
        (apply notin_append_right with (l := fv_tm t1); exact Hfresh).
    assert (H2 : ~ In x (fv_tm t2)) by
        (apply notin_append_left with (r := fv_tm t3); exact Hrest).
    assert (H3 : ~ In x (fv_tm t3)) by
        (apply notin_append_right with (l := fv_tm t2); exact Hrest).
    f_equal; [apply IHt1|apply IHt2|apply IHt3]; assumption.
  - assert (H1 : ~ In x (fv_tm t1)) by
        (intro Hin; apply Hfresh; simpl; apply in_or_app; left; exact Hin).
    assert (H2 : ~ In x (fv_tm t2)) by
        (intro Hin; apply Hfresh; simpl; apply in_or_app; right; exact Hin).
    f_equal; [apply IHt1|apply IHt2]; assumption.
  - reflexivity.
  - reflexivity.
  - assert (H1 : ~ In x (fv_tm t1)) by
        (apply notin_append_left with (r := fv_tm t2 ++ fv_tm t3); exact Hfresh).
    assert (Hrest : ~ In x (fv_tm t2 ++ fv_tm t3)) by
        (apply notin_append_right with (l := fv_tm t1); exact Hfresh).
    assert (H2 : ~ In x (fv_tm t2)) by
        (apply notin_append_left with (r := fv_tm t3); exact Hrest).
    assert (H3 : ~ In x (fv_tm t3)) by
        (apply notin_append_right with (l := fv_tm t2); exact Hrest).
    f_equal; [apply IHt1|apply IHt2|apply IHt3]; assumption.
Qed.

Lemma instantiate_ty_update_fresh : forall theta X U T,
  ~ In X (fv_ty T) ->
  instantiate_ty (type_subst_update theta X U) T = instantiate_ty theta T.
Proof.
  intros theta X U T; induction T as [n|Y|T1 IH1 T2 IH2|T IH| |];
    simpl; intros Hfresh; try reflexivity.
  - assert (Hneq : X <> Y).
    { intro Heq; subst Y; apply Hfresh; simpl; auto. }
    unfold type_subst_update. rewrite (proj2 (Nat.eqb_neq X Y) Hneq). reflexivity.
  - assert (H1 : ~ In X (fv_ty T1)) by
        (apply notin_append_left with (r := fv_ty T2); exact Hfresh).
    assert (H2 : ~ In X (fv_ty T2)) by
        (apply notin_append_right with (l := fv_ty T1); exact Hfresh).
    rewrite IH1, IH2; auto.
  - f_equal. apply IH. exact Hfresh.
Qed.

Lemma instantiate_term_ty_update_fresh : forall theta gamma X U t,
  ~ In X (ftv_tm t) ->
  instantiate (type_subst_update theta X U) gamma t = instantiate theta gamma t.
Proof.
  intros theta gamma X U t; induction t; simpl; intros Hfresh.
  - reflexivity.
  - reflexivity.
  - assert (H1 : ~ In X (fv_ty t)) by
        (apply notin_append_left with (r := ftv_tm t0); exact Hfresh).
    assert (H2 : ~ In X (ftv_tm t0)) by
        (apply notin_append_right with (l := fv_ty t); exact Hfresh).
    rewrite instantiate_ty_update_fresh by exact H1.
    f_equal. apply IHt. exact H2.
  - assert (H1 : ~ In X (ftv_tm t1)) by
        (apply notin_append_left with (r := ftv_tm t2); exact Hfresh).
    assert (H2 : ~ In X (ftv_tm t2)) by
        (apply notin_append_right with (l := ftv_tm t1); exact Hfresh).
    f_equal; [apply IHt1|apply IHt2]; assumption.
  - f_equal. apply IHt. exact Hfresh.
  - assert (H1 : ~ In X (ftv_tm t)) by
        (apply notin_append_left with (r := fv_ty t0); exact Hfresh).
    assert (H2 : ~ In X (fv_ty t0)) by
        (apply notin_append_right with (l := ftv_tm t); exact Hfresh).
    rewrite IHt by exact H1. f_equal. apply instantiate_ty_update_fresh. exact H2.
  - reflexivity.
  - assert (H1 : ~ In X (ftv_tm t1)) by
        (apply notin_append_left with (r := ftv_tm t2); exact Hfresh).
    assert (H2 : ~ In X (ftv_tm t2)) by
        (apply notin_append_right with (l := ftv_tm t1); exact Hfresh).
    f_equal; [apply IHt1|apply IHt2]; assumption.
  - assert (H1 : ~ In X (ftv_tm t1)) by
        (apply notin_append_left with (r := ftv_tm t2); exact Hfresh).
    assert (H2 : ~ In X (ftv_tm t2)) by
        (apply notin_append_right with (l := ftv_tm t1); exact Hfresh).
    f_equal; [apply IHt1|apply IHt2]; assumption.
  - assert (H1 : ~ In X (fv_ty t1)) by
        (apply notin_append_left with (r := fv_ty t2 ++ ftv_tm t3 ++ ftv_tm t4); exact Hfresh).
    assert (Hrest : ~ In X (fv_ty t2 ++ ftv_tm t3 ++ ftv_tm t4)) by
        (apply notin_append_right with (l := fv_ty t1); exact Hfresh).
    assert (H2 : ~ In X (fv_ty t2)) by
        (apply notin_append_left with (r := ftv_tm t3 ++ ftv_tm t4); exact Hrest).
    assert (Hrest2 : ~ In X (ftv_tm t3 ++ ftv_tm t4)) by
        (apply notin_append_right with (l := fv_ty t2); exact Hrest).
    assert (H3 : ~ In X (ftv_tm t3)) by
        (apply notin_append_left with (r := ftv_tm t4); exact Hrest2).
    assert (H4 : ~ In X (ftv_tm t4)) by
        (apply notin_append_right with (l := ftv_tm t3); exact Hrest2).
    rewrite instantiate_ty_update_fresh by exact H1.
    rewrite instantiate_ty_update_fresh by exact H2.
    f_equal; [apply IHt1|apply IHt2]; assumption.
  - assert (H1 : ~ In X (ftv_tm t1)) by
        (apply notin_append_left with (r := ftv_tm t2 ++ ftv_tm t3); exact Hfresh).
    assert (Hrest : ~ In X (ftv_tm t2 ++ ftv_tm t3)) by
        (apply notin_append_right with (l := ftv_tm t1); exact Hfresh).
    assert (H2 : ~ In X (ftv_tm t2)) by
        (apply notin_append_left with (r := ftv_tm t3); exact Hrest).
    assert (H3 : ~ In X (ftv_tm t3)) by
        (apply notin_append_right with (l := ftv_tm t2); exact Hrest).
    f_equal; [apply IHt1|apply IHt2|apply IHt3]; assumption.
  - assert (H1 : ~ In X (ftv_tm t1)) by
        (apply notin_append_left with (r := ftv_tm t2); exact Hfresh).
    assert (H2 : ~ In X (ftv_tm t2)) by
        (apply notin_append_right with (l := ftv_tm t1); exact Hfresh).
    f_equal; [apply IHt1|apply IHt2]; assumption.
  - reflexivity.
  - reflexivity.
  - assert (H1 : ~ In X (ftv_tm t1)) by
        (apply notin_append_left with (r := ftv_tm t2 ++ ftv_tm t3); exact Hfresh).
    assert (Hrest : ~ In X (ftv_tm t2 ++ ftv_tm t3)) by
        (apply notin_append_right with (l := ftv_tm t1); exact Hfresh).
    assert (H2 : ~ In X (ftv_tm t2)) by
        (apply notin_append_left with (r := ftv_tm t3); exact Hrest).
    assert (H3 : ~ In X (ftv_tm t3)) by
        (apply notin_append_right with (l := ftv_tm t2); exact Hrest).
    f_equal; [apply IHt1|apply IHt2|apply IHt3]; assumption.
Qed.

Lemma instantiate_open_update_tm : forall theta gamma x t u,
  term_substitution_closed gamma ->
  ~ In x (fv_tm t) ->
  locally_closed_tm u -> fv_tm u = [] -> ftv_tm u = [] ->
  instantiate theta gamma (open_tm t u) =
  instantiate theta (term_subst_update gamma x u)
    (open_tm t (tm_fvar x)).
Proof.
  intros theta gamma x t u Hgamma Hfresh Hluc Hfv Hftv.
  rewrite (instantiate_open_tm theta gamma t u Hgamma).
  rewrite (instantiate_closed_tm theta gamma u Hfv Hftv).
  rewrite (instantiate_open_tm theta (term_subst_update gamma x u) t
    (tm_fvar x) (term_subst_update_closed gamma x u Hgamma Hluc)).
  rewrite (instantiate_update_fresh theta gamma x u t Hfresh).
  unfold term_subst_update.
  destruct (Nat.eqb x x) eqn:E.
  - simpl [instantiate]. rewrite E. reflexivity.
  - apply Nat.eqb_neq in E. contradiction.
Qed.

Lemma instantiate_pred_update_fresh : forall theta gamma x u p,
  ~ In x (fv_pred p) ->
  instantiate_pred theta (term_subst_update gamma x u) p =
  instantiate_pred theta gamma p.
Proof.
  intros theta gamma x u p;
    induction p as [| |t1 t2|t1 t2|t1 t2|p1 IHp1 p2 IHp2|p1 IHp1 p2 IHp2|p IHp];
    simpl; intros Hfresh; try reflexivity.
  - assert (H1 : ~ In x (fv_tm t1)) by
        (apply notin_append_left with (r := fv_tm t2); exact Hfresh).
    assert (H2 : ~ In x (fv_tm t2)) by
        (apply notin_append_right with (l := fv_tm t1); exact Hfresh).
    rewrite (instantiate_update_fresh theta gamma x u t1 H1),
      (instantiate_update_fresh theta gamma x u t2 H2). reflexivity.
  - assert (H1 : ~ In x (fv_tm t1)) by
        (apply notin_append_left with (r := fv_tm t2); exact Hfresh).
    assert (H2 : ~ In x (fv_tm t2)) by
        (apply notin_append_right with (l := fv_tm t1); exact Hfresh).
    rewrite (instantiate_update_fresh theta gamma x u t1 H1),
      (instantiate_update_fresh theta gamma x u t2 H2). reflexivity.
  - assert (H1 : ~ In x (fv_tm t1)) by
        (apply notin_append_left with (r := fv_tm t2); exact Hfresh).
    assert (H2 : ~ In x (fv_tm t2)) by
        (apply notin_append_right with (l := fv_tm t1); exact Hfresh).
    rewrite (instantiate_update_fresh theta gamma x u t1 H1),
      (instantiate_update_fresh theta gamma x u t2 H2). reflexivity.
  - assert (H1 : ~ In x (fv_pred p1)) by
        (apply notin_append_left with (r := fv_pred p2); exact Hfresh).
    assert (H2 : ~ In x (fv_pred p2)) by
        (apply notin_append_right with (l := fv_pred p1); exact Hfresh).
    rewrite IHp1, IHp2; auto.
  - assert (H1 : ~ In x (fv_pred p1)) by
        (apply notin_append_left with (r := fv_pred p2); exact Hfresh).
    assert (H2 : ~ In x (fv_pred p2)) by
        (apply notin_append_right with (l := fv_pred p1); exact Hfresh).
    rewrite IHp1, IHp2; auto.
  - f_equal. apply IHp. exact Hfresh.
Qed.

Lemma instantiate_rty_update_fresh : forall theta gamma x u R,
  ~ In x (fv_rty R) ->
  instantiate_rty theta (term_subst_update gamma x u) R =
  instantiate_rty theta gamma R.
Proof.
  intros theta gamma x u R; induction R; simpl; intros Hfresh.
  - rewrite instantiate_pred_update_fresh; auto.
  - assert (H1 : ~ In x (fv_rty R1)) by
        (apply notin_append_left with (r := fv_rty R2); exact Hfresh).
    assert (H2 : ~ In x (fv_rty R2)) by
        (apply notin_append_right with (l := fv_rty R1); exact Hfresh).
    rewrite IHR1, IHR2; auto.
  - assert (H1 : ~ In x (fv_rty R1)) by
        (apply notin_append_left with (r := fv_rty R2); exact Hfresh).
    assert (H2 : ~ In x (fv_rty R2)) by
        (apply notin_append_right with (l := fv_rty R1); exact Hfresh).
    rewrite IHR1, IHR2; auto.
  - f_equal. apply IHR. exact Hfresh.
Qed.

Lemma instantiate_pred_ty_update_fresh : forall theta gamma X U p,
  ~ In X (ftv_pred p) ->
  instantiate_pred (type_subst_update theta X U) gamma p =
  instantiate_pred theta gamma p.
Proof.
  intros theta gamma X U p;
    induction p as [| |t1 t2|t1 t2|t1 t2|p1 IHp1 p2 IHp2|p1 IHp1 p2 IHp2|p IHp];
    simpl; intros Hfresh; try reflexivity.
  - assert (H1 : ~ In X (ftv_tm t1)) by
        (apply notin_append_left with (r := ftv_tm t2); exact Hfresh).
    assert (H2 : ~ In X (ftv_tm t2)) by
        (apply notin_append_right with (l := ftv_tm t1); exact Hfresh).
    rewrite (instantiate_term_ty_update_fresh theta gamma X U t1 H1),
      (instantiate_term_ty_update_fresh theta gamma X U t2 H2). reflexivity.
  - assert (H1 : ~ In X (ftv_tm t1)) by
        (apply notin_append_left with (r := ftv_tm t2); exact Hfresh).
    assert (H2 : ~ In X (ftv_tm t2)) by
        (apply notin_append_right with (l := ftv_tm t1); exact Hfresh).
    rewrite (instantiate_term_ty_update_fresh theta gamma X U t1 H1),
      (instantiate_term_ty_update_fresh theta gamma X U t2 H2). reflexivity.
  - assert (H1 : ~ In X (ftv_tm t1)) by
        (apply notin_append_left with (r := ftv_tm t2); exact Hfresh).
    assert (H2 : ~ In X (ftv_tm t2)) by
        (apply notin_append_right with (l := ftv_tm t1); exact Hfresh).
    rewrite (instantiate_term_ty_update_fresh theta gamma X U t1 H1),
      (instantiate_term_ty_update_fresh theta gamma X U t2 H2). reflexivity.
  - assert (H1 : ~ In X (ftv_pred p1)) by
        (apply notin_append_left with (r := ftv_pred p2); exact Hfresh).
    assert (H2 : ~ In X (ftv_pred p2)) by
        (apply notin_append_right with (l := ftv_pred p1); exact Hfresh).
    rewrite IHp1, IHp2; auto.
  - assert (H1 : ~ In X (ftv_pred p1)) by
        (apply notin_append_left with (r := ftv_pred p2); exact Hfresh).
    assert (H2 : ~ In X (ftv_pred p2)) by
        (apply notin_append_right with (l := ftv_pred p1); exact Hfresh).
    rewrite IHp1, IHp2; auto.
  - f_equal. apply IHp. exact Hfresh.
Qed.

Lemma instantiate_rty_ty_update_fresh : forall theta gamma X U R,
  ~ In X (ftv_rty R) ->
  instantiate_rty (type_subst_update theta X U) gamma R =
  instantiate_rty theta gamma R.
Proof.
  intros theta gamma X U R; induction R; intros Hfresh.
  - change (R_Refine (instantiate_ty (type_subst_update theta X U) t)
      (instantiate_pred (type_subst_update theta X U) gamma q) =
      R_Refine (instantiate_ty theta t) (instantiate_pred theta gamma q)).
    assert (H1 : ~ In X (fv_ty t)) by
        (apply notin_append_left with (r := ftv_qualifier q); exact Hfresh).
    assert (H2 : ~ In X (ftv_qualifier q)) by
        (apply notin_append_right with (l := fv_ty t); exact Hfresh).
    rewrite (instantiate_ty_update_fresh theta X U t H1),
      (instantiate_pred_ty_update_fresh theta gamma X U q H2). reflexivity.
  - change (R_Func (instantiate_rty (type_subst_update theta X U) gamma R1)
      (instantiate_rty (type_subst_update theta X U) gamma R2) =
      R_Func (instantiate_rty theta gamma R1) (instantiate_rty theta gamma R2)).
    assert (H1 : ~ In X (ftv_rty R1)) by
        (apply notin_append_left with (r := ftv_rty R2); exact Hfresh).
    assert (H2 : ~ In X (ftv_rty R2)) by
        (apply notin_append_right with (l := ftv_rty R1); exact Hfresh).
    rewrite IHR1, IHR2; auto.
  - change (R_Exists (instantiate_rty (type_subst_update theta X U) gamma R1)
      (instantiate_rty (type_subst_update theta X U) gamma R2) =
      R_Exists (instantiate_rty theta gamma R1) (instantiate_rty theta gamma R2)).
    assert (H1 : ~ In X (ftv_rty R1)) by
        (apply notin_append_left with (r := ftv_rty R2); exact Hfresh).
    assert (H2 : ~ In X (ftv_rty R2)) by
        (apply notin_append_right with (l := ftv_rty R1); exact Hfresh).
    rewrite IHR1, IHR2; auto.
  - change (R_Poly (instantiate_rty (type_subst_update theta X U) gamma R) =
      R_Poly (instantiate_rty theta gamma R)).
    f_equal. apply IHR. exact Hfresh.
Qed.

Lemma instantiate_pred_open_tm_rec : forall k theta gamma u p,
  term_substitution_closed gamma ->
  instantiate_pred theta gamma (open_pred_tm_rec k u p) =
  open_pred_tm_rec k (instantiate theta gamma u) (instantiate_pred theta gamma p).
Proof.
  intros k theta gamma u p Hgamma; revert k theta gamma u Hgamma.
  induction p as [| |t1 t2|t1 t2|t1 t2|p1 IHp1 p2 IHp2|p1 IHp1 p2 IHp2|p IHp];
    intros k theta gamma u Hgamma; simpl; try reflexivity.
  - rewrite (instantiate_open_tm_rec k theta gamma u t1 Hgamma),
      (instantiate_open_tm_rec k theta gamma u t2 Hgamma). reflexivity.
  - rewrite (instantiate_open_tm_rec k theta gamma u t1 Hgamma),
      (instantiate_open_tm_rec k theta gamma u t2 Hgamma). reflexivity.
  - rewrite (instantiate_open_tm_rec k theta gamma u t1 Hgamma),
      (instantiate_open_tm_rec k theta gamma u t2 Hgamma). reflexivity.
  - rewrite IHp1, IHp2; auto.
  - rewrite IHp1, IHp2; auto.
  - f_equal. apply IHp. exact Hgamma.
Qed.

Lemma instantiate_rty_open_tm_rec : forall k theta gamma u R,
  term_substitution_closed gamma ->
  instantiate_rty theta gamma (open_rty_tm_rec k u R) =
  open_rty_tm_rec k (instantiate theta gamma u) (instantiate_rty theta gamma R).
Proof.
  intros k theta gamma u R Hgamma; revert k theta gamma u Hgamma.
  induction R; intros k theta gamma u Hgamma; simpl.
  - f_equal. apply instantiate_pred_open_tm_rec. exact Hgamma.
  - f_equal; [apply IHR1|apply IHR2]; exact Hgamma.
  - f_equal; [apply IHR1|apply IHR2]; exact Hgamma.
  - f_equal. apply IHR. exact Hgamma.
Qed.

Lemma instantiate_open_update_rty : forall theta gamma x R u,
  term_substitution_closed gamma ->
  ~ In x (fv_rty R) ->
  locally_closed_tm u -> fv_tm u = [] -> ftv_tm u = [] ->
  instantiate_rty theta gamma (open_rty_tm R u) =
  instantiate_rty theta (term_subst_update gamma x u)
    (open_rty_tm R (tm_fvar x)).
Proof.
  intros theta gamma x R u Hgamma Hfresh Hluc Hfv Hftv.
  unfold open_rty_tm.
  rewrite (instantiate_rty_open_tm_rec 0 theta gamma u R Hgamma).
  rewrite (instantiate_closed_tm theta gamma u Hfv Hftv).
  rewrite (instantiate_rty_open_tm_rec 0 theta (term_subst_update gamma x u)
    (tm_fvar x) R (term_subst_update_closed gamma x u Hgamma Hluc)).
  rewrite (instantiate_rty_update_fresh theta gamma x u R Hfresh).
  unfold term_subst_update.
  cbn [instantiate_rty instantiate_pred instantiate].
  assert (E : Nat.eqb x x = true) by apply Nat.eqb_refl.
  rewrite E. reflexivity.
Qed.

Lemma related_value_computation : forall R v,
  related_value R v -> value v -> related_computation R v.
Proof.
  intros R v Hrel Hv fuel. destruct fuel as [|fuel].
  - intros v' Hmulti. rewrite (value_multi_eq _ _ Hv Hmulti). left; exact Hv.
  - split.
    + intros v' Hmulti. rewrite (value_multi_eq _ _ Hv Hmulti). left; exact Hv.
    + intros v' Hmulti Hv'.
      assert (Heq : v' = v) by (eapply value_multi_eq; eauto).
      subst v'. apply Hrel.
Qed.

Lemma entails_sound_under_context : forall Delta RGamma p q,
  entails Delta RGamma p q -> forall theta gamma,
  (forall x, value (gamma x)) ->
  context_formulas_hold theta gamma RGamma ->
  qualifier_holds (instantiate_formula theta gamma p) ->
  qualifier_holds (instantiate_formula theta gamma q).
Proof.
  intros Delta RGamma p q Hent; induction Hent;
    intros theta gamma Hvalues Hctx Hp; simpl in *; try assumption; try exact I.
  - apply IHHent2 with (theta := theta) (gamma := gamma); auto.
  - destruct Hp as [Hp1 Hp2]; exact Hp1.
  - destruct Hp as [Hp1 Hp2]; exact Hp2.
  - split; [eapply IHHent1|eapply IHHent2]; eauto.
  - left; exact Hp.
  - right; exact Hp.
  - destruct Hp as [Hp|Hq].
    + eapply IHHent1; eauto.
    + eapply IHHent2; eauto.
  - intro Hq. apply (IHHent theta gamma Hvalues Hctx).
    split; assumption.
  - destruct Hp as [Hp Hnot]; apply Hnot; exact Hp.
  - eapply Hctx; eauto.
  - contradiction.
  - eapply H; eauto.
Qed.

Lemma safe_computation_reduct : forall t t',
  safe_computation t -> multi t t' -> safe_computation t'.
Proof.
  intros t t' Hsafe Hmulti u Hreach.
  eapply Hsafe. eapply multi_trans; eauto.
Qed.

Lemma related_computation_reduct : forall R t t',
  related_computation R t -> multi t t' -> related_computation R t'.
Proof.
  intros R t t' Hrel Hmulti fuel.
  destruct fuel as [|fuel].
  - eapply safe_computation_reduct; [exact (Hrel 0)|exact Hmulti].
  - split.
    + eapply safe_computation_reduct; [exact (proj1 (Hrel (S fuel)))|exact Hmulti].
    + intros v Hreach Hv. specialize (Hrel (S fuel)).
      destruct Hrel as [_ Hfinal].
      eapply Hfinal; [eapply multi_trans; eauto|exact Hv].
Qed.

Lemma related_computation_never_stuck : forall R t t',
  related_computation R t -> multi t t' ->
  value t' \/ exists u, t' --> u.
Proof.
  intros R t t' Hrel Hmulti. specialize (Hrel 0).
  eapply Hrel. exact Hmulti.
Qed.

Lemma related_computation_final : forall R t v,
  related_computation R t -> multi t v -> value v -> related_value R v.
Proof.
  intros R t v Hrel Hmulti Hv fuel.
  specialize (Hrel (S fuel)). destruct Hrel as [_ Hfinal].
  eapply Hfinal; eassumption.
Qed.


Lemma related_integer : forall n : Z,
  related_computation
    (R_Refine Ty_Int (Pred_Eq (tm_bvar 0) (tm_int n))) (tm_int n).
Proof.
  intros n fuel. destruct fuel as [|fuel].
  - intros t' Hmulti. pose proof (value_multi_eq _ _ (v_int n) Hmulti).
    subst; left; constructor.
  - split.
    + intros t' Hmulti. pose proof (value_multi_eq _ _ (v_int n) Hmulti).
      subst; left; constructor.
    + intros v Hmulti Hv. pose proof (value_multi_eq _ _ (v_int n) Hmulti).
      subst v. destruct fuel; simpl.
      * exact I.
      * split.
        -- eapply T_Int.
        -- split; [constructor|]. simpl. exists (tm_int n). split.
           ++ constructor.
           ++ split; [constructor|constructor].
Qed.

Lemma related_boolean_true :
  related_computation (R_Refine Ty_Bool Pred_True) tm_true.
Proof.
  intros fuel. destruct fuel as [|fuel].
  - intros t' Hmulti. pose proof (value_multi_eq _ _ v_true Hmulti).
    subst; left; constructor.
  - split.
    + intros t' Hmulti. pose proof (value_multi_eq _ _ v_true Hmulti).
      subst; left; constructor.
    + intros v Hmulti Hv. pose proof (value_multi_eq _ _ v_true Hmulti).
      subst v. destruct fuel; simpl.
      * exact I.
      * split; [eapply T_True|]. split; [constructor|exact I].
Qed.

Lemma related_boolean_false :
  related_computation (R_Refine Ty_Bool Pred_True) tm_false.
Proof.
  intros fuel. destruct fuel as [|fuel].
  - intros t' Hmulti. pose proof (value_multi_eq _ _ v_false Hmulti).
    subst; left; constructor.
  - split.
    + intros t' Hmulti. pose proof (value_multi_eq _ _ v_false Hmulti).
      subst; left; constructor.
    + intros v Hmulti Hv. pose proof (value_multi_eq _ _ v_false Hmulti).
      subst v. destruct fuel; simpl.
      * exact I.
      * split; [eapply T_False|]. split; [constructor|exact I].
Qed.

Lemma zero_not_nonzero :
  ~ qualifier_holds (Pred_Ne (tm_int 0%Z) (tm_int 0%Z)).
Proof.
  unfold qualifier_holds, predicate_holds, Pred_Ne, interpret_qualifier,
    operational_atoms. simpl. intro H. apply H.
  exists (tm_int 0%Z). repeat split; constructor.
Qed.

Lemma related_zero_cannot_be_nonzero :
  related_value (R_Refine Ty_Int (Pred_Ne (tm_bvar 0) (tm_int 0%Z))) (tm_int 0%Z) -> False.
Proof.
  intros Hrel. specialize (Hrel 1). simpl in Hrel.
  destruct Hrel as [_ [_ Hholds]].
  apply zero_not_nonzero. simpl in Hholds. exact Hholds.
Qed.

Lemma related_computation_nonzero_excludes_zero : forall t,
  related_computation
    (R_Refine Ty_Int (Pred_Ne (tm_bvar 0) (tm_int 0%Z))) t ->
  multi t (tm_int 0%Z) -> False.
Proof.
  intros t Hrel Hmulti. specialize (Hrel 2). simpl in Hrel.
  destruct Hrel as [_ Hfinal].
  specialize (Hfinal (tm_int 0%Z) Hmulti (v_int 0%Z)).
  simpl in Hfinal. destruct Hfinal as [_ [_ Hholds]].
  eapply zero_not_nonzero. simpl in Hholds. exact Hholds.
Qed.

Theorem never_stuck : forall (t t' : tm) (R : rty),
  has_rtype [] empty_rcontext t R ->
  multi t t' ->
  value t' \/ exists t'' : tm, t' --> t''.
Proof.
  (* Complete this proof. *)
Qed.

End SystemFRefinementIfNonDeterminismRecursionTask.
