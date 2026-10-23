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

Lemma wf_ty_lc : forall Delta T,
  wf_ty Delta T ->
  locally_closed_ty T.
Proof.
  intros Delta T Hwf. induction Hwf.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; assumption.
  - unfold locally_closed_ty in *.
    apply lc_ty_all.
    set (X := fresh L).
    apply (lc_ty_at_open_inv T 0 X).
    apply H0. subst X. apply fresh_notin.
  - apply lc_ty_int.
  - constructor.
Qed.

Lemma typing_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  locally_closed_tm t.
Proof.
  intros Delta Gamma t T Hty. induction Hty.
  - apply lc_tm_fvar.
  - unfold locally_closed_tm in *.
    apply lc_tm_abs.
    + apply wf_ty_lc with Delta. assumption.
    + set (x := fresh L).
      apply (lc_tm_at_open_tm_inv t2 0 0 x).
      apply H1. subst x. apply fresh_notin.
  - apply lc_tm_app; assumption.
  - unfold locally_closed_tm in *.
    apply lc_tm_tabs.
    set (X := fresh L).
    apply (lc_tm_at_open_ty_inv t 0 0 X).
    apply H0. subst X. apply fresh_notin.
  - apply lc_tm_tapp.
    + assumption.
    + apply wf_ty_lc with Delta. assumption.
  - apply lc_tm_int.
  - apply lc_tm_div; assumption.
  - apply lc_tm_arith; assumption.
  - apply lc_tm_fix.
    + eapply wf_ty_lc; eauto.
    + eapply wf_ty_lc; eauto.
    + apply (lc_tm_at_open_tm_inv metric 0 0 (fresh L)).
      apply H2. apply fresh_notin.
    + set (f := fresh L). set (x := fresh (f :: L)).
      apply (lc_tm_at_open_tm_inv body 0 1 f).
      apply (lc_tm_at_open_tm_inv (open_tm_rec 1 (tm_fvar f) body) 0 0 x).
      apply H4; [apply fresh_notin|apply fresh_notin].
  - apply lc_tm_ifzero; assumption.
  - try (inversion Hlc; subst). apply lc_tm_choice; eauto.
  - constructor.
  - constructor.
  - try (inversion Hlc; subst). apply lc_tm_if; eauto.
Qed.

Lemma typing_type_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  locally_closed_ty T.
Proof.
  intros Delta Gamma t T Hty. induction Hty.
  - apply wf_ty_lc with Delta. assumption.
  - apply lc_ty_arrow.
    + apply wf_ty_lc with Delta. assumption.
    + set (x := fresh L). apply H1 with x.
      subst x. apply fresh_notin.
  - inversion IHHty1; assumption.
  - unfold locally_closed_ty in *.
    apply lc_ty_all.
    set (X := fresh L).
    apply (lc_ty_at_open_inv T 0 X).
    apply H0. subst X. apply fresh_notin.
  - unfold locally_closed_ty in *.
    inversion IHHty; subst.
    apply lc_ty_at_open.
    + assumption.
    + apply wf_ty_lc with Delta. assumption.
  - apply lc_ty_int.
  - apply lc_ty_int.
  - apply lc_ty_int.
  - apply lc_ty_arrow; eapply wf_ty_lc; eauto.
  - assumption.
  - exact IHHty1.
  - constructor.
  - constructor.
  - exact IHHty2.
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

Lemma instantiate_ty_lc_at : forall T k theta,
  lc_ty_at k T ->
  type_substitution_closed theta ->
  lc_ty_at k (instantiate_ty theta T).
Proof.
  intros T k theta Hlc. induction Hlc; intros Htheta; simpl.
  - apply lc_ty_bvar. assumption.
  - eapply lc_ty_at_monotone.
    + apply Htheta.
    + lia.
  - apply lc_ty_arrow; auto.
  - apply lc_ty_all. auto.
  - apply lc_ty_int.
  - constructor.
Qed.

Lemma instantiate_lc_at : forall t K k theta gamma,
  lc_tm_at K k t ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  lc_tm_at K k (instantiate theta gamma t).
Proof.
  intros t K k theta gamma Hlc. induction Hlc; intros Htheta Hgamma; simpl.
  - apply lc_tm_bvar. assumption.
  - eapply lc_tm_at_monotone.
    + apply Hgamma.
    + lia.
    + lia.
  - apply lc_tm_abs.
    + apply instantiate_ty_lc_at; assumption.
    + auto.
  - apply lc_tm_app; auto.
  - apply lc_tm_tabs. auto.
  - apply lc_tm_tapp.
    + auto.
    + apply instantiate_ty_lc_at; assumption.
  - apply lc_tm_int.
  - apply lc_tm_div; auto.
  - apply lc_tm_arith; auto.
  - apply lc_tm_fix; eauto using instantiate_ty_lc_at.
  - apply lc_tm_ifzero; eauto.
  - try (inversion Hlc; subst). apply lc_tm_choice; eauto.
  - constructor.
  - constructor.
  - try (inversion Hlc; subst). apply lc_tm_if; eauto.
Qed.

Lemma instantiate_ty_closed : forall theta T,
  locally_closed_ty T ->
  type_substitution_closed theta ->
  locally_closed_ty (instantiate_ty theta T).
Proof.
  intros. apply instantiate_ty_lc_at; assumption.
Qed.

Lemma instantiate_closed : forall theta gamma t,
  locally_closed_tm t ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm (instantiate theta gamma t).
Proof.
  intros. apply instantiate_lc_at; assumption.
Qed.

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

Lemma instantiate_open_tm_rec : forall t k theta gamma x u,
  ~ In x (fv_tm t) ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  instantiate theta (term_subst_update gamma x u)
    (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k u (instantiate theta gamma t).
Proof.
  induction t; intros k theta gamma x u Hfresh Htheta Hgamma Hu; simpl in *.
  - destruct (Nat.eqb k n); simpl.
    + unfold term_subst_update. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - assert (x <> a) by (intro; subst; apply Hfresh; auto).
    unfold term_subst_update.
    assert (E : Nat.eqb x a = false) by (apply Nat.eqb_neq; assumption).
    rewrite E.
    symmetry. apply open_tm_rec_lc_at with (K := 0).
    eapply lc_tm_at_monotone.
    + apply Hgamma.
    + lia.
    + lia.
  - rewrite (IHt (S k) theta gamma x u Hfresh Htheta Hgamma Hu).
    reflexivity.
  - rewrite in_app_iff in Hfresh.
    assert (H1 : ~ In x (fv_tm t1)) by intuition.
    assert (H2 : ~ In x (fv_tm t2)) by intuition.
    rewrite (IHt1 k theta gamma x u H1 Htheta Hgamma Hu).
    rewrite (IHt2 k theta gamma x u H2 Htheta Hgamma Hu).
    reflexivity.
  - rewrite (IHt k theta gamma x u Hfresh Htheta Hgamma Hu).
    reflexivity.
  - rewrite (IHt k theta gamma x u Hfresh Htheta Hgamma Hu).
    reflexivity.
  - reflexivity.
  - rewrite in_app_iff in Hfresh.
    rewrite IHt1, IHt2; intuition.
  - rewrite in_app_iff in Hfresh. rewrite IHt1, IHt2; intuition.
  - rewrite in_app_iff in Hfresh. rewrite IHt1, IHt2; intuition.
  - repeat rewrite in_app_iff in Hfresh. rewrite IHt1, IHt2, IHt3; intuition.
  - rewrite in_app_iff in Hfresh. rewrite IHt1, IHt2; intuition.
  - reflexivity.
  - reflexivity.
  - repeat rewrite in_app_iff in Hfresh. rewrite IHt1, IHt2, IHt3; intuition.
Qed.

Lemma instantiate_open_tm : forall t theta gamma x u,
  ~ In x (fv_tm t) ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  instantiate theta (term_subst_update gamma x u)
    (open_tm t (tm_fvar x)) =
  open_tm (instantiate theta gamma t) u.
Proof.
  intros. unfold open_tm.
  apply instantiate_open_tm_rec; assumption.
Qed.

Lemma instantiate_ty_open_rec : forall T k theta X U,
  ~ In X (fv_ty T) ->
  type_substitution_closed theta ->
  locally_closed_ty U ->
  instantiate_ty (type_subst_update theta X U)
    (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k U (instantiate_ty theta T).
Proof.
  induction T; intros k theta X U Hfresh Htheta HU; simpl in *.
  - destruct (Nat.eqb k n); simpl.
    + unfold type_subst_update. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - assert (X <> a) by (intro; subst; apply Hfresh; auto).
    unfold type_subst_update.
    assert (E : Nat.eqb X a = false) by (apply Nat.eqb_neq; assumption).
    rewrite E.
    symmetry. apply open_ty_rec_lc_at.
    eapply lc_ty_at_monotone.
    + apply Htheta.
    + lia.
  - rewrite in_app_iff in Hfresh.
    assert (H1 : ~ In X (fv_ty T1)) by intuition.
    assert (H2 : ~ In X (fv_ty T2)) by intuition.
    rewrite (IHT1 k theta X U H1 Htheta HU).
    rewrite (IHT2 k theta X U H2 Htheta HU).
    reflexivity.
  - rewrite (IHT (S k) theta X U Hfresh Htheta HU). reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma instantiate_ty_open : forall T theta X U,
  ~ In X (fv_ty T) ->
  type_substitution_closed theta ->
  locally_closed_ty U ->
  instantiate_ty (type_subst_update theta X U)
    (open_ty T (Ty_FVar X)) =
  open_ty (instantiate_ty theta T) U.
Proof.
  intros. unfold open_ty.
  apply instantiate_ty_open_rec; assumption.
Qed.

Lemma instantiate_open_ty_rec : forall t K theta gamma X U,
  ~ In X (ftv_tm t) ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_ty U ->
  instantiate (type_subst_update theta X U) gamma
    (open_tm_ty_rec K (Ty_FVar X) t) =
  open_tm_ty_rec K U (instantiate theta gamma t).
Proof.
  induction t as
      [i | x | T body IHbody | t1 IH1 t2 IH2 | body IHbody | body IHbody T
      | n | t1 IH1 t2 IH2 | op t1 IH1 t2 IH2
      | A B metric IHm body IHb | t IH t0 IH0 t1 IH1 | t1 IH1 t2 IH2 | | | t1 IH1 t2 IH2 t3 IH3];
    intros K theta gamma X U Hfresh Htheta Hgamma HU; simpl in *.
  - reflexivity.
  - symmetry. apply open_tm_ty_rec_lc_at with (k := 0).
    eapply lc_tm_at_monotone.
    + apply Hgamma.
    + lia.
    + lia.
  - rewrite in_app_iff in Hfresh.
    assert (HT : ~ In X (fv_ty T)) by intuition.
    assert (Hbody : ~ In X (ftv_tm body)) by intuition.
    rewrite (instantiate_ty_open_rec T K theta X U HT Htheta HU).
    rewrite (IHbody K theta gamma X U Hbody Htheta Hgamma HU).
    reflexivity.
  - rewrite in_app_iff in Hfresh.
    assert (H1 : ~ In X (ftv_tm t1)) by intuition.
    assert (H2 : ~ In X (ftv_tm t2)) by intuition.
    rewrite (IH1 K theta gamma X U H1 Htheta Hgamma HU).
    rewrite (IH2 K theta gamma X U H2 Htheta Hgamma HU).
    reflexivity.
  - rewrite (IHbody (S K) theta gamma X U Hfresh Htheta Hgamma HU).
    reflexivity.
  - rewrite in_app_iff in Hfresh.
    assert (Hbody : ~ In X (ftv_tm body)) by intuition.
    assert (HT : ~ In X (fv_ty T)) by intuition.
    rewrite (IHbody K theta gamma X U Hbody Htheta Hgamma HU).
    rewrite (instantiate_ty_open_rec T K theta X U HT Htheta HU).
    reflexivity.
  - reflexivity.
  - rewrite in_app_iff in Hfresh.
    rewrite IH1, IH2; intuition.
  - rewrite in_app_iff in Hfresh. rewrite IH1, IH2; intuition.
  - repeat rewrite in_app_iff in Hfresh.
    rewrite !instantiate_ty_open_rec, IHm, IHb; intuition.
  - repeat rewrite in_app_iff in Hfresh. rewrite IH, IH0, IH1; intuition.
  - rewrite in_app_iff in Hfresh. rewrite IH1, IH2; intuition.
  - reflexivity.
  - reflexivity.
  - repeat rewrite in_app_iff in Hfresh. rewrite IH1, IH2, IH3; intuition.
Qed.

Lemma instantiate_open_ty : forall t theta gamma X U,
  ~ In X (ftv_tm t) ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_ty U ->
  instantiate (type_subst_update theta X U) gamma
    (open_tm_ty t (Ty_FVar X)) =
  open_tm_ty (instantiate theta gamma t) U.
Proof.
  intros. unfold open_tm_ty.
  apply instantiate_open_ty_rec; assumption.
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

Lemma instantiate_ty_identity : forall T,
  instantiate_ty identity_type_substitution T = T.
Proof.
  induction T; simpl; try rewrite ?IHT1, ?IHT2, ?IHT; reflexivity.
Qed.

Lemma instantiate_identity : forall t,
  instantiate identity_type_substitution identity_term_substitution t = t.
Proof.
  induction t; simpl; rewrite ?IHt1, ?IHt2, ?IHt3, ?IHt3, ?IHt;
    try rewrite !instantiate_ty_identity; reflexivity.
Qed.

Lemma fv_open_tm_rec : forall t k u x,
  In x (fv_tm (open_tm_rec k u t)) ->
  In x (fv_tm t) \/ In x (fv_tm u).
Proof.
  induction t; intros k u x H; simpl in *.
  - destruct (Nat.eqb k n); simpl in *; tauto.
  - tauto.
  - eauto.
  - repeat rewrite in_app_iff in *. firstorder.
  - eauto.
  - eauto.
  - contradiction.
  - repeat rewrite in_app_iff in *. firstorder.
  - repeat rewrite in_app_iff in *. firstorder.
  - repeat rewrite in_app_iff in *. firstorder.
  - repeat rewrite in_app_iff in *. firstorder.
  - repeat rewrite in_app_iff in *. firstorder.
  - contradiction.
  - contradiction.
  - repeat rewrite in_app_iff in *. firstorder.
Qed.

Lemma instantiate_gamma_ext : forall t theta gamma gamma',
  (forall x, gamma x = gamma' x) ->
  instantiate theta gamma t = instantiate theta gamma' t.
Proof.
  induction t; intros; simpl; f_equal; eauto.
Qed.

Lemma instantiate_updates_commute : forall t theta gamma x y u v,
  x <> y ->
  instantiate theta (term_subst_update (term_subst_update gamma x u) y v) t =
  instantiate theta (term_subst_update (term_subst_update gamma y v) x u) t.
Proof.
  intros. apply instantiate_gamma_ext. intro z. unfold term_subst_update.
  destruct (Nat.eqb y z) eqn:Ey, (Nat.eqb x z) eqn:Ex; auto.
  apply Nat.eqb_eq in Ey, Ex. congruence.
Qed.

Lemma instantiate_open_fix_body : forall body theta gamma f x fv xv,
  ~ In f (fv_tm body) -> ~ In x (fv_tm body) -> f <> x ->
  type_substitution_closed theta -> term_substitution_closed gamma ->
  locally_closed_tm fv -> locally_closed_tm xv ->
  instantiate theta (term_subst_update (term_subst_update gamma x xv) f fv)
    (open_fix_body body (tm_fvar f) (tm_fvar x)) =
  open_fix_body (instantiate theta gamma body) fv xv.
Proof.
  intros body theta gamma f x fv xv Hf Hx Hneq Htheta Hgamma Hfv Hxv.
  rewrite instantiate_updates_commute by congruence.
  unfold open_fix_body, open_tm.
  rewrite instantiate_open_tm_rec.
  - rewrite instantiate_open_tm_rec; auto.
  - intro Hin. apply fv_open_tm_rec in Hin. simpl in Hin. intuition.
  - assumption.
  - apply term_subst_update_closed; assumption.
  - assumption.
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

Lemma wf_ty_weaken : forall Delta T,
  wf_ty Delta T ->
  forall Delta', ty_context_included Delta Delta' -> wf_ty Delta' T.
Proof.
  intros Delta T Hwf. induction Hwf; intros Delta' Hinc.
  - apply WF_Var. apply Hinc. assumption.
  - apply WF_Arrow; auto.
  - apply WF_All with L. intros X Hfresh.
    apply H0. exact Hfresh.
    unfold ty_context_included in *. simpl. intros Y [E | Hin].
    + left. exact E.
    + right. apply Hinc. exact Hin.
  - apply WF_Int.
  - apply WF_Bool.
Qed.

Lemma has_type_weaken_context : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall Gamma', context_included Gamma Gamma' ->
  has_type Delta Gamma' t T.
Proof.
  intros Delta Gamma t T Hty. induction Hty; intros Gamma' Hinc.
  - apply T_Var; [apply Hinc; assumption | assumption].
  - apply T_Abs with L; [assumption |]. intros x Hfresh.
    apply H1. exact Hfresh.
    unfold context_included in *. intros y U Hlookup.
    unfold update in *. simpl in *.
    destruct (Nat.eqb y x); [exact Hlookup |].
    apply Hinc. exact Hlookup.
  - apply T_App with T1; auto.
  - apply T_TAbs with L. intros X Hfresh. apply H0; assumption.
  - eapply T_TApp; eauto.
  - apply T_Int.
  - apply T_Div; auto.
  - apply T_Arith; auto.
  - apply T_Fix with L; try assumption.
    + intros x Hx. apply H2; [assumption |].
      intros y U Hy. simpl in *. destruct (Nat.eqb y x); auto.
    + intros f x Hf Hx. apply H4; try assumption.
      intros y U Hy. simpl in *. destruct (Nat.eqb y f); [assumption |].
      destruct (Nat.eqb y x); auto.
  - apply T_IfZero; auto.
  - apply T_Choice; auto.
  - apply T_True.
  - apply T_False.
  - eapply T_If; eauto.
Qed.

Lemma has_type_weaken_type : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall Delta', ty_context_included Delta Delta' ->
  has_type Delta' Gamma t T.
Proof.
  intros Delta Gamma t T Hty. induction Hty; intros Delta' Hinc.
  - apply T_Var; [assumption | eapply wf_ty_weaken; eauto].
  - apply T_Abs with L.
    + eapply wf_ty_weaken; eauto.
    + intros x Hfresh. apply H1; assumption.
  - apply T_App with T1; auto.
  - apply T_TAbs with L. intros X Hfresh.
    apply H0. exact Hfresh.
    unfold ty_context_included in *. simpl. intros Y [E | Hin].
    + left. exact E.
    + right. apply Hinc. exact Hin.
  - eapply T_TApp; eauto. eapply wf_ty_weaken; eauto.
  - apply T_Int.
  - apply T_Div; auto.
  - apply T_Arith; auto.
  - apply T_Fix with L.
    + eapply wf_ty_weaken; eauto.
    + eapply wf_ty_weaken; eauto.
    + intros x Hx. apply H2; assumption.
    + intros f x Hf Hx. apply H4; assumption.
  - apply T_IfZero; auto.
  - apply T_Choice; auto.
  - apply T_True.
  - apply T_False.
  - eapply T_If; eauto.
Qed.

Definition type_substitution_wf
    (Delta Delta' : ty_context) (theta : type_substitution) : Prop :=
  forall X, In X Delta -> wf_ty Delta' (theta X).

Lemma fv_ty_open_rec_preserves : forall T k U X,
  In X (fv_ty T) -> In X (fv_ty (open_ty_rec k U T)).
Proof.
  induction T; intros k U X Hin; simpl in *.
  - contradiction.
  - exact Hin.
  - apply in_app_iff in Hin. apply in_app_iff.
    destruct Hin as [Hin | Hin].
    + left. apply IHT1. exact Hin.
    + right. apply IHT2. exact Hin.
  - apply IHT. exact Hin.
  - contradiction.
  - contradiction.
Qed.

Lemma wf_ty_fv : forall Delta T,
  wf_ty Delta T -> forall X, In X (fv_ty T) -> In X Delta.
Proof.
  intros Delta T Hwf. induction Hwf; intros Y Hin; simpl in *.
  - destruct Hin as [E | Hin].
    + subst. assumption.
    + contradiction.
  - apply in_app_iff in Hin. destruct Hin; auto.
  - set (X := fresh (L ++ fv_ty T)).
    assert (HX : ~ In X (L ++ fv_ty T)).
    { subst X. apply fresh_notin. }
    rewrite in_app_iff in HX.
    assert (HXL : ~ In X L) by intuition.
    assert (HXfv : ~ In X (fv_ty T)) by intuition.
    pose proof (H0 X HXL Y) as IH.
    assert (Hopen : In Y (fv_ty (open_ty T (Ty_FVar X)))).
    { unfold open_ty. apply fv_ty_open_rec_preserves. exact Hin. }
    specialize (IH Hopen). simpl in IH.
    destruct IH as [E | HinDelta].
    + subst Y. contradiction.
    + exact HinDelta.
  - contradiction.
  - contradiction.
Qed.

Lemma instantiate_ty_open_rec_local : forall T k theta X U,
  ~ In X (fv_ty T) ->
  (forall Y, In Y (fv_ty T) -> locally_closed_ty (theta Y)) ->
  locally_closed_ty U ->
  instantiate_ty (type_subst_update theta X U)
    (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k U (instantiate_ty theta T).
Proof.
  induction T; intros k theta X U Hfresh Htheta HU; simpl in *.
  - destruct (Nat.eqb k n); simpl.
    + unfold type_subst_update. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - assert (X <> a) by (intro; subst; apply Hfresh; auto).
    unfold type_subst_update.
    rewrite (proj2 (Nat.eqb_neq X a)) by assumption.
    symmetry. apply open_ty_rec_lc_at.
    eapply lc_ty_at_monotone.
    + apply Htheta. auto.
    + lia.
  - rewrite in_app_iff in Hfresh.
    assert (Hfresh1 : ~ In X (fv_ty T1)) by intuition.
    assert (Hfresh2 : ~ In X (fv_ty T2)) by intuition.
    rewrite (IHT1 k theta X U Hfresh1),
      (IHT2 k theta X U Hfresh2); try assumption.
    + reflexivity.
    + intros Y Hin. apply Htheta. apply in_app_iff. auto.
    + intros Y Hin. apply Htheta. apply in_app_iff. auto.
  - rewrite IHT; try assumption. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma instantiate_ty_open_local : forall T theta X U,
  ~ In X (fv_ty T) ->
  (forall Y, In Y (fv_ty T) -> locally_closed_ty (theta Y)) ->
  locally_closed_ty U ->
  instantiate_ty (type_subst_update theta X U)
    (open_ty T (Ty_FVar X)) =
  open_ty (instantiate_ty theta T) U.
Proof.
  intros. unfold open_ty. apply instantiate_ty_open_rec_local; assumption.
Qed.

Lemma wf_ty_instantiate : forall Delta T,
  wf_ty Delta T ->
  forall Delta' theta,
    type_substitution_wf Delta Delta' theta ->
    wf_ty Delta' (instantiate_ty theta T).
Proof.
  intros Delta T Hwf. induction Hwf; intros Delta' theta Htheta; simpl.
  - apply Htheta. assumption.
  - apply WF_Arrow; auto.
  - apply WF_All with (L ++ Delta ++ Delta' ++ fv_ty T).
    intros X Hfresh.
    repeat rewrite in_app_iff in Hfresh.
    assert (HXL : ~ In X L) by intuition.
    assert (HXDelta : ~ In X Delta) by intuition.
    assert (HXDelta' : ~ In X Delta') by intuition.
    assert (HXT : ~ In X (fv_ty T)) by intuition.
    pose proof (H0 X HXL (X :: Delta')
      (type_subst_update theta X (Ty_FVar X))) as IH.
    assert (Hsub : type_substitution_wf (X :: Delta) (X :: Delta')
      (type_subst_update theta X (Ty_FVar X))).
    { unfold type_substitution_wf in *. intros Y [E | Hin].
      - subst Y. unfold type_subst_update. rewrite Nat.eqb_refl.
        apply WF_Var. simpl. auto.
      - assert (Hneq : X <> Y).
        { intro E. subst. contradiction. }
        unfold type_subst_update.
        rewrite (proj2 (Nat.eqb_neq X Y)) by assumption.
        eapply wf_ty_weaken.
        + apply Htheta. exact Hin.
        + unfold ty_context_included. simpl. auto. }
    assert (Hopen :
      instantiate_ty (type_subst_update theta X (Ty_FVar X))
        (open_ty T (Ty_FVar X)) =
      open_ty (instantiate_ty theta T) (Ty_FVar X)).
    { apply instantiate_ty_open_local.
      - exact HXT.
      - intros Y Hin. apply wf_ty_lc with Delta'. apply Htheta.
        assert (Hwhole : wf_ty Delta (Ty_All T)).
        { apply WF_All with L. exact H. }
        eapply wf_ty_fv; [exact Hwhole |]. simpl. exact Hin.
      - apply lc_ty_fvar. }
    rewrite <- Hopen. exact (IH Hsub).
  - apply WF_Int.
  - apply WF_Bool.
Qed.

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

Lemma context_included_update_fresh : forall Gamma x T,
  ~ In x (dom_context Gamma) ->
  context_included Gamma (update Gamma x T).
Proof.
  intros Gamma x T Hfresh y U Hlookup. unfold update. simpl.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst y.
    rewrite notin_dom_lookup_none in Hlookup by assumption. discriminate.
  - exact Hlookup.
Qed.

Lemma context_wf_update : forall Delta Gamma x T,
  context_wf Delta Gamma -> wf_ty Delta T ->
  context_wf Delta (update Gamma x T).
Proof.
  intros Delta Gamma x T Hctx HT y U Hlookup.
  unfold update in Hlookup. simpl in Hlookup.
  destruct (Nat.eqb y x) eqn:E.
  - inversion Hlookup; subst. exact HT.
  - apply Hctx with y. exact Hlookup.
Qed.

Lemma context_wf_weaken_type : forall Delta Gamma,
  context_wf Delta Gamma ->
  forall Delta', ty_context_included Delta Delta' ->
  context_wf Delta' Gamma.
Proof.
  intros Delta Gamma Hctx Delta' Hinc x T Hlookup.
  eapply wf_ty_weaken; [eapply Hctx; eauto | exact Hinc].
Qed.

Lemma instantiate_ty_update_irrelevant : forall T theta X U,
  ~ In X (fv_ty T) ->
  instantiate_ty (type_subst_update theta X U) T = instantiate_ty theta T.
Proof.
  induction T; intros theta X U Hfresh; simpl in *.
  - reflexivity.
  - unfold type_subst_update.
    assert (Hneq : X <> a) by (intro; subst; apply Hfresh; auto).
    rewrite (proj2 (Nat.eqb_neq X a)) by assumption. reflexivity.
  - rewrite in_app_iff in Hfresh.
    rewrite IHT1, IHT2; tauto.
  - f_equal. apply IHT. assumption.
  - reflexivity.
  - reflexivity.
Qed.

Lemma instantiate_ty_open_rec_commute : forall T k U theta,
  type_substitution_closed theta ->
  instantiate_ty theta (open_ty_rec k U T) =
  open_ty_rec k (instantiate_ty theta U) (instantiate_ty theta T).
Proof.
  induction T; intros k U theta Htheta; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. apply open_ty_rec_lc_at.
    eapply lc_ty_at_monotone; [apply Htheta | lia].
  - rewrite IHT1, IHT2; try assumption. reflexivity.
  - rewrite IHT; try assumption. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma instantiate_ty_open_commute : forall T U theta,
  type_substitution_closed theta ->
  instantiate_ty theta (open_ty T U) =
  open_ty (instantiate_ty theta T) (instantiate_ty theta U).
Proof.
  intros. unfold open_ty. apply instantiate_ty_open_rec_commute. assumption.
Qed.

Lemma term_substitution_typed_update : forall Gamma Delta' Gamma' theta gamma x T,
  term_substitution_typed Gamma Delta' Gamma' theta gamma ->
  ~ In x (dom_context Gamma') ->
  wf_ty Delta' (instantiate_ty theta T) ->
  term_substitution_typed (update Gamma x T) Delta'
    (update Gamma' x (instantiate_ty theta T)) theta
    (term_subst_update gamma x (tm_fvar x)).
Proof.
  intros Gamma Delta' Gamma' theta gamma x T Hgamma Hfresh Hwf y U Hlookup.
  simpl in Hlookup. unfold term_subst_update.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst y. rewrite Nat.eqb_refl.
    inversion Hlookup; subst U. apply T_Var; [apply lookup_context_update_eq | assumption].
  - apply Nat.eqb_neq in E. rewrite (proj2 (Nat.eqb_neq x y)) by congruence.
    eapply has_type_weaken_context; [eapply Hgamma; eauto |].
    apply context_included_update_fresh. assumption.
Qed.

Lemma has_type_instantiate : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  context_wf Delta Gamma ->
  forall Delta' Gamma' theta gamma,
    type_substitution_closed theta ->
    term_substitution_closed gamma ->
    type_substitution_wf Delta Delta' theta ->
    term_substitution_typed Gamma Delta' Gamma' theta gamma ->
    has_type Delta' Gamma'
      (instantiate theta gamma t) (instantiate_ty theta T).
Proof.
  intros Delta Gamma t T Hty. induction Hty as
      [Delta Gamma x T Hlookup Hwf
      | L Delta Gamma T1 body T2 Hwf Hbody IHbody
      | Delta Gamma t1 t2 T1 T2 Ht1 IHt1 Ht2 IHt2
      | L Delta Gamma body T Hbody IHbody
      | Delta Gamma t T U Ht IHt HU
      | Delta Gamma n
      | Delta Gamma t1 t2 Ht1 IHt1 Ht2 IHt2
      | Delta Gamma op t1 t2 Ht1 IHt1 Ht2 IHt2
      | L Delta Gamma A B metric body HA HB Hmetric IHmetric Hbody IHbody
      | Delta Gamma t t0 t1 T Ht IHt Ht0 IHt0 Ht1 IHt1
      | Delta Gamma t1 t2 T Ht1 IHt1 Ht2 IHt2
      | Delta Gamma
      | Delta Gamma
      | Delta Gamma t1 t2 t3 T Ht1 IHt1 Ht2 IHt2 Ht3 IHt3];
    intros Hctx Delta' Gamma' theta gamma Htheta Hgamma Htheta_wf Hgamma_ty;
    simpl.
  - eapply Hgamma_ty. exact Hlookup.
  - apply T_Abs with (L ++ fv_tm body ++ dom_context Gamma').
    + eapply wf_ty_instantiate; eauto.
    + intros x Hfresh. repeat rewrite in_app_iff in Hfresh.
      assert (HxL : ~ In x L) by intuition.
      assert (Hxbody : ~ In x (fv_tm body)) by intuition.
      assert (HxGamma' : ~ In x (dom_context Gamma')) by intuition.
      pose proof (IHbody x HxL
        (context_wf_update Delta Gamma x T1 Hctx Hwf)
        Delta' (update Gamma' x (instantiate_ty theta T1)) theta
        (term_subst_update gamma x (tm_fvar x))) as IH.
      rewrite <- (instantiate_open_tm body theta gamma x (tm_fvar x));
        try assumption; try apply lc_tm_fvar.
      apply IH; try assumption.
      * apply term_subst_update_closed; [assumption | apply lc_tm_fvar].
      * unfold term_substitution_typed. intros y U Hlookup'.
        unfold update in Hlookup'. simpl in Hlookup'.
        unfold term_subst_update.
        destruct (Nat.eqb y x) eqn:E.
        -- apply Nat.eqb_eq in E. subst y. rewrite Nat.eqb_refl.
           inversion Hlookup'; subst U.
           apply T_Var.
           ++ unfold update. simpl. rewrite Nat.eqb_refl. reflexivity.
           ++ eapply wf_ty_instantiate; eauto.
        -- apply Nat.eqb_neq in E.
           rewrite (proj2 (Nat.eqb_neq x y)) by congruence.
           eapply has_type_weaken_context.
           ++ eapply Hgamma_ty. exact Hlookup'.
           ++ apply context_included_update_fresh. exact HxGamma'.
  - eapply T_App.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
  - apply T_TAbs with
      (L ++ Delta ++ Delta' ++ ftv_tm body ++ fv_ty T).
    intros X Hfresh. repeat rewrite in_app_iff in Hfresh.
    assert (HXL : ~ In X L) by intuition.
    assert (HXDelta : ~ In X Delta) by intuition.
    assert (HXDelta' : ~ In X Delta') by intuition.
    assert (HXbody : ~ In X (ftv_tm body)) by intuition.
    assert (HXT : ~ In X (fv_ty T)) by intuition.
    set (theta' := type_subst_update theta X (Ty_FVar X)).
    assert (Hctx' : context_wf (X :: Delta) Gamma).
    { eapply context_wf_weaken_type; [exact Hctx |].
      unfold ty_context_included. simpl. auto. }
    assert (Htheta_wf' : type_substitution_wf
      (X :: Delta) (X :: Delta') theta').
    { unfold theta', type_substitution_wf, type_subst_update.
      intros Y [E | Hin].
      - subst Y. rewrite Nat.eqb_refl. apply WF_Var. simpl. auto.
      - assert (Hneq : X <> Y) by (intro; subst; contradiction).
        rewrite (proj2 (Nat.eqb_neq X Y)) by assumption.
        eapply wf_ty_weaken.
        + apply Htheta_wf. exact Hin.
        + unfold ty_context_included. simpl. auto. }
    assert (Hgamma_ty' : term_substitution_typed
      Gamma (X :: Delta') Gamma' theta' gamma).
    { unfold term_substitution_typed in *. intros x U Hlookup.
      assert (HwfU : wf_ty Delta U) by (eapply Hctx; eauto).
      assert (HXU : ~ In X (fv_ty U)).
      { intro Hin. apply HXDelta. eapply wf_ty_fv; eauto. }
      unfold theta'.
      rewrite instantiate_ty_update_irrelevant by exact HXU.
      eapply has_type_weaken_type.
      - eapply Hgamma_ty. exact Hlookup.
      - unfold ty_context_included. simpl. auto. }
    pose proof (IHbody X HXL Hctx' (X :: Delta') Gamma'
      theta' gamma) as IH.
    rewrite <- (instantiate_open_ty body theta gamma X (Ty_FVar X));
      try assumption; try apply lc_ty_fvar.
    rewrite <- (instantiate_ty_open T theta X (Ty_FVar X));
      try assumption; try apply lc_ty_fvar.
    assert (Htheta' : type_substitution_closed theta').
    { unfold theta'. apply type_subst_update_closed; auto. apply lc_ty_fvar. }
    exact (IH Htheta' Hgamma Htheta_wf' Hgamma_ty').
  - rewrite instantiate_ty_open_commute by exact Htheta.
    eapply T_TApp.
    + apply IHt; assumption.
    + eapply wf_ty_instantiate; eauto.
  - apply T_Int.
  - apply T_Div; [apply IHt1 | apply IHt2]; assumption.
  - apply T_Arith; [apply IHt1 | apply IHt2]; assumption.
  - apply T_Fix with (L ++ fv_tm metric ++ fv_tm body ++ dom_context Gamma').
    + eapply wf_ty_instantiate; eauto.
    + eapply wf_ty_instantiate; eauto.
    + intros x Hx. repeat rewrite in_app_iff in Hx.
      rewrite <- (instantiate_open_tm metric theta gamma x (tm_fvar x));
        try assumption; try apply lc_tm_fvar; try tauto.
      apply IHmetric.
      * tauto.
      * apply context_wf_update; assumption.
      * assumption.
      * apply term_subst_update_closed; [assumption | constructor].
      * assumption.
      * apply term_substitution_typed_update; try assumption; try tauto.
        eapply wf_ty_instantiate; eauto.
    + intros f x Hf Hx. simpl in Hx.
      repeat rewrite in_app_iff in Hf, Hx.
      rewrite <- (instantiate_open_fix_body body theta gamma f x (tm_fvar f) (tm_fvar x));
        try assumption; try constructor; try tauto.
      apply IHbody.
      * tauto.
      * simpl. tauto.
      * apply context_wf_update.
        -- apply context_wf_update; assumption.
        -- apply WF_Arrow; assumption.
      * assumption.
      * apply term_subst_update_closed; [| constructor].
        apply term_subst_update_closed; [assumption | constructor].
      * assumption.
      * change (term_substitution_typed (update (update Gamma x A) f (Ty_Arrow A B))
          Delta' (update (update Gamma' x (instantiate_ty theta A))
            f (instantiate_ty theta (Ty_Arrow A B))) theta
          (term_subst_update (term_subst_update gamma x (tm_fvar x)) f (tm_fvar f))).
        apply term_substitution_typed_update.
        -- apply term_substitution_typed_update; try assumption; try tauto.
           eapply wf_ty_instantiate; eauto.
        -- simpl. intuition congruence.
        -- simpl. apply WF_Arrow; eapply wf_ty_instantiate; eauto.
  - apply T_IfZero; [apply IHt | apply IHt0 | apply IHt1]; assumption.
  - apply T_Choice; [apply IHt1 | apply IHt2]; assumption.
  - apply T_True.
  - apply T_False.
  - eapply T_If; [apply IHt1 | apply IHt2 | apply IHt3]; assumption.
Qed.

Lemma wf_ty_open_all : forall Delta T U,
  wf_ty Delta (Ty_All T) -> wf_ty Delta U -> wf_ty Delta (open_ty T U).
Proof.
  intros Delta T U Hall HU.
  inversion Hall as [| |L Delta0 body Hbody| |]; subst.
  set (X := fresh (L ++ Delta ++ fv_ty T)).
  assert (HX : ~ In X (L ++ Delta ++ fv_ty T)).
  { subst X. apply fresh_notin. }
  repeat rewrite in_app_iff in HX.
  assert (HXL : ~ In X L) by intuition.
  assert (HXDelta : ~ In X Delta) by intuition.
  assert (HXT : ~ In X (fv_ty T)) by intuition.
  pose proof (Hbody X HXL) as Hopened.
  set (theta := type_subst_update identity_type_substitution X U).
  assert (Htheta_closed : type_substitution_closed theta).
  { unfold theta. apply type_subst_update_closed.
    - apply identity_type_substitution_closed.
    - apply wf_ty_lc with Delta. exact HU. }
  assert (Htheta_wf : type_substitution_wf (X :: Delta) Delta theta).
  { unfold theta, type_substitution_wf, type_subst_update,
      identity_type_substitution.
    intros Y [E | Hin].
    - subst Y. rewrite Nat.eqb_refl. exact HU.
    - assert (Hneq : X <> Y) by (intro; subst; contradiction).
      rewrite (proj2 (Nat.eqb_neq X Y)) by assumption.
      apply WF_Var. exact Hin. }
  pose proof (wf_ty_instantiate _ _ Hopened Delta theta Htheta_wf) as Hinst.
  assert (Hopen : instantiate_ty theta (open_ty T (Ty_FVar X)) = open_ty T U).
  { unfold theta.
    rewrite instantiate_ty_open_local.
    - rewrite instantiate_ty_identity. reflexivity.
    - exact HXT.
    - intros Y Hin. apply lc_ty_fvar.
    - apply wf_ty_lc with Delta. exact HU. }
  rewrite Hopen in Hinst. exact Hinst.
Qed.

Lemma typing_type_wf : forall Delta Gamma t T,
  has_type Delta Gamma t T -> wf_ty Delta T.
Proof.
  intros Delta Gamma t T Hty. induction Hty.
  - exact H0.
  - apply WF_Arrow; [exact H |].
    set (x := fresh L). apply H1 with x. subst x. apply fresh_notin.
  - inversion IHHty1. assumption.
  - apply WF_All with L. intros X Hfresh. apply H0. exact Hfresh.
  - eapply wf_ty_open_all; eauto.
  - apply WF_Int.
  - apply WF_Int.
  - apply WF_Int.
  - apply WF_Arrow; assumption.
  - assumption.
  - exact IHHty1.
  - apply WF_Bool.
  - apply WF_Bool.
  - exact IHHty2.
Qed.

Lemma fv_tm_open_preserves : forall t k u x,
  In x (fv_tm t) -> In x (fv_tm (open_tm_rec k u t)).
Proof.
  induction t; intros k u x Hin; simpl in *; try contradiction; try assumption;
    try solve [eauto];
    repeat rewrite in_app_iff in *; intuition eauto.
Qed.

Lemma fv_tm_open_type : forall t k U,
  fv_tm (open_tm_ty_rec k U t) = fv_tm t.
Proof.
  induction t; intros; simpl; rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3; reflexivity.
Qed.

Lemma typing_fv_bound : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall x, lookup_context x Gamma = None -> ~ In x (fv_tm t).
Proof.
  intros Delta Gamma t T Hty.
  induction Hty as
    [Delta Gamma y T Hlookup Hwf
    |L Delta Gamma A body B HA Hbody IHbody
    |Delta Gamma t1 t2 A B Ht1 IHt1 Ht2 IHt2
    |L Delta Gamma body T Hbody IHbody
    |Delta Gamma t T U Ht IHt HU
    |Delta Gamma n
    |Delta Gamma t1 t2 Ht1 IHt1 Ht2 IHt2
      | Delta Gamma op t1 t2 Ht1 IHt1 Ht2 IHt2
    |L Delta Gamma A B metric body HA HB Hmetric IHmetric Hbody IHbody
    |Delta Gamma t t0 t1 T Ht IHt Ht0 IHt0 Ht1 IHt1
      | Delta Gamma t1 t2 T Ht1 IHt1 Ht2 IHt2
      | Delta Gamma | Delta Gamma
      | Delta Gamma t1 t2 t3 T Ht1 IHt1 Ht2 IHt2 Ht3 IHt3];
    intros x Hnone Hin; simpl in Hin.
  - destruct Hin as [E | []]. subst. congruence.
  - set (y := fresh (x :: L)).
    assert (Hy : ~ In y (x :: L)) by apply fresh_notin. simpl in Hy.
    apply (IHbody y ltac:(tauto) x).
    + simpl. rewrite (proj2 (Nat.eqb_neq x y)) by intuition congruence. exact Hnone.
    + apply fv_tm_open_preserves. exact Hin.
  - apply in_app_iff in Hin. destruct Hin; [eapply IHt1 | eapply IHt2]; eauto.
  - apply (IHbody (fresh L) (fresh_notin L) x Hnone).
    unfold open_tm_ty. rewrite fv_tm_open_type. exact Hin.
  - eapply IHt; eauto.
  - contradiction.
  - apply in_app_iff in Hin. destruct Hin; [eapply IHt1 | eapply IHt2]; eauto.
  - apply in_app_iff in Hin. destruct Hin; [eapply IHt1 | eapply IHt2]; eauto.
  - set (f := fresh (x :: L)).
    set (y := fresh (f :: x :: L)).
    assert (Hf : ~ In f (x :: L)) by apply fresh_notin.
    assert (Hy : ~ In y (f :: x :: L)) by apply fresh_notin.
    simpl in Hf, Hy.
    apply in_app_iff in Hin. destruct Hin as [Hin | Hin].
    + apply (IHmetric y ltac:(tauto) x).
      * simpl. rewrite (proj2 (Nat.eqb_neq x y)) by intuition congruence. exact Hnone.
      * apply fv_tm_open_preserves. exact Hin.
    + apply (IHbody f y ltac:(tauto) ltac:(simpl; tauto) x).
      * simpl. rewrite (proj2 (Nat.eqb_neq x f)) by intuition congruence.
        rewrite (proj2 (Nat.eqb_neq x y)) by intuition congruence. exact Hnone.
      * unfold open_fix_body, open_tm.
        apply fv_tm_open_preserves. apply fv_tm_open_preserves. exact Hin.
  - repeat rewrite in_app_iff in Hin.
    destruct Hin as [Hin | [Hin | Hin]]; [eapply IHt | eapply IHt0 | eapply IHt1]; eauto.
  - apply in_app_iff in Hin. destruct Hin; [eapply IHt1 |eapply IHt2]; eauto.
  - contradiction.
  - contradiction.
  - repeat rewrite in_app_iff in Hin. destruct Hin as [Hin | [Hin | Hin]]; [eapply IHt1 |eapply IHt2 |eapply IHt3]; eauto.
Qed.

Lemma closed_typing_no_free_terms : forall Delta t T,
  has_type Delta empty t T -> fv_tm t = [].
Proof.
  intros Delta t T Htyped.
  destruct (fv_tm t) as [| x xs] eqn:E; [reflexivity |].
  exfalso. apply (typing_fv_bound _ _ _ _ Htyped x eq_refl).
  rewrite E. simpl. auto.
Qed.

Lemma instantiate_no_free_terms : forall t gamma,
  fv_tm t = [] ->
  instantiate identity_type_substitution gamma t = t.
Proof.
  induction t; intros gamma Hfv; simpl in *; try discriminate;
    repeat match goal with H : _ ++ _ = [] |- _ => apply app_eq_nil in H as [? ?] end;
    rewrite ?instantiate_ty_identity; f_equal; eauto.
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

Lemma interpret_qualifier_ext : forall atoms1 atoms2 p,
  (forall t1 t2, atoms1.(interpret_eq) t1 t2 <-> atoms2.(interpret_eq) t1 t2) ->
  (forall t1 t2, atoms1.(interpret_lt) t1 t2 <-> atoms2.(interpret_lt) t1 t2) ->
  (forall t1 t2, atoms1.(interpret_le) t1 t2 <-> atoms2.(interpret_le) t1 t2) ->
  (interpret_qualifier atoms1 p <-> interpret_qualifier atoms2 p).
Proof.
  intros atoms1 atoms2 p Heq Hlt Hle.
  induction p; simpl; firstorder.
Qed.

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

Lemma erase_open_rty_tm_rec : forall R k u,
  erase (open_rty_tm_rec k u R) = erase R.
Proof.
  induction R; intros; simpl; try rewrite IHR1; try rewrite IHR2;
    try rewrite IHR; reflexivity.
Qed.

Lemma erase_open_rty_tm : forall R u,
  erase (open_rty_tm R u) = erase R.
Proof.
  intros. apply erase_open_rty_tm_rec.
Qed.

Lemma erase_open_rty_ty_rec : forall R k U,
  erase (open_rty_ty_rec k U R) = open_ty_rec k U (erase R).
Proof.
  induction R; intros; simpl.
  - reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR2. reflexivity.
  - rewrite IHR. reflexivity.
Qed.

Lemma erase_open_rty_ty : forall R U,
  erase (open_rty_ty R U) = open_ty (erase R) U.
Proof.
  intros. unfold open_rty_ty, open_ty. apply erase_open_rty_ty_rec.
Qed.

Lemma lookup_erase_context : forall RGamma x R,
  lookup_rcontext x RGamma = Some R ->
  lookup_context x (erase_context RGamma) = Some (erase R).
Proof.
  induction RGamma as [|[y S] RGamma IH]; intros x R Hlookup; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + inversion Hlookup; subst. reflexivity.
    + apply IH. exact Hlookup.
Qed.

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

Lemma close_open_ty_rec : forall T k X,
  ~ In X (fv_ty T) ->
  close_ty_rec k X (open_ty_rec k (Ty_FVar X) T) = T.
Proof.
  induction T; intros k X Hfresh; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n.
      change ((if Nat.eqb X X then Ty_BVar k else Ty_FVar X) = Ty_BVar k).
      rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - assert (X <> a) by intuition.
    rewrite (proj2 (Nat.eqb_neq X a)) by assumption. reflexivity.
  - rewrite in_app_iff in Hfresh. rewrite IHT1, IHT2; intuition.
  - rewrite IHT by assumption. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma open_ty_fresh_injective : forall T1 T2 X,
  ~ In X (fv_ty T1) ->
  ~ In X (fv_ty T2) ->
  open_ty T1 (Ty_FVar X) = open_ty T2 (Ty_FVar X) ->
  T1 = T2.
Proof.
  intros T1 T2 X H1 H2 E.
  apply (f_equal (close_ty_rec 0 X)) in E.
  unfold open_ty in E.
  rewrite (close_open_ty_rec T1 0 X H1) in E.
  rewrite (close_open_ty_rec T2 0 X H2) in E.
  exact E.
Qed.

Lemma subtype_erases : forall Delta RGamma R S,
  subtype Delta RGamma R S -> erase R = erase S.
Proof.
  fix IH 5.
  intros Delta RGamma R S Hsub.
  destruct Hsub as
    [Delta RGamma R
    |L Delta RGamma T ps qs Hentails
    |L Delta RGamma R1 R2 S1 S2 Hdom Hcod
    |Delta RGamma v R1 R2 S Hv Htyped Hbody
    |L Delta RGamma R1 R2 S HR1 HS Hbody
    |L Delta RGamma R S Hbody
    |Delta RGamma R S U HRS HSU].
  - reflexivity.
  - reflexivity.
  - simpl. f_equal.
    + symmetry. exact (IH _ _ _ _ Hdom).
    + set (x := fresh L).
      assert (Hfresh : ~ In x L) by (subst x; apply fresh_notin).
      pose proof (IH _ _ _ _ (Hcod x Hfresh)) as E.
      rewrite !erase_open_rty_tm in E. exact E.
  - simpl. pose proof (IH _ _ _ _ Hbody) as E.
    rewrite erase_open_rty_tm in E. exact E.
  - simpl. set (x := fresh L).
    assert (Hfresh : ~ In x L) by (subst x; apply fresh_notin).
    pose proof (IH _ _ _ _ (Hbody x Hfresh)) as E.
    rewrite erase_open_rty_tm in E. exact E.
  - simpl. f_equal.
    set (X := fresh (L ++ fv_ty (erase R) ++ fv_ty (erase S))).
    assert (HX : ~ In X (L ++ fv_ty (erase R) ++ fv_ty (erase S))).
    { subst X. apply fresh_notin. }
    repeat rewrite in_app_iff in HX.
    assert (HXL : ~ In X L) by intuition.
    assert (HXR : ~ In X (fv_ty (erase R))) by intuition.
    assert (HXS : ~ In X (fv_ty (erase S))) by intuition.
    pose proof (IH _ _ _ _ (Hbody X HXL)) as E.
    rewrite !erase_open_rty_ty in E.
    eapply open_ty_fresh_injective; eauto.
  - etransitivity.
    + exact (IH _ _ _ _ HRS).
    + exact (IH _ _ _ _ HSU).
Qed.

Lemma wf_rty_erases : forall Delta RGamma R,
  wf_rty Delta RGamma R -> wf_ty Delta (erase R).
Proof.
  fix IH 4.
  intros Delta RGamma R Hwf.
  destruct Hwf as
    [L Delta RGamma T ps HT Hps
    |L Delta RGamma R1 R2 HR1 HR2
    |L Delta RGamma R1 R2 HR1 HR2
    |L Delta RGamma R HR].
  - exact HT.
  - simpl. apply WF_Arrow.
    + exact (IH _ _ _ HR1).
    + set (x := fresh L).
      rewrite <- (erase_open_rty_tm R2 (tm_fvar x)).
      apply IH with (RGamma := update_rcontext RGamma x R1).
      apply HR2. subst x. apply fresh_notin.
  - simpl. set (x := fresh L).
    rewrite <- (erase_open_rty_tm R2 (tm_fvar x)).
    apply IH with (RGamma := update_rcontext RGamma x R1).
    apply HR2. subst x. apply fresh_notin.
  - simpl. apply WF_All with L. intros X Hfresh.
    rewrite <- erase_open_rty_ty.
    apply IH with (RGamma := RGamma).
    apply HR. exact Hfresh.
Qed.

Lemma core_typing_context : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall Gamma',
    (forall x U, lookup_context x Gamma = Some U ->
                 lookup_context x Gamma' = Some U) ->
    has_type Delta Gamma' t T.
Proof.
  intros Delta Gamma t T Hty. induction Hty; intros Gamma' Hinc.
  - apply T_Var; [apply Hinc; assumption | assumption].
  - apply T_Abs with L; [assumption |]. intros x Hfresh.
    apply H1; [assumption |]. intros y U Hlookup.
    simpl in *. destruct (Nat.eqb y x); auto.
  - eapply T_App; eauto.
  - apply T_TAbs with L. intros X Hfresh. apply H0; assumption.
  - eapply T_TApp; eauto.
  - apply T_Int.
  - apply T_Div; auto.
  - apply T_Arith; auto.
  - apply T_Fix with L; try assumption.
    + intros x Hfresh. apply H2; [assumption |].
      intros y U Hlookup. simpl in *.
      destruct (Nat.eqb y x); auto.
    + intros f x Hf Hx. apply H4; try assumption.
      intros y U Hlookup. simpl in *.
      destruct (Nat.eqb y f); [assumption |].
      destruct (Nat.eqb y x); auto.
  - apply T_IfZero; auto.
  - apply T_Choice; auto.
  - apply T_True.
  - apply T_False.
  - eapply T_If; eauto.
Qed.

Lemma erase_context_strengthen : forall RGamma x p q,
  lookup_rcontext x RGamma = Some (R_Refine Ty_Int p) ->
  forall y U,
    lookup_context y (erase_context
      (update_rcontext RGamma x (R_Refine Ty_Int q))) = Some U ->
    lookup_context y (erase_context RGamma) = Some U.
Proof.
  intros RGamma x p q Hx y U Hy. simpl in Hy.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst y. inversion Hy; subst U.
    exact (lookup_erase_context RGamma x (R_Refine Ty_Int p) Hx).
  - exact Hy.
Qed.

Theorem refinement_typing_erases : forall Delta RGamma t R,
  has_rtype Delta RGamma t R ->
  has_type Delta (erase_context RGamma) t (erase R).
Proof.
  intros Delta RGamma t R Hty. induction Hty.
  - apply T_Var.
    + eapply lookup_erase_context. exact H.
    + exact (wf_rty_erases Delta RGamma R H0).
  - simpl. apply T_Abs with L.
    + exact (wf_rty_erases Delta RGamma R1 H).
    + intros x Hfresh. simpl.
      rewrite <- (erase_open_rty_tm R2 (tm_fvar x)).
      apply H1. exact Hfresh.
  - simpl. eapply T_App; eauto.
  - simpl. apply T_TAbs with L. intros X Hfresh.
    rewrite <- (erase_open_rty_ty R (Ty_FVar X)). apply H0. exact Hfresh.
  - rewrite (erase_open_rty_ty R U). eapply T_TApp; eauto.
  - apply T_Int.
  - simpl in *. apply T_Div; assumption.
  - simpl in *. apply T_Arith; assumption.
  - apply T_Choice; auto.
  - apply T_True.
  - apply T_False.
  - eapply T_If; eauto.
  - exact H.
  - simpl. apply T_Fix with L.
    + pose proof (wf_rty_erases _ _ _ H) as E. inversion E; assumption.
    + pose proof (wf_rty_erases _ _ _ H) as E. inversion E; assumption.
    + exact H0.
    + intros f x Hf Hx.
      pose proof (H2 f x Hf Hx) as E.
      rewrite erase_open_rty_tm in E. exact E.
  - simpl in *. apply T_IfZero.
    + apply T_Var.
      * exact (lookup_erase_context RGamma x (R_Refine Ty_Int p) H).
      * apply WF_Int.
    + eapply core_typing_context; [exact IHHty1 |].
      exact (erase_context_strengthen RGamma x p
        (Pred_And p (Pred_Eq (tm_bvar 0) (tm_int 0%Z))) H).
    + eapply core_typing_context; [exact IHHty2 |].
      exact (erase_context_strengthen RGamma x p
        (Pred_And p (Pred_Ne (tm_bvar 0) (tm_int 0%Z))) H).
  - match goal with
    | Hsub : subtype _ _ _ _ |- _ =>
        pose proof (subtype_erases _ _ _ _ Hsub) as E
    end.
    rewrite <- E. exact IHHty.
Qed.

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

Lemma step_preserves_lc : forall t u,
  t --> u -> locally_closed_tm t -> locally_closed_tm u.
Proof.
  intros t u Hstep. induction Hstep; intros Hlc; unfold locally_closed_tm in *;
    inversion Hlc; subst; eauto 10 using lc_tm_at, value_regular.
  - eapply open_tm_preserves_lc_at.
    + inversion H; eassumption.
    + apply value_regular. exact H0.
  - eapply open_tm_ty_preserves_lc_at.
    + inversion H; eassumption.
    + exact H0.
  - unfold open_fix_body, open_tm.
    eapply open_tm_preserves_lc_at.
    + eapply open_tm_preserves_lc_at.
      * inversion H; eassumption.
      * exact H.
    + apply value_regular. exact H0.
Qed.

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

Lemma term_beta_typing : forall L T1 body T2 v,
  wf_ty [] T1 ->
  (forall x, ~ In x L ->
    has_type [] (update empty x T1)
      (open_tm body (tm_fvar x)) T2) ->
  has_type [] empty v T1 ->
  has_type [] empty (open_tm body v) T2.
Proof.
  intros L T1 body T2 v HT1 Hbody Hv.
  set (x := fresh (L ++ fv_tm body)).
  assert (Hx : ~ In x (L ++ fv_tm body)).
  { subst x. apply fresh_notin. }
  rewrite in_app_iff in Hx.
  assert (HxL : ~ In x L) by intuition.
  assert (Hxfv : ~ In x (fv_tm body)) by intuition.
  pose proof (Hbody x HxL) as Hopened.
  set (gamma := term_subst_update identity_term_substitution x v).
  assert (Hctx : context_wf [] (update empty x T1)).
  { intros y U Hlookup. unfold update, empty in Hlookup. simpl in Hlookup.
    destruct (Nat.eqb y x) eqn:E; try discriminate.
    inversion Hlookup; subst. exact HT1. }
  assert (Htheta_wf :
    type_substitution_wf [] [] identity_type_substitution).
  { intros X Hin. contradiction. }
  assert (Hgamma_typed : term_substitution_typed
      (update empty x T1) [] empty identity_type_substitution gamma).
  { intros y U Hlookup. unfold update, empty in Hlookup. simpl in Hlookup.
    destruct (Nat.eqb y x) eqn:E; try discriminate.
    apply Nat.eqb_eq in E. subst y. inversion Hlookup; subst U.
    unfold gamma, term_subst_update. rewrite Nat.eqb_refl.
    rewrite instantiate_ty_identity. exact Hv. }
  pose proof (has_type_instantiate _ _ _ _ Hopened Hctx
    [] empty identity_type_substitution gamma
    identity_type_substitution_closed
    (term_subst_update_closed identity_term_substitution x v
      identity_term_substitution_closed (typing_lc _ _ _ _ Hv))
    Htheta_wf Hgamma_typed) as Hinst.
  unfold gamma in Hinst.
  rewrite (instantiate_open_tm body identity_type_substitution
      identity_term_substitution x v Hxfv
      identity_type_substitution_closed identity_term_substitution_closed
      (typing_lc _ _ _ _ Hv)) in Hinst.
  rewrite instantiate_identity, instantiate_ty_identity in Hinst.
  exact Hinst.
Qed.

Lemma type_beta_typing : forall L body T U,
  (forall X, ~ In X L ->
    has_type [X] empty
      (open_tm_ty body (Ty_FVar X))
      (open_ty T (Ty_FVar X))) ->
  wf_ty [] U ->
  has_type [] empty (open_tm_ty body U) (open_ty T U).
Proof.
  intros L body T U Hbody HU.
  set (X := fresh (L ++ ftv_tm body ++ fv_ty T)).
  assert (HX : ~ In X (L ++ ftv_tm body ++ fv_ty T)).
  { subst X. apply fresh_notin. }
  repeat rewrite in_app_iff in HX.
  assert (HXL : ~ In X L) by intuition.
  assert (HXbody : ~ In X (ftv_tm body)) by intuition.
  assert (HXT : ~ In X (fv_ty T)) by intuition.
  pose proof (Hbody X HXL) as Hopened.
  set (theta := type_subst_update identity_type_substitution X U).
  assert (Htheta_closed : type_substitution_closed theta).
  { unfold theta. apply type_subst_update_closed.
    - exact identity_type_substitution_closed.
    - exact (wf_ty_lc [] U HU). }
  assert (Htheta_wf : type_substitution_wf [X] [] theta).
  { intros Y Hin. simpl in Hin. destruct Hin as [E | Hin]; [|contradiction].
    subst Y. unfold theta, type_subst_update. rewrite Nat.eqb_refl. exact HU. }
  assert (Hctx : context_wf [X] empty).
  { intros y V Hlookup. discriminate. }
  assert (Hgamma_typed : term_substitution_typed
      empty [] empty theta identity_term_substitution).
  { intros y V Hlookup. discriminate. }
  pose proof (has_type_instantiate _ _ _ _ Hopened Hctx
    [] empty theta identity_term_substitution
    Htheta_closed identity_term_substitution_closed
    Htheta_wf Hgamma_typed) as Hinst.
  unfold theta in Hinst.
  rewrite (instantiate_open_ty body identity_type_substitution
      identity_term_substitution X U HXbody
      identity_type_substitution_closed identity_term_substitution_closed
      (wf_ty_lc [] U HU)) in Hinst.
  rewrite (instantiate_ty_open_local T identity_type_substitution X U HXT) in Hinst.
  - rewrite instantiate_identity, instantiate_ty_identity in Hinst. exact Hinst.
  - intros Y Hin. apply lc_ty_fvar.
  - exact (wf_ty_lc [] U HU).
Qed.

Lemma fix_beta_typing : forall A B metric body arg,
  has_type [] empty (tm_fix A B metric body) (Ty_Arrow A B) ->
  has_type [] empty arg A ->
  has_type [] empty (open_fix_body body (tm_fix A B metric body) arg) B.
Proof.
  intros A B metric body arg Hfix Harg.
  inversion Hfix as [ | | | | | | | | L D G A' B' m b HA HB Hmetric Hbody | | | | | ]; subst.
  set (f := fresh (L ++ fv_tm body)).
  set (x := fresh (f :: L ++ fv_tm body)).
  assert (Hf : ~ In f (L ++ fv_tm body)) by (apply fresh_notin).
  assert (Hx : ~ In x (f :: L ++ fv_tm body)) by (apply fresh_notin).
  simpl in Hx. repeat rewrite in_app_iff in Hf, Hx.
  assert (HfL : ~ In f L) by tauto.
  assert (HxL : ~ In x (f :: L)) by (simpl; tauto).
  pose proof (Hbody f x HfL HxL) as Ho.
  set (gamma := term_subst_update
    (term_subst_update identity_term_substitution x arg) f (tm_fix A B metric body)).
  assert (Hctx : context_wf [] (update (update empty x A) f (Ty_Arrow A B))).
  { apply context_wf_update.
    - apply context_wf_update; [intros y T E; discriminate | assumption].
    - apply WF_Arrow; assumption. }
  assert (Hgamma : term_substitution_closed gamma).
  { unfold gamma. apply term_subst_update_closed.
    - apply term_subst_update_closed; [apply identity_term_substitution_closed |].
      eapply typing_lc; eauto.
    - eapply typing_lc; eauto. }
  assert (Hgt : term_substitution_typed
    (update (update empty x A) f (Ty_Arrow A B))
    [] empty identity_type_substitution gamma).
  { intros y T Hy. simpl in Hy. unfold gamma, term_subst_update.
    destruct (Nat.eqb y f) eqn:Ef.
    - apply Nat.eqb_eq in Ef. subst y. rewrite Nat.eqb_refl.
      inversion Hy; subst T. rewrite instantiate_ty_identity. assumption.
    - apply Nat.eqb_neq in Ef. rewrite (proj2 (Nat.eqb_neq f y)) by congruence.
      destruct (Nat.eqb y x) eqn:Ex; [| discriminate].
      apply Nat.eqb_eq in Ex. subst y. rewrite Nat.eqb_refl.
      inversion Hy; subst T. rewrite instantiate_ty_identity. assumption. }
  assert (Htw : type_substitution_wf [] [] identity_type_substitution).
  { intros X HX. contradiction. }
  pose proof (has_type_instantiate _ _ _ _ Ho Hctx [] empty
    identity_type_substitution gamma identity_type_substitution_closed
    Hgamma Htw Hgt) as Hinst.
  unfold gamma in Hinst.
  rewrite instantiate_open_fix_body in Hinst;
    try tauto; try apply identity_type_substitution_closed;
    try apply identity_term_substitution_closed;
    try solve [eapply typing_lc; eauto].
  rewrite instantiate_identity, instantiate_ty_identity in Hinst. exact Hinst.
Qed.

Theorem core_preservation : forall t t' T,
  has_type [] empty t T ->
  t --> t' ->
  has_type [] empty t' T.
Proof.
  intros t t' T Hty Hstep.
  remember (@nil atom) as Delta eqn:EDelta.
  remember empty as Gamma eqn:EGamma.
  generalize dependent t'.
  induction Hty; intros t' Hstep; subst; inversion Hstep; subst.
  - inversion Hty1; subst. eapply term_beta_typing; eauto.
  - eapply T_App; eauto.
  - eapply T_App; eauto.
  - inversion Hty1; subst. eapply fix_beta_typing; eauto.
  - inversion Hty; subst. eapply type_beta_typing; eauto.
  - eapply T_TApp; eauto.
  - apply T_Div; eauto.
  - apply T_Div; eauto.
  - apply T_Int.
  - apply T_Arith; eauto.
  - apply T_Arith; eauto.
  - apply T_Int.
  - apply T_IfZero; eauto.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - eapply T_If; eauto.
  - assumption.
  - assumption.
Qed.

Lemma multi_preservation : forall t t' T,
  has_type [] empty t T ->
  multi t t' ->
  has_type [] empty t' T.
Proof.
  intros t t' T Hty Hmulti. induction Hmulti.
  - exact Hty.
  - apply IHHmulti. eapply core_preservation; eauto.
Qed.

Lemma multi_trans : forall t u v,
  multi t u -> multi u v -> multi t v.
Proof. intros t u v H. induction H; eauto using multi. Qed.

Lemma must_terminate_value : forall v, value v -> must_terminate v.
Proof.
  intros v Hv. constructor; [left; assumption |].
  intros u Hs. exfalso. eapply value_no_step; eauto.
Qed.

Lemma must_terminate_step : forall t u,
  must_terminate t -> t --> u -> must_terminate u.
Proof. intros t u H Hs. inversion H; eauto. Qed.

Lemma must_terminate_multi : forall t u,
  multi t u -> must_terminate t -> must_terminate u.
Proof.
  intros t u H. induction H; intros; eauto using must_terminate_step.
Qed.

Lemma must_terminate_progress : forall t,
  must_terminate t -> value t \/ exists u, t --> u.
Proof. intros t H; inversion H; assumption. Qed.

Lemma must_terminate_halts : forall t, must_terminate t -> halts t.
Proof.
  intros t H. induction H as [t Hp Hnext IH].
  destruct Hp as [Hv | [u Hs]].
  - exists t. split; [constructor | assumption].
  - destruct (IH u Hs) as [v [Hm Hv]].
    exists v. split; [eapply multi_step; eauto | assumption].
Qed.

End SystemFRefinementIfNonDeterminismRecursionEvaluation.

From Stdlib Require Import Arith.PeanoNat Lists.List Lia Program.Wf.
From Equations Require Import Equations.
Module SystemFRefinementIfNonDeterminismRecursionDenotations.
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

Lemma rty_size_open_tm_rec : forall R k u,
  rty_size (open_rty_tm_rec k u R) = rty_size R.
Proof.
  induction R; intros; simpl; rewrite ?IHR1, ?IHR2, ?IHR; reflexivity.
Qed.

Lemma rty_size_open_tm : forall R u,
  rty_size (open_rty_tm R u) = rty_size R.
Proof.
  intros. apply rty_size_open_tm_rec.
Qed.

Lemma rty_size_open_ty_rec : forall R k U,
  rty_size (open_rty_ty_rec k U R) = rty_size R.
Proof.
  induction R; intros; simpl; rewrite ?IHR1, ?IHR2, ?IHR; reflexivity.
Qed.

Lemma rty_size_open_ty : forall R U,
  rty_size (open_rty_ty R U) = rty_size R.
Proof.
  intros. apply rty_size_open_ty_rec.
Qed.

Lemma erase_instantiate_rty : forall theta gamma R,
  erase (instantiate_rty theta gamma R) = instantiate_ty theta (erase R).
Proof.
  induction R; intros; simpl; rewrite ?IHR1, ?IHR2, ?IHR; reflexivity.
Qed.

Lemma instantiate_pred_open_tm_rec : forall p k theta gamma x u,
  ~ In x (fv_pred p) ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  instantiate_pred theta (term_subst_update gamma x u)
    (open_pred_tm_rec k (tm_fvar x) p) =
  open_pred_tm_rec k u (instantiate_pred theta gamma p).
Proof.
  induction p; intros; simpl in *; try reflexivity;
    try solve [rewrite in_app_iff in H; rewrite !instantiate_open_tm_rec; intuition];
    try solve [rewrite in_app_iff in H; rewrite IHp1, IHp2; intuition].
  f_equal. apply IHp; assumption.
Qed.

Lemma instantiate_qualifier_open_tm_rec : forall ps k theta gamma x u,
  ~ In x (fv_qualifier ps) ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  instantiate_qualifier theta (term_subst_update gamma x u)
    (open_qualifier_tm_rec k (tm_fvar x) ps) =
  open_qualifier_tm_rec k u (instantiate_qualifier theta gamma ps).
Proof.
  exact instantiate_pred_open_tm_rec.
Qed.

Lemma instantiate_rty_open_tm_rec : forall R k theta gamma x u,
  ~ In x (fv_rty R) ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  instantiate_rty theta (term_subst_update gamma x u)
    (open_rty_tm_rec k (tm_fvar x) R) =
  open_rty_tm_rec k u (instantiate_rty theta gamma R).
Proof.
  induction R; intros; simpl in *.
  - f_equal. apply instantiate_qualifier_open_tm_rec; assumption.
  - rewrite in_app_iff in H.
    rewrite IHR1, IHR2; intuition.
  - rewrite in_app_iff in H.
    rewrite IHR1, IHR2; intuition.
  - f_equal. apply IHR; assumption.
Qed.

Lemma instantiate_rty_open_tm : forall R theta gamma x u,
  ~ In x (fv_rty R) ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  instantiate_rty theta (term_subst_update gamma x u)
    (open_rty_tm R (tm_fvar x)) =
  open_rty_tm (instantiate_rty theta gamma R) u.
Proof.
  intros. unfold open_rty_tm.
  apply instantiate_rty_open_tm_rec; assumption.
Qed.

Lemma instantiate_pred_open_ty_rec : forall p k theta gamma X U,
  ~ In X (ftv_pred p) ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_ty U ->
  instantiate_pred (type_subst_update theta X U) gamma
    (open_pred_ty_rec k (Ty_FVar X) p) =
  open_pred_ty_rec k U (instantiate_pred theta gamma p).
Proof.
  induction p; intros; simpl in *; try reflexivity;
    try solve [rewrite in_app_iff in H; rewrite !instantiate_open_ty_rec; intuition];
    try solve [rewrite in_app_iff in H; rewrite IHp1, IHp2; intuition].
  f_equal. apply IHp; assumption.
Qed.

Lemma instantiate_qualifier_open_ty_rec : forall ps k theta gamma X U,
  ~ In X (ftv_qualifier ps) ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_ty U ->
  instantiate_qualifier (type_subst_update theta X U) gamma
    (open_qualifier_ty_rec k (Ty_FVar X) ps) =
  open_qualifier_ty_rec k U (instantiate_qualifier theta gamma ps).
Proof.
  exact instantiate_pred_open_ty_rec.
Qed.

Lemma instantiate_rty_open_ty_rec : forall R k theta gamma X U,
  ~ In X (ftv_rty R) ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_ty U ->
  instantiate_rty (type_subst_update theta X U) gamma
    (open_rty_ty_rec k (Ty_FVar X) R) =
  open_rty_ty_rec k U (instantiate_rty theta gamma R).
Proof.
  induction R; intros; simpl in *.
  - rewrite in_app_iff in H.
    f_equal.
    + apply instantiate_ty_open_rec; intuition.
    + apply instantiate_qualifier_open_ty_rec; intuition.
  - rewrite in_app_iff in H.
    rewrite IHR1, IHR2; intuition.
  - rewrite in_app_iff in H.
    rewrite IHR1, IHR2; intuition.
  - f_equal. apply IHR; assumption.
Qed.

Lemma instantiate_rty_open_ty : forall R theta gamma X U,
  ~ In X (ftv_rty R) ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_ty U ->
  instantiate_rty (type_subst_update theta X U) gamma
    (open_rty_ty R (Ty_FVar X)) =
  open_rty_ty (instantiate_rty theta gamma R) U.
Proof.
  intros. unfold open_rty_ty.
  apply instantiate_rty_open_ty_rec; assumption.
Qed.

Lemma instantiate_term_update_irrelevant : forall t theta gamma x u,
  ~ In x (fv_tm t) ->
  instantiate theta (term_subst_update gamma x u) t =
  instantiate theta gamma t.
Proof.
  induction t; intros; simpl in *; try reflexivity.
  - unfold term_subst_update.
    rewrite (proj2 (Nat.eqb_neq x a)); [reflexivity | intuition].
  - f_equal. apply IHt. exact H.
  - rewrite in_app_iff in H. f_equal; [apply IHt1 | apply IHt2]; intuition.
  - f_equal. apply IHt. exact H.
  - f_equal. apply IHt. exact H.
  - rewrite in_app_iff in H. f_equal; [apply IHt1 | apply IHt2]; intuition.
  - rewrite in_app_iff in H. f_equal; [apply IHt1 | apply IHt2]; intuition.
  - rewrite in_app_iff in H. f_equal; [apply IHt1 | apply IHt2]; intuition.
  - repeat rewrite in_app_iff in H. f_equal; [apply IHt1 | apply IHt2 | apply IHt3]; intuition.
  - rewrite in_app_iff in H. f_equal; [apply IHt1 |apply IHt2]; intuition.
  - repeat rewrite in_app_iff in H. rewrite IHt1, IHt2, IHt3; intuition.
Qed.

Lemma instantiate_rty_term_update_irrelevant : forall R theta gamma x u,
  ~ In x (fv_rty R) ->
  instantiate_rty theta (term_subst_update gamma x u) R =
  instantiate_rty theta gamma R.
Proof.
  induction R as [T ps | R1 IHR1 R2 IHR2 | R1 IHR1 R2 IHR2 | R IHR];
    intros; simpl in *.
  - f_equal. induction ps; simpl in *; try reflexivity;
      try solve [rewrite in_app_iff in H; f_equal; apply instantiate_term_update_irrelevant; intuition];
      try solve [rewrite in_app_iff in H; f_equal; [apply IHps1|apply IHps2]; intuition].
    f_equal. apply IHps. exact H.
  - rewrite in_app_iff in H. f_equal; [apply IHR1|apply IHR2]; intuition.
  - rewrite in_app_iff in H. f_equal; [apply IHR1|apply IHR2]; intuition.
  - f_equal. apply IHR. exact H.
Qed.

Lemma instantiate_term_type_update_irrelevant : forall t theta gamma X U,
  ~ In X (ftv_tm t) ->
  instantiate (type_subst_update theta X U) gamma t =
  instantiate theta gamma t.
Proof.
  induction t; intros; simpl in *; try reflexivity.
  - rewrite in_app_iff in H. f_equal.
    + apply instantiate_ty_update_irrelevant. tauto.
    + apply IHt. tauto.
  - rewrite in_app_iff in H. f_equal; [apply IHt1 | apply IHt2]; tauto.
  - f_equal. apply IHt. exact H.
  - rewrite in_app_iff in H. f_equal.
    + apply IHt. tauto.
    + apply instantiate_ty_update_irrelevant. tauto.
  - rewrite in_app_iff in H. f_equal; [apply IHt1 | apply IHt2]; intuition.
  - rewrite in_app_iff in H. f_equal; [apply IHt1 | apply IHt2]; intuition.
  - repeat rewrite in_app_iff in H. f_equal;
      [apply instantiate_ty_update_irrelevant | apply instantiate_ty_update_irrelevant | apply IHt1 | apply IHt2]; tauto.
  - repeat rewrite in_app_iff in H. f_equal; [apply IHt1 | apply IHt2 | apply IHt3]; tauto.
  - rewrite in_app_iff in H. f_equal; [apply IHt1 |apply IHt2]; intuition.
  - repeat rewrite in_app_iff in H. rewrite IHt1, IHt2, IHt3; intuition.
Qed.

Lemma instantiate_rty_type_update_irrelevant : forall R theta gamma X U,
  ~ In X (ftv_rty R) ->
  instantiate_rty (type_subst_update theta X U) gamma R =
  instantiate_rty theta gamma R.
Proof.
  induction R as [T ps | R1 IHR1 R2 IHR2 | R1 IHR1 R2 IHR2 | R IHR];
    intros; simpl in *.
  - rewrite in_app_iff in H. f_equal.
    + apply instantiate_ty_update_irrelevant. intuition.
    + assert (HF : ~ In X (ftv_pred ps)) by intuition.
      clear H. rename HF into H.
      induction ps; simpl in *; try reflexivity;
        try solve [rewrite in_app_iff in H; f_equal; apply instantiate_term_type_update_irrelevant; intuition];
        try solve [rewrite in_app_iff in H; f_equal; [apply IHps1|apply IHps2]; intuition].
      f_equal. apply IHps. exact H.
  - rewrite in_app_iff in H. f_equal; [apply IHR1|apply IHR2]; intuition.
  - rewrite in_app_iff in H. f_equal; [apply IHR1|apply IHR2]; intuition.
  - f_equal. apply IHR. exact H.
Qed.

Lemma instantiate_open_tm_rec_commute : forall t k u theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  instantiate theta gamma (open_tm_rec k u t) =
  open_tm_rec k (instantiate theta gamma u) (instantiate theta gamma t).
Proof.
  induction t; intros; simpl; try reflexivity.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. apply open_tm_rec_lc_at with (K := 0).
    eapply lc_tm_at_monotone; [apply H0 | lia | lia].
  - f_equal. apply IHt; assumption.
  - f_equal; [apply IHt1 | apply IHt2]; assumption.
  - f_equal. apply IHt; assumption.
  - f_equal. apply IHt; assumption.
  - f_equal; [apply IHt1 | apply IHt2]; assumption.
  - f_equal; [apply IHt1 | apply IHt2]; assumption.
  - f_equal; [apply IHt1 | apply IHt2]; assumption.
  - f_equal; [apply IHt1 | apply IHt2 | apply IHt3]; assumption.
  - f_equal; [apply IHt1 |apply IHt2]; assumption.
  - rewrite IHt1, IHt2, IHt3; auto.
Qed.

Lemma instantiate_open_tm_commute : forall t u theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  instantiate theta gamma (open_tm t u) =
  open_tm (instantiate theta gamma t) (instantiate theta gamma u).
Proof.
  intros. unfold open_tm. apply instantiate_open_tm_rec_commute; assumption.
Qed.

Lemma instantiate_pred_open_tm_commute : forall p k u theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  instantiate_pred theta gamma (open_pred_tm_rec k u p) =
  open_pred_tm_rec k (instantiate theta gamma u)
    (instantiate_pred theta gamma p).
Proof.
  induction p; intros; simpl; try reflexivity;
    try solve [rewrite !instantiate_open_tm_rec_commute; try assumption; reflexivity];
    try solve [rewrite IHp1, IHp2; try assumption; reflexivity].
  f_equal. apply IHp; assumption.
Qed.

Lemma instantiate_qualifier_open_tm_commute : forall ps k u theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  instantiate_qualifier theta gamma (open_qualifier_tm_rec k u ps) =
  open_qualifier_tm_rec k (instantiate theta gamma u)
    (instantiate_qualifier theta gamma ps).
Proof.
  exact instantiate_pred_open_tm_commute.
Qed.

Lemma instantiate_rty_open_tm_commute : forall R k u theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  instantiate_rty theta gamma (open_rty_tm_rec k u R) =
  open_rty_tm_rec k (instantiate theta gamma u)
    (instantiate_rty theta gamma R).
Proof.
  induction R; intros; simpl.
  - f_equal. apply instantiate_qualifier_open_tm_commute; assumption.
  - rewrite IHR1, IHR2; try assumption. reflexivity.
  - rewrite IHR1, IHR2; try assumption. reflexivity.
  - rewrite IHR; try assumption. reflexivity.
Qed.

Lemma instantiate_rty_open_tm_commute_top : forall R u theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  instantiate_rty theta gamma (open_rty_tm R u) =
  open_rty_tm (instantiate_rty theta gamma R) (instantiate theta gamma u).
Proof.
  intros. unfold open_rty_tm. apply instantiate_rty_open_tm_commute; assumption.
Qed.

Lemma instantiate_open_ty_tm_rec_commute : forall t k U theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_ty U ->
  instantiate theta gamma (open_tm_ty_rec k U t) =
  open_tm_ty_rec k (instantiate_ty theta U) (instantiate theta gamma t).
Proof.
  induction t; intros; simpl; try reflexivity.
  - symmetry. apply open_tm_ty_rec_lc_at with (k := 0).
    eapply lc_tm_at_monotone; [apply H0 | lia | lia].
  - f_equal.
    + apply instantiate_ty_open_rec_commute. exact H.
    + apply IHt; assumption.
  - f_equal; [apply IHt1 | apply IHt2]; assumption.
  - f_equal. apply IHt; assumption.
  - f_equal.
    + apply IHt; assumption.
    + apply instantiate_ty_open_rec_commute. exact H.
  - f_equal; [apply IHt1 | apply IHt2]; assumption.
  - f_equal; [apply IHt1 | apply IHt2]; assumption.
  - f_equal;
      [apply instantiate_ty_open_rec_commute | apply instantiate_ty_open_rec_commute | apply IHt1 | apply IHt2]; assumption.
  - f_equal; [apply IHt1 | apply IHt2 | apply IHt3]; assumption.
  - f_equal; [apply IHt1 |apply IHt2]; assumption.
  - rewrite IHt1, IHt2, IHt3; auto.
Qed.

Lemma instantiate_open_ty_tm_commute : forall t U theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_ty U ->
  instantiate theta gamma (open_tm_ty t U) =
  open_tm_ty (instantiate theta gamma t) (instantiate_ty theta U).
Proof.
  intros. unfold open_tm_ty.
  apply instantiate_open_ty_tm_rec_commute; assumption.
Qed.

Lemma instantiate_pred_open_ty_commute : forall p k U theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_ty U ->
  instantiate_pred theta gamma (open_pred_ty_rec k U p) =
  open_pred_ty_rec k (instantiate_ty theta U)
    (instantiate_pred theta gamma p).
Proof.
  induction p; intros; simpl; try reflexivity;
    try solve [rewrite !instantiate_open_ty_tm_rec_commute; try assumption; reflexivity];
    try solve [rewrite IHp1, IHp2; try assumption; reflexivity].
  f_equal. apply IHp; assumption.
Qed.

Lemma instantiate_qualifier_open_ty_commute : forall ps k U theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_ty U ->
  instantiate_qualifier theta gamma (open_qualifier_ty_rec k U ps) =
  open_qualifier_ty_rec k (instantiate_ty theta U)
    (instantiate_qualifier theta gamma ps).
Proof.
  exact instantiate_pred_open_ty_commute.
Qed.

Lemma instantiate_rty_open_ty_commute : forall R k U theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_ty U ->
  instantiate_rty theta gamma (open_rty_ty_rec k U R) =
  open_rty_ty_rec k (instantiate_ty theta U)
    (instantiate_rty theta gamma R).
Proof.
  induction R; intros; simpl.
  - rewrite instantiate_ty_open_rec_commute,
      instantiate_qualifier_open_ty_commute; try assumption. reflexivity.
  - rewrite IHR1, IHR2; try assumption. reflexivity.
  - rewrite IHR1, IHR2; try assumption. reflexivity.
  - rewrite IHR; try assumption. reflexivity.
Qed.

Lemma instantiate_rty_open_ty_commute_top : forall R U theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_ty U ->
  instantiate_rty theta gamma (open_rty_ty R U) =
  open_rty_ty (instantiate_rty theta gamma R) (instantiate_ty theta U).
Proof.
  intros. unfold open_rty_ty. apply instantiate_rty_open_ty_commute; assumption.
Qed.

Lemma instantiate_value : forall v theta gamma,
  value v ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  value (instantiate theta gamma v).
Proof.
  intros v theta gamma Hv Htheta Hgamma. inversion Hv; subst; simpl.
  - apply v_abs.
    change (locally_closed_tm (instantiate theta gamma (tm_abs T t))).
    apply instantiate_closed; assumption.
  - apply v_tabs.
    change (locally_closed_tm (instantiate theta gamma (tm_tabs t))).
    apply instantiate_closed; assumption.
  - apply v_int.
  - apply v_fix.
    change (locally_closed_tm (instantiate theta gamma (tm_fix A B metric body))).
    apply instantiate_closed; assumption.
  - apply v_true.
  - apply v_false.
Qed.

Lemma instantiate_step : forall t t' theta gamma,
  t --> t' ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  instantiate theta gamma t --> instantiate theta gamma t'.
Proof.
  intros t t' theta gamma Hstep Htheta Hgamma. induction Hstep; simpl.
  - rewrite instantiate_open_tm_commute; try assumption.
    + apply ST_AppAbs.
      * change (locally_closed_tm (instantiate theta gamma (tm_abs T t))).
        apply instantiate_closed; assumption.
      * apply instantiate_value; assumption.
    + apply value_regular. exact H0.
  - apply ST_App1.
    + apply IHHstep.
    + apply instantiate_closed; assumption.
  - apply ST_App2.
    + apply instantiate_value; assumption.
    + apply IHHstep.
  - rewrite instantiate_open_ty_tm_commute; try assumption.
    + apply ST_TAppTabs.
      * change (locally_closed_tm (instantiate theta gamma (tm_tabs t))).
        apply instantiate_closed; assumption.
      * apply instantiate_ty_closed; assumption.
  - apply ST_TApp.
    + apply IHHstep.
    + apply instantiate_ty_closed; assumption.
  - apply ST_Div1; [assumption|apply instantiate_closed; assumption].
  - apply ST_Div2; [apply instantiate_value; assumption|assumption].
  - apply ST_DivInt. assumption.
  - apply ST_Arith1; [assumption|apply instantiate_closed; assumption].
  - apply ST_Arith2; [apply instantiate_value; assumption|assumption].
  - apply ST_ArithInt.
  - unfold open_fix_body, open_tm.
    rewrite instantiate_open_tm_rec_commute.
    + rewrite instantiate_open_tm_rec_commute; try assumption.
      * apply ST_AppFix.
        -- change (locally_closed_tm (instantiate theta gamma (tm_fix A B metric body))).
           apply instantiate_closed; assumption.
        -- apply instantiate_value; assumption.
    + assumption.
    + assumption.
    + apply value_regular. assumption.
  - apply ST_IfZeroArg; [assumption | apply instantiate_closed; assumption | apply instantiate_closed; assumption].
  - apply ST_IfZero; apply instantiate_closed; assumption.
  - apply ST_IfNonzero; [assumption | apply instantiate_closed; assumption | apply instantiate_closed; assumption].
  - apply ST_ChoiceLeft; eauto using instantiate_closed.
  - apply ST_ChoiceRight; eauto using instantiate_closed.
  - apply ST_If; eauto using instantiate_closed.
  - apply ST_IfTrue; eauto using instantiate_closed.
  - apply ST_IfFalse; eauto using instantiate_closed.
Qed.

Lemma instantiate_predicate_multistep : forall t t' theta gamma,
  predicate_multistep t t' ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  predicate_multistep (instantiate theta gamma t)
    (instantiate theta gamma t').
Proof.
  intros t t' theta gamma Hmulti Htheta Hgamma. induction Hmulti.
  - apply PMS_Refl.
  - eapply PMS_Step.
    + eapply instantiate_step; eauto.
    + exact IHHmulti.
Qed.

Lemma instantiate_ty_no_free : forall T theta,
  fv_ty T = [] -> instantiate_ty theta T = T.
Proof.
  induction T; intros; simpl in *; try discriminate; try reflexivity.
  - apply app_eq_nil in H as [H1 H2]. rewrite IHT1, IHT2; auto.
  - rewrite IHT; auto.
Qed.

Lemma instantiate_no_free : forall t theta gamma,
  fv_tm t = [] -> ftv_tm t = [] -> instantiate theta gamma t = t.
Proof.
  induction t; intros; simpl in *; try discriminate; try reflexivity;
    repeat match goal with H : _ ++ _ = [] |- _ => apply app_eq_nil in H as [? ?] end;
    f_equal; eauto using instantiate_ty_no_free.
Qed.

Lemma instantiate_pred_closed : forall p theta gamma,
  predicate_closed p -> instantiate_pred theta gamma p = p.
Proof.
  induction p; intros; simpl in *; try reflexivity;
    try solve [decompose [and] H; f_equal; apply instantiate_no_free; assumption];
    try solve [destruct H; f_equal; auto].
  f_equal. apply IHp. assumption.
Qed.

Lemma instantiate_qualifier_holds : forall ps theta gamma,
  predicate_closed ps ->
  qualifier_holds ps ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  qualifier_holds (instantiate_qualifier theta gamma ps).
Proof.
  intros ps theta gamma Hclosed Hholds Htheta Hgamma.
  unfold instantiate_qualifier. rewrite instantiate_pred_closed by assumption.
  exact Hholds.
Qed.

Lemma instantiate_pred_open_rec_commute : forall p k u theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  instantiate_pred theta gamma (open_pred_tm_rec k u p) =
  open_pred_tm_rec k (instantiate theta gamma u)
    (instantiate_pred theta gamma p).
Proof.
  induction p; intros; simpl; try reflexivity;
    try solve [rewrite !instantiate_open_tm_rec_commute; try assumption; reflexivity];
    try solve [rewrite IHp1, IHp2; try assumption; reflexivity].
  f_equal. apply IHp; assumption.
Qed.

Lemma instantiate_qualifier_open_commute : forall ps u theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  instantiate_qualifier theta gamma (open_qualifier_tm ps u) =
  open_qualifier_tm (instantiate_qualifier theta gamma ps)
    (instantiate theta gamma u).
Proof.
  intros. apply instantiate_pred_open_rec_commute; assumption.
Qed.

Equations denotes (R : rty) (v : tm) : Prop by wf (rty_size R) lt :=
  denotes (R_Refine T ps) v :=

      value v /\
      has_type [] empty v T /\
      qualifier_holds (open_qualifier_tm ps v);
  denotes (R_Func R1 R2) v :=

      value v /\
      has_type [] empty v (erase (R_Func R1 R2)) /\
      forall arg,
        denotes R1 arg ->
        locally_closed_tm (tm_app v arg) /\
        must_terminate (tm_app v arg) /\
        forall result,
          multi (tm_app v arg) result ->
          value result ->
          denotes (open_rty_tm R2 arg) result;
  denotes (R_Exists R1 R2) v :=
      value v /\
      has_type [] empty v (erase (R_Exists R1 R2)) /\
      exists witness,
        denotes R1 witness /\
        denotes (open_rty_tm R2 witness) v;
  denotes (R_Poly R1) v :=
      value v /\
      has_type [] empty v (erase (R_Poly R1)) /\
      forall U,
        wf_ty [] U ->
        locally_closed_tm (tm_tapp v U) /\
        must_terminate (tm_tapp v U) /\
        forall result,
          multi (tm_tapp v U) result ->
          value result ->
          denotes (open_rty_ty R1 U) result.
Next Obligation.
  simpl. lia.
Qed.
Next Obligation.
  rewrite rty_size_open_tm. simpl. lia.
Qed.
Next Obligation.
  simpl. lia.
Qed.
Next Obligation.
  rewrite rty_size_open_tm. simpl. lia.
Qed.
Next Obligation.
  rewrite rty_size_open_ty. simpl. lia.
Qed.

Definition evals_denotes (R : rty) (t : tm) : Prop :=
  locally_closed_tm t /\
  must_terminate t /\
  forall v,
    multi t v ->
    value v ->
    denotes R v.

Lemma denotes_refine_iff : forall T ps v,
  denotes (R_Refine T ps) v <->
  value v /\ has_type [] empty v T /\
  qualifier_holds (open_qualifier_tm ps v).
Proof.
  intros. simp denotes. reflexivity.
Qed.

Lemma denotes_func_iff : forall R1 R2 v,
  denotes (R_Func R1 R2) v <->
  value v /\ has_type [] empty v (erase (R_Func R1 R2)) /\
  forall arg,
    denotes R1 arg ->
    locally_closed_tm (tm_app v arg) /\
    must_terminate (tm_app v arg) /\
    forall result,
      multi (tm_app v arg) result ->
      value result ->
      denotes (open_rty_tm R2 arg) result.
Proof.
  intros. simp denotes. reflexivity.
Qed.

Lemma denotes_exists_iff : forall R1 R2 v,
  denotes (R_Exists R1 R2) v <->
  value v /\ has_type [] empty v (erase (R_Exists R1 R2)) /\
  exists witness,
    denotes R1 witness /\ denotes (open_rty_tm R2 witness) v.
Proof.
  intros. simp denotes. reflexivity.
Qed.

Lemma denotes_poly_iff : forall R v,
  denotes (R_Poly R) v <->
  value v /\ has_type [] empty v (erase (R_Poly R)) /\
  forall U,
    wf_ty [] U ->
    locally_closed_tm (tm_tapp v U) /\
    must_terminate (tm_tapp v U) /\
    forall result,
      multi (tm_tapp v U) result ->
      value result ->
      denotes (open_rty_ty R U) result.
Proof.
  intros. simp denotes. reflexivity.
Qed.

Lemma denotes_value : forall R v,
  denotes R v -> value v.
Proof.
  intros R v H.
  destruct R; cbn [denotes] in H; exact (proj1 H).
Qed.

Lemma denotes_refinement_predicates : forall T ps v,
  denotes (R_Refine T ps) v ->
  qualifier_holds (open_qualifier_tm ps v).
Proof.
  intros T ps v H.
  cbn [denotes] in H.
  exact (proj2 (proj2 H)).
Qed.

Lemma instantiate_pred_identity : forall p,
  instantiate_pred identity_type_substitution identity_term_substitution p = p.
Proof.
  induction p; simpl; rewrite ?instantiate_identity, ?IHp1, ?IHp2, ?IHp; reflexivity.
Qed.

Lemma instantiate_qualifier_identity : forall ps,
  instantiate_qualifier identity_type_substitution identity_term_substitution ps = ps.
Proof.
  exact instantiate_pred_identity.
Qed.

Lemma instantiate_rty_identity : forall R,
  instantiate_rty identity_type_substitution identity_term_substitution R = R.
Proof.
  induction R; simpl.
  - rewrite instantiate_ty_identity, instantiate_qualifier_identity. reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR. reflexivity.
Qed.

End SystemFRefinementIfNonDeterminismRecursionDenotations.

From Stdlib Require Import Arith.Wf_nat ZArith.ZArith Lia.

Module SystemFRefinementIfNonDeterminismRecursionTermination.

Definition integer_decreases (next current : Z) : Prop :=
  (0 <= next /\ next < current)%Z.

Lemma integer_decreases_wf : well_founded integer_decreases.
Proof.
  apply (well_founded_lt_compat Z Z.to_nat integer_decreases).
  intros next current [Hnonneg Hlt].
  apply (proj1 (Z2Nat.inj_lt next current Hnonneg ltac:(lia))).
  exact Hlt.
Qed.

End SystemFRefinementIfNonDeterminismRecursionTermination.

From Stdlib Require Import Arith.PeanoNat Arith.Wf_nat Lists.List Lia ZArith.ZArith.
Module SystemFRefinementIfNonDeterminismRecursionSoundness.
Import ListNotations.
Import SystemFRefinementIfNonDeterminismRecursion.
Import SystemFRefinementIfNonDeterminismRecursionInfrastructure.
Import SystemFRefinementIfNonDeterminismRecursionCoreTyping.
Import SystemFRefinementIfNonDeterminismRecursionTyping.
Import SystemFRefinementIfNonDeterminismRecursionEvaluation.
Import SystemFRefinementIfNonDeterminismRecursionDenotations.
Import SystemFRefinementIfNonDeterminismRecursionTermination.

Record related_substitution
    (theta : type_substitution) (gamma : term_substitution)
    (RGamma : rcontext) : Prop := {
  substitution_values : forall x, value (gamma x);
  substitution_lookup : forall x R,
    lookup_rcontext x RGamma = Some R ->
    denotes (instantiate_rty theta gamma R) (gamma x)
}.
Arguments substitution_values {theta gamma RGamma} _ _.
Arguments substitution_lookup {theta gamma RGamma} _ _ _ _.
Coercion substitution_lookup : related_substitution >-> Funclass.

Lemma denotes_typing : forall R v,
  denotes R v -> has_type [] empty v (erase R).
Proof.
  intros R v H. destruct R; cbn [denotes] in H; exact (proj1 (proj2 H)).
Qed.

Lemma evals_denotes_of_denotes : forall R v,
  denotes R v -> evals_denotes R v.
Proof.
  intros R v Hden. split.
  - apply value_regular. eapply denotes_value. exact Hden.
  - split.
    + apply must_terminate_value. eapply denotes_value. exact Hden.
    + intros result Hsteps Hvalue.
      assert (Hv : value v) by (eapply denotes_value; exact Hden).
      assert (result = v).
      { exact (value_multi_eq v result Hv Hsteps). }
      subst result. exact Hden.
Qed.

Lemma evals_denotes_from_value : forall R v,
  value v -> evals_denotes R v -> denotes R v.
Proof.
  intros R v Hv [_ [_ Hall]].
  apply (Hall v (multi_refl v) Hv).
Qed.

Lemma core_multi_preservation : forall t v T,
  has_type [] empty t T ->
  multi t v ->
  has_type [] empty v T.
Proof.
  intros t v T Htyped Hsteps. induction Hsteps.
  - exact Htyped.
  - apply IHHsteps. eapply core_preservation; eauto.
Qed.

Lemma lookup_erase_context_inv : forall RGamma x T,
  lookup_context x (erase_context RGamma) = Some T ->
  exists R,
    lookup_rcontext x RGamma = Some R /\ erase R = T.
Proof.
  induction RGamma as [|[y R] RGamma IH]; intros x T Hlookup; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + inversion Hlookup; subst. exists R. split; reflexivity.
    + destruct (IH x T Hlookup) as [S [HS HE]].
      exists S. split; assumption.
Qed.

Lemma related_substitution_typed : forall theta gamma RGamma,
  related_substitution theta gamma RGamma ->
  term_substitution_typed (erase_context RGamma) [] empty theta gamma.
Proof.
  intros theta gamma RGamma Hrel x T Hlookup.
  destruct (lookup_erase_context_inv RGamma x T Hlookup)
    as [R [HR Herase]].
  pose proof (denotes_typing _ _ (Hrel x R HR)) as Htyped.
  rewrite erase_instantiate_rty in Htyped.
  rewrite Herase in Htyped. exact Htyped.
Qed.

Lemma lookup_rcontext_fv : forall RGamma y R x,
  lookup_rcontext y RGamma = Some R ->
  In x (fv_rty R) ->
  In x (fv_rcontext RGamma).
Proof.
  induction RGamma as [|[z S] RGamma IH]; intros y R x Hlookup Hin; simpl in *.
  - discriminate.
  - destruct (Nat.eqb y z) eqn:E.
    + inversion Hlookup; subst. apply in_or_app. left. exact Hin.
    + apply in_or_app. right. eapply IH; eauto.
Qed.

Lemma lookup_rcontext_ftv : forall RGamma y R X,
  lookup_rcontext y RGamma = Some R ->
  In X (ftv_rty R) ->
  In X (ftv_rcontext RGamma).
Proof.
  induction RGamma as [|[z S] RGamma IH]; intros y R X Hlookup Hin; simpl in *.
  - discriminate.
  - destruct (Nat.eqb y z) eqn:E.
    + inversion Hlookup; subst. apply in_or_app. left. exact Hin.
    + apply in_or_app. right. eapply IH; eauto.
Qed.

Lemma related_substitution_update : forall theta gamma RGamma x R v,
  related_substitution theta gamma RGamma ->
  denotes (instantiate_rty theta gamma R) v ->
  ~ In x (fv_rty R) ->
  ~ In x (fv_rcontext RGamma) ->
  related_substitution theta (term_subst_update gamma x v)
    (update_rcontext RGamma x R).
Proof.
  intros theta gamma RGamma x R v Hrel Hden HfreshR HfreshGamma.
  constructor.
  { intro y. unfold term_subst_update. destruct (Nat.eqb x y).
    - eapply denotes_value; exact Hden.
    - exact (substitution_values Hrel y). }
  intros y S Hlookup. simpl in Hlookup.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst y. inversion Hlookup; subst S.
    rewrite instantiate_rty_term_update_irrelevant by exact HfreshR.
    unfold term_subst_update. rewrite Nat.eqb_refl.
    exact Hden.
  - apply Nat.eqb_neq in E.
    assert (HlookupS : lookup_rcontext y RGamma = Some S) by exact Hlookup.
    assert (HfreshS : ~ In x (fv_rty S)).
    { intro Hin. apply HfreshGamma. eapply lookup_rcontext_fv; eauto. }
    rewrite instantiate_rty_term_update_irrelevant by exact HfreshS.
    unfold term_subst_update.
    rewrite (proj2 (Nat.eqb_neq x y)) by congruence.
    exact (Hrel y S HlookupS).
Qed.

Lemma related_substitution_type_update : forall theta gamma RGamma X U,
  related_substitution theta gamma RGamma ->
  ~ In X (ftv_rcontext RGamma) ->
  related_substitution (type_subst_update theta X U) gamma RGamma.
Proof.
  intros theta gamma RGamma X U Hrel Hfresh.
  constructor; [exact (substitution_values Hrel) |].
  intros x R Hlookup.
  rewrite instantiate_rty_type_update_irrelevant.
  - exact (Hrel x R Hlookup).
  - intro Hin. apply Hfresh. eapply lookup_rcontext_ftv; eauto.
Qed.

Lemma entails_sound : forall Delta RGamma ps qs,
  entails Delta RGamma ps qs ->
  forall theta gamma,
    type_substitution_closed theta ->
    term_substitution_closed gamma ->
    related_substitution theta gamma RGamma ->
    qualifier_holds (instantiate_qualifier theta gamma ps) ->
    qualifier_holds (instantiate_qualifier theta gamma qs).
Proof.
  intros Delta RGamma ps qs Hentails. induction Hentails;
    intros theta gamma Htheta Hgamma Hrel Hholds;
    cbn [instantiate_qualifier instantiate_pred qualifier_holds predicate_holds interpret_qualifier] in *;
    repeat match goal with
    | IH : forall theta gamma, type_substitution_closed theta ->
        term_substitution_closed gamma -> related_substitution theta gamma _ -> _ |- _ =>
        specialize (IH theta gamma Htheta Hgamma Hrel)
    end; try tauto.
  - pose proof (Hrel x (R_Refine T p) H) as Hd.
  apply denotes_refine_iff in Hd. destruct Hd as [Hv [Ht Hp]].
  unfold open_qualifier_tm, open_qualifier_tm_rec.
  unfold qualifier_holds, instantiate_qualifier.
  rewrite (instantiate_pred_open_tm_commute p 0 (tm_fvar x) theta gamma
    Htheta Hgamma (lc_tm_fvar 0 0 x)).
  exact Hp.
  - apply H.
    + exact (substitution_values Hrel).
    + intros x T q0 Hlookup.
      pose proof (Hrel x (R_Refine T q0) Hlookup) as Hd.
      apply denotes_refine_iff in Hd. destruct Hd as [_ [_ Hp]].
      change (qualifier_holds (instantiate_qualifier theta gamma (open_qualifier_tm q0 (tm_fvar x)))).
      rewrite instantiate_qualifier_open_commute.
      * exact Hp.
      * exact Htheta.
      * exact Hgamma.
      * apply lc_tm_fvar.
    + exact Hholds.
Qed.

Scheme has_rtype_mut_ind := Induction for has_rtype Sort Prop
with subtype_mut_ind := Induction for subtype Sort Prop.

Combined Scheme refinement_typing_mutind
  from has_rtype_mut_ind, subtype_mut_ind.

Lemma multi_app_left : forall t1 t1' t2,
  multi t1 t1' -> locally_closed_tm t2 ->
  multi (tm_app t1 t2) (tm_app t1' t2).
Proof.
  intros t1 t1' t2 Hsteps Hlc. induction Hsteps.
  - apply multi_refl.
  - eapply multi_step.
    + apply ST_App1; eauto.
    + exact IHHsteps.
Qed.

Lemma multi_app_right : forall v1 t2 t2',
  value v1 -> multi t2 t2' ->
  multi (tm_app v1 t2) (tm_app v1 t2').
Proof.
  intros v1 t2 t2' Hv Hsteps. induction Hsteps.
  - apply multi_refl.
  - eapply multi_step.
    + apply ST_App2; eauto.
    + exact IHHsteps.
Qed.

Lemma multi_tapp : forall t t' U,
  multi t t' -> locally_closed_ty U ->
  multi (tm_tapp t U) (tm_tapp t' U).
Proof.
  intros t t' U Hsteps HU. induction Hsteps.
  - apply multi_refl.
  - eapply multi_step.
    + apply ST_TApp; eauto.
    + exact IHHsteps.
Qed.

Lemma multi_trans : forall t1 t2 t3,
  multi t1 t2 -> multi t2 t3 -> multi t1 t3.
Proof.
  intros t1 t2 t3 H12 H23. induction H12.
  - exact H23.
  - eapply multi_step; eauto.
Qed.

Lemma evals_denotes_intro : forall R t,
  locally_closed_tm t ->
  (value t \/ exists u, t --> u) ->
  (value t -> denotes R t) ->
  (forall u, t --> u -> evals_denotes R u) ->
  evals_denotes R t.
Proof.
  intros R t Hlc Hp Hv Hnext. split; [assumption |]. split.
  - constructor; [assumption |].
    intros u Hs. exact (proj1 (proj2 (Hnext u Hs))).
  - intros v Hm Hvalue. inversion Hm; subst.
    + apply Hv; assumption.
    + match goal with
      | Hs : t --> ?u, Hrest : multi ?u v |- _ =>
          exact (proj2 (proj2 (Hnext u Hs)) v Hrest Hvalue)
      end.
Qed.

Lemma evals_denotes_map : forall R S t,
  (forall v, denotes R v -> denotes S v) ->
  evals_denotes R t -> evals_denotes S t.
Proof.
  intros R S t Hmap [Hlc [Htotal Hall]].
  split; [assumption |]. split; [assumption |].
  intros v Hm Hv. apply Hmap. apply Hall; assumption.
Qed.

Lemma evals_denotes_reduct : forall R t u,
  evals_denotes R t -> t --> u -> evals_denotes R u.
Proof.
  intros R t u [Hlc [Htotal Hall]] Hs. split.
  - eapply step_preserves_lc; eauto.
  - split; [eapply must_terminate_step; eauto |].
    intros v Hm Hv. apply Hall; [eapply multi_step; eauto |assumption].
Qed.

Lemma evals_denotes_single : forall R t u,
  locally_closed_tm t ->
  t --> u ->
  (forall w, t --> w -> w = u) ->
  evals_denotes R u ->
  evals_denotes R t.
Proof.
  intros R t u Hlc Hs Hunique Hu. apply evals_denotes_intro.
  - exact Hlc.
  - right. eauto.
  - intros Hv. exfalso. eapply value_no_step; eauto.
  - intros w Hw. rewrite (Hunique w Hw). exact Hu.
Qed.

Lemma evals_denotes_bind : forall S R t (E : tm -> tm),
  evals_denotes S t ->
  (forall u, locally_closed_tm u -> locally_closed_tm (E u)) ->
  (forall u, ~ value (E u)) ->
  (forall u u', u --> u' -> E u --> E u') ->
  (forall u w, ~ value u -> E u --> w ->
    exists u', u --> u' /\ w = E u') ->
  (forall v, multi t v -> value v -> denotes S v -> evals_denotes R (E v)) ->
  evals_denotes R (E t).
Proof.
  intros S R t E [Hlc [Htotal Hall]] HElc HEnval HEstep HEinv.
  revert Hlc Hall.
  induction Htotal as [t Hp Hnext IH]; intros Hlc Hall Hcont.
  destruct Hp as [Hv | [u Hs]].
  - apply Hcont; [constructor |assumption |apply Hall; [constructor |assumption]].
  - apply evals_denotes_intro.
    + apply HElc; assumption.
    + right. exists (E u). apply HEstep; assumption.
    + intros Hv. exfalso. exact (HEnval t Hv).
    + intros w Hw.
      assert (Hnv : ~ value t) by (intro Hv; eapply value_no_step; eauto).
      destruct (HEinv t w Hnv Hw) as [u' [Hs' ->]].
      apply (IH u' Hs').
      * eapply step_preserves_lc; eauto.
      * intros v Hm Hv. apply Hall; [eapply multi_step; eauto |assumption].
      * intros v Hm Hv Hd. apply Hcont; [eapply multi_step; eauto |assumption |assumption].
Qed.

Lemma evals_denotes_app_exists : forall R1 R2 t1 t2,
  evals_denotes (R_Func R1 R2) t1 ->
  evals_denotes R1 t2 ->
  evals_denotes (R_Exists R1 R2) (tm_app t1 t2).
Proof.
  intros R1 R2 t1 t2 Hfun Harg.
  eapply evals_denotes_bind with (S := R_Func R1 R2) (E := fun u => tm_app u t2).
  - exact Hfun.
  - intros; apply lc_tm_app; [assumption |exact (proj1 Harg)].
  - intros u Hv; inversion Hv.
  - intros; apply ST_App1; [assumption |exact (proj1 Harg)].
  - intros u w Hnv Hs. inversion Hs; subst.
    + exfalso. apply Hnv. constructor; assumption.
    + eauto.
    + contradiction.
    + exfalso. apply Hnv. constructor; assumption.
  - intros f Htf Hvf Hdf.
    eapply evals_denotes_bind with (S := R1) (E := fun u => tm_app f u).
    + exact Harg.
    + intros; apply lc_tm_app; [apply value_regular; assumption |assumption].
    + intros u Hv; inversion Hv.
    + intros; apply ST_App2; assumption.
    + intros u w Hnv Hs. inversion Hs; subst.
      * contradiction.
      * exfalso. eapply value_no_step; eauto.
      * eauto.
      * contradiction.
    + intros arg Hta Hva Hda.
      apply denotes_func_iff in Hdf. destruct Hdf as [_ [_ Happ]].
      eapply evals_denotes_map; [|exact (Happ arg Hda)].
      intros result Hd. apply denotes_exists_iff.
      split; [eapply denotes_value; eauto |]. split.
      * pose proof (denotes_typing _ _ Hd) as Ht.
        rewrite erase_open_rty_tm in Ht. exact Ht.
      * exists arg. auto.
Qed.

Lemma evals_denotes_tapp : forall R t U,
  evals_denotes (R_Poly R) t -> wf_ty [] U ->
  evals_denotes (open_rty_ty R U) (tm_tapp t U).
Proof.
  intros R t U Ht HU.
  eapply evals_denotes_bind with (S := R_Poly R) (E := fun u => tm_tapp u U).
  - exact Ht.
  - intros; apply lc_tm_tapp; [assumption |eapply wf_ty_lc; eauto].
  - intros u Hv; inversion Hv.
  - intros; apply ST_TApp; [assumption |eapply wf_ty_lc; eauto].
  - intros u w Hnv Hs. inversion Hs; subst.
    + exfalso. apply Hnv. constructor; assumption.
    + eauto.
  - intros v Hm Hv Hd. apply denotes_poly_iff in Hd.
    destruct Hd as [_ [_ Happ]]. apply Happ; assumption.
Qed.

Lemma evals_denotes_choice : forall R t1 t2,
  evals_denotes R t1 -> evals_denotes R t2 ->
  evals_denotes R (tm_choice t1 t2).
Proof.
  intros R t1 t2 H1 H2. apply evals_denotes_intro.
  - apply lc_tm_choice; [exact (proj1 H1) |exact (proj1 H2)].
  - right. exists t1. apply ST_ChoiceLeft; [exact (proj1 H1) |exact (proj1 H2)].
  - intros Hv. inversion Hv.
  - intros u Hs. inversion Hs; subst; assumption.
Qed.

Lemma multi_div_left : forall t1 t1' t2,
  multi t1 t1' -> locally_closed_tm t2 ->
  multi (tm_div t1 t2) (tm_div t1' t2).
Proof.
  intros t1 t1' t2 H Hlc. induction H; eauto using multi, step.
Qed.

Lemma multi_div_right : forall v t2 t2',
  value v -> multi t2 t2' ->
  multi (tm_div v t2) (tm_div v t2').
Proof.
  intros v t2 t2' Hv H. induction H; eauto using multi, step.
Qed.

Lemma value_int_canonical : forall v,
  value v -> has_type [] empty v Ty_Int -> exists n, v = tm_int n.
Proof.
  intros v Hv Ht. inversion Hv; subst; inversion Ht; eauto.
Qed.

Lemma evals_denotes_div : forall t1 t2,
  evals_denotes (R_Refine Ty_Int Pred_True) t1 ->
  evals_denotes (R_Refine Ty_Int (Pred_Ne (tm_bvar 0) (tm_int 0%Z))) t2 ->
  evals_denotes (R_Refine Ty_Int (Pred_Eq (tm_bvar 0) (tm_div t1 t2))) (tm_div t1 t2).
Proof.
  intros t1 t2 H1 H2.
  eapply evals_denotes_bind with
    (S := R_Refine Ty_Int Pred_True) (E := fun u => tm_div u t2).
  - exact H1.
  - intros; apply lc_tm_div; [assumption |exact (proj1 H2)].
  - intros u Hv; inversion Hv.
  - intros; apply ST_Div1; [assumption |exact (proj1 H2)].
  - intros u w Hnv Hs. inversion Hs; subst; eauto;
      exfalso; apply Hnv; first [assumption |constructor].
  - intros v1 Hm1 Hv1 Hd1. apply denotes_refine_iff in Hd1.
    destruct Hd1 as [_ [Ht1 _]].
    destruct (value_int_canonical _ Hv1 Ht1) as [n ->].
    eapply evals_denotes_bind with
      (S := R_Refine Ty_Int (Pred_Ne (tm_bvar 0) (tm_int 0%Z)))
      (E := fun u => tm_div (tm_int n) u).
    + exact H2.
    + intros; apply lc_tm_div; [constructor |assumption].
    + intros u Hv; inversion Hv.
    + intros; apply ST_Div2; [constructor |assumption].
    + intros u w Hnv Hs. inversion Hs; subst; eauto;
        try match goal with Hs : step (tm_int _) _ |- _ => inversion Hs end;
        exfalso; apply Hnv; first [assumption |constructor].
    + intros v2 Hm2 Hv2 Hd2. apply denotes_refine_iff in Hd2.
      destruct Hd2 as [_ [Ht2 Hnz]].
      destruct (value_int_canonical _ Hv2 Ht2) as [m ->].
      assert (Em : m <> 0%Z).
      { intro E. subst m. apply Hnz.
        exists (tm_int 0%Z). repeat split; constructor. }
      eapply evals_denotes_single with (u := tm_int (Z.div n m)).
      * repeat constructor.
      * apply ST_DivInt; assumption.
      * intros w Hs. inversion Hs; subst; try reflexivity;
          match goal with Hs : step (tm_int _) _ |- _ => inversion Hs end.
      * apply evals_denotes_of_denotes. apply denotes_refine_iff.
        split; [constructor |]. split; [constructor |].
        unfold open_qualifier_tm, open_qualifier_tm_rec. simpl.
        rewrite (open_tm_rec_lc_at t1 0 0 (tm_int (Z.div n m)) (proj1 H1)),
          (open_tm_rec_lc_at t2 0 0 (tm_int (Z.div n m)) (proj1 H2)).
        exists (tm_int (Z.div n m)). split; [constructor |]. split; [|constructor].
        assert (Hm : multi (tm_div t1 t2) (tm_int (Z.div n m))).
        { eapply multi_trans; [apply multi_div_left; [exact Hm1 |exact (proj1 H2)] |].
          eapply multi_trans; [apply multi_div_right; eauto using value |].
          eapply multi_step; [apply ST_DivInt; assumption |constructor]. }
        induction Hm; eauto using predicate_multistep.
Qed.

Lemma multi_arith_left : forall op t1 t1' t2,
  multi t1 t1' -> locally_closed_tm t2 ->
  multi (tm_arith op t1 t2) (tm_arith op t1' t2).
Proof. intros op t1 t1' t2 H Hlc. induction H; eauto using multi, step. Qed.

Lemma multi_arith_right : forall op v t2 t2',
  value v -> multi t2 t2' ->
  multi (tm_arith op v t2) (tm_arith op v t2').
Proof. intros op v t2 t2' Hv H. induction H; eauto using multi, step. Qed.

Lemma evals_denotes_arith : forall op t1 t2,
  evals_denotes (R_Refine Ty_Int Pred_True) t1 ->
  evals_denotes (R_Refine Ty_Int Pred_True) t2 ->
  evals_denotes (R_Refine Ty_Int
    (Pred_Eq (tm_bvar 0) (tm_arith op t1 t2))) (tm_arith op t1 t2).
Proof.
  intros op t1 t2 H1 H2.
  eapply evals_denotes_bind with
    (S := R_Refine Ty_Int Pred_True) (E := fun u => tm_arith op u t2).
  - exact H1.
  - intros; apply lc_tm_arith; [assumption |exact (proj1 H2)].
  - intros u Hv; inversion Hv.
  - intros; apply ST_Arith1; [assumption |exact (proj1 H2)].
  - intros u w Hnv Hs. inversion Hs; subst; eauto;
      exfalso; apply Hnv; first [assumption |constructor].
  - intros v1 Hm1 Hv1 Hd1. apply denotes_refine_iff in Hd1.
    destruct Hd1 as [_ [Ht1 _]].
    destruct (value_int_canonical _ Hv1 Ht1) as [n ->].
    eapply evals_denotes_bind with
      (S := R_Refine Ty_Int Pred_True) (E := fun u => tm_arith op (tm_int n) u).
    + exact H2.
    + intros; apply lc_tm_arith; [constructor |assumption].
    + intros u Hv; inversion Hv.
    + intros; apply ST_Arith2; [constructor |assumption].
    + intros u w Hnv Hs. inversion Hs; subst; eauto;
        try match goal with Hs : step (tm_int _) _ |- _ => inversion Hs end;
        exfalso; apply Hnv; first [assumption |constructor].
    + intros v2 Hm2 Hv2 Hd2. apply denotes_refine_iff in Hd2.
      destruct Hd2 as [_ [Ht2 _]].
      destruct (value_int_canonical _ Hv2 Ht2) as [m ->].
      set (result := eval_integer_operator op n m).
      eapply evals_denotes_single with (u := tm_int result).
      * repeat constructor.
      * apply ST_ArithInt.
      * intros w Hs. inversion Hs; subst; try reflexivity;
          match goal with Hs : step (tm_int _) _ |- _ => inversion Hs end.
      * apply evals_denotes_of_denotes. apply denotes_refine_iff.
        split; [constructor |]. split; [constructor |].
        unfold open_qualifier_tm, open_qualifier_tm_rec. simpl.
        rewrite (open_tm_rec_lc_at t1 0 0 (tm_int result) (proj1 H1)),
          (open_tm_rec_lc_at t2 0 0 (tm_int result) (proj1 H2)).
        exists (tm_int result). split; [constructor |]. split; [|constructor].
        assert (Hm : multi (tm_arith op t1 t2) (tm_int result)).
        { eapply multi_trans; [apply multi_arith_left; [exact Hm1 |exact (proj1 H2)] |].
          eapply multi_trans; [apply multi_arith_right; eauto using value |].
          eapply multi_step; [apply ST_ArithInt |constructor]. }
        induction Hm; eauto using predicate_multistep.
Qed.

Lemma evals_denotes_if : forall R t1 t2 t3,
  evals_denotes (R_Refine Ty_Bool Pred_True) t1 ->
  evals_denotes R t2 -> evals_denotes R t3 ->
  evals_denotes R (tm_if t1 t2 t3).
Proof.
  intros R t1 t2 t3 H1 H2 H3.
  eapply evals_denotes_bind with (S := R_Refine Ty_Bool Pred_True)
    (E := fun u => tm_if u t2 t3).
  - exact H1.
  - intros; apply lc_tm_if; [assumption |exact (proj1 H2) |exact (proj1 H3)].
  - intros u Hv; inversion Hv.
  - intros; apply ST_If; [assumption |exact (proj1 H2) |exact (proj1 H3)].
  - intros u w Hnv Hs. inversion Hs; subst; eauto;
      exfalso; apply Hnv; constructor.
  - intros b Hm Hv Hd. apply denotes_refine_iff in Hd.
    destruct Hd as [_ [Ht _]].
    assert (E : b = tm_true \/ b = tm_false).
    { inversion Hv; subst; inversion Ht; auto. }
    destruct E; subst.
    + eapply evals_denotes_single with t2.
      * apply lc_tm_if; [constructor |exact (proj1 H2) |exact (proj1 H3)].
      * apply ST_IfTrue; [exact (proj1 H2) |exact (proj1 H3)].
      * intros w Hs. inversion Hs; subst; [|reflexivity].
        match goal with Hs : step tm_true _ |- _ => inversion Hs end.
      * exact H2.
    + eapply evals_denotes_single with t3.
      * apply lc_tm_if; [constructor |exact (proj1 H2) |exact (proj1 H3)].
      * apply ST_IfFalse; [exact (proj1 H2) |exact (proj1 H3)].
      * intros w Hs. inversion Hs; subst; [|reflexivity].
        match goal with Hs : step tm_false _ |- _ => inversion Hs end.
      * exact H3.
Qed.

Lemma instantiated_refinement_typing_erases : forall Delta RGamma t R theta gamma,
  has_rtype Delta RGamma t R ->
  context_wf Delta (erase_context RGamma) ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  type_substitution_wf Delta [] theta ->
  related_substitution theta gamma RGamma ->
  has_type [] empty (instantiate theta gamma t)
    (erase (instantiate_rty theta gamma R)).
Proof.
  intros Delta RGamma t R theta gamma Htyped Hctx Htheta Hgamma
    HthetaWf Hrelated.
  pose proof (refinement_typing_erases _ _ _ _ Htyped) as Herased.
  pose proof (has_type_instantiate Delta (erase_context RGamma) t (erase R)
    Herased Hctx [] empty theta gamma Htheta Hgamma HthetaWf
    (related_substitution_typed theta gamma RGamma Hrelated)) as Hinst.
  rewrite erase_instantiate_rty. exact Hinst.
Qed.

Definition typing_semantics
    (Delta : ty_context) (RGamma : rcontext) (t : tm) (R : rty) : Prop :=
  context_wf Delta (erase_context RGamma) ->
  forall theta gamma,
    type_substitution_closed theta ->
    term_substitution_closed gamma ->
    type_substitution_wf Delta [] theta ->
    related_substitution theta gamma RGamma ->
    evals_denotes (instantiate_rty theta gamma R)
      (instantiate theta gamma t).

Definition subtype_semantics
    (Delta : ty_context) (RGamma : rcontext) (R S : rty) : Prop :=
  wf_ty Delta (erase S) ->
  context_wf Delta (erase_context RGamma) ->
  forall theta gamma,
    type_substitution_closed theta ->
    term_substitution_closed gamma ->
    type_substitution_wf Delta [] theta ->
    related_substitution theta gamma RGamma ->
    forall v,
      denotes (instantiate_rty theta gamma R) v ->
      denotes (instantiate_rty theta gamma S) v.

Lemma predicate_multi_to_multi : forall t u,
  predicate_multistep t u -> multi t u.
Proof. intros t u H. induction H; eauto using multi. Qed.

Lemma nonnegative_metric_result : forall t,
  qualifier_holds (Pred_Ge t (tm_int 0%Z)) ->
  exists n : Z, predicate_multistep t (tm_int n) /\ (0 <= n)%Z.
Proof.
  intros t [z [n [Hz [Hn Hle]]]].
  assert (z = 0%Z).
  { pose proof (value_multi_eq _ _ (v_int 0) (predicate_multi_to_multi _ _ Hz)). congruence. }
  subst z. exists n. auto.
Qed.

Lemma measured_argument_metric : forall A p metric arg,
  denotes (measured_input A p metric) arg ->
  exists n : Z, predicate_multistep (open_tm metric arg) (tm_int n) /\ (0 <= n)%Z.
Proof.
  intros A p metric arg Hd.
  apply denotes_refine_iff in Hd. destruct Hd as [_ [_ [_ Hmetric]]].
  apply nonnegative_metric_result. exact Hmetric.
Qed.

Lemma smaller_argument_metric : forall A p metric current next n,
  locally_closed_tm current ->
  predicate_multistep current (tm_int n) ->
  denotes (smaller_input A p metric current) next ->
  denotes (measured_input A p metric) next /\
  exists m : Z,
    predicate_multistep (open_tm metric next) (tm_int m) /\
    (0 <= m)%Z /\ (m < n)%Z.
Proof.
  intros A p metric current next n Hlc Hcurrent Hd.
  apply denotes_refine_iff in Hd. destruct Hd as [Hv [Ht [Hp [Hge Hlt]]]].
  change (qualifier_holds
    (Pred_Lt (open_tm metric next) (open_tm_rec 0 next current))) in Hlt.
  rewrite (open_tm_rec_lc_at current 0 0 next Hlc) in Hlt.
  split.
  - apply denotes_refine_iff. repeat split; assumption.
  - destruct (nonnegative_metric_result _ Hge) as [m [Hm Hnonneg]].
    destruct Hlt as [a [b [Ha [Hb [Hab Hall]]]]].
    exists m. repeat split; try assumption. exact (Hall m n Hm Hcurrent).
Qed.

Lemma recursive_function_denotes : forall A B p metric body R2,
  has_type [] empty (tm_fix A B metric body) (Ty_Arrow A (erase R2)) ->
  (forall arg,
    denotes (measured_input A p metric) arg ->
    denotes (R_Func (smaller_input A p metric (open_tm metric arg)) R2)
      (tm_fix A B metric body) ->
    evals_denotes (open_rty_tm R2 arg)
      (open_fix_body body (tm_fix A B metric body) arg)) ->
  denotes (R_Func (measured_input A p metric) R2) (tm_fix A B metric body).
Proof.
  intros A B p metric body R2 Htyped Hbody.
  assert (Hfixlc : locally_closed_tm (tm_fix A B metric body)).
  { eapply typing_lc; eauto. }
  assert (Hmetriclc : lc_tm_at 0 1 metric).
  { inversion Hfixlc; assumption. }
  assert (Hfixv : value (tm_fix A B metric body)) by (constructor; assumption).
  assert (Hrun : forall n : Z, forall arg,
    denotes (measured_input A p metric) arg ->
    predicate_multistep (open_tm metric arg) (tm_int n) ->
    evals_denotes (open_rty_tm R2 arg) (tm_app (tm_fix A B metric body) arg)).
  { intro n. induction n as [n IH] using
      (well_founded_induction integer_decreases_wf).
    intros arg Harg Hmetric.
    assert (Hargv : value arg) by (eapply denotes_value; eauto).
    assert (Harglc : locally_closed_tm arg) by (apply value_regular; assumption).
    eapply evals_denotes_single.
    - apply lc_tm_app; assumption.
    - apply ST_AppFix; assumption.
    - intros w Hs. inversion Hs; subst; try reflexivity.
      + exfalso. eapply value_no_step; [exact Hfixv | exact H1].
      + exfalso. eapply value_no_step; [exact Hargv | eassumption].
    - apply Hbody; [assumption |].
      apply denotes_func_iff. split; [assumption |]. split; [exact Htyped |].
      intros next Hnext.
      assert (Hcurrentlc : locally_closed_tm (open_tm metric arg)).
      { apply open_tm_preserves_lc_at; assumption. }
      destruct (smaller_argument_metric _ _ _ _ _ _ Hcurrentlc Hmetric Hnext)
        as [Hnextbase [m [Hm [Hnonneg Hlt]]]].
      apply (IH m).
      + split; assumption.
      + exact Hnextbase.
      + exact Hm. }
  apply denotes_func_iff. split; [assumption |]. split; [exact Htyped |].
  intros arg Harg.
  destruct (measured_argument_metric _ _ _ _ Harg) as [m [Hm Hnonneg]].
  apply (Hrun m); assumption.
Qed.

Lemma instantiate_pred_update_irrelevant : forall p theta gamma x u,
  ~ In x (fv_pred p) ->
  instantiate_pred theta (term_subst_update gamma x u) p =
  instantiate_pred theta gamma p.
Proof.
  induction p; intros; simpl in *; try reflexivity;
    try solve [rewrite in_app_iff in H; f_equal;
      apply instantiate_term_update_irrelevant; intuition];
    try solve [rewrite in_app_iff in H; f_equal; [apply IHp1 | apply IHp2]; intuition].
  f_equal. apply IHp. assumption.
Qed.

Lemma instantiate_smaller_input : forall A p metric theta gamma x arg,
  ~ In x (fv_pred p) -> ~ In x (fv_tm metric) ->
  type_substitution_closed theta -> term_substitution_closed gamma ->
  locally_closed_tm arg ->
  instantiate_rty theta (term_subst_update gamma x arg)
    (smaller_input A p metric (open_tm metric (tm_fvar x))) =
  smaller_input (instantiate_ty theta A) (instantiate_pred theta gamma p)
    (instantiate theta gamma metric) (open_tm (instantiate theta gamma metric) arg).
Proof.
  intros A p metric theta gamma x arg Hp Hmetric Htheta Hgamma Harg.
  unfold smaller_input. cbn [instantiate_rty instantiate_qualifier instantiate_pred Pred_Ge].
  rewrite instantiate_pred_update_irrelevant by assumption.
  rewrite (instantiate_term_update_irrelevant metric theta gamma x arg Hmetric).
  rewrite instantiate_open_tm by assumption. reflexivity.
Qed.

Lemma fresh_open_pred : forall p k x y,
  x <> y -> ~ In x (fv_pred p) ->
  ~ In x (fv_pred (open_pred_tm_rec k (tm_fvar y) p)).
Proof.
  induction p; intros k x y Hneq Hfresh; simpl in *; try tauto;
    repeat rewrite in_app_iff in *;
    try solve [intro Hin; destruct Hin; apply fv_open_tm_rec in H;
      simpl in H; intuition];
    try solve [intuition eauto].
Qed.

Lemma fresh_open_rty : forall R k x y,
  x <> y -> ~ In x (fv_rty R) ->
  ~ In x (fv_rty (open_rty_tm_rec k (tm_fvar y) R)).
Proof.
  induction R; intros k x y Hneq Hfresh; simpl in *.
  - apply fresh_open_pred; assumption.
  - rewrite in_app_iff in *. intuition eauto.
  - rewrite in_app_iff in *. intuition eauto.
  - eauto.
Qed.

Lemma related_substitution_strengthen : forall theta gamma RGamma x T p q,
  related_substitution theta gamma RGamma ->
  lookup_rcontext x RGamma = Some (R_Refine T p) ->
  qualifier_holds (open_qualifier_tm (instantiate_qualifier theta gamma q) (gamma x)) ->
  related_substitution theta gamma (update_rcontext RGamma x (R_Refine T q)).
Proof.
  intros theta gamma RGamma x T p q Hrel Hx Hq.
  constructor; [exact (substitution_values Hrel) |].
  intros y R Hy. simpl in Hy. destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst y. inversion Hy; subst R.
    pose proof (Hrel x (R_Refine T p) Hx) as Hd.
    apply denotes_refine_iff in Hd. destruct Hd as [Hv [Ht Hp]].
    apply denotes_refine_iff. auto.
  - apply Hrel. exact Hy.
Qed.

Theorem fundamental_and_subtyping :
  (forall Delta RGamma t R (H : has_rtype Delta RGamma t R),
    typing_semantics Delta RGamma t R) /\
  (forall Delta RGamma R S (H : subtype Delta RGamma R S),
    subtype_semantics Delta RGamma R S).
Proof.
  apply refinement_typing_mutind;
    unfold typing_semantics, subtype_semantics.
  - intros Delta RGamma x R Hlookup Hwf Hctx theta gamma Htheta Hgamma
      HthetaWf Hrelated. simpl.
    apply evals_denotes_of_denotes. exact (Hrelated x R Hlookup).
  - intros L Delta RGamma R1 body R2 Hwf Hbody IHbody Hctx
      theta gamma Htheta Hgamma HthetaWf Hrelated.
    assert (Hwhole : has_rtype Delta RGamma
      (tm_abs (erase R1) body) (R_Func R1 R2)).
    { apply RT_Abs with L; assumption. }
    pose proof (instantiated_refinement_typing_erases _ _ _ _ _ _ Hwhole
      Hctx Htheta Hgamma HthetaWf Hrelated) as Htyped.
    assert (Hvalue : value (instantiate theta gamma (tm_abs (erase R1) body))).
    { apply v_abs. eapply typing_lc. exact Htyped. }
    apply evals_denotes_of_denotes.
    apply (proj2 (denotes_func_iff _ _ _)).
    split; [exact Hvalue |]. split; [exact Htyped |].
    intros arg Harg.
    assert (Harglc : locally_closed_tm arg).
    { apply value_regular. eapply denotes_value. exact Harg. }
    set (x := fresh (L ++ fv_tm body ++ fv_rty R1 ++ fv_rty R2 ++
      fv_rcontext RGamma)).
    assert (Hxall : ~ In x (L ++ fv_tm body ++ fv_rty R1 ++ fv_rty R2 ++
      fv_rcontext RGamma)) by (subst x; apply fresh_notin).
    repeat rewrite in_app_iff in Hxall.
    assert (Hctx' : context_wf Delta
      (erase_context (update_rcontext RGamma x R1))).
    { simpl. apply context_wf_update; [exact Hctx |].
      eapply wf_rty_erases. exact Hwf. }
    pose proof (IHbody x ltac:(tauto) Hctx' theta
      (term_subst_update gamma x arg) Htheta
      (term_subst_update_closed gamma x arg Hgamma Harglc) HthetaWf
      (related_substitution_update theta gamma RGamma x R1 arg Hrelated Harg
        ltac:(tauto) ltac:(tauto))) as Hresult.
    rewrite (instantiate_open_tm body theta gamma x arg) in Hresult;
      try tauto.
    rewrite (instantiate_rty_open_tm R2 theta gamma x arg) in Hresult;
      try tauto.
    apply evals_denotes_intro.
    + apply lc_tm_app.
      * apply value_regular. exact Hvalue.
      * exact Harglc.
    + right. eexists. apply ST_AppAbs.
      * exact (value_regular _ Hvalue).
      * eapply denotes_value. exact Harg.
    + intros HappValue. inversion HappValue.
    + intros u Hstep. inversion Hstep; subst.
      * exact Hresult.
      * match goal with Hs : tm_abs _ _ --> _ |- _ => inversion Hs end.
      * exfalso. eapply value_no_step.
        -- eapply denotes_value. exact Harg.
        -- eassumption.
  - intros Delta RGamma t1 t2 R1 R2 Ht1 IHt1 Ht2 IHt2 Hctx
      theta gamma Htheta Hgamma HthetaWf Hrelated.
    pose proof (IHt1 Hctx theta gamma Htheta Hgamma HthetaWf Hrelated) as Hfun.
    pose proof (IHt2 Hctx theta gamma Htheta Hgamma HthetaWf Hrelated) as Harg.
    eapply evals_denotes_app_exists; eauto.
  - intros L Delta RGamma body R Hbody IHbody Hctx theta gamma
      Htheta Hgamma HthetaWf Hrelated.
    assert (Hwhole : has_rtype Delta RGamma (tm_tabs body) (R_Poly R)).
    { apply RT_TAbs with L. exact Hbody. }
    pose proof (instantiated_refinement_typing_erases _ _ _ _ _ _ Hwhole
      Hctx Htheta Hgamma HthetaWf Hrelated) as Htyped.
    assert (Hvalue : value (instantiate theta gamma (tm_tabs body))).
    { apply v_tabs. eapply typing_lc. exact Htyped. }
    apply evals_denotes_of_denotes.
    apply (proj2 (denotes_poly_iff _ _)).
    split; [exact Hvalue |]. split; [exact Htyped |].
    intros U HU.
    set (X := fresh (L ++ ftv_tm body ++ ftv_rty R ++ ftv_rcontext RGamma)).
    assert (HXall : ~ In X
      (L ++ ftv_tm body ++ ftv_rty R ++ ftv_rcontext RGamma))
      by (subst X; apply fresh_notin).
    repeat rewrite in_app_iff in HXall.
    assert (Hctx' : context_wf (X :: Delta) (erase_context RGamma)).
    { eapply context_wf_weaken_type; [exact Hctx |].
      unfold ty_context_included. simpl. auto. }
    assert (Htheta' : type_substitution_closed
      (type_subst_update theta X U)).
    { apply type_subst_update_closed; [exact Htheta |].
      eapply wf_ty_lc. exact HU. }
    assert (HthetaWf' : type_substitution_wf (X :: Delta) []
      (type_subst_update theta X U)).
    { intros Y HY. simpl in HY. destruct HY as [HY | HY].
      - subst Y. unfold type_subst_update. rewrite Nat.eqb_refl. exact HU.
      - unfold type_subst_update.
        destruct (Nat.eqb X Y) eqn:E.
        + exact HU.
        + apply HthetaWf. exact HY. }
    pose proof (IHbody X ltac:(tauto) Hctx'
      (type_subst_update theta X U) gamma Htheta' Hgamma HthetaWf'
      (related_substitution_type_update theta gamma RGamma X U Hrelated
        ltac:(tauto))) as Hresult.
    rewrite (instantiate_open_ty body theta gamma X U) in Hresult;
      try tauto; try (eapply wf_ty_lc; exact HU).
    rewrite (instantiate_rty_open_ty R theta gamma X U) in Hresult;
      try tauto; try (eapply wf_ty_lc; exact HU).
    apply evals_denotes_intro.
    + apply lc_tm_tapp.
      * apply value_regular. exact Hvalue.
      * eapply wf_ty_lc. exact HU.
    + right. eexists. apply ST_TAppTabs.
      * exact (value_regular _ Hvalue).
      * eapply wf_ty_lc. exact HU.
    + intros HtappValue. inversion HtappValue.
    + intros u Hstep. inversion Hstep; subst.
      * exact Hresult.
      * match goal with Hs : tm_tabs _ --> _ |- _ => inversion Hs end.
  - intros Delta RGamma t R U Ht IHt HU Hctx theta gamma Htheta Hgamma
      HthetaWf Hrelated.
    pose proof (IHt Hctx theta gamma Htheta Hgamma HthetaWf Hrelated) as Hpoly.
    assert (HUinst : wf_ty [] (instantiate_ty theta U)).
    { eapply wf_ty_instantiate; eauto. }
    pose proof (evals_denotes_tapp _ _ _ Hpoly HUinst) as Hresult.
    assert (Heq :
      instantiate_rty theta gamma (open_rty_ty R U) =
      open_rty_ty (instantiate_rty theta gamma R) (instantiate_ty theta U)).
    { apply instantiate_rty_open_ty_commute_top; try assumption.
      eapply wf_ty_lc. exact HU. }
    rewrite Heq. exact Hresult.
  - intros Delta RGamma n Hctx theta gamma Htheta Hgamma HthetaWf Hrelated.
    apply evals_denotes_of_denotes. apply denotes_refine_iff.
    split; [constructor|]. split; [constructor|].
    exists (tm_int n). repeat split; constructor.
  - intros Delta RGamma t1 t2 Ht1 IHt1 Ht2 IHt2 Hctx theta gamma
      Htheta Hgamma HthetaWf Hrelated.
    apply evals_denotes_div.
    + exact (IHt1 Hctx theta gamma Htheta Hgamma HthetaWf Hrelated).
    + exact (IHt2 Hctx theta gamma Htheta Hgamma HthetaWf Hrelated).
  - intros Delta RGamma op t1 t2 Ht1 IHt1 Ht2 IHt2 Hctx theta gamma
      Htheta Hgamma HthetaWf Hrelated.
    apply evals_denotes_arith.
    + exact (IHt1 Hctx theta gamma Htheta Hgamma HthetaWf Hrelated).
    + exact (IHt2 Hctx theta gamma Htheta Hgamma HthetaWf Hrelated).
  - intros Delta RGamma t1 t2 R Ht1 IHt1 Ht2 IHt2 Hctx theta gamma
      Htheta Hgamma HthetaWf Hrelated.
    apply evals_denotes_choice.
    + exact (IHt1 Hctx theta gamma Htheta Hgamma HthetaWf Hrelated).
    + exact (IHt2 Hctx theta gamma Htheta Hgamma HthetaWf Hrelated).
  - intros Delta RGamma Hctx theta gamma Htheta Hgamma HthetaWf Hrelated.
    apply evals_denotes_of_denotes. apply denotes_refine_iff.
    split; [constructor |]. split; [constructor |exact I].
  - intros Delta RGamma Hctx theta gamma Htheta Hgamma HthetaWf Hrelated.
    apply evals_denotes_of_denotes. apply denotes_refine_iff.
    split; [constructor |]. split; [constructor |exact I].
  - intros Delta RGamma t1 t2 t3 R Ht1 IHt1 Ht2 IHt2 Ht3 IHt3
      Hctx theta gamma Htheta Hgamma HthetaWf Hrelated.
    apply evals_denotes_if.
    + exact (IHt1 Hctx theta gamma Htheta Hgamma HthetaWf Hrelated).
    + exact (IHt2 Hctx theta gamma Htheta Hgamma HthetaWf Hrelated).
    + exact (IHt3 Hctx theta gamma Htheta Hgamma HthetaWf Hrelated).
  - intros Delta RGamma v T ps Htyped Hv Hwf Hclosed Hpred Hctx theta gamma
      Htheta Hgamma HthetaWf Hrelated.
    assert (Hinst_value : value (instantiate theta gamma v)).
    { eapply instantiate_value; eauto. }
    apply evals_denotes_of_denotes.
    apply (proj2 (denotes_refine_iff _ _ _)).
    split; [exact Hinst_value |]. split.
    + eapply has_type_instantiate; eauto.
      exact (related_substitution_typed theta gamma RGamma Hrelated).
    + pose proof (instantiate_qualifier_holds _ theta gamma Hclosed Hpred Htheta Hgamma)
        as Hpred'.
      assert (Heq : instantiate_qualifier theta gamma (open_qualifier_tm ps v) =
        open_qualifier_tm (instantiate_qualifier theta gamma ps)
          (instantiate theta gamma v)).
      { apply instantiate_qualifier_open_commute; try assumption.
        apply value_regular. exact Hv. }
      rewrite Heq in Hpred'.
      exact Hpred'.
  - intros L Delta RGamma A p metric body R2 Hwf Hmetric Hbody IHbody Hctx
      theta gamma Htheta Hgamma HthetaWf Hrelated.
    assert (Hwhole : has_rtype Delta RGamma (tm_fix A (erase R2) metric body)
      (R_Func (measured_input A p metric) R2)).
    { apply RT_Fix with L; assumption. }
    pose proof (instantiated_refinement_typing_erases _ _ _ _ _ _ Hwhole
      Hctx Htheta Hgamma HthetaWf Hrelated) as Htyped.
    set (vf := instantiate theta gamma (tm_fix A (erase R2) metric body)).
    assert (Hvflc : locally_closed_tm vf) by (eapply typing_lc; exact Htyped).
    assert (HAv : wf_ty Delta A).
    { pose proof (wf_rty_erases _ _ _ Hwf) as H. inversion H; assumption. }
    assert (HBv : wf_ty Delta (erase R2)).
    { pose proof (wf_rty_erases _ _ _ Hwf) as H. inversion H; assumption. }
    apply evals_denotes_of_denotes.
    apply (recursive_function_denotes (instantiate_ty theta A)
      (instantiate_ty theta (erase R2)) (instantiate_pred theta gamma p)
      (instantiate theta gamma metric) (instantiate theta gamma body)
      (instantiate_rty theta gamma R2)).
    + exact Htyped.
    + intros arg Harg Hrec.
      assert (Harglc : locally_closed_tm arg) by
        (apply value_regular; eapply denotes_value; exact Harg).
      set (all := L ++ fv_tm body ++ fv_tm metric ++ fv_pred p ++
        fv_rty R2 ++ fv_rcontext RGamma).
      set (x := fresh all).
      set (f := fresh (x :: all)).
      assert (Hxall : ~ In x all) by apply fresh_notin.
      assert (Hfall : ~ In f (x :: all)) by apply fresh_notin.
      unfold all in Hxall, Hfall. simpl in Hfall.
      repeat rewrite in_app_iff in Hxall, Hfall.
      assert (Hfx : f <> x) by intuition congruence.
      assert (Hfreshopen : ~ In f (fv_tm (open_tm metric (tm_fvar x)))).
      { intro Hin. apply fv_open_tm_rec in Hin. simpl in Hin. intuition congruence. }
      set (Rin := measured_input A p metric).
      set (Rrec := R_Func (smaller_input A p metric (open_tm metric (tm_fvar x))) R2).
      assert (Hfreshrec : ~ In f (fv_rty Rrec)).
      { unfold Rrec, smaller_input. simpl.
        repeat rewrite in_app_iff. simpl. tauto. }
      assert (Hfreshctx : ~ In f (fv_rcontext (update_rcontext RGamma x Rin))).
      { unfold Rin, measured_input. simpl. repeat rewrite in_app_iff. simpl. tauto. }
      assert (Hrelx : related_substitution theta (term_subst_update gamma x arg)
        (update_rcontext RGamma x Rin)).
      { apply related_substitution_update; try assumption.
        - unfold Rin, measured_input. simpl. repeat rewrite in_app_iff. simpl. tauto.
        - tauto. }
      assert (Hrecx : denotes
        (instantiate_rty theta (term_subst_update gamma x arg) Rrec) vf).
      { unfold Rrec. cbn [instantiate_rty].
        rewrite instantiate_smaller_input; try tauto.
        rewrite instantiate_rty_term_update_irrelevant by tauto.
        exact Hrec. }
      assert (Hrelxf : related_substitution theta
        (term_subst_update (term_subst_update gamma x arg) f vf)
        (update_rcontext (update_rcontext RGamma x Rin) f Rrec)).
      { apply related_substitution_update; assumption. }
      assert (Hctxxf : context_wf Delta
        (erase_context (update_rcontext (update_rcontext RGamma x Rin) f Rrec))).
      { simpl. apply context_wf_update.
        - apply context_wf_update; assumption.
        - apply WF_Arrow; assumption. }
      pose proof (IHbody f x ltac:(tauto) ltac:(simpl; intuition congruence)
        Hctxxf theta (term_subst_update (term_subst_update gamma x arg) f vf)
        Htheta
        (term_subst_update_closed _ f vf
          (term_subst_update_closed gamma x arg Hgamma Harglc) Hvflc)
        HthetaWf Hrelxf) as Hresult.
      rewrite instantiate_open_fix_body in Hresult; try tauto.
      rewrite (instantiate_rty_term_update_irrelevant
        (open_rty_tm R2 (tm_fvar x)) theta (term_subst_update gamma x arg) f vf) in Hresult.
      * rewrite instantiate_rty_open_tm in Hresult; try tauto.
      * apply fresh_open_rty; tauto.
  - intros Delta RGamma x p t0 t1 R Hlookup Ht0 IHt0 Ht1 IHt1 Hctx
      theta gamma Htheta Hgamma HthetaWf Hrelated.
    assert (Hwhole : has_rtype Delta RGamma (tm_ifzero (tm_fvar x) t0 t1) R).
    { eapply RT_IfZero; eauto. }
    pose proof (instantiated_refinement_typing_erases _ _ _ _ _ _ Hwhole
      Hctx Htheta Hgamma HthetaWf Hrelated) as Htyped.
    pose proof (typing_lc _ _ _ _ Htyped) as Hlc.
    pose proof (Hrelated x (R_Refine Ty_Int p) Hlookup) as Hd.
    apply denotes_refine_iff in Hd. destruct Hd as [Hv [Ht Hp]].
    destruct (value_int_canonical _ Hv Ht) as [n Hn].
    assert (Hctx' : forall q, context_wf Delta
      (erase_context (update_rcontext RGamma x (R_Refine Ty_Int q)))).
    { intro q. simpl. apply context_wf_update; [assumption | constructor]. }
    simpl in Hlc |- *. rewrite Hn in Hlc |- *.
    inversion Hlc; subst.
    destruct (Z.eq_dec n 0) as [En | En].
    + subst n. eapply evals_denotes_single; [exact Hlc | apply ST_IfZero; assumption | |].
      * intros w Hs. inversion Hs; subst; try reflexivity; try congruence;
          match goal with Hs : step (tm_int _) _ |- _ => inversion Hs end.
      *
      apply IHt0; try assumption; [apply Hctx' |].
      eapply related_substitution_strengthen; [exact Hrelated | exact Hlookup |].
      change (qualifier_holds (open_qualifier_tm (instantiate_qualifier theta gamma p) (gamma x)) /\
        qualifier_holds (Pred_Eq (gamma x) (tm_int 0%Z))).
      split; [exact Hp |]. rewrite Hn. exists (tm_int 0%Z). repeat split; constructor.
    + eapply evals_denotes_single; [exact Hlc | apply ST_IfNonzero; assumption | |].
      * intros w Hs. inversion Hs; subst; try reflexivity; try congruence;
          match goal with Hs : step (tm_int _) _ |- _ => inversion Hs end.
      *
      apply IHt1; try assumption; [apply Hctx' |].
      eapply related_substitution_strengthen; [exact Hrelated | exact Hlookup |].
      change (qualifier_holds (open_qualifier_tm (instantiate_qualifier theta gamma p) (gamma x)) /\
        ~ qualifier_holds (Pred_Eq (gamma x) (tm_int 0%Z))).
      split; [exact Hp |]. rewrite Hn.
      intros [v [Hnv [H0v Hvv]]].
      pose proof (value_multi_eq _ _ (v_int n) (predicate_multi_to_multi _ _ Hnv)) as E1.
      pose proof (value_multi_eq _ _ (v_int 0) (predicate_multi_to_multi _ _ H0v)) as E2.
      congruence.
  - intros Delta RGamma t R S Ht IHt Hwf Hsub IHsub Hctx theta gamma
      Htheta Hgamma HthetaWf Hrelated.
    pose proof (IHt Hctx theta gamma Htheta Hgamma HthetaWf Hrelated) as Hresult.
    eapply evals_denotes_map; [|exact Hresult].
    intros v Hden.
    apply (IHsub (wf_rty_erases _ _ _ Hwf) Hctx theta gamma Htheta Hgamma
      HthetaWf Hrelated v Hden).
  - intros Delta RGamma R Hwf Hctx theta gamma Htheta Hgamma HthetaWf
      Hrelated v Hden. exact Hden.
  - intros L Delta RGamma T ps qs Hentails Hwf Hctx theta gamma Htheta
      Hgamma HthetaWf Hrelated v Hden.
    apply (proj1 (denotes_refine_iff _ _ _)) in Hden.
    destruct Hden as [Hv [Htyped Hps]].
    set (x := fresh (L ++ fv_qualifier ps ++ fv_qualifier qs ++ fv_rcontext RGamma)).
    assert (Hxall : ~ In x (L ++ fv_qualifier ps ++ fv_qualifier qs ++ fv_rcontext RGamma))
      by (subst x; apply fresh_notin).
    repeat rewrite in_app_iff in Hxall.
    pose proof (entails_sound _ _ _ _ (Hentails x ltac:(tauto)) theta
      (term_subst_update gamma x v)) as Hsound.
    assert (Hvlc : locally_closed_tm v) by (apply value_regular; exact Hv).
    assert (Hgamma' : term_substitution_closed (term_subst_update gamma x v)).
    { apply term_subst_update_closed; assumption. }
    assert (Hps_eq :
      instantiate_qualifier theta (term_subst_update gamma x v)
        (open_qualifier_tm ps (tm_fvar x)) =
      open_qualifier_tm (instantiate_qualifier theta gamma ps) v).
    { unfold open_qualifier_tm. apply instantiate_qualifier_open_tm_rec; tauto. }
    assert (Hqs_eq :
      instantiate_qualifier theta (term_subst_update gamma x v)
        (open_qualifier_tm qs (tm_fvar x)) =
      open_qualifier_tm (instantiate_qualifier theta gamma qs) v).
    { unfold open_qualifier_tm. apply instantiate_qualifier_open_tm_rec; tauto. }
    apply (proj2 (denotes_refine_iff _ _ _)).
    split; [exact Hv |]. split; [exact Htyped |].
    rewrite <- Hqs_eq. apply Hsound; try assumption.
    + apply related_substitution_update; try assumption.
      * apply denotes_refine_iff. split; [exact Hv|]. split; [exact Htyped|exact I].
      * simpl. tauto.
      * tauto.
    + rewrite Hps_eq. exact Hps.
  - intros L Delta RGamma R1 R2 S1 S2 Hdomain IHdomain Hcodomain IHcodomain
      Hwf Hctx theta gamma Htheta Hgamma HthetaWf Hrelated v Hden.
    apply (proj1 (denotes_func_iff _ _ _)) in Hden.
    destruct Hden as [Hv [Htyped Hmap]].
    assert (HwfS1 : wf_ty Delta (erase S1)).
    { simpl in Hwf. inversion Hwf. assumption. }
    assert (HwfS2 : wf_ty Delta (erase S2)).
    { simpl in Hwf. inversion Hwf. assumption. }
    apply (proj2 (denotes_func_iff _ _ _)).
    split; [exact Hv |]. split.
    + pose proof (subtype_erases _ _ _ _
        (S_Func L Delta RGamma R1 R2 S1 S2 Hdomain Hcodomain)) as Herase.
      simpl in Htyped |- *.
      rewrite !erase_instantiate_rty in Htyped |- *.
      simpl in Herase. injection Herase as E1 E2.
      rewrite <- E1, <- E2. exact Htyped.
    + intros arg HargS1.
      assert (HwfR1 : wf_ty Delta (erase R1)).
      { pose proof (subtype_erases _ _ _ _ Hdomain) as E.
        rewrite <- E. exact HwfS1. }
      pose proof (IHdomain HwfR1 Hctx theta gamma Htheta Hgamma HthetaWf
        Hrelated arg HargS1) as HargR1.
      pose proof (Hmap arg HargR1) as Hresult.
      set (x := fresh (L ++ fv_rty R1 ++ fv_rty R2 ++ fv_rty S1 ++
        fv_rty S2 ++ fv_rcontext RGamma)).
      assert (Hxall : ~ In x
        (L ++ fv_rty R1 ++ fv_rty R2 ++ fv_rty S1 ++ fv_rty S2 ++
          fv_rcontext RGamma)) by (subst x; apply fresh_notin).
      repeat rewrite in_app_iff in Hxall.
      assert (Harglc : locally_closed_tm arg).
      { apply value_regular. eapply denotes_value. exact HargS1. }
      assert (Hctx' : context_wf Delta
        (erase_context (update_rcontext RGamma x S1))).
      { simpl. apply context_wf_update; assumption. }
      assert (HwfOpenS2 : wf_ty Delta
        (erase (open_rty_tm S2 (tm_fvar x)))).
      { rewrite erase_open_rty_tm. exact HwfS2. }
      assert (HR2eq :
        instantiate_rty theta (term_subst_update gamma x arg)
          (open_rty_tm R2 (tm_fvar x)) =
        open_rty_tm (instantiate_rty theta gamma R2) arg).
      { apply instantiate_rty_open_tm; tauto. }
      assert (HS2eq :
        instantiate_rty theta (term_subst_update gamma x arg)
          (open_rty_tm S2 (tm_fvar x)) =
        open_rty_tm (instantiate_rty theta gamma S2) arg).
      { apply instantiate_rty_open_tm; tauto. }
      eapply evals_denotes_map; [|exact Hresult].
      intros result Hresult_denotes.
      pose proof (IHcodomain x ltac:(tauto) HwfOpenS2 Hctx' theta
        (term_subst_update gamma x arg) Htheta
        (term_subst_update_closed gamma x arg Hgamma Harglc) HthetaWf
        (related_substitution_update theta gamma RGamma x S1 arg Hrelated
          HargS1 ltac:(tauto) ltac:(tauto)) result) as Hconvert.
      rewrite HR2eq, HS2eq in Hconvert.
      apply Hconvert. exact Hresult_denotes.
  - intros Delta RGamma witness R1 R2 S Hwitness Htyping IHtyping Hsub IHsub
      Hwf Hctx theta gamma Htheta Hgamma HthetaWf Hrelated v HdenS.
    pose proof (IHtyping Hctx theta gamma Htheta Hgamma HthetaWf Hrelated)
      as Hwit_eval.
    assert (Hwit_value : value (instantiate theta gamma witness)).
    { eapply instantiate_value; eauto. }
    pose proof (evals_denotes_from_value _ _ Hwit_value Hwit_eval) as Hwit_den.
    assert (HwfOpen : wf_ty Delta (erase (open_rty_tm R2 witness))).
    { rewrite erase_open_rty_tm. simpl in Hwf. exact Hwf. }
    pose proof (IHsub HwfOpen Hctx theta gamma Htheta Hgamma HthetaWf Hrelated
      v HdenS) as Hbody_den.
    assert (Hopen_eq :
      instantiate_rty theta gamma (open_rty_tm R2 witness) =
      open_rty_tm (instantiate_rty theta gamma R2)
        (instantiate theta gamma witness)).
    { apply instantiate_rty_open_tm_commute_top; try assumption.
      apply value_regular. exact Hwitness. }
    rewrite Hopen_eq in Hbody_den.
    apply (proj2 (denotes_exists_iff _ _ _)).
    split.
    + eapply denotes_value. exact HdenS.
    + split.
      * pose proof (denotes_typing _ _ HdenS) as Htyped.
        pose proof (subtype_erases _ _ _ _
          (S_Witness Delta RGamma witness R1 R2 S Hwitness Htyping Hsub))
          as Herase.
        change (has_type [] empty v
          (erase (instantiate_rty theta gamma (R_Exists R1 R2)))).
        rewrite erase_instantiate_rty.
        rewrite <- Herase.
        rewrite erase_instantiate_rty in Htyped. exact Htyped.
      * exists (instantiate theta gamma witness). split; assumption.
  - intros L Delta RGamma R1 R2 S HwfR1 HlcS Hsub IHsub HwfS Hctx
      theta gamma Htheta Hgamma HthetaWf Hrelated v Hden.
    apply (proj1 (denotes_exists_iff _ _ _)) in Hden.
    destruct Hden as [Hv [Htyped [witness [Hwitness Hbody]]]].
    set (x := fresh (L ++ fv_rty R1 ++ fv_rty R2 ++ fv_rty S ++
      fv_rcontext RGamma)).
    assert (Hxall : ~ In x
      (L ++ fv_rty R1 ++ fv_rty R2 ++ fv_rty S ++ fv_rcontext RGamma))
      by (subst x; apply fresh_notin).
    repeat rewrite in_app_iff in Hxall.
    assert (Hwitness_lc : locally_closed_tm witness).
    { apply value_regular. eapply denotes_value. exact Hwitness. }
    assert (Hctx' : context_wf Delta
      (erase_context (update_rcontext RGamma x R1))).
    { simpl. apply context_wf_update; [exact Hctx |].
      eapply wf_rty_erases. exact HwfR1. }
    assert (HwfS' : wf_ty Delta (erase S)) by exact HwfS.
    pose proof (IHsub x ltac:(tauto) HwfS' Hctx' theta
      (term_subst_update gamma x witness) Htheta
      (term_subst_update_closed gamma x witness Hgamma Hwitness_lc) HthetaWf
      (related_substitution_update theta gamma RGamma x R1 witness Hrelated
        Hwitness ltac:(tauto) ltac:(tauto)) v) as Hconvert.
    assert (Hsource_eq :
      instantiate_rty theta (term_subst_update gamma x witness)
        (open_rty_tm R2 (tm_fvar x)) =
      open_rty_tm (instantiate_rty theta gamma R2) witness).
    { apply instantiate_rty_open_tm; tauto. }
    rewrite Hsource_eq in Hconvert.
    assert (Htarget_eq :
      instantiate_rty theta (term_subst_update gamma x witness) S =
      instantiate_rty theta gamma S).
    { apply instantiate_rty_term_update_irrelevant. tauto. }
    rewrite Htarget_eq in Hconvert. apply Hconvert. exact Hbody.
  - intros L Delta RGamma R S Hsub IHsub Hwf Hctx theta gamma Htheta Hgamma
      HthetaWf Hrelated v Hden.
    apply (proj1 (denotes_poly_iff _ _)) in Hden.
    destruct Hden as [Hv [Htyped Hmap]].
    apply (proj2 (denotes_poly_iff _ _)).
    split; [exact Hv |]. split.
    + pose proof (subtype_erases _ _ _ _
        (S_Poly L Delta RGamma R S Hsub)) as Herase.
      simpl in Htyped |- *.
      rewrite !erase_instantiate_rty in Htyped |- *.
      simpl in Herase. injection Herase as E.
      rewrite <- E. exact Htyped.
    + intros U HU.
      pose proof (Hmap U HU) as Hresult.
      set (X := fresh (L ++ ftv_rty R ++ ftv_rty S ++ ftv_rcontext RGamma)).
      assert (HXall : ~ In X
        (L ++ ftv_rty R ++ ftv_rty S ++ ftv_rcontext RGamma))
        by (subst X; apply fresh_notin).
      repeat rewrite in_app_iff in HXall.
      assert (Hctx' : context_wf (X :: Delta) (erase_context RGamma)).
      { eapply context_wf_weaken_type; [exact Hctx |].
        unfold ty_context_included. simpl. auto. }
      assert (Htheta' : type_substitution_closed
        (type_subst_update theta X U)).
      { apply type_subst_update_closed; [exact Htheta |].
        eapply wf_ty_lc. exact HU. }
      assert (HthetaWf' : type_substitution_wf (X :: Delta) []
        (type_subst_update theta X U)).
      { intros Y HY. simpl in HY. destruct HY as [HY | HY].
        - subst Y. unfold type_subst_update. rewrite Nat.eqb_refl. exact HU.
        - unfold type_subst_update. destruct (Nat.eqb X Y); auto. }
      assert (HwfOpenS : wf_ty (X :: Delta)
        (erase (open_rty_ty S (Ty_FVar X)))).
      { rewrite erase_open_rty_ty.
        apply wf_ty_open_all.
        - eapply wf_ty_weaken; [exact Hwf |].
          unfold ty_context_included. simpl. auto.
        - apply WF_Var. simpl. auto. }
      assert (HR_eq :
        instantiate_rty (type_subst_update theta X U) gamma
          (open_rty_ty R (Ty_FVar X)) =
        open_rty_ty (instantiate_rty theta gamma R) U).
      { apply instantiate_rty_open_ty; try tauto.
        eapply wf_ty_lc. exact HU. }
      assert (HS_eq :
        instantiate_rty (type_subst_update theta X U) gamma
          (open_rty_ty S (Ty_FVar X)) =
        open_rty_ty (instantiate_rty theta gamma S) U).
      { apply instantiate_rty_open_ty; try tauto.
        eapply wf_ty_lc. exact HU. }
      eapply evals_denotes_map; [|exact Hresult].
      intros result Hresult_denotes.
      pose proof (IHsub X ltac:(tauto) HwfOpenS Hctx'
        (type_subst_update theta X U) gamma Htheta' Hgamma HthetaWf'
        (related_substitution_type_update theta gamma RGamma X U Hrelated
          ltac:(tauto)) result) as Hconvert.
      rewrite HR_eq, HS_eq in Hconvert.
      apply Hconvert. exact Hresult_denotes.
  - intros Delta RGamma R S U HRS IHRS HSU IHSU HwfU Hctx theta gamma
      Htheta Hgamma HthetaWf Hrelated v HdenR.
    assert (HwfS : wf_ty Delta (erase S)).
    { pose proof (subtype_erases _ _ _ _ HSU) as E.
      rewrite E. exact HwfU. }
    apply (IHSU HwfU Hctx theta gamma Htheta Hgamma HthetaWf Hrelated v).
    apply (IHRS HwfS Hctx theta gamma Htheta Hgamma HthetaWf Hrelated v).
    exact HdenR.
Qed.

Theorem fundamental : forall Delta RGamma t R,
  has_rtype Delta RGamma t R ->
  typing_semantics Delta RGamma t R.
Proof.
  intros Delta RGamma t R Htyping.
  exact ((proj1 fundamental_and_subtyping) Delta RGamma t R Htyping).
Qed.

End SystemFRefinementIfNonDeterminismRecursionSoundness.

Module SystemFRefinementIfNonDeterminismRecursionTask.
Import ListNotations SystemFRefinementIfNonDeterminismRecursion SystemFRefinementIfNonDeterminismRecursionInfrastructure SystemFRefinementIfNonDeterminismRecursionCoreTyping SystemFRefinementIfNonDeterminismRecursionLogic SystemFRefinementIfNonDeterminismRecursionTyping SystemFRefinementIfNonDeterminismRecursionEvaluation SystemFRefinementIfNonDeterminismRecursionDenotations SystemFRefinementIfNonDeterminismRecursionSoundness.

Theorem never_stuck : forall (t t' : tm) (R : rty),
  has_rtype [] empty_rcontext t R ->
  multi t t' ->
  value t' \/ exists t'' : tm, t' --> t''.
Proof.
  intros t t' R Htyping Hmulti.
  set (gamma := (fun _ : atom => tm_int 0%Z)).
  assert (Hctx : context_wf [] (erase_context empty_rcontext)).
  { intros x T Hlookup. simpl in Hlookup. discriminate. }
  assert (Hgamma : term_substitution_closed gamma).
  { intro x. unfold gamma. apply lc_tm_int. }
  assert (HthetaWf :
      type_substitution_wf [] [] identity_type_substitution).
  { unfold type_substitution_wf. intros X HX. contradiction. }
  assert (Hrelated :
      related_substitution identity_type_substitution gamma empty_rcontext).
  { constructor.
    - intro x. unfold gamma. apply v_int.
    - intros x S Hlookup. simpl in Hlookup. discriminate. }
  pose proof (fundamental [] empty_rcontext t R Htyping
    Hctx identity_type_substitution gamma
    identity_type_substitution_closed Hgamma HthetaWf Hrelated) as Heval.
  assert (Hcore : has_type [] empty t (erase R)).
  { pose proof (refinement_typing_erases [] empty_rcontext t R Htyping) as H.
    exact H. }
  assert (Hfv : fv_tm t = []).
  { eapply closed_typing_no_free_terms; exact Hcore. }
  rewrite (instantiate_no_free_terms t gamma Hfv) in Heval.
  pose proof (must_terminate_multi t t' Hmulti
    (proj1 (proj2 Heval))) as Hterm.
  exact (must_terminate_progress t' Hterm).
Qed.

End SystemFRefinementIfNonDeterminismRecursionTask.
