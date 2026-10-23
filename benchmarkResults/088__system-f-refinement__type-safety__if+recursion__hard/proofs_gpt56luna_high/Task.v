From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
From Stdlib Require Import ZArith.BinInt.
From Stdlib Require Import Program.Equality.

Module SystemFRefinementIfRecursion.

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
  | tm_fix A B metric body =>
      tm_fix (A) (B)
        (open_tm_rec (S k) u metric) (open_tm_rec (S (S k)) u body)
  | tm_ifzero t t0 t1 =>
      tm_ifzero (open_tm_rec k u t) (open_tm_rec k u t0) (open_tm_rec k u t1)
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
  | tm_fix A B metric body => fv_tm metric ++ fv_tm body
  | tm_ifzero t t0 t1 => fv_tm t ++ fv_tm t0 ++ fv_tm t1
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
  | tm_fix A B metric body => fv_ty A ++ fv_ty B ++ ftv_tm metric ++ ftv_tm body
  | tm_ifzero t t0 t1 => ftv_tm t ++ ftv_tm t0 ++ ftv_tm t1
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
  | tm_fix A B metric body =>
      tm_fix (open_ty_rec k U A) (open_ty_rec k U B)
        (open_tm_ty_rec k U metric) (open_tm_ty_rec k U body)
  | tm_ifzero t t0 t1 =>
      tm_ifzero (open_tm_ty_rec k U t) (open_tm_ty_rec k U t0) (open_tm_ty_rec k U t1)
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
  | tm_fix A B metric body =>
      tm_fix (ty_subst X U A) (ty_subst X U B)
        (tm_ty_subst X U metric) (tm_ty_subst X U body)
  | tm_ifzero t t0 t1 =>
      tm_ifzero (tm_ty_subst X U t) (tm_ty_subst X U t0) (tm_ty_subst X U t1)
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
  | tm_fix A B metric body =>
      tm_fix (A) (B)
        (tm_subst x s metric) (tm_subst x s body)
  | tm_ifzero t t0 t1 =>
      tm_ifzero (tm_subst x s t) (tm_subst x s t0) (tm_subst x s t1)
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

End SystemFRefinementIfRecursion.

Module SystemFRefinementIfRecursionInfrastructure.
Import ListNotations SystemFRefinementIfRecursion.

Definition type_substitution := atom -> ty.

Definition term_substitution := atom -> tm.

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
  | tm_fix A B metric body => tm_fix (instantiate_ty theta A) (instantiate_ty theta B)
      (instantiate theta gamma metric) (instantiate theta gamma body)
  | tm_ifzero t t0 t1 => tm_ifzero (instantiate theta gamma t)
      (instantiate theta gamma t0) (instantiate theta gamma t1)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (instantiate theta gamma t1) (instantiate theta gamma t2) (instantiate theta gamma t3)
  end.

End SystemFRefinementIfRecursionInfrastructure.

From Stdlib Require Import Arith.PeanoNat Lists.List ZArith.BinInt.
Module SystemFRefinementIfRecursionLogic.
Import ListNotations SystemFRefinementIfRecursion.

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
      predicate_multistep t2 (tm_int n2) /\ (n1 < n2)%Z;
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

End SystemFRefinementIfRecursionLogic.

From Stdlib Require Import Arith.PeanoNat Lists.List Lia ZArith.BinInt.
Module SystemFRefinementIfRecursionTyping.
Import ListNotations.
Import SystemFRefinementIfRecursion.
Export SystemFRefinementIfRecursionLogic.
Import SystemFRefinementIfRecursionInfrastructure.

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

End SystemFRefinementIfRecursionTyping.

Module SystemFRefinementIfRecursionEvaluation.
Import ListNotations SystemFRefinementIfRecursion SystemFRefinementIfRecursionInfrastructure SystemFRefinementIfRecursionLogic SystemFRefinementIfRecursionTyping.

Inductive multi : tm -> tm -> Prop :=
  | multi_refl : forall t, multi t t
  | multi_step : forall t1 t2 t3,
      t1 --> t2 -> multi t2 t3 -> multi t1 t3.
Notation "t '-->*' u" := (multi t u) (at level 40).

End SystemFRefinementIfRecursionEvaluation.

Module SystemFRefinementIfRecursionTask.
Import ListNotations SystemFRefinementIfRecursion SystemFRefinementIfRecursionInfrastructure SystemFRefinementIfRecursionLogic SystemFRefinementIfRecursionTyping SystemFRefinementIfRecursionEvaluation.

Lemma lc_tm_open_inv : forall K k t x,
  lc_tm_at K k (open_tm_rec k (tm_fvar x) t) ->
  lc_tm_at K (S k) t.
Proof.
  intros K k t; revert K k.
  induction t; intros K k x H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply lc_tm_bvar. apply Nat.eqb_eq in E. lia.
    + inversion H. apply lc_tm_bvar. apply Nat.eqb_neq in E. lia.
  - inversion H; constructor.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - inversion H; constructor.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - constructor.
  - constructor.
  - inversion H; subst; constructor; eauto.
Qed.

Lemma lc_ty_mono : forall K1 T,
  lc_ty_at K1 T -> forall K2, K1 <= K2 -> lc_ty_at K2 T.
Proof.
  intros K1 T H; induction H; intros K2 Hle.
  - apply lc_ty_bvar; lia.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; eauto.
  - apply lc_ty_all. eapply IHlc_ty_at. lia.
  - apply lc_ty_int.
  - apply lc_ty_bool.
Qed.

Lemma lc_ty_open_inv : forall K k T U,
  k <= K -> lc_ty_at K U ->
  lc_ty_at K (open_ty_rec k U T) ->
  lc_ty_at (S K) T.
Proof.
  intros K k T; revert K k.
  induction T; intros K k U Hk HU H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply lc_ty_bvar. apply Nat.eqb_eq in E. lia.
    + inversion H. apply lc_ty_bvar. apply Nat.eqb_neq in E. lia.
  - constructor.
  - inversion H; subst; constructor; eauto.
  - inversion H. apply lc_ty_all.
    apply IHT with (K := S K) (k := S k) (U := U).
    + lia.
    + apply lc_ty_mono with (K1 := K).
      * exact HU.
      * lia.
    + assumption.
  - constructor.
  - constructor.
Qed.

Lemma lc_tm_ty_open_inv : forall K q j t U,
  q <= K -> lc_ty_at K U ->
  lc_tm_at K j (open_tm_ty_rec q U t) ->
  lc_tm_at (S K) j t.
Proof.
  intros K q j t; revert K q j.
  induction t; intros K q j U Hq HU H; simpl in H.
  - inversion H; apply lc_tm_bvar; lia.
  - constructor.
  - inversion H; subst.
    apply lc_tm_abs.
    + eapply lc_ty_open_inv.
      * exact Hq.
      * exact HU.
      * assumption.
    + eapply IHt.
      * exact Hq.
      * exact HU.
      * assumption.
  - inversion H; subst. apply lc_tm_app; eauto.
  - inversion H; subst. apply lc_tm_tabs.
    refine (IHt (S K) (S q) j U _ _ _).
    + lia.
    + assert (HK : K <= S K) by lia.
      exact (lc_ty_mono K U HU (S K) HK).
    + assumption.
  - inversion H; subst. apply lc_tm_tapp.
    + refine (IHt K q j U _ _ _).
      * exact Hq.
      * exact HU.
      * assumption.
    + refine (lc_ty_open_inv K q t0 U Hq HU _).
      assumption.
  - constructor.
  - inversion H; subst. apply lc_tm_div; eauto.
  - inversion H; subst. apply lc_tm_arith; eauto.
  - inversion H; subst. apply lc_tm_fix.
    + eapply lc_ty_open_inv.
      * exact Hq.
      * exact HU.
      * assumption.
    + eapply lc_ty_open_inv.
      * exact Hq.
      * exact HU.
      * assumption.
    + eauto.
    + eauto.
  - inversion H; subst. apply lc_tm_ifzero; eauto.
  - constructor.
  - constructor.
  - inversion H; subst. apply lc_tm_if; eauto.
Qed.

Lemma max_atom_in : forall x L, In x L -> x <= max_atom L.
Proof.
  intros x L H; induction L as [|y L IH].
  - inversion H.
  - simpl in *. destruct H as [<-|H].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; exact H|apply Nat.le_max_r].
Qed.

Lemma not_in_fresh : forall L, ~ In (fresh L) L.
Proof.
  intros L H.
  unfold fresh in *.
  pose proof (max_atom_in (S (max_atom L)) L H) as Q.
  lia.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> lc_ty_at 0 T.
Proof.
  intros Delta T H; induction H as
    [ Delta X HX
    | Delta T1 T2 H1 IH1 H2 IH2
    | L Delta T H IH
    | Delta
    | Delta ].
  - constructor.
  - apply lc_ty_arrow; eauto.
  - apply lc_ty_all.
    pose proof (H (fresh L) (not_in_fresh L)) as Q.
    pose proof (IH (fresh L) (not_in_fresh L)) as Qlc.
    refine (lc_ty_open_inv 0 0 T (Ty_FVar (fresh L)) (le_n 0) _ Qlc).
    constructor.
  - constructor.
  - constructor.
Qed.

Lemma erase_open_rty_tm_rec : forall k R u,
  erase (open_rty_tm_rec k u R) = erase R.
Proof.
  intros k R u; revert k; induction R; intros k; simpl; try reflexivity.
  - f_equal; [apply IHR1|apply IHR2].
  - apply IHR2.
  - f_equal. apply IHR.
Qed.

Lemma erase_open_rty_tm : forall R u,
  erase (open_rty_tm R u) = erase R.
Proof.
  intros; apply erase_open_rty_tm_rec.
Qed.

Lemma erase_open_rty_ty_rec : forall k R U,
  erase (open_rty_ty_rec k U R) = open_ty_rec k U (erase R).
Proof.
  intros k R U; revert k; induction R; intros k; simpl; try reflexivity.
  - f_equal; [apply IHR1|apply IHR2].
  - apply IHR2.
  - f_equal. apply IHR.
Qed.

Lemma erase_open_rty_ty : forall R U,
  erase (open_rty_ty R U) = open_ty (erase R) U.
Proof.
  intros; apply erase_open_rty_ty_rec.
Qed.

Lemma wf_rty_erase : forall Delta RGamma R,
  wf_rty Delta RGamma R -> wf_ty Delta (erase R).
Proof.
  intros Delta RGamma R H; induction H as
    [ L Delta RGamma T ps HT HQ
    | L Delta RGamma R1 R2 H1 IH1 H2 IH2
    | L Delta RGamma R1 R2 H1 IH1 H2 IH2
    | L Delta RGamma R H IH ].
  - exact HT.
  - simpl. apply WF_Arrow.
    + exact IH1.
    + specialize (IH2 (fresh L) (not_in_fresh L)).
      rewrite erase_open_rty_tm in IH2. exact IH2.
  - simpl.
    specialize (IH2 (fresh L) (not_in_fresh L)).
    rewrite erase_open_rty_tm in IH2. exact IH2.
  - simpl. apply (WF_All L Delta (erase R)). intros X HX.
    specialize (IH X HX). rewrite (erase_open_rty_ty R (Ty_FVar X)) in IH. exact IH.
Qed.

Lemma value_lc : forall v, value v -> locally_closed_tm v.
Proof.
  intros v H; destruct H as [T t H|t H|n|A B m b H| |].
  - exact H.
  - exact H.
  - constructor.
  - exact H.
  - constructor.
  - constructor.
Qed.

Lemma type_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T H; induction H as
    [ Delta Gamma x T HL HW
    | L Delta Gamma T1 t2 T2 HT HB IHB
    | Delta Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
    | L Delta Gamma t T HB IHB
    | Delta Gamma t T U H1 IH1 HU
    | Delta Gamma n
    | Delta Gamma t1 t2 H1 IH1 H2 IH2
    | Delta Gamma op t1 t2 H1 IH1 H2 IH2
    | L Delta Gamma A B metric body HA HB HM IHM HBody IHBody
    | Delta Gamma t t0 t1 T H1 IH1 H2 IH2 H3 IH3
    | Delta Gamma
    | Delta Gamma
    | Delta Gamma t1 t2 t3 T H1 IH1 H2 IH2 H3 IH3 ].
  - constructor.
  - unfold locally_closed_tm in *; apply lc_tm_abs.
    + eauto using wf_ty_lc.
    + pose proof (HB (fresh L) (not_in_fresh L)) as Q.
      assert (lc_tm_at 0 0 (open_tm t2 (tm_fvar (fresh L)))) as Qlc.
      { exact (IHB (fresh L) (not_in_fresh L)). }
      apply lc_tm_open_inv with (x := fresh L) in Qlc. exact Qlc.
  - unfold locally_closed_tm in *; apply lc_tm_app; eauto.
  - unfold locally_closed_tm in *; apply lc_tm_tabs.
    pose proof (HB (fresh L) (not_in_fresh L)) as Q.
    assert (lc_tm_at 0 0
      (open_tm_ty t (Ty_FVar (fresh L)))) as Qlc.
    { exact (IHB (fresh L) (not_in_fresh L)). }
    refine (lc_tm_ty_open_inv 0 0 0 t (Ty_FVar (fresh L))
      (le_n 0) _ Qlc).
    constructor.
  - unfold locally_closed_tm in *; apply lc_tm_tapp.
    + eauto.
    + eauto using wf_ty_lc.
  - constructor.
  - unfold locally_closed_tm in *; apply lc_tm_div; eauto.
  - unfold locally_closed_tm in *; apply lc_tm_arith; eauto.
  - unfold locally_closed_tm in *; apply lc_tm_fix.
    + eauto using wf_ty_lc.
    + eauto using wf_ty_lc.
    + pose proof (HM (fresh L) (not_in_fresh L)) as Q.
      assert (lc_tm_at 0 0 (open_tm metric (tm_fvar (fresh L)))) as Qlc.
      { exact (IHM (fresh L) (not_in_fresh L)). }
      apply lc_tm_open_inv with (x := fresh L) in Qlc. exact Qlc.
    + pose proof (HBody (fresh L) (fresh (fresh L :: L))
        (not_in_fresh L)
        (not_in_fresh (fresh L :: L))) as Q.
      assert (lc_tm_at 0 0
        (open_fix_body body (tm_fvar (fresh L))
          (tm_fvar (fresh (fresh L :: L))))) as Qlc.
      { exact (IHBody (fresh L) (fresh (fresh L :: L))
          (not_in_fresh L) (not_in_fresh (fresh L :: L))). }
      apply lc_tm_open_inv with (x := fresh (fresh L :: L)) in Qlc.
      apply lc_tm_open_inv with (k := 1) (x := fresh L) in Qlc.
      exact Qlc.
  - unfold locally_closed_tm in *; apply lc_tm_ifzero; eauto.
  - constructor.
  - constructor.
  - unfold locally_closed_tm in *; apply lc_tm_if; eauto.
Qed.

Lemma rtype_lc : forall Delta RGamma t R,
  has_rtype Delta RGamma t R -> locally_closed_tm t.
Proof.
  intros Delta RGamma t R H; induction H.
  - constructor.
  - eapply lc_tm_abs.
    + eauto using wf_ty_lc, wf_rty_erase.
    + pose proof (H0 (fresh L) (not_in_fresh L)) as Q.
      assert (locally_closed_tm (open_tm body (tm_fvar (fresh L)))) as Qlc.
      { match goal with
        | Hx : forall _ : atom, _ -> locally_closed_tm _ |- _ =>
            exact (Hx (fresh L) (not_in_fresh L))
        end. }
      unfold locally_closed_tm in Qlc.
      apply lc_tm_open_inv with (x := fresh L) in Qlc.
      exact Qlc.
  - unfold locally_closed_tm in *.
    apply lc_tm_app; assumption.
  - apply lc_tm_tabs.
    assert (locally_closed_tm
      (open_tm_ty body (Ty_FVar (fresh L)))) as Qlc.
    { match goal with
      | Hx : forall _ : atom, _ -> locally_closed_tm _ |- _ =>
          exact (Hx (fresh L) (not_in_fresh L))
      end. }
    unfold locally_closed_tm in Qlc.
    pose proof (lc_tm_ty_open_inv 0 0 0 body (Ty_FVar (fresh L))
      (le_n 0) (lc_ty_fvar 0 (fresh L)) Qlc) as Qbody.
    exact Qbody.
  - unfold locally_closed_tm in *; apply lc_tm_tapp.
    + assumption.
    + eauto using wf_ty_lc.
  - unfold locally_closed_tm in *; constructor; eauto.
  - unfold locally_closed_tm in *; constructor; eauto.
  - unfold locally_closed_tm in *; constructor; eauto.
  - unfold locally_closed_tm in *; constructor; eauto.
  - unfold locally_closed_tm in *; constructor; eauto.
  - unfold locally_closed_tm in *; constructor; eauto.
  - exact (value_lc v H0).
  - unfold locally_closed_tm in *.
    apply lc_tm_fix.
    + pose proof (wf_rty_erase Delta RGamma
        (R_Func (measured_input A p metric) R2) H) as W.
      simpl in W. inversion W; eauto using wf_ty_lc.
    + pose proof (wf_rty_erase Delta RGamma
        (R_Func (measured_input A p metric) R2) H) as W.
      simpl in W. inversion W; eauto using wf_ty_lc.
    + pose proof (H0 (fresh L) (not_in_fresh L)) as Q.
      pose proof (type_lc _ _ _ _ Q) as Qlc.
      unfold locally_closed_tm in Qlc.
      apply lc_tm_open_inv with (x := fresh L) in Qlc. exact Qlc.
    + pose proof (H2 (fresh L) (fresh (fresh L :: L))
        (not_in_fresh L) (not_in_fresh (fresh L :: L))) as Qlc.
      unfold locally_closed_tm in Qlc.
      apply lc_tm_open_inv with (x := fresh (fresh L :: L)) in Qlc.
      apply lc_tm_open_inv with (k := 1) (x := fresh L) in Qlc.
      exact Qlc.
  - unfold locally_closed_tm in *.
    apply lc_tm_ifzero.
    + constructor.
    + assumption.
    + assumption.
  - exact IHhas_rtype.
Qed.

Lemma lookup_erase : forall x RGamma R,
  lookup_rcontext x RGamma = Some R ->
  lookup_context x (erase_context RGamma) = Some (erase R).
Proof.
  intros x RGamma; induction RGamma as [|[y R0] RG IH]; intros R H.
  - inversion H.
  - simpl in H. simpl. destruct (Nat.eqb x y) eqn:E.
    + inversion H; reflexivity.
    + apply IH; exact H.
Qed.

(* raw erasure is not injective for the polymorphic subtype rule; the
   progress proof below therefore uses the refinement derivation directly. *)
(*
Lemma subtype_erase_eq : forall Delta RGamma R S,
  subtype Delta RGamma R S -> erase R = erase S.
Proof.
  intros Delta RGamma R S H; induction H.
  - reflexivity.
  - reflexivity.
  - simpl. f_equal.
    + symmetry; exact IHsubtype.
    + pose proof (H1 (fresh L) (not_in_fresh L)) as Q.
      repeat rewrite erase_open_rty_tm in Q. exact Q.
  - simpl. rewrite erase_open_rty_tm in IHsubtype. exact IHsubtype.
  - simpl. specialize (H2 (fresh L) (not_in_fresh L)).
    repeat rewrite erase_open_rty_tm in H2. exact H2.
  - simpl. specialize (H0 (fresh L) (not_in_fresh L)).
    rewrite erase_open_rty_ty in H0. exact H0.
  - simpl. specialize (IHsubtype (fresh L) (not_in_fresh L)).
    rewrite erase_open_rty_ty in IHsubtype. exact IHsubtype.
  - etransitivity; eauto.
Qed.

Lemma rtype_has_type : forall Delta RGamma t R,
  has_rtype Delta RGamma t R ->
  has_type Delta (erase_context RGamma) t (erase R).
Proof.
  intros Delta RGamma t R H; induction H.
  - apply T_Var; eauto using lookup_erase, wf_rty_erase.
  - apply T_Abs with (L := L).
    + eauto using wf_rty_erase.
    + intros x Hx.
      specialize (IHhas_rtype x Hx).
      simpl in *. rewrite erase_open_rty_tm in IHhas_rtype. exact IHhas_rtype.
  - simpl. apply T_App; eauto.
  - apply T_TAbs with (L := L).
    intros X HX. specialize (IHhas_rtype X HX).
    rewrite erase_open_rty_ty in IHhas_rtype. exact IHhas_rtype.
  - apply T_TApp; eauto using wf_ty_lc.
  - constructor.
  - apply T_Div; eauto.
  - apply T_Arith; eauto.
  - constructor.
  - constructor.
  - apply T_If; eauto.
  - exact H.
  - apply T_Fix with (L := L).
    + eauto using wf_rty_erase.
    + exact H0.
    + intros f x Hf Hx. specialize (IHhas_rtype f x Hf Hx).
      exact IHhas_rtype.
  - apply T_IfZero; eauto.
  - specialize (IHhas_rtype). rewrite (subtype_erase_eq _ _ _ _ H1) in IHhas_rtype.
    exact IHhas_rtype.
Qed.
*)

Lemma value_int : forall Gamma v,
  value v -> has_type [] Gamma v Ty_Int -> exists n : Z, v = tm_int n.
Proof.
  intros Gamma v Hv Ht; destruct Hv.
  - inversion Ht.
  - inversion Ht.
  - exists n; reflexivity.
  - inversion Ht.
  - inversion Ht.
  - inversion Ht.
Qed.

Lemma value_bool : forall Gamma v,
  value v -> has_type [] Gamma v Ty_Bool -> v = tm_true \/ v = tm_false.
Proof.
  intros Gamma v Hv Ht; destruct Hv.
  - inversion Ht.
  - inversion Ht.
  - inversion Ht.
  - inversion Ht.
  - left; reflexivity.
  - right; reflexivity.
Qed.

Lemma rtype_int_value : forall v p,
  has_rtype [] empty_rcontext v (R_Refine Ty_Int p) ->
  value v -> exists n : Z, v = tm_int n.
Proof.
  intros v p H Hv; dependent destruction H; simpl in *.
  all: try (inversion Hv).
  all: try (eexists; reflexivity).
  all: try (match goal with
    | Hx : has_type [] _ _ Ty_Int |- _ =>
        eapply value_int; [exact Hv | exact Hx]
    end).
  all: try match goal with
    | Hvx : value ?vv |- _ =>
        match goal with
        | Htx : has_type _ _ ?vv Ty_Int |- _ => exact (value_int _ _ Hvx Htx)
        end
    end.
  all: eauto.
  all: match goal with |- ?G => idtac G end.
Qed.

Lemma rtype_bool_value : forall v,
  has_rtype [] empty_rcontext v (R_Refine Ty_Bool Pred_True) ->
  value v -> v = tm_true \/ v = tm_false.
Proof.
  intros v H Hv; dependent destruction H; simpl in *; eauto using value_bool.
Qed.

Lemma rtype_fun_value : forall v R1 R2,
  has_rtype [] empty_rcontext v (R_Func R1 R2) ->
  value v ->
  (exists T b, v = tm_abs T b) \/
  (exists A B m b, v = tm_fix A B m b).
Proof.
  intros v R1 R2 H Hv; induction H; try discriminate.
  - left; eauto.
  - right; eauto.
  - eauto.
Qed.

Lemma ne_int_zero : forall n,
  qualifier_holds (Pred_Ne (tm_int n) (tm_int 0%Z)) -> n <> 0%Z.
Proof.
  intros n H E; subst n; apply H.
  exists (tm_int 0%Z); repeat split; constructor; try constructor.
Qed.

Lemma progress_closed : forall t R,
  has_rtype [] empty_rcontext t R ->
  value t \/ exists t', t --> t'.
Proof.
  intros t R H; induction H.
  - simpl in H; discriminate.
  - left; apply v_abs; apply rtype_lc; assumption.
  - destruct IHhas_rtype1 as [V1|[u S1]].
    + destruct IHhas_rtype2 as [V2|[u S2]].
      * destruct (rtype_fun_value _ _ _ H V1) as [[T b ->]|[A B m b ->]].
        -- right; exists (open_tm b V2); apply ST_AppAbs; eauto.
        -- right; exists (open_fix_body b (tm_fix A B m b) V2); apply ST_AppFix; eauto.
      * right; exists (tm_app (tm_abs (erase R1) body) u); apply ST_App2; eauto.
    + right; exists (tm_app u0 t2); apply ST_App1; eauto using rtype_lc.
  - left; apply v_tabs; apply rtype_lc; assumption.
  - destruct IHhas_rtype as [V|[u S]].
    + destruct V as [T b Hlc|b Hlc|n|A B m b Hlc| |].
      * discriminate.
      * right; exists (open_tm_ty b U); apply ST_TAppTabs; eauto.
      * discriminate.
      * discriminate.
      * discriminate.
      * discriminate.
    + right; exists (tm_tapp u U); apply ST_TApp; eauto.
  - left; apply v_int.
  - destruct IHhas_rtype1 as [V1|[u S1]].
    + destruct IHhas_rtype2 as [V2|[u S2]].
      * destruct (rtype_int_value _ _ H V1) as [n ->].
        destruct (rtype_int_value _ _ H0 V2) as [m ->].
        right; exists (tm_int (Z.div n m)); apply ST_DivInt.
        apply ne_int_zero.
        exact H3.
      * right; exists (tm_div v u); apply ST_Div2; eauto.
    + right; exists (tm_div u t2); apply ST_Div1; eauto using rtype_lc.
  - destruct IHhas_rtype1 as [V1|[u S1]].
    + destruct IHhas_rtype2 as [V2|[u S2]].
      * destruct (rtype_int_value _ _ H V1) as [n ->].
        destruct (rtype_int_value _ _ H0 V2) as [m ->].
        right; exists (tm_int (eval_integer_operator op n m)); apply ST_ArithInt.
      * right; exists (tm_arith op v u); apply ST_Arith2; eauto.
    + right; exists (tm_arith op u t2); apply ST_Arith1; eauto using rtype_lc.
  - left; constructor.
  - left; constructor.
  - destruct IHhas_rtype1 as [V|[u S]].
    + destruct (rtype_bool_value _ H V) as [->|->].
      * right; exists t2; apply ST_IfTrue; eauto using rtype_lc.
      * right; exists t3; apply ST_IfFalse; eauto using rtype_lc.
    + right; exists (tm_if u t2 t3); apply ST_If; eauto using rtype_lc.
  - left; exact H0.
  - left; apply v_fix; apply rtype_lc; assumption.
  - simpl in H; discriminate.
  - exact IHhas_rtype.
Qed.

Theorem never_stuck : forall (t t' : tm) (R : rty),
  has_rtype [] empty_rcontext t R ->
  multi t t' ->
  value t' \/ exists t'' : tm, t' --> t''.
Proof.

Qed.

End SystemFRefinementIfRecursionTask.
