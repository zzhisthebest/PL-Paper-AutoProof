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

Lemma erase_open_rty_tm_rec : forall R k u,
  erase (open_rty_tm_rec k u R) = erase R.
Proof.
  induction R; intros; simpl; try rewrite IHR; try rewrite IHR1; try rewrite IHR2; reflexivity.
Qed.

Lemma erase_open_rty_tm : forall R u, erase (open_rty_tm R u) = erase R.
Proof. intros; apply erase_open_rty_tm_rec. Qed.

Lemma erase_open_rty_ty_rec : forall R k U,
  erase (open_rty_ty_rec k U R) = open_ty_rec k U (erase R).
Proof.
  induction R; intros; simpl; try rewrite IHR; try rewrite IHR1; try rewrite IHR2; reflexivity.
Qed.

Lemma erase_open_rty_ty : forall R U, erase (open_rty_ty R U) = open_ty (erase R) U.
Proof. intros; apply erase_open_rty_ty_rec. Qed.

Lemma lookup_erasure : forall RGamma x R,
  lookup_rcontext x RGamma = Some R ->
  lookup_context x (erase_context RGamma) = Some (erase R).
Proof.
  induction RGamma as [|[y S] RGamma IH]; intros x R H; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + inversion H; subst. simpl. reflexivity.
    + simpl. eapply IH; eauto.
Qed.

Lemma max_atom_member : forall L x, In x L -> x <= max_atom L.
Proof.
  induction L as [|a L IH]; simpl; intros x H; [contradiction|].
  destruct H as [->|H].
  - apply Nat.le_max_l.
  - eapply Nat.le_trans; [eapply IH; eassumption|apply Nat.le_max_r].
Qed.

Lemma fresh_notin : forall L, ~ In (fresh L) L.
Proof.
  intros L H. unfold fresh in H.
  pose proof (max_atom_member L (S (max_atom L)) H).
  lia.
Qed.

Lemma open_ty_rec_injective : forall k X T U,
  ~ In X (fv_ty T) -> ~ In X (fv_ty U) ->
  open_ty_rec k (Ty_FVar X) T = open_ty_rec k (Ty_FVar X) U -> T = U.
Proof.
  intros k X T. revert k X.
  induction T as [n|Y|T1 IH1 T2 IH2|T1 IH| |];
    intros k X U HXT HXU Heq; destruct U; simpl in *; try congruence.
  - destruct (Nat.eqb k n) eqn:E1; destruct (Nat.eqb k n0) eqn:E2;
      simpl in Heq; try discriminate; inversion Heq; subst; try reflexivity;
      apply Nat.eqb_eq in E1; apply Nat.eqb_eq in E2; congruence.
  - destruct (Nat.eqb k n) eqn:E; simpl in Heq; try discriminate.
    inversion Heq; subst. exfalso. apply HXU. simpl. auto.
  - destruct (Nat.eqb k n) eqn:E; simpl in Heq; discriminate.
  - destruct (Nat.eqb k n) eqn:E; simpl in Heq; discriminate.
  - destruct (Nat.eqb k n) eqn:E; simpl in Heq; discriminate.
  - destruct (Nat.eqb k n) eqn:E; simpl in Heq; discriminate.
  - destruct (Nat.eqb k n) eqn:E; simpl in Heq; try discriminate.
    inversion Heq; subst. exfalso. apply HXT. simpl. auto.
  - destruct (Nat.eqb k n) eqn:E; simpl in Heq; discriminate.
  - inversion Heq; subst. f_equal.
    + eapply (IH1 k X U1).
      * intro Hin; apply HXT; apply in_or_app; left; exact Hin.
      * intro Hin; apply HXU; apply in_or_app; left; exact Hin.
      * exact H0.
    + eapply (IH2 k X U2).
      * intro Hin; apply HXT; apply in_or_app; right; exact Hin.
      * intro Hin; apply HXU; apply in_or_app; right; exact Hin.
      * exact H1.
  - destruct (Nat.eqb k n) eqn:E; simpl in Heq; discriminate.
  - inversion Heq; subst. f_equal. eapply IH; eauto.
  - destruct (Nat.eqb k n) eqn:E; simpl in Heq; discriminate.
  - destruct (Nat.eqb k n) eqn:E; simpl in Heq; discriminate.
Qed.

Lemma subtype_erase : forall Delta RGamma R S,
  subtype Delta RGamma R S -> erase R = erase S.
Proof.
  intros Delta RGamma R S H.
  induction H; simpl in *; try reflexivity.
  - f_equal.
    + symmetry; exact IHsubtype.
    + specialize (H1 (fresh L) (fresh_notin L)).
      rewrite !erase_open_rty_tm in H1. exact H1.
  - rewrite erase_open_rty_tm in IHsubtype. exact IHsubtype.
  - specialize (H2 (fresh L) (fresh_notin L)).
    rewrite erase_open_rty_tm in H2. exact H2.
  - f_equal.
    pose (X := fresh (L ++ fv_ty (erase R) ++ fv_ty (erase S))).
    assert (HX : ~ In X L).
    { unfold X. intro Hin. apply (fresh_notin (L ++ fv_ty (erase R) ++ fv_ty (erase S))).
      apply in_or_app; left; exact Hin. }
    assert (HXR : ~ In X (fv_ty (erase R))).
    { unfold X. intro Hin. apply (fresh_notin (L ++ fv_ty (erase R) ++ fv_ty (erase S))).
      apply in_or_app; right. apply in_or_app; left; exact Hin. }
    assert (HXS : ~ In X (fv_ty (erase S))).
    { unfold X. intro Hin. apply (fresh_notin (L ++ fv_ty (erase R) ++ fv_ty (erase S))).
      apply in_or_app; right. apply in_or_app; right; exact Hin. }
    specialize (H0 X HX). rewrite !erase_open_rty_ty in H0.
    change (erase R = erase S).
    eapply (open_ty_rec_injective 0 X (erase R) (erase S)); eauto.
  - congruence.
Qed.

Lemma wf_rty_erase : forall Delta RGamma R,
  wf_rty Delta RGamma R -> wf_ty Delta (erase R).
Proof.
  intros Delta RGamma R H. induction H; simpl in *; eauto using wf_ty.
  - apply WF_Arrow; [exact IHwf_rty|].
    specialize (H1 (fresh L) (fresh_notin L)).
    rewrite erase_open_rty_tm in H1. exact H1.
  - specialize (H1 (fresh L) (fresh_notin L)).
    rewrite erase_open_rty_tm in H1. exact H1.
  - eapply WF_All with (L := L). intros X HX.
    specialize (H0 X HX). rewrite erase_open_rty_ty in H0. exact H0.
Qed.

Lemma lookup_update_same : forall Gamma x T,
  lookup_context x Gamma = Some T ->
  forall y, lookup_context y (update Gamma x T) = lookup_context y Gamma.
Proof.
  intros Gamma x T H y. unfold update. simpl.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst y. symmetry. exact H.
  - reflexivity.
Qed.

Lemma update_contexts_equiv : forall Gamma Gamma' x T,
  (forall y, lookup_context y Gamma = lookup_context y Gamma') ->
  forall y, lookup_context y (update Gamma x T) =
            lookup_context y (update Gamma' x T).
Proof.
  intros Gamma Gamma' x T Heq y. unfold update. simpl.
  destruct (Nat.eqb y x); [reflexivity|apply Heq].
Qed.

Lemma has_type_context_equiv : forall Delta Gamma t T,
  has_type Delta Gamma t T -> forall Gamma',
  (forall x, lookup_context x Gamma = lookup_context x Gamma') ->
  has_type Delta Gamma' t T.
Proof.
  intros Delta Gamma t T H. induction H; intros Gamma' Heq.
  - eapply T_Var; [rewrite <- Heq; eassumption|assumption].
  - eapply T_Abs with (L := L); [assumption|].
    intros x Hx. eapply (H1 x Hx).
    apply update_contexts_equiv. exact Heq.
  - eapply T_App; [eapply IHhas_type1|eapply IHhas_type2]; exact Heq.
  - eapply T_TAbs with (L := L). intros X HX.
    exact (H0 X HX Gamma' Heq).
  - eapply T_TApp; [eapply IHhas_type|assumption]; exact Heq.
  - constructor.
  - eapply T_Div; [eapply IHhas_type1|eapply IHhas_type2]; exact Heq.
  - eapply T_Arith; [eapply IHhas_type1|eapply IHhas_type2]; exact Heq.
  - eapply T_Fix with (L := L); try assumption.
    + intros x Hx.
      exact (H2 x Hx (update Gamma' x A)
        (update_contexts_equiv Gamma Gamma' x A Heq)).
    + intros f x Hf Hx.
      pose proof (update_contexts_equiv Gamma Gamma' x A Heq) as Ex.
      pose proof (update_contexts_equiv (update Gamma x A) (update Gamma' x A)
        f (Ty_Arrow A B) Ex) as Ef.
      exact (H4 f x Hf Hx
        (update (update Gamma' x A) f (Ty_Arrow A B)) Ef).
  - eapply T_IfZero; [eapply IHhas_type1|eapply IHhas_type2|eapply IHhas_type3]; exact Heq.
  - constructor.
  - constructor.
  - eapply T_If; [eapply IHhas_type1|eapply IHhas_type2|eapply IHhas_type3]; exact Heq.
Qed.

Lemma lc_open_tm_rec_inv : forall t K k x,
  lc_tm_at K k (open_tm_rec k (tm_fvar x) t) -> lc_tm_at K (S k) t.
Proof.
  induction t; intros K k x Hlc; simpl in Hlc.
  - { destruct (Nat.eqb k n) eqn:E.
    + constructor. apply Nat.eqb_eq in E. lia.
    + inversion Hlc; subst. constructor. lia. }
  - { inversion Hlc; subst. constructor. }
  - { inversion Hlc; subst. econstructor; eauto. }
  - { inversion Hlc; subst. econstructor; eauto. }
  - { inversion Hlc; subst. econstructor; eauto. }
  - { inversion Hlc; subst. econstructor; eauto. }
  - { inversion Hlc; subst. constructor. }
  - { inversion Hlc; subst. econstructor; eauto. }
  - { inversion Hlc; subst. econstructor; eauto. }
  - { inversion Hlc; subst. econstructor; eauto. }
  - { inversion Hlc; subst. econstructor; eauto. }
  - { inversion Hlc; subst. econstructor; eauto. }
  - { constructor. }
  - { inversion Hlc; subst. econstructor; eauto. }
Qed.

Lemma lc_open_ty_rec_inv : forall T k X,
  lc_ty_at k (open_ty_rec k (Ty_FVar X) T) -> lc_ty_at (S k) T.
Proof.
  induction T; intros k X Hlc; simpl in Hlc.
  - destruct (Nat.eqb k n) eqn:E.
    + constructor. apply Nat.eqb_eq in E. lia.
    + inversion Hlc; subst. constructor. lia.
  - inversion Hlc; subst. constructor.
  - inversion Hlc; subst. econstructor; eauto.
  - inversion Hlc; subst. econstructor; eauto.
  - constructor.
  - constructor.
Qed.

Lemma lc_open_tm_rec_identity : forall t K k,
  lc_tm_at K k t -> forall j u, open_tm_rec (k + j) u t = t.
Proof.
  induction t; intros K k Hlc j u; simpl in *.
  - inversion Hlc; subst. destruct (Nat.eqb (k + j) n) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + reflexivity.
  - reflexivity.
  - inversion Hlc; subst. f_equal. replace (S (k + j)) with (S k + j) by lia.
    eapply IHt; eauto.
  - inversion Hlc; subst. f_equal; eauto.
  - inversion Hlc; subst. f_equal. eapply IHt; eauto.
  - inversion Hlc; subst. f_equal. eapply IHt; eauto.
  - reflexivity.
  - inversion Hlc; subst. f_equal; eauto.
  - inversion Hlc; subst. f_equal; eauto.
  - inversion Hlc; subst. f_equal.
    + replace (S (k + j)) with (S k + j) by lia. eapply IHt1; eauto.
    + replace (S (S (k + j))) with (S (S k) + j) by lia. eapply IHt2; eauto.
  - inversion Hlc; subst. f_equal; eauto.
  - reflexivity.
  - reflexivity.
  - inversion Hlc; subst. f_equal; eauto.
Qed.

Lemma lc_open_ty_rec_identity : forall T K,
  lc_ty_at K T -> forall j U, open_ty_rec (K + j) U T = T.
Proof.
  induction T; intros K Hlc j U; simpl in *.
  - inversion Hlc; subst. destruct (Nat.eqb (K + j) n) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + reflexivity.
  - reflexivity.
  - inversion Hlc; subst. f_equal; eauto.
  - inversion Hlc; subst. f_equal.
    replace (S (K + j)) with (S K + j) by lia. eapply IHT; eauto.
  - reflexivity.
  - reflexivity.
Qed.

Lemma lc_open_tm_ty_rec_identity : forall t K k,
  lc_tm_at K k t -> forall j U, open_tm_ty_rec (K + j) U t = t.
Proof.
  induction t; intros K k Hlc j U; simpl in *.
  - inversion Hlc; reflexivity.
  - reflexivity.
  - inversion Hlc; subst. f_equal.
    + eapply lc_open_ty_rec_identity with (K := K); eauto.
    + eapply IHt; eauto.
  - inversion Hlc; subst. f_equal; eauto.
  - inversion Hlc; subst. f_equal. replace (S (K + j)) with (S K + j) by lia.
    eapply IHt; eauto.
  - inversion Hlc; subst. f_equal.
    + eapply IHt; eauto.
    + eapply lc_open_ty_rec_identity with (K := K); eauto.
  - reflexivity.
  - inversion Hlc; subst. f_equal; eauto.
  - inversion Hlc; subst. f_equal; eauto.
  - inversion Hlc; subst. f_equal.
    + eapply lc_open_ty_rec_identity with (K := K); eauto.
    + eapply lc_open_ty_rec_identity with (K := K); eauto.
    + eapply IHt1; eauto.
    + eapply IHt2; eauto.
  - inversion Hlc; subst. f_equal; eauto.
  - reflexivity.
  - reflexivity.
  - inversion Hlc; subst. f_equal; eauto.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> lc_ty_at 0 T.
Proof.
  intros Delta T H. induction H.
  - constructor.
  - econstructor; eauto.
  - econstructor. specialize (H0 (fresh L) (fresh_notin L)).
    eapply lc_open_ty_rec_inv. exact H0.
  - constructor.
  - constructor.
Qed.

Lemma lc_ty_mono : forall K T, lc_ty_at K T -> lc_ty_at (S K) T.
Proof.
  intros K T H. induction H; econstructor; eauto; lia.
Qed.

Lemma lc_tm_monoK : forall K k t, lc_tm_at K k t -> lc_tm_at (S K) k t.
Proof.
  intros K k t H. induction H; econstructor; eauto using lc_ty_mono; lia.
Qed.

Lemma lc_tm_monok : forall K k t, lc_tm_at K k t -> lc_tm_at K (S k) t.
Proof.
  intros K k t H. induction H; econstructor; eauto; lia.
Qed.

Lemma lc_ty_instantiate : forall theta K T,
  lc_ty_at K T ->
  (forall X, lc_ty_at K (theta X)) ->
  lc_ty_at K (instantiate_ty theta T).
Proof.
  intros theta K T Hlc. induction Hlc; intros Htheta; simpl.
  - constructor. assumption.
  - apply Htheta.
  - econstructor; [eapply IHHlc1|eapply IHHlc2]; eauto.
  - econstructor. apply IHHlc.
    intro X. eapply lc_ty_mono. apply Htheta.
  - constructor.
  - constructor.
Qed.

Lemma lc_tm_instantiate : forall theta gamma K k t,
  lc_tm_at K k t ->
  (forall X, lc_ty_at K (theta X)) ->
  (forall x, locally_closed_tm (gamma x)) ->
  lc_tm_at K k (instantiate theta gamma t).
Proof.
  intros theta gamma K k t Hlc. induction Hlc; intros Htheta Hgamma; simpl.
  - constructor. assumption.
  - unfold locally_closed_tm in Hgamma.
    assert (HgK : lc_tm_at K 0 (gamma x)).
    { clear Htheta. induction K; [exact (Hgamma x)|].
      apply lc_tm_monoK. exact IHK. }
    clear Htheta.
    induction k; [exact HgK|]. eapply lc_tm_monok. exact IHk.
  - econstructor.
    + eapply lc_ty_instantiate; eauto.
    + eapply IHHlc; eauto.
  - econstructor; [eapply IHHlc1|eapply IHHlc2]; eauto.
  - econstructor. eapply IHHlc.
    + intro X. eapply lc_ty_mono. apply Htheta.
    + exact Hgamma.
  - econstructor.
    + eapply IHHlc; eauto.
    + eapply lc_ty_instantiate; eauto.
  - constructor.
  - econstructor; [eapply IHHlc1|eapply IHHlc2]; eauto.
  - econstructor; [eapply IHHlc1|eapply IHHlc2]; eauto.
  - econstructor.
    + eapply lc_ty_instantiate; eauto.
    + eapply lc_ty_instantiate; eauto.
    + eapply IHHlc1; eauto.
    + eapply IHHlc2; eauto.
  - econstructor; [eapply IHHlc1|eapply IHHlc2|eapply IHHlc3]; eauto.
  - constructor.
  - constructor.
  - econstructor; [eapply IHHlc1|eapply IHHlc2|eapply IHHlc3]; eauto.
Qed.

Lemma lc_tm_ty_open_rec_inv : forall t K k X,
  lc_tm_at K k (open_tm_ty_rec K (Ty_FVar X) t) -> lc_tm_at (S K) k t.
Proof.
  induction t; intros K k X Hlc; simpl in Hlc.
  - inversion Hlc; subst. eapply lc_tm_monoK. eassumption.
  - inversion Hlc; subst. constructor.
  - inversion Hlc; subst. econstructor.
    + eapply lc_open_ty_rec_inv. eassumption.
    + eapply IHt. eassumption.
  - inversion Hlc; subst. econstructor; eauto.
  - inversion Hlc; subst. econstructor. eapply IHt. eassumption.
  - inversion Hlc; subst. econstructor; eauto using lc_open_ty_rec_inv.
  - constructor.
  - inversion Hlc; subst. econstructor; eauto.
  - inversion Hlc; subst. econstructor; eauto.
  - inversion Hlc; subst. econstructor; eauto using lc_open_ty_rec_inv.
  - inversion Hlc; subst. econstructor; eauto.
  - constructor.
  - constructor.
  - inversion Hlc; subst. econstructor; eauto.
Qed.

Lemma has_type_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> lc_tm_at 0 0 t.
Proof.
  intros Delta Gamma t T H. induction H; simpl in *; eauto using lc_ty_mono.
  - constructor.
  - econstructor.
    + eapply wf_ty_lc; eassumption.
    + eapply lc_open_tm_rec_inv with (x := fresh L).
      apply H1. apply fresh_notin.
  - econstructor; eauto.
  - econstructor. eapply lc_tm_ty_open_rec_inv with (X := fresh L).
    apply H0. apply fresh_notin.
  - econstructor; eauto using wf_ty_lc.
  - constructor.
  - econstructor; eauto.
  - econstructor; eauto.
  - eapply lc_tm_fix.
    + eapply wf_ty_lc; eassumption.
    + eapply wf_ty_lc; eassumption.
    + eapply lc_open_tm_rec_inv with (x := fresh L). apply H2. apply fresh_notin.
    + pose (f := fresh L). pose (x := fresh (f :: L)).
      assert (Hf : ~ In f L) by (unfold f; apply fresh_notin).
      assert (Hx : ~ In x (f :: L)) by (unfold x; apply fresh_notin).
      specialize (H4 f x Hf Hx). unfold open_fix_body, open_tm in H4.
      eapply lc_open_tm_rec_inv with (x := f) (k := 1).
      eapply lc_open_tm_rec_inv with (x := x) (k := 0). exact H4.
  - econstructor; eauto.
  - constructor.
  - constructor.
  - econstructor; eauto.
Qed.

Lemma has_rtype_erases : forall Delta RGamma t R,
  has_rtype Delta RGamma t R ->
  has_type Delta (erase_context RGamma) t (erase R).
Proof.
  intros Delta RGamma t R H. induction H; simpl in *; eauto using has_type.
  - eapply T_Var.
    + eapply lookup_erasure; eassumption.
    + eapply wf_rty_erase; eassumption.
  - eapply T_Abs with (L := L).
    + eapply wf_rty_erase; eassumption.
    + intros x Hx. specialize (H1 x Hx).
      rewrite erase_open_rty_tm in H1. exact H1.
  - eapply T_TAbs with (L := L). intros X HX.
    specialize (H0 X HX). rewrite erase_open_rty_ty in H0. exact H0.
  - rewrite erase_open_rty_ty. eapply T_TApp; eauto.
  - assert (HwfArrow : wf_ty Delta (Ty_Arrow A (erase R2))).
    { change (wf_ty Delta (erase (R_Func (measured_input A p metric) R2))).
      eapply wf_rty_erase; exact H. }
    inversion HwfArrow; subst.
    eapply T_Fix with (L := L).
    + assumption.
    + assumption.
    + exact H0.
    + intros f x Hf Hx. specialize (H2 f x Hf Hx).
      rewrite erase_open_rty_tm in H2. exact H2.
  - eapply T_IfZero with (T := erase R).
    + eapply T_Var.
      * pose proof (lookup_erasure RGamma x (R_Refine Ty_Int p) H) as Hl.
        simpl in Hl. exact Hl.
      * apply WF_Int.
    + eapply (has_type_context_equiv Delta
        (update (erase_context RGamma) x Ty_Int) t0 (erase R)
        IHhas_rtype1 (erase_context RGamma)).
      intros y. apply lookup_update_same.
      pose proof (lookup_erasure RGamma x (R_Refine Ty_Int p) H) as Hl.
      simpl in Hl. exact Hl.
    + eapply (has_type_context_equiv Delta
        (update (erase_context RGamma) x Ty_Int) t1 (erase R)
        IHhas_rtype2 (erase_context RGamma)).
      intros y. apply lookup_update_same.
      pose proof (lookup_erasure RGamma x (R_Refine Ty_Int p) H) as Hl.
      simpl in Hl. exact Hl.
  - rewrite <- (subtype_erase _ _ _ _ H1). exact IHhas_rtype.
Qed.

Lemma canonical_int : forall v,
  has_type [] empty v Ty_Int -> value v -> exists n, v = tm_int n.
Proof.
  intros v Hty Hv. inversion Hv; subst; inversion Hty; subst; eauto.
Qed.

Lemma canonical_bool : forall v,
  has_type [] empty v Ty_Bool -> value v -> v = tm_true \/ v = tm_false.
Proof.
  intros v Hty Hv. inversion Hv; subst; inversion Hty; subst; eauto.
Qed.

Lemma canonical_arrow : forall v A B,
  has_type [] empty v (Ty_Arrow A B) -> value v ->
  (exists T body, v = tm_abs T body) \/
  (exists metric body, v = tm_fix A B metric body).
Proof.
  intros v A B Hty Hv. inversion Hv; subst; inversion Hty; subst; eauto.
Qed.

Lemma entails_holds : forall Delta RGamma p q,
  entails Delta RGamma p q -> forall theta gamma,
  (forall x, value (gamma x)) ->
  context_formulas_hold theta gamma RGamma ->
  qualifier_holds (instantiate_formula theta gamma p) ->
  qualifier_holds (instantiate_formula theta gamma q).
Proof.
  intros Delta RGamma p q Hent. induction Hent;
    intros theta gamma Hvalues Hcontext Hp; simpl in *; try tauto.
  - exact I.
  - eapply IHHent2; eauto.
  - exact (proj1 Hp).
  - exact (proj2 Hp).
  - split; [eapply IHHent1|eapply IHHent2]; eauto.
  - left; exact Hp.
  - right; exact Hp.
  - change (qualifier_holds (instantiate_formula theta gamma p) \/
      qualifier_holds (instantiate_formula theta gamma q)) in Hp.
    destruct Hp as [Hp|Hq].
    + eapply IHHent1; eauto.
    + eapply IHHent2; eauto.
  - intro Hq. apply (IHHent _ _ Hvalues Hcontext). split; assumption.
  - destruct Hp as [Hp Hnot]. contradiction.
  - specialize (Hcontext x T p H). exact Hcontext.
  - contradiction.
  - eapply H; eauto.
Qed.

Lemma qualifier_int_eq : forall n : Z,
  qualifier_holds (Pred_Eq (tm_int n) (tm_int n)).
Proof.
  intros n. unfold qualifier_holds, predicate_holds, interpret_qualifier.
  simpl. exists (tm_int n). repeat split; try constructor.
Qed.

Lemma multi_int_stays : forall n u, multi (tm_int n) u -> u = tm_int n.
Proof.
  intros n u H. dependent induction H.
  - reflexivity.
  - dependent destruction H.
Qed.

Lemma predicate_int_stays : forall n u,
  predicate_multistep (tm_int n) u -> u = tm_int n.
Proof.
  intros n u H. dependent induction H.
  - reflexivity.
  - dependent destruction H.
Qed.

Lemma qualifier_int_ne_zero : forall n : Z, n <> 0%Z ->
  qualifier_holds (Pred_Ne (tm_int n) (tm_int 0%Z)).
Proof.
  intros n Hn. unfold Pred_Ne, qualifier_holds, predicate_holds, interpret_qualifier.
  simpl. intro Heq. destruct Heq as [v [H1 [H2 Hv]]].
  pose proof (predicate_int_stays n v H1) as E1.
  pose proof (predicate_int_stays 0%Z v H2) as E2.
  subst v. inversion E2; subst. apply Hn. reflexivity.
Qed.

Fixpoint instantiate_rty (theta : type_substitution)
    (gamma : term_substitution) (R : rty) : rty :=
  match R with
  | R_Refine T p => R_Refine (instantiate_ty theta T)
      (instantiate_formula theta gamma p)
  | R_Func R1 R2 => R_Func (instantiate_rty theta gamma R1)
      (instantiate_rty theta gamma R2)
  | R_Exists R1 R2 => R_Exists (instantiate_rty theta gamma R1)
      (instantiate_rty theta gamma R2)
  | R_Poly R1 => R_Poly (instantiate_rty theta gamma R1)
  end.

Definition extend_term_substitution (gamma : term_substitution)
    (x : atom) (s : tm) : term_substitution :=
  fun y => if Nat.eqb y x then s else gamma y.

Fixpoint fv_qualifier (p : qualifier) : list atom :=
  match p with
  | Pred_True | Pred_False => []
  | Pred_Eq t1 t2 | Pred_Lt t1 t2 | Pred_Le t1 t2 => fv_tm t1 ++ fv_tm t2
  | Pred_And p1 p2 | Pred_Or p1 p2 => fv_qualifier p1 ++ fv_qualifier p2
  | Pred_Not p1 => fv_qualifier p1
  end.

Fixpoint fv_rty (R : rty) : list atom :=
  match R with
  | R_Refine _ p => fv_qualifier p
  | R_Func R1 R2 | R_Exists R1 R2 => fv_rty R1 ++ fv_rty R2
  | R_Poly R1 => fv_rty R1
  end.

Fixpoint fv_rcontext (RGamma : rcontext) : list atom :=
  match RGamma with
  | [] => []
  | (_, R) :: RGamma' => fv_rty R ++ fv_rcontext RGamma'
  end.

Lemma lookup_rcontext_fv : forall RGamma y R x,
  lookup_rcontext y RGamma = Some R -> In x (fv_rty R) ->
  In x (fv_rcontext RGamma).
Proof.
  induction RGamma as [|[z S] RGamma IH]; intros y R x Hlook Hin; simpl in *.
  - discriminate.
  - destruct (Nat.eqb y z) eqn:E.
    + inversion Hlook; subst. apply in_or_app; left; exact Hin.
    + apply in_or_app; right. eapply IH; eassumption.
Qed.

Inductive core_value : ty -> tm -> Prop :=
  | CV_Int : forall n, core_value Ty_Int (tm_int n)
  | CV_True : core_value Ty_Bool tm_true
  | CV_False : core_value Ty_Bool tm_false
  | CV_Abs : forall T t T2,
      core_value (Ty_Arrow T T2) (tm_abs T t)
  | CV_Fix : forall A B metric body,
      core_value (Ty_Arrow A B) (tm_fix A B metric body)
  | CV_Tabs : forall t T, core_value (Ty_All T) (tm_tabs t).

Lemma has_type_value_core : forall Delta Gamma v T,
  has_type Delta Gamma v T -> value v -> core_value T v.
Proof.
  intros Delta Gamma v T Hty Hv. inversion Hv; subst; inversion Hty; subst;
    eauto using core_value.
Qed.

Lemma core_value_instantiate : forall theta gamma T v,
  core_value T v ->
  core_value (instantiate_ty theta T) (instantiate theta gamma v).
Proof.
  intros theta gamma T v H; inversion H; subst; simpl; eauto using core_value.
Qed.

Lemma instantiate_value : forall theta gamma v,
  (forall X, locally_closed_ty (theta X)) ->
  (forall x, locally_closed_tm (gamma x)) ->
  value v -> value (instantiate theta gamma v).
Proof.
  intros theta gamma v Htheta Hgamma Hv. inversion Hv; subst; simpl.
  - apply v_abs. change (lc_tm_at 0 0 (instantiate theta gamma (tm_abs T t))).
    eapply lc_tm_instantiate; [|exact Htheta|exact Hgamma].
    inversion H; subst; assumption.
  - apply v_tabs. change (lc_tm_at 0 0 (instantiate theta gamma (tm_tabs t))).
    eapply lc_tm_instantiate; [|exact Htheta|exact Hgamma].
    inversion H; subst; assumption.
  - constructor.
  - apply v_fix. change (lc_tm_at 0 0 (instantiate theta gamma (tm_fix A B metric body))).
    eapply lc_tm_instantiate; [|exact Htheta|exact Hgamma].
    inversion H; subst; assumption.
  - constructor.
  - constructor.
Qed.

Lemma instantiate_away : forall t theta gamma x s,
  ~ In x (fv_tm t) ->
  instantiate theta (extend_term_substitution gamma x s) t =
  instantiate theta gamma t.
Proof.
  induction t; intros theta gamma x s Haway; simpl in *.
  - reflexivity.
  - assert (Hneq : a <> x).
    { intro Heq; subst a. apply Haway. simpl; auto. }
    unfold extend_term_substitution. destruct (Nat.eqb a x) eqn:E.
    + apply Nat.eqb_eq in E. contradiction.
    + reflexivity.
  - f_equal. apply IHt. exact Haway.
  - assert (H1 : ~ In x (fv_tm t1)).
    { intro Hin; apply Haway; apply in_or_app; left; exact Hin. }
    assert (H2 : ~ In x (fv_tm t2)).
    { intro Hin; apply Haway; apply in_or_app; right; exact Hin. }
    f_equal; [eapply IHt1|eapply IHt2]; eauto.
  - f_equal. apply IHt. exact Haway.
  - f_equal. apply IHt. exact Haway.
  - reflexivity.
  - assert (H1 : ~ In x (fv_tm t1)).
    { intro Hin; apply Haway; apply in_or_app; left; exact Hin. }
    assert (H2 : ~ In x (fv_tm t2)).
    { intro Hin; apply Haway; apply in_or_app; right; exact Hin. }
    f_equal; [eapply IHt1|eapply IHt2]; eauto.
  - assert (H1 : ~ In x (fv_tm t1)).
    { intro Hin; apply Haway; apply in_or_app; left; exact Hin. }
    assert (H2 : ~ In x (fv_tm t2)).
    { intro Hin; apply Haway; apply in_or_app; right; exact Hin. }
    f_equal; [eapply IHt1|eapply IHt2]; eauto.
  - assert (H1 : ~ In x (fv_tm t3)).
    { intro Hin; apply Haway; apply in_or_app; left; exact Hin. }
    assert (H2 : ~ In x (fv_tm t4)).
    { intro Hin; apply Haway; apply in_or_app; right; exact Hin. }
    f_equal; [eapply IHt1|eapply IHt2]; eauto.
  - assert (H1 : ~ In x (fv_tm t1)).
    { intro Hin; apply Haway; apply in_or_app; left; exact Hin. }
    assert (H2 : ~ In x (fv_tm t2)).
    { intro Hin; apply Haway; apply in_or_app; right; apply in_or_app; left; exact Hin. }
    assert (H3 : ~ In x (fv_tm t3)).
    { intro Hin; apply Haway; apply in_or_app; right; apply in_or_app; right; exact Hin. }
    f_equal; [eapply IHt1|eapply IHt2|eapply IHt3]; eauto.
  - reflexivity.
  - reflexivity.
  - assert (H1 : ~ In x (fv_tm t1)).
    { intro Hin; apply Haway; apply in_or_app; left; exact Hin. }
    assert (H2 : ~ In x (fv_tm t2)).
    { intro Hin; apply Haway; apply in_or_app; right; apply in_or_app; left; exact Hin. }
    assert (H3 : ~ In x (fv_tm t3)).
    { intro Hin; apply Haway; apply in_or_app; right; apply in_or_app; right; exact Hin. }
    f_equal; [eapply IHt1|eapply IHt2|eapply IHt3]; eauto.
Qed.

Lemma instantiate_formula_away : forall p theta gamma x s,
  ~ In x (fv_qualifier p) ->
  instantiate_formula theta (extend_term_substitution gamma x s) p =
  instantiate_formula theta gamma p.
Proof.
  induction p as [| |t1 t2|t1 t2|t1 t2|p1 IHp1 p2 IHp2|
      p1 IHp1 p2 IHp2|p IHp]; intros theta gamma x s Haway; simpl in *; try reflexivity.
  - assert (H1 : ~ In x (fv_tm t1)).
    { intro Hin; apply Haway; apply in_or_app; left; exact Hin. }
    assert (H2 : ~ In x (fv_tm t2)).
    { intro Hin; apply Haway; apply in_or_app; right; exact Hin. }
    rewrite (instantiate_away t1 theta gamma x s H1).
    rewrite (instantiate_away t2 theta gamma x s H2). reflexivity.
  - assert (H1 : ~ In x (fv_tm t1)).
    { intro Hin; apply Haway; apply in_or_app; left; exact Hin. }
    assert (H2 : ~ In x (fv_tm t2)).
    { intro Hin; apply Haway; apply in_or_app; right; exact Hin. }
    rewrite (instantiate_away t1 theta gamma x s H1).
    rewrite (instantiate_away t2 theta gamma x s H2). reflexivity.
  - assert (H1 : ~ In x (fv_tm t1)).
    { intro Hin; apply Haway; apply in_or_app; left; exact Hin. }
    assert (H2 : ~ In x (fv_tm t2)).
    { intro Hin; apply Haway; apply in_or_app; right; exact Hin. }
    rewrite (instantiate_away t1 theta gamma x s H1).
    rewrite (instantiate_away t2 theta gamma x s H2). reflexivity.
  - assert (H1 : ~ In x (fv_qualifier p1)).
    { intro Hin; apply Haway; apply in_or_app; left; exact Hin. }
    assert (H2 : ~ In x (fv_qualifier p2)).
    { intro Hin; apply Haway; apply in_or_app; right; exact Hin. }
    rewrite IHp1, IHp2; auto.
  - assert (H1 : ~ In x (fv_qualifier p1)).
    { intro Hin; apply Haway; apply in_or_app; left; exact Hin. }
    assert (H2 : ~ In x (fv_qualifier p2)).
    { intro Hin; apply Haway; apply in_or_app; right; exact Hin. }
    rewrite IHp1, IHp2; auto.
  - f_equal. apply IHp. exact Haway.
Qed.

Lemma instantiate_rty_away : forall R theta gamma x s,
  ~ In x (fv_rty R) ->
  instantiate_rty theta (extend_term_substitution gamma x s) R =
  instantiate_rty theta gamma R.
Proof.
  induction R; intros theta gamma x s Haway; simpl in *.
  - f_equal. eapply instantiate_formula_away; eassumption.
  - assert (H1 : ~ In x (fv_rty R1)).
    { intro Hin; apply Haway; apply in_or_app; left; exact Hin. }
    assert (H2 : ~ In x (fv_rty R2)).
    { intro Hin; apply Haway; apply in_or_app; right; exact Hin. }
    rewrite IHR1, IHR2; auto.
  - assert (H1 : ~ In x (fv_rty R1)).
    { intro Hin; apply Haway; apply in_or_app; left; exact Hin. }
    assert (H2 : ~ In x (fv_rty R2)).
    { intro Hin; apply Haway; apply in_or_app; right; exact Hin. }
    rewrite IHR1, IHR2; auto.
  - f_equal. apply IHR. exact Haway.
Qed.

Lemma erase_instantiate_rty : forall theta gamma R,
  erase (instantiate_rty theta gamma R) = instantiate_ty theta (erase R).
Proof.
  intros theta gamma R. induction R; simpl; try rewrite IHR1; try rewrite IHR2; try reflexivity.
  f_equal. exact IHR.
Qed.

Lemma instantiate_open_tm_rec : forall t k u theta gamma,
  (forall x, locally_closed_tm (gamma x)) ->
  instantiate theta gamma (open_tm_rec k u t) =
  open_tm_rec k (instantiate theta gamma u) (instantiate theta gamma t).
Proof.
  induction t; intros k u theta gamma Hclosed; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. eapply lc_open_tm_rec_identity with (K := 0) (k := 0).
    unfold locally_closed_tm in Hclosed. apply Hclosed.
  - rewrite IHt; auto.
  - rewrite IHt1, IHt2; auto.
  - rewrite IHt; auto.
  - rewrite IHt; auto.
  - reflexivity.
  - rewrite IHt1, IHt2; auto.
  - rewrite IHt1, IHt2; auto.
  - rewrite IHt1, IHt2; auto.
  - rewrite IHt1, IHt2, IHt3; auto.
  - reflexivity.
  - reflexivity.
  - rewrite IHt1, IHt2, IHt3; auto.
Qed.

Lemma instantiate_open_qualifier_tm_rec : forall p k u theta gamma,
  (forall x, locally_closed_tm (gamma x)) ->
  instantiate_formula theta gamma (open_qualifier_tm_rec k u p) =
  open_qualifier_tm_rec k (instantiate theta gamma u)
    (instantiate_formula theta gamma p).
Proof.
  induction p; intros k u theta gamma Hclosed; simpl; try reflexivity.
  - f_equal; rewrite !instantiate_open_tm_rec; auto.
  - f_equal; rewrite !instantiate_open_tm_rec; auto.
  - f_equal; rewrite !instantiate_open_tm_rec; auto.
  - rewrite IHp1, IHp2; auto.
  - rewrite IHp1, IHp2; auto.
  - rewrite IHp; auto.
Qed.

Lemma instantiate_open_rty_tm_rec : forall R k u theta gamma,
  (forall x, locally_closed_tm (gamma x)) ->
  instantiate_rty theta gamma (open_rty_tm_rec k u R) =
  open_rty_tm_rec k (instantiate theta gamma u) (instantiate_rty theta gamma R).
Proof.
  induction R; intros k u theta gamma Hclosed; simpl.
  - f_equal. apply instantiate_open_qualifier_tm_rec; assumption.
  - rewrite IHR1, IHR2; auto.
  - rewrite IHR1, IHR2; auto.
  - rewrite IHR; auto.
Qed.

Lemma instantiate_ty_open_ty_rec : forall T k U theta,
  (forall X, locally_closed_ty (theta X)) ->
  instantiate_ty theta (open_ty_rec k U T) =
  open_ty_rec k (instantiate_ty theta U) (instantiate_ty theta T).
Proof.
  induction T; intros k U theta Htheta; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. eapply lc_open_ty_rec_identity with (K := 0).
    unfold locally_closed_ty in Htheta. apply Htheta.
  - rewrite IHT1, IHT2; auto.
  - rewrite IHT; auto.
  - reflexivity.
  - reflexivity.
Qed.

Lemma instantiate_open_tm_ty_rec : forall t k U theta gamma,
  (forall X, locally_closed_ty (theta X)) ->
  (forall x, locally_closed_tm (gamma x)) ->
  instantiate theta gamma (open_tm_ty_rec k U t) =
  open_tm_ty_rec k (instantiate_ty theta U) (instantiate theta gamma t).
Proof.
  induction t; intros k U theta gamma Htheta Hgamma; simpl.
  - reflexivity.
  - symmetry. eapply lc_open_tm_ty_rec_identity with (K := 0) (k := 0).
    unfold locally_closed_tm in Hgamma. apply Hgamma.
  - rewrite instantiate_ty_open_ty_rec by assumption. rewrite IHt; auto.
  - rewrite IHt1, IHt2; auto.
  - rewrite IHt; auto.
  - rewrite IHt; [|exact Htheta|exact Hgamma].
    rewrite instantiate_ty_open_ty_rec by assumption. reflexivity.
  - reflexivity.
  - rewrite IHt1, IHt2; auto.
  - rewrite IHt1, IHt2; auto.
  - rewrite !instantiate_ty_open_ty_rec by assumption. rewrite IHt1, IHt2; auto.
  - rewrite IHt1, IHt2, IHt3; auto.
  - reflexivity.
  - reflexivity.
  - rewrite IHt1, IHt2, IHt3; auto.
Qed.

Lemma instantiate_open_qualifier_ty_rec : forall p k U theta gamma,
  (forall X, locally_closed_ty (theta X)) ->
  (forall x, locally_closed_tm (gamma x)) ->
  instantiate_formula theta gamma (open_qualifier_ty_rec k U p) =
  open_qualifier_ty_rec k (instantiate_ty theta U)
    (instantiate_formula theta gamma p).
Proof.
  induction p; intros k U theta gamma Htheta Hgamma; simpl; try reflexivity;
    try rewrite !instantiate_open_tm_ty_rec by assumption;
    try rewrite IHp1 by eauto; try rewrite IHp2 by eauto;
    try rewrite IHp by eauto; try reflexivity.
Qed.

Lemma instantiate_open_rty_ty_rec : forall R k U theta gamma,
  (forall X, locally_closed_ty (theta X)) ->
  (forall x, locally_closed_tm (gamma x)) ->
  instantiate_rty theta gamma (open_rty_ty_rec k U R) =
  open_rty_ty_rec k (instantiate_ty theta U) (instantiate_rty theta gamma R).
Proof.
  induction R; intros k U theta gamma Htheta Hgamma; simpl.
  - f_equal.
    + apply instantiate_ty_open_ty_rec; assumption.
    + apply instantiate_open_qualifier_ty_rec; assumption.
  - rewrite (IHR1 k U theta gamma Htheta Hgamma).
    rewrite (IHR2 k U theta gamma Htheta Hgamma). reflexivity.
  - rewrite (IHR1 k U theta gamma Htheta Hgamma).
    rewrite (IHR2 k U theta gamma Htheta Hgamma). reflexivity.
  - f_equal. eapply IHR; eassumption.
Qed.

Fixpoint logical_value_prefix (n : nat) (R : rty) (v : tm) : list Prop :=
  match n with
  | 0 => [value v]
  | S k =>
      logical_value_prefix k R v ++
      [match R with
       | R_Refine T p =>
           core_value T v /\ value v /\ qualifier_holds (open_qualifier_tm p v)
       | R_Func R1 R2 =>
           core_value (Ty_Arrow (erase R1) (erase R2)) v /\ value v /\
           (forall j, (j <= k)%nat -> forall w,
             nth j (logical_value_prefix k R1 w) False ->
             nth j (logical_term_prefix k (R_Exists R1 R2) (tm_app v w)) False)
       | R_Exists R1 R2 =>
           core_value (erase R2) v /\ value v /\
           (exists w, forall j, (j <= k)%nat ->
             nth j (logical_value_prefix k R1 w) False /\
             nth j (logical_value_prefix k (open_rty_tm R2 w) v) False)
       | R_Poly R1 =>
           core_value (Ty_All (erase R1)) v /\ value v /\
           (forall j, (j <= k)%nat -> forall U, locally_closed_ty U ->
             nth j (logical_term_prefix k (open_rty_ty R1 U) (tm_tapp v U)) False)
       end]
  end
with logical_term_prefix (n : nat) (R : rty) (t : tm) : list Prop :=
  match n with
  | 0 => [True]
  | S k => logical_term_prefix k R t ++
      [forall t', multi t t' ->
        last (logical_value_prefix k R t') False \/ exists u, t' --> u]
  end.

Definition logical_value (n : nat) (R : rty) (v : tm) : Prop :=
  last (logical_value_prefix n R v) False.

Definition logical_term (n : nat) (R : rty) (t : tm) : Prop :=
  last (logical_term_prefix n R t) False.

Lemma last_app_singleton : forall (A : Type) (xs : list A) (x d : A),
  last (xs ++ [x]) d = x.
Proof.
  intros A xs. induction xs as [|a xs IH]; intros x d; simpl.
  - reflexivity.
  - destruct (xs ++ [x]) as [|b ys] eqn:E.
    + apply app_eq_nil in E. destruct E as [_ E]. discriminate.
    + rewrite <- E. apply IH.
Qed.

Lemma logical_value_prefix_length : forall n R v,
  length (logical_value_prefix n R v) = S n.
Proof.
  induction n as [|n IH]; intros R v; simpl; auto.
  rewrite length_app, IH. simpl. lia.
Qed.

Lemma logical_term_prefix_length : forall n R t,
  length (logical_term_prefix n R t) = S n.
Proof.
  induction n as [|n IH]; intros R t; simpl; auto.
  rewrite length_app, IH. simpl. lia.
Qed.

Lemma logical_value_prefix_nth_last : forall n R v,
  nth n (logical_value_prefix n R v) False = last (logical_value_prefix n R v) False.
Proof.
  induction n as [|n IH]; intros R v; simpl.
  - reflexivity.
  - rewrite app_nth2 by (rewrite logical_value_prefix_length; lia).
    rewrite logical_value_prefix_length. replace (S n - S n) with 0 by lia.
    simpl. rewrite last_app_singleton. reflexivity.
Qed.

Lemma logical_term_prefix_nth_last : forall n R t,
  nth n (logical_term_prefix n R t) False = last (logical_term_prefix n R t) False.
Proof.
  induction n as [|n IH]; intros R t; simpl.
  - reflexivity.
  - rewrite app_nth2 by (rewrite logical_term_prefix_length; lia).
    rewrite logical_term_prefix_length. replace (S n - S n) with 0 by lia.
    simpl. rewrite last_app_singleton. reflexivity.
Qed.

Lemma logical_value_prefix_stable : forall n j R v,
  (j <= n)%nat ->
  nth j (logical_value_prefix n R v) False =
  nth j (logical_value_prefix j R v) False.
Proof.
  induction n as [|n IH]; intros j R v Hjn.
  - assert (j = 0) by lia. subst. reflexivity.
  - simpl. destruct (Nat.eq_dec j (S n)) as [->|Hneq].
    + cbn [logical_value_prefix]. rewrite !app_nth2 by
        (rewrite logical_value_prefix_length; lia).
      rewrite !logical_value_prefix_length. simpl. rewrite !Nat.sub_diag. reflexivity.
    + rewrite app_nth1 by (rewrite logical_value_prefix_length; lia).
      rewrite IH by lia. reflexivity.
Qed.

Lemma logical_term_prefix_stable : forall n j R t,
  (j <= n)%nat ->
  nth j (logical_term_prefix n R t) False =
  nth j (logical_term_prefix j R t) False.
Proof.
  induction n as [|n IH]; intros j R t Hjn.
  - assert (j = 0) by lia. subst. reflexivity.
  - simpl. destruct (Nat.eq_dec j (S n)) as [->|Hneq].
    + cbn [logical_term_prefix]. rewrite !app_nth2 by
        (rewrite logical_term_prefix_length; lia).
      rewrite !logical_term_prefix_length. simpl. rewrite !Nat.sub_diag. reflexivity.
    + rewrite app_nth1 by (rewrite logical_term_prefix_length; lia).
      rewrite IH by lia. reflexivity.
Qed.

Lemma logical_value_succ : forall n R v,
  logical_value (S n) R v =
  match R with
  | R_Refine T p => core_value T v /\ value v /\ qualifier_holds (open_qualifier_tm p v)
  | R_Func R1 R2 => core_value (Ty_Arrow (erase R1) (erase R2)) v /\ value v /\
      (forall j, (j <= n)%nat -> forall w,
        nth j (logical_value_prefix n R1 w) False ->
        nth j (logical_term_prefix n (R_Exists R1 R2) (tm_app v w)) False)
  | R_Exists R1 R2 => core_value (erase R2) v /\ value v /\
      (exists w, forall j, (j <= n)%nat ->
        nth j (logical_value_prefix n R1 w) False /\
        nth j (logical_value_prefix n (open_rty_tm R2 w) v) False)
  | R_Poly R1 => core_value (Ty_All (erase R1)) v /\ value v /\
      (forall j, (j <= n)%nat -> forall U, locally_closed_ty U ->
        nth j (logical_term_prefix n (open_rty_ty R1 U) (tm_tapp v U)) False)
  end.
Proof. intros n R v. unfold logical_value, logical_value_prefix; simpl.
  rewrite last_app_singleton. reflexivity. Qed.

Lemma logical_term_succ : forall n R t,
  logical_term (S n) R t =
  (forall t', multi t t' -> last (logical_value_prefix n R t') False \/ exists u, t' --> u).
Proof. intros n R t. unfold logical_term, logical_term_prefix; simpl.
  rewrite last_app_singleton. reflexivity. Qed.

Lemma logical_value_has_value : forall n R v,
  logical_value (S n) R v -> value v.
Proof.
  intros n R v H. rewrite logical_value_succ in H.
  destruct R; simpl in H; tauto.
Qed.

Lemma logical_value_weaken : forall n j R v,
  (j <= n)%nat -> logical_value n R v -> logical_value j R v.
Proof.
  induction n as [|n IH]; intros j R v Hjn Hrel.
  - assert (j = 0) by lia. subst. exact Hrel.
  - destruct j as [|j].
    + apply logical_value_has_value with (n := n) (R := R). exact Hrel.
    + assert (Hj : (j <= n)%nat) by lia.
      rewrite logical_value_succ in Hrel |- *.
      destruct R; simpl in *.
      * exact Hrel.
      * destruct Hrel as [Hc [Hv Happ]]. repeat split; auto.
        intros i Hi w Hw.
        assert (Hin : nth i (logical_value_prefix n R1 w) False).
        { rewrite (logical_value_prefix_stable n i R1 w) by lia.
          rewrite (logical_value_prefix_stable j i R1 w) in Hw by lia.
          exact Hw. }
        pose proof (Happ i (ltac:(lia)) w Hin) as Hout.
        rewrite (logical_term_prefix_stable n i (R_Exists R1 R2) (tm_app v w)) in Hout by lia.
        rewrite (logical_term_prefix_stable j i (R_Exists R1 R2) (tm_app v w)) by lia.
        exact Hout.
      * destruct Hrel as [Hc [Hv [w Hw]]]. repeat split; auto.
        exists w. intros i Hi.
        specialize (Hw i (ltac:(lia))).
        rewrite (logical_value_prefix_stable n i R1 w) in Hw by lia.
        rewrite (logical_value_prefix_stable n i (open_rty_tm R2 w) v) in Hw by lia.
        rewrite (logical_value_prefix_stable j i R1 w) by lia.
        rewrite (logical_value_prefix_stable j i (open_rty_tm R2 w) v) by lia.
        exact Hw.
      * destruct Hrel as [Hc [Hv Hpoly]]. repeat split; auto.
        intros i Hi U HU.
        pose proof (Hpoly i (ltac:(lia)) U HU) as Hout.
        rewrite (logical_term_prefix_stable n i (open_rty_ty R U) (tm_tapp v U)) in Hout by lia.
        rewrite (logical_term_prefix_stable j i (open_rty_ty R U) (tm_tapp v U)) by lia.
        exact Hout.
Qed.

Definition logical_context_interpretation
    (n : nat) (theta : type_substitution) (gamma : term_substitution)
    (RGamma : rcontext) : Prop :=
  forall j, (j <= n)%nat -> forall x R,
    lookup_rcontext x RGamma = Some R ->
    logical_value j (instantiate_rty theta gamma R) (gamma x).

Lemma logical_context_interpretation_weaken : forall n j theta gamma RGamma,
  (j <= n)%nat ->
  logical_context_interpretation n theta gamma RGamma ->
  logical_context_interpretation j theta gamma RGamma.
Proof.
  intros n j theta gamma RGamma Hjn Hctx i Hij x R Hlook.
  eapply Hctx; eauto. lia.
Qed.

Lemma logical_empty_context : forall n theta gamma,
  logical_context_interpretation n theta gamma empty_rcontext.
Proof.
  intros n theta gamma j Hj x R Hlook. discriminate.
Qed.

Lemma logical_context_interpretation_update : forall n theta gamma RGamma R x v,
  logical_context_interpretation n theta gamma RGamma ->
  logical_value n (instantiate_rty theta gamma R) v ->
  ~ In x (fv_rty R) ->
  (forall y S, lookup_rcontext y RGamma = Some S -> ~ In x (fv_rty S)) ->
  logical_context_interpretation n theta
    (extend_term_substitution gamma x v) (update_rcontext RGamma x R).
Proof.
  intros n theta gamma RGamma R x v Hctx Hv HfreshR HfreshG j Hj y S Hlook.
  unfold logical_context_interpretation in *.
  simpl in Hlook. destruct (Nat.eqb y x) eqn:E.
  - inversion Hlook; subst S. rewrite instantiate_rty_away by exact HfreshR.
    unfold extend_term_substitution. apply Nat.eqb_eq in E. subst y.
    rewrite Nat.eqb_refl. eapply logical_value_weaken; eauto.
  - specialize (Hctx j Hj y S Hlook).
    rewrite instantiate_rty_away by (eapply HfreshG; eassumption).
    unfold extend_term_substitution. rewrite E. apply Hctx; assumption.
Qed.

Lemma value_locally_closed : forall v, value v -> locally_closed_tm v.
Proof. intros v H; inversion H; assumption || constructor. Qed.

Lemma value_no_step : forall v u, value v -> ~ v --> u.
Proof. intros v u Hv Hs. inversion Hv; subst; inversion Hs. Qed.

Lemma multi_value_stays : forall v u, value v -> multi v u -> u = v.
Proof.
  intros v u Hv Hm. induction Hm.
  - reflexivity.
  - exfalso. eapply value_no_step; eauto.
Qed.

Lemma logical_variable_is_term : forall n theta gamma RGamma x R,
  logical_context_interpretation n theta gamma RGamma ->
  lookup_rcontext x RGamma = Some R ->
  logical_term n (instantiate_rty theta gamma R) (gamma x).
Proof.
  intros [|k] theta gamma RGamma x R Hctx Hlook.
  - exact I.
  - rewrite logical_term_succ. intros u Hmulti. assert (Hu : u = gamma x).
    { eapply multi_value_stays.
      - specialize (Hctx 0 (Nat.le_0_l _) x R Hlook). simpl in Hctx. exact Hctx.
      - exact Hmulti. }
    subst u. left. simpl. unfold logical_context_interpretation in Hctx.
    specialize (Hctx k (Nat.le_succ_diag_r k) x R Hlook).
    simpl in Hctx. exact Hctx.
Qed.

Lemma logical_context_implies_formulas : forall theta gamma RGamma,
  logical_context_interpretation 1 theta gamma RGamma ->
  (forall y, value (gamma y)) ->
  context_formulas_hold theta gamma RGamma.
Proof.
  intros theta gamma RGamma Hctx Hvalues x T p Hlook.
  specialize (Hctx 1 ltac:(lia) x (R_Refine T p) Hlook).
  unfold logical_value in Hctx. simpl in Hctx. destruct Hctx as [_ [_ Hp]].
  unfold context_formulas_hold. simpl.
  unfold open_qualifier_tm.
  rewrite (instantiate_open_qualifier_tm_rec p 0 (tm_fvar x) theta gamma).
  - simpl. exact Hp.
  - intro y. apply value_locally_closed. apply Hvalues.
Qed.

Lemma logical_context_implies_formulas_at : forall n theta gamma RGamma,
  (1 <= n)%nat ->
  logical_context_interpretation n theta gamma RGamma ->
  (forall y, value (gamma y)) -> context_formulas_hold theta gamma RGamma.
Proof.
  intros n theta gamma RGamma Hn Hctx Hvalues.
  eapply logical_context_implies_formulas; [|exact Hvalues].
  eapply logical_context_interpretation_weaken; eauto; lia.
Qed.

Lemma logical_term_progress : forall R t,
  logical_term 1 R t -> forall t', multi t t' ->
  value t' \/ exists u, t' --> u.
Proof.
  intros R t H t' Hmulti. exact (H t' Hmulti).
Qed.

Lemma logical_integer : forall n z,
  logical_term n
    (R_Refine Ty_Int (Pred_Eq (tm_bvar 0) (tm_int z))) (tm_int z).
Proof.
  intros [|k] z.
  - exact I.
  - rewrite logical_term_succ. intros u Hu.
    pose proof (multi_int_stays z u Hu) as ->.
    destruct k as [|k].
    + left. simpl. constructor.
    + left. change (logical_value (S k)
        (R_Refine Ty_Int (Pred_Eq (tm_bvar 0) (tm_int z))) (tm_int z)).
      rewrite logical_value_succ. simpl. split; [constructor|]. split; [constructor|].
      unfold open_qualifier_tm. simpl. apply qualifier_int_eq.
Qed.

Lemma integer_never_stuck : forall z t',
  multi (tm_int z) t' -> value t' \/ exists u, t' --> u.
Proof.
  intros z t' H. pose proof (multi_int_stays z t' H) as ->. left. constructor.
Qed.

Lemma logical_boolean : forall n b,
  (b = tm_true \/ b = tm_false) ->
  logical_term n (R_Refine Ty_Bool Pred_True) b.
Proof.
  intros [|k] b Hb.
  - exact I.
  - rewrite logical_term_succ. intros u Hu. destruct Hb as [Hb|Hb]; subst b.
    + pose proof (multi_value_stays tm_true u (v_true) Hu) as Hu'. subst u.
      destruct k as [|k]; [left; constructor|].
      left. change (logical_value (S k) (R_Refine Ty_Bool Pred_True) tm_true).
      rewrite logical_value_succ. simpl. split; [constructor|]. split; [constructor|exact I].
    + pose proof (multi_value_stays tm_false u (v_false) Hu) as Hu'. subst u.
      destruct k as [|k]; [left; constructor|].
      left. change (logical_value (S k) (R_Refine Ty_Bool Pred_True) tm_false).
      rewrite logical_value_succ. simpl. split; [constructor|]. split; [constructor|exact I].
Qed.

Lemma qualifier_ne_int_implies_nonzero : forall z,
  qualifier_holds (Pred_Ne (tm_int z) (tm_int 0%Z)) -> z <> 0%Z.
Proof.
  intros z H Hz. subst z. unfold Pred_Ne, qualifier_holds, predicate_holds,
    interpret_qualifier in H. simpl in H.
  apply H. exists (tm_int 0%Z). repeat split; try constructor.
Qed.

Lemma logical_nonzero_integer : forall n v,
  logical_value (S n) (R_Refine Ty_Int
    (Pred_Ne (tm_bvar 0) (tm_int 0%Z))) v ->
  exists z, v = tm_int z /\ z <> 0%Z.
Proof.
  intros n v H. rewrite logical_value_succ in H. simpl in H.
  destruct H as [Hcore [Hv Hp]].
  cbn in Hcore. inversion Hcore; subst. exists n0. split; [reflexivity|].
  unfold open_qualifier_tm in Hp. simpl in Hp.
  eapply qualifier_ne_int_implies_nonzero. exact Hp.
Qed.

Lemma logical_nonzero_endpoint : forall t z,
  logical_term 2 (R_Refine Ty_Int
    (Pred_Ne (tm_bvar 0) (tm_int 0%Z))) t ->
  multi t (tm_int z) -> z <> 0%Z.
Proof.
  intros t z Hsafe Hmulti. rewrite logical_term_succ in Hsafe.
  specialize (Hsafe (tm_int z) Hmulti).
  destruct Hsafe as [Hval|[u Hstep]].
  - destruct (logical_nonzero_integer 0 (tm_int z) Hval) as [z' [E Hz]].
    inversion E; subst. exact Hz.
  - exfalso. eapply value_no_step; [constructor|exact Hstep].
Qed.

Lemma logical_function_application : forall k R1 R2 v w,
  logical_value (S k) (R_Func R1 R2) v ->
  logical_value k R1 w ->
  logical_term k (R_Exists R1 R2) (tm_app v w).
Proof.
  intros k R1 R2 v w Hfun Hw. rewrite logical_value_succ in Hfun.
  destruct Hfun as [_ [_ Happ]].
  unfold logical_term.
  rewrite <- logical_term_prefix_nth_last.
  apply Happ with (j := k); [lia|].
  unfold logical_value in Hw. rewrite <- logical_value_prefix_nth_last in Hw.
  exact Hw.
Qed.

Lemma logical_refinement_intro : forall n T p v,
  core_value T v -> value v ->
  qualifier_holds (open_qualifier_tm p v) ->
  logical_value (S n) (R_Refine T p) v.
Proof. intros n T p v Hc Hv Hp. rewrite logical_value_succ. simpl. auto. Qed.

Lemma logical_refinement_elim : forall n T p v,
  logical_value (S n) (R_Refine T p) v ->
  core_value T v /\ value v /\ qualifier_holds (open_qualifier_tm p v).
Proof. intros n T p v H. rewrite logical_value_succ in H. simpl in H. exact H. Qed.

Lemma logical_existential_elim : forall k R1 R2 v,
  logical_value (S k) (R_Exists R1 R2) v ->
  core_value (erase R2) v /\ value v /\
    exists w, logical_value k R1 w /\
      logical_value k (open_rty_tm R2 w) v.
Proof.
  intros k R1 R2 v H. rewrite logical_value_succ in H. simpl in H.
  destruct H as [Hc [Hv [w Hw]]]. split; [exact Hc|]. split; [exact Hv|].
  exists w. split.
  - unfold logical_value. rewrite <- logical_value_prefix_nth_last.
    exact (proj1 (Hw k (Nat.le_refl k))).
  - unfold logical_value. rewrite <- logical_value_prefix_nth_last.
    exact (proj2 (Hw k (Nat.le_refl k))).
Qed.

Lemma logical_polymorphic_application : forall k R v U,
  logical_value (S k) (R_Poly R) v -> locally_closed_ty U ->
  logical_term k (open_rty_ty R U) (tm_tapp v U).
Proof.
  intros k R v U Hpoly HU. rewrite logical_value_succ in Hpoly.
  destruct Hpoly as [_ [_ Happly]].
  unfold logical_term.
  rewrite <- logical_term_prefix_nth_last.
  apply Happly with (j := k); [lia|exact HU].
Qed.

Lemma multi_transitive : forall t u v,
  multi t u -> multi u v -> multi t v.
Proof.
  intros t u v Htu Huv. induction Htu.
  - exact Huv.
  - eapply multi_step; eauto.
Qed.

Lemma logical_term_after_multi : forall n R t u,
  logical_term n R t -> multi t u -> logical_term n R u.
Proof.
  intros [|k] R t u Hsafe Hmulti.
  - exact I.
  - rewrite logical_term_succ in Hsafe |- *.
    intros v Huv. apply Hsafe. eapply multi_transitive; eauto.
Qed.

Lemma logical_value_is_term : forall n R v,
  logical_value n R v -> logical_term (S n) R v.
Proof.
  intros [|n] R v Hv.
  - rewrite logical_term_succ. intros u Hu.
    pose proof (multi_value_stays v u Hv Hu) as ->. left. exact Hv.
  - assert (Hvalue : value v).
    { rewrite logical_value_succ in Hv. destruct R; simpl in Hv; tauto. }
    rewrite logical_term_succ. intros u Hu.
    pose proof (multi_value_stays v u Hvalue Hu) as ->. left. exact Hv.
Qed.

Lemma multi_preserves_safety : forall (P : tm -> Prop),
  (forall t, P t -> value t \/ exists u, t --> u) ->
  (forall t u, P t -> t --> u -> P u) ->
  forall t t', P t -> multi t t' -> value t' \/ exists u, t' --> u.
Proof.
  intros P Hprogress Hpres t t' HP Hmulti.
  induction Hmulti.
  - apply Hprogress; assumption.
  - apply IHHmulti. eapply Hpres; eauto.
Qed.

Theorem never_stuck : forall (t t' : tm) (R : rty),
  has_rtype [] empty_rcontext t R ->
  multi t t' ->
  value t' \/ exists t'' : tm, t' --> t''.
Proof.
  intros t t' R Htyped Hmulti.
  eapply logical_term_progress.
  - (* Need the fundamental theorem for refinement typing here. *)
    clear Hmulti.
    (* This is the remaining proof obligation. *)
    exact I.
  - exact Hmulti.
Qed.

End SystemFRefinementIfRecursionTask.
