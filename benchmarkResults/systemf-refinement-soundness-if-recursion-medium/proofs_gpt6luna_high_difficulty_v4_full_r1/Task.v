From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
From Stdlib Require Import ZArith.BinInt.

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

End SystemFRefinementIfRecursion.

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
Module SystemFRefinementIfRecursionInfrastructure.
Import ListNotations.
Import SystemFRefinementIfRecursion.

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
  | tm_fix A B metric body => tm_fix (instantiate_ty theta A) (instantiate_ty theta B)
      (instantiate theta gamma metric) (instantiate theta gamma body)
  | tm_ifzero t t0 t1 => tm_ifzero (instantiate theta gamma t)
      (instantiate theta gamma t0) (instantiate theta gamma t1)
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

End SystemFRefinementIfRecursionInfrastructure.

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
Module SystemFRefinementIfRecursionCoreTyping.
Import ListNotations.
Import SystemFRefinementIfRecursion.
Import SystemFRefinementIfRecursionInfrastructure.

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

End SystemFRefinementIfRecursionCoreTyping.

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

End SystemFRefinementIfRecursionTyping.

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Module SystemFRefinementIfRecursionEvaluation.
Import ListNotations SystemFRefinementIfRecursion SystemFRefinementIfRecursionInfrastructure
  SystemFRefinementIfRecursionCoreTyping.

Inductive multi : tm -> tm -> Prop :=
  | multi_refl : forall t, multi t t
  | multi_step : forall t1 t2 t3,
      t1 --> t2 -> multi t2 t3 -> multi t1 t3.
Notation "t '-->*' u" := (multi t u) (at level 40).

Definition halts (t : tm) : Prop :=
  exists v, multi t v /\ value v.

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

End SystemFRefinementIfRecursionEvaluation.

From Stdlib Require Import Arith.PeanoNat Lists.List Lia Program.Wf.
From Equations Require Import Equations.
Module SystemFRefinementIfRecursionSubstitution.
Import ListNotations.
Import SystemFRefinementIfRecursion.
Import SystemFRefinementIfRecursionInfrastructure.
Import SystemFRefinementIfRecursionCoreTyping.
Import SystemFRefinementIfRecursionTyping.
Import SystemFRefinementIfRecursionEvaluation.

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
End SystemFRefinementIfRecursionSubstitution.

Module SystemFRefinementIfRecursionTask.
Import ListNotations SystemFRefinementIfRecursion SystemFRefinementIfRecursionInfrastructure SystemFRefinementIfRecursionCoreTyping SystemFRefinementIfRecursionLogic SystemFRefinementIfRecursionTyping SystemFRefinementIfRecursionEvaluation SystemFRefinementIfRecursionSubstitution .

Lemma canonical_integer : forall v,
  value v -> has_type [] [] v Ty_Int ->
  exists n, v = tm_int n.
Proof.
  intros v Hv Hty. inversion Hv; subst; inversion Hty; subst; eauto.
Qed.

Lemma canonical_boolean : forall v,
  value v -> has_type [] [] v Ty_Bool ->
  v = tm_true \/ v = tm_false.
Proof.
  intros v Hv Hty. inversion Hv; subst; inversion Hty; subst; eauto.
Qed.

Lemma canonical_function : forall A B v,
  value v -> has_type [] [] v (Ty_Arrow A B) ->
  (exists body, v = tm_abs A body) \/
  (exists metric body, v = tm_fix A B metric body).
Proof.
  intros A B v Hv Hty. inversion Hv; subst; inversion Hty; subst; eauto.
Qed.

Lemma canonical_poly : forall T v,
  value v -> has_type [] [] v (Ty_All T) ->
  exists body, v = tm_tabs body.
Proof.
  intros T v Hv Hty. inversion Hv; subst; inversion Hty; subst; eauto.
Qed.

Lemma context_included_update : forall Gamma Gamma' x T,
  context_included Gamma Gamma' ->
  context_included (update Gamma x T) (update Gamma' x T).
Proof.
  intros Gamma Gamma' x T Hinc y U Hlookup.
  unfold update in *. simpl in *.
  destruct (Nat.eqb y x) eqn:E.
  - inversion Hlookup; subst. reflexivity.
  - apply Hinc. exact Hlookup.
Qed.

Lemma core_typing_context_weaken : forall Delta Gamma t T,
  has_type Delta Gamma t T -> forall Gamma',
    context_included Gamma Gamma' -> has_type Delta Gamma' t T.
Proof.
  intros Delta Gamma t T Hty. induction Hty; intros Gamma' Hinc.
  - econstructor; eauto.
  - econstructor; eauto.
    intros x Hx. apply H1; eauto using context_included_update.
  - econstructor; eauto.
  - econstructor. intros X HX. apply H0; eauto.
  - econstructor; eauto.
  - constructor.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
    + intros x Hx. eapply H2; [exact Hx|].
      apply context_included_update. exact Hinc.
    + intros f x Hf Hx. eapply H4; [exact Hf|exact Hx|].
      apply context_included_update. apply context_included_update. exact Hinc.
  - econstructor; eauto.
  - constructor.
  - constructor.
  - econstructor; eauto.
Qed.

Lemma lookup_context_in_dom : forall x Gamma T,
  lookup_context x Gamma = Some T -> In x (dom_context Gamma).
Proof.
  intros x Gamma. induction Gamma as [|[y U] Gamma IH]; intros T Hlookup.
  - discriminate.
  - simpl in *. destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. subst x. left. reflexivity.
    + right. eapply IH. exact Hlookup.
Qed.

Lemma term_substitution_typed_update_fvar : forall Gamma Delta' Gamma' theta gamma x T,
  term_substitution_typed Gamma Delta' Gamma' theta gamma ->
  ~ In x (dom_context Gamma') ->
  wf_ty Delta' (instantiate_ty theta T) ->
  term_substitution_typed (update Gamma x T) Delta'
    (update Gamma' x (instantiate_ty theta T)) theta
    (term_subst_update gamma x (tm_fvar x)).
Proof.
  intros Gamma Delta' Gamma' theta gamma x T Htyped Hfresh Hwf.
  unfold term_substitution_typed in *.
  intros y U Hlookup.
  unfold update in Hlookup. simpl in Hlookup.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst y. inversion Hlookup; subst U.
    unfold term_subst_update. rewrite Nat.eqb_refl.
    apply T_Var.
    + simpl. rewrite Nat.eqb_refl. reflexivity.
    + exact Hwf.
  - assert (Hxy : y <> x) by (apply Nat.eqb_neq; exact E).
    assert (Hlookup0 : lookup_context y Gamma = Some U) by exact Hlookup.
    specialize (Htyped y U Hlookup0).
    assert (HlookupTerm : term_subst_update gamma x (tm_fvar x) y = gamma y).
    { unfold term_subst_update. destruct (Nat.eqb x y) eqn:E'.
      - apply Nat.eqb_eq in E'. exfalso. apply Hxy. symmetry. exact E'.
      - reflexivity. }
    rewrite HlookupTerm.
    eapply core_typing_context_weaken; [exact Htyped|].
    unfold context_included, update.
    intros z V Hz. simpl in Hz.
    destruct (Nat.eqb z x) eqn:E2.
    + apply Nat.eqb_eq in E2. subst z. exfalso. apply Hfresh.
      eapply lookup_context_in_dom. exact Hz.
    + simpl. rewrite E2. exact Hz.
Qed.


Lemma entails_sound : forall Delta RGamma p q,
  entails Delta RGamma p q ->
  forall theta gamma,
    (forall x, value (gamma x)) ->
    context_formulas_hold theta gamma RGamma ->
    qualifier_holds (instantiate_formula theta gamma p) ->
    qualifier_holds (instantiate_formula theta gamma q).
Proof.
  intros Delta RGamma p q Hent.
  induction Hent; intros theta gamma Hvalues Hctx Hp;
    cbn [qualifier_holds predicate_holds interpret_qualifier
      instantiate_formula] in *.
  - exact Hp.
  - exact I.
  - eapply IHHent2; [exact Hvalues|exact Hctx|].
    eapply IHHent1; eauto.
  - exact (proj1 Hp).
  - exact (proj2 Hp).
  - split.
    + eapply IHHent1; eauto.
    + eapply IHHent2; eauto.
  - left. exact Hp.
  - right. exact Hp.
  - destruct Hp as [Hp|Hq].
    + eapply IHHent1; eauto.
    + eapply IHHent2; eauto.
  - intros Hq. eapply IHHent; eauto.
  - destruct Hp as [Hp Hnot]. contradiction.
  - eapply Hctx; eauto.
  - contradiction.
  - eapply H; eauto.
Qed.

Lemma instantiate_open_tm_rec : forall t k theta gamma u,
  term_substitution_closed gamma ->
  instantiate theta gamma (open_tm_rec k u t) =
  open_tm_rec k (instantiate theta gamma u) (instantiate theta gamma t).
Proof.
  induction t; intros k theta gamma u Hgamma; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - assert (Hclosed : lc_tm_at 0 k (gamma a)).
    { eapply lc_tm_at_monotone; [apply Hgamma|lia|lia]. }
    rewrite (open_tm_rec_lc_at (gamma a) 0 k
      (instantiate theta gamma u) Hclosed). reflexivity.
  - f_equal. apply IHt. assumption.
  - f_equal; [apply IHt1|apply IHt2]; assumption.
  - f_equal. apply IHt. assumption.
  - f_equal. apply IHt. assumption.
  - reflexivity.
  - f_equal; [apply IHt1|apply IHt2]; assumption.
  - f_equal; [apply IHt1|apply IHt2]; assumption.
  - f_equal.
    + exact (IHt1 (S k) theta gamma u Hgamma).
    + exact (IHt2 (S (S k)) theta gamma u Hgamma).
  - f_equal; [apply IHt1|apply IHt2|apply IHt3]; assumption.
  - reflexivity.
  - reflexivity.
  - f_equal; [apply IHt1|apply IHt2|apply IHt3]; assumption.
Qed.

Lemma instantiate_open_fix_body : forall body f x theta gamma,
  term_substitution_closed gamma ->
  instantiate theta gamma (open_fix_body body f x) =
    open_fix_body (instantiate theta gamma body)
      (instantiate theta gamma f) (instantiate theta gamma x).
Proof.
  intros body f x theta gamma Hclosed.
  unfold open_fix_body, open_tm.
  rewrite (instantiate_open_tm_rec
    (open_tm_rec 1 f body) 0 theta gamma x Hclosed).
  rewrite (instantiate_open_tm_rec body 1 theta gamma f Hclosed).
  reflexivity.
Qed.

Lemma instantiate_formula_open_tm : forall p theta gamma u,
  term_substitution_closed gamma ->
  instantiate_formula theta gamma (open_qualifier_tm p u) =
  open_qualifier_tm (instantiate_formula theta gamma p)
    (instantiate theta gamma u).
Proof.
  induction p; intros theta gamma u Hgamma;
    cbn [instantiate_formula open_qualifier_tm open_qualifier_tm_rec
      open_pred_tm_rec];
    try reflexivity.
  - f_equal; eapply instantiate_open_tm_rec; eauto.
  - f_equal; eapply instantiate_open_tm_rec; eauto.
  - f_equal; eapply instantiate_open_tm_rec; eauto.
  - f_equal; [apply IHp1|apply IHp2]; assumption.
  - f_equal; [apply IHp1|apply IHp2]; assumption.
  - f_equal. apply IHp. assumption.
Qed.

Lemma instantiate_update_fresh_tm : forall t theta gamma x v,
  ~ In x (fv_tm t) ->
  instantiate theta (term_subst_update gamma x v) t =
  instantiate theta gamma t.
Proof.
  induction t; intros theta gamma x v Hfresh; simpl in *.
  - reflexivity.
  - unfold term_subst_update.
    destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply Hfresh. simpl. auto.
    + reflexivity.
  - f_equal. apply IHt. assumption.
  - f_equal.
    + apply IHt1. intro H. apply Hfresh. apply in_or_app. left. exact H.
    + apply IHt2. intro H. apply Hfresh. apply in_or_app. right. exact H.
  - f_equal. apply IHt. assumption.
  - f_equal. apply IHt. assumption.
  - reflexivity.
  - f_equal.
    + apply IHt1. intro H. apply Hfresh. apply in_or_app. left. exact H.
    + apply IHt2. intro H. apply Hfresh. apply in_or_app. right. exact H.
  - f_equal.
    + apply IHt1. intro H. apply Hfresh. apply in_or_app. left. exact H.
    + apply IHt2. intro H. apply Hfresh. apply in_or_app. right. exact H.
  - f_equal.
    + apply IHt1. intro H. apply Hfresh. apply in_or_app. left. exact H.
    + apply IHt2. intro H. apply Hfresh. apply in_or_app. right. exact H.
  - f_equal.
    + apply IHt1. intro H. apply Hfresh. apply in_or_app. left. exact H.
    + apply IHt2. intro H. apply Hfresh. apply in_or_app. right. apply in_or_app. left. exact H.
    + apply IHt3. intro H. apply Hfresh. apply in_or_app. right. apply in_or_app. right. exact H.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + apply IHt1. intro H. apply Hfresh. apply in_or_app. left. exact H.
    + apply IHt2. intro H. apply Hfresh. apply in_or_app. right. apply in_or_app. left. exact H.
    + apply IHt3. intro H. apply Hfresh. apply in_or_app. right. apply in_or_app. right. exact H.
Qed.

Lemma instantiate_update_fresh_formula : forall p theta gamma x v,
  ~ In x (fv_qualifier p) ->
  instantiate_formula theta (term_subst_update gamma x v) p =
  instantiate_formula theta gamma p.
Proof.
  induction p; intros theta gamma x v Hfresh; simpl in *.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + apply instantiate_update_fresh_tm.
      intro H. apply Hfresh. simpl. apply in_or_app. left. exact H.
    + apply instantiate_update_fresh_tm.
      intro H. apply Hfresh. simpl. apply in_or_app. right. exact H.
  - f_equal.
    + apply instantiate_update_fresh_tm.
      intro H. apply Hfresh. simpl. apply in_or_app. left. exact H.
    + apply instantiate_update_fresh_tm.
      intro H. apply Hfresh. simpl. apply in_or_app. right. exact H.
  - f_equal.
    + apply instantiate_update_fresh_tm.
      intro H. apply Hfresh. simpl. apply in_or_app. left. exact H.
    + apply instantiate_update_fresh_tm.
      intro H. apply Hfresh. simpl. apply in_or_app. right. exact H.
  - f_equal.
    + apply IHp1. intuition.
    + apply IHp2. intuition.
  - f_equal.
    + apply IHp1. intuition.
    + apply IHp2. intuition.
  - f_equal. apply IHp. assumption.
Qed.

Lemma instantiate_update_fresh_open_formula : forall p theta gamma x v u,
  term_substitution_closed gamma -> locally_closed_tm v ->
  ~ In x (fv_qualifier p) -> ~ In x (fv_tm u) ->
  instantiate_formula theta (term_subst_update gamma x v)
    (open_qualifier_tm p u) =
  instantiate_formula theta gamma (open_qualifier_tm p u).
Proof.
  intros p theta gamma x v u Hgamma Hv Hfreshp Hfreshu.
  rewrite (instantiate_formula_open_tm p theta
    (term_subst_update gamma x v) u).
  2: { apply term_subst_update_closed; assumption. }
  rewrite (instantiate_formula_open_tm p theta gamma u) by exact Hgamma.
  rewrite instantiate_update_fresh_formula by assumption.
  rewrite instantiate_update_fresh_tm by assumption.
  reflexivity.
Qed.

Lemma erase_open_rty_tm_rec : forall R k u,
  erase (open_rty_tm_rec k u R) = erase R.
Proof.
  induction R; intros k u; simpl.
  - reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR2. reflexivity.
  - rewrite IHR. reflexivity.
Qed.

Lemma erase_open_rty_tm : forall R u,
  erase (open_rty_tm R u) = erase R.
Proof. intros. apply erase_open_rty_tm_rec. Qed.

Lemma erase_open_rty_ty_rec : forall R k U,
  erase (open_rty_ty_rec k U R) = open_ty_rec k U (erase R).
Proof.
  induction R; intros k U; simpl; f_equal; eauto.
Qed.

Lemma erase_open_rty_ty : forall R U,
  erase (open_rty_ty R U) = open_ty (erase R) U.
Proof. intros. apply erase_open_rty_ty_rec. Qed.

Lemma erase_instantiate_rty : forall R theta gamma,
  erase (instantiate_rty theta gamma R) =
  instantiate_ty theta (erase R).
Proof.
  induction R; intros theta gamma; simpl.
  - reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - apply IHR2.
  - rewrite IHR. reflexivity.
Qed.

Lemma lookup_erase_context_inv : forall RGamma x T,
  lookup_context x (erase_context RGamma) = Some T ->
  exists R, lookup_rcontext x RGamma = Some R /\ erase R = T.
Proof.
  induction RGamma as [|[y R] RGamma IH]; intros x T Hlookup.
  - discriminate.
  - simpl in Hlookup. destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. subst x. inversion Hlookup; subst.
      exists R. split.
      * simpl. rewrite Nat.eqb_refl. reflexivity.
      * reflexivity.
    + destruct (IH x T Hlookup) as [S [Hfind Herase]].
      exists S. split.
      * simpl. rewrite E. exact Hfind.
      * exact Herase.
Qed.

Lemma wf_ty_weaken : forall Delta T,
  wf_ty Delta T -> forall Delta',
    (forall X, In X Delta -> In X Delta') -> wf_ty Delta' T.
Proof.
  intros Delta T Hwf.
  induction Hwf as
    [Delta X Hxin
    | Delta T1 T2 Hwf1 IH1 Hwf2 IH2
    | L Delta T Hbody IHbody
    | Delta
    | Delta]; intros Delta' Hincl.
  - constructor. apply Hincl. assumption.
  - constructor; eauto.
  - econstructor. intros X HX.
    eapply IHbody; [exact HX|].
    intros Y HY. simpl in HY. destruct HY as [HY|HY].
    + subst Y. simpl. auto.
    + simpl. right. apply Hincl. exact HY.
  - constructor.
  - constructor.
Qed.

Lemma ty_context_included_update : forall Delta Delta' X,
  ty_context_included Delta Delta' ->
  ty_context_included (X :: Delta) (X :: Delta').
Proof.
  intros Delta Delta' X Hinc Y HY. simpl in HY. destruct HY as [HY|HY].
  - subst Y. simpl. auto.
  - simpl. right. apply Hinc. exact HY.
Qed.

Lemma core_typing_ty_weaken : forall Delta Gamma t T,
  has_type Delta Gamma t T -> forall Delta',
    ty_context_included Delta Delta' -> has_type Delta' Gamma t T.
Proof.
  intros Delta Gamma t T Hty. induction Hty; intros Delta' Hinc.
  - eapply T_Var; [exact H|]. eapply wf_ty_weaken; eauto.
  - eapply T_Abs.
    + eapply wf_ty_weaken; eauto.
    + intros x Hx. apply H1; eauto.
  - eapply T_App; eauto.
  - eapply T_TAbs. intros X HX. apply H0; eauto using ty_context_included_update.
  - eapply T_TApp; [eauto|]. eapply wf_ty_weaken; eauto.
  - constructor.
  - econstructor; eauto.
  - econstructor; eauto.
  - eapply T_Fix.
    * eapply wf_ty_weaken; eauto.
    * eapply wf_ty_weaken; eauto.
    * intros x Hx. apply H2; eauto.
    * intros f x Hf Hx. apply H4; eauto.
  - econstructor; eauto.
  - constructor.
  - constructor.
  - econstructor; eauto.
Qed.

Lemma instantiate_ty_update_fresh : forall T theta X U,
  ~ In X (fv_ty T) ->
  instantiate_ty (type_subst_update theta X U) T = instantiate_ty theta T.
Proof.
  induction T; intros theta X U Hfresh; simpl in *.
  - reflexivity.
  - destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply Hfresh. simpl. auto.
    + unfold type_subst_update. rewrite E. reflexivity.
  - f_equal.
    + apply IHT1. intro H. apply Hfresh. simpl. apply in_or_app. left. exact H.
    + apply IHT2. intro H. apply Hfresh. simpl. apply in_or_app. right. exact H.
  - f_equal. apply IHT. assumption.
  - reflexivity.
  - reflexivity.
Qed.

Lemma instantiate_ty_update_open : forall T theta X k,
  type_substitution_closed theta ->
  ~ In X (fv_ty T) ->
  instantiate_ty (type_subst_update theta X (Ty_FVar X))
    (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k (Ty_FVar X) (instantiate_ty theta T).
Proof.
  induction T; intros theta X k Htheta Hfresh; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + unfold type_subst_update. simpl. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - assert (Hneq : X <> a).
    { intro E. subst. apply Hfresh. simpl. auto. }
    unfold type_subst_update. simpl.
    destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E. exfalso. apply Hneq. exact E.
    + assert (Hlc : lc_ty_at k (theta a)).
      { exact (@lc_ty_at_monotone 0 k (theta a)
          (Htheta a) (Nat.le_0_l k)). }
      rewrite (@open_ty_rec_lc_at (theta a) k (Ty_FVar X) Hlc). reflexivity.
  - f_equal.
    + apply IHT1; [exact Htheta|]. intro H. apply Hfresh. simpl. apply in_or_app. left. exact H.
    + apply IHT2; [exact Htheta|]. intro H. apply Hfresh. simpl. apply in_or_app. right. exact H.
  - f_equal. apply IHT; assumption.
  - reflexivity.
  - reflexivity.
Qed.

Lemma wf_ty_instantiation : forall Delta T,
  wf_ty Delta T -> forall Delta' theta,
    type_substitution_closed theta ->
    type_substitution_wf Delta Delta' theta ->
    wf_ty Delta' (instantiate_ty theta T).
Proof.
  intros Delta T Hwf.
  induction Hwf as
    [Delta X Hxin
    | Delta T1 T2 Hwf1 IH1 Hwf2 IH2
    | L Delta T Hbody IHbody
    | Delta
    | Delta]; intros Delta' theta Hclosed Hsub.
  - simpl. apply Hsub. exact Hxin.
  - simpl. constructor.
    + eapply IH1; eauto.
    + eapply IH2; eauto.
  - simpl. eapply WF_All with (L := L ++ (Delta ++ fv_ty T)).
    intros X HX.
    assert (HXL : ~ In X L).
    { intro Hin. apply HX. apply in_or_app. left. exact Hin. }
    assert (HXDelta : ~ In X Delta).
    { intro Hin. apply HX. apply in_or_app. right. apply in_or_app. left. exact Hin. }
    assert (HXfv : ~ In X (fv_ty T)).
    { intro Hin. apply HX. apply in_or_app. right. apply in_or_app. right. exact Hin. }
    set (thetaX := type_subst_update theta X (Ty_FVar X)).
    assert (HclosedX : type_substitution_closed thetaX).
    { unfold thetaX. apply type_subst_update_closed; [exact Hclosed|apply lc_ty_fvar]. }
    assert (HsubX : type_substitution_wf (X :: Delta) (X :: Delta') thetaX).
    { intros Y HY. simpl in HY. destruct HY as [HY|HY].
      - subst Y. unfold thetaX, type_subst_update. rewrite Nat.eqb_refl.
        constructor. simpl. auto.
      - assert (Hneq : Y <> X).
        { intro E. subst. apply HXDelta. exact HY. }
        unfold thetaX, type_subst_update. destruct (Nat.eqb X Y) eqn:E.
        + apply Nat.eqb_eq in E. exfalso. apply Hneq. symmetry. exact E.
        + eapply wf_ty_weaken.
          * apply Hsub. exact HY.
          * intros Z HZ. simpl. right. exact HZ. }
    unfold thetaX.
    unfold open_ty.
    rewrite <- (@instantiate_ty_update_open T theta X 0 Hclosed HXfv).
    apply (IHbody X HXL (X :: Delta') thetaX HclosedX HsubX).
  - constructor.
  - constructor.
Qed.

Lemma type_substitution_wf_update_fvar : forall Delta Delta' theta X,
  type_substitution_wf Delta Delta' theta ->
  ~ In X Delta ->
  type_substitution_wf (X :: Delta) (X :: Delta')
    (type_subst_update theta X (Ty_FVar X)).
Proof.
  intros Delta Delta' theta X Hsub HX Y HY.
  simpl in HY. destruct HY as [HY|HY].
  - subst Y. unfold type_subst_update. rewrite Nat.eqb_refl.
    constructor. simpl. auto.
  - assert (Hneq : Y <> X).
    { intro E. subst. apply HX. exact HY. }
    unfold type_subst_update. destruct (Nat.eqb X Y) eqn:E.
    + apply Nat.eqb_eq in E. exfalso. apply Hneq. symmetry. exact E.
    + eapply wf_ty_weaken.
      * apply Hsub. exact HY.
      * intros Z HZ. simpl. right. exact HZ.
Qed.

Lemma instantiate_open_tm_ty_rec : forall t K theta gamma X,
  type_substitution_closed theta -> term_substitution_closed gamma ->
  ~ In X (ftv_tm t) ->
  instantiate (type_subst_update theta X (Ty_FVar X)) gamma
    (open_tm_ty_rec K (Ty_FVar X) t) =
  open_tm_ty_rec K (Ty_FVar X) (instantiate theta gamma t).
Proof.
  induction t; intros K theta gamma X Htheta Hgamma Hfresh; simpl in *.
  - reflexivity.
  - assert (Hlc : lc_tm_at K 0 (gamma a)).
    { eapply lc_tm_at_monotone; [apply Hgamma|lia|lia]. }
    rewrite (@open_tm_ty_rec_lc_at (gamma a) K 0 (Ty_FVar X) Hlc).
    reflexivity.
  - f_equal.
    + apply instantiate_ty_update_open.
      * exact Htheta.
      * intro H. apply Hfresh. simpl. apply in_or_app. left. exact H.
    + apply IHt; try assumption. intro H. apply Hfresh. simpl. apply in_or_app. right. exact H.
  - f_equal.
    + apply IHt1; try assumption. intuition.
    + apply IHt2; try assumption. intuition.
  - f_equal. apply IHt; assumption.
  - f_equal.
    + apply IHt; try assumption. intuition.
    + apply instantiate_ty_update_open; try assumption.
      intro H. apply Hfresh. simpl. apply in_or_app. right. exact H.
  - reflexivity.
  - f_equal.
    + apply IHt1; try assumption. intuition.
    + apply IHt2; try assumption. intuition.
  - f_equal.
    + apply IHt1; try assumption. intuition.
    + apply IHt2; try assumption. intuition.
  - f_equal.
    + apply instantiate_ty_update_open; [exact Htheta|].
      intro H. apply Hfresh. simpl. apply in_or_app. left. exact H.
    + apply instantiate_ty_update_open; [exact Htheta|].
      intro H. apply Hfresh. simpl. apply in_or_app. right. apply in_or_app. left. exact H.
    + apply IHt1; try assumption.
      intro H. apply Hfresh. simpl. apply in_or_app. right. apply in_or_app. right.
      apply in_or_app. left. exact H.
    + apply IHt2; try assumption.
      intro H. apply Hfresh. simpl. apply in_or_app. right. apply in_or_app. right.
      apply in_or_app. right. exact H.
  - f_equal.
    + apply IHt1; try assumption.
      intro H. apply Hfresh. simpl. apply in_or_app. left. exact H.
    + apply IHt2; try assumption.
      intro H. apply Hfresh. simpl. apply in_or_app. right. apply in_or_app. left. exact H.
    + apply IHt3; try assumption.
      intro H. apply Hfresh. simpl. apply in_or_app. right. apply in_or_app. right. exact H.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + apply IHt1; try assumption.
      intro H. apply Hfresh. simpl. apply in_or_app. left. exact H.
    + apply IHt2; try assumption.
      intro H. apply Hfresh. simpl. apply in_or_app. right. apply in_or_app. left. exact H.
    + apply IHt3; try assumption.
      intro H. apply Hfresh. simpl. apply in_or_app. right. apply in_or_app. right. exact H.
Qed.



Lemma lookup_fv_ty_context : forall x Gamma T,
  lookup_context x Gamma = Some T -> incl (fv_ty T) (ftv_context Gamma).
Proof.
  intros x Gamma. induction Gamma as [|[y U] Gamma IH]; intros T Hlookup.
  - discriminate.
  - simpl in Hlookup. simpl. destruct (Nat.eqb x y) eqn:E.
    + inversion Hlookup; subst. intros Z HZ. apply in_or_app. left. exact HZ.
    + intros Z HZ. apply in_or_app. right. eapply IH; eauto.
Qed.

Lemma term_substitution_typed_ty_extend : forall Gamma Delta' Gamma' theta gamma X,
  term_substitution_typed Gamma Delta' Gamma' theta gamma ->
  ~ In X Delta' -> ~ In X (ftv_context Gamma) ->
  term_substitution_typed Gamma (X :: Delta') Gamma'
    (type_subst_update theta X (Ty_FVar X)) gamma.
Proof.
  intros Gamma Delta' Gamma' theta gamma X Htyped HXDelta HXGamma.
  unfold term_substitution_typed in *.
  intros x T Hlookup. specialize (Htyped x T Hlookup).
  rewrite (instantiate_ty_update_fresh T theta X (Ty_FVar X)).
  - eapply core_typing_ty_weaken; [exact Htyped|].
    intros Y HY. simpl. right. exact HY.
  - intro H. apply HXGamma. apply (lookup_fv_ty_context x Gamma T Hlookup). exact H.
Qed.

Lemma instantiate_ty_open_ty_rec : forall T k theta U,
  type_substitution_closed theta ->
  instantiate_ty theta (open_ty_rec k U T) =
    open_ty_rec k (instantiate_ty theta U) (instantiate_ty theta T).
Proof.
  induction T; intros k theta U Hclosed; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - assert (Hlc : lc_ty_at k (theta a)).
    { eapply lc_ty_at_monotone; [apply Hclosed|lia]. }
    rewrite (@open_ty_rec_lc_at (theta a) k (instantiate_ty theta U) Hlc).
    reflexivity.
  - f_equal; [apply IHT1|apply IHT2]; exact Hclosed.
  - f_equal. apply IHT. exact Hclosed.
  - reflexivity.
  - reflexivity.
Qed.

Lemma instantiate_fvar : forall theta gamma x,
  instantiate theta gamma (tm_fvar x) = gamma x.
Proof. reflexivity. Qed.

Lemma term_subst_update_same : forall gamma x v,
  term_subst_update gamma x v x = v.
Proof. intros. unfold term_subst_update. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma term_subst_update_other : forall gamma x v y,
  x <> y -> term_subst_update gamma x v y = gamma y.
Proof.
  intros. unfold term_subst_update.
  rewrite (proj2 (Nat.eqb_neq x y) H). reflexivity.
Qed.

Lemma wf_rty_erases : forall Delta RGamma R,
  wf_rty Delta RGamma R -> wf_ty Delta (erase R).
Proof.
  intros Delta RGamma R Hwf.
  induction Hwf as
    [L Delta RGamma T ps Hty Hq
    |L Delta RGamma R1 R2 Hwf1 IH1 Hbody IHbody
    |L Delta RGamma R1 R2 Hwf1 IH1 Hbody IHbody
    |L Delta RGamma R Hbody IHbody]; simpl.
  - exact Hty.
  - constructor.
    + exact IH1.
    + pose proof (IHbody (fresh L) (fresh_notin L)) as Hbodywf.
      rewrite erase_open_rty_tm in Hbodywf. exact Hbodywf.
  - pose proof (IHbody (fresh L) (fresh_notin L)) as Hbodywf.
    rewrite erase_open_rty_tm in Hbodywf. exact Hbodywf.
  - eapply WF_All with (L := L ++ fv_rty R). intros X HX.
    assert (HXL : ~ In X L).
    { intro Hin. apply HX. apply in_or_app. left. exact Hin. }
    specialize (IHbody X HXL). rewrite erase_open_rty_ty in IHbody.
    exact IHbody.
Qed.

Lemma close_open_ty_rec_fresh : forall k X T,
  ~ In X (fv_ty T) ->
  close_ty_rec k X (open_ty_rec k (Ty_FVar X) T) = T.
Proof.
  intros k X T. revert k X.
  induction T; intros k X Hfresh; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. simpl. rewrite Nat.eqb_refl. subst. reflexivity.
    + reflexivity.
  - assert (Hneq : X <> a).
    { intro E. subst. apply Hfresh. simpl. auto. }
    unfold close_ty_rec. simpl.
    rewrite (proj2 (Nat.eqb_neq X a) Hneq). reflexivity.
  - f_equal.
    + apply IHT1. intro H. apply Hfresh. simpl. apply in_or_app. left. exact H.
    + apply IHT2. intro H. apply Hfresh. simpl. apply in_or_app. right. exact H.
  - f_equal. apply IHT. assumption.
  - reflexivity.
  - reflexivity.
Qed.

Lemma open_ty_rec_injective_fresh : forall k X T U,
  ~ In X (fv_ty T) -> ~ In X (fv_ty U) ->
  open_ty_rec k (Ty_FVar X) T = open_ty_rec k (Ty_FVar X) U -> T = U.
Proof.
  intros k X T U HXT HXU Hopen.
  pose proof (close_open_ty_rec_fresh k X T HXT) as HT.
  pose proof (close_open_ty_rec_fresh k X U HXU) as HU.
  rewrite Hopen in HT. congruence.
Qed.

Lemma fv_ty_erase_in_ftv_rty : forall R,
  incl (fv_ty (erase R)) (ftv_rty R).
Proof.
  induction R; simpl.
  - intros X HX. apply in_or_app. left. exact HX.
  - intros X HX. apply in_app_or in HX. apply in_or_app.
    destruct HX as [HX|HX]; [left|right]; [apply IHR1|apply IHR2]; exact HX.
  - intros X HX. apply in_or_app. right. apply IHR2. exact HX.
  - exact IHR.
Qed.

Lemma subtype_erases : forall Delta RGamma R S,
  subtype Delta RGamma R S -> erase R = erase S.
Proof.
  intros Delta RGamma R S Hsub.
  induction Hsub as
    [Delta RGamma R
    |L Delta RGamma T ps qs Hent
    |L Delta RGamma R1 R2 S1 S2 Hdomain IHdomain Hcod IHcod
    |Delta RGamma v R1 R2 S Hval Htyp Hwit IHwit
    |L Delta RGamma R1 R2 S Hwf Hlc Hbody IHbody
    |L Delta RGamma R S Hbody IHbody
    |Delta RGamma R S U Hleft IHleft Hright IHright]; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal; [symmetry; exact IHdomain|].
    specialize (IHcod (fresh L) (fresh_notin L)).
    rewrite !erase_open_rty_tm in IHcod. exact IHcod.
  - rewrite erase_open_rty_tm in IHwit. exact IHwit.
  - specialize (IHbody (fresh L) (fresh_notin L)).
    rewrite erase_open_rty_tm in IHbody. exact IHbody.
  - set (X := fresh (L ++ ftv_rty R ++ ftv_rty S)).
    assert (HXL : ~ In X L).
    { unfold X. intro Hin. apply (fresh_notin (L ++ ftv_rty R ++ ftv_rty S)).
      apply in_or_app. left. exact Hin. }
    assert (HXR : ~ In X (fv_ty (erase R))).
    { intro Hin. apply (fresh_notin (L ++ ftv_rty R ++ ftv_rty S)).
      apply in_or_app. right. apply in_or_app. left.
      apply fv_ty_erase_in_ftv_rty. exact Hin. }
    assert (HXS : ~ In X (fv_ty (erase S))).
    { intro Hin. apply (fresh_notin (L ++ ftv_rty R ++ ftv_rty S)).
      apply in_or_app. right. apply in_or_app. right.
      apply fv_ty_erase_in_ftv_rty. exact Hin. }
    specialize (IHbody X HXL). rewrite !erase_open_rty_ty in IHbody.
    unfold open_ty in IHbody.
    f_equal. exact (open_ty_rec_injective_fresh 0 X (erase R) (erase S) HXR HXS IHbody).
  - congruence.
Qed.

Lemma lookup_rcontext_erased : forall RGamma x R,
  lookup_rcontext x RGamma = Some R ->
  lookup_context x (erase_context RGamma) = Some (erase R).
Proof.
  intros RGamma. induction RGamma as [|[y S] RGamma IH]; intros x R Hlookup.
  - discriminate.
  - simpl in Hlookup. simpl. destruct (Nat.eqb x y) eqn:E.
    + inversion Hlookup; subst. unfold update. simpl. reflexivity.
    + unfold update. simpl. eapply IH. exact Hlookup.
Qed.

Lemma context_included_update_existing : forall Gamma x T,
  lookup_context x Gamma = Some T ->
  context_included (update Gamma x T) Gamma.
Proof.
  intros Gamma x T Hx y U Hlookup.
  unfold update in Hlookup. simpl in Hlookup.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst. inversion Hlookup; subst. exact Hx.
  - exact Hlookup.
Qed.

Lemma has_rtype_erases : forall Delta RGamma t R,
  has_rtype Delta RGamma t R ->
  has_type Delta (erase_context RGamma) t (erase R).
Proof.
  intros Delta RGamma t R Hrt.
  induction Hrt as
    [Delta RGamma x R Hlookup Hwf
    |L Delta RGamma R1 body R2 Hwf1 Hbody IHbody
    |Delta RGamma t1 t2 R1 R2 IH1 IH2
    |L Delta RGamma body R IHbody
    |Delta RGamma t R U IH HwfU
    |Delta RGamma n
    |Delta RGamma t1 t2 IH1 IH2
    |Delta RGamma op t1 t2 IH1 IH2
    |Delta RGamma
    |Delta RGamma
    |Delta RGamma t1 t2 t3 R IH1 IH2 IH3
    |Delta RGamma v T ps Hcore Hval Hwf Hclosed Hholds
    |L Delta RGamma A p metric body R2 Hwf Hmetric Hbody IHbody
    |Delta RGamma x p t0 t1 R Hlookup IH0 IH1
    |Delta RGamma t R S IH HwfS Hsub]; simpl.
  - eapply T_Var.
    + eapply lookup_rcontext_erased. exact Hlookup.
    + eapply wf_rty_erases. exact Hwf.
  - eapply T_Abs with (L := L).
    + eapply wf_rty_erases. exact Hwf1.
    + intros x Hx. specialize (IHbody x Hx).
      rewrite erase_open_rty_tm in IHbody. exact IHbody.
  - eapply T_App; eauto.
  - eapply T_TAbs with (L := L). intros X HX.
    specialize (H X HX). rewrite erase_open_rty_ty in H. exact H.
  - rewrite erase_open_rty_ty. eapply T_TApp; [exact HwfU|exact H].
  - constructor.
  - econstructor; eauto.
  - econstructor; eauto.
  - constructor.
  - constructor.
  - eapply T_If; eauto.
  - exact Hcore.
  - assert (Hwf0 : wf_ty Delta (Ty_Arrow A (erase R2))).
    { pose proof (wf_rty_erases _ _ _ Hwf) as Hwf'. simpl in Hwf'. exact Hwf'. }
    inversion Hwf0; subst.
    eapply T_Fix with (L := L).
    + assumption.
    + assumption.
    + intros x Hx. exact (Hmetric x Hx).
    + intros f x Hf Hx.
      specialize (IHbody f x Hf Hx).
      rewrite erase_open_rty_tm in IHbody. exact IHbody.
  - pose proof (@lookup_rcontext_erased RGamma x (R_Refine Ty_Int p) Hlookup) as Hlook.
    simpl in Hlook.
    eapply T_IfZero.
    + eapply T_Var.
      * exact Hlook.
      * constructor.
    + change (has_type Delta (update (erase_context RGamma) x Ty_Int) t0 (erase R)) in IH1.
      eapply core_typing_context_weaken; [exact IH1|].
      eapply context_included_update_existing. exact Hlook.
    + change (has_type Delta (update (erase_context RGamma) x Ty_Int) t1 (erase R)) in IHHrt1.
      eapply core_typing_context_weaken; [exact IHHrt1|].
      eapply context_included_update_existing. exact Hlook.
  - rewrite <- (@subtype_erases Delta RGamma R S H). exact HwfS.
Qed.

Lemma instantiate_open_tm_ty_rec_general : forall t K theta gamma X U,
  type_substitution_closed theta -> term_substitution_closed gamma ->
  locally_closed_ty U ->
  instantiate (type_subst_update theta X U) gamma
    (open_tm_ty_rec K U t) =
  open_tm_ty_rec K (instantiate_ty (type_subst_update theta X U) U)
    (instantiate (type_subst_update theta X U) gamma t).
Proof.
  induction t; intros K theta gamma X U Htheta Hgamma HU; simpl.
  - reflexivity.
  - assert (Hlc : lc_tm_at K 0 (gamma a)).
    { eapply lc_tm_at_monotone; [apply Hgamma|lia|lia]. }
    rewrite (@open_tm_ty_rec_lc_at (gamma a) K 0
      (instantiate_ty (type_subst_update theta X U) U) Hlc). reflexivity.
  - f_equal.
    + exact (@instantiate_ty_open_ty_rec t K (type_subst_update theta X U) U
        (@type_subst_update_closed theta X U Htheta HU)).
    + apply IHt; assumption.
  - f_equal; [apply IHt1|apply IHt2]; assumption.
  - f_equal. apply IHt; assumption.
  - f_equal.
    + apply IHt; assumption.
    + exact (@instantiate_ty_open_ty_rec t0 K (type_subst_update theta X U) U
        (@type_subst_update_closed theta X U Htheta HU)).
  - reflexivity.
  - f_equal; [apply IHt1|apply IHt2]; assumption.
  - f_equal; [apply IHt1|apply IHt2]; assumption.
  - f_equal.
    + exact (@instantiate_ty_open_ty_rec t1 K (type_subst_update theta X U) U
        (@type_subst_update_closed theta X U Htheta HU)).
    + exact (@instantiate_ty_open_ty_rec t2 K (type_subst_update theta X U) U
        (@type_subst_update_closed theta X U Htheta HU)).
    + apply IHt1; assumption.
    + apply IHt2; assumption.
  - f_equal; [apply IHt1|apply IHt2|apply IHt3]; assumption.
  - reflexivity.
  - reflexivity.
  - f_equal; [apply IHt1|apply IHt2|apply IHt3]; assumption.
Qed.

Lemma core_typing_instantiation : forall Delta Gamma t T,
  has_type Delta Gamma t T -> forall Delta' Gamma' theta gamma,
    type_substitution_closed theta -> term_substitution_closed gamma ->
    type_substitution_wf Delta Delta' theta ->
    term_substitution_typed Gamma Delta' Gamma' theta gamma ->
    has_type Delta' Gamma' (instantiate theta gamma t)
      (instantiate_ty theta T).
Proof.
  intros Delta Gamma t T Hty. induction Hty;
    intros Delta' Gamma' theta gamma Hclosed HgammaClosed Htwf Hgamma.
  - simpl. eapply Hgamma; eauto.
  - simpl. eapply T_Abs with (L := L ++ dom_context Gamma' ++ fv_tm t2).
    + eapply wf_ty_instantiation; eauto.
    + intros x Hx.
      assert (HxL : ~ In x L) by (intro Hbad; apply Hx; apply in_or_app; left; exact Hbad).
      assert (Hxdom : ~ In x (dom_context Gamma')) by
        (intro Hbad; apply Hx; apply in_or_app; right; apply in_or_app; left; exact Hbad).
      assert (Hxft : ~ In x (fv_tm t2)) by
        (intro Hbad; apply Hx; apply in_or_app; right; apply in_or_app; right; exact Hbad).
      set (gammaX := term_subst_update gamma x (tm_fvar x)).
      assert (HgammaX : term_substitution_typed (update Gamma x T1) Delta'
        (update Gamma' x (instantiate_ty theta T1)) theta gammaX).
      { unfold gammaX. eapply term_substitution_typed_update_fvar; eauto.
        eapply wf_ty_instantiation; eauto. }
      assert (HgammaClosedX : term_substitution_closed gammaX).
      { unfold gammaX. eapply term_subst_update_closed.
        - exact HgammaClosed.
        - apply lc_tm_fvar. }
      specialize (H1 x HxL Delta' (update Gamma' x (instantiate_ty theta T1))
        theta gammaX Hclosed HgammaClosedX Htwf HgammaX).
      unfold open_tm in H1.
      rewrite (instantiate_open_tm_rec t2 0 theta gammaX (tm_fvar x)) in H1.
      2: exact HgammaClosedX.
      simpl in H1.
      unfold gammaX in H1.
      rewrite (instantiate_update_fresh_tm t2 theta gamma x (tm_fvar x) Hxft) in H1.
      unfold term_subst_update in H1. rewrite Nat.eqb_refl in H1.
      change (has_type Delta' (update Gamma' x (instantiate_ty theta T1))
        (open_tm (instantiate theta gamma t2) (tm_fvar x))
        (instantiate_ty theta T2)) in H1.
      exact H1.
  - simpl. eapply T_App; eauto.
  - simpl. eapply T_TAbs with
      (L := L ++ Delta ++ Delta' ++ ftv_tm t ++ ftv_context Gamma ++ fv_ty T).
    intros Y HY.
    assert (HYL : ~ In Y L) by (intro Hbad; apply HY; apply in_or_app; left; exact Hbad).
    assert (HYDelta : ~ In Y Delta) by
      (intro Hbad; apply HY; apply in_or_app; right; apply in_or_app; left; exact Hbad).
    assert (HYDelta' : ~ In Y Delta') by
      (intro Hbad; apply HY; apply in_or_app; right; apply in_or_app; right;
        apply in_or_app; left; exact Hbad).
    assert (HYft : ~ In Y (ftv_tm t)) by
      (intro Hbad; apply HY; apply in_or_app; right; apply in_or_app; right;
        apply in_or_app; right; apply in_or_app; left; exact Hbad).
    assert (HYctx : ~ In Y (ftv_context Gamma)) by
      (intro Hbad; apply HY; apply in_or_app; right; apply in_or_app; right;
        apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hbad).
    assert (HYty : ~ In Y (fv_ty T)) by
      (intro Hbad; apply HY; apply in_or_app; right; apply in_or_app; right;
        apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hbad).
    set (thetaY := type_subst_update theta Y (Ty_FVar Y)).
    assert (HclosedY : type_substitution_closed thetaY).
    { unfold thetaY. eapply type_subst_update_closed.
      - exact Hclosed.
      - apply lc_ty_fvar. }
    assert (HtwfY : type_substitution_wf (Y :: Delta) (Y :: Delta') thetaY).
    { unfold thetaY. eapply type_substitution_wf_update_fvar.
      - exact Htwf.
      - exact HYDelta. }
    assert (HgammaY : term_substitution_typed Gamma (Y :: Delta') Gamma' thetaY gamma).
    { unfold thetaY. eapply term_substitution_typed_ty_extend; eauto. }
    specialize (H0 Y HYL (Y :: Delta') Gamma' thetaY gamma
      HclosedY HgammaClosed HtwfY HgammaY).
    unfold thetaY, open_tm_ty, open_ty in H0.
    rewrite (instantiate_open_tm_ty_rec t 0 theta gamma Y Hclosed HgammaClosed HYft) in H0.
    rewrite (instantiate_ty_update_open T theta Y 0 Hclosed HYty) in H0.
    exact H0.
  - simpl. unfold open_ty. rewrite (instantiate_ty_open_ty_rec T 0 theta U Hclosed).
    eapply T_TApp.
    + eapply IHHty; eauto.
    + eapply wf_ty_instantiation; eauto.
  - constructor.
  - simpl. econstructor; eauto.
  - simpl. econstructor; eauto.
  - simpl. eapply T_Fix with (L := L ++ dom_context Gamma' ++ fv_tm metric ++ fv_tm body).
    + eapply wf_ty_instantiation; eauto.
    + eapply wf_ty_instantiation; eauto.
    + intros y Hy.
      assert (HyL : ~ In y L) by (intro Hbad; apply Hy; apply in_or_app; left; exact Hbad).
      assert (Hydom : ~ In y (dom_context Gamma')) by
        (intro Hbad; apply Hy; apply in_or_app; right; apply in_or_app; left; exact Hbad).
      assert (HyM : ~ In y (fv_tm metric)) by
        (intro Hbad; apply Hy; apply in_or_app; right; apply in_or_app; right;
          apply in_or_app; left; exact Hbad).
      set (gammaY := term_subst_update gamma y (tm_fvar y)).
      assert (HgY : term_substitution_typed (update Gamma y A) Delta'
        (update Gamma' y (instantiate_ty theta A)) theta gammaY).
      { unfold gammaY. eapply term_substitution_typed_update_fvar; eauto.
        eapply wf_ty_instantiation; eauto. }
      assert (HgCY : term_substitution_closed gammaY).
      { unfold gammaY. eapply term_subst_update_closed.
        - exact HgammaClosed.
        - apply lc_tm_fvar. }
      specialize (H2 y HyL Delta' (update Gamma' y (instantiate_ty theta A))
        theta gammaY Hclosed HgCY Htwf HgY).
      unfold open_tm in H2.
      rewrite (instantiate_open_tm_rec metric 0 theta gammaY (tm_fvar y)) in H2.
      2: exact HgCY.
      simpl in H2.
      unfold gammaY in H2.
      rewrite (instantiate_update_fresh_tm metric theta gamma y (tm_fvar y) HyM) in H2.
      unfold term_subst_update in H2. rewrite Nat.eqb_refl in H2.
      change (has_type Delta' (update Gamma' y (instantiate_ty theta A))
        (open_tm (instantiate theta gamma metric) (tm_fvar y)) Ty_Int) in H2.
      exact H2.
    + intros f x Hf Hx.
      assert (HfL : ~ In f L).
      { intro Hin. apply Hf. apply in_or_app. left. exact Hin. }
      assert (HxL : ~ In x L).
      { intro Hin. apply Hx. simpl. right. apply in_or_app. left. exact Hin. }
      assert (HxBound : ~ In x (f :: L)).
      { intro Hin. apply Hx. simpl. destruct Hin as [Hin|Hin].
        - left. exact Hin.
        - right. apply in_or_app. left. exact Hin. }
      assert (Hxf : x <> f).
      { intro E. subst x. apply Hx. simpl. left. reflexivity. }
      assert (Hfdom : ~ In f (dom_context Gamma')).
      { intro Hin. apply Hf. apply in_or_app. right. apply in_or_app. left. exact Hin. }
      assert (Hxdom : ~ In x (dom_context Gamma')).
      { intro Hin. apply Hx. simpl. right. apply in_or_app. right.
        apply in_or_app. left. exact Hin. }
      assert (Hffv : ~ In f (fv_tm body)).
      { intro Hin. apply Hf. apply in_or_app. right. apply in_or_app. right.
        apply in_or_app. right. exact Hin. }
      assert (Hxfv : ~ In x (fv_tm body)).
      { intro Hin. apply Hx. simpl. right. apply in_or_app. right.
        apply in_or_app. right. apply in_or_app. right. exact Hin. }
      set (gammaX := term_subst_update gamma x (tm_fvar x)).
      set (GammaX := update Gamma' x (instantiate_ty theta A)).
      assert (HgX : term_substitution_typed (update Gamma x A) Delta' GammaX theta gammaX).
      { unfold GammaX, gammaX. eapply term_substitution_typed_update_fvar; eauto.
        eapply wf_ty_instantiation; eauto. }
      assert (HgCX : term_substitution_closed gammaX).
      { unfold gammaX. eapply term_subst_update_closed.
        - exact HgammaClosed.
        - apply lc_tm_fvar. }
      set (gammaF := term_subst_update gammaX f (tm_fvar f)).
      assert (HfnotX : ~ In f (dom_context GammaX)).
      { unfold GammaX, dom_context, update. simpl. intro Hin.
        destruct Hin as [Hin|Hin].
        - apply Hxf. exact Hin.
        - apply Hfdom. exact Hin. }
      assert (HgF : term_substitution_typed
        (update (update Gamma x A) f (Ty_Arrow A B)) Delta'
        (update GammaX f (Ty_Arrow (instantiate_ty theta A) (instantiate_ty theta B)))
        theta gammaF).
      { unfold gammaF. eapply (@term_substitution_typed_update_fvar
          (update Gamma x A) Delta' GammaX theta gammaX f (Ty_Arrow A B)).
        - exact HgX.
        - exact HfnotX.
        - simpl. constructor; eapply wf_ty_instantiation; eauto. }
      assert (HgCF : term_substitution_closed gammaF).
      { unfold gammaF. eapply term_subst_update_closed.
        - exact HgCX.
        - apply lc_tm_fvar. }
      specialize (H4 f x HfL HxBound Delta' (update GammaX f
        (Ty_Arrow (instantiate_ty theta A) (instantiate_ty theta B)))
        theta gammaF Hclosed HgCF Htwf HgF).
      rewrite instantiate_open_fix_body in H4 by exact HgCF.
      rewrite !instantiate_fvar in H4.
      unfold gammaF, gammaX in H4.
      assert (Hfx : f <> x).
      { intro E. apply Hxf. symmetry. exact E. }
      rewrite term_subst_update_same in H4.
      rewrite (term_subst_update_other
        (term_subst_update gamma x (tm_fvar x)) f (tm_fvar f) x Hfx) in H4.
      rewrite term_subst_update_same in H4.
      rewrite (instantiate_update_fresh_tm body theta
        (term_subst_update gamma x (tm_fvar x)) f (tm_fvar f) Hffv) in H4.
      rewrite (instantiate_update_fresh_tm body theta gamma x (tm_fvar x) Hxfv) in H4.
      exact H4.
  - simpl. econstructor; eauto.
  - constructor.
  - constructor.
  - simpl. econstructor; eauto.
Qed.

(* The value interpretation records the erased typing judgment as well as the
   operational meaning of a refinement.  The computation interpretation is
   deliberately a safety property (rather than a termination property): a
   recursive function may diverge, but none of its finite execution prefixes
   may get stuck. *)
Fixpoint value_relation (n : nat) (R : rty) (v : tm) {struct n} : Prop :=
  match n with
  | 0 => value v
  | S n' =>
      value v /\ has_type [] [] v (erase R) /\
      match R with
      | R_Refine T p =>
          has_type [] [] v T /\ qualifier_holds (open_qualifier_tm p v)
      | R_Func R1 R2 =>
          forall w, value_relation n' R1 w ->
            computation_relation n' R2 (tm_app v w)
      | R_Exists R1 R2 =>
          exists w, value_relation n' R1 w /\
            value_relation n' (open_rty_tm R2 w) v
      | R_Poly R1 =>
          forall U, locally_closed_ty U ->
            computation_relation n' (open_rty_ty R1 U) (tm_tapp v U)
      end
  end
with computation_relation (n : nat) (R : rty) (t : tm) {struct n} : Prop :=
  match n with
  | 0 => True
  | S n' => forall u, multi t u ->
      (value u -> value_relation n' R u) /\
      (value u \/ exists u', u --> u')
  end.

Definition context_interpretation
    (n : nat) (theta : type_substitution) (gamma : term_substitution)
    (RGamma : rcontext) : Prop :=
  forall x R, lookup_rcontext x RGamma = Some R ->
    value_relation n (instantiate_rty theta gamma R) (gamma x).

Lemma context_interpretation_term_substitution_typed : forall n theta gamma RGamma,
  context_interpretation (S n) theta gamma RGamma ->
  term_substitution_typed (erase_context RGamma) [] [] theta gamma.
Proof.
  intros n theta gamma RGamma Hctx.
  unfold term_substitution_typed.
  intros x T Hlookup.
  destruct (lookup_erase_context_inv RGamma x T Hlookup) as [R [Hfind Herase]].
  pose proof (Hctx x R Hfind) as Hrel.
  simpl in Hrel. destruct Hrel as [_ [Hty _]].
  rewrite erase_instantiate_rty, Herase in Hty.
  exact Hty.
Qed.

Lemma context_interpretation_formulas : forall n theta gamma RGamma,
  term_substitution_closed gamma ->
  context_interpretation (S n) theta gamma RGamma ->
  context_formulas_hold theta gamma RGamma.
Proof.
  intros n theta gamma RGamma Hclosed Hctx x T p Hlookup.
  specialize (Hctx x (R_Refine T p) Hlookup).
  simpl in Hctx.
  destruct Hctx as [_ [_ [_ Hpred]]].
  rewrite instantiate_formula_open_tm by assumption.
  simpl. exact Hpred.
Qed.

Lemma computation_relation_succ_adequate : forall n R t,
  computation_relation (S n) R t ->
  forall u, multi t u -> value u \/ exists u', u --> u'.
Proof.
  intros n R t H u Hu.
  exact (proj2 (H u Hu)).
Qed.

Lemma value_relation_refine_core : forall n T p v,
  value_relation (S n) (R_Refine T p) v ->
  value v /\ has_type [] [] v T.
Proof.
  intros n T p v H. simpl in H. destruct H as [Hv [_ [Hty _]]].
  split; assumption.
Qed.

Lemma instantiate_update_fresh_rty : forall R theta gamma x v,
  ~ In x (fv_rty R) ->
  instantiate_rty theta (term_subst_update gamma x v) R =
  instantiate_rty theta gamma R.
Proof.
  induction R; intros theta gamma x v Hfresh; simpl in *.
  - f_equal. change (instantiate_formula theta (term_subst_update gamma x v) q =
      instantiate_formula theta gamma q).
    apply instantiate_update_fresh_formula. assumption.
  - f_equal.
    + apply IHR1. intuition.
    + apply IHR2. intuition.
  - f_equal.
    + apply IHR1. intuition.
    + apply IHR2. intuition.
  - f_equal. apply IHR. assumption.
Qed.

Fixpoint dom_rcontext (RGamma : rcontext) : list atom :=
  match RGamma with
  | [] => []
  | (x, _) :: RGamma' => x :: dom_rcontext RGamma'
  end.

Lemma lookup_rcontext_in_dom : forall x RGamma R,
  lookup_rcontext x RGamma = Some R -> In x (dom_rcontext RGamma).
Proof.
  intros x RGamma. induction RGamma as [|[y S] RGamma IH]; intros R Hlook.
  - discriminate.
  - simpl in *. destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. subst y. left. reflexivity.
    + right. eapply IH. exact Hlook.
Qed.

Lemma lookup_rcontext_fv_rty : forall y RGamma R,
  lookup_rcontext y RGamma = Some R ->
  forall a, In a (fv_rty R) -> In a (fv_rcontext RGamma).
Proof.
  intros y RGamma. induction RGamma as [|[z S] RGamma IH]; intros R Hlookup a Ha.
  - discriminate.
  - simpl in Hlookup. simpl. destruct (Nat.eqb y z) eqn:E.
    + inversion Hlookup; subst. apply in_or_app. left. exact Ha.
    + apply in_or_app. right. eapply IH; eauto.
Qed.

Lemma fresh_for_rcontext : forall a RGamma,
  ~ In a (fv_rcontext RGamma ++ dom_rcontext RGamma) ->
  forall y R, lookup_rcontext y RGamma = Some R ->
    ~ In a (fv_rty R) /\ a <> y.
Proof.
  intros a RGamma Hfresh y R Hlookup.
  split.
  - intro Hin. apply Hfresh. apply in_or_app. left.
    eapply lookup_rcontext_fv_rty; eauto.
  - intro E. subst y. apply Hfresh. apply in_or_app. right.
    eapply lookup_rcontext_in_dom; eauto.
Qed.

Lemma context_interpretation_extend : forall n theta gamma RGamma x T p v,
  term_substitution_closed gamma -> locally_closed_tm v ->
  context_interpretation (S n) theta gamma RGamma ->
  value_relation (S n) (instantiate_rty theta gamma (R_Refine T p)) v ->
  (forall y R, lookup_rcontext y RGamma = Some R ->
    ~ In x (fv_rty R) /\ x <> y) ->
  context_interpretation (S n) theta (term_subst_update gamma x v)
    (update_rcontext RGamma x (R_Refine T Pred_True)).
Proof.
  intros n theta gamma RGamma x T p v Hgamma Hv Hctx Hrel Hfresh y R Hlookup.
  unfold update_rcontext in Hlookup. simpl in Hlookup.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst y. inversion Hlookup; subst R.
    unfold term_subst_update. rewrite Nat.eqb_refl.
    simpl.
    destruct (value_relation_refine_core n (instantiate_ty theta T)
      (instantiate_qualifier theta gamma p) v Hrel) as [Hv' Hty].
    repeat split; assumption || exact I.
  - assert (Hyx : y <> x) by (apply Nat.eqb_neq; exact E).
    assert (Hsuby : term_subst_update gamma x v y = gamma y).
    { unfold term_subst_update. destruct (Nat.eqb x y) eqn:E'.
      - apply Nat.eqb_eq in E'. exfalso. apply Hyx. symmetry. exact E'.
      - reflexivity. }
    pose proof (Hctx y R Hlookup) as HrelY.
    rewrite instantiate_update_fresh_rty.
    + rewrite Hsuby. exact HrelY.
    + destruct (Hfresh y R Hlookup) as [Hnot _]. exact Hnot.
Qed.

Lemma context_interpretation_extend_any : forall n theta gamma RGamma x R w,
  term_substitution_closed gamma ->
  context_interpretation (S n) theta gamma RGamma ->
  value_relation (S n) (instantiate_rty theta gamma R) w ->
  ~ In x (fv_rty R) ->
  (forall y S, lookup_rcontext y RGamma = Some S ->
    ~ In x (fv_rty S) /\ x <> y) ->
  context_interpretation (S n) theta (term_subst_update gamma x w)
    (update_rcontext RGamma x R).
Proof.
  intros n theta gamma RGamma x R w Hgamma Hctx Hrel HfreshR Hfresh y S Hlookup.
  pose proof Hrel as Hrel0. simpl in Hrel0. destruct Hrel0 as [Hv _].
  pose proof (value_regular w Hv) as Hloc.
  unfold update_rcontext in Hlookup. simpl in Hlookup.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst y. inversion Hlookup; subst S.
    rewrite instantiate_update_fresh_rty by exact HfreshR.
    unfold term_subst_update. rewrite Nat.eqb_refl. exact Hrel.
  - assert (Hyx : y <> x) by (apply Nat.eqb_neq; exact E).
    assert (Hsuby : term_subst_update gamma x w y = gamma y).
    { unfold term_subst_update. destruct (Nat.eqb x y) eqn:E'.
      - apply Nat.eqb_eq in E'. exfalso. apply Hyx. symmetry. exact E'.
      - reflexivity. }
    pose proof (Hctx y S Hlookup) as HrelY.
    rewrite instantiate_update_fresh_rty.
    + rewrite Hsuby. exact HrelY.
    + destruct (Hfresh y S Hlookup) as [Hnot _]. exact Hnot.
Qed.

Lemma subtype_refine_value_relation : forall n Delta RGamma L T ps qs,
  (forall a, ~ In a L ->
    entails Delta (update_rcontext RGamma a (R_Refine T Pred_True))
      (open_qualifier_tm ps (tm_fvar a))
      (open_qualifier_tm qs (tm_fvar a))) ->
  forall theta gamma x w,
    ~ In x L ->
    term_substitution_closed gamma ->
    (forall y, value (gamma y)) ->
    context_interpretation (S n) theta gamma RGamma ->
    (forall y R, lookup_rcontext y RGamma = Some R ->
      ~ In x (fv_rty R) /\ x <> y) ->
    ~ In x (fv_qualifier ps) -> ~ In x (fv_qualifier qs) ->
    value_relation (S n) (instantiate_rty theta gamma (R_Refine T ps)) w ->
    value_relation (S n) (instantiate_rty theta gamma (R_Refine T qs)) w.
Proof.
  intros n Delta RGamma L T ps qs Hsub theta gamma a w Hav Hgamma Hvalues Hctx
    Hfresh Hps Hqs Hrel.
  simpl in Hrel.
  destruct Hrel as [Hv [Hcore [Hty Hpred]]].
  pose proof (value_regular w Hv) as Hloc.
  set (gamma' := term_subst_update gamma a w).
  assert (Hclosed' : term_substitution_closed gamma').
  { unfold gamma'. apply term_subst_update_closed; assumption. }
  assert (HaFresh : forall y R, lookup_rcontext y RGamma = Some R ->
      ~ In a (fv_rty R) /\ a <> y).
  { intros y R Hlookup. specialize (Hfresh y R Hlookup). tauto. }
  assert (Hrel' : value_relation (S n)
      (instantiate_rty theta gamma (R_Refine T ps)) w).
  { simpl. repeat split; assumption. }
  assert (Hctx' : context_interpretation (S n) theta gamma'
      (update_rcontext RGamma a (R_Refine T Pred_True))).
  { unfold gamma'. eapply context_interpretation_extend.
    - exact Hgamma.
    - exact Hloc.
    - exact Hctx.
    - exact Hrel'.
    - exact HaFresh. }
  assert (Hform' : context_formulas_hold theta gamma'
      (update_rcontext RGamma a (R_Refine T Pred_True))).
  { eapply context_interpretation_formulas; eauto. }
  assert (Hvalues' : forall y, value (gamma' y)).
  { intro y. unfold gamma'. unfold term_subst_update.
    destruct (Nat.eqb a y) eqn:E.
    - exact Hv.
    - apply Hvalues. }
  specialize (Hsub a Hav).
  assert (Ha : instantiate theta gamma' (tm_fvar a) = w).
  { unfold gamma'. simpl. unfold term_subst_update. rewrite Nat.eqb_refl. reflexivity. }
  assert (Hsource : qualifier_holds
      (instantiate_formula theta gamma'
        (open_qualifier_tm ps (tm_fvar a)))).
  { rewrite instantiate_formula_open_tm by exact Hclosed'.
    rewrite Ha. change (qualifier_holds
      (open_qualifier_tm (instantiate_formula theta gamma' ps) w)).
    unfold gamma' in *.
    rewrite instantiate_update_fresh_formula by assumption.
    change (qualifier_holds
      (open_qualifier_tm (instantiate_formula theta gamma ps) w)).
    exact Hpred. }
  pose proof (entails_sound Delta
    (update_rcontext RGamma a (R_Refine T Pred_True))
    (open_qualifier_tm ps (tm_fvar a))
    (open_qualifier_tm qs (tm_fvar a)) Hsub theta gamma'
    Hvalues' Hform' Hsource) as Htarget.
  simpl. repeat split; try assumption.
  rewrite instantiate_formula_open_tm in Htarget by exact Hclosed'.
  rewrite Ha in Htarget.
  unfold gamma' in Htarget.
  rewrite instantiate_update_fresh_formula in Htarget by assumption.
  change (qualifier_holds
    (open_qualifier_tm (instantiate_formula theta gamma qs) w)).
  exact Htarget.
Qed.

Lemma subtype_refine_value_relation_fresh : forall n Delta RGamma L T ps qs,
  (forall a, ~ In a L ->
    entails Delta (update_rcontext RGamma a (R_Refine T Pred_True))
      (open_qualifier_tm ps (tm_fvar a))
      (open_qualifier_tm qs (tm_fvar a))) ->
  forall theta gamma w,
    term_substitution_closed gamma ->
    (forall y, value (gamma y)) ->
    context_interpretation (S n) theta gamma RGamma ->
    value_relation (S n) (instantiate_rty theta gamma (R_Refine T ps)) w ->
    value_relation (S n) (instantiate_rty theta gamma (R_Refine T qs)) w.
Proof.
  intros n Delta RGamma L T ps qs Hsub theta gamma w Hclosed Hvalues Hctx Hrel.
  set (a := fresh (L ++ (fv_rcontext RGamma ++
    (dom_rcontext RGamma ++ (fv_qualifier ps ++ fv_qualifier qs))))).
  assert (Hfreshall : ~ In a
      (L ++ (fv_rcontext RGamma ++
       (dom_rcontext RGamma ++ (fv_qualifier ps ++ fv_qualifier qs))))).
  { unfold a. apply fresh_notin. }
  assert (HnotL : ~ In a L).
  { intro Hin. apply Hfreshall. apply in_or_app. left. exact Hin. }
  assert (Hnotctx : ~ In a (fv_rcontext RGamma ++ dom_rcontext RGamma)).
  { intro Hin. apply Hfreshall. apply in_or_app. right.
    apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
    - apply in_or_app. left. exact Hin.
    - apply in_or_app. right. apply in_or_app. left. exact Hin. }
  assert (Hnotps : ~ In a (fv_qualifier ps)).
  { intro Hin. apply Hfreshall. apply in_or_app. right.
    apply in_or_app. right. apply in_or_app. right.
    apply in_or_app. left. exact Hin. }
  assert (Hnotqs : ~ In a (fv_qualifier qs)).
  { intro Hin. apply Hfreshall. apply in_or_app. right.
    apply in_or_app. right. apply in_or_app. right.
    apply in_or_app. right. exact Hin. }
  eapply subtype_refine_value_relation; eauto using fresh_for_rcontext.
Qed.

Lemma context_formulas_hold_update_fresh : forall theta gamma RGamma x v,
  term_substitution_closed gamma -> locally_closed_tm v ->
  context_formulas_hold theta gamma RGamma ->
  (forall y T p, lookup_rcontext y RGamma = Some (R_Refine T p) ->
    ~ In x (fv_qualifier p) /\ x <> y) ->
  context_formulas_hold theta (term_subst_update gamma x v) RGamma.
Proof.
  intros theta gamma RGamma x v Hgamma Hv Hholds Hfresh.
  intros y T p Hlookup.
  rewrite instantiate_update_fresh_open_formula.
  - apply Hholds with (x := y) (T := T) (p := p). exact Hlookup.
  - exact Hgamma.
  - exact Hv.
  - destruct (Hfresh y T p Hlookup) as [Hfreshp _]. exact Hfreshp.
  - simpl. destruct (Hfresh y T p Hlookup) as [_ Hxy].
    intro E. destruct E as [E|[]]. apply Hxy. symmetry. exact E.
Qed.

Lemma context_formulas_hold_extend_fresh : forall theta gamma RGamma x T v,
  term_substitution_closed gamma -> locally_closed_tm v ->
  context_formulas_hold theta gamma RGamma ->
  (forall y U p, lookup_rcontext y RGamma = Some (R_Refine U p) ->
    ~ In x (fv_qualifier p) /\ x <> y) ->
  context_formulas_hold theta (term_subst_update gamma x v)
    (update_rcontext RGamma x (R_Refine T Pred_True)).
Proof.
  intros theta gamma RGamma x T v Hgamma Hv Hholds Hfresh.
  intros y U p Hlookup.
  unfold update_rcontext in Hlookup. simpl in Hlookup.
  destruct (Nat.eqb y x) eqn:E.
  - inversion Hlookup; subst. simpl. exact I.
  - pose proof (context_formulas_hold_update_fresh theta gamma RGamma x v
      Hgamma Hv Hholds Hfresh) as Hupdated.
    exact (Hupdated y U p Hlookup).
Qed.

Lemma computation_relation_one_adequate : forall R t,
  computation_relation 1 R t ->
  forall u, multi t u -> value u \/ exists u', u --> u'.
Proof.
  intros R t H u Hu.
  exact (proj2 (H u Hu)).
Qed.

Lemma computation_relation_value_one : forall R v,
  value v -> computation_relation 1 R v.
Proof.
  intros R v Hv u Hmulti.
  pose proof (value_multi_eq v u Hv Hmulti) as ->.
  split.
  - intros _. exact Hv.
  - left. exact Hv.
Qed.

Lemma wf_ty_locally_closed : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T H. induction H; try constructor; eauto.
  eapply lc_ty_at_open_inv with (X := fresh L).
  match goal with
  | Hopen : forall X, ~ In X L -> locally_closed_ty (open_ty _ (Ty_FVar X)) |- _ =>
      specialize (Hopen (fresh L) (fresh_notin L)); exact Hopen
  end.
Qed.

Lemma instantiate_identity_ty : forall T,
  instantiate_ty identity_type_substitution T = T.
Proof.
  induction T; cbn [instantiate_ty identity_type_substitution]; try reflexivity.
  - f_equal; assumption.
  - f_equal; assumption.
Qed.

Lemma instantiate_identity_tm : forall t,
  instantiate identity_type_substitution identity_term_substitution t = t.
Proof.
  induction t; cbn [instantiate identity_type_substitution identity_term_substitution];
    rewrite ?instantiate_identity_ty, ?IHt, ?IHt1, ?IHt2, ?IHt3; reflexivity.
Qed.

Lemma has_type_locally_closed : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T Hty. induction Hty.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + eapply wf_ty_locally_closed; eauto.
    + apply lc_tm_at_open_tm_inv with (x := fresh L).
      unfold open_tm. apply H1. apply fresh_notin.
  - constructor; assumption.
  - apply lc_tm_tabs.
    apply lc_tm_at_open_ty_inv with (X := fresh L).
    unfold open_tm_ty. apply H0. apply fresh_notin.
  - constructor; [assumption|eapply wf_ty_locally_closed; eauto].
  - constructor.
  - constructor; assumption.
  - constructor; assumption.
  - apply lc_tm_fix.
    + eapply wf_ty_locally_closed; eauto.
    + eapply wf_ty_locally_closed; eauto.
    + apply lc_tm_at_open_tm_inv with (x := fresh L).
      unfold open_tm. apply H2. apply fresh_notin.
    + set (f := fresh L). set (x := fresh (f :: L)).
      assert (Hf : ~ In f L) by (unfold f; apply fresh_notin).
      assert (Hx : ~ In x (f :: L)) by (unfold x; apply fresh_notin).
      pose proof (H4 f x Hf Hx) as Hopen.
      unfold open_fix_body, open_tm in Hopen.
      apply lc_tm_at_open_tm_inv with (x := x) in Hopen.
      apply lc_tm_at_open_tm_inv with (x := f) in Hopen.
      exact Hopen.
  - constructor; assumption.
  - constructor.
  - constructor.
  - constructor; assumption.
Qed.

Lemma core_typing_beta_abs : forall T body U v,
  has_type [] [] (tm_abs T body) (Ty_Arrow T U) ->
  value v -> has_type [] [] v T ->
  has_type [] [] (open_tm body v) U.
Proof.
  intros T body U v Hab Hv Hvt.
  inversion Hab; subst.
  set (x := fresh (L ++ fv_tm body)).
  assert (HxL : ~ In x L).
  { unfold x. intro Hin. apply fresh_notin with (L := L ++ fv_tm body).
    apply in_or_app. left. exact Hin. }
  assert (Hxbody : ~ In x (fv_tm body)).
  { unfold x. intro Hin. apply fresh_notin with (L := L ++ fv_tm body).
    apply in_or_app. right. exact Hin. }
  set (gamma := term_subst_update identity_term_substitution x v).
  assert (Hgclosed : term_substitution_closed gamma).
  { unfold gamma. apply term_subst_update_closed; [apply identity_term_substitution_closed|].
    apply value_regular. exact Hv. }
  assert (Htyped : term_substitution_typed (update [] x T) [] []
      identity_type_substitution gamma).
  { unfold term_substitution_typed. intros y V Hlook.
    simpl in Hlook. destruct (Nat.eqb y x) eqn:E.
    - apply Nat.eqb_eq in E. subst y. inversion Hlook; subst V.
      unfold gamma, term_subst_update. rewrite Nat.eqb_refl.
      rewrite instantiate_identity_ty. exact Hvt.
    - discriminate. }
  assert (Htwf : type_substitution_wf [] [] identity_type_substitution).
  { unfold type_substitution_wf. intros X HX. contradiction. }
  pose proof (core_typing_instantiation [] (update [] x T)
    (open_tm body (tm_fvar x)) U (H5 x HxL)
    [] [] identity_type_substitution gamma
    identity_type_substitution_closed Hgclosed Htwf Htyped) as Hinst.
  unfold open_tm in Hinst.
  rewrite (instantiate_open_tm_rec body 0 identity_type_substitution gamma
    (tm_fvar x) Hgclosed) in Hinst.
  unfold gamma in Hinst.
  rewrite (instantiate_update_fresh_tm body identity_type_substitution
    identity_term_substitution x v Hxbody) in Hinst.
  rewrite instantiate_identity_tm in Hinst.
  simpl in Hinst.
  unfold term_subst_update in Hinst. rewrite Nat.eqb_refl in Hinst.
  rewrite instantiate_identity_ty in Hinst. unfold open_tm. exact Hinst.
Qed.

Lemma type_substitution_wf_update : forall Delta Delta' theta X U,
  type_substitution_wf Delta Delta' theta ->
  wf_ty Delta' U ->
  type_substitution_wf (X :: Delta) Delta'
    (type_subst_update theta X U).
Proof.
  intros Delta Delta' theta X U Hwf HU Y HY.
  unfold type_subst_update. destruct (Nat.eqb X Y) eqn:E.
  - exact HU.
  - apply Hwf. simpl in HY. destruct HY as [HY|HY].
    + subst Y. rewrite Nat.eqb_refl in E. discriminate.
    + exact HY.
Qed.

Lemma core_typing_beta_tabs : forall body T U,
  has_type [] [] (tm_tabs body) (Ty_All T) ->
  locally_closed_ty U ->
  has_type [] [] (open_tm_ty body U) (open_ty T U).
Proof.
  intros body T U Habs HU. inversion Habs; subst.
  set (X := fresh (L ++ fv_tm body ++ fv_ty T ++ fv_ty U)).
  assert (HX : ~ In X L).
  { unfold X. intro Hin. apply fresh_notin with
      (L := L ++ fv_tm body ++ fv_ty T ++ fv_ty U).
    apply in_or_app. left. exact Hin. }
  assert (HXbody : ~ In X (fv_tm body)).
  { unfold X. intro Hin. apply fresh_notin with
      (L := L ++ fv_tm body ++ fv_ty T ++ fv_ty U).
    apply in_or_app. right. apply in_or_app. left. exact Hin. }
  assert (HXty : ~ In X (fv_ty T)).
  { unfold X. intro Hin. apply fresh_notin with
      (L := L ++ fv_tm body ++ fv_ty T ++ fv_ty U).
    apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hin. }
  assert (HXU : ~ In X (fv_ty U)).
  { unfold X. intro Hin. apply fresh_notin with
      (L := L ++ fv_tm body ++ fv_ty T ++ fv_ty U).
    apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact Hin. }
  set (theta := type_subst_update identity_type_substitution X U).
  assert (Htc : type_substitution_closed theta).
  { unfold theta. apply type_subst_update_closed.
    - apply identity_type_substitution_closed.
    - exact HU. }
  assert (Htwf : type_substitution_wf (X :: []) [] theta).
  { unfold theta. eapply type_substitution_wf_update.
    - intros Y HY. contradiction.
    - constructor. }
  assert (Htyped : term_substitution_typed [] [] [] theta identity_term_substitution).
  { unfold term_substitution_typed. intros y V Hlook. discriminate. }
  pose proof (core_typing_instantiation (X :: []) []
    (open_tm_ty body (Ty_FVar X)) (open_ty T (Ty_FVar X))
    (H0 X HX) [] [] theta identity_term_substitution
    Htc identity_term_substitution_closed Htwf Htyped) as Hinst.
  unfold open_ty in Hinst.
  rewrite (instantiate_open_tm_ty_rec_general body 0
    identity_type_substitution identity_term_substitution X U
    identity_type_substitution_closed identity_term_substitution_closed HU) in Hinst.
  assert (HinstU : instantiate_ty theta U = U).
  { unfold theta. apply instantiate_ty_update_fresh. exact HXU. }
  rewrite HinstU in Hinst.
  assert (HinstT : instantiate_ty theta (open_ty T (Ty_FVar X)) = open_ty T U).
  { unfold theta, open_ty. rewrite instantiate_ty_update_open.
    - reflexivity.
    - apply identity_type_substitution_closed.
    - exact HXty. }
  rewrite HinstT in Hinst.
  assert (Hbodyeq : instantiate theta identity_term_substitution body = body).
  { unfold theta. rewrite instantiate_update_fresh_tm with
      (gamma := identity_term_substitution) (v := Ty_FVar X).
    - rewrite instantiate_identity_tm. reflexivity.
    - exact HXbody. }
  rewrite Hbodyeq in Hinst. exact Hinst.
Qed.

Theorem never_stuck : forall (t t' : tm) (R : rty),
  has_rtype [] empty_rcontext t R ->
  multi t t' ->
  value t' \/ exists t'' : tm, t' --> t''.
Proof.
  (* Complete this proof. *)
Qed.

End SystemFRefinementIfRecursionTask.
