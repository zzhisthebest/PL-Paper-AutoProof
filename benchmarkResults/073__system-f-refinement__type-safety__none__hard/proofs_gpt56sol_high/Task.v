From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
From Stdlib Require Import ZArith.BinInt.

Module SystemFRefinement.

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
  | Ty_Int : ty.

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
  | tm_arith : integer_operator -> tm -> tm -> tm.

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
  end.

Definition open_tm (t u : tm) : tm := open_tm_rec 0 u t.

Fixpoint fv_ty (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow T1 T2 => fv_ty T1 ++ fv_ty T2
  | Ty_All T1 => fv_ty T1
  | Ty_Int => []
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
  | lc_ty_int : forall k, lc_ty_at k Ty_Int.

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
      lc_tm_at K k (tm_arith op t1 t2).

Definition locally_closed_tm (t : tm) : Prop := lc_tm_at 0 0 t.

Inductive value : tm -> Prop :=
  | v_abs : forall T t,
      locally_closed_tm (tm_abs T t) ->
      value (tm_abs T t)
  | v_tabs : forall t,
      locally_closed_tm (tm_tabs t) ->
      value (tm_tabs t)
  | v_int : forall n : Z, value (tm_int n).

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
  | WF_Int : forall Delta, wf_ty Delta Ty_Int.

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
      has_type Delta Gamma (tm_arith op t1 t2) Ty_Int.

Fixpoint max_atom (L : list atom) : atom :=
  match L with
  | [] => 0
  | x :: L' => Nat.max x (max_atom L')
  end.

Definition fresh (L : list atom) : atom := S (max_atom L).

End SystemFRefinement.

From Stdlib Require Import Arith.PeanoNat Lists.List ZArith.BinInt.
Module SystemFRefinementLogic.
Import ListNotations SystemFRefinement.

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

End SystemFRefinementLogic.

From Stdlib Require Import Arith.PeanoNat Lists.List Lia ZArith.BinInt.
Module SystemFRefinementTyping.
Import ListNotations.
Import SystemFRefinement.
Export SystemFRefinementLogic.

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

End SystemFRefinementTyping.

Module SystemFRefinementEvaluation.
Import ListNotations SystemFRefinement SystemFRefinementLogic SystemFRefinementTyping.

Inductive multi : tm -> tm -> Prop :=
  | multi_refl : forall t, multi t t
  | multi_step : forall t1 t2 t3,
      t1 --> t2 -> multi t2 t3 -> multi t1 t3.
Notation "t '-->*' u" := (multi t u) (at level 40).

End SystemFRefinementEvaluation.

Module SystemFRefinementTask.
Import ListNotations SystemFRefinement SystemFRefinementLogic SystemFRefinementTyping SystemFRefinementEvaluation.
From Equations Require Import Equations.

(** A small step-indexed logical relation.  Indexing is only used to make the
    (negative) occurrence at function types well founded. *)

Fixpoint safe_for (n : nat) (t : tm) : Prop :=
  match n with
  | 0 => True
  | S n' =>
      value t \/
      ((exists u, t --> u) /\ forall u, t --> u -> safe_for n' u)
  end.

Fixpoint rty_size (R : rty) : nat :=
  match R with
  | R_Refine _ _ => 1
  | R_Func A B | R_Exists A B => S (rty_size A + rty_size B)
  | R_Poly A => S (rty_size A)
  end.

Lemma size_open_rty_tm : forall R k u,
  rty_size (open_rty_tm_rec k u R) = rty_size R.
Proof. induction R; intros; simpl; f_equal; auto. Qed.
Lemma size_open_rty_ty : forall R k U,
  rty_size (open_rty_ty_rec k U R) = rty_size R.
Proof. induction R; intros; simpl; f_equal; auto. Qed.

Equations LRhead (n : nat) (V : rty -> tm -> Prop) (R : rty) (v : tm) : Prop
  by wf (rty_size R) lt :=
LRhead n V (R_Refine T q) v :=
  value v /\ (T = Ty_Int -> exists z, v = tm_int z) /\
  qualifier_holds (open_qualifier_tm q v);
LRhead n V (R_Func A B) v :=
  value v /\ exists T body, v = tm_abs T body /\
    forall w, (V A w /\ LRhead n V A w) ->
      safe_for (S n) (tm_app v w) /\
      forall u, multi (tm_app v w) u -> value u ->
        (V (open_rty_tm B w) u /\ LRhead n V (open_rty_tm B w) u);
LRhead n V (R_Exists A B) v :=
  value v /\ exists w, (V A w /\ LRhead n V A w) /\
    (V (open_rty_tm B w) v /\ LRhead n V (open_rty_tm B w) v);
LRhead n V (R_Poly B) v :=
  value v /\ exists body, v = tm_tabs body /\
    forall U, locally_closed_ty U ->
      safe_for (S n) (tm_tapp v U) /\
      forall u, multi (tm_tapp v U) u -> value u ->
        (V (open_rty_ty B U) u /\ LRhead n V (open_rty_ty B U) u).
Next Obligation. simpl; lia. Qed.
Next Obligation. unfold open_rty_tm; rewrite size_open_rty_tm; simpl; lia. Qed.
Next Obligation. simpl; lia. Qed.
Next Obligation. unfold open_rty_tm; rewrite size_open_rty_tm; simpl; lia. Qed.
Next Obligation. unfold open_rty_ty; rewrite size_open_rty_ty; simpl; lia. Qed.

Fixpoint LRv (n : nat) (R : rty) (v : tm) : Prop :=
  match n with
  | 0 => value v
  | S n' => LRv n' R v /\ LRhead n' (LRv n') R v
  end.

Definition LRe (n : nat) (R : rty) (t : tm) : Prop :=
  locally_closed_tm t /\ safe_for n t /\
  forall v, multi t v -> value v -> LRv n R v.

Definition logical_relation (R : rty) (t : tm) : Prop :=
  forall n, LRe n R t.

Lemma LRv_value0 : forall n R v, LRv n R v -> value v.
Proof. induction n; simpl; intuition. Qed.

(** Simultaneous closing substitutions are functions.  This avoids all
    irrelevant ordering issues of list substitutions. *)
Fixpoint inst_ty (eta : atom -> ty) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => eta X
  | Ty_Arrow A B => Ty_Arrow (inst_ty eta A) (inst_ty eta B)
  | Ty_All A => Ty_All (inst_ty eta A)
  | Ty_Int => Ty_Int
  end.

Fixpoint inst_tm (eta : atom -> ty) (rho : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => rho x
  | tm_abs T b => tm_abs (inst_ty eta T) (inst_tm eta rho b)
  | tm_app a b => tm_app (inst_tm eta rho a) (inst_tm eta rho b)
  | tm_tabs b => tm_tabs (inst_tm eta rho b)
  | tm_tapp a T => tm_tapp (inst_tm eta rho a) (inst_ty eta T)
  | tm_int z => tm_int z
  | tm_div a b => tm_div (inst_tm eta rho a) (inst_tm eta rho b)
  | tm_arith op a b => tm_arith op (inst_tm eta rho a) (inst_tm eta rho b)
  end.

Fixpoint inst_q (eta : atom -> ty) (rho : atom -> tm) (q : qualifier) : qualifier :=
  match q with
  | Pred_True => Pred_True | Pred_False => Pred_False
  | Pred_Eq a b => Pred_Eq (inst_tm eta rho a) (inst_tm eta rho b)
  | Pred_Lt a b => Pred_Lt (inst_tm eta rho a) (inst_tm eta rho b)
  | Pred_Le a b => Pred_Le (inst_tm eta rho a) (inst_tm eta rho b)
  | Pred_And p q => Pred_And (inst_q eta rho p) (inst_q eta rho q)
  | Pred_Or p q => Pred_Or (inst_q eta rho p) (inst_q eta rho q)
  | Pred_Not p => Pred_Not (inst_q eta rho p)
  end.

Fixpoint inst_rty (eta : atom -> ty) (rho : atom -> tm) (R : rty) : rty :=
  match R with
  | R_Refine T q => R_Refine (inst_ty eta T) (inst_q eta rho q)
  | R_Func A B => R_Func (inst_rty eta rho A) (inst_rty eta rho B)
  | R_Exists A B => R_Exists (inst_rty eta rho A) (inst_rty eta rho B)
  | R_Poly A => R_Poly (inst_rty eta rho A)
  end.

Definition extend_tm (rho : atom -> tm) (x : atom) (v : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then v else rho y.
Definition extend_ty (eta : atom -> ty) (X : atom) (U : ty) : atom -> ty :=
  fun Y => if Nat.eqb X Y then U else eta Y.

Definition type_environment (D : ty_context) (eta : atom -> ty) : Prop :=
  forall X, locally_closed_ty (eta X).

Definition context_interpretation (n : nat) (eta : atom -> ty)
    (rho : atom -> tm) (G : rcontext) : Prop :=
  (forall x, value (rho x)) /\
  forall x R, lookup_rcontext x G = Some R ->
    LRv n (inst_rty eta rho R) (rho x).

Fixpoint fv_q_tm (q : qualifier) : list atom :=
  match q with
  | Pred_True | Pred_False => []
  | Pred_Eq a b | Pred_Lt a b | Pred_Le a b => fv_tm a ++ fv_tm b
  | Pred_And p q | Pred_Or p q => fv_q_tm p ++ fv_q_tm q
  | Pred_Not p => fv_q_tm p
  end.
Fixpoint fv_rty_tm (R : rty) : list atom :=
  match R with
  | R_Refine _ q => fv_q_tm q
  | R_Func A B | R_Exists A B => fv_rty_tm A ++ fv_rty_tm B
  | R_Poly A => fv_rty_tm A
  end.

Lemma notin_app_l : forall (x : atom) A B, ~ In x (A ++ B) -> ~ In x A.
Proof. intros x A B H Hin; apply H; apply in_or_app; auto. Qed.
Lemma notin_app_r : forall (x : atom) A B, ~ In x (A ++ B) -> ~ In x B.
Proof. intros x A B H Hin; apply H; apply in_or_app; auto. Qed.

Lemma in_le_max_atom : forall L x, In x L -> x <= max_atom L.
Proof.
  induction L as [|a L IH]; intros x H; simpl in *; [contradiction|].
  destruct H as [->|H]; lia || specialize (IH _ H); lia.
Qed.

Lemma fresh_notin : forall L, ~ In (fresh L) L.
Proof.
  intros L H. unfold fresh in H. pose proof (in_le_max_atom _ _ H). lia.
Qed.

Lemma open_rec_lc_at : forall K j s,
  lc_tm_at K j s -> forall k v, j <= k -> open_tm_rec k v s = s.
Proof.
  intros K j s H. induction H; intros k0 v Hle; simpl; try reflexivity.
  - destruct (Nat.eqb k0 i) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
  - f_equal. apply IHlc_tm_at. lia.
  - f_equal; [apply IHlc_tm_at1|apply IHlc_tm_at2]; assumption.
  - f_equal. apply IHlc_tm_at. assumption.
  - f_equal. apply IHlc_tm_at. assumption.
  - f_equal; [apply IHlc_tm_at1|apply IHlc_tm_at2]; assumption.
  - f_equal; [apply IHlc_tm_at1|apply IHlc_tm_at2]; assumption.
Qed.

Lemma open_rec_lc : forall s k v,
  locally_closed_tm s -> open_tm_rec k v s = s.
Proof. intros. eapply open_rec_lc_at; eauto. lia. Qed.

Lemma inst_open_tm_rec : forall t k eta rho x v,
  ~ In x (fv_tm t) ->
  (forall y, locally_closed_tm (rho y)) ->
  inst_tm eta (extend_tm rho x v) (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k v (inst_tm eta rho t).
Proof.
  induction t; intros k eta rho x v H HC; simpl in *; try reflexivity.
  - destruct (Nat.eqb k n); cbn; unfold extend_tm;
      destruct (Nat.eqb x x) eqn:E; try reflexivity;
      rewrite Nat.eqb_refl in E; discriminate.
  - unfold extend_tm. destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E; subst. exfalso; apply H; auto.
    + symmetry. apply open_rec_lc. apply HC.
  - f_equal. apply IHt; assumption.
  - f_equal; [apply IHt1; [eapply notin_app_l|] | apply IHt2; [eapply notin_app_r|]]; eauto.
  - f_equal. apply IHt; assumption.
  - f_equal. apply IHt; assumption.
  - f_equal; [apply IHt1; [eapply notin_app_l|] | apply IHt2; [eapply notin_app_r|]]; eauto.
  - f_equal; [apply IHt1; [eapply notin_app_l|] | apply IHt2; [eapply notin_app_r|]]; eauto.
Qed.

Lemma inst_open_tm : forall t eta rho x v,
  ~ In x (fv_tm t) ->
  (forall y, locally_closed_tm (rho y)) ->
  inst_tm eta (extend_tm rho x v) (open_tm t (tm_fvar x)) =
  open_tm (inst_tm eta rho t) v.
Proof. intros; apply inst_open_tm_rec; assumption. Qed.

Lemma inst_open_q_rec : forall q k eta rho x v,
  ~ In x (fv_q_tm q) ->
  (forall y, locally_closed_tm (rho y)) ->
  inst_q eta (extend_tm rho x v) (open_qualifier_tm_rec k (tm_fvar x) q) =
  open_qualifier_tm_rec k v (inst_q eta rho q).
Proof.
  induction q; intros k eta rho x v H HC; simpl in *; try reflexivity.
  - f_equal; apply inst_open_tm_rec; [eapply notin_app_l|exact HC|eapply notin_app_r|exact HC]; eauto.
  - f_equal; apply inst_open_tm_rec; [eapply notin_app_l|exact HC|eapply notin_app_r|exact HC]; eauto.
  - f_equal; apply inst_open_tm_rec; [eapply notin_app_l|exact HC|eapply notin_app_r|exact HC]; eauto.
  - f_equal; [apply IHq1; [eapply notin_app_l|] | apply IHq2; [eapply notin_app_r|]]; eauto.
  - f_equal; [apply IHq1; [eapply notin_app_l|] | apply IHq2; [eapply notin_app_r|]]; eauto.
  - f_equal. apply IHq; assumption.
Qed.

Lemma inst_open_rty_tm_rec : forall R k eta rho x v,
  ~ In x (fv_rty_tm R) ->
  (forall y, locally_closed_tm (rho y)) ->
  inst_rty eta (extend_tm rho x v) (open_rty_tm_rec k (tm_fvar x) R) =
  open_rty_tm_rec k v (inst_rty eta rho R).
Proof.
  induction R; intros k eta rho x v H HC; simpl in *.
  - f_equal. apply inst_open_q_rec; assumption.
  - f_equal; [apply IHR1; [eapply notin_app_l|] | apply IHR2; [eapply notin_app_r|]]; eauto.
  - f_equal; [apply IHR1; [eapply notin_app_l|] | apply IHR2; [eapply notin_app_r|]]; eauto.
  - f_equal. apply IHR; assumption.
Qed.

Lemma inst_open_rty_tm : forall R eta rho x v,
  ~ In x (fv_rty_tm R) ->
  (forall y, locally_closed_tm (rho y)) ->
  inst_rty eta (extend_tm rho x v) (open_rty_tm R (tm_fvar x)) =
  open_rty_tm (inst_rty eta rho R) v.
Proof. intros; apply inst_open_rty_tm_rec; assumption. Qed.

Lemma inst_tm_extend_irrel : forall t eta rho x v,
  ~ In x (fv_tm t) -> inst_tm eta (extend_tm rho x v) t = inst_tm eta rho t.
Proof.
  induction t; intros eta rho x v H; simpl in *; try reflexivity.
  - unfold extend_tm. destruct (Nat.eqb x a) eqn:E; auto.
    apply Nat.eqb_eq in E; subst; exfalso; apply H; auto.
  - f_equal. apply IHt; exact H.
  - f_equal; [apply IHt1; eapply notin_app_l|apply IHt2; eapply notin_app_r]; eauto.
  - f_equal. apply IHt; exact H.
  - f_equal. apply IHt; exact H.
  - f_equal; [apply IHt1; eapply notin_app_l|apply IHt2; eapply notin_app_r]; eauto.
  - f_equal; [apply IHt1; eapply notin_app_l|apply IHt2; eapply notin_app_r]; eauto.
Qed.

Lemma inst_q_extend_irrel : forall q eta rho x v,
  ~ In x (fv_q_tm q) -> inst_q eta (extend_tm rho x v) q = inst_q eta rho q.
Proof.
  induction q; intros eta rho x v H; simpl in *; try reflexivity.
  - f_equal; apply inst_tm_extend_irrel; [eapply notin_app_l|eapply notin_app_r]; eauto.
  - f_equal; apply inst_tm_extend_irrel; [eapply notin_app_l|eapply notin_app_r]; eauto.
  - f_equal; apply inst_tm_extend_irrel; [eapply notin_app_l|eapply notin_app_r]; eauto.
  - f_equal; [apply IHq1; eapply notin_app_l|apply IHq2; eapply notin_app_r]; eauto.
  - f_equal; [apply IHq1; eapply notin_app_l|apply IHq2; eapply notin_app_r]; eauto.
  - f_equal. apply IHq; exact H.
Qed.

Lemma inst_rty_extend_irrel : forall R eta rho x v,
  ~ In x (fv_rty_tm R) ->
  inst_rty eta (extend_tm rho x v) R = inst_rty eta rho R.
Proof.
  induction R; intros eta rho x v H; simpl in *.
  - f_equal. apply inst_q_extend_irrel; exact H.
  - f_equal; [apply IHR1; eapply notin_app_l|apply IHR2; eapply notin_app_r]; eauto.
  - f_equal; [apply IHR1; eapply notin_app_l|apply IHR2; eapply notin_app_r]; eauto.
  - f_equal. apply IHR; exact H.
Qed.

Fixpoint support_rcontext (G : rcontext) : list atom :=
  match G with
  | [] => []
  | (x,R)::G' => x :: (fv_rty_tm R ++ support_rcontext G')
  end.

Lemma lookup_support : forall G y R x,
  lookup_rcontext y G = Some R -> ~ In x (support_rcontext G) ->
  x <> y /\ ~ In x (fv_rty_tm R).
Proof.
  induction G as [|[z S] G IH]; intros y R x Hlook Hfresh; simpl in *; try discriminate.
  destruct (Nat.eqb y z) eqn:E.
  - inversion Hlook; subst. apply Nat.eqb_eq in E; subst. split.
    + intro; subst; apply Hfresh; auto.
    + intro Hin; apply Hfresh; right; apply in_or_app; auto.
  - eapply IH with (x:=x) in Hlook; [|intro Hin; apply Hfresh; right; apply in_or_app; auto].
    exact Hlook.
Qed.

Lemma context_extend_tm : forall n eta rho G x A v,
  context_interpretation n eta rho G -> LRv n (inst_rty eta rho A) v ->
  ~ In x (fv_rty_tm A ++ support_rcontext G) ->
  context_interpretation n eta (extend_tm rho x v) ((x,A)::G).
Proof.
  intros n eta rho G x A v [Hall Hlook] Hv Hfresh. split.
  - intros y. unfold extend_tm. destruct (Nat.eqb x y) eqn:E.
    + eapply LRv_value0; eauto.
    + apply Hall.
  - intros y R. simpl. destruct (Nat.eqb y x) eqn:E.
    + intro Ei. inversion Ei; subst. apply Nat.eqb_eq in E; subst.
      rewrite inst_rty_extend_irrel; [|eapply notin_app_l; eauto].
      replace (extend_tm rho x v x) with v.
      * exact Hv.
      * unfold extend_tm. now rewrite Nat.eqb_refl.
    + intro Ey. pose proof (lookup_support G y R x Ey (notin_app_r _ _ _ Hfresh)) as [Hxy HxR].
      rewrite inst_rty_extend_irrel by exact HxR.
      replace (extend_tm rho x v y) with (rho y).
      * eapply Hlook; eauto.
      * unfold extend_tm. destruct (Nat.eqb x y) eqn:Exy; auto.
        apply Nat.eqb_eq in Exy; contradiction.
Qed.

Fixpoint ftv_q (q : qualifier) : list atom :=
  match q with
  | Pred_True | Pred_False => []
  | Pred_Eq a b | Pred_Lt a b | Pred_Le a b => ftv_tm a ++ ftv_tm b
  | Pred_And p q | Pred_Or p q => ftv_q p ++ ftv_q q
  | Pred_Not p => ftv_q p
  end.
Fixpoint ftv_rty (R : rty) : list atom :=
  match R with
  | R_Refine T q => fv_ty T ++ ftv_q q
  | R_Func A B | R_Exists A B => ftv_rty A ++ ftv_rty B
  | R_Poly A => ftv_rty A
  end.

Lemma open_ty_rec_lc_at : forall K T, lc_ty_at K T ->
  forall k U, K <= k -> open_ty_rec k U T = T.
Proof.
  intros K T H. induction H; intros j U Hj; simpl; try reflexivity.
  - destruct (Nat.eqb j i) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
  - f_equal; [eapply IHlc_ty_at1|eapply IHlc_ty_at2]; eauto.
  - f_equal. eapply IHlc_ty_at; lia.
Qed.

Lemma open_ty_rec_lc : forall T k U,
  locally_closed_ty T -> open_ty_rec k U T = T.
Proof. intros; eapply open_ty_rec_lc_at; eauto; lia. Qed.

Lemma inst_open_ty_rec : forall T k eta X U,
  ~ In X (fv_ty T) -> (forall Y, locally_closed_ty (eta Y)) ->
  inst_ty (extend_ty eta X U) (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k U (inst_ty eta T).
Proof.
  induction T; intros k eta X U Hfresh Heta; simpl in *; try reflexivity.
  - destruct (Nat.eqb k n); simpl; [unfold extend_ty; now rewrite Nat.eqb_refl|reflexivity].
  - unfold extend_ty. destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E; subst; exfalso; apply Hfresh; auto.
    + symmetry; apply open_ty_rec_lc. apply Heta.
  - f_equal; [apply IHT1; [eapply notin_app_l|] | apply IHT2; [eapply notin_app_r|]]; eauto.
  - f_equal. apply IHT; assumption.
Qed.

Lemma open_tm_ty_rec_lc_at : forall K k t, lc_tm_at K k t ->
  forall j U, K <= j -> open_tm_ty_rec j U t = t.
Proof.
  intros K k t H. induction H; intros j U Hj; simpl; try reflexivity.
  - f_equal.
    + eapply open_ty_rec_lc_at; eauto.
    + eapply IHlc_tm_at; eauto.
  - f_equal; [eapply IHlc_tm_at1|eapply IHlc_tm_at2]; eauto.
  - f_equal. eapply IHlc_tm_at. lia.
  - f_equal.
    + eapply IHlc_tm_at; eauto.
    + eapply open_ty_rec_lc_at; eauto.
  - f_equal; [eapply IHlc_tm_at1|eapply IHlc_tm_at2]; eauto.
  - f_equal; [eapply IHlc_tm_at1|eapply IHlc_tm_at2]; eauto.
Qed.

Lemma open_tm_ty_rec_lc : forall t j U,
  locally_closed_tm t -> open_tm_ty_rec j U t = t.
Proof. intros; eapply open_tm_ty_rec_lc_at; eauto; lia. Qed.

Lemma inst_open_tm_ty_rec : forall t k eta rho X U,
  ~ In X (ftv_tm t) -> (forall Y, locally_closed_ty (eta Y)) ->
  (forall y, locally_closed_tm (rho y)) ->
  inst_tm (extend_ty eta X U) rho (open_tm_ty_rec k (Ty_FVar X) t) =
  open_tm_ty_rec k U (inst_tm eta rho t).
Proof.
  induction t; intros k eta rho X U Hfresh Heta Hrho; simpl in *; try reflexivity.
  - symmetry. apply open_tm_ty_rec_lc. apply Hrho.
  - f_equal.
    + apply inst_open_ty_rec; [eapply notin_app_l|exact Heta]; eauto.
    + apply IHt; [eapply notin_app_r|exact Heta|exact Hrho]; eauto.
  - f_equal; [apply IHt1; [eapply notin_app_l|exact Heta|exact Hrho] |
      apply IHt2; [eapply notin_app_r|exact Heta|exact Hrho]]; eauto.
  - f_equal. apply IHt; assumption.
  - f_equal.
    + apply IHt; [eapply notin_app_l|exact Heta|exact Hrho]; eauto.
    + apply inst_open_ty_rec; [eapply notin_app_r|exact Heta]; eauto.
  - f_equal; [apply IHt1; [eapply notin_app_l|exact Heta|exact Hrho] |
      apply IHt2; [eapply notin_app_r|exact Heta|exact Hrho]]; eauto.
  - f_equal; [apply IHt1; [eapply notin_app_l|exact Heta|exact Hrho] |
      apply IHt2; [eapply notin_app_r|exact Heta|exact Hrho]]; eauto.
Qed.

Lemma inst_open_q_ty_rec : forall q k eta rho X U,
  ~ In X (ftv_q q) -> (forall Y, locally_closed_ty (eta Y)) ->
  (forall y, locally_closed_tm (rho y)) ->
  inst_q (extend_ty eta X U) rho (open_qualifier_ty_rec k (Ty_FVar X) q) =
  open_qualifier_ty_rec k U (inst_q eta rho q).
Proof.
  induction q; intros k eta rho X U Hf He Hr; simpl in *; try reflexivity.
  - f_equal; apply inst_open_tm_ty_rec;
      [eapply notin_app_l|exact He|exact Hr|eapply notin_app_r|exact He|exact Hr]; eauto.
  - f_equal; apply inst_open_tm_ty_rec;
      [eapply notin_app_l|exact He|exact Hr|eapply notin_app_r|exact He|exact Hr]; eauto.
  - f_equal; apply inst_open_tm_ty_rec;
      [eapply notin_app_l|exact He|exact Hr|eapply notin_app_r|exact He|exact Hr]; eauto.
  - f_equal; [apply IHq1; [eapply notin_app_l|exact He|exact Hr] |
      apply IHq2; [eapply notin_app_r|exact He|exact Hr]]; eauto.
  - f_equal; [apply IHq1; [eapply notin_app_l|exact He|exact Hr] |
      apply IHq2; [eapply notin_app_r|exact He|exact Hr]]; eauto.
  - f_equal. apply IHq; assumption.
Qed.

Lemma inst_open_rty_ty_rec : forall R k eta rho X U,
  ~ In X (ftv_rty R) -> (forall Y, locally_closed_ty (eta Y)) ->
  (forall y, locally_closed_tm (rho y)) ->
  inst_rty (extend_ty eta X U) rho (open_rty_ty_rec k (Ty_FVar X) R) =
  open_rty_ty_rec k U (inst_rty eta rho R).
Proof.
  induction R; intros k eta rho X U Hf He Hr; simpl in *.
  - f_equal.
    + apply inst_open_ty_rec; [eapply notin_app_l|exact He]; eauto.
    + apply inst_open_q_ty_rec; [eapply notin_app_r|exact He|exact Hr]; eauto.
  - f_equal; [apply IHR1; [eapply notin_app_l|exact He|exact Hr] |
      apply IHR2; [eapply notin_app_r|exact He|exact Hr]]; eauto.
  - f_equal; [apply IHR1; [eapply notin_app_l|exact He|exact Hr] |
      apply IHR2; [eapply notin_app_r|exact He|exact Hr]]; eauto.
  - f_equal. apply IHR; assumption.
Qed.

Lemma inst_open_rty_ty : forall R eta rho X U,
  ~ In X (ftv_rty R) -> (forall Y, locally_closed_ty (eta Y)) ->
  (forall y, locally_closed_tm (rho y)) ->
  inst_rty (extend_ty eta X U) rho (open_rty_ty R (Ty_FVar X)) =
  open_rty_ty (inst_rty eta rho R) U.
Proof. intros; apply inst_open_rty_ty_rec; assumption. Qed.

Lemma inst_ty_open_general : forall T k eta U,
  (forall X, locally_closed_ty (eta X)) ->
  inst_ty eta (open_ty_rec k U T) = open_ty_rec k (inst_ty eta U) (inst_ty eta T).
Proof.
  induction T; intros k eta U He; simpl; try reflexivity.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry; apply open_ty_rec_lc; apply He.
  - f_equal; auto.
  - f_equal; auto.
Qed.

Lemma inst_tm_ty_open_general : forall t k eta rho U,
  (forall X, locally_closed_ty (eta X)) ->
  (forall x, locally_closed_tm (rho x)) ->
  inst_tm eta rho (open_tm_ty_rec k U t) =
  open_tm_ty_rec k (inst_ty eta U) (inst_tm eta rho t).
Proof.
  induction t; intros k eta rho U He Hr; simpl; try reflexivity.
  - symmetry; apply open_tm_ty_rec_lc; apply Hr.
  - f_equal; [apply inst_ty_open_general|apply IHt]; auto.
  - f_equal; [apply IHt1|apply IHt2]; auto.
  - f_equal; auto.
  - f_equal; [apply IHt|apply inst_ty_open_general]; auto.
  - f_equal; [apply IHt1|apply IHt2]; auto.
  - f_equal; [apply IHt1|apply IHt2]; auto.
Qed.

Lemma inst_q_ty_open_general : forall q k eta rho U,
  (forall X, locally_closed_ty (eta X)) ->
  (forall x, locally_closed_tm (rho x)) ->
  inst_q eta rho (open_qualifier_ty_rec k U q) =
  open_qualifier_ty_rec k (inst_ty eta U) (inst_q eta rho q).
Proof.
  induction q; intros k eta rho U He Hr; simpl; try reflexivity.
  - f_equal; apply inst_tm_ty_open_general; auto.
  - f_equal; apply inst_tm_ty_open_general; auto.
  - f_equal; apply inst_tm_ty_open_general; auto.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
Qed.

Lemma inst_rty_ty_open_general : forall R k eta rho U,
  (forall X, locally_closed_ty (eta X)) ->
  (forall x, locally_closed_tm (rho x)) ->
  inst_rty eta rho (open_rty_ty_rec k U R) =
  open_rty_ty_rec k (inst_ty eta U) (inst_rty eta rho R).
Proof.
  induction R; intros k eta rho U He Hr; simpl.
  - f_equal; [apply inst_ty_open_general|apply inst_q_ty_open_general]; auto.
  - f_equal; [apply IHR1|apply IHR2]; auto.
  - f_equal; [apply IHR1|apply IHR2]; auto.
  - f_equal; auto.
Qed.

Lemma erase_open_rty_tm_rec : forall R k u,
  erase (open_rty_tm_rec k u R) = erase R.
Proof.
  induction R; intros; simpl.
  - reflexivity.
  - rewrite IHR1, IHR2; reflexivity.
  - rewrite IHR2; reflexivity.
  - rewrite IHR; reflexivity.
Qed.

Lemma erase_open_rty_ty_rec : forall R k U,
  erase (open_rty_ty_rec k U R) = open_ty_rec k U (erase R).
Proof.
  induction R; intros; simpl.
  - reflexivity.
  - rewrite IHR1, IHR2; reflexivity.
  - rewrite IHR2; reflexivity.
  - rewrite IHR; reflexivity.
Qed.

Lemma wf_rty_erase_wf : forall D G R, wf_rty D G R -> wf_ty D (erase R).
Proof.
  intros D G R H. induction H; simpl; auto.
  - constructor; auto. specialize (H1 (fresh L) (fresh_notin L)).
    unfold open_rty_tm in H1. rewrite erase_open_rty_tm_rec in H1. exact H1.
  - specialize (H1 (fresh L) (fresh_notin L)).
    unfold open_rty_tm in H1. rewrite erase_open_rty_tm_rec in H1. exact H1.
  - apply WF_All with (L:=L). intros X HX. specialize (H0 X HX).
    unfold open_rty_ty, open_ty in H0. rewrite erase_open_rty_ty_rec in H0. exact H0.
Qed.

Lemma lc_ty_close_open : forall K T U,
  lc_ty_at K (open_ty_rec K U T) -> lc_ty_at (S K) T.
Proof.
  intros K T. revert K. induction T; intros K U H; simpl in H.
  - destruct (Nat.eqb K n) eqn:E.
    + apply Nat.eqb_eq in E; subst; constructor; lia.
    + inversion H; subst; constructor; apply Nat.eqb_neq in E; lia.
  - constructor.
  - inversion H; subst; constructor; [eapply IHT1|eapply IHT2]; eauto.
  - inversion H; subst; constructor. eapply IHT; eauto.
  - constructor.
Qed.

Lemma inst_open_ty_direct : forall T k eta X,
  (forall Y, locally_closed_ty (eta Y)) ->
  inst_ty eta (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k (eta X) (inst_ty eta T).
Proof.
  induction T; intros k eta X He; simpl; try reflexivity.
  - destruct (Nat.eqb k n); simpl; auto.
  - symmetry. apply open_ty_rec_lc. apply He.
  - f_equal; auto.
  - f_equal. auto.
Qed.

Lemma wf_ty_inst_lc : forall D T, wf_ty D T -> forall eta,
  (forall X, locally_closed_ty (eta X)) -> locally_closed_ty (inst_ty eta T).
Proof.
  intros D T H. induction H; intros eta He; simpl.
  - apply He.
  - constructor; [apply IHwf_ty1|apply IHwf_ty2]; exact He.
  - constructor. set (X := fresh L).
    specialize (H0 X (fresh_notin L) eta He). unfold open_ty in H0.
    (* Instantiation commutes with replacing the outer bound variable. *)
    assert (E : inst_ty eta (open_ty_rec 0 (Ty_FVar X) T) =
                open_ty_rec 0 (eta X) (inst_ty eta T)) by
      (apply inst_open_ty_direct; exact He).
    rewrite E in H0. eapply lc_ty_close_open; exact H0.
  - constructor.
Qed.

Lemma lc_ty_weaken0 : forall K T, lc_ty_at K T ->
  forall J, K <= J -> lc_ty_at J T.
Proof.
  intros K T H. induction H; intros J HJ; constructor; try lia; eauto.
  eapply IHlc_ty_at; lia.
Qed.

Lemma lc_tm_weaken_var0 : forall K k t, lc_tm_at K k t ->
  forall j, k <= j -> lc_tm_at K j t.
Proof.
  intros K k t H. induction H; intros j Hj; constructor; try lia; eauto.
  eapply IHlc_tm_at; lia.
Qed.

Lemma lc_tm_weaken_ty0 : forall K k t, lc_tm_at K k t ->
  forall J, K <= J -> lc_tm_at J k t.
Proof.
  intros K k t H. induction H; intros J HJ; constructor; eauto using lc_ty_weaken0.
  eapply IHlc_tm_at; lia.
Qed.

Lemma inst_ty_lc_at : forall K T, lc_ty_at K T -> forall eta,
  (forall X, locally_closed_ty (eta X)) -> lc_ty_at K (inst_ty eta T).
Proof.
  intros K T H. induction H; intros eta He; simpl.
  - constructor; assumption.
  - eapply lc_ty_weaken0; [apply He|lia].
  - constructor; auto.
  - constructor; auto.
  - constructor.
Qed.

Lemma inst_tm_lc_at : forall K k t, lc_tm_at K k t -> forall eta rho,
  (forall X, locally_closed_ty (eta X)) ->
  (forall x, locally_closed_tm (rho x)) -> lc_tm_at K k (inst_tm eta rho t).
Proof.
  intros K k t H. induction H; intros eta rho He Hr; simpl.
  - constructor; assumption.
  - eapply lc_tm_weaken_var0; [eapply lc_tm_weaken_ty0; [apply Hr|lia]|lia].
  - constructor; [eapply inst_ty_lc_at|eapply IHlc_tm_at]; eauto.
  - constructor; eauto.
  - constructor. eauto.
  - constructor; [eauto|eapply inst_ty_lc_at]; eauto.
  - constructor.
  - apply lc_tm_div; [apply IHlc_tm_at1|apply IHlc_tm_at2]; assumption.
  - apply lc_tm_arith; [apply IHlc_tm_at1|apply IHlc_tm_at2]; assumption.
Qed.

Lemma inst_tm_lc : forall t eta rho,
  locally_closed_tm t -> (forall X, locally_closed_ty (eta X)) ->
  (forall x, locally_closed_tm (rho x)) -> locally_closed_tm (inst_tm eta rho t).
Proof. intros; eapply inst_tm_lc_at; eauto. Qed.

Lemma lc_tm_close_open : forall K k t u,
  lc_tm_at K k (open_tm_rec k u t) -> lc_tm_at K (S k) t.
Proof.
  intros K k t. revert K k. induction t; intros K k u H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst; constructor; lia.
    + inversion H; subst; constructor; apply Nat.eqb_neq in E; lia.
  - constructor.
  - inversion H; subst; constructor; auto. eapply IHt; eauto.
  - inversion H; subst; constructor; [eapply IHt1|eapply IHt2]; eauto.
  - inversion H; subst; constructor. eapply IHt; eauto.
  - inversion H; subst; constructor; [eapply IHt|exact H5]; eauto.
  - constructor.
  - inversion H; subst; constructor; [eapply IHt1|eapply IHt2]; eauto.
  - inversion H; subst; constructor; [eapply IHt1|eapply IHt2]; eauto.
Qed.

Lemma lc_tm_ty_close_open : forall K k t U,
  lc_tm_at K k (open_tm_ty_rec K U t) -> lc_tm_at (S K) k t.
Proof.
  intros K k t. revert K k. induction t; intros K k U H; simpl in H.
  - inversion H; constructor; assumption.
  - inversion H; constructor.
  - inversion H; subst; constructor.
    + eapply lc_ty_close_open; eauto.
    + eapply IHt; eauto.
  - inversion H; subst; constructor; [eapply IHt1|eapply IHt2]; eauto.
  - inversion H; subst; constructor. eapply IHt; eauto.
  - inversion H; subst; constructor.
    + eapply IHt; eauto.
    + eapply lc_ty_close_open; eauto.
  - constructor.
  - inversion H; subst; constructor; [eapply IHt1|eapply IHt2]; eauto.
  - inversion H; subst; constructor; [eapply IHt1|eapply IHt2]; eauto.
Qed.

Lemma inst_ty_extend_irrel : forall T eta X U,
  ~ In X (fv_ty T) -> inst_ty (extend_ty eta X U) T = inst_ty eta T.
Proof.
  induction T; intros eta X U H; simpl in *; try reflexivity.
  - unfold extend_ty. destruct (Nat.eqb X a) eqn:E; auto.
    apply Nat.eqb_eq in E; subst; exfalso; apply H; auto.
  - f_equal; [apply IHT1; eapply notin_app_l|apply IHT2; eapply notin_app_r]; eauto.
  - f_equal. apply IHT; exact H.
Qed.

Lemma inst_tm_ty_extend_irrel : forall t eta rho X U,
  ~ In X (ftv_tm t) -> inst_tm (extend_ty eta X U) rho t = inst_tm eta rho t.
Proof.
  induction t; intros eta rho X U H; simpl in *; try reflexivity.
  - f_equal.
    + apply inst_ty_extend_irrel; eapply notin_app_l; eauto.
    + apply IHt; eapply notin_app_r; eauto.
  - f_equal; [apply IHt1; eapply notin_app_l|apply IHt2; eapply notin_app_r]; eauto.
  - f_equal. apply IHt; exact H.
  - f_equal; [apply IHt; eapply notin_app_l|apply inst_ty_extend_irrel; eapply notin_app_r]; eauto.
  - f_equal; [apply IHt1; eapply notin_app_l|apply IHt2; eapply notin_app_r]; eauto.
  - f_equal; [apply IHt1; eapply notin_app_l|apply IHt2; eapply notin_app_r]; eauto.
Qed.

Lemma inst_q_ty_extend_irrel : forall q eta rho X U,
  ~ In X (ftv_q q) -> inst_q (extend_ty eta X U) rho q = inst_q eta rho q.
Proof.
  induction q; intros eta rho X U H; simpl in *; try reflexivity.
  - f_equal; apply inst_tm_ty_extend_irrel; [eapply notin_app_l|eapply notin_app_r]; eauto.
  - f_equal; apply inst_tm_ty_extend_irrel; [eapply notin_app_l|eapply notin_app_r]; eauto.
  - f_equal; apply inst_tm_ty_extend_irrel; [eapply notin_app_l|eapply notin_app_r]; eauto.
  - f_equal; [apply IHq1; eapply notin_app_l|apply IHq2; eapply notin_app_r]; eauto.
  - f_equal; [apply IHq1; eapply notin_app_l|apply IHq2; eapply notin_app_r]; eauto.
  - f_equal. apply IHq; exact H.
Qed.

Lemma inst_rty_ty_extend_irrel : forall R eta rho X U,
  ~ In X (ftv_rty R) -> inst_rty (extend_ty eta X U) rho R = inst_rty eta rho R.
Proof.
  induction R; intros eta rho X U H; simpl in *.
  - f_equal.
    + apply inst_ty_extend_irrel; eapply notin_app_l; eauto.
    + apply inst_q_ty_extend_irrel; eapply notin_app_r; eauto.
  - f_equal; [apply IHR1; eapply notin_app_l|apply IHR2; eapply notin_app_r]; eauto.
  - f_equal; [apply IHR1; eapply notin_app_l|apply IHR2; eapply notin_app_r]; eauto.
  - f_equal. apply IHR; exact H.
Qed.

Fixpoint support_ty_rcontext (G : rcontext) : list atom :=
  match G with [] => [] | (_,R)::G' => ftv_rty R ++ support_ty_rcontext G' end.

Lemma lookup_ty_support : forall G y R X,
  lookup_rcontext y G = Some R -> ~ In X (support_ty_rcontext G) ->
  ~ In X (ftv_rty R).
Proof.
  induction G as [|[z S] G IH]; intros y R X Hlook Hfresh; simpl in *; try discriminate.
  destruct (Nat.eqb y z) eqn:E.
  - inversion Hlook; subst. eapply notin_app_l; eauto.
  - eapply IH; eauto. eapply notin_app_r; eauto.
Qed.

Lemma type_environment_extend : forall D eta X U,
  type_environment D eta -> locally_closed_ty U ->
  type_environment (X::D) (extend_ty eta X U).
Proof.
  intros D eta X U He HU Y. unfold extend_ty.
  destruct (Nat.eqb X Y); auto.
Qed.

Lemma context_extend_ty : forall n eta rho G X U,
  context_interpretation n eta rho G ->
  ~ In X (support_ty_rcontext G) ->
  context_interpretation n (extend_ty eta X U) rho G.
Proof.
  intros n eta rho G X U [Hall Hlook] Hfresh. split; [exact Hall|].
  intros y R Hy. rewrite inst_rty_ty_extend_irrel.
  - eapply Hlook; eauto.
  - eapply lookup_ty_support; eauto.
Qed.

Scheme rtyping_mut := Induction for has_rtype Sort Prop
with subtyping_mut := Induction for subtype Sort Prop.
Combined Scheme rtyping_subtyping_mutind from rtyping_mut, subtyping_mut.

Definition FundamentalP (D : ty_context) (G : rcontext) (t : tm) (R : rty) : Prop :=
  forall n eta rho, type_environment D eta ->
    context_interpretation n eta rho G ->
    LRe n (inst_rty eta rho R) (inst_tm eta rho t).

Definition SubtypingP (D : ty_context) (G : rcontext) (R S : rty) : Prop :=
  forall n eta rho, type_environment D eta ->
    context_interpretation n eta rho G ->
    forall v, LRv n (inst_rty eta rho R) v ->
      LRv n (inst_rty eta rho S) v.

Lemma value_no_step : forall v u, value v -> ~ (v --> u).
Proof. intros v u Hv Hs; inversion Hv; subst; inversion Hs. Qed.

Lemma step_deterministic : forall t u, t --> u -> forall v, t --> v -> u = v.
Proof.
  intros t u H. induction H; intros w Hw; inversion Hw; subst; try reflexivity;
    try (f_equal; eapply IHstep; eauto).
  all: try (f_equal; eapply IHstep; eauto).
  all: try match goal with
       | Hs : ?x --> _, Hv : value ?x |- _ =>
           exfalso; exact (value_no_step x _ Hv Hs)
       end.
  all: try match goal with
       | Hv : value ?x, Hs : ?x --> _ |- _ =>
           exfalso; exact (value_no_step x _ Hv Hs)
       end.
  all: try match goal with
       | Hs : tm_abs _ _ --> _ |- _ => inversion Hs
       | Hs : tm_tabs _ --> _ |- _ => inversion Hs
       | Hs : tm_int _ --> _ |- _ => inversion Hs
       end.
Qed.

Lemma multi_value : forall v u, value v -> multi v u -> u = v.
Proof.
  intros v u Hv Hm. inversion Hm; subst; auto.
  exfalso; eapply value_no_step; eauto.
Qed.

Lemma safe_value : forall n v, value v -> safe_for n v.
Proof. induction n; simpl; auto. Qed.

Lemma LRv_is_value : forall n R v, LRv n R v -> value v.
Proof. induction n; simpl; intuition. Qed.

Lemma value_is_lc : forall v, value v -> locally_closed_tm v.
Proof. intros v H; inversion H; subst; auto. constructor. Qed.

Lemma LRe_value : forall n R v, LRv n R v -> LRe n R v.
Proof.
  intros n R v H. split; [apply value_is_lc; eapply LRv_is_value; eauto|]. split.
  - apply safe_value. eapply LRv_is_value; eauto.
  - intros u Hm Hu. assert (Hv : value v) by (eapply LRv_is_value; eauto).
    pose proof (multi_value v u Hv Hm) as E. subst u. exact H.
Qed.

Lemma LRv_int_exact : forall n z,
  LRv n (R_Refine Ty_Int (Pred_Eq (tm_bvar 0) (tm_int z))) (tm_int z).
Proof.
  induction n as [|n IH]; simpl; [constructor|]. split; [exact (IH z)|].
  rewrite LRhead_equation_1. split; [constructor|]. split.
  - intros _. exists z; reflexivity.
  - unfold qualifier_holds, predicate_holds; simpl.
    exists (tm_int z). repeat split; constructor.
Qed.

Lemma LRe_int_exact : forall n z,
  LRe n (R_Refine Ty_Int (Pred_Eq (tm_bvar 0) (tm_int z))) (tm_int z).
Proof. intros; apply LRe_value; apply LRv_int_exact. Qed.

Lemma LRv_down : forall n R v, LRv (S n) R v -> LRv n R v.
Proof. intros n R v H. exact (proj1 H). Qed.

Lemma LRv_down_le : forall n m R v, m <= n -> LRv n R v -> LRv m R v.
Proof.
  induction n as [|n IH]; intros m R v Hle H.
  - assert (m = 0) by lia. subst; exact H.
  - destruct m as [|m].
    + simpl. eapply LRv_is_value; eauto.
    + destruct (Nat.eq_dec m n) as [E|E].
      * subst; exact H.
      * eapply IH with (m:=S m) (R:=R) (v:=v); [lia|].
        apply LRv_down with (n:=n); exact H.
Qed.

Lemma context_lookup_LRe : forall n eta rho G x R,
  context_interpretation n eta rho G -> lookup_rcontext x G = Some R ->
  LRe n (inst_rty eta rho R) (rho x).
Proof.
  intros n eta rho G x R [Hall Hlook] E. apply LRe_value.
  eapply Hlook; eauto.
Qed.

Lemma context_interpretation_down : forall n k eta rho G,
  k <= n -> context_interpretation n eta rho G ->
  context_interpretation k eta rho G.
Proof.
  intros n k eta rho G Hkn [Hall Hlook]. split; [exact Hall|].
  intros x R Hx. eapply LRv_down_le; [exact Hkn|eapply Hlook; eauto].
Qed.

Lemma lc_tm_weaken_var : forall K k t, lc_tm_at K k t ->
  forall j, k <= j -> lc_tm_at K j t.
Proof.
  intros K k t H. induction H; intros j Hj; constructor; try lia; eauto.
  eapply IHlc_tm_at; lia.
Qed.

Lemma lc_ty_weaken : forall K T, lc_ty_at K T ->
  forall J, K <= J -> lc_ty_at J T.
Proof.
  intros K T H. induction H; intros J HJ; constructor; try lia; eauto.
  eapply IHlc_ty_at; lia.
Qed.

Lemma lc_tm_weaken_ty : forall K k t, lc_tm_at K k t ->
  forall J, K <= J -> lc_tm_at J k t.
Proof.
  intros K k t H. induction H; intros J HJ; constructor; eauto using lc_ty_weaken.
  eapply IHlc_tm_at; lia.
Qed.

Lemma lc_open_tm_rec : forall K k t,
  lc_tm_at K (S k) t -> forall u, lc_tm_at K k u ->
  lc_tm_at K k (open_tm_rec k u t).
Proof.
  intros K k t H. remember (S k) as j eqn:E.
  revert k E. induction H; intros j Ej u Hu; subst; simpl.
  - destruct (Nat.eqb j i) eqn:Ei.
    + exact Hu.
    + constructor. apply Nat.eqb_neq in Ei. lia.
  - constructor.
  - constructor; auto. eapply IHlc_tm_at; eauto.
    eapply lc_tm_weaken_var; eauto; lia.
  - constructor; [eapply IHlc_tm_at1|eapply IHlc_tm_at2]; eauto.
  - constructor. eapply IHlc_tm_at; eauto.
    eapply lc_tm_weaken_ty; eauto; lia.
  - constructor; [eapply IHlc_tm_at|exact H0]; eauto.
  - constructor.
  - constructor; [eapply IHlc_tm_at1|eapply IHlc_tm_at2]; eauto.
  - constructor; [eapply IHlc_tm_at1|eapply IHlc_tm_at2]; eauto.
Qed.

Lemma lc_open_tm : forall T b v,
  locally_closed_tm (tm_abs T b) -> locally_closed_tm v ->
  locally_closed_tm (open_tm b v).
Proof.
  intros T b v H Hv. inversion H; subst. unfold open_tm.
  eapply lc_open_tm_rec; eauto.
Qed.

Lemma lc_open_ty_rec : forall K T,
  lc_ty_at (S K) T -> forall U, lc_ty_at K U ->
  lc_ty_at K (open_ty_rec K U T).
Proof.
  intros K T H. remember (S K) as J eqn:E. revert K E.
  induction H; intros J EJ U HU; subst; simpl.
  - destruct (Nat.eqb J i) eqn:Ei; auto. constructor.
    apply Nat.eqb_neq in Ei. lia.
  - constructor.
  - constructor; [eapply IHlc_ty_at1|eapply IHlc_ty_at2]; eauto.
  - constructor. eapply IHlc_ty_at; eauto. eapply lc_ty_weaken; eauto; lia.
  - constructor.
Qed.

Lemma lc_open_tm_ty_rec : forall K k t,
  lc_tm_at (S K) k t -> forall U, lc_ty_at K U ->
  lc_tm_at K k (open_tm_ty_rec K U t).
Proof.
  intros K k t H. remember (S K) as J eqn:E. revert K E.
  induction H; intros J EJ U HU; subst; simpl; constructor; eauto using lc_open_ty_rec.
  - eapply IHlc_tm_at. reflexivity. eapply lc_ty_weaken; eauto; lia.
Qed.

Lemma lc_open_tm_ty : forall b U,
  locally_closed_tm (tm_tabs b) -> locally_closed_ty U ->
  locally_closed_tm (open_tm_ty b U).
Proof.
  intros b U H HU. inversion H; subst. unfold open_tm_ty.
  eapply lc_open_tm_ty_rec; eauto.
Qed.

Lemma step_preserves_lc : forall t u,
  locally_closed_tm t -> t --> u -> locally_closed_tm u.
Proof.
  intros t u Hlc Hs. revert Hlc. induction Hs; intros Hlc; inversion Hlc; subst;
    try constructor; eauto using lc_open_tm, lc_open_tm_ty, value_is_lc.
  all: apply IHHs; assumption.
Qed.

Lemma multi_trans : forall a b c, multi a b -> multi b c -> multi a c.
Proof. intros a b c H. induction H; intros; eauto using multi. Qed.

Lemma safe_for_reduct : forall n t u,
  safe_for (S n) t -> t --> u -> safe_for n u.
Proof.
  intros n t u [Hv|[Hex Hall]] Hs.
  - exfalso; eapply value_no_step; eauto.
  - eapply Hall; eauto.
Qed.

Lemma safe_for_down : forall n t, safe_for (S n) t -> safe_for n t.
Proof.
  induction n as [|n IH]; intros t H; simpl; auto.
  destruct H as [Hv|[Hex Hall]].
  - left; exact Hv.
  - right. split; [exact Hex|]. intros u Hu. apply IH. apply Hall; exact Hu.
Qed.

Lemma LRe_reduct : forall n R t u,
  LRe (S n) R t -> t --> u -> LRe n R u.
Proof.
  intros n R t u [Hlc [Hsafe Hval]] Hs. split.
  - eapply step_preserves_lc; eauto.
  - split; [eapply safe_for_reduct; eauto|].
    intros v Hm Hv. apply LRv_down with (n:=n). apply Hval; auto.
    eapply multi_step; eauto.
Qed.

Lemma LRe_down : forall n R t, LRe (S n) R t -> LRe n R t.
Proof.
  intros n R t [Hlc [Hs Hv]]. split; [exact Hlc|]. split.
  - apply safe_for_down; exact Hs.
  - intros v Hm Hval. apply LRv_down with (n:=n); eauto.
Qed.

Lemma app_multi_value : forall a b v,
  multi (tm_app a b) v -> value v ->
  exists va vb, multi a va /\ value va /\ multi b vb /\ value vb /\
    multi (tm_app va vb) v.
Proof.
  intros a b v Hm Hv. remember (tm_app a b) as ab eqn:E.
  revert a b E. induction Hm; intros a b E; subst.
  - inversion Hv.
  - inversion H; subst.
    + match goal with
      | Hvarg : value ?arg, Hlcabs : locally_closed_tm (tm_abs ?T ?body) |- _ =>
          exists (tm_abs T body), arg
      end; repeat split; eauto using multi; try (constructor; assumption).
    + destruct (IHHm Hv _ _ eq_refl) as [va [vb [Ha [Hva [Hb [Hvb Happ]]]]]].
      exists va, vb. repeat split; eauto using multi.
    + destruct (IHHm Hv _ _ eq_refl) as [va [vb [Ha [Hva [Hb [Hvb Happ]]]]]].
      pose proof (multi_value a va H2 Ha) as E; subst va.
      exists a, vb. repeat split; eauto using multi.
Qed.

Lemma tapp_multi_value : forall a U v,
  multi (tm_tapp a U) v -> value v ->
  exists va, multi a va /\ value va /\ multi (tm_tapp va U) v.
Proof.
  intros a U v Hm Hv. remember (tm_tapp a U) as ab eqn:E.
  revert a U E. induction Hm; intros a U E; subst.
  - inversion Hv.
  - inversion H; subst.
    + exists (tm_tabs t). repeat split; eauto using multi; try (constructor; assumption).
    + destruct (IHHm Hv _ _ eq_refl) as [va [Ha [Hva Happ]]].
      exists va. repeat split; eauto using multi.
Qed.

Lemma div_multi_value : forall a b v,
  multi (tm_div a b) v -> value v -> exists z, v = tm_int z.
Proof.
  intros a b v Hm Hv. remember (tm_div a b) as ab eqn:E.
  revert a b E. induction Hm; intros a b E; subst.
  - inversion Hv.
  - inversion H; subst; eauto.
    pose proof (multi_value (tm_int (n / m)) t3 (v_int _) Hm) as E; subst; eauto.
Qed.

Lemma arith_multi_value : forall op a b v,
  multi (tm_arith op a b) v -> value v -> exists z, v = tm_int z.
Proof.
  intros op a b v Hm Hv. remember (tm_arith op a b) as ab eqn:E.
  revert op a b E. induction Hm; intros op0 a b E; subst.
  - inversion Hv.
  - inversion H; subst; eauto.
    pose proof (multi_value (tm_int (eval_integer_operator op0 n m)) t3 (v_int _) Hm) as E;
      subst; eauto.
Qed.

Lemma LRe_app : forall n A B a b,
  LRe n (R_Func A B) a -> LRe n A b ->
  LRe n (R_Exists A B) (tm_app a b).
Proof.
  induction n as [|n IH]; intros A B a b Ea Eb.
  - destruct Ea as [Hca [Hsa Hva]], Eb as [Hcb [Hsb Hvb]].
    split; [constructor; assumption|]. split; [simpl; auto|].
    intros v Hm Hv; simpl; exact Hv.
  - destruct Ea as [Hca [Hsa Hva]], Eb as [Hcb [Hsb Hvb]].
    split; [constructor; assumption|]. split.
    + destruct Hsa as [Hav|[[a' Ha'] HallA]].
      * destruct Hsb as [Hbv|[[b' Hb'] HallB]].
        -- pose proof (Hva a (multi_refl a) Hav) as VA.
           pose proof (Hvb b (multi_refl b) Hbv) as VB.
           simpl in VA. rewrite LRhead_equation_2 in VA.
           destruct VA as [_ [_ [T [body [-> F]]]]].
           apply (proj1 (F b VB)).
        -- right. split.
           ++ exists (tm_app a b'). constructor; assumption.
           ++ intros u Hu.
              assert (u = tm_app a b') as ->.
              { symmetry. exact (step_deterministic (tm_app a b) (tm_app a b')
                    (ST_App2 a b b' Hav Hb') u Hu). }
              pose proof (LRe_down n (R_Func A B) a
                (conj Hca (conj (or_introl Hav) Hva))) as EA'.
              pose proof (LRe_reduct n A b b'
                (conj Hcb (conj (or_intror (conj (ex_intro _ b' Hb') HallB)) Hvb)) Hb') as EB'.
              exact (proj1 (proj2 (IH A B a b' EA' EB'))).
      * right. split.
        -- exists (tm_app a' b). constructor; assumption.
        -- intros u Hu.
           assert (u = tm_app a' b) as ->.
           { symmetry. exact (step_deterministic (tm_app a b) (tm_app a' b)
                 (ST_App1 a a' b Ha' Hcb) u Hu). }
           pose proof (LRe_reduct n (R_Func A B) a a'
             (conj Hca (conj (or_intror (conj (ex_intro _ a' Ha') HallA)) Hva)) Ha') as EA'.
           pose proof (LRe_down n A b (conj Hcb (conj Hsb Hvb))) as EB'.
           exact (proj1 (proj2 (IH A B a' b EA' EB'))).
    + intros v Hm Hv. simpl. split.
      * exact (proj2 (proj2 (IH A B a b
          (LRe_down n _ _ (conj Hca (conj Hsa Hva)))
          (LRe_down n _ _ (conj Hcb (conj Hsb Hvb))))) v Hm Hv).
      * rewrite LRhead_equation_3. split; [exact Hv|].
        destruct (app_multi_value a b v Hm Hv)
          as [va [vb [Hma [Hva' [Hmb [Hvb' Hmapp]]]]]].
        pose proof (Hva va Hma Hva') as VA.
        pose proof (Hvb vb Hmb Hvb') as VB.
        simpl in VA. rewrite LRhead_equation_2 in VA.
        destruct VA as [_ [_ [T [body [E F]]]]].
        exists vb. split; [exact VB|exact (proj2 (F vb VB) v Hmapp Hv)].
Qed.

Lemma LRe_expand : forall n R t u,
  locally_closed_tm t -> t --> u -> LRe n R u -> LRe n R t.
Proof.
  intros n R t u Hct Htu [Hcu [Hsu Hvu]]. split; [exact Hct|]. split.
  - destruct n as [|n]; [simpl; auto|]. right. split; [eauto|]. intros u' Htu'.
    assert (u' = u) as -> by (eapply step_deterministic; eauto).
    apply safe_for_down; exact Hsu.
  - intros v Hm Hv. inversion Hm; subst.
    + exfalso; eapply value_no_step; eauto.
    + assert (t2 = u) by (eapply step_deterministic; eauto). subst.
      match goal with Htail : multi u v |- _ => exact (Hvu v Htail Hv) end.
Qed.

Lemma LRe_redex : forall n R t u,
  t --> u -> LRe n R u ->
  safe_for (S n) t /\
  (forall v, multi t v -> value v -> LRv n R v).
Proof.
  intros n R t u Htu [Hcu [Hsu Hvu]]. split.
  - right. split; [eauto|]. intros u' Htu'.
    assert (u' = u) as -> by (eapply step_deterministic; eauto). exact Hsu.
  - intros v Hm Hv. inversion Hm; subst.
    + exfalso; eapply value_no_step; eauto.
    + assert (t2 = u) by (eapply step_deterministic; eauto).
      subst. match goal with Htail : multi u v |- _ => exact (Hvu v Htail Hv) end.
Qed.

Lemma LRe_abs : forall n A B T body,
  locally_closed_tm (tm_abs T body) ->
  (forall k w, k <= n -> LRv k A w ->
    LRe k (open_rty_tm B w) (open_tm body w)) ->
  LRe n (R_Func A B) (tm_abs T body).
Proof.
  induction n as [|n IH]; intros A B T body Hlc Hbody.
  - apply LRe_value. simpl. constructor; exact Hlc.
  - apply LRe_value. simpl. split.
    + pose proof (IH A B T body Hlc
        (fun k w Hk Hw => Hbody k w ltac:(lia) Hw)) as Eprev.
      exact (proj2 (proj2 Eprev) (tm_abs T body) (multi_refl _)
        (v_abs T body Hlc)).
    + rewrite LRhead_equation_2. split; [constructor; exact Hlc|].
      exists T, body. split; [reflexivity|]. intros w Hw.
      pose proof (Hbody (S n) w (Nat.le_refl _) Hw) as Ebody.
      pose proof (LRe_redex (S n) (open_rty_tm B w)
        (tm_app (tm_abs T body) w) (open_tm body w)
        (ST_AppAbs T body w Hlc (LRv_is_value (S n) A w Hw)) Ebody) as HR.
      split; [apply safe_for_down; exact (proj1 HR)|exact (proj2 HR)].
Qed.

Lemma LRe_tabs : forall n B body,
  locally_closed_tm (tm_tabs body) ->
  (forall k U, k <= n -> locally_closed_ty U ->
    LRe k (open_rty_ty B U) (open_tm_ty body U)) ->
  LRe n (R_Poly B) (tm_tabs body).
Proof.
  induction n as [|n IH]; intros B body Hlc Hbody.
  - apply LRe_value. simpl. constructor; exact Hlc.
  - apply LRe_value. simpl. split.
    + pose proof (IH B body Hlc
        (fun k U Hk HU => Hbody k U ltac:(lia) HU)) as Eprev.
      exact (proj2 (proj2 Eprev) (tm_tabs body) (multi_refl _)
        (v_tabs body Hlc)).
    + rewrite LRhead_equation_4. split; [constructor; exact Hlc|]. exists body. split; [reflexivity|].
      intros U HU.
      pose proof (LRe_redex (S n) (open_rty_ty B U)
        (tm_tapp (tm_tabs body) U) (open_tm_ty body U)
        (ST_TAppTabs body U Hlc HU)
        (Hbody (S n) U (Nat.le_refl _) HU)) as HR.
      split; [apply safe_for_down; exact (proj1 HR)|exact (proj2 HR)].
Qed.

Lemma LRe_tapp : forall n B t U,
  LRe n (R_Poly B) t -> locally_closed_ty U ->
  LRe n (open_rty_ty B U) (tm_tapp t U).
Proof.
  induction n as [|n IH]; intros B t U Et HU.
  - destruct Et as [Hct [Hst Hvt]]. split; [constructor; assumption|].
    split; [simpl; auto|]. intros v Hm Hv; simpl; exact Hv.
  - destruct Et as [Hct [Hst Hvt]]. split; [constructor; assumption|]. split.
    + destruct Hst as [Htv|[[t' Ht'] Hall]].
      * pose proof (Hvt t (multi_refl _) Htv) as VT. simpl in VT.
        rewrite LRhead_equation_4 in VT.
        destruct VT as [_ [_ [body [-> F]]]]. exact (proj1 (F U HU)).
      * right. split; [exists (tm_tapp t' U); apply ST_TApp; assumption|].
        intros u Hu. assert (u = tm_tapp t' U) as ->.
        { symmetry. exact (step_deterministic _ _ (ST_TApp t t' U Ht' HU) _ Hu). }
        pose proof (LRe_reduct n (R_Poly B) t t'
          (conj Hct (conj (or_intror (conj (ex_intro _ t' Ht') Hall)) Hvt)) Ht') as Et'.
        exact (proj1 (proj2 (IH B t' U Et' HU))).
    + intros v Hm Hv. split.
      * pose proof (IH B t U (LRe_down n _ _ (conj Hct (conj Hst Hvt))) HU) as Eprev.
        exact (proj2 (proj2 Eprev) v Hm Hv).
      * destruct (tapp_multi_value t U v Hm Hv) as [vt [Hmt [Hvt' Hmapp]]].
        pose proof (Hvt vt Hmt Hvt') as VT. simpl in VT.
        rewrite LRhead_equation_4 in VT.
        destruct VT as [_ [_ [body [E F]]]]. exact (proj2 (proj2 (F U HU) v Hmapp Hv)).
Qed.

Lemma LRv_ne_nonzero : forall n v,
  LRv (S n) (R_Refine Ty_Int (Pred_Ne (tm_bvar 0) (tm_int 0%Z))) v ->
  exists z, v = tm_int z /\ z <> 0%Z.
Proof.
  intros n v H. simpl in H. destruct H as [_ HH].
  rewrite LRhead_equation_1 in HH. destruct HH as [Hv [Hshape Hneq]].
  destruct (Hshape eq_refl) as [z ->]. exists z. split; [reflexivity|].
  intro Ez; subst. apply Hneq. unfold qualifier_holds, predicate_holds; simpl.
  exists (tm_int 0%Z). repeat split; constructor.
Qed.

Lemma LRe_div : forall n a b,
  LRe n (R_Refine Ty_Int Pred_True) a ->
  LRe n (R_Refine Ty_Int (Pred_Ne (tm_bvar 0) (tm_int 0%Z))) b ->
  LRe n (R_Refine Ty_Int Pred_True) (tm_div a b).
Proof.
  induction n as [|n IH]; intros a b Ea Eb.
  - destruct Ea as [Hca [Hsa Hva]], Eb as [Hcb [Hsb Hvb]].
    split; [constructor; assumption|]. split; [simpl; auto|].
    intros v Hm Hv; simpl; exact Hv.
  - destruct Ea as [Hca [Hsa Hva]], Eb as [Hcb [Hsb Hvb]].
    split; [constructor; assumption|]. split.
    + destruct Hsa as [Hav|[[a' Ha'] HallA]].
      * destruct Hsb as [Hbv|[[b' Hb'] HallB]].
        -- pose proof (Hva a (multi_refl _) Hav) as VA.
           pose proof (Hvb b (multi_refl _) Hbv) as VB.
           simpl in VA. rewrite LRhead_equation_1 in VA.
           destruct VA as [_ [_ [HA _]]]. destruct (HA eq_refl) as [z ->].
           destruct (LRv_ne_nonzero n b VB) as [m [-> Hm]].
           right. split; [exists (tm_int (Z.div z m)); constructor; exact Hm|].
           intros u Hu. assert (u = tm_int (Z.div z m)) as ->.
           { symmetry. exact (step_deterministic _ _ (ST_DivInt z m Hm) _ Hu). }
           apply safe_value; constructor.
        -- right. split; [exists (tm_div a b'); apply ST_Div2; assumption|].
           intros u Hu. assert (u = tm_div a b') as ->.
           { symmetry. exact (step_deterministic _ _ (ST_Div2 a b b' Hav Hb') _ Hu). }
           apply (proj1 (proj2 (IH a b'
             (LRe_down n _ _ (conj Hca (conj (or_introl Hav) Hva)))
             (LRe_reduct n _ b b'
               (conj Hcb (conj (or_intror (conj (ex_intro _ b' Hb') HallB)) Hvb)) Hb')))).
      * right. split; [exists (tm_div a' b); apply ST_Div1; assumption|].
        intros u Hu. assert (u = tm_div a' b) as ->.
        { symmetry. exact (step_deterministic _ _ (ST_Div1 a a' b Ha' Hcb) _ Hu). }
        apply (proj1 (proj2 (IH a' b
          (LRe_reduct n _ a a'
            (conj Hca (conj (or_intror (conj (ex_intro _ a' Ha') HallA)) Hva)) Ha')
          (LRe_down n _ _ (conj Hcb (conj Hsb Hvb)))))).
    + intros v Hm Hv. simpl. split.
      * exact (proj2 (proj2 (IH a b
          (LRe_down n _ _ (conj Hca (conj Hsa Hva)))
          (LRe_down n _ _ (conj Hcb (conj Hsb Hvb))))) v Hm Hv).
      * rewrite LRhead_equation_1. split; [exact Hv|]. split.
        -- intros _. apply div_multi_value in Hm; assumption.
        -- simpl; exact I.
Qed.

Lemma multi_predicate_multistep : forall t u,
  multi t u -> predicate_multistep t u.
Proof. intros t u H; induction H; eauto using predicate_multistep. Qed.

Lemma LRe_arith : forall n op a b,
  LRe n (R_Refine Ty_Int Pred_True) a ->
  LRe n (R_Refine Ty_Int Pred_True) b ->
  LRe n (R_Refine Ty_Int (Pred_Eq (tm_bvar 0) (tm_arith op a b)))
    (tm_arith op a b).
Proof.
  induction n as [|n IH]; intros op a b Ea Eb.
  - destruct Ea as [Hca [Hsa Hva]], Eb as [Hcb [Hsb Hvb]].
    split; [constructor; assumption|]. split; [simpl; auto|].
    intros v Hm Hv; simpl; exact Hv.
  - destruct Ea as [Hca [Hsa Hva]], Eb as [Hcb [Hsb Hvb]].
    split; [constructor; assumption|]. split.
    + destruct Hsa as [Hav|[[a' Ha'] HallA]].
      * destruct Hsb as [Hbv|[[b' Hb'] HallB]].
        -- pose proof (Hva a (multi_refl _) Hav) as VA.
           pose proof (Hvb b (multi_refl _) Hbv) as VB.
           simpl in VA, VB. rewrite LRhead_equation_1 in VA.
           rewrite LRhead_equation_1 in VB.
           destruct VA as [_ [_ [HA _]]], VB as [_ [_ [HB _]]].
           destruct (HA eq_refl) as [z ->], (HB eq_refl) as [m ->].
           right. split; [exists (tm_int (eval_integer_operator op z m)); constructor|].
           intros u Hu. assert (u = tm_int (eval_integer_operator op z m)) as ->.
           { symmetry. exact (step_deterministic _ _ (ST_ArithInt op z m) _ Hu). }
           apply safe_value; constructor.
        -- right. split; [exists (tm_arith op a b'); apply ST_Arith2; assumption|].
           intros u Hu. assert (u = tm_arith op a b') as ->.
           { symmetry. exact (step_deterministic _ _ (ST_Arith2 op a b b' Hav Hb') _ Hu). }
           apply (proj1 (proj2 (IH op a b'
             (LRe_down n _ _ (conj Hca (conj (or_introl Hav) Hva)))
             (LRe_reduct n _ b b'
               (conj Hcb (conj (or_intror (conj (ex_intro _ b' Hb') HallB)) Hvb)) Hb')))).
      * right. split; [exists (tm_arith op a' b); apply ST_Arith1; assumption|].
        intros u Hu. assert (u = tm_arith op a' b) as ->.
        { symmetry. exact (step_deterministic _ _ (ST_Arith1 op a a' b Ha' Hcb) _ Hu). }
        apply (proj1 (proj2 (IH op a' b
          (LRe_reduct n _ a a'
            (conj Hca (conj (or_intror (conj (ex_intro _ a' Ha') HallA)) Hva)) Ha')
          (LRe_down n _ _ (conj Hcb (conj Hsb Hvb)))))).
    + intros v Hm Hv. simpl. split.
      * exact (proj2 (proj2 (IH op a b
          (LRe_down n _ _ (conj Hca (conj Hsa Hva)))
          (LRe_down n _ _ (conj Hcb (conj Hsb Hvb))))) v Hm Hv).
      * rewrite LRhead_equation_1. split; [exact Hv|]. split.
        -- intros _. apply arith_multi_value in Hm; assumption.
        -- unfold qualifier_holds, predicate_holds; simpl.
           exists v. split; [constructor|]. split.
           ++ rewrite (open_rec_lc a 0 v Hca), (open_rec_lc b 0 v Hcb).
              apply multi_predicate_multistep; exact Hm.
           ++ exact Hv.
Qed.

Lemma has_rtype_inst_lc : forall D G t R,
  has_rtype D G t R -> forall eta rho,
  (forall X, locally_closed_ty (eta X)) ->
  (forall x, locally_closed_tm (rho x)) ->
  locally_closed_tm (inst_tm eta rho t).
Proof.
  intros D G t R H. induction H; intros eta rho He Hr; simpl.
  - apply Hr.
  - set (x := fresh (L ++ fv_tm body)).
    assert (HxL : ~ In x L).
    { intro Hin; apply (fresh_notin (L ++ fv_tm body)); apply in_or_app; auto. }
    assert (Hxb : ~ In x (fv_tm body)).
    { intro Hin; apply (fresh_notin (L ++ fv_tm body)); apply in_or_app; auto. }
    specialize (H1 x HxL eta (extend_tm rho x (tm_int 0%Z)) He).
    assert (Hext : forall y, locally_closed_tm (extend_tm rho x (tm_int 0%Z) y)).
    { intros y. unfold extend_tm. destruct (Nat.eqb x y); auto. constructor. }
    specialize (H1 Hext). constructor.
    + apply wf_ty_inst_lc with (D:=Delta). apply wf_rty_erase_wf with (G:=RGamma); exact H. exact He.
    + eapply lc_tm_close_open with (u:=tm_int 0%Z).
      rewrite inst_open_tm in H1; [exact H1|exact Hxb|exact Hr].
  - constructor; [apply IHhas_rtype1|apply IHhas_rtype2]; assumption.
  - set (X := fresh (L ++ ftv_tm body)).
    assert (HXL : ~ In X L).
    { intro Hin; apply (fresh_notin (L ++ ftv_tm body)); apply in_or_app; auto. }
    assert (HXb : ~ In X (ftv_tm body)).
    { intro Hin; apply (fresh_notin (L ++ ftv_tm body)); apply in_or_app; auto. }
    specialize (H0 X HXL (extend_ty eta X Ty_Int) rho).
    assert (Het : forall Y, locally_closed_ty (extend_ty eta X Ty_Int Y)).
    { intros Y. unfold extend_ty. destruct (Nat.eqb X Y); auto. constructor. }
    specialize (H0 Het Hr). constructor.
    eapply lc_tm_ty_close_open with (U:=Ty_Int).
    unfold open_tm_ty in H0.
    rewrite inst_open_tm_ty_rec in H0; [exact H0|exact HXb|exact He|exact Hr].
  - constructor.
    + apply IHhas_rtype; assumption.
    + apply wf_ty_inst_lc with (D:=Delta); assumption.
  - constructor.
  - apply lc_tm_div; [apply IHhas_rtype1|apply IHhas_rtype2]; assumption.
  - apply lc_tm_arith; [apply IHhas_rtype1|apply IHhas_rtype2]; assumption.
  - eapply inst_tm_lc; eauto using value_is_lc.
  - eauto.
Qed.

Lemma inst_value : forall v eta rho,
  value v -> (forall X, locally_closed_ty (eta X)) ->
  (forall x, locally_closed_tm (rho x)) -> value (inst_tm eta rho v).
Proof.
  intros v eta rho Hv He Hr. inversion Hv; subst; simpl; constructor;
    eapply inst_tm_lc; eauto.
Qed.

Lemma typed_value_inst_int : forall D G v T eta rho,
  has_type D G v T -> value v -> inst_ty eta T = Ty_Int ->
  exists z, inst_tm eta rho v = tm_int z.
Proof.
  intros D G v T eta rho Ht Hv E. inversion Hv; subst; inversion Ht; subst;
    simpl in E; try discriminate; eauto.
Qed.

Lemma inst_tm_closed : forall t eta rho,
  fv_tm t = [] -> ftv_tm t = [] -> inst_tm eta rho t = t.
Proof.
  induction t; intros eta rho Hf Htf; simpl in *; try reflexivity; try discriminate.
  - f_equal.
    + clear Hf IHt. induction t0; simpl in *; try reflexivity; try discriminate.
      * f_equal; [apply IHt0_1|apply IHt0_2]; apply app_eq_nil in Htf; tauto.
      * f_equal. apply IHt0. exact Htf.
    + apply IHt; assumption.
  - apply app_eq_nil in Hf as [Hf1 Hf2].
    apply app_eq_nil in Htf as [Ht1 Ht2]. f_equal; [apply IHt1|apply IHt2]; assumption.
  - f_equal. apply IHt; assumption.
  - apply app_eq_nil in Htf as [Ht1 Ht2]. f_equal.
    + apply IHt; assumption.
    + clear Hf IHt. induction t0; simpl in *; try reflexivity; try discriminate.
      * f_equal; [apply IHt0_1|apply IHt0_2]; apply app_eq_nil in Ht2; tauto.
      * f_equal. apply IHt0. exact Ht2.
  - apply app_eq_nil in Hf as [Hf1 Hf2].
    apply app_eq_nil in Htf as [Ht1 Ht2]. f_equal; [apply IHt1|apply IHt2]; assumption.
  - apply app_eq_nil in Hf as [Hf1 Hf2].
    apply app_eq_nil in Htf as [Ht1 Ht2]. f_equal; [apply IHt1|apply IHt2]; assumption.
Qed.

Lemma inst_q_closed : forall q eta rho,
  predicate_closed q -> inst_q eta rho q = q.
Proof.
  induction q; intros eta rho H; simpl in *; try reflexivity.
  - destruct H as [Ha [Hfa [Hta [Hb [Hfb Htb]]]]].
    f_equal; apply inst_tm_closed; assumption.
  - destruct H as [Ha [Hfa [Hta [Hb [Hfb Htb]]]]].
    f_equal; apply inst_tm_closed; assumption.
  - destruct H as [Ha [Hfa [Hta [Hb [Hfb Htb]]]]].
    f_equal; apply inst_tm_closed; assumption.
  - destruct H; f_equal; auto.
  - destruct H; f_equal; auto.
  - f_equal; auto.
Qed.

Lemma inst_tm_open_general : forall t k eta rho u,
  (forall x, locally_closed_tm (rho x)) ->
  inst_tm eta rho (open_tm_rec k u t) =
  open_tm_rec k (inst_tm eta rho u) (inst_tm eta rho t).
Proof.
  induction t; intros k eta rho u Hr; simpl; try reflexivity.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry; apply open_rec_lc; apply Hr.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
Qed.

Lemma inst_q_open_general : forall q k eta rho u,
  (forall x, locally_closed_tm (rho x)) ->
  inst_q eta rho (open_qualifier_tm_rec k u q) =
  open_qualifier_tm_rec k (inst_tm eta rho u) (inst_q eta rho q).
Proof.
  induction q; intros k eta rho u Hr; simpl; try reflexivity;
    f_equal; auto using inst_tm_open_general.
Qed.

Lemma LRv_refine_value : forall n T q v,
  value v -> (T = Ty_Int -> exists z, v = tm_int z) ->
  qualifier_holds (open_qualifier_tm q v) -> LRv n (R_Refine T q) v.
Proof.
  induction n as [|n IH]; intros T q v Hv Hshape Hq; simpl; [exact Hv|].
  split; [apply IH; assumption|]. rewrite LRhead_equation_1.
  repeat split; assumption.
Qed.

Lemma fundamental_and_subtyping :
  (forall D G t R, has_rtype D G t R -> FundamentalP D G t R) /\
  (forall D G R S, subtype D G R S -> SubtypingP D G R S).
Proof.
  apply rtyping_subtyping_mutind; unfold FundamentalP, SubtypingP.
  - intros. eapply context_lookup_LRe; eauto.
  - intros L Delta RGamma R1 body R2 Hw Hbody IH n eta rho Heta Hctx.
    simpl. apply LRe_abs.
    + assert (Habs : has_rtype Delta RGamma (tm_abs (erase R1) body)
          (R_Func R1 R2)).
      { eapply RT_Abs with (L:=L); eauto. }
      exact (has_rtype_inst_lc Delta RGamma _ _ Habs eta rho Heta
        (fun y => value_is_lc _ ((proj1 Hctx) y))).
    + intros k v Hkn Hv.
      set (xs := L ++ fv_tm body ++ fv_rty_tm R2 ++
                 (fv_rty_tm R1 ++ support_rcontext RGamma)).
      set (x := fresh xs).
      assert (Hxf : ~ In x xs) by (apply fresh_notin).
      assert (HxL : ~ In x L).
      { intro E; apply Hxf. unfold xs. apply in_or_app; left; exact E. }
      assert (Hxb : ~ In x (fv_tm body)).
      { intro E; apply Hxf. unfold xs. apply in_or_app; right.
        apply in_or_app; left; exact E. }
      assert (HxR2 : ~ In x (fv_rty_tm R2)).
      { intro E; apply Hxf. unfold xs. apply in_or_app; right.
        apply in_or_app; right. apply in_or_app; left; exact E. }
      assert (Hxlast : ~ In x (fv_rty_tm R1 ++ support_rcontext RGamma)).
      { intro E; apply Hxf. unfold xs. apply in_or_app; right.
        apply in_or_app; right. apply in_or_app; right; exact E. }
      pose proof (context_interpretation_down n k eta rho RGamma Hkn Hctx) as Hctxk.
      pose proof (context_extend_tm k eta rho RGamma x R1 v Hctxk Hv Hxlast) as Hext.
      pose proof (IH x HxL k eta (extend_tm rho x v) Heta Hext) as Ebody.
      assert (Hr : forall y, locally_closed_tm (rho y)).
      { intros y; apply value_is_lc; apply (proj1 Hctx). }
      unfold open_tm, open_rty_tm in *.
      rewrite inst_open_tm_rec in Ebody; [|exact Hxb|exact Hr].
      rewrite inst_open_rty_tm_rec in Ebody; [|exact HxR2|exact Hr].
      exact Ebody.
  - intros. simpl. eapply LRe_app; eauto.
  - intros L Delta RGamma body R Hbody IH n eta rho Heta Hctx.
    simpl. apply LRe_tabs.
    + assert (Htabs : has_rtype Delta RGamma (tm_tabs body) (R_Poly R)).
      { eapply RT_TAbs with (L:=L); eauto. }
      exact (has_rtype_inst_lc Delta RGamma _ _ Htabs eta rho Heta
        (fun y => value_is_lc _ ((proj1 Hctx) y))).
    + intros k U Hkn HU.
      set (xs := L ++ ftv_tm body ++ ftv_rty R ++ support_ty_rcontext RGamma).
      set (X := fresh xs).
      assert (HXf : ~ In X xs) by (apply fresh_notin).
      assert (HXL : ~ In X L).
      { intro E; apply HXf. unfold xs. apply in_or_app; left; exact E. }
      assert (HXb : ~ In X (ftv_tm body)).
      { intro E; apply HXf. unfold xs. apply in_or_app; right.
        apply in_or_app; left; exact E. }
      assert (HXR : ~ In X (ftv_rty R)).
      { intro E; apply HXf. unfold xs. apply in_or_app; right.
        apply in_or_app; right. apply in_or_app; left; exact E. }
      assert (HXG : ~ In X (support_ty_rcontext RGamma)).
      { intro E; apply HXf. unfold xs. apply in_or_app; right.
        apply in_or_app; right. apply in_or_app; right; exact E. }
      pose proof (context_interpretation_down n k eta rho RGamma Hkn Hctx) as Hctxk.
      pose proof (context_extend_ty k eta rho RGamma X U Hctxk HXG) as HctxX.
      pose proof (IH X HXL k (extend_ty eta X U) rho
        (type_environment_extend Delta eta X U Heta HU) HctxX) as Ebody.
      assert (Hr : forall y, locally_closed_tm (rho y)).
      { intros y; apply value_is_lc; apply (proj1 Hctx). }
      unfold open_tm_ty, open_rty_ty in *.
      rewrite inst_open_tm_ty_rec in Ebody; [|exact HXb|exact Heta|exact Hr].
      rewrite inst_open_rty_ty_rec in Ebody; [|exact HXR|exact Heta|exact Hr].
      exact Ebody.
  - intros Delta RGamma t R U Ht IHt Hwf n eta rho Heta Hctx.
    assert (Hr : forall y, locally_closed_tm (rho y)).
    { intros y; apply value_is_lc; apply (proj1 Hctx). }
    unfold open_rty_ty. rewrite inst_rty_ty_open_general; [|exact Heta|exact Hr].
    apply LRe_tapp.
    + apply IHt; assumption.
    + apply wf_ty_inst_lc with (D:=Delta); assumption.
  - intros. apply LRe_int_exact.
  - intros. simpl. apply LRe_div; eauto.
  - intros. simpl. apply LRe_arith; eauto.
  - intros. Show.
Abort.

Theorem never_stuck : forall (t t' : tm) (R : rty),
  has_rtype [] empty_rcontext t R ->
  multi t t' ->
  value t' \/ exists t'' : tm, t' --> t''.
Proof.

Qed.

End SystemFRefinementTask.
