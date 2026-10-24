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

(* ============================================================ *)
(* Infrastructure: simultaneous type and term substitutions      *)
(* ============================================================ *)

Definition tenv := atom -> ty.
Definition menv := atom -> tm.

Definition upd_tenv (σ : tenv) (X : atom) (U : ty) : tenv :=
  fun Y => if Nat.eqb Y X then U else σ Y.

Definition upd_menv (ρ : menv) (x : atom) (w : tm) : menv :=
  fun y => if Nat.eqb y x then w else ρ y.

Lemma upd_tenv_same : forall σ X U, upd_tenv σ X U X = U.
Proof. intros. unfold upd_tenv. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma upd_tenv_other : forall σ X U Y, Y <> X -> upd_tenv σ X U Y = σ Y.
Proof. intros. unfold upd_tenv. apply Nat.eqb_neq in H. rewrite H. reflexivity. Qed.

Lemma upd_menv_same : forall ρ x w, upd_menv ρ x w x = w.
Proof. intros. unfold upd_menv. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma upd_menv_other : forall ρ x w y, y <> x -> upd_menv ρ x w y = ρ y.
Proof. intros. unfold upd_menv. apply Nat.eqb_neq in H. rewrite H. reflexivity. Qed.

Fixpoint ty_tsubst (σ : tenv) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => σ X
  | Ty_Arrow T1 T2 => Ty_Arrow (ty_tsubst σ T1) (ty_tsubst σ T2)
  | Ty_All T1 => Ty_All (ty_tsubst σ T1)
  | Ty_Int => Ty_Int
  end.

Fixpoint tm_tsubst (σ : tenv) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T t1 => tm_abs (ty_tsubst σ T) (tm_tsubst σ t1)
  | tm_app t1 t2 => tm_app (tm_tsubst σ t1) (tm_tsubst σ t2)
  | tm_tabs t1 => tm_tabs (tm_tsubst σ t1)
  | tm_tapp t1 T => tm_tapp (tm_tsubst σ t1) (ty_tsubst σ T)
  | tm_int n => tm_int n
  | tm_div t1 t2 => tm_div (tm_tsubst σ t1) (tm_tsubst σ t2)
  | tm_arith op t1 t2 => tm_arith op (tm_tsubst σ t1) (tm_tsubst σ t2)
  end.

Fixpoint q_tsubst (σ : tenv) (p : qualifier) : qualifier :=
  match p with
  | Pred_True => Pred_True
  | Pred_False => Pred_False
  | Pred_Eq t1 t2 => Pred_Eq (tm_tsubst σ t1) (tm_tsubst σ t2)
  | Pred_Lt t1 t2 => Pred_Lt (tm_tsubst σ t1) (tm_tsubst σ t2)
  | Pred_Le t1 t2 => Pred_Le (tm_tsubst σ t1) (tm_tsubst σ t2)
  | Pred_And p1 p2 => Pred_And (q_tsubst σ p1) (q_tsubst σ p2)
  | Pred_Or p1 p2 => Pred_Or (q_tsubst σ p1) (q_tsubst σ p2)
  | Pred_Not p1 => Pred_Not (q_tsubst σ p1)
  end.

Fixpoint r_tsubst (σ : tenv) (R : rty) : rty :=
  match R with
  | R_Refine T p => R_Refine (ty_tsubst σ T) (q_tsubst σ p)
  | R_Func R1 R2 => R_Func (r_tsubst σ R1) (r_tsubst σ R2)
  | R_Exists R1 R2 => R_Exists (r_tsubst σ R1) (r_tsubst σ R2)
  | R_Poly R1 => R_Poly (r_tsubst σ R1)
  end.

Fixpoint tm_msubst (ρ : menv) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => ρ x
  | tm_abs T t1 => tm_abs T (tm_msubst ρ t1)
  | tm_app t1 t2 => tm_app (tm_msubst ρ t1) (tm_msubst ρ t2)
  | tm_tabs t1 => tm_tabs (tm_msubst ρ t1)
  | tm_tapp t1 T => tm_tapp (tm_msubst ρ t1) T
  | tm_int n => tm_int n
  | tm_div t1 t2 => tm_div (tm_msubst ρ t1) (tm_msubst ρ t2)
  | tm_arith op t1 t2 => tm_arith op (tm_msubst ρ t1) (tm_msubst ρ t2)
  end.

Fixpoint q_msubst (ρ : menv) (p : qualifier) : qualifier :=
  match p with
  | Pred_True => Pred_True
  | Pred_False => Pred_False
  | Pred_Eq t1 t2 => Pred_Eq (tm_msubst ρ t1) (tm_msubst ρ t2)
  | Pred_Lt t1 t2 => Pred_Lt (tm_msubst ρ t1) (tm_msubst ρ t2)
  | Pred_Le t1 t2 => Pred_Le (tm_msubst ρ t1) (tm_msubst ρ t2)
  | Pred_And p1 p2 => Pred_And (q_msubst ρ p1) (q_msubst ρ p2)
  | Pred_Or p1 p2 => Pred_Or (q_msubst ρ p1) (q_msubst ρ p2)
  | Pred_Not p1 => Pred_Not (q_msubst ρ p1)
  end.

Fixpoint r_msubst (ρ : menv) (R : rty) : rty :=
  match R with
  | R_Refine T p => R_Refine T (q_msubst ρ p)
  | R_Func R1 R2 => R_Func (r_msubst ρ R1) (r_msubst ρ R2)
  | R_Exists R1 R2 => R_Exists (r_msubst ρ R1) (r_msubst ρ R2)
  | R_Poly R1 => R_Poly (r_msubst ρ R1)
  end.

Definition tm_subst_all (ρ : menv) (σ : tenv) (t : tm) : tm :=
  tm_msubst ρ (tm_tsubst σ t).

Definition q_subst_all (ρ : menv) (σ : tenv) (p : qualifier) : qualifier :=
  q_msubst ρ (q_tsubst σ p).

Definition r_subst_all (ρ : menv) (σ : tenv) (R : rty) : rty :=
  r_msubst ρ (r_tsubst σ R).

(* Free term variables and free type variables of qualifiers / rtypes *)

Fixpoint fv_q (p : qualifier) : list atom :=
  match p with
  | Pred_True | Pred_False => []
  | Pred_Eq t1 t2 | Pred_Lt t1 t2 | Pred_Le t1 t2 => fv_tm t1 ++ fv_tm t2
  | Pred_And p1 p2 | Pred_Or p1 p2 => fv_q p1 ++ fv_q p2
  | Pred_Not p1 => fv_q p1
  end.

Fixpoint ftv_q (p : qualifier) : list atom :=
  match p with
  | Pred_True | Pred_False => []
  | Pred_Eq t1 t2 | Pred_Lt t1 t2 | Pred_Le t1 t2 => ftv_tm t1 ++ ftv_tm t2
  | Pred_And p1 p2 | Pred_Or p1 p2 => ftv_q p1 ++ ftv_q p2
  | Pred_Not p1 => ftv_q p1
  end.

Fixpoint fv_r (R : rty) : list atom :=
  match R with
  | R_Refine T p => fv_q p
  | R_Func R1 R2 => fv_r R1 ++ fv_r R2
  | R_Exists R1 R2 => fv_r R1 ++ fv_r R2
  | R_Poly R1 => fv_r R1
  end.

Fixpoint ftv_r (R : rty) : list atom :=
  match R with
  | R_Refine T p => fv_ty T ++ ftv_q p
  | R_Func R1 R2 => ftv_r R1 ++ ftv_r R2
  | R_Exists R1 R2 => ftv_r R1 ++ ftv_r R2
  | R_Poly R1 => ftv_r R1
  end.

Fixpoint fv_rcontext (RGamma : rcontext) : list atom :=
  match RGamma with
  | [] => []
  | (x, R) :: RGamma' => fv_r R ++ fv_rcontext RGamma'
  end.

Fixpoint ftv_rcontext (RGamma : rcontext) : list atom :=
  match RGamma with
  | [] => []
  | (x, R) :: RGamma' => ftv_r R ++ ftv_rcontext RGamma'
  end.

(* Fresh atoms *)

Lemma max_atom_ge : forall L x, In x L -> x <= max_atom L.
Proof.
  induction L as [| a L IH]; intros x Hin; simpl in Hin.
  - destruct Hin.
  - destruct Hin as [-> | Hin].
    + apply Nat.le_max_l.
    + apply Nat.le_trans with (max_atom L); [apply IH; auto | apply Nat.le_max_r].
Qed.

Lemma fresh_notin : forall L, ~ In (fresh L) L.
Proof.
  intros L Hin. unfold fresh in Hin.
  pose proof (max_atom_ge L _ Hin). lia.
Qed.

Lemma fresh_notin_app : forall L1 L2, ~ In (fresh (L1 ++ L2)) L1 /\ ~ In (fresh (L1 ++ L2)) L2.
Proof.
  intros. split; intro H; apply fresh_notin with (L := L1 ++ L2);
    [ apply in_app_iff; left; auto | apply in_app_iff; right; auto ].
Qed.

Definition lc_tenv (σ : tenv) : Prop := forall X, locally_closed_ty (σ X).
Definition lc_menv (ρ : menv) : Prop := forall x, locally_closed_tm (ρ x).

Lemma lc_ty_bvar_absurd : forall T, locally_closed_ty T -> forall i, T <> Ty_BVar i.
Proof.
  intros T Hlc i. intro H. subst T. inversion Hlc. lia.
Qed.

Lemma lc_tm_bvar_absurd : forall t, locally_closed_tm t -> forall i, t <> tm_bvar i.
Proof.
  intros t Hlc i. intro H. subst t. inversion Hlc. lia.
Qed.

Lemma open_ty_rec_lc : forall K k T U, lc_ty_at K T -> K <= k -> open_ty_rec k U T = T.
Proof.
  intros K k T U Hlc Hle. revert k U Hle. induction Hlc; intros k0 U0 Hle; simpl.
  - destruct (Nat.eqb k0 i) eqn:E; [|reflexivity].
    apply Nat.eqb_eq in E. lia.
  - reflexivity.
  - rewrite (IHHlc1 k0 U0 Hle), (IHHlc2 k0 U0 Hle). reflexivity.
  - rewrite (IHHlc (S k0) U0). reflexivity. lia.
  - reflexivity.
Qed.

Lemma open_tm_ty_rec_lc : forall K kt t U, lc_tm_at K kt t -> forall k, K <= k -> open_tm_ty_rec k U t = t.
Proof.
  intros K kt t U Hlc. induction Hlc; intros k0 Hle; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite (open_ty_rec_lc K k0 T U H Hle). rewrite (IHHlc k0 Hle). reflexivity.
  - rewrite (IHHlc1 k0 Hle), (IHHlc2 k0 Hle). reflexivity.
  - rewrite (IHHlc (S k0) (le_n_S _ _ Hle)). reflexivity.
  - rewrite (IHHlc k0 Hle). rewrite (open_ty_rec_lc K k0 T U H Hle). reflexivity.
  - reflexivity.
  - rewrite (IHHlc1 k0 Hle), (IHHlc2 k0 Hle). reflexivity.
  - rewrite (IHHlc1 k0 Hle), (IHHlc2 k0 Hle). reflexivity.
Qed.

Lemma open_tm_rec_lc : forall K k k' t u, lc_tm_at K k t -> k <= k' -> open_tm_rec k' u t = t.
Proof.
  intros K k k' t u Hlc Hle. revert k' u Hle. induction Hlc; intros k0 u0 Hle; simpl.
  - destruct (Nat.eqb k0 i) eqn:E; [|reflexivity].
    apply Nat.eqb_eq in E. lia.
  - reflexivity.
  - rewrite (IHHlc (S k0) u0). reflexivity. lia.
  - rewrite (IHHlc1 k0 u0 Hle), (IHHlc2 k0 u0 Hle). reflexivity.
  - rewrite (IHHlc k0 u0 Hle). reflexivity.
  - rewrite (IHHlc k0 u0 Hle). reflexivity.
  - reflexivity.
  - rewrite (IHHlc1 k0 u0 Hle), (IHHlc2 k0 u0 Hle). reflexivity.
  - rewrite (IHHlc1 k0 u0 Hle), (IHHlc2 k0 u0 Hle). reflexivity.
Qed.

(* Type substitution commutes with opening *)

Lemma ty_tsubst_open_ty_rec : forall σ k U T,
  lc_tenv σ ->
  ty_tsubst σ (open_ty_rec k U T) = open_ty_rec k (ty_tsubst σ U) (ty_tsubst σ T).
Proof.
  intros σ k U T Hσ. revert k U. induction T; intros k0 U0; simpl.
  - destruct (Nat.eqb k0 n); reflexivity.
  - symmetry. apply (open_ty_rec_lc 0 k0 (σ a) (ty_tsubst σ U0)).
    apply Hσ. lia.
  - rewrite IHT1, IHT2. reflexivity.
  - rewrite IHT. reflexivity.
  - reflexivity.
Qed.

Lemma tm_tsubst_open_tm_rec : forall σ k u t,
  tm_tsubst σ (open_tm_rec k u t) = open_tm_rec k (tm_tsubst σ u) (tm_tsubst σ t).
Proof.
  intros σ k u t. revert k u. induction t as [ i | x | T0 t1 IHt1 | t1 IHt1 t2 IHt2 | t1 IHt1 | t1 IHt1 T0 | z | t1 IHt1 t2 IHt2 | op t1 IHt1 t2 IHt2 ]; intros k0 u0; simpl.
  - destruct (Nat.eqb k0 i); reflexivity.
  - reflexivity.
  - rewrite IHt1. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt1. reflexivity.
  - rewrite IHt1. reflexivity.
  - reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma tm_msubst_open_tm_rec : forall ρ k u t,
  lc_menv ρ ->
  tm_msubst ρ (open_tm_rec k u t) = open_tm_rec k (tm_msubst ρ u) (tm_msubst ρ t).
Proof.
  intros ρ k u t Hρ. revert k u. induction t as [ i | x | T0 t1 IHt1 | t1 IHt1 t2 IHt2 | t1 IHt1 | t1 IHt1 T0 | z | t1 IHt1 t2 IHt2 | op t1 IHt1 t2 IHt2 ]; intros k0 u0; simpl.
  - destruct (Nat.eqb k0 i); reflexivity.
  - symmetry. apply (open_tm_rec_lc 0 0 k0 (ρ x) (tm_msubst ρ u0)).
    apply Hρ. lia.
  - rewrite IHt1. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt1. reflexivity.
  - rewrite IHt1. reflexivity.
  - reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma tm_tsubst_open_tm_ty_rec : forall σ k U t,
  lc_tenv σ ->
  tm_tsubst σ (open_tm_ty_rec k U t) = open_tm_ty_rec k (ty_tsubst σ U) (tm_tsubst σ t).
Proof.
  intros σ k U t Hσ. revert k U. induction t as [ i | x | T0 t1 IHt1 | t1 IHt1 t2 IHt2 | t1 IHt1 | t1 IHt1 T0 | z | t1 IHt1 t2 IHt2 | op t1 IHt1 t2 IHt2 ]; intros k0 U0; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite (ty_tsubst_open_ty_rec σ k0 U0 T0 Hσ), IHt1. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt1. reflexivity.
  - rewrite IHt1, (ty_tsubst_open_ty_rec σ k0 U0 T0 Hσ). reflexivity.
  - reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma tm_msubst_open_tm_ty_rec : forall ρ k U t,
  lc_menv ρ ->
  tm_msubst ρ (open_tm_ty_rec k U t) = open_tm_ty_rec k U (tm_msubst ρ t).
Proof.
  intros ρ k U t Hρ. revert k U. induction t as [ i | x | T0 t1 IHt1 | t1 IHt1 t2 IHt2 | t1 IHt1 | t1 IHt1 T0 | z | t1 IHt1 t2 IHt2 | op t1 IHt1 t2 IHt2 ]; intros k0 U0; simpl.
  - reflexivity.
  - symmetry. apply (open_tm_ty_rec_lc 0 0 (ρ x) U0 (Hρ x) k0). lia.
  - rewrite IHt1. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt1. reflexivity.
  - rewrite IHt1. reflexivity.
  - reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma q_tsubst_open_pred_tm_rec : forall σ k u p,
  q_tsubst σ (open_pred_tm_rec k u p) = open_pred_tm_rec k (tm_tsubst σ u) (q_tsubst σ p).
Proof.
  intros σ k u p. revert k u. induction p as [ | | t1 t2 | t1 t2 | t1 t2 | p1 IHp1 p2 IHp2 | p1 IHp1 p2 IHp2 | p1 IHp1 ]; intros k0 u0; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite !tm_tsubst_open_tm_rec. reflexivity.
  - rewrite !tm_tsubst_open_tm_rec. reflexivity.
  - rewrite !tm_tsubst_open_tm_rec. reflexivity.
  - rewrite IHp1, IHp2. reflexivity.
  - rewrite IHp1, IHp2. reflexivity.
  - rewrite IHp1. reflexivity.
Qed.

Lemma q_msubst_open_pred_tm_rec : forall ρ k u p,
  lc_menv ρ ->
  q_msubst ρ (open_pred_tm_rec k u p) = open_pred_tm_rec k (tm_msubst ρ u) (q_msubst ρ p).
Proof.
  intros ρ k u p Hρ. revert k u. induction p as [ | | t1 t2 | t1 t2 | t1 t2 | p1 IHp1 p2 IHp2 | p1 IHp1 p2 IHp2 | p1 IHp1 ]; intros k0 u0; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite !(tm_msubst_open_tm_rec ρ _ _ _ Hρ). reflexivity.
  - rewrite !(tm_msubst_open_tm_rec ρ _ _ _ Hρ). reflexivity.
  - rewrite !(tm_msubst_open_tm_rec ρ _ _ _ Hρ). reflexivity.
  - rewrite IHp1, IHp2. reflexivity.
  - rewrite IHp1, IHp2. reflexivity.
  - rewrite IHp1. reflexivity.
Qed.

Lemma q_tsubst_open_pred_ty_rec : forall σ k U p,
  lc_tenv σ ->
  q_tsubst σ (open_pred_ty_rec k U p) = open_pred_ty_rec k (ty_tsubst σ U) (q_tsubst σ p).
Proof.
  intros σ k U p Hσ. revert k U. induction p as [ | | t1 t2 | t1 t2 | t1 t2 | p1 IHp1 p2 IHp2 | p1 IHp1 p2 IHp2 | p1 IHp1 ]; intros k0 U0; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite !(tm_tsubst_open_tm_ty_rec σ _ _ _ Hσ). reflexivity.
  - rewrite !(tm_tsubst_open_tm_ty_rec σ _ _ _ Hσ). reflexivity.
  - rewrite !(tm_tsubst_open_tm_ty_rec σ _ _ _ Hσ). reflexivity.
  - rewrite IHp1, IHp2. reflexivity.
  - rewrite IHp1, IHp2. reflexivity.
  - rewrite IHp1. reflexivity.
Qed.

Lemma q_msubst_open_pred_ty_rec : forall ρ k U p,
  lc_menv ρ ->
  q_msubst ρ (open_pred_ty_rec k U p) = open_pred_ty_rec k U (q_msubst ρ p).
Proof.
  intros ρ k U p Hρ. revert k U. induction p as [ | | t1 t2 | t1 t2 | t1 t2 | p1 IHp1 p2 IHp2 | p1 IHp1 p2 IHp2 | p1 IHp1 ]; intros k0 U0; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite !(tm_msubst_open_tm_ty_rec ρ _ _ _ Hρ). reflexivity.
  - rewrite !(tm_msubst_open_tm_ty_rec ρ _ _ _ Hρ). reflexivity.
  - rewrite !(tm_msubst_open_tm_ty_rec ρ _ _ _ Hρ). reflexivity.
  - rewrite IHp1, IHp2. reflexivity.
  - rewrite IHp1, IHp2. reflexivity.
  - rewrite IHp1. reflexivity.
Qed.

Lemma r_tsubst_open_rty_tm_rec : forall σ k u R,
  r_tsubst σ (open_rty_tm_rec k u R) = open_rty_tm_rec k (tm_tsubst σ u) (r_tsubst σ R).
Proof.
  intros σ k u R. revert k u. induction R as [ T0 p0 | R1 IHR1 R2 IHR2 | R1 IHR1 R2 IHR2 | R1 IHR1 ]; intros k0 u0; simpl.
  - unfold open_qualifier_tm_rec. rewrite q_tsubst_open_pred_tm_rec. reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR1. reflexivity.
Qed.

Lemma r_msubst_open_rty_tm_rec : forall ρ k u R,
  lc_menv ρ ->
  r_msubst ρ (open_rty_tm_rec k u R) = open_rty_tm_rec k (tm_msubst ρ u) (r_msubst ρ R).
Proof.
  intros ρ k u R Hρ. revert k u. induction R as [ T0 p0 | R1 IHR1 R2 IHR2 | R1 IHR1 R2 IHR2 | R1 IHR1 ]; intros k0 u0; simpl.
  - unfold open_qualifier_tm_rec.
    rewrite (q_msubst_open_pred_tm_rec ρ (S k0) u0 p0 Hρ). reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR1. reflexivity.
Qed.

Lemma r_tsubst_open_rty_ty_rec : forall σ k U R,
  lc_tenv σ ->
  r_tsubst σ (open_rty_ty_rec k U R) = open_rty_ty_rec k (ty_tsubst σ U) (r_tsubst σ R).
Proof.
  intros σ k U R Hσ. revert k U. induction R as [ T0 p0 | R1 IHR1 R2 IHR2 | R1 IHR1 R2 IHR2 | R1 IHR1 ]; intros k0 U0; simpl.
  - unfold open_qualifier_ty_rec.
    rewrite (ty_tsubst_open_ty_rec σ k0 U0 T0 Hσ), (q_tsubst_open_pred_ty_rec σ k0 U0 p0 Hσ). reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR1. reflexivity.
Qed.

Lemma r_msubst_open_rty_ty_rec : forall ρ k U R,
  lc_menv ρ ->
  r_msubst ρ (open_rty_ty_rec k U R) = open_rty_ty_rec k U (r_msubst ρ R).
Proof.
  intros ρ k U R Hρ. revert k U. induction R as [ T0 p0 | R1 IHR1 R2 IHR2 | R1 IHR1 R2 IHR2 | R1 IHR1 ]; intros k0 U0; simpl.
  - unfold open_qualifier_ty_rec.
    rewrite (q_msubst_open_pred_ty_rec ρ k0 U0 p0 Hρ). reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR1. reflexivity.
Qed.

(* Specialized forms with [open_ty], [open_tm], [open_tm_ty], [open_rty_tm], [open_rty_ty] *)

Lemma tm_tsubst_open_tm : forall σ t u,
  tm_tsubst σ (open_tm t u) = open_tm (tm_tsubst σ t) (tm_tsubst σ u).
Proof. intros. apply tm_tsubst_open_tm_rec. Qed.

Lemma tm_msubst_open_tm : forall ρ t u,
  lc_menv ρ ->
  tm_msubst ρ (open_tm t u) = open_tm (tm_msubst ρ t) (tm_msubst ρ u).
Proof. intros. apply tm_msubst_open_tm_rec; auto. Qed.

Lemma tm_tsubst_open_tm_ty : forall σ t U,
  lc_tenv σ ->
  tm_tsubst σ (open_tm_ty t U) = open_tm_ty (tm_tsubst σ t) (ty_tsubst σ U).
Proof. intros. apply tm_tsubst_open_tm_ty_rec; auto. Qed.

Lemma tm_msubst_open_tm_ty : forall ρ t U,
  lc_menv ρ ->
  tm_msubst ρ (open_tm_ty t U) = open_tm_ty (tm_msubst ρ t) U.
Proof. intros. apply tm_msubst_open_tm_ty_rec; auto. Qed.

Lemma r_tsubst_open_rty_tm : forall σ R u,
  r_tsubst σ (open_rty_tm R u) = open_rty_tm (r_tsubst σ R) (tm_tsubst σ u).
Proof. intros. apply r_tsubst_open_rty_tm_rec. Qed.

Lemma r_msubst_open_rty_tm : forall ρ R u,
  lc_menv ρ ->
  r_msubst ρ (open_rty_tm R u) = open_rty_tm (r_msubst ρ R) (tm_msubst ρ u).
Proof. intros. apply r_msubst_open_rty_tm_rec; auto. Qed.

Lemma r_tsubst_open_rty_ty : forall σ R U,
  lc_tenv σ ->
  r_tsubst σ (open_rty_ty R U) = open_rty_ty (r_tsubst σ R) (ty_tsubst σ U).
Proof. intros. apply r_tsubst_open_rty_ty_rec; auto. Qed.

Lemma r_msubst_open_rty_ty : forall ρ R U,
  lc_menv ρ ->
  r_msubst ρ (open_rty_ty R U) = open_rty_ty (r_msubst ρ R) U.
Proof. intros. apply r_msubst_open_rty_ty_rec; auto. Qed.

(* Combined substitutions commute with opening *)

Lemma tm_subst_all_open_tm : forall ρ σ t u,
  lc_menv ρ -> lc_tenv σ ->
  tm_subst_all ρ σ (open_tm t u) =
  open_tm (tm_subst_all ρ σ t) (tm_subst_all ρ σ u).
Proof.
  intros ρ σ t u Hρ Hσ. unfold tm_subst_all.
  rewrite tm_tsubst_open_tm.
  rewrite (tm_msubst_open_tm ρ _ _ Hρ).
  reflexivity.
Qed.

Lemma tm_subst_all_open_tm_ty : forall ρ σ t U,
  lc_menv ρ -> lc_tenv σ ->
  tm_subst_all ρ σ (open_tm_ty t U) =
  open_tm_ty (tm_subst_all ρ σ t) (ty_tsubst σ U).
Proof.
  intros ρ σ t U Hρ Hσ. unfold tm_subst_all.
  rewrite (tm_tsubst_open_tm_ty σ _ _ Hσ).
  rewrite (tm_msubst_open_tm_ty ρ _ _ Hρ).
  reflexivity.
Qed.

Lemma q_subst_all_open_pred_tm : forall ρ σ p u,
  lc_menv ρ -> lc_tenv σ ->
  q_subst_all ρ σ (open_pred_tm p u) =
  open_pred_tm (q_subst_all ρ σ p) (tm_subst_all ρ σ u).
Proof.
  intros ρ σ p u Hρ Hσ. unfold q_subst_all, open_pred_tm, tm_subst_all.
  rewrite (q_tsubst_open_pred_tm_rec σ 0 u p).
  rewrite (q_msubst_open_pred_tm_rec ρ 0 _ _ Hρ).
  reflexivity.
Qed.

Lemma q_subst_all_open_pred_ty : forall ρ σ p U,
  lc_menv ρ -> lc_tenv σ ->
  q_subst_all ρ σ (open_pred_ty_rec 0 U p) =
  open_pred_ty_rec 0 (ty_tsubst σ U) (q_subst_all ρ σ p).
Proof.
  intros ρ σ p U Hρ Hσ. unfold q_subst_all.
  rewrite (q_tsubst_open_pred_ty_rec σ 0 U p Hσ).
  rewrite (q_msubst_open_pred_ty_rec ρ 0 _ _ Hρ).
  reflexivity.
Qed.

Lemma r_subst_all_open_rty_tm : forall ρ σ R u,
  lc_menv ρ -> lc_tenv σ ->
  r_subst_all ρ σ (open_rty_tm R u) =
  open_rty_tm (r_subst_all ρ σ R) (tm_subst_all ρ σ u).
Proof.
  intros ρ σ R u Hρ Hσ. unfold r_subst_all, open_rty_tm, tm_subst_all.
  rewrite (r_tsubst_open_rty_tm_rec σ 0 u R).
  rewrite (r_msubst_open_rty_tm_rec ρ 0 _ _ Hρ).
  reflexivity.
Qed.

Lemma r_subst_all_open_rty_ty : forall ρ σ R U,
  lc_menv ρ -> lc_tenv σ ->
  r_subst_all ρ σ (open_rty_ty R U) =
  open_rty_ty (r_subst_all ρ σ R) (ty_tsubst σ U).
Proof.
  intros ρ σ R U Hρ Hσ. unfold r_subst_all, open_rty_ty.
  rewrite (r_tsubst_open_rty_ty_rec σ 0 U R Hσ).
  rewrite (r_msubst_open_rty_ty_rec ρ 0 _ _ Hρ).
  reflexivity.
Qed.

(* ============================================================ *)
(* Locally closed metatheory                                     *)
(* ============================================================ *)

Lemma notin_app_l : forall (L1 L2 : list atom) x, ~ In x (L1 ++ L2) -> ~ In x L1.
Proof. intros L1 L2 x H Hin. apply H. apply in_app_iff. left. auto. Qed.

Lemma notin_app_r : forall (L1 L2 : list atom) x, ~ In x (L1 ++ L2) -> ~ In x L2.
Proof. intros L1 L2 x H Hin. apply H. apply in_app_iff. right. auto. Qed.

Lemma lc_ty_at_mono : forall K K' T, lc_ty_at K T -> K <= K' -> lc_ty_at K' T.
Proof.
  intros K K' T. revert K K'. induction T as [ n | a | T1 IHT1 T2 IHT2 | T1 IHT1 | ];
    intros K K' Hlc Hle; inversion Hlc; subst;
    try (apply lc_ty_bvar; lia);
    try apply lc_ty_fvar;
    try (apply lc_ty_arrow; [apply IHT1 with (K:=K); auto | apply IHT2 with (K:=K); auto]);
    try (apply lc_ty_all; apply IHT1 with (K:=S K); auto; lia);
    try apply lc_ty_int.
Qed.

Lemma lc_tm_at_mono : forall K k K' k' t,
  lc_tm_at K k t -> K <= K' -> k <= k' -> lc_tm_at K' k' t.
Proof.
  intros K k K' k' t. revert K k K' k'.
  induction t as [ i | x | T0 t1 IHt1 | t1 IHt1 t2 IHt2 | t1 IHt1 | t1 IHt1 T0 | z | t1 IHt1 t2 IHt2 | op t1 IHt1 t2 IHt2 ];
    intros K k K' k' Hlc HK Hk; inversion Hlc; subst.
  - apply lc_tm_bvar. lia.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + apply lc_ty_at_mono with (K := K); auto.
    + apply IHt1 with (K := K) (k := S k); auto. lia.
  - apply lc_tm_app; [apply IHt1 with (K:=K) (k:=k) | apply IHt2 with (K:=K) (k:=k)]; auto.
  - apply lc_tm_tabs. apply IHt1 with (K := S K) (k := k); auto. lia.
  - apply lc_tm_tapp.
    + apply IHt1 with (K := K) (k := k); auto.
    + apply lc_ty_at_mono with (K := K); auto.
  - apply lc_tm_int.
  - apply lc_tm_div; [apply IHt1 with (K:=K) (k:=k) | apply IHt2 with (K:=K) (k:=k)]; auto.
  - apply lc_tm_arith; [apply IHt1 with (K:=K) (k:=k) | apply IHt2 with (K:=K) (k:=k)]; auto.
Qed.

Lemma lc_ty_open_close : forall K k T X,
  ~ In X (fv_ty T) ->
  lc_ty_at K (open_ty_rec k (Ty_FVar X) T) ->
  lc_ty_at (Nat.max K (S k)) T.
Proof.
  intros K k T. revert K k. induction T as [ n | a | T1 IHT1 T2 IHT2 | T1 IHT1 | ];
    intros K k X Hnin Hlc; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. apply lc_ty_bvar.
      apply Nat.lt_le_trans with (S k); [lia | pose proof (Nat.le_max_r K (S k)) as Hmax; exact Hmax].
    + inversion Hlc. subst.
      apply lc_ty_bvar. apply Nat.lt_le_trans with K; [assumption | pose proof (Nat.le_max_l K (S k)) as Hmax; exact Hmax].
  - apply lc_ty_fvar.
  - inversion Hlc; subst. apply lc_ty_arrow.
    + apply IHT1 with (K := K) (k := k) (X := X).
      * exact (notin_app_l _ _ _ Hnin).
      * assumption.
    + apply IHT2 with (K := K) (k := k) (X := X).
      * exact (notin_app_r _ _ _ Hnin).
      * assumption.
  - inversion Hlc; subst.
    match goal with
    | Hp : lc_ty_at (S K) (open_ty_rec (S k) (Ty_FVar X) T1) |- _ =>
        assert (H := IHT1 (S K) (S k) X Hnin Hp)
    end.
    rewrite <- Nat.succ_max_distr in H.
    apply lc_ty_all. exact H.
  - apply lc_ty_int.
Qed.

Lemma lc_tm_open_close : forall K kt k t x,
  ~ In x (fv_tm t) ->
  lc_tm_at K kt (open_tm_rec k (tm_fvar x) t) ->
  lc_tm_at K (Nat.max kt (S k)) t.
Proof.
  intros K kt k t. revert K kt k.
  induction t as [ i | y | T0 t1 IHt1 | t1 IHt1 t2 IHt2 | t1 IHt1 | t1 IHt1 T0 | z | t1 IHt1 t2 IHt2 | op t1 IHt1 t2 IHt2 ];
    intros K kt k x Hnin Hlc; simpl in *.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst i. apply lc_tm_bvar.
      apply Nat.lt_le_trans with (S k); [lia | pose proof (Nat.le_max_r kt (S k)) as Hmax; exact Hmax].
    + inversion Hlc; subst. apply lc_tm_bvar.
      apply Nat.lt_le_trans with kt; [assumption | pose proof (Nat.le_max_l kt (S k)) as Hmax; exact Hmax].
  - apply lc_tm_fvar.
  - inversion Hlc; subst. apply lc_tm_abs.
    + assumption.
    + rewrite Nat.succ_max_distr.
      apply IHt1 with (K := K) (kt := S kt) (k := S k) (x := x);
        [exact Hnin | assumption].
  - inversion Hlc; subst. apply lc_tm_app.
    + apply IHt1 with (K := K) (kt := kt) (k := k) (x := x);
        [exact (notin_app_l _ _ _ Hnin) | assumption].
    + apply IHt2 with (K := K) (kt := kt) (k := k) (x := x);
        [exact (notin_app_r _ _ _ Hnin) | assumption].
  - inversion Hlc; subst. apply lc_tm_tabs.
    apply IHt1 with (K := S K) (kt := kt) (k := k) (x := x); [exact Hnin | assumption].
  - inversion Hlc; subst. apply lc_tm_tapp.
    + apply IHt1 with (K := K) (kt := kt) (k := k) (x := x);
        [exact Hnin | assumption].
    + assumption.
  - apply lc_tm_int.
  - inversion Hlc; subst. apply lc_tm_div.
    + apply IHt1 with (K := K) (kt := kt) (k := k) (x := x);
        [exact (notin_app_l _ _ _ Hnin) | assumption].
    + apply IHt2 with (K := K) (kt := kt) (k := k) (x := x);
        [exact (notin_app_r _ _ _ Hnin) | assumption].
  - inversion Hlc; subst. apply lc_tm_arith.
    + apply IHt1 with (K := K) (kt := kt) (k := k) (x := x);
        [exact (notin_app_l _ _ _ Hnin) | assumption].
    + apply IHt2 with (K := K) (kt := kt) (k := k) (x := x);
        [exact (notin_app_r _ _ _ Hnin) | assumption].
Qed.

Lemma lc_tm_ty_open_close : forall K kt k t X,
  ~ In X (ftv_tm t) ->
  lc_tm_at K kt (open_tm_ty_rec k (Ty_FVar X) t) ->
  lc_tm_at (Nat.max K (S k)) kt t.
Proof.
  intros K kt k t. revert K kt k.
  induction t as [ i | y | T0 t1 IHt1 | t1 IHt1 t2 IHt2 | t1 IHt1 | t1 IHt1 T0 | z | t1 IHt1 t2 IHt2 | op t1 IHt1 t2 IHt2 ];
    intros K kt k X Hnin Hlc; simpl in *.
  - inversion Hlc; subst. apply lc_tm_bvar. assumption.
  - apply lc_tm_fvar.
  - inversion Hlc; subst. apply lc_tm_abs.
    + apply lc_ty_open_close with (K := K) (k := k) (X := X);
        [exact (notin_app_l _ _ _ Hnin) | assumption].
    + apply IHt1 with (K := K) (kt := S kt) (k := k) (X := X);
        [exact (notin_app_r _ _ _ Hnin) | assumption].
  - inversion Hlc; subst. apply lc_tm_app.
    + apply IHt1 with (K := K) (kt := kt) (k := k) (X := X);
        [exact (notin_app_l _ _ _ Hnin) | assumption].
    + apply IHt2 with (K := K) (kt := kt) (k := k) (X := X);
        [exact (notin_app_r _ _ _ Hnin) | assumption].
  - inversion Hlc; subst. apply lc_tm_tabs.
    rewrite Nat.succ_max_distr.
    apply IHt1 with (K := S K) (kt := kt) (k := S k) (X := X); [exact Hnin | assumption].
  - inversion Hlc; subst. apply lc_tm_tapp.
    + apply IHt1 with (K := K) (kt := kt) (k := k) (X := X);
        [exact (notin_app_l _ _ _ Hnin) | assumption].
    + apply lc_ty_open_close with (K := K) (k := k) (X := X);
        [exact (notin_app_r _ _ _ Hnin) | assumption].
  - apply lc_tm_int.
  - inversion Hlc; subst. apply lc_tm_div.
    + apply IHt1 with (K := K) (kt := kt) (k := k) (X := X);
        [exact (notin_app_l _ _ _ Hnin) | assumption].
    + apply IHt2 with (K := K) (kt := kt) (k := k) (X := X);
        [exact (notin_app_r _ _ _ Hnin) | assumption].
  - inversion Hlc; subst. apply lc_tm_arith.
    + apply IHt1 with (K := K) (kt := kt) (k := k) (X := X);
        [exact (notin_app_l _ _ _ Hnin) | assumption].
    + apply IHt2 with (K := K) (kt := kt) (k := k) (X := X);
        [exact (notin_app_r _ _ _ Hnin) | assumption].
Qed.

Lemma lc_pred_tm_open_close : forall K kt k p x,
  ~ In x (fv_q p) ->
  lc_pred_at K kt (open_pred_tm_rec k (tm_fvar x) p) ->
  lc_pred_at K (Nat.max kt (S k)) p.
Proof.
  intros K kt k p. revert K kt k.
  induction p as [ | | t1 t2 | t1 t2 | t1 t2 | p1 IHp1 p2 IHp2 | p1 IHp1 p2 IHp2 | p1 IHp1 ];
    intros K kt k x Hnin Hlc; simpl in *.
  - apply LCP_True.
  - apply LCP_False.
  - inversion Hlc; subst. apply LCP_Eq.
    + apply lc_tm_open_close with (K := K) (kt := kt) (k := k) (x := x);
        [exact (notin_app_l _ _ _ Hnin) | assumption].
    + apply lc_tm_open_close with (K := K) (kt := kt) (k := k) (x := x);
        [exact (notin_app_r _ _ _ Hnin) | assumption].
  - inversion Hlc; subst. apply LCP_Lt.
    + apply lc_tm_open_close with (K := K) (kt := kt) (k := k) (x := x);
        [exact (notin_app_l _ _ _ Hnin) | assumption].
    + apply lc_tm_open_close with (K := K) (kt := kt) (k := k) (x := x);
        [exact (notin_app_r _ _ _ Hnin) | assumption].
  - inversion Hlc; subst. apply LCP_Le.
    + apply lc_tm_open_close with (K := K) (kt := kt) (k := k) (x := x);
        [exact (notin_app_l _ _ _ Hnin) | assumption].
    + apply lc_tm_open_close with (K := K) (kt := kt) (k := k) (x := x);
        [exact (notin_app_r _ _ _ Hnin) | assumption].
  - inversion Hlc; subst. apply LCP_And.
    + apply IHp1 with (K := K) (kt := kt) (k := k) (x := x);
        [exact (notin_app_l _ _ _ Hnin) | assumption].
    + apply IHp2 with (K := K) (kt := kt) (k := k) (x := x);
        [exact (notin_app_r _ _ _ Hnin) | assumption].
  - inversion Hlc; subst. apply LCP_Or.
    + apply IHp1 with (K := K) (kt := kt) (k := k) (x := x);
        [exact (notin_app_l _ _ _ Hnin) | assumption].
    + apply IHp2 with (K := K) (kt := kt) (k := k) (x := x);
        [exact (notin_app_r _ _ _ Hnin) | assumption].
  - inversion Hlc; subst. apply LCP_Not.
    apply IHp1 with (K := K) (kt := kt) (k := k) (x := x); [exact Hnin | assumption].
Qed.

Lemma lc_pred_ty_open_close : forall K kt k p X,
  ~ In X (ftv_q p) ->
  lc_pred_at K kt (open_pred_ty_rec k (Ty_FVar X) p) ->
  lc_pred_at (Nat.max K (S k)) kt p.
Proof.
  intros K kt k p. revert K kt k.
  induction p as [ | | t1 t2 | t1 t2 | t1 t2 | p1 IHp1 p2 IHp2 | p1 IHp1 p2 IHp2 | p1 IHp1 ];
    intros K kt k X Hnin Hlc; simpl in *.
  - apply LCP_True.
  - apply LCP_False.
  - inversion Hlc; subst. apply LCP_Eq.
    + apply lc_tm_ty_open_close with (K := K) (kt := kt) (k := k) (X := X);
        [exact (notin_app_l _ _ _ Hnin) | assumption].
    + apply lc_tm_ty_open_close with (K := K) (kt := kt) (k := k) (X := X);
        [exact (notin_app_r _ _ _ Hnin) | assumption].
  - inversion Hlc; subst. apply LCP_Lt.
    + apply lc_tm_ty_open_close with (K := K) (kt := kt) (k := k) (X := X);
        [exact (notin_app_l _ _ _ Hnin) | assumption].
    + apply lc_tm_ty_open_close with (K := K) (kt := kt) (k := k) (X := X);
        [exact (notin_app_r _ _ _ Hnin) | assumption].
  - inversion Hlc; subst. apply LCP_Le.
    + apply lc_tm_ty_open_close with (K := K) (kt := kt) (k := k) (X := X);
        [exact (notin_app_l _ _ _ Hnin) | assumption].
    + apply lc_tm_ty_open_close with (K := K) (kt := kt) (k := k) (X := X);
        [exact (notin_app_r _ _ _ Hnin) | assumption].
  - inversion Hlc; subst. apply LCP_And.
    + apply IHp1 with (K := K) (kt := kt) (k := k) (X := X);
        [exact (notin_app_l _ _ _ Hnin) | assumption].
    + apply IHp2 with (K := K) (kt := kt) (k := k) (X := X);
        [exact (notin_app_r _ _ _ Hnin) | assumption].
  - inversion Hlc; subst. apply LCP_Or.
    + apply IHp1 with (K := K) (kt := kt) (k := k) (X := X);
        [exact (notin_app_l _ _ _ Hnin) | assumption].
    + apply IHp2 with (K := K) (kt := kt) (k := k) (X := X);
        [exact (notin_app_r _ _ _ Hnin) | assumption].
  - inversion Hlc; subst. apply LCP_Not.
    apply IHp1 with (K := K) (kt := kt) (k := k) (X := X); [exact Hnin | assumption].
Qed.

Lemma lc_rty_tm_open_close : forall K k ktm R x,
  ~ In x (fv_r R) ->
  lc_rty_at K k (open_rty_tm_rec ktm (tm_fvar x) R) ->
  lc_rty_at K (Nat.max k (S ktm)) R.
Proof.
  intros K k ktm R. revert K k ktm.
  induction R as [ T0 p0 | R1 IHR1 R2 IHR2 | R1 IHR1 R2 IHR2 | R1 IHR1 ];
    intros K k ktm x Hnin Hlc; simpl in *.
  - unfold open_qualifier_tm_rec in Hlc.
    inversion Hlc; subst. apply LCR_Refine.
    + assumption.
    + rewrite Nat.succ_max_distr.
      apply lc_pred_tm_open_close with (K := K) (kt := S k) (k := S ktm) (x := x);
        [exact Hnin | assumption].
  - inversion Hlc; subst. apply LCR_Func.
    + apply IHR1 with (K := K) (k := k) (ktm := ktm) (x := x);
        [exact (notin_app_l _ _ _ Hnin) | assumption].
    + rewrite Nat.succ_max_distr.
      apply IHR2 with (K := K) (k := S k) (ktm := S ktm) (x := x);
        [exact (notin_app_r _ _ _ Hnin) | assumption].
  - inversion Hlc; subst. apply LCR_Exists.
    + apply IHR1 with (K := K) (k := k) (ktm := ktm) (x := x);
        [exact (notin_app_l _ _ _ Hnin) | assumption].
    + rewrite Nat.succ_max_distr.
      apply IHR2 with (K := K) (k := S k) (ktm := S ktm) (x := x);
        [exact (notin_app_r _ _ _ Hnin) | assumption].
  - inversion Hlc; subst. apply LCR_Poly.
    apply IHR1 with (K := S K) (k := k) (ktm := ktm) (x := x); [exact Hnin | assumption].
Qed.

Lemma lc_rty_ty_open_close : forall K k kty R X,
  ~ In X (ftv_r R) ->
  lc_rty_at K k (open_rty_ty_rec kty (Ty_FVar X) R) ->
  lc_rty_at (Nat.max K (S kty)) k R.
Proof.
  intros K k kty R. revert K k kty.
  induction R as [ T0 p0 | R1 IHR1 R2 IHR2 | R1 IHR1 R2 IHR2 | R1 IHR1 ];
    intros K k kty X Hnin Hlc; simpl in *.
  - unfold open_qualifier_ty_rec in Hlc.
    inversion Hlc; subst. apply LCR_Refine.
    + apply lc_ty_open_close with (K := K) (k := kty) (X := X);
        [exact (notin_app_l _ _ _ Hnin) | assumption].
    + apply lc_pred_ty_open_close with (K := K) (kt := S k) (k := kty) (X := X);
        [exact (notin_app_r _ _ _ Hnin) | assumption].
  - inversion Hlc; subst. apply LCR_Func.
    + apply IHR1 with (K := K) (k := k) (kty := kty) (X := X);
        [exact (notin_app_l _ _ _ Hnin) | assumption].
    + apply IHR2 with (K := K) (k := S k) (kty := kty) (X := X);
        [exact (notin_app_r _ _ _ Hnin) | assumption].
  - inversion Hlc; subst. apply LCR_Exists.
    + apply IHR1 with (K := K) (k := k) (kty := kty) (X := X);
        [exact (notin_app_l _ _ _ Hnin) | assumption].
    + apply IHR2 with (K := K) (k := S k) (kty := kty) (X := X);
        [exact (notin_app_r _ _ _ Hnin) | assumption].
  - inversion Hlc; subst. apply LCR_Poly.
    rewrite Nat.succ_max_distr.
    apply IHR1 with (K := S K) (k := k) (kty := S kty) (X := X); [exact Hnin | assumption].
Qed.

(* ===== well-formedness implies locally closed ===== *)

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T H. induction H as [ Delta0 X Hin
    | Delta0 T1 T2 H1 IH1 H2 IH2
    | L Delta0 T Hbody IHbody
    | Delta0 ].
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; auto.
  - apply lc_ty_all.
    pose proof (lc_ty_open_close 0 0 T (fresh (L ++ fv_ty T))
                  (notin_app_r _ _ _ (fresh_notin _))
                  (IHbody (fresh (L ++ fv_ty T)) (notin_app_l _ _ _ (fresh_notin _)))) as H.
    simpl in H. exact H.
  - apply lc_ty_int.
Qed.

Lemma lc_ty_erase_gen : forall R K k, lc_rty_at K k R -> lc_ty_at K (erase R).
Proof.
  intros R. induction R as [ T0 p0 | R1 IHR1 R2 IHR2 | R1 IHR1 R2 IHR2 | R1 IHR1 ];
    intros K k Hlc; inversion Hlc; subst; simpl.
  - assumption.
  - apply lc_ty_arrow.
    + apply (IHR1 K k). assumption.
    + apply (IHR2 K (S k)). assumption.
  - apply (IHR2 K (S k)). assumption.
  - apply lc_ty_all. apply (IHR1 (S K) k). assumption.
Qed.

Lemma lc_ty_erase : forall R, locally_closed_rty R -> locally_closed_ty (erase R).
Proof. intros R H. apply (lc_ty_erase_gen R 0 0); auto. Qed.

Lemma has_type_lc : forall Delta Gamma t T, has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T H. induction H as [ Delta0 Gamma0 x T0 Hlk Hwf
    | L Delta0 Gamma0 T1 t2 T2 Hwf Hbody IHbody
    | Delta0 Gamma0 t1 t2 T1 T2 H1 IH1 H2 IH2
    | L Delta0 Gamma0 t T0 Hbody IHbody
    | Delta0 Gamma0 t T0 U H1 IH1 Hwf
    | Delta0 Gamma0 n
    | Delta0 Gamma0 t1 t2 H1 IH1 H2 IH2
    | Delta0 Gamma0 op t1 t2 H1 IH1 H2 IH2 ].
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + exact (wf_ty_lc Delta0 T1 Hwf).
    + pose proof (lc_tm_open_close 0 0 0 t2 (fresh (L ++ fv_tm t2))
                    (notin_app_r _ _ _ (fresh_notin _))
                    (IHbody (fresh (L ++ fv_tm t2)) (notin_app_l _ _ _ (fresh_notin _)))) as H.
      simpl in H. exact H.
  - apply lc_tm_app; auto.
  - apply lc_tm_tabs.
    pose proof (lc_tm_ty_open_close 0 0 0 t (fresh (L ++ ftv_tm t))
                  (notin_app_r _ _ _ (fresh_notin _))
                  (IHbody (fresh (L ++ ftv_tm t)) (notin_app_l _ _ _ (fresh_notin _)))) as H.
    simpl in H. exact H.
  - apply lc_tm_tapp; auto. exact (wf_ty_lc Delta0 U Hwf).
  - apply lc_tm_int.
  - apply lc_tm_div; auto.
  - apply lc_tm_arith; auto.
Qed.

Lemma predicate_wf_lc : forall Delta Gamma p, predicate_wf Delta Gamma p -> lc_pred_at 0 0 p.
Proof.
  intros Delta Gamma p H. induction H as [ Delta0 Gamma0
    | Delta0 Gamma0
    | Delta0 Gamma0 t1 t2 T0 H1 H2
    | Delta0 Gamma0 t1 t2 H1 H2
    | Delta0 Gamma0 t1 t2 H1 H2
    | Delta0 Gamma0 p1 p2 H1 IH1 H2 IH2
    | Delta0 Gamma0 p1 p2 H1 IH1 H2 IH2
    | Delta0 Gamma0 p H IH ].
  - apply LCP_True.
  - apply LCP_False.
  - apply LCP_Eq; [exact (has_type_lc _ _ _ _ H1) | exact (has_type_lc _ _ _ _ H2)].
  - apply LCP_Lt; [exact (has_type_lc _ _ _ _ H1) | exact (has_type_lc _ _ _ _ H2)].
  - apply LCP_Le; [exact (has_type_lc _ _ _ _ H1) | exact (has_type_lc _ _ _ _ H2)].
  - apply LCP_And; auto.
  - apply LCP_Or; auto.
  - apply LCP_Not; auto.
Qed.

Lemma wf_rty_lc : forall Delta RGamma R, wf_rty Delta RGamma R -> locally_closed_rty R.
Proof.
  intros Delta RGamma R H. induction H as [ L Delta0 RGamma0 T ps Hwf Hq
    | L Delta0 RGamma0 R1 R2 H1 IH1 H2 IH2
    | L Delta0 RGamma0 R1 R2 H1 IH1 H2 IH2
    | L Delta0 RGamma0 R Hbody IHbody ].
  - unfold locally_closed_rty. apply LCR_Refine.
    + exact (wf_ty_lc Delta0 T Hwf).
    + pose proof (predicate_wf_lc _ _ _
                    (Hq (fresh (L ++ fv_q ps)) (notin_app_l _ _ _ (fresh_notin _)))) as Hp.
      unfold qualifier_wf in Hp. unfold open_qualifier_tm in Hp.
      pose proof (lc_pred_tm_open_close 0 0 0 ps (fresh (L ++ fv_q ps))
                    (notin_app_r _ _ _ (fresh_notin _)) Hp) as H.
      simpl in H. exact H.
  - unfold locally_closed_rty. apply LCR_Func.
    + unfold locally_closed_rty in IH1. exact IH1.
    + pose proof (IH2 (fresh (L ++ fv_r R2)) (notin_app_l _ _ _ (fresh_notin _))) as Hlc.
      unfold locally_closed_rty in Hlc. unfold open_rty_tm in Hlc.
      pose proof (lc_rty_tm_open_close 0 0 0 R2 (fresh (L ++ fv_r R2))
                    (notin_app_r _ _ _ (fresh_notin _)) Hlc) as H.
      simpl in H. exact H.
  - unfold locally_closed_rty. apply LCR_Exists.
    + unfold locally_closed_rty in IH1. exact IH1.
    + pose proof (IH2 (fresh (L ++ fv_r R2)) (notin_app_l _ _ _ (fresh_notin _))) as Hlc.
      unfold locally_closed_rty in Hlc. unfold open_rty_tm in Hlc.
      pose proof (lc_rty_tm_open_close 0 0 0 R2 (fresh (L ++ fv_r R2))
                    (notin_app_r _ _ _ (fresh_notin _)) Hlc) as H.
      simpl in H. exact H.
  - unfold locally_closed_rty. apply LCR_Poly.
    pose proof (IHbody (fresh (L ++ ftv_r R)) (notin_app_l _ _ _ (fresh_notin _))) as Hlc.
    unfold locally_closed_rty in Hlc. unfold open_rty_ty in Hlc.
    pose proof (lc_rty_ty_open_close 0 0 0 R (fresh (L ++ ftv_r R))
                  (notin_app_r _ _ _ (fresh_notin _)) Hlc) as H.
    simpl in H. exact H.
Qed.

Lemma has_rtype_lc : forall Delta RGamma t R, has_rtype Delta RGamma t R -> locally_closed_tm t.
Proof.
  intros Delta RGamma t R H. induction H as [ Delta0 RGamma0 x R0 Hlk Hwf
    | L Delta0 RGamma0 R1 body R2 Hwf Hbody IHbody
    | Delta0 RGamma0 t1 t2 R1 R2 H1 IH1 H2 IH2
    | L Delta0 RGamma0 body R0 Hbody IHbody
    | Delta0 RGamma0 t R0 U H1 IH1 Hwf
    | Delta0 RGamma0 n
    | Delta0 RGamma0 t1 t2 H1 IH1 H2 IH2
    | Delta0 RGamma0 op t1 t2 H1 IH1 H2 IH2
    | Delta0 RGamma0 v T0 ps Hty Hval Hwf Hpc Hqh
    | Delta0 RGamma0 t R0 S0 H1 IH1 Hwf Hsub ].
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + apply lc_ty_erase. exact (wf_rty_lc Delta0 RGamma0 R1 Hwf).
    + pose proof (lc_tm_open_close 0 0 0 body (fresh (L ++ fv_tm body))
                    (notin_app_r _ _ _ (fresh_notin _))
                    (IHbody (fresh (L ++ fv_tm body)) (notin_app_l _ _ _ (fresh_notin _)))) as H.
      simpl in H. exact H.
  - apply lc_tm_app; auto.
  - apply lc_tm_tabs.
    pose proof (lc_tm_ty_open_close 0 0 0 body (fresh (L ++ ftv_tm body))
                  (notin_app_r _ _ _ (fresh_notin _))
                  (IHbody (fresh (L ++ ftv_tm body)) (notin_app_l _ _ _ (fresh_notin _)))) as H.
    simpl in H. exact H.
  - apply lc_tm_tapp; auto. exact (wf_ty_lc Delta0 U Hwf).
  - apply lc_tm_int.
  - apply lc_tm_div; auto.
  - apply lc_tm_arith; auto.
  - apply has_type_lc in Hty. exact Hty.
  - exact IH1.
Qed.

(* ===== substitution preserves locally closed ===== *)

Lemma lc_ty_tsubst : forall K T σ, lc_ty_at K T -> lc_tenv σ -> lc_ty_at K (ty_tsubst σ T).
Proof.
  intros K T. revert K. induction T as [ n | a | T1 IHT1 T2 IHT2 | T1 IHT1 | ];
    intros K σ Hlc Hσ; inversion Hlc; subst; simpl.
  - apply lc_ty_bvar. auto.
  - exact (lc_ty_at_mono 0 K (σ a) (Hσ a) (Nat.le_0_l K)).
  - apply lc_ty_arrow; auto.
  - apply lc_ty_all. apply IHT1 with (K := S K); auto.
  - apply lc_ty_int.
Qed.

Lemma lc_tm_tsubst : forall K k t σ, lc_tm_at K k t -> lc_tenv σ -> lc_tm_at K k (tm_tsubst σ t).
Proof.
  intros K k t. revert K k.
  induction t as [ i | x | T0 t1 IHt1 | t1 IHt1 t2 IHt2 | t1 IHt1 | t1 IHt1 T0 | z | t1 IHt1 t2 IHt2 | op t1 IHt1 t2 IHt2 ];
    intros K k σ Hlc Hσ; inversion Hlc; subst; simpl.
  - apply lc_tm_bvar. auto.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + apply lc_ty_tsubst with (K := K); auto.
    + apply IHt1 with (K := K) (k := S k); auto.
  - apply lc_tm_app; auto.
  - apply lc_tm_tabs. apply IHt1 with (K := S K) (k := k); auto.
  - apply lc_tm_tapp.
    + apply IHt1 with (K := K) (k := k); auto.
    + apply lc_ty_tsubst with (K := K); auto.
  - apply lc_tm_int.
  - apply lc_tm_div; auto.
  - apply lc_tm_arith; auto.
Qed.

Lemma lc_tm_msubst : forall K k t ρ, lc_tm_at K k t -> lc_menv ρ -> lc_tm_at K k (tm_msubst ρ t).
Proof.
  intros K k t. revert K k.
  induction t as [ i | x | T0 t1 IHt1 | t1 IHt1 t2 IHt2 | t1 IHt1 | t1 IHt1 T0 | z | t1 IHt1 t2 IHt2 | op t1 IHt1 t2 IHt2 ];
    intros K k ρ Hlc Hρ; inversion Hlc; subst; simpl.
  - apply lc_tm_bvar. auto.
  - exact (lc_tm_at_mono 0 0 K k (ρ x) (Hρ x) (Nat.le_0_l K) (Nat.le_0_l k)).
  - apply lc_tm_abs.
    + assumption.
    + apply IHt1 with (K := K) (k := S k); auto.
  - apply lc_tm_app; auto.
  - apply lc_tm_tabs. apply IHt1 with (K := S K) (k := k); auto.
  - apply lc_tm_tapp; auto.
  - apply lc_tm_int.
  - apply lc_tm_div; auto.
  - apply lc_tm_arith; auto.
Qed.

Lemma lc_tm_subst_all : forall K k t ρ σ,
  lc_tm_at K k t -> lc_menv ρ -> lc_tenv σ -> lc_tm_at K k (tm_subst_all ρ σ t).
Proof.
  intros. unfold tm_subst_all.
  apply lc_tm_msubst; auto.
  apply lc_tm_tsubst; auto.
Qed.

(* ===== opening preserves locally closed ===== *)

Lemma lc_ty_open_lc_gen : forall T kty U,
  lc_ty_at (S kty) T -> locally_closed_ty U -> lc_ty_at kty (open_ty_rec kty U T).
Proof.
  intros T. induction T as [ n | a | T1 IHT1 T2 IHT2 | T1 IHT1 | ];
    intros kty U Hlc HU; simpl.
  - destruct (Nat.eqb kty n) eqn:E.
    + apply Nat.eqb_eq in E. subst n.
      exact (lc_ty_at_mono 0 kty U HU (Nat.le_0_l kty)).
    + apply Nat.eqb_neq in E. inversion Hlc; subst. apply lc_ty_bvar. lia.
  - apply lc_ty_fvar.
  - inversion Hlc; subst. apply lc_ty_arrow.
    + apply IHT1 with (kty := kty); auto.
    + apply IHT2 with (kty := kty); auto.
  - inversion Hlc; subst. apply lc_ty_all.
    apply IHT1 with (kty := S kty); auto.
  - apply lc_ty_int.
Qed.

Lemma lc_tm_ty_open_lc_gen : forall t kty k U,
  lc_tm_at (S kty) k t -> locally_closed_ty U -> lc_tm_at kty k (open_tm_ty_rec kty U t).
Proof.
  intros t. induction t as [ i | x | T0 t1 IHt1 | t1 IHt1 t2 IHt2 | t1 IHt1 | t1 IHt1 T0 | z | t1 IHt1 t2 IHt2 | op t1 IHt1 t2 IHt2 ];
    intros kty k U Hlc HU; simpl.
  - inversion Hlc; subst. apply lc_tm_bvar. auto.
  - apply lc_tm_fvar.
  - inversion Hlc; subst. apply lc_tm_abs.
    + apply lc_ty_open_lc_gen with (kty := kty); auto.
    + apply IHt1 with (kty := kty) (k := S k); auto.
  - inversion Hlc; subst. apply lc_tm_app.
    + apply IHt1 with (kty := kty) (k := k); auto.
    + apply IHt2 with (kty := kty) (k := k); auto.
  - inversion Hlc; subst. apply lc_tm_tabs.
    apply IHt1 with (kty := S kty) (k := k); auto.
  - inversion Hlc; subst. apply lc_tm_tapp.
    + apply IHt1 with (kty := kty) (k := k); auto.
    + apply lc_ty_open_lc_gen with (kty := kty); auto.
  - apply lc_tm_int.
  - inversion Hlc; subst. apply lc_tm_div.
    + apply IHt1 with (kty := kty) (k := k); auto.
    + apply IHt2 with (kty := kty) (k := k); auto.
  - inversion Hlc; subst. apply lc_tm_arith.
    + apply IHt1 with (kty := kty) (k := k); auto.
    + apply IHt2 with (kty := kty) (k := k); auto.
Qed.

Lemma lc_tm_open_lc_gen : forall t K k u,
  lc_tm_at K (S k) t -> lc_tm_at K k u -> lc_tm_at K k (open_tm_rec k u t).
Proof.
  intros t. induction t as [ i | x | T0 t1 IHt1 | t1 IHt1 t2 IHt2 | t1 IHt1 | t1 IHt1 T0 | z | t1 IHt1 t2 IHt2 | op t1 IHt1 t2 IHt2 ];
    intros K k u Hlc Hu; simpl.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst i. exact Hu.
    + apply Nat.eqb_neq in E. inversion Hlc; subst. apply lc_tm_bvar. lia.
  - apply lc_tm_fvar.
  - inversion Hlc; subst. apply lc_tm_abs.
    + assumption.
    + apply IHt1 with (K := K) (k := S k).
      * assumption.
      * exact (lc_tm_at_mono K k K (S k) u Hu (Nat.le_refl K) (Nat.le_succ_diag_r k)).
  - inversion Hlc; subst. apply lc_tm_app.
    + apply IHt1 with (K := K) (k := k); auto.
    + apply IHt2 with (K := K) (k := k); auto.
  - inversion Hlc; subst. apply lc_tm_tabs.
    apply IHt1 with (K := S K) (k := k); auto.
    exact (lc_tm_at_mono K k (S K) k u Hu (Nat.le_succ_diag_r K) (Nat.le_refl k)).
  - inversion Hlc; subst. apply lc_tm_tapp.
    + apply IHt1 with (K := K) (k := k); auto.
    + assumption.
  - apply lc_tm_int.
  - inversion Hlc; subst. apply lc_tm_div.
    + apply IHt1 with (K := K) (k := k); auto.
    + apply IHt2 with (K := K) (k := k); auto.
  - inversion Hlc; subst. apply lc_tm_arith.
    + apply IHt1 with (K := K) (k := k); auto.
    + apply IHt2 with (K := K) (k := k); auto.
Qed.

(* ===== inversion helpers for locally closed terms and types ===== *)

Lemma lc_ty_arrow_inv : forall K T1 T2, lc_ty_at K (Ty_Arrow T1 T2) -> lc_ty_at K T1 /\ lc_ty_at K T2.
Proof. intros. inversion H. subst. auto. Qed.

Lemma lc_ty_all_inv : forall K T, lc_ty_at K (Ty_All T) -> lc_ty_at (S K) T.
Proof. intros. inversion H. subst. auto. Qed.

Lemma lc_tm_abs_inv : forall K k T t, lc_tm_at K k (tm_abs T t) -> lc_ty_at K T /\ lc_tm_at K (S k) t.
Proof. intros. inversion H. subst. auto. Qed.

Lemma lc_tm_app_inv : forall K k t1 t2, lc_tm_at K k (tm_app t1 t2) -> lc_tm_at K k t1 /\ lc_tm_at K k t2.
Proof. intros. inversion H. subst. auto. Qed.

Lemma lc_tm_tabs_inv : forall K k t, lc_tm_at K k (tm_tabs t) -> lc_tm_at (S K) k t.
Proof. intros. inversion H. subst. auto. Qed.

Lemma lc_tm_tapp_inv : forall K k t T, lc_tm_at K k (tm_tapp t T) -> lc_tm_at K k t /\ lc_ty_at K T.
Proof. intros. inversion H. subst. auto. Qed.

Lemma lc_tm_div_inv : forall K k t1 t2, lc_tm_at K k (tm_div t1 t2) -> lc_tm_at K k t1 /\ lc_tm_at K k t2.
Proof. intros. inversion H. subst. auto. Qed.

Lemma lc_tm_arith_inv : forall K k op t1 t2, lc_tm_at K k (tm_arith op t1 t2) -> lc_tm_at K k t1 /\ lc_tm_at K k t2.
Proof. intros. inversion H. subst. auto. Qed.

(* ===== values, multi-step, safety ===== *)

Lemma value_lc : forall v, value v -> locally_closed_tm v.
Proof. intros v H. destruct H; auto. apply lc_tm_int. Qed.

Lemma value_no_step : forall v u, value v -> step v u -> False.
Proof. intros v u Hv Hs. destruct Hv; inversion Hs. Qed.

Lemma multi_of_value : forall v u, value v -> multi v u -> u = v.
Proof.
  intros v u Hv Hm. induction Hm.
  - reflexivity.
  - exfalso. apply (value_no_step _ _ Hv H).
Qed.

Lemma multi_trans : forall a b c, multi a b -> multi b c -> multi a c.
Proof.
  intros a b c H1. induction H1 as [ x | x y z Hstep Htail IH ].
  - intros H2. exact H2.
  - intros H2. apply multi_step with (t2 := y); [exact Hstep | apply IH; exact H2].
Qed.

Lemma lc_step : forall t u, step t u -> locally_closed_tm t -> locally_closed_tm u.
Proof.
  intros t u Hstep. induction Hstep as
    [ T body v Hlcabs Hval
    | t1 t1' t2 Hst IH Hlc2
    | v1 t2 t2' Hval Hst IH
    | body T Hlcabs HlcT
    | t t' T Hst IH HlcT
    | t1 t1' t2 Hst IH Hlc2
    | v1 t2 t2' Hval Hst IH
    | n m Hneq
    | op t1 t1' t2 Hst IH Hlc2
    | op v1 t2 t2' Hval Hst IH
    | op n m ];
    intros Hlc.
  - destruct (lc_tm_app_inv _ _ _ _ Hlc) as [Hl1 Hl2].
    destruct (lc_tm_abs_inv _ _ _ _ Hl1) as [Hty Hbody].
    apply lc_tm_open_lc_gen with (K := 0) (k := 0); auto.
  - destruct (lc_tm_app_inv _ _ _ _ Hlc) as [Hl1 Hl2].
    apply lc_tm_app; [apply IH; exact Hl1 | exact Hl2].
  - destruct (lc_tm_app_inv _ _ _ _ Hlc) as [Hl1 Hl2].
    apply lc_tm_app; [apply value_lc; exact Hval | apply IH; exact Hl2].
  - destruct (lc_tm_tapp_inv _ _ _ _ Hlc) as [Hlt HlT].
    pose proof (lc_tm_tabs_inv _ _ _ Hlt) as Hbody.
    change (lc_tm_at 0 0 (open_tm_ty_rec 0 T body)).
    apply lc_tm_ty_open_lc_gen with (kty := 0) (k := 0); simpl; auto.
  - destruct (lc_tm_tapp_inv _ _ _ _ Hlc) as [Hlt HlT].
    apply lc_tm_tapp; [apply IH; exact Hlt | exact HlT].
  - destruct (lc_tm_div_inv _ _ _ _ Hlc) as [Hl1 Hl2].
    apply lc_tm_div; [apply IH; exact Hl1 | exact Hl2].
  - destruct (lc_tm_div_inv _ _ _ _ Hlc) as [Hl1 Hl2].
    apply lc_tm_div; [apply value_lc; exact Hval | apply IH; exact Hl2].
  - apply lc_tm_int.
  - destruct (lc_tm_arith_inv _ _ _ _ _ Hlc) as [Hl1 Hl2].
    apply lc_tm_arith; [apply IH; exact Hl1 | exact Hl2].
  - destruct (lc_tm_arith_inv _ _ _ _ _ Hlc) as [Hl1 Hl2].
    apply lc_tm_arith; [apply value_lc; exact Hval | apply IH; exact Hl2].
  - apply lc_tm_int.
Qed.

From Stdlib Require Import Arith.Wf_nat.

(* ============================================================ *)
(* Semantic types: fuel-indexed logical relation                 *)
(* ============================================================ *)

Fixpoint rty_nodes (R : rty) : nat :=
  match R with
  | R_Refine _ _ => 1
  | R_Func R1 R2 => 1 + rty_nodes R1 + rty_nodes R2
  | R_Exists R1 R2 => 1 + rty_nodes R1 + rty_nodes R2
  | R_Poly R1 => 1 + rty_nodes R1
  end.

Lemma rty_nodes_ge1 : forall R, 1 <= rty_nodes R.
Proof. intros R. destruct R; simpl; lia. Qed.

Lemma rty_nodes_open_rty_tm_rec : forall k u R,
  rty_nodes (open_rty_tm_rec k u R) = rty_nodes R.
Proof.
  intros k u R. revert k u.
  induction R as [ T0 p0 | R1 IHR1 R2 IHR2 | R1 IHR1 R2 IHR2 | R1 IHR1 ];
    intros k u; simpl.
  - reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR1. reflexivity.
Qed.

Lemma rty_nodes_open_rty_ty_rec : forall k U R,
  rty_nodes (open_rty_ty_rec k U R) = rty_nodes R.
Proof.
  intros k U R. revert k U.
  induction R as [ T0 p0 | R1 IHR1 R2 IHR2 | R1 IHR1 R2 IHR2 | R1 IHR1 ];
    intros k U; simpl.
  - reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR1. reflexivity.
Qed.

Lemma rty_nodes_open_rty_tm : forall R u,
  rty_nodes (open_rty_tm R u) = rty_nodes R.
Proof. intros. apply rty_nodes_open_rty_tm_rec. Qed.

Lemma rty_nodes_open_rty_ty : forall R U,
  rty_nodes (open_rty_ty R U) = rty_nodes R.
Proof. intros. apply rty_nodes_open_rty_ty_rec. Qed.

Lemma rty_nodes_r_tsubst : forall σ R, rty_nodes (r_tsubst σ R) = rty_nodes R.
Proof.
  intros σ R. revert σ.
  induction R as [ T0 p0 | R1 IHR1 R2 IHR2 | R1 IHR1 R2 IHR2 | R1 IHR1 ];
    intros σ; simpl.
  - reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR1. reflexivity.
Qed.

Lemma rty_nodes_r_msubst : forall ρ R, rty_nodes (r_msubst ρ R) = rty_nodes R.
Proof.
  intros ρ R. revert ρ.
  induction R as [ T0 p0 | R1 IHR1 R2 IHR2 | R1 IHR1 R2 IHR2 | R1 IHR1 ];
    intros ρ; simpl.
  - reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR1. reflexivity.
Qed.

Lemma rty_nodes_r_subst_all : forall ρ σ R,
  rty_nodes (r_subst_all ρ σ R) = rty_nodes R.
Proof.
  intros. unfold r_subst_all. rewrite rty_nodes_r_msubst, rty_nodes_r_tsubst. reflexivity.
Qed.

Lemma rty_nodes_open_rty_tm_le : forall R u n,
  rty_nodes R <= n -> rty_nodes (open_rty_tm R u) <= n.
Proof.
  intros. apply Nat.le_trans with (m := rty_nodes R);
    [apply Nat.eq_le_incl; apply rty_nodes_open_rty_tm | auto].
Qed.

Lemma rty_nodes_open_rty_ty_le : forall R U n,
  rty_nodes R <= n -> rty_nodes (open_rty_ty R U) <= n.
Proof.
  intros. apply Nat.le_trans with (m := rty_nodes R);
    [apply Nat.eq_le_incl; apply rty_nodes_open_rty_ty | auto].
Qed.

Definition safe (t : tm) : Prop :=
  forall t', multi t t' -> value t' \/ exists t'', t' --> t''.

Fixpoint value_shape (T : ty) (v : tm) : Prop :=
  match T with
  | Ty_BVar _ => False
  | Ty_FVar _ => False
  | Ty_Arrow _ _ => exists T0 body, v = tm_abs T0 body
  | Ty_All _ => exists body, v = tm_tabs body
  | Ty_Int => exists n, v = tm_int n
  end.

Fixpoint semF (n : nat) (t : tm) (R : rty) {struct n} : Prop :=
  match n with
  | 0 => True
  | S n' =>
    locally_closed_tm t /\
    safe t /\
    match R with
    | R_Refine T p =>
        forall t', multi t t' -> value t' ->
          locally_closed_tm t' /\ value_shape T t' /\
          predicate_holds (open_pred_tm p t')
    | R_Func R1 R2 =>
        forall t', multi t t' -> value t' ->
          locally_closed_tm t' /\
          exists T0 body, t' = tm_abs T0 body /\
            locally_closed_tm (tm_abs T0 body) /\
            forall w, value w -> semF n' w R1 ->
              semF n' (open_tm body w) (open_rty_tm R2 w)
    | R_Exists R1 R2 =>
        forall t', multi t t' -> value t' ->
          locally_closed_tm t' /\
          exists w, value w /\ semF n' w R1 /\
            semF n' t' (open_rty_tm R2 w)
    | R_Poly R1 =>
        forall t', multi t t' -> value t' ->
          locally_closed_tm t' /\
          exists body, t' = tm_tabs body /\
            locally_closed_tm (tm_tabs body) /\
            forall U, locally_closed_ty U ->
              semF n' (open_tm_ty body U) (open_rty_ty R1 U)
    end
  end.

Definition sem (t : tm) (R : rty) : Prop := semF (rty_nodes R) t R.

Lemma semF_ext : forall n m (t : tm) (R : rty),
  rty_nodes R <= n -> rty_nodes R <= m -> (semF n t R <-> semF m t R).
Proof.
  intros n. induction n as [ n IH ] using lt_wf_ind.
  intros m t R Hn Hm.
  destruct n as [| n'].
  - destruct R; simpl in Hn; lia.
  - destruct m as [| m'].
    + destruct R; simpl in Hm; lia.
    + destruct R as [ T0 p0 | R1 R2 | R1 R2 | R1 ];
        simpl in *; simpl.
      * split.
        -- intros [Hlc [Hs Hv]]. split; [exact Hlc |]. split; [exact Hs |].
           intros r Hmu Hval. destruct (Hv r Hmu Hval) as [A [B C]]. repeat split; auto.
        -- intros [Hlc [Hs Hv]]. split; [exact Hlc |]. split; [exact Hs |].
           intros r Hmu Hval. destruct (Hv r Hmu Hval) as [A [B C]]. repeat split; auto.
      * assert (En1 : rty_nodes R1 <= n') by lia.
        assert (Em1 : rty_nodes R1 <= m') by lia.
        assert (En2 : rty_nodes R2 <= n') by lia.
        assert (Em2 : rty_nodes R2 <= m') by lia.
        split.
        -- intros [Hlc [Hs Hv]]. split; [exact Hlc |]. split; [exact Hs |].
           intros r Hmu Hval.
           destruct (Hv r Hmu Hval) as [Hlct [T1 [body [Heq [Hlca Hf]]]]].
           split; [exact Hlct |].
           exists T1, body. split; [exact Heq |]. split; [exact Hlca |].
           intros w Hw Hsw.
           assert (E1 : semF n' w R1 <-> semF m' w R1) by
             (apply (IH n' (Nat.lt_succ_diag_r n') m' w R1); auto).
           assert (E2 : semF n' (open_tm body w) (open_rty_tm R2 w) <->
                      semF m' (open_tm body w) (open_rty_tm R2 w)) by
             (apply (IH n' (Nat.lt_succ_diag_r n') m' (open_tm body w) (open_rty_tm R2 w));
              [apply rty_nodes_open_rty_tm_le; auto | apply rty_nodes_open_rty_tm_le; auto]).
           apply (proj1 E2). apply Hf; auto. apply (proj2 E1); auto.
        -- intros [Hlc [Hs Hv]]. split; [exact Hlc |]. split; [exact Hs |].
           intros r Hmu Hval.
           destruct (Hv r Hmu Hval) as [Hlct [T1 [body [Heq [Hlca Hf]]]]].
           split; [exact Hlct |].
           exists T1, body. split; [exact Heq |]. split; [exact Hlca |].
           intros w Hw Hsw.
           assert (E1 : semF n' w R1 <-> semF m' w R1) by
             (apply (IH n' (Nat.lt_succ_diag_r n') m' w R1); auto).
           assert (E2 : semF n' (open_tm body w) (open_rty_tm R2 w) <->
                      semF m' (open_tm body w) (open_rty_tm R2 w)) by
             (apply (IH n' (Nat.lt_succ_diag_r n') m' (open_tm body w) (open_rty_tm R2 w));
              [apply rty_nodes_open_rty_tm_le; auto | apply rty_nodes_open_rty_tm_le; auto]).
           apply (proj2 E2). apply Hf; auto. apply (proj1 E1); auto.
      * assert (En1 : rty_nodes R1 <= n') by lia.
        assert (Em1 : rty_nodes R1 <= m') by lia.
        assert (En2 : rty_nodes R2 <= n') by lia.
        assert (Em2 : rty_nodes R2 <= m') by lia.
        split.
        -- intros [Hlc [Hs Hv]]. split; [exact Hlc |]. split; [exact Hs |].
           intros r Hmu Hval.
           destruct (Hv r Hmu Hval) as [Hlct [w [Hw [Hs1 Hs2]]]].
           split; [exact Hlct |].
           exists w. split; [exact Hw |]. split.
           ++ assert (E1 : semF n' w R1 <-> semF m' w R1) by
                (apply (IH n' (Nat.lt_succ_diag_r n') m' w R1); auto).
              apply (proj1 E1); auto.
           ++ assert (E2 : semF n' r (open_rty_tm R2 w) <-> semF m' r (open_rty_tm R2 w)) by
                (apply (IH n' (Nat.lt_succ_diag_r n') m' r (open_rty_tm R2 w));
                 [apply rty_nodes_open_rty_tm_le; auto | apply rty_nodes_open_rty_tm_le; auto]).
              apply (proj1 E2). exact Hs2.
        -- intros [Hlc [Hs Hv]]. split; [exact Hlc |]. split; [exact Hs |].
           intros r Hmu Hval.
           destruct (Hv r Hmu Hval) as [Hlct [w [Hw [Hs1 Hs2]]]].
           split; [exact Hlct |].
           exists w. split; [exact Hw |]. split.
           ++ assert (E1 : semF n' w R1 <-> semF m' w R1) by
                (apply (IH n' (Nat.lt_succ_diag_r n') m' w R1); auto).
              apply (proj2 E1); auto.
           ++ assert (E2 : semF n' r (open_rty_tm R2 w) <-> semF m' r (open_rty_tm R2 w)) by
                (apply (IH n' (Nat.lt_succ_diag_r n') m' r (open_rty_tm R2 w));
                 [apply rty_nodes_open_rty_tm_le; auto | apply rty_nodes_open_rty_tm_le; auto]).
              apply (proj2 E2). exact Hs2.
      * assert (En1 : rty_nodes R1 <= n') by lia.
        assert (Em1 : rty_nodes R1 <= m') by lia.
        split.
        -- intros [Hlc [Hs Hv]]. split; [exact Hlc |]. split; [exact Hs |].
           intros r Hmu Hval.
           destruct (Hv r Hmu Hval) as [Hlct [body [Heq [Hlca Hf]]]].
           split; [exact Hlct |].
           exists body. split; [exact Heq |]. split; [exact Hlca |].
           intros U HU.
           assert (E : semF n' (open_tm_ty body U) (open_rty_ty R1 U) <->
                      semF m' (open_tm_ty body U) (open_rty_ty R1 U)) by
             (apply (IH n' (Nat.lt_succ_diag_r n') m' (open_tm_ty body U) (open_rty_ty R1 U));
              [apply rty_nodes_open_rty_ty_le; auto | apply rty_nodes_open_rty_ty_le; auto]).
           apply (proj1 E). apply Hf; auto.
        -- intros [Hlc [Hs Hv]]. split; [exact Hlc |]. split; [exact Hs |].
           intros r Hmu Hval.
           destruct (Hv r Hmu Hval) as [Hlct [body [Heq [Hlca Hf]]]].
           split; [exact Hlct |].
           exists body. split; [exact Heq |]. split; [exact Hlca |].
           intros U HU.
           assert (E : semF n' (open_tm_ty body U) (open_rty_ty R1 U) <->
                      semF m' (open_tm_ty body U) (open_rty_ty R1 U)) by
             (apply (IH n' (Nat.lt_succ_diag_r n') m' (open_tm_ty body U) (open_rty_ty R1 U));
              [apply rty_nodes_open_rty_ty_le; auto | apply rty_nodes_open_rty_ty_le; auto]).
           apply (proj2 E). apply Hf; auto.
Qed.

(* ============================================================ *)
(* Semantic lemmas: step closure, values, fuel conversions       *)
(* ============================================================ *)

Lemma semF_step : forall n t u R, step t u -> semF n t R -> semF n u R.
Proof.
  intros n t u R Hstep. destruct n as [| n'].
  - simpl. auto.
  - destruct R as [ T0 p0 | R1 R2 | R1 R2 | R1 ]; simpl; intros (Hlc & Hs & Hv);
      (split; [apply lc_step with t; auto |]);
      (split; [ intros r Hmu; apply Hs; eapply multi_step; eauto
              | intros r Hmu Hval; apply Hv; [eapply multi_step; eauto | auto] ]).
Qed.

Lemma sem_step : forall t u R, step t u -> sem t R -> sem u R.
Proof.
  intros t u R Hstep Hsem. unfold sem in *.
  eapply semF_step; eauto.
Qed.

Lemma safe_value : forall v, value v -> safe v.
Proof.
  intros v Hv r Hmu. left. rewrite (multi_of_value v r Hv Hmu). exact Hv.
Qed.

Lemma sem_to_semF : forall t R n, rty_nodes R <= n -> sem t R -> semF n t R.
Proof.
  intros t R n Hn Hsem. unfold sem in Hsem.
  exact (proj1 (semF_ext (rty_nodes R) n t R (Nat.le_refl _) Hn) Hsem).
Qed.

Lemma semF_to_sem : forall t R n, rty_nodes R <= n -> semF n t R -> sem t R.
Proof.
  intros t R n Hn Hsem. unfold sem.
  exact (proj2 (semF_ext (rty_nodes R) n t R (Nat.le_refl _) Hn) Hsem).
Qed.

(* Value semantics without fuel *)

Fixpoint valok (v : tm) (R : rty) : Prop :=
  locally_closed_tm v /\
  match R with
  | R_Refine T p =>
      value_shape T v /\ predicate_holds (open_pred_tm p v)
  | R_Func R1 R2 =>
      exists T0 body, v = tm_abs T0 body /\
        locally_closed_tm (tm_abs T0 body) /\
        forall w, value w -> valok w R1 ->
          sem (open_tm body w) (open_rty_tm R2 w)
  | R_Exists R1 R2 =>
      exists w, value w /\ valok w R1 /\
        sem v (open_rty_tm R2 w)
  | R_Poly R1 =>
      exists body, v = tm_tabs body /\
        locally_closed_tm (tm_tabs body) /\
        forall U, locally_closed_ty U ->
          sem (open_tm_ty body U) (open_rty_ty R1 U)
  end.

Lemma sem_valok : forall R,
  (forall v, value v -> valok v R -> sem v R) /\
  (forall v, value v -> sem v R -> valok v R).
Proof.
  induction R as [ T0 p0 | R1 IHR1 R2 IHR2 | R1 IHR1 R2 IHR2 | R1 IHR1 ].
  - split.
    + intros v Hv [Hlc [Hshape Hpred]]. unfold sem.
      change (semF 1 v (R_Refine T0 p0)). simpl.
      split; [exact Hlc |]. split; [apply safe_value; exact Hv |].
      intros r Hmu Hvalr. rewrite (multi_of_value v r Hv Hmu).
      repeat split; auto.
    + intros v Hv Hsem. unfold sem in Hsem.
      change (semF 1 v (R_Refine T0 p0)) in Hsem. simpl in Hsem.
      destruct Hsem as [Hlc [Hs Hvl]].
      split; [exact Hlc |].
      destruct (Hvl v (multi_refl v) Hv) as [A [B C]]. auto.
  - split.
    + intros v Hv [Hlc [T1 [body [Heq [Hlca Hf]]]]]. unfold sem.
      change (semF (S (rty_nodes R1 + rty_nodes R2)) v (R_Func R1 R2)). simpl.
      split; [exact Hlc |]. split; [apply safe_value; exact Hv |].
      intros r Hmu Hvalr. rewrite (multi_of_value v r Hv Hmu).
      split; [exact Hlc |].
      exists T1, body. split; [exact Heq |]. split; [exact Hlca |].
      intros w Hw Hsw.
      assert (Hsemw : sem w R1) by
        (apply semF_to_sem with (n := rty_nodes R1 + rty_nodes R2); [lia | exact Hsw]).
      assert (Hvalw : valok w R1) by (apply (proj2 IHR1); auto).
      pose proof (Hf w Hw Hvalw) as Hres.
      apply sem_to_semF with (n := rty_nodes R1 + rty_nodes R2);
        [rewrite rty_nodes_open_rty_tm; lia | exact Hres].
    + intros v Hv Hsem. unfold sem in Hsem.
      change (semF (S (rty_nodes R1 + rty_nodes R2)) v (R_Func R1 R2)) in Hsem. simpl in Hsem.
      destruct Hsem as [Hlc [Hs Hvl]].
      destruct (Hvl v (multi_refl v) Hv) as [Hlcr [T1 [body [Heq [Hlca Hf]]]]].
      split; [exact Hlc |].
      exists T1, body. split; [exact Heq |]. split; [exact Hlca |].
      intros w Hw Hvalw.
      assert (Hsemw : sem w R1) by (apply (proj1 IHR1); auto).
      assert (Hfsw : semF (rty_nodes R1 + rty_nodes R2) w R1) by
        (apply sem_to_semF with (n := rty_nodes R1 + rty_nodes R2); [lia | exact Hsemw]).
      pose proof (Hf w Hw Hfsw) as Hres.
      apply semF_to_sem with (n := rty_nodes R1 + rty_nodes R2);
        [rewrite rty_nodes_open_rty_tm; lia | exact Hres].
  - split.
    + intros v Hv [Hlc [w [Hw [Hvalw Hsv]]]]. unfold sem.
      change (semF (S (rty_nodes R1 + rty_nodes R2)) v (R_Exists R1 R2)). simpl.
      split; [exact Hlc |]. split; [apply safe_value; exact Hv |].
      intros r Hmu Hvalr. rewrite (multi_of_value v r Hv Hmu).
      split; [exact Hlc |].
      exists w. split; [exact Hw |]. split.
      * assert (Hsems : sem w R1) by (apply (proj1 IHR1); auto).
        apply sem_to_semF with (n := rty_nodes R1 + rty_nodes R2); [lia | exact Hsems].
      * apply sem_to_semF with (n := rty_nodes R1 + rty_nodes R2);
          [rewrite rty_nodes_open_rty_tm; lia | exact Hsv].
    + intros v Hv Hsem. unfold sem in Hsem.
      change (semF (S (rty_nodes R1 + rty_nodes R2)) v (R_Exists R1 R2)) in Hsem. simpl in Hsem.
      destruct Hsem as [Hlc [Hs Hvl]].
      destruct (Hvl v (multi_refl v) Hv) as [Hlcr [w [Hw [Hsw Hsv]]]].
      split; [exact Hlc |].
      exists w. split; [exact Hw |]. split.
      * assert (Hsemw : sem w R1) by
          (apply semF_to_sem with (n := rty_nodes R1 + rty_nodes R2); [lia | exact Hsw]).
        apply (proj2 IHR1); auto.
      * apply semF_to_sem with (n := rty_nodes R1 + rty_nodes R2);
          [rewrite rty_nodes_open_rty_tm; lia | exact Hsv].
  - split.
    + intros v Hv [Hlc [body [Heq [Hlca Hf]]]]. unfold sem.
      change (semF (S (rty_nodes R1)) v (R_Poly R1)). simpl.
      split; [exact Hlc |]. split; [apply safe_value; exact Hv |].
      intros r Hmu Hvalr. rewrite (multi_of_value v r Hv Hmu).
      split; [exact Hlc |].
      exists body. split; [exact Heq |]. split; [exact Hlca |].
      intros U HU.
      apply sem_to_semF with (n := rty_nodes R1);
        [rewrite rty_nodes_open_rty_ty; lia | apply Hf; auto].
    + intros v Hv Hsem. unfold sem in Hsem.
      change (semF (S (rty_nodes R1)) v (R_Poly R1)) in Hsem. simpl in Hsem.
      destruct Hsem as [Hlc [Hs Hvl]].
      destruct (Hvl v (multi_refl v) Hv) as [Hlcr [body [Heq [Hlca Hf]]]].
      split; [exact Hlc |].
      exists body. split; [exact Heq |]. split; [exact Hlca |].
      intros U HU.
      apply semF_to_sem with (n := rty_nodes R1);
        [rewrite rty_nodes_open_rty_ty; lia | apply Hf; auto].
Qed.

Lemma valok_to_sem : forall v R, value v -> valok v R -> sem v R.
Proof. intros. apply (proj1 (sem_valok R)); auto. Qed.

Lemma sem_to_valok : forall v R, value v -> sem v R -> valok v R.
Proof. intros. apply (proj2 (sem_valok R)); auto. Qed.

(* ============================================================ *)
(* Step inversion lemmas and semantic composition lemmas         *)
(* ============================================================ *)

Lemma step_app_inv : forall a b y, step (tm_app a b) y ->
  (exists a', step a a' /\ y = tm_app a' b) \/
  (exists b', value a /\ step b b' /\ y = tm_app a b') \/
  (exists T body, a = tm_abs T body /\ y = open_tm body b /\
     locally_closed_tm (tm_abs T body) /\ value b).
Proof.
  intros a b y H. inversion H; subst.
  - right; right. exists T, t. split; [reflexivity |]. split; [reflexivity |]. auto.
  - left. exists t1'. split; [assumption | reflexivity].
  - right; left. exists t2'. split; [assumption |]. split; [assumption | reflexivity].
Qed.

Lemma step_tapp_inv : forall a U y, step (tm_tapp a U) y ->
  (exists a', step a a' /\ y = tm_tapp a' U) \/
  (exists body, a = tm_tabs body /\ y = open_tm_ty body U /\
     locally_closed_tm (tm_tabs body) /\ locally_closed_ty U).
Proof.
  intros a U y H. inversion H; subst.
  - right. eauto.
  - left. eauto.
Qed.

Lemma step_div_inv : forall a b y, step (tm_div a b) y ->
  (exists a', step a a' /\ y = tm_div a' b) \/
  (exists b', value a /\ step b b' /\ y = tm_div a b') \/
  (exists n m, a = tm_int n /\ b = tm_int m /\ m <> 0%Z /\
     y = tm_int (Z.div n m)).
Proof.
  intros a b y H. inversion H; subst.
  - left. exists t1'. split; [assumption | reflexivity].
  - right; left. exists t2'. split; [assumption |]. split; [assumption | reflexivity].
  - right; right. exists n, m. split; [reflexivity |]. split; [reflexivity |].
    split; [assumption | reflexivity].
Qed.

Lemma step_arith_inv : forall op a b y, step (tm_arith op a b) y ->
  (exists a', step a a' /\ y = tm_arith op a' b) \/
  (exists b', value a /\ step b b' /\ y = tm_arith op a b') \/
  (exists n m, a = tm_int n /\ b = tm_int m /\
     y = tm_int (eval_integer_operator op n m)).
Proof.
  intros op a b y H. inversion H; subst.
  - left. exists t1'. split; [assumption | reflexivity].
  - right; left. exists t2'. split; [assumption |]. split; [assumption | reflexivity].
  - right; right. exists n, m. split; [reflexivity |]. split; [reflexivity | reflexivity].
Qed.

(* Components of the semantic relation *)

Lemma sem_lc : forall t R, sem t R -> locally_closed_tm t.
Proof.
  intros t R H. unfold sem in H.
  destruct (rty_nodes R) as [| n] eqn:E.
  - pose proof (rty_nodes_ge1 R). lia.
  - simpl in H. destruct H as [Hlc _]. exact Hlc.
Qed.

Lemma sem_safe : forall t R, sem t R -> safe t.
Proof.
  intros t R H. unfold sem in H.
  destruct (rty_nodes R) as [| n] eqn:E.
  - pose proof (rty_nodes_ge1 R). lia.
  - simpl in H. destruct H as [_ [Hs _]]. exact Hs.
Qed.

Lemma sem_multi : forall t u R, multi t u -> sem t R -> sem u R.
Proof.
  intros t u R Hm. induction Hm as [ x | x y z Hstep Htail IH ]; intros H.
  - exact H.
  - apply IH. apply sem_step with (t := x); auto.
Qed.

(* ===== Applications ===== *)

Lemma safe_app : forall t1 t2 R1 R2,
  sem t1 (R_Func R1 R2) -> sem t2 R1 -> safe (tm_app t1 t2).
Proof.
  intros t1 t2 R1 R2 Hs1 Hs2 u Hmu.
  remember (tm_app t1 t2) as x eqn:Hx.
  revert t1 t2 Hs1 Hs2 Hx.
  induction Hmu as [ x0 | x0 y z Hstep Htail IH ]; intros t1 t2 Hs1 Hs2 Hx.
  - subst x0. simpl.
    destruct (sem_safe t1 (R_Func R1 R2) Hs1 t1 (multi_refl t1)) as [Hv1 | [a Hstep1]].
    + destruct (sem_safe t2 R1 Hs2 t2 (multi_refl t2)) as [Hv2 | [b Hstep2]].
      * right.
        destruct (sem_to_valok t1 (R_Func R1 R2) Hv1 Hs1)
          as [Hlc1 [T0 [body [Heq [Hlca Hf]]]]].
        exists (open_tm body t2). rewrite Heq.
        apply ST_AppAbs; [exact Hlca | exact Hv2].
      * right. exists (tm_app t1 b). apply ST_App2; [exact Hv1 | exact Hstep2].
    + right. exists (tm_app a t2). apply ST_App1; [exact Hstep1 | exact (sem_lc t2 R1 Hs2)].
  - subst x0.
    destruct (step_app_inv t1 t2 y Hstep)
      as [(a' & Hst & Heq) | [(b' & Hv & Hst & Heq) | (T0 & body & Heq & Hy & Hlca & Hval)]].
    + subst y. apply (IH a' t2). apply sem_step with (t := t1); auto. exact Hs2. reflexivity.
    + subst y. apply (IH t1 b'). exact Hs1. apply sem_step with (t := t2); auto. reflexivity.
    + subst y. subst t1.
      destruct (sem_to_valok (tm_abs T0 body) (R_Func R1 R2) (v_abs T0 body Hlca) Hs1)
        as [Hlc1 [T1 [body1 [Heq1 [Hlca1 Hf]]]]].
      injection Heq1 as HT Hb. subst T1. subst body1.
      pose proof (Hf t2 Hval (sem_to_valok t2 R1 Hval Hs2)) as Hres.
      exact (sem_safe _ _ Hres _ Htail).
Qed.

Lemma app_value_spec : forall t1 t2 R1 R2 r,
  sem t1 (R_Func R1 R2) -> sem t2 R1 ->
  multi (tm_app t1 t2) r -> value r ->
  exists w, value w /\ sem w R1 /\ sem r (open_rty_tm R2 w).
Proof.
  intros t1 t2 R1 R2 r Hs1 Hs2 Hmu.
  remember (tm_app t1 t2) as x eqn:Hx.
  revert t1 t2 Hs1 Hs2 Hx.
  induction Hmu as [ x0 | x0 y z Hstep Htail IH ]; intros t1 t2 Hs1 Hs2 Hx Hval.
  - subst x0. inversion Hval.
  - subst x0.
    destruct (step_app_inv t1 t2 y Hstep)
      as [(a' & Hst & Heq) | [(b' & Hv & Hst & Heq) | (T0 & body & Heq & Hy & Hlca & Hval')]].
    + subst y. apply (IH a' t2).
      * apply sem_step with (t := t1); auto.
      * exact Hs2.
      * reflexivity.
      * exact Hval.
    + subst y. apply (IH t1 b').
      * exact Hs1.
      * apply sem_step with (t := t2); auto.
      * reflexivity.
      * exact Hval.
    + subst y. subst t1.
      destruct (sem_to_valok (tm_abs T0 body) (R_Func R1 R2) (v_abs T0 body Hlca) Hs1)
        as [Hlc1 [T1 [body1 [Heq1 [Hlca1 Hf]]]]].
      injection Heq1 as HT Hb. subst T1. subst body1.
      exists t2. split; [exact Hval' |]. split; [exact Hs2 |].
      apply sem_multi with (t := open_tm body t2); auto.
      apply Hf; auto. apply sem_to_valok; auto.
Qed.

Lemma sem_app : forall t1 t2 R1 R2,
  sem t1 (R_Func R1 R2) -> sem t2 R1 ->
  sem (tm_app t1 t2) (R_Exists R1 R2).
Proof.
  intros t1 t2 R1 R2 Hs1 Hs2.
  unfold sem. change (semF (S (rty_nodes R1 + rty_nodes R2)) (tm_app t1 t2) (R_Exists R1 R2)).
  simpl.
  split.
  - apply lc_tm_app; [exact (sem_lc t1 (R_Func R1 R2) Hs1) | exact (sem_lc t2 R1 Hs2)].
  - split.
    + apply (safe_app t1 t2 R1 R2); auto.
    + intros r Hmu Hval.
      destruct (app_value_spec t1 t2 R1 R2 r Hs1 Hs2 Hmu Hval)
        as [w [Hw [Hsw Hsr]]].
      split; [exact (sem_lc r (open_rty_tm R2 w) Hsr) |].
      exists w. split; [exact Hw |]. split.
      * apply sem_to_semF with (n := rty_nodes R1 + rty_nodes R2); [lia | exact Hsw].
      * apply sem_to_semF with (n := rty_nodes R1 + rty_nodes R2);
          [rewrite rty_nodes_open_rty_tm; lia | exact Hsr].
Qed.

(* ============================================================ *)
(* Integers, division and arithmetic                             *)
(* ============================================================ *)

Lemma lc_multi : forall t u, multi t u -> locally_closed_tm t -> locally_closed_tm u.
Proof.
  intros t u Hm. induction Hm as [ x | x y z Hstep Htail IH ]; intros Hlc.
  - exact Hlc.
  - apply IH. apply lc_step with (t := x); auto.
Qed.

Lemma multi_to_pms : forall t u, multi t u -> predicate_multistep t u.
Proof.
  intros t u Hm. induction Hm as [ x | x y z Hstep Htail IH ].
  - apply PMS_Refl.
  - eapply PMS_Step; eauto.
Qed.

Lemma pms_to_multi : forall t u, predicate_multistep t u -> multi t u.
Proof.
  intros t u Hm. induction Hm as [ x | x y z Hstep Htail IH ].
  - apply multi_refl.
  - eapply multi_step; eauto.
Qed.

Lemma pred_ne_nonzero : forall m,
  predicate_holds (Pred_Ne (tm_int m) (tm_int 0%Z)) -> m <> 0%Z.
Proof.
  intros m H E. subst m.
  unfold predicate_holds, Pred_Ne in H.
  simpl in H.
  apply H. exists (tm_int 0%Z). split; [apply PMS_Refl |]. split; [apply PMS_Refl | apply v_int].
Qed.

Lemma sem_int_true : forall n, sem (tm_int n) (R_Refine Ty_Int Pred_True).
Proof.
  intros n. unfold sem. change (semF 1 (tm_int n) (R_Refine Ty_Int Pred_True)). simpl.
  split; [apply lc_tm_int |]. split; [apply safe_value; apply v_int |].
  intros r Hmu Hval. rewrite (multi_of_value _ _ (v_int n) Hmu).
  repeat split; auto.
  - apply lc_tm_int.
  - exists n; reflexivity.
Qed.

Lemma open_pred_eq_int : forall n,
  open_pred_tm (Pred_Eq (tm_bvar 0) (tm_int n)) (tm_int n) = Pred_Eq (tm_int n) (tm_int n).
Proof. intros. simpl. reflexivity. Qed.

Lemma sem_int_eq : forall n,
  sem (tm_int n) (R_Refine Ty_Int (Pred_Eq (tm_bvar 0) (tm_int n))).
Proof.
  intros n. unfold sem.
  change (semF 1 (tm_int n) (R_Refine Ty_Int (Pred_Eq (tm_bvar 0) (tm_int n)))). simpl.
  split; [apply lc_tm_int |]. split; [apply safe_value; apply v_int |].
  intros r Hmu Hval. rewrite (multi_of_value _ _ (v_int n) Hmu).
  rewrite open_pred_eq_int.
  repeat split; auto.
  - apply lc_tm_int.
  - exists n; reflexivity.
  - unfold predicate_holds. simpl.
    exists (tm_int n). split; [apply PMS_Refl |]. split; [apply PMS_Refl | apply v_int].
Qed.

(* ===== Division ===== *)

Lemma div_multi_int : forall t1 t2 r,
  multi (tm_div t1 t2) r -> value r -> exists n, r = tm_int n.
Proof.
  intros t1 t2 r Hmu.
  remember (tm_div t1 t2) as x eqn:Hx.
  revert t1 t2 Hx.
  induction Hmu as [ x0 | x0 y z Hstep Htail IH ]; intros t1 t2 Hx Hval.
  - subst x0. inversion Hval.
  - subst x0.
    destruct (step_div_inv t1 t2 y Hstep)
      as [(a' & Hst & Heq) | [(b' & Hv & Hst & Heq) | (n & m & Heq1 & Heq2 & Hneq & Hy)]].
    + subst y. eapply IH; eauto.
    + subst y. eapply IH; eauto.
    + subst y. subst t1. subst t2.
      rewrite (multi_of_value _ _ (v_int (Z.div n m)) Htail). exists (Z.div n m). reflexivity.
Qed.

Lemma safe_div : forall t1 t2,
  sem t1 (R_Refine Ty_Int Pred_True) ->
  sem t2 (R_Refine Ty_Int (Pred_Ne (tm_bvar 0) (tm_int 0%Z))) ->
  safe (tm_div t1 t2).
Proof.
  intros t1 t2 Hs1 Hs2 u Hmu.
  remember (tm_div t1 t2) as x eqn:Hx.
  revert t1 t2 Hs1 Hs2 Hx.
  induction Hmu as [ x0 | x0 y z Hstep Htail IH ]; intros t1 t2 Hs1 Hs2 Hx.
  - subst x0. simpl.
    destruct (sem_safe t1 _ Hs1 t1 (multi_refl t1)) as [Hv1 | [a Hst1]].
    + destruct (sem_safe t2 _ Hs2 t2 (multi_refl t2)) as [Hv2 | [b Hst2]].
      * right.
        assert (H1 : semF 1 t1 (R_Refine Ty_Int Pred_True)) by
          (apply sem_to_semF; [simpl; lia | exact Hs1]).
        simpl in H1. destruct H1 as [_ [_ Hvcl1]].
        destruct (Hvcl1 t1 (multi_refl t1) Hv1) as [_ [Hsh1 _]].
        destruct Hsh1 as [n Heq1].
        assert (H2 : semF 1 t2 (R_Refine Ty_Int (Pred_Ne (tm_bvar 0) (tm_int 0%Z)))) by
          (apply sem_to_semF; [simpl; lia | exact Hs2]).
        simpl in H2. destruct H2 as [_ [_ Hvcl2]].
        destruct (Hvcl2 t2 (multi_refl t2) Hv2) as [_ [Hsh2 Hpred2]].
        destruct Hsh2 as [m Heq2].
        subst t1. subst t2.
        exists (tm_int (Z.div n m)). apply ST_DivInt.
        change (predicate_holds (Pred_Ne (tm_int m) (tm_int 0%Z))) in Hpred2.
        apply pred_ne_nonzero in Hpred2. exact Hpred2.
      * right. exists (tm_div t1 b). apply ST_Div2; auto.
    + right. exists (tm_div a t2). apply ST_Div1; [exact Hst1 | exact (sem_lc t2 _ Hs2)].
  - subst x0.
    destruct (step_div_inv t1 t2 y Hstep)
      as [(a' & Hst & Heq) | [(b' & Hv & Hst & Heq) | (n & m & Heq1 & Heq2 & Hneq & Hy)]].
    + subst y. apply (IH a' t2).
      * apply sem_step with (t := t1); auto.
      * exact Hs2.
      * reflexivity.
    + subst y. apply (IH t1 b').
      * exact Hs1.
      * apply sem_step with (t := t2); auto.
      * reflexivity.
    + subst y. subst t1. subst t2.
      left. rewrite (multi_of_value _ _ (v_int (Z.div n m)) Htail). apply v_int.
Qed.

Lemma sem_div : forall t1 t2,
  sem t1 (R_Refine Ty_Int Pred_True) ->
  sem t2 (R_Refine Ty_Int (Pred_Ne (tm_bvar 0) (tm_int 0%Z))) ->
  sem (tm_div t1 t2) (R_Refine Ty_Int Pred_True).
Proof.
  intros t1 t2 Hs1 Hs2.
  unfold sem. change (semF 1 (tm_div t1 t2) (R_Refine Ty_Int Pred_True)). simpl.
  split.
  - apply lc_tm_div; [exact (sem_lc t1 _ Hs1) | exact (sem_lc t2 _ Hs2)].
  - split; [apply safe_div; auto |].
    intros r Hmu Hval.
    destruct (div_multi_int t1 t2 r Hmu Hval) as [n Heq]. subst r.
    assert (Hlcd : locally_closed_tm (tm_div t1 t2)) by
      (apply lc_tm_div; [exact (sem_lc t1 _ Hs1) | exact (sem_lc t2 _ Hs2)]).
    split; [apply lc_multi with (t := tm_div t1 t2); auto |].
    split; [exists n; reflexivity | exact I].
Qed.

(* ===== Arithmetic ===== *)

Lemma arith_multi_int : forall op t1 t2 r,
  multi (tm_arith op t1 t2) r -> value r -> exists n, r = tm_int n.
Proof.
  intros op t1 t2 r Hmu.
  remember (tm_arith op t1 t2) as x eqn:Hx.
  revert op t1 t2 Hx.
  induction Hmu as [ x0 | x0 y z Hstep Htail IH ]; intros op0 t1 t2 Hx Hval.
  - subst x0. inversion Hval.
  - subst x0.
    destruct (step_arith_inv op0 t1 t2 y Hstep)
      as [(a' & Hst & Heq) | [(b' & Hv & Hst & Heq) | (n & m & Heq1 & Heq2 & Hy)]].
    + subst y. eapply IH; eauto.
    + subst y. eapply IH; eauto.
    + subst y. subst t1. subst t2.
      rewrite (multi_of_value _ _ (v_int (eval_integer_operator op0 n m)) Htail).
      exists (eval_integer_operator op0 n m). reflexivity.
Qed.

Lemma safe_arith : forall op t1 t2,
  sem t1 (R_Refine Ty_Int Pred_True) ->
  sem t2 (R_Refine Ty_Int Pred_True) ->
  safe (tm_arith op t1 t2).
Proof.
  intros op t1 t2 Hs1 Hs2 u Hmu.
  remember (tm_arith op t1 t2) as x eqn:Hx.
  revert op t1 t2 Hs1 Hs2 Hx.
  induction Hmu as [ x0 | x0 y z Hstep Htail IH ]; intros op0 t1 t2 Hs1 Hs2 Hx.
  - subst x0. simpl.
    destruct (sem_safe t1 _ Hs1 t1 (multi_refl t1)) as [Hv1 | [a Hst1]].
    + destruct (sem_safe t2 _ Hs2 t2 (multi_refl t2)) as [Hv2 | [b Hst2]].
      * right.
        assert (H1 : semF 1 t1 (R_Refine Ty_Int Pred_True)) by
          (apply sem_to_semF; [simpl; lia | exact Hs1]).
        simpl in H1. destruct H1 as [_ [_ Hvcl1]].
        destruct (Hvcl1 t1 (multi_refl t1) Hv1) as [_ [Hsh1 _]].
        destruct Hsh1 as [n Heq1].
        assert (H2 : semF 1 t2 (R_Refine Ty_Int Pred_True)) by
          (apply sem_to_semF; [simpl; lia | exact Hs2]).
        simpl in H2. destruct H2 as [_ [_ Hvcl2]].
        destruct (Hvcl2 t2 (multi_refl t2) Hv2) as [_ [Hsh2 _]].
        destruct Hsh2 as [m Heq2].
        subst t1. subst t2.
        exists (tm_int (eval_integer_operator op0 n m)). apply ST_ArithInt.
      * right. exists (tm_arith op0 t1 b). apply ST_Arith2; auto.
    + right. exists (tm_arith op0 a t2). apply ST_Arith1; [exact Hst1 | exact (sem_lc t2 _ Hs2)].
  - subst x0.
    destruct (step_arith_inv op0 t1 t2 y Hstep)
      as [(a' & Hst & Heq) | [(b' & Hv & Hst & Heq) | (n & m & Heq1 & Heq2 & Hy)]].
    + subst y. apply (IH op0 a' t2).
      * apply sem_step with (t := t1); auto.
      * exact Hs2.
      * reflexivity.
    + subst y. apply (IH op0 t1 b').
      * exact Hs1.
      * apply sem_step with (t := t2); auto.
      * reflexivity.
    + subst y. subst t1. subst t2.
      left. rewrite (multi_of_value _ _ (v_int (eval_integer_operator op0 n m)) Htail).
      apply v_int.
Qed.

Lemma open_pred_eq_arith : forall op t1 t2 n,
  lc_tm_at 0 0 t1 -> lc_tm_at 0 0 t2 ->
  open_pred_tm (Pred_Eq (tm_bvar 0) (tm_arith op t1 t2)) (tm_int n) =
  Pred_Eq (tm_int n) (tm_arith op t1 t2).
Proof.
  intros op t1 t2 n H1 H2. unfold open_pred_tm. simpl.
  rewrite (open_tm_rec_lc 0 0 0 t1 (tm_int n) H1 (Nat.le_refl 0)).
  rewrite (open_tm_rec_lc 0 0 0 t2 (tm_int n) H2 (Nat.le_refl 0)).
  reflexivity.
Qed.

Lemma sem_arith : forall op t1 t2,
  sem t1 (R_Refine Ty_Int Pred_True) ->
  sem t2 (R_Refine Ty_Int Pred_True) ->
  sem (tm_arith op t1 t2)
      (R_Refine Ty_Int (Pred_Eq (tm_bvar 0) (tm_arith op t1 t2))).
Proof.
  intros op t1 t2 Hs1 Hs2.
  unfold sem.
  change (semF 1 (tm_arith op t1 t2)
            (R_Refine Ty_Int (Pred_Eq (tm_bvar 0) (tm_arith op t1 t2)))). simpl.
  split.
  - apply lc_tm_arith; [exact (sem_lc t1 _ Hs1) | exact (sem_lc t2 _ Hs2)].
  - split; [apply safe_arith; auto |].
    intros r Hmu Hval.
    destruct (arith_multi_int op t1 t2 r Hmu Hval) as [n Heq]. subst r.
    assert (Hlc1 : lc_tm_at 0 0 t1) by (apply sem_lc in Hs1; exact Hs1).
    assert (Hlc2 : lc_tm_at 0 0 t2) by (apply sem_lc in Hs2; exact Hs2).
    assert (Hlcd : locally_closed_tm (tm_arith op t1 t2)) by
      (apply lc_tm_arith; auto).
    split; [apply lc_multi with (t := tm_arith op t1 t2); auto |].
    split; [exists n; reflexivity |].
    rewrite open_pred_eq_arith; auto.
    unfold predicate_holds. simpl.
    exists (tm_int n). split; [apply PMS_Refl |]. split.
    + apply multi_to_pms. exact Hmu.
    + apply v_int.
Qed.

(* ===== Type application ===== *)

Lemma tapp_value_spec : forall t U R1 r,
  sem t (R_Poly R1) -> locally_closed_ty U ->
  multi (tm_tapp t U) r -> value r ->
  sem r (open_rty_ty R1 U).
Proof.
  intros t U R1 r Hs HU Hmu.
  remember (tm_tapp t U) as x eqn:Hx.
  revert t U R1 Hs HU Hx.
  induction Hmu as [ x0 | x0 y z Hstep Htail IH ]; intros t U R1 Hs HU Hx Hval.
  - subst x0. inversion Hval.
  - subst x0.
    destruct (step_tapp_inv t U y Hstep)
      as [(a' & Hst & Heq) | (body & Heq & Hy & Hlca & HlcU)].
    + subst y. apply (IH a' U R1).
      * apply sem_step with (t := t); auto.
      * exact HU.
      * reflexivity.
      * exact Hval.
    + subst y. subst t.
      destruct (sem_to_valok (tm_tabs body) (R_Poly R1) (v_tabs body Hlca) Hs)
        as [Hlc [body1 [Heq1 [Hlca1 Hf]]]].
      injection Heq1 as Hb. subst body1.
      apply sem_multi with (t := open_tm_ty body U); auto.
Qed.

Lemma safe_tapp : forall t U R1,
  sem t (R_Poly R1) -> locally_closed_ty U -> safe (tm_tapp t U).
Proof.
  intros t U R1 Hs HU u Hmu.
  remember (tm_tapp t U) as x eqn:Hx.
  revert t U R1 Hs HU Hx.
  induction Hmu as [ x0 | x0 y z Hstep Htail IH ]; intros t U R1 Hs HU Hx.
  - subst x0. simpl.
    destruct (sem_safe t (R_Poly R1) Hs t (multi_refl t)) as [Hv | [a Hst]].
    + right.
      destruct (sem_to_valok t (R_Poly R1) Hv Hs)
        as [Hlc [body [Heq [Hlca Hf]]]].
      exists (open_tm_ty body U). rewrite Heq. apply ST_TAppTabs; auto.
    + right. exists (tm_tapp a U). apply ST_TApp; auto.
  - subst x0.
    destruct (step_tapp_inv t U y Hstep)
      as [(a' & Hst & Heq) | (body & Heq & Hy & Hlca & HlcU)].
    + subst y. apply (IH a' U R1).
      * apply sem_step with (t := t); auto.
      * exact HU.
      * reflexivity.
    + subst y. subst t.
      destruct (sem_to_valok (tm_tabs body) (R_Poly R1) (v_tabs body Hlca) Hs)
        as [Hlc [body1 [Heq1 [Hlca1 Hf]]]].
      injection Heq1 as Hb. subst body1.
      exact (sem_safe _ _ (Hf U HU) _ Htail).
Qed.

Lemma sem_tapp : forall t U R1,
  sem t (R_Poly R1) -> locally_closed_ty U ->
  sem (tm_tapp t U) (open_rty_ty R1 U).
Proof.
  intros t U R1 Hs HU.
  unfold sem. rewrite rty_nodes_open_rty_ty.
  destruct R1 as [ T0 p0 | A B | A B | A ]; simpl.
  - split.
    + apply lc_tm_tapp; [exact (sem_lc t (R_Poly (R_Refine T0 p0)) Hs) | exact HU].
    + split.
      * apply (safe_tapp t U (R_Refine T0 p0)); auto.
      * intros r Hmu Hval.
        assert (Hsr : sem r (open_rty_ty (R_Refine T0 p0) U)) by
          (apply tapp_value_spec with (t := t) (U := U) (R1 := R_Refine T0 p0); auto).
        assert (Hnf : semF (rty_nodes (R_Refine T0 p0)) r
                        (open_rty_ty (R_Refine T0 p0) U)) by
          (apply sem_to_semF; [rewrite rty_nodes_open_rty_ty; apply Nat.le_refl | exact Hsr]).
        simpl in Hnf. destruct Hnf as [_ [_ HB]].
        apply (HB r (multi_refl r) Hval).
  - split.
    + apply lc_tm_tapp; [exact (sem_lc t (R_Poly (R_Func A B)) Hs) | exact HU].
    + split.
      * apply (safe_tapp t U (R_Func A B)); auto.
      * intros r Hmu Hval.
        assert (Hsr : sem r (open_rty_ty (R_Func A B) U)) by
          (apply tapp_value_spec with (t := t) (U := U) (R1 := R_Func A B); auto).
        assert (Hnf : semF (rty_nodes (R_Func A B)) r
                        (open_rty_ty (R_Func A B) U)) by
          (apply sem_to_semF; [rewrite rty_nodes_open_rty_ty; apply Nat.le_refl | exact Hsr]).
        simpl in Hnf. destruct Hnf as [_ [_ HB]].
        apply (HB r (multi_refl r) Hval).
  - split.
    + apply lc_tm_tapp; [exact (sem_lc t (R_Poly (R_Exists A B)) Hs) | exact HU].
    + split.
      * apply (safe_tapp t U (R_Exists A B)); auto.
      * intros r Hmu Hval.
        assert (Hsr : sem r (open_rty_ty (R_Exists A B) U)) by
          (apply tapp_value_spec with (t := t) (U := U) (R1 := R_Exists A B); auto).
        assert (Hnf : semF (rty_nodes (R_Exists A B)) r
                        (open_rty_ty (R_Exists A B) U)) by
          (apply sem_to_semF; [rewrite rty_nodes_open_rty_ty; apply Nat.le_refl | exact Hsr]).
        simpl in Hnf. destruct Hnf as [_ [_ HB]].
        apply (HB r (multi_refl r) Hval).
  - split.
    + apply lc_tm_tapp; [exact (sem_lc t (R_Poly (R_Poly A)) Hs) | exact HU].
    + split.
      * apply (safe_tapp t U (R_Poly A)); auto.
      * intros r Hmu Hval.
        assert (Hsr : sem r (open_rty_ty (R_Poly A) U)) by
          (apply tapp_value_spec with (t := t) (U := U) (R1 := R_Poly A); auto).
        assert (Hnf : semF (rty_nodes (R_Poly A)) r
                        (open_rty_ty (R_Poly A) U)) by
          (apply sem_to_semF; [rewrite rty_nodes_open_rty_ty; apply Nat.le_refl | exact Hsr]).
        simpl in Hnf. destruct Hnf as [_ [_ HB]].
        apply (HB r (multi_refl r) Hval).
Qed.

Theorem never_stuck : forall (t t' : tm) (R : rty),
  has_rtype [] empty_rcontext t R ->
  multi t t' ->
  value t' \/ exists t'' : tm, t' --> t''.
Proof.

Qed.

End SystemFRefinementTask.
