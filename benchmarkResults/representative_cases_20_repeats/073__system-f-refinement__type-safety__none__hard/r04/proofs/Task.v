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

Module SystemFRefinementLib.
Import ListNotations SystemFRefinement SystemFRefinementLogic SystemFRefinementTyping SystemFRefinementEvaluation.

Definition env := atom -> tm.
Definition tyenv := atom -> ty.

Fixpoint tsubst (s : env) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => s x
  | tm_abs T t1 => tm_abs T (tsubst s t1)
  | tm_app t1 t2 => tm_app (tsubst s t1) (tsubst s t2)
  | tm_tabs t1 => tm_tabs (tsubst s t1)
  | tm_tapp t1 T => tm_tapp (tsubst s t1) T
  | tm_int n => tm_int n
  | tm_div t1 t2 => tm_div (tsubst s t1) (tsubst s t2)
  | tm_arith op t1 t2 => tm_arith op (tsubst s t1) (tsubst s t2)
  end.

Fixpoint qsubst (s : env) (q : qualifier) : qualifier :=
  match q with
  | Pred_True => Pred_True
  | Pred_False => Pred_False
  | Pred_Eq t1 t2 => Pred_Eq (tsubst s t1) (tsubst s t2)
  | Pred_Lt t1 t2 => Pred_Lt (tsubst s t1) (tsubst s t2)
  | Pred_Le t1 t2 => Pred_Le (tsubst s t1) (tsubst s t2)
  | Pred_And p1 p2 => Pred_And (qsubst s p1) (qsubst s p2)
  | Pred_Or p1 p2 => Pred_Or (qsubst s p1) (qsubst s p2)
  | Pred_Not p1 => Pred_Not (qsubst s p1)
  end.

Fixpoint ty_subst_atoms (sg : tyenv) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => sg X
  | Ty_Arrow T1 T2 => Ty_Arrow (ty_subst_atoms sg T1) (ty_subst_atoms sg T2)
  | Ty_All T1 => Ty_All (ty_subst_atoms sg T1)
  | Ty_Int => Ty_Int
  end.

Fixpoint tm_ty_subst_atoms (sg : tyenv) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T t1 => tm_abs (ty_subst_atoms sg T) (tm_ty_subst_atoms sg t1)
  | tm_app t1 t2 => tm_app (tm_ty_subst_atoms sg t1) (tm_ty_subst_atoms sg t2)
  | tm_tabs t1 => tm_tabs (tm_ty_subst_atoms sg t1)
  | tm_tapp t1 T => tm_tapp (tm_ty_subst_atoms sg t1) (ty_subst_atoms sg T)
  | tm_int n => tm_int n
  | tm_div t1 t2 => tm_div (tm_ty_subst_atoms sg t1) (tm_ty_subst_atoms sg t2)
  | tm_arith op t1 t2 => tm_arith op (tm_ty_subst_atoms sg t1) (tm_ty_subst_atoms sg t2)
  end.

Fixpoint q_ty_subst_atoms (sg : tyenv) (q : qualifier) : qualifier :=
  match q with
  | Pred_True => Pred_True
  | Pred_False => Pred_False
  | Pred_Eq t1 t2 => Pred_Eq (tm_ty_subst_atoms sg t1) (tm_ty_subst_atoms sg t2)
  | Pred_Lt t1 t2 => Pred_Lt (tm_ty_subst_atoms sg t1) (tm_ty_subst_atoms sg t2)
  | Pred_Le t1 t2 => Pred_Le (tm_ty_subst_atoms sg t1) (tm_ty_subst_atoms sg t2)
  | Pred_And p1 p2 => Pred_And (q_ty_subst_atoms sg p1) (q_ty_subst_atoms sg p2)
  | Pred_Or p1 p2 => Pred_Or (q_ty_subst_atoms sg p1) (q_ty_subst_atoms sg p2)
  | Pred_Not p1 => Pred_Not (q_ty_subst_atoms sg p1)
  end.

Fixpoint rty_subst_env (s : env) (R : rty) : rty :=
  match R with
  | R_Refine T ps => R_Refine T (qsubst s ps)
  | R_Func R1 R2 => R_Func (rty_subst_env s R1) (rty_subst_env s R2)
  | R_Exists R1 R2 => R_Exists (rty_subst_env s R1) (rty_subst_env s R2)
  | R_Poly R1 => R_Poly (rty_subst_env s R1)
  end.

Fixpoint rty_ty_subst_atoms (sg : tyenv) (R : rty) : rty :=
  match R with
  | R_Refine T ps => R_Refine (ty_subst_atoms sg T) (q_ty_subst_atoms sg ps)
  | R_Func R1 R2 => R_Func (rty_ty_subst_atoms sg R1) (rty_ty_subst_atoms sg R2)
  | R_Exists R1 R2 => R_Exists (rty_ty_subst_atoms sg R1) (rty_ty_subst_atoms sg R2)
  | R_Poly R1 => R_Poly (rty_ty_subst_atoms sg R1)
  end.

Definition subst_all (sg : tyenv) (s : env) (t : tm) : tm :=
  tsubst s (tm_ty_subst_atoms sg t).

Definition rty_subst_all (sg : tyenv) (s : env) (R : rty) : rty :=
  rty_subst_env s (rty_ty_subst_atoms sg R).

Fixpoint rty_size (R : rty) : nat :=
  match R with
  | R_Refine _ _ => 1
  | R_Func R1 R2 => S (rty_size R1 + rty_size R2)
  | R_Exists R1 R2 => S (rty_size R1 + rty_size R2)
  | R_Poly R1 => S (rty_size R1)
  end.

Definition shape (T : ty) (v : tm) : Prop :=
  match T with
  | Ty_BVar _ => False
  | Ty_FVar _ => False
  | Ty_Int => exists n : Z, v = tm_int n
  | Ty_Arrow _ _ => exists (T0 : ty) (body : tm), v = tm_abs T0 body
  | Ty_All _ => exists body : tm, v = tm_tabs body
  end.

Definition closed_ty (T : ty) : Prop := locally_closed_ty T /\ fv_ty T = [].

Definition closed_sigma (sg : tyenv) : Prop := forall X, closed_ty (sg X).

Definition env_ok_base (s : env) : Prop :=
  (forall x, locally_closed_tm (s x)) /\ (forall x, ftv_tm (s x) = []).

End SystemFRefinementLib.

Module SystemFRefinementLib2.
Import ListNotations SystemFRefinement SystemFRefinementLogic SystemFRefinementTyping SystemFRefinementEvaluation SystemFRefinementLib.

(** ** Basic list helpers *)

Lemma max_atom_spec : forall (L : list atom) (x : atom), In x L -> x <= max_atom L.
Proof.
  induction L as [| y L' IH]; intros x H; simpl in *.
  - destruct H.
  - destruct H as [-> | H].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; eauto | apply Nat.le_max_r].
Qed.

Lemma fresh_notin : forall L, ~ In (fresh L) L.
Proof.
  intros L H. unfold fresh in H.
  apply max_atom_spec in H. lia.
Qed.

Lemma fresh_notin_app_l : forall L1 L2, ~ In (fresh (L1 ++ L2)) L1.
Proof.
  intros L1 L2 H. apply (fresh_notin (L1 ++ L2)).
  apply in_app_iff. left. exact H.
Qed.

Lemma fresh_notin_app_r : forall L1 L2, ~ In (fresh (L1 ++ L2)) L2.
Proof.
  intros L1 L2 H. apply (fresh_notin (L1 ++ L2)).
  apply in_app_iff. right. exact H.
Qed.

(** ** Identity substitutions *)

Lemma tsubst_id : forall t, tsubst (fun x => tm_fvar x) t = t.
Proof.
  induction t; simpl.
  - reflexivity. - reflexivity.
  - f_equal. assumption.
  - f_equal; assumption.
  - f_equal. assumption.
  - f_equal. assumption.
  - reflexivity.
  - f_equal; assumption.
  - f_equal; assumption.
Qed.

Lemma qsubst_id : forall q, qsubst (fun x => tm_fvar x) q = q.
Proof.
  induction q; simpl.
  - reflexivity. - reflexivity.
  - rewrite tsubst_id, tsubst_id. reflexivity.
  - rewrite tsubst_id, tsubst_id. reflexivity.
  - rewrite tsubst_id, tsubst_id. reflexivity.
  - f_equal; assumption.
  - f_equal; assumption.
  - f_equal. assumption.
Qed.

Lemma rty_subst_env_id : forall R, rty_subst_env (fun x => tm_fvar x) R = R.
Proof.
  induction R; simpl.
  - rewrite qsubst_id. reflexivity.
  - f_equal; assumption.
  - f_equal; assumption.
  - f_equal. assumption.
Qed.

Lemma ty_subst_atoms_id : forall T, ty_subst_atoms (fun X => Ty_FVar X) T = T.
Proof.
  induction T; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal; assumption.
  - f_equal. assumption.
  - reflexivity.
Qed.

Lemma tm_ty_subst_atoms_id : forall t, tm_ty_subst_atoms (fun X => Ty_FVar X) t = t.
Proof.
  induction t; simpl.
  - reflexivity. - reflexivity.
  - rewrite ty_subst_atoms_id. f_equal. assumption.
  - f_equal; assumption.
  - f_equal. assumption.
  - rewrite ty_subst_atoms_id. f_equal. assumption.
  - reflexivity.
  - f_equal; assumption.
  - f_equal; assumption.
Qed.

Lemma q_ty_subst_atoms_id : forall q, q_ty_subst_atoms (fun X => Ty_FVar X) q = q.
Proof.
  induction q; simpl.
  - reflexivity. - reflexivity.
  - rewrite tm_ty_subst_atoms_id, tm_ty_subst_atoms_id. reflexivity.
  - rewrite tm_ty_subst_atoms_id, tm_ty_subst_atoms_id. reflexivity.
  - rewrite tm_ty_subst_atoms_id, tm_ty_subst_atoms_id. reflexivity.
  - f_equal; assumption.
  - f_equal; assumption.
  - f_equal. assumption.
Qed.

Lemma rty_ty_subst_atoms_id : forall R, rty_ty_subst_atoms (fun X => Ty_FVar X) R = R.
Proof.
  induction R; simpl.
  - rewrite ty_subst_atoms_id, q_ty_subst_atoms_id. reflexivity.
  - f_equal; assumption.
  - f_equal; assumption.
  - f_equal. assumption.
Qed.

(** ** Monotonicity of local closure *)

Lemma lc_ty_mono : forall K T, lc_ty_at K T -> forall K', K <= K' -> lc_ty_at K' T.
Proof.
  intros K T H. induction H as
    [k i Hlt | k X | k T1 T2 H1 H2 IH1 IH2 | k T1 H1 IH1 | k];
    intros K' Hle; simpl in *.
  - apply lc_ty_bvar. lia.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; auto.
  - apply lc_ty_all. apply IH1; lia.
  - apply lc_ty_int.
Qed.

Lemma lc_tm_mono : forall K k t, lc_tm_at K k t ->
  forall K' k', K <= K' -> k <= k' -> lc_tm_at K' k' t.
Proof.
  intros K k t H. induction H as
    [K k i Hlt | K k x | K k T t Hty Hbody IHbody |
     K k t1 t2 H1 H2 IH1 IH2 | K k t H IH |
     K k t T H IH Hty | K k n |
     K k t1 t2 H1 H2 IH1 IH2 | K k op t1 t2 H1 H2 IH1 IH2];
    intros K' k' HK Hk; simpl in *.
  - apply lc_tm_bvar. lia.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + apply lc_ty_mono with (K := K); auto.
    + apply IHbody; lia.
  - apply lc_tm_app; auto.
  - apply lc_tm_tabs. apply IH; lia.
  - apply lc_tm_tapp.
    + apply IH; auto.
    + apply lc_ty_mono with (K := K); auto.
  - apply lc_tm_int.
  - apply lc_tm_div; auto.
  - apply lc_tm_arith; auto.
Qed.

Lemma lc_ty_at_0_mono : forall T, lc_ty_at 0 T -> forall K, lc_ty_at K T.
Proof.
  intros T H K. apply lc_ty_mono with (K := 0); auto. lia.
Qed.

Lemma lc_tm_at_0_mono : forall t, lc_tm_at 0 0 t -> forall K k, lc_tm_at K k t.
Proof.
  intros t H K k. apply lc_tm_mono with (K := 0) (k := 0); auto; lia.
Qed.

(** ** Opening a locally closed type/term is the identity *)

Lemma open_ty_id_lc : forall K T, lc_ty_at K T ->
  forall K' U, K <= K' -> open_ty_rec K' U T = T.
Proof.
  intros K T; revert K; induction T as [n | X | T1 IHT1 T2 IHT2 | T1 IHT1 |]; intros K Hlc K' U Hle; simpl in *.
  - inversion Hlc; subst.
    destruct (Nat.eqb K' n) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + reflexivity.
  - reflexivity.
  - inversion Hlc; subst. f_equal.
    + eapply IHT1; eauto; try lia.
    + eapply IHT2; eauto; try lia.
  - inversion Hlc; subst. f_equal. eapply IHT1; eauto; try lia.
  - reflexivity.
Qed.

Lemma open_tm_id_lc : forall K k t, lc_tm_at K k t ->
  forall k' u, k <= k' -> open_tm_rec k' u t = t.
Proof.
  intros K k t; revert K k; induction t as [i | x | T t IHt | t1 IHt1 t2 IHt2 | t IHt | t IHt T | n | t1 IHt1 t2 IHt2 | op t1 IHt1 t2 IHt2]; intros K k Hlc k' u Hle; simpl in *.
  - inversion Hlc; subst.
    destruct (Nat.eqb k' i) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + reflexivity.
  - reflexivity.
  - inversion Hlc; subst. f_equal. eapply IHt; eauto; try lia.
  - inversion Hlc; subst. f_equal.
    + eapply IHt1; eauto; try lia.
    + eapply IHt2; eauto; try lia.
  - inversion Hlc; subst. f_equal. eapply IHt; eauto; try lia.
  - inversion Hlc; subst. f_equal. eapply IHt; eauto; try lia.
  - reflexivity.
  - inversion Hlc; subst. f_equal.
    + eapply IHt1; eauto; try lia.
    + eapply IHt2; eauto; try lia.
  - inversion Hlc; subst. f_equal.
    + eapply IHt1; eauto; try lia.
    + eapply IHt2; eauto; try lia.
Qed.

Lemma open_tm_ty_id_lc : forall K k t, lc_tm_at K k t ->
  forall K' U, K <= K' -> open_tm_ty_rec K' U t = t.
Proof.
  intros K k t; revert K k; induction t as [i | x | T t IHt | t1 IHt1 t2 IHt2 | t IHt | t IHt T | n | t1 IHt1 t2 IHt2 | op t1 IHt1 t2 IHt2]; intros K k Hlc K' U Hle; simpl in *.
  - reflexivity.
  - reflexivity.
  - inversion Hlc; subst. f_equal.
    + eapply open_ty_id_lc; eauto; try lia.
    + eapply IHt; eauto; try lia.
  - inversion Hlc; subst. f_equal.
    + eapply IHt1; eauto; try lia.
    + eapply IHt2; eauto; try lia.
  - inversion Hlc; subst. f_equal. eapply IHt; eauto; try lia.
  - inversion Hlc; subst. f_equal.
    + eapply IHt; eauto; try lia.
    + eapply open_ty_id_lc; eauto; try lia.
  - reflexivity.
  - inversion Hlc; subst. f_equal.
    + eapply IHt1; eauto; try lia.
    + eapply IHt2; eauto; try lia.
  - inversion Hlc; subst. f_equal.
    + eapply IHt1; eauto; try lia.
    + eapply IHt2; eauto; try lia.
Qed.

(** ** Forward and inverse local closure for opening *)

Lemma locally_closed_tm_open_tm_id : forall t u k, locally_closed_tm t -> open_tm_rec k u t = t.
Proof.
  intros. apply open_tm_id_lc with (K := 0) (k := 0); auto. lia.
Qed.

Lemma locally_closed_tm_ty_subst_id : forall t K U, locally_closed_tm t -> open_tm_ty_rec K U t = t.
Proof.
  intros. apply open_tm_ty_id_lc with (K := 0) (k := 0); auto. lia.
Qed.

Lemma lc_ty_open_ty : forall K T, lc_ty_at (S K) T -> forall U,
  lc_ty_at K U -> lc_ty_at K (open_ty_rec K U T).
Proof.
  intros K T; revert K; induction T as [n | X | T1 IHT1 T2 IHT2 | T1 IHT1 |];
    intros K Hlc U HU; simpl in *.
  - inversion Hlc; subst.
    destruct (Nat.eqb K n) eqn:E.
    + apply Nat.eqb_eq in E. subst. exact HU.
    + apply lc_ty_bvar. apply Nat.eqb_neq in E. lia.
  - apply lc_ty_fvar.
  - inversion Hlc; subst. apply lc_ty_arrow.
    + eapply IHT1; eauto.
    + eapply IHT2; eauto.
  - inversion Hlc; subst. apply lc_ty_all.
    eapply IHT1.
    + eassumption.
    + apply lc_ty_mono with (K := K); auto; lia.
  - apply lc_ty_int.
Qed.

Lemma lc_ty_open_ty_inv : forall K T U, lc_ty_at K (open_ty_rec K U T) ->
  lc_ty_at K U -> lc_ty_at (S K) T.
Proof.
  intros K T; revert K; induction T as [n | X | T1 IHT1 T2 IHT2 | T1 IHT1 |];
    intros K U Hlc HU; simpl in *.
  - destruct (Nat.eqb K n) eqn:E.
    + apply Nat.eqb_eq in E. subst. apply lc_ty_bvar. lia.
    + apply lc_ty_bvar. apply Nat.eqb_neq in E. inversion Hlc; subst. lia.
  - apply lc_ty_fvar.
  - inversion Hlc; subst. apply lc_ty_arrow.
    + eapply IHT1; eauto.
    + eapply IHT2; eauto.
  - inversion Hlc; subst. apply lc_ty_all.
    eapply IHT1.
    + eassumption.
    + apply lc_ty_mono with (K := K); auto; lia.
  - apply lc_ty_int.
Qed.

Lemma lc_tm_open_tm : forall K k t, lc_tm_at K (S k) t -> forall u,
  lc_tm_at K k u -> lc_tm_at K k (open_tm_rec k u t).
Proof.
  intros K k t; revert K k;
  induction t as [i | x | T t IHt | t1 IHt1 t2 IHt2 | t IHt | t IHt T | n | t1 IHt1 t2 IHt2 | op t1 IHt1 t2 IHt2];
    intros K k Hlc u Hu; simpl in *.
  - inversion Hlc; subst.
    destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst. exact Hu.
    + apply lc_tm_bvar. apply Nat.eqb_neq in E. lia.
  - apply lc_tm_fvar.
  - inversion Hlc; subst. apply lc_tm_abs.
    + assumption.
    + eapply IHt; eauto. apply lc_tm_mono with (K := K) (k := k); auto; lia.
  - inversion Hlc; subst. apply lc_tm_app.
    + eapply IHt1; eauto.
    + eapply IHt2; eauto.
  - inversion Hlc; subst. apply lc_tm_tabs.
    eapply IHt; eauto. apply lc_tm_mono with (K := K) (k := k); auto; lia.
  - inversion Hlc; subst. apply lc_tm_tapp.
    + eapply IHt; eauto.
    + assumption.
  - apply lc_tm_int.
  - inversion Hlc; subst. apply lc_tm_div; [eapply IHt1; eauto | eapply IHt2; eauto].
  - inversion Hlc; subst. apply lc_tm_arith; [eapply IHt1; eauto | eapply IHt2; eauto].
Qed.

Lemma lc_tm_open_tm_inv : forall K k t u, lc_tm_at K k (open_tm_rec k u t) ->
  lc_tm_at K k u -> lc_tm_at K (S k) t.
Proof.
  intros K k t; revert K k;
  induction t as [i | x | T t IHt | t1 IHt1 t2 IHt2 | t IHt | t IHt T | n | t1 IHt1 t2 IHt2 | op t1 IHt1 t2 IHt2];
    intros K k u Hlc Hu; simpl in *.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst. apply lc_tm_bvar. lia.
    + apply lc_tm_bvar. apply Nat.eqb_neq in E. inversion Hlc; subst. lia.
  - apply lc_tm_fvar.
  - inversion Hlc; subst. apply lc_tm_abs.
    + assumption.
    + eapply IHt; eauto. apply lc_tm_mono with (K := K) (k := k); auto; lia.
  - inversion Hlc; subst. apply lc_tm_app.
    + eapply IHt1; eauto.
    + eapply IHt2; eauto.
  - inversion Hlc; subst. apply lc_tm_tabs.
    eapply IHt; eauto. apply lc_tm_mono with (K := K) (k := k); auto; lia.
  - inversion Hlc; subst. apply lc_tm_tapp.
    + eapply IHt; eauto.
    + assumption.
  - apply lc_tm_int.
  - inversion Hlc; subst. apply lc_tm_div; [eapply IHt1; eauto | eapply IHt2; eauto].
  - inversion Hlc; subst. apply lc_tm_arith; [eapply IHt1; eauto | eapply IHt2; eauto].
Qed.

Lemma lc_tm_open_ty : forall K k t, lc_tm_at (S K) k t -> forall U,
  lc_ty_at K U -> lc_tm_at K k (open_tm_ty_rec K U t).
Proof.
  intros K k t; revert K k;
  induction t as [i | x | T t IHt | t1 IHt1 t2 IHt2 | t IHt | t IHt T | n | t1 IHt1 t2 IHt2 | op t1 IHt1 t2 IHt2];
    intros K k Hlc U HU; simpl in *.
  - apply lc_tm_bvar. inversion Hlc; subst. lia.
  - apply lc_tm_fvar.
  - inversion Hlc; subst. apply lc_tm_abs.
    + eapply lc_ty_open_ty; eauto.
    + eapply IHt; eauto.
  - inversion Hlc; subst. apply lc_tm_app; [eapply IHt1; eauto | eapply IHt2; eauto].
  - inversion Hlc; subst. apply lc_tm_tabs.
    eapply IHt; eauto. apply lc_ty_mono with (K := K); auto; lia.
  - inversion Hlc; subst. apply lc_tm_tapp.
    + eapply IHt; eauto.
    + eapply lc_ty_open_ty; eauto.
  - apply lc_tm_int.
  - inversion Hlc; subst. apply lc_tm_div; [eapply IHt1; eauto | eapply IHt2; eauto].
  - inversion Hlc; subst. apply lc_tm_arith; [eapply IHt1; eauto | eapply IHt2; eauto].
Qed.

Lemma lc_tm_open_ty_inv : forall K k t U, lc_tm_at K k (open_tm_ty_rec K U t) ->
  lc_ty_at K U -> lc_tm_at (S K) k t.
Proof.
  intros K k t; revert K k;
  induction t as [i | x | T t IHt | t1 IHt1 t2 IHt2 | t IHt | t IHt T | n | t1 IHt1 t2 IHt2 | op t1 IHt1 t2 IHt2];
    intros K k U Hlc HU; simpl in *.
  - apply lc_tm_bvar. inversion Hlc; subst. lia.
  - apply lc_tm_fvar.
  - inversion Hlc; subst. apply lc_tm_abs.
    + eapply lc_ty_open_ty_inv; eauto.
    + eapply IHt; eauto.
  - inversion Hlc; subst. apply lc_tm_app; [eapply IHt1; eauto | eapply IHt2; eauto].
  - inversion Hlc; subst. apply lc_tm_tabs.
    eapply IHt; eauto. apply lc_ty_mono with (K := K); auto; lia.
  - inversion Hlc; subst. apply lc_tm_tapp.
    + eapply IHt; eauto.
    + eapply lc_ty_open_ty_inv; eauto.
  - apply lc_tm_int.
  - inversion Hlc; subst. apply lc_tm_div; [eapply IHt1; eauto | eapply IHt2; eauto].
  - inversion Hlc; subst. apply lc_tm_arith; [eapply IHt1; eauto | eapply IHt2; eauto].
Qed.

(** ** Local closure under substitutions *)

Lemma lc_ty_ty_subst_atoms : forall K T, lc_ty_at K T ->
  forall sg, (forall X, lc_ty_at 0 (sg X)) -> lc_ty_at K (ty_subst_atoms sg T).
Proof.
  intros K T; revert K; induction T as [n | X | T1 IHT1 T2 IHT2 | T1 IHT1 |];
    intros K Hlc sg Hsg; simpl in *.
  - assumption.
  - apply lc_ty_mono with (K := 0); auto. lia.
  - inversion Hlc; subst. apply lc_ty_arrow; [eapply IHT1; eauto | eapply IHT2; eauto].
  - inversion Hlc; subst. apply lc_ty_all. eapply IHT1; eauto.
  - apply lc_ty_int.
Qed.

Lemma lc_tm_tm_ty_subst_atoms : forall K k t, lc_tm_at K k t ->
  forall sg, (forall X, lc_ty_at 0 (sg X)) -> lc_tm_at K k (tm_ty_subst_atoms sg t).
Proof.
  intros K k t; revert K k;
  induction t as [i | x | T t IHt | t1 IHt1 t2 IHt2 | t IHt | t IHt T | n | t1 IHt1 t2 IHt2 | op t1 IHt1 t2 IHt2];
    intros K k Hlc sg Hsg; simpl in *.
  - assumption.
  - apply lc_tm_fvar.
  - inversion Hlc; subst. apply lc_tm_abs.
    + eapply lc_ty_ty_subst_atoms; eauto.
    + eapply IHt; eauto.
  - inversion Hlc; subst. apply lc_tm_app; [eapply IHt1; eauto | eapply IHt2; eauto].
  - inversion Hlc; subst. apply lc_tm_tabs. eapply IHt; eauto.
  - inversion Hlc; subst. apply lc_tm_tapp.
    + eapply IHt; eauto.
    + eapply lc_ty_ty_subst_atoms; eauto.
  - apply lc_tm_int.
  - inversion Hlc; subst. apply lc_tm_div; [eapply IHt1; eauto | eapply IHt2; eauto].
  - inversion Hlc; subst. apply lc_tm_arith; [eapply IHt1; eauto | eapply IHt2; eauto].
Qed.

Lemma lc_tm_tsubst : forall K k t, lc_tm_at K k t ->
  forall s, (forall x, lc_tm_at 0 0 (s x)) -> lc_tm_at K k (tsubst s t).
Proof.
  intros K k t; revert K k;
  induction t as [i | x | T t IHt | t1 IHt1 t2 IHt2 | t IHt | t IHt T | n | t1 IHt1 t2 IHt2 | op t1 IHt1 t2 IHt2];
    intros K k Hlc s Hs; simpl in *.
  - assumption.
  - apply lc_tm_mono with (K := 0) (k := 0); auto; lia.
  - inversion Hlc; subst. apply lc_tm_abs.
    + assumption.
    + eapply IHt; eauto.
  - inversion Hlc; subst. apply lc_tm_app; [eapply IHt1; eauto | eapply IHt2; eauto].
  - inversion Hlc; subst. apply lc_tm_tabs. eapply IHt; eauto.
  - inversion Hlc; subst. apply lc_tm_tapp.
    + eapply IHt; eauto.
    + assumption.
  - apply lc_tm_int.
  - inversion Hlc; subst. apply lc_tm_div; [eapply IHt1; eauto | eapply IHt2; eauto].
  - inversion Hlc; subst. apply lc_tm_arith; [eapply IHt1; eauto | eapply IHt2; eauto].
Qed.

(** ** Free type atoms of qualifiers and refinement types *)

Fixpoint q_ftv (q : qualifier) : list atom :=
  match q with
  | Pred_True | Pred_False => []
  | Pred_Eq t1 t2 | Pred_Lt t1 t2 | Pred_Le t1 t2 => ftv_tm t1 ++ ftv_tm t2
  | Pred_And p1 p2 | Pred_Or p1 p2 => q_ftv p1 ++ q_ftv p2
  | Pred_Not p1 => q_ftv p1
  end.

Fixpoint q_fv (q : qualifier) : list atom :=
  match q with
  | Pred_True | Pred_False => []
  | Pred_Eq t1 t2 | Pred_Lt t1 t2 | Pred_Le t1 t2 => fv_tm t1 ++ fv_tm t2
  | Pred_And p1 p2 | Pred_Or p1 p2 => q_fv p1 ++ q_fv p2
  | Pred_Not p1 => q_fv p1
  end.

Fixpoint rty_ftv (R : rty) : list atom :=
  match R with
  | R_Refine T ps => fv_ty T ++ q_ftv ps
  | R_Func R1 R2 => rty_ftv R1 ++ rty_ftv R2
  | R_Exists R1 R2 => rty_ftv R1 ++ rty_ftv R2
  | R_Poly R1 => rty_ftv R1
  end.

Fixpoint rty_fv (R : rty) : list atom :=
  match R with
  | R_Refine T ps => q_fv ps
  | R_Func R1 R2 => rty_fv R1 ++ rty_fv R2
  | R_Exists R1 R2 => rty_fv R1 ++ rty_fv R2
  | R_Poly R1 => rty_fv R1
  end.

Lemma ty_subst_atoms_fv_nil : forall sg T,
  (forall X, fv_ty (sg X) = []) -> fv_ty (ty_subst_atoms sg T) = [].
Proof.
  intros sg T; revert T; induction T as [n | X | T1 IH1 T2 IH2 | T1 IH1 |]; intros H; simpl.
  - reflexivity.
  - apply H.
  - rewrite IH1; [|exact H]. rewrite IH2; [|exact H]. reflexivity.
  - apply IH1. exact H.
  - reflexivity.
Qed.

Lemma tm_ty_subst_atoms_ftv_nil : forall sg t,
  (forall X, fv_ty (sg X) = []) -> ftv_tm (tm_ty_subst_atoms sg t) = [].
Proof.
  intros sg t; revert t.
  induction t as [i | x | T t IHt | t1 IHt1 t2 IHt2 | t IHt | t IHt T | n | t1 IHt1 t2 IHt2 | op t1 IHt1 t2 IHt2];
    intros H; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite ty_subst_atoms_fv_nil; [|exact H]. rewrite IHt; [|exact H]. reflexivity.
  - rewrite IHt1; [|exact H]. rewrite IHt2; [|exact H]. reflexivity.
  - rewrite IHt; [|exact H]. reflexivity.
  - rewrite IHt; [|exact H]. rewrite ty_subst_atoms_fv_nil; [|exact H]. reflexivity.
  - reflexivity.
  - rewrite IHt1; [|exact H]. rewrite IHt2; [|exact H]. reflexivity.
  - rewrite IHt1; [|exact H]. rewrite IHt2; [|exact H]. reflexivity.
Qed.

Lemma q_ty_subst_atoms_ftv_nil : forall sg q,
  (forall X, fv_ty (sg X) = []) -> q_ftv (q_ty_subst_atoms sg q) = [].
Proof.
  intros sg q; revert q. induction q; intros H; simpl.
  - reflexivity. - reflexivity.
  - rewrite tm_ty_subst_atoms_ftv_nil; [|exact H].
    rewrite tm_ty_subst_atoms_ftv_nil; [|exact H]. reflexivity.
  - rewrite tm_ty_subst_atoms_ftv_nil; [|exact H].
    rewrite tm_ty_subst_atoms_ftv_nil; [|exact H]. reflexivity.
  - rewrite tm_ty_subst_atoms_ftv_nil; [|exact H].
    rewrite tm_ty_subst_atoms_ftv_nil; [|exact H]. reflexivity.
  - rewrite IHq1; [|exact H]. rewrite IHq2; [|exact H]. reflexivity.
  - rewrite IHq1; [|exact H]. rewrite IHq2; [|exact H]. reflexivity.
  - rewrite IHq; [|exact H]. reflexivity.
Qed.

Lemma rty_ty_subst_atoms_ftv_nil : forall sg R,
  (forall X, fv_ty (sg X) = []) -> rty_ftv (rty_ty_subst_atoms sg R) = [].
Proof.
  intros sg R; revert R. induction R; intros H; simpl.
  - rewrite ty_subst_atoms_fv_nil; [|exact H].
    rewrite q_ty_subst_atoms_ftv_nil; [|exact H]. reflexivity.
  - rewrite IHR1; [|exact H]. rewrite IHR2; [|exact H]. reflexivity.
  - rewrite IHR1; [|exact H]. rewrite IHR2; [|exact H]. reflexivity.
  - apply IHR. exact H.
Qed.

Lemma ftv_tm_tsubst : forall s t,
  (forall x, ftv_tm (s x) = []) -> ftv_tm (tsubst s t) = ftv_tm t.
Proof.
  intros s t; revert t.
  induction t as [i | x | T t IHt | t1 IHt1 t2 IHt2 | t IHt | t IHt T | n | t1 IHt1 t2 IHt2 | op t1 IHt1 t2 IHt2];
    intros H; simpl.
  - reflexivity.
  - apply H.
  - rewrite IHt; [|exact H]. reflexivity.
  - rewrite IHt1; [|exact H]. rewrite IHt2; [|exact H]. reflexivity.
  - rewrite IHt; [|exact H]. reflexivity.
  - rewrite IHt; [|exact H]. reflexivity.
  - reflexivity.
  - rewrite IHt1; [|exact H]. rewrite IHt2; [|exact H]. reflexivity.
  - rewrite IHt1; [|exact H]. rewrite IHt2; [|exact H]. reflexivity.
Qed.

Lemma qsubst_ftv : forall s q,
  (forall x, ftv_tm (s x) = []) -> q_ftv (qsubst s q) = q_ftv q.
Proof.
  intros s q; revert q. induction q; intros H; simpl.
  - reflexivity. - reflexivity.
  - rewrite ftv_tm_tsubst; [|exact H]. rewrite ftv_tm_tsubst; [|exact H]. reflexivity.
  - rewrite ftv_tm_tsubst; [|exact H]. rewrite ftv_tm_tsubst; [|exact H]. reflexivity.
  - rewrite ftv_tm_tsubst; [|exact H]. rewrite ftv_tm_tsubst; [|exact H]. reflexivity.
  - rewrite IHq1; [|exact H]. rewrite IHq2; [|exact H]. reflexivity.
  - rewrite IHq1; [|exact H]. rewrite IHq2; [|exact H]. reflexivity.
  - rewrite IHq; [|exact H]. reflexivity.
Qed.

Lemma rty_subst_env_ftv : forall s R,
  (forall x, ftv_tm (s x) = []) -> rty_ftv (rty_subst_env s R) = rty_ftv R.
Proof.
  intros s R; revert R. induction R; intros H; simpl.
  - rewrite qsubst_ftv; [|exact H]. reflexivity.
  - rewrite IHR1; [|exact H]. rewrite IHR2; [|exact H]. reflexivity.
  - rewrite IHR1; [|exact H]. rewrite IHR2; [|exact H]. reflexivity.
  - rewrite IHR; [|exact H]. reflexivity.
Qed.

Lemma fv_tm_tm_ty_subst_atoms : forall sg t, fv_tm (tm_ty_subst_atoms sg t) = fv_tm t.
Proof.
  intros sg t; revert t.
  induction t as [i | x | T t IHt | t1 IHt1 t2 IHt2 | t IHt | t IHt T | n | t1 IHt1 t2 IHt2 | op t1 IHt1 t2 IHt2];
    simpl; auto; try (rewrite IHt1, IHt2; reflexivity).
Qed.

Lemma q_ty_subst_atoms_fv : forall sg q, q_fv (q_ty_subst_atoms sg q) = q_fv q.
Proof.
  intros sg q; revert q. induction q; simpl.
  - reflexivity. - reflexivity.
  - rewrite !fv_tm_tm_ty_subst_atoms. reflexivity.
  - rewrite !fv_tm_tm_ty_subst_atoms. reflexivity.
  - rewrite !fv_tm_tm_ty_subst_atoms. reflexivity.
  - rewrite IHq1, IHq2. reflexivity.
  - rewrite IHq1, IHq2. reflexivity.
  - rewrite IHq. reflexivity.
Qed.

(** ** Identity of substitutions on closed qualifiers/terms *)

Lemma tsubst_id_of_closed : forall t, fv_tm t = [] -> forall s, tsubst s t = t.
Proof.
  intros t; revert t.
  induction t as [i | x | T t IHt | t1 IHt1 t2 IHt2 | t IHt | t IHt T | n | t1 IHt1 t2 IHt2 | op t1 IHt1 t2 IHt2];
    intros H s; simpl in *.
  - reflexivity.
  - simpl in H. discriminate H.
  - f_equal. apply IHt. simpl in H. apply H.
  - apply app_eq_nil in H. destruct H as [H1 H2]. f_equal; [apply IHt1; exact H1 | apply IHt2; exact H2].
  - f_equal. apply IHt. exact H.
  - f_equal. apply IHt. simpl in H. exact H.
  - reflexivity.
  - apply app_eq_nil in H. destruct H as [H1 H2]. f_equal; [apply IHt1; exact H1 | apply IHt2; exact H2].
  - apply app_eq_nil in H. destruct H as [H1 H2]. f_equal; [apply IHt1; exact H1 | apply IHt2; exact H2].
Qed.

Lemma ty_subst_atoms_id_of_closed : forall T, fv_ty T = [] -> forall sg, ty_subst_atoms sg T = T.
Proof.
  intros T; revert T.
  induction T as [n | X | T1 IH1 T2 IH2 | T1 IH1 |]; intros H sg; simpl in *.
  - reflexivity.
  - simpl in H. discriminate H.
  - apply app_eq_nil in H. destruct H as [H1 H2]. rewrite IH1; [|exact H1]. rewrite IH2; [|exact H2]. reflexivity.
  - f_equal. apply IH1. exact H.
  - reflexivity.
Qed.

Lemma tm_ty_subst_atoms_id_of_closed : forall t, ftv_tm t = [] -> forall sg, tm_ty_subst_atoms sg t = t.
Proof.
  intros t; revert t.
  induction t as [i | x | T t IHt | t1 IHt1 t2 IHt2 | t IHt | t IHt T | n | t1 IHt1 t2 IHt2 | op t1 IHt1 t2 IHt2];
    intros H sg; simpl in *.
  - reflexivity. - reflexivity.
  - rewrite ty_subst_atoms_id_of_closed; [|apply app_eq_nil in H; tauto]. f_equal. apply IHt. apply app_eq_nil in H; tauto.
  - apply app_eq_nil in H. destruct H as [H1 H2]. f_equal; [apply IHt1; exact H1 | apply IHt2; exact H2].
  - f_equal. apply IHt. exact H.
  - apply app_eq_nil in H. destruct H as [H1 H2]. f_equal.
    + apply IHt; exact H1.
    + apply ty_subst_atoms_id_of_closed; exact H2.
  - reflexivity.
  - apply app_eq_nil in H. destruct H as [H1 H2]. f_equal; [apply IHt1; exact H1 | apply IHt2; exact H2].
  - apply app_eq_nil in H. destruct H as [H1 H2]. f_equal; [apply IHt1; exact H1 | apply IHt2; exact H2].
Qed.

Lemma qsubst_id_of_closed : forall q, q_fv q = [] -> forall s, qsubst s q = q.
Proof.
  intros q; revert q. induction q; intros H s; simpl in *.
  - reflexivity. - reflexivity.
  - apply app_eq_nil in H. destruct H as [H1 H2]. f_equal; [apply tsubst_id_of_closed; exact H1 | apply tsubst_id_of_closed; exact H2].
  - apply app_eq_nil in H. destruct H as [H1 H2]. f_equal; [apply tsubst_id_of_closed; exact H1 | apply tsubst_id_of_closed; exact H2].
  - apply app_eq_nil in H. destruct H as [H1 H2]. f_equal; [apply tsubst_id_of_closed; exact H1 | apply tsubst_id_of_closed; exact H2].
  - apply app_eq_nil in H. destruct H as [H1 H2]. f_equal; [apply IHq1; exact H1 | apply IHq2; exact H2].
  - apply app_eq_nil in H. destruct H as [H1 H2]. f_equal; [apply IHq1; exact H1 | apply IHq2; exact H2].
  - f_equal. apply IHq. exact H.
Qed.

Lemma q_ty_subst_atoms_id_of_closed : forall q, q_ftv q = [] -> forall sg, q_ty_subst_atoms sg q = q.
Proof.
  intros q; revert q. induction q; intros H sg; simpl in *.
  - reflexivity. - reflexivity.
  - apply app_eq_nil in H. destruct H as [H1 H2]. f_equal; [apply tm_ty_subst_atoms_id_of_closed; exact H1 | apply tm_ty_subst_atoms_id_of_closed; exact H2].
  - apply app_eq_nil in H. destruct H as [H1 H2]. f_equal; [apply tm_ty_subst_atoms_id_of_closed; exact H1 | apply tm_ty_subst_atoms_id_of_closed; exact H2].
  - apply app_eq_nil in H. destruct H as [H1 H2]. f_equal; [apply tm_ty_subst_atoms_id_of_closed; exact H1 | apply tm_ty_subst_atoms_id_of_closed; exact H2].
  - apply app_eq_nil in H. destruct H as [H1 H2]. f_equal; [apply IHq1; exact H1 | apply IHq2; exact H2].
  - apply app_eq_nil in H. destruct H as [H1 H2]. f_equal; [apply IHq1; exact H1 | apply IHq2; exact H2].
  - f_equal. apply IHq. exact H.
Qed.

Lemma rty_subst_env_id_of_closed : forall R, rty_fv R = [] -> forall s, rty_subst_env s R = R.
Proof.
  intros R; revert R. induction R; intros H s; simpl in *.
  - rewrite qsubst_id_of_closed; auto.
  - apply app_eq_nil in H. destruct H as [H1 H2]. f_equal; [apply IHR1; exact H1 | apply IHR2; exact H2].
  - apply app_eq_nil in H. destruct H as [H1 H2]. f_equal; [apply IHR1; exact H1 | apply IHR2; exact H2].
  - f_equal. apply IHR. exact H.
Qed.

Lemma rty_ty_subst_atoms_id_of_closed : forall R, rty_ftv R = [] -> forall sg, rty_ty_subst_atoms sg R = R.
Proof.
  intros R; revert R. induction R; intros H sg; simpl in *.
  - apply app_eq_nil in H. destruct H as [H1 H2]. f_equal.
    + apply ty_subst_atoms_id_of_closed; exact H1.
    + apply q_ty_subst_atoms_id_of_closed; exact H2.
  - apply app_eq_nil in H. destruct H as [H1 H2]. f_equal; [apply IHR1; exact H1 | apply IHR2; exact H2].
  - apply app_eq_nil in H. destruct H as [H1 H2]. f_equal; [apply IHR1; exact H1 | apply IHR2; exact H2].
  - f_equal. apply IHR. exact H.
Qed.

(** ** Commutation of substitutions and openings *)

Lemma tsubst_open_tm_rec : forall s, (forall x, locally_closed_tm (s x)) ->
  forall k t u, tsubst s (open_tm_rec k u t) = open_tm_rec k (tsubst s u) (tsubst s t).
Proof.
  intros s Hs k t. revert k.
  induction t as [i | x | T t IHt | t1 IHt1 t2 IHt2 | t IHt | t IHt T | n | t1 IHt1 t2 IHt2 | op t1 IHt1 t2 IHt2];
    intros k u; simpl.
  - destruct (Nat.eqb k i); reflexivity.
  - symmetry. apply locally_closed_tm_open_tm_id. apply Hs.
  - f_equal. apply IHt.
  - f_equal; [apply IHt1 | apply IHt2].
  - f_equal. apply IHt.
  - f_equal. apply IHt.
  - reflexivity.
  - f_equal; [apply IHt1 | apply IHt2].
  - f_equal; [apply IHt1 | apply IHt2].
Qed.

Lemma tm_ty_subst_atoms_open_tm_rec : forall sg k t u,
  tm_ty_subst_atoms sg (open_tm_rec k u t) =
  open_tm_rec k (tm_ty_subst_atoms sg u) (tm_ty_subst_atoms sg t).
Proof.
  intros sg k t. revert k.
  induction t as [i | x | T t IHt | t1 IHt1 t2 IHt2 | t IHt | t IHt T | n | t1 IHt1 t2 IHt2 | op t1 IHt1 t2 IHt2];
    intros k u; simpl.
  - destruct (Nat.eqb k i); reflexivity.
  - reflexivity.
  - f_equal. apply IHt.
  - f_equal; [apply IHt1 | apply IHt2].
  - f_equal. apply IHt.
  - f_equal. apply IHt.
  - reflexivity.
  - f_equal; [apply IHt1 | apply IHt2].
  - f_equal; [apply IHt1 | apply IHt2].
Qed.

Lemma ty_subst_atoms_open_ty_rec : forall sg,
  (forall X, locally_closed_ty (sg X)) -> forall k T U,
  ty_subst_atoms sg (open_ty_rec k U T) =
  open_ty_rec k (ty_subst_atoms sg U) (ty_subst_atoms sg T).
Proof.
  intros sg Hsg k T. revert k.
  induction T as [n | X | T1 IH1 T2 IH2 | T1 IH1 |]; intros k U; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. eapply open_ty_id_lc; [apply Hsg | lia].
  - f_equal; [apply IH1 | apply IH2].
  - f_equal. apply IH1.
  - reflexivity.
Qed.

Lemma tm_ty_subst_atoms_open_tm_ty_rec : forall sg,
  (forall X, locally_closed_ty (sg X)) -> forall k t U,
  tm_ty_subst_atoms sg (open_tm_ty_rec k U t) =
  open_tm_ty_rec k (ty_subst_atoms sg U) (tm_ty_subst_atoms sg t).
Proof.
  intros sg Hsg k t. revert k.
  induction t as [i | x | T t IHt | t1 IHt1 t2 IHt2 | t IHt | t IHt T | n | t1 IHt1 t2 IHt2 | op t1 IHt1 t2 IHt2];
    intros k U; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + apply ty_subst_atoms_open_ty_rec; auto.
    + apply IHt.
  - f_equal; [apply IHt1 | apply IHt2].
  - f_equal. apply IHt.
  - f_equal.
    + apply IHt.
    + apply ty_subst_atoms_open_ty_rec; auto.
  - reflexivity.
  - f_equal; [apply IHt1 | apply IHt2].
  - f_equal; [apply IHt1 | apply IHt2].
Qed.

Lemma tsubst_open_tm_ty_rec : forall s, (forall x, locally_closed_tm (s x)) ->
  forall k t U, tsubst s (open_tm_ty_rec k U t) = open_tm_ty_rec k U (tsubst s t).
Proof.
  intros s Hs k t. revert k.
  induction t as [i | x | T t IHt | t1 IHt1 t2 IHt2 | t IHt | t IHt T | n | t1 IHt1 t2 IHt2 | op t1 IHt1 t2 IHt2];
    intros k U; simpl.
  - reflexivity.
  - symmetry. apply locally_closed_tm_ty_subst_id. apply Hs.
  - f_equal. apply IHt.
  - f_equal; [apply IHt1 | apply IHt2].
  - f_equal. apply IHt.
  - f_equal. apply IHt.
  - reflexivity.
  - f_equal; [apply IHt1 | apply IHt2].
  - f_equal; [apply IHt1 | apply IHt2].
Qed.

Lemma qsubst_open_pred_tm_rec : forall s, (forall x, locally_closed_tm (s x)) ->
  forall k u q,
  qsubst s (open_pred_tm_rec k u q) = open_pred_tm_rec k (tsubst s u) (qsubst s q).
Proof.
  intros s Hs k u q. revert k u.
  induction q; intros k u; simpl.
  - reflexivity. - reflexivity.
  - f_equal; [apply tsubst_open_tm_rec; auto | apply tsubst_open_tm_rec; auto].
  - f_equal; [apply tsubst_open_tm_rec; auto | apply tsubst_open_tm_rec; auto].
  - f_equal; [apply tsubst_open_tm_rec; auto | apply tsubst_open_tm_rec; auto].
  - f_equal; [apply IHq1 | apply IHq2].
  - f_equal; [apply IHq1 | apply IHq2].
  - f_equal. apply IHq.
Qed.

Lemma qsubst_open_pred_ty_rec : forall s,
  (forall x, locally_closed_tm (s x)) -> forall k U q,
  qsubst s (open_pred_ty_rec k U q) = open_pred_ty_rec k U (qsubst s q).
Proof.
  intros s Hs k U q. revert k U.
  induction q; intros k U; simpl.
  - reflexivity. - reflexivity.
  - f_equal; [apply tsubst_open_tm_ty_rec; auto | apply tsubst_open_tm_ty_rec; auto].
  - f_equal; [apply tsubst_open_tm_ty_rec; auto | apply tsubst_open_tm_ty_rec; auto].
  - f_equal; [apply tsubst_open_tm_ty_rec; auto | apply tsubst_open_tm_ty_rec; auto].
  - f_equal; [apply IHq1 | apply IHq2].
  - f_equal; [apply IHq1 | apply IHq2].
  - f_equal. apply IHq.
Qed.

Lemma q_ty_subst_atoms_open_pred_tm_rec : forall sg k u q,
  q_ty_subst_atoms sg (open_pred_tm_rec k u q) =
  open_pred_tm_rec k (tm_ty_subst_atoms sg u) (q_ty_subst_atoms sg q).
Proof.
  intros sg k u q. revert k u.
  induction q; intros k u; simpl.
  - reflexivity. - reflexivity.
  - f_equal; [apply tm_ty_subst_atoms_open_tm_rec | apply tm_ty_subst_atoms_open_tm_rec].
  - f_equal; [apply tm_ty_subst_atoms_open_tm_rec | apply tm_ty_subst_atoms_open_tm_rec].
  - f_equal; [apply tm_ty_subst_atoms_open_tm_rec | apply tm_ty_subst_atoms_open_tm_rec].
  - f_equal; [apply IHq1 | apply IHq2].
  - f_equal; [apply IHq1 | apply IHq2].
  - f_equal. apply IHq.
Qed.

Lemma q_ty_subst_atoms_open_pred_ty_rec : forall sg,
  (forall X, locally_closed_ty (sg X)) -> forall k U q,
  q_ty_subst_atoms sg (open_pred_ty_rec k U q) =
  open_pred_ty_rec k (ty_subst_atoms sg U) (q_ty_subst_atoms sg q).
Proof.
  intros sg Hsg k U q. revert k U.
  induction q; intros k U; simpl.
  - reflexivity. - reflexivity.
  - f_equal; [apply tm_ty_subst_atoms_open_tm_ty_rec; auto | apply tm_ty_subst_atoms_open_tm_ty_rec; auto].
  - f_equal; [apply tm_ty_subst_atoms_open_tm_ty_rec; auto | apply tm_ty_subst_atoms_open_tm_ty_rec; auto].
  - f_equal; [apply tm_ty_subst_atoms_open_tm_ty_rec; auto | apply tm_ty_subst_atoms_open_tm_ty_rec; auto].
  - f_equal; [apply IHq1 | apply IHq2].
  - f_equal; [apply IHq1 | apply IHq2].
  - f_equal. apply IHq.
Qed.

Lemma tsubst_tm_ty_subst_atoms : forall s,
  (forall x, ftv_tm (s x) = []) -> forall sg t,
  tsubst s (tm_ty_subst_atoms sg t) = tm_ty_subst_atoms sg (tsubst s t).
Proof.
  intros s Hs sg t. revert t.
  induction t as [i | x | T t IHt | t1 IHt1 t2 IHt2 | t IHt | t IHt T | n | t1 IHt1 t2 IHt2 | op t1 IHt1 t2 IHt2];
    simpl.
  - reflexivity.
  - symmetry. apply tm_ty_subst_atoms_id_of_closed. apply Hs.
  - f_equal. apply IHt.
  - f_equal; [apply IHt1 | apply IHt2].
  - f_equal. apply IHt.
  - f_equal. apply IHt.
  - reflexivity.
  - f_equal; [apply IHt1 | apply IHt2].
  - f_equal; [apply IHt1 | apply IHt2].
Qed.

Lemma qsubst_q_ty_subst_atoms : forall s,
  (forall x, ftv_tm (s x) = []) -> forall sg q,
  qsubst s (q_ty_subst_atoms sg q) = q_ty_subst_atoms sg (qsubst s q).
Proof.
  intros s Hs sg q. revert q.
  induction q; simpl.
  - reflexivity. - reflexivity.
  - f_equal; [apply tsubst_tm_ty_subst_atoms; auto | apply tsubst_tm_ty_subst_atoms; auto].
  - f_equal; [apply tsubst_tm_ty_subst_atoms; auto | apply tsubst_tm_ty_subst_atoms; auto].
  - f_equal; [apply tsubst_tm_ty_subst_atoms; auto | apply tsubst_tm_ty_subst_atoms; auto].
  - f_equal; [apply IHq1 | apply IHq2].
  - f_equal; [apply IHq1 | apply IHq2].
  - f_equal. apply IHq.
Qed.

Lemma rty_subst_env_rty_ty_subst_atoms : forall s,
  (forall x, ftv_tm (s x) = []) -> forall sg R,
  rty_subst_env s (rty_ty_subst_atoms sg R) = rty_ty_subst_atoms sg (rty_subst_env s R).
Proof.
  intros s Hs sg R. revert R.
  induction R; simpl.
  - f_equal. apply qsubst_q_ty_subst_atoms. auto.
  - f_equal; [apply IHR1 | apply IHR2].
  - f_equal; [apply IHR1 | apply IHR2].
  - f_equal. apply IHR.
Qed.

Lemma rty_subst_env_open_rty_tm_rec : forall s,
  (forall x, locally_closed_tm (s x)) -> forall k u R,
  rty_subst_env s (open_rty_tm_rec k u R) =
  open_rty_tm_rec k (tsubst s u) (rty_subst_env s R).
Proof.
  intros s Hs k u R. revert k u.
  induction R; intros k u; simpl.
  - f_equal. apply qsubst_open_pred_tm_rec. auto.
  - f_equal; [apply IHR1 | apply IHR2].
  - f_equal; [apply IHR1 | apply IHR2].
  - f_equal. apply IHR.
Qed.

Lemma rty_subst_env_open_rty_ty_rec : forall s,
  (forall x, locally_closed_tm (s x)) -> forall k U R,
  rty_subst_env s (open_rty_ty_rec k U R) =
  open_rty_ty_rec k U (rty_subst_env s R).
Proof.
  intros s Hs k U R. revert k U.
  induction R; intros k U; simpl.
  - f_equal. apply qsubst_open_pred_ty_rec. auto.
  - f_equal; [apply IHR1 | apply IHR2].
  - f_equal; [apply IHR1 | apply IHR2].
  - f_equal. apply IHR.
Qed.

Lemma rty_ty_subst_atoms_open_rty_tm_rec : forall sg k u R,
  rty_ty_subst_atoms sg (open_rty_tm_rec k u R) =
  open_rty_tm_rec k (tm_ty_subst_atoms sg u) (rty_ty_subst_atoms sg R).
Proof.
  intros sg k u R. revert k u.
  induction R; intros k u; simpl.
  - f_equal. apply q_ty_subst_atoms_open_pred_tm_rec.
  - f_equal; [apply IHR1 | apply IHR2].
  - f_equal; [apply IHR1 | apply IHR2].
  - f_equal. apply IHR.
Qed.

Lemma rty_ty_subst_atoms_open_rty_ty_rec : forall sg,
  (forall X, locally_closed_ty (sg X)) -> forall k U R,
  rty_ty_subst_atoms sg (open_rty_ty_rec k U R) =
  open_rty_ty_rec k (ty_subst_atoms sg U) (rty_ty_subst_atoms sg R).
Proof.
  intros sg Hsg k U R. revert k U.
  induction R; intros k U; simpl.
  - f_equal.
    + apply ty_subst_atoms_open_ty_rec; auto.
    + apply q_ty_subst_atoms_open_pred_ty_rec; auto.
  - f_equal; [apply IHR1 | apply IHR2].
  - f_equal; [apply IHR1 | apply IHR2].
  - f_equal. apply IHR.
Qed.

(** ** Erasure and size are invariant under substitution/opening *)

Lemma erase_rty_subst_env : forall s R, erase (rty_subst_env s R) = erase R.
Proof.
  intros s R. revert R. induction R; simpl.
  - reflexivity.
  - f_equal; [apply IHR1 | apply IHR2].
  - apply IHR2.
  - f_equal. apply IHR.
Qed.

Lemma erase_rty_ty_subst_atoms : forall sg R,
  erase (rty_ty_subst_atoms sg R) = ty_subst_atoms sg (erase R).
Proof.
  intros sg R. revert R. induction R; simpl.
  - reflexivity.
  - f_equal; [apply IHR1 | apply IHR2].
  - apply IHR2.
  - f_equal. apply IHR.
Qed.

Lemma erase_open_rty_tm_rec : forall k u R, erase (open_rty_tm_rec k u R) = erase R.
Proof.
  intros k u R. revert k u. induction R; intros k u; simpl.
  - reflexivity.
  - f_equal; [apply IHR1 | apply IHR2].
  - apply IHR2.
  - f_equal. apply IHR.
Qed.

Lemma erase_open_rty_ty_rec : forall k U R,
  erase (open_rty_ty_rec k U R) = open_ty_rec k U (erase R).
Proof.
  intros k U R. revert k U. induction R; intros k U; simpl.
  - reflexivity.
  - f_equal; [apply IHR1 | apply IHR2].
  - apply IHR2.
  - f_equal. apply IHR.
Qed.

Lemma rty_size_rty_subst_env : forall s R, rty_size (rty_subst_env s R) = rty_size R.
Proof.
  intros s R. revert R. induction R; simpl.
  - reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR. reflexivity.
Qed.

Lemma rty_size_rty_ty_subst_atoms : forall sg R, rty_size (rty_ty_subst_atoms sg R) = rty_size R.
Proof.
  intros sg R. revert R. induction R; simpl.
  - reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR. reflexivity.
Qed.

Lemma rty_size_open_rty_tm_rec : forall k u R, rty_size (open_rty_tm_rec k u R) = rty_size R.
Proof.
  intros k u R. revert k u. induction R; intros k u; simpl.
  - reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR. reflexivity.
Qed.

Lemma rty_size_open_rty_ty_rec : forall k U R, rty_size (open_rty_ty_rec k U R) = rty_size R.
Proof.
  intros k U R. revert k U. induction R; intros k U; simpl.
  - reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR. reflexivity.
Qed.

End SystemFRefinementLib2.

Module SystemFRefinementStep.
Import ListNotations SystemFRefinement SystemFRefinementLogic SystemFRefinementTyping SystemFRefinementEvaluation SystemFRefinementLib SystemFRefinementLib2.

Lemma value_no_step : forall t, value t -> forall t', ~ step t t'.
Proof.
  intros t Hv. induction Hv; intros t' Hstep; inversion Hstep.
Qed.

Lemma value_lc : forall t, value t -> locally_closed_tm t.
Proof. intros t Hv. induction Hv; try assumption. apply lc_tm_int. Qed.

Hint Constructors value : core.
Hint Resolve value_no_step : core.

Ltac solve_contr :=
  exfalso;
  match goal with
  | Hv : value ?v, Hs : step ?v ?u |- _ =>
      apply value_no_step with (t := v) (t' := u); [exact Hv | exact Hs]
  | Hlc : locally_closed_tm (tm_abs ?T ?b), Hs : step (tm_abs ?T ?b) ?u |- _ =>
      apply value_no_step with (t := tm_abs T b) (t' := u); [apply v_abs; exact Hlc | exact Hs]
  | Hlc : locally_closed_tm (tm_tabs ?b), Hs : step (tm_tabs ?b) ?u |- _ =>
      apply value_no_step with (t := tm_tabs b) (t' := u); [apply v_tabs; exact Hlc | exact Hs]
  | Hs : step (tm_int ?n) ?u |- _ =>
      exact (value_no_step (tm_int n) (v_int n) u Hs)
  end.

Lemma step_det : forall t u, step t u -> forall v, step t v -> u = v.
Proof.
  intros t. induction t as
    [i | x | T t IHt | t1 IHt1 t2 IHt2 | t IHt | t1 IHt1 T | n | t1 IHt1 t2 IHt2 | op t1 IHt1 t2 IHt2];
    intros u H1 v H2.
  - inversion H1.
  - inversion H1.
  - inversion H1.
  - inversion H1; inversion H2; subst;
      repeat match goal with
      | H : ?X = ?Y |- _ =>
          first [ progress (subst H)
                | progress (injection H; intros; subst; try clear H) ]
      end;
      try solve [reflexivity]; try solve [congruence];
      try solve [solve_contr]; try solve [f_equal; eauto].
  - inversion H1.
  - inversion H1; inversion H2; subst;
      repeat match goal with
      | H : ?X = ?Y |- _ =>
          first [ progress (subst H)
                | progress (injection H; intros; subst; try clear H) ]
      end;
      try solve [reflexivity]; try solve [congruence];
      try solve [solve_contr]; try solve [f_equal; eauto].
  - inversion H1.
  - inversion H1; inversion H2; subst;
      repeat match goal with
      | H : ?X = ?Y |- _ =>
          first [ progress (subst H)
                | progress (injection H; intros; subst; try clear H) ]
      end;
      try solve [reflexivity]; try solve [congruence];
      try solve [solve_contr]; try solve [f_equal; eauto].
  - inversion H1; inversion H2; subst;
      repeat match goal with
      | H : ?X = ?Y |- _ =>
          first [ progress (subst H)
                | progress (injection H; intros; subst; try clear H) ]
      end;
      try solve [reflexivity]; try solve [congruence];
      try solve [solve_contr]; try solve [f_equal; eauto].
Qed.

Lemma multi_trans : forall t u, multi t u -> forall v, multi u v -> multi t v.
Proof.
  intros t u H. induction H as [t | t t2 t3 Hstep Hmulti IH].
  - intros v H2. exact H2.
  - intros v H2. eapply multi_step; [exact Hstep | apply IH; exact H2].
Qed.

Lemma step_multi_value : forall t t2, step t t2 -> forall v, multi t v -> value v -> multi t2 v.
Proof.
  intros t t2 Hstep v Hm. induction Hm as [t0 | t0 t0' t0'' Hs Hm' IH].
  - intros Hval. exfalso.
    match goal with Hv : value ?x |- _ => exact (value_no_step x Hv t2 Hstep) end.
  - intros Hval. assert (t0' = t2) by (eapply step_det; eauto). subst.
    exact Hm'.
Qed.

Lemma multi_det_value : forall t u, multi t u -> forall v, multi t v -> value v -> multi u v.
Proof.
  intros t u H. induction H as [t | t t2 t3 Hstep Hmulti IH].
  - intros v H2 _. exact H2.
  - intros v H2 Hval.
    assert (multi t2 v) as Hmv by (eapply step_multi_value; eauto).
    eapply IH; eauto.
Qed.

Lemma multi_from_value : forall u, value u -> forall v, multi u v -> u = v.
Proof.
  intros u Hv v Hm. induction Hm.
  - reflexivity.
  - exfalso. match goal with Hv0 : value ?x, Hs : step ?x ?w |- _ => exact (value_no_step x Hv0 w Hs) end.
Qed.

Lemma step_lc_back : forall t t', step t t' -> locally_closed_tm t' -> locally_closed_tm t.
Proof.
  intros t t' H. induction H as
    [T t0 v Hlc0 Hval
    | t1 t1' t2 Hst IHst Hlc2
    | v1 t2 t2' Hval Hst IHst
    | t0 T Hlc0 Hlcty
    | t1 t1' T Hst IHst Hlcty
    | t1 t1' t2 Hst IHst Hlc2
    | v1 t2 t2' Hval Hst IHst
    | n m Hnz
    | op t1 t1' t2 Hst IHst Hlc2
    | op v1 t2 t2' Hval Hst IHst
    | op n m];
    intros Hlc; simpl in *.
  - apply lc_tm_app; [assumption | apply value_lc; assumption].
  - inversion Hlc; subst. apply lc_tm_app; [apply IHst; assumption | assumption].
  - inversion Hlc; subst. apply lc_tm_app; [assumption | apply IHst; assumption].
  - apply lc_tm_tapp; assumption.
  - inversion Hlc; subst. apply lc_tm_tapp; [apply IHst; assumption | assumption].
  - inversion Hlc; subst. apply lc_tm_div; [apply IHst; assumption | assumption].
  - inversion Hlc; subst. apply lc_tm_div; [assumption | apply IHst; assumption].
  - apply lc_tm_div; apply lc_tm_int.
  - inversion Hlc; subst. apply lc_tm_arith; [apply IHst; assumption | assumption].
  - inversion Hlc; subst. apply lc_tm_arith; [assumption | apply IHst; assumption].
  - apply lc_tm_arith; apply lc_tm_int.
Qed.

Lemma multi_lc_back : forall t u, multi t u -> locally_closed_tm u -> locally_closed_tm t.
Proof.
  intros t u H. induction H as [t | t t2 t3 Hstep Hmulti IH]; intros Hlc.
  - exact Hlc.
  - eapply step_lc_back.
    + exact Hstep.
    + eapply IH; eauto.
Qed.

Lemma multi_app1 : forall t1 v1, multi t1 v1 -> forall t2,
  locally_closed_tm t2 -> multi (tm_app t1 t2) (tm_app v1 t2).
Proof.
  intros t1 v1 H. induction H as [t | t t2' t3 Hstep Hmulti IH]; intros t2 Hlc.
  - apply multi_refl.
  - eapply multi_step.
    + apply ST_App1; [exact Hstep | exact Hlc].
    + apply IH. exact Hlc.
Qed.

Lemma multi_app2 : forall v1 t2 v2, value v1 -> multi t2 v2 ->
  multi (tm_app v1 t2) (tm_app v1 v2).
Proof.
  intros v1 t2 v2 Hv H. induction H as [t | t t2' t3 Hstep Hmulti IH].
  - apply multi_refl.
  - eapply multi_step.
    + apply ST_App2; [exact Hv | exact Hstep].
    + apply IH.
Qed.

Lemma multi_tapp : forall t v, multi t v -> forall T, locally_closed_ty T ->
  multi (tm_tapp t T) (tm_tapp v T).
Proof.
  intros t v H. induction H as [t | t t2 t3 Hstep Hmulti IH]; intros T Hlc.
  - apply multi_refl.
  - eapply multi_step.
    + apply ST_TApp; [exact Hstep | exact Hlc].
    + apply IH. exact Hlc.
Qed.

Lemma multi_div1 : forall t1 v1, multi t1 v1 -> forall t2,
  locally_closed_tm t2 -> multi (tm_div t1 t2) (tm_div v1 t2).
Proof.
  intros t1 v1 H. induction H as [t | t t2' t3 Hstep Hmulti IH]; intros t2 Hlc.
  - apply multi_refl.
  - eapply multi_step.
    + apply ST_Div1; [exact Hstep | exact Hlc].
    + apply IH. exact Hlc.
Qed.

Lemma multi_div2 : forall v1 t2 v2, value v1 -> multi t2 v2 ->
  multi (tm_div v1 t2) (tm_div v1 v2).
Proof.
  intros v1 t2 v2 Hv H. induction H as [t | t t2' t3 Hstep Hmulti IH].
  - apply multi_refl.
  - eapply multi_step.
    + apply ST_Div2; [exact Hv | exact Hstep].
    + apply IH.
Qed.

Lemma multi_arith1 : forall op t1 v1, multi t1 v1 -> forall t2,
  locally_closed_tm t2 -> multi (tm_arith op t1 t2) (tm_arith op v1 t2).
Proof.
  intros op t1 v1 H. induction H as [t | t t2' t3 Hstep Hmulti IH]; intros t2 Hlc.
  - apply multi_refl.
  - eapply multi_step.
    + apply ST_Arith1; [exact Hstep | exact Hlc].
    + apply IH. exact Hlc.
Qed.

Lemma multi_arith2 : forall op v1 t2 v2, value v1 -> multi t2 v2 ->
  multi (tm_arith op v1 t2) (tm_arith op v1 v2).
Proof.
  intros op v1 t2 v2 Hv H. induction H as [t | t t2' t3 Hstep Hmulti IH].
  - apply multi_refl.
  - eapply multi_step.
    + apply ST_Arith2; [exact Hv | exact Hstep].
    + apply IH.
Qed.

(** ** Free type atoms under opening *)

Lemma atom_incl_trans : forall (l m n : list atom), incl l m -> incl m n -> incl l n.
Proof.
  intros l m n H1 H2 a Ha. apply H2. apply H1. exact Ha.
Qed.

Lemma atom_incl_app_app : forall (l1 l2 m1 m2 : list atom),
  incl l1 m1 -> incl l2 m2 -> incl (l1 ++ l2) (m1 ++ m2).
Proof.
  intros l1 l2 m1 m2 H1 H2 a Ha.
  apply in_app_iff in Ha. apply in_app_iff.
  destruct Ha as [Ha | Ha]; [left; apply H1 | right; apply H2]; exact Ha.
Qed.

Ltac solve_incl_atom :=
  intros a Ha; unfold incl in *; repeat rewrite in_app_iff in *; firstorder.

Lemma fv_ty_open_ty_rec_incl : forall k U T, incl (fv_ty T) (fv_ty (open_ty_rec k U T)).
Proof.
  intros k U T. revert k. induction T as [n | X | T1 IH1 T2 IH2 | T1 IH1 |]; intros k; simpl.
  - destruct (Nat.eqb k n); simpl; apply incl_nil_l.
  - apply incl_refl.
  - solve_incl_atom.
  - solve_incl_atom.
  - apply incl_nil_l.
Qed.

Lemma fv_ty_open_ty_rec_subset : forall k U T, incl (fv_ty (open_ty_rec k U T)) (fv_ty T ++ fv_ty U).
Proof.
  intros k U T. revert k. induction T as [n | X | T1 IH1 T2 IH2 | T1 IH1 |]; intros k; simpl.
  - destruct (Nat.eqb k n); simpl.
    + apply incl_refl.
    + apply incl_nil_l.
  - apply incl_cons. left. reflexivity. apply incl_nil_l.
  - intros a Ha. apply in_app_iff in Ha. destruct Ha as [Ha | Ha].
    + pose proof (IH1 k a Ha) as H1. apply in_app_iff in H1. destruct H1 as [H1 | H1].
      * apply in_app_iff. left. apply in_app_iff. left. exact H1.
      * apply in_app_iff. right. exact H1.
    + pose proof (IH2 k a Ha) as H2. apply in_app_iff in H2. destruct H2 as [H2 | H2].
      * apply in_app_iff. left. apply in_app_iff. right. exact H2.
      * apply in_app_iff. right. exact H2.
  - intros a Ha. simpl in Ha. exact (IH1 (S k) a Ha).
  - apply incl_nil_l.
Qed.

Lemma ftv_tm_open_tm_fvar : forall k x t, ftv_tm (open_tm_rec k (tm_fvar x) t) = ftv_tm t.
Proof.
  intros k x t. revert k. induction t as
    [i | y | T t IHt | t1 IHt1 t2 IHt2 | t IHt | t IHt T | n | t1 IHt1 t2 IHt2 | op t1 IHt1 t2 IHt2];
    intros k; simpl.
  - destruct (Nat.eqb k i); reflexivity.
  - reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt. reflexivity.
  - reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma ftv_tm_open_tm_incl : forall k u t, incl (ftv_tm t) (ftv_tm (open_tm_rec k u t)).
Proof.
  intros k u t. revert k. induction t as
    [i | y | T t IHt | t1 IHt1 t2 IHt2 | t IHt | t IHt T | n | t1 IHt1 t2 IHt2 | op t1 IHt1 t2 IHt2];
    intros k; simpl.
  - destruct (Nat.eqb k i).
    + apply incl_nil_l.
    + apply incl_refl.
  - apply incl_refl.
  - solve_incl_atom.
  - solve_incl_atom.
  - solve_incl_atom.
  - solve_incl_atom.
  - apply incl_nil_l.
  - solve_incl_atom.
  - solve_incl_atom.
Qed.

Lemma ftv_tm_open_tm_ty_incl : forall k U t, incl (ftv_tm t) (ftv_tm (open_tm_ty_rec k U t)).
Proof.
  intros k U t. revert k. induction t as
    [i | y | T t IHt | t1 IHt1 t2 IHt2 | t IHt | t IHt T | n | t1 IHt1 t2 IHt2 | op t1 IHt1 t2 IHt2];
    intros k; simpl.
  - apply incl_refl.
  - apply incl_refl.
  - pose proof (fv_ty_open_ty_rec_incl k U T). solve_incl_atom.
  - solve_incl_atom.
  - solve_incl_atom.
  - pose proof (fv_ty_open_ty_rec_incl k U T). solve_incl_atom.
  - apply incl_nil_l.
  - solve_incl_atom.
  - solve_incl_atom.
Qed.

Lemma ftv_tm_open_tm_ty_subset : forall k U t,
  incl (ftv_tm (open_tm_ty_rec k U t)) (ftv_tm t ++ fv_ty U).
Proof.
  intros k U t. revert k. induction t as
    [i | y | T t IHt | t1 IHt1 t2 IHt2 | t IHt | t IHt T | n | t1 IHt1 t2 IHt2 | op t1 IHt1 t2 IHt2];
    intros k; simpl.
  - apply incl_nil_l.
  - apply incl_nil_l.
  - pose proof (fv_ty_open_ty_rec_subset k U T) as Htype.
    intros a Ha. apply in_app_iff in Ha. destruct Ha as [Ha | Ha].
    + pose proof (Htype a Ha) as H. apply in_app_iff in H. destruct H as [H | H].
      * apply in_app_iff. left. apply in_app_iff. left. exact H.
      * apply in_app_iff. right. exact H.
    + pose proof (IHt k a Ha) as H. apply in_app_iff in H. destruct H as [H | H].
      * apply in_app_iff. left. apply in_app_iff. right. exact H.
      * apply in_app_iff. right. exact H.
  - intros a Ha. apply in_app_iff in Ha. destruct Ha as [Ha | Ha].
    + pose proof (IHt1 k a Ha) as H1. apply in_app_iff in H1. destruct H1 as [H1 | H1].
      * apply in_app_iff. left. apply in_app_iff. left. exact H1.
      * apply in_app_iff. right. exact H1.
    + pose proof (IHt2 k a Ha) as H2. apply in_app_iff in H2. destruct H2 as [H2 | H2].
      * apply in_app_iff. left. apply in_app_iff. right. exact H2.
      * apply in_app_iff. right. exact H2.
  - intros a Ha. exact (IHt (S k) a Ha).
  - pose proof (fv_ty_open_ty_rec_subset k U T) as Htype.
    intros a Ha. apply in_app_iff in Ha. destruct Ha as [Ha | Ha].
    + pose proof (IHt k a Ha) as H. apply in_app_iff in H. destruct H as [H | H].
      * apply in_app_iff. left. apply in_app_iff. left. exact H.
      * apply in_app_iff. right. exact H.
    + pose proof (Htype a Ha) as H. apply in_app_iff in H. destruct H as [H | H].
      * apply in_app_iff. left. apply in_app_iff. right. exact H.
      * apply in_app_iff. right. exact H.
  - apply incl_nil_l.
  - intros a Ha. apply in_app_iff in Ha. destruct Ha as [Ha | Ha].
    + pose proof (IHt1 k a Ha) as H1. apply in_app_iff in H1. destruct H1 as [H1 | H1].
      * apply in_app_iff. left. apply in_app_iff. left. exact H1.
      * apply in_app_iff. right. exact H1.
    + pose proof (IHt2 k a Ha) as H2. apply in_app_iff in H2. destruct H2 as [H2 | H2].
      * apply in_app_iff. left. apply in_app_iff. right. exact H2.
      * apply in_app_iff. right. exact H2.
  - intros a Ha. apply in_app_iff in Ha. destruct Ha as [Ha | Ha].
    + pose proof (IHt1 k a Ha) as H1. apply in_app_iff in H1. destruct H1 as [H1 | H1].
      * apply in_app_iff. left. apply in_app_iff. left. exact H1.
      * apply in_app_iff. right. exact H1.
    + pose proof (IHt2 k a Ha) as H2. apply in_app_iff in H2. destruct H2 as [H2 | H2].
      * apply in_app_iff. left. apply in_app_iff. right. exact H2.
      * apply in_app_iff. right. exact H2.
Qed.

Lemma q_ftv_open_pred_tm_subset : forall k u q,
  incl (q_ftv q) (q_ftv (open_pred_tm_rec k u q) ++ ftv_tm u).
Proof.
  intros k u q. revert k u.
  induction q as [| | t1 t2 | t1 t2 | t1 t2 | q1 IHq1 q2 IHq2 | q1 IHq1 q2 IHq2 | q IHq];
    intros k u; simpl.
  - apply incl_nil_l. - apply incl_nil_l.
  - pose proof (ftv_tm_open_tm_incl k u t1) as H1.
    pose proof (ftv_tm_open_tm_incl k u t2) as H2.
    intros a Ha. apply in_app_iff in Ha. destruct Ha as [Ha | Ha].
    + pose proof (H1 a Ha) as H. apply in_app_iff. left. apply in_app_iff. left. exact H.
    + pose proof (H2 a Ha) as H. apply in_app_iff. left. apply in_app_iff. right. exact H.
  - pose proof (ftv_tm_open_tm_incl k u t1) as H1.
    pose proof (ftv_tm_open_tm_incl k u t2) as H2.
    intros a Ha. apply in_app_iff in Ha. destruct Ha as [Ha | Ha].
    + pose proof (H1 a Ha) as H. apply in_app_iff. left. apply in_app_iff. left. exact H.
    + pose proof (H2 a Ha) as H. apply in_app_iff. left. apply in_app_iff. right. exact H.
  - pose proof (ftv_tm_open_tm_incl k u t1) as H1.
    pose proof (ftv_tm_open_tm_incl k u t2) as H2.
    intros a Ha. apply in_app_iff in Ha. destruct Ha as [Ha | Ha].
    + pose proof (H1 a Ha) as H. apply in_app_iff. left. apply in_app_iff. left. exact H.
    + pose proof (H2 a Ha) as H. apply in_app_iff. left. apply in_app_iff. right. exact H.
  - intros a Ha. apply in_app_iff in Ha. destruct Ha as [Ha | Ha].
    + pose proof (IHq1 k u a Ha) as H. apply in_app_iff in H. destruct H as [H | H].
      * apply in_app_iff. left. apply in_app_iff. left. exact H.
      * apply in_app_iff. right. exact H.
    + pose proof (IHq2 k u a Ha) as H. apply in_app_iff in H. destruct H as [H | H].
      * apply in_app_iff. left. apply in_app_iff. right. exact H.
      * apply in_app_iff. right. exact H.
  - intros a Ha. apply in_app_iff in Ha. destruct Ha as [Ha | Ha].
    + pose proof (IHq1 k u a Ha) as H. apply in_app_iff in H. destruct H as [H | H].
      * apply in_app_iff. left. apply in_app_iff. left. exact H.
      * apply in_app_iff. right. exact H.
    + pose proof (IHq2 k u a Ha) as H. apply in_app_iff in H. destruct H as [H | H].
      * apply in_app_iff. left. apply in_app_iff. right. exact H.
      * apply in_app_iff. right. exact H.
  - intros a Ha. exact (IHq k u a Ha).
Qed.

Lemma q_ftv_open_pred_tm_eq : forall k x q,
  q_ftv (open_pred_tm_rec k (tm_fvar x) q) = q_ftv q.
Proof.
  intros k x q. revert k.
  induction q as [| | t1 t2 | t1 t2 | t1 t2 | q1 IHq1 q2 IHq2 | q1 IHq1 q2 IHq2 | q IHq];
    intros k; simpl.
  - reflexivity. - reflexivity.
  - rewrite !ftv_tm_open_tm_fvar. reflexivity.
  - rewrite !ftv_tm_open_tm_fvar. reflexivity.
  - rewrite !ftv_tm_open_tm_fvar. reflexivity.
  - rewrite IHq1, IHq2. reflexivity.
  - rewrite IHq1, IHq2. reflexivity.
  - rewrite IHq. reflexivity.
Qed.

Lemma q_ftv_open_pred_ty_subset : forall k U q,
  incl (q_ftv (open_pred_ty_rec k U q)) (q_ftv q ++ fv_ty U).
Proof.
  intros k U q. revert k U.
  induction q as [| | t1 t2 | t1 t2 | t1 t2 | q1 IHq1 q2 IHq2 | q1 IHq1 q2 IHq2 | q IHq];
    intros k U; simpl.
  - apply incl_nil_l. - apply incl_nil_l.
  - pose proof (ftv_tm_open_tm_ty_subset k U t1) as H1.
    pose proof (ftv_tm_open_tm_ty_subset k U t2) as H2.
    intros a Ha. apply in_app_iff in Ha. destruct Ha as [Ha | Ha].
    + pose proof (H1 a Ha) as H. apply in_app_iff in H. destruct H as [H | H].
      * apply in_app_iff. left. apply in_app_iff. left. exact H.
      * apply in_app_iff. right. exact H.
    + pose proof (H2 a Ha) as H. apply in_app_iff in H. destruct H as [H | H].
      * apply in_app_iff. left. apply in_app_iff. right. exact H.
      * apply in_app_iff. right. exact H.
  - pose proof (ftv_tm_open_tm_ty_subset k U t1) as H1.
    pose proof (ftv_tm_open_tm_ty_subset k U t2) as H2.
    intros a Ha. apply in_app_iff in Ha. destruct Ha as [Ha | Ha].
    + pose proof (H1 a Ha) as H. apply in_app_iff in H. destruct H as [H | H].
      * apply in_app_iff. left. apply in_app_iff. left. exact H.
      * apply in_app_iff. right. exact H.
    + pose proof (H2 a Ha) as H. apply in_app_iff in H. destruct H as [H | H].
      * apply in_app_iff. left. apply in_app_iff. right. exact H.
      * apply in_app_iff. right. exact H.
  - pose proof (ftv_tm_open_tm_ty_subset k U t1) as H1.
    pose proof (ftv_tm_open_tm_ty_subset k U t2) as H2.
    intros a Ha. apply in_app_iff in Ha. destruct Ha as [Ha | Ha].
    + pose proof (H1 a Ha) as H. apply in_app_iff in H. destruct H as [H | H].
      * apply in_app_iff. left. apply in_app_iff. left. exact H.
      * apply in_app_iff. right. exact H.
    + pose proof (H2 a Ha) as H. apply in_app_iff in H. destruct H as [H | H].
      * apply in_app_iff. left. apply in_app_iff. right. exact H.
      * apply in_app_iff. right. exact H.
  - intros a Ha. apply in_app_iff in Ha. destruct Ha as [Ha | Ha].
    + pose proof (IHq1 k U a Ha) as H. apply in_app_iff in H. destruct H as [H | H].
      * apply in_app_iff. left. apply in_app_iff. left. exact H.
      * apply in_app_iff. right. exact H.
    + pose proof (IHq2 k U a Ha) as H. apply in_app_iff in H. destruct H as [H | H].
      * apply in_app_iff. left. apply in_app_iff. right. exact H.
      * apply in_app_iff. right. exact H.
  - intros a Ha. apply in_app_iff in Ha. destruct Ha as [Ha | Ha].
    + pose proof (IHq1 k U a Ha) as H. apply in_app_iff in H. destruct H as [H | H].
      * apply in_app_iff. left. apply in_app_iff. left. exact H.
      * apply in_app_iff. right. exact H.
    + pose proof (IHq2 k U a Ha) as H. apply in_app_iff in H. destruct H as [H | H].
      * apply in_app_iff. left. apply in_app_iff. right. exact H.
      * apply in_app_iff. right. exact H.
  - intros a Ha. exact (IHq k U a Ha).
Qed.

Lemma q_ftv_open_pred_ty_incl : forall k U q,
  incl (q_ftv q) (q_ftv (open_pred_ty_rec k U q)).
Proof.
  intros k U q. revert k U.
  induction q as [| | t1 t2 | t1 t2 | t1 t2 | q1 IHq1 q2 IHq2 | q1 IHq1 q2 IHq2 | q IHq];
    intros k U; simpl.
  - apply incl_nil_l. - apply incl_nil_l.
  - pose proof (ftv_tm_open_tm_ty_incl k U t1) as H1.
    pose proof (ftv_tm_open_tm_ty_incl k U t2) as H2.
    intros a Ha. apply in_app_iff in Ha. destruct Ha as [Ha | Ha].
    + pose proof (H1 a Ha) as H. apply in_app_iff. left. exact H.
    + pose proof (H2 a Ha) as H. apply in_app_iff. right. exact H.
  - pose proof (ftv_tm_open_tm_ty_incl k U t1) as H1.
    pose proof (ftv_tm_open_tm_ty_incl k U t2) as H2.
    intros a Ha. apply in_app_iff in Ha. destruct Ha as [Ha | Ha].
    + pose proof (H1 a Ha) as H. apply in_app_iff. left. exact H.
    + pose proof (H2 a Ha) as H. apply in_app_iff. right. exact H.
  - pose proof (ftv_tm_open_tm_ty_incl k U t1) as H1.
    pose proof (ftv_tm_open_tm_ty_incl k U t2) as H2.
    intros a Ha. apply in_app_iff in Ha. destruct Ha as [Ha | Ha].
    + pose proof (H1 a Ha) as H. apply in_app_iff. left. exact H.
    + pose proof (H2 a Ha) as H. apply in_app_iff. right. exact H.
  - intros a Ha. apply in_app_iff in Ha. destruct Ha as [Ha | Ha].
    + pose proof (IHq1 k U a Ha) as H. apply in_app_iff. left. exact H.
    + pose proof (IHq2 k U a Ha) as H. apply in_app_iff. right. exact H.
  - intros a Ha. apply in_app_iff in Ha. destruct Ha as [Ha | Ha].
    + pose proof (IHq1 k U a Ha) as H. apply in_app_iff. left. exact H.
    + pose proof (IHq2 k U a Ha) as H. apply in_app_iff. right. exact H.
  - intros a Ha. exact (IHq k U a Ha).
Qed.

Lemma rty_ftv_open_rty_tm_fvar : forall k x R,
  rty_ftv (open_rty_tm_rec k (tm_fvar x) R) = rty_ftv R.
Proof.
  intros k x R. revert k.
  induction R as [T q | R1 IHR1 R2 IHR2 | R1 IHR1 R2 IHR2 | R1 IHR1]; intros k; simpl.
  - rewrite q_ftv_open_pred_tm_eq. reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR1. reflexivity.
Qed.

Lemma rty_ftv_open_rty_ty_subset : forall k U R,
  incl (rty_ftv (open_rty_ty_rec k U R)) (rty_ftv R ++ fv_ty U).
Proof.
  intros k U R. revert k U.
  induction R as [T q | R1 IHR1 R2 IHR2 | R1 IHR1 R2 IHR2 | R1 IHR1]; intros k U; simpl.
  - pose proof (fv_ty_open_ty_rec_subset k U T) as H1.
    pose proof (q_ftv_open_pred_ty_subset k U q) as H2.
    intros a Ha. apply in_app_iff in Ha. destruct Ha as [Ha | Ha].
    + pose proof (H1 a Ha) as H. apply in_app_iff in H. destruct H as [H | H].
      * apply in_app_iff. left. apply in_app_iff. left. exact H.
      * apply in_app_iff. right. exact H.
    + pose proof (H2 a Ha) as H. apply in_app_iff in H. destruct H as [H | H].
      * apply in_app_iff. left. apply in_app_iff. right. exact H.
      * apply in_app_iff. right. exact H.
  - intros a Ha. apply in_app_iff in Ha. destruct Ha as [Ha | Ha].
    + pose proof (IHR1 k U a Ha) as H. apply in_app_iff in H. destruct H as [H | H].
      * apply in_app_iff. left. apply in_app_iff. left. exact H.
      * apply in_app_iff. right. exact H.
    + pose proof (IHR2 k U a Ha) as H. apply in_app_iff in H. destruct H as [H | H].
      * apply in_app_iff. left. apply in_app_iff. right. exact H.
      * apply in_app_iff. right. exact H.
  - intros a Ha. apply in_app_iff in Ha. destruct Ha as [Ha | Ha].
    + pose proof (IHR1 k U a Ha) as H. apply in_app_iff in H. destruct H as [H | H].
      * apply in_app_iff. left. apply in_app_iff. left. exact H.
      * apply in_app_iff. right. exact H.
    + pose proof (IHR2 k U a Ha) as H. apply in_app_iff in H. destruct H as [H | H].
      * apply in_app_iff. left. apply in_app_iff. right. exact H.
      * apply in_app_iff. right. exact H.
  - intros a Ha. exact (IHR1 (S k) U a Ha).
Qed.

Lemma rty_ftv_open_rty_ty_incl : forall k U R,
  incl (rty_ftv R) (rty_ftv (open_rty_ty_rec k U R)).
Proof.
  intros k U R. revert k U.
  induction R as [T q | R1 IHR1 R2 IHR2 | R1 IHR1 R2 IHR2 | R1 IHR1]; intros k U; simpl.
  - pose proof (fv_ty_open_ty_rec_incl k U T) as H1.
    pose proof (q_ftv_open_pred_ty_incl k U q) as H2.
    intros a Ha. apply in_app_iff in Ha. destruct Ha as [Ha | Ha].
    + pose proof (H1 a Ha) as H. apply in_app_iff. left. exact H.
    + pose proof (H2 a Ha) as H. apply in_app_iff. right. exact H.
  - intros a Ha. apply in_app_iff in Ha. destruct Ha as [Ha | Ha].
    + pose proof (IHR1 k U a Ha) as H. apply in_app_iff. left. exact H.
    + pose proof (IHR2 k U a Ha) as H. apply in_app_iff. right. exact H.
  - intros a Ha. apply in_app_iff in Ha. destruct Ha as [Ha | Ha].
    + pose proof (IHR1 k U a Ha) as H. apply in_app_iff. left. exact H.
    + pose proof (IHR2 k U a Ha) as H. apply in_app_iff. right. exact H.
  - intros a Ha. exact (IHR1 (S k) U a Ha).
Qed.

End SystemFRefinementStep.

Module SystemFRefinementInv.
Import ListNotations SystemFRefinement SystemFRefinementLogic SystemFRefinementTyping SystemFRefinementEvaluation SystemFRefinementLib SystemFRefinementLib2 SystemFRefinementStep.

Lemma fresh_avoid_l : forall (L : list atom) (a : atom), ~ In (fresh (L ++ a :: nil)) L.
Proof.
  intros L a H. apply (fresh_notin (L ++ a :: nil)).
  apply in_app_iff. left. exact H.
Qed.

Lemma fresh_avoid_neq : forall (L : list atom) (a : atom), fresh (L ++ a :: nil) <> a.
Proof.
  intros L a Heq. apply (fresh_notin (L ++ a :: nil)).
  apply in_app_iff. right. simpl. left. symmetry. exact Heq.
Qed.

Lemma fresh_avoid_list_l : forall (L M : list atom), ~ In (fresh (L ++ M)) L.
Proof.
  intros L M H. apply (fresh_notin (L ++ M)). apply in_app_iff. left. exact H.
Qed.

Lemma fresh_avoid_list_r : forall (L M : list atom), ~ In (fresh (L ++ M)) M.
Proof.
  intros L M H. apply (fresh_notin (L ++ M)). apply in_app_iff. right. exact H.
Qed.

Lemma wf_ty_fv_subset : forall Delta T, wf_ty Delta T -> incl (fv_ty T) Delta.
Proof.
  intros Delta T H. induction H as
    [Delta0 X Hin | Delta0 T1 T2 H1 IH1 H2 IH2 | L0 Delta0 T0 Hprem IHprem | Delta0].
  - intros a Ha. simpl in Ha. destruct Ha as [-> | []]. exact Hin.
  - intros a Ha. simpl in Ha. apply in_app_iff in Ha.
    destruct Ha as [Ha | Ha]; [apply IH1 | apply IH2]; exact Ha.
  - intros a Ha. simpl in Ha.
    set (Y := fresh (L0 ++ a :: nil)).
    assert (HY : ~ In Y L0) by (unfold Y; apply fresh_avoid_l).
    assert (Hneq : Y <> a) by (unfold Y; apply fresh_avoid_neq).
    assert (Hfa : In a (fv_ty (open_ty T0 (Ty_FVar Y)))).
    { unfold open_ty. apply (fv_ty_open_ty_rec_incl 0 (Ty_FVar Y) T0). exact Ha. }
    pose proof (IHprem Y HY a Hfa) as Hin.
    simpl in Hin. destruct Hin as [Heq | Hin].
    + exfalso. apply Hneq. exact Heq.
    + exact Hin.
  - intros a Ha. simpl in Ha. destruct Ha.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T H. induction H as
    [Delta0 X Hin | Delta0 T1 T2 H1 IH1 H2 IH2 | L0 Delta0 T0 Hprem IHprem | Delta0].
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; assumption.
  - apply lc_ty_all.
    pose proof (IHprem (fresh L0) (fresh_notin L0)) as Hlc.
    eapply lc_ty_open_ty_inv; [exact Hlc | apply lc_ty_fvar].
  - apply lc_ty_int.
Qed.

Lemma wf_rty_wf_erase : forall Delta RGamma R, wf_rty Delta RGamma R -> wf_ty Delta (erase R).
Proof.
  intros Delta RGamma R H. induction H as
    [L0 Delta0 RGamma0 T0 ps0 Hty Hq
    | L0 Delta0 RGamma0 R1 R2 H1 IH1 H2 IH2
    | L0 Delta0 RGamma0 R1 R2 H1 IH1 H2 IH2
    | L0 Delta0 RGamma0 R0 H1 IH1].
  - simpl. exact Hty.
  - simpl. apply WF_Arrow.
    + exact IH1.
    + pose proof (IH2 (fresh L0) (fresh_notin L0)) as H2'.
      assert (E : erase (open_rty_tm R2 (tm_fvar (fresh L0))) = erase R2)
        by apply erase_open_rty_tm_rec.
      rewrite E in H2'. exact H2'.
  - simpl. pose proof (IH2 (fresh L0) (fresh_notin L0)) as H2'.
    assert (E : erase (open_rty_tm R2 (tm_fvar (fresh L0))) = erase R2)
      by apply erase_open_rty_tm_rec.
    rewrite E in H2'. exact H2'.
  - simpl. apply WF_All with (L := L0).
    intros X HX. pose proof (IH1 X HX) as H1'.
    assert (E : erase (open_rty_ty R0 (Ty_FVar X)) = open_ty (erase R0) (Ty_FVar X))
      by apply erase_open_rty_ty_rec.
    rewrite E in H1'. exact H1'.
Qed.

Lemma wf_rty_lc_erase : forall Delta RGamma R, wf_rty Delta RGamma R -> locally_closed_ty (erase R).
Proof.
  intros Delta RGamma R H.
  exact (wf_ty_lc Delta (erase R) (wf_rty_wf_erase Delta RGamma R H)).
Qed.

Lemma in_cons_ne : forall (X a : atom) (l : list atom), X <> a -> In a (X :: l) -> In a l.
Proof.
  intros X a l Hne Hin. simpl in Hin. destruct Hin as [Heq | Hin].
  - exfalso. exact (Hne Heq).
  - exact Hin.
Qed.

Lemma has_type_inv : forall Delta Gamma t T, has_type Delta Gamma t T ->
  incl (fv_ty T) Delta /\ incl (ftv_tm t) Delta.
Proof.
  intros Delta Gamma t T H. induction H as
    [Delta0 Gamma0 x T0 Hlook Hwf
    | L0 Delta0 Gamma0 T1 t2 T2 Hwf Hprem IHprem
    | Delta0 Gamma0 t1 t2 T1 T2 H1 IH1 H2 IH2
    | L0 Delta0 Gamma0 t0 T0 Hprem IHprem
    | Delta0 Gamma0 t0 T0 U H1 IH1 Hwf
    | Delta0 Gamma0 n
    | Delta0 Gamma0 t1 t2 H1 IH1 H2 IH2
    | Delta0 Gamma0 op t1 t2 H1 IH1 H2 IH2].
  - split.
    + apply wf_ty_fv_subset with (Delta := Delta0). exact Hwf.
    + apply incl_nil_l.
  - destruct (IHprem (fresh L0) (fresh_notin L0)) as [Hfv2 Hftv].
    split.
    + intros a Ha. simpl in Ha. apply in_app_iff in Ha. destruct Ha as [Ha | Ha].
      * exact (wf_ty_fv_subset Delta0 T1 Hwf a Ha).
      * apply Hfv2. exact Ha.
    + intros a Ha. simpl in Ha. apply in_app_iff in Ha. destruct Ha as [Ha | Ha].
      * exact (wf_ty_fv_subset Delta0 T1 Hwf a Ha).
      * apply Hftv. unfold open_tm. rewrite ftv_tm_open_tm_fvar. exact Ha.
  - destruct IH1 as [Hfv1 Hftv1]. destruct IH2 as [Hfv2 Hftv2].
    split.
    + intros a Ha. apply Hfv1. simpl. apply in_app_iff. right. exact Ha.
    + intros a Ha. simpl in Ha. apply in_app_iff in Ha. destruct Ha as [Ha | Ha].
      * apply Hftv1. exact Ha.
      * apply Hftv2. exact Ha.
  - split.
    + intros a Ha. simpl in Ha.
      set (X := fresh (L0 ++ a :: nil)).
      assert (HX : ~ In X L0) by (unfold X; apply fresh_avoid_l).
      assert (Hne : X <> a) by (unfold X; apply fresh_avoid_neq).
      pose proof (IHprem X HX) as [Hfv Hftv].
      apply in_cons_ne with (X := X); [exact Hne |].
      apply Hfv. unfold open_ty. apply (fv_ty_open_ty_rec_incl 0 (Ty_FVar X) T0). exact Ha.
    + intros a Ha.
      set (X := fresh (L0 ++ a :: nil)).
      assert (HX : ~ In X L0) by (unfold X; apply fresh_avoid_l).
      assert (Hne : X <> a) by (unfold X; apply fresh_avoid_neq).
      pose proof (IHprem X HX) as [Hfv Hftv].
      apply in_cons_ne with (X := X); [exact Hne |].
      apply Hftv. unfold open_tm_ty. exact (ftv_tm_open_tm_ty_incl 0 (Ty_FVar X) t0 a Ha).
  - destruct IH1 as [Hfv1 Hftv1].
    split.
    + intros a Ha. apply fv_ty_open_ty_rec_subset with (k := 0) in Ha.
      apply in_app_iff in Ha. destruct Ha as [Ha | Ha].
      * apply Hfv1. simpl. simpl in Ha. exact Ha.
      * exact (wf_ty_fv_subset Delta0 U Hwf a Ha).
    + intros a Ha. simpl in Ha. apply in_app_iff in Ha. destruct Ha as [Ha | Ha].
      * apply Hftv1. exact Ha.
      * exact (wf_ty_fv_subset Delta0 U Hwf a Ha).
  - split.
    + apply incl_nil_l.
    + apply incl_nil_l.
  - destruct IH1 as [Hfv1 Hftv1]. destruct IH2 as [Hfv2 Hftv2].
    split.
    + apply incl_nil_l.
    + intros a Ha. simpl in Ha. apply in_app_iff in Ha. destruct Ha as [Ha | Ha].
      * apply Hftv1. exact Ha.
      * apply Hftv2. exact Ha.
  - destruct IH1 as [Hfv1 Hftv1]. destruct IH2 as [Hfv2 Hftv2].
    split.
    + apply incl_nil_l.
    + intros a Ha. simpl in Ha. apply in_app_iff in Ha. destruct Ha as [Ha | Ha].
      * apply Hftv1. exact Ha.
      * apply Hftv2. exact Ha.
Qed.

Lemma predicate_closed_q_fv : forall q, predicate_closed q -> q_fv q = [].
Proof.
  intros q H. induction q; simpl in *.
  - reflexivity. - reflexivity.
  - destruct H as [H1 [H2 [H3 [H4 [H5 H6]]]]]. now rewrite H2, H5.
  - destruct H as [H1 [H2 [H3 [H4 [H5 H6]]]]]. now rewrite H2, H5.
  - destruct H as [H1 [H2 [H3 [H4 [H5 H6]]]]]. now rewrite H2, H5.
  - destruct H as [H1 H2]. rewrite IHq1; [|exact H1]. rewrite IHq2; [|exact H2]. reflexivity.
  - destruct H as [H1 H2]. rewrite IHq1; [|exact H1]. rewrite IHq2; [|exact H2]. reflexivity.
  - apply IHq. exact H.
Qed.

Lemma predicate_closed_q_ftv : forall q, predicate_closed q -> q_ftv q = [].
Proof.
  intros q H. induction q; simpl in *.
  - reflexivity. - reflexivity.
  - destruct H as [H1 [H2 [H3 [H4 [H5 H6]]]]]. now rewrite H3, H6.
  - destruct H as [H1 [H2 [H3 [H4 [H5 H6]]]]]. now rewrite H3, H6.
  - destruct H as [H1 [H2 [H3 [H4 [H5 H6]]]]]. now rewrite H3, H6.
  - destruct H as [H1 H2]. rewrite IHq1; [|exact H1]. rewrite IHq2; [|exact H2]. reflexivity.
  - destruct H as [H1 H2]. rewrite IHq1; [|exact H1]. rewrite IHq2; [|exact H2]. reflexivity.
  - apply IHq. exact H.
Qed.

Lemma predicate_wf_ftv_subset : forall Delta Gamma q, predicate_wf Delta Gamma q -> incl (q_ftv q) Delta.
Proof.
  intros Delta Gamma q H. induction H as
    [Delta0 Gamma0 | Delta0 Gamma0
    | Delta0 Gamma0 t1 t2 T0 H1 H2
    | Delta0 Gamma0 t1 t2 H1 H2
    | Delta0 Gamma0 t1 t2 H1 H2
    | Delta0 Gamma0 p1 p2 H1 IH1 H2 IH2
    | Delta0 Gamma0 p1 p2 H1 IH1 H2 IH2
    | Delta0 Gamma0 p H1 IH1].
  - apply incl_nil_l.
  - apply incl_nil_l.
  - intros a Ha. simpl in Ha. apply in_app_iff in Ha. destruct Ha as [Ha | Ha].
    + exact (proj2 (has_type_inv Delta0 Gamma0 t1 T0 H1) a Ha).
    + exact (proj2 (has_type_inv Delta0 Gamma0 t2 T0 H2) a Ha).
  - intros a Ha. simpl in Ha. apply in_app_iff in Ha. destruct Ha as [Ha | Ha].
    + exact (proj2 (has_type_inv Delta0 Gamma0 t1 Ty_Int H1) a Ha).
    + exact (proj2 (has_type_inv Delta0 Gamma0 t2 Ty_Int H2) a Ha).
  - intros a Ha. simpl in Ha. apply in_app_iff in Ha. destruct Ha as [Ha | Ha].
    + exact (proj2 (has_type_inv Delta0 Gamma0 t1 Ty_Int H1) a Ha).
    + exact (proj2 (has_type_inv Delta0 Gamma0 t2 Ty_Int H2) a Ha).
  - intros a Ha. simpl in Ha. apply in_app_iff in Ha. destruct Ha as [Ha | Ha].
    + apply IH1. exact Ha.
    + apply IH2. exact Ha.
  - intros a Ha. simpl in Ha. apply in_app_iff in Ha. destruct Ha as [Ha | Ha].
    + apply IH1. exact Ha.
    + apply IH2. exact Ha.
  - apply IH1.
Qed.

Lemma wf_rty_ftv_subset : forall Delta RGamma R, wf_rty Delta RGamma R -> incl (rty_ftv R) Delta.
Proof.
  intros Delta RGamma R H. induction H as
    [L0 Delta0 RGamma0 T0 ps0 Hty Hq
    | L0 Delta0 RGamma0 R1 R2 H1 IH1 H2 IH2
    | L0 Delta0 RGamma0 R1 R2 H1 IH1 H2 IH2
    | L0 Delta0 RGamma0 R0 H1 IH1].
  - intros a Ha. simpl in Ha. apply in_app_iff in Ha. destruct Ha as [Ha | Ha].
    + exact (wf_ty_fv_subset Delta0 T0 Hty a Ha).
    + pose proof (Hq (fresh L0) (fresh_notin L0)) as Hqwf.
      pose proof (predicate_wf_ftv_subset Delta0 (update (erase_context RGamma0) (fresh L0) T0)
                    (open_qualifier_tm ps0 (tm_fvar (fresh L0))) Hqwf) as Hqsub.
      apply Hqsub. unfold open_qualifier_tm. rewrite q_ftv_open_pred_tm_eq. exact Ha.
  - intros a Ha. simpl in Ha. apply in_app_iff in Ha. destruct Ha as [Ha | Ha].
    + apply IH1. exact Ha.
    + pose proof (IH2 (fresh L0) (fresh_notin L0)) as H2'.
      assert (E : rty_ftv (open_rty_tm R2 (tm_fvar (fresh L0))) = rty_ftv R2)
        by apply rty_ftv_open_rty_tm_fvar.
      rewrite E in H2'. apply H2'. exact Ha.
  - intros a Ha. simpl in Ha. apply in_app_iff in Ha. destruct Ha as [Ha | Ha].
    + apply IH1. exact Ha.
    + pose proof (IH2 (fresh L0) (fresh_notin L0)) as H2'.
      assert (E : rty_ftv (open_rty_tm R2 (tm_fvar (fresh L0))) = rty_ftv R2)
        by apply rty_ftv_open_rty_tm_fvar.
      rewrite E in H2'. apply H2'. exact Ha.
  - intros a Ha. simpl in Ha.
    set (X := fresh (L0 ++ a :: nil)).
    assert (HX : ~ In X L0) by (unfold X; apply fresh_avoid_l).
    assert (Hne : X <> a) by (unfold X; apply fresh_avoid_neq).
    pose proof (IH1 X HX) as Hsub.
    apply in_cons_ne with (X := X); [exact Hne |].
    apply Hsub. unfold open_rty_ty. exact (rty_ftv_open_rty_ty_incl 0 (Ty_FVar X) R0 a Ha).
Qed.

Lemma has_rtype_ftv_subset : forall Delta RGamma t R, has_rtype Delta RGamma t R ->
  incl (ftv_tm t) Delta /\ incl (rty_ftv R) Delta.
Proof.
  intros Delta RGamma t R H. induction H as
    [Delta0 RGamma0 x R0 Hlook Hwf
    | L0 Delta0 RGamma0 R1 body R2 Hwf Hprem IHprem
    | Delta0 RGamma0 t1 t2 R1 R2 H1 IH1 H2 IH2
    | L0 Delta0 RGamma0 body R0 Hprem IHprem
    | Delta0 RGamma0 t0 R0 U H1 IH1 Hwf
    | Delta0 RGamma0 n
    | Delta0 RGamma0 t1 t2 H1 IH1 H2 IH2
    | Delta0 RGamma0 op t1 t2 H1 IH1 H2 IH2
    | Delta0 RGamma0 v T0 ps0 Hty Hval Hwf Hclosed Hholds
    | Delta0 RGamma0 t0 R0 S H1 IH1 Hwf Hsub].
  - split.
    + apply incl_nil_l.
    + exact (wf_rty_ftv_subset Delta0 RGamma0 R0 Hwf).
  - destruct (IHprem (fresh L0) (fresh_notin L0)) as [Hftv2 Hrty2].
    split.
    + intros a Ha. simpl in Ha. apply in_app_iff in Ha. destruct Ha as [Ha | Ha].
      * exact (wf_ty_fv_subset Delta0 (erase R1) (wf_rty_wf_erase Delta0 RGamma0 R1 Hwf) a Ha).
      * apply Hftv2. unfold open_tm. rewrite ftv_tm_open_tm_fvar. exact Ha.
    + intros a Ha. simpl in Ha. apply in_app_iff in Ha. destruct Ha as [Ha | Ha].
      * exact (wf_rty_ftv_subset Delta0 RGamma0 R1 Hwf a Ha).
      * assert (E : rty_ftv (open_rty_tm R2 (tm_fvar (fresh L0))) = rty_ftv R2)
          by apply rty_ftv_open_rty_tm_fvar.
        rewrite E in Hrty2. apply Hrty2. exact Ha.
  - destruct IH1 as [Hftv1 Hrty1]. destruct IH2 as [Hftv2 Hrty2].
    split.
    + intros a Ha. simpl in Ha. apply in_app_iff in Ha. destruct Ha as [Ha | Ha].
      * apply Hftv1. exact Ha.
      * apply Hftv2. exact Ha.
    + intros a Ha. apply Hrty1. exact Ha.
  - split.
    + intros a Ha.
      set (X := fresh (L0 ++ a :: nil)).
      assert (HX : ~ In X L0) by (unfold X; apply fresh_avoid_l).
      assert (Hne : X <> a) by (unfold X; apply fresh_avoid_neq).
      pose proof (IHprem X HX) as [Hftv Hrty].
      apply in_cons_ne with (X := X); [exact Hne |].
      apply Hftv. unfold open_tm_ty. exact (ftv_tm_open_tm_ty_incl 0 (Ty_FVar X) body a Ha).
    + intros a Ha.
      set (X := fresh (L0 ++ a :: nil)).
      assert (HX : ~ In X L0) by (unfold X; apply fresh_avoid_l).
      assert (Hne : X <> a) by (unfold X; apply fresh_avoid_neq).
      pose proof (IHprem X HX) as [Hftv Hrty].
      apply in_cons_ne with (X := X); [exact Hne |].
      apply Hrty. unfold open_rty_ty. exact (rty_ftv_open_rty_ty_incl 0 (Ty_FVar X) R0 a Ha).
  - destruct IH1 as [Hftv1 Hrty1].
    split.
    + intros a Ha. simpl in Ha. apply in_app_iff in Ha. destruct Ha as [Ha | Ha].
      * apply Hftv1. exact Ha.
      * exact (wf_ty_fv_subset Delta0 U Hwf a Ha).
    + intros a Ha.
      pose proof (rty_ftv_open_rty_ty_subset 0 U R0) as Hsub.
      assert (Hin : In a (rty_ftv R0 ++ fv_ty U)).
      { apply Hsub. unfold open_rty_ty in Ha. exact Ha. }
      apply in_app_iff in Hin. destruct Hin as [Hin | Hin].
      * apply Hrty1. simpl in Hin. exact Hin.
      * exact (wf_ty_fv_subset Delta0 U Hwf a Hin).
  - split; apply incl_nil_l.
  - destruct IH1 as [Hftv1 Hrty1]. destruct IH2 as [Hftv2 Hrty2].
    split.
    + intros a Ha. simpl in Ha. apply in_app_iff in Ha. destruct Ha as [Ha | Ha].
      * apply Hftv1. exact Ha.
      * apply Hftv2. exact Ha.
    + apply incl_nil_l.
  - destruct IH1 as [Hftv1 Hrty1]. destruct IH2 as [Hftv2 Hrty2].
    split.
    + intros a Ha. simpl in Ha. apply in_app_iff in Ha. destruct Ha as [Ha | Ha].
      * apply Hftv1. exact Ha.
      * apply Hftv2. exact Ha.
    + intros a Ha. simpl in Ha. simpl in Ha. apply in_app_iff in Ha. destruct Ha as [Ha | Ha].
      * apply Hftv1. exact Ha.
      * apply Hftv2. exact Ha.
  - destruct (has_type_inv Delta0 (erase_context RGamma0) v T0 Hty) as [HfvT Hftvv].
    split.
    + exact Hftvv.
    + intros a Ha. simpl in Ha. apply in_app_iff in Ha. destruct Ha as [Ha | Ha].
      * exact (HfvT a Ha).
      * pose proof (q_ftv_open_pred_tm_subset 0 v ps0) as Hsub.
        assert (Hin : In a (q_ftv (open_qualifier_tm ps0 v) ++ ftv_tm v)).
        { apply Hsub. unfold open_qualifier_tm in Ha. simpl in Ha. exact Ha. }
        apply in_app_iff in Hin. destruct Hin as [Hin | Hin].
        -- rewrite predicate_closed_q_ftv in Hin; [contradiction | exact Hclosed].
        -- exact (Hftvv a Hin).
  - destruct IH1 as [Hftv1 Hrty1].
    split.
    + exact Hftv1.
    + exact (wf_rty_ftv_subset Delta0 RGamma0 S Hwf).
Qed.

Lemma value_has_type_shape : forall Delta Gamma v T,
  has_type Delta Gamma v T -> value v ->
  forall sg s, shape (ty_subst_atoms sg T) (tsubst s (tm_ty_subst_atoms sg v)).
Proof.
  intros Delta Gamma v T H. induction H as
    [Delta0 Gamma0 x T0 Hlook Hwf
    | L0 Delta0 Gamma0 T1 t2 T2 Hwf Hprem IHprem
    | Delta0 Gamma0 t1 t2 T1 T2 H1 IH1 H2 IH2
    | L0 Delta0 Gamma0 t0 T0 Hprem IHprem
    | Delta0 Gamma0 t0 T0 U H1 IH1 Hwf
    | Delta0 Gamma0 n
    | Delta0 Gamma0 t1 t2 H1 IH1 H2 IH2
    | Delta0 Gamma0 op t1 t2 H1 IH1 H2 IH2];
    intros Hv sg s; simpl in *.
  - inversion Hv.
  - exists (ty_subst_atoms sg T1). exists (tsubst s (tm_ty_subst_atoms sg t2)). reflexivity.
  - inversion Hv.
  - exists (tsubst s (tm_ty_subst_atoms sg t0)). reflexivity.
  - inversion Hv.
  - exists n. reflexivity.
  - inversion Hv.
  - inversion Hv.
Qed.

End SystemFRefinementInv.

Module SystemFRefinementSem.
Import ListNotations SystemFRefinement SystemFRefinementLogic SystemFRefinementTyping SystemFRefinementEvaluation SystemFRefinementLib SystemFRefinementLib2 SystemFRefinementStep SystemFRefinementInv.
From Stdlib Require Import Wf_nat.

Fixpoint semVf (n : nat) (R : rty) (v : tm) {struct n} : Prop :=
  match n with
  | 0 => False
  | S n' =>
    match R with
    | R_Refine T ps =>
        value v /\ ftv_tm v = [] /\ shape T v /\
        predicate_holds (open_qualifier_tm ps v)
    | R_Func R1 R2 =>
        value v /\ ftv_tm v = [] /\
        exists (T0 : ty) (body : tm), v = tm_abs T0 body /\
        (forall u : tm, value u -> ftv_tm u = [] ->
           (exists v', multi u v' /\ semVf n' R1 v') ->
           (exists v', multi (open_tm body u) v' /\ semVf n' (open_rty_tm R2 u) v'))
    | R_Exists R1 R2 =>
        value v /\ ftv_tm v = [] /\
        exists w : tm, value w /\ ftv_tm w = [] /\
          semVf n' R1 w /\ semVf n' (open_rty_tm R2 w) v
    | R_Poly R1 =>
        value v /\ ftv_tm v = [] /\
        exists body : tm, v = tm_tabs body /\
        (forall U : ty, closed_ty U ->
           exists v', multi (open_tm_ty body U) v' /\ semVf n' (open_rty_ty R1 U) v')
    end
  end.

Definition semV (R : rty) : tm -> Prop := semVf (rty_size R) R.

Definition semT (R : rty) (t : tm) : Prop :=
  exists v, multi t v /\ semV R v.

(** ** Fuel irrelevance *)

Lemma semVf_irrel_aux : forall m R, rty_size R <= m ->
  forall n1 n2, m <= n1 -> m <= n2 -> forall v, semVf n1 R v <-> semVf n2 R v.
Proof.
  intros m. pattern m. apply lt_wf_ind. clear m.
  intros m IH R HR n1 n2 Hn1 Hn2 v.
  destruct R as [T ps | R1 R2 | R1 R2 | R1]; simpl in HR.
  - destruct n1 as [| n1']; [lia |]. destruct n2 as [| n2']; [lia |]. simpl. tauto.
  - destruct n1 as [| n1']; [lia |]. destruct n2 as [| n2']; [lia |]. simpl.
    assert (Hs1 : rty_size R1 <= n1') by lia.
    assert (Hs1' : rty_size R1 <= n2') by lia.
    assert (Hs2 : rty_size R2 <= n1') by lia.
    assert (Hs2' : rty_size R2 <= n2') by lia.
    assert (Hlt1 : rty_size R1 < m) by lia.
    assert (Hlt2 : rty_size R2 < m) by lia.
    pose (I1 := IH (rty_size R1) Hlt1 R1 (Nat.le_refl _) n1' n2' Hs1 Hs1').
    split.
    + intros [Hv [Hf [T0 [body [Heq Hbody]]]]].
      split; [exact Hv |]. split; [exact Hf |].
      exists T0. exists body. split; [exact Heq |].
      intros u Hu Hfu [w [Hw Hsem]].
      destruct (Hbody u Hu Hfu (ex_intro _ w (conj Hw (proj2 (I1 w) Hsem)))) as [v' [Hm Hs]].
      exists v'. split; [exact Hm |].
      assert (Esize : rty_size (open_rty_tm R2 u) = rty_size R2) by apply rty_size_open_rty_tm_rec.
      pose (Io := IH (rty_size (open_rty_tm R2 u)) (ltac:(rewrite Esize; lia))
                   (open_rty_tm R2 u) (Nat.le_refl _) n1' n2'
                   (ltac:(rewrite Esize; lia)) (ltac:(rewrite Esize; lia)) v').
      exact (proj1 Io Hs).
    + intros [Hv [Hf [T0 [body [Heq Hbody]]]]].
      split; [exact Hv |]. split; [exact Hf |].
      exists T0. exists body. split; [exact Heq |].
      intros u Hu Hfu [w [Hw Hsem]].
      destruct (Hbody u Hu Hfu (ex_intro _ w (conj Hw (proj1 (I1 w) Hsem)))) as [v' [Hm Hs]].
      exists v'. split; [exact Hm |].
      assert (Esize : rty_size (open_rty_tm R2 u) = rty_size R2) by apply rty_size_open_rty_tm_rec.
      pose (Io := IH (rty_size (open_rty_tm R2 u)) (ltac:(rewrite Esize; lia))
                   (open_rty_tm R2 u) (Nat.le_refl _) n1' n2'
                   (ltac:(rewrite Esize; lia)) (ltac:(rewrite Esize; lia)) v').
      exact (proj2 Io Hs).
  - destruct n1 as [| n1']; [lia |]. destruct n2 as [| n2']; [lia |]. simpl.
    assert (Hs1 : rty_size R1 <= n1') by lia.
    assert (Hs1' : rty_size R1 <= n2') by lia.
    assert (Hlt1 : rty_size R1 < m) by lia.
    pose (I1 := IH (rty_size R1) Hlt1 R1 (Nat.le_refl _) n1' n2' Hs1 Hs1').
    split.
    + intros [Hv [Hf [w0 [Hw [Hfw [H1 H2]]]]]].
      split; [exact Hv |]. split; [exact Hf |].
      exists w0. split; [exact Hw |]. split; [exact Hfw |]. split.
      * exact (proj1 (I1 w0) H1).
      * assert (Esize : rty_size (open_rty_tm R2 w0) = rty_size R2)
          by apply rty_size_open_rty_tm_rec.
        pose (Io := IH (rty_size (open_rty_tm R2 w0)) (ltac:(rewrite Esize; lia))
                     (open_rty_tm R2 w0) (Nat.le_refl _) n1' n2'
                     (ltac:(rewrite Esize; lia)) (ltac:(rewrite Esize; lia)) v).
        exact (proj1 Io H2).
    + intros [Hv [Hf [w0 [Hw [Hfw [H1 H2]]]]]].
      split; [exact Hv |]. split; [exact Hf |].
      exists w0. split; [exact Hw |]. split; [exact Hfw |]. split.
      * exact (proj2 (I1 w0) H1).
      * assert (Esize : rty_size (open_rty_tm R2 w0) = rty_size R2)
          by apply rty_size_open_rty_tm_rec.
        pose (Io := IH (rty_size (open_rty_tm R2 w0)) (ltac:(rewrite Esize; lia))
                     (open_rty_tm R2 w0) (Nat.le_refl _) n1' n2'
                     (ltac:(rewrite Esize; lia)) (ltac:(rewrite Esize; lia)) v).
        exact (proj2 Io H2).
  - destruct n1 as [| n1']; [lia |]. destruct n2 as [| n2']; [lia |]. simpl.
    assert (Hs1 : rty_size R1 <= n1') by lia.
    assert (Hs1' : rty_size R1 <= n2') by lia.
    assert (Hlt1 : rty_size R1 < m) by lia.
    split.
    + intros [Hv [Hf [body [Heq Hbody]]]].
      split; [exact Hv |]. split; [exact Hf |].
      exists body. split; [exact Heq |].
      intros U HU. destruct (Hbody U HU) as [v' [Hm Hs]].
      exists v'. split; [exact Hm |].
      assert (Esize : rty_size (open_rty_ty R1 U) = rty_size R1)
        by apply rty_size_open_rty_ty_rec.
      pose (Io := IH (rty_size (open_rty_ty R1 U)) (ltac:(rewrite Esize; lia))
                   (open_rty_ty R1 U) (Nat.le_refl _) n1' n2'
                   (ltac:(rewrite Esize; lia)) (ltac:(rewrite Esize; lia)) v').
      exact (proj1 Io Hs).
    + intros [Hv [Hf [body [Heq Hbody]]]].
      split; [exact Hv |]. split; [exact Hf |].
      exists body. split; [exact Heq |].
      intros U HU. destruct (Hbody U HU) as [v' [Hm Hs]].
      exists v'. split; [exact Hm |].
      assert (Esize : rty_size (open_rty_ty R1 U) = rty_size R1)
        by apply rty_size_open_rty_ty_rec.
      pose (Io := IH (rty_size (open_rty_ty R1 U)) (ltac:(rewrite Esize; lia))
                   (open_rty_ty R1 U) (Nat.le_refl _) n1' n2'
                   (ltac:(rewrite Esize; lia)) (ltac:(rewrite Esize; lia)) v').
      exact (proj2 Io Hs).
Qed.


Lemma semVf_irrel : forall R n1 n2, rty_size R <= n1 -> rty_size R <= n2 ->
  forall v, semVf n1 R v <-> semVf n2 R v.
Proof.
  intros R n1 n2 H1 H2 v. apply semVf_irrel_aux with (m := rty_size R); auto.
Qed.

Lemma semTf_iff_semT : forall R g, rty_size R <= g -> forall t,
  (exists v, multi t v /\ semVf g R v) <-> semT R t.
Proof.
  intros R g Hg t. split; intros [v [Hm Hv]].
  - exists v. split; [exact Hm |].
    exact (proj1 (semVf_irrel R g (rty_size R) Hg (Nat.le_refl _) v) Hv).
  - exists v. split; [exact Hm |].
    exact (proj2 (semVf_irrel R g (rty_size R) Hg (Nat.le_refl _) v) Hv).
Qed.

Lemma semV_Refine : forall T ps v,
  semV (R_Refine T ps) v <->
  value v /\ ftv_tm v = [] /\ shape T v /\ predicate_holds (open_qualifier_tm ps v).
Proof.
  intros. unfold semV. simpl. tauto.
Qed.

Lemma semV_Func : forall R1 R2 v,
  semV (R_Func R1 R2) v <->
  value v /\ ftv_tm v = [] /\
  exists (T0 : ty) (body : tm), v = tm_abs T0 body /\
    (forall u : tm, value u -> ftv_tm u = [] -> semT R1 u ->
       semT (open_rty_tm R2 u) (open_tm body u)).
Proof.
  intros R1 R2 v. unfold semV. simpl.
  assert (Hg1 : rty_size R1 <= rty_size R1 + rty_size R2) by lia.
  assert (Hg2 : forall u, rty_size (open_rty_tm R2 u) <= rty_size R1 + rty_size R2).
  { intros u. rewrite rty_size_open_rty_tm_rec. lia. }
  split.
  - intros [Hv [Hf [T0 [body [Heq Hbody]]]]].
    split; [exact Hv |]. split; [exact Hf |].
    exists T0. exists body. split; [exact Heq |].
    intros u Hu Hfu Ht.
    destruct (Hbody u Hu Hfu (proj2 (semTf_iff_semT R1 (rty_size R1 + rty_size R2) Hg1 u) Ht))
      as [v' [Hm Hs]].
    exists v'. split; [exact Hm |].
    exact (proj1 (semVf_irrel (open_rty_tm R2 u) (rty_size R1 + rty_size R2)
                     (rty_size (open_rty_tm R2 u)) (Hg2 u) (Nat.le_refl _) v') Hs).
  - intros [Hv [Hf [T0 [body [Heq Hbody]]]]].
    split; [exact Hv |]. split; [exact Hf |].
    exists T0. exists body. split; [exact Heq |].
    intros u Hu Hfu [v' [Hm Hs]].
    assert (Ht : semT R1 u).
    { exact (proj1 (semTf_iff_semT R1 (rty_size R1 + rty_size R2) Hg1 u) (ex_intro _ v' (conj Hm Hs))). }
    destruct (Hbody u Hu Hfu Ht) as [w [Hm' Hs']].
    exists w. split; [exact Hm' |].
    exact (proj2 (semVf_irrel (open_rty_tm R2 u) (rty_size R1 + rty_size R2)
                     (rty_size (open_rty_tm R2 u)) (Hg2 u) (Nat.le_refl _) w) Hs').
Qed.

Lemma semV_Exists : forall R1 R2 v,
  semV (R_Exists R1 R2) v <->
  value v /\ ftv_tm v = [] /\
  exists w : tm, value w /\ ftv_tm w = [] /\ semV R1 w /\ semV (open_rty_tm R2 w) v.
Proof.
  intros R1 R2 v. unfold semV. simpl.
  assert (Hg1 : rty_size R1 <= rty_size R1 + rty_size R2) by lia.
  assert (Hg2 : forall w, rty_size (open_rty_tm R2 w) <= rty_size R1 + rty_size R2).
  { intros w. unfold open_rty_tm. rewrite rty_size_open_rty_tm_rec. lia. }
  split.
  - intros [Hv [Hf [w0 [Hw [Hfw [H1 H2]]]]]].
    split; [exact Hv |]. split; [exact Hf |].
    exists w0. split; [exact Hw |]. split; [exact Hfw |]. split.
    + exact (proj1 (semVf_irrel R1 (rty_size R1 + rty_size R2) (rty_size R1) Hg1 (Nat.le_refl _) w0) H1).
    + exact (proj1 (semVf_irrel (open_rty_tm R2 w0) (rty_size R1 + rty_size R2)
                     (rty_size (open_rty_tm R2 w0)) (Hg2 w0) (Nat.le_refl _) v) H2).
  - intros [Hv [Hf [w0 [Hw [Hfw [H1 H2]]]]]].
    split; [exact Hv |]. split; [exact Hf |].
    exists w0. split; [exact Hw |]. split; [exact Hfw |]. split.
    + exact (proj2 (semVf_irrel R1 (rty_size R1 + rty_size R2) (rty_size R1) Hg1 (Nat.le_refl _) w0) H1).
    + exact (proj2 (semVf_irrel (open_rty_tm R2 w0) (rty_size R1 + rty_size R2)
                     (rty_size (open_rty_tm R2 w0)) (Hg2 w0) (Nat.le_refl _) v) H2).
Qed.

Lemma semV_Poly : forall R1 v,
  semV (R_Poly R1) v <->
  value v /\ ftv_tm v = [] /\
  exists body : tm, v = tm_tabs body /\
    forall U : ty, closed_ty U -> semT (open_rty_ty R1 U) (open_tm_ty body U).
Proof.
  intros R1 v. unfold semV. simpl.
  assert (Hg : forall U, rty_size (open_rty_ty R1 U) <= rty_size R1).
  { intros U. unfold open_rty_ty. rewrite rty_size_open_rty_ty_rec. lia. }
  split.
  - intros [Hv [Hf [body [Heq Hbody]]]].
    split; [exact Hv |]. split; [exact Hf |].
    exists body. split; [exact Heq |].
    intros U HU. destruct (Hbody U HU) as [v' [Hm Hs]].
    exists v'. split; [exact Hm |].
    exact (proj1 (semVf_irrel (open_rty_ty R1 U) (rty_size R1)
                     (rty_size (open_rty_ty R1 U)) (Hg U) (Nat.le_refl _) v') Hs).
  - intros [Hv [Hf [body [Heq Hbody]]]].
    split; [exact Hv |]. split; [exact Hf |].
    exists body. split; [exact Heq |].
    intros U HU. destruct (Hbody U HU) as [v' [Hm Hs]].
    exists v'. split; [exact Hm |].
    exact (proj2 (semVf_irrel (open_rty_ty R1 U) (rty_size R1)
                     (rty_size (open_rty_ty R1 U)) (Hg U) (Nat.le_refl _) v') Hs).
Qed.

Lemma semV_value : forall R v, semV R v -> value v.
Proof.
  intros R v H. destruct R as [T ps | R1 R2 | R1 R2 | R1].
  - pose proof (proj1 (semV_Refine T ps v) H) as Hc. tauto.
  - pose proof (proj1 (semV_Func R1 R2 v) H) as Hc. tauto.
  - pose proof (proj1 (semV_Exists R1 R2 v) H) as Hc. tauto.
  - pose proof (proj1 (semV_Poly R1 v) H) as Hc. tauto.
Qed.

Lemma semV_ftv : forall R v, semV R v -> ftv_tm v = [].
Proof.
  intros R v H. destruct R as [T ps | R1 R2 | R1 R2 | R1].
  - pose proof (proj1 (semV_Refine T ps v) H) as Hc. tauto.
  - pose proof (proj1 (semV_Func R1 R2 v) H) as Hc. tauto.
  - pose proof (proj1 (semV_Exists R1 R2 v) H) as Hc. tauto.
  - pose proof (proj1 (semV_Poly R1 v) H) as Hc. tauto.
Qed.

Lemma semT_lc : forall R t, semT R t -> locally_closed_tm t.
Proof.
  intros R t [v [Hm Hv]].
  apply multi_lc_back with (u := v); [exact Hm |].
  apply value_lc. apply semV_value with (R := R). exact Hv.
Qed.

Lemma semT_safe : forall R t, semT R t -> value t \/ exists t', t --> t'.
Proof.
  intros R t [v [Hm Hv]]. destruct Hm as [t0 | t0 t1 t2 Hs Hm'].
  - left. apply semV_value with (R := R). exact Hv.
  - right. exists t1. exact Hs.
Qed.

Lemma semT_step : forall R t t', semT R t -> t --> t' -> semT R t'.
Proof.
  intros R t t' [v [Hm Hv]] Hs.
  exists v. split; [| exact Hv].
  eapply multi_det_value.
  - eapply multi_step; [exact Hs | apply multi_refl].
  - exact Hm.
  - apply semV_value with (R := R). exact Hv.
Qed.

Lemma semT_multi : forall R t t', semT R t -> multi t t' -> semT R t'.
Proof.
  intros R t t' [v [Hm Hv]] Hmt.
  exists v. split; [| exact Hv].
  eapply multi_det_value; [exact Hmt | exact Hm | apply semV_value with (R := R); exact Hv].
Qed.

Lemma semT_intro : forall R t v, multi t v -> semV R v -> semT R t.
Proof. intros. exists v. split; assumption. Qed.

Lemma semT_value_iff : forall R u, value u -> (semT R u <-> semV R u).
Proof.
  intros R u Hv. split.
  - intros [v [Hm Hs]]. rewrite (multi_from_value u Hv v Hm). exact Hs.
  - intros Hs. exists u. split; [apply multi_refl | exact Hs].
Qed.

End SystemFRefinementSem.

Module SystemFRefinementSound.
Import ListNotations SystemFRefinement SystemFRefinementLogic SystemFRefinementTyping SystemFRefinementEvaluation SystemFRefinementLib SystemFRefinementLib2 SystemFRefinementStep SystemFRefinementInv SystemFRefinementSem.

Definition env_ok (sg : tyenv) (rho : env) (RGamma : rcontext) : Prop :=
  (forall x, locally_closed_tm (rho x) /\ ftv_tm (rho x) = []) /\
  (forall x R, lookup_rcontext x RGamma = Some R ->
     semV (rty_subst_env rho (rty_ty_subst_atoms sg R)) (rho x)).

Lemma env_ok_lc : forall sg rho RGamma, env_ok sg rho RGamma ->
  forall x, locally_closed_tm (rho x).
Proof. intros sg rho RGamma [H1 H2] x. apply H1. Qed.

Lemma env_ok_ftv : forall sg rho RGamma, env_ok sg rho RGamma ->
  forall x, ftv_tm (rho x) = [].
Proof. intros sg rho RGamma [H1 H2] x. apply H1. Qed.

Lemma lookup_update_eq : forall RGamma x R0,
  lookup_rcontext x (update_rcontext RGamma x R0) = Some R0.
Proof.
  intros. simpl. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma rty_fv_rty_ty_subst_atoms : forall sg R, rty_fv (rty_ty_subst_atoms sg R) = rty_fv R.
Proof.
  intros sg R. revert R.
  induction R as [T q | R1 IHR1 R2 IHR2 | R1 IHR1 R2 IHR2 | R1 IHR1]; simpl.
  - rewrite q_ty_subst_atoms_fv. reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR1. reflexivity.
Qed.

Lemma not_in_app_iff : forall (x : atom) (l m : list atom),
  ~ In x (l ++ m) -> ~ In x l /\ ~ In x m.
Proof.
  intros x l m H. split.
  - intros Hi. apply H. apply in_app_iff. left. exact Hi.
  - intros Hi. apply H. apply in_app_iff. right. exact Hi.
Qed.

Lemma tsubst_agree : forall s s' x,
  (forall y, y <> x -> s' y = s y) ->
  forall t, ~ In x (fv_tm t) -> tsubst s' t = tsubst s t.
Proof.
  intros s s' x Hag t. revert t.
  induction t as
    [i | y | T t IHt | t1 IHt1 t2 IHt2 | t IHt | t IHt T | n | t1 IHt1 t2 IHt2 | op t1 IHt1 t2 IHt2];
    intros Hx; simpl.
  - reflexivity.
  - apply Hag. intros Heq. apply Hx. rewrite Heq. simpl. left. reflexivity.
  - f_equal. apply IHt. exact Hx.
  - apply not_in_app_iff in Hx. destruct Hx as [Hx1 Hx2].
    f_equal; [apply IHt1; exact Hx1 | apply IHt2; exact Hx2].
  - f_equal. apply IHt. exact Hx.
  - f_equal. apply IHt. exact Hx.
  - reflexivity.
  - apply not_in_app_iff in Hx. destruct Hx as [Hx1 Hx2].
    f_equal; [apply IHt1; exact Hx1 | apply IHt2; exact Hx2].
  - apply not_in_app_iff in Hx. destruct Hx as [Hx1 Hx2].
    f_equal; [apply IHt1; exact Hx1 | apply IHt2; exact Hx2].
Qed.

Lemma qsubst_agree : forall s s' x,
  (forall y, y <> x -> s' y = s y) ->
  forall q, ~ In x (q_fv q) -> qsubst s' q = qsubst s q.
Proof.
  intros s s' x Hag q. revert q.
  induction q as [| | t1 t2 | t1 t2 | t1 t2 | q1 IHq1 q2 IHq2 | q1 IHq1 q2 IHq2 | q IHq];
    intros Hx; simpl.
  - reflexivity. - reflexivity.
  - apply not_in_app_iff in Hx. destruct Hx as [Hx1 Hx2].
    f_equal; [apply tsubst_agree with (x := x); auto | apply tsubst_agree with (x := x); auto].
  - apply not_in_app_iff in Hx. destruct Hx as [Hx1 Hx2].
    f_equal; [apply tsubst_agree with (x := x); auto | apply tsubst_agree with (x := x); auto].
  - apply not_in_app_iff in Hx. destruct Hx as [Hx1 Hx2].
    f_equal; [apply tsubst_agree with (x := x); auto | apply tsubst_agree with (x := x); auto].
  - apply not_in_app_iff in Hx. destruct Hx as [Hx1 Hx2].
    f_equal; [apply IHq1; exact Hx1 | apply IHq2; exact Hx2].
  - apply not_in_app_iff in Hx. destruct Hx as [Hx1 Hx2].
    f_equal; [apply IHq1; exact Hx1 | apply IHq2; exact Hx2].
  - f_equal. apply IHq. exact Hx.
Qed.

Lemma rty_subst_env_agree : forall s s' x,
  (forall y, y <> x -> s' y = s y) ->
  forall R, ~ In x (rty_fv R) -> rty_subst_env s' R = rty_subst_env s R.
Proof.
  intros s s' x Hag R. revert R.
  induction R as [T q | R1 IHR1 R2 IHR2 | R1 IHR1 R2 IHR2 | R1 IHR1]; simpl.
  - intros Hx. f_equal. apply qsubst_agree with (x := x); auto.
  - intros Hx. apply not_in_app_iff in Hx. destruct Hx as [Hx1 Hx2].
    f_equal; [apply IHR1; exact Hx1 | apply IHR2; exact Hx2].
  - intros Hx. apply not_in_app_iff in Hx. destruct Hx as [Hx1 Hx2].
    f_equal; [apply IHR1; exact Hx1 | apply IHR2; exact Hx2].
  - intros Hx. f_equal. apply IHR1. exact Hx.
Qed.

Definition rcontext_fv (RGamma : rcontext) : list atom :=
  flat_map (fun p => rty_fv (snd p)) RGamma.

Lemma rty_fv_in_context : forall RGamma y R, lookup_rcontext y RGamma = Some R ->
  incl (rty_fv R) (rcontext_fv RGamma).
Proof.
  intros RGamma. induction RGamma as [| p rest IH]; intros y R Hlook.
  - simpl in Hlook. discriminate.
  - destruct p as [z Rz]. simpl in Hlook.
    destruct (Nat.eqb y z) eqn:E.
    + apply Nat.eqb_eq in E. subst y. inversion Hlook; subst.
      simpl. intros a Ha. apply in_app_iff. left. exact Ha.
    + simpl. intros a Ha. apply in_app_iff. right.
      exact (IH y R Hlook a Ha).
Qed.

Lemma env_ok_bind : forall sg rho RGamma x R0 v,
  env_ok sg rho RGamma ->
  ~ In x (rty_fv R0) ->
  ~ In x (rcontext_fv RGamma) ->
  locally_closed_tm v -> ftv_tm v = [] ->
  semV (rty_subst_env rho (rty_ty_subst_atoms sg R0)) v ->
  env_ok sg (fun y => if Nat.eqb y x then v else rho y) (update_rcontext RGamma x R0).
Proof.
  intros sg rho RGamma x R0 v [Himg Hb] Hfresh HfreshC Hlc Hft Hsem.
  split.
  - intros y. destruct (Nat.eqb y x) eqn:E.
    + split; [exact Hlc | exact Hft].
    + apply Himg.
  - intros y R Hlook. destruct (Nat.eqb y x) eqn:E.
    + apply Nat.eqb_eq in E. subst y.
      simpl in Hlook. rewrite Nat.eqb_refl in Hlook.
      injection Hlook as Heq. subst R.
      assert (Esub : rty_subst_env (fun y => if Nat.eqb y x then v else rho y) (rty_ty_subst_atoms sg R0)
                   = rty_subst_env rho (rty_ty_subst_atoms sg R0)).
      { apply rty_subst_env_agree with (x := x).
        - intros y Hy. destruct (Nat.eqb y x) eqn:E2.
          + apply Nat.eqb_eq in E2. contradiction.
          + reflexivity.
        - rewrite rty_fv_rty_ty_subst_atoms. exact Hfresh. }
      rewrite Esub. exact Hsem.
    + simpl in Hlook. rewrite E in Hlook.
      assert (Ex : ~ In x (rty_fv R)).
      { intros Hin. apply HfreshC. apply (rty_fv_in_context RGamma y R Hlook). exact Hin. }
      assert (Esub : rty_subst_env (fun y => if Nat.eqb y x then v else rho y) (rty_ty_subst_atoms sg R)
                   = rty_subst_env rho (rty_ty_subst_atoms sg R)).
      { apply rty_subst_env_agree with (x := x).
        - intros z Hz. destruct (Nat.eqb z x) eqn:E2.
          + apply Nat.eqb_eq in E2. contradiction.
          + reflexivity.
        - rewrite rty_fv_rty_ty_subst_atoms. exact Ex. }
      rewrite Esub. apply Hb. exact Hlook.
Qed.

Lemma ty_subst_atoms_agree : forall sg sg' X,
  (forall Y, Y <> X -> sg' Y = sg Y) ->
  forall T, ~ In X (fv_ty T) -> ty_subst_atoms sg' T = ty_subst_atoms sg T.
Proof.
  intros sg sg' X Hag T. revert T.
  induction T as [n | Y | T1 IH1 T2 IH2 | T1 IH1 |]; simpl.
  - reflexivity.
  - intros Hx. apply Hag. intros Heq. apply Hx. rewrite Heq. simpl. left. reflexivity.
  - intros Hx. apply not_in_app_iff in Hx. destruct Hx as [Hx1 Hx2].
    rewrite IH1; [|exact Hx1]. rewrite IH2; [|exact Hx2]. reflexivity.
  - intros Hx. f_equal. apply IH1. exact Hx.
  - reflexivity.
Qed.

Lemma tm_ty_subst_atoms_agree : forall sg sg' X,
  (forall Y, Y <> X -> sg' Y = sg Y) ->
  forall t, ~ In X (ftv_tm t) -> tm_ty_subst_atoms sg' t = tm_ty_subst_atoms sg t.
Proof.
  intros sg sg' X Hag t. revert t.
  induction t as
    [i | y | T t IHt | t1 IHt1 t2 IHt2 | t IHt | t IHt T | n | t1 IHt1 t2 IHt2 | op t1 IHt1 t2 IHt2];
    intros Hx; simpl.
  - reflexivity. - reflexivity.
  - apply not_in_app_iff in Hx. destruct Hx as [Hx1 Hx2].
    f_equal.
    + apply ty_subst_atoms_agree with (X := X); [exact Hag | exact Hx1].
    + apply IHt; exact Hx2.
  - apply not_in_app_iff in Hx. destruct Hx as [Hx1 Hx2].
    f_equal; [apply IHt1; exact Hx1 | apply IHt2; exact Hx2].
  - f_equal. apply IHt. exact Hx.
  - apply not_in_app_iff in Hx. destruct Hx as [Hx1 Hx2].
    f_equal.
    + apply IHt; exact Hx1.
    + apply ty_subst_atoms_agree with (X := X); [exact Hag | exact Hx2].
  - reflexivity.
  - apply not_in_app_iff in Hx. destruct Hx as [Hx1 Hx2].
    f_equal; [apply IHt1; exact Hx1 | apply IHt2; exact Hx2].
  - apply not_in_app_iff in Hx. destruct Hx as [Hx1 Hx2].
    f_equal; [apply IHt1; exact Hx1 | apply IHt2; exact Hx2].
Qed.

Lemma q_ty_subst_atoms_agree : forall sg sg' X,
  (forall Y, Y <> X -> sg' Y = sg Y) ->
  forall q, ~ In X (q_ftv q) -> q_ty_subst_atoms sg' q = q_ty_subst_atoms sg q.
Proof.
  intros sg sg' X Hag q. revert q.
  induction q as [| | t1 t2 | t1 t2 | t1 t2 | q1 IHq1 q2 IHq2 | q1 IHq1 q2 IHq2 | q IHq];
    intros Hx; simpl.
  - reflexivity. - reflexivity.
  - apply not_in_app_iff in Hx. destruct Hx as [Hx1 Hx2].
    f_equal.
    + exact (tm_ty_subst_atoms_agree sg sg' X Hag t1 Hx1).
    + exact (tm_ty_subst_atoms_agree sg sg' X Hag t2 Hx2).
  - apply not_in_app_iff in Hx. destruct Hx as [Hx1 Hx2].
    f_equal.
    + exact (tm_ty_subst_atoms_agree sg sg' X Hag t1 Hx1).
    + exact (tm_ty_subst_atoms_agree sg sg' X Hag t2 Hx2).
  - apply not_in_app_iff in Hx. destruct Hx as [Hx1 Hx2].
    f_equal.
    + exact (tm_ty_subst_atoms_agree sg sg' X Hag t1 Hx1).
    + exact (tm_ty_subst_atoms_agree sg sg' X Hag t2 Hx2).
  - apply not_in_app_iff in Hx. destruct Hx as [Hx1 Hx2].
    f_equal; [apply IHq1; exact Hx1 | apply IHq2; exact Hx2].
  - apply not_in_app_iff in Hx. destruct Hx as [Hx1 Hx2].
    f_equal; [apply IHq1; exact Hx1 | apply IHq2; exact Hx2].
  - f_equal. apply IHq. exact Hx.
Qed.

Lemma rty_ty_subst_atoms_agree : forall sg sg' X,
  (forall Y, Y <> X -> sg' Y = sg Y) ->
  forall R, ~ In X (rty_ftv R) -> rty_ty_subst_atoms sg' R = rty_ty_subst_atoms sg R.
Proof.
  intros sg sg' X Hag R. revert R.
  induction R as [T q | R1 IHR1 R2 IHR2 | R1 IHR1 R2 IHR2 | R1 IHR1]; simpl.
  - intros Hx. apply not_in_app_iff in Hx. destruct Hx as [Hx1 Hx2].
    f_equal.
    + exact (ty_subst_atoms_agree sg sg' X Hag T Hx1).
    + exact (q_ty_subst_atoms_agree sg sg' X Hag q Hx2).
  - intros Hx. apply not_in_app_iff in Hx. destruct Hx as [Hx1 Hx2].
    f_equal; [apply IHR1; exact Hx1 | apply IHR2; exact Hx2].
  - intros Hx. apply not_in_app_iff in Hx. destruct Hx as [Hx1 Hx2].
    f_equal; [apply IHR1; exact Hx1 | apply IHR2; exact Hx2].
  - intros Hx. f_equal. apply IHR1. exact Hx.
Qed.

Lemma closed_ty_int : closed_ty Ty_Int.
Proof. split; [apply lc_ty_int | reflexivity]. Qed.

Lemma closed_ty_ty_subst_atoms : forall sg T, closed_sigma sg -> locally_closed_ty T ->
  closed_ty (ty_subst_atoms sg T).
Proof.
  intros sg T Hsg Hlc. split.
  - exact (lc_ty_ty_subst_atoms 0 T Hlc sg (fun X => proj1 (Hsg X))).
  - apply ty_subst_atoms_fv_nil. intros X. exact (proj2 (Hsg X)).
Qed.

Lemma value_subst_all : forall sg s v, closed_sigma sg -> env_ok_base s ->
  value v -> value (tsubst s (tm_ty_subst_atoms sg v)).
Proof.
  intros sg s v Hsg [Hs1 Hs2] Hv.
  induction Hv as [T t Hlc0 | t Hlc0 | n].
  - simpl. apply v_abs. inversion Hlc0 as [| | K0 k0 T0 t0 HT Hbody | | | | | |]; subst.
    apply lc_tm_abs.
    + exact (lc_ty_ty_subst_atoms 0 T HT sg (fun X => proj1 (Hsg X))).
    + apply lc_tm_tsubst.
      * exact (lc_tm_tm_ty_subst_atoms 0 1 t Hbody sg (fun X => proj1 (Hsg X))).
      * intros x. exact (Hs1 x).
  - simpl. apply v_tabs. inversion Hlc0 as [| | | | K0 k0 t0 Hbody | | | |]; subst.
    apply lc_tm_tabs.
    apply lc_tm_tsubst.
    + exact (lc_tm_tm_ty_subst_atoms 1 0 t Hbody sg (fun X => proj1 (Hsg X))).
    + intros x. exact (Hs1 x).
  - simpl. apply v_int.
Qed.

Lemma ftv_subst_all : forall sg s t, closed_sigma sg -> (forall x, ftv_tm (s x) = []) ->
  ftv_tm (tsubst s (tm_ty_subst_atoms sg t)) = [].
Proof.
  intros sg s t Hsg Hft. rewrite ftv_tm_tsubst; [|exact Hft].
  apply tm_ty_subst_atoms_ftv_nil. intros X. exact (proj2 (Hsg X)).
Qed.

Lemma rty_ftv_subst_all : forall sg rho R, closed_sigma sg -> (forall x, ftv_tm (rho x) = []) ->
  rty_ftv (rty_subst_env rho (rty_ty_subst_atoms sg R)) = [].
Proof.
  intros sg rho R Hsg Hft. rewrite rty_subst_env_ftv; [|exact Hft].
  apply rty_ty_subst_atoms_ftv_nil. intros X. exact (proj2 (Hsg X)).
Qed.

Lemma open_rty_tm_subst_all : forall sg rho R u,
  (forall x, locally_closed_tm (rho x)) ->
  rty_subst_env rho (rty_ty_subst_atoms sg (open_rty_tm R u)) =
  open_rty_tm (rty_subst_env rho (rty_ty_subst_atoms sg R))
              (tsubst rho (tm_ty_subst_atoms sg u)).
Proof.
  intros sg rho R u Hlc.
  unfold open_rty_tm.
  rewrite rty_ty_subst_atoms_open_rty_tm_rec.
  rewrite rty_subst_env_open_rty_tm_rec; [reflexivity | exact Hlc].
Qed.

Lemma open_rty_ty_subst_all : forall sg rho R U,
  closed_sigma sg -> (forall x, locally_closed_tm (rho x)) ->
  rty_subst_env rho (rty_ty_subst_atoms sg (open_rty_ty R U)) =
  open_rty_ty (rty_subst_env rho (rty_ty_subst_atoms sg R)) (ty_subst_atoms sg U).
Proof.
  intros sg rho R U Hsg Hlc.
  unfold open_rty_ty.
  rewrite rty_ty_subst_atoms_open_rty_ty_rec; [|intros X; exact (proj1 (Hsg X))].
  rewrite rty_subst_env_open_rty_ty_rec; [reflexivity | exact Hlc].
Qed.

Lemma open_qualifier_subst_all : forall sg rho ps v,
  (forall x, locally_closed_tm (rho x)) -> (forall x, ftv_tm (rho x) = []) ->
  q_ty_subst_atoms sg (qsubst rho (open_qualifier_tm ps v)) =
  open_qualifier_tm (q_ty_subst_atoms sg (qsubst rho ps)) (tsubst rho (tm_ty_subst_atoms sg v)).
Proof.
  intros sg rho ps v Hlc Hft.
  unfold open_qualifier_tm.
  rewrite qsubst_open_pred_tm_rec; [|exact Hlc].
  rewrite q_ty_subst_atoms_open_pred_tm_rec.
  assert (E : tm_ty_subst_atoms sg (tsubst rho v) = tsubst rho (tm_ty_subst_atoms sg v)).
  { symmetry. apply tsubst_tm_ty_subst_atoms. exact Hft. }
  rewrite E. reflexivity.
Qed.

Lemma semT_pre : forall R t u, multi t u -> semT R u -> semT R t.
Proof.
  intros R t u Hm [v [Hm2 Hv]]. exists v. split; [|exact Hv].
  eapply multi_trans; [exact Hm | exact Hm2].
Qed.

Lemma wf_ty_closed_sigma : forall sg, closed_sigma sg -> forall Delta T, wf_ty Delta T ->
  closed_ty (ty_subst_atoms sg T).
Proof.
  intros sg Hsg Delta T Hwf. split.
  - exact (lc_ty_ty_subst_atoms 0 T (wf_ty_lc Delta T Hwf) sg (fun X => proj1 (Hsg X))).
  - apply ty_subst_atoms_fv_nil. intros X. exact (proj2 (Hsg X)).
Qed.

Lemma ty_subst_atoms_Int : forall sg, ty_subst_atoms sg Ty_Int = Ty_Int.
Proof. reflexivity. Qed.

Lemma entails_sound : forall Delta RGamma p q, entails Delta RGamma p q ->
  forall sg rho, closed_sigma sg -> env_ok sg rho RGamma ->
  predicate_holds (q_ty_subst_atoms sg (qsubst rho p)) ->
  predicate_holds (q_ty_subst_atoms sg (qsubst rho q)).
Proof.
  intros Delta RGamma p q H. induction H as
    [Delta0 RGamma0 ps
    | Delta0 RGamma0 ps
    | Delta0 RGamma0 ps qs rs H1 IH1 H2 IH2
    | Delta0 RGamma0 p0 q0
    | Delta0 RGamma0 p0 q0
    | Delta0 RGamma0 ps p0 qs H1 IH1 H2 IH2
    | Delta0 RGamma0 p0 q0
    | Delta0 RGamma0 p0 q0
    | Delta0 RGamma0 p0 q0 r0 H1 IH1 H2 IH2
    | Delta0 RGamma0 p0 q0 H1 IH1
    | Delta0 RGamma0 p0
    | Delta0 RGamma0 x T0 p0 q0 Hlook
    | Delta0 RGamma0 q0];
    intros sg rho Hsg Henv Hp.
  - exact Hp.
  - unfold predicate_holds. cbn. exact I.
  - apply IH2; [exact Hsg | exact Henv |].
    apply IH1; [exact Hsg | exact Henv | exact Hp].
  - unfold predicate_holds in Hp. cbn in Hp. exact (proj1 Hp).
  - unfold predicate_holds in Hp. cbn in Hp. exact (proj2 Hp).
  - unfold predicate_holds. cbn. split.
    + apply IH1; [exact Hsg | exact Henv | exact Hp].
    + apply IH2; [exact Hsg | exact Henv | exact Hp].
  - unfold predicate_holds. cbn. left. exact Hp.
  - unfold predicate_holds. cbn. right. exact Hp.
  - unfold predicate_holds in Hp. cbn in Hp. destruct Hp as [Hp | Hp].
    + unfold predicate_holds. apply IH1; [exact Hsg | exact Henv | exact Hp].
    + unfold predicate_holds. apply IH2; [exact Hsg | exact Henv | exact Hp].
  - unfold predicate_holds. cbn. intro Hq.
    apply IH1 with (sg := sg) (rho := rho); [exact Hsg | exact Henv |].
    split; [exact Hp | exact Hq].
  - unfold predicate_holds in Hp. cbn in Hp. destruct Hp as [Hp Hnp]. exact (Hnp Hp).
  - pose proof (proj2 Henv x (R_Refine T0 p0) Hlook) as Hsem.
    pose proof (proj1 (semV_Refine (ty_subst_atoms sg T0) (qsubst rho (q_ty_subst_atoms sg p0)) (rho x)) Hsem) as Hq.
    assert (E : q_ty_subst_atoms sg (qsubst rho (open_qualifier_tm p0 (tm_fvar x)))
              = open_qualifier_tm (qsubst rho (q_ty_subst_atoms sg p0)) (rho x)).
    { assert (E1 := open_qualifier_subst_all sg rho p0 (tm_fvar x)
                     (env_ok_lc sg rho RGamma0 Henv) (env_ok_ftv sg rho RGamma0 Henv)).
      assert (E2 : q_ty_subst_atoms sg (qsubst rho p0) = qsubst rho (q_ty_subst_atoms sg p0)).
      { symmetry. apply qsubst_q_ty_subst_atoms.
        apply env_ok_ftv with (sg := sg) (RGamma := RGamma0); exact Henv. }
      rewrite E2 in E1. exact E1. }
    rewrite E. exact (proj2 (proj2 (proj2 Hq))).
  - unfold predicate_holds in Hp. cbn in Hp. destruct Hp.
Qed.

Lemma subst_all_open_rty_tm_fvar : forall sg rho RGamma x R0 u,
  env_ok sg rho RGamma -> locally_closed_tm u -> ~ In x (rty_fv R0) ->
  rty_subst_env (fun y => if Nat.eqb y x then u else rho y)
     (rty_ty_subst_atoms sg (open_rty_tm R0 (tm_fvar x)))
  = open_rty_tm (rty_subst_env rho (rty_ty_subst_atoms sg R0)) u.
Proof.
  intros sg rho RGamma x R0 u Henv Hu Hx.
  unfold open_rty_tm.
  rewrite rty_ty_subst_atoms_open_rty_tm_rec.
  rewrite rty_subst_env_open_rty_tm_rec.
  - simpl. rewrite Nat.eqb_refl. simpl.
    f_equal.
    apply rty_subst_env_agree with (x := x).
    + intros y Hy. destruct (Nat.eqb y x) eqn:E.
      * apply Nat.eqb_eq in E. contradiction.
      * reflexivity.
    + rewrite rty_fv_rty_ty_subst_atoms. exact Hx.
  - intros y. destruct (Nat.eqb y x) eqn:E.
    + exact Hu.
    + apply env_ok_lc with (sg := sg) (RGamma := RGamma); exact Henv.
Qed.

Lemma subst_all_open_body_fvar : forall sg rho x body u,
  (forall y, locally_closed_tm (rho y)) -> locally_closed_tm u ->
  ~ In x (fv_tm body) ->
  tsubst (fun y => if Nat.eqb y x then u else rho y)
    (tm_ty_subst_atoms sg (open_tm body (tm_fvar x)))
  = open_tm (tsubst rho (tm_ty_subst_atoms sg body)) u.
Proof.
  intros sg rho x body u Hlc Hu Hx.
  unfold open_tm.
  rewrite tm_ty_subst_atoms_open_tm_rec.
  rewrite tsubst_open_tm_rec.
  - simpl. rewrite Nat.eqb_refl. simpl.
    assert (Hagree : tsubst (fun y => if Nat.eqb y x then u else rho y) (tm_ty_subst_atoms sg body)
                   = tsubst rho (tm_ty_subst_atoms sg body)).
    { apply tsubst_agree with (x := x).
      - intros y Hy. destruct (Nat.eqb y x) eqn:E.
        + apply Nat.eqb_eq in E. contradiction.
        + reflexivity.
      - rewrite fv_tm_tm_ty_subst_atoms. exact Hx. }
    rewrite Hagree. reflexivity.
  - intros y. destruct (Nat.eqb y x) eqn:E.
    + exact Hu.
    + apply Hlc.
Qed.

Lemma rty_subst_all_open_rty_ty_fvar : forall sg sg' rho R0 X U,
  closed_sigma sg -> closed_sigma sg' ->
  (forall Y, Y <> X -> sg' Y = sg Y) -> sg' X = U ->
  (forall y, locally_closed_tm (rho y)) ->
  ~ In X (rty_ftv R0) ->
  rty_subst_env rho (rty_ty_subst_atoms sg' (open_rty_ty R0 (Ty_FVar X)))
  = open_rty_ty (rty_subst_env rho (rty_ty_subst_atoms sg R0)) U.
Proof.
  intros sg sg' rho R0 X U Hsg Hsg' Hagree HX Hrho Hfresh.
  unfold open_rty_ty.
  rewrite rty_ty_subst_atoms_open_rty_ty_rec.
  - simpl.
    rewrite HX.
    rewrite (rty_ty_subst_atoms_agree sg sg' X Hagree R0 Hfresh).
    rewrite rty_subst_env_open_rty_ty_rec.
    + reflexivity.
    + exact Hrho.
  - intros Y. exact (proj1 (Hsg' Y)).
Qed.

Lemma subst_all_open_body_ty_fvar : forall sg sg' rho body X U,
  closed_sigma sg' -> (forall Y, Y <> X -> sg' Y = sg Y) -> sg' X = U ->
  (forall y, locally_closed_tm (rho y)) ->
  ~ In X (ftv_tm body) ->
  tsubst rho (tm_ty_subst_atoms sg' (open_tm_ty body (Ty_FVar X)))
  = open_tm_ty (tsubst rho (tm_ty_subst_atoms sg body)) U.
Proof.
  intros sg sg' rho body X U Hsg' Hagree HX Hrho Hfresh.
  unfold open_tm_ty.
  rewrite tm_ty_subst_atoms_open_tm_ty_rec.
  - simpl.
    rewrite HX.
    rewrite (tm_ty_subst_atoms_agree sg sg' X Hagree body Hfresh).
    apply tsubst_open_tm_ty_rec.
    exact Hrho.
  - intros Y. exact (proj1 (Hsg' Y)).
Qed.

Scheme has_rtype_mut := Induction for has_rtype Sort Prop
  with subtype_mut := Induction for subtype Sort Prop.

Check has_rtype_mut.

End SystemFRefinementSound.

Module SystemFRefinementTask.
Import ListNotations SystemFRefinement SystemFRefinementLogic SystemFRefinementTyping SystemFRefinementEvaluation SystemFRefinementLib SystemFRefinementLib2 SystemFRefinementStep SystemFRefinementInv SystemFRefinementSem.

Theorem never_stuck : forall (t t' : tm) (R : rty),
  has_rtype [] empty_rcontext t R ->
  multi t t' ->
  value t' \/ exists t'' : tm, t' --> t''.
Proof.

Qed.

End SystemFRefinementTask.
