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

Module SystemFRefinementSemantics.
Import ListNotations SystemFRefinement SystemFRefinementLogic SystemFRefinementTyping SystemFRefinementEvaluation.

(* ============================================================ *)
(* Freshness utilities                                          *)
(* ============================================================ *)

Lemma max_atom_ge : forall (L : list atom) (x : atom), In x L -> x <= max_atom L.
Proof.
  induction L as [| a L IH]; intros x Hin; simpl in *.
  - inversion Hin.
  - destruct Hin as [-> | Hin].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; eassumption | apply Nat.le_max_r].
Qed.

Lemma fresh_not_in : forall (L : list atom), ~ In (fresh L) L.
Proof.
  intros L Hin. unfold fresh in *.
  pose proof max_atom_ge L _ Hin. lia.
Qed.

Lemma fresh_not_in_app_l : forall (L1 L2 : list atom),
  ~ In (fresh (L1 ++ L2)) L1.
Proof.
  intros L1 L2 Hin.
  apply (fresh_not_in (L1 ++ L2)).
  apply in_app_iff. left. exact Hin.
Qed.

Lemma fresh_not_in_app_r : forall (L1 L2 : list atom),
  ~ In (fresh (L1 ++ L2)) L2.
Proof.
  intros L1 L2 Hin.
  apply (fresh_not_in (L1 ++ L2)).
  apply in_app_iff. right. exact Hin.
Qed.

(* ============================================================ *)
(* Closing substitutions (environments)                         *)
(* ============================================================ *)

Definition upd_tm (x : atom) (w : tm) (sigma : atom -> tm) : atom -> tm :=
  fun y => if Nat.eqb y x then w else sigma y.

Definition upd_ty (X : atom) (U : ty) (rho : atom -> ty) : atom -> ty :=
  fun Y => if Nat.eqb Y X then U else rho Y.

Lemma upd_tm_eq : forall x w sigma, upd_tm x w sigma x = w.
Proof. intros. unfold upd_tm. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma upd_tm_neq : forall x y w sigma, x <> y -> upd_tm x w sigma y = sigma y.
Proof.
  intros x y w sigma H. unfold upd_tm.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. congruence.
  - reflexivity.
Qed.

Lemma upd_ty_eq : forall X U rho, upd_ty X U rho X = U.
Proof. intros. unfold upd_ty. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma upd_ty_neq : forall X Y U rho, X <> Y -> upd_ty X U rho Y = rho Y.
Proof.
  intros X Y U rho H. unfold upd_ty.
  destruct (Nat.eqb Y X) eqn:E.
  - apply Nat.eqb_eq in E. congruence.
  - reflexivity.
Qed.

Fixpoint ty_env (rho : atom -> ty) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => rho X
  | Ty_Arrow T1 T2 => Ty_Arrow (ty_env rho T1) (ty_env rho T2)
  | Ty_All T1 => Ty_All (ty_env rho T1)
  | Ty_Int => Ty_Int
  end.

Fixpoint tm_env (rho : atom -> ty) (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_abs T t1 => tm_abs (ty_env rho T) (tm_env rho sigma t1)
  | tm_app t1 t2 => tm_app (tm_env rho sigma t1) (tm_env rho sigma t2)
  | tm_tabs t1 => tm_tabs (tm_env rho sigma t1)
  | tm_tapp t1 T => tm_tapp (tm_env rho sigma t1) (ty_env rho T)
  | tm_int n => tm_int n
  | tm_div t1 t2 => tm_div (tm_env rho sigma t1) (tm_env rho sigma t2)
  | tm_arith op t1 t2 => tm_arith op (tm_env rho sigma t1) (tm_env rho sigma t2)
  end.

Fixpoint qual_env (rho : atom -> ty) (sigma : atom -> tm) (q : qualifier) : qualifier :=
  match q with
  | Pred_True => Pred_True
  | Pred_False => Pred_False
  | Pred_Eq t1 t2 => Pred_Eq (tm_env rho sigma t1) (tm_env rho sigma t2)
  | Pred_Lt t1 t2 => Pred_Lt (tm_env rho sigma t1) (tm_env rho sigma t2)
  | Pred_Le t1 t2 => Pred_Le (tm_env rho sigma t1) (tm_env rho sigma t2)
  | Pred_And p1 p2 => Pred_And (qual_env rho sigma p1) (qual_env rho sigma p2)
  | Pred_Or p1 p2 => Pred_Or (qual_env rho sigma p1) (qual_env rho sigma p2)
  | Pred_Not p1 => Pred_Not (qual_env rho sigma p1)
  end.

Fixpoint rty_env (rho : atom -> ty) (sigma : atom -> tm) (R : rty) : rty :=
  match R with
  | R_Refine T ps => R_Refine (ty_env rho T) (qual_env rho sigma ps)
  | R_Func R1 R2 => R_Func (rty_env rho sigma R1) (rty_env rho sigma R2)
  | R_Exists R1 R2 => R_Exists (rty_env rho sigma R1) (rty_env rho sigma R2)
  | R_Poly R1 => R_Poly (rty_env rho sigma R1)
  end.

(* Identity environment *)
Lemma ty_env_id : forall T, ty_env (fun X => Ty_FVar X) T = T.
Proof.
  induction T; simpl; try reflexivity; f_equal; assumption.
Qed.

Lemma tm_env_id : forall t, tm_env (fun X => Ty_FVar X) (fun x => tm_fvar x) t = t.
Proof.
  induction t; simpl; try reflexivity.
  - f_equal; [apply ty_env_id | apply IHt].
  - f_equal; assumption.
  - f_equal. apply IHt.
  - f_equal; [assumption | apply ty_env_id].
  - f_equal; assumption.
  - f_equal; assumption.
Qed.

Lemma qual_env_id : forall q,
  qual_env (fun X => Ty_FVar X) (fun x => tm_fvar x) q = q.
Proof.
  induction q; simpl; try reflexivity.
  - f_equal; apply tm_env_id.
  - f_equal; apply tm_env_id.
  - f_equal; apply tm_env_id.
  - f_equal; assumption.
  - f_equal; assumption.
  - f_equal; assumption.
Qed.

Lemma rty_env_id : forall R,
  rty_env (fun X => Ty_FVar X) (fun x => tm_fvar x) R = R.
Proof.
  induction R; simpl.
  - f_equal; [apply ty_env_id | apply qual_env_id].
  - f_equal; assumption.
  - f_equal; assumption.
  - f_equal; assumption.
Qed.

(* ============================================================ *)
(* Free variables of qualifiers and rties                       *)
(* ============================================================ *)

Fixpoint fv_qual (q : qualifier) : list atom :=
  match q with
  | Pred_True | Pred_False => []
  | Pred_Eq t1 t2 | Pred_Lt t1 t2 | Pred_Le t1 t2 => fv_tm t1 ++ fv_tm t2
  | Pred_And p1 p2 | Pred_Or p1 p2 => fv_qual p1 ++ fv_qual p2
  | Pred_Not p1 => fv_qual p1
  end.

Fixpoint ftv_qual (q : qualifier) : list atom :=
  match q with
  | Pred_True | Pred_False => []
  | Pred_Eq t1 t2 | Pred_Lt t1 t2 | Pred_Le t1 t2 => ftv_tm t1 ++ ftv_tm t2
  | Pred_And p1 p2 | Pred_Or p1 p2 => ftv_qual p1 ++ ftv_qual p2
  | Pred_Not p1 => ftv_qual p1
  end.

Fixpoint fv_rty (R : rty) : list atom :=
  match R with
  | R_Refine T ps => fv_qual ps
  | R_Func R1 R2 => fv_rty R1 ++ fv_rty R2
  | R_Exists R1 R2 => fv_rty R1 ++ fv_rty R2
  | R_Poly R1 => fv_rty R1
  end.

Fixpoint ftv_rty (R : rty) : list atom :=
  match R with
  | R_Refine T ps => fv_ty T ++ ftv_qual ps
  | R_Func R1 R2 => ftv_rty R1 ++ ftv_rty R2
  | R_Exists R1 R2 => ftv_rty R1 ++ ftv_rty R2
  | R_Poly R1 => ftv_rty R1
  end.

(* ============================================================ *)
(* Environment extension lemmas                                 *)
(* ============================================================ *)

Lemma tm_env_upd_notin : forall t x w rho sigma,
  ~ In x (fv_tm t) -> tm_env rho (upd_tm x w sigma) t = tm_env rho sigma t.
Proof.
  induction t; intros x w rho sigma Hnot; simpl in *.
  - reflexivity.
  - apply upd_tm_neq. intros ->. apply Hnot. simpl. auto.
  - f_equal. apply IHt. exact Hnot.
  - f_equal.
    + apply IHt1. intro Hin. apply Hnot. apply in_app_iff. auto.
    + apply IHt2. intro Hin. apply Hnot. apply in_app_iff. auto.
  - f_equal. apply IHt. exact Hnot.
  - f_equal. apply IHt. exact Hnot.
  - reflexivity.
  - f_equal.
    + apply IHt1. intro Hin. apply Hnot. apply in_app_iff. auto.
    + apply IHt2. intro Hin. apply Hnot. apply in_app_iff. auto.
  - f_equal.
    + apply IHt1. intro Hin. apply Hnot. apply in_app_iff. auto.
    + apply IHt2. intro Hin. apply Hnot. apply in_app_iff. auto.
Qed.

Lemma ty_env_upd_notin : forall T X U rho,
  ~ In X (fv_ty T) -> ty_env (upd_ty X U rho) T = ty_env rho T.
Proof.
  induction T; intros X U rho Hnot; simpl in *.
  - reflexivity.
  - apply upd_ty_neq. intros ->. apply Hnot. simpl. auto.
  - f_equal.
    + apply IHT1. intro Hin. apply Hnot. apply in_app_iff. auto.
    + apply IHT2. intro Hin. apply Hnot. apply in_app_iff. auto.
  - f_equal. apply IHT. exact Hnot.
  - reflexivity.
Qed.

Lemma qual_env_upd_tm_notin : forall q x w rho sigma,
  ~ In x (fv_qual q) -> qual_env rho (upd_tm x w sigma) q = qual_env rho sigma q.
Proof.
  induction q; intros x w rho sigma Hnot; simpl in *.
  - reflexivity.
  - reflexivity.
  - f_equal; apply tm_env_upd_notin; intro Hin; apply Hnot; apply in_app_iff; auto.
  - f_equal; apply tm_env_upd_notin; intro Hin; apply Hnot; apply in_app_iff; auto.
  - f_equal; apply tm_env_upd_notin; intro Hin; apply Hnot; apply in_app_iff; auto.
  - f_equal.
    + apply IHq1. intro Hin. apply Hnot. apply in_app_iff. auto.
    + apply IHq2. intro Hin. apply Hnot. apply in_app_iff. auto.
  - f_equal.
    + apply IHq1. intro Hin. apply Hnot. apply in_app_iff. auto.
    + apply IHq2. intro Hin. apply Hnot. apply in_app_iff. auto.
  - f_equal. apply IHq. exact Hnot.
Qed.

Lemma tm_env_ty_upd_notin : forall t X U rho sigma,
  ~ In X (ftv_tm t) -> tm_env (upd_ty X U rho) sigma t = tm_env rho sigma t.
Proof.
  induction t; intros X U rho sigma Hnot; simpl in *.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + apply ty_env_upd_notin. intro Hin. apply Hnot. apply in_app_iff. left. exact Hin.
    + apply IHt. intro Hin. apply Hnot. apply in_app_iff. right. exact Hin.
  - f_equal.
    + apply IHt1. intro Hin. apply Hnot. apply in_app_iff. auto.
    + apply IHt2. intro Hin. apply Hnot. apply in_app_iff. auto.
  - f_equal. apply IHt. exact Hnot.
  - f_equal.
    + apply IHt. intro Hin. apply Hnot. apply in_app_iff. auto.
    + apply ty_env_upd_notin. intro Hin. apply Hnot. apply in_app_iff. auto.
  - reflexivity.
  - f_equal.
    + apply IHt1. intro Hin. apply Hnot. apply in_app_iff. auto.
    + apply IHt2. intro Hin. apply Hnot. apply in_app_iff. auto.
  - f_equal.
    + apply IHt1. intro Hin. apply Hnot. apply in_app_iff. auto.
    + apply IHt2. intro Hin. apply Hnot. apply in_app_iff. auto.
Qed.

Lemma qual_env_upd_ty_notin : forall q X U rho sigma,
  ~ In X (ftv_qual q) -> qual_env (upd_ty X U rho) sigma q = qual_env rho sigma q.
Proof.
  induction q; intros X U rho sigma Hnot; simpl in *.
  - reflexivity.
  - reflexivity.
  - f_equal; apply tm_env_ty_upd_notin; intro Hin; apply Hnot; apply in_app_iff; auto.
  - f_equal; apply tm_env_ty_upd_notin; intro Hin; apply Hnot; apply in_app_iff; auto.
  - f_equal; apply tm_env_ty_upd_notin; intro Hin; apply Hnot; apply in_app_iff; auto.
  - f_equal.
    + apply IHq1. intro Hin. apply Hnot. apply in_app_iff. auto.
    + apply IHq2. intro Hin. apply Hnot. apply in_app_iff. auto.
  - f_equal.
    + apply IHq1. intro Hin. apply Hnot. apply in_app_iff. auto.
    + apply IHq2. intro Hin. apply Hnot. apply in_app_iff. auto.
  - f_equal. apply IHq. exact Hnot.
Qed.

Lemma rty_env_upd_tm_notin : forall R x w rho sigma,
  ~ In x (fv_rty R) -> rty_env rho (upd_tm x w sigma) R = rty_env rho sigma R.
Proof.
  induction R; intros x w rho sigma Hnot; simpl in *.
  - f_equal. apply qual_env_upd_tm_notin. exact Hnot.
  - f_equal.
    + apply IHR1. intro Hin. apply Hnot. apply in_app_iff. auto.
    + apply IHR2. intro Hin. apply Hnot. apply in_app_iff. auto.
  - f_equal.
    + apply IHR1. intro Hin. apply Hnot. apply in_app_iff. auto.
    + apply IHR2. intro Hin. apply Hnot. apply in_app_iff. auto.
  - f_equal. apply IHR. exact Hnot.
Qed.

Lemma rty_env_upd_ty_notin : forall R X U rho sigma,
  ~ In X (ftv_rty R) -> rty_env (upd_ty X U rho) sigma R = rty_env rho sigma R.
Proof.
  induction R; intros X U rho sigma Hnot; simpl in *.
  - f_equal.
    + apply ty_env_upd_notin. intro Hin. apply Hnot. apply in_app_iff. left. exact Hin.
    + apply qual_env_upd_ty_notin. intro Hin. apply Hnot. apply in_app_iff. right. exact Hin.
  - f_equal.
    + apply IHR1. intro Hin. apply Hnot. apply in_app_iff. auto.
    + apply IHR2. intro Hin. apply Hnot. apply in_app_iff. auto.
  - f_equal.
    + apply IHR1. intro Hin. apply Hnot. apply in_app_iff. auto.
    + apply IHR2. intro Hin. apply Hnot. apply in_app_iff. auto.
  - f_equal. apply IHR. exact Hnot.
Qed.


(* ============================================================ *)
(* Opening / closing commutation                                *)
(* ============================================================ *)

Lemma open_tm_rec_lc_id : forall t K k, lc_tm_at K k t ->
  forall j u, k <= j -> open_tm_rec j u t = t.
Proof.
  intros t K k H. induction H; intros j u Hle; simpl.
  - destruct (Nat.eqb j i) eqn:E.
    + apply Nat.eqb_eq in E. exfalso. lia.
    + reflexivity.
  - reflexivity.
  - f_equal. apply IHlc_tm_at. lia.
  - f_equal.
    + apply IHlc_tm_at1. exact Hle.
    + apply IHlc_tm_at2. exact Hle.
  - f_equal. apply IHlc_tm_at. exact Hle.
  - f_equal. apply IHlc_tm_at. exact Hle.
  - reflexivity.
  - f_equal.
    + apply IHlc_tm_at1. exact Hle.
    + apply IHlc_tm_at2. exact Hle.
  - f_equal.
    + apply IHlc_tm_at1. exact Hle.
    + apply IHlc_tm_at2. exact Hle.
Qed.

Lemma open_ty_rec_lc_id : forall T k, lc_ty_at k T ->
  forall j U, k <= j -> open_ty_rec j U T = T.
Proof.
  intros T k H. induction H; intros j U Hle; simpl.
  - destruct (Nat.eqb j i) eqn:E.
    + apply Nat.eqb_eq in E. exfalso. lia.
    + reflexivity.
  - reflexivity.
  - f_equal.
    + apply IHlc_ty_at1. exact Hle.
    + apply IHlc_ty_at2. exact Hle.
  - f_equal. apply IHlc_ty_at. lia.
  - reflexivity.
Qed.

Lemma tm_env_open_tm_rec : forall rho sigma t k u,
  (forall x, locally_closed_tm (sigma x)) ->
  tm_env rho sigma (open_tm_rec k u t) =
  open_tm_rec k (tm_env rho sigma u) (tm_env rho sigma t).
Proof.
  induction t as [i | x | T t1 IHt1 | t1 IHt1 t2 IHt2 | t1 IHt1 | t1 IHt1 T | n | t1 IHt1 t2 IHt2 | op t1 IHt1 t2 IHt2]; intros k u Hsig; simpl in *.
  - destruct (Nat.eqb k i); reflexivity.
  - symmetry. apply open_tm_rec_lc_id with (K := 0) (k := 0); [apply Hsig | lia].
  - f_equal. apply IHt1. exact Hsig.
  - f_equal; auto.
  - f_equal. apply IHt1. exact Hsig.
  - f_equal; auto.
  - reflexivity.
  - f_equal; auto.
  - f_equal; auto.
Qed.

Lemma ty_env_open_ty_rec : forall rho T k U,
  (forall X, locally_closed_ty (rho X)) ->
  ty_env rho (open_ty_rec k U T) = open_ty_rec k (ty_env rho U) (ty_env rho T).
Proof.
  induction T as [i | X | T1 IH1 T2 IH2 | T1 IH1 | ]; intros k U Hrho; simpl in *.
  - destruct (Nat.eqb k i); reflexivity.
  - symmetry. apply open_ty_rec_lc_id with (k := 0); [apply Hrho | lia].
  - f_equal; auto.
  - simpl. f_equal. apply IH1 with (k := S k); exact Hrho.
  - reflexivity.
Qed.

Lemma qual_env_open_tm_rec : forall rho sigma q k u,
  (forall x, locally_closed_tm (sigma x)) ->
  qual_env rho sigma (open_qualifier_tm_rec k u q) =
  open_qualifier_tm_rec k (tm_env rho sigma u) (qual_env rho sigma q).
Proof.
  induction q; intros k u Hsig; simpl in *; try reflexivity.
  - f_equal; apply tm_env_open_tm_rec; exact Hsig.
  - f_equal; apply tm_env_open_tm_rec; exact Hsig.
  - f_equal; apply tm_env_open_tm_rec; exact Hsig.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
Qed.

Lemma rty_env_open_rty_tm_rec : forall rho sigma R k u,
  (forall x, locally_closed_tm (sigma x)) ->
  rty_env rho sigma (open_rty_tm_rec k u R) =
  open_rty_tm_rec k (tm_env rho sigma u) (rty_env rho sigma R).
Proof.
  induction R; intros k u Hsig; simpl in *.
  - f_equal. apply qual_env_open_tm_rec. exact Hsig.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
Qed.

Lemma open_tm_ty_rec_lc_id : forall t K k, lc_tm_at K k t ->
  forall j U, K <= j -> open_tm_ty_rec j U t = t.
Proof.
  intros t K k H. induction H; intros j U Hle; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + apply open_ty_rec_lc_id with (k := K); assumption.
    + apply IHlc_tm_at. exact Hle.
  - f_equal.
    + apply IHlc_tm_at1. exact Hle.
    + apply IHlc_tm_at2. exact Hle.
  - f_equal. apply IHlc_tm_at. lia.
  - f_equal.
    + apply IHlc_tm_at. exact Hle.
    + apply open_ty_rec_lc_id with (k := K); assumption.
  - reflexivity.
  - f_equal.
    + apply IHlc_tm_at1. exact Hle.
    + apply IHlc_tm_at2. exact Hle.
  - f_equal.
    + apply IHlc_tm_at1. exact Hle.
    + apply IHlc_tm_at2. exact Hle.
Qed.

Lemma tm_env_open_tm_ty_rec : forall rho sigma t k U,
  (forall X, locally_closed_ty (rho X)) ->
  (forall x, locally_closed_tm (sigma x)) ->
  tm_env rho sigma (open_tm_ty_rec k U t) =
  open_tm_ty_rec k (ty_env rho U) (tm_env rho sigma t).
Proof.
  induction t; intros k U Hrho Hsig; simpl in *; try reflexivity.
  - symmetry. apply open_tm_ty_rec_lc_id with (K := 0) (k := 0); [apply Hsig | lia].
  - f_equal.
    + apply ty_env_open_ty_rec. exact Hrho.
    + apply IHt; assumption.
  - f_equal; auto.
  - f_equal. apply IHt. exact Hrho. exact Hsig.
  - f_equal.
    + apply IHt; assumption.
    + apply ty_env_open_ty_rec. exact Hrho.
  - f_equal; auto.
  - f_equal; auto.
Qed.

Lemma qual_env_open_ty_rec : forall rho sigma q k U,
  (forall X, locally_closed_ty (rho X)) ->
  (forall x, locally_closed_tm (sigma x)) ->
  qual_env rho sigma (open_qualifier_ty_rec k U q) =
  open_qualifier_ty_rec k (ty_env rho U) (qual_env rho sigma q).
Proof.
  induction q; intros k U Hrho Hsig; simpl in *; try reflexivity.
  - f_equal; apply tm_env_open_tm_ty_rec; assumption.
  - f_equal; apply tm_env_open_tm_ty_rec; assumption.
  - f_equal; apply tm_env_open_tm_ty_rec; assumption.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
Qed.

Lemma rty_env_open_rty_ty_rec : forall rho sigma R k U,
  (forall X, locally_closed_ty (rho X)) ->
  (forall x, locally_closed_tm (sigma x)) ->
  rty_env rho sigma (open_rty_ty_rec k U R) =
  open_rty_ty_rec k (ty_env rho U) (rty_env rho sigma R).
Proof.
  induction R; intros k U Hrho Hsig; simpl in *.
  - f_equal.
    + apply ty_env_open_ty_rec. exact Hrho.
    + apply qual_env_open_ty_rec; assumption.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
Qed.

(* Specialized commutation lemmas (top-level openings) *)

Lemma qual_env_open_tm : forall rho sigma q u,
  (forall x, locally_closed_tm (sigma x)) ->
  qual_env rho sigma (open_qualifier_tm q u) =
  open_qualifier_tm (qual_env rho sigma q) (tm_env rho sigma u).
Proof. intros. apply qual_env_open_tm_rec. exact H. Qed.

Lemma tm_env_open_tm : forall rho sigma t u,
  (forall x, locally_closed_tm (sigma x)) ->
  tm_env rho sigma (open_tm t u) =
  open_tm (tm_env rho sigma t) (tm_env rho sigma u).
Proof. intros. apply tm_env_open_tm_rec. exact H. Qed.

Lemma rty_env_open_rty_tm : forall rho sigma R u,
  (forall x, locally_closed_tm (sigma x)) ->
  rty_env rho sigma (open_rty_tm R u) =
  open_rty_tm (rty_env rho sigma R) (tm_env rho sigma u).
Proof. intros. apply rty_env_open_rty_tm_rec. exact H. Qed.

Lemma rty_env_open_rty_ty : forall rho sigma R U,
  (forall X, locally_closed_ty (rho X)) ->
  (forall x, locally_closed_tm (sigma x)) ->
  rty_env rho sigma (open_rty_ty R U) =
  open_rty_ty (rty_env rho sigma R) (ty_env rho U).
Proof. intros. apply rty_env_open_rty_ty_rec; assumption. Qed.

Lemma tm_env_open_tm_ty : forall rho sigma t U,
  (forall X, locally_closed_ty (rho X)) ->
  (forall x, locally_closed_tm (sigma x)) ->
  tm_env rho sigma (open_tm_ty t U) =
  open_tm_ty (tm_env rho sigma t) (ty_env rho U).
Proof. intros. apply tm_env_open_tm_ty_rec; assumption. Qed.

(* ============================================================ *)
(* locally-closed monotonicity and opening lemmas               *)
(* ============================================================ *)

Lemma lc_ty_at_mono : forall k k' T, k <= k' -> lc_ty_at k T -> lc_ty_at k' T.
Proof.
  intros k k' T Hle H. revert k' Hle.
  induction H; intros k' Hle.
  - apply lc_ty_bvar. lia.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow.
    + apply IHlc_ty_at1. assumption.
    + apply IHlc_ty_at2. assumption.
  - apply lc_ty_all. apply IHlc_ty_at. lia.
  - apply lc_ty_int.
Qed.

Lemma lc_tm_at_mono_k : forall K k k' t, k <= k' -> lc_tm_at K k t -> lc_tm_at K k' t.
Proof.
  intros K k k' t Hle H. revert k' Hle.
  induction H; intros k' Hle.
  - apply lc_tm_bvar. lia.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + assumption.
    + apply IHlc_tm_at. lia.
  - apply lc_tm_app.
    + apply IHlc_tm_at1. assumption.
    + apply IHlc_tm_at2. assumption.
  - apply lc_tm_tabs. apply IHlc_tm_at. exact Hle.
  - apply lc_tm_tapp.
    + apply IHlc_tm_at. assumption.
    + assumption.
  - apply lc_tm_int.
  - apply lc_tm_div.
    + apply IHlc_tm_at1. assumption.
    + apply IHlc_tm_at2. assumption.
  - apply lc_tm_arith.
    + apply IHlc_tm_at1. assumption.
    + apply IHlc_tm_at2. assumption.
Qed.

Lemma lc_tm_at_mono_K : forall K K' k t, K <= K' -> lc_tm_at K k t -> lc_tm_at K' k t.
Proof.
  intros K K' k t Hle H. revert K' Hle.
  induction H; intros K' Hle.
  - apply lc_tm_bvar. assumption.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + apply lc_ty_at_mono with (k := K); assumption.
    + apply IHlc_tm_at. assumption.
  - apply lc_tm_app.
    + apply IHlc_tm_at1. assumption.
    + apply IHlc_tm_at2. assumption.
  - apply lc_tm_tabs. apply IHlc_tm_at. lia.
  - apply lc_tm_tapp.
    + apply IHlc_tm_at. assumption.
    + apply lc_ty_at_mono with (k := K); assumption.
  - apply lc_tm_int.
  - apply lc_tm_div.
    + apply IHlc_tm_at1. assumption.
    + apply IHlc_tm_at2. assumption.
  - apply lc_tm_arith.
    + apply IHlc_tm_at1. assumption.
    + apply IHlc_tm_at2. assumption.
Qed.

Lemma lc_ty_open_backward : forall T k U,
  lc_ty_at k U -> lc_ty_at k (open_ty_rec k U T) -> lc_ty_at (S k) T.
Proof.
  induction T as [i | X | T1 IH1 T2 IH2 | T1 IH1 | ];
  intros k U HU Hopen; simpl in *.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst. apply lc_ty_bvar. lia.
    + inversion Hopen; subst. apply lc_ty_bvar. lia.
  - apply lc_ty_fvar.
  - inversion Hopen; subst. apply lc_ty_arrow.
    + apply IH1 with (k := k) (U := U); assumption.
    + apply IH2 with (k := k) (U := U); assumption.
  - inversion Hopen; subst. apply lc_ty_all.
    apply IH1 with (U := U).
    + apply lc_ty_at_mono with (k := k); [lia | assumption].
    + assumption.
  - apply lc_ty_int.
Qed.

Lemma lc_ty_open_forward : forall T k U,
  lc_ty_at (S k) T -> lc_ty_at k U -> lc_ty_at k (open_ty_rec k U T).
Proof.
  induction T as [i | X | T1 IH1 T2 IH2 | T1 IH1 | ];
  intros k U HT HU; simpl in *.
  - destruct (Nat.eqb k i) eqn:E.
    + apply HU.
    + apply Nat.eqb_neq in E. inversion HT; subst. apply lc_ty_bvar. lia.
  - apply lc_ty_fvar.
  - inversion HT; subst. apply lc_ty_arrow.
    + apply IH1 with (U := U); assumption.
    + apply IH2 with (U := U); assumption.
  - inversion HT; subst. apply lc_ty_all.
    apply IH1 with (U := U).
    + assumption.
    + apply lc_ty_at_mono with (k := k); [lia | assumption].
  - apply lc_ty_int.
Qed.

Lemma lc_tm_open_backward : forall t K k u,
  lc_tm_at K k u ->
  lc_tm_at K k (open_tm_rec k u t) ->
  lc_tm_at K (S k) t.
Proof.
  induction t as [i | x | T t1 IHt1 | t1 IHt1 t2 IHt2 | t1 IHt1 | t1 IHt1 T | n | t1 IHt1 t2 IHt2 | op t1 IHt1 t2 IHt2];
  intros K k u Hu Hopen; simpl in *.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst. apply lc_tm_bvar. lia.
    + inversion Hopen; subst. apply lc_tm_bvar. lia.
  - inversion Hopen; subst. apply lc_tm_fvar.
  - inversion Hopen; subst. apply lc_tm_abs.
    + assumption.
    + apply (IHt1 K (S k) u).
      * apply lc_tm_at_mono_k with (k := k); [lia | assumption].
      * assumption.
  - inversion Hopen; subst. apply lc_tm_app.
    + apply (IHt1 K k u); assumption.
    + apply (IHt2 K k u); assumption.
  - inversion Hopen; subst. apply lc_tm_tabs.
    apply (IHt1 (S K) k u).
    + apply lc_tm_at_mono_K with (K := K); [lia | assumption].
    + assumption.
  - inversion Hopen; subst. apply lc_tm_tapp.
    + apply (IHt1 K k u); assumption.
    + assumption.
  - apply lc_tm_int.
  - inversion Hopen; subst. apply lc_tm_div.
    + apply (IHt1 K k u); assumption.
    + apply (IHt2 K k u); assumption.
  - inversion Hopen; subst. apply lc_tm_arith.
    + apply (IHt1 K k u); assumption.
    + apply (IHt2 K k u); assumption.
Qed.

Lemma lc_tm_open_forward : forall t K k u,
  lc_tm_at K (S k) t ->
  lc_tm_at K k u ->
  lc_tm_at K k (open_tm_rec k u t).
Proof.
  induction t as [i | x | T t1 IHt1 | t1 IHt1 t2 IHt2 | t1 IHt1 | t1 IHt1 T | n | t1 IHt1 t2 IHt2 | op t1 IHt1 t2 IHt2];
  intros K k u Ht Hu; simpl in *.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Hu.
    + apply Nat.eqb_neq in E. inversion Ht; subst. apply lc_tm_bvar. lia.
  - apply lc_tm_fvar.
  - inversion Ht; subst. apply lc_tm_abs.
    + assumption.
    + apply (IHt1 K (S k) u).
      * assumption.
      * apply lc_tm_at_mono_k with (k := k); [lia | assumption].
  - inversion Ht; subst. apply lc_tm_app.
    + apply (IHt1 K k u); assumption.
    + apply (IHt2 K k u); assumption.
  - inversion Ht; subst. apply lc_tm_tabs.
    apply (IHt1 (S K) k u).
    + assumption.
    + apply lc_tm_at_mono_K with (K := K); [lia | assumption].
  - inversion Ht; subst. apply lc_tm_tapp.
    + apply (IHt1 K k u); assumption.
    + assumption.
  - apply lc_tm_int.
  - inversion Ht; subst. apply lc_tm_div.
    + apply (IHt1 K k u); assumption.
    + apply (IHt2 K k u); assumption.
  - inversion Ht; subst. apply lc_tm_arith.
    + apply (IHt1 K k u); assumption.
    + apply (IHt2 K k u); assumption.
Qed.

Lemma lc_tm_ty_open_backward : forall t K k U,
  lc_ty_at K U ->
  lc_tm_at K k (open_tm_ty_rec K U t) ->
  lc_tm_at (S K) k t.
Proof.
  induction t as [i | x | T t1 IHt1 | t1 IHt1 t2 IHt2 | t1 IHt1 | t1 IHt1 T | n | t1 IHt1 t2 IHt2 | op t1 IHt1 t2 IHt2];
  intros K k U HU Hopen; simpl in *.
  - apply lc_tm_at_mono_K with (K := K); [lia | assumption].
  - inversion Hopen; subst. apply lc_tm_fvar.
  - inversion Hopen; subst. apply lc_tm_abs.
    + apply lc_ty_open_backward with (U := U); assumption.
    + apply (IHt1 K (S k) U); assumption.
  - inversion Hopen; subst. apply lc_tm_app.
    + apply (IHt1 K k U); assumption.
    + apply (IHt2 K k U); assumption.
  - inversion Hopen; subst. apply lc_tm_tabs.
    apply (IHt1 (S K) k U).
    + apply lc_ty_at_mono with (k := K); [lia | assumption].
    + assumption.
  - inversion Hopen; subst. apply lc_tm_tapp.
    + apply (IHt1 K k U); assumption.
    + apply lc_ty_open_backward with (U := U); assumption.
  - apply lc_tm_int.
  - inversion Hopen; subst. apply lc_tm_div.
    + apply (IHt1 K k U); assumption.
    + apply (IHt2 K k U); assumption.
  - inversion Hopen; subst. apply lc_tm_arith.
    + apply (IHt1 K k U); assumption.
    + apply (IHt2 K k U); assumption.
Qed.

Lemma lc_tm_ty_open_forward : forall t K k U,
  lc_tm_at (S K) k t ->
  lc_ty_at K U ->
  lc_tm_at K k (open_tm_ty_rec K U t).
Proof.
  induction t as [i | x | T t1 IHt1 | t1 IHt1 t2 IHt2 | t1 IHt1 | t1 IHt1 T | n | t1 IHt1 t2 IHt2 | op t1 IHt1 t2 IHt2];
  intros K k U Ht HU; simpl in *.
  - inversion Ht; subst. apply lc_tm_bvar. lia.
  - apply lc_tm_fvar.
  - inversion Ht; subst. apply lc_tm_abs.
    + apply lc_ty_open_forward with (k := K); assumption.
    + apply (IHt1 K (S k) U); assumption.
  - inversion Ht; subst. apply lc_tm_app.
    + apply (IHt1 K k U); assumption.
    + apply (IHt2 K k U); assumption.
  - inversion Ht; subst. apply lc_tm_tabs.
    apply (IHt1 (S K) k U).
    + assumption.
    + apply lc_ty_at_mono with (k := K); [lia | assumption].
  - inversion Ht; subst. apply lc_tm_tapp.
    + apply (IHt1 K k U); assumption.
    + apply lc_ty_open_forward with (k := K); assumption.
  - apply lc_tm_int.
  - inversion Ht; subst. apply lc_tm_div.
    + apply (IHt1 K k U); assumption.
    + apply (IHt2 K k U); assumption.
  - inversion Ht; subst. apply lc_tm_arith.
    + apply (IHt1 K k U); assumption.
    + apply (IHt2 K k U); assumption.
Qed.

(* ============================================================ *)
(* Closing preserves locally-closed                             *)
(* ============================================================ *)

Lemma lc_ty_ty_env : forall T K, lc_ty_at K T ->
  forall rho, (forall X, lc_ty_at K (rho X)) -> lc_ty_at K (ty_env rho T).
Proof.
  induction T as [i | X | T1 IH1 T2 IH2 | T1 IH1 | ];
  intros K Hlc rho Hrho; simpl in *.
  - assumption.
  - apply Hrho.
  - inversion Hlc; subst. apply lc_ty_arrow.
    + apply IH1 with (K := K); assumption.
    + apply IH2 with (K := K); assumption.
  - inversion Hlc; subst. apply lc_ty_all.
    apply IH1 with (K := S K).
    + assumption.
    + intro X. apply lc_ty_at_mono with (k := K); [lia | apply Hrho].
  - apply lc_ty_int.
Qed.

Lemma tm_env_lc : forall t K k, lc_tm_at K k t ->
  forall rho sigma,
    (forall X, lc_ty_at K (rho X)) ->
    (forall x, locally_closed_tm (sigma x)) ->
    lc_tm_at K k (tm_env rho sigma t).
Proof.
  induction t as [i | x | T t1 IHt1 | t1 IHt1 t2 IHt2 | t1 IHt1 | t1 IHt1 T | n | t1 IHt1 t2 IHt2 | op t1 IHt1 t2 IHt2];
  intros K k Hlc rho sigma Hrho Hsig; simpl in *.
  - assumption.
  - apply lc_tm_at_mono_k with (k := 0).
    + lia.
    + apply lc_tm_at_mono_K with (K := 0).
      * lia.
      * apply Hsig.
  - inversion Hlc; subst. apply lc_tm_abs.
    + apply lc_ty_ty_env with (K := K); assumption.
    + apply (IHt1 K (S k)); assumption.
  - inversion Hlc; subst. apply lc_tm_app.
    + apply (IHt1 K k); assumption.
    + apply (IHt2 K k); assumption.
  - inversion Hlc; subst. apply lc_tm_tabs. apply (IHt1 (S K) k).
    + assumption.
    + intro X. apply lc_ty_at_mono with (k := K); [lia | apply Hrho].
    + exact Hsig.
  - inversion Hlc; subst. apply lc_tm_tapp.
    + apply (IHt1 K k); assumption.
    + apply lc_ty_ty_env with (K := K); assumption.
  - apply lc_tm_int.
  - inversion Hlc; subst. apply lc_tm_div.
    + apply (IHt1 K k); assumption.
    + apply (IHt2 K k); assumption.
  - inversion Hlc; subst. apply lc_tm_arith.
    + apply (IHt1 K k); assumption.
    + apply (IHt2 K k); assumption.
Qed.

Lemma value_lc : forall v, value v -> locally_closed_tm v.
Proof.
  intros v H. induction H.
  - assumption.
  - assumption.
  - apply lc_tm_int.
Qed.

(* ============================================================ *)
(* Erasure lemmas                                               *)
(* ============================================================ *)

Lemma erase_open_rty_tm_gen : forall R k u, erase (open_rty_tm_rec k u R) = erase R.
Proof.
  induction R; intros k u; simpl.
  - reflexivity.
  - f_equal; [apply IHR1 | apply IHR2].
  - apply IHR2.
  - f_equal. apply IHR.
Qed.

Lemma erase_open_rty_tm : forall R u, erase (open_rty_tm R u) = erase R.
Proof. intros. apply erase_open_rty_tm_gen. Qed.

Lemma erase_open_rty_ty_gen : forall R k U, erase (open_rty_ty_rec k U R) = open_ty_rec k U (erase R).
Proof.
  induction R; intros k U; simpl.
  - reflexivity.
  - f_equal; [apply IHR1 | apply IHR2].
  - apply IHR2.
  - f_equal. apply IHR.
Qed.

Lemma erase_open_rty_ty : forall R U, erase (open_rty_ty R U) = open_ty (erase R) U.
Proof. intros. apply erase_open_rty_ty_gen. Qed.

Lemma erase_rty_env : forall rho sigma R, erase (rty_env rho sigma R) = ty_env rho (erase R).
Proof.
  induction R; simpl.
  - reflexivity.
  - f_equal; [apply IHR1 | apply IHR2].
  - apply IHR2.
  - f_equal. apply IHR.
Qed.

(* ============================================================ *)
(* Well-formedness implies locally-closed erasure               *)
(* ============================================================ *)

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T H.
  induction H as [Delta X Hin | Delta T1 T2 H1 IH1 H2 IH2 | L Delta T H IH | Delta].
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; assumption.
  - apply lc_ty_all.
    apply lc_ty_open_backward with (U := Ty_FVar (fresh L)) (k := 0).
    + apply lc_ty_fvar.
    + apply IH. apply fresh_not_in.
  - apply lc_ty_int.
Qed.

Lemma wf_rty_erase_lc : forall Delta RGamma R, wf_rty Delta RGamma R -> locally_closed_ty (erase R).
Proof.
  intros Delta RGamma R H.
  induction H as [L Delta RGamma T ps Hwf Hq
               | L Delta RGamma R1 R2 Hwf1 IH1 Hwf2 IH2
               | L Delta RGamma R1 R2 Hwf1 IH1 Hwf2 IH2
               | L Delta RGamma R Hwf IH].
  - simpl. apply wf_ty_lc with (Delta := Delta); exact Hwf.
  - simpl. apply lc_ty_arrow.
    + exact IH1.
    + specialize (IH2 (fresh L) (fresh_not_in L)).
      rewrite erase_open_rty_tm in IH2. exact IH2.
  - simpl. specialize (IH2 (fresh L) (fresh_not_in L)).
    rewrite erase_open_rty_tm in IH2. exact IH2.
  - simpl. apply lc_ty_all.
    specialize (IH (fresh L) (fresh_not_in L)).
    rewrite erase_open_rty_ty in IH.
    apply lc_ty_open_backward with (U := Ty_FVar (fresh L)) (k := 0).
    + apply lc_ty_fvar.
    + exact IH.
Qed.

(* ============================================================ *)
(* Syntactic locally-closed preservation for refinement typing  *)
(* ============================================================ *)

Lemma has_rtype_lc_env : forall Delta RGamma t R, has_rtype Delta RGamma t R ->
  forall rho sigma,
    (forall X, locally_closed_ty (rho X)) ->
    (forall x, locally_closed_tm (sigma x)) ->
    locally_closed_tm (tm_env rho sigma t).
Proof.
  intros Delta RGamma t R H.
  induction H as [Delta0 RGamma0 x R0 Hlk Hwf
    | L Delta0 RGamma0 R1 body R2 Hwf Hbody IHHbody
    | Delta0 RGamma0 t1 t2 R1 R2 H1 IH1 H2 IH2
    | L Delta0 RGamma0 body R0 Hbody IHHbody
    | Delta0 RGamma0 t0 R0 U H1 IH1 Hwf
    | Delta0 RGamma0 n
    | Delta0 RGamma0 t1 t2 H1 IH1 H2 IH2
    | Delta0 RGamma0 op t1 t2 H1 IH1 H2 IH2
    | Delta0 RGamma0 v T ps Htype Hval Hwf Hpc Hqh
    | Delta0 RGamma0 t0 R0 S H1 IH1 Hwf Hsub];
  intros rho sigma Hrho Hsig; simpl.
  - apply Hsig.
  - apply lc_tm_abs.
    + apply lc_ty_ty_env with (K := 0).
      * apply wf_rty_erase_lc with (Delta := Delta0) (RGamma := RGamma0). exact Hwf.
      * exact Hrho.
    + set (x := fresh (L ++ fv_tm body)).
      assert (HxL : ~ In x L) by (unfold x; apply fresh_not_in_app_l).
      assert (Hxb : ~ In x (fv_tm body)) by (unfold x; apply fresh_not_in_app_r).
      assert (Hsig' : forall y, locally_closed_tm (upd_tm x (tm_int 0%Z) sigma y)).
      { intro y. unfold upd_tm. destruct (Nat.eqb y x) eqn:E.
        - apply lc_tm_int.
        - apply Hsig. }
      specialize (IHHbody x HxL rho (upd_tm x (tm_int 0%Z) sigma) Hrho Hsig').
      rewrite (tm_env_open_tm rho (upd_tm x (tm_int 0%Z) sigma) body (tm_fvar x) Hsig') in IHHbody.
      cbn [tm_env] in IHHbody.
      rewrite upd_tm_eq in IHHbody.
      rewrite tm_env_upd_notin in IHHbody. 2: exact Hxb.
      assert (Hgoal : lc_tm_at 0 1 (tm_env rho sigma body)).
      { apply lc_tm_open_backward with (K := 0) (k := 0) (u := tm_int 0%Z).
        - apply lc_tm_int.
        - exact IHHbody. }
      exact Hgoal.
  - apply lc_tm_app.
    + apply IH1; assumption.
    + apply IH2; assumption.
  - apply lc_tm_tabs.
    set (x := fresh (L ++ ftv_tm body)).
    assert (HxL : ~ In x L) by (unfold x; apply fresh_not_in_app_l).
    assert (Hxb : ~ In x (ftv_tm body)) by (unfold x; apply fresh_not_in_app_r).
    assert (Hrho' : forall X, locally_closed_ty (upd_ty x Ty_Int rho X)).
    { intro X. unfold upd_ty. destruct (Nat.eqb X x) eqn:E.
      - apply lc_ty_int.
      - apply Hrho. }
    specialize (IHHbody x HxL (upd_ty x Ty_Int rho) sigma Hrho' Hsig).
    rewrite (tm_env_open_tm_ty (upd_ty x Ty_Int rho) sigma body (Ty_FVar x) Hrho' Hsig) in IHHbody.
    cbn [tm_env ty_env] in IHHbody.
    rewrite upd_ty_eq in IHHbody.
    rewrite tm_env_ty_upd_notin in IHHbody. 2: exact Hxb.
    assert (Hgoal : lc_tm_at 1 0 (tm_env rho sigma body)).
    { apply lc_tm_ty_open_backward with (K := 0) (U := Ty_Int).
      - apply lc_ty_int.
      - exact IHHbody. }
    exact Hgoal.
  - apply lc_tm_tapp.
    + apply IH1; assumption.
    + apply lc_ty_ty_env with (K := 0).
      * apply wf_ty_lc with (Delta := Delta0). exact Hwf.
      * exact Hrho.
  - apply lc_tm_int.
  - apply lc_tm_div.
    + apply IH1; assumption.
    + apply IH2; assumption.
  - apply lc_tm_arith.
    + apply IH1; assumption.
    + apply IH2; assumption.
  - apply tm_env_lc with (K := 0) (k := 0).
    + apply value_lc. exact Hval.
    + exact Hrho.
    + exact Hsig.
  - apply IH1; assumption.
Qed.

End SystemFRefinementSemantics.

Module SystemFRefinementBvarSubst.
Import ListNotations SystemFRefinement SystemFRefinementLogic SystemFRefinementTyping SystemFRefinementEvaluation SystemFRefinementSemantics.

(* ============================================================ *)
(* Depth-based substitution of rty-bound de Bruijn variables.   *)
(* Environments are lists: entry i binds free variable i.       *)
(* ============================================================ *)

Fixpoint set_nth {A : Type} (k : nat) (l : list A) (x : A) {struct l} : list A :=
  match l with
  | [] => [x]
  | a :: l' => match k with 0 => x :: l' | S k' => a :: set_nth k' l' x end
  end.

Definition nth_ty_def (env : list ty) (i dflt : nat) : ty :=
  match nth_error env i with Some U => U | None => Ty_BVar dflt end.

Definition nth_tm_def (env : list tm) (i dflt : nat) : tm :=
  match nth_error env i with Some u => u | None => tm_bvar dflt end.

Fixpoint subst_ty_d (env : list ty) (d : nat) (T : ty) : ty :=
  match T with
  | Ty_BVar i => if Nat.ltb i d then Ty_BVar i else nth_ty_def env (i - d) i
  | Ty_FVar X => Ty_FVar X
  | Ty_Arrow T1 T2 => Ty_Arrow (subst_ty_d env d T1) (subst_ty_d env d T2)
  | Ty_All T1 => Ty_All (subst_ty_d env (S d) T1)
  | Ty_Int => Ty_Int
  end.

Fixpoint subst_tm_d (envT : list ty) (envM : list tm) (dM dT : nat) (t : tm) : tm :=
  match t with
  | tm_bvar i =>
      if Nat.ltb i dM then tm_bvar i else nth_tm_def envM (i - dM) i
  | tm_fvar x => tm_fvar x
  | tm_abs T t1 => tm_abs (subst_ty_d envT dT T) (subst_tm_d envT envM (S dM) dT t1)
  | tm_app t1 t2 => tm_app (subst_tm_d envT envM dM dT t1) (subst_tm_d envT envM dM dT t2)
  | tm_tabs t1 => tm_tabs (subst_tm_d envT envM dM (S dT) t1)
  | tm_tapp t1 T => tm_tapp (subst_tm_d envT envM dM dT t1) (subst_ty_d envT dT T)
  | tm_int n => tm_int n
  | tm_div t1 t2 => tm_div (subst_tm_d envT envM dM dT t1) (subst_tm_d envT envM dM dT t2)
  | tm_arith op t1 t2 =>
      tm_arith op (subst_tm_d envT envM dM dT t1) (subst_tm_d envT envM dM dT t2)
  end.

Fixpoint subst_q_d (envT : list ty) (envM : list tm) (dM dT : nat)
    (q : qualifier) : qualifier :=
  match q with
  | Pred_True => Pred_True
  | Pred_False => Pred_False
  | Pred_Eq t1 t2 =>
      Pred_Eq (subst_tm_d envT envM dM dT t1) (subst_tm_d envT envM dM dT t2)
  | Pred_Lt t1 t2 =>
      Pred_Lt (subst_tm_d envT envM dM dT t1) (subst_tm_d envT envM dM dT t2)
  | Pred_Le t1 t2 =>
      Pred_Le (subst_tm_d envT envM dM dT t1) (subst_tm_d envT envM dM dT t2)
  | Pred_And p1 p2 =>
      Pred_And (subst_q_d envT envM dM dT p1) (subst_q_d envT envM dM dT p2)
  | Pred_Or p1 p2 =>
      Pred_Or (subst_q_d envT envM dM dT p1) (subst_q_d envT envM dM dT p2)
  | Pred_Not p1 => Pred_Not (subst_q_d envT envM dM dT p1)
  end.

(* ============================================================ *)
(* Substitution does not change locally-closed objects          *)
(* ============================================================ *)

Lemma subst_ty_d_lc : forall T K, lc_ty_at K T ->
  forall env d, K <= d -> subst_ty_d env d T = T.
Proof.
  induction T as [i | X | T1 IH1 T2 IH2 | T1 IH1 | ];
  intros K Hlc env d Hle; simpl in *.
  - inversion Hlc; subst. destruct (Nat.ltb i d) eqn:E.
    + reflexivity.
    + apply Nat.ltb_ge in E. exfalso. lia.
  - reflexivity.
  - inversion Hlc; subst. f_equal.
    + apply IH1 with (K := K); assumption.
    + apply IH2 with (K := K); assumption.
  - inversion Hlc; subst. f_equal. apply IH1 with (K := S K); auto. lia.
  - reflexivity.
Qed.

Lemma subst_tm_d_lc : forall t K k, lc_tm_at K k t ->
  forall envT envM dM dT, k <= dM -> K <= dT ->
  subst_tm_d envT envM dM dT t = t.
Proof.
  induction t as [i | x | T t1 IHt1 | t1 IHt1 t2 IHt2 | t1 IHt1 | t1 IHt1 T | n | t1 IHt1 t2 IHt2 | op t1 IHt1 t2 IHt2];
  intros K k Hlc envT envM dM dT HleM HleT; simpl in *.
  - inversion Hlc; subst. destruct (Nat.ltb i dM) eqn:E; [reflexivity|].
    apply Nat.ltb_ge in E. exfalso. lia.
  - reflexivity.
  - inversion Hlc; subst. f_equal.
    + apply subst_ty_d_lc with (K := K); assumption.
    + apply IHt1 with (K := K) (k := S k); auto. lia.
  - inversion Hlc; subst. f_equal.
    + apply IHt1 with (K := K) (k := k); assumption.
    + apply IHt2 with (K := K) (k := k); assumption.
  - inversion Hlc; subst. f_equal. apply IHt1 with (K := S K) (k := k); auto. lia.
  - inversion Hlc; subst. f_equal.
    + apply IHt1 with (K := K) (k := k); assumption.
    + apply subst_ty_d_lc with (K := K); assumption.
  - reflexivity.
  - inversion Hlc; subst. f_equal.
    + apply IHt1 with (K := K) (k := k); assumption.
    + apply IHt2 with (K := K) (k := k); assumption.
  - inversion Hlc; subst. f_equal.
    + apply IHt1 with (K := K) (k := k); assumption.
    + apply IHt2 with (K := K) (k := k); assumption.
Qed.

(* ============================================================ *)
(* Basic list lemmas for set_nth                               *)
(* ============================================================ *)

Lemma length_set_nth_lt : forall (A : Type) (env : list A) (k : nat) (u : A),
  k < length env -> length (set_nth k env u) = length env.
Proof.
  intros A env. induction env as [| a l IH]; intros k u Hlt; simpl in *.
  - lia.
  - destruct k as [| k']; simpl; [reflexivity|].
    assert (Hk : k' < length l) by lia. simpl. rewrite IH; auto.
Qed.

Lemma nth_error_set_nth_same : forall (A : Type) (env : list A) (k : nat) (u : A),
  k < length env -> nth_error (set_nth k env u) k = Some u.
Proof.
  intros A env. induction env as [| a l IH]; intros k u Hlt; simpl in *.
  - lia.
  - destruct k as [| k']; simpl; [reflexivity|]. apply IH. lia.
Qed.

Lemma nth_error_set_nth_other : forall (A : Type) (env : list A) (k : nat) (u : A) (j : nat),
  j < length env -> j <> k -> nth_error (set_nth k env u) j = nth_error env j.
Proof.
  intros A env. induction env as [| a l IH]; intros k u j Hlt Hne; simpl in *.
  - lia.
  - destruct k as [| k']; destruct j as [| j']; simpl.
    + exfalso; apply Hne; reflexivity.
    + reflexivity.
    + reflexivity.
    + apply IH; [lia | intro Heq; apply Hne; lia].
Qed.

Lemma nth_error_set_nth_ge : forall (A : Type) (env : list A) (k : nat) (u : A) (j : nat),
  k < length env -> length env <= j -> nth_error (set_nth k env u) j = None.
Proof.
  intros A env k u j Hk Hge.
  apply nth_error_None.
  rewrite length_set_nth_lt by exact Hk. lia.
Qed.

Lemma nth_tm_def_set_nth_same : forall (env : list tm) (k : nat) (u : tm) (i : nat),
  k < length env -> nth_tm_def (set_nth k env u) k i = u.
Proof.
  intros. unfold nth_tm_def. rewrite nth_error_set_nth_same; auto.
Qed.

Lemma nth_tm_def_set_nth_other : forall (env : list tm) (k : nat) (u : tm) (j i : nat),
  k < length env -> j <> k ->
  nth_tm_def (set_nth k env u) j i = nth_tm_def env j i.
Proof.
  intros. unfold nth_tm_def.
  destruct (Nat.ltb j (length env)) eqn:E.
  - apply Nat.ltb_lt in E. rewrite nth_error_set_nth_other; auto.
  - apply Nat.ltb_ge in E.
    assert (H1 : nth_error (set_nth k env u) j = None)
      by (apply nth_error_set_nth_ge; auto; lia).
    assert (H2 : nth_error env j = None) by (apply nth_error_None; lia).
    rewrite H1. rewrite H2. reflexivity.
Qed.

Lemma nth_ty_def_set_nth_same : forall (env : list ty) (k : nat) (u : ty) (i : nat),
  k < length env -> nth_ty_def (set_nth k env u) k i = u.
Proof.
  intros. unfold nth_ty_def. rewrite nth_error_set_nth_same; auto.
Qed.

Lemma nth_ty_def_set_nth_other : forall (env : list ty) (k : nat) (u : ty) (j i : nat),
  k < length env -> j <> k ->
  nth_ty_def (set_nth k env u) j i = nth_ty_def env j i.
Proof.
  intros. unfold nth_ty_def.
  destruct (Nat.ltb j (length env)) eqn:E.
  - apply Nat.ltb_lt in E. rewrite nth_error_set_nth_other; auto.
  - apply Nat.ltb_ge in E.
    assert (H1 : nth_error (set_nth k env u) j = None)
      by (apply nth_error_set_nth_ge; auto; lia).
    assert (H2 : nth_error env j = None) by (apply nth_error_None; lia).
    rewrite H1. rewrite H2. reflexivity.
Qed.

Lemma subst_ty_d_bvar_lt : forall env d i, i < d ->
  subst_ty_d env d (Ty_BVar i) = Ty_BVar i.
Proof.
  intros env d i H. simpl. destruct (Nat.ltb i d) eqn:E; [reflexivity|].
  apply Nat.ltb_ge in E. exfalso. lia.
Qed.

Lemma subst_ty_d_bvar_ge : forall env d i, d <= i ->
  subst_ty_d env d (Ty_BVar i) = nth_ty_def env (i - d) i.
Proof.
  intros env d i H. simpl. destruct (Nat.ltb i d) eqn:E; [|reflexivity].
  apply Nat.ltb_lt in E. exfalso. lia.
Qed.

Lemma subst_tm_d_bvar_lt : forall envT envM dM dT i, i < dM ->
  subst_tm_d envT envM dM dT (tm_bvar i) = tm_bvar i.
Proof.
  intros envT envM dM dT i H. simpl. destruct (Nat.ltb i dM) eqn:E; [reflexivity|].
  apply Nat.ltb_ge in E. exfalso. lia.
Qed.

Lemma subst_tm_d_bvar_ge : forall envT envM dM dT i, dM <= i ->
  subst_tm_d envT envM dM dT (tm_bvar i) = nth_tm_def envM (i - dM) i.
Proof.
  intros envT envM dM dT i H. simpl. destruct (Nat.ltb i dM) eqn:E; [|reflexivity].
  apply Nat.ltb_lt in E. exfalso. lia.
Qed.

(* ============================================================ *)
(* Substitution commutes with opening                           *)
(* ============================================================ *)

Lemma subst_ty_d_open : forall T k U, locally_closed_ty U ->
  forall env d, k < length env ->
  subst_ty_d env d (open_ty_rec (k + d) U T) = subst_ty_d (set_nth k env U) d T.
Proof.
  induction T as [i | X | T1 IH1 T2 IH2 | T1 IH1 | ];
  intros k U HU env d Hlen; simpl in *.
  - destruct (Nat.ltb i d) eqn:Ed.
    + assert (Hlt : i < d) by (apply Nat.ltb_lt; exact Ed).
      assert (Hneq : (k + d =? i) = false) by (apply Nat.eqb_neq; lia).
      rewrite Hneq.
      rewrite subst_ty_d_bvar_lt by lia. reflexivity.
    + assert (Hge : d <= i) by (apply Nat.ltb_ge; exact Ed).
      destruct (Nat.eqb (k + d) i) eqn:E.
      * apply Nat.eqb_eq in E. subst i. rewrite Nat.add_sub.
        assert (HUl : subst_ty_d env d U = U)
          by (apply subst_ty_d_lc with (K := 0); auto; lia).
        rewrite HUl.
        rewrite nth_ty_def_set_nth_same by exact Hlen. reflexivity.
      * apply Nat.eqb_neq in E.
        assert (Hne : i - d <> k) by lia.
        rewrite subst_ty_d_bvar_ge by lia.
        rewrite nth_ty_def_set_nth_other; [reflexivity | exact Hlen | exact Hne].
  - reflexivity.
  - f_equal.
    + apply IH1 with (U := U); assumption.
    + apply IH2 with (U := U); assumption.
  - f_equal. rewrite <- Nat.add_succ_r.
    apply IH1 with (k := k) (U := U); assumption.
  - reflexivity.
Qed.

Lemma subst_tm_d_open_tm : forall t k u, locally_closed_tm u ->
  forall envT envM dM dT, k < length envM ->
  subst_tm_d envT envM dM dT (open_tm_rec (k + dM) u t) =
  subst_tm_d envT (set_nth k envM u) dM dT t.
Proof.
  induction t as [i | x | T t1 IHt1 | t1 IHt1 t2 IHt2 | t1 IHt1 | t1 IHt1 T | n | t1 IHt1 t2 IHt2 | op t1 IHt1 t2 IHt2];
  intros k u Hu envT envM dM dT Hlen; simpl in *.
  - destruct (Nat.ltb i dM) eqn:Ed.
    + assert (Hlt : i < dM) by (apply Nat.ltb_lt; exact Ed).
      assert (Hneq : (k + dM =? i) = false) by (apply Nat.eqb_neq; lia).
      rewrite Hneq.
      rewrite subst_tm_d_bvar_lt by lia. reflexivity.
    + assert (Hge : dM <= i) by (apply Nat.ltb_ge; exact Ed).
      destruct (Nat.eqb (k + dM) i) eqn:E.
      * apply Nat.eqb_eq in E. subst i. rewrite Nat.add_sub.
        assert (Hul : subst_tm_d envT envM dM dT u = u)
          by (apply subst_tm_d_lc with (K := 0) (k := 0); auto; lia).
        rewrite Hul.
        rewrite nth_tm_def_set_nth_same by exact Hlen. reflexivity.
      * apply Nat.eqb_neq in E.
        assert (Hne : i - dM <> k) by lia.
        rewrite subst_tm_d_bvar_ge by lia.
        rewrite nth_tm_def_set_nth_other; [reflexivity | exact Hlen | exact Hne].
  - reflexivity.
  - f_equal. rewrite <- Nat.add_succ_r.
    apply IHt1 with (k := k) (u := u); assumption.
  - f_equal.
    + apply IHt1 with (k := k) (u := u); auto.
    + apply IHt2 with (k := k) (u := u); auto.
  - f_equal. apply IHt1 with (k := k) (u := u); auto.
  - f_equal. apply IHt1 with (k := k) (u := u); auto.
  - reflexivity.
  - f_equal.
    + apply IHt1 with (k := k) (u := u); auto.
    + apply IHt2 with (k := k) (u := u); auto.
  - f_equal.
    + apply IHt1 with (k := k) (u := u); auto.
    + apply IHt2 with (k := k) (u := u); auto.
Qed.

Lemma subst_tm_d_open_tm_ty : forall t k U, locally_closed_ty U ->
  forall envT envM dM dT, k < length envT ->
  subst_tm_d envT envM dM dT (open_tm_ty_rec (k + dT) U t) =
  subst_tm_d (set_nth k envT U) envM dM dT t.
Proof.
  induction t as [i | x | T t1 IHt1 | t1 IHt1 t2 IHt2 | t1 IHt1 | t1 IHt1 T | n | t1 IHt1 t2 IHt2 | op t1 IHt1 t2 IHt2];
  intros k U HU envT envM dM dT Hlen; simpl in *.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + apply subst_ty_d_open with (k := k); auto.
    + apply IHt1 with (k := k) (U := U); auto.
  - f_equal.
    + apply IHt1 with (k := k) (U := U); auto.
    + apply IHt2 with (k := k) (U := U); auto.
  - f_equal. rewrite <- Nat.add_succ_r. apply IHt1 with (k := k) (U := U); auto.
  - f_equal.
    + apply IHt1 with (k := k) (U := U); auto.
    + apply subst_ty_d_open with (k := k); auto.
  - reflexivity.
  - f_equal.
    + apply IHt1 with (k := k) (U := U); auto.
    + apply IHt2 with (k := k) (U := U); auto.
  - f_equal.
    + apply IHt1 with (k := k) (U := U); auto.
    + apply IHt2 with (k := k) (U := U); auto.
Qed.

Lemma subst_q_d_open_tm : forall q k u, locally_closed_tm u ->
  forall envT envM dM dT, k < length envM ->
  subst_q_d envT envM dM dT (open_qualifier_tm_rec (k + dM) u q) =
  subst_q_d envT (set_nth k envM u) dM dT q.
Proof.
  induction q; intros k u Hu envT envM dM dT Hlen; simpl in *; try reflexivity.
  - f_equal; apply subst_tm_d_open_tm; assumption.
  - f_equal; apply subst_tm_d_open_tm; assumption.
  - f_equal; apply subst_tm_d_open_tm; assumption.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
Qed.

Lemma subst_q_d_open_ty : forall q k U, locally_closed_ty U ->
  forall envT envM dM dT, k < length envT ->
  subst_q_d envT envM dM dT (open_qualifier_ty_rec (k + dT) U q) =
  subst_q_d (set_nth k envT U) envM dM dT q.
Proof.
  induction q; intros k U HU envT envM dM dT Hlen; simpl in *; try reflexivity.
  - f_equal; apply subst_tm_d_open_tm_ty; assumption.
  - f_equal; apply subst_tm_d_open_tm_ty; assumption.
  - f_equal; apply subst_tm_d_open_tm_ty; assumption.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
Qed.

End SystemFRefinementBvarSubst.

Module SystemFRefinementLogicalRelation.
Import ListNotations SystemFRefinement SystemFRefinementLogic SystemFRefinementTyping SystemFRefinementEvaluation SystemFRefinementSemantics SystemFRefinementBvarSubst.

(* Core shape semantics for types *)
Definition CV (T : ty) (v : tm) : Prop :=
  match T with
  | Ty_BVar _ => True
  | Ty_FVar _ => True
  | Ty_Int => exists n : Z, v = tm_int n
  | Ty_Arrow _ _ => exists (T0 : ty) (body : tm), v = tm_abs T0 body
  | Ty_All _ => exists body : tm, v = tm_tabs body
  end.

(* ============================================================ *)
(* Operational logical relation, parameterised by environments  *)
(* for the de Bruijn variables bound by rty constructors.       *)
(* envM: term binders, envT: type binders.                      *)
(* ============================================================ *)

Fixpoint V (envT : list ty) (envM : list tm) (R : rty) (v : tm) {struct R} : Prop :=
  match R with
  | R_Refine T ps =>
      value v /\ CV (subst_ty_d envT 0 T) v /\
      qualifier_holds (open_qualifier_tm (subst_q_d envT envM 1 0 ps) v)
  | R_Func R1 R2 =>
      value v /\
      (forall w, V envT envM R1 w ->
         locally_closed_tm (tm_app v w) /\
         exists u, multi (tm_app v w) u /\ V envT (w :: envM) R2 u)
  | R_Exists R1 R2 =>
      value v /\
      exists w, (locally_closed_tm w /\ exists u, multi w u /\ V envT envM R1 u) /\
                (locally_closed_tm v /\ exists u, multi v u /\ V envT (w :: envM) R2 u)
  | R_Poly R1 =>
      value v /\
      exists body, v = tm_tabs body /\
        forall U, locally_closed_ty U ->
          locally_closed_tm (open_tm_ty body U) /\
          exists u, multi (open_tm_ty body U) u /\ V (U :: envT) envM R1 u
  end.

Definition ET (envT : list ty) (envM : list tm) (R : rty) (t : tm) : Prop :=
  locally_closed_tm t /\ exists v, multi t v /\ V envT envM R v.

Lemma V_value : forall envT envM R v, V envT envM R v -> value v.
Proof. intros envT envM R v H. destruct R; simpl in H; tauto. Qed.

Lemma ET_lc : forall envT envM R t, ET envT envM R t -> locally_closed_tm t.
Proof. intros. destruct H; assumption. Qed.

Lemma ET_multi_v : forall envT envM R t,
  ET envT envM R t -> exists v, multi t v /\ V envT envM R v.
Proof. intros. destruct H as [Hlc [v [Hm Hv]]]. exists v. auto. Qed.

Lemma V_ET : forall envT envM R v, V envT envM R v -> ET envT envM R v.
Proof.
  intros envT envM R v H.
  pose proof (V_value envT envM R v H) as Hval.
  split.
  - apply value_lc. exact Hval.
  - exists v. split; [apply multi_refl | exact H].
Qed.

Lemma ET_value : forall envT envM R v, V envT envM R v ->
  ET envT envM R v.
Proof. intros. apply V_ET. exact H. Qed.

(* ============================================================ *)
(* Environment agreement (irrelevance of unused entries)        *)
(* ============================================================ *)

Lemma subst_ty_d_agree : forall T K d, lc_ty_at (K + d) T ->
  forall env1 env2,
    (forall i, i < K -> nth_error env1 i = nth_error env2 i) ->
    subst_ty_d env1 d T = subst_ty_d env2 d T.
Proof.
  induction T as [i | X | T1 IH1 T2 IH2 | T1 IH1 | ];
  intros K d Hlc env1 env2 Hag; simpl in *.
  - destruct (Nat.ltb i d) eqn:E; [reflexivity|].
    apply Nat.ltb_ge in E.
    inversion Hlc as [k' i' Hlt | | | | ]; subst.
    unfold nth_ty_def.
    rewrite Hag; [reflexivity | lia].
  - reflexivity.
  - inversion Hlc as [| | k' T1' T2' H1 H2 | | ]; subst. f_equal.
    + apply IH1 with (K := K); auto.
    + apply IH2 with (K := K); auto.
  - inversion Hlc as [| | | k' T1' Hprem | ]; subst. f_equal.
    apply IH1 with (K := K) (d := S d).
    + rewrite Nat.add_succ_r. exact Hprem.
    + exact Hag.
  - reflexivity.
Qed.

Lemma subst_tm_d_agree : forall t K k dM dT,
  lc_tm_at (K + dT) (k + dM) t ->
  forall envT1 envT2 envM1 envM2,
    (forall i, i < K -> nth_error envT1 i = nth_error envT2 i) ->
    (forall i, i < k -> nth_error envM1 i = nth_error envM2 i) ->
    subst_tm_d envT1 envM1 dM dT t = subst_tm_d envT2 envM2 dM dT t.
Proof.
  induction t as [i | x | T t1 IHt1 | t1 IHt1 t2 IHt2 | t1 IHt1 | t1 IHt1 T | n | t1 IHt1 t2 IHt2 | op t1 IHt1 t2 IHt2];
  intros K k dM dT Hlc envT1 envT2 envM1 envM2 HagT HagM; simpl in *.
  - destruct (Nat.ltb i dM) eqn:E; [reflexivity|].
    apply Nat.ltb_ge in E.
    inversion Hlc as [K' k' i' Hlt | | | | | | | | ]; subst.
    unfold nth_tm_def.
    rewrite HagM; [reflexivity | lia].
  - reflexivity.
  - inversion Hlc as [| | K' k' T' t' Hty Hbody | | | | | | ]; subst. f_equal.
    + apply subst_ty_d_agree with (K := K); auto.
    + apply IHt1 with (K := K) (k := k) (dM := S dM); auto.
      rewrite Nat.add_succ_r. exact Hbody.
  - inversion Hlc as [| | | K' k' t1' t2' H1 H2 | | | | | ]; subst. f_equal.
    + apply IHt1 with (K := K) (k := k); auto.
    + apply IHt2 with (K := K) (k := k); auto.
  - inversion Hlc as [| | | | K' k' t' Hbody | | | | ]; subst. f_equal.
    apply IHt1 with (K := K) (k := k) (dT := S dT).
    + rewrite Nat.add_succ_r. exact Hbody.
    + exact HagT.
    + exact HagM.
  - inversion Hlc as [| | | | | K' k' t' T' H1 H2 | | | ]; subst. f_equal.
    + apply IHt1 with (K := K) (k := k); auto.
    + apply subst_ty_d_agree with (K := K); auto.
  - reflexivity.
  - inversion Hlc as [| | | | | | | K' k' t1' t2' H1 H2 | ]; subst. f_equal.
    + apply IHt1 with (K := K) (k := k); auto.
    + apply IHt2 with (K := K) (k := k); auto.
  - inversion Hlc as [| | | | | | | | K' k' op' t1' t2' H1 H2]; subst. f_equal.
    + apply IHt1 with (K := K) (k := k); auto.
    + apply IHt2 with (K := K) (k := k); auto.
Qed.

Lemma subst_q_d_agree : forall q K k dM dT,
  lc_pred_at (K + dT) (k + dM) q ->
  forall envT1 envT2 envM1 envM2,
    (forall i, i < K -> nth_error envT1 i = nth_error envT2 i) ->
    (forall i, i < k -> nth_error envM1 i = nth_error envM2 i) ->
    subst_q_d envT1 envM1 dM dT q = subst_q_d envT2 envM2 dM dT q.
Proof.
  induction q; intros K k dM dT Hlc envT1 envT2 envM1 envM2 HagT HagM;
  simpl in *; try reflexivity.
  - inversion Hlc as [| | K' k' t1' t2' H1 H2 | | | | | ]; subst. f_equal.
    + apply subst_tm_d_agree with (K := K) (k := k); assumption.
    + apply subst_tm_d_agree with (K := K) (k := k); assumption.
  - inversion Hlc as [| | | K' k' t1' t2' H1 H2 | | | | ]; subst. f_equal.
    + apply subst_tm_d_agree with (K := K) (k := k); assumption.
    + apply subst_tm_d_agree with (K := K) (k := k); assumption.
  - inversion Hlc as [| | | | K' k' t1' t2' H1 H2 | | | ]; subst. f_equal.
    + apply subst_tm_d_agree with (K := K) (k := k); assumption.
    + apply subst_tm_d_agree with (K := K) (k := k); assumption.
  - inversion Hlc as [| | | | | K' k' p1 p2 H1 H2 | | ]; subst. f_equal.
    + apply IHq1 with (K := K) (k := k); auto.
    + apply IHq2 with (K := K) (k := k); auto.
  - inversion Hlc as [| | | | | | K' k' p1 p2 H1 H2 | ]; subst. f_equal.
    + apply IHq1 with (K := K) (k := k); auto.
    + apply IHq2 with (K := K) (k := k); auto.
  - inversion Hlc as [| | | | | | | K' k' p H]; subst. f_equal.
    apply IHq with (K := K) (k := k); auto.
Qed.

Lemma agree_cons_tm : forall (w : tm) env1 env2 k,
  (forall i, i < k -> nth_error env1 i = nth_error env2 i) ->
  (forall i, i < S k -> nth_error (w :: env1) i = nth_error (w :: env2) i).
Proof.
  intros w env1 env2 k H i Hi. destruct i as [|i]; simpl.
  - reflexivity.
  - apply H. lia.
Qed.

Lemma agree_cons_ty : forall (U : ty) env1 env2 k,
  (forall i, i < k -> nth_error env1 i = nth_error env2 i) ->
  (forall i, i < S k -> nth_error (U :: env1) i = nth_error (U :: env2) i).
Proof.
  intros U env1 env2 k H i Hi. destruct i as [|i]; simpl.
  - reflexivity.
  - apply H. lia.
Qed.

Lemma V_env_agree : forall R K k, lc_rty_at K k R ->
  forall envT1 envT2 envM1 envM2 v,
    (forall i, i < K -> nth_error envT1 i = nth_error envT2 i) ->
    (forall i, i < k -> nth_error envM1 i = nth_error envM2 i) ->
    (V envT1 envM1 R v <-> V envT2 envM2 R v).
Proof.
  induction R as [T ps | R1 IH1 R2 IH2 | R1 IH1 R2 IH2 | R1 IH1];
  intros K k Hlc envT1 envT2 envM1 envM2 v HagT HagM; simpl.
  - inversion Hlc as [K' k' T' ps' Hty Hq | | | ]; subst.
    assert (H1 : subst_ty_d envT1 0 T = subst_ty_d envT2 0 T).
    { apply subst_ty_d_agree with (K := K).
      - replace (K + 0) with K by lia. exact Hty.
      - exact HagT. }
    assert (H2 : subst_q_d envT1 envM1 1 0 ps = subst_q_d envT2 envM2 1 0 ps).
    { apply subst_q_d_agree with (K := K) (k := k).
      - replace (K + 0) with K by lia.
        replace (k + 1) with (S k) by lia. exact Hq.
      - exact HagT.
      - exact HagM. }
    rewrite H1, H2. reflexivity.
  - inversion Hlc as [| K' k' R1' R2' H1 H2 | | ]; subst.
    assert (IHa : forall w, V envT1 envM1 R1 w <-> V envT2 envM2 R1 w).
    { intros w. apply IH1 with (K := K) (k := k).
      assumption. exact HagT. exact HagM. }
    assert (IHb : forall w u,
      V envT1 (w :: envM1) R2 u <-> V envT2 (w :: envM2) R2 u).
    { intros w u. apply IH2 with (K := K) (k := S k).
      assumption. exact HagT. apply agree_cons_tm. assumption. }
    split.
    + intros [Hv H]. split; [exact Hv |].
      intros w Hw. specialize (H w (proj2 (IHa w) Hw)).
      destruct H as [Hlc2 [u [Hm Hu]]]. split; [exact Hlc2 |].
      exists u. split; [exact Hm | apply (proj1 (IHb w u)); exact Hu].
    + intros [Hv H]. split; [exact Hv |].
      intros w Hw. specialize (H w (proj1 (IHa w) Hw)).
      destruct H as [Hlc2 [u [Hm Hu]]]. split; [exact Hlc2 |].
      exists u. split; [exact Hm | apply (proj2 (IHb w u)); exact Hu].
  - inversion Hlc as [| | K' k' R1' R2' H1 H2 | ]; subst.
    assert (IHa : forall w, V envT1 envM1 R1 w <-> V envT2 envM2 R1 w).
    { intros w. apply IH1 with (K := K) (k := k).
      assumption. exact HagT. exact HagM. }
    assert (IHb : forall w u,
      V envT1 (w :: envM1) R2 u <-> V envT2 (w :: envM2) R2 u).
    { intros w u. apply IH2 with (K := K) (k := S k).
      assumption. exact HagT. apply agree_cons_tm. assumption. }
    split.
    + intros [Hv [w [[Hw1 [u1 [Hm1 Hu1]]] [Hv2 [u2 [Hm2 Hu2]]]]]].
      split; [exact Hv |]. exists w. split.
      * split; [exact Hw1 |]. exists u1. split; [exact Hm1 |].
        apply (proj1 (IHa u1)); exact Hu1.
      * split; [exact Hv2 |]. exists u2. split; [exact Hm2 |].
        apply (proj1 (IHb w u2)); exact Hu2.
    + intros [Hv [w [[Hw1 [u1 [Hm1 Hu1]]] [Hv2 [u2 [Hm2 Hu2]]]]]].
      split; [exact Hv |]. exists w. split.
      * split; [exact Hw1 |]. exists u1. split; [exact Hm1 |].
        apply (proj2 (IHa u1)); exact Hu1.
      * split; [exact Hv2 |]. exists u2. split; [exact Hm2 |].
        apply (proj2 (IHb w u2)); exact Hu2.
  - inversion Hlc as [| | | K' k' R1' H1]; subst.
    assert (IHa : forall U u,
      V (U :: envT1) envM1 R1 u <-> V (U :: envT2) envM2 R1 u).
    { intros U u. apply IH1 with (K := S K) (k := k).
      assumption. apply agree_cons_ty. assumption. exact HagM. }
    split.
    + intros [Hv [body [Heq H]]]. split; [exact Hv |].
      exists body. split; [exact Heq |].
      intros U HU. specialize (H U HU).
      destruct H as [Hlc2 [u [Hm Hu]]]. split; [exact Hlc2 |].
      exists u. split; [exact Hm | apply (proj1 (IHa U u)); exact Hu].
    + intros [Hv [body [Heq H]]]. split; [exact Hv |].
      exists body. split; [exact Heq |].
      intros U HU. specialize (H U HU).
      destruct H as [Hlc2 [u [Hm Hu]]]. split; [exact Hlc2 |].
      exists u. split; [exact Hm | apply (proj2 (IHa U u)); exact Hu].
Qed.

Lemma subst_ty_d_open0 : forall T k U, locally_closed_ty U ->
  forall env, k < length env ->
  subst_ty_d env 0 (open_ty_rec k U T) = subst_ty_d (set_nth k env U) 0 T.
Proof.
  intros T k U HU env Hlen.
  pose proof (subst_ty_d_open T k U HU env 0 Hlen) as H.
  rewrite Nat.add_0_r in H. exact H.
Qed.

Lemma subst_q_d_open_ty0 : forall q k U, locally_closed_ty U ->
  forall envT envM dM, k < length envT ->
  subst_q_d envT envM dM 0 (open_qualifier_ty_rec k U q) =
  subst_q_d (set_nth k envT U) envM dM 0 q.
Proof.
  intros q k U HU envT envM dM Hlen.
  pose proof (subst_q_d_open_ty q k U HU envT envM dM 0 Hlen) as H.
  rewrite Nat.add_0_r in H. exact H.
Qed.

Lemma V_open_tm : forall R K k, lc_rty_at K k R ->
  forall j u envT envM v,
    length envT = K -> length envM = k -> j < k ->
    locally_closed_tm u ->
    (V envT envM (open_rty_tm_rec j u R) v <-> V envT (set_nth j envM u) R v).
Proof.
  intros R. induction R as [T ps | R1 IH1 R2 IH2 | R1 IH1 R2 IH2 | R1 IH1];
  intros K k Hlc j u envT envM v HlT HlM Hj Hu; simpl.
  - inversion Hlc as [K' k' T' ps' Hty Hq | | | ].
    replace (S j) with (j + 1) by lia.
    assert (Hq' : subst_q_d envT envM 1 0 (open_qualifier_tm_rec (j + 1) u ps) =
                  subst_q_d envT (set_nth j envM u) 1 0 ps).
    { apply subst_q_d_open_tm with (k := j) (dM := 1).
      - exact Hu.
      - lia. }
    rewrite Hq'. reflexivity.
  - inversion Hlc as [| K' k' R1' R2' H1 H2 | | ].
    assert (IHa : forall w, V envT envM (open_rty_tm_rec j u R1) w <->
                          V envT (set_nth j envM u) R1 w).
    { intros w. apply IH1 with (K := K) (k := k); auto. }
    assert (IHb : forall w u',
      V envT (w :: envM) (open_rty_tm_rec (S j) u R2) u' <->
      V envT (w :: set_nth j envM u) R2 u').
    { intros w u'. apply IH2 with (K := K) (k := S k).
      - assumption.
      - simpl. lia.
      - simpl. lia.
      - lia.
      - exact Hu. }
    split.
    + intros [Hv Hbody]. split; [exact Hv |].
      intros w Hw. specialize (Hbody w (proj2 (IHa w) Hw)).
      destruct Hbody as [Hlc2 [u' [Hm Hu']]]. split; [exact Hlc2 |].
      exists u'. split; [exact Hm | apply (proj1 (IHb w u')); exact Hu'].
    + intros [Hv Hbody]. split; [exact Hv |].
      intros w Hw. specialize (Hbody w (proj1 (IHa w) Hw)).
      destruct Hbody as [Hlc2 [u' [Hm Hu']]]. split; [exact Hlc2 |].
      exists u'. split; [exact Hm | apply (proj2 (IHb w u')); exact Hu'].
  - inversion Hlc as [| | K' k' R1' R2' H1 H2 | ].
    assert (IHa : forall w, V envT envM (open_rty_tm_rec j u R1) w <->
                          V envT (set_nth j envM u) R1 w).
    { intros w. apply IH1 with (K := K) (k := k); auto. }
    assert (IHb : forall w u',
      V envT (w :: envM) (open_rty_tm_rec (S j) u R2) u' <->
      V envT (w :: set_nth j envM u) R2 u').
    { intros w u'. apply IH2 with (K := K) (k := S k).
      - assumption.
      - simpl. lia.
      - simpl. lia.
      - lia.
      - exact Hu. }
    split.
    + intros [Hv [w [[Hw1 [u1 [Hm1 Hu1]]] [Hv2 [u2 [Hm2 Hu2]]]]]].
      split; [exact Hv |]. exists w. split.
      * split; [exact Hw1 |]. exists u1. split; [exact Hm1 |].
        apply (proj1 (IHa u1)); exact Hu1.
      * split; [exact Hv2 |]. exists u2. split; [exact Hm2 |].
        apply (proj1 (IHb w u2)); exact Hu2.
    + intros [Hv [w [[Hw1 [u1 [Hm1 Hu1]]] [Hv2 [u2 [Hm2 Hu2]]]]]].
      split; [exact Hv |]. exists w. split.
      * split; [exact Hw1 |]. exists u1. split; [exact Hm1 |].
        apply (proj2 (IHa u1)); exact Hu1.
      * split; [exact Hv2 |]. exists u2. split; [exact Hm2 |].
        apply (proj2 (IHb w u2)); exact Hu2.
  - inversion Hlc as [| | | K' k' R1' H1]; subst K' k' R1'.
    assert (IHa : forall U u',
      V (U :: envT) envM (open_rty_tm_rec j u R1) u' <->
      V (U :: envT) (set_nth j envM u) R1 u').
    { intros U u'. apply IH1 with (K := S K) (k := k); auto. simpl. lia. }
    split.
    + intros [Hv [body [Heq Hbody]]]. split; [exact Hv |].
      exists body; split; [exact Heq |].
      intros U HU. specialize (Hbody U HU).
      destruct Hbody as [Hlc2 [u' [Hm Hu']]]. split; [exact Hlc2 |].
      exists u'; split; [exact Hm | apply (proj1 (IHa U u')); exact Hu'].
    + intros [Hv [body [Heq Hbody]]]. split; [exact Hv |].
      exists body; split; [exact Heq |].
      intros U HU. specialize (Hbody U HU).
      destruct Hbody as [Hlc2 [u' [Hm Hu']]]. split; [exact Hlc2 |].
      exists u'; split; [exact Hm | apply (proj2 (IHa U u')); exact Hu'].
Qed.

Lemma V_open_ty : forall R K k, lc_rty_at K k R ->
  forall j U envT envM v,
    length envT = K -> length envM = k -> j < K ->
    locally_closed_ty U ->
    (V envT envM (open_rty_ty_rec j U R) v <-> V (set_nth j envT U) envM R v).
Proof.
  intros R. induction R as [T ps | R1 IH1 R2 IH2 | R1 IH1 R2 IH2 | R1 IH1];
  intros K k Hlc j U envT envM v HlT HlM Hj HU; simpl.
  - inversion Hlc as [K' k' T' ps' Hty Hq | | | ].
    assert (Hsub1 : subst_ty_d envT 0 (open_ty_rec j U T) = subst_ty_d (set_nth j envT U) 0 T).
    { apply subst_ty_d_open0.
      - exact HU.
      - lia. }
    assert (Hsub2 : subst_q_d envT envM 1 0 (open_qualifier_ty_rec j U ps) =
                 subst_q_d (set_nth j envT U) envM 1 0 ps).
    { apply subst_q_d_open_ty0.
      - exact HU.
      - lia. }
    rewrite Hsub1, Hsub2. reflexivity.
  - inversion Hlc as [| K' k' R1' R2' H1 H2 | | ].
    assert (IHa : forall w, V envT envM (open_rty_ty_rec j U R1) w <->
                          V (set_nth j envT U) envM R1 w).
    { intros w. apply IH1 with (K := K) (k := k); auto. }
    assert (IHb : forall w u',
      V envT (w :: envM) (open_rty_ty_rec j U R2) u' <->
      V (set_nth j envT U) (w :: envM) R2 u').
    { intros w u'. apply IH2 with (K := K) (k := S k); auto. simpl. lia. }
    split.
    + intros [Hv Hbody]. split; [exact Hv |].
      intros w Hw. specialize (Hbody w (proj2 (IHa w) Hw)).
      destruct Hbody as [Hlc2 [u' [Hm Hu']]]. split; [exact Hlc2 |].
      exists u'. split; [exact Hm | apply (proj1 (IHb w u')); exact Hu'].
    + intros [Hv Hbody]. split; [exact Hv |].
      intros w Hw. specialize (Hbody w (proj1 (IHa w) Hw)).
      destruct Hbody as [Hlc2 [u' [Hm Hu']]]. split; [exact Hlc2 |].
      exists u'. split; [exact Hm | apply (proj2 (IHb w u')); exact Hu'].
  - inversion Hlc as [| | K' k' R1' R2' H1 H2 | ].
    assert (IHa : forall w, V envT envM (open_rty_ty_rec j U R1) w <->
                          V (set_nth j envT U) envM R1 w).
    { intros w. apply IH1 with (K := K) (k := k); auto. }
    assert (IHb : forall w u',
      V envT (w :: envM) (open_rty_ty_rec j U R2) u' <->
      V (set_nth j envT U) (w :: envM) R2 u').
    { intros w u'. apply IH2 with (K := K) (k := S k); auto. simpl. lia. }
    split.
    + intros [Hv [w [[Hw1 [u1 [Hm1 Hu1]]] [Hv2 [u2 [Hm2 Hu2]]]]]].
      split; [exact Hv |]. exists w. split.
      * split; [exact Hw1 |]. exists u1. split; [exact Hm1 |].
        apply (proj1 (IHa u1)); exact Hu1.
      * split; [exact Hv2 |]. exists u2. split; [exact Hm2 |].
        apply (proj1 (IHb w u2)); exact Hu2.
    + intros [Hv [w [[Hw1 [u1 [Hm1 Hu1]]] [Hv2 [u2 [Hm2 Hu2]]]]]].
      split; [exact Hv |]. exists w. split.
      * split; [exact Hw1 |]. exists u1. split; [exact Hm1 |].
        apply (proj2 (IHa u1)); exact Hu1.
      * split; [exact Hv2 |]. exists u2. split; [exact Hm2 |].
        apply (proj2 (IHb w u2)); exact Hu2.
  - inversion Hlc as [| | | K' k' R1' H1]; subst K' k' R1'.
    assert (IHa : forall U' u',
      V (U' :: envT) envM (open_rty_ty_rec (S j) U R1) u' <->
      V (U' :: set_nth j envT U) envM R1 u').
    { intros U' u'. apply IH1 with (K := S K) (k := k).
      - assumption.
      - simpl. lia.
      - exact HlM.
      - lia.
      - exact HU. }
    split.
    + intros [Hv [body [Heq Hbody]]]. split; [exact Hv |].
      exists body; split; [exact Heq |].
      intros U' HU'. specialize (Hbody U' HU').
      destruct Hbody as [Hlc2 [u' [Hm Hu']]]. split; [exact Hlc2 |].
      exists u'; split; [exact Hm | apply (proj1 (IHa U' u')); exact Hu'].
    + intros [Hv [body [Heq Hbody]]]. split; [exact Hv |].
      exists body; split; [exact Heq |].
      intros U' HU'. specialize (Hbody U' HU').
      destruct Hbody as [Hlc2 [u' [Hm Hu']]]. split; [exact Hlc2 |].
      exists u'; split; [exact Hm | apply (proj2 (IHa U' u')); exact Hu'].
Qed.

(* ============================================================ *)
(* Environment well-formedness for substitution                 *)
(* ============================================================ *)

Definition envT_ok (envT : list ty) : Prop :=
  forall i U, nth_error envT i = Some U -> locally_closed_ty U.

Definition envM_ok (envM : list tm) : Prop :=
  forall i u, nth_error envM i = Some u -> locally_closed_tm u.

Lemma open_tm_rec_idem : forall t k u v, locally_closed_tm u ->
  open_tm_rec k v (open_tm_rec k u t) = open_tm_rec k u t.
Proof.
  induction t as [i | x | T t1 IHt1 | t1 IHt1 t2 IHt2 | t1 IHt1 | t1 IHt1 T | n | t1 IHt1 t2 IHt2 | op t1 IHt1 t2 IHt2];
  intros k u v Hu; simpl in *.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst i.
      apply open_tm_rec_lc_id with (K := 0) (k := 0); auto. lia.
    + cbn [open_tm_rec]. rewrite E. reflexivity.
  - reflexivity.
  - f_equal. apply IHt1. exact Hu.
  - f_equal; [apply IHt1 | apply IHt2]; exact Hu.
  - f_equal. apply IHt1. exact Hu.
  - f_equal. apply IHt1. exact Hu.
  - reflexivity.
  - f_equal; [apply IHt1 | apply IHt2]; exact Hu.
  - f_equal; [apply IHt1 | apply IHt2]; exact Hu.
Qed.

Lemma open_qualifier_tm_idem : forall q k u v, locally_closed_tm u ->
  open_qualifier_tm_rec k v (open_qualifier_tm_rec k u q) = open_qualifier_tm_rec k u q.
Proof.
  induction q; intros k u v Hu; simpl in *; try reflexivity;
  try (f_equal; apply open_tm_rec_idem; exact Hu);
  try (f_equal; auto).
Qed.

Lemma nth_tm_def_lc_or_bvar : forall envM i dflt, envM_ok envM ->
  locally_closed_tm (nth_tm_def envM i dflt) \/
  nth_tm_def envM i dflt = tm_bvar dflt.
Proof.
  intros envM i dflt Hok. unfold nth_tm_def.
  destruct (nth_error envM i) as [u|] eqn:E.
  - left. apply Hok with (i := i). exact E.
  - right. reflexivity.
Qed.

Lemma open_tm_rec_lc_entry : forall envM i dflt k v, envM_ok envM -> dflt <> k ->
  open_tm_rec k v (nth_tm_def envM i dflt) = nth_tm_def envM i dflt.
Proof.
  intros envM i dflt k v Hok Hne.
  destruct (nth_tm_def_lc_or_bvar envM i dflt Hok) as [Hlc | Hbv].
  - apply open_tm_rec_lc_id with (K := 0) (k := 0); auto. lia.
  - rewrite Hbv. simpl. destruct (Nat.eqb k dflt) eqn:E.
    + apply Nat.eqb_eq in E. exfalso. apply Hne. lia.
    + reflexivity.
Qed.

Lemma open_tm_rec_bvar_lt : forall i k u, i < k ->
  open_tm_rec k u (tm_bvar i) = tm_bvar i.
Proof.
  intros. simpl. destruct (Nat.eqb k i) eqn:E.
  - apply Nat.eqb_eq in E. exfalso. lia.
  - reflexivity.
Qed.

Lemma open_tm_rec_bvar_eq : forall k u, open_tm_rec k u (tm_bvar k) = u.
Proof. intros. simpl. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma open_tm_rec_bvar_gt : forall i k u, k < i ->
  open_tm_rec k u (tm_bvar i) = tm_bvar i.
Proof.
  intros. simpl. destruct (Nat.eqb k i) eqn:E.
  - apply Nat.eqb_eq in E. exfalso. lia.
  - reflexivity.
Qed.

Lemma subst_tm_d_open_tm_S : forall t d u, locally_closed_tm u ->
  forall envT envM dT, envT_ok envT -> envM_ok envM ->
  subst_tm_d envT envM (S d) dT (open_tm_rec d u t) =
  open_tm_rec d u (subst_tm_d envT envM (S d) dT t).
Proof.
  induction t as [i | x | T t1 IHt1 | t1 IHt1 t2 IHt2 | t1 IHt1 | t1 IHt1 T | n | t1 IHt1 t2 IHt2 | op t1 IHt1 t2 IHt2];
  intros d u Hu envT envM dT HokT HokM; simpl in *.
  - destruct (Nat.ltb i d) eqn:Ed.
    + assert (Hlt : i < d) by (apply Nat.ltb_lt; exact Ed).
      destruct (Nat.eqb d i) eqn:E1.
      * apply Nat.eqb_eq in E1. exfalso. lia.
      * destruct (Nat.ltb i (S d)) eqn:E2.
        -- rewrite subst_tm_d_bvar_lt by lia.
           rewrite open_tm_rec_bvar_lt by lia. reflexivity.
        -- apply Nat.ltb_ge in E2. exfalso. lia.
    + assert (Hge : d <= i) by (apply Nat.ltb_ge; exact Ed).
      destruct (Nat.eqb d i) eqn:E1.
      * apply Nat.eqb_eq in E1. subst i.
        destruct (Nat.ltb d (S d)) eqn:E2.
        -- rewrite open_tm_rec_bvar_eq.
           assert (Huu : subst_tm_d envT envM (S d) dT u = u)
             by (apply subst_tm_d_lc with (K := 0) (k := 0); [exact Hu | lia | lia]).
           rewrite Huu. reflexivity.
        -- apply Nat.ltb_ge in E2. exfalso. lia.
      * apply Nat.eqb_neq in E1.
        destruct (Nat.ltb i (S d)) eqn:E2.
        -- apply Nat.ltb_lt in E2. exfalso. lia.
        -- rewrite subst_tm_d_bvar_ge by lia.
           erewrite open_tm_rec_lc_entry with (envM := envM) (dflt := i) (k := d) (v := u);
             [reflexivity | exact HokM | lia].
  - reflexivity.
  - f_equal. apply IHt1 with (d := S d); auto.
  - f_equal; [apply IHt1 with (d := d) | apply IHt2 with (d := d)]; auto.
  - f_equal. apply IHt1 with (d := d) (dT := S dT); auto.
  - f_equal. apply IHt1 with (d := d); auto.
  - reflexivity.
  - f_equal; [apply IHt1 with (d := d) | apply IHt2 with (d := d)]; auto.
  - f_equal; [apply IHt1 with (d := d) | apply IHt2 with (d := d)]; auto.
Qed.

Lemma subst_q_d_open_q_S : forall q d u, locally_closed_tm u ->
  forall envT envM dT, envT_ok envT -> envM_ok envM ->
  subst_q_d envT envM (S d) dT (open_qualifier_tm_rec d u q) =
  open_qualifier_tm_rec d u (subst_q_d envT envM (S d) dT q).
Proof.
  induction q; intros d u Hu envT envM dT HokT HokM; simpl in *; try reflexivity;
  try (f_equal; apply subst_tm_d_open_tm_S; assumption);
  try (f_equal; auto).
Qed.

(* ============================================================ *)
(* Semantic soundness of entailment                             *)
(* ============================================================ *)

Definition qsem (envT : list ty) (envM : list tm) (rho : atom -> ty)
    (sigma : atom -> tm) (q : qualifier) (v : tm) : Prop :=
  qualifier_holds (open_qualifier_tm (subst_q_d envT envM 1 0 (qual_env rho sigma q)) v).

Lemma qsem_And : forall envT envM rho sigma p q v,
  qsem envT envM rho sigma (Pred_And p q) v <->
  (qsem envT envM rho sigma p v /\ qsem envT envM rho sigma q v).
Proof. intros. unfold qsem, qualifier_holds, predicate_holds, open_qualifier_tm. cbn. tauto. Qed.

Lemma qsem_Or : forall envT envM rho sigma p q v,
  qsem envT envM rho sigma (Pred_Or p q) v <->
  (qsem envT envM rho sigma p v \/ qsem envT envM rho sigma q v).
Proof. intros. unfold qsem, qualifier_holds, predicate_holds, open_qualifier_tm. cbn. tauto. Qed.

Lemma qsem_Not : forall envT envM rho sigma p v,
  qsem envT envM rho sigma (Pred_Not p) v <->
  ~ qsem envT envM rho sigma p v.
Proof. intros. unfold qsem, qualifier_holds, predicate_holds, open_qualifier_tm. cbn. tauto. Qed.

Lemma qsem_True : forall envT envM rho sigma v,
  qsem envT envM rho sigma Pred_True v.
Proof. intros. unfold qsem, qualifier_holds, predicate_holds. cbn. exact I. Qed.

Lemma qsem_False : forall envT envM rho sigma v,
  qsem envT envM rho sigma Pred_False v -> False.
Proof. intros. unfold qsem, qualifier_holds, predicate_holds in H. cbn in H. exact H. Qed.

Lemma entails_sound : forall Delta RGamma p q, entails Delta RGamma p q ->
  forall rho sigma envT envM,
    (forall x, locally_closed_tm (sigma x)) ->
    (forall x R, lookup_rcontext x RGamma = Some R ->
       V envT envM (rty_env rho sigma R) (sigma x)) ->
    envT_ok envT -> envM_ok envM ->
    forall v, qsem envT envM rho sigma p v -> qsem envT envM rho sigma q v.
Proof.
  intros Delta RGamma p q H.
  induction H as [Delta' RGamma' ps
    | Delta' RGamma' ps
    | Delta' RGamma' ps qs rs H1 IH1 H2 IH2
    | Delta' RGamma' p0 q0
    | Delta' RGamma' p0 q0
    | Delta' RGamma' ps p0 qs H1 IH1 H2 IH2
    | Delta' RGamma' p0 q0
    | Delta' RGamma' p0 q0
    | Delta' RGamma' p0 q0 r H1 IH1 H2 IH2
    | Delta' RGamma' p0 q0 H1 IH1
    | Delta' RGamma' p0
    | Delta' RGamma' x T p0 q0 Hlk
    | Delta' RGamma' q0];
  intros rho sigma envT envM Hsig Henv HokT HokM v Hv.
  - exact Hv.
  - apply qsem_True.
  - apply (IH2 rho sigma envT envM Hsig Henv HokT HokM).
    apply (IH1 rho sigma envT envM Hsig Henv HokT HokM). exact Hv.
  - apply (proj1 (qsem_And envT envM rho sigma p0 q0 v)). exact Hv.
  - apply (proj2 (qsem_And envT envM rho sigma p0 q0 v)). exact Hv.
  - apply qsem_And. split.
    + apply (IH1 rho sigma envT envM Hsig Henv HokT HokM). exact Hv.
    + apply (IH2 rho sigma envT envM Hsig Henv HokT HokM). exact Hv.
  - apply qsem_Or. left. exact Hv.
  - apply qsem_Or. right. exact Hv.
  - destruct (proj1 (qsem_Or _ _ _ _ _ _ _) Hv) as [Hv' | Hv'].
    + apply (IH1 rho sigma envT envM Hsig Henv HokT HokM). exact Hv'.
    + apply (IH2 rho sigma envT envM Hsig Henv HokT HokM). exact Hv'.
  - apply qsem_Not. intro Hq.
    apply (qsem_False envT envM rho sigma v).
    apply (IH1 rho sigma envT envM Hsig Henv HokT HokM).
    apply qsem_And. split; assumption.
  - apply (qsem_False envT envM rho sigma v).
    destruct (proj1 (qsem_And envT envM rho sigma p0 (Pred_Not p0) v) Hv) as [Hp Hnp].
    apply (proj1 (qsem_Not envT envM rho sigma p0 v)) in Hnp.
    exact (Hnp Hp).
  - (* Context rule *)
    destruct (Henv x (R_Refine T p0) Hlk) as [Hval [Hcv Hq]].
    unfold qsem.
    rewrite qual_env_open_tm.
    2: exact Hsig.
    cbn [tm_env].
    unfold open_qualifier_tm in *.
    rewrite (subst_q_d_open_q_S (qual_env rho sigma p0) 0 (sigma x) (Hsig x) envT envM 0 HokT HokM).
    rewrite open_qualifier_tm_idem.
    2: exact (Hsig x).
    exact Hq.
  - apply (qsem_False envT envM rho sigma v) in Hv. destruct Hv.
Qed.

End SystemFRefinementLogicalRelation.

Module SystemFRefinementTask.
Import ListNotations SystemFRefinement SystemFRefinementLogic SystemFRefinementTyping SystemFRefinementEvaluation SystemFRefinementSemantics SystemFRefinementLogicalRelation.

Theorem never_stuck : forall (t t' : tm) (R : rty),
  has_rtype [] empty_rcontext t R ->
  multi t t' ->
  value t' \/ exists t'' : tm, t' --> t''.
Proof.

Qed.

End SystemFRefinementTask.
