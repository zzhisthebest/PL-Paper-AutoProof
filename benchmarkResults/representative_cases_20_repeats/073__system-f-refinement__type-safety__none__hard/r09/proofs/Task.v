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

Definition safe (t : tm) : Prop := value t \/ (exists t', step t t').

Definition closed_ty (T : ty) : Prop := lc_ty_at 0 T /\ fv_ty T = [].

Fixpoint fv_qual (p : qualifier) : list atom :=
  match p with
  | Pred_True => []
  | Pred_False => []
  | Pred_Eq t1 t2 => fv_tm t1 ++ fv_tm t2
  | Pred_Lt t1 t2 => fv_tm t1 ++ fv_tm t2
  | Pred_Le t1 t2 => fv_tm t1 ++ fv_tm t2
  | Pred_And p1 p2 => fv_qual p1 ++ fv_qual p2
  | Pred_Or p1 p2 => fv_qual p1 ++ fv_qual p2
  | Pred_Not p1 => fv_qual p1
  end.

Fixpoint ftv_qual (p : qualifier) : list atom :=
  match p with
  | Pred_True => []
  | Pred_False => []
  | Pred_Eq t1 t2 => ftv_tm t1 ++ ftv_tm t2
  | Pred_Lt t1 t2 => ftv_tm t1 ++ ftv_tm t2
  | Pred_Le t1 t2 => ftv_tm t1 ++ ftv_tm t2
  | Pred_And p1 p2 => ftv_qual p1 ++ ftv_qual p2
  | Pred_Or p1 p2 => ftv_qual p1 ++ ftv_qual p2
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

Definition upd_ty (sigma : atom -> ty) (X : atom) (U : ty) : atom -> ty :=
  fun Y => if Nat.eqb X Y then U else sigma Y.

Definition upd_te (te : atom -> tm) (x : atom) (u : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then u else te y.

Fixpoint ty_fsubst (sigma : atom -> ty) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => sigma X
  | Ty_Arrow T1 T2 => Ty_Arrow (ty_fsubst sigma T1) (ty_fsubst sigma T2)
  | Ty_All T1 => Ty_All (ty_fsubst sigma T1)
  | Ty_Int => Ty_Int
  end.

Fixpoint tm_fsubst (sigma : atom -> ty) (te : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => te x
  | tm_abs T t1 => tm_abs (ty_fsubst sigma T) (tm_fsubst sigma te t1)
  | tm_app t1 t2 => tm_app (tm_fsubst sigma te t1) (tm_fsubst sigma te t2)
  | tm_tabs t1 => tm_tabs (tm_fsubst sigma te t1)
  | tm_tapp t1 T => tm_tapp (tm_fsubst sigma te t1) (ty_fsubst sigma T)
  | tm_int n => tm_int n
  | tm_div t1 t2 => tm_div (tm_fsubst sigma te t1) (tm_fsubst sigma te t2)
  | tm_arith op t1 t2 =>
      tm_arith op (tm_fsubst sigma te t1) (tm_fsubst sigma te t2)
  end.

Fixpoint qual_fsubst (sigma : atom -> ty) (te : atom -> tm) (p : qualifier) : qualifier :=
  match p with
  | Pred_True => Pred_True
  | Pred_False => Pred_False
  | Pred_Eq t1 t2 => Pred_Eq (tm_fsubst sigma te t1) (tm_fsubst sigma te t2)
  | Pred_Lt t1 t2 => Pred_Lt (tm_fsubst sigma te t1) (tm_fsubst sigma te t2)
  | Pred_Le t1 t2 => Pred_Le (tm_fsubst sigma te t1) (tm_fsubst sigma te t2)
  | Pred_And p1 p2 => Pred_And (qual_fsubst sigma te p1) (qual_fsubst sigma te p2)
  | Pred_Or p1 p2 => Pred_Or (qual_fsubst sigma te p1) (qual_fsubst sigma te p2)
  | Pred_Not p1 => Pred_Not (qual_fsubst sigma te p1)
  end.

Fixpoint rty_fsubst (sigma : atom -> ty) (te : atom -> tm) (R : rty) : rty :=
  match R with
  | R_Refine T ps => R_Refine (ty_fsubst sigma T) (qual_fsubst sigma te ps)
  | R_Func R1 R2 => R_Func (rty_fsubst sigma te R1) (rty_fsubst sigma te R2)
  | R_Exists R1 R2 => R_Exists (rty_fsubst sigma te R1) (rty_fsubst sigma te R2)
  | R_Poly R1 => R_Poly (rty_fsubst sigma te R1)
  end.

(* Monotonicity of locally-closed predicates *)
Lemma lc_ty_at_mono : forall K K', K <= K' -> forall T,
  lc_ty_at K T -> lc_ty_at K' T.
Proof.
  intros K K' HK T H. revert K' HK.
  induction H; intros K' HK; simpl.
  - apply lc_ty_bvar. lia.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; auto.
  - apply lc_ty_all. apply IHlc_ty_at. lia.
  - apply lc_ty_int.
Qed.

Lemma lc_tm_at_mono : forall K K' k k', K <= K' -> k <= k' -> forall t,
  lc_tm_at K k t -> lc_tm_at K' k' t.
Proof.
  intros K K' k k' HK Hk t H. revert K' k' HK Hk.
  induction H; intros K' k' HK Hk; simpl.
  - apply lc_tm_bvar. lia.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + apply lc_ty_at_mono with (K := K); auto.
    + apply IHlc_tm_at; lia.
  - apply lc_tm_app; auto.
  - apply lc_tm_tabs. apply IHlc_tm_at; lia.
  - apply lc_tm_tapp; auto. apply lc_ty_at_mono with (K:=K); auto.
  - apply lc_tm_int.
  - apply lc_tm_div; auto.
  - apply lc_tm_arith; auto.
Qed.

Lemma lc_ty_at_closed_any : forall T, lc_ty_at 0 T -> forall K, lc_ty_at K T.
Proof. intros T H K. apply lc_ty_at_mono with (K:=0); auto. lia. Qed.

Lemma lc_tm_at_closed_any : forall t K k, lc_tm_at 0 0 t -> lc_tm_at K k t.
Proof. intros t K k H. apply lc_tm_at_mono with (K:=0) (k:=0); auto; lia. Qed.

Lemma lc_ty_fsubst : forall sigma K T,
  (forall X, lc_ty_at 0 (sigma X)) ->
  lc_ty_at K T -> lc_ty_at K (ty_fsubst sigma T).
Proof.
  intros sigma K0 T. revert K0. induction T; intros K Hs H; simpl.
  - apply lc_ty_bvar. inversion H; subst; auto.
  - apply lc_ty_at_closed_any; auto.
  - apply lc_ty_arrow; inversion H; subst; auto.
  - apply lc_ty_all. apply (IHT (S K) Hs). inversion H; subst; auto.
  - apply lc_ty_int.
Qed.

Lemma lc_tm_fsubst : forall sigma te t,
  (forall X, lc_ty_at 0 (sigma X)) ->
  (forall x, lc_tm_at 0 0 (te x)) ->
  forall K k, lc_tm_at K k t -> lc_tm_at K k (tm_fsubst sigma te t).
Proof.
  intros sigma te t. induction t; intros Hs Ht K k H; simpl.
  - apply lc_tm_bvar. inversion H; subst; auto.
  - apply lc_tm_at_mono with (K:=0) (k:=0); [lia|lia|apply Ht].
  - inversion H; subst. apply lc_tm_abs.
    + apply lc_ty_fsubst with (K:=K); auto.
    + apply IHt; auto.
  - inversion H; subst. apply lc_tm_app; auto.
  - inversion H; subst. apply lc_tm_tabs. apply IHt; auto.
  - inversion H; subst. apply lc_tm_tapp; auto.
    apply lc_ty_fsubst with (K:=K); auto.
  - apply lc_tm_int.
  - inversion H; subst. apply lc_tm_div; auto.
  - inversion H; subst. apply lc_tm_arith; auto.
Qed.


(* A locally closed type is unaffected by opening *)
Lemma open_ty_rec_absorb : forall T K k U,
  lc_ty_at K T -> K <= k -> open_ty_rec k U T = T.
Proof.
  induction T; intros K k U H HK; inversion H; subst; simpl.
  - destruct (Nat.eqb k n) eqn:E. apply Nat.eqb_eq in E. lia. reflexivity.
  - reflexivity.
  - f_equal; [ apply (IHT1 K k U) | apply (IHT2 K k U) ]; auto.
  - f_equal. apply (IHT (S K) (S k) U); auto. lia.
  - reflexivity.
Qed.

(* A locally closed term is unaffected by term-level opening *)
Lemma open_tm_rec_absorb : forall t K k (u : tm),
  lc_tm_at K k t -> open_tm_rec k u t = t.
Proof.
  induction t; intros K k u H; inversion H; subst; simpl.
  - destruct (Nat.eqb k n) eqn:E. apply Nat.eqb_eq in E. lia. reflexivity.
  - reflexivity.
  - f_equal. apply (IHt K (S k) u). assumption.
  - f_equal; [apply (IHt1 K k u) | apply (IHt2 K k u)]; assumption.
  - f_equal. apply (IHt (S K) k u). assumption.
  - f_equal. apply (IHt K k u). assumption.
  - reflexivity.
  - f_equal; [apply (IHt1 K k u) | apply (IHt2 K k u)]; assumption.
  - f_equal; [apply (IHt1 K k u) | apply (IHt2 K k u)]; assumption.
Qed.

(* Commutation: free-variable substitution versus term opening *)
Lemma tm_fsubst_open_tm : forall sigma te
  (Ht : forall x, lc_tm_at 0 0 (te x)) k u t,
  tm_fsubst sigma te (open_tm_rec k u t) =
  open_tm_rec k (tm_fsubst sigma te u) (tm_fsubst sigma te t).
Proof.
  intros sigma te Ht k u t. revert k.
  induction t; intros k; simpl.
  - destruct (Nat.eqb k n); auto.
  - assert (E: open_tm_rec k (tm_fsubst sigma te u) (te a) = te a).
    { apply (open_tm_rec_absorb (te a) 0 k). apply lc_tm_at_closed_any. apply Ht. }
    rewrite E. reflexivity.
  - f_equal. apply IHt.
  - f_equal. apply IHt1. apply IHt2.
  - f_equal. apply IHt.
  - f_equal. apply IHt.
  - reflexivity.
  - f_equal. apply IHt1. apply IHt2.
  - f_equal. apply IHt1. apply IHt2.
Qed.

(* Commutation: type free-variable substitution versus type opening *)
Lemma ty_fsubst_open_ty : forall sigma (Hs : forall X, lc_ty_at 0 (sigma X))
  k U T,
  ty_fsubst sigma (open_ty_rec k U T) =
  open_ty_rec k (ty_fsubst sigma U) (ty_fsubst sigma T).
Proof.
  intros sigma Hs k U T. revert k.
  induction T; intros k; simpl.
  - destruct (Nat.eqb k n); auto.
  - rewrite (open_ty_rec_absorb (sigma a) 0 k (ty_fsubst sigma U)); auto. lia.
  - f_equal; auto.
  - f_equal. apply IHT.
  - reflexivity.
Qed.

Lemma open_tm_ty_rec_absorb : forall t K k kt (U : ty),
  lc_tm_at K k t -> K <= kt -> open_tm_ty_rec kt U t = t.
Proof.
  induction t; intros K k kt U H HK; inversion H; subst; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + apply open_ty_rec_absorb with (K:=K); auto.
    + apply (IHt K (S k) kt U); auto.
  - f_equal; [apply (IHt1 K k kt U) | apply (IHt2 K k kt U)]; auto.
  - f_equal. apply (IHt (S K) k (S kt) U); auto. lia.
  - f_equal.
    + apply (IHt K k kt U); auto.
    + apply open_ty_rec_absorb with (K:=K); auto.
  - reflexivity.
  - f_equal; [apply (IHt1 K k kt U) | apply (IHt2 K k kt U)]; auto.
  - f_equal; [apply (IHt1 K k kt U) | apply (IHt2 K k kt U)]; auto.
Qed.

(* Commutation: free-variable substitution versus type opening of a term *)
Lemma tm_fsubst_open_tm_ty : forall sigma te
  (Hs : forall X, lc_ty_at 0 (sigma X))
  (Ht : forall x, lc_tm_at 0 0 (te x)) k U t,
  tm_fsubst sigma te (open_tm_ty_rec k U t) =
  open_tm_ty_rec k (ty_fsubst sigma U) (tm_fsubst sigma te t).
Proof.
  intros sigma te Hs Ht k U t. revert k.
  induction t; intros k; simpl.
  - reflexivity.
  - assert (E: open_tm_ty_rec k (ty_fsubst sigma U) (te a) = te a).
    { apply (open_tm_ty_rec_absorb (te a) 0 0 k). apply Ht. lia. }
    rewrite E. reflexivity.
  - f_equal.
    + apply ty_fsubst_open_ty; auto.
    + apply IHt.
  - f_equal; auto.
  - f_equal. apply IHt.
  - f_equal; auto.
    apply ty_fsubst_open_ty; auto.
  - reflexivity.
  - f_equal; auto.
  - f_equal; auto.
Qed.

(* qualifier-level commutations *)
Lemma qual_fsubst_open_tm : forall sigma te
  (Ht : forall x, lc_tm_at 0 0 (te x)) k u p,
  qual_fsubst sigma te (open_pred_tm_rec k u p) =
  open_pred_tm_rec k (tm_fsubst sigma te u) (qual_fsubst sigma te p).
Proof.
  intros sigma te Ht k u p. revert k.
  induction p; intros k; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal; apply tm_fsubst_open_tm; auto.
  - f_equal; apply tm_fsubst_open_tm; auto.
  - f_equal; apply tm_fsubst_open_tm; auto.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
Qed.

Lemma qual_fsubst_open_ty : forall sigma te
  (Hs : forall X, lc_ty_at 0 (sigma X))
  (Ht : forall x, lc_tm_at 0 0 (te x)) k U p,
  qual_fsubst sigma te (open_pred_ty_rec k U p) =
  open_pred_ty_rec k (ty_fsubst sigma U) (qual_fsubst sigma te p).
Proof.
  intros sigma te Hs Ht k U p. revert k.
  induction p; intros k; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal; apply tm_fsubst_open_tm_ty; auto.
  - f_equal; apply tm_fsubst_open_tm_ty; auto.
  - f_equal; apply tm_fsubst_open_tm_ty; auto.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
Qed.


(* ------------------------------------------------------------------ *)
(* Basic lemmas about values, small steps, and locally closed terms    *)
(* ------------------------------------------------------------------ *)

Lemma value_lc : forall v, value v -> locally_closed_tm v.
Proof. intros v H. induction H; simpl; auto. apply lc_tm_int. Qed.

Lemma value_step_false : forall v u, value v -> step v u -> False.
Proof. intros v u Hv Hs. induction Hv; inversion Hs. Qed.

Lemma multi_value_eq : forall v u, multi v u -> value v -> u = v.
Proof.
  intros v u H. induction H; intros Hv.
  - reflexivity.
  - exfalso. eapply value_step_false; eauto.
Qed.

Lemma lc_ty_open_gen : forall T K U,
  lc_ty_at (S K) T -> lc_ty_at 0 U -> lc_ty_at K (open_ty_rec K U T).
Proof.
  induction T; intros K U H HU; inversion H; subst; simpl.
  - destruct (Nat.eqb K n) eqn:E; simpl.
    + apply Nat.eqb_eq in E; subst. apply lc_ty_at_closed_any; auto.
    + apply Nat.eqb_neq in E. apply lc_ty_bvar. lia.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; auto.
  - apply lc_ty_all. apply (IHT (S K) U); auto.
  - apply lc_ty_int.
Qed.

Lemma lc_tm_at_weaken_k : forall t K k k', k <= k' -> lc_tm_at K k t -> lc_tm_at K k' t.
Proof. intros t K k k' Hk H. eapply lc_tm_at_mono; eauto. Qed.

Lemma lc_tm_at_weaken_K : forall t K K' k, K <= K' -> lc_tm_at K k t -> lc_tm_at K' k t.
Proof. intros t K K' k HK H. eapply lc_tm_at_mono; eauto. Qed.

Lemma lc_tm_open_gen : forall t K k,
  lc_tm_at K (S k) t -> forall u, lc_tm_at K k u ->
  lc_tm_at K k (open_tm_rec k u t).
Proof.
  induction t; intros K k H u Hu; inversion H; subst; simpl.
  - destruct (Nat.eqb k n) eqn:E; simpl.
    + apply Nat.eqb_eq in E; subst; auto.
    + apply Nat.eqb_neq in E. apply lc_tm_bvar. lia.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + auto.
    + apply (IHt K (S k)); auto. apply lc_tm_at_weaken_k with (k:=k); auto; lia.
  - apply lc_tm_app; auto.
  - apply lc_tm_tabs. apply (IHt (S K) k); auto. apply lc_tm_at_weaken_K with (K:=K); auto; lia.
  - apply lc_tm_tapp; auto.
  - apply lc_tm_int.
  - apply lc_tm_div; auto.
  - apply lc_tm_arith; auto.
Qed.

Lemma lc_tm_ty_open_gen : forall t K k,
  lc_tm_at (S K) k t -> forall U, lc_ty_at 0 U ->
  lc_tm_at K k (open_tm_ty_rec K U t).
Proof.
  induction t; intros K k H U HU; inversion H; subst; simpl.
  - apply lc_tm_bvar; auto.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + apply lc_ty_open_gen with (K:=K); auto.
    + apply (IHt K (S k)); auto.
  - apply lc_tm_app; auto.
  - apply lc_tm_tabs. apply (IHt (S K) k); auto.
  - apply lc_tm_tapp; auto.
    apply lc_ty_open_gen with (K:=K); auto.
  - apply lc_tm_int.
  - apply lc_tm_div; auto.
  - apply lc_tm_arith; auto.
Qed.

Lemma lc_app_inv : forall K k t1 t2,
  lc_tm_at K k (tm_app t1 t2) -> lc_tm_at K k t1 /\ lc_tm_at K k t2.
Proof. intros K k t1 t2 H. inversion H; subst; auto. Qed.

Lemma lc_abs_inv : forall K k T t,
  lc_tm_at K k (tm_abs T t) -> lc_ty_at K T /\ lc_tm_at K (S k) t.
Proof. intros K k T t H. inversion H; subst; auto. Qed.

Lemma lc_tabs_inv : forall K k t,
  lc_tm_at K k (tm_tabs t) -> lc_tm_at (S K) k t.
Proof. intros K k t H. inversion H; subst; auto. Qed.

Lemma lc_tapp_inv : forall K k t T,
  lc_tm_at K k (tm_tapp t T) -> lc_tm_at K k t /\ lc_ty_at K T.
Proof. intros K k t T H. inversion H; subst; auto. Qed.

Lemma lc_div_inv : forall K k t1 t2,
  lc_tm_at K k (tm_div t1 t2) -> lc_tm_at K k t1 /\ lc_tm_at K k t2.
Proof. intros K k t1 t2 H. inversion H; subst; auto. Qed.

Lemma lc_arith_inv : forall K k op t1 t2,
  lc_tm_at K k (tm_arith op t1 t2) -> lc_tm_at K k t1 /\ lc_tm_at K k t2.
Proof. intros K k op t1 t2 H. inversion H; subst; auto. Qed.

Lemma step_preserves_lc : forall t u, step t u -> locally_closed_tm t -> locally_closed_tm u.
Proof.
  intros t u H. induction H; intros Hlc.
  - (* ST_AppAbs *)
    destruct (lc_app_inv 0 0 (tm_abs T t) v Hlc) as [H1 H2].
    destruct (lc_abs_inv 0 0 T t H1) as [HT Ht].
    apply lc_tm_open_gen with (K:=0) (k:=0); auto.
  - (* ST_App1 *)
    destruct (lc_app_inv 0 0 t1 t2 Hlc) as [H1 H2].
    apply lc_tm_app; [apply IHstep; auto | auto].
  - (* ST_App2 *)
    destruct (lc_app_inv 0 0 v1 t2 Hlc) as [H1 H2].
    apply lc_tm_app; [auto | apply IHstep; auto].
  - (* ST_TAppTabs *)
    destruct (lc_tapp_inv 0 0 (tm_tabs t) T Hlc) as [H1 H2].
    apply lc_tm_ty_open_gen with (K:=0) (k:=0).
    + apply lc_tabs_inv in H1. exact H1.
    + unfold locally_closed_ty in H0. exact H0.
  - (* ST_TApp *)
    destruct (lc_tapp_inv 0 0 t T Hlc) as [H1 H2].
    apply lc_tm_tapp; [apply IHstep; auto | auto].
  - (* ST_Div1 *)
    destruct (lc_div_inv 0 0 t1 t2 Hlc) as [H1 H2].
    apply lc_tm_div; [apply IHstep; auto | auto].
  - (* ST_Div2 *)
    destruct (lc_div_inv 0 0 v1 t2 Hlc) as [H1 H2].
    apply lc_tm_div; [auto | apply IHstep; auto].
  - (* ST_DivInt *) apply lc_tm_int.
  - (* ST_Arith1 *)
    destruct (lc_arith_inv 0 0 op t1 t2 Hlc) as [H1 H2].
    apply lc_tm_arith; [apply IHstep; auto | auto].
  - (* ST_Arith2 *)
    destruct (lc_arith_inv 0 0 op v1 t2 Hlc) as [H1 H2].
    apply lc_tm_arith; [auto | apply IHstep; auto].
  - (* ST_ArithInt *) apply lc_tm_int.
Qed.

(* ------------------------------------------------------------------ *)
(* Commutation of rty free-variable substitution and opening           *)
(* ------------------------------------------------------------------ *)

Lemma rty_fsubst_open_rty_tm : forall R sigma te,
  (forall x, lc_tm_at 0 0 (te x)) ->
  forall k u,
  rty_fsubst sigma te (open_rty_tm_rec k u R) =
  open_rty_tm_rec k (tm_fsubst sigma te u) (rty_fsubst sigma te R).
Proof.
  induction R; intros sigma te Ht k u; simpl.
  - f_equal. apply qual_fsubst_open_tm; auto.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
Qed.

Lemma rty_fsubst_open_rty_ty : forall R sigma te,
  (forall X, lc_ty_at 0 (sigma X)) ->
  (forall x, lc_tm_at 0 0 (te x)) ->
  forall k U,
  rty_fsubst sigma te (open_rty_ty_rec k U R) =
  open_rty_ty_rec k (ty_fsubst sigma U) (rty_fsubst sigma te R).
Proof.
  induction R; intros sigma te Hs Ht k U; simpl.
  - f_equal.
    + apply ty_fsubst_open_ty; auto.
    + apply qual_fsubst_open_ty; auto.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
Qed.

(* ------------------------------------------------------------------ *)
(* Freshness: substitution is insensitive to atoms not occurring       *)
(* ------------------------------------------------------------------ *)

Lemma notin_app_l : forall (x : atom) l1 l2, ~ In x (l1 ++ l2) -> ~ In x l1.
Proof. intros x l1 l2 H Hin. apply H. apply in_or_app. left; auto. Qed.
Lemma notin_app_r : forall (x : atom) l1 l2, ~ In x (l1 ++ l2) -> ~ In x l2.
Proof. intros x l1 l2 H Hin. apply H. apply in_or_app. right; auto. Qed.

Lemma ty_fsubst_upd_ty_notin : forall sigma X U T,
  ~ In X (fv_ty T) ->
  ty_fsubst (upd_ty sigma X U) T = ty_fsubst sigma T.
Proof.
  intros sigma X U T H. revert sigma X U H.
  induction T; intros sigma X U H; simpl.
  - reflexivity.
  - unfold upd_ty. destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E; subst. exfalso; apply H; simpl; auto.
    + reflexivity.
  - f_equal.
    + apply IHT1. apply notin_app_l with (l2 := fv_ty T2). auto.
    + apply IHT2. apply notin_app_r with (l1 := fv_ty T1). auto.
  - f_equal. apply IHT. auto.
  - reflexivity.
Qed.

Lemma tm_fsubst_upd_ty_notin : forall sigma te X U t,
  ~ In X (ftv_tm t) ->
  tm_fsubst (upd_ty sigma X U) te t = tm_fsubst sigma te t.
Proof.
  intros sigma te X U t H. revert sigma te X U H.
  induction t as [n | a | T body IHbody | t1 IH1 t2 IH2 | body IHbody
                 | t1 IH1 T | z | t1 IH1 t2 IH2 | op t1 IH1 t2 IH2];
    intros sigma te X U H; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + apply ty_fsubst_upd_ty_notin. apply notin_app_l with (l2 := ftv_tm body). auto.
    + apply IHbody. apply notin_app_r with (l1 := fv_ty T). auto.
  - f_equal.
    + apply IH1. apply notin_app_l with (l2 := ftv_tm t2). auto.
    + apply IH2. apply notin_app_r with (l1 := ftv_tm t1). auto.
  - f_equal. apply IHbody. auto.
  - f_equal.
    + apply IH1. apply notin_app_l with (l2 := fv_ty T). auto.
    + apply ty_fsubst_upd_ty_notin. apply notin_app_r with (l1 := ftv_tm t1). auto.
  - reflexivity.
  - f_equal.
    + apply IH1. apply notin_app_l with (l2 := ftv_tm t2). auto.
    + apply IH2. apply notin_app_r with (l1 := ftv_tm t1). auto.
  - f_equal.
    + apply IH1. apply notin_app_l with (l2 := ftv_tm t2). auto.
    + apply IH2. apply notin_app_r with (l1 := ftv_tm t1). auto.
Qed.

Lemma qual_fsubst_upd_ty_notin : forall sigma te X U p,
  ~ In X (ftv_qual p) ->
  qual_fsubst (upd_ty sigma X U) te p = qual_fsubst sigma te p.
Proof.
  intros sigma te X U p H. revert sigma te X U H.
  induction p as [ | | t1 t2 | t1 t2 | t1 t2 | p1 IH1 p2 IH2 | p1 IH1 p2 IH2 | p IH];
    intros sigma te X U H; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + apply tm_fsubst_upd_ty_notin. apply notin_app_l with (l2 := ftv_tm t2). auto.
    + apply tm_fsubst_upd_ty_notin. apply notin_app_r with (l1 := ftv_tm t1). auto.
  - f_equal.
    + apply tm_fsubst_upd_ty_notin. apply notin_app_l with (l2 := ftv_tm t2). auto.
    + apply tm_fsubst_upd_ty_notin. apply notin_app_r with (l1 := ftv_tm t1). auto.
  - f_equal.
    + apply tm_fsubst_upd_ty_notin. apply notin_app_l with (l2 := ftv_tm t2). auto.
    + apply tm_fsubst_upd_ty_notin. apply notin_app_r with (l1 := ftv_tm t1). auto.
  - f_equal.
    + apply IH1. apply notin_app_l with (l2 := ftv_qual p2). auto.
    + apply IH2. apply notin_app_r with (l1 := ftv_qual p1). auto.
  - f_equal.
    + apply IH1. apply notin_app_l with (l2 := ftv_qual p2). auto.
    + apply IH2. apply notin_app_r with (l1 := ftv_qual p1). auto.
  - f_equal. apply IH. auto.
Qed.

Lemma rty_fsubst_upd_ty_notin : forall R sigma te X U,
  ~ In X (ftv_rty R) ->
  rty_fsubst (upd_ty sigma X U) te R = rty_fsubst sigma te R.
Proof.
  induction R as [T ps | R1 IH1 R2 IH2 | R1 IH1 R2 IH2 | R IH];
    intros sigma te X U H; simpl.
  - f_equal.
    + apply ty_fsubst_upd_ty_notin. apply notin_app_l with (l2 := ftv_qual ps). auto.
    + apply qual_fsubst_upd_ty_notin. apply notin_app_r with (l1 := fv_ty T). auto.
  - f_equal.
    + apply IH1. apply notin_app_l with (l2 := ftv_rty R2). auto.
    + apply IH2. apply notin_app_r with (l1 := ftv_rty R1). auto.
  - f_equal.
    + apply IH1. apply notin_app_l with (l2 := ftv_rty R2). auto.
    + apply IH2. apply notin_app_r with (l1 := ftv_rty R1). auto.
  - f_equal. apply IH. auto.
Qed.

Lemma tm_fsubst_upd_te_notin : forall sigma te x u t,
  ~ In x (fv_tm t) ->
  tm_fsubst sigma (upd_te te x u) t = tm_fsubst sigma te t.
Proof.
  intros sigma te x u t H. revert sigma te x u H.
  induction t as [n | a | T body IHbody | t1 IH1 t2 IH2 | body IHbody
                 | t1 IH1 T | z | t1 IH1 t2 IH2 | op t1 IH1 t2 IH2];
    intros sigma te x u H; simpl.
  - reflexivity.
  - unfold upd_te. destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E; subst. exfalso; apply H; simpl; auto.
    + reflexivity.
  - f_equal. apply IHbody. auto.
  - f_equal.
    + apply IH1. apply notin_app_l with (l2 := fv_tm t2). auto.
    + apply IH2. apply notin_app_r with (l1 := fv_tm t1). auto.
  - f_equal. apply IHbody. auto.
  - f_equal. apply IH1. auto.
  - reflexivity.
  - f_equal.
    + apply IH1. apply notin_app_l with (l2 := fv_tm t2). auto.
    + apply IH2. apply notin_app_r with (l1 := fv_tm t1). auto.
  - f_equal.
    + apply IH1. apply notin_app_l with (l2 := fv_tm t2). auto.
    + apply IH2. apply notin_app_r with (l1 := fv_tm t1). auto.
Qed.

Lemma qual_fsubst_upd_te_notin : forall sigma te x u p,
  ~ In x (fv_qual p) ->
  qual_fsubst sigma (upd_te te x u) p = qual_fsubst sigma te p.
Proof.
  intros sigma te x u p H. revert sigma te x u H.
  induction p as [ | | t1 t2 | t1 t2 | t1 t2 | p1 IH1 p2 IH2 | p1 IH1 p2 IH2 | p IH];
    intros sigma te x u H; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + apply tm_fsubst_upd_te_notin. apply notin_app_l with (l2 := fv_tm t2). auto.
    + apply tm_fsubst_upd_te_notin. apply notin_app_r with (l1 := fv_tm t1). auto.
  - f_equal.
    + apply tm_fsubst_upd_te_notin. apply notin_app_l with (l2 := fv_tm t2). auto.
    + apply tm_fsubst_upd_te_notin. apply notin_app_r with (l1 := fv_tm t1). auto.
  - f_equal.
    + apply tm_fsubst_upd_te_notin. apply notin_app_l with (l2 := fv_tm t2). auto.
    + apply tm_fsubst_upd_te_notin. apply notin_app_r with (l1 := fv_tm t1). auto.
  - f_equal.
    + apply IH1. apply notin_app_l with (l2 := fv_qual p2). auto.
    + apply IH2. apply notin_app_r with (l1 := fv_qual p1). auto.
  - f_equal.
    + apply IH1. apply notin_app_l with (l2 := fv_qual p2). auto.
    + apply IH2. apply notin_app_r with (l1 := fv_qual p1). auto.
  - f_equal. apply IH. auto.
Qed.

Lemma rty_fsubst_upd_te_notin : forall R sigma te x u,
  ~ In x (fv_rty R) ->
  rty_fsubst sigma (upd_te te x u) R = rty_fsubst sigma te R.
Proof.
  induction R as [T ps | R1 IH1 R2 IH2 | R1 IH1 R2 IH2 | R IH];
    intros sigma te x u H; simpl.
  - f_equal. apply qual_fsubst_upd_te_notin. auto.
  - f_equal.
    + apply IH1. apply notin_app_l with (l2 := fv_rty R2). auto.
    + apply IH2. apply notin_app_r with (l1 := fv_rty R1). auto.
  - f_equal.
    + apply IH1. apply notin_app_l with (l2 := fv_rty R2). auto.
    + apply IH2. apply notin_app_r with (l1 := fv_rty R1). auto.
  - f_equal. apply IH. auto.
Qed.

(* ------------------------------------------------------------------ *)
(* Derived opening lemmas for the cofinite style binders               *)
(* ------------------------------------------------------------------ *)

Lemma upd_ty_same : forall sigma X U, upd_ty sigma X U X = U.
Proof. intros. unfold upd_ty. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma upd_ty_neq : forall sigma X Y U, X <> Y -> upd_ty sigma X U Y = sigma Y.
Proof.
  intros. unfold upd_ty. destruct (Nat.eqb X Y) eqn:E.
  apply Nat.eqb_eq in E; contradiction. reflexivity.
Qed.

Lemma upd_te_same : forall te x u, upd_te te x u x = u.
Proof. intros. unfold upd_te. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma upd_te_neq : forall te x y u, x <> y -> upd_te te x u y = te y.
Proof.
  intros. unfold upd_te. destruct (Nat.eqb x y) eqn:E.
  apply Nat.eqb_eq in E; contradiction. reflexivity.
Qed.

Lemma tm_fsubst_te_open : forall sigma te x u t,
  (forall y, lc_tm_at 0 0 (te y)) -> lc_tm_at 0 0 u ->
  ~ In x (fv_tm t) ->
  tm_fsubst sigma (upd_te te x u) (open_tm t (tm_fvar x)) =
  open_tm (tm_fsubst sigma te t) u.
Proof.
  intros sigma te x u t Ht Hu Hfresh. unfold open_tm.
  rewrite tm_fsubst_open_tm.
  - replace (tm_fsubst sigma (upd_te te x u) (tm_fvar x)) with u.
    + rewrite tm_fsubst_upd_te_notin; auto.
    + symmetry. simpl. apply upd_te_same.
  - intro y. destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E; subst. rewrite upd_te_same. auto.
    + apply Nat.eqb_neq in E. rewrite upd_te_neq by auto. apply Ht.
Qed.

Lemma rty_fsubst_te_open : forall sigma te x u R,
  (forall y, lc_tm_at 0 0 (te y)) -> lc_tm_at 0 0 u ->
  ~ In x (fv_rty R) ->
  rty_fsubst sigma (upd_te te x u) (open_rty_tm R (tm_fvar x)) =
  open_rty_tm (rty_fsubst sigma te R) u.
Proof.
  intros sigma te x u R Ht Hu Hfresh. unfold open_rty_tm.
  rewrite rty_fsubst_open_rty_tm.
  - replace (tm_fsubst sigma (upd_te te x u) (tm_fvar x)) with u.
    + rewrite rty_fsubst_upd_te_notin; auto.
    + symmetry. simpl. apply upd_te_same.
  - intro y. destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E; subst. rewrite upd_te_same. auto.
    + apply Nat.eqb_neq in E. rewrite upd_te_neq by auto. apply Ht.
Qed.

Lemma tm_fsubst_ty_open : forall sigma te X U t,
  (forall Y, lc_ty_at 0 (sigma Y)) ->
  (forall y, lc_tm_at 0 0 (te y)) ->
  lc_ty_at 0 U ->
  ~ In X (ftv_tm t) ->
  tm_fsubst (upd_ty sigma X U) te (open_tm_ty t (Ty_FVar X)) =
  open_tm_ty (tm_fsubst sigma te t) U.
Proof.
  intros sigma te X U t Hs Ht HU Hfresh. unfold open_tm_ty.
  rewrite tm_fsubst_open_tm_ty.
  - rewrite tm_fsubst_upd_ty_notin; auto.
    replace (ty_fsubst (upd_ty sigma X U) (Ty_FVar X)) with U.
    + reflexivity.
    + symmetry. simpl. apply upd_ty_same.
  - intro Y. destruct (Nat.eqb X Y) eqn:E.
    + apply Nat.eqb_eq in E; subst. rewrite upd_ty_same. auto.
    + apply Nat.eqb_neq in E. rewrite upd_ty_neq by auto. apply Hs.
  - apply Ht.
Qed.

Lemma rty_fsubst_ty_open : forall sigma te X U R,
  (forall Y, lc_ty_at 0 (sigma Y)) ->
  (forall y, lc_tm_at 0 0 (te y)) ->
  lc_ty_at 0 U ->
  ~ In X (ftv_rty R) ->
  rty_fsubst (upd_ty sigma X U) te (open_rty_ty R (Ty_FVar X)) =
  open_rty_ty (rty_fsubst sigma te R) U.
Proof.
  intros sigma te X U R Hs Ht HU Hfresh. unfold open_rty_ty.
  rewrite rty_fsubst_open_rty_ty.
  - rewrite rty_fsubst_upd_ty_notin; auto.
    replace (ty_fsubst (upd_ty sigma X U) (Ty_FVar X)) with U.
    + reflexivity.
    + symmetry. simpl. apply upd_ty_same.
  - intro Y. destruct (Nat.eqb X Y) eqn:E.
    + apply Nat.eqb_eq in E; subst. rewrite upd_ty_same. auto.
    + apply Nat.eqb_neq in E. rewrite upd_ty_neq by auto. apply Hs.
  - apply Ht.
Qed.


(* ------------------------------------------------------------------ *)
(* Semantic interpretation                                             *)
(* ------------------------------------------------------------------ *)

Definition tcons (u : tm) (tes : nat -> tm) : nat -> tm :=
  fun i => match i with 0 => u | S j => tes j end.

Definition tycons (U : ty) (taus : nat -> ty) : nat -> ty :=
  fun i => match i with 0 => U | S j => taus j end.

(* Instantiate the free bound type variables of a type *)
Fixpoint ty_inst (taus : nat -> ty) (d : nat) (T : ty) : ty :=
  match T with
  | Ty_BVar i => if Nat.ltb i d then Ty_BVar i else taus (i - d)
  | Ty_FVar X => Ty_FVar X
  | Ty_Arrow T1 T2 => Ty_Arrow (ty_inst taus d T1) (ty_inst taus d T2)
  | Ty_All T1 => Ty_All (ty_inst taus (S d) T1)
  | Ty_Int => Ty_Int
  end.

(* Instantiate the free bound term variables (with the distinguished
   refinement value v) and type variables of a term *)
Fixpoint tm_inst (taus : nat -> ty) (tes : nat -> tm) (v : tm)
  (dt dy : nat) (t : tm) : tm :=
  match t with
  | tm_bvar i =>
      if Nat.ltb i dt then tm_bvar i
      else match i - dt with
           | 0 => v
           | S j => tes j
           end
  | tm_fvar x => tm_fvar x
  | tm_abs T t1 =>
      tm_abs (ty_inst taus dy T) (tm_inst taus tes v (S dt) dy t1)
  | tm_app t1 t2 =>
      tm_app (tm_inst taus tes v dt dy t1) (tm_inst taus tes v dt dy t2)
  | tm_tabs t1 => tm_tabs (tm_inst taus tes v dt (S dy) t1)
  | tm_tapp t1 T =>
      tm_tapp (tm_inst taus tes v dt dy t1) (ty_inst taus dy T)
  | tm_int n => tm_int n
  | tm_div t1 t2 =>
      tm_div (tm_inst taus tes v dt dy t1) (tm_inst taus tes v dt dy t2)
  | tm_arith op t1 t2 =>
      tm_arith op (tm_inst taus tes v dt dy t1) (tm_inst taus tes v dt dy t2)
  end.

Fixpoint qual_inst (taus : nat -> ty) (tes : nat -> tm) (v : tm)
  (dt dy : nat) (p : qualifier) : qualifier :=
  match p with
  | Pred_True => Pred_True
  | Pred_False => Pred_False
  | Pred_Eq t1 t2 =>
      Pred_Eq (tm_inst taus tes v dt dy t1) (tm_inst taus tes v dt dy t2)
  | Pred_Lt t1 t2 =>
      Pred_Lt (tm_inst taus tes v dt dy t1) (tm_inst taus tes v dt dy t2)
  | Pred_Le t1 t2 =>
      Pred_Le (tm_inst taus tes v dt dy t1) (tm_inst taus tes v dt dy t2)
  | Pred_And p1 p2 =>
      Pred_And (qual_inst taus tes v dt dy p1) (qual_inst taus tes v dt dy p2)
  | Pred_Or p1 p2 =>
      Pred_Or (qual_inst taus tes v dt dy p1) (qual_inst taus tes v dt dy p2)
  | Pred_Not p1 => Pred_Not (qual_inst taus tes v dt dy p1)
  end.

Definition qinst (taus : nat -> ty) (tes : nat -> tm) (v : tm) (p : qualifier) : qualifier :=
  qual_inst taus tes v 0 0 p.

Definition vty0 (T : ty) (v : tm) : Prop :=
  match T with
  | Ty_Int => exists n : Z, v = tm_int n
  | Ty_Arrow _ _ => exists T' b, v = tm_abs T' b
  | Ty_All _ => exists b, v = tm_tabs b
  | Ty_BVar _ => True
  | Ty_FVar _ => True
  end.

Definition vty (taus : nat -> ty) (T : ty) (v : tm) : Prop :=
  match T with
  | Ty_BVar i => vty0 (taus i) v
  | _ => vty0 T v
  end.

(* ------------------------------------------------------------------ *)
(* Laws of bound-variable instantiation                               *)
(* ------------------------------------------------------------------ *)

Lemma ty_inst_closed : forall T d taus, lc_ty_at d T -> ty_inst taus d T = T.
Proof.
  induction T; intros d taus H; inversion H; subst; simpl.
  - destruct (Nat.ltb n d) eqn:E; auto. apply Nat.ltb_ge in E. lia.
  - reflexivity.
  - f_equal; auto.
  - f_equal. apply (IHT (S d) taus); auto.
  - reflexivity.
Qed.

Lemma ty_inst_env_irrel : forall T K d taus taus',
  lc_ty_at (K + d) T ->
  (forall i, i < K -> taus i = taus' i) ->
  ty_inst taus d T = ty_inst taus' d T.
Proof.
  induction T as [n | a | T1 IH1 T2 IH2 | T1 IH1 | ];
    intros K d taus taus' H Hagree; inversion H; subst; simpl.
  - destruct (Nat.ltb n d) eqn:E; auto.
    apply Nat.ltb_ge in E.
    assert (Hlt : n - d < K) by lia.
    rewrite (Hagree (n - d) Hlt). reflexivity.
  - reflexivity.
  - f_equal.
    + apply (IH1 K d taus taus'); auto.
    + apply (IH2 K d taus taus'); auto.
  - f_equal. apply (IH1 K (S d) taus taus').
    + replace (K + S d) with (S (K + d)) by lia. exact H2.
    + exact Hagree.
  - reflexivity.
Qed.

Lemma ty_inst_open_ty : forall T taus d k U,
  taus k = U -> lc_ty_at 0 U ->
  ty_inst taus d (open_ty_rec (k + d) U T) = ty_inst taus d T.
Proof.
  induction T as [n | a | T1 IH1 T2 IH2 | T1 IH1 | ];
    intros taus d k U Hk HU; simpl.
  - destruct (Nat.eqb (k + d) n) eqn:E.
    + apply Nat.eqb_eq in E; subst n. simpl.
      rewrite (ty_inst_closed U d taus).
      * rewrite (proj2 (Nat.ltb_ge (k + d) d)) by lia.
        replace (k + d - d) with k by lia. symmetry. exact Hk.
      * apply lc_ty_at_closed_any; auto.
    + reflexivity.
  - reflexivity.
  - f_equal; auto.
  - f_equal.
    replace (S (k + d)) with (k + S d) by lia.
    apply (IH1 taus (S d) k U); auto.
  - reflexivity.
Qed.

Lemma tm_inst_env_irrel : forall t K dt dy taus taus' tes v,
  lc_tm_at (K + dy) dt t ->
  (forall i, i < K -> taus i = taus' i) ->
  tm_inst taus tes v dt dy t = tm_inst taus' tes v dt dy t.
Proof.
  induction t as [n | a | T body IHbody | t1 IH1 t2 IH2 | body IHbody
                 | t1 IH1 T | z | t1 IH1 t2 IH2 | op t1 IH1 t2 IH2];
    intros K dt dy taus taus' tes v H Hagree; inversion H; subst; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + apply ty_inst_env_irrel with (K:=K) (d:=dy); assumption || exact Hagree.
    + apply (IHbody K (S dt) dy taus taus' tes v); assumption || exact Hagree.
  - f_equal.
    + apply (IH1 K dt dy taus taus' tes v); assumption || exact Hagree.
    + apply (IH2 K dt dy taus taus' tes v); assumption || exact Hagree.
  - f_equal. apply (IHbody K dt (S dy) taus taus' tes v).
    + replace (K + S dy) with (S (K + dy)) by lia. assumption.
    + exact Hagree.
  - f_equal.
    + apply (IH1 K dt dy taus taus' tes v); assumption || exact Hagree.
    + apply ty_inst_env_irrel with (K:=K) (d:=dy); assumption || exact Hagree.
  - reflexivity.
  - f_equal.
    + apply (IH1 K dt dy taus taus' tes v); assumption || exact Hagree.
    + apply (IH2 K dt dy taus taus' tes v); assumption || exact Hagree.
  - f_equal.
    + apply (IH1 K dt dy taus taus' tes v); assumption || exact Hagree.
    + apply (IH2 K dt dy taus taus' tes v); assumption || exact Hagree.
Qed.

Lemma tm_inst_open_tm_ty : forall t taus tes v dt dy k U,
  taus k = U -> lc_ty_at 0 U ->
  tm_inst taus tes v dt dy (open_tm_ty_rec (k + dy) U t) = tm_inst taus tes v dt dy t.
Proof.
  induction t as [n | a | T body IHbody | t1 IH1 t2 IH2 | body IHbody
                 | t1 IH1 T | z | t1 IH1 t2 IH2 | op t1 IH1 t2 IH2];
    intros taus tes v dt dy k U Hk HU; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + apply ty_inst_open_ty; assumption.
    + apply (IHbody taus tes v (S dt) dy k U); assumption.
  - f_equal.
    + apply (IH1 taus tes v dt dy k U); assumption.
    + apply (IH2 taus tes v dt dy k U); assumption.
  - f_equal.
    replace (S (k + dy)) with (k + S dy) by lia.
    apply (IHbody taus tes v dt (S dy) k U); assumption.
  - f_equal.
    + apply (IH1 taus tes v dt dy k U); assumption.
    + apply ty_inst_open_ty; assumption.
  - reflexivity.
  - f_equal.
    + apply (IH1 taus tes v dt dy k U); assumption.
    + apply (IH2 taus tes v dt dy k U); assumption.
  - f_equal.
    + apply (IH1 taus tes v dt dy k U); assumption.
    + apply (IH2 taus tes v dt dy k U); assumption.
Qed.

Lemma qual_inst_env_irrel : forall p K dt dy taus taus' tes v,
  lc_qualifier_at (K + dy) dt p ->
  (forall i, i < K -> taus i = taus' i) ->
  qual_inst taus tes v dt dy p = qual_inst taus' tes v dt dy p.
Proof.
  induction p as [ | | t1 t2 | t1 t2 | t1 t2 | p1 IH1 p2 IH2 | p1 IH1 p2 IH2 | p IH];
    intros K dt dy taus taus' tes v H Hagree; inversion H; subst; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal; apply tm_inst_env_irrel with (K:=K) (dy:=dy); assumption || exact Hagree.
  - f_equal; apply tm_inst_env_irrel with (K:=K) (dy:=dy); assumption || exact Hagree.
  - f_equal; apply tm_inst_env_irrel with (K:=K) (dy:=dy); assumption || exact Hagree.
  - f_equal.
    + apply (IH1 K dt dy taus taus' tes v); assumption || exact Hagree.
    + apply (IH2 K dt dy taus taus' tes v); assumption || exact Hagree.
  - f_equal.
    + apply (IH1 K dt dy taus taus' tes v); assumption || exact Hagree.
    + apply (IH2 K dt dy taus taus' tes v); assumption || exact Hagree.
  - f_equal. apply (IH K dt dy taus taus' tes v); assumption || exact Hagree.
Qed.

Lemma qual_inst_open_ty : forall p taus tes v dt dy k U,
  taus k = U -> lc_ty_at 0 U ->
  qual_inst taus tes v dt dy (open_pred_ty_rec (k + dy) U p)
  = qual_inst taus tes v dt dy p.
Proof.
  induction p as [ | | t1 t2 | t1 t2 | t1 t2 | p1 IH1 p2 IH2 | p1 IH1 p2 IH2 | p IH];
    intros taus tes v dt dy k U Hk HU; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal; apply tm_inst_open_tm_ty; assumption.
  - f_equal; apply tm_inst_open_tm_ty; assumption.
  - f_equal; apply tm_inst_open_tm_ty; assumption.
  - f_equal.
    + apply (IH1 taus tes v dt dy k U); assumption.
    + apply (IH2 taus tes v dt dy k U); assumption.
  - f_equal.
    + apply (IH1 taus tes v dt dy k U); assumption.
    + apply (IH2 taus tes v dt dy k U); assumption.
  - f_equal; apply (IH taus tes v dt dy k U); assumption.
Qed.

Lemma lc_ty_at_bvar_false : forall i, lc_ty_at 0 (Ty_BVar i) -> False.
Proof. intros i H. inversion H; subst; lia. Qed.

Lemma vty_closed_eq : forall taus U v, lc_ty_at 0 U -> (vty taus U v <-> vty0 U v).
Proof.
  intros taus U v HU. destruct U; simpl.
  - exfalso. eapply lc_ty_at_bvar_false. exact HU.
  - tauto.
  - tauto.
  - tauto.
  - tauto.
Qed.

Lemma vty_open_ty : forall taus k U T v,
  taus k = U -> lc_ty_at 0 U ->
  (vty taus (open_ty_rec k U T) v <-> vty taus T v).
Proof.
  intros taus k U T v Hk HU. destruct T; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst n. simpl.
      rewrite Hk. apply vty_closed_eq; auto.
    + reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(* Type-only locally-closed predicates (term bvariables ignored) *)
Fixpoint lc_tm_ty (K : nat) (t : tm) : Prop :=
  match t with
  | tm_bvar _ => True
  | tm_fvar _ => True
  | tm_abs T t1 => lc_ty_at K T /\ lc_tm_ty K t1
  | tm_app t1 t2 => lc_tm_ty K t1 /\ lc_tm_ty K t2
  | tm_tabs t1 => lc_tm_ty (S K) t1
  | tm_tapp t1 T => lc_tm_ty K t1 /\ lc_ty_at K T
  | tm_int _ => True
  | tm_div t1 t2 => lc_tm_ty K t1 /\ lc_tm_ty K t2
  | tm_arith _ t1 t2 => lc_tm_ty K t1 /\ lc_tm_ty K t2
  end.

Fixpoint lc_qual_ty (K : nat) (p : qualifier) : Prop :=
  match p with
  | Pred_True => True
  | Pred_False => True
  | Pred_Eq t1 t2 => lc_tm_ty K t1 /\ lc_tm_ty K t2
  | Pred_Lt t1 t2 => lc_tm_ty K t1 /\ lc_tm_ty K t2
  | Pred_Le t1 t2 => lc_tm_ty K t1 /\ lc_tm_ty K t2
  | Pred_And p1 p2 => lc_qual_ty K p1 /\ lc_qual_ty K p2
  | Pred_Or p1 p2 => lc_qual_ty K p1 /\ lc_qual_ty K p2
  | Pred_Not p1 => lc_qual_ty K p1
  end.

Lemma lc_tm_at_lc_tm_ty : forall t K k, lc_tm_at K k t -> lc_tm_ty K t.
Proof.
  induction t as [n | a | T body IHbody | t1 IH1 t2 IH2 | body IHbody
                 | t1 IH1 T | z | t1 IH1 t2 IH2 | op t1 IH1 t2 IH2];
    intros K k H; inversion H; subst; simpl.
  - exact I.
  - exact I.
  - split.
    + assumption.
    + apply (IHbody K (S k)); assumption.
  - split.
    + apply (IH1 K k); assumption.
    + apply (IH2 K k); assumption.
  - apply (IHbody (S K) k); assumption.
  - split.
    + apply (IH1 K k); assumption.
    + assumption.
  - exact I.
  - split.
    + apply (IH1 K k); assumption.
    + apply (IH2 K k); assumption.
  - split.
    + apply (IH1 K k); assumption.
    + apply (IH2 K k); assumption.
Qed.

Lemma lc_qual_at_lc_qual_ty : forall p K k, lc_qualifier_at K k p -> lc_qual_ty K p.
Proof.
  induction p as [ | | t1 t2 | t1 t2 | t1 t2 | p1 IH1 p2 IH2 | p1 IH1 p2 IH2 | p IH];
    intros K k H; inversion H; subst; simpl.
  - exact I.
  - exact I.
  - split; apply lc_tm_at_lc_tm_ty with (k:=k); assumption.
  - split; apply lc_tm_at_lc_tm_ty with (k:=k); assumption.
  - split; apply lc_tm_at_lc_tm_ty with (k:=k); assumption.
  - split.
    + apply (IH1 K k); assumption.
    + apply (IH2 K k); assumption.
  - split.
    + apply (IH1 K k); assumption.
    + apply (IH2 K k); assumption.
  - apply (IH K k); assumption.
Qed.

Lemma lc_rty_refine_qual_ty : forall K k T ps,
  lc_rty_at K k (R_Refine T ps) -> lc_qual_ty K ps.
Proof.
  intros K k T ps H. inversion H; subst.
  eapply lc_qual_at_lc_qual_ty. eauto.
Qed.

Lemma tm_inst_env_irrel_ty : forall t K dy taus taus' tes v dt,
  lc_tm_ty (K + dy) t ->
  (forall i, i < K -> taus i = taus' i) ->
  tm_inst taus tes v dt dy t = tm_inst taus' tes v dt dy t.
Proof.
  induction t as [n | a | T body IHbody | t1 IH1 t2 IH2 | body IHbody
                 | t1 IH1 T | z | t1 IH1 t2 IH2 | op t1 IH1 t2 IH2];
    intros K dy taus taus' tes v dt H Hagree; simpl in *.
  - reflexivity.
  - reflexivity.
  - destruct H as [HT Hbody]. f_equal.
    + apply ty_inst_env_irrel with (K:=K) (d:=dy); auto.
    + apply (IHbody K dy taus taus' tes v (S dt)); auto.
  - destruct H as [H1 H2]. f_equal.
    + apply (IH1 K dy taus taus' tes v dt); auto.
    + apply (IH2 K dy taus taus' tes v dt); auto.
  - f_equal. apply (IHbody K (S dy) taus taus' tes v dt).
    + replace (K + S dy) with (S (K + dy)) by lia. exact H.
    + exact Hagree.
  - destruct H as [H1 H2]. f_equal.
    + apply (IH1 K dy taus taus' tes v dt); auto.
    + apply ty_inst_env_irrel with (K:=K) (d:=dy); auto.
  - reflexivity.
  - destruct H as [H1 H2]. f_equal.
    + apply (IH1 K dy taus taus' tes v dt); auto.
    + apply (IH2 K dy taus taus' tes v dt); auto.
  - destruct H as [H1 H2]. f_equal.
    + apply (IH1 K dy taus taus' tes v dt); auto.
    + apply (IH2 K dy taus taus' tes v dt); auto.
Qed.

Lemma qual_inst_env_irrel_ty : forall p K dy taus taus' tes v dt,
  lc_qual_ty (K + dy) p ->
  (forall i, i < K -> taus i = taus' i) ->
  qual_inst taus tes v dt dy p = qual_inst taus' tes v dt dy p.
Proof.
  induction p as [ | | t1 t2 | t1 t2 | t1 t2 | p1 IH1 p2 IH2 | p1 IH1 p2 IH2 | p IH];
    intros K dy taus taus' tes v dt H Hagree; simpl in *.
  - reflexivity.
  - reflexivity.
  - destruct H as [H1 H2]. f_equal; apply tm_inst_env_irrel_ty with (K:=K) (dy:=dy); auto.
  - destruct H as [H1 H2]. f_equal; apply tm_inst_env_irrel_ty with (K:=K) (dy:=dy); auto.
  - destruct H as [H1 H2]. f_equal; apply tm_inst_env_irrel_ty with (K:=K) (dy:=dy); auto.
  - destruct H as [H1 H2]. f_equal.
    + apply (IH1 K dy taus taus' tes v dt); auto.
    + apply (IH2 K dy taus taus' tes v dt); auto.
  - destruct H as [H1 H2]. f_equal.
    + apply (IH1 K dy taus taus' tes v dt); auto.
    + apply (IH2 K dy taus taus' tes v dt); auto.
  - f_equal. apply (IH K dy taus taus' tes v dt); auto.
Qed.

Lemma qinst_env_irrel : forall p K k taus taus' tes v,
  lc_qualifier_at K k p ->
  (forall i, i < K -> taus i = taus' i) ->
  qinst taus tes v p = qinst taus' tes v p.
Proof.
  intros p K k taus taus' tes v H Hagree. unfold qinst.
  apply qual_inst_env_irrel_ty with (K:=K) (dy:=0).
  - replace (K + 0) with K by lia. eapply lc_qual_at_lc_qual_ty; eauto.
  - exact Hagree.
Qed.

Lemma vty_env_irrel : forall taus taus' K T v,
  lc_ty_at K T ->
  (forall i, i < K -> taus i = taus' i) ->
  (vty taus T v <-> vty taus' T v).
Proof.
  intros taus taus' K T v H Hagree. destruct T; simpl.
  - inversion H; subst.
    match goal with Hlt : n < K |- _ => rewrite (Hagree n Hlt); reflexivity end.
  - tauto.
  - tauto.
  - tauto.
  - tauto.
Qed.

Fixpoint sem (taus : nat -> ty) (tes : nat -> tm) (R : rty) (t : tm) : Prop :=
  match R with
  | R_Refine T ps =>
      (forall t', multi t t' -> locally_closed_tm t') /\
      (forall t', multi t t' -> safe t') /\
      (forall v, multi t v -> value v ->
         locally_closed_tm v /\ vty taus T v /\
         qualifier_holds (qinst taus tes v ps))
  | R_Func R1 R2 =>
      (forall t', multi t t' -> locally_closed_tm t') /\
      (forall t', multi t t' -> safe t') /\
      (forall v, multi t v -> value v ->
         locally_closed_tm v /\
         (exists Tb b, v = tm_abs Tb b) /\
         (forall u, value u -> sem taus tes R1 u ->
            sem taus (tcons u tes) R2 (tm_app v u)))
  | R_Exists R1 R2 =>
      (forall t', multi t t' -> locally_closed_tm t') /\
      (forall t', multi t t' -> safe t') /\
      (forall v, multi t v -> value v ->
         locally_closed_tm v /\
         exists u, value u /\ sem taus tes R1 u /\
                   sem taus (tcons u tes) R2 v)
  | R_Poly R1 =>
      (forall t', multi t t' -> locally_closed_tm t') /\
      (forall t', multi t t' -> safe t') /\
      (forall v, multi t v -> value v ->
         locally_closed_tm v /\
         (exists b, v = tm_tabs b) /\
         (forall U, closed_ty U ->
            sem (tycons U taus) tes R1 (tm_tapp v U)))
  end
with value_sem (taus : nat -> ty) (tes : nat -> tm) (R : rty) (v : tm) : Prop :=
  match R with
  | R_Refine T ps =>
      locally_closed_tm v /\ vty taus T v /\
      qualifier_holds (qinst taus tes v ps)
  | R_Func R1 R2 =>
      locally_closed_tm v /\
      (exists Tb b, v = tm_abs Tb b) /\
      (forall u, value u -> sem taus tes R1 u ->
         sem taus (tcons u tes) R2 (tm_app v u))
  | R_Exists R1 R2 =>
      locally_closed_tm v /\
      exists u, value u /\ sem taus tes R1 u /\
                sem taus (tcons u tes) R2 v
  | R_Poly R1 =>
      locally_closed_tm v /\
      (exists b, v = tm_tabs b) /\
      (forall U, closed_ty U ->
         sem (tycons U taus) tes R1 (tm_tapp v U))
  end.

Lemma sem_value_sem : forall taus tes R v, value v ->
  (sem taus tes R v <-> value_sem taus tes R v).
Proof.
  intros taus tes R v Hv. destruct R; simpl.
  - split.
    + intros [Hlc [Hsafe Hval]]. exact (Hval v (multi_refl v) Hv).
    + intros [Hlc [Hvty Hq]]. split.
      * intros t' Hm. rewrite (multi_value_eq v t' Hm Hv). auto.
      * split.
        -- intros t' Hm. rewrite (multi_value_eq v t' Hm Hv). left; auto.
        -- intros v' Hm Hv'. rewrite (multi_value_eq v v' Hm Hv). auto.
  - split.
    + intros [Hlc [Hsafe Hval]]. exact (Hval v (multi_refl v) Hv).
    + intros [Hlc [Habs Hfun]]. split.
      * intros t' Hm. rewrite (multi_value_eq v t' Hm Hv). auto.
      * split.
        -- intros t' Hm. rewrite (multi_value_eq v t' Hm Hv). left; auto.
        -- intros v' Hm Hv'. rewrite (multi_value_eq v v' Hm Hv). auto.
  - split.
    + intros [Hlc [Hsafe Hval]]. exact (Hval v (multi_refl v) Hv).
    + intros [Hlc Hex]. split.
      * intros t' Hm. rewrite (multi_value_eq v t' Hm Hv). auto.
      * split.
        -- intros t' Hm. rewrite (multi_value_eq v t' Hm Hv). left; auto.
        -- intros v' Hm Hv'. rewrite (multi_value_eq v v' Hm Hv). auto.
  - split.
    + intros [Hlc [Hsafe Hval]]. exact (Hval v (multi_refl v) Hv).
    + intros [Hlc [Htabs Hpoly]]. split.
      * intros t' Hm. rewrite (multi_value_eq v t' Hm Hv). auto.
      * split.
        -- intros t' Hm. rewrite (multi_value_eq v t' Hm Hv). left; auto.
        -- intros v' Hm Hv'. rewrite (multi_value_eq v v' Hm Hv). auto.
Qed.

Lemma sem_step : forall taus tes R t t', sem taus tes R t -> step t t' -> sem taus tes R t'.
Proof.
  intros taus tes R t t' H Hs. destruct R; simpl in *.
  - destruct H as [Hlc [Hsafe Hval]]. split.
    + intros u Hu. apply Hlc. eapply multi_step; eauto.
    + split.
      * intros u Hu. apply Hsafe. eapply multi_step; eauto.
      * intros v Hu Hv. apply Hval; auto. eapply multi_step; eauto.
  - destruct H as [Hlc [Hsafe Hval]]. split.
    + intros u Hu. apply Hlc. eapply multi_step; eauto.
    + split.
      * intros u Hu. apply Hsafe. eapply multi_step; eauto.
      * intros v Hu Hv. apply Hval; auto. eapply multi_step; eauto.
  - destruct H as [Hlc [Hsafe Hval]]. split.
    + intros u Hu. apply Hlc. eapply multi_step; eauto.
    + split.
      * intros u Hu. apply Hsafe. eapply multi_step; eauto.
      * intros v Hu Hv. apply Hval; auto. eapply multi_step; eauto.
  - destruct H as [Hlc [Hsafe Hval]]. split.
    + intros u Hu. apply Hlc. eapply multi_step; eauto.
    + split.
      * intros u Hu. apply Hsafe. eapply multi_step; eauto.
      * intros v Hu Hv. apply Hval; auto. eapply multi_step; eauto.
Qed.

Lemma step_bvar_inv : forall n u, step (tm_bvar n) u -> False.
Proof. intros; inversion H. Qed.
Lemma step_fvar_inv : forall x u, step (tm_fvar x) u -> False.
Proof. intros; inversion H. Qed.
Lemma step_abs_inv : forall T b u, step (tm_abs T b) u -> False.
Proof. intros; inversion H. Qed.
Lemma step_tabs_inv : forall b u, step (tm_tabs b) u -> False.
Proof. intros; inversion H. Qed.
Lemma step_int_inv : forall n u, step (tm_int n) u -> False.
Proof. intros; inversion H. Qed.

Ltac solve_head_contra :=
  exfalso;
  match goal with
  | Hs : step (tm_bvar ?n) ?x |- _ => exact (step_bvar_inv n x Hs)
  | Hs : step (tm_fvar ?a) ?x |- _ => exact (step_fvar_inv a x Hs)
  | Hs : step (tm_abs ?T ?b) ?x |- _ => exact (step_abs_inv T b x Hs)
  | Hs : step (tm_tabs ?b) ?x |- _ => exact (step_tabs_inv b x Hs)
  | Hs : step (tm_int ?n) ?x |- _ => exact (step_int_inv n x Hs)
  | Hv : value ?x, Hs : step ?x ?y |- _ => exact (value_step_false x y Hv Hs)
  | Hs : step ?x ?y, Hv : value ?x |- _ => exact (value_step_false x y Hv Hs)
  end.

Lemma step_det : forall t u v, step t u -> step t v -> u = v.
Proof.
  intros t u v H. revert v. induction H; intros w Hw; inversion Hw; subst;
    try reflexivity;
    try solve_head_contra;
    try (f_equal; eauto).
Qed.

Lemma multi_step_start : forall t t' u,
  step t t' -> multi t u -> multi t' u \/ u = t.
Proof.
  intros t t' u Hst Hm. destruct Hm as [t0 | t1 t2 t3 h d2].
  - right; reflexivity.
  - left. assert (Hz : t2 = t') by (eapply step_det; eauto). subst t2. exact d2.
Qed.

Lemma sem_back_step : forall taus tes R t t',
  sem taus tes R t' -> step t t' -> locally_closed_tm t -> sem taus tes R t.
Proof.
  intros taus tes R t t' Hsem Hstep Hlc.
  assert (Hnotval : ~ value t).
  { intro Hv. eapply value_step_false; eauto. }
  destruct R; simpl in *; destruct Hsem as [Hlc' [Hsafe' Hval']].
  all: split;
    [ intros u Hu; destruct (multi_step_start t t' u Hstep Hu) as [Hm | ->];
      [ apply Hlc'; exact Hm | exact Hlc ]
    | split;
      [ intros u Hu; destruct (multi_step_start t t' u Hstep Hu) as [Hm | ->];
        [ apply Hsafe'; exact Hm | right; exists t'; exact Hstep ]
      | intros v Hu Hv; destruct (multi_step_start t t' v Hstep Hu) as [Hm | ->];
        [ apply Hval'; auto | exfalso; apply Hnotval; exact Hv ] ] ].
Qed.

Lemma has_type_value_vty_fsubst : forall sigma te Delta Gamma v T,
  has_type Delta Gamma v T -> value v ->
  vty0 (ty_fsubst sigma T) (tm_fsubst sigma te v).
Proof.
  intros sigma te Delta Gamma v T Htype Hv.
  destruct v; try (inversion Hv).
  - (* tm_abs *) inversion Htype; subst. simpl. unfold vty0. eauto.
  - (* tm_tabs *) inversion Htype; subst. simpl. unfold vty0. eauto.
  - (* tm_int *) inversion Htype; subst. simpl. unfold vty0. eauto.
Qed.

Lemma qinst_open_ty : forall p taus tes v k U,
  taus k = U -> lc_ty_at 0 U ->
  qinst taus tes v (open_qualifier_ty_rec k U p) = qinst taus tes v p.
Proof.
  intros p taus tes v k U Hk HU. unfold qinst, open_qualifier_ty_rec.
  replace k with (k + 0) by lia.
  apply qual_inst_open_ty; auto.
Qed.

(* The semantic relation only depends on the entries of the type
   environment that are actually free in the refinement type. *)
Lemma lc_rty_refine_lc_ty : forall K k T ps,
  lc_rty_at K k (R_Refine T ps) -> lc_ty_at K T.
Proof. intros K k T ps H. inversion H; assumption. Qed.

Lemma lc_rty_refine_qual : forall K k T ps,
  lc_rty_at K k (R_Refine T ps) -> lc_qualifier_at K (S k) ps.
Proof. intros K k T ps H. inversion H; assumption. Qed.

Lemma lc_rty_func : forall K k R1 R2,
  lc_rty_at K k (R_Func R1 R2) -> lc_rty_at K k R1 /\ lc_rty_at K (S k) R2.
Proof. intros K k R1 R2 H. inversion H; subst; auto. Qed.

Lemma lc_rty_exists : forall K k R1 R2,
  lc_rty_at K k (R_Exists R1 R2) -> lc_rty_at K k R1 /\ lc_rty_at K (S k) R2.
Proof. intros K k R1 R2 H. inversion H; subst; auto. Qed.

Lemma lc_rty_poly : forall K k R1,
  lc_rty_at K k (R_Poly R1) -> lc_rty_at (S K) k R1.
Proof. intros K k R1 H. inversion H; assumption. Qed.

(* ------------------------------------------------------------------ *)
(* Locally-closed invariants and opening inversions                   *)
(* ------------------------------------------------------------------ *)

Lemma lc_ty_at_open_inv : forall T K U,
  lc_ty_at K (open_ty_rec K U T) -> lc_ty_at 0 U -> lc_ty_at (S K) T.
Proof.
  induction T as [n | a | T1 IH1 T2 IH2 | T1 IH1 | ];
    intros K U H HU; simpl in H.
  - destruct (Nat.eqb K n) eqn:E.
    + apply Nat.eqb_eq in E; subst n. apply lc_ty_bvar. lia.
    + inversion H; subst. apply lc_ty_bvar. lia.
  - apply lc_ty_fvar.
  - inversion H; subst. apply lc_ty_arrow.
    + eapply IH1; [eassumption | exact HU].
    + eapply IH2; [eassumption | exact HU].
  - inversion H; subst. apply lc_ty_all. eapply IH1; [eassumption | exact HU].
  - apply lc_ty_int.
Qed.

Lemma lc_tm_open_inv : forall t K k x,
  lc_tm_at K k (open_tm_rec k (tm_fvar x) t) -> lc_tm_at K (S k) t.
Proof.
  induction t as [n | a | T body IHbody | t1 IH1 t2 IH2 | body IHbody
                 | t1 IH1 T | z | t1 IH1 t2 IH2 | op t1 IH1 t2 IH2];
    intros K k x H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst n. apply lc_tm_bvar. lia.
    + inversion H; subst. apply lc_tm_bvar. lia.
  - apply lc_tm_fvar.
  - inversion H; subst. apply lc_tm_abs.
    + eassumption.
    + eapply IHbody; eassumption.
  - inversion H; subst. apply lc_tm_app.
    + eapply IH1; eassumption.
    + eapply IH2; eassumption.
  - inversion H; subst. apply lc_tm_tabs.
    eapply IHbody with (K:=S K) (k:=k). eassumption.
  - inversion H; subst. apply lc_tm_tapp.
    + eapply IH1; eassumption.
    + apply lc_ty_at_mono with (K:=K); auto. lia.
  - apply lc_tm_int.
  - inversion H; subst. apply lc_tm_div.
    + eapply IH1; eassumption.
    + eapply IH2; eassumption.
  - inversion H; subst. apply lc_tm_arith.
    + eapply IH1; eassumption.
    + eapply IH2; eassumption.
Qed.

Lemma lc_tm_ty_open_inv : forall t K k U,
  lc_tm_at K k (open_tm_ty_rec K U t) -> lc_ty_at 0 U -> lc_tm_at (S K) k t.
Proof.
  induction t as [n | a | T body IHbody | t1 IH1 t2 IH2 | body IHbody
                 | t1 IH1 T | z | t1 IH1 t2 IH2 | op t1 IH1 t2 IH2];
    intros K k U H HU; simpl in H.
  - apply lc_tm_bvar. inversion H; subst; lia.
  - apply lc_tm_fvar.
  - inversion H; subst. apply lc_tm_abs.
    + apply lc_ty_at_open_inv with (K:=K) (U:=U); auto.
    + apply (IHbody K (S k) U); auto.
  - inversion H; subst. apply lc_tm_app; auto.
  - inversion H; subst. apply lc_tm_tabs. apply (IHbody (S K) k U); auto.
  - inversion H; subst. apply lc_tm_tapp.
    + apply (IH1 K k U); auto.
    + apply lc_ty_at_open_inv with (K:=K) (U:=U); auto.
  - apply lc_tm_int.
  - inversion H; subst. apply lc_tm_div; auto.
  - inversion H; subst. apply lc_tm_arith; auto.
Qed.

Lemma lc_qual_ty_open : forall p K k U,
  lc_qualifier_at (S K) k p -> lc_ty_at 0 U ->
  lc_qualifier_at K k (open_pred_ty_rec K U p).
Proof.
  induction p as [ | | t1 t2 | t1 t2 | t1 t2 | p1 IH1 p2 IH2 | p1 IH1 p2 IH2 | p IH];
    intros K k U H HU; simpl.
  - apply LCP_True.
  - apply LCP_False.
  - inversion H; subst. apply LCP_Eq; apply lc_tm_ty_open_gen; auto.
  - inversion H; subst. apply LCP_Lt; apply lc_tm_ty_open_gen; auto.
  - inversion H; subst. apply LCP_Le; apply lc_tm_ty_open_gen; auto.
  - inversion H; subst. apply LCP_And.
    + eapply IH1; [eassumption | exact HU].
    + eapply IH2; [eassumption | exact HU].
  - inversion H; subst. apply LCP_Or.
    + eapply IH1; [eassumption | exact HU].
    + eapply IH2; [eassumption | exact HU].
  - inversion H; subst. apply LCP_Not. eapply IH; [eassumption | exact HU].
Qed.

Lemma lc_qual_ty_open_inv : forall p K k U,
  lc_qualifier_at K k (open_pred_ty_rec K U p) -> lc_ty_at 0 U ->
  lc_qualifier_at (S K) k p.
Proof.
  induction p as [ | | t1 t2 | t1 t2 | t1 t2 | p1 IH1 p2 IH2 | p1 IH1 p2 IH2 | p IH];
    intros K k U H HU; simpl in H.
  - apply LCP_True.
  - apply LCP_False.
  - inversion H; subst. apply LCP_Eq; apply lc_tm_ty_open_inv with (K:=K); auto.
  - inversion H; subst. apply LCP_Lt; apply lc_tm_ty_open_inv with (K:=K); auto.
  - inversion H; subst. apply LCP_Le; apply lc_tm_ty_open_inv with (K:=K); auto.
  - inversion H; subst. apply LCP_And.
    + eapply IH1; [eassumption | exact HU].
    + eapply IH2; [eassumption | exact HU].
  - inversion H; subst. apply LCP_Or.
    + eapply IH1; [eassumption | exact HU].
    + eapply IH2; [eassumption | exact HU].
  - inversion H; subst. apply LCP_Not. eapply IH; [eassumption | exact HU].
Qed.

Lemma lc_qual_tm_open : forall p K k x,
  lc_qualifier_at K (S k) p -> lc_qualifier_at K k (open_pred_tm_rec k (tm_fvar x) p).
Proof.
  induction p as [ | | t1 t2 | t1 t2 | t1 t2 | p1 IH1 p2 IH2 | p1 IH1 p2 IH2 | p IH];
    intros K k x H; simpl.
  - apply LCP_True.
  - apply LCP_False.
  - inversion H; subst. apply LCP_Eq; apply lc_tm_open_gen; auto.
  - inversion H; subst. apply LCP_Lt; apply lc_tm_open_gen; auto.
  - inversion H; subst. apply LCP_Le; apply lc_tm_open_gen; auto.
  - inversion H; subst. apply LCP_And.
    + eapply IH1; eassumption.
    + eapply IH2; eassumption.
  - inversion H; subst. apply LCP_Or.
    + eapply IH1; eassumption.
    + eapply IH2; eassumption.
  - inversion H; subst. apply LCP_Not. eapply IH; eassumption.
Qed.

Lemma lc_qual_tm_open_inv : forall p K k x,
  lc_qualifier_at K k (open_pred_tm_rec k (tm_fvar x) p) -> lc_qualifier_at K (S k) p.
Proof.
  induction p as [ | | t1 t2 | t1 t2 | t1 t2 | p1 IH1 p2 IH2 | p1 IH1 p2 IH2 | p IH];
    intros K k x H; simpl in H.
  - apply LCP_True.
  - apply LCP_False.
  - inversion H; subst. apply LCP_Eq; apply lc_tm_open_inv with (k:=k); auto.
  - inversion H; subst. apply LCP_Lt; apply lc_tm_open_inv with (k:=k); auto.
  - inversion H; subst. apply LCP_Le; apply lc_tm_open_inv with (k:=k); auto.
  - inversion H; subst. apply LCP_And.
    + eapply IH1; eassumption.
    + eapply IH2; eassumption.
  - inversion H; subst. apply LCP_Or.
    + eapply IH1; eassumption.
    + eapply IH2; eassumption.
  - inversion H; subst. apply LCP_Not. eapply IH; eassumption.
Qed.

Lemma lc_rty_tm_open_inv : forall R K k x,
  lc_rty_at K k (open_rty_tm_rec k (tm_fvar x) R) -> lc_rty_at K (S k) R.
Proof.
  induction R as [T ps | R1 IH1 R2 IH2 | R1 IH1 R2 IH2 | R1 IH1];
    intros K k x H; simpl in H.
  - inversion H; subst. apply LCR_Refine; auto.
    apply lc_qual_tm_open_inv with (k:=S k); auto.
  - inversion H; subst. apply LCR_Func.
    + apply IH1; auto.
    + apply (IH2 K (S k) x); auto.
  - inversion H; subst. apply LCR_Exists.
    + apply IH1; auto.
    + apply (IH2 K (S k) x); auto.
  - inversion H; subst. apply LCR_Poly. apply (IH1 (S K) k x); auto.
Qed.

Lemma lc_rty_ty_open : forall R K k U,
  lc_rty_at (S K) k R -> lc_ty_at 0 U -> lc_rty_at K k (open_rty_ty_rec K U R).
Proof.
  induction R as [T ps | R1 IH1 R2 IH2 | R1 IH1 R2 IH2 | R1 IH1];
    intros K k U H HU; simpl.
  - inversion H; subst. apply LCR_Refine.
    + apply lc_ty_open_gen; auto.
    + apply lc_qual_ty_open; auto.
  - inversion H; subst. apply LCR_Func; auto.
  - inversion H; subst. apply LCR_Exists; auto.
  - inversion H; subst. apply LCR_Poly. apply (IH1 (S K) k U); auto.
Qed.

Lemma lc_rty_ty_open_inv : forall R K k U,
  lc_rty_at K k (open_rty_ty_rec K U R) -> lc_ty_at 0 U -> lc_rty_at (S K) k R.
Proof.
  induction R as [T ps | R1 IH1 R2 IH2 | R1 IH1 R2 IH2 | R1 IH1];
    intros K k U H HU; simpl in H.
  - inversion H; subst. apply LCR_Refine.
    + apply lc_ty_at_open_inv with (K:=K) (U:=U); auto.
    + apply lc_qual_ty_open_inv with (K:=K); auto.
  - inversion H; subst. apply LCR_Func; auto.
  - inversion H; subst. apply LCR_Exists; auto.
  - inversion H; subst. apply LCR_Poly. apply (IH1 (S K) k U); auto.
Qed.

Lemma lc_rty_erase : forall R K k, lc_rty_at K k R -> lc_ty_at K (erase R).
Proof.
  induction R as [T ps | R1 IH1 R2 IH2 | R1 IH1 R2 IH2 | R1 IH1];
    intros K k H; simpl.
  - inversion H; subst; assumption.
  - inversion H; subst. apply lc_ty_arrow; auto.
  - inversion H; subst; auto.
  - inversion H; subst. apply lc_ty_all. apply (IH1 (S K) k); auto.
Qed.

Lemma sem_env_irrel_and : forall R K k taus taus' tes,
  lc_rty_at K k R ->
  (forall i, i < K -> taus i = taus' i) ->
  (forall t, sem taus tes R t <-> sem taus' tes R t) /\
  (forall v, value_sem taus tes R v <-> value_sem taus' tes R v).
Proof.
  induction R as [T ps | R1 IH1 R2 IH2 | R1 IH1 R2 IH2 | R1 IH1];
    intros K k taus taus' tes Hlc Hagree; simpl.
  - pose proof (lc_rty_refine_lc_ty K k T ps Hlc) as Hty.
    pose proof (lc_rty_refine_qual K k T ps Hlc) as Hqual.
    assert (HVS : forall v,
      value_sem taus tes (R_Refine T ps) v <->
      value_sem taus' tes (R_Refine T ps) v).
    { intro v. simpl. split.
      - intros [A [B C]]. split; [exact A | split].
        + apply (proj1 (vty_env_irrel taus taus' K T v Hty Hagree)); exact B.
        + rewrite <- (qinst_env_irrel ps K (S k) taus taus' tes v Hqual Hagree). exact C.
      - intros [A [B C]]. split; [exact A | split].
        + apply (proj2 (vty_env_irrel taus taus' K T v Hty Hagree)); exact B.
        + rewrite (qinst_env_irrel ps K (S k) taus taus' tes v Hqual Hagree). exact C. }
    split.
    + intro t. split.
      * intros [A [B C]]. split; [exact A | split; [exact B | idtac]].
        intros v Hm Hv. apply (proj1 (HVS v)). apply C; auto.
      * intros [A [B C]]. split; [exact A | split; [exact B | idtac]].
        intros v Hm Hv. apply (proj2 (HVS v)). apply C; auto.
    + exact HVS.
  - destruct (lc_rty_func K k R1 R2 Hlc) as [H1 H2].
    assert (HVS : forall v,
      value_sem taus tes (R_Func R1 R2) v <->
      value_sem taus' tes (R_Func R1 R2) v).
    { intro v. simpl. split.
      - intros [A [Ab F]]. split; [exact A | split; [exact Ab | idtac]].
        intros u0 Hu0 Hu1.
        apply (proj1 ((proj1 (IH2 K (S k) taus taus' (tcons u0 tes) H2 Hagree)) (tm_app v u0))).
        apply F; auto.
        apply (proj2 ((proj1 (IH1 K k taus taus' tes H1 Hagree)) u0)). exact Hu1.
      - intros [A [Ab F]]. split; [exact A | split; [exact Ab | idtac]].
        intros u0 Hu0 Hu1.
        apply (proj2 ((proj1 (IH2 K (S k) taus taus' (tcons u0 tes) H2 Hagree)) (tm_app v u0))).
        apply F; auto.
        apply (proj1 ((proj1 (IH1 K k taus taus' tes H1 Hagree)) u0)). exact Hu1. }
    split.
    + intro t. split.
      * intros [A [B C]]. split; [exact A | split; [exact B | idtac]].
        intros v Hm Hv. apply (proj1 (HVS v)). apply C; auto.
      * intros [A [B C]]. split; [exact A | split; [exact B | idtac]].
        intros v Hm Hv. apply (proj2 (HVS v)). apply C; auto.
    + exact HVS.
  - destruct (lc_rty_exists K k R1 R2 Hlc) as [H1 H2].
    assert (HVS : forall v,
      value_sem taus tes (R_Exists R1 R2) v <->
      value_sem taus' tes (R_Exists R1 R2) v).
    { intro v. simpl. split.
      - intros [A [u0 [Hu0 [Hr1 Hr2]]]]. split; [exact A |].
        exists u0. split; [exact Hu0 | split].
        + apply (proj1 ((proj1 (IH1 K k taus taus' tes H1 Hagree)) u0)). exact Hr1.
        + apply (proj1 ((proj1 (IH2 K (S k) taus taus' (tcons u0 tes) H2 Hagree)) v)). exact Hr2.
      - intros [A [u0 [Hu0 [Hr1 Hr2]]]]. split; [exact A |].
        exists u0. split; [exact Hu0 | split].
        + apply (proj2 ((proj1 (IH1 K k taus taus' tes H1 Hagree)) u0)). exact Hr1.
        + apply (proj2 ((proj1 (IH2 K (S k) taus taus' (tcons u0 tes) H2 Hagree)) v)). exact Hr2. }
    split.
    + intro t. split.
      * intros [A [B C]]. split; [exact A | split; [exact B | idtac]].
        intros v Hm Hv. apply (proj1 (HVS v)). apply C; auto.
      * intros [A [B C]]. split; [exact A | split; [exact B | idtac]].
        intros v Hm Hv. apply (proj2 (HVS v)). apply C; auto.
    + exact HVS.
  - pose proof (lc_rty_poly K k R1 Hlc) as H1.
    assert (Hagree' : forall (U0 : ty) i, i < S K -> tycons U0 taus i = tycons U0 taus' i).
    { intros U0 i Hi. destruct i; simpl. reflexivity. apply Hagree. lia. }
    assert (HVS : forall v,
      value_sem taus tes (R_Poly R1) v <->
      value_sem taus' tes (R_Poly R1) v).
    { intro v. simpl. split.
      - intros [A [Tb F]]. split; [exact A | split; [exact Tb | idtac]].
        intros U0 HU0.
        apply (proj1 ((proj1 (IH1 (S K) k (tycons U0 taus) (tycons U0 taus') tes H1 (Hagree' U0))) (tm_tapp v U0))).
        apply F; auto.
      - intros [A [Tb F]]. split; [exact A | split; [exact Tb | idtac]].
        intros U0 HU0.
        apply (proj2 ((proj1 (IH1 (S K) k (tycons U0 taus) (tycons U0 taus') tes H1 (Hagree' U0))) (tm_tapp v U0))).
        apply F; auto. }
    split.
    + intro t. split.
      * intros [A [B C]]. split; [exact A | split; [exact B | idtac]].
        intros v Hm Hv. apply (proj1 (HVS v)). apply C; auto.
      * intros [A [B C]]. split; [exact A | split; [exact B | idtac]].
        intros v Hm Hv. apply (proj2 (HVS v)). apply C; auto.
    + exact HVS.
Qed.

(* Opening a bound type variable commutes with the semantic relation. *)
Lemma sem_open_env_and : forall R k U taus tes,
  taus k = U -> lc_ty_at 0 U ->
  (forall t, sem taus tes R t <-> sem taus tes (open_rty_ty_rec k U R) t) /\
  (forall v, value_sem taus tes R v <-> value_sem taus tes (open_rty_ty_rec k U R) v).
Proof.
  induction R as [T ps | R1 IH1 R2 IH2 | R1 IH1 R2 IH2 | R1 IH1];
    intros k U taus tes Hk HU; simpl.
  - assert (HVS : forall v,
      value_sem taus tes (R_Refine T ps) v <->
      value_sem taus tes (R_Refine (open_ty_rec k U T) (open_qualifier_ty_rec k U ps)) v).
    { intro v. simpl. split.
      - intros [A [B C]]. split; [exact A | split].
        + apply (proj2 (vty_open_ty taus k U T v Hk HU)); exact B.
        + rewrite (qinst_open_ty ps taus tes v k U Hk HU). exact C.
      - intros [A [B C]]. split; [exact A | split].
        + apply (proj1 (vty_open_ty taus k U T v Hk HU)); exact B.
        + rewrite <- (qinst_open_ty ps taus tes v k U Hk HU). exact C. }
    split.
    + intro t. split.
      * intros [A [B C]]. split; [exact A | split; [exact B | idtac]].
        intros v Hm Hv. apply (proj1 (HVS v)). apply C; auto.
      * intros [A [B C]]. split; [exact A | split; [exact B | idtac]].
        intros v Hm Hv. apply (proj2 (HVS v)). apply C; auto.
    + exact HVS.
  - assert (HVS : forall v,
      value_sem taus tes (R_Func R1 R2) v <->
      value_sem taus tes (R_Func (open_rty_ty_rec k U R1) (open_rty_ty_rec k U R2)) v).
    { intro v. simpl. split.
      - intros [A [Ab F]]. split; [exact A | split; [exact Ab | idtac]].
        intros u0 Hu0 Hu1.
        apply (proj1 ((proj1 (IH2 k U taus (tcons u0 tes) Hk HU)) (tm_app v u0))).
        apply F; auto.
        apply (proj2 ((proj1 (IH1 k U taus tes Hk HU)) u0)). exact Hu1.
      - intros [A [Ab F]]. split; [exact A | split; [exact Ab | idtac]].
        intros u0 Hu0 Hu1.
        apply (proj2 ((proj1 (IH2 k U taus (tcons u0 tes) Hk HU)) (tm_app v u0))).
        apply F; auto.
        apply (proj1 ((proj1 (IH1 k U taus tes Hk HU)) u0)). exact Hu1. }
    split.
    + intro t. split.
      * intros [A [B C]]. split; [exact A | split; [exact B | idtac]].
        intros v Hm Hv. apply (proj1 (HVS v)). apply C; auto.
      * intros [A [B C]]. split; [exact A | split; [exact B | idtac]].
        intros v Hm Hv. apply (proj2 (HVS v)). apply C; auto.
    + exact HVS.
  - assert (HVS : forall v,
      value_sem taus tes (R_Exists R1 R2) v <->
      value_sem taus tes (R_Exists (open_rty_ty_rec k U R1) (open_rty_ty_rec k U R2)) v).
    { intro v. simpl. split.
      - intros [A [u0 [Hu0 [Hr1 Hr2]]]]. split; [exact A |].
        exists u0. split; [exact Hu0 | split].
        + apply (proj1 ((proj1 (IH1 k U taus tes Hk HU)) u0)). exact Hr1.
        + apply (proj1 ((proj1 (IH2 k U taus (tcons u0 tes) Hk HU)) v)). exact Hr2.
      - intros [A [u0 [Hu0 [Hr1 Hr2]]]]. split; [exact A |].
        exists u0. split; [exact Hu0 | split].
        + apply (proj2 ((proj1 (IH1 k U taus tes Hk HU)) u0)). exact Hr1.
        + apply (proj2 ((proj1 (IH2 k U taus (tcons u0 tes) Hk HU)) v)). exact Hr2. }
    split.
    + intro t. split.
      * intros [A [B C]]. split; [exact A | split; [exact B | idtac]].
        intros v Hm Hv. apply (proj1 (HVS v)). apply C; auto.
      * intros [A [B C]]. split; [exact A | split; [exact B | idtac]].
        intros v Hm Hv. apply (proj2 (HVS v)). apply C; auto.
    + exact HVS.
  - assert (HVS : forall v,
      value_sem taus tes (R_Poly R1) v <->
      value_sem taus tes (R_Poly (open_rty_ty_rec (S k) U R1)) v).
    { intro v. simpl. split.
      - intros [A [Tb F]]. split; [exact A | split; [exact Tb | idtac]].
        intros U0 HU0.
        apply (proj1 ((proj1 (IH1 (S k) U (tycons U0 taus) tes Hk HU)) (tm_tapp v U0))).
        apply F; auto.
      - intros [A [Tb F]]. split; [exact A | split; [exact Tb | idtac]].
        intros U0 HU0.
        apply (proj2 ((proj1 (IH1 (S k) U (tycons U0 taus) tes Hk HU)) (tm_tapp v U0))).
        apply F; auto. }
    split.
    + intro t. split.
      * intros [A [B C]]. split; [exact A | split; [exact B | idtac]].
        intros v Hm Hv. apply (proj1 (HVS v)). apply C; auto.
      * intros [A [B C]]. split; [exact A | split; [exact B | idtac]].
        intros v Hm Hv. apply (proj2 (HVS v)). apply C; auto.
    + exact HVS.
Qed.

End SystemFRefinementSemantics.

Module SystemFRefinementTask.
Import ListNotations SystemFRefinement SystemFRefinementLogic SystemFRefinementTyping SystemFRefinementEvaluation SystemFRefinementSemantics.

Theorem never_stuck : forall (t t' : tm) (R : rty),
  has_rtype [] empty_rcontext t R ->
  multi t t' ->
  value t' \/ exists t'' : tm, t' --> t''.
Proof.

Qed.

End SystemFRefinementTask.
