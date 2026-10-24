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

(* ---------- simultaneous substitutions ---------- *)

Fixpoint tsubst_tm (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_abs T t1 => tm_abs T (tsubst_tm sigma t1)
  | tm_app t1 t2 => tm_app (tsubst_tm sigma t1) (tsubst_tm sigma t2)
  | tm_tabs t1 => tm_tabs (tsubst_tm sigma t1)
  | tm_tapp t1 T => tm_tapp (tsubst_tm sigma t1) T
  | tm_int n => tm_int n
  | tm_div t1 t2 => tm_div (tsubst_tm sigma t1) (tsubst_tm sigma t2)
  | tm_arith op t1 t2 => tm_arith op (tsubst_tm sigma t1) (tsubst_tm sigma t2)
  end.

Fixpoint tysubst_ty (tau : atom -> ty) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => tau X
  | Ty_Arrow T1 T2 => Ty_Arrow (tysubst_ty tau T1) (tysubst_ty tau T2)
  | Ty_All T1 => Ty_All (tysubst_ty tau T1)
  | Ty_Int => Ty_Int
  end.

Fixpoint tysubst_tm (tau : atom -> ty) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T t1 => tm_abs (tysubst_ty tau T) (tysubst_tm tau t1)
  | tm_app t1 t2 => tm_app (tysubst_tm tau t1) (tysubst_tm tau t2)
  | tm_tabs t1 => tm_tabs (tysubst_tm tau t1)
  | tm_tapp t1 T => tm_tapp (tysubst_tm tau t1) (tysubst_ty tau T)
  | tm_int n => tm_int n
  | tm_div t1 t2 => tm_div (tysubst_tm tau t1) (tysubst_tm tau t2)
  | tm_arith op t1 t2 => tm_arith op (tysubst_tm tau t1) (tysubst_tm tau t2)
  end.

Fixpoint tsubst_qual (sigma : atom -> tm) (p : qualifier) : qualifier :=
  match p with
  | Pred_True => Pred_True
  | Pred_False => Pred_False
  | Pred_Eq t1 t2 => Pred_Eq (tsubst_tm sigma t1) (tsubst_tm sigma t2)
  | Pred_Lt t1 t2 => Pred_Lt (tsubst_tm sigma t1) (tsubst_tm sigma t2)
  | Pred_Le t1 t2 => Pred_Le (tsubst_tm sigma t1) (tsubst_tm sigma t2)
  | Pred_And p1 p2 => Pred_And (tsubst_qual sigma p1) (tsubst_qual sigma p2)
  | Pred_Or p1 p2 => Pred_Or (tsubst_qual sigma p1) (tsubst_qual sigma p2)
  | Pred_Not p1 => Pred_Not (tsubst_qual sigma p1)
  end.

Fixpoint tysubst_qual (tau : atom -> ty) (p : qualifier) : qualifier :=
  match p with
  | Pred_True => Pred_True
  | Pred_False => Pred_False
  | Pred_Eq t1 t2 => Pred_Eq (tysubst_tm tau t1) (tysubst_tm tau t2)
  | Pred_Lt t1 t2 => Pred_Lt (tysubst_tm tau t1) (tysubst_tm tau t2)
  | Pred_Le t1 t2 => Pred_Le (tysubst_tm tau t1) (tysubst_tm tau t2)
  | Pred_And p1 p2 => Pred_And (tysubst_qual tau p1) (tysubst_qual tau p2)
  | Pred_Or p1 p2 => Pred_Or (tysubst_qual tau p1) (tysubst_qual tau p2)
  | Pred_Not p1 => Pred_Not (tysubst_qual tau p1)
  end.

Fixpoint tsubst_rty (sigma : atom -> tm) (R : rty) : rty :=
  match R with
  | R_Refine T ps => R_Refine T (tsubst_qual sigma ps)
  | R_Func R1 R2 => R_Func (tsubst_rty sigma R1) (tsubst_rty sigma R2)
  | R_Exists R1 R2 => R_Exists (tsubst_rty sigma R1) (tsubst_rty sigma R2)
  | R_Poly R1 => R_Poly (tsubst_rty sigma R1)
  end.

Fixpoint tysubst_rty (tau : atom -> ty) (R : rty) : rty :=
  match R with
  | R_Refine T ps => R_Refine (tysubst_ty tau T) (tysubst_qual tau ps)
  | R_Func R1 R2 => R_Func (tysubst_rty tau R1) (tysubst_rty tau R2)
  | R_Exists R1 R2 => R_Exists (tysubst_rty tau R1) (tysubst_rty tau R2)
  | R_Poly R1 => R_Poly (tysubst_rty tau R1)
  end.

Definition close_ty (tau : atom -> ty) (T : ty) : ty := tysubst_ty tau T.
Definition close_tm (sigma : atom -> tm) (tau : atom -> ty) (t : tm) : tm :=
  tysubst_tm tau (tsubst_tm sigma t).
Definition close_qual (sigma : atom -> tm) (tau : atom -> ty) (p : qualifier) : qualifier :=
  tysubst_qual tau (tsubst_qual sigma p).
Definition close_rty (sigma : atom -> tm) (tau : atom -> ty) (R : rty) : rty :=
  tysubst_rty tau (tsubst_rty sigma R).

(* ---------- opening locally closed things is the identity ---------- *)

Lemma open_ty_lc_id : forall T K, lc_ty_at K T ->
  forall j U, K <= j -> open_ty_rec j U T = T.
Proof.
  induction T as [i|X|T1 IH1 T2 IH2|T1 IH1|]; intros K Hlc j U Hle; simpl.
  - inversion Hlc as [k0 i0 Hlt|k0 X0|k0 A B HA HB|k0 A HA|k0]; subst.
    destruct (Nat.eqb j i) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + reflexivity.
  - reflexivity.
  - inversion Hlc as [k0 i0 Hlt|k0 X0|k0 A B HA HB|k0 A HA|k0]; subst.
    rewrite (IH1 K HA j U Hle). rewrite (IH2 K HB j U Hle). reflexivity.
  - inversion Hlc as [k0 i0 Hlt|k0 X0|k0 A B HA HB|k0 A HA|k0]; subst.
    rewrite (IH1 (S K) HA (S j) U ltac:(lia)). reflexivity.
  - reflexivity.
Qed.

Lemma open_tm_lc_id : forall t K k, lc_tm_at K k t ->
  forall j u, k <= j -> open_tm_rec j u t = t.
Proof.
  induction t as [i|x|T t1 IH1|t1 IH1 t2 IH2|t1 IH1|t1 IH1 T|n|t1 IH1 t2 IH2|op t1 IH1 t2 IH2];
    intros K k Hlc j u Hle; simpl.
  - inversion Hlc as [K0 k0 i0 Hlt|K0 k0 x0|K0 k0 T0 t0 HT Ht|K0 k0 t0 t3 H1 H2|K0 k0 t0 H1
      |K0 k0 t0 T0 H1 HT|K0 k0 z|K0 k0 t0 t3 H1 H2|K0 k0 op0 t0 t3 H1 H2]; subst.
    destruct (Nat.eqb j i) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + reflexivity.
  - reflexivity.
  - inversion Hlc as [K0 k0 i0 Hlt|K0 k0 x0|K0 k0 T0 t0 HT Ht|K0 k0 t0 t3 H1 H2|K0 k0 t0 H1
      |K0 k0 t0 T0 H1 HT|K0 k0 z|K0 k0 t0 t3 H1 H2|K0 k0 op0 t0 t3 H1 H2]; subst.
    rewrite (IH1 K (S k) Ht (S j) u ltac:(lia)). reflexivity.
  - inversion Hlc as [K0 k0 i0 Hlt|K0 k0 x0|K0 k0 T0 t0 HT Ht|K0 k0 t0 t3 H1 H2|K0 k0 t0 H1
      |K0 k0 t0 T0 H1 HT|K0 k0 z|K0 k0 t0 t3 H1 H2|K0 k0 op0 t0 t3 H1 H2]; subst.
    rewrite (IH1 K k H1 j u Hle). rewrite (IH2 K k H2 j u Hle). reflexivity.
  - inversion Hlc as [K0 k0 i0 Hlt|K0 k0 x0|K0 k0 T0 t0 HT Ht|K0 k0 t0 t3 H1 H2|K0 k0 t0 H1
      |K0 k0 t0 T0 H1 HT|K0 k0 z|K0 k0 t0 t3 H1 H2|K0 k0 op0 t0 t3 H1 H2]; subst.
    rewrite (IH1 (S K) k H1 j u Hle). reflexivity.
  - inversion Hlc as [K0 k0 i0 Hlt|K0 k0 x0|K0 k0 T0 t0 HT Ht|K0 k0 t0 t3 H1 H2|K0 k0 t0 H1
      |K0 k0 t0 T0 H1 HT|K0 k0 z|K0 k0 t0 t3 H1 H2|K0 k0 op0 t0 t3 H1 H2]; subst.
    rewrite (IH1 K k H1 j u Hle). reflexivity.
  - reflexivity.
  - inversion Hlc as [K0 k0 i0 Hlt|K0 k0 x0|K0 k0 T0 t0 HT Ht|K0 k0 t0 t3 H1 H2|K0 k0 t0 H1
      |K0 k0 t0 T0 H1 HT|K0 k0 z|K0 k0 t0 t3 H1 H2|K0 k0 op0 t0 t3 H1 H2]; subst.
    rewrite (IH1 K k H1 j u Hle). rewrite (IH2 K k H2 j u Hle). reflexivity.
  - inversion Hlc as [K0 k0 i0 Hlt|K0 k0 x0|K0 k0 T0 t0 HT Ht|K0 k0 t0 t3 H1 H2|K0 k0 t0 H1
      |K0 k0 t0 T0 H1 HT|K0 k0 z|K0 k0 t0 t3 H1 H2|K0 k0 op0 t0 t3 H1 H2]; subst.
    rewrite (IH1 K k H1 j u Hle). rewrite (IH2 K k H2 j u Hle). reflexivity.
Qed.

Lemma open_tm_ty_lc_id : forall t K k, lc_tm_at K k t ->
  forall j U, K <= j -> open_tm_ty_rec j U t = t.
Proof.
  induction t as [i|x|T t1 IH1|t1 IH1 t2 IH2|t1 IH1|t1 IH1 T|n|t1 IH1 t2 IH2|op t1 IH1 t2 IH2];
    intros K k Hlc j U Hle; simpl.
  - reflexivity.
  - reflexivity.
  - inversion Hlc as [K0 k0 i0 Hlt|K0 k0 x0|K0 k0 T0 t0 HT Ht|K0 k0 t0 t3 H1 H2|K0 k0 t0 H1
      |K0 k0 t0 T0 H1 HT|K0 k0 z|K0 k0 t0 t3 H1 H2|K0 k0 op0 t0 t3 H1 H2]; subst.
    rewrite (open_ty_lc_id T K HT j U Hle). rewrite (IH1 K (S k) Ht j U Hle). reflexivity.
  - inversion Hlc as [K0 k0 i0 Hlt|K0 k0 x0|K0 k0 T0 t0 HT Ht|K0 k0 t0 t3 H1 H2|K0 k0 t0 H1
      |K0 k0 t0 T0 H1 HT|K0 k0 z|K0 k0 t0 t3 H1 H2|K0 k0 op0 t0 t3 H1 H2]; subst.
    rewrite (IH1 K k H1 j U Hle). rewrite (IH2 K k H2 j U Hle). reflexivity.
  - inversion Hlc as [K0 k0 i0 Hlt|K0 k0 x0|K0 k0 T0 t0 HT Ht|K0 k0 t0 t3 H1 H2|K0 k0 t0 H1
      |K0 k0 t0 T0 H1 HT|K0 k0 z|K0 k0 t0 t3 H1 H2|K0 k0 op0 t0 t3 H1 H2]; subst.
    rewrite (IH1 (S K) k H1 (S j) U ltac:(lia)). reflexivity.
  - inversion Hlc as [K0 k0 i0 Hlt|K0 k0 x0|K0 k0 T0 t0 HT Ht|K0 k0 t0 t3 H1 H2|K0 k0 t0 H1
      |K0 k0 t0 T0 H1 HT|K0 k0 z|K0 k0 t0 t3 H1 H2|K0 k0 op0 t0 t3 H1 H2]; subst.
    rewrite (IH1 K k H1 j U Hle). rewrite (open_ty_lc_id T K HT j U Hle). reflexivity.
  - reflexivity.
  - inversion Hlc as [K0 k0 i0 Hlt|K0 k0 x0|K0 k0 T0 t0 HT Ht|K0 k0 t0 t3 H1 H2|K0 k0 t0 H1
      |K0 k0 t0 T0 H1 HT|K0 k0 z|K0 k0 t0 t3 H1 H2|K0 k0 op0 t0 t3 H1 H2]; subst.
    rewrite (IH1 K k H1 j U Hle). rewrite (IH2 K k H2 j U Hle). reflexivity.
  - inversion Hlc as [K0 k0 i0 Hlt|K0 k0 x0|K0 k0 T0 t0 HT Ht|K0 k0 t0 t3 H1 H2|K0 k0 t0 H1
      |K0 k0 t0 T0 H1 HT|K0 k0 z|K0 k0 t0 t3 H1 H2|K0 k0 op0 t0 t3 H1 H2]; subst.
    rewrite (IH1 K k H1 j U Hle). rewrite (IH2 K k H2 j U Hle). reflexivity.
Qed.

(* ---------- commutation of substitution with opening ---------- *)

Lemma tsubst_tm_open : forall sigma, (forall x, locally_closed_tm (sigma x)) ->
  forall k u t,
  tsubst_tm sigma (open_tm_rec k u t) =
  open_tm_rec k (tsubst_tm sigma u) (tsubst_tm sigma t).
Proof.
  intros sigma Hsig k u t. revert k u.
  induction t as [i|x|T t1 IH1|t1 IH1 t2 IH2|t1 IH1|t1 IH1 T|n|t1 IH1 t2 IH2|op t1 IH1 t2 IH2];
    intros k u; simpl.
  - destruct (Nat.eqb k i); auto.
  - rewrite (open_tm_lc_id (sigma x) 0 0 (Hsig x) k (tsubst_tm sigma u) ltac:(lia)). reflexivity.
  - rewrite IH1; auto.
  - rewrite IH1, IH2; auto.
  - rewrite IH1; auto.
  - rewrite IH1; auto.
  - auto.
  - rewrite IH1, IH2; auto.
  - rewrite IH1, IH2; auto.
Qed.

Lemma tysubst_tm_open : forall tau k u t,
  tysubst_tm tau (open_tm_rec k u t) =
  open_tm_rec k (tysubst_tm tau u) (tysubst_tm tau t).
Proof.
  intros tau k u t. revert k u.
  induction t as [i|x|T t1 IH1|t1 IH1 t2 IH2|t1 IH1|t1 IH1 T|n|t1 IH1 t2 IH2|op t1 IH1 t2 IH2];
    intros k u; simpl.
  - destruct (Nat.eqb k i); auto.
  - auto.
  - rewrite IH1; auto.
  - rewrite IH1, IH2; auto.
  - rewrite IH1; auto.
  - rewrite IH1; auto.
  - auto.
  - rewrite IH1, IH2; auto.
  - rewrite IH1, IH2; auto.
Qed.

Lemma tysubst_ty_open : forall tau, (forall X, lc_ty_at 0 (tau X)) ->
  forall k U T,
  tysubst_ty tau (open_ty_rec k U T) =
  open_ty_rec k (tysubst_ty tau U) (tysubst_ty tau T).
Proof.
  intros tau Htau k U T. revert k U.
  induction T as [i|X|T1 IH1 T2 IH2|T1 IH1|]; intros k U; simpl.
  - destruct (Nat.eqb k i); auto.
  - rewrite (open_ty_lc_id (tau X) 0 (Htau X) k (tysubst_ty tau U) ltac:(lia)). reflexivity.
  - rewrite IH1, IH2; auto.
  - rewrite IH1; auto.
  - auto.
Qed.

Lemma tysubst_tm_open_ty : forall tau, (forall X, lc_ty_at 0 (tau X)) ->
  forall k U t,
  tysubst_tm tau (open_tm_ty_rec k U t) =
  open_tm_ty_rec k (tysubst_ty tau U) (tysubst_tm tau t).
Proof.
  intros tau Htau k U t. revert k U.
  induction t as [i|x|T t1 IH1|t1 IH1 t2 IH2|t1 IH1|t1 IH1 T|n|t1 IH1 t2 IH2|op t1 IH1 t2 IH2];
    intros k U; simpl.
  - auto.
  - auto.
  - rewrite (tysubst_ty_open tau Htau), IH1; auto.
  - rewrite IH1, IH2; auto.
  - rewrite IH1; auto.
  - rewrite IH1, (tysubst_ty_open tau Htau); auto.
  - auto.
  - rewrite IH1, IH2; auto.
  - rewrite IH1, IH2; auto.
Qed.

Lemma tsubst_tm_open_ty : forall sigma, (forall x, locally_closed_tm (sigma x)) ->
  forall k U t,
  tsubst_tm sigma (open_tm_ty_rec k U t) =
  open_tm_ty_rec k U (tsubst_tm sigma t).
Proof.
  intros sigma Hsig k U t. revert k U.
  induction t as [i|x|T t1 IH1|t1 IH1 t2 IH2|t1 IH1|t1 IH1 T|n|t1 IH1 t2 IH2|op t1 IH1 t2 IH2];
    intros k U; simpl.
  - auto.
  - rewrite (open_tm_ty_lc_id (sigma x) 0 0 (Hsig x) k U ltac:(lia)). reflexivity.
  - rewrite IH1; auto.
  - rewrite IH1, IH2; auto.
  - rewrite IH1; auto.
  - rewrite IH1; auto.
  - auto.
  - rewrite IH1, IH2; auto.
  - rewrite IH1, IH2; auto.
Qed.
(* the input file omits open_qualifier_ty; we add it *)
Definition open_qualifier_ty (p : qualifier) (U : ty) : qualifier :=
  open_qualifier_ty_rec 0 U p.

(* ---------- monotonicity of locally-closed judgments ---------- *)

Lemma lc_ty_mono : forall k T, lc_ty_at k T -> forall k', k <= k' -> lc_ty_at k' T.
Proof.
  intros k T H. induction H as [k0 i Hlt|k0 X|k0 T1 H1 IH1 T2 H2 IH2|k0 T1 H1 IH1|k0];
    intros k' Hle; simpl.
  - apply lc_ty_bvar. lia.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; auto.
  - apply lc_ty_all. apply IH1. lia.
  - apply lc_ty_int.
Qed.

Lemma lc_tm_mono : forall K k t, lc_tm_at K k t ->
  forall K' k', K <= K' -> k <= k' -> lc_tm_at K' k' t.
Proof.
  intros K k t H. induction H as [K0 k0 i Hlt|K0 k0 x|K0 k0 T t1 HT Ht IHt|K0 k0 t1 H1 IH1 t2 H2 IH2
    |K0 k0 t1 H1 IH1|K0 k0 t1 H1 IH1 T HT|K0 k0 z|K0 k0 t1 H1 IH1 t2 H2 IH2|K0 k0 op t1 H1 IH1 t2 H2 IH2];
    intros K' k' HK Hk; simpl.
  - apply lc_tm_bvar. lia.
  - apply lc_tm_fvar.
  - apply lc_tm_abs. apply (lc_ty_mono _ _ HT). auto. apply IHt; auto. lia.
  - apply lc_tm_app; auto.
  - apply lc_tm_tabs. apply IH1; auto. lia.
  - apply lc_tm_tapp; auto. apply (lc_ty_mono _ _ HT). auto.
  - apply lc_tm_int.
  - apply lc_tm_div; auto.
  - apply lc_tm_arith; auto.
Qed.

(* ---------- qualifier substitution commutes with opening ---------- *)

Lemma tsubst_qual_open_tm : forall sigma, (forall x, locally_closed_tm (sigma x)) ->
  forall k u p,
  tsubst_qual sigma (open_qualifier_tm_rec k u p) =
  open_qualifier_tm_rec k (tsubst_tm sigma u) (tsubst_qual sigma p).
Proof.
  intros sigma Hsig k u p. revert k u.
  induction p as [| |t1 t2|t1 t2|t1 t2|p1 IH1 p2 IH2|p1 IH1 p2 IH2|p1 IH1];
    intros k u; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite !tsubst_tm_open; auto.
  - rewrite !tsubst_tm_open; auto.
  - rewrite !tsubst_tm_open; auto.
  - rewrite IH1, IH2; reflexivity.
  - rewrite IH1, IH2; reflexivity.
  - rewrite IH1; reflexivity.
Qed.

Lemma tysubst_qual_open_tm : forall tau k u p,
  tysubst_qual tau (open_qualifier_tm_rec k u p) =
  open_qualifier_tm_rec k (tysubst_tm tau u) (tysubst_qual tau p).
Proof.
  intros tau k u p. revert k u.
  induction p as [| |t1 t2|t1 t2|t1 t2|p1 IH1 p2 IH2|p1 IH1 p2 IH2|p1 IH1];
    intros k u; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite !tysubst_tm_open; reflexivity.
  - rewrite !tysubst_tm_open; reflexivity.
  - rewrite !tysubst_tm_open; reflexivity.
  - rewrite IH1, IH2; reflexivity.
  - rewrite IH1, IH2; reflexivity.
  - rewrite IH1; reflexivity.
Qed.

Lemma tsubst_qual_open_ty : forall sigma, (forall x, locally_closed_tm (sigma x)) ->
  forall k U p,
  tsubst_qual sigma (open_qualifier_ty_rec k U p) =
  open_qualifier_ty_rec k U (tsubst_qual sigma p).
Proof.
  intros sigma Hsig k U p. revert k U.
  induction p as [| |t1 t2|t1 t2|t1 t2|p1 IH1 p2 IH2|p1 IH1 p2 IH2|p1 IH1];
    intros k U; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite !tsubst_tm_open_ty; auto.
  - rewrite !tsubst_tm_open_ty; auto.
  - rewrite !tsubst_tm_open_ty; auto.
  - rewrite IH1, IH2; reflexivity.
  - rewrite IH1, IH2; reflexivity.
  - rewrite IH1; reflexivity.
Qed.

Lemma tysubst_qual_open_ty : forall tau, (forall X, lc_ty_at 0 (tau X)) ->
  forall k U p,
  tysubst_qual tau (open_qualifier_ty_rec k U p) =
  open_qualifier_ty_rec k (tysubst_ty tau U) (tysubst_qual tau p).
Proof.
  intros tau Htau k U p. revert k U.
  induction p as [| |t1 t2|t1 t2|t1 t2|p1 IH1 p2 IH2|p1 IH1 p2 IH2|p1 IH1];
    intros k U; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite !tysubst_tm_open_ty; auto.
  - rewrite !tysubst_tm_open_ty; auto.
  - rewrite !tysubst_tm_open_ty; auto.
  - rewrite IH1, IH2; reflexivity.
  - rewrite IH1, IH2; reflexivity.
  - rewrite IH1; reflexivity.
Qed.

(* ---------- rty substitution commutes with opening ---------- *)

Lemma tsubst_rty_open_tm : forall sigma, (forall x, locally_closed_tm (sigma x)) ->
  forall k u R,
  tsubst_rty sigma (open_rty_tm_rec k u R) =
  open_rty_tm_rec k (tsubst_tm sigma u) (tsubst_rty sigma R).
Proof.
  intros sigma Hsig k u R. revert k u.
  induction R as [T ps|R1 IH1 R2 IH2|R1 IH1 R2 IH2|R1 IH1]; intros k u; simpl.
  - rewrite tsubst_qual_open_tm; auto.
  - rewrite IH1, IH2; reflexivity.
  - rewrite IH1, IH2; reflexivity.
  - rewrite IH1; reflexivity.
Qed.

Lemma tysubst_rty_open_tm : forall tau k u R,
  tysubst_rty tau (open_rty_tm_rec k u R) =
  open_rty_tm_rec k (tysubst_tm tau u) (tysubst_rty tau R).
Proof.
  intros tau k u R. revert k u.
  induction R as [T ps|R1 IH1 R2 IH2|R1 IH1 R2 IH2|R1 IH1]; intros k u; simpl.
  - rewrite tysubst_qual_open_tm; reflexivity.
  - rewrite IH1, IH2; reflexivity.
  - rewrite IH1, IH2; reflexivity.
  - rewrite IH1; reflexivity.
Qed.

Lemma tsubst_rty_open_ty : forall sigma, (forall x, locally_closed_tm (sigma x)) ->
  forall k U R,
  tsubst_rty sigma (open_rty_ty_rec k U R) =
  open_rty_ty_rec k U (tsubst_rty sigma R).
Proof.
  intros sigma Hsig k U R. revert k U.
  induction R as [T ps|R1 IH1 R2 IH2|R1 IH1 R2 IH2|R1 IH1]; intros k U; simpl.
  - rewrite tsubst_qual_open_ty; auto.
  - rewrite IH1, IH2; reflexivity.
  - rewrite IH1, IH2; reflexivity.
  - rewrite IH1; reflexivity.
Qed.

Lemma tysubst_rty_open_ty : forall tau, (forall X, lc_ty_at 0 (tau X)) ->
  forall k U R,
  tysubst_rty tau (open_rty_ty_rec k U R) =
  open_rty_ty_rec k (tysubst_ty tau U) (tysubst_rty tau R).
Proof.
  intros tau Htau k U R. revert k U.
  induction R as [T ps|R1 IH1 R2 IH2|R1 IH1 R2 IH2|R1 IH1]; intros k U; simpl.
  - rewrite tysubst_ty_open; auto. rewrite tysubst_qual_open_ty; auto.
  - rewrite IH1, IH2; reflexivity.
  - rewrite IH1, IH2; reflexivity.
  - rewrite IH1; reflexivity.
Qed.

(* ---------- closed substitution lemmas ---------- *)

Lemma close_tm_open : forall sigma tau, (forall x, locally_closed_tm (sigma x)) ->
  (forall X, lc_ty_at 0 (tau X)) ->
  forall t u,
  close_tm sigma tau (open_tm t u) =
  open_tm (close_tm sigma tau t) (close_tm sigma tau u).
Proof.
  intros sigma tau Hsig Htau t u. unfold close_tm, open_tm.
  rewrite tsubst_tm_open; auto. now rewrite tysubst_tm_open.
Qed.

Lemma close_qual_open_tm : forall sigma tau, (forall x, locally_closed_tm (sigma x)) ->
  (forall X, lc_ty_at 0 (tau X)) ->
  forall p u,
  close_qual sigma tau (open_qualifier_tm p u) =
  open_qualifier_tm (close_qual sigma tau p) (close_tm sigma tau u).
Proof.
  intros sigma tau Hsig Htau p u. unfold close_qual, close_tm, open_qualifier_tm.
  rewrite tsubst_qual_open_tm; auto. now rewrite tysubst_qual_open_tm.
Qed.

Lemma close_rty_open_tm : forall sigma tau, (forall x, locally_closed_tm (sigma x)) ->
  (forall X, lc_ty_at 0 (tau X)) ->
  forall R u,
  close_rty sigma tau (open_rty_tm R u) =
  open_rty_tm (close_rty sigma tau R) (close_tm sigma tau u).
Proof.
  intros sigma tau Hsig Htau R u. unfold close_rty, close_tm, open_rty_tm.
  rewrite tsubst_rty_open_tm; auto. now rewrite tysubst_rty_open_tm.
Qed.

Lemma close_tm_open_ty : forall sigma tau, (forall x, locally_closed_tm (sigma x)) ->
  (forall X, lc_ty_at 0 (tau X)) ->
  forall t U,
  close_tm sigma tau (open_tm_ty t U) =
  open_tm_ty (close_tm sigma tau t) (close_ty tau U).
Proof.
  intros sigma tau Hsig Htau t U. unfold close_tm, close_ty, open_tm_ty.
  rewrite tsubst_tm_open_ty; auto. now rewrite tysubst_tm_open_ty.
Qed.

Lemma close_qual_open_ty : forall sigma tau, (forall x, locally_closed_tm (sigma x)) ->
  (forall X, lc_ty_at 0 (tau X)) ->
  forall p U,
  close_qual sigma tau (open_qualifier_ty p U) =
  open_qualifier_ty (close_qual sigma tau p) (close_ty tau U).
Proof.
  intros sigma tau Hsig Htau p U. unfold close_qual, close_ty, open_qualifier_ty.
  rewrite tsubst_qual_open_ty; auto. now rewrite tysubst_qual_open_ty.
Qed.

Lemma close_rty_open_ty : forall sigma tau, (forall x, locally_closed_tm (sigma x)) ->
  (forall X, lc_ty_at 0 (tau X)) ->
  forall R U,
  close_rty sigma tau (open_rty_ty R U) =
  open_rty_ty (close_rty sigma tau R) (close_ty tau U).
Proof.
  intros sigma tau Hsig Htau R U. unfold close_rty, close_ty, open_rty_ty.
  rewrite tsubst_rty_open_ty; auto. now rewrite tysubst_rty_open_ty.
Qed.

(* ---------- free variables of qualifiers and rtypes ---------- *)

Fixpoint fv_qual (p : qualifier) : list atom :=
  match p with
  | Pred_True | Pred_False => []
  | Pred_Eq t1 t2 | Pred_Lt t1 t2 | Pred_Le t1 t2 => fv_tm t1 ++ fv_tm t2
  | Pred_And p1 p2 | Pred_Or p1 p2 => fv_qual p1 ++ fv_qual p2
  | Pred_Not p1 => fv_qual p1
  end.

Fixpoint ftv_qual (p : qualifier) : list atom :=
  match p with
  | Pred_True | Pred_False => []
  | Pred_Eq t1 t2 | Pred_Lt t1 t2 | Pred_Le t1 t2 => ftv_tm t1 ++ ftv_tm t2
  | Pred_And p1 p2 | Pred_Or p1 p2 => ftv_qual p1 ++ ftv_qual p2
  | Pred_Not p1 => ftv_qual p1
  end.

Fixpoint fv_rty (R : rty) : list atom :=
  match R with
  | R_Refine T ps => fv_qual ps
  | R_Func R1 R2 | R_Exists R1 R2 => fv_rty R1 ++ fv_rty R2
  | R_Poly R1 => fv_rty R1
  end.

Fixpoint ftv_rty (R : rty) : list atom :=
  match R with
  | R_Refine T ps => fv_ty T ++ ftv_qual ps
  | R_Func R1 R2 | R_Exists R1 R2 => ftv_rty R1 ++ ftv_rty R2
  | R_Poly R1 => ftv_rty R1
  end.

Lemma in_fv_ty_fvar : forall X Y, In X (fv_ty (Ty_FVar Y)) -> Y = X.
Proof.
  intros X Y H. cbn [fv_ty] in H. destruct H as [E|H]; auto. destruct H.
Qed.

(* ---------- free type variables under type substitution ---------- *)

Lemma fv_ty_tysubst_closed : forall tau, (forall X, fv_ty (tau X) = []) ->
  forall T, fv_ty (tysubst_ty tau T) = [].
Proof.
  intros tau H T. induction T as [i|X|T1 IH1 T2 IH2|T1 IH1|]; simpl.
  - reflexivity.
  - apply H.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH1. reflexivity.
  - reflexivity.
Qed.

Lemma tysubst_ty_id : forall tau T, fv_ty T = [] -> tysubst_ty tau T = T.
Proof.
  intros tau T. induction T as [i|X|T1 IH1 T2 IH2|T1 IH1|]; simpl; intros H.
  - reflexivity.
  - simpl in H. discriminate H.
  - apply app_eq_nil in H as [H1 H2]. rewrite IH1; auto. rewrite IH2; auto.
  - rewrite IH1; auto.
  - reflexivity.
Qed.

(* ---------- free variable facts for substitution ---------- *)

Lemma fv_tm_tysubst : forall tau t, fv_tm (tysubst_tm tau t) = fv_tm t.
Proof.
  intros tau t. induction t as [i|x|T t1 IH1|t1 IH1 t2 IH2|t1 IH1|t1 IH1 T|n|t1 IH1 t2 IH2|op t1 IH1 t2 IH2];
    simpl.
  - reflexivity. - reflexivity. - rewrite IH1; reflexivity.
  - rewrite IH1, IH2; reflexivity. - rewrite IH1; reflexivity. - rewrite IH1; reflexivity.
  - reflexivity. - rewrite IH1, IH2; reflexivity. - rewrite IH1, IH2; reflexivity.
Qed.

Lemma ftv_tm_tsubst : forall sigma, (forall x, ftv_tm (sigma x) = []) ->
  forall t, ftv_tm (tsubst_tm sigma t) = ftv_tm t.
Proof.
  intros sigma H t. induction t as [i|x|T t1 IH1|t1 IH1 t2 IH2|t1 IH1|t1 IH1 T|n|t1 IH1 t2 IH2|op t1 IH1 t2 IH2];
    simpl.
  - reflexivity. - apply H. - rewrite IH1; reflexivity.
  - rewrite IH1, IH2; reflexivity. - rewrite IH1; reflexivity. - rewrite IH1; reflexivity.
  - reflexivity. - rewrite IH1, IH2; reflexivity. - rewrite IH1, IH2; reflexivity.
Qed.

Lemma fv_tm_tsubst : forall sigma, (forall x, fv_tm (sigma x) = []) ->
  forall t, fv_tm (tsubst_tm sigma t) = [].
Proof.
  intros sigma H t. induction t as [i|x|T t1 IH1|t1 IH1 t2 IH2|t1 IH1|t1 IH1 T|n|t1 IH1 t2 IH2|op t1 IH1 t2 IH2];
    simpl.
  - reflexivity. - apply H. - rewrite IH1; reflexivity.
  - rewrite IH1, IH2; reflexivity. - rewrite IH1; reflexivity. - rewrite IH1; reflexivity.
  - reflexivity. - rewrite IH1, IH2; reflexivity. - rewrite IH1, IH2; reflexivity.
Qed.

Lemma ftv_tm_tysubst : forall tau, (forall X, fv_ty (tau X) = []) ->
  forall t, ftv_tm (tysubst_tm tau t) = [].
Proof.
  intros tau H t. induction t as [i|x|T t1 IH1|t1 IH1 t2 IH2|t1 IH1|t1 IH1 T|n|t1 IH1 t2 IH2|op t1 IH1 t2 IH2];
    simpl.
  - reflexivity. - reflexivity.
  - rewrite IH1, (fv_ty_tysubst_closed tau H T); reflexivity.
  - rewrite IH1, IH2; reflexivity. - rewrite IH1; reflexivity.
  - rewrite IH1, (fv_ty_tysubst_closed tau H T); reflexivity.
  - reflexivity. - rewrite IH1, IH2; reflexivity. - rewrite IH1, IH2; reflexivity.
Qed.

Lemma fv_tm_close : forall sigma tau, (forall x, fv_tm (sigma x) = []) ->
  forall t, fv_tm (close_tm sigma tau t) = [].
Proof.
  intros sigma tau H t. unfold close_tm.
  rewrite fv_tm_tysubst. apply fv_tm_tsubst; auto.
Qed.

Lemma ftv_tm_close : forall sigma tau, (forall x, ftv_tm (sigma x) = []) ->
  (forall X, fv_ty (tau X) = []) ->
  forall t, ftv_tm (close_tm sigma tau t) = [].
Proof.
  intros sigma tau Hs Ht t. unfold close_tm.
  apply ftv_tm_tysubst; auto.
Qed.

(* ---------- substitution into fully closed things is the identity ---------- *)

Lemma tsubst_tm_id : forall sigma t, fv_tm t = [] -> tsubst_tm sigma t = t.
Proof.
  intros sigma t. induction t as [i|x|T t1 IH1|t1 IH1 t2 IH2|t1 IH1|t1 IH1 T|n|t1 IH1 t2 IH2|op t1 IH1 t2 IH2];
    simpl; intros H.
  - reflexivity.
  - simpl in H. discriminate H.
  - rewrite IH1; auto.
  - apply app_eq_nil in H as [H1 H2]. rewrite IH1; auto. rewrite IH2; auto.
  - rewrite IH1; auto.
  - rewrite IH1; auto.
  - reflexivity.
  - apply app_eq_nil in H as [H1 H2]. rewrite IH1; auto. rewrite IH2; auto.
  - apply app_eq_nil in H as [H1 H2]. rewrite IH1; auto. rewrite IH2; auto.
Qed.

Lemma tysubst_tm_id : forall tau t, ftv_tm t = [] -> tysubst_tm tau t = t.
Proof.
  intros tau t. induction t as [i|x|T t1 IH1|t1 IH1 t2 IH2|t1 IH1|t1 IH1 T|n|t1 IH1 t2 IH2|op t1 IH1 t2 IH2];
    simpl; intros H.
  - reflexivity.
  - reflexivity.
  - apply app_eq_nil in H as [H1 H2]. rewrite (tysubst_ty_id tau T H1). rewrite IH1; auto.
  - apply app_eq_nil in H as [H1 H2]. rewrite IH1; auto. rewrite IH2; auto.
  - rewrite IH1; auto.
  - apply app_eq_nil in H as [H1 H2]. rewrite (tysubst_ty_id tau T H2). rewrite IH1; auto.
  - reflexivity.
  - apply app_eq_nil in H as [H1 H2]. rewrite IH1; auto. rewrite IH2; auto.
  - apply app_eq_nil in H as [H1 H2]. rewrite IH1; auto. rewrite IH2; auto.
Qed.

Lemma close_tm_id : forall sigma tau t, fv_tm t = [] -> ftv_tm t = [] ->
  close_tm sigma tau t = t.
Proof.
  intros sigma tau t H1 H2. unfold close_tm.
  rewrite tsubst_tm_id; auto. apply tysubst_tm_id; auto.
Qed.

Lemma tsubst_qual_id : forall sigma p, fv_qual p = [] -> tsubst_qual sigma p = p.
Proof.
  intros sigma p. induction p as [| |t1 t2|t1 t2|t1 t2|p1 IH1 p2 IH2|p1 IH1 p2 IH2|p1 IH1];
    simpl; intros H.
  - reflexivity. - reflexivity.
  - apply app_eq_nil in H as [H1 H2]. rewrite (tsubst_tm_id _ _ H1), (tsubst_tm_id _ _ H2); reflexivity.
  - apply app_eq_nil in H as [H1 H2]. rewrite (tsubst_tm_id _ _ H1), (tsubst_tm_id _ _ H2); reflexivity.
  - apply app_eq_nil in H as [H1 H2]. rewrite (tsubst_tm_id _ _ H1), (tsubst_tm_id _ _ H2); reflexivity.
  - apply app_eq_nil in H as [H1 H2]. rewrite IH1; auto. rewrite IH2; auto.
  - apply app_eq_nil in H as [H1 H2]. rewrite IH1; auto. rewrite IH2; auto.
  - rewrite IH1; auto.
Qed.

Lemma tysubst_qual_id : forall tau p, ftv_qual p = [] -> tysubst_qual tau p = p.
Proof.
  intros tau p. induction p as [| |t1 t2|t1 t2|t1 t2|p1 IH1 p2 IH2|p1 IH1 p2 IH2|p1 IH1];
    simpl; intros H.
  - reflexivity. - reflexivity.
  - apply app_eq_nil in H as [H1 H2]. rewrite (tysubst_tm_id _ _ H1), (tysubst_tm_id _ _ H2); reflexivity.
  - apply app_eq_nil in H as [H1 H2]. rewrite (tysubst_tm_id _ _ H1), (tysubst_tm_id _ _ H2); reflexivity.
  - apply app_eq_nil in H as [H1 H2]. rewrite (tysubst_tm_id _ _ H1), (tysubst_tm_id _ _ H2); reflexivity.
  - apply app_eq_nil in H as [H1 H2]. rewrite IH1; auto. rewrite IH2; auto.
  - apply app_eq_nil in H as [H1 H2]. rewrite IH1; auto. rewrite IH2; auto.
  - rewrite IH1; auto.
Qed.

Lemma close_qual_id : forall sigma tau p, fv_qual p = [] -> ftv_qual p = [] ->
  close_qual sigma tau p = p.
Proof.
  intros sigma tau p H1 H2. unfold close_qual.
  rewrite tsubst_qual_id; auto. apply tysubst_qual_id; auto.
Qed.

(* ---------- persistence of free variables under opening ---------- *)

Lemma fv_ty_open_ty_persist : forall T k U x,
  In x (fv_ty T) -> In x (fv_ty (open_ty_rec k U T)) \/ In x (fv_ty U).
Proof.
  induction T as [i|X|T1 IH1 T2 IH2|T1 IH1|]; intros k U x Hin; simpl in *.
  - destruct Hin.
  - destruct Hin as [E|[]]; subst; simpl; auto.
  - apply in_app_or in Hin as [H|H].
    + destruct (IH1 k U x H) as [H1|H1]; [left; apply in_or_app; left; exact H1 | right; exact H1].
    + destruct (IH2 k U x H) as [H1|H1]; [left; apply in_or_app; right; exact H1 | right; exact H1].
  - apply (IH1 (S k) U x Hin).
  - destruct Hin.
Qed.

Lemma fv_tm_open_persist : forall t k u x,
  In x (fv_tm t) -> In x (fv_tm (open_tm_rec k u t)).
Proof.
  induction t as [i|x0|T t1 IH1|t1 IH1 t2 IH2|t1 IH1|t1 IH1 T|n|t1 IH1 t2 IH2|op t1 IH1 t2 IH2];
    intros k u x Hin; simpl in *.
  - destruct Hin.
  - destruct Hin as [E|[]]; subst; auto.
  - apply (IH1 (S k) u x Hin).
  - apply in_app_or in Hin as [H|H]; apply in_or_app; [left|right]; auto.
  - apply (IH1 k u x Hin).
  - apply (IH1 k u x Hin).
  - destruct Hin.
  - apply in_app_or in Hin as [H|H]; apply in_or_app; [left|right]; auto.
  - apply in_app_or in Hin as [H|H]; apply in_or_app; [left|right]; auto.
Qed.

Lemma ftv_tm_open_persist : forall t k u x,
  In x (ftv_tm t) -> In x (ftv_tm (open_tm_rec k u t)).
Proof.
  induction t as [i|x0|T t1 IH1|t1 IH1 t2 IH2|t1 IH1|t1 IH1 T|n|t1 IH1 t2 IH2|op t1 IH1 t2 IH2];
    intros k u x Hin; simpl in *.
  - destruct Hin.
  - destruct Hin.
  - apply in_app_or in Hin as [H|H]; apply in_or_app; [left|right]; auto.
  - apply in_app_or in Hin as [H|H]; apply in_or_app; [left|right]; auto.
  - apply (IH1 k u x Hin).
  - apply in_app_or in Hin as [H|H]; apply in_or_app; [left|right]; auto.
  - destruct Hin.
  - apply in_app_or in Hin as [H|H]; apply in_or_app; [left|right]; auto.
  - apply in_app_or in Hin as [H|H]; apply in_or_app; [left|right]; auto.
Qed.

Lemma fv_tm_open_ty : forall k U t, fv_tm (open_tm_ty_rec k U t) = fv_tm t.
Proof.
  intros k U t. revert k U.
  induction t as [i|x|T t1 IH1|t1 IH1 t2 IH2|t1 IH1|t1 IH1 T|n|t1 IH1 t2 IH2|op t1 IH1 t2 IH2];
    intros k U; simpl.
  - reflexivity. - reflexivity. - apply IH1.
  - rewrite IH1, IH2; reflexivity. - apply IH1. - apply IH1.
  - reflexivity. - rewrite IH1, IH2; reflexivity. - rewrite IH1, IH2; reflexivity.
Qed.

Lemma ftv_tm_open_ty_persist : forall t k U x,
  In x (ftv_tm t) -> In x (ftv_tm (open_tm_ty_rec k U t)) \/ In x (fv_ty U).
Proof.
  induction t as [i|x0|T t1 IH1|t1 IH1 t2 IH2|t1 IH1|t1 IH1 T|n|t1 IH1 t2 IH2|op t1 IH1 t2 IH2];
    intros k U x Hin; simpl in *.
  - destruct Hin.
  - destruct Hin.
  - apply in_app_or in Hin as [H|H].
    + destruct (fv_ty_open_ty_persist T k U x H) as [H1|H1].
      * left. apply in_or_app. left. auto.
      * right. auto.
    + destruct (IH1 k U x H) as [H1|H1].
      * left. apply in_or_app. right. auto.
      * right. auto.
  - apply in_app_or in Hin as [H|H].
    + destruct (IH1 k U x H) as [H1|H1]; [left; apply in_or_app; left; auto | right; auto].
    + destruct (IH2 k U x H) as [H1|H1]; [left; apply in_or_app; right; auto | right; auto].
  - destruct (IH1 (S k) U x Hin) as [H1|H1]; [left; auto | right; auto].
  - apply in_app_or in Hin as [H|H].
    + destruct (IH1 k U x H) as [H1|H1]; [left; apply in_or_app; left; auto | right; auto].
    + destruct (fv_ty_open_ty_persist T k U x H) as [H1|H1].
      * left. apply in_or_app. right. auto.
      * right. auto.
  - destruct Hin.
  - apply in_app_or in Hin as [H|H].
    + destruct (IH1 k U x H) as [H1|H1]; [left; apply in_or_app; left; auto | right; auto].
    + destruct (IH2 k U x H) as [H1|H1]; [left; apply in_or_app; right; auto | right; auto].
  - apply in_app_or in Hin as [H|H].
    + destruct (IH1 k U x H) as [H1|H1]; [left; apply in_or_app; left; auto | right; auto].
    + destruct (IH2 k U x H) as [H1|H1]; [left; apply in_or_app; right; auto | right; auto].
Qed.

(* ---------- local closure is preserved by substitution ---------- *)

Lemma lc_ty_tysubst : forall T K, lc_ty_at K T ->
  forall tau, (forall X, lc_ty_at K (tau X)) -> lc_ty_at K (tysubst_ty tau T).
Proof.
  induction T as [i|X|T1 IH1 T2 IH2|T1 IH1|]; intros K Hlc tau Htau; simpl.
  - inversion Hlc as [k i0 Hlt|k X0|k A B HA HB|k A HA|k]; subst. apply lc_ty_bvar; auto.
  - apply Htau.
  - inversion Hlc as [k i0 Hlt|k X0|k A B HA HB|k A HA|k]; subst.
    apply lc_ty_arrow; [apply (IH1 K HA tau Htau) | apply (IH2 K HB tau Htau)].
  - inversion Hlc as [k i0 Hlt|k X0|k A B HA HB|k A HA|k]; subst.
    apply lc_ty_all. apply (IH1 (S K) HA tau).
    intros X. apply (lc_ty_mono K (tau X) (Htau X) (S K) (Nat.le_succ_diag_r K)).
  - apply lc_ty_int.
Qed.

Lemma lc_tm_tysubst : forall t K k, lc_tm_at K k t ->
  forall tau, (forall X, lc_ty_at K (tau X)) -> lc_tm_at K k (tysubst_tm tau t).
Proof.
  induction t as [i|x|T t1 IH1|t1 IH1 t2 IH2|t1 IH1|t1 IH1 T|n|t1 IH1 t2 IH2|op t1 IH1 t2 IH2];
    intros K k Hlc tau Htau; simpl.
  - inversion Hlc as [K0 k0 i0 Hlt|K0 k0 x0|K0 k0 T0 t0 HT Ht|K0 k0 t0 t3 H1 H2|K0 k0 t0 H1
      |K0 k0 t0 T0 H1 HT0|K0 k0 z|K0 k0 t0 t3 H1 H2|K0 k0 op0 t0 t3 H1 H2]; subst.
    apply lc_tm_bvar; auto.
  - apply lc_tm_fvar.
  - inversion Hlc as [K0 k0 i0 Hlt|K0 k0 x0|K0 k0 T0 t0 HT Ht|K0 k0 t0 t3 H1 H2|K0 k0 t0 H1
      |K0 k0 t0 T0 H1 HT0|K0 k0 z|K0 k0 t0 t3 H1 H2|K0 k0 op0 t0 t3 H1 H2]; subst.
    apply lc_tm_abs. apply (lc_ty_tysubst T K HT tau Htau). apply (IH1 K (S k) Ht tau Htau).
  - inversion Hlc as [K0 k0 i0 Hlt|K0 k0 x0|K0 k0 T0 t0 HT Ht|K0 k0 t0 t3 H1 H2|K0 k0 t0 H1
      |K0 k0 t0 T0 H1 HT0|K0 k0 z|K0 k0 t0 t3 H1 H2|K0 k0 op0 t0 t3 H1 H2]; subst.
    apply lc_tm_app; [apply (IH1 K k H1 tau Htau) | apply (IH2 K k H2 tau Htau)].
  - inversion Hlc as [K0 k0 i0 Hlt|K0 k0 x0|K0 k0 T0 t0 HT Ht|K0 k0 t0 t3 H1 H2|K0 k0 t0 H1
      |K0 k0 t0 T0 H1 HT0|K0 k0 z|K0 k0 t0 t3 H1 H2|K0 k0 op0 t0 t3 H1 H2]; subst.
    apply lc_tm_tabs. apply (IH1 (S K) k H1 tau).
    intros X. apply (lc_ty_mono K (tau X) (Htau X) (S K) (Nat.le_succ_diag_r K)).
  - inversion Hlc as [K0 k0 i0 Hlt|K0 k0 x0|K0 k0 T0 t0 HT Ht|K0 k0 t0 t3 H1 H2|K0 k0 t0 H1
      |K0 k0 t0 T0 H1 HT0|K0 k0 z|K0 k0 t0 t3 H1 H2|K0 k0 op0 t0 t3 H1 H2]; subst.
    apply lc_tm_tapp. apply (IH1 K k H1 tau Htau). apply (lc_ty_tysubst T K HT0 tau Htau).
  - inversion Hlc as [K0 k0 i0 Hlt|K0 k0 x0|K0 k0 T0 t0 HT Ht|K0 k0 t0 t3 H1 H2|K0 k0 t0 H1
      |K0 k0 t0 T0 H1 HT0|K0 k0 z|K0 k0 t0 t3 H1 H2|K0 k0 op0 t0 t3 H1 H2]; subst.
    apply lc_tm_int.
  - inversion Hlc as [K0 k0 i0 Hlt|K0 k0 x0|K0 k0 T0 t0 HT Ht|K0 k0 t0 t3 H1 H2|K0 k0 t0 H1
      |K0 k0 t0 T0 H1 HT0|K0 k0 z|K0 k0 t0 t3 H1 H2|K0 k0 op0 t0 t3 H1 H2]; subst.
    apply lc_tm_div; [apply (IH1 K k H1 tau Htau) | apply (IH2 K k H2 tau Htau)].
  - inversion Hlc as [K0 k0 i0 Hlt|K0 k0 x0|K0 k0 T0 t0 HT Ht|K0 k0 t0 t3 H1 H2|K0 k0 t0 H1
      |K0 k0 t0 T0 H1 HT0|K0 k0 z|K0 k0 t0 t3 H1 H2|K0 k0 op0 t0 t3 H1 H2]; subst.
    apply lc_tm_arith; [apply (IH1 K k H1 tau Htau) | apply (IH2 K k H2 tau Htau)].
Qed.

Lemma lc_tm_tsubst : forall t K k, lc_tm_at K k t ->
  forall sigma, (forall x, lc_tm_at K k (sigma x)) -> lc_tm_at K k (tsubst_tm sigma t).
Proof.
  induction t as [i|x|T t1 IH1|t1 IH1 t2 IH2|t1 IH1|t1 IH1 T|n|t1 IH1 t2 IH2|op t1 IH1 t2 IH2];
    intros K k Hlc sigma Hsig; simpl.
  - inversion Hlc as [K0 k0 i0 Hlt|K0 k0 x0|K0 k0 T0 t0 HT Ht|K0 k0 t0 t3 H1 H2|K0 k0 t0 H1
      |K0 k0 t0 T0 H1 HT0|K0 k0 z|K0 k0 t0 t3 H1 H2|K0 k0 op0 t0 t3 H1 H2]; subst.
    apply lc_tm_bvar; auto.
  - apply Hsig.
  - inversion Hlc as [K0 k0 i0 Hlt|K0 k0 x0|K0 k0 T0 t0 HT Ht|K0 k0 t0 t3 H1 H2|K0 k0 t0 H1
      |K0 k0 t0 T0 H1 HT0|K0 k0 z|K0 k0 t0 t3 H1 H2|K0 k0 op0 t0 t3 H1 H2]; subst.
    apply lc_tm_abs. auto. apply (IH1 K (S k) Ht sigma).
    intros x. apply (lc_tm_mono K k (sigma x) (Hsig x) K (S k) (le_n K) (Nat.le_succ_diag_r k)).
  - inversion Hlc as [K0 k0 i0 Hlt|K0 k0 x0|K0 k0 T0 t0 HT Ht|K0 k0 t0 t3 H1 H2|K0 k0 t0 H1
      |K0 k0 t0 T0 H1 HT0|K0 k0 z|K0 k0 t0 t3 H1 H2|K0 k0 op0 t0 t3 H1 H2]; subst.
    apply lc_tm_app; [apply (IH1 K k H1 sigma Hsig) | apply (IH2 K k H2 sigma Hsig)].
  - inversion Hlc as [K0 k0 i0 Hlt|K0 k0 x0|K0 k0 T0 t0 HT Ht|K0 k0 t0 t3 H1 H2|K0 k0 t0 H1
      |K0 k0 t0 T0 H1 HT0|K0 k0 z|K0 k0 t0 t3 H1 H2|K0 k0 op0 t0 t3 H1 H2]; subst.
    apply lc_tm_tabs. apply (IH1 (S K) k H1 sigma).
    intros x. apply (lc_tm_mono K k (sigma x) (Hsig x) (S K) k (Nat.le_succ_diag_r K) (le_n k)).
  - inversion Hlc as [K0 k0 i0 Hlt|K0 k0 x0|K0 k0 T0 t0 HT Ht|K0 k0 t0 t3 H1 H2|K0 k0 t0 H1
      |K0 k0 t0 T0 H1 HT0|K0 k0 z|K0 k0 t0 t3 H1 H2|K0 k0 op0 t0 t3 H1 H2]; subst.
    apply lc_tm_tapp; [apply (IH1 K k H1 sigma Hsig) | auto].
  - inversion Hlc as [K0 k0 i0 Hlt|K0 k0 x0|K0 k0 T0 t0 HT Ht|K0 k0 t0 t3 H1 H2|K0 k0 t0 H1
      |K0 k0 t0 T0 H1 HT0|K0 k0 z|K0 k0 t0 t3 H1 H2|K0 k0 op0 t0 t3 H1 H2]; subst.
    apply lc_tm_int.
  - inversion Hlc as [K0 k0 i0 Hlt|K0 k0 x0|K0 k0 T0 t0 HT Ht|K0 k0 t0 t3 H1 H2|K0 k0 t0 H1
      |K0 k0 t0 T0 H1 HT0|K0 k0 z|K0 k0 t0 t3 H1 H2|K0 k0 op0 t0 t3 H1 H2]; subst.
    apply lc_tm_div; [apply (IH1 K k H1 sigma Hsig) | apply (IH2 K k H2 sigma Hsig)].
  - inversion Hlc as [K0 k0 i0 Hlt|K0 k0 x0|K0 k0 T0 t0 HT Ht|K0 k0 t0 t3 H1 H2|K0 k0 t0 H1
      |K0 k0 t0 T0 H1 HT0|K0 k0 z|K0 k0 t0 t3 H1 H2|K0 k0 op0 t0 t3 H1 H2]; subst.
    apply lc_tm_arith; [apply (IH1 K k H1 sigma Hsig) | apply (IH2 K k H2 sigma Hsig)].
Qed.

Lemma lc_tm_close : forall K k t, lc_tm_at K k t ->
  forall sigma tau, (forall x, lc_tm_at 0 0 (sigma x)) -> (forall X, lc_ty_at 0 (tau X)) ->
  lc_tm_at K k (close_tm sigma tau t).
Proof.
  intros K k t Hlc sigma tau Hsig Htau. unfold close_tm.
  apply lc_tm_tysubst.
  - apply lc_tm_tsubst with (K := K) (k := k).
    + auto.
    + intros x. apply (lc_tm_mono 0 0 (sigma x) (Hsig x) K k (Nat.le_0_l K) (Nat.le_0_l k)).
  - intros X. apply (lc_ty_mono 0 (tau X) (Htau X) K (Nat.le_0_l K)).
Qed.

Lemma value_lc : forall v, value v -> locally_closed_tm v.
Proof.
  intros v H. destruct H as [T t Hlc|t Hlc|n].
  - auto.
  - auto.
  - apply lc_tm_int.
Qed.

Lemma value_close : forall v, value v ->
  forall sigma tau, (forall x, lc_tm_at 0 0 (sigma x)) -> (forall X, lc_ty_at 0 (tau X)) ->
  value (close_tm sigma tau v).
Proof.
  intros v Hv. induction Hv as [T t Hlc|t Hlc|n]; intros sigma tau Hsig Htau; simpl.
  - apply v_abs. simpl. unfold locally_closed_tm in Hlc.
    inversion Hlc as [K0 k0 i Hlt|K0 k0 x|K0 k0 T0 t0 HT Ht|K0 k0 t0 H1 H2|K0 k0 t0 H1
      |K0 k0 t0 H1 T0 HT|K0 k0 z|K0 k0 t0 H1 t3 H2|K0 k0 op0 t0 H1 t3 H2]; subst.
    apply lc_tm_abs.
    + apply (lc_ty_tysubst T 0 HT tau Htau).
    + apply (lc_tm_close 0 (S 0) t Ht sigma tau Hsig Htau).
  - apply v_tabs. simpl. unfold locally_closed_tm in Hlc.
    inversion Hlc as [K0 k0 i Hlt|K0 k0 x|K0 k0 T0 t0 HT Ht|K0 k0 t0 H1 H2|K0 k0 t0 H1
      |K0 k0 t0 H1 T0 HT|K0 k0 z|K0 k0 t0 H1 t3 H2|K0 k0 op0 t0 H1 t3 H2]; subst.
    apply lc_tm_tabs. apply (lc_tm_close (S 0) 0 t H1 sigma tau Hsig Htau).
  - apply v_int.
Qed.

(* ---------- opening inversion for local closure ---------- *)

Lemma lc_ty_open_inv : forall K j U T, j < K ->
  lc_ty_at K (open_ty_rec j U T) -> lc_ty_at K T.
Proof.
  intros K j U T. revert K j U.
  induction T as [i|X|T1 IH1 T2 IH2|T1 IH1|]; intros K j U Hlt Hlc; simpl in *.
  - destruct (Nat.eqb j i) eqn:E.
    + apply Nat.eqb_eq in E. subst j. apply lc_ty_bvar. auto.
    + auto.
  - apply lc_ty_fvar.
  - inversion Hlc as [k0 i0 Hl0|k0 X0|k0 A B HA HB|k0 A HA|k0]; subst.
    apply lc_ty_arrow; [exact (IH1 K j U Hlt HA) | exact (IH2 K j U Hlt HB)].
  - inversion Hlc as [k0 i0 Hl0|k0 X0|k0 A B HA HB|k0 A HA|k0]; subst.
    apply lc_ty_all. apply (IH1 (S K) (S j) U ltac:(lia) HA).
  - apply lc_ty_int.
Qed.

Lemma lc_ty_open_inv_succ_aux : forall T K U,
  lc_ty_at K (open_ty_rec K U T) -> lc_ty_at (S K) T.
Proof.
  induction T as [i|X|T1 IH1 T2 IH2|T1 IH1|]; intros K U Hlc; simpl in *.
  - destruct (Nat.eqb K i) eqn:E.
    + apply Nat.eqb_eq in E. subst i. apply lc_ty_bvar. lia.
    + apply lc_ty_bvar. inversion Hlc as [k0 i0 Hl0|k0 X0|k0 A B HA HB|k0 A HA|k0]; subst. lia.
  - apply lc_ty_fvar.
  - inversion Hlc as [k0 i0 Hl0|k0 X0|k0 A B HA HB|k0 A HA|k0]; subst.
    apply lc_ty_arrow; [exact (IH1 K U HA) | exact (IH2 K U HB)].
  - inversion Hlc as [k0 i0 Hl0|k0 X0|k0 A B HA HB|k0 A HA|k0]; subst.
    apply lc_ty_all. apply (IH1 (S K) U HA).
  - apply lc_ty_int.
Qed.

Lemma lc_ty_open_inv_succ : forall K j U T, j = K ->
  lc_ty_at K (open_ty_rec j U T) -> lc_ty_at (S K) T.
Proof.
  intros K j U T Heq. subst j. apply lc_ty_open_inv_succ_aux.
Qed.

Lemma lc_tm_open_inv_aux : forall t K k u,
  lc_tm_at K k (open_tm_rec k u t) -> lc_tm_at K (S k) t.
Proof.
  induction t as [i|x|T t1 IH1|t1 IH1 t2 IH2|t1 IH1|t1 IH1 T|n|t1 IH1 t2 IH2|op t1 IH1 t2 IH2];
    intros K k u Hlc; simpl in *.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst i. apply lc_tm_bvar. lia.
    + inversion Hlc as [K0 k0 i0 Hlt|K0 k0 x0|K0 k0 T0 t0 HT Ht|K0 k0 t0 t3 H1 H2|K0 k0 t0 H1
        |K0 k0 t0 T0 H1 HT0|K0 k0 z|K0 k0 t0 t3 H1 H2|K0 k0 op0 t0 t3 H1 H2]; subst.
      apply lc_tm_bvar. lia.
  - apply lc_tm_fvar.
  - inversion Hlc as [K0 k0 i0 Hlt|K0 k0 x0|K0 k0 T0 t0 HT Ht|K0 k0 t0 t3 H1 H2|K0 k0 t0 H1
      |K0 k0 t0 T0 H1 HT0|K0 k0 z|K0 k0 t0 t3 H1 H2|K0 k0 op0 t0 t3 H1 H2]; subst.
    apply lc_tm_abs. exact HT. apply (IH1 K (S k) u Ht).
  - inversion Hlc as [K0 k0 i0 Hlt|K0 k0 x0|K0 k0 T0 t0 HT Ht|K0 k0 t0 t3 H1 H2|K0 k0 t0 H1
      |K0 k0 t0 T0 H1 HT0|K0 k0 z|K0 k0 t0 t3 H1 H2|K0 k0 op0 t0 t3 H1 H2]; subst.
    apply lc_tm_app; [exact (IH1 K k u H1) | exact (IH2 K k u H2)].
  - inversion Hlc as [K0 k0 i0 Hlt|K0 k0 x0|K0 k0 T0 t0 HT Ht|K0 k0 t0 t3 H1 H2|K0 k0 t0 H1
      |K0 k0 t0 T0 H1 HT0|K0 k0 z|K0 k0 t0 t3 H1 H2|K0 k0 op0 t0 t3 H1 H2]; subst.
    apply lc_tm_tabs. apply (IH1 (S K) k u H1).
  - inversion Hlc as [K0 k0 i0 Hlt|K0 k0 x0|K0 k0 T0 t0 HT Ht|K0 k0 t0 t3 H1 H2|K0 k0 t0 H1
      |K0 k0 t0 T0 H1 HT0|K0 k0 z|K0 k0 t0 t3 H1 H2|K0 k0 op0 t0 t3 H1 H2]; subst.
    apply lc_tm_tapp; [exact (IH1 K k u H1) | exact HT0].
  - inversion Hlc as [K0 k0 i0 Hlt|K0 k0 x0|K0 k0 T0 t0 HT Ht|K0 k0 t0 t3 H1 H2|K0 k0 t0 H1
      |K0 k0 t0 T0 H1 HT0|K0 k0 z|K0 k0 t0 t3 H1 H2|K0 k0 op0 t0 t3 H1 H2]; subst.
    apply lc_tm_int.
  - inversion Hlc as [K0 k0 i0 Hlt|K0 k0 x0|K0 k0 T0 t0 HT Ht|K0 k0 t0 t3 H1 H2|K0 k0 t0 H1
      |K0 k0 t0 T0 H1 HT0|K0 k0 z|K0 k0 t0 t3 H1 H2|K0 k0 op0 t0 t3 H1 H2]; subst.
    apply lc_tm_div; [exact (IH1 K k u H1) | exact (IH2 K k u H2)].
  - inversion Hlc as [K0 k0 i0 Hlt|K0 k0 x0|K0 k0 T0 t0 HT Ht|K0 k0 t0 t3 H1 H2|K0 k0 t0 H1
      |K0 k0 t0 T0 H1 HT0|K0 k0 z|K0 k0 t0 t3 H1 H2|K0 k0 op0 t0 t3 H1 H2]; subst.
    apply lc_tm_arith; [exact (IH1 K k u H1) | exact (IH2 K k u H2)].
Qed.

Lemma lc_tm_open_inv : forall K k j u t, j = k ->
  lc_tm_at K k (open_tm_rec j u t) -> lc_tm_at K (S k) t.
Proof.
  intros K k j u t Heq. subst j. apply lc_tm_open_inv_aux.
Qed.

Lemma lc_tm_ty_open_inv_aux : forall t K k U,
  lc_tm_at K k (open_tm_ty_rec K U t) -> lc_tm_at (S K) k t.
Proof.
  induction t as [i|x|T t1 IH1|t1 IH1 t2 IH2|t1 IH1|t1 IH1 T|n|t1 IH1 t2 IH2|op t1 IH1 t2 IH2];
    intros K k U Hlc; simpl in *.
  - apply lc_tm_bvar. inversion Hlc as [K0 k0 i0 Hlt|K0 k0 x0|K0 k0 T0 t0 HT Ht|K0 k0 t0 t3 H1 H2|K0 k0 t0 H1
      |K0 k0 t0 T0 H1 HT0|K0 k0 z|K0 k0 t0 t3 H1 H2|K0 k0 op0 t0 t3 H1 H2]; subst. lia.
  - apply lc_tm_fvar.
  - inversion Hlc as [K0 k0 i0 Hlt|K0 k0 x0|K0 k0 T0 t0 HT Ht|K0 k0 t0 t3 H1 H2|K0 k0 t0 H1
      |K0 k0 t0 T0 H1 HT0|K0 k0 z|K0 k0 t0 t3 H1 H2|K0 k0 op0 t0 t3 H1 H2]; subst.
    apply lc_tm_abs. apply (lc_ty_open_inv_succ_aux T K U HT).
    apply (IH1 K (S k) U Ht).
  - inversion Hlc as [K0 k0 i0 Hlt|K0 k0 x0|K0 k0 T0 t0 HT Ht|K0 k0 t0 t3 H1 H2|K0 k0 t0 H1
      |K0 k0 t0 T0 H1 HT0|K0 k0 z|K0 k0 t0 t3 H1 H2|K0 k0 op0 t0 t3 H1 H2]; subst.
    apply lc_tm_app; [exact (IH1 K k U H1) | exact (IH2 K k U H2)].
  - inversion Hlc as [K0 k0 i0 Hlt|K0 k0 x0|K0 k0 T0 t0 HT Ht|K0 k0 t0 t3 H1 H2|K0 k0 t0 H1
      |K0 k0 t0 T0 H1 HT0|K0 k0 z|K0 k0 t0 t3 H1 H2|K0 k0 op0 t0 t3 H1 H2]; subst.
    apply lc_tm_tabs. apply (IH1 (S K) k U H1).
  - inversion Hlc as [K0 k0 i0 Hlt|K0 k0 x0|K0 k0 T0 t0 HT Ht|K0 k0 t0 t3 H1 H2|K0 k0 t0 H1
      |K0 k0 t0 T0 H1 HT0|K0 k0 z|K0 k0 t0 t3 H1 H2|K0 k0 op0 t0 t3 H1 H2]; subst.
    apply lc_tm_tapp.
    + exact (IH1 K k U H1).
    + apply (lc_ty_open_inv_succ_aux T K U HT0).
  - apply lc_tm_int.
  - inversion Hlc as [K0 k0 i0 Hlt|K0 k0 x0|K0 k0 T0 t0 HT Ht|K0 k0 t0 t3 H1 H2|K0 k0 t0 H1
      |K0 k0 t0 T0 H1 HT0|K0 k0 z|K0 k0 t0 t3 H1 H2|K0 k0 op0 t0 t3 H1 H2]; subst.
    apply lc_tm_div; [exact (IH1 K k U H1) | exact (IH2 K k U H2)].
  - inversion Hlc as [K0 k0 i0 Hlt|K0 k0 x0|K0 k0 T0 t0 HT Ht|K0 k0 t0 t3 H1 H2|K0 k0 t0 H1
      |K0 k0 t0 T0 H1 HT0|K0 k0 z|K0 k0 t0 t3 H1 H2|K0 k0 op0 t0 t3 H1 H2]; subst.
    apply lc_tm_arith; [exact (IH1 K k U H1) | exact (IH2 K k U H2)].
Qed.

Lemma lc_tm_ty_open_inv : forall K k j U t, j = K ->
  lc_tm_at K k (open_tm_ty_rec j U t) -> lc_tm_at (S K) k t.
Proof.
  intros K k j U t Heq. subst j. apply lc_tm_ty_open_inv_aux.
Qed.

(* ---------- erase commutes with substitution of type variables ---------- *)

Lemma erase_open_rty_ty : forall k U R,
  erase (open_rty_ty_rec k U R) = open_ty_rec k U (erase R).
Proof.
  intros k U R. revert k U.
  induction R as [T ps|R1 IH1 R2 IH2|R1 IH1 R2 IH2|R1 IH1]; intros k U; simpl.
  - reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH2. reflexivity.
  - rewrite IH1. reflexivity.
Qed.

Lemma erase_open_rty_tm : forall k u R, erase (open_rty_tm_rec k u R) = erase R.
Proof.
  intros k u R. revert k u.
  induction R as [T ps|R1 IH1 R2 IH2|R1 IH1 R2 IH2|R1 IH1]; intros k u; simpl.
  - reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH2. reflexivity.
  - rewrite IH1. reflexivity.
Qed.

(* ---------- freshness ---------- *)

Lemma max_atom_ub : forall L x, In x L -> x <= max_atom L.
Proof.
  intros L. induction L as [|a L IH]; intros x Hin; simpl in *.
  - destruct Hin.
  - destruct Hin as [E|H]; subst.
    + apply Nat.le_max_l.
    + apply Nat.le_trans with (max_atom L); [apply IH; auto | apply Nat.le_max_r].
Qed.

Lemma fresh_notin : forall L, ~ In (fresh L) L.
Proof.
  intros L Hin. apply max_atom_ub in Hin. unfold fresh in Hin. lia.
Qed.

Lemma fresh_notin_app_l : forall L1 L2, ~ In (fresh (L1 ++ L2)) L1.
Proof.
  intros L1 L2 Hin. apply (fresh_notin (L1 ++ L2)). apply in_or_app. left. auto.
Qed.

Lemma fresh_notin_app_r : forall L1 L2, ~ In (fresh (L1 ++ L2)) L2.
Proof.
  intros L1 L2 Hin. apply (fresh_notin (L1 ++ L2)). apply in_or_app. right. auto.
Qed.

(* ---------- lookup lemmas ---------- *)

Lemma lookup_update_neq : forall Gamma x y T, y <> x ->
  lookup_context y (update Gamma x T) = lookup_context y Gamma.
Proof.
  intros Gamma x y T Hne. simpl. destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. exfalso. auto.
  - reflexivity.
Qed.

Lemma lookup_rupdate_neq : forall RGamma x y R, y <> x ->
  lookup_rcontext y (update_rcontext RGamma x R) = lookup_rcontext y RGamma.
Proof.
  intros RGamma x y R Hne. simpl. destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. exfalso. auto.
  - reflexivity.
Qed.

Lemma lookup_update_eq : forall Gamma x T,
  lookup_context x (update Gamma x T) = Some T.
Proof.
  intros Gamma x T. simpl. destruct (Nat.eqb x x) eqn:E.
  - reflexivity.
  - apply Nat.eqb_neq in E. exfalso. auto.
Qed.

Lemma lookup_rupdate_eq : forall RGamma x R,
  lookup_rcontext x (update_rcontext RGamma x R) = Some R.
Proof.
  intros RGamma x R. simpl. destruct (Nat.eqb x x) eqn:E.
  - reflexivity.
  - apply Nat.eqb_neq in E. exfalso. auto.
Qed.

Lemma lookup_erase_context : forall x RGamma T,
  lookup_context x (erase_context RGamma) = Some T -> exists R, lookup_rcontext x RGamma = Some R.
Proof.
  intros x RGamma. induction RGamma as [|p RGamma IH]; intros T H.
  - simpl in H. discriminate H.
  - destruct p as [y R]. simpl in H.
    destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. subst y. exists R.
      change (lookup_rcontext x (update_rcontext RGamma x R) = Some R).
      rewrite lookup_rupdate_eq. reflexivity.
    + simpl in H. apply IH in H. destruct H as [R0 H0]. exists R0.
      change (lookup_rcontext x (update_rcontext RGamma y R) = Some R0).
      rewrite lookup_rupdate_neq; auto. apply Nat.eqb_neq in E; auto.
Qed.

Lemma erase_context_dom_lookup : forall x RGamma R,
  lookup_rcontext x RGamma = Some R -> exists T, lookup_context x (erase_context RGamma) = Some T.
Proof.
  intros x RGamma. induction RGamma as [|p RGamma IH]; intros R H.
  - simpl in H. discriminate H.
  - destruct p as [y R0]. simpl in H.
    destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. subst y. exists (erase R0).
      change (lookup_context x (update (erase_context RGamma) x (erase R0)) = Some (erase R0)).
      rewrite lookup_update_eq. reflexivity.
    + simpl in H. apply IH in H. destruct H as [T HT]. exists T.
      change (lookup_context x (update (erase_context RGamma) y (erase R0)) = Some T).
      rewrite lookup_update_neq; auto. apply Nat.eqb_neq in E; auto.
Qed.

(* ---------- two distinct fresh atoms ---------- *)

Definition fresh2 (L : list atom) : atom := fresh (fresh L :: L).

Lemma fresh2_notin : forall L, ~ In (fresh2 L) L.
Proof.
  intros L H. unfold fresh2 in H. apply (fresh_notin (fresh L :: L)). apply in_cons. auto.
Qed.

Lemma fresh2_neq : forall L, fresh L <> fresh2 L.
Proof.
  intros L E. unfold fresh2 in E. assert (~ In (fresh (fresh L :: L)) (fresh L :: L)).
  { apply fresh_notin. }
  apply H. rewrite <- E. left. reflexivity.
Qed.

(* ---------- well-formed types are locally closed ---------- *)

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> forall k, lc_ty_at k T.
Proof.
  intros Delta T H. induction H as [Delta X HIn|Delta T1 T2 H1 IH1 H2 IH2|L Delta T H IH|Delta];
    intros k.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; [apply IH1 | apply IH2].
  - apply lc_ty_all. apply (lc_ty_open_inv (S k) 0 (Ty_FVar (fresh (L ++ fv_ty T))) T).
    + lia.
    + apply (IH (fresh (L ++ fv_ty T)) (fresh_notin_app_l L (fv_ty T)) (S k)).
  - apply lc_ty_int.
Qed.

(* ---------- free type variables of well-formed types ---------- *)

Lemma wf_ty_fvty : forall Delta T, wf_ty Delta T ->
  forall X, In X (fv_ty T) -> In X Delta.
Proof.
  intros Delta T H. induction H as [Delta X HIn|Delta T1 T2 H1 IH1 H2 IH2|L Delta T H IH|Delta];
    intros X0 Hin.
  - simpl in Hin. destruct Hin as [E|[]]. subst. auto.
  - simpl in Hin. apply in_app_or in Hin as [Hin|Hin]; [apply IH1 | apply IH2]; auto.
  - simpl in Hin. set (Y := fresh (L ++ fv_ty T)).
    assert (HYL : ~ In Y L) by apply fresh_notin_app_l.
    assert (HYT : ~ In Y (fv_ty T)) by apply fresh_notin_app_r.
    assert (Hwf : wf_ty (Y :: Delta) (open_ty T (Ty_FVar Y))) by (unfold Y; apply H, HYL).
    assert (HIH := IH Y HYL).
    destruct (fv_ty_open_ty_persist T 0 (Ty_FVar Y) X0 Hin) as [H1|H1].
    + specialize (HIH X0 H1). destruct HIH as [E|H2].
      * exfalso. apply HYT. rewrite E. exact Hin.
      * exact H2.
    + simpl in H1. destruct H1 as [E|[]]. exfalso. apply HYT. rewrite E. exact Hin.
  - simpl in Hin. destruct Hin.
Qed.

(* ---------- erasure of well-formed rtypes is locally closed ---------- *)

Lemma wf_rty_erase_lc : forall Delta RGamma R, wf_rty Delta RGamma R ->
  forall k, lc_ty_at k (erase R).
Proof.
  intros Delta RGamma R H. induction H as [L Delta RGamma T ps Hwf Hq|L Delta RGamma R1 R2 H1 IH1 H2 IH2
    |L Delta RGamma R1 R2 H1 IH1 H2 IH2|L Delta RGamma R H IH]; intros k.
  - apply (wf_ty_lc Delta T Hwf k).
  - simpl. apply lc_ty_arrow.
    + apply IH1.
    + rewrite <- (erase_open_rty_tm 0 (tm_fvar (fresh L)) R2).
      apply (IH2 (fresh L) (fresh_notin L) k).
  - simpl. rewrite <- (erase_open_rty_tm 0 (tm_fvar (fresh L)) R2).
    apply (IH2 (fresh L) (fresh_notin L) k).
  - simpl. apply lc_ty_all.
    apply (lc_ty_open_inv (S k) 0 (Ty_FVar (fresh L)) (erase R)).
    + lia.
    + rewrite <- erase_open_rty_ty.
      apply (IH (fresh L) (fresh_notin L) (S k)).
Qed.

Lemma wf_rty_erase_fvty : forall Delta RGamma R, wf_rty Delta RGamma R ->
  forall X, In X (fv_ty (erase R)) -> In X Delta.
Proof.
  intros Delta RGamma R H. induction H as [L Delta RGamma T ps Hwf Hq|L Delta RGamma R1 R2 H1 IH1 H2 IH2
    |L Delta RGamma R1 R2 H1 IH1 H2 IH2|L Delta RGamma R H IH]; intros X0 Hin.
  - apply (wf_ty_fvty Delta T Hwf X0 Hin).
  - simpl in Hin. apply in_app_or in Hin as [Hin|Hin].
    + apply IH1; auto.
    + rewrite <- (erase_open_rty_tm 0 (tm_fvar (fresh L)) R2) in Hin.
      apply (IH2 (fresh L) (fresh_notin L)); auto.
  - simpl in Hin. rewrite <- (erase_open_rty_tm 0 (tm_fvar (fresh L)) R2) in Hin.
    apply (IH2 (fresh L) (fresh_notin L)); auto.
  - simpl in Hin. set (Y := fresh (L ++ fv_ty (erase R))).
    assert (HYL : ~ In Y L) by apply fresh_notin_app_l.
    assert (HYE : ~ In Y (fv_ty (erase R))) by apply fresh_notin_app_r.
    assert (Hwf : wf_rty (Y :: Delta) RGamma (open_rty_ty R (Ty_FVar Y)))
      by (unfold Y; apply H, HYL).
    assert (HIH := IH Y HYL).
    destruct (fv_ty_open_ty_persist (erase R) 0 (Ty_FVar Y) X0 Hin) as [H1|H1].
    + rewrite <- erase_open_rty_ty in H1. specialize (HIH X0 H1).
      destruct HIH as [E|H2].
      * exfalso. apply HYE. rewrite E. exact Hin.
      * exact H2.
    + simpl in H1. destruct H1 as [E|[]]. exfalso. apply HYE. rewrite E. exact Hin.
Qed.

(* ---------- base value shapes ---------- *)

Definition base_val (T : ty) (v : tm) : Prop :=
  match T with
  | Ty_Int => exists n : Z, v = tm_int n
  | Ty_Arrow _ _ => exists (T0 : ty) (body : tm), v = tm_abs T0 body
  | Ty_All _ => exists body : tm, v = tm_tabs body
  | _ => True
  end.

Lemma has_type_base_val : forall Delta Gamma v T,
  has_type Delta Gamma v T -> value v -> base_val T v.
Proof.
  intros Delta Gamma v T H. induction H as [Delta0 Gamma0 x T0 Hlk Hwf|L Delta0 Gamma0 T1 t2 T2 Hwf H IH
    |Delta0 Gamma0 t1 t2 T1 T2 H1 IH1 H2 IH2|L Delta0 Gamma0 t T H IH
    |Delta0 Gamma0 t T U H IH Hwf|Delta0 Gamma0 n|Delta0 Gamma0 t1 t2 H1 IH1 H2 IH2
    |Delta0 Gamma0 op t1 t2 H1 IH1 H2 IH2]; intros Hval.
  - inversion Hval.
  - simpl. exists T1, t2. reflexivity.
  - inversion Hval.
  - simpl. exists t. reflexivity.
  - inversion Hval.
  - simpl. exists n. reflexivity.
  - inversion Hval.
  - inversion Hval.
Qed.

(* ---------- core typing terms are locally closed ---------- *)

Lemma has_type_lc : forall Delta Gamma t T, has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T H. induction H as [Delta0 Gamma0 x T0 Hlk Hwf|L Delta0 Gamma0 T1 t2 T2 Hwf H IH
    |Delta0 Gamma0 t1 t2 T1 T2 H1 IH1 H2 IH2|L Delta0 Gamma0 t T H IH
    |Delta0 Gamma0 t T U H IH Hwf|Delta0 Gamma0 n|Delta0 Gamma0 t1 t2 H1 IH1 H2 IH2
    |Delta0 Gamma0 op t1 t2 H1 IH1 H2 IH2].
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + apply (wf_ty_lc Delta0 T1 Hwf 0).
    + apply (lc_tm_open_inv 0 0 0 (tm_fvar (fresh L)) t2 eq_refl).
      apply (IH (fresh L) (fresh_notin L)).
  - apply lc_tm_app; auto.
  - apply lc_tm_tabs.
    apply (lc_tm_ty_open_inv 0 0 0 (Ty_FVar (fresh L)) t eq_refl).
    apply (IH (fresh L) (fresh_notin L)).
  - apply lc_tm_tapp.
    + auto.
    + apply (wf_ty_lc Delta0 U Hwf 0).
  - apply lc_tm_int.
  - apply lc_tm_div; auto.
  - apply lc_tm_arith; auto.
Qed.

(* ---------- free variables of core-typed terms ---------- *)

Lemma has_type_fv : forall Delta Gamma t T, has_type Delta Gamma t T ->
  (forall x, In x (fv_tm t) -> exists T0, lookup_context x Gamma = Some T0) /\
  (forall X, In X (ftv_tm t) -> In X Delta).
Proof.
  intros Delta Gamma t T H. induction H as [Delta0 Gamma0 x T0 Hlk Hwf|L Delta0 Gamma0 T1 t2 T2 Hwf H IH
    |Delta0 Gamma0 t1 t2 T1 T2 H1 IH1 H2 IH2|L Delta0 Gamma0 t T H IH
    |Delta0 Gamma0 t T U H IH Hwf|Delta0 Gamma0 n|Delta0 Gamma0 t1 t2 H1 IH1 H2 IH2
    |Delta0 Gamma0 op t1 t2 H1 IH1 H2 IH2].
  - simpl. split.
    + intros y Hy. destruct Hy as [E|[]]. subst. exists T0. exact Hlk.
    + intros X Hx. destruct Hx.
  - simpl. destruct (IH (fresh L) (fresh_notin L)) as [IHf1 IHt1].
    destruct (IH (fresh2 L) (fresh2_notin L)) as [IHf2 IHt2].
    split.
    + intros y Hy.
      assert (Hy1 : In y (fv_tm (open_tm_rec 0 (tm_fvar (fresh L)) t2)))
        by (apply fv_tm_open_persist; auto).
      destruct (Nat.eqb y (fresh L)) eqn:E.
      * apply Nat.eqb_eq in E. subst y.
        assert (Hy2 : In (fresh L) (fv_tm (open_tm_rec 0 (tm_fvar (fresh2 L)) t2)))
          by (apply fv_tm_open_persist; auto).
        destruct (IHf2 (fresh L) Hy2) as [R0 H0]. exists R0.
        rewrite lookup_update_neq in H0; auto. apply fresh2_neq.
      * destruct (IHf1 y Hy1) as [R0 H0]. exists R0.
        rewrite lookup_update_neq in H0; auto. apply Nat.eqb_neq in E; auto.
    + intros X Hx. apply in_app_or in Hx as [Hx|Hx].
      * apply (wf_ty_fvty Delta0 T1 Hwf X Hx).
      * apply (IHt1 X). apply ftv_tm_open_persist. auto.
  - simpl. split.
    + intros y Hy. apply in_app_or in Hy as [Hy|Hy].
      * apply (proj1 IH1); auto.
      * apply (proj1 IH2); auto.
    + intros X Hx. apply in_app_or in Hx as [Hx|Hx].
      * apply (proj2 IH1); auto.
      * apply (proj2 IH2); auto.
  - simpl. destruct (IH (fresh L) (fresh_notin L)) as [IHf1 IHt1].
    destruct (IH (fresh2 L) (fresh2_notin L)) as [IHf2 IHt2].
    split.
    + intros y Hy. apply (IHf1 y). unfold open_tm_ty. rewrite fv_tm_open_ty. exact Hy.
    + intros X Hx.
      assert (H1 : In X (fresh L :: Delta0)).
      { destruct (ftv_tm_open_ty_persist t 0 (Ty_FVar (fresh L)) X Hx) as [H'|H'].
        - apply (IHt1 X). exact H'.
        - apply in_fv_ty_fvar in H'. rewrite H'. left. reflexivity. }
      assert (H2 : In X (fresh2 L :: Delta0)).
      { destruct (ftv_tm_open_ty_persist t 0 (Ty_FVar (fresh2 L)) X Hx) as [H'|H'].
        - apply (IHt2 X). exact H'.
        - apply in_fv_ty_fvar in H'. rewrite H'. left. reflexivity. }
      destruct H1 as [E1|E1]; destruct H2 as [E2|E2].
      * exfalso. apply (fresh2_neq L). transitivity X; auto.
      * exact E2.
      * exact E1.
      * exact E1.
  - simpl. split.
    + intros y Hy. apply (proj1 IH); auto.
    + intros X Hx. apply in_app_or in Hx as [Hx|Hx].
      * apply (proj2 IH); auto.
      * apply (wf_ty_fvty Delta0 U Hwf X Hx).
  - simpl. split; intros x Hx; destruct Hx.
  - simpl. split.
    + intros y Hy. apply in_app_or in Hy as [Hy|Hy].
      * apply (proj1 IH1); auto.
      * apply (proj1 IH2); auto.
    + intros X Hx. apply in_app_or in Hx as [Hx|Hx].
      * apply (proj2 IH1); auto.
      * apply (proj2 IH2); auto.
  - simpl. split.
    + intros y Hy. apply in_app_or in Hy as [Hy|Hy].
      * apply (proj1 IH1); auto.
      * apply (proj1 IH2); auto.
    + intros X Hx. apply in_app_or in Hx as [Hx|Hx].
      * apply (proj2 IH1); auto.
      * apply (proj2 IH2); auto.
Qed.

(* ---------- refinement-typed terms are locally closed and context-local ---------- *)

Lemma has_rtype_lc : forall Delta RGamma t R, has_rtype Delta RGamma t R -> locally_closed_tm t.
Proof.
  intros Delta RGamma t R H.
  induction H as [Delta0 RGamma0 x R0 Hlk Hwf|L Delta0 RGamma0 R1 body R2 Hwf Hbody IH
    |Delta0 RGamma0 t1 t2 R1 R2 H1 IH1 H2 IH2|L Delta0 RGamma0 body R0 Hbody IH
    |Delta0 RGamma0 t R0 U H1 IH Hwf|Delta0 RGamma0 n|Delta0 RGamma0 t1 t2 H1 IH1 H2 IH2
    |Delta0 RGamma0 op t1 t2 H1 IH1 H2 IH2|Delta0 RGamma0 v T ps Hty Hval Hwf Hpc Hqh
    |Delta0 RGamma0 t R0 S H1 IH Hwf Hsub] using has_rtype_ind.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + apply (wf_rty_erase_lc Delta0 RGamma0 R1 Hwf 0).
    + apply (lc_tm_open_inv 0 0 0 (tm_fvar (fresh L)) body eq_refl).
      apply (IH (fresh L) (fresh_notin L)).
  - apply lc_tm_app; auto.
  - apply lc_tm_tabs.
    apply (lc_tm_ty_open_inv 0 0 0 (Ty_FVar (fresh L)) body eq_refl).
    apply (IH (fresh L) (fresh_notin L)).
  - apply lc_tm_tapp; auto. apply (wf_ty_lc Delta0 U Hwf 0).
  - apply lc_tm_int.
  - apply lc_tm_div; auto.
  - apply lc_tm_arith; auto.
  - apply value_lc; auto.
  - auto.
Qed.

Lemma has_rtype_fv : forall Delta RGamma t R, has_rtype Delta RGamma t R ->
  (forall x, In x (fv_tm t) -> exists R0, lookup_rcontext x RGamma = Some R0) /\
  (forall X, In X (ftv_tm t) -> In X Delta).
Proof.
  intros Delta RGamma t R H.
  induction H as [Delta0 RGamma0 x R0 Hlk Hwf|L Delta0 RGamma0 R1 body R2 Hwf Hbody IH
    |Delta0 RGamma0 t1 t2 R1 R2 H1 IH1 H2 IH2|L Delta0 RGamma0 body R0 Hbody IH
    |Delta0 RGamma0 t R0 U H1 IH Hwf|Delta0 RGamma0 n|Delta0 RGamma0 t1 t2 H1 IH1 H2 IH2
    |Delta0 RGamma0 op t1 t2 H1 IH1 H2 IH2|Delta0 RGamma0 v T ps Hty Hval Hwf Hpc Hqh
    |Delta0 RGamma0 t R0 S H1 IH Hwf Hsub] using has_rtype_ind.
  - simpl. split.
    + intros y Hy. destruct Hy as [E|[]]. subst. exists R0. exact Hlk.
    + intros X Hx. destruct Hx.
  - simpl.
    destruct (IH (fresh L) (fresh_notin L)) as [IHf1 IHt1].
    destruct (IH (fresh2 L) (fresh2_notin L)) as [IHf2 IHt2].
    split.
    + intros y Hy.
      assert (Hy1 : In y (fv_tm (open_tm_rec 0 (tm_fvar (fresh L)) body)))
        by (apply fv_tm_open_persist; auto).
      destruct (Nat.eqb y (fresh L)) eqn:E.
      * apply Nat.eqb_eq in E. subst y.
        assert (Hy2 : In (fresh L) (fv_tm (open_tm_rec 0 (tm_fvar (fresh2 L)) body)))
          by (apply fv_tm_open_persist; auto).
        destruct (IHf2 (fresh L) Hy2) as [R0 H0]. exists R0.
        rewrite lookup_rupdate_neq in H0; auto. apply fresh2_neq.
      * destruct (IHf1 y Hy1) as [R0 H0]. exists R0.
        rewrite lookup_rupdate_neq in H0; auto. apply Nat.eqb_neq in E; auto.
    + intros X Hx. apply in_app_or in Hx as [Hx|Hx].
      * apply (wf_rty_erase_fvty Delta0 RGamma0 R1 Hwf X Hx).
      * apply (IHt1 X). apply ftv_tm_open_persist. auto.
  - simpl. split.
    + intros y Hy. apply in_app_or in Hy as [Hy|Hy].
      * apply (proj1 IH1); auto.
      * apply (proj1 IH2); auto.
    + intros X Hx. apply in_app_or in Hx as [Hx|Hx].
      * apply (proj2 IH1); auto.
      * apply (proj2 IH2); auto.
  - simpl.
    destruct (IH (fresh L) (fresh_notin L)) as [IHf1 IHt1].
    destruct (IH (fresh2 L) (fresh2_notin L)) as [IHf2 IHt2].
    split.
    + intros y Hy. apply (IHf1 y). unfold open_tm_ty. rewrite fv_tm_open_ty. exact Hy.
    + intros X Hx.
      assert (H1 : In X (fresh L :: Delta0)).
      { destruct (ftv_tm_open_ty_persist body 0 (Ty_FVar (fresh L)) X Hx) as [H'|H'].
        - apply (IHt1 X). exact H'.
        - apply in_fv_ty_fvar in H'. rewrite H'. left. reflexivity. }
      assert (H2 : In X (fresh2 L :: Delta0)).
      { destruct (ftv_tm_open_ty_persist body 0 (Ty_FVar (fresh2 L)) X Hx) as [H'|H'].
        - apply (IHt2 X). exact H'.
        - apply in_fv_ty_fvar in H'. rewrite H'. left. reflexivity. }
      destruct H1 as [E1|E1]; destruct H2 as [E2|E2].
      * exfalso. apply (fresh2_neq L). transitivity X; auto.
      * exact E2.
      * exact E1.
      * exact E1.
  - simpl. split.
    + intros y Hy. apply (proj1 IH); auto.
    + intros X Hx. apply in_app_or in Hx as [Hx|Hx].
      * apply (proj2 IH); auto.
      * apply (wf_ty_fvty Delta0 U Hwf X Hx).
  - simpl. split; intros x Hx; destruct Hx.
  - simpl. split.
    + intros y Hy. apply in_app_or in Hy as [Hy|Hy].
      * apply (proj1 IH1); auto.
      * apply (proj1 IH2); auto.
    + intros X Hx. apply in_app_or in Hx as [Hx|Hx].
      * apply (proj2 IH1); auto.
      * apply (proj2 IH2); auto.
  - simpl. split.
    + intros y Hy. apply in_app_or in Hy as [Hy|Hy].
      * apply (proj1 IH1); auto.
      * apply (proj1 IH2); auto.
    + intros X Hx. apply in_app_or in Hx as [Hx|Hx].
      * apply (proj2 IH1); auto.
      * apply (proj2 IH2); auto.
  - pose proof (has_type_fv Delta0 (erase_context RGamma0) v T Hty) as [Hfv Hftv].
    simpl. split.
    + intros y Hy. destruct (Hfv y Hy) as [T0 H0].
      apply lookup_erase_context in H0. destruct H0 as [R0 H0]. exists R0. exact H0.
    + intros X Hx. apply (Hftv X Hx).
  - exact IH.
Qed.

(* ---------- rank of an rtype (ignores qualifiers and type structure) ---------- *)

Fixpoint rank (R : rty) : nat :=
  match R with
  | R_Refine _ _ => 0
  | R_Func R1 R2 => S (Nat.max (rank R1) (rank R2))
  | R_Exists R1 R2 => S (Nat.max (rank R1) (rank R2))
  | R_Poly R1 => S (rank R1)
  end.

Lemma rank_open_rty_tm : forall R k u, rank (open_rty_tm_rec k u R) = rank R.
Proof.
  intros R. induction R as [T ps|R1 IH1 R2 IH2|R1 IH1 R2 IH2|R1 IH1]; intros k u; simpl.
  - reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH1. reflexivity.
Qed.

Lemma rank_open_rty_ty : forall R k U, rank (open_rty_ty_rec k U R) = rank R.
Proof.
  intros R. induction R as [T ps|R1 IH1 R2 IH2|R1 IH1 R2 IH2|R1 IH1]; intros k U; simpl.
  - reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH1. reflexivity.
Qed.

Lemma rank_open_rty_tm0 : forall R u, rank (open_rty_tm R u) = rank R.
Proof. intros. apply rank_open_rty_tm. Qed.
Lemma rank_open_rty_ty0 : forall R U, rank (open_rty_ty R U) = rank R.
Proof. intros. apply rank_open_rty_ty. Qed.

Lemma rank_func_l : forall R1 R2, rank R1 < rank (R_Func R1 R2).
Proof. intros. simpl. lia. Qed.
Lemma rank_func_r : forall R1 R2, rank R2 < rank (R_Func R1 R2).
Proof. intros. simpl. lia. Qed.
Lemma rank_exists_l : forall R1 R2, rank R1 < rank (R_Exists R1 R2).
Proof. intros. simpl. lia. Qed.
Lemma rank_exists_r : forall R1 R2, rank R2 < rank (R_Exists R1 R2).
Proof. intros. simpl. lia. Qed.
Lemma rank_poly : forall R, rank R < rank (R_Poly R).
Proof. intros. simpl. lia. Qed.

(* ---------- fuel-indexed semantic value relation ---------- *)

Fixpoint Vf (fuel : nat) (R : rty) (v : tm) : Prop :=
  match fuel with
  | 0 => False
  | S f =>
      match R with
      | R_Refine T ps =>
          value v /\ fv_tm v = [] /\ ftv_tm v = [] /\ base_val T v /\
          predicate_holds (open_qualifier_tm ps v)
      | R_Func R1 R2 =>
          value v /\ fv_tm v = [] /\ ftv_tm v = [] /\
          (forall w, Vf f R1 w ->
             exists u, multi (tm_app v w) u /\ Vf f (open_rty_tm R2 w) u)
      | R_Exists R1 R2 =>
          value v /\ fv_tm v = [] /\ ftv_tm v = [] /\
          (exists w, Vf f R1 w /\ Vf f (open_rty_tm R2 w) v)
      | R_Poly R1 =>
          value v /\ fv_tm v = [] /\ ftv_tm v = [] /\
          (forall U, locally_closed_ty U -> fv_ty U = [] ->
             exists u, multi (tm_tapp v U) u /\ Vf f (open_rty_ty R1 U) u)
      end
  end.

Definition V (R : rty) (v : tm) : Prop := Vf (S (rank R)) R v.
Definition T (R : rty) (t : tm) : Prop := exists v, multi t v /\ V R v.

(* ---------- fuel irrelevance ---------- *)

Lemma Vf_irrel : forall f g R v, rank R < f -> rank R < g ->
  (Vf f R v <-> Vf g R v).
Proof.
  induction f as [|f' IH]; intros g R v Hf Hg.
  - inversion Hf.
  - destruct g as [|g']. { inversion Hg. }
    destruct R as [T ps|R1 R2|R1 R2|R1]; simpl in *.
    + simpl. tauto.
    + assert (Hr1f : rank R1 < f') by lia.
      assert (Hr1g : rank R1 < g') by lia.
      assert (Hr2f : rank R2 < f') by lia.
      assert (Hr2g : rank R2 < g') by lia.
      simpl. split.
      * intros (Hv & Hfv & Hftv & Hbody). repeat split; auto.
        intros w Hw.
        apply (proj2 (IH g' R1 w Hr1f Hr1g)) in Hw.
        destruct (Hbody w Hw) as [u [Hu1 Hu2]].
        exists u. split; auto.
        assert (Ho2f : rank (open_rty_tm R2 w) < f') by (rewrite rank_open_rty_tm0; auto).
        assert (Ho2g : rank (open_rty_tm R2 w) < g') by (rewrite rank_open_rty_tm0; auto).
        exact (proj1 (IH g' _ u Ho2f Ho2g) Hu2).
      * intros (Hv & Hfv & Hftv & Hbody). repeat split; auto.
        intros w Hw.
        apply (proj1 (IH g' R1 w Hr1f Hr1g)) in Hw.
        destruct (Hbody w Hw) as [u [Hu1 Hu2]].
        exists u. split; auto.
        assert (Ho2f : rank (open_rty_tm R2 w) < f') by (rewrite rank_open_rty_tm0; auto).
        assert (Ho2g : rank (open_rty_tm R2 w) < g') by (rewrite rank_open_rty_tm0; auto).
        exact (proj2 (IH g' _ u Ho2f Ho2g) Hu2).
    + assert (Hr1f : rank R1 < f') by lia.
      assert (Hr1g : rank R1 < g') by lia.
      assert (Hr2f : rank R2 < f') by lia.
      assert (Hr2g : rank R2 < g') by lia.
      simpl. split.
      * intros (Hv & Hfv & Hftv & [w [Hw1 Hw2]]). repeat split; auto.
        exists w. split.
        { exact (proj1 (IH g' R1 w Hr1f Hr1g) Hw1). }
        { assert (Ho2f : rank (open_rty_tm R2 w) < f') by (rewrite rank_open_rty_tm0; auto).
          assert (Ho2g : rank (open_rty_tm R2 w) < g') by (rewrite rank_open_rty_tm0; auto).
          exact (proj1 (IH g' _ v Ho2f Ho2g) Hw2). }
      * intros (Hv & Hfv & Hftv & [w [Hw1 Hw2]]). repeat split; auto.
        exists w. split.
        { exact (proj2 (IH g' R1 w Hr1f Hr1g) Hw1). }
        { assert (Ho2f : rank (open_rty_tm R2 w) < f') by (rewrite rank_open_rty_tm0; auto).
          assert (Ho2g : rank (open_rty_tm R2 w) < g') by (rewrite rank_open_rty_tm0; auto).
          exact (proj2 (IH g' _ v Ho2f Ho2g) Hw2). }
    + assert (Hr1f : rank R1 < f') by lia.
      assert (Hr1g : rank R1 < g') by lia.
      simpl. split.
      * intros (Hv & Hfv & Hftv & Hbody). repeat split; auto.
        intros U Hlc Hft.
        destruct (Hbody U Hlc Hft) as [u [Hu1 Hu2]].
        exists u. split; auto.
        assert (Ho1f : rank (open_rty_ty R1 U) < f') by (rewrite rank_open_rty_ty0; auto).
        assert (Ho1g : rank (open_rty_ty R1 U) < g') by (rewrite rank_open_rty_ty0; auto).
        exact (proj1 (IH g' _ u Ho1f Ho1g) Hu2).
      * intros (Hv & Hfv & Hftv & Hbody). repeat split; auto.
        intros U Hlc Hft.
        destruct (Hbody U Hlc Hft) as [u [Hu1 Hu2]].
        exists u. split; auto.
        assert (Ho1f : rank (open_rty_ty R1 U) < f') by (rewrite rank_open_rty_ty0; auto).
        assert (Ho1g : rank (open_rty_ty R1 U) < g') by (rewrite rank_open_rty_ty0; auto).
        exact (proj2 (IH g' _ u Ho1f Ho1g) Hu2).
Qed.

Lemma Vf_at : forall R v f, rank R < f -> (Vf f R v <-> V R v).
Proof.
  intros R v f H. unfold V. apply Vf_irrel.
  - auto.
  - lia.
Qed.

(* ---------- unfolding lemmas ---------- *)

Lemma Vf_Refine_unfold : forall f T ps v,
  Vf (S f) (R_Refine T ps) v <->
  value v /\ fv_tm v = [] /\ ftv_tm v = [] /\ base_val T v /\
  predicate_holds (open_qualifier_tm ps v).
Proof. intros. simpl. reflexivity. Qed.

Lemma Vf_Func_unfold : forall f R1 R2 v,
  Vf (S f) (R_Func R1 R2) v <->
  value v /\ fv_tm v = [] /\ ftv_tm v = [] /\
  (forall w, Vf f R1 w ->
     exists u, multi (tm_app v w) u /\ Vf f (open_rty_tm R2 w) u).
Proof. intros. simpl. reflexivity. Qed.

Lemma Vf_Exists_unfold : forall f R1 R2 v,
  Vf (S f) (R_Exists R1 R2) v <->
  value v /\ fv_tm v = [] /\ ftv_tm v = [] /\
  (exists w, Vf f R1 w /\ Vf f (open_rty_tm R2 w) v).
Proof. intros. simpl. reflexivity. Qed.

Lemma Vf_Poly_unfold : forall f R v,
  Vf (S f) (R_Poly R) v <->
  value v /\ fv_tm v = [] /\ ftv_tm v = [] /\
  (forall U, locally_closed_ty U -> fv_ty U = [] ->
     exists u, multi (tm_tapp v U) u /\ Vf f (open_rty_ty R U) u).
Proof. intros. simpl. reflexivity. Qed.

Lemma V_Refine : forall T ps v,
  V (R_Refine T ps) v <->
  value v /\ fv_tm v = [] /\ ftv_tm v = [] /\ base_val T v /\
  predicate_holds (open_qualifier_tm ps v).
Proof.
  intros. unfold V. rewrite Vf_Refine_unfold. reflexivity.
Qed.

Lemma V_Func : forall R1 R2 v,
  V (R_Func R1 R2) v <->
  value v /\ fv_tm v = [] /\ ftv_tm v = [] /\
  (forall w, V R1 w ->
     exists u, multi (tm_app v w) u /\ V (open_rty_tm R2 w) u).
Proof.
  intros. unfold V. rewrite Vf_Func_unfold.
  split; intros (Hv & Hfv & Hftv & Hbody); repeat split; auto.
  - intros w Hw.
    assert (Hw' : Vf (rank (R_Func R1 R2)) R1 w).
    { apply (proj2 (Vf_at R1 w (rank (R_Func R1 R2)) (rank_func_l R1 R2))). auto. }
    destruct (Hbody w Hw') as [u [Hu1 Hu2]].
    exists u. split; auto.
    assert (Ho2 : rank (open_rty_tm R2 w) < rank (R_Func R1 R2))
      by (rewrite rank_open_rty_tm0; apply rank_func_r).
    exact (proj1 (Vf_at (open_rty_tm R2 w) u (rank (R_Func R1 R2)) Ho2) Hu2).
  - intros w Hw.
    assert (Hw' : V R1 w).
    { exact (proj1 (Vf_at R1 w (rank (R_Func R1 R2)) (rank_func_l R1 R2)) Hw). }
    destruct (Hbody w Hw') as [u [Hu1 Hu2]].
    exists u. split; auto.
    assert (Ho2 : rank (open_rty_tm R2 w) < rank (R_Func R1 R2))
      by (rewrite rank_open_rty_tm0; apply rank_func_r).
    exact (proj2 (Vf_at (open_rty_tm R2 w) u (rank (R_Func R1 R2)) Ho2) Hu2).
Qed.

Lemma V_Exists : forall R1 R2 v,
  V (R_Exists R1 R2) v <->
  value v /\ fv_tm v = [] /\ ftv_tm v = [] /\
  (exists w, V R1 w /\ V (open_rty_tm R2 w) v).
Proof.
  intros. unfold V. rewrite Vf_Exists_unfold.
  split; intros (Hv & Hfv & Hftv & Hbody).
  - repeat split; auto. destruct Hbody as [w [Hw1 Hw2]]. exists w. split.
    + apply (proj1 (Vf_at R1 w (rank (R_Exists R1 R2)) (rank_exists_l R1 R2))). auto.
    + assert (Ho2 : rank (open_rty_tm R2 w) < rank (R_Exists R1 R2))
        by (rewrite rank_open_rty_tm0; apply rank_exists_r).
      exact (proj1 (Vf_at (open_rty_tm R2 w) v (rank (R_Exists R1 R2)) Ho2) Hw2).
  - repeat split; auto. destruct Hbody as [w [Hw1 Hw2]]. exists w. split.
    + apply (proj2 (Vf_at R1 w (rank (R_Exists R1 R2)) (rank_exists_l R1 R2))). auto.
    + assert (Ho2 : rank (open_rty_tm R2 w) < rank (R_Exists R1 R2))
        by (rewrite rank_open_rty_tm0; apply rank_exists_r).
      exact (proj2 (Vf_at (open_rty_tm R2 w) v (rank (R_Exists R1 R2)) Ho2) Hw2).
Qed.

Lemma V_Poly : forall R v,
  V (R_Poly R) v <->
  value v /\ fv_tm v = [] /\ ftv_tm v = [] /\
  (forall U, locally_closed_ty U -> fv_ty U = [] ->
     exists u, multi (tm_tapp v U) u /\ V (open_rty_ty R U) u).
Proof.
  intros. unfold V. rewrite Vf_Poly_unfold.
  split; intros (Hv & Hfv & Hftv & Hbody); repeat split; auto.
  - intros U Hlc Hft.
    destruct (Hbody U Hlc Hft) as [u [Hu1 Hu2]].
    exists u. split; auto.
    assert (Ho1 : rank (open_rty_ty R U) < rank (R_Poly R))
      by (rewrite rank_open_rty_ty0; apply rank_poly).
    exact (proj1 (Vf_at (open_rty_ty R U) u (rank (R_Poly R)) Ho1) Hu2).
  - intros U Hlc Hft.
    destruct (Hbody U Hlc Hft) as [u [Hu1 Hu2]].
    exists u. split; auto.
    assert (Ho1 : rank (open_rty_ty R U) < rank (R_Poly R))
      by (rewrite rank_open_rty_ty0; apply rank_poly).
    exact (proj2 (Vf_at (open_rty_ty R U) u (rank (R_Poly R)) Ho1) Hu2).
Qed.

Lemma T_unfold : forall R t, T R t <-> exists v, multi t v /\ V R v.
Proof. intros. reflexivity. Qed.

(* ---------- basic projections ---------- *)

Lemma V_value : forall R v, V R v -> value v.
Proof.
  intros R v H. destruct R as [T ps|R1 R2|R1 R2|R1].
  - rewrite V_Refine in H. tauto.
  - rewrite V_Func in H. tauto.
  - rewrite V_Exists in H. tauto.
  - rewrite V_Poly in H. tauto.
Qed.

Lemma V_fv : forall R v, V R v -> fv_tm v = [].
Proof.
  intros R v H. destruct R as [T ps|R1 R2|R1 R2|R1].
  - rewrite V_Refine in H. tauto.
  - rewrite V_Func in H. tauto.
  - rewrite V_Exists in H. tauto.
  - rewrite V_Poly in H. tauto.
Qed.

Lemma V_ftv : forall R v, V R v -> ftv_tm v = [].
Proof.
  intros R v H. destruct R as [T ps|R1 R2|R1 R2|R1].
  - rewrite V_Refine in H. tauto.
  - rewrite V_Func in H. tauto.
  - rewrite V_Exists in H. tauto.
  - rewrite V_Poly in H. tauto.
Qed.

Lemma V_lc : forall R v, V R v -> locally_closed_tm v.
Proof. intros R v H. apply value_lc. apply (V_value R v). auto. Qed.
Lemma not_in_app : forall (A : Type) (x : A) (l1 l2 : list A),
  ~ In x (l1 ++ l2) -> ~ In x l1 /\ ~ In x l2.
Proof.
  intros A x l1 l2 H. split; intros Hc; apply H; apply in_app_iff; auto.
Qed.


(* ---------- environments ---------- *)

Definition env_good (sigma : atom -> tm) : Prop :=
  forall x, value (sigma x) /\ fv_tm (sigma x) = [] /\ ftv_tm (sigma x) = [].

Definition tenv_good (tau : atom -> ty) : Prop :=
  forall X, locally_closed_ty (tau X) /\ fv_ty (tau X) = [].

Definition satisfies_context (sigma : atom -> tm) (tau : atom -> ty) (RGamma : rcontext) : Prop :=
  forall x R, lookup_rcontext x RGamma = Some R -> V (close_rty sigma tau R) (sigma x).

Definition upd_tm (sigma : atom -> tm) (x : atom) (w : tm) : atom -> tm :=
  fun y => if Nat.eqb y x then w else sigma y.

Definition upd_ty (tau : atom -> ty) (X : atom) (U : ty) : atom -> ty :=
  fun Y => if Nat.eqb Y X then U else tau Y.

Lemma upd_tm_eq : forall sigma x w, upd_tm sigma x w x = w.
Proof. intros. unfold upd_tm. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma upd_tm_neq : forall sigma x w y, y <> x -> upd_tm sigma x w y = sigma y.
Proof. intros. unfold upd_tm. destruct (Nat.eqb y x) eqn:E. apply Nat.eqb_eq in E. exfalso. auto. reflexivity. Qed.

Lemma upd_ty_eq : forall tau X U, upd_ty tau X U X = U.
Proof. intros. unfold upd_ty. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma upd_ty_neq : forall tau X U Y, Y <> X -> upd_ty tau X U Y = tau Y.
Proof. intros. unfold upd_ty. destruct (Nat.eqb Y X) eqn:E. apply Nat.eqb_eq in E. exfalso. auto. reflexivity. Qed.

Lemma env_good_lc : forall sigma, env_good sigma -> forall x, lc_tm_at 0 0 (sigma x).
Proof. intros sigma H x. apply value_lc. apply H. Qed.

Lemma env_good_fv : forall sigma, env_good sigma -> forall x, fv_tm (sigma x) = [].
Proof. intros sigma H x. apply H. Qed.

Lemma env_good_ftv : forall sigma, env_good sigma -> forall x, ftv_tm (sigma x) = [].
Proof. intros sigma H x. apply H. Qed.

Lemma env_good_value : forall sigma, env_good sigma -> forall x, value (sigma x).
Proof. intros sigma H x. apply H. Qed.

Lemma tenv_good_lc : forall tau, tenv_good tau -> forall X, lc_ty_at 0 (tau X).
Proof. intros tau H X. apply H. Qed.

Lemma tenv_good_fv : forall tau, tenv_good tau -> forall X, fv_ty (tau X) = [].
Proof. intros tau H X. apply H. Qed.

Lemma env_good_upd : forall sigma x w, env_good sigma -> value w -> fv_tm w = [] -> ftv_tm w = [] ->
  env_good (upd_tm sigma x w).
Proof.
  intros sigma x w H Hg Hfv Hftv y. unfold upd_tm.
  destruct (Nat.eqb y x) eqn:E; auto.
Qed.

Lemma tenv_good_upd : forall tau X U, tenv_good tau -> locally_closed_ty U -> fv_ty U = [] ->
  tenv_good (upd_ty tau X U).
Proof.
  intros tau X U H Hlc Hfv Y. unfold upd_ty.
  destruct (Nat.eqb Y X) eqn:E; auto.
Qed.

(* ---------- agreement lemmas for environments ---------- *)

Lemma tsubst_tm_absent : forall t sigma x w, ~ In x (fv_tm t) ->
  tsubst_tm (upd_tm sigma x w) t = tsubst_tm sigma t.
Proof.
  induction t as [i|y|T t1 IH1|t1 IH1 t2 IH2|t1 IH1|t1 IH1 T|n|t1 IH1 t2 IH2|op t1 IH1 t2 IH2];
    intros sigma x w H; simpl in *.
  - reflexivity.
  - apply upd_tm_neq. intros E. subst. apply H. auto.
  - rewrite (IH1 sigma x w H). reflexivity.
  - apply not_in_app in H as [H1 H2]. rewrite (IH1 sigma x w H1), (IH2 sigma x w H2). reflexivity.
  - rewrite (IH1 sigma x w H). reflexivity.
  - rewrite (IH1 sigma x w H). reflexivity.
  - reflexivity.
  - apply not_in_app in H as [H1 H2]. rewrite (IH1 sigma x w H1), (IH2 sigma x w H2). reflexivity.
  - apply not_in_app in H as [H1 H2]. rewrite (IH1 sigma x w H1), (IH2 sigma x w H2). reflexivity.
Qed.

Lemma tsubst_qual_absent : forall p sigma x w, ~ In x (fv_qual p) ->
  tsubst_qual (upd_tm sigma x w) p = tsubst_qual sigma p.
Proof.
  induction p as [| |t1 t2|t1 t2|t1 t2|p1 IH1 p2 IH2|p1 IH1 p2 IH2|p1 IH1];
    intros sigma x w H; simpl in *.
  - reflexivity. - reflexivity.
  - apply not_in_app in H as [H1 H2]. rewrite (tsubst_tm_absent _ _ _ _ H1), (tsubst_tm_absent _ _ _ _ H2). reflexivity.
  - apply not_in_app in H as [H1 H2]. rewrite (tsubst_tm_absent _ _ _ _ H1), (tsubst_tm_absent _ _ _ _ H2). reflexivity.
  - apply not_in_app in H as [H1 H2]. rewrite (tsubst_tm_absent _ _ _ _ H1), (tsubst_tm_absent _ _ _ _ H2). reflexivity.
  - apply not_in_app in H as [H1 H2]. rewrite (IH1 sigma x w H1), (IH2 sigma x w H2). reflexivity.
  - apply not_in_app in H as [H1 H2]. rewrite (IH1 sigma x w H1), (IH2 sigma x w H2). reflexivity.
  - rewrite (IH1 sigma x w H). reflexivity.
Qed.

Lemma tsubst_rty_absent : forall R sigma x w, ~ In x (fv_rty R) ->
  tsubst_rty (upd_tm sigma x w) R = tsubst_rty sigma R.
Proof.
  induction R as [T ps|R1 IH1 R2 IH2|R1 IH1 R2 IH2|R1 IH1]; intros sigma x w H; simpl in *.
  - rewrite (tsubst_qual_absent ps sigma x w H). reflexivity.
  - apply not_in_app in H as [H1 H2]. rewrite (IH1 sigma x w H1), (IH2 sigma x w H2). reflexivity.
  - apply not_in_app in H as [H1 H2]. rewrite (IH1 sigma x w H1), (IH2 sigma x w H2). reflexivity.
  - rewrite (IH1 sigma x w H). reflexivity.
Qed.

Lemma tysubst_ty_absent : forall T tau X U, ~ In X (fv_ty T) ->
  tysubst_ty (upd_ty tau X U) T = tysubst_ty tau T.
Proof.
  intros T tau X U. revert tau X U.
  induction T as [i|Y|T1 IH1 T2 IH2|T1 IH1|]; intros tau X U H; simpl in *.
  - reflexivity.
  - apply upd_ty_neq. intros E. subst. apply H. auto.
  - apply not_in_app in H as [H1 H2]. rewrite (IH1 tau X U H1), (IH2 tau X U H2). reflexivity.
  - rewrite (IH1 tau X U H). reflexivity.
  - reflexivity.
Qed.

Lemma tysubst_tm_absent : forall t tau X U, ~ In X (ftv_tm t) ->
  tysubst_tm (upd_ty tau X U) t = tysubst_tm tau t.
Proof.
  induction t as [i|y|T t1 IH1|t1 IH1 t2 IH2|t1 IH1|t1 IH1 T|n|t1 IH1 t2 IH2|op t1 IH1 t2 IH2];
    intros tau X U H; simpl in *.
  - reflexivity. - reflexivity.
  - apply not_in_app in H as [H1 H2].
    rewrite (tysubst_ty_absent T tau X U H1), (IH1 tau X U H2). reflexivity.
  - apply not_in_app in H as [H1 H2]. rewrite (IH1 tau X U H1), (IH2 tau X U H2). reflexivity.
  - rewrite (IH1 tau X U H). reflexivity.
  - apply not_in_app in H as [H1 H2].
    rewrite (IH1 tau X U H1), (tysubst_ty_absent T tau X U H2). reflexivity.
  - reflexivity.
  - apply not_in_app in H as [H1 H2]. rewrite (IH1 tau X U H1), (IH2 tau X U H2). reflexivity.
  - apply not_in_app in H as [H1 H2]. rewrite (IH1 tau X U H1), (IH2 tau X U H2). reflexivity.
Qed.

Lemma tysubst_qual_absent : forall p tau X U, ~ In X (ftv_qual p) ->
  tysubst_qual (upd_ty tau X U) p = tysubst_qual tau p.
Proof.
  induction p as [| |t1 t2|t1 t2|t1 t2|p1 IH1 p2 IH2|p1 IH1 p2 IH2|p1 IH1];
    intros tau X U H; simpl in *.
  - reflexivity. - reflexivity.
  - apply not_in_app in H as [H1 H2]. rewrite (tysubst_tm_absent _ _ _ _ H1), (tysubst_tm_absent _ _ _ _ H2). reflexivity.
  - apply not_in_app in H as [H1 H2]. rewrite (tysubst_tm_absent _ _ _ _ H1), (tysubst_tm_absent _ _ _ _ H2). reflexivity.
  - apply not_in_app in H as [H1 H2]. rewrite (tysubst_tm_absent _ _ _ _ H1), (tysubst_tm_absent _ _ _ _ H2). reflexivity.
  - apply not_in_app in H as [H1 H2]. rewrite (IH1 tau X U H1), (IH2 tau X U H2). reflexivity.
  - apply not_in_app in H as [H1 H2]. rewrite (IH1 tau X U H1), (IH2 tau X U H2). reflexivity.
  - rewrite (IH1 tau X U H). reflexivity.
Qed.

Lemma tysubst_rty_absent : forall R tau X U, ~ In X (ftv_rty R) ->
  tysubst_rty (upd_ty tau X U) R = tysubst_rty tau R.
Proof.
  induction R as [T ps|R1 IH1 R2 IH2|R1 IH1 R2 IH2|R1 IH1]; intros tau X U H; simpl in *.
  - apply not_in_app in H as [H1 H2].
    rewrite (tysubst_ty_absent T tau X U H1), (tysubst_qual_absent ps tau X U H2). reflexivity.
  - apply not_in_app in H as [H1 H2]. rewrite (IH1 tau X U H1), (IH2 tau X U H2). reflexivity.
  - apply not_in_app in H as [H1 H2]. rewrite (IH1 tau X U H1), (IH2 tau X U H2). reflexivity.
  - rewrite (IH1 tau X U H). reflexivity.
Qed.

(* free type variables are unchanged by term substitution of type-closed terms *)
Lemma ftv_qual_tsubst : forall p sigma, (forall x, ftv_tm (sigma x) = []) ->
  ftv_qual (tsubst_qual sigma p) = ftv_qual p.
Proof.
  induction p as [| |t1 t2|t1 t2|t1 t2|p1 IH1 p2 IH2|p1 IH1 p2 IH2|p1 IH1];
    intros sigma H; simpl.
  - reflexivity. - reflexivity.
  - rewrite !ftv_tm_tsubst; auto.
  - rewrite !ftv_tm_tsubst; auto.
  - rewrite !ftv_tm_tsubst; auto.
  - rewrite IH1; auto. rewrite IH2; auto.
  - rewrite IH1; auto. rewrite IH2; auto.
  - rewrite IH1; auto.
Qed.

Lemma ftv_rty_tsubst : forall R sigma, (forall x, ftv_tm (sigma x) = []) ->
  ftv_rty (tsubst_rty sigma R) = ftv_rty R.
Proof.
  induction R as [T ps|R1 IH1 R2 IH2|R1 IH1 R2 IH2|R1 IH1]; intros sigma H; simpl.
  - rewrite ftv_qual_tsubst; auto.
  - rewrite IH1; auto. rewrite IH2; auto.
  - rewrite IH1; auto. rewrite IH2; auto.
  - rewrite IH1; auto.
Qed.

(* close versions *)
Lemma close_tm_absent : forall t sigma tau x w, ~ In x (fv_tm t) ->
  close_tm (upd_tm sigma x w) tau t = close_tm sigma tau t.
Proof.
  intros. unfold close_tm. rewrite tsubst_tm_absent; auto.
Qed.

Lemma close_qual_absent : forall p sigma tau x w, ~ In x (fv_qual p) ->
  close_qual (upd_tm sigma x w) tau p = close_qual sigma tau p.
Proof.
  intros. unfold close_qual. rewrite tsubst_qual_absent; auto.
Qed.

Lemma close_rty_absent : forall R sigma tau x w, ~ In x (fv_rty R) ->
  close_rty (upd_tm sigma x w) tau R = close_rty sigma tau R.
Proof.
  intros. unfold close_rty. rewrite tsubst_rty_absent; auto.
Qed.

Lemma close_tm_absent_ty : forall t sigma tau X U,
  (forall x, ftv_tm (sigma x) = []) -> ~ In X (ftv_tm t) ->
  close_tm sigma (upd_ty tau X U) t = close_tm sigma tau t.
Proof.
  intros t sigma tau X U Hsig HX. unfold close_tm.
  rewrite (tysubst_tm_absent (tsubst_tm sigma t) tau X U).
  - reflexivity.
  - rewrite ftv_tm_tsubst; auto.
Qed.

Lemma close_qual_absent_ty : forall p sigma tau X U,
  (forall x, ftv_tm (sigma x) = []) -> ~ In X (ftv_qual p) ->
  close_qual sigma (upd_ty tau X U) p = close_qual sigma tau p.
Proof.
  intros p sigma tau X U Hsig HX. unfold close_qual.
  rewrite (tysubst_qual_absent (tsubst_qual sigma p) tau X U).
  - reflexivity.
  - rewrite ftv_qual_tsubst; auto.
Qed.

Lemma close_rty_absent_ty : forall R sigma tau X U,
  (forall x, ftv_tm (sigma x) = []) -> ~ In X (ftv_rty R) ->
  close_rty sigma (upd_ty tau X U) R = close_rty sigma tau R.
Proof.
  intros R sigma tau X U Hsig HX. unfold close_rty.
  rewrite (tysubst_rty_absent (tsubst_rty sigma R) tau X U).
  - reflexivity.
  - rewrite ftv_rty_tsubst; auto.
Qed.

(* close of a variable *)
Lemma close_tm_fvar : forall sigma tau x, ftv_tm (sigma x) = [] ->
  close_tm sigma tau (tm_fvar x) = sigma x.
Proof.
  intros. unfold close_tm. simpl. apply tysubst_tm_id. auto.
Qed.

Lemma close_ty_fvar : forall tau X, close_ty tau (Ty_FVar X) = tau X.
Proof. intros. reflexivity. Qed.

(* close of a fully closed term *)
Lemma close_tm_of_closed : forall sigma tau t, fv_tm t = [] -> ftv_tm t = [] ->
  close_tm sigma tau t = t.
Proof. intros. apply close_tm_id; auto. Qed.

Lemma predicate_closed_fv : forall p, predicate_closed p -> fv_qual p = [].
Proof.
  induction p as [| |t1 t2|t1 t2|t1 t2|p1 IH1 p2 IH2|p1 IH1 p2 IH2|p1 IH1]; simpl; intros H.
  - reflexivity.
  - reflexivity.
  - destruct H as (H1 & H2 & H3 & H4 & H5 & H6). rewrite H2, H5. reflexivity.
  - destruct H as (H1 & H2 & H3 & H4 & H5 & H6). rewrite H2, H5. reflexivity.
  - destruct H as (H1 & H2 & H3 & H4 & H5 & H6). rewrite H2, H5. reflexivity.
  - destruct H as [H1 H2]. rewrite (IH1 H1), (IH2 H2). reflexivity.
  - destruct H as [H1 H2]. rewrite (IH1 H1), (IH2 H2). reflexivity.
  - apply IH1. auto.
Qed.

Lemma predicate_closed_ftv : forall p, predicate_closed p -> ftv_qual p = [].
Proof.
  induction p as [| |t1 t2|t1 t2|t1 t2|p1 IH1 p2 IH2|p1 IH1 p2 IH2|p1 IH1]; simpl; intros H.
  - reflexivity.
  - reflexivity.
  - destruct H as (H1 & H2 & H3 & H4 & H5 & H6). rewrite H3, H6. reflexivity.
  - destruct H as (H1 & H2 & H3 & H4 & H5 & H6). rewrite H3, H6. reflexivity.
  - destruct H as (H1 & H2 & H3 & H4 & H5 & H6). rewrite H3, H6. reflexivity.
  - destruct H as [H1 H2]. rewrite (IH1 H1), (IH2 H2). reflexivity.
  - destruct H as [H1 H2]. rewrite (IH1 H1), (IH2 H2). reflexivity.
  - apply IH1. auto.
Qed.

Lemma close_qual_of_closed : forall sigma tau p, predicate_closed p ->
  close_qual sigma tau p = p.
Proof.
  intros. apply close_qual_id.
  - apply predicate_closed_fv; auto.
  - apply predicate_closed_ftv; auto.
Qed.

(* values and closure under close *)
Lemma close_tm_value : forall sigma tau v, env_good sigma -> tenv_good tau -> value v ->
  value (close_tm sigma tau v).
Proof.
  intros sigma tau v Hg Ht Hv.
  apply (value_close v Hv sigma tau).
  - intros x. apply value_lc. apply env_good_value; auto.
  - intros X. apply tenv_good_lc; auto.
Qed.

Lemma close_tm_fv_nil : forall sigma tau t, env_good sigma -> fv_tm (close_tm sigma tau t) = [].
Proof.
  intros. apply fv_tm_close. intros x. apply env_good_fv; auto.
Qed.

Lemma close_tm_ftv_nil : forall sigma tau t, env_good sigma -> tenv_good tau ->
  ftv_tm (close_tm sigma tau t) = [].
Proof.
  intros. apply ftv_tm_close.
  - intros x. apply env_good_ftv; auto.
  - intros X. apply tenv_good_fv; auto.
Qed.

Lemma close_tm_lc_at : forall sigma tau t K k, env_good sigma -> tenv_good tau ->
  lc_tm_at K k t -> lc_tm_at K k (close_tm sigma tau t).
Proof.
  intros sigma tau t K k Hg Ht Hlc. apply lc_tm_close.
  - exact Hlc.
  - intros x. apply env_good_lc; auto.
  - intros X. apply tenv_good_lc; auto.
Qed.

(* the key identities used in the abstraction case *)
Lemma close_tm_open_fvar : forall sigma tau body x w,
  env_good sigma -> tenv_good tau -> value w -> fv_tm w = [] -> ftv_tm w = [] ->
  ~ In x (fv_tm body) ->
  close_tm (upd_tm sigma x w) tau (open_tm body (tm_fvar x)) =
  open_tm (close_tm sigma tau body) w.
Proof.
  intros sigma tau body x w Hg Ht Hw Hfw Hftw Hx.
  assert (Heq : close_tm (upd_tm sigma x w) tau (open_tm body (tm_fvar x)) =
                open_tm (close_tm (upd_tm sigma x w) tau body)
                        (close_tm (upd_tm sigma x w) tau (tm_fvar x))).
  { apply close_tm_open.
    - intros y. apply env_good_lc. apply env_good_upd; auto.
    - intros X. apply tenv_good_lc; auto. }
  rewrite Heq. rewrite (close_tm_absent body sigma tau x w Hx). rewrite close_tm_fvar.
  - rewrite upd_tm_eq. reflexivity.
  - rewrite upd_tm_eq. apply Hftw.
Qed.

Lemma close_rty_open_fvar : forall sigma tau R x w,
  env_good sigma -> tenv_good tau -> value w -> fv_tm w = [] -> ftv_tm w = [] ->
  ~ In x (fv_rty R) ->
  close_rty (upd_tm sigma x w) tau (open_rty_tm R (tm_fvar x)) =
  open_rty_tm (close_rty sigma tau R) w.
Proof.
  intros sigma tau R x w Hg Ht Hw Hfw Hftw Hx.
  assert (Heq : close_rty (upd_tm sigma x w) tau (open_rty_tm R (tm_fvar x)) =
                open_rty_tm (close_rty (upd_tm sigma x w) tau R)
                            (close_tm (upd_tm sigma x w) tau (tm_fvar x))).
  { apply close_rty_open_tm.
    - intros y. apply env_good_lc. apply env_good_upd; auto.
    - intros X. apply tenv_good_lc; auto. }
  rewrite Heq. rewrite (close_rty_absent R sigma tau x w Hx). rewrite close_tm_fvar.
  - rewrite upd_tm_eq. reflexivity.
  - rewrite upd_tm_eq. apply Hftw.
Qed.

Lemma close_tm_open_ty_fvar : forall sigma tau t X U,
  env_good sigma -> tenv_good tau -> locally_closed_ty U -> fv_ty U = [] ->
  ~ In X (ftv_tm t) ->
  close_tm sigma (upd_ty tau X U) (open_tm_ty t (Ty_FVar X)) =
  open_tm_ty (close_tm sigma tau t) U.
Proof.
  intros sigma tau t X U Hg Ht Hlc Hfv HX.
  assert (Heq : close_tm sigma (upd_ty tau X U) (open_tm_ty t (Ty_FVar X)) =
                open_tm_ty (close_tm sigma (upd_ty tau X U) t) (close_ty (upd_ty tau X U) (Ty_FVar X))).
  { apply close_tm_open_ty.
    - intros x. apply env_good_lc; auto.
    - intros Y. unfold upd_ty. destruct (Nat.eqb Y X) eqn:E.
      + apply Nat.eqb_eq in E. subst. auto.
      + apply tenv_good_lc; auto. }
  rewrite Heq.
  rewrite (close_tm_absent_ty t sigma tau X U ltac:(apply env_good_ftv; auto) HX).
  rewrite close_ty_fvar, upd_ty_eq. reflexivity.
Qed.

Lemma close_rty_open_ty_fvar : forall sigma tau R X U,
  env_good sigma -> tenv_good tau -> locally_closed_ty U -> fv_ty U = [] ->
  ~ In X (ftv_rty R) ->
  close_rty sigma (upd_ty tau X U) (open_rty_ty R (Ty_FVar X)) =
  open_rty_ty (close_rty sigma tau R) U.
Proof.
  intros sigma tau R X U Hg Ht Hlc Hfv HX.
  assert (Heq : close_rty sigma (upd_ty tau X U) (open_rty_ty R (Ty_FVar X)) =
                open_rty_ty (close_rty sigma (upd_ty tau X U) R) (close_ty (upd_ty tau X U) (Ty_FVar X))).
  { apply close_rty_open_ty.
    - intros x. apply env_good_lc; auto.
    - intros Y. unfold upd_ty. destruct (Nat.eqb Y X) eqn:E.
      + apply Nat.eqb_eq in E. subst. auto.
      + apply tenv_good_lc; auto. }
  rewrite Heq.
  rewrite (close_rty_absent_ty R sigma tau X U ltac:(apply env_good_ftv; auto) HX).
  rewrite close_ty_fvar, upd_ty_eq. reflexivity.
Qed.

(* ---------- unfolding lemmas for the operational semantics of qualifiers ---------- *)

Lemma holds_true : predicate_holds Pred_True.
Proof. unfold predicate_holds, interpret_qualifier. cbn. exact I. Qed.

Lemma holds_false : predicate_holds Pred_False <-> False.
Proof. unfold predicate_holds, interpret_qualifier, operational_atoms. cbn. tauto. Qed.

Lemma holds_and : forall p q, predicate_holds (Pred_And p q) <->
  (predicate_holds p /\ predicate_holds q).
Proof. intros. unfold predicate_holds, interpret_qualifier, operational_atoms. cbn. tauto. Qed.

Lemma holds_or : forall p q, predicate_holds (Pred_Or p q) <->
  (predicate_holds p \/ predicate_holds q).
Proof. intros. unfold predicate_holds, interpret_qualifier, operational_atoms. cbn. tauto. Qed.

Lemma holds_not : forall p, predicate_holds (Pred_Not p) <-> ~ predicate_holds p.
Proof. intros. unfold predicate_holds, interpret_qualifier, operational_atoms. cbn. tauto. Qed.

Lemma holds_eq : forall t1 t2, predicate_holds (Pred_Eq t1 t2) <->
  (exists v, predicate_multistep t1 v /\ predicate_multistep t2 v /\ value v).
Proof. intros. unfold predicate_holds, interpret_qualifier, operational_atoms. cbn. tauto. Qed.

Lemma holds_lt : forall t1 t2, predicate_holds (Pred_Lt t1 t2) <->
  (exists n1 n2, predicate_multistep t1 (tm_int n1) /\ predicate_multistep t2 (tm_int n2) /\ (n1 < n2)%Z).
Proof. intros. unfold predicate_holds, interpret_qualifier, operational_atoms. cbn. tauto. Qed.

Lemma holds_le : forall t1 t2, predicate_holds (Pred_Le t1 t2) <->
  (exists n1 n2, predicate_multistep t1 (tm_int n1) /\ predicate_multistep t2 (tm_int n2) /\ (n1 <= n2)%Z).
Proof. intros. unfold predicate_holds, interpret_qualifier, operational_atoms. cbn. tauto. Qed.

Lemma close_qual_true : forall sigma tau, close_qual sigma tau Pred_True = Pred_True.
Proof. intros. unfold close_qual. reflexivity. Qed.
Lemma close_qual_false : forall sigma tau, close_qual sigma tau Pred_False = Pred_False.
Proof. intros. unfold close_qual. reflexivity. Qed.
Lemma close_qual_eq : forall sigma tau t1 t2,
  close_qual sigma tau (Pred_Eq t1 t2) = Pred_Eq (close_tm sigma tau t1) (close_tm sigma tau t2).
Proof. intros. unfold close_qual, close_tm. reflexivity. Qed.
Lemma close_qual_lt : forall sigma tau t1 t2,
  close_qual sigma tau (Pred_Lt t1 t2) = Pred_Lt (close_tm sigma tau t1) (close_tm sigma tau t2).
Proof. intros. unfold close_qual, close_tm. reflexivity. Qed.
Lemma close_qual_le : forall sigma tau t1 t2,
  close_qual sigma tau (Pred_Le t1 t2) = Pred_Le (close_tm sigma tau t1) (close_tm sigma tau t2).
Proof. intros. unfold close_qual, close_tm. reflexivity. Qed.
Lemma close_qual_and : forall sigma tau p q,
  close_qual sigma tau (Pred_And p q) = Pred_And (close_qual sigma tau p) (close_qual sigma tau q).
Proof. intros. unfold close_qual. reflexivity. Qed.
Lemma close_qual_or : forall sigma tau p q,
  close_qual sigma tau (Pred_Or p q) = Pred_Or (close_qual sigma tau p) (close_qual sigma tau q).
Proof. intros. unfold close_qual. reflexivity. Qed.
Lemma close_qual_not : forall sigma tau p,
  close_qual sigma tau (Pred_Not p) = Pred_Not (close_qual sigma tau p).
Proof. intros. unfold close_qual. reflexivity. Qed.

(* ---------- soundness of entailment w.r.t. the operational interpretation ---------- *)

Lemma close_qual_open_fvar : forall sigma tau p x,
  env_good sigma -> tenv_good tau ->
  close_qual sigma tau (open_qualifier_tm p (tm_fvar x)) =
  open_qualifier_tm (close_qual sigma tau p) (sigma x).
Proof.
  intros sigma tau p x Hg Ht.
  assert (Hq : close_qual sigma tau (open_qualifier_tm p (tm_fvar x)) =
               open_qualifier_tm (close_qual sigma tau p) (close_tm sigma tau (tm_fvar x))).
  { apply close_qual_open_tm.
    - intros y. apply value_lc. apply env_good_value; auto.
    - intros X. apply tenv_good_lc; auto. }
  rewrite Hq. rewrite close_tm_fvar.
  - reflexivity.
  - apply env_good_ftv; auto.
Qed.

Lemma entails_sound : forall Delta RGamma p q, entails Delta RGamma p q ->
  forall sigma tau, env_good sigma -> tenv_good tau -> satisfies_context sigma tau RGamma ->
  predicate_holds (close_qual sigma tau p) -> predicate_holds (close_qual sigma tau q).
Proof.
  intros Delta RGamma p q H. induction H as [Delta0 RGamma0 ps|Delta0 RGamma0 ps
    |Delta0 RGamma0 ps qs rs H1 IH1 H2 IH2|Delta0 RGamma0 p0 q0|Delta0 RGamma0 p0 q0
    |Delta0 RGamma0 ps p0 qs H1 IH1 H2 IH2|Delta0 RGamma0 p0 q0|Delta0 RGamma0 p0 q0
    |Delta0 RGamma0 p0 q0 r H1 IH1 H2 IH2|Delta0 RGamma0 p0 q0 H1 IH1|Delta0 RGamma0 p0
    |Delta0 RGamma0 x T p0 q0 Hlk|Delta0 RGamma0 q0];
    intros sigma tau Hg Ht Hctx Hp.
  - exact Hp.
  - rewrite close_qual_true. apply holds_true.
  - apply (IH2 sigma tau Hg Ht Hctx). apply (IH1 sigma tau Hg Ht Hctx Hp).
  - rewrite close_qual_and in Hp. rewrite holds_and in Hp. exact (proj1 Hp).
  - rewrite close_qual_and in Hp. rewrite holds_and in Hp. exact (proj2 Hp).
  - rewrite close_qual_and. rewrite holds_and. split.
    + apply (IH1 sigma tau Hg Ht Hctx Hp).
    + apply (IH2 sigma tau Hg Ht Hctx Hp).
  - rewrite close_qual_or. rewrite holds_or. left. exact Hp.
  - rewrite close_qual_or. rewrite holds_or. right. exact Hp.
  - rewrite close_qual_or in Hp. rewrite holds_or in Hp. destruct Hp as [Hp|Hp].
    + apply (IH1 sigma tau Hg Ht Hctx Hp).
    + apply (IH2 sigma tau Hg Ht Hctx Hp).
  - rewrite close_qual_not. rewrite holds_not. intros Hq.
    apply (IH1 sigma tau Hg Ht Hctx). rewrite close_qual_and, holds_and. split; auto.
  - rewrite close_qual_false. rewrite holds_false.
    rewrite close_qual_and in Hp. rewrite holds_and in Hp.
    rewrite close_qual_not in Hp. rewrite holds_not in Hp.
    destruct Hp as [H1 H2]. exact (H2 H1).
  - pose proof (Hctx x (R_Refine T p0) Hlk) as HV.
    change (V (R_Refine (close_ty tau T) (close_qual sigma tau p0)) (sigma x)) in HV.
    rewrite V_Refine in HV.
    destruct HV as (_ & _ & _ & _ & HV).
    rewrite close_qual_open_fvar; auto.
  - rewrite close_qual_false in Hp. rewrite holds_false in Hp. destruct Hp.
Qed.

(* ---------- multi-step congruence ---------- *)

Lemma multi_trans : forall t1 t2 t3, multi t1 t2 -> multi t2 t3 -> multi t1 t3.
Proof.
  intros t1 t2 t3 H. induction H as [u|a b c Hstep Hm IH]; intros H23.
  - exact H23.
  - apply multi_step with (t2 := b); auto.
Qed.

Lemma multi_app_l : forall t1 t1' t2, multi t1 t1' -> locally_closed_tm t2 ->
  multi (tm_app t1 t2) (tm_app t1' t2).
Proof.
  intros t1 t1' t2 H. induction H as [u|a b c Hstep Hm IH]; intros Hlc.
  - apply multi_refl.
  - apply multi_step with (t2 := tm_app b t2); auto. apply ST_App1; auto.
Qed.

Lemma multi_app_r : forall v1 t2 t2', value v1 -> multi t2 t2' ->
  multi (tm_app v1 t2) (tm_app v1 t2').
Proof.
  intros v1 t2 t2' Hv H. induction H as [u|a b c Hstep Hm IH].
  - apply multi_refl.
  - apply multi_step with (t2 := tm_app v1 b); auto. apply ST_App2; auto.
Qed.

Lemma multi_app : forall t1 t1' t2 t2', multi t1 t1' -> multi t2 t2' ->
  locally_closed_tm t2 -> value t1' -> multi (tm_app t1 t2) (tm_app t1' t2').
Proof.
  intros t1 t1' t2 t2' H1 H2 Hlc Hv.
  apply multi_trans with (t2 := tm_app t1' t2).
  - apply multi_app_l; auto.
  - apply multi_app_r; auto.
Qed.

Lemma multi_tapp : forall t t' U, multi t t' -> locally_closed_ty U ->
  multi (tm_tapp t U) (tm_tapp t' U).
Proof.
  intros t t' U H. induction H as [u|a b c Hstep Hm IH]; intros Hlc.
  - apply multi_refl.
  - apply multi_step with (t2 := tm_tapp b U); auto. apply ST_TApp; auto.
Qed.

Lemma multi_div_l : forall t1 t1' t2, multi t1 t1' -> locally_closed_tm t2 ->
  multi (tm_div t1 t2) (tm_div t1' t2).
Proof.
  intros t1 t1' t2 H. induction H as [u|a b c Hstep Hm IH]; intros Hlc.
  - apply multi_refl.
  - apply multi_step with (t2 := tm_div b t2); auto. apply ST_Div1; auto.
Qed.

Lemma multi_div_r : forall v1 t2 t2', value v1 -> multi t2 t2' ->
  multi (tm_div v1 t2) (tm_div v1 t2').
Proof.
  intros v1 t2 t2' Hv H. induction H as [u|a b c Hstep Hm IH].
  - apply multi_refl.
  - apply multi_step with (t2 := tm_div v1 b); auto. apply ST_Div2; auto.
Qed.

Lemma multi_div : forall t1 t1' t2 t2', multi t1 t1' -> multi t2 t2' ->
  locally_closed_tm t2 -> value t1' -> multi (tm_div t1 t2) (tm_div t1' t2').
Proof.
  intros t1 t1' t2 t2' H1 H2 Hlc Hv.
  apply multi_trans with (t2 := tm_div t1' t2).
  - apply multi_div_l; auto.
  - apply multi_div_r; auto.
Qed.

Lemma multi_arith_l : forall op t1 t1' t2, multi t1 t1' -> locally_closed_tm t2 ->
  multi (tm_arith op t1 t2) (tm_arith op t1' t2).
Proof.
  intros op t1 t1' t2 H. induction H as [u|a b c Hstep Hm IH]; intros Hlc.
  - apply multi_refl.
  - apply multi_step with (t2 := tm_arith op b t2); auto. apply ST_Arith1; auto.
Qed.

Lemma multi_arith_r : forall op v1 t2 t2', value v1 -> multi t2 t2' ->
  multi (tm_arith op v1 t2) (tm_arith op v1 t2').
Proof.
  intros op v1 t2 t2' Hv H. induction H as [u|a b c Hstep Hm IH].
  - apply multi_refl.
  - apply multi_step with (t2 := tm_arith op v1 b); auto. apply ST_Arith2; auto.
Qed.

Lemma multi_arith : forall op t1 t1' t2 t2', multi t1 t1' -> multi t2 t2' ->
  locally_closed_tm t2 -> value t1' -> multi (tm_arith op t1 t2) (tm_arith op t1' t2').
Proof.
  intros op t1 t1' t2 t2' H1 H2 Hlc Hv.
  apply multi_trans with (t2 := tm_arith op t1' t2).
  - apply multi_arith_l; auto.
  - apply multi_arith_r; auto.
Qed.

Lemma value_no_step : forall v t, value v -> ~ (v --> t).
Proof.
  intros v t Hv Hstep. destruct Hv as [T body Hlc|body Hlc|n]; inversion Hstep.
Qed.

Lemma multi_value_inv' : forall t u, multi t u -> value t -> u = t.
Proof.
  intros t u H. induction H as [x|a b c Hstep Hm IH]; intros Hv.
  - reflexivity.
  - exfalso. exact (value_no_step a b Hv Hstep).
Qed.

Lemma multi_value_inv : forall v t, value v -> multi v t -> t = v.
Proof. intros. apply (multi_value_inv' v t); auto. Qed.

Lemma multi_to_pms : forall t u, multi t u -> predicate_multistep t u.
Proof.
  intros t u H. induction H as [x|a b c Hstep Hm IH].
  - apply PMS_Refl.
  - apply PMS_Step with (t2 := b); auto.
Qed.

(* ---------- T properties ---------- *)

Lemma T_intro : forall R t v, multi t v -> V R v -> T R t.
Proof. intros. unfold T. exists v. auto. Qed.

Lemma T_multi : forall R t u, multi t u -> T R u -> T R t.
Proof.
  intros R t u H1 H2. unfold T in *. destruct H2 as [v [H2 H3]].
  exists v. split; auto. apply multi_trans with (t2 := u); auto.
Qed.

Lemma T_value : forall R t, T R t -> exists v, multi t v /\ V R v.
Proof. intros. exact H. Qed.

Lemma T_lc : forall R t, T R t -> exists v, multi t v /\ value v.
Proof.
  intros R t [v [Hm Hv]]. exists v. split; auto. apply V_value with (R := R); auto.
Qed.

(* ---------- free variables of rcontexts ---------- *)

Fixpoint fv_rcontext (RGamma : rcontext) : list atom :=
  match RGamma with
  | [] => []
  | (y, R) :: rest => y :: fv_rty R ++ fv_rcontext rest
  end.

Fixpoint ftv_rcontext (RGamma : rcontext) : list atom :=
  match RGamma with
  | [] => []
  | (y, R) :: rest => ftv_rty R ++ ftv_rcontext rest
  end.

Lemma lookup_rcontext_fv : forall y R RGamma, lookup_rcontext y RGamma = Some R ->
  In y (fv_rcontext RGamma).
Proof.
  intros y R RGamma. induction RGamma as [|p rest IH]; intros H.
  - simpl in H. discriminate H.
  - destruct p as [x0 R0].
    destruct (Nat.eqb y x0) eqn:E.
    + apply Nat.eqb_eq in E. subst y. simpl. left. reflexivity.
    + apply Nat.eqb_neq in E.
      change (lookup_rcontext y (update_rcontext rest x0 R0) = Some R) in H.
      rewrite (lookup_rupdate_neq rest x0 y R0 E) in H.
      apply IH in H. simpl. right. apply in_app_iff. right. auto.
Qed.

Lemma lookup_rcontext_fv_rty : forall y R RGamma z, lookup_rcontext y RGamma = Some R ->
  In z (fv_rty R) -> In z (fv_rcontext RGamma).
Proof.
  intros y R RGamma. induction RGamma as [|p rest IH]; intros z H Hz.
  - simpl in H. discriminate H.
  - destruct p as [x0 R0].
    destruct (Nat.eqb y x0) eqn:E.
    + apply Nat.eqb_eq in E. subst y.
      change (lookup_rcontext x0 (update_rcontext rest x0 R0) = Some R) in H.
      rewrite lookup_rupdate_eq in H. injection H as E2. subst R.
      simpl. right. apply in_app_iff. left. auto.
    + apply Nat.eqb_neq in E.
      change (lookup_rcontext y (update_rcontext rest x0 R0) = Some R) in H.
      rewrite (lookup_rupdate_neq rest x0 y R0 E) in H.
      assert (HIn : In z (fv_rcontext rest)) by (apply (IH z); auto).
      simpl. right. apply in_app_iff. right. exact HIn.
Qed.

Lemma lookup_rcontext_ftv_rty : forall y R RGamma z, lookup_rcontext y RGamma = Some R ->
  In z (ftv_rty R) -> In z (ftv_rcontext RGamma).
Proof.
  intros y R RGamma. induction RGamma as [|p rest IH]; intros z H Hz.
  - simpl in H. discriminate H.
  - destruct p as [x0 R0].
    destruct (Nat.eqb y x0) eqn:E.
    + apply Nat.eqb_eq in E. subst y.
      change (lookup_rcontext x0 (update_rcontext rest x0 R0) = Some R) in H.
      rewrite lookup_rupdate_eq in H. injection H as E2. subst R.
      simpl. apply in_app_iff. left. auto.
    + apply Nat.eqb_neq in E.
      change (lookup_rcontext y (update_rcontext rest x0 R0) = Some R) in H.
      rewrite (lookup_rupdate_neq rest x0 y R0 E) in H.
      assert (HIn : In z (ftv_rcontext rest)) by (apply (IH z); auto).
      simpl. apply in_app_iff. right. exact HIn.
Qed.

(* ---------- base value shapes are preserved by closing ---------- *)

Lemma has_type_value_base_close : forall Delta Gamma v T, has_type Delta Gamma v T -> value v ->
  forall sigma tau, base_val (close_ty tau T) (close_tm sigma tau v).
Proof.
  intros Delta Gamma v T H. induction H as [Delta0 Gamma0 x T0 Hlk Hwf|L Delta0 Gamma0 T1 t2 T2 Hwf H IH
    |Delta0 Gamma0 t1 t2 T1 T2 H1 IH1 H2 IH2|L Delta0 Gamma0 t T H IH
    |Delta0 Gamma0 t T U H IH Hwf|Delta0 Gamma0 n|Delta0 Gamma0 t1 t2 H1 IH1 H2 IH2
    |Delta0 Gamma0 op t1 t2 H1 IH1 H2 IH2]; intros Hval sigma tau.
  - inversion Hval.
  - simpl. exists (tysubst_ty tau T1), (tysubst_tm tau (tsubst_tm sigma t2)). reflexivity.
  - inversion Hval.
  - simpl. exists (tysubst_tm tau (tsubst_tm sigma t)). reflexivity.
  - inversion Hval.
  - simpl. exists n. reflexivity.
  - inversion Hval.
  - inversion Hval.
Qed.

(* ---------- fresh atoms avoiding a five-part concatenation ---------- *)

Lemma in_concat1 : forall (A B C D E : list atom) z, In z A -> In z (A ++ B ++ C ++ D ++ E).
Proof. intros. apply in_app_iff. left. auto. Qed.
Lemma in_concat2 : forall (A B C D E : list atom) z, In z B -> In z (A ++ B ++ C ++ D ++ E).
Proof. intros. apply in_app_iff. right. apply in_app_iff. left. auto. Qed.
Lemma in_concat3 : forall (A B C D E : list atom) z, In z C -> In z (A ++ B ++ C ++ D ++ E).
Proof. intros. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. auto. Qed.
Lemma in_concat4 : forall (A B C D E : list atom) z, In z D -> In z (A ++ B ++ C ++ D ++ E).
Proof. intros. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. auto. Qed.
Lemma in_concat5 : forall (A B C D E : list atom) z, In z E -> In z (A ++ B ++ C ++ D ++ E).
Proof. intros. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. auto. Qed.

Lemma fresh_notin1 : forall A B C D E, ~ In (fresh (A ++ B ++ C ++ D ++ E)) A.
Proof. intros. intro H. apply (fresh_notin (A ++ B ++ C ++ D ++ E)). apply in_concat1; auto. Qed.
Lemma fresh_notin2 : forall A B C D E, ~ In (fresh (A ++ B ++ C ++ D ++ E)) B.
Proof. intros. intro H. apply (fresh_notin (A ++ B ++ C ++ D ++ E)). apply in_concat2; auto. Qed.
Lemma fresh_notin3 : forall A B C D E, ~ In (fresh (A ++ B ++ C ++ D ++ E)) C.
Proof. intros. intro H. apply (fresh_notin (A ++ B ++ C ++ D ++ E)). apply in_concat3; auto. Qed.
Lemma fresh_notin4 : forall A B C D E, ~ In (fresh (A ++ B ++ C ++ D ++ E)) D.
Proof. intros. intro H. apply (fresh_notin (A ++ B ++ C ++ D ++ E)). apply in_concat4; auto. Qed.
Lemma fresh_notin5 : forall A B C D E, ~ In (fresh (A ++ B ++ C ++ D ++ E)) E.
Proof. intros. intro H. apply (fresh_notin (A ++ B ++ C ++ D ++ E)). apply in_concat5; auto. Qed.

(* ---------- type-level: closedness of substituted types ---------- *)

Lemma lc_ty_close : forall tau T, tenv_good tau ->
  lc_ty_at 0 T -> lc_ty_at 0 (close_ty tau T).
Proof.
  intros tau T Ht Hlc. unfold close_ty. apply (lc_ty_tysubst T 0 Hlc tau).
  intros X. apply tenv_good_lc; auto.
Qed.

Lemma fv_ty_close : forall tau T, tenv_good tau -> fv_ty (close_ty tau T) = [].
Proof.
  intros tau T Ht. unfold close_ty. apply fv_ty_tysubst_closed. intros X. apply tenv_good_fv; auto.
Qed.

Lemma wf_ty_close : forall Delta tau U, wf_ty Delta U -> tenv_good tau ->
  locally_closed_ty (close_ty tau U) /\ fv_ty (close_ty tau U) = [].
Proof.
  intros Delta tau U Hwf Ht. split.
  - apply lc_ty_close; auto. apply (wf_ty_lc Delta U Hwf 0).
  - apply fv_ty_close; auto.
Qed.

(* ---------- extending the context interpretation ---------- *)

Lemma satisfies_context_update_tm : forall sigma tau RGamma x R w,
  env_good sigma -> tenv_good tau -> satisfies_context sigma tau RGamma ->
  V (close_rty sigma tau R) w ->
  ~ In x (fv_rcontext RGamma) -> ~ In x (fv_rty R) ->
  satisfies_context (upd_tm sigma x w) tau (update_rcontext RGamma x R).
Proof.
  intros sigma tau RGamma x R w Hg Ht Hctx Hw Hdom HxR y R0 Hy.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst y.
    change (lookup_rcontext x (update_rcontext RGamma x R) = Some R0) in Hy.
    rewrite lookup_rupdate_eq in Hy. injection Hy as E2. subst R0.
    rewrite upd_tm_eq.
    rewrite (close_rty_absent R sigma tau x w HxR).
    exact Hw.
  - apply Nat.eqb_neq in E.
    change (lookup_rcontext y (update_rcontext RGamma x R) = Some R0) in Hy.
    rewrite (lookup_rupdate_neq RGamma x y R E) in Hy.
    rewrite (upd_tm_neq sigma x w y E).
    assert (HxR0 : ~ In x (fv_rty R0)).
    { intro Hc. apply Hdom. apply (lookup_rcontext_fv_rty y R0 RGamma x Hy Hc). }
    rewrite (close_rty_absent R0 sigma tau x w HxR0).
    apply Hctx; auto.
Qed.

Lemma satisfies_context_update_ty : forall sigma tau RGamma X U,
  env_good sigma -> tenv_good tau -> satisfies_context sigma tau RGamma ->
  locally_closed_ty U -> fv_ty U = [] ->
  ~ In X (ftv_rcontext RGamma) ->
  satisfies_context sigma (upd_ty tau X U) RGamma.
Proof.
  intros sigma tau RGamma X U Hg Ht Hctx Hlc Hfv Hdom y R Hy.
  assert (HXR : ~ In X (ftv_rty R)).
  { intro Hc. apply Hdom. apply (lookup_rcontext_ftv_rty y R RGamma X Hy Hc). }
  rewrite (close_rty_absent_ty R sigma tau X U ltac:(apply env_good_ftv; auto) HXR).
  apply Hctx; auto.
Qed.

(* ---------- local closure of closed abstractions ---------- *)

Lemma lc_abs_intro : forall T body, lc_ty_at 0 T -> lc_tm_at 0 1 body ->
  locally_closed_tm (tm_abs T body).
Proof. intros. apply lc_tm_abs; auto. Qed.

Lemma value_abs_of_lc : forall T body, locally_closed_tm (tm_abs T body) -> value (tm_abs T body).
Proof. intros. apply v_abs; auto. Qed.

(* ---------- integer-divisor nonzero from the refinement ---------- *)

Lemma neq_zero_of_holds : forall n,
  predicate_holds (Pred_Not (Pred_Eq (tm_int n) (tm_int 0%Z))) -> n <> 0%Z.
Proof.
  intros n Hneg Hz.
  rewrite holds_not in Hneg. rewrite holds_eq in Hneg.
  apply Hneg.
  exists (tm_int 0%Z). split; [|split].
  - rewrite Hz. apply PMS_Refl.
  - apply PMS_Refl.
  - apply v_int.
Qed.
Scheme has_rtype_mut := Induction for has_rtype Sort Prop
  with subtype_mut := Induction for subtype Sort Prop.
Combined Scheme has_rtype_subtype_combined from has_rtype_mut, subtype_mut.


(* ---------- the fundamental theorem and subtype soundness ---------- *)

Definition Pfun (Delta : ty_context) (RGamma : rcontext) (t : tm) (R : rty)
    (_ : has_rtype Delta RGamma t R) : Prop :=
  forall sigma tau, env_good sigma -> tenv_good tau ->
  satisfies_context sigma tau RGamma -> T (close_rty sigma tau R) (close_tm sigma tau t).

Definition P0fun (Delta : ty_context) (RGamma : rcontext) (R S : rty)
    (_ : subtype Delta RGamma R S) : Prop :=
  forall sigma tau, env_good sigma -> tenv_good tau ->
  satisfies_context sigma tau RGamma ->
  forall v, V (close_rty sigma tau R) v -> V (close_rty sigma tau S) v.

Lemma close_rty_refine : forall sigma tau T0 ps,
  close_rty sigma tau (R_Refine T0 ps) = R_Refine (close_ty tau T0) (close_qual sigma tau ps).
Proof. intros. reflexivity. Qed.

Lemma close_rty_func : forall sigma tau R1 R2,
  close_rty sigma tau (R_Func R1 R2) = R_Func (close_rty sigma tau R1) (close_rty sigma tau R2).
Proof. intros. reflexivity. Qed.

Lemma close_rty_exists : forall sigma tau R1 R2,
  close_rty sigma tau (R_Exists R1 R2) = R_Exists (close_rty sigma tau R1) (close_rty sigma tau R2).
Proof. intros. reflexivity. Qed.

Lemma close_rty_poly : forall sigma tau R,
  close_rty sigma tau (R_Poly R) = R_Poly (close_rty sigma tau R).
Proof. intros. reflexivity. Qed.

Lemma close_tm_abs : forall sigma tau T0 body,
  close_tm sigma tau (tm_abs T0 body) = tm_abs (close_ty tau T0) (close_tm sigma tau body).
Proof. intros. reflexivity. Qed.

Lemma close_tm_app : forall sigma tau t1 t2,
  close_tm sigma tau (tm_app t1 t2) = tm_app (close_tm sigma tau t1) (close_tm sigma tau t2).
Proof. intros. reflexivity. Qed.

Lemma close_tm_tabs : forall sigma tau body,
  close_tm sigma tau (tm_tabs body) = tm_tabs (close_tm sigma tau body).
Proof. intros. reflexivity. Qed.

Lemma close_tm_tapp : forall sigma tau t T0,
  close_tm sigma tau (tm_tapp t T0) = tm_tapp (close_tm sigma tau t) (close_ty tau T0).
Proof. intros. reflexivity. Qed.

Lemma close_tm_int : forall sigma tau n,
  close_tm sigma tau (tm_int n) = tm_int n.
Proof. intros. reflexivity. Qed.

Lemma close_tm_div : forall sigma tau t1 t2,
  close_tm sigma tau (tm_div t1 t2) = tm_div (close_tm sigma tau t1) (close_tm sigma tau t2).
Proof. intros. reflexivity. Qed.

Lemma close_tm_arith : forall sigma tau op t1 t2,
  close_tm sigma tau (tm_arith op t1 t2) = tm_arith op (close_tm sigma tau t1) (close_tm sigma tau t2).
Proof. intros. reflexivity. Qed.

Lemma fund_and_subtype :
  (forall Delta RGamma t R (H : has_rtype Delta RGamma t R), Pfun Delta RGamma t R H) /\
  (forall Delta RGamma R S (H : subtype Delta RGamma R S), P0fun Delta RGamma R S H).
Proof.
  apply has_rtype_subtype_combined with (P := Pfun) (P0 := P0fun).
  (* RT_Var *)
  - intros Delta RGamma x R Hlk Hwf sigma tau Hg Ht Hctx.
    unfold T. exists (sigma x). split.
    + assert (Hfvx : ftv_tm (sigma x) = []) by (apply env_good_ftv; auto).
      rewrite (close_tm_fvar sigma tau x Hfvx). apply multi_refl.
    + exact (Hctx x R Hlk).
  (* RT_Abs *)
  - intros L Delta RGamma R1 body R2 Hwf Hbody IH sigma tau Hg Ht Hctx.
    set (x := fresh (L ++ fv_rcontext RGamma ++ fv_rty R1 ++ fv_rty R2 ++ fv_tm body)).
    assert (HxL : ~ In x L) by (subst x; apply fresh_notin1).
    assert (Hxctx : ~ In x (fv_rcontext RGamma)) by (subst x; apply fresh_notin2).
    assert (HxR1 : ~ In x (fv_rty R1)) by (subst x; apply fresh_notin3).
    assert (HxR2 : ~ In x (fv_rty R2)) by (subst x; apply fresh_notin4).
    assert (Hxbody : ~ In x (fv_tm body)) by (subst x; apply fresh_notin5).
    assert (Hlc_ty : lc_ty_at 0 (erase R1)) by (apply (wf_rty_erase_lc Delta RGamma R1 Hwf 0)).
    assert (Hlc_body : lc_tm_at 0 1 body).
    { apply (lc_tm_open_inv 0 0 0 (tm_fvar x) body eq_refl).
      exact (has_rtype_lc _ _ _ _ (Hbody x HxL)). }
    assert (Hval_abs : value (tm_abs (erase R1) body)).
    { apply v_abs. apply lc_tm_abs; auto. }
    unfold T. exists (close_tm sigma tau (tm_abs (erase R1) body)). split.
    + apply multi_refl.
    + rewrite close_rty_func. rewrite V_Func.
      split; [apply close_tm_value; auto | split; [apply close_tm_fv_nil; auto | split; [apply close_tm_ftv_nil; auto |]]].
      intros w Hw.
      assert (Hwv : value w) by (apply (V_value _ _ Hw)).
      assert (Hwfv : fv_tm w = []) by (apply (V_fv _ _ Hw)).
      assert (Hwftv : ftv_tm w = []) by (apply (V_ftv _ _ Hw)).
      assert (Hlc_abs : locally_closed_tm (tm_abs (tysubst_ty tau (erase R1)) (close_tm sigma tau body))).
      { apply lc_tm_abs.
        - apply (lc_ty_tysubst (erase R1) 0 Hlc_ty tau). intros X. apply tenv_good_lc; auto.
        - apply close_tm_lc_at; auto. }
      assert (Hstep : tm_app (close_tm sigma tau (tm_abs (erase R1) body)) w -->
                      open_tm (close_tm sigma tau body) w).
      { change (tm_app (tm_abs (tysubst_ty tau (erase R1)) (close_tm sigma tau body)) w -->
                open_tm (close_tm sigma tau body) w).
        apply ST_AppAbs; auto. }
      assert (Hg' : env_good (upd_tm sigma x w)).
      { apply env_good_upd; auto. }
      assert (Hctx' : satisfies_context (upd_tm sigma x w) tau (update_rcontext RGamma x R1)).
      { apply satisfies_context_update_tm; auto. }
      pose proof (IH x HxL (upd_tm sigma x w) tau Hg' Ht Hctx') as HbodyT.
      rewrite (close_rty_open_fvar sigma tau R2 x w Hg Ht Hwv Hwfv Hwftv HxR2) in HbodyT.
      rewrite (close_tm_open_fvar sigma tau body x w Hg Ht Hwv Hwfv Hwftv Hxbody) in HbodyT.
      destruct HbodyT as [u [Hmulti Hu]].
      rewrite close_tm_abs.
      exists u. split.
      * apply multi_trans with (t2 := open_tm (close_tm sigma tau body) w).
        { apply multi_step with (t2 := open_tm (close_tm sigma tau body) w); auto. apply multi_refl. }
        { exact Hmulti. }
      * exact Hu.
  (* RT_App *)
  - intros Delta RGamma t1 t2 R1 R2 H1 IH1 H2 IH2 sigma tau Hg Ht Hctx.
    destruct (IH1 sigma tau Hg Ht Hctx) as [v1 [Hm1 Hv1]].
    destruct (IH2 sigma tau Hg Ht Hctx) as [v2 [Hm2 Hv2]].
    rewrite close_rty_func in Hv1. rewrite V_Func in Hv1.
    destruct Hv1 as [Hval1 [Hfv1 [Hftv1 Hbody1]]].
    destruct (Hbody1 v2 Hv2) as [u [Hmu Hu]].
    assert (Hlc2 : locally_closed_tm (close_tm sigma tau t2)).
    { apply close_tm_lc_at; auto. exact (has_rtype_lc _ _ _ _ H2). }
    assert (Hmulti : multi (tm_app (close_tm sigma tau t1) (close_tm sigma tau t2)) (tm_app v1 v2)).
    { apply multi_app; auto. }
    unfold T. exists u. split.
    + apply multi_trans with (t2 := tm_app v1 v2); auto.
    + rewrite close_rty_exists. rewrite V_Exists. split; [apply (V_value _ _ Hu) | split; [apply (V_fv _ _ Hu) | split; [apply (V_ftv _ _ Hu) |]]].
      exists v2. split; auto.
  (* RT_TAbs *)
  - intros L Delta RGamma body R Hbody IH sigma tau Hg Ht Hctx.
    set (X := fresh (L ++ ftv_rcontext RGamma ++ ftv_rty R ++ ftv_tm body ++ [])).
    assert (HxL : ~ In X L) by (subst X; apply fresh_notin1).
    assert (Hxctx : ~ In X (ftv_rcontext RGamma)) by (subst X; apply fresh_notin2).
    assert (HxR : ~ In X (ftv_rty R)) by (subst X; apply fresh_notin3).
    assert (Hxbody : ~ In X (ftv_tm body)) by (subst X; apply fresh_notin4).
    assert (Hlc_body : lc_tm_at 1 0 body).
    { apply (lc_tm_ty_open_inv 0 0 0 (Ty_FVar X) body eq_refl).
      exact (has_rtype_lc _ _ _ _ (Hbody X HxL)). }
    assert (Hval : value (tm_tabs (close_tm sigma tau body))).
    { apply v_tabs. apply lc_tm_tabs. apply close_tm_lc_at; auto. }
    unfold T. exists (tm_tabs (close_tm sigma tau body)). split.
    + apply multi_refl.
    + rewrite close_rty_poly. rewrite V_Poly.
      split; [exact Hval | split; [apply close_tm_fv_nil; auto | split; [apply close_tm_ftv_nil; auto |]]].
      intros U HlcU HfvU.
      assert (Ht' : tenv_good (upd_ty tau X U)) by (apply tenv_good_upd; auto).
      assert (Hctx' : satisfies_context sigma (upd_ty tau X U) RGamma).
      { apply satisfies_context_update_ty; auto. }
      pose proof (IH X HxL sigma (upd_ty tau X U) Hg Ht' Hctx') as HbodyT.
      assert (Heq1 : close_rty sigma (upd_ty tau X U) (open_rty_ty R (Ty_FVar X)) =
                     open_rty_ty (close_rty sigma tau R) U).
      { apply close_rty_open_ty_fvar; auto. }
      assert (Heq2 : close_tm sigma (upd_ty tau X U) (open_tm_ty body (Ty_FVar X)) =
                     open_tm_ty (close_tm sigma tau body) U).
      { apply close_tm_open_ty_fvar; auto. }
      rewrite Heq1, Heq2 in HbodyT.
      destruct HbodyT as [u [Hmu Hu]].
      exists u. split.
      * apply multi_trans with (t2 := open_tm_ty (close_tm sigma tau body) U).
        { apply multi_step with (t2 := open_tm_ty (close_tm sigma tau body) U).
          - apply ST_TAppTabs; [apply value_lc; auto | exact HlcU].
          - apply multi_refl. }
        { exact Hmu. }
      * exact Hu.
  (* RT_TApp *)
  - intros Delta RGamma t R U H1 IH Hwf sigma tau Hg Ht Hctx.
    destruct (IH sigma tau Hg Ht Hctx) as [v [Hm Hv]].
    rewrite close_rty_poly in Hv. rewrite V_Poly in Hv.
    destruct Hv as [Hval [Hfv [Hftv Hbody]]].
    assert (HlcU : locally_closed_ty (close_ty tau U)).
    { apply lc_ty_close; auto. apply (wf_ty_lc Delta U Hwf 0). }
    assert (HfvU : fv_ty (close_ty tau U) = []) by (apply fv_ty_close; auto).
    destruct (Hbody (close_ty tau U) HlcU HfvU) as [u [Hmu Hu]].
    exists u. split.
    + change (multi (tm_tapp (close_tm sigma tau t) (close_ty tau U)) u).
      apply multi_trans with (t2 := tm_tapp v (close_ty tau U)).
      * apply multi_tapp; auto.
      * exact Hmu.
    + assert (Heq : close_rty sigma tau (open_rty_ty R U) =
                    open_rty_ty (close_rty sigma tau R) (close_ty tau U)).
      { apply close_rty_open_ty; [intros y; apply value_lc; apply env_good_value; auto | intros Y; apply tenv_good_lc; auto]. }
      rewrite Heq. exact Hu.
  (* RT_Int *)
  - intros Delta RGamma n sigma tau Hg Ht Hctx.
    unfold T. exists (tm_int n). split.
    + apply multi_refl.
    + rewrite close_rty_refine. rewrite V_Refine.
      split; [apply v_int | split; [reflexivity | split; [reflexivity | split]]].
      * simpl. exists n. reflexivity.
      * assert (Hoq : open_qualifier_tm (close_qual sigma tau (Pred_Eq (tm_bvar 0) (tm_int n))) (tm_int n) =
                      Pred_Eq (tm_int n) (tm_int n)).
        { unfold close_qual, open_qualifier_tm. reflexivity. }
        rewrite Hoq. rewrite holds_eq. exists (tm_int n). split; [|split]; [apply PMS_Refl | apply PMS_Refl | apply v_int].
  (* RT_Div *)
  - intros Delta RGamma t1 t2 H1 IH1 H2 IH2 sigma tau Hg Ht Hctx.
    destruct (IH1 sigma tau Hg Ht Hctx) as [v1 [Hm1 Hv1]].
    destruct (IH2 sigma tau Hg Ht Hctx) as [v2 [Hm2 Hv2]].
    rewrite close_rty_refine in Hv1. rewrite V_Refine in Hv1. destruct Hv1 as [_ [_ [_ [Hb1 _]]]].
    rewrite close_rty_refine in Hv2. rewrite V_Refine in Hv2. destruct Hv2 as [Hval2 [_ [_ [Hb2 Hp2]]]].
    unfold base_val in Hb1. destruct Hb1 as [n1 E1]. subst v1.
    unfold base_val in Hb2. destruct Hb2 as [n2 E2]. subst v2.
    assert (Hp2' : predicate_holds (Pred_Not (Pred_Eq (tm_int n2) (tm_int 0%Z)))).
    { change (predicate_holds (Pred_Not (Pred_Eq (tm_int n2) (tm_int 0%Z)))). exact Hp2. }
    assert (Hnz : n2 <> 0%Z) by (apply neq_zero_of_holds; auto).
    assert (Hm : multi (tm_div (close_tm sigma tau t1) (close_tm sigma tau t2)) (tm_int (Z.div n1 n2))).
    { apply multi_trans with (t2 := tm_div (tm_int n1) (tm_int n2)).
      - apply multi_div; auto.
        + apply close_tm_lc_at; auto. exact (has_rtype_lc _ _ _ _ H2).
        + apply v_int.
      - apply multi_step with (t2 := tm_int (Z.div n1 n2)).
        + apply ST_DivInt. auto.
        + apply multi_refl. }
    unfold T. exists (tm_int (Z.div n1 n2)). split.
    + exact Hm.
    + rewrite close_rty_refine. rewrite V_Refine.
      split; [apply v_int | split; [reflexivity | split; [reflexivity | split]]].
      * simpl. exists (Z.div n1 n2). reflexivity.
      * rewrite close_qual_true. unfold open_qualifier_tm. apply holds_true.
  (* RT_Arith *)
  - intros Delta RGamma op t1 t2 H1 IH1 H2 IH2 sigma tau Hg Ht Hctx.
    destruct (IH1 sigma tau Hg Ht Hctx) as [v1 [Hm1 Hv1]].
    destruct (IH2 sigma tau Hg Ht Hctx) as [v2 [Hm2 Hv2]].
    rewrite close_rty_refine in Hv1. rewrite V_Refine in Hv1. destruct Hv1 as [_ [_ [_ [Hb1 _]]]].
    rewrite close_rty_refine in Hv2. rewrite V_Refine in Hv2. destruct Hv2 as [Hval2 [_ [_ [Hb2 _]]]].
    unfold base_val in Hb1. destruct Hb1 as [n1 E1]. subst v1.
    unfold base_val in Hb2. destruct Hb2 as [n2 E2]. subst v2.
    assert (Hm : multi (tm_arith op (close_tm sigma tau t1) (close_tm sigma tau t2))
                     (tm_int (eval_integer_operator op n1 n2))).
    { apply multi_trans with (t2 := tm_arith op (tm_int n1) (tm_int n2)).
      - apply multi_arith; auto.
        + apply close_tm_lc_at; auto. exact (has_rtype_lc _ _ _ _ H2).
        + apply v_int.
      - apply multi_step with (t2 := tm_int (eval_integer_operator op n1 n2)).
        + apply ST_ArithInt.
        + apply multi_refl. }
    unfold T. exists (tm_int (eval_integer_operator op n1 n2)). split.
    + exact Hm.
    + rewrite close_rty_refine. rewrite V_Refine.
      split; [apply v_int | split; [reflexivity | split; [reflexivity | split]]].
      * simpl. exists (eval_integer_operator op n1 n2). reflexivity.
      * assert (Hlc1 : lc_tm_at 0 0 (close_tm sigma tau t1)).
        { apply close_tm_lc_at; auto. exact (has_rtype_lc _ _ _ _ H1). }
        assert (Hlc2 : lc_tm_at 0 0 (close_tm sigma tau t2)).
        { apply close_tm_lc_at; auto. exact (has_rtype_lc _ _ _ _ H2). }
        assert (Hoq : open_qualifier_tm (close_qual sigma tau (Pred_Eq (tm_bvar 0) (tm_arith op t1 t2)))
                        (tm_int (eval_integer_operator op n1 n2))
                      = Pred_Eq (tm_int (eval_integer_operator op n1 n2))
                          (tm_arith op (close_tm sigma tau t1) (close_tm sigma tau t2))).
        { unfold close_qual, open_qualifier_tm, open_qualifier_tm_rec.
          cbn [open_pred_tm_rec open_tm_rec tysubst_qual tsubst_qual tysubst_tm tsubst_tm close_tm close_ty].
          rewrite (open_tm_lc_id (tysubst_tm tau (tsubst_tm sigma t1)) 0 0 Hlc1 0 (tm_int (eval_integer_operator op n1 n2)) (le_n 0)).
          rewrite (open_tm_lc_id (tysubst_tm tau (tsubst_tm sigma t2)) 0 0 Hlc2 0 (tm_int (eval_integer_operator op n1 n2)) (le_n 0)).
          reflexivity. }
        rewrite Hoq. rewrite holds_eq.
        exists (tm_int (eval_integer_operator op n1 n2)). split; [|split].
        { apply PMS_Refl. }
        { apply multi_to_pms; exact Hm. }
        { apply v_int. }
  (* RT_RefineValue *)
  - intros Delta RGamma v T0 ps Hty Hval Hwf Hpc Hqh sigma tau Hg Ht Hctx.
    unfold T. exists (close_tm sigma tau v). split.
    + apply multi_refl.
    + rewrite close_rty_refine. rewrite V_Refine.
      split; [apply close_tm_value; auto | split; [apply close_tm_fv_nil; auto | split; [apply close_tm_ftv_nil; auto | split]]].
      * exact (has_type_value_base_close Delta (erase_context RGamma) v T0 Hty Hval sigma tau).
      * assert (Heq : close_qual sigma tau (open_qualifier_tm ps v) =
                      open_qualifier_tm (close_qual sigma tau ps) (close_tm sigma tau v)).
        { apply close_qual_open_tm.
          - intros y. apply value_lc. apply env_good_value; auto.
          - intros Y. apply tenv_good_lc; auto. }
        rewrite <- Heq.
        rewrite (close_qual_of_closed sigma tau (open_qualifier_tm ps v) Hpc).
        exact Hqh.
  (* RT_Sub *)
  - intros Delta RGamma t R S H1 IH Hwf Hsub IHsub sigma tau Hg Ht Hctx.
    destruct (IH sigma tau Hg Ht Hctx) as [v [Hm Hv]].
    assert (HvS : V (close_rty sigma tau S) v).
    { apply (IHsub sigma tau Hg Ht Hctx v Hv). }
    unfold T. exists v. split; auto.
  (* S_Refl *)
  - intros Delta RGamma R sigma tau Hg Ht Hctx v Hv. exact Hv.
  (* S_Refine *)
  - intros L Delta RGamma T0 ps qs He sigma tau Hg Ht Hctx v Hv.
    set (x := fresh (L ++ fv_rcontext RGamma ++ fv_qual ps ++ fv_qual qs ++ [])).
    assert (HxL : ~ In x L) by (subst x; apply fresh_notin1).
    assert (Hxctx : ~ In x (fv_rcontext RGamma)) by (subst x; apply fresh_notin2).
    assert (Hxps : ~ In x (fv_qual ps)) by (subst x; apply fresh_notin3).
    assert (Hxqs : ~ In x (fv_qual qs)) by (subst x; apply fresh_notin4).
    rewrite close_rty_refine in Hv. rewrite V_Refine in Hv. destruct Hv as [Hval [Hfv [Hftv [Hb Hp]]]].
    assert (Hg' : env_good (upd_tm sigma x v)).
    { apply env_good_upd; auto. }
    assert (HVx : V (close_rty sigma tau (R_Refine T0 Pred_True)) v).
    { rewrite close_rty_refine. rewrite V_Refine. split; [exact Hval | split; [exact Hfv | split; [exact Hftv | split]]].
      - exact Hb.
      - rewrite close_qual_true. unfold open_qualifier_tm. apply holds_true. }
    assert (Hctx' : satisfies_context (upd_tm sigma x v) tau (update_rcontext RGamma x (R_Refine T0 Pred_True))).
    { apply satisfies_context_update_tm; auto; try (simpl; intro Hc; destruct Hc). }
    assert (Hps : predicate_holds (close_qual (upd_tm sigma x v) tau (open_qualifier_tm ps (tm_fvar x)))).
    { rewrite (close_qual_open_fvar (upd_tm sigma x v) tau ps x Hg' Ht).
      rewrite (close_qual_absent ps sigma tau x v Hxps).
      rewrite upd_tm_eq. exact Hp. }
    assert (Himp := entails_sound _ _ _ _ (He x HxL) (upd_tm sigma x v) tau Hg' Ht Hctx' Hps).
    rewrite (close_qual_open_fvar (upd_tm sigma x v) tau qs x Hg' Ht) in Himp.
    rewrite (close_qual_absent qs sigma tau x v Hxqs) in Himp.
    rewrite upd_tm_eq in Himp.
    rewrite close_rty_refine. rewrite V_Refine. split; [exact Hval | split; [exact Hfv | split; [exact Hftv | split]]].
    + exact Hb.
    + exact Himp.
  (* S_Func *)
  - intros L Delta RGamma R1 R2 S1 S2 Hs1 IHs1 Hs2 IHs2 sigma tau Hg Ht Hctx v Hv.
    rewrite close_rty_func in Hv. rewrite V_Func in Hv. destruct Hv as [Hval [Hfv [Hftv Hbody]]].
    rewrite close_rty_func. rewrite V_Func. split; [exact Hval | split; [exact Hfv | split; [exact Hftv |]]].
    intros w Hw.
    assert (Hw1 : V (close_rty sigma tau R1) w).
    { exact (IHs1 sigma tau Hg Ht Hctx w Hw). }
    destruct (Hbody w Hw1) as [u [Hmu Hu]].
    exists u. split; auto.
    set (x := fresh (L ++ fv_rcontext RGamma ++ fv_rty S1 ++ fv_rty R2 ++ fv_rty S2)).
    assert (HxL : ~ In x L) by (subst x; apply fresh_notin1).
    assert (Hxctx : ~ In x (fv_rcontext RGamma)) by (subst x; apply fresh_notin2).
    assert (HxS1 : ~ In x (fv_rty S1)) by (subst x; apply fresh_notin3).
    assert (HxR2 : ~ In x (fv_rty R2)) by (subst x; apply fresh_notin4).
    assert (HxS2 : ~ In x (fv_rty S2)) by (subst x; apply fresh_notin5).
    assert (Hwv : value w) by (apply (V_value _ _ Hw)).
    assert (Hwfv : fv_tm w = []) by (apply (V_fv _ _ Hw)).
    assert (Hwftv : ftv_tm w = []) by (apply (V_ftv _ _ Hw)).
    assert (Hg' : env_good (upd_tm sigma x w)).
    { apply env_good_upd; auto. }
    assert (Hctx' : satisfies_context (upd_tm sigma x w) tau (update_rcontext RGamma x S1)).
    { apply satisfies_context_update_tm; auto. }
    pose proof (IHs2 x HxL (upd_tm sigma x w) tau Hg' Ht Hctx' u) as Hfin.
    rewrite <- (close_rty_open_fvar sigma tau S2 x w Hg Ht Hwv Hwfv Hwftv HxS2).
    apply Hfin.
    rewrite (close_rty_open_fvar sigma tau R2 x w Hg Ht Hwv Hwfv Hwftv HxR2).
    exact Hu.
  (* S_Witness *)
  - intros Delta RGamma v0 R1 R2 S Hval0 Hrt IHrt Hsub IHsub sigma tau Hg Ht Hctx v Hv.
    rewrite close_rty_exists. rewrite V_Exists. split; [exact (V_value _ _ Hv) | split; [exact (V_fv _ _ Hv) | split; [exact (V_ftv _ _ Hv) |]]].
    exists (close_tm sigma tau v0). split.
    + destruct (IHrt sigma tau Hg Ht Hctx) as [u [Hm Hu]].
      assert (Hm' : u = close_tm sigma tau v0).
      { apply (multi_value_inv' (close_tm sigma tau v0) u Hm). apply close_tm_value; auto. }
      subst u. exact Hu.
    + assert (Hfin : V (close_rty sigma tau (open_rty_tm R2 v0)) v).
      { exact (IHsub sigma tau Hg Ht Hctx v Hv). }
      assert (Hfin2 : V (open_rty_tm (close_rty sigma tau R2) (close_tm sigma tau v0)) v).
      { rewrite <- (close_rty_open_tm sigma tau ltac:(intros y; apply value_lc; apply env_good_value; auto) ltac:(intros Y; apply tenv_good_lc; auto) R2 v0). exact Hfin. }
      exact Hfin2.
  (* S_Bind *)
  - intros L Delta RGamma R1 R2 S Hwf HlcS Hs IHs sigma tau Hg Ht Hctx v Hv.
    rewrite close_rty_exists in Hv. rewrite V_Exists in Hv. destruct Hv as [Hval [Hfv [Hftv [w [Hw1 Hw2]]]]].
    set (x := fresh (L ++ fv_rcontext RGamma ++ fv_rty R1 ++ fv_rty R2 ++ fv_rty S)).
    assert (HxL : ~ In x L) by (subst x; apply fresh_notin1).
    assert (Hxctx : ~ In x (fv_rcontext RGamma)) by (subst x; apply fresh_notin2).
    assert (HxR1 : ~ In x (fv_rty R1)) by (subst x; apply fresh_notin3).
    assert (HxR2 : ~ In x (fv_rty R2)) by (subst x; apply fresh_notin4).
    assert (HxS : ~ In x (fv_rty S)) by (subst x; apply fresh_notin5).
    assert (Hwv : value w) by (apply (V_value _ _ Hw1)).
    assert (Hwfv : fv_tm w = []) by (apply (V_fv _ _ Hw1)).
    assert (Hwftv : ftv_tm w = []) by (apply (V_ftv _ _ Hw1)).
    assert (Hg' : env_good (upd_tm sigma x w)).
    { apply env_good_upd; auto. }
    assert (Hctx' : satisfies_context (upd_tm sigma x w) tau (update_rcontext RGamma x R1)).
    { apply satisfies_context_update_tm; auto. }
    pose proof (IHs x HxL (upd_tm sigma x w) tau Hg' Ht Hctx' v) as Hfin.
    rewrite (close_rty_absent S sigma tau x w HxS) in Hfin.
    apply Hfin.
    rewrite (close_rty_open_fvar sigma tau R2 x w Hg Ht Hwv Hwfv Hwftv HxR2).
    exact Hw2.
  (* S_Poly *)
  - intros L Delta RGamma R S Hs IHs sigma tau Hg Ht Hctx v Hv.
    rewrite close_rty_poly in Hv. rewrite V_Poly in Hv. destruct Hv as [Hval [Hfv [Hftv Hbody]]].
    rewrite close_rty_poly. rewrite V_Poly. split; [exact Hval | split; [exact Hfv | split; [exact Hftv |]]].
    intros U HlcU HfvU.
    destruct (Hbody U HlcU HfvU) as [u [Hmu Hu]].
    exists u. split; auto.
    set (X := fresh (L ++ ftv_rcontext RGamma ++ ftv_rty R ++ ftv_rty S ++ [])).
    assert (HxL : ~ In X L) by (subst X; apply fresh_notin1).
    assert (Hxctx : ~ In X (ftv_rcontext RGamma)) by (subst X; apply fresh_notin2).
    assert (HxR : ~ In X (ftv_rty R)) by (subst X; apply fresh_notin3).
    assert (HxS : ~ In X (ftv_rty S)) by (subst X; apply fresh_notin4).
    assert (Ht' : tenv_good (upd_ty tau X U)) by (apply tenv_good_upd; auto).
    assert (Hctx' : satisfies_context sigma (upd_ty tau X U) RGamma).
    { apply satisfies_context_update_ty; auto. }
    pose proof (IHs X HxL sigma (upd_ty tau X U) Hg Ht' Hctx' u) as Hfin.
    rewrite <- (close_rty_open_ty_fvar sigma tau S X U Hg Ht HlcU HfvU HxS).
    apply Hfin.
    rewrite (close_rty_open_ty_fvar sigma tau R X U Hg Ht HlcU HfvU HxR).
    exact Hu.
  (* S_Trans *)
  - intros Delta RGamma R S U Hs1 IHs1 Hs2 IHs2 sigma tau Hg Ht Hctx v Hv.
    apply (IHs2 sigma tau Hg Ht Hctx). apply (IHs1 sigma tau Hg Ht Hctx). exact Hv.
Qed.

Lemma fund : forall Delta RGamma t R (H : has_rtype Delta RGamma t R),
  forall sigma tau, env_good sigma -> tenv_good tau ->
  satisfies_context sigma tau RGamma -> T (close_rty sigma tau R) (close_tm sigma tau t).
Proof.
  intros Delta RGamma t R H sigma tau Hg Ht Hctx.
  exact (proj1 fund_and_subtype Delta RGamma t R H sigma tau Hg Ht Hctx).
Qed.

Lemma subtype_sound : forall Delta RGamma R S (H : subtype Delta RGamma R S),
  forall sigma tau, env_good sigma -> tenv_good tau ->
  satisfies_context sigma tau RGamma ->
  forall v, V (close_rty sigma tau R) v -> V (close_rty sigma tau S) v.
Proof.
  intros Delta RGamma R S H sigma tau Hg Ht Hctx v Hv.
  exact (proj2 fund_and_subtype Delta RGamma R S H sigma tau Hg Ht Hctx v Hv).
Qed.

(* ---------- determinism of the small-step relation ---------- *)

Ltac close_step_contra :=
  exfalso;
  match goal with
  | Hv : value ?v, Hs : ?v --> ?w |- _ => exact (value_no_step v w Hv Hs)
  | Hlc : locally_closed_tm (tm_abs ?T0 ?b), Hs : tm_abs ?T0 ?b --> ?w |- _ =>
      exact (value_no_step (tm_abs T0 b) w (v_abs T0 b Hlc) Hs)
  | Hlc : locally_closed_tm (tm_tabs ?b), Hs : tm_tabs ?b --> ?w |- _ =>
      exact (value_no_step (tm_tabs b) w (v_tabs b Hlc) Hs)
  | Hs : tm_int ?n --> ?w |- _ =>
      exact (value_no_step (tm_int n) w (v_int n) Hs)
  end.

Ltac close_step_goal :=
  try reflexivity;
  try assumption;
  try close_step_contra;
  try (intros; close_step_contra);
  try (f_equal; eauto).

Lemma step_det : forall t a b, t --> a -> t --> b -> a = b.
Proof.
  intros t. induction t as [i|x|T body IH|t1 IH1 t2 IH2|body IH|t T0 IH|n|t1 IH1 t2 IH2|op t1 IH1 t2 IH2];
    intros a b Ha Hb.
  - inversion Ha.
  - inversion Ha.
  - inversion Ha.
  - inversion Ha; subst; inversion Hb; subst; close_step_goal.
    all: try close_step_contra.
  - inversion Ha.
  - inversion Ha; subst; inversion Hb; subst; close_step_goal.
    all: try close_step_contra.
  - inversion Ha.
  - inversion Ha; subst; inversion Hb; subst; close_step_goal.
    all: try close_step_contra.
    all: try (match goal with |- ?G => idtac "DIVLEFT:" G end).
  - inversion Ha; subst; inversion Hb; subst; close_step_goal.
    all: try close_step_contra.
    all: try (match goal with |- ?G => idtac "ARITHLEFT:" G end).
Qed.

(* ---------- prefixes of multi-step reductions ---------- *)

Lemma multi_prefix : forall t u v, t --> u -> multi t v -> v = t \/ multi u v.
Proof.
  intros t u v Hstep Hm. revert u Hstep.
  induction Hm as [x|a b c Hstep' Hm' IH]; intros u Hstep.
  - left. reflexivity.
  - right.
    assert (E : u = b) by (apply (step_det a u b Hstep Hstep')).
    subst u. exact Hm'.
Qed.

(* ---------- reachability to a value implies safety ---------- *)

Lemma multi_value_safe : forall t v, multi t v -> value v ->
  forall t', multi t t' -> value t' \/ exists t'', t' --> t''.
Proof.
  intros t v Hm. induction Hm as [x|a b c Hstep Hm' IH]; intros Hv t' H'.
  - left. assert (E : t' = x) by (apply (multi_value_inv x t' Hv H')). subst t'. exact Hv.
  - destruct (multi_prefix a b t' Hstep H') as [E|Hm''].
    + subst t'. right. exists b. exact Hstep.
    + apply (IH Hv t' Hm'').
Qed.

End SystemFRefinementSemantics.

Module SystemFRefinementTask.
Import ListNotations SystemFRefinement SystemFRefinementLogic SystemFRefinementTyping SystemFRefinementEvaluation SystemFRefinementSemantics.

Theorem never_stuck : forall (t t' : tm) (R : rty),
  has_rtype [] empty_rcontext t R ->
  multi t t' ->
  value t' \/ exists t'' : tm, t' --> t''.
Proof.
  intros t t' R Hrt Hmulti.
  destruct (has_rtype_fv [] empty_rcontext t R Hrt) as [Hfv Hftv].
  assert (Hfvnil : fv_tm t = []).
  { destruct (fv_tm t) as [|a l] eqn:E; auto. exfalso.
    destruct (Hfv a) as [R0 H0]. { left. reflexivity. }
    simpl in H0. discriminate H0. }
  assert (Hftvnil : ftv_tm t = []).
  { destruct (ftv_tm t) as [|a l] eqn:E; auto. exfalso.
    exact (Hftv a (or_introl eq_refl)). }
  set (sigma0 := fun (_ : atom) => tm_int 0%Z).
  set (tau0 := fun (_ : atom) => Ty_Int).
  assert (Hg : env_good sigma0).
  { intros x. unfold sigma0. split; [apply v_int | split; [reflexivity | reflexivity]]. }
  assert (Ht0 : tenv_good tau0).
  { intros X. unfold tau0. split; [apply lc_ty_int | reflexivity]. }
  assert (Hctx : satisfies_context sigma0 tau0 empty_rcontext).
  { intros x R0 Hlk. simpl in Hlk. discriminate Hlk. }
  pose proof (fund [] empty_rcontext t R Hrt sigma0 tau0 Hg Ht0 Hctx) as Hfund.
  assert (Hclose : close_tm sigma0 tau0 t = t).
  { apply close_tm_of_closed; auto. }
  rewrite Hclose in Hfund.
  destruct Hfund as [v [Hmv Hv]].
  exact (multi_value_safe t v Hmv (V_value (close_rty sigma0 tau0 R) v Hv) t' Hmulti).
Qed.

End SystemFRefinementTask.
