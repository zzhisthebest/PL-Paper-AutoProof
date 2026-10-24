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

(* ================= Part 1: substitution infrastructure ================= *)
(* ================= Part 1: substitution infrastructure ================= *)
Module SystemFRefinementSemantics.
Import ListNotations.
Import SystemFRefinement SystemFRefinementLogic SystemFRefinementTyping SystemFRefinementEvaluation.

Definition type_ok (tau : atom -> ty) : Prop :=
  forall X, locally_closed_ty (tau X).
Definition term_ok (s : atom -> tm) : Prop :=
  forall x, locally_closed_tm (s x).

(* ---------- freshness helpers ---------- *)
Lemma max_atom_spec : forall (L : list atom) (x : atom),
  In x L -> x <= max_atom L.
Proof.
  induction L as [|y L IH]; intros x Hin; simpl in *.
  - contradiction.
  - destruct Hin as [->|Hin].
    + apply Nat.le_max_l.
    + apply Nat.le_trans with (max_atom L); [apply IH; auto|apply Nat.le_max_r].
Qed.

Lemma fresh_not_in : forall (L : list atom), ~ In (fresh L) L.
Proof.
  intros L Hin. unfold fresh in Hin.
  pose proof (max_atom_spec L (S (max_atom L)) Hin). lia.
Qed.

Lemma fresh_neq : forall (L : list atom) (x : atom), In x L -> fresh L <> x.
Proof.
  intros L x Hin Heq. apply (fresh_not_in L). rewrite Heq. auto.
Qed.

Lemma not_in_app : forall (x : atom) (L1 L2 : list atom),
  ~ In x (L1 ++ L2) -> ~ In x L1 /\ ~ In x L2.
Proof.
  intros x L1 L2 H. split; intros Hx; apply H; apply in_or_app; auto.
Qed.

Lemma fresh_not_in_lists : forall (L1 L2 : list atom), ~ In (fresh (L1 ++ L2)) L1.
Proof. intros. apply (proj1 (not_in_app _ _ _ (fresh_not_in _))). Qed.

(* ---------- simultaneous type/term substitution ---------- *)
Fixpoint mty (tau : atom -> ty) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => tau X
  | Ty_Arrow T1 T2 => Ty_Arrow (mty tau T1) (mty tau T2)
  | Ty_All T1 => Ty_All (mty tau T1)
  | Ty_Int => Ty_Int
  end.

Fixpoint mtm (tau : atom -> ty) (s : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => s x
  | tm_abs T t1 => tm_abs (mty tau T) (mtm tau s t1)
  | tm_app t1 t2 => tm_app (mtm tau s t1) (mtm tau s t2)
  | tm_tabs t1 => tm_tabs (mtm tau s t1)
  | tm_tapp t1 T => tm_tapp (mtm tau s t1) (mty tau T)
  | tm_int n => tm_int n
  | tm_div t1 t2 => tm_div (mtm tau s t1) (mtm tau s t2)
  | tm_arith op t1 t2 => tm_arith op (mtm tau s t1) (mtm tau s t2)
  end.

Fixpoint mqual (tau : atom -> ty) (s : atom -> tm) (p : qualifier) : qualifier :=
  match p with
  | Pred_True => Pred_True
  | Pred_False => Pred_False
  | Pred_Eq t1 t2 => Pred_Eq (mtm tau s t1) (mtm tau s t2)
  | Pred_Lt t1 t2 => Pred_Lt (mtm tau s t1) (mtm tau s t2)
  | Pred_Le t1 t2 => Pred_Le (mtm tau s t1) (mtm tau s t2)
  | Pred_And p1 p2 => Pred_And (mqual tau s p1) (mqual tau s p2)
  | Pred_Or p1 p2 => Pred_Or (mqual tau s p1) (mqual tau s p2)
  | Pred_Not p1 => Pred_Not (mqual tau s p1)
  end.

Fixpoint mrty (tau : atom -> ty) (s : atom -> tm) (R : rty) : rty :=
  match R with
  | R_Refine T p => R_Refine (mty tau T) (mqual tau s p)
  | R_Func R1 R2 => R_Func (mrty tau s R1) (mrty tau s R2)
  | R_Exists R1 R2 => R_Exists (mrty tau s R1) (mrty tau s R2)
  | R_Poly R => R_Poly (mrty tau s R)
  end.

(* ---------- monotonicity of locally-closed judgments ---------- *)
Lemma lc_ty_mono : forall K T, lc_ty_at K T -> forall K', K <= K' -> lc_ty_at K' T.
Proof.
  intros K T H. induction H; intros K' Hle; simpl.
  - constructor. lia.
  - constructor.
  - constructor; auto.
  - constructor. apply IHlc_ty_at. lia.
  - constructor.
Qed.

Lemma lc_tm_mono : forall K k t, lc_tm_at K k t ->
  forall K' k', K <= K' -> k <= k' -> lc_tm_at K' k' t.
Proof.
  intros K k t H. induction H; intros K' k' HK Hk; simpl.
  - constructor. lia.
  - constructor.
  - constructor; [apply lc_ty_mono with (K:=K); auto| apply IHlc_tm_at; lia].
  - constructor; auto.
  - constructor. apply IHlc_tm_at; lia.
  - constructor; [auto | apply lc_ty_mono with (K:=K); auto].
  - constructor.
  - constructor; auto.
  - constructor; auto.
Qed.

Lemma lc_pred_mono : forall K k p, lc_pred_at K k p ->
  forall K' k', K <= K' -> k <= k' -> lc_pred_at K' k' p.
Proof.
  intros K k p H. induction H; intros K' k' HK Hk; simpl.
  - constructor.
  - constructor.
  - constructor; apply lc_tm_mono with (K:=K) (k:=k); auto.
  - constructor; apply lc_tm_mono with (K:=K) (k:=k); auto.
  - constructor; apply lc_tm_mono with (K:=K) (k:=k); auto.
  - constructor; auto.
  - constructor; auto.
  - constructor; auto.
Qed.

Lemma lc_rty_mono : forall K k R, lc_rty_at K k R ->
  forall K' k', K <= K' -> k <= k' -> lc_rty_at K' k' R.
Proof.
  intros K k R H. induction H; intros K' k' HK Hk; simpl.
  - constructor.
    exact (lc_ty_mono K T H K' HK).
    exact (lc_pred_mono K (S k) ps H0 K' (S k') HK (le_n_S k k' Hk)).
  - constructor.
    exact (IHlc_rty_at1 K' k' HK Hk).
    exact (IHlc_rty_at2 K' (S k') HK (le_n_S k k' Hk)).
  - constructor.
    exact (IHlc_rty_at1 K' k' HK Hk).
    exact (IHlc_rty_at2 K' (S k') HK (le_n_S k k' Hk)).
  - constructor. exact (IHlc_rty_at (S K') k' (le_n_S K K' HK) Hk).
Qed.

Definition lc_ty_any (U : ty) : Prop := forall K, lc_ty_at K U.
Definition lc_tm_any (u : tm) : Prop := forall K k, lc_tm_at K k u.

Lemma lc_ty_any_intro : forall U, locally_closed_ty U -> lc_ty_any U.
Proof. intros U H K. exact (lc_ty_mono 0 U H K (Nat.le_0_l K)). Qed.

Lemma lc_tm_any_intro : forall t, locally_closed_tm t -> lc_tm_any t.
Proof. intros t H K k. exact (lc_tm_mono 0 0 t H K k (Nat.le_0_l K) (Nat.le_0_l k)). Qed.

Lemma lc_ty_any_fvar : forall X, lc_ty_any (Ty_FVar X).
Proof. intros X K. constructor. Qed.

Lemma lc_tm_any_fvar : forall x, lc_tm_any (tm_fvar x).
Proof. intros x K k. constructor. Qed.

Lemma lc_ty_at_0 : forall (T : ty) K, lc_ty_at 0 T -> lc_ty_at K T.
Proof. intros T K H. exact (lc_ty_mono 0 T H K (Nat.le_0_l K)). Qed.

Lemma lc_tm_at_00 : forall (t : tm) K k, lc_tm_at 0 0 t -> lc_tm_at K k t.
Proof. intros t K k H. exact (lc_tm_mono 0 0 t H K k (Nat.le_0_l K) (Nat.le_0_l k)). Qed.


(* ---------- opening locally-closed objects does nothing ---------- *)
Lemma open_ty_lc_id : forall k (U T : ty),
  lc_ty_at k T -> open_ty_rec k U T = T.
Proof.
  intros k U T H. induction H as [k i Hi | k X | k T1 T2 H1 IH1 H2 IH2 | k T H IH | k].
  - simpl. destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. exfalso. lia.
    + reflexivity.
  - reflexivity.
  - simpl. rewrite IH1. rewrite IH2. reflexivity.
  - simpl. rewrite IH. reflexivity.
  - reflexivity.
Qed.

Lemma open_tm_lc_id : forall (K k : nat) (u t : tm),
  lc_tm_at K k t -> open_tm_rec k u t = t.
Proof.
  intros K k u t H.
  induction H as [K k i Hi | K k x | K k T t Hty Htm IH | K k t1 t2 H1 IH1 H2 IH2
                 | K k t Ht IH | K k t T Ht IH Hty | K k n
                 | K k t1 t2 H1 IH1 H2 IH2 | K k op t1 t2 H1 IH1 H2 IH2].
  - simpl. destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. exfalso. lia.
    + reflexivity.
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
  - simpl. rewrite IH1. rewrite IH2. reflexivity.
  - simpl. rewrite IH. reflexivity.
  - simpl. rewrite IH. reflexivity.
  - reflexivity.
  - simpl. rewrite IH1. rewrite IH2. reflexivity.
  - simpl. rewrite IH1. rewrite IH2. reflexivity.
Qed.

Lemma open_tm_ty_lc_id : forall (K k : nat) (U : ty) (t : tm),
  lc_tm_at K k t -> open_tm_ty_rec K U t = t.
Proof.
  intros K k U t H.
  induction H as [K k i Hi | K k x | K k T t Hty Htm IH | K k t1 t2 H1 IH1 H2 IH2
                 | K k t Ht IH | K k t T Ht IH Hty | K k n
                 | K k t1 t2 H1 IH1 H2 IH2 | K k op t1 t2 H1 IH1 H2 IH2].
  - reflexivity.
  - reflexivity.
  - simpl. rewrite (open_ty_lc_id K U T Hty). rewrite IH. reflexivity.
  - simpl. rewrite IH1. rewrite IH2. reflexivity.
  - simpl. rewrite IH. reflexivity.
  - simpl. rewrite (open_ty_lc_id K U T Hty). rewrite IH. reflexivity.
  - reflexivity.
  - simpl. rewrite IH1. rewrite IH2. reflexivity.
  - simpl. rewrite IH1. rewrite IH2. reflexivity.
Qed.

Lemma open_pred_tm_lc_id : forall (K k : nat) (u : tm) (p : qualifier),
  lc_pred_at K k p -> open_pred_tm_rec k u p = p.
Proof.
  intros K k u p H.
  induction H as [K k | K k | K k t1 t2 H1 H2 | K k t1 t2 H1 H2 | K k t1 t2 H1 H2
                 | K k p1 p2 H1 IH1 H2 IH2 | K k p1 p2 H1 IH1 H2 IH2 | K k p H IH].
  - reflexivity.
  - reflexivity.
  - simpl. rewrite (open_tm_lc_id K k u t1 H1). rewrite (open_tm_lc_id K k u t2 H2). reflexivity.
  - simpl. rewrite (open_tm_lc_id K k u t1 H1). rewrite (open_tm_lc_id K k u t2 H2). reflexivity.
  - simpl. rewrite (open_tm_lc_id K k u t1 H1). rewrite (open_tm_lc_id K k u t2 H2). reflexivity.
  - simpl. rewrite IH1. rewrite IH2. reflexivity.
  - simpl. rewrite IH1. rewrite IH2. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma open_pred_ty_lc_id : forall (K k : nat) (U : ty) (p : qualifier),
  lc_pred_at K k p -> open_pred_ty_rec K U p = p.
Proof.
  intros K k U p H.
  induction H as [K k | K k | K k t1 t2 H1 H2 | K k t1 t2 H1 H2 | K k t1 t2 H1 H2
                 | K k p1 p2 H1 IH1 H2 IH2 | K k p1 p2 H1 IH1 H2 IH2 | K k p H IH].
  - reflexivity.
  - reflexivity.
  - simpl. rewrite (open_tm_ty_lc_id K k U t1 H1). rewrite (open_tm_ty_lc_id K k U t2 H2). reflexivity.
  - simpl. rewrite (open_tm_ty_lc_id K k U t1 H1). rewrite (open_tm_ty_lc_id K k U t2 H2). reflexivity.
  - simpl. rewrite (open_tm_ty_lc_id K k U t1 H1). rewrite (open_tm_ty_lc_id K k U t2 H2). reflexivity.
  - simpl. rewrite IH1. rewrite IH2. reflexivity.
  - simpl. rewrite IH1. rewrite IH2. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma open_rty_tm_lc_id : forall (K k : nat) (u : tm) (R : rty),
  lc_rty_at K k R -> open_rty_tm_rec k u R = R.
Proof.
  intros K k u R H.
  induction H as [K k T ps Hty Hps | K k R1 R2 H1 IH1 H2 IH2
                 | K k R1 R2 H1 IH1 H2 IH2 | K k R H IH].
  - simpl. unfold open_qualifier_tm_rec.
    rewrite (open_pred_tm_lc_id K (S k) u ps Hps). reflexivity.
  - simpl. rewrite IH1. rewrite IH2. reflexivity.
  - simpl. rewrite IH1. rewrite IH2. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma open_rty_ty_lc_id : forall (K k : nat) (U : ty) (R : rty),
  lc_rty_at K k R -> open_rty_ty_rec K U R = R.
Proof.
  intros K k U R H.
  induction H as [K k T ps Hty Hps | K k R1 R2 H1 IH1 H2 IH2
                 | K k R1 R2 H1 IH1 H2 IH2 | K k R H IH].
  - simpl. rewrite (open_ty_lc_id K U T Hty). unfold open_qualifier_ty_rec.
    rewrite (open_pred_ty_lc_id K (S k) U ps Hps). reflexivity.
  - simpl. rewrite IH1. rewrite IH2. reflexivity.
  - simpl. rewrite IH1. rewrite IH2. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(* ---------- commutation with opening ---------- *)
Lemma mty_open_ty : forall (tau : atom -> ty) k (U T : ty),
  type_ok tau ->
  mty tau (open_ty_rec k U T) = open_ty_rec k (mty tau U) (mty tau T).
Proof.
  intros tau k U T Hok. revert k U.
  induction T as [n | a | T1 IH1 T2 IH2 | T IH |]; intros k U; simpl.
  - destruct (Nat.eqb k n); simpl; reflexivity.
  - rewrite (open_ty_lc_id k (mty tau U) (tau a) (lc_ty_at_0 (tau a) k (Hok a))).
    reflexivity.
  - rewrite (IH1 k U). rewrite (IH2 k U). reflexivity.
  - rewrite (IH (S k) U). reflexivity.
  - reflexivity.
Qed.

Lemma mtm_open_tm : forall (tau : atom -> ty) (s : atom -> tm) k (u t : tm),
  type_ok tau -> term_ok s ->
  mtm tau s (open_tm_rec k u t) = open_tm_rec k (mtm tau s u) (mtm tau s t).
Proof.
  intros tau s k u t Hok Hs. revert k u.
  induction t as [n | x | T t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 T | n | t1 IH1 t2 IH2 | op t1 IH1 t2 IH2];
    intros k u; simpl.
  - destruct (Nat.eqb k n); simpl; reflexivity.
  - rewrite (open_tm_lc_id 0 k (mtm tau s u) (s x) (lc_tm_at_00 (s x) 0 k (Hs x))).
    reflexivity.
  - rewrite (IH1 (S k) u). reflexivity.
  - rewrite (IH1 k u). rewrite (IH2 k u). reflexivity.
  - rewrite (IH1 k u). reflexivity.
  - rewrite (IH1 k u). reflexivity.
  - reflexivity.
  - rewrite (IH1 k u). rewrite (IH2 k u). reflexivity.
  - rewrite (IH1 k u). rewrite (IH2 k u). reflexivity.
Qed.

Lemma mtm_open_tm_ty : forall (tau : atom -> ty) (s : atom -> tm) k (U : ty) (t : tm),
  type_ok tau -> term_ok s ->
  mtm tau s (open_tm_ty_rec k U t) = open_tm_ty_rec k (mty tau U) (mtm tau s t).
Proof.
  intros tau s k U t Hok Hs. revert k U.
  induction t as [n | x | T t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 T | n | t1 IH1 t2 IH2 | op t1 IH1 t2 IH2];
    intros k U; simpl.
  - reflexivity.
  - rewrite (open_tm_ty_lc_id k 0 (mty tau U) (s x) (lc_tm_at_00 (s x) k 0 (Hs x))).
    reflexivity.
  - rewrite (mty_open_ty tau k U T Hok). rewrite (IH1 k U). reflexivity.
  - rewrite (IH1 k U). rewrite (IH2 k U). reflexivity.
  - rewrite (IH1 (S k) U). reflexivity.
  - rewrite (mty_open_ty tau k U T Hok). rewrite (IH1 k U). reflexivity.
  - reflexivity.
  - rewrite (IH1 k U). rewrite (IH2 k U). reflexivity.
  - rewrite (IH1 k U). rewrite (IH2 k U). reflexivity.
Qed.

Lemma mqual_open_tm : forall (tau : atom -> ty) (s : atom -> tm) k (u : tm) (p : qualifier),
  type_ok tau -> term_ok s ->
  mqual tau s (open_qualifier_tm_rec k u p)
  = open_qualifier_tm_rec k (mtm tau s u) (mqual tau s p).
Proof.
  intros tau s k u p Hok Hs. revert k u.
  induction p as [ | | t1 t2 | t1 t2 | t1 t2 | p1 IH1 p2 IH2 | p1 IH1 p2 IH2 | p IH];
    intros k u; simpl; try reflexivity.
  - rewrite (mtm_open_tm tau s k u t1 Hok Hs). rewrite (mtm_open_tm tau s k u t2 Hok Hs). reflexivity.
  - rewrite (mtm_open_tm tau s k u t1 Hok Hs). rewrite (mtm_open_tm tau s k u t2 Hok Hs). reflexivity.
  - rewrite (mtm_open_tm tau s k u t1 Hok Hs). rewrite (mtm_open_tm tau s k u t2 Hok Hs). reflexivity.
  - rewrite (IH1 k u). rewrite (IH2 k u). reflexivity.
  - rewrite (IH1 k u). rewrite (IH2 k u). reflexivity.
  - rewrite (IH k u). reflexivity.
Qed.

Lemma mqual_open_ty : forall (tau : atom -> ty) (s : atom -> tm) k (U : ty) (p : qualifier),
  type_ok tau -> term_ok s ->
  mqual tau s (open_pred_ty_rec k U p)
  = open_pred_ty_rec k (mty tau U) (mqual tau s p).
Proof.
  intros tau s k U p Hok Hs. revert k U.
  induction p as [ | | t1 t2 | t1 t2 | t1 t2 | p1 IH1 p2 IH2 | p1 IH1 p2 IH2 | p IH];
    intros k U; simpl; try reflexivity.
  - rewrite (mtm_open_tm_ty tau s k U t1 Hok Hs). rewrite (mtm_open_tm_ty tau s k U t2 Hok Hs). reflexivity.
  - rewrite (mtm_open_tm_ty tau s k U t1 Hok Hs). rewrite (mtm_open_tm_ty tau s k U t2 Hok Hs). reflexivity.
  - rewrite (mtm_open_tm_ty tau s k U t1 Hok Hs). rewrite (mtm_open_tm_ty tau s k U t2 Hok Hs). reflexivity.
  - rewrite (IH1 k U). rewrite (IH2 k U). reflexivity.
  - rewrite (IH1 k U). rewrite (IH2 k U). reflexivity.
  - rewrite (IH k U). reflexivity.
Qed.

Lemma mrty_open_tm : forall (tau : atom -> ty) (s : atom -> tm) k (u : tm) (R : rty),
  type_ok tau -> term_ok s ->
  mrty tau s (open_rty_tm_rec k u R)
  = open_rty_tm_rec k (mtm tau s u) (mrty tau s R).
Proof.
  intros tau s k u R Hok Hs. revert k u.
  induction R as [T p | R1 IH1 R2 IH2 | R1 IH1 R2 IH2 | R IH]; intros k u; simpl.
  - rewrite (mqual_open_tm tau s (S k) u p Hok Hs). reflexivity.
  - rewrite (IH1 k u). rewrite (IH2 (S k) u). reflexivity.
  - rewrite (IH1 k u). rewrite (IH2 (S k) u). reflexivity.
  - rewrite (IH k u). reflexivity.
Qed.

Lemma mrty_open_ty : forall (tau : atom -> ty) (s : atom -> tm) k (U : ty) (R : rty),
  type_ok tau -> term_ok s ->
  mrty tau s (open_rty_ty_rec k U R)
  = open_rty_ty_rec k (mty tau U) (mrty tau s R).
Proof.
  intros tau s k U R Hok Hs. revert k U.
  induction R as [T p | R1 IH1 R2 IH2 | R1 IH1 R2 IH2 | R IH]; intros k U; simpl.
  - rewrite (mty_open_ty tau k U T Hok). unfold open_qualifier_ty_rec.
    rewrite (mqual_open_ty tau s k U p Hok Hs). reflexivity.
  - rewrite (IH1 k U). rewrite (IH2 k U). reflexivity.
  - rewrite (IH1 k U). rewrite (IH2 k U). reflexivity.
  - rewrite (IH (S k) U). reflexivity.
Qed.

Lemma mty_open_ty_fvar : forall (tau : atom -> ty) (X : atom) k (T : ty),
  type_ok tau ->
  mty tau (open_ty_rec k (Ty_FVar X) T)
  = open_ty_rec k (tau X) (mty tau T).
Proof. intros. apply mty_open_ty; auto. Qed.

Lemma mtm_open_tm_fvar : forall (tau : atom -> ty) (s : atom -> tm) (x : atom) k (t : tm),
  type_ok tau -> term_ok s ->
  mtm tau s (open_tm_rec k (tm_fvar x) t)
  = open_tm_rec k (s x) (mtm tau s t).
Proof. intros. apply mtm_open_tm; auto. Qed.

Lemma mrty_open_tm_fvar : forall (tau : atom -> ty) (s : atom -> tm) (x : atom) k (R : rty),
  type_ok tau -> term_ok s ->
  mrty tau s (open_rty_tm_rec k (tm_fvar x) R)
  = open_rty_tm_rec k (s x) (mrty tau s R).
Proof. intros. apply mrty_open_tm; auto. Qed.

Lemma mrty_open_ty_fvar : forall (tau : atom -> ty) (s : atom -> tm) (X : atom) k (R : rty),
  type_ok tau -> term_ok s ->
  mrty tau s (open_rty_ty_rec k (Ty_FVar X) R)
  = open_rty_ty_rec k (tau X) (mrty tau s R).
Proof. intros. apply mrty_open_ty; auto. Qed.

(* ---------- free variable lists ---------- *)
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
  | R_Refine T p => fv_qual p
  | R_Func R1 R2 => fv_rty R1 ++ fv_rty R2
  | R_Exists R1 R2 => fv_rty R1 ++ fv_rty R2
  | R_Poly R => fv_rty R
  end.

Fixpoint ftv_rty (R : rty) : list atom :=
  match R with
  | R_Refine T p => fv_ty T ++ ftv_qual p
  | R_Func R1 R2 => ftv_rty R1 ++ ftv_rty R2
  | R_Exists R1 R2 => ftv_rty R1 ++ ftv_rty R2
  | R_Poly R => ftv_rty R
  end.

Definition fv_rcontext (RG : rcontext) : list atom :=
  flat_map (fun xR => fv_rty (snd xR)) RG.
Definition ftv_rcontext (RG : rcontext) : list atom :=
  flat_map (fun xR => ftv_rty (snd xR)) RG.
Definition keys_rcontext (RG : rcontext) : list atom := map fst RG.

(* ---------- substitution extensionality ---------- *)
Lemma in_app_l : forall (x : atom) (L1 L2 : list atom), In x L1 -> In x (L1 ++ L2).
Proof. intros. apply in_or_app. auto. Qed.
Lemma in_app_r : forall (x : atom) (L1 L2 : list atom), In x L2 -> In x (L1 ++ L2).
Proof. intros. apply in_or_app. auto. Qed.

Lemma mty_ftv_ext : forall (tau tau' : atom -> ty) (T : ty),
  (forall X, In X (fv_ty T) -> tau X = tau' X) ->
  mty tau T = mty tau' T.
Proof.
  intros tau tau' T H. induction T as [n | a | T1 IH1 T2 IH2 | T IH |].
  - reflexivity.
  - apply H. simpl. auto.
  - simpl. rewrite (IH1 (fun X HX => H X (in_app_l _ _ _ HX))).
    rewrite (IH2 (fun X HX => H X (in_app_r _ _ _ HX))). reflexivity.
  - simpl. rewrite (IH (fun X HX => H X HX)). reflexivity.
  - reflexivity.
Qed.

Lemma mtm_fv_ext : forall (tau : atom -> ty) (s s' : atom -> tm) (t : tm),
  (forall x, In x (fv_tm t) -> s x = s' x) ->
  mtm tau s t = mtm tau s' t.
Proof.
  intros tau s s' t H.
  induction t as [n | x | T t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 T | n | t1 IH1 t2 IH2 | op t1 IH1 t2 IH2].
  - reflexivity.
  - apply H. simpl. auto.
  - simpl. rewrite (IH1 (fun y Hy => H y Hy)). reflexivity.
  - simpl. rewrite (IH1 (fun y Hy => H y (in_app_l _ _ _ Hy))).
    rewrite (IH2 (fun y Hy => H y (in_app_r _ _ _ Hy))). reflexivity.
  - simpl. rewrite (IH1 (fun y Hy => H y Hy)). reflexivity.
  - simpl. rewrite (IH1 (fun y Hy => H y Hy)). reflexivity.
  - reflexivity.
  - simpl. rewrite (IH1 (fun y Hy => H y (in_app_l _ _ _ Hy))).
    rewrite (IH2 (fun y Hy => H y (in_app_r _ _ _ Hy))). reflexivity.
  - simpl. rewrite (IH1 (fun y Hy => H y (in_app_l _ _ _ Hy))).
    rewrite (IH2 (fun y Hy => H y (in_app_r _ _ _ Hy))). reflexivity.
Qed.

Lemma mtm_ftv_ext : forall (tau tau' : atom -> ty) (s : atom -> tm) (t : tm),
  (forall X, In X (ftv_tm t) -> tau X = tau' X) ->
  mtm tau s t = mtm tau' s t.
Proof.
  intros tau tau' s t H.
  induction t as [n | x | T t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 T | n | t1 IH1 t2 IH2 | op t1 IH1 t2 IH2].
  - reflexivity.
  - reflexivity.
  - simpl. rewrite (mty_ftv_ext tau tau' T (fun X HX => H X (in_app_l _ _ _ HX))).
    rewrite (IH1 (fun X HX => H X (in_app_r _ _ _ HX))). reflexivity.
  - simpl. rewrite (IH1 (fun X HX => H X (in_app_l _ _ _ HX))).
    rewrite (IH2 (fun X HX => H X (in_app_r _ _ _ HX))). reflexivity.
  - simpl. rewrite (IH1 (fun X HX => H X HX)). reflexivity.
  - simpl. rewrite (IH1 (fun X HX => H X (in_app_l _ _ _ HX))).
    rewrite (mty_ftv_ext tau tau' T (fun X HX => H X (in_app_r _ _ _ HX))). reflexivity.
  - reflexivity.
  - simpl. rewrite (IH1 (fun X HX => H X (in_app_l _ _ _ HX))).
    rewrite (IH2 (fun X HX => H X (in_app_r _ _ _ HX))). reflexivity.
  - simpl. rewrite (IH1 (fun X HX => H X (in_app_l _ _ _ HX))).
    rewrite (IH2 (fun X HX => H X (in_app_r _ _ _ HX))). reflexivity.
Qed.

Lemma mqual_fv_ext : forall (tau : atom -> ty) (s s' : atom -> tm) (p : qualifier),
  (forall x, In x (fv_qual p) -> s x = s' x) ->
  mqual tau s p = mqual tau s' p.
Proof.
  intros tau s s' p H.
  induction p as [ | | t1 t2 | t1 t2 | t1 t2 | p1 IH1 p2 IH2 | p1 IH1 p2 IH2 | p IH].
  - reflexivity.
  - reflexivity.
  - simpl. rewrite (mtm_fv_ext tau s s' t1 (fun y Hy => H y (in_app_l _ _ _ Hy))).
    rewrite (mtm_fv_ext tau s s' t2 (fun y Hy => H y (in_app_r _ _ _ Hy))). reflexivity.
  - simpl. rewrite (mtm_fv_ext tau s s' t1 (fun y Hy => H y (in_app_l _ _ _ Hy))).
    rewrite (mtm_fv_ext tau s s' t2 (fun y Hy => H y (in_app_r _ _ _ Hy))). reflexivity.
  - simpl. rewrite (mtm_fv_ext tau s s' t1 (fun y Hy => H y (in_app_l _ _ _ Hy))).
    rewrite (mtm_fv_ext tau s s' t2 (fun y Hy => H y (in_app_r _ _ _ Hy))). reflexivity.
  - simpl. rewrite (IH1 (fun y Hy => H y (in_app_l _ _ _ Hy))).
    rewrite (IH2 (fun y Hy => H y (in_app_r _ _ _ Hy))). reflexivity.
  - simpl. rewrite (IH1 (fun y Hy => H y (in_app_l _ _ _ Hy))).
    rewrite (IH2 (fun y Hy => H y (in_app_r _ _ _ Hy))). reflexivity.
  - simpl. rewrite (IH (fun y Hy => H y Hy)). reflexivity.
Qed.

Lemma mqual_ftv_ext : forall (tau tau' : atom -> ty) (s : atom -> tm) (p : qualifier),
  (forall X, In X (ftv_qual p) -> tau X = tau' X) ->
  mqual tau s p = mqual tau' s p.
Proof.
  intros tau tau' s p H.
  induction p as [ | | t1 t2 | t1 t2 | t1 t2 | p1 IH1 p2 IH2 | p1 IH1 p2 IH2 | p IH].
  - reflexivity.
  - reflexivity.
  - simpl. rewrite (mtm_ftv_ext tau tau' s t1 (fun X HX => H X (in_app_l _ _ _ HX))).
    rewrite (mtm_ftv_ext tau tau' s t2 (fun X HX => H X (in_app_r _ _ _ HX))). reflexivity.
  - simpl. rewrite (mtm_ftv_ext tau tau' s t1 (fun X HX => H X (in_app_l _ _ _ HX))).
    rewrite (mtm_ftv_ext tau tau' s t2 (fun X HX => H X (in_app_r _ _ _ HX))). reflexivity.
  - simpl. rewrite (mtm_ftv_ext tau tau' s t1 (fun X HX => H X (in_app_l _ _ _ HX))).
    rewrite (mtm_ftv_ext tau tau' s t2 (fun X HX => H X (in_app_r _ _ _ HX))). reflexivity.
  - simpl. rewrite (IH1 (fun X HX => H X (in_app_l _ _ _ HX))).
    rewrite (IH2 (fun X HX => H X (in_app_r _ _ _ HX))). reflexivity.
  - simpl. rewrite (IH1 (fun X HX => H X (in_app_l _ _ _ HX))).
    rewrite (IH2 (fun X HX => H X (in_app_r _ _ _ HX))). reflexivity.
  - simpl. rewrite (IH (fun X HX => H X HX)). reflexivity.
Qed.

Lemma mrty_fv_ext : forall (tau : atom -> ty) (s s' : atom -> tm) (R : rty),
  (forall x, In x (fv_rty R) -> s x = s' x) ->
  mrty tau s R = mrty tau s' R.
Proof.
  intros tau s s' R H.
  induction R as [T p | R1 IH1 R2 IH2 | R1 IH1 R2 IH2 | R IH].
  - simpl. rewrite (mqual_fv_ext tau s s' p (fun y Hy => H y Hy)). reflexivity.
  - simpl. rewrite (IH1 (fun y Hy => H y (in_app_l _ _ _ Hy))).
    rewrite (IH2 (fun y Hy => H y (in_app_r _ _ _ Hy))). reflexivity.
  - simpl. rewrite (IH1 (fun y Hy => H y (in_app_l _ _ _ Hy))).
    rewrite (IH2 (fun y Hy => H y (in_app_r _ _ _ Hy))). reflexivity.
  - simpl. rewrite (IH (fun y Hy => H y Hy)). reflexivity.
Qed.

Lemma mrty_ftv_ext : forall (tau tau' : atom -> ty) (s : atom -> tm) (R : rty),
  (forall X, In X (ftv_rty R) -> tau X = tau' X) ->
  mrty tau s R = mrty tau' s R.
Proof.
  intros tau tau' s R H.
  induction R as [T p | R1 IH1 R2 IH2 | R1 IH1 R2 IH2 | R IH].
  - simpl. rewrite (mty_ftv_ext tau tau' T (fun X HX => H X (in_app_l _ _ _ HX))).
    rewrite (mqual_ftv_ext tau tau' s p (fun X HX => H X (in_app_r _ _ _ HX))). reflexivity.
  - simpl. rewrite (IH1 (fun X HX => H X (in_app_l _ _ _ HX))).
    rewrite (IH2 (fun X HX => H X (in_app_r _ _ _ HX))). reflexivity.
  - simpl. rewrite (IH1 (fun X HX => H X (in_app_l _ _ _ HX))).
    rewrite (IH2 (fun X HX => H X (in_app_r _ _ _ HX))). reflexivity.
  - simpl. rewrite (IH (fun X HX => H X HX)). reflexivity.
Qed.

(* ---------- open / locally-closed correspondences ---------- *)
Lemma lc_ty_open_ty : forall K (U T : ty),
  lc_ty_any U ->
  (lc_ty_at K (open_ty_rec K U T) <-> lc_ty_at (S K) T).
Proof.
  intros K U T HU. revert K.
  induction T as [n | a | T1 IH1 T2 IH2 | T IH |]; intros K; simpl.
  - destruct (Nat.eqb K n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. split; intros H.
      * constructor. lia.
      * apply HU.
    + apply Nat.eqb_neq in E. split; intros H; inversion H; subst; constructor; lia.
  - split; intros H; constructor.
  - split; intros H.
    + pose proof (proj1 (IH1 K)) as P1. pose proof (proj1 (IH2 K)) as P2.
      inversion H; subst; constructor; eauto 10.
    + pose proof (proj2 (IH1 K)) as P1. pose proof (proj2 (IH2 K)) as P2.
      inversion H; subst; constructor; eauto 10.
  - split; intros H.
    + inversion H; subst. constructor. apply (proj1 (IH (S K))). assumption.
    + inversion H; subst. constructor. apply (proj2 (IH (S K))). assumption.
  - split; intros H; constructor.
Qed.

Lemma lc_tm_open_tm : forall K k (u t : tm),
  lc_tm_any u ->
  (lc_tm_at K k (open_tm_rec k u t) <-> lc_tm_at K (S k) t).
Proof.
  intros K k u t Hu. revert K k.
  induction t as [n | x | T t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 T | n | t1 IH1 t2 IH2 | op t1 IH1 t2 IH2];
    intros K k; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. split; intros H.
      * constructor. lia.
      * exact (Hu K k).
    + apply Nat.eqb_neq in E. split; intros H; inversion H; subst; constructor; lia.
  - split; intros H; constructor.
  - split; intros H.
    + pose proof (proj1 (IH1 K (S k))) as P. inversion H; subst; constructor; eauto 10.
    + pose proof (proj2 (IH1 K (S k))) as P. inversion H; subst; constructor; eauto 10.
  - split; intros H.
    + pose proof (proj1 (IH1 K k)) as P1. pose proof (proj1 (IH2 K k)) as P2.
      inversion H; subst; constructor; eauto 10.
    + pose proof (proj2 (IH1 K k)) as P1. pose proof (proj2 (IH2 K k)) as P2.
      inversion H; subst; constructor; eauto 10.
  - split; intros H.
    + pose proof (proj1 (IH1 (S K) k)) as P. inversion H; subst; constructor; eauto 10.
    + pose proof (proj2 (IH1 (S K) k)) as P. inversion H; subst; constructor; eauto 10.
  - split; intros H.
    + pose proof (proj1 (IH1 K k)) as P. inversion H; subst; constructor; eauto 10.
    + pose proof (proj2 (IH1 K k)) as P. inversion H; subst; constructor; eauto 10.
  - split; intros H; constructor.
  - split; intros H.
    + pose proof (proj1 (IH1 K k)) as P1. pose proof (proj1 (IH2 K k)) as P2.
      inversion H; subst; constructor; eauto 10.
    + pose proof (proj2 (IH1 K k)) as P1. pose proof (proj2 (IH2 K k)) as P2.
      inversion H; subst; constructor; eauto 10.
  - split; intros H.
    + pose proof (proj1 (IH1 K k)) as P1. pose proof (proj1 (IH2 K k)) as P2.
      inversion H; subst; constructor; eauto 10.
    + pose proof (proj2 (IH1 K k)) as P1. pose proof (proj2 (IH2 K k)) as P2.
      inversion H; subst; constructor; eauto 10.
Qed.

Lemma lc_tm_open_tm_ty : forall K k (U : ty) (t : tm),
  lc_ty_any U ->
  (lc_tm_at K k (open_tm_ty_rec K U t) <-> lc_tm_at (S K) k t).
Proof.
  intros K k U t HU. revert K k.
  induction t as [n | x | T t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 T | n | t1 IH1 t2 IH2 | op t1 IH1 t2 IH2];
    intros K k; simpl.
  - split; intros H; inversion H; subst; constructor; lia.
  - split; intros H; constructor.
  - split; intros H.
    + pose proof (proj1 (lc_ty_open_ty K U T HU)) as PT.
      pose proof (proj1 (IH1 K (S k))) as P. inversion H; subst; constructor; eauto 10.
    + pose proof (proj2 (lc_ty_open_ty K U T HU)) as PT.
      pose proof (proj2 (IH1 K (S k))) as P. inversion H; subst; constructor; eauto 10.
  - split; intros H.
    + pose proof (proj1 (IH1 K k)) as P1. pose proof (proj1 (IH2 K k)) as P2.
      inversion H; subst; constructor; eauto 10.
    + pose proof (proj2 (IH1 K k)) as P1. pose proof (proj2 (IH2 K k)) as P2.
      inversion H; subst; constructor; eauto 10.
  - split; intros H.
    + pose proof (proj1 (IH1 (S K) k)) as P. inversion H; subst; constructor; eauto 10.
    + pose proof (proj2 (IH1 (S K) k)) as P. inversion H; subst; constructor; eauto 10.
  - split; intros H.
    + pose proof (proj1 (lc_ty_open_ty K U T HU)) as PT.
      pose proof (proj1 (IH1 K k)) as P. inversion H; subst; constructor; eauto 10.
    + pose proof (proj2 (lc_ty_open_ty K U T HU)) as PT.
      pose proof (proj2 (IH1 K k)) as P. inversion H; subst; constructor; eauto 10.
  - split; intros H; constructor.
  - split; intros H.
    + pose proof (proj1 (IH1 K k)) as P1. pose proof (proj1 (IH2 K k)) as P2.
      inversion H; subst; constructor; eauto 10.
    + pose proof (proj2 (IH1 K k)) as P1. pose proof (proj2 (IH2 K k)) as P2.
      inversion H; subst; constructor; eauto 10.
  - split; intros H.
    + pose proof (proj1 (IH1 K k)) as P1. pose proof (proj1 (IH2 K k)) as P2.
      inversion H; subst; constructor; eauto 10.
    + pose proof (proj2 (IH1 K k)) as P1. pose proof (proj2 (IH2 K k)) as P2.
      inversion H; subst; constructor; eauto 10.
Qed.

Lemma lc_pred_open_tm : forall K k (u : tm) (p : qualifier),
  lc_tm_any u ->
  (lc_pred_at K k (open_pred_tm_rec k u p) <-> lc_pred_at K (S k) p).
Proof.
  intros K k u p Hu. revert K k.
  induction p as [ | | t1 t2 | t1 t2 | t1 t2 | p1 IH1 p2 IH2 | p1 IH1 p2 IH2 | p IH];
    intros K k; simpl.
  - split; intros H; constructor.
  - split; intros H; constructor.
  - split; intros H.
    + pose proof (proj1 (lc_tm_open_tm K k u t1 Hu)) as P1.
      pose proof (proj1 (lc_tm_open_tm K k u t2 Hu)) as P2.
      inversion H; subst; constructor; eauto 10.
    + pose proof (proj2 (lc_tm_open_tm K k u t1 Hu)) as P1.
      pose proof (proj2 (lc_tm_open_tm K k u t2 Hu)) as P2.
      inversion H; subst; constructor; eauto 10.
  - split; intros H.
    + pose proof (proj1 (lc_tm_open_tm K k u t1 Hu)) as P1.
      pose proof (proj1 (lc_tm_open_tm K k u t2 Hu)) as P2.
      inversion H; subst; constructor; eauto 10.
    + pose proof (proj2 (lc_tm_open_tm K k u t1 Hu)) as P1.
      pose proof (proj2 (lc_tm_open_tm K k u t2 Hu)) as P2.
      inversion H; subst; constructor; eauto 10.
  - split; intros H.
    + pose proof (proj1 (lc_tm_open_tm K k u t1 Hu)) as P1.
      pose proof (proj1 (lc_tm_open_tm K k u t2 Hu)) as P2.
      inversion H; subst; constructor; eauto 10.
    + pose proof (proj2 (lc_tm_open_tm K k u t1 Hu)) as P1.
      pose proof (proj2 (lc_tm_open_tm K k u t2 Hu)) as P2.
      inversion H; subst; constructor; eauto 10.
  - split; intros H.
    + pose proof (proj1 (IH1 K k)) as P1. pose proof (proj1 (IH2 K k)) as P2.
      inversion H; subst; constructor; eauto 10.
    + pose proof (proj2 (IH1 K k)) as P1. pose proof (proj2 (IH2 K k)) as P2.
      inversion H; subst; constructor; eauto 10.
  - split; intros H.
    + pose proof (proj1 (IH1 K k)) as P1. pose proof (proj1 (IH2 K k)) as P2.
      inversion H; subst; constructor; eauto 10.
    + pose proof (proj2 (IH1 K k)) as P1. pose proof (proj2 (IH2 K k)) as P2.
      inversion H; subst; constructor; eauto 10.
  - split; intros H.
    + pose proof (proj1 (IH K k)) as P. inversion H; subst; constructor; eauto 10.
    + pose proof (proj2 (IH K k)) as P. inversion H; subst; constructor; eauto 10.
Qed.

Lemma lc_pred_open_ty : forall K k (U : ty) (p : qualifier),
  lc_ty_any U ->
  (lc_pred_at K k (open_pred_ty_rec K U p) <-> lc_pred_at (S K) k p).
Proof.
  intros K k U p HU. revert K k.
  induction p as [ | | t1 t2 | t1 t2 | t1 t2 | p1 IH1 p2 IH2 | p1 IH1 p2 IH2 | p IH];
    intros K k; simpl.
  - split; intros H; constructor.
  - split; intros H; constructor.
  - split; intros H.
    + pose proof (proj1 (lc_tm_open_tm_ty K k U t1 HU)) as P1.
      pose proof (proj1 (lc_tm_open_tm_ty K k U t2 HU)) as P2.
      inversion H; subst; constructor; eauto 10.
    + pose proof (proj2 (lc_tm_open_tm_ty K k U t1 HU)) as P1.
      pose proof (proj2 (lc_tm_open_tm_ty K k U t2 HU)) as P2.
      inversion H; subst; constructor; eauto 10.
  - split; intros H.
    + pose proof (proj1 (lc_tm_open_tm_ty K k U t1 HU)) as P1.
      pose proof (proj1 (lc_tm_open_tm_ty K k U t2 HU)) as P2.
      inversion H; subst; constructor; eauto 10.
    + pose proof (proj2 (lc_tm_open_tm_ty K k U t1 HU)) as P1.
      pose proof (proj2 (lc_tm_open_tm_ty K k U t2 HU)) as P2.
      inversion H; subst; constructor; eauto 10.
  - split; intros H.
    + pose proof (proj1 (lc_tm_open_tm_ty K k U t1 HU)) as P1.
      pose proof (proj1 (lc_tm_open_tm_ty K k U t2 HU)) as P2.
      inversion H; subst; constructor; eauto 10.
    + pose proof (proj2 (lc_tm_open_tm_ty K k U t1 HU)) as P1.
      pose proof (proj2 (lc_tm_open_tm_ty K k U t2 HU)) as P2.
      inversion H; subst; constructor; eauto 10.
  - split; intros H.
    + pose proof (proj1 (IH1 K k)) as P1. pose proof (proj1 (IH2 K k)) as P2.
      inversion H; subst; constructor; eauto 10.
    + pose proof (proj2 (IH1 K k)) as P1. pose proof (proj2 (IH2 K k)) as P2.
      inversion H; subst; constructor; eauto 10.
  - split; intros H.
    + pose proof (proj1 (IH1 K k)) as P1. pose proof (proj1 (IH2 K k)) as P2.
      inversion H; subst; constructor; eauto 10.
    + pose proof (proj2 (IH1 K k)) as P1. pose proof (proj2 (IH2 K k)) as P2.
      inversion H; subst; constructor; eauto 10.
  - split; intros H.
    + pose proof (proj1 (IH K k)) as P. inversion H; subst; constructor; eauto 10.
    + pose proof (proj2 (IH K k)) as P. inversion H; subst; constructor; eauto 10.
Qed.

Lemma lc_rty_open_tm : forall K k (u : tm) (R : rty),
  lc_tm_any u ->
  (lc_rty_at K k (open_rty_tm_rec k u R) <-> lc_rty_at K (S k) R).
Proof.
  intros K k u R Hu. revert K k.
  induction R as [T p | R1 IH1 R2 IH2 | R1 IH1 R2 IH2 | R IH]; intros K k; simpl.
  - split.
    + intros H. unfold open_qualifier_tm_rec in H.
      inversion H; subst; constructor; unfold lc_qualifier_at in *;
        [assumption | apply (proj1 (lc_pred_open_tm K (S k) u p Hu))]; assumption.
    + intros H. unfold open_qualifier_tm_rec.
      inversion H; subst; constructor; unfold lc_qualifier_at in *;
        [assumption | apply (proj2 (lc_pred_open_tm K (S k) u p Hu))]; assumption.
  - split.
    + intros H. inversion H; subst; constructor;
        [apply (proj1 (IH1 K k)) | apply (proj1 (IH2 K (S k)))]; assumption.
    + intros H. inversion H; subst; constructor;
        [apply (proj2 (IH1 K k)) | apply (proj2 (IH2 K (S k)))]; assumption.
  - split.
    + intros H. inversion H; subst; constructor;
        [apply (proj1 (IH1 K k)) | apply (proj1 (IH2 K (S k)))]; assumption.
    + intros H. inversion H; subst; constructor;
        [apply (proj2 (IH1 K k)) | apply (proj2 (IH2 K (S k)))]; assumption.
  - split.
    + intros H. inversion H; subst; constructor.
      apply (proj1 (IH (S K) k)). assumption.
    + intros H. inversion H; subst; constructor.
      apply (proj2 (IH (S K) k)). assumption.
Qed.

Lemma lc_rty_open_ty : forall K k (U : ty) (R : rty),
  lc_ty_any U ->
  (lc_rty_at K k (open_rty_ty_rec K U R) <-> lc_rty_at (S K) k R).
Proof.
  intros K k U R HU. revert K k.
  induction R as [T p | R1 IH1 R2 IH2 | R1 IH1 R2 IH2 | R IH]; intros K k; simpl.
  - split.
    + intros H. unfold open_qualifier_ty_rec in H.
      inversion H; subst; constructor; unfold lc_qualifier_at in *;
        [apply (proj1 (lc_ty_open_ty K U T HU)) |
         apply (proj1 (lc_pred_open_ty K (S k) U p HU))]; assumption.
    + intros H. unfold open_qualifier_ty_rec.
      inversion H; subst; constructor; unfold lc_qualifier_at in *;
        [apply (proj2 (lc_ty_open_ty K U T HU)) |
         apply (proj2 (lc_pred_open_ty K (S k) U p HU))]; assumption.
  - split.
    + intros H. inversion H; subst; constructor;
        [apply (proj1 (IH1 K k)) | apply (proj1 (IH2 K (S k)))]; assumption.
    + intros H. inversion H; subst; constructor;
        [apply (proj2 (IH1 K k)) | apply (proj2 (IH2 K (S k)))]; assumption.
  - split.
    + intros H. inversion H; subst; constructor;
        [apply (proj1 (IH1 K k)) | apply (proj1 (IH2 K (S k)))]; assumption.
    + intros H. inversion H; subst; constructor;
        [apply (proj2 (IH1 K k)) | apply (proj2 (IH2 K (S k)))]; assumption.
  - split.
    + intros H. inversion H; subst; constructor.
      apply (proj1 (IH (S K) k)). assumption.
    + intros H. inversion H; subst; constructor.
      apply (proj2 (IH (S K) k)). assumption.
Qed.

(* ---------- substitution preserves local closedness ---------- *)
Lemma mty_lc : forall (tau : atom -> ty) (K : nat) (T : ty),
  lc_ty_at K T -> type_ok tau -> lc_ty_at K (mty tau T).
Proof.
  intros tau K T H. induction H as [k i Hi | k X | k T1 T2 H1 IH1 H2 IH2 | k T H IH | k];
    intros Hok; simpl.
  - constructor; lia.
  - exact (lc_ty_mono 0 (tau X) (Hok X) k (Nat.le_0_l k)).
  - constructor; [exact (IH1 Hok) | exact (IH2 Hok)].
  - constructor; exact (IH Hok).
  - constructor.
Qed.

Lemma mty_lc_any : forall (tau : atom -> ty) (T : ty), locally_closed_ty T -> type_ok tau -> lc_ty_any (mty tau T).
Proof.
  intros tau T H Hok K.
  exact (mty_lc tau K T (lc_ty_mono 0 T H K (Nat.le_0_l K)) Hok).
Qed.

Lemma mtm_lc : forall (tau : atom -> ty) (s : atom -> tm) (K k : nat) (t : tm),
  lc_tm_at K k t -> type_ok tau -> term_ok s -> lc_tm_at K k (mtm tau s t).
Proof.
  intros tau s K k t H.
  induction H as [K k i Hi | K k x | K k T t Hty Htm IH | K k t1 t2 H1 IH1 H2 IH2
                 | K k t Ht IH | K k t T Ht IH Hty | K k n
                 | K k t1 t2 H1 IH1 H2 IH2 | K k op t1 t2 H1 IH1 H2 IH2];
    intros Hok Hs; simpl.
  - constructor; lia.
  - exact (lc_tm_at_00 (s x) K k (Hs x)).
  - constructor; [exact (mty_lc tau K T Hty Hok) | exact (IH Hok Hs)].
  - constructor; [exact (IH1 Hok Hs) | exact (IH2 Hok Hs)].
  - constructor; exact (IH Hok Hs).
  - constructor; [exact (IH Hok Hs) | exact (mty_lc tau K T Hty Hok)].
  - constructor.
  - constructor; [exact (IH1 Hok Hs) | exact (IH2 Hok Hs)].
  - constructor; [exact (IH1 Hok Hs) | exact (IH2 Hok Hs)].
Qed.

Lemma mtm_lc_any : forall (tau : atom -> ty) (s : atom -> tm) (t : tm),
  locally_closed_tm t -> type_ok tau -> term_ok s -> lc_tm_any (mtm tau s t).
Proof.
  intros tau s t H Ht Hs K k.
  exact (mtm_lc tau s K k t (lc_tm_mono 0 0 t H K k (Nat.le_0_l K) (Nat.le_0_l k)) Ht Hs).
Qed.

Lemma mqual_lc : forall (tau : atom -> ty) (s : atom -> tm) (K k : nat) (p : qualifier),
  lc_pred_at K k p -> type_ok tau -> term_ok s -> lc_pred_at K k (mqual tau s p).
Proof.
  intros tau s K k p H.
  induction H as [K k | K k | K k t1 t2 H1 H2 | K k t1 t2 H1 H2 | K k t1 t2 H1 H2
                 | K k p1 p2 H1 IH1 H2 IH2 | K k p1 p2 H1 IH1 H2 IH2 | K k p H IH];
    intros Hok Hs; simpl.
  - constructor.
  - constructor.
  - constructor; [exact (mtm_lc tau s K k t1 H1 Hok Hs) | exact (mtm_lc tau s K k t2 H2 Hok Hs)].
  - constructor; [exact (mtm_lc tau s K k t1 H1 Hok Hs) | exact (mtm_lc tau s K k t2 H2 Hok Hs)].
  - constructor; [exact (mtm_lc tau s K k t1 H1 Hok Hs) | exact (mtm_lc tau s K k t2 H2 Hok Hs)].
  - constructor; [exact (IH1 Hok Hs) | exact (IH2 Hok Hs)].
  - constructor; [exact (IH1 Hok Hs) | exact (IH2 Hok Hs)].
  - constructor; exact (IH Hok Hs).
Qed.

Lemma mrty_lc : forall (tau : atom -> ty) (s : atom -> tm) (K k : nat) (R : rty),
  lc_rty_at K k R -> type_ok tau -> term_ok s -> lc_rty_at K k (mrty tau s R).
Proof.
  intros tau s K k R H.
  induction H as [K k T ps Hty Hps | K k R1 R2 H1 IH1 H2 IH2
                 | K k R1 R2 H1 IH1 H2 IH2 | K k R H IH];
    intros Hok Hs; simpl.
  - constructor; unfold lc_qualifier_at in *.
    + exact (mty_lc tau K T Hty Hok).
    + exact (mqual_lc tau s K (S k) ps Hps Hok Hs).
  - constructor; [exact (IH1 Hok Hs) | exact (IH2 Hok Hs)].
  - constructor; [exact (IH1 Hok Hs) | exact (IH2 Hok Hs)].
  - constructor; exact (IH Hok Hs).
Qed.

Lemma mrty_lc_00 : forall (tau : atom -> ty) (s : atom -> tm) (R : rty),
  locally_closed_rty R -> type_ok tau -> term_ok s -> lc_rty_at 0 0 (mrty tau s R).
Proof.
  intros tau s R H Ht Hs. exact (mrty_lc tau s 0 0 R H Ht Hs).
Qed.

Lemma mrty_lc_at : forall (tau : atom -> ty) (s : atom -> tm) (K k : nat) (R : rty),
  lc_rty_at K k R -> type_ok tau -> term_ok s -> lc_rty_at K k (mrty tau s R).
Proof. intros. exact (mrty_lc tau s K k R H H0 H1). Qed.

(* value is locally closed *)
Lemma value_lc : forall v, value v -> locally_closed_tm v.
Proof. intros v H. destruct H. - assumption. - assumption. - constructor. Qed.

Lemma value_mtm : forall (tau : atom -> ty) (s : atom -> tm) (v : tm),
  value v -> type_ok tau -> term_ok s -> value (mtm tau s v).
Proof.
  intros tau s v H Ht Hs. destruct H as [T t Hlc | t Hlc | n].
  - simpl. apply v_abs. constructor.
    + inversion Hlc; subst. apply mty_lc; assumption.
    + inversion Hlc; subst. apply mtm_lc; assumption.
  - simpl. apply v_tabs. constructor. inversion Hlc; subst. apply mtm_lc; assumption.
  - simpl. apply v_int.
Qed.


(* ================= Part 2: operational and syntactic lemmas ================= *)
Lemma multi_trans : forall t1 t2 t3 : tm,
  multi t1 t2 -> multi t2 t3 -> multi t1 t3.
Proof.
  intros t1 t2 t3 H12 H23. revert t3 H23.
  induction H12 as [t | a b c Hstep Hmulti IH]; intros t3 H23.
  - exact H23.
  - eapply multi_step. exact Hstep. apply IH. exact H23.
Qed.

Lemma multi_one : forall t1 t2 : tm, t1 --> t2 -> multi t1 t2.
Proof.
  intros t1 t2 H. apply multi_step with t2; [assumption|apply multi_refl].
Qed.

Lemma value_no_step : forall (v t : tm), value v -> v --> t -> False.
Proof.
  intros v t Hv Hs. destruct Hv; inversion Hs.
Qed.

Lemma multi_value_inv : forall (v t : tm), value v -> multi v t -> t = v.
Proof.
  intros v t Hv Hm. induction Hm.
  - reflexivity.
  - exfalso. eapply value_no_step; eauto.
Qed.

Definition safe (t : tm) : Prop := value t \/ (exists t', t --> t').
Definition safe_multi (t : tm) : Prop := forall t', multi t t' -> safe t'.

Lemma safe_multi_def : forall t, safe_multi t <-> (forall t', multi t t' -> safe t').
Proof. intros. unfold safe_multi. reflexivity. Qed.

Lemma safe_multi_mono : forall t t', safe_multi t -> multi t t' -> safe_multi t'.
Proof.
  intros t t' H Hm t'' Hm'. apply H. eapply multi_trans; eauto.
Qed.

Lemma value_safe_multi : forall v, value v -> safe_multi v.
Proof.
  intros v Hv t' Hm. left.
  rewrite (multi_value_inv v t' Hv Hm). assumption.
Qed.

Lemma safe_multi_safe : forall t, safe_multi t -> safe t.
Proof. intros t H. apply H. apply multi_refl. Qed.

(* step preserves local closedness (both source and target) *)
Lemma step_lc : forall t t', t --> t' -> locally_closed_tm t /\ locally_closed_tm t'.
Proof.
  intros t t' H.
  induction H as [T t v Hlc Hv
                 | t1 t1' t2 Hstep IH Hlc2
                 | v1 t2 t2' Hv Hstep IH
                 | t T Hlc Hlcty
                 | t t' T Hstep IH Hlcty
                 | t1 t1' t2 Hstep IH Hlc2
                 | v1 t2 t2' Hv Hstep IH
                 | n m Hne
                 | op t1 t1' t2 Hstep IH Hlc2
                 | op v1 t2 t2' Hv Hstep IH
                 | op n m].
  - (* AppAbs *) split.
    + apply lc_tm_app. exact Hlc. apply value_lc. exact Hv.
    + assert (Ht : lc_tm_at 0 1 t) by (inversion Hlc; subst; assumption).
      exact (proj2 (lc_tm_open_tm 0 0 v t (lc_tm_any_intro v (value_lc v Hv))) Ht).
  - (* App1 *) destruct IH as [Hs Ht]. split.
    + apply lc_tm_app; [exact Hs | exact Hlc2].
    + apply lc_tm_app; [exact Ht | exact Hlc2].
  - (* App2 *) destruct IH as [Hs Ht]. split.
    + apply lc_tm_app; [apply value_lc; exact Hv | exact Hs].
    + apply lc_tm_app; [apply value_lc; exact Hv | exact Ht].
  - (* TAppTabs *) split.
    + apply lc_tm_tapp; [exact Hlc | exact Hlcty].
    + assert (Ht : lc_tm_at 1 0 t) by (inversion Hlc; subst; assumption).
      exact (proj2 (lc_tm_open_tm_ty 0 0 T t (lc_ty_any_intro T Hlcty)) Ht).
  - (* TApp *) destruct IH as [Hs Ht]. split.
    + apply lc_tm_tapp; [exact Hs | exact Hlcty].
    + apply lc_tm_tapp; [exact Ht | exact Hlcty].
  - (* Div1 *) destruct IH as [Hs Ht]. split.
    + apply lc_tm_div; [exact Hs | exact Hlc2].
    + apply lc_tm_div; [exact Ht | exact Hlc2].
  - (* Div2 *) destruct IH as [Hs Ht]. split.
    + apply lc_tm_div; [apply value_lc; exact Hv | exact Hs].
    + apply lc_tm_div; [apply value_lc; exact Hv | exact Ht].
  - (* DivInt *) split; [apply lc_tm_div; apply lc_tm_int | apply lc_tm_int].
  - (* Arith1 *) destruct IH as [Hs Ht]. split.
    + apply lc_tm_arith; [exact Hs | exact Hlc2].
    + apply lc_tm_arith; [exact Ht | exact Hlc2].
  - (* Arith2 *) destruct IH as [Hs Ht]. split.
    + apply lc_tm_arith; [apply value_lc; exact Hv | exact Hs].
    + apply lc_tm_arith; [apply value_lc; exact Hv | exact Ht].
  - (* ArithInt *) split; [apply lc_tm_arith; apply lc_tm_int | apply lc_tm_int].
Qed.

Lemma step_lc_source : forall t t', t --> t' -> locally_closed_tm t.
Proof. intros. apply step_lc in H. apply H. Qed.
Lemma step_lc_target : forall t t', t --> t' -> locally_closed_tm t'.
Proof. intros. apply step_lc in H. apply H. Qed.

Lemma multi_lc : forall t t', multi t t' -> locally_closed_tm t -> locally_closed_tm t'.
Proof.
  intros t t' H.
  induction H as [u | a b c Hstep Hmulti IH]; intros Hlc.
  - exact Hlc.
  - apply IH. eapply step_lc_target; eauto.
Qed.


(* ================= Part 2b: shape and well-formedness ================= *)
Definition cshape (T : ty) (v : tm) : Prop :=
  match T with
  | Ty_Int => exists n, v = tm_int n
  | Ty_Arrow _ _ => exists T0 b, v = tm_abs T0 b
  | Ty_All _ => exists b, v = tm_tabs b
  | Ty_FVar _ => False
  | Ty_BVar _ => False
  end.

Lemma has_type_cshape : forall Delta Gamma (v : tm) T,
  has_type Delta Gamma v T -> value v -> cshape T v.
Proof.
  intros Delta Gamma v T H.
  induction H as [Delta Gamma x T Hlook Hwf
                 | L Delta Gamma T1 t2 T2 Hwf Hbody IH
                 | Delta Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
                 | L Delta Gamma t T Hbody IH
                 | Delta Gamma t T U H1 IH1 Hwf
                 | Delta Gamma n
                 | Delta Gamma t1 t2 H1 IH1 H2 IH2
                 | Delta Gamma op t1 t2 H1 IH1 H2 IH2];
    intros Hv; simpl.
  - inversion Hv.
  - exists T1, t2. reflexivity.
  - inversion Hv.
  - exists t. reflexivity.
  - inversion Hv.
  - exists n. reflexivity.
  - inversion Hv.
  - inversion Hv.
Qed.

Lemma cshape_mty : forall (tau : atom -> ty) (s : atom -> tm) (T : ty) (v : tm),
  cshape T v -> cshape (mty tau T) (mtm tau s v).
Proof.
  intros tau s T v H. destruct T as [i | X | T1 T2 | T1 |]; simpl in *.
  - destruct H.
  - destruct H.
  - destruct H as [T0 [b Hb]]. subst v. simpl. exists (mty tau T0), (mtm tau s b). reflexivity.
  - destruct H as [b Hb]. subst v. simpl. exists (mtm tau s b). reflexivity.
  - destruct H as [n Hn]. subst v. simpl. exists n. reflexivity.
Qed.

Lemma erase_mrty : forall (tau : atom -> ty) (s : atom -> tm) (R : rty),
  erase (mrty tau s R) = mty tau (erase R).
Proof.
  intros tau s R. induction R as [T p | R1 IH1 R2 IH2 | R1 IH1 R2 IH2 | R IH]; simpl.
  - reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH2. reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma lc_rty_erase : forall K k (R : rty), lc_rty_at K k R -> lc_ty_at K (erase R).
Proof.
  intros K k R H.
  induction H as [K k T ps Hty Hps | K k R1 R2 H1 IH1 H2 IH2
                 | K k R1 R2 H1 IH1 H2 IH2 | K k R H IH].
  - simpl. exact Hty.
  - simpl. constructor; assumption.
  - simpl. exact IH2.
  - simpl. constructor. exact IH.
Qed.

(* wf_ty implies locally closed type at any depth *)
Lemma wf_ty_lc : forall Delta (T : ty), wf_ty Delta T -> forall K, lc_ty_at K T.
Proof.
  intros Delta T H. induction H as [Delta X Hin | Delta T1 T2 H1 IH1 H2 IH2
                 | L Delta T Hbody IH | Delta].
  - intros K. constructor.
  - intros K. constructor; [apply IH1 | apply IH2].
  - intros K. constructor.
    pose proof (IH (fresh (L ++ fv_ty T ++ Delta)) (fresh_not_in_lists _ _) 0) as H1.
    pose proof (proj1 (lc_ty_open_ty 0 (Ty_FVar (fresh (L ++ fv_ty T ++ Delta))) T
                         (lc_ty_any_fvar _)) H1) as H2.
    apply lc_ty_mono with (K:=1); auto. lia.
  - intros K. constructor.
Qed.

(* has_type implies locally closed term *)
Lemma has_type_lc : forall Delta Gamma (t : tm) T, has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T H.
  induction H as [Delta Gamma x T Hlook Hwf
                 | L Delta Gamma T1 t2 T2 Hwf Hbody IH
                 | Delta Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
                 | L Delta Gamma t T Hbody IH
                 | Delta Gamma t T U H1 IH1 Hwf
                 | Delta Gamma n
                 | Delta Gamma t1 t2 H1 IH1 H2 IH2
                 | Delta Gamma op t1 t2 H1 IH1 H2 IH2].
  - constructor.
  - simpl. constructor.
    + exact (wf_ty_lc Delta T1 Hwf 0).
    + pose proof (IH (fresh (L ++ fv_tm t2)) (fresh_not_in_lists _ _)) as Hopen.
      exact (proj1 (lc_tm_open_tm 0 0 (tm_fvar (fresh (L ++ fv_tm t2))) t2
                     (lc_tm_any_fvar _)) Hopen).
  - simpl. apply lc_tm_app; assumption.
  - simpl. constructor.
    pose proof (IH (fresh (L ++ ftv_tm t)) (fresh_not_in_lists _ _)) as Hopen.
    exact (proj1 (lc_tm_open_tm_ty 0 0 (Ty_FVar (fresh (L ++ ftv_tm t))) t
                   (lc_ty_any_fvar _)) Hopen).
  - simpl. apply lc_tm_tapp; [assumption | exact (wf_ty_lc Delta U Hwf 0)].
  - constructor.
  - simpl. apply lc_tm_div; assumption.
  - simpl. apply lc_tm_arith; assumption.
Qed.

(* predicate_wf implies locally closed qualifier at any depth *)
Lemma predicate_wf_lc : forall Delta Gamma (p : qualifier),
  predicate_wf Delta Gamma p -> forall K k, lc_pred_at K k p.
Proof.
  intros Delta Gamma p H.
  induction H as [Delta Gamma | Delta Gamma
                 | Delta Gamma t1 t2 T H1 H2
                 | Delta Gamma t1 t2 H1 H2
                 | Delta Gamma t1 t2 H1 H2
                 | Delta Gamma p1 p2 H1 IH1 H2 IH2
                 | Delta Gamma p1 p2 H1 IH1 H2 IH2
                 | Delta Gamma p H IH].
  - intros K k. constructor.
  - intros K k. constructor.
  - intros K k. constructor.
    + exact (lc_tm_at_00 t1 K k (has_type_lc Delta Gamma t1 T H1)).
    + exact (lc_tm_at_00 t2 K k (has_type_lc Delta Gamma t2 T H2)).
  - intros K k. constructor.
    + exact (lc_tm_at_00 t1 K k (has_type_lc Delta Gamma t1 Ty_Int H1)).
    + exact (lc_tm_at_00 t2 K k (has_type_lc Delta Gamma t2 Ty_Int H2)).
  - intros K k. constructor.
    + exact (lc_tm_at_00 t1 K k (has_type_lc Delta Gamma t1 Ty_Int H1)).
    + exact (lc_tm_at_00 t2 K k (has_type_lc Delta Gamma t2 Ty_Int H2)).
  - intros K k. constructor; auto.
  - intros K k. constructor; auto.
  - intros K k. constructor; auto.
Qed.

(* wf_rty implies locally closed rty at any depth *)
Lemma wf_rty_lc : forall Delta RGamma (R : rty), wf_rty Delta RGamma R -> forall K k, lc_rty_at K k R.
Proof.
  intros Delta RGamma R H.
  induction H as [L Delta RGamma T ps Hwf Hqual
                 | L Delta RGamma R1 R2 Hwf1 IH1 Hbody IH2
                 | L Delta RGamma R1 R2 Hwf1 IH1 Hbody IH2
                 | L Delta RGamma R Hbody IH].
  - intros K k. constructor.
    + exact (wf_ty_lc Delta T Hwf K).
    + unfold lc_qualifier_at.
      pose proof (Hqual (fresh (L ++ fv_qual ps)) (fresh_not_in_lists _ _)) as Hq.
      unfold qualifier_wf in Hq.
      pose proof (predicate_wf_lc Delta (update (erase_context RGamma) (fresh (L ++ fv_qual ps)) T)
                    (open_qualifier_tm ps (tm_fvar (fresh (L ++ fv_qual ps)))) Hq K 0) as Hp.
      unfold open_qualifier_tm in Hp.
      pose proof (proj1 (lc_pred_open_tm K 0 (tm_fvar (fresh (L ++ fv_qual ps))) ps
                           (lc_tm_any_fvar _)) Hp) as Hp1.
      apply lc_pred_mono with (K:=K) (k:=1); auto. lia.
  - intros K k. constructor.
    + apply IH1.
    + pose proof (IH2 (fresh (L ++ fv_rty R2)) (fresh_not_in_lists _ _)) as Ho.
      pose proof (proj1 (lc_rty_open_tm K 0 (tm_fvar (fresh (L ++ fv_rty R2))) R2
                           (lc_tm_any_fvar _)) (Ho K 0)) as H1.
      apply lc_rty_mono with (K:=K) (k:=1); auto. lia.
  - intros K k. constructor.
    + apply IH1.
    + pose proof (IH2 (fresh (L ++ fv_rty R2)) (fresh_not_in_lists _ _)) as Ho.
      pose proof (proj1 (lc_rty_open_tm K 0 (tm_fvar (fresh (L ++ fv_rty R2))) R2
                           (lc_tm_any_fvar _)) (Ho K 0)) as H1.
      apply lc_rty_mono with (K:=K) (k:=1); auto. lia.
  - intros K k. constructor.
    pose proof (IH (fresh (L ++ ftv_rty R)) (fresh_not_in_lists _ _)) as Ho.
    pose proof (proj1 (lc_rty_open_ty 0 0 (Ty_FVar (fresh (L ++ ftv_rty R))) R
                         (lc_ty_any_fvar _)) (Ho 0 0)) as H1.
    exact (lc_rty_mono 1 0 R H1 (S K) k (le_n_S 0 K (Nat.le_0_l K)) (Nat.le_0_l k)).
Qed.

Lemma wf_rty_erase_lc : forall Delta RGamma (R : rty),
  wf_rty Delta RGamma R -> forall K, lc_ty_at K (erase R).
Proof.
  intros Delta RGamma R H K. exact (lc_rty_erase K 0 R (wf_rty_lc Delta RGamma R H K 0)).
Qed.

(* has_rtype implies locally closed term *)
Lemma has_rtype_lc : forall Delta RGamma (t : tm) R,
  has_rtype Delta RGamma t R -> locally_closed_tm t.
Proof.
  intros Delta RGamma t R H.
  induction H as [Delta RGamma x R Hlook Hwf
                 | L Delta RGamma R1 body R2 Hwf Hbody IH
                 | Delta RGamma t1 t2 R1 R2 H1 IH1 H2 IH2
                 | L Delta RGamma body R Hbody IH
                 | Delta RGamma t R U H1 IH1 Hwf
                 | Delta RGamma n
                 | Delta RGamma t1 t2 H1 IH1 H2 IH2
                 | Delta RGamma op t1 t2 H1 IH1 H2 IH2
                 | Delta RGamma v T ps Htype Hval Hwf Hclosed Hholds
                 | Delta RGamma t R S H1 IH1 Hwf Hsub].
  - constructor.
  - simpl. constructor.
    + exact (lc_rty_erase 0 0 R1 (wf_rty_lc Delta RGamma R1 Hwf 0 0)).
    + pose proof (IH (fresh (L ++ fv_tm body)) (fresh_not_in_lists _ _)) as Hopen.
      exact (proj1 (lc_tm_open_tm 0 0 (tm_fvar (fresh (L ++ fv_tm body))) body
                     (lc_tm_any_fvar _)) Hopen).
  - simpl. apply lc_tm_app; assumption.
  - simpl. constructor.
    pose proof (IH (fresh (L ++ ftv_tm body)) (fresh_not_in_lists _ _)) as Hopen.
    exact (proj1 (lc_tm_open_tm_ty 0 0 (Ty_FVar (fresh (L ++ ftv_tm body))) body
                   (lc_ty_any_fvar _)) Hopen).
  - simpl. apply lc_tm_tapp; [assumption | exact (wf_ty_lc Delta U Hwf 0)].
  - constructor.
  - simpl. apply lc_tm_div; assumption.
  - simpl. apply lc_tm_arith; assumption.
  - exact (value_lc v Hval).
  - assumption.
Qed.

End SystemFRefinementSemantics.

Module SystemFRefinementTask.
Import ListNotations SystemFRefinement SystemFRefinementLogic SystemFRefinementTyping SystemFRefinementEvaluation.

Theorem never_stuck : forall (t t' : tm) (R : rty),
  has_rtype [] empty_rcontext t R ->
  multi t t' ->
  value t' \/ exists t'' : tm, t' --> t''.
Proof.
Abort.

End SystemFRefinementTask.
