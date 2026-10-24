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

(* ================================================================ *)
(* Infrastructure for the semantic proof of never_stuck.             *)
(* ================================================================ *)

Definition env := atom -> tm.
Definition tyenv := atom -> tm -> Prop.

(* Simultaneous substitution of free term variables. *)
Fixpoint subst_env (sigma : env) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_abs T b => tm_abs T (subst_env sigma b)
  | tm_app a b => tm_app (subst_env sigma a) (subst_env sigma b)
  | tm_tabs b => tm_tabs (subst_env sigma b)
  | tm_tapp a T => tm_tapp (subst_env sigma a) T
  | tm_int n => tm_int n
  | tm_div a b => tm_div (subst_env sigma a) (subst_env sigma b)
  | tm_arith op a b => tm_arith op (subst_env sigma a) (subst_env sigma b)
  end.

Fixpoint subst_pred_env (sigma : env) (p : qualifier) : qualifier :=
  match p with
  | Pred_True => Pred_True
  | Pred_False => Pred_False
  | Pred_Eq a b => Pred_Eq (subst_env sigma a) (subst_env sigma b)
  | Pred_Lt a b => Pred_Lt (subst_env sigma a) (subst_env sigma b)
  | Pred_Le a b => Pred_Le (subst_env sigma a) (subst_env sigma b)
  | Pred_And p q => Pred_And (subst_pred_env sigma p) (subst_pred_env sigma q)
  | Pred_Or p q => Pred_Or (subst_pred_env sigma p) (subst_pred_env sigma q)
  | Pred_Not p => Pred_Not (subst_pred_env sigma p)
  end.

(* Erasure of all type annotations (to Ty_Int). *)
Fixpoint erase_tm (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T b => tm_abs Ty_Int (erase_tm b)
  | tm_app a b => tm_app (erase_tm a) (erase_tm b)
  | tm_tabs b => tm_tabs (erase_tm b)
  | tm_tapp a T => tm_tapp (erase_tm a) Ty_Int
  | tm_int n => tm_int n
  | tm_div a b => tm_div (erase_tm a) (erase_tm b)
  | tm_arith op a b => tm_arith op (erase_tm a) (erase_tm b)
  end.

Fixpoint erase_pred (p : qualifier) : qualifier :=
  match p with
  | Pred_True => Pred_True
  | Pred_False => Pred_False
  | Pred_Eq a b => Pred_Eq (erase_tm a) (erase_tm b)
  | Pred_Lt a b => Pred_Lt (erase_tm a) (erase_tm b)
  | Pred_Le a b => Pred_Le (erase_tm a) (erase_tm b)
  | Pred_And p q => Pred_And (erase_pred p) (erase_pred q)
  | Pred_Or p q => Pred_Or (erase_pred p) (erase_pred q)
  | Pred_Not p => Pred_Not (erase_pred p)
  end.

(* ---------- erasure commutations ---------- *)

Lemma erase_open_tm_rec : forall k u t,
  erase_tm (open_tm_rec k u t)
  = open_tm_rec k (erase_tm u) (erase_tm t).
Proof.
  intros k u t. revert k.
  induction t as [i|x|T b IH|a IHa b IHb|b IH|a IHa T|n|a IHa b IHb|op a IHa b IHb];
    intros k; simpl.
  - destruct (Nat.eqb k i); reflexivity.
  - reflexivity.
  - f_equal. apply IH.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
  - reflexivity.
  - f_equal; auto.
  - f_equal; auto.
Qed.

Lemma erase_open_tm : forall u t,
  erase_tm (open_tm t u) = open_tm (erase_tm t) (erase_tm u).
Proof. intros. apply erase_open_tm_rec. Qed.

Lemma erase_open_tm_ty_rec : forall k U t,
  erase_tm (open_tm_ty_rec k U t) = erase_tm t.
Proof.
  intros k U t. revert k.
  induction t as [i|x|T b IH|a IHa b IHb|b IH|a IHa T|n|a IHa b IHb|op a IHa b IHb];
    intros k; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal. apply IH.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
  - reflexivity.
  - f_equal; auto.
  - f_equal; auto.
Qed.

Lemma erase_open_tm_ty : forall U t,
  erase_tm (open_tm_ty t U) = erase_tm t.
Proof. intros. apply erase_open_tm_ty_rec. Qed.

Lemma erase_idem : forall t, erase_tm (erase_tm t) = erase_tm t.
Proof.
  induction t as [i|x|T b IH|a IHa b IHb|b IH|a IHa T|n|a IHa b IHb|op a IHa b IHb];
    simpl; auto.
  - f_equal. apply IH.
  - f_equal; auto.
  - f_equal. apply IH.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
Qed.

Lemma open_tm_erase_id : forall k U t,
  open_tm_ty_rec k U (erase_tm t) = erase_tm t.
Proof.
  intros k U t. revert k.
  induction t as [i|x|T b IH|a IHa b IHb|b IH|a IHa T|n|a IHa b IHb|op a IHa b IHb];
    intros k; simpl; auto.
  - f_equal. apply IH.
  - f_equal; auto.
  - f_equal. apply IH.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
Qed.

Lemma erase_tm_subst_env_erase : forall sigma,
  (forall x, erase_tm (sigma x) = sigma x) ->
  forall t, erase_tm (subst_env sigma t) = subst_env sigma (erase_tm t).
Proof.
  intros sigma He.
  induction t as [i|x|T b IH|a IHa b IHb|b IH|a IHa T|n|a IHa b IHb|op a IHa b IHb];
    simpl; auto.
  - f_equal. apply IH.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
Qed.

Lemma erase_pred_subst_erase : forall sigma,
  (forall x, erase_tm (sigma x) = sigma x) ->
  forall p, erase_pred (subst_pred_env sigma p) = subst_pred_env sigma (erase_pred p).
Proof.
  intros sigma He p. induction p; simpl; auto; try (f_equal; auto using erase_tm_subst_env_erase).
Qed.

(* ---------- commutation of substitution and opening ---------- *)

Lemma open_tm_rec_closed : forall t K k,
  lc_tm_at K k t -> forall j u, k <= j -> open_tm_rec j u t = t.
Proof.
  intros t K k H. induction H; intros j u Hkj; simpl.
  - (* bvar *) destruct (Nat.eqb j i) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + reflexivity.
  - (* fvar *) reflexivity.
  - (* abs *) f_equal. apply IHlc_tm_at. lia.
  - (* app *) f_equal; auto.
  - (* tabs *) f_equal. apply IHlc_tm_at. lia.
  - (* tapp *) f_equal; auto.
  - (* int *) reflexivity.
  - (* div *) f_equal; auto.
  - (* arith *) f_equal; auto.
Qed.

Lemma subst_env_open_tm_rec : forall sigma,
  (forall x, lc_tm_at 0 0 (sigma x)) ->
  forall k u t,
  subst_env sigma (open_tm_rec k u t)
  = open_tm_rec k (subst_env sigma u) (subst_env sigma t).
Proof.
  intros sigma Hcl k u t. revert k.
  induction t as [i|x|T b IH|a IHa b IHb|b IH|a IHa T|n|a IHa b IHb|op a IHa b IHb];
    intros k; simpl.
  - destruct (Nat.eqb k i); reflexivity.
  - symmetry. apply open_tm_rec_closed with (K := 0) (k := 0); [apply Hcl | lia].
  - f_equal. apply IH.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
  - reflexivity.
  - f_equal; auto.
  - f_equal; auto.
Qed.

Lemma subst_env_open_tm : forall sigma,
  (forall x, lc_tm_at 0 0 (sigma x)) ->
  forall u t,
  subst_env sigma (open_tm t u)
  = open_tm (subst_env sigma t) (subst_env sigma u).
Proof. intros. apply subst_env_open_tm_rec; auto. Qed.

Lemma erase_subst_open_tm_rec : forall sigma,
  (forall x, lc_tm_at 0 0 (sigma x)) ->
  forall k u t,
  erase_tm (subst_env sigma (open_tm_rec k u t))
  = open_tm_rec k (erase_tm (subst_env sigma u)) (erase_tm (subst_env sigma t)).
Proof.
  intros. rewrite subst_env_open_tm_rec; auto. apply erase_open_tm_rec.
Qed.

Lemma erase_subst_open_tm : forall sigma,
  (forall x, lc_tm_at 0 0 (sigma x)) ->
  forall u t,
  erase_tm (subst_env sigma (open_tm t u))
  = open_tm (erase_tm (subst_env sigma t)) (erase_tm (subst_env sigma u)).
Proof. intros. apply erase_subst_open_tm_rec; auto. Qed.

Lemma erase_subst_open_tm_ty_rec : forall sigma k U t,
  erase_tm (subst_env sigma (open_tm_ty_rec k U t))
  = erase_tm (subst_env sigma t).
Proof.
  intros sigma k U t. revert k.
  induction t as [i|x|T b IH|a IHa b IHb|b IH|a IHa T|n|a IHa b IHb|op a IHa b IHb];
    intros k; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal. apply IH.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
  - reflexivity.
  - f_equal; auto.
  - f_equal; auto.
Qed.

Lemma subst_pred_env_open_rec : forall sigma,
  (forall x, lc_tm_at 0 0 (sigma x)) ->
  forall k u p,
  subst_pred_env sigma (open_pred_tm_rec k u p)
  = open_pred_tm_rec k (subst_env sigma u) (subst_pred_env sigma p).
Proof.
  intros sigma Hcl k u p. revert k.
  induction p; intros k; simpl; auto.
  - f_equal; apply subst_env_open_tm_rec; auto.
  - f_equal; apply subst_env_open_tm_rec; auto.
  - f_equal; apply subst_env_open_tm_rec; auto.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
Qed.

Lemma subst_pred_env_open : forall sigma,
  (forall x, lc_tm_at 0 0 (sigma x)) ->
  forall u p,
  subst_pred_env sigma (open_qualifier_tm p u)
  = open_qualifier_tm (subst_pred_env sigma p) (subst_env sigma u).
Proof. intros. apply subst_pred_env_open_rec; auto. Qed.

Lemma erase_subst_pred_open_rec : forall sigma,
  (forall x, lc_tm_at 0 0 (sigma x)) ->
  forall k u p,
  erase_pred (subst_pred_env sigma (open_pred_tm_rec k u p))
  = open_pred_tm_rec k (erase_tm (subst_env sigma u))
      (erase_pred (subst_pred_env sigma p)).
Proof.
  intros sigma Hcl k u p. revert k.
  induction p; intros k; simpl; auto.
  - f_equal; apply erase_subst_open_tm_rec; auto.
  - f_equal; apply erase_subst_open_tm_rec; auto.
  - f_equal; apply erase_subst_open_tm_rec; auto.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
Qed.

Lemma erase_subst_pred_open_ty_rec : forall sigma k U p,
  erase_pred (subst_pred_env sigma (open_pred_ty_rec k U p))
  = erase_pred (subst_pred_env sigma p).
Proof.
  intros sigma k U p. revert k.
  induction p; intros k; simpl; auto.
  - f_equal; apply erase_subst_open_tm_ty_rec.
  - f_equal; apply erase_subst_open_tm_ty_rec.
  - f_equal; apply erase_subst_open_tm_ty_rec.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
Qed.

(* ---------- free variables ---------- *)

Lemma fv_tm_subst_env_nil : forall sigma t,
  (forall x, fv_tm (sigma x) = []) -> fv_tm (subst_env sigma t) = [].
Proof.
  intros sigma t H.
  induction t as [i|x|T b IH|a IHa b IHb|b IH|a IHa T|n|a IHa b IHb|op a IHa b IHb];
    simpl.
  - reflexivity.
  - apply H.
  - apply IH.
  - rewrite IHa, IHb; reflexivity.
  - apply IH.
  - apply IHa.
  - reflexivity.
  - rewrite IHa, IHb; reflexivity.
  - rewrite IHa, IHb; reflexivity.
Qed.

Lemma subst_env_nil_id : forall sigma t,
  fv_tm t = [] -> subst_env sigma t = t.
Proof.
  intros sigma t.
  induction t as [i|x|T b IH|a IHa b IHb|b IH|a IHa T|n|a IHa b IHb|op a IHa b IHb];
    simpl; intros H.
  - reflexivity.
  - discriminate.
  - f_equal. apply IH. exact H.
  - apply app_eq_nil in H. destruct H as [H1 H2]. f_equal.
    + apply IHa. exact H1.
    + apply IHb. exact H2.
  - f_equal. apply IH. exact H.
  - f_equal. apply IHa. exact H.
  - reflexivity.
  - apply app_eq_nil in H. destruct H as [H1 H2]. f_equal.
    + apply IHa. exact H1.
    + apply IHb. exact H2.
  - apply app_eq_nil in H. destruct H as [H1 H2]. f_equal.
    + apply IHa. exact H1.
    + apply IHb. exact H2.
Qed.

Lemma fv_tm_erase : forall t, fv_tm (erase_tm t) = fv_tm t.
Proof.
  induction t as [i|x|T b IH|a IHa b IHb|b IH|a IHa T|n|a IHa b IHb|op a IHa b IHb];
    simpl.
  - reflexivity.
  - reflexivity.
  - apply IH.
  - rewrite IHa, IHb; reflexivity.
  - apply IH.
  - apply IHa.
  - reflexivity.
  - rewrite IHa, IHb; reflexivity.
  - rewrite IHa, IHb; reflexivity.
Qed.

(* ---------- locally closed types: monotonicity ---------- *)

Lemma lc_ty_at_mono : forall K T, lc_ty_at K T ->
  forall K', K <= K' -> lc_ty_at K' T.
Proof.
  intros K T H. induction H; intros K' Hle.
  - apply lc_ty_bvar. lia.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; auto.
  - apply lc_ty_all. apply IHlc_ty_at. lia.
  - apply lc_ty_int.
Qed.

Lemma lc_ty_at_erase_any : forall T,
  lc_ty_at 0 T -> forall K, lc_ty_at K T.
Proof.
  intros T H K. apply lc_ty_at_mono with (K := 0); auto. lia.
Qed.

(* ---------- locally closed terms: monotonicity ---------- *)

Lemma lc_tm_at_mono : forall K k t, lc_tm_at K k t ->
  forall K' k', K <= K' -> k <= k' -> lc_tm_at K' k' t.
Proof.
  intros K k t H. induction H; intros K' k' HK Hk.
  - apply lc_tm_bvar. lia.
  - apply lc_tm_fvar.
  - apply lc_tm_abs with (T := T).
    + apply lc_ty_at_mono with (K := K); auto.
    + apply IHlc_tm_at; lia.
  - apply lc_tm_app; auto.
  - apply lc_tm_tabs. apply IHlc_tm_at; lia.
  - apply lc_tm_tapp.
    + apply IHlc_tm_at; lia.
    + apply lc_ty_at_mono with (K := K); auto.
  - apply lc_tm_int.
  - apply lc_tm_div; auto.
  - apply lc_tm_arith; auto.
Qed.

Lemma lc_tm_erase : forall K k t, lc_tm_at K k t -> lc_tm_at K k (erase_tm t).
Proof.
  intros K k t H. induction H; simpl.
  - apply lc_tm_bvar. assumption.
  - apply lc_tm_fvar.
  - apply lc_tm_abs with (T := Ty_Int). apply lc_ty_int. apply IHlc_tm_at.
  - apply lc_tm_app; auto.
  - apply lc_tm_tabs. apply IHlc_tm_at.
  - apply lc_tm_tapp. apply IHlc_tm_at. apply lc_ty_int.
  - apply lc_tm_int.
  - apply lc_tm_div; auto.
  - apply lc_tm_arith; auto.
Qed.

Lemma lc_tm_at_erase_any : forall K k t,
  lc_tm_at 0 0 t -> lc_tm_at K k (erase_tm t).
Proof.
  intros. apply lc_tm_at_mono with (K := 0) (k := 0); auto using lc_tm_erase; lia.
Qed.

Lemma lc_tm_subst_env : forall sigma t K k,
  lc_tm_at K k t ->
  (forall x, lc_tm_at 0 0 (sigma x)) ->
  lc_tm_at K k (subst_env sigma t).
Proof.
  intros sigma t.
  induction t as [i|x|T b IH|a IHa b IHb|b IH|a IHa T|n|a IHa b IHb|op a IHa b IHb];
    intros K k Hlc Hsig; simpl; inversion Hlc; subst.
  - apply lc_tm_bvar. assumption.
  - apply lc_tm_at_mono with (K := 0) (k := 0); auto; lia.
  - apply lc_tm_abs with (T := T).
    + assumption.
    + apply IH; assumption.
  - apply lc_tm_app; auto.
  - apply lc_tm_tabs. apply IH; assumption.
  - apply lc_tm_tapp; auto.
  - apply lc_tm_int.
  - apply lc_tm_div; auto.
  - apply lc_tm_arith; auto.
Qed.

Lemma lc_tm_at_fvar : forall K k x, lc_tm_at K k (tm_fvar x).
Proof. intros. apply lc_tm_fvar. Qed.

Lemma lc_tm_at_int : forall K k n, lc_tm_at K k (tm_int n).
Proof. intros. apply lc_tm_int. Qed.

(* opening with a variable, inverted *)
Lemma lc_open_tm_rec_inv : forall K k j x t,
  lc_tm_at K k (open_tm_rec j (tm_fvar x) t) ->
  j <= k ->
  lc_tm_at K (S k) t.
Proof.
  intros K k j x t. revert K k j.
  induction t as [i|x0|T b IH|a IHa b IHb|b IH|a IHa T|n|a IHa b IHb|op a IHa b IHb];
    intros K k j H Hjk; simpl in H.
  - (* bvar *) destruct (Nat.eqb j i) eqn:E.
    + apply Nat.eqb_eq in E. subst i. apply lc_tm_bvar. lia.
    + inversion H; subst. apply lc_tm_bvar. lia.
  - (* fvar *) inversion H. apply lc_tm_fvar.
  - (* abs *) inversion H; subst.
    apply lc_tm_abs with (T := T).
    + assumption.
    + apply IH with (j := S j); auto. lia.
  - (* app *) inversion H; subst. apply lc_tm_app.
    + apply IHa with (j := j); auto.
    + apply IHb with (j := j); auto.
  - (* tabs *) inversion H; subst. apply lc_tm_tabs.
    apply IH with (j := j); auto.
  - (* tapp *) inversion H; subst. apply lc_tm_tapp.
    + apply IHa with (j := j); auto.
    + assumption.
  - (* int *) inversion H. apply lc_tm_int.
  - (* div *) inversion H; subst. apply lc_tm_div.
    + apply IHa with (j := j); auto.
    + apply IHb with (j := j); auto.
  - (* arith *) inversion H; subst. apply lc_tm_arith.
    + apply IHa with (j := j); auto.
    + apply IHb with (j := j); auto.
Qed.

Lemma lc_open_tm_inv : forall x t,
  lc_tm_at 0 0 (open_tm t (tm_fvar x)) -> lc_tm_at 0 1 t.
Proof. intros. apply lc_open_tm_rec_inv with (K := 0) (k := 0) (j := 0) (x := x); auto. Qed.

(* ---------- values and erasure ---------- *)

Lemma value_erase : forall t, value t -> value (erase_tm t).
Proof.
  intros t H. induction H; simpl.
  - apply v_abs. inversion H. simpl. apply lc_tm_abs with (T := Ty_Int).
    + apply lc_ty_int.
    + apply lc_tm_erase. assumption.
  - apply v_tabs. inversion H. simpl. apply lc_tm_tabs.
    apply lc_tm_erase. assumption.
  - apply v_int.
Qed.

Lemma value_erase_reflect : forall t,
  locally_closed_tm t -> value (erase_tm t) -> value t.
Proof.
  intros t Hlc Hv. destruct t; simpl in Hv.
  - inversion Hv.
  - inversion Hv.
  - (* abs *) apply v_abs. exact Hlc.
  - inversion Hv.
  - (* tabs *) apply v_tabs. exact Hlc.
  - inversion Hv.
  - (* int *) apply v_int.
  - inversion Hv.
  - inversion Hv.
Qed.

Lemma value_no_step : forall v u, value v -> step v u -> False.
Proof.
  intros v u Hv Hs. destruct Hv; inversion Hs.
Qed.

Lemma multi_from_value : forall v u, value v -> multi v u -> value u -> v = u.
Proof.
  intros v u Hv Hm. induction Hm.
  - reflexivity.
  - exfalso. eapply value_no_step; eauto.
Qed.

(* ---------- step and erasure ---------- *)

Lemma step_erase : forall t u, step t u -> step (erase_tm t) (erase_tm u).
Proof.
  intros t u H. induction H; simpl.
  - (* ST_AppAbs *) rewrite erase_open_tm. apply ST_AppAbs.
    + apply lc_tm_abs with (T := Ty_Int). constructor.
      inversion H; simpl. apply lc_tm_erase. assumption.
    + apply value_erase. assumption.
  - (* ST_App1 *) apply ST_App1; auto. apply lc_tm_erase. assumption.
  - (* ST_App2 *) apply ST_App2; auto. apply value_erase. assumption.
  - (* ST_TAppTabs *)
    assert (Heq : erase_tm (open_tm_ty t T) = open_tm_ty (erase_tm t) Ty_Int).
    { rewrite erase_open_tm_ty. symmetry. apply open_tm_erase_id. }
    rewrite Heq. apply ST_TAppTabs.
    + apply lc_tm_tabs. inversion H; simpl. apply lc_tm_erase. assumption.
    + constructor.
  - (* ST_TApp *) apply ST_TApp; auto. constructor.
  - (* ST_Div1 *) apply ST_Div1; auto. apply lc_tm_erase. assumption.
  - (* ST_Div2 *) apply ST_Div2; auto. apply value_erase. assumption.
  - (* ST_DivInt *) simpl. apply ST_DivInt. assumption.
  - (* ST_Arith1 *) apply ST_Arith1; auto. apply lc_tm_erase. assumption.
  - (* ST_Arith2 *) apply ST_Arith2; auto. apply value_erase. assumption.
  - (* ST_ArithInt *) simpl. apply ST_ArithInt.
Qed.

Lemma multi_erase : forall t u, multi t u -> multi (erase_tm t) (erase_tm u).
Proof.
  intros t u H. induction H.
  - apply multi_refl.
  - apply multi_step with (t2 := erase_tm t2); auto using step_erase.
Qed.

(* inversion lemmas for local closedness *)
Lemma lc_tm_app_inv : forall K k a b,
  lc_tm_at K k (tm_app a b) -> lc_tm_at K k a /\ lc_tm_at K k b.
Proof. intros. inversion H. auto. Qed.

Lemma lc_tm_abs_inv : forall K k T b,
  lc_tm_at K k (tm_abs T b) -> lc_ty_at K T /\ lc_tm_at K (S k) b.
Proof. intros. inversion H. auto. Qed.

Lemma lc_tm_tabs_inv : forall K k b,
  lc_tm_at K k (tm_tabs b) -> lc_tm_at (S K) k b.
Proof. intros. inversion H. auto. Qed.

Lemma lc_tm_tapp_inv : forall K k a T,
  lc_tm_at K k (tm_tapp a T) -> lc_tm_at K k a /\ lc_ty_at K T.
Proof. intros. inversion H. auto. Qed.

Lemma lc_tm_div_inv : forall K k a b,
  lc_tm_at K k (tm_div a b) -> lc_tm_at K k a /\ lc_tm_at K k b.
Proof. intros. inversion H. auto. Qed.

Lemma lc_tm_arith_inv : forall K k op a b,
  lc_tm_at K k (tm_arith op a b) -> lc_tm_at K k a /\ lc_tm_at K k b.
Proof. intros. inversion H. auto. Qed.

(* inversion lemmas for erasure *)
Lemma erase_tm_app_inv : forall t a b, erase_tm t = tm_app a b ->
  exists a0 b0, t = tm_app a0 b0 /\ a = erase_tm a0 /\ b = erase_tm b0.
Proof.
  intros t a b H. destruct t; simpl in H; try discriminate.
  injection H as H1 H2. subst. eexists; eexists; repeat split; reflexivity.
Qed.

Lemma erase_tm_abs_inv : forall t T b, erase_tm t = tm_abs T b ->
  exists T0 b0, t = tm_abs T0 b0 /\ T = Ty_Int /\ b = erase_tm b0.
Proof.
  intros t T b H. destruct t; simpl in H; try discriminate.
  injection H as H1 H2. subst. eexists; eexists; repeat split; reflexivity.
Qed.

Lemma erase_tm_tabs_inv : forall t b, erase_tm t = tm_tabs b ->
  exists b0, t = tm_tabs b0 /\ b = erase_tm b0.
Proof.
  intros t b H. destruct t; simpl in H; try discriminate.
  injection H as H1. subst. eexists; split; reflexivity.
Qed.

Lemma erase_tm_tapp_inv : forall t a T, erase_tm t = tm_tapp a T ->
  exists a0 T0, t = tm_tapp a0 T0 /\ a = erase_tm a0 /\ T = Ty_Int.
Proof.
  intros t a T H. destruct t; simpl in H; try discriminate.
  injection H as H1 H2. subst. eexists; eexists; repeat split; reflexivity.
Qed.

Lemma erase_tm_int_inv : forall t n, erase_tm t = tm_int n -> t = tm_int n.
Proof.
  intros t n H. destruct t; simpl in H; try discriminate. injection H as H1. subst. reflexivity.
Qed.

Lemma erase_tm_div_inv : forall t a b, erase_tm t = tm_div a b ->
  exists a0 b0, t = tm_div a0 b0 /\ a = erase_tm a0 /\ b = erase_tm b0.
Proof.
  intros t a b H. destruct t; simpl in H; try discriminate.
  injection H as H1 H2. subst. eexists; eexists; repeat split; reflexivity.
Qed.

Lemma erase_tm_arith_inv : forall t op a b, erase_tm t = tm_arith op a b ->
  exists op0 a0 b0, t = tm_arith op0 a0 b0 /\ op = op0 /\ a = erase_tm a0 /\ b = erase_tm b0.
Proof.
  intros t op a b H. destruct t; simpl in H; try discriminate.
  injection H as H1 H2 H3. subst. eexists; eexists; eexists; repeat split; reflexivity.
Qed.

(* lifting an erased reduction back *)
Lemma step_erase_inv : forall t u',
  locally_closed_tm t -> step (erase_tm t) u' ->
  exists u, u' = erase_tm u /\ step t u.
Proof.
  intros t u' Hlc Hs.
  remember (erase_tm t) as et eqn:E.
  revert t Hlc E. induction Hs; intros t0 Hlc E.
  - (* ST_AppAbs *)
    symmetry in E. apply erase_tm_app_inv in E.
    destruct E as [a0 [b0 [E0 [E1 E2]]]].
    symmetry in E1. apply erase_tm_abs_inv in E1.
    destruct E1 as [Ta [body [Ea [ET Eb]]]].
    subst t0. subst a0. subst T. subst t. subst v.
    apply lc_tm_app_inv in Hlc. destruct Hlc as [Hlca Hlcb].
    pose proof Hlca as Hlca_abs.
    apply lc_tm_abs_inv in Hlca. destruct Hlca as [Hty Hbody].
    assert (Hvb : value b0).
    { apply value_erase_reflect; [exact Hlcb | exact H0]. }
    exists (open_tm body b0). split.
    + rewrite erase_open_tm. reflexivity.
    + apply ST_AppAbs; assumption.
  - (* ST_App1 *)
    symmetry in E. apply erase_tm_app_inv in E.
    destruct E as [a0 [b0 [E0 [E1 E2]]]].
    subst t0. apply lc_tm_app_inv in Hlc. destruct Hlc as [Hlca Hlcb].
    destruct (IHHs a0 Hlca E1) as [u [Hu Hstep]].
    exists (tm_app u b0). split.
    + simpl. rewrite Hu, E2. reflexivity.
    + apply ST_App1; assumption.
  - (* ST_App2 *)
    symmetry in E. apply erase_tm_app_inv in E.
    destruct E as [a0 [b0 [E0 [E1 E2]]]].
    subst t0. apply lc_tm_app_inv in Hlc. destruct Hlc as [Hlca Hlcb].
    assert (Hva : value a0).
    { apply value_erase_reflect; [exact Hlca | rewrite <- E1; exact H]. }
    destruct (IHHs b0 Hlcb E2) as [u [Hu Hstep]].
    exists (tm_app a0 u). split.
    + simpl. rewrite Hu, E1. reflexivity.
    + apply ST_App2; assumption.
  - (* ST_TAppTabs *)
    symmetry in E. apply erase_tm_tapp_inv in E.
    destruct E as [a0 [T0 [E0 [E1 ET]]]].
    symmetry in E1. apply erase_tm_tabs_inv in E1.
    destruct E1 as [body [Ea Eb]].
    subst t0. subst a0. subst T. subst t.
    apply lc_tm_tapp_inv in Hlc. destruct Hlc as [Hlca Hty].
    exists (open_tm_ty body T0). split.
    + rewrite erase_open_tm_ty. apply open_tm_erase_id.
    + apply ST_TAppTabs; assumption.
  - (* ST_TApp *)
    symmetry in E. apply erase_tm_tapp_inv in E.
    destruct E as [a0 [T0 [E0 [E1 ET]]]].
    subst t0. subst T. apply lc_tm_tapp_inv in Hlc. destruct Hlc as [Hlca Hty].
    destruct (IHHs a0 Hlca E1) as [u [Hu Hstep]].
    exists (tm_tapp u T0). split.
    + simpl. rewrite Hu. reflexivity.
    + apply ST_TApp; assumption.
  - (* ST_Div1 *)
    symmetry in E. apply erase_tm_div_inv in E.
    destruct E as [a0 [b0 [E0 [E1 E2]]]].
    subst t0. apply lc_tm_div_inv in Hlc. destruct Hlc as [Hlca Hlcb].
    destruct (IHHs a0 Hlca E1) as [u [Hu Hstep]].
    exists (tm_div u b0). split.
    + simpl. rewrite Hu, E2. reflexivity.
    + apply ST_Div1; assumption.
  - (* ST_Div2 *)
    symmetry in E. apply erase_tm_div_inv in E.
    destruct E as [a0 [b0 [E0 [E1 E2]]]].
    subst t0. apply lc_tm_div_inv in Hlc. destruct Hlc as [Hlca Hlcb].
    assert (Hva : value a0).
    { apply value_erase_reflect; [exact Hlca | rewrite <- E1; exact H]. }
    destruct (IHHs b0 Hlcb E2) as [u [Hu Hstep]].
    exists (tm_div a0 u). split.
    + simpl. rewrite Hu, E1. reflexivity.
    + apply ST_Div2; assumption.
  - (* ST_DivInt *)
    symmetry in E. apply erase_tm_div_inv in E.
    destruct E as [a0 [b0 [E0 [E1 E2]]]].
    subst t0. symmetry in E1; symmetry in E2.
    apply erase_tm_int_inv in E1. apply erase_tm_int_inv in E2.
    subst a0. subst b0.
    exists (tm_int (Z.div n m)). split; [reflexivity|].
    apply ST_DivInt. assumption.
  - (* ST_Arith1 *)
    symmetry in E. apply erase_tm_arith_inv in E.
    destruct E as [op0 [a0 [b0 [E0 [Eop [E1 E2]]]]]].
    subst t0. subst op. apply lc_tm_arith_inv in Hlc. destruct Hlc as [Hlca Hlcb].
    destruct (IHHs a0 Hlca E1) as [u [Hu Hstep]].
    exists (tm_arith op0 u b0). split.
    + simpl. rewrite Hu, E2. reflexivity.
    + apply ST_Arith1; assumption.
  - (* ST_Arith2 *)
    symmetry in E. apply erase_tm_arith_inv in E.
    destruct E as [op0 [a0 [b0 [E0 [Eop [E1 E2]]]]]].
    subst t0. subst op. apply lc_tm_arith_inv in Hlc. destruct Hlc as [Hlca Hlcb].
    assert (Hva : value a0).
    { apply value_erase_reflect; [exact Hlca | rewrite <- E1; exact H]. }
    destruct (IHHs b0 Hlcb E2) as [u [Hu Hstep]].
    exists (tm_arith op0 a0 u). split.
    + simpl. rewrite Hu, E1. reflexivity.
    + apply ST_Arith2; assumption.
  - (* ST_ArithInt *)
    symmetry in E. apply erase_tm_arith_inv in E.
    destruct E as [op0 [a0 [b0 [E0 [Eop [E1 E2]]]]]].
    subst t0. subst op. symmetry in E1; symmetry in E2.
    apply erase_tm_int_inv in E1. apply erase_tm_int_inv in E2.
    subst a0. subst b0.
    exists (tm_int (eval_integer_operator op0 n m)). split; [reflexivity|].
    apply ST_ArithInt.
Qed.

(* ---------- multi: transitivity and congruences ---------- *)

Lemma multi_trans : forall t u v, multi t u -> multi u v -> multi t v.
Proof.
  intros t u v H. induction H; intros H2.
  - assumption.
  - apply multi_step with (t2 := t2); auto.
Qed.

Lemma multi_app_1 : forall t1 t1' a,
  multi t1 t1' -> locally_closed_tm a ->
  multi (tm_app t1 a) (tm_app t1' a).
Proof.
  intros t1 t1' a H. induction H; intros Hlc.
  - apply multi_refl.
  - apply multi_step with (t2 := tm_app t2 a).
    + simpl. apply ST_App1; auto.
    + apply IHmulti. assumption.
Qed.

Lemma multi_app_2 : forall v1 t2 t2',
  value v1 -> multi t2 t2' ->
  multi (tm_app v1 t2) (tm_app v1 t2').
Proof.
  intros v1 t2 t2' Hv H. induction H.
  - apply multi_refl.
  - apply multi_step with (t2 := tm_app v1 t2); [apply ST_App2; auto|].
    apply IHmulti.
Qed.

Lemma multi_tapp : forall t t' T,
  multi t t' -> locally_closed_ty T ->
  multi (tm_tapp t T) (tm_tapp t' T).
Proof.
  intros t t' T H. induction H; intros Hlc.
  - apply multi_refl.
  - apply multi_step with (t2 := tm_tapp t2 T); [apply ST_TApp; auto|].
    apply IHmulti. assumption.
Qed.

Lemma multi_div_1 : forall t1 t1' a,
  multi t1 t1' -> locally_closed_tm a ->
  multi (tm_div t1 a) (tm_div t1' a).
Proof.
  intros t1 t1' a H. induction H; intros Hlc.
  - apply multi_refl.
  - apply multi_step with (t2 := tm_div t2 a).
    + simpl. apply ST_Div1; auto.
    + apply IHmulti. assumption.
Qed.

Lemma multi_div_2 : forall v1 t2 t2',
  value v1 -> multi t2 t2' ->
  multi (tm_div v1 t2) (tm_div v1 t2').
Proof.
  intros v1 t2 t2' Hv H. induction H.
  - apply multi_refl.
  - apply multi_step with (t2 := tm_div v1 t2); [apply ST_Div2; auto|].
    apply IHmulti.
Qed.

Lemma multi_arith_1 : forall op t1 t1' a,
  multi t1 t1' -> locally_closed_tm a ->
  multi (tm_arith op t1 a) (tm_arith op t1' a).
Proof.
  intros op t1 t1' a H. induction H; intros Hlc.
  - apply multi_refl.
  - apply multi_step with (t2 := tm_arith op t2 a).
    + simpl. apply ST_Arith1; auto.
    + apply IHmulti. assumption.
Qed.

Lemma multi_arith_2 : forall op v1 t2 t2',
  value v1 -> multi t2 t2' ->
  multi (tm_arith op v1 t2) (tm_arith op v1 t2').
Proof.
  intros op v1 t2 t2' Hv H. induction H.
  - apply multi_refl.
  - apply multi_step with (t2 := tm_arith op v1 t2); [apply ST_Arith2; auto|].
    apply IHmulti.
Qed.

(* ---------- predicate erasure ---------- *)

Lemma predicate_multistep_multi : forall t u,
  predicate_multistep t u -> multi t u.
Proof.
  intros t u H. induction H.
  - apply multi_refl.
  - eapply multi_step; eauto.
Qed.

Lemma multi_predicate_multistep : forall t u,
  multi t u -> predicate_multistep t u.
Proof.
  intros t u H. induction H.
  - apply PMS_Refl.
  - eapply PMS_Step; eauto.
Qed.

Lemma predicate_multistep_erase : forall t u,
  predicate_multistep t u -> predicate_multistep (erase_tm t) (erase_tm u).
Proof.
  intros. apply multi_predicate_multistep, multi_erase, predicate_multistep_multi. assumption.
Qed.

(* ================================================================ *)
(* Semantic predicate interpretation                                  *)
(* ================================================================ *)

Definition closed_env (sigma : env) : Prop :=
  forall x, fv_tm (sigma x) = [].

Definition psem (sigma : env) (p : qualifier) : Prop :=
  predicate_holds (erase_pred (subst_pred_env sigma p)).

Lemma psem_true : forall sigma, psem sigma Pred_True.
Proof. intros. unfold psem, predicate_holds. simpl. exact I. Qed.

Lemma psem_false : forall sigma, psem sigma Pred_False -> False.
Proof. intros sigma H. unfold psem, predicate_holds in H. simpl in H. exact H. Qed.

Lemma psem_and : forall sigma p q,
  psem sigma (Pred_And p q) <-> (psem sigma p /\ psem sigma q).
Proof. intros. unfold psem, predicate_holds. simpl. tauto. Qed.

Lemma psem_or : forall sigma p q,
  psem sigma (Pred_Or p q) <-> (psem sigma p \/ psem sigma q).
Proof. intros. unfold psem, predicate_holds. simpl. tauto. Qed.

Lemma psem_not : forall sigma p,
  psem sigma (Pred_Not p) <-> ~ psem sigma p.
Proof. intros. unfold psem, predicate_holds. simpl. tauto. Qed.

(* ================================================================ *)
(* Type substitution environments                                    *)
(* ================================================================ *)

Fixpoint ty_subst_env (nu : atom -> ty) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => nu X
  | Ty_Arrow T1 T2 => Ty_Arrow (ty_subst_env nu T1) (ty_subst_env nu T2)
  | Ty_All T1 => Ty_All (ty_subst_env nu T1)
  | Ty_Int => Ty_Int
  end.

Fixpoint tm_ty_subst_env (nu : atom -> ty) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T b => tm_abs (ty_subst_env nu T) (tm_ty_subst_env nu b)
  | tm_app a b => tm_app (tm_ty_subst_env nu a) (tm_ty_subst_env nu b)
  | tm_tabs b => tm_tabs (tm_ty_subst_env nu b)
  | tm_tapp a T => tm_tapp (tm_ty_subst_env nu a) (ty_subst_env nu T)
  | tm_int n => tm_int n
  | tm_div a b => tm_div (tm_ty_subst_env nu a) (tm_ty_subst_env nu b)
  | tm_arith op a b => tm_arith op (tm_ty_subst_env nu a) (tm_ty_subst_env nu b)
  end.

Fixpoint qual_ty_subst_env (nu : atom -> ty) (p : qualifier) : qualifier :=
  match p with
  | Pred_True => Pred_True
  | Pred_False => Pred_False
  | Pred_Eq a b => Pred_Eq (tm_ty_subst_env nu a) (tm_ty_subst_env nu b)
  | Pred_Lt a b => Pred_Lt (tm_ty_subst_env nu a) (tm_ty_subst_env nu b)
  | Pred_Le a b => Pred_Le (tm_ty_subst_env nu a) (tm_ty_subst_env nu b)
  | Pred_And p q => Pred_And (qual_ty_subst_env nu p) (qual_ty_subst_env nu q)
  | Pred_Or p q => Pred_Or (qual_ty_subst_env nu p) (qual_ty_subst_env nu q)
  | Pred_Not p => Pred_Not (qual_ty_subst_env nu p)
  end.

Fixpoint rty_ty_subst_env (nu : atom -> ty) (R : rty) : rty :=
  match R with
  | R_Refine T ps => R_Refine (ty_subst_env nu T) (qual_ty_subst_env nu ps)
  | R_Func R1 R2 => R_Func (rty_ty_subst_env nu R1) (rty_ty_subst_env nu R2)
  | R_Exists R1 R2 => R_Exists (rty_ty_subst_env nu R1) (rty_ty_subst_env nu R2)
  | R_Poly R1 => R_Poly (rty_ty_subst_env nu R1)
  end.

Definition tysub_ok (nu : atom -> ty) : Prop :=
  forall X, locally_closed_ty (nu X) /\ fv_ty (nu X) = [].

(* ---------- commutation of type substitution with opening ---------- *)

Lemma ty_subst_env_open_ty_rec : forall nu k U T,
  ty_subst_env nu (open_ty_rec k U T)
  = open_ty_rec k (ty_subst_env nu U) (ty_subst_env nu T).
Proof.
  intros nu k U T. revert k.
  induction T as [i|X|T1 IH1 T2 IH2|T1 IH|]; intros k; simpl.
  - destruct (Nat.eqb k i); reflexivity.
  - reflexivity.
  - f_equal; auto.
  - f_equal. apply IH.
  - reflexivity.
Qed.

Lemma tm_ty_subst_env_open_tm_ty_rec : forall nu k U t,
  tm_ty_subst_env nu (open_tm_ty_rec k U t)
  = open_tm_ty_rec k (ty_subst_env nu U) (tm_ty_subst_env nu t).
Proof.
  intros nu k U t. revert k.
  induction t as [i|x|T b IH|a IHa b IHb|b IH|a IHa T|n|a IHa b IHb|op a IHa b IHb];
    intros k; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite ty_subst_env_open_ty_rec. f_equal. apply IH.
  - f_equal; auto.
  - f_equal; auto.
  - rewrite ty_subst_env_open_ty_rec. f_equal; auto.
  - reflexivity.
  - f_equal; auto.
  - f_equal; auto.
Qed.

Lemma qual_ty_subst_env_open_pred_ty_rec : forall nu k U p,
  qual_ty_subst_env nu (open_pred_ty_rec k U p)
  = open_pred_ty_rec k (ty_subst_env nu U) (qual_ty_subst_env nu p).
Proof.
  intros nu k U p. revert k.
  induction p; intros k; simpl; auto.
  - f_equal; apply tm_ty_subst_env_open_tm_ty_rec.
  - f_equal; apply tm_ty_subst_env_open_tm_ty_rec.
  - f_equal; apply tm_ty_subst_env_open_tm_ty_rec.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
Qed.

Lemma rty_ty_subst_env_open_rty_ty_rec : forall nu k U R,
  rty_ty_subst_env nu (open_rty_ty_rec k U R)
  = open_rty_ty_rec k (ty_subst_env nu U) (rty_ty_subst_env nu R).
Proof.
  intros nu k U R. revert k.
  induction R; intros k; simpl.
  - rewrite ty_subst_env_open_ty_rec. rewrite qual_ty_subst_env_open_pred_ty_rec. reflexivity.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal. apply IHR.
Qed.

Lemma tm_ty_subst_env_open_tm_rec : forall nu k u t,
  tm_ty_subst_env nu (open_tm_rec k u t)
  = open_tm_rec k (tm_ty_subst_env nu u) (tm_ty_subst_env nu t).
Proof.
  intros nu k u t. revert k.
  induction t as [i|x|T b IH|a IHa b IHb|b IH|a IHa T|n|a IHa b IHb|op a IHa b IHb];
    intros k; simpl.
  - destruct (Nat.eqb k i); reflexivity.
  - reflexivity.
  - f_equal. apply IH.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
  - reflexivity.
  - f_equal; auto.
  - f_equal; auto.
Qed.

Lemma qual_ty_subst_env_open_pred_tm_rec : forall nu k u p,
  qual_ty_subst_env nu (open_pred_tm_rec k u p)
  = open_pred_tm_rec k (tm_ty_subst_env nu u) (qual_ty_subst_env nu p).
Proof.
  intros nu k u p. revert k.
  induction p; intros k; simpl; auto.
  - f_equal; apply tm_ty_subst_env_open_tm_rec.
  - f_equal; apply tm_ty_subst_env_open_tm_rec.
  - f_equal; apply tm_ty_subst_env_open_tm_rec.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
Qed.

Lemma rty_ty_subst_env_open_rty_tm_rec : forall nu k w R,
  rty_ty_subst_env nu (open_rty_tm_rec k w R)
  = open_rty_tm_rec k (tm_ty_subst_env nu w) (rty_ty_subst_env nu R).
Proof.
  intros nu k w R. revert k.
  induction R; intros k; simpl.
  - rewrite qual_ty_subst_env_open_pred_tm_rec. reflexivity.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal. apply IHR.
Qed.

(* ---------- composition of type and term substitution ---------- *)

Lemma tm_ty_subst_env_subst_env : forall nu sigma t,
  tm_ty_subst_env nu (subst_env sigma t)
  = subst_env (fun x => tm_ty_subst_env nu (sigma x)) (tm_ty_subst_env nu t).
Proof.
  intros nu sigma t.
  induction t as [i|x|T b IH|a IHa b IHb|b IH|a IHa T|n|a IHa b IHb|op a IHa b IHb];
    simpl.
  - reflexivity.
  - reflexivity.
  - f_equal. apply IH.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
  - reflexivity.
  - f_equal; auto.
  - f_equal; auto.
Qed.

Lemma qual_ty_subst_env_subst_pred_env : forall nu sigma p,
  qual_ty_subst_env nu (subst_pred_env sigma p)
  = subst_pred_env (fun x => tm_ty_subst_env nu (sigma x)) (qual_ty_subst_env nu p).
Proof.
  intros nu sigma p. induction p; simpl; auto;
    try (f_equal; apply tm_ty_subst_env_subst_env).
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
Qed.

(* ---------- nil lemmas ---------- *)

Lemma ty_subst_env_nil : forall nu T, fv_ty T = [] -> ty_subst_env nu T = T.
Proof.
  intros nu T. induction T; simpl; intros H.
  - reflexivity.
  - simpl in H. discriminate.
  - f_equal; auto.
  - f_equal; auto.
  - reflexivity.
Qed.

Lemma tm_ty_subst_env_nil : forall nu t, ftv_tm t = [] -> tm_ty_subst_env nu t = t.
Proof.
  intros nu t.
  induction t as [i|x|T b IH|a IHa b IHb|b IH|a IHa T|n|a IHa b IHb|op a IHa b IHb];
    simpl; intros H.
  - reflexivity.
  - reflexivity.
  - apply app_eq_nil in H. destruct H as [HT Hb].
    rewrite ty_subst_env_nil by exact HT. f_equal. apply IH. exact Hb.
  - apply app_eq_nil in H. destruct H as [H1 H2]. f_equal; auto.
  - f_equal. apply IH. exact H.
  - apply app_eq_nil in H. destruct H as [H1 H2]. f_equal; auto.
    rewrite ty_subst_env_nil by exact H2. reflexivity.
  - reflexivity.
  - apply app_eq_nil in H. destruct H as [H1 H2]. f_equal; auto.
  - apply app_eq_nil in H. destruct H as [H1 H2]. f_equal; auto.
Qed.

Fixpoint pred_ftv_nil (p : qualifier) : Prop :=
  match p with
  | Pred_True | Pred_False => True
  | Pred_Eq a b | Pred_Lt a b | Pred_Le a b => ftv_tm a = [] /\ ftv_tm b = []
  | Pred_And p q | Pred_Or p q => pred_ftv_nil p /\ pred_ftv_nil q
  | Pred_Not p => pred_ftv_nil p
  end.

Fixpoint pred_fv_nil (p : qualifier) : Prop :=
  match p with
  | Pred_True | Pred_False => True
  | Pred_Eq a b | Pred_Lt a b | Pred_Le a b => fv_tm a = [] /\ fv_tm b = []
  | Pred_And p q | Pred_Or p q => pred_fv_nil p /\ pred_fv_nil q
  | Pred_Not p => pred_fv_nil p
  end.

Lemma predicate_closed_ftv : forall p, predicate_closed p -> pred_ftv_nil p.
Proof.
  intros p H. induction p; simpl in *; auto.
  - destruct H as [H1 [H2 [H3 [H4 [H5 H6]]]]]. auto.
  - destruct H as [H1 [H2 [H3 [H4 [H5 H6]]]]]. auto.
  - destruct H as [H1 [H2 [H3 [H4 [H5 H6]]]]]. auto.
  - destruct H as [H1 H2]. split; auto.
  - destruct H as [H1 H2]. split; auto.
  - auto.
Qed.

Lemma predicate_closed_fv : forall p, predicate_closed p -> pred_fv_nil p.
Proof.
  intros p H. induction p; simpl in *; auto.
  - destruct H as [H1 [H2 [H3 [H4 [H5 H6]]]]]. auto.
  - destruct H as [H1 [H2 [H3 [H4 [H5 H6]]]]]. auto.
  - destruct H as [H1 [H2 [H3 [H4 [H5 H6]]]]]. auto.
  - destruct H as [H1 H2]. split; auto.
  - destruct H as [H1 H2]. split; auto.
  - auto.
Qed.

Lemma qual_ty_subst_env_nil : forall nu p,
  pred_ftv_nil p -> qual_ty_subst_env nu p = p.
Proof.
  intros nu p. induction p; simpl; intros H; auto.
  - destruct H as [H1 H2]. f_equal; apply tm_ty_subst_env_nil; auto.
  - destruct H as [H1 H2]. f_equal; apply tm_ty_subst_env_nil; auto.
  - destruct H as [H1 H2]. f_equal; apply tm_ty_subst_env_nil; auto.
  - destruct H as [H1 H2]. f_equal; auto.
  - destruct H as [H1 H2]. f_equal; auto.
  - f_equal; auto.
Qed.

Lemma qual_subst_env_nil : forall sigma p,
  (forall x, fv_tm (sigma x) = []) -> pred_fv_nil p -> subst_pred_env sigma p = p.
Proof.
  intros sigma p. induction p; simpl; intros Hcl H; auto.
  - destruct H as [H1 H2]. f_equal.
    + apply subst_env_nil_id. assumption.
    + apply subst_env_nil_id. assumption.
  - destruct H as [H1 H2]. f_equal.
    + apply subst_env_nil_id. assumption.
    + apply subst_env_nil_id. assumption.
  - destruct H as [H1 H2]. f_equal.
    + apply subst_env_nil_id. assumption.
    + apply subst_env_nil_id. assumption.
  - destruct H as [H1 H2]. f_equal; auto.
  - destruct H as [H1 H2]. f_equal; auto.
  - f_equal; auto.
Qed.

Theorem never_stuck : forall (t t' : tm) (R : rty),
  has_rtype [] empty_rcontext t R ->
  multi t t' ->
  value t' \/ exists t'' : tm, t' --> t''.
Proof.

Qed.

End SystemFRefinementTask.
