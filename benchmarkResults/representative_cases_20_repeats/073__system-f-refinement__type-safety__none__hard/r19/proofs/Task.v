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
(* Infrastructure for the semantic proof of type safety.            *)
(* ================================================================ *)

(* ---------- fresh atoms and list helpers ---------- *)

Lemma in_max_atom : forall (L : list atom) (x : atom), In x L -> x <= max_atom L.
Proof.
  induction L as [| a L IH]; intros x Hin; simpl in *.
  - contradiction.
  - destruct Hin as [-> | Hin].
    + apply Nat.le_max_l.
    + apply Nat.le_trans with (max_atom L).
      * apply IH; auto.
      * apply Nat.le_max_r.
Qed.

Lemma fresh_notin : forall (L : list atom), ~ In (fresh L) L.
Proof.
  intros L Hin. unfold fresh in Hin.
  pose proof (in_max_atom L _ Hin). lia.
Qed.

Fixpoint concat_lists (ls : list (list atom)) : list atom :=
  match ls with
  | [] => []
  | L :: ls' => L ++ concat_lists ls'
  end.

Lemma in_concat_lists : forall (ls : list (list atom)) (L : list atom) (x : atom),
  In L ls -> In x L -> In x (concat_lists ls).
Proof.
  induction ls as [|A ls IH]; simpl; intros L x Hin Hx.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + subst A. apply in_app_iff; auto.
    + apply in_app_iff; right. apply IH with (L := L); auto.
Qed.

Lemma fresh_notin_concat : forall (ls : list (list atom)) (L : list atom),
  In L ls -> ~ In (fresh (concat_lists ls)) L.
Proof.
  intros ls L Hin Hx.
  apply (fresh_notin (concat_lists ls)).
  apply (in_concat_lists ls L); auto.
Qed.

Lemma notin_cons : forall (x y : atom) (L : list atom), ~ In x (y :: L) -> x <> y /\ ~ In x L.
Proof. intros x y L H; simpl in H; intuition. Qed.

Lemma notin_app_iff : forall (x : atom) (A B : list atom),
  ~ In x (A ++ B) <-> ~ In x A /\ ~ In x B.
Proof. intros; rewrite in_app_iff. intuition. Qed.

(* ---------- free variables of qualifiers and refinement types ---------- *)

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
  | R_Func R1 R2 => fv_rty R1 ++ fv_rty R2
  | R_Exists R1 R2 => fv_rty R1 ++ fv_rty R2
  | R_Poly R => fv_rty R
  end.

Fixpoint ftv_rty (R : rty) : list atom :=
  match R with
  | R_Refine T ps => fv_ty T ++ ftv_qual ps
  | R_Func R1 R2 => ftv_rty R1 ++ ftv_rty R2
  | R_Exists R1 R2 => ftv_rty R1 ++ ftv_rty R2
  | R_Poly R => ftv_rty R
  end.

(* ---------- simultaneous free-variable substitutions ---------- *)

Fixpoint subst_tm (s : atom -> tm) (t : tm) {struct t} : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => s x
  | tm_abs T t1 => tm_abs T (subst_tm s t1)
  | tm_app t1 t2 => tm_app (subst_tm s t1) (subst_tm s t2)
  | tm_tabs t1 => tm_tabs (subst_tm s t1)
  | tm_tapp t1 T => tm_tapp (subst_tm s t1) T
  | tm_int n => tm_int n
  | tm_div t1 t2 => tm_div (subst_tm s t1) (subst_tm s t2)
  | tm_arith op t1 t2 => tm_arith op (subst_tm s t1) (subst_tm s t2)
  end.

Fixpoint subst_ty (s : atom -> ty) (T : ty) {struct T} : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => s X
  | Ty_Arrow T1 T2 => Ty_Arrow (subst_ty s T1) (subst_ty s T2)
  | Ty_All T1 => Ty_All (subst_ty s T1)
  | Ty_Int => Ty_Int
  end.

Fixpoint subst_tm_ty (s : atom -> ty) (t : tm) {struct t} : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T t1 => tm_abs (subst_ty s T) (subst_tm_ty s t1)
  | tm_app t1 t2 => tm_app (subst_tm_ty s t1) (subst_tm_ty s t2)
  | tm_tabs t1 => tm_tabs (subst_tm_ty s t1)
  | tm_tapp t1 T => tm_tapp (subst_tm_ty s t1) (subst_ty s T)
  | tm_int n => tm_int n
  | tm_div t1 t2 => tm_div (subst_tm_ty s t1) (subst_tm_ty s t2)
  | tm_arith op t1 t2 => tm_arith op (subst_tm_ty s t1) (subst_tm_ty s t2)
  end.

Fixpoint subst_qual_tm (s : atom -> tm) (p : qualifier) {struct p} : qualifier :=
  match p with
  | Pred_True => Pred_True
  | Pred_False => Pred_False
  | Pred_Eq t1 t2 => Pred_Eq (subst_tm s t1) (subst_tm s t2)
  | Pred_Lt t1 t2 => Pred_Lt (subst_tm s t1) (subst_tm s t2)
  | Pred_Le t1 t2 => Pred_Le (subst_tm s t1) (subst_tm s t2)
  | Pred_And p1 p2 => Pred_And (subst_qual_tm s p1) (subst_qual_tm s p2)
  | Pred_Or p1 p2 => Pred_Or (subst_qual_tm s p1) (subst_qual_tm s p2)
  | Pred_Not p1 => Pred_Not (subst_qual_tm s p1)
  end.

Fixpoint subst_qual_ty (s : atom -> ty) (p : qualifier) {struct p} : qualifier :=
  match p with
  | Pred_True => Pred_True
  | Pred_False => Pred_False
  | Pred_Eq t1 t2 => Pred_Eq (subst_tm_ty s t1) (subst_tm_ty s t2)
  | Pred_Lt t1 t2 => Pred_Lt (subst_tm_ty s t1) (subst_tm_ty s t2)
  | Pred_Le t1 t2 => Pred_Le (subst_tm_ty s t1) (subst_tm_ty s t2)
  | Pred_And p1 p2 => Pred_And (subst_qual_ty s p1) (subst_qual_ty s p2)
  | Pred_Or p1 p2 => Pred_Or (subst_qual_ty s p1) (subst_qual_ty s p2)
  | Pred_Not p1 => Pred_Not (subst_qual_ty s p1)
  end.

Fixpoint subst_rty_tm (s : atom -> tm) (R : rty) {struct R} : rty :=
  match R with
  | R_Refine T ps => R_Refine T (subst_qual_tm s ps)
  | R_Func R1 R2 => R_Func (subst_rty_tm s R1) (subst_rty_tm s R2)
  | R_Exists R1 R2 => R_Exists (subst_rty_tm s R1) (subst_rty_tm s R2)
  | R_Poly R1 => R_Poly (subst_rty_tm s R1)
  end.

Fixpoint subst_rty_ty (s : atom -> ty) (R : rty) {struct R} : rty :=
  match R with
  | R_Refine T ps => R_Refine (subst_ty s T) (subst_qual_ty s ps)
  | R_Func R1 R2 => R_Func (subst_rty_ty s R1) (subst_rty_ty s R2)
  | R_Exists R1 R2 => R_Exists (subst_rty_ty s R1) (subst_rty_ty s R2)
  | R_Poly R1 => R_Poly (subst_rty_ty s R1)
  end.

Definition close_tm (s : atom -> tm) (ts : atom -> ty) (t : tm) : tm :=
  subst_tm s (subst_tm_ty ts t).

Definition close_qual (s : atom -> tm) (ts : atom -> ty) (p : qualifier) : qualifier :=
  subst_qual_tm s (subst_qual_ty ts p).

Definition close_rty (s : atom -> tm) (ts : atom -> ty) (R : rty) : rty :=
  subst_rty_tm s (subst_rty_ty ts R).

Definition upd (s : atom -> tm) (x : atom) (u : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then u else s y.

Definition upd_ty (s : atom -> ty) (x : atom) (U : ty) : atom -> ty :=
  fun y => if Nat.eqb x y then U else s y.

(* ---------- locally closed definitions and monotonicity ---------- *)

Definition lc0_tm (t : tm) : Prop := lc_tm_at 0 0 t.
Definition lc0_ty (T : ty) : Prop := lc_ty_at 0 T.
Definition lc0_tm_env (s : atom -> tm) : Prop := forall x, lc_tm_at 0 0 (s x).
Definition lc0_ty_env (s : atom -> ty) : Prop := forall X, lc_ty_at 0 (s X).

Lemma lc_ty_at_mono : forall K K' T, lc_ty_at K T -> K <= K' -> lc_ty_at K' T.
Proof.
  intros K K' T H. revert K'.
  induction H; intros K' HK.
  - apply lc_ty_bvar. lia.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; [apply IHlc_ty_at1; lia | apply IHlc_ty_at2; lia].
  - apply lc_ty_all. apply IHlc_ty_at. lia.
  - apply lc_ty_int.
Qed.

Lemma lc_tm_at_mono : forall K k t, lc_tm_at K k t ->
  forall K' k', K <= K' -> k <= k' -> lc_tm_at K' k' t.
Proof.
  intros K k t H. induction H; intros K' k' HK Hk.
  - apply lc_tm_bvar. lia.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + eapply lc_ty_at_mono; eauto.
    + apply IHlc_tm_at; lia.
  - apply lc_tm_app; [apply IHlc_tm_at1; lia | apply IHlc_tm_at2; lia].
  - apply lc_tm_tabs. apply IHlc_tm_at; lia.
  - apply lc_tm_tapp.
    + apply IHlc_tm_at; auto.
    + eapply lc_ty_at_mono; eauto.
  - apply lc_tm_int.
  - apply lc_tm_div; [apply IHlc_tm_at1; lia | apply IHlc_tm_at2; lia].
  - apply lc_tm_arith; [apply IHlc_tm_at1; lia | apply IHlc_tm_at2; lia].
Qed.

Lemma open_tm_rec_lc : forall K k t, lc_tm_at K k t -> forall u, open_tm_rec k u t = t.
Proof.
  intros K k t H. induction H; intros u; simpl.
  - destruct (Nat.eqb k i) eqn:E; [| reflexivity].
    apply Nat.eqb_eq in E. exfalso. lia.
  - reflexivity.
  - f_equal. apply IHlc_tm_at.
  - f_equal; [apply IHlc_tm_at1 | apply IHlc_tm_at2].
  - f_equal. apply IHlc_tm_at.
  - f_equal. apply IHlc_tm_at.
  - reflexivity.
  - f_equal; [apply IHlc_tm_at1 | apply IHlc_tm_at2].
  - f_equal; [apply IHlc_tm_at1 | apply IHlc_tm_at2].
Qed.

Lemma open_ty_rec_lc : forall K T, lc_ty_at K T -> forall U, open_ty_rec K U T = T.
Proof.
  intros K T H. induction H; intros U; simpl.
  - destruct (Nat.eqb k i) eqn:E; [| reflexivity].
    apply Nat.eqb_eq in E. exfalso. lia.
  - reflexivity.
  - f_equal; [apply IHlc_ty_at1 | apply IHlc_ty_at2].
  - f_equal. apply IHlc_ty_at.
  - reflexivity.
Qed.

Lemma open_tm_ty_rec_lc : forall K k t, lc_tm_at K k t ->
  forall U, open_tm_ty_rec K U t = t.
Proof.
  intros K k t H. induction H; intros U; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + apply open_ty_rec_lc; auto.
    + apply IHlc_tm_at.
  - f_equal; [apply IHlc_tm_at1 | apply IHlc_tm_at2].
  - f_equal. apply IHlc_tm_at.
  - f_equal.
    + apply IHlc_tm_at.
    + apply open_ty_rec_lc; auto.
  - reflexivity.
  - f_equal; [apply IHlc_tm_at1 | apply IHlc_tm_at2].
  - f_equal; [apply IHlc_tm_at1 | apply IHlc_tm_at2].
Qed.

(* ---------- lc preservation under substitutions ---------- *)

Lemma lc_ty_subst_ty : forall s T, lc0_ty_env s -> forall K,
  lc_ty_at K T -> lc_ty_at K (subst_ty s T).
Proof.
  intros s T Hs K H.
  induction H; simpl.
  - apply lc_ty_bvar. auto.
  - apply lc_ty_at_mono with (K := 0); [apply Hs | lia].
  - apply lc_ty_arrow; [apply IHlc_ty_at1 | apply IHlc_ty_at2].
  - apply lc_ty_all. apply IHlc_ty_at.
  - apply lc_ty_int.
Qed.

Lemma lc_tm_subst_tm : forall s t, lc0_tm_env s -> forall K k,
  lc_tm_at K k t -> lc_tm_at K k (subst_tm s t).
Proof.
  intros s t Hs K k H.
  induction H; simpl.
  - apply lc_tm_bvar. auto.
  - apply lc_tm_at_mono with (K := 0) (k := 0); [apply Hs | lia | lia].
  - apply lc_tm_abs.
    + eapply lc_ty_at_mono; eauto.
    + apply IHlc_tm_at.
  - apply lc_tm_app; [apply IHlc_tm_at1 | apply IHlc_tm_at2].
  - apply lc_tm_tabs. apply IHlc_tm_at.
  - apply lc_tm_tapp.
    + apply IHlc_tm_at.
    + eapply lc_ty_at_mono; eauto.
  - apply lc_tm_int.
  - apply lc_tm_div; [apply IHlc_tm_at1 | apply IHlc_tm_at2].
  - apply lc_tm_arith; [apply IHlc_tm_at1 | apply IHlc_tm_at2].
Qed.

Lemma lc_tm_subst_tm_ty : forall s t, lc0_ty_env s -> forall K k,
  lc_tm_at K k t -> lc_tm_at K k (subst_tm_ty s t).
Proof.
  intros s t Hs K k H.
  induction H; simpl.
  - apply lc_tm_bvar. auto.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + apply lc_ty_subst_ty; auto.
    + apply IHlc_tm_at.
  - apply lc_tm_app; [apply IHlc_tm_at1 | apply IHlc_tm_at2].
  - apply lc_tm_tabs. apply IHlc_tm_at.
  - apply lc_tm_tapp.
    + apply IHlc_tm_at.
    + apply lc_ty_subst_ty; auto.
  - apply lc_tm_int.
  - apply lc_tm_div; [apply IHlc_tm_at1 | apply IHlc_tm_at2].
  - apply lc_tm_arith; [apply IHlc_tm_at1 | apply IHlc_tm_at2].
Qed.

(* ---------- commutation of substitution and opening ---------- *)

Lemma subst_tm_open_tm_rec : forall (s : atom -> tm) k u t,
  lc_tm_at 0 0 u ->
  lc0_tm_env s ->
  subst_tm s (open_tm_rec k u t) = open_tm_rec k (subst_tm s u) (subst_tm s t).
Proof.
  intros s k u t Hu Hs. revert k u Hu.
  induction t; intros k u Hu; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - apply eq_sym. apply open_tm_rec_lc with (K := 0).
    apply lc_tm_at_mono with (K := 0) (k := 0); [apply Hs | lia | lia].
  - f_equal. apply IHt; auto.
  - f_equal; [apply IHt1; auto | apply IHt2; auto].
  - f_equal. apply IHt; auto.
  - f_equal. apply IHt; auto.
  - reflexivity.
  - f_equal; [apply IHt1; auto | apply IHt2; auto].
  - f_equal; [apply IHt1; auto | apply IHt2; auto].
Qed.

Lemma subst_tm_ty_open_tm_rec : forall (s : atom -> ty) k u t,
  subst_tm_ty s (open_tm_rec k u t) = open_tm_rec k (subst_tm_ty s u) (subst_tm_ty s t).
Proof.
  intros s k u t. revert k u.
  induction t; intros k u; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - reflexivity.
  - f_equal. apply IHt.
  - f_equal; [apply IHt1 | apply IHt2].
  - f_equal. apply IHt.
  - f_equal. apply IHt.
  - reflexivity.
  - f_equal; [apply IHt1 | apply IHt2].
  - f_equal; [apply IHt1 | apply IHt2].
Qed.

Lemma subst_ty_open_ty_rec : forall (s : atom -> ty) k u T,
  lc0_ty_env s ->
  subst_ty s (open_ty_rec k u T) = open_ty_rec k (subst_ty s u) (subst_ty s T).
Proof.
  intros s k u T Hs. revert k u.
  induction T; intros k u; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - apply eq_sym. apply open_ty_rec_lc with (K := k).
    apply lc_ty_at_mono with (K := 0); [apply Hs | lia].
  - f_equal; [apply IHT1; auto | apply IHT2; auto].
  - f_equal. apply IHT; auto.
  - reflexivity.
Qed.

Lemma subst_tm_ty_open_tm_ty_rec : forall (s : atom -> ty) k U t,
  lc0_ty_env s ->
  subst_tm_ty s (open_tm_ty_rec k U t) = open_tm_ty_rec k (subst_ty s U) (subst_tm_ty s t).
Proof.
  intros s k U t Hs. revert k U.
  induction t; intros k U; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + apply subst_ty_open_ty_rec; auto.
    + apply IHt; auto.
  - f_equal; [apply IHt1; auto | apply IHt2; auto].
  - f_equal. apply IHt; auto.
  - f_equal.
    + apply IHt; auto.
    + apply subst_ty_open_ty_rec; auto.
  - reflexivity.
  - f_equal; [apply IHt1; auto | apply IHt2; auto].
  - f_equal; [apply IHt1; auto | apply IHt2; auto].
Qed.

Lemma subst_tm_open_tm_ty_rec : forall (s : atom -> tm) k U t,
  lc0_tm_env s ->
  subst_tm s (open_tm_ty_rec k U t) = open_tm_ty_rec k U (subst_tm s t).
Proof.
  intros s k U t Hs. revert k U.
  induction t; intros k U; simpl.
  - reflexivity.
  - apply eq_sym. apply open_tm_ty_rec_lc with (K := k) (k := k).
    apply lc_tm_at_mono with (K := 0) (k := 0) (K' := k) (k' := k);
      [apply Hs | lia | lia].
  - f_equal. apply IHt; auto.
  - f_equal; [apply IHt1; auto | apply IHt2; auto].
  - f_equal. apply IHt; auto.
  - f_equal. apply IHt; auto.
  - reflexivity.
  - f_equal; [apply IHt1; auto | apply IHt2; auto].
  - f_equal; [apply IHt1; auto | apply IHt2; auto].
Qed.

Lemma close_tm_open_tm : forall s ts u t,
  lc_tm_at 0 0 u -> lc0_tm_env s -> lc0_ty_env ts ->
  close_tm s ts (open_tm t u) = open_tm (close_tm s ts t) (close_tm s ts u).
Proof.
  intros s ts u t Hu Hs Hts. unfold close_tm, open_tm.
  rewrite subst_tm_ty_open_tm_rec by auto.
  rewrite subst_tm_open_tm_rec.
  - reflexivity.
  - apply lc_tm_subst_tm_ty; auto.
  - auto.
Qed.

Lemma close_tm_open_tm_ty : forall s ts U t,
  lc0_tm_env s -> lc0_ty_env ts ->
  close_tm s ts (open_tm_ty t U) = open_tm_ty (close_tm s ts t) (subst_ty ts U).
Proof.
  intros s ts U t Hs Hts. unfold close_tm, open_tm_ty.
  rewrite subst_tm_ty_open_tm_ty_rec by auto.
  rewrite subst_tm_open_tm_ty_rec by auto.
  reflexivity.
Qed.


(* ---------- opening inversion for local closedness ---------- *)

Lemma lc_ty_open_ty_inv : forall K U T, lc_ty_at K (open_ty_rec K U T) -> lc_ty_at (S K) T.
Proof.
  intros K U T. revert K U.
  induction T as [ i | X | T1 IHT1 T2 IHT2 | T1 IHT1 | ]; intros K U H; simpl in *.
  - destruct (Nat.eqb K i) eqn:E.
    + apply Nat.eqb_eq in E. subst i. apply lc_ty_bvar. lia.
    + inversion H; subst. apply lc_ty_bvar. lia.
  - apply lc_ty_fvar.
  - inversion H; subst. apply lc_ty_arrow.
    + apply IHT1 with (K := K) (U := U); auto.
    + apply IHT2 with (K := K) (U := U); auto.
  - inversion H; subst. apply lc_ty_all. apply IHT1 with (K := S K) (U := U); auto.
  - apply lc_ty_int.
Qed.

Lemma lc_tm_open_tm_inv : forall K k u t,
  lc_tm_at K k (open_tm_rec k u t) -> lc_tm_at K (S k) t.
Proof.
  intros K k u t. revert K k u.
  induction t as [ n | x | T t1 IHt1 | t1 IHt1 t2 IHt2 | t1 IHt1 | t1 IHt1 T
                 | z | t1 IHt1 t2 IHt2 | op t1 IHt1 t2 IHt2 ];
    intros K k u H; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. apply lc_tm_bvar. lia.
    + inversion H; subst. apply lc_tm_bvar. lia.
  - apply lc_tm_fvar.
  - inversion H; subst. apply lc_tm_abs.
    + auto.
    + apply IHt1 with (k := S k) (u := u); auto.
  - inversion H; subst. apply lc_tm_app.
    + apply IHt1 with (k := k) (u := u); auto.
    + apply IHt2 with (k := k) (u := u); auto.
  - inversion H; subst. apply lc_tm_tabs.
    apply IHt1 with (K := S K) (k := k) (u := u); auto.
  - inversion H; subst. apply lc_tm_tapp.
    + apply IHt1 with (k := k) (u := u); auto.
    + auto.
  - apply lc_tm_int.
  - inversion H; subst. apply lc_tm_div.
    + apply IHt1 with (k := k) (u := u); auto.
    + apply IHt2 with (k := k) (u := u); auto.
  - inversion H; subst. apply lc_tm_arith.
    + apply IHt1 with (k := k) (u := u); auto.
    + apply IHt2 with (k := k) (u := u); auto.
Qed.

Lemma lc_tm_open_tm_ty_inv : forall K k U t,
  lc_tm_at K k (open_tm_ty_rec K U t) -> lc_tm_at (S K) k t.
Proof.
  intros K k U t. revert K k U.
  induction t as [ n | x | T t1 IHt1 | t1 IHt1 t2 IHt2 | t1 IHt1 | t1 IHt1 T
                 | z | t1 IHt1 t2 IHt2 | op t1 IHt1 t2 IHt2 ];
    intros K k U H; simpl in *.
  - inversion H; subst. apply lc_tm_bvar. lia.
  - apply lc_tm_fvar.
  - inversion H; subst. apply lc_tm_abs.
    + apply lc_ty_open_ty_inv with (K := K) (U := U); auto.
    + apply IHt1 with (k := S k) (U := U); auto.
  - inversion H; subst. apply lc_tm_app.
    + apply IHt1 with (k := k) (U := U); auto.
    + apply IHt2 with (k := k) (U := U); auto.
  - inversion H; subst. apply lc_tm_tabs.
    apply IHt1 with (K := S K) (k := k) (U := U); auto.
  - inversion H; subst. apply lc_tm_tapp.
    + apply IHt1 with (k := k) (U := U); auto.
    + apply lc_ty_open_ty_inv with (K := K) (U := U); auto.
  - apply lc_tm_int.
  - inversion H; subst. apply lc_tm_div.
    + apply IHt1 with (k := k) (U := U); auto.
    + apply IHt2 with (k := k) (U := U); auto.
  - inversion H; subst. apply lc_tm_arith.
    + apply IHt1 with (k := k) (U := U); auto.
    + apply IHt2 with (k := k) (U := U); auto.
Qed.

(* ---------- erase and well-formedness ---------- *)

Lemma erase_open_rty_tm_rec : forall k u R, erase (open_rty_tm_rec k u R) = erase R.
Proof.
  intros k u R. revert k u.
  induction R; intros k u; simpl; congruence.
Qed.

Lemma erase_open_rty_tm : forall R u, erase (open_rty_tm R u) = erase R.
Proof. intros; apply erase_open_rty_tm_rec. Qed.

Lemma erase_open_rty_ty_rec : forall k U R,
  erase (open_rty_ty_rec k U R) = open_ty_rec k U (erase R).
Proof.
  intros k U R. revert k U.
  induction R; intros k U; simpl; congruence.
Qed.

Lemma erase_open_rty_ty : forall R U, erase (open_rty_ty R U) = open_ty (erase R) U.
Proof. intros; apply erase_open_rty_ty_rec. Qed.

Lemma erase_subst_rty_ty : forall s R, erase (subst_rty_ty s R) = subst_ty s (erase R).
Proof.
  intros s R. induction R; simpl; congruence.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> lc_ty_at 0 T.
Proof.
  intros Delta T H.
  induction H as [ Delta X HX | Delta T1 T2 H1 IH1 H2 IH2
                 | L Delta T H IH | Delta ].
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; auto.
  - apply lc_ty_all.
    eapply lc_ty_open_ty_inv.
    apply IH. apply fresh_notin.
  - apply lc_ty_int.
Qed.

Lemma wf_rty_erase : forall Delta RGamma R, wf_rty Delta RGamma R -> wf_ty Delta (erase R).
Proof.
  intros Delta RGamma R H.
  induction H as [ L Delta RGamma T ps Hwf Hq
                 | L Delta RGamma R1 R2 H1 IH1 H2 IH2
                 | L Delta RGamma R1 R2 H1 IH1 H2 IH2
                 | L Delta RGamma R H IH ].
  - auto.
  - simpl. apply WF_Arrow.
    + auto.
    + specialize (IH2 (fresh L) (fresh_notin L)).
      rewrite erase_open_rty_tm in IH2. apply IH2.
  - simpl. specialize (IH2 (fresh L) (fresh_notin L)).
    rewrite erase_open_rty_tm in IH2. apply IH2.
  - simpl. apply WF_All with (L := L). intros X HX.
    specialize (IH X HX). rewrite erase_open_rty_ty in IH. apply IH.
Qed.

(* ---------- values are locally closed ---------- *)

Lemma value_lc : forall v, value v -> lc_tm_at 0 0 v.
Proof.
  intros v H. induction H; simpl; auto.
  - apply lc_tm_int.
Qed.

(* ---------- canonical forms ---------- *)

Definition canon (T : ty) (v : tm) : Prop :=
  match T with
  | Ty_Int => exists n : Z, v = tm_int n
  | Ty_Arrow _ _ => exists T' body, v = tm_abs T' body
  | Ty_All _ => exists body, v = tm_tabs body
  | Ty_FVar _ | Ty_BVar _ => False
  end.

Lemma has_type_canon : forall Delta Gamma v T,
  has_type Delta Gamma v T -> value v -> canon T v.
Proof.
  intros Delta Gamma v T H. induction H; intros Hv; simpl; try (inversion Hv).
  - eexists; eexists; reflexivity.
  - eexists; reflexivity.
  - eexists; reflexivity.
Qed.

(* ---------- has_rtype terms are locally closed ---------- *)

Lemma has_rtype_lc : forall Delta RGamma t R,
  has_rtype Delta RGamma t R -> lc_tm_at 0 0 t.
Proof.
  intros Delta RGamma t R H.
  induction H as [ Delta RGamma x R Hlook Hwf
                 | L Delta RGamma R1 body R2 Hwf Hbody IHb
                 | Delta RGamma t1 t2 R1 R2 H1 IH1 H2 IH2
                 | L Delta RGamma body R H IH
                 | Delta RGamma t R U Ht IHt Hwf
                 | Delta RGamma n
                 | Delta RGamma t1 t2 H1 IH1 H2 IH2
                 | Delta RGamma op t1 t2 H1 IH1 H2 IH2
                 | Delta RGamma v T ps Htype Hval Hwf Hcl Hholds
                 | Delta RGamma t R S Ht IHt Hwf Hsub ].
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + apply wf_ty_lc with (Delta := Delta).
      apply wf_rty_erase with (RGamma := RGamma). auto.
    + apply lc_tm_open_tm_inv with (k := 0) (u := tm_fvar (fresh L)) (K := 0).
      apply IHb. apply fresh_notin.
  - apply lc_tm_app; auto.
  - apply lc_tm_tabs.
    apply lc_tm_open_tm_ty_inv with (K := 0) (U := Ty_FVar (fresh L)) (k := 0).
    apply IH. apply fresh_notin.
  - apply lc_tm_tapp; auto.
    apply wf_ty_lc with (Delta := Delta). auto.
  - apply lc_tm_int.
  - apply lc_tm_div; auto.
  - apply lc_tm_arith; auto.
  - apply value_lc. auto.
  - auto.
Qed.


(* ---------- environments ---------- *)

Definition env_ok (s : atom -> tm) (ts : atom -> ty) : Prop :=
  (forall x, value (s x) /\ fv_tm (s x) = []) /\ (forall X, lc_ty_at 0 (ts X)).

Lemma env_ok_lc : forall s ts, env_ok s ts -> lc0_tm_env s.
Proof.
  intros s ts [Hs Hts] x. apply value_lc. apply (proj1 (Hs x)).
Qed.

Lemma env_ok_ty : forall s ts, env_ok s ts -> lc0_ty_env ts.
Proof. intros s ts [Hs Hts]. auto. Qed.

Lemma env_ok_fv : forall s ts, env_ok s ts -> forall x, fv_tm (s x) = [].
Proof. intros s ts [Hs Hts] x. apply (proj2 (Hs x)). Qed.

Lemma env_ok_value : forall s ts, env_ok s ts -> forall x, value (s x).
Proof. intros s ts [Hs Hts] x. apply (proj1 (Hs x)). Qed.

Lemma env_ok_upd : forall s ts x u,
  env_ok s ts -> value u -> fv_tm u = [] -> env_ok (upd s x u) ts.
Proof.
  intros s ts x u [Hs Hts] Hv Hfv. split.
  - intros y. unfold upd. destruct (Nat.eqb x y).
    + auto.
    + apply Hs.
  - auto.
Qed.

Lemma env_ok_upd_ty : forall s ts X U,
  env_ok s ts -> lc_ty_at 0 U -> env_ok s (upd_ty ts X U).
Proof.
  intros s ts X U [Hs Hts] HU. split.
  - auto.
  - intros Y. unfold upd_ty. destruct (Nat.eqb X Y); auto.
Qed.

(* ---------- commutation: close_tm with openings, general index ---------- *)

Lemma close_tm_open_tm_rec : forall s ts k u t,
  lc_tm_at 0 0 u -> lc0_tm_env s -> lc0_ty_env ts ->
  close_tm s ts (open_tm_rec k u t) = open_tm_rec k (close_tm s ts u) (close_tm s ts t).
Proof.
  intros s ts k u t Hu Hs Hts. unfold close_tm.
  rewrite subst_tm_ty_open_tm_rec by auto.
  rewrite subst_tm_open_tm_rec.
  - reflexivity.
  - apply lc_tm_subst_tm_ty; auto.
  - auto.
Qed.

Lemma close_tm_open_tm_ty_rec : forall s ts k U t,
  lc0_tm_env s -> lc0_ty_env ts ->
  close_tm s ts (open_tm_ty_rec k U t) = open_tm_ty_rec k (subst_ty ts U) (close_tm s ts t).
Proof.
  intros s ts k U t Hs Hts. unfold close_tm.
  rewrite subst_tm_ty_open_tm_ty_rec by auto.
  rewrite subst_tm_open_tm_ty_rec by auto.
  reflexivity.
Qed.

(* ---------- commutation: close_qual with openings ---------- *)

Lemma close_qual_open_qual_tm_rec : forall s ts k u p,
  lc_tm_at 0 0 u -> lc0_tm_env s -> lc0_ty_env ts ->
  close_qual s ts (open_pred_tm_rec k u p)
  = open_pred_tm_rec k (close_tm s ts u) (close_qual s ts p).
Proof.
  intros s ts k u p. revert k u.
  induction p; intros k u Hu Hs Hts; unfold close_qual, close_tm; simpl;
    try reflexivity.
  - f_equal; apply close_tm_open_tm_rec; auto.
  - f_equal; apply close_tm_open_tm_rec; auto.
  - f_equal; apply close_tm_open_tm_rec; auto.
  - f_equal; [apply IHp1; auto | apply IHp2; auto].
  - f_equal; [apply IHp1; auto | apply IHp2; auto].
  - f_equal; apply IHp; auto.
Qed.

Lemma close_qual_open_qual_ty_rec : forall s ts k U p,
  lc0_tm_env s -> lc0_ty_env ts ->
  close_qual s ts (open_pred_ty_rec k U p)
  = open_pred_ty_rec k (subst_ty ts U) (close_qual s ts p).
Proof.
  intros s ts k U p. revert k U.
  induction p; intros k U Hs Hts; unfold close_qual, close_tm; simpl;
    try reflexivity.
  - f_equal; apply close_tm_open_tm_ty_rec; auto.
  - f_equal; apply close_tm_open_tm_ty_rec; auto.
  - f_equal; apply close_tm_open_tm_ty_rec; auto.
  - f_equal; [apply IHp1; auto | apply IHp2; auto].
  - f_equal; [apply IHp1; auto | apply IHp2; auto].
  - f_equal; apply IHp; auto.
Qed.

(* ---------- commutation: close_rty with openings ---------- *)

Lemma close_rty_open_rty_tm_rec : forall s ts k u R,
  lc_tm_at 0 0 u -> lc0_tm_env s -> lc0_ty_env ts ->
  close_rty s ts (open_rty_tm_rec k u R)
  = open_rty_tm_rec k (close_tm s ts u) (close_rty s ts R).
Proof.
  intros s ts k u R. revert k.
  induction R as [ T ps | R1 IHR1 R2 IHR2 | R1 IHR1 R2 IHR2 | R1 IHR1 ];
    intros k Hu Hs Hts; unfold close_rty, close_qual, close_tm; simpl.
  - f_equal. apply close_qual_open_qual_tm_rec; auto.
  - f_equal; [apply IHR1; auto | apply IHR2; auto].
  - f_equal; [apply IHR1; auto | apply IHR2; auto].
  - f_equal. apply IHR1; auto.
Qed.

Lemma close_rty_open_rty_ty_rec : forall s ts k U R,
  lc0_tm_env s -> lc0_ty_env ts ->
  close_rty s ts (open_rty_ty_rec k U R)
  = open_rty_ty_rec k (subst_ty ts U) (close_rty s ts R).
Proof.
  intros s ts k U R. revert k U.
  induction R as [ T ps | R1 IHR1 R2 IHR2 | R1 IHR1 R2 IHR2 | R1 IHR1 ];
    intros k U Hs Hts; unfold close_rty, close_qual, close_tm; simpl.
  - f_equal.
    + apply subst_ty_open_ty_rec; auto.
    + apply close_qual_open_qual_ty_rec; auto.
  - f_equal; [apply IHR1; auto | apply IHR2; auto].
  - f_equal; [apply IHR1; auto | apply IHR2; auto].
  - f_equal. apply IHR1; auto.
Qed.

(* ---------- free variables and substitution ---------- *)

Lemma fv_tm_subst_tm_ty : forall s t, fv_tm (subst_tm_ty s t) = fv_tm t.
Proof.
  intros s t. induction t; simpl; auto; try (f_equal; auto).
Qed.

Lemma fv_qual_subst_qual_ty : forall s p, fv_qual (subst_qual_ty s p) = fv_qual p.
Proof.
  intros s p. induction p; simpl; auto; try (f_equal; auto);
    try (repeat rewrite fv_tm_subst_tm_ty); auto.
Qed.

Lemma fv_rty_subst_rty_ty : forall s R, fv_rty (subst_rty_ty s R) = fv_rty R.
Proof.
  intros s R. induction R as [ T ps | R1 IHR1 R2 IHR2 | R1 IHR1 R2 IHR2 | R1 IHR1 ];
    simpl.
  - apply fv_qual_subst_qual_ty.
  - f_equal; [apply IHR1 | apply IHR2].
  - f_equal; [apply IHR1 | apply IHR2].
  - apply IHR1.
Qed.

Lemma fv_tm_subst_tm_nil : forall s t, (forall x, fv_tm (s x) = []) ->
  fv_tm t = [] -> fv_tm (subst_tm s t) = [].
Proof.
  intros s t Hs H. induction t; simpl in *.
  - reflexivity.
  - apply Hs.
  - apply IHt. auto.
  - apply app_eq_nil in H. destruct H as [H1 H2].
    rewrite (IHt1 H1), (IHt2 H2). reflexivity.
  - apply IHt. auto.
  - apply IHt. auto.
  - reflexivity.
  - apply app_eq_nil in H. destruct H as [H1 H2].
    rewrite (IHt1 H1), (IHt2 H2). reflexivity.
  - apply app_eq_nil in H. destruct H as [H1 H2].
    rewrite (IHt1 H1), (IHt2 H2). reflexivity.
Qed.

(* ---------- freshness of simultaneous substitutions ---------- *)

Lemma subst_tm_upd_fresh : forall s x u t,
  ~ In x (fv_tm t) -> subst_tm (upd s x u) t = subst_tm s t.
Proof.
  intros s x u t. induction t; simpl; intros H; auto.
  - unfold upd. destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E. subst a. exfalso. apply H. simpl. auto.
    + reflexivity.
  - f_equal; auto.
  - f_equal.
    + apply IHt1. intro Hin. apply H. simpl. apply in_app_iff. auto.
    + apply IHt2. intro Hin. apply H. simpl. apply in_app_iff. auto.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal.
    + apply IHt1. intro Hin. apply H. simpl. apply in_app_iff. auto.
    + apply IHt2. intro Hin. apply H. simpl. apply in_app_iff. auto.
  - f_equal.
    + apply IHt1. intro Hin. apply H. simpl. apply in_app_iff. auto.
    + apply IHt2. intro Hin. apply H. simpl. apply in_app_iff. auto.
Qed.

Lemma subst_ty_upd_ty_fresh : forall s X U T,
  ~ In X (fv_ty T) -> subst_ty (upd_ty s X U) T = subst_ty s T.
Proof.
  intros s X U T. induction T; simpl; intros H; auto.
  - unfold upd_ty. destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E. subst a. exfalso. apply H. simpl. auto.
    + reflexivity.
  - f_equal.
    + apply IHT1. intro Hin. apply H. simpl. apply in_app_iff. auto.
    + apply IHT2. intro Hin. apply H. simpl. apply in_app_iff. auto.
  - f_equal. apply IHT. intro Hin. apply H. auto.
Qed.

Lemma subst_tm_ty_upd_fresh : forall s X U t,
  ~ In X (ftv_tm t) -> subst_tm_ty (upd_ty s X U) t = subst_tm_ty s t.
Proof.
  intros s X U t. induction t; simpl; intros H; auto.
  - f_equal.
    + apply subst_ty_upd_ty_fresh. intro Hin. apply H. simpl. apply in_app_iff. auto.
    + apply IHt. intro Hin. apply H. simpl. apply in_app_iff. auto.
  - f_equal.
    + apply IHt1. intro Hin. apply H. simpl. apply in_app_iff. auto.
    + apply IHt2. intro Hin. apply H. simpl. apply in_app_iff. auto.
  - f_equal; auto.
  - f_equal.
    + apply IHt. intro Hin. apply H. simpl. apply in_app_iff. auto.
    + apply subst_ty_upd_ty_fresh. intro Hin. apply H. simpl. apply in_app_iff. auto.
  - f_equal.
    + apply IHt1. intro Hin. apply H. simpl. apply in_app_iff. auto.
    + apply IHt2. intro Hin. apply H. simpl. apply in_app_iff. auto.
  - f_equal.
    + apply IHt1. intro Hin. apply H. simpl. apply in_app_iff. auto.
    + apply IHt2. intro Hin. apply H. simpl. apply in_app_iff. auto.
Qed.

Lemma subst_qual_tm_upd_fresh : forall s x u p,
  ~ In x (fv_qual p) -> subst_qual_tm (upd s x u) p = subst_qual_tm s p.
Proof.
  intros s x u p. induction p; simpl; intros H; auto.
  - f_equal; apply subst_tm_upd_fresh;
      intro Hin; apply H; simpl; apply in_app_iff; auto.
  - f_equal; apply subst_tm_upd_fresh;
      intro Hin; apply H; simpl; apply in_app_iff; auto.
  - f_equal; apply subst_tm_upd_fresh;
      intro Hin; apply H; simpl; apply in_app_iff; auto.
  - f_equal.
    + apply IHp1. intro Hin. apply H. simpl. apply in_app_iff; auto.
    + apply IHp2. intro Hin. apply H. simpl. apply in_app_iff; auto.
  - f_equal.
    + apply IHp1. intro Hin. apply H. simpl. apply in_app_iff; auto.
    + apply IHp2. intro Hin. apply H. simpl. apply in_app_iff; auto.
  - f_equal. apply IHp. auto.
Qed.

Lemma subst_qual_ty_upd_fresh : forall s X U p,
  ~ In X (ftv_qual p) -> subst_qual_ty (upd_ty s X U) p = subst_qual_ty s p.
Proof.
  intros s X U p. induction p; simpl; intros H; auto.
  - f_equal; apply subst_tm_ty_upd_fresh;
      intro Hin; apply H; simpl; apply in_app_iff; auto.
  - f_equal; apply subst_tm_ty_upd_fresh;
      intro Hin; apply H; simpl; apply in_app_iff; auto.
  - f_equal; apply subst_tm_ty_upd_fresh;
      intro Hin; apply H; simpl; apply in_app_iff; auto.
  - f_equal.
    + apply IHp1. intro Hin. apply H. simpl. apply in_app_iff; auto.
    + apply IHp2. intro Hin. apply H. simpl. apply in_app_iff; auto.
  - f_equal.
    + apply IHp1. intro Hin. apply H. simpl. apply in_app_iff; auto.
    + apply IHp2. intro Hin. apply H. simpl. apply in_app_iff; auto.
  - f_equal. apply IHp. auto.
Qed.

Lemma subst_rty_tm_upd_fresh : forall s x u R,
  ~ In x (fv_rty R) -> subst_rty_tm (upd s x u) R = subst_rty_tm s R.
Proof.
  intros s x u R.
  induction R as [ T ps | R1 IHR1 R2 IHR2 | R1 IHR1 R2 IHR2 | R1 IHR1 ];
    simpl; intros H.
  - f_equal. apply subst_qual_tm_upd_fresh. auto.
  - f_equal.
    + apply IHR1. intro Hin. apply H. simpl. apply in_app_iff; auto.
    + apply IHR2. intro Hin. apply H. simpl. apply in_app_iff; auto.
  - f_equal.
    + apply IHR1. intro Hin. apply H. simpl. apply in_app_iff; auto.
    + apply IHR2. intro Hin. apply H. simpl. apply in_app_iff; auto.
  - f_equal. apply IHR1. auto.
Qed.

Lemma subst_rty_ty_upd_fresh : forall s X U R,
  ~ In X (ftv_rty R) -> subst_rty_ty (upd_ty s X U) R = subst_rty_ty s R.
Proof.
  intros s X U R.
  induction R as [ T ps | R1 IHR1 R2 IHR2 | R1 IHR1 R2 IHR2 | R1 IHR1 ];
    simpl; intros H.
  - f_equal.
    + apply subst_ty_upd_ty_fresh.
      intro Hin. apply H. simpl. apply in_app_iff; auto.
    + apply subst_qual_ty_upd_fresh.
      intro Hin. apply H. simpl. apply in_app_iff; auto.
  - f_equal.
    + apply IHR1. intro Hin. apply H. simpl. apply in_app_iff; auto.
    + apply IHR2. intro Hin. apply H. simpl. apply in_app_iff; auto.
  - f_equal.
    + apply IHR1. intro Hin. apply H. simpl. apply in_app_iff; auto.
    + apply IHR2. intro Hin. apply H. simpl. apply in_app_iff; auto.
  - f_equal. apply IHR1. auto.
Qed.

(* ---------- instantiation at a fresh variable ---------- *)

Lemma close_tm_upd_open : forall s ts x u body,
  lc_tm_at 0 0 u -> lc0_tm_env s -> lc0_ty_env ts -> ~ In x (fv_tm body) ->
  close_tm (upd s x u) ts (open_tm body (tm_fvar x)) = open_tm (close_tm s ts body) u.
Proof.
  intros s ts x u body Hu Hs Hts Hx.
  assert (H1 : close_tm (upd s x u) ts (tm_fvar x) = u).
  { unfold close_tm. simpl. unfold upd. rewrite Nat.eqb_refl. reflexivity. }
  assert (H2 : close_tm (upd s x u) ts body = close_tm s ts body).
  { unfold close_tm. rewrite subst_tm_upd_fresh.
    - reflexivity.
    - rewrite fv_tm_subst_tm_ty. auto. }
  unfold open_tm. rewrite (close_tm_open_tm_rec (upd s x u) ts 0 (tm_fvar x) body).
  - rewrite H1, H2. reflexivity.
  - apply lc_tm_fvar.
  - intros y. unfold upd. destruct (Nat.eqb x y); auto.
  - exact Hts.
Qed.

Lemma close_rty_upd_open_rty_tm : forall s ts x u R,
  lc_tm_at 0 0 u -> lc0_tm_env s -> lc0_ty_env ts -> ~ In x (fv_rty R) ->
  close_rty (upd s x u) ts (open_rty_tm R (tm_fvar x)) = open_rty_tm (close_rty s ts R) u.
Proof.
  intros s ts x u R Hu Hs Hts Hx.
  assert (H1 : close_tm (upd s x u) ts (tm_fvar x) = u).
  { unfold close_tm. simpl. unfold upd. rewrite Nat.eqb_refl. reflexivity. }
  assert (H2 : close_rty (upd s x u) ts R = close_rty s ts R).
  { unfold close_rty. rewrite subst_rty_tm_upd_fresh.
    - reflexivity.
    - rewrite fv_rty_subst_rty_ty. auto. }
  unfold open_rty_tm.
  rewrite (close_rty_open_rty_tm_rec (upd s x u) ts 0 (tm_fvar x) R).
  - rewrite H1, H2. reflexivity.
  - apply lc_tm_fvar.
  - intros y. unfold upd. destruct (Nat.eqb x y); auto.
  - exact Hts.
Qed.

Lemma close_tm_upd_ty_open : forall s ts X U body,
  lc0_tm_env s -> lc0_ty_env ts -> lc_ty_at 0 U -> ~ In X (ftv_tm body) ->
  close_tm s (upd_ty ts X U) (open_tm_ty body (Ty_FVar X)) = open_tm_ty (close_tm s ts body) U.
Proof.
  intros s ts X U body Hs Hts HU HX.
  assert (H1 : subst_ty (upd_ty ts X U) (Ty_FVar X) = U).
  { unfold upd_ty. simpl. rewrite Nat.eqb_refl. reflexivity. }
  assert (H2 : close_tm s (upd_ty ts X U) body = close_tm s ts body).
  { unfold close_tm. rewrite subst_tm_ty_upd_fresh.
    - reflexivity.
    - auto. }
  unfold open_tm_ty.
  rewrite (close_tm_open_tm_ty_rec s (upd_ty ts X U) 0 (Ty_FVar X) body).
  - rewrite H2, H1. reflexivity.
  - exact Hs.
  - intros Y. unfold upd_ty. destruct (Nat.eqb X Y); auto.
Qed.

Lemma close_rty_upd_ty_open : forall s ts X U R,
  lc0_tm_env s -> lc0_ty_env ts -> lc_ty_at 0 U -> ~ In X (ftv_rty R) ->
  close_rty s (upd_ty ts X U) (open_rty_ty R (Ty_FVar X)) = open_rty_ty (close_rty s ts R) U.
Proof.
  intros s ts X U R Hs Hts HU HX.
  assert (H1 : subst_ty (upd_ty ts X U) (Ty_FVar X) = U).
  { unfold upd_ty. simpl. rewrite Nat.eqb_refl. reflexivity. }
  assert (H2 : close_rty s (upd_ty ts X U) R = close_rty s ts R).
  { unfold close_rty. rewrite subst_rty_ty_upd_fresh.
    - reflexivity.
    - auto. }
  unfold open_rty_ty.
  rewrite (close_rty_open_rty_ty_rec s (upd_ty ts X U) 0 (Ty_FVar X) R).
  - rewrite H2, H1. reflexivity.
  - exact Hs.
  - intros Y. unfold upd_ty. destruct (Nat.eqb X Y); auto.
Qed.

(* ---------- preservation of syntactic properties under closing ---------- *)

Lemma fv_close_tm_nil : forall s ts t, env_ok s ts -> fv_tm t = [] ->
  fv_tm (close_tm s ts t) = [].
Proof.
  intros s ts t Henv Hfv. unfold close_tm.
  apply fv_tm_subst_tm_nil.
  - intros x. exact (env_ok_fv s ts Henv x).
  - rewrite fv_tm_subst_tm_ty. auto.
Qed.

Lemma lc_close_tm : forall s ts t K k, env_ok s ts ->
  lc_tm_at K k t -> lc_tm_at K k (close_tm s ts t).
Proof.
  intros s ts t K k Henv Hlc. unfold close_tm.
  apply lc_tm_subst_tm.
  - apply (env_ok_lc s ts Henv).
  - apply lc_tm_subst_tm_ty.
    + apply (env_ok_ty s ts Henv).
    + auto.
Qed.

Lemma value_close_tm : forall s ts v, env_ok s ts -> value v ->
  value (close_tm s ts v).
Proof.
  intros s ts v Henv Hv. induction Hv; simpl.
  - apply v_abs. change (lc_tm_at 0 0 (close_tm s ts (tm_abs T t))).
    apply lc_close_tm; auto.
  - apply v_tabs. change (lc_tm_at 0 0 (close_tm s ts (tm_tabs t))).
    apply lc_close_tm; auto.
  - change (value (tm_int n)). apply v_int.
Qed.

Lemma canon_close : forall s ts T v, env_ok s ts -> canon T v ->
  canon (subst_ty ts T) (close_tm s ts v).
Proof.
  intros s ts T v Henv Hc. destruct T; simpl in *.
  - destruct Hc.
  - destruct Hc.
  - destruct Hc as [T' [body Hbody]]. subst v. simpl. eexists; eexists; reflexivity.
  - destruct Hc as [body Hbody]. subst v. simpl. eexists; reflexivity.
  - destruct Hc as [n Hn]. subst v. simpl. exists n. reflexivity.
Qed.

Lemma erase_subst_rty_tm : forall s R, erase (subst_rty_tm s R) = erase R.
Proof. intros s R. induction R; simpl; congruence. Qed.

Lemma close_rty_erase : forall s ts R,
  erase (close_rty s ts R) = subst_ty ts (erase R).
Proof.
  intros s ts R. unfold close_rty.
  rewrite erase_subst_rty_tm. rewrite erase_subst_rty_ty. reflexivity.
Qed.

(* ================================================================ *)
(* The logical relation.                                            *)
(* ================================================================ *)

From Equations Require Import Equations.

Fixpoint size_rty (R : rty) : nat :=
  match R with
  | R_Refine _ _ => 1
  | R_Func R1 R2 => 1 + size_rty R1 + size_rty R2
  | R_Exists R1 R2 => 1 + size_rty R1 + size_rty R2
  | R_Poly R1 => 1 + size_rty R1
  end.

Lemma size_open_rty_tm_rec : forall k u R,
  size_rty (open_rty_tm_rec k u R) = size_rty R.
Proof. intros k u R. revert k u. induction R; simpl; congruence. Qed.

Lemma size_open_rty_tm : forall R u, size_rty (open_rty_tm R u) = size_rty R.
Proof. intros; apply size_open_rty_tm_rec. Qed.

Lemma size_open_rty_ty_rec : forall k U R,
  size_rty (open_rty_ty_rec k U R) = size_rty R.
Proof. intros k U R. revert k U. induction R; simpl; congruence. Qed.

Lemma size_open_rty_ty : forall R U, size_rty (open_rty_ty R U) = size_rty R.
Proof. intros; apply size_open_rty_ty_rec. Qed.

Obligation Tactic :=
  intros; try rewrite size_open_rty_tm; try rewrite size_open_rty_ty;
  cbn [size_rty]; lia.

Equations V (R : rty) (v : tm) : Prop by wf (size_rty R) :=
  V (R_Refine T ps) v =>
    value v /\ fv_tm v = [] /\ canon T v /\
    qualifier_holds (open_qualifier_tm ps v) ;
  V (R_Func R1 R2) v =>
    value v /\ fv_tm v = [] /\
    (forall u, V R1 u ->
       forall t', multi (tm_app v u) t' ->
         fv_tm t' = [] /\ lc_tm_at 0 0 t' /\
         ((value t' /\ V (open_rty_tm R2 u) t') \/ (exists t'', t' --> t''))) ;
  V (R_Exists R1 R2) v =>
    value v /\ fv_tm v = [] /\
    (exists u, V R1 u /\ V (open_rty_tm R2 u) v) ;
  V (R_Poly R1) v =>
    value v /\ fv_tm v = [] /\
    (forall U, lc_ty_at 0 U ->
       forall t', multi (tm_tapp v U) t' ->
         fv_tm t' = [] /\ lc_tm_at 0 0 t' /\
         ((value t' /\ V (open_rty_ty R1 U) t') \/ (exists t'', t' --> t''))).

Definition NotStuck (R : rty) (t : tm) : Prop :=
  fv_tm t = [] /\ lc_tm_at 0 0 t /\
  ((value t /\ V R t) \/ (exists t', t --> t')).

Definition Safe (R : rty) (t : tm) : Prop :=
  forall t', multi t t' -> NotStuck R t'.

(* ---------- elimination and introduction lemmas for V ---------- *)

Lemma V_value : forall R v, V R v -> value v.
Proof.
  intros R v H. destruct R.
  - rewrite V_equation_1 in H. tauto.
  - rewrite V_equation_2 in H. tauto.
  - rewrite V_equation_3 in H. tauto.
  - rewrite V_equation_4 in H. tauto.
Qed.

Lemma V_fv : forall R v, V R v -> fv_tm v = [].
Proof.
  intros R v H. destruct R.
  - rewrite V_equation_1 in H. tauto.
  - rewrite V_equation_2 in H. tauto.
  - rewrite V_equation_3 in H. tauto.
  - rewrite V_equation_4 in H. tauto.
Qed.

Lemma V_refine_elim : forall T ps v, V (R_Refine T ps) v ->
  value v /\ fv_tm v = [] /\ canon T v /\
  qualifier_holds (open_qualifier_tm ps v).
Proof. intros. rewrite V_equation_1 in H. exact H. Qed.

Lemma V_refine_intro : forall T ps v,
  value v -> fv_tm v = [] -> canon T v ->
  qualifier_holds (open_qualifier_tm ps v) -> V (R_Refine T ps) v.
Proof. intros. rewrite V_equation_1. auto. Qed.

Lemma V_func_elim : forall R1 R2 v, V (R_Func R1 R2) v ->
  value v /\ fv_tm v = [] /\
  (forall u, V R1 u -> Safe (open_rty_tm R2 u) (tm_app v u)).
Proof.
  intros R1 R2 v H. rewrite V_equation_2 in H.
  destruct H as [Hv [Hfv H]]. split; [exact Hv | split; [exact Hfv | ]].
  intros w Hw. unfold Safe. apply H; auto.
Qed.

Lemma V_func_intro : forall R1 R2 v,
  value v -> fv_tm v = [] ->
  (forall u, V R1 u -> Safe (open_rty_tm R2 u) (tm_app v u)) ->
  V (R_Func R1 R2) v.
Proof.
  intros R1 R2 v Hv Hfv H. rewrite V_equation_2.
  split; [exact Hv | split; [exact Hfv | ]].
  intros w Hw. unfold Safe in H. apply H; auto.
Qed.

Lemma V_exists_elim : forall R1 R2 v, V (R_Exists R1 R2) v ->
  value v /\ fv_tm v = [] /\
  (exists u, V R1 u /\ V (open_rty_tm R2 u) v).
Proof. intros. rewrite V_equation_3 in H. exact H. Qed.

Lemma V_exists_intro : forall R1 R2 v u,
  value v -> fv_tm v = [] -> V R1 u -> V (open_rty_tm R2 u) v ->
  V (R_Exists R1 R2) v.
Proof. intros. rewrite V_equation_3. repeat split; auto. exists u; auto. Qed.

Lemma V_poly_elim : forall R v, V (R_Poly R) v ->
  value v /\ fv_tm v = [] /\
  (forall U, lc_ty_at 0 U -> Safe (open_rty_ty R U) (tm_tapp v U)).
Proof.
  intros R v H. rewrite V_equation_4 in H.
  destruct H as [Hv [Hfv H]]. split; [exact Hv | split; [exact Hfv | ]].
  intros U HU. unfold Safe. apply H; auto.
Qed.

Lemma V_poly_intro : forall R v,
  value v -> fv_tm v = [] ->
  (forall U, lc_ty_at 0 U -> Safe (open_rty_ty R U) (tm_tapp v U)) ->
  V (R_Poly R) v.
Proof.
  intros R v Hv Hfv H. rewrite V_equation_4.
  split; [exact Hv | split; [exact Hfv | ]].
  intros U HU. unfold Safe in H. apply H; auto.
Qed.

(* ---------- values and multi-step reduction ---------- *)

Lemma value_no_step : forall v t, value v -> v --> t -> False.
Proof.
  intros v t Hv Hstep. revert Hv.
  induction Hstep; intros Hv; inversion Hv.
Qed.

Lemma abs_no_step : forall T body u, tm_abs T body --> u -> False.
Proof. intros T body u H. inversion H. Qed.

Lemma tabs_no_step : forall body u, tm_tabs body --> u -> False.
Proof. intros body u H. inversion H. Qed.

Lemma int_no_step : forall n u, tm_int n --> u -> False.
Proof. intros n u H. inversion H. Qed.

Lemma multi_value_inv : forall v t, value v -> multi v t -> t = v.
Proof.
  intros v t Hv Hm. induction Hm as [ | s t1 t2 Hstep Hmulti IH].
  - reflexivity.
  - exfalso. apply (value_no_step s t1). auto. exact Hstep.
Qed.

Lemma V_safe : forall R v, V R v -> Safe R v.
Proof.
  intros R v H. unfold Safe. intros t' Hm.
  assert (Hval : value v) by (apply (V_value R v); auto).
  assert (Heq : t' = v) by (apply (multi_value_inv v t'); auto).
  subst t'. split.
  - apply (V_fv R v); auto.
  - split.
    + apply value_lc; auto.
    + left. split; auto.
Qed.

Lemma Safe_mono : forall R S,
  (forall v, V R v -> V S v) -> forall t, Safe R t -> Safe S t.
Proof.
  intros R S Hsub t H. unfold Safe in *. intros t' Hm.
  destruct (H t' Hm) as [Hfv [Hlc Hcase]].
  split; [auto | split; [auto | ]].
  destruct Hcase as [[Hv HV] | Hstep].
  - left. split; auto.
  - right; auto.
Qed.

(* ---------- basic consequences of Safe ---------- *)

Lemma Safe_refl : forall R t, Safe R t ->
  fv_tm t = [] /\ lc_tm_at 0 0 t /\
  ((value t /\ V R t) \/ (exists t', t --> t')).
Proof. intros R t H. unfold Safe in H. apply H. apply multi_refl. Qed.

Lemma Safe_fv : forall R t, Safe R t -> fv_tm t = [].
Proof. intros R t H. apply (proj1 (Safe_refl _ _ H)). Qed.

Lemma Safe_lc : forall R t, Safe R t -> lc_tm_at 0 0 t.
Proof. intros R t H. apply (proj1 (proj2 (Safe_refl _ _ H))). Qed.

Lemma Safe_of_step : forall R t t', Safe R t -> t --> t' -> Safe R t'.
Proof.
  intros R t t' H Hs. unfold Safe in *. intros t'' Hm.
  apply H. eapply multi_step; eauto.
Qed.

Lemma Safe_exists_intro : forall R1 R2 u t,
  V R1 u -> Safe (open_rty_tm R2 u) t -> Safe (R_Exists R1 R2) t.
Proof.
  intros R1 R2 u t Hv H. unfold Safe in *.
  intros t' Hm. destruct (H t' Hm) as [Hfv [Hlc Hcase]].
  split; [auto | split; [auto | ]].
  destruct Hcase as [[Hval HV] | Hstep].
  - left. split; auto. apply V_exists_intro with u; auto.
  - right; auto.
Qed.

(* ---------- first-step case analysis ---------- *)

Lemma app_step_cases : forall u1 u2 w, tm_app u1 u2 --> w ->
  (exists u1', u1 --> u1' /\ w = tm_app u1' u2) \/
  (exists u2', value u1 /\ u2 --> u2' /\ w = tm_app u1 u2') \/
  (exists T body v, u1 = tm_abs T body /\ u2 = v /\ value v /\ w = open_tm body v).
Proof.
  intros u1 u2 w H.
  remember (tm_app u1 u2) as s eqn:Es.
  revert u1 u2 Es.
  induction H; intros ua ub Es; try (inversion Es; fail).
  - inversion Es; subst. right; right.
    eexists; eexists; eexists. repeat split; eauto.
  - inversion Es; subst. left. eexists; split; eauto.
  - inversion Es; subst. right; left. eexists. repeat split; eauto.
Qed.

Lemma tapp_step_cases : forall u U w, tm_tapp u U --> w ->
  (exists u', u --> u' /\ w = tm_tapp u' U) \/
  (exists body, u = tm_tabs body /\ w = open_tm_ty body U).
Proof.
  intros u U w H.
  remember (tm_tapp u U) as s eqn:Es.
  revert u U Es.
  induction H; intros ua Ua Es; try (inversion Es; fail).
  - inversion Es; subst. right. eexists. split; eauto.
  - inversion Es; subst. left. eexists. split; eauto.
Qed.

Lemma div_step_cases : forall u1 u2 w, tm_div u1 u2 --> w ->
  (exists u1', u1 --> u1' /\ w = tm_div u1' u2) \/
  (exists u2', value u1 /\ u2 --> u2' /\ w = tm_div u1 u2') \/
  (exists n m, u1 = tm_int n /\ u2 = tm_int m /\ m <> 0%Z /\ w = tm_int (Z.div n m)).
Proof.
  intros u1 u2 w H.
  remember (tm_div u1 u2) as s eqn:Es.
  revert u1 u2 Es.
  induction H; intros ua ub Es; try (inversion Es; fail).
  - inversion Es; subst. left. eexists; split; eauto.
  - inversion Es; subst. right; left. eexists. repeat split; eauto.
  - inversion Es; subst. right; right. eexists; eexists. repeat split; eauto.
Qed.

Lemma arith_step_cases : forall op u1 u2 w, tm_arith op u1 u2 --> w ->
  (exists u1', u1 --> u1' /\ w = tm_arith op u1' u2) \/
  (exists u2', value u1 /\ u2 --> u2' /\ w = tm_arith op u1 u2') \/
  (exists n m, u1 = tm_int n /\ u2 = tm_int m /\ w = tm_int (eval_integer_operator op n m)).
Proof.
  intros op u1 u2 w H.
  remember (tm_arith op u1 u2) as s eqn:Es.
  revert op u1 u2 Es.
  induction H; intros opa ua ub Es; try (inversion Es; fail).
  - inversion Es; subst. left. eexists; split; eauto.
  - inversion Es; subst. right; left. eexists. repeat split; eauto.
  - inversion Es; subst. right; right. eexists; eexists. repeat split; eauto.
Qed.

(* ---------- multi-step decomposition for stuck-free redexes ---------- *)

Lemma multi_app_abs : forall T body u t',
  value (tm_abs T body) -> value u ->
  multi (tm_app (tm_abs T body) u) t' ->
  t' = tm_app (tm_abs T body) u \/ multi (open_tm body u) t'.
Proof.
  intros T body u t' Hv Hu Hm.
  remember (tm_app (tm_abs T body) u) as s eqn:Es.
  revert T body u Hv Hu Es.
  induction Hm as [ | s w t'' Hstep Hmulti IH].
  - intros. left. auto.
  - intros T0 body0 u0 Hv0 Hu0 Es. right. subst s.
    destruct (app_step_cases (tm_abs T0 body0) u0 w Hstep)
      as [[u1' [Hs1 Heq]] | [[u2' [Hv1 [Hs2 Heq]]] | [T' [body' [v [Heq1 [Heq2 [Hvv Heq3]]]]]]]].
    + exfalso. exact (value_no_step _ _ Hv0 Hs1).
    + exfalso. exact (value_no_step _ _ Hu0 Hs2).
    + inversion Heq1; subst; auto.
Qed.

Lemma multi_tapp_tabs : forall body U t',
  value (tm_tabs body) -> lc_ty_at 0 U ->
  multi (tm_tapp (tm_tabs body) U) t' ->
  t' = tm_tapp (tm_tabs body) U \/ multi (open_tm_ty body U) t'.
Proof.
  intros body U t' Hv HU Hm.
  remember (tm_tapp (tm_tabs body) U) as s eqn:Es.
  revert body U Hv HU Es.
  induction Hm as [ | s w t'' Hstep Hmulti IH].
  - intros. left. auto.
  - intros body0 U0 Hv0 HU0 Es. right. subst s.
    destruct (tapp_step_cases (tm_tabs body0) U0 w Hstep)
      as [[u' [Hs Heq]] | [body' [Heq1 Heq2]]].
    + exfalso. exact (value_no_step _ _ Hv0 Hs).
    + inversion Heq1; subst; auto.
Qed.

Lemma multi_div_int : forall n m t', m <> 0%Z ->
  multi (tm_div (tm_int n) (tm_int m)) t' ->
  t' = tm_div (tm_int n) (tm_int m) \/ multi (tm_int (Z.div n m)) t'.
Proof.
  intros n m t' Hm0 Hm.
  remember (tm_div (tm_int n) (tm_int m)) as s eqn:Es.
  revert n m Hm0 Es.
  induction Hm as [ | s w t'' Hstep Hmulti IH].
  - intros. left. auto.
  - intros n0 m0 Hm00 Es. right. subst s.
    destruct (div_step_cases (tm_int n0) (tm_int m0) w Hstep)
      as [[u1' [Hs Heq]] | [[u2' [Hv1 [Hs Heq]]] | [n' [m' [Heq1 [Heq2 [Hne Heq3]]]]]]].
    + exfalso. exact (value_no_step _ _ (v_int n0) Hs).
    + exfalso. exact (value_no_step _ _ (v_int m0) Hs).
    + inversion Heq1; subst; inversion Heq2; subst; auto.
Qed.

Lemma multi_arith_int : forall op n m t',
  multi (tm_arith op (tm_int n) (tm_int m)) t' ->
  t' = tm_arith op (tm_int n) (tm_int m) \/
  multi (tm_int (eval_integer_operator op n m)) t'.
Proof.
  intros op n m t' Hm.
  remember (tm_arith op (tm_int n) (tm_int m)) as s eqn:Es.
  revert op n m Es.
  induction Hm as [ | s w t'' Hstep Hmulti IH].
  - intros. left. auto.
  - intros op0 n0 m0 Es. right. subst s.
    destruct (arith_step_cases op0 (tm_int n0) (tm_int m0) w Hstep)
      as [[u1' [Hs Heq]] | [[u2' [Hv1 [Hs Heq]]] | [n' [m' [Heq1 [Heq2 Heq3]]]]]].
    + exfalso. exact (value_no_step _ _ (v_int n0) Hs).
    + exfalso. exact (value_no_step _ _ (v_int m0) Hs).
    + inversion Heq1; subst; inversion Heq2; subst; auto.
Qed.

(* ---------- arithmetic refinement facts ---------- *)

Definition RIntTrue : rty := R_Refine Ty_Int Pred_True.
Definition RIntNeZero : rty := R_Refine Ty_Int (Pred_Ne (tm_bvar 0) (tm_int 0)).

Lemma qual_ne_zero : forall m,
  qualifier_holds (Pred_Ne (tm_int m) (tm_int 0)) -> m <> 0%Z.
Proof.
  intros m H Heq. subst m. apply H.
  exists (tm_int 0%Z). split; [apply PMS_Refl | split; [apply PMS_Refl | apply v_int]].
Qed.

Lemma qual_arith_eq : forall op n m,
  qualifier_holds (Pred_Eq (tm_int (eval_integer_operator op n m))
                           (tm_arith op (tm_int n) (tm_int m))).
Proof.
  intros op n m. unfold qualifier_holds, predicate_holds. simpl.
  exists (tm_int (eval_integer_operator op n m)). split.
  - apply PMS_Refl.
  - split.
    + apply PMS_Step with (t2 := tm_int (eval_integer_operator op n m)).
      apply ST_ArithInt. apply PMS_Refl.
    + apply v_int.
Qed.

Lemma qual_int_self : forall n, qualifier_holds (Pred_Eq (tm_int n) (tm_int n)).
Proof.
  intros n. unfold qualifier_holds, predicate_holds. simpl.
  exists (tm_int n). split; [apply PMS_Refl | split; [apply PMS_Refl | apply v_int]].
Qed.

(* ---------- composition lemmas for Safe ---------- *)

Lemma Safe_app : forall R1 R2 t1 t2,
  Safe (R_Func R1 R2) t1 -> Safe R1 t2 -> Safe (R_Exists R1 R2) (tm_app t1 t2).
Proof.
  intros R1 R2 t1 t2 H1 H2 t' Hm.
  remember (tm_app t1 t2) as s eqn:Es.
  revert t1 t2 H1 H2 Es.
  induction Hm as [ | s w t'' Hstep Hmulti IH].
  - (* refl *) intros u1 u2 H1' H2' Es. rewrite Es.
    destruct (Safe_refl _ _ H1') as [Hfv1 [Hlc1 Hc1]].
    destruct (Safe_refl _ _ H2') as [Hfv2 [Hlc2 Hc2]].
    split; [ simpl; rewrite Hfv1, Hfv2; reflexivity | ].
    split; [ simpl; apply lc_tm_app; auto | ].
    destruct Hc1 as [[Hv1 HV1] | [u1' Hs1]].
    + destruct Hc2 as [[Hv2 HV2] | [u2' Hs2]].
      * pose proof (V_func_elim _ _ _ HV1) as [_ [_ Hcont]].
        destruct (Safe_refl _ _ (Hcont u2 HV2)) as [_ [_ Hc3]].
        destruct Hc3 as [[Hval _] | Hstep3].
        -- exfalso. inversion Hval.
        -- right. exact Hstep3.
      * right. exists (tm_app u1 u2'). apply ST_App2; auto.
    + right. exists (tm_app u1' u2). apply ST_App1; auto.
  - (* step *) intros u1 u2 H1' H2' Es. subst s.
    destruct (app_step_cases u1 u2 w Hstep)
      as [[u1' [Hs1 Heq]] | [[u2' [Hv1 [Hs2 Heq]]] | [T [body [v [Heq1 [Heq2 [Hvv Heq3]]]]]]]].
    + subst w. apply IH with (t1 := u1') (t2 := u2).
      * apply Safe_of_step with (t := u1); auto.
      * auto.
      * reflexivity.
    + subst w. apply IH with (t1 := u1) (t2 := u2').
      * auto.
      * apply Safe_of_step with (t := u2); auto.
      * reflexivity.
    + subst u1. subst u2. subst w.
      destruct (Safe_refl _ _ H1') as [_ [_ Hc1]].
      destruct Hc1 as [[Hval1 HV1] | [w1 Hs1]].
      * destruct (Safe_refl _ _ H2') as [_ [_ Hc2]].
        destruct Hc2 as [[Hval2 HV2] | [w2 Hs2]].
        -- pose proof (V_func_elim _ _ _ HV1) as [_ [_ Hcont]].
           pose proof (Safe_exists_intro R1 R2 v (tm_app (tm_abs T body) v) HV2 (Hcont v HV2)) as Hsafe.
           unfold Safe in Hsafe. apply Hsafe. eapply multi_step; eauto.
        -- exfalso. exact (value_no_step _ _ Hvv Hs2).
      * exfalso. eapply abs_no_step; eauto.
Qed.

Lemma Safe_tapp : forall R t U,
  Safe (R_Poly R) t -> lc_ty_at 0 U -> Safe (open_rty_ty R U) (tm_tapp t U).
Proof.
  intros R t U H1 HU t' Hm.
  remember (tm_tapp t U) as s eqn:Es.
  revert t U H1 HU Es.
  induction Hm as [ | s w t'' Hstep Hmulti IH].
  - intros u U0 H1' HU0 Es. rewrite Es.
    destruct (Safe_refl _ _ H1') as [Hfv1 [Hlc1 Hc1]].
    split; [ simpl; auto | ].
    split; [ simpl; apply lc_tm_tapp; auto | ].
    destruct Hc1 as [[Hv1 HV1] | [u' Hs1]].
    + pose proof (V_poly_elim _ _ HV1) as [_ [_ Hcont]].
      destruct (Safe_refl _ _ (Hcont U0 HU0)) as [_ [_ Hc3]].
      destruct Hc3 as [[Hval _] | Hstep3].
      * exfalso. inversion Hval.
      * right. exact Hstep3.
    + right. exists (tm_tapp u' U0). apply ST_TApp; auto.
  - intros u U0 H1' HU0 Es. subst s.
    destruct (tapp_step_cases u U0 w Hstep) as [[u' [Hs Heq]] | [body [Heq1 Heq2]]].
    + subst w. apply IH with (t := u') (U := U0).
      * apply Safe_of_step with (t := u); auto.
      * auto.
      * reflexivity.
    + subst u. subst w.
      destruct (Safe_refl _ _ H1') as [_ [_ Hc1]].
      destruct Hc1 as [[Hval1 HV1] | [w1 Hs1]].
      * pose proof (V_poly_elim _ _ HV1) as [_ [_ Hcont]].
        pose proof (Hcont U0 HU0) as Hsafe.
        unfold Safe in Hsafe. apply Hsafe. eapply multi_step; eauto.
      * exfalso. eapply tabs_no_step; eauto.
Qed.

Lemma Safe_div : forall t1 t2,
  Safe RIntTrue t1 -> Safe RIntNeZero t2 -> Safe RIntTrue (tm_div t1 t2).
Proof.
  intros t1 t2 H1 H2 t' Hm.
  remember (tm_div t1 t2) as s eqn:Es.
  revert t1 t2 H1 H2 Es.
  induction Hm as [ | s w t'' Hstep Hmulti IH].
  - intros u1 u2 H1' H2' Es. rewrite Es.
    destruct (Safe_refl _ _ H1') as [Hfv1 [Hlc1 Hc1]].
    destruct (Safe_refl _ _ H2') as [Hfv2 [Hlc2 Hc2]].
    split; [ simpl; rewrite Hfv1, Hfv2; reflexivity | ].
    split; [ simpl; apply lc_tm_div; auto | ].
    destruct Hc1 as [[Hv1 HV1] | [u1' Hs1]].
    + destruct Hc2 as [[Hv2 HV2] | [u2' Hs2]].
      * destruct (V_refine_elim _ _ _ HV1) as [_ [_ [[n Hn] _]]].
        destruct (V_refine_elim _ _ _ HV2) as [_ [_ [[m Hm'] Hq]]].
        subst u1. subst u2.
        right. exists (tm_int (Z.div n m)). apply ST_DivInt.
        apply qual_ne_zero. auto.
      * right. exists (tm_div u1 u2'). apply ST_Div2; auto.
    + right. exists (tm_div u1' u2). apply ST_Div1; auto.
  - intros u1 u2 H1' H2' Es. subst s.
    destruct (div_step_cases u1 u2 w Hstep)
      as [[u1' [Hs1 Heq]] | [[u2' [Hv1 [Hs2 Heq]]] | [n [m [Heq1 [Heq2 [Hne Heq3]]]]]]].
    + subst w. apply IH with (t1 := u1') (t2 := u2).
      * apply Safe_of_step with (t := u1); auto.
      * auto.
      * reflexivity.
    + subst w. apply IH with (t1 := u1) (t2 := u2').
      * auto.
      * apply Safe_of_step with (t := u2); auto.
      * reflexivity.
    + subst u1. subst u2. subst w.
      assert (Ht'' : t'' = tm_int (Z.div n m)).
      { apply (multi_value_inv (tm_int (Z.div n m)) t''); auto. apply v_int. }
      subst t''.
      split; [ simpl; auto | ].
      split; [ simpl; apply lc_tm_int | ].
      left. split; [apply v_int | ].
      apply V_refine_intro.
      * apply v_int.
      * reflexivity.
      * exists (Z.div n m). reflexivity.
      * unfold qualifier_holds, predicate_holds. simpl. exact I.
Qed.

Lemma multi_step_r : forall t u v, multi t u -> u --> v -> multi t v.
Proof.
  intros t u v H Huv. induction H as [ | a b c Hs Hm IH].
  - apply multi_step with (t2 := v); auto. apply multi_refl.
  - eapply multi_step; eauto.
Qed.

Lemma multi_pms : forall t t', multi t t' -> predicate_multistep t t'.
Proof.
  intros t t' H. induction H as [ | a b c Hs Hm IH].
  - apply PMS_Refl.
  - apply PMS_Step with (t2 := b); auto.
Qed.

Lemma Safe_arith : forall op t1 t2,
  lc_tm_at 0 0 t1 -> lc_tm_at 0 0 t2 ->
  Safe RIntTrue t1 -> Safe RIntTrue t2 ->
  Safe (R_Refine Ty_Int (Pred_Eq (tm_bvar 0) (tm_arith op t1 t2)))
       (tm_arith op t1 t2).
Proof.
  intros op t1 t2 Hlc1 Hlc2 H1 H2.
  assert (Haux : forall s, multi (tm_arith op t1 t2) s ->
      (exists u1 u2, s = tm_arith op u1 u2 /\ Safe RIntTrue u1 /\ Safe RIntTrue u2) ->
      Safe (R_Refine Ty_Int (Pred_Eq (tm_bvar 0) (tm_arith op t1 t2))) s).
  { intros s Hhist Hex. unfold Safe. intros t' Hms. revert Hhist Hex.
    induction Hms as [ | s0 w t'' Hstep Hmulti IH].
    - (* refl *) intros Hhist Hex.
      destruct Hex as [u1 [u2 [Es [H1u H2u]]]]. subst.
      destruct (Safe_refl _ _ H1u) as [Hfv1u [Hlc1u Hc1]].
      destruct (Safe_refl _ _ H2u) as [Hfv2u [Hlc2u Hc2]].
      split; [ simpl; rewrite Hfv1u, Hfv2u; reflexivity | ].
      split; [ simpl; apply lc_tm_arith; auto | ].
      destruct Hc1 as [[Hv1 HV1] | [u1' Hs1]].
      + destruct Hc2 as [[Hv2 HV2] | [u2' Hs2]].
        * destruct (V_refine_elim _ _ _ HV1) as [_ [_ [[n Hn] _]]].
          destruct (V_refine_elim _ _ _ HV2) as [_ [_ [[m Hm2] _]]].
          subst u1. subst u2.
          right. exists (tm_int (eval_integer_operator op n m)). apply ST_ArithInt.
        * right. exists (tm_arith op u1 u2'). apply ST_Arith2; auto.
      + right. exists (tm_arith op u1' u2). apply ST_Arith1; auto.
    - (* step *) intros Hhist Hex. subst.
      destruct Hex as [u1 [u2 [Es [H1u H2u]]]]. subst.
      destruct (arith_step_cases op u1 u2 w Hstep)
        as [[u1' [Hs1 Heq]] | [[u2' [Hv1 [Hs2 Heq]]] | [n [m [Heq1 [Heq2 Heq3]]]]]].
      + subst w. apply IH.
        * eapply multi_step_r; eauto.
        * exists u1', u2. split; [reflexivity | split].
          -- apply Safe_of_step with (t := u1); auto.
          -- auto.
      + subst w. apply IH.
        * eapply multi_step_r; eauto.
        * exists u1, u2'. split; [reflexivity | split].
          -- auto.
          -- apply Safe_of_step with (t := u2); auto.
      + subst u1. subst u2. subst w.
        assert (Ht'' : t'' = tm_int (eval_integer_operator op n m)).
        { apply (multi_value_inv (tm_int (eval_integer_operator op n m)) t''); auto. apply v_int. }
        subst t''.
        split; [ simpl; auto | ].
        split; [ simpl; apply lc_tm_int | ].
        left. split; [apply v_int | ].
        apply V_refine_intro.
        * apply v_int.
        * reflexivity.
        * exists (eval_integer_operator op n m). reflexivity.
        * unfold qualifier_holds, predicate_holds. simpl.
          rewrite (open_tm_rec_lc 0 0 t1 Hlc1 (tm_int (eval_integer_operator op n m))).
          rewrite (open_tm_rec_lc 0 0 t2 Hlc2 (tm_int (eval_integer_operator op n m))).
          exists (tm_int (eval_integer_operator op n m)). split.
          -- apply PMS_Refl.
          -- split.
             ++ apply multi_pms. eapply multi_step_r; eauto.
             ++ apply v_int. }
  apply Haux with (s := tm_arith op t1 t2).
  - apply multi_refl.
  - exists t1, t2. split.
    + reflexivity.
    + split; assumption.
Qed.


(* ---------- free occurrences of a binder and opening ---------- *)

Fixpoint occurs_free (k : nat) (t : tm) : Prop :=
  match t with
  | tm_bvar i => i = k
  | tm_fvar _ => False
  | tm_abs T t1 => occurs_free (S k) t1
  | tm_app t1 t2 => occurs_free k t1 \/ occurs_free k t2
  | tm_tabs t1 => occurs_free k t1
  | tm_tapp t1 T => occurs_free k t1
  | tm_int _ => False
  | tm_div t1 t2 => occurs_free k t1 \/ occurs_free k t2
  | tm_arith op t1 t2 => occurs_free k t1 \/ occurs_free k t2
  end.

Lemma occurs_free_dec : forall k t, occurs_free k t \/ ~ occurs_free k t.
Proof.
  intros k t. revert k. induction t; intros k; simpl.
  - destruct (Nat.eq_dec n k); auto.
  - auto.
  - apply IHt.
  - specialize (IHt1 k). specialize (IHt2 k).
    destruct IHt1 as [H1 | H1]; destruct IHt2 as [H2 | H2]; auto.
    right. intros [H | H]; contradiction.
  - apply IHt.
  - apply IHt.
  - auto.
  - specialize (IHt1 k). specialize (IHt2 k).
    destruct IHt1 as [H1 | H1]; destruct IHt2 as [H2 | H2]; auto.
    right. intros [H | H]; contradiction.
  - specialize (IHt1 k). specialize (IHt2 k).
    destruct IHt1 as [H1 | H1]; destruct IHt2 as [H2 | H2]; auto.
    right. intros [H | H]; contradiction.
Qed.

Lemma open_tm_no_occ : forall k u t, ~ occurs_free k t -> open_tm_rec k u t = t.
Proof.
  intros k u t. revert k u. induction t; intros k u H; simpl in *.
  - destruct (Nat.eqb k n) eqn:E; [| reflexivity].
    apply Nat.eqb_eq in E. subst n. exfalso. apply H. reflexivity.
  - reflexivity.
  - f_equal. apply IHt. intro Hc. apply H. simpl. auto.
  - f_equal; [apply IHt1 | apply IHt2]; intro Hc; apply H; simpl; auto.
  - f_equal. apply IHt. intro Hc. apply H. simpl. auto.
  - f_equal. apply IHt. intro Hc. apply H. simpl. auto.
  - reflexivity.
  - f_equal; [apply IHt1 | apply IHt2]; intro Hc; apply H; simpl; auto.
  - f_equal; [apply IHt1 | apply IHt2]; intro Hc; apply H; simpl; auto.
Qed.

Lemma occurs_free_fv : forall k u t, occurs_free k t ->
  incl (fv_tm u) (fv_tm (open_tm_rec k u t)).
Proof.
  intros k u t. revert k u. induction t; intros k u H; simpl in *.
  - assert (Hnk : n = k) by auto. subst n. simpl.
    destruct (Nat.eqb k k) eqn:E.
    + intros x Hx. exact Hx.
    + apply Nat.eqb_neq in E. exfalso. apply E. reflexivity.
  - contradiction.
  - intros x Hx. apply IHt; auto.
  - destruct H as [H | H].
    + intros x Hx. apply in_app_iff. left. apply IHt1; auto.
    + intros x Hx. apply in_app_iff. right. apply IHt2; auto.
  - intros x Hx. apply IHt; auto.
  - intros x Hx. apply IHt; auto.
  - contradiction.
  - destruct H as [H | H].
    + intros x Hx. apply in_app_iff. left. apply IHt1; auto.
    + intros x Hx. apply in_app_iff. right. apply IHt2; auto.
  - destruct H as [H | H].
    + intros x Hx. apply in_app_iff. left. apply IHt1; auto.
    + intros x Hx. apply in_app_iff. right. apply IHt2; auto.
Qed.

Lemma occurs_free_ftv : forall k u t, occurs_free k t ->
  incl (ftv_tm u) (ftv_tm (open_tm_rec k u t)).
Proof.
  intros k u t. revert k u. induction t; intros k u H; simpl in *.
  - assert (Hnk : n = k) by auto. subst n. simpl.
    destruct (Nat.eqb k k) eqn:E.
    + intros x Hx. exact Hx.
    + apply Nat.eqb_neq in E. exfalso. apply E. reflexivity.
  - contradiction.
  - intros x Hx. apply in_app_iff. right. apply IHt; auto.
  - destruct H as [H | H].
    + intros x Hx. apply in_app_iff. left. apply IHt1; auto.
    + intros x Hx. apply in_app_iff. right. apply IHt2; auto.
  - intros x Hx. apply IHt; auto.
  - intros x Hx. apply in_app_iff. left. apply IHt; auto.
  - contradiction.
  - destruct H as [H | H].
    + intros x Hx. apply in_app_iff. left. apply IHt1; auto.
    + intros x Hx. apply in_app_iff. right. apply IHt2; auto.
  - destruct H as [H | H].
    + intros x Hx. apply in_app_iff. left. apply IHt1; auto.
    + intros x Hx. apply in_app_iff. right. apply IHt2; auto.
Qed.

Lemma fv_open_tm_incl : forall k u t, incl (fv_tm t) (fv_tm (open_tm_rec k u t)).
Proof.
  intros k u t. revert k u. induction t; intros k u; simpl.
  - intros x Hx. destruct (Nat.eqb k n); auto. simpl in Hx. contradiction.
  - intros x Hx. exact Hx.
  - intros x Hx. apply IHt; auto.
  - simpl in *. intros x Hx. apply in_app_iff in Hx. apply in_app_iff.
    destruct Hx as [Hx | Hx]; [left; apply IHt1 | right; apply IHt2]; auto.
  - intros x Hx. apply IHt; auto.
  - simpl in *. intros x Hx. apply IHt; auto.
  - intros x Hx. exact Hx.
  - simpl in *. intros x Hx. apply in_app_iff in Hx. apply in_app_iff.
    destruct Hx as [Hx | Hx]; [left; apply IHt1 | right; apply IHt2]; auto.
  - simpl in *. intros x Hx. apply in_app_iff in Hx. apply in_app_iff.
    destruct Hx as [Hx | Hx]; [left; apply IHt1 | right; apply IHt2]; auto.
Qed.

Lemma ftv_open_tm_incl : forall k u t, incl (ftv_tm t) (ftv_tm (open_tm_rec k u t)).
Proof.
  intros k u t. revert k u. induction t; intros k u; simpl.
  - intros x Hx. destruct (Nat.eqb k n); auto. simpl in Hx. contradiction.
  - intros x Hx. contradiction.
  - simpl in *. intros x Hx. apply in_app_iff in Hx. apply in_app_iff.
    destruct Hx as [Hx | Hx].
    + left. auto.
    + right. apply IHt; auto.
  - simpl in *. intros x Hx. apply in_app_iff in Hx. apply in_app_iff.
    destruct Hx as [Hx | Hx].
    + left. apply IHt1; auto.
    + right. apply IHt2; auto.
  - intros x Hx. apply IHt; auto.
  - simpl in *. intros x Hx. apply in_app_iff in Hx. apply in_app_iff.
    destruct Hx as [Hx | Hx].
    + left. apply IHt; auto.
    + right. auto.
  - intros x Hx. contradiction.
  - simpl in *. intros x Hx. apply in_app_iff in Hx. apply in_app_iff.
    destruct Hx as [Hx | Hx].
    + left. apply IHt1; auto.
    + right. apply IHt2; auto.
  - simpl in *. intros x Hx. apply in_app_iff in Hx. apply in_app_iff.
    destruct Hx as [Hx | Hx].
    + left. apply IHt1; auto.
    + right. apply IHt2; auto.
Qed.

Lemma subst_ty_nil : forall s T, fv_ty T = [] -> subst_ty s T = T.
Proof.
  intros s T. induction T; simpl; intros H.
  - reflexivity.
  - simpl in H. discriminate H.
  - apply app_eq_nil in H. destruct H as [H1 H2]. f_equal.
    + apply IHT1. auto.
    + apply IHT2. auto.
  - f_equal. apply IHT. auto.
  - reflexivity.
Qed.

Lemma subst_tm_nil : forall s t, fv_tm t = [] -> subst_tm s t = t.
Proof.
  intros s t. induction t; simpl; intros H.
  - reflexivity.
  - simpl in H. discriminate H.
  - f_equal. apply IHt. auto.
  - apply app_eq_nil in H. destruct H as [H1 H2]. f_equal.
    + apply IHt1. auto.
    + apply IHt2. auto.
  - f_equal. apply IHt. auto.
  - f_equal. apply IHt. auto.
  - reflexivity.
  - apply app_eq_nil in H. destruct H as [H1 H2]. f_equal.
    + apply IHt1. auto.
    + apply IHt2. auto.
  - apply app_eq_nil in H. destruct H as [H1 H2]. f_equal.
    + apply IHt1. auto.
    + apply IHt2. auto.
Qed.

Lemma subst_tm_ty_nil : forall s t, ftv_tm t = [] -> subst_tm_ty s t = t.
Proof.
  intros s t. induction t; simpl; intros H.
  - reflexivity.
  - reflexivity.
  - apply app_eq_nil in H. destruct H as [H1 H2]. f_equal.
    + apply subst_ty_nil. auto.
    + apply IHt. auto.
  - apply app_eq_nil in H. destruct H as [H1 H2]. f_equal.
    + apply IHt1. auto.
    + apply IHt2. auto.
  - f_equal. apply IHt. auto.
  - apply app_eq_nil in H. destruct H as [H1 H2]. f_equal.
    + apply IHt. auto.
    + apply subst_ty_nil. auto.
  - reflexivity.
  - apply app_eq_nil in H. destruct H as [H1 H2]. f_equal.
    + apply IHt1. auto.
    + apply IHt2. auto.
  - apply app_eq_nil in H. destruct H as [H1 H2]. f_equal.
    + apply IHt1. auto.
    + apply IHt2. auto.
Qed.

Lemma close_tm_nil : forall s ts t, fv_tm t = [] -> ftv_tm t = [] -> close_tm s ts t = t.
Proof.
  intros s ts t Hfv Hftv. unfold close_tm.
  rewrite subst_tm_ty_nil with (s := ts) by auto.
  apply subst_tm_nil. auto.
Qed.


Lemma incl_nil_eq : forall (l l' : list atom), incl l l' -> l' = [] -> l = [].
Proof.
  intros l l' H H'. subst l'. destruct l; auto.
  exfalso. apply (H a). simpl. auto.
Qed.

(* ---------- contexts: atoms, free variables ---------- *)

Fixpoint atoms_rcontext (RGamma : rcontext) : list atom :=
  match RGamma with
  | [] => []
  | (x, R) :: tl => x :: atoms_rcontext tl
  end.

Fixpoint fvs_rcontext (RGamma : rcontext) : list atom :=
  match RGamma with
  | [] => []
  | (x, R) :: tl => fv_rty R ++ fvs_rcontext tl
  end.

Fixpoint ftvs_rcontext (RGamma : rcontext) : list atom :=
  match RGamma with
  | [] => []
  | (x, R) :: tl => ftv_rty R ++ ftvs_rcontext tl
  end.

Lemma lookup_rcontext_in_atoms : forall (RGamma : rcontext) (x : atom) (R : rty),
  lookup_rcontext x RGamma = Some R -> In x (atoms_rcontext RGamma).
Proof.
  intros RGamma. induction RGamma as [| [y R'] tl IH]; intros x R H; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. subst y. left. reflexivity.
    + right. apply (IH x R). auto.
Qed.

Lemma lookup_rcontext_in_fvs : forall (RGamma : rcontext) (x : atom) (R : rty),
  lookup_rcontext x RGamma = Some R -> incl (fv_rty R) (fvs_rcontext RGamma).
Proof.
  intros RGamma. induction RGamma as [| [y R'] tl IH]; intros x R H; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. subst y. inversion H. subst R'.
      intros a Ha. apply in_app_iff. auto.
    + intros a Ha. apply in_app_iff. right. apply (IH x R); auto.
Qed.

Lemma lookup_rcontext_in_ftvs : forall (RGamma : rcontext) (x : atom) (R : rty),
  lookup_rcontext x RGamma = Some R -> incl (ftv_rty R) (ftvs_rcontext RGamma).
Proof.
  intros RGamma. induction RGamma as [| [y R'] tl IH]; intros x R H; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. subst y. inversion H. subst R'.
      intros a Ha. apply in_app_iff. auto.
    + intros a Ha. apply in_app_iff. right. apply (IH x R); auto.
Qed.

Lemma lookup_rcontext_upd_neq : forall (RGamma : rcontext) (x : atom) (R1 : rty)
  (y : atom), y <> x -> lookup_rcontext y (update_rcontext RGamma x R1) = lookup_rcontext y RGamma.
Proof.
  intros RGamma x R1 y H. simpl. destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst. exfalso. apply H. reflexivity.
  - reflexivity.
Qed.

Lemma lookup_rcontext_upd_eq : forall (RGamma : rcontext) (x : atom) (R1 : rty),
  lookup_rcontext x (update_rcontext RGamma x R1) = Some R1.
Proof.
  intros. simpl. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma notin_atoms_lookup : forall (RGamma : rcontext) (x : atom),
  ~ In x (atoms_rcontext RGamma) -> lookup_rcontext x RGamma = None.
Proof.
  intros RGamma. induction RGamma as [| [y R'] tl IH]; intros x H; simpl in *.
  - reflexivity.
  - destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. subst y. exfalso. apply H. left. reflexivity.
    + apply IH. intro Hin. apply H. right. auto.
Qed.

(* ---------- the fundamental theorem and semantic subtyping ---------- *)

Definition ctx_interp (s : atom -> tm) (ts : atom -> ty) (RGamma : rcontext) : Prop :=
  forall x R, lookup_rcontext x RGamma = Some R -> V (close_rty s ts R) (s x).

Lemma open_close_tm_eq : forall s ts t u, env_ok s ts ->
  fv_tm (open_tm t u) = [] -> ftv_tm (open_tm t u) = [] ->
  open_tm (close_tm s ts t) (close_tm s ts u) = open_tm t u.
Proof.
  intros s ts t u Henv Hfv Hftv.
  destruct (occurs_free_dec 0 t) as [Hocc | Hnocc].
  - (* u occurs: everything is closed *) unfold open_tm.
    assert (Hfvu : fv_tm u = []) by
      (apply (incl_nil_eq (fv_tm u) (fv_tm (open_tm t u))); [apply occurs_free_fv; auto | auto]).
    assert (Hftvu : ftv_tm u = []) by
      (apply (incl_nil_eq (ftv_tm u) (ftv_tm (open_tm t u))); [apply occurs_free_ftv; auto | auto]).
    assert (Hfvt : fv_tm t = []) by
      (apply (incl_nil_eq (fv_tm t) (fv_tm (open_tm t u))); [apply fv_open_tm_incl | auto]).
    assert (Hftvt : ftv_tm t = []) by
      (apply (incl_nil_eq (ftv_tm t) (ftv_tm (open_tm t u))); [apply ftv_open_tm_incl | auto]).
    rewrite (close_tm_nil s ts t Hfvt Hftvt).
    rewrite (close_tm_nil s ts u Hfvu Hftvu).
    reflexivity.
  - (* u does not occur *) unfold open_tm.
    rewrite (open_tm_no_occ 0 u t Hnocc).
    assert (Hfvt : fv_tm t = []) by
      (apply (incl_nil_eq (fv_tm t) (fv_tm (open_tm t u))); [apply fv_open_tm_incl | auto]).
    assert (Hftvt : ftv_tm t = []) by
      (apply (incl_nil_eq (ftv_tm t) (ftv_tm (open_tm t u))); [apply ftv_open_tm_incl | auto]).
    rewrite (close_tm_nil s ts t Hfvt Hftvt).
    rewrite (open_tm_no_occ 0 (close_tm s ts u) t Hnocc).
    reflexivity.
Qed.

Lemma open_close_qual_eq : forall s ts p u, env_ok s ts ->
  predicate_closed (open_qualifier_tm p u) ->
  open_qualifier_tm (close_qual s ts p) (close_tm s ts u) = open_qualifier_tm p u.
Proof.
  intros s ts p. induction p; intros u Henv Hpc; auto; try (unfold close_qual, open_qualifier_tm; simpl).
  - (* Eq *) destruct Hpc as [H1 [H2 [H3 [H4 [H5 H6]]]]].
    unfold close_qual, open_qualifier_tm. simpl.
    f_equal.
    + apply open_close_tm_eq; auto.
    + apply open_close_tm_eq; auto.
  - destruct Hpc as [H1 [H2 [H3 [H4 [H5 H6]]]]].
    unfold close_qual, open_qualifier_tm. simpl.
    f_equal.
    + apply open_close_tm_eq; auto.
    + apply open_close_tm_eq; auto.
  - destruct Hpc as [H1 [H2 [H3 [H4 [H5 H6]]]]].
    unfold close_qual, open_qualifier_tm. simpl.
    f_equal.
    + apply open_close_tm_eq; auto.
    + apply open_close_tm_eq; auto.
  - destruct Hpc as [Hpc1 Hpc2]. f_equal.
    + apply IHp1; auto.
    + apply IHp2; auto.
  - destruct Hpc as [Hpc1 Hpc2]. f_equal.
    + apply IHp1; auto.
    + apply IHp2; auto.
  - f_equal. apply IHp; auto.
Qed.

Lemma qual_close_holds : forall s ts p u, env_ok s ts ->
  predicate_closed (open_qualifier_tm p u) ->
  qualifier_holds (open_qualifier_tm p u) ->
  qualifier_holds (open_qualifier_tm (close_qual s ts p) (close_tm s ts u)).
Proof.
  intros s ts p u Henv Hpc Hq.
  rewrite (open_close_qual_eq s ts p u); auto.
Qed.

(* closed qualifiers are unaffected by closing substitutions *)
Lemma close_qual_closed : forall s ts p, predicate_closed p -> close_qual s ts p = p.
Proof.
  intros s ts p. induction p; simpl; intros H; auto.
  - (* Eq *) destruct H as [H1 [H2 [H3 [H4 [H5 H6]]]]].
    unfold close_qual. simpl. f_equal.
    + apply close_tm_nil; auto.
    + apply close_tm_nil; auto.
  - destruct H as [H1 [H2 [H3 [H4 [H5 H6]]]]].
    unfold close_qual. simpl. f_equal.
    + apply close_tm_nil; auto.
    + apply close_tm_nil; auto.
  - destruct H as [H1 [H2 [H3 [H4 [H5 H6]]]]].
    unfold close_qual. simpl. f_equal.
    + apply close_tm_nil; auto.
    + apply close_tm_nil; auto.
  - destruct H as [H1 H2]. unfold close_qual. simpl. f_equal.
    + apply IHp1; auto.
    + apply IHp2; auto.
  - destruct H as [H1 H2]. unfold close_qual. simpl. f_equal.
    + apply IHp1; auto.
    + apply IHp2; auto.
  - unfold close_qual. simpl. f_equal. apply IHp; auto.
Qed.


(* ---------- more closing-substitution helpers ---------- *)

Lemma fv_subst_tm_all_nil : forall (s : atom -> tm) (t : tm),
  (forall x, fv_tm (s x) = []) -> fv_tm (subst_tm s t) = [].
Proof.
  intros s t Hs. induction t; simpl.
  - reflexivity.
  - apply Hs.
  - apply IHt.
  - rewrite (IHt1), (IHt2). reflexivity.
  - apply IHt.
  - apply IHt.
  - reflexivity.
  - rewrite (IHt1), (IHt2). reflexivity.
  - rewrite (IHt1), (IHt2). reflexivity.
Qed.

Lemma fv_close_tm : forall s ts t, env_ok s ts -> fv_tm (close_tm s ts t) = [].
Proof.
  intros s ts t Henv. unfold close_tm.
  apply fv_subst_tm_all_nil. apply (env_ok_fv s ts Henv).
Qed.

Lemma upd_eq : forall (s : atom -> tm) (x : atom) (u : tm), upd s x u x = u.
Proof. intros. unfold upd. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma upd_neq : forall (s : atom -> tm) (x : atom) (u : tm) (y : atom),
  y <> x -> upd s x u y = s y.
Proof. intros. unfold upd. destruct (Nat.eqb x y) eqn:E. apply Nat.eqb_eq in E. exfalso; auto. auto. Qed.

Lemma upd_ty_eq : forall (s : atom -> ty) (x : atom) (u : ty), upd_ty s x u x = u.
Proof. intros. unfold upd_ty. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma upd_ty_neq : forall (s : atom -> ty) (x : atom) (u : ty) (y : atom),
  y <> x -> upd_ty s x u y = s y.
Proof. intros. unfold upd_ty. destruct (Nat.eqb x y) eqn:E. apply Nat.eqb_eq in E. exfalso; auto. auto. Qed.

Lemma close_tm_upd_neq : forall s ts x u t,
  ~ In x (fv_tm t) -> close_tm (upd s x u) ts t = close_tm s ts t.
Proof.
  intros. unfold close_tm. rewrite subst_tm_upd_fresh; auto.
  rewrite fv_tm_subst_tm_ty. auto.
Qed.

Lemma close_tm_upd_ty_neq : forall s ts x u t,
  ~ In x (ftv_tm t) -> close_tm s (upd_ty ts x u) t = close_tm s ts t.
Proof.
  intros. unfold close_tm. rewrite subst_tm_ty_upd_fresh; auto.
Qed.

Lemma close_rty_upd_neq : forall s ts x u R,
  ~ In x (fv_rty R) -> close_rty (upd s x u) ts R = close_rty s ts R.
Proof.
  intros. unfold close_rty. rewrite subst_rty_tm_upd_fresh; auto.
  rewrite fv_rty_subst_rty_ty. auto.
Qed.

Lemma close_rty_upd_ty_neq : forall s ts x u R,
  ~ In x (ftv_rty R) -> close_rty s (upd_ty ts x u) R = close_rty s ts R.
Proof.
  intros. unfold close_rty. rewrite subst_rty_ty_upd_fresh; auto.
Qed.

Lemma close_qual_upd_open : forall s ts x u p,
  lc_tm_at 0 0 u -> lc0_tm_env s -> lc0_ty_env ts -> ~ In x (fv_qual p) ->
  close_qual (upd s x u) ts (open_qualifier_tm p (tm_fvar x)) =
  open_qualifier_tm (close_qual s ts p) u.
Proof.
  intros s ts x u p Hu Hs Hts Hx.
  assert (H1 : close_tm (upd s x u) ts (tm_fvar x) = u).
  { unfold close_tm. simpl. unfold upd. rewrite Nat.eqb_refl. reflexivity. }
  assert (H2 : close_qual (upd s x u) ts p = close_qual s ts p).
  { unfold close_qual. rewrite subst_qual_tm_upd_fresh.
    - reflexivity.
    - rewrite fv_qual_subst_qual_ty. auto. }
  unfold open_qualifier_tm, open_qualifier_tm_rec.
  rewrite (close_qual_open_qual_tm_rec (upd s x u) ts 0 (tm_fvar x) p).
  - rewrite H1, H2. reflexivity.
  - apply lc_tm_fvar.
  - intros y. unfold upd. destruct (Nat.eqb x y); auto.
  - exact Hts.
Qed.

(* ---------- safety of specific closed redexes ---------- *)

Lemma Safe_beta : forall R T body u,
  value (tm_abs T body) -> value u ->
  fv_tm body = [] -> fv_tm u = [] ->
  Safe R (open_tm body u) -> Safe R (tm_app (tm_abs T body) u).
Proof.
  intros R T body u Hv Hu Hfv1 Hfv2 H. unfold Safe in *.
  intros t' Hm. destruct (multi_app_abs T body u t' Hv Hu Hm) as [-> | Hm'].
  - split.
    + simpl. rewrite Hfv1, Hfv2. reflexivity.
    + split.
      * simpl. apply lc_tm_app.
        -- apply value_lc. auto.
        -- apply value_lc. auto.
      * right. exists (open_tm body u). apply ST_AppAbs.
        -- apply value_lc. auto.
        -- auto.
  - apply H. auto.
Qed.

Lemma Safe_tapp_tabs : forall R body U,
  value (tm_tabs body) -> lc_ty_at 0 U ->
  fv_tm body = [] ->
  Safe (open_rty_ty R U) (open_tm_ty body U) ->
  Safe (open_rty_ty R U) (tm_tapp (tm_tabs body) U).
Proof.
  intros R body U Hv HU Hfv H. unfold Safe in *.
  intros t' Hm. destruct (multi_tapp_tabs body U t' Hv HU Hm) as [-> | Hm'].
  - split.
    + simpl. auto.
    + split.
      * simpl. apply lc_tm_tapp.
        -- apply value_lc. auto.
        -- auto.
      * right. exists (open_tm_ty body U). apply ST_TAppTabs.
        -- apply value_lc. auto.
        -- auto.
  - apply H. auto.
Qed.

(* ---------- semantic soundness of entailment ---------- *)

Lemma qh_true : qualifier_holds Pred_True.
Proof. reflexivity. Qed.

Lemma qh_and : forall p q,
  qualifier_holds (Pred_And p q) <-> (qualifier_holds p /\ qualifier_holds q).
Proof. intros. reflexivity. Qed.

Lemma qh_or : forall p q,
  qualifier_holds (Pred_Or p q) <-> (qualifier_holds p \/ qualifier_holds q).
Proof. intros. reflexivity. Qed.

Lemma qh_not : forall p, qualifier_holds (Pred_Not p) <-> ~ qualifier_holds p.
Proof. intros. reflexivity. Qed.

Lemma qh_false : qualifier_holds Pred_False <-> False.
Proof. reflexivity. Qed.

Lemma close_qual_and : forall s ts p q,
  close_qual s ts (Pred_And p q) = Pred_And (close_qual s ts p) (close_qual s ts q).
Proof. intros. unfold close_qual. simpl. reflexivity. Qed.

Lemma close_qual_or : forall s ts p q,
  close_qual s ts (Pred_Or p q) = Pred_Or (close_qual s ts p) (close_qual s ts q).
Proof. intros. unfold close_qual. simpl. reflexivity. Qed.

Lemma close_qual_not : forall s ts p,
  close_qual s ts (Pred_Not p) = Pred_Not (close_qual s ts p).
Proof. intros. unfold close_qual. simpl. reflexivity. Qed.

Lemma entails_sound : forall Delta RGamma ps qs,
  entails Delta RGamma ps qs ->
  forall s ts, env_ok s ts -> ctx_interp s ts RGamma ->
  qualifier_holds (close_qual s ts ps) -> qualifier_holds (close_qual s ts qs).
Proof.
  intros Delta RGamma ps qs H. induction H; intros s ts Henv Hctx Hq.
  - exact Hq.
  - apply qh_true.
  - apply IHentails2; auto.
  - rewrite close_qual_and in Hq. rewrite qh_and in Hq. tauto.
  - rewrite close_qual_and in Hq. rewrite qh_and in Hq. tauto.
  - rewrite close_qual_and. rewrite qh_and. split.
    + apply IHentails1; auto.
    + apply IHentails2; auto.
  - rewrite close_qual_or. rewrite qh_or. left. auto.
  - rewrite close_qual_or. rewrite qh_or. right. auto.
  - rewrite close_qual_or in Hq. rewrite qh_or in Hq.
    destruct Hq as [Hq | Hq].
    + apply IHentails1; auto.
    + apply IHentails2; auto.
  - rewrite close_qual_not. rewrite qh_not. intro Hq2.
    apply IHentails with (s := s) (ts := ts); auto.
    rewrite close_qual_and. rewrite qh_and. split; auto.
  - rewrite close_qual_and in Hq. rewrite close_qual_not in Hq.
    rewrite qh_and in Hq. destruct Hq as [Hq Hnq].
    rewrite qh_not in Hnq. tauto.
  - (* Context *)
    unfold open_qualifier_tm, open_qualifier_tm_rec.
    rewrite (close_qual_open_qual_tm_rec s ts 0 (tm_fvar x) p).
    + pose proof (Hctx x (R_Refine T p) H) as HV.
      apply V_refine_elim in HV. tauto.
    + apply lc_tm_fvar.
    + apply (env_ok_lc s ts Henv).
    + apply (env_ok_ty s ts Henv).
  - rewrite qh_false in Hq. destruct Hq.
Qed.


(* ---------- combined induction scheme and the fundamental theorem ---------- *)

Scheme has_rtype_mutind := Induction for has_rtype Sort Prop
  with subtype_mutind := Induction for subtype Sort Prop.
Combined Scheme has_rtype_subtype_ind from has_rtype_mutind, subtype_mutind.

Lemma fundamental_and_subtype :
  (forall (Delta : ty_context) (RGamma : rcontext) (t : tm) (R : rty)
     (d : has_rtype Delta RGamma t R),
     forall s ts, env_ok s ts -> ctx_interp s ts RGamma ->
       Safe (close_rty s ts R) (close_tm s ts t))
  /\ (forall (Delta : ty_context) (RGamma : rcontext) (R : rty) (S : rty)
     (d : subtype Delta RGamma R S),
     forall s ts, env_ok s ts -> ctx_interp s ts RGamma ->
       forall v, V (close_rty s ts R) v -> V (close_rty s ts S) v).
Proof.
  apply has_rtype_subtype_ind
    with (P := fun (Delta : ty_context) (RGamma : rcontext) (t : tm) (R : rty)
                    (d : has_rtype Delta RGamma t R) =>
                 forall s ts, env_ok s ts -> ctx_interp s ts RGamma ->
                   Safe (close_rty s ts R) (close_tm s ts t))
         (P0 := fun (Delta : ty_context) (RGamma : rcontext) (R : rty) (S : rty)
                    (d : subtype Delta RGamma R S) =>
                 forall s ts, env_ok s ts -> ctx_interp s ts RGamma ->
                   forall v, V (close_rty s ts R) v -> V (close_rty s ts S) v).
  - (* RT_Var *)
    intros Delta RGamma x R Hlook Hwf s ts Henv Hctx.
    apply V_safe. apply (Hctx x R Hlook).
  - (* RT_Abs *)
    intros L Delta RGamma R1 body R2 Hwf Hbody IHb s ts Henv Hctx.
    set (x := fresh (concat_lists
       [L; atoms_rcontext RGamma; fvs_rcontext RGamma; fv_tm body; fv_rty R1; fv_rty R2])).
    assert (HxL : ~ In x L) by (unfold x; apply fresh_notin_concat; simpl; auto 10).
    assert (HxA : ~ In x (atoms_rcontext RGamma)) by (unfold x; apply fresh_notin_concat; simpl; auto 10).
    assert (HxF : ~ In x (fvs_rcontext RGamma)) by (unfold x; apply fresh_notin_concat; simpl; auto 10).
    assert (Hxbody : ~ In x (fv_tm body)) by (unfold x; apply fresh_notin_concat; simpl; auto 10).
    assert (HxR1 : ~ In x (fv_rty R1)) by (unfold x; apply fresh_notin_concat; simpl; auto 10).
    assert (HxR2 : ~ In x (fv_rty R2)) by (unfold x; apply fresh_notin_concat; simpl; auto 10).
    assert (Habs : value (close_tm s ts (tm_abs (erase R1) body))).
    { apply v_abs. change (lc_tm_at 0 0 (close_tm s ts (tm_abs (erase R1) body))).
      apply lc_close_tm; auto.
      apply (has_rtype_lc Delta RGamma (tm_abs (erase R1) body) (R_Func R1 R2)).
      apply RT_Abs with (L := L); auto. }
    apply V_safe. apply V_func_intro.
    + exact Habs.
    + change (fv_tm (close_tm s ts (tm_abs (erase R1) body)) = []).
      apply fv_close_tm; auto.
    + intros u Hu.
      set (s' := upd s x u).
      assert (Henv' : env_ok s' ts).
      { unfold s'. apply env_ok_upd; auto.
        - apply (V_value (close_rty s ts R1) u); auto.
        - apply (V_fv (close_rty s ts R1) u); auto. }
      assert (Hctx' : ctx_interp s' ts (update_rcontext RGamma x R1)).
      { intros y R' Hy. unfold s'.
        destruct (Nat.eqb y x) eqn:E.
        - apply Nat.eqb_eq in E. subst y.
          rewrite lookup_rcontext_upd_eq in Hy. inversion Hy. subst R'.
          rewrite upd_eq.
          rewrite (close_rty_upd_neq s ts x u R1 HxR1).
          auto.
        - apply Nat.eqb_neq in E.
          rewrite (lookup_rcontext_upd_neq RGamma x R1 y E) in Hy.
          rewrite (upd_neq s x u y E).
          assert (Hin : incl (fv_rty R') (fvs_rcontext RGamma)).
          { apply lookup_rcontext_in_fvs with (x := y). auto. }
          assert (HxR' : ~ In x (fv_rty R')).
          { intro Hc. apply HxF. apply Hin. auto. }
          rewrite (close_rty_upd_neq s ts x u R' HxR').
          auto. }
      pose proof (IHb x HxL s' ts Henv' Hctx') as Hsafe.
      unfold s' in Hsafe.
      rewrite (close_rty_upd_open_rty_tm s ts x u R2) in Hsafe;
        [| apply value_lc; apply (V_value (close_rty s ts R1) u); auto
         | apply (env_ok_lc s ts Henv) | apply (env_ok_ty s ts Henv) | auto].
      rewrite (close_tm_upd_open s ts x u body) in Hsafe;
        [| apply value_lc; apply (V_value (close_rty s ts R1) u); auto
         | apply (env_ok_lc s ts Henv) | apply (env_ok_ty s ts Henv) | auto].
      change (Safe (open_rty_tm (close_rty s ts R2) u)
                (tm_app (tm_abs (subst_ty ts (erase R1)) (close_tm s ts body)) u)).
      apply Safe_beta.
      * exact Habs.
      * apply (V_value (close_rty s ts R1) u); auto.
      * change (fv_tm (close_tm s ts body) = []). apply fv_close_tm; auto.
      * apply (V_fv (close_rty s ts R1) u); auto.
      * exact Hsafe.
  - (* RT_App *)
    intros Delta RGamma t1 t2 R1 R2 H1 IH1 H2 IH2 s ts Henv Hctx.
    pose proof (IH1 s ts Henv Hctx) as Hs1.
    pose proof (IH2 s ts Henv Hctx) as Hs2.
    apply Safe_app.
    + exact Hs1.
    + exact Hs2.
  - (* RT_TAbs *)
    intros L Delta RGamma body R Hbody IH s ts Henv Hctx.
    set (x := fresh (concat_lists
       [L; atoms_rcontext RGamma; ftvs_rcontext RGamma; ftv_tm body; ftv_rty R])).
    assert (HxL : ~ In x L) by (unfold x; apply fresh_notin_concat; simpl; auto 10).
    assert (HxA : ~ In x (atoms_rcontext RGamma)) by (unfold x; apply fresh_notin_concat; simpl; auto 10).
    assert (HxT : ~ In x (ftvs_rcontext RGamma)) by (unfold x; apply fresh_notin_concat; simpl; auto 10).
    assert (Hxbody : ~ In x (ftv_tm body)) by (unfold x; apply fresh_notin_concat; simpl; auto 10).
    assert (HxR : ~ In x (ftv_rty R)) by (unfold x; apply fresh_notin_concat; simpl; auto 10).
    assert (Habs : value (close_tm s ts (tm_tabs body))).
    { apply v_tabs. change (lc_tm_at 0 0 (close_tm s ts (tm_tabs body))).
      apply lc_close_tm; auto.
      apply (has_rtype_lc Delta RGamma (tm_tabs body) (R_Poly R)).
      apply RT_TAbs with (L := L); auto. }
    apply V_safe. apply V_poly_intro.
    + exact Habs.
    + change (fv_tm (close_tm s ts (tm_tabs body)) = []). apply fv_close_tm; auto.
    + intros U HU.
      set (ts' := upd_ty ts x U).
      assert (Henv' : env_ok s ts').
      { unfold ts'. apply env_ok_upd_ty; auto. }
      assert (Hctx' : ctx_interp s ts' RGamma).
      { intros y R' Hy. unfold ts'.
        assert (Hin : incl (ftv_rty R') (ftvs_rcontext RGamma)).
        { apply lookup_rcontext_in_ftvs with (x := y). auto. }
        assert (HxR' : ~ In x (ftv_rty R')).
        { intro Hc. apply HxT. apply Hin. auto. }
        rewrite (close_rty_upd_ty_neq s ts x U R' HxR').
        apply Hctx; auto. }
      pose proof (IH x HxL s ts' Henv' Hctx') as Hsafe.
      unfold ts' in Hsafe.
      rewrite (close_rty_upd_ty_open s ts x U R) in Hsafe;
        [| apply (env_ok_lc s ts Henv) | apply (env_ok_ty s ts Henv) | exact HU | exact HxR].
      rewrite (close_tm_upd_ty_open s ts x U body) in Hsafe;
        [| apply (env_ok_lc s ts Henv) | apply (env_ok_ty s ts Henv) | exact HU | exact Hxbody].
      change (Safe (open_rty_ty (close_rty s ts R) U)
                (tm_tapp (tm_tabs (close_tm s ts body)) U)).
      apply Safe_tapp_tabs.
      * exact Habs.
      * exact HU.
      * change (fv_tm (close_tm s ts body) = []). apply fv_close_tm; auto.
      * exact Hsafe.
  - (* RT_TApp *)
    intros Delta RGamma t R U Ht IHt Hwf s ts Henv Hctx.
    pose proof (IHt s ts Henv Hctx) as Hsafe.
    change (Safe (close_rty s ts (open_rty_ty_rec 0 U R)) (close_tm s ts (tm_tapp t U))).
    rewrite (close_rty_open_rty_ty_rec s ts 0 U R);
      [| apply (env_ok_lc s ts Henv) | apply (env_ok_ty s ts Henv)].
    change (Safe (open_rty_ty_rec 0 (subst_ty ts U) (close_rty s ts R))
              (tm_tapp (close_tm s ts t) (subst_ty ts U))).
    apply Safe_tapp with (R := close_rty s ts R).
    + change (Safe (R_Poly (close_rty s ts R)) (close_tm s ts t)). exact Hsafe.
    + apply lc_ty_subst_ty.
      * apply (env_ok_ty s ts Henv).
      * apply wf_ty_lc with (Delta := Delta). auto.
  - (* RT_Int *)
    intros Delta RGamma n s ts Henv Hctx.
    apply V_safe. apply V_refine_intro.
    + apply v_int.
    + reflexivity.
    + exists n. reflexivity.
    + apply qual_int_self.
  - (* RT_Div *)
    intros Delta RGamma t1 t2 H1 IH1 H2 IH2 s ts Henv Hctx.
    pose proof (IH1 s ts Henv Hctx) as Hs1.
    pose proof (IH2 s ts Henv Hctx) as Hs2.
    apply Safe_div; auto.
  - (* RT_Arith *)
    intros Delta RGamma op t1 t2 H1 IH1 H2 IH2 s ts Henv Hctx.
    pose proof (IH1 s ts Henv Hctx) as Hs1.
    pose proof (IH2 s ts Henv Hctx) as Hs2.
    apply Safe_arith.
    + apply lc_close_tm; auto.
      apply (has_rtype_lc Delta RGamma t1 (R_Refine Ty_Int Pred_True) H1).
    + apply lc_close_tm; auto.
      apply (has_rtype_lc Delta RGamma t2 (R_Refine Ty_Int Pred_True) H2).
    + exact Hs1.
    + exact Hs2.
  - (* RT_RefineValue *)
    intros Delta RGamma v T ps Htype Hval Hwf Hcl Hholds s ts Henv Hctx.
    apply V_safe. apply V_refine_intro.
    + apply value_close_tm; auto.
    + apply fv_close_tm; auto.
    + apply canon_close; auto.
      apply (has_type_canon Delta (erase_context RGamma) v T); auto.
    + apply qual_close_holds; auto.
  - (* RT_Sub *)
    intros Delta RGamma t R S Ht IHt Hwf Hsub IHsub s ts Henv Hctx.
    apply Safe_mono with (R := close_rty s ts R).
    + intros v Hv. apply (IHsub s ts Henv Hctx v Hv).
    + apply IHt; auto.
  - (* S_Refl *)
    intros Delta RGamma R s ts Henv Hctx v Hv. exact Hv.
  - (* S_Refine *)
    intros L Delta RGamma T ps qs Hent s ts Henv Hctx v Hv.
    destruct (V_refine_elim _ _ _ Hv) as [Hval [Hfv [Hcan Hq]]].
    apply V_refine_intro; auto.
    set (x := fresh (concat_lists
       [L; atoms_rcontext RGamma; fvs_rcontext RGamma; fv_qual ps; fv_qual qs])).
    assert (HxL : ~ In x L) by (unfold x; apply fresh_notin_concat; simpl; auto 10).
    assert (HxA : ~ In x (atoms_rcontext RGamma)) by (unfold x; apply fresh_notin_concat; simpl; auto 10).
    assert (HxF : ~ In x (fvs_rcontext RGamma)) by (unfold x; apply fresh_notin_concat; simpl; auto 10).
    assert (Hxps : ~ In x (fv_qual ps)) by (unfold x; apply fresh_notin_concat; simpl; auto 10).
    assert (Hxqs : ~ In x (fv_qual qs)) by (unfold x; apply fresh_notin_concat; simpl; auto 10).
    assert (Henv' : env_ok (upd s x v) ts).
    { apply env_ok_upd; auto. }
    assert (Hctx' : ctx_interp (upd s x v) ts
                    (update_rcontext RGamma x (R_Refine T Pred_True))).
    { intros y R' Hy.
      destruct (Nat.eqb y x) eqn:E.
      - apply Nat.eqb_eq in E. subst y.
        rewrite lookup_rcontext_upd_eq in Hy. inversion Hy. subst R'.
        rewrite upd_eq.
        rewrite (close_rty_upd_neq s ts x v (R_Refine T Pred_True)).
        + apply V_refine_intro; auto.
          apply qh_true.
        + simpl. auto.
      - apply Nat.eqb_neq in E.
        rewrite (lookup_rcontext_upd_neq RGamma x (R_Refine T Pred_True) y E) in Hy.
        rewrite (upd_neq s x v y E).
        assert (Hin : incl (fv_rty R') (fvs_rcontext RGamma)).
        { apply lookup_rcontext_in_fvs with (x := y). auto. }
        assert (HxR' : ~ In x (fv_rty R')).
        { intro Hc. apply HxF. apply Hin. auto. }
        rewrite (close_rty_upd_neq s ts x v R' HxR').
        apply Hctx; auto. }
    pose proof (entails_sound Delta (update_rcontext RGamma x (R_Refine T Pred_True))
                  (open_qualifier_tm ps (tm_fvar x))
                  (open_qualifier_tm qs (tm_fvar x))
                  (Hent x HxL) (upd s x v) ts Henv' Hctx') as Hs.
    change (qualifier_holds (open_qualifier_tm (close_qual s ts qs) v)).
    rewrite <- (close_qual_upd_open s ts x v qs);
      [| apply value_lc; auto | apply (env_ok_lc s ts Henv) | apply (env_ok_ty s ts Henv) | exact Hxqs].
    apply Hs.
    change (qualifier_holds (close_qual (upd s x v) ts (open_qualifier_tm ps (tm_fvar x)))).
    rewrite (close_qual_upd_open s ts x v ps);
      [| apply value_lc; auto | apply (env_ok_lc s ts Henv) | apply (env_ok_ty s ts Henv) | exact Hxps].
    exact Hq.
  - (* S_Func *)
    intros L Delta RGamma R1 R2 S1 S2 Hsub1 IH1 Hsub2 IH2 s ts Henv Hctx v Hv.
    destruct (V_func_elim _ _ _ Hv) as [Hval [Hfv Hcont]].
    apply V_func_intro; auto.
    intros u Hu.
    assert (HuR : V (close_rty s ts R1) u) by (apply (IH1 s ts Henv Hctx u); auto).
    pose proof (Hcont u HuR) as Hsafe.
    eapply Safe_mono with (R := open_rty_tm (close_rty s ts R2) u).
    + intros w Hw.
      set (x := fresh (concat_lists
         [L; atoms_rcontext RGamma; fvs_rcontext RGamma; fv_rty R2; fv_rty S2; fv_rty S1])).
      assert (HxL : ~ In x L) by (unfold x; apply fresh_notin_concat; simpl; auto 10).
      assert (HxA : ~ In x (atoms_rcontext RGamma)) by (unfold x; apply fresh_notin_concat; simpl; auto 10).
      assert (HxF : ~ In x (fvs_rcontext RGamma)) by (unfold x; apply fresh_notin_concat; simpl; auto 10).
      assert (HxR2 : ~ In x (fv_rty R2)) by (unfold x; apply fresh_notin_concat; simpl; auto 10).
      assert (HxS2 : ~ In x (fv_rty S2)) by (unfold x; apply fresh_notin_concat; simpl; auto 10).
      assert (HxS1 : ~ In x (fv_rty S1)) by (unfold x; apply fresh_notin_concat; simpl; auto 10).
      assert (Henv' : env_ok (upd s x u) ts).
      { apply env_ok_upd; auto.
        - apply (V_value (close_rty s ts S1) u); auto.
        - apply (V_fv (close_rty s ts S1) u); auto. }
      assert (Hctx' : ctx_interp (upd s x u) ts (update_rcontext RGamma x S1)).
      { intros y R' Hy.
        destruct (Nat.eqb y x) eqn:E.
        - apply Nat.eqb_eq in E. subst y.
          rewrite lookup_rcontext_upd_eq in Hy. inversion Hy. subst R'.
          rewrite upd_eq. rewrite (close_rty_upd_neq s ts x u S1 HxS1). auto.
        - apply Nat.eqb_neq in E.
          rewrite (lookup_rcontext_upd_neq RGamma x S1 y E) in Hy.
          rewrite (upd_neq s x u y E).
          assert (Hin : incl (fv_rty R') (fvs_rcontext RGamma)).
          { apply lookup_rcontext_in_fvs with (x := y). auto. }
          assert (HxR' : ~ In x (fv_rty R')).
          { intro Hc. apply HxF. apply Hin. auto. }
          rewrite (close_rty_upd_neq s ts x u R' HxR').
          apply Hctx; auto. }
      pose proof (IH2 x HxL (upd s x u) ts Henv' Hctx' w) as Hres.
      rewrite (close_rty_upd_open_rty_tm s ts x u R2) in Hres;
        [| apply value_lc; apply (V_value (close_rty s ts S1) u); auto
         | apply (env_ok_lc s ts Henv) | apply (env_ok_ty s ts Henv) | exact HxR2].
      rewrite (close_rty_upd_open_rty_tm s ts x u S2) in Hres;
        [| apply value_lc; apply (V_value (close_rty s ts S1) u); auto
         | apply (env_ok_lc s ts Henv) | apply (env_ok_ty s ts Henv) | exact HxS2].
      apply Hres. exact Hw.
    + exact Hsafe.
  - (* S_Witness *)
    intros Delta RGamma v0 R1 R2 S Hval0 Hrt IHrt Hsub IHsub s ts Henv Hctx w Hw.
    assert (Hrt' : Safe (close_rty s ts R1) (close_tm s ts v0)) by (apply IHrt; auto).
    destruct (Safe_refl _ _ Hrt') as [Hfvv [Hlcv Hcase]].
    destruct Hcase as [[Hvalv HV1] | [w' Hstep]].
    + assert (Hsub' : V (close_rty s ts (open_rty_tm R2 v0)) w).
      { apply (IHsub s ts Henv Hctx w). auto. }
      change (V (close_rty s ts (open_rty_tm_rec 0 v0 R2)) w) in Hsub'.
      rewrite (close_rty_open_rty_tm_rec s ts 0 v0 R2) in Hsub';
        [| apply value_lc; auto | apply (env_ok_lc s ts Henv) | apply (env_ok_ty s ts Henv)].
      apply V_exists_intro with (u := close_tm s ts v0).
      * apply V_value in Hw; auto.
      * apply V_fv in Hw; auto.
      * exact HV1.
      * exact Hsub'.
    + exfalso.
      apply (value_no_step (close_tm s ts v0) w').
      * apply value_close_tm; auto.
      * exact Hstep.
  - (* S_Bind *)
    intros L Delta RGamma R1 R2 S Hwf HlcS Hsub IHsub s ts Henv Hctx w Hw.
    destruct (V_exists_elim _ _ _ Hw) as [Hval [Hfv [u [Hu1 Hu2]]]].
    set (x := fresh (concat_lists
       [L; atoms_rcontext RGamma; fvs_rcontext RGamma; fv_rty R1; fv_rty R2; fv_rty S])).
    assert (HxL : ~ In x L) by (unfold x; apply fresh_notin_concat; simpl; auto 10).
    assert (HxA : ~ In x (atoms_rcontext RGamma)) by (unfold x; apply fresh_notin_concat; simpl; auto 10).
    assert (HxF : ~ In x (fvs_rcontext RGamma)) by (unfold x; apply fresh_notin_concat; simpl; auto 10).
    assert (HxR1 : ~ In x (fv_rty R1)) by (unfold x; apply fresh_notin_concat; simpl; auto 10).
    assert (HxR2 : ~ In x (fv_rty R2)) by (unfold x; apply fresh_notin_concat; simpl; auto 10).
    assert (HxS : ~ In x (fv_rty S)) by (unfold x; apply fresh_notin_concat; simpl; auto 10).
    assert (Henv' : env_ok (upd s x u) ts).
    { apply env_ok_upd; auto.
      - apply (V_value (close_rty s ts R1) u); auto.
      - apply (V_fv (close_rty s ts R1) u); auto. }
    assert (Hctx' : ctx_interp (upd s x u) ts (update_rcontext RGamma x R1)).
    { intros y R' Hy.
      destruct (Nat.eqb y x) eqn:E.
      - apply Nat.eqb_eq in E. subst y.
        rewrite lookup_rcontext_upd_eq in Hy. inversion Hy. subst R'.
        rewrite upd_eq. rewrite (close_rty_upd_neq s ts x u R1 HxR1). auto.
      - apply Nat.eqb_neq in E.
        rewrite (lookup_rcontext_upd_neq RGamma x R1 y E) in Hy.
        rewrite (upd_neq s x u y E).
        assert (Hin : incl (fv_rty R') (fvs_rcontext RGamma)).
        { apply lookup_rcontext_in_fvs with (x := y). auto. }
        assert (HxR' : ~ In x (fv_rty R')).
        { intro Hc. apply HxF. apply Hin. auto. }
        rewrite (close_rty_upd_neq s ts x u R' HxR').
        apply Hctx; auto. }
    pose proof (IHsub x HxL (upd s x u) ts Henv' Hctx' w) as Hres.
    rewrite (close_rty_upd_open_rty_tm s ts x u R2) in Hres;
      [| apply value_lc; apply (V_value (close_rty s ts R1) u); auto
       | apply (env_ok_lc s ts Henv) | apply (env_ok_ty s ts Henv) | exact HxR2].
    rewrite (close_rty_upd_neq s ts x u S HxS) in Hres.
    apply Hres. exact Hu2.
  - (* S_Poly *)
    intros L Delta RGamma R S Hsub IHsub s ts Henv Hctx v Hv.
    destruct (V_poly_elim _ _ Hv) as [Hval [Hfv Hcont]].
    apply V_poly_intro; auto.
    intros U HU.
    pose proof (Hcont U HU) as Hsafe.
    eapply Safe_mono with (R := open_rty_ty (close_rty s ts R) U).
    + intros w Hw.
      set (x := fresh (concat_lists
         [L; atoms_rcontext RGamma; ftvs_rcontext RGamma; ftv_rty R; ftv_rty S])).
      assert (HxL : ~ In x L) by (unfold x; apply fresh_notin_concat; simpl; auto 10).
      assert (HxA : ~ In x (atoms_rcontext RGamma)) by (unfold x; apply fresh_notin_concat; simpl; auto 10).
      assert (HxT : ~ In x (ftvs_rcontext RGamma)) by (unfold x; apply fresh_notin_concat; simpl; auto 10).
      assert (HxR : ~ In x (ftv_rty R)) by (unfold x; apply fresh_notin_concat; simpl; auto 10).
      assert (HxS : ~ In x (ftv_rty S)) by (unfold x; apply fresh_notin_concat; simpl; auto 10).
      assert (Henv' : env_ok s (upd_ty ts x U)).
      { apply env_ok_upd_ty; auto. }
      assert (Hctx' : ctx_interp s (upd_ty ts x U) RGamma).
      { intros y R' Hy.
        assert (Hin : incl (ftv_rty R') (ftvs_rcontext RGamma)).
        { apply lookup_rcontext_in_ftvs with (x := y). auto. }
        assert (HxR' : ~ In x (ftv_rty R')).
        { intro Hc. apply HxT. apply Hin. auto. }
        rewrite (close_rty_upd_ty_neq s ts x U R' HxR').
        apply Hctx; auto. }
      pose proof (IHsub x HxL s (upd_ty ts x U) Henv' Hctx' w) as Hres.
      rewrite (close_rty_upd_ty_open s ts x U R) in Hres;
        [| apply (env_ok_lc s ts Henv) | apply (env_ok_ty s ts Henv) | exact HU | exact HxR].
      rewrite (close_rty_upd_ty_open s ts x U S) in Hres;
        [| apply (env_ok_lc s ts Henv) | apply (env_ok_ty s ts Henv) | exact HU | exact HxS].
      apply Hres. exact Hw.
    + exact Hsafe.
  - (* S_Trans *)
    intros Delta RGamma R S U Hsub1 IH1 Hsub2 IH2 s ts Henv Hctx v Hv.
    apply (IH2 s ts Henv Hctx). apply (IH1 s ts Henv Hctx). exact Hv.
Qed.

Lemma fundamental : forall Delta RGamma t R,
  has_rtype Delta RGamma t R ->
  forall s ts, env_ok s ts -> ctx_interp s ts RGamma ->
  Safe (close_rty s ts R) (close_tm s ts t).
Proof.
  intros Delta RGamma t R Hd s ts Henv Hctx.
  exact (proj1 fundamental_and_subtype Delta RGamma t R Hd s ts Henv Hctx).
Qed.

Lemma subtype_sem : forall Delta RGamma R S,
  subtype Delta RGamma R S ->
  forall s ts, env_ok s ts -> ctx_interp s ts RGamma ->
  forall v, V (close_rty s ts R) v -> V (close_rty s ts S) v.
Proof.
  intros Delta RGamma R S Hd s ts Henv Hctx v Hv.
  exact (proj2 fundamental_and_subtype Delta RGamma R S Hd s ts Henv Hctx v Hv).
Qed.

Lemma fv_open_tm_ty_rec : forall k t U, fv_tm (open_tm_ty_rec k U t) = fv_tm t.
Proof.
  intros k t U. revert k U. induction t; intros k U; simpl.
  - reflexivity.
  - reflexivity.
  - apply IHt.
  - rewrite IHt1, IHt2. reflexivity.
  - apply IHt.
  - apply IHt.
  - reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma fv_open_tm_ty : forall t U, fv_tm (open_tm_ty t U) = fv_tm t.
Proof. intros; apply fv_open_tm_ty_rec. Qed.

(* ---------- free variables of typed terms ---------- *)

Definition atoms_context (Gamma : context) : list atom := map (fun p => fst p) Gamma.

Lemma lookup_context_in_atoms : forall (Gamma : context) (x : atom) (T : ty),
  lookup_context x Gamma = Some T -> In x (atoms_context Gamma).
Proof.
  intros Gamma. induction Gamma as [| [y T'] tl IH]; intros x T H; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. subst y. left. reflexivity.
    + right. apply (IH x T). auto.
Qed.

Lemma atoms_context_erase : forall (RGamma : rcontext),
  atoms_context (erase_context RGamma) = atoms_rcontext RGamma.
Proof.
  intros RGamma. induction RGamma as [| [y R] tl IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma has_type_fv_incl : forall Delta Gamma t T, has_type Delta Gamma t T ->
  incl (fv_tm t) (atoms_context Gamma).
Proof.
  intros Delta Gamma t T H.
  induction H as [ Delta Gamma x T Hlook Hwf
                 | L Delta Gamma T1 t2 T2 Hwf Hbody IHb
                 | Delta Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
                 | L Delta Gamma t T Hbody IHb
                 | Delta Gamma t T U Ht IHt Hwf
                 | Delta Gamma n
                 | Delta Gamma t1 t2 H1 IH1 H2 IH2
                 | Delta Gamma op t1 t2 H1 IH1 H2 IH2 ].
  - intros a Ha. simpl in Ha. destruct Ha as [Heq | Hc].
    + subst a. apply lookup_context_in_atoms with (T := T); auto.
    + contradiction.
  - (* T_Abs *)
    intros y Hy.
    assert (Hfresh : ~ In (fresh (L ++ fv_tm t2)) (L ++ fv_tm t2)) by apply fresh_notin.
    apply notin_app_iff in Hfresh. destruct Hfresh as [HxL Hxbody].
    assert (Hin : In y (fv_tm (open_tm t2 (tm_fvar (fresh (L ++ fv_tm t2)))))).
    { apply fv_open_tm_incl. auto. }
    pose proof (IHb (fresh (L ++ fv_tm t2)) HxL) as Hres.
    apply Hres in Hin.
    simpl in Hin. destruct Hin as [Heq | Hin].
    + subst y. exfalso. apply Hxbody. auto.
    + auto.
  - intros y Hy. apply in_app_iff in Hy.
    destruct Hy as [Hy | Hy].
    + apply IH1; auto.
    + apply IH2; auto.
  - (* T_TAbs *)
    intros y Hy.
    assert (Hfresh : ~ In (fresh (L ++ fv_tm t)) (L ++ fv_tm t)) by apply fresh_notin.
    apply notin_app_iff in Hfresh. destruct Hfresh as [HxL Hxbody].
    pose proof (IHb (fresh (L ++ fv_tm t)) HxL) as Hres.
    apply Hres. rewrite fv_open_tm_ty. auto.
  - intros y Hy. apply IHt. auto.
  - intros a Ha. simpl in Ha. contradiction.
  - intros y Hy. apply in_app_iff in Hy.
    destruct Hy as [Hy | Hy].
    + apply IH1; auto.
    + apply IH2; auto.
  - intros y Hy. apply in_app_iff in Hy.
    destruct Hy as [Hy | Hy].
    + apply IH1; auto.
    + apply IH2; auto.
Qed.

Lemma has_rtype_fv_incl : forall Delta RGamma t R, has_rtype Delta RGamma t R ->
  incl (fv_tm t) (atoms_rcontext RGamma).
Proof.
  intros Delta RGamma t R H.
  induction H as [ Delta RGamma x R Hlook Hwf
                 | L Delta RGamma R1 body R2 Hwf Hbody IHb
                 | Delta RGamma t1 t2 R1 R2 H1 IH1 H2 IH2
                 | L Delta RGamma body R H IH
                 | Delta RGamma t R U Ht IHt Hwf
                 | Delta RGamma n
                 | Delta RGamma t1 t2 H1 IH1 H2 IH2
                 | Delta RGamma op t1 t2 H1 IH1 H2 IH2
                 | Delta RGamma v T ps Htype Hval Hwf Hcl Hholds
                 | Delta RGamma t R S Ht IHt Hwf Hsub ].
  - intros a Ha. simpl in Ha. destruct Ha as [Heq | Hc].
    + subst a. apply lookup_rcontext_in_atoms with (R := R); auto.
    + contradiction.
  - (* RT_Abs *)
    intros y Hy.
    assert (Hfresh : ~ In (fresh (L ++ fv_tm body)) (L ++ fv_tm body)) by apply fresh_notin.
    apply notin_app_iff in Hfresh. destruct Hfresh as [HxL Hxbody].
    assert (Hin : In y (fv_tm (open_tm body (tm_fvar (fresh (L ++ fv_tm body)))))).
    { apply fv_open_tm_incl. auto. }
    specialize (IHb (fresh (L ++ fv_tm body)) HxL).
    apply IHb in Hin.
    simpl in Hin. destruct Hin as [Heq | Hin].
    + subst y. exfalso. apply Hxbody. auto.
    + auto.
  - intros y Hy. apply in_app_iff in Hy.
    destruct Hy as [Hy | Hy].
    + apply IH1; auto.
    + apply IH2; auto.
  - (* RT_TAbs *)
    intros y Hy.
    assert (Hfresh : ~ In (fresh (L ++ fv_tm body)) (L ++ fv_tm body)) by apply fresh_notin.
    apply notin_app_iff in Hfresh. destruct Hfresh as [HxL Hxbody].
    specialize (IH (fresh (L ++ fv_tm body)) HxL).
    apply IH. rewrite fv_open_tm_ty. auto.
  - intros y Hy. apply IHt. auto.
  - intros a Ha. simpl in Ha. contradiction.
  - intros y Hy. apply in_app_iff in Hy.
    destruct Hy as [Hy | Hy].
    + apply IH1; auto.
    + apply IH2; auto.
  - intros y Hy. apply in_app_iff in Hy.
    destruct Hy as [Hy | Hy].
    + apply IH1; auto.
    + apply IH2; auto.
  - (* RT_RefineValue *)
    intros y Hy.
    rewrite <- atoms_context_erase.
    exact (has_type_fv_incl Delta (erase_context RGamma) v T Htype y Hy).
  - auto.
Qed.

(* ---------- the identity type substitution ---------- *)

Definition id_tm (x : atom) : tm := tm_fvar x.
Definition id_ty (x : atom) : ty := Ty_FVar x.

Lemma subst_ty_id : forall T, subst_ty id_ty T = T.
Proof.
  intros T. induction T; simpl; auto; try (f_equal; auto).
Qed.

Lemma subst_tm_ty_id : forall t, subst_tm_ty id_ty t = t.
Proof.
  intros t. induction t; simpl; auto; try (f_equal; auto);
    try (rewrite subst_ty_id); auto.
Qed.

Lemma subst_tm_ty_id_fst : forall t, subst_tm_ty id_ty t = t.
Proof. apply subst_tm_ty_id. Qed.

Theorem never_stuck : forall (t t' : tm) (R : rty),
  has_rtype [] empty_rcontext t R ->
  multi t t' ->
  value t' \/ exists t'' : tm, t' --> t''.
Proof.
  intros t t' R H Hm.
  assert (Hfv : fv_tm t = []).
  { apply (incl_nil_eq (fv_tm t) (atoms_rcontext empty_rcontext)).
    - apply has_rtype_fv_incl with (Delta := []) (R := R). auto.
    - reflexivity. }
  pose (sigma := fun _ : atom => tm_int 0%Z).
  assert (Henv : env_ok sigma id_ty).
  { split.
    - intros x. split; [apply v_int | reflexivity].
    - intros X. apply lc_ty_fvar. }
  assert (Hctx : ctx_interp sigma id_ty empty_rcontext).
  { intros x R' Hl. simpl in Hl. discriminate Hl. }
  pose proof (fundamental [] empty_rcontext t R H sigma id_ty Henv Hctx) as Hsafe.
  assert (Hclose : close_tm sigma id_ty t = t).
  { unfold close_tm. rewrite subst_tm_ty_id. apply subst_tm_nil. auto. }
  rewrite Hclose in Hsafe.
  unfold Safe in Hsafe.
  destruct (Hsafe t' Hm) as [Hf [Hl Hcase]].
  destruct Hcase as [[Hv _] | Hstep].
  - left; auto.
  - right; auto.
Qed.

End SystemFRefinementTask.
