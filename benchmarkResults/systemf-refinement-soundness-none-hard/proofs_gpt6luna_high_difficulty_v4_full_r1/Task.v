From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
From Stdlib Require Import ZArith.BinInt.
From Stdlib Require Import Program.Wf.

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

(* Some operational facts used by the adequacy argument. *)
Lemma multi_trans : forall t u v, multi t u -> multi u v -> multi t v.
Proof.
  intros t u v H; induction H; intros Huv.
  - exact Huv.
  - econstructor; eauto.
Qed.

Lemma value_no_step : forall v t, value v -> ~ (v --> t).
Proof.
  intros v t Hv Hs; inversion Hv; subst; inversion Hs.
Qed.

Lemma value_locally_closed_tm : forall v, value v -> locally_closed_tm v.
Proof.
  intros v H; inversion H; subst; try assumption; constructor.
Qed.

Lemma canonical_int : forall Delta v,
  has_type Delta [] v Ty_Int -> value v -> exists n, v = tm_int n.
Proof.
  intros Delta v Hty Hv; inversion Hv; subst; inversion Hty; subst; eexists; reflexivity.
Qed.

Lemma canonical_arrow : forall Delta v T1 T2,
  has_type Delta [] v (Ty_Arrow T1 T2) -> value v ->
  exists body, v = tm_abs T1 body.
Proof.
  intros Delta v T1 T2 Hty Hv; inversion Hv; subst; inversion Hty; subst; eexists; reflexivity.
Qed.

Lemma canonical_all : forall Delta v T,
  has_type Delta [] v (Ty_All T) -> value v ->
  exists body, v = tm_tabs body.
Proof.
  intros Delta v T Hty Hv; inversion Hv; subst; inversion Hty; subst; eexists; reflexivity.
Qed.

Lemma multi_to_predicate_multi : forall t u,
  multi t u -> predicate_multistep t u.
Proof.
  intros t u H; induction H.
  - constructor.
  - econstructor; eauto.
Qed.

Lemma value_equality_holds : forall v,
  value v -> predicate_holds (Pred_Eq v v).
Proof.
  intros v Hv; unfold predicate_holds; simpl.
  exists v; split; [constructor|].
  split; [constructor|exact Hv].
Qed.

Lemma nonzero_observation : forall d m,
  predicate_holds (Pred_Ne d (tm_int 0%Z)) ->
  multi d (tm_int m) -> m <> 0%Z.
Proof.
  intros d m Hne Hrun Heq; subst m.
  unfold predicate_holds, Pred_Ne in Hne.
  unfold open_qualifier_tm, open_qualifier_tm_rec, open_pred_tm_rec in Hne.
  simpl in Hne.
  apply Hne.
  exists (tm_int 0%Z); repeat split.
  - apply multi_to_predicate_multi; exact Hrun.
  - constructor.
  - constructor.
Qed.

Lemma closed_division_progress : forall v1 v2,
  has_type [] [] v1 Ty_Int -> value v1 ->
  has_type [] [] v2 Ty_Int -> value v2 ->
  predicate_holds (Pred_Ne v2 (tm_int 0%Z)) ->
  exists t', tm_div v1 v2 --> t'.
Proof.
  intros v1 v2 Hty1 Hv1 Hty2 Hv2 Hne.
  destruct (canonical_int [] v1 Hty1 Hv1) as [n ->].
  destruct (canonical_int [] v2 Hty2 Hv2) as [m ->].
  assert (Hm : m <> 0%Z).
  { eapply nonzero_observation; eauto using multi_refl. }
  exists (tm_int (Z.div n m)); constructor; exact Hm.
Qed.

Lemma erase_open_rty_tm_rec : forall R k u,
  erase (open_rty_tm_rec k u R) = erase R.
Proof.
  induction R; intros; simpl; try rewrite IHR; try rewrite IHR1; try rewrite IHR2; reflexivity.
Qed.

Lemma erase_open_rty_tm : forall R u,
  erase (open_rty_tm R u) = erase R.
Proof. intros; apply erase_open_rty_tm_rec. Qed.

Lemma erase_open_rty_ty_rec : forall R k U,
  erase (open_rty_ty_rec k U R) = open_ty_rec k U (erase R).
Proof.
  induction R; intros; simpl; try rewrite IHR; try rewrite IHR1; try rewrite IHR2; reflexivity.
Qed.

Lemma erase_open_rty_ty : forall R U,
  erase (open_rty_ty R U) = open_ty (erase R) U.
Proof. intros; apply erase_open_rty_ty_rec. Qed.

Lemma max_atom_bound : forall x L, In x L -> x <= max_atom L.
Proof.
  intros x L; induction L as [|y L IH]; simpl; intros Hin; [contradiction|].
  destruct Hin as [->|Hin]; [apply Nat.le_max_l|].
  eapply Nat.le_trans; [apply IH; exact Hin|apply Nat.le_max_r].
Qed.

Lemma fresh_notin : forall L, ~ In (fresh L) L.
Proof.
  intros L Hin; unfold fresh in *; pose proof (max_atom_bound _ _ Hin); lia.
Qed.

Lemma div_int_step_iff : forall n m,
  (exists t', tm_div (tm_int n) (tm_int m) --> t') <-> m <> 0%Z.
Proof.
  intros n m; split.
  - intros [t' H]; inversion H; subst;
      try solve [inversion H2]; try solve [inversion H4]; assumption.
  - intros H; eexists; apply ST_DivInt; exact H.
Qed.

(* A semantic environment assigns the locally nameless dependent binders.
   Its explicit use keeps the interpretation structurally recursive in rty. *)
Fixpoint instantiate_tm_rec (k : nat) (rho : list tm) (t : tm) : tm :=
  match t with
  | tm_bvar i =>
      if i <? k then tm_bvar i else nth (i - k) rho (tm_bvar i)
  | tm_fvar x => tm_fvar x
  | tm_abs T t1 => tm_abs T (instantiate_tm_rec (S k) rho t1)
  | tm_app t1 t2 => tm_app (instantiate_tm_rec k rho t1) (instantiate_tm_rec k rho t2)
  | tm_tabs t1 => tm_tabs (instantiate_tm_rec k rho t1)
  | tm_tapp t1 T => tm_tapp (instantiate_tm_rec k rho t1) T
  | tm_int n => tm_int n
  | tm_div t1 t2 => tm_div (instantiate_tm_rec k rho t1) (instantiate_tm_rec k rho t2)
  | tm_arith op t1 t2 => tm_arith op (instantiate_tm_rec k rho t1) (instantiate_tm_rec k rho t2)
  end.

Fixpoint instantiate_qualifier_rec (k : nat) (rho : list tm) (p : qualifier)
    : qualifier :=
  match p with
  | Pred_True => Pred_True
  | Pred_False => Pred_False
  | Pred_Eq t1 t2 => Pred_Eq (instantiate_tm_rec k rho t1) (instantiate_tm_rec k rho t2)
  | Pred_Lt t1 t2 => Pred_Lt (instantiate_tm_rec k rho t1) (instantiate_tm_rec k rho t2)
  | Pred_Le t1 t2 => Pred_Le (instantiate_tm_rec k rho t1) (instantiate_tm_rec k rho t2)
  | Pred_And p1 p2 => Pred_And (instantiate_qualifier_rec k rho p1)
                               (instantiate_qualifier_rec k rho p2)
  | Pred_Or p1 p2 => Pred_Or (instantiate_qualifier_rec k rho p1)
                             (instantiate_qualifier_rec k rho p2)
  | Pred_Not p1 => Pred_Not (instantiate_qualifier_rec k rho p1)
  end.

Definition insert_after_first (a : tm) (rho : list tm) : list tm :=
  match rho with
  | [] => [a]
  | x :: xs => x :: a :: xs
  end.

Lemma instantiate_tm_rec_lc : forall K k t,
  lc_tm_at K k t -> forall rho, instantiate_tm_rec k rho t = t.
Proof.
  intros K k t H; induction H; intros rho; simpl; try rewrite IHlc_tm_at;
    try rewrite IHlc_tm_at1; try rewrite IHlc_tm_at2; try reflexivity.
  - assert (Hi : (i <? k) = true) by (apply Nat.ltb_lt; exact H).
    rewrite Hi; reflexivity.
Qed.

Lemma open_tm_rec_lc : forall K k t,
  lc_tm_at K k t -> forall u, open_tm_rec k u t = t.
Proof.
  intros K k t H; induction H; intros u; simpl; try rewrite IHlc_tm_at;
    try rewrite IHlc_tm_at1; try rewrite IHlc_tm_at2; try reflexivity.
  - assert (Heq : Nat.eqb k i = false) by (apply Nat.eqb_neq; lia).
    rewrite Heq; reflexivity.
Qed.

Lemma lc_tm_at_mono : forall K k t,
  lc_tm_at K k t -> forall k', k <= k' -> lc_tm_at K k' t.
Proof.
  intros K k t H; induction H; intros k' Hle; eauto using lc_tm_at.
  - constructor; lia.
  - econstructor; eauto. apply IHlc_tm_at; lia.
Qed.

Lemma tm_subst_open_tm_rec : forall t,
  forall k x s u, locally_closed_tm s ->
    tm_subst x s (open_tm_rec k u t) =
    open_tm_rec k (tm_subst x s u) (tm_subst x s t).
Proof.
  induction t; intros k x s u Hlc; simpl; try reflexivity.
  - destruct (Nat.eqb k n); reflexivity.
  - destruct (Nat.eqb x a) eqn:E; simpl.
    + rewrite open_tm_rec_lc with (K:=0) (k:=k) (t:=s).
      * reflexivity.
      * eapply lc_tm_at_mono; [exact Hlc|lia].
    + reflexivity.
  - f_equal; apply IHt; exact Hlc.
  - f_equal; [apply IHt1|apply IHt2]; exact Hlc.
  - f_equal; apply IHt; exact Hlc.
  - f_equal; apply IHt; exact Hlc.
  - f_equal; [apply IHt1|apply IHt2]; exact Hlc.
  - f_equal; [apply IHt1|apply IHt2]; exact Hlc.
Qed.

Lemma lc_ty_at_mono : forall K T,
  lc_ty_at K T -> forall K', K <= K' -> lc_ty_at K' T.
Proof.
  intros K T H; induction H; intros K' Hle.
  - constructor; lia.
  - constructor.
  - econstructor; [eapply IHlc_ty_at1|eapply IHlc_ty_at2]; lia.
  - econstructor; eapply IHlc_ty_at; lia.
  - constructor.
Qed.

Lemma lc_tm_at_mono_both : forall K k t,
  lc_tm_at K k t -> forall K' k', K <= K' -> k <= k' -> lc_tm_at K' k' t.
Proof.
  intros K k t H; induction H; intros K' k' HK Hk.
  - constructor; lia.
  - constructor.
  - econstructor.
    + eapply lc_ty_at_mono; eauto.
    + eapply IHlc_tm_at; lia.
  - econstructor; [eapply IHlc_tm_at1|eapply IHlc_tm_at2]; eauto; lia.
  - econstructor. eapply IHlc_tm_at; lia.
  - econstructor.
    + eapply IHlc_tm_at; lia.
    + eapply lc_ty_at_mono; eauto.
  - constructor.
  - econstructor; [eapply IHlc_tm_at1|eapply IHlc_tm_at2]; eauto; lia.
  - econstructor; [eapply IHlc_tm_at1|eapply IHlc_tm_at2]; eauto; lia.
Qed.

Lemma lc_tm_at_subst : forall K k t,
  lc_tm_at K k t -> forall x s,
  locally_closed_tm s -> lc_tm_at K k (tm_subst x s t).
Proof.
  intros K k t H; induction H; intros z s Hs; simpl.
  - constructor; assumption.
  - destruct (Nat.eqb z x); [eapply lc_tm_at_mono_both; [exact Hs|lia|lia]|constructor].
  - econstructor.
    + assumption.
    + apply IHlc_tm_at; exact Hs.
  - econstructor; [apply IHlc_tm_at1|apply IHlc_tm_at2]; exact Hs.
  - econstructor; apply IHlc_tm_at; exact Hs.
  - econstructor; [apply IHlc_tm_at|assumption]; exact Hs.
  - constructor.
  - econstructor; [apply IHlc_tm_at1|apply IHlc_tm_at2]; exact Hs.
  - econstructor; [apply IHlc_tm_at1|apply IHlc_tm_at2]; exact Hs.
Qed.

Lemma value_tm_subst : forall x s v,
  value v -> locally_closed_tm s -> value (tm_subst x s v).
Proof.
  intros x s v Hv; induction Hv; intro Hs; simpl.
  - apply v_abs; change (lc_tm_at 0 0 (tm_subst x s (tm_abs T t))).
    eapply lc_tm_at_subst; eauto.
  - apply v_tabs; change (lc_tm_at 0 0 (tm_subst x s (tm_tabs t))).
    eapply lc_tm_at_subst; eauto.
  - apply v_int.
Qed.

Lemma open_ty_rec_lc : forall K T,
  lc_ty_at K T -> forall U, open_ty_rec K U T = T.
Proof.
  intros K T H; induction H; intros U; simpl.
  - assert (Heq : Nat.eqb k i = false) by (apply Nat.eqb_neq; lia).
    rewrite Heq; reflexivity.
  - reflexivity.
  - rewrite IHlc_ty_at1, IHlc_ty_at2; reflexivity.
  - rewrite IHlc_ty_at; reflexivity.
  - reflexivity.
Qed.

Lemma open_tm_ty_rec_lc : forall K k t,
  lc_tm_at K k t -> forall U, open_tm_ty_rec K U t = t.
Proof.
  intros K k t H; induction H; intros U; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite open_ty_rec_lc with (U:=U) (T:=T); [rewrite IHlc_tm_at; reflexivity|assumption].
  - rewrite IHlc_tm_at1, IHlc_tm_at2; reflexivity.
  - rewrite IHlc_tm_at; reflexivity.
  - rewrite IHlc_tm_at; rewrite open_ty_rec_lc with (U:=U) (T:=T); [reflexivity|assumption].
  - reflexivity.
  - rewrite IHlc_tm_at1, IHlc_tm_at2; reflexivity.
  - rewrite IHlc_tm_at1, IHlc_tm_at2; reflexivity.
Qed.

Lemma tm_subst_open_tm_ty_rec : forall (t : tm) (k : nat)
    (U : ty) (x : atom) (s : tm),
  locally_closed_tm s ->
  tm_subst x s (open_tm_ty_rec k U t) =
  open_tm_ty_rec k U (tm_subst x s t).
Proof.
  induction t; intros k U x s Hs; simpl; try reflexivity.
  - destruct (Nat.eqb x a); simpl.
    + rewrite open_tm_ty_rec_lc with (K:=k) (k:=0) (U:=U) (t:=s).
      * reflexivity.
      * eapply lc_tm_at_mono_both; [exact Hs|lia|lia].
    + reflexivity.
  - f_equal; eapply IHt; eauto.
  - f_equal; [eapply IHt1|eapply IHt2]; eauto.
  - f_equal; eapply IHt; eauto.
  - f_equal; eapply IHt; eauto.
  - f_equal; [eapply IHt1|eapply IHt2]; eauto.
  - f_equal; [eapply IHt1|eapply IHt2]; eauto.
Qed.

Lemma tm_subst_step : forall t u,
  t --> u -> forall x s, locally_closed_tm s ->
  tm_subst x s t --> tm_subst x s u.
Proof.
  intros t u Hstep; induction Hstep; intros x s Hs; simpl.
  - assert (Hcomm : tm_subst x s (open_tm t v) =
        open_tm (tm_subst x s t) (tm_subst x s v)).
    { unfold open_tm; apply tm_subst_open_tm_rec; exact Hs. }
    rewrite Hcomm; eapply ST_AppAbs.
    + change (locally_closed_tm (tm_subst x s (tm_abs T t))).
      eapply lc_tm_at_subst; eauto.
    + eapply value_tm_subst; eauto.
  - apply ST_App1; [apply IHHstep; exact Hs|].
    eapply lc_tm_at_subst; eauto.
  - apply ST_App2; [eapply value_tm_subst; eauto|apply IHHstep; exact Hs].
  - unfold open_tm_ty.
    rewrite (tm_subst_open_tm_ty_rec t 0 T x s Hs).
    apply ST_TAppTabs.
    + change (locally_closed_tm (tm_subst x s (tm_tabs t))).
      eapply lc_tm_at_subst; eauto.
    + assumption.
  - apply ST_TApp; [apply IHHstep; exact Hs|assumption].
  - apply ST_Div1; [apply IHHstep; exact Hs|].
    eapply lc_tm_at_subst; eauto.
  - apply ST_Div2; [eapply value_tm_subst; eauto|apply IHHstep; exact Hs].
  - apply ST_DivInt; assumption.
  - apply ST_Arith1; [apply IHHstep; exact Hs|].
    eapply lc_tm_at_subst; eauto.
  - apply ST_Arith2; [eapply value_tm_subst; eauto|apply IHHstep; exact Hs].
  - apply ST_ArithInt.
Qed.

Lemma multi_tm_subst : forall t u,
  multi t u -> forall x s, locally_closed_tm s ->
  multi (tm_subst x s t) (tm_subst x s u).
Proof.
  intros t u H; induction H; intros x s Hs.
  - constructor.
  - econstructor.
    + eapply tm_subst_step; eauto.
    + apply IHmulti; exact Hs.
Qed.

Lemma instantiate_open_tm_rec : forall t K k rho replacement,
  lc_tm_at K (S (S k)) t -> rho <> [] -> locally_closed_tm replacement ->
  instantiate_tm_rec k rho (open_tm_rec (S k) replacement t) =
  instantiate_tm_rec k (insert_after_first replacement rho) t.
Proof.
  induction t; intros K k rho replacement Hlc Hrho Hrep.
  - inversion Hlc; subst.
    change (instantiate_tm_rec k rho
      (if Nat.eqb (S k) n then replacement else tm_bvar n) =
      instantiate_tm_rec k (insert_after_first replacement rho) (tm_bvar n)).
    destruct (Nat.lt_ge_cases n k) as [Hlt|Hge].
    + assert (Hinst : (n <? k) = true) by (apply Nat.ltb_lt; exact Hlt).
      assert (Hopen : Nat.eqb (S k) n = false) by (apply Nat.eqb_neq; lia).
      rewrite Hopen; cbn [instantiate_tm_rec]; rewrite Hinst; reflexivity.
    + destruct (Nat.eq_dec n k) as [Heq|Hneq].
      * subst n.
        assert (Hopen : Nat.eqb (S k) k = false) by (apply Nat.eqb_neq; lia).
        assert (Hinst : (k <? k) = false) by (apply Nat.ltb_ge; lia).
        rewrite Hopen; cbn [instantiate_tm_rec]; rewrite Hinst.
        destruct rho as [|head tail]; [contradiction|].
        replace (k - k) with 0 by lia.
        cbv [insert_after_first nth]; reflexivity.
      * assert (Heq : n = S k) by lia; subst n.
      assert (Hopen : Nat.eqb (S k) (S k) = true) by apply Nat.eqb_refl.
      rewrite Hopen; cbn [instantiate_tm_rec].
      assert (Hrep' : lc_tm_at K k replacement).
      { eapply lc_tm_at_mono_both; [exact Hrep|lia|lia]. }
      rewrite instantiate_tm_rec_lc with (K:=K) (t:=replacement) (rho:=rho); [|exact Hrep'].
      destruct rho as [|head tail]; [contradiction|].
      replace (S k - k) with 1 by lia.
      cbv [insert_after_first nth].
      assert (Hltfalse : (S k <? k) = false) by (apply Nat.ltb_ge; lia).
      rewrite Hltfalse; reflexivity.
  - reflexivity.
  - inversion Hlc; subst. cbn [open_tm_rec instantiate_tm_rec]; f_equal. eapply IHt with (K:=K) (k:=S k); eauto.
  - inversion Hlc; subst. cbn [open_tm_rec instantiate_tm_rec]; f_equal; [eapply IHt1 with (K:=K) (k:=k)|eapply IHt2 with (K:=K) (k:=k)]; eauto.
  - inversion Hlc; subst. cbn [open_tm_rec instantiate_tm_rec]; f_equal. eapply IHt with (K:=S K) (k:=k); eauto.
  - inversion Hlc; subst. cbn [open_tm_rec instantiate_tm_rec]; f_equal. eapply IHt with (K:=K) (k:=k); eauto.
  - reflexivity.
  - inversion Hlc; subst. cbn [open_tm_rec instantiate_tm_rec]; f_equal; [eapply IHt1 with (K:=K) (k:=k)|eapply IHt2 with (K:=K) (k:=k)]; eauto.
  - inversion Hlc; subst. cbn [open_tm_rec instantiate_tm_rec]; f_equal; [eapply IHt1 with (K:=K) (k:=k)|eapply IHt2 with (K:=K) (k:=k)]; eauto.
Qed.

Definition sem_value (v : tm) : Prop :=
  value v /\ fv_tm v = [] /\ ftv_tm v = [].

Definition closed_substitution (theta : list (atom * tm)) : Prop :=
  forall x v, In (x, v) theta -> sem_value v.

Fixpoint qualifier_fv (p : qualifier) : list atom :=
  match p with
  | Pred_True | Pred_False => []
  | Pred_Eq t1 t2 | Pred_Lt t1 t2 | Pred_Le t1 t2 => fv_tm t1 ++ fv_tm t2
  | Pred_And p1 p2 | Pred_Or p1 p2 => qualifier_fv p1 ++ qualifier_fv p2
  | Pred_Not p1 => qualifier_fv p1
  end.

Fixpoint rty_term_fv (R : rty) : list atom :=
  match R with
  | R_Refine _ p => qualifier_fv p
  | R_Func R1 R2 | R_Exists R1 R2 => rty_term_fv R1 ++ rty_term_fv R2
  | R_Poly R1 => rty_term_fv R1
  end.

Definition context_type_fv (RGamma : rcontext) : list atom :=
  concat (map (fun b => rty_term_fv (snd b)) RGamma).

Fixpoint qualifier_substitute_many (theta : list (atom * tm)) (p : qualifier)
    : qualifier :=
  match theta with
  | [] => p
  | (x, s) :: theta' =>
      qualifier_substitute_many theta' (qualifier_subst x s p)
  end.

Fixpoint rvalue_core (n : nat) (Delta : ty_context)
    (theta : list (atom * tm)) (R : rty) (v : tm) : Prop :=
  match n with
  | 0 => has_type Delta [] v (erase R) /\ sem_value v
  | S n' =>
      match R with
      | R_Refine T p =>
          has_type Delta [] v T /\ sem_value v /\
          (T = Ty_Int -> exists m, v = tm_int m) /\
          predicate_holds (qualifier_substitute_many theta (open_qualifier_tm p v))
      | R_Func R1 R2 =>
          sem_value v /\ forall a,
            (forall ext, closed_substitution ext ->
              (forall x s, In (x,s) ext -> ~ In x (map fst theta)) ->
              rvalue_core n' Delta (ext ++ theta) R1 a) -> forall L,
            exists x, ~ In x L /\
              exists b, multi (tm_app v a) b /\ sem_value b /\
                (forall ext, closed_substitution ext ->
                (forall y s, In (y,s) ext -> ~ In y (map fst ((x,a)::theta))) ->
                  rvalue_core n' Delta (ext ++ ((x,a)::theta))
                    (open_rty_tm R2 (tm_fvar x)) b)
      | R_Exists R1 R2 =>
          sem_value v /\ exists w,
            (forall ext, closed_substitution ext ->
              (forall x s, In (x,s) ext -> ~ In x (map fst theta)) ->
              rvalue_core n' Delta (ext ++ theta) R1 w) /\ forall L,
            exists x, ~ In x L /\
              (forall ext, closed_substitution ext ->
                (forall y s, In (y,s) ext -> ~ In y (map fst ((x,w)::theta))) ->
                rvalue_core n' Delta (ext ++ ((x,w)::theta))
                  (open_rty_tm R2 (tm_fvar x)) v)
      | R_Poly R1 =>
          sem_value v /\ forall U, wf_ty Delta U -> forall ext,
            closed_substitution ext ->
            (forall x s, In (x,s) ext -> ~ In x (map fst theta)) ->
            rvalue_core n' Delta (ext ++ theta) (open_rty_ty R1 U) v
      end
  end.

Definition rvalue_n (n : nat) (Delta : ty_context)
    (theta : list (atom * tm)) (R : rty) (v : tm) : Prop :=
  forall ext, closed_substitution ext ->
    (forall x s, In (x,s) ext -> ~ In x (map fst theta)) ->
    rvalue_core n Delta (ext ++ theta) R v.

Definition rvalue (Delta : ty_context) (theta : list (atom * tm))
    (R : rty) (v : tm) : Prop :=
  forall n, rvalue_n n Delta theta R v.

Definition reducible (Delta : ty_context) (theta : list (atom * tm))
    (R : rty) (t : tm) : Prop :=
  forall u, multi t u ->
    exists v, multi u v /\ value v /\ rvalue Delta theta R v.


Fixpoint lookup_value_substitution (x : atom) (theta : list (atom * tm))
    : option tm :=
  match theta with
  | [] => None
  | (y, v) :: theta' =>
      if Nat.eqb x y then Some v else lookup_value_substitution x theta'
  end.

Fixpoint subst_many (theta : list (atom * tm)) (t : tm) : tm :=
  match theta with
  | [] => t
  | (x, s) :: theta' => subst_many theta' (tm_subst x s t)
  end.

Fixpoint qualifier_map_subst_many (theta : list (atom * tm)) (p : qualifier)
    : qualifier :=
  match p with
  | Pred_True => Pred_True
  | Pred_False => Pred_False
  | Pred_Eq t1 t2 => Pred_Eq (subst_many theta t1) (subst_many theta t2)
  | Pred_Lt t1 t2 => Pred_Lt (subst_many theta t1) (subst_many theta t2)
  | Pred_Le t1 t2 => Pred_Le (subst_many theta t1) (subst_many theta t2)
  | Pred_And p1 p2 => Pred_And (qualifier_map_subst_many theta p1)
                               (qualifier_map_subst_many theta p2)
  | Pred_Or p1 p2 => Pred_Or (qualifier_map_subst_many theta p1)
                             (qualifier_map_subst_many theta p2)
  | Pred_Not p1 => Pred_Not (qualifier_map_subst_many theta p1)
  end.

Lemma qualifier_map_subst_head : forall theta x s p,
  qualifier_map_subst_many theta (qualifier_subst x s p) =
  qualifier_map_subst_many ((x,s)::theta) p.
Proof.
  induction p; intros; unfold qualifier_subst in *; simpl in *; try reflexivity.
  - rewrite IHp1, IHp2; reflexivity.
  - rewrite IHp1, IHp2; reflexivity.
  - rewrite IHp; reflexivity.
Qed.

Lemma qualifier_map_subst_nil : forall p,
  qualifier_map_subst_many [] p = p.
Proof.
  induction p; simpl; try reflexivity.
  - rewrite IHp1, IHp2; reflexivity.
  - rewrite IHp1, IHp2; reflexivity.
  - rewrite IHp; reflexivity.
Qed.

Lemma qualifier_substitute_many_map : forall theta p,
  qualifier_substitute_many theta p = qualifier_map_subst_many theta p.
Proof.
  induction theta as [|[x s] theta IH]; intros p; simpl.
  - symmetry; apply qualifier_map_subst_nil.
  - rewrite IH; apply qualifier_map_subst_head.
Qed.

Lemma multi_subst_many : forall theta t u,
  closed_substitution theta -> multi t u ->
  multi (subst_many theta t) (subst_many theta u).
Proof.
  induction theta as [|[x s] theta IH]; intros t u Hclosed Hmulti; simpl.
  - exact Hmulti.
  - apply IH.
    + intros y v Hin; eapply Hclosed; simpl; right; exact Hin.
    + apply multi_tm_subst; [exact Hmulti|].
      eapply value_locally_closed_tm.
      apply (Hclosed x s); simpl; auto.
Qed.

Lemma subst_many_open_tm_ty_rec : forall theta K U t,
  closed_substitution theta ->
  subst_many theta (open_tm_ty_rec K U t) =
  open_tm_ty_rec K U (subst_many theta t).
Proof.
  induction theta as [|[x s] theta IH]; intros K U t Hclosed; simpl.
  - reflexivity.
  - rewrite tm_subst_open_tm_ty_rec with (k:=K) (U:=U) (x:=x) (s:=s).
    2: { eapply value_locally_closed_tm; apply (Hclosed x s); simpl; auto. }
    rewrite IH.
    + reflexivity.
    + intros y v Hin; eapply Hclosed; simpl; right; exact Hin.
Qed.

Definition reducible_at (n : nat) (Delta : ty_context)
    (theta : list (atom * tm)) (R : rty) (t : tm) : Prop :=
  forall u, multi (subst_many theta t) u ->
    exists v, multi u v /\ value v /\ rvalue_n n Delta theta R v.

Lemma tm_subst_fv_empty : forall x s t,
  fv_tm t = [] -> tm_subst x s t = t.
Proof.
  intros x s t; induction t; intro Hfv; simpl in *; try reflexivity.
  - destruct (Nat.eqb x a) eqn:Heq.
    + apply Nat.eqb_eq in Heq; subst; discriminate.
    + reflexivity.
  - rewrite IHt; auto.
  - apply app_eq_nil in Hfv as [H1 H2]. rewrite IHt1, IHt2; auto.
  - rewrite IHt; auto.
  - rewrite IHt; auto.
  - apply app_eq_nil in Hfv as [H1 H2]. rewrite IHt1, IHt2; auto.
  - apply app_eq_nil in Hfv as [H1 H2]. rewrite IHt1, IHt2; auto.
Qed.

Lemma tm_subst_notin_fv : forall x s t,
  ~ In x (fv_tm t) -> tm_subst x s t = t.
Proof.
  intros x s t; induction t; simpl; intro H; try reflexivity.
  - destruct (Nat.eqb x a) eqn:E; [apply Nat.eqb_eq in E; subst; exfalso; apply H; simpl; auto|reflexivity].
  - f_equal; apply IHt; exact H.
  - assert (H1 : ~ In x (fv_tm t1)) by (intro Hin; apply H; apply in_or_app; left; exact Hin).
    assert (H2 : ~ In x (fv_tm t2)) by (intro Hin; apply H; apply in_or_app; right; exact Hin).
    f_equal; [apply IHt1|apply IHt2]; assumption.
  - f_equal; apply IHt; exact H.
  - f_equal; apply IHt; exact H.
  - assert (H1 : ~ In x (fv_tm t1)) by (intro Hin; apply H; apply in_or_app; left; exact Hin).
    assert (H2 : ~ In x (fv_tm t2)) by (intro Hin; apply H; apply in_or_app; right; exact Hin).
    f_equal; [apply IHt1|apply IHt2]; assumption.
  - assert (H1 : ~ In x (fv_tm t1)) by (intro Hin; apply H; apply in_or_app; left; exact Hin).
    assert (H2 : ~ In x (fv_tm t2)) by (intro Hin; apply H; apply in_or_app; right; exact Hin).
    f_equal; [apply IHt1|apply IHt2]; assumption.
Qed.

Fixpoint qualifier_fv_empty (p : qualifier) : Prop :=
  match p with
  | Pred_True | Pred_False => True
  | Pred_Eq t1 t2 | Pred_Lt t1 t2 | Pred_Le t1 t2 =>
      fv_tm t1 = [] /\ fv_tm t2 = []
  | Pred_And p1 p2 | Pred_Or p1 p2 =>
      qualifier_fv_empty p1 /\ qualifier_fv_empty p2
  | Pred_Not p1 => qualifier_fv_empty p1
  end.

Lemma predicate_closed_fv_empty : forall p,
  predicate_closed p -> qualifier_fv_empty p.
Proof.
  induction p; simpl; intros H; try exact I.
  - destruct H as [_ [H1 [_ [_ [H2 _]]]]]; auto.
  - destruct H as [_ [H1 [_ [_ [H2 _]]]]]; auto.
  - destruct H as [_ [H1 [_ [_ [H2 _]]]]]; auto.
  - destruct H as [H1 H2]; split; [apply IHp1|apply IHp2]; assumption.
  - destruct H as [H1 H2]; split; [apply IHp1|apply IHp2]; assumption.
  - apply IHp; assumption.
Qed.

Lemma qualifier_subst_fv_empty : forall x s p,
  qualifier_fv_empty p -> qualifier_subst x s p = p.
Proof.
  intros x s p; induction p; simpl; intros H; try reflexivity.
  - destruct H as [H1 H2]; unfold qualifier_subst; simpl.
    rewrite !tm_subst_fv_empty; auto.
  - destruct H as [H1 H2]; unfold qualifier_subst; simpl.
    rewrite !tm_subst_fv_empty; auto.
  - destruct H as [H1 H2]; unfold qualifier_subst; simpl.
    rewrite !tm_subst_fv_empty; auto.
  - destruct H as [H1 H2]; rewrite IHp1, IHp2; auto.
  - destruct H as [H1 H2]; rewrite IHp1, IHp2; auto.
  - rewrite IHp; auto.
Qed.

Lemma qualifier_subst_notin_fv : forall x s p,
  ~ In x (qualifier_fv p) -> qualifier_subst x s p = p.
Proof.
  intros x s p; induction p; simpl; intro H; try reflexivity.
  - assert (H1 : ~ In x (fv_tm t)) by
      (intro Hin; apply H; apply in_or_app; left; exact Hin).
    assert (H2 : ~ In x (fv_tm t0)) by
      (intro Hin; apply H; apply in_or_app; right; exact Hin).
    unfold qualifier_subst; simpl; rewrite !tm_subst_notin_fv; auto.
  - assert (H1 : ~ In x (fv_tm t)) by
      (intro Hin; apply H; apply in_or_app; left; exact Hin).
    assert (H2 : ~ In x (fv_tm t0)) by
      (intro Hin; apply H; apply in_or_app; right; exact Hin).
    unfold qualifier_subst; simpl; rewrite !tm_subst_notin_fv; auto.
  - assert (H1 : ~ In x (fv_tm t)) by
      (intro Hin; apply H; apply in_or_app; left; exact Hin).
    assert (H2 : ~ In x (fv_tm t0)) by
      (intro Hin; apply H; apply in_or_app; right; exact Hin).
    unfold qualifier_subst; simpl; rewrite !tm_subst_notin_fv; auto.
  - assert (H1 : ~ In x (qualifier_fv p1)) by
      (intro Hin; apply H; apply in_or_app; left; exact Hin).
    assert (H2 : ~ In x (qualifier_fv p2)) by
      (intro Hin; apply H; apply in_or_app; right; exact Hin).
    rewrite IHp1, IHp2; auto.
  - assert (H1 : ~ In x (qualifier_fv p1)) by
      (intro Hin; apply H; apply in_or_app; left; exact Hin).
    assert (H2 : ~ In x (qualifier_fv p2)) by
      (intro Hin; apply H; apply in_or_app; right; exact Hin).
    rewrite IHp1, IHp2; auto.
  - f_equal; apply IHp; exact H.
Qed.

Lemma qualifier_substitute_many_fv_empty : forall theta p,
  qualifier_fv_empty p -> qualifier_substitute_many theta p = p.
Proof.
  induction theta as [|[x s] theta IH]; intros p Hclosed; simpl; auto.
  rewrite qualifier_subst_fv_empty; [apply IH; exact Hclosed|exact Hclosed].
Qed.

Lemma qualifier_substitute_many_notin_fv : forall theta p,
  (forall x s, In (x,s) theta -> ~ In x (qualifier_fv p)) ->
  qualifier_substitute_many theta p = p.
Proof.
  induction theta as [|[x s] theta IH]; intros p Hfresh; simpl; [reflexivity|].
  rewrite qualifier_subst_notin_fv.
  - apply IH; intros y v Hin; apply (Hfresh y v); simpl; auto.
  - apply (Hfresh x s); simpl; auto.
Qed.

Lemma subst_many_fixed : forall theta t,
  fv_tm t = [] -> subst_many theta t = t.
Proof.
  induction theta as [|[x s] theta IH]; intros t Hfv; simpl; auto.
  rewrite tm_subst_fv_empty by exact Hfv; apply IH; exact Hfv.
Qed.

Lemma lookup_value_substitution_some_in : forall theta x v,
  lookup_value_substitution x theta = Some v -> In (x,v) theta.
Proof.
  induction theta as [|[y w] theta IH]; intros x v H; simpl in H; [discriminate|].
  destruct (Nat.eqb x y) eqn:Heq.
  - apply Nat.eqb_eq in Heq; subst x; inversion H; subst v; left; reflexivity.
  - right; eapply IH; exact H.
Qed.

Lemma subst_many_open_lookup : forall theta x w t,
  closed_substitution theta ->
  lookup_value_substitution x theta = Some w ->
  subst_many theta (open_tm t (tm_fvar x)) =
  subst_many theta (open_tm t w).
Proof.
  induction theta as [|[y s] theta IH]; intros x w t Hclosed Hlookup; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:Heq.
    + apply Nat.eqb_eq in Heq; subst y.
      inversion Hlookup; subst w.
      assert (HsLC : locally_closed_tm s).
      { pose proof (Hclosed x s (or_introl eq_refl)) as [Hvs _].
        eapply value_locally_closed_tm; exact Hvs. }
      unfold open_tm at 1 2.
      rewrite tm_subst_open_tm_rec with (k:=0) (u:=tm_fvar x) by exact HsLC.
      cbn [tm_subst]. rewrite Nat.eqb_refl.
      rewrite tm_subst_open_tm_rec with (k:=0) (u:=s) by exact HsLC.
      assert (Hss : tm_subst x s s = s).
      { apply tm_subst_fv_empty.
        destruct (Hclosed x s (or_introl eq_refl)) as [_ [Hfv _]]; exact Hfv. }
      rewrite Hss; reflexivity.
    + assert (Htail : lookup_value_substitution x theta = Some w).
      { exact Hlookup. }
      assert (HsLC : locally_closed_tm s).
      { pose proof (Hclosed y s (or_introl eq_refl)) as [Hvs _].
        eapply value_locally_closed_tm; exact Hvs. }
      unfold open_tm at 1 2.
      rewrite tm_subst_open_tm_rec with (k:=0) (u:=tm_fvar x) by exact HsLC.
      pose proof (lookup_value_substitution_some_in _ _ _ Hlookup) as Hmem.
      assert (Hsw : tm_subst y s w = w).
      { eapply tm_subst_fv_empty. destruct (Hclosed x w (or_intror Hmem)) as [_ [Hfv _]]; exact Hfv. }
      rewrite tm_subst_open_tm_rec with (k:=0) (u:=w) by exact HsLC.
      rewrite Hsw.
      cbn [tm_subst].
      assert (Eyx : (y =? x) = false) by (rewrite Nat.eqb_sym; exact Heq).
      rewrite Eyx.
      apply IH.
      * intros z v Hin; apply (Hclosed z v); simpl; auto.
      * exact Htail.
Qed.

Lemma qualifier_substitute_many_open_lookup : forall theta x w p,
  closed_substitution theta ->
  lookup_value_substitution x theta = Some w ->
  qualifier_substitute_many theta (open_qualifier_tm p (tm_fvar x)) =
  qualifier_substitute_many theta (open_qualifier_tm p w).
Proof.
  intros theta x w p Hclosed Hlookup.
  rewrite !qualifier_substitute_many_map.
  induction p; simpl; try reflexivity.
  - f_equal; [apply subst_many_open_lookup|apply subst_many_open_lookup]; assumption.
  - f_equal; [apply subst_many_open_lookup|apply subst_many_open_lookup]; assumption.
  - f_equal; [apply subst_many_open_lookup|apply subst_many_open_lookup]; assumption.
  - f_equal; [apply IHp1|apply IHp2].
  - f_equal; [apply IHp1|apply IHp2].
  - f_equal; apply IHp.
Qed.

Lemma subst_many_fvar : forall theta x,
  (forall y s, In (y, s) theta -> fv_tm s = []) ->
  subst_many theta (tm_fvar x) =
    match lookup_value_substitution x theta with
    | Some v => v
    | None => tm_fvar x
    end.
Proof.
  induction theta as [|[y s] theta IH]; intros x Hclosed; simpl.
  - reflexivity.
  - destruct (Nat.eqb y x) eqn:Heq.
    + apply Nat.eqb_eq in Heq; subst y.
      rewrite subst_many_fixed.
      * cbn [lookup_value_substitution]; rewrite Nat.eqb_refl; reflexivity.
      * eapply Hclosed; simpl; auto.
    + rewrite IH.
      * rewrite Nat.eqb_sym, Heq; reflexivity.
      * intros z w Hin. apply (Hclosed z w). simpl; auto.
Qed.

Lemma subst_many_open_fresh : forall theta x s t,
  locally_closed_tm s -> ~ In x (fv_tm t) ->
  subst_many ((x,s)::theta) (open_tm t (tm_fvar x)) =
  subst_many theta (open_tm t s).
Proof.
  intros theta x s t Hlc Hfresh.
  cbn [subst_many].
  unfold open_tm.
  rewrite tm_subst_open_tm_rec with (k:=0) (u:=tm_fvar x); [|exact Hlc].
  cbn [tm_subst].
  rewrite (tm_subst_notin_fv x s t Hfresh).
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

Lemma lookup_value_substitution_app_no_key : forall ext theta x,
  (forall y v, In (y,v) ext -> y <> x) ->
  lookup_value_substitution x (ext ++ theta) =
    lookup_value_substitution x theta.
Proof.
  induction ext as [|[y w] ext IH]; intros theta x Hfresh; simpl.
  - reflexivity.
  - assert (Hy : (x =? y) = false).
    { apply Nat.eqb_neq; intro Heq; subst y.
      eapply Hfresh; simpl; eauto. }
    rewrite Hy; apply IH; intros z s Hin; apply (Hfresh z s); simpl; auto.
Qed.

Lemma lookup_value_substitution_some_key : forall theta x v,
  lookup_value_substitution x theta = Some v -> In x (map fst theta).
Proof.
  induction theta as [|[y w] theta IH]; intros x v H; simpl in H; [discriminate|].
  destruct (Nat.eqb x y) eqn:Heq.
  - apply Nat.eqb_eq in Heq; subst x; simpl; auto.
  - right; eapply IH; exact H.
Qed.

Definition context_interpretation (Delta : ty_context) (RGamma : rcontext)
    (theta : list (atom * tm)) : Prop :=
  closed_substitution theta /\
  forall x R, lookup_rcontext x RGamma = Some R ->
    exists v, lookup_value_substitution x theta = Some v /\ rvalue Delta theta R v.

Definition context_interpretation_at (n : nat) (Delta : ty_context)
    (RGamma : rcontext) (theta : list (atom * tm)) : Prop :=
  closed_substitution theta /\
  forall x R, lookup_rcontext x RGamma = Some R ->
    exists v, lookup_value_substitution x theta = Some v /\
              rvalue_n n Delta theta R v.

Lemma empty_context_interpretation_at : forall n,
  context_interpretation_at n [] [] [].
Proof.
  intros n; split.
  - intros x v Hin; inversion Hin.
  - intros x R Hlookup; discriminate.
Qed.

Lemma context_interpretation_at_extend : forall n Delta RGamma theta ext,
  context_interpretation_at n Delta RGamma theta ->
  closed_substitution ext ->
  (forall x v, In (x,v) ext -> ~ In x (map fst theta)) ->
  (forall x v, In (x,v) ext ->
    forall y R, lookup_rcontext y RGamma = Some R ->
      ~ In x (rty_term_fv R)) ->
  context_interpretation_at n Delta RGamma (ext ++ theta).
Proof.
  intros n Delta RGamma theta ext [Hclosed Hint] Hext Hkeys Hfresh.
  split.
  - intros x v Hin; apply in_app_iff in Hin; destruct Hin as [Hin|Hin].
    + eapply Hext; eauto.
    + eapply Hclosed; eauto.
  - intros y R Hlookup.
    destruct (Hint y R Hlookup) as [v [Hv Hrv]].
    exists v; split.
    + rewrite lookup_value_substitution_app_no_key; [exact Hv|].
      intros z s Hin Hz.
      pose proof (lookup_value_substitution_some_key _ _ _ Hv) as Hy.
      subst z; apply (Hkeys y s Hin); exact Hy.
    + intros ext' Hext' Hdom'.
      specialize (Hrv (ext' ++ ext)).
      assert (Hboth : closed_substitution (ext' ++ ext)).
      { intros z s Hin; apply in_app_iff in Hin; destruct Hin as [Hin|Hin];
          [eapply Hext'|eapply Hext]; eauto. }
      assert (Hbothdom : forall z s, In (z,s) (ext' ++ ext) ->
          ~ In z (map fst theta)).
      { intros z s Hin; apply in_app_iff in Hin; destruct Hin as [Hin|Hin].
        - intro Hz; apply (Hdom' z s Hin); rewrite map_app; apply in_app_iff; right; exact Hz.
        - eapply Hkeys; eauto. }
      specialize (Hrv Hboth Hbothdom).
      rewrite <- app_assoc in Hrv; exact Hrv.
Qed.

Lemma rvalue_sem_value : forall R v,
  forall Delta theta, rvalue Delta theta R v -> sem_value v.
Proof.
  intros R v Delta theta H.
  specialize (H 1 [] (ltac:(intros x s Hin; inversion Hin))
    (ltac:(intros x s Hin; inversion Hin))).
  destruct R; simpl in H; tauto.
Qed.

Lemma rvalue_n_sem_value : forall n Delta theta R v,
  rvalue_n (S n) Delta theta R v -> sem_value v.
Proof.
  intros n Delta theta R v H.
  specialize (H [] (ltac:(intros x s Hin; inversion Hin))
    (ltac:(intros x s Hin; inversion Hin))).
  simpl in H; destruct R; simpl in H; tauto.
Qed.

Lemma rvalue_n_zero_core : forall Delta theta R v,
  rvalue_n 0 Delta theta R v ->
  has_type Delta [] v (erase R) /\ sem_value v.
Proof.
  intros Delta theta R v H.
  specialize (H [] (ltac:(intros x s Hin; inversion Hin))
    (ltac:(intros x s Hin; inversion Hin))).
  exact H.
Qed.

Lemma rvalue_nonzero_int : forall Delta v,
  forall theta, rvalue Delta theta (R_Refine Ty_Int (Pred_Ne (tm_bvar 0) (tm_int 0%Z))) v ->
  exists m, v = tm_int m /\ m <> 0%Z.
Proof.
  intros Delta v theta Hrv.
  specialize (Hrv 1 [] (ltac:(intros x s Hin; inversion Hin))
    (ltac:(intros x s Hin; inversion Hin))).
  cbn [rvalue_n] in Hrv.
  destruct Hrv as [_ [Hv [Hcanonical Hne]]].
  destruct (Hcanonical eq_refl) as [m Hm]; subst v.
  change (predicate_holds
    (qualifier_substitute_many theta (Pred_Ne (tm_int m) (tm_int 0%Z)))) in Hne.
  rewrite qualifier_substitute_many_fv_empty in Hne by (simpl; auto).
  exists m; split; [reflexivity|].
  eapply nonzero_observation; eauto using multi_refl.
Qed.

Lemma rvalue_n_nonzero_int : forall n Delta v theta,
  rvalue_n (S n) Delta theta
    (R_Refine Ty_Int (Pred_Ne (tm_bvar 0) (tm_int 0%Z))) v ->
  exists m, v = tm_int m /\ m <> 0%Z.
Proof.
  intros n Delta v theta Hrv.
  specialize (Hrv [] (ltac:(intros x s Hin; inversion Hin))
    (ltac:(intros x s Hin; inversion Hin))).
  cbn [rvalue_core] in Hrv.
  destruct Hrv as [_ [Hv [Hcanonical Hne]]].
  destruct (Hcanonical eq_refl) as [m Hm]; subst v.
  change (predicate_holds
    (qualifier_substitute_many theta (Pred_Ne (tm_int m) (tm_int 0%Z)))) in Hne.
  rewrite qualifier_substitute_many_fv_empty in Hne by (simpl; auto).
  exists m; split; [reflexivity|].
  eapply nonzero_observation; eauto using multi_refl.
Qed.

Lemma rvalue_n_refine_predicate : forall n Delta theta T p v,
  rvalue_n (S n) Delta theta (R_Refine T p) v ->
  predicate_holds (qualifier_substitute_many theta (open_qualifier_tm p v)).
Proof.
  intros n Delta theta T p v Hrv.
  specialize (Hrv [] (ltac:(intros x s Hin; inversion Hin))
    (ltac:(intros x s Hin; inversion Hin))).
  simpl in Hrv.
  exact (proj2 (proj2 (proj2 Hrv))).
Qed.

Lemma qualifier_substitute_many_true : forall theta,
  qualifier_substitute_many theta Pred_True = Pred_True.
Proof. induction theta as [|[x s] theta IH]; simpl; auto. Qed.

Lemma rvalue_n_refine_true : forall n Delta theta T p v,
  rvalue_n (S n) Delta theta (R_Refine T p) v ->
  rvalue_n (S n) Delta theta (R_Refine T Pred_True) v.
Proof.
  intros n Delta theta T p v Hrv ext Hext Hdom.
  specialize (Hrv ext Hext Hdom).
  cbn [rvalue_core] in *.
  destruct Hrv as [Hty [Hsv [Hcan _]]].
  split; [exact Hty|].
  split; [exact Hsv|].
  split; [exact Hcan|].
  rewrite qualifier_substitute_many_true.
  unfold predicate_holds; simpl; exact I.
Qed.

Lemma qualifier_substitute_many_false : forall theta,
  qualifier_substitute_many theta Pred_False = Pred_False.
Proof. induction theta as [|[x s] theta IH]; simpl; auto. Qed.

Lemma entails_sound : forall Delta RGamma p q,
  entails Delta RGamma p q -> forall n theta,
  context_interpretation_at (S n) Delta RGamma theta ->
  predicate_holds (qualifier_substitute_many theta p) ->
  predicate_holds (qualifier_substitute_many theta q).
Proof.
  intros Delta RGamma p q Hent; induction Hent; intros n theta Hci Hsrc.
  all: rewrite !qualifier_substitute_many_map in *; simpl in *.
  - exact Hsrc.
  - unfold predicate_holds; simpl; exact I.
  - rewrite <- qualifier_substitute_many_map in Hsrc.
    rewrite <- qualifier_substitute_many_map.
    apply IHHent2 with (n:=n) (theta:=theta); [exact Hci|].
    apply IHHent1 with (n:=n) (theta:=theta); [exact Hci|].
    exact Hsrc.
  - unfold predicate_holds in *; simpl in *; exact (proj1 Hsrc).
  - unfold predicate_holds in *; simpl in *; exact (proj2 Hsrc).
  - unfold predicate_holds in *; simpl in *.
    rewrite <- qualifier_substitute_many_map in Hsrc.
    split.
    + rewrite <- qualifier_substitute_many_map.
      apply IHHent1 with (n:=n) (theta:=theta); [exact Hci|].
      exact Hsrc.
    + rewrite <- qualifier_substitute_many_map.
      apply IHHent2 with (n:=n) (theta:=theta); [exact Hci|].
      exact Hsrc.
  - unfold predicate_holds in *; simpl in *; left; exact Hsrc.
  - unfold predicate_holds in *; simpl in *; right; exact Hsrc.
  - unfold predicate_holds in *; cbn [qualifier_map_subst_many] in *; simpl in Hsrc.
    rewrite <- qualifier_substitute_many_map.
    destruct Hsrc as [Hp|Hq].
    + rewrite <- qualifier_substitute_many_map in Hp.
      eapply IHHent1; eauto.
    + rewrite <- qualifier_substitute_many_map in Hq.
      eapply IHHent2; eauto.
  - intros Hnotq.
    rewrite <- qualifier_substitute_many_map in Hsrc, Hnotq.
    assert (Hand : predicate_holds (qualifier_substitute_many theta (Pred_And p q))).
    { rewrite qualifier_substitute_many_map; unfold predicate_holds; simpl.
      rewrite qualifier_substitute_many_map in Hsrc, Hnotq.
      split; [exact Hsrc|].
      exact Hnotq. }
    pose proof (IHHent n theta Hci Hand) as Hfalse.
    rewrite qualifier_substitute_many_false in Hfalse.
    unfold predicate_holds in Hfalse; simpl in Hfalse; exact Hfalse.
  - destruct Hsrc as [Hp Hnp]; contradiction.
  - destruct (proj2 Hci x (R_Refine T p) H) as [v [Hv Hrv]].
    rewrite <- qualifier_substitute_many_map.
    rewrite (qualifier_substitute_many_open_lookup theta x v p (proj1 Hci) Hv).
    eapply rvalue_n_refine_predicate; exact Hrv.
  - contradiction.
Qed.

Lemma rvalue_integer_literal : forall Delta n,
  forall theta, rvalue Delta theta
    (R_Refine Ty_Int (Pred_Eq (tm_bvar 0) (tm_int n))) (tm_int n).
Proof.
  intros Delta n theta k ext Hext Hdom; destruct k as [|k]; simpl.
  - split.
    + constructor.
    + split; [constructor|split; reflexivity].
  - split; [constructor|].
    split.
    + split; [constructor|split; reflexivity].
    + split; [intros _; exists n; reflexivity|].
      change (predicate_holds
        (qualifier_substitute_many (ext ++ theta) (Pred_Eq (tm_int n) (tm_int n)))).
      rewrite qualifier_substitute_many_fv_empty by (simpl; auto).
      apply value_equality_holds; constructor.
Qed.

Lemma lookup_value_substitution_app_fresh : forall theta x v,
  (forall y w, In (y,w) theta -> y <> x) ->
  lookup_value_substitution x (theta ++ [(x,v)]) = Some v.
Proof.
  induction theta as [|[y w] theta IH]; intros x v Hfresh; simpl.
  - rewrite Nat.eqb_refl; reflexivity.
  - assert (Hy : y <> x) by (intro E; subst; eapply Hfresh; simpl; auto).
    assert (E : (x =? y) = false) by (apply Nat.eqb_neq; congruence).
    rewrite E.
    apply IH; intros z s Hin; apply (Hfresh z s); simpl; right; exact Hin.
Qed.

Lemma lookup_value_substitution_app_other : forall theta x v y,
  y <> x ->
  lookup_value_substitution y (theta ++ [(x,v)]) =
    lookup_value_substitution y theta.
Proof.
  induction theta as [|[z w] theta IH]; intros x v y Hneq; simpl.
  - destruct (Nat.eqb y x) eqn:E; [apply Nat.eqb_eq in E; contradiction|reflexivity].
  - destruct (Nat.eqb y z); [reflexivity|apply IH; exact Hneq].
Qed.

Lemma context_interpretation_update : forall Delta RGamma theta x R v,
  context_interpretation Delta RGamma theta ->
  rvalue Delta theta R v ->
  ~ In x (rty_term_fv R) ->
  ~ In x (map fst theta) ->
  (forall y S, lookup_rcontext y RGamma = Some S -> ~ In x (rty_term_fv S)) ->
  context_interpretation Delta (update_rcontext RGamma x R) ((x,v)::theta).
Proof.
  intros Delta RGamma theta x R v [Hclosed Hint] Hrv HfreshR Hkey HfreshCtx.
  pose proof (rvalue_sem_value R v Delta theta Hrv) as Hsv.
  split.
  - intros y w Hin; simpl in Hin; destruct Hin as [Hin|Hin].
    + inversion Hin; subst; exact Hsv.
    + apply Hclosed with (x:=y); exact Hin.
  - intros y S Hlookup.
    simpl in Hlookup.
    destruct (Nat.eqb y x) eqn:Heq.
    + apply Nat.eqb_eq in Heq; subst y. inversion Hlookup; subst S.
      exists v; split; [simpl; rewrite Nat.eqb_refl; reflexivity|].
      intros n ext Hext Hdom.
      specialize (Hrv n (ext ++ [(x,v)])).
      assert (Hext' : closed_substitution (ext ++ [(x,v)])).
      { intros z s Hin; apply in_app_iff in Hin; destruct Hin as [Hin|Hin].
        - eapply Hext; eauto.
        - simpl in Hin; destruct Hin as [Hin|[]]; inversion Hin; subst.
          exact Hsv. }
      assert (Hdom' : forall z s, In (z,s) (ext ++ [(x,v)]) ->
          ~ In z (map fst theta)).
      { intros z s Hin; apply in_app_iff in Hin; destruct Hin as [Hin|Hin].
        - intro Hz; apply (Hdom z s Hin); simpl; right; exact Hz.
        - simpl in Hin; destruct Hin as [Hin|[]]; inversion Hin; subst; exact Hkey. }
      specialize (Hrv Hext' Hdom').
      rewrite <- app_assoc in Hrv; exact Hrv.
    + destruct (Hint y S Hlookup) as [w [Hw Hrw]].
      exists w; split; [simpl; rewrite Heq; exact Hw|].
      intros n ext Hext Hdom.
      specialize (Hrw n (ext ++ [(x,v)])).
      assert (Hext' : closed_substitution (ext ++ [(x,v)])).
      { intros z s Hin; apply in_app_iff in Hin; destruct Hin as [Hin|Hin].
        - eapply Hext; eauto.
        - simpl in Hin; destruct Hin as [Hin|[]]; inversion Hin; subst.
          exact Hsv. }
      assert (Hdom' : forall z s, In (z,s) (ext ++ [(x,v)]) ->
          ~ In z (map fst theta)).
      { intros z s Hin; apply in_app_iff in Hin; destruct Hin as [Hin|Hin].
        - intro Hz; apply (Hdom z s Hin); simpl; right; exact Hz.
        - simpl in Hin; destruct Hin as [Hin|[]]; inversion Hin; subst; exact Hkey. }
      specialize (Hrw Hext' Hdom').
      rewrite <- app_assoc in Hrw; exact Hrw.
Qed.

Lemma context_interpretation_at_update : forall n Delta RGamma theta x R v,
  context_interpretation_at (S n) Delta RGamma theta ->
  rvalue_n (S n) Delta theta R v ->
  ~ In x (rty_term_fv R) ->
  ~ In x (map fst theta) ->
  (forall y S, lookup_rcontext y RGamma = Some S -> ~ In x (rty_term_fv S)) ->
  context_interpretation_at (S n) Delta (update_rcontext RGamma x R)
    ((x,v)::theta).
Proof.
  intros n Delta RGamma theta x R v [Hclosed Hint] Hrv HfreshR Hkey HfreshCtx.
  pose proof (rvalue_n_sem_value n Delta theta R v Hrv) as Hsv.
  split.
  - intros y w Hin; simpl in Hin; destruct Hin as [Hin|Hin].
    + inversion Hin; subst; exact Hsv.
    + apply Hclosed with (x:=y); exact Hin.
  - intros y S Hlookup; simpl in Hlookup.
    destruct (Nat.eqb y x) eqn:Heq.
    + apply Nat.eqb_eq in Heq; subst y; inversion Hlookup; subst S.
      exists v; split; [simpl; rewrite Nat.eqb_refl; reflexivity|].
      intros ext Hext Hdom.
      specialize (Hrv (ext ++ [(x,v)])).
      assert (Hext' : closed_substitution (ext ++ [(x,v)])).
      { intros z s Hin; apply in_app_iff in Hin; destruct Hin as [Hin|Hin].
        - eapply Hext; eauto.
        - simpl in Hin; destruct Hin as [Hin|[]]; inversion Hin; subst.
          exact Hsv. }
      assert (Hdom' : forall z s, In (z,s) (ext ++ [(x,v)]) ->
          ~ In z (map fst theta)).
      { intros z s Hin; apply in_app_iff in Hin; destruct Hin as [Hin|Hin].
        - intro Hz; apply (Hdom z s Hin); simpl; right; exact Hz.
        - simpl in Hin; destruct Hin as [Hin|[]]; inversion Hin; subst; exact Hkey. }
      specialize (Hrv Hext' Hdom').
      rewrite <- app_assoc in Hrv; exact Hrv.
    + destruct (Hint y S Hlookup) as [w [Hw Hrw]].
      exists w; split; [simpl; rewrite Heq; exact Hw|].
      intros ext Hext Hdom.
      specialize (Hrw (ext ++ [(x,v)])).
      assert (Hext' : closed_substitution (ext ++ [(x,v)])).
      { intros z s Hin; apply in_app_iff in Hin; destruct Hin as [Hin|Hin].
        - eapply Hext; eauto.
        - simpl in Hin; destruct Hin as [Hin|[]]; inversion Hin; subst.
          exact Hsv. }
      assert (Hdom' : forall z s, In (z,s) (ext ++ [(x,v)]) ->
          ~ In z (map fst theta)).
      { intros z s Hin; apply in_app_iff in Hin; destruct Hin as [Hin|Hin].
        - intro Hz; apply (Hdom z s Hin); simpl; right; exact Hz.
        - simpl in Hin; destruct Hin as [Hin|[]]; inversion Hin; subst; exact Hkey. }
      specialize (Hrw Hext' Hdom').
      rewrite <- app_assoc in Hrw; exact Hrw.
Qed.



Lemma reducible_progress : forall R t u,
  forall Delta theta, reducible Delta theta R t -> multi t u ->
  value u \/ exists u', u --> u'.
Proof.
  intros R t u Delta theta Hred Hrun.
  destruct (Hred u Hrun) as [v [Huv [Hv _]]].
  inversion Huv; subst.
  - left; exact Hv.
  - right; eauto.
Qed.

Lemma reducible_at_progress : forall n R t u,
  forall Delta theta, reducible_at n Delta theta R t ->
  multi (subst_many theta t) u -> value u \/ exists u', u --> u'.
Proof.
  intros n R t u Delta theta Hred Hrun.
  destruct (Hred u Hrun) as [v [Huv [Hv _]]].
  inversion Huv; subst.
  - left; exact Hv.
  - right; eauto.
Qed.

Lemma value_multi_stays : forall v u, value v -> multi v u -> u = v.
Proof.
  intros v u Hv H; induction H.
  - reflexivity.
  - exfalso; eapply value_no_step; eauto.
Qed.

Lemma subst_many_int : forall theta z,
  subst_many theta (tm_int z) = tm_int z.
Proof. induction theta as [|[x s] theta IH]; intros; simpl; auto. Qed.

Lemma reducible_at_integer_literal : forall Delta theta z n,
  reducible_at (S n) Delta theta
    (R_Refine Ty_Int (Pred_Eq (tm_bvar 0) (tm_int z))) (tm_int z).
Proof.
  intros Delta theta z n u Hrun.
  assert (Hu : u = tm_int z).
  { rewrite subst_many_int in Hrun.
    eapply value_multi_stays; [constructor|exact Hrun]. }
  subst u; exists (tm_int z); split; [constructor|].
  split; [constructor|].
  eapply rvalue_integer_literal.
Qed.

Lemma fresh_notin_app : forall L1 L2, ~ In (fresh (L1 ++ L2)) (L1 ++ L2).
Proof. intros; apply fresh_notin. Qed.

Scheme has_rtype_ind_mut := Induction for has_rtype Sort Prop
with subtype_ind_mut := Induction for subtype Sort Prop.
Combined Scheme rtyping_subtyping_mutind from has_rtype_ind_mut, subtype_ind_mut.

Lemma variable_reducible_at : forall n Delta RGamma x R theta,
  lookup_rcontext x RGamma = Some R ->
  context_interpretation Delta RGamma theta ->
  reducible_at (S n) Delta theta R (tm_fvar x).
Proof.
  intros n Delta RGamma x R theta Hlookup [Hclosed Hint] u Hrun.
  destruct (Hint x R Hlookup) as [v [Hfind Hrv]].
  assert (Hsubst : forall y s, In (y,s) theta -> fv_tm s = []).
  { intros y s Hin; destruct (Hclosed y s Hin) as [_ [Hfv _]]; exact Hfv. }
  rewrite (subst_many_fvar theta x Hsubst) in Hrun.
  rewrite Hfind in Hrun.
  pose proof (rvalue_sem_value R v Delta theta Hrv) as [Hv _].
  assert (Hu : u = v) by (eapply value_multi_stays; eauto).
  subst u; exists v; split; [apply multi_refl|].
  split; [exact Hv|].
  apply Hrv.
Qed.

Lemma subtype_refl_fundamental : forall n Delta RGamma R theta v,
  context_interpretation Delta RGamma theta ->
  rvalue_n (S n) Delta theta R v ->
  rvalue_n (S n) Delta theta R v.
Proof. auto. Qed.

Lemma subtype_trans_fundamental : forall n Delta R Mid U theta v,
  (rvalue_n (S n) Delta theta R v -> rvalue_n (S n) Delta theta Mid v) ->
  (rvalue_n (S n) Delta theta Mid v -> rvalue_n (S n) Delta theta U v) ->
  rvalue_n (S n) Delta theta R v -> rvalue_n (S n) Delta theta U v.
Proof. intros; eauto. Qed.

Lemma subtype_erasure_equality : forall Delta RGamma R U,
  subtype Delta RGamma R U -> erase R = erase U.
Proof.
  intros Delta RGamma R U Hsub.
  assert (Hmut :
    (forall Delta RGamma t R (H : has_rtype Delta RGamma t R), True) /\
    (forall Delta RGamma R U (H : subtype Delta RGamma R U), erase R = erase U)).
  { apply (rtyping_subtyping_mutind
      (fun _ _ _ _ _ => True)
      (fun _ _ R U _ => erase R = erase U));
      intros; simpl in *; try exact I; try reflexivity; try congruence.
    - (* function *)
      Show.
      rewrite erase_open_rty_tm in H0.
      rewrite erase_open_rty_tm in H0.
      congruence.
    - (* witness *)
      rewrite erase_open_rty_tm in H.
      symmetry; exact H.
    - (* existential bind *)
      rewrite erase_open_rty_tm in H.
      exact H.
    - (* transitivity *) congruence.
  }
  destruct Hmut as [_ Hmut].
  exact (Hmut Delta RGamma R U Hsub).
Qed.

Theorem never_stuck : forall (t t' : tm) (R : rty),
  has_rtype [] empty_rcontext t R ->
  multi t t' ->
  value t' \/ exists t'' : tm, t' --> t''.
Proof.

Qed.

End SystemFRefinementTask.
