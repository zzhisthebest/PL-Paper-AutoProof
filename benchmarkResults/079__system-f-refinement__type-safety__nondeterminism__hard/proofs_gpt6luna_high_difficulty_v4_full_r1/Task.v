From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
From Stdlib Require Import ZArith.BinInt.

Module SystemFRefinementNonDeterminism.

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
  | tm_arith : integer_operator -> tm -> tm -> tm
  | tm_choice : tm -> tm -> tm.

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
  | tm_choice t1 t2 => tm_choice (open_tm_rec k u t1) (open_tm_rec k u t2)
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
  | tm_choice t1 t2 => fv_tm t1 ++ fv_tm t2
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
  | tm_choice t1 t2 => ftv_tm t1 ++ ftv_tm t2
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
  | tm_choice t1 t2 => tm_choice (open_tm_ty_rec k U t1) (open_tm_ty_rec k U t2)
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
  | tm_choice t1 t2 => tm_choice (tm_ty_subst X U t1) (tm_ty_subst X U t2)
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
  | tm_choice t1 t2 => tm_choice (tm_subst x s t1) (tm_subst x s t2)
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
      lc_tm_at K k (tm_arith op t1 t2)
  | lc_tm_choice : forall K k t1 t2,
      lc_tm_at K k t1 -> lc_tm_at K k t2 -> lc_tm_at K k (tm_choice t1 t2).

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
  | ST_ChoiceLeft : forall t1 t2,
      locally_closed_tm t1 -> locally_closed_tm t2 ->
      tm_choice t1 t2 --> t1
  | ST_ChoiceRight : forall t1 t2,
      locally_closed_tm t1 -> locally_closed_tm t2 ->
      tm_choice t1 t2 --> t2
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
      has_type Delta Gamma (tm_arith op t1 t2) Ty_Int
  | T_Choice : forall Delta Gamma t1 t2 T,
      has_type Delta Gamma t1 T -> has_type Delta Gamma t2 T ->
      has_type Delta Gamma (tm_choice t1 t2) T.

Fixpoint max_atom (L : list atom) : atom :=
  match L with
  | [] => 0
  | x :: L' => Nat.max x (max_atom L')
  end.

Definition fresh (L : list atom) : atom := S (max_atom L).

End SystemFRefinementNonDeterminism.

From Stdlib Require Import Arith.PeanoNat Lists.List ZArith.BinInt.
Module SystemFRefinementNonDeterminismLogic.
Import ListNotations SystemFRefinementNonDeterminism.

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
      predicate_multistep t2 (tm_int n2) /\ (n1 < n2)%Z /\
      (forall m1 m2 : Z,
        predicate_multistep t1 (tm_int m1) ->
        predicate_multistep t2 (tm_int m2) -> (m1 < m2)%Z);
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

End SystemFRefinementNonDeterminismLogic.

From Stdlib Require Import Arith.PeanoNat Lists.List Lia ZArith.BinInt.
From Stdlib Require Import Program.Equality.
From Stdlib Require Import Program.Wf.
From Stdlib Require Import Arith.Wf_nat.
Module SystemFRefinementNonDeterminismTyping.
Import ListNotations.
Import SystemFRefinementNonDeterminism.
Export SystemFRefinementNonDeterminismLogic.

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

  | RT_Choice : forall Delta RGamma t1 t2 R,
      has_rtype Delta RGamma t1 R ->
      has_rtype Delta RGamma t2 R ->
      has_rtype Delta RGamma (tm_choice t1 t2) R
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

Scheme has_rtype_subtype_mut_ind := Induction for has_rtype Sort Prop with has_rtype_subtype_ind2 := Induction for subtype Sort Prop.

End SystemFRefinementNonDeterminismTyping.


Module SystemFRefinementNonDeterminismEvaluation.
Import ListNotations SystemFRefinementNonDeterminism SystemFRefinementNonDeterminismLogic SystemFRefinementNonDeterminismTyping.

Inductive multi : tm -> tm -> Prop :=
  | multi_refl : forall t, multi t t
  | multi_step : forall t1 t2 t3,
      t1 --> t2 -> multi t2 t3 -> multi t1 t3.
Notation "t '-->*' u" := (multi t u) (at level 40).

End SystemFRefinementNonDeterminismEvaluation.

Module SystemFRefinementNonDeterminismTask.
Import ListNotations SystemFRefinementNonDeterminism SystemFRefinementNonDeterminismLogic SystemFRefinementNonDeterminismTyping SystemFRefinementNonDeterminismEvaluation.

Lemma atom_le_max : forall x L, In x L -> x <= max_atom L.
Proof.
  intros x L; induction L as [|y L IH]; simpl; intros Hin.
  - contradiction.
  - destruct Hin as [->|Hin].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; exact Hin|apply Nat.le_max_r].
Qed.

Lemma fresh_not_in : forall L, ~ In (fresh L) L.
Proof.
  intros L Hin.
  unfold fresh in Hin.
  pose proof (atom_le_max (S (max_atom L)) L Hin).
  lia.
Qed.

Lemma tm_subst_open_fvar_rec : forall t k x v,
  ~ In x (fv_tm t) ->
  tm_subst x v (open_tm_rec k (tm_fvar x) t) = open_tm_rec k v t.
Proof.
  induction t; intros k x v Hfresh; simpl in *.
  - destruct (Nat.eqb k n); simpl; try rewrite Nat.eqb_refl; reflexivity.
  - destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E; subst. exfalso; apply Hfresh; simpl; auto.
    + reflexivity.
  - f_equal. eapply IHt; eassumption.
  - f_equal.
    + eapply IHt1; intro Hin; apply Hfresh; apply in_or_app; left; exact Hin.
    + eapply IHt2; intro Hin; apply Hfresh; apply in_or_app; right; exact Hin.
  - f_equal. eapply IHt; eassumption.
  - f_equal. eapply IHt; eassumption.
  - reflexivity.
  - f_equal.
    + eapply IHt1; intro Hin; apply Hfresh; apply in_or_app; left; exact Hin.
    + eapply IHt2; intro Hin; apply Hfresh; apply in_or_app; right; exact Hin.
  - f_equal.
    + eapply IHt1; intro Hin; apply Hfresh; apply in_or_app; left; exact Hin.
    + eapply IHt2; intro Hin; apply Hfresh; apply in_or_app; right; exact Hin.
  - f_equal.
    + eapply IHt1; intro Hin; apply Hfresh; apply in_or_app; left; exact Hin.
    + eapply IHt2; intro Hin; apply Hfresh; apply in_or_app; right; exact Hin.
Qed.

Lemma open_tm_rec_above_lc : forall K d t,
  lc_tm_at K d t -> forall k u, d <= k -> open_tm_rec k u t = t.
Proof.
  intros K d t Hlc. induction Hlc; intros k0 u Hdk; simpl.
  - assert (Nat.eqb k0 i = false) by (apply Nat.eqb_neq; lia). now rewrite H0.
  - reflexivity.
  - f_equal. apply IHHlc. lia.
  - f_equal; [apply IHHlc1|apply IHHlc2]; assumption.
  - f_equal. apply IHHlc. assumption.
  - f_equal. apply IHHlc. assumption.
  - reflexivity.
  - f_equal; [apply IHHlc1|apply IHHlc2]; assumption.
  - f_equal; [apply IHHlc1|apply IHHlc2]; assumption.
  - f_equal; [apply IHHlc1|apply IHHlc2]; assumption.
Qed.

Lemma tm_subst_open_rec_commute : forall t k y s u,
  locally_closed_tm s ->
  tm_subst y s (open_tm_rec k u t) =
  open_tm_rec k (tm_subst y s u) (tm_subst y s t).
Proof.
  induction t; intros k y s u Hlc; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - destruct (Nat.eqb y a) eqn:E; simpl.
    + symmetry. eapply open_tm_rec_above_lc; [exact Hlc|lia].
    + reflexivity.
  - f_equal. eapply IHt; exact Hlc.
  - f_equal; [eapply IHt1|eapply IHt2]; exact Hlc.
  - f_equal. eapply IHt; exact Hlc.
  - f_equal. eapply IHt; exact Hlc.
  - reflexivity.
  - f_equal; [eapply IHt1|eapply IHt2]; exact Hlc.
  - f_equal; [eapply IHt1|eapply IHt2]; exact Hlc.
  - f_equal; [eapply IHt1|eapply IHt2]; exact Hlc.
Qed.

Lemma value_locally_closed : forall v, value v -> locally_closed_tm v.
Proof.
  intros v Hv. inversion Hv; subst; try assumption.
  constructor.
Qed.


Lemma tm_subst_open_fvar_commute_rec : forall t k x y v,
  x <> y -> ~ In x (fv_tm v) -> locally_closed_tm v ->
  tm_subst y v (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k (tm_fvar x) (tm_subst y v t).
Proof.
  induction t; intros k x y v Hxy Hfv Hlc; simpl in *.
  - destruct (Nat.eqb k n); simpl.
    + assert (E : Nat.eqb y x = false) by (apply Nat.eqb_neq; congruence).
      rewrite E; reflexivity.
    + reflexivity.
  - destruct (Nat.eqb x a) eqn:Ex; destruct (Nat.eqb y a) eqn:Ey.
    + apply Nat.eqb_eq in Ex; apply Nat.eqb_eq in Ey; subst; contradiction.
    + apply Nat.eqb_eq in Ex; subst a.
      reflexivity.
    + apply Nat.eqb_eq in Ey; subst a.
      simpl. symmetry. eapply open_tm_rec_above_lc; [exact Hlc|lia].
    + apply Nat.eqb_neq in Ex; apply Nat.eqb_neq in Ey.
      reflexivity.
  - f_equal. eapply IHt; eassumption.
  - f_equal; [eapply IHt1|eapply IHt2]; eassumption.
  - f_equal. eapply IHt; eassumption.
  - f_equal. eapply IHt; eassumption.
  - reflexivity.
  - f_equal; [eapply IHt1|eapply IHt2]; eassumption.
  - f_equal; [eapply IHt1|eapply IHt2]; eassumption.
  - f_equal; [eapply IHt1|eapply IHt2]; eassumption.
Qed.


Fixpoint qualifier_fv (p : qualifier) : list atom :=
  match p with
  | Pred_True | Pred_False => []
  | Pred_Eq t1 t2 | Pred_Lt t1 t2 | Pred_Le t1 t2 => fv_tm t1 ++ fv_tm t2
  | Pred_And p1 p2 | Pred_Or p1 p2 => qualifier_fv p1 ++ qualifier_fv p2
  | Pred_Not p1 => qualifier_fv p1
  end.


Lemma fv_tm_open_closed_incl : forall t k u,
  fv_tm u = [] -> incl (fv_tm (open_tm_rec k u t)) (fv_tm t).
Proof.
  induction t; intros k u Hu x Hx; simpl in *.
  - destruct (Nat.eqb k n); simpl in *; [rewrite Hu in Hx; contradiction|contradiction].
  - destruct Hx as [Hx|[]]; left; exact Hx.
  - apply IHt with (k := S k) (u := u) in Hx; [exact Hx|exact Hu].
  - apply in_app_or in Hx. apply in_or_app. destruct Hx as [Hx|Hx].
    + left. eapply IHt1; eassumption.
    + right. eapply IHt2; eassumption.
  - apply IHt with (k := k) (u := u) in Hx; [exact Hx|exact Hu].
  - apply IHt with (k := k) (u := u) in Hx; [exact Hx|exact Hu].
  - contradiction.
  - apply in_app_or in Hx. apply in_or_app. destruct Hx as [Hx|Hx].
    + left. eapply IHt1; eassumption.
    + right. eapply IHt2; eassumption.
  - apply in_app_or in Hx. apply in_or_app. destruct Hx as [Hx|Hx].
    + left. eapply IHt1; eassumption.
    + right. eapply IHt2; eassumption.
  - apply in_app_or in Hx. apply in_or_app. destruct Hx as [Hx|Hx].
    + left. eapply IHt1; eassumption.
    + right. eapply IHt2; eassumption.
Qed.

Lemma fv_tm_subst_incl : forall t x s,
  incl (fv_tm (tm_subst x s t)) (fv_tm t ++ fv_tm s).
Proof.
  intros t; induction t; intros x s a1 Hmem; simpl in *.
  - contradiction.
  - destruct (Nat.eqb x a) eqn:E; simpl in *.
    + right; exact Hmem.
    + destruct Hmem as [Hmem|[]]. left; exact Hmem.
  - exact (IHt x s a1 Hmem).
  - apply in_app_iff in Hmem. apply in_app_iff.
    destruct Hmem as [Hmem|Hmem].
    + apply in_app_iff in Hmem. destruct Hmem as [Hmem|Hmem].
      * pose proof (IHt1 x s a1 Hmem) as Hinc. apply in_app_iff in Hinc.
        destruct Hinc as [Hterm|Hs].
        -- left; apply in_app_iff; left; exact Hterm.
        -- right; exact Hs.
      * right; exact Hmem.
    + apply in_app_iff in Hmem. destruct Hmem as [Hmem|Hmem].
      * pose proof (IHt2 x s a1 Hmem) as Hinc. apply in_app_iff in Hinc.
        destruct Hinc as [Hterm|Hs].
        -- left; apply in_app_iff; right; exact Hterm.
        -- right; exact Hs.
      * right; exact Hmem.
  - exact (IHt x s a1 Hmem).
  - exact (IHt x s a1 Hmem).
  - contradiction.
  - apply in_app_iff in Hmem. apply in_app_iff.
    destruct Hmem as [Hmem|Hmem].
    + apply in_app_iff in Hmem. destruct Hmem as [Hmem|Hmem].
      * pose proof (IHt1 x s a1 Hmem) as Hinc. apply in_app_iff in Hinc.
        destruct Hinc as [Hterm|Hs].
        -- left; apply in_app_iff; left; exact Hterm.
        -- right; exact Hs.
      * right; exact Hmem.
    + apply in_app_iff in Hmem. destruct Hmem as [Hmem|Hmem].
      * pose proof (IHt2 x s a1 Hmem) as Hinc. apply in_app_iff in Hinc.
        destruct Hinc as [Hterm|Hs].
        -- left; apply in_app_iff; right; exact Hterm.
        -- right; exact Hs.
      * right; exact Hmem.
  - apply in_app_iff in Hmem. apply in_app_iff.
    destruct Hmem as [Hmem|Hmem].
    + apply in_app_iff in Hmem. destruct Hmem as [Hmem|Hmem].
      * pose proof (IHt1 x s a1 Hmem) as Hinc. apply in_app_iff in Hinc.
        destruct Hinc as [Hterm|Hs].
        -- left; apply in_app_iff; left; exact Hterm.
        -- right; exact Hs.
      * right; exact Hmem.
    + apply in_app_iff in Hmem. destruct Hmem as [Hmem|Hmem].
      * pose proof (IHt2 x s a1 Hmem) as Hinc. apply in_app_iff in Hinc.
        destruct Hinc as [Hterm|Hs].
        -- left; apply in_app_iff; right; exact Hterm.
        -- right; exact Hs.
      * right; exact Hmem.
  - apply in_app_iff in Hmem. apply in_app_iff.
    destruct Hmem as [Hmem|Hmem].
    + apply in_app_iff in Hmem. destruct Hmem as [Hmem|Hmem].
      * pose proof (IHt1 x s a1 Hmem) as Hinc. apply in_app_iff in Hinc.
        destruct Hinc as [Hterm|Hs].
        -- left; apply in_app_iff; left; exact Hterm.
        -- right; exact Hs.
      * right; exact Hmem.
    + apply in_app_iff in Hmem. destruct Hmem as [Hmem|Hmem].
      * pose proof (IHt2 x s a1 Hmem) as Hinc. apply in_app_iff in Hinc.
        destruct Hinc as [Hterm|Hs].
        -- left; apply in_app_iff; right; exact Hterm.
        -- right; exact Hs.
      * right; exact Hmem.

Qed.

Lemma qualifier_fv_open_closed_incl : forall p u,
  fv_tm u = [] -> incl (qualifier_fv (open_qualifier_tm p u)) (qualifier_fv p).
Proof.
  induction p; intros u Hu x Hx; simpl in *; try contradiction.
  - apply in_app_or in Hx. apply in_or_app. destruct Hx as [Hx|Hx].
    + left. eapply fv_tm_open_closed_incl; eassumption.
    + right. eapply fv_tm_open_closed_incl; eassumption.
  - apply in_app_or in Hx. apply in_or_app. destruct Hx as [Hx|Hx].
    + left. eapply fv_tm_open_closed_incl; eassumption.
    + right. eapply fv_tm_open_closed_incl; eassumption.
  - apply in_app_or in Hx. apply in_or_app. destruct Hx as [Hx|Hx].
    + left. eapply fv_tm_open_closed_incl; eassumption.
    + right. eapply fv_tm_open_closed_incl; eassumption.
  - apply in_app_or in Hx. apply in_or_app. destruct Hx as [Hx|Hx].
    + left. eapply IHp1; eassumption.
    + right. eapply IHp2; eassumption.
  - apply in_app_or in Hx. apply in_or_app. destruct Hx as [Hx|Hx].
    + left. eapply IHp1; eassumption.
    + right. eapply IHp2; eassumption.
  - eapply IHp; eassumption.
Qed.

Lemma qualifier_subst_open_fvar : forall p x v,
  ~ In x (qualifier_fv p) ->
  qualifier_subst x v (open_qualifier_tm p (tm_fvar x)) =
  open_qualifier_tm p v.
Proof.
  intros p x v Hfresh.
  unfold qualifier_subst, open_qualifier_tm, open_qualifier_tm_rec,
    open_pred_tm, open_pred_tm_rec.
  induction p; simpl in *; try reflexivity.
  - f_equal.
    + eapply tm_subst_open_fvar_rec; intro Hin; apply Hfresh; apply in_or_app; left; exact Hin.
    + eapply tm_subst_open_fvar_rec; intro Hin; apply Hfresh; apply in_or_app; right; exact Hin.
  - f_equal.
    + eapply tm_subst_open_fvar_rec; intro Hin; apply Hfresh; apply in_or_app; left; exact Hin.
    + eapply tm_subst_open_fvar_rec; intro Hin; apply Hfresh; apply in_or_app; right; exact Hin.
  - f_equal.
    + eapply tm_subst_open_fvar_rec; intro Hin; apply Hfresh; apply in_or_app; left; exact Hin.
    + eapply tm_subst_open_fvar_rec; intro Hin; apply Hfresh; apply in_or_app; right; exact Hin.
  - f_equal.
    + eapply IHp1; intro Hin; apply Hfresh; apply in_or_app; left; exact Hin.
    + eapply IHp2; intro Hin; apply Hfresh; apply in_or_app; right; exact Hin.
  - f_equal.
    + eapply IHp1; intro Hin; apply Hfresh; apply in_or_app; left; exact Hin.
    + eapply IHp2; intro Hin; apply Hfresh; apply in_or_app; right; exact Hin.
  - f_equal. eapply IHp; eassumption.
Qed.

Lemma open_ty_rec_fresh_injective : forall k L T U,
  (forall X, ~ In X L ->
    open_ty_rec k (Ty_FVar X) T = open_ty_rec k (Ty_FVar X) U) ->
  T = U.
Proof.
  intros k L T U Hall; revert k L U Hall;
  induction T; intros k L U Hall; destruct U; simpl in Hall;
    try (exfalso; specialize (Hall (fresh L) (fresh_not_in L)); discriminate).
  all: try solve [destruct (Nat.eqb k n);
    specialize (Hall (fresh L) (fresh_not_in L)); simpl in Hall; discriminate].
  - destruct (Nat.eqb k n) eqn:En, (Nat.eqb k n0) eqn:Em.
    + apply Nat.eqb_eq in En; apply Nat.eqb_eq in Em; subst; reflexivity.
    + exfalso. specialize (Hall (fresh L) (fresh_not_in L)).
      discriminate.
    + exfalso. specialize (Hall (fresh L) (fresh_not_in L)).
      discriminate.
    + specialize (Hall (fresh L) (fresh_not_in L)).
      inversion Hall; subst; reflexivity.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst.
      set (X := fresh L); set (Y := fresh (X :: L)).
      assert (HX : ~ In X L) by (unfold X; apply fresh_not_in).
      assert (HY0 : ~ In Y (X :: L)) by (unfold Y; apply fresh_not_in).
      assert (HYX : Y <> X).
      { intro Heq; apply HY0; simpl; left; symmetry; exact Heq. }
      assert (HY : ~ In Y L).
      { intro Hin; apply HY0; simpl; right; exact Hin. }
      assert (HXY : X <> Y) by congruence.
      pose proof (Hall X HX) as Hx.
      pose proof (Hall Y HY) as Hy.
      simpl in Hx, Hy. congruence.
    + specialize (Hall (fresh L) (fresh_not_in L)). discriminate.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst.
      set (X := fresh L); set (Y := fresh (X :: L)).
      assert (HX : ~ In X L) by (unfold X; apply fresh_not_in).
      assert (HY0 : ~ In Y (X :: L)) by (unfold Y; apply fresh_not_in).
      assert (HYX : Y <> X).
      { intro Heq; apply HY0; simpl; left; symmetry; exact Heq. }
      assert (HY : ~ In Y L).
      { intro Hin; apply HY0; simpl; right; exact Hin. }
      pose proof (Hall X HX) as Hx; pose proof (Hall Y HY) as Hy.
      simpl in Hx, Hy. congruence.
    + specialize (Hall (fresh L) (fresh_not_in L)); discriminate.
  - specialize (Hall (fresh L) (fresh_not_in L)); exact Hall.
  - f_equal.
    + eapply IHT1. intros X HX. pose proof (Hall X HX) as Heq.
      injection Heq as E1 E2; exact E1.
    + eapply IHT2. intros X HX. pose proof (Hall X HX) as Heq.
      injection Heq as E1 E2; exact E2.
  - f_equal. eapply IHT with (k := S k).
    intros X HX. pose proof (Hall X HX) as Heq.
    injection Heq as E; exact E.
  - reflexivity.
Qed.

Lemma lc_open_fvar_reflect : forall (K k : nat) (x : atom) (t : tm),
  lc_tm_at K k (open_tm_rec k (tm_fvar x) t) ->
  lc_tm_at K (S k) t.
Proof.
  intros K k x t H; revert K k H.
  induction t; intros K k H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst; constructor; lia.
    + inversion H; subst; constructor; lia.
  - constructor.
  - inversion H; subst. econstructor; eauto.
  - inversion H; subst. econstructor; eauto.
  - inversion H; subst. econstructor; eauto.
  - inversion H; subst. econstructor; eauto.
  - constructor.
  - inversion H; subst. econstructor; eauto.
  - inversion H; subst. econstructor; eauto.
  - inversion H; subst. econstructor; eauto.
Qed.

Lemma lc_open_ty_fvar_reflect : forall (K k : nat) (X : atom) (T : ty),
  k < K -> lc_ty_at K (open_ty_rec k (Ty_FVar X) T) -> lc_ty_at K T.
Proof.
  intros K k X T Hlt H; revert K k Hlt H.
  induction T; intros K k Hlt H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst; constructor; exact Hlt.
    + inversion H; subst; constructor; assumption.
  - constructor.
  - inversion H; subst. econstructor; eauto.
  - inversion H; subst. eapply lc_ty_all.
    assert (Hlt' : S k < S K) by lia.
    eapply (IHT (S K) (S k)); eauto.
  - constructor.
Qed.

Lemma wf_ty_locally_closed : forall Delta T,
  wf_ty Delta T -> lc_ty_at (length Delta) T.
Proof.
  intros Delta T H; induction H as
    [Delta X Hin
    | Delta T1 T2 H1 IH1 H2 IH2
    | L Delta T Hbody IHbody
    | Delta].
  - constructor.
  - econstructor; eauto.
  - assert (Hfresh : ~ In (fresh L) L) by apply fresh_not_in.
    specialize (IHbody (fresh L) Hfresh).
    simpl in IHbody.
    apply lc_ty_all.
    eapply (lc_open_ty_fvar_reflect (S (length Delta)) 0 (fresh L) T).
    + simpl; lia.
    + exact IHbody.
  - constructor.
Qed.

Lemma lc_open_ty_tm_reflect : forall (K k depth : nat) (X : atom) (t : tm),
  depth < K ->
  lc_tm_at K k (open_tm_ty_rec depth (Ty_FVar X) t) ->
  lc_tm_at K k t.
Proof.
  intros K k depth X t Hnk Hlc; revert K k depth Hnk Hlc.
  induction t; intros K k depth Hnk Hlc; simpl in Hlc.
  - inversion Hlc; subst; constructor; assumption.
  - constructor.
  - inversion Hlc; subst.
    econstructor.
    + eapply lc_open_ty_fvar_reflect; eauto.
    + eapply IHt; eauto.
  - inversion Hlc; subst. econstructor; eauto.
  - inversion Hlc; subst. econstructor.
    eapply IHt with (K := S K) (depth := S depth); eauto; lia.
  - inversion Hlc; subst.
    econstructor; [eapply IHt; eauto|eapply lc_open_ty_fvar_reflect; eauto].
  - constructor.
  - inversion Hlc; subst. econstructor; eauto.
  - inversion Hlc; subst. econstructor; eauto.
  - inversion Hlc; subst. econstructor; eauto.
Qed.

Lemma erase_open_rty_tm_rec : forall k u R,
  erase (open_rty_tm_rec k u R) = erase R.
Proof.
  intros k u R; revert k u; induction R; intros k u; simpl;
    try rewrite IHR1; try rewrite IHR2; try rewrite IHR; reflexivity.
Qed.

Lemma erase_open_rty_tm : forall R u,
  erase (open_rty_tm R u) = erase R.
Proof. intros; apply erase_open_rty_tm_rec. Qed.

Lemma erase_open_rty_ty_rec : forall k U R,
  erase (open_rty_ty_rec k U R) = open_ty_rec k U (erase R).
Proof.
  intros k U R; revert k U; induction R; intros k U; simpl;
    try rewrite IHR1; try rewrite IHR2; try rewrite IHR; reflexivity.
Qed.

Lemma erase_open_rty_ty : forall R U,
  erase (open_rty_ty R U) = open_ty (erase R) U.
Proof. intros; apply erase_open_rty_ty_rec. Qed.

Lemma erase_subtype_equal : forall Delta RGamma R S,
  subtype Delta RGamma R S -> erase R = erase S.
Proof.
  intros Delta RGamma R S H; induction H as
    [Delta RGamma R
    | L Delta RGamma T ps qs Hbody
    | L Delta RGamma R1 R2 S1 S2 Hdom IHdom Hcod IHcod
    | Delta RGamma v R1 R2 S Hv Hvr Hsub IHsub
    | L Delta RGamma R1 R2 S Hwf Hlc Hbody IHbody
    | L Delta RGamma R S Hbody IHbody
    | Delta RGamma R S U H1 IH1 H2 IH2]; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + symmetry; exact IHdom.
    + pose proof (IHcod (fresh L) (fresh_not_in L)) as Hx.
      rewrite !erase_open_rty_tm in Hx; exact Hx.
  - rewrite erase_open_rty_tm in IHsub; exact IHsub.
  - pose proof (IHbody (fresh L) (fresh_not_in L)) as Hx.
    rewrite erase_open_rty_tm in Hx; exact Hx.
  - f_equal. apply open_ty_rec_fresh_injective with (L := L) (k := 0).
    intros X HX. pose proof (IHbody X HX) as Hx.
    rewrite !erase_open_rty_ty in Hx; exact Hx.
  - transitivity (erase S); assumption.
Qed.

Lemma lookup_erased_context : forall x RGamma,
  lookup_context x (erase_context RGamma) =
  option_map erase (lookup_rcontext x RGamma).
Proof.
  intros x RGamma; induction RGamma as [|[y R] RGamma IH]; simpl.
  - reflexivity.
  - unfold update; simpl. destruct (Nat.eqb x y); simpl; auto.
Qed.



Lemma has_type_locally_closed : forall Delta Gamma t T,
  has_type Delta Gamma t T -> lc_tm_at (length Delta) 0 t.
Proof.
  intros Delta Gamma t T H; induction H as
    [Delta Gamma x T Hlookup Hwf
    | L Delta Gamma T1 body T2 Hwf Hbody IHbody
    | Delta Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
    | L Delta Gamma body T Hbody IHbody
    | Delta Gamma t T U Ht IHt Hwf
    | Delta Gamma z
    | Delta Gamma t1 t2 H1 IH1 H2 IH2
    | Delta Gamma op t1 t2 H1 IH1 H2 IH2
    | Delta Gamma t1 t2 T H1 IH1 H2 IH2].
  - constructor.
  - assert (Hfresh : ~ In (fresh L) L) by apply fresh_not_in.
    specialize (IHbody (fresh L) Hfresh).
    econstructor.
    + eapply wf_ty_locally_closed; eassumption.
    + eapply lc_open_fvar_reflect; exact IHbody.
  - econstructor; eauto.
  - assert (Hfresh : ~ In (fresh L) L) by apply fresh_not_in.
    specialize (IHbody (fresh L) Hfresh).
    econstructor. eapply lc_open_ty_tm_reflect with (depth := 0)
      (X := fresh L); [simpl; lia|exact IHbody].
  - econstructor; [exact IHt|eapply wf_ty_locally_closed; eassumption].
  - constructor.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
Qed.

Lemma wf_rty_erasure : forall Delta RGamma R,
  wf_rty Delta RGamma R -> wf_ty Delta (erase R).
Proof.
  intros Delta RGamma R H; induction H as
    [L Delta RGamma T ps Hwf Hpred
    | L Delta RGamma R1 R2 Hwf IHwf Hbody IHbody
    | L Delta RGamma R1 R2 Hwf IHwf Hbody IHbody
    | L Delta RGamma R Hbody IHbody].
  - simpl; exact Hwf.
  - simpl; constructor; [exact IHwf|].
    assert (Hfresh : ~ In (fresh L) L) by apply fresh_not_in.
    specialize (IHbody (fresh L) Hfresh).
    rewrite erase_open_rty_tm in IHbody; exact IHbody.
  - simpl.
    assert (Hfresh : ~ In (fresh L) L) by apply fresh_not_in.
    specialize (IHbody (fresh L) Hfresh).
    rewrite erase_open_rty_tm in IHbody; exact IHbody.
  - simpl. apply WF_All with (L := L).
    intros X HX.
    specialize (IHbody X HX).
    rewrite erase_open_rty_ty in IHbody.
    exact IHbody.
Qed.

Lemma has_rtype_erases : forall Delta RGamma t R,
  has_rtype Delta RGamma t R ->
  has_type Delta (erase_context RGamma) t (erase R).
Proof.
  intros Delta RGamma t R H; induction H as
    [Delta RGamma x R Hlookup Hwf
    | L Delta RGamma R1 body R2 Hwf Hbody IHbody
    | Delta RGamma t1 t2 R1 R2 H1 IH1 H2 IH2
    | L Delta RGamma body R Hbody IHbody
    | Delta RGamma t R U Ht IHt Hwf
    | Delta RGamma z
    | Delta RGamma t1 t2 H1 IH1 H2 IH2
    | Delta RGamma op t1 t2 H1 IH1 H2 IH2
    | Delta RGamma t1 t2 R H1 IH1 H2 IH2
    | Delta RGamma v T ps Htype Hv Hwf Hclosed Hholds
    | Delta RGamma t R S Ht IHt Hwf Hsub].
  - apply T_Var.
    + rewrite lookup_erased_context, Hlookup; reflexivity.
    + eapply wf_rty_erasure; eassumption.
  - eapply T_Abs.
    + eapply wf_rty_erasure; eassumption.
    + intros x Hx.
      specialize (IHbody x Hx).
      rewrite erase_open_rty_tm in IHbody.
      exact IHbody.
  - eapply T_App; eassumption.
  - eapply T_TAbs. intros X HX.
    specialize (IHbody X HX).
    rewrite erase_open_rty_ty in IHbody; exact IHbody.
  - rewrite erase_open_rty_ty.
    eapply T_TApp; [exact IHt|exact Hwf].
  - constructor.
  - econstructor; eassumption.
  - econstructor; eassumption.
  - econstructor; eassumption.
  - exact Htype.
  - rewrite <- (erase_subtype_equal _ _ _ _ Hsub).
    exact IHt.
Qed.

Lemma value_arrow_form : forall Delta v A B,
  has_type Delta empty v (Ty_Arrow A B) -> value v ->
  exists T body, v = tm_abs T body.
Proof.
  intros Delta v A B Hty Hv.
  inversion Hv; subst; inversion Hty; subst; eexists; eexists; reflexivity.
Qed.

Lemma value_poly_form : forall Delta v T,
  has_type Delta empty v (Ty_All T) -> value v ->
  exists body, v = tm_tabs body.
Proof.
  intros Delta v T Hty Hv.
  inversion Hv; subst; inversion Hty; subst; eexists; reflexivity.
Qed.

Lemma value_int_form : forall Delta v,
  has_type Delta empty v Ty_Int -> value v ->
  exists n, v = tm_int n.
Proof.
  intros Delta v Hty Hv.
  inversion Hv; subst; inversion Hty; subst; eexists; reflexivity.
Qed.



Lemma has_rtype_locally_closed : forall Delta RGamma t R,
  has_rtype Delta RGamma t R -> lc_tm_at (length Delta) 0 t.
Proof.
  intros Delta RGamma t R H; induction H as
    [Delta RGamma x R Hlookup Hwf
    | L Delta RGamma R1 body R2 Hwf Hbody IHbody
    | Delta RGamma t1 t2 R1 R2 H1 IH1 H2 IH2
    | L Delta RGamma body R Hbody IHbody
    | Delta RGamma t R U Ht IHt Hwf
    | Delta RGamma z
    | Delta RGamma t1 t2 H1 IH1 H2 IH2
    | Delta RGamma op t1 t2 H1 IH1 H2 IH2
    | Delta RGamma t1 t2 R H1 IH1 H2 IH2
    | Delta RGamma v T ps Htype Hv Hwf Hclosed Hholds
    | Delta RGamma t R S Ht IHt Hwf Hsub].
  - constructor.
  - assert (Hfresh : ~ In (fresh L) L) by apply fresh_not_in.
    specialize (IHbody (fresh L) Hfresh).
    econstructor.
    + eapply wf_ty_locally_closed. eapply wf_rty_erasure; eassumption.
    + eapply lc_open_fvar_reflect; exact IHbody.
  - econstructor; eauto.
  - assert (Hfresh : ~ In (fresh L) L) by apply fresh_not_in.
    specialize (IHbody (fresh L) Hfresh).
    econstructor. eapply lc_open_ty_tm_reflect with (depth := 0)
      (X := fresh L); [simpl; lia|exact IHbody].
  - econstructor; [exact IHt|eapply wf_ty_locally_closed; eassumption].
  - constructor.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
  - eapply has_type_locally_closed; eassumption.
  - exact IHt.
Qed.

Lemma rtype_progress_given_nonzero_values :
  (forall t, has_rtype [] empty_rcontext t
      (R_Refine Ty_Int (Pred_Ne (tm_bvar 0) (tm_int 0%Z))) ->
      value t -> exists m : Z, t = tm_int m /\ m <> 0%Z) ->
  forall t R, has_rtype [] empty_rcontext t R ->
  value t \/ exists u, t --> u.
Proof.
  intros Hnz t R Hty; dependent induction Hty.
  - left. apply v_abs.
    eapply lc_tm_abs.
    + eapply (wf_ty_locally_closed [] (erase R1)).
      eapply wf_rty_erasure; eassumption.
    + assert (Hfresh : ~ In (fresh L) L) by apply fresh_not_in.
      specialize (H0 (fresh L) Hfresh).
      pose proof (has_rtype_locally_closed _ _ _ _ H0) as Hlc.
      simpl in Hlc. eapply lc_open_fvar_reflect; exact Hlc.
  - destruct (IHHty1 (JMeq_refl []) eq_refl) as [Hv1|[t1' Hstep1]].
    + destruct (IHHty2 (JMeq_refl []) eq_refl) as [Hv2|[t2' Hstep2]].
      * right. destruct (value_arrow_form [] t1 (erase R1) (erase R2)
          (has_rtype_erases _ _ _ _ Hty1) Hv1) as [T [body ->]].
        exists (open_tm body t2). apply ST_AppAbs.
        -- eapply (has_rtype_locally_closed [] [] _ _ Hty1).
        -- exact Hv2.
      * right. exists (tm_app t1 t2'). apply ST_App2; assumption.
    + right. exists (tm_app t1' t2). apply ST_App1; [exact Hstep1|].
      eapply (has_rtype_locally_closed [] [] _ _ Hty2).
  - left. apply v_tabs. eapply lc_tm_tabs.
    assert (Hfresh : ~ In (fresh L) L) by apply fresh_not_in.
    pose proof (H (fresh L) Hfresh) as Hopen.
    pose proof (has_rtype_locally_closed _ _ _ _ Hopen) as Hlc.
    simpl in Hlc.
    eapply lc_open_ty_tm_reflect with (depth := 0) (X := fresh L).
    + simpl; lia.
    + exact Hlc.
  - destruct (IHHty (JMeq_refl []) eq_refl) as [Hv|[t' Hstep]].
    + right. destruct (value_poly_form [] t (erase R)
        (has_rtype_erases _ _ _ _ Hty) Hv) as [body ->].
      exists (open_tm_ty body U). apply ST_TAppTabs.
      * eapply (has_rtype_locally_closed [] [] _ _ Hty).
      * eapply (wf_ty_locally_closed [] U); eassumption.
    + right. exists (tm_tapp t' U). apply ST_TApp; [exact Hstep|].
      eapply (wf_ty_locally_closed [] U); eassumption.
  - left; constructor.
  - destruct (IHHty1 (JMeq_refl []) eq_refl) as [Hv1|[t1' Hstep1]].
    + destruct (IHHty2 (JMeq_refl []) eq_refl) as [Hv2|[t2' Hstep2]].
      * right. destruct (value_int_form [] t1 (has_rtype_erases _ _ _ _ Hty1) Hv1)
          as [n ->].
        destruct (Hnz t2 Hty2 Hv2) as [m [-> Hm]].
        exists (tm_int (Z.div n m)). apply ST_DivInt; exact Hm.
      * right. exists (tm_div t1 t2'). apply ST_Div2; assumption.
    + right. exists (tm_div t1' t2). apply ST_Div1; [exact Hstep1|].
      eapply (has_rtype_locally_closed [] [] _ _ Hty2).
  - destruct (IHHty1 (JMeq_refl []) eq_refl) as [Hv1|[t1' Hstep1]].
    + destruct (IHHty2 (JMeq_refl []) eq_refl) as [Hv2|[t2' Hstep2]].
      * right. destruct (value_int_form [] t1 (has_rtype_erases _ _ _ _ Hty1) Hv1)
          as [n ->].
        destruct (value_int_form [] t2 (has_rtype_erases _ _ _ _ Hty2) Hv2)
          as [m ->].
        exists (tm_int (eval_integer_operator op n m)). constructor.
      * right. exists (tm_arith op t1 t2'). apply ST_Arith2; assumption.
    + right. exists (tm_arith op t1' t2). apply ST_Arith1; [exact Hstep1|].
      eapply (has_rtype_locally_closed [] [] _ _ Hty2).
  - right. exists t1. apply ST_ChoiceLeft.
    + eapply (has_rtype_locally_closed [] [] _ _ Hty1).
    + eapply (has_rtype_locally_closed [] [] _ _ Hty2).
  - left; exact H0.
  - exact (IHHty (JMeq_refl []) eq_refl).

Qed.

Lemma predicate_multistep_zero :
  predicate_multistep (tm_int 0%Z) (tm_int 0%Z).
Proof. constructor. Qed.

Lemma multi_to_predicate_multistep : forall t u,
  multi t u -> predicate_multistep t u.
Proof.
  intros t u H; induction H.
  - constructor.
  - econstructor; eauto.
Qed.

Lemma multi_trans : forall t u v,
  multi t u -> multi u v -> multi t v.
Proof.
  intros t u v Htu Huv; induction Htu.
  - exact Huv.
  - econstructor; eauto.
Qed.

Lemma predicate_multistep_to_multi : forall t u,
  predicate_multistep t u -> multi t u.
Proof.
  intros t u H; induction H.
  - constructor.
  - econstructor; eauto.
Qed.

Lemma predicate_multistep_trans : forall t u v,
  predicate_multistep t u -> predicate_multistep u v ->
  predicate_multistep t v.
Proof.
  intros t u v Htu Huv; induction Htu.
  - exact Huv.
  - econstructor; eauto.
Qed.

Lemma predicate_multistep_refl : forall t,
  predicate_multistep t t.
Proof. constructor. Qed.

Lemma predicate_multistep_int_eq : forall n m,
  interpret_eq operational_atoms (tm_int n) (tm_int m) -> n = m.
Proof.
  intros n m [v [Hn [Hm Hv]]].
  inversion Hn; subst; clear Hn.
  - inversion Hm; subst; [congruence | inversion H].
  - inversion H; subst.
Qed.

Lemma nonzero_refinement_excludes_zero : forall t,
  qualifier_holds (Pred_Ne t (tm_int 0%Z)) ->
  predicate_multistep t (tm_int 0%Z) -> False.
Proof.
  intros t Hneq Hzero.
  unfold qualifier_holds, predicate_holds, Pred_Ne, interpret_qualifier in Hneq.
  simpl in Hneq.
  apply Hneq.
  exists (tm_int 0%Z).
  split; [exact Hzero|].
  split; [apply predicate_multistep_zero|constructor].
Qed.

Lemma integer_nonzero_of_refinement : forall n,
  qualifier_holds (Pred_Ne (tm_int n) (tm_int 0%Z)) -> n <> 0%Z.
Proof.
  intros n Hq Heq; subst n.
  eapply nonzero_refinement_excludes_zero; [exact Hq|constructor].
Qed.

Lemma entails_sound_under_context : forall Delta RGamma p q,
  (forall x T ps, lookup_rcontext x RGamma = Some (R_Refine T ps) ->
    qualifier_holds (open_qualifier_tm ps (tm_fvar x))) ->
  entails Delta RGamma p q ->
  qualifier_holds p -> qualifier_holds q.
Proof.
  intros Delta RGamma p q Hctx Hent.
  unfold qualifier_holds, predicate_holds in *.
  induction Hent; simpl in *; intuition.
  - eapply Hctx; eassumption.
Qed.

Lemma entails_sound_true_context : forall Delta x T p q,
  entails Delta (update_rcontext empty_rcontext x (R_Refine T Pred_True)) p q ->
  qualifier_holds p -> qualifier_holds q.
Proof.
  intros Delta x T p q Hent Hp.
  eapply entails_sound_under_context; [|exact Hent|exact Hp].
  intros y U ps Hlookup.
  simpl in Hlookup.
  destruct (Nat.eqb y x) eqn:E; inversion Hlookup; subst.
  simpl; exact I.
Qed.

Lemma entails_sound_true_context_subst : forall Delta x T p q v,
  entails Delta (update_rcontext empty_rcontext x (R_Refine T Pred_True)) p q ->
  qualifier_holds (qualifier_subst x v p) ->
  qualifier_holds (qualifier_subst x v q).
Proof.
  intros Delta x T p q v Hent Hp.
  unfold qualifier_holds, predicate_holds in *.
  dependent induction Hent; simpl in *; intuition eauto.
  all: try match goal with
  | Hctx : update_rcontext empty_rcontext ?x1 (R_Refine ?T1 Pred_True) =
      update_rcontext empty_rcontext ?y (R_Refine ?U Pred_True) |- _ =>
      inversion Hctx; subst; simpl; exact I
  end.
  all: intuition eauto.
  simpl in H. destruct (Nat.eqb x0 x) eqn:E; inversion H; subst.
  simpl; exact I.
Qed.

Lemma entails_sound_substituted_context : forall Delta RGamma x v p q,
  (forall y T ps,
    lookup_rcontext y RGamma = Some (R_Refine T ps) ->
    qualifier_holds
      (qualifier_subst x v (open_qualifier_tm ps (tm_fvar y)))) ->
  entails Delta RGamma p q ->
  qualifier_holds (qualifier_subst x v p) ->
  qualifier_holds (qualifier_subst x v q).
Proof.
  intros Delta RGamma x v p q Hctx Hent Hp.
  unfold qualifier_holds, predicate_holds in *.
  induction Hent; simpl in *; intuition.
  - eapply Hctx; eassumption.
Qed.

Definition term_environment := list (atom * tm).

Fixpoint lookup_term_environment (x : atom) (rho : term_environment) : option tm :=
  match rho with
  | [] => None
  | (y, v) :: rho' => if Nat.eqb x y then Some v else lookup_term_environment x rho'
  end.

Fixpoint substitute_term_environment (rho : term_environment) (t : tm) : tm :=
  match rho with
  | [] => t
  | (x, v) :: rho' => tm_subst x v (substitute_term_environment rho' t)
  end.

Lemma substitute_term_environment_open_fvar : forall rho t x,
  (forall y v, In (y,v) rho -> x <> y) ->
  (forall y v, In (y,v) rho -> ~ In x (fv_tm v)) ->
  (forall y v, In (y,v) rho -> locally_closed_tm v) ->
  substitute_term_environment rho (open_tm t (tm_fvar x)) =
  open_tm (substitute_term_environment rho t) (tm_fvar x).
Proof.
  intros rho; induction rho as [|[y v] rho IH]; intros t x Hdom Hfv Hlc; simpl.
  - reflexivity.
  - rewrite IH.
    + eapply tm_subst_open_fvar_commute_rec.
      * exact (Hdom y v (or_introl eq_refl)).
      * exact (Hfv y v (or_introl eq_refl)).
      * exact (Hlc y v (or_introl eq_refl)).
    + intros z w Hin. exact (Hdom z w (or_intror Hin)).
    + intros z w Hin. exact (Hfv z w (or_intror Hin)).
    + intros z w Hin. exact (Hlc z w (or_intror Hin)).
Qed.

Lemma substitute_term_environment_open : forall rho t w,
  (forall y v, In (y,v) rho -> locally_closed_tm v) ->
  substitute_term_environment rho (open_tm t w) =
  open_tm (substitute_term_environment rho t)
    (substitute_term_environment rho w).
Proof.
  intros rho; induction rho as [|[y v] rho IH]; intros t w Hlc; simpl.
  - reflexivity.
  - rewrite IH.
    + exact (tm_subst_open_rec_commute
        (substitute_term_environment rho t) 0 y v
        (substitute_term_environment rho w)
        (Hlc y v (or_introl eq_refl))).
    + intros z u Hin. exact (Hlc z u (or_intror Hin)).
Qed.

Lemma substitute_term_environment_open_bound : forall rho body x w,
  (forall y v, In (y,v) rho -> x <> y) ->
  (forall y v, In (y,v) rho -> ~ In x (fv_tm v)) ->
  (forall y v, In (y,v) rho -> locally_closed_tm v) ->
  ~ In x (fv_tm (substitute_term_environment rho body)) ->
  locally_closed_tm w ->
  substitute_term_environment ((x,w)::rho) (open_tm body (tm_fvar x)) =
  open_tm (substitute_term_environment rho body) w.
Proof.
  intros rho body x w Hdom Hfv Hlc Hbody Hlw. simpl.
  rewrite substitute_term_environment_open_fvar with
    (x := x) (t := body); try assumption.
  eapply tm_subst_open_fvar_rec; assumption.
Qed.

Fixpoint substitute_qualifier_environment (rho : term_environment)
    (p : qualifier) : qualifier :=
  match p with
  | Pred_True => Pred_True
  | Pred_False => Pred_False
  | Pred_Eq t1 t2 => Pred_Eq (substitute_term_environment rho t1)
      (substitute_term_environment rho t2)
  | Pred_Lt t1 t2 => Pred_Lt (substitute_term_environment rho t1)
      (substitute_term_environment rho t2)
  | Pred_Le t1 t2 => Pred_Le (substitute_term_environment rho t1)
      (substitute_term_environment rho t2)
  | Pred_And p1 p2 => Pred_And (substitute_qualifier_environment rho p1)
      (substitute_qualifier_environment rho p2)
  | Pred_Or p1 p2 => Pred_Or (substitute_qualifier_environment rho p1)
      (substitute_qualifier_environment rho p2)
  | Pred_Not p1 => Pred_Not (substitute_qualifier_environment rho p1)
  end.

Lemma substitute_qualifier_environment_open : forall rho p u,
  (forall x v, In (x,v) rho -> locally_closed_tm v) ->
  substitute_qualifier_environment rho (open_qualifier_tm p u) =
  open_qualifier_tm (substitute_qualifier_environment rho p)
    (substitute_term_environment rho u).
Proof.
  intros rho p; induction p; intros u Hlc; simpl.
  - reflexivity.
  - reflexivity.
  - change (Pred_Eq (substitute_term_environment rho (open_tm t u))
        (substitute_term_environment rho (open_tm t0 u)) =
      Pred_Eq (open_tm (substitute_term_environment rho t)
        (substitute_term_environment rho u))
        (open_tm (substitute_term_environment rho t0)
        (substitute_term_environment rho u))).
    rewrite (substitute_term_environment_open rho t u Hlc),
      (substitute_term_environment_open rho t0 u Hlc). reflexivity.
  - change (Pred_Lt (substitute_term_environment rho (open_tm t u))
        (substitute_term_environment rho (open_tm t0 u)) =
      Pred_Lt (open_tm (substitute_term_environment rho t)
        (substitute_term_environment rho u))
        (open_tm (substitute_term_environment rho t0)
        (substitute_term_environment rho u))).
    rewrite (substitute_term_environment_open rho t u Hlc),
      (substitute_term_environment_open rho t0 u Hlc). reflexivity.
  - change (Pred_Le (substitute_term_environment rho (open_tm t u))
        (substitute_term_environment rho (open_tm t0 u)) =
      Pred_Le (open_tm (substitute_term_environment rho t)
        (substitute_term_environment rho u))
        (open_tm (substitute_term_environment rho t0)
        (substitute_term_environment rho u))).
    rewrite (substitute_term_environment_open rho t u Hlc),
      (substitute_term_environment_open rho t0 u Hlc). reflexivity.
  - change (Pred_And
      (substitute_qualifier_environment rho (open_qualifier_tm p1 u))
      (substitute_qualifier_environment rho (open_qualifier_tm p2 u)) =
      Pred_And
      (open_qualifier_tm (substitute_qualifier_environment rho p1)
        (substitute_term_environment rho u))
      (open_qualifier_tm (substitute_qualifier_environment rho p2)
        (substitute_term_environment rho u))).
    rewrite (IHp1 u Hlc), (IHp2 u Hlc). reflexivity.
  - change (Pred_Or
      (substitute_qualifier_environment rho (open_qualifier_tm p1 u))
      (substitute_qualifier_environment rho (open_qualifier_tm p2 u)) =
      Pred_Or
      (open_qualifier_tm (substitute_qualifier_environment rho p1)
        (substitute_term_environment rho u))
      (open_qualifier_tm (substitute_qualifier_environment rho p2)
        (substitute_term_environment rho u))).
    rewrite (IHp1 u Hlc), (IHp2 u Hlc). reflexivity.
  - change (Pred_Not
      (substitute_qualifier_environment rho (open_qualifier_tm p u)) =
      Pred_Not (open_qualifier_tm (substitute_qualifier_environment rho p)
        (substitute_term_environment rho u))).
    rewrite ( IHp u Hlc). reflexivity.
Qed.

Lemma substitute_term_environment_fvar_absent : forall rho x,
  (forall y v, In (y,v) rho -> x <> y) ->
  substitute_term_environment rho (tm_fvar x) = tm_fvar x.
Proof.
  intros rho; induction rho as [|[y v] rho IH]; intros x Hdom; simpl.
  - reflexivity.
  - rewrite IH.
    + assert (Nat.eqb y x = false) by (apply Nat.eqb_neq; intro E; subst; specialize (Hdom x v (or_introl eq_refl)); contradiction).
      simpl. rewrite H. reflexivity.
    + intros z w Hin. exact (Hdom z w (or_intror Hin)).
Qed.

Lemma substitute_qualifier_environment_cons : forall rho x w p,
  substitute_qualifier_environment ((x,w)::rho) p =
  qualifier_subst x w (substitute_qualifier_environment rho p).
Proof.
  intros rho x w p; induction p; simpl; try reflexivity;
    rewrite ?IHp, ?IHp1, ?IHp2; reflexivity.
Qed.

Lemma substitute_qualifier_environment_open_bound : forall rho p x w,
  (forall y v, In (y,v) rho -> x <> y) ->
  (forall y v, In (y,v) rho -> ~ In x (fv_tm v)) ->
  (forall y v, In (y,v) rho -> locally_closed_tm v) ->
  ~ In x (qualifier_fv (substitute_qualifier_environment rho p)) ->
  substitute_term_environment rho w = w ->
  substitute_qualifier_environment ((x,w)::rho)
    (open_qualifier_tm p (tm_fvar x)) =
  substitute_qualifier_environment rho (open_qualifier_tm p w).
Proof.
  intros rho p x w Hdom Hfv Hlc Hfresh Hw.
  rewrite substitute_qualifier_environment_cons.
  rewrite (substitute_qualifier_environment_open rho p (tm_fvar x) Hlc).
  rewrite substitute_term_environment_fvar_absent by exact Hdom.
  rewrite qualifier_subst_open_fvar by exact Hfresh.
  rewrite (substitute_qualifier_environment_open rho p w Hlc).
  now rewrite Hw.

Qed.

Fixpoint rty_term_fv (R : rty) : list atom :=
  match R with
  | R_Refine _ p => qualifier_fv p
  | R_Func R1 R2 | R_Exists R1 R2 => rty_term_fv R1 ++ rty_term_fv R2
  | R_Poly R1 => rty_term_fv R1
  end.

Fixpoint rcontext_term_fv (Gamma : rcontext) : list atom :=
  match Gamma with
  | [] => []
  | (_,R)::Gamma' => rty_term_fv R ++ rcontext_term_fv Gamma'
  end.

Fixpoint environment_term_fv (rho : term_environment) : list atom :=
  match rho with
  | [] => []
  | (_,v)::rho' => fv_tm v ++ environment_term_fv rho'
  end.

Definition context_interpretation (RGamma : rcontext)
    (rho : term_environment) : Prop :=
  forall x T ps,
    lookup_rcontext x RGamma = Some (R_Refine T ps) ->
    qualifier_holds
      (substitute_qualifier_environment rho
        (open_qualifier_tm ps (tm_fvar x))).

Lemma entails_sound_under_environment : forall Delta RGamma rho p q,
  context_interpretation RGamma rho ->
  entails Delta RGamma p q ->
  qualifier_holds (substitute_qualifier_environment rho p) ->
  qualifier_holds (substitute_qualifier_environment rho q).
Proof.
  intros Delta RGamma rho p q Hctx Hent Hp.
  unfold qualifier_holds, predicate_holds, context_interpretation in *.
  induction Hent; simpl in *; intuition.
  - eapply Hctx; eassumption.
Qed.

Definition safe_traces (t : tm) : Prop :=
  forall u, multi t u -> value u \/ exists u', u --> u'.

Definition canonical_shape (T : ty) (v : tm) : Prop :=
  match T with
  | Ty_Int => exists n, v = tm_int n
  | Ty_Arrow _ _ => exists A body, v = tm_abs A body
  | Ty_All _ => exists body, v = tm_tabs body
  | Ty_BVar _ | Ty_FVar _ => True
  end.

Fixpoint logical_relation_table (fuel : nat) :
    nat -> bool -> term_environment -> rty -> tm -> Prop :=
  match fuel with
  | 0 => fun _ _ _ _ _ => True
  | S k => fun j =>
      match j with
      | 0 => fun _ _ _ _ => True
      | S i => fun isv rho R t =>
          if isv then
            match R with
            | R_Refine T ps =>
                canonical_shape T t /\ fv_tm t = [] /\ value t /\
                qualifier_holds
                  (substitute_qualifier_environment rho
                    (open_qualifier_tm ps t))
            | R_Func R1 R2 =>
                fv_tm t = [] /\ value t /\ forall j, j <= i -> forall w, fv_tm w = [] -> value w ->
                  logical_relation_table k j true rho R1 w /\
                  logical_relation_table k j false rho
                    (open_rty_tm R2 w) (tm_app t w)
            | R_Exists R1 R2 =>
                fv_tm t = [] /\ value t /\ exists w, fv_tm w = [] /\ value w /\ forall j, j <= i ->
                  logical_relation_table k j true rho R1 w /\
                  logical_relation_table k j true rho
                    (open_rty_tm R2 w) t
            | R_Poly R1 =>
                fv_tm t = [] /\ value t /\ forall U, locally_closed_ty U ->
                  forall j, j <= i ->
                  logical_relation_table k j false rho
                    (open_rty_ty R1 U) (tm_tapp t U)
            end
          else
            safe_traces (substitute_term_environment rho t) /\
            forall u, multi (substitute_term_environment rho t) u -> value u ->
              forall j, j <= i ->
                logical_relation_table k j true rho R u
      end
  end.

Lemma logical_relation_table_down : forall n m,
  m <= n -> forall j, j <= m -> forall isv rho R t,
  logical_relation_table n j isv rho R t ->
  logical_relation_table m j isv rho R t.
Proof.
  intros n m Hmn. revert n Hmn.
  induction m as [|m IH]; intros n Hmn j Hjm isv rho R t Hrel.
  - simpl; exact I.
  - destruct n as [|n']; [lia|].
    destruct j as [|j]; [simpl; exact I|].
    simpl in Hrel |- *.
    destruct isv.
    + destruct R; simpl in Hrel |- *.
      * exact Hrel.
      * destruct Hrel as [Hfv [Hv Hrest]]. split; [exact Hfv|]. split; [exact Hv|].
        intros j0 Hj0 w Hfw Hwv.
        destruct (Hrest j0 Hj0 w Hfw Hwv) as [Hz Hb]. split.
        -- exact (IH n' (le_S_n _ _ Hmn) j0
          (Nat.le_trans _ _ _ Hj0 (le_S_n _ _ Hjm)) true rho R1 w Hz).
        -- exact (IH n' (le_S_n _ _ Hmn) j0
          (Nat.le_trans _ _ _ Hj0 (le_S_n _ _ Hjm)) false rho
          (open_rty_tm R2 w) (tm_app t w) Hb).
      * destruct Hrel as [Hfv [Hv [w [Hfw [Hwv Hrest]]]]].
        split; [exact Hfv|]. split; [exact Hv|exists w]. split; [exact Hfw|]. split; [exact Hwv|].
        intros j0 Hj0. destruct (Hrest j0 Hj0) as [Hz Hb]. split.
        -- exact (IH n' (le_S_n _ _ Hmn) j0
          (Nat.le_trans _ _ _ Hj0 (le_S_n _ _ Hjm)) true rho R1 w Hz).
        -- exact (IH n' (le_S_n _ _ Hmn) j0
          (Nat.le_trans _ _ _ Hj0 (le_S_n _ _ Hjm)) true rho
          (open_rty_tm R2 w) t Hb).
      * destruct Hrel as [Hfv [Hv Hrest]]. split; [exact Hfv|]. split; [exact Hv|].
        intros U HU j0 Hj0.
        exact (IH n' (le_S_n _ _ Hmn) j0
          (Nat.le_trans _ _ _ Hj0 (le_S_n _ _ Hjm)) false rho
          (open_rty_ty R U) (tm_tapp t U) (Hrest U HU j0 Hj0)).
    + destruct R; simpl in Hrel |- *.
      * destruct Hrel as [Hs Hrest]. split; [exact Hs|].
        intros u Hu Hv j0 Hj0.
        exact (IH n' (le_S_n _ _ Hmn) j0
          (Nat.le_trans _ _ _ Hj0 (le_S_n _ _ Hjm)) true rho (R_Refine t0 q) u
          (Hrest u Hu Hv j0 Hj0)).
      * destruct Hrel as [Hs Hrest]. split; [exact Hs|].
        intros u Hu Hv j0 Hj0.
        exact (IH n' (le_S_n _ _ Hmn) j0
          (Nat.le_trans _ _ _ Hj0 (le_S_n _ _ Hjm)) true rho (R_Func R1 R2) u
          (Hrest u Hu Hv j0 Hj0)).
      * destruct Hrel as [Hs Hrest]. split; [exact Hs|].
        intros u Hu Hv j0 Hj0.
        exact (IH n' (le_S_n _ _ Hmn) j0
          (Nat.le_trans _ _ _ Hj0 (le_S_n _ _ Hjm)) true rho (R_Exists R1 R2) u
          (Hrest u Hu Hv j0 Hj0)).
      * destruct Hrel as [Hs Hrest]. split; [exact Hs|].
        intros u Hu Hv j0 Hj0.
        exact (IH n' (le_S_n _ _ Hmn) j0
          (Nat.le_trans _ _ _ Hj0 (le_S_n _ _ Hjm)) true rho (R_Poly R) u
          (Hrest u Hu Hv j0 Hj0)).

Qed.

Lemma logical_relation_table_index_down : forall n j k,
  k <= j -> forall isv rho R t,
  logical_relation_table n j isv rho R t ->
  logical_relation_table n k isv rho R t.
Proof.
  intros n j k Hkj. revert n j Hkj.
  induction k as [|k IH]; intros n j Hkj isv rho R t Hrel.
  - destruct n; simpl; exact I.
  - destruct j as [|j]; [lia|].
    simpl in Hrel |- *.
    destruct n as [|n]; [simpl; exact I|].
    simpl in Hrel |- *.
    destruct isv; destruct R; simpl in Hrel |- *.
    + exact Hrel.
    + destruct Hrel as [Hfv [Hv Hrest]]. split; [exact Hfv|]. split; [exact Hv|].
      intros j0 Hj0 w Hfw Hwv. apply Hrest; try assumption; lia.
    + destruct Hrel as [Hfv [Hv [w [Hfw [Hwv Hrest]]]]].
      split; [exact Hfv|]. split; [exact Hv|exists w]. split; [exact Hfw|]. split; [exact Hwv|].
      intros j0 Hj0. apply Hrest; lia.
    + destruct Hrel as [Hfv [Hv Hrest]]. split; [exact Hfv|]. split; [exact Hv|].
      intros U HU j0 Hj0.
      exact (Hrest U HU j0 (Nat.le_trans _ _ _ Hj0 (le_S_n _ _ Hkj))).
    + destruct Hrel as [Hs Hrest]. split; [exact Hs|].
      intros u Hu Hv j0 Hj0.
      exact (Hrest u Hu Hv j0
        (Nat.le_trans _ _ _ Hj0 (le_S_n _ _ Hkj))).
    + destruct Hrel as [Hs Hrest]. split; [exact Hs|].
      intros u Hu Hv j0 Hj0.
      exact (Hrest u Hu Hv j0
        (Nat.le_trans _ _ _ Hj0 (le_S_n _ _ Hkj))).
    + destruct Hrel as [Hs Hrest]. split; [exact Hs|].
      intros u Hu Hv j0 Hj0.
      exact (Hrest u Hu Hv j0
        (Nat.le_trans _ _ _ Hj0 (le_S_n _ _ Hkj))).
    + destruct Hrel as [Hs Hrest]. split; [exact Hs|].
      intros u Hu Hv j0 Hj0.
      exact (Hrest u Hu Hv j0
        (Nat.le_trans _ _ _ Hj0 (le_S_n _ _ Hkj))).
Qed.

Definition logical_value (fuel : nat) (rho : term_environment)
    (R : rty) (v : tm) : Prop :=
  logical_relation_table fuel fuel true rho R v.

Definition logical_expression (fuel : nat) (rho : term_environment)
    (R : rty) (t : tm) : Prop :=
  logical_relation_table fuel fuel false rho R t.

Definition logical_context_interpretation (fuel : nat)
    (rho : term_environment) (RGamma : rcontext) : Prop :=
  forall x R, lookup_rcontext x RGamma = Some R ->
    exists v, lookup_term_environment x rho = Some v /\
      substitute_term_environment rho (tm_fvar x) = v /\
      value v /\ logical_value fuel rho R v.

Lemma lookup_rcontext_update_fresh : forall Gamma x R y S,
  lookup_rcontext x Gamma = None ->
  lookup_rcontext y (update_rcontext Gamma x R) = Some S ->
  (y = x /\ S = R) \/ (y <> x /\ lookup_rcontext y Gamma = Some S).
Proof.
  intros Gamma x R y S Hfresh Hlook. unfold update_rcontext in Hlook; simpl in Hlook.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E; subst. inversion Hlook; subst. left; auto.
  - right. apply Nat.eqb_neq in E. auto.
Qed.

Lemma logical_context_interpretation_extend : forall fuel rho Gamma x R w,
  lookup_rcontext x Gamma = None ->
  lookup_term_environment x rho = None ->
  substitute_term_environment rho (tm_fvar x) = tm_fvar x ->
  value w -> logical_value fuel ((x,w)::rho) R w ->
  (forall y S v, lookup_rcontext y Gamma = Some S ->
    lookup_term_environment y rho = Some v ->
    substitute_term_environment rho (tm_fvar y) = v ->
    tm_subst x w v = v) ->
  (forall y S v, lookup_rcontext y Gamma = Some S ->
    lookup_term_environment y rho = Some v ->
    substitute_term_environment ((x,w)::rho) (tm_fvar y) =
      substitute_term_environment rho (tm_fvar y) ->
    logical_value fuel rho S v ->
    logical_value fuel ((x,w)::rho) S v) ->
  logical_context_interpretation fuel rho Gamma ->
  logical_context_interpretation fuel ((x,w)::rho)
    (update_rcontext Gamma x R).
Proof.
  intros fuel rho Gamma x R w HxG HxEnv HxSub Hnew Hnewrel Hfix Hstable Hctx y S Hlook.
  destruct (lookup_rcontext_update_fresh _ _ _ _ _ HxG Hlook)
    as [[-> ->]|[Hy Hlook0]].
  - exists w. split.
    + simpl. rewrite Nat.eqb_refl. reflexivity.
    + split.
      * simpl. rewrite HxSub. simpl. rewrite Nat.eqb_refl. reflexivity.
      * split; [exact Hnew|exact Hnewrel].
  - destruct (Hctx y S Hlook0) as [v [Henv [Hsub [Hv Hrel]]]].
    exists v. repeat split.
    + simpl. assert (E : Nat.eqb y x = false) by (apply Nat.eqb_neq; congruence).
      rewrite E. exact Henv.
    + simpl. assert (E : Nat.eqb y x = false) by (apply Nat.eqb_neq; congruence).
      rewrite Hsub. exact (Hfix y S v Hlook0 Henv Hsub).
    + exact Hv.
    + assert (Heq : substitute_term_environment ((x,w)::rho) (tm_fvar y) =
        substitute_term_environment rho (tm_fvar y)).
      { change (tm_subst x w (substitute_term_environment rho (tm_fvar y)) =
          substitute_term_environment rho (tm_fvar y)).
        rewrite Hsub. exact (Hfix y S v Hlook0 Henv Hsub). }
      exact (Hstable y S v Hlook0 Henv Heq Hrel).
Qed.

Lemma logical_context_interpretation_down : forall n m rho RGamma,
  m <= n -> logical_context_interpretation n rho RGamma ->
  logical_context_interpretation m rho RGamma.
Proof.
  intros n m rho RGamma Hmn Hctx x R Hlook.
  destruct (Hctx x R Hlook) as [v [Henv [Hsubst [Hv Hrel]]]].
  exists v; repeat split; try assumption.
  unfold logical_value in Hrel |- *.
  eapply logical_relation_table_down with (n := n) (m := m) (j := m).
  - exact Hmn.
  - apply Nat.le_refl.
  - eapply logical_relation_table_index_down with (j := n); eauto.

Qed.

Lemma substitute_term_environment_int : forall rho n,
  substitute_term_environment rho (tm_int n) = tm_int n.
Proof.
  intros rho n; induction rho as [|[x v] rho IH]; simpl.
  - reflexivity.
  - rewrite IH; reflexivity.
Qed.

Lemma integer_self_equality_holds : forall n,
  qualifier_holds (Pred_Eq (tm_int n) (tm_int n)).
Proof.
  intros n. unfold qualifier_holds, predicate_holds, interpret_qualifier.
  simpl. exists (tm_int n). repeat split; try constructor.
Qed.

Lemma multi_integer_terminal : forall n v,
  multi (tm_int n) v -> v = tm_int n.
Proof.
  intros n v Hmulti. inversion Hmulti; subst; auto.
  inversion H.
Qed.

Lemma logical_integer_value_at_positive : forall fuel j rho n,
  0 < j -> j <= fuel ->
  logical_relation_table fuel j true rho
    (R_Refine Ty_Int (Pred_Eq (tm_bvar 0) (tm_int n))) (tm_int n).
Proof.
  intros fuel j rho n Hpos Hle.
  destruct fuel as [|fuel]; [lia|].
  destruct j as [|j]; [lia|].
  simpl. split; [exists n; reflexivity|]. split; [reflexivity|].
  split; [constructor|].
  unfold qualifier_holds, predicate_holds, interpret_qualifier.
  simpl. rewrite substitute_term_environment_int.
  exists (tm_int n). repeat split; try constructor.
Qed.

Lemma value_multi_identity : forall v u,
  value v -> multi v u -> u = v.
Proof.
  intros v u Hv Hmulti. induction Hmulti.
  - reflexivity.
  - exfalso. inversion Hv; subst; inversion H.
Qed.

Lemma logical_value_expression_environment : forall fuel rho R t v,
  substitute_term_environment rho t = v -> value v ->
  logical_value fuel rho R v -> logical_expression (S fuel) rho R t.
Proof.
  intros fuel rho R t v Hsubst Hv Hrel.
  unfold logical_expression, logical_value in *; simpl.
  split.
  - intros u Hmulti. rewrite Hsubst in Hmulti.
    left. rewrite (value_multi_identity v u Hv Hmulti). exact Hv.
  - intros u Hmulti Hu j Hj. rewrite Hsubst in Hmulti.
    rewrite (value_multi_identity v u Hv Hmulti).
    eapply logical_relation_table_index_down with (j := fuel); eauto.
Qed.

Lemma logical_value_expression_empty : forall fuel R v,
  value v -> logical_value fuel [] R v ->
  logical_expression (S fuel) [] R v.
Proof.
  intros fuel R v Hv Hrel. unfold logical_expression, logical_value in *.
  simpl. split.
  - intros u Hmulti. left.
    rewrite (value_multi_identity v u Hv Hmulti). exact Hv.
  - intros u Hmulti Hu j Hj.
    rewrite (value_multi_identity _ _ Hv Hmulti).
    eapply logical_relation_table_index_down with (j := fuel); eauto.
Qed.

Lemma multi_choice_inversion : forall t1 t2 u,
  multi (tm_choice t1 t2) u ->
  u = tm_choice t1 t2 \/ multi t1 u \/ multi t2 u.
Proof.
  intros t1 t2 u Hmulti. inversion Hmulti; subst.
  - left; reflexivity.
  - inversion H; subst.
    + right; left; assumption.
    + right; right; assumption.
Qed.

Lemma logical_expression_choice : forall fuel t1 t2 R,
  locally_closed_tm t1 -> locally_closed_tm t2 ->
  logical_expression (S (S fuel)) [] R t1 ->
  logical_expression (S (S fuel)) [] R t2 ->
  logical_expression (S fuel) [] R (tm_choice t1 t2).
Proof.
  intros fuel t1 t2 R Hlc1 Hlc2 Hsem1 Hsem2.
  unfold logical_expression in *; simpl in *.
  split.
  - intros u Hmulti. destruct (multi_choice_inversion _ _ _ Hmulti) as [->|[Hleft|Hright]].
    + right. exists t1. apply ST_ChoiceLeft; assumption.
    + exact (proj1 Hsem1 u Hleft).
    + exact (proj1 Hsem2 u Hright).
  - intros u Hmulti Hu j Hj.
    destruct (multi_choice_inversion _ _ _ Hmulti) as [->|[Hleft|Hright]].
    + inversion Hu.
    + pose proof (proj2 Hsem1 u Hleft Hu j (Nat.le_trans _ _ _ Hj (Nat.le_succ_diag_r fuel))) as Hrel.
      eapply logical_relation_table_down with (n := S fuel) (m := fuel) (j := j).
      * exact (Nat.le_succ_diag_r fuel).
      * exact Hj.
      * exact Hrel.
    + pose proof (proj2 Hsem2 u Hright Hu j (Nat.le_trans _ _ _ Hj (Nat.le_succ_diag_r fuel))) as Hrel.
      eapply logical_relation_table_down with (n := S fuel) (m := fuel) (j := j).
      * exact (Nat.le_succ_diag_r fuel).
      * exact Hj.
      * exact Hrel.
Qed.

Lemma logical_expression_integer : forall fuel rho n,
  logical_expression (S fuel) rho
    (R_Refine Ty_Int (Pred_Eq (tm_bvar 0) (tm_int n))) (tm_int n).
Proof.
  intros fuel rho n. unfold logical_expression. simpl.
  split.
  - intros u Hmulti. rewrite substitute_term_environment_int in Hmulti.
    left. rewrite (multi_integer_terminal _ _ Hmulti).
    constructor.
  - intros u Hmulti Hv j Hj.
    rewrite substitute_term_environment_int in Hmulti.
    rewrite (multi_integer_terminal _ _ Hmulti).
    destruct j as [|j].
    + destruct fuel; simpl; exact I.
    + eapply logical_integer_value_at_positive; [lia|exact Hj].
Qed.

Lemma logical_value_integer : forall fuel rho n,
  logical_value (S fuel) rho
    (R_Refine Ty_Int (Pred_Eq (tm_bvar 0) (tm_int n))) (tm_int n).
Proof.
  intros fuel rho n. simpl. split; [exists n; reflexivity|].
  split; [reflexivity|]. split; [constructor|].
  unfold qualifier_holds, predicate_holds, interpret_qualifier.
  simpl. rewrite substitute_term_environment_int.
  exists (tm_int n). repeat split; try constructor.
Qed.

Lemma logical_value_nonzero_integer : forall fuel v,
  logical_value (S fuel) []
    (R_Refine Ty_Int (Pred_Ne (tm_bvar 0) (tm_int 0%Z))) v ->
  exists n : Z, v = tm_int n /\ n <> 0%Z.
Proof.
  intros fuel v Hrel. simpl in Hrel.
  destruct Hrel as [[n ->] [Hfv [Hv Hq]]].
  exists n; split; [reflexivity|].
  apply integer_nonzero_of_refinement.
  exact Hq.
Qed.

Lemma logical_expression_safe_traces : forall fuel R t,
  logical_expression (S fuel) [] R t -> safe_traces t.
Proof. intros fuel R t H; exact (proj1 H). Qed.

Lemma logical_expression_values : forall fuel rho R t v,
  logical_expression (S fuel) rho R t ->
  multi (substitute_term_environment rho t) v -> value v ->
  logical_value fuel rho R v.
Proof.
  intros fuel rho R t v Hsem Hmulti Hv.
  exact (proj2 Hsem v Hmulti Hv fuel (Nat.le_refl fuel)).
Qed.

Lemma never_stuck_from_logical_expression : forall fuel t t' R,
  logical_expression (S fuel) [] R t -> multi t t' ->
  value t' \/ exists u, t' --> u.
Proof.
  intros fuel t t' R Hsem Hmulti.
  eapply (proj1 Hsem); simpl; eassumption.
Qed.

Lemma never_stuck_of_logical_fundamental : forall t t' R,
  (forall fuel, logical_expression (S fuel) [] R t) ->
  multi t t' -> value t' \/ exists u, t' --> u.
Proof.
  intros t t' R Hfund Hmulti.
  eapply never_stuck_from_logical_expression with (fuel := 0).
  - apply Hfund.
  - exact Hmulti.
Qed.

Lemma nonzero_refinement_excludes_zero_multi : forall t,
  qualifier_holds (Pred_Ne t (tm_int 0%Z)) ->
  multi t (tm_int 0%Z) -> False.
Proof.
  intros t Hq Hm.
  eapply nonzero_refinement_excludes_zero; eauto using multi_to_predicate_multistep.
Qed.

Lemma nonzero_survives_reduction_prefix : forall t u,
  qualifier_holds (Pred_Ne t (tm_int 0%Z)) ->
  multi t u -> multi u (tm_int 0%Z) -> False.
Proof.
  intros t u Hq Htu Hu0.
  eapply nonzero_refinement_excludes_zero_multi; [exact Hq|].
  eapply multi_trans; eassumption.
Qed.

Lemma multistep_progress_from_preservation :
  (forall t u R, has_rtype [] empty_rcontext t R -> t --> u ->
    exists S, has_rtype [] empty_rcontext u S) ->
  (forall t R, has_rtype [] empty_rcontext t R ->
    value t \/ exists u, t --> u) ->
  forall t t' R, has_rtype [] empty_rcontext t R -> multi t t' ->
    value t' \/ exists u, t' --> u.
Proof.
  intros Hpres Hprog t t' R Hty Hmulti.
  revert R Hty.
  induction Hmulti; intros R Hty.
  - eapply Hprog; eassumption.
  - destruct (Hpres t1 t2 R Hty H) as [S Hty2].
    eapply IHHmulti; eassumption.
Qed.

Theorem never_stuck : forall (t t' : tm) (R : rty),
  has_rtype [] empty_rcontext t R ->
  multi t t' ->
  value t' \/ exists t'' : tm, t' --> t''.
Proof.

Qed.

End SystemFRefinementNonDeterminismTask.
