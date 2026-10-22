From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
From Stdlib Require Import ZArith.BinInt.

Module SystemFRefinementIfNonDeterminism.

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
  | Ty_Int : ty
  | Ty_Bool : ty.

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
  | tm_choice : tm -> tm -> tm
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm -> tm -> tm -> tm.

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
  | Ty_Bool => Ty_Bool
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
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (open_tm_rec k u t1) (open_tm_rec k u t2) (open_tm_rec k u t3)
  end.

Definition open_tm (t u : tm) : tm := open_tm_rec 0 u t.

Fixpoint fv_ty (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow T1 T2 => fv_ty T1 ++ fv_ty T2
  | Ty_All T1 => fv_ty T1
  | Ty_Int => []
  | Ty_Bool => []
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
  | tm_true => []
  | tm_false => []
  | tm_if t1 t2 t3 => fv_tm t1 ++ fv_tm t2 ++ fv_tm t3
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
  | tm_true => []
  | tm_false => []
  | tm_if t1 t2 t3 => ftv_tm t1 ++ ftv_tm t2 ++ ftv_tm t3
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
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (open_tm_ty_rec k U t1) (open_tm_ty_rec k U t2) (open_tm_ty_rec k U t3)
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
  | Ty_Bool => Ty_Bool
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
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (tm_ty_subst X U t1) (tm_ty_subst X U t2) (tm_ty_subst X U t3)
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
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (tm_subst x s t1) (tm_subst x s t2) (tm_subst x s t3)
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
  | lc_ty_int : forall k, lc_ty_at k Ty_Int
  | lc_ty_bool : forall k, lc_ty_at k Ty_Bool.

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
      lc_tm_at K k t1 -> lc_tm_at K k t2 -> lc_tm_at K k (tm_choice t1 t2)
  | lc_tm_true : forall K k, lc_tm_at K k tm_true
  | lc_tm_false : forall K k, lc_tm_at K k tm_false
  | lc_tm_if : forall K k t1 t2 t3,
      lc_tm_at K k t1 -> lc_tm_at K k t2 -> lc_tm_at K k t3 ->
      lc_tm_at K k (tm_if t1 t2 t3).

Definition locally_closed_tm (t : tm) : Prop := lc_tm_at 0 0 t.

Inductive value : tm -> Prop :=
  | v_abs : forall T t,
      locally_closed_tm (tm_abs T t) ->
      value (tm_abs T t)
  | v_tabs : forall t,
      locally_closed_tm (tm_tabs t) ->
      value (tm_tabs t)
  | v_int : forall n : Z, value (tm_int n)
  | v_true : value tm_true
  | v_false : value tm_false.

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
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' -> locally_closed_tm t2 -> locally_closed_tm t3 ->
      tm_if t1 t2 t3 --> tm_if t1' t2 t3
  | ST_IfTrue : forall t2 t3,
      locally_closed_tm t2 -> locally_closed_tm t3 -> tm_if tm_true t2 t3 --> t2
  | ST_IfFalse : forall t2 t3,
      locally_closed_tm t2 -> locally_closed_tm t3 -> tm_if tm_false t2 t3 --> t3
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
  | WF_Int : forall Delta, wf_ty Delta Ty_Int
  | WF_Bool : forall Delta, wf_ty Delta Ty_Bool.

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
      has_type Delta Gamma (tm_choice t1 t2) T
  | T_True : forall Delta Gamma, has_type Delta Gamma tm_true Ty_Bool
  | T_False : forall Delta Gamma, has_type Delta Gamma tm_false Ty_Bool
  | T_If : forall Delta Gamma t1 t2 t3 T,
      has_type Delta Gamma t1 Ty_Bool -> has_type Delta Gamma t2 T ->
      has_type Delta Gamma t3 T -> has_type Delta Gamma (tm_if t1 t2 t3) T.

Fixpoint max_atom (L : list atom) : atom :=
  match L with
  | [] => 0
  | x :: L' => Nat.max x (max_atom L')
  end.

Definition fresh (L : list atom) : atom := S (max_atom L).

End SystemFRefinementIfNonDeterminism.

From Stdlib Require Import Arith.PeanoNat Lists.List ZArith.BinInt.
Module SystemFRefinementIfNonDeterminismLogic.
Import ListNotations SystemFRefinementIfNonDeterminism.

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

End SystemFRefinementIfNonDeterminismLogic.

From Stdlib Require Import Arith.PeanoNat Lists.List Lia ZArith.BinInt.
Module SystemFRefinementIfNonDeterminismTyping.
Import ListNotations.
Import SystemFRefinementIfNonDeterminism.
Export SystemFRefinementIfNonDeterminismLogic.

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
  | RT_True : forall Delta RGamma,
      has_rtype Delta RGamma tm_true (R_Refine Ty_Bool Pred_True)
  | RT_False : forall Delta RGamma,
      has_rtype Delta RGamma tm_false (R_Refine Ty_Bool Pred_True)
  | RT_If : forall Delta RGamma t1 t2 t3 R,
      has_rtype Delta RGamma t1 (R_Refine Ty_Bool Pred_True) ->
      has_rtype Delta RGamma t2 R -> has_rtype Delta RGamma t3 R ->
      has_rtype Delta RGamma (tm_if t1 t2 t3) R
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

End SystemFRefinementIfNonDeterminismTyping.

Module SystemFRefinementIfNonDeterminismErasure.
Import ListNotations.
Import SystemFRefinementIfNonDeterminism SystemFRefinementIfNonDeterminismTyping.

Lemma erase_open_rty_tm_rec : forall k u R,
  erase (open_rty_tm_rec k u R) = erase R.
Proof.
  intros k u R; revert k u; induction R; intros k u; simpl;
    try rewrite (IHR1 k u); try rewrite (IHR2 (S k) u);
    try rewrite (IHR k u); reflexivity.
Qed.

Lemma erase_open_rty_ty_rec : forall k U R,
  erase (open_rty_ty_rec k U R) = open_ty_rec k U (erase R).
Proof.
  intros k U R; revert k U; induction R; intros k U; simpl;
    try rewrite (IHR1 k U); try rewrite (IHR2 k U);
    try rewrite (IHR (S k) U); reflexivity.
Qed.

Inductive ty_shape : Type :=
  | Shape_Var | Shape_Int | Shape_Bool | Shape_Arrow | Shape_All.

Definition shape_ty (T : ty) : ty_shape :=
  match T with
  | Ty_BVar _ | Ty_FVar _ => Shape_Var
  | Ty_Int => Shape_Int
  | Ty_Bool => Shape_Bool
  | Ty_Arrow _ _ => Shape_Arrow
  | Ty_All _ => Shape_All
  end.

Lemma shape_open_rty_tm_rec : forall k u R,
  shape_ty (erase (open_rty_tm_rec k u R)) = shape_ty (erase R).
Proof.
  intros; rewrite erase_open_rty_tm_rec; reflexivity.
Qed.

Lemma max_atom_ge_in : forall L x, In x L -> x <= max_atom L.
Proof.
  induction L as [|a L IH]; simpl; intros x H; [contradiction|].
  destruct H as [H|H].
  - subst; apply Nat.le_max_l.
  - eapply Nat.le_trans; [apply IH; exact H|apply Nat.le_max_r].
Qed.

Lemma fresh_not_in : forall L, ~ In (fresh L) L.
Proof.
  intros L H; unfold fresh in H; apply max_atom_ge_in in H; lia.
Qed.

Lemma subtype_shape : forall Delta RGamma R S,
  subtype Delta RGamma R S -> shape_ty (erase R) = shape_ty (erase S).
Proof.
  intros Delta RGamma R S H; induction H; simpl in *; try congruence.
  - unfold open_rty_tm in IHsubtype.
    rewrite erase_open_rty_tm_rec in IHsubtype.
    exact IHsubtype.
  - specialize (H2 (fresh L) (fresh_not_in L)).
    unfold open_rty_tm in H2.
    rewrite shape_open_rty_tm_rec in H2.
    exact H2.
Qed.

Lemma open_ty_rec_injective_fresh : forall k T U X,
  ~ In X (fv_ty T ++ fv_ty U) ->
  open_ty_rec k (Ty_FVar X) T = open_ty_rec k (Ty_FVar X) U ->
  T = U.
Proof.
  intros k T; revert k; induction T; intros k U X Hfresh Heq;
    destruct U; simpl in *;
    repeat match goal with
    | H0 : context [if ?b then _ else _] |- _ => destruct b eqn:? in H0
    | |- context [if ?b then _ else _] => destruct b eqn:?
    end;
    simpl in *; try discriminate; try congruence;
    try solve [inversion Heq; subst; f_equal; eauto].
  - apply Nat.eqb_eq in Heqb. apply Nat.eqb_eq in Heqb0. congruence.
  - destruct (Nat.eqb k n) eqn:E; simpl in Heq; try discriminate.
    inversion Heq; subst. simpl in Hfresh; tauto.
  - destruct (Nat.eqb k n) eqn:E; simpl in Heq; try discriminate.
    inversion Heq; subst. simpl in Hfresh; tauto.
  - inversion Heq; subst. f_equal.
    + eapply IHT1.
      * intro Hin. apply in_app_iff in Hin as [Hin|Hin].
        -- apply Hfresh. apply in_or_app. left. apply in_or_app. left. exact Hin.
        -- apply Hfresh. apply in_or_app. right. apply in_or_app. left. exact Hin.
      * exact H0.
    + eapply IHT2.
      * intro Hin. apply in_app_iff in Hin as [Hin|Hin].
        -- apply Hfresh. apply in_or_app. left. apply in_or_app. right. exact Hin.
        -- apply Hfresh. apply in_or_app. right. apply in_or_app. right. exact Hin.
      * exact H1.
Qed.

Lemma subtype_erase_equal : forall Delta RGamma R S,
  subtype Delta RGamma R S -> erase R = erase S.
Proof.
  intros Delta RGamma R S Hsub. induction Hsub.
  - reflexivity.
  - reflexivity.
  - simpl. f_equal.
    + symmetry; assumption.
    + specialize (H0 (fresh L) (fresh_not_in L)).
      unfold open_rty_tm in H0. rewrite !erase_open_rty_tm_rec in H0.
      exact H0.
  - rewrite IHHsub. simpl. unfold open_rty_tm. apply erase_open_rty_tm_rec.
  - specialize (H2 (fresh L) (fresh_not_in L)).
    unfold open_rty_tm in H2. rewrite !erase_open_rty_tm_rec in H2.
    exact H2.
  - simpl. f_equal.
    set (X := fresh ((L ++ fv_ty (erase R)) ++ fv_ty (erase S))).
    assert (HxL : ~ In X L).
    { unfold X. intro Hin. apply (fresh_not_in
        ((L ++ fv_ty (erase R)) ++ fv_ty (erase S))).
      apply in_or_app. left. apply in_or_app. left. exact Hin. }
    assert (HxFS : ~ In X (fv_ty (erase R) ++ fv_ty (erase S))).
    { unfold X. intro Hin. apply in_app_iff in Hin as [Hin|Hin].
      - apply (fresh_not_in ((L ++ fv_ty (erase R)) ++ fv_ty (erase S))).
        apply in_or_app. left. apply in_or_app. right. exact Hin.
      - apply (fresh_not_in ((L ++ fv_ty (erase R)) ++ fv_ty (erase S))).
        apply in_or_app. right. exact Hin. }
    specialize (H0 X HxL).
    unfold open_rty_ty in H0. rewrite !erase_open_rty_ty_rec in H0.
    eapply open_ty_rec_injective_fresh with
      (k:=0) (X:=X).
    + exact HxFS.
    + exact H0.
  - etransitivity; eauto.
Qed.

Lemma core_value_arrow : forall Delta Gamma v T,
  has_type Delta Gamma v T -> value v -> shape_ty T = Shape_Arrow ->
  exists A body, v = tm_abs A body.
Proof.
  intros Delta Gamma v T Hty Hv Hshape.
  inversion Hv; subst; inversion Hty; subst; simpl in Hshape; try discriminate.
  eexists; eexists; reflexivity.
Qed.

Lemma core_value_poly : forall Delta Gamma v T,
  has_type Delta Gamma v T -> value v -> shape_ty T = Shape_All ->
  exists body, v = tm_tabs body.
Proof.
  intros Delta Gamma v T Hty Hv Hshape.
  inversion Hv; subst; inversion Hty; subst; simpl in Hshape; try discriminate.
  eexists; reflexivity.
Qed.

Lemma core_value_int : forall Delta Gamma v T,
  has_type Delta Gamma v T -> value v -> shape_ty T = Shape_Int ->
  exists n, v = tm_int n.
Proof.
  intros Delta Gamma v T Hty Hv Hshape.
  inversion Hv; subst; inversion Hty; subst; simpl in Hshape; try discriminate.
  eexists; reflexivity.
Qed.

Lemma core_value_bool : forall Delta Gamma v T,
  has_type Delta Gamma v T -> value v -> shape_ty T = Shape_Bool ->
  v = tm_true \/ v = tm_false.
Proof.
  intros Delta Gamma v T Hty Hv Hshape.
  inversion Hv; subst; inversion Hty; subst; simpl in Hshape; try discriminate; auto.
Qed.

Lemma lc_tm_open_var_inv : forall K k t x,
  lc_tm_at K k (open_tm_rec k (tm_fvar x) t) ->
  lc_tm_at K (S k) t.
Proof.
  intros K k t x; revert K k x; induction t; intros K k x Hlc; simpl in Hlc.
  - destruct (Nat.eqb k n) eqn:E.
    + constructor. apply Nat.eqb_eq in E; lia.
    + inversion Hlc; subst. constructor.
      apply Nat.eqb_neq in E; lia.
  - inversion Hlc; constructor.
  - inversion Hlc; subst. constructor; eauto.
  - inversion Hlc; subst. constructor; eauto.
  - inversion Hlc; subst. constructor. eauto.
  - inversion Hlc; subst. constructor; eauto.
  - inversion Hlc; constructor.
  - inversion Hlc; subst. constructor; eauto.
  - inversion Hlc; subst. constructor; eauto.
  - inversion Hlc; subst. constructor; eauto.
  - inversion Hlc; constructor.
  - inversion Hlc; constructor.
  - inversion Hlc; subst. constructor; eauto.
Qed.

Lemma lc_ty_open_fvar_inv : forall K k T X,
  k <= K ->
  lc_ty_at (S K) (open_ty_rec k (Ty_FVar X) T) ->
  lc_ty_at (S K) T.
Proof.
  intros K k T; revert K k; induction T; intros K k X Hle Hlc; simpl in Hlc.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; inversion Hlc; subst; constructor; lia.
    + inversion Hlc; subst; constructor; assumption.
  - inversion Hlc; constructor.
  - inversion Hlc; subst; constructor; eauto.
  - inversion Hlc; subst; constructor.
    eapply IHT with (K:=S K) (k:=S k) (X:=X); [lia|exact H1].
  - inversion Hlc; constructor.
  - inversion Hlc; constructor.
Qed.

Lemma wf_ty_lc : forall Delta T,
  wf_ty Delta T -> lc_ty_at (length Delta) T.
Proof.
  intros Delta T H; induction H.
  - constructor.
  - constructor; assumption.
  - constructor.
    specialize (H0 (fresh L) (fresh_not_in L)).
    unfold open_ty in H0.
    eapply lc_ty_open_fvar_inv with (K:=length Delta) (k:=0) (X:=fresh L).
    + lia.
    + simpl in H0. exact H0.
  - constructor.
  - constructor.
Qed.

Lemma wf_rty_erase : forall Delta RGamma R,
  wf_rty Delta RGamma R -> wf_ty Delta (erase R).
Proof.
  intros Delta RGamma R H; induction H; simpl.
  - assumption.
  - constructor; [assumption|].
    specialize (H1 (fresh L) (fresh_not_in L)).
    unfold open_rty_tm in H1.
    rewrite erase_open_rty_tm_rec in H1. exact H1.
  -
    specialize (H1 (fresh L) (fresh_not_in L)).
    unfold open_rty_tm in H1.
    rewrite erase_open_rty_tm_rec in H1. exact H1.
  - apply WF_All with (L:=L).
    intros X HX.
    specialize (H0 X HX).
    unfold open_rty_ty in H0.
    rewrite erase_open_rty_ty_rec in H0. exact H0.
Qed.

Lemma lc_tm_ty_open_inv : forall K k j t X,
  k <= K ->
  lc_tm_at (S K) j (open_tm_ty_rec k (Ty_FVar X) t) ->
  lc_tm_at (S K) j t.
Proof.
  intros K k j t; revert K k j; induction t; intros K k j X Hle Hlc; simpl in Hlc.
  - inversion Hlc; constructor; assumption.
  - inversion Hlc; constructor.
  - inversion Hlc; subst. constructor.
    + eapply lc_ty_open_fvar_inv; eauto.
    + eapply IHt; eauto.
  - inversion Hlc; subst. constructor; eauto.
  - inversion Hlc; subst. constructor.
    eapply IHt with (K:=S K) (k:=S k) (j:=j) (X:=X); eauto; lia.
  - inversion Hlc; subst. constructor; eauto.
    eapply lc_ty_open_fvar_inv; eauto.
  - inversion Hlc; constructor.
  - inversion Hlc; subst. constructor; eauto.
  - inversion Hlc; subst. constructor; eauto.
  - inversion Hlc; subst. constructor; eauto.
  - inversion Hlc; constructor.
  - inversion Hlc; constructor.
  - inversion Hlc; subst. constructor; eauto.
Qed.

Lemma lc_ty_mono : forall K K' T,
  K <= K' -> lc_ty_at K T -> lc_ty_at K' T.
Proof.
  intros K K' T Hle Hlc; revert K' Hle.
  induction Hlc; intros K' Hle.
  - constructor; lia.
  - constructor.
  - constructor; eauto.
  - constructor. apply IHHlc; lia.
  - constructor.
  - constructor.
Qed.

Lemma lc_tm_mono : forall K K' k t,
  K <= K' -> lc_tm_at K k t -> lc_tm_at K' k t.
Proof.
  intros K K' k t Hle Hlc; revert K' Hle.
  induction Hlc; intros K' Hle.
  - constructor; assumption.
  - constructor.
  - constructor.
    + eapply lc_ty_mono; eauto.
    + eapply IHHlc; eauto.
  - constructor; eauto.
  - constructor. eapply IHHlc; lia.
  - constructor; eauto using lc_ty_mono.
  - constructor.
  - constructor; eauto.
  - constructor; eauto.
  - constructor; eauto.
  - constructor.
  - constructor.
  - constructor; eauto.
Qed.

Lemma value_lc_tm : forall v, value v -> locally_closed_tm v.
Proof.
  intros v H; inversion H; subst; try assumption; constructor.
Qed.

Lemma has_rtype_lc_tm : forall Delta RGamma t R,
  has_rtype Delta RGamma t R -> lc_tm_at (length Delta) 0 t.
Proof.
  intros Delta RGamma t R H; induction H; simpl.
  - constructor.
  - constructor.
    + apply wf_ty_lc. eapply wf_rty_erase; eauto.
    + specialize (H1 (fresh L) (fresh_not_in L)).
      unfold open_tm in H1.
      apply lc_tm_open_var_inv in H1. exact H1.
  - constructor; assumption.
  - constructor.
    specialize (H0 (fresh L) (fresh_not_in L)).
    unfold open_tm_ty in H0.
    eapply lc_tm_ty_open_inv with (K:=length Delta) (k:=0) (j:=0) (X:=fresh L).
    + lia.
    + exact H0.
  - constructor; [assumption|].
    apply wf_ty_lc; assumption.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; assumption.
  - constructor.
  - constructor.
  - constructor; assumption.
  - eapply lc_tm_mono with (K:=0); [lia|].
    apply value_lc_tm; assumption.
  - assumption.
Qed.

Lemma entails_sound_true_singleton : forall Delta x T p q,
  entails Delta [(x, R_Refine T Pred_True)] p q ->
  forall atoms, interpret_qualifier atoms p -> interpret_qualifier atoms q.
Proof.
  intros Delta x T p q H.
  remember [(x, R_Refine T Pred_True)] as G eqn:HG in H.
  induction H; intros atoms Hp; simpl in *;
    try tauto.
  - eapply (IHentails2 HG). eapply (IHentails1 HG). exact Hp.
  - split; [eapply (IHentails1 HG)|eapply (IHentails2 HG)]; exact Hp.
  - destruct Hp as [Hp|Hp]; [eapply (IHentails1 HG)|eapply (IHentails2 HG)]; assumption.
  - intro Hq. apply (IHentails HG atoms). simpl. tauto.
  - rewrite HG in H. simpl in H.
    destruct (Nat.eqb x0 x) eqn:E; inversion H; subst; simpl; tauto.
Qed.

Lemma notin_app_left : forall (x : atom) (l1 l2 : list atom),
  ~ In x (l1 ++ l2) -> ~ In x l1.
Proof. intros x l1 l2 H Hin; apply H; apply in_or_app; left; exact Hin. Qed.

Lemma notin_app_right : forall (x : atom) (l1 l2 : list atom),
  ~ In x (l1 ++ l2) -> ~ In x l2.
Proof. intros x l1 l2 H Hin; apply H; apply in_or_app; right; exact Hin. Qed.

Lemma tm_subst_open_rec_fresh : forall t k x s u,
  ~ In x (fv_tm t) ->
  tm_subst x s (open_tm_rec k u t) =
  open_tm_rec k (tm_subst x s u) t.
Proof.
  intros t; induction t; intros k x s u Hfresh; simpl in *.
  - destruct (Nat.eqb k n); reflexivity.
  - simpl in Hfresh. destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E; subst; exfalso; apply Hfresh; left; reflexivity.
    + reflexivity.
  - f_equal. apply IHt. exact Hfresh.
  - unfold open_qualifier_tm, open_qualifier_tm_rec, open_pred_tm; simpl. f_equal.
    + apply IHt1. eapply notin_app_left; exact Hfresh.
    + apply IHt2. eapply notin_app_right; exact Hfresh.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal. apply IHt. exact Hfresh.
  - reflexivity.
  - unfold open_qualifier_tm, open_qualifier_tm_rec, open_pred_tm; simpl. f_equal.
    + apply IHt1. eapply notin_app_left; exact Hfresh.
    + apply IHt2. eapply notin_app_right; exact Hfresh.
  - f_equal.
    + apply IHt1. eapply notin_app_left; exact Hfresh.
    + apply IHt2. eapply notin_app_right; exact Hfresh.
  - f_equal.
    + apply IHt1. eapply notin_app_left; exact Hfresh.
    + apply IHt2. eapply notin_app_right; exact Hfresh.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + apply IHt1. eapply notin_app_left; exact Hfresh.
    + apply IHt2. eapply notin_app_left. eapply notin_app_right; exact Hfresh.
    + apply IHt3. eapply notin_app_right. eapply notin_app_right; exact Hfresh.
Qed.

Lemma tm_subst_open_var_rec_fresh : forall t k x s,
  ~ In x (fv_tm t) ->
  tm_subst x s (open_tm_rec k (tm_fvar x) t) = open_tm_rec k s t.
Proof.
  intros. rewrite tm_subst_open_rec_fresh by assumption.
  simpl. rewrite Nat.eqb_refl. reflexivity.
Qed.

Fixpoint fv_qualifier (q : qualifier) : list atom :=
  match q with
  | Pred_True | Pred_False => []
  | Pred_Eq t1 t2 | Pred_Lt t1 t2 | Pred_Le t1 t2 => fv_tm t1 ++ fv_tm t2
  | Pred_And p q | Pred_Or p q => fv_qualifier p ++ fv_qualifier q
  | Pred_Not p => fv_qualifier p
  end.

Lemma qualifier_subst_open_fresh : forall q x s,
  ~ In x (fv_qualifier q) ->
  qualifier_subst x s (open_qualifier_tm q (tm_fvar x)) =
  open_qualifier_tm q s.
Proof.
  induction q; intros x s Hfresh; simpl in *; try reflexivity.
  - unfold open_qualifier_tm, open_qualifier_tm_rec, open_pred_tm; simpl. f_equal.
    + apply tm_subst_open_var_rec_fresh. eapply notin_app_left; exact Hfresh.
    + apply tm_subst_open_var_rec_fresh. eapply notin_app_right; exact Hfresh.
  - unfold open_qualifier_tm, open_qualifier_tm_rec, open_pred_tm; simpl. f_equal.
    + apply tm_subst_open_var_rec_fresh. eapply notin_app_left; exact Hfresh.
    + apply tm_subst_open_var_rec_fresh. eapply notin_app_right; exact Hfresh.
  - unfold open_qualifier_tm, open_qualifier_tm_rec, open_pred_tm; simpl. f_equal.
    + apply tm_subst_open_var_rec_fresh. eapply notin_app_left; exact Hfresh.
    + apply tm_subst_open_var_rec_fresh. eapply notin_app_right; exact Hfresh.
  - unfold open_qualifier_tm, open_qualifier_tm_rec, open_pred_tm; simpl.
    f_equal.
    + apply IHq1. eapply notin_app_left; exact Hfresh.
    + apply IHq2. eapply notin_app_right; exact Hfresh.
  - unfold open_qualifier_tm, open_qualifier_tm_rec, open_pred_tm; simpl.
    f_equal.
    + apply IHq1. eapply notin_app_left; exact Hfresh.
    + apply IHq2. eapply notin_app_right; exact Hfresh.
  - unfold open_qualifier_tm, open_qualifier_tm_rec, open_pred_tm; simpl.
    f_equal. apply IHq. exact Hfresh.
Qed.

Definition substituted_atoms (x : atom) (v : tm) : atom_interpretation := {| 
  interpret_eq := fun t1 t2 => interpret_eq operational_atoms (tm_subst x v t1) (tm_subst x v t2);
  interpret_lt := fun t1 t2 => interpret_lt operational_atoms (tm_subst x v t1) (tm_subst x v t2);
  interpret_le := fun t1 t2 => interpret_le operational_atoms (tm_subst x v t1) (tm_subst x v t2)
|}.

Lemma interpret_substituted_atoms : forall x v q,
  interpret_qualifier (substituted_atoms x v) q =
  qualifier_holds (qualifier_subst x v q).
Proof.
  intros x v q; induction q; simpl; try reflexivity.
  - rewrite IHq1, IHq2; reflexivity.
  - rewrite IHq1, IHq2; reflexivity.
  - rewrite IHq; reflexivity.
Qed.

Lemma entails_instantiated_true_singleton : forall Delta x T p q v,
  ~ In x (fv_qualifier p) ->
  ~ In x (fv_qualifier q) ->
  entails Delta [(x, R_Refine T Pred_True)]
    (open_qualifier_tm p (tm_fvar x))
    (open_qualifier_tm q (tm_fvar x)) ->
  qualifier_holds (open_qualifier_tm p v) ->
  qualifier_holds (open_qualifier_tm q v).
Proof.
  intros Delta x T p q v Hfp Hfq Hent Hp.
  pose proof (entails_sound_true_singleton Delta x T
    (open_qualifier_tm p (tm_fvar x))
    (open_qualifier_tm q (tm_fvar x)) Hent
    (substituted_atoms x v)) as Hsound.
  assert (Hsource : interpret_qualifier (substituted_atoms x v)
      (open_qualifier_tm p (tm_fvar x))).
  { rewrite interpret_substituted_atoms.
    rewrite qualifier_subst_open_fresh by exact Hfp.
    exact Hp. }
  specialize (Hsound Hsource).
  rewrite interpret_substituted_atoms in Hsound.
  rewrite qualifier_subst_open_fresh in Hsound by exact Hfq.
  exact Hsound.
Qed.

Lemma entails_sound_singleton_refinement : forall x T p q r,
  entails [] [(x, R_Refine T p)] q r ->
  forall atoms,
    interpret_qualifier atoms (open_qualifier_tm p (tm_fvar x)) ->
    interpret_qualifier atoms q -> interpret_qualifier atoms r.
Proof.
  intros x T p q r Hent.
  remember [(x, R_Refine T p)] as G eqn:HG in Hent.
  induction Hent; intros atoms Hctx Hq; simpl in *; try tauto.
  - eapply (IHHent2 HG atoms Hctx).
    eapply (IHHent1 HG atoms Hctx). exact Hq.
  - split; [eapply (IHHent1 HG atoms Hctx)|eapply (IHHent2 HG atoms Hctx)]; exact Hq.
  - destruct Hq as [Hq|Hq];
      [eapply (IHHent1 HG atoms Hctx)|eapply (IHHent2 HG atoms Hctx)]; assumption.
  - intro Hr. apply (IHHent HG atoms Hctx). simpl. tauto.
  - rewrite HG in H. simpl in H.
    destruct (Nat.eqb x0 x) eqn:E; inversion H; subst.
    apply Nat.eqb_eq in E; subst x0. exact Hctx.
Qed.

Lemma entails_instantiated_singleton_refinement : forall x T p q r v,
  ~ In x (fv_qualifier p) ->
  ~ In x (fv_qualifier q) ->
  ~ In x (fv_qualifier r) ->
  entails [] [(x, R_Refine T p)]
    (open_qualifier_tm q (tm_fvar x))
    (open_qualifier_tm r (tm_fvar x)) ->
  qualifier_holds (open_qualifier_tm p v) ->
  qualifier_holds (open_qualifier_tm q v) ->
  qualifier_holds (open_qualifier_tm r v).
Proof.
  intros x T p q r v Hfp Hfq Hfr Hent Hp Hq.
  pose proof (entails_sound_singleton_refinement x T p
    (open_qualifier_tm q (tm_fvar x))
    (open_qualifier_tm r (tm_fvar x)) Hent
    (substituted_atoms x v)) as Hsound.
  assert (Hctx : interpret_qualifier (substituted_atoms x v)
      (open_qualifier_tm p (tm_fvar x))).
  { rewrite interpret_substituted_atoms.
    rewrite qualifier_subst_open_fresh by exact Hfp. exact Hp. }
  assert (Hsource : interpret_qualifier (substituted_atoms x v)
      (open_qualifier_tm q (tm_fvar x))).
  { rewrite interpret_substituted_atoms.
    rewrite qualifier_subst_open_fresh by exact Hfq. exact Hq. }
  specialize (Hsound Hctx Hsource).
  rewrite interpret_substituted_atoms in Hsound.
  rewrite qualifier_subst_open_fresh in Hsound by exact Hfr.
  exact Hsound.
Qed.

Lemma refine_entails_value_sound : forall L T p q v,
  (forall x, ~ In x L ->
    entails [] [(x, R_Refine T Pred_True)]
      (open_qualifier_tm p (tm_fvar x))
      (open_qualifier_tm q (tm_fvar x))) ->
  qualifier_holds (open_qualifier_tm p v) ->
  qualifier_holds (open_qualifier_tm q v).
Proof.
  intros L T p q v Hent Hp.
  set (x := fresh ((L ++ fv_qualifier p) ++ fv_qualifier q)).
  assert (Hbig : ~ In x ((L ++ fv_qualifier p) ++ fv_qualifier q)).
  { unfold x; apply fresh_not_in. }
  assert (HxL : ~ In x L).
  { intro H; apply Hbig; apply in_or_app; left; apply in_or_app; left; exact H. }
  assert (Hleft : ~ In x (L ++ fv_qualifier p)).
  { eapply notin_app_left; exact Hbig. }
  assert (Hxp : ~ In x (fv_qualifier p)).
  { eapply notin_app_right; exact Hleft. }
  assert (Hxq : ~ In x (fv_qualifier q)).
  { eapply notin_app_right; exact Hbig. }
  specialize (Hent x HxL).
  exact (@entails_instantiated_true_singleton [] x T p q v Hxp Hxq Hent Hp).
Qed.

Lemma predicate_multistep_prepend : forall t t' v,
  t --> t' -> predicate_multistep t' v -> predicate_multistep t v.
Proof. intros; econstructor; eauto. Qed.

Lemma operational_equality_prepend_left : forall t t' u,
  t --> t' -> interpret_eq operational_atoms t' u ->
  interpret_eq operational_atoms t u.
Proof.
  intros t t' u Hstep [v [Ht [Hu Hv]]].
  exists v. split; [eapply predicate_multistep_prepend; eauto|].
  split; assumption.
Qed.

Lemma nonzero_refinement_step : forall t t',
  t --> t' ->
  qualifier_holds (Pred_Ne t (tm_int 0%Z)) ->
  qualifier_holds (Pred_Ne t' (tm_int 0%Z)).
Proof.
  intros t t' Hstep Hne. unfold qualifier_holds, predicate_holds in *.
  simpl in *. intro Heq. apply Hne.
  eapply operational_equality_prepend_left; eauto.
Qed.

End SystemFRefinementIfNonDeterminismErasure.

Module SystemFRefinementIfNonDeterminismEvaluation.
Import ListNotations SystemFRefinementIfNonDeterminism SystemFRefinementIfNonDeterminismLogic SystemFRefinementIfNonDeterminismTyping.

Inductive multi : tm -> tm -> Prop :=
  | multi_refl : forall t, multi t t
  | multi_step : forall t1 t2 t3,
      t1 --> t2 -> multi t2 t3 -> multi t1 t3.
Notation "t '-->*' u" := (multi t u) (at level 40).

Lemma multi_trans : forall t u v, multi t u -> multi u v -> multi t v.
Proof.
  intros t u v Htu Huv. induction Htu; eauto using multi.
Qed.

End SystemFRefinementIfNonDeterminismEvaluation.

Module SystemFRefinementIfNonDeterminismTask.
Import ListNotations SystemFRefinementIfNonDeterminism SystemFRefinementIfNonDeterminismLogic SystemFRefinementIfNonDeterminismTyping SystemFRefinementIfNonDeterminismErasure SystemFRefinementIfNonDeterminismEvaluation.

Fixpoint lookup_tm_environment (x : atom) (rho : list (atom * tm)) : option tm :=
  match rho with
  | [] => None
  | (y, v) :: rho' =>
      if Nat.eqb x y then Some v else lookup_tm_environment x rho'
  end.

Fixpoint tm_subst_environment (rho : list (atom * tm)) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => match lookup_tm_environment x rho with
      | Some v => v | None => tm_fvar x end
  | tm_abs T b => tm_abs T (tm_subst_environment rho b)
  | tm_app t1 t2 => tm_app (tm_subst_environment rho t1) (tm_subst_environment rho t2)
  | tm_tabs b => tm_tabs (tm_subst_environment rho b)
  | tm_tapp t1 T => tm_tapp (tm_subst_environment rho t1) T
  | tm_int n => tm_int n
  | tm_div t1 t2 => tm_div (tm_subst_environment rho t1) (tm_subst_environment rho t2)
  | tm_arith op t1 t2 => tm_arith op (tm_subst_environment rho t1) (tm_subst_environment rho t2)
  | tm_choice t1 t2 => tm_choice (tm_subst_environment rho t1) (tm_subst_environment rho t2)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (tm_subst_environment rho t1)
      (tm_subst_environment rho t2) (tm_subst_environment rho t3)
  end.

Definition environment_atoms (rho : list (atom * tm)) : atom_interpretation :=
  match rho with
  | [] => operational_atoms
  | _ => {| 
      interpret_eq := fun t1 t2 =>
        interpret_eq operational_atoms
          (tm_subst_environment rho t1) (tm_subst_environment rho t2);
      interpret_lt := fun t1 t2 =>
        interpret_lt operational_atoms
          (tm_subst_environment rho t1) (tm_subst_environment rho t2);
      interpret_le := fun t1 t2 =>
        interpret_le operational_atoms
          (tm_subst_environment rho t1) (tm_subst_environment rho t2)
    |}
  end.

Lemma tm_subst_environment_fvar : forall rho x v,
  lookup_tm_environment x rho = Some v ->
  tm_subst_environment rho (tm_fvar x) = v.
Proof. intros; simpl; now rewrite H. Qed.

Lemma tm_subst_environment_extend_fresh : forall t x v rho,
  ~ In x (fv_tm t) ->
  tm_subst_environment ((x,v)::rho) t = tm_subst_environment rho t.
Proof.
  induction t; intros x v rho Hfresh; simpl in *; try reflexivity.
  - destruct (Nat.eqb a x) eqn:E.
    + apply Nat.eqb_eq in E; subst. exfalso. apply Hfresh. simpl; auto.
    + reflexivity.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal.
    + apply IHt1. eapply notin_app_left; exact Hfresh.
    + apply IHt2. eapply notin_app_right; exact Hfresh.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal.
    + apply IHt1. eapply notin_app_left; exact Hfresh.
    + apply IHt2. eapply notin_app_right; exact Hfresh.
  - f_equal.
    + apply IHt1. eapply notin_app_left; exact Hfresh.
    + apply IHt2. eapply notin_app_right; exact Hfresh.
  - f_equal.
    + apply IHt1. eapply notin_app_left; exact Hfresh.
    + apply IHt2. eapply notin_app_right; exact Hfresh.
  - f_equal.
    + apply IHt1. eapply notin_app_left; exact Hfresh.
    + apply IHt2. eapply notin_app_left. eapply notin_app_right; exact Hfresh.
    + apply IHt3. eapply notin_app_right. eapply notin_app_right; exact Hfresh.
Qed.

Lemma tm_subst_environment_empty : forall t,
  tm_subst_environment [] t = t.
Proof.
  induction t; simpl; try reflexivity; try rewrite IHt; try rewrite IHt1;
    try rewrite IHt2; try rewrite IHt3; reflexivity.
Qed.

Lemma qualifier_environment_extend_fresh : forall q x v rho,
  ~ In x (fv_qualifier q) ->
  interpret_qualifier (environment_atoms ((x,v)::rho)) q =
  interpret_qualifier (environment_atoms rho) q.
Proof.
  induction q; intros x v rho Hfresh; simpl in *; try reflexivity.
  - destruct rho as [|[y w] rho']; unfold environment_atoms; simpl.
    + rewrite (tm_subst_environment_extend_fresh t x v []
        (notin_app_left x (fv_tm t) (fv_tm t0) Hfresh)).
      rewrite (tm_subst_environment_extend_fresh t0 x v []
        (notin_app_right x (fv_tm t) (fv_tm t0) Hfresh)).
      rewrite !tm_subst_environment_empty. reflexivity.
    + rewrite (tm_subst_environment_extend_fresh t x v ((y,w)::rho')
        (notin_app_left x (fv_tm t) (fv_tm t0) Hfresh)).
      rewrite (tm_subst_environment_extend_fresh t0 x v ((y,w)::rho')
        (notin_app_right x (fv_tm t) (fv_tm t0) Hfresh)).
      reflexivity.
  - destruct rho as [|[y w] rho']; unfold environment_atoms; simpl.
    + rewrite (tm_subst_environment_extend_fresh t x v []
        (notin_app_left x (fv_tm t) (fv_tm t0) Hfresh)).
      rewrite (tm_subst_environment_extend_fresh t0 x v []
        (notin_app_right x (fv_tm t) (fv_tm t0) Hfresh)).
      rewrite !tm_subst_environment_empty. reflexivity.
    + rewrite (tm_subst_environment_extend_fresh t x v ((y,w)::rho')
        (notin_app_left x (fv_tm t) (fv_tm t0) Hfresh)).
      rewrite (tm_subst_environment_extend_fresh t0 x v ((y,w)::rho')
        (notin_app_right x (fv_tm t) (fv_tm t0) Hfresh)).
      reflexivity.
  - destruct rho as [|[y w] rho']; unfold environment_atoms; simpl.
    + rewrite (tm_subst_environment_extend_fresh t x v []
        (notin_app_left x (fv_tm t) (fv_tm t0) Hfresh)).
      rewrite (tm_subst_environment_extend_fresh t0 x v []
        (notin_app_right x (fv_tm t) (fv_tm t0) Hfresh)).
      rewrite !tm_subst_environment_empty. reflexivity.
    + rewrite (tm_subst_environment_extend_fresh t x v ((y,w)::rho')
        (notin_app_left x (fv_tm t) (fv_tm t0) Hfresh)).
      rewrite (tm_subst_environment_extend_fresh t0 x v ((y,w)::rho')
        (notin_app_right x (fv_tm t) (fv_tm t0) Hfresh)).
      reflexivity.
  - rewrite IHq1 by (eapply notin_app_left; exact Hfresh).
    rewrite IHq2 by (eapply notin_app_right; exact Hfresh). reflexivity.
  - rewrite IHq1 by (eapply notin_app_left; exact Hfresh).
    rewrite IHq2 by (eapply notin_app_right; exact Hfresh). reflexivity.
  - rewrite IHq by exact Hfresh. reflexivity.
Qed.

Lemma tm_subst_environment_open_rec : forall t k rho x v,
  lookup_tm_environment x rho = Some v ->
  tm_subst_environment rho v = v ->
  tm_subst_environment rho (open_tm_rec k (tm_fvar x) t) =
  tm_subst_environment rho (open_tm_rec k v t).
Proof.
  induction t; intros k rho x v Hlookup Hfixed; simpl.
  - destruct (Nat.eqb k n); simpl.
    + rewrite Hlookup. symmetry. exact Hfixed.
    + reflexivity.
  - reflexivity.
  - f_equal. apply IHt; assumption.
  - f_equal.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
  - f_equal. apply IHt; assumption.
  - f_equal. apply IHt; assumption.
  - reflexivity.
  - f_equal.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
  - f_equal.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
  - f_equal.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
    + apply IHt3; assumption.
Qed.

Lemma environment_interpret_open_qualifier : forall p k rho x v,
  lookup_tm_environment x rho = Some v ->
  tm_subst_environment rho v = v ->
  interpret_qualifier (environment_atoms rho)
      (open_qualifier_tm_rec k (tm_fvar x) p) =
  interpret_qualifier (environment_atoms rho)
      (open_qualifier_tm_rec k v p).
Proof.
  induction p; intros k rho x v Hlookup Hfixed; simpl; try reflexivity.
  - destruct rho as [|[y w] rho']; simpl in Hlookup; [discriminate|].
    unfold environment_atoms; simpl.
    rewrite (tm_subst_environment_open_rec t k ((y,w)::rho') x v Hlookup Hfixed).
    rewrite (tm_subst_environment_open_rec t0 k ((y,w)::rho') x v Hlookup Hfixed).
    reflexivity.
  - destruct rho as [|[y w] rho']; simpl in Hlookup; [discriminate|].
    unfold environment_atoms; simpl.
    rewrite (tm_subst_environment_open_rec t k ((y,w)::rho') x v Hlookup Hfixed).
    rewrite (tm_subst_environment_open_rec t0 k ((y,w)::rho') x v Hlookup Hfixed).
    reflexivity.
  - destruct rho as [|[y w] rho']; simpl in Hlookup; [discriminate|].
    unfold environment_atoms; simpl.
    rewrite (tm_subst_environment_open_rec t k ((y,w)::rho') x v Hlookup Hfixed).
    rewrite (tm_subst_environment_open_rec t0 k ((y,w)::rho') x v Hlookup Hfixed).
    reflexivity.
  - rewrite (IHp1 k rho x v Hlookup Hfixed).
    rewrite (IHp2 k rho x v Hlookup Hfixed). reflexivity.
  - rewrite (IHp1 k rho x v Hlookup Hfixed).
    rewrite (IHp2 k rho x v Hlookup Hfixed). reflexivity.
  - rewrite (IHp k rho x v Hlookup Hfixed). reflexivity.
Qed.

Fixpoint logical_relation (fuel : nat) (rho : list (atom * tm))
    (R : rty) (v : tm) : Prop :=
  match fuel with
  | 0 => True
  | S fuel' =>
      match R with
      | R_Refine T p =>
          value v /\ interpret_qualifier (environment_atoms rho)
            (open_qualifier_tm p v)
      | R_Func R1 R2 =>
          value v /\ forall w, logical_relation fuel' rho R1 w ->
            exists u, multi (tm_app v w) u /\
              logical_relation fuel' rho (open_rty_tm R2 w) u
      | R_Exists R1 R2 =>
          value v /\ exists w, value w /\ logical_relation fuel' rho R1 w /\
            logical_relation fuel' rho (open_rty_tm R2 w) v
      | R_Poly R1 =>
          value v /\ forall U, locally_closed_ty U ->
            exists u, multi (tm_tapp v U) u /\
              logical_relation fuel' rho (open_rty_ty R1 U) u
      end
  end.

Definition context_interpretation (fuel : nat) (RGamma : rcontext)
    (rho : list (atom * tm)) : Prop :=
  forall x R, lookup_rcontext x RGamma = Some R ->
    exists v, lookup_tm_environment x rho = Some v /\
      tm_subst_environment rho v = v /\ value v /\
      logical_relation fuel rho R v.

Definition context_facts (RGamma : rcontext)
    (atoms : atom_interpretation) : Prop :=
  forall x T p, lookup_rcontext x RGamma = Some (R_Refine T p) ->
    interpret_qualifier atoms (open_qualifier_tm p (tm_fvar x)).

Lemma context_facts_empty : forall atoms, context_facts [] atoms.
Proof. intros atoms x T p H; discriminate. Qed.

Lemma context_facts_update : forall RGamma atoms x T p,
  context_facts RGamma atoms ->
  interpret_qualifier atoms (open_qualifier_tm p (tm_fvar x)) ->
  context_facts (update_rcontext RGamma x (R_Refine T p)) atoms.
Proof.
  intros RGamma atoms x T p Hctx Hnew y U q Hlookup.
  simpl in Hlookup. destruct (Nat.eqb y x) eqn:E.
  - inversion Hlookup; subst. apply Nat.eqb_eq in E; subst y. exact Hnew.
  - eapply Hctx. exact Hlookup.
Qed.

Lemma context_facts_environment_extend : forall RGamma rho x v,
  context_facts RGamma (environment_atoms rho) ->
  (forall y T p, lookup_rcontext y RGamma = Some (R_Refine T p) ->
    ~ In x (fv_qualifier (open_qualifier_tm p (tm_fvar y)))) ->
  context_facts RGamma (environment_atoms ((x,v)::rho)).
Proof.
  intros RGamma rho x v Hctx Hfresh y T p Hlookup.
  rewrite (qualifier_environment_extend_fresh
    (open_qualifier_tm p (tm_fvar y)) x v rho (Hfresh y T p Hlookup)).
  eapply Hctx. exact Hlookup.
Qed.

Lemma context_facts_extend_value : forall fuel RGamma rho x v R,
  context_facts RGamma (environment_atoms rho) ->
  (forall y T p, lookup_rcontext y RGamma = Some (R_Refine T p) ->
    ~ In x (fv_qualifier (open_qualifier_tm p (tm_fvar y)))) ->
  tm_subst_environment ((x,v)::rho) v = v ->
  logical_relation (S fuel) ((x,v)::rho) R v ->
  context_facts (update_rcontext RGamma x R)
    (environment_atoms ((x,v)::rho)).
Proof.
  intros fuel RGamma rho x v R Hctx Hfresh Hfixed Hrel y T p Hlookup.
  simpl in Hlookup. destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E; subst y.
    destruct R; simpl in Hlookup; try discriminate;
      inversion Hlookup; subst.
    simpl in Hrel. destruct Hrel as [_ Hqual].
    assert (Henv : lookup_tm_environment x ((x,v)::rho) = Some v).
    { simpl. rewrite Nat.eqb_refl. reflexivity. }
    pose proof (environment_interpret_open_qualifier p 0
      ((x,v)::rho) x v Henv Hfixed) as Hopen.
    unfold open_qualifier_tm in Hqual |- *. rewrite Hopen. exact Hqual.
  - pose proof (context_facts_environment_extend RGamma rho x v Hctx Hfresh) as Hext.
    eapply Hext. exact Hlookup.
Qed.

Lemma entails_sound_in_context : forall Delta RGamma p q,
  entails Delta RGamma p q -> forall atoms,
  context_facts RGamma atoms -> interpret_qualifier atoms p ->
  interpret_qualifier atoms q.
Proof.
  intros Delta RGamma p q Hent.
  induction Hent; intros atoms Hctx Hp; simpl in *; try tauto.
  - eapply (IHHent2 atoms Hctx). eapply (IHHent1 atoms Hctx). exact Hp.
  - split; [eapply (IHHent1 atoms Hctx)|eapply (IHHent2 atoms Hctx)]; exact Hp.
  - destruct Hp as [Hp|Hp];
      [eapply (IHHent1 atoms Hctx)|eapply (IHHent2 atoms Hctx)]; assumption.
  - intro Hq. apply (IHHent atoms Hctx). simpl. tauto.
  - eapply Hctx; eauto.
Qed.

Definition term_interpretation (fuel : nat) (rho : list (atom * tm))
    (R : rty) (t : tm) : Prop :=
  forall t', multi (tm_subst_environment rho t) t' ->
    value t' -> logical_relation fuel rho R t'.

Lemma term_interpretation_zero : forall rho R t,
  term_interpretation 0 rho R t.
Proof. intros rho R t t' Hmulti Hv. exact I. Qed.

Lemma value_no_step : forall v v', value v -> ~ v --> v'.
Proof. intros v v' Hv Hstep; inversion Hv; subst; inversion Hstep. Qed.

Lemma multi_value_identity : forall v t',
  value v -> multi v t' -> t' = v.
Proof.
  intros v t' Hv Hmulti. induction Hmulti; auto.
  exfalso. eapply value_no_step; eauto.
Qed.

Lemma term_interpretation_variable : forall fuel rho RGamma x R v,
  lookup_tm_environment x rho = Some v ->
  lookup_rcontext x RGamma = Some R ->
  context_interpretation fuel RGamma rho ->
  term_interpretation fuel rho R (tm_fvar x).
Proof.
  intros fuel rho RGamma x R v Henv Hlookup Hctx t' Hmulti Hv.
  simpl in Hmulti. rewrite Henv in Hmulti.
  destruct (Hctx x R Hlookup) as [v0 [Henv0 [_ [Hv0 Hrel]]]].
  rewrite Henv in Henv0. inversion Henv0; subst v0.
  assert (Heq : t' = v) by (eapply multi_value_identity; eauto).
  subst t'. exact Hrel.
Qed.

Lemma empty_context_interpretation : forall fuel rho,
  context_interpretation fuel [] rho.
Proof. intros fuel rho x R H; discriminate. Qed.

Lemma context_interpretation_facts : forall fuel RGamma rho,
  context_interpretation (S fuel) RGamma rho ->
  context_facts RGamma (environment_atoms rho).
Proof.
  intros fuel RGamma rho Hctx x T p Hlookup.
  destruct (Hctx x (R_Refine T p) Hlookup)
    as [v [Henv [Hfixed [Hv Hrel]]]].
  simpl in Hrel. destruct Hrel as [_ Hqual].
  pose proof (environment_interpret_open_qualifier p 0 rho x v Henv Hfixed) as Hopen.
  unfold open_qualifier_tm in Hqual |- *.
  rewrite Hopen. exact Hqual.
Qed.

Lemma entails_sound_in_interpreted_context : forall fuel Delta RGamma p q rho,
  entails Delta RGamma p q ->
  context_interpretation (S fuel) RGamma rho ->
  interpret_qualifier (environment_atoms rho) p ->
  interpret_qualifier (environment_atoms rho) q.
Proof.
  intros fuel Delta RGamma p q rho Hent Hctx Hp.
  eapply entails_sound_in_context; eauto using context_interpretation_facts.
Qed.

Lemma logical_relation_refinement_holds : forall fuel T p v,
  logical_relation (S fuel) [] (R_Refine T p) v ->
  value v /\ qualifier_holds (open_qualifier_tm p v).
Proof.
  intros fuel T p v H. simpl in H. unfold environment_atoms in H. simpl in H.
  unfold qualifier_holds, predicate_holds. exact H.
Qed.

Lemma logical_relation_value : forall fuel rho R v,
  logical_relation (S fuel) rho R v -> value v.
Proof.
  intros fuel rho R v H. destruct R; simpl in H; intuition.
Qed.

Lemma logical_relation_integer : forall fuel rho m,
  logical_relation (S fuel) rho
    (R_Refine Ty_Int (Pred_Eq (tm_bvar 0) (tm_int m))) (tm_int m).
Proof.
  intros fuel rho m. simpl. split; [constructor|].
  unfold environment_atoms. destruct rho; simpl;
  unfold operational_atoms; simpl; exists (tm_int m).
  repeat split; constructor.
Qed.

Lemma nonzero_refinement_multistep : forall t t',
  multi t t' ->
  qualifier_holds (Pred_Ne t (tm_int 0%Z)) ->
  qualifier_holds (Pred_Ne t' (tm_int 0%Z)).
Proof.
  intros t t' Hmulti. induction Hmulti; intros Hne.
  - exact Hne.
  - apply IHHmulti. eapply nonzero_refinement_step; eauto.
Qed.

Lemma rtype_value_arrow : forall Delta RGamma v R,
  has_rtype Delta RGamma v R -> value v ->
  shape_ty (erase R) = Shape_Arrow ->
  exists A body, v = tm_abs A body.
Proof.
  intros Delta RGamma v R Hty; induction Hty; intros Hv Hshape;
    try solve [inversion Hv; subst; simpl in Hshape; discriminate].
  - inversion Hv; subst. simpl in Hshape.
    exists (erase R1), body; reflexivity.
  - simpl in Hshape. eapply core_value_arrow; eauto.
  -
    apply IHHty; auto.
    pose proof (subtype_shape _ _ _ _ H0); simpl in *; congruence.
Qed.

Lemma rtype_value_poly : forall Delta RGamma v R,
  has_rtype Delta RGamma v R -> value v ->
  shape_ty (erase R) = Shape_All ->
  exists body, v = tm_tabs body.
Proof.
  intros Delta RGamma v R Hty; induction Hty; intros Hv Hshape;
    try solve [inversion Hv; subst; simpl in Hshape; discriminate].
  - inversion Hv; subst. eexists; reflexivity.
  - simpl in Hshape. eapply core_value_poly; eauto.
  - apply IHHty; auto.
    pose proof (subtype_shape _ _ _ _ H0); simpl in *; congruence.
Qed.

Lemma rtype_value_int : forall Delta RGamma v R,
  has_rtype Delta RGamma v R -> value v ->
  shape_ty (erase R) = Shape_Int ->
  exists n, v = tm_int n.
Proof.
  intros Delta RGamma v R Hty; induction Hty; intros Hv Hshape;
    try solve [inversion Hv; subst; simpl in Hshape; discriminate].
  - inversion Hv; subst. eexists; reflexivity.
  - simpl in Hshape. eapply core_value_int; eauto.
  - apply IHHty; auto.
    pose proof (subtype_shape _ _ _ _ H0); simpl in *; congruence.
Qed.

Lemma rtype_value_bool : forall Delta RGamma v R,
  has_rtype Delta RGamma v R -> value v ->
  shape_ty (erase R) = Shape_Bool ->
  v = tm_true \/ v = tm_false.
Proof.
  intros Delta RGamma v R Hty; induction Hty; intros Hv Hshape;
    try solve [inversion Hv; subst; simpl in Hshape; discriminate].
  - left; reflexivity.
  - right; reflexivity.
  - simpl in Hshape. eapply core_value_bool; eauto.
  - apply IHHty; auto.
    pose proof (subtype_shape _ _ _ _ H0); simpl in *; congruence.
Qed.

Lemma has_rtype_lc_closed : forall t R,
  has_rtype [] empty_rcontext t R -> locally_closed_tm t.
Proof.
  intros t R H; unfold locally_closed_tm.
  exact (@has_rtype_lc_tm [] empty_rcontext t R H).
Qed.

Lemma wf_ty_lc_closed : forall T,
  wf_ty [] T -> locally_closed_ty T.
Proof.
  intros T H; unfold locally_closed_ty.
  exact (@wf_ty_lc [] T H).
Qed.

Lemma erase_context_update : forall RGamma x R,
  erase_context (update_rcontext RGamma x R) =
  update (erase_context RGamma) x (erase R).
Proof. reflexivity. Qed.

Lemma lookup_erase_context : forall x RGamma R,
  lookup_rcontext x RGamma = Some R ->
  lookup_context x (erase_context RGamma) = Some (erase R).
Proof.
  intros x RGamma; induction RGamma as [|[y S] RG IH]; intros R H; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + inversion H; subst. reflexivity.
    + eapply IH. exact H.
Qed.

Lemma has_rtype_erasure : forall Delta RGamma t R,
  has_rtype Delta RGamma t R ->
  has_type Delta (erase_context RGamma) t (erase R).
Proof.
  intros Delta RGamma t R Hty; induction Hty; simpl.
  - econstructor; [eapply lookup_erase_context; eassumption|eapply wf_rty_erase; eassumption].
  - apply T_Abs with (L:=L).
    + eapply wf_rty_erase; eauto.
    + intros x Hx. specialize (H1 x Hx).
      rewrite erase_context_update in H1.
      unfold open_rty_tm in H1. rewrite erase_open_rty_tm_rec in H1.
      exact H1.
  - econstructor; eauto.
  - apply T_TAbs with (L:=L). intros X HX.
    specialize (H0 X HX). unfold open_rty_ty in H0.
    rewrite erase_open_rty_ty_rec in H0. exact H0.
  - unfold open_rty_ty. rewrite erase_open_rty_ty_rec. eapply T_TApp; eauto.
  - constructor.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
  - constructor.
  - constructor.
  - econstructor; eauto.
  - exact H.
  - pose proof (subtype_erase_equal _ _ _ _ H0) as Heq.
    rewrite <- Heq. exact IHHty.
Qed.

Lemma int_ne_holds_nonzero : forall m,
  qualifier_holds
    (open_qualifier_tm (Pred_Ne (tm_bvar 0) (tm_int 0%Z)) (tm_int m)) ->
  m <> 0%Z.
Proof.
  intros m H holds.
  unfold qualifier_holds, predicate_holds, interpret_qualifier in H.
  simpl in H. subst m. apply H.
  unfold operational_atoms; simpl.
  exists (tm_int 0%Z); repeat split; constructor.
Qed.

Lemma rtype_progress_closed :
  (forall m, has_rtype [] empty_rcontext (tm_int m)
      (R_Refine Ty_Int (Pred_Ne (tm_bvar 0) (tm_int 0%Z))) -> m <> 0%Z) ->
  forall t R,
  has_rtype [] empty_rcontext t R ->
  value t \/ exists t', t --> t'.
Proof.
  intros Hnz t R Hty.
  remember ([] : ty_context) as Delta eqn:HD.
  remember empty_rcontext as RGamma eqn:HG.
  induction Hty; subst; simpl in *.
  - discriminate.
  - left. apply v_abs. eapply has_rtype_lc_closed. econstructor; eauto.
  - destruct (IHHty1 eq_refl eq_refl Hnz) as [Hv1|[t1' Hs1]].
    + destruct (IHHty2 eq_refl eq_refl Hnz) as [Hv2|[t2' Hs2]].
      * destruct (rtype_value_arrow _ _ _ _ Hty1 Hv1 eq_refl) as [A [b Hb]].
        subst t1. right. eexists. eapply ST_AppAbs; eauto using value_lc_tm.
      * right. eexists. eapply ST_App2; eauto.
    + right. eexists. eapply ST_App1; eauto using has_rtype_lc_closed.
  - left. apply v_tabs. eapply has_rtype_lc_closed. econstructor; eauto.
  - destruct (IHHty eq_refl eq_refl Hnz) as [Hv|[t' Hs]].
    + destruct (rtype_value_poly _ _ _ _ Hty Hv eq_refl) as [b Hb].
      subst t. right. eexists. eapply ST_TAppTabs; eauto using value_lc_tm, wf_ty_lc_closed.
    + right. eexists. eapply ST_TApp; eauto using wf_ty_lc_closed.
  - left. constructor.
  - destruct (IHHty1 eq_refl eq_refl Hnz) as [Hv1|[t1' Hs1]].
    + destruct (IHHty2 eq_refl eq_refl Hnz) as [Hv2|[t2' Hs2]].
      * destruct (rtype_value_int _ _ _ _ Hty1 Hv1 eq_refl) as [n Hn].
        destruct (rtype_value_int _ _ _ _ Hty2 Hv2 eq_refl) as [m Hm].
        subst t1 t2. right. eexists. eapply ST_DivInt.
        eapply Hnz; exact Hty2.
      * right. exists (tm_div t1 t2'). apply ST_Div2 with (v1:=t1); assumption.
    + right. exists (tm_div t1' t2). apply ST_Div1; [exact Hs1|exact (@has_rtype_lc_closed t2 (R_Refine Ty_Int (Pred_Ne (tm_bvar 0) (tm_int 0%Z))) Hty2)].
  - destruct (IHHty1 eq_refl eq_refl Hnz) as [Hv1|[t1' Hs1]].
    + destruct (IHHty2 eq_refl eq_refl Hnz) as [Hv2|[t2' Hs2]].
      * destruct (rtype_value_int _ _ _ _ Hty1 Hv1 eq_refl) as [n Hn].
        destruct (rtype_value_int _ _ _ _ Hty2 Hv2 eq_refl) as [m Hm].
        subst t1 t2. right. eexists. apply ST_ArithInt.
      * right. exists (tm_arith op t1 t2'). apply ST_Arith2 with (v1:=t1); assumption.
    + right. exists (tm_arith op t1' t2). apply ST_Arith1; [exact Hs1|exact (@has_rtype_lc_closed t2 (R_Refine Ty_Int Pred_True) Hty2)].
  - right. eexists. apply ST_ChoiceLeft; eapply has_rtype_lc_closed; eauto.
  - left. constructor.
  - left. constructor.
  - destruct (IHHty1 eq_refl eq_refl Hnz) as [Hv|[t1' Hs]].
    + destruct (rtype_value_bool _ _ _ _ Hty1 Hv eq_refl) as [Hb|Hb]; subst t1.
      * right. eexists. apply ST_IfTrue; eapply has_rtype_lc_closed; eauto.
      * right. eexists. apply ST_IfFalse; eapply has_rtype_lc_closed; eauto.
    + right. eexists. apply ST_If; eauto using has_rtype_lc_closed.
  - left. assumption.
  - destruct (IHHty eq_refl eq_refl Hnz); auto.
Qed.

Theorem never_stuck : forall (t t' : tm) (R : rty),
  has_rtype [] empty_rcontext t R ->
  multi t t' ->
  value t' \/ exists t'' : tm, t' --> t''.
Proof.
  intros t t' R Htyped Hsteps.
  induction Hsteps.
  - induction Htyped; eauto 10 using value, step.
Qed.

End SystemFRefinementIfNonDeterminismTask.
