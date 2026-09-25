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

Module SystemFRefinementIfNonDeterminismEvaluation.
Import ListNotations SystemFRefinementIfNonDeterminism SystemFRefinementIfNonDeterminismLogic SystemFRefinementIfNonDeterminismTyping.

Inductive multi : tm -> tm -> Prop :=
  | multi_refl : forall t, multi t t
  | multi_step : forall t1 t2 t3,
      t1 --> t2 -> multi t2 t3 -> multi t1 t3.
Notation "t '-->*' u" := (multi t u) (at level 40).

End SystemFRefinementIfNonDeterminismEvaluation.

Module SystemFRefinementIfNonDeterminismTask.
Import ListNotations SystemFRefinementIfNonDeterminism SystemFRefinementIfNonDeterminismLogic SystemFRefinementIfNonDeterminismTyping SystemFRefinementIfNonDeterminismEvaluation.

Definition closed_term (t : tm) : Prop :=
  locally_closed_tm t /\ fv_tm t = [] /\ ftv_tm t = [].

Definition computation_relation (P : tm -> Prop) (t : tm) : Prop :=
  forall t', multi t t' ->
    closed_term t' /\
    ((value t' /\ P t') \/ exists t'', t' --> t'').

Fixpoint value_relation (R : rty) (close : rty -> rty) (v : tm) : Prop :=
  match R with
  | R_Refine T ps =>
      value v /\ closed_term v /\
      match close (R_Refine T ps) with
      | R_Refine T' ps' =>
          (match T' with
           | Ty_Int => exists n, v = tm_int n
           | Ty_Bool => v = tm_true \/ v = tm_false
           | _ => True
           end) /\
          predicate_closed (open_qualifier_tm ps' v) /\
          qualifier_holds (open_qualifier_tm ps' v)
      | _ => False
      end
  | R_Func R1 R2 =>
      exists T body, v = tm_abs T body /\ closed_term v /\
        forall w, value_relation R1 close w ->
          computation_relation
            (value_relation R2 (fun S => close (open_rty_tm S w)))
            (open_tm body w)
  | R_Exists R1 R2 =>
      value v /\ closed_term v /\ exists w, value_relation R1 close w /\
        value_relation R2 (fun S => close (open_rty_tm S w)) v
  | R_Poly R1 =>
      exists body, v = tm_tabs body /\ closed_term v /\
        forall U, wf_ty [] U ->
          computation_relation
            (value_relation R1 (fun S => close (open_rty_ty S U)))
            (open_tm_ty body U)
  end.

Definition semantic_type (R : rty) (close : rty -> rty) (t : tm) : Prop :=
  computation_relation (value_relation R close) t.

Lemma value_relation_closed : forall R close v,
  value_relation R close v -> closed_term v.
Proof.
  intros R close v Hrelation.
  destruct R; simpl in Hrelation.
  - exact (proj1 (proj2 Hrelation)).
  - destruct Hrelation as [T [body [_ [Hclosed _]]]]; exact Hclosed.
  - exact (proj1 (proj2 Hrelation)).
  - destruct Hrelation as [body [_ [Hclosed _]]]; exact Hclosed.
Qed.

Lemma value_relation_value : forall R close v,
  value_relation R close v -> value v.
Proof.
  intros R close v Hrelation.
  destruct R; simpl in Hrelation.
  - exact (proj1 Hrelation).
  - destruct Hrelation as [T [body [-> [Hclosed _]]]].
    apply v_abs; exact (proj1 Hclosed).
  - exact (proj1 Hrelation).
  - destruct Hrelation as [body [-> [Hclosed _]]].
    apply v_tabs; exact (proj1 Hclosed).
Qed.

Fixpoint instantiate_tm (rho : list (atom * tm)) (t : tm) : tm :=
  match rho with
  | [] => t
  | (x, v) :: rho' => instantiate_tm rho' (tm_subst x v t)
  end.

Fixpoint instantiate_rty_tm (rho : list (atom * tm)) (R : rty) : rty :=
  match rho with
  | [] => R
  | (x, v) :: rho' => instantiate_rty_tm rho' (rty_subst x v R)
  end.

Fixpoint instantiate_tm_ty (theta : list (atom * ty)) (t : tm) : tm :=
  match theta with
  | [] => t
  | (X, U) :: theta' => instantiate_tm_ty theta' (tm_ty_subst X U t)
  end.

Fixpoint instantiate_rty_ty (theta : list (atom * ty)) (R : rty) : rty :=
  match theta with
  | [] => R
  | (X, U) :: theta' => instantiate_rty_ty theta' (rty_ty_subst X U R)
  end.

Definition close_rty (rho : list (atom * tm))
    (theta : list (atom * ty)) (R : rty) : rty :=
  instantiate_rty_tm rho (instantiate_rty_ty theta R).

Fixpoint lookup_values (x : atom) (rho : list (atom * tm)) : option tm :=
  match rho with
  | [] => None
  | (y, v) :: rho' =>
      if Nat.eqb x y then Some v else lookup_values x rho'
  end.

Fixpoint lookup_types (X : atom) (theta : list (atom * ty)) : option ty :=
  match theta with
  | [] => None
  | (Y, U) :: theta' =>
      if Nat.eqb X Y then Some U else lookup_types X theta'
  end.

Definition context_relation (Delta : ty_context) (RGamma : rcontext)
    (theta : list (atom * ty)) (rho : list (atom * tm)) : Prop :=
  (forall X, In X Delta -> exists U, lookup_types X theta = Some U /\ wf_ty [] U) /\
  (forall x R, lookup_rcontext x RGamma = Some R ->
    exists v, lookup_values x rho = Some v /\ closed_term v /\
      value v /\ value_relation R (close_rty rho theta) v) /\
  (forall x v, In (x, v) rho -> closed_term v /\ value v) /\
  (forall X U, In (X, U) theta -> wf_ty [] U).

Lemma context_relation_empty : context_relation [] [] [] [].
Proof.
  unfold context_relation; repeat split; intros; simpl in *; try contradiction.
  discriminate.
Qed.

Lemma multi_trans : forall t u v,
  multi t u -> multi u v -> multi t v.
Proof.
  intros t u v H.
  induction H; intros Huv; eauto using multi.
Qed.

Lemma computation_relation_reachable : forall P t u,
  computation_relation P t -> multi t u -> computation_relation P u.
Proof.
  intros P t u H tu v uv.
  apply H.
  eapply multi_trans; eauto.
Qed.

Lemma computation_relation_progress : forall P t,
  computation_relation P t -> value t \/ exists u, t --> u.
Proof.
  intros P t H.
  specialize (H t (multi_refl t)).
  destruct H as [_ [[Hv _] | Hstep]]; auto.
Qed.

Lemma computation_relation_closed : forall P t,
  computation_relation P t -> closed_term t.
Proof.
  intros P t H; exact (proj1 (H t (multi_refl t))).
Qed.

Lemma closed_integer : forall n, closed_term (tm_int n).
Proof.
  intros n; unfold closed_term, locally_closed_tm; simpl;
    repeat split; auto using lc_tm_at.
Qed.

Lemma closed_division : forall a b,
  closed_term a -> closed_term b -> closed_term (tm_div a b).
Proof.
  intros a b [Hla [Hfa Hta]] [Hlb [Hfb Htb]].
  unfold closed_term; simpl; repeat split.
  - unfold locally_closed_tm in *; now constructor.
  - now rewrite Hfa, Hfb.
  - now rewrite Hta, Htb.
Qed.

Lemma closed_arithmetic : forall op a b,
  closed_term a -> closed_term b -> closed_term (tm_arith op a b).
Proof.
  intros op a b [Hla [Hfa Hta]] [Hlb [Hfb Htb]].
  unfold closed_term; simpl; repeat split.
  - unfold locally_closed_tm in *; now constructor.
  - now rewrite Hfa, Hfb.
  - now rewrite Hta, Htb.
Qed.

Lemma closed_conditional : forall c a b,
  closed_term c -> closed_term a -> closed_term b ->
  closed_term (tm_if c a b).
Proof.
  intros c a b [Hlc [Hfc Htc]] [Hla [Hfa Hta]]
    [Hlb [Hfb Htb]].
  unfold closed_term; simpl; repeat split.
  - unfold locally_closed_tm in *; now constructor.
  - now rewrite Hfc, Hfa, Hfb.
  - now rewrite Htc, Hta, Htb.
Qed.

Lemma opening_locally_closed_term : forall K k t,
  lc_tm_at K k t -> forall u j, k <= j -> open_tm_rec j u t = t.
Proof.
  intros K k t Hlc; induction Hlc; intros u j Hle; simpl;
    try (f_equal; eauto using le_n_S);
    try reflexivity.
  destruct (Nat.eqb j i) eqn:Heq; auto.
  apply Nat.eqb_eq in Heq; lia.
Qed.

Lemma opening_closed_term : forall t u,
  locally_closed_tm t -> open_tm_rec 0 u t = t.
Proof.
  intros t u Hlc; eapply opening_locally_closed_term; eauto.
Qed.

Lemma substitution_opening : forall t x v k,
  locally_closed_tm v ->
  tm_subst x v (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k v (tm_subst x v t).
Proof.
  induction t; intros x v k Hlc; simpl;
    try (f_equal; eauto); try reflexivity.
  - destruct (Nat.eqb k n); simpl; rewrite ?Nat.eqb_refl; reflexivity.
  - destruct (Nat.eqb x a); simpl.
    + symmetry; eapply opening_locally_closed_term; [exact Hlc | lia].
    + reflexivity.
Qed.

Lemma value_locally_closed : forall v, value v -> locally_closed_tm v.
Proof.
  intros v H; destruct H; try assumption;
    unfold locally_closed_tm; constructor.
Qed.

Lemma computation_relation_value : forall P v,
  closed_term v -> value v -> P v -> computation_relation P v.
Proof.
  intros P v Hclosed Hv HP u Hsteps.
  inversion Hsteps; subst; auto.
  inversion Hv; subst; inversion H.
Qed.

Lemma computation_relation_prestep : forall P t,
  closed_term t ->
  (exists u, t --> u) ->
  (forall u, t --> u -> computation_relation P u) ->
  computation_relation P t.
Proof.
  intros P t Hlc Hprogress Hsuccessors u Hsteps.
  inversion Hsteps; subst.
  - split; [assumption | right; exact Hprogress].
  - apply Hsuccessors in H. apply H. assumption.
Qed.

Lemma computation_relation_choice : forall P t1 t2,
  computation_relation P t1 ->
  computation_relation P t2 ->
  computation_relation P (tm_choice t1 t2).
Proof.
  intros P t1 t2 Hleft Hright.
  destruct (computation_relation_closed _ _ Hleft) as [Hlc1 [Hfv1 Hftv1]].
  destruct (computation_relation_closed _ _ Hright) as [Hlc2 [Hfv2 Hftv2]].
  eapply computation_relation_prestep.
  - unfold closed_term; simpl; repeat split; auto.
    + now constructor.
    + now rewrite Hfv1, Hfv2.
    + now rewrite Hftv1, Hftv2.
  - eexists; now apply ST_ChoiceLeft.
  - intros u Hstep; inversion Hstep; subst; assumption.
Qed.

Lemma value_relation_integer : forall ps v,
  value_relation (R_Refine Ty_Int ps) (fun R => R) v ->
  exists n, v = tm_int n.
Proof.
  intros ps v [_ [_ [H _]]].
  exact H.
Qed.

Lemma value_relation_boolean : forall ps v,
  value_relation (R_Refine Ty_Bool ps) (fun R => R) v ->
  v = tm_true \/ v = tm_false.
Proof.
  intros ps v [_ [_ [H _]]].
  exact H.
Qed.

Lemma value_relation_nonzero : forall v,
  value_relation
    (R_Refine Ty_Int (Pred_Ne (tm_bvar 0) (tm_int 0%Z)))
    (fun R => R) v ->
  exists n, v = tm_int n /\ n <> 0%Z.
Proof.
  intros v [_ [_ [Hv [_ Hne]]]].
  destruct Hv as [n ->].
  exists n; split; auto.
  intros ->.
  apply Hne.
  exists (tm_int 0%Z); repeat split;
    try apply PMS_Refl; constructor.
Qed.

Lemma computation_relation_invariant : forall (I P : tm -> Prop) t,
  I t ->
  (forall u, I u ->
    closed_term u /\
    ((value u /\ P u) \/ exists v, u --> v)) ->
  (forall u v, I u -> u --> v -> I v) ->
  computation_relation P t.
Proof.
  intros I P t Hinitial Hprogress Hpreserve u Hsteps.
  apply Hprogress.
  induction Hsteps; eauto.
Qed.

Definition division_invariant (u : tm) : Prop :=
  (exists a b, u = tm_div a b /\
    semantic_type (R_Refine Ty_Int Pred_True) (fun R => R) a /\
    semantic_type
      (R_Refine Ty_Int (Pred_Ne (tm_bvar 0) (tm_int 0%Z)))
      (fun R => R) b) \/
  exists n, u = tm_int n.

Lemma division_invariant_progress : forall u,
  division_invariant u ->
  closed_term u /\
  ((value u /\ value_relation (R_Refine Ty_Int Pred_True)
       (fun R => R) u) \/ exists v, u --> v).
Proof.
  intros u [[a [b [-> [Ha Hb]]]] | [n ->]].
  - destruct (Ha a (multi_refl a)) as [Hla [[Hva Hpa] | [a' Hsa]]].
    + destruct (Hb b (multi_refl b)) as [Hlb [[Hvb Hpb] | [b' Hsb]]].
      * destruct (value_relation_integer _ _ Hpa) as [na ->].
        destruct (value_relation_nonzero _ Hpb) as [nb [-> Hnz]].
        split; [apply closed_division; assumption | right].
        eexists; now apply ST_DivInt.
      * split; [apply closed_division; assumption | right].
        eexists; eapply ST_Div2; eauto.
    + destruct (Hb b (multi_refl b)) as [Hlb _].
      split; [apply closed_division; assumption | right].
      eexists; eapply ST_Div1; eauto; exact (proj1 Hlb).
  - split; [apply closed_integer | left].
    split; [constructor |].
    simpl; repeat split.
    + constructor.
    + unfold locally_closed_tm; constructor.
    + exists n; reflexivity.
Qed.

Lemma division_invariant_step : forall u v,
  division_invariant u -> u --> v -> division_invariant v.
Proof.
  intros u v [[a [b [-> [Ha Hb]]]] | [n ->]] Hstep.
  - inversion Hstep; subst.
    + left; exists t1', b; split; [reflexivity | split].
      eapply computation_relation_reachable; [exact Ha |].
      eapply multi_step; eauto using multi_refl.
      exact Hb.
    + left; exists a, t2'; split; [reflexivity | split].
      exact Ha.
      eapply computation_relation_reachable; [exact Hb |].
      eapply multi_step; eauto using multi_refl.
    + right; eauto.
  - inversion Hstep.
Qed.

Lemma computation_relation_div : forall a b,
  semantic_type (R_Refine Ty_Int Pred_True) (fun R => R) a ->
  semantic_type
    (R_Refine Ty_Int (Pred_Ne (tm_bvar 0) (tm_int 0%Z)))
    (fun R => R) b ->
  semantic_type (R_Refine Ty_Int Pred_True) (fun R => R) (tm_div a b).
Proof.
  intros a b Ha Hb.
  eapply computation_relation_invariant with (I := division_invariant).
  - left; eauto.
  - exact division_invariant_progress.
  - exact division_invariant_step.
Qed.

Definition conditional_invariant (P : tm -> Prop) (then_branch else_branch u : tm) : Prop :=
  (exists condition, u = tm_if condition then_branch else_branch /\
    semantic_type (R_Refine Ty_Bool Pred_True) (fun R => R) condition) \/
  computation_relation P u.

Lemma computation_relation_if : forall P condition then_branch else_branch,
  semantic_type (R_Refine Ty_Bool Pred_True) (fun R => R) condition ->
  computation_relation P then_branch ->
  computation_relation P else_branch ->
  computation_relation P (tm_if condition then_branch else_branch).
Proof.
  intros P condition then_branch else_branch Hcondition Hthen Helse.
  eapply computation_relation_invariant
    with (I := conditional_invariant P then_branch else_branch).
  - left; eauto.
  - intros u [[c [-> Hc]] | Hu].
    + destruct (Hthen then_branch (multi_refl then_branch)) as [Hlc2 _].
      destruct (Helse else_branch (multi_refl else_branch)) as [Hlc3 _].
      destruct (Hc c (multi_refl c)) as [Hlc1 [[Hv Hval] | [c' Hstep]]].
      * destruct (value_relation_boolean _ _ Hval) as [-> | ->].
        -- split; [apply closed_conditional; assumption | right].
           eexists; apply ST_IfTrue; [exact (proj1 Hlc2) | exact (proj1 Hlc3)].
        -- split; [apply closed_conditional; assumption | right].
           eexists; apply ST_IfFalse; [exact (proj1 Hlc2) | exact (proj1 Hlc3)].
      * split; [apply closed_conditional; assumption | right].
        eexists; eapply ST_If; eauto; [exact (proj1 Hlc2) | exact (proj1 Hlc3)].
    + apply Hu; constructor.
  - intros u v [[c [-> Hc]] | Hu] Hstep.
    + inversion Hstep; subst.
      * left; exists t1'; split; [reflexivity |].
        eapply computation_relation_reachable; [exact Hc |].
        eapply multi_step; eauto using multi_refl.
      * right; exact Hthen.
      * right; exact Helse.
    + right; eapply computation_relation_reachable; [exact Hu |].
      eapply multi_step; eauto using multi_refl.
Qed.

Definition arithmetic_invariant (op : integer_operator) (u : tm) : Prop :=
  (exists a b, u = tm_arith op a b /\
    semantic_type (R_Refine Ty_Int Pred_True) (fun R => R) a /\
    semantic_type (R_Refine Ty_Int Pred_True) (fun R => R) b) \/
  exists n, u = tm_int n.

Lemma arithmetic_invariant_progress : forall op u,
  arithmetic_invariant op u ->
  closed_term u /\
  ((value u /\ value_relation (R_Refine Ty_Int Pred_True)
       (fun R => R) u) \/ exists v, u --> v).
Proof.
  intros op u [[a [b [-> [Ha Hb]]]] | [n ->]].
  - destruct (Ha a (multi_refl a)) as [Hla [[Hva Hpa] | [a' Hsa]]].
    + destruct (Hb b (multi_refl b)) as [Hlb [[Hvb Hpb] | [b' Hsb]]].
      * destruct (value_relation_integer _ _ Hpa) as [na ->].
        destruct (value_relation_integer _ _ Hpb) as [nb ->].
        split; [apply closed_arithmetic; assumption | right].
        eexists; now apply ST_ArithInt.
      * split; [apply closed_arithmetic; assumption | right].
        eexists; eapply ST_Arith2; eauto.
    + destruct (Hb b (multi_refl b)) as [Hlb _].
      split; [apply closed_arithmetic; assumption | right].
      eexists; eapply ST_Arith1; eauto; exact (proj1 Hlb).
  - split; [apply closed_integer | left].
    split; [constructor |].
    simpl; repeat split.
    + constructor.
    + unfold locally_closed_tm; constructor.
    + exists n; reflexivity.
Qed.

Lemma arithmetic_invariant_step : forall op u v,
  arithmetic_invariant op u -> u --> v -> arithmetic_invariant op v.
Proof.
  intros op u v [[a [b [-> [Ha Hb]]]] | [n ->]] Hstep.
  - inversion Hstep; subst.
    + left; exists t1', b; split; [reflexivity | split].
      * eapply computation_relation_reachable; [exact Ha |].
        eapply multi_step; eauto using multi_refl.
      * exact Hb.
    + left; exists a, t2'; split; [reflexivity | split].
      * exact Ha.
      * eapply computation_relation_reachable; [exact Hb |].
        eapply multi_step; eauto using multi_refl.
    + right; eauto.
  - inversion Hstep.
Qed.

Lemma computation_relation_arithmetic_true : forall op a b,
  semantic_type (R_Refine Ty_Int Pred_True) (fun R => R) a ->
  semantic_type (R_Refine Ty_Int Pred_True) (fun R => R) b ->
  semantic_type (R_Refine Ty_Int Pred_True) (fun R => R)
    (tm_arith op a b).
Proof.
  intros op a b Ha Hb.
  eapply computation_relation_invariant with (I := arithmetic_invariant op).
  - left; eauto.
  - exact (arithmetic_invariant_progress op).
  - exact (arithmetic_invariant_step op).
Qed.

Lemma predicate_multistep_of_multi : forall a b,
  multi a b -> predicate_multistep a b.
Proof.
  intros a b H; induction H; eauto using predicate_multistep.
Qed.

Lemma computation_relation_strengthen : forall P Q t,
  computation_relation P t ->
  (forall v, multi t v -> value v -> P v -> Q v) ->
  computation_relation Q t.
Proof.
  intros P Q t H HQ v Hsteps.
  destruct (H v Hsteps) as [Hlc [[Hv HP] | Hstep]].
  - split; [exact Hlc | left; split; auto].
  - split; [exact Hlc | right; exact Hstep].
Qed.

Lemma computation_relation_arithmetic : forall op a b,
  semantic_type (R_Refine Ty_Int Pred_True) (fun R => R) a ->
  semantic_type (R_Refine Ty_Int Pred_True) (fun R => R) b ->
  semantic_type
    (R_Refine Ty_Int (Pred_Eq (tm_bvar 0) (tm_arith op a b)))
    (fun R => R) (tm_arith op a b).
Proof.
  intros op a b Ha Hb.
  eapply computation_relation_strengthen.
  - now apply computation_relation_arithmetic_true.
  - intros v Hsteps Hv HP.
    destruct (value_relation_integer _ _ HP) as [n ->].
    destruct (computation_relation_closed _ _ Ha) as [Hla [Hfa Hta]].
    destruct (computation_relation_closed _ _ Hb) as [Hlb [Hfb Htb]].
    simpl.
    rewrite (opening_closed_term a (tm_int n) Hla).
    rewrite (opening_closed_term b (tm_int n) Hlb).
    repeat split; auto using v_int.
    + unfold locally_closed_tm; constructor.
    + exists n; reflexivity.
    + unfold locally_closed_tm; constructor.
    + apply closed_arithmetic; repeat split; assumption.
    + now rewrite Hfa, Hfb.
    + now rewrite Hta, Htb.
    + exists (tm_int n); repeat split;
        auto using PMS_Refl, v_int, predicate_multistep_of_multi.
      rewrite (opening_closed_term (tm_arith op a b) (tm_int n)).
      * now apply predicate_multistep_of_multi.
      * apply closed_arithmetic; repeat split; assumption.
Qed.

Lemma computation_relation_integer : forall n,
  semantic_type (R_Refine Ty_Int
    (Pred_Eq (tm_bvar 0) (tm_int n)))
    (fun R => R) (tm_int n).
Proof.
  intros n; apply computation_relation_value.
  - apply closed_integer.
  - constructor.
  - simpl; repeat split; auto using v_int, lc_tm_at.
    + unfold locally_closed_tm; constructor.
    + exists n; reflexivity.
    + unfold locally_closed_tm; constructor.
    + unfold locally_closed_tm; constructor.
    + exists (tm_int n); repeat split;
        auto using PMS_Refl, v_int.
Qed.

Lemma computation_relation_true :
  semantic_type (R_Refine Ty_Bool Pred_True)
    (fun R => R) tm_true.
Proof.
  apply computation_relation_value; auto using v_true.
  - unfold closed_term, locally_closed_tm; simpl;
      repeat split; auto using lc_tm_at.
  - simpl; repeat split; auto using v_true, lc_tm_at.
    unfold locally_closed_tm; constructor.
Qed.

Lemma computation_relation_false :
  semantic_type (R_Refine Ty_Bool Pred_True)
    (fun R => R) tm_false.
Proof.
  apply computation_relation_value; auto using v_false.
  - unfold closed_term, locally_closed_tm; simpl;
      repeat split; auto using lc_tm_at.
  - simpl; repeat split; auto using v_false, lc_tm_at.
    unfold locally_closed_tm; constructor.
Qed.

Lemma entails_truth : forall Delta RGamma p q,
  entails Delta RGamma p q ->
  (forall x T ps,
    lookup_rcontext x RGamma = Some (R_Refine T ps) ->
    qualifier_holds (open_qualifier_tm ps (tm_fvar x))) ->
  qualifier_holds p -> qualifier_holds q.
Proof.
  intros Delta RGamma p q Hentails.
  induction Hentails; intros Hcontext Hsource; simpl in *.
  - exact Hsource.
  - exact I.
  - eauto.
  - exact (proj1 Hsource).
  - exact (proj2 Hsource).
  - split; [apply IHHentails1 | apply IHHentails2]; auto.
  - left; exact Hsource.
  - right; exact Hsource.
  - destruct Hsource as [Hp | Hq]; [apply IHHentails1 | apply IHHentails2]; auto.
  - intros Hq; apply (IHHentails Hcontext); split; assumption.
  - destruct Hsource as [Hp Hnotp]; apply Hnotp; exact Hp.
  - eapply Hcontext; eauto.
  - contradiction.
Qed.

Lemma core_integer_value : forall Delta Gamma v,
  has_type Delta Gamma v Ty_Int -> value v ->
  exists n, v = tm_int n.
Proof.
  intros Delta Gamma v Htype Hvalue.
  inversion Hvalue; subst; inversion Htype; subst; eauto; discriminate.
Qed.

Lemma core_boolean_value : forall Delta Gamma v,
  has_type Delta Gamma v Ty_Bool -> value v ->
  v = tm_true \/ v = tm_false.
Proof.
  intros Delta Gamma v Htype Hvalue.
  inversion Hvalue; subst; inversion Htype; subst; eauto; discriminate.
Qed.

Lemma closed_refinement_value : forall v T ps,
  has_type [] [] v T -> closed_term v -> value v ->
  predicate_closed (open_qualifier_tm ps v) ->
  qualifier_holds (open_qualifier_tm ps v) ->
  value_relation (R_Refine T ps) (fun R => R) v.
Proof.
  intros v T ps Htype [Hlc [Hfv Hftv]] Hvalue Hclosed Hholds.
  simpl; repeat split; auto.
  destruct T; simpl; auto.
  - eapply core_integer_value; eauto.
  - eapply core_boolean_value; eauto.
Qed.

Lemma semantic_type_safety : forall R close t t',
  semantic_type R close t -> multi t t' ->
  value t' \/ exists t'', t' --> t''.
Proof.
  intros R close t t' Hsemantic Hsteps.
  destruct (Hsemantic t' Hsteps) as [_ [[Hv _] | Hstep]];
    auto.
Qed.

Theorem never_stuck : forall (t t' : tm) (R : rty),
  has_rtype [] empty_rcontext t R ->
  multi t t' ->
  value t' \/ exists t'' : tm, t' --> t''.
Proof.
  intros t t' R Htyped Hsteps.
  eapply (semantic_type_safety R (fun S => S) t t'); [|exact Hsteps].
Qed.

End SystemFRefinementIfNonDeterminismTask.
