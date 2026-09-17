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
Inductive must_terminate : tm -> Prop :=
  | MT_intro : forall t,
      (value t \/ exists u, t --> u) ->
      (forall u, t --> u -> must_terminate u) ->
      must_terminate t.

End SystemFRefinementIfNonDeterminismEvaluation.

From Stdlib Require Import Program.Wf.
From Equations Require Import Equations.
Module SystemFRefinementIfNonDeterminismDenotations.
Import ListNotations SystemFRefinementIfNonDeterminism SystemFRefinementIfNonDeterminismLogic SystemFRefinementIfNonDeterminismTyping SystemFRefinementIfNonDeterminismEvaluation.

Fixpoint rty_size (R : rty) : nat :=
  match R with
  | R_Refine _ _ => 1
  | R_Func R1 R2 => S (rty_size R1 + rty_size R2)
  | R_Exists R1 R2 => S (rty_size R1 + rty_size R2)
  | R_Poly R1 => S (rty_size R1)
  end.

Lemma rty_size_open_tm_rec : forall R k u,
  rty_size (open_rty_tm_rec k u R) = rty_size R.
Proof.
  induction R; intros; simpl; rewrite ?IHR1, ?IHR2, ?IHR; reflexivity.
Qed.

Lemma rty_size_open_tm : forall R u,
  rty_size (open_rty_tm R u) = rty_size R.
Proof.
  intros. apply rty_size_open_tm_rec.
Qed.

Lemma rty_size_open_ty_rec : forall R k U,
  rty_size (open_rty_ty_rec k U R) = rty_size R.
Proof.
  induction R; intros; simpl; rewrite ?IHR1, ?IHR2, ?IHR; reflexivity.
Qed.

Lemma rty_size_open_ty : forall R U,
  rty_size (open_rty_ty R U) = rty_size R.
Proof.
  intros. apply rty_size_open_ty_rec.
Qed.

Equations denotes (R : rty) (v : tm) : Prop by wf (rty_size R) lt :=
  denotes (R_Refine T ps) v :=

      value v /\
      has_type [] empty v T /\
      qualifier_holds (open_qualifier_tm ps v);
  denotes (R_Func R1 R2) v :=

      value v /\
      has_type [] empty v (erase (R_Func R1 R2)) /\
      forall arg,
        denotes R1 arg ->
        locally_closed_tm (tm_app v arg) /\
        must_terminate (tm_app v arg) /\
        forall result,
          multi (tm_app v arg) result ->
          value result ->
          denotes (open_rty_tm R2 arg) result;
  denotes (R_Exists R1 R2) v :=
      value v /\
      has_type [] empty v (erase (R_Exists R1 R2)) /\
      exists witness,
        denotes R1 witness /\
        denotes (open_rty_tm R2 witness) v;
  denotes (R_Poly R1) v :=
      value v /\
      has_type [] empty v (erase (R_Poly R1)) /\
      forall U,
        wf_ty [] U ->
        locally_closed_tm (tm_tapp v U) /\
        must_terminate (tm_tapp v U) /\
        forall result,
          multi (tm_tapp v U) result ->
          value result ->
          denotes (open_rty_ty R1 U) result.
Next Obligation.
  simpl. lia.
Qed.
Next Obligation.
  rewrite rty_size_open_tm. simpl. lia.
Qed.
Next Obligation.
  simpl. lia.
Qed.
Next Obligation.
  rewrite rty_size_open_tm. simpl. lia.
Qed.
Next Obligation.
  rewrite rty_size_open_ty. simpl. lia.
Qed.

Definition evals_denotes (R : rty) (t : tm) : Prop :=
  locally_closed_tm t /\
  must_terminate t /\
  forall v,
    multi t v ->
    value v ->
    denotes R v.

Scheme has_rtype_ind' := Induction for has_rtype Sort Prop
  with subtype_ind' := Induction for subtype Sort Prop.

Lemma in_le_max_atom : forall x L, In x L -> x <= max_atom L.
Proof.
  induction L as [| y L IH]; simpl; intros H.
  - contradiction.
  - destruct H as [<-|H].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; eauto|apply Nat.le_max_r].
Qed.

Lemma fresh_not_in : forall L, ~ In (fresh L) L.
Proof.
  intros L H.
  pose proof (in_le_max_atom (fresh L) L H).
  unfold fresh in *. lia.
Qed.

Fixpoint close_ty_rec (k : nat) (X : atom) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar Y => if Nat.eqb X Y then Ty_BVar k else Ty_FVar Y
  | Ty_Arrow T1 T2 => Ty_Arrow (close_ty_rec k X T1) (close_ty_rec k X T2)
  | Ty_All T1 => Ty_All (close_ty_rec (S k) X T1)
  | Ty_Int => Ty_Int
  | Ty_Bool => Ty_Bool
  end.

Lemma close_ty_open_ty_rec : forall T k X,
  ~ In X (fv_ty T) ->
  close_ty_rec k X (open_ty_rec k (Ty_FVar X) T) = T.
Proof.
  induction T; intros k X HF; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst.
      destruct (Nat.eqb X X) eqn:E2.
      * cbn. rewrite E2. reflexivity.
      * apply Nat.eqb_neq in E2. exfalso. apply E2. reflexivity.
    + simpl. reflexivity.
  - destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E. subst.
      exfalso. apply HF. simpl. left. reflexivity.
    + simpl. reflexivity.
  - f_equal.
    + apply IHT1. intro Hx. apply HF. apply in_or_app. left. exact Hx.
    + apply IHT2. intro Hx. apply HF. apply in_or_app. right. exact Hx.
  - f_equal. apply IHT. exact HF.
  - reflexivity.
  - reflexivity.
Qed.

Lemma open_ty_fresh_inj : forall T S X,
  ~ In X (fv_ty T) -> ~ In X (fv_ty S) ->
  open_ty T (Ty_FVar X) = open_ty S (Ty_FVar X) -> T = S.
Proof.
  intros T S X HT HS E.
  pose proof (f_equal (close_ty_rec 0 X) E) as E'.
  unfold open_ty in E'.
  rewrite (close_ty_open_ty_rec T 0 X HT) in E'.
  rewrite (close_ty_open_ty_rec S 0 X HS) in E'.
  exact E'.
Qed.

Lemma erase_open_rty_tm_rec : forall R k u,
  erase (open_rty_tm_rec k u R) = erase R.
Proof.
  induction R; intros; simpl; try reflexivity;
    rewrite ?IHR1, ?IHR2, ?IHR; reflexivity.
Qed.

Lemma erase_open_rty_tm : forall R u,
  erase (open_rty_tm R u) = erase R.
Proof. intros; apply erase_open_rty_tm_rec. Qed.

Lemma erase_open_rty_ty_rec : forall R k U,
  erase (open_rty_ty_rec k U R) = open_ty_rec k U (erase R).
Proof.
  induction R; intros; simpl; try reflexivity;
    rewrite ?IHR1, ?IHR2, ?IHR; reflexivity.
Qed.

Lemma erase_open_rty_ty : forall R U,
  erase (open_rty_ty R U) = open_ty (erase R) U.
Proof. intros; apply erase_open_rty_ty_rec. Qed.

Lemma subtype_erase : forall Delta RGamma R S,
  subtype Delta RGamma R S -> erase R = erase S.
Proof.
  intros Delta RGamma R S H.
  eapply (subtype_ind'
    (fun _ _ _ _ _ => True)
    (fun _ _ R S _ => erase R = erase S));
    simpl; intros; try exact I; try reflexivity.
  all: cbn in *.
  - specialize (H1 (fresh L) (fresh_not_in L)).
    cbn in H1. rewrite !erase_open_rty_tm in H1.
    rewrite <- H0. f_equal. exact H1.
  - rewrite erase_open_rty_tm in H1. exact H1.
  - specialize (H0 (fresh L) (fresh_not_in L)).
    rewrite !erase_open_rty_tm in H0. exact H0.
  - set (X := fresh (L ++ fv_ty (erase R0) ++ fv_ty (erase S0))).
    assert (~ In X L) as HX.
    { intro HXL. apply (fresh_not_in (L ++ fv_ty (erase R0) ++ fv_ty (erase S0))).
      apply in_or_app. left. exact HXL. }
    specialize (H0 X HX).
    rewrite !erase_open_rty_ty in H0.
    apply f_equal.
    apply open_ty_fresh_inj with (X := X).
    + intro HXR. apply (fresh_not_in (L ++ fv_ty (erase R0) ++ fv_ty (erase S0))).
      apply in_or_app. right. apply in_or_app. left. exact HXR.
    + intro HXS. apply (fresh_not_in (L ++ fv_ty (erase R0) ++ fv_ty (erase S0))).
      apply in_or_app. right. apply in_or_app. right. exact HXS.
    + exact H0.
  - etransitivity; eassumption.
  - exact H.
Qed.

Lemma lookup_erase_context : forall x RGamma R,
  lookup_rcontext x RGamma = Some R ->
  lookup_context x (erase_context RGamma) = Some (erase R).
Proof.
  induction RGamma as [| [y S] RGamma IH]; simpl; intros R H.
  - inversion H.
  - destruct (Nat.eqb x y) eqn:E.
    + inversion H. reflexivity.
    + eauto.
Qed.

Lemma wf_rty_erase : forall Delta RGamma R,
  wf_rty Delta RGamma R -> wf_ty Delta (erase R).
Proof.
  intros Delta RGamma R W.
  induction W; simpl; try eauto.
  - constructor.
    + exact IHW.
    + specialize (H0 (fresh L) (fresh_not_in L)).
      rewrite erase_open_rty_tm in H0. exact H0.
  - specialize (H0 (fresh L) (fresh_not_in L)).
    rewrite erase_open_rty_tm in H0. exact H0.
  - apply (WF_All L). intros X HX.
    specialize (H0 X HX).
    rewrite erase_open_rty_ty in H0. exact H0.
Qed.

Lemma has_rtype_erase : forall Delta RGamma t R,
  has_rtype Delta RGamma t R ->
  has_type Delta (erase_context RGamma) t (erase R).
Proof.
  intros Delta RGamma t R H.
  eapply (has_rtype_ind'
    (fun Delta RGamma t R _ => has_type Delta (erase_context RGamma) t (erase R))
    (fun _ _ _ _ _ => True)); simpl in *; intros; try exact I.
  - apply T_Var.
    + eapply lookup_erase_context; eauto.
    + eapply (wf_rty_erase _ _ _); eauto.
  - apply (T_Abs L); eauto.
    + eapply (wf_rty_erase _ _ _); eauto.
    + intros x Hx. specialize (H0 x Hx).
      rewrite erase_open_rty_tm in H0. exact H0.
  - apply (T_App _ _ _ _ (erase R1) (erase R2)); eauto.
  - apply (T_TAbs L).
    intros X HX. specialize (H0 X HX).
    rewrite erase_open_rty_ty in H0. exact H0.
  - rewrite erase_open_rty_ty. apply T_TApp; eauto.
  - apply T_Int.
  - apply T_Div; eauto.
  - apply T_Arith; eauto.
  - apply T_Choice; eauto.
  - apply T_True.
  - apply T_False.
  - apply T_If; eauto.
  - exact h.
  - rewrite <- (subtype_erase _ _ _ _ s). exact H0.
  - exact H.
Qed.

End SystemFRefinementIfNonDeterminismDenotations.

Module SystemFRefinementIfNonDeterminismTask.
Import ListNotations SystemFRefinementIfNonDeterminism SystemFRefinementIfNonDeterminismLogic SystemFRefinementIfNonDeterminismTyping SystemFRefinementIfNonDeterminismEvaluation SystemFRefinementIfNonDeterminismDenotations.

Lemma lc_ty_open_inv : forall T K k X,
  k < K ->
  lc_ty_at K (open_ty_rec k (Ty_FVar X) T) -> lc_ty_at K T.
Proof.
  induction T; intros K k X HK H; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + apply lc_ty_bvar. apply Nat.eqb_eq in E. lia.
    + inversion H; constructor; lia.
  - constructor.
  - inversion H; constructor; eauto.
  - inversion H. apply lc_ty_all.
    apply (IHT (S K) (S k) X); [lia|assumption].
  - constructor.
  - constructor.
Qed.

Lemma lc_tm_open_inv : forall t K k x,
  lc_tm_at K k (open_tm_rec k (tm_fvar x) t) ->
  lc_tm_at K (S k) t.
Proof.
  induction t; intros K k x H; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + apply lc_tm_bvar. apply Nat.eqb_eq in E. lia.
    + inversion H; constructor; lia.
  - constructor.
  - inversion H. constructor; eauto.
  - inversion H. constructor; eauto.
  - inversion H. constructor. apply IHt with (x := x); eauto.
  - inversion H. constructor; eauto.
  - inversion H. constructor; eauto.
  - inversion H. constructor; eauto.
  - inversion H. constructor; eauto.
  - inversion H. constructor; eauto.
  - constructor.
  - constructor.
  - inversion H. constructor; eauto.
Qed.

Lemma wf_ty_lc : forall Delta T,
  wf_ty Delta T -> lc_ty_at (length Delta) T.
Proof.
  intros Delta T H. induction H; simpl.
  - constructor.
  - constructor; eauto.
  - apply lc_ty_all. specialize (H0 (fresh L) (fresh_not_in L)).
    apply (lc_ty_open_inv T (length (fresh L :: Delta)) 0 (fresh L));
      simpl; try lia; exact H0.
  - constructor.
  - constructor.
Qed.

Lemma lc_tm_ty_open_inv : forall t K j d X,
  d < K ->
  lc_tm_at K j (open_tm_ty_rec d (Ty_FVar X) t) ->
  lc_tm_at K j t.
Proof.
  induction t; intros K j d X HD H; simpl in *.
  - inversion H; constructor; eauto.
  - constructor.
  - inversion H. apply lc_tm_abs.
    + eapply lc_ty_open_inv; eauto.
    + eapply IHt; eauto.
  - inversion H. constructor; eauto.
  - inversion H. apply lc_tm_tabs.
    eapply IHt with (K := S K) (d := S d); eauto. lia.
  - inversion H. apply lc_tm_tapp; eauto.
    eapply lc_ty_open_inv; eauto.
  - constructor.
  - inversion H. constructor; eauto.
  - inversion H. constructor; eauto.
  - inversion H. constructor; eauto.
  - constructor.
  - constructor.
  - inversion H. constructor; eauto.
Qed.

Lemma has_type_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> lc_tm_at (length Delta) 0 t.
Proof.
  intros Delta Gamma t T H. induction H; simpl.
  - constructor.
  - apply lc_tm_abs.
    + apply wf_ty_lc; eauto.
    + specialize (H1 (fresh L) (fresh_not_in L)).
      apply lc_tm_open_inv in H1. exact H1.
  - constructor; eauto.
  - apply lc_tm_tabs. specialize (H0 (fresh L) (fresh_not_in L)).
    apply (lc_tm_ty_open_inv t (length (fresh L :: Delta)) 0 0 (fresh L));
      simpl; try lia; exact H0.
  - constructor; eauto using wf_ty_lc.
  - constructor; eauto.
  - constructor; eauto.
  - constructor; eauto.
  - constructor; eauto.
  - constructor.
  - constructor.
  - constructor; eauto.
Qed.

Lemma canonical_arrow : forall v T1 T2,
  value v -> has_type [] [] v (Ty_Arrow T1 T2) ->
  exists A b, v = tm_abs A b /\ locally_closed_tm (tm_abs A b).
Proof.
  intros v T1 T2 V H. destruct V; simpl in H; inversion H; subst; eauto.
Qed.

Lemma canonical_int : forall v,
  value v -> has_type [] [] v Ty_Int -> exists n : Z, v = tm_int n.
Proof.
  intros v V H. destruct V; simpl in H; inversion H; subst; eauto.
Qed.

Lemma canonical_bool : forall v,
  value v -> has_type [] [] v Ty_Bool -> v = tm_true \/ v = tm_false.
Proof.
  intros v V H. destruct V; simpl in H; inversion H; subst; eauto.
Qed.

Lemma canonical_all : forall v T,
  value v -> has_type [] [] v (Ty_All T) ->
  exists b, v = tm_tabs b /\ locally_closed_tm (tm_tabs b).
Proof.
  intros v T V H. destruct V; simpl in H; inversion H; subst; eauto.
Qed.

Definition value_environment := list (atom * tm).

Fixpoint lookup_value_environment (x : atom) (rho : value_environment) : option tm :=
  match rho with
  | [] => None
  | (y, v) :: rho' => if Nat.eqb x y then Some v else lookup_value_environment x rho'
  end.

Definition context_denotes (RGamma : rcontext) (rho : value_environment) : Prop :=
  forall x R v,
    lookup_rcontext x RGamma = Some R ->
    lookup_value_environment x rho = Some v -> denotes R v.

Lemma must_terminate_multi : forall t u,
  must_terminate t -> multi t u -> must_terminate u.
Proof.
  intros t u MT M. induction M.
  - exact MT.
  - inversion MT as [t0 P All].
    apply IHM. apply All. exact H.
Qed.

Lemma progress_from_evals : forall t t' R,
  evals_denotes R t -> multi t t' ->
  value t' \/ exists t'', t' --> t''.
Proof.
  intros t t' R E M.
  destruct E as [LC [MT D]].
  pose proof (must_terminate_multi t t' MT M) as MT'.
  inversion MT' as [u P All]. exact P.
Qed.

Theorem never_stuck : forall (t t' : tm) (R : rty),
  has_rtype [] empty_rcontext t R ->
  multi t t' ->
  value t' \/ exists t'' : tm, t' --> t''.
Proof.
  intros t t' R H M.
  eapply progress_from_evals; eauto.
Qed.

End SystemFRefinementIfNonDeterminismTask.
