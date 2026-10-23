From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
From Stdlib Require Import ZArith.BinInt.

Module SystemFRefinementIf.

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

Notation "'Bool'" := Ty_Bool (in custom systemf_ty at level 0) : systemf_scope.
Notation "'true'" := tm_true (in custom systemf_tm at level 0) : systemf_scope.
Notation "'false'" := tm_false (in custom systemf_tm at level 0) : systemf_scope.
Notation "'if' t1 'then' t2 'else' t3" := (tm_if t1 t2 t3)
  (in custom systemf_tm at level 200, t1 custom systemf_tm,
   t2 custom systemf_tm, t3 custom systemf_tm at level 200) : systemf_scope.

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
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' -> locally_closed_tm t2 -> locally_closed_tm t3 ->
      tm_if t1 t2 t3 --> tm_if t1' t2 t3
  | ST_IfTrue : forall t2 t3,
      locally_closed_tm t2 -> locally_closed_tm t3 ->
      tm_if tm_true t2 t3 --> t2
  | ST_IfFalse : forall t2 t3,
      locally_closed_tm t2 -> locally_closed_tm t3 ->
      tm_if tm_false t2 t3 --> t3
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
  | T_True : forall Delta Gamma, has_type Delta Gamma tm_true Ty_Bool
  | T_False : forall Delta Gamma, has_type Delta Gamma tm_false Ty_Bool
  | T_If : forall Delta Gamma t1 t2 t3 T,
      has_type Delta Gamma t1 Ty_Bool ->
      has_type Delta Gamma t2 T ->
      has_type Delta Gamma t3 T ->
      has_type Delta Gamma (tm_if t1 t2 t3) T.

Fixpoint max_atom (L : list atom) : atom :=
  match L with
  | [] => 0
  | x :: L' => Nat.max x (max_atom L')
  end.

Definition fresh (L : list atom) : atom := S (max_atom L).

End SystemFRefinementIf.

From Stdlib Require Import Arith.PeanoNat Lists.List ZArith.BinInt.
Module SystemFRefinementIfLogic.
Import ListNotations SystemFRefinementIf.

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

End SystemFRefinementIfLogic.

From Stdlib Require Import Arith.PeanoNat Lists.List Lia ZArith.BinInt.
Module SystemFRefinementIfTyping.
Import ListNotations.
Import SystemFRefinementIf.
Export SystemFRefinementIfLogic.

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

  | RT_True : forall Delta RGamma,
      has_rtype Delta RGamma tm_true (R_Refine Ty_Bool Pred_True)
  | RT_False : forall Delta RGamma,
      has_rtype Delta RGamma tm_false (R_Refine Ty_Bool Pred_True)
  | RT_If : forall Delta RGamma t1 t2 t3 R,
      has_rtype Delta RGamma t1 (R_Refine Ty_Bool Pred_True) ->
      has_rtype Delta RGamma t2 R ->
      has_rtype Delta RGamma t3 R ->
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

End SystemFRefinementIfTyping.

Module SystemFRefinementIfEvaluation.
Import ListNotations SystemFRefinementIf SystemFRefinementIfLogic SystemFRefinementIfTyping.

Inductive multi : tm -> tm -> Prop :=
  | multi_refl : forall t, multi t t
  | multi_step : forall t1 t2 t3,
      t1 --> t2 -> multi t2 t3 -> multi t1 t3.
Notation "t '-->*' u" := (multi t u) (at level 40).

End SystemFRefinementIfEvaluation.

Module SystemFRefinementIfTask.
Import ListNotations SystemFRefinementIf SystemFRefinementIfLogic SystemFRefinementIfTyping SystemFRefinementIfEvaluation.

Fixpoint close_ty_at (depth : nat) (types : list ty) (T : ty) : ty :=
  match T with
  | Ty_BVar index =>
      if index <? depth then Ty_BVar index
      else nth (index - depth) types (Ty_BVar index)
  | Ty_FVar X => Ty_FVar X
  | Ty_Arrow T1 T2 =>
      Ty_Arrow (close_ty_at depth types T1) (close_ty_at depth types T2)
  | Ty_All T1 => Ty_All (close_ty_at (S depth) types T1)
  | Ty_Int => Ty_Int
  | Ty_Bool => Ty_Bool
  end.

Fixpoint close_tm_at (type_depth term_depth : nat)
    (types : list ty) (terms : list tm) (t : tm) : tm :=
  match t with
  | tm_bvar index =>
      if index <? term_depth then tm_bvar index
      else nth (index - term_depth) terms (tm_bvar index)
  | tm_fvar x => tm_fvar x
  | tm_abs T body =>
      tm_abs (close_ty_at type_depth types T)
        (close_tm_at type_depth (S term_depth) types terms body)
  | tm_app t1 t2 =>
      tm_app (close_tm_at type_depth term_depth types terms t1)
        (close_tm_at type_depth term_depth types terms t2)
  | tm_tabs body =>
      tm_tabs (close_tm_at (S type_depth) term_depth types terms body)
  | tm_tapp t1 T =>
      tm_tapp (close_tm_at type_depth term_depth types terms t1)
        (close_ty_at type_depth types T)
  | tm_int n => tm_int n
  | tm_div t1 t2 =>
      tm_div (close_tm_at type_depth term_depth types terms t1)
        (close_tm_at type_depth term_depth types terms t2)
  | tm_arith op t1 t2 =>
      tm_arith op (close_tm_at type_depth term_depth types terms t1)
        (close_tm_at type_depth term_depth types terms t2)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 =>
      tm_if (close_tm_at type_depth term_depth types terms t1)
        (close_tm_at type_depth term_depth types terms t2)
        (close_tm_at type_depth term_depth types terms t3)
  end.

Fixpoint close_qualifier_at (type_depth term_depth : nat)
    (types : list ty) (terms : list tm) (q : qualifier) : qualifier :=
  match q with
  | Pred_True => Pred_True
  | Pred_False => Pred_False
  | Pred_Eq t1 t2 =>
      Pred_Eq (close_tm_at type_depth term_depth types terms t1)
        (close_tm_at type_depth term_depth types terms t2)
  | Pred_Lt t1 t2 =>
      Pred_Lt (close_tm_at type_depth term_depth types terms t1)
        (close_tm_at type_depth term_depth types terms t2)
  | Pred_Le t1 t2 =>
      Pred_Le (close_tm_at type_depth term_depth types terms t1)
        (close_tm_at type_depth term_depth types terms t2)
  | Pred_And p1 p2 =>
      Pred_And (close_qualifier_at type_depth term_depth types terms p1)
        (close_qualifier_at type_depth term_depth types terms p2)
  | Pred_Or p1 p2 =>
      Pred_Or (close_qualifier_at type_depth term_depth types terms p1)
        (close_qualifier_at type_depth term_depth types terms p2)
  | Pred_Not p => Pred_Not (close_qualifier_at type_depth term_depth types terms p)
  end.

Definition can_step (t : tm) : Prop :=
  value t \/ exists t', t --> t'.

Definition canonical (T : ty) (v : tm) : Prop :=
  match T with
  | Ty_Int => exists n, v = tm_int n
  | Ty_Bool => v = tm_true \/ v = tm_false
  | Ty_Arrow _ _ => exists A body, v = tm_abs A body
  | Ty_All _ => exists body, v = tm_tabs body
  | Ty_BVar _ | Ty_FVar _ => False
  end.

Fixpoint related_value (types : list ty) (terms : list tm)
    (R : rty) (v : tm) {struct R} : Prop :=
  match R with
  | R_Refine T q =>
      value v /\ canonical (close_ty_at 0 types T) v /\
      qualifier_holds (close_qualifier_at 0 0 types (v :: terms) q)
  | R_Func R1 R2 =>
      value v /\ (exists A body, v = tm_abs A body) /\
      (forall u, related_value types terms R1 u ->
        forall t', multi (tm_app v u) t' ->
          can_step t' /\
          (value t' -> related_value types (u :: terms) R2 t'))
  | R_Exists R1 R2 =>
      value v /\ exists u, related_value types terms R1 u /\
        related_value types (u :: terms) R2 v
  | R_Poly R1 =>
      value v /\ (exists body, v = tm_tabs body) /\
      (forall U, locally_closed_ty U ->
        forall t', multi (tm_tapp v U) t' ->
          can_step t' /\
          (value t' -> related_value (U :: types) terms R1 t'))
  end.

Definition related_term (types : list ty) (terms : list tm)
    (R : rty) (t : tm) : Prop :=
  locally_closed_tm t /\
  forall t', multi t t' ->
    can_step t' /\ (value t' -> related_value types terms R t').

Fixpoint instantiate_tm_types (environment : list (atom * ty))
    (t : tm) : tm :=
  match environment with
  | [] => t
  | (X, U) :: rest => tm_ty_subst X U (instantiate_tm_types rest t)
  end.

Fixpoint instantiate_tm_terms (environment : list (atom * tm))
    (t : tm) : tm :=
  match environment with
  | [] => t
  | (x, v) :: rest => tm_subst x v (instantiate_tm_terms rest t)
  end.

Definition instantiate_tm (types : list (atom * ty))
    (terms : list (atom * tm)) (t : tm) : tm :=
  instantiate_tm_terms terms (instantiate_tm_types types t).

Fixpoint instantiate_rty_types (environment : list (atom * ty))
    (R : rty) : rty :=
  match environment with
  | [] => R
  | (X, U) :: rest => rty_ty_subst X U (instantiate_rty_types rest R)
  end.

Fixpoint instantiate_rty_terms (environment : list (atom * tm))
    (R : rty) : rty :=
  match environment with
  | [] => R
  | (x, v) :: rest => rty_subst x v (instantiate_rty_terms rest R)
  end.

Definition instantiate_rty (types : list (atom * ty))
    (terms : list (atom * tm)) (R : rty) : rty :=
  instantiate_rty_terms terms (instantiate_rty_types types R).

Fixpoint lookup_term (x : atom) (environment : list (atom * tm)) : option tm :=
  match environment with
  | [] => None
  | (y, v) :: rest =>
      if Nat.eqb x y then Some v else lookup_term x rest
  end.

Fixpoint lookup_type (X : atom) (environment : list (atom * ty)) : option ty :=
  match environment with
  | [] => None
  | (Y, U) :: rest =>
      if Nat.eqb X Y then Some U else lookup_type X rest
  end.

Definition related_context (Delta : ty_context) (RGamma : rcontext)
    (types : list (atom * ty)) (terms : list (atom * tm)) : Prop :=
  NoDup (map fst types) /\ NoDup (map fst terms) /\
  (forall X, In X Delta ->
    exists U, lookup_type X types = Some U /\ locally_closed_ty U) /\
  (forall x R, lookup_rcontext x RGamma = Some R ->
    exists v, lookup_term x terms = Some v /\
      related_value [] [] (instantiate_rty types terms R) v).

Lemma empty_related_context :
  related_context [] empty_rcontext [] [].
Proof.
  repeat split; try constructor; intros; inversion H.
Qed.

Lemma related_term_safe : forall types terms R t t',
  related_term types terms R t -> multi t t' -> can_step t'.
Proof.
  intros types terms R t t' Hrel Hsteps.
  exact (proj1 ((proj2 Hrel) t' Hsteps)).
Qed.

Lemma value_no_step : forall v t, value v -> ~ v --> t.
Proof.
  intros v t Hv Hstep.
  induction Hstep; inversion Hv; subst; try solve [inversion H];
    try solve [inversion Hstep]; try solve [inversion H0].
Qed.

Lemma multi_value : forall v t, value v -> multi v t -> v = t.
Proof.
  intros v t Hv Hmulti.
  inversion Hmulti; subst; auto.
  exfalso; eapply value_no_step; eauto.
Qed.

Lemma predicate_multistep_value : forall v t,
  value v -> predicate_multistep v t -> v = t.
Proof.
  intros v t Hv Hmulti.
  inversion Hmulti; subst; auto.
  exfalso; eapply value_no_step; eauto.
Qed.

Lemma predicate_int_not_zero : forall n,
  qualifier_holds (Pred_Ne (tm_int n) (tm_int 0%Z)) -> n <> 0%Z.
Proof.
  intros n Hnot Heq; subst.
  unfold qualifier_holds, predicate_holds, Pred_Ne in Hnot.
  simpl in Hnot. apply Hnot.
  exists (tm_int 0%Z); repeat split; constructor.
Qed.

Lemma related_divisor_nonzero : forall types terms n,
  related_value types terms
    (R_Refine Ty_Int (Pred_Ne (tm_bvar 0) (tm_int 0%Z)))
    (tm_int n) -> n <> 0%Z.
Proof.
  intros types terms n Hrel.
  simpl in Hrel.
  destruct Hrel as [_ [_ Hholds]].
  apply predicate_int_not_zero; exact Hholds.
Qed.

Lemma multi_trans : forall t1 t2 t3,
  multi t1 t2 -> multi t2 t3 -> multi t1 t3.
Proof.
  intros t1 t2 t3 H12 H23.
  induction H12; eauto using multi.
Qed.

Lemma value_locally_closed : forall v, value v -> locally_closed_tm v.
Proof.
  intros v Hv; inversion Hv; subst; auto; constructor.
Qed.

Lemma related_value_is_value : forall types terms R v,
  related_value types terms R v -> value v.
Proof.
  intros types terms R v Hrel.
  destruct R; exact (proj1 Hrel).
Qed.

Lemma related_term_of_value : forall types terms R v,
  related_value types terms R v -> related_term types terms R v.
Proof.
  intros types terms R v Hrel; split.
  - apply value_locally_closed.
    eapply related_value_is_value; eauto.
  - intros t' Hsteps.
    pose proof (related_value_is_value types terms R v Hrel) as Hv.
    pose proof (multi_value v t' Hv Hsteps) as Heq.
    subst; split; [left; exact Hv | intros _; exact Hrel].
Qed.

Lemma step_deterministic : forall t u w,
  t --> u -> t --> w -> u = w.
Proof.
  intros t u w Hstep.
  generalize dependent w.
  induction Hstep; intros w Hother; inversion Hother; subst;
    try reflexivity; try solve [f_equal; eauto];
    try solve [exfalso; match goal with
      | Hv : value ?v, Hs : step ?v ?u |- _ =>
          exact (value_no_step v u Hv Hs)
      end];
    try solve [match goal with
      | H : tm_int _ --> _ |- _ => inversion H
      | H : tm_true --> _ |- _ => inversion H
      | H : tm_false --> _ |- _ => inversion H
      | H : tm_abs _ _ --> _ |- _ => inversion H
      | H : tm_tabs _ --> _ |- _ => inversion H
      end].
Qed.

Lemma related_term_step : forall types terms R t u,
  locally_closed_tm t -> t --> u ->
  related_term types terms R u -> related_term types terms R t.
Proof.
  intros types terms R t u Hlc Hstep [_ Hrel]; split; auto.
  intros result Hmulti.
  inversion Hmulti; subst.
  - split.
    + right; eauto.
    + intros Hv. exfalso; eapply value_no_step; eauto.
  - assert (u = t2) by (eapply step_deterministic; eauto).
    subst; eapply Hrel; eauto.
Qed.

Lemma close_ty_at_empty : forall T depth,
  close_ty_at depth [] T = T.
Proof.
  induction T; intros depth; simpl; try reflexivity.
  - destruct (n <? depth); simpl; auto.
    destruct (n - depth); reflexivity.
  - rewrite IHT1, IHT2; reflexivity.
  - rewrite IHT; reflexivity.
Qed.

Lemma close_tm_at_empty : forall t type_depth term_depth,
  close_tm_at type_depth term_depth [] [] t = t.
Proof.
  induction t; intros type_depth term_depth; simpl;
    try rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3,
      ?close_ty_at_empty; try reflexivity.
  destruct (n <? term_depth); simpl; auto.
  destruct (n - term_depth); reflexivity.
Qed.

Lemma close_qualifier_at_empty : forall q type_depth term_depth,
  close_qualifier_at type_depth term_depth [] [] q = q.
Proof.
  induction q; intros type_depth term_depth; simpl;
    try rewrite ?IHq, ?IHq1, ?IHq2,
      ?close_tm_at_empty; reflexivity.
Qed.

Lemma not_in_append : forall (x : atom) first second,
  ~ In x (first ++ second) -> ~ In x first /\ ~ In x second.
Proof.
  intros x first second Hnot.
  rewrite in_app_iff in Hnot; tauto.
Qed.

Lemma subst_open_tm_rec : forall body x v depth,
  ~ In x (fv_tm body) ->
  tm_subst x v (open_tm_rec depth (tm_fvar x) body) =
  open_tm_rec depth v body.
Proof.
  induction body; intros x v depth Hfresh; simpl in *;
    try reflexivity.
  - destruct (Nat.eqb depth n); simpl.
    + rewrite Nat.eqb_refl; reflexivity.
    + reflexivity.
  - destruct (Nat.eqb x a) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst. exfalso. apply Hfresh. auto.
    + reflexivity.
  - f_equal. apply IHbody. exact Hfresh.
  - apply not_in_append in Hfresh as [Hleft Hright].
    f_equal; [apply IHbody1 | apply IHbody2]; assumption.
  - f_equal. apply IHbody. exact Hfresh.
  - f_equal. apply IHbody. exact Hfresh.
  - apply not_in_append in Hfresh as [Hleft Hright].
    f_equal; [apply IHbody1 | apply IHbody2]; assumption.
  - apply not_in_append in Hfresh as [Hleft Hright].
    f_equal; [apply IHbody1 | apply IHbody2]; assumption.
  - apply not_in_append in Hfresh as [Hleft Hright].
    apply not_in_append in Hright as [Hmiddle Hlast].
    f_equal; [apply IHbody1 | apply IHbody2 | apply IHbody3]; assumption.
Qed.

Fixpoint map_qualifier (transform : tm -> tm) (q : qualifier) : qualifier :=
  match q with
  | Pred_True => Pred_True
  | Pred_False => Pred_False
  | Pred_Eq t1 t2 => Pred_Eq (transform t1) (transform t2)
  | Pred_Lt t1 t2 => Pred_Lt (transform t1) (transform t2)
  | Pred_Le t1 t2 => Pred_Le (transform t1) (transform t2)
  | Pred_And p1 p2 =>
      Pred_And (map_qualifier transform p1) (map_qualifier transform p2)
  | Pred_Or p1 p2 =>
      Pred_Or (map_qualifier transform p1) (map_qualifier transform p2)
  | Pred_Not p => Pred_Not (map_qualifier transform p)
  end.

Lemma entails_sound : forall Delta RGamma p q,
  entails Delta RGamma p q ->
  forall (transform : tm -> tm) atoms,
    (forall x T ps,
      lookup_rcontext x RGamma = Some (R_Refine T ps) ->
      interpret_qualifier atoms
        (map_qualifier transform (open_qualifier_tm ps (tm_fvar x)))) ->
    interpret_qualifier atoms (map_qualifier transform p) ->
    interpret_qualifier atoms (map_qualifier transform q).
Proof.
  intros Delta RGamma p q Hent.
  induction Hent; intros transform atoms Hcontext Hholds;
    simpl in *; try tauto; eauto.
  - destruct Hholds as [Hleft | Hright];
      [eapply IHHent1 | eapply IHHent2]; eauto.
Qed.

Lemma division_progress : forall types terms t1 t2,
  related_term types terms (R_Refine Ty_Int Pred_True) t1 ->
  related_term types terms
    (R_Refine Ty_Int (Pred_Ne (tm_bvar 0) (tm_int 0%Z))) t2 ->
  can_step (tm_div t1 t2).
Proof.
  intros types terms t1 t2 [Hlc1 Hrel1] [Hlc2 Hrel2].
  destruct (proj1 (Hrel1 t1 (multi_refl t1))) as
    [Hvalue1 | [next1 Hstep1]].
  - pose proof (proj2 (Hrel1 t1 (multi_refl t1)) Hvalue1) as Hcanonical1.
    simpl in Hcanonical1.
    destruct Hcanonical1 as [_ [[n Heq1] _]]; subst t1.
    destruct (proj1 (Hrel2 t2 (multi_refl t2))) as
      [Hvalue2 | [next2 Hstep2]].
    + pose proof (proj2 (Hrel2 t2 (multi_refl t2)) Hvalue2)
        as Hcanonical2.
      simpl in Hcanonical2.
      destruct Hcanonical2 as [_ [[m Heq2] _]]; subst t2.
      assert (Hnonzero : m <> 0%Z).
      { eapply related_divisor_nonzero.
        apply (proj2 (Hrel2 (tm_int m) (multi_refl (tm_int m)))).
        exact Hvalue2. }
      right; exists (tm_int (Z.div n m)).
      apply ST_DivInt; exact Hnonzero.
    + right; exists (tm_div (tm_int n) next2).
      apply ST_Div2; auto using value.
  - right; exists (tm_div next1 t2).
    apply ST_Div1; assumption.
Qed.

Lemma arithmetic_progress : forall types terms op t1 t2,
  related_term types terms (R_Refine Ty_Int Pred_True) t1 ->
  related_term types terms (R_Refine Ty_Int Pred_True) t2 ->
  can_step (tm_arith op t1 t2).
Proof.
  intros types terms op t1 t2 [Hlc1 Hrel1] [Hlc2 Hrel2].
  destruct (proj1 (Hrel1 t1 (multi_refl t1))) as
    [Hvalue1 | [next1 Hstep1]].
  - pose proof (proj2 (Hrel1 t1 (multi_refl t1)) Hvalue1) as Hcanonical1.
    simpl in Hcanonical1.
    destruct Hcanonical1 as [_ [[n Heq1] _]]; subst t1.
    destruct (proj1 (Hrel2 t2 (multi_refl t2))) as
      [Hvalue2 | [next2 Hstep2]].
    + pose proof (proj2 (Hrel2 t2 (multi_refl t2)) Hvalue2)
        as Hcanonical2.
      simpl in Hcanonical2.
      destruct Hcanonical2 as [_ [[m Heq2] _]]; subst t2.
      right; eexists; apply ST_ArithInt.
    + right; exists (tm_arith op (tm_int n) next2).
      apply ST_Arith2; assumption.
  - right; exists (tm_arith op next1 t2).
    apply ST_Arith1; assumption.
Qed.

Lemma conditional_progress : forall types terms condition yes no R,
  related_term types terms (R_Refine Ty_Bool Pred_True) condition ->
  related_term types terms R yes ->
  related_term types terms R no ->
  can_step (tm_if condition yes no).
Proof.
  intros types terms condition yes no R [Hlc Hrel] [Hyes _] [Hno _].
  destruct (proj1 (Hrel condition (multi_refl condition))) as
    [Hvalue | [next Hstep]].
  - pose proof (proj2 (Hrel condition (multi_refl condition)) Hvalue)
      as Hcanonical.
    simpl in Hcanonical.
    destruct Hcanonical as [_ [[Heq | Heq] _]]; subst condition.
    + right; eexists; apply ST_IfTrue; assumption.
    + right; eexists; apply ST_IfFalse; assumption.
  - right; eexists; apply ST_If; eauto.
Qed.

Lemma lc_ty_weaken : forall K T,
  lc_ty_at K T -> forall K', K <= K' -> lc_ty_at K' T.
Proof.
  intros K T Hlc.
  induction Hlc; intros K' Hle.
  - apply lc_ty_bvar; lia.
  - constructor.
  - apply lc_ty_arrow; [apply IHHlc1 | apply IHHlc2]; assumption.
  - apply lc_ty_all. apply IHHlc; lia.
  - constructor.
  - constructor.
Qed.

Lemma lc_tm_weaken : forall K k t,
  lc_tm_at K k t -> forall K' k',
    K <= K' -> k <= k' -> lc_tm_at K' k' t.
Proof.
  intros K k t Hlc.
  induction Hlc; intros K' k' HK Hk; constructor;
    eauto using lc_ty_weaken; try lia;
    eapply IHHlc; lia.
Qed.

Lemma lc_tm_open_rec : forall K k t u,
  lc_tm_at K (S k) t -> locally_closed_tm u ->
  lc_tm_at K k (open_tm_rec k u t).
Proof.
  intros K k t u Hlc Hu.
  revert K k Hlc Hu.
  induction t; intros K k Hlc Hu; simpl in *;
    inversion Hlc; subst; try constructor; eauto.
  - destruct (Nat.eqb k n) eqn:Heq.
    + apply Nat.eqb_eq in Heq; subst.
      eapply lc_tm_weaken; [exact Hu | lia | lia].
    + apply Nat.eqb_neq in Heq; constructor; lia.
Qed.

Lemma lc_ty_open_rec : forall K T U,
  lc_ty_at (S K) T -> locally_closed_ty U ->
  lc_ty_at K (open_ty_rec K U T).
Proof.
  intros K T U Hlc Hu.
  revert K Hlc Hu.
  induction T; intros K Hlc Hu; simpl in *;
    inversion Hlc; subst; try constructor; eauto.
  destruct (Nat.eqb K n) eqn:Heq.
  - apply Nat.eqb_eq in Heq; subst.
    eapply lc_ty_weaken; [exact Hu | lia].
  - apply Nat.eqb_neq in Heq; constructor; lia.
Qed.

Lemma lc_tm_ty_open_rec : forall K k t U,
  lc_tm_at (S K) k t -> locally_closed_ty U ->
  lc_tm_at K k (open_tm_ty_rec K U t).
Proof.
  intros K k t U Hlc Hu.
  revert K k Hlc Hu.
  induction t; intros K k Hlc Hu; simpl in *;
    inversion Hlc; subst; try constructor;
    eauto using lc_ty_open_rec.
Qed.

Lemma step_preserves_lc : forall t u,
  t --> u -> locally_closed_tm t -> locally_closed_tm u.
Proof.
  intros t u Hstep.
  induction Hstep; intros Hlc; inversion Hlc; subst;
    try solve [constructor; eauto; apply IHHstep; assumption];
    try solve [assumption].
  - inversion H5; subst.
    eapply lc_tm_open_rec; eauto using value_locally_closed.
  - inversion H5; subst.
    eapply lc_tm_ty_open_rec; eauto.
Qed.

Lemma multi_preserves_lc : forall t u,
  multi t u -> locally_closed_tm t -> locally_closed_tm u.
Proof.
  intros t u Hsteps Hlc.
  induction Hsteps; eauto using step_preserves_lc.
Qed.

Lemma related_term_reduction : forall types terms R t u,
  related_term types terms R t -> multi t u ->
  related_term types terms R u.
Proof.
  intros types terms R t u [Hlc Hrel] Hsteps.
  split.
  - eapply multi_preserves_lc; eauto.
  - intros result Hfuture.
    apply Hrel.
    eapply multi_trans; eauto.
Qed.

Lemma related_term_conditional : forall types terms condition yes no R,
  related_term types terms (R_Refine Ty_Bool Pred_True) condition ->
  related_term types terms R yes ->
  related_term types terms R no ->
  related_term types terms R (tm_if condition yes no).
Proof.
  intros types terms condition yes no R Hcondition Hyes Hno.
  split.
  - constructor; [exact (proj1 Hcondition) | exact (proj1 Hyes) | exact (proj1 Hno)].
  - intros result Hsteps.
    remember (tm_if condition yes no) as start eqn:Heq.
    revert condition yes no Hcondition Hyes Hno Heq.
    induction Hsteps; intros condition yes no Hcondition Hyes Hno Heq;
      subst.
    + split.
      * eapply conditional_progress; eauto.
      * intros Hvalue; inversion Hvalue.
    + inversion H; subst.
      * eapply (IHHsteps t1' yes no).
        -- eapply related_term_reduction; [exact Hcondition |].
           eapply multi_step; [eassumption | constructor].
        -- exact Hyes.
        -- exact Hno.
        -- reflexivity.
      * exact ((proj2 Hyes) _ Hsteps).
      * exact ((proj2 Hno) _ Hsteps).
Qed.

Lemma related_integer_true : forall types terms n,
  related_value types terms (R_Refine Ty_Int Pred_True) (tm_int n).
Proof.
  intros types terms n; simpl.
  split; [constructor |].
  split; [exists n; reflexivity | exact I].
Qed.

Lemma related_term_division : forall types terms t1 t2,
  related_term types terms (R_Refine Ty_Int Pred_True) t1 ->
  related_term types terms
    (R_Refine Ty_Int (Pred_Ne (tm_bvar 0) (tm_int 0%Z))) t2 ->
  related_term types terms (R_Refine Ty_Int Pred_True) (tm_div t1 t2).
Proof.
  intros types terms t1 t2 Hleft Hright.
  split.
  - constructor; [exact (proj1 Hleft) | exact (proj1 Hright)].
  - intros result Hsteps.
    remember (tm_div t1 t2) as start eqn:Heq.
    revert t1 t2 Hleft Hright Heq.
    induction Hsteps; intros left_operand right_operand Hleft Hright Heq;
      subst.
    + split.
      * eapply division_progress; eauto.
      * intros Hvalue; inversion Hvalue.
    + inversion H; subst.
      * eapply (IHHsteps t1' right_operand).
        -- eapply related_term_reduction; [exact Hleft |].
           eapply multi_step; [eassumption | constructor].
        -- exact Hright.
        -- reflexivity.
      * eapply (IHHsteps left_operand t2').
        -- exact Hleft.
        -- eapply related_term_reduction; [exact Hright |].
           eapply multi_step; [eassumption | constructor].
        -- reflexivity.
      * exact ((proj2 (related_term_of_value types terms
          (R_Refine Ty_Int Pred_True) (tm_int (Z.div n m))
          (related_integer_true types terms (Z.div n m)))) _ Hsteps).
Qed.

Lemma application_progress : forall types terms t1 t2 R1 R2,
  related_term types terms (R_Func R1 R2) t1 ->
  related_term types terms R1 t2 ->
  can_step (tm_app t1 t2).
Proof.
  intros types terms t1 t2 R1 R2 [Hlc1 Hrel1] [Hlc2 Hrel2].
  destruct (proj1 (Hrel1 t1 (multi_refl t1))) as
    [Hvalue1 | [next1 Hstep1]].
  - pose proof (proj2 (Hrel1 t1 (multi_refl t1)) Hvalue1) as Hfunction.
    simpl in Hfunction.
    destruct Hfunction as [_ [[A [body Heq]] _]]; subst t1.
    destruct (proj1 (Hrel2 t2 (multi_refl t2))) as
      [Hvalue2 | [next2 Hstep2]].
    + right; exists (open_tm body t2).
      apply ST_AppAbs; [eapply value_locally_closed; constructor; exact Hlc1 | assumption].
    + right; exists (tm_app (tm_abs A body) next2).
      apply ST_App2; [constructor; exact Hlc1 | assumption].
  - right; exists (tm_app next1 t2).
    apply ST_App1; assumption.
Qed.

Lemma related_term_application : forall types terms t1 t2 R1 R2,
  related_term types terms (R_Func R1 R2) t1 ->
  related_term types terms R1 t2 ->
  related_term types terms (R_Exists R1 R2) (tm_app t1 t2).
Proof.
  intros types terms t1 t2 R1 R2 Hleft Hright.
  split.
  - constructor; [exact (proj1 Hleft) | exact (proj1 Hright)].
  - intros result Hsteps.
    remember (tm_app t1 t2) as start eqn:Heq.
    revert t1 t2 Hleft Hright Heq.
    induction Hsteps; intros left_operand right_operand Hleft Hright Heq;
      subst.
    + split.
      * eapply application_progress; eauto.
      * intros Hvalue; inversion Hvalue.
    + inversion H; subst.
      * pose proof (proj2 Hleft (tm_abs T t) (multi_refl (tm_abs T t))) as Hleft_at_value.
        pose proof (proj2 Hright right_operand (multi_refl right_operand)) as Hright_at_value.
        assert (Hfunction : related_value types terms (R_Func R1 R2) (tm_abs T t)).
        { apply Hleft_at_value; constructor; assumption. }
        assert (Hargument : related_value types terms R1 right_operand).
        { apply Hright_at_value; assumption. }
        destruct Hfunction as [_ [_ Happly]].
        destruct (Happly right_operand Hargument t3
          (multi_step _ _ _ H Hsteps)) as [Hprogress Hresult].
        split; [exact Hprogress |].
        intros Hvalue.
        simpl; split; [exact Hvalue |].
        exists right_operand; split; [exact Hargument |].
        exact (Hresult Hvalue).
      * eapply (IHHsteps t1' right_operand).
        -- eapply related_term_reduction; [exact Hleft |].
           eapply multi_step; [eassumption | constructor].
        -- exact Hright.
        -- reflexivity.
      * eapply (IHHsteps left_operand t2').
        -- exact Hleft.
        -- eapply related_term_reduction; [exact Hright |].
           eapply multi_step; [eassumption | constructor].
        -- reflexivity.
Qed.

Lemma type_application_progress : forall types terms t U R,
  related_term types terms (R_Poly R) t -> locally_closed_ty U ->
  can_step (tm_tapp t U).
Proof.
  intros types terms t U R [Hlc Hrel] HU.
  destruct (proj1 (Hrel t (multi_refl t))) as
    [Hvalue | [next Hstep]].
  - pose proof (proj2 (Hrel t (multi_refl t)) Hvalue) as Hpoly.
    simpl in Hpoly.
    destruct Hpoly as [_ [[body Heq] _]]; subst t.
    right; exists (open_tm_ty body U).
    apply ST_TAppTabs; [eapply value_locally_closed; constructor; exact Hlc | exact HU].
  - right; exists (tm_tapp next U).
    apply ST_TApp; assumption.
Qed.

Lemma related_term_type_application : forall types terms t U R,
  related_term types terms (R_Poly R) t -> locally_closed_ty U ->
  related_term (U :: types) terms R (tm_tapp t U).
Proof.
  intros types terms t U R Hpoly HU.
  split.
  - constructor; [exact (proj1 Hpoly) | exact HU].
  - intros result Hsteps.
    remember (tm_tapp t U) as start eqn:Heq.
    revert t Hpoly Heq.
    induction Hsteps; intros term Hpoly Heq; subst.
    + split.
      * eapply type_application_progress; eauto.
      * intros Hvalue; inversion Hvalue.
    + inversion H; subst.
      * pose proof (proj2 Hpoly (tm_tabs t) (multi_refl (tm_tabs t)))
          as Hpoly_at_value.
        assert (Hfunction : related_value types terms (R_Poly R) (tm_tabs t)).
        { apply Hpoly_at_value; constructor; assumption. }
        destruct Hfunction as [_ [_ Happly]].
        exact (Happly U HU t3 (multi_step _ _ _ H Hsteps)).
      * eapply (IHHsteps t').
        -- eapply related_term_reduction; [exact Hpoly |].
           eapply multi_step; [eassumption | constructor].
        -- reflexivity.
Qed.

Lemma close_ty_at_lc : forall K T types,
  lc_ty_at K T -> close_ty_at K types T = T.
Proof.
  intros K T types Hlc.
  induction Hlc; simpl; try reflexivity.
  - apply Nat.ltb_lt in H; rewrite H; reflexivity.
  - rewrite IHHlc1, IHHlc2; reflexivity.
  - rewrite IHHlc; reflexivity.
Qed.

Lemma close_tm_at_lc : forall K k t types terms,
  lc_tm_at K k t -> close_tm_at K k types terms t = t.
Proof.
  intros K k t types terms Hlc.
  induction Hlc; simpl; try reflexivity;
    try rewrite ?IHHlc, ?IHHlc1, ?IHHlc2, ?IHHlc3;
    try rewrite (close_ty_at_lc _ _ _ H); try reflexivity.
  apply Nat.ltb_lt in H; rewrite H; reflexivity.
Qed.

Lemma multi_predicate_multistep : forall t u,
  multi t u -> predicate_multistep t u.
Proof.
  intros t u Hsteps; induction Hsteps; eauto using predicate_multistep.
Qed.

Lemma related_term_arithmetic_true : forall types terms op t1 t2,
  related_term types terms (R_Refine Ty_Int Pred_True) t1 ->
  related_term types terms (R_Refine Ty_Int Pred_True) t2 ->
  related_term types terms (R_Refine Ty_Int Pred_True)
    (tm_arith op t1 t2).
Proof.
  intros types terms op t1 t2 Hleft Hright.
  split.
  - constructor; [exact (proj1 Hleft) | exact (proj1 Hright)].
  - intros result Hsteps.
    remember (tm_arith op t1 t2) as start eqn:Heq.
    revert t1 t2 Hleft Hright Heq.
    induction Hsteps; intros left_operand right_operand Hleft Hright Heq;
      subst.
    + split.
      * eapply arithmetic_progress; eauto.
      * intros Hvalue; inversion Hvalue.
    + inversion H; subst.
      * eapply (IHHsteps t1' right_operand).
        -- eapply related_term_reduction; [exact Hleft |].
           eapply multi_step; [eassumption | constructor].
        -- exact Hright.
        -- reflexivity.
      * eapply (IHHsteps left_operand t2').
        -- exact Hleft.
        -- eapply related_term_reduction; [exact Hright |].
           eapply multi_step; [eassumption | constructor].
        -- reflexivity.
      * exact ((proj2 (related_term_of_value types terms
          (R_Refine Ty_Int Pred_True) (tm_int (eval_integer_operator op n m))
          (related_integer_true types terms (eval_integer_operator op n m))))
          _ Hsteps).
Qed.

Lemma related_term_arithmetic_exact : forall types terms op t1 t2,
  related_term types terms (R_Refine Ty_Int Pred_True) t1 ->
  related_term types terms (R_Refine Ty_Int Pred_True) t2 ->
  related_term types terms
    (R_Refine Ty_Int
      (Pred_Eq (tm_bvar 0) (tm_arith op t1 t2)))
    (tm_arith op t1 t2).
Proof.
  intros types terms op t1 t2 Hleft Hright.
  pose proof (related_term_arithmetic_true types terms op t1 t2 Hleft Hright)
    as Hbase.
  destruct Hbase as [Hlc Hsafe].
  split; [exact Hlc |].
  intros result Hsteps.
  destruct (Hsafe result Hsteps) as [Hprogress Hresult].
  split; [exact Hprogress |].
  intros Hvalue.
  pose proof (Hresult Hvalue) as Hcanonical.
  simpl in Hcanonical.
  destruct Hcanonical as [_ [[n Heq] _]].
  subst result.
  simpl.
  split; [constructor |].
  split; [exists n; reflexivity |].
  change (qualifier_holds
    (Pred_Eq (tm_int n)
      (close_tm_at 0 0 types (tm_int n :: terms) (tm_arith op t1 t2)))).
  rewrite (close_tm_at_lc 0 0 (tm_arith op t1 t2)
    types (tm_int n :: terms) Hlc).
  unfold qualifier_holds, predicate_holds; simpl.
  exists (tm_int n); repeat split; try constructor.
  exact (multi_predicate_multistep _ _ Hsteps).
Qed.

Definition fundamental_property : Prop :=
  forall Delta RGamma t R,
    has_rtype Delta RGamma t R ->
    forall types terms,
      related_context Delta RGamma types terms ->
      related_term [] [] (instantiate_rty types terms R)
        (instantiate_tm types terms t).

Lemma fundamental_integer : forall Delta RGamma n types terms,
  related_context Delta RGamma types terms ->
  related_term [] []
    (instantiate_rty types terms
      (R_Refine Ty_Int (Pred_Eq (tm_bvar 0) (tm_int n))))
    (instantiate_tm types terms (tm_int n)).
Proof.
  intros Delta RGamma n types terms _.
  assert (Htype_rty : forall environment,
    instantiate_rty_types environment
      (R_Refine Ty_Int (Pred_Eq (tm_bvar 0) (tm_int n))) =
      R_Refine Ty_Int (Pred_Eq (tm_bvar 0) (tm_int n))).
  { induction environment as [|[X U] tail IH]; simpl; auto.
    rewrite IH; reflexivity. }
  assert (Hterm_rty : forall environment,
    instantiate_rty_terms environment
      (R_Refine Ty_Int (Pred_Eq (tm_bvar 0) (tm_int n))) =
      R_Refine Ty_Int (Pred_Eq (tm_bvar 0) (tm_int n))).
  { induction environment as [|[x v] rest IH]; simpl; auto.
    rewrite IH; reflexivity. }
  assert (Htype_tm : forall environment,
    instantiate_tm_types environment (tm_int n) = tm_int n).
  { induction environment as [|[X U] tail IH]; simpl; auto.
    rewrite IH; reflexivity. }
  assert (Hterm_tm : forall environment,
    instantiate_tm_terms environment (tm_int n) = tm_int n).
  { induction environment as [|[x v] rest IH]; simpl; auto.
    rewrite IH; reflexivity. }
  assert (Hvalue : related_value [] []
    (instantiate_rty types terms
      (R_Refine Ty_Int (Pred_Eq (tm_bvar 0) (tm_int n))))
    (instantiate_tm types terms (tm_int n))).
  { unfold instantiate_rty, instantiate_tm.
    rewrite Htype_rty, Hterm_rty, Htype_tm, Hterm_tm.
    simpl; split; [constructor |].
    split; [exists n; reflexivity |].
    unfold qualifier_holds, predicate_holds; simpl.
    exists (tm_int n); repeat split; constructor. }
  exact (related_term_of_value [] [] _ _ Hvalue).
Qed.

Lemma instantiate_tm_if : forall types terms condition yes no,
  instantiate_tm types terms (tm_if condition yes no) =
  tm_if (instantiate_tm types terms condition)
    (instantiate_tm types terms yes)
    (instantiate_tm types terms no).
Proof.
  intros types terms condition yes no.
  assert (Htype : forall environment,
    instantiate_tm_types environment (tm_if condition yes no) =
    tm_if (instantiate_tm_types environment condition)
      (instantiate_tm_types environment yes)
      (instantiate_tm_types environment no)).
  { induction environment as [|[X U] rest IH]; simpl; auto.
    rewrite IH; reflexivity. }
  assert (Hterm : forall environment a b c,
    instantiate_tm_terms environment (tm_if a b c) =
    tm_if (instantiate_tm_terms environment a)
      (instantiate_tm_terms environment b)
      (instantiate_tm_terms environment c)).
  { induction environment as [|[x v] rest IH];
      intros a b c; simpl; auto.
    rewrite IH; reflexivity. }
  unfold instantiate_tm.
  rewrite Htype, Hterm; reflexivity.
Qed.

Lemma fundamental_if_rule : forall types terms condition yes no R,
  related_term [] [] (R_Refine Ty_Bool Pred_True)
    (instantiate_tm types terms condition) ->
  related_term [] [] R (instantiate_tm types terms yes) ->
  related_term [] [] R (instantiate_tm types terms no) ->
  related_term [] [] R
    (instantiate_tm types terms (tm_if condition yes no)).
Proof.
  intros types terms condition yes no R Hcondition Hyes Hno.
  rewrite instantiate_tm_if.
  eapply related_term_conditional; eauto.
Qed.

Lemma fundamental_implies_never_stuck :
  fundamental_property ->
  forall (t t' : tm) (R : rty),
    has_rtype [] empty_rcontext t R ->
    multi t t' -> can_step t'.
Proof.
  intros Hfund t t' R Htyped Hsteps.
  pose proof (Hfund [] empty_rcontext t R Htyped [] []
    empty_related_context) as Hrel.
  simpl in Hrel.
  eapply related_term_safe; eauto.
Qed.

Theorem never_stuck : forall (t t' : tm) (R : rty),
  has_rtype [] empty_rcontext t R ->
  multi t t' ->
  value t' \/ exists t'' : tm, t' --> t''.
Proof.
  intros t t' R Htyped Hsteps.
  eapply fundamental_implies_never_stuck; eauto.
Qed.

End SystemFRefinementIfTask.
