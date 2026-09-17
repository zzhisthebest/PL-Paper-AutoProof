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

Lemma erase_open_rty_tm_rec : forall k R u,
  erase (open_rty_tm_rec k u R) = erase R.
Proof.
  intros k R; revert k;
  induction R as [T ps | R1 IH1 R2 IH2 | R1 IH1 R2 IH2 | R1 IH1].
  - intros; reflexivity.
  - intros; simpl; f_equal; [apply IH1 | apply IH2].
  - intros; simpl; apply IH2.
  - intros; simpl; f_equal; apply IH1.
Qed.

Lemma erase_open_rty_tm : forall R u,
  erase (open_rty_tm R u) = erase R.
Proof. intros; apply erase_open_rty_tm_rec. Qed.

Lemma erase_open_rty_ty_rec : forall k R U,
  erase (open_rty_ty_rec k U R) = open_ty_rec k U (erase R).
Proof.
  intros k R; revert k;
  induction R as [T ps | R1 IH1 R2 IH2 | R1 IH1 R2 IH2 | R1 IH1].
  - intros; reflexivity.
  - intros; simpl; f_equal; [apply IH1 | apply IH2].
  - intros; simpl; apply IH2.
  - intros; simpl; f_equal; apply IH1.
Qed.

Lemma erase_open_rty_ty : forall R U,
  erase (open_rty_ty R U) = open_ty (erase R) U.
Proof. intros; apply erase_open_rty_ty_rec. Qed.

Lemma max_atom_in : forall x L, In x L -> x <= max_atom L.
Proof.
  intros x L; induction L as [|a L IH]; simpl; intros H;
    [exact (False_rect _ H) |].
  destruct H as [-> | H].
  - apply Nat.le_max_l.
  - eapply Nat.le_trans; [apply IH; exact H | apply Nat.le_max_r].
Qed.

Lemma fresh_not_in : forall L, ~ In (fresh L) L.
Proof.
  intros L H.
  unfold fresh in H.
  pose proof (max_atom_in (S (max_atom L)) L H).
  lia.
Qed.

Lemma open_ty_fvar_inj : forall k X T U,
  ~ In X (fv_ty T) -> ~ In X (fv_ty U) ->
  open_ty_rec k (Ty_FVar X) T = open_ty_rec k (Ty_FVar X) U -> T = U.
Proof.
  intros k X T; revert k X;
  induction T as [i | a | T1 IH1 T2 IH2 | T IH | |].
  - intros k X U HT HU E.
    destruct U as [j | b | U1 U2 | U | |]; simpl in E.
    + destruct (Nat.eqb k i) eqn:Ei.
      * destruct (Nat.eqb k j) eqn:Ej; simpl in E.
        -- apply Nat.eqb_eq in Ei; apply Nat.eqb_eq in Ej; subst; reflexivity.
        -- inversion E.
      * destruct (Nat.eqb k j) eqn:Ej; simpl in E.
        -- inversion E.
        -- inversion E; reflexivity.
    + destruct (Nat.eqb k i) eqn:Ei; simpl in E.
      * apply Nat.eqb_eq in Ei; subst.
        inversion E; subst.
        exfalso; apply HU; simpl; auto.
      * inversion E.
    + destruct (Nat.eqb k i); simpl in E; inversion E.
    + destruct (Nat.eqb k i); simpl in E; inversion E.
    + destruct (Nat.eqb k i); simpl in E; inversion E.
    + destruct (Nat.eqb k i); simpl in E; inversion E.
  - intros k X U HT HU E.
    destruct U as [j | b | U1 U2 | U | |]; simpl in E.
    + destruct (Nat.eqb k j) eqn:Ej; simpl in E.
      * apply Nat.eqb_eq in Ej; subst.
        inversion E; subst.
        exfalso; apply HT; simpl; auto.
      * inversion E.
    + inversion E; reflexivity.
    + inversion E.
    + inversion E.
    + inversion E.
    + inversion E.
  - intros k X U HT HU E.
    destruct U as [j | b | U1 U2 | U | |]; simpl in E.
    + destruct (Nat.eqb k j); simpl in E; inversion E.
    + inversion E.
    + injection E as E1 E2.
      f_equal.
      * apply IH1 with (k := k) (X := X); [intro H; apply HT; apply in_or_app; left; exact H |
                    intro H; apply HU; apply in_or_app; left; exact H | exact E1].
      * apply IH2 with (k := k) (X := X); [intro H; apply HT; apply in_or_app; right; exact H |
                    intro H; apply HU; apply in_or_app; right; exact H | exact E2].
    + inversion E.
    + inversion E.
    + inversion E.
  - intros k X U HT HU E.
    destruct U as [j | b | U1 U2 | U | |]; simpl in E.
    + destruct (Nat.eqb k j); simpl in E; inversion E.
    + inversion E.
    + inversion E.
    + injection E as E'.
      f_equal.
      apply IH with (k := S k) (X := X).
      * exact HT.
      * exact HU.
      * exact E'.
    + inversion E.
    + inversion E.
  - intros k X U HT HU E.
    destruct U as [j | b | U1 U2 | U | |]; simpl in E.
    + destruct (Nat.eqb k j); simpl in E; inversion E.
    + inversion E.
    + inversion E.
    + inversion E.
    + reflexivity.
    + inversion E.
  - intros k X U HT HU E.
    destruct U as [j | b | U1 U2 | U | |]; simpl in E.
    + destruct (Nat.eqb k j); simpl in E; inversion E.
    + inversion E.
    + inversion E.
    + inversion E.
    + inversion E.
    + reflexivity.
Qed.

Lemma fresh_not_in_left : forall L M,
  ~ In (fresh (L ++ M)) L.
Proof.
  intros L M H.
  apply (fresh_not_in (L ++ M)).
  apply in_or_app; left; exact H.
Qed.

Lemma fresh_not_in_middle : forall L M N,
  ~ In (fresh (L ++ M ++ N)) M.
Proof.
  intros L M N H.
  apply (fresh_not_in (L ++ M ++ N)).
  apply in_or_app; right; apply in_or_app; left; exact H.
Qed.

Lemma fresh_not_in_right : forall L M N,
  ~ In (fresh (L ++ M ++ N)) N.
Proof.
  intros L M N H.
  apply (fresh_not_in (L ++ M ++ N)).
  apply in_or_app; right; apply in_or_app; right; exact H.
Qed.

Lemma erase_subtype : forall Delta RGamma R S,
  subtype Delta RGamma R S -> erase R = erase S.
Proof.
  intros Delta RGamma R S H; induction H; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite (IHsubtype).
    assert (E := H1 (fresh L) (fresh_not_in L)).
    rewrite (erase_open_rty_tm _ _) in E.
    rewrite (erase_open_rty_tm _ _) in E.
    rewrite E; reflexivity.
  - rewrite (IHsubtype); rewrite erase_open_rty_tm; reflexivity.
  - assert (E := H2 (fresh L) (fresh_not_in L)).
    rewrite (erase_open_rty_tm _ _) in E.
    exact E.
  - assert (E := H0 (fresh (L ++ fv_ty (erase R) ++ fv_ty (erase S)))
      (fresh_not_in_left L (fv_ty (erase R) ++ fv_ty (erase S)))).
    rewrite (erase_open_rty_ty _ _) in E.
    rewrite (erase_open_rty_ty _ _) in E.
    f_equal.
    apply open_ty_fvar_inj with
      (k := 0) (T := erase R) (U := erase S)
      (X := fresh (L ++ fv_ty (erase R) ++ fv_ty (erase S))).
    + apply fresh_not_in_middle.
    + apply fresh_not_in_right.
    + exact E.
  - rewrite (IHsubtype1); rewrite (IHsubtype2); reflexivity.
Qed.

Hint Rewrite erase_open_rty_tm erase_open_rty_ty : erase_simp.

Lemma lookup_erase_context : forall x RGamma R,
  lookup_rcontext x RGamma = Some R ->
  lookup_context x (erase_context RGamma) = Some (erase R).
Proof.
  intros x RGamma R H; induction RGamma as [|[y S] RGamma IH]; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + inversion H; reflexivity.
    + eapply IH; exact H.
Qed.

Lemma erase_wf_rty : forall Delta RGamma R,
  wf_rty Delta RGamma R -> wf_ty Delta (erase R).
Proof.
  intros Delta RGamma R H; induction H; simpl;
    autorewrite with erase_simp in *.
  - assumption.
  - constructor.
    + exact IHwf_rty.
    + specialize (H1 (fresh L) (fresh_not_in L));
      rewrite (erase_open_rty_tm _ _) in H1; exact H1.
  - specialize (H1 (fresh L) (fresh_not_in L));
    rewrite (erase_open_rty_tm _ _) in H1; exact H1.
  - apply WF_All with (L := L).
    intros X HX.
    specialize (H0 X HX).
    rewrite (erase_open_rty_ty _ _) in H0.
    exact H0.
Qed.

Lemma erase_has_rtype : forall Delta RGamma t R,
  has_rtype Delta RGamma t R ->
  has_type Delta (erase_context RGamma) t (erase R).
Proof.
  intros Delta RGamma t R H; induction H; simpl in *;
    autorewrite with erase_simp in *;
    try solve [eauto using erase_wf_rty].
  - eapply T_Var.
    + apply lookup_erase_context; exact H.
    + apply (erase_wf_rty Delta RGamma R); exact H0.
  - eapply T_Abs with (L := L).
    + apply (erase_wf_rty Delta RGamma R1); exact H.
    + intros x hx.
      specialize (H1 x hx).
      rewrite (erase_open_rty_tm _ _) in H1.
      exact H1.
  - eapply T_App; eauto.
  - eapply T_TAbs with (L := L).
    intros X hx.
    match goal with
    | [ Hx : forall X : atom, ~ In X L -> _ |- _ ] =>
        specialize (Hx X hx); rewrite (erase_open_rty_ty _ _) in Hx; exact Hx
    end.
  - eapply T_TApp; eauto.
  - constructor.
  - eapply T_Div; eauto.
  - eapply T_Arith; eauto.
  - constructor.
  - constructor.
  - eapply T_If; eauto.
  - rewrite (erase_subtype _ _ _ _ H1) in IHhas_rtype.
    exact IHhas_rtype.
Qed.

Theorem never_stuck : forall (t t' : tm) (R : rty),
  has_rtype [] empty_rcontext t R ->
  multi t t' ->
  value t' \/ exists t'' : tm, t' --> t''.
Proof.
Qed.

End SystemFRefinementIfTask.
