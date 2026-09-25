From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
From Stdlib Require Import ZArith.BinInt.

Module SystemFRefinementRecursion.

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

  | tm_fix : ty -> ty -> tm -> tm -> tm
  | tm_ifzero : tm -> tm -> tm -> tm.

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
  | tm_fix A B metric body =>
      tm_fix (A) (B)
        (open_tm_rec (S k) u metric) (open_tm_rec (S (S k)) u body)
  | tm_ifzero t t0 t1 =>
      tm_ifzero (open_tm_rec k u t) (open_tm_rec k u t0) (open_tm_rec k u t1)
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
  | tm_fix A B metric body => fv_tm metric ++ fv_tm body
  | tm_ifzero t t0 t1 => fv_tm t ++ fv_tm t0 ++ fv_tm t1
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
  | tm_fix A B metric body => fv_ty A ++ fv_ty B ++ ftv_tm metric ++ ftv_tm body
  | tm_ifzero t t0 t1 => ftv_tm t ++ ftv_tm t0 ++ ftv_tm t1
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
  | tm_fix A B metric body =>
      tm_fix (open_ty_rec k U A) (open_ty_rec k U B)
        (open_tm_ty_rec k U metric) (open_tm_ty_rec k U body)
  | tm_ifzero t t0 t1 =>
      tm_ifzero (open_tm_ty_rec k U t) (open_tm_ty_rec k U t0) (open_tm_ty_rec k U t1)
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
  | tm_fix A B metric body =>
      tm_fix (ty_subst X U A) (ty_subst X U B)
        (tm_ty_subst X U metric) (tm_ty_subst X U body)
  | tm_ifzero t t0 t1 =>
      tm_ifzero (tm_ty_subst X U t) (tm_ty_subst X U t0) (tm_ty_subst X U t1)
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
  | tm_fix A B metric body =>
      tm_fix (A) (B)
        (tm_subst x s metric) (tm_subst x s body)
  | tm_ifzero t t0 t1 =>
      tm_ifzero (tm_subst x s t) (tm_subst x s t0) (tm_subst x s t1)
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
      lc_tm_at K k t1 -> lc_tm_at K k t2 ->
      lc_tm_at K k (tm_arith op t1 t2)
  | lc_tm_fix : forall K k A B metric body,
      lc_ty_at K A -> lc_ty_at K B ->
      lc_tm_at K (S k) metric ->
      lc_tm_at K (S (S k)) body ->
      lc_tm_at K k (tm_fix A B metric body)
  | lc_tm_ifzero : forall K k t t0 t1,
      lc_tm_at K k t -> lc_tm_at K k t0 -> lc_tm_at K k t1 ->
      lc_tm_at K k (tm_ifzero t t0 t1).

Definition locally_closed_tm (t : tm) : Prop := lc_tm_at 0 0 t.

Inductive value : tm -> Prop :=
  | v_abs : forall T t,
      locally_closed_tm (tm_abs T t) ->
      value (tm_abs T t)
  | v_tabs : forall t,
      locally_closed_tm (tm_tabs t) ->
      value (tm_tabs t)
  | v_int : forall n : Z, value (tm_int n)
  | v_fix : forall A B metric body,
      locally_closed_tm (tm_fix A B metric body) ->
      value (tm_fix A B metric body).

Definition open_fix_body (body f x : tm) : tm :=
  open_tm (open_tm_rec 1 f body) x.

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
  | ST_AppFix : forall A B metric body v,
      locally_closed_tm (tm_fix A B metric body) ->
      value v ->
      tm_app (tm_fix A B metric body) v -->
        open_fix_body body (tm_fix A B metric body) v
  | ST_IfZeroArg : forall t t' t0 t1,
      t --> t' -> locally_closed_tm t0 -> locally_closed_tm t1 ->
      tm_ifzero t t0 t1 --> tm_ifzero t' t0 t1
  | ST_IfZero : forall t0 t1,
      locally_closed_tm t0 -> locally_closed_tm t1 ->
      tm_ifzero (tm_int 0%Z) t0 t1 --> t0
  | ST_IfNonzero : forall (n : Z) t0 t1,
      n <> 0%Z -> locally_closed_tm t0 -> locally_closed_tm t1 ->
      tm_ifzero (tm_int n) t0 t1 --> t1
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
  | T_Fix : forall (L : list atom) Delta Gamma A B metric body,
      wf_ty Delta A -> wf_ty Delta B ->
      (forall x, ~ In x L ->
        has_type Delta (update Gamma x A)
          (open_tm metric (tm_fvar x)) Ty_Int) ->
      (forall f x, ~ In f L -> ~ In x (f :: L) ->
        has_type Delta (update (update Gamma x A) f (Ty_Arrow A B))
          (open_fix_body body (tm_fvar f) (tm_fvar x)) B) ->
      has_type Delta Gamma (tm_fix A B metric body) (Ty_Arrow A B)
  | T_IfZero : forall Delta Gamma t t0 t1 T,
      has_type Delta Gamma t Ty_Int ->
      has_type Delta Gamma t0 T -> has_type Delta Gamma t1 T ->
      has_type Delta Gamma (tm_ifzero t t0 t1) T.

Fixpoint max_atom (L : list atom) : atom :=
  match L with
  | [] => 0
  | x :: L' => Nat.max x (max_atom L')
  end.

Definition fresh (L : list atom) : atom := S (max_atom L).

End SystemFRefinementRecursion.

Module SystemFRefinementRecursionInfrastructure.
Import ListNotations SystemFRefinementRecursion.

Definition type_substitution := atom -> ty.

Definition term_substitution := atom -> tm.

Fixpoint instantiate_ty (theta : type_substitution) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => theta X
  | Ty_Arrow T1 T2 =>
      Ty_Arrow (instantiate_ty theta T1) (instantiate_ty theta T2)
  | Ty_All T1 => Ty_All (instantiate_ty theta T1)
  | Ty_Int => Ty_Int
  end.

Fixpoint instantiate
    (theta : type_substitution) (gamma : term_substitution) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => gamma x
  | tm_abs T t1 => tm_abs (instantiate_ty theta T) (instantiate theta gamma t1)
  | tm_app t1 t2 => tm_app (instantiate theta gamma t1) (instantiate theta gamma t2)
  | tm_tabs t1 => tm_tabs (instantiate theta gamma t1)
  | tm_tapp t1 T => tm_tapp (instantiate theta gamma t1) (instantiate_ty theta T)
  | tm_int n => tm_int n
  | tm_div t1 t2 => tm_div (instantiate theta gamma t1) (instantiate theta gamma t2)
  | tm_arith op t1 t2 => tm_arith op (instantiate theta gamma t1) (instantiate theta gamma t2)
  | tm_fix A B metric body => tm_fix (instantiate_ty theta A) (instantiate_ty theta B)
      (instantiate theta gamma metric) (instantiate theta gamma body)
  | tm_ifzero t t0 t1 => tm_ifzero (instantiate theta gamma t)
      (instantiate theta gamma t0) (instantiate theta gamma t1)
  end.

End SystemFRefinementRecursionInfrastructure.

From Stdlib Require Import Arith.PeanoNat Lists.List ZArith.BinInt.
Module SystemFRefinementRecursionLogic.
Import ListNotations SystemFRefinementRecursion.

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

End SystemFRefinementRecursionLogic.

From Stdlib Require Import Arith.PeanoNat Lists.List Lia ZArith.BinInt.
Module SystemFRefinementRecursionTyping.
Import ListNotations.
Import SystemFRefinementRecursion.
Export SystemFRefinementRecursionLogic.
Import SystemFRefinementRecursionInfrastructure.

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
Fixpoint instantiate_formula
    (theta : type_substitution) (gamma : term_substitution)
    (p : qualifier) : qualifier :=
  match p with
  | Pred_True => Pred_True
  | Pred_False => Pred_False
  | Pred_Eq t1 t2 => Pred_Eq (instantiate theta gamma t1) (instantiate theta gamma t2)
  | Pred_Lt t1 t2 => Pred_Lt (instantiate theta gamma t1) (instantiate theta gamma t2)
  | Pred_Le t1 t2 => Pred_Le (instantiate theta gamma t1) (instantiate theta gamma t2)
  | Pred_And p q => Pred_And (instantiate_formula theta gamma p) (instantiate_formula theta gamma q)
  | Pred_Or p q => Pred_Or (instantiate_formula theta gamma p) (instantiate_formula theta gamma q)
  | Pred_Not p => Pred_Not (instantiate_formula theta gamma p)
  end.

Definition context_formulas_hold
    (theta : type_substitution) (gamma : term_substitution)
    (RGamma : rcontext) : Prop :=
  forall x T p,
    lookup_rcontext x RGamma = Some (R_Refine T p) ->
    qualifier_holds
      (instantiate_formula theta gamma (open_qualifier_tm p (tm_fvar x))).

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
      entails Delta RGamma Pred_False q

  | Entails_Valid : forall Delta RGamma p q,
      (forall (theta : type_substitution) (gamma : term_substitution),
        (forall x, value (gamma x)) ->
        context_formulas_hold theta gamma RGamma ->
        qualifier_holds (instantiate_formula theta gamma p) ->
        qualifier_holds (instantiate_formula theta gamma q)) ->
      entails Delta RGamma p q.

Definition measured_input (A : ty) (p : qualifier) (metric : tm) : rty :=
  R_Refine A (Pred_And p (Pred_Ge metric (tm_int 0%Z))).

Definition smaller_input
    (A : ty) (p : qualifier) (metric current_metric : tm) : rty :=
  R_Refine A
    (Pred_And p
      (Pred_And (Pred_Ge metric (tm_int 0%Z))
                (Pred_Lt metric current_metric))).

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
      has_rtype Delta RGamma (tm_div t1 t2)
        (R_Refine Ty_Int (Pred_Eq (tm_bvar 0) (tm_div t1 t2)))
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

  | RT_Fix : forall (L : list atom) Delta RGamma A p metric body R2,
      wf_rty Delta RGamma (R_Func (measured_input A p metric) R2) ->
      (forall x, ~ In x L ->
        has_type Delta (update (erase_context RGamma) x A)
          (open_tm metric (tm_fvar x)) Ty_Int) ->
      (forall f x, ~ In f L -> ~ In x (f :: L) ->
        has_rtype Delta
          (update_rcontext
            (update_rcontext RGamma x (measured_input A p metric))
            f (R_Func
                (smaller_input A p metric (open_tm metric (tm_fvar x))) R2))
          (open_fix_body body (tm_fvar f) (tm_fvar x))
          (open_rty_tm R2 (tm_fvar x))) ->
      has_rtype Delta RGamma (tm_fix A (erase R2) metric body)
        (R_Func (measured_input A p metric) R2)

  | RT_IfZero : forall Delta RGamma x p t0 t1 R,
      lookup_rcontext x RGamma = Some (R_Refine Ty_Int p) ->
      has_rtype Delta
        (update_rcontext RGamma x
          (R_Refine Ty_Int (Pred_And p (Pred_Eq (tm_bvar 0) (tm_int 0%Z))))) t0 R ->
      has_rtype Delta
        (update_rcontext RGamma x
          (R_Refine Ty_Int (Pred_And p (Pred_Ne (tm_bvar 0) (tm_int 0%Z))))) t1 R ->
      has_rtype Delta RGamma (tm_ifzero (tm_fvar x) t0 t1) R

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

End SystemFRefinementRecursionTyping.

Module SystemFRefinementRecursionEvaluation.
Import ListNotations SystemFRefinementRecursion SystemFRefinementRecursionInfrastructure SystemFRefinementRecursionLogic SystemFRefinementRecursionTyping.

Inductive multi : tm -> tm -> Prop :=
  | multi_refl : forall t, multi t t
  | multi_step : forall t1 t2 t3,
      t1 --> t2 -> multi t2 t3 -> multi t1 t3.
Notation "t '-->*' u" := (multi t u) (at level 40).
Definition halts (t : tm) : Prop :=
  exists v, multi t v /\ value v.

End SystemFRefinementRecursionEvaluation.

From Stdlib Require Import Program.Wf.
From Equations Require Import Equations.
Module SystemFRefinementRecursionDenotations.
Import ListNotations SystemFRefinementRecursion SystemFRefinementRecursionInfrastructure SystemFRefinementRecursionLogic SystemFRefinementRecursionTyping SystemFRefinementRecursionEvaluation.

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
        halts (tm_app v arg) /\
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
        halts (tm_tapp v U) /\
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
  halts t /\
  forall v,
    multi t v ->
    value v ->
    denotes R v.

End SystemFRefinementRecursionDenotations.

Module SystemFRefinementRecursionTask.
Import ListNotations SystemFRefinementRecursion SystemFRefinementRecursionInfrastructure SystemFRefinementRecursionLogic SystemFRefinementRecursionTyping SystemFRefinementRecursionEvaluation SystemFRefinementRecursionDenotations.

Fixpoint instantiate_rty (theta : type_substitution)
    (gamma : term_substitution) (R : rty) : rty :=
  match R with
  | R_Refine T ps => R_Refine (instantiate_ty theta T)
      (instantiate_formula theta gamma ps)
  | R_Func R1 R2 => R_Func (instantiate_rty theta gamma R1)
      (instantiate_rty theta gamma R2)
  | R_Exists R1 R2 => R_Exists (instantiate_rty theta gamma R1)
      (instantiate_rty theta gamma R2)
  | R_Poly R1 => R_Poly (instantiate_rty theta gamma R1)
  end.

Definition context_denotes (theta : type_substitution)
    (gamma : term_substitution) (RGamma : rcontext) : Prop :=
  (forall x, value (gamma x)) /\
  (forall x R, lookup_rcontext x RGamma = Some R ->
    denotes (instantiate_rty theta gamma R) (gamma x)).

Lemma entails_sound : forall Delta RGamma p q,
  entails Delta RGamma p q ->
  forall theta gamma,
    (forall x, value (gamma x)) ->
    context_formulas_hold theta gamma RGamma ->
    qualifier_holds (instantiate_formula theta gamma p) ->
    qualifier_holds (instantiate_formula theta gamma q).
Proof.
  intros Delta RGamma p q Hentails.
  induction Hentails; intros theta gamma Hvalues Hcontext Hp;
    unfold qualifier_holds, predicate_holds in *; simpl in *;
    try tauto.
  - eapply IHHentails2; eauto.
  - split; [eapply IHHentails1 | eapply IHHentails2]; eauto.
  - destruct Hp as [Hp | Hq].
    + exact (IHHentails1 _ _ Hvalues Hcontext Hp).
    + exact (IHHentails2 _ _ Hvalues Hcontext Hq).
  - intro Hq. eapply IHHentails; eauto.
  - eapply Hcontext; eauto.
  - eapply H; eauto.
Qed.

Lemma values_do_not_step : forall v t,
  value v -> ~ step v t.
Proof.
  intros v t Hv Hs. inversion Hv; subst; inversion Hs.
Qed.

Lemma step_deterministic : forall t u other,
  step t u -> step t other -> u = other.
Proof.
  intros t u other Hstep.
  revert other.
  induction Hstep; intros other Hother; inversion Hother; subst;
    try match goal with
      | H : step (tm_abs _ _) _ |- _ => inversion H
      | H : step (tm_tabs _) _ |- _ => inversion H
      | H : step (tm_fix _ _ _ _) _ |- _ => inversion H
      | H : step (tm_int _) _ |- _ => inversion H
      | V : value ?w, S : step ?w ?z |- _ =>
          exfalso; exact (values_do_not_step w z V S)
      end;
    try (f_equal; eauto); try congruence.
Qed.

Lemma multi_deterministic_value : forall t v w,
  multi t v -> value v -> multi t w -> value w -> v = w.
Proof.
  intros t v w Htv Hv Htw Hw.
  revert w Htw Hw.
  induction Htv; intros w Htw Hw.
  - inversion Htw; subst; auto.
    match goal with
    | H : step t ?next |- _ =>
        exfalso; exact (values_do_not_step t next Hv H)
    end.
  - inversion Htw; subst.
    + exfalso. exact (values_do_not_step _ _ Hw H).
    + assert (t2 = t4) by (eapply step_deterministic; eauto).
      subst. eapply IHHtv; eauto.
Qed.

Lemma halts_reachable_safe : forall t u,
  halts t -> multi t u -> value u \/ exists v, step u v.
Proof.
  intros t u [v [Htv Hv]] Htu.
  revert v Htv Hv.
  induction Htu; intros v Htv Hv.
  - destruct Htv as [| ? next ? Hs Hrest].
    + now left.
    + right. eauto.
  - inversion Htv; subst.
    + exfalso. exact (values_do_not_step _ _ Hv H).
    + assert (t2 = t4) by (eapply step_deterministic; eauto).
      subst. eapply IHHtu; eauto.
Qed.

Lemma evals_denotes_reachable_safe : forall R t u,
  evals_denotes R t -> multi t u ->
  value u \/ exists v, step u v.
Proof.
  intros R t u [_ [Hhalts _]] Hmulti.
  eapply halts_reachable_safe; eauto.
Qed.

Lemma predicate_int_normal : forall n v,
  predicate_multistep (tm_int n) v -> v = tm_int n.
Proof.
  intros n v H.
  inversion H; subst; auto.
  inversion H0.
Qed.

Lemma core_int_canonical : forall v,
  value v -> has_type [] empty v Ty_Int ->
  exists n, v = tm_int n.
Proof.
  intros v Hv Hty.
  inversion Hv; subst; inversion Hty; subst; try discriminate;
    eauto.
Qed.

Lemma refine_nonzero_int : forall v,
  denotes (R_Refine Ty_Int (Pred_Ne (tm_bvar 0) (tm_int 0%Z))) v ->
  exists n, v = tm_int n /\ n <> 0%Z.
Proof.
  intros v Hden.
  simp denotes in Hden.
  destruct Hden as [Hv [Ht Hpred]].
  destruct (core_int_canonical _ Hv Ht) as [n ->].
  exists n. split; auto.
  unfold qualifier_holds, predicate_holds, Pred_Ne in Hpred.
  simpl in Hpred.
  intro Heq; subst n.
  apply Hpred. simpl.
  exists (tm_int 0%Z). repeat split; constructor.
Qed.

Lemma refine_int_canonical : forall ps v,
  denotes (R_Refine Ty_Int ps) v -> exists n, v = tm_int n.
Proof.
  intros ps v Hden.
  simp denotes in Hden.
  destruct Hden as [Hv [Ht _]].
  eapply core_int_canonical; eauto.
Qed.

Lemma value_closed : forall v, value v -> locally_closed_tm v.
Proof.
  intros v Hv. inversion Hv; subst; auto.
  constructor.
Qed.

Lemma open_tm_rec_lc : forall K k t,
  lc_tm_at K k t -> forall j u,
  k <= j -> open_tm_rec j u t = t.
Proof.
  intros K k t Hclosed.
  induction Hclosed; intros j u Hle; simpl;
    try solve [reflexivity | f_equal; eauto using le_n_S].
  destruct (Nat.eqb j i) eqn:Heq; auto.
  apply Nat.eqb_eq in Heq. lia.
Qed.

Lemma open_tm_closed : forall t u,
  locally_closed_tm t -> open_tm t u = t.
Proof.
  intros t u Hclosed.
  unfold open_tm. now apply open_tm_rec_lc with (K := 0) (k := 0).
Qed.

Lemma evals_denotes_value : forall R v,
  denotes R v -> evals_denotes R v.
Proof.
  intros R v Hden.
  split.
  - destruct R; simp denotes in Hden; apply value_closed; tauto.
  - split.
    + exists v. split; [constructor |].
      destruct R; simp denotes in Hden; tauto.
    + intros w Hmulti Hw.
      assert (Hv : value v) by
        (destruct R; simp denotes in Hden; tauto).
      assert (v = w) by
        (eapply multi_deterministic_value; eauto; constructor).
      subst. exact Hden.
Qed.

Lemma division_can_step : forall t1 t2,
  evals_denotes (R_Refine Ty_Int Pred_True) t1 ->
  evals_denotes
    (R_Refine Ty_Int (Pred_Ne (tm_bvar 0) (tm_int 0%Z))) t2 ->
  exists t, step (tm_div t1 t2) t.
Proof.
  intros t1 t2 Hleft Hright.
  destruct Hleft as [_ [Hhalt1 Hden1]].
  destruct Hright as [Hclosed2 [Hhalt2 Hden2]].
  destruct (halts_reachable_safe t1 t1 Hhalt1 (multi_refl t1)) as
    [Hval1 | [t1' Hstep1]].
  2: { exists (tm_div t1' t2). now apply ST_Div1. }
  destruct (refine_int_canonical _ _ (Hden1 _ (multi_refl _) Hval1))
    as [n ->].
  destruct (halts_reachable_safe t2 t2 Hhalt2 (multi_refl t2)) as
    [Hval2 | [t2' Hstep2]].
  2: { exists (tm_div (tm_int n) t2').
       now apply ST_Div2. }
  destruct (refine_nonzero_int _ (Hden2 _ (multi_refl _) Hval2))
    as [m [-> Hnonzero]].
  exists (tm_int (Z.div n m)). now apply ST_DivInt.
Qed.

Lemma multi_transitive : forall t u v,
  multi t u -> multi u v -> multi t v.
Proof.
  intros t u v Htu Huv. induction Htu; eauto using multi.
Qed.

Lemma multi_div_left : forall t1 u1 t2,
  multi t1 u1 -> locally_closed_tm t2 ->
  multi (tm_div t1 t2) (tm_div u1 t2).
Proof.
  intros t1 u1 t2 Hmulti Hclosed.
  induction Hmulti.
  - constructor.
  - eapply multi_step; eauto using step.
Qed.

Lemma multi_div_right : forall v1 t2 u2,
  value v1 -> multi t2 u2 ->
  multi (tm_div v1 t2) (tm_div v1 u2).
Proof.
  intros v1 t2 u2 Hval Hmulti.
  induction Hmulti.
  - constructor.
  - eapply multi_step; eauto using step.
Qed.

Lemma multi_predicate : forall t u,
  multi t u -> predicate_multistep t u.
Proof.
  intros t u Hmulti. induction Hmulti; eauto using predicate_multistep.
Qed.

Lemma division_evals_denotes : forall t1 t2,
  evals_denotes (R_Refine Ty_Int Pred_True) t1 ->
  evals_denotes
    (R_Refine Ty_Int (Pred_Ne (tm_bvar 0) (tm_int 0%Z))) t2 ->
  evals_denotes
    (R_Refine Ty_Int (Pred_Eq (tm_bvar 0) (tm_div t1 t2)))
    (tm_div t1 t2).
Proof.
  intros t1 t2 [Hclosed1 [Hhalt1 Hden1]]
    [Hclosed2 [Hhalt2 Hden2]].
  destruct Hhalt1 as [v1 [Hmulti1 Hval1]].
  destruct Hhalt2 as [v2 [Hmulti2 Hval2]].
  destruct (refine_int_canonical _ _ (Hden1 _ Hmulti1 Hval1))
    as [n ->].
  destruct (refine_nonzero_int _ (Hden2 _ Hmulti2 Hval2))
    as [m [-> Hnonzero]].
  assert (Heval : multi (tm_div t1 t2) (tm_int (Z.div n m))).
  { eapply multi_transitive with (u := tm_div (tm_int n) t2).
    - now apply multi_div_left.
    - eapply multi_transitive with
        (u := tm_div (tm_int n) (tm_int m)).
      + apply multi_div_right; [constructor | exact Hmulti2].
      + eapply multi_step; [now apply ST_DivInt | constructor]. }
  split.
  - now constructor.
  - split.
    + exists (tm_int (Z.div n m)). split; [exact Heval | constructor].
    + intros v Hmulti Hv.
      assert (tm_int (Z.div n m) = v) by
        (eapply multi_deterministic_value; eauto; constructor).
      subst v.
      simp denotes. repeat split; eauto using value, has_type.
      unfold qualifier_holds, predicate_holds. simpl.
      exists (tm_int (Z.div n m)). repeat split.
      * constructor.
      * change (predicate_multistep
          (tm_div (open_tm t1 (tm_int (Z.div n m)))
                  (open_tm t2 (tm_int (Z.div n m))))
          (tm_int (Z.div n m))).
        rewrite (open_tm_closed t1 _ Hclosed1).
        rewrite (open_tm_closed t2 _ Hclosed2).
        now apply multi_predicate.
      * constructor.
Qed.

Lemma multi_app_left : forall t1 u1 t2,
  multi t1 u1 -> locally_closed_tm t2 ->
  multi (tm_app t1 t2) (tm_app u1 t2).
Proof.
  intros t1 u1 t2 Hmulti Hclosed.
  induction Hmulti; eauto using multi, step.
Qed.

Lemma multi_app_right : forall v1 t2 u2,
  value v1 -> multi t2 u2 ->
  multi (tm_app v1 t2) (tm_app v1 u2).
Proof.
  intros v1 t2 u2 Hval Hmulti.
  induction Hmulti; eauto using multi, step.
Qed.

Lemma denotes_value : forall R v,
  denotes R v -> value v.
Proof.
  intros R v Hden. destruct R; simp denotes in Hden; tauto.
Qed.

Lemma denotes_erase : forall R v,
  denotes R v -> has_type [] empty v (erase R).
Proof.
  intros R v Hden. destruct R; simp denotes in Hden; tauto.
Qed.

Lemma erase_open_tm : forall R u,
  erase (open_rty_tm R u) = erase R.
Proof.
  intros R u. unfold open_rty_tm.
  generalize 0 as k.
  induction R; intros k; simpl; auto;
    rewrite ?IHR1, ?IHR2, ?IHR; reflexivity.
Qed.

Lemma application_evals_denotes : forall t1 t2 R1 R2,
  evals_denotes (R_Func R1 R2) t1 ->
  evals_denotes R1 t2 ->
  evals_denotes (R_Exists R1 R2) (tm_app t1 t2).
Proof.
  intros t1 t2 R1 R2 [Hclosed1 [[v1 [Hmulti1 Hv1]] Hden1]]
    [Hclosed2 [[v2 [Hmulti2 Hv2]] Hden2]].
  pose proof (Hden1 _ Hmulti1 Hv1) as Hfun.
  pose proof (Hden2 _ Hmulti2 Hv2) as Harg.
  simp denotes in Hfun.
  destruct Hfun as [_ [_ Happly]].
  specialize (Happly _ Harg).
  destruct Happly as [_ [Hhalts Hresult]].
  assert (Hprefix : multi (tm_app t1 t2) (tm_app v1 v2)).
  { eapply multi_transitive with (u := tm_app v1 t2).
    - now apply multi_app_left.
    - now apply multi_app_right. }
  destruct Hhalts as [result [Hcompute Hvalue]].
  assert (Hwhole : multi (tm_app t1 t2) result).
  { eapply multi_transitive; eauto. }
  split.
  - now constructor.
  - split.
    + exists result. auto.
    + intros v Hmulti Hv.
      assert (result = v) by
        (eapply multi_deterministic_value; eauto).
      subst v.
      simp denotes. repeat split.
      * assumption.
      * change (has_type [] empty result (erase R2)).
        rewrite <- (erase_open_tm R2 v2).
        exact (denotes_erase _ _ (Hresult _ Hcompute Hvalue)).
      * exists v2. split; [exact Harg |].
        exact (Hresult _ Hcompute Hvalue).
Qed.

Lemma multi_arith_left : forall op t1 u1 t2,
  multi t1 u1 -> locally_closed_tm t2 ->
  multi (tm_arith op t1 t2) (tm_arith op u1 t2).
Proof.
  intros op t1 u1 t2 Hmulti Hclosed.
  induction Hmulti; eauto using multi, step.
Qed.

Lemma multi_arith_right : forall op v1 t2 u2,
  value v1 -> multi t2 u2 ->
  multi (tm_arith op v1 t2) (tm_arith op v1 u2).
Proof.
  intros op v1 t2 u2 Hval Hmulti.
  induction Hmulti; eauto using multi, step.
Qed.

Lemma arithmetic_evals_denotes : forall op t1 t2,
  evals_denotes (R_Refine Ty_Int Pred_True) t1 ->
  evals_denotes (R_Refine Ty_Int Pred_True) t2 ->
  evals_denotes
    (R_Refine Ty_Int (Pred_Eq (tm_bvar 0) (tm_arith op t1 t2)))
    (tm_arith op t1 t2).
Proof.
  intros op t1 t2 [Hclosed1 [[v1 [Hmulti1 Hv1]] Hden1]]
    [Hclosed2 [[v2 [Hmulti2 Hv2]] Hden2]].
  destruct (refine_int_canonical _ _ (Hden1 _ Hmulti1 Hv1))
    as [n ->].
  destruct (refine_int_canonical _ _ (Hden2 _ Hmulti2 Hv2))
    as [m ->].
  set (result := eval_integer_operator op n m).
  assert (Heval : multi (tm_arith op t1 t2) (tm_int result)).
  { eapply multi_transitive with (u := tm_arith op (tm_int n) t2).
    - now apply multi_arith_left.
    - eapply multi_transitive with
        (u := tm_arith op (tm_int n) (tm_int m)).
      + apply multi_arith_right; [constructor | exact Hmulti2].
      + eapply multi_step; [apply ST_ArithInt | constructor]. }
  split.
  - now constructor.
  - split.
    + exists (tm_int result). split; [exact Heval | constructor].
    + intros v Hmulti Hv.
      assert (tm_int result = v) by
        (eapply multi_deterministic_value; eauto; constructor).
      subst v.
      simp denotes. repeat split; eauto using value, has_type.
      unfold qualifier_holds, predicate_holds. simpl.
      exists (tm_int result). repeat split.
      * constructor.
      * change (predicate_multistep
          (tm_arith op (open_tm t1 (tm_int result))
                       (open_tm t2 (tm_int result))) (tm_int result)).
        rewrite (open_tm_closed t1 _ Hclosed1).
        rewrite (open_tm_closed t2 _ Hclosed2).
        now apply multi_predicate.
      * constructor.
Qed.

Lemma integer_evals_denotes : forall n,
  evals_denotes
    (R_Refine Ty_Int (Pred_Eq (tm_bvar 0) (tm_int n)))
    (tm_int n).
Proof.
  intro n.
  apply evals_denotes_value.
  simp denotes. repeat split; eauto using value, has_type.
  unfold qualifier_holds, predicate_holds. simpl.
  exists (tm_int n). repeat split; constructor.
Qed.

Lemma refinement_value_evals_denotes : forall v T ps,
  value v -> has_type [] empty v T ->
  qualifier_holds (open_qualifier_tm ps v) ->
  evals_denotes (R_Refine T ps) v.
Proof.
  intros v T ps Hv Htype Hqualifier.
  apply evals_denotes_value.
  simp denotes. auto.
Qed.

Lemma multi_tapp_term : forall t u U,
  multi t u -> locally_closed_ty U ->
  multi (tm_tapp t U) (tm_tapp u U).
Proof.
  intros t u U Hmulti Hclosed.
  induction Hmulti; eauto using multi, step.
Qed.

Lemma type_application_evals_denotes : forall t U R,
  evals_denotes (R_Poly R) t ->
  wf_ty [] U -> locally_closed_ty U ->
  evals_denotes (open_rty_ty R U) (tm_tapp t U).
Proof.
  intros t U R [Hclosed [[v [Hmulti Hv]] Hden]] Hwf HclosedU.
  pose proof (Hden _ Hmulti Hv) as Hpoly.
  simp denotes in Hpoly.
  destruct Hpoly as [_ [_ Happly]].
  specialize (Happly U Hwf).
  destruct Happly as [_ [[result [Hcompute Hvalue]] Hresult]].
  assert (Hwhole : multi (tm_tapp t U) result).
  { eapply multi_transitive with (u := tm_tapp v U).
    - now apply multi_tapp_term.
    - exact Hcompute. }
  split.
  - now constructor.
  - split.
    + exists result. auto.
    + intros w Hmulti' Hw.
      assert (result = w) by
        (eapply multi_deterministic_value; eauto).
      subst w. now apply Hresult.
Qed.

Theorem never_stuck : forall (t t' : tm) (R : rty),
  has_rtype [] empty_rcontext t R ->
  multi t t' ->
  value t' \/ exists t'' : tm, t' --> t''.
Proof.
  intros t t' R Htyping Hmulti.
  eapply evals_denotes_reachable_safe with (R := R);
    [| exact Hmulti].
Qed.

End SystemFRefinementRecursionTask.
