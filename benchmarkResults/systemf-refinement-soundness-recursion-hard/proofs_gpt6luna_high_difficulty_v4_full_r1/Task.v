From Stdlib Require Import Program.Equality.
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

End SystemFRefinementRecursionEvaluation.

Module SystemFRefinementRecursionTask.
Import ListNotations SystemFRefinementRecursion SystemFRefinementRecursionInfrastructure SystemFRefinementRecursionLogic SystemFRefinementRecursionTyping SystemFRefinementRecursionEvaluation.

Scheme rtype_subtype_mutind := Induction for has_rtype Sort Prop
with subtype_rtype_mutind := Induction for subtype Sort Prop.

Lemma lc_open_tm_inv : forall t K k x,
  lc_tm_at K k (open_tm_rec k (tm_fvar x) t) ->
  lc_tm_at K (S k) t.
Proof.
  induction t; intros K k x H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + inversion H; subst. apply lc_tm_bvar. apply Nat.eqb_eq in E; lia.
    + inversion H; subst. apply lc_tm_bvar. apply Nat.eqb_neq in E. lia.
  - inversion H; constructor.
  - inversion H; subst. constructor.
    + assumption.
    + eapply IHt. exact H5.
  - inversion H; subst. constructor; [eapply IHt1|eapply IHt2]; eassumption.
  - inversion H; subst. constructor. eapply IHt. eassumption.
  - inversion H; subst. constructor; [eapply IHt|]; eassumption.
  - inversion H; constructor.
  - inversion H; subst. constructor; [eapply IHt1|eapply IHt2]; eassumption.
  - inversion H; subst. constructor; [eapply IHt1|eapply IHt2]; eassumption.
  - inversion H; subst. constructor; eauto using IHt1, IHt2.
  - inversion H; subst. constructor; [eapply IHt1|eapply IHt2|eapply IHt3]; eassumption.
Qed.

Lemma lc_open_ty_inv : forall T K k X,
  k < K ->
  lc_ty_at K (open_ty_rec k (Ty_FVar X) T) ->
  lc_ty_at K T.
Proof.
  induction T; intros K k X Hk H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + inversion H; subst. econstructor. apply Nat.eqb_eq in E; lia.
    + inversion H; subst. econstructor. apply Nat.eqb_neq in E; lia.
  - inversion H; constructor.
  - inversion H; subst. constructor; [eapply IHT1|eapply IHT2]; eassumption.
  - inversion H; subst. constructor. eapply IHT with (K := S K) (k := S k) (X := X); [lia|assumption].
  - inversion H; constructor.
Qed.

Lemma max_atom_ge : forall x L, In x L -> x <= max_atom L.
Proof.
  intros x L; induction L as [|a L IH]; simpl; intros H; [contradiction|].
  destruct H as [->|H].
  - apply Nat.le_max_l.
  - eapply Nat.le_trans; [eapply IH; eassumption|apply Nat.le_max_r].
Qed.

Lemma fresh_notin : forall L, ~ In (fresh L) L.
Proof.
  intros L H. unfold fresh in H. pose proof (max_atom_ge _ _ H). lia.
Qed.

Lemma wf_ty_lc : forall Delta T,
  wf_ty Delta T -> lc_ty_at (length Delta) T.
Proof.
  intros Delta T Hwf. induction Hwf as [Delta X Hin|Delta T1 T2 H1 IH1 H2 IH2|L Delta T Hbody IHbody|Delta].
  - constructor.
  - constructor; assumption.
  - constructor. specialize (IHbody (fresh L) (fresh_notin L)).
    eapply lc_open_ty_inv with (k := 0); [simpl; lia|exact IHbody].
  - constructor.
Qed.

Lemma erase_open_rty_tm : forall R k u,
  erase (open_rty_tm_rec k u R) = erase R.
Proof. induction R; intros; simpl; congruence. Qed.

Lemma erase_open_rty_ty : forall R k U,
  erase (open_rty_ty_rec k U R) = open_ty_rec k U (erase R).
Proof. induction R; intros; simpl; f_equal; eauto. Qed.

Lemma wf_rty_erasure_lc : forall Delta RGamma R,
  wf_rty Delta RGamma R -> lc_ty_at (length Delta) (erase R).
Proof.
  intros Delta RGamma R Hwf. induction Hwf as
    [L Delta RGamma T ps Hty Hpred
    |L Delta RGamma R1 R2 H1 IH1 Hbody IHbody
    |L Delta RGamma R1 R2 H1 IH1 Hbody IHbody
    |L Delta RGamma R Hbody IHbody].
  - simpl. eapply wf_ty_lc. exact Hty.
  - simpl. constructor; [exact IH1|].
    specialize (IHbody (fresh L) (fresh_notin L)).
    unfold open_rty_tm in IHbody. rewrite erase_open_rty_tm in IHbody. exact IHbody.
  - simpl. specialize (IHbody (fresh L) (fresh_notin L)).
    unfold open_rty_tm in IHbody. rewrite erase_open_rty_tm in IHbody. exact IHbody.
  - simpl. constructor.
    specialize (IHbody (fresh L) (fresh_notin L)).
    unfold open_rty_ty in IHbody. rewrite erase_open_rty_ty in IHbody.
    eapply lc_open_ty_inv with (k := 0); [simpl; lia|exact IHbody].
Qed.

Lemma wf_rty_erasure_wf : forall Delta RGamma R,
  wf_rty Delta RGamma R -> wf_ty Delta (erase R).
Proof.
  intros Delta RGamma R Hwf. induction Hwf as
    [L Delta RGamma T ps Hty Hpred
    |L Delta RGamma R1 R2 H1 IH1 Hbody IHbody
    |L Delta RGamma R1 R2 H1 IH1 Hbody IHbody
    |L Delta RGamma R Hbody IHbody].
  - simpl. exact Hty.
  - simpl. constructor; [exact IH1|].
    specialize (IHbody (fresh L) (fresh_notin L)).
    unfold open_rty_tm in IHbody. rewrite erase_open_rty_tm in IHbody. exact IHbody.
  - simpl. specialize (IHbody (fresh L) (fresh_notin L)).
    unfold open_rty_tm in IHbody. rewrite erase_open_rty_tm in IHbody. exact IHbody.
  - simpl. apply WF_All with (L := L). intros X HX.
    specialize (IHbody X HX). unfold open_rty_ty in IHbody.
    rewrite erase_open_rty_ty in IHbody. exact IHbody.
Qed.

Fixpoint close_ty_rec (K : nat) (X : atom) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar Y => if Nat.eqb X Y then Ty_BVar K else Ty_FVar Y
  | Ty_Arrow T1 T2 => Ty_Arrow (close_ty_rec K X T1) (close_ty_rec K X T2)
  | Ty_All T1 => Ty_All (close_ty_rec (S K) X T1)
  | Ty_Int => Ty_Int
  end.

Lemma close_open_ty_rec : forall T K X,
  ~ In X (fv_ty T) -> close_ty_rec K X (open_ty_rec K (Ty_FVar X) T) = T.
Proof.
  induction T; intros K X Hfresh; simpl in *.
  - destruct (Nat.eqb K n) eqn:E; simpl.
    + apply Nat.eqb_eq in E. subst. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - destruct (Nat.eqb X a) eqn:E.
    + exfalso. apply Hfresh. simpl. apply Nat.eqb_eq in E; subst; simpl; auto.
    + reflexivity.
  - simpl in Hfresh.
    assert (H1 : ~ In X (fv_ty T1)).
    { intro Hin. apply Hfresh. apply in_or_app; left; exact Hin. }
    assert (H2 : ~ In X (fv_ty T2)).
    { intro Hin. apply Hfresh. apply in_or_app; right; exact Hin. }
    simpl. rewrite (IHT1 K X H1), (IHT2 K X H2). reflexivity.
  - simpl. rewrite IHT with (K := S K) (X := X); [reflexivity|exact Hfresh].
  - reflexivity.
Qed.

Lemma open_ty_rec_injective_fresh : forall T U K X,
  ~ In X (fv_ty T) -> ~ In X (fv_ty U) ->
  open_ty_rec K (Ty_FVar X) T = open_ty_rec K (Ty_FVar X) U -> T = U.
Proof.
  intros T U K X Ht Hu Heq.
  pose proof (f_equal (close_ty_rec K X) Heq) as H.
  rewrite close_open_ty_rec in H by exact Ht.
  rewrite close_open_ty_rec in H by exact Hu.
  exact H.
Qed.

Lemma fresh_notin_left_app : forall A B, ~ In (fresh (A ++ B)) A.
Proof.
  intros A B H. apply fresh_notin with (L := A ++ B). apply in_or_app; left; exact H.
Qed.
Lemma fresh_notin_right_app : forall A B, ~ In (fresh (A ++ B)) B.
Proof.
  intros A B H. apply fresh_notin with (L := A ++ B). apply in_or_app; right; exact H.
Qed.

Lemma subtype_erases_equal : forall Delta RGamma R S,
  subtype Delta RGamma R S -> erase R = erase S.
Proof.
  intros Delta RGamma R S Hsub. induction Hsub; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + symmetry. assumption.
    + specialize (H0 (fresh L) (fresh_notin L)).
      unfold open_rty_tm in H0. repeat rewrite erase_open_rty_tm in H0. exact H0.
  - unfold open_rty_tm in IHHsub. rewrite erase_open_rty_tm in IHHsub. exact IHHsub.
  - specialize (H2 (fresh L) (fresh_notin L)).
    unfold open_rty_tm in H2. rewrite erase_open_rty_tm in H2. exact H2.
  - f_equal.
    pose (X := fresh (L ++ fv_ty (erase R) ++ fv_ty (erase S))).
    assert (HX : ~ In X L).
    { unfold X. intro Hin. apply fresh_notin with (L := L ++ fv_ty (erase R) ++ fv_ty (erase S)).
      apply in_or_app; left; exact Hin. }
    specialize (H0 X HX).
    unfold open_rty_ty in H0. repeat rewrite erase_open_rty_ty in H0.
    eapply open_ty_rec_injective_fresh with (K := 0) (X := X).
    + unfold X. intro Hin. apply fresh_notin with (L := L ++ fv_ty (erase R) ++ fv_ty (erase S)).
      apply in_or_app; right. apply in_or_app; left; exact Hin.
    + unfold X. intro Hin. apply fresh_notin with (L := L ++ fv_ty (erase R) ++ fv_ty (erase S)).
      apply in_or_app; right. apply in_or_app; right; exact Hin.
    + exact H0.
  - etransitivity; eassumption.
Qed.

Lemma lc_open_tm_ty_inv : forall t K k j X,
  j < K ->
  lc_tm_at K k (open_tm_ty_rec j (Ty_FVar X) t) ->
  lc_tm_at K k t.
Proof.
  induction t; intros K k j X Hj H; simpl in H.
  - inversion H; subst; constructor; assumption.
  - inversion H; subst; constructor; assumption.
  - inversion H; subst. constructor.
    + eapply lc_open_ty_inv; eassumption.
    + eapply IHt with (j := j) (X := X); eassumption.
  - inversion H; subst. constructor; [eapply IHt1|eapply IHt2]; eassumption.
  - inversion H; subst. constructor. eapply IHt with (j := S j) (X := X); [lia|eassumption].
  - inversion H; subst. constructor; [eapply IHt|]; try eassumption.
    eapply lc_open_ty_inv; eassumption.
  - inversion H; constructor.
  - inversion H; subst. constructor; [eapply IHt1|eapply IHt2]; eassumption.
  - inversion H; subst. constructor; [eapply IHt1|eapply IHt2]; eassumption.
  - inversion H; subst. constructor.
    + eapply lc_open_ty_inv; eassumption.
    + eapply lc_open_ty_inv; eassumption.
    + eapply IHt1 with (j := j) (X := X); eassumption.
    + eapply IHt2 with (j := j) (X := X); eassumption.
  - inversion H; subst. constructor; [eapply IHt1|eapply IHt2|eapply IHt3]; eassumption.
Qed.

Lemma has_type_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> lc_tm_at (length Delta) 0 t.
Proof.
  intros Delta Gamma t T Hty. induction Hty as
    [Delta Gamma x T Hlookup Hwf
    |L Delta Gamma T1 t2 T2 Hwf Hbody IHbody
    |Delta Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
    |L Delta Gamma t T Hbody IHbody
    |Delta Gamma t T U H1 IH1 Hwf
    |Delta Gamma n
    |Delta Gamma t1 t2 H1 IH1 H2 IH2
    |Delta Gamma op t1 t2 H1 IH1 H2 IH2
    |L Delta Gamma A B metric body HA HB Hmetric IHmetric Hbody IHbody
    |Delta Gamma t t0 t1 T Ht IHt H0 IH0 H1 IH1].
  - constructor.
  - constructor.
    + eapply wf_ty_lc; eassumption.
    + specialize (IHbody (fresh L) (fresh_notin L)).
      eapply lc_open_tm_inv. exact IHbody.
  - constructor; assumption.
  - constructor. specialize (IHbody (fresh L) (fresh_notin L)).
    eapply lc_open_tm_ty_inv with (j := 0); [simpl; lia|exact IHbody].
  - constructor; [exact IH1|]. eapply wf_ty_lc; eassumption.
  - constructor.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; try (eapply wf_ty_lc; eassumption).
    + specialize (IHmetric (fresh L) (fresh_notin L)).
      eapply lc_open_tm_inv. exact IHmetric.
    + specialize (IHbody (fresh L) (fresh (fresh L :: L))
        (fresh_notin L) (fresh_notin (fresh L :: L))).
      eapply lc_open_tm_inv. eapply lc_open_tm_inv. exact IHbody.
  - constructor; assumption.
Qed.

Lemma lc_ty_weaken : forall K T,
  lc_ty_at K T -> lc_ty_at (S K) T.
Proof.
  intros K T H; induction H; eauto using lc_ty_at.
Qed.

Lemma lc_tm_type_weaken : forall K k t,
  lc_tm_at K k t -> lc_tm_at (S K) k t.
Proof.
  intros K k t H; induction H; eauto using lc_tm_at, lc_ty_weaken.
Qed.

Lemma lc_tm_type_weaken_n : forall n K k t,
  lc_tm_at K k t -> lc_tm_at (n + K) k t.
Proof.
  induction n; intros K k t H; simpl.
  - exact H.
  - apply lc_tm_type_weaken. apply IHn. exact H.
Qed.

Lemma value_lc_any_type_context : forall v K,
  value v -> lc_tm_at K 0 v.
Proof.
  intros v K Hv. induction Hv.
  - unfold locally_closed_tm in H.
    replace K with (K + 0) by lia.
    eapply lc_tm_type_weaken_n; exact H.
  - unfold locally_closed_tm in H.
    replace K with (K + 0) by lia.
    eapply lc_tm_type_weaken_n; exact H.
  - constructor.
  - unfold locally_closed_tm in H.
    replace K with (K + 0) by lia.
    eapply lc_tm_type_weaken_n; exact H.
Qed.

Lemma has_rtype_lc : forall Delta RGamma t R,
  has_rtype Delta RGamma t R -> lc_tm_at (length Delta) 0 t.
Proof.
  intros Delta RGamma t R Hty. induction Hty as
    [Delta RGamma x R Hlookup Hwf
    |L Delta RGamma R1 body R2 Hwf Hbody IHbody
    |Delta RGamma t1 t2 R1 R2 H1 IH1 H2 IH2
    |L Delta RGamma body R Hbody IHbody
    |Delta RGamma t R U H1 IH1 Hwf
    |Delta RGamma n
    |Delta RGamma t1 t2 H1 IH1 H2 IH2
    |Delta RGamma op t1 t2 H1 IH1 H2 IH2
    |Delta RGamma v T ps Htype Hv Hwf Hclosed Hholds
    |L Delta RGamma A p metric body R2 Hwf Hmetric Hbody IHbody
    |Delta RGamma x p t0 t1 R Hlookup H0 IH0 H1 IH1
    |Delta RGamma t R S Ht IHt Hwf Hsub].
  - constructor.
  - apply lc_tm_abs.
    + eapply wf_rty_erasure_lc; eassumption.
    + specialize (IHbody (fresh L) (fresh_notin L)).
      eapply lc_open_tm_inv. exact IHbody.
  - constructor; assumption.
  - constructor. specialize (IHbody (fresh L) (fresh_notin L)).
    eapply lc_open_tm_ty_inv with (j := 0); [simpl; lia|exact IHbody].
  - constructor; [exact IH1|]. eapply wf_ty_lc; eassumption.
  - constructor.
  - constructor; assumption.
  - constructor; assumption.
  - eapply value_lc_any_type_context; eassumption.
  - pose proof (wf_rty_erasure_lc _ _ _ Hwf) as Hlc.
    inversion Hlc; subst.
    apply lc_tm_fix; eauto using wf_ty_lc.
    + specialize (Hmetric (fresh L) (fresh_notin L)).
      eapply has_type_lc in Hmetric. eapply lc_open_tm_inv. exact Hmetric.
    + specialize (IHbody (fresh L) (fresh (fresh L :: L))
        (fresh_notin L) (fresh_notin (fresh L :: L))).
      eapply lc_open_tm_inv. eapply lc_open_tm_inv. exact IHbody.
  - constructor; [constructor|assumption|assumption].
  - exact IHt.
Qed.

Lemma lookup_erase_context : forall x RGamma R,
  lookup_rcontext x RGamma = Some R ->
  lookup_context x (erase_context RGamma) = Some (erase R).
Proof.
  intros x RGamma; induction RGamma as [|[y S] RGamma IH]; intros R H; simpl in *; [discriminate|].
  destruct (Nat.eqb x y) eqn:E.
  - inversion H; subst. reflexivity.
  - eapply IH. exact H.
Qed.

Definition core_context_equiv (G1 G2 : context) : Prop :=
  forall x, lookup_context x G1 = lookup_context x G2.

Lemma core_context_equiv_update : forall G1 G2 x T,
  core_context_equiv G1 G2 ->
  core_context_equiv (update G1 x T) (update G2 x T).
Proof.
  intros G1 G2 x T Heq y. simpl. destruct (Nat.eqb y x); auto.
Qed.

Lemma core_context_equiv_same_update : forall G x T,
  lookup_context x G = Some T ->
  core_context_equiv (update G x T) G.
Proof.
  intros G x T H y. simpl. destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E; subst. symmetry; exact H.
  - reflexivity.
Qed.

Lemma has_type_context_equiv : forall Delta G1 G2 t T,
  core_context_equiv G1 G2 -> has_type Delta G1 t T -> has_type Delta G2 t T.
Proof.
  intros Delta G1 G2 t T Heq Hty. revert G2 Heq.
  induction Hty as
    [Delta Gamma x T Hlookup Hwf
    |L Delta Gamma T1 t2 T2 Hwf Hbody IHbody
    |Delta Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
    |L Delta Gamma t T Hbody IHbody
    |Delta Gamma t T U H1 IH1 Hwf
    |Delta Gamma n
    |Delta Gamma t1 t2 H1 IH1 H2 IH2
    |Delta Gamma op t1 t2 H1 IH1 H2 IH2
    |L Delta Gamma A B metric body HA HB Hmetric IHmetric Hbody IHbody
    |Delta Gamma t t0 t1 T Ht IHt H0 IH0 H1 IH1];
    intros G2 Heq.
  - econstructor; [rewrite <- (Heq x); exact Hlookup|exact Hwf].
  - eapply T_Abs with (L := L); [exact Hwf|]. intros x Hx.
    specialize (IHbody x Hx (update G2 x T1)). eapply IHbody.
    apply core_context_equiv_update. exact Heq.
  - eapply T_App; [eapply IH1|eapply IH2]; exact Heq.
  - eapply T_TAbs with (L := L). intros X HX.
    specialize (IHbody X HX G2). eapply IHbody. exact Heq.
  - eapply T_TApp; [eapply IH1; exact Heq|exact Hwf].
  - constructor.
  - eapply T_Div; [eapply IH1|eapply IH2]; exact Heq.
  - eapply T_Arith; [eapply IH1|eapply IH2]; exact Heq.
  - eapply T_Fix with (L := L); try assumption.
    + intros x Hx. specialize (IHmetric x Hx (update G2 x A)).
      eapply IHmetric. apply core_context_equiv_update. exact Heq.
    + intros f x Hf Hx. specialize (IHbody f x Hf Hx (update (update G2 x A) f (Ty_Arrow A B))).
      eapply IHbody. apply core_context_equiv_update. apply core_context_equiv_update. exact Heq.
  - eapply T_IfZero; [eapply IHt|eapply IH0|eapply IH1]; exact Heq.

Qed.

Lemma has_rtype_erasure_typing : forall Delta RGamma t R,
  has_rtype Delta RGamma t R ->
  has_type Delta (erase_context RGamma) t (erase R).
Proof.
  intros Delta RGamma t R Hty. induction Hty as
    [Delta RGamma x R Hlookup Hwf
    |L Delta RGamma R1 body R2 Hwf Hbody IHbody
    |Delta RGamma t1 t2 R1 R2 H1 IH1 H2 IH2
    |L Delta RGamma body R Hbody IHbody
    |Delta RGamma t R U H1 IH1 Hwf
    |Delta RGamma n
    |Delta RGamma t1 t2 H1 IH1 H2 IH2
    |Delta RGamma op t1 t2 H1 IH1 H2 IH2
    |Delta RGamma v T ps Htype Hv Hwf Hclosed Hholds
    |L Delta RGamma A p metric body R2 Hwf Hmetric Hbody IHbody
    |Delta RGamma x p t0 t1 R Hlookup H0 IH0 H1 IH1
    |Delta RGamma t R S Ht IHt Hwf Hsub].
  - econstructor; [eapply lookup_erase_context; exact Hlookup|].
    eapply wf_rty_erasure_wf; exact Hwf.
  - eapply T_Abs with (L := L).
    + eapply wf_rty_erasure_wf; exact Hwf.
    + intros x Hx. specialize (IHbody x Hx).
      unfold open_rty_tm in IHbody. rewrite erase_open_rty_tm in IHbody.
      exact IHbody.
  - simpl. eapply T_App; eassumption.
  - eapply T_TAbs with (L := L). intros X HX.
    specialize (IHbody X HX). unfold open_rty_ty in IHbody.
    rewrite erase_open_rty_ty in IHbody. exact IHbody.
  - unfold open_rty_ty. rewrite erase_open_rty_ty.
    eapply T_TApp; [exact IH1|exact Hwf].
  - constructor.
  - eapply T_Div; eassumption.
  - eapply T_Arith; eassumption.
  - exact Htype.
  - pose proof (wf_rty_erasure_wf _ _ _ Hwf) as Harrow.
    inversion Harrow; subst.
    eapply T_Fix with (L := L) (A := A) (B := erase R2)
      (metric := metric) (body := body).
    + assumption.
    + assumption.
    + exact Hmetric.
    + intros f x Hf Hx.
      specialize (IHbody f x Hf Hx).
      unfold open_rty_tm in IHbody. rewrite erase_open_rty_tm in IHbody.
      exact IHbody.
  - assert (Hx : lookup_context x (erase_context RGamma) = Some Ty_Int).
    { eapply lookup_erase_context in Hlookup. simpl in Hlookup. exact Hlookup. }
    eapply T_IfZero with (T := erase R).
    + econstructor; [exact Hx|constructor].
    + change (has_type Delta (update (erase_context RGamma) x Ty_Int) t0 (erase R)) in IH0.
      eapply has_type_context_equiv; [apply core_context_equiv_same_update; exact Hx|exact IH0].
    + change (has_type Delta (update (erase_context RGamma) x Ty_Int) t1 (erase R)) in IH1.
      eapply has_type_context_equiv; [apply core_context_equiv_same_update; exact Hx|exact IH1].
  - pose proof (subtype_erases_equal _ _ _ _ Hsub) as E.
    rewrite <- E. exact IHt.
Qed.

Lemma canonical_int : forall v,
  has_type [] [] v Ty_Int -> value v -> exists n, v = tm_int n.
Proof.
  intros v Hty Hv. dependent induction Hty; inversion Hv; subst; eauto; try discriminate.
Qed.

Lemma canonical_arrow : forall v A B,
  has_type [] [] v (Ty_Arrow A B) -> value v ->
  (exists T body, v = tm_abs T body) \/
  (exists metric body, v = tm_fix A B metric body).
Proof.
  intros v A B Hty Hv. dependent induction Hty; inversion Hv; subst; eauto; try discriminate.
Qed.

Lemma canonical_all : forall v T,
  has_type [] [] v (Ty_All T) -> value v -> exists body, v = tm_tabs body.
Proof.
  intros v T Hty Hv. dependent induction Hty; inversion Hv; subst; eauto; try discriminate.
Qed.

Lemma arith_progress : forall op t1 t2,
  has_rtype [] [] t1 (R_Refine Ty_Int Pred_True) ->
  has_rtype [] [] t2 (R_Refine Ty_Int Pred_True) ->
  (value t1 \/ exists u, t1 --> u) ->
  (value t2 \/ exists u, t2 --> u) ->
  value (tm_arith op t1 t2) \/ exists u, tm_arith op t1 t2 --> u.
Proof.
  intros op t1 t2 Hty1 Hty2 P1 P2.
  destruct P1 as [V1|[t1' S1]].
  - destruct P2 as [V2|[t2' S2]].
    + pose proof (has_rtype_erasure_typing _ _ _ _ Hty1) as C1.
      pose proof (has_rtype_erasure_typing _ _ _ _ Hty2) as C2.
      destruct (canonical_int t1 C1 V1) as [n ->].
      destruct (canonical_int t2 C2 V2) as [m ->].
      right. exists (tm_int (eval_integer_operator op n m)). constructor.
    + right. exists (tm_arith op t1 t2'). apply ST_Arith2; assumption.
  - right. exists (tm_arith op t1' t2). apply ST_Arith1.
    + exact S1.
    + unfold locally_closed_tm. exact (has_rtype_lc [] [] _ _ Hty2).
Qed.

Lemma div_progress_with_nonzero : forall t1 t2,
  has_rtype [] [] t1 (R_Refine Ty_Int Pred_True) ->
  has_rtype [] [] t2 (R_Refine Ty_Int (Pred_Ne (tm_bvar 0) (tm_int 0%Z))) ->
  (value t1 \/ exists u, t1 --> u) ->
  (value t2 \/ exists u, t2 --> u) ->
  (forall m, t2 = tm_int m -> m <> 0%Z) ->
  value (tm_div t1 t2) \/ exists u, tm_div t1 t2 --> u.
Proof.
  intros t1 t2 Hty1 Hty2 P1 P2 Hnz.
  destruct P1 as [V1|[t1' S1]].
  - destruct P2 as [V2|[t2' S2]].
    + pose proof (has_rtype_erasure_typing _ _ _ _ Hty1) as C1.
      pose proof (has_rtype_erasure_typing _ _ _ _ Hty2) as C2.
      destruct (canonical_int t1 C1 V1) as [n ->].
      destruct (canonical_int t2 C2 V2) as [m ->].
      right. exists (tm_int (Z.div n m)). apply ST_DivInt. eapply Hnz; reflexivity.
    + right. exists (tm_div t1 t2'). apply ST_Div2; assumption.
  - right. exists (tm_div t1' t2). apply ST_Div1.
    + exact S1.
    + unfold locally_closed_tm. exact (has_rtype_lc [] [] _ _ Hty2).
Qed.

Lemma entails_sound : forall Delta RGamma p q,
  entails Delta RGamma p q ->
  forall theta gamma,
    (forall x, value (gamma x)) ->
    context_formulas_hold theta gamma RGamma ->
    qualifier_holds (instantiate_formula theta gamma p) ->
    qualifier_holds (instantiate_formula theta gamma q).
Proof.
  intros Delta RGamma p q Hent. induction Hent;
    intros theta gamma Hval Hctx Hp; simpl in *.
  - exact Hp.
  - exact I.
  - eapply IHHent2; [exact Hval|exact Hctx|].
    eapply IHHent1; eassumption.
  - destruct Hp as [Hp _]. exact Hp.
  - destruct Hp as [_ Hq]. exact Hq.
  - split.
    + eapply IHHent1; eassumption.
    + eapply IHHent2; eassumption.
  - left. exact Hp.
  - right. exact Hp.
  - destruct Hp as [Hp|Hq].
    + eapply IHHent1; eassumption.
    + eapply IHHent2; eassumption.
  - intro Hq. pose proof (IHHent theta gamma Hval Hctx (conj Hp Hq)). contradiction.
  - destruct Hp as [Hp Hnot]. contradiction.
  - eapply Hctx; eassumption.
  - contradiction.
  - eapply H; eassumption.

Qed.

Lemma multi_int_value : forall n v,
  predicate_multistep (tm_int n) v -> value v -> v = tm_int n.
Proof.
  intros n v Hm. dependent induction Hm; intro Hv.
  - reflexivity.
  - inversion H; subst; try discriminate.
Qed.

Lemma ne_literal_nonzero : forall n,
  qualifier_holds (open_qualifier_tm
    (Pred_Ne (tm_bvar 0) (tm_int 0%Z)) (tm_int n)) -> n <> 0%Z.
Proof.
  intros n H Hzero. subst n. simpl in H.
  assert (Hex : exists v, predicate_multistep (tm_int 0%Z) v /\
       predicate_multistep (tm_int 0%Z) v /\ value v).
  { exists (tm_int 0%Z). repeat split; try constructor. }
  exact (H Hex).
Qed.

Lemma eq_literal_holds : forall n,
  qualifier_holds (Pred_Eq (tm_int n) (tm_int n)).
Proof.
  intros n. simpl. exists (tm_int n). repeat split; try constructor.
Qed.

Lemma arith_result_holds : forall op n m,
  qualifier_holds
    (Pred_Eq (tm_int (eval_integer_operator op n m))
      (tm_arith op (tm_int n) (tm_int m))).
Proof.
  intros op n m. simpl. exists (tm_int (eval_integer_operator op n m)).
  split; [constructor|]. split.
  - eapply PMS_Step. apply ST_ArithInt. constructor.
  - constructor.
Qed.

Lemma div_result_holds : forall n m, m <> 0%Z ->
  qualifier_holds
    (Pred_Eq (tm_int (n / m)) (tm_div (tm_int n) (tm_int m))).
Proof.
  intros n m Hnz. simpl. exists (tm_int (n / m)).
  split; [constructor|]. split.
  - eapply PMS_Step. apply ST_DivInt. exact Hnz. constructor.
  - constructor.
Qed.

Lemma arith_result_closed : forall op n m,
  predicate_closed
    (Pred_Eq (tm_int (eval_integer_operator op n m))
      (tm_arith op (tm_int n) (tm_int m))).
Proof. intros; simpl; repeat split; try constructor; simpl; auto; apply lc_tm_int. Qed.

Lemma div_result_closed : forall n m,
  predicate_closed (Pred_Eq (tm_int (n / m)) (tm_div (tm_int n) (tm_int m))).
Proof. intros; simpl; repeat split; try constructor; simpl; auto; apply lc_tm_int. Qed.

Lemma rtype_arith_eval : forall op n m,
  has_rtype [] [] (tm_int (eval_integer_operator op n m))
    (R_Refine Ty_Int
      (Pred_Eq (tm_bvar 0) (tm_arith op (tm_int n) (tm_int m)))).
Proof.
  intros op n m. eapply RT_RefineValue with (T := Ty_Int).
  - constructor.
  - constructor.
  - eapply RWF_Refine with (L := []).
    + constructor.
    + intros x Hx. unfold open_qualifier_tm, open_qualifier_tm_rec, open_pred_tm_rec.
      simpl. unfold qualifier_wf. apply PWF_Eq; eauto 12 using has_type.
  - simpl. apply arith_result_closed.
  - simpl. apply arith_result_holds.
Qed.

Lemma eq_literal_closed : forall n,
  predicate_closed (Pred_Eq (tm_int n) (tm_int n)).
Proof. intros; simpl; repeat split; try constructor; reflexivity. Qed.

Lemma instantiate_open_tm_rec_value : forall theta gamma x w k t,
  gamma x = instantiate theta gamma w ->
  instantiate theta gamma (open_tm_rec k (tm_fvar x) t) =
  instantiate theta gamma (open_tm_rec k w t).
Proof.
  intros theta gamma x w k t Hx. revert k.
  induction t; intros k; simpl.
  - destruct (Nat.eqb k n); simpl; [rewrite Hx|]; reflexivity.
  - reflexivity.
  - f_equal. apply IHt.
  - f_equal; [apply IHt1|apply IHt2].
  - f_equal. apply IHt.
  - f_equal. apply IHt.
  - reflexivity.
  - f_equal; [apply IHt1|apply IHt2].
  - f_equal; [apply IHt1|apply IHt2].
  - f_equal; [apply IHt1|apply IHt2].
  - f_equal; [apply IHt1|apply IHt2|apply IHt3].
Qed.

Lemma instantiate_open_qualifier_rec_value : forall theta gamma x w k p,
  gamma x = instantiate theta gamma w ->
  instantiate_formula theta gamma
    (open_qualifier_tm_rec k (tm_fvar x) p) =
  instantiate_formula theta gamma
    (open_qualifier_tm_rec k w p).
Proof.
  intros theta gamma x w k p Hx. revert k.
  induction p; intros k; simpl; try reflexivity.
  - f_equal; eapply instantiate_open_tm_rec_value; exact Hx.
  - f_equal; eapply instantiate_open_tm_rec_value; exact Hx.
  - f_equal; eapply instantiate_open_tm_rec_value; exact Hx.
  - rewrite IHp1, IHp2; reflexivity.
  - rewrite IHp1, IHp2; reflexivity.
  - rewrite IHp; reflexivity.
Qed.

Lemma instantiate_open_qualifier_value : forall theta gamma x w p,
  gamma x = instantiate theta gamma w ->
  instantiate_formula theta gamma (open_qualifier_tm p (tm_fvar x)) =
  instantiate_formula theta gamma (open_qualifier_tm p w).
Proof. intros; apply instantiate_open_qualifier_rec_value; assumption. Qed.

Lemma instantiate_ty_identity : forall T,
  instantiate_ty (fun X : atom => Ty_FVar X) T = T.
Proof. induction T; simpl; try rewrite ?IHT1, ?IHT2, ?IHT; reflexivity. Qed.

Lemma instantiate_closed_tm_identity : forall t gamma,
  fv_tm t = [] ->
  instantiate (fun X : atom => Ty_FVar X) gamma t = t.
Proof.
  induction t; intros gamma Hfv; simpl in *; simpl; try reflexivity.
  - discriminate.
  - rewrite instantiate_ty_identity, IHt; [reflexivity|exact Hfv].
  - apply app_eq_nil in Hfv as [H1 H2]. rewrite IHt1, IHt2; auto.
  - rewrite IHt; auto.
  - rewrite IHt, instantiate_ty_identity; auto.
  - apply app_eq_nil in Hfv as [H1 H2]. rewrite IHt1, IHt2; auto.
  - apply app_eq_nil in Hfv as [H1 H2]. rewrite IHt1, IHt2; auto.
  - apply app_eq_nil in Hfv as [H1 H2].
    rewrite instantiate_ty_identity, instantiate_ty_identity, IHt1, IHt2; auto.
  - apply app_eq_nil in Hfv as [H1 H23].
    apply app_eq_nil in H23 as [H2 H3].
    rewrite IHt1, IHt2, IHt3; auto.
Qed.

Lemma instantiate_closed_qualifier_identity : forall p gamma,
  predicate_closed p ->
  instantiate_formula (fun X : atom => Ty_FVar X) gamma p = p.
Proof.
  induction p; intros gamma Hclosed; simpl in *; try reflexivity.
  - destruct Hclosed as [_ [H1 [_ [_ [H2 _]]]]].
    rewrite (instantiate_closed_tm_identity t gamma H1),
      (instantiate_closed_tm_identity t0 gamma H2). reflexivity.
  - destruct Hclosed as [_ [H1 [_ [_ [H2 _]]]]].
    rewrite (instantiate_closed_tm_identity t gamma H1),
      (instantiate_closed_tm_identity t0 gamma H2). reflexivity.
  - destruct Hclosed as [_ [H1 [_ [_ [H2 _]]]]].
    rewrite (instantiate_closed_tm_identity t gamma H1),
      (instantiate_closed_tm_identity t0 gamma H2). reflexivity.
  - destruct Hclosed as [H1 H2]. rewrite IHp1, IHp2; auto.
  - destruct Hclosed as [H1 H2]. rewrite IHp1, IHp2; auto.
  - rewrite IHp; auto.
Qed.

Fixpoint instantiate_rty (theta : type_substitution) (gamma : term_substitution)
    (R : rty) : rty :=
  match R with
  | R_Refine T p => R_Refine (instantiate_ty theta T)
      (instantiate_formula theta gamma p)
  | R_Func R1 R2 => R_Func (instantiate_rty theta gamma R1)
      (instantiate_rty theta gamma R2)
  | R_Exists R1 R2 => R_Exists (instantiate_rty theta gamma R1)
      (instantiate_rty theta gamma R2)
  | R_Poly R1 => R_Poly (instantiate_rty theta gamma R1)
  end.

Fixpoint fv_qualifier (p : qualifier) : list atom :=
  match p with
  | Pred_True | Pred_False => []
  | Pred_Eq t1 t2 | Pred_Lt t1 t2 | Pred_Le t1 t2 => fv_tm t1 ++ fv_tm t2
  | Pred_And p q | Pred_Or p q => fv_qualifier p ++ fv_qualifier q
  | Pred_Not p => fv_qualifier p
  end.

Fixpoint fv_rty_tm (R : rty) : list atom :=
  match R with
  | R_Refine _ p => fv_qualifier p
  | R_Func R1 R2 | R_Exists R1 R2 => fv_rty_tm R1 ++ fv_rty_tm R2
  | R_Poly R => fv_rty_tm R
  end.

Fixpoint fv_rcontext_tm (RGamma : rcontext) : list atom :=
  match RGamma with
  | [] => []
  | (_, R) :: RGamma' => fv_rty_tm R ++ fv_rcontext_tm RGamma'
  end.

Lemma lookup_rcontext_fv_in : forall RGamma x R y,
  lookup_rcontext x RGamma = Some R ->
  In y (fv_rty_tm R) -> In y (fv_rcontext_tm RGamma).
Proof.
  induction RGamma as [|[z Q] RGamma IH]; intros x R y Hlookup Hfv; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x z) eqn:E.
    + inversion Hlookup; subst. apply in_or_app. left; exact Hfv.
    + apply in_or_app. right. eapply IH; eassumption.
Qed.

Lemma instantiate_tm_ext : forall t theta gamma1 gamma2,
  (forall x, In x (fv_tm t) -> gamma1 x = gamma2 x) ->
  instantiate theta gamma1 t = instantiate theta gamma2 t.
Proof.
  induction t; intros theta gamma1 gamma2 Hext; simpl; try reflexivity.
  - simpl in Hext. specialize (Hext a (or_introl eq_refl)). now rewrite Hext.
  - f_equal. apply IHt. intros x Hx. apply Hext. exact Hx.
  - f_equal.
    + apply IHt1. intros x Hx. apply Hext. apply in_or_app. left; exact Hx.
    + apply IHt2. intros x Hx. apply Hext. apply in_or_app. right; exact Hx.
  - f_equal. apply IHt. intros x Hx. apply Hext. exact Hx.
  - f_equal. apply IHt. intros x Hx. apply Hext. exact Hx.
  - f_equal.
    + apply IHt1. intros x Hx. apply Hext. apply in_or_app. left; exact Hx.
    + apply IHt2. intros x Hx. apply Hext. apply in_or_app. right; exact Hx.
  - f_equal.
    + apply IHt1. intros x Hx. apply Hext. apply in_or_app. left; exact Hx.
    + apply IHt2. intros x Hx. apply Hext. apply in_or_app. right; exact Hx.
  - f_equal.
    + apply IHt1. intros x Hx. apply Hext. apply in_or_app. left; exact Hx.
    + apply IHt2. intros x Hx. apply Hext. apply in_or_app. right; exact Hx.
  - f_equal.
    + apply IHt1. intros x Hx. apply Hext. apply in_or_app. left; exact Hx.
    + apply IHt2. intros x Hx. apply Hext. apply in_or_app. right; apply in_or_app; left; exact Hx.
    + apply IHt3. intros x Hx. apply Hext. repeat (apply in_or_app; right); exact Hx.
Qed.

Lemma instantiate_qualifier_ext : forall p theta gamma1 gamma2,
  (forall x, In x (fv_qualifier p) -> gamma1 x = gamma2 x) ->
  instantiate_formula theta gamma1 p = instantiate_formula theta gamma2 p.
Proof.
  induction p; intros theta gamma1 gamma2 Hext; simpl; try reflexivity.
  - f_equal; apply instantiate_tm_ext; intros x Hx; apply Hext;
      apply in_or_app; [left|right]; exact Hx.
  - f_equal; apply instantiate_tm_ext; intros x Hx; apply Hext;
      apply in_or_app; [left|right]; exact Hx.
  - f_equal; apply instantiate_tm_ext; intros x Hx; apply Hext;
      apply in_or_app; [left|right]; exact Hx.
  - f_equal.
    + apply IHp1. intros x Hx. apply Hext. apply in_or_app; left; exact Hx.
    + apply IHp2. intros x Hx. apply Hext. apply in_or_app; right; exact Hx.
  - f_equal.
    + apply IHp1. intros x Hx. apply Hext. apply in_or_app; left; exact Hx.
    + apply IHp2. intros x Hx. apply Hext. apply in_or_app; right; exact Hx.
  - f_equal. apply IHp. exact Hext.
Qed.

Lemma instantiate_rty_ext : forall R theta gamma1 gamma2,
  (forall x, In x (fv_rty_tm R) -> gamma1 x = gamma2 x) ->
  instantiate_rty theta gamma1 R = instantiate_rty theta gamma2 R.
Proof.
  induction R; intros theta gamma1 gamma2 Hext; simpl.
  - f_equal. apply instantiate_qualifier_ext. exact Hext.
  - f_equal.
    + apply IHR1. intros x Hx. apply Hext. apply in_or_app; left; exact Hx.
    + apply IHR2. intros x Hx. apply Hext. apply in_or_app; right; exact Hx.
  - f_equal.
    + apply IHR1. intros x Hx. apply Hext. apply in_or_app; left; exact Hx.
    + apply IHR2. intros x Hx. apply Hext. apply in_or_app; right; exact Hx.
  - f_equal. apply IHR. exact Hext.
Qed.

Lemma instantiate_rty_open_value : forall theta gamma x w k R,
  gamma x = instantiate theta gamma w ->
  instantiate_rty theta gamma (open_rty_tm_rec k (tm_fvar x) R) =
  instantiate_rty theta gamma (open_rty_tm_rec k w R).
Proof.
  intros theta gamma x w k R Hx. revert k.
  induction R; intros k; simpl.
  - f_equal. apply instantiate_open_qualifier_rec_value. exact Hx.
  - f_equal; [apply IHR1|apply IHR2]; exact Hx.
  - f_equal; [apply IHR1|apply IHR2]; exact Hx.
  - f_equal. apply IHR.
Qed.

Lemma instantiate_rty_open_value_top : forall theta gamma x w R,
  gamma x = instantiate theta gamma w ->
  instantiate_rty theta gamma (open_rty_tm R (tm_fvar x)) =
  instantiate_rty theta gamma (open_rty_tm R w).
Proof. intros; apply instantiate_rty_open_value; assumption. Qed.

Lemma open_rec_lc_identity : forall K k t,
  lc_tm_at K k t -> forall j u, k <= j -> open_tm_rec j u t = t.
Proof.
  intros K k t Hlc. induction Hlc; intros j u Hj; simpl.
  - assert (E : (j =? i) = false) by (apply Nat.eqb_neq; lia).
    rewrite E. reflexivity.
  - reflexivity.
  - f_equal. eapply IHHlc; lia.
  - f_equal; [eapply IHHlc1|eapply IHHlc2]; lia.
  - f_equal. eapply IHHlc; lia.
  - f_equal. eapply IHHlc; lia.
  - reflexivity.
  - f_equal; [eapply IHHlc1|eapply IHHlc2]; lia.
  - f_equal; [eapply IHHlc1|eapply IHHlc2]; lia.
  - f_equal; [eapply IHHlc1|eapply IHHlc2]; lia.
  - f_equal; [eapply IHHlc1|eapply IHHlc2|eapply IHHlc3]; lia.
Qed.

Lemma instantiate_open_tm_rec_commute : forall theta gamma x k t,
  (forall y, locally_closed_tm (gamma y)) ->
  instantiate theta gamma (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k (instantiate theta gamma (tm_fvar x))
    (instantiate theta gamma t).
Proof.
  intros theta gamma x k t Hvals. revert k.
  induction t; intros k; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. apply open_rec_lc_identity with (K := 0) (k := 0); [apply Hvals|lia].
  - f_equal. apply IHt.
  - f_equal; [apply IHt1|apply IHt2].
  - f_equal. apply IHt.
  - f_equal. apply IHt.
  - reflexivity.
  - f_equal; [apply IHt1|apply IHt2].
  - f_equal; [apply IHt1|apply IHt2].
  - f_equal; [apply IHt1|apply IHt2].
  - f_equal; [apply IHt1|apply IHt2|apply IHt3].
Qed.

Lemma instantiate_open_tm_rec_general : forall theta gamma u k t,
  (forall y, locally_closed_tm (gamma y)) ->
  instantiate theta gamma (open_tm_rec k u t) =
  open_tm_rec k (instantiate theta gamma u) (instantiate theta gamma t).
Proof.
  intros theta gamma u k t Hvals. revert k.
  induction t; intros k; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. apply open_rec_lc_identity with (K := 0) (k := 0); [apply Hvals|lia].
  - f_equal. apply IHt.
  - f_equal; [apply IHt1|apply IHt2].
  - f_equal. apply IHt.
  - f_equal. apply IHt.
  - reflexivity.
  - f_equal; [apply IHt1|apply IHt2].
  - f_equal; [apply IHt1|apply IHt2].
  - f_equal; [apply IHt1|apply IHt2].
  - f_equal; [apply IHt1|apply IHt2|apply IHt3].
Qed.

Lemma instantiate_open_qualifier_rec_general : forall theta gamma u k p,
  (forall y, locally_closed_tm (gamma y)) ->
  instantiate_formula theta gamma (open_qualifier_tm_rec k u p) =
  open_qualifier_tm_rec k (instantiate theta gamma u)
    (instantiate_formula theta gamma p).
Proof.
  intros theta gamma u k p Hvals. induction p; simpl;
    try reflexivity; try (unfold open_qualifier_tm_rec, open_pred_tm_rec; simpl).
  - f_equal; f_equal; apply instantiate_open_tm_rec_general; exact Hvals.
  - f_equal; f_equal; apply instantiate_open_tm_rec_general; exact Hvals.
  - f_equal; f_equal; apply instantiate_open_tm_rec_general; exact Hvals.
  - f_equal; assumption.
  - f_equal; assumption.
  - f_equal; assumption.
Qed.

Lemma instantiate_open_qualifier_general : forall theta gamma u p,
  (forall y, locally_closed_tm (gamma y)) ->
  instantiate_formula theta gamma (open_qualifier_tm p u) =
  open_qualifier_tm (instantiate_formula theta gamma p)
    (instantiate theta gamma u).
Proof. intros; unfold open_qualifier_tm; apply instantiate_open_qualifier_rec_general; assumption. Qed.

Inductive rty_sem : rty -> tm -> Prop :=
  | Sem_Refine : forall T p v,
      qualifier_holds (open_qualifier_tm p v) ->
      rty_sem (R_Refine T p) v
  | Sem_Func : forall R1 R2 v,
      rty_sem (R_Func R1 R2) v
  | Sem_Poly : forall R v,
      rty_sem (R_Poly R) v
  | Sem_Exists : forall R1 R2 v w,
      value w ->
      rty_sem R1 w ->
      rty_sem (open_rty_tm R2 w) v ->
      rty_sem (R_Exists R1 R2) v.

Definition sem_context (theta : type_substitution) (gamma : term_substitution)
    (RGamma : rcontext) : Prop :=
  forall x R, lookup_rcontext x RGamma = Some R ->
    value (instantiate theta gamma (tm_fvar x)) /\
    rty_sem (instantiate_rty theta gamma R)
      (instantiate theta gamma (tm_fvar x)).

Definition update_gamma (gamma : term_substitution) (x : atom) (v : tm) : term_substitution :=
  fun y => if Nat.eqb y x then v else gamma y.

Lemma sem_context_update : forall theta gamma RGamma x R1 w,
  sem_context theta gamma RGamma ->
  ~ In x (fv_rty_tm R1) ->
  (forall y R, lookup_rcontext y RGamma = Some R ->
     ~ In x (fv_rty_tm R)) ->
  (forall y, locally_closed_tm (gamma y)) ->
  value w ->
  rty_sem (instantiate_rty theta gamma R1) w ->
  sem_context theta (update_gamma gamma x w) (update_rcontext RGamma x R1).
Proof.
  intros theta gamma RGamma x R1 w Hctx Hfresh1 Hfresh Hlc Hv Hsat y R Hlookup.
  unfold update_rcontext, lookup_rcontext in Hlookup. simpl in Hlookup.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst y. inversion Hlookup; subst R.
    split.
    + change (value (update_gamma gamma x w x)).
      unfold update_gamma. rewrite Nat.eqb_refl. exact Hv.
    + cbn [instantiate].
      change (rty_sem (instantiate_rty theta (update_gamma gamma x w) R1)
        (if Nat.eqb x x then w else gamma x)).
      rewrite Nat.eqb_refl.
      rewrite (instantiate_rty_ext R1 theta (update_gamma gamma x w) gamma).
      * exact Hsat.
      * intros z Hz. unfold update_gamma. destruct (Nat.eqb z x) eqn:Ez.
        -- apply Nat.eqb_eq in Ez; subst z. exfalso. apply Hfresh1. exact Hz.
        -- reflexivity.
  - apply Nat.eqb_neq in E.
    assert (Ebool : Nat.eqb y x = false) by (apply Nat.eqb_neq; exact E).
    pose proof (Hctx y R) as Hold. assert (Hlook : lookup_rcontext y RGamma = Some R).
    { exact Hlookup. }
    specialize (Hold Hlook) as [Hvold Hsatold]. split.
    + assert (Hterm : instantiate theta (update_gamma gamma x w) (tm_fvar y) =
          instantiate theta gamma (tm_fvar y)).
      { unfold instantiate. simpl. unfold update_gamma. rewrite Ebool. reflexivity. }
      rewrite Hterm. exact Hvold.
    + assert (Hterm : instantiate theta (update_gamma gamma x w) (tm_fvar y) =
          instantiate theta gamma (tm_fvar y)).
      { unfold instantiate. simpl. unfold update_gamma. rewrite Ebool. reflexivity. }
      rewrite Hterm.
      rewrite (instantiate_rty_ext R theta (update_gamma gamma x w) gamma).
      * exact Hsatold.
      * intros z Hz. unfold update_gamma. destruct (Nat.eqb z x) eqn:Ez.
        -- apply Nat.eqb_eq in Ez; subst z. exfalso.
           apply (Hfresh y R Hlook). exact Hz.
        -- reflexivity.
Qed.

Lemma lc_tm_bvar_weaken : forall K k t,
  lc_tm_at K k t -> lc_tm_at K (S k) t.
Proof.
  intros K k t Hlc. induction Hlc; eauto using lc_tm_at.
Qed.

Lemma lc_tm_bvar_weaken_n : forall n K k t,
  lc_tm_at K k t -> lc_tm_at K (n + k) t.
Proof.
  induction n; intros K k t H; simpl.
  - exact H.
  - apply lc_tm_bvar_weaken. apply IHn. exact H.
Qed.

Lemma instantiate_lc_tm : forall K k t gamma,
  lc_tm_at K k t ->
  (forall x, value (gamma x)) ->
  lc_tm_at K k (instantiate (fun X : atom => Ty_FVar X) gamma t).
Proof.
  intros K k t gamma Hlc. revert gamma.
  induction Hlc; intros gamma Hvals; simpl.
  - constructor. exact H.
  - pose proof (value_lc_any_type_context (gamma x) K (Hvals x)) as Hx.
    replace k with (k + 0) by lia.
    eapply lc_tm_bvar_weaken_n. exact Hx.
  - rewrite instantiate_ty_identity. constructor; eauto.
  - constructor; eauto.
  - constructor. eapply IHHlc; eauto.
  - rewrite instantiate_ty_identity. constructor; eauto.
  - constructor.
  - constructor; eauto.
  - constructor; eauto.
  - rewrite !instantiate_ty_identity. constructor; eauto.
  - constructor; eauto.
Qed.

Lemma instantiate_value : forall v gamma,
  (forall x, value (gamma x)) -> value v ->
  value (instantiate (fun X : atom => Ty_FVar X) gamma v).
Proof.
  intros v gamma Hvals Hv. inversion Hv; subst; simpl.
  - apply v_abs. eapply instantiate_lc_tm with (t := tm_abs T t) (K := 0) (k := 0).
    + unfold locally_closed_tm in H. exact H.
    + exact Hvals.
  - apply v_tabs. eapply instantiate_lc_tm with (t := tm_tabs t) (K := 0) (k := 0).
    + unfold locally_closed_tm in H. exact H.
    + exact Hvals.
  - constructor.
  - apply v_fix. eapply instantiate_lc_tm with (t := tm_fix A B metric body) (K := 0) (k := 0).
    + unfold locally_closed_tm in H. exact H.
    + exact Hvals.
Qed.

Definition value_valuation (gamma : term_substitution) : Prop :=
  forall x, value (gamma x).

Lemma update_gamma_values : forall gamma x v,
  value_valuation gamma -> value v -> value_valuation (update_gamma gamma x v).
Proof. intros gamma x v Hgamma Hv y. unfold update_gamma. destruct (Nat.eqb y x); eauto. Qed.

Lemma gamma_values_lc : forall gamma,
  value_valuation gamma -> forall x, locally_closed_tm (gamma x).
Proof.
  intros gamma Hgamma x. eapply value_lc_any_type_context. apply Hgamma.
Qed.

Lemma instantiate_open_qualifier_rec_commute : forall theta gamma x k p,
  (forall y, locally_closed_tm (gamma y)) ->
  instantiate_formula theta gamma
    (open_qualifier_tm_rec k (tm_fvar x) p) =
  open_qualifier_tm_rec k (instantiate theta gamma (tm_fvar x))
    (instantiate_formula theta gamma p).
Proof.
  intros theta gamma x k p Hvals. induction p;
    simpl; try reflexivity; try (unfold open_qualifier_tm, open_qualifier_tm_rec, open_pred_tm_rec; simpl).
  - f_equal; f_equal; apply instantiate_open_tm_rec_commute; exact Hvals.
  - f_equal; f_equal; apply instantiate_open_tm_rec_commute; exact Hvals.
  - f_equal; f_equal; apply instantiate_open_tm_rec_commute; exact Hvals.
  - f_equal; assumption.
  - f_equal; assumption.
  - f_equal; assumption.
Qed.

Lemma instantiate_open_qualifier_commute : forall theta gamma x p,
  (forall y, locally_closed_tm (gamma y)) ->
  instantiate_formula theta gamma (open_qualifier_tm p (tm_fvar x)) =
  open_qualifier_tm (instantiate_formula theta gamma p)
    (instantiate theta gamma (tm_fvar x)).
Proof.
  intros. unfold open_qualifier_tm. apply instantiate_open_qualifier_rec_commute; assumption.
Qed.

Lemma instantiate_rty_open_commute : forall theta gamma x k R,
  (forall y, locally_closed_tm (gamma y)) ->
  instantiate_rty theta gamma (open_rty_tm_rec k (tm_fvar x) R) =
  open_rty_tm_rec k (instantiate theta gamma (tm_fvar x))
    (instantiate_rty theta gamma R).
Proof.
  intros theta gamma x k R Hlc. revert k.
  induction R; intros k; simpl.
  - f_equal. apply instantiate_open_qualifier_rec_commute. exact Hlc.
  - f_equal; [apply IHR1|apply IHR2].
  - f_equal; [apply IHR1|apply IHR2].
  - f_equal. apply IHR.
Qed.

Lemma instantiate_rty_open_general : forall theta gamma u k R,
  (forall y, locally_closed_tm (gamma y)) ->
  instantiate_rty theta gamma (open_rty_tm_rec k u R) =
  open_rty_tm_rec k (instantiate theta gamma u)
    (instantiate_rty theta gamma R).
Proof.
  intros theta gamma u k R Hlc. revert k.
  induction R; intros k; simpl.
  - f_equal. apply instantiate_open_qualifier_rec_general. exact Hlc.
  - f_equal; [apply IHR1|apply IHR2]; exact Hlc.
  - f_equal; [apply IHR1|apply IHR2]; exact Hlc.
  - f_equal. apply IHR.
Qed.

Lemma sem_context_entails_context_formulas : forall theta gamma RGamma,
  sem_context theta gamma RGamma ->
  (forall x, locally_closed_tm (gamma x)) ->
  context_formulas_hold theta gamma RGamma.
Proof.
  intros theta gamma RGamma Hsem Hlc x T p Hlookup.
  specialize (Hsem x (R_Refine T p) Hlookup) as [_ Hsat].
  inversion Hsat; subst; simpl in *.
  rewrite instantiate_open_qualifier_commute; auto.
Qed.


Lemma entail_literal_ne : forall m x p,
  entails [] (update_rcontext [] x (R_Refine Ty_Int Pred_True))
    (open_qualifier_tm p (tm_fvar x))
    (open_qualifier_tm (Pred_Ne (tm_bvar 0) (tm_int 0%Z)) (tm_fvar x)) ->
  predicate_closed (open_qualifier_tm p (tm_int m)) ->
  qualifier_holds (open_qualifier_tm p (tm_int m)) -> m <> 0%Z.
Proof.
  intros m x p Hent Hclosed Hp.
  set (theta := fun X : atom => Ty_FVar X).
  set (gamma := fun y : atom => if Nat.eqb y x then tm_int m else tm_int 0%Z).
  assert (Hvals : forall y, value (gamma y)).
  { intro y. unfold gamma. destruct (Nat.eqb y x); constructor. }
  assert (Hctx : context_formulas_hold theta gamma
      (update_rcontext [] x (R_Refine Ty_Int Pred_True))).
  { intros y T q Hlookup. simpl in Hlookup.
    unfold lookup_rcontext, update_rcontext in Hlookup. simpl in Hlookup.
    destruct (Nat.eqb y x) eqn:E; inversion Hlookup; subst.
    simpl. exact I. }
  pose proof (entails_sound _ _ _ _ Hent theta gamma Hvals Hctx) as Hsound.
  unfold theta in Hsound.
  assert (Hgam : gamma x = instantiate theta gamma (tm_int m)).
  { unfold gamma. rewrite Nat.eqb_refl. reflexivity. }
  unfold theta in Hgam. simpl in Hgam.
  rewrite (instantiate_open_qualifier_value
    (fun X : atom => Ty_FVar X) gamma x (tm_int m) p Hgam) in Hsound.
  rewrite (instantiate_closed_qualifier_identity
    (open_qualifier_tm p (tm_int m)) gamma Hclosed) in Hsound.
  specialize (Hsound Hp).
  rewrite (instantiate_open_qualifier_value (fun X : atom => Ty_FVar X) gamma x (tm_int m)
    (Pred_Ne (tm_bvar 0) (tm_int 0%Z)) Hgam) in Hsound.
  eapply ne_literal_nonzero. exact Hsound.
Qed.

Definition rtype_semantic_property Delta RGamma t R
    (H : has_rtype Delta RGamma t R) : Prop :=
  forall gamma, value_valuation gamma ->
    sem_context (fun X : atom => Ty_FVar X) gamma RGamma ->
    value t ->
    rty_sem (instantiate_rty (fun X : atom => Ty_FVar X) gamma R)
      (instantiate (fun X : atom => Ty_FVar X) gamma t).

Definition subtype_semantic_property Delta RGamma R S
    (H : subtype Delta RGamma R S) : Prop :=
  forall gamma, value_valuation gamma ->
    sem_context (fun X : atom => Ty_FVar X) gamma RGamma ->
    forall v, value v ->
      rty_sem (instantiate_rty (fun X : atom => Ty_FVar X) gamma R) v ->
      rty_sem (instantiate_rty (fun X : atom => Ty_FVar X) gamma S) v.

Definition subtype_semantic_relation (Delta : ty_context) (RGamma : rcontext)
    (R S : rty) : Prop :=
  forall gamma, value_valuation gamma ->
    sem_context (fun X : atom => Ty_FVar X) gamma RGamma ->
    forall v, value v ->
      rty_sem (instantiate_rty (fun X : atom => Ty_FVar X) gamma R) v ->
      rty_sem (instantiate_rty (fun X : atom => Ty_FVar X) gamma S) v.

Lemma rtype_semantics_fundamental : forall Delta RGamma t R (H : has_rtype Delta RGamma t R),
      rtype_semantic_property Delta RGamma t R H.
Proof.
  apply (rtype_subtype_mutind rtype_semantic_property subtype_semantic_property);
      unfold rtype_semantic_property, subtype_semantic_property, value_valuation;
      simpl; intros; try solve [inversion H4].
    all: try solve [eauto 12 using rty_sem, value].
    all: try solve [inversion H1].
    all: try solve [inversion H3].
    all: try solve [inversion H2].
    1: { apply Sem_Refine. simpl. apply eq_literal_holds. }
    1: { apply Sem_Refine.
      rewrite <- (instantiate_open_qualifier_general
        (fun X : atom => Ty_FVar X) gamma v ps).
      - rewrite (instantiate_closed_qualifier_identity
          (open_qualifier_tm ps v) gamma); [assumption|assumption].
      - intros y. apply value_lc_any_type_context. apply H.
    }
    1: { eapply H0.
      - exact H1.
      - exact H2.
      - eapply instantiate_value; eauto.
      - eapply H; eauto.
    }
    1: { apply Sem_Refine.
      inversion H2; subst; simpl in *.
      set (x := fresh (L ++ fv_qualifier ps ++ fv_qualifier qs ++ fv_rcontext_tm RGamma)).
      assert (Hxall : ~ In x (L ++ fv_qualifier ps ++ fv_qualifier qs ++ fv_rcontext_tm RGamma)).
      { unfold x. apply fresh_notin. }
      assert (HxL : ~ In x L).
      { intro Hin. apply Hxall. apply in_or_app. left; exact Hin. }
      assert (Hxps : ~ In x (fv_qualifier ps)).
      { intro Hin. apply Hxall. apply in_or_app; right. apply in_or_app; left; exact Hin. }
      assert (Hxqs : ~ In x (fv_qualifier qs)).
      { intro Hin. apply Hxall. apply in_or_app; right. apply in_or_app; right. apply in_or_app; left; exact Hin. }
      assert (Hxctx : forall y R, lookup_rcontext y RGamma = Some R -> ~ In x (fv_rty_tm R)).
      { intros y R Hlook Hin. apply Hxall. apply in_or_app; right.
        apply in_or_app; right. apply in_or_app; right.
        eapply lookup_rcontext_fv_in; eassumption. }
      set (gamma' := update_gamma gamma x v).
      assert (Hvals' : value_valuation gamma').
      { unfold gamma'. eapply update_gamma_values; eauto. }
      assert (Hsem' : sem_context (fun X : atom => Ty_FVar X) gamma'
          (update_rcontext RGamma x (R_Refine T Pred_True))).
      { unfold gamma'. eapply sem_context_update.
        - exact H0.
        - simpl. intuition.
        - exact Hxctx.
        - apply gamma_values_lc. exact H.
        - exact H1.
        - apply Sem_Refine. simpl. exact I. }
      assert (Hforms' : context_formulas_hold (fun X : atom => Ty_FVar X) gamma'
          (update_rcontext RGamma x (R_Refine T Pred_True))).
      { eapply sem_context_entails_context_formulas; [exact Hsem'|].
        apply gamma_values_lc. exact Hvals'. }
      pose proof (entails_sound _ _ _ _ (e x HxL)
        (fun X : atom => Ty_FVar X) gamma' (fun y => Hvals' y) Hforms') as Hsound.
      assert (Hinstps : instantiate_formula (fun X : atom => Ty_FVar X) gamma' ps =
          instantiate_formula (fun X : atom => Ty_FVar X) gamma ps).
      { apply instantiate_qualifier_ext. intros y Hy. unfold gamma', update_gamma.
        destruct (Nat.eqb y x) eqn:E; [apply Nat.eqb_eq in E; subst; exfalso; apply Hxps; exact Hy|reflexivity]. }
      assert (Hinstqs : instantiate_formula (fun X : atom => Ty_FVar X) gamma' qs =
          instantiate_formula (fun X : atom => Ty_FVar X) gamma qs).
      { apply instantiate_qualifier_ext. intros y Hy. unfold gamma', update_gamma.
        destruct (Nat.eqb y x) eqn:E; [apply Nat.eqb_eq in E; subst; exfalso; apply Hxqs; exact Hy|reflexivity]. }
      rewrite instantiate_open_qualifier_commute in Hsound.
      2: { apply gamma_values_lc. exact Hvals'. }
      assert (Hvx : instantiate (fun X : atom => Ty_FVar X) gamma' (tm_fvar x) = v).
      { unfold instantiate, gamma', update_gamma. simpl. rewrite Nat.eqb_refl. reflexivity. }
      rewrite Hvx in Hsound.
      rewrite Hinstps in Hsound.
      specialize (Hsound H6).
      rewrite instantiate_open_qualifier_commute in Hsound.
      2: { apply gamma_values_lc. exact Hvals'. }
      rewrite Hvx, Hinstqs in Hsound. exact Hsound.
    }
    1: { eapply Sem_Exists with (w := instantiate (fun X : atom => Ty_FVar X) gamma v).
      - eapply instantiate_value; eauto.
      - eapply H; eauto.
      - unfold open_rty_tm. rewrite <- (instantiate_rty_open_general
          (fun X : atom => Ty_FVar X) gamma v 0 R2).
        + eapply H0; eauto.
        + apply gamma_values_lc. exact H1.
    }
    1: { inversion H3; subst.
      set (x := fresh (L ++ fv_rty_tm R1 ++ fv_rty_tm R2 ++ fv_rty_tm S ++ fv_rcontext_tm RGamma)).
      assert (Hxall : ~ In x (L ++ fv_rty_tm R1 ++ fv_rty_tm R2 ++ fv_rty_tm S ++ fv_rcontext_tm RGamma)).
      { unfold x. apply fresh_notin. }
      assert (HxL : ~ In x L).
      { intro Hin. apply Hxall. apply in_or_app; left; exact Hin. }
      assert (HxR1 : ~ In x (fv_rty_tm R1)).
      { intro Hin. apply Hxall. apply in_or_app; right. apply in_or_app; left; exact Hin. }
      assert (HxR2 : ~ In x (fv_rty_tm R2)).
      { intro Hin. apply Hxall. apply in_or_app; right. apply in_or_app; right. apply in_or_app; left; exact Hin. }
      assert (HxS : ~ In x (fv_rty_tm S)).
      { intro Hin. apply Hxall. apply in_or_app; right. apply in_or_app; right.
        apply in_or_app; right. apply in_or_app; left; exact Hin. }
      assert (Hxctx : forall y R, lookup_rcontext y RGamma = Some R -> ~ In x (fv_rty_tm R)).
      { intros y R Hlook Hin. apply Hxall. apply in_or_app; right.
        apply in_or_app; right. apply in_or_app; right. apply in_or_app; right.
        eapply lookup_rcontext_fv_in; eassumption. }
      set (gamma' := update_gamma gamma x w0).
      assert (Hvals' : value_valuation gamma').
      { unfold gamma'. eapply update_gamma_values; eauto. }
      assert (Hsem' : sem_context (fun X : atom => Ty_FVar X) gamma'
          (update_rcontext RGamma x R1)).
      { unfold gamma'. eapply sem_context_update.
        - exact H1.
        - exact HxR1.
        - exact Hxctx.
        - apply gamma_values_lc. exact H0.
        - exact H6.
        - exact H7. }
      assert (Hvx : instantiate (fun X : atom => Ty_FVar X) gamma' (tm_fvar x) = w0).
      { unfold instantiate, gamma', update_gamma. simpl. rewrite Nat.eqb_refl. reflexivity. }
      assert (HextR2 : instantiate_rty (fun X : atom => Ty_FVar X) gamma' R2 =
          instantiate_rty (fun X : atom => Ty_FVar X) gamma R2).
      { apply instantiate_rty_ext. intros y Hy. unfold gamma', update_gamma.
        destruct (Nat.eqb y x) eqn:E; [apply Nat.eqb_eq in E; subst y; exfalso; apply HxR2; exact Hy|reflexivity]. }
      assert (HextS : instantiate_rty (fun X : atom => Ty_FVar X) gamma' S =
          instantiate_rty (fun X : atom => Ty_FVar X) gamma S).
      { apply instantiate_rty_ext. intros y Hy. unfold gamma', update_gamma.
        destruct (Nat.eqb y x) eqn:E; [apply Nat.eqb_eq in E; subst y; exfalso; apply HxS; exact Hy|reflexivity]. }
      assert (Hbodyeq : instantiate_rty (fun X : atom => Ty_FVar X) gamma'
          (open_rty_tm R2 (tm_fvar x)) =
          open_rty_tm (instantiate_rty (fun X : atom => Ty_FVar X) gamma R2) w0).
      { unfold open_rty_tm. rewrite (instantiate_rty_open_general
          (fun X : atom => Ty_FVar X) gamma' (tm_fvar x) 0 R2
          (gamma_values_lc gamma' Hvals')).
        rewrite Hvx, HextR2. reflexivity. }
      assert (Hsource : rty_sem
          (instantiate_rty (fun X : atom => Ty_FVar X) gamma'
            (open_rty_tm R2 (tm_fvar x))) v).
      { rewrite Hbodyeq. exact H9. }
      pose proof (H x HxL gamma' Hvals' Hsem' v H2 Hsource) as Hresult.
      rewrite HextS in Hresult. exact Hresult.
    }
Qed.

Lemma subtype_semantics_fundamental : forall Delta RGamma R S (H : subtype Delta RGamma R S),
  subtype_semantic_property Delta RGamma R S H.
Proof.
  intros Delta RGamma R S Hsub. change (subtype_semantic_relation Delta RGamma R S).
  apply (subtype_ind subtype_semantic_relation);
    unfold subtype_semantic_relation, value_valuation;
    simpl; intros.
  all: try solve [eauto 12 using rty_sem, value].
  1: { apply Sem_Refine. inversion H3; subst; simpl in *.
    set (x := fresh (L ++ fv_qualifier ps ++ fv_qualifier qs ++ fv_rcontext_tm RGamma0)).
    assert (Hxall : ~ In x (L ++ fv_qualifier ps ++ fv_qualifier qs ++ fv_rcontext_tm RGamma0)).
    { unfold x. apply fresh_notin. }
    assert (HxL : ~ In x L).
    { intro Hin. apply Hxall. apply in_or_app; left; exact Hin. }
    assert (Hxps : ~ In x (fv_qualifier ps)).
    { intro Hin. apply Hxall. apply in_or_app; right. apply in_or_app; left; exact Hin. }
    assert (Hxqs : ~ In x (fv_qualifier qs)).
    { intro Hin. apply Hxall. apply in_or_app; right. apply in_or_app; right. apply in_or_app; left; exact Hin. }
    assert (Hxctx : forall y Rctx, lookup_rcontext y RGamma0 = Some Rctx -> ~ In x (fv_rty_tm Rctx)).
    { intros y Rctx Hlook Hin. apply Hxall. apply in_or_app; right.
      apply in_or_app; right. apply in_or_app; right.
      eapply lookup_rcontext_fv_in; eassumption. }
    set (gamma' := update_gamma gamma x v).
    assert (Hvals' : value_valuation gamma').
    { unfold gamma'. eapply update_gamma_values; eauto. }
    assert (Hsem' : sem_context (fun X : atom => Ty_FVar X) gamma'
        (update_rcontext RGamma0 x (R_Refine T Pred_True))).
    { unfold gamma'. eapply sem_context_update.
      - exact H1.
      - simpl. intuition.
      - exact Hxctx.
      - apply gamma_values_lc. exact H0.
      - exact H2.
      - apply Sem_Refine. simpl. exact I. }
    assert (Hforms' : context_formulas_hold (fun X : atom => Ty_FVar X) gamma'
        (update_rcontext RGamma0 x (R_Refine T Pred_True))).
    { eapply sem_context_entails_context_formulas; [exact Hsem'|].
      apply gamma_values_lc. exact Hvals'. }
    pose proof (entails_sound _ _ _ _ (H x HxL)
      (fun X : atom => Ty_FVar X) gamma' (fun y => Hvals' y) Hforms') as Hsound.
    assert (Hinstps : instantiate_formula (fun X : atom => Ty_FVar X) gamma' ps =
        instantiate_formula (fun X : atom => Ty_FVar X) gamma ps).
    { apply instantiate_qualifier_ext. intros y Hy. unfold gamma', update_gamma.
      destruct (Nat.eqb y x) eqn:E; [apply Nat.eqb_eq in E; subst y; exfalso; apply Hxps; exact Hy|reflexivity]. }
    assert (Hinstqs : instantiate_formula (fun X : atom => Ty_FVar X) gamma' qs =
        instantiate_formula (fun X : atom => Ty_FVar X) gamma qs).
    { apply instantiate_qualifier_ext. intros y Hy. unfold gamma', update_gamma.
      destruct (Nat.eqb y x) eqn:E; [apply Nat.eqb_eq in E; subst y; exfalso; apply Hxqs; exact Hy|reflexivity]. }
    rewrite instantiate_open_qualifier_commute in Hsound.
    2: { apply gamma_values_lc. exact Hvals'. }
    assert (Hvx : instantiate (fun X : atom => Ty_FVar X) gamma' (tm_fvar x) = v).
    { unfold instantiate, gamma', update_gamma. simpl. rewrite Nat.eqb_refl. reflexivity. }
    rewrite Hvx, Hinstps in Hsound.
    match goal with
    | Hq : qualifier_holds (open_qualifier_tm
        (instantiate_formula (fun X : atom => Ty_FVar X) gamma ps) v) |- _ =>
        specialize (Hsound Hq)
    end.
    rewrite instantiate_open_qualifier_commute in Hsound.
    2: { apply gamma_values_lc. exact Hvals'. }
    rewrite Hvx, Hinstqs in Hsound. exact Hsound.
  }
  1: { eapply Sem_Exists with (w := instantiate (fun X : atom => Ty_FVar X) gamma v).
    - eapply instantiate_value; eauto.
    - eapply rtype_semantics_fundamental; eauto 12.
    - assert (Heq : instantiate_rty (fun X : atom => Ty_FVar X) gamma
          (open_rty_tm R2 v) =
          open_rty_tm (instantiate_rty (fun X : atom => Ty_FVar X) gamma R2)
            (instantiate (fun X : atom => Ty_FVar X) gamma v)).
      { apply instantiate_rty_open_general. apply gamma_values_lc. exact H3. }
      pose proof (H2 gamma H3 H4 v0 H5 H6) as Hresult.
      rewrite Heq in Hresult. exact Hresult.
  }
  1: { inversion H6; subst.
    set (x := fresh (L ++ fv_rty_tm R1 ++ fv_rty_tm R2 ++ fv_rty_tm S0 ++ fv_rcontext_tm RGamma0)).
    assert (Hxall : ~ In x (L ++ fv_rty_tm R1 ++ fv_rty_tm R2 ++ fv_rty_tm S0 ++ fv_rcontext_tm RGamma0)).
    { unfold x. apply fresh_notin. }
    assert (HxL : ~ In x L).
    { intro Hin. apply Hxall. apply in_or_app; left; exact Hin. }
    assert (HxR1 : ~ In x (fv_rty_tm R1)).
    { intro Hin. apply Hxall. apply in_or_app; right. apply in_or_app; left; exact Hin. }
    assert (HxR2 : ~ In x (fv_rty_tm R2)).
    { intro Hin. apply Hxall. apply in_or_app; right. apply in_or_app; right. apply in_or_app; left; exact Hin. }
    assert (HxS : ~ In x (fv_rty_tm S0)).
    { intro Hin. apply Hxall. apply in_or_app; right. apply in_or_app; right. apply in_or_app; right. apply in_or_app; left; exact Hin. }
    assert (Hxctx : forall y Rctx, lookup_rcontext y RGamma0 = Some Rctx -> ~ In x (fv_rty_tm Rctx)).
    { intros y Rctx Hlook Hin. apply Hxall. apply in_or_app; right.
      apply in_or_app; right. apply in_or_app; right. apply in_or_app; right.
      eapply lookup_rcontext_fv_in; eassumption. }
    set (gamma' := update_gamma gamma x w).
    assert (Hvals' : value_valuation gamma').
    { unfold gamma'. eapply update_gamma_values; eauto. }
    assert (Hsem' : sem_context (fun X : atom => Ty_FVar X) gamma'
        (update_rcontext RGamma0 x R1)).
    { unfold gamma'. eapply sem_context_update.
      - exact H4.
      - exact HxR1.
      - exact Hxctx.
      - apply gamma_values_lc. exact H3.
      - exact H9.
      - exact H10. }
    assert (Hvx : instantiate (fun X : atom => Ty_FVar X) gamma' (tm_fvar x) = w).
    { unfold instantiate, gamma', update_gamma. simpl. rewrite Nat.eqb_refl. reflexivity. }
    assert (HextR2 : instantiate_rty (fun X : atom => Ty_FVar X) gamma' R2 =
        instantiate_rty (fun X : atom => Ty_FVar X) gamma R2).
    { apply instantiate_rty_ext. intros y Hy. unfold gamma', update_gamma.
      destruct (Nat.eqb y x) eqn:E; [apply Nat.eqb_eq in E; subst y; exfalso; apply HxR2; exact Hy|reflexivity]. }
    assert (HextS : instantiate_rty (fun X : atom => Ty_FVar X) gamma' S0 =
        instantiate_rty (fun X : atom => Ty_FVar X) gamma S0).
    { apply instantiate_rty_ext. intros y Hy. unfold gamma', update_gamma.
      destruct (Nat.eqb y x) eqn:E; [apply Nat.eqb_eq in E; subst y; exfalso; apply HxS; exact Hy|reflexivity]. }
    assert (Hbodyeq : instantiate_rty (fun X : atom => Ty_FVar X) gamma'
        (open_rty_tm R2 (tm_fvar x)) =
        open_rty_tm (instantiate_rty (fun X : atom => Ty_FVar X) gamma R2) w).
    { unfold open_rty_tm. rewrite (instantiate_rty_open_general
        (fun X : atom => Ty_FVar X) gamma' (tm_fvar x) 0 R2
        (gamma_values_lc gamma' Hvals')).
      rewrite Hvx, HextR2. reflexivity. }
    assert (Hsource : rty_sem
        (instantiate_rty (fun X : atom => Ty_FVar X) gamma'
          (open_rty_tm R2 (tm_fvar x))) v).
      { rewrite Hbodyeq. exact H12. }
    pose proof (H2 x HxL gamma' Hvals' Hsem' v H5 Hsource) as Hresult.
    rewrite HextS in Hresult. exact Hresult.
  }
Qed.

Lemma rtype_subtyping_fundamental :
  (forall Delta RGamma t R (H : has_rtype Delta RGamma t R),
      rtype_semantic_property Delta RGamma t R H) /\
  (forall Delta RGamma R S (H : subtype Delta RGamma R S),
      subtype_semantic_property Delta RGamma R S H).
Proof. split; [apply rtype_semantics_fundamental|apply subtype_semantics_fundamental]. Qed.

Lemma typed_integer_nonzero : forall m,
  has_rtype [] [] (tm_int m)
    (R_Refine Ty_Int (Pred_Ne (tm_bvar 0) (tm_int 0%Z))) -> m <> 0%Z.
Proof.
  intros m Hty.
  set (gamma := fun _ : atom => tm_int 0%Z).
  assert (Hvals : value_valuation gamma).
  { intros x. unfold gamma. constructor. }
  assert (Hctx : sem_context (fun X : atom => Ty_FVar X) gamma []).
  { intros x R Hlook. discriminate. }
  pose proof (rtype_semantics_fundamental [] [] (tm_int m)
    (R_Refine Ty_Int (Pred_Ne (tm_bvar 0) (tm_int 0%Z))) Hty
    gamma Hvals Hctx (v_int m)) as Hsem.
  inversion Hsem; subst; simpl in *.
  eapply ne_literal_nonzero. exact H2.
Qed.

Lemma initial_progress : forall t R,
  has_rtype [] empty_rcontext t R ->
  value t \/ exists t' : tm, t --> t'.
Proof.
  intros t R Hty. pose proof Hty as Htyped.
  dependent induction Hty; simpl in *; eauto 8 using value, step; try discriminate.
  all: try solve [eapply arith_progress; [eassumption|eassumption|
    eapply IHHty1; [apply JMeq_refl|reflexivity|eassumption]|
    eapply IHHty2; [apply JMeq_refl|reflexivity|eassumption]]].
  all: try (left; apply v_abs; unfold locally_closed_tm; exact (has_rtype_lc [] [] _ _ Htyped)).
  all: try (left; apply v_tabs; unfold locally_closed_tm; exact (has_rtype_lc [] [] _ _ Htyped)).
  all: try (left; apply v_fix; unfold locally_closed_tm; exact (has_rtype_lc [] [] _ _ Htyped)).
  - destruct (IHHty1 JMeq_refl eq_refl Hty1) as [Hv1|[t1' Hstep1]].
    + pose proof (has_rtype_erasure_typing _ _ _ _ Hty1) as Hcore1.
      destruct (canonical_arrow t1 (erase R1) (erase R2) Hcore1 Hv1)
        as [[T [body ->]]|[metric [body ->]]].
      * destruct (IHHty2 JMeq_refl eq_refl Hty2) as [Hv2|[t2' Hstep2]].
        -- right. exists (open_tm body t2). apply ST_AppAbs.
           ++ inversion Hv1; subst; assumption.
           ++ exact Hv2.
        -- right. exists (tm_app (tm_abs T body) t2'). apply ST_App2; assumption.
      * destruct (IHHty2 JMeq_refl eq_refl Hty2) as [Hv2|[t2' Hstep2]].
        -- right. exists (open_fix_body body (tm_fix (erase R1) (erase R2) metric body) t2).
           apply ST_AppFix; [inversion Hv1; subst; assumption|exact Hv2].
        -- right. exists (tm_app (tm_fix (erase R1) (erase R2) metric body) t2'). apply ST_App2; assumption.
    + right. exists (tm_app t1' t2). apply ST_App1.
      * exact Hstep1.
      * unfold locally_closed_tm. exact (has_rtype_lc [] [] _ _ Hty2).
  - destruct (IHHty JMeq_refl eq_refl Hty) as [Hv|[t' Hstep]].
    + pose proof (has_rtype_erasure_typing _ _ _ _ Hty) as Hcore.
      destruct (canonical_all t (erase R) Hcore Hv) as [body ->].
      right. exists (open_tm_ty body U). apply ST_TAppTabs.
      * inversion Hv; subst; assumption.
      * unfold locally_closed_ty. exact (wf_ty_lc [] U H).
    + right. exists (tm_tapp t' U). apply ST_TApp; [exact Hstep|exact (wf_ty_lc [] U H)].
  - eapply div_progress_with_nonzero; [eassumption|eassumption|
      eapply IHHty1; [apply JMeq_refl|reflexivity|eassumption]|
      eapply IHHty2; [apply JMeq_refl|reflexivity|eassumption]|].
    intros m Heq. subst t2. eapply typed_integer_nonzero. exact Hty2.
Qed.

Lemma rtype_preservation_closed : forall t t' R,
  has_rtype [] empty_rcontext t R -> t --> t' ->
  has_rtype [] empty_rcontext t' R.
Proof.
  intros t t' R Hty Hstep.
  dependent induction Hty; inversion Hstep; subst; eauto 12 using has_rtype. Show.
Qed.

Theorem never_stuck : forall (t t' : tm) (R : rty),
  has_rtype [] empty_rcontext t R ->
  multi t t' ->
  value t' \/ exists t'' : tm, t' --> t''.
Proof.
  intros t t' R Hty Hmulti.
  induction Hmulti.
  - eapply initial_progress; eauto.
  - eapply IHHmulti. eapply rtype_preservation_closed; eassumption.
Qed.

End SystemFRefinementRecursionTask.
