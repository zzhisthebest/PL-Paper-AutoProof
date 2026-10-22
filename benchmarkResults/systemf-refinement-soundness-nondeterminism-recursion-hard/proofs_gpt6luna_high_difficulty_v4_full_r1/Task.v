From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
From Stdlib Require Import ZArith.BinInt.
From Stdlib Require Import Program.Equality.
From Stdlib Require Import Program.Wf.

Module SystemFRefinementNonDeterminismRecursion.

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
  | tm_ifzero : tm -> tm -> tm -> tm
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
  | tm_choice t1 t2 => fv_tm t1 ++ fv_tm t2
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
  | tm_choice t1 t2 => ftv_tm t1 ++ ftv_tm t2
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
  | tm_choice t1 t2 => tm_choice (open_tm_ty_rec k U t1) (open_tm_ty_rec k U t2)
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
  | tm_choice t1 t2 => tm_choice (tm_ty_subst X U t1) (tm_ty_subst X U t2)
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
  | tm_choice t1 t2 => tm_choice (tm_subst x s t1) (tm_subst x s t2)
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
      lc_tm_at K k (tm_ifzero t t0 t1)
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
  | ST_ChoiceLeft : forall t1 t2,
      locally_closed_tm t1 -> locally_closed_tm t2 -> tm_choice t1 t2 --> t1
  | ST_ChoiceRight : forall t1 t2,
      locally_closed_tm t1 -> locally_closed_tm t2 -> tm_choice t1 t2 --> t2
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
      has_type Delta Gamma (tm_ifzero t t0 t1) T
  | T_Choice : forall Delta Gamma t1 t2 T,
      has_type Delta Gamma t1 T -> has_type Delta Gamma t2 T ->
      has_type Delta Gamma (tm_choice t1 t2) T.

Fixpoint max_atom (L : list atom) : atom :=
  match L with
  | [] => 0
  | x :: L' => Nat.max x (max_atom L')
  end.

Definition fresh (L : list atom) : atom := S (max_atom L).

End SystemFRefinementNonDeterminismRecursion.

Module SystemFRefinementNonDeterminismRecursionInfrastructure.
Import ListNotations SystemFRefinementNonDeterminismRecursion.

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
  | tm_choice t1 t2 => tm_choice (instantiate theta gamma t1) (instantiate theta gamma t2)
  | tm_fix A B metric body => tm_fix (instantiate_ty theta A) (instantiate_ty theta B)
      (instantiate theta gamma metric) (instantiate theta gamma body)
  | tm_ifzero t t0 t1 => tm_ifzero (instantiate theta gamma t)
      (instantiate theta gamma t0) (instantiate theta gamma t1)
  end.

End SystemFRefinementNonDeterminismRecursionInfrastructure.

From Stdlib Require Import Arith.PeanoNat Lists.List ZArith.BinInt.
Module SystemFRefinementNonDeterminismRecursionLogic.
Import ListNotations SystemFRefinementNonDeterminismRecursion.

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

Lemma int_no_step : forall n t, ~ (tm_int n --> t).
Proof. intros n t H; inversion H. Qed.

Lemma pms_int_inv : forall n v,
  predicate_multistep (tm_int n) v -> v = tm_int n.
Proof.
  intros n v H. inversion H; subst; auto.
  exfalso. eapply int_no_step; eauto.
Qed.

Lemma pms_int_int : forall n m,
  predicate_multistep (tm_int n) (tm_int m) -> n = m.
Proof.
  intros n m H. pose proof (pms_int_inv n (tm_int m) H). congruence.
Qed.

Lemma operational_eq_int : forall n m,
  interpret_eq operational_atoms (tm_int n) (tm_int m) -> n = m.
Proof.
  intros n m [v [Hn [Hm Hv]]].
  pose proof (pms_int_inv n v Hn) as En.
  pose proof (pms_int_inv m v Hm) as Em. congruence.
Qed.

Lemma nonzero_refinement_int : forall n,
  qualifier_holds (Pred_Ne (tm_int n) (tm_int 0%Z)) -> n <> 0%Z.
Proof.
  intros n H. unfold qualifier_holds, predicate_holds, Pred_Ne in H.
  simpl in H. intro E. subst n. apply H. exists (tm_int 0%Z).
  repeat split; constructor.
Qed.

Lemma nonzero_refinement_outcomes : forall t,
  qualifier_holds (Pred_Ne t (tm_int 0%Z)) ->
  forall n, predicate_multistep t (tm_int n) -> n <> 0%Z.
Proof.
  intros t H n Hrun E. subst n.
  unfold qualifier_holds, predicate_holds, Pred_Ne in H.
  simpl in H. apply H. exists (tm_int 0%Z).
  split; [exact Hrun|]. split; [constructor|constructor].
Qed.

Lemma predicate_multistep_trans : forall t u v,
  predicate_multistep t u -> predicate_multistep u v ->
  predicate_multistep t v.
Proof.
  intros t u v H. induction H; intros Huv.
  - exact Huv.
  - eapply PMS_Step; [exact H|eauto].
Qed.

Lemma nonzero_refinement_reduction_stable : forall t u,
  predicate_multistep t u ->
  qualifier_holds (Pred_Ne t (tm_int 0%Z)) ->
  qualifier_holds (Pred_Ne u (tm_int 0%Z)).
Proof.
  intros t u Htu H. unfold qualifier_holds, predicate_holds, Pred_Ne in *.
  simpl in *. intro Heq. apply H.
  destruct Heq as [v [Hu [Hz Hv]]].
  exists v. split; [eapply predicate_multistep_trans; eauto|].
  split; assumption.
Qed.

Lemma max_atom_bound : forall x L, In x L -> x <= max_atom L.
Proof.
  intros x L. induction L as [|a L IH]; simpl; intros H; [contradiction|].
  destruct H as [->|H].
  - apply Nat.le_max_l.
  - eapply Nat.le_trans; [apply IH; exact H|apply Nat.le_max_r].
Qed.

Lemma fresh_not_in : forall L, ~ In (fresh L) L.
Proof.
  intros L H. unfold fresh in H. pose proof (max_atom_bound (S (max_atom L)) L H).
  lia.
Qed.

Lemma lc_ty_at_weaken : forall K T,
  lc_ty_at K T -> lc_ty_at (S K) T.
Proof.
  intros K T H. induction H; eauto using lc_ty_at; constructor; lia.
Qed.

Lemma lc_ty_at_open_inv : forall K k T X,
  k <= K -> lc_ty_at K (open_ty_rec k (Ty_FVar X) T) ->
  ~ In X (fv_ty T) -> lc_ty_at (S K) T.
Proof.
  intros K k T. revert K k. induction T; intros K k X Hk Hlc Hfresh;
    simpl in Hlc, Hfresh.
  - destruct (Nat.eqb k n) eqn:E; simpl in Hlc.
    + apply Nat.eqb_eq in E. subst. constructor. lia.
    + inversion Hlc; subst. constructor. lia.
  - inversion Hlc; subst. constructor; lia.
  - inversion Hlc; subst. constructor.
    + eapply IHT1; [exact Hk|eassumption|].
      intro Hin. apply Hfresh. apply in_or_app; left; exact Hin.
    + eapply IHT2; [exact Hk|eassumption|].
      intro Hin. apply Hfresh. apply in_or_app; right; exact Hin.
  - inversion Hlc; subst. constructor.
    eapply IHT with (K:=S K) (k:=S k) (X:=X).
    + lia.
    + exact H1.
    + exact Hfresh.
  - inversion Hlc; subst. constructor.
Qed.

Lemma wf_ty_lc : forall Delta T,
  wf_ty Delta T -> lc_ty_at 0 T.
Proof.
  intros Delta T H. induction H.
  - constructor.
  - constructor; assumption.
  - constructor. set (X := fresh (L ++ fv_ty T)).
    assert (HX : ~ In X L).
    { unfold X. intro Hin. apply (fresh_not_in (L ++ fv_ty T)).
      apply in_or_app; left; exact Hin. }
    assert (Hfv : ~ In X (fv_ty T)).
    { unfold X. intro Hin. apply (fresh_not_in (L ++ fv_ty T)).
      apply in_or_app; right; exact Hin. }
    specialize (H0 X HX).
    apply lc_ty_at_open_inv with (k:=0) (X:=X); try lia; eauto.
  - constructor.
Qed.

Lemma lc_tm_at_weaken_type : forall K k t,
  lc_tm_at K k t -> lc_tm_at (S K) k t.
Proof.
  intros K k t H. induction H; eauto using lc_tm_at, lc_ty_at_weaken.
Qed.

Lemma lc_tm_at_weaken_term : forall K k t,
  lc_tm_at K k t -> lc_tm_at K (S k) t.
Proof.
  intros K k t H. induction H; eauto using lc_tm_at; try lia.
Qed.

Lemma lc_tm_at_open_far : forall K k t,
  lc_tm_at K k t -> forall j u,
  k <= j -> lc_tm_at K k u -> lc_tm_at K k (open_tm_rec j u t).
Proof.
  intros K k t H. induction H; intros j u Hkj Hu; simpl.
  - destruct (Nat.eqb j i) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + constructor. apply Nat.eqb_neq in E. lia.
  - constructor.
  - constructor; [assumption|].
    eapply IHlc_tm_at; [lia|eapply lc_tm_at_weaken_term; eassumption].
  - constructor; eauto.
  - constructor. eapply IHlc_tm_at. lia. eapply lc_tm_at_weaken_type. exact Hu.
  - constructor; eauto using lc_ty_at.
  - constructor.
  - constructor; eauto.
  - constructor; eauto.
  - econstructor; [assumption|assumption| |].
    + eapply IHlc_tm_at1; [lia|eapply lc_tm_at_weaken_term; exact Hu].
    + eapply IHlc_tm_at2; [lia|eapply lc_tm_at_weaken_term; eapply lc_tm_at_weaken_term; exact Hu].
  - constructor; eauto.
  - constructor; eauto.
Qed.

Lemma lc_tm_at_open : forall K k t u,
  lc_tm_at K (S k) t -> lc_tm_at K k u ->
  lc_tm_at K k (open_tm_rec k u t).
Proof.
  intros K k t. revert K k. induction t;
    intros K k u Ht Hu; inversion Ht; subst; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. exact Hu.
    + constructor. apply Nat.eqb_neq in E. lia.
  - constructor.
  - constructor; [assumption|].
    eapply IHt; [eassumption|eapply lc_tm_at_weaken_term; exact Hu].
  - constructor; eauto.
  - constructor. eapply IHt; [eassumption|eapply lc_tm_at_weaken_type; exact Hu].
  - constructor; eauto.
  - constructor.
  - constructor; eauto.
  - constructor; eauto.
  - econstructor; [eassumption|eassumption| |].
    + eapply IHt1; [eassumption|eapply lc_tm_at_weaken_term; exact Hu].
    + eapply IHt2; [eassumption|eapply lc_tm_at_weaken_term; eapply lc_tm_at_weaken_term; exact Hu].
  - constructor; eauto.
  - constructor; eauto.
Qed.

Lemma lc_tm_at_open_inv : forall K k t x,
  lc_tm_at K k (open_tm_rec k (tm_fvar x) t) ->
  ~ In x (fv_tm t) -> lc_tm_at K (S k) t.
Proof.
  intros K k t. revert K k. induction t;
    intros K k x Hlc Hfresh; simpl in Hlc, Hfresh.
  - destruct (Nat.eqb k n) eqn:E; simpl in Hlc.
    + inversion Hlc; subst. constructor. apply Nat.eqb_eq in E. lia.
    + inversion Hlc; subst. constructor. apply Nat.eqb_neq in E. lia.
  - inversion Hlc; subst. constructor.
  - inversion Hlc; subst. constructor; [assumption|].
    eapply IHt; eauto.
  - inversion Hlc; subst. constructor.
    + eapply IHt1; [eassumption|].
      intro Hin. apply Hfresh. apply in_or_app; left; exact Hin.
    + eapply IHt2; [eassumption|].
      intro Hin. apply Hfresh. apply in_or_app; right; exact Hin.
  - inversion Hlc; subst. constructor. eapply IHt; eauto.
  - inversion Hlc; subst. constructor; eauto.
  - inversion Hlc; subst. constructor.
  - inversion Hlc; subst. constructor.
    + eapply IHt1; [eassumption|].
      intro Hin. apply Hfresh. apply in_or_app; left; exact Hin.
    + eapply IHt2; [eassumption|].
      intro Hin. apply Hfresh. apply in_or_app; right; exact Hin.
  - inversion Hlc; subst. constructor.
    + eapply IHt1; [eassumption|].
      intro Hin. apply Hfresh. apply in_or_app; left; exact Hin.
    + eapply IHt2; [eassumption|].
      intro Hin. apply Hfresh. apply in_or_app; right; exact Hin.
  - inversion Hlc; subst. econstructor; [assumption|assumption| |].
    + eapply IHt1; [eassumption|].
      intro Hin. apply Hfresh. apply in_or_app; left; exact Hin.
    + eapply IHt2; [eassumption|].
      intro Hin. apply Hfresh. apply in_or_app; right; exact Hin.
  - inversion Hlc; subst. constructor.
    + eapply IHt1; [eassumption|].
      intro Hin. apply Hfresh. simpl. apply in_or_app; left; exact Hin.
    + eapply IHt2; [eassumption|].
      intro Hin. apply Hfresh. simpl. apply in_or_app; right. apply in_or_app; left; exact Hin.
    + eapply IHt3; [eassumption|].
      intro Hin. apply Hfresh. simpl. apply in_or_app; right. apply in_or_app; right; exact Hin.
  - inversion Hlc; subst. constructor.
    + eapply IHt1; [eassumption|].
      intro Hin. apply Hfresh. apply in_or_app; left; exact Hin.
    + eapply IHt2; [eassumption|].
      intro Hin. apply Hfresh. apply in_or_app; right; exact Hin.
Qed.

Lemma lc_tm_at_ty_open_inv : forall K k j t X,
  j <= K ->
  lc_tm_at K k (open_tm_ty_rec j (Ty_FVar X) t) ->
  ~ In X (ftv_tm t) -> lc_tm_at (S K) k t.
Proof.
  intros K k j t. revert K k j. induction t;
    intros K k j X Hjk Hlc Hfresh; simpl in Hlc, Hfresh.
  - inversion Hlc; subst. constructor; lia.
  - inversion Hlc; subst. constructor.
  - inversion Hlc; subst. econstructor.
    + eapply lc_ty_at_open_inv; eauto.
      intro Hin. apply Hfresh. apply in_or_app; left; exact Hin.
    + eapply IHt; eauto.
      intro Hin. apply Hfresh. apply in_or_app; right; exact Hin.
  - inversion Hlc; subst. constructor.
    + eapply IHt1; eauto.
      intro Hin. apply Hfresh. apply in_or_app; left; exact Hin.
    + eapply IHt2; eauto.
      intro Hin. apply Hfresh. apply in_or_app; right; exact Hin.
  - inversion Hlc; subst. constructor.
    eapply IHt with (j:=S j); eauto; lia.
  - inversion Hlc; subst. econstructor.
    + eapply IHt; eauto.
      intro Hin. apply Hfresh. apply in_or_app; left; exact Hin.
    + eapply lc_ty_at_open_inv; eauto.
      intro Hin. apply Hfresh. apply in_or_app; right; exact Hin.
  - inversion Hlc; subst. constructor.
  - inversion Hlc; subst. constructor.
    + eapply IHt1; eauto.
      intro Hin. apply Hfresh. apply in_or_app; left; exact Hin.
    + eapply IHt2; eauto.
      intro Hin. apply Hfresh. apply in_or_app; right; exact Hin.
  - inversion Hlc; subst. constructor.
    + eapply IHt1; eauto.
      intro Hin. apply Hfresh. apply in_or_app; left; exact Hin.
    + eapply IHt2; eauto.
      intro Hin. apply Hfresh. apply in_or_app; right; exact Hin.
  - inversion Hlc; subst. econstructor.
    + eapply lc_ty_at_open_inv; eauto.
      intro Hin. apply Hfresh. apply in_or_app; left; exact Hin.
    + eapply lc_ty_at_open_inv; eauto.
      intro Hin. apply Hfresh. apply in_or_app; right. apply in_or_app; left; exact Hin.
    + eapply IHt1; eauto.
      intro Hin. apply Hfresh. apply in_or_app; right. apply in_or_app; right. apply in_or_app; left; exact Hin.
    + eapply IHt2; eauto.
      intro Hin. apply Hfresh. apply in_or_app; right. apply in_or_app; right. apply in_or_app; right; exact Hin.
  - inversion Hlc; subst. constructor.
    + eapply IHt1; eauto.
      intro Hin. apply Hfresh. apply in_or_app; left; exact Hin.
    + eapply IHt2; eauto.
      intro Hin. apply Hfresh. apply in_or_app; right. apply in_or_app; left; exact Hin.
    + eapply IHt3; eauto.
      intro Hin. apply Hfresh. apply in_or_app; right. apply in_or_app; right; exact Hin.
  - inversion Hlc; subst. constructor.
    + eapply IHt1; eauto.
      intro Hin. apply Hfresh. apply in_or_app; left; exact Hin.
    + eapply IHt2; eauto.
      intro Hin. apply Hfresh. apply in_or_app; right; exact Hin.
Qed.

End SystemFRefinementNonDeterminismRecursionLogic.

From Stdlib Require Import Arith.PeanoNat Lists.List Lia ZArith.BinInt.
Module SystemFRefinementNonDeterminismRecursionTyping.
Import ListNotations.
Import SystemFRefinementNonDeterminismRecursion.
Export SystemFRefinementNonDeterminismRecursionLogic.
Import SystemFRefinementNonDeterminismRecursionInfrastructure.

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

Lemma entails_sound : forall Delta RGamma p q,
  entails Delta RGamma p q ->
  forall theta gamma,
    (forall x, value (gamma x)) ->
    context_formulas_hold theta gamma RGamma ->
    qualifier_holds (instantiate_formula theta gamma p) ->
    qualifier_holds (instantiate_formula theta gamma q).
Proof.
  intros Delta RGamma p q H. induction H;
    intros theta gamma Hvalues Hcontext Hp;
    unfold qualifier_holds, predicate_holds in *; simpl in *.
  - exact Hp.
  - exact I.
  - eapply IHentails2; [exact Hvalues|exact Hcontext|].
    eapply IHentails1; eauto.
  - exact (proj1 Hp).
  - exact (proj2 Hp).
  - split; [eapply IHentails1|eapply IHentails2]; eauto.
  - left; exact Hp.
  - right; exact Hp.
  - destruct Hp as [Hp|Hq].
    + eapply IHentails1; eauto.
    + eapply IHentails2; eauto.
  - intros Hq. apply (IHentails theta gamma Hvalues Hcontext).
    split; assumption.
  - destruct Hp as [Hp Hnot]. contradiction.
  - eapply Hcontext; eauto.
  - contradiction.
  - eapply H; eauto.
Qed.

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

  | RT_Choice : forall Delta RGamma t1 t2 R,
      has_rtype Delta RGamma t1 R -> has_rtype Delta RGamma t2 R ->
      has_rtype Delta RGamma (tm_choice t1 t2) R
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

End SystemFRefinementNonDeterminismRecursionTyping.

Module SystemFRefinementNonDeterminismRecursionEvaluation.
Import ListNotations SystemFRefinementNonDeterminismRecursion SystemFRefinementNonDeterminismRecursionInfrastructure SystemFRefinementNonDeterminismRecursionLogic SystemFRefinementNonDeterminismRecursionTyping.

Inductive multi : tm -> tm -> Prop :=
  | multi_refl : forall t, multi t t
  | multi_step : forall t1 t2 t3,
      t1 --> t2 -> multi t2 t3 -> multi t1 t3.
Notation "t '-->*' u" := (multi t u) (at level 40).

End SystemFRefinementNonDeterminismRecursionEvaluation.

Module SystemFRefinementNonDeterminismRecursionTask.
Import ListNotations SystemFRefinementNonDeterminismRecursion SystemFRefinementNonDeterminismRecursionInfrastructure SystemFRefinementNonDeterminismRecursionLogic SystemFRefinementNonDeterminismRecursionTyping SystemFRefinementNonDeterminismRecursionEvaluation.

Lemma erase_open_rty_tm_rec : forall k R u,
  erase (open_rty_tm_rec k u R) = erase R.
Proof.
  intros k R. revert k. induction R; intros k u; simpl; try reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR2. reflexivity.
  - rewrite IHR. reflexivity.
Qed.

Lemma erase_open_rty_tm : forall R u,
  erase (open_rty_tm R u) = erase R.
Proof. intros R u. apply erase_open_rty_tm_rec. Qed.

Lemma erase_open_rty_ty_rec : forall k R U,
  erase (open_rty_ty_rec k U R) = open_ty_rec k U (erase R).
Proof.
  intros k R. revert k. induction R; intros k U; simpl; try reflexivity;
    f_equal; auto.
Qed.

Lemma erase_open_rty_ty : forall R U,
  erase (open_rty_ty R U) = open_ty (erase R) U.
Proof. intros R U. apply erase_open_rty_ty_rec. Qed.

Lemma open_ty_rec_inj_fresh : forall T U k X,
  ~ In X (fv_ty T) -> ~ In X (fv_ty U) ->
  open_ty_rec k (Ty_FVar X) T = open_ty_rec k (Ty_FVar X) U -> T = U.
Proof.
  induction T; intros U k X HfT HfU Hop; destruct U; simpl in Hop.
  - destruct (Nat.eqb k n) eqn:E1;
    destruct (Nat.eqb k n0) eqn:E2; simpl in Hop; try discriminate;
    inversion Hop; subst; try reflexivity;
    apply Nat.eqb_eq in E1; apply Nat.eqb_eq in E2; congruence.
  - destruct (Nat.eqb k n) eqn:E; simpl in Hop.
    + inversion Hop; subst. exfalso. apply HfU. simpl. auto.
    + discriminate.
  - destruct (Nat.eqb k n); simpl in Hop; discriminate.
  - destruct (Nat.eqb k n); simpl in Hop; discriminate.
  - destruct (Nat.eqb k n); simpl in Hop; discriminate.
  - destruct (Nat.eqb k n) eqn:E; simpl in Hop.
    + inversion Hop; subst. exfalso. apply HfT. simpl. auto.
    + discriminate.
  - inversion Hop; reflexivity.
  - discriminate.
  - discriminate.
  - discriminate.
  - destruct (Nat.eqb k n); simpl in Hop; discriminate.
  - discriminate.
  - inversion Hop; subst. f_equal.
    + eapply IHT1 with (k:=k) (X:=X).
      * intro Hin. apply HfT. apply in_or_app; left; exact Hin.
      * intro Hin. apply HfU. apply in_or_app; left; exact Hin.
      * now inversion Hop.
    + eapply IHT2 with (k:=k) (X:=X).
      * intro Hin. apply HfT. apply in_or_app; right; exact Hin.
      * intro Hin. apply HfU. apply in_or_app; right; exact Hin.
      * now inversion Hop.
  - discriminate. (* arrow / forall *)
  - discriminate. (* arrow / int *)
  - destruct (Nat.eqb k n); simpl in Hop; discriminate.
  - discriminate.
  - discriminate.
  - inversion Hop; subst. f_equal. eapply IHT with (k:=S k) (X:=X); eauto.
  - discriminate.
  - destruct (Nat.eqb k n); simpl in Hop; discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - reflexivity.
Qed.

Lemma erase_subtype : forall D G R S,
  subtype D G R S -> erase R = erase S.
Proof.
  intros D G R S H. induction H; simpl; try congruence.
  - f_equal; [symmetry; exact IHsubtype|].
    specialize (H1 (fresh L) (fresh_not_in L)).
    rewrite !erase_open_rty_tm in H1. exact H1.
  - rewrite erase_open_rty_tm in IHsubtype. exact IHsubtype.
  - specialize (H2 (fresh L) (fresh_not_in L)).
    rewrite erase_open_rty_tm in H2. exact H2.
  - set (X := fresh (L ++ fv_ty (erase R) ++ fv_ty (erase S))).
    assert (HXL : ~ In X L).
    { unfold X. intro Hin. apply (fresh_not_in (L ++ fv_ty (erase R) ++ fv_ty (erase S))).
      apply in_or_app. left. exact Hin. }
    assert (HXR : ~ In X (fv_ty (erase R))).
    { unfold X. intro Hin. apply (fresh_not_in (L ++ fv_ty (erase R) ++ fv_ty (erase S))).
      apply in_or_app. right. apply in_or_app. left. exact Hin. }
    assert (HXS : ~ In X (fv_ty (erase S))).
    { unfold X. intro Hin. apply (fresh_not_in (L ++ fv_ty (erase R) ++ fv_ty (erase S))).
      apply in_or_app. right. apply in_or_app. right. exact Hin. }
    specialize (H0 X HXL). rewrite !erase_open_rty_ty in H0.
    f_equal. eapply open_ty_rec_inj_fresh with (k:=0) (X:=X); eauto.
Qed.

Lemma erase_wf_rty : forall D G R,
  wf_rty D G R -> wf_ty D (erase R).
Proof.
  intros D G R H. induction H; simpl; eauto using wf_ty.
  - apply WF_Arrow; [exact IHwf_rty|].
    specialize (H1 (fresh L) (fresh_not_in L)).
    rewrite erase_open_rty_tm in H1. exact H1.
  - specialize (H1 (fresh L) (fresh_not_in L)).
    rewrite erase_open_rty_tm in H1. exact H1.
  - eapply WF_All with (L:=L). intros X HX.
    specialize (H0 X HX). rewrite erase_open_rty_ty in H0. exact H0.
Qed.

Lemma lookup_erase_context : forall x RGamma R,
  lookup_rcontext x RGamma = Some R ->
  lookup_context x (erase_context RGamma) = Some (erase R).
Proof.
  intros x RGamma. induction RGamma as [|[y S] Gamma IH]; intros R H;
    simpl in *; [discriminate|].
  destruct (Nat.eqb x y) eqn:E.
  - inversion H; subst. simpl. reflexivity.
  - simpl. eapply IH; eauto.
Qed.

Lemma lookup_update_equiv : forall G1 G2 x T,
  (forall y, lookup_context y G1 = lookup_context y G2) ->
  forall y, lookup_context y (update G1 x T) =
            lookup_context y (update G2 x T).
Proof.
  intros G1 G2 x T Heq y. unfold update. simpl.
  destruct (Nat.eqb y x); auto.
Qed.

Lemma has_type_context_equiv : forall D G1 t T,
  has_type D G1 t T ->
  forall G2, (forall x, lookup_context x G1 = lookup_context x G2) ->
    has_type D G2 t T.
Proof.
  intros D G1 t T H. induction H; intros G2 Heq.
  - eapply T_Var; [rewrite <- Heq; eassumption|assumption].
  - eapply T_Abs with (L:=L); [assumption|].
    intros x Hx. specialize (H1 x Hx).
    eapply H1 with (G2:=update G2 x T1).
    apply lookup_update_equiv. exact Heq.
  - eapply T_App; eauto.
  - eapply T_TAbs with (L:=L). intros X HX.
    specialize (H0 X HX). eapply H0. exact Heq.
  - eapply T_TApp; eauto.
  - constructor.
  - eapply T_Div; eauto.
  - eapply T_Arith; eauto.
  - eapply T_Fix with (L:=L); [assumption|assumption| |].
    + intros x Hx. specialize (H2 x Hx).
      eapply H2 with (G2:=update G2 x A).
      apply lookup_update_equiv. exact Heq.
    + intros f x Hf Hx. specialize (H4 f x Hf Hx).
      eapply H4 with (G2:=update (update G2 x A) f (Ty_Arrow A B)).
      apply lookup_update_equiv. apply lookup_update_equiv. exact Heq.
  - eapply T_IfZero; eauto.
  - eapply T_Choice; eauto.
Qed.

Lemma has_type_lc : forall D G t T,
  has_type D G t T -> locally_closed_tm t.
Proof.
  intros D G t T H. induction H.
  - constructor.
  - constructor.
    + eapply wf_ty_lc; eauto.
    + set (x := fresh (L ++ fv_tm t2)).
      assert (HxL : ~ In x L).
      { unfold x. intro Hin. apply (fresh_not_in (L ++ fv_tm t2)).
        apply in_or_app; left; exact Hin. }
      assert (Hxfv : ~ In x (fv_tm t2)).
      { unfold x. intro Hin. apply (fresh_not_in (L ++ fv_tm t2)).
        apply in_or_app; right; exact Hin. }
      specialize (H1 x HxL).
      eapply lc_tm_at_open_inv; eauto.
  - constructor; assumption.
  - constructor.
    set (X := fresh (L ++ ftv_tm t)).
    assert (HXL : ~ In X L).
    { unfold X. intro Hin. apply (fresh_not_in (L ++ ftv_tm t)).
      apply in_or_app; left; exact Hin. }
    assert (HXT : ~ In X (ftv_tm t)).
    { unfold X. intro Hin. apply (fresh_not_in (L ++ ftv_tm t)).
      apply in_or_app; right; exact Hin. }
    specialize (H0 X HXL).
    eapply lc_tm_at_ty_open_inv with (j:=0) (X:=X); eauto; lia.
  - constructor. exact IHhas_type.
    eapply wf_ty_lc; eassumption.
  - constructor.
  - constructor; assumption.
  - constructor; assumption.
  - set (f := fresh (L ++ fv_tm body)).
    assert (HfL : ~ In f L).
    { unfold f. intro Hin. apply (fresh_not_in (L ++ fv_tm body)).
      apply in_or_app; left; exact Hin. }
    assert (Hffv : ~ In f (fv_tm body)).
    { unfold f. intro Hin. apply (fresh_not_in (L ++ fv_tm body)).
      apply in_or_app; right; exact Hin. }
    set (x := fresh (f :: (L ++
      (fv_tm (open_tm_rec 1 (tm_fvar f) body) ++ fv_tm metric)))).
    assert (HxFL : ~ In x (f :: L)).
    { unfold x. intro Hin. apply (fresh_not_in (f :: (L ++
        (fv_tm (open_tm_rec 1 (tm_fvar f) body) ++ fv_tm metric)))).
      simpl. destruct Hin as [Hin|Hin].
      - left; exact Hin.
      - right. apply in_or_app; left; exact Hin. }
    assert (Hxbody : ~ In x (fv_tm (open_tm_rec 1 (tm_fvar f) body))).
    { unfold x. intro Hin. apply (fresh_not_in (f :: (L ++
        (fv_tm (open_tm_rec 1 (tm_fvar f) body) ++ fv_tm metric)))).
      simpl. right. apply in_or_app; right. apply in_or_app; left; exact Hin. }
    assert (Hxmetric : ~ In x (fv_tm metric)).
    { unfold x. intro Hin. apply (fresh_not_in (f :: (L ++
        (fv_tm (open_tm_rec 1 (tm_fvar f) body) ++ fv_tm metric)))).
      simpl. right. apply in_or_app; right. apply in_or_app; right; exact Hin. }
    assert (HxL : ~ In x L).
    { intro Hin. apply HxFL. simpl. right. exact Hin. }
    constructor.
    + eapply wf_ty_lc; eauto.
    + eapply wf_ty_lc; eauto.
    + specialize (H2 x HxL).
      eapply lc_tm_at_open_inv; eauto.
    + specialize (H4 f x HfL HxFL).
      unfold open_fix_body in H4.
      pose proof (lc_tm_at_open_inv 0 0 (open_tm_rec 1 (tm_fvar f) body)
        x H4 Hxbody) as Hmid.
      eapply lc_tm_at_open_inv with (k:=1) (x:=f); eauto.
  - constructor; assumption.
  - constructor; assumption.
Qed.

Lemma canonical_int : forall v,
  has_type [] empty v Ty_Int -> value v ->
  exists n : Z, v = tm_int n.
Proof.
  intros v Hty Hv. inversion Hv; subst; inversion Hty; subst; eauto.
Qed.

Lemma canonical_arrow : forall v A B,
  has_type [] empty v (Ty_Arrow A B) -> value v ->
  (exists body, v = tm_abs A body) \/
  (exists metric body, v = tm_fix A B metric body).
Proof.
  intros v A B Hty Hv. inversion Hv; subst; inversion Hty; subst; eauto.
Qed.

Lemma canonical_all : forall v T,
  has_type [] empty v (Ty_All T) -> value v -> exists body, v = tm_tabs body.
Proof.
  intros v T Hty Hv. inversion Hv; subst; inversion Hty; subst; eauto.
Qed.

CoInductive safe_state : tm -> Prop :=
| SafeState : forall t,
    (value t \/ exists u, t --> u) ->
    (forall u, t --> u -> safe_state u) ->
    safe_state t.

Lemma value_no_step : forall v u, value v -> ~ v --> u.
Proof. intros v u Hv Hs; inversion Hv; subst; inversion Hs. Qed.

Lemma safe_value : forall v, value v -> safe_state v.
Proof.
  intros v Hv. apply SafeState.
  - left; exact Hv.
  - intros u Hu. exfalso. eapply value_no_step; eauto.
Qed.

Lemma safe_state_progress : forall t,
  safe_state t -> value t \/ exists u, t --> u.
Proof. intros t H. inversion H; assumption. Qed.

Lemma safe_state_multi : forall t u,
  safe_state t -> multi t u -> safe_state u.
Proof.
  intros t u Hsafe Hmulti. induction Hmulti.
  - exact Hsafe.
  - inversion Hsafe as [t0 Hprogress Hnext]; subst.
    apply IHHmulti. eapply Hnext; eauto.
Qed.

Lemma erase_has_rtype : forall D G t R,
  has_rtype D G t R -> has_type D (erase_context G) t (erase R).
Proof.
  intros D G t R H. induction H; simpl; eauto using has_type, erase_wf_rty.
  - eapply T_Var.
    + eapply lookup_erase_context; eauto.
    + eapply erase_wf_rty; eauto.
  - eapply T_Abs with (L:=L).
    + eapply erase_wf_rty; eauto.
    + intros x Hx. specialize (H1 x Hx).
      rewrite erase_open_rty_tm in H1. exact H1.
  - eapply T_TAbs with (L:=L). intros X HX.
    specialize (H0 X HX). rewrite erase_open_rty_ty in H0.
    exact H0.
  - rewrite erase_open_rty_ty. eapply T_TApp; eauto.
  - pose proof (erase_wf_rty _ _ _ H) as Hwf. inversion Hwf; subst.
    eapply T_Fix with (L:=L); eauto.
    intros f x Hf Hx. specialize (H2 f x Hf Hx).
    rewrite erase_open_rty_tm in H2. exact H2.
  - change (has_type Delta (update (erase_context RGamma) x Ty_Int)
      t0 (erase R)) in IHhas_rtype1.
    change (has_type Delta (update (erase_context RGamma) x Ty_Int)
      t1 (erase R)) in IHhas_rtype2.
    assert (Hbase : lookup_context x (erase_context RGamma) = Some Ty_Int).
    { change (lookup_context x (erase_context RGamma) =
        Some (erase (R_Refine Ty_Int p))).
      eapply lookup_erase_context; eauto. }
    assert (Hif : has_type Delta (update (erase_context RGamma) x Ty_Int)
        (tm_ifzero (tm_fvar x) t0 t1) (erase R)).
    { eapply T_IfZero.
      - eapply T_Var; [simpl; rewrite Nat.eqb_refl; reflexivity|constructor].
      - exact IHhas_rtype1.
      - exact IHhas_rtype2. }
    eapply has_type_context_equiv; [exact Hif|].
    intro y. unfold update. simpl. destruct (Nat.eqb y x) eqn:E.
    + apply Nat.eqb_eq in E. subst y. rewrite Hbase. reflexivity.
    + reflexivity.
  - rewrite <- (erase_subtype Delta RGamma R S H1). exact IHhas_rtype.
Qed.

Definition nonzero_value_sound : Prop :=
  forall u, has_rtype [] empty_rcontext u
      (R_Refine Ty_Int (Pred_Ne (tm_bvar 0) (tm_int 0%Z))) ->
    value u -> forall n, u = tm_int n -> n <> 0%Z.

Lemma rtype_progress : forall t R,
  has_rtype [] empty_rcontext t R ->
  nonzero_value_sound ->
  value t \/ exists u, t --> u.
Proof.
  intros t R H. dependent induction H; intros Hnz.
  - left. apply v_abs.
    assert (Hrt : has_rtype [] empty_rcontext (tm_abs (erase R1) body)
        (R_Func R1 R2)) by (eapply RT_Abs; eauto).
    eapply has_type_lc. eapply erase_has_rtype; exact Hrt.
  - pose proof (IHhas_rtype1 JMeq_refl eq_refl Hnz) as Hprog1.
    pose proof (IHhas_rtype2 JMeq_refl eq_refl Hnz) as Hprog2.
    destruct Hprog1 as [Hv1|[t1' Hs1]].
    + destruct Hprog2 as [Hv2|[t2' Hs2]].
      * pose proof (erase_has_rtype [] empty_rcontext t1 (R_Func R1 R2) H) as Hcore.
        destruct (canonical_arrow t1 (erase R1) (erase R2) Hcore Hv1)
          as [[body ->]|[metric [body ->]]].
        -- right. exists (open_tm body t2). eapply ST_AppAbs.
           ++ eapply has_type_lc; exact Hcore.
           ++ exact Hv2.
        -- right. exists (open_fix_body body
             (tm_fix (erase R1) (erase R2) metric body) t2). eapply ST_AppFix.
           ++ eapply has_type_lc; exact Hcore.
           ++ exact Hv2.
      * right. exists (tm_app t1 t2'). eapply ST_App2; eauto.
    + right. exists (tm_app t1' t2). eapply ST_App1; eauto.
      pose proof (erase_has_rtype [] empty_rcontext t2 R1 H0) as Hcore2.
      eapply has_type_lc; exact Hcore2.
  - left. apply v_tabs.
    assert (Hrt : has_rtype [] empty_rcontext (tm_tabs body) (R_Poly R))
      by (eapply RT_TAbs; eauto).
    eapply has_type_lc. eapply erase_has_rtype; exact Hrt.
  - pose proof (IHhas_rtype JMeq_refl eq_refl Hnz) as Hprog.
    destruct Hprog as [Hv|[t' Hs]].
    + pose proof (erase_has_rtype [] empty_rcontext t (R_Poly R) H) as Hcore.
      destruct (canonical_all t (erase R) Hcore Hv) as [body ->].
      right. exists (open_tm_ty body U). eapply ST_TAppTabs.
      * eapply has_type_lc; exact Hcore.
      * eapply wf_ty_lc; eassumption.
    + right. exists (tm_tapp t' U). eapply ST_TApp; eauto.
      eapply wf_ty_lc; eassumption.
  - left. constructor.
  - pose proof (IHhas_rtype1 JMeq_refl eq_refl Hnz) as Hprog1.
    pose proof (IHhas_rtype2 JMeq_refl eq_refl Hnz) as Hprog2.
    destruct Hprog1 as [Hv1|[t1' Hs1]].
    + destruct Hprog2 as [Hv2|[t2' Hs2]].
      * pose proof (erase_has_rtype [] empty_rcontext t1
          (R_Refine Ty_Int Pred_True) H) as Hcore1.
        pose proof (erase_has_rtype [] empty_rcontext t2
          (R_Refine Ty_Int (Pred_Ne (tm_bvar 0) (tm_int 0%Z))) H0) as Hcore2.
        destruct (canonical_int t1 Hcore1 Hv1) as [n ->].
        destruct (canonical_int t2 Hcore2 Hv2) as [m ->].
        right. exists (tm_int (Z.div n m)). eapply ST_DivInt.
        eapply Hnz; eauto.
      * right. exists (tm_div t1 t2'). eapply ST_Div2; eauto.
    + right. exists (tm_div t1' t2). eapply ST_Div1; eauto.
      pose proof (erase_has_rtype [] empty_rcontext t2
        (R_Refine Ty_Int (Pred_Ne (tm_bvar 0) (tm_int 0%Z))) H0) as Hcore2.
      eapply has_type_lc; exact Hcore2.
  - pose proof (IHhas_rtype1 JMeq_refl eq_refl Hnz) as Hprog1.
    pose proof (IHhas_rtype2 JMeq_refl eq_refl Hnz) as Hprog2.
    destruct Hprog1 as [Hv1|[t1' Hs1]].
    + destruct Hprog2 as [Hv2|[t2' Hs2]].
      * pose proof (erase_has_rtype [] empty_rcontext t1
          (R_Refine Ty_Int Pred_True) H) as Hcore1.
        pose proof (erase_has_rtype [] empty_rcontext t2
          (R_Refine Ty_Int Pred_True) H0) as Hcore2.
        destruct (canonical_int t1 Hcore1 Hv1) as [n ->].
        destruct (canonical_int t2 Hcore2 Hv2) as [m ->].
        right. exists (tm_int (eval_integer_operator op n m)). constructor.
      * right. exists (tm_arith op t1 t2'). eapply ST_Arith2; eauto.
    + right. exists (tm_arith op t1' t2). eapply ST_Arith1; eauto.
      pose proof (erase_has_rtype [] empty_rcontext t2
        (R_Refine Ty_Int Pred_True) H0) as Hcore2.
      eapply has_type_lc; exact Hcore2.
  - right. exists t1. apply ST_ChoiceLeft.
    + pose proof (erase_has_rtype [] empty_rcontext t1 R H) as Hcore1.
      eapply has_type_lc; exact Hcore1.
    + pose proof (erase_has_rtype [] empty_rcontext t2 R H0) as Hcore2.
      eapply has_type_lc; exact Hcore2.
  - left. assumption.
  - left. apply v_fix.
    assert (Hrt : has_rtype [] empty_rcontext
        (tm_fix A (erase R2) metric body)
        (R_Func (measured_input A p metric) R2)) by (eapply RT_Fix; eauto).
    eapply has_type_lc. eapply erase_has_rtype; exact Hrt.
  - exact (IHhas_rtype JMeq_refl eq_refl Hnz).
Qed.

Lemma never_stuck_of_typed_reach : forall t t',
  (forall u, multi t u -> exists S, has_rtype [] empty_rcontext u S) ->
  nonzero_value_sound ->
  multi t t' -> value t' \/ exists t'', t' --> t''.
Proof.
  intros t t' Htyped Hnz Hmulti.
  destruct (Htyped t' Hmulti) as [S HS].
  eapply rtype_progress; eauto.
Qed.

Fixpoint rty_size (R : rty) : nat :=
  match R with
  | R_Refine _ _ => 1
  | R_Func R1 R2 | R_Exists R1 R2 => S (rty_size R1 + rty_size R2)
  | R_Poly R1 => S (rty_size R1)
  end.

Lemma rty_size_open_tm_rec : forall k u R,
  rty_size (open_rty_tm_rec k u R) = rty_size R.
Proof.
  intros k u R. revert k. induction R; intros k; simpl; try reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR. reflexivity.
Qed.

Fixpoint qualifier_fv (p : qualifier) : list atom :=
  match p with
  | Pred_True | Pred_False => []
  | Pred_Eq t1 t2 | Pred_Lt t1 t2 | Pred_Le t1 t2 => fv_tm t1 ++ fv_tm t2
  | Pred_And p q | Pred_Or p q => qualifier_fv p ++ qualifier_fv q
  | Pred_Not p => qualifier_fv p
  end.

Fixpoint rty_term_fv (R : rty) : list atom :=
  match R with
  | R_Refine _ ps => qualifier_fv ps
  | R_Func R1 R2 | R_Exists R1 R2 => rty_term_fv R1 ++ rty_term_fv R2
  | R_Poly R1 => rty_term_fv R1
  end.


Fixpoint open_qualifier_env (k : nat) (rho : list tm) (p : qualifier) : qualifier :=
  match rho with
  | [] => p
  | w :: rho' => open_qualifier_tm_rec k w (open_qualifier_env (S k) rho' p)
  end.

Fixpoint env_insert (k : nat) (w : tm) (rho : list tm) : list tm :=
  match k, rho with
  | 0, _ => w :: rho
  | S _, [] => [w]
  | S k', z :: rho' => z :: env_insert k' w rho'
  end.

Fixpoint rty_value_semantics (theta : type_substitution)
    (gamma : term_substitution) (R : rty) (rho : list tm) (v : tm) : Prop :=
  match R with
  | R_Refine _ ps =>
      value v /\ qualifier_holds
        (open_qualifier_tm
          (open_qualifier_env 1 rho (instantiate_formula theta gamma ps)) v)
  | R_Func _ _ => value v
  | R_Exists R1 R2 =>
      value v /\ exists w, value w /\
        rty_value_semantics theta gamma R1 rho w /\
        rty_value_semantics theta gamma R2 (w :: rho) v
  | R_Poly _ => value v
  end.

Definition update_term_substitution
    (gamma : term_substitution) (x : atom) (v : tm) : term_substitution :=
  fun y => if Nat.eqb y x then v else gamma y.

Definition semantic_rcontext
    (theta : type_substitution) (gamma : term_substitution)
    (G : rcontext) : Prop :=
  (forall x, value (gamma x) /\ locally_closed_tm (gamma x)) /\
  (forall x R, lookup_rcontext x G = Some R ->
    rty_value_semantics theta gamma R [] (gamma x)).

Fixpoint rcontext_support (G : rcontext) : list atom :=
  match G with
  | [] => []
  | (x, R) :: G' => x :: (rty_term_fv R ++ rcontext_support G')
  end.

Lemma lookup_rcontext_support : forall x G R,
  lookup_rcontext x G = Some R -> In x (rcontext_support G).
Proof.
  intros x G. induction G as [|[y S] G IH]; simpl; intros R H; [discriminate|].
  destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E. subst. simpl. auto.
  - right. apply in_or_app. right. eapply IH; eauto.
Qed.

Lemma lookup_rcontext_type_support : forall y G R x,
  lookup_rcontext y G = Some R ->
  In x (rty_term_fv R) -> In x (rcontext_support G).
Proof.
  intros y G. induction G as [|[z S] G IH]; intros R x Hlookup Hfv;
    simpl in *; [discriminate|].
  destruct (Nat.eqb y z) eqn:E.
  - inversion Hlookup; subst. right. apply in_or_app; left. exact Hfv.
  - right. apply in_or_app; right. eapply IH; eauto.
Qed.



Lemma instantiate_ty_fv_empty : forall theta T,
  fv_ty T = [] -> instantiate_ty theta T = T.
Proof.
  intros theta T. induction T; simpl; intros H; try reflexivity.
  - discriminate.
  - apply app_eq_nil in H as [H1 H2]. rewrite (IHT1 H1), (IHT2 H2). reflexivity.
  - f_equal. apply IHT. exact H.
Qed.

Lemma instantiate_tm_fv_empty : forall theta gamma t,
  fv_tm t = [] -> ftv_tm t = [] -> instantiate theta gamma t = t.
Proof.
  intros theta gamma t. induction t; simpl; intros Hfv Hftv; try reflexivity.
  - discriminate.
  - f_equal.
    + eapply instantiate_ty_fv_empty. apply app_eq_nil in Hftv as [Hty _]. exact Hty.
    + apply IHt; [exact Hfv|]. apply app_eq_nil in Hftv as [_ H]. exact H.
  - apply app_eq_nil in Hfv as [H1 H2].
    apply app_eq_nil in Hftv as [H1' H2']. f_equal; eauto.
  - f_equal. apply IHt; assumption.
  - simpl in Hftv. apply app_eq_nil in Hftv as [Hbody Hty].
    f_equal.
    + apply IHt; [exact Hfv|exact Hbody].
    + eapply instantiate_ty_fv_empty; eauto.
  - apply app_eq_nil in Hfv as [H1 H2].
    apply app_eq_nil in Hftv as [H1' H2']. f_equal; eauto.
  - apply app_eq_nil in Hfv as [H1 H2].
    apply app_eq_nil in Hftv as [H1' H2']. f_equal; eauto.
  - apply app_eq_nil in Hfv as [Hm Hb].
    apply app_eq_nil in Hftv as [Hty1 Hrest].
    apply app_eq_nil in Hrest as [Hty2 Hrest].
    apply app_eq_nil in Hrest as [Hm' Hb'].
    f_equal.
    + eapply instantiate_ty_fv_empty; eauto.
    + eapply instantiate_ty_fv_empty; eauto.
    + eapply IHt1; eauto.
    + eapply IHt2; eauto.
  - apply app_eq_nil in Hfv as [H1 Hrest].
    apply app_eq_nil in Hrest as [H2 H3].
    apply app_eq_nil in Hftv as [H1' Hrest'].
    apply app_eq_nil in Hrest' as [H2' H3'].
    f_equal; eauto.
  - apply app_eq_nil in Hfv as [H1 H2].
    apply app_eq_nil in Hftv as [H1' H2']. f_equal; eauto.
Qed.

Lemma instantiate_formula_closed : forall theta gamma p,
  predicate_closed p -> instantiate_formula theta gamma p = p.
Proof.
  intros theta gamma p. induction p; simpl; intros H; try reflexivity.
  - destruct H as [_ [F1 [FT1 [_ [F2 FT2]]]]]. f_equal;
      [eapply instantiate_tm_fv_empty; eauto|eapply instantiate_tm_fv_empty; eauto].
  - destruct H as [_ [F1 [FT1 [_ [F2 FT2]]]]]. f_equal;
      [eapply instantiate_tm_fv_empty; eauto|eapply instantiate_tm_fv_empty; eauto].
  - destruct H as [_ [F1 [FT1 [_ [F2 FT2]]]]]. f_equal;
      [eapply instantiate_tm_fv_empty; eauto|eapply instantiate_tm_fv_empty; eauto].
  - destruct H as [H1 H2]. f_equal; eauto.
  - destruct H as [H1 H2]. f_equal; eauto.
  - f_equal; eauto.
Qed.

Lemma nonzero_from_semantics : forall theta gamma n,
  rty_value_semantics theta gamma
    (R_Refine Ty_Int (Pred_Ne (tm_bvar 0) (tm_int 0%Z))) [] (tm_int n) ->
  n <> 0%Z.
Proof.
  intros theta gamma n Hsem.
  cbn [rty_value_semantics instantiate_formula
       open_qualifier_tm open_qualifier_tm_rec open_pred_tm_rec] in Hsem.
  destruct Hsem as [_ Hsem].
  apply nonzero_refinement_int. exact Hsem.
Qed.

Lemma instantiate_tm_update_fresh : forall theta gamma x v t,
  ~ In x (fv_tm t) ->
  instantiate theta (update_term_substitution gamma x v) t =
  instantiate theta gamma t.
Proof.
  intros theta gamma x v t. induction t; intros Hfresh; simpl in *;
    try reflexivity.
  all: unfold update_term_substitution; simpl.
  - destruct (Nat.eqb a x) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso; apply Hfresh; simpl; auto.
    + reflexivity.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal; [apply IHt1|apply IHt2]; intro Hin; apply Hfresh;
      simpl; apply in_or_app; [left|right]; exact Hin.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal; [apply IHt1|apply IHt2]; intro Hin; apply Hfresh;
      simpl; apply in_or_app; [left|right]; exact Hin.
  - f_equal; [apply IHt1|apply IHt2]; intro Hin; apply Hfresh;
      simpl; apply in_or_app; [left|right]; exact Hin.
  - f_equal.
    + apply IHt1. intro Hin. apply Hfresh. simpl. apply in_or_app; left; exact Hin.
    + apply IHt2. intro Hin. apply Hfresh. simpl. apply in_or_app; right; exact Hin.
  - f_equal.
    + apply IHt1. intro Hin. apply Hfresh. simpl. apply in_or_app; left; exact Hin.
    + apply IHt2. intro Hin. apply Hfresh. simpl. apply in_or_app; right.
      apply in_or_app; left; exact Hin.
    + apply IHt3. intro Hin. apply Hfresh. simpl. apply in_or_app; right.
      apply in_or_app; right; exact Hin.
  - f_equal.
    + apply IHt1. intro Hin. apply Hfresh. simpl. apply in_or_app; left; exact Hin.
    + apply IHt2. intro Hin. apply Hfresh. simpl. apply in_or_app; right; exact Hin.
Qed.



Lemma instantiate_formula_update_fresh : forall theta gamma x v p,
  ~ In x (qualifier_fv p) ->
  instantiate_formula theta (update_term_substitution gamma x v) p =
  instantiate_formula theta gamma p.
Proof.
  intros theta gamma x v p. induction p; intros Hfresh; simpl in *; try reflexivity.
  - f_equal; [eapply instantiate_tm_update_fresh|eapply instantiate_tm_update_fresh];
      intro Hin; apply Hfresh; simpl; apply in_or_app; [left|right]; exact Hin.
  - f_equal; [eapply instantiate_tm_update_fresh|eapply instantiate_tm_update_fresh];
      intro Hin; apply Hfresh; simpl; apply in_or_app; [left|right]; exact Hin.
  - f_equal; [eapply instantiate_tm_update_fresh|eapply instantiate_tm_update_fresh];
      intro Hin; apply Hfresh; simpl; apply in_or_app; [left|right]; exact Hin.
  - f_equal; [apply IHp1|apply IHp2]; intro Hin; apply Hfresh;
      simpl; apply in_or_app; [left|right]; exact Hin.
  - f_equal; [apply IHp1|apply IHp2]; intro Hin; apply Hfresh;
      simpl; apply in_or_app; [left|right]; exact Hin.
  - f_equal. apply IHp. exact Hfresh.
Qed.



Lemma rty_value_semantics_update_fresh : forall theta gamma x w R rho v,
  ~ In x (rty_term_fv R) ->
  rty_value_semantics theta (update_term_substitution gamma x w) R rho v <->
  rty_value_semantics theta gamma R rho v.
Proof.
  intros theta gamma x w R. induction R; intros rho v Hfresh; simpl in *.
  - split.
    + intros [Hv Hq]. split; [exact Hv|].
      rewrite instantiate_formula_update_fresh in Hq by exact Hfresh. exact Hq.
    + intros [Hv Hq]. split; [exact Hv|].
      rewrite instantiate_formula_update_fresh by exact Hfresh. exact Hq.
  - tauto.
  - assert (Hf1 : ~ In x (rty_term_fv R1)).
    { intro Hin. apply Hfresh. apply in_or_app; left; exact Hin. }
    assert (Hf2 : ~ In x (rty_term_fv R2)).
    { intro Hin. apply Hfresh. apply in_or_app; right; exact Hin. }
    split.
    + intros [Hv [z [Hz [H1 H2]]]]. split; [exact Hv|]. exists z. repeat split; try assumption.
      * apply (IHR1 rho z Hf1). exact H1.
      * apply (IHR2 (z :: rho) v Hf2). exact H2.
    + intros [Hv [z [Hz [H1 H2]]]]. split; [exact Hv|]. exists z. repeat split; try assumption.
      * apply (IHR1 rho z Hf1). exact H1.
      * apply (IHR2 (z :: rho) v Hf2). exact H2.
  - tauto.
Qed.

Lemma semantic_rcontext_update_fresh : forall theta gamma G x v,
  ~ In x (rcontext_support G) ->
  semantic_rcontext theta gamma G ->
  value v ->
  semantic_rcontext theta (update_term_substitution gamma x v) G.
Proof.
  intros theta gamma G. induction G as [|[y R] G IH]; intros x v Hfresh Hctx Hv.
  - split.
    + intro z. unfold update_term_substitution. destruct (Nat.eqb z x) eqn:E.
      * apply Nat.eqb_eq in E. subst. split; [exact Hv|].
        unfold locally_closed_tm. inversion Hv; subst; eauto using lc_tm_at.
      * destruct Hctx as [Hg _]. apply Hg.
    + intros z S Hlookup. discriminate.
  - assert (Hneq : y <> x).
    { intro E. subst. apply Hfresh. simpl. auto. }
    assert (Hrest : ~ In x (rty_term_fv R ++ rcontext_support G)).
    { intro Hin. apply Hfresh. simpl. right. exact Hin. }
    assert (Hrf : ~ In x (rty_term_fv R)).
    { intro Hin. apply Hrest. apply in_or_app; left; exact Hin. }
    assert (Htail : ~ In x (rcontext_support G)).
    { intro Hin. apply Hrest. apply in_or_app; right; exact Hin. }
    destruct Hctx as [Hg Hsem]. split.
    + intro z. unfold update_term_substitution. destruct (Nat.eqb z x) eqn:E.
      * apply Nat.eqb_eq in E. subst. split; [exact Hv|].
        unfold locally_closed_tm. inversion Hv; subst; eauto using lc_tm_at.
      * apply Hg.
    + intros z S Hlookup. simpl in Hlookup. destruct (Nat.eqb z y) eqn:Ezy.
      * inversion Hlookup; subst S.
        apply Nat.eqb_eq in Ezy. subst z.
        assert (Ezx : y <> x) by exact Hneq.
        unfold update_term_substitution.
        assert (Efalse : Nat.eqb y x = false) by (apply Nat.eqb_neq; exact Ezx).
        rewrite Efalse.
        apply (proj2 (rty_value_semantics_update_fresh theta gamma x v R [] (gamma y) Hrf)).
        eapply Hsem. simpl. rewrite Nat.eqb_refl. reflexivity.
      * assert (HlookupG : lookup_rcontext z G = Some S) by exact Hlookup.
        assert (Htypefresh : ~ In x (rty_term_fv S)).
        { intro Hin. apply Htail.
          eapply lookup_rcontext_type_support; eauto. }
        assert (Ezx : z <> x).
        { intro E. subst z. apply Hfresh. simpl. right. apply in_or_app; right.
          eapply lookup_rcontext_support; eauto. }
        unfold update_term_substitution.
        assert (Efalse : Nat.eqb z x = false) by (apply Nat.eqb_neq; exact Ezx).
        rewrite Efalse.
        apply (proj2 (rty_value_semantics_update_fresh theta gamma x v S [] (gamma z) Htypefresh)).
        eapply Hsem. simpl. rewrite Ezy. exact HlookupG.
Qed.

Lemma instantiate_open_tm_rec_update : forall theta gamma x v t k,
  ~ In x (fv_tm t) ->
  instantiate theta
    (update_term_substitution gamma x (instantiate theta gamma v))
    (open_tm_rec k (tm_fvar x) t) =
  instantiate theta gamma (open_tm_rec k v t).
Proof.
  intros theta gamma x v t. induction t; intros k Hfresh; simpl in *;
    try reflexivity.
  - destruct (Nat.eqb k n); simpl.
    + unfold update_term_substitution. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - destruct (Nat.eqb a x) eqn:E; simpl.
    + apply Nat.eqb_eq in E. subst. exfalso; apply Hfresh; simpl; auto.
    + unfold update_term_substitution. rewrite E. reflexivity.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal; [apply IHt1|apply IHt2]; intro Hin; apply Hfresh;
      simpl; apply in_or_app; [left|right]; exact Hin.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal; [apply IHt1|apply IHt2]; intro Hin; apply Hfresh;
      simpl; apply in_or_app; [left|right]; exact Hin.
  - f_equal; [apply IHt1|apply IHt2]; intro Hin; apply Hfresh;
      simpl; apply in_or_app; [left|right]; exact Hin.
  - f_equal.
    + apply IHt1. intro Hin. apply Hfresh. simpl. apply in_or_app; left; exact Hin.
    + apply IHt2. intro Hin. apply Hfresh. simpl. apply in_or_app; right; exact Hin.
  - f_equal.
    + apply IHt1. intro Hin. apply Hfresh. simpl. apply in_or_app; left; exact Hin.
    + apply IHt2. intro Hin. apply Hfresh. simpl. apply in_or_app; right.
      apply in_or_app; left; exact Hin.
    + apply IHt3. intro Hin. apply Hfresh. simpl. apply in_or_app; right.
      apply in_or_app; right; exact Hin.
  - f_equal.
    + apply IHt1. intro Hin. apply Hfresh. simpl. apply in_or_app; left; exact Hin.
    + apply IHt2. intro Hin. apply Hfresh. simpl. apply in_or_app; right; exact Hin.
Qed.

Lemma instantiate_open_qualifier_update : forall theta gamma x v p,
  ~ In x (qualifier_fv p) ->
  instantiate_formula theta
    (update_term_substitution gamma x (instantiate theta gamma v))
    (open_qualifier_tm p (tm_fvar x)) =
  instantiate_formula theta gamma (open_qualifier_tm p v).
Proof.
  intros theta gamma x v p. induction p; intros Hfresh; simpl in *; try reflexivity.
  - f_equal; apply instantiate_open_tm_rec_update; intro Hin;
      apply Hfresh; simpl; apply in_or_app; [left|right]; exact Hin.
  - f_equal; apply instantiate_open_tm_rec_update; intro Hin;
      apply Hfresh; simpl; apply in_or_app; [left|right]; exact Hin.
  - f_equal; apply instantiate_open_tm_rec_update; intro Hin;
      apply Hfresh; simpl; apply in_or_app; [left|right]; exact Hin.
  - f_equal; [apply IHp1|apply IHp2]; intro Hin; apply Hfresh;
      simpl; apply in_or_app; [left|right]; exact Hin.
  - f_equal; [apply IHp1|apply IHp2]; intro Hin; apply Hfresh;
      simpl; apply in_or_app; [left|right]; exact Hin.
  - f_equal. apply IHp. exact Hfresh.
Qed.

Lemma open_tm_rec_lc_identity : forall K k t j u,
  lc_tm_at K k t -> k <= j -> open_tm_rec j u t = t.
Proof.
  intros K k t. revert K k. induction t; intros K k j u Hlc Hkj; simpl.
  - inversion Hlc; subst. destruct (Nat.eqb j n) eqn:E;
      [apply Nat.eqb_eq in E; lia|reflexivity].
  - reflexivity.
  - inversion Hlc; subst. f_equal. eapply IHt; [eassumption|lia].
  - inversion Hlc; subst. f_equal; [eapply IHt1|eapply IHt2]; eauto.
  - inversion Hlc; subst. f_equal. eapply IHt with (K:=S K) (k:=k) (j:=j);
      [eassumption|exact Hkj].
  - inversion Hlc; subst. f_equal. eapply IHt; eauto.
  - reflexivity.
  - inversion Hlc; subst. f_equal; [eapply IHt1|eapply IHt2]; eauto.
  - inversion Hlc; subst. f_equal; [eapply IHt1|eapply IHt2]; eauto.
  - inversion Hlc; subst. f_equal.
    + eapply IHt1 with (K:=K) (k:=S k) (j:=S j); [exact H7|lia].
    + eapply IHt2 with (K:=K) (k:=S (S k)) (j:=S (S j)); [exact H8|lia].
  - inversion Hlc; subst. f_equal; [eapply IHt1|eapply IHt2|eapply IHt3]; eauto.
  - inversion Hlc; subst. f_equal; [eapply IHt1|eapply IHt2]; eauto.
Qed.

Lemma instantiate_open_tm_rec : forall theta gamma k u t,
  (forall x, locally_closed_tm (gamma x)) ->
  instantiate theta gamma (open_tm_rec k u t) =
  open_tm_rec k (instantiate theta gamma u) (instantiate theta gamma t).
Proof.
  intros theta gamma k u t Hgamma. revert k. induction t; intros k; simpl; try reflexivity.
  - destruct (Nat.eqb k n); reflexivity.
  - rewrite open_tm_rec_lc_identity with (K:=0) (k:=0) (j:=k).
    + reflexivity.
    + apply Hgamma.
    + lia.
  - f_equal. apply IHt.
  - f_equal; [apply IHt1|apply IHt2].
  - f_equal. apply IHt.
  - f_equal. apply IHt.
  - f_equal; [apply IHt1|apply IHt2].
  - f_equal; [apply IHt1|apply IHt2].
  - f_equal; [apply IHt1|apply IHt2].
  - f_equal; [apply IHt1|apply IHt2|apply IHt3].
  - f_equal; [apply IHt1|apply IHt2].
Qed.

Lemma instantiate_open_qualifier : forall theta gamma p u,
  (forall x, locally_closed_tm (gamma x)) ->
  instantiate_formula theta gamma (open_qualifier_tm p u) =
  open_qualifier_tm (instantiate_formula theta gamma p) (instantiate theta gamma u).
Proof.
  intros theta gamma p. induction p; intros u Hgamma; simpl; try reflexivity.
  - unfold open_qualifier_tm, open_qualifier_tm_rec, open_pred_tm, open_pred_tm_rec.
    simpl. f_equal; apply instantiate_open_tm_rec; assumption.
  - unfold open_qualifier_tm, open_qualifier_tm_rec, open_pred_tm, open_pred_tm_rec.
    simpl. f_equal; apply instantiate_open_tm_rec; assumption.
  - unfold open_qualifier_tm, open_qualifier_tm_rec, open_pred_tm, open_pred_tm_rec.
    simpl. f_equal; apply instantiate_open_tm_rec; assumption.
  - unfold open_qualifier_tm. simpl. f_equal; [apply IHp1|apply IHp2]; exact Hgamma.
  - unfold open_qualifier_tm. simpl. f_equal; [apply IHp1|apply IHp2]; exact Hgamma.
  - unfold open_qualifier_tm. simpl. f_equal. apply IHp. exact Hgamma.
Qed.

Lemma instantiate_open_qualifier_rec : forall theta gamma k p u,
  (forall x, locally_closed_tm (gamma x)) ->
  instantiate_formula theta gamma (open_qualifier_tm_rec k u p) =
  open_qualifier_tm_rec k (instantiate theta gamma u)
    (instantiate_formula theta gamma p).
Proof.
  intros theta gamma k p. induction p; intros u Hgamma; simpl; try reflexivity.
  - unfold open_qualifier_tm_rec, open_pred_tm_rec. simpl.
    f_equal; apply instantiate_open_tm_rec; assumption.
  - unfold open_qualifier_tm_rec, open_pred_tm_rec. simpl.
    f_equal; apply instantiate_open_tm_rec; assumption.
  - unfold open_qualifier_tm_rec, open_pred_tm_rec. simpl.
    f_equal; apply instantiate_open_tm_rec; assumption.
  - unfold open_qualifier_tm_rec, open_pred_tm_rec. simpl.
    f_equal; [apply IHp1|apply IHp2]; assumption.
  - unfold open_qualifier_tm_rec, open_pred_tm_rec. simpl.
    f_equal; [apply IHp1|apply IHp2]; assumption.
  - unfold open_qualifier_tm_rec, open_pred_tm_rec. simpl.
    f_equal. apply IHp. exact Hgamma.
Qed.

Lemma lc_ty_at_weaken_many : forall n K T,
  lc_ty_at K T -> lc_ty_at (K + n) T.
Proof.
  intros n. induction n; intros K T H.
  - simpl. replace (K + 0) with K by lia. exact H.
  - replace (K + S n) with (S K + n) by lia.
    apply IHn. eapply lc_ty_at_weaken. exact H.
Qed.

Lemma lc_tm_at_weaken_type_many : forall n K k t,
  lc_tm_at K k t -> lc_tm_at (K + n) k t.
Proof.
  intros n. induction n; intros K k t H.
  - replace (K + 0) with K by lia. exact H.
  - replace (K + S n) with (S K + n) by lia.
    apply IHn. eapply lc_tm_at_weaken_type. exact H.
Qed.

Lemma lc_tm_at_weaken_term_many : forall n K k t,
  lc_tm_at K k t -> lc_tm_at K (k + n) t.
Proof.
  intros n. induction n; intros K k t H.
  - replace (k + 0) with k by lia. exact H.
  - replace (k + S n) with (S k + n) by lia.
    apply IHn. eapply lc_tm_at_weaken_term. exact H.
Qed.

Lemma instantiate_ty_lc_at : forall theta K T,
  lc_ty_at K T ->
  (forall X, locally_closed_ty (theta X)) ->
  lc_ty_at K (instantiate_ty theta T).
Proof.
  intros theta K T. revert K. induction T; intros K Hlc Htheta; simpl.
  - inversion Hlc; subst. constructor. assumption.
  - specialize (Htheta a). unfold locally_closed_ty in Htheta.
    replace K with (0 + K) by lia. eapply lc_ty_at_weaken_many; exact Htheta.
  - inversion Hlc; subst. constructor.
    + eapply IHT1; eassumption.
    + eapply IHT2; eassumption.
  - inversion Hlc; subst. constructor. eapply IHT with (K:=S K).
    + exact H1.
    + intro X. specialize (Htheta X). unfold locally_closed_ty in Htheta.
      replace (S K) with (0 + S K) by lia. eapply lc_ty_at_weaken_many; exact Htheta.
  - inversion Hlc; subst. constructor.
Qed.

Lemma instantiate_tm_lc_at : forall theta gamma K k t,
  lc_tm_at K k t ->
  (forall X, locally_closed_ty (theta X)) ->
  (forall x, locally_closed_tm (gamma x)) ->
  lc_tm_at K k (instantiate theta gamma t).
Proof.
  intros theta gamma K k t Hlc. induction Hlc; intros Htheta Hgamma; simpl.
  - constructor. exact H.
  - unfold locally_closed_tm in Hgamma.
    eapply lc_tm_at_weaken_type_many.
    eapply lc_tm_at_weaken_term_many.
    apply Hgamma.
  - econstructor.
    + eapply instantiate_ty_lc_at; eauto.
    + eapply IHHlc; eauto.
  - constructor; [eapply IHHlc1|eapply IHHlc2]; eauto.
  - constructor. eapply IHHlc; eauto.
  - econstructor.
    + eapply IHHlc; eauto.
    + eapply instantiate_ty_lc_at; eauto.
  - constructor.
  - constructor; [eapply IHHlc1|eapply IHHlc2]; eauto.
  - constructor; [eapply IHHlc1|eapply IHHlc2]; eauto.
  - econstructor.
    + eapply instantiate_ty_lc_at; eauto.
    + eapply instantiate_ty_lc_at; eauto.
    + eapply IHHlc1; eauto.
    + eapply IHHlc2; eauto.
  - constructor; [eapply IHHlc1|eapply IHHlc2|eapply IHHlc3]; eauto.
  - constructor; eauto.
Qed.

Lemma instantiate_value : forall theta gamma v,
  value v ->
  (forall X, locally_closed_ty (theta X)) ->
  (forall x, value (gamma x) /\ locally_closed_tm (gamma x)) ->
  value (instantiate theta gamma v).
Proof.
  intros theta gamma v Hv Htheta Hgamma. inversion Hv; subst.
  - apply v_abs. eapply instantiate_tm_lc_at; eauto.
  - apply v_tabs. eapply instantiate_tm_lc_at; eauto.
  - simpl. constructor.
  - apply v_fix. eapply instantiate_tm_lc_at; eauto.
Qed.

Lemma open_qualifier_env_insert : forall j k rho w p,
  length rho = k ->
  open_qualifier_env j rho (open_qualifier_tm_rec (j + k) w p) =
  open_qualifier_env j (env_insert k w rho) p.
Proof.
  intros j k rho. revert j k. induction rho as [|z rho IH];
    intros j k w p Hlen; destruct k; simpl in *.
  - rewrite Nat.add_0_r. reflexivity.
  - discriminate.
  - discriminate.
  - inversion Hlen; subst. simpl.
    replace (j + S (length rho)) with (S j + length rho) by lia.
    rewrite IH with (j:=S j) (k:=length rho) (w:=w) (p:=p);
      [reflexivity|reflexivity].
Qed.

Lemma rty_value_semantics_open : forall theta gamma R k w rho v,
  (forall x, locally_closed_tm (gamma x)) ->
  length rho = k ->
  rty_value_semantics theta gamma (open_rty_tm_rec k w R) rho v <->
  rty_value_semantics theta gamma R (env_insert k (instantiate theta gamma w) rho) v.
Proof.
  intros theta gamma R. induction R; intros k w rho v Hgamma Hlen; simpl in *.
  - split; intros [Hv Hq]; split; [exact Hv| |exact Hv|].
    + rewrite instantiate_open_qualifier_rec in Hq by exact Hgamma.
      rewrite open_qualifier_env_insert in Hq by exact Hlen. exact Hq.
    + rewrite instantiate_open_qualifier_rec.
      * rewrite open_qualifier_env_insert. exact Hq. exact Hlen.
      * exact Hgamma.
  - tauto.
  - split.
    + intros [Hv [z [Hz [H1 H2]]]]. split; [exact Hv|exists z]. repeat split; try assumption.
      * apply (IHR1 k w rho z Hgamma Hlen). exact H1.
      * apply (IHR2 (S k) w (z :: rho) v Hgamma). 
        -- simpl. f_equal. exact Hlen.
        -- exact H2.
    + intros [Hv [z [Hz [H1 H2]]]]. split; [exact Hv|exists z]. repeat split; try assumption.
      * apply (IHR1 k w rho z Hgamma Hlen). exact H1.
      * apply (IHR2 (S k) w (z :: rho) v Hgamma).
        -- simpl. f_equal. exact Hlen.
        -- exact H2.
  - tauto.
Qed.

Lemma semantic_rcontext_formulas : forall theta gamma G,
  semantic_rcontext theta gamma G ->
  context_formulas_hold theta gamma G.
Proof.
  intros theta gamma G [Hg Hsem] x T p Hlookup.
  specialize (Hsem x (R_Refine T p) Hlookup).
  simpl in Hsem. destruct Hsem as [_ Hsem].
  rewrite (instantiate_open_qualifier theta gamma p (tm_fvar x)
    (fun y => proj2 (Hg y))).
  simpl. exact Hsem.
Qed.

Lemma semantic_rcontext_add_true : forall theta gamma G x T v,
  semantic_rcontext theta gamma G ->
  gamma x = v ->
  semantic_rcontext theta gamma
    (update_rcontext G x (R_Refine T Pred_True)).
Proof.
  intros theta gamma G x T v [Hg Hsem] Hx. split; [exact Hg|].
  intros y R Hlookup. simpl in Hlookup. destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst y. inversion Hlookup; subst R. subst v. simpl.
    split; [apply (proj1 (Hg x))|]. exact I.
  - eapply Hsem. exact Hlookup.
Qed.

Scheme has_rtype_subtype_mutind := Induction for has_rtype Sort Prop
with subtype_has_rtype_mutind := Induction for subtype Sort Prop.
Combined Scheme rtype_and_subtype_mutind from
  has_rtype_subtype_mutind, subtype_has_rtype_mutind.

Definition sem_rtyping_prop (Delta : ty_context) (G : rcontext)
    (t : tm) (R : rty) (_ : has_rtype Delta G t R) : Prop :=
  forall theta gamma,
    semantic_rcontext theta gamma G ->
    value (instantiate theta gamma t) ->
    rty_value_semantics theta gamma R [] (instantiate theta gamma t).

Definition sem_subtype_prop (Delta : ty_context) (G : rcontext)
    (R S : rty) (_ : subtype Delta G R S) : Prop :=
  forall theta gamma v,
    semantic_rcontext theta gamma G ->
    rty_value_semantics theta gamma R [] v ->
    rty_value_semantics theta gamma S [] v.

Lemma fundamental_value_and_subtyping :
  (forall Delta G t R (H : has_rtype Delta G t R),
      sem_rtyping_prop Delta G t R H) /\
  (forall Delta G R S (H : subtype Delta G R S),
      sem_subtype_prop Delta G R S H).
Proof.
  apply rtype_and_subtype_mutind with
    (P:=sem_rtyping_prop) (P0:=sem_subtype_prop).
  - unfold sem_rtyping_prop. intros Delta G x R Hlookup Hwf theta gamma Hctx Hv.
    simpl in Hv. destruct Hctx as [_ Hctx]. eapply Hctx; eauto.
  - unfold sem_rtyping_prop. intros. simpl. assumption.
  - unfold sem_rtyping_prop. intros. exfalso.
    match goal with Hval : value (instantiate _ _ (tm_app _ _)) |- _ => simpl in Hval; inversion Hval end.
  - unfold sem_rtyping_prop. intros. simpl. assumption.
  - unfold sem_rtyping_prop. intros. exfalso.
    match goal with Hval : value (instantiate _ _ (tm_tapp _ _)) |- _ => simpl in Hval; inversion Hval end.
  - unfold sem_rtyping_prop. intros. simpl. split; [constructor|].
    unfold qualifier_holds, predicate_holds. simpl. exists (tm_int n).
    repeat split; try constructor.
  - unfold sem_rtyping_prop. intros. exfalso.
    match goal with Hval : value (instantiate _ _ (tm_div _ _)) |- _ => simpl in Hval; inversion Hval end.
  - unfold sem_rtyping_prop. intros. exfalso.
    match goal with Hval : value (instantiate _ _ (tm_arith _ _ _)) |- _ => simpl in Hval; inversion Hval end.
  - unfold sem_rtyping_prop. intros. exfalso.
    match goal with Hval : value (instantiate _ _ (tm_choice _ _)) |- _ => simpl in Hval; inversion Hval end.
  - unfold sem_rtyping_prop. intros. cbn [rty_value_semantics].
    split; [assumption|].
    destruct H as [Hg _].
    cbn [open_qualifier_env].
    rewrite <- (instantiate_open_qualifier theta gamma ps v
      (fun x => proj2 (Hg x))).
    rewrite instantiate_formula_closed by exact p. exact q.
  - unfold sem_rtyping_prop. intros. simpl. assumption.
  - unfold sem_rtyping_prop. intros. exfalso.
    match goal with Hval : value (instantiate _ _ (tm_ifzero _ _ _)) |- _ => simpl in Hval; inversion Hval end.
  - unfold sem_rtyping_prop. intros. eapply H0; [exact H1|].
    eapply H; eauto.
  - unfold sem_subtype_prop. intros. assumption.
  - unfold sem_subtype_prop. intros L Delta RGamma T ps qs Hent theta gamma v Hctx Hsrc.
    simpl in Hsrc. destruct Hsrc as [Hv Hps].
    set (x := fresh (L ++ rcontext_support RGamma ++ qualifier_fv ps ++ qualifier_fv qs)).
    assert (HxL : ~ In x L).
    { unfold x. intro Hin. apply (fresh_not_in (L ++ rcontext_support RGamma ++ qualifier_fv ps ++ qualifier_fv qs)).
      apply in_or_app; left; exact Hin. }
    assert (HxG : ~ In x (rcontext_support RGamma)).
    { unfold x. intro Hin. apply (fresh_not_in (L ++ rcontext_support RGamma ++ qualifier_fv ps ++ qualifier_fv qs)).
      apply in_or_app; right. apply in_or_app; left; exact Hin. }
    assert (Hxps : ~ In x (qualifier_fv ps)).
    { unfold x. intro Hin. apply (fresh_not_in (L ++ rcontext_support RGamma ++ qualifier_fv ps ++ qualifier_fv qs)).
      apply in_or_app; right. apply in_or_app; right. apply in_or_app; left; exact Hin. }
    assert (Hxqs : ~ In x (qualifier_fv qs)).
    { unfold x. intro Hin. apply (fresh_not_in (L ++ rcontext_support RGamma ++ qualifier_fv ps ++ qualifier_fv qs)).
      apply in_or_app; right. apply in_or_app; right. apply in_or_app; right; exact Hin. }
    set (gamma' := update_term_substitution gamma x v).
    assert (Hctx' : semantic_rcontext theta gamma' RGamma).
    { unfold gamma'. eapply semantic_rcontext_update_fresh; eauto. }
    assert (Hg' : forall z, locally_closed_tm (gamma' z)).
    { intro z. exact (proj2 (proj1 Hctx' z)). }
    assert (Hvalues : forall z, value (gamma' z)).
    { intro z. exact (proj1 (proj1 Hctx' z)). }
    assert (Hxv : gamma' x = v).
    { unfold gamma'. unfold update_term_substitution. rewrite Nat.eqb_refl. reflexivity. }
    pose proof (semantic_rcontext_add_true theta gamma' RGamma x T v Hctx' Hxv) as Hctx_ext.
    pose proof (semantic_rcontext_formulas theta gamma'
      (update_rcontext RGamma x (R_Refine T Pred_True)) Hctx_ext) as Hform.
    assert (Hsource : qualifier_holds
      (instantiate_formula theta gamma' (open_qualifier_tm ps (tm_fvar x)))).
    { rewrite (instantiate_open_qualifier theta gamma' ps (tm_fvar x) Hg').
      unfold gamma'.
      cbn [instantiate].
      assert (Ex : update_term_substitution gamma x v x = v).
      { unfold update_term_substitution. rewrite Nat.eqb_refl. reflexivity. }
      rewrite Ex.
      rewrite instantiate_formula_update_fresh by exact Hxps. exact Hps. }
    pose proof (entails_sound Delta
      (update_rcontext RGamma x (R_Refine T Pred_True))
      (open_qualifier_tm ps (tm_fvar x))
      (open_qualifier_tm qs (tm_fvar x)) (Hent x HxL)
      theta gamma' Hvalues Hform Hsource) as Htarget.
    change (value v /\
      qualifier_holds (open_qualifier_tm (instantiate_formula theta gamma qs) v)).
    split; [exact Hv|].
    assert (Htarget' : qualifier_holds
      (instantiate_formula theta gamma' (open_qualifier_tm qs (tm_fvar x)))).
    { exact Htarget. }
    rewrite (instantiate_open_qualifier theta gamma' qs (tm_fvar x) Hg') in Htarget'.
    unfold gamma' in Htarget'. cbn [instantiate] in Htarget'.
    assert (Ex : update_term_substitution gamma x v x = v).
    { unfold update_term_substitution. rewrite Nat.eqb_refl. reflexivity. }
    rewrite Ex in Htarget'.
    rewrite instantiate_formula_update_fresh in Htarget' by exact Hxqs.
    exact Htarget'.
  - unfold sem_subtype_prop. intros. simpl in H0. assumption.
  - unfold sem_subtype_prop. intros. simpl. Show.
  - unfold sem_subtype_prop. intros. simpl in H0. Show.
  - unfold sem_subtype_prop. intros. simpl. assumption.
  - unfold sem_subtype_prop. intros. eapply H0; eauto.
Qed.

Theorem never_stuck : forall (t t' : tm) (R : rty),
  has_rtype [] empty_rcontext t R ->
  multi t t' ->
  value t' \/ exists t'' : tm, t' --> t''.
Proof.

Qed.

End SystemFRefinementNonDeterminismRecursionTask.
