From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Arith.Wf_nat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
From Stdlib Require Import ZArith.BinInt.
From Stdlib Require Import ZArith.Znat.

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

Lemma in_le_max_atom : forall x L,
  In x L -> x <= max_atom L.
Proof.
  induction L; simpl; intros.
  - contradiction.
  - destruct H as [H | H].
    + subst. lia.
    + specialize (IHL H). lia.
Qed.

Lemma fresh_notin : forall L,
  ~ In (fresh L) L.
Proof.
  unfold fresh. intros L H.
  pose proof (in_le_max_atom _ _ H). lia.
Qed.

End SystemFRefinementNonDeterminismRecursion.

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
Module SystemFRefinementNonDeterminismRecursionInfrastructure.
Import ListNotations.
Import SystemFRefinementNonDeterminismRecursion.

Fixpoint ftv_context (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (_, T) :: Gamma' => fv_ty T ++ ftv_context Gamma'
  end.

Fixpoint dom_context (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (x, _) :: Gamma' => x :: dom_context Gamma'
  end.

Lemma lookup_context_update_eq : forall Gamma x T,
  lookup_context x <{ x |-> $(T); Gamma }> = Some T.
Proof.
  intros. unfold update. simpl. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma lookup_context_update_neq : forall Gamma x y T,
  x <> y ->
  lookup_context y <{ x |-> $(T); Gamma }> = lookup_context y Gamma.
Proof.
  intros. unfold update. simpl.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. exfalso. apply H. symmetry. exact E.
  - reflexivity.
Qed.

Lemma lc_ty_at_monotone : forall k k' T,
  lc_ty_at k T ->
  k <= k' ->
  lc_ty_at k' T.
Proof.
  intros k k' T Hlc. generalize dependent k'.
  induction Hlc; intros k' Hle.
  - apply lc_ty_bvar. lia.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; eauto.
  - apply lc_ty_all. apply IHHlc. lia.
  - apply lc_ty_int.
Qed.

Lemma lc_tm_at_monotone : forall K k K' k' t,
  lc_tm_at K k t ->
  K <= K' ->
  k <= k' ->
  lc_tm_at K' k' t.
Proof.
  intros K k K' k' t Hlc. generalize dependent K'. generalize dependent k'.
  induction Hlc; intros k' Hk K' HK.
  - apply lc_tm_bvar. lia.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + eapply lc_ty_at_monotone; eauto.
    + apply IHHlc; lia.
  - apply lc_tm_app; eauto.
  - apply lc_tm_tabs. apply IHHlc; lia.
  - apply lc_tm_tapp.
    + apply IHHlc; assumption.
    + eapply lc_ty_at_monotone; eauto.
  - apply lc_tm_int.
  - apply lc_tm_div; eauto.
  - apply lc_tm_arith; eauto.
  - apply lc_tm_fix; eauto using lc_ty_at_monotone; [apply IHHlc1|apply IHHlc2]; lia.
  - apply lc_tm_ifzero; eauto.
  - try (inversion Hlc; subst). apply lc_tm_choice; eauto.
Qed.

Lemma open_ty_rec_lc_at : forall T k U,
  lc_ty_at k T ->
  open_ty_rec k U T = T.
Proof.
  intros T k U Hlc. induction Hlc; simpl; try rewrite ?IHHlc1, ?IHHlc2, ?IHHlc3;
    try reflexivity.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + reflexivity.
  - rewrite IHHlc. reflexivity.
Qed.

Lemma open_tm_rec_lc_at : forall t K k u,
  lc_tm_at K k t ->
  open_tm_rec k u t = t.
Proof.
  intros t K k u Hlc. induction Hlc; simpl;
    try rewrite ?IHHlc, ?IHHlc1, ?IHHlc2, ?IHHlc3; try reflexivity.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + reflexivity.
Qed.

Lemma open_tm_ty_rec_lc_at : forall t K k U,
  lc_tm_at K k t ->
  open_tm_ty_rec K U t = t.
Proof.
  intros t K k U Hlc. induction Hlc; simpl;
    try rewrite ?IHHlc1, ?IHHlc2, ?IHHlc3; try reflexivity.
  - erewrite open_ty_rec_lc_at; eauto. rewrite IHHlc. reflexivity.
  - rewrite IHHlc. reflexivity.
  - rewrite IHHlc. erewrite open_ty_rec_lc_at; eauto.
  - rewrite !open_ty_rec_lc_at by assumption. reflexivity.
Qed.

Lemma lc_ty_at_open_inv : forall T k X,
  lc_ty_at k (open_ty_rec k (Ty_FVar X) T) ->
  lc_ty_at (S k) T.
Proof.
  induction T; intros k X Hlc; simpl in Hlc.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. apply lc_ty_bvar. lia.
    + inversion Hlc; subst. apply lc_ty_bvar. lia.
  - apply lc_ty_fvar.
  - inversion Hlc; subst. apply lc_ty_arrow; eauto.
  - inversion Hlc; subst. apply lc_ty_all. eapply IHT; eauto.
  - apply lc_ty_int.
Qed.

Lemma lc_ty_at_open : forall T k U,
  lc_ty_at (S k) T ->
  lc_ty_at k U ->
  lc_ty_at k (open_ty_rec k U T).
Proof.
  induction T; intros k U HT HU; simpl.
  - inversion HT; subst.
    destruct (Nat.eqb k n) eqn:E.
    + exact HU.
    + apply lc_ty_bvar. apply Nat.eqb_neq in E. lia.
  - apply lc_ty_fvar.
  - inversion HT; subst. apply lc_ty_arrow; eauto.
  - inversion HT; subst. apply lc_ty_all.
    apply IHT.
    + assumption.
    + eapply lc_ty_at_monotone.
      * exact HU.
      * lia.
  - apply lc_ty_int.
Qed.

Lemma lc_tm_at_open_tm_inv : forall t K k x,
  lc_tm_at K k (open_tm_rec k (tm_fvar x) t) ->
  lc_tm_at K (S k) t.
Proof.
  induction t; intros K k x Hlc; simpl in Hlc.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. apply lc_tm_bvar. lia.
    + inversion Hlc; subst. apply lc_tm_bvar. lia.
  - apply lc_tm_fvar.
  - inversion Hlc; subst. apply lc_tm_abs; eauto.
  - inversion Hlc; subst. apply lc_tm_app; eauto.
  - inversion Hlc; subst. apply lc_tm_tabs; eauto.
  - inversion Hlc; subst. apply lc_tm_tapp; eauto.
  - apply lc_tm_int.
  - inversion Hlc; subst. apply lc_tm_div; eauto.
  - inversion Hlc; subst. apply lc_tm_arith; eauto.
  - inversion Hlc; subst. apply lc_tm_fix; eauto.
  - inversion Hlc; subst. apply lc_tm_ifzero; eauto.
  - try (inversion Hlc; subst). apply lc_tm_choice; eauto.
Qed.

Lemma lc_tm_at_open_ty_inv : forall t K k X,
  lc_tm_at K k (open_tm_ty_rec K (Ty_FVar X) t) ->
  lc_tm_at (S K) k t.
Proof.
  induction t; intros K k X Hlc; simpl in Hlc.
  - inversion Hlc; subst. apply lc_tm_bvar. assumption.
  - apply lc_tm_fvar.
  - inversion Hlc; subst. apply lc_tm_abs.
    + eapply lc_ty_at_open_inv; eauto.
    + eapply IHt; eauto.
  - inversion Hlc; subst. apply lc_tm_app; eauto.
  - inversion Hlc; subst. apply lc_tm_tabs. eapply IHt; eauto.
  - inversion Hlc; subst. apply lc_tm_tapp.
    + eapply IHt; eauto.
    + eapply lc_ty_at_open_inv; eauto.
  - apply lc_tm_int.
  - inversion Hlc; subst. apply lc_tm_div; eauto.
  - inversion Hlc; subst. apply lc_tm_arith; eauto.
  - inversion Hlc; subst. apply lc_tm_fix; eauto using lc_ty_at_open_inv.
  - inversion Hlc; subst. apply lc_tm_ifzero; eauto.
  - try (inversion Hlc; subst). apply lc_tm_choice; eauto.
Qed.

Definition type_substitution := atom -> ty.

Definition term_substitution := atom -> tm.

Definition type_subst_update
    (theta : type_substitution) (X : atom) (U : ty) : type_substitution :=
  fun Y => if Nat.eqb X Y then U else theta Y.

Definition term_subst_update
    (gamma : term_substitution) (x : atom) (u : tm) : term_substitution :=
  fun y => if Nat.eqb x y then u else gamma y.

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

Definition type_substitution_closed (theta : type_substitution) : Prop :=
  forall X : atom, locally_closed_ty (theta X).

Definition term_substitution_closed (gamma : term_substitution) : Prop :=
  forall x : atom, locally_closed_tm (gamma x).

Lemma type_subst_update_closed : forall theta X U,
  type_substitution_closed theta ->
  locally_closed_ty U ->
  type_substitution_closed (type_subst_update theta X U).
Proof.
  intros theta X U Htheta HU Y. unfold type_subst_update.
  destruct (Nat.eqb X Y); auto.
Qed.

Lemma term_subst_update_closed : forall gamma x u,
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  term_substitution_closed (term_subst_update gamma x u).
Proof.
  intros gamma x u Hgamma Hu y. unfold term_subst_update.
  destruct (Nat.eqb x y); auto.
Qed.

Definition identity_type_substitution : type_substitution :=
  fun X : atom => Ty_FVar X.

Definition identity_term_substitution : term_substitution :=
  fun x : atom => tm_fvar x.

Lemma identity_type_substitution_closed :
  type_substitution_closed identity_type_substitution.
Proof.
  intros X. apply lc_ty_fvar.
Qed.

Lemma identity_term_substitution_closed :
  term_substitution_closed identity_term_substitution.
Proof.
  intros x. apply lc_tm_fvar.
Qed.

End SystemFRefinementNonDeterminismRecursionInfrastructure.

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
Module SystemFRefinementNonDeterminismRecursionCoreTyping.
Import ListNotations.
Import SystemFRefinementNonDeterminismRecursion.
Import SystemFRefinementNonDeterminismRecursionInfrastructure.

Definition ty_context_included (Delta Delta' : ty_context) : Prop :=
  forall X, In X Delta -> In X Delta'.

Definition context_included (Gamma Gamma' : context) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    lookup_context x Gamma' = Some T.

Definition type_substitution_wf
    (Delta Delta' : ty_context) (theta : type_substitution) : Prop :=
  forall X, In X Delta -> wf_ty Delta' (theta X).

Definition context_wf (Delta : ty_context) (Gamma : context) : Prop :=
  forall x T, lookup_context x Gamma = Some T -> wf_ty Delta T.

Definition term_substitution_typed
    (Gamma : context) (Delta' : ty_context) (Gamma' : context)
    (theta : type_substitution) (gamma : term_substitution) : Prop :=
  forall x T,
    lookup_context x Gamma = Some T ->
    has_type Delta' Gamma' (gamma x) (instantiate_ty theta T).

Lemma notin_dom_lookup_none : forall x Gamma,
  ~ In x (dom_context Gamma) -> lookup_context x Gamma = None.
Proof.
  intros x Gamma. induction Gamma as [|[y T] Gamma IH]; intros Hfresh; simpl in *.
  - reflexivity.
  - assert (Hxy : x <> y) by intuition.
    rewrite (proj2 (Nat.eqb_neq x y)) by assumption.
    apply IH. intuition.
Qed.

End SystemFRefinementNonDeterminismRecursionCoreTyping.

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

Fixpoint close_ty_rec (k : nat) (X : atom) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar Y => if Nat.eqb X Y then Ty_BVar k else Ty_FVar Y
  | Ty_Arrow T1 T2 =>
      Ty_Arrow (close_ty_rec k X T1) (close_ty_rec k X T2)
  | Ty_All T1 => Ty_All (close_ty_rec (S k) X T1)
  | Ty_Int => Ty_Int
  end.

End SystemFRefinementNonDeterminismRecursionTyping.

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Module SystemFRefinementNonDeterminismRecursionEvaluation.
Import ListNotations SystemFRefinementNonDeterminismRecursion SystemFRefinementNonDeterminismRecursionInfrastructure
  SystemFRefinementNonDeterminismRecursionCoreTyping.

Inductive multi : tm -> tm -> Prop :=
  | multi_refl : forall t, multi t t
  | multi_step : forall t1 t2 t3,
      t1 --> t2 -> multi t2 t3 -> multi t1 t3.
Notation "t '-->*' u" := (multi t u) (at level 40).

Definition halts (t : tm) : Prop :=
  exists v, multi t v /\ value v.

Inductive must_terminate : tm -> Prop :=
  | MT_intro : forall t,
      (value t \/ exists u, t --> u) ->
      (forall u, t --> u -> must_terminate u) ->
      must_terminate t.

Lemma open_tm_preserves_lc_at : forall t K k u,
  lc_tm_at K (S k) t -> locally_closed_tm u ->
  lc_tm_at K k (open_tm_rec k u t).
Proof.
  induction t; intros K k u Hlc Hu; simpl; inversion Hlc; subst;
    eauto 8 using lc_tm_at.
  destruct (Nat.eqb k n) eqn:E.
  - eapply lc_tm_at_monotone; [exact Hu|lia|lia].
  - apply Nat.eqb_neq in E. apply lc_tm_bvar. lia.
Qed.

Lemma open_tm_ty_preserves_lc_at : forall t K k U,
  lc_tm_at (S K) k t -> locally_closed_ty U ->
  lc_tm_at K k (open_tm_ty_rec K U t).
Proof.
  induction t; intros K k U Hlc HU; simpl; inversion Hlc; subst;
    eauto 8 using lc_tm_at.
  - apply lc_tm_abs.
    + apply lc_ty_at_open; [assumption|].
      eapply lc_ty_at_monotone; [exact HU|lia].
    + eapply IHt; eauto.
  - apply lc_tm_tapp.
    + eapply IHt; eauto.
    + apply lc_ty_at_open; [assumption|].
      eapply lc_ty_at_monotone; [exact HU|lia].
  - apply lc_tm_fix.
    + apply lc_ty_at_open; [assumption |]. eapply lc_ty_at_monotone; [exact HU | lia].
    + apply lc_ty_at_open; [assumption |]. eapply lc_ty_at_monotone; [exact HU | lia].
    + eapply IHt1; eauto.
    + eapply IHt2; eauto.
Qed.

Lemma value_regular : forall v, value v -> locally_closed_tm v.
Proof. intros v H. destruct H; try assumption; constructor. Qed.

Lemma value_no_step : forall v, value v -> forall t, ~ (v --> t).
Proof. intros v Hv t Hs. destruct Hv; inversion Hs. Qed.

Lemma value_multi_eq : forall v t,
  value v ->
  v -->* t ->
  t = v.
Proof.
  intros v t Hv Hmulti.
  inversion Hmulti; subst.
  - reflexivity.
  - exfalso. eapply value_no_step; eauto.
Qed.

Lemma multi_trans : forall t u v,
  multi t u -> multi u v -> multi t v.
Proof. intros t u v H. induction H; eauto using multi. Qed.

End SystemFRefinementNonDeterminismRecursionEvaluation.

From Stdlib Require Import Arith.PeanoNat Lists.List Lia Program.Wf.
From Equations Require Import Equations.
Module SystemFRefinementNonDeterminismRecursionSubstitution.
Import ListNotations.
Import SystemFRefinementNonDeterminismRecursion.
Import SystemFRefinementNonDeterminismRecursionInfrastructure.
Import SystemFRefinementNonDeterminismRecursionCoreTyping.
Import SystemFRefinementNonDeterminismRecursionTyping.
Import SystemFRefinementNonDeterminismRecursionEvaluation.

Fixpoint fv_pred (p : qualifier) : list atom :=
  match p with
  | Pred_True | Pred_False => []
  | Pred_Eq t1 t2 | Pred_Lt t1 t2 | Pred_Le t1 t2 => fv_tm t1 ++ fv_tm t2
  | Pred_And p1 p2 | Pred_Or p1 p2 => fv_pred p1 ++ fv_pred p2
  | Pred_Not p => fv_pred p
  end.

Definition fv_qualifier := fv_pred.

Fixpoint fv_rty (R : rty) : list atom :=
  match R with
  | R_Refine _ ps => fv_qualifier ps
  | R_Func R1 R2 | R_Exists R1 R2 => fv_rty R1 ++ fv_rty R2
  | R_Poly R1 => fv_rty R1
  end.

Fixpoint ftv_pred (p : qualifier) : list atom :=
  match p with
  | Pred_True | Pred_False => []
  | Pred_Eq t1 t2 | Pred_Lt t1 t2 | Pred_Le t1 t2 => ftv_tm t1 ++ ftv_tm t2
  | Pred_And p1 p2 | Pred_Or p1 p2 => ftv_pred p1 ++ ftv_pred p2
  | Pred_Not p => ftv_pred p
  end.

Definition ftv_qualifier := ftv_pred.

Fixpoint ftv_rty (R : rty) : list atom :=
  match R with
  | R_Refine T ps => fv_ty T ++ ftv_qualifier ps
  | R_Func R1 R2 | R_Exists R1 R2 => ftv_rty R1 ++ ftv_rty R2
  | R_Poly R1 => ftv_rty R1
  end.

Fixpoint fv_rcontext (RGamma : rcontext) : list atom :=
  match RGamma with
  | [] => []
  | (_, R) :: RGamma' => fv_rty R ++ fv_rcontext RGamma'
  end.

Fixpoint ftv_rcontext (RGamma : rcontext) : list atom :=
  match RGamma with
  | [] => []
  | (_, R) :: RGamma' => ftv_rty R ++ ftv_rcontext RGamma'
  end.

Fixpoint instantiate_pred
    (theta : type_substitution) (gamma : term_substitution)
    (p : qualifier) : qualifier :=
  match p with
  | Pred_True => Pred_True
  | Pred_False => Pred_False
  | Pred_Eq t1 t2 =>
      Pred_Eq (instantiate theta gamma t1) (instantiate theta gamma t2)
  | Pred_Lt t1 t2 => Pred_Lt (instantiate theta gamma t1) (instantiate theta gamma t2)
  | Pred_Le t1 t2 => Pred_Le (instantiate theta gamma t1) (instantiate theta gamma t2)
  | Pred_And p1 p2 => Pred_And (instantiate_pred theta gamma p1) (instantiate_pred theta gamma p2)
  | Pred_Not p => Pred_Not (instantiate_pred theta gamma p)
  | Pred_Or p1 p2 =>
      Pred_Or (instantiate_pred theta gamma p1)
        (instantiate_pred theta gamma p2)
  end.

Definition instantiate_qualifier := instantiate_pred.

Fixpoint instantiate_rty
    (theta : type_substitution) (gamma : term_substitution)
    (R : rty) : rty :=
  match R with
  | R_Refine T ps =>
      R_Refine (instantiate_ty theta T) (instantiate_qualifier theta gamma ps)
  | R_Func R1 R2 =>
      R_Func (instantiate_rty theta gamma R1)
        (instantiate_rty theta gamma R2)
  | R_Exists R1 R2 =>
      R_Exists (instantiate_rty theta gamma R1)
        (instantiate_rty theta gamma R2)
  | R_Poly R1 => R_Poly (instantiate_rty theta gamma R1)
  end.

Fixpoint rty_size (R : rty) : nat :=
  match R with
  | R_Refine _ _ => 1
  | R_Func R1 R2 => S (rty_size R1 + rty_size R2)
  | R_Exists R1 R2 => S (rty_size R1 + rty_size R2)
  | R_Poly R1 => S (rty_size R1)
  end.

Scheme has_rtype_mut_ind := Induction for has_rtype Sort Prop
with subtype_mut_ind := Induction for subtype Sort Prop.
Combined Scheme refinement_typing_mutind
  from has_rtype_mut_ind, subtype_mut_ind.
End SystemFRefinementNonDeterminismRecursionSubstitution.

Module SystemFRefinementNonDeterminismRecursionTask.
Import ListNotations SystemFRefinementNonDeterminismRecursion SystemFRefinementNonDeterminismRecursionInfrastructure SystemFRefinementNonDeterminismRecursionCoreTyping SystemFRefinementNonDeterminismRecursionLogic SystemFRefinementNonDeterminismRecursionTyping SystemFRefinementNonDeterminismRecursionEvaluation SystemFRefinementNonDeterminismRecursionSubstitution .

(* The value interpretation records the refinement facts that are needed by
   the primitive operations.  In particular, qualifier_holds uses the
   all-outcomes interpretation of strict inequalities and the existential
   operational interpretation of disequality. *)
Definition computation_safe (t : tm) : Prop :=
  forall u, multi t u -> value u \/ exists u', u --> u'.

Lemma rty_size_open_tm_rec : forall R k v,
  rty_size (open_rty_tm_rec k v R) = rty_size R.
Proof.
  intros R. induction R; intros k v; simpl.
  - reflexivity.
  - rewrite (IHR1 k v), (IHR2 (S k) v). reflexivity.
  - rewrite (IHR1 k v), (IHR2 (S k) v). reflexivity.
  - rewrite (IHR k v). reflexivity.
Qed.

Lemma rty_size_open_ty_rec : forall R k U,
  rty_size (open_rty_ty_rec k U R) = rty_size R.
Proof.
  intros R. induction R; intros k U; simpl.
  - reflexivity.
  - rewrite (IHR1 k U), (IHR2 k U). reflexivity.
  - rewrite (IHR1 k U), (IHR2 k U). reflexivity.
  - rewrite (IHR (S k) U). reflexivity.
Qed.

Fixpoint logical_value_fuel (fuel : nat) (R : rty) (v : tm) : Prop :=
  match fuel with
  | 0 =>
      match R with
      | R_Refine Ty_Int p =>
          value v /\ exists n, v = tm_int n /\
            qualifier_holds (open_qualifier_tm p v)
      | R_Refine _ p => value v /\ qualifier_holds (open_qualifier_tm p v)
      | _ => value v
      end
  | S fuel' =>
      match R with
      | R_Refine Ty_Int p =>
          value v /\ exists n, v = tm_int n /\
            qualifier_holds (open_qualifier_tm p v)
      | R_Refine _ p => value v /\ qualifier_holds (open_qualifier_tm p v)
      | R_Func A B =>
          value v /\ forall w, logical_value_fuel fuel' A w ->
            forall u, multi (tm_app v w) u ->
              (value u /\ logical_value_fuel fuel' (open_rty_tm B w) u) \/
              exists u', u --> u'
      | R_Exists A B =>
          value v /\ exists w, logical_value_fuel fuel' A w /\
            logical_value_fuel fuel' (open_rty_tm B w) v
      | R_Poly B =>
          value v /\ forall U, locally_closed_ty U ->
            forall u, multi (tm_tapp v U) u ->
              (value u /\ logical_value_fuel fuel' (open_rty_ty B U) u) \/
              exists u', u --> u'
      end
  end.

Definition logical_value (R : rty) (v : tm) : Prop :=
  forall fuel, logical_value_fuel fuel R v.

Definition logical_context
    (theta : type_substitution) (gamma : term_substitution)
    (RGamma : rcontext) : Prop :=
  forall x R, lookup_rcontext x RGamma = Some R ->
    logical_value (instantiate_rty theta gamma R) (gamma x).

Definition logical_environment
    (theta : type_substitution) (gamma : term_substitution)
    (RGamma : rcontext) : Prop :=
  (forall x, value (gamma x)) /\
  logical_context theta gamma RGamma /\
  context_formulas_hold theta gamma RGamma.

Definition logical_context_fuel (fuel : nat)
    (theta : type_substitution) (gamma : term_substitution)
    (RGamma : rcontext) : Prop :=
  forall x R, lookup_rcontext x RGamma = Some R ->
    logical_value_fuel fuel (instantiate_rty theta gamma R) (gamma x).

Definition logical_environment_fuel (fuel : nat)
    (theta : type_substitution) (gamma : term_substitution)
    (RGamma : rcontext) : Prop :=
  (forall x, value (gamma x)) /\
  logical_context_fuel fuel theta gamma RGamma /\
  context_formulas_hold theta gamma RGamma.

Fixpoint rcontext_formula_fv (RGamma : rcontext) : list atom :=
  match RGamma with
  | [] => []
  | (x, R) :: RGamma' =>
      match R with
      | R_Refine _ p => fv_qualifier (open_qualifier_tm p (tm_fvar x)) ++ rcontext_formula_fv RGamma'
      | _ => rcontext_formula_fv RGamma'
      end
  end.

Lemma lookup_rcontext_fv : forall RGamma y R a,
  lookup_rcontext y RGamma = Some R -> In a (fv_rty R) -> In a (fv_rcontext RGamma).
Proof.
  induction RGamma as [|[x S] G IH]; intros y R a Hlook Ha; simpl in *.
  - discriminate.
  - simpl in Hlook. destruct (Nat.eqb y x) eqn:E.
    + inversion Hlook; subst. apply in_or_app. left. exact Ha.
    + apply in_or_app. right. eapply IH; eassumption.
Qed.

Lemma lookup_rcontext_formula_fv : forall RGamma y T p a,
  lookup_rcontext y RGamma = Some (R_Refine T p) ->
  In a (fv_qualifier (open_qualifier_tm p (tm_fvar y))) ->
  In a (rcontext_formula_fv RGamma).
Proof.
  induction RGamma as [|[x R] G IH]; intros y T p a Hlook Ha; simpl in *.
  - discriminate.
  - simpl in Hlook. destruct (Nat.eqb y x) eqn:E.
    + apply Nat.eqb_eq in E. subst y. inversion Hlook; subst R. simpl. apply in_or_app. left. exact Ha.
    + destruct R; simpl; try (eapply IH; eassumption).
      simpl. apply in_or_app. right. eapply IH; eassumption.
Qed.

Lemma logical_value_is_value : forall R v,
  logical_value R v -> value v.
Proof.
  intros R v H. specialize (H 0). destruct R as [T p|A B|A B|B]; simpl in H; try tauto.
  destruct T; simpl in H; tauto.
Qed.

Lemma logical_value_refinement : forall T p v,
  logical_value (R_Refine T p) v ->
  qualifier_holds (open_qualifier_tm p v).
Proof.
  intros T p v H. specialize (H 1). destruct T; simpl in H;
    try (destruct H as [_ Hq]; exact Hq).
  destruct H as [_ [n [_ Hq]]]. exact Hq.
Qed.

Lemma logical_value_fuel_refinement : forall fuel T p v,
  logical_value_fuel fuel (R_Refine T p) v ->
  qualifier_holds (open_qualifier_tm p v).
Proof.
  intros fuel T p v H. destruct T; destruct fuel; simpl in H; firstorder.
Qed.

Lemma logical_value_fuel_is_value : forall fuel R v,
  logical_value_fuel fuel R v -> value v.
Proof.
  intros fuel R v H. destruct fuel; simpl in H.
  - destruct R as [T p|A B|A B|B]; simpl in H; try tauto.
    destruct T; simpl in H; tauto.
  - destruct R as [T p|A B|A B|B]; simpl in H; try tauto.
    destruct T; simpl in H; tauto.
Qed.

Definition logical_computation_fuel (fuel : nat) (R : rty) (t : tm) : Prop :=
  forall u, multi t u ->
    (value u /\ logical_value_fuel fuel R u) \/ exists u', u --> u'.

Lemma logical_value_function_result : forall A B f w,
  logical_value (R_Func A B) f -> logical_value A w ->
  forall fuel u, multi (tm_app f w) u ->
    (value u /\ logical_value_fuel fuel (open_rty_tm B w) u) \/ exists u', u --> u'.
Proof.
  intros A B f w Hf Hw fuel u Hu.
  specialize (Hf (S fuel)). simpl in Hf. destruct Hf as [_ Hsafe].
  specialize (Hsafe w (Hw fuel) u Hu). exact Hsafe.
Qed.

Lemma multi_app_abs_decompose : forall T body w u,
  locally_closed_tm (tm_abs T body) -> value w ->
  multi (tm_app (tm_abs T body) w) u ->
  u = tm_app (tm_abs T body) w \/ multi (open_tm body w) u.
Proof.
  intros T body w u Habs Hw Hmulti. inversion Hmulti; subst.
  - left. reflexivity.
  - inversion H; subst.
    + right. assumption.
    + exfalso. eapply value_no_step; [apply v_abs; exact Habs|eassumption].
    + exfalso. eapply value_no_step with (v:=w) (t:=t2'); eassumption.
Qed.

Lemma logical_abs_application : forall T body A B fuel,
  locally_closed_tm (tm_abs T body) ->
  (forall w, logical_value_fuel fuel A w ->
    logical_computation_fuel fuel (open_rty_tm B w) (open_tm body w)) ->
  logical_value_fuel (S fuel) (R_Func A B) (tm_abs T body).
Proof.
  intros T body A B fuel Habs Hbody. simpl. split.
  - apply v_abs. exact Habs.
  - intros w Hw u Hmulti.
    destruct (multi_app_abs_decompose T body w u Habs
      (logical_value_fuel_is_value fuel A w Hw) Hmulti) as [->|Hbodymulti].
    + right. eexists. eapply ST_AppAbs; [exact Habs|].
      exact (logical_value_fuel_is_value fuel A w Hw).
    + exact (Hbody w Hw u Hbodymulti).
Qed.

Lemma multi_tapp_tabs_decompose : forall body U u,
  locally_closed_tm (tm_tabs body) -> locally_closed_ty U ->
  multi (tm_tapp (tm_tabs body) U) u ->
  u = tm_tapp (tm_tabs body) U \/ multi (open_tm_ty body U) u.
Proof.
  intros body U u Htabs HU Hmulti. inversion Hmulti; subst.
  - left. reflexivity.
  - inversion H; subst.
    + right. assumption.
    + exfalso. eapply value_no_step; [apply v_tabs; exact Htabs|eassumption].
Qed.

Lemma logical_tabs_application : forall body B fuel,
  locally_closed_tm (tm_tabs body) ->
  (forall U, locally_closed_ty U ->
    logical_computation_fuel fuel (open_rty_ty B U) (open_tm_ty body U)) ->
  logical_value_fuel (S fuel) (R_Poly B) (tm_tabs body).
Proof.
  intros body B fuel Htabs Hbody. simpl. split.
  - apply v_tabs. exact Htabs.
  - intros U HU u Hmulti.
    destruct (multi_tapp_tabs_decompose body U u Htabs HU Hmulti) as [->|Hbodymulti].
    + right. eexists. eapply ST_TAppTabs; eauto.
    + exact (Hbody U HU u Hbodymulti).
Qed.

Lemma logical_application : forall A B f w,
  logical_value (R_Func A B) f -> logical_value A w ->
  forall fuel, logical_computation_fuel fuel (R_Exists A B) (tm_app f w).
Proof.
  intros A B f w Hf Hw fuel u Hu.
  destruct fuel as [|fuel].
  - destruct (logical_value_function_result A B f w Hf Hw 0 u Hu)
      as [[Hvalue _]|Hstep].
    + left. split; [exact Hvalue|]. simpl. exact Hvalue.
    + right. exact Hstep.
  - destruct (logical_value_function_result A B f w Hf Hw fuel u Hu)
      as [[Hvalue Hbody]|Hstep].
    + left. split; [exact Hvalue|]. simpl. split; [exact Hvalue|].
      exists w. split; [apply Hw|exact Hbody].
    + right. exact Hstep.
Qed.

Lemma logical_choice : forall fuel R t1 t2,
  locally_closed_tm t1 -> locally_closed_tm t2 ->
  logical_computation_fuel fuel R t1 ->
  logical_computation_fuel fuel R t2 ->
  logical_computation_fuel fuel R (tm_choice t1 t2).
Proof.
  intros fuel R t1 t2 Hlc1 Hlc2 Hleft Hright u Hmulti.
  inversion Hmulti; subst.
  - right. eexists. eapply ST_ChoiceLeft; assumption.
  - inversion H; subst.
    + eapply Hleft. assumption.
    + eapply Hright. assumption.
Qed.

Lemma multi_app_left : forall t t' a,
  locally_closed_tm a -> multi t t' ->
  multi (tm_app t a) (tm_app t' a).
Proof.
  intros t t' a Hlc Hmulti. induction Hmulti.
  - constructor.
  - eapply multi_step; [eapply ST_App1; eauto|exact IHHmulti].
Qed.

Lemma multi_app_right : forall v t t',
  value v -> multi t t' -> multi (tm_app v t) (tm_app v t').
Proof.
  intros v t t' Hv Hmulti. induction Hmulti.
  - constructor.
  - eapply multi_step; [eapply ST_App2; eauto|exact IHHmulti].
Qed.

Lemma multi_div_left : forall t t' a,
  locally_closed_tm a -> multi t t' -> multi (tm_div t a) (tm_div t' a).
Proof.
  intros t t' a Hlc Hmulti. induction Hmulti.
  - constructor.
  - eapply multi_step; [eapply ST_Div1; eauto|exact IHHmulti].
Qed.

Lemma multi_div_right : forall v t t',
  value v -> multi t t' -> multi (tm_div v t) (tm_div v t').
Proof.
  intros v t t' Hv Hmulti. induction Hmulti.
  - constructor.
  - eapply multi_step; [eapply ST_Div2; eauto|exact IHHmulti].
Qed.

Lemma multi_tapp : forall t t' U,
  locally_closed_ty U -> multi t t' ->
  multi (tm_tapp t U) (tm_tapp t' U).
Proof.
  intros t t' U HU Hmulti. induction Hmulti.
  - constructor.
  - eapply multi_step; [eapply ST_TApp; eauto|exact IHHmulti].
Qed.

Lemma multi_arith_left : forall op t t' a,
  locally_closed_tm a -> multi t t' ->
  multi (tm_arith op t a) (tm_arith op t' a).
Proof.
  intros op t t' a Hlc Hmulti. induction Hmulti.
  - constructor.
  - eapply multi_step; [eapply ST_Arith1; eauto|exact IHHmulti].
Qed.

Lemma multi_arith_right : forall op v t t',
  value v -> multi t t' -> multi (tm_arith op v t) (tm_arith op v t').
Proof.
  intros op v t t' Hv Hmulti. induction Hmulti.
  - constructor.
  - eapply multi_step; [eapply ST_Arith2; eauto|exact IHHmulti].
Qed.

Lemma multi_ifzero_arg : forall t t' t0 t1,
  locally_closed_tm t0 -> locally_closed_tm t1 -> multi t t' ->
  multi (tm_ifzero t t0 t1) (tm_ifzero t' t0 t1).
Proof.
  intros t t' t0 t1 H0 H1 Hmulti. induction Hmulti.
  - constructor.
  - eapply multi_step; [eapply ST_IfZeroArg; eauto|exact IHHmulti].
Qed.

Lemma multi_choice_cases : forall t1 t2 u,
  locally_closed_tm t1 -> locally_closed_tm t2 ->
  multi (tm_choice t1 t2) u ->
  u = tm_choice t1 t2 \/ multi t1 u \/ multi t2 u.
Proof.
  intros t1 t2 u Hlc1 Hlc2 Hmulti. inversion Hmulti; subst.
  - left. reflexivity.
  - inversion H; subst.
    + right; left; assumption.
    + right; right; assumption.
Qed.

Lemma logical_value_exists_elim : forall A B v,
  logical_value (R_Exists A B) v ->
  forall fuel, exists w,
    logical_value_fuel fuel A w /\
    logical_value_fuel fuel (open_rty_tm B w) v.
Proof.
  intros A B v H fuel. specialize (H (S fuel)).
  simpl in H. destruct H as [_ [w [Hw Hbody]]].
  exists w. split; assumption.
Qed.

Lemma logical_value_poly_elim : forall B v U,
  logical_value (R_Poly B) v -> locally_closed_ty U ->
  forall fuel u, multi (tm_tapp v U) u ->
    (value u /\ logical_value_fuel fuel (open_rty_ty B U) u) \/ exists u', u --> u'.
Proof.
  intros B v U H HU fuel u Hu. specialize (H (S fuel)). simpl in H.
  destruct H as [_ Hpoly]. eapply Hpoly; eassumption.
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
    intros theta gamma Hvalues Hctx Hp;
    cbn [qualifier_holds predicate_holds interpret_qualifier instantiate_formula] in *.
  - exact Hp.
  - exact I.
  - apply (IHHent2 theta gamma Hvalues Hctx).
    apply (IHHent1 theta gamma Hvalues Hctx). exact Hp.
  - destruct Hp as [Hp _]. exact Hp.
  - destruct Hp as [_ Hq]. exact Hq.
  - split.
    + eapply IHHent1; eauto.
    + eapply IHHent2; eauto.
  - left. exact Hp.
  - right. exact Hp.
  - destruct Hp as [Hp | Hq].
    + eapply IHHent1; eauto.
    + eapply IHHent2; eauto.
  - intros Hq. apply (IHHent theta gamma Hvalues Hctx).
    split; assumption.
  - destruct Hp as [Hpp Hnot]. apply Hnot. exact Hpp.
  - apply (Hctx x T p H).
  - contradiction.
  - eapply H; eauto.
Qed.

Definition logical_computation (R : rty) (t : tm) : Prop :=
  forall u, multi t u ->
    (value u /\ logical_value R u) \/ exists u', u --> u'.

Lemma logical_value_computation_fuel : forall R v,
  logical_value R v -> forall fuel, logical_computation_fuel fuel R v.
Proof.
  intros R v Hv fuel u Hmulti.
  assert (Hu : u = v) by (eapply value_multi_eq; [eapply logical_value_is_value; exact Hv|exact Hmulti]).
  subst u. left. split; [eapply logical_value_is_value; exact Hv|apply Hv].
Qed.

Lemma logical_value_fuel_computation : forall fuel R v,
  logical_value_fuel fuel R v -> logical_computation_fuel fuel R v.
Proof.
  intros fuel R v Hlv u Hu.
  assert (E : u = v) by (eapply value_multi_eq; [eapply logical_value_fuel_is_value; exact Hlv|exact Hu]).
  subst u. left. split; [eapply logical_value_fuel_is_value; exact Hlv|exact Hlv].
Qed.

Lemma open_tm_rec_lc_identity : forall t K d k u,
  lc_tm_at K d t -> open_tm_rec (k + d) u t = t.
Proof.
  induction t; intros K d k u Hlc; simpl; inversion Hlc; subst.
  - destruct (Nat.eqb (k + d) n) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + reflexivity.
  - reflexivity.
  - f_equal. replace (S (k + d)) with (k + S d) by lia.
    eapply IHt. exact H4.
  - f_equal; eauto.
  - f_equal. eapply IHt. eassumption.
  - f_equal. eapply IHt. eassumption.
  - reflexivity.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal.
    + replace (S (k + d)) with (k + S d) by lia. eapply IHt1; eassumption.
    + replace (S (S (k + d))) with (k + S (S d)) by lia. eapply IHt2; eassumption.
  - f_equal; eauto.
  - f_equal; eauto.
Qed.

Lemma instantiate_open_tm_rec : forall t k theta gamma x v,
  ~ In x (fv_tm t) ->
  term_substitution_closed gamma ->
  instantiate theta (term_subst_update gamma x v) (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k v (instantiate theta gamma t).
Proof.
  induction t; intros k theta gamma x v Hfresh Hgamma; simpl in *.
  - destruct (Nat.eqb k n) eqn:E; simpl.
    + unfold term_subst_update. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply Hfresh. simpl. auto.
    + unfold term_subst_update. rewrite E.
      replace (open_tm_rec k v (gamma a)) with (gamma a).
      * reflexivity.
      * pose proof (open_tm_rec_lc_identity (gamma a) 0 0 k v (Hgamma a)) as Hopen.
        rewrite Nat.add_0_r in Hopen. symmetry. exact Hopen.
  - f_equal. eapply IHt; [exact Hfresh|exact Hgamma].
  - f_equal.
    + eapply IHt1; [intro Hin; apply Hfresh; simpl; apply in_or_app; left; exact Hin|exact Hgamma].
    + eapply IHt2; [intro Hin; apply Hfresh; simpl; apply in_or_app; right; exact Hin|exact Hgamma].
  - f_equal. eapply IHt; [exact Hfresh|exact Hgamma].
  - f_equal. eapply IHt; [exact Hfresh|exact Hgamma].
  - reflexivity.
  - f_equal.
    + eapply IHt1; [intro Hin; apply Hfresh; simpl; apply in_or_app; left; exact Hin|exact Hgamma].
    + eapply IHt2; [intro Hin; apply Hfresh; simpl; apply in_or_app; right; exact Hin|exact Hgamma].
  - f_equal.
    + eapply IHt1; [intro Hin; apply Hfresh; simpl; apply in_or_app; left; exact Hin|exact Hgamma].
    + eapply IHt2; [intro Hin; apply Hfresh; simpl; apply in_or_app; right; exact Hin|exact Hgamma].
  - f_equal.
    + eapply IHt1; [intro Hin; apply Hfresh; simpl; apply in_or_app; left; exact Hin|exact Hgamma].
    + eapply IHt2; [intro Hin; apply Hfresh; simpl; apply in_or_app; right; exact Hin|exact Hgamma].
  - f_equal.
    + eapply IHt1; [intro Hin; apply Hfresh; simpl; repeat rewrite in_app_iff; tauto|exact Hgamma].
    + eapply IHt2; [intro Hin; apply Hfresh; simpl; repeat rewrite in_app_iff; tauto|exact Hgamma].
    + eapply IHt3; [intro Hin; apply Hfresh; simpl; repeat rewrite in_app_iff; tauto|exact Hgamma].
  - f_equal.
    + eapply IHt1; [intro Hin; apply Hfresh; simpl; apply in_or_app; left; exact Hin|exact Hgamma].
    + eapply IHt2; [intro Hin; apply Hfresh; simpl; apply in_or_app; right; exact Hin|exact Hgamma].
Qed.

Lemma instantiate_open_qualifier_rec : forall p k theta gamma x v,
  ~ In x (fv_qualifier p) -> term_substitution_closed gamma ->
  instantiate_formula theta (term_subst_update gamma x v)
      (open_qualifier_tm_rec k (tm_fvar x) p) =
  open_qualifier_tm_rec k v (instantiate_formula theta gamma p).
Proof.
  induction p; intros k theta gamma x v Hfresh Hgamma; simpl in *; try reflexivity.
  - f_equal.
    + eapply instantiate_open_tm_rec; [intro Hin; apply Hfresh; simpl; apply in_or_app; left; exact Hin|exact Hgamma].
    + eapply instantiate_open_tm_rec; [intro Hin; apply Hfresh; simpl; apply in_or_app; right; exact Hin|exact Hgamma].
  - f_equal.
    + eapply instantiate_open_tm_rec; [intro Hin; apply Hfresh; simpl; apply in_or_app; left; exact Hin|exact Hgamma].
    + eapply instantiate_open_tm_rec; [intro Hin; apply Hfresh; simpl; apply in_or_app; right; exact Hin|exact Hgamma].
  - f_equal.
    + eapply instantiate_open_tm_rec; [intro Hin; apply Hfresh; simpl; apply in_or_app; left; exact Hin|exact Hgamma].
    + eapply instantiate_open_tm_rec; [intro Hin; apply Hfresh; simpl; apply in_or_app; right; exact Hin|exact Hgamma].
  - f_equal.
    + eapply IHp1; [intro Hin; apply Hfresh; simpl; apply in_or_app; left; exact Hin|exact Hgamma].
    + eapply IHp2; [intro Hin; apply Hfresh; simpl; apply in_or_app; right; exact Hin|exact Hgamma].
  - f_equal.
    + eapply IHp1; [intro Hin; apply Hfresh; simpl; apply in_or_app; left; exact Hin|exact Hgamma].
    + eapply IHp2; [intro Hin; apply Hfresh; simpl; apply in_or_app; right; exact Hin|exact Hgamma].
  - f_equal. eapply IHp. exact Hfresh. exact Hgamma.
Qed.

Lemma instantiate_open_rty_tm_rec : forall R k theta gamma x v,
  ~ In x (fv_rty R) -> term_substitution_closed gamma ->
  instantiate_rty theta (term_subst_update gamma x v)
      (open_rty_tm_rec k (tm_fvar x) R) =
  open_rty_tm_rec k v (instantiate_rty theta gamma R).
Proof.
  induction R; intros k theta gamma x v Hfresh Hgamma; simpl in *.
  - f_equal. eapply instantiate_open_qualifier_rec; eauto.
  - f_equal.
    + eapply IHR1; [intro Hin; apply Hfresh; simpl; apply in_or_app; left; exact Hin|exact Hgamma].
    + eapply IHR2; [intro Hin; apply Hfresh; simpl; apply in_or_app; right; exact Hin|exact Hgamma].
  - f_equal.
    + eapply IHR1; [intro Hin; apply Hfresh; simpl; apply in_or_app; left; exact Hin|exact Hgamma].
    + eapply IHR2; [intro Hin; apply Hfresh; simpl; apply in_or_app; right; exact Hin|exact Hgamma].
  - f_equal. eapply IHR. exact Hfresh. exact Hgamma.
Qed.

Lemma instantiate_tm_irrelevant : forall t theta gamma x v,
  ~ In x (fv_tm t) ->
  instantiate theta (term_subst_update gamma x v) t = instantiate theta gamma t.
Proof.
  induction t; intros theta gamma x v Hfresh; simpl in *; try reflexivity.
  - destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply Hfresh. simpl; auto.
    + unfold term_subst_update. rewrite E. reflexivity.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal.
    + apply IHt1. intro Hin. apply Hfresh. simpl. apply in_or_app; left; exact Hin.
    + apply IHt2. intro Hin. apply Hfresh. simpl. apply in_or_app; right; exact Hin.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal.
    + apply IHt1. intro Hin. apply Hfresh. simpl. apply in_or_app; left; exact Hin.
    + apply IHt2. intro Hin. apply Hfresh. simpl. apply in_or_app; right; exact Hin.
  - f_equal.
    + apply IHt1. intro Hin. apply Hfresh. simpl. apply in_or_app; left; exact Hin.
    + apply IHt2. intro Hin. apply Hfresh. simpl. apply in_or_app; right; exact Hin.
  - f_equal.
    + apply IHt1. intro Hin. apply Hfresh. simpl. apply in_or_app; left; exact Hin.
    + apply IHt2. intro Hin. apply Hfresh. simpl. apply in_or_app; right; exact Hin.
  - f_equal.
    + apply IHt1. intro Hin. apply Hfresh. simpl. repeat rewrite in_app_iff; tauto.
    + apply IHt2. intro Hin. apply Hfresh. simpl. repeat rewrite in_app_iff; tauto.
    + apply IHt3. intro Hin. apply Hfresh. simpl. repeat rewrite in_app_iff; tauto.
  - f_equal.
    + apply IHt1. intro Hin. apply Hfresh. simpl. repeat rewrite in_app_iff; tauto.
    + apply IHt2. intro Hin. apply Hfresh. simpl. repeat rewrite in_app_iff; tauto.
Qed.

Lemma instantiate_qualifier_irrelevant : forall p theta gamma x v,
  ~ In x (fv_qualifier p) ->
  instantiate_formula theta (term_subst_update gamma x v) p =
  instantiate_formula theta gamma p.
Proof.
  induction p; intros theta gamma x v Hfresh; simpl in *; try reflexivity.
  - f_equal.
    + apply instantiate_tm_irrelevant. intro Hin. apply Hfresh. simpl; apply in_or_app; left; exact Hin.
    + apply instantiate_tm_irrelevant. intro Hin. apply Hfresh. simpl; apply in_or_app; right; exact Hin.
  - f_equal.
    + apply instantiate_tm_irrelevant. intro Hin. apply Hfresh. simpl; apply in_or_app; left; exact Hin.
    + apply instantiate_tm_irrelevant. intro Hin. apply Hfresh. simpl; apply in_or_app; right; exact Hin.
  - f_equal.
    + apply instantiate_tm_irrelevant. intro Hin. apply Hfresh. simpl; apply in_or_app; left; exact Hin.
    + apply instantiate_tm_irrelevant. intro Hin. apply Hfresh. simpl; apply in_or_app; right; exact Hin.
  - f_equal.
    + apply IHp1. intro Hin. apply Hfresh. simpl; apply in_or_app; left; exact Hin.
    + apply IHp2. intro Hin. apply Hfresh. simpl; apply in_or_app; right; exact Hin.
  - f_equal.
    + apply IHp1. intro Hin. apply Hfresh. simpl; apply in_or_app; left; exact Hin.
    + apply IHp2. intro Hin. apply Hfresh. simpl; apply in_or_app; right; exact Hin.
  - f_equal. apply IHp. exact Hfresh.
Qed.

Lemma instantiate_rty_irrelevant : forall R theta gamma x v,
  ~ In x (fv_rty R) ->
  instantiate_rty theta (term_subst_update gamma x v) R =
  instantiate_rty theta gamma R.
Proof.
  induction R; intros theta gamma x v Hfresh; simpl in *.
  - f_equal. apply instantiate_qualifier_irrelevant. exact Hfresh.
  - f_equal.
    + apply IHR1. intro Hin. apply Hfresh. simpl; apply in_or_app; left; exact Hin.
    + apply IHR2. intro Hin. apply Hfresh. simpl; apply in_or_app; right; exact Hin.
  - f_equal.
    + apply IHR1. intro Hin. apply Hfresh. simpl; apply in_or_app; left; exact Hin.
    + apply IHR2. intro Hin. apply Hfresh. simpl; apply in_or_app; right; exact Hin.
  - f_equal. apply IHR. exact Hfresh.
Qed.

Lemma logical_context_extend : forall theta gamma RGamma x R v,
  logical_context theta gamma RGamma ->
  logical_value (instantiate_rty theta gamma R) v ->
  (forall y S, lookup_rcontext y RGamma = Some S -> ~ In x (fv_rty S)) ->
  ~ In x (fv_rty R) ->
  logical_context theta (term_subst_update gamma x v)
    (update_rcontext RGamma x R).
Proof.
  intros theta gamma RGamma x R v Hctx Hval HfreshG HfreshR y S Hlook.
  unfold logical_context in Hctx |- *.
  unfold update_rcontext in Hlook. simpl in Hlook.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst y. inversion Hlook; subst S.
    rewrite (instantiate_rty_irrelevant R theta gamma x v HfreshR).
    unfold term_subst_update. rewrite Nat.eqb_refl. exact Hval.
  - apply Nat.eqb_neq in E.
    rewrite (instantiate_rty_irrelevant S theta gamma x v (HfreshG y S Hlook)).
    unfold term_subst_update. assert (Nat.eqb x y = false) as Hxy.
    { apply Nat.eqb_neq. congruence. }
    rewrite Hxy. apply Hctx with (x:=y) (R:=S). exact Hlook.
Qed.

Lemma logical_environment_extend : forall theta gamma RGamma x R v,
  logical_environment theta gamma RGamma ->
  logical_value (instantiate_rty theta gamma R) v -> value v ->
  (forall y S, lookup_rcontext y RGamma = Some S -> ~ In x (fv_rty S)) ->
  ~ In x (fv_rty R) ->
  (forall y T p, lookup_rcontext y RGamma = Some (R_Refine T p) ->
     ~ In x (fv_qualifier (open_qualifier_tm p (tm_fvar y)))) ->
  logical_environment theta (term_subst_update gamma x v)
    (update_rcontext RGamma x R).
Proof.
  intros theta gamma RGamma x R v [Hvalues [Hctx Hforms]] Hval Hv HfreshG HfreshR HfreshQ.
  assert (Hgamma : term_substitution_closed gamma).
  { intro y. apply value_regular. apply Hvalues. }
  split.
  - intro y. unfold term_subst_update. destruct (Nat.eqb x y); auto.
  - split.
    + eapply logical_context_extend; eauto.
    + intros y T p Hlook. unfold update_rcontext in Hlook. simpl in Hlook.
      destruct (Nat.eqb y x) eqn:E.
      * apply Nat.eqb_eq in E. subst y. inversion Hlook; subst.
        simpl in Hval |- *.
        change (qualifier_holds (instantiate_formula theta (term_subst_update gamma x v)
          (open_qualifier_tm_rec 0 (tm_fvar x) p))).
        rewrite (instantiate_open_qualifier_rec p 0 theta gamma x v HfreshR Hgamma).
        change (qualifier_holds (open_qualifier_tm (instantiate_qualifier theta gamma p) v)).
        eapply logical_value_refinement. exact Hval.
      * apply Nat.eqb_neq in E. specialize (Hforms y T p Hlook).
        rewrite (instantiate_qualifier_irrelevant
          (open_qualifier_tm p (tm_fvar y)) theta gamma x v (HfreshQ y T p Hlook)).
        exact Hforms.
Qed.

Lemma logical_environment_fuel_extend : forall fuel theta gamma RGamma x R v,
  logical_environment_fuel fuel theta gamma RGamma ->
  logical_value_fuel fuel (instantiate_rty theta gamma R) v -> value v ->
  (forall y S, lookup_rcontext y RGamma = Some S -> ~ In x (fv_rty S)) ->
  ~ In x (fv_rty R) ->
  (forall y T p, lookup_rcontext y RGamma = Some (R_Refine T p) ->
     ~ In x (fv_qualifier (open_qualifier_tm p (tm_fvar y)))) ->
  logical_environment_fuel fuel theta (term_subst_update gamma x v)
    (update_rcontext RGamma x R).
Proof.
  intros fuel theta gamma RGamma x R v [Hvalues [Hctx Hforms]] Hval Hv HfreshG HfreshR HfreshQ.
  assert (Hgamma : term_substitution_closed gamma).
  { intro y. apply value_regular. apply Hvalues. }
  split.
  - intro y. unfold term_subst_update. destruct (Nat.eqb x y); auto.
  - split.
    + intros y S Hlook. unfold update_rcontext in Hlook. simpl in Hlook.
      destruct (Nat.eqb y x) eqn:E.
      * apply Nat.eqb_eq in E. subst y. inversion Hlook; subst S.
        rewrite (instantiate_rty_irrelevant R theta gamma x v HfreshR).
        unfold term_subst_update. rewrite Nat.eqb_refl. exact Hval.
      * apply Nat.eqb_neq in E.
        rewrite (instantiate_rty_irrelevant S theta gamma x v (HfreshG y S Hlook)).
        unfold term_subst_update. assert (Nat.eqb x y = false) as Hxy.
        { apply Nat.eqb_neq. congruence. }
        rewrite Hxy. apply Hctx with (x:=y) (R:=S). exact Hlook.
    + intros y T p Hlook. unfold update_rcontext in Hlook. simpl in Hlook.
      destruct (Nat.eqb y x) eqn:E.
      * apply Nat.eqb_eq in E. subst y. inversion Hlook; subst.
        change (qualifier_holds (instantiate_formula theta (term_subst_update gamma x v)
          (open_qualifier_tm_rec 0 (tm_fvar x) p))).
        rewrite (instantiate_open_qualifier_rec p 0 theta gamma x v HfreshR Hgamma).
        change (qualifier_holds (open_qualifier_tm (instantiate_qualifier theta gamma p) v)).
        eapply logical_value_fuel_refinement. exact Hval.
      * specialize (Hforms y T p Hlook).
        rewrite (instantiate_qualifier_irrelevant
          (open_qualifier_tm p (tm_fvar y)) theta gamma x v (HfreshQ y T p Hlook)).
        exact Hforms.
Qed.

Lemma logical_computation_safe : forall R t,
  logical_computation R t -> computation_safe t.
Proof.
  intros R t H u Hu. specialize (H u Hu). destruct H as [[Hv _]|Hs]; auto.
Qed.

Lemma logical_computation_fuel_zero_safe : forall R t,
  logical_computation_fuel 0 R t -> computation_safe t.
Proof.
  intros R t H u Hu. specialize (H u Hu). destruct H as [[Hv _]|Hs]; auto.
Qed.

Lemma logical_computation_fuel_endpoint : forall fuel R t u,
  logical_computation_fuel fuel R t -> multi t u ->
  value u \/ exists u', u --> u'.
Proof.
  intros fuel R t u Hsafe Hmulti. specialize (Hsafe u Hmulti).
  destruct Hsafe as [[Hv _]|Hs]; auto.
Qed.

Lemma fundamental_integer : forall n fuel,
  logical_computation_fuel fuel
    (R_Refine Ty_Int (Pred_Eq (tm_bvar 0) (tm_int n))) (tm_int n).
Proof.
  intros n fuel u Hu.
  assert (E : u = tm_int n).
  { eapply value_multi_eq; [apply v_int|exact Hu]. }
  subst u. left. split; [apply v_int|].
  destruct fuel as [|fuel]; simpl.
  - split; [apply v_int|]. exists n. split; [reflexivity|].
    unfold qualifier_holds, predicate_holds, operational_atoms, interpret_qualifier.
    simpl. exists (tm_int n). repeat split; try constructor; apply v_int.
  - split; [apply v_int|]. exists n. split; [reflexivity|].
    unfold qualifier_holds, predicate_holds, operational_atoms, interpret_qualifier.
    simpl. exists (tm_int n). repeat split; try constructor; apply v_int.
Qed.

Lemma fundamental_variable : forall RGamma x R theta gamma,
  lookup_rcontext x RGamma = Some R ->
  logical_environment theta gamma RGamma ->
  forall fuel,
    logical_computation_fuel fuel
      (instantiate_rty theta gamma R) (instantiate theta gamma (tm_fvar x)).
Proof.
  intros RGamma x R theta gamma Hlook Henv fuel.
  destruct Henv as [_ [Hctx _]]. simpl. eapply logical_value_computation_fuel.
  eapply Hctx. exact Hlook.
Qed.

Lemma fundamental_variable_fuel : forall fuel RGamma x R theta gamma,
  lookup_rcontext x RGamma = Some R ->
  logical_environment_fuel fuel theta gamma RGamma ->
  logical_computation_fuel fuel (instantiate_rty theta gamma R)
    (instantiate theta gamma (tm_fvar x)).
Proof.
  intros fuel RGamma x R theta gamma Hlook [_ [Hctx _]]. simpl.
  pose proof (Hctx x R Hlook) as Hlv.
  intros u Hu. assert (E : u = gamma x).
  { eapply value_multi_eq; [eapply logical_value_fuel_is_value; exact Hlv|exact Hu]. }
  subst u. left. split; [eapply logical_value_fuel_is_value; exact Hlv|exact Hlv].
Qed.

Lemma wf_ty_locally_closed : forall Delta T,
  wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T Hwf. induction Hwf.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; assumption.
  - apply lc_ty_all. apply lc_ty_at_open_inv with (X := fresh L).
    apply H0. apply fresh_notin.
  - apply lc_ty_int.
Qed.

Lemma has_type_locally_closed : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T Hty. induction Hty.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + apply (wf_ty_locally_closed Delta T1). assumption.
    + apply lc_tm_at_open_tm_inv with (x := fresh L).
      apply H1. apply fresh_notin.
  - apply lc_tm_app; assumption.
  - apply lc_tm_tabs. apply lc_tm_at_open_ty_inv with (X := fresh L).
    apply H0. apply fresh_notin.
  - apply lc_tm_tapp.
    + assumption.
    + apply (wf_ty_locally_closed Delta U). assumption.
  - apply lc_tm_int.
  - apply lc_tm_div; assumption.
  - apply lc_tm_arith; assumption.
  - apply lc_tm_fix.
    + apply (wf_ty_locally_closed Delta A). assumption.
    + apply (wf_ty_locally_closed Delta B). assumption.
    + apply lc_tm_at_open_tm_inv with (x := fresh L).
      apply H2. apply fresh_notin.
    + apply lc_tm_at_open_tm_inv with (x := fresh (fresh L :: L)).
      apply lc_tm_at_open_tm_inv with (x := fresh L).
      apply (H4 (fresh (fresh L :: L)) (fresh L)).
      * intro Hin. apply (fresh_notin (fresh L :: L)). simpl. right. exact Hin.
      * simpl. intro Hin. destruct Hin as [Heq | Hin].
        -- apply (fresh_notin (fresh L :: L)). simpl. left. symmetry. exact Heq.
        -- apply (fresh_notin L). exact Hin.
  - apply lc_tm_ifzero; assumption.
  - apply lc_tm_choice; assumption.
Qed.

Lemma instantiate_ty_locally_closed : forall theta K T,
  type_substitution_closed theta -> lc_ty_at K T ->
  lc_ty_at K (instantiate_ty theta T).
Proof.
  intros theta K T Htheta Hlc. induction Hlc; simpl.
  - constructor. assumption.
  - apply lc_ty_at_monotone with (k:=0); [apply Htheta|lia].
  - apply lc_ty_arrow; assumption.
  - apply lc_ty_all. assumption.
  - constructor.
Qed.

Lemma instantiate_tm_locally_closed : forall theta gamma K k t,
  type_substitution_closed theta -> term_substitution_closed gamma ->
  lc_tm_at K k t -> lc_tm_at K k (instantiate theta gamma t).
Proof.
  intros theta gamma K k t Htheta Hgamma Hlc. induction Hlc; simpl.
  - constructor. assumption.
  - apply lc_tm_at_monotone with (K:=0) (k:=0); try lia. apply Hgamma.
  - apply lc_tm_abs.
    + eapply instantiate_ty_locally_closed; eauto.
    + assumption.
  - apply lc_tm_app; assumption.
  - apply lc_tm_tabs. assumption.
  - apply lc_tm_tapp.
    + assumption.
    + eapply instantiate_ty_locally_closed; eauto.
  - constructor.
  - apply lc_tm_div; assumption.
  - apply lc_tm_arith; assumption.
  - apply lc_tm_fix.
    + eapply instantiate_ty_locally_closed; eauto.
    + eapply instantiate_ty_locally_closed; eauto.
    + assumption.
    + assumption.
  - apply lc_tm_ifzero; assumption.
  - apply lc_tm_choice; assumption.
Qed.

Lemma erase_open_rty_tm_rec : forall k R u,
  erase (open_rty_tm_rec k u R) = erase R.
Proof.
  intros k R. revert k. induction R; intros k u; simpl.
  - reflexivity.
  - rewrite (IHR1 k u), (IHR2 (S k) u). reflexivity.
  - rewrite (IHR2 (S k) u). reflexivity.
  - rewrite (IHR k u). reflexivity.
Qed.

Lemma erase_open_rty_tm : forall R u,
  erase (open_rty_tm R u) = erase R.
Proof. intros; apply erase_open_rty_tm_rec. Qed.

Lemma erase_open_rty_ty_rec : forall k R U,
  erase (open_rty_ty_rec k U R) = open_ty_rec k U (erase R).
Proof.
  intros k R. revert k. induction R; intros k U; simpl.
  - reflexivity.
  - rewrite (IHR1 k U), (IHR2 k U). reflexivity.
  - rewrite (IHR2 k U). reflexivity.
  - rewrite (IHR (S k) U). reflexivity.
Qed.

Lemma erase_open_rty_ty : forall R U,
  erase (open_rty_ty R U) = open_ty (erase R) U.
Proof. intros; apply erase_open_rty_ty_rec. Qed.

Lemma wf_rty_erase : forall Delta RGamma R,
  wf_rty Delta RGamma R -> wf_ty Delta (erase R).
Proof.
  intros Delta RGamma R Hwf. induction Hwf.
  - simpl. assumption.
  - simpl. apply WF_Arrow.
    + exact IHHwf.
    + specialize (H0 (fresh L) (fresh_notin L)).
      rewrite erase_open_rty_tm in H0. exact H0.
  - simpl. specialize (H0 (fresh L) (fresh_notin L)).
    rewrite erase_open_rty_tm in H0. exact H0.
  - simpl. apply WF_All with (L := L).
    intros X HX. specialize (H0 X HX).
    rewrite erase_open_rty_ty in H0. exact H0.
Qed.

Lemma close_open_ty_rec_cancel : forall T k X,
  ~ In X (fv_ty T) ->
  close_ty_rec k X (open_ty_rec k (Ty_FVar X) T) = T.
Proof.
  induction T; intros k X Hfresh; simpl in *.
  - destruct (Nat.eqb k n) eqn:E; simpl.
    + apply Nat.eqb_eq in E. subst. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - assert (X <> a) by (intro Heq; subst; apply Hfresh; simpl; auto).
    destruct (Nat.eqb X a) eqn:E; [apply Nat.eqb_eq in E; contradiction|reflexivity].
  - rewrite IHT1, IHT2; try (intro Hin; apply Hfresh; simpl; apply in_or_app; auto).
    reflexivity.
  - f_equal. apply IHT. exact Hfresh.
  - reflexivity.
Qed.

Lemma subtype_erase : forall Delta RGamma R S,
  subtype Delta RGamma R S -> erase R = erase S.
Proof.
  intros Delta RGamma R S Hsub. induction Hsub.
  - reflexivity.
  - reflexivity.
  - simpl. f_equal.
    + symmetry. exact IHHsub.
    + specialize (H0 (fresh L) (fresh_notin L)).
      rewrite !erase_open_rty_tm in H0. exact H0.
  - simpl.
    rewrite erase_open_rty_tm in IHHsub. exact IHHsub.
  - simpl. specialize (H2 (fresh L) (fresh_notin L)).
    rewrite erase_open_rty_tm in H2. exact H2.
  - simpl.
    set (X := fresh (L ++ fv_ty (erase R) ++ fv_ty (erase S))).
    assert (HX_L : ~ In X L).
    { unfold X. intro Hin. apply (fresh_notin (L ++ fv_ty (erase R) ++ fv_ty (erase S))).
      apply in_or_app. left. exact Hin. }
    assert (HX_R : ~ In X (fv_ty (erase R))).
    { unfold X. intro Hin. apply (fresh_notin (L ++ fv_ty (erase R) ++ fv_ty (erase S))).
      apply in_or_app. right. apply in_or_app. left. exact Hin. }
    assert (HX_S : ~ In X (fv_ty (erase S))).
    { unfold X. intro Hin. apply (fresh_notin (L ++ fv_ty (erase R) ++ fv_ty (erase S))).
      apply in_or_app. right. apply in_or_app. right. exact Hin. }
    specialize (H0 X HX_L) as Heq.
    rewrite !erase_open_rty_ty in Heq.
    unfold open_ty in Heq.
    apply (f_equal (close_ty_rec 0 X)) in Heq.
    rewrite !close_open_ty_rec_cancel in Heq by assumption.
    f_equal. exact Heq.
  - exact (eq_trans IHHsub1 IHHsub2).
Qed.

Lemma lookup_erase_context : forall x RGamma R,
  lookup_rcontext x RGamma = Some R ->
  lookup_context x (erase_context RGamma) = Some (erase R).
Proof.
  intros x RGamma. induction RGamma as [|[y S] RGamma IH]; intros R H; simpl in H.
  - discriminate.
  - simpl. unfold update. simpl.
    destruct (Nat.eqb x y) eqn:E.
    + inversion H; subst. reflexivity.
    + apply IH in H. exact H.
Qed.

Lemma context_included_update : forall G G' x T,
  context_included G G' ->
  context_included (update G x T) (update G' x T).
Proof.
  intros G G' x T Hinc y U Hlook. unfold update in *; simpl in *.
  destruct (Nat.eqb y x) eqn:E.
  - inversion Hlook; subst. reflexivity.
  - eapply Hinc. exact Hlook.
Qed.

Lemma has_type_context_inclusion : forall Delta G G' t T,
  context_included G G' -> has_type Delta G t T -> has_type Delta G' t T.
Proof.
  intros Delta G G' t T Hinc Hty. revert G' Hinc.
  induction Hty; intros G' Hinc.
  - eapply T_Var; eauto.
  - apply T_Abs with (L := L).
    + exact H.
    + intros x Hx. eapply (H1 x Hx (update G' x T1)).
      eapply context_included_update. exact Hinc.
  - eapply T_App; eauto.
  - apply T_TAbs with (L := L). intros X HX. eapply H0; eauto.
  - eapply T_TApp; eauto.
  - constructor.
  - eapply T_Div; eauto.
  - eapply T_Arith; eauto.
  - apply T_Fix with (L := L).
    + exact H.
    + exact H0.
    + intros x Hx. eapply (H2 x Hx (update G' x A)).
      eapply context_included_update. exact Hinc.
    + intros f x Hf Hx.
      eapply (H4 f x Hf Hx (update (update G' x A) f (Ty_Arrow A B))).
      eapply context_included_update. eapply context_included_update. exact Hinc.
  - eapply T_IfZero; eauto.
  - eapply T_Choice; eauto.
Qed.

Lemma context_update_same_included : forall G x T,
  lookup_context x G = Some T -> context_included (update G x T) G.
Proof.
  intros G x T Hlookup y U H. unfold update in H. simpl in H.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst y. inversion H; subst. exact Hlookup.
  - exact H.
Qed.

Lemma has_rtype_erase : forall Delta RGamma t R,
  has_rtype Delta RGamma t R ->
  has_type Delta (erase_context RGamma) t (erase R).
Proof.
  intros Delta RGamma t R Hty. induction Hty.
  - eapply T_Var.
    + eapply lookup_erase_context. exact H.
    + eapply wf_rty_erase. exact H0.
  - apply T_Abs with (L := L).
    + exact (wf_rty_erase Delta RGamma R1 H).
    + intros x Hx. specialize (H1 x Hx).
      rewrite erase_open_rty_tm in H1. exact H1.
  - change (has_type Delta (erase_context RGamma) (tm_app t1 t2) (erase R2)).
    eapply T_App with (T1 := erase R1); eassumption.
  - apply T_TAbs with (L := L). intros X HX.
    specialize (H0 X HX). rewrite erase_open_rty_ty in H0. exact H0.
  - rewrite erase_open_rty_ty. eapply T_TApp.
    + exact IHHty.
    + assumption.
  - simpl. apply T_Int.
  - simpl. apply T_Div; assumption.
  - simpl. apply T_Arith; assumption.
  - simpl. apply T_Choice; assumption.
  - exact H.
  - apply T_Fix with (L := L).
    + pose proof (wf_rty_erase Delta RGamma
        (R_Func (measured_input A p metric) R2) H) as Hwfarr.
      inversion Hwfarr; assumption.
    + pose proof (wf_rty_erase Delta RGamma
        (R_Func (measured_input A p metric) R2) H) as Hwfarr.
      inversion Hwfarr; assumption.
    + intros x Hx. specialize (H0 x Hx). exact H0.
    + intros f x Hf Hx. specialize (H2 f x Hf Hx).
      rewrite erase_open_rty_tm in H2. exact H2.
  - simpl. apply T_IfZero.
    + eapply T_Var.
      * pose proof (lookup_erase_context x RGamma
          (R_Refine Ty_Int p) H) as Hlook. simpl in Hlook. exact Hlook.
      * apply WF_Int.
    + pose proof (lookup_erase_context x RGamma (R_Refine Ty_Int p) H) as Hlook.
      simpl in Hlook. eapply has_type_context_inclusion.
      * eapply context_update_same_included. exact Hlook.
      * exact IHHty1.
    + pose proof (lookup_erase_context x RGamma (R_Refine Ty_Int p) H) as Hlook.
      simpl in Hlook. eapply has_type_context_inclusion.
      * eapply context_update_same_included. exact Hlook.
      * exact IHHty2.
  - match goal with
    | Hsub : subtype _ _ _ _ |- _ =>
        pose proof (subtype_erase _ _ _ _ Hsub) as Herase
    end.
    rewrite Herase in IHHty. exact IHHty.
Qed.

Lemma value_int_form : forall Delta v,
  value v -> has_type Delta empty v Ty_Int -> exists n, v = tm_int n.
Proof.
  intros Delta v Hv Hty. inversion Hv; subst; inversion Hty; subst;
    try discriminate; eexists; reflexivity.
Qed.

Definition stuck (t : tm) : Prop :=
  ~ value t /\ forall u, ~ (t --> u).

Lemma predicate_multistep_int : forall n v,
  predicate_multistep (tm_int n) v -> v = tm_int n.
Proof.
  intros n v H. inversion H; subst; auto.
  inversion H0.
Qed.

Lemma predicate_multistep_trans : forall t u v,
  predicate_multistep t u -> predicate_multistep u v -> predicate_multistep t v.
Proof.
  intros t u v H. induction H; eauto using predicate_multistep.
Qed.

Lemma predicate_multistep_sound : forall t u,
  predicate_multistep t u -> multi t u.
Proof.
  intros t u H. induction H; eauto using multi.
Qed.

Lemma metric_nonnegative : forall metric,
  qualifier_holds (Pred_Ge metric (tm_int 0%Z)) ->
  exists n, predicate_multistep metric (tm_int n) /\ (0%Z <= n)%Z.
Proof.
  intros metric H. unfold qualifier_holds, predicate_holds, operational_atoms,
    interpret_qualifier, Pred_Ge in H. simpl in H.
  destruct H as [n0 [n [Hzero [Hm Hle]]]].
  pose proof (predicate_multistep_int 0%Z (tm_int n0) Hzero) as E.
  inversion E; subst. exists n. split; [exact Hm|lia].
Qed.

Lemma metric_strictly_decreases : forall metric current n m,
  qualifier_holds (Pred_Lt metric current) ->
  predicate_multistep metric (tm_int n) ->
  predicate_multistep current (tm_int m) -> (n < m)%Z.
Proof.
  intros metric current n m Hlt Hn Hm.
  unfold qualifier_holds, predicate_holds, operational_atoms, interpret_qualifier in Hlt.
  simpl in Hlt. destruct Hlt as [n1 [m1 [H1 [H2 [Hlt Hall]]]]].
  eapply Hall; eassumption.
Qed.

Definition metric_decrease (n m : Z) : Prop := (0%Z <= n)%Z /\ (n < m)%Z.

Lemma metric_decrease_well_founded : well_founded metric_decrease.
Proof.
  apply (well_founded_lt_compat Z Z.to_nat metric_decrease).
  intros n m [Hn Hlt].
  assert (Hm : (0%Z <= m)%Z) by lia.
  apply (proj1 (Z2Nat.inj_lt n m Hn Hm)). exact Hlt.
Qed.

Lemma logical_measured_input : forall A p metric theta gamma v,
  logical_value (instantiate_rty theta gamma (measured_input A p metric)) v ->
  exists m,
    predicate_multistep (open_tm (instantiate theta gamma metric) v) (tm_int m) /\
    (0%Z <= m)%Z /\
    qualifier_holds (open_qualifier_tm (instantiate_qualifier theta gamma p) v).
Proof.
  intros A p metric theta gamma v Hsem.
  pose proof (logical_value_fuel_refinement 1 (instantiate_ty theta A)
    (Pred_And (instantiate_qualifier theta gamma p)
      (Pred_Ge (instantiate theta gamma metric) (tm_int 0%Z))) v (Hsem 1)) as Hq.
  simpl in Hq. destruct Hq as [Hp Hge].
  unfold qualifier_holds, predicate_holds, operational_atoms, interpret_qualifier in Hge.
  simpl in Hge. destruct Hge as [n0 [m [Hzero [Hm Hle]]]].
  pose proof (predicate_multistep_int 0%Z (tm_int n0) Hzero) as Ezero.
  inversion Ezero; subst n0.
  exists m. split; [exact Hm|]. split; [lia|exact Hp].
Qed.

Lemma logical_smaller_input : forall A p metric current theta gamma v,
  logical_value (instantiate_rty theta gamma
    (smaller_input A p metric current)) v ->
  exists n m, predicate_multistep (open_tm (instantiate theta gamma metric) v)
      (tm_int n) /\
    predicate_multistep (open_tm (instantiate theta gamma current) v)
      (tm_int m) /\
    (n < m)%Z /\
    qualifier_holds (open_qualifier_tm (instantiate_qualifier theta gamma p) v).
Proof.
  intros A p metric current theta gamma v Hsem.
  pose proof (logical_value_fuel_refinement 1 (instantiate_ty theta A)
    (Pred_And (instantiate_qualifier theta gamma p)
      (Pred_And
        (Pred_Ge (instantiate theta gamma metric) (tm_int 0%Z))
        (Pred_Lt (instantiate theta gamma metric) (instantiate theta gamma current))))
    v (Hsem 1)) as Hq.
  simpl in Hq. destruct Hq as [Hp [Hge Hlt]].
  unfold qualifier_holds, predicate_holds, operational_atoms, interpret_qualifier in *.
  simpl in Hge, Hlt.
  destruct Hge as [n0 [n [Hzero [Hmetric Hnonneg]]]].
  pose proof (predicate_multistep_int 0%Z (tm_int n0) Hzero) as Ez.
  inversion Ez; subst n0.
  destruct Hlt as [n1 [m [Hmetric1 [Hcurrent [Hlt Hall]]]]].
  assert (Hstrict : (n < m)%Z).
  { eapply Hall; eassumption. }
  exists n, m. repeat split; try assumption.
Qed.

Lemma nonzero_from_ne_int : forall n,
  qualifier_holds (Pred_Ne (tm_int n) (tm_int 0%Z)) -> n <> 0%Z.
Proof.
  intros n Hne Heq. subst n. apply Hne. exists (tm_int 0%Z). split.
  - constructor.
  - split; constructor; constructor.
Qed.

Lemma logical_nonzero_integer : forall v,
  logical_value (R_Refine Ty_Int
    (Pred_Ne (tm_bvar 0) (tm_int 0%Z))) v ->
  exists n, v = tm_int n /\ n <> 0%Z.
Proof.
  intros v Hsem. specialize (Hsem 1). simpl in Hsem.
  destruct Hsem as [_ [n [Hv Hpred]]]. subst v.
  exists n. split; [reflexivity|]. apply nonzero_from_ne_int.
  simpl in Hpred. exact Hpred.
Qed.

Lemma logical_integer_shape : forall p v,
  logical_value (R_Refine Ty_Int p) v -> exists n, v = tm_int n.
Proof.
  intros p v H. specialize (H 0). simpl in H. destruct H as [_ [n [Heq _]]].
  exists n. exact Heq.
Qed.

Lemma division_of_integer_values_steps : forall n v,
  logical_value (R_Refine Ty_Int
    (Pred_Ne (tm_bvar 0) (tm_int 0%Z))) v ->
  exists u, tm_div (tm_int n) v --> u.
Proof.
  intros n v Hsem. destruct (logical_nonzero_integer v Hsem) as [m [-> Hnz]].
  exists (tm_int (Z.div n m)). apply ST_DivInt. exact Hnz.
Qed.

Lemma stuck_app_left : forall t1 t2,
  stuck t1 -> locally_closed_tm t2 -> stuck (tm_app t1 t2).
Proof.
  intros t1 t2 [Hnv Hns] Hlc. split.
  - intro Hv. inversion Hv.
  - intros u Hs. inversion Hs; subst.
    + exfalso. apply Hnv. constructor; assumption.
    + exfalso. eapply Hns; eassumption.
    + exfalso. apply Hnv. assumption.
    + exfalso. apply Hnv. constructor; assumption.
Qed.

Lemma stuck_app_right : forall v t,
  value v -> stuck t -> stuck (tm_app v t).
Proof.
  intros v t Hv [Hnv Hns]. split.
  - intro H. inversion H.
  - intros u Hs. inversion Hs; subst.
    + exfalso. apply Hnv. assumption.
    + exfalso. eapply value_no_step; eassumption.
    + exfalso. eapply Hns; eassumption.
    + exfalso. apply Hnv. assumption.
Qed.

Lemma stuck_tapp : forall t T,
  stuck t -> locally_closed_ty T -> stuck (tm_tapp t T).
Proof.
  intros t T [Hnv Hns] HT. split.
  - intro Hv. inversion Hv.
  - intros u Hs. inversion Hs; subst.
    + exfalso. apply Hnv. constructor; assumption.
    + exfalso. eapply Hns; eassumption.
Qed.

Lemma stuck_div_left : forall t1 t2,
  stuck t1 -> locally_closed_tm t2 -> stuck (tm_div t1 t2).
Proof.
  intros t1 t2 [Hnv Hns] Hlc. split.
  - intro Hv. inversion Hv.
  - intros u Hs. inversion Hs; subst.
    + exfalso. eapply Hns; eassumption.
    + exfalso. apply Hnv. assumption.
    + exfalso. apply Hnv. constructor.
Qed.

Lemma stuck_div_right : forall v t,
  value v -> stuck t -> stuck (tm_div v t).
Proof.
  intros v t Hv [Hnv Hns]. split.
  - intro H. inversion H.
  - intros u Hs. inversion Hs; subst.
    + exfalso. eapply value_no_step; eassumption.
    + exfalso. eapply Hns; eassumption.
    + exfalso. apply Hnv. constructor.
Qed.

Lemma stuck_arith_left : forall op t1 t2,
  stuck t1 -> locally_closed_tm t2 -> stuck (tm_arith op t1 t2).
Proof.
  intros op t1 t2 [Hnv Hns] Hlc. split.
  - intro Hv. inversion Hv.
  - intros u Hs. inversion Hs; subst.
    + exfalso. eapply Hns; eassumption.
    + exfalso. apply Hnv. assumption.
    + exfalso. apply Hnv. constructor.
Qed.

Lemma stuck_arith_right : forall op v t,
  value v -> stuck t -> stuck (tm_arith op v t).
Proof.
  intros op v t Hv [Hnv Hns]. split.
  - intro H. inversion H.
  - intros u Hs. inversion Hs; subst.
    + exfalso. eapply value_no_step; eassumption.
    + exfalso. eapply Hns; eassumption.
    + exfalso. apply Hnv. constructor.
Qed.

Lemma stuck_ifzero_arg : forall t t0 t1,
  stuck t -> locally_closed_tm t0 -> locally_closed_tm t1 ->
  stuck (tm_ifzero t t0 t1).
Proof.
  intros t t0 t1 [Hnv Hns] H0 H1. split.
  - intro Hv. inversion Hv.
  - intros u Hs. inversion Hs; subst.
    + exfalso. eapply Hns; eassumption.
    + exfalso. apply Hnv. constructor.
    + exfalso. apply Hnv. constructor.
Qed.

Lemma stuck_div_zero : forall n,
  stuck (tm_div (tm_int n) (tm_int 0%Z)).
Proof.
  intros n. split.
  - intro Hv. inversion Hv.
  - intros u Hs. inversion Hs; subst.
    + exfalso. eapply value_no_step; [apply v_int | eassumption].
    + exfalso. eapply value_no_step; [apply v_int | eassumption].
    + exfalso. match goal with Hnz : ?m <> 0%Z |- _ => apply Hnz; reflexivity end.
Qed.

Lemma core_progress_or_stuck : forall Delta t T,
  has_type Delta empty t T ->
  value t \/ (exists u, t --> u) \/ stuck t.
Proof.
  intros Delta t T Hty. remember empty as Gamma eqn:HG in Hty.
  induction Hty; subst Gamma.
  - unfold empty in H. simpl in H. discriminate.
  - left. apply v_abs. apply lc_tm_abs.
    + apply (wf_ty_locally_closed Delta T1). assumption.
    + apply lc_tm_at_open_tm_inv with (x := fresh L).
      apply (has_type_locally_closed Delta (update empty (fresh L) T1)
               (open_tm t2 (tm_fvar (fresh L))) T2).
      apply H0. apply fresh_notin.
  - destruct (IHHty1 eq_refl) as [Hv1 | [Hs1 | Hst1]].
    + destruct (IHHty2 eq_refl) as [Hv2 | [Hs2 | Hst2]].
      * destruct Hv1; inversion Hty1; subst;
          right; left; eexists; eauto using ST_AppAbs, ST_AppFix.
      * right; left. destruct Hs2 as [u Hu]. eexists. eapply ST_App2; eauto.
      * right; right. eapply stuck_app_right; eauto.
    + right; left. destruct Hs1 as [u Hu]. eexists. eapply ST_App1; eauto.
        eapply has_type_locally_closed. exact Hty2.
    + right; right. eapply stuck_app_left; eauto using has_type_locally_closed.
  - left. apply v_tabs. apply lc_tm_tabs.
    apply lc_tm_at_open_ty_inv with (X := fresh L).
    apply (has_type_locally_closed (fresh L :: Delta) empty
             (open_tm_ty t (Ty_FVar (fresh L))) (open_ty T (Ty_FVar (fresh L)))).
    apply H. apply fresh_notin.
  - destruct (IHHty eq_refl) as [Hv | [Hs | Hst]].
    + destruct Hv; inversion Hty; subst.
      right; left. eexists. eapply ST_TAppTabs; eauto using wf_ty_locally_closed.
    + right; left. destruct Hs as [u Hu]. eexists. eapply ST_TApp; eauto.
      exact (wf_ty_locally_closed Delta U H).
    + right; right. eapply stuck_tapp; [exact Hst | exact (wf_ty_locally_closed Delta U H)].
  - left. apply v_int.
  - destruct (IHHty1 eq_refl) as [Hv1 | [Hs1 | Hst1]].
    + destruct (IHHty2 eq_refl) as [Hv2 | [Hs2 | Hst2]].
      * destruct (value_int_form Delta t1 Hv1 Hty1) as [n ->].
        destruct (value_int_form Delta t2 Hv2 Hty2) as [m ->].
        destruct (Z.eq_dec m 0%Z) as [E | E].
        -- subst m. right; right. apply stuck_div_zero.
        -- right; left. eexists. apply ST_DivInt. exact E.
      * right; left. destruct Hs2 as [u Hu]. eexists. eapply ST_Div2; eauto.
      * right; right. eapply stuck_div_right; eauto.
    + right; left. destruct Hs1 as [u Hu]. eexists. eapply ST_Div1; eauto.
      eapply has_type_locally_closed. exact Hty2.
    + right; right. eapply stuck_div_left; eauto using has_type_locally_closed.
  - destruct (IHHty1 eq_refl) as [Hv1 | [Hs1 | Hst1]].
    + destruct (IHHty2 eq_refl) as [Hv2 | [Hs2 | Hst2]].
      * destruct (value_int_form Delta t1 Hv1 Hty1) as [n ->].
        destruct (value_int_form Delta t2 Hv2 Hty2) as [m ->].
        right; left. eexists. apply ST_ArithInt.
      * right; left. destruct Hs2 as [u Hu]. eexists. eapply ST_Arith2; eauto.
      * right; right. eapply stuck_arith_right; eauto.
    + right; left. destruct Hs1 as [u Hu]. eexists. eapply ST_Arith1; eauto.
      eapply has_type_locally_closed. exact Hty2.
    + right; right. eapply stuck_arith_left; eauto using has_type_locally_closed.
  - left. apply v_fix. apply lc_tm_fix.
    + apply (wf_ty_locally_closed Delta A). assumption.
    + apply (wf_ty_locally_closed Delta B). assumption.
    + apply lc_tm_at_open_tm_inv with (x := fresh L).
      apply (has_type_locally_closed Delta (update empty (fresh L) A)
               (open_tm metric (tm_fvar (fresh L))) Ty_Int).
      apply H1. apply fresh_notin.
    + apply lc_tm_at_open_tm_inv with (x := fresh (fresh L :: L)).
      apply lc_tm_at_open_tm_inv with (x := fresh L).
      apply (has_type_locally_closed Delta
               (update (update empty (fresh L) A) (fresh (fresh L :: L))
                 (Ty_Arrow A B))
               (open_fix_body body (tm_fvar (fresh (fresh L :: L)))
                 (tm_fvar (fresh L))) B).
      apply (H3 (fresh (fresh L :: L)) (fresh L)).
      * intro Hin. apply (fresh_notin (fresh L :: L)). simpl. right. exact Hin.
      * simpl. intro Hin. destruct Hin as [Heq | Hin].
        -- apply (fresh_notin (fresh L :: L)). simpl. left. symmetry. exact Heq.
        -- apply (fresh_notin L). exact Hin.
  - destruct (IHHty1 eq_refl) as [Hv | [Hs | Hst]].
    + destruct (value_int_form Delta t Hv Hty1) as [n ->].
      destruct (Z.eq_dec n 0%Z) as [E | E].
      * right; left. eexists. subst. apply ST_IfZero;
          eapply has_type_locally_closed; eauto.
      * right; left. eexists. apply ST_IfNonzero; eauto.
        -- eapply has_type_locally_closed; eauto.
        -- eapply has_type_locally_closed; eauto.
    + right; left. destruct Hs as [u Hu]. eexists. eapply ST_IfZeroArg; eauto.
      * eapply has_type_locally_closed; eauto.
      * eapply has_type_locally_closed; eauto.
    + right; right. eapply stuck_ifzero_arg; eauto using has_type_locally_closed.
  - right; left. eexists. apply ST_ChoiceLeft;
      eapply has_type_locally_closed; eauto.
Qed.

Definition semantic_has_rtype (Delta : ty_context) (RGamma : rcontext)
    (t : tm) (R : rty) : Prop :=
  forall theta gamma,
    type_substitution_closed theta ->
    forall fuel, logical_environment_fuel fuel theta gamma RGamma ->
      logical_computation_fuel fuel (instantiate_rty theta gamma R)
        (instantiate theta gamma t).

Definition semantic_subtype (Delta : ty_context) (RGamma : rcontext)
    (R S : rty) : Prop :=
  forall theta gamma,
    type_substitution_closed theta ->
    forall fuel, logical_environment_fuel fuel theta gamma RGamma ->
      forall v, logical_value_fuel fuel (instantiate_rty theta gamma R) v ->
        logical_value_fuel fuel (instantiate_rty theta gamma S) v.

Lemma fundamental_mutual :
  (forall Delta RGamma t R, has_rtype Delta RGamma t R ->
    semantic_has_rtype Delta RGamma t R) /\
  (forall Delta RGamma R S, subtype Delta RGamma R S ->
    semantic_subtype Delta RGamma R S).
Proof.
  apply (refinement_typing_mutind
    (fun Delta RGamma t R _ => semantic_has_rtype Delta RGamma t R)
    (fun Delta RGamma R S _ => semantic_subtype Delta RGamma R S)).
  all: try solve [intros; unfold semantic_has_rtype, semantic_subtype in *;
    eauto using fundamental_variable_fuel, fundamental_integer].
  all: try solve [
    intros Delta RGamma t1 t2 R Hty1 Hsem1 Hty2 Hsem2 theta gamma Htheta fuel Henv;
    unfold semantic_has_rtype in Hsem1, Hsem2 |- *;
    pose proof (Hsem1 theta gamma Htheta fuel Henv) as Hcomp1;
    pose proof (Hsem2 theta gamma Htheta fuel Henv) as Hcomp2;
    destruct Henv as [Hvalues [Hcontext Hformulas]];
    assert (Hgamma : term_substitution_closed gamma)
      by (intro y; apply value_regular; apply Hvalues);
    pose proof (has_rtype_erase Delta RGamma t1 R Hty1) as Hcore1;
    pose proof (has_rtype_erase Delta RGamma t2 R Hty2) as Hcore2;
    pose proof (has_type_locally_closed _ _ _ _ Hcore1) as Hlc1;
    pose proof (has_type_locally_closed _ _ _ _ Hcore2) as Hlc2;
    cbn [instantiate] in *;
    eapply logical_choice;
    [eapply instantiate_tm_locally_closed; eauto|eapply instantiate_tm_locally_closed; eauto|exact Hcomp1|exact Hcomp2]].
  all: try solve [
    intros Delta RGamma t R S Hty IHty Hwf Hsub IHsub theta gamma Htheta fuel Henv;
    unfold semantic_has_rtype, semantic_subtype in *;
    pose proof (IHty theta gamma Htheta fuel Henv) as Hcomp;
    intros u Hu; specialize (Hcomp u Hu); destruct Hcomp as [[Hv Hval]|Hstep];
    [left; split; [exact Hv|eapply IHsub; eauto]|right; exact Hstep]].
  all: try solve [
    intros L Delta RGamma R1 body R2 Hwf Hbody HbodyIH theta gamma Htheta fuel Henv;
    unfold semantic_has_rtype in *;
    assert (Hgamma : term_substitution_closed gamma)
      by (destruct Henv as [Hvals _]; intro y; apply value_regular; apply Hvals);
    set (x0 := fresh L);
    assert (Hx0 : ~ In x0 L) by (unfold x0; apply fresh_notin);
    pose proof (has_rtype_erase Delta (update_rcontext RGamma x0 R1)
      (open_tm body (tm_fvar x0)) (open_rty_tm R2 (tm_fvar x0))
      (Hbody x0 Hx0)) as Hcoreopen;
    pose proof (has_type_locally_closed _ _ _ _ Hcoreopen) as Hlcopen;
    assert (Habs : locally_closed_tm (tm_abs (erase R1) body))
      by (apply lc_tm_abs;
          [apply wf_ty_locally_closed with (Delta:=Delta); eapply wf_rty_erase; exact Hwf|
           eapply lc_tm_at_open_tm_inv with (x:=x0); exact Hlcopen]);
    assert (Habsinst : locally_closed_tm
      (tm_abs (instantiate_ty theta (erase R1)) (instantiate theta gamma body)))
      by (eapply instantiate_tm_locally_closed; eauto);
    destruct fuel; [
      change (logical_computation_fuel 0
        (instantiate_rty theta gamma (R_Func R1 R2))
        (instantiate theta gamma (tm_abs (erase R1) body)));
      apply logical_value_fuel_computation; simpl; apply v_abs; exact Habsinst
    | set (x := fresh (L ++ fv_tm body ++ fv_rty R1 ++ fv_rty R2 ++
          fv_rcontext RGamma ++ rcontext_formula_fv RGamma ++ map fst RGamma));
      assert (Hxall : ~ In x (L ++ fv_tm body ++ fv_rty R1 ++ fv_rty R2 ++
          fv_rcontext RGamma ++ rcontext_formula_fv RGamma ++ map fst RGamma))
        by (unfold x; apply fresh_notin);
      assert (HxL : ~ In x L) by (intro Hin; apply Hxall; repeat rewrite in_app_iff; tauto);
      assert (Hxbody : ~ In x (fv_tm body)) by (intro Hin; apply Hxall; repeat rewrite in_app_iff; tauto);
      assert (HxR1 : ~ In x (fv_rty R1)) by (intro Hin; apply Hxall; repeat rewrite in_app_iff; tauto);
      assert (HxR2 : ~ In x (fv_rty R2)) by (intro Hin; apply Hxall; repeat rewrite in_app_iff; tauto);
      assert (Hxctx : ~ In x (fv_rcontext RGamma)) by (intro Hin; apply Hxall; repeat rewrite in_app_iff; tauto);
      assert (Hxform : ~ In x (rcontext_formula_fv RGamma)) by (intro Hin; apply Hxall; repeat rewrite in_app_iff; tauto);
      assert (Hxdom : ~ In x (map fst RGamma)) by (intro Hin; apply Hxall; repeat rewrite in_app_iff; tauto);
      assert (HxR1f : forall y S, lookup_rcontext y RGamma = Some S -> ~ In x (fv_rty S))
        by (intros y S Hlook Hin; apply Hxctx; eapply lookup_rcontext_fv; eassumption);
      assert (HxQ : forall y T p, lookup_rcontext y RGamma = Some (R_Refine T p) ->
          ~ In x (fv_qualifier (open_qualifier_tm p (tm_fvar y))))
        by (intros y T p Hlook Hin; apply Hxform; eapply lookup_rcontext_formula_fv; eassumption);
      intros u Hu; apply logical_value_fuel_computation;
      eapply logical_abs_application with
        (T := instantiate_ty theta (erase R1))
        (body := instantiate theta gamma body)
        (A := instantiate_rty theta gamma R1)
        (B := instantiate_rty theta gamma R2);
      [exact Habsinst|intros w Hw;
        pose proof (logical_environment_fuel_extend fuel theta gamma RGamma x R1 w
          Henv Hw (logical_value_fuel_is_value fuel (instantiate_rty theta gamma R1) w Hw)
          HxR1f HxR1 HxQ) as Henv';
        pose proof (HbodyIH x HxL theta (term_subst_update gamma x w) Htheta fuel Henv') as Hcomp;
        unfold semantic_has_rtype in Hcomp;
        rewrite (instantiate_open_tm_rec body 0 theta gamma x w Hxbody Hgamma) in Hcomp;
        rewrite (instantiate_open_rty_tm_rec R2 0 theta gamma x w HxR2 Hgamma) in Hcomp;
        exact Hcomp]
    ].
  Show.
Qed.

Theorem never_stuck : forall (t t' : tm) (R : rty),
  has_rtype [] empty_rcontext t R ->
  multi t t' ->
  value t' \/ exists t'' : tm, t' --> t''.
Proof.
  (* Complete this proof. *)
Qed.

End SystemFRefinementNonDeterminismRecursionTask.
