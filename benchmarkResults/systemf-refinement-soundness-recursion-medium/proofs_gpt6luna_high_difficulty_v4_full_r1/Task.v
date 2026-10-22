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

End SystemFRefinementRecursion.

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
Module SystemFRefinementRecursionInfrastructure.
Import ListNotations.
Import SystemFRefinementRecursion.

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

End SystemFRefinementRecursionInfrastructure.

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
Module SystemFRefinementRecursionCoreTyping.
Import ListNotations.
Import SystemFRefinementRecursion.
Import SystemFRefinementRecursionInfrastructure.

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

End SystemFRefinementRecursionCoreTyping.

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

Fixpoint close_ty_rec (k : nat) (X : atom) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar Y => if Nat.eqb X Y then Ty_BVar k else Ty_FVar Y
  | Ty_Arrow T1 T2 =>
      Ty_Arrow (close_ty_rec k X T1) (close_ty_rec k X T2)
  | Ty_All T1 => Ty_All (close_ty_rec (S k) X T1)
  | Ty_Int => Ty_Int
  end.

End SystemFRefinementRecursionTyping.

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Module SystemFRefinementRecursionEvaluation.
Import ListNotations SystemFRefinementRecursion SystemFRefinementRecursionInfrastructure
  SystemFRefinementRecursionCoreTyping.

Inductive multi : tm -> tm -> Prop :=
  | multi_refl : forall t, multi t t
  | multi_step : forall t1 t2 t3,
      t1 --> t2 -> multi t2 t3 -> multi t1 t3.
Notation "t '-->*' u" := (multi t u) (at level 40).

Definition halts (t : tm) : Prop :=
  exists v, multi t v /\ value v.

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

End SystemFRefinementRecursionEvaluation.

From Stdlib Require Import Arith.PeanoNat Lists.List Lia Program.Wf Arith.Wf_nat.
From Equations Require Import Equations.
Module SystemFRefinementRecursionSubstitution.
Import ListNotations.
Import SystemFRefinementRecursion.
Import SystemFRefinementRecursionInfrastructure.
Import SystemFRefinementRecursionCoreTyping.
Import SystemFRefinementRecursionTyping.
Import SystemFRefinementRecursionEvaluation.

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
End SystemFRefinementRecursionSubstitution.

Module SystemFRefinementRecursionTask.
Import ListNotations SystemFRefinementRecursion SystemFRefinementRecursionInfrastructure SystemFRefinementRecursionCoreTyping SystemFRefinementRecursionLogic SystemFRefinementRecursionTyping SystemFRefinementRecursionEvaluation SystemFRefinementRecursionSubstitution .

Lemma open_ty_rec_injective : forall k X T1 T2,
  ~ In X (fv_ty T1) -> ~ In X (fv_ty T2) ->
  open_ty_rec k (Ty_FVar X) T1 = open_ty_rec k (Ty_FVar X) T2 -> T1 = T2.
Proof.
  intros k X T1. revert k X. induction T1; intros k X T2 F1 F2 H;
    destruct T2; simpl in H.
  - destruct (Nat.eqb k n) eqn:E1; destruct (Nat.eqb k n0) eqn:E2;
      simpl in H.
    + apply Nat.eqb_eq in E1. apply Nat.eqb_eq in E2. subst. reflexivity.
    + discriminate H.
    + discriminate H.
    + inversion H. subst. reflexivity.
  - destruct (Nat.eqb k n) eqn:E; simpl in H.
    + inversion H; subst. apply Nat.eqb_eq in E. subst n. exfalso.
      apply F2. simpl. auto.
    + discriminate H.
  - destruct (Nat.eqb k n); simpl in H; discriminate H.
  - destruct (Nat.eqb k n); simpl in H; discriminate H.
  - destruct (Nat.eqb k n); simpl in H; discriminate H.
  - destruct (Nat.eqb k n) eqn:E; simpl in H.
    + inversion H; subst. apply Nat.eqb_eq in E. subst n. exfalso.
      apply F1. simpl. auto.
    + discriminate H.
  - inversion H. reflexivity.
  - discriminate H.
  - discriminate H.
  - discriminate H.
  - destruct (Nat.eqb k n); simpl in H; discriminate H.
  - discriminate H.
  - inversion H. subst. f_equal.
    + eapply IHT1_1.
      * intro Hin. apply F1. simpl. apply in_or_app. left. exact Hin.
      * intro Hin. apply F2. simpl. apply in_or_app. left. exact Hin.
      * eassumption.
    + eapply IHT1_2.
      * intro Hin. apply F1. simpl. apply in_or_app. right. exact Hin.
      * intro Hin. apply F2. simpl. apply in_or_app. right. exact Hin.
      * eassumption.
  - discriminate H.
  - discriminate H.
  - destruct (Nat.eqb k n); simpl in H; discriminate H.
  - discriminate H.
  - discriminate H.
  - inversion H. subst. f_equal. eapply IHT1; eauto.
  - discriminate H.
  - destruct (Nat.eqb k n); simpl in H; discriminate H.
  - discriminate H.
  - discriminate H.
  - discriminate H.
  - reflexivity.
Qed.

Lemma erase_open_rty_tm_rec : forall R k u,
  erase (open_rty_tm_rec k u R) = erase R.
Proof.
  induction R; intros k u; simpl.
  - reflexivity.
  - rewrite IHR1, (IHR2 (S k) u). reflexivity.
  - rewrite (IHR2 (S k) u). reflexivity.
  - rewrite (IHR k u). reflexivity.
Qed.

Lemma erase_open_rty_tm : forall R u,
  erase (open_rty_tm R u) = erase R.
Proof. intros; apply erase_open_rty_tm_rec. Qed.

Lemma erase_open_rty_ty : forall R k U,
  erase (open_rty_ty_rec k U R) = open_ty_rec k U (erase R).
Proof.
  induction R; intros k U; simpl.
  - reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR2. reflexivity.
  - rewrite IHR. reflexivity.
Qed.

Lemma subtype_erases_equally : forall Delta RGamma R S,
  subtype Delta RGamma R S -> erase R = erase S.
Proof.
  intros Delta RGamma R S H. induction H; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal; [symmetry; exact IHsubtype|].
    specialize (H1 (fresh L) (fresh_notin L)).
    rewrite !erase_open_rty_tm in H1. exact H1.
  - rewrite erase_open_rty_tm in IHsubtype. exact IHsubtype.
  - specialize (H2 (fresh L) (fresh_notin L)).
    rewrite erase_open_rty_tm in H2. exact H2.
  - assert (Fresh : ~ In (fresh (L ++ fv_ty (erase R) ++ fv_ty (erase S))) L).
    { intro Hin. apply (fresh_notin (L ++ fv_ty (erase R) ++ fv_ty (erase S))).
      apply in_or_app. left. exact Hin. }
    specialize (H0 (fresh (L ++ fv_ty (erase R) ++ fv_ty (erase S))) Fresh).
    pose proof (H0) as E. unfold open_rty_ty in E. rewrite !erase_open_rty_ty in E.
    assert (E0 : erase R = erase S).
    { eapply open_ty_rec_injective.
      - intro Hin. apply (fresh_notin (L ++ fv_ty (erase R) ++ fv_ty (erase S))).
        apply in_or_app. right. apply in_or_app. left. exact Hin.
      - intro Hin. apply (fresh_notin (L ++ fv_ty (erase R) ++ fv_ty (erase S))).
        apply in_or_app. right. apply in_or_app. right. exact Hin.
      - exact E. }
    f_equal. exact E0.
  - congruence.
Qed.

Lemma wf_rty_erases : forall Delta RGamma R,
  wf_rty Delta RGamma R -> wf_ty Delta (erase R).
Proof.
  intros Delta RGamma R H. induction H; simpl.
  - exact H.
  - apply WF_Arrow; [exact IHwf_rty|].
    specialize (H1 (fresh L) (fresh_notin L)).
    rewrite erase_open_rty_tm in H1. exact H1.
  - specialize (H1 (fresh L) (fresh_notin L)).
    rewrite erase_open_rty_tm in H1. exact H1.
  - apply WF_All with (L := L). intros X HX.
    specialize (H0 X HX).
    unfold open_rty_ty in H0. rewrite erase_open_rty_ty in H0. exact H0.
Qed.

Lemma lookup_erase_context : forall x RGamma R,
  lookup_rcontext x RGamma = Some R ->
  lookup_context x (erase_context RGamma) = Some (erase R).
Proof.
  intros x RGamma. induction RGamma as [|[y Q] G IH]; intros R H; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + inversion H; subst. reflexivity.
    + apply IH. exact H.
Qed.

Lemma core_context_equiv : forall Delta G1 t T G2,
  (forall x, lookup_context x G1 = lookup_context x G2) ->
  has_type Delta G1 t T -> has_type Delta G2 t T.
Proof.
  intros Delta G1 t T G2 Heq HT. revert G2 Heq.
  induction HT; intros G2 Heq.
  - eapply T_Var; [rewrite <- Heq; eassumption|assumption].
  - eapply T_Abs with (L := L); [assumption|].
    intros x Hx. specialize (H1 x Hx). apply H1. intros y. unfold update.
    destruct (Nat.eqb y x) eqn:E.
    + apply Nat.eqb_eq in E. subst. simpl. rewrite Nat.eqb_refl. reflexivity.
    + simpl. rewrite E. apply Heq.
  - eapply T_App; eauto.
  - eapply T_TAbs with (L := L). intros X HX. exact (H0 X HX G2 Heq).
  - eapply T_TApp; eauto.
  - constructor.
  - eapply T_Div; eauto.
  - eapply T_Arith; eauto.
  - eapply T_Fix with (L := L); try assumption.
    + intros x Hx. specialize (H2 x Hx). apply H2.
      intros y. unfold update. simpl. destruct (Nat.eqb y x); [reflexivity|apply Heq].
    + intros f x Hf Hx. specialize (H4 f x Hf Hx). apply H4.
      intros y. unfold update. simpl.
      destruct (Nat.eqb y f); [reflexivity|].
      destruct (Nat.eqb y x); [reflexivity|apply Heq].
  - eapply T_IfZero; eauto.
Qed.

Lemma lookup_context_update_same : forall G x T y,
  lookup_context x G = Some T ->
  lookup_context y (update G x T) = lookup_context y G.
Proof.
  intros G x T y H. unfold update. simpl.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst y. simpl. symmetry. exact H.
  - reflexivity.
Qed.

Lemma has_rtype_erases : forall Delta RGamma t R,
  has_rtype Delta RGamma t R ->
  has_type Delta (erase_context RGamma) t (erase R).
Proof.
  intros Delta RGamma t R H. induction H; simpl.
  - eapply T_Var.
    + eapply lookup_erase_context. exact H.
    + eapply wf_rty_erases. eassumption.
  - eapply T_Abs with (L := L).
    + eapply wf_rty_erases; eauto.
    + intros x Hx. specialize (H1 x Hx).
      rewrite erase_open_rty_tm in H1. exact H1.
  - eapply T_App; eauto.
  - eapply T_TAbs with (L := L). intros X HX.
    specialize (H0 X HX). unfold open_rty_ty in H0.
    rewrite erase_open_rty_ty in H0. exact H0.
  - unfold open_rty_ty. rewrite erase_open_rty_ty. eapply T_TApp; eauto.
  - constructor.
  - eapply T_Div; eauto.
  - eapply T_Arith; eauto.
  - exact H.
  - pose proof (wf_rty_erases _ _ _ H) as W.
    inversion W; subst.
    eapply T_Fix with (L := L); eauto.
    intros f x Hf Hx. specialize (H2 f x Hf Hx).
    simpl in H2. rewrite erase_open_rty_tm in H2. exact H2.
  - eapply T_IfZero with (T := erase R).
    + eapply T_Var with (T := Ty_Int).
      * change (lookup_context x (erase_context RGamma) =
          Some (erase (R_Refine Ty_Int p))).
        eapply lookup_erase_context. exact H.
      * constructor.
    + eapply core_context_equiv; [|exact IHhas_rtype1].
      intros y. eapply lookup_context_update_same.
      exact (lookup_erase_context x RGamma (R_Refine Ty_Int p) H).
    + eapply core_context_equiv; [|exact IHhas_rtype2].
      intros y. eapply lookup_context_update_same.
      exact (lookup_erase_context x RGamma (R_Refine Ty_Int p) H).
  - rewrite <- (subtype_erases_equally _ _ _ _ H1). exact IHhas_rtype.
Qed.

Lemma multi_to_predicate_multistep : forall t u,
  multi t u -> predicate_multistep t u.
Proof. intros t u H; induction H; econstructor; eauto. Qed.

Lemma nonzero_refinement_evaluation : forall t n,
  qualifier_holds (Pred_Ne t (tm_int 0%Z)) ->
  multi t (tm_int n) -> n <> 0%Z.
Proof.
  intros t n Hq Hm Heq. subst n.
  unfold qualifier_holds, predicate_holds, Pred_Ne, Pred_Implies,
    interpret_qualifier in Hq. simpl in Hq.
  apply Hq. exists (tm_int 0%Z). split.
  - apply multi_to_predicate_multistep. exact Hm.
  - split.
    + constructor.
    + constructor.
Qed.

Lemma entails_sound : forall Delta RGamma p q,
  entails Delta RGamma p q ->
  forall theta gamma,
    (forall x, value (gamma x)) ->
    context_formulas_hold theta gamma RGamma ->
    qualifier_holds (instantiate_formula theta gamma p) ->
    qualifier_holds (instantiate_formula theta gamma q).
Proof.
  intros Delta RGamma p q H. induction H; intros theta gamma Hv Hctx Hp;
    unfold qualifier_holds, predicate_holds in *; simpl in *; try tauto.
  all: try (eapply IHentails2; [exact Hv|exact Hctx|eapply IHentails1; eauto]).
  all: try (split; [eapply IHentails1|eapply IHentails2]; eauto).
  all: try (destruct Hp as [Hp|Hq]; [left|right]; eauto).
  all: try (destruct Hp as [Hp|Hq]; [eapply IHentails1|eapply IHentails2]; eauto).
  all: try (intro Hq; apply IHentails with (theta := theta) (gamma := gamma); eauto; split; assumption).
  all: try (exact (Hctx x T p H)).
  all: try (eapply H; eauto).
Qed.

CoInductive behavior_safe : tm -> Prop :=
  | BS_Value : forall v, value v -> behavior_safe v
  | BS_Step : forall t,
      (exists u, t --> u) ->
      (forall u, t --> u -> behavior_safe u) ->
      behavior_safe t.

Lemma behavior_safe_progress : forall t,
  behavior_safe t -> value t \/ exists u, t --> u.
Proof.
  intros t H. inversion H; subst; eauto.
Qed.

Lemma behavior_safe_step : forall t u,
  behavior_safe t -> t --> u -> behavior_safe u.
Proof.
  intros t u Hsafe Hstep. inversion Hsafe; subst.
  - exfalso. eapply value_no_step; eauto.
  - eauto.
Qed.

Lemma behavior_safe_multi : forall t u,
  behavior_safe t -> multi t u -> behavior_safe u.
Proof.
  intros t u Hsafe Hmulti. induction Hmulti.
  - exact Hsafe.
  - apply IHHmulti. eapply behavior_safe_step; eauto.
Qed.

Lemma value_int_canonical : forall v Delta Gamma,
  value v -> has_type Delta Gamma v Ty_Int -> exists z, v = tm_int z.
Proof.
  intros v Delta Gamma Hv HT. inversion Hv; subst; inversion HT; subst; eauto.
Qed.

Lemma value_arrow_canonical : forall v A B Delta Gamma,
  value v -> has_type Delta Gamma v (Ty_Arrow A B) ->
  (exists body, v = tm_abs A body) \/
  (exists metric body, v = tm_fix A B metric body).
Proof.
  intros v A B Delta Gamma Hv HT. inversion Hv; subst; inversion HT; subst; eauto.
Qed.

Lemma value_all_canonical : forall v T Delta Gamma,
  value v -> has_type Delta Gamma v (Ty_All T) -> exists body, v = tm_tabs body.
Proof.
  intros v T Delta Gamma Hv HT. inversion Hv; subst; inversion HT; subst; eauto.
Qed.

Definition canonical_for (T : ty) (v : tm) : Prop :=
  match T with
  | Ty_Int => exists z, v = tm_int z
  | Ty_Arrow A B =>
      (exists body, v = tm_abs A body) \/
      (exists metric body, v = tm_fix A B metric body)
  | Ty_All _ => exists body, v = tm_tabs body
  | _ => True
  end.

Lemma value_typing_canonical : forall v T Delta Gamma,
  value v -> has_type Delta Gamma v T -> canonical_for T v.
Proof.
  intros v T Delta Gamma Hv HT. destruct Hv; inversion HT; subst; simpl; eauto.
Qed.

Fixpoint term_relation (n : nat) (R : rty) (t : tm) {struct n} : Prop :=
  match n with
  | 0 => True
  | S k =>
      (value t -> value_relation k R t) /\
      (value t \/ exists u, t --> u) /\
      (forall u, t --> u -> term_relation k R u)
  end
with value_relation (n : nat) (R : rty) (t : tm) {struct n} : Prop :=
  match n with
  | 0 => True
  | S k =>
      match R with
      | R_Refine T p =>
          value t /\ canonical_for T t /\
          qualifier_holds (open_qualifier_tm p t)
      | R_Func R1 R2 =>
          value t /\
          (forall w, value_relation k R1 w ->
             term_relation k (R_Exists R1 R2) (tm_app t w))
      | R_Exists R1 R2 =>
          exists w, value w /\ value_relation k R1 w /\
            value t /\ value_relation k (open_rty_tm R2 w) t
      | R_Poly R1 =>
          value t /\ (forall U, locally_closed_ty U ->
            term_relation k (open_rty_ty R1 U) (tm_tapp t U))
      end
  end.

Lemma term_relation_progress : forall n R t,
  term_relation (S n) R t -> value t \/ exists u, t --> u.
Proof. intros n R t H. simpl in H. tauto. Qed.

Lemma value_relation_int_literal : forall k z,
  value_relation (S k)
    (R_Refine Ty_Int (Pred_Eq (tm_bvar 0) (tm_int z))) (tm_int z).
Proof.
  intros k z. simpl. split; [constructor|]. split.
  - exists z. reflexivity.
  - unfold qualifier_holds, predicate_holds, interpret_qualifier,
      operational_atoms. simpl. exists (tm_int z). split; [constructor|].
    split; [constructor|constructor].
Qed.

Lemma term_relation_int_literal : forall n z,
  term_relation n
    (R_Refine Ty_Int (Pred_Eq (tm_bvar 0) (tm_int z))) (tm_int z).
Proof.
  intros [|n] z; simpl; [exact I|]. split.
  - intros _. destruct n; [exact I|apply value_relation_int_literal].
  - split; [left; constructor|]. intros u Hstep.
    exfalso. eapply value_no_step; [constructor|exact Hstep].
Qed.

CoFixpoint term_relation_behavior_safe (R : rty) (t : tm)
    (Hrel : forall n, term_relation n R t) : behavior_safe t.
Proof.
  destruct (term_relation_progress 0 R t (Hrel 1)) as [Hv|[u Hstep]].
  - apply BS_Value. exact Hv.
  - eapply BS_Step.
    + eexists. exact Hstep.
    + intros u' Hu'. apply term_relation_behavior_safe with (R := R).
      intros [|n].
      * exact I.
      * destruct (Hrel (S (S n))) as [_ [_ Hsteps]].
        eapply Hsteps. exact Hu'.
Qed.

Lemma term_relation_behavior_safe_multi : forall R t t',
  (forall n, term_relation n R t) -> multi t t' -> behavior_safe t'.
Proof.
  intros R t t' Hrel Hmulti.
  eapply behavior_safe_multi.
  - eapply term_relation_behavior_safe. exact Hrel.
  - exact Hmulti.
Qed.

Lemma value_relation_nonzero_int : forall v,
  value_relation 1 (R_Refine Ty_Int (Pred_Ne (tm_bvar 0) (tm_int 0%Z))) v ->
  exists z, v = tm_int z /\ z <> 0%Z.
Proof.
  intros v H. simpl in H. destruct H as [Hv [Hcan Hq]].
  destruct Hcan as [z Hz]. subst v. exists z. split; [reflexivity|].
  intro Heq. subst z. unfold qualifier_holds, predicate_holds,
    Pred_Ne, interpret_qualifier in Hq. simpl in Hq. apply Hq.
  exists (tm_int 0%Z). split; [constructor|]. split; [constructor|constructor].
Qed.

Definition rcontext_realized (n : nat) (theta : type_substitution)
    (gamma : term_substitution) (RGamma : rcontext) : Prop :=
  term_substitution_closed gamma /\
  context_formulas_hold theta gamma RGamma /\
  forall x R, lookup_rcontext x RGamma = Some R ->
    value_relation n (instantiate_rty theta gamma R) (gamma x).

Lemma instantiate_ty_open_ty_rec : forall T k theta X U,
  ~ In X (fv_ty T) -> type_substitution_closed theta -> locally_closed_ty U ->
  instantiate_ty (type_subst_update theta X U)
    (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k U (instantiate_ty theta T).
Proof.
  induction T; intros k theta X U Hfresh Htheta HU; simpl in *.
  - destruct (Nat.eqb k n); simpl; [unfold type_subst_update; rewrite Nat.eqb_refl; reflexivity|reflexivity].
  - assert (Hneq : X <> a) by (intro E; subst; apply Hfresh; simpl; auto).
    unfold type_subst_update. rewrite (proj2 (Nat.eqb_neq X a) Hneq).
    assert (Hlc : lc_ty_at k (theta a)).
    { eapply lc_ty_at_monotone; [apply Htheta|lia]. }
    rewrite open_ty_rec_lc_at by exact Hlc. reflexivity.
  - f_equal.
    + eapply IHT1.
      * intro Hin. apply Hfresh. simpl. apply in_or_app. left. exact Hin.
      * exact Htheta.
      * exact HU.
    + eapply IHT2.
      * intro Hin. apply Hfresh. simpl. apply in_or_app. right. exact Hin.
      * exact Htheta.
      * exact HU.
  - f_equal. eapply IHT; [exact Hfresh|exact Htheta|exact HU].
  - reflexivity.
Qed.

Lemma instantiate_open_tm_ty_rec : forall t k theta gamma X U,
  ~ In X (ftv_tm t) -> type_substitution_closed theta -> locally_closed_ty U ->
  term_substitution_closed gamma ->
  instantiate (type_subst_update theta X U) gamma
    (open_tm_ty_rec k (Ty_FVar X) t) =
  open_tm_ty_rec k U (instantiate theta gamma t).
Proof.
  induction t; intros k theta gamma X U Hfresh Htheta HU Hclosed; simpl in *.
  - reflexivity.
  - assert (Hlc : locally_closed_tm (gamma a)) by apply Hclosed.
    assert (Hlc' : lc_tm_at k 0 (gamma a)).
    { eapply lc_tm_at_monotone; [exact Hlc|lia|lia]. }
    rewrite (open_tm_ty_rec_lc_at (gamma a) k 0 U Hlc'). reflexivity.
  - f_equal.
    + eapply instantiate_ty_open_ty_rec.
      * intro Hin. apply Hfresh. simpl. apply in_or_app. left. exact Hin.
      * exact Htheta.
      * exact HU.
    + eapply IHt.
      * intro Hin. apply Hfresh. simpl. apply in_or_app. right. exact Hin.
      * exact Htheta.
      * exact HU.
      * exact Hclosed.
  - f_equal.
    + eapply IHt1.
      * intro Hin. apply Hfresh. simpl. apply in_or_app. left. exact Hin.
      * exact Htheta.
      * exact HU.
      * exact Hclosed.
    + eapply IHt2.
      * intro Hin. apply Hfresh. simpl. apply in_or_app. right. exact Hin.
      * exact Htheta.
      * exact HU.
      * exact Hclosed.
  - f_equal. eapply IHt.
    + exact Hfresh.
    + exact Htheta.
    + exact HU.
    + exact Hclosed.
  - f_equal.
    + eapply IHt.
      * intro Hin. apply Hfresh. simpl. apply in_or_app. left. exact Hin.
      * exact Htheta.
      * exact HU.
      * exact Hclosed.
    + eapply instantiate_ty_open_ty_rec.
      * intro Hin. apply Hfresh. simpl. apply in_or_app. right. exact Hin.
      * exact Htheta.
      * exact HU.
  - reflexivity.
  - f_equal.
    + eapply IHt1.
      * intro Hin. apply Hfresh. simpl. apply in_or_app. left. exact Hin.
      * exact Htheta.
      * exact HU.
      * exact Hclosed.
    + eapply IHt2.
      * intro Hin. apply Hfresh. simpl. apply in_or_app. right. exact Hin.
      * exact Htheta.
      * exact HU.
      * exact Hclosed.
  - f_equal.
    + eapply IHt1.
      * intro Hin. apply Hfresh. simpl. apply in_or_app. left. exact Hin.
      * exact Htheta.
      * exact HU.
      * exact Hclosed.
    + eapply IHt2.
      * intro Hin. apply Hfresh. simpl. apply in_or_app. right. exact Hin.
      * exact Htheta.
      * exact HU.
      * exact Hclosed.
  - f_equal.
    + eapply instantiate_ty_open_ty_rec.
      * intro Hin. apply Hfresh. simpl. apply in_or_app. left. exact Hin.
      * exact Htheta.
      * exact HU.
    + eapply instantiate_ty_open_ty_rec.
      * intro Hin. apply Hfresh. simpl. apply in_or_app. right. apply in_or_app. left. exact Hin.
      * exact Htheta.
      * exact HU.
    + eapply IHt1.
      * intro Hin. apply Hfresh. simpl. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hin.
      * exact Htheta.
      * exact HU.
      * exact Hclosed.
    + eapply IHt2.
      * intro Hin. apply Hfresh. simpl. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact Hin.
      * exact Htheta.
      * exact HU.
      * exact Hclosed.
  - f_equal.
    + eapply IHt1.
      * intro Hin. apply Hfresh. simpl. apply in_or_app. left. exact Hin.
      * exact Htheta.
      * exact HU.
      * exact Hclosed.
    + eapply IHt2.
      * intro Hin. apply Hfresh. simpl. apply in_or_app. right. apply in_or_app. left. exact Hin.
      * exact Htheta.
      * exact HU.
      * exact Hclosed.
    + eapply IHt3.
      * intro Hin. apply Hfresh. simpl. apply in_or_app. right. apply in_or_app. right. exact Hin.
      * exact Htheta.
      * exact HU.
      * exact Hclosed.
Qed.

Lemma instantiate_open_pred_ty_rec : forall p k theta gamma X U,
  ~ In X (ftv_pred p) -> type_substitution_closed theta ->
  locally_closed_ty U -> term_substitution_closed gamma ->
  instantiate_pred (type_subst_update theta X U) gamma
    (open_pred_ty_rec k (Ty_FVar X) p) =
  open_pred_ty_rec k U (instantiate_pred theta gamma p).
Proof.
  induction p; intros k theta gamma X U Hfresh Htheta HU Hclosed; simpl in *.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + eapply instantiate_open_tm_ty_rec; [simpl in Hfresh; intuition|assumption|assumption|assumption].
    + eapply instantiate_open_tm_ty_rec; [simpl in Hfresh; intuition|assumption|assumption|assumption].
  - f_equal.
    + eapply instantiate_open_tm_ty_rec; [simpl in Hfresh; intuition|assumption|assumption|assumption].
    + eapply instantiate_open_tm_ty_rec; [simpl in Hfresh; intuition|assumption|assumption|assumption].
  - f_equal.
    + eapply instantiate_open_tm_ty_rec; [simpl in Hfresh; intuition|assumption|assumption|assumption].
    + eapply instantiate_open_tm_ty_rec; [simpl in Hfresh; intuition|assumption|assumption|assumption].
  - f_equal.
    + eapply IHp1; [simpl in Hfresh; intuition|assumption|assumption|assumption].
    + eapply IHp2; [simpl in Hfresh; intuition|assumption|assumption|assumption].
  - f_equal.
    + eapply IHp1; [simpl in Hfresh; intuition|assumption|assumption|assumption].
    + eapply IHp2; [simpl in Hfresh; intuition|assumption|assumption|assumption].
  - f_equal. eapply IHp; eauto.
Qed.

Lemma instantiate_open_rty_ty_rec : forall R k theta gamma X U,
  ~ In X (ftv_rty R) -> type_substitution_closed theta ->
  locally_closed_ty U -> term_substitution_closed gamma ->
  instantiate_rty (type_subst_update theta X U) gamma
    (open_rty_ty_rec k (Ty_FVar X) R) =
  open_rty_ty_rec k U (instantiate_rty theta gamma R).
Proof.
  induction R; intros k theta gamma X U Hfresh Htheta HU Hclosed; simpl in *.
  - f_equal.
    + eapply instantiate_ty_open_ty_rec; [simpl in Hfresh; intuition|assumption|assumption].
    + eapply instantiate_open_pred_ty_rec; [simpl in Hfresh; intuition|assumption|assumption|assumption].
  - f_equal.
    + eapply IHR1; [simpl in Hfresh; intuition|assumption|assumption|assumption].
    + eapply IHR2; [simpl in Hfresh; intuition|assumption|assumption|assumption].
  - f_equal.
    + eapply IHR1; [simpl in Hfresh; intuition|assumption|assumption|assumption].
    + eapply IHR2; [simpl in Hfresh; intuition|assumption|assumption|assumption].
  - f_equal. eapply IHR; [exact Hfresh|assumption|assumption|assumption].
Qed.

Lemma instantiate_open_rty_ty : forall R theta gamma X U,
  ~ In X (ftv_rty R) -> type_substitution_closed theta ->
  locally_closed_ty U -> term_substitution_closed gamma ->
  instantiate_rty (type_subst_update theta X U) gamma
    (open_rty_ty R (Ty_FVar X)) =
  open_rty_ty (instantiate_rty theta gamma R) U.
Proof.
  intros. unfold open_rty_ty. apply instantiate_open_rty_ty_rec; assumption.
Qed.

Lemma instantiate_tm_update_irrelevant : forall t theta gamma x w,
  ~ In x (fv_tm t) ->
  instantiate theta (term_subst_update gamma x w) t = instantiate theta gamma t.
Proof.
  induction t; intros theta gamma x w Hfresh; simpl in *.
  - reflexivity.
  - assert (Hneq : x <> a) by (intro E; subst; apply Hfresh; simpl; auto).
    unfold term_subst_update. rewrite (proj2 (Nat.eqb_neq x a) Hneq). reflexivity.
  - f_equal. eapply IHt; exact Hfresh.
  - f_equal.
    + eapply IHt1; [simpl in Hfresh; intuition].
    + eapply IHt2; [simpl in Hfresh; intuition].
  - f_equal. eapply IHt; exact Hfresh.
  - f_equal. eapply IHt; exact Hfresh.
  - reflexivity.
  - f_equal.
    + eapply IHt1; [simpl in Hfresh; intuition].
    + eapply IHt2; [simpl in Hfresh; intuition].
  - f_equal.
    + eapply IHt1; [simpl in Hfresh; intuition].
    + eapply IHt2; [simpl in Hfresh; intuition].
  - f_equal.
    + eapply IHt1; [simpl in Hfresh; intuition].
    + eapply IHt2; [simpl in Hfresh; intuition].
  - f_equal.
    + eapply IHt1.
      * intro Hin. apply Hfresh. simpl. apply in_or_app. left. exact Hin.
    + eapply IHt2.
      * intro Hin. apply Hfresh. simpl. apply in_or_app. right. apply in_or_app. left. exact Hin.
    + eapply IHt3.
      * intro Hin. apply Hfresh. simpl. apply in_or_app. right. apply in_or_app. right. exact Hin.
Qed.

Lemma open_tm_rec_fv_incl : forall t k y q,
  In q (fv_tm (open_tm_rec k (tm_fvar y) t)) -> In q (fv_tm t) \/ q = y.
Proof.
  induction t; intros k y q Hin; simpl in *.
  - destruct (Nat.eqb k n); simpl in Hin.
    + destruct Hin as [E|[]]. right. symmetry. exact E.
    + contradiction.
  - destruct Hin as [E|[]]. left. simpl. left. exact E.
  - apply IHt in Hin. destruct Hin as [Hin|E]; [left; exact Hin|right; exact E].
  - apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
    + apply IHt1 in Hin. destruct Hin; [left; apply in_or_app; left; assumption|right; assumption].
    + apply IHt2 in Hin. destruct Hin; [left; apply in_or_app; right; assumption|right; assumption].
  - apply IHt in Hin. destruct Hin as [Hin|E]; [left; exact Hin|right; exact E].
  - apply IHt in Hin. destruct Hin as [Hin|E]; [left; exact Hin|right; exact E].
  - contradiction.
  - apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
    + apply IHt1 in Hin. destruct Hin; [left; apply in_or_app; left; assumption|right; assumption].
    + apply IHt2 in Hin. destruct Hin; [left; apply in_or_app; right; assumption|right; assumption].
  - apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
    + apply IHt1 in Hin. destruct Hin; [left; apply in_or_app; left; assumption|right; assumption].
    + apply IHt2 in Hin. destruct Hin; [left; apply in_or_app; right; assumption|right; assumption].
  - apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
    + apply IHt1 in Hin. destruct Hin; [left; apply in_or_app; left; assumption|right; assumption].
    + apply IHt2 in Hin. destruct Hin; [left; apply in_or_app; right; assumption|right; assumption].
  - apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
    + apply IHt1 in Hin. destruct Hin; [left; apply in_or_app; left; assumption|right; assumption].
    + apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
      * apply IHt2 in Hin. destruct Hin; [left; apply in_or_app; right; apply in_or_app; left; assumption|right; assumption].
      * apply IHt3 in Hin. destruct Hin; [left; apply in_or_app; right; apply in_or_app; right; assumption|right; assumption].
Qed.

Lemma open_pred_tm_fv_incl : forall p k y z,
  In z (fv_pred (open_pred_tm_rec k (tm_fvar y) p)) -> In z (fv_pred p) \/ z = y.
Proof.
  induction p; intros k y z Hin; simpl in *; try contradiction.
  - apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
    + apply open_tm_rec_fv_incl in Hin. destruct Hin as [Hin|E].
      * left. simpl. apply in_or_app. left. exact Hin.
      * right. exact E.
    + apply open_tm_rec_fv_incl in Hin. destruct Hin as [Hin|E].
      * left. simpl. apply in_or_app. right. exact Hin.
      * right. exact E.
  - apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
    + apply open_tm_rec_fv_incl in Hin. destruct Hin as [Hin|E].
      * left. simpl. apply in_or_app. left. exact Hin.
      * right. exact E.
    + apply open_tm_rec_fv_incl in Hin. destruct Hin as [Hin|E].
      * left. simpl. apply in_or_app. right. exact Hin.
      * right. exact E.
  - apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
    + apply open_tm_rec_fv_incl in Hin. destruct Hin as [Hin|E].
      * left. simpl. apply in_or_app. left. exact Hin.
      * right. exact E.
    + apply open_tm_rec_fv_incl in Hin. destruct Hin as [Hin|E].
      * left. simpl. apply in_or_app. right. exact Hin.
      * right. exact E.
  - apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
    + apply IHp1 in Hin. destruct Hin; [left; simpl; apply in_or_app; left; assumption|right; assumption].
    + apply IHp2 in Hin. destruct Hin; [left; simpl; apply in_or_app; right; assumption|right; assumption].
  - apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
    + apply IHp1 in Hin. destruct Hin; [left; simpl; apply in_or_app; left; assumption|right; assumption].
    + apply IHp2 in Hin. destruct Hin; [left; simpl; apply in_or_app; right; assumption|right; assumption].
  - apply IHp in Hin. destruct Hin as [Hin|E]; [left; exact Hin|right; exact E].
Qed.

Lemma open_pred_fresh_notin : forall p y x,
  ~ In x (fv_pred p) -> x <> y ->
  ~ In x (fv_pred (open_qualifier_tm p (tm_fvar y))).
Proof.
  intros p y x Hfresh Hneq Hin. unfold open_qualifier_tm in Hin.
  apply open_pred_tm_fv_incl in Hin. destruct Hin; [apply Hfresh; assumption|congruence].
Qed.

Lemma instantiate_pred_update_irrelevant : forall p theta gamma x w,
  ~ In x (fv_pred p) ->
  instantiate_pred theta (term_subst_update gamma x w) p =
  instantiate_pred theta gamma p.
Proof.
  induction p; intros theta gamma x w Hfresh; simpl in *.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + eapply instantiate_tm_update_irrelevant; simpl in Hfresh; intuition.
    + eapply instantiate_tm_update_irrelevant; simpl in Hfresh; intuition.
  - f_equal.
    + eapply instantiate_tm_update_irrelevant; simpl in Hfresh; intuition.
    + eapply instantiate_tm_update_irrelevant; simpl in Hfresh; intuition.
  - f_equal.
    + eapply instantiate_tm_update_irrelevant; simpl in Hfresh; intuition.
    + eapply instantiate_tm_update_irrelevant; simpl in Hfresh; intuition.
  - f_equal.
    + eapply IHp1; [simpl in Hfresh; intuition].
    + eapply IHp2; [simpl in Hfresh; intuition].
  - f_equal.
    + eapply IHp1; [simpl in Hfresh; intuition].
    + eapply IHp2; [simpl in Hfresh; intuition].
  - f_equal. eapply IHp; exact Hfresh.
Qed.

Lemma instantiate_open_tm_rec : forall t k theta gamma x w,
  ~ In x (fv_tm t) ->
  term_substitution_closed gamma ->
  instantiate theta (term_subst_update gamma x w)
    (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k w (instantiate theta gamma t).
Proof.
  induction t; intros k theta gamma x w Hfresh Hclosed; simpl in *.
  - destruct (Nat.eqb k n) eqn:E; simpl.
    + unfold term_subst_update. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - assert (Hneq : x <> a) by (intro E; subst; apply Hfresh; simpl; auto).
    unfold term_subst_update. rewrite (proj2 (Nat.eqb_neq x a) Hneq).
    assert (Hlc : locally_closed_tm (gamma a)) by (apply Hclosed).
    assert (Hlc' : lc_tm_at 0 k (gamma a)).
    { eapply lc_tm_at_monotone; [exact Hlc|lia|lia]. }
    rewrite (open_tm_rec_lc_at (gamma a) 0 k w Hlc'). reflexivity.
  - f_equal. eapply IHt; [exact Hfresh|exact Hclosed].
  - f_equal.
    + eapply IHt1; [simpl in Hfresh; intuition|exact Hclosed].
    + eapply IHt2; [simpl in Hfresh; intuition|exact Hclosed].
  - f_equal. eapply IHt; [exact Hfresh|exact Hclosed].
  - f_equal. eapply IHt; [exact Hfresh|exact Hclosed].
  - reflexivity.
  - f_equal.
    + eapply IHt1; [simpl in Hfresh; intuition|exact Hclosed].
    + eapply IHt2; [simpl in Hfresh; intuition|exact Hclosed].
  - f_equal.
    + eapply IHt1; [simpl in Hfresh; intuition|exact Hclosed].
    + eapply IHt2; [simpl in Hfresh; intuition|exact Hclosed].
  - f_equal.
    + eapply IHt1; [simpl in Hfresh; intuition|exact Hclosed].
    + eapply IHt2; [simpl in Hfresh; intuition|exact Hclosed].
  - f_equal.
    + eapply IHt1; [simpl in Hfresh; intuition|exact Hclosed].
    + eapply IHt2.
      * intro Hin. apply Hfresh. simpl. apply in_or_app. right.
        apply in_or_app. left. exact Hin.
      * exact Hclosed.
    + eapply IHt3.
      * intro Hin. apply Hfresh. simpl. apply in_or_app. right.
        apply in_or_app. right. exact Hin.
      * exact Hclosed.
Qed.

Lemma instantiate_open_pred_tm_rec : forall p k theta gamma x w,
  ~ In x (fv_pred p) -> term_substitution_closed gamma ->
  instantiate_pred theta (term_subst_update gamma x w)
    (open_pred_tm_rec k (tm_fvar x) p) =
  open_pred_tm_rec k w (instantiate_pred theta gamma p).
Proof.
  induction p; intros k theta gamma x w Hfresh Hclosed; simpl in *.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + eapply instantiate_open_tm_rec; [simpl in Hfresh; intuition|exact Hclosed].
    + eapply instantiate_open_tm_rec; [simpl in Hfresh; intuition|exact Hclosed].
  - f_equal.
    + eapply instantiate_open_tm_rec; [simpl in Hfresh; intuition|exact Hclosed].
    + eapply instantiate_open_tm_rec; [simpl in Hfresh; intuition|exact Hclosed].
  - f_equal.
    + eapply instantiate_open_tm_rec; [simpl in Hfresh; intuition|exact Hclosed].
    + eapply instantiate_open_tm_rec; [simpl in Hfresh; intuition|exact Hclosed].
  - f_equal.
    + eapply IHp1; [simpl in Hfresh; intuition|exact Hclosed].
    + eapply IHp2; [simpl in Hfresh; intuition|exact Hclosed].
  - f_equal.
    + eapply IHp1; [simpl in Hfresh; intuition|exact Hclosed].
    + eapply IHp2; [simpl in Hfresh; intuition|exact Hclosed].
  - f_equal. eapply IHp; [exact Hfresh|exact Hclosed].
Qed.

Lemma instantiate_formula_eq_pred : forall theta gamma p,
  instantiate_formula theta gamma p = instantiate_pred theta gamma p.
Proof.
  intros theta gamma p. induction p; simpl; try reflexivity;
    rewrite ?IHp, ?IHp1, ?IHp2; reflexivity.
Qed.

Lemma instantiate_rty_update_irrelevant : forall R theta gamma x w,
  ~ In x (fv_rty R) ->
  instantiate_rty theta (term_subst_update gamma x w) R =
  instantiate_rty theta gamma R.
Proof.
  induction R; intros theta gamma x w Hfresh; simpl in *.
  - f_equal. eapply instantiate_pred_update_irrelevant; exact Hfresh.
  - f_equal.
    + eapply IHR1; [simpl in Hfresh; intuition].
    + eapply IHR2; [simpl in Hfresh; intuition].
  - f_equal.
    + eapply IHR1; [simpl in Hfresh; intuition].
    + eapply IHR2; [simpl in Hfresh; intuition].
  - f_equal. eapply IHR; exact Hfresh.
Qed.

Lemma instantiate_open_rty_tm_rec : forall R k theta gamma x w,
  ~ In x (fv_rty R) -> term_substitution_closed gamma ->
  instantiate_rty theta (term_subst_update gamma x w)
    (open_rty_tm_rec k (tm_fvar x) R) =
  open_rty_tm_rec k w (instantiate_rty theta gamma R).
Proof.
  induction R; intros k theta gamma x w Hfresh Hclosed; simpl in *.
  - f_equal. eapply instantiate_open_pred_tm_rec; eauto.
  - f_equal.
    + eapply IHR1; [simpl in Hfresh; intuition|exact Hclosed].
    + eapply IHR2; [simpl in Hfresh; intuition|exact Hclosed].
  - f_equal.
    + eapply IHR1; [simpl in Hfresh; intuition|exact Hclosed].
    + eapply IHR2; [simpl in Hfresh; intuition|exact Hclosed].
  - f_equal. eapply IHR; [exact Hfresh|exact Hclosed].
Qed.

Lemma instantiate_open_rty_tm : forall R theta gamma x w,
  ~ In x (fv_rty R) -> term_substitution_closed gamma ->
  instantiate_rty theta (term_subst_update gamma x w)
    (open_rty_tm R (tm_fvar x)) =
  open_rty_tm (instantiate_rty theta gamma R) w.
Proof.
  intros. unfold open_rty_tm. apply instantiate_open_rty_tm_rec; assumption.
Qed.

Lemma rcontext_realized_update : forall n theta gamma RGamma x R w,
  rcontext_realized (S n) theta gamma RGamma ->
  lookup_rcontext x RGamma = None ->
  (forall y Q, lookup_rcontext y RGamma = Some Q -> ~ In x (fv_rty Q)) ->
  ~ In x (fv_rty R) ->
  value w ->
  value_relation (S n) (instantiate_rty theta gamma R) w ->
  rcontext_realized (S n) theta (term_subst_update gamma x w)
    (update_rcontext RGamma x R).
Proof.
  intros n theta gamma RGamma x R w [Hclosed [Hform Henv]] Hlookup Hfresh HfreshR Hwv Hrel.
  split.
  - eapply term_subst_update_closed; [exact Hclosed|apply value_regular; exact Hwv].
  - split.
    + intros y T p Hlook.
      simpl in Hlook. destruct (Nat.eqb y x) eqn:E.
      * apply Nat.eqb_eq in E. subst y. inversion Hlook; subst.
        simpl in Hrel. destruct Hrel as [_ [_ Hqual]].
        rewrite instantiate_formula_eq_pred.
        unfold open_qualifier_tm, open_qualifier_tm_rec in *.
        rewrite (@instantiate_open_pred_tm_rec p 0 theta gamma x w).
        -- exact Hqual.
        -- simpl in HfreshR. exact HfreshR.
        -- exact Hclosed.
      * apply Nat.eqb_neq in E.
        assert (Hold : lookup_rcontext y RGamma = Some (R_Refine T p)).
        { exact Hlook. }
        specialize (Hform y T p Hold).
        rewrite instantiate_formula_eq_pred in *.
        rewrite (instantiate_pred_update_irrelevant
          (open_qualifier_tm p (tm_fvar y)) theta gamma x w).
        -- exact Hform.
        -- apply open_pred_fresh_notin.
           ++ specialize (Hfresh y (R_Refine T p) Hold). simpl in Hfresh. exact Hfresh.
           ++ intro Heq. apply E. symmetry. exact Heq.
    + intros y Q Hlook. simpl in Hlook. destruct (Nat.eqb y x) eqn:E.
      * apply Nat.eqb_eq in E. subst y. inversion Hlook; subst.
        rewrite (instantiate_rty_update_irrelevant Q theta gamma x w) by exact HfreshR.
        unfold term_subst_update. rewrite Nat.eqb_refl. exact Hrel.
      * apply Nat.eqb_neq in E.
        assert (Hold : lookup_rcontext y RGamma = Some Q).
        { exact Hlook. }
        specialize (Henv y Q Hold).
        rewrite (instantiate_rty_update_irrelevant Q theta gamma x w).
        -- unfold term_subst_update. rewrite (proj2 (Nat.eqb_neq x y) (fun Heq => E (eq_sym Heq))). exact Henv.
        -- eapply Hfresh; eauto.
Qed.

Lemma value_relation_term : forall n R v,
  value v -> value_relation n R v -> term_relation (S n) R v.
Proof.
  intros n R v Hv Hrel. destruct n; simpl.
  - split; [intros _; exact I|]. split; [left; exact Hv|].
    intros u Hstep. exfalso. eapply value_no_step; eauto.
  - split; [intros _; exact Hrel|]. split; [left; exact Hv|].
    intros u Hstep. exfalso. eapply value_no_step; eauto.
Qed.

Inductive multi_steps : nat -> tm -> tm -> Prop :=
| MS_Refl : forall t, multi_steps 0 t t
| MS_Step : forall n t u v, t --> u -> multi_steps n u v ->
    multi_steps (S n) t v.

Lemma multi_has_steps : forall t u,
  multi t u -> exists n, multi_steps n t u.
Proof.
  intros t u H. induction H as [t|t m u Hstep Hmulti IH].
  - exists 0. constructor.
  - destruct IH as [n Hn]. exists (S n). econstructor; eauto.
Qed.

Lemma term_relation_multi_steps : forall n R t u,
  term_relation (S n) R t -> multi_steps n t u ->
  value u \/ exists v, u --> v.
Proof.
  induction n; intros R t u Hrel Hsteps.
  - inversion Hsteps; subst. eapply term_relation_progress. exact Hrel.
  - inversion Hsteps as [t0|n0 t0 t1 u0 Hstep Htail]; subst.
    simpl in Hrel. destruct Hrel as [_ [_ Hcont]].
    eapply IHn; [eapply Hcont; exact Hstep|exact Htail].
Qed.

Lemma term_relation_multi_value : forall n R t v,
  term_relation (S (S n)) R t -> multi_steps n t v -> value v ->
  value_relation 1 R v.
Proof.
  induction n; intros R t v Hrel Hsteps Hv.
  - inversion Hsteps; subst. simpl in Hrel. destruct Hrel as [Hval _].
    apply Hval. exact Hv.
  - inversion Hsteps as [t0|n0 t0 t1 v0 Hstep Htail]; subst.
    simpl in Hrel. destruct Hrel as [_ [_ Hcont]].
    eapply IHn; [eapply Hcont; exact Hstep|exact Htail|exact Hv].
Qed.

Lemma term_relation_reachable_progress : forall R t u,
  (forall n, term_relation n R t) -> multi t u ->
  value u \/ exists v, u --> v.
Proof.
  intros R t u Hrel Hmulti. destruct (multi_has_steps _ _ Hmulti) as [n Hn].
  eapply term_relation_multi_steps with (n := n) (R := R) (t := t); eauto.
Qed.

Lemma wf_ty_locally_closed : forall Delta T,
  wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T H. induction H.
  - constructor.
  - constructor; assumption.
  - constructor. eapply lc_ty_at_open_inv with (X := fresh L).
    specialize (H0 (fresh L) (fresh_notin L)). exact H0.
  - constructor.
Qed.

Lemma has_type_locally_closed : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T H. induction H.
  - constructor.
  - apply lc_tm_abs.
    + eapply wf_ty_locally_closed; eassumption.
    + eapply lc_tm_at_open_tm_inv with (x := fresh L).
      specialize (H1 (fresh L) (fresh_notin L)). exact H1.
  - apply lc_tm_app; assumption.
  - apply lc_tm_tabs. eapply lc_tm_at_open_ty_inv with (X := fresh L).
    specialize (H0 (fresh L) (fresh_notin L)). exact H0.
  - apply lc_tm_tapp; [assumption|eapply wf_ty_locally_closed; eassumption].
  - constructor.
  - apply lc_tm_div; assumption.
  - apply lc_tm_arith; assumption.
  - apply lc_tm_fix.
    + eapply wf_ty_locally_closed; eassumption.
    + eapply wf_ty_locally_closed; eassumption.
    + eapply lc_tm_at_open_tm_inv with (x := fresh L).
      specialize (H2 (fresh L) (fresh_notin L)). exact H2.
    + unfold open_fix_body in H4.
      pose proof (H4 (fresh L) (fresh (fresh L :: L))
        (fresh_notin L) (fresh_notin (fresh L :: L))) as Hbody.
      eapply lc_tm_at_open_tm_inv with (k := 0) (x := fresh (fresh L :: L)) in Hbody.
      eapply lc_tm_at_open_tm_inv with (k := 1) (x := fresh L) in Hbody.
      exact Hbody.
  - apply lc_tm_ifzero; assumption.
Qed.

Lemma has_rtype_locally_closed : forall Delta RGamma t R,
  has_rtype Delta RGamma t R -> locally_closed_tm t.
Proof.
  intros Delta RGamma t R H.
  eapply (has_type_locally_closed Delta (erase_context RGamma) t (erase R)).
  eapply has_rtype_erases. exact H.
Qed.

Lemma instantiate_ty_locally_closed_at : forall K T theta,
  lc_ty_at K T -> type_substitution_closed theta ->
  lc_ty_at K (instantiate_ty theta T).
Proof.
  intros K T. revert K. induction T; intros K theta Hlc Htheta; simpl in *; inversion Hlc; subst.
  - constructor. assumption.
  - eapply lc_ty_at_monotone; [apply Htheta|lia].
  - constructor; [eapply IHT1|eapply IHT2]; eauto.
  - constructor. eapply IHT with (K := S K); eauto.
  - constructor.
Qed.

Lemma instantiate_locally_closed_at : forall t K k theta gamma,
  lc_tm_at K k t -> type_substitution_closed theta ->
  term_substitution_closed gamma ->
  lc_tm_at K k (instantiate theta gamma t).
Proof.
  induction t; intros K k theta gamma Hlc Htheta Hgamma; simpl in *;
    inversion Hlc; subst.
  - constructor. assumption.
  - unfold term_substitution_closed in Hgamma.
    eapply lc_tm_at_monotone; [apply Hgamma|lia|lia].
  - apply lc_tm_abs.
    + eapply instantiate_ty_locally_closed_at; eauto.
    + eapply IHt; eauto.
  - apply lc_tm_app; [eapply IHt1|eapply IHt2]; eauto.
  - apply lc_tm_tabs. eapply IHt; eauto.
  - apply lc_tm_tapp.
    + eapply IHt; eauto.
    + eapply instantiate_ty_locally_closed_at; eauto.
  - constructor.
  - apply lc_tm_div; [eapply IHt1|eapply IHt2]; eauto.
  - apply lc_tm_arith; [eapply IHt1|eapply IHt2]; eauto.
  - apply lc_tm_fix.
    + eapply instantiate_ty_locally_closed_at; eauto.
    + eapply instantiate_ty_locally_closed_at; eauto.
    + eapply IHt1; eauto.
    + eapply IHt2; eauto.
  - apply lc_tm_ifzero; [eapply IHt1|eapply IHt2|eapply IHt3]; eauto.
Qed.

Lemma instantiate_locally_closed : forall t theta gamma,
  locally_closed_tm t -> type_substitution_closed theta ->
  term_substitution_closed gamma -> locally_closed_tm (instantiate theta gamma t).
Proof. intros. eapply instantiate_locally_closed_at; eauto. Qed.

Lemma step_preserves_lc : forall t u,
  t --> u -> locally_closed_tm t -> locally_closed_tm u.
Proof.
  intros t u Hstep. induction Hstep; intros Hlc; inversion Hlc; subst.
  - inversion H5; subst. eapply open_tm_preserves_lc_at; eassumption.
  - apply lc_tm_app; [eapply IHHstep; eassumption|assumption].
  - apply lc_tm_app; [assumption|eapply IHHstep; eassumption].
  - inversion H5; subst. eapply open_tm_ty_preserves_lc_at; eassumption.
  - apply lc_tm_tapp; [eapply IHHstep; eassumption|assumption].
  - apply lc_tm_div; [eapply IHHstep; eassumption|assumption].
  - apply lc_tm_div; [assumption|eapply IHHstep; eassumption].
  - constructor.
  - apply lc_tm_arith; [eapply IHHstep; eassumption|assumption].
  - apply lc_tm_arith; [assumption|eapply IHHstep; eassumption].
  - constructor.
  - unfold open_fix_body. inversion H5; subst.
    eapply open_tm_preserves_lc_at.
    + eapply open_tm_preserves_lc_at; eassumption.
    + exact H6.
  - apply lc_tm_ifzero; [eapply IHHstep; eassumption|assumption|assumption].
  - assumption.
  - assumption.
Qed.

Lemma rty_size_open_tm_rec : forall k R w,
  rty_size (open_rty_tm_rec k w R) = rty_size R.
Proof.
  intros k R. revert k. induction R; intros k w; simpl; try reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR. reflexivity.
Qed.

Lemma rty_size_open_tm : forall R w,
  rty_size (open_rty_tm R w) = rty_size R.
Proof. intros. apply rty_size_open_tm_rec. Qed.

Lemma rty_size_open_ty_rec : forall k R U,
  rty_size (open_rty_ty_rec k U R) = rty_size R.
Proof.
  intros k R. revert k. induction R; intros k U; simpl; try reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR. reflexivity.
Qed.

Lemma rty_size_open_ty : forall R U,
  rty_size (open_rty_ty R U) = rty_size R.
Proof. intros. apply rty_size_open_ty_rec. Qed.

Equations sem_value (R : rty) (v : tm) : Prop by wf (rty_size R) lt :=
sem_value (R_Refine T p) v :=
  value v /\ canonical_for T v /\ qualifier_holds (open_qualifier_tm p v);
sem_value (R_Func R1 R2) v :=
  value v /\ (forall w, sem_value R1 w -> behavior_safe (tm_app v w));
sem_value (R_Exists R1 R2) v :=
  exists w, value w /\ sem_value R1 w /\ value v /\
    sem_value (open_rty_tm R2 w) v;
sem_value (R_Poly R1) v :=
  value v /\ (forall U, locally_closed_ty U -> behavior_safe (tm_tapp v U)).
Next Obligation. simpl. lia. Qed.
Next Obligation. simpl. lia. Qed.
Next Obligation. rewrite rty_size_open_tm. simpl. lia. Qed.

Definition sem_context_realized (theta : type_substitution)
    (gamma : term_substitution) (RGamma : rcontext) : Prop :=
  term_substitution_closed gamma /\
  context_formulas_hold theta gamma RGamma /\
  forall x R, lookup_rcontext x RGamma = Some R ->
    sem_value (instantiate_rty theta gamma R) (gamma x).

CoFixpoint behavior_safe_app (f a : tm)
    (Hf : behavior_safe f) (Ha : behavior_safe a)
    (Hla : locally_closed_tm a)
    (Hready : forall vf va, value vf -> value va ->
       behavior_safe (tm_app vf va)) : behavior_safe (tm_app f a).
Proof.
  destruct Hf as [vf Hvf|f0 Hsome Hnext].
  - destruct Ha as [va Hva|a0 Hsomea Hnexta].
    + apply Hready; assumption.
    + destruct Hsomea as [a' Hsa].
      eapply BS_Step.
      * exists (tm_app vf a'). apply ST_App2; assumption.
      * intros u Hu. inversion Hu; subst; try solve [exfalso; eapply value_no_step; eauto].
        eapply behavior_safe_app.
        -- constructor. exact Hvf.
        -- eapply Hnexta. eassumption.
        -- eapply step_preserves_lc; eassumption.
        -- exact Hready.
  - destruct Hsome as [f' Hsf].
    eapply BS_Step.
    + exists (tm_app f' a). apply ST_App1; assumption.
    + intros u Hu. inversion Hu; subst;
        try solve [exfalso; eapply value_no_step; eauto];
        try solve [inversion Hsf].
      eapply behavior_safe_app.
      * eapply Hnext. eassumption.
      * exact Ha.
      * exact Hla.
      * exact Hready.
Qed.

Lemma behavior_safe_beta : forall T body v,
  value (tm_abs T body) -> value v ->
  behavior_safe (open_tm body v) ->
  behavior_safe (tm_app (tm_abs T body) v).
Proof.
  intros T body v Habs Hv Hbody. eapply BS_Step.
  - exists (open_tm body v). apply ST_AppAbs; assumption.
  - intros u Hu. inversion Hu; subst.
    + exact Hbody.
    + exfalso. eapply value_no_step; eauto.
    + exfalso. eapply value_no_step; eauto.
    + inversion Habs.
Qed.

Lemma behavior_safe_tbeta : forall body U,
  value (tm_tabs body) -> locally_closed_ty U ->
  behavior_safe (open_tm_ty body U) ->
  behavior_safe (tm_tapp (tm_tabs body) U).
Proof.
  intros body U Htabs HU Hbody. eapply BS_Step.
  - exists (open_tm_ty body U). apply ST_TAppTabs; assumption.
  - intros u Hu. inversion Hu; subst.
    + exact Hbody.
    + inversion Htabs.
Qed.

Lemma behavior_safe_ifzero : forall n t0 t1 u,
  locally_closed_tm t0 -> locally_closed_tm t1 ->
  tm_ifzero (tm_int n) t0 t1 --> u -> behavior_safe u ->
  behavior_safe (tm_ifzero (tm_int n) t0 t1).
Proof.
  intros n t0 t1 u Hlc0 Hlc1 Hstep Hsafe. eapply BS_Step.
  - exists u. exact Hstep.
  - intros v Hv. inversion Hv; subst.
    + exfalso. inversion H3.
    + destruct n; [exact Hsafe|].
      exfalso. eapply value_no_step; [constructor|eassumption].
    + destruct n; [exfalso; eapply value_no_step; [constructor|eassumption]|exact Hsafe].
Qed.

CoFixpoint behavior_safe_tapp (t : tm) (T : ty)
    (Ht : behavior_safe t) (HT : locally_closed_ty T)
    (Hready : forall v, value v -> behavior_safe (tm_tapp v T)) :
    behavior_safe (tm_tapp t T).
Proof.
  destruct Ht as [v Hv|t0 Hsome Hnext].
  - apply Hready. exact Hv.
  - destruct Hsome as [t' Hstep]. eapply BS_Step.
    + exists (tm_tapp t' T). apply ST_TApp; assumption.
    + intros u Hu. inversion Hu; subst; try solve [inversion Hstep].
      eapply behavior_safe_tapp; eauto.
Qed.

CoFixpoint behavior_safe_div (a b : tm)
    (Ha : behavior_safe a) (Hb : behavior_safe b)
    (Hlb : locally_closed_tm b)
    (Hready : forall va vb, value va -> value vb -> behavior_safe (tm_div va vb)) :
    behavior_safe (tm_div a b).
Proof.
  destruct Ha as [va Hva|a0 Hsomea Hnexta].
  - destruct Hb as [vb Hvb|b0 Hsomeb Hnextb].
    + apply Hready; assumption.
    + destruct Hsomeb as [b' Hsb]. eapply BS_Step.
      * exists (tm_div va b'). apply ST_Div2; assumption.
      * intros u Hu. inversion Hu; subst; try solve [exfalso; eapply value_no_step; eauto].
        all: try solve [apply BS_Value; constructor].
        eapply behavior_safe_div.
        -- constructor. exact Hva.
        -- eapply Hnextb. eassumption.
        -- eapply step_preserves_lc; eassumption.
        -- exact Hready.
  - destruct Hsomea as [a' Hsa]. eapply BS_Step.
    + exists (tm_div a' b). apply ST_Div1; assumption.
    + intros u Hu. inversion Hu; subst;
        try solve [inversion Hsa];
        try solve [exfalso; eapply value_no_step; eauto].
      all: try solve [apply BS_Value; constructor].
      eapply behavior_safe_div.
      * eapply Hnexta. eassumption.
      * exact Hb.
      * exact Hlb.
      * exact Hready.
Qed.

CoFixpoint behavior_safe_arith (op : integer_operator) (a b : tm)
    (Ha : behavior_safe a) (Hb : behavior_safe b)
    (Hlb : locally_closed_tm b)
    (Hready : forall va vb, value va -> value vb ->
       behavior_safe (tm_arith op va vb)) : behavior_safe (tm_arith op a b).
Proof.
  destruct Ha as [va Hva|a0 Hsomea Hnexta].
  - destruct Hb as [vb Hvb|b0 Hsomeb Hnextb].
    + apply Hready; assumption.
    + destruct Hsomeb as [b' Hsb]. eapply BS_Step.
      * exists (tm_arith op va b'). apply ST_Arith2; assumption.
      * intros u Hu. inversion Hu; subst; try solve [exfalso; eapply value_no_step; eauto].
        all: try solve [apply BS_Value; constructor].
        eapply behavior_safe_arith.
        -- constructor. exact Hva.
        -- eapply Hnextb. eassumption.
        -- eapply step_preserves_lc; eassumption.
        -- exact Hready.
  - destruct Hsomea as [a' Hsa]. eapply BS_Step.
    + exists (tm_arith op a' b). apply ST_Arith1; assumption.
    + intros u Hu. inversion Hu; subst;
        try solve [inversion Hsa];
        try solve [exfalso; eapply value_no_step; eauto].
      all: try solve [apply BS_Value; constructor].
      eapply behavior_safe_arith.
      * eapply Hnexta. eassumption.
      * exact Hb.
      * exact Hlb.
      * exact Hready.
Qed.

Lemma sem_value_value : forall R v, sem_value R v -> value v.
Proof.
  intros R v H. destruct R; simpl in H.
  - destruct H as [Hv _]. exact Hv.
  - destruct H as [Hv _]. exact Hv.
  - destruct H as [w [_ [_ [Hv _]]]]. exact Hv.
  - destruct H as [Hv _]. exact Hv.
Qed.

Lemma sem_value_int_literal : forall p v,
  sem_value (R_Refine Ty_Int p) v -> exists z, v = tm_int z.
Proof.
  intros p v H. simpl in H. destruct H as [_ [Hcan _]]. exact Hcan.
Qed.

Lemma sem_value_nonzero_literal : forall v,
  sem_value (R_Refine Ty_Int (Pred_Ne (tm_bvar 0) (tm_int 0%Z))) v ->
  exists z, v = tm_int z /\ z <> 0%Z.
Proof.
  intros v H. simpl in H. apply value_relation_nonzero_int. exact H.
Qed.

Lemma behavior_safe_div_ints : forall n m,
  (m <> 0%Z) -> behavior_safe (tm_div (tm_int n) (tm_int m)).
Proof.
  intros n m Hnz. eapply BS_Step with (t := tm_div (tm_int n) (tm_int m)).
  - exists (tm_int (Z.div n m)). apply ST_DivInt. exact Hnz.
  - intros u Hu. inversion Hu; subst;
      try solve [inversion H1];
      try solve [exfalso; eapply value_no_step; [constructor|eassumption]].
    apply BS_Value. constructor.
Qed.

Lemma behavior_safe_arith_ints : forall op n m,
  behavior_safe (tm_arith op (tm_int n) (tm_int m)).
Proof.
  intros. eapply BS_Step with (t := tm_arith op (tm_int n) (tm_int m)).
  - exists (tm_int (eval_integer_operator op n m)). apply ST_ArithInt.
  - intros u Hu. inversion Hu; subst;
      try solve [inversion H1];
      try solve [exfalso; eapply value_no_step; [constructor|eassumption]].
    apply BS_Value. constructor.
Qed.

Lemma lookup_rcontext_fv_incl : forall RGamma x R a,
  lookup_rcontext x RGamma = Some R -> In a (fv_rty R) ->
  In a (fv_rcontext RGamma).
Proof.
  induction RGamma as [|[y Q] G IH]; intros x R a Hlook Hin; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + inversion Hlook; subst. apply in_or_app. left. exact Hin.
    + apply in_or_app. right. eapply IH; eauto.
Qed.

Lemma sem_value_update : forall theta gamma RGamma x R w,
  sem_context_realized theta gamma RGamma ->
  lookup_rcontext x RGamma = None ->
  (forall y Q, lookup_rcontext y RGamma = Some Q -> ~ In x (fv_rty Q)) ->
  ~ In x (fv_rty R) ->
  value w -> sem_value (instantiate_rty theta gamma R) w ->
  sem_context_realized theta (term_subst_update gamma x w)
    (update_rcontext RGamma x R).
Proof.
  intros theta gamma RGamma x R w [Hclosed [Hform Henv]] Hlookup Hfresh HfreshR Hwv Hrel.
  split.
  - eapply term_subst_update_closed; [exact Hclosed|apply value_regular; exact Hwv].
  - split.
    + intros y T p Hlook. simpl in Hlook. destruct (Nat.eqb y x) eqn:E.
      * apply Nat.eqb_eq in E. subst y. inversion Hlook; subst.
        simpl in Hrel. destruct Hrel as [_ [_ Hqual]].
        rewrite instantiate_formula_eq_pred.
        unfold open_qualifier_tm, open_qualifier_tm_rec in *.
        rewrite (@instantiate_open_pred_tm_rec p 0 theta gamma x w).
        -- exact Hqual.
        -- simpl in HfreshR. exact HfreshR.
        -- exact Hclosed.
      * apply Nat.eqb_neq in E.
        assert (Hold : lookup_rcontext y RGamma = Some (R_Refine T p)) by exact Hlook.
        specialize (Hform y T p Hold).
        rewrite instantiate_formula_eq_pred in *.
        rewrite (instantiate_pred_update_irrelevant
          (open_qualifier_tm p (tm_fvar y)) theta gamma x w).
        -- exact Hform.
        -- apply open_pred_fresh_notin.
           ++ specialize (Hfresh y (R_Refine T p) Hold). simpl in Hfresh. exact Hfresh.
           ++ intro Heq. apply E. symmetry. exact Heq.
    + intros y Q Hlook. simpl in Hlook. destruct (Nat.eqb y x) eqn:E.
      * apply Nat.eqb_eq in E. subst y. inversion Hlook; subst.
        rewrite (instantiate_rty_update_irrelevant Q theta gamma x w) by exact HfreshR.
        unfold term_subst_update. rewrite Nat.eqb_refl. exact Hrel.
      * apply Nat.eqb_neq in E.
        assert (Hold : lookup_rcontext y RGamma = Some Q) by exact Hlook.
        specialize (Henv y Q Hold).
        rewrite (instantiate_rty_update_irrelevant Q theta gamma x w).
        -- unfold term_subst_update. rewrite (proj2 (Nat.eqb_neq x y)
             (fun Heq => E (eq_sym Heq))). exact Henv.
        -- eapply Hfresh; eauto.
Qed.

Theorem never_stuck : forall (t t' : tm) (R : rty),
  has_rtype [] empty_rcontext t R ->
  multi t t' ->
  value t' \/ exists t'' : tm, t' --> t''.
Proof.
  (* Complete this proof. *)
Qed.

End SystemFRefinementRecursionTask.
