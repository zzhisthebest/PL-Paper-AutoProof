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

End SystemFRefinementIf.

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
Module SystemFRefinementIfInfrastructure.
Import ListNotations.
Import SystemFRefinementIf.

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
  - constructor.
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
  - constructor.
  - constructor.
  - try (inversion Hlc; subst). apply lc_tm_if; eauto.
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
  - constructor.
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
  - constructor.
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
  - constructor.
  - constructor.
  - try (inversion Hlc; subst). apply lc_tm_if; eauto.
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
  - constructor.
  - constructor.
  - try (inversion Hlc; subst). apply lc_tm_if; eauto.
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
  | Ty_Bool => Ty_Bool
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
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (instantiate theta gamma t1) (instantiate theta gamma t2) (instantiate theta gamma t3)
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

End SystemFRefinementIfInfrastructure.

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
Module SystemFRefinementIfCoreTyping.
Import ListNotations.
Import SystemFRefinementIf.
Import SystemFRefinementIfInfrastructure.

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

End SystemFRefinementIfCoreTyping.

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

Fixpoint close_ty_rec (k : nat) (X : atom) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar Y => if Nat.eqb X Y then Ty_BVar k else Ty_FVar Y
  | Ty_Arrow T1 T2 =>
      Ty_Arrow (close_ty_rec k X T1) (close_ty_rec k X T2)
  | Ty_All T1 => Ty_All (close_ty_rec (S k) X T1)
  | Ty_Int => Ty_Int
  | Ty_Bool => Ty_Bool
  end.

End SystemFRefinementIfTyping.

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Module SystemFRefinementIfEvaluation.
Import ListNotations SystemFRefinementIf SystemFRefinementIfInfrastructure
  SystemFRefinementIfCoreTyping.

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

End SystemFRefinementIfEvaluation.

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
From Equations Require Import Equations.
Module SystemFRefinementIfSubstitution.
Import ListNotations.
Import SystemFRefinementIf.
Import SystemFRefinementIfInfrastructure.
Import SystemFRefinementIfCoreTyping.
Import SystemFRefinementIfTyping.
Import SystemFRefinementIfEvaluation.

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
End SystemFRefinementIfSubstitution.

From Equations Require Import Equations.
Module SystemFRefinementIfTask.
Import ListNotations SystemFRefinementIf SystemFRefinementIfInfrastructure SystemFRefinementIfCoreTyping SystemFRefinementIfLogic SystemFRefinementIfTyping SystemFRefinementIfEvaluation SystemFRefinementIfSubstitution .

Lemma canonical_int : forall Delta Gamma v,
  has_type Delta Gamma v Ty_Int -> value v -> exists n, v = tm_int n.
Proof.
  intros Delta Gamma v Hty Hv. inversion Hv; subst; inversion Hty; subst; eauto.
Qed.

Lemma canonical_bool : forall Delta Gamma v,
  has_type Delta Gamma v Ty_Bool -> value v -> v = tm_true \/ v = tm_false.
Proof.
  intros Delta Gamma v Hty Hv. inversion Hv; subst; inversion Hty; subst; eauto.
Qed.

Lemma canonical_arrow : forall Delta Gamma v T1 T2,
  has_type Delta Gamma v (Ty_Arrow T1 T2) -> value v ->
  exists body, v = tm_abs T1 body.
Proof.
  intros Delta Gamma v T1 T2 Hty Hv. inversion Hv; subst; inversion Hty; subst; eauto.
Qed.

Lemma canonical_all : forall Delta Gamma v T,
  has_type Delta Gamma v (Ty_All T) -> value v -> exists body, v = tm_tabs body.
Proof.
  intros Delta Gamma v T Hty Hv. inversion Hv; subst; inversion Hty; subst; eauto.
Qed.

Lemma predicate_multi_value_eq : forall v u,
  value v -> predicate_multistep v u -> u = v.
Proof.
  intros v u Hv Hm. inversion Hm; subst; auto.
  exfalso. eapply value_no_step; eauto.
Qed.

Lemma nonzero_integer_holds : forall n : Z,
  qualifier_holds (Pred_Ne (tm_int n) (tm_int 0%Z)) -> n <> 0%Z.
Proof.
  intros n Hnz Heq. subst n.
  unfold qualifier_holds, predicate_holds in Hnz.
  simpl in Hnz.
  assert (He : exists v, predicate_multistep (tm_int 0%Z) v /\
                    predicate_multistep (tm_int 0%Z) v /\ value v).
  { exists (tm_int 0%Z). repeat split; constructor. }
  contradiction.
Qed.

Lemma multi_to_predicate_multi : forall t u,
  multi t u -> predicate_multistep t u.
Proof.
  intros t u Hm. induction Hm.
  - constructor.
  - eapply PMS_Step; eassumption.
Qed.

Lemma nonzero_qualifier_excludes_zero : forall t,
  qualifier_holds (Pred_Ne t (tm_int 0%Z)) ->
  ~ multi t (tm_int 0%Z).
Proof.
  intros t Hnz Hzero. unfold qualifier_holds, predicate_holds in Hnz.
  simpl in Hnz. apply Hnz. exists (tm_int 0%Z). repeat split.
  - apply multi_to_predicate_multi. exact Hzero.
  - constructor.
  - constructor.
Qed.

Lemma erase_open_rty_tm_rec : forall R k u,
  erase (open_rty_tm_rec k u R) = erase R.
Proof.
  intros R. induction R; intros k u.
  - reflexivity.
  - change (Ty_Arrow (erase (open_rty_tm_rec k u R1))
      (erase (open_rty_tm_rec (S k) u R2)) = Ty_Arrow (erase R1) (erase R2)).
    f_equal; [apply IHR1 | apply IHR2].
  - change (erase (open_rty_tm_rec (S k) u R2) = erase R2).
    apply IHR2.
  - change (Ty_All (erase (open_rty_tm_rec k u R)) = Ty_All (erase R)).
    f_equal; apply IHR.
Qed.

Lemma erase_open_rty_tm : forall R u,
  erase (open_rty_tm R u) = erase R.
Proof. intros; unfold open_rty_tm; apply erase_open_rty_tm_rec. Qed.

Lemma erase_open_rty_ty_rec : forall R k U,
  erase (open_rty_ty_rec k U R) = open_ty_rec k U (erase R).
Proof.
  intros R. induction R; intros k U; simpl.
  - reflexivity.
  - f_equal; [apply IHR1 | apply IHR2].
  - apply IHR2.
  - f_equal; apply IHR.
Qed.

Lemma close_ty_open_ty_rec : forall T k X,
  ~ In X (fv_ty T) ->
  close_ty_rec k X (open_ty_rec k (Ty_FVar X) T) = T.
Proof.
  induction T; intros k X Hfresh; simpl in *.
  - destruct (Nat.eqb k n) eqn:E; simpl.
    + apply Nat.eqb_eq in E. subst. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply Hfresh. simpl. auto.
    + reflexivity.
  - rewrite IHT1, IHT2; try (intro Hin; apply Hfresh; apply in_or_app; auto).
    reflexivity.
  - rewrite IHT; try assumption. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma subtype_erases : forall Delta RGamma R S,
  subtype Delta RGamma R S -> erase R = erase S.
Proof.
  assert (Q :
    (forall Delta RGamma t R (Hty : has_rtype Delta RGamma t R), True) /\
    (forall Delta RGamma R S (Hsub : subtype Delta RGamma R S), erase R = erase S)).
  { apply (refinement_typing_mutind
      (fun _ _ _ _ _ => True)
      (fun _ _ R S _ => erase R = erase S)); intros; simpl in *;
      try exact I; try reflexivity.
    - f_equal.
      + symmetry; assumption.
      + rewrite <- (erase_open_rty_tm R2 (tm_fvar (fresh L))).
        rewrite <- (erase_open_rty_tm S2 (tm_fvar (fresh L))).
        match goal with
        | IH : forall x : atom, ~ In x L ->
            erase (open_rty_tm R2 (tm_fvar x)) =
            erase (open_rty_tm S2 (tm_fvar x)) |- _ =>
              exact (IH (fresh L) (fresh_notin L))
        end.
    - transitivity (erase (open_rty_tm R2 v));
        [assumption | apply erase_open_rty_tm].
    - rewrite <- (erase_open_rty_tm R2 (tm_fvar (fresh L))).
      eauto using fresh_notin.
    - set (X := fresh (fv_ty (erase R) ++ fv_ty (erase S) ++ L)).
      assert (HX : ~ In X (fv_ty (erase R) ++ fv_ty (erase S) ++ L)).
      { unfold X. apply fresh_notin. }
      assert (HXR : ~ In X (fv_ty (erase R))).
      { intro Hin. apply HX. apply in_or_app. left. exact Hin. }
      assert (HXS : ~ In X (fv_ty (erase S))).
      { intro Hin. apply HX. apply in_or_app. right. apply in_or_app. left. exact Hin. }
      assert (HXL : ~ In X L).
      { intro Hin. apply HX. apply in_or_app. right. apply in_or_app. right. exact Hin. }
      specialize (H X HXL).
      unfold open_rty_ty in H. rewrite !erase_open_rty_ty_rec in H.
      pose proof (f_equal (close_ty_rec 0 X) H) as Hclosed.
      rewrite close_ty_open_ty_rec in Hclosed by exact HXR.
      rewrite close_ty_open_ty_rec in Hclosed by exact HXS.
      f_equal. exact Hclosed.
    - etransitivity; eauto.
  }
  destruct Q as [_ Hsub]. intros. eapply Hsub. exact H.
Qed.

Lemma wf_rty_erases : forall Delta RGamma R,
  wf_rty Delta RGamma R -> wf_ty Delta (erase R).
Proof.
  intros Delta RGamma R Hwf. induction Hwf; simpl.
  - assumption.
  - apply WF_Arrow.
    + exact IHHwf.
    + pose proof (H0 (fresh L) (fresh_notin L)) as Hty.
      rewrite erase_open_rty_tm in Hty. exact Hty.
  - pose proof (H0 (fresh L) (fresh_notin L)) as Hty.
    rewrite erase_open_rty_tm in Hty. exact Hty.
  - apply WF_All with (L := L). intros X HX.
    pose proof (H0 X HX) as Hty.
    unfold open_rty_ty in Hty.
    rewrite erase_open_rty_ty_rec in Hty. exact Hty.
Qed.

Lemma lookup_erase_context : forall x RGamma R,
  lookup_rcontext x RGamma = Some R ->
  lookup_context x (erase_context RGamma) = Some (erase R).
Proof.
  intros x RGamma. induction RGamma as [|[y S] RGamma IH]; intros R H; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + inversion H; subst. reflexivity.
    + apply IH in H. exact H.
Qed.

Lemma has_rtype_erases : forall Delta RGamma t R,
  has_rtype Delta RGamma t R ->
  has_type Delta (erase_context RGamma) t (erase R).
Proof.
  assert (Q :
    (forall Delta RGamma t R (Hty : has_rtype Delta RGamma t R),
       has_type Delta (erase_context RGamma) t (erase R)) /\
    (forall Delta RGamma R S (Hsub : subtype Delta RGamma R S),
       erase R = erase S)).
  { apply (refinement_typing_mutind
      (fun Delta RGamma t R _ =>
        has_type Delta (erase_context RGamma) t (erase R))
      (fun _ _ R S _ => erase R = erase S)); intros; simpl in *.
    - eapply T_Var.
      + eapply lookup_erase_context. eassumption.
      + eapply wf_rty_erases. eassumption.
    - eapply T_Abs with (L := L).
      + eapply wf_rty_erases. eassumption.
      + intros x Hx. specialize (H x Hx).
        rewrite erase_open_rty_tm in H. exact H.
    - eapply T_App; eauto.
    - eapply T_TAbs with (L := L). intros X HX.
      specialize (H X HX). unfold open_rty_ty in H.
      rewrite erase_open_rty_ty_rec in H. exact H.
    - unfold open_rty_ty. rewrite erase_open_rty_ty_rec.
      eapply T_TApp; eauto using wf_rty_erases.
    - constructor.
    - eapply T_Div; eauto.
    - eapply T_Arith; eauto.
    - constructor.
    - constructor.
    - eapply T_If; eauto.
    - assumption.
    - rewrite <- H0. assumption.
    - reflexivity.
    - reflexivity.
    - f_equal; [symmetry; assumption |].
      rewrite <- (erase_open_rty_tm R2 (tm_fvar (fresh L))).
      rewrite <- (erase_open_rty_tm S2 (tm_fvar (fresh L))).
      match goal with
      | IH : forall x : atom, ~ In x L ->
          erase (open_rty_tm R2 (tm_fvar x)) =
          erase (open_rty_tm S2 (tm_fvar x)) |- _ =>
            exact (IH (fresh L) (fresh_notin L))
      end.
    - transitivity (erase (open_rty_tm R2 v)); [assumption | apply erase_open_rty_tm].
    - rewrite <- (erase_open_rty_tm R2 (tm_fvar (fresh L))).
      eauto using fresh_notin.
    - set (X := fresh (fv_ty (erase R) ++ fv_ty (erase S) ++ L)).
      assert (HX : ~ In X (fv_ty (erase R) ++ fv_ty (erase S) ++ L)).
      { unfold X. apply fresh_notin. }
      assert (HXR : ~ In X (fv_ty (erase R))).
      { intro Hin. apply HX. apply in_or_app. left. exact Hin. }
      assert (HXS : ~ In X (fv_ty (erase S))).
      { intro Hin. apply HX. apply in_or_app. right. apply in_or_app. left. exact Hin. }
      assert (HXL : ~ In X L).
      { intro Hin. apply HX. apply in_or_app. right. apply in_or_app. right. exact Hin. }
      specialize (H X HXL). unfold open_rty_ty in H.
      rewrite !erase_open_rty_ty_rec in H.
      pose proof (f_equal (close_ty_rec 0 X) H) as Hclosed.
      rewrite close_ty_open_ty_rec in Hclosed by exact HXR.
      rewrite close_ty_open_ty_rec in Hclosed by exact HXS.
      f_equal. exact Hclosed.
    - etransitivity; eauto.
  }
  destruct Q as [Hty _]. intros. eapply Hty. exact H.
Qed.

Lemma wf_ty_lc : forall Delta T,
  wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T Hwf. induction Hwf.
  - constructor.
  - constructor; assumption.
  - apply lc_ty_all.
    pose proof (H0 (fresh L) (fresh_notin L)) as Hlc.
    eapply lc_ty_at_open_inv; exact Hlc.
  - constructor.
  - constructor.
Qed.

Lemma has_type_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T Hty. induction Hty.
  - constructor.
  - apply lc_tm_abs.
    + eapply wf_ty_lc. eassumption.
    + apply lc_tm_at_open_tm_inv with (x := fresh L).
      apply H1. apply fresh_notin.
  - econstructor; eauto.
  - apply lc_tm_tabs.
    apply lc_tm_at_open_ty_inv with (X := fresh L).
    apply H0. apply fresh_notin.
  - apply lc_tm_tapp.
    + exact IHHty.
    + eapply wf_ty_lc. eassumption.
  - constructor.
  - econstructor; eauto.
  - econstructor; eauto.
  - constructor.
  - constructor.
  - econstructor; eauto.
Qed.

Lemma has_rtype_lc : forall Delta RGamma t R,
  has_rtype Delta RGamma t R -> locally_closed_tm t.
Proof.
  intros. eapply has_type_lc. eapply has_rtype_erases. eassumption.
Qed.

Lemma open_tm_rec_lc_identity : forall t K k u,
  lc_tm_at K k t -> open_tm_rec k u t = t.
Proof.
  induction t; intros K k u Hlc; simpl; inversion Hlc; subst.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + reflexivity.
  - reflexivity.
  - f_equal. eapply IHt. eassumption.
  - f_equal; [eapply IHt1 | eapply IHt2]; eassumption.
  - f_equal. eapply IHt. eassumption.
  - f_equal; eauto.
  - reflexivity.
  - f_equal; [eapply IHt1 | eapply IHt2]; eassumption.
  - f_equal; [eapply IHt1 | eapply IHt2]; eassumption.
  - reflexivity.
  - reflexivity.
  - f_equal; [eapply IHt1 | eapply IHt2 | eapply IHt3]; eassumption.
Qed.

Lemma open_ty_rec_lc_identity : forall T k U,
  lc_ty_at k T -> open_ty_rec k U T = T.
Proof.
  induction T; intros k U Hlc; simpl; inversion Hlc; subst.
  - destruct (Nat.eqb k n) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
  - reflexivity.
  - f_equal; [eapply IHT1 | eapply IHT2]; eassumption.
  - f_equal. eapply IHT. eassumption.
  - reflexivity.
  - reflexivity.
Qed.

Lemma open_tm_ty_rec_lc_identity : forall t K k U,
  lc_tm_at K k t -> open_tm_ty_rec K U t = t.
Proof.
  induction t; intros K k U Hlc; simpl; inversion Hlc; subst.
  - reflexivity.
  - reflexivity.
  - rewrite open_ty_rec_lc_identity by assumption.
    f_equal. eapply IHt. eassumption.
  - f_equal; [eapply IHt1 | eapply IHt2]; eassumption.
  - f_equal. eapply IHt. eassumption.
  - f_equal.
    + eapply IHt. eassumption.
    + rewrite open_ty_rec_lc_identity by assumption. reflexivity.
  - reflexivity.
  - f_equal; [eapply IHt1 | eapply IHt2]; eassumption.
  - f_equal; [eapply IHt1 | eapply IHt2]; eassumption.
  - reflexivity.
  - reflexivity.
  - f_equal; [eapply IHt1 | eapply IHt2 | eapply IHt3]; eassumption.
Qed.

Lemma instantiate_open_tm_rec : forall t k u theta gamma,
  term_substitution_closed gamma ->
  instantiate theta gamma (open_tm_rec k u t) =
  open_tm_rec k (instantiate theta gamma u) (instantiate theta gamma t).
Proof.
  induction t; intros k u theta gamma Hgamma; simpl; try reflexivity.
  - destruct (Nat.eqb k n); reflexivity.
  - rewrite (open_tm_rec_lc_identity (gamma a) 0 k
      (instantiate theta gamma u)).
    + reflexivity.
    + eapply lc_tm_at_monotone; [apply Hgamma | lia | lia].
  - f_equal. apply IHt. exact Hgamma.
  - f_equal; [apply IHt1 | apply IHt2]; exact Hgamma.
  - f_equal. apply IHt. exact Hgamma.
  - f_equal. apply IHt. exact Hgamma.
  - f_equal; [apply IHt1 | apply IHt2]; exact Hgamma.
  - f_equal; [apply IHt1 | apply IHt2]; exact Hgamma.
  - f_equal; [apply IHt1 | apply IHt2 | apply IHt3]; exact Hgamma.
Qed.

Lemma instantiate_open_tm : forall t u theta gamma,
  term_substitution_closed gamma ->
  instantiate theta gamma (open_tm t u) =
  open_tm (instantiate theta gamma t) (instantiate theta gamma u).
Proof. intros; unfold open_tm; apply instantiate_open_tm_rec; assumption. Qed.

Lemma instantiate_ty_identity : forall T,
  instantiate_ty identity_type_substitution T = T.
Proof. induction T; simpl; try reflexivity; f_equal; eauto. Qed.

Lemma instantiate_open_tm_ty_rec_identity : forall t K U gamma,
  term_substitution_closed gamma ->
  instantiate identity_type_substitution gamma (open_tm_ty_rec K U t) =
  open_tm_ty_rec K U (instantiate identity_type_substitution gamma t).
Proof.
  induction t; intros K U gamma Hgamma; simpl; try reflexivity.
  - symmetry. eapply open_tm_ty_rec_lc_identity with (K := K) (k := 0) (U := U).
    eapply lc_tm_at_monotone with (K := 0) (k := 0) (K' := K) (k' := 0).
    + apply Hgamma.
    + lia.
    + lia.
  - f_equal.
    + rewrite !instantiate_ty_identity. reflexivity.
    + apply IHt. exact Hgamma.
  - f_equal; [apply IHt1 | apply IHt2]; exact Hgamma.
  - f_equal. apply IHt. exact Hgamma.
  - f_equal.
    + apply IHt. exact Hgamma.
    + rewrite !instantiate_ty_identity. reflexivity.
  - f_equal; [apply IHt1 | apply IHt2]; exact Hgamma.
  - f_equal; [apply IHt1 | apply IHt2]; exact Hgamma.
  - f_equal; [apply IHt1 | apply IHt2 | apply IHt3]; exact Hgamma.
Qed.

Lemma instantiate_ty_no_fv : forall T theta,
  fv_ty T = [] -> instantiate_ty theta T = T.
Proof.
  induction T; intros theta Hfv; simpl in *; try reflexivity.
  - discriminate.
  - f_equal.
    + apply IHT1. apply app_eq_nil in Hfv as [H1 H2]. exact H1.
    + apply IHT2. apply app_eq_nil in Hfv as [H1 H2]. exact H2.
  - f_equal. apply IHT. exact Hfv.
Qed.

Lemma instantiate_ty_update_fresh : forall T theta X U,
  ~ In X (fv_ty T) ->
  instantiate_ty (type_subst_update theta X U) T = instantiate_ty theta T.
Proof.
  induction T; intros theta X U Hfresh; simpl in *; try reflexivity.
  - destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply Hfresh. simpl. auto.
    + unfold type_subst_update. rewrite E. reflexivity.
  - f_equal.
    + apply IHT1. intros Hin; apply Hfresh; rewrite in_app_iff; auto.
    + apply IHT2. intros Hin; apply Hfresh; rewrite in_app_iff; auto.
  - f_equal. apply IHT. exact Hfresh.
Qed.

Lemma instantiate_tm_ty_update_fresh : forall t theta gamma X U,
  ~ In X (ftv_tm t) ->
  instantiate (type_subst_update theta X U) gamma t = instantiate theta gamma t.
Proof.
  induction t; intros theta gamma X U Hfresh; simpl in *; try reflexivity.
  - f_equal.
    + apply instantiate_ty_update_fresh. intros Hin; apply Hfresh; simpl; rewrite in_app_iff; left; exact Hin.
    + apply IHt. intros Hin; apply Hfresh; simpl; rewrite in_app_iff; right; exact Hin.
  - f_equal; [apply IHt1 | apply IHt2]; intros Hin; apply Hfresh; simpl; rewrite in_app_iff; auto.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal.
    + apply IHt. intros Hin; apply Hfresh; simpl; rewrite in_app_iff; left; exact Hin.
    + apply instantiate_ty_update_fresh. intros Hin; apply Hfresh; simpl; rewrite in_app_iff; right; exact Hin.
  - f_equal; [apply IHt1 | apply IHt2]; intros Hin; apply Hfresh; simpl; rewrite in_app_iff; auto.
  - f_equal; [apply IHt1 | apply IHt2]; intros Hin; apply Hfresh; simpl; rewrite in_app_iff; auto.
  - f_equal.
    + apply IHt1. intros Hin. apply Hfresh.
      apply (proj2 (in_app_iff (ftv_tm t1) (ftv_tm t2 ++ ftv_tm t3) X)). left. exact Hin.
    + apply IHt2. intros Hin. apply Hfresh.
      apply (proj2 (in_app_iff (ftv_tm t1) (ftv_tm t2 ++ ftv_tm t3) X)). right.
      apply (proj2 (in_app_iff (ftv_tm t2) (ftv_tm t3) X)). left. exact Hin.
    + apply IHt3. intros Hin. apply Hfresh.
      apply (proj2 (in_app_iff (ftv_tm t1) (ftv_tm t2 ++ ftv_tm t3) X)). right.
      apply (proj2 (in_app_iff (ftv_tm t2) (ftv_tm t3) X)). right. exact Hin.
Qed.

Lemma instantiate_pred_ty_update_fresh : forall p theta gamma X U,
  ~ In X (ftv_pred p) ->
  instantiate_qualifier (type_subst_update theta X U) gamma p =
  instantiate_qualifier theta gamma p.
Proof.
  induction p as [| |u v|u v|u v|p1 IHp1 p2 IHp2|p1 IHp1 p2 IHp2|p IHp]; intros theta gamma X U Hfresh; simpl in *; try reflexivity.
  - f_equal.
    + apply instantiate_tm_ty_update_fresh. intros Hin; apply Hfresh.
      simpl. apply (proj2 (in_app_iff (ftv_tm u) (ftv_tm v) X)). left. exact Hin.
    + apply instantiate_tm_ty_update_fresh. intros Hin; apply Hfresh.
      simpl. apply (proj2 (in_app_iff (ftv_tm u) (ftv_tm v) X)). right. exact Hin.
  - f_equal.
    + apply instantiate_tm_ty_update_fresh. intros Hin; apply Hfresh.
      simpl. apply (proj2 (in_app_iff (ftv_tm u) (ftv_tm v) X)). left. exact Hin.
    + apply instantiate_tm_ty_update_fresh. intros Hin; apply Hfresh.
      simpl. apply (proj2 (in_app_iff (ftv_tm u) (ftv_tm v) X)). right. exact Hin.
  - f_equal.
    + apply instantiate_tm_ty_update_fresh. intros Hin; apply Hfresh.
      simpl. apply (proj2 (in_app_iff (ftv_tm u) (ftv_tm v) X)). left. exact Hin.
    + apply instantiate_tm_ty_update_fresh. intros Hin; apply Hfresh.
      simpl. apply (proj2 (in_app_iff (ftv_tm u) (ftv_tm v) X)). right. exact Hin.
  - f_equal.
    + apply IHp1. intros Hin; apply Hfresh. simpl.
      apply (proj2 (in_app_iff (ftv_pred p1) (ftv_pred p2) X)). left. exact Hin.
    + apply IHp2. intros Hin; apply Hfresh. simpl.
      apply (proj2 (in_app_iff (ftv_pred p1) (ftv_pred p2) X)). right. exact Hin.
  - f_equal.
    + apply IHp1. intros Hin; apply Hfresh. simpl.
      apply (proj2 (in_app_iff (ftv_pred p1) (ftv_pred p2) X)). left. exact Hin.
    + apply IHp2. intros Hin; apply Hfresh. simpl.
      apply (proj2 (in_app_iff (ftv_pred p1) (ftv_pred p2) X)). right. exact Hin.
  - f_equal. apply IHp. exact Hfresh.
Qed.

Lemma instantiate_rty_ty_update_fresh : forall R theta gamma X U,
  ~ In X (ftv_rty R) ->
  instantiate_rty (type_subst_update theta X U) gamma R = instantiate_rty theta gamma R.
Proof.
  induction R as [T q|R1 IHR1 R2 IHR2|R1 IHR1 R2 IHR2|R IHR]; intros theta gamma X U Hfresh; simpl in *.
  - f_equal.
    + apply instantiate_ty_update_fresh. intros Hin; apply Hfresh.
      simpl. apply (proj2 (in_app_iff (fv_ty T) (ftv_qualifier q) X)). left. exact Hin.
    + apply instantiate_pred_ty_update_fresh. intros Hin; apply Hfresh.
      simpl. apply (proj2 (in_app_iff (fv_ty T) (ftv_qualifier q) X)). right. exact Hin.
  - f_equal.
    + apply IHR1. intros Hin; apply Hfresh. simpl.
      apply (proj2 (in_app_iff (ftv_rty R1) (ftv_rty R2) X)). left. exact Hin.
    + apply IHR2. intros Hin; apply Hfresh. simpl.
      apply (proj2 (in_app_iff (ftv_rty R1) (ftv_rty R2) X)). right. exact Hin.
  - f_equal.
    + apply IHR1. intros Hin; apply Hfresh. simpl.
      apply (proj2 (in_app_iff (ftv_rty R1) (ftv_rty R2) X)). left. exact Hin.
    + apply IHR2. intros Hin; apply Hfresh. simpl.
      apply (proj2 (in_app_iff (ftv_rty R1) (ftv_rty R2) X)). right. exact Hin.
  - f_equal. apply IHR. exact Hfresh.
Qed.

Lemma fv_ty_open_contains : forall T k U X,
  In X (fv_ty T) -> In X (fv_ty (open_ty_rec k U T)).
Proof.
  induction T; intros k U X Hin; simpl in *.
  - contradiction.
  - exact Hin.
  - apply in_app_iff in Hin as [Hin|Hin].
    + apply in_app_iff. left. eapply IHT1. exact Hin.
    + apply in_app_iff. right. eapply IHT2. exact Hin.
  - eapply IHT. exact Hin.
  - contradiction.
  - contradiction.
Qed.

Lemma wf_ty_fv_in_context : forall Delta T,
  wf_ty Delta T -> forall X, In X (fv_ty T) -> In X Delta.
Proof.
  intros Delta T Hwf. induction Hwf; intros Y Hin; simpl in *.
  - destruct Hin as [Hin|[]]. symmetry in Hin. subst Y. exact H.
  - apply in_app_iff in Hin as [Hin|Hin].
    + apply IHHwf1. exact Hin.
    + apply IHHwf2. exact Hin.
  - pose (Z := fresh (L ++ [Y])).
    assert (HZL : ~ In Z L).
    { unfold Z. intro HinZ. pose proof (fresh_notin (L ++ [Y])) as Hfresh.
      apply Hfresh. apply in_app_iff. left. exact HinZ. }
    assert (HZY : Z <> Y).
    { unfold Z. intro Heq. pose proof (fresh_notin (L ++ [Y])) as Hfresh.
      apply Hfresh. apply in_app_iff. right. simpl. left. symmetry; exact Heq. }
    specialize (H Z HZL).
    assert (HYopen : In Y (fv_ty (open_ty T (Ty_FVar Z)))).
    { unfold open_ty. eapply fv_ty_open_contains. exact Hin. }
    pose proof (IHHwf Z HYopen) as HinDelta.
    simpl in HinDelta. destruct HinDelta as [Heq|HinDelta].
    + symmetry in Heq. contradiction.
    + exact HinDelta.
  - contradiction.
  - contradiction.
Qed.

Lemma wf_ty_empty_fv : forall T,
  wf_ty [] T -> fv_ty T = [].
Proof.
  intros T Hwf. apply not_in_nil. intros X Hin.
  eapply wf_ty_fv_in_context; eauto.
Qed.

Lemma instantiate_open_ty_fresh : forall T k X U theta,
  type_substitution_closed theta -> locally_closed_ty U -> fv_ty U = [] ->
  ~ In X (fv_ty T) ->
  instantiate_ty (type_subst_update theta X U)
      (open_ty_rec k (Ty_FVar X) T) =
    open_ty_rec k U (instantiate_ty theta T).
Proof.
  induction T; intros k X U theta Htheta HU Hfvu Hfresh; simpl in *.
  - destruct (Nat.eqb k n) eqn:E; simpl.
    + unfold type_subst_update. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply Hfresh. simpl. auto.
    + unfold type_subst_update. rewrite E. simpl.
      rewrite open_ty_rec_lc_identity; [reflexivity|].
      eapply lc_ty_at_monotone with (k := 0) (k' := k).
      * apply Htheta.
      * lia.
  - f_equal.
    + apply IHT1; try assumption. intros Hin; apply Hfresh; apply in_app_iff; auto.
    + apply IHT2; try assumption. intros Hin; apply Hfresh; apply in_app_iff; auto.
  - f_equal. apply IHT; assumption.
  - reflexivity.
  - reflexivity.
Qed.

Lemma instantiate_open_tm_ty_fresh : forall t k X U theta gamma,
  type_substitution_closed theta -> term_substitution_closed gamma ->
  locally_closed_ty U -> fv_ty U = [] -> ~ In X (ftv_tm t) ->
  instantiate (type_subst_update theta X U) gamma
      (open_tm_ty_rec k (Ty_FVar X) t) =
    open_tm_ty_rec k U (instantiate theta gamma t).
Proof.
  induction t; intros k X U theta gamma Htheta Hgamma HU Hfvu Hfresh; simpl in *;
    try reflexivity.
  - symmetry. eapply open_tm_ty_rec_lc_identity with (K := k) (k := 0) (U := U).
    eapply lc_tm_at_monotone with (K := 0) (k := 0) (K' := k) (k' := 0).
    + apply Hgamma.
    + lia.
    + lia.
  - f_equal.
    + apply instantiate_open_ty_fresh; try assumption.
      intros Hin; apply Hfresh. simpl. apply in_app_iff. left. exact Hin.
    + apply IHt; try assumption.
      intros Hin; apply Hfresh. simpl. apply in_app_iff. right. exact Hin.
  - f_equal.
    + apply IHt1; try assumption. intros Hin; apply Hfresh; simpl.
      apply in_app_iff. left. exact Hin.
    + apply IHt2; try assumption. intros Hin; apply Hfresh; simpl.
      apply in_app_iff. right. exact Hin.
  - f_equal. apply IHt; assumption.
  - f_equal.
    + apply IHt; try assumption. intros Hin; apply Hfresh; simpl. apply in_app_iff; left; exact Hin.
    + apply instantiate_open_ty_fresh; try assumption. intros Hin; apply Hfresh; simpl; apply in_app_iff; right; exact Hin.
  - f_equal; [apply IHt1 | apply IHt2]; try assumption; intros Hin; apply Hfresh; simpl; apply in_app_iff; auto.
  - f_equal; [apply IHt1 | apply IHt2]; try assumption; intros Hin; apply Hfresh; simpl; apply in_app_iff; auto.
  - f_equal.
    + apply IHt1; try assumption. intros Hin. apply Hfresh. simpl. rewrite in_app_iff. left. exact Hin.
    + apply IHt2; try assumption. intros Hin. apply Hfresh. simpl. rewrite in_app_iff. right. rewrite in_app_iff. left. exact Hin.
    + apply IHt3; try assumption. intros Hin. apply Hfresh. simpl. rewrite in_app_iff. right. rewrite in_app_iff. right. exact Hin.
Qed.

Lemma instantiate_open_qualifier_ty_fresh : forall p k X U theta gamma,
  type_substitution_closed theta -> term_substitution_closed gamma ->
  locally_closed_ty U -> fv_ty U = [] -> ~ In X (ftv_pred p) ->
  instantiate_qualifier (type_subst_update theta X U) gamma
      (open_qualifier_ty_rec k (Ty_FVar X) p) =
    open_qualifier_ty_rec k U (instantiate_qualifier theta gamma p).
Proof.
  induction p; intros k X U theta gamma Htheta Hgamma HU Hfvu Hfresh; simpl in *;
    try reflexivity.
  - f_equal; [apply instantiate_open_tm_ty_fresh|apply instantiate_open_tm_ty_fresh];
      try assumption; intros Hin; apply Hfresh; simpl; apply in_app_iff; auto.
  - f_equal; [apply instantiate_open_tm_ty_fresh|apply instantiate_open_tm_ty_fresh];
      try assumption; intros Hin; apply Hfresh; simpl; apply in_app_iff; auto.
  - f_equal; [apply instantiate_open_tm_ty_fresh|apply instantiate_open_tm_ty_fresh];
      try assumption; intros Hin; apply Hfresh; simpl; apply in_app_iff; auto.
  - f_equal.
    + apply IHp1; try assumption. intros Hin; apply Hfresh; simpl; rewrite in_app_iff; auto.
    + apply IHp2; try assumption. intros Hin; apply Hfresh; simpl; rewrite in_app_iff; auto.
  - f_equal.
    + apply IHp1; try assumption. intros Hin; apply Hfresh; simpl; rewrite in_app_iff; auto.
    + apply IHp2; try assumption. intros Hin; apply Hfresh; simpl; rewrite in_app_iff; auto.
  - f_equal. apply IHp; assumption.
Qed.

Lemma instantiate_open_rty_ty_fresh : forall R k X U theta gamma,
  type_substitution_closed theta -> term_substitution_closed gamma ->
  locally_closed_ty U -> fv_ty U = [] -> ~ In X (ftv_rty R) ->
  instantiate_rty (type_subst_update theta X U) gamma
      (open_rty_ty_rec k (Ty_FVar X) R) =
    open_rty_ty_rec k U (instantiate_rty theta gamma R).
Proof.
  induction R; intros k X U theta gamma Htheta Hgamma HU Hfvu Hfresh; simpl in *.
  - f_equal.
    + apply instantiate_open_ty_fresh; try assumption.
      intros Hin; apply Hfresh; simpl; rewrite in_app_iff; left; exact Hin.
    + apply instantiate_open_qualifier_ty_fresh; try assumption.
      intros Hin; apply Hfresh; simpl; rewrite in_app_iff; right; exact Hin.
  - f_equal.
    + apply IHR1; try assumption. intros Hin; apply Hfresh; simpl; rewrite in_app_iff; left; exact Hin.
    + apply IHR2; try assumption. intros Hin; apply Hfresh; simpl; rewrite in_app_iff; right; exact Hin.
  - f_equal.
    + apply IHR1; try assumption. intros Hin; apply Hfresh; simpl; rewrite in_app_iff; left; exact Hin.
    + apply IHR2; try assumption. intros Hin; apply Hfresh; simpl; rewrite in_app_iff; right; exact Hin.
  - f_equal. apply IHR; assumption.
Qed.

Lemma instantiate_open_tm_ty_identity : forall t U gamma,
  term_substitution_closed gamma ->
  instantiate identity_type_substitution gamma (open_tm_ty t U) =
  open_tm_ty (instantiate identity_type_substitution gamma t) U.
Proof. intros; unfold open_tm_ty; apply instantiate_open_tm_ty_rec_identity; assumption. Qed.

Lemma instantiate_open_qualifier_tm_rec : forall ps k u theta gamma,
  term_substitution_closed gamma ->
  instantiate_qualifier theta gamma (open_qualifier_tm_rec k u ps) =
  open_qualifier_tm_rec k (instantiate theta gamma u)
    (instantiate_qualifier theta gamma ps).
Proof.
  induction ps; intros k u theta gamma Hgamma; simpl; try reflexivity.
  - rewrite !instantiate_open_tm_rec by exact Hgamma. reflexivity.
  - rewrite !instantiate_open_tm_rec by exact Hgamma. reflexivity.
  - rewrite !instantiate_open_tm_rec by exact Hgamma. reflexivity.
  - f_equal; [apply IHps1 | apply IHps2]; exact Hgamma.
  - f_equal; [apply IHps1 | apply IHps2]; exact Hgamma.
  - f_equal. apply IHps. exact Hgamma.
Qed.

Lemma instantiate_open_rty_tm_rec : forall R k u theta gamma,
  term_substitution_closed gamma ->
  instantiate_rty theta gamma (open_rty_tm_rec k u R) =
  open_rty_tm_rec k (instantiate theta gamma u)
    (instantiate_rty theta gamma R).
Proof.
  intros R. induction R; intros k u theta gamma Hgamma; simpl.
  - f_equal. apply instantiate_open_qualifier_tm_rec. exact Hgamma.
  - f_equal.
    + apply IHR1. exact Hgamma.
    + apply IHR2. exact Hgamma.
  - f_equal.
    + apply IHR1. exact Hgamma.
    + apply IHR2. exact Hgamma.
  - f_equal. apply IHR. exact Hgamma.
Qed.

Lemma lc_tm_at_instantiate_identity : forall t K k gamma,
  lc_tm_at K k t -> term_substitution_closed gamma ->
  lc_tm_at K k (instantiate identity_type_substitution gamma t).
Proof.
  intros t K k gamma Hlc. revert gamma.
  induction Hlc; intros gamma Hgamma; simpl.
  - constructor. assumption.
  - apply lc_tm_at_monotone with (K := 0) (k := 0).
    + apply Hgamma.
    + lia.
    + lia.
  - rewrite instantiate_ty_identity. apply lc_tm_abs.
    + assumption.
    + apply IHHlc. exact Hgamma.
  - apply lc_tm_app; [apply IHHlc1 | apply IHHlc2]; exact Hgamma.
  - apply lc_tm_tabs. apply IHHlc. exact Hgamma.
  - rewrite instantiate_ty_identity. apply lc_tm_tapp.
    + apply IHHlc. exact Hgamma.
    + assumption.
  - constructor.
  - apply lc_tm_div; [apply IHHlc1 | apply IHHlc2]; exact Hgamma.
  - apply lc_tm_arith; [apply IHHlc1 | apply IHHlc2]; exact Hgamma.
  - constructor.
  - constructor.
  - apply lc_tm_if; [apply IHHlc1 | apply IHHlc2 | apply IHHlc3]; exact Hgamma.
Qed.

Lemma lc_ty_at_instantiate : forall theta T k,
  type_substitution_closed theta -> lc_ty_at k T ->
  lc_ty_at k (instantiate_ty theta T).
Proof.
  intros theta T k Htheta Hlc. induction Hlc; simpl.
  - constructor. assumption.
  - eapply lc_ty_at_monotone; [apply Htheta|lia].
  - apply lc_ty_arrow; assumption.
  - apply lc_ty_all. apply IHHlc.
  - constructor.
  - constructor.
Qed.

Lemma lc_tm_at_instantiate : forall theta gamma t K k,
  type_substitution_closed theta -> term_substitution_closed gamma ->
  lc_tm_at K k t -> lc_tm_at K k (instantiate theta gamma t).
Proof.
  intros theta gamma t K k Htheta Hgamma Hlc.
  induction Hlc; simpl.
  - constructor. assumption.
  - eapply lc_tm_at_monotone; [apply Hgamma|lia|lia].
  - apply lc_tm_abs.
    + eapply lc_ty_at_instantiate; eauto.
    + apply IHHlc.
  - apply lc_tm_app; assumption.
  - apply lc_tm_tabs. apply IHHlc.
  - apply lc_tm_tapp.
    + apply IHHlc.
    + eapply lc_ty_at_instantiate; eauto.
  - constructor.
  - apply lc_tm_div; assumption.
  - apply lc_tm_arith; assumption.
  - constructor.
  - constructor.
  - apply lc_tm_if; assumption.
Qed.

Lemma instantiate_locally_closed_tm : forall theta gamma t,
  type_substitution_closed theta -> term_substitution_closed gamma ->
  locally_closed_tm t -> locally_closed_tm (instantiate theta gamma t).
Proof. intros. eapply lc_tm_at_instantiate; eauto. Qed.

Lemma instantiate_value : forall theta gamma v,
  type_substitution_closed theta -> term_substitution_closed gamma ->
  value v -> value (instantiate theta gamma v).
Proof.
  intros theta gamma v Htheta Hgamma Hv. destruct Hv.
  - apply v_abs. change (locally_closed_tm (instantiate theta gamma (tm_abs T t))).
    apply instantiate_locally_closed_tm; assumption.
  - apply v_tabs. change (locally_closed_tm (instantiate theta gamma (tm_tabs t))).
    apply instantiate_locally_closed_tm; assumption.
  - constructor.
  - constructor.
  - constructor.
Qed.

Lemma instantiate_tm_no_free : forall t theta gamma,
  fv_tm t = [] -> ftv_tm t = [] -> instantiate theta gamma t = t.
Proof.
  induction t; intros theta gamma Hfv Hftv; simpl in *; try reflexivity.
  - discriminate.
  - f_equal.
    + apply instantiate_ty_no_fv. apply app_eq_nil in Hftv as [H1 H2]. exact H1.
    + apply IHt; [exact Hfv|apply app_eq_nil in Hftv as [H1 H2]; exact H2].
  - f_equal.
    + apply IHt1; [apply app_eq_nil in Hfv as [H1 H2]; exact H1|apply app_eq_nil in Hftv as [H1 H2]; exact H1].
    + apply IHt2; [apply app_eq_nil in Hfv as [H1 H2]; exact H2|apply app_eq_nil in Hftv as [H1 H2]; exact H2].
  - f_equal. apply IHt; assumption.
  - f_equal.
    + apply IHt; [exact Hfv|apply app_eq_nil in Hftv as [H1 H2]; exact H1].
    + apply instantiate_ty_no_fv. apply app_eq_nil in Hftv as [H1 H2]. exact H2.
  - f_equal.
    + apply IHt1; [apply app_eq_nil in Hfv as [H1 H2]; exact H1|apply app_eq_nil in Hftv as [H1 H2]; exact H1].
    + apply IHt2; [apply app_eq_nil in Hfv as [H1 H2]; exact H2|apply app_eq_nil in Hftv as [H1 H2]; exact H2].
  - f_equal.
    + apply IHt1; [apply app_eq_nil in Hfv as [H1 H2]; exact H1|apply app_eq_nil in Hftv as [H1 H2]; exact H1].
    + apply IHt2; [apply app_eq_nil in Hfv as [H1 H2]; exact H2|apply app_eq_nil in Hftv as [H1 H2]; exact H2].
  - f_equal.
    + apply IHt1.
      * apply app_eq_nil in Hfv as [H1 H2]. exact H1.
      * apply app_eq_nil in Hftv as [H1 H2]. exact H1.
    + apply IHt2.
      * apply app_eq_nil in Hfv as [H1 H2]. apply app_eq_nil in H2 as [H21 H22]. exact H21.
      * apply app_eq_nil in Hftv as [H1 H2]. apply app_eq_nil in H2 as [H21 H22]. exact H21.
    + apply IHt3.
      * apply app_eq_nil in Hfv as [H1 H2]. apply app_eq_nil in H2 as [H21 H22]. exact H22.
      * apply app_eq_nil in Hftv as [H1 H2]. apply app_eq_nil in H2 as [H21 H22]. exact H22.
Qed.

Lemma instantiate_predicate_closed : forall p theta gamma,
  predicate_closed p -> instantiate_qualifier theta gamma p = p.
Proof.
  induction p as [| |t1 t2|t1 t2|t1 t2|p1 IH1 p2 IH2|p1 IH1 p2 IH2|p IH];
    intros theta gamma Hclosed; simpl in *; try reflexivity.
  - destruct Hclosed as [_ [Hfv1 [Hftv1 [_ [Hfv2 Hftv2]]]]].
    rewrite (instantiate_tm_no_free t1 theta gamma Hfv1 Hftv1).
    rewrite (instantiate_tm_no_free t2 theta gamma Hfv2 Hftv2). reflexivity.
  - destruct Hclosed as [_ [Hfv1 [Hftv1 [_ [Hfv2 Hftv2]]]]].
    rewrite (instantiate_tm_no_free t1 theta gamma Hfv1 Hftv1).
    rewrite (instantiate_tm_no_free t2 theta gamma Hfv2 Hftv2). reflexivity.
  - destruct Hclosed as [_ [Hfv1 [Hftv1 [_ [Hfv2 Hftv2]]]]].
    rewrite (instantiate_tm_no_free t1 theta gamma Hfv1 Hftv1).
    rewrite (instantiate_tm_no_free t2 theta gamma Hfv2 Hftv2). reflexivity.
  - destruct Hclosed as [H1 H2]. rewrite (IH1 theta gamma H1), (IH2 theta gamma H2). reflexivity.
  - destruct Hclosed as [H1 H2]. rewrite (IH1 theta gamma H1), (IH2 theta gamma H2). reflexivity.
  - rewrite (IH theta gamma Hclosed). reflexivity.
Qed.

Lemma instantiate_open_qualifier_tm : forall p u theta gamma,
  term_substitution_closed gamma ->
  instantiate_qualifier theta gamma (open_qualifier_tm p u) =
  open_qualifier_tm (instantiate_qualifier theta gamma p)
    (instantiate theta gamma u).
Proof.
  intros. unfold open_qualifier_tm. apply instantiate_open_qualifier_tm_rec. assumption.
Qed.

Lemma instantiate_value_identity : forall v gamma,
  value v -> term_substitution_closed gamma ->
  value (instantiate identity_type_substitution gamma v).
Proof.
  intros v gamma Hv Hgamma. destruct Hv; simpl.
  - rewrite instantiate_ty_identity. apply v_abs.
    rewrite <- (instantiate_ty_identity T).
    change (locally_closed_tm (instantiate identity_type_substitution gamma (tm_abs T t))).
    eapply lc_tm_at_instantiate_identity; [exact H | exact Hgamma].
  - apply v_tabs.
    change (locally_closed_tm (instantiate identity_type_substitution gamma (tm_tabs t))).
    eapply lc_tm_at_instantiate_identity; [exact H | exact Hgamma].
  - constructor.
  - constructor.
  - constructor.
Qed.

Lemma value_type_top_form : forall Delta Gamma v T,
  has_type Delta Gamma v T -> value v ->
  (exists T1 T2, T = Ty_Arrow T1 T2) \/
  (exists T1, T = Ty_All T1) \/ T = Ty_Int \/ T = Ty_Bool.
Proof.
  intros Delta Gamma v T Hty Hv. inversion Hv; subst; inversion Hty; subst; eauto 8.
Qed.

Lemma instantiated_value_primitive_shape : forall Delta Gamma v T theta,
  has_type Delta Gamma v T -> value v ->
  (instantiate_ty theta T = Ty_Int -> exists n, v = tm_int n) /\
  (instantiate_ty theta T = Ty_Bool -> v = tm_true \/ v = tm_false).
Proof.
  intros Delta Gamma v T theta Hty Hv.
  pose proof (value_type_top_form _ _ _ _ Hty Hv) as Hform.
  split; intro Hinst.
  - destruct Hform as [Harr|[Hall|[Hint|Hbool]]].
    + destruct Harr as [A [B HT]]. subst T. simpl in Hinst. discriminate.
    + destruct Hall as [A HT]. subst T. simpl in Hinst. discriminate.
    + subst T. eapply canonical_int; eauto.
    + subst T. simpl in Hinst. discriminate.
  - destruct Hform as [Harr|[Hall|[Hint|Hbool]]].
    + destruct Harr as [A [B HT]]. subst T. simpl in Hinst. discriminate.
    + destruct Hall as [A HT]. subst T. simpl in Hinst. discriminate.
    + subst T. simpl in Hinst. discriminate.
    + subst T. eapply canonical_bool; eauto.
Qed.

Definition primitive_value_shape (T : ty) (v : tm) : Prop :=
  match T with
  | Ty_Arrow _ _ => exists body, v = tm_abs (match T with Ty_Arrow A _ => A | _ => Ty_Int end) body
  | Ty_All _ => exists body, v = tm_tabs body
  | Ty_Int => exists n : Z, v = tm_int n
  | Ty_Bool => v = tm_true \/ v = tm_false
  | _ => True
  end.

Lemma rty_size_open_tm_rec : forall R k u,
  rty_size (open_rty_tm_rec k u R) = rty_size R.
Proof.
  induction R; intros k u; simpl; try reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR. reflexivity.
Qed.

Lemma rty_size_open_tm : forall R u,
  rty_size (open_rty_tm R u) = rty_size R.
Proof. intros. unfold open_rty_tm. apply rty_size_open_tm_rec. Qed.

Lemma rty_size_open_ty_rec : forall R k U,
  rty_size (open_rty_ty_rec k U R) = rty_size R.
Proof.
  induction R; intros k U; simpl; try reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR. reflexivity.
Qed.

Lemma rty_size_open_ty : forall R U,
  rty_size (open_rty_ty R U) = rty_size R.
Proof. intros. unfold open_rty_ty. apply rty_size_open_ty_rec. Qed.

Equations semantic_value (R : rty) (v : tm) : Prop by wf (rty_size R) lt :=
semantic_value (R_Refine T ps) v :=
  value v /\ primitive_value_shape T v /\ qualifier_holds (open_qualifier_tm ps v);
semantic_value (R_Func R1 R2) v :=
  value v /\ exists body, v = tm_abs (erase R1) body /\
  (forall w, semantic_value R1 w ->
    exists v', multi (open_tm body w) v' /\ semantic_value (open_rty_tm R2 w) v');
semantic_value (R_Exists R1 R2) v :=
  value v /\ exists w, semantic_value R1 w /\ semantic_value (open_rty_tm R2 w) v;
semantic_value (R_Poly R1) v :=
  value v /\ exists body, v = tm_tabs body /\
  (forall U, wf_ty [] U ->
    exists v', multi (open_tm_ty body U) v' /\ semantic_value (open_rty_ty R1 U) v').
Next Obligation. simpl; lia. Qed.
Next Obligation. rewrite rty_size_open_tm. simpl; lia. Qed.
Next Obligation. simpl; lia. Qed.
Next Obligation. rewrite rty_size_open_tm. simpl; lia. Qed.
Next Obligation. rewrite rty_size_open_ty. simpl; lia. Qed.

Definition semantic_term (R : rty) (t : tm) : Prop :=
  exists v, multi t v /\ semantic_value R v.

Definition semantic_context (theta : type_substitution) (RGamma : rcontext)
    (gamma : term_substitution) : Prop :=
  forall x R, lookup_rcontext x RGamma = Some R ->
    semantic_value (instantiate_rty theta gamma R) (gamma x).

Lemma semantic_value_is_value : forall R v, semantic_value R v -> value v.
Proof. intros R v H. destruct R; simp semantic_value in H; tauto. Qed.

Lemma instantiated_value_shape : forall Delta Gamma v T theta,
  has_type Delta Gamma v T -> value v ->
  primitive_value_shape (instantiate_ty theta T) (instantiate theta identity_term_substitution v).
Proof.
  intros Delta Gamma v T theta Hty Hv.
  pose proof (value_type_top_form _ _ _ _ Hty Hv) as Hform.
  destruct Hform as [Harr|[Hall|[Hint|Hbool]]].
  - destruct Harr as [A [B HT]]. subst T. simpl.
    destruct (canonical_arrow Delta Gamma v A B Hty Hv) as [body ->].
    exists (instantiate theta identity_term_substitution body). reflexivity.
  - destruct Hall as [A HT]. subst T. simpl.
    destruct (canonical_all Delta Gamma v A Hty Hv) as [body ->].
    exists (instantiate theta identity_term_substitution body). reflexivity.
  - subst T. simpl.
    destruct (canonical_int Delta Gamma v Hty Hv) as [n ->].
    exists n. reflexivity.
  - subst T. simpl. destruct (canonical_bool Delta Gamma v Hty Hv) as [E|E]; subst v; simpl; auto.
Qed.

Fixpoint logical_value (fuel : nat) (R : rty) (v : tm) : Prop :=
  match fuel with
  | 0 => True
  | S fuel' =>
      match R with
      | R_Refine T ps =>
          value v /\
          (match T with
           | Ty_Int => exists n : Z, v = tm_int n
           | Ty_Bool => v = tm_true \/ v = tm_false
           | _ => True
           end) /\
          qualifier_holds (open_qualifier_tm ps v)
      | R_Func R1 R2 =>
          value v /\ exists body, v = tm_abs (erase R1) body /\
          (forall w, logical_value fuel' R1 w ->
            exists v', multi (open_tm body w) v' /\
              logical_value fuel' (open_rty_tm R2 w) v')
      | R_Exists R1 R2 =>
          value v /\ exists w, logical_value fuel' R1 w /\
            logical_value fuel' (open_rty_tm R2 w) v
      | R_Poly R1 =>
          value v /\ exists body, v = tm_tabs body /\
            (forall U, locally_closed_ty U ->
              exists v', multi (open_tm_ty body U) v' /\
                logical_value fuel' (open_rty_ty R1 U) v')
      end
  end.

Definition logical_term (R : rty) (t : tm) : Prop :=
  exists v, multi t v /\ forall fuel, rty_size R <= fuel -> logical_value fuel R v.

Definition logical_context (theta : type_substitution) (RGamma : rcontext)
    (gamma : term_substitution) : Prop :=
  forall x R, lookup_rcontext x RGamma = Some R ->
    forall fuel, rty_size (instantiate_rty theta gamma R) <= fuel ->
      logical_value fuel (instantiate_rty theta gamma R) (gamma x).

Lemma lookup_rcontext_update_eq : forall RGamma x R,
  lookup_rcontext x (update_rcontext RGamma x R) = Some R.
Proof. intros. simpl. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma lookup_rcontext_update_neq : forall RGamma x y R,
  x <> y -> lookup_rcontext y (update_rcontext RGamma x R) = lookup_rcontext y RGamma.
Proof.
  intros RGamma x y R Hxy. simpl. destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. exfalso. apply Hxy. symmetry. exact E.
  - reflexivity.
Qed.

Lemma instantiate_update_fresh_tm : forall t theta gamma x w,
  ~ In x (fv_tm t) ->
  instantiate theta (term_subst_update gamma x w) t = instantiate theta gamma t.
Proof.
  induction t; intros theta gamma x w Hfresh; simpl in *; try reflexivity.
  - destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply Hfresh. simpl. auto.
    + unfold term_subst_update; simpl; rewrite E; reflexivity.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal; [apply IHt1 | apply IHt2]; intros Hin; apply Hfresh; apply in_or_app; auto.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal; [apply IHt1 | apply IHt2]; intros Hin; apply Hfresh; apply in_or_app; auto.
  - f_equal; [apply IHt1 | apply IHt2]; intros Hin; apply Hfresh; apply in_or_app; auto.
  - f_equal.
    + apply IHt1. intros Hin. apply Hfresh.
      apply in_app_iff. left. exact Hin.
    + apply IHt2. intros Hin. apply Hfresh.
      apply in_app_iff. right. apply in_app_iff. left. exact Hin.
    + apply IHt3. intros Hin. apply Hfresh.
      apply in_app_iff. right. apply in_app_iff. right. exact Hin.
Qed.

Lemma instantiate_update_fresh_qual : forall p theta gamma x w,
  ~ In x (fv_qualifier p) ->
  instantiate_qualifier theta (term_subst_update gamma x w) p =
  instantiate_qualifier theta gamma p.
Proof.
  induction p; intros theta gamma x w Hfresh; simpl in *; try reflexivity.
  - f_equal.
    + apply instantiate_update_fresh_tm. intros Hin. apply Hfresh. simpl. apply in_app_iff. left. exact Hin.
    + apply instantiate_update_fresh_tm. intros Hin. apply Hfresh. simpl. apply in_app_iff. right. exact Hin.
  - f_equal.
    + apply instantiate_update_fresh_tm. intros Hin. apply Hfresh. simpl. apply in_app_iff. left. exact Hin.
    + apply instantiate_update_fresh_tm. intros Hin. apply Hfresh. simpl. apply in_app_iff. right. exact Hin.
  - f_equal.
    + apply instantiate_update_fresh_tm. intros Hin. apply Hfresh. simpl. apply in_app_iff. left. exact Hin.
    + apply instantiate_update_fresh_tm. intros Hin. apply Hfresh. simpl. apply in_app_iff. right. exact Hin.
  - f_equal.
    + apply IHp1. intros Hin. apply Hfresh. simpl. apply in_app_iff. auto.
    + apply IHp2. intros Hin. apply Hfresh. simpl. apply in_app_iff. auto.
  - f_equal.
    + apply IHp1. intros Hin. apply Hfresh. simpl. apply in_app_iff. auto.
    + apply IHp2. intros Hin. apply Hfresh. simpl. apply in_app_iff. auto.
  - f_equal. apply IHp. intros Hin. apply Hfresh. simpl. auto.
Qed.

Lemma instantiate_rty_update_fresh : forall R theta gamma x w,
  ~ In x (fv_rty R) ->
  instantiate_rty theta (term_subst_update gamma x w) R =
  instantiate_rty theta gamma R.
Proof.
  induction R; intros theta gamma x w Hfresh; simpl in *.
  - f_equal. apply instantiate_update_fresh_qual. exact Hfresh.
  - f_equal.
    + apply IHR1. intros Hin; apply Hfresh; apply in_app_iff; auto.
    + apply IHR2. intros Hin; apply Hfresh; apply in_app_iff; auto.
  - f_equal.
    + apply IHR1. intros Hin; apply Hfresh; apply in_app_iff; auto.
    + apply IHR2. intros Hin; apply Hfresh; apply in_app_iff; auto.
  - f_equal. apply IHR. exact Hfresh.
Qed.

Lemma lookup_rcontext_ftv : forall RGamma x R X,
  lookup_rcontext x RGamma = Some R -> In X (ftv_rty R) -> In X (ftv_rcontext RGamma).
Proof.
  induction RGamma as [|[y S] rest IH]; intros x R X Hlook Hin; simpl in *; try discriminate.
  destruct (Nat.eqb x y) eqn:E.
  - inversion Hlook; subst. apply in_or_app. left. exact Hin.
  - apply in_or_app. right. eapply IH; eauto.
Qed.

Lemma lookup_rcontext_fv : forall RGamma x R X,
  lookup_rcontext x RGamma = Some R -> In X (fv_rty R) -> In X (fv_rcontext RGamma).
Proof.
  induction RGamma as [|[y S] rest IH]; intros x R X Hlook Hin; simpl in *; try discriminate.
  destruct (Nat.eqb x y) eqn:E.
  - inversion Hlook; subst. apply in_or_app. left. exact Hin.
  - apply in_or_app. right. eapply IH; eauto.
Qed.

Lemma rty_size_instantiate : forall theta gamma R,
  rty_size (instantiate_rty theta gamma R) = rty_size R.
Proof. intros theta gamma R. induction R; simpl; rewrite ?IHR, ?IHR1, ?IHR2; reflexivity. Qed.

Lemma logical_context_type_update_fresh : forall theta gamma RGamma X U,
  logical_context theta RGamma gamma ->
  ~ In X (ftv_rcontext RGamma) ->
  logical_context (type_subst_update theta X U) RGamma gamma.
Proof.
  intros theta gamma RGamma X U Hctx Hfresh y R Hlook n Hsize.
  rewrite rty_size_instantiate in Hsize.
  rewrite instantiate_rty_ty_update_fresh.
  - apply Hctx with (R := R); [exact Hlook|].
    rewrite rty_size_instantiate. exact Hsize.
  - intro Hin. apply Hfresh. eapply lookup_rcontext_ftv; eauto.
Qed.

Lemma semantic_context_type_update_fresh : forall theta gamma RGamma X U,
  semantic_context theta RGamma gamma ->
  ~ In X (ftv_rcontext RGamma) ->
  semantic_context (type_subst_update theta X U) RGamma gamma.
Proof.
  intros theta gamma RGamma X U Hctx Hfresh y R Hlook.
  rewrite instantiate_rty_ty_update_fresh.
  - apply Hctx with (R := R); assumption.
  - intro Hin. apply Hfresh. eapply lookup_rcontext_ftv; eauto.
Qed.

Lemma semantic_context_update : forall theta RGamma gamma x R w,
  semantic_context theta RGamma gamma ->
  (forall y S, lookup_rcontext y RGamma = Some S -> ~ In x (fv_rty S)) ->
  ~ In x (fv_rty R) ->
  semantic_value (instantiate_rty theta gamma R) w ->
  semantic_context theta (update_rcontext RGamma x R)
    (term_subst_update gamma x w).
Proof.
  intros theta RGamma gamma x R w Hctx Hfreshctx HfreshR Hw y S Hlookup.
  destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E. subst y. rewrite lookup_rcontext_update_eq in Hlookup.
    inversion Hlookup; subst.
    change (semantic_value (instantiate_rty theta (term_subst_update gamma x w) S)
      (if Nat.eqb x x then w else gamma x)).
    rewrite Nat.eqb_refl. rewrite instantiate_rty_update_fresh by exact HfreshR. exact Hw.
  - rewrite lookup_rcontext_update_neq in Hlookup by
        (intro H; subst; rewrite Nat.eqb_refl in E; discriminate).
    change (semantic_value (instantiate_rty theta (term_subst_update gamma x w) S)
      (if Nat.eqb x y then w else gamma y)).
    rewrite E. rewrite instantiate_rty_update_fresh.
    + apply Hctx with (R := S); assumption.
    + apply Hfreshctx with (y := y); assumption.
Qed.

Lemma erase_instantiate_rty : forall theta gamma R,
  erase (instantiate_rty theta gamma R) = instantiate_ty theta (erase R).
Proof.
  intros theta gamma R. induction R; simpl; try reflexivity.
  - f_equal; assumption.
  - exact IHR2.
  - f_equal; assumption.
Qed.

Lemma logical_context_update : forall theta RGamma gamma x R w,
  logical_context theta RGamma gamma ->
  (forall y S, lookup_rcontext y RGamma = Some S -> ~ In x (fv_rty S)) ->
  ~ In x (fv_rty R) ->
  (forall n, rty_size (instantiate_rty theta gamma R) <= n ->
      logical_value n (instantiate_rty theta gamma R) w) ->
  logical_context theta (update_rcontext RGamma x R)
    (term_subst_update gamma x w).
Proof.
  intros theta RGamma gamma x R w Hctx Hfreshctx HfreshR Hw y S Hlookup n Hsize.
  destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E. subst y. rewrite lookup_rcontext_update_eq in Hlookup.
    inversion Hlookup; subst.
    change (logical_value n (instantiate_rty theta (term_subst_update gamma x w) S)
      (if Nat.eqb x x then w else gamma x)).
    rewrite Nat.eqb_refl. rewrite instantiate_rty_update_fresh by exact HfreshR.
    apply Hw. rewrite instantiate_rty_update_fresh in Hsize by exact HfreshR. exact Hsize.
  - rewrite lookup_rcontext_update_neq in Hlookup by
        (intro H; subst; rewrite Nat.eqb_refl in E; discriminate).
    change (logical_value n (instantiate_rty theta (term_subst_update gamma x w) S)
      (if Nat.eqb x y then w else gamma y)).
    rewrite E. rewrite instantiate_rty_update_fresh.
    + apply Hctx with (R := S); [assumption|].
      rewrite instantiate_rty_update_fresh in Hsize.
      * exact Hsize.
      * apply Hfreshctx with (y := y); assumption.
    + apply Hfreshctx with (y := y); assumption.
Qed.

Lemma entails_sound : forall Delta RGamma p q,
  entails Delta RGamma p q -> forall theta gamma,
  type_substitution_closed theta -> term_substitution_closed gamma ->
  logical_context theta RGamma gamma ->
  qualifier_holds (instantiate_qualifier theta gamma p) ->
  qualifier_holds (instantiate_qualifier theta gamma q).
Proof.
  intros Delta RGamma p q Hent. induction Hent;
    intros theta gamma Htheta Hgamma Hctx Hholds; simpl in *.
  - exact Hholds.
  - exact I.
  - apply IHHent2 with (theta := theta) (gamma := gamma); auto.
  - exact (proj1 Hholds).
  - exact (proj2 Hholds).
  - split.
    + apply IHHent1 with (theta := theta) (gamma := gamma); auto.
    + apply IHHent2 with (theta := theta) (gamma := gamma); auto.
  - left. exact Hholds.
  - right. exact Hholds.
  - destruct Hholds as [Hp | Hq].
    + apply IHHent1 with (theta := theta) (gamma := gamma); auto.
    + apply IHHent2 with (theta := theta) (gamma := gamma); auto.
  - simpl. intro Hq. apply (IHHent theta gamma Htheta Hgamma Hctx).
    exact (conj Hholds Hq).
  - simpl in Hholds. destruct Hholds as [Hp Hnot]. contradiction.
  - unfold open_qualifier_tm.
    rewrite instantiate_open_qualifier_tm_rec by exact Hgamma.
    specialize (Hctx x (R_Refine T p) H 1).
    specialize (Hctx (le_n 1)).
    simpl in Hctx. destruct Hctx as [_ [_ Hq]]. exact Hq.
  - simpl in Hholds. contradiction.
Qed.

Lemma multi_app_left : forall t t' u,
  multi t t' -> locally_closed_tm u -> multi (tm_app t u) (tm_app t' u).
Proof. intros t t' u Hm. induction Hm; intros Hlc.
  - apply multi_refl.
  - econstructor. apply ST_App1; eauto. apply IHHm. exact Hlc.
Qed.

Lemma multi_app_right : forall v t t',
  value v -> multi t t' -> multi (tm_app v t) (tm_app v t').
Proof. intros v t t' Hv Hm. induction Hm.
  - apply multi_refl.
  - econstructor. apply ST_App2; eauto. apply IHHm.
Qed.

Lemma multi_tapp_left : forall t t' T,
  multi t t' -> locally_closed_ty T ->
  multi (tm_tapp t T) (tm_tapp t' T).
Proof. intros t t' T Hm. induction Hm; intros HT.
  - apply multi_refl.
  - econstructor. apply ST_TApp; eauto. apply IHHm. exact HT.
Qed.

Lemma multi_div_left : forall t t' u,
  multi t t' -> locally_closed_tm u -> multi (tm_div t u) (tm_div t' u).
Proof. intros t t' u Hm. induction Hm; intros Hlc.
  - apply multi_refl.
  - econstructor. apply ST_Div1; eauto. apply IHHm. exact Hlc.
Qed.

Lemma multi_div_right : forall v t t',
  value v -> multi t t' -> multi (tm_div v t) (tm_div v t').
Proof. intros v t t' Hv Hm. induction Hm.
  - apply multi_refl.
  - econstructor. apply ST_Div2; eauto. apply IHHm.
Qed.

Lemma multi_arith_left : forall op t t' u,
  multi t t' -> locally_closed_tm u ->
  multi (tm_arith op t u) (tm_arith op t' u).
Proof. intros op t t' u Hm. induction Hm; intros Hlc.
  - apply multi_refl.
  - econstructor. apply ST_Arith1; eauto. apply IHHm. exact Hlc.
Qed.

Lemma multi_arith_right : forall op v t t',
  value v -> multi t t' ->
  multi (tm_arith op v t) (tm_arith op v t').
Proof. intros op v t t' Hv Hm. induction Hm.
  - apply multi_refl.
  - econstructor. apply ST_Arith2; eauto. apply IHHm.
Qed.

Lemma multi_if_cond : forall t t' u v,
  multi t t' -> locally_closed_tm u -> locally_closed_tm v ->
  multi (tm_if t u v) (tm_if t' u v).
Proof. intros t t' u v Hm. induction Hm; intros Hu Hv.
  - apply multi_refl.
  - econstructor. apply ST_If; eauto. apply IHHm; assumption.
Qed.

Lemma logical_value_is_value : forall n R v,
  0 < n -> logical_value n R v -> value v.
Proof.
  intros n R v Hn Hrel. destruct n; [lia|].
  destruct R; simpl in Hrel; tauto.
Qed.

Lemma logical_refine_int_shape : forall n ps v,
  rty_size (R_Refine Ty_Int ps) <= n ->
  logical_value n (R_Refine Ty_Int ps) v -> exists m : Z, v = tm_int m.
Proof.
  intros n ps v Hsize Hrel. destruct n; [simpl in Hsize; lia|].
  simpl in Hrel. exact (proj1 (proj2 Hrel)).
Qed.

Lemma logical_refine_bool_shape : forall n ps v,
  rty_size (R_Refine Ty_Bool ps) <= n ->
  logical_value n (R_Refine Ty_Bool ps) v -> v = tm_true \/ v = tm_false.
Proof.
  intros n ps v Hsize Hrel. destruct n; [simpl in Hsize; lia|].
  simpl in Hrel. exact (proj1 (proj2 Hrel)).
Qed.

Lemma logical_nonzero_integer : forall n m,
  0 < n ->
  logical_value n (R_Refine Ty_Int (Pred_Ne (tm_bvar 0) (tm_int 0%Z)))
    (tm_int m) -> m <> 0%Z.
Proof.
  intros n m Hn Hrel. destruct n; [lia|].
  simpl in Hrel. destruct Hrel as [_ [_ Hqual]].
  apply nonzero_integer_holds. exact Hqual.
Qed.

Lemma step_deterministic : forall t u v, t --> u -> t --> v -> u = v.
Proof.
  intros t u v Hstep. revert v.
  induction Hstep; intros v0 Hother; inversion Hother; subst;
    try reflexivity; try congruence;
    try solve [match goal with
      | Hv : value ?x, Hs : ?x --> ?y |- _ =>
          exfalso; exact (value_no_step x Hv y Hs)
      end];
    try solve [match goal with
      | Hlc : locally_closed_tm (tm_abs ?T ?b),
        Hs : tm_abs ?T ?b --> ?u |- _ =>
          exfalso; eapply value_no_step; [apply v_abs; exact Hlc | exact Hs]
      | Hlc : locally_closed_tm (tm_tabs ?b),
        Hs : tm_tabs ?b --> ?u |- _ =>
          exfalso; eapply value_no_step; [apply v_tabs; exact Hlc | exact Hs]
      | Hs : tm_int ?n --> ?u |- _ =>
          exfalso; exact (value_no_step (tm_int n) (v_int n) u Hs)
      | Hs : tm_true --> ?u |- _ =>
          exfalso; exact (value_no_step tm_true v_true u Hs)
      | Hs : tm_false --> ?u |- _ =>
          exfalso; exact (value_no_step tm_false v_false u Hs)
      end];
    try solve [match goal with Hs : ?x --> ?y |- _ => inversion Hs end];
    try solve [f_equal; eauto].
Qed.

Lemma multi_comparable : forall t u v,
  multi t u -> multi t v -> multi u v \/ multi v u.
Proof.
  intros t u v Hleft. revert v.
  induction Hleft; intros v Hright.
  - left. exact Hright.
  - inversion Hright; subst.
    + right. econstructor; eauto.
    + pose proof (step_deterministic _ _ _ H H0) as Heq. subst t4.
      destruct (IHHleft _ H1) as [Huv | Hvu].
      * left. exact Huv.
      * right. exact Hvu.
Qed.

Lemma safety_from_value_path : forall t t' v,
  multi t t' -> multi t v -> value v ->
  value t' \/ exists u, t' --> u.
Proof.
  intros t t' v Hstate Hfinal Hv.
  destruct (multi_comparable _ _ _ Hstate Hfinal) as [Htf | Hft].
  - inversion Htf; subst.
    + left. exact Hv.
    + right. eauto.
  - left. pose proof (value_multi_eq _ _ Hv Hft) as Heq. now subst.
Qed.

Lemma rty_size_positive : forall R, 0 < rty_size R.
Proof. destruct R; simpl; lia. Qed.

Lemma logical_term_safe : forall R t t',
  logical_term R t -> multi t t' ->
  value t' \/ exists u, t' --> u.
Proof.
  intros R t t' [v [Htv Hrel]] Hstate.
  eapply safety_from_value_path; [exact Hstate | exact Htv |].
  eapply logical_value_is_value with (n := rty_size R) (R := R).
  - apply rty_size_positive.
  - apply Hrel. lia.
Qed.

Lemma multi_drop_deterministic_step : forall t u v,
  t --> u -> multi t v -> value v -> multi u v.
Proof.
  intros t u v Hstep Hmulti. induction Hmulti.
  - intro Hv. exfalso. exact (value_no_step t Hv u Hstep).
  - assert (t2 = u) by (eapply step_deterministic; eauto).
    subst. intro Hv. exact Hmulti.
Qed.

Lemma logical_term_step : forall R t u,
  t --> u -> logical_term R t -> logical_term R u.
Proof.
  intros R t u Hstep [v [Htv Hrel]].
  exists v. split.
  - eapply multi_drop_deterministic_step; [exact Hstep|exact Htv|].
    eapply logical_value_is_value with (n := rty_size R) (R := R).
    + apply rty_size_positive.
    + apply Hrel. lia.
  - exact Hrel.
Qed.

Lemma logical_term_multi_safe : forall R t t',
  logical_term R t -> multi t t' ->
  value t' \/ exists u, t' --> u.
Proof.
  intros R t t' Hrel Hmulti. revert Hrel.
  induction Hmulti; intros Hrel.
  - eapply logical_term_safe; eauto using multi_refl.
  - apply IHHmulti. eapply logical_term_step; eauto.
Qed.


Theorem never_stuck : forall (t t' : tm) (R : rty),
  has_rtype [] empty_rcontext t R ->
  multi t t' ->
  value t' \/ exists t'' : tm, t' --> t''.
Proof.
  (* Complete this proof. *)
Qed.

End SystemFRefinementIfTask.
