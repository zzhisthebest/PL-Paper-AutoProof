From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
From Stdlib Require Import ZArith.BinInt.

Module SystemFRefinementNonDeterminism.

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
      lc_tm_at K k t1 ->
      lc_tm_at K k t2 ->
      lc_tm_at K k (tm_arith op t1 t2)
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
  | v_int : forall n : Z, value (tm_int n).

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

End SystemFRefinementNonDeterminism.

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
Module SystemFRefinementNonDeterminismInfrastructure.
Import ListNotations.
Import SystemFRefinementNonDeterminism.

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
  - try (inversion Hlc; subst). apply lc_tm_choice; eauto.
Qed.

Lemma open_ty_rec_lc_at : forall T k U,
  lc_ty_at k T ->
  open_ty_rec k U T = T.
Proof.
  intros T k U Hlc. induction Hlc; simpl; try rewrite ?IHHlc1, ?IHHlc2;
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
    try rewrite ?IHHlc, ?IHHlc1, ?IHHlc2; try reflexivity.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + reflexivity.
Qed.

Lemma open_tm_ty_rec_lc_at : forall t K k U,
  lc_tm_at K k t ->
  open_tm_ty_rec K U t = t.
Proof.
  intros t K k U Hlc. induction Hlc; simpl;
    try rewrite ?IHHlc1, ?IHHlc2; try reflexivity.
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

End SystemFRefinementNonDeterminismInfrastructure.

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
Module SystemFRefinementNonDeterminismCoreTyping.
Import ListNotations.
Import SystemFRefinementNonDeterminism.
Import SystemFRefinementNonDeterminismInfrastructure.

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

End SystemFRefinementNonDeterminismCoreTyping.

From Stdlib Require Import Arith.PeanoNat Lists.List ZArith.BinInt.
Module SystemFRefinementNonDeterminismLogic.
Import ListNotations SystemFRefinementNonDeterminism.

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

End SystemFRefinementNonDeterminismLogic.

From Stdlib Require Import Arith.PeanoNat Lists.List Lia ZArith.BinInt.
Module SystemFRefinementNonDeterminismTyping.
Import ListNotations.
Import SystemFRefinementNonDeterminism.
Export SystemFRefinementNonDeterminismLogic.

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
  end.

End SystemFRefinementNonDeterminismTyping.

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Module SystemFRefinementNonDeterminismEvaluation.
Import ListNotations SystemFRefinementNonDeterminism SystemFRefinementNonDeterminismInfrastructure
  SystemFRefinementNonDeterminismCoreTyping.

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

End SystemFRefinementNonDeterminismEvaluation.

From Stdlib Require Import Arith.PeanoNat Lists.List Lia Program.Wf.
From Equations Require Import Equations.
Module SystemFRefinementNonDeterminismSubstitution.
Import ListNotations.
Import SystemFRefinementNonDeterminism.
Import SystemFRefinementNonDeterminismInfrastructure.
Import SystemFRefinementNonDeterminismCoreTyping.
Import SystemFRefinementNonDeterminismTyping.
Import SystemFRefinementNonDeterminismEvaluation.

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
End SystemFRefinementNonDeterminismSubstitution.

Module SystemFRefinementNonDeterminismTask.
Import ListNotations SystemFRefinementNonDeterminism SystemFRefinementNonDeterminismInfrastructure SystemFRefinementNonDeterminismCoreTyping SystemFRefinementNonDeterminismLogic SystemFRefinementNonDeterminismTyping SystemFRefinementNonDeterminismEvaluation SystemFRefinementNonDeterminismSubstitution .

Lemma erase_open_tm_rec : forall R k u, erase (open_rty_tm_rec k u R) = erase R.
Proof.
  induction R; intros; simpl; try rewrite IHR1; try rewrite IHR2; try rewrite IHR; reflexivity.
Qed.
Lemma erase_open_tm : forall R u, erase (open_rty_tm R u) = erase R.
Proof. intros; apply erase_open_tm_rec. Qed.

Lemma erase_open_ty_rec : forall R k U, erase (open_rty_ty_rec k U R) = open_ty_rec k U (erase R).
Proof.
  induction R; intros; simpl; try rewrite IHR1; try rewrite IHR2; try rewrite IHR;
    reflexivity.
Qed.
Lemma erase_open_ty : forall R U, erase (open_rty_ty R U) = open_ty (erase R) U.
Proof. intros; apply erase_open_ty_rec. Qed.

Lemma open_ty_rec_fresh_inj : forall k X T U,
  ~ In X (fv_ty T) -> ~ In X (fv_ty U) ->
  open_ty_rec k (Ty_FVar X) T = open_ty_rec k (Ty_FVar X) U -> T = U.
Proof.
  intros k X T. revert k.
  induction T; intros k U HXT HXU Heq; destruct U; simpl in Heq;
    try discriminate; try (inversion Heq; subst; reflexivity).
  - destruct (Nat.eqb k n) eqn:En, (Nat.eqb k n0) eqn:Em;
      simpl in Heq; try discriminate; inversion Heq; subst; f_equal; try congruence.
    apply Nat.eqb_eq in En. apply Nat.eqb_eq in Em. lia.
  - destruct (Nat.eqb k n) eqn:En; simpl in Heq.
    + inversion Heq; subst. exfalso. apply HXU. simpl. now left.
    + discriminate.
  - destruct (Nat.eqb k n); discriminate.
  - destruct (Nat.eqb k n); discriminate.
  - destruct (Nat.eqb k n); discriminate.
  - destruct (Nat.eqb k n) eqn:En; simpl in Heq.
    + inversion Heq; subst. exfalso. apply HXT. simpl. now left.
    + discriminate.
  - destruct (Nat.eqb k n); discriminate.
  - inversion Heq; subst. f_equal.
    + eapply IHT1; [| | exact H0].
      * intro Hin. apply HXT. apply in_or_app. left. exact Hin.
      * intro Hin. apply HXU. apply in_or_app. left. exact Hin.
    + eapply IHT2; [| | exact H1].
      * intro Hin. apply HXT. apply in_or_app. right. exact Hin.
      * intro Hin. apply HXU. apply in_or_app. right. exact Hin.
  - destruct (Nat.eqb k n); discriminate.
  - inversion Heq; subst. f_equal. eapply IHT; [exact HXT|exact HXU|exact H0].
  - destruct (Nat.eqb k n); discriminate.
Qed.

Lemma subtype_erase : forall Delta RGamma R S,
  subtype Delta RGamma R S -> erase R = erase S.
Proof.
  intros Delta RGamma R S H. induction H; simpl in *; try congruence.
  - f_equal.
    + symmetry. exact IHsubtype.
    + specialize (H1 (fresh L) (fresh_notin L)).
      rewrite !erase_open_tm in H1. exact H1.
  all: simpl in *; try rewrite erase_open_tm_rec in *;
    try rewrite erase_open_ty_rec in *; intuition congruence; eauto 8.
  - match goal with Hih : erase _ = erase _ |- _ =>
      rewrite erase_open_tm in Hih; exact Hih end.
  - match goal with Hih : forall x, _ |- _ =>
      specialize (Hih (fresh L) (fresh_notin L));
      rewrite erase_open_tm in Hih; exact Hih end.
  - set (X0 := fresh (L ++ fv_ty (erase R) ++ fv_ty (erase S))).
    assert (HXL : ~ In X0 L).
    { unfold X0. intro Hin. apply fresh_notin with
        (L := L ++ fv_ty (erase R) ++ fv_ty (erase S)).
      apply in_or_app. left. exact Hin. }
    assert (HXR : ~ In X0 (fv_ty (erase R))).
    { unfold X0. intro Hin. apply fresh_notin with
        (L := L ++ fv_ty (erase R) ++ fv_ty (erase S)).
      apply in_or_app. right. apply in_or_app. left. exact Hin. }
    assert (HXS : ~ In X0 (fv_ty (erase S))).
    { unfold X0. intro Hin. apply fresh_notin with
        (L := L ++ fv_ty (erase R) ++ fv_ty (erase S)).
      apply in_or_app. right. apply in_or_app. right. exact Hin. }
    specialize (H0 X0 HXL). rewrite !erase_open_ty in H0.
    simpl in H0. f_equal. eapply open_ty_rec_fresh_inj; eauto.
Qed.

Lemma wf_rty_erases : forall Delta RGamma R,
  wf_rty Delta RGamma R -> wf_ty Delta (erase R).
Proof.
  intros Delta RGamma R H. induction H; simpl.
  - assumption.
  - apply WF_Arrow; [exact IHwf_rty|].
    specialize (H1 (fresh L) (fresh_notin L)).
    rewrite erase_open_tm in H1. exact H1.
  - specialize (H1 (fresh L) (fresh_notin L)).
    rewrite erase_open_tm in H1. exact H1.
  - apply WF_All with (L := L). intros X HX.
    specialize (H0 X HX). rewrite erase_open_ty in H0. exact H0.
Qed.

Lemma lookup_rcontext_erases : forall x RGamma R,
  lookup_rcontext x RGamma = Some R ->
  lookup_context x (erase_context RGamma) = Some (erase R).
Proof.
  intros x RGamma. induction RGamma as [|[y S] RGamma IH]; intros R H; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + inversion H; subst. simpl. reflexivity.
    + simpl. eapply IH. exact H.
Qed.

Lemma has_rtype_erases : forall Delta RGamma t R,
  has_rtype Delta RGamma t R ->
  has_type Delta (erase_context RGamma) t (erase R).
Proof.
  intros Delta RGamma t R H. induction H; simpl in *.
  - eapply T_Var.
    + eapply lookup_rcontext_erases. exact H.
    + eapply wf_rty_erases. exact H0.
  - eapply T_Abs with (L := L).
    + eapply wf_rty_erases. exact H.
    + intros x Hx. specialize (H1 x Hx).
      rewrite erase_open_tm in H1. exact H1.
  - eapply T_App; eauto.
  - eapply T_TAbs with (L := L). intros X HX.
    specialize (H0 X HX). rewrite erase_open_ty in H0. exact H0.
  - rewrite erase_open_ty. eapply T_TApp; eauto.
  - constructor.
  - eapply T_Div; eauto.
  - eapply T_Arith; eauto.
  - eapply T_Choice; eauto.
  - eauto.
  - rewrite <- (subtype_erase _ _ _ _ H1). exact IHhas_rtype.
Qed.

Lemma predicate_multistep_trans : forall t u v,
  predicate_multistep t u -> predicate_multistep u v ->
  predicate_multistep t v.
Proof. intros t u v H. induction H; eauto using predicate_multistep. Qed.

Lemma multi_as_predicate_multistep : forall t u,
  multi t u -> predicate_multistep t u.
Proof. intros t u H. induction H; eauto using predicate_multistep. Qed.

Lemma predicate_nonzero : forall t,
  qualifier_holds (Pred_Ne t (tm_int 0%Z)) ->
  ~ predicate_multistep t (tm_int 0%Z).
Proof.
  intros t Hneq Hzero. unfold qualifier_holds, predicate_holds in Hneq.
  simpl in Hneq. apply Hneq. exists (tm_int 0%Z). split; [exact Hzero|].
  split; [constructor|constructor].
Qed.

Lemma nonzero_multistep : forall t u,
  qualifier_holds (Pred_Ne t (tm_int 0%Z)) ->
  multi t u ->
  ~ predicate_multistep u (tm_int 0%Z).
Proof.
  intros t u Hneq Htu Huzero.
  apply (predicate_nonzero t Hneq).
  eapply predicate_multistep_trans; eauto using multi_as_predicate_multistep.
Qed.

Lemma nonzero_integer_result : forall t n,
  qualifier_holds (Pred_Ne t (tm_int 0%Z)) ->
  multi t (tm_int n) -> n <> 0%Z.
Proof.
  intros t n Hnz Hmulti Heq. subst n.
  apply (nonzero_multistep t (tm_int 0%Z) Hnz Hmulti).
  constructor.
Qed.

Lemma lookup_update_ext : forall Gamma Gamma' x T,
  (forall z, lookup_context z Gamma = lookup_context z Gamma') ->
  forall z, lookup_context z (update Gamma x T) =
            lookup_context z (update Gamma' x T).
Proof.
  intros Gamma Gamma' x T Heq z. unfold update. simpl.
  destruct (Nat.eqb z x); auto.
Qed.

Lemma lookup_update_swap : forall Gamma x Tx y Ty,
  x <> y -> forall z,
  lookup_context z (update (update Gamma x Tx) y Ty) =
  lookup_context z (update (update Gamma y Ty) x Tx).
Proof.
  intros Gamma x Tx y Ty Hxy z. unfold update. simpl.
  destruct (Nat.eqb z y) eqn:Ezy.
  - destruct (Nat.eqb z x) eqn:Ezx.
    + apply Nat.eqb_eq in Ezy. apply Nat.eqb_eq in Ezx. subst. contradiction.
    + reflexivity.
  - destruct (Nat.eqb z x) eqn:Ezx.
    + reflexivity.
    + reflexivity.
Qed.

Lemma lookup_in_dom_context : forall x Gamma T,
  lookup_context x Gamma = Some T -> In x (dom_context Gamma).
Proof.
  intros x Gamma. induction Gamma as [|[y U] Gamma IH]; intros T H; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + left. apply Nat.eqb_eq in E. symmetry. exact E.
    + right. eapply IH. exact H.
Qed.

Lemma has_type_context_included : forall Delta Gamma t T,
  has_type Delta Gamma t T -> forall Gamma',
  context_included Gamma Gamma' -> has_type Delta Gamma' t T.
Proof.
  intros Delta Gamma t T H. induction H; intros Gamma' Hincl.
  - eapply T_Var; [eapply Hincl; exact H|exact H0].
  - eapply T_Abs with (L := L); [exact H|].
    intros x Hx. eapply (H1 x Hx). intros z Tz Hz.
    unfold update. simpl. destruct (Nat.eqb z x) eqn:E.
    + apply Nat.eqb_eq in E. subst z. simpl in Hz. rewrite Nat.eqb_refl in Hz. inversion Hz; subst. reflexivity.
    + simpl in Hz. rewrite E in Hz. eapply Hincl. exact Hz.
  - eapply T_App; eauto.
  - eapply T_TAbs with (L := L); eauto.
  - eapply T_TApp; eauto.
  - constructor.
  - eapply T_Div; eauto.
  - eapply T_Arith; eauto.
  - eapply T_Choice; eauto.
Qed.

Lemma ty_context_included_cons : forall Delta Delta' X,
  ty_context_included Delta Delta' ->
  ty_context_included (X :: Delta) (X :: Delta').
Proof.
  intros Delta Delta' X Hincl Y [Heq|Hin].
  - subst. now left.
  - right. apply Hincl. exact Hin.
Qed.

Lemma wf_ty_context_included : forall Delta T,
  wf_ty Delta T -> forall Delta', ty_context_included Delta Delta' -> wf_ty Delta' T.
Proof.
  intros Delta T H. induction H; intros Delta' Hincl.
  - constructor. apply Hincl. exact H.
  - constructor; eauto.
  - eapply WF_All with (L := L). intros X HX.
    eapply H0; [exact HX|]. apply ty_context_included_cons. exact Hincl.
  - constructor.
Qed.

Lemma has_type_type_context_included : forall Delta Gamma t T,
  has_type Delta Gamma t T -> forall Delta',
  ty_context_included Delta Delta' -> has_type Delta' Gamma t T.
Proof.
  intros Delta Gamma t T H. induction H; intros Delta' Hincl.
  - eapply T_Var; [exact H|]. eapply wf_ty_context_included; eauto.
  - eapply T_Abs with (L := L).
    + eapply wf_ty_context_included; eauto.
    + intros x Hx. eapply H1; eauto.
  - eapply T_App; eauto.
  - eapply T_TAbs with (L := L). intros X HX.
    eapply H0; [exact HX|]. apply ty_context_included_cons. exact Hincl.
  - eapply T_TApp; [eauto|]. eapply wf_ty_context_included; eauto.
  - constructor.
  - eapply T_Div; eauto.
  - eapply T_Arith; eauto.
  - eapply T_Choice; eauto.
Qed.

Lemma context_included_fresh_update : forall Gamma y T,
  ~ In y (dom_context Gamma) -> context_included Gamma (update Gamma y T).
Proof.
  intros Gamma y T Hy x U Hlookup. unfold context_included.
  unfold update. simpl. destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E. subst x.
    exfalso. apply Hy. eapply lookup_in_dom_context. exact Hlookup.
  - exact Hlookup.
Qed.

Lemma has_type_context_equiv : forall Delta Gamma t T,
  has_type Delta Gamma t T -> forall Gamma',
  (forall x, lookup_context x Gamma = lookup_context x Gamma') ->
  has_type Delta Gamma' t T.
Proof.
  intros Delta Gamma t T H. induction H; intros Gamma' Heq.
  - eapply T_Var.
    + rewrite <- (Heq x). exact H.
    + exact H0.
  - eapply T_Abs with (L := L).
    + exact H.
    + intros y Hy. eapply H1.
      * exact Hy.
      * eapply lookup_update_ext. exact Heq.
  - eapply T_App; eauto.
  - eapply T_TAbs with (L := L); eauto.
  - eapply T_TApp; eauto.
  - constructor.
  - eapply T_Div; eauto.
  - eapply T_Arith; eauto.
  - eapply T_Choice; eauto.
Qed.

Lemma open_tm_rec_closed : forall v k y,
  locally_closed_tm v -> open_tm_rec k (tm_fvar y) v = v.
Proof.
  intros v k y Hlc. eapply open_tm_rec_lc_at with (K := 0).
  eapply lc_tm_at_monotone; [exact Hlc|lia|lia].
Qed.

Lemma tm_subst_open_commute_rec : forall t k x v y,
  x <> y ->
  locally_closed_tm v ->
  tm_subst x v (open_tm_rec k (tm_fvar y) t) =
  open_tm_rec k (tm_fvar y) (tm_subst x v t).
Proof.
  induction t; intros k x v y Hxy Hlc; simpl;
    try rewrite ?IHt by assumption; try rewrite ?IHt1 by assumption;
    try rewrite ?IHt2 by assumption; try reflexivity.
  - destruct (Nat.eqb k n); simpl.
    + destruct (Nat.eqb x y) eqn:E.
      * apply Nat.eqb_eq in E. contradiction.
      * reflexivity.
    + reflexivity.
  - destruct (Nat.eqb x a); simpl.
    + rewrite open_tm_rec_closed by exact Hlc. reflexivity.
    + reflexivity.
Qed.

Lemma tm_subst_open_commute : forall t x v y,
  x <> y ->
  locally_closed_tm v ->
  tm_subst x v (open_tm t (tm_fvar y)) =
  open_tm (tm_subst x v t) (tm_fvar y).
Proof. intros. apply tm_subst_open_commute_rec; assumption. Qed.

Lemma open_tm_ty_rec_closed : forall v k U,
  locally_closed_tm v -> open_tm_ty_rec k U v = v.
Proof.
  intros v k U Hlc. eapply open_tm_ty_rec_lc_at with (k := 0).
  eapply lc_tm_at_monotone; [exact Hlc|lia|lia].
Qed.

Lemma tm_subst_open_tm_ty_rec : forall t k U x v,
  locally_closed_tm v ->
  tm_subst x v (open_tm_ty_rec k U t) =
  open_tm_ty_rec k U (tm_subst x v t).
Proof.
  induction t; intros k U x v Hlc; simpl;
    try rewrite ?IHt by exact Hlc; try rewrite ?IHt1 by exact Hlc;
    try rewrite ?IHt2 by exact Hlc; try reflexivity.
  - destruct (Nat.eqb x a); simpl; try reflexivity.
    rewrite open_tm_ty_rec_closed by exact Hlc. reflexivity.
Qed.

Lemma tm_subst_open_tm_ty : forall t U x v,
  locally_closed_tm v ->
  tm_subst x v (open_tm_ty t U) = open_tm_ty (tm_subst x v t) U.
Proof. intros. apply tm_subst_open_tm_ty_rec. assumption. Qed.

Lemma has_type_substitution_gen : forall Delta Gamma0 t U,
  has_type Delta Gamma0 t U ->
  forall Gamma x T,
  (forall z, lookup_context z Gamma0 = lookup_context z (update Gamma x T)) ->
  forall v, has_type Delta Gamma v T -> locally_closed_tm v ->
  has_type Delta Gamma (tm_subst x v t) U.
Proof.
  intros Delta Gamma0 t U H. induction H; intros Gsub xsub Tsub Heq vsub Hv Hlc.
  - simpl. destruct (Nat.eqb x xsub) eqn:E.
    + apply Nat.eqb_eq in E. subst x.
      rewrite (Heq xsub) in H. rewrite lookup_context_update_eq in H.
      inversion H; subst. rewrite Nat.eqb_refl. exact Hv.
    + rewrite Nat.eqb_sym. rewrite E. apply T_Var with (T := T).
      * rewrite (Heq x) in H. rewrite lookup_context_update_neq in H.
        -- exact H.
        -- intro Hbad. subst. apply Nat.eqb_neq in E. apply E. reflexivity.
      * exact H0.
  - simpl. eapply T_Abs with (L := L ++ xsub :: dom_context Gsub).
    + exact H.
    + intros y Hy.
      assert (Hy0 : ~ In y L).
      { intro Hin. apply Hy. apply in_or_app. left. exact Hin. }
      assert (Hxy : xsub <> y).
      { intro Hbad. subst y. apply Hy. apply in_or_app. right. simpl. now left. }
      assert (HyDom : ~ In y (dom_context Gsub)).
      { intro Hin. apply Hy. apply in_or_app. right. simpl. now right. }
      specialize (H0 y Hy0).
      assert (Heqbody : forall z,
        lookup_context z (update Gamma y T1) =
        lookup_context z (update (update Gsub y T1) xsub Tsub)).
      { intro z. transitivity (lookup_context z (update (update Gsub xsub Tsub) y T1)).
        - apply lookup_update_ext. exact Heq.
        - symmetry. apply lookup_update_swap. congruence. }
      assert (Hv' : has_type Delta (update Gsub y T1) vsub Tsub).
      { eapply has_type_context_included; [exact Hv|].
        apply context_included_fresh_update. exact HyDom. }
      specialize (H1 y Hy0 (update Gsub y T1) xsub Tsub Heqbody vsub Hv' Hlc).
      rewrite tm_subst_open_commute in H1 by assumption.
      exact H1.
  - simpl. eapply T_App; eauto using has_type_context_equiv.
  - simpl. eapply T_TAbs with (L := L). intros X HX.
    assert (HvX : has_type (X :: Delta) Gsub vsub Tsub).
    { eapply has_type_type_context_included; [exact Hv|].
      intros Y HY. right. exact HY. }
    specialize (H0 X HX Gsub xsub Tsub Heq vsub HvX Hlc).
    rewrite tm_subst_open_tm_ty in H0 by exact Hlc. exact H0.
  - simpl. eapply T_TApp; eauto.
  - simpl. constructor.
  - simpl. eapply T_Div; eauto using has_type_context_equiv.
  - simpl. eapply T_Arith; eauto using has_type_context_equiv.
  - simpl. eapply T_Choice; eauto using has_type_context_equiv.
Qed.

Lemma has_type_substitution : forall Delta Gamma x T t U,
  has_type Delta (update Gamma x T) t U ->
  forall v, has_type Delta Gamma v T -> locally_closed_tm v ->
  has_type Delta Gamma (tm_subst x v t) U.
Proof.
  intros Delta Gamma x T t U H v Hv Hlc.
  eapply has_type_substitution_gen with (Gamma0 := update Gamma x T); eauto.
Qed.

Lemma rty_size_open_tm_rec : forall R k u,
  rty_size (open_rty_tm_rec k u R) = rty_size R.
Proof. intros R; induction R; intros k u; simpl; rewrite ?IHR1, ?IHR2, ?IHR; reflexivity. Qed.
Lemma rty_size_open_tm : forall R u,
  rty_size (open_rty_tm R u) = rty_size R.
Proof. intros; apply rty_size_open_tm_rec. Qed.

Lemma rty_size_open_ty_rec : forall R k U,
  rty_size (open_rty_ty_rec k U R) = rty_size R.
Proof. intros R; induction R; intros k U; simpl; rewrite ?IHR1, ?IHR2, ?IHR; reflexivity. Qed.
Lemma rty_size_open_ty : forall R U,
  rty_size (open_rty_ty R U) = rty_size R.
Proof. intros; apply rty_size_open_ty_rec. Qed.

(* Values of refinements satisfy their operational predicates.  At function,
   existential, and polymorphic types the index decreases, so the relation is
   well-founded even though codomains are opened at run time.  The expression
   interpretation asks for progress at every reachable state and checks the
   value relation at every reachable value. *)
Fixpoint logical_value (fuel : nat) (R : rty) (v : tm) {struct fuel} : Prop :=
  match fuel with
  | 0 => match R with
         | R_Refine _ ps => value v /\ qualifier_holds (open_qualifier_tm ps v)
         | _ => True
         end
  | S k =>
      match R with
      | R_Refine _ ps => value v /\ qualifier_holds (open_qualifier_tm ps v)
      | R_Func A B => value v /\ forall u,
          logical_value k A u ->
          logical_expr k (open_rty_tm B u) (tm_app v u)
      | R_Exists A B => exists w,
          logical_value k A w /\ logical_value k (open_rty_tm B w) v
      | R_Poly B => value v /\ forall U,
          locally_closed_ty U -> logical_value k (open_rty_ty B U) v
      end
  end
with logical_expr (fuel : nat) (R : rty) (t : tm) {struct fuel} : Prop :=
  match fuel with
  | 0 => True
  | S k => forall u, multi t u ->
      (value u \/ (exists u', u --> u')) /\
      (value u -> logical_value k R u)
  end.

Definition logical_context (fuel : nat) (theta : type_substitution)
    (gamma : term_substitution) (RGamma : rcontext) : Prop :=
  forall x R, lookup_rcontext x RGamma = Some R ->
    logical_value fuel (instantiate_rty theta gamma R) (gamma x).

Lemma logical_expr_step_closure : forall n R t,
  (value t \/ exists u, t --> u) ->
  (value t -> logical_value n R t) ->
  (forall u, t --> u -> logical_expr (S n) R u) ->
  logical_expr (S n) R t.
Proof.
  intros n R t Hprog Hval Hnext u Hmulti. induction Hmulti.
  - split; [exact Hprog|exact Hval].
  - specialize (Hnext t2 H). simpl in Hnext. exact (Hnext t3 Hmulti).
Qed.

Lemma logical_expr_step_inv : forall n R t u,
  logical_expr (S n) R t -> t --> u -> logical_expr (S n) R u.
Proof.
  intros n R t u Hrel Hstep z Hmulti.
  unfold logical_expr in Hrel; simpl in Hrel.
  assert (Htz : multi t z) by (eapply multi_step; eassumption).
  specialize (Hrel z Htz). exact Hrel.
Qed.

Lemma instantiate_ty_identity : forall T,
  instantiate_ty identity_type_substitution T = T.
Proof. induction T; simpl; try rewrite ?IHT1, ?IHT2, ?IHT; try reflexivity. Qed.

Lemma instantiate_identity : forall t,
  instantiate identity_type_substitution identity_term_substitution t = t.
Proof.
  induction t; simpl; try rewrite ?instantiate_ty_identity, ?IHt, ?IHt1, ?IHt2;
    try reflexivity.
Qed.

Lemma instantiate_qualifier_identity : forall p,
  instantiate_qualifier identity_type_substitution identity_term_substitution p = p.
Proof.
  induction p; simpl; try rewrite ?IHp, ?IHp1, ?IHp2; try rewrite ?instantiate_identity;
    reflexivity.
Qed.

Lemma instantiate_rty_identity : forall R,
  instantiate_rty identity_type_substitution identity_term_substitution R = R.
Proof. induction R; simpl; rewrite ?instantiate_ty_identity, ?instantiate_qualifier_identity, ?IHR, ?IHR1, ?IHR2; reflexivity. Qed.

Lemma logical_context_empty : forall fuel theta gamma,
  logical_context fuel theta gamma empty_rcontext.
Proof. intros fuel theta gamma x R H; discriminate. Qed.

Lemma lookup_rcontext_update_eq : forall RGamma x R,
  lookup_rcontext x (update_rcontext RGamma x R) = Some R.
Proof. intros; simpl; rewrite Nat.eqb_refl; reflexivity. Qed.

Lemma lookup_rcontext_update_neq : forall RGamma x y R,
  x <> y ->
  lookup_rcontext y (update_rcontext RGamma x R) = lookup_rcontext y RGamma.
Proof.
  intros RGamma x y R Hxy. simpl. destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. exfalso. apply Hxy. symmetry. exact E.
  - reflexivity.
Qed.

Lemma instantiate_update_fresh_tm : forall theta gamma x v t,
  ~ In x (fv_tm t) ->
  instantiate theta (term_subst_update gamma x v) t = instantiate theta gamma t.
Proof.
  intros theta gamma x v t. induction t; intros Hfresh; simpl in *.
  - reflexivity.
  - unfold term_subst_update. destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply Hfresh. simpl; auto.
    + reflexivity.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal.
    + apply IHt1. intro Hin. apply Hfresh. apply in_or_app; left; exact Hin.
    + apply IHt2. intro Hin. apply Hfresh. apply in_or_app; right; exact Hin.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal. apply IHt. exact Hfresh.
  - reflexivity.
  - f_equal.
    + apply IHt1. intro Hin. apply Hfresh. apply in_or_app; left; exact Hin.
    + apply IHt2. intro Hin. apply Hfresh. apply in_or_app; right; exact Hin.
  - f_equal.
    + apply IHt1. intro Hin. apply Hfresh. apply in_or_app; left; exact Hin.
    + apply IHt2. intro Hin. apply Hfresh. apply in_or_app; right; exact Hin.
  - f_equal.
    + apply IHt1. intro Hin. apply Hfresh. apply in_or_app; left; exact Hin.
    + apply IHt2. intro Hin. apply Hfresh. apply in_or_app; right; exact Hin.
Qed.

Lemma instantiate_update_fresh_pred : forall theta gamma x v p,
  ~ In x (fv_pred p) ->
  instantiate_qualifier theta (term_subst_update gamma x v) p =
  instantiate_qualifier theta gamma p.
Proof.
  intros theta gamma x v p. induction p; intros Hfresh; simpl in *; try reflexivity.
  - f_equal; [eapply instantiate_update_fresh_tm|eapply instantiate_update_fresh_tm];
      intro Hin; apply Hfresh; apply in_or_app; [left|right]; exact Hin.
  - f_equal; [eapply instantiate_update_fresh_tm|eapply instantiate_update_fresh_tm];
      intro Hin; apply Hfresh; apply in_or_app; [left|right]; exact Hin.
  - f_equal; [eapply instantiate_update_fresh_tm|eapply instantiate_update_fresh_tm];
      intro Hin; apply Hfresh; apply in_or_app; [left|right]; exact Hin.
  - f_equal; [apply IHp1|apply IHp2]; intro Hin; apply Hfresh; apply in_or_app; [left|right]; exact Hin.
  - f_equal; [apply IHp1|apply IHp2]; intro Hin; apply Hfresh; apply in_or_app; [left|right]; exact Hin.
  - f_equal. apply IHp. exact Hfresh.
Qed.

Lemma instantiate_update_fresh_rty : forall theta gamma x v R,
  ~ In x (fv_rty R) ->
  instantiate_rty theta (term_subst_update gamma x v) R = instantiate_rty theta gamma R.
Proof.
  intros theta gamma x v R. induction R; intros Hfresh; simpl in *.
  - f_equal. eapply instantiate_update_fresh_pred. exact Hfresh.
  - f_equal.
    + apply IHR1. intro Hin. apply Hfresh. apply in_or_app; left; exact Hin.
    + apply IHR2. intro Hin. apply Hfresh. apply in_or_app; right; exact Hin.
  - f_equal.
    + apply IHR1. intro Hin. apply Hfresh. apply in_or_app; left; exact Hin.
    + apply IHR2. intro Hin. apply Hfresh. apply in_or_app; right; exact Hin.
  - f_equal. apply IHR. exact Hfresh.
Qed.

Lemma logical_context_extend : forall fuel theta gamma RGamma x R v,
  logical_context fuel theta gamma RGamma ->
  locally_closed_tm v ->
  logical_value fuel (instantiate_rty theta gamma R) v ->
  ~ In x (fv_rty R) ->
  (forall y S, lookup_rcontext y RGamma = Some S -> ~ In x (fv_rty S)) ->
  logical_context fuel theta (term_subst_update gamma x v)
    (update_rcontext RGamma x R).
Proof.
  intros fuel theta gamma RGamma x R v Hctx Hlc Hval HfreshR HfreshCtx.
  unfold logical_context in *. intros y S Hlookup.
  unfold update_rcontext in Hlookup. simpl in Hlookup.
  destruct (Nat.eqb y x) eqn:Eyx.
  - apply Nat.eqb_eq in Eyx. subst y. inversion Hlookup; subst S.
    rewrite instantiate_update_fresh_rty by exact HfreshR.
    unfold term_subst_update. rewrite Nat.eqb_refl. exact Hval.
  - assert (Exy : Nat.eqb x y = false).
    { apply Nat.eqb_neq. intro Heq. apply Nat.eqb_neq in Eyx. apply Eyx. symmetry. exact Heq. }
    specialize (Hctx y S Hlookup).
    rewrite instantiate_update_fresh_rty by (eapply HfreshCtx; eauto).
    unfold term_subst_update. rewrite Exy. exact Hctx.
Qed.


Lemma logical_expr_progress : forall n R t t',
  logical_expr (S n) R t -> multi t t' ->
  value t' \/ exists u, t' --> u.
Proof.
  intros n R t t' Hrel Hmulti. unfold logical_expr in Hrel; simpl in Hrel.
  specialize (Hrel t' Hmulti). exact (proj1 Hrel).
Qed.

Lemma logical_refine_has_predicate : forall n T p v,
  logical_value n (R_Refine T p) v ->
  value v /\ qualifier_holds (open_qualifier_tm p v).
Proof. intros [|n] T p v H; simpl in H; exact H. Qed.

Lemma logical_expr_refine_preserves : forall n T p t v,
  logical_expr (S n) (R_Refine T p) t ->
  multi t v -> value v ->
  qualifier_holds (open_qualifier_tm p v).
Proof.
  intros n T p t v Hrel Hmulti Hv.
  unfold logical_expr in Hrel; simpl in Hrel.
  specialize (Hrel v Hmulti) as [_ Hval].
  pose proof (Hval Hv) as Hlv.
  exact (proj2 (logical_refine_has_predicate n T p v Hlv)).
Qed.

Lemma logical_integer_nonzero : forall n t m,
  logical_expr (S n)
    (R_Refine Ty_Int (Pred_Ne (tm_bvar 0) (tm_int 0%Z))) t ->
  multi t (tm_int m) -> m <> 0%Z.
Proof.
  intros n t m Hrel Hmulti Heq. subst m.
  pose proof (logical_expr_refine_preserves n Ty_Int
    (Pred_Ne (tm_bvar 0) (tm_int 0%Z)) t (tm_int 0%Z) Hrel Hmulti
    (v_int 0%Z)) as Hholds.
  simpl in Hholds.
  eapply predicate_nonzero; [exact Hholds|]. constructor.
Qed.

Lemma logical_integer_literal : forall n k,
  logical_value k
    (R_Refine Ty_Int (Pred_Eq (tm_bvar 0) (tm_int n))) (tm_int n).
Proof.
  intros n k. destruct k; simpl; split; [constructor| |constructor|];
    unfold qualifier_holds, predicate_holds; simpl;
    exists (tm_int n); repeat split; try constructor.
Qed.

Lemma logical_integer_literal_expr : forall n k,
  logical_expr (S k)
    (R_Refine Ty_Int (Pred_Eq (tm_bvar 0) (tm_int n))) (tm_int n).
Proof.
  intros n k u Hmulti. pose proof (v_int n) as Hv.
  pose proof (value_multi_eq _ _ Hv Hmulti) as Heq. subst u.
  split.
  - left. constructor.
  - intros _. apply logical_integer_literal.
Qed.

Lemma logical_choice : forall n R t1 t2,
  locally_closed_tm t1 -> locally_closed_tm t2 ->
  logical_expr (S n) R t1 -> logical_expr (S n) R t2 ->
  logical_expr (S n) R (tm_choice t1 t2).
Proof.
  intros n R t1 t2 Hlc1 Hlc2 Hrel1 Hrel2 u Hmulti.
  unfold logical_expr in *. simpl in *.
  inversion Hmulti; subst.
  - split. right. exists t1. eapply ST_ChoiceLeft; assumption.
    intros Hval. inversion Hval.
  - inversion H; subst.
    + specialize (Hrel1 u H0). exact Hrel1.
    + specialize (Hrel2 u H0). exact Hrel2.
Qed.


Fixpoint ty_size (T : ty) : nat :=
  match T with
  | Ty_BVar _ | Ty_FVar _ | Ty_Int => 1
  | Ty_Arrow T1 T2 => S (ty_size T1 + ty_size T2)
  | Ty_All T1 => S (ty_size T1)
  end.

Lemma ty_size_open_fvar_rec : forall T k X,
  ty_size (open_ty_rec k (Ty_FVar X) T) = ty_size T.
Proof.
  intros T; induction T; intros k X; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - reflexivity.
  - rewrite IHT1, IHT2. reflexivity.
  - rewrite IHT. reflexivity.
  - reflexivity.
Qed.

Lemma wf_ty_lc_aux : forall n Delta T,
  ty_size T < n -> wf_ty Delta T -> locally_closed_ty T.
Proof.
  induction n as [|n IH]; intros Delta T Hsize Hwf.
  - lia.
  - inversion Hwf; subst; simpl in *.
    + apply lc_ty_fvar.
    + apply lc_ty_arrow.
      * eapply IH; [simpl in Hsize; lia|eassumption].
      * eapply IH; [simpl in Hsize; lia|eassumption].
    + apply lc_ty_all.
      match goal with
      | |- lc_ty_at 1 ?Body =>
        match goal with
        | Hgen : forall Y, _ -> wf_ty (Y :: ?D) (open_ty Body (Ty_FVar Y)) |- _ =>
          let X := fresh "X" in set (X := fresh L);
          pose proof (Hgen X (fresh_notin L)) as Htyped;
          assert (Hs : ty_size (open_ty Body (Ty_FVar X)) < n)
            by (unfold open_ty; rewrite ty_size_open_fvar_rec; simpl in Hsize; lia);
          pose proof (IH (X :: D) (open_ty Body (Ty_FVar X)) Hs Htyped) as Hlc;
          eapply lc_ty_at_open_inv; exact Hlc
        end
      end.
    + apply lc_ty_int.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T H. eapply wf_ty_lc_aux with (n := S (ty_size T)); eauto; lia.
Qed.

Lemma instantiate_ty_lc_at : forall theta K T,
  type_substitution_closed theta -> lc_ty_at K T ->
  lc_ty_at K (instantiate_ty theta T).
Proof.
  intros theta K T Htheta Hlc. induction Hlc; simpl.
  - apply lc_ty_bvar; assumption.
  - eapply lc_ty_at_monotone; [apply Htheta|lia].
  - apply lc_ty_arrow; assumption.
  - apply lc_ty_all. assumption.
  - apply lc_ty_int.
Qed.

Lemma instantiate_lc_tm_at : forall theta gamma K k t,
  type_substitution_closed theta -> term_substitution_closed gamma ->
  lc_tm_at K k t -> lc_tm_at K k (instantiate theta gamma t).
Proof.
  intros theta gamma K k t Htheta Hgamma Hlc. induction Hlc; simpl.
  - apply lc_tm_bvar; assumption.
  - eapply lc_tm_at_monotone; [apply Hgamma|lia|lia].
  - apply lc_tm_abs.
    + eapply instantiate_ty_lc_at; eauto.
    + assumption.
  - apply lc_tm_app; assumption.
  - apply lc_tm_tabs. assumption.
  - apply lc_tm_tapp; [assumption|eapply instantiate_ty_lc_at; eauto].
  - apply lc_tm_int.
  - apply lc_tm_div; assumption.
  - apply lc_tm_arith; assumption.
  - apply lc_tm_choice; assumption.
Qed.

Lemma instantiate_open_tm_rec : forall theta gamma k x t,
  term_substitution_closed gamma ->
  instantiate theta gamma (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k (gamma x) (instantiate theta gamma t).
Proof.
  intros theta gamma k x t Hgamma. revert k. induction t; intros k; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - erewrite open_tm_rec_lc_at; [reflexivity|].
    pose proof (Hgamma a) as Hlc.
    eapply lc_tm_at_monotone with (K := 0) (k := 0) (K' := 0) (k' := k) in Hlc;
      [exact Hlc|lia|lia].
  - f_equal. apply IHt.
  - rewrite IHt1, IHt2; reflexivity.
  - f_equal. apply IHt.
  - rewrite IHt; reflexivity.
  - reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
Qed.

Lemma instantiate_open_tm : forall theta gamma x t,
  term_substitution_closed gamma ->
  instantiate theta gamma (open_tm t (tm_fvar x)) =
  open_tm (instantiate theta gamma t) (gamma x).
Proof. intros; apply instantiate_open_tm_rec; assumption. Qed.

Lemma instantiate_ty_open_fvar_rec : forall theta k X T,
  type_substitution_closed theta ->
  instantiate_ty theta (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k (theta X) (instantiate_ty theta T).
Proof.
  intros theta k X T Hclosed. revert k. induction T; intros k; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - pose proof (Hclosed a) as Ha.
    assert (Hlc : lc_ty_at k (theta a)).
    { eapply lc_ty_at_monotone with (k' := k); [exact Ha|lia]. }
    rewrite (open_ty_rec_lc_at (theta a) k (theta X) Hlc). reflexivity.
  - rewrite IHT1, IHT2; reflexivity.
  - rewrite IHT; reflexivity.
  - reflexivity.
Qed.

Lemma instantiate_tm_open_ty_rec : forall theta gamma k X t,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  instantiate theta gamma (open_tm_ty_rec k (Ty_FVar X) t) =
  open_tm_ty_rec k (theta X) (instantiate theta gamma t).
Proof.
  intros theta gamma k X t Hclosed Hgamma. revert k. induction t; intros k; simpl.
  - reflexivity.
  - symmetry. eapply open_tm_ty_rec_lc_at.
    eapply lc_tm_at_monotone with (K' := k) (k' := 0).
    + apply Hgamma.
    + lia.
    + lia.
  - rewrite instantiate_ty_open_fvar_rec by assumption. rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
  - rewrite IHt; reflexivity.
  - rewrite instantiate_ty_open_fvar_rec by assumption. rewrite IHt; reflexivity.
  - reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
Qed.

Lemma instantiate_tm_open_ty : forall theta gamma X t,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  instantiate theta gamma (open_tm_ty t (Ty_FVar X)) =
  open_tm_ty (instantiate theta gamma t) (theta X).
Proof. intros; apply instantiate_tm_open_ty_rec; assumption. Qed.

Lemma instantiate_pred_open_tm_rec : forall theta gamma k x p,
  term_substitution_closed gamma ->
  instantiate_qualifier theta gamma (open_qualifier_tm_rec k (tm_fvar x) p) =
  open_qualifier_tm_rec k (gamma x) (instantiate_qualifier theta gamma p).
Proof.
  intros theta gamma k x p Hgamma. induction p; simpl;
    try rewrite ?instantiate_open_tm_rec by assumption;
    try rewrite ?IHp, ?IHp1, ?IHp2 by assumption; reflexivity.
Qed.

Lemma instantiate_rty_open_tm_rec : forall theta gamma k x R,
  term_substitution_closed gamma ->
  instantiate_rty theta gamma (open_rty_tm_rec k (tm_fvar x) R) =
  open_rty_tm_rec k (gamma x) (instantiate_rty theta gamma R).
Proof.
  intros theta gamma k x R Hgamma. revert k. induction R; intros k; simpl.
  - rewrite instantiate_pred_open_tm_rec by assumption. reflexivity.
  - rewrite (IHR1 k), (IHR2 (S k)); reflexivity.
  - rewrite (IHR1 k), (IHR2 (S k)); reflexivity.
  - rewrite (IHR k); reflexivity.
Qed.

Lemma instantiate_rty_open_tm : forall theta gamma x R,
  term_substitution_closed gamma ->
  instantiate_rty theta gamma (open_rty_tm R (tm_fvar x)) =
  open_rty_tm (instantiate_rty theta gamma R) (gamma x).
Proof. intros; apply instantiate_rty_open_tm_rec; assumption. Qed.

Lemma instantiate_pred_open_ty_rec : forall theta gamma k X p,
  type_substitution_closed theta -> term_substitution_closed gamma ->
  instantiate_qualifier theta gamma (open_qualifier_ty_rec k (Ty_FVar X) p) =
  open_qualifier_ty_rec k (theta X) (instantiate_qualifier theta gamma p).
Proof.
  intros theta gamma k X p Htheta Hgamma. induction p; simpl;
    try rewrite ?instantiate_tm_open_ty_rec by assumption;
    try rewrite ?IHp, ?IHp1, ?IHp2 by assumption; reflexivity.
Qed.

Lemma instantiate_rty_open_ty_rec : forall theta gamma k X R,
  type_substitution_closed theta -> term_substitution_closed gamma ->
  instantiate_rty theta gamma (open_rty_ty_rec k (Ty_FVar X) R) =
  open_rty_ty_rec k (theta X) (instantiate_rty theta gamma R).
Proof.
  intros theta gamma k X R Htheta Hgamma. revert k. induction R; intros k; simpl.
  - rewrite instantiate_ty_open_fvar_rec by assumption.
    rewrite instantiate_pred_open_ty_rec by assumption. reflexivity.
  - rewrite (IHR1 k), (IHR2 k); reflexivity.
  - rewrite (IHR1 k), (IHR2 k); reflexivity.
  - rewrite (IHR (S k)); reflexivity.
Qed.

Lemma instantiate_rty_open_ty : forall theta gamma X R,
  type_substitution_closed theta -> term_substitution_closed gamma ->
  instantiate_rty theta gamma (open_rty_ty R (Ty_FVar X)) =
  open_rty_ty (instantiate_rty theta gamma R) (theta X).
Proof. intros; apply instantiate_rty_open_ty_rec; assumption. Qed.

Fixpoint tm_size (t : tm) : nat :=
  match t with
  | tm_bvar _ | tm_fvar _ | tm_int _ => 1
  | tm_abs _ t1 | tm_tabs t1 => S (tm_size t1)
  | tm_app t1 t2 | tm_div t1 t2 | tm_choice t1 t2 => S (tm_size t1 + tm_size t2)
  | tm_tapp t1 _ => S (tm_size t1)
  | tm_arith _ t1 t2 => S (tm_size t1 + tm_size t2)
  end.

Lemma tm_size_open_fvar_rec : forall t k x,
  tm_size (open_tm_rec k (tm_fvar x) t) = tm_size t.
Proof.
  intros t; induction t; intros k x; simpl; rewrite ?IHt, ?IHt1, ?IHt2;
    try reflexivity; destruct (Nat.eqb k n); reflexivity.
Qed.

Lemma tm_size_open_ty_rec : forall t k U,
  tm_size (open_tm_ty_rec k U t) = tm_size t.
Proof.
  intros t; induction t; intros k U; simpl; rewrite ?IHt, ?IHt1, ?IHt2;
    try reflexivity.
Qed.

Lemma has_type_lc_aux : forall n Delta Gamma t T,
  tm_size t < n -> has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  induction n as [|n IH]; intros Delta Gamma t T Hsize Hty.
  - lia.
  - inversion Hty; subst; simpl in *.
    + apply lc_tm_fvar.
    + apply lc_tm_abs.
      * eapply wf_ty_lc; eassumption.
      * pose proof (H0 (fresh L) (fresh_notin L)) as Hbody.
        assert (Hs : tm_size (open_tm t2 (tm_fvar (fresh L))) < n).
        { unfold open_tm. rewrite tm_size_open_fvar_rec. simpl in Hsize. lia. }
        pose proof (IH Delta (update Gamma (fresh L) T1)
          (open_tm t2 (tm_fvar (fresh L))) T2 Hs Hbody) as Hlc.
        eapply lc_tm_at_open_tm_inv. exact Hlc.
    + apply lc_tm_app.
      * eapply IH; [simpl in Hsize; lia|eassumption].
      * eapply IH; [simpl in Hsize; lia|eassumption].
    + apply lc_tm_tabs.
      pose proof (H (fresh L) (fresh_notin L)) as Hbody.
      assert (Hs : tm_size (open_tm_ty t0 (Ty_FVar (fresh L))) < n).
      { unfold open_tm_ty. rewrite tm_size_open_ty_rec. simpl in Hsize. lia. }
      pose proof (IH (fresh L :: Delta) Gamma
        (open_tm_ty t0 (Ty_FVar (fresh L))) (open_ty T0 (Ty_FVar (fresh L))) Hs Hbody) as Hlc.
      eapply lc_tm_at_open_ty_inv. exact Hlc.
    + apply lc_tm_tapp.
      * eapply IH; [simpl in Hsize; lia|eassumption].
      * eapply wf_ty_lc; eassumption.
    + apply lc_tm_int.
    + apply lc_tm_div.
      * eapply IH; [simpl in Hsize; lia|eassumption].
      * eapply IH; [simpl in Hsize; lia|eassumption].
    + apply lc_tm_arith.
      * eapply IH; [simpl in Hsize; lia|eassumption].
      * eapply IH; [simpl in Hsize; lia|eassumption].
    + apply lc_tm_choice.
      * eapply IH; [simpl in Hsize; lia|eassumption].
      * eapply IH; [simpl in Hsize; lia|eassumption].
Qed.

Lemma has_type_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros. eapply has_type_lc_aux with (n := S (tm_size t)); eauto; lia.
Qed.

Lemma has_rtype_lc : forall Delta RGamma t R,
  has_rtype Delta RGamma t R -> locally_closed_tm t.
Proof.
  intros Delta RGamma t R H.
  exact (has_type_lc Delta (erase_context RGamma) t (erase R)
    (has_rtype_erases Delta RGamma t R H)).
Qed.

Lemma entails_sound : forall Delta RGamma ps qs,
  entails Delta RGamma ps qs -> forall fuel theta gamma,
  term_substitution_closed gamma -> logical_context fuel theta gamma RGamma ->
  qualifier_holds (instantiate_qualifier theta gamma ps) ->
  qualifier_holds (instantiate_qualifier theta gamma qs).
Proof.
  intros Delta RGamma ps qs Hent. induction Hent;
    intros fuel theta gamma Hgamma Hctx Hholds;
    unfold qualifier_holds, predicate_holds in *; simpl in *.
  - exact Hholds.
  - exact I.
  - apply (IHHent2 fuel theta gamma Hgamma Hctx).
    apply (IHHent1 fuel theta gamma Hgamma Hctx Hholds).
  - destruct Hholds as [Hp Hq]. exact Hp.
  - destruct Hholds as [Hp Hq]. exact Hq.
  - split.
    + eapply IHHent1; eauto.
    + eapply IHHent2; eauto.
  - left. exact Hholds.
  - right. exact Hholds.
  - destruct Hholds as [Hp|Hq].
    + eapply IHHent1; eauto.
    + eapply IHHent2; eauto.
  - intros Hq. apply (IHHent fuel theta gamma Hgamma Hctx).
    split; assumption.
  - destruct Hholds as [Hp Hnot]. contradiction.
  - pose proof (Hctx x (R_Refine T p) H) as Hrel.
    destruct fuel; simpl in Hrel; destruct Hrel as [_ Hrel].
    all: change (interpret_qualifier operational_atoms
      (instantiate_qualifier theta gamma
        (open_qualifier_tm_rec 0 (tm_fvar x) p))).
    all: pose proof (instantiate_pred_open_tm_rec theta gamma 0 x p Hgamma) as Heq.
    all: unfold qualifier_holds, predicate_holds, open_qualifier_tm in Hrel.
    all: change (interpret_qualifier operational_atoms
      (open_qualifier_tm_rec 0 (gamma x) (instantiate_qualifier theta gamma p))) in Hrel.
    all: rewrite <- Heq in Hrel.
    all: exact Hrel.
  - contradiction.
Qed.

Lemma core_progress_or_stuck : forall t T,
  has_type [] empty t T ->
  value t \/ (exists t', t --> t') \/
  (~ value t /\ forall t', ~ t --> t').
Proof.
  intros t T Hty. remember [] as Delta. remember empty as Gamma.
  induction Hty; subst; simpl in *.
  - discriminate.
  - left. apply v_abs. apply lc_tm_abs.
    + eapply wf_ty_lc; eassumption.
    + pose proof (H0 (fresh L) (fresh_notin L)) as Hb.
      pose proof (has_type_lc _ _ _ _ Hb) as Hlc.
      eapply lc_tm_at_open_tm_inv. exact Hlc.
  - specialize (IHHty1 eq_refl eq_refl). specialize (IHHty2 eq_refl eq_refl).
    destruct IHHty1 as [Hv1|[Hs1|[Hnv1 Hns1]]].
    + destruct IHHty2 as [Hv2|[Hs2|[Hnv2 Hns2]]].
      * inversion Hv1; subst; try solve [inversion Hty1].
        right; left. eexists. eapply ST_AppAbs; eauto.
      * right; left. destruct Hs2 as [u Hu]. exists (tm_app t1 u). apply ST_App2; assumption.
      * right; right. split.
        -- intro Hv. inversion Hv.
        -- intros u Hstep. inversion Hstep; subst; try contradiction.
           all: try solve [eapply value_no_step; eauto].
           all: eapply Hns2; eauto.
    + right; left. destruct Hs1 as [u Hu]. exists (tm_app u t2). apply ST_App1; [assumption|eapply has_type_lc; eauto].
    + right; right. split.
      * intro Hv. inversion Hv; subst; contradiction.
      * intros u Hstep. inversion Hstep; subst; eauto using v_abs.
        all: eapply Hns1; eassumption.
  - left. apply v_tabs. apply lc_tm_tabs.
    pose proof (H (fresh L) (fresh_notin L)) as Hb.
    pose proof (has_type_lc _ _ _ _ Hb) as Hlc.
    eapply lc_tm_at_open_ty_inv. exact Hlc.
  - specialize (IHHty eq_refl eq_refl). destruct IHHty as [Hv|[Hs|[Hnv Hns]]].
    + inversion Hv; subst; try solve [inversion Hty].
      right; left. eexists. eapply ST_TAppTabs.
      * eapply value_regular. exact Hv.
      * eapply wf_ty_lc. exact H.
    + right; left. destruct Hs as [u Hu]. exists (tm_tapp u U). apply ST_TApp; [exact Hu|eapply wf_ty_lc; eassumption].
    + right; right. split.
      * intro Hv. inversion Hv; subst; contradiction.
      * intros u Hstep. inversion Hstep; subst; try contradiction; eauto using v_tabs.
        all: eapply Hns; eassumption.
  - left. constructor.
  - specialize (IHHty1 eq_refl eq_refl). specialize (IHHty2 eq_refl eq_refl).
    destruct IHHty1 as [Hv1|[Hs1|[Hnv1 Hns1]]].
    + destruct IHHty2 as [Hv2|[Hs2|[Hnv2 Hns2]]].
      * inversion Hv1; subst; try solve [inversion Hty1].
        inversion Hv2; subst; try solve [inversion Hty2].
        destruct (Z.eq_dec n0 0%Z) as [Hz|Hz].
        -- right; right. split.
           ++ intro Hval; inversion Hval.
           ++ intros u Hstep. inversion Hstep; subst; try lia.
              all: exfalso; eapply value_no_step; [constructor|eassumption].
        -- right; left. exists (tm_int (Z.div n n0)). eapply ST_DivInt; eauto.
      * right; left. destruct Hs2 as [u Hu]. exists (tm_div t1 u). apply ST_Div2; assumption.
      * right; right. split.
        -- intro Hval; inversion Hval.
        -- intros u Hstep. inversion Hstep; subst; try contradiction; eauto using v_int.
           all: try solve [exfalso; eapply value_no_step; eauto].
           all: eapply Hns2; eassumption.
    + right; left. destruct Hs1 as [u Hu]. exists (tm_div u t2). apply ST_Div1; [assumption|eapply has_type_lc; eauto].
    + right; right. split.
      * intro Hval; inversion Hval.
      * intros u Hstep. inversion Hstep; subst; try contradiction; eauto using v_int.
        all: try solve [exfalso; apply Hnv1; constructor].
        all: eapply Hns1; eassumption.
  - specialize (IHHty1 eq_refl eq_refl). specialize (IHHty2 eq_refl eq_refl).
    destruct IHHty1 as [Hv1|[Hs1|[Hnv1 Hns1]]].
    + destruct IHHty2 as [Hv2|[Hs2|[Hnv2 Hns2]]].
      * inversion Hv1; subst; try solve [inversion Hty1].
        inversion Hv2; subst; try solve [inversion Hty2].
        right; left. exists (tm_int (eval_integer_operator op n n0)). constructor.
      * right; left. destruct Hs2 as [u Hu]. exists (tm_arith op t1 u). apply ST_Arith2; assumption.
      * right; right. split.
        -- intro Hval; inversion Hval.
        -- intros u Hstep. inversion Hstep; subst; try contradiction; eauto using v_int.
           all: try solve [exfalso; eapply value_no_step; eauto].
           all: eapply Hns2; eassumption.
    + right; left. destruct Hs1 as [u Hu]. exists (tm_arith op u t2). apply ST_Arith1; [assumption|eapply has_type_lc; eauto].
    + right; right. split.
      * intro Hval; inversion Hval.
      * intros u Hstep. inversion Hstep; subst; try contradiction; eauto using v_int.
        all: try solve [exfalso; apply Hnv1; constructor].
        all: eapply Hns1; eassumption.
  - right; left. exists t1. eapply ST_ChoiceLeft; eapply has_type_lc; eauto.
Qed.

Lemma value_int_typed_inv : forall v,
  value v -> has_type [] empty v Ty_Int -> exists n, v = tm_int n.
Proof.
  intros v Hv Hty. inversion Hv; subst.
  - inversion Hty.
  - inversion Hty.
  - eexists. reflexivity.
Qed.

Lemma logical_division_immediate_progress : forall n t1 t2,
  has_type [] empty t1 Ty_Int -> has_type [] empty t2 Ty_Int ->
  logical_expr (S n) (R_Refine Ty_Int Pred_True) t1 ->
  logical_expr (S n)
    (R_Refine Ty_Int (Pred_Ne (tm_bvar 0) (tm_int 0%Z))) t2 ->
  exists u, tm_div t1 t2 --> u.
Proof.
  intros n t1 t2 Hty1 Hty2 Hrel1 Hrel2.
  pose proof Hrel2 as Hsafe2.
  unfold logical_expr in Hrel1, Hrel2; simpl in Hrel1, Hrel2.
  specialize (Hrel1 t1 (multi_refl t1)) as [Hp1 _].
  specialize (Hrel2 t2 (multi_refl t2)) as [Hp2 _].
  destruct Hp1 as [Hv1|[t1' Hs1]].
  - destruct Hp2 as [Hv2|[t2' Hs2]].
    + destruct (value_int_typed_inv t1 Hv1 Hty1) as [m1 ->].
      destruct (value_int_typed_inv t2 Hv2 Hty2) as [m2 ->].
      assert (Hm2 : m2 <> 0%Z).
      { eapply logical_integer_nonzero with (n := n) (t := tm_int m2).
        - exact Hsafe2.
        - constructor. }
      exists (tm_int (Z.div m1 m2)). apply ST_DivInt. exact Hm2.
    + exists (tm_div t1 t2'). apply ST_Div2; assumption.
  - exists (tm_div t1' t2). apply ST_Div1; [assumption|eapply has_type_lc; eauto].
Qed.

Theorem never_stuck : forall (t t' : tm) (R : rty),
  has_rtype [] empty_rcontext t R ->
  multi t t' ->
  value t' \/ exists t'' : tm, t' --> t''.
Proof.
  (* Complete this proof. *)
Qed.

End SystemFRefinementNonDeterminismTask.
