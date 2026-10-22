From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
From Stdlib Require Import ZArith.BinInt.

Module SystemFRefinement.

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
  | tm_arith : integer_operator -> tm -> tm -> tm.

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
      lc_tm_at K k (tm_arith op t1 t2).

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
      has_type Delta Gamma (tm_arith op t1 t2) Ty_Int.

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

End SystemFRefinement.

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
Module SystemFRefinementInfrastructure.
Import ListNotations.
Import SystemFRefinement.

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
Qed.

Lemma wf_ty_lc : forall Delta T,
  wf_ty Delta T ->
  locally_closed_ty T.
Proof.
  intros Delta T Hwf. induction Hwf.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; assumption.
  - unfold locally_closed_ty in *.
    apply lc_ty_all.
    set (X := fresh L).
    apply (lc_ty_at_open_inv T 0 X).
    apply H0. subst X. apply fresh_notin.
  - apply lc_ty_int.
Qed.

Lemma typing_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  locally_closed_tm t.
Proof.
  intros Delta Gamma t T Hty. induction Hty.
  - apply lc_tm_fvar.
  - unfold locally_closed_tm in *.
    apply lc_tm_abs.
    + apply wf_ty_lc with Delta. assumption.
    + set (x := fresh L).
      apply (lc_tm_at_open_tm_inv t2 0 0 x).
      apply H1. subst x. apply fresh_notin.
  - apply lc_tm_app; assumption.
  - unfold locally_closed_tm in *.
    apply lc_tm_tabs.
    set (X := fresh L).
    apply (lc_tm_at_open_ty_inv t 0 0 X).
    apply H0. subst X. apply fresh_notin.
  - apply lc_tm_tapp.
    + assumption.
    + apply wf_ty_lc with Delta. assumption.
  - apply lc_tm_int.
  - apply lc_tm_div; assumption.
  - apply lc_tm_arith; assumption.
Qed.

Lemma typing_type_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  locally_closed_ty T.
Proof.
  intros Delta Gamma t T Hty. induction Hty.
  - apply wf_ty_lc with Delta. assumption.
  - apply lc_ty_arrow.
    + apply wf_ty_lc with Delta. assumption.
    + set (x := fresh L). apply H1 with x.
      subst x. apply fresh_notin.
  - inversion IHHty1; assumption.
  - unfold locally_closed_ty in *.
    apply lc_ty_all.
    set (X := fresh L).
    apply (lc_ty_at_open_inv T 0 X).
    apply H0. subst X. apply fresh_notin.
  - unfold locally_closed_ty in *.
    inversion IHHty; subst.
    apply lc_ty_at_open.
    + assumption.
    + apply wf_ty_lc with Delta. assumption.
  - apply lc_ty_int.
  - apply lc_ty_int.
  - apply lc_ty_int.
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
  end.

Definition type_substitution_closed (theta : type_substitution) : Prop :=
  forall X : atom, locally_closed_ty (theta X).

Definition term_substitution_closed (gamma : term_substitution) : Prop :=
  forall x : atom, locally_closed_tm (gamma x).

Lemma instantiate_ty_lc_at : forall T k theta,
  lc_ty_at k T ->
  type_substitution_closed theta ->
  lc_ty_at k (instantiate_ty theta T).
Proof.
  intros T k theta Hlc. induction Hlc; intros Htheta; simpl.
  - apply lc_ty_bvar. assumption.
  - eapply lc_ty_at_monotone.
    + apply Htheta.
    + lia.
  - apply lc_ty_arrow; auto.
  - apply lc_ty_all. auto.
  - apply lc_ty_int.
Qed.

Lemma instantiate_lc_at : forall t K k theta gamma,
  lc_tm_at K k t ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  lc_tm_at K k (instantiate theta gamma t).
Proof.
  intros t K k theta gamma Hlc. induction Hlc; intros Htheta Hgamma; simpl.
  - apply lc_tm_bvar. assumption.
  - eapply lc_tm_at_monotone.
    + apply Hgamma.
    + lia.
    + lia.
  - apply lc_tm_abs.
    + apply instantiate_ty_lc_at; assumption.
    + auto.
  - apply lc_tm_app; auto.
  - apply lc_tm_tabs. auto.
  - apply lc_tm_tapp.
    + auto.
    + apply instantiate_ty_lc_at; assumption.
  - apply lc_tm_int.
  - apply lc_tm_div; auto.
  - apply lc_tm_arith; auto.
Qed.

Lemma instantiate_ty_closed : forall theta T,
  locally_closed_ty T ->
  type_substitution_closed theta ->
  locally_closed_ty (instantiate_ty theta T).
Proof.
  intros. apply instantiate_ty_lc_at; assumption.
Qed.

Lemma instantiate_closed : forall theta gamma t,
  locally_closed_tm t ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm (instantiate theta gamma t).
Proof.
  intros. apply instantiate_lc_at; assumption.
Qed.

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

Lemma instantiate_open_tm_rec : forall t k theta gamma x u,
  ~ In x (fv_tm t) ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  instantiate theta (term_subst_update gamma x u)
    (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k u (instantiate theta gamma t).
Proof.
  induction t; intros k theta gamma x u Hfresh Htheta Hgamma Hu; simpl in *.
  - destruct (Nat.eqb k n); simpl.
    + unfold term_subst_update. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - assert (x <> a) by (intro; subst; apply Hfresh; auto).
    unfold term_subst_update.
    assert (E : Nat.eqb x a = false) by (apply Nat.eqb_neq; assumption).
    rewrite E.
    symmetry. apply open_tm_rec_lc_at with (K := 0).
    eapply lc_tm_at_monotone.
    + apply Hgamma.
    + lia.
    + lia.
  - rewrite (IHt (S k) theta gamma x u Hfresh Htheta Hgamma Hu).
    reflexivity.
  - rewrite in_app_iff in Hfresh.
    assert (H1 : ~ In x (fv_tm t1)) by intuition.
    assert (H2 : ~ In x (fv_tm t2)) by intuition.
    rewrite (IHt1 k theta gamma x u H1 Htheta Hgamma Hu).
    rewrite (IHt2 k theta gamma x u H2 Htheta Hgamma Hu).
    reflexivity.
  - rewrite (IHt k theta gamma x u Hfresh Htheta Hgamma Hu).
    reflexivity.
  - rewrite (IHt k theta gamma x u Hfresh Htheta Hgamma Hu).
    reflexivity.
  - reflexivity.
  - rewrite in_app_iff in Hfresh.
    rewrite IHt1, IHt2; intuition.
  - rewrite in_app_iff in Hfresh.
    rewrite IHt1, IHt2; intuition.
Qed.

Lemma instantiate_open_tm : forall t theta gamma x u,
  ~ In x (fv_tm t) ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  instantiate theta (term_subst_update gamma x u)
    (open_tm t (tm_fvar x)) =
  open_tm (instantiate theta gamma t) u.
Proof.
  intros. unfold open_tm.
  apply instantiate_open_tm_rec; assumption.
Qed.

Lemma instantiate_ty_open_rec : forall T k theta X U,
  ~ In X (fv_ty T) ->
  type_substitution_closed theta ->
  locally_closed_ty U ->
  instantiate_ty (type_subst_update theta X U)
    (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k U (instantiate_ty theta T).
Proof.
  induction T; intros k theta X U Hfresh Htheta HU; simpl in *.
  - destruct (Nat.eqb k n); simpl.
    + unfold type_subst_update. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - assert (X <> a) by (intro; subst; apply Hfresh; auto).
    unfold type_subst_update.
    assert (E : Nat.eqb X a = false) by (apply Nat.eqb_neq; assumption).
    rewrite E.
    symmetry. apply open_ty_rec_lc_at.
    eapply lc_ty_at_monotone.
    + apply Htheta.
    + lia.
  - rewrite in_app_iff in Hfresh.
    assert (H1 : ~ In X (fv_ty T1)) by intuition.
    assert (H2 : ~ In X (fv_ty T2)) by intuition.
    rewrite (IHT1 k theta X U H1 Htheta HU).
    rewrite (IHT2 k theta X U H2 Htheta HU).
    reflexivity.
  - rewrite (IHT (S k) theta X U Hfresh Htheta HU). reflexivity.
  - reflexivity.
Qed.

Lemma instantiate_ty_open : forall T theta X U,
  ~ In X (fv_ty T) ->
  type_substitution_closed theta ->
  locally_closed_ty U ->
  instantiate_ty (type_subst_update theta X U)
    (open_ty T (Ty_FVar X)) =
  open_ty (instantiate_ty theta T) U.
Proof.
  intros. unfold open_ty.
  apply instantiate_ty_open_rec; assumption.
Qed.

Lemma instantiate_open_ty_rec : forall t K theta gamma X U,
  ~ In X (ftv_tm t) ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_ty U ->
  instantiate (type_subst_update theta X U) gamma
    (open_tm_ty_rec K (Ty_FVar X) t) =
  open_tm_ty_rec K U (instantiate theta gamma t).
Proof.
  induction t as
      [i | x | T body IHbody | t1 IH1 t2 IH2 | body IHbody | body IHbody T
      | n | t1 IH1 t2 IH2 | op t1 IH1 t2 IH2];
    intros K theta gamma X U Hfresh Htheta Hgamma HU; simpl in *.
  - reflexivity.
  - symmetry. apply open_tm_ty_rec_lc_at with (k := 0).
    eapply lc_tm_at_monotone.
    + apply Hgamma.
    + lia.
    + lia.
  - rewrite in_app_iff in Hfresh.
    assert (HT : ~ In X (fv_ty T)) by intuition.
    assert (Hbody : ~ In X (ftv_tm body)) by intuition.
    rewrite (instantiate_ty_open_rec T K theta X U HT Htheta HU).
    rewrite (IHbody K theta gamma X U Hbody Htheta Hgamma HU).
    reflexivity.
  - rewrite in_app_iff in Hfresh.
    assert (H1 : ~ In X (ftv_tm t1)) by intuition.
    assert (H2 : ~ In X (ftv_tm t2)) by intuition.
    rewrite (IH1 K theta gamma X U H1 Htheta Hgamma HU).
    rewrite (IH2 K theta gamma X U H2 Htheta Hgamma HU).
    reflexivity.
  - rewrite (IHbody (S K) theta gamma X U Hfresh Htheta Hgamma HU).
    reflexivity.
  - rewrite in_app_iff in Hfresh.
    assert (Hbody : ~ In X (ftv_tm body)) by intuition.
    assert (HT : ~ In X (fv_ty T)) by intuition.
    rewrite (IHbody K theta gamma X U Hbody Htheta Hgamma HU).
    rewrite (instantiate_ty_open_rec T K theta X U HT Htheta HU).
    reflexivity.
  - reflexivity.
  - rewrite in_app_iff in Hfresh.
    rewrite IH1, IH2; intuition.
  - rewrite in_app_iff in Hfresh.
    rewrite IH1, IH2; intuition.
Qed.

Lemma instantiate_open_ty : forall t theta gamma X U,
  ~ In X (ftv_tm t) ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_ty U ->
  instantiate (type_subst_update theta X U) gamma
    (open_tm_ty t (Ty_FVar X)) =
  open_tm_ty (instantiate theta gamma t) U.
Proof.
  intros. unfold open_tm_ty.
  apply instantiate_open_ty_rec; assumption.
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

Lemma instantiate_ty_identity : forall T,
  instantiate_ty identity_type_substitution T = T.
Proof.
  induction T; simpl; try rewrite ?IHT1, ?IHT2, ?IHT; reflexivity.
Qed.

Lemma instantiate_identity : forall t,
  instantiate identity_type_substitution identity_term_substitution t = t.
Proof.
  induction t; simpl; try rewrite ?IHt1, ?IHt2, ?IHt;
    try rewrite instantiate_ty_identity; reflexivity.
Qed.

End SystemFRefinementInfrastructure.

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
Module SystemFRefinementCoreTyping.
Import ListNotations.
Import SystemFRefinement.
Import SystemFRefinementInfrastructure.

Definition ty_context_included (Delta Delta' : ty_context) : Prop :=
  forall X, In X Delta -> In X Delta'.

Definition context_included (Gamma Gamma' : context) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    lookup_context x Gamma' = Some T.

Lemma wf_ty_weaken : forall Delta T,
  wf_ty Delta T ->
  forall Delta', ty_context_included Delta Delta' -> wf_ty Delta' T.
Proof.
  intros Delta T Hwf. induction Hwf; intros Delta' Hinc.
  - apply WF_Var. apply Hinc. assumption.
  - apply WF_Arrow; auto.
  - apply WF_All with L. intros X Hfresh.
    apply H0. exact Hfresh.
    unfold ty_context_included in *. simpl. intros Y [E | Hin].
    + left. exact E.
    + right. apply Hinc. exact Hin.
  - apply WF_Int.
Qed.

Lemma has_type_weaken_context : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall Gamma', context_included Gamma Gamma' ->
  has_type Delta Gamma' t T.
Proof.
  intros Delta Gamma t T Hty. induction Hty; intros Gamma' Hinc.
  - apply T_Var; [apply Hinc; assumption | assumption].
  - apply T_Abs with L; [assumption |]. intros x Hfresh.
    apply H1. exact Hfresh.
    unfold context_included in *. intros y U Hlookup.
    unfold update in *. simpl in *.
    destruct (Nat.eqb y x); [exact Hlookup |].
    apply Hinc. exact Hlookup.
  - apply T_App with T1; auto.
  - apply T_TAbs with L. intros X Hfresh. apply H0; assumption.
  - eapply T_TApp; eauto.
  - apply T_Int.
  - apply T_Div; auto.
  - apply T_Arith; auto.
Qed.

Lemma has_type_weaken_type : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall Delta', ty_context_included Delta Delta' ->
  has_type Delta' Gamma t T.
Proof.
  intros Delta Gamma t T Hty. induction Hty; intros Delta' Hinc.
  - apply T_Var; [assumption | eapply wf_ty_weaken; eauto].
  - apply T_Abs with L.
    + eapply wf_ty_weaken; eauto.
    + intros x Hfresh. apply H1; assumption.
  - apply T_App with T1; auto.
  - apply T_TAbs with L. intros X Hfresh.
    apply H0. exact Hfresh.
    unfold ty_context_included in *. simpl. intros Y [E | Hin].
    + left. exact E.
    + right. apply Hinc. exact Hin.
  - eapply T_TApp; eauto. eapply wf_ty_weaken; eauto.
  - apply T_Int.
  - apply T_Div; auto.
  - apply T_Arith; auto.
Qed.

Definition type_substitution_wf
    (Delta Delta' : ty_context) (theta : type_substitution) : Prop :=
  forall X, In X Delta -> wf_ty Delta' (theta X).

Lemma fv_ty_open_rec_preserves : forall T k U X,
  In X (fv_ty T) -> In X (fv_ty (open_ty_rec k U T)).
Proof.
  induction T; intros k U X Hin; simpl in *.
  - contradiction.
  - exact Hin.
  - apply in_app_iff in Hin. apply in_app_iff.
    destruct Hin as [Hin | Hin].
    + left. apply IHT1. exact Hin.
    + right. apply IHT2. exact Hin.
  - apply IHT. exact Hin.
  - contradiction.
Qed.

Lemma wf_ty_fv : forall Delta T,
  wf_ty Delta T -> forall X, In X (fv_ty T) -> In X Delta.
Proof.
  intros Delta T Hwf. induction Hwf; intros Y Hin; simpl in *.
  - destruct Hin as [E | Hin].
    + subst. assumption.
    + contradiction.
  - apply in_app_iff in Hin. destruct Hin; auto.
  - set (X := fresh (L ++ fv_ty T)).
    assert (HX : ~ In X (L ++ fv_ty T)).
    { subst X. apply fresh_notin. }
    rewrite in_app_iff in HX.
    assert (HXL : ~ In X L) by intuition.
    assert (HXfv : ~ In X (fv_ty T)) by intuition.
    pose proof (H0 X HXL Y) as IH.
    assert (Hopen : In Y (fv_ty (open_ty T (Ty_FVar X)))).
    { unfold open_ty. apply fv_ty_open_rec_preserves. exact Hin. }
    specialize (IH Hopen). simpl in IH.
    destruct IH as [E | HinDelta].
    + subst Y. contradiction.
    + exact HinDelta.
  - contradiction.
Qed.

Lemma instantiate_ty_open_rec_local : forall T k theta X U,
  ~ In X (fv_ty T) ->
  (forall Y, In Y (fv_ty T) -> locally_closed_ty (theta Y)) ->
  locally_closed_ty U ->
  instantiate_ty (type_subst_update theta X U)
    (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k U (instantiate_ty theta T).
Proof.
  induction T; intros k theta X U Hfresh Htheta HU; simpl in *.
  - destruct (Nat.eqb k n); simpl.
    + unfold type_subst_update. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - assert (X <> a) by (intro; subst; apply Hfresh; auto).
    unfold type_subst_update.
    rewrite (proj2 (Nat.eqb_neq X a)) by assumption.
    symmetry. apply open_ty_rec_lc_at.
    eapply lc_ty_at_monotone.
    + apply Htheta. auto.
    + lia.
  - rewrite in_app_iff in Hfresh.
    assert (Hfresh1 : ~ In X (fv_ty T1)) by intuition.
    assert (Hfresh2 : ~ In X (fv_ty T2)) by intuition.
    rewrite (IHT1 k theta X U Hfresh1),
      (IHT2 k theta X U Hfresh2); try assumption.
    + reflexivity.
    + intros Y Hin. apply Htheta. apply in_app_iff. auto.
    + intros Y Hin. apply Htheta. apply in_app_iff. auto.
  - rewrite IHT; try assumption. reflexivity.
  - reflexivity.
Qed.

Lemma instantiate_ty_open_local : forall T theta X U,
  ~ In X (fv_ty T) ->
  (forall Y, In Y (fv_ty T) -> locally_closed_ty (theta Y)) ->
  locally_closed_ty U ->
  instantiate_ty (type_subst_update theta X U)
    (open_ty T (Ty_FVar X)) =
  open_ty (instantiate_ty theta T) U.
Proof.
  intros. unfold open_ty. apply instantiate_ty_open_rec_local; assumption.
Qed.

Lemma wf_ty_instantiate : forall Delta T,
  wf_ty Delta T ->
  forall Delta' theta,
    type_substitution_wf Delta Delta' theta ->
    wf_ty Delta' (instantiate_ty theta T).
Proof.
  intros Delta T Hwf. induction Hwf; intros Delta' theta Htheta; simpl.
  - apply Htheta. assumption.
  - apply WF_Arrow; auto.
  - apply WF_All with (L ++ Delta ++ Delta' ++ fv_ty T).
    intros X Hfresh.
    repeat rewrite in_app_iff in Hfresh.
    assert (HXL : ~ In X L) by intuition.
    assert (HXDelta : ~ In X Delta) by intuition.
    assert (HXDelta' : ~ In X Delta') by intuition.
    assert (HXT : ~ In X (fv_ty T)) by intuition.
    pose proof (H0 X HXL (X :: Delta')
      (type_subst_update theta X (Ty_FVar X))) as IH.
    assert (Hsub : type_substitution_wf (X :: Delta) (X :: Delta')
      (type_subst_update theta X (Ty_FVar X))).
    { unfold type_substitution_wf in *. intros Y [E | Hin].
      - subst Y. unfold type_subst_update. rewrite Nat.eqb_refl.
        apply WF_Var. simpl. auto.
      - assert (Hneq : X <> Y).
        { intro E. subst. contradiction. }
        unfold type_subst_update.
        rewrite (proj2 (Nat.eqb_neq X Y)) by assumption.
        eapply wf_ty_weaken.
        + apply Htheta. exact Hin.
        + unfold ty_context_included. simpl. auto. }
    assert (Hopen :
      instantiate_ty (type_subst_update theta X (Ty_FVar X))
        (open_ty T (Ty_FVar X)) =
      open_ty (instantiate_ty theta T) (Ty_FVar X)).
    { apply instantiate_ty_open_local.
      - exact HXT.
      - intros Y Hin. apply wf_ty_lc with Delta'. apply Htheta.
        assert (Hwhole : wf_ty Delta (Ty_All T)).
        { apply WF_All with L. exact H. }
        eapply wf_ty_fv; [exact Hwhole |]. simpl. exact Hin.
      - apply lc_ty_fvar. }
    rewrite <- Hopen. exact (IH Hsub).
  - apply WF_Int.
Qed.

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

Lemma context_included_update_fresh : forall Gamma x T,
  ~ In x (dom_context Gamma) ->
  context_included Gamma (update Gamma x T).
Proof.
  intros Gamma x T Hfresh y U Hlookup. unfold update. simpl.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst y.
    rewrite notin_dom_lookup_none in Hlookup by assumption. discriminate.
  - exact Hlookup.
Qed.

Lemma context_wf_update : forall Delta Gamma x T,
  context_wf Delta Gamma -> wf_ty Delta T ->
  context_wf Delta (update Gamma x T).
Proof.
  intros Delta Gamma x T Hctx HT y U Hlookup.
  unfold update in Hlookup. simpl in Hlookup.
  destruct (Nat.eqb y x) eqn:E.
  - inversion Hlookup; subst. exact HT.
  - apply Hctx with y. exact Hlookup.
Qed.

Lemma context_wf_weaken_type : forall Delta Gamma,
  context_wf Delta Gamma ->
  forall Delta', ty_context_included Delta Delta' ->
  context_wf Delta' Gamma.
Proof.
  intros Delta Gamma Hctx Delta' Hinc x T Hlookup.
  eapply wf_ty_weaken; [eapply Hctx; eauto | exact Hinc].
Qed.

Lemma instantiate_ty_update_irrelevant : forall T theta X U,
  ~ In X (fv_ty T) ->
  instantiate_ty (type_subst_update theta X U) T = instantiate_ty theta T.
Proof.
  induction T; intros theta X U Hfresh; simpl in *.
  - reflexivity.
  - unfold type_subst_update.
    assert (Hneq : X <> a) by (intro; subst; apply Hfresh; auto).
    rewrite (proj2 (Nat.eqb_neq X a)) by assumption. reflexivity.
  - rewrite in_app_iff in Hfresh.
    rewrite IHT1, IHT2; tauto.
  - f_equal. apply IHT. assumption.
  - reflexivity.
Qed.

Lemma instantiate_ty_open_rec_commute : forall T k U theta,
  type_substitution_closed theta ->
  instantiate_ty theta (open_ty_rec k U T) =
  open_ty_rec k (instantiate_ty theta U) (instantiate_ty theta T).
Proof.
  induction T; intros k U theta Htheta; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. apply open_ty_rec_lc_at.
    eapply lc_ty_at_monotone; [apply Htheta | lia].
  - rewrite IHT1, IHT2; try assumption. reflexivity.
  - rewrite IHT; try assumption. reflexivity.
  - reflexivity.
Qed.

Lemma instantiate_ty_open_commute : forall T U theta,
  type_substitution_closed theta ->
  instantiate_ty theta (open_ty T U) =
  open_ty (instantiate_ty theta T) (instantiate_ty theta U).
Proof.
  intros. unfold open_ty. apply instantiate_ty_open_rec_commute. assumption.
Qed.

Lemma has_type_instantiate : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  context_wf Delta Gamma ->
  forall Delta' Gamma' theta gamma,
    type_substitution_closed theta ->
    term_substitution_closed gamma ->
    type_substitution_wf Delta Delta' theta ->
    term_substitution_typed Gamma Delta' Gamma' theta gamma ->
    has_type Delta' Gamma'
      (instantiate theta gamma t) (instantiate_ty theta T).
Proof.
  intros Delta Gamma t T Hty. induction Hty as
      [Delta Gamma x T Hlookup Hwf
      | L Delta Gamma T1 body T2 Hwf Hbody IHbody
      | Delta Gamma t1 t2 T1 T2 Ht1 IHt1 Ht2 IHt2
      | L Delta Gamma body T Hbody IHbody
      | Delta Gamma t T U Ht IHt HU
      | Delta Gamma n
      | Delta Gamma t1 t2 Ht1 IHt1 Ht2 IHt2
      | Delta Gamma op t1 t2 Ht1 IHt1 Ht2 IHt2];
    intros Hctx Delta' Gamma' theta gamma Htheta Hgamma Htheta_wf Hgamma_ty;
    simpl.
  - eapply Hgamma_ty. exact Hlookup.
  - apply T_Abs with (L ++ fv_tm body ++ dom_context Gamma').
    + eapply wf_ty_instantiate; eauto.
    + intros x Hfresh. repeat rewrite in_app_iff in Hfresh.
      assert (HxL : ~ In x L) by intuition.
      assert (Hxbody : ~ In x (fv_tm body)) by intuition.
      assert (HxGamma' : ~ In x (dom_context Gamma')) by intuition.
      pose proof (IHbody x HxL
        (context_wf_update Delta Gamma x T1 Hctx Hwf)
        Delta' (update Gamma' x (instantiate_ty theta T1)) theta
        (term_subst_update gamma x (tm_fvar x))) as IH.
      rewrite <- (instantiate_open_tm body theta gamma x (tm_fvar x));
        try assumption; try apply lc_tm_fvar.
      apply IH; try assumption.
      * apply term_subst_update_closed; [assumption | apply lc_tm_fvar].
      * unfold term_substitution_typed. intros y U Hlookup'.
        unfold update in Hlookup'. simpl in Hlookup'.
        unfold term_subst_update.
        destruct (Nat.eqb y x) eqn:E.
        -- apply Nat.eqb_eq in E. subst y. rewrite Nat.eqb_refl.
           inversion Hlookup'; subst U.
           apply T_Var.
           ++ unfold update. simpl. rewrite Nat.eqb_refl. reflexivity.
           ++ eapply wf_ty_instantiate; eauto.
        -- apply Nat.eqb_neq in E.
           rewrite (proj2 (Nat.eqb_neq x y)) by congruence.
           eapply has_type_weaken_context.
           ++ eapply Hgamma_ty. exact Hlookup'.
           ++ apply context_included_update_fresh. exact HxGamma'.
  - eapply T_App.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
  - apply T_TAbs with
      (L ++ Delta ++ Delta' ++ ftv_tm body ++ fv_ty T).
    intros X Hfresh. repeat rewrite in_app_iff in Hfresh.
    assert (HXL : ~ In X L) by intuition.
    assert (HXDelta : ~ In X Delta) by intuition.
    assert (HXDelta' : ~ In X Delta') by intuition.
    assert (HXbody : ~ In X (ftv_tm body)) by intuition.
    assert (HXT : ~ In X (fv_ty T)) by intuition.
    set (theta' := type_subst_update theta X (Ty_FVar X)).
    assert (Hctx' : context_wf (X :: Delta) Gamma).
    { eapply context_wf_weaken_type; [exact Hctx |].
      unfold ty_context_included. simpl. auto. }
    assert (Htheta_wf' : type_substitution_wf
      (X :: Delta) (X :: Delta') theta').
    { unfold theta', type_substitution_wf, type_subst_update.
      intros Y [E | Hin].
      - subst Y. rewrite Nat.eqb_refl. apply WF_Var. simpl. auto.
      - assert (Hneq : X <> Y) by (intro; subst; contradiction).
        rewrite (proj2 (Nat.eqb_neq X Y)) by assumption.
        eapply wf_ty_weaken.
        + apply Htheta_wf. exact Hin.
        + unfold ty_context_included. simpl. auto. }
    assert (Hgamma_ty' : term_substitution_typed
      Gamma (X :: Delta') Gamma' theta' gamma).
    { unfold term_substitution_typed in *. intros x U Hlookup.
      assert (HwfU : wf_ty Delta U) by (eapply Hctx; eauto).
      assert (HXU : ~ In X (fv_ty U)).
      { intro Hin. apply HXDelta. eapply wf_ty_fv; eauto. }
      unfold theta'.
      rewrite instantiate_ty_update_irrelevant by exact HXU.
      eapply has_type_weaken_type.
      - eapply Hgamma_ty. exact Hlookup.
      - unfold ty_context_included. simpl. auto. }
    pose proof (IHbody X HXL Hctx' (X :: Delta') Gamma'
      theta' gamma) as IH.
    rewrite <- (instantiate_open_ty body theta gamma X (Ty_FVar X));
      try assumption; try apply lc_ty_fvar.
    rewrite <- (instantiate_ty_open T theta X (Ty_FVar X));
      try assumption; try apply lc_ty_fvar.
    assert (Htheta' : type_substitution_closed theta').
    { unfold theta'. apply type_subst_update_closed; auto. apply lc_ty_fvar. }
    exact (IH Htheta' Hgamma Htheta_wf' Hgamma_ty').
  - rewrite instantiate_ty_open_commute by exact Htheta.
    eapply T_TApp.
    + apply IHt; assumption.
    + eapply wf_ty_instantiate; eauto.
  - apply T_Int.
  - apply T_Div; [apply IHt1 | apply IHt2]; assumption.
  - apply T_Arith; [apply IHt1 | apply IHt2]; assumption.
Qed.

Lemma wf_ty_open_all : forall Delta T U,
  wf_ty Delta (Ty_All T) -> wf_ty Delta U -> wf_ty Delta (open_ty T U).
Proof.
  intros Delta T U Hall HU.
  inversion Hall as [| |L Delta0 body Hbody|]; subst.
  set (X := fresh (L ++ Delta ++ fv_ty T)).
  assert (HX : ~ In X (L ++ Delta ++ fv_ty T)).
  { subst X. apply fresh_notin. }
  repeat rewrite in_app_iff in HX.
  assert (HXL : ~ In X L) by intuition.
  assert (HXDelta : ~ In X Delta) by intuition.
  assert (HXT : ~ In X (fv_ty T)) by intuition.
  pose proof (Hbody X HXL) as Hopened.
  set (theta := type_subst_update identity_type_substitution X U).
  assert (Htheta_closed : type_substitution_closed theta).
  { unfold theta. apply type_subst_update_closed.
    - apply identity_type_substitution_closed.
    - apply wf_ty_lc with Delta. exact HU. }
  assert (Htheta_wf : type_substitution_wf (X :: Delta) Delta theta).
  { unfold theta, type_substitution_wf, type_subst_update,
      identity_type_substitution.
    intros Y [E | Hin].
    - subst Y. rewrite Nat.eqb_refl. exact HU.
    - assert (Hneq : X <> Y) by (intro; subst; contradiction).
      rewrite (proj2 (Nat.eqb_neq X Y)) by assumption.
      apply WF_Var. exact Hin. }
  pose proof (wf_ty_instantiate _ _ Hopened Delta theta Htheta_wf) as Hinst.
  assert (Hopen : instantiate_ty theta (open_ty T (Ty_FVar X)) = open_ty T U).
  { unfold theta.
    rewrite instantiate_ty_open_local.
    - rewrite instantiate_ty_identity. reflexivity.
    - exact HXT.
    - intros Y Hin. apply lc_ty_fvar.
    - apply wf_ty_lc with Delta. exact HU. }
  rewrite Hopen in Hinst. exact Hinst.
Qed.

Lemma typing_type_wf : forall Delta Gamma t T,
  has_type Delta Gamma t T -> wf_ty Delta T.
Proof.
  intros Delta Gamma t T Hty. induction Hty.
  - exact H0.
  - apply WF_Arrow; [exact H |].
    set (x := fresh L). apply H1 with x. subst x. apply fresh_notin.
  - inversion IHHty1. assumption.
  - apply WF_All with L. intros X Hfresh. apply H0. exact Hfresh.
  - eapply wf_ty_open_all; eauto.
  - apply WF_Int.
  - apply WF_Int.
  - apply WF_Int.
Qed.

End SystemFRefinementCoreTyping.

From Stdlib Require Import Arith.PeanoNat Lists.List ZArith.BinInt.
Module SystemFRefinementLogic.
Import ListNotations SystemFRefinement.

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

Lemma interpret_qualifier_ext : forall atoms1 atoms2 p,
  (forall t1 t2, atoms1.(interpret_eq) t1 t2 <-> atoms2.(interpret_eq) t1 t2) ->
  (forall t1 t2, atoms1.(interpret_lt) t1 t2 <-> atoms2.(interpret_lt) t1 t2) ->
  (forall t1 t2, atoms1.(interpret_le) t1 t2 <-> atoms2.(interpret_le) t1 t2) ->
  (interpret_qualifier atoms1 p <-> interpret_qualifier atoms2 p).
Proof.
  intros atoms1 atoms2 p Heq Hlt Hle.
  induction p; simpl; firstorder.
Qed.

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

End SystemFRefinementLogic.

From Stdlib Require Import Arith.PeanoNat Lists.List Lia ZArith.BinInt.
Module SystemFRefinementTyping.
Import ListNotations.
Import SystemFRefinement.
Export SystemFRefinementLogic.

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

Lemma erase_open_rty_tm_rec : forall R k u,
  erase (open_rty_tm_rec k u R) = erase R.
Proof.
  induction R; intros; simpl; try rewrite IHR1; try rewrite IHR2;
    try rewrite IHR; reflexivity.
Qed.

Lemma erase_open_rty_tm : forall R u,
  erase (open_rty_tm R u) = erase R.
Proof.
  intros. apply erase_open_rty_tm_rec.
Qed.

Lemma erase_open_rty_ty_rec : forall R k U,
  erase (open_rty_ty_rec k U R) = open_ty_rec k U (erase R).
Proof.
  induction R; intros; simpl.
  - reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR2. reflexivity.
  - rewrite IHR. reflexivity.
Qed.

Lemma erase_open_rty_ty : forall R U,
  erase (open_rty_ty R U) = open_ty (erase R) U.
Proof.
  intros. unfold open_rty_ty, open_ty. apply erase_open_rty_ty_rec.
Qed.

Lemma lookup_erase_context : forall RGamma x R,
  lookup_rcontext x RGamma = Some R ->
  lookup_context x (erase_context RGamma) = Some (erase R).
Proof.
  induction RGamma as [|[y S] RGamma IH]; intros x R Hlookup; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + inversion Hlookup; subst. reflexivity.
    + apply IH. exact Hlookup.
Qed.

Fixpoint close_ty_rec (k : nat) (X : atom) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar Y => if Nat.eqb X Y then Ty_BVar k else Ty_FVar Y
  | Ty_Arrow T1 T2 =>
      Ty_Arrow (close_ty_rec k X T1) (close_ty_rec k X T2)
  | Ty_All T1 => Ty_All (close_ty_rec (S k) X T1)
  | Ty_Int => Ty_Int
  end.

Lemma close_open_ty_rec : forall T k X,
  ~ In X (fv_ty T) ->
  close_ty_rec k X (open_ty_rec k (Ty_FVar X) T) = T.
Proof.
  induction T; intros k X Hfresh; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n.
      change ((if Nat.eqb X X then Ty_BVar k else Ty_FVar X) = Ty_BVar k).
      rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - assert (X <> a) by intuition.
    rewrite (proj2 (Nat.eqb_neq X a)) by assumption. reflexivity.
  - rewrite in_app_iff in Hfresh. rewrite IHT1, IHT2; intuition.
  - rewrite IHT by assumption. reflexivity.
  - reflexivity.
Qed.

Lemma open_ty_fresh_injective : forall T1 T2 X,
  ~ In X (fv_ty T1) ->
  ~ In X (fv_ty T2) ->
  open_ty T1 (Ty_FVar X) = open_ty T2 (Ty_FVar X) ->
  T1 = T2.
Proof.
  intros T1 T2 X H1 H2 E.
  apply (f_equal (close_ty_rec 0 X)) in E.
  unfold open_ty in E.
  rewrite (close_open_ty_rec T1 0 X H1) in E.
  rewrite (close_open_ty_rec T2 0 X H2) in E.
  exact E.
Qed.

Lemma subtype_erases : forall Delta RGamma R S,
  subtype Delta RGamma R S -> erase R = erase S.
Proof.
  fix IH 5.
  intros Delta RGamma R S Hsub.
  destruct Hsub as
    [Delta RGamma R
    |L Delta RGamma T ps qs Hentails
    |L Delta RGamma R1 R2 S1 S2 Hdom Hcod
    |Delta RGamma v R1 R2 S Hv Htyped Hbody
    |L Delta RGamma R1 R2 S HR1 HS Hbody
    |L Delta RGamma R S Hbody
    |Delta RGamma R S U HRS HSU].
  - reflexivity.
  - reflexivity.
  - simpl. f_equal.
    + symmetry. exact (IH _ _ _ _ Hdom).
    + set (x := fresh L).
      assert (Hfresh : ~ In x L) by (subst x; apply fresh_notin).
      pose proof (IH _ _ _ _ (Hcod x Hfresh)) as E.
      rewrite !erase_open_rty_tm in E. exact E.
  - simpl. pose proof (IH _ _ _ _ Hbody) as E.
    rewrite erase_open_rty_tm in E. exact E.
  - simpl. set (x := fresh L).
    assert (Hfresh : ~ In x L) by (subst x; apply fresh_notin).
    pose proof (IH _ _ _ _ (Hbody x Hfresh)) as E.
    rewrite erase_open_rty_tm in E. exact E.
  - simpl. f_equal.
    set (X := fresh (L ++ fv_ty (erase R) ++ fv_ty (erase S))).
    assert (HX : ~ In X (L ++ fv_ty (erase R) ++ fv_ty (erase S))).
    { subst X. apply fresh_notin. }
    repeat rewrite in_app_iff in HX.
    assert (HXL : ~ In X L) by intuition.
    assert (HXR : ~ In X (fv_ty (erase R))) by intuition.
    assert (HXS : ~ In X (fv_ty (erase S))) by intuition.
    pose proof (IH _ _ _ _ (Hbody X HXL)) as E.
    rewrite !erase_open_rty_ty in E.
    eapply open_ty_fresh_injective; eauto.
  - etransitivity.
    + exact (IH _ _ _ _ HRS).
    + exact (IH _ _ _ _ HSU).
Qed.

Lemma wf_rty_erases : forall Delta RGamma R,
  wf_rty Delta RGamma R -> wf_ty Delta (erase R).
Proof.
  fix IH 4.
  intros Delta RGamma R Hwf.
  destruct Hwf as
    [L Delta RGamma T ps HT Hps
    |L Delta RGamma R1 R2 HR1 HR2
    |L Delta RGamma R1 R2 HR1 HR2
    |L Delta RGamma R HR].
  - exact HT.
  - simpl. apply WF_Arrow.
    + exact (IH _ _ _ HR1).
    + set (x := fresh L).
      rewrite <- (erase_open_rty_tm R2 (tm_fvar x)).
      apply IH with (RGamma := update_rcontext RGamma x R1).
      apply HR2. subst x. apply fresh_notin.
  - simpl. set (x := fresh L).
    rewrite <- (erase_open_rty_tm R2 (tm_fvar x)).
    apply IH with (RGamma := update_rcontext RGamma x R1).
    apply HR2. subst x. apply fresh_notin.
  - simpl. apply WF_All with L. intros X Hfresh.
    rewrite <- erase_open_rty_ty.
    apply IH with (RGamma := RGamma).
    apply HR. exact Hfresh.
Qed.

Theorem refinement_typing_erases : forall Delta RGamma t R,
  has_rtype Delta RGamma t R ->
  has_type Delta (erase_context RGamma) t (erase R).
Proof.
  intros Delta RGamma t R Hty. induction Hty.
  - apply T_Var.
    + eapply lookup_erase_context. exact H.
    + exact (wf_rty_erases Delta RGamma R H0).
  - simpl. apply T_Abs with L.
    + exact (wf_rty_erases Delta RGamma R1 H).
    + intros x Hfresh. simpl.
      rewrite <- (erase_open_rty_tm R2 (tm_fvar x)).
      apply H1. exact Hfresh.
  - simpl. eapply T_App; eauto.
  - simpl. apply T_TAbs with L. intros X Hfresh.
    rewrite <- (erase_open_rty_ty R (Ty_FVar X)). apply H0. exact Hfresh.
  - rewrite (erase_open_rty_ty R U). eapply T_TApp; eauto.
  - apply T_Int.
  - simpl in *. apply T_Div; assumption.
  - simpl in *. apply T_Arith; assumption.
  - exact H.
  - match goal with
    | Hsub : subtype _ _ _ _ |- _ =>
        pose proof (subtype_erases _ _ _ _ Hsub) as E
    end.
    rewrite <- E. exact IHHty.
Qed.

End SystemFRefinementTyping.

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Module SystemFRefinementEvaluation.
Import ListNotations SystemFRefinement SystemFRefinementInfrastructure
  SystemFRefinementCoreTyping.

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

Lemma step_preserves_lc : forall t u,
  t --> u -> locally_closed_tm t -> locally_closed_tm u.
Proof.
  intros t u Hstep. induction Hstep; intros Hlc; unfold locally_closed_tm in *;
    inversion Hlc; subst; eauto 10 using lc_tm_at, value_regular.
  - eapply open_tm_preserves_lc_at.
    + inversion H; eassumption.
    + apply value_regular. exact H0.
  - eapply open_tm_ty_preserves_lc_at.
    + inversion H; eassumption.
    + exact H0.

Qed.

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

Lemma term_beta_typing : forall L T1 body T2 v,
  wf_ty [] T1 ->
  (forall x, ~ In x L ->
    has_type [] (update empty x T1)
      (open_tm body (tm_fvar x)) T2) ->
  has_type [] empty v T1 ->
  has_type [] empty (open_tm body v) T2.
Proof.
  intros L T1 body T2 v HT1 Hbody Hv.
  set (x := fresh (L ++ fv_tm body)).
  assert (Hx : ~ In x (L ++ fv_tm body)).
  { subst x. apply fresh_notin. }
  rewrite in_app_iff in Hx.
  assert (HxL : ~ In x L) by intuition.
  assert (Hxfv : ~ In x (fv_tm body)) by intuition.
  pose proof (Hbody x HxL) as Hopened.
  set (gamma := term_subst_update identity_term_substitution x v).
  assert (Hctx : context_wf [] (update empty x T1)).
  { intros y U Hlookup. unfold update, empty in Hlookup. simpl in Hlookup.
    destruct (Nat.eqb y x) eqn:E; try discriminate.
    inversion Hlookup; subst. exact HT1. }
  assert (Htheta_wf :
    type_substitution_wf [] [] identity_type_substitution).
  { intros X Hin. contradiction. }
  assert (Hgamma_typed : term_substitution_typed
      (update empty x T1) [] empty identity_type_substitution gamma).
  { intros y U Hlookup. unfold update, empty in Hlookup. simpl in Hlookup.
    destruct (Nat.eqb y x) eqn:E; try discriminate.
    apply Nat.eqb_eq in E. subst y. inversion Hlookup; subst U.
    unfold gamma, term_subst_update. rewrite Nat.eqb_refl.
    rewrite instantiate_ty_identity. exact Hv. }
  pose proof (has_type_instantiate _ _ _ _ Hopened Hctx
    [] empty identity_type_substitution gamma
    identity_type_substitution_closed
    (term_subst_update_closed identity_term_substitution x v
      identity_term_substitution_closed (typing_lc _ _ _ _ Hv))
    Htheta_wf Hgamma_typed) as Hinst.
  unfold gamma in Hinst.
  rewrite (instantiate_open_tm body identity_type_substitution
      identity_term_substitution x v Hxfv
      identity_type_substitution_closed identity_term_substitution_closed
      (typing_lc _ _ _ _ Hv)) in Hinst.
  rewrite instantiate_identity, instantiate_ty_identity in Hinst.
  exact Hinst.
Qed.

Lemma type_beta_typing : forall L body T U,
  (forall X, ~ In X L ->
    has_type [X] empty
      (open_tm_ty body (Ty_FVar X))
      (open_ty T (Ty_FVar X))) ->
  wf_ty [] U ->
  has_type [] empty (open_tm_ty body U) (open_ty T U).
Proof.
  intros L body T U Hbody HU.
  set (X := fresh (L ++ ftv_tm body ++ fv_ty T)).
  assert (HX : ~ In X (L ++ ftv_tm body ++ fv_ty T)).
  { subst X. apply fresh_notin. }
  repeat rewrite in_app_iff in HX.
  assert (HXL : ~ In X L) by intuition.
  assert (HXbody : ~ In X (ftv_tm body)) by intuition.
  assert (HXT : ~ In X (fv_ty T)) by intuition.
  pose proof (Hbody X HXL) as Hopened.
  set (theta := type_subst_update identity_type_substitution X U).
  assert (Htheta_closed : type_substitution_closed theta).
  { unfold theta. apply type_subst_update_closed.
    - exact identity_type_substitution_closed.
    - exact (wf_ty_lc [] U HU). }
  assert (Htheta_wf : type_substitution_wf [X] [] theta).
  { intros Y Hin. simpl in Hin. destruct Hin as [E | Hin]; [|contradiction].
    subst Y. unfold theta, type_subst_update. rewrite Nat.eqb_refl. exact HU. }
  assert (Hctx : context_wf [X] empty).
  { intros y V Hlookup. discriminate. }
  assert (Hgamma_typed : term_substitution_typed
      empty [] empty theta identity_term_substitution).
  { intros y V Hlookup. discriminate. }
  pose proof (has_type_instantiate _ _ _ _ Hopened Hctx
    [] empty theta identity_term_substitution
    Htheta_closed identity_term_substitution_closed
    Htheta_wf Hgamma_typed) as Hinst.
  unfold theta in Hinst.
  rewrite (instantiate_open_ty body identity_type_substitution
      identity_term_substitution X U HXbody
      identity_type_substitution_closed identity_term_substitution_closed
      (wf_ty_lc [] U HU)) in Hinst.
  rewrite (instantiate_ty_open_local T identity_type_substitution X U HXT) in Hinst.
  - rewrite instantiate_identity, instantiate_ty_identity in Hinst. exact Hinst.
  - intros Y Hin. apply lc_ty_fvar.
  - exact (wf_ty_lc [] U HU).
Qed.

Theorem core_preservation : forall t t' T,
  has_type [] empty t T ->
  t --> t' ->
  has_type [] empty t' T.
Proof.
  intros t t' T Hty Hstep.
  remember (@nil atom) as Delta eqn:EDelta.
  remember empty as Gamma eqn:EGamma.
  generalize dependent t'.
  induction Hty; intros t' Hstep; subst; inversion Hstep; subst.
  - inversion Hty1; subst. eapply term_beta_typing; eauto.
  - eapply T_App; eauto.
  - eapply T_App; eauto.
  - inversion Hty; subst. eapply type_beta_typing; eauto.
  - eapply T_TApp; eauto.
  - apply T_Div; eauto.
  - apply T_Div; eauto.
  - apply T_Int.
  - apply T_Arith; eauto.
  - apply T_Arith; eauto.
  - apply T_Int.
Qed.

Lemma multi_preservation : forall t t' T,
  has_type [] empty t T ->
  multi t t' ->
  has_type [] empty t' T.
Proof.
  intros t t' T Hty Hmulti. induction Hmulti.
  - exact Hty.
  - apply IHHmulti. eapply core_preservation; eauto.
Qed.

Lemma step_deterministic : forall t u,
  t --> u -> forall v, t --> v -> u = v.
Proof.
  intros t u H. induction H; intros z Hz; inversion Hz; subst;
    try reflexivity;
    try solve [match goal with Hs : step (tm_abs _ _) _ |- _ => inversion Hs end];
    try solve [match goal with Hs : step (tm_tabs _) _ |- _ => inversion Hs end];
    try solve [match goal with Hs : step (tm_int _) _ |- _ => inversion Hs end];
    try solve [exfalso; eapply value_no_step; eauto using value];
    try solve [exfalso; match goal with Hv : value ?v, Hs : step ?v _ |- _ => exact (value_no_step v Hv _ Hs) end];
    f_equal; eauto.
Qed.

Lemma multi_trans : forall t u v,
  multi t u -> multi u v -> multi t v.
Proof. intros t u v H. induction H; eauto using multi. Qed.

Lemma halts_value : forall v, value v -> halts v.
Proof. intros v Hv. exists v. split; [constructor|assumption]. Qed.

Lemma halts_step : forall t u, t --> u -> halts t -> halts u.
Proof.
  intros t u Hstep [v [Hsteps Hv]].
  inversion Hsteps; subst.
  - exfalso. eapply value_no_step; eauto.
  - assert (u = t2) by (eapply step_deterministic; eauto).
    subst. exists v. auto.
Qed.

Lemma halts_multi : forall t u, multi t u -> halts t -> halts u.
Proof.
  intros t u H. induction H; intros HH; auto.
  apply IHmulti. eapply halts_step; eauto.
Qed.
Lemma multi_value_unique : forall t v,
  multi t v -> value v ->
  forall w, multi t w -> value w -> v = w.
Proof.
  intros t v H. induction H; intros Hv w Hw Hvw.
  - symmetry. eapply value_multi_eq; eauto.
  - inversion Hw; subst.
    + exfalso. eapply value_no_step; eauto.
    + match goal with Hs : t1 --> ?u |- _ =>
        assert (t2 = u) by (eapply step_deterministic; eauto); subst u
      end.
      eapply IHmulti; eauto.
Qed.

End SystemFRefinementEvaluation.

From Stdlib Require Import Arith.PeanoNat Lists.List Lia Program.Wf.
From Equations Require Import Equations.
Module SystemFRefinementDenotations.
Import ListNotations.
Import SystemFRefinement.
Import SystemFRefinementInfrastructure.
Import SystemFRefinementCoreTyping.
Import SystemFRefinementTyping.
Import SystemFRefinementEvaluation.

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

Lemma erase_instantiate_rty : forall theta gamma R,
  erase (instantiate_rty theta gamma R) = instantiate_ty theta (erase R).
Proof.
  induction R; intros; simpl; rewrite ?IHR1, ?IHR2, ?IHR; reflexivity.
Qed.

Lemma instantiate_pred_open_tm_rec : forall p k theta gamma x u,
  ~ In x (fv_pred p) ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  instantiate_pred theta (term_subst_update gamma x u)
    (open_pred_tm_rec k (tm_fvar x) p) =
  open_pred_tm_rec k u (instantiate_pred theta gamma p).
Proof.
  induction p; intros; simpl in *; try reflexivity;
    try solve [rewrite in_app_iff in H; rewrite !instantiate_open_tm_rec; intuition];
    try solve [rewrite in_app_iff in H; rewrite IHp1, IHp2; intuition].
  f_equal. apply IHp; assumption.
Qed.

Lemma instantiate_qualifier_open_tm_rec : forall ps k theta gamma x u,
  ~ In x (fv_qualifier ps) ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  instantiate_qualifier theta (term_subst_update gamma x u)
    (open_qualifier_tm_rec k (tm_fvar x) ps) =
  open_qualifier_tm_rec k u (instantiate_qualifier theta gamma ps).
Proof.
  exact instantiate_pred_open_tm_rec.
Qed.

Lemma instantiate_rty_open_tm_rec : forall R k theta gamma x u,
  ~ In x (fv_rty R) ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  instantiate_rty theta (term_subst_update gamma x u)
    (open_rty_tm_rec k (tm_fvar x) R) =
  open_rty_tm_rec k u (instantiate_rty theta gamma R).
Proof.
  induction R; intros; simpl in *.
  - f_equal. apply instantiate_qualifier_open_tm_rec; assumption.
  - rewrite in_app_iff in H.
    rewrite IHR1, IHR2; intuition.
  - rewrite in_app_iff in H.
    rewrite IHR1, IHR2; intuition.
  - f_equal. apply IHR; assumption.
Qed.

Lemma instantiate_rty_open_tm : forall R theta gamma x u,
  ~ In x (fv_rty R) ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  instantiate_rty theta (term_subst_update gamma x u)
    (open_rty_tm R (tm_fvar x)) =
  open_rty_tm (instantiate_rty theta gamma R) u.
Proof.
  intros. unfold open_rty_tm.
  apply instantiate_rty_open_tm_rec; assumption.
Qed.

Lemma instantiate_pred_open_ty_rec : forall p k theta gamma X U,
  ~ In X (ftv_pred p) ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_ty U ->
  instantiate_pred (type_subst_update theta X U) gamma
    (open_pred_ty_rec k (Ty_FVar X) p) =
  open_pred_ty_rec k U (instantiate_pred theta gamma p).
Proof.
  induction p; intros; simpl in *; try reflexivity;
    try solve [rewrite in_app_iff in H; rewrite !instantiate_open_ty_rec; intuition];
    try solve [rewrite in_app_iff in H; rewrite IHp1, IHp2; intuition].
  f_equal. apply IHp; assumption.
Qed.

Lemma instantiate_qualifier_open_ty_rec : forall ps k theta gamma X U,
  ~ In X (ftv_qualifier ps) ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_ty U ->
  instantiate_qualifier (type_subst_update theta X U) gamma
    (open_qualifier_ty_rec k (Ty_FVar X) ps) =
  open_qualifier_ty_rec k U (instantiate_qualifier theta gamma ps).
Proof.
  exact instantiate_pred_open_ty_rec.
Qed.

Lemma instantiate_rty_open_ty_rec : forall R k theta gamma X U,
  ~ In X (ftv_rty R) ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_ty U ->
  instantiate_rty (type_subst_update theta X U) gamma
    (open_rty_ty_rec k (Ty_FVar X) R) =
  open_rty_ty_rec k U (instantiate_rty theta gamma R).
Proof.
  induction R; intros; simpl in *.
  - rewrite in_app_iff in H.
    f_equal.
    + apply instantiate_ty_open_rec; intuition.
    + apply instantiate_qualifier_open_ty_rec; intuition.
  - rewrite in_app_iff in H.
    rewrite IHR1, IHR2; intuition.
  - rewrite in_app_iff in H.
    rewrite IHR1, IHR2; intuition.
  - f_equal. apply IHR; assumption.
Qed.

Lemma instantiate_rty_open_ty : forall R theta gamma X U,
  ~ In X (ftv_rty R) ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_ty U ->
  instantiate_rty (type_subst_update theta X U) gamma
    (open_rty_ty R (Ty_FVar X)) =
  open_rty_ty (instantiate_rty theta gamma R) U.
Proof.
  intros. unfold open_rty_ty.
  apply instantiate_rty_open_ty_rec; assumption.
Qed.

Lemma instantiate_term_update_irrelevant : forall t theta gamma x u,
  ~ In x (fv_tm t) ->
  instantiate theta (term_subst_update gamma x u) t =
  instantiate theta gamma t.
Proof.
  induction t; intros; simpl in *; try reflexivity.
  - unfold term_subst_update.
    rewrite (proj2 (Nat.eqb_neq x a)); [reflexivity | intuition].
  - f_equal. apply IHt. exact H.
  - rewrite in_app_iff in H. f_equal; [apply IHt1 | apply IHt2]; intuition.
  - f_equal. apply IHt. exact H.
  - f_equal. apply IHt. exact H.
  - rewrite in_app_iff in H. f_equal; [apply IHt1 | apply IHt2]; intuition.
  - rewrite in_app_iff in H. f_equal; [apply IHt1 | apply IHt2]; intuition.
Qed.

Lemma instantiate_rty_term_update_irrelevant : forall R theta gamma x u,
  ~ In x (fv_rty R) ->
  instantiate_rty theta (term_subst_update gamma x u) R =
  instantiate_rty theta gamma R.
Proof.
  induction R as [T ps | R1 IHR1 R2 IHR2 | R1 IHR1 R2 IHR2 | R IHR];
    intros; simpl in *.
  - f_equal. induction ps; simpl in *; try reflexivity;
      try solve [rewrite in_app_iff in H; f_equal; apply instantiate_term_update_irrelevant; intuition];
      try solve [rewrite in_app_iff in H; f_equal; [apply IHps1|apply IHps2]; intuition].
    f_equal. apply IHps. exact H.
  - rewrite in_app_iff in H. f_equal; [apply IHR1|apply IHR2]; intuition.
  - rewrite in_app_iff in H. f_equal; [apply IHR1|apply IHR2]; intuition.
  - f_equal. apply IHR. exact H.
Qed.

Lemma instantiate_term_type_update_irrelevant : forall t theta gamma X U,
  ~ In X (ftv_tm t) ->
  instantiate (type_subst_update theta X U) gamma t =
  instantiate theta gamma t.
Proof.
  induction t; intros; simpl in *; try reflexivity.
  - rewrite in_app_iff in H. f_equal.
    + apply instantiate_ty_update_irrelevant. tauto.
    + apply IHt. tauto.
  - rewrite in_app_iff in H. f_equal; [apply IHt1 | apply IHt2]; tauto.
  - f_equal. apply IHt. exact H.
  - rewrite in_app_iff in H. f_equal.
    + apply IHt. tauto.
    + apply instantiate_ty_update_irrelevant. tauto.
  - rewrite in_app_iff in H. f_equal; [apply IHt1 | apply IHt2]; intuition.
  - rewrite in_app_iff in H. f_equal; [apply IHt1 | apply IHt2]; intuition.
Qed.

Lemma instantiate_rty_type_update_irrelevant : forall R theta gamma X U,
  ~ In X (ftv_rty R) ->
  instantiate_rty (type_subst_update theta X U) gamma R =
  instantiate_rty theta gamma R.
Proof.
  induction R as [T ps | R1 IHR1 R2 IHR2 | R1 IHR1 R2 IHR2 | R IHR];
    intros; simpl in *.
  - rewrite in_app_iff in H. f_equal.
    + apply instantiate_ty_update_irrelevant. intuition.
    + assert (HF : ~ In X (ftv_pred ps)) by intuition.
      clear H. rename HF into H.
      induction ps; simpl in *; try reflexivity;
        try solve [rewrite in_app_iff in H; f_equal; apply instantiate_term_type_update_irrelevant; intuition];
        try solve [rewrite in_app_iff in H; f_equal; [apply IHps1|apply IHps2]; intuition].
      f_equal. apply IHps. exact H.
  - rewrite in_app_iff in H. f_equal; [apply IHR1|apply IHR2]; intuition.
  - rewrite in_app_iff in H. f_equal; [apply IHR1|apply IHR2]; intuition.
  - f_equal. apply IHR. exact H.
Qed.

Lemma instantiate_open_tm_rec_commute : forall t k u theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  instantiate theta gamma (open_tm_rec k u t) =
  open_tm_rec k (instantiate theta gamma u) (instantiate theta gamma t).
Proof.
  induction t; intros; simpl; try reflexivity.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. apply open_tm_rec_lc_at with (K := 0).
    eapply lc_tm_at_monotone; [apply H0 | lia | lia].
  - f_equal. apply IHt; assumption.
  - f_equal; [apply IHt1 | apply IHt2]; assumption.
  - f_equal. apply IHt; assumption.
  - f_equal. apply IHt; assumption.
  - f_equal; [apply IHt1 | apply IHt2]; assumption.
  - f_equal; [apply IHt1 | apply IHt2]; assumption.
Qed.

Lemma instantiate_open_tm_commute : forall t u theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  instantiate theta gamma (open_tm t u) =
  open_tm (instantiate theta gamma t) (instantiate theta gamma u).
Proof.
  intros. unfold open_tm. apply instantiate_open_tm_rec_commute; assumption.
Qed.

Lemma instantiate_pred_open_tm_commute : forall p k u theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  instantiate_pred theta gamma (open_pred_tm_rec k u p) =
  open_pred_tm_rec k (instantiate theta gamma u)
    (instantiate_pred theta gamma p).
Proof.
  induction p; intros; simpl; try reflexivity;
    try solve [rewrite !instantiate_open_tm_rec_commute; try assumption; reflexivity];
    try solve [rewrite IHp1, IHp2; try assumption; reflexivity].
  f_equal. apply IHp; assumption.
Qed.

Lemma instantiate_qualifier_open_tm_commute : forall ps k u theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  instantiate_qualifier theta gamma (open_qualifier_tm_rec k u ps) =
  open_qualifier_tm_rec k (instantiate theta gamma u)
    (instantiate_qualifier theta gamma ps).
Proof.
  exact instantiate_pred_open_tm_commute.
Qed.

Lemma instantiate_rty_open_tm_commute : forall R k u theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  instantiate_rty theta gamma (open_rty_tm_rec k u R) =
  open_rty_tm_rec k (instantiate theta gamma u)
    (instantiate_rty theta gamma R).
Proof.
  induction R; intros; simpl.
  - f_equal. apply instantiate_qualifier_open_tm_commute; assumption.
  - rewrite IHR1, IHR2; try assumption. reflexivity.
  - rewrite IHR1, IHR2; try assumption. reflexivity.
  - rewrite IHR; try assumption. reflexivity.
Qed.

Lemma instantiate_rty_open_tm_commute_top : forall R u theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  instantiate_rty theta gamma (open_rty_tm R u) =
  open_rty_tm (instantiate_rty theta gamma R) (instantiate theta gamma u).
Proof.
  intros. unfold open_rty_tm. apply instantiate_rty_open_tm_commute; assumption.
Qed.

Lemma instantiate_open_ty_tm_rec_commute : forall t k U theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_ty U ->
  instantiate theta gamma (open_tm_ty_rec k U t) =
  open_tm_ty_rec k (instantiate_ty theta U) (instantiate theta gamma t).
Proof.
  induction t; intros; simpl; try reflexivity.
  - symmetry. apply open_tm_ty_rec_lc_at with (k := 0).
    eapply lc_tm_at_monotone; [apply H0 | lia | lia].
  - f_equal.
    + apply instantiate_ty_open_rec_commute. exact H.
    + apply IHt; assumption.
  - f_equal; [apply IHt1 | apply IHt2]; assumption.
  - f_equal. apply IHt; assumption.
  - f_equal.
    + apply IHt; assumption.
    + apply instantiate_ty_open_rec_commute. exact H.
  - f_equal; [apply IHt1 | apply IHt2]; assumption.
  - f_equal; [apply IHt1 | apply IHt2]; assumption.
Qed.

Lemma instantiate_open_ty_tm_commute : forall t U theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_ty U ->
  instantiate theta gamma (open_tm_ty t U) =
  open_tm_ty (instantiate theta gamma t) (instantiate_ty theta U).
Proof.
  intros. unfold open_tm_ty.
  apply instantiate_open_ty_tm_rec_commute; assumption.
Qed.

Lemma instantiate_pred_open_ty_commute : forall p k U theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_ty U ->
  instantiate_pred theta gamma (open_pred_ty_rec k U p) =
  open_pred_ty_rec k (instantiate_ty theta U)
    (instantiate_pred theta gamma p).
Proof.
  induction p; intros; simpl; try reflexivity;
    try solve [rewrite !instantiate_open_ty_tm_rec_commute; try assumption; reflexivity];
    try solve [rewrite IHp1, IHp2; try assumption; reflexivity].
  f_equal. apply IHp; assumption.
Qed.

Lemma instantiate_qualifier_open_ty_commute : forall ps k U theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_ty U ->
  instantiate_qualifier theta gamma (open_qualifier_ty_rec k U ps) =
  open_qualifier_ty_rec k (instantiate_ty theta U)
    (instantiate_qualifier theta gamma ps).
Proof.
  exact instantiate_pred_open_ty_commute.
Qed.

Lemma instantiate_rty_open_ty_commute : forall R k U theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_ty U ->
  instantiate_rty theta gamma (open_rty_ty_rec k U R) =
  open_rty_ty_rec k (instantiate_ty theta U)
    (instantiate_rty theta gamma R).
Proof.
  induction R; intros; simpl.
  - rewrite instantiate_ty_open_rec_commute,
      instantiate_qualifier_open_ty_commute; try assumption. reflexivity.
  - rewrite IHR1, IHR2; try assumption. reflexivity.
  - rewrite IHR1, IHR2; try assumption. reflexivity.
  - rewrite IHR; try assumption. reflexivity.
Qed.

Lemma instantiate_rty_open_ty_commute_top : forall R U theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_ty U ->
  instantiate_rty theta gamma (open_rty_ty R U) =
  open_rty_ty (instantiate_rty theta gamma R) (instantiate_ty theta U).
Proof.
  intros. unfold open_rty_ty. apply instantiate_rty_open_ty_commute; assumption.
Qed.

Lemma instantiate_value : forall v theta gamma,
  value v ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  value (instantiate theta gamma v).
Proof.
  intros v theta gamma Hv Htheta Hgamma. inversion Hv; subst; simpl.
  - apply v_abs.
    change (locally_closed_tm (instantiate theta gamma (tm_abs T t))).
    apply instantiate_closed; assumption.
  - apply v_tabs.
    change (locally_closed_tm (instantiate theta gamma (tm_tabs t))).
    apply instantiate_closed; assumption.
  - apply v_int.
Qed.

Lemma instantiate_step : forall t t' theta gamma,
  t --> t' ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  instantiate theta gamma t --> instantiate theta gamma t'.
Proof.
  intros t t' theta gamma Hstep Htheta Hgamma. induction Hstep; simpl.
  - rewrite instantiate_open_tm_commute; try assumption.
    + apply ST_AppAbs.
      * change (locally_closed_tm (instantiate theta gamma (tm_abs T t))).
        apply instantiate_closed; assumption.
      * apply instantiate_value; assumption.
    + apply value_regular. exact H0.
  - apply ST_App1.
    + apply IHHstep.
    + apply instantiate_closed; assumption.
  - apply ST_App2.
    + apply instantiate_value; assumption.
    + apply IHHstep.
  - rewrite instantiate_open_ty_tm_commute; try assumption.
    + apply ST_TAppTabs.
      * change (locally_closed_tm (instantiate theta gamma (tm_tabs t))).
        apply instantiate_closed; assumption.
      * apply instantiate_ty_closed; assumption.
  - apply ST_TApp.
    + apply IHHstep.
    + apply instantiate_ty_closed; assumption.
  - apply ST_Div1; [assumption|apply instantiate_closed; assumption].
  - apply ST_Div2; [apply instantiate_value; assumption|assumption].
  - apply ST_DivInt. assumption.
  - apply ST_Arith1; [assumption|apply instantiate_closed; assumption].
  - apply ST_Arith2; [apply instantiate_value; assumption|assumption].
  - apply ST_ArithInt.
Qed.

Lemma instantiate_predicate_multistep : forall t t' theta gamma,
  predicate_multistep t t' ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  predicate_multistep (instantiate theta gamma t)
    (instantiate theta gamma t').
Proof.
  intros t t' theta gamma Hmulti Htheta Hgamma. induction Hmulti.
  - apply PMS_Refl.
  - eapply PMS_Step.
    + eapply instantiate_step; eauto.
    + exact IHHmulti.
Qed.

Lemma instantiate_ty_no_free : forall T theta,
  fv_ty T = [] -> instantiate_ty theta T = T.
Proof.
  induction T; intros; simpl in *; try discriminate; try reflexivity.
  - apply app_eq_nil in H as [H1 H2]. rewrite IHT1, IHT2; auto.
  - rewrite IHT; auto.
Qed.

Lemma instantiate_no_free : forall t theta gamma,
  fv_tm t = [] -> ftv_tm t = [] -> instantiate theta gamma t = t.
Proof.
  induction t; intros; simpl in *; try discriminate; try reflexivity;
    repeat match goal with H : _ ++ _ = [] |- _ => apply app_eq_nil in H as [? ?] end;
    f_equal; eauto using instantiate_ty_no_free.
Qed.

Lemma instantiate_pred_closed : forall p theta gamma,
  predicate_closed p -> instantiate_pred theta gamma p = p.
Proof.
  induction p; intros; simpl in *; try reflexivity;
    try solve [decompose [and] H; f_equal; apply instantiate_no_free; assumption];
    try solve [destruct H; f_equal; auto].
  f_equal. apply IHp. assumption.
Qed.

Lemma instantiate_qualifier_holds : forall ps theta gamma,
  predicate_closed ps ->
  qualifier_holds ps ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  qualifier_holds (instantiate_qualifier theta gamma ps).
Proof.
  intros ps theta gamma Hclosed Hholds Htheta Hgamma.
  unfold instantiate_qualifier. rewrite instantiate_pred_closed by assumption.
  exact Hholds.
Qed.

Lemma instantiate_pred_open_rec_commute : forall p k u theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  instantiate_pred theta gamma (open_pred_tm_rec k u p) =
  open_pred_tm_rec k (instantiate theta gamma u)
    (instantiate_pred theta gamma p).
Proof.
  induction p; intros; simpl; try reflexivity;
    try solve [rewrite !instantiate_open_tm_rec_commute; try assumption; reflexivity];
    try solve [rewrite IHp1, IHp2; try assumption; reflexivity].
  f_equal. apply IHp; assumption.
Qed.

Lemma instantiate_qualifier_open_commute : forall ps u theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  instantiate_qualifier theta gamma (open_qualifier_tm ps u) =
  open_qualifier_tm (instantiate_qualifier theta gamma ps)
    (instantiate theta gamma u).
Proof.
  intros. apply instantiate_pred_open_rec_commute; assumption.
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

Lemma denotes_refine_iff : forall T ps v,
  denotes (R_Refine T ps) v <->
  value v /\ has_type [] empty v T /\
  qualifier_holds (open_qualifier_tm ps v).
Proof.
  intros. simp denotes. reflexivity.
Qed.

Lemma denotes_func_iff : forall R1 R2 v,
  denotes (R_Func R1 R2) v <->
  value v /\ has_type [] empty v (erase (R_Func R1 R2)) /\
  forall arg,
    denotes R1 arg ->
    locally_closed_tm (tm_app v arg) /\
    halts (tm_app v arg) /\
    forall result,
      multi (tm_app v arg) result ->
      value result ->
      denotes (open_rty_tm R2 arg) result.
Proof.
  intros. simp denotes. reflexivity.
Qed.

Lemma denotes_exists_iff : forall R1 R2 v,
  denotes (R_Exists R1 R2) v <->
  value v /\ has_type [] empty v (erase (R_Exists R1 R2)) /\
  exists witness,
    denotes R1 witness /\ denotes (open_rty_tm R2 witness) v.
Proof.
  intros. simp denotes. reflexivity.
Qed.

Lemma denotes_poly_iff : forall R v,
  denotes (R_Poly R) v <->
  value v /\ has_type [] empty v (erase (R_Poly R)) /\
  forall U,
    wf_ty [] U ->
    locally_closed_tm (tm_tapp v U) /\
    halts (tm_tapp v U) /\
    forall result,
      multi (tm_tapp v U) result ->
      value result ->
      denotes (open_rty_ty R U) result.
Proof.
  intros. simp denotes. reflexivity.
Qed.

Lemma denotes_value : forall R v,
  denotes R v -> value v.
Proof.
  intros R v H.
  destruct R; cbn [denotes] in H; exact (proj1 H).
Qed.

Lemma denotes_refinement_predicates : forall T ps v,
  denotes (R_Refine T ps) v ->
  qualifier_holds (open_qualifier_tm ps v).
Proof.
  intros T ps v H.
  cbn [denotes] in H.
  exact (proj2 (proj2 H)).
Qed.

Lemma instantiate_pred_identity : forall p,
  instantiate_pred identity_type_substitution identity_term_substitution p = p.
Proof.
  induction p; simpl; rewrite ?instantiate_identity, ?IHp1, ?IHp2, ?IHp; reflexivity.
Qed.

Lemma instantiate_qualifier_identity : forall ps,
  instantiate_qualifier identity_type_substitution identity_term_substitution ps = ps.
Proof.
  exact instantiate_pred_identity.
Qed.

Lemma instantiate_rty_identity : forall R,
  instantiate_rty identity_type_substitution identity_term_substitution R = R.
Proof.
  induction R; simpl.
  - rewrite instantiate_ty_identity, instantiate_qualifier_identity. reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR. reflexivity.
Qed.

End SystemFRefinementDenotations.

From Stdlib Require Import Arith.PeanoNat Lists.List Lia ZArith.BinInt.
Module SystemFRefinementSoundness.
Import ListNotations.
Import SystemFRefinement.
Import SystemFRefinementInfrastructure.
Import SystemFRefinementCoreTyping.
Import SystemFRefinementTyping.
Import SystemFRefinementEvaluation.
Import SystemFRefinementDenotations.

Definition related_substitution
    (theta : type_substitution) (gamma : term_substitution)
    (RGamma : rcontext) : Prop :=
  forall x R,
    lookup_rcontext x RGamma = Some R ->
    denotes (instantiate_rty theta gamma R) (gamma x).

Lemma denotes_typing : forall R v,
  denotes R v -> has_type [] empty v (erase R).
Proof.
  intros R v H. destruct R; cbn [denotes] in H; exact (proj1 (proj2 H)).
Qed.

Lemma predicate_multistep_value : forall v u,
  value v -> predicate_multistep v u -> u = v.
Proof.
  intros v u Hv H. induction H.
  - reflexivity.
  - exfalso. eapply value_no_step; eauto.
Qed.

Lemma predicate_multistep_values_equal : forall v1 v2 u,
  value v1 -> value v2 ->
  predicate_multistep v1 u -> predicate_multistep v2 u -> v1 = v2.
Proof.
  intros. pose proof (predicate_multistep_value _ _ H H1).
  pose proof (predicate_multistep_value _ _ H0 H2). congruence.
Qed.

Lemma evals_denotes_of_denotes : forall R v,
  denotes R v -> evals_denotes R v.
Proof.
  intros R v Hden. split.
  - apply value_regular. eapply denotes_value. exact Hden.
  - split.
    + apply halts_value. eapply denotes_value. exact Hden.
    + intros result Hsteps Hvalue.
      assert (Hv : value v) by (eapply denotes_value; exact Hden).
      assert (result = v).
      { exact (value_multi_eq v result Hv Hsteps). }
      subst result. exact Hden.
Qed.

Lemma evals_denotes_from_value : forall R v,
  value v -> evals_denotes R v -> denotes R v.
Proof.
  intros R v Hv [_ [_ Hall]].
  apply (Hall v (multi_refl v) Hv).
Qed.

Lemma core_multi_preservation : forall t v T,
  has_type [] empty t T ->
  multi t v ->
  has_type [] empty v T.
Proof.
  intros t v T Htyped Hsteps. induction Hsteps.
  - exact Htyped.
  - apply IHHsteps. eapply core_preservation; eauto.
Qed.

Lemma lookup_erase_context_inv : forall RGamma x T,
  lookup_context x (erase_context RGamma) = Some T ->
  exists R,
    lookup_rcontext x RGamma = Some R /\ erase R = T.
Proof.
  induction RGamma as [|[y R] RGamma IH]; intros x T Hlookup; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + inversion Hlookup; subst. exists R. split; reflexivity.
    + destruct (IH x T Hlookup) as [S [HS HE]].
      exists S. split; assumption.
Qed.

Lemma related_substitution_typed : forall theta gamma RGamma,
  related_substitution theta gamma RGamma ->
  term_substitution_typed (erase_context RGamma) [] empty theta gamma.
Proof.
  intros theta gamma RGamma Hrel x T Hlookup.
  destruct (lookup_erase_context_inv RGamma x T Hlookup)
    as [R [HR Herase]].
  pose proof (denotes_typing _ _ (Hrel x R HR)) as Htyped.
  rewrite erase_instantiate_rty in Htyped.
  rewrite Herase in Htyped. exact Htyped.
Qed.

Lemma lookup_rcontext_fv : forall RGamma y R x,
  lookup_rcontext y RGamma = Some R ->
  In x (fv_rty R) ->
  In x (fv_rcontext RGamma).
Proof.
  induction RGamma as [|[z S] RGamma IH]; intros y R x Hlookup Hin; simpl in *.
  - discriminate.
  - destruct (Nat.eqb y z) eqn:E.
    + inversion Hlookup; subst. apply in_or_app. left. exact Hin.
    + apply in_or_app. right. eapply IH; eauto.
Qed.

Lemma lookup_rcontext_ftv : forall RGamma y R X,
  lookup_rcontext y RGamma = Some R ->
  In X (ftv_rty R) ->
  In X (ftv_rcontext RGamma).
Proof.
  induction RGamma as [|[z S] RGamma IH]; intros y R X Hlookup Hin; simpl in *.
  - discriminate.
  - destruct (Nat.eqb y z) eqn:E.
    + inversion Hlookup; subst. apply in_or_app. left. exact Hin.
    + apply in_or_app. right. eapply IH; eauto.
Qed.

Lemma related_substitution_update : forall theta gamma RGamma x R v,
  related_substitution theta gamma RGamma ->
  denotes (instantiate_rty theta gamma R) v ->
  ~ In x (fv_rty R) ->
  ~ In x (fv_rcontext RGamma) ->
  related_substitution theta (term_subst_update gamma x v)
    (update_rcontext RGamma x R).
Proof.
  intros theta gamma RGamma x R v Hrel Hden HfreshR HfreshGamma.
  intros y S Hlookup. simpl in Hlookup.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst y. inversion Hlookup; subst S.
    rewrite instantiate_rty_term_update_irrelevant by exact HfreshR.
    unfold term_subst_update. rewrite Nat.eqb_refl.
    exact Hden.
  - apply Nat.eqb_neq in E.
    assert (HlookupS : lookup_rcontext y RGamma = Some S) by exact Hlookup.
    assert (HfreshS : ~ In x (fv_rty S)).
    { intro Hin. apply HfreshGamma. eapply lookup_rcontext_fv; eauto. }
    rewrite instantiate_rty_term_update_irrelevant by exact HfreshS.
    unfold term_subst_update.
    rewrite (proj2 (Nat.eqb_neq x y)) by congruence.
    exact (Hrel y S HlookupS).
Qed.

Lemma related_substitution_type_update : forall theta gamma RGamma X U,
  related_substitution theta gamma RGamma ->
  ~ In X (ftv_rcontext RGamma) ->
  related_substitution (type_subst_update theta X U) gamma RGamma.
Proof.
  intros theta gamma RGamma X U Hrel Hfresh x R Hlookup.
  rewrite instantiate_rty_type_update_irrelevant.
  - exact (Hrel x R Hlookup).
  - intro Hin. apply Hfresh. eapply lookup_rcontext_ftv; eauto.
Qed.

Scheme has_rtype_mut_ind := Induction for has_rtype Sort Prop
with subtype_mut_ind := Induction for subtype Sort Prop.

Combined Scheme refinement_typing_mutind
  from has_rtype_mut_ind, subtype_mut_ind.

Lemma multi_app_left : forall t1 t1' t2,
  multi t1 t1' -> locally_closed_tm t2 ->
  multi (tm_app t1 t2) (tm_app t1' t2).
Proof.
  intros t1 t1' t2 Hsteps Hlc. induction Hsteps.
  - apply multi_refl.
  - eapply multi_step.
    + apply ST_App1; eauto.
    + exact IHHsteps.
Qed.

Lemma multi_app_right : forall v1 t2 t2',
  value v1 -> multi t2 t2' ->
  multi (tm_app v1 t2) (tm_app v1 t2').
Proof.
  intros v1 t2 t2' Hv Hsteps. induction Hsteps.
  - apply multi_refl.
  - eapply multi_step.
    + apply ST_App2; eauto.
    + exact IHHsteps.
Qed.

Lemma multi_tapp : forall t t' U,
  multi t t' -> locally_closed_ty U ->
  multi (tm_tapp t U) (tm_tapp t' U).
Proof.
  intros t t' U Hsteps HU. induction Hsteps.
  - apply multi_refl.
  - eapply multi_step.
    + apply ST_TApp; eauto.
    + exact IHHsteps.
Qed.

Lemma multi_trans : forall t1 t2 t3,
  multi t1 t2 -> multi t2 t3 -> multi t1 t3.
Proof.
  intros t1 t2 t3 H12 H23. induction H12.
  - exact H23.
  - eapply multi_step; eauto.
Qed.

Lemma multi_to_predicate_multistep : forall t u,
  multi t u -> predicate_multistep t u.
Proof.
  intros t u H. induction H.
  - constructor.
  - eapply PMS_Step; eauto.
Qed.

Lemma evals_denotes_intro : forall R t,
  locally_closed_tm t ->
  (value t \/ exists u, t --> u) ->
  (value t -> denotes R t) ->
  (forall u, t --> u -> evals_denotes R u) ->
  evals_denotes R t.
Proof.
  intros R t Hlc Hprogress Hvalue Hnext. split; [exact Hlc|]. split.
  - destruct Hprogress as [Hv|[u Hu]].
    + apply halts_value. exact Hv.
    + destruct (Hnext u Hu) as [_ [[v [Huv Hv]] _]].
      exists v. split; [eapply multi_step; eauto|exact Hv].
  - intros v Hsteps Hv. inversion Hsteps; subst.
    + apply Hvalue. exact Hv.
    + match goal with
      | Hfirst : t --> ?u, Hrest : multi ?u v |- _ =>
          destruct (Hnext u Hfirst) as [_ [_ Hall]];
          exact (Hall v Hrest Hv)
      end.
Qed.

Lemma evals_denotes_result : forall R t v,
  locally_closed_tm t -> multi t v -> denotes R v -> evals_denotes R t.
Proof.
  intros R t v Hlc Hsteps Hden.
  assert (Hv : value v) by (eapply denotes_value; eauto).
  split; [exact Hlc|]. split.
  - exists v. auto.
  - intros w Htw Hw.
    assert (v = w) by (eapply multi_value_unique; eauto).
    subst. assumption.
Qed.

Lemma evals_denotes_map : forall R S t,
  (forall v, denotes R v -> denotes S v) ->
  evals_denotes R t ->
  evals_denotes S t.
Proof.
  intros R S t Hmap [Hlc [Hsn Hall]].
  split; [exact Hlc |]. split; [exact Hsn |].
  intros v Hsteps Hv. apply Hmap. eapply Hall; eauto.
Qed.

Lemma evals_denotes_reduct : forall R t u,
  evals_denotes R t ->
  t --> u ->
  evals_denotes R u.
Proof.
  intros R t u [Hlc [Hsn Hall]] Hstep. split.
  - eapply step_preserves_lc; eauto.
  - split.
    + eapply halts_step; eauto.
    + intros v Hsteps Hv. apply Hall; [|exact Hv].
      eapply multi_step; eauto.
Qed.

Lemma halts_progress : forall t,
  halts t -> value t \/ exists u, t --> u.
Proof.
  intros t [v [Hsteps Hv]]. inversion Hsteps; subst.
  - left. exact Hv.
  - right. eauto.
Qed.

Lemma multi_after_step : forall t u v,
  t --> u -> ~ value t -> multi t v -> value v -> multi u v.
Proof.
  intros t u v Hstep Hnv Hmulti Hv. inversion Hmulti; subst.
  - exfalso. apply Hnv. exact Hv.
  - assert (u = t2) by (eapply step_deterministic; eauto).
    subst. assumption.
Qed.

Lemma evals_denotes_back_step : forall R t u,
  t --> u -> locally_closed_tm t -> evals_denotes R u -> evals_denotes R t.
Proof.
  intros R t u Hstep Hlc [Hlu [Hhalt Hall]].
  split; [exact Hlc|]. split.
  - destruct Hhalt as [v [Huv Hv]]. exists v. split.
    + eapply multi_step; eauto.
    + exact Hv.
  - intros v Htv Hv.
    assert (Hnv : ~ value t).
    { intro Hval. eapply value_no_step; eauto. }
    apply Hall; [|exact Hv].
    eapply multi_after_step; eauto.
Qed.

Lemma evals_denotes_back_multi : forall R t u,
  multi t u -> locally_closed_tm t -> evals_denotes R u -> evals_denotes R t.
Proof.
  intros R t u Hsteps. induction Hsteps; intros Hlc Hden.
  - exact Hden.
  - apply evals_denotes_back_step with (u := t2).
    + exact H.
    + exact Hlc.
    + apply IHHsteps.
      * eapply step_preserves_lc; eauto.
      * exact Hden.
Qed.

Lemma multi_div_left : forall t1 t1' t2,
  multi t1 t1' -> locally_closed_tm t2 ->
  multi (tm_div t1 t2) (tm_div t1' t2).
Proof.
  intros t1 t1' t2 H Hlc. induction H; eauto using multi, step.
Qed.

Lemma multi_div_right : forall v t2 t2',
  value v -> multi t2 t2' ->
  multi (tm_div v t2) (tm_div v t2').
Proof.
  intros v t2 t2' Hv H. induction H; eauto using multi, step.
Qed.

Lemma value_int_canonical : forall v,
  value v -> has_type [] empty v Ty_Int -> exists n, v = tm_int n.
Proof.
  intros v Hv Ht. inversion Hv; subst; inversion Ht; eauto.
Qed.

Lemma denotes_nonzero_integer : forall v,
  denotes (R_Refine Ty_Int (Pred_Ne (tm_bvar 0) (tm_int 0%Z))) v ->
  exists n, v = tm_int n /\ n <> 0%Z.
Proof.
  intros v Hden.
  pose proof (denotes_typing _ _ Hden) as Htyped.
  pose proof (denotes_value _ _ Hden) as Hv.
  destruct (value_int_canonical v Hv Htyped) as [n ->].
  exists n. split; [reflexivity|].
  pose proof (denotes_refinement_predicates Ty_Int
    (Pred_Ne (tm_bvar 0) (tm_int 0%Z)) (tm_int n) Hden) as Hp.
  cbn [open_qualifier_tm open_pred_tm_rec open_tm_rec] in Hp.
  unfold qualifier_holds, predicate_holds, interpret_qualifier,
    operational_atoms in Hp. simpl in Hp.
  intro E. subst n. apply Hp.
  exists (tm_int 0%Z). split; [constructor|]. split; [constructor|constructor].
Qed.

Lemma multi_arith_left : forall op t1 t1' t2,
  multi t1 t1' -> locally_closed_tm t2 ->
  multi (tm_arith op t1 t2) (tm_arith op t1' t2).
Proof. intros op t1 t1' t2 H Hlc. induction H; eauto using multi, step. Qed.

Lemma multi_arith_right : forall op v t2 t2',
  value v -> multi t2 t2' ->
  multi (tm_arith op v t2) (tm_arith op v t2').
Proof. intros op v t2 t2' Hv H. induction H; eauto using multi, step. Qed.

Lemma instantiated_refinement_typing_erases : forall Delta RGamma t R theta gamma,
  has_rtype Delta RGamma t R ->
  context_wf Delta (erase_context RGamma) ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  type_substitution_wf Delta [] theta ->
  related_substitution theta gamma RGamma ->
  has_type [] empty (instantiate theta gamma t)
    (erase (instantiate_rty theta gamma R)).
Proof.
  intros Delta RGamma t R theta gamma Htyped Hctx Htheta Hgamma
    HthetaWf Hrelated.
  pose proof (refinement_typing_erases _ _ _ _ Htyped) as Herased.
  pose proof (has_type_instantiate Delta (erase_context RGamma) t (erase R)
    Herased Hctx [] empty theta gamma Htheta Hgamma HthetaWf
    (related_substitution_typed theta gamma RGamma Hrelated)) as Hinst.
  rewrite erase_instantiate_rty. exact Hinst.
Qed.

Lemma entails_interpreted : forall Delta RGamma p q theta gamma,
  entails Delta RGamma p q ->
  type_substitution_closed theta -> term_substitution_closed gamma ->
  related_substitution theta gamma RGamma ->
  qualifier_holds (instantiate_qualifier theta gamma p) ->
  qualifier_holds (instantiate_qualifier theta gamma q).
Proof.
  intros Delta RGamma p q theta gamma Hent.
  induction Hent; intros Htheta Hgamma Hrel Hholds;
    unfold qualifier_holds, predicate_holds in *; simpl in *;
    try tauto; try eauto.
  - destruct (Hrel x (R_Refine T p) H) as [Hv [Ht Hpred]].
    change (qualifier_holds
      (open_qualifier_tm (instantiate_qualifier theta gamma p) (gamma x))) in Hpred.
    pose proof (instantiate_qualifier_open_commute p (tm_fvar x) theta gamma
      Htheta Hgamma (lc_tm_fvar 0 0 x)) as E.
    simpl in E. rewrite <- E in Hpred.
    exact Hpred.
Qed.

Definition typing_semantics
    (Delta : ty_context) (RGamma : rcontext) (t : tm) (R : rty) : Prop :=
  context_wf Delta (erase_context RGamma) ->
  forall theta gamma,
    type_substitution_closed theta ->
    term_substitution_closed gamma ->
    type_substitution_wf Delta [] theta ->
    related_substitution theta gamma RGamma ->
    evals_denotes (instantiate_rty theta gamma R)
      (instantiate theta gamma t).

Definition subtype_semantics
    (Delta : ty_context) (RGamma : rcontext) (R S : rty) : Prop :=
  wf_ty Delta (erase S) ->
  context_wf Delta (erase_context RGamma) ->
  forall theta gamma,
    type_substitution_closed theta ->
    term_substitution_closed gamma ->
    type_substitution_wf Delta [] theta ->
    related_substitution theta gamma RGamma ->
    forall v,
      denotes (instantiate_rty theta gamma R) v ->
      denotes (instantiate_rty theta gamma S) v.

Theorem fundamental_and_subtyping :
  (forall Delta RGamma t R (H : has_rtype Delta RGamma t R),
    typing_semantics Delta RGamma t R) /\
  (forall Delta RGamma R S (H : subtype Delta RGamma R S),
    subtype_semantics Delta RGamma R S).
Proof.
  apply refinement_typing_mutind; unfold typing_semantics, subtype_semantics;
    intros; try assumption.
  - simpl. apply evals_denotes_of_denotes. exact (H3 x R e).
  -
    pose proof (instantiated_refinement_typing_erases Delta RGamma
      (tm_abs (erase R1) body) (R_Func R1 R2) theta gamma
      (RT_Abs L Delta RGamma R1 body R2 w h) H0 H1 H2 H3 H4) as Hcore.
    apply evals_denotes_of_denotes.
    apply (proj2 (denotes_func_iff _ _ _)).
    split.
    + apply v_abs. eapply typing_lc. exact Hcore.
    + split; [exact Hcore|].
      intros arg Harg.
      set (x := fresh (L ++ fv_rty R1 ++ fv_rty R2 ++ fv_rcontext RGamma ++
        dom_context (erase_context RGamma) ++ fv_tm body)).
      assert (Hxall : ~ In x (L ++ fv_rty R1 ++ fv_rty R2 ++ fv_rcontext RGamma ++
        dom_context (erase_context RGamma) ++ fv_tm body)).
      { subst x. apply fresh_notin. }
      repeat rewrite in_app_iff in Hxall.
      assert (HxL : ~ In x L) by intuition.
      assert (HxR1 : ~ In x (fv_rty R1)) by intuition.
      assert (HxR2 : ~ In x (fv_rty R2)) by intuition.
      assert (HxG : ~ In x (fv_rcontext RGamma)) by intuition.
      assert (Hxdom : ~ In x (dom_context (erase_context RGamma))) by intuition.
      assert (Hxbody : ~ In x (fv_tm body)) by intuition.
      assert (Harglc : locally_closed_tm arg).
      { apply value_regular. eapply denotes_value. exact Harg. }
      assert (Hctxx : context_wf Delta (erase_context (update_rcontext RGamma x R1))).
      { simpl. eapply context_wf_update; [exact H0|].
        exact (wf_rty_erases Delta RGamma R1 w). }
      set (gamma' := term_subst_update gamma x arg).
      assert (Hgamma' : term_substitution_closed gamma').
      { intros y. unfold gamma', term_subst_update.
        destruct (Nat.eqb x y); [exact Harglc|apply H2]. }
      assert (Hrelx : related_substitution theta gamma'
        (update_rcontext RGamma x R1)).
      { eapply related_substitution_update; eauto. }
      pose proof (H x HxL Hctxx theta gamma' H1 Hgamma' H3 Hrelx) as Hb.
      assert (Hbody : evals_denotes
        (open_rty_tm (instantiate_rty theta gamma R2) arg)
        (open_tm (instantiate theta gamma body) arg)).
      { replace (open_rty_tm (instantiate_rty theta gamma R2) arg)
          with (instantiate_rty theta gamma'
            (open_rty_tm R2 (tm_fvar x))).
        2: { unfold gamma'. rewrite instantiate_rty_open_tm; try assumption.
          reflexivity. }
        replace (open_tm (instantiate theta gamma body) arg)
          with (instantiate theta gamma' (open_tm body (tm_fvar x))).
        2: { rewrite (instantiate_open_tm_commute body (tm_fvar x)
              theta gamma' H1 Hgamma' (lc_tm_fvar 0 0 x)).
          unfold gamma'. rewrite instantiate_term_update_irrelevant by exact Hxbody.
          simpl. unfold term_subst_update. rewrite Nat.eqb_refl. reflexivity. }
        exact Hb. }
      split.
      * apply lc_tm_app.
        -- eapply typing_lc. exact Hcore.
        -- exact Harglc.
      * split.
        -- destruct Hbody as [_ [Hhalt _]].
           destruct Hhalt as [res [Hsteps Hres]].
           exists res. split.
           ++ eapply multi_step.
              ** apply ST_AppAbs; [eapply typing_lc; exact Hcore|].
                 eapply denotes_value; exact Harg.
              ** exact Hsteps.
           ++ exact Hres.
        -- intros result Hsteps Hresult.
           assert (Happstep :
             tm_app (instantiate theta gamma (tm_abs (erase R1) body)) arg -->
             open_tm (instantiate theta gamma body) arg).
           { apply ST_AppAbs; [eapply typing_lc; exact Hcore|].
             eapply denotes_value; exact Harg. }
           assert (Happnv : ~ value
             (tm_app (instantiate theta gamma (tm_abs (erase R1) body)) arg)).
           { intro Hv. inversion Hv. }
           pose proof (multi_after_step _ _ _ Happstep Happnv Hsteps Hresult) as Hrest.
           destruct Hbody as [_ [_ Hall]]. eapply Hall; eauto.
  -
    destruct (H H1 theta gamma H2 H3 H4 H5) as [Hlc1 [Hhalt1 Hall1]].
    destruct (H0 H1 theta gamma H2 H3 H4 H5) as [Hlc2 [Hhalt2 Hall2]].
    destruct Hhalt1 as [f [Hfsteps Hfv]].
    destruct Hhalt2 as [arg [Hargsteps Hargval]].
    pose proof (Hall1 f Hfsteps Hfv) as Hfden.
    pose proof (Hall2 arg Hargsteps Hargval) as Hargden.
    change (denotes (R_Func (instantiate_rty theta gamma R1)
      (instantiate_rty theta gamma R2)) f) in Hfden.
    apply (proj1 (denotes_func_iff _ _ _)) in Hfden.
    destruct Hfden as [Hfv' [Hftyped Hfbehavior]].
    assert (HappDen : evals_denotes
      (open_rty_tm (instantiate_rty theta gamma R2) arg)
      (tm_app f arg)).
    { destruct (Hfbehavior arg Hargden) as [Happlc [Happhalt Hallapp]].
      split; [exact Happlc|]. split; [exact Happhalt|].
      intros result Hsteps Hresult. eapply Hallapp; eauto. }
    assert (HexistDen : evals_denotes
      (R_Exists (instantiate_rty theta gamma R1)
        (instantiate_rty theta gamma R2)) (tm_app f arg)).
    { eapply evals_denotes_map.
      - intros result Hden.
        apply (proj2 (denotes_exists_iff _ _ _)).
        split.
        + eapply denotes_value. exact Hden.
        + split.
          * pose proof (denotes_typing
              (open_rty_tm (instantiate_rty theta gamma R2) arg) result Hden) as Hty.
            rewrite erase_open_rty_tm in Hty. exact Hty.
          * exists arg. split; assumption.
      - exact HappDen. }
    eapply evals_denotes_back_multi; [| |exact HexistDen].
    + eapply multi_trans.
      * apply multi_app_left; [exact Hfsteps|exact Hlc2].
      * apply multi_app_right; assumption.
    + apply lc_tm_app; assumption.
  -
    pose proof (instantiated_refinement_typing_erases Delta RGamma
      (tm_tabs body) (R_Poly R) theta gamma
      (RT_TAbs L Delta RGamma body R h) H0 H1 H2 H3 H4) as Hcore.
    apply evals_denotes_of_denotes.
    apply (proj2 (denotes_poly_iff _ _)).
    split.
    + apply v_tabs. eapply typing_lc. exact Hcore.
    + split; [exact Hcore|].
      intros U HU.
      set (X := fresh (L ++ Delta ++ ftv_rty R ++ ftv_rcontext RGamma ++ ftv_tm body)).
      assert (HXall : ~ In X (L ++ Delta ++ ftv_rty R ++ ftv_rcontext RGamma ++ ftv_tm body)).
      { subst X. apply fresh_notin. }
      repeat rewrite in_app_iff in HXall.
      assert (HXL : ~ In X L) by intuition.
      assert (HXDelta : ~ In X Delta) by intuition.
      assert (HXR : ~ In X (ftv_rty R)) by intuition.
      assert (HXG : ~ In X (ftv_rcontext RGamma)) by intuition.
      assert (HXbody : ~ In X (ftv_tm body)) by intuition.
      set (theta' := type_subst_update theta X U).
      assert (HUlc : locally_closed_ty U) by (eapply wf_ty_lc; eauto).
      assert (Htheta' : type_substitution_closed theta').
      { unfold theta'. apply type_subst_update_closed; assumption. }
      assert (Hwf' : type_substitution_wf (X :: Delta) [] theta').
      { intros Y HY. simpl in HY. destruct HY as [E|HY].
        - subst Y. unfold theta', type_subst_update. rewrite Nat.eqb_refl. exact HU.
        - unfold theta', type_subst_update.
          assert (Hneq : X <> Y) by (intro E; subst; contradiction).
          rewrite (proj2 (Nat.eqb_neq X Y)) by exact Hneq. apply H3. exact HY. }
      assert (Hctx' : context_wf (X :: Delta) (erase_context RGamma)).
      { eapply context_wf_weaken_type; [exact H0|].
        intros Y HY. right. exact HY. }
      assert (Hrel' : related_substitution theta' gamma RGamma).
      { unfold theta'. eapply related_substitution_type_update; eauto. }
      pose proof (H X HXL Hctx' theta' gamma Htheta' H2 Hwf' Hrel') as Hb.
      assert (Hbody : evals_denotes
        (open_rty_ty (instantiate_rty theta gamma R) U)
        (open_tm_ty (instantiate theta gamma body) U)).
      { replace (open_rty_ty (instantiate_rty theta gamma R) U)
          with (instantiate_rty theta' gamma (open_rty_ty R (Ty_FVar X))).
        2: { unfold theta'. rewrite instantiate_rty_open_ty; try assumption.
          reflexivity. }
        replace (open_tm_ty (instantiate theta gamma body) U)
          with (instantiate theta' gamma (open_tm_ty body (Ty_FVar X))).
        2: { rewrite (instantiate_open_ty_tm_commute body (Ty_FVar X)
              theta' gamma Htheta' H2 (lc_ty_fvar 0 X)).
          unfold theta'. rewrite instantiate_term_type_update_irrelevant by exact HXbody.
          unfold type_subst_update. simpl. rewrite Nat.eqb_refl. reflexivity. }
        exact Hb. }
      split.
      * apply lc_tm_tapp.
        -- eapply typing_lc. exact Hcore.
        -- exact HUlc.
      * split.
        -- destruct Hbody as [_ [Hhalt _]]. destruct Hhalt as [res [Hsteps Hres]].
           exists res. split.
           ++ eapply multi_step.
              ** apply ST_TAppTabs; [eapply typing_lc; exact Hcore|exact HUlc].
              ** exact Hsteps.
           ++ exact Hres.
        -- intros result Hsteps Hresult.
           assert (Hstep :
             tm_tapp (instantiate theta gamma (tm_tabs body)) U -->
             open_tm_ty (instantiate theta gamma body) U).
           { apply ST_TAppTabs; [eapply typing_lc; exact Hcore|exact HUlc]. }
           assert (Hnv : ~ value (tm_tapp (instantiate theta gamma (tm_tabs body)) U)).
           { intro Hv. inversion Hv. }
           pose proof (multi_after_step _ _ _ Hstep Hnv Hsteps Hresult) as Hrest.
           destruct Hbody as [_ [_ Hall]]. eapply Hall; eauto.
  -
    destruct (H H0 theta gamma H1 H2 H3 H4) as [Hlc [Hhalt Hall]].
    destruct Hhalt as [f [Hfsteps Hfv]].
    pose proof (Hall f Hfsteps Hfv) as Hfden.
    change (denotes (R_Poly (instantiate_rty theta gamma R)) f) in Hfden.
    apply (proj1 (denotes_poly_iff _ _)) in Hfden.
    destruct Hfden as [Hfv' [Hftyped Hbehavior]].
    set (U' := instantiate_ty theta U).
    assert (HU' : wf_ty [] U').
    { unfold U'. eapply wf_ty_instantiate; [exact w|exact H3]. }
    destruct (Hbehavior U' HU') as [Htapplc [Htapphalt Htappall]].
    assert (Htap : evals_denotes
      (open_rty_ty (instantiate_rty theta gamma R) U')
      (tm_tapp f U')).
    { split; [exact Htapplc|]. split; [exact Htapphalt|exact Htappall]. }
    assert (Hprefix : multi
      (tm_tapp (instantiate theta gamma t) U') (tm_tapp f U')).
    { apply multi_tapp; [exact Hfsteps|].
      unfold U'. eapply wf_ty_lc; eauto. }
    assert (Htypeeq : instantiate_rty theta gamma (open_rty_ty R U) =
      open_rty_ty (instantiate_rty theta gamma R) U').
    { unfold U'. apply instantiate_rty_open_ty_commute_top; try assumption.
      eapply wf_ty_lc; eauto. }
    rewrite Htypeeq.
    eapply evals_denotes_back_multi; [exact Hprefix| |exact Htap].
    apply lc_tm_tapp; [exact Hlc|]. unfold U'. eapply wf_ty_lc; eauto.
  -
    simpl. apply evals_denotes_of_denotes.
    apply (proj2 (denotes_refine_iff Ty_Int
      (Pred_Eq (tm_bvar 0) (tm_int n)) (tm_int n))).
    split; [constructor|]. split; [apply T_Int|].
    unfold qualifier_holds, predicate_holds, interpret_qualifier, operational_atoms.
    simpl. exists (tm_int n). split; [constructor|]. split; [constructor|constructor].
  -
    destruct (H H1 theta gamma H2 H3 H4 H5) as [Hlc1 [Hhalt1 Hall1]].
    destruct (H0 H1 theta gamma H2 H3 H4 H5) as [Hlc2 [Hhalt2 Hall2]].
    destruct Hhalt1 as [v1 [Hsteps1 Hv1]].
    destruct Hhalt2 as [v2 [Hsteps2 Hv2]].
    pose proof (Hall1 v1 Hsteps1 Hv1) as Hd1.
    pose proof (Hall2 v2 Hsteps2 Hv2) as Hd2.
    change (denotes (R_Refine Ty_Int Pred_True) v1) in Hd1.
    change (denotes (R_Refine Ty_Int
      (Pred_Ne (tm_bvar 0) (tm_int 0%Z))) v2) in Hd2.
    destruct (value_int_canonical v1 Hv1 (denotes_typing _ _ Hd1)) as [n ->].
    destruct (denotes_nonzero_integer v2 Hd2) as [m [-> Hm]].
    assert (Hsteps : multi (tm_div (instantiate theta gamma t1)
      (instantiate theta gamma t2)) (tm_int (Z.div n m))).
    { eapply multi_trans.
      - eapply multi_trans.
        + eapply multi_div_left; [exact Hsteps1|exact Hlc2].
        + eapply multi_div_right; [constructor|exact Hsteps2].
      - eapply multi_step. apply ST_DivInt. exact Hm. apply multi_refl. }
    assert (Hden : denotes (R_Refine Ty_Int Pred_True) (tm_int (Z.div n m))).
    { apply (proj2 (denotes_refine_iff Ty_Int Pred_True _)).
      split; [constructor|]. split; [apply T_Int|]. simpl. exact I. }
    change (evals_denotes (R_Refine Ty_Int Pred_True)
      (tm_div (instantiate theta gamma t1) (instantiate theta gamma t2))).
    eapply evals_denotes_result; [|exact Hsteps|exact Hden].
    apply lc_tm_div; assumption.
  -
    destruct (H H1 theta gamma H2 H3 H4 H5) as [Hlc1 [Hhalt1 Hall1]].
    destruct (H0 H1 theta gamma H2 H3 H4 H5) as [Hlc2 [Hhalt2 Hall2]].
    destruct Hhalt1 as [v1 [Hsteps1 Hv1]].
    destruct Hhalt2 as [v2 [Hsteps2 Hv2]].
    pose proof (Hall1 v1 Hsteps1 Hv1) as Hd1.
    pose proof (Hall2 v2 Hsteps2 Hv2) as Hd2.
    change (denotes (R_Refine Ty_Int Pred_True) v1) in Hd1.
    change (denotes (R_Refine Ty_Int Pred_True) v2) in Hd2.
    destruct (value_int_canonical v1 Hv1 (denotes_typing _ _ Hd1)) as [n ->].
    destruct (value_int_canonical v2 Hv2 (denotes_typing _ _ Hd2)) as [m ->].
    set (r := eval_integer_operator op n m).
    assert (Hsteps : multi (tm_arith op (instantiate theta gamma t1)
      (instantiate theta gamma t2)) (tm_int r)).
    { eapply multi_trans.
      - eapply multi_trans.
        + eapply multi_arith_left; [exact Hsteps1|exact Hlc2].
        + eapply multi_arith_right; [constructor|exact Hsteps2].
      - eapply multi_step. apply ST_ArithInt. apply multi_refl. }
    assert (Hden : denotes
      (R_Refine Ty_Int
        (Pred_Eq (tm_bvar 0) (tm_arith op (instantiate theta gamma t1)
          (instantiate theta gamma t2)))) (tm_int r)).
    { apply (proj2 (denotes_refine_iff Ty_Int
        (Pred_Eq (tm_bvar 0) (tm_arith op (instantiate theta gamma t1)
          (instantiate theta gamma t2))) (tm_int r))).
      split; [constructor|]. split; [apply T_Int|].
      unfold qualifier_holds, predicate_holds, interpret_qualifier,
        operational_atoms. simpl.
      rewrite (open_tm_rec_lc_at (instantiate theta gamma t1) 0 0
        (tm_int r) Hlc1).
      rewrite (open_tm_rec_lc_at (instantiate theta gamma t2) 0 0
        (tm_int r) Hlc2).
      exists (tm_int r). split; [constructor|]. split.
      - eapply multi_to_predicate_multistep. exact Hsteps.
      - constructor. }
    change (evals_denotes
      (R_Refine Ty_Int
        (Pred_Eq (tm_bvar 0) (tm_arith op (instantiate theta gamma t1)
          (instantiate theta gamma t2))))
      (tm_arith op (instantiate theta gamma t1) (instantiate theta gamma t2))).
    eapply evals_denotes_result; [|exact Hsteps|exact Hden].
    apply lc_tm_arith; assumption.
  -
    apply evals_denotes_of_denotes.
    apply (proj2 (denotes_refine_iff (instantiate_ty theta T)
      (instantiate_qualifier theta gamma ps) (instantiate theta gamma v))).
    assert (Htyped : has_type [] empty (instantiate theta gamma v)
      (instantiate_ty theta T)).
    { exact (has_type_instantiate Delta (erase_context RGamma) v T h H
        [] empty theta gamma H0 H1 H2
        (related_substitution_typed theta gamma RGamma H3)). }
    split.
    + exact (instantiate_value v theta gamma v0 H0 H1).
    + split; [exact Htyped|].
      pose proof (instantiate_qualifier_holds
        (open_qualifier_tm ps v) theta gamma p q H0 H1) as Hholds.
      pose proof (instantiate_qualifier_open_commute ps v theta gamma
        H0 H1 (value_regular v v0)) as E.
      rewrite E in Hholds. exact Hholds.
  - eapply evals_denotes_map.
    + intros v Hv. eapply H0; try eassumption.
      apply wf_rty_erases with (RGamma := RGamma). exact w.
    + apply H; assumption.
  -
    apply (proj2 (denotes_refine_iff (instantiate_ty theta T)
      (instantiate_qualifier theta gamma qs) v)).
    apply (proj1 (denotes_refine_iff (instantiate_ty theta T)
      (instantiate_qualifier theta gamma ps) v)) in H5.
    destruct H5 as [Hv [Htyped Hpred]].
    split; [exact Hv|]. split; [exact Htyped|].
    set (x := fresh (L ++ fv_rty (R_Refine T ps) ++
      fv_rty (R_Refine T qs) ++ fv_rcontext RGamma)).
    assert (Hxall : ~ In x (L ++ fv_rty (R_Refine T ps) ++
      fv_rty (R_Refine T qs) ++ fv_rcontext RGamma)).
    { subst x. apply fresh_notin. }
    repeat rewrite in_app_iff in Hxall.
    assert (HxL : ~ In x L) by intuition.
    assert (Hxps : ~ In x (fv_rty (R_Refine T ps))) by intuition.
    assert (Hxqs : ~ In x (fv_rty (R_Refine T qs))) by intuition.
    assert (HxG : ~ In x (fv_rcontext RGamma)) by intuition.
    assert (Htrue : denotes (instantiate_rty theta gamma
      (R_Refine T Pred_True)) v).
    { apply (proj2 (denotes_refine_iff (instantiate_ty theta T)
        Pred_True v)).
      split; [exact Hv|]. split; [exact Htyped|exact I]. }
    set (gamma' := term_subst_update gamma x v).
    assert (Hgamma' : term_substitution_closed gamma').
    { intros y. unfold gamma', term_subst_update.
      destruct (Nat.eqb x y); [eapply value_regular; exact Hv|apply H2]. }
    assert (Hrel' : related_substitution theta gamma'
      (update_rcontext RGamma x (R_Refine T Pred_True))).
    { eapply related_substitution_update with
        (x := x) (R := R_Refine T Pred_True) (v := v).
      - exact H4.
      - exact Htrue.
      - simpl. tauto.
      - exact HxG. }
    assert (Hps' : instantiate_qualifier theta gamma'
      (open_qualifier_tm ps (tm_fvar x)) =
      open_qualifier_tm (instantiate_qualifier theta gamma ps) v).
    { rewrite (instantiate_qualifier_open_commute ps (tm_fvar x) theta gamma'
        H1 Hgamma' (lc_tm_fvar 0 0 x)).
      unfold gamma'.
      pose proof (instantiate_rty_term_update_irrelevant
        (R_Refine T ps) theta gamma x v Hxps) as E.
      inversion E. simpl. unfold term_subst_update. rewrite Nat.eqb_refl. reflexivity. }
    assert (Hqs' : instantiate_qualifier theta gamma'
      (open_qualifier_tm qs (tm_fvar x)) =
      open_qualifier_tm (instantiate_qualifier theta gamma qs) v).
    { rewrite (instantiate_qualifier_open_commute qs (tm_fvar x) theta gamma'
        H1 Hgamma' (lc_tm_fvar 0 0 x)).
      unfold gamma'.
      pose proof (instantiate_rty_term_update_irrelevant
        (R_Refine T qs) theta gamma x v Hxqs) as E.
      inversion E. simpl. unfold term_subst_update. rewrite Nat.eqb_refl. reflexivity. }
    assert (Hprem : qualifier_holds (instantiate_qualifier theta gamma'
      (open_qualifier_tm ps (tm_fvar x)))).
    { rewrite Hps'. exact Hpred. }
    assert (Hout : qualifier_holds (instantiate_qualifier theta gamma'
      (open_qualifier_tm qs (tm_fvar x)))).
    { eapply entails_interpreted; eauto. }
    rewrite Hqs' in Hout. exact Hout.
  -
    pose proof (subtype_erases Delta RGamma (R_Func R1 R2) (R_Func S1 S2)
      (S_Func L Delta RGamma R1 R2 S1 S2 s s0)) as Ewhole.
    apply (proj1 (denotes_func_iff _ _ _)) in H7.
    destruct H7 as [Hv [Htyped Hbehavior]].
    apply (proj2 (denotes_func_iff _ _ _)).
    split; [exact Hv|].
    split.
    + change (has_type [] empty v
        (Ty_Arrow (erase (instantiate_rty theta gamma S1))
          (erase (instantiate_rty theta gamma S2)))).
      change (has_type [] empty v
        (Ty_Arrow (erase (instantiate_rty theta gamma R1))
          (erase (instantiate_rty theta gamma R2)))) in Htyped.
      rewrite !erase_instantiate_rty.
      rewrite !erase_instantiate_rty in Htyped.
      pose proof (f_equal (instantiate_ty theta) Ewhole) as Ei.
      simpl in Ei. rewrite <- Ei. exact Htyped.
    + intros arg Harg.
      assert (Hwfr1 : wf_ty Delta (erase R1)).
      { inversion H1; subst.
        rewrite <- (subtype_erases Delta RGamma S1 R1 s). assumption. }
      pose proof (H Hwfr1 H2 theta gamma H3 H4 H5 H6 arg Harg) as HargR.
      destruct (Hbehavior arg HargR) as [Happlc [Happhalt Hallapp]].
      set (x := fresh (L ++ fv_rty S1 ++ fv_rty R2 ++ fv_rty S2 ++
        fv_rcontext RGamma)).
      assert (Hxall : ~ In x (L ++ fv_rty S1 ++ fv_rty R2 ++ fv_rty S2 ++
        fv_rcontext RGamma)).
      { subst x. apply fresh_notin. }
      repeat rewrite in_app_iff in Hxall.
      assert (HxL : ~ In x L) by intuition.
      assert (HxS1 : ~ In x (fv_rty S1)) by intuition.
      assert (HxR2 : ~ In x (fv_rty R2)) by intuition.
      assert (HxS2 : ~ In x (fv_rty S2)) by intuition.
      assert (HxG : ~ In x (fv_rcontext RGamma)) by intuition.
      set (gamma' := term_subst_update gamma x arg).
      assert (Harglc : locally_closed_tm arg).
      { eapply value_regular. exact (denotes_value _ _ Harg). }
      assert (Hgamma' : term_substitution_closed gamma').
      { intros y. unfold gamma', term_subst_update.
        destruct (Nat.eqb x y); [exact Harglc|apply H4]. }
      assert (Hctxx : context_wf Delta (erase_context (update_rcontext RGamma x S1))).
      { simpl. eapply context_wf_update; [exact H2|].
        inversion H1; assumption. }
      assert (Hrelx : related_substitution theta gamma'
        (update_rcontext RGamma x S1)).
      { eapply related_substitution_update with (x := x) (R := S1) (v := arg);
          eauto. }
      assert (HwfS2x : wf_ty Delta (erase (open_rty_tm S2 (tm_fvar x)))).
      { rewrite erase_open_rty_tm. inversion H1; assumption. }
      assert (Hbodyden : forall result, multi (tm_app v arg) result -> value result ->
        denotes (instantiate_rty theta gamma'
          (open_rty_tm R2 (tm_fvar x))) result).
      { intros result Hresult Hresultv.
        assert (Heqsrc : instantiate_rty theta gamma'
          (open_rty_tm R2 (tm_fvar x)) =
          open_rty_tm (instantiate_rty theta gamma R2) arg).
        { unfold gamma'. exact (instantiate_rty_open_tm R2 theta gamma x arg
            HxR2 H3 H4 Harglc). }
        rewrite Heqsrc. apply Hallapp; assumption. }
      pose proof (H0 x HxL HwfS2x Hctxx theta gamma' H3 Hgamma' H5 Hrelx)
        as Hcod.
      split; [exact Happlc|]. split; [exact Happhalt|].
      intros result Hresult Hresultv.
      assert (Hsource : denotes (instantiate_rty theta gamma'
        (open_rty_tm R2 (tm_fvar x))) result).
      { apply Hbodyden; assumption. }
      assert (Hetgt : instantiate_rty theta gamma'
        (open_rty_tm S2 (tm_fvar x)) =
        open_rty_tm (instantiate_rty theta gamma S2) arg).
      { unfold gamma'. apply instantiate_rty_open_tm; assumption. }
      pose proof (Hcod result Hsource) as Hout.
      rewrite Hetgt in Hout. exact Hout.
  -
    pose proof (H H2 theta gamma H3 H4 H5 H6) as HwitEval.
    assert (Hwit : denotes (instantiate_rty theta gamma R1)
      (instantiate theta gamma v)).
    { apply evals_denotes_from_value.
      - exact (instantiate_value v theta gamma v0 H3 H4).
      - exact HwitEval. }
    assert (Hwfr2 : wf_ty Delta (erase (open_rty_tm R2 v))).
    { rewrite erase_open_rty_tm. exact H1. }
    pose proof (H0 Hwfr2 H2 theta gamma H3 H4 H5 H6 v1 H7) as Hout.
    apply (proj2 (denotes_exists_iff
      (instantiate_rty theta gamma R1) (instantiate_rty theta gamma R2) v1)).
    split; [eapply denotes_value; exact H7|]. split.
    + pose proof (denotes_typing _ _ Hout) as Hty.
      rewrite !erase_instantiate_rty in Hty.
      rewrite erase_open_rty_tm in Hty.
      simpl. rewrite erase_instantiate_rty. exact Hty.
    + exists (instantiate theta gamma v). split; [exact Hwit|].
      rewrite (instantiate_rty_open_tm_commute_top R2 v theta gamma
        H3 H4 (value_regular v v0)) in Hout.
      exact Hout.
  -
    change (denotes (R_Exists (instantiate_rty theta gamma R1)
      (instantiate_rty theta gamma R2)) v) in H6.
    apply (proj1 (denotes_exists_iff _ _ _)) in H6.
    destruct H6 as [Hv [Htyped [witness [Hwitness Hbody]]]].
    set (x := fresh (L ++ fv_rty R1 ++ fv_rty R2 ++ fv_rty S ++
      fv_rcontext RGamma)).
    assert (Hxall : ~ In x (L ++ fv_rty R1 ++ fv_rty R2 ++ fv_rty S ++
      fv_rcontext RGamma)).
    { subst x. apply fresh_notin. }
    repeat rewrite in_app_iff in Hxall.
    assert (HxL : ~ In x L) by intuition.
    assert (HxR1 : ~ In x (fv_rty R1)) by intuition.
    assert (HxR2 : ~ In x (fv_rty R2)) by intuition.
    assert (HxS : ~ In x (fv_rty S)) by intuition.
    assert (HxG : ~ In x (fv_rcontext RGamma)) by intuition.
    set (gamma' := term_subst_update gamma x witness).
    assert (Hwitnesslc : locally_closed_tm witness).
    { eapply value_regular. eapply denotes_value. exact Hwitness. }
    assert (Hgamma' : term_substitution_closed gamma').
    { intros y. unfold gamma', term_subst_update.
      destruct (Nat.eqb x y); [exact Hwitnesslc|apply H3]. }
    assert (Hctxx : context_wf Delta (erase_context (update_rcontext RGamma x R1))).
    { simpl. eapply context_wf_update; [exact H1|].
      exact (wf_rty_erases Delta RGamma R1 w). }
    assert (Hrelx : related_substitution theta gamma'
      (update_rcontext RGamma x R1)).
    { eapply related_substitution_update with (x := x) (R := R1) (v := witness);
        eauto. }
    assert (Hbody' : denotes (instantiate_rty theta gamma'
      (open_rty_tm R2 (tm_fvar x))) v).
    { unfold gamma'. rewrite (instantiate_rty_open_tm R2 theta gamma x witness
        HxR2 H2 H3 Hwitnesslc). exact Hbody. }
    pose proof (H x HxL H0 Hctxx theta gamma' H2 Hgamma' H4 Hrelx v Hbody') as Hout.
    unfold gamma' in Hout.
    rewrite instantiate_rty_term_update_irrelevant in Hout by exact HxS.
    exact Hout.
  -
    pose proof (subtype_erases Delta RGamma (R_Poly R) (R_Poly S)
      (S_Poly L Delta RGamma R S s)) as Ewhole.
    change (denotes (R_Poly (instantiate_rty theta gamma R)) v) in H6.
    apply (proj1 (denotes_poly_iff _ _)) in H6.
    destruct H6 as [Hv [Htyped Hbehavior]].
    apply (proj2 (denotes_poly_iff _ _)).
    split; [exact Hv|]. split.
    + change (has_type [] empty v (Ty_All (erase (instantiate_rty theta gamma S)))).
      change (has_type [] empty v (Ty_All (erase (instantiate_rty theta gamma R)))) in Htyped.
      rewrite !erase_instantiate_rty.
      rewrite !erase_instantiate_rty in Htyped.
      pose proof (f_equal (instantiate_ty theta) Ewhole) as Ei.
      simpl in Ei. rewrite <- Ei. exact Htyped.
    + intros U HU.
      inversion H0 as [| |L0 D0 Sbody Hforall|]; subst.
      set (X := fresh (L ++ L0 ++ Delta ++ ftv_rty R ++ ftv_rty S ++
        ftv_rcontext RGamma)).
      assert (HXall : ~ In X (L ++ L0 ++ Delta ++ ftv_rty R ++ ftv_rty S ++
        ftv_rcontext RGamma)).
      { subst X. apply fresh_notin. }
      repeat rewrite in_app_iff in HXall.
      assert (HXL : ~ In X L) by intuition.
      assert (HXL0 : ~ In X L0) by intuition.
      assert (HXDelta : ~ In X Delta) by intuition.
      assert (HXR : ~ In X (ftv_rty R)) by intuition.
      assert (HXS : ~ In X (ftv_rty S)) by intuition.
      assert (HXG : ~ In X (ftv_rcontext RGamma)) by intuition.
      set (theta' := type_subst_update theta X U).
      assert (HUlc : locally_closed_ty U) by (eapply wf_ty_lc; eauto).
      assert (Htheta' : type_substitution_closed theta').
      { unfold theta'. apply type_subst_update_closed; assumption. }
      assert (Hwf' : type_substitution_wf (X :: Delta) [] theta').
      { intros Y HY. simpl in HY. destruct HY as [E|HY].
        - subst Y. unfold theta', type_subst_update. rewrite Nat.eqb_refl. exact HU.
        - unfold theta', type_subst_update.
          assert (Hneq : X <> Y) by (intro E; subst; contradiction).
          rewrite (proj2 (Nat.eqb_neq X Y)) by exact Hneq. apply H4. exact HY. }
      assert (Hctx' : context_wf (X :: Delta) (erase_context RGamma)).
      { eapply context_wf_weaken_type; [exact H1|].
        intros Y HY. right. exact HY. }
      assert (Hrel' : related_substitution theta' gamma RGamma).
      { unfold theta'. eapply related_substitution_type_update; eauto. }
      assert (HwfS : wf_ty (X :: Delta) (erase (open_rty_ty S (Ty_FVar X)))).
      { rewrite erase_open_rty_ty. apply Hforall. exact HXL0. }
      destruct (Hbehavior U HU) as [Htapplc [Htapplhalt Htapall]].
      split; [exact Htapplc|]. split; [exact Htapplhalt|].
      intros result Hresult Hresultv.
      assert (Hinputeq : instantiate_rty theta' gamma
        (open_rty_ty R (Ty_FVar X)) =
        open_rty_ty (instantiate_rty theta gamma R) U).
      { unfold theta'. apply instantiate_rty_open_ty; try assumption. }
      assert (Hinput : denotes (instantiate_rty theta' gamma
        (open_rty_ty R (Ty_FVar X))) result).
      { rewrite Hinputeq. eapply Htapall; eauto. }
      pose proof (H X HXL HwfS Hctx' theta' gamma Htheta' H3 Hwf' Hrel'
        result Hinput) as Houtput.
      assert (Houteq : instantiate_rty theta' gamma
        (open_rty_ty S (Ty_FVar X)) =
        open_rty_ty (instantiate_rty theta gamma S) U).
      { unfold theta'. apply instantiate_rty_open_ty; try assumption. }
      rewrite Houteq in Houtput. exact Houtput.
  -
    assert (HwfS : wf_ty Delta (erase S)).
    { rewrite (subtype_erases Delta RGamma S U s0). exact H1. }
    pose proof (H HwfS H2 theta gamma H3 H4 H5 H6 v H7) as Hmid.
    exact (H0 H1 H2 theta gamma H3 H4 H5 H6 v Hmid).
Qed.

(* Optional reference theorem statement.
Theorem fundamental_and_subtyping :
  (forall Delta RGamma t R (H : has_rtype Delta RGamma t R),
    typing_semantics Delta RGamma t R) /\
  (forall Delta RGamma R S (H : subtype Delta RGamma R S),
    subtype_semantics Delta RGamma R S).
*)

(* Optional reference theorem statement.
Theorem fundamental : forall Delta RGamma t R,
  has_rtype Delta RGamma t R ->
  typing_semantics Delta RGamma t R.
*)

End SystemFRefinementSoundness.

Module SystemFRefinementTask.
Import ListNotations SystemFRefinement SystemFRefinementInfrastructure SystemFRefinementCoreTyping SystemFRefinementLogic SystemFRefinementTyping SystemFRefinementEvaluation SystemFRefinementDenotations SystemFRefinementSoundness.

Theorem never_stuck : forall (t t' : tm) (R : rty),
  has_rtype [] empty_rcontext t R ->
  multi t t' ->
  value t' \/ exists t'' : tm, t' --> t''.
Proof.
  intros t t' R Htyped Hsteps.
  pose proof ((proj1 fundamental_and_subtyping) [] empty_rcontext t R Htyped)
    as Hsem.
  assert (Hctx : context_wf [] empty).
  { intros x T Hlookup. discriminate. }
  assert (HthetaWf : type_substitution_wf [] [] identity_type_substitution).
  { intros X HX. contradiction. }
  assert (Hrel : related_substitution identity_type_substitution
    identity_term_substitution empty_rcontext).
  { intros x S Hlookup. discriminate. }
  pose proof (Hsem Hctx identity_type_substitution identity_term_substitution
    identity_type_substitution_closed identity_term_substitution_closed
    HthetaWf Hrel) as Hevals.
  rewrite instantiate_rty_identity, instantiate_identity in Hevals.
  destruct Hevals as [_ [Hhalt _]].
  apply halts_progress. eapply halts_multi; eauto.
Qed.

End SystemFRefinementTask.
