From Stdlib Require Import Program.Equality.
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

Fixpoint close_ty_rec (k : nat) (X : atom) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar Y => if Nat.eqb X Y then Ty_BVar k else Ty_FVar Y
  | Ty_Arrow T1 T2 =>
      Ty_Arrow (close_ty_rec k X T1) (close_ty_rec k X T2)
  | Ty_All T1 => Ty_All (close_ty_rec (S k) X T1)
  | Ty_Int => Ty_Int
  end.

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

End SystemFRefinementEvaluation.

From Stdlib Require Import Arith.PeanoNat Lists.List Lia Program.Wf.
From Equations Require Import Equations.
Module SystemFRefinementSubstitution.
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

Scheme has_rtype_mut_ind := Induction for has_rtype Sort Prop
with subtype_mut_ind := Induction for subtype Sort Prop.
Combined Scheme refinement_typing_mutind
  from has_rtype_mut_ind, subtype_mut_ind.
End SystemFRefinementSubstitution.

Module SystemFRefinementTask.
Import ListNotations SystemFRefinement SystemFRefinementInfrastructure SystemFRefinementCoreTyping SystemFRefinementLogic SystemFRefinementTyping SystemFRefinementEvaluation SystemFRefinementSubstitution .

Lemma rty_size_open_tm_rec : forall k R u,
  rty_size (open_rty_tm_rec k u R) = rty_size R.
Proof.
  intros k R u. revert k. induction R; intros k; simpl; try reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR. reflexivity.
Qed.

Lemma rty_size_open_tm : forall R u, rty_size (open_rty_tm R u) = rty_size R.
Proof. intros. unfold open_rty_tm. apply rty_size_open_tm_rec. Qed.

Fixpoint logical_value_fuel (fuel : nat) (R : rty) (v : tm) : Prop :=
  match fuel with
  | 0 => value v
  | S fuel' =>
      match R with
      | R_Refine _ ps => value v /\ qualifier_holds (open_qualifier_tm ps v)
      | R_Func _ _ => value v
      | R_Exists R1 R2 =>
          value v /\ exists w, value w /\ logical_value_fuel fuel' R1 w /\
            logical_value_fuel fuel' (open_rty_tm R2 w) v
      | R_Poly _ => value v
      end
  end.

Definition logical_value (R : rty) (v : tm) : Prop :=
  logical_value_fuel (rty_size R) R v.

Lemma logical_value_fuel_is_value : forall fuel R v,
  logical_value_fuel fuel R v -> value v.
Proof.
  induction fuel; intros R v H; simpl in H.
  - exact H.
  - destruct R; simpl in H; tauto.
Qed.

Lemma logical_value_fuel_monotone : forall n m R v,
  n <= m -> logical_value_fuel m R v -> logical_value_fuel n R v.
Proof.
  induction n; intros m R v Hle Hrel.
  - destruct m; simpl in *.
    + exact Hrel.
    + destruct R; simpl in Hrel; tauto.
  - destruct m; [lia|].
    destruct R; simpl in *; try exact Hrel.
    destruct Hrel as [Hv [w [Hw [HR1 HR2]]]].
    split; [exact Hv|]. exists w. split; [exact Hw|]. split.
    + apply IHn with (m := m) (R := R1) (v := w); [lia | exact HR1].
    + apply IHn with (m := m) (R := open_rty_tm R2 w) (v := v); [lia | exact HR2].
Qed.

Lemma logical_value_fuel_high_mono : forall n m R v,
  rty_size R <= n -> n <= m ->
  logical_value_fuel n R v -> logical_value_fuel m R v.
Proof.
  induction n; intros m R v Hsize Hle Hrel.
  - assert (1 <= rty_size R).
    { destruct R; simpl; lia. }
    lia.
  - destruct m; [lia|].
    destruct R; simpl in *; try exact Hrel.
    destruct Hrel as [Hv [w [Hw [HR1 HR2]]]].
    split; [exact Hv|]. exists w. split; [exact Hw|]. split.
    + apply IHn with (m := m); try assumption; lia.
    + apply IHn with (m := m).
      * rewrite rty_size_open_tm. lia.
      * lia.
      * exact HR2.
Qed.

Lemma logical_value_is_value : forall R v,
  logical_value R v -> value v.
Proof.
  intros R v H. unfold logical_value in H.
  eapply logical_value_fuel_is_value. exact H.
Qed.

Definition logical_context_interpretation
    (gamma : term_substitution) (RGamma : rcontext) : Prop :=
  forall x R, lookup_rcontext x RGamma = Some R ->
    logical_value (instantiate_rty identity_type_substitution gamma R)
      (gamma x).


Lemma instantiate_open_tm_rec : forall k x theta gamma t,
  term_substitution_closed gamma ->
  instantiate theta gamma (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k (gamma x) (instantiate theta gamma t).
Proof.
  intros k x theta gamma t Hclosed. revert k x theta gamma Hclosed.
  induction t; intros k x theta gamma Hclosed; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - assert (Hlc : lc_tm_at 0 k (gamma a)).
    { eapply lc_tm_at_monotone.
      - apply Hclosed.
      - lia.
      - lia. }
    rewrite (open_tm_rec_lc_at (gamma a) 0 k (gamma x) Hlc). reflexivity.
  - f_equal. apply IHt; exact Hclosed.
  - rewrite IHt1, IHt2; try exact Hclosed. reflexivity.
  - f_equal. apply IHt; exact Hclosed.
  - f_equal. apply IHt; exact Hclosed.
  - reflexivity.
  - rewrite IHt1, IHt2; try exact Hclosed. reflexivity.
  - rewrite IHt1, IHt2; try exact Hclosed. reflexivity.
Qed.

Lemma instantiate_open_qualifier_tm_rec : forall k x theta gamma p,
  term_substitution_closed gamma ->
  instantiate_qualifier theta gamma
    (open_qualifier_tm_rec k (tm_fvar x) p) =
  open_qualifier_tm_rec k (gamma x)
    (instantiate_qualifier theta gamma p).
Proof.
  intros k x theta gamma p Hclosed. revert k x theta gamma Hclosed.
  induction p; intros k x theta gamma Hclosed; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite (instantiate_open_tm_rec k x theta gamma t Hclosed),
      (instantiate_open_tm_rec k x theta gamma t0 Hclosed). reflexivity.
  - rewrite (instantiate_open_tm_rec k x theta gamma t Hclosed),
      (instantiate_open_tm_rec k x theta gamma t0 Hclosed). reflexivity.
  - rewrite (instantiate_open_tm_rec k x theta gamma t Hclosed),
      (instantiate_open_tm_rec k x theta gamma t0 Hclosed). reflexivity.
  - rewrite IHp1, IHp2; try exact Hclosed. reflexivity.
  - rewrite IHp1, IHp2; try exact Hclosed. reflexivity.
  - rewrite IHp; try exact Hclosed. reflexivity.
Qed.

Definition logical_qualifier_interpretation
    (gamma : term_substitution) (p : qualifier) : Prop :=
  qualifier_holds (instantiate_qualifier identity_type_substitution gamma p).

Lemma instantiate_term_subst_fresh : forall t theta gamma x u,
  ~ In x (fv_tm t) ->
  instantiate theta (term_subst_update gamma x u) t = instantiate theta gamma t.
Proof.
  induction t; intros theta gamma x u Hfresh; simpl in *.
  - reflexivity.
  - destruct (Nat.eqb x a) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst. exfalso. apply Hfresh. simpl. auto.
    + unfold term_subst_update. rewrite Heq. reflexivity.
  - f_equal. apply IHt. exact Hfresh.
  - assert (H1 : ~ In x (fv_tm t1)).
    { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
    assert (H2 : ~ In x (fv_tm t2)).
    { intro Hin. apply Hfresh. apply in_or_app. right. exact Hin. }
    rewrite IHt1 by exact H1. rewrite IHt2 by exact H2. reflexivity.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal. apply IHt. exact Hfresh.
  - reflexivity.
  - assert (H1 : ~ In x (fv_tm t1)).
    { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
    assert (H2 : ~ In x (fv_tm t2)).
    { intro Hin. apply Hfresh. apply in_or_app. right. exact Hin. }
    rewrite IHt1 by exact H1. rewrite IHt2 by exact H2. reflexivity.
  - assert (H1 : ~ In x (fv_tm t1)).
    { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
    assert (H2 : ~ In x (fv_tm t2)).
    { intro Hin. apply Hfresh. apply in_or_app. right. exact Hin. }
    rewrite IHt1 by exact H1. rewrite IHt2 by exact H2. reflexivity.
Qed.

Lemma instantiate_qualifier_subst_fresh : forall p theta gamma x u,
  ~ In x (fv_qualifier p) ->
  instantiate_qualifier theta (term_subst_update gamma x u) p =
  instantiate_qualifier theta gamma p.
Proof.
  induction p; intros theta gamma x u Hfresh; simpl in *; try reflexivity.
  - assert (H1 : ~ In x (fv_tm t)).
    { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
    assert (H2 : ~ In x (fv_tm t0)).
    { intro Hin. apply Hfresh. apply in_or_app. right. exact Hin. }
    rewrite (instantiate_term_subst_fresh t theta gamma x u H1).
    rewrite (instantiate_term_subst_fresh t0 theta gamma x u H2). reflexivity.
  - assert (H1 : ~ In x (fv_tm t)).
    { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
    assert (H2 : ~ In x (fv_tm t0)).
    { intro Hin. apply Hfresh. apply in_or_app. right. exact Hin. }
    rewrite (instantiate_term_subst_fresh t theta gamma x u H1).
    rewrite (instantiate_term_subst_fresh t0 theta gamma x u H2). reflexivity.
  - assert (H1 : ~ In x (fv_tm t)).
    { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
    assert (H2 : ~ In x (fv_tm t0)).
    { intro Hin. apply Hfresh. apply in_or_app. right. exact Hin. }
    rewrite (instantiate_term_subst_fresh t theta gamma x u H1).
    rewrite (instantiate_term_subst_fresh t0 theta gamma x u H2). reflexivity.
  - assert (H1 : ~ In x (fv_qualifier p1)).
    { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
    assert (H2 : ~ In x (fv_qualifier p2)).
    { intro Hin. apply Hfresh. apply in_or_app. right. exact Hin. }
    rewrite IHp1 by exact H1. rewrite IHp2 by exact H2. reflexivity.
  - assert (H1 : ~ In x (fv_qualifier p1)).
    { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
    assert (H2 : ~ In x (fv_qualifier p2)).
    { intro Hin. apply Hfresh. apply in_or_app. right. exact Hin. }
    rewrite IHp1 by exact H1. rewrite IHp2 by exact H2. reflexivity.
  - f_equal. apply IHp. exact Hfresh.
Qed.

Lemma instantiate_rty_subst_fresh : forall R theta gamma x u,
  ~ In x (fv_rty R) ->
  instantiate_rty theta (term_subst_update gamma x u) R =
  instantiate_rty theta gamma R.
Proof.
  induction R; intros theta gamma x u Hfresh; simpl in *.
  - f_equal. apply instantiate_qualifier_subst_fresh. exact Hfresh.
  - assert (H1 : ~ In x (fv_rty R1)).
    { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
    assert (H2 : ~ In x (fv_rty R2)).
    { intro Hin. apply Hfresh. apply in_or_app. right. exact Hin. }
    rewrite IHR1 by exact H1. rewrite IHR2 by exact H2. reflexivity.
  - assert (H1 : ~ In x (fv_rty R1)).
    { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
    assert (H2 : ~ In x (fv_rty R2)).
    { intro Hin. apply Hfresh. apply in_or_app. right. exact Hin. }
    rewrite IHR1 by exact H1. rewrite IHR2 by exact H2. reflexivity.
  - f_equal. apply IHR. exact Hfresh.
Qed.

Fixpoint dom_rcontext (RGamma : rcontext) : list atom :=
  match RGamma with
  | [] => []
  | (x, _) :: RGamma' => x :: dom_rcontext RGamma'
  end.

Lemma lookup_rcontext_update_neq : forall RGamma x y R,
  x <> y ->
  lookup_rcontext y (update_rcontext RGamma x R) = lookup_rcontext y RGamma.
Proof.
  intros RGamma x y R Hneq. unfold update_rcontext. simpl.
  destruct (Nat.eqb y x) eqn:Heq.
  - apply Nat.eqb_eq in Heq. exfalso. apply Hneq. symmetry. exact Heq.
  - reflexivity.
Qed.

Lemma lookup_rcontext_fv_incl : forall x RGamma R,
  lookup_rcontext x RGamma = Some R ->
  forall y, In y (fv_rty R) -> In y (fv_rcontext RGamma).
Proof.
  intros x RGamma. induction RGamma as [|[z S] RGamma IH]; intros R Hlookup y Hin; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x z) eqn:Heq.
    + inversion Hlookup; subst R. apply in_or_app. left. exact Hin.
    + apply in_or_app. right. eapply IH; eauto.
Qed.

Lemma logical_context_interpretation_update : forall gamma RGamma x R v,
  logical_context_interpretation gamma RGamma ->
  ~ In x (dom_rcontext RGamma) ->
  (forall y S, lookup_rcontext y RGamma = Some S ->
    ~ In x (fv_rty S)) ->
  ~ In x (fv_rty R) ->
  value v ->
  logical_value (instantiate_rty identity_type_substitution gamma R) v ->
  logical_context_interpretation (term_subst_update gamma x v)
    (update_rcontext RGamma x R).
Proof.
  intros gamma RGamma x R v Hctx Hdom Hfvctx HfvR Hv Hrel y S Hlookup.
  unfold update_rcontext in Hlookup. simpl in Hlookup.
  destruct (Nat.eqb y x) eqn:Heq.
  - apply Nat.eqb_eq in Heq. subst y. inversion Hlookup; subst S.
    assert (Hnew : term_subst_update gamma x v x = v).
    { unfold term_subst_update. rewrite Nat.eqb_refl. reflexivity. }
    rewrite Hnew.
    rewrite instantiate_rty_subst_fresh by exact HfvR. exact Hrel.
  - assert (Hxy : x <> y).
    { intro Heqxy. subst y. rewrite Nat.eqb_refl in Heq. discriminate. }
    specialize (Hctx y S Hlookup).
    assert (Hgamma : term_subst_update gamma x v y = gamma y).
    { unfold term_subst_update.
      assert (Hfalse : Nat.eqb x y = false) by (apply Nat.eqb_neq; exact Hxy).
      rewrite Hfalse. reflexivity. }
    rewrite instantiate_rty_subst_fresh by (apply Hfvctx with (y := y) (S := S); assumption).
    rewrite Hgamma. exact Hctx.
Qed.

Lemma entails_logical_context_sound : forall Delta RGamma p q,
  entails Delta RGamma p q -> forall gamma,
  term_substitution_closed gamma ->
  logical_context_interpretation gamma RGamma ->
  logical_qualifier_interpretation gamma p ->
  logical_qualifier_interpretation gamma q.
Proof.
  intros Delta RGamma p q Hent. induction Hent; intros gamma Hclosed Hctx Hsem;
    unfold logical_qualifier_interpretation in *; simpl in *; try firstorder.
  pose proof (Hctx x (R_Refine T p) H) as Hrel.
  cbn [logical_value logical_value_fuel rty_size instantiate_rty] in Hrel.
  unfold logical_qualifier_interpretation, open_qualifier_tm.
  rewrite (instantiate_open_qualifier_tm_rec 0 x identity_type_substitution gamma p Hclosed).
  exact (proj2 Hrel).
Qed.

Lemma rty_size_instantiate : forall theta gamma R,
  rty_size (instantiate_rty theta gamma R) = rty_size R.
Proof.
  intros theta gamma R. revert theta gamma. induction R; intros theta gamma; simpl; try reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR. reflexivity.
Qed.

Lemma instantiate_ty_identity : forall T,
  instantiate_ty identity_type_substitution T = T.
Proof. induction T; simpl; try reflexivity.
  - rewrite IHT1, IHT2. reflexivity.
  - rewrite IHT. reflexivity.
Qed.

Lemma instantiate_term_fv_nil : forall t gamma,
  fv_tm t = [] -> instantiate identity_type_substitution gamma t = t.
Proof.
  induction t; intros gamma Hfv; simpl in *.
  - reflexivity.
  - discriminate.
  - rewrite instantiate_ty_identity. f_equal. apply IHt. exact Hfv.
  - apply app_eq_nil in Hfv as [H1 H2]. rewrite IHt1 by exact H1. rewrite IHt2 by exact H2. reflexivity.
  - f_equal. apply IHt. exact Hfv.
  - rewrite instantiate_ty_identity. f_equal. apply IHt. exact Hfv.
  - reflexivity.
  - apply app_eq_nil in Hfv as [H1 H2]. rewrite IHt1 by exact H1. rewrite IHt2 by exact H2. reflexivity.
  - apply app_eq_nil in Hfv as [H1 H2]. rewrite IHt1 by exact H1. rewrite IHt2 by exact H2. reflexivity.
Qed.

Lemma instantiate_qualifier_predicate_closed : forall p gamma,
  predicate_closed p ->
  instantiate_qualifier identity_type_substitution gamma p = p.
Proof.
  induction p; intros gamma Hclosed; simpl in *; try reflexivity.
  - destruct Hclosed as [_ [Hfv1 [_ [_ [Hfv2 _]]]]].
    rewrite instantiate_term_fv_nil with (gamma := gamma) by exact Hfv1.
    rewrite instantiate_term_fv_nil with (gamma := gamma) by exact Hfv2. reflexivity.
  - destruct Hclosed as [_ [Hfv1 [_ [_ [Hfv2 _]]]]].
    rewrite instantiate_term_fv_nil with (gamma := gamma) by exact Hfv1.
    rewrite instantiate_term_fv_nil with (gamma := gamma) by exact Hfv2. reflexivity.
  - destruct Hclosed as [_ [Hfv1 [_ [_ [Hfv2 _]]]]].
    rewrite instantiate_term_fv_nil with (gamma := gamma) by exact Hfv1.
    rewrite instantiate_term_fv_nil with (gamma := gamma) by exact Hfv2. reflexivity.
  - destruct Hclosed as [H1 H2]. rewrite (IHp1 gamma H1), (IHp2 gamma H2). reflexivity.
  - destruct Hclosed as [H1 H2]. rewrite (IHp1 gamma H1), (IHp2 gamma H2). reflexivity.
  - rewrite (IHp gamma Hclosed). reflexivity.
Qed.

Lemma instantiate_open_tm_rec_term : forall k theta gamma t u,
  term_substitution_closed gamma ->
  instantiate theta gamma (open_tm_rec k u t) =
  open_tm_rec k (instantiate theta gamma u) (instantiate theta gamma t).
Proof.
  intros k theta gamma t u Hclosed. revert k theta gamma u Hclosed.
  induction t; intros k theta gamma u Hclosed; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - assert (Hlc : lc_tm_at 0 k (gamma a)).
    { eapply lc_tm_at_monotone; [apply Hclosed | lia | lia]. }
    rewrite (open_tm_rec_lc_at (gamma a) 0 k (instantiate theta gamma u) Hlc).
    reflexivity.
  - f_equal. apply IHt; exact Hclosed.
  - rewrite IHt1, IHt2; try exact Hclosed. reflexivity.
  - f_equal. apply IHt; exact Hclosed.
  - f_equal. apply IHt; exact Hclosed.
  - reflexivity.
  - rewrite IHt1, IHt2; try exact Hclosed. reflexivity.
  - rewrite IHt1, IHt2; try exact Hclosed. reflexivity.
Qed.

Lemma instantiate_open_qualifier_tm_rec_term : forall k theta gamma p u,
  term_substitution_closed gamma ->
  instantiate_qualifier theta gamma (open_qualifier_tm_rec k u p) =
  open_qualifier_tm_rec k (instantiate theta gamma u)
    (instantiate_qualifier theta gamma p).
Proof.
  intros k theta gamma p u Hclosed. revert k theta gamma u Hclosed.
  induction p; intros k theta gamma u Hclosed; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite (instantiate_open_tm_rec_term k theta gamma t u Hclosed),
      (instantiate_open_tm_rec_term k theta gamma t0 u Hclosed). reflexivity.
  - rewrite (instantiate_open_tm_rec_term k theta gamma t u Hclosed),
      (instantiate_open_tm_rec_term k theta gamma t0 u Hclosed). reflexivity.
  - rewrite (instantiate_open_tm_rec_term k theta gamma t u Hclosed),
      (instantiate_open_tm_rec_term k theta gamma t0 u Hclosed). reflexivity.
  - rewrite IHp1, IHp2; try exact Hclosed. reflexivity.
  - rewrite IHp1, IHp2; try exact Hclosed. reflexivity.
  - rewrite IHp; try exact Hclosed. reflexivity.
Qed.

Lemma instantiate_lc_tm_at : forall K k t gamma,
  lc_tm_at K k t -> term_substitution_closed gamma ->
  lc_tm_at K k (instantiate identity_type_substitution gamma t).
Proof.
  intros K k t gamma Hlc. induction Hlc; intros Hgamma; simpl.
  - apply lc_tm_bvar. assumption.
  - eapply lc_tm_at_monotone.
    + apply Hgamma.
    + lia.
    + lia.
  - apply lc_tm_abs.
    + rewrite instantiate_ty_identity. assumption.
    + apply IHHlc. exact Hgamma.
  - apply lc_tm_app; [apply IHHlc1 | apply IHHlc2]; exact Hgamma.
  - apply lc_tm_tabs. apply IHHlc. exact Hgamma.
  - apply lc_tm_tapp.
    + apply IHHlc. exact Hgamma.
    + rewrite instantiate_ty_identity. assumption.
  - constructor.
  - apply lc_tm_div; [apply IHHlc1 | apply IHHlc2]; exact Hgamma.
  - apply lc_tm_arith; [apply IHHlc1 | apply IHHlc2]; exact Hgamma.
Qed.

Lemma instantiate_preserves_value : forall v gamma,
  value v -> term_substitution_closed gamma ->
  value (instantiate identity_type_substitution gamma v).
Proof.
  intros v gamma Hv Hgamma. inversion Hv; subst; simpl.
  - rewrite instantiate_ty_identity. apply v_abs.
    unfold locally_closed_tm in H. inversion H; subst. apply lc_tm_abs.
    + assumption.
    + eapply instantiate_lc_tm_at; eauto.
  - apply v_tabs. unfold locally_closed_tm in H. inversion H; subst.
    apply lc_tm_tabs. eapply instantiate_lc_tm_at; eauto.
  - constructor.
Qed.

Lemma instantiate_open_rty_tm_rec_term : forall k theta gamma R u,
  term_substitution_closed gamma ->
  instantiate_rty theta gamma (open_rty_tm_rec k u R) =
  open_rty_tm_rec k (instantiate theta gamma u)
    (instantiate_rty theta gamma R).
Proof.
  intros k theta gamma R. revert k.
  induction R; intros k u Hclosed; simpl.
  - f_equal. apply instantiate_open_qualifier_tm_rec_term. exact Hclosed.
  - rewrite IHR1, IHR2; try exact Hclosed. reflexivity.
  - rewrite IHR1, IHR2; try exact Hclosed. reflexivity.
  - f_equal. apply IHR. exact Hclosed.
Qed.

Lemma instantiate_open_rty_tm_term : forall theta gamma R u,
  term_substitution_closed gamma ->
  instantiate_rty theta gamma (open_rty_tm R u) =
  open_rty_tm (instantiate_rty theta gamma R) (instantiate theta gamma u).
Proof.
  intros. unfold open_rty_tm. apply instantiate_open_rty_tm_rec_term. assumption.
Qed.

Definition Pvalue_typing (Delta : ty_context) (RGamma : rcontext)
    (t : tm) (R : rty) (_ : has_rtype Delta RGamma t R) : Prop :=
  forall gamma, term_substitution_closed gamma ->
    logical_context_interpretation gamma RGamma ->
    value (instantiate identity_type_substitution gamma t) ->
    logical_value (instantiate_rty identity_type_substitution gamma R)
      (instantiate identity_type_substitution gamma t).

Definition Pvalue_subtyping (Delta : ty_context) (RGamma : rcontext)
    (R S : rty) (_ : subtype Delta RGamma R S) : Prop :=
  forall gamma, term_substitution_closed gamma ->
    logical_context_interpretation gamma RGamma -> forall v,
    logical_value (instantiate_rty identity_type_substitution gamma R) v ->
    logical_value (instantiate_rty identity_type_substitution gamma S) v.

Lemma value_fundamental_mutual :
  (forall Delta RGamma t R (H : has_rtype Delta RGamma t R), Pvalue_typing Delta RGamma t R H) /\
  (forall Delta RGamma R S (H : subtype Delta RGamma R S), Pvalue_subtyping Delta RGamma R S H).
Proof.
  apply (refinement_typing_mutind Pvalue_typing Pvalue_subtyping);
    intros; simpl in *; try firstorder.
  - unfold Pvalue_typing. intros gamma Hclosed Hctx Hval. simpl in Hval. inversion Hval.
  - unfold Pvalue_typing. intros gamma Hclosed Hctx Hval. simpl in Hval. inversion Hval.
  - unfold Pvalue_typing. intros gamma Hclosed Hctx Hval. simpl in *.
    split; [exact Hval|]. unfold qualifier_holds, predicate_holds. simpl.
    exists (tm_int n). repeat split; constructor.
  - unfold Pvalue_typing. intros gamma Hclosed Hctx Hval. simpl in Hval. inversion Hval.
  - unfold Pvalue_typing. intros gamma Hclosed Hctx Hval.
    cbn [instantiate_rty instantiate]. split; [exact Hval|].
    unfold open_qualifier_tm.
    rewrite <- (instantiate_open_qualifier_tm_rec_term 0 identity_type_substitution gamma ps v Hclosed).
    change (qualifier_holds (instantiate_qualifier identity_type_substitution gamma
      (open_qualifier_tm ps v))).
    rewrite instantiate_qualifier_predicate_closed with (p := open_qualifier_tm ps v) (gamma := gamma) by exact p.
    exact q.
  - unfold Pvalue_subtyping. intros gamma Hclosed Hctx v Hrel.
    cbn [logical_value logical_value_fuel rty_size instantiate_rty] in Hrel.
    destruct Hrel as [Hv Hps]. split; [exact Hv|].
    set (X := fresh (L ++ dom_rcontext RGamma ++ fv_rcontext RGamma ++ fv_qualifier ps ++ fv_qualifier qs)).
    assert (HX : ~ In X L).
    { unfold X. intro Hin. apply (fresh_notin (L ++ dom_rcontext RGamma ++ fv_rcontext RGamma ++ fv_qualifier ps ++ fv_qualifier qs)).
      apply in_or_app. left. exact Hin. }
    assert (HXdom : ~ In X (dom_rcontext RGamma)).
    { unfold X. intro Hin. apply (fresh_notin (L ++ dom_rcontext RGamma ++ fv_rcontext RGamma ++ fv_qualifier ps ++ fv_qualifier qs)).
      apply in_or_app. right. apply in_or_app. left. exact Hin. }
    assert (HXctx : ~ In X (fv_rcontext RGamma)).
    { unfold X. intro Hin. apply (fresh_notin (L ++ dom_rcontext RGamma ++ fv_rcontext RGamma ++ fv_qualifier ps ++ fv_qualifier qs)).
      apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hin. }
    assert (HXp : ~ In X (fv_qualifier ps)).
    { unfold X. intro Hin. apply (fresh_notin (L ++ dom_rcontext RGamma ++ fv_rcontext RGamma ++ fv_qualifier ps ++ fv_qualifier qs)).
      apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hin. }
    assert (HXq : ~ In X (fv_qualifier qs)).
    { unfold X. intro Hin. apply (fresh_notin (L ++ dom_rcontext RGamma ++ fv_rcontext RGamma ++ fv_qualifier ps ++ fv_qualifier qs)).
      apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact Hin. }
    assert (Hclosed' : term_substitution_closed (term_subst_update gamma X v))
      by (apply term_subst_update_closed; [exact Hclosed | apply value_regular; exact Hv]).
    assert (Htrue : logical_value (instantiate_rty identity_type_substitution
      (term_subst_update gamma X v) (R_Refine T Pred_True)) v).
    { cbn [logical_value logical_value_fuel rty_size instantiate_rty]. split; [exact Hv|exact I]. }
    assert (Hctx' : logical_context_interpretation (term_subst_update gamma X v)
      (update_rcontext RGamma X (R_Refine T Pred_True))).
    { eapply logical_context_interpretation_update.
      - exact Hctx.
      - exact HXdom.
      - intros y S Hlook Hin. apply HXctx. eapply lookup_rcontext_fv_incl; eauto.
      - simpl. tauto.
      - exact Hv.
      - exact Htrue. }
    specialize (e X HX) as Hent.
    assert (Hsource : logical_qualifier_interpretation (term_subst_update gamma X v)
      (open_qualifier_tm ps (tm_fvar X))).
    { unfold logical_qualifier_interpretation, open_qualifier_tm.
      rewrite (instantiate_open_qualifier_tm_rec 0 X identity_type_substitution
        (term_subst_update gamma X v) ps Hclosed').
      assert (HgX : term_subst_update gamma X v X = v).
      { unfold term_subst_update. rewrite Nat.eqb_refl. reflexivity. }
      rewrite HgX.
      rewrite instantiate_qualifier_subst_fresh by exact HXp.
      exact Hps. }
    pose proof (entails_logical_context_sound _ _ _ _ Hent
      (term_subst_update gamma X v) Hclosed' Hctx' Hsource) as Htarget.
    unfold logical_qualifier_interpretation, open_qualifier_tm in Htarget.
    rewrite (instantiate_open_qualifier_tm_rec 0 X identity_type_substitution
      (term_subst_update gamma X v) qs Hclosed') in Htarget.
    assert (HgX : term_subst_update gamma X v X = v).
    { unfold term_subst_update. rewrite Nat.eqb_refl. reflexivity. }
    rewrite HgX in Htarget.
    rewrite instantiate_qualifier_subst_fresh in Htarget by exact HXq.
    exact Htarget.
  - unfold Pvalue_subtyping. intros gamma Hclosed Hctx u Hsource.
    pose proof (instantiate_preserves_value v gamma v0 Hclosed) as Hvw.
    pose proof (H gamma Hclosed Hctx Hvw) as Hrelw.
    pose proof (H0 gamma Hclosed Hctx u Hsource) as Hrelu.
    rewrite instantiate_open_rty_tm_term in Hrelu by exact Hclosed.
    apply logical_value_is_value in Hsource.
    split; [exact Hsource|]. exists (instantiate identity_type_substitution gamma v).
    split; [exact Hvw|]. split.
    + unfold logical_value in Hrelw.
      apply (logical_value_fuel_high_mono
        (rty_size (instantiate_rty identity_type_substitution gamma R1))
        (rty_size (instantiate_rty identity_type_substitution gamma R1) +
         rty_size (instantiate_rty identity_type_substitution gamma R2))
        (instantiate_rty identity_type_substitution gamma R1)
        (instantiate identity_type_substitution gamma v)).
      * lia.
      * lia.
      * exact Hrelw.
    + unfold logical_value in Hrelu.
      rewrite rty_size_open_tm in Hrelu.
      rewrite rty_size_instantiate in Hrelu.
      apply (logical_value_fuel_high_mono
        (rty_size R2)
        (rty_size (instantiate_rty identity_type_substitution gamma R1) +
         rty_size (instantiate_rty identity_type_substitution gamma R2))
        (open_rty_tm (instantiate_rty identity_type_substitution gamma R2)
          (instantiate identity_type_substitution gamma v)) u).
      * rewrite rty_size_open_tm, !rty_size_instantiate. lia.
      * rewrite !rty_size_instantiate. lia.
      * exact Hrelu.
  - unfold Pvalue_subtyping. intros gamma Hclosed Hctx u Hsource.
    cbn [logical_value logical_value_fuel rty_size instantiate_rty] in Hsource.
    destruct Hsource as [Hvu [z [Hz [Hrel1 Hrel2]]]].
    assert (HrelR1 : logical_value (instantiate_rty identity_type_substitution gamma R1) z).
    { unfold logical_value.
      apply logical_value_fuel_monotone with
        (m := rty_size (instantiate_rty identity_type_substitution gamma R1) +
              rty_size (instantiate_rty identity_type_substitution gamma R2)).
      - lia.
      - exact Hrel1. }
    set (X := fresh (L ++ dom_rcontext RGamma ++ fv_rcontext RGamma ++
      fv_rty R1 ++ fv_rty R2 ++ fv_rty S)).
    assert (HX : ~ In X L).
    { unfold X. intro Hin. apply (fresh_notin (L ++ dom_rcontext RGamma ++ fv_rcontext RGamma ++ fv_rty R1 ++ fv_rty R2 ++ fv_rty S)).
      apply in_or_app. left. exact Hin. }
    assert (HXdom : ~ In X (dom_rcontext RGamma)).
    { unfold X. intro Hin. apply (fresh_notin (L ++ dom_rcontext RGamma ++ fv_rcontext RGamma ++ fv_rty R1 ++ fv_rty R2 ++ fv_rty S)).
      apply in_or_app. right. apply in_or_app. left. exact Hin. }
    assert (HXctx : ~ In X (fv_rcontext RGamma)).
    { unfold X. intro Hin. apply (fresh_notin (L ++ dom_rcontext RGamma ++ fv_rcontext RGamma ++ fv_rty R1 ++ fv_rty R2 ++ fv_rty S)).
      apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hin. }
    assert (HX1 : ~ In X (fv_rty R1)).
    { unfold X. intro Hin. apply (fresh_notin (L ++ dom_rcontext RGamma ++ fv_rcontext RGamma ++ fv_rty R1 ++ fv_rty R2 ++ fv_rty S)).
      apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hin. }
    assert (HX2 : ~ In X (fv_rty R2)).
    { unfold X. intro Hin. apply (fresh_notin (L ++ dom_rcontext RGamma ++ fv_rcontext RGamma ++ fv_rty R1 ++ fv_rty R2 ++ fv_rty S)).
      apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hin. }
    assert (HXS : ~ In X (fv_rty S)).
    { unfold X. intro Hin. apply (fresh_notin (L ++ dom_rcontext RGamma ++ fv_rcontext RGamma ++ fv_rty R1 ++ fv_rty R2 ++ fv_rty S)).
      apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact Hin. }
    set (gamma' := term_subst_update gamma X z).
    assert (Hclosed' : term_substitution_closed gamma').
    { unfold gamma'. apply term_subst_update_closed; [exact Hclosed|apply value_regular; exact Hz]. }
    assert (Hctx' : logical_context_interpretation gamma'
      (update_rcontext RGamma X R1)).
    { unfold gamma'. eapply logical_context_interpretation_update.
      - exact Hctx.
      - exact HXdom.
      - intros y Q Hlook Hin. apply HXctx. eapply lookup_rcontext_fv_incl; eauto.
      - exact HX1.
      - exact Hz.
      - exact HrelR1. }
    assert (Hbody : logical_value
      (instantiate_rty identity_type_substitution gamma' (open_rty_tm R2 (tm_fvar X))) u).
    { unfold gamma'. rewrite instantiate_open_rty_tm_term by exact Hclosed'.
      assert (HinstX : instantiate identity_type_substitution
        (term_subst_update gamma X z) (tm_fvar X) = z).
      { simpl. unfold term_subst_update. rewrite Nat.eqb_refl. reflexivity. }
      rewrite HinstX. rewrite instantiate_rty_subst_fresh by exact HX2.
      unfold logical_value. rewrite rty_size_open_tm.
      apply logical_value_fuel_monotone with
        (m := rty_size (instantiate_rty identity_type_substitution gamma R1) +
              rty_size (instantiate_rty identity_type_substitution gamma R2)).
      - rewrite !rty_size_instantiate. lia.
      - exact Hrel2. }
    specialize (H X HX) as Hsubprop.
    specialize (Hsubprop gamma' Hclosed' Hctx' u Hbody).
    unfold gamma' in Hsubprop.
    rewrite instantiate_rty_subst_fresh in Hsubprop by exact HXS.
    exact Hsubprop.
Qed.

Lemma core_value_arrow : forall Gamma v T1 T2,
  has_type [] Gamma v (Ty_Arrow T1 T2) -> value v ->
  exists T body, v = tm_abs T body.
Proof.
  intros Gamma v T1 T2 Hty Hv. inversion Hv; subst.
  - eexists. eexists. reflexivity.
  - inversion Hty.
  - inversion Hty.
Qed.

Lemma core_value_all : forall Gamma v T,
  has_type [] Gamma v (Ty_All T) -> value v ->
  exists body, v = tm_tabs body.
Proof.
  intros Gamma v T Hty Hv. inversion Hv; subst.
  - inversion Hty.
  - eexists. reflexivity.
  - inversion Hty.
Qed.

Lemma core_value_int : forall Gamma v,
  has_type [] Gamma v Ty_Int -> value v ->
  exists n, v = tm_int n.
Proof.
  intros Gamma v Hty Hv. inversion Hv; subst.
  - inversion Hty.
  - inversion Hty.
  - eexists. reflexivity.
Qed.

Lemma step_preserves_lc : forall t t',
  t --> t' -> locally_closed_tm t -> locally_closed_tm t'.
Proof.
  intros t t' Hstep. induction Hstep; intros Hlc.
  - inversion Hlc; subst. unfold locally_closed_tm in *.
    eapply open_tm_preserves_lc_at.
    + inversion H5; assumption.
    + apply value_regular. assumption.
  - inversion Hlc; subst. unfold locally_closed_tm in *.
    apply lc_tm_app; eauto.
  - inversion Hlc; subst. unfold locally_closed_tm in *.
    apply lc_tm_app; eauto.
  - inversion Hlc; subst. unfold locally_closed_tm in *.
    eapply open_tm_ty_preserves_lc_at.
    + inversion H5; assumption.
    + exact H6.
  - inversion Hlc; subst. unfold locally_closed_tm in *.
    apply lc_tm_tapp; eauto.
  - inversion Hlc; subst. unfold locally_closed_tm in *.
    apply lc_tm_div; eauto.
  - inversion Hlc; subst. unfold locally_closed_tm in *.
    apply lc_tm_div; eauto.
  - constructor.
  - inversion Hlc; subst. unfold locally_closed_tm in *.
    apply lc_tm_arith; eauto.
  - inversion Hlc; subst. unfold locally_closed_tm in *.
    apply lc_tm_arith; eauto.
  - constructor.
Qed.

Lemma empty_context_no_variable : forall x T,
  has_type [] empty (tm_fvar x) T -> False.
Proof.
  intros x T Hty. inversion Hty; subst.
  simpl in *. discriminate.
Qed.

Lemma multi_preserves_lc : forall t t',
  multi t t' -> locally_closed_tm t -> locally_closed_tm t'.
Proof.
  intros t t' Hmulti. induction Hmulti; intros Hlc.
  - exact Hlc.
  - apply IHHmulti. eapply step_preserves_lc; eauto.
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

Lemma open_ty_rec_fvar_injective : forall T U k X,
  ~ In X (fv_ty T) -> ~ In X (fv_ty U) ->
  open_ty_rec k (Ty_FVar X) T = open_ty_rec k (Ty_FVar X) U -> T = U.
Proof.
  induction T; intros U k X HnotT HnotU Heq.
  - destruct U; simpl in Heq.
    + destruct (Nat.eqb k n) eqn:E1; destruct (Nat.eqb k n0) eqn:E2.
      * apply Nat.eqb_eq in E1. apply Nat.eqb_eq in E2. subst. reflexivity.
      * discriminate Heq.
      * discriminate Heq.
      * inversion Heq. reflexivity.
    + destruct (Nat.eqb k n) eqn:E; [|discriminate Heq].
      inversion Heq; subst. exfalso. apply HnotU. simpl. auto.
    + destruct (Nat.eqb k n); discriminate Heq.
    + destruct (Nat.eqb k n); discriminate Heq.
    + destruct (Nat.eqb k n); discriminate Heq.
  - destruct U; simpl in Heq.
    + destruct (Nat.eqb k n) eqn:E; [|discriminate Heq].
      inversion Heq; subst. exfalso. apply HnotT. simpl. auto.
    + inversion Heq. reflexivity.
    + discriminate Heq.
    + discriminate Heq.
    + discriminate Heq.
  - destruct U; simpl in Heq.
    + destruct (Nat.eqb k n); discriminate.
    + discriminate.
    + inversion Heq; subst. f_equal.
      * eapply IHT1.
        -- intros Hin. apply HnotT. apply in_or_app. left. exact Hin.
        -- intros Hin. apply HnotU. apply in_or_app. left. exact Hin.
        -- exact H0.
      * eapply IHT2.
        -- intros Hin. apply HnotT. apply in_or_app. right. exact Hin.
        -- intros Hin. apply HnotU. apply in_or_app. right. exact Hin.
        -- exact H1.
    + discriminate.
    + discriminate.
  - destruct U; simpl in Heq.
    + destruct (Nat.eqb k n); discriminate.
    + discriminate.
    + discriminate.
    + inversion Heq; subst. f_equal. eapply IHT; eauto.
    + discriminate.
  - destruct U; simpl in Heq.
    + destruct (Nat.eqb k n); discriminate.
    + discriminate.
    + discriminate.
    + discriminate.
    + inversion Heq. reflexivity.
Qed.

Lemma subtype_erases : forall Delta RGamma R S,
  subtype Delta RGamma R S -> erase R = erase S.
Proof.
  intros Delta RGamma R S Hsub.
  induction Hsub; simpl in *.
  - reflexivity.
  - reflexivity.
  - rewrite <- IHHsub.
    specialize (H0 (fresh L) (fresh_notin L)).
    rewrite (erase_open_rty_tm R2 (tm_fvar (fresh L))) in H0.
    rewrite (erase_open_rty_tm S2 (tm_fvar (fresh L))) in H0.
    f_equal. exact H0.
  - rewrite (erase_open_rty_tm R2 v) in IHHsub. exact IHHsub.
  - specialize (H2 (fresh L) (fresh_notin L)).
    rewrite (erase_open_rty_tm R2 (tm_fvar (fresh L))) in H2. exact H2.
  - set (X := fresh (L ++ fv_ty (erase R) ++ fv_ty (erase S))).
    assert (HX : ~ In X L).
    { unfold X. intro Hin. apply (fresh_notin (L ++ fv_ty (erase R) ++ fv_ty (erase S))).
      apply in_or_app. left. exact Hin. }
    assert (HXR : ~ In X (fv_ty (erase R))).
    { unfold X. intro Hin. apply (fresh_notin (L ++ fv_ty (erase R) ++ fv_ty (erase S))).
      apply in_or_app. right. apply in_or_app. left. exact Hin. }
    assert (HXS : ~ In X (fv_ty (erase S))).
    { unfold X. intro Hin. apply (fresh_notin (L ++ fv_ty (erase R) ++ fv_ty (erase S))).
      apply in_or_app. right. apply in_or_app. right. exact Hin. }
    specialize (H0 X HX). repeat rewrite erase_open_rty_ty in H0.
    assert (Hbase : erase R = erase S).
    { eapply open_ty_rec_fvar_injective.
      - exact HXR.
      - exact HXS.
      - exact H0. }
    rewrite Hbase. reflexivity.
  - rewrite IHHsub1, IHHsub2. reflexivity.
Qed.

Lemma lookup_erase_context : forall x RGamma,
  lookup_context x (erase_context RGamma) =
  option_map erase (lookup_rcontext x RGamma).
Proof.
  intros x RGamma. induction RGamma as [|[y R] RGamma IH]; simpl.
  - reflexivity.
  - unfold update. simpl. destruct (Nat.eqb x y); auto.
Qed.

Lemma wf_rty_erases : forall Delta RGamma R,
  wf_rty Delta RGamma R -> wf_ty Delta (erase R).
Proof.
  intros Delta RGamma R Hwf. induction Hwf; simpl.
  - assumption.
  - apply WF_Arrow.
    + exact IHHwf.
    + specialize (H0 (fresh L) (fresh_notin L)).
      rewrite erase_open_rty_tm in H0. exact H0.
  - specialize (H0 (fresh L) (fresh_notin L)).
    rewrite erase_open_rty_tm in H0. exact H0.
  - apply WF_All with (L := L). intros X Hfresh.
    specialize (H0 X Hfresh). rewrite erase_open_rty_ty in H0. exact H0.
Qed.

Lemma has_rtype_erases : forall Delta RGamma t R,
  has_rtype Delta RGamma t R ->
  has_type Delta (erase_context RGamma) t (erase R).
Proof.
  intros Delta RGamma t R Htyping.
  induction Htyping; simpl.
  - apply T_Var.
    + rewrite lookup_erase_context, H. reflexivity.
    + eapply wf_rty_erases; eauto.
  - apply T_Abs with (L := L).
    + eapply wf_rty_erases; eauto.
    + intros x Hfresh. specialize (H1 x Hfresh).
      rewrite erase_open_rty_tm in H1. exact H1.
  - eapply T_App; eauto.
  - apply T_TAbs with (L := L). intros X Hfresh.
    specialize (H0 X Hfresh).
    rewrite erase_open_rty_ty in H0. exact H0.
  - rewrite erase_open_rty_ty. eapply T_TApp; eauto.
  - constructor.
  - eapply T_Div; eauto.
  - eapply T_Arith; eauto.
  - assumption.
  - rewrite <- (subtype_erases _ _ _ _ H0). exact IHHtyping.
Qed.

Lemma operational_nonzero_integer : forall n : Z,
  qualifier_holds (Pred_Ne (tm_int n) (tm_int 0%Z)) -> n <> 0%Z.
Proof.
  intros n Hneq Heq. subst n. unfold qualifier_holds, predicate_holds in Hneq.
  simpl in Hneq. apply Hneq. exists (tm_int 0%Z). repeat split.
  - constructor.
  - constructor.
  - constructor.
Qed.

Lemma logical_value_nonzero_integer : forall n,
  logical_value (R_Refine Ty_Int (Pred_Ne (tm_bvar 0) (tm_int 0%Z)))
    (tm_int n) -> n <> 0%Z.
Proof.
  intros n Hrel. simpl in Hrel. destruct Hrel as [_ Hneq].
  apply operational_nonzero_integer with (n := n).
  exact Hneq.
Qed.

Lemma multistep_to_value_progress : forall t v,
  multi t v -> value v -> ~ value t -> exists t', t --> t'.
Proof.
  intros t v Hrun Hv Hnot.
  inversion Hrun; subst.
  - contradiction.
  - eexists. eassumption.
Qed.

Lemma wf_ty_locally_closed : forall Delta T,
  wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T Hwf. induction Hwf.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; assumption.
  - unfold locally_closed_ty. apply lc_ty_all.
    specialize (H0 (fresh L) (fresh_notin L)).
    eapply lc_ty_at_open_inv. simpl in H0. exact H0.
  - apply lc_ty_int.
Qed.

Lemma has_type_locally_closed : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T Hty. induction Hty.
  - constructor.
  - unfold locally_closed_tm. apply lc_tm_abs.
    + apply (wf_ty_locally_closed Delta). assumption.
    + specialize (H0 (fresh L) (fresh_notin L)).
      pose proof (H1 (fresh L) (fresh_notin L)) as Hlc.
      unfold locally_closed_tm in Hlc.
      eapply lc_tm_at_open_tm_inv. exact Hlc.
  - unfold locally_closed_tm. apply lc_tm_app; assumption.
  - unfold locally_closed_tm. apply lc_tm_tabs.
    pose proof (H0 (fresh L) (fresh_notin L)) as Hlc.
    unfold locally_closed_tm in Hlc.
    eapply lc_tm_at_open_ty_inv. exact Hlc.
  - unfold locally_closed_tm. apply lc_tm_tapp; [assumption | apply (wf_ty_locally_closed Delta); assumption].
  - constructor.
  - unfold locally_closed_tm. apply lc_tm_div; assumption.
  - unfold locally_closed_tm. apply lc_tm_arith; assumption.
Qed.

Lemma has_rtype_locally_closed : forall t R,
  has_rtype [] empty_rcontext t R -> locally_closed_tm t.
Proof.
  intros t R Hty. apply has_type_locally_closed with (Delta := []) (T := erase R) (Gamma := erase_context empty_rcontext).
  apply has_rtype_erases. exact Hty.
Qed.

Lemma tm_subst_open_fvar_nil : forall t x s k,
  fv_tm t = [] ->
  tm_subst x s (open_tm_rec k (tm_fvar x) t) = open_tm_rec k s t.
Proof.
  induction t; intros x s k Hfv; simpl in *.
  - destruct (Nat.eqb k n); simpl; try rewrite Nat.eqb_refl; reflexivity.
  - discriminate.
  - f_equal. apply IHt with (x := x) (s := s) (k := S k). exact Hfv.
  - apply app_eq_nil in Hfv as [Hfv1 Hfv2].
    rewrite (IHt1 x s k Hfv1), (IHt2 x s k Hfv2). reflexivity.
  - f_equal. apply IHt with (x := x) (s := s) (k := k). exact Hfv.
  - f_equal. apply IHt with (x := x) (s := s) (k := k). exact Hfv.
  - reflexivity.
  - apply app_eq_nil in Hfv as [Hfv1 Hfv2].
    rewrite (IHt1 x s k Hfv1), (IHt2 x s k Hfv2). reflexivity.
  - apply app_eq_nil in Hfv as [Hfv1 Hfv2].
    rewrite (IHt1 x s k Hfv1), (IHt2 x s k Hfv2). reflexivity.
Qed.

Lemma qualifier_subst_open_fvar_nil : forall p x s,
  fv_qualifier p = [] ->
  qualifier_subst x s (open_qualifier_tm p (tm_fvar x)) =
  open_qualifier_tm p s.
Proof.
  induction p; intros x s Hfv; simpl in *; try reflexivity.
  - apply app_eq_nil in Hfv as [H1 H2].
    rewrite (tm_subst_open_fvar_nil t x s 0 H1),
      (tm_subst_open_fvar_nil t0 x s 0 H2). reflexivity.
  - apply app_eq_nil in Hfv as [H1 H2].
    rewrite (tm_subst_open_fvar_nil t x s 0 H1),
      (tm_subst_open_fvar_nil t0 x s 0 H2). reflexivity.
  - apply app_eq_nil in Hfv as [H1 H2].
    rewrite (tm_subst_open_fvar_nil t x s 0 H1),
      (tm_subst_open_fvar_nil t0 x s 0 H2). reflexivity.
  - apply app_eq_nil in Hfv as [H1 H2].
    unfold open_qualifier_tm; simpl. f_equal.
    + apply IHp1. exact H1.
    + apply IHp2. exact H2.
  - apply app_eq_nil in Hfv as [H1 H2].
    unfold open_qualifier_tm; simpl. f_equal.
    + apply IHp1. exact H1.
    + apply IHp2. exact H2.
  - unfold open_qualifier_tm; simpl. f_equal. apply IHp. exact Hfv.
Qed.

Lemma entails_singleton_context_sound : forall x s T ps p q,
  entails [] (update_rcontext [] x (R_Refine T ps)) p q ->
  qualifier_holds (qualifier_subst x s (open_qualifier_tm ps (tm_fvar x))) ->
  qualifier_holds (qualifier_subst x s p) ->
  qualifier_holds (qualifier_subst x s q).
Proof.
  intros x s T ps p q Hent.
  unfold qualifier_holds, predicate_holds in *.
  dependent induction Hent; simpl in *; intros Hctx Hsem; try tauto.
  - apply (IHHent2 x T ps JMeq_refl eq_refl Hctx).
    apply (IHHent1 x T ps JMeq_refl eq_refl Hctx). exact Hsem.
  - split; [apply (IHHent1 x T ps JMeq_refl eq_refl Hctx) | apply (IHHent2 x T ps JMeq_refl eq_refl Hctx)]; exact Hsem.
  - destruct Hsem as [Hp | Hq].
    + apply (IHHent1 x T ps JMeq_refl eq_refl Hctx). exact Hp.
    + apply (IHHent2 x T ps JMeq_refl eq_refl Hctx). exact Hq.
  - intros Hq. apply (IHHent x T ps JMeq_refl eq_refl Hctx). split; assumption.
  - unfold update_rcontext in H. simpl in H.
    destruct (Nat.eqb x0 x) eqn:Heq; try discriminate.
    apply Nat.eqb_eq in Heq. subst x0.
    inversion H; subst. exact Hctx.
Qed.

Lemma entails_true_context_subst : forall x s p q,
  entails [] (update_rcontext [] x (R_Refine Ty_Int Pred_True)) p q ->
  qualifier_holds (qualifier_subst x s p) ->
  qualifier_holds (qualifier_subst x s q).
Proof.
  intros x s p q Hent Hsem.
  eapply entails_singleton_context_sound; eauto.
  simpl. exact I.
Qed.

Lemma typed_nonzero_integer_value_context : forall RGamma gamma n,
  term_substitution_closed gamma ->
  logical_context_interpretation gamma RGamma ->
  has_rtype [] RGamma (tm_int n)
    (R_Refine Ty_Int (Pred_Ne (tm_bvar 0) (tm_int 0%Z))) -> n <> 0%Z.
Proof.
  intros RGamma gamma n Hclosed Hctx Hty.
  pose proof (proj1 value_fundamental_mutual [] RGamma (tm_int n)
    (R_Refine Ty_Int (Pred_Ne (tm_bvar 0) (tm_int 0%Z))) Hty
    gamma Hclosed Hctx (v_int n)) as Hfund.
  cbn [instantiate instantiate_rty instantiate_ty instantiate_qualifier
    instantiate_pred] in Hfund.
  apply logical_value_nonzero_integer with (n := n). exact Hfund.
Qed.

Lemma refinement_progress : forall t R RGamma gamma,
  has_rtype [] RGamma t R -> locally_closed_tm t -> fv_tm t = [] ->
  term_substitution_closed gamma ->
  logical_context_interpretation gamma RGamma ->
  value t \/ exists t', t --> t'.
Proof.
  intros t R RGamma gamma Hty. dependent induction Hty;
    intros Hlc Hfv Hclosed Hctx; try (left; assumption).
  - simpl in Hfv. discriminate.
  - (* abstraction *)
    left. constructor. exact Hlc.
  - (* application *)
    inversion Hlc; subst.
    simpl in Hfv. apply app_eq_nil in Hfv as [Hfv1 Hfv2].
    unfold locally_closed_tm in *.
    assert (Hprog1 : value t1 \/ exists u, t1 --> u)
      by (eapply IHHty1; eauto).
    assert (Hprog2 : value t2 \/ exists u, t2 --> u)
      by (eapply IHHty2; eauto).
    destruct Hprog1 as [Hv1 | [t1' Hs1]].
    + destruct Hprog2 as [Hv2 | [t2' Hs2]].
      * right. destruct (core_value_arrow _ _ _ _ (has_rtype_erases _ _ _ _ Hty1) Hv1)
          as [T [body Heq]]. subst t1.
        inversion Hv1; subst. eexists. apply ST_AppAbs; [assumption | exact Hv2].
      * right. exists (tm_app t1 t2'). apply ST_App2; assumption.
    + right. exists (tm_app t1' t2). apply ST_App1; [exact Hs1 |].
      unfold locally_closed_tm. exact H4.
  - (* type abstraction *)
    left. constructor. exact Hlc.
  - (* type application *)
    simpl in Hfv.
    inversion Hlc; subst. unfold locally_closed_tm in *.
    assert (Hprog : value t \/ exists u, t --> u).
    { eapply IHHty; eauto. }
    destruct Hprog as [Hv | [u' Hs]].
    + right. destruct (core_value_all _ _ _ (has_rtype_erases _ _ _ _ Hty) Hv)
        as [body Heq]. subst t. inversion Hv; subst. eexists.
      apply ST_TAppTabs; [assumption | apply wf_ty_locally_closed with (Delta := []); assumption].
    + right. exists (tm_tapp u' U). apply ST_TApp; [exact Hs |].
      apply wf_ty_locally_closed with (Delta := []); assumption.
  - (* integer *)
    left. constructor.
  - (* division *)
    inversion Hlc; subst. unfold locally_closed_tm in *.
    simpl in Hfv. apply app_eq_nil in Hfv as [Hfv1 Hfv2].
    assert (Hprog1 : value t1 \/ exists u, t1 --> u)
      by (eapply IHHty1; eauto).
    assert (Hprog2 : value t2 \/ exists u, t2 --> u)
      by (eapply IHHty2; eauto).
    destruct Hprog1 as [Hv1 | [u1' Hs1]].
    + destruct Hprog2 as [Hv2 | [u2' Hs2]].
      * right. destruct (core_value_int _ _ (has_rtype_erases _ _ _ _ Hty1) Hv1)
          as [n Heq1]. subst t1.
        destruct (core_value_int _ _ (has_rtype_erases _ _ _ _ Hty2) Hv2)
          as [m Heq2]. subst t2.
        (* the refinement on the divisor supplies nonzeroness *)
        eexists. apply ST_DivInt.
        eapply typed_nonzero_integer_value_context; eauto.
      * right. exists (tm_div t1 u2'). apply ST_Div2; assumption.
    + right. exists (tm_div u1' t2). apply ST_Div1; [exact Hs1 | unfold locally_closed_tm; exact H4].
  - (* arithmetic *)
    inversion Hlc; subst. unfold locally_closed_tm in *.
    simpl in Hfv. apply app_eq_nil in Hfv as [Hfv1 Hfv2].
    assert (Hloc2 : locally_closed_tm t2) by (unfold locally_closed_tm; eassumption).
    assert (Hprog1 : value t1 \/ exists u, t1 --> u)
      by (eapply IHHty1; eauto).
    assert (Hprog2 : value t2 \/ exists u, t2 --> u)
      by (eapply IHHty2; eauto).
    destruct Hprog1 as [Hv1 | [u1' Hs1]].
    + destruct Hprog2 as [Hv2 | [u2' Hs2]].
      * right. destruct (core_value_int _ _ (has_rtype_erases _ _ _ _ Hty1) Hv1)
          as [n Heq1]. subst t1.
        destruct (core_value_int _ _ (has_rtype_erases _ _ _ _ Hty2) Hv2)
          as [m Heq2]. subst t2.
        eexists. apply ST_ArithInt.
      * right. exists (tm_arith op t1 u2'). apply ST_Arith2; assumption.
    + right. exists (tm_arith op u1' t2). apply ST_Arith1; [exact Hs1 | exact Hloc2].
  - (* subsumption *)
    eapply IHHty; eauto.
Qed.

Lemma typed_nonzero_integer_value : forall n,
  has_rtype [] [] (tm_int n)
    (R_Refine Ty_Int (Pred_Ne (tm_bvar 0) (tm_int 0%Z))) -> n <> 0%Z.
Proof.
  intros n Hty.
  pose proof (proj1 value_fundamental_mutual [] [] (tm_int n)
    (R_Refine Ty_Int (Pred_Ne (tm_bvar 0) (tm_int 0%Z))) Hty) as Hfund.
  assert (Hctx : logical_context_interpretation identity_term_substitution []).
  { intros x R Hlook. discriminate. }
  specialize (Hfund identity_term_substitution
    identity_term_substitution_closed Hctx (v_int n)).
  cbn [instantiate identity_type_substitution identity_term_substitution
    instantiate_rty instantiate_ty] in Hfund.
  apply logical_value_nonzero_integer with (n := n). exact Hfund.
Qed.

Lemma multistep_safety_conditional : forall t t' R,
  has_rtype [] empty_rcontext t R ->
  multi t t' ->
  (forall u u' S, has_rtype [] empty_rcontext u S -> u --> u' ->
    has_rtype [] empty_rcontext u' S) ->
  (forall n, has_rtype [] [] (tm_int n)
    (R_Refine Ty_Int (Pred_Ne (tm_bvar 0) (tm_int 0%Z))) -> n <> 0%Z) ->
  value t' \/ exists t'', t' --> t''.
Proof.
  intros t t' R Htyping Hsteps. induction Hsteps; intros Hpres Hsafe.
  - eapply refinement_progress with (R := R) (RGamma := empty_rcontext)
      (gamma := identity_term_substitution).
    + exact Htyping.
    + apply has_rtype_locally_closed with (R := R). exact Htyping.
    + exact identity_term_substitution_closed.
    + intros x Q Hlook. discriminate.
  - eapply IHHsteps.
    + exact (Hpres t1 t2 R Htyping H).
    + exact Hpres.
    + exact Hsafe.
Qed.

Theorem never_stuck : forall (t t' : tm) (R : rty),
  has_rtype [] empty_rcontext t R ->
  multi t t' ->
  value t' \/ exists t'' : tm, t' --> t''.
Proof.
  intros t t' R Htyping Hsteps.
  eapply multistep_safety_conditional; eauto using typed_nonzero_integer_value.
Qed.

End SystemFRefinementTask.
