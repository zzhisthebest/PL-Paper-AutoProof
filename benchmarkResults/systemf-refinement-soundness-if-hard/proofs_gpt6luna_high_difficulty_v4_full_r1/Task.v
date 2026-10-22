From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
From Stdlib Require Import ZArith.BinInt.
From Stdlib Require Import Program.Equality.

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

Lemma lc_ty_at_weaken : forall K T, lc_ty_at K T -> forall K', K <= K' -> lc_ty_at K' T.
Proof.
  intros K T Hlc. induction Hlc; intros K' Hle.
  - constructor. lia.
  - constructor.
  - constructor; [eapply IHHlc1|eapply IHHlc2]; eauto.
  - constructor. eapply IHHlc. lia.
  - constructor.
  - constructor.
Qed.

Lemma lc_tm_at_weaken : forall K k t, lc_tm_at K k t ->
  forall K' k', K <= K' -> k <= k' -> lc_tm_at K' k' t.
Proof.
  intros K k t Hlc. induction Hlc; intros K' k' HK Hk.
  - constructor. lia.
  - constructor.
  - constructor.
    + eapply lc_ty_at_weaken; eauto.
    + eapply IHHlc. lia. lia.
  - constructor; [eapply IHHlc1|eapply IHHlc2]; eauto.
  - constructor. eapply IHHlc. lia. exact Hk.
  - constructor.
    + eapply IHHlc; eauto.
    + eapply lc_ty_at_weaken; eauto.
  - constructor.
  - constructor; [eapply IHHlc1|eapply IHHlc2]; eauto.
  - constructor; [eapply IHHlc1|eapply IHHlc2]; eauto.
  - constructor.
  - constructor.
  - constructor; [eapply IHHlc1|eapply IHHlc2|eapply IHHlc3]; eauto.
Qed.

Lemma lc_tm_subst : forall K k t, lc_tm_at K k t -> forall x s,
  locally_closed_tm s -> lc_tm_at K k (tm_subst x s t).
Proof.
  intros K k t Hlc. induction Hlc; intros z s Hs; simpl.
  - constructor; assumption.
  - destruct (Nat.eqb z x).
    + eapply lc_tm_at_weaken; [exact Hs|lia|lia].
    + constructor.
  - constructor.
    + assumption.
    + eapply IHHlc; exact Hs.
  - constructor; [eapply IHHlc1|eapply IHHlc2]; eauto.
  - constructor. eapply IHHlc; exact Hs.
  - constructor; [eapply IHHlc; exact Hs|assumption].
  - constructor.
  - constructor; [eapply IHHlc1|eapply IHHlc2]; eauto.
  - constructor; [eapply IHHlc1|eapply IHHlc2]; eauto.
  - constructor.
  - constructor.
  - constructor; [eapply IHHlc1|eapply IHHlc2|eapply IHHlc3]; eauto.
Qed.



Lemma lc_tm_open_rec_identity : forall K j t,
  lc_tm_at K j t -> forall k u, j <= k -> open_tm_rec k u t = t.
Proof.
  intros K j t Hlc. induction Hlc; intros kk u Hle; simpl.
  - destruct (Nat.eqb kk i) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
  - reflexivity.
  - rewrite (IHHlc (S kk) u (le_n_S _ _ Hle)). reflexivity.
  - rewrite (IHHlc1 kk u Hle), (IHHlc2 kk u Hle). reflexivity.
  - rewrite (IHHlc kk u Hle). reflexivity.
  - rewrite (IHHlc kk u Hle). reflexivity.
  - reflexivity.
  - rewrite (IHHlc1 kk u Hle), (IHHlc2 kk u Hle). reflexivity.
  - rewrite (IHHlc1 kk u Hle), (IHHlc2 kk u Hle). reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite (IHHlc1 kk u Hle), (IHHlc2 kk u Hle), (IHHlc3 kk u Hle). reflexivity.
Qed.

Lemma tm_subst_open_tm_rec_comm_lc : forall t k u x s,
  locally_closed_tm s ->
  tm_subst x s (open_tm_rec k u t) =
  open_tm_rec k (tm_subst x s u) (tm_subst x s t).
Proof.
  induction t; intros k u x s Hlc; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E. subst a. unfold locally_closed_tm in Hlc.
      rewrite (lc_tm_open_rec_identity 0 0 s Hlc k (tm_subst x s u) (le_0_n k)). reflexivity.
    + reflexivity.
  - rewrite IHt; [reflexivity|assumption].
  - rewrite IHt1, IHt2; [reflexivity|assumption|assumption].
  - rewrite IHt; [reflexivity|assumption].
  - rewrite IHt; [reflexivity|assumption].
  - reflexivity.
  - rewrite IHt1, IHt2; [reflexivity|assumption|assumption].
  - rewrite IHt1, IHt2; [reflexivity|assumption|assumption].
  - reflexivity.
  - reflexivity.
  - rewrite IHt1, IHt2, IHt3; [reflexivity|assumption|assumption|assumption].
Qed.

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

Lemma value_tm_subst : forall v x s,
  value v -> locally_closed_tm s -> value (tm_subst x s v).
Proof.
  intros v x s Hv Hs. inversion Hv; subst; simpl.
  - apply v_abs. change (lc_tm_at 0 0 (tm_subst x s (tm_abs T t))).
    eapply lc_tm_subst; eassumption.
  - apply v_tabs. change (lc_tm_at 0 0 (tm_subst x s (tm_tabs t))).
    eapply lc_tm_subst; eassumption.
  - constructor.
  - constructor.
  - constructor.
Qed.

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

Lemma erase_open_rty_tm : forall k u R,
  erase (open_rty_tm_rec k u R) = erase R.
Proof.
  intros k u R; revert k u; induction R; intros; simpl; try rewrite IHR1; try rewrite IHR2; try rewrite IHR; reflexivity.
Qed.

Lemma erase_open_rty_ty_rec : forall k U R,
  erase (open_rty_ty_rec k U R) = open_ty_rec k U (erase R).
Proof.
  intros k U R; revert k U; induction R; intros; simpl; try rewrite IHR1; try rewrite IHR2; try rewrite IHR; reflexivity.
Qed.

Lemma erase_open_rty_ty : forall R U,
  erase (open_rty_ty R U) = open_ty (erase R) U.
Proof. intros; unfold open_rty_ty, open_ty; apply erase_open_rty_ty_rec. Qed.

Lemma value_no_step : forall v t, value v -> ~ v --> t.
Proof. intros v t Hv Hs; inversion Hv; subst; inversion Hs. Qed.

Lemma predicate_multistep_value : forall v u,
  value v -> predicate_multistep v u -> u = v.
Proof.
  intros v u Hv Hm; inversion Hm; subst; auto.
  exfalso; eapply value_no_step; eauto.
Qed.

Lemma nonzero_refinement_int : forall n,
  qualifier_holds
    (open_qualifier_tm (Pred_Ne (tm_bvar 0) (tm_int 0%Z)) (tm_int n)) ->
  n <> 0%Z.
Proof.
  intros n H Hzero; subst n.
  unfold qualifier_holds, predicate_holds, interpret_qualifier,
    operational_atoms, Pred_Ne in H; simpl in H.
  apply H. exists (tm_int 0%Z). repeat split; constructor.
Qed.

Inductive ty_shape : Type :=
| Sh_Var | Sh_Arrow : ty_shape -> ty_shape -> ty_shape
| Sh_All : ty_shape -> ty_shape | Sh_Int | Sh_Bool.

Fixpoint shape_ty (T : ty) : ty_shape :=
  match T with
  | Ty_BVar _ | Ty_FVar _ => Sh_Var
  | Ty_Arrow T1 T2 => Sh_Arrow (shape_ty T1) (shape_ty T2)
  | Ty_All T1 => Sh_All (shape_ty T1)
  | Ty_Int => Sh_Int
  | Ty_Bool => Sh_Bool
  end.


Fixpoint shape_rty (R : rty) : ty_shape :=
  match R with
  | R_Refine T _ => shape_ty T
  | R_Func R1 R2 => Sh_Arrow (shape_rty R1) (shape_rty R2)
  | R_Exists _ R2 => shape_rty R2
  | R_Poly R => Sh_All (shape_rty R)
  end.

Inductive shape_value : ty_shape -> tm -> Prop :=
| SV_Int : forall n, shape_value Sh_Int (tm_int n)
| SV_BoolTrue : shape_value Sh_Bool tm_true
| SV_BoolFalse : shape_value Sh_Bool tm_false
| SV_Arrow : forall A B T body,
    locally_closed_tm (tm_abs T body) ->
    shape_value (Sh_Arrow A B) (tm_abs T body)
| SV_All : forall A body,
    locally_closed_tm (tm_tabs body) ->
    shape_value (Sh_All A) (tm_tabs body).

Lemma shape_value_tm_subst : forall S v x s,
  shape_value S v -> locally_closed_tm s ->
  shape_value S (tm_subst x s v).
Proof.
  intros S v x s Hshape Hs. inversion Hshape; subst; simpl.
  - constructor.
  - constructor.
  - constructor.
  - apply SV_Arrow. change (lc_tm_at 0 0 (tm_subst x s (tm_abs T body))).
    eapply lc_tm_subst; eassumption.
  - apply SV_All. change (lc_tm_at 0 0 (tm_subst x s (tm_tabs body))).
    eapply lc_tm_subst; eassumption.
Qed.

Lemma shape_open_ty_rec_fvar : forall k X T,
  shape_ty (open_ty_rec k (Ty_FVar X) T) = shape_ty T.
Proof.
  intros k X T; revert k X; induction T; intros; simpl; auto.
  - destruct (Nat.eqb k n); reflexivity.
  - rewrite IHT1, IHT2; reflexivity.
  - rewrite IHT; reflexivity.
Qed.

Lemma shape_open_rty_tm_rec : forall k u R,
  shape_rty (open_rty_tm_rec k u R) = shape_rty R.
Proof.
  intros k u R; revert k u; induction R; intros; simpl;
    try rewrite IHR1; try rewrite IHR2; try rewrite IHR; reflexivity.
Qed.

Lemma shape_open_rty_ty_rec_fvar : forall k X R,
  shape_rty (open_rty_ty_rec k (Ty_FVar X) R) = shape_rty R.
Proof.
  intros k X R; revert k X; induction R; intros; simpl;
    try rewrite shape_open_ty_rec_fvar; try rewrite IHR1; try rewrite IHR2; try rewrite IHR; reflexivity.
Qed.

Scheme rtype_subtype_ind := Induction for has_rtype Sort Prop
with subtype_mut_ind := Induction for subtype Sort Prop.

Lemma in_le_max_atom : forall x L, In x L -> x <= max_atom L.
Proof.
  intros x L; induction L as [|a L IH]; simpl; intros H; try contradiction.
  destruct H as [->|H]. apply Nat.le_max_l.
  eapply Nat.le_trans; [apply IH; exact H|apply Nat.le_max_r].
Qed.

Lemma fresh_not_in : forall L, ~ In (fresh L) L.
Proof.
  intros L H. unfold fresh in H. pose proof (in_le_max_atom _ _ H). lia.
Qed.

Lemma open_ty_rec_injective_fresh : forall k X T U,
  ~ In X (fv_ty T ++ fv_ty U) ->
  open_ty_rec k (Ty_FVar X) T = open_ty_rec k (Ty_FVar X) U -> T = U.
Proof.
  intros k X T; revert k X; induction T as [i|Y|T1 IH1 T2 IH2|T IH| |].
  - intros k X U Hfresh Heq. destruct U as [j|Z|U1 U2|U| |]; simpl in *.
    + destruct (Nat.eqb k i) eqn:E1, (Nat.eqb k j) eqn:E2; simpl in Heq.
      * apply Nat.eqb_eq in E1; apply Nat.eqb_eq in E2; subst; reflexivity.
      * discriminate.
      * discriminate.
      * inversion Heq; reflexivity.
    + destruct (Nat.eqb k i) eqn:E; simpl in Heq.
      * inversion Heq; subst. exfalso. apply Hfresh. simpl; auto.
      * discriminate.
    + destruct (Nat.eqb k i); simpl in Heq; discriminate.
    + destruct (Nat.eqb k i); simpl in Heq; discriminate.
    + destruct (Nat.eqb k i); simpl in Heq; discriminate.
    + destruct (Nat.eqb k i); simpl in Heq; discriminate.
  - intros k X U Hfresh Heq. destruct U as [j|Z|U1 U2|U| |]; simpl in *.
    + destruct (Nat.eqb k j) eqn:E; simpl in Heq.
      * inversion Heq; subst. exfalso. apply Hfresh. simpl; auto.
      * discriminate.
    + inversion Heq; reflexivity.
    + discriminate.
    + discriminate.
    + discriminate.
    + discriminate.
  - intros k X U Hfresh Heq. destruct U as [j|Z|U1 U2|U| |]; simpl in *.
    + destruct (Nat.eqb k j); simpl in Heq; discriminate.
    + discriminate.
    + inversion Heq; subst. simpl in Hfresh. repeat rewrite in_app_iff in Hfresh.
      assert (HF1 : ~ In X (fv_ty T1 ++ fv_ty U1)) by (intro Hf; apply in_app_iff in Hf; tauto).
      assert (HF2 : ~ In X (fv_ty T2 ++ fv_ty U2)) by (intro Hf; apply in_app_iff in Hf; tauto).
      f_equal; [eapply IH1 | eapply IH2]; eauto.
    + discriminate.
    + discriminate.
    + discriminate.
  - intros k X U Hfresh Heq. destruct U as [j|Z|U1 U2|U| |]; simpl in *.
    + destruct (Nat.eqb k j); simpl in Heq; discriminate.
    + discriminate.
    + discriminate.
    + inversion Heq; subst. f_equal. eapply IH; eauto.
    + discriminate.
    + discriminate.
  - intros k X U Hfresh Heq. destruct U as [j|Z|U1 U2|U| |]; simpl in *.
    + destruct (Nat.eqb k j); simpl in Heq; discriminate.
    + discriminate.
    + discriminate.
    + discriminate.
    + inversion Heq; reflexivity.
    + discriminate.
  - intros k X U Hfresh Heq. destruct U as [j|Z|U1 U2|U| |]; simpl in *.
    + destruct (Nat.eqb k j); simpl in Heq; discriminate.
    + discriminate.
    + discriminate.
    + discriminate.
    + discriminate.
    + inversion Heq; reflexivity.
Qed.

Lemma subtype_erasure : forall Delta Gamma R S,
  subtype Delta Gamma R S -> erase R = erase S.
Proof.
  intros Delta Gamma R S H.
  induction H using subtype_mut_ind
    with (P := fun _ _ _ _ _ => True)
         (P0 := fun _ _ R S _ => erase R = erase S);
    simpl in *; try exact I; try congruence.
  - rewrite IHsubtype. f_equal. specialize (H0 (fresh L) (fresh_not_in L)).
    unfold open_rty_tm in H0. rewrite !erase_open_rty_tm in H0. exact H0.
  - unfold open_rty_tm in IHsubtype0. rewrite erase_open_rty_tm in IHsubtype0. exact IHsubtype0.
  - specialize (H (fresh L) (fresh_not_in L)).
    unfold open_rty_tm in H. rewrite erase_open_rty_tm in H. exact H.
  - set (X := fresh (L ++ fv_ty (erase R) ++ fv_ty (erase S))).
    assert (HX : ~ In X L).
    { intro Hin. apply (fresh_not_in (L ++ fv_ty (erase R) ++ fv_ty (erase S))).
      apply in_or_app; left; exact Hin. }
    assert (HF : ~ In X (fv_ty (erase R) ++ fv_ty (erase S))).
    { intro Hin. apply (fresh_not_in (L ++ fv_ty (erase R) ++ fv_ty (erase S))).
      apply in_or_app; right; exact Hin. }
    specialize (H X HX). rewrite !erase_open_rty_ty in H. unfold open_ty in H.
    f_equal. eapply open_ty_rec_injective_fresh; eauto.
Qed.

Lemma subtype_shape : forall Delta Gamma R S,
  subtype Delta Gamma R S -> shape_rty R = shape_rty S.
Proof.
  intros Delta Gamma R S H.
  induction H using subtype_mut_ind
    with (P := fun _ _ _ _ _ => True)
         (P0 := fun _ _ R S _ => shape_rty R = shape_rty S);
    simpl in *; try exact I; try congruence.
  - rewrite IHsubtype. f_equal. specialize (H0 (fresh L) (fresh_not_in L)).
    unfold open_rty_tm in H0. rewrite !shape_open_rty_tm_rec in H0. exact H0.
  - unfold open_rty_tm in IHsubtype0. rewrite shape_open_rty_tm_rec in IHsubtype0. exact IHsubtype0.
  - specialize (H (fresh L) (fresh_not_in L)).
    unfold open_rty_tm in H. rewrite !shape_open_rty_tm_rec in H. exact H.
  - specialize (H (fresh L) (fresh_not_in L)).
    unfold open_rty_ty in H. rewrite !shape_open_rty_ty_rec_fvar in H. f_equal; exact H.
Qed.

Lemma wf_rty_erasure : forall Delta Gamma R,
  wf_rty Delta Gamma R -> wf_ty Delta (erase R).
Proof.
  intros Delta Gamma R H; induction H; simpl.
  - assumption.
  - apply WF_Arrow; [assumption|].
    specialize (H1 (fresh L) (fresh_not_in L)).
    unfold open_rty_tm in H1. rewrite erase_open_rty_tm in H1. exact H1.
  - specialize (H1 (fresh L) (fresh_not_in L)).
    unfold open_rty_tm in H1. rewrite erase_open_rty_tm in H1. exact H1.
  - apply WF_All with (L := L). intros X HX.
    specialize (H0 X HX). rewrite erase_open_rty_ty in H0. exact H0.
Qed.

Lemma lookup_erased_context : forall x RGamma R,
  lookup_rcontext x RGamma = Some R ->
  lookup_context x (erase_context RGamma) = Some (erase R).
Proof.
  intros x RGamma; induction RGamma as [|[y S] RGamma IH]; simpl; intros R H; try discriminate.
  destruct (Nat.eqb x y) eqn:E.
  - inversion H; reflexivity.
  - eapply IH; eauto.
Qed.

Lemma rtype_core_typing : forall Delta RGamma t R,
  has_rtype Delta RGamma t R ->
  has_type Delta (erase_context RGamma) t (erase R).
Proof.
  intros Delta RGamma t R H.
  induction H using rtype_subtype_ind
    with (P := fun Delta RGamma t R _ => has_type Delta (erase_context RGamma) t (erase R))
         (P0 := fun _ _ _ _ _ => True); simpl in *; try exact I.
  - eapply T_Var; [eapply lookup_erased_context; eassumption|eapply wf_rty_erasure; eassumption].
  - apply T_Abs with (L := L).
    + eapply wf_rty_erasure; eassumption.
    + intros x Hx. specialize (H x Hx).
      unfold open_rty_tm in H. rewrite erase_open_rty_tm in H. exact H.
  - eapply T_App; eassumption.
  - apply T_TAbs with (L := L). intros X HX.
    specialize (H X HX). rewrite erase_open_rty_ty in H. exact H.
  - rewrite erase_open_rty_ty. eapply T_TApp; eauto.
  - constructor.
  - eapply T_Div; eassumption.
  - eapply T_Arith; eassumption.
  - constructor.
  - constructor.
  - eapply T_If; eassumption.
  - assumption.
  - rewrite <- (subtype_erasure Delta RGamma R S s). exact IHhas_rtype.
Qed.

Lemma canonical_int : forall Delta Gamma v T,
  has_type Delta Gamma v T -> value v -> shape_ty T = Sh_Int ->
  exists n, v = tm_int n.
Proof.
  intros Delta Gamma v T HT HV HS. inversion HV; subst; inversion HT; subst; simpl in HS; try discriminate.
  eexists; reflexivity.
Qed.

Lemma canonical_bool : forall Delta Gamma v T,
  has_type Delta Gamma v T -> value v -> shape_ty T = Sh_Bool ->
  v = tm_true \/ v = tm_false.
Proof.
  intros Delta Gamma v T HT HV HS. inversion HV; subst; inversion HT; subst; simpl in HS; try discriminate; auto.
Qed.

Lemma canonical_fun : forall Delta Gamma v T,
  has_type Delta Gamma v T -> value v ->
  (exists A B, shape_ty T = Sh_Arrow A B) ->
  exists A body, v = tm_abs A body.
Proof.
  intros Delta Gamma v T HT HV [A [B HS]].
  inversion HV; subst; inversion HT; subst; simpl in HS; try discriminate.
  eexists; eexists; reflexivity.
Qed.

Lemma shape_erase : forall R, shape_ty (erase R) = shape_rty R.
Proof. intros R; induction R; simpl; try rewrite IHR1; try rewrite IHR2; try rewrite IHR; reflexivity. Qed.

Lemma rtype_canonical_int : forall v R,
  has_rtype [] empty_rcontext v R -> value v -> shape_rty R = Sh_Int ->
  exists n, v = tm_int n.
Proof.
  intros v R HR HV HS.
  pose proof (rtype_core_typing _ _ _ _ HR) as HT.
  destruct (canonical_int [] empty v (erase R) HT HV
    ltac:(rewrite shape_erase; exact HS)) as [n Hn].
  exists n. exact Hn.
Qed.

Lemma rtype_canonical_bool : forall v R,
  has_rtype [] empty_rcontext v R -> value v -> shape_rty R = Sh_Bool ->
  v = tm_true \/ v = tm_false.
Proof.
  intros v R HR HV HS.
  pose proof (rtype_core_typing _ _ _ _ HR) as HT.
  eapply canonical_bool; [exact HT|exact HV|].
  rewrite shape_erase. exact HS.
Qed.

Lemma rtype_canonical_fun : forall v R A B,
  has_rtype [] empty_rcontext v R -> value v ->
  shape_rty R = Sh_Arrow A B ->
  exists T body, v = tm_abs T body.
Proof.
  intros v R A B HR HV HS.
  pose proof (rtype_core_typing _ _ _ _ HR) as HT.
  eapply canonical_fun; [exact HT|exact HV|].
  exists A, B. rewrite shape_erase. exact HS.
Qed.

Lemma canonical_tabs : forall Delta Gamma v T A,
  has_type Delta Gamma v T -> value v -> shape_ty T = Sh_All A ->
  exists body, v = tm_tabs body.
Proof.
  intros Delta Gamma v T A HT HV HS.
  inversion HV; subst; inversion HT; subst; simpl in HS; try discriminate.
  eexists; reflexivity.
Qed.

Lemma core_value_has_shape : forall Delta Gamma v T,
  has_type Delta Gamma v T -> value v -> shape_value (shape_ty T) v.
Proof.
  intros Delta Gamma v T HT HV.
  inversion HV; subst; inversion HT; subst; simpl in *; try discriminate.
  - apply SV_Arrow. assumption.
  - apply SV_All. assumption.
  - constructor.
  - constructor.
  - constructor.
Qed.

Lemma rtype_canonical_tabs : forall v R A,
  has_rtype [] empty_rcontext v R -> value v -> shape_rty R = Sh_All A ->
  exists body, v = tm_tabs body.
Proof.
  intros v R A HR HV HS.
  pose proof (rtype_core_typing _ _ _ _ HR) as HT.
  eapply canonical_tabs; [exact HT|exact HV|].
  rewrite shape_erase. exact HS.
Qed.

Lemma rtype_value_has_shape : forall v R,
  has_rtype [] empty_rcontext v R -> value v -> shape_value (shape_rty R) v.
Proof.
  intros v R HR HV. pose proof (rtype_core_typing _ _ _ _ HR) as HT.
  pose proof (core_value_has_shape _ _ _ _ HT HV) as Hshape.
  rewrite <- shape_erase. exact Hshape.
Qed.



Lemma lc_ty_open_fvar_inv : forall K X T,
  lc_ty_at K (open_ty_rec K (Ty_FVar X) T) -> lc_ty_at (S K) T.
Proof.
  intros K X T; revert K X; induction T as [i|Y|T1 IH1 T2 IH2|T IH| |];
    intros K X H; simpl in H.
  - destruct (Nat.eqb K i) eqn:E.
    + apply Nat.eqb_eq in E. subst i. constructor; lia.
    + inversion H; subst. constructor. lia.
  - constructor.
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor. eapply IH. exact H2.
  - constructor.
  - constructor.
Qed.

Lemma wf_ty_locally_closed : forall Delta T, wf_ty Delta T -> lc_ty_at 0 T.
Proof.
  intros Delta T Hwf; induction Hwf; simpl.
  - constructor.
  - constructor; assumption.
  - constructor. specialize (H0 (fresh L) (fresh_not_in L)).
    eapply lc_ty_open_fvar_inv; exact H0.
  - constructor.
  - constructor.
Qed.

Lemma lc_tm_open_fvar_inv : forall K k x t,
  lc_tm_at K k (open_tm_rec k (tm_fvar x) t) -> lc_tm_at K (S k) t.
Proof.
  intros K k x t; revert K k; induction t; intros K k H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. constructor; lia.
    + inversion H; subst. constructor. lia.
  - constructor.
  - inversion H; subst. constructor; [assumption|]. eapply IHt; eassumption.
  - inversion H; subst. constructor; [eapply IHt1|eapply IHt2]; eassumption.
  - inversion H; subst. constructor. eapply IHt; eassumption.
  - inversion H; subst. constructor; [eapply IHt; eassumption|assumption].
  - constructor.
  - inversion H; subst. constructor; [eapply IHt1|eapply IHt2]; eassumption.
  - inversion H; subst. constructor; [eapply IHt1|eapply IHt2]; eassumption.
  - constructor.
  - constructor.
  - inversion H; subst. constructor; [eapply IHt1|eapply IHt2|eapply IHt3]; eassumption.
Qed.

Lemma lc_tm_ty_open_fvar_inv : forall K k X t,
  lc_tm_at K k (open_tm_ty_rec K (Ty_FVar X) t) -> lc_tm_at (S K) k t.
Proof.
  intros K k X t; revert K k; induction t; intros K k H; simpl in H.
  - inversion H; subst. constructor; assumption.
  - inversion H; subst. constructor; assumption.
  - inversion H; subst. constructor.
    + eapply lc_ty_open_fvar_inv; eassumption.
    + eapply IHt; eassumption.
  - inversion H; subst. constructor; [eapply IHt1|eapply IHt2]; eassumption.
  - inversion H; subst. constructor. eapply IHt; eassumption.
  - inversion H; subst. constructor; [eapply IHt; eassumption|eapply lc_ty_open_fvar_inv; eassumption].
  - constructor.
  - inversion H; subst. constructor; [eapply IHt1|eapply IHt2]; eassumption.
  - inversion H; subst. constructor; [eapply IHt1|eapply IHt2]; eassumption.
  - constructor.
  - constructor.
  - inversion H; subst. constructor; [eapply IHt1|eapply IHt2|eapply IHt3]; eassumption.
Qed.

Lemma has_type_locally_closed : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T H; induction H.
  - constructor.
  - unfold locally_closed_tm. constructor.
    + eapply wf_ty_locally_closed; eassumption.
    + specialize (H1 (fresh L) (fresh_not_in L)).
      eapply lc_tm_open_fvar_inv; exact H1.
  - constructor; assumption.
  - unfold locally_closed_tm. constructor.
    specialize (H0 (fresh L) (fresh_not_in L)).
    eapply lc_tm_ty_open_fvar_inv; exact H0.
  - constructor; [assumption|eapply wf_ty_locally_closed; eassumption].
  - constructor.
  - constructor; assumption.
  - constructor; assumption.
  - constructor.
  - constructor.
  - constructor; assumption.
Qed.

Fixpoint qualifier_fv (p : qualifier) : list atom :=
  match p with
  | Pred_True | Pred_False => []
  | Pred_Eq t1 t2 | Pred_Lt t1 t2 | Pred_Le t1 t2 => fv_tm t1 ++ fv_tm t2
  | Pred_And p1 p2 | Pred_Or p1 p2 => qualifier_fv p1 ++ qualifier_fv p2
  | Pred_Not p1 => qualifier_fv p1
  end.

Definition rcontext_satisfies (RGamma : rcontext)
    (atoms : atom_interpretation) : Prop :=
  forall x T p,
    lookup_rcontext x RGamma = Some (R_Refine T p) ->
    interpret_qualifier atoms (open_qualifier_tm p (tm_fvar x)).

Lemma empty_rcontext_satisfies : forall atoms,
  rcontext_satisfies empty_rcontext atoms.
Proof. intros atoms x T p H; discriminate. Qed.

Fixpoint rcontext_support (RGamma : rcontext) : list atom :=
  match RGamma with
  | [] => []
  | (x, R) :: G' =>
      x :: (match R with
            | R_Refine _ p => qualifier_fv (open_qualifier_tm p (tm_fvar x))
            | _ => []
            end ++ rcontext_support G')
  end.

Lemma lookup_rcontext_support : forall RGamma x T p,
  lookup_rcontext x RGamma = Some (R_Refine T p) ->
  forall y, In y (qualifier_fv (open_qualifier_tm p (tm_fvar x))) ->
    In y (rcontext_support RGamma).
Proof.
  induction RGamma as [|[z R] G IH]; intros x T p Hlookup y Hy; simpl in *; try discriminate.
  destruct (Nat.eqb x z) eqn:E.
  - apply Nat.eqb_eq in E. subst x. inversion Hlookup; subst.
    simpl. right. apply in_or_app. left. exact Hy.
  - right. apply in_or_app. right. eapply IH; eauto.
Qed.

Lemma rcontext_support_fresh : forall RGamma x,
  ~ In x (rcontext_support RGamma) ->
  forall y T p, lookup_rcontext y RGamma = Some (R_Refine T p) ->
    ~ In x (qualifier_fv (open_qualifier_tm p (tm_fvar y))).
Proof.
  intros RGamma x Hfresh y T p Hlookup Hin.
  apply Hfresh. eapply (lookup_rcontext_support RGamma y T p Hlookup x). exact Hin.
Qed.

Lemma entails_sound : forall Delta RGamma p q atoms,
  rcontext_satisfies RGamma atoms -> entails Delta RGamma p q ->
  (interpret_qualifier atoms p -> interpret_qualifier atoms q).
Proof.
  intros Delta RGamma p q atoms Hctx Hent.
  induction Hent; simpl; intros Hp.
  - exact Hp.
  - exact I.
  - apply (IHHent2 Hctx). apply (IHHent1 Hctx). exact Hp.
  - exact (proj1 Hp).
  - exact (proj2 Hp).
  - split; [apply (IHHent1 Hctx)|apply (IHHent2 Hctx)]; exact Hp.
  - left; exact Hp.
  - right; exact Hp.
  - destruct Hp as [Hp|Hq]; [apply (IHHent1 Hctx)|apply (IHHent2 Hctx)]; assumption.
  - intro Hq. apply (IHHent Hctx). split; assumption.
  - destruct Hp as [Hp Hnot]. exfalso. apply Hnot. exact Hp.
  - eapply Hctx; eassumption.
  - contradiction.
Qed.

Lemma rcontext_satisfies_true_extend : forall RGamma atoms x T,
  rcontext_satisfies RGamma atoms ->
  rcontext_satisfies (update_rcontext RGamma x (R_Refine T Pred_True)) atoms.
Proof.
  intros RGamma atoms x T Hctx y U p Hlookup.
  unfold update_rcontext in Hlookup. simpl in Hlookup.
  destruct (Nat.eqb y x) eqn:E.
  - inversion Hlookup; subst. simpl. exact I.
  - eapply Hctx; eassumption.
Qed.

Lemma rcontext_satisfies_extend : forall RGamma atoms x R,
  rcontext_satisfies RGamma atoms ->
  (forall T p, R = R_Refine T p ->
    interpret_qualifier atoms (open_qualifier_tm p (tm_fvar x))) ->
  rcontext_satisfies (update_rcontext RGamma x R) atoms.
Proof.
  intros RGamma atoms x R Hold Hnew y T p Hlookup.
  unfold update_rcontext in Hlookup. simpl in Hlookup.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst y. inversion Hlookup; subst. eapply Hnew. reflexivity.
  - eapply Hold; eassumption.
Qed.

Lemma tm_subst_open_tm_rec_fresh : forall t k x v,
  ~ In x (fv_tm t) ->
  tm_subst x v (open_tm_rec k (tm_fvar x) t) = open_tm_rec k v t.
Proof.
  induction t; intros k x v Hfresh; simpl in *.
  - destruct (Nat.eqb k n); [|reflexivity].
    destruct (Nat.eqb x x) eqn:Ex.
    + unfold tm_subst; simpl. rewrite Ex. reflexivity.
    + apply Nat.eqb_neq in Ex; contradiction.
  - assert (x <> a) by (intro E; subst; apply Hfresh; simpl; auto).
    destruct (Nat.eqb x a) eqn:E; [apply Nat.eqb_eq in E; contradiction|reflexivity].
  - rewrite IHt; auto.
  - rewrite IHt1, IHt2; [reflexivity| |]; intro H; apply Hfresh; simpl; apply in_or_app; auto.
  - rewrite IHt; auto.
  - rewrite IHt; auto.
  - reflexivity.
  - rewrite IHt1, IHt2; [reflexivity| |]; intro H; apply Hfresh; simpl; apply in_or_app; auto.
  - rewrite IHt1, IHt2; [reflexivity| |]; intro H; apply Hfresh; simpl; apply in_or_app; auto.
  - reflexivity.
  - reflexivity.
  - rewrite IHt1, IHt2, IHt3; [reflexivity| | |].
    + intro H; apply Hfresh; simpl; repeat rewrite in_app_iff; tauto.
    + intro H; apply Hfresh; simpl; repeat rewrite in_app_iff; tauto.
    + intro H; apply Hfresh; simpl; repeat rewrite in_app_iff; tauto.
Qed.

Lemma tm_subst_fresh : forall t x v,
  ~ In x (fv_tm t) -> tm_subst x v t = t.
Proof.
  induction t; intros x v Hfresh; simpl in *.
  - reflexivity.
  - assert (x <> a) by (intro E; subst; apply Hfresh; simpl; auto).
    destruct (Nat.eqb x a) eqn:E; [apply Nat.eqb_eq in E; contradiction|reflexivity].
  - rewrite IHt; auto.
  - rewrite IHt1, IHt2; [reflexivity| |]; intro H; apply Hfresh; simpl; apply in_or_app; auto.
  - rewrite IHt; auto.
  - rewrite IHt; auto.
  - reflexivity.
  - rewrite IHt1, IHt2; [reflexivity| |]; intro H; apply Hfresh; simpl; apply in_or_app; auto.
  - rewrite IHt1, IHt2; [reflexivity| |]; intro H; apply Hfresh; simpl; apply in_or_app; auto.
  - reflexivity.
  - reflexivity.
  - rewrite IHt1, IHt2, IHt3; [reflexivity| | |].
    + intro H; apply Hfresh; simpl; repeat rewrite in_app_iff; tauto.
    + intro H; apply Hfresh; simpl; repeat rewrite in_app_iff; tauto.
    + intro H; apply Hfresh; simpl; repeat rewrite in_app_iff; tauto.
Qed.




Lemma qualifier_subst_fresh : forall p x v,
  ~ In x (qualifier_fv p) -> qualifier_subst x v p = p.
Proof.
  induction p; intros x v Hfresh; simpl in *; try reflexivity.
  - f_equal.
    + rewrite tm_subst_fresh; [reflexivity|intro H; apply Hfresh; apply in_or_app; left; exact H].
    + rewrite tm_subst_fresh; [reflexivity|intro H; apply Hfresh; apply in_or_app; right; exact H].
  - f_equal.
    + rewrite tm_subst_fresh; [reflexivity|intro H; apply Hfresh; apply in_or_app; left; exact H].
    + rewrite tm_subst_fresh; [reflexivity|intro H; apply Hfresh; apply in_or_app; right; exact H].
  - f_equal.
    + rewrite tm_subst_fresh; [reflexivity|intro H; apply Hfresh; apply in_or_app; left; exact H].
    + rewrite tm_subst_fresh; [reflexivity|intro H; apply Hfresh; apply in_or_app; right; exact H].
  - f_equal; [apply IHp1|apply IHp2]; intro H; apply Hfresh; apply in_or_app; auto.
  - f_equal; [apply IHp1|apply IHp2]; intro H; apply Hfresh; apply in_or_app; auto.
  - f_equal. apply IHp. exact Hfresh.
Qed.

Lemma predicate_closed_qualifier_fv_nil : forall p,
  predicate_closed p -> qualifier_fv p = [].
Proof.
  induction p; simpl; intros H; try reflexivity.
  - destruct H as [_ [H1 [_ [_ [H2 _]]]]]. rewrite H1, H2; reflexivity.
  - destruct H as [_ [H1 [_ [_ [H2 _]]]]]. rewrite H1, H2; reflexivity.
  - destruct H as [_ [H1 [_ [_ [H2 _]]]]]. rewrite H1, H2; reflexivity.
  - destruct H as [H1 H2]. rewrite IHp1, IHp2 by assumption. reflexivity.
  - destruct H as [H1 H2]. rewrite IHp1, IHp2 by assumption. reflexivity.
  - rewrite IHp by assumption. reflexivity.
Qed.

Definition atoms_agree_closed (atoms : atom_interpretation) : Prop :=
  forall p, predicate_closed p ->
    (interpret_qualifier atoms p <-> predicate_holds p).



Lemma qualifier_subst_open_fresh : forall p x v,
  ~ In x (qualifier_fv p) ->
  qualifier_subst x v (open_qualifier_tm p (tm_fvar x)) =
  open_qualifier_tm p v.
Proof.
  induction p; intros x v Hfresh; simpl in *;
    unfold open_qualifier_tm, open_qualifier_tm_rec, open_pred_tm in *;
    simpl in *; try reflexivity.
  - f_equal.
    + eapply tm_subst_open_tm_rec_fresh. intro H; apply Hfresh. apply in_or_app; left; exact H.
    + eapply tm_subst_open_tm_rec_fresh. intro H; apply Hfresh. apply in_or_app; right; exact H.
  - f_equal.
    + eapply tm_subst_open_tm_rec_fresh. intro H; apply Hfresh. apply in_or_app; left; exact H.
    + eapply tm_subst_open_tm_rec_fresh. intro H; apply Hfresh. apply in_or_app; right; exact H.
  - f_equal.
    + eapply tm_subst_open_tm_rec_fresh. intro H; apply Hfresh. apply in_or_app; left; exact H.
    + eapply tm_subst_open_tm_rec_fresh. intro H; apply Hfresh. apply in_or_app; right; exact H.
  - f_equal; [apply IHp1|apply IHp2]; intro H; apply Hfresh; apply in_or_app; auto.
  - f_equal; [apply IHp1|apply IHp2]; intro H; apply Hfresh; apply in_or_app; auto.
  - f_equal. apply IHp. exact Hfresh.
Qed.

Lemma qualifier_subst_open_rec_fresh : forall p k x v,
  ~ In x (qualifier_fv p) ->
  qualifier_subst x v (open_qualifier_tm_rec k (tm_fvar x) p) =
  open_qualifier_tm_rec k v p.
Proof.
  induction p; intros k x v Hfresh; simpl in *;
    unfold open_qualifier_tm_rec, open_pred_tm_rec, open_pred_tm in *;
    simpl in *; try reflexivity.
  - f_equal.
    + eapply tm_subst_open_tm_rec_fresh. intro H; apply Hfresh; apply in_or_app; left; exact H.
    + eapply tm_subst_open_tm_rec_fresh. intro H; apply Hfresh; apply in_or_app; right; exact H.
  - f_equal.
    + eapply tm_subst_open_tm_rec_fresh. intro H; apply Hfresh; apply in_or_app; left; exact H.
    + eapply tm_subst_open_tm_rec_fresh. intro H; apply Hfresh; apply in_or_app; right; exact H.
  - f_equal.
    + eapply tm_subst_open_tm_rec_fresh. intro H; apply Hfresh; apply in_or_app; left; exact H.
    + eapply tm_subst_open_tm_rec_fresh. intro H; apply Hfresh; apply in_or_app; right; exact H.
  - f_equal.
    + apply IHp1. intro H. apply Hfresh. apply in_or_app; left; exact H.
    + apply IHp2. intro H. apply Hfresh. apply in_or_app; right; exact H.
  - f_equal.
    + apply IHp1. intro H. apply Hfresh. apply in_or_app; left; exact H.
    + apply IHp2. intro H. apply Hfresh. apply in_or_app; right; exact H.
  - f_equal. apply IHp. exact Hfresh.
Qed.

Lemma qualifier_subst_open_rec_comm_lc : forall p k u x s,
  locally_closed_tm s ->
  qualifier_subst x s (open_qualifier_tm_rec k u p) =
  open_qualifier_tm_rec k (tm_subst x s u) (qualifier_subst x s p).
Proof.
  induction p; intros k u x s Hlc; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal; apply tm_subst_open_tm_rec_comm_lc; exact Hlc.
  - f_equal; apply tm_subst_open_tm_rec_comm_lc; exact Hlc.
  - f_equal; apply tm_subst_open_tm_rec_comm_lc; exact Hlc.
  - rewrite (IHp1 k u x s Hlc), (IHp2 k u x s Hlc). reflexivity.
  - rewrite (IHp1 k u x s Hlc), (IHp2 k u x s Hlc). reflexivity.
  - rewrite (IHp k u x s Hlc). reflexivity.
Qed.

Lemma qualifier_subst_open_nested_fresh : forall p k v x s,
  locally_closed_tm s ->
  ~ In x (qualifier_fv p) -> ~ In x (fv_tm v) ->
  qualifier_subst x s
    (open_qualifier_tm_rec 0 v
      (open_qualifier_tm_rec k (tm_fvar x) p)) =
  open_qualifier_tm_rec 0 v (open_qualifier_tm_rec k s p).
Proof.
  intros p k v x s Hlc Hp Hv.
  rewrite qualifier_subst_open_rec_comm_lc by exact Hlc.
  rewrite tm_subst_fresh by exact Hv.
  rewrite qualifier_subst_open_rec_comm_lc by exact Hlc.
  rewrite qualifier_subst_fresh by exact Hp.
  assert (Hxx : tm_subst x s (tm_fvar x) = s).
  { unfold tm_subst; simpl. destruct (Nat.eqb x x) eqn:E.
    - reflexivity.
    - apply Nat.eqb_neq in E. contradiction. }
  rewrite Hxx.
  reflexivity.
Qed.

Fixpoint rty_qualifier_fv (R : rty) : list atom :=
  match R with
  | R_Refine _ p => qualifier_fv p
  | R_Func R1 R2 | R_Exists R1 R2 => rty_qualifier_fv R1 ++ rty_qualifier_fv R2
  | R_Poly R1 => rty_qualifier_fv R1
  end.

Lemma shape_rty_subst_tm : forall R x s,
  shape_rty (rty_subst x s R) = shape_rty R.
Proof.
  induction R; intros; simpl; try rewrite IHR1; try rewrite IHR2; try rewrite IHR; reflexivity.
Qed.

Lemma rty_subst_open_rty_tm_rec_fresh : forall R k x v,
  ~ In x (rty_qualifier_fv R) ->
  rty_subst x v (open_rty_tm_rec k (tm_fvar x) R) =
  open_rty_tm_rec k v R.
Proof.
  induction R; intros k x v Hfresh; simpl in *.
  - f_equal. apply qualifier_subst_open_rec_fresh. exact Hfresh.
  - f_equal.
    + apply IHR1. intro H. apply Hfresh. apply in_or_app; left; exact H.
    + apply IHR2. intro H. apply Hfresh. apply in_or_app; right; exact H.
  - f_equal.
    + apply IHR1. intro H. apply Hfresh. apply in_or_app; left; exact H.
    + apply IHR2. intro H. apply Hfresh. apply in_or_app; right; exact H.
  - f_equal. apply IHR. exact Hfresh.
Qed.

Lemma rty_subst_open_rty_tm_rec_comm_lc : forall R k u x s,
  locally_closed_tm s ->
  rty_subst x s (open_rty_tm_rec k u R) =
  open_rty_tm_rec k (tm_subst x s u) (rty_subst x s R).
Proof.
  induction R; intros k u x s Hlc; simpl.
  - f_equal. apply qualifier_subst_open_rec_comm_lc. exact Hlc.
  - f_equal.
    + apply IHR1. exact Hlc.
    + apply IHR2. exact Hlc.
  - f_equal.
    + apply IHR1. exact Hlc.
    + apply IHR2. exact Hlc.
  - f_equal. apply IHR. exact Hlc.
Qed.

Definition subst_atoms (x : atom) (v : tm) : atom_interpretation := {| 
  interpret_eq := fun t1 t2 =>
    interpret_eq operational_atoms (tm_subst x v t1) (tm_subst x v t2);
  interpret_lt := fun t1 t2 =>
    interpret_lt operational_atoms (tm_subst x v t1) (tm_subst x v t2);
  interpret_le := fun t1 t2 =>
    interpret_le operational_atoms (tm_subst x v t1) (tm_subst x v t2)
|}.

Definition subst_atoms_from (atoms : atom_interpretation) (x : atom) (v : tm)
  : atom_interpretation := {| 
  interpret_eq := fun t1 t2 =>
    interpret_eq atoms (tm_subst x v t1) (tm_subst x v t2);
  interpret_lt := fun t1 t2 =>
    interpret_lt atoms (tm_subst x v t1) (tm_subst x v t2);
  interpret_le := fun t1 t2 =>
    interpret_le atoms (tm_subst x v t1) (tm_subst x v t2)
|}.

Lemma interpret_qualifier_subst_atoms_from : forall atoms p x v,
  interpret_qualifier (subst_atoms_from atoms x v) p =
  interpret_qualifier atoms (qualifier_subst x v p).
Proof.
  induction p; intros; simpl.
  - reflexivity.
  - reflexivity.
  - unfold subst_atoms_from; simpl; reflexivity.
  - unfold subst_atoms_from; simpl; reflexivity.
  - unfold subst_atoms_from; simpl; reflexivity.
  - rewrite IHp1, IHp2; reflexivity.
  - rewrite IHp1, IHp2; reflexivity.
  - rewrite IHp; reflexivity.
Qed.

Lemma subst_atoms_from_agree_closed : forall atoms x v,
  atoms_agree_closed atoms ->
  atoms_agree_closed (subst_atoms_from atoms x v).
Proof.
  intros atoms x v Hagree p Hp. rewrite interpret_qualifier_subst_atoms_from.
  rewrite qualifier_subst_fresh.
  - apply Hagree; exact Hp.
  - rewrite (predicate_closed_qualifier_fv_nil p Hp). simpl. tauto.
Qed.

Lemma rcontext_satisfies_subst_fresh : forall RGamma atoms x v,
  rcontext_satisfies RGamma atoms ->
  (forall y T p, lookup_rcontext y RGamma = Some (R_Refine T p) ->
    ~ In x (qualifier_fv (open_qualifier_tm p (tm_fvar y)))) ->
  rcontext_satisfies RGamma (subst_atoms_from atoms x v).
Proof.
  intros RGamma atoms x v Hctx Hfresh y T p Hlookup.
  specialize (Hctx y T p Hlookup).
  rewrite interpret_qualifier_subst_atoms_from.
  rewrite qualifier_subst_fresh.
  - exact Hctx.
  - eapply Hfresh; eassumption.
Qed.

Inductive logical_value (atoms : atom_interpretation) : rty -> tm -> Prop :=
| LV_Refine : forall T p v,
    value v ->
    shape_value (shape_ty T) v ->
    interpret_qualifier atoms (open_qualifier_tm p v) ->
    logical_value atoms (R_Refine T p) v
| LV_Func : forall R S v,
    value v -> shape_value (shape_rty (R_Func R S)) v ->
    logical_value atoms (R_Func R S) v
| LV_Exists : forall R S v w,
    value v -> value w -> shape_value (shape_rty (open_rty_tm S w)) v ->
    logical_value atoms R w ->
    logical_value atoms (open_rty_tm S w) v ->
    logical_value atoms (R_Exists R S) v
| LV_Poly : forall R v,
    value v -> shape_value (shape_rty (R_Poly R)) v ->
    logical_value atoms (R_Poly R) v.

Inductive logical_value_support (atoms : atom_interpretation) : rty -> tm -> list atom -> Prop :=
| LVS_Refine : forall T p v,
    value v -> shape_value (shape_ty T) v ->
    interpret_qualifier atoms (open_qualifier_tm p v) ->
    logical_value_support atoms (R_Refine T p) v (fv_tm v)
| LVS_Func : forall R S v,
    value v -> shape_value (shape_rty (R_Func R S)) v ->
    logical_value_support atoms (R_Func R S) v (fv_tm v)
| LVS_Exists : forall R S v w L1 L2,
    value v -> value w -> shape_value (shape_rty (open_rty_tm S w)) v ->
    logical_value_support atoms R w L1 ->
    logical_value_support atoms (open_rty_tm S w) v L2 ->
    logical_value_support atoms (R_Exists R S) v (fv_tm v ++ fv_tm w ++ L1 ++ L2)
| LVS_Poly : forall R v,
    value v -> shape_value (shape_rty (R_Poly R)) v ->
    logical_value_support atoms (R_Poly R) v (fv_tm v).

Lemma logical_value_has_support : forall atoms R v (H : logical_value atoms R v),
  exists L, logical_value_support atoms R v L.
Proof.
  intros atoms R v H. induction H.
  - exists (fv_tm v). econstructor; eassumption.
  - exists (fv_tm v). econstructor; eassumption.
  - destruct IHlogical_value1 as [L1 HS1].
    destruct IHlogical_value2 as [L2 HS2].
    exists (fv_tm v ++ fv_tm w ++ L1 ++ L2). econstructor; eassumption.
  - exists (fv_tm v). econstructor; eassumption.
Qed.

Lemma logical_value_subst : forall atoms R v x s,
  locally_closed_tm s ->
  logical_value (subst_atoms_from atoms x s) R v ->
  logical_value atoms (rty_subst x s R) (tm_subst x s v).
Proof.
  intros atoms R v x s Hs Hrel. induction Hrel; simpl.
  - apply LV_Refine.
    + eapply value_tm_subst; eassumption.
    + eapply shape_value_tm_subst; eassumption.
    + rewrite interpret_qualifier_subst_atoms_from in H1.
      unfold open_qualifier_tm in H1.
      rewrite qualifier_subst_open_rec_comm_lc in H1 by exact Hs.
      exact H1.
  - apply LV_Func.
    + eapply value_tm_subst; eassumption.
    + change (shape_value (Sh_Arrow (shape_rty (rty_subst x s R))
        (shape_rty (rty_subst x s S))) (tm_subst x s v)).
      rewrite (shape_rty_subst_tm R x s), (shape_rty_subst_tm S x s).
      eapply shape_value_tm_subst; eassumption.
  - pose proof IHHrel1 as Hleft.
    pose proof IHHrel2 as Hright.
    unfold open_rty_tm in Hright.
    rewrite rty_subst_open_rty_tm_rec_comm_lc in Hright by exact Hs.
    eapply LV_Exists with (w := tm_subst x s w).
    + eapply value_tm_subst; eassumption.
    + eapply value_tm_subst; eassumption.
    + unfold open_rty_tm. rewrite shape_open_rty_tm_rec, shape_rty_subst_tm.
      eapply shape_value_tm_subst.
      * unfold open_rty_tm in H1. rewrite shape_open_rty_tm_rec in H1. exact H1.
      * exact Hs.
    + exact Hleft.
    + exact Hright.
  - apply LV_Poly.
    + eapply value_tm_subst; eassumption.
    + change (shape_value (Sh_All (shape_rty (rty_subst x s R))) (tm_subst x s v)).
      rewrite shape_rty_subst_tm. eapply shape_value_tm_subst; eassumption.
Qed.

Lemma logical_value_open_subst_fresh : forall atoms R v x s,
  locally_closed_tm s ->
  ~ In x (rty_qualifier_fv R) -> ~ In x (fv_tm v) ->
  logical_value (subst_atoms_from atoms x s)
    (open_rty_tm R (tm_fvar x)) v ->
  logical_value atoms (open_rty_tm R s) v.
Proof.
  intros atoms R v x s Hs HR Hv Hrel.
  pose proof (logical_value_subst atoms (open_rty_tm R (tm_fvar x)) v x s Hs Hrel) as Hnew.
  unfold open_rty_tm in *.
  rewrite rty_subst_open_rty_tm_rec_fresh in Hnew by exact HR.
  rewrite tm_subst_fresh in Hnew by exact Hv.
  exact Hnew.
Qed.

Lemma logical_value_support_contains_value_fv : forall atoms R v L,
  logical_value_support atoms R v L ->
  forall x, In x (fv_tm v) -> In x L.
Proof.
  intros atoms R v L Hsupport. induction Hsupport; intros x Hin; simpl in *.
  - exact Hin.
  - exact Hin.
  - apply in_or_app. left. exact Hin.
  - exact Hin.
Qed.

Lemma logical_value_shape : forall atoms R v,
  logical_value atoms R v -> shape_value (shape_rty R) v.
Proof.
  intros atoms R v H. inversion H; subst; simpl.
  - assumption.
  - change (shape_value (shape_rty (R_Func R0 S)) v). exact H1.
  - unfold open_rty_tm in H2. rewrite shape_open_rty_tm_rec in H2. exact H2.
  - assumption.
Qed.

Lemma rcontext_satisfies_extend_logical : forall RGamma atoms x R v,
  rcontext_satisfies RGamma atoms ->
  (forall y T p, lookup_rcontext y RGamma = Some (R_Refine T p) ->
    ~ In x (qualifier_fv (open_qualifier_tm p (tm_fvar y)))) ->
  ~ In x (rty_qualifier_fv R) ->
  logical_value atoms R v ->
  rcontext_satisfies (update_rcontext RGamma x R)
    (subst_atoms_from atoms x v).
Proof.
  intros RGamma atoms x R v Hctx Hfresh HxR Hrel.
  assert (Hctx' : rcontext_satisfies RGamma (subst_atoms_from atoms x v)).
  { eapply rcontext_satisfies_subst_fresh; eauto. }
  eapply rcontext_satisfies_extend; [exact Hctx'|].
  intros T p Heq. subst R.
  inversion Hrel; subst.
  rewrite interpret_qualifier_subst_atoms_from.
  rewrite qualifier_subst_open_fresh.
  - assumption.
  - exact HxR.
Qed.

Lemma operational_atoms_agree_closed : atoms_agree_closed operational_atoms.
Proof. intros p Hp; split; intro H; exact H. Qed.

Lemma logical_value_refine_from_closed : forall atoms T p v,
  atoms_agree_closed atoms ->
  predicate_closed (open_qualifier_tm p v) ->
  shape_value (shape_ty T) v ->
  value v -> qualifier_holds (open_qualifier_tm p v) ->
  logical_value atoms (R_Refine T p) v.
Proof.
  intros atoms T p v Hagree Hclosed Hshape Hv Hholds. constructor; [exact Hv|exact Hshape|].
  apply (proj2 (Hagree _ Hclosed)). exact Hholds.
Qed.

Lemma logical_value_int_literal : forall n : Z,
  logical_value operational_atoms
    (R_Refine Ty_Int (Pred_Eq (tm_bvar 0) (tm_int n))) (tm_int n).
Proof.
  intros n. apply LV_Refine; [constructor|constructor|].
  unfold interpret_qualifier, operational_atoms; simpl.
  exists (tm_int n). repeat split; constructor.
Qed.

Lemma logical_value_true : logical_value operational_atoms
  (R_Refine Ty_Bool Pred_True) tm_true.
Proof. apply LV_Refine; [constructor|constructor|exact I]. Qed.

Lemma logical_value_false : logical_value operational_atoms
  (R_Refine Ty_Bool Pred_True) tm_false.
Proof. apply LV_Refine; [constructor|constructor|exact I]. Qed.

Lemma logical_value_nonzero_int : forall v,
  logical_value operational_atoms
    (R_Refine Ty_Int (Pred_Ne (tm_bvar 0) (tm_int 0%Z))) v ->
  exists n, v = tm_int n /\ n <> 0%Z.
Proof.
  intros v Hrel. inversion Hrel; subst.
  inversion H2; subst. exists n. split; [reflexivity|].
  eapply nonzero_refinement_int. exact H4.
Qed.





Lemma subtype_refine_semantic_at_fresh : forall L Delta RGamma atoms T p q v x,
  rcontext_satisfies RGamma atoms ->
  ~ In x L -> ~ In x (qualifier_fv p) -> ~ In x (qualifier_fv q) ->
  (forall y U s, lookup_rcontext y RGamma = Some (R_Refine U s) ->
    ~ In x (qualifier_fv (open_qualifier_tm s (tm_fvar y)))) ->
  (forall z, ~ In z L ->
    entails Delta (update_rcontext RGamma z (R_Refine T Pred_True))
      (open_qualifier_tm p (tm_fvar z))
      (open_qualifier_tm q (tm_fvar z))) ->
  logical_value atoms (R_Refine T p) v ->
  logical_value atoms (R_Refine T q) v.
Proof.
  intros L Delta RGamma atoms T p q v x Hctx HxL Hxp Hxq Hctxfresh Hsub Hrel.
  inversion Hrel; subst.
  assert (Hctx' : rcontext_satisfies RGamma (subst_atoms_from atoms x v)).
  { eapply rcontext_satisfies_subst_fresh; eauto. }
  assert (Hctx'' : rcontext_satisfies
      (update_rcontext RGamma x (R_Refine T Pred_True))
      (subst_atoms_from atoms x v)).
  { eapply rcontext_satisfies_extend; [exact Hctx'|].
    intros U s Heq. inversion Heq; subst. simpl. exact I. }
  pose proof (entails_sound Delta _ _ _ (subst_atoms_from atoms x v) Hctx''
    (Hsub x HxL)) as Hsound.
  rewrite !interpret_qualifier_subst_atoms_from in Hsound.
  rewrite !qualifier_subst_open_fresh in Hsound by assumption.
  apply LV_Refine; [assumption|assumption|].
  apply Hsound. assumption.
Qed.

Lemma subtype_refine_semantic : forall L Delta RGamma atoms T p q v,
  rcontext_satisfies RGamma atoms ->
  (forall x, ~ In x L ->
    entails Delta (update_rcontext RGamma x (R_Refine T Pred_True))
      (open_qualifier_tm p (tm_fvar x))
      (open_qualifier_tm q (tm_fvar x))) ->
  logical_value atoms (R_Refine T p) v ->
  logical_value atoms (R_Refine T q) v.
Proof.
  intros L Delta RGamma atoms T p q v Hctx Hsub Hrel.
  set (x := fresh (L ++ qualifier_fv p ++ qualifier_fv q ++ rcontext_support RGamma)).
  assert (Hx : ~ In x (L ++ qualifier_fv p ++ qualifier_fv q ++ rcontext_support RGamma)).
  { unfold x. apply fresh_not_in. }
  assert (HxL : ~ In x L).
  { intro H. apply Hx. repeat rewrite in_app_iff. tauto. }
  assert (Hxp : ~ In x (qualifier_fv p)).
  { intro H. apply Hx. repeat rewrite in_app_iff. tauto. }
  assert (Hxq : ~ In x (qualifier_fv q)).
  { intro H. apply Hx. repeat rewrite in_app_iff. tauto. }
  assert (Hxc : forall y U s,
      lookup_rcontext y RGamma = Some (R_Refine U s) ->
      ~ In x (qualifier_fv (open_qualifier_tm s (tm_fvar y)))).
  { intros y U s Hlookup Hbad. apply Hx.
    apply in_or_app. right. apply in_or_app. right. apply in_or_app. right.
    eapply lookup_rcontext_support; eauto. }
  exact (subtype_refine_semantic_at_fresh L Delta RGamma atoms T p q v x
    Hctx HxL Hxp Hxq Hxc Hsub Hrel).
Qed.

Lemma interpret_qualifier_subst_atoms : forall p x v,
  interpret_qualifier (subst_atoms x v) p =
  interpret_qualifier operational_atoms (qualifier_subst x v p).
Proof.
  induction p; intros; simpl.
  - reflexivity.
  - reflexivity.
  - unfold subst_atoms; simpl; reflexivity.
  - unfold subst_atoms; simpl; reflexivity.
  - unfold subst_atoms; simpl; reflexivity.
  - rewrite IHp1, IHp2; reflexivity.
  - rewrite IHp1, IHp2; reflexivity.
  - rewrite IHp; reflexivity.
Qed.

Lemma true_extend_satisfies_subst_atoms : forall x v T,
  rcontext_satisfies (update_rcontext empty_rcontext x (R_Refine T Pred_True))
    (subst_atoms x v).
Proof.
  intros x v T y U p Hlookup. unfold update_rcontext, empty_rcontext in Hlookup.
  simpl in Hlookup. destruct (Nat.eqb y x) eqn:E; try discriminate.
  inversion Hlookup; subst. simpl. exact I.
Qed.

Lemma entails_sound_true_extend_subst : forall Delta x T p q v,
  entails Delta (update_rcontext empty_rcontext x (R_Refine T Pred_True))
    (open_qualifier_tm p (tm_fvar x)) (open_qualifier_tm q (tm_fvar x)) ->
  (interpret_qualifier operational_atoms
     (qualifier_subst x v (open_qualifier_tm p (tm_fvar x))) ->
   interpret_qualifier operational_atoms
     (qualifier_subst x v (open_qualifier_tm q (tm_fvar x)))).
Proof.
  intros Delta x T p q v Hent.
  pose proof (entails_sound Delta _ _ _ (subst_atoms x v)
    (true_extend_satisfies_subst_atoms x v T) Hent) as Hsound.
  rewrite !interpret_qualifier_subst_atoms in Hsound. exact Hsound.
Qed.

Lemma entails_refinement_value : forall Delta x T p q v,
  ~ In x (qualifier_fv p) -> ~ In x (qualifier_fv q) ->
  entails Delta (update_rcontext empty_rcontext x (R_Refine T Pred_True))
    (open_qualifier_tm p (tm_fvar x)) (open_qualifier_tm q (tm_fvar x)) ->
  qualifier_holds (open_qualifier_tm p v) ->
  qualifier_holds (open_qualifier_tm q v).
Proof.
  intros Delta x T p q v HpFresh HqFresh Hent Hp.
  pose proof (entails_sound_true_extend_subst Delta x T p q v Hent) as Hsound.
  rewrite !qualifier_subst_open_fresh in Hsound by assumption.
  unfold qualifier_holds, predicate_holds in *. apply Hsound. exact Hp.
Qed.

Lemma rtype_progress_with_nonzero :
  (forall v, has_rtype [] empty_rcontext v
      (R_Refine Ty_Int (Pred_Ne (tm_bvar 0) (tm_int 0%Z))) ->
      value v ->
      qualifier_holds
        (open_qualifier_tm (Pred_Ne (tm_bvar 0) (tm_int 0%Z)) v)) ->
  forall t R, has_rtype [] empty_rcontext t R ->
  value t \/ exists t', t --> t'.
Proof.
  intros Hnz t R HR.
  assert (P : forall Delta RGamma t R,
      has_rtype Delta RGamma t R -> Delta = [] -> RGamma = empty_rcontext ->
      value t \/ exists t', t --> t').
  {
    intros Delta RGamma t0 R0 Htyping.
    induction Htyping using rtype_subtype_ind
      with (P := fun Delta RGamma t R _ =>
        Delta = [] -> RGamma = empty_rcontext -> value t \/ exists t', t --> t')
           (P0 := fun _ _ _ _ _ => True).
    - intros HD HG. subst Delta RGamma. simpl in e. discriminate.
    - intros HD HG. left. apply v_abs.
      pose proof (rtype_core_typing _ _ _ _ (RT_Abs L Delta RGamma R1 body R2 w h)) as HTcore.
      exact (has_type_locally_closed _ _ _ _ HTcore).
    - intros HD HG. subst Delta RGamma.
      destruct (IHHtyping1 eq_refl eq_refl) as [Hv1|[t1' Hs1]].
      + destruct (IHHtyping2 eq_refl eq_refl) as [Hv2|[t2' Hs2]].
        * right. destruct (rtype_canonical_fun _ _ _ _ Htyping1 Hv1 eq_refl) as [T [body ->]].
          eexists. eapply ST_AppAbs.
          -- exact (has_type_locally_closed _ _ _ _ (rtype_core_typing _ _ _ _ Htyping1)).
          -- exact Hv2.
        * right. eexists. eapply ST_App2; eassumption.
      + right. eexists. eapply ST_App1.
        * exact Hs1.
        * exact (has_type_locally_closed _ _ _ _ (rtype_core_typing _ _ _ _ Htyping2)).
    - intros HD HG. left. constructor.
      exact (has_type_locally_closed _ _ _ _
        (rtype_core_typing _ _ _ _ (RT_TAbs L Delta RGamma body R0 h))).
    - intros HD HG. subst Delta RGamma.
      destruct (IHHtyping eq_refl eq_refl) as [Hv|[t' Hs]].
      + right. destruct (rtype_canonical_tabs _ _ _ Htyping Hv eq_refl) as [body ->].
        eexists. eapply ST_TAppTabs.
        * exact (has_type_locally_closed _ _ _ _ (rtype_core_typing _ _ _ _ Htyping)).
        * exact (wf_ty_locally_closed _ _ w).
      + right. eexists. eapply ST_TApp.
        * exact Hs.
        * exact (wf_ty_locally_closed _ _ w).
    - intros HD HG. left. constructor.
    - intros HD HG. subst Delta RGamma.
      destruct (IHHtyping1 eq_refl eq_refl) as [Hv1|[t1' Hs1]].
      + destruct (IHHtyping2 eq_refl eq_refl) as [Hv2|[t2' Hs2]].
        * destruct (rtype_canonical_int _ _ Htyping1 Hv1 eq_refl) as [n ->].
          destruct (rtype_canonical_int _ _ Htyping2 Hv2 eq_refl) as [m ->].
          pose proof (nonzero_refinement_int m (Hnz _ Htyping2 Hv2)) as Hm.
          right. eexists. eapply ST_DivInt; exact Hm.
        * right. eexists. eapply ST_Div2; [exact Hv1|exact Hs2].
      + right. eexists. eapply ST_Div1.
        * exact Hs1.
        * exact (has_type_locally_closed _ _ _ _ (rtype_core_typing _ _ _ _ Htyping2)).
    - intros HD HG. subst Delta RGamma.
      destruct (IHHtyping1 eq_refl eq_refl) as [Hv1|[t1' Hs1]].
      + destruct (IHHtyping2 eq_refl eq_refl) as [Hv2|[t2' Hs2]].
        * destruct (rtype_canonical_int _ _ Htyping1 Hv1 eq_refl) as [n ->].
          destruct (rtype_canonical_int _ _ Htyping2 Hv2 eq_refl) as [m ->].
          right. eexists. apply ST_ArithInt.
        * right. eexists. eapply ST_Arith2; [exact Hv1|exact Hs2].
      + right. eexists. eapply ST_Arith1.
        * exact Hs1.
        * exact (has_type_locally_closed _ _ _ _ (rtype_core_typing _ _ _ _ Htyping2)).
    - intros HD HG. left. constructor.
    - intros HD HG. left. constructor.
    - intros HD HG. subst Delta RGamma.
      destruct (IHHtyping1 eq_refl eq_refl) as [Hv|[t1' Hs]].
      + destruct (rtype_canonical_bool _ _ Htyping1 Hv eq_refl) as [Heq|Heq]; subst t1.
        * right. eexists. eapply ST_IfTrue;
            [exact (has_type_locally_closed _ _ _ _ (rtype_core_typing _ _ _ _ Htyping2))|exact (has_type_locally_closed _ _ _ _ (rtype_core_typing _ _ _ _ Htyping3))].
        * right. eexists. eapply ST_IfFalse;
            [exact (has_type_locally_closed _ _ _ _ (rtype_core_typing _ _ _ _ Htyping2))|exact (has_type_locally_closed _ _ _ _ (rtype_core_typing _ _ _ _ Htyping3))].
      + right. eexists. eapply ST_If.
        * exact Hs.
        * exact (has_type_locally_closed _ _ _ _ (rtype_core_typing _ _ _ _ Htyping2)).
        * exact (has_type_locally_closed _ _ _ _ (rtype_core_typing _ _ _ _ Htyping3)).
    - intros HD HG. left. exact v0.
    - intros HD HG. exact (IHHtyping HD HG).
    - exact I.
    - exact I.
    - exact I.
    - exact I.
    - exact I.
    - exact I.
    - exact I.
  }
  eapply P; eauto.
Qed.

Lemma subtype_refine_value_direct : forall L T p q v,
  (forall x, ~ In x L ->
    entails [] (update_rcontext empty_rcontext x (R_Refine T Pred_True))
      (open_qualifier_tm p (tm_fvar x))
      (open_qualifier_tm q (tm_fvar x))) ->
  value v -> qualifier_holds (open_qualifier_tm p v) ->
  exists x, ~ In x L /\
    qualifier_holds (open_qualifier_tm q v).
Proof.
  intros L T p q v Hsub Hv Hp.
  set (x := fresh (L ++ qualifier_fv p ++ qualifier_fv q)).
  assert (Hx : ~ In x (L ++ qualifier_fv p ++ qualifier_fv q)).
  { unfold x. apply fresh_not_in. }
  assert (HxL : ~ In x L).
  { intro Hin. apply Hx. repeat rewrite in_app_iff. tauto. }
  assert (Hxp : ~ In x (qualifier_fv p)).
  { intro Hin. apply Hx. repeat rewrite in_app_iff. tauto. }
  assert (Hxq : ~ In x (qualifier_fv q)).
  { intro Hin. apply Hx. repeat rewrite in_app_iff. tauto. }
  exists x. split; [exact HxL|].
  exact (entails_refinement_value [] x T p q v Hxp Hxq
    (Hsub x HxL) Hp).
Qed.

Lemma subtype_refine_operational_value : forall L T p q v,
  (forall x, ~ In x L ->
    entails [] (update_rcontext empty_rcontext x (R_Refine T Pred_True))
      (open_qualifier_tm p (tm_fvar x)) (open_qualifier_tm q (tm_fvar x))) ->
  value v -> shape_value (shape_ty T) v ->
  qualifier_holds (open_qualifier_tm p v) ->
  qualifier_holds (open_qualifier_tm q v).
Proof.
  intros L T p q v Hsub Hv Hshape Hp.
  assert (Hrel : logical_value operational_atoms (R_Refine T p) v)
    by (apply LV_Refine; assumption).
  pose proof (subtype_refine_semantic L [] empty_rcontext operational_atoms
    T p q v (empty_rcontext_satisfies operational_atoms) Hsub Hrel) as Hres.
  inversion Hres; assumption.
Qed.

Lemma never_stuck_from_preservation :
  (forall t t' R, has_rtype [] empty_rcontext t R -> t --> t' ->
    has_rtype [] empty_rcontext t' R) ->
  (forall v, has_rtype [] empty_rcontext v
      (R_Refine Ty_Int (Pred_Ne (tm_bvar 0) (tm_int 0%Z))) ->
      value v ->
      qualifier_holds
        (open_qualifier_tm (Pred_Ne (tm_bvar 0) (tm_int 0%Z)) v)) ->
  forall t t' R, has_rtype [] empty_rcontext t R -> multi t t' ->
  value t' \/ exists t'', t' --> t''.
Proof.
  intros Hpres Hnz t t' R Htyping Hmulti.
  induction Hmulti.
  - eapply rtype_progress_with_nonzero; eauto.
  - apply IHHmulti. eapply Hpres; eassumption.
Qed.

Theorem never_stuck : forall (t t' : tm) (R : rty),
  has_rtype [] empty_rcontext t R ->
  multi t t' ->
  value t' \/ exists t'' : tm, t' --> t''.
Proof.
  intros t t' R Htyping Hmulti.
  eapply never_stuck_from_preservation; eauto.
Qed.

End SystemFRefinementIfTask.
