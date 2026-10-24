(** System F CBV strong-normalization benchmark, Hard variant.
    Features: recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFNormalizationRecursionHardTask.

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
  | Ty_Nat : ty.

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

Inductive tm : Type :=
  | tm_bvar : nat -> tm
  | tm_fvar : atom -> tm
  | tm_abs : ty -> tm -> tm
  | tm_app : tm -> tm -> tm

  | tm_tabs : tm -> tm

  | tm_tapp : tm -> ty -> tm
  | tm_zero : tm
  | tm_succ : tm -> tm
  | tm_natrec : tm -> tm -> tm -> tm.

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

Notation "'Nat'" := Ty_Nat (in custom systemf_ty at level 0) : systemf_scope.
Notation "'zero'" := tm_zero (in custom systemf_tm at level 0) : systemf_scope.
Notation "'succ' t" := (tm_succ t) (in custom systemf_tm at level 9, t custom systemf_tm at level 0) : systemf_scope.
Notation "'rec' n b s" := (tm_natrec n b s)
  (in custom systemf_tm at level 9, n custom systemf_tm at level 0, b custom systemf_tm at level 0, s custom systemf_tm at level 0) : systemf_scope.

Fixpoint open_ty_rec (k : nat) (U T : ty) : ty :=
  match T with
  | Ty_BVar i => if Nat.eqb k i then U else Ty_BVar i
  | Ty_FVar X => Ty_FVar X
  | Ty_Arrow T1 T2 =>
      Ty_Arrow (open_ty_rec k U T1) (open_ty_rec k U T2)
  | Ty_All T1 => Ty_All (open_ty_rec (S k) U T1)
  | Ty_Nat => Ty_Nat
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
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (open_tm_rec k u t1)
  | tm_natrec n b f => tm_natrec (open_tm_rec k u n) (open_tm_rec k u b) (open_tm_rec k u f)
  end.

Definition open_tm (t u : tm) : tm := open_tm_rec 0 u t.

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
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (open_tm_ty_rec k U t1)
  | tm_natrec n b f => tm_natrec (open_tm_ty_rec k U n) (open_tm_ty_rec k U b) (open_tm_ty_rec k U f)
  end.

Definition open_tm_ty (t : tm) (U : ty) : tm :=
  open_tm_ty_rec 0 U t.

Fixpoint ty_subst (X : atom) (U T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar Y => if Nat.eqb X Y then U else Ty_FVar Y
  | Ty_Arrow T1 T2 => Ty_Arrow (ty_subst X U T1) (ty_subst X U T2)
  | Ty_All T1 => Ty_All (ty_subst X U T1)
  | Ty_Nat => Ty_Nat
  end.

Fixpoint tm_ty_subst (X : atom) (U : ty) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T t1 => tm_abs (ty_subst X U T) (tm_ty_subst X U t1)
  | tm_app t1 t2 => tm_app (tm_ty_subst X U t1) (tm_ty_subst X U t2)
  | tm_tabs t1 => tm_tabs (tm_ty_subst X U t1)
  | tm_tapp t1 T => tm_tapp (tm_ty_subst X U t1) (ty_subst X U T)
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (tm_ty_subst X U t1)
  | tm_natrec n b f => tm_natrec (tm_ty_subst X U n) (tm_ty_subst X U b) (tm_ty_subst X U f)
  end.

Fixpoint tm_subst (x : atom) (s t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar y => if Nat.eqb x y then s else tm_fvar y
  | tm_abs T t1 => tm_abs T (tm_subst x s t1)
  | tm_app t1 t2 => tm_app (tm_subst x s t1) (tm_subst x s t2)
  | tm_tabs t1 => tm_tabs (tm_subst x s t1)
  | tm_tapp t1 T => tm_tapp (tm_subst x s t1) T
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (tm_subst x s t1)
  | tm_natrec n b f => tm_natrec (tm_subst x s n) (tm_subst x s b) (tm_subst x s f)
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
  | lc_ty_nat : forall k, lc_ty_at k Ty_Nat.

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
  | lc_tm_zero : forall K k, lc_tm_at K k tm_zero
  | lc_tm_succ : forall K k t, lc_tm_at K k t -> lc_tm_at K k (tm_succ t)
  | lc_tm_rec : forall K k n b s,
      lc_tm_at K k n -> lc_tm_at K k b -> lc_tm_at K k s -> lc_tm_at K k (tm_natrec n b s).

Definition locally_closed_tm (t : tm) : Prop := lc_tm_at 0 0 t.

Inductive numeric_value : tm -> Prop :=
  | nv_zero : numeric_value tm_zero
  | nv_succ : forall (n : tm), numeric_value n -> numeric_value (tm_succ n).

Fixpoint numeral (n : nat) : tm :=
  match n with O => tm_zero | S m => tm_succ (numeral m) end.

Inductive value : tm -> Prop :=
  | v_abs : forall T t,
      locally_closed_tm (tm_abs T t) ->
      value (tm_abs T t)
  | v_tabs : forall t,
      locally_closed_tm (tm_tabs t) ->
      value (tm_tabs t)
  | v_nat : forall n, numeric_value n -> value n.

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
  | ST_Succ : forall t t',
      t --> t' -> tm_succ t --> tm_succ t'
  | ST_RecArg : forall n n' b s,

      n --> n' -> locally_closed_tm b -> locally_closed_tm s ->
      tm_natrec n b s --> tm_natrec n' b s
  | ST_RecBase : forall n b b' s,

      numeric_value n -> b --> b' -> locally_closed_tm s ->
      tm_natrec n b s --> tm_natrec n b' s
  | ST_RecStep : forall n b s s',

      numeric_value n -> value b -> s --> s' ->
      tm_natrec n b s --> tm_natrec n b s'
  | ST_RecZero : forall b s,

      value b -> value s -> tm_natrec tm_zero b s --> b
  | ST_RecSucc : forall n b s,

      numeric_value n -> value b -> value s ->
      tm_natrec (tm_succ n) b s -->
        tm_app (tm_app s n) (tm_natrec n b s)
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
  | WF_Nat : forall Delta, wf_ty Delta Ty_Nat.

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
  | T_Zero : forall Delta Gamma, has_type Delta Gamma tm_zero Ty_Nat
  | T_Succ : forall Delta Gamma n,
      has_type Delta Gamma n Ty_Nat -> has_type Delta Gamma (tm_succ n) Ty_Nat
  | T_Rec : forall Delta Gamma n b s T,
      has_type Delta Gamma n Ty_Nat -> has_type Delta Gamma b T ->
      has_type Delta Gamma s (Ty_Arrow Ty_Nat (Ty_Arrow T T)) ->
      has_type Delta Gamma (tm_natrec n b s) T.

Inductive multi : tm -> tm -> Prop :=
  | multi_refl : forall x, multi x x
  | multi_step : forall x y z, x --> y -> multi y z -> multi x z.
Notation "t '-->*' u" := (multi t u) (at level 40).

Inductive strongly_normalizing : tm -> Prop :=
  | SN_intro : forall t,
      (forall u, t --> u -> strongly_normalizing u) -> strongly_normalizing t.

Hint Constructors lc_ty_at lc_tm_at value : core.

(* ============================================================ *)
(* Skeleton calculus: erase all type annotations.  Type         *)
(* annotations are computationally irrelevant for the shape of  *)
(* the reduction relation, and erasing them makes the universal *)
(* type's semantic clause structurally recursive.               *)
(* ============================================================ *)

Inductive sktm : Type :=
| sk_bvar : nat -> sktm
| sk_fvar : atom -> sktm
| sk_abs : sktm -> sktm
| sk_app : sktm -> sktm -> sktm
| sk_tabs : sktm -> sktm
| sk_tapp : sktm -> sktm
| sk_zero : sktm
| sk_succ : sktm -> sktm
| sk_natrec : sktm -> sktm -> sktm -> sktm.

Fixpoint sk (t : tm) : sktm :=
  match t with
  | tm_bvar i => sk_bvar i
  | tm_fvar x => sk_fvar x
  | tm_abs _ t1 => sk_abs (sk t1)
  | tm_app t1 t2 => sk_app (sk t1) (sk t2)
  | tm_tabs t1 => sk_tabs (sk t1)
  | tm_tapp t1 _ => sk_tapp (sk t1)
  | tm_zero => sk_zero
  | tm_succ t1 => sk_succ (sk t1)
  | tm_natrec n b s => sk_natrec (sk n) (sk b) (sk s)
  end.

Fixpoint open_sk_rec (k : nat) (u t : sktm) : sktm :=
  match t with
  | sk_bvar i => if Nat.eqb k i then u else sk_bvar i
  | sk_fvar x => sk_fvar x
  | sk_abs t1 => sk_abs (open_sk_rec (S k) u t1)
  | sk_app t1 t2 => sk_app (open_sk_rec k u t1) (open_sk_rec k u t2)
  | sk_tabs t1 => sk_tabs (open_sk_rec k u t1)
  | sk_tapp t1 => sk_tapp (open_sk_rec k u t1)
  | sk_zero => sk_zero
  | sk_succ t1 => sk_succ (open_sk_rec k u t1)
  | sk_natrec n b s =>
      sk_natrec (open_sk_rec k u n) (open_sk_rec k u b) (open_sk_rec k u s)
  end.

Definition open_sk (t u : sktm) : sktm := open_sk_rec 0 u t.

Fixpoint sksubst (sigma : atom -> sktm) (t : sktm) : sktm :=
  match t with
  | sk_bvar i => sk_bvar i
  | sk_fvar x => sigma x
  | sk_abs t1 => sk_abs (sksubst sigma t1)
  | sk_app t1 t2 => sk_app (sksubst sigma t1) (sksubst sigma t2)
  | sk_tabs t1 => sk_tabs (sksubst sigma t1)
  | sk_tapp t1 => sk_tapp (sksubst sigma t1)
  | sk_zero => sk_zero
  | sk_succ t1 => sk_succ (sksubst sigma t1)
  | sk_natrec n b s =>
      sk_natrec (sksubst sigma n) (sksubst sigma b) (sksubst sigma s)
  end.

(* Erasure commutes with term opening and type opening *)

Lemma sk_open_tm : forall t k u,
  sk (open_tm_rec k u t) = open_sk_rec k (sk u) (sk t).
Proof.
  induction t; intros k u; simpl; auto.
  - destruct (Nat.eqb k n); reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2, IHt3. reflexivity.
Qed.

Lemma sk_open_tm_ty : forall t k U,
  sk (open_tm_ty_rec k U t) = sk t.
Proof.
  induction t; intros k U; simpl; auto;
    try (rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3; reflexivity).
Qed.

(* Locally closed skeletons *)

Inductive lc_sk_at : nat -> sktm -> Prop :=
  | lc_sk_bvar : forall k i, i < k -> lc_sk_at k (sk_bvar i)
  | lc_sk_fvar : forall k x, lc_sk_at k (sk_fvar x)
  | lc_sk_abs : forall k t,
      lc_sk_at (S k) t -> lc_sk_at k (sk_abs t)
  | lc_sk_app : forall k t1 t2,
      lc_sk_at k t1 -> lc_sk_at k t2 -> lc_sk_at k (sk_app t1 t2)
  | lc_sk_tabs : forall k t,
      lc_sk_at k t -> lc_sk_at k (sk_tabs t)
  | lc_sk_tapp : forall k t,
      lc_sk_at k t -> lc_sk_at k (sk_tapp t)
  | lc_sk_zero : forall k, lc_sk_at k sk_zero
  | lc_sk_succ : forall k t,
      lc_sk_at k t -> lc_sk_at k (sk_succ t)
  | lc_sk_natrec : forall k n b s,
      lc_sk_at k n -> lc_sk_at k b -> lc_sk_at k s ->
      lc_sk_at k (sk_natrec n b s).

Definition lc_sk (t : sktm) : Prop := lc_sk_at 0 t.

Hint Constructors lc_sk_at : core.

Lemma sk_lc_tm : forall K k t, lc_tm_at K k t -> lc_sk_at k (sk t).
Proof.
  intros K k t H. induction H; simpl; eauto.
Qed.

(* Skeleton values and numerals *)

Inductive numeric_sk : sktm -> Prop :=
  | nv_sk_zero : numeric_sk sk_zero
  | nv_sk_succ : forall n, numeric_sk n -> numeric_sk (sk_succ n).

Inductive value_sk : sktm -> Prop :=
  | v_sk_abs : forall t, lc_sk (sk_abs t) -> value_sk (sk_abs t)
  | v_sk_tabs : forall t, lc_sk (sk_tabs t) -> value_sk (sk_tabs t)
  | v_sk_nat : forall n, numeric_sk n -> value_sk n.

Hint Constructors numeric_sk value_sk : core.

Lemma sk_numeric : forall t, numeric_value t -> numeric_sk (sk t).
Proof.
  intros t H. induction H; simpl; eauto.
Qed.

Lemma sk_value : forall t, value t -> value_sk (sk t).
Proof.
  intros t H. induction H; simpl.
  - apply v_sk_abs. apply sk_lc_tm in H. simpl in H. exact H.
  - apply v_sk_tabs. apply sk_lc_tm in H. simpl in H. exact H.
  - apply v_sk_nat. apply sk_numeric. exact H.
Qed.

(* Skeleton small-step semantics *)

Reserved Notation "t1 '-->s' t2" (at level 40).

Inductive sstep : sktm -> sktm -> Prop :=
  | s_AppAbs : forall t v,
      lc_sk (sk_abs t) ->
      value_sk v ->
      sk_app (sk_abs t) v -->s open_sk t v
  | s_App1 : forall t1 t1' t2,
      t1 -->s t1' ->
      lc_sk t2 ->
      sk_app t1 t2 -->s sk_app t1' t2
  | s_App2 : forall v1 t2 t2',
      value_sk v1 ->
      t2 -->s t2' ->
      sk_app v1 t2 -->s sk_app v1 t2'
  | s_TAppTabs : forall t,
      lc_sk (sk_tabs t) ->
      sk_tapp (sk_tabs t) -->s t
  | s_TApp : forall t t',
      t -->s t' ->
      sk_tapp t -->s sk_tapp t'
  | s_Succ : forall t t',
      t -->s t' ->
      sk_succ t -->s sk_succ t'
  | s_RecArg : forall n n' b s,
      n -->s n' ->
      lc_sk b -> lc_sk s ->
      sk_natrec n b s -->s sk_natrec n' b s
  | s_RecBase : forall n b b' s,
      numeric_sk n ->
      b -->s b' ->
      lc_sk s ->
      sk_natrec n b s -->s sk_natrec n b' s
  | s_RecStep : forall n b s s',
      numeric_sk n ->
      value_sk b ->
      s -->s s' ->
      sk_natrec n b s -->s sk_natrec n b s'
  | s_RecZero : forall b s,
      value_sk b -> value_sk s ->
      sk_natrec sk_zero b s -->s b
  | s_RecSucc : forall n b s,
      numeric_sk n -> value_sk b -> value_sk s ->
      sk_natrec (sk_succ n) b s -->s
        sk_app (sk_app s n) (sk_natrec n b s)
where "t1 '-->s' t2" := (sstep t1 t2).

Inductive SN_sk : sktm -> Prop :=
  | SN_sk_intro : forall t,
      (forall u, t -->s u -> SN_sk u) -> SN_sk t.

(* Projection: every typed step is a skeleton step after erasure *)

Lemma sk_step : forall t t', t --> t' -> sk t -->s sk t'.
Proof.
  intros t t' H. induction H; simpl.
  - (* ST_AppAbs *)
    change (sk_app (sk_abs (sk t)) (sk v) -->s sk (open_tm_rec 0 v t)).
    rewrite (sk_open_tm t 0 v).
    eapply s_AppAbs.
    + apply sk_lc_tm in H. simpl in H. exact H.
    + apply sk_value. exact H0.
  - (* ST_App1 *)
    eapply s_App1.
    + exact IHstep.
    + exact (sk_lc_tm 0 0 t2 H0).
  - (* ST_App2 *)
    eapply s_App2; [ apply sk_value; exact H | exact IHstep ].
  - (* ST_TAppTabs *)
    change (sk_tapp (sk_tabs (sk t)) -->s sk (open_tm_ty_rec 0 T t)).
    rewrite (sk_open_tm_ty t 0 T).
    eapply s_TAppTabs. exact (sk_lc_tm 0 0 (tm_tabs t) H).
  - (* ST_TApp *)
    eapply s_TApp. exact IHstep.
  - (* ST_Succ *)
    eapply s_Succ. exact IHstep.
  - (* ST_RecArg *)
    eapply s_RecArg.
    + exact IHstep.
    + exact (sk_lc_tm 0 0 b H0).
    + exact (sk_lc_tm 0 0 s H1).
  - (* ST_RecBase *)
    eapply s_RecBase.
    + apply sk_numeric; exact H.
    + exact IHstep.
    + exact (sk_lc_tm 0 0 s H1).
  - (* ST_RecStep *)
    eapply s_RecStep; [ apply sk_numeric; exact H | apply sk_value; exact H0 | exact IHstep ].
  - (* ST_RecZero *)
    eapply s_RecZero; [ apply sk_value; exact H | apply sk_value; exact H0 ].
  - (* ST_RecSucc *)
    eapply s_RecSucc; [ apply sk_numeric; exact H | apply sk_value; exact H0 | apply sk_value; exact H1 ].
Qed.

(* If the skeleton is strongly normalizing then so is the typed term:
   every typed step projects to a skeleton step. *)

Lemma SN_sk_to_SN : forall s, SN_sk s -> forall t, sk t = s -> strongly_normalizing t.
Proof.
  intros s H. induction H as [s Hred IH].
  intros t Heq. apply SN_intro. intros t' Hstep.
  apply (IH (sk t')).
  - rewrite <- Heq. apply sk_step. exact Hstep.
  - reflexivity.
Qed.

(* ============================================================ *)
(* Reducibility candidates over skeletons.                      *)
(* ============================================================ *)

Record cand : Type := mk_cand {
  cpred :> sktm -> Prop;
  cpred_lc : forall t, cpred t -> lc_sk t;
  cpred_sn : forall t, cpred t -> SN_sk t;
  cpred_red : forall t t', cpred t -> t -->s t' -> cpred t';
  cpred_sat : forall t, ~ value_sk t -> lc_sk t -> SN_sk t ->
      (forall t', t -->s t' -> cpred t') -> cpred t
}.

Definition env := atom -> cand.
Definition benv := nat -> cand.

(* Point update of the de Bruijn candidate environment *)
Definition upd_b (n : nat) (C : cand) (rhob : benv) : benv :=
  fun i => if Nat.eqb n i then C else rhob i.

(* Extension of the de Bruijn candidate environment at level 0 *)
Definition bcons (C : cand) (rhob : benv) : benv :=
  fun i => match i with 0 => C | S j => rhob j end.

(* The logical relation.  Free type variables are interpreted by rho,
   bound type variables (de Bruijn levels) by rhob.  The universal case
   is structural in the type: the body is interpreted under a
   candidate-extension of the environment, with no syntactic type
   substitution. *)

Fixpoint R (T : ty) (rho : env) (rhob : benv) : sktm -> Prop :=
  match T with
  | Ty_BVar i => fun t => rhob i t
  | Ty_FVar X => fun t => rho X t
  | Ty_Arrow A B => fun t =>
      lc_sk t /\ SN_sk t /\
      (forall u, R A rho rhob u -> R B rho rhob (sk_app t u))
  | Ty_All A => fun t =>
      lc_sk t /\ SN_sk t /\
      (forall C : cand, R A rho (bcons C rhob) (sk_tapp t))
  | Ty_Nat => fun t => lc_sk t /\ SN_sk t
  end.

(* ---------------- Basic skeleton lemmas ---------------- *)

Lemma numeric_sk_no_step : forall n, numeric_sk n -> forall t', ~ (n -->s t').
Proof.
  intros n Hn. induction Hn as [| m Hm IHm].
  - intros t' Hs. inversion Hs.
  - intros t' Hs. inversion Hs; subst. eapply IHm. eassumption.
Qed.

Lemma value_sk_no_step : forall t, value_sk t -> forall t', ~ (t -->s t').
Proof.
  intros t Hv. induction Hv as [b Hlc | b Hlc | n Hn].
  - intros t' Hs. inversion Hs.
  - intros t' Hs. inversion Hs.
  - intros t' Hs. exact (numeric_sk_no_step n Hn t' Hs).
Qed.

Lemma not_value_sk_app : forall t u, ~ value_sk (sk_app t u).
Proof. intros t u H. inversion H; subst; try discriminate;
  match goal with Hn : numeric_sk _ |- _ => inversion Hn end. Qed.

Lemma not_value_sk_tapp : forall t, ~ value_sk (sk_tapp t).
Proof. intros t H. inversion H; subst; try discriminate;
  match goal with Hn : numeric_sk _ |- _ => inversion Hn end. Qed.

Lemma not_value_sk_natrec : forall n b s, ~ value_sk (sk_natrec n b s).
Proof. intros n b s H. inversion H; subst; try discriminate;
  match goal with Hn : numeric_sk _ |- _ => inversion Hn end. Qed.

Lemma not_value_sk_fvar : forall x, ~ value_sk (sk_fvar x).
Proof. intros x H. inversion H; subst; try discriminate;
  match goal with Hn : numeric_sk _ |- _ => inversion Hn end. Qed.

Lemma not_value_sk_bvar : forall i, ~ value_sk (sk_bvar i).
Proof. intros i H. inversion H; subst; try discriminate;
  match goal with Hn : numeric_sk _ |- _ => inversion Hn end. Qed.

Lemma SN_sk_step : forall t t', SN_sk t -> t -->s t' -> SN_sk t'.
Proof.
  intros t t' H Hs. inversion H as [s Hred]. apply Hred. exact Hs.
Qed.

Lemma SN_sk_succ_inv : forall t, SN_sk (sk_succ t) -> SN_sk t.
Proof.
  intros t H. remember (sk_succ t) as s eqn:E. revert t E.
  induction H as [s Hred IH]. intros t0 E. apply SN_sk_intro. intros t' Hstep.
  apply (IH (sk_succ t')).
  - rewrite E. apply s_Succ. exact Hstep.
  - reflexivity.
Qed.

Lemma lc_sk_at_weaken : forall k k' t, k <= k' -> lc_sk_at k t -> lc_sk_at k' t.
Proof.
  intros k k' t Hle H. revert k' Hle.
  induction H; intros k' Hle.
  - apply lc_sk_bvar. lia.
  - apply lc_sk_fvar.
  - apply lc_sk_abs. apply IHlc_sk_at. lia.
  - apply lc_sk_app; [ apply IHlc_sk_at1 | apply IHlc_sk_at2 ]; auto.
  - apply lc_sk_tabs. apply IHlc_sk_at. auto.
  - apply lc_sk_tapp. apply IHlc_sk_at. auto.
  - apply lc_sk_zero.
  - apply lc_sk_succ. apply IHlc_sk_at. auto.
  - apply lc_sk_natrec; [ apply IHlc_sk_at1 | apply IHlc_sk_at2 | apply IHlc_sk_at3 ]; auto.
Qed.

(* Opening preserves local closedness *)
Lemma lc_open_sk : forall t k u,
  lc_sk_at (S k) t -> lc_sk u -> lc_sk_at k (open_sk_rec k u t).
Proof.
  induction t; intros k u Ht Hu; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. apply lc_sk_at_weaken with (k := 0); [ lia | exact Hu ].
    + apply Nat.eqb_neq in E. apply lc_sk_bvar. inversion Ht; subst; lia.
  - apply lc_sk_fvar.
  - apply lc_sk_abs. apply IHt. inversion Ht; subst; assumption. exact Hu.
  - apply lc_sk_app.
    + apply IHt1. inversion Ht; subst; assumption. exact Hu.
    + apply IHt2. inversion Ht; subst; assumption. exact Hu.
  - apply lc_sk_tabs. apply IHt. inversion Ht; subst; assumption. exact Hu.
  - apply lc_sk_tapp. apply IHt. inversion Ht; subst; assumption. exact Hu.
  - apply lc_sk_zero.
  - apply lc_sk_succ. apply IHt. inversion Ht; subst; assumption. exact Hu.
  - apply lc_sk_natrec.
    + apply IHt1. inversion Ht; subst; assumption. exact Hu.
    + apply IHt2. inversion Ht; subst; assumption. exact Hu.
    + apply IHt3. inversion Ht; subst; assumption. exact Hu.
Qed.

Lemma lc_sk_abs_inv : forall k t, lc_sk_at k (sk_abs t) -> lc_sk_at (S k) t.
Proof. intros k t H. inversion H; subst; assumption. Qed.

Lemma lc_sk_app_inv : forall k t1 t2,
  lc_sk_at k (sk_app t1 t2) -> lc_sk_at k t1 /\ lc_sk_at k t2.
Proof. intros k t1 t2 H. inversion H; subst; auto. Qed.

Lemma lc_sk_tabs_inv : forall k t, lc_sk_at k (sk_tabs t) -> lc_sk_at k t.
Proof. intros k t H. inversion H; subst; assumption. Qed.

Lemma lc_sk_tapp_inv : forall k t, lc_sk_at k (sk_tapp t) -> lc_sk_at k t.
Proof. intros k t H. inversion H; subst; assumption. Qed.

Lemma lc_sk_succ_inv : forall k t, lc_sk_at k (sk_succ t) -> lc_sk_at k t.
Proof. intros k t H. inversion H; subst; assumption. Qed.

Lemma lc_sk_natrec_inv : forall k n b s,
  lc_sk_at k (sk_natrec n b s) -> lc_sk_at k n /\ lc_sk_at k b /\ lc_sk_at k s.
Proof. intros k n b s H. inversion H; subst; auto. Qed.

Lemma lc_sk_step : forall t t', t -->s t' -> lc_sk t -> lc_sk t'.
Proof.
  intros t t' H. induction H; intros Hlc; simpl in *.
  - (* s_AppAbs *)
    apply lc_sk_app_inv in Hlc. destruct Hlc as [Hla Hlv].
    apply lc_open_sk.
    + apply lc_sk_abs_inv in Hla. exact Hla.
    + exact Hlv.
  - (* s_App1 *)
    apply lc_sk_app_inv in Hlc. destruct Hlc as [Hl1 Hl2].
    apply lc_sk_app.
    + apply IHsstep. exact Hl1.
    + exact Hl2.
  - (* s_App2 *)
    apply lc_sk_app_inv in Hlc. destruct Hlc as [Hl1 Hl2].
    apply lc_sk_app.
    + exact Hl1.
    + apply IHsstep. exact Hl2.
  - (* s_TAppTabs *)
    apply lc_sk_tapp_inv in Hlc. apply lc_sk_tabs_inv in Hlc. exact Hlc.
  - (* s_TApp *)
    apply lc_sk_tapp_inv in Hlc. apply lc_sk_tapp. apply IHsstep. exact Hlc.
  - (* s_Succ *)
    apply lc_sk_succ_inv in Hlc. apply lc_sk_succ. apply IHsstep. exact Hlc.
  - (* s_RecArg *)
    apply lc_sk_natrec_inv in Hlc. destruct Hlc as [Hln [Hlb Hls]].
    apply lc_sk_natrec.
    + apply IHsstep. exact Hln.
    + exact Hlb.
    + exact Hls.
  - (* s_RecBase *)
    apply lc_sk_natrec_inv in Hlc. destruct Hlc as [Hln [Hlb Hls]].
    apply lc_sk_natrec.
    + exact Hln.
    + apply IHsstep. exact Hlb.
    + exact Hls.
  - (* s_RecStep *)
    apply lc_sk_natrec_inv in Hlc. destruct Hlc as [Hln [Hlb Hls]].
    apply lc_sk_natrec.
    + exact Hln.
    + exact Hlb.
    + apply IHsstep. exact Hls.
  - (* s_RecZero *)
    apply lc_sk_natrec_inv in Hlc. destruct Hlc as [Hln [Hlb Hls]]. exact Hlb.
  - (* s_RecSucc *)
    apply lc_sk_natrec_inv in Hlc. destruct Hlc as [Hln [Hlb Hls]].
    apply lc_sk_succ_inv in Hln.
    apply lc_sk_app.
    + apply lc_sk_app; [ exact Hls | exact Hln ].
    + apply lc_sk_natrec; assumption.
Qed.

(* A term with no successor is strongly normalizing *)
Lemma SN_sk_stuck : forall t, (forall t', ~ (t -->s t')) -> SN_sk t.
Proof.
  intros t H. apply SN_sk_intro. intros t' Hs. exfalso. apply (H t'). exact Hs.
Qed.

(* ---------------- Candidate structure of R ---------------- *)

Definition is_cand (P : sktm -> Prop) : Prop :=
  (forall t, P t -> lc_sk t) /\
  (forall t, P t -> SN_sk t) /\
  (forall t t', P t -> t -->s t' -> P t') /\
  (forall t, ~ value_sk t -> lc_sk t -> SN_sk t ->
      (forall t', t -->s t' -> P t') -> P t).

Lemma SN_app_of_R_steps : forall A B rho rhob t u,
  (forall v, R B rho rhob v -> SN_sk v) ->
  lc_sk t -> ~ value_sk t ->
  (forall t', t -->s t' -> R (Ty_Arrow A B) rho rhob t') ->
  R A rho rhob u ->
  SN_sk (sk_app t u).
Proof.
  intros A B rho rhob t u HsnB Hlc Hnv Hreds Hu.
  apply SN_sk_intro. intros t' Hstep.
  inversion Hstep; subst.
  - (* s_AppAbs: t = sk_abs t0 *) exfalso. apply Hnv. eapply v_sk_abs. eassumption.
  - (* s_App1 *)
    match goal with
    | Hst : t -->s ?t1' |- SN_sk (sk_app ?t1' u) =>
        destruct (Hreds t1' Hst) as [_ [_ Hfield]];
        apply HsnB; apply Hfield; exact Hu
    end.
  - (* s_App2 *) exfalso. apply Hnv. eassumption.
Qed.

Lemma SN_tapp_of_R_steps : forall A rho rhob t,
  (forall C v, R A rho (bcons C rhob) v -> SN_sk v) ->
  ~ value_sk t ->
  (forall t', t -->s t' -> R (Ty_All A) rho rhob t') ->
  SN_sk (sk_tapp t).
Proof.
  intros A rho rhob t HsnA Hnv Hreds.
  apply SN_sk_intro. intros t' Hstep.
  inversion Hstep; subst.
  - (* s_TAppTabs: t = sk_tabs t0 *) exfalso. apply Hnv. eapply v_sk_tabs. eassumption.
  - (* s_TApp *)
    match goal with
    | Hst : t -->s ?t1' |- SN_sk (sk_tapp ?t1') =>
        destruct (Hreds t1' Hst) as [_ [_ Hfield]];
        exact (HsnA (rhob 0) (sk_tapp t1') (Hfield (rhob 0)))
    end.
Qed.

Lemma R_is_cand : forall T rho rhob, is_cand (R T rho rhob).
Proof.
  induction T; intros rho rhob; simpl.
  - (* Ty_BVar *)
    destruct (rhob n) as [P Plc Psn Pred Psat]. simpl.
    unfold is_cand. auto.
  - (* Ty_FVar *)
    destruct (rho a) as [P Plc Psn Pred Psat]. simpl.
    unfold is_cand. auto.
  - (* Ty_Arrow A B *)
    destruct (IHT1 rho rhob) as [Alc [Asn [Ared Asat]]].
    destruct (IHT2 rho rhob) as [Blc [Bsn [Bred Bsat]]].
    unfold is_cand. split; [ | split; [ | split ] ].
    + intros t [Hlc _]. exact Hlc.
    + intros t [_ [Hsn _]]. exact Hsn.
    + intros t t' [Hlc [Hsn Hfield]] Hstep. split.
      * apply lc_sk_step with (t := t); assumption.
      * split.
        -- apply SN_sk_step with (t := t); assumption.
        -- intros u Hu. apply Bred with (t := sk_app t u).
           ++ apply Hfield. exact Hu.
           ++ apply s_App1; [ exact Hstep | apply Alc; exact Hu ].
    + intros t Hnv Hlc Hsn Hreds. split; [ exact Hlc | split; [ exact Hsn | ] ].
      intros u Hu.
      assert (HSN : SN_sk (sk_app t u)).
      { eapply SN_app_of_R_steps; [ exact Bsn | exact Hlc | exact Hnv | exact Hreds | exact Hu ]. }
      apply Bsat.
      * exact (not_value_sk_app t u).
      * apply lc_sk_app; [ exact Hlc | apply Alc; exact Hu ].
      * exact HSN.
      * intros t' Hstep. inversion Hstep; subst.
        -- exfalso. apply Hnv. eapply v_sk_abs. eassumption.
        -- match goal with
           | Hst : t -->s ?t1' |- R T2 rho rhob (sk_app ?t1' u) =>
               destruct (Hreds t1' Hst) as [_ [_ Hfield]];
               apply Hfield; exact Hu
           end.
        -- match goal with Hv : value_sk t |- _ => exfalso; exact (Hnv Hv) end.
  - (* Ty_All A *)
    destruct (IHT rho rhob) as [Alc [Asn [Ared Asat]]].
    unfold is_cand. split; [ | split; [ | split ] ].
    + intros t [Hlc _]. exact Hlc.
    + intros t [_ [Hsn _]]. exact Hsn.
    + intros t t' [Hlc [Hsn Hfield]] Hstep. split.
      * apply lc_sk_step with (t := t); assumption.
      * split.
        -- apply SN_sk_step with (t := t); assumption.
        -- intros C.
           exact (proj1 (proj2 (proj2 (IHT rho (bcons C rhob))))
                    (sk_tapp t) (sk_tapp t') (Hfield C) (s_TApp t t' Hstep)).
    + intros t Hnv Hlc Hsn Hreds. split; [ exact Hlc | split; [ exact Hsn | ] ].
      intros C.
      assert (HSN : SN_sk (sk_tapp t)).
      { eapply SN_tapp_of_R_steps.
        - intros C' v HR. exact (proj1 (proj2 (IHT rho (bcons C' rhob))) v HR).
        - exact Hnv.
        - exact Hreds. }
      assert (HredsC : forall t', sk_tapp t -->s t' -> R T rho (bcons C rhob) t').
      { intros t' Hstep. inversion Hstep; subst.
        - exfalso. apply Hnv. eapply v_sk_tabs. eassumption.
        - match goal with
           | Hst : t -->s ?t1' |- R T rho (bcons C rhob) (sk_tapp ?t1') =>
               destruct (Hreds t1' Hst) as [_ [_ Hfield]]; exact (Hfield C)
           end. }
      assert (Hnvapp : ~ value_sk (sk_tapp t)) by exact (not_value_sk_tapp t).
      assert (Hlcapp : lc_sk (sk_tapp t)) by (apply lc_sk_tapp; exact Hlc).
      exact (proj2 (proj2 (proj2 (IHT rho (bcons C rhob))))
               (sk_tapp t) Hnvapp Hlcapp HSN HredsC).
  - (* Ty_Nat *)
    unfold is_cand. split; [ | split; [ | split ] ].
    + intros t [Hlc _]. exact Hlc.
    + intros t [_ Hsn]. exact Hsn.
    + intros t t' [Hlc Hsn] Hstep. split.
      * apply lc_sk_step with (t := t); assumption.
      * apply SN_sk_step with (t := t); assumption.
    + intros t Hnv Hlc Hsn Hreds. split; assumption.
Qed.

(* ---------------- Environment agreement ---------------- *)

Definition R_cand (T : ty) (rho : env) (rhob : benv) : cand :=
  mk_cand (R T rho rhob)
    (fun t H => proj1 (R_is_cand T rho rhob) t H)
    (fun t H => proj1 (proj2 (R_is_cand T rho rhob)) t H)
    (fun t t' H Hs => proj1 (proj2 (proj2 (R_is_cand T rho rhob))) t t' H Hs)
    (fun t Hnv Hlc Hsn Hred => proj2 (proj2 (proj2 (R_is_cand T rho rhob))) t Hnv Hlc Hsn Hred).

Lemma R_cand_carrier : forall T rho rhob t, R_cand T rho rhob t <-> R T rho rhob t.
Proof. intros. reflexivity. Qed.

Lemma R_env_agree : forall (T : ty) (rho1 rho2 : env) (rhob1 rhob2 : benv),
  (forall X t, rho1 X t <-> rho2 X t) ->
  (forall i t, rhob1 i t <-> rhob2 i t) ->
  forall t, R T rho1 rhob1 t <-> R T rho2 rhob2 t.
Proof.
  intros T. induction T; intros rho1 rho2 rhob1 rhob2 Hr Hb t; simpl.
  - apply Hb.
  - apply Hr.
  - split.
    + intros [Hlc [Hsn Hf]]. split; [ exact Hlc | split; [ exact Hsn | ] ].
      intros u Hu.
      apply (proj1 (IHT2 rho1 rho2 rhob1 rhob2 Hr Hb (sk_app t u))).
      apply Hf. apply (proj2 (IHT1 rho1 rho2 rhob1 rhob2 Hr Hb u)). exact Hu.
    + intros [Hlc [Hsn Hf]]. split; [ exact Hlc | split; [ exact Hsn | ] ].
      intros u Hu.
      apply (proj2 (IHT2 rho1 rho2 rhob1 rhob2 Hr Hb (sk_app t u))).
      apply Hf. apply (proj1 (IHT1 rho1 rho2 rhob1 rhob2 Hr Hb u)). exact Hu.
  - split.
    + intros [Hlc [Hsn Hf]]. split; [ exact Hlc | split; [ exact Hsn | ] ]. intros C.
      assert (Hb' : forall i t0, bcons C rhob1 i t0 <-> bcons C rhob2 i t0).
      { intros i; destruct i as [|j]; simpl; [ split; auto | apply Hb ]. }
      exact (proj1 (IHT rho1 rho2 (bcons C rhob1) (bcons C rhob2) Hr Hb' (sk_tapp t)) (Hf C)).
    + intros [Hlc [Hsn Hf]]. split; [ exact Hlc | split; [ exact Hsn | ] ]. intros C.
      assert (Hb' : forall i t0, bcons C rhob1 i t0 <-> bcons C rhob2 i t0).
      { intros i; destruct i as [|j]; simpl; [ split; auto | apply Hb ]. }
      exact (proj2 (IHT rho1 rho2 (bcons C rhob1) (bcons C rhob2) Hr Hb' (sk_tapp t)) (Hf C)).
  - split; intros [Hlc Hsn]; split; assumption.
Qed.

(* ---------------- Dependence on the de Bruijn environment ---------------- *)

Fixpoint ty_bound (T : ty) : nat :=
  match T with
  | Ty_BVar i => S i
  | Ty_FVar _ => 0
  | Ty_Arrow A B => Nat.max (ty_bound A) (ty_bound B)
  | Ty_All A => Nat.pred (ty_bound A)
  | Ty_Nat => 0
  end.

Lemma lc_ty_bound : forall k T, lc_ty_at k T -> ty_bound T <= k.
Proof.
  intros k T H. induction H; simpl; try lia.
Qed.

Lemma lt_pred_S : forall n j, S j < n -> j < Nat.pred n.
Proof. intros n j H. destruct n; [ lia | simpl; lia ]. Qed.

Lemma R_rhob_agree : forall (T : ty) (rho : env) (rhob1 rhob2 : benv),
  (forall i, i < ty_bound T -> forall t, rhob1 i t <-> rhob2 i t) ->
  forall t, R T rho rhob1 t <-> R T rho rhob2 t.
Proof.
  intros T. induction T; intros rho rhob1 rhob2 Hag t; simpl.
  - apply Hag. simpl. lia.
  - tauto.
  - assert (Hag1 : forall i, i < ty_bound T1 -> forall t0, rhob1 i t0 <-> rhob2 i t0).
    { intros i Hi. apply Hag. simpl. lia. }
    assert (Hag2 : forall i, i < ty_bound T2 -> forall t0, rhob1 i t0 <-> rhob2 i t0).
    { intros i Hi. apply Hag. simpl. lia. }
    split.
    + intros [Hlc [Hsn Hf]]. split; [ exact Hlc | split; [ exact Hsn | ] ].
      intros u Hu.
      apply (proj1 (IHT2 rho rhob1 rhob2 Hag2 (sk_app t u))).
      apply Hf. apply (proj2 (IHT1 rho rhob1 rhob2 Hag1 u)). exact Hu.
    + intros [Hlc [Hsn Hf]]. split; [ exact Hlc | split; [ exact Hsn | ] ].
      intros u Hu.
      apply (proj2 (IHT2 rho rhob1 rhob2 Hag2 (sk_app t u))).
      apply Hf. apply (proj1 (IHT1 rho rhob1 rhob2 Hag1 u)). exact Hu.
  - split.
    + intros [Hlc [Hsn Hf]]. split; [ exact Hlc | split; [ exact Hsn | ] ]. intros C.
      assert (Hag' : forall i, i < ty_bound T -> forall t0, bcons C rhob1 i t0 <-> bcons C rhob2 i t0).
      { intros i Hi. destruct i as [|j].
        - simpl. split; auto.
        - simpl. assert (Hj : j < ty_bound (Ty_All T)).
          { change (j < Nat.pred (ty_bound T)). apply lt_pred_S. exact Hi. }
          apply (Hag j Hj). }
      exact (proj1 (IHT rho (bcons C rhob1) (bcons C rhob2) Hag' (sk_tapp t)) (Hf C)).
    + intros [Hlc [Hsn Hf]]. split; [ exact Hlc | split; [ exact Hsn | ] ]. intros C.
      assert (Hag' : forall i, i < ty_bound T -> forall t0, bcons C rhob1 i t0 <-> bcons C rhob2 i t0).
      { intros i Hi. destruct i as [|j].
        - simpl. split; auto.
        - simpl. assert (Hj : j < ty_bound (Ty_All T)).
          { change (j < Nat.pred (ty_bound T)). apply lt_pred_S. exact Hi. }
          apply (Hag j Hj). }
      exact (proj2 (IHT rho (bcons C rhob1) (bcons C rhob2) Hag' (sk_tapp t)) (Hf C)).
  - split; intros [Hlc Hsn]; split; assumption.
Qed.

Lemma R_rhob_irrel : forall (T : ty) (rho : env) (rhob1 rhob2 : benv),
  lc_ty_at 0 T ->
  forall t, R T rho rhob1 t <-> R T rho rhob2 t.
Proof.
  intros T rho rhob1 rhob2 Hlc t.
  apply R_rhob_agree. intros i Hi.
  pose proof (lc_ty_bound 0 T Hlc). lia.
Qed.

(* ---------------- Dependence on free type variables ---------------- *)

Fixpoint ty_free (X : atom) (T : ty) : Prop :=
  match T with
  | Ty_BVar _ => False
  | Ty_FVar Y => X = Y
  | Ty_Arrow A B => ty_free X A \/ ty_free X B
  | Ty_All A => ty_free X A
  | Ty_Nat => False
  end.

Lemma R_atom_agree : forall (T : ty) (rho1 rho2 : env) (rhob : benv),
  (forall X, ty_free X T -> forall t, rho1 X t <-> rho2 X t) ->
  forall t, R T rho1 rhob t <-> R T rho2 rhob t.
Proof.
  intros T. induction T; intros rho1 rho2 rhob Hag t; simpl.
  - tauto.
  - apply Hag. simpl. reflexivity.
  - assert (Hag1 : forall X, ty_free X T1 -> forall t0, rho1 X t0 <-> rho2 X t0).
    { intros X Hf. apply Hag. simpl. auto. }
    assert (Hag2 : forall X, ty_free X T2 -> forall t0, rho1 X t0 <-> rho2 X t0).
    { intros X Hf. apply Hag. simpl. auto. }
    split.
    + intros [Hlc [Hsn Hf]]. split; [ exact Hlc | split; [ exact Hsn | ] ].
      intros u Hu.
      apply (proj1 (IHT2 rho1 rho2 rhob Hag2 (sk_app t u))).
      apply Hf. apply (proj2 (IHT1 rho1 rho2 rhob Hag1 u)). exact Hu.
    + intros [Hlc [Hsn Hf]]. split; [ exact Hlc | split; [ exact Hsn | ] ].
      intros u Hu.
      apply (proj2 (IHT2 rho1 rho2 rhob Hag2 (sk_app t u))).
      apply Hf. apply (proj1 (IHT1 rho1 rho2 rhob Hag1 u)). exact Hu.
  - assert (Hag1 : forall X, ty_free X T -> forall t0, rho1 X t0 <-> rho2 X t0).
    { intros X Hf. apply Hag. simpl. exact Hf. }
    split.
    + intros [Hlc [Hsn Hf]]. split; [ exact Hlc | split; [ exact Hsn | ] ]. intros C.
      apply (proj1 (IHT rho1 rho2 (bcons C rhob) Hag1 (sk_tapp t))). apply Hf.
    + intros [Hlc [Hsn Hf]]. split; [ exact Hlc | split; [ exact Hsn | ] ]. intros C.
      apply (proj2 (IHT rho1 rho2 (bcons C rhob) Hag1 (sk_tapp t))). apply Hf.
  - split; intros [Hlc Hsn]; split; assumption.
Qed.

(* ---------------- Type-level local closure ---------------- *)

Lemma lc_ty_at_weaken : forall k k' T, k <= k' -> lc_ty_at k T -> lc_ty_at k' T.
Proof.
  intros k k' T. revert k k'. induction T; intros k k' Hle H; inversion H; subst;
    eauto using lc_ty_at.
  - (* bvar *) apply lc_ty_bvar. lia.
  - (* all *) apply lc_ty_all. apply IHT with (k := S k). lia. assumption.
Qed.

Lemma lc_ty_open : forall T k U,
  lc_ty_at (S k) T -> lc_ty_at 0 U -> lc_ty_at k (open_ty_rec k U T).
Proof.
  induction T; intros k U HT HU; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. apply lc_ty_at_weaken with (k := 0); [ lia | exact HU ].
    + apply Nat.eqb_neq in E. apply lc_ty_bvar. inversion HT; subst; lia.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow.
    + apply IHT1. inversion HT; subst; assumption. exact HU.
    + apply IHT2. inversion HT; subst; assumption. exact HU.
  - apply lc_ty_all. apply IHT. inversion HT; subst; assumption. exact HU.
  - apply lc_ty_nat.
Qed.

Lemma lc_ty_open_inv : forall T K k X,
  lc_ty_at K (open_ty_rec k (Ty_FVar X) T) -> lc_ty_at (Nat.max K (S k)) T.
Proof.
  induction T; intros K k X H; simpl in *.
  - destruct (Nat.eqb k n) eqn:E; simpl in H.
    + apply Nat.eqb_eq in E. subst. apply lc_ty_bvar. lia.
    + apply Nat.eqb_neq in E. apply lc_ty_bvar. inversion H; subst; lia.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow.
    + apply IHT1 with (K := K) (k := k) (X := X). inversion H; subst; assumption.
    + apply IHT2 with (K := K) (k := k) (X := X). inversion H; subst; assumption.
  - apply lc_ty_all. apply IHT with (K := S K) (k := S k) (X := X).
    inversion H; subst; assumption.
  - apply lc_ty_nat.
Qed.

(* fresh atoms *)

Fixpoint max_list (xs : list nat) : nat :=
  match xs with
  | [] => 0
  | x :: xs' => Nat.max x (max_list xs')
  end.

Lemma max_list_spec : forall xs x, In x xs -> x <= max_list xs.
Proof.
  induction xs as [|y ys IH]; intros x Hin; simpl in *.
  - destruct Hin.
  - destruct Hin as [-> | Hin].
    + apply Nat.le_max_l.
    + apply Nat.le_trans with (m := max_list ys).
      * apply IH. exact Hin.
      * apply Nat.le_max_r.
Qed.

Definition fresh_atom (xs : list atom) : atom := S (max_list xs).

Lemma fresh_atom_spec : forall xs, ~ In (fresh_atom xs) xs.
Proof.
  intros xs Hin. unfold fresh_atom in Hin.
  pose proof (max_list_spec xs (S (max_list xs)) Hin). lia.
Qed.

(* well-formed types are locally closed *)
Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> lc_ty_at 0 T.
Proof.
  intros Delta T H. induction H.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; assumption.
  - apply lc_ty_all.
    pose proof (H0 (fresh_atom L) (fresh_atom_spec L)) as Hlc.
    apply lc_ty_open_inv with (K := 0) (k := 0) (X := fresh_atom L).
    simpl. exact Hlc.
  - apply lc_ty_nat.
Qed.

(* Typing derivations only mention locally closed types *)
Lemma has_type_lc_ty : forall Delta Gamma t T, has_type Delta Gamma t T -> lc_ty_at 0 T.
Proof.
  intros Delta Gamma t T H. induction H.
  - (* T_Var *) exact (wf_ty_lc Delta T H0).
  - (* T_Abs *) apply lc_ty_arrow.
    + exact (wf_ty_lc Delta T1 H).
    + exact (H1 (fresh_atom L) (fresh_atom_spec L)).
  - (* T_App *) inversion IHhas_type1; subst. assumption.
  - (* T_TAbs *) apply lc_ty_all.
    pose proof (H0 (fresh_atom L) (fresh_atom_spec L)) as Hlc.
    apply lc_ty_open_inv with (K := 0) (k := 0) (X := fresh_atom L).
    simpl. exact Hlc.
  - (* T_TApp *) apply lc_ty_open.
    + inversion IHhas_type; subst. assumption.
    + exact (wf_ty_lc Delta U H0).
  - (* T_Zero *) apply lc_ty_nat.
  - (* T_Succ *) apply lc_ty_nat.
  - (* T_Rec *) exact IHhas_type2.
Qed.

(* Opening the type at level n corresponds to point-updating the
   candidate environment at n, provided the substituted type is locally
   closed.  This is where the impredicative universal is handled: the
   term never changes, and the bound type variable is interpreted by a
   candidate. *)
Lemma R_open_ty : forall (T : ty) (k : nat) (V : ty) (rho : env) (rhob : benv) (t : sktm),
  lc_ty_at 0 V ->
  (R (open_ty_rec k V T) rho rhob t <->
   R T rho (upd_b k (R_cand V rho rhob) rhob) t).
Proof.
  intros T. induction T; intros k V rho rhob t0 HlcV; simpl.
  - (* Ty_BVar *)
    destruct (Nat.eqb k n) eqn:E.
    + simpl. unfold upd_b. rewrite E. simpl. apply iff_sym. apply R_cand_carrier.
    + simpl. unfold upd_b. rewrite E. simpl. reflexivity.
  - (* Ty_FVar *) reflexivity.
  - (* Ty_Arrow A B *)
    split.
    + intros [Hlc [Hsn Hf]]. split; [ exact Hlc | split; [ exact Hsn | ] ]. intros u Hu.
      apply (proj1 (IHT2 k V rho rhob (sk_app t0 u) HlcV)).
      apply Hf. apply (proj2 (IHT1 k V rho rhob u HlcV)). exact Hu.
    + intros [Hlc [Hsn Hf]]. split; [ exact Hlc | split; [ exact Hsn | ] ]. intros u Hu.
      apply (proj2 (IHT2 k V rho rhob (sk_app t0 u) HlcV)).
      apply Hf. apply (proj1 (IHT1 k V rho rhob u HlcV)). exact Hu.
  - (* Ty_All A *)
    split.
    + intros [Hlc [Hsn Hf]]. split; [ exact Hlc | split; [ exact Hsn | ] ]. intros C.
      set (E1 := upd_b (S k) (R_cand V rho (bcons C rhob)) (bcons C rhob)).
      assert (EqEnv : forall i t1, E1 i t1 <-> bcons C (upd_b k (R_cand V rho rhob) rhob) i t1).
      { intros i t1. subst E1. destruct i as [|j].
        - unfold upd_b. simpl. tauto.
        - unfold upd_b. simpl. destruct (Nat.eqb k j) eqn:E; simpl.
          + apply R_rhob_irrel. exact HlcV.
          + tauto. }
      apply (proj1 (R_env_agree T rho rho E1 (bcons C (upd_b k (R_cand V rho rhob) rhob))
                     (fun X t1 => iff_refl (rho X t1)) EqEnv (sk_tapp t0))).
      apply (proj1 (IHT (S k) V rho (bcons C rhob) (sk_tapp t0) HlcV)).
      exact (Hf C).
    + intros [Hlc [Hsn Hf]]. split; [ exact Hlc | split; [ exact Hsn | ] ]. intros C.
      set (E1 := upd_b (S k) (R_cand V rho (bcons C rhob)) (bcons C rhob)).
      assert (EqEnv : forall i t1, E1 i t1 <-> bcons C (upd_b k (R_cand V rho rhob) rhob) i t1).
      { intros i t1. subst E1. destruct i as [|j].
        - unfold upd_b. simpl. tauto.
        - unfold upd_b. simpl. destruct (Nat.eqb k j) eqn:E; simpl.
          + apply R_rhob_irrel. exact HlcV.
          + tauto. }
      apply (proj2 (IHT (S k) V rho (bcons C rhob) (sk_tapp t0) HlcV)).
      apply (proj2 (R_env_agree T rho rho E1 (bcons C (upd_b k (R_cand V rho rhob) rhob))
                    (fun X t1 => iff_refl (rho X t1)) EqEnv (sk_tapp t0))).
      exact (Hf C).
  - (* Ty_Nat *)
    tauto.
Qed.

(* Stuck terms (no steps, not values) are reducible at every type. *)

Definition stuck_sk (t : sktm) : Prop :=
  (forall t', ~ (t -->s t')) /\ ~ value_sk t.

Lemma stuck_R : forall (T : ty) (rho : env) (rhob : benv) (t : sktm),
  lc_sk t -> stuck_sk t -> R T rho rhob t.
Proof.
  intros T. induction T; intros rho rhob t Hlc Hst; simpl.
  - (* Ty_BVar *)
    destruct Hst as [Hns Hnv].
    apply (cpred_sat (rhob n) t Hnv Hlc).
    + apply SN_sk_stuck. exact Hns.
    + intros t' Hs. exfalso. exact (Hns t' Hs).
  - (* Ty_FVar *)
    destruct Hst as [Hns Hnv].
    apply (cpred_sat (rho a) t Hnv Hlc).
    + apply SN_sk_stuck. exact Hns.
    + intros t' Hs. exfalso. exact (Hns t' Hs).
  - (* Ty_Arrow A B *)
    destruct Hst as [Hns Hnv]. split; [ exact Hlc | split ].
    + apply SN_sk_stuck. exact Hns.
    + intros u Hu.
      apply IHT2.
      * apply lc_sk_app.
        -- exact Hlc.
        -- exact (proj1 (R_is_cand T1 rho rhob) u Hu).
      * split.
        -- intros t' Hstep. inversion Hstep; subst.
           ++ exfalso. apply Hnv. eapply v_sk_abs. eassumption.
           ++ match goal with Hst' : t -->s ?t1' |- False => exact (Hns t1' Hst') end.
           ++ exfalso. apply Hnv. eassumption.
        -- exact (not_value_sk_app t u).
  - (* Ty_All A *)
    destruct Hst as [Hns Hnv]. split; [ exact Hlc | split ].
    + apply SN_sk_stuck. exact Hns.
    + intros C.
      apply IHT.
      * apply lc_sk_tapp. exact Hlc.
      * split.
        -- intros t' Hstep. inversion Hstep; subst.
           ++ exfalso. apply Hnv. eapply v_sk_tabs. eassumption.
           ++ match goal with Hst' : t -->s ?t1' |- False => exact (Hns t1' Hst') end.
        -- exact (not_value_sk_tapp t).
  - (* Ty_Nat *)
    destruct Hst as [Hns Hnv]. split; [ exact Hlc | apply SN_sk_stuck; exact Hns ].
Qed.

Lemma R_fvar : forall (T : ty) (rho : env) (rhob : benv) (x : atom),
  R T rho rhob (sk_fvar x).
Proof.
  intros. apply stuck_R.
  - constructor.
  - split.
    + intros t' Hs. inversion Hs.
    + apply not_value_sk_fvar.
Qed.

(* ---------------- Free term variables of skeletons ---------------- *)

Fixpoint free_sk (x : atom) (t : sktm) : Prop :=
  match t with
  | sk_bvar _ => False
  | sk_fvar y => x = y
  | sk_abs t1 => free_sk x t1
  | sk_app t1 t2 => free_sk x t1 \/ free_sk x t2
  | sk_tabs t1 => free_sk x t1
  | sk_tapp t1 => free_sk x t1
  | sk_zero => False
  | sk_succ t1 => free_sk x t1
  | sk_natrec n b s => free_sk x n \/ free_sk x b \/ free_sk x s
  end.

(* Opening a locally closed skeleton at any level is the identity *)
Lemma open_sk_rec_lc_any : forall t k u, lc_sk_at k t -> open_sk_rec k u t = t.
Proof.
  induction t; intros k u H; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. inversion H; subst. exfalso. lia.
    + reflexivity.
  - reflexivity.
  - f_equal. apply IHt. inversion H; subst. assumption.
  - apply lc_sk_app_inv in H. destruct H as [H1 H2].
    rewrite (IHt1 k u H1). rewrite (IHt2 k u H2). reflexivity.
  - f_equal. apply IHt. apply lc_sk_tabs_inv in H. exact H.
  - f_equal. apply IHt. apply lc_sk_tapp_inv in H. exact H.
  - reflexivity.
  - f_equal. apply IHt. apply lc_sk_succ_inv in H. exact H.
  - apply lc_sk_natrec_inv in H. destruct H as [H1 [H2 H3]].
    rewrite (IHt1 k u H1). rewrite (IHt2 k u H2). rewrite (IHt3 k u H3).
    reflexivity.
Qed.

Lemma open_sk_lc : forall t u, lc_sk t -> open_sk t u = t.
Proof. intros. apply open_sk_rec_lc_any. exact H. Qed.

(* Substituting under an opening *)
Lemma sksubst_open_sk_gen : forall (t : sktm) (sigma : atom -> sktm) (k : nat) (x : atom) (u : sktm),
  (forall y, lc_sk (sigma y)) ->
  lc_sk u ->
  ~ free_sk x t ->
  sksubst (fun y => if Nat.eqb y x then u else sigma y)
          (open_sk_rec k (sk_fvar x) t)
  = open_sk_rec k u (sksubst sigma t).
Proof.
  induction t; intros sigma k x u Hsig Hu Hfree; simpl in *.
  - (* bvar *) destruct (Nat.eqb k n) eqn:E.
    + simpl. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - (* fvar *) simpl.
    rewrite (open_sk_rec_lc_any (sigma a) k u).
    + destruct (Nat.eqb a x) eqn:E.
      * apply Nat.eqb_eq in E. subst. exfalso. apply Hfree. reflexivity.
      * reflexivity.
    + apply lc_sk_at_weaken with (k := 0); [ lia | apply Hsig ].
  - (* abs *) simpl. f_equal. apply IHt with (k := S k); auto.
  - (* app *) simpl.
    assert (Hf1 : ~ free_sk x t1) by tauto.
    assert (Hf2 : ~ free_sk x t2) by tauto.
    rewrite (IHt1 sigma k x u Hsig Hu Hf1).
    rewrite (IHt2 sigma k x u Hsig Hu Hf2).
    reflexivity.
  - (* tabs *) simpl. f_equal. apply IHt with (k := k); auto.
  - (* tapp *) simpl. f_equal. apply IHt with (k := k); auto.
  - reflexivity.
  - (* succ *) simpl. f_equal. apply IHt with (k := k); auto.
  - (* natrec *) simpl.
    assert (Hf1 : ~ free_sk x t1) by tauto.
    assert (Hf2 : ~ free_sk x t2) by tauto.
    assert (Hf3 : ~ free_sk x t3) by tauto.
    rewrite (IHt1 sigma k x u Hsig Hu Hf1).
    rewrite (IHt2 sigma k x u Hsig Hu Hf2).
    rewrite (IHt3 sigma k x u Hsig Hu Hf3).
    reflexivity.
Qed.

Lemma sksubst_id : forall t, sksubst (fun x => sk_fvar x) t = t.
Proof.
  induction t; simpl; auto; try (rewrite IHt; reflexivity);
    try (rewrite IHt1, IHt2; reflexivity);
    try (rewrite IHt1, IHt2, IHt3; reflexivity).
Qed.

(* ---------------- Primitive recursion ---------------- *)

(* Auxiliary: given a fixed numeric numeral n, recursion is reducible.
   The case where n is a successor and both branches are values is
   supplied by [Hsucc]. *)
Lemma natrec_sat_T : forall (T : ty) (rho : env) (rhob : benv) (n : sktm),
  numeric_sk n -> lc_sk n -> SN_sk n ->
  (forall n0 b0 s0, n = sk_succ n0 -> value_sk b0 -> value_sk s0 ->
      R T rho rhob b0 -> R (Ty_Arrow Ty_Nat (Ty_Arrow T T)) rho rhob s0 ->
      R T rho rhob (sk_app (sk_app s0 n0) (sk_natrec n0 b0 s0))) ->
  forall b0 s0, R T rho rhob b0 ->
    R (Ty_Arrow Ty_Nat (Ty_Arrow T T)) rho rhob s0 ->
    R T rho rhob (sk_natrec n b0 s0).
Proof.
  intros T rho rhob n Hnum Hlcn Hsn Hsucc b s Hb Hs.
  assert (Hmain : forall b0, SN_sk b0 -> forall s1, R T rho rhob b0 ->
      R (Ty_Arrow Ty_Nat (Ty_Arrow T T)) rho rhob s1 ->
      R T rho rhob (sk_natrec n b0 s1)).
  { intros b0 Hsnb. induction Hsnb as [b0 Hredb IHb]. intros s1 Hbmain Hs1.
    assert (Hinner : forall s2, SN_sk s2 -> R T rho rhob b0 ->
        R (Ty_Arrow Ty_Nat (Ty_Arrow T T)) rho rhob s2 ->
        R T rho rhob (sk_natrec n b0 s2)).
    { intros s2 Hsns. induction Hsns as [s2 Hreds IHs]. intros Hb0 Hs2.
      assert (HredsRT : forall t', sk_natrec n b0 s2 -->s t' -> R T rho rhob t').
      { intros t' Hstep. inversion Hstep; subst.
        - (* s_RecArg *) exfalso.
          match goal with Hst : n -->s ?n' |- False =>
            exact (numeric_sk_no_step n Hnum n' Hst) end.
        - (* s_RecBase *)
          match goal with
          | Hst : b0 -->s ?b' |- R T rho rhob (sk_natrec n ?b' s2) =>
              apply (IHb b' Hst s2)
          end.
          apply (proj1 (proj2 (proj2 (R_is_cand T rho rhob))) b0 b' Hb0 ltac:(eassumption)).
          exact Hs2.
        - (* s_RecStep *)
          match goal with
          | Hst : s2 -->s ?s' |- R T rho rhob (sk_natrec n b0 ?s') =>
              apply (IHs s' Hst Hb0)
          end.
          apply (proj1 (proj2 (proj2 (R_is_cand (Ty_Arrow Ty_Nat (Ty_Arrow T T)) rho rhob))) s2 s' Hs2 ltac:(eassumption)).
        - (* s_RecZero *) exact Hb0.
        - (* s_RecSucc *)
          match goal with
          | Hn0 : numeric_sk ?n0, Hvb : value_sk b0, Hvs : value_sk s2
            |- R T rho rhob (sk_app (sk_app s2 ?n0) (sk_natrec ?n0 b0 s2)) =>
              exact (Hsucc n0 b0 s2 eq_refl Hvb Hvs Hb0 Hs2)
          end.
      }
      assert (Hnv : ~ value_sk (sk_natrec n b0 s2)) by exact (not_value_sk_natrec n b0 s2).
      assert (Hlcnr : lc_sk (sk_natrec n b0 s2)).
      { apply lc_sk_natrec.
        - exact Hlcn.
        - exact (proj1 (R_is_cand T rho rhob) b0 Hb0).
        - exact (proj1 (R_is_cand (Ty_Arrow Ty_Nat (Ty_Arrow T T)) rho rhob) s2 Hs2). }
      assert (HSN : SN_sk (sk_natrec n b0 s2)).
      { apply SN_sk_intro. intros t' Hstep.
        exact (proj1 (proj2 (R_is_cand T rho rhob)) t' (HredsRT t' Hstep)). }
      exact (proj2 (proj2 (proj2 (R_is_cand T rho rhob)))
               (sk_natrec n b0 s2) Hnv Hlcnr HSN HredsRT).
    }
    exact (Hinner s1 (proj1 (proj2 (R_is_cand (Ty_Arrow Ty_Nat (Ty_Arrow T T)) rho rhob)) s1 Hs1) Hbmain Hs1).
  }
  exact (Hmain b (proj1 (proj2 (R_is_cand T rho rhob)) b Hb) s Hb Hs).
Qed.

(* Recursion at a numeric value *)
Lemma natrec_numeric_R : forall (T : ty) (rho : env) (rhob : benv) (n : sktm),
  numeric_sk n -> lc_sk n -> SN_sk n ->
  forall b s, R T rho rhob b ->
    R (Ty_Arrow Ty_Nat (Ty_Arrow T T)) rho rhob s ->
    R T rho rhob (sk_natrec n b s).
Proof.
  intros T rho rhob n Hnum. induction Hnum as [| n0 Hnum0 IHnum];
    intros Hlcn Hsn b s Hb Hs.
  - (* zero *)
    apply natrec_sat_T with (n := sk_zero).
    + constructor.
    + constructor.
    + apply SN_sk_stuck. intros t' Hstep. inversion Hstep.
    + intros n1 b' s' Heq Hvb Hvs Hb' Hs'. discriminate Heq.
    + exact Hb.
    + exact Hs.
  - (* succ n0 *)
    apply natrec_sat_T with (n := sk_succ n0).
    + constructor. exact Hnum0.
    + exact Hlcn.
    + exact Hsn.
    + intros n1 b' s' Heq Hvb Hvs Hb' Hs'.
      injection Heq as Hn. subst n1.
      assert (HRn0 : R Ty_Nat rho rhob n0).
      { split.
        - apply lc_sk_succ_inv in Hlcn. exact Hlcn.
        - apply SN_sk_succ_inv in Hsn. exact Hsn. }
      pose proof (proj2 (proj2 Hs') n0 HRn0) as HRapp.
      simpl in HRapp.
      pose proof (IHnum (lc_sk_succ_inv 0 n0 Hlcn) (SN_sk_succ_inv n0 Hsn) b' s' Hb' Hs') as HRrec.
      exact (proj2 (proj2 HRapp) (sk_natrec n0 b' s') HRrec).
    + exact Hb.
    + exact Hs.
Qed.

(* Recursion at an arbitrary strongly normalizing natural *)
Lemma natrec_R : forall (T : ty) (rho : env) (rhob : benv) (n : sktm),
  SN_sk n -> lc_sk n ->
  forall b s, R T rho rhob b ->
    R (Ty_Arrow Ty_Nat (Ty_Arrow T T)) rho rhob s ->
    R T rho rhob (sk_natrec n b s).
Proof.
  intros T rho rhob n Hsn. induction Hsn as [n Hred IH]. intros Hlc b s Hb Hs.
  assert (Hsn' : SN_sk n) by (constructor; exact Hred).
  assert (HredsRT : forall t', sk_natrec n b s -->s t' -> R T rho rhob t').
  { intros t' Hstep. inversion Hstep; subst.
    - (* s_RecArg *)
      match goal with Hst : n -->s ?m |- R T rho rhob (sk_natrec ?m b s) =>
        apply (IH m Hst (lc_sk_step n m Hst Hlc) b s Hb Hs) end.
    - (* s_RecBase *)
      match goal with
      | Hnum : numeric_sk n, Hst : b -->s ?b' |- R T rho rhob (sk_natrec n ?b' s) =>
          apply (natrec_numeric_R T rho rhob n Hnum Hlc Hsn' b' s)
      end.
      apply (proj1 (proj2 (proj2 (R_is_cand T rho rhob))) b b' Hb ltac:(eassumption)).
      exact Hs.
    - (* s_RecStep *)
      match goal with
      | Hnum : numeric_sk n, Hst : s -->s ?s' |- R T rho rhob (sk_natrec n b ?s') =>
          apply (natrec_numeric_R T rho rhob n Hnum Hlc Hsn' b s')
      end.
      exact Hb.
      apply (proj1 (proj2 (proj2 (R_is_cand (Ty_Arrow Ty_Nat (Ty_Arrow T T)) rho rhob))) s s' Hs ltac:(eassumption)).
    - (* s_RecZero *) exact Hb.
    - (* s_RecSucc *)
      match goal with
      | Hnum0 : numeric_sk ?n0, Hvb : value_sk b, Hvs : value_sk s
        |- R T rho rhob (sk_app (sk_app s ?n0) (sk_natrec ?n0 b s)) =>
          assert (Hlcn0 : lc_sk n0) by (apply lc_sk_succ_inv in Hlc; exact Hlc);
          assert (Hsn0 : SN_sk n0) by (apply SN_sk_succ_inv in Hsn'; exact Hsn');
          assert (HRn0 : R Ty_Nat rho rhob n0) by (split; assumption);
          pose proof (proj2 (proj2 Hs) n0 HRn0) as HRapp;
          simpl in HRapp;
          pose proof (natrec_numeric_R T rho rhob n0 Hnum0 Hlcn0 Hsn0 b s Hb Hs) as HRrec;
          exact (proj2 (proj2 HRapp) (sk_natrec n0 b s) HRrec)
      end.
  }
  assert (Hnv : ~ value_sk (sk_natrec n b s)) by exact (not_value_sk_natrec n b s).
  assert (Hlcnr : lc_sk (sk_natrec n b s)).
  { apply lc_sk_natrec.
    - exact Hlc.
    - exact (proj1 (R_is_cand T rho rhob) b Hb).
    - exact (proj1 (R_is_cand (Ty_Arrow Ty_Nat (Ty_Arrow T T)) rho rhob) s Hs). }
  assert (HSN : SN_sk (sk_natrec n b s)).
  { apply SN_sk_intro. intros t' Hstep.
    exact (proj1 (proj2 (R_is_cand T rho rhob)) t' (HredsRT t' Hstep)). }
  exact (proj2 (proj2 (proj2 (R_is_cand T rho rhob)))
           (sk_natrec n b s) Hnv Hlcnr HSN HredsRT).
Qed.

(* ---------------- More skeleton helpers ---------------- *)

Lemma lc_open_sk_inv : forall (t : sktm) (K k : nat) (x : atom),
  lc_sk_at K (open_sk_rec k (sk_fvar x) t) -> lc_sk_at (Nat.max K (S k)) t.
Proof.
  induction t; intros K k x H; simpl in *.
  - destruct (Nat.eqb k n) eqn:E; simpl in H.
    + apply Nat.eqb_eq in E. subst. apply lc_sk_bvar. lia.
    + apply Nat.eqb_neq in E. apply lc_sk_bvar. inversion H; subst; lia.
  - apply lc_sk_fvar.
  - apply lc_sk_abs. apply IHt with (K := S K) (k := S k) (x := x).
    inversion H; subst; assumption.
  - apply lc_sk_app_inv in H. destruct H as [H1 H2].
    apply lc_sk_app.
    + apply IHt1 with (K := K) (k := k) (x := x). exact H1.
    + apply IHt2 with (K := K) (k := k) (x := x). exact H2.
  - apply lc_sk_tabs. apply IHt with (K := K) (k := k) (x := x).
    apply lc_sk_tabs_inv in H. exact H.
  - apply lc_sk_tapp. apply IHt with (K := K) (k := k) (x := x).
    apply lc_sk_tapp_inv in H. exact H.
  - apply lc_sk_zero.
  - apply lc_sk_succ. apply IHt with (K := K) (k := k) (x := x).
    apply lc_sk_succ_inv in H. exact H.
  - apply lc_sk_natrec_inv in H. destruct H as [H1 [H2 H3]].
    apply lc_sk_natrec.
    + apply IHt1 with (K := K) (k := k) (x := x). exact H1.
    + apply IHt2 with (K := K) (k := k) (x := x). exact H2.
    + apply IHt3 with (K := K) (k := k) (x := x). exact H3.
Qed.

Lemma SN_sk_value : forall t, value_sk t -> SN_sk t.
Proof.
  intros t Hv. apply SN_sk_intro. intros t' Hs.
  exfalso. exact (value_sk_no_step t Hv t' Hs).
Qed.

Lemma SN_sk_succ : forall t, SN_sk t -> SN_sk (sk_succ t).
Proof.
  intros t H. induction H as [t Hred IH].
  apply SN_sk_intro. intros t' Hstep. inversion Hstep; subst.
  apply IH. eassumption.
Qed.

(* Applying an abstraction to a related argument *)
Lemma R_abs_app : forall (A B : ty) (rho : env) (rhob : benv) (b u : sktm),
  lc_sk (sk_abs b) ->
  (forall u, R A rho rhob u -> R B rho rhob (open_sk b u)) ->
  R A rho rhob u ->
  R B rho rhob (sk_app (sk_abs b) u).
Proof.
  intros A B rho rhob b u Hlc Hbeta Hu.
  assert (H : forall u0, SN_sk u0 -> R A rho rhob u0 ->
      R B rho rhob (sk_app (sk_abs b) u0)).
  { intros u0 Hsn. induction Hsn as [u0 Hred IH]. intros Hu0.
    assert (Hreds : forall t', sk_app (sk_abs b) u0 -->s t' -> R B rho rhob t').
    { intros t' Hstep. inversion Hstep; subst.
      - (* s_AppAbs *) exact (Hbeta u0 Hu0).
      - (* s_App1 *) exfalso.
        match goal with Hst : sk_abs b -->s ?v |- _ =>
          exact (value_sk_no_step (sk_abs b) (v_sk_abs b Hlc) v Hst) end.
      - (* s_App2 *)
        match goal with Hst : u0 -->s ?v |- R B rho rhob (sk_app (sk_abs b) ?v) =>
          apply (IH v Hst);
          apply (proj1 (proj2 (proj2 (R_is_cand A rho rhob))) u0 v Hu0 Hst)
        end.
    }
    assert (Hnv : ~ value_sk (sk_app (sk_abs b) u0)) by exact (not_value_sk_app (sk_abs b) u0).
    assert (Hlcapp : lc_sk (sk_app (sk_abs b) u0)).
    { apply lc_sk_app; [ exact Hlc | exact (proj1 (R_is_cand A rho rhob) u0 Hu0) ]. }
    assert (HSN : SN_sk (sk_app (sk_abs b) u0)).
    { apply SN_sk_intro. intros t' Hstep.
      exact (proj1 (proj2 (R_is_cand B rho rhob)) t' (Hreds t' Hstep)). }
    exact (proj2 (proj2 (proj2 (R_is_cand B rho rhob)))
             (sk_app (sk_abs b) u0) Hnv Hlcapp HSN Hreds).
  }
  exact (H u (proj1 (proj2 (R_is_cand A rho rhob)) u Hu) Hu).
Qed.

(* Type application of a type abstraction *)
Lemma R_tapp_tabs : forall (T : ty) (rho : env) (rhob : benv) (b : sktm),
  lc_sk (sk_tabs b) -> R T rho rhob b -> R T rho rhob (sk_tapp (sk_tabs b)).
Proof.
  intros T rho rhob b Hlc HR.
  assert (Hreds : forall t', sk_tapp (sk_tabs b) -->s t' -> R T rho rhob t').
  { intros t' Hstep. inversion Hstep; subst.
    - (* s_TAppTabs *) exact HR.
    - (* s_TApp *) exfalso.
      match goal with Hst : sk_tabs b -->s ?v |- _ =>
        exact (value_sk_no_step (sk_tabs b) (v_sk_tabs b Hlc) v Hst) end.
  }
  assert (Hnv : ~ value_sk (sk_tapp (sk_tabs b))) by exact (not_value_sk_tapp (sk_tabs b)).
  assert (Hlcapp : lc_sk (sk_tapp (sk_tabs b))) by (apply lc_sk_tapp; exact Hlc).
  assert (HSN : SN_sk (sk_tapp (sk_tabs b))).
  { apply SN_sk_intro. intros t' Hstep.
    exact (proj1 (proj2 (R_is_cand T rho rhob)) t' (Hreds t' Hstep)). }
  exact (proj2 (proj2 (proj2 (R_is_cand T rho rhob)))
           (sk_tapp (sk_tabs b)) Hnv Hlcapp HSN Hreds).
Qed.

(* ---------------- Free variable lists and lookup ---------------- *)

Fixpoint tm_fvars (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs _ t1 => tm_fvars t1
  | tm_app t1 t2 => tm_fvars t1 ++ tm_fvars t2
  | tm_tabs t1 => tm_fvars t1
  | tm_tapp t1 _ => tm_fvars t1
  | tm_zero => []
  | tm_succ t1 => tm_fvars t1
  | tm_natrec n b s => tm_fvars n ++ tm_fvars b ++ tm_fvars s
  end.

Lemma sk_free_iff : forall (x : atom) (t : tm),
  free_sk x (sk t) <-> In x (tm_fvars t).
Proof.
  intros x t. induction t; simpl.
  - firstorder congruence.
  - firstorder congruence.
  - apply IHt.
  - rewrite IHt1, IHt2, in_app_iff. firstorder congruence.
  - apply IHt.
  - apply IHt.
  - firstorder congruence.
  - apply IHt.
  - rewrite IHt1, IHt2, IHt3, in_app_iff, in_app_iff. firstorder congruence.
Qed.

Fixpoint ty_fvars (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow A B => ty_fvars A ++ ty_fvars B
  | Ty_All A => ty_fvars A
  | Ty_Nat => []
  end.

Lemma in_ty_fvars : forall (X : atom) (T : ty),
  In X (ty_fvars T) <-> ty_free X T.
Proof.
  intros X T. induction T; simpl.
  - firstorder congruence.
  - firstorder congruence.
  - rewrite in_app_iff, IHT1, IHT2. firstorder congruence.
  - apply IHT.
  - firstorder congruence.
Qed.

Definition eupd (rho : env) (X : atom) (C : cand) : env :=
  fun Y => if Nat.eqb X Y then C else rho Y.

Lemma eupd_same : forall rho X C, eupd rho X C X = C.
Proof. intros. unfold eupd. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma lookup_update_eq : forall Gamma x T,
  lookup_context x (update Gamma x T) = Some T.
Proof. intros. simpl. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma lookup_update_neq : forall Gamma x y T,
  x <> y -> lookup_context x (update Gamma y T) = lookup_context x Gamma.
Proof.
  intros Gamma x y T Hneq. simpl.
  destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E. exfalso. exact (Hneq E).
  - reflexivity.
Qed.

(* ---------------- Context free type variables ---------------- *)

Fixpoint ctx_fvars (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (_, T) :: G => ty_fvars T ++ ctx_fvars G
  end.

Lemma lookup_ctx_fvars : forall Gamma x U, lookup_context x Gamma = Some U ->
  forall Y, ty_free Y U -> In Y (ctx_fvars Gamma).
Proof.
  induction Gamma as [| [z T] G IH]; intros x U H Y Hf; simpl in *.
  - discriminate H.
  - destruct (Nat.eqb x z) eqn:E.
    + apply Nat.eqb_eq in E. subst z. injection H as HU. subst U.
      apply in_app_iff. left. apply in_ty_fvars. exact Hf.
    + apply in_app_iff. right. apply (IH x U H Y Hf).
Qed.

(* ---------------- Fundamental theorem ---------------- *)

Theorem fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall (rho : env) (rhob : benv) (sigma : atom -> sktm),
    (forall x, lc_sk (sigma x)) ->
    (forall x U, lookup_context x Gamma = Some U -> R U rho rhob (sigma x)) ->
    R T rho rhob (sksubst sigma (sk t)).
Proof.
  intros Delta Gamma t T Hty. induction Hty; intros rho rhob sigma Hsig Henv.
  - (* T_Var *) simpl. apply Henv. exact H.
  - (* T_Abs *)
    set (b := sksubst sigma (sk t2)).
    set (x := fresh_atom (L ++ tm_fvars t2)).
    assert (HxL : ~ In x L).
    { intro Hin. apply (fresh_atom_spec (L ++ tm_fvars t2)).
      apply in_app_iff. left. exact Hin. }
    assert (Hxfree : ~ free_sk x (sk t2)).
    { intro Hf. apply (fresh_atom_spec (L ++ tm_fvars t2)).
      apply in_app_iff. right. apply sk_free_iff. exact Hf. }
    assert (Hbeta : forall u, R T1 rho rhob u -> R T2 rho rhob (open_sk b u)).
    { intros u Hu.
      set (sigma_u := fun z => if Nat.eqb z x then u else sigma z).
      assert (Hsig_u : forall z, lc_sk (sigma_u z)).
      { intro z. unfold sigma_u. destruct (Nat.eqb z x) eqn:E.
        - exact (proj1 (R_is_cand T1 rho rhob) u Hu).
        - apply Hsig. }
      assert (Henv_u : forall z U, lookup_context z (update Gamma x T1) = Some U ->
          R U rho rhob (sigma_u z)).
      { intros z U Hlook. unfold sigma_u.
        destruct (Nat.eqb z x) eqn:E.
        - apply Nat.eqb_eq in E. subst z.
          assert (Hlook' : lookup_context x (update Gamma x T1) = Some T1).
          { apply lookup_update_eq. }
          rewrite Hlook' in Hlook. injection Hlook as HU. subst U. exact Hu.
        - apply Nat.eqb_neq in E.
          rewrite (lookup_update_neq Gamma z x T1 E) in Hlook.
          exact (Henv z U Hlook). }
      pose proof (H1 x HxL rho rhob sigma_u Hsig_u Henv_u) as Hres.
      change (R T2 rho rhob (sksubst sigma_u (sk (open_tm_rec 0 (tm_fvar x) t2)))) in Hres.
      rewrite (sk_open_tm t2 0 (tm_fvar x)) in Hres.
      unfold sigma_u in Hres.
      change (R T2 rho rhob
        (sksubst (fun y => if Nat.eqb y x then u else sigma y)
           (open_sk_rec 0 (sk_fvar x) (sk t2)))) in Hres.
      rewrite (sksubst_open_sk_gen (sk t2) sigma 0 x u Hsig (proj1 (R_is_cand T1 rho rhob) u Hu) Hxfree) in Hres.
      exact Hres. }
    assert (Hlcabs : lc_sk (sk_abs b)).
    { apply lc_sk_abs.
      pose proof (Hbeta (sk_fvar x) (R_fvar T1 rho rhob x)) as Hopen.
      apply (proj1 (R_is_cand T2 rho rhob)) in Hopen.
      apply (lc_open_sk_inv b 0 0 x) in Hopen. simpl in Hopen. exact Hopen. }
    split.
    + exact Hlcabs.
    + split.
      * apply SN_sk_value. apply v_sk_abs. exact Hlcabs.
      * intros u Hu. exact (R_abs_app T1 T2 rho rhob b u Hlcabs Hbeta Hu).
  - (* T_App *) simpl.
    pose proof (IHHty1 rho rhob sigma Hsig Henv) as H1.
    pose proof (IHHty2 rho rhob sigma Hsig Henv) as H2.
    exact (proj2 (proj2 H1) (sksubst sigma (sk t2)) H2).
  - (* T_TAbs *)
    set (b := sksubst sigma (sk t)).
    set (X := fresh_atom (L ++ ty_fvars T ++ ctx_fvars Gamma)).
    assert (HXL : ~ In X L).
    { intro Hin. apply (fresh_atom_spec (L ++ ty_fvars T ++ ctx_fvars Gamma)).
      rewrite in_app_iff. left. exact Hin. }
    assert (HXfreeT : ~ ty_free X T).
    { intro Hf. apply (fresh_atom_spec (L ++ ty_fvars T ++ ctx_fvars Gamma)).
      rewrite in_app_iff. right. rewrite in_app_iff. left.
      apply in_ty_fvars. exact Hf. }
    assert (HXctx : ~ In X (ctx_fvars Gamma)).
    { intro Hin. apply (fresh_atom_spec (L ++ ty_fvars T ++ ctx_fvars Gamma)).
      rewrite in_app_iff. right. rewrite in_app_iff. right. exact Hin. }
    pose proof (has_type_lc_ty (X :: Delta) Gamma (open_tm_ty t (Ty_FVar X))
                  (open_ty T (Ty_FVar X)) (H X HXL)) as Hlcopen.
    pose proof (lc_ty_open_inv T 0 0 X Hlcopen) as HTlc1. simpl in HTlc1.
    assert (Hbound : ty_bound T <= 1) by (apply lc_ty_bound; exact HTlc1).
    assert (Hall : forall C : cand, R T rho (bcons C rhob) b).
    { intros C.
      set (rho' := eupd rho X C).
      assert (Henv' : forall y U, lookup_context y Gamma = Some U ->
          R U rho' rhob (sigma y)).
      { intros y U Hlook.
        assert (Hpt : forall Y, ty_free Y U -> forall t0, rho' Y t0 <-> rho Y t0).
        { intros Y Hf t0. unfold rho'. unfold eupd.
          destruct (Nat.eqb X Y) eqn:E2.
          - apply Nat.eqb_eq in E2. subst Y. exfalso. apply HXctx.
            eapply lookup_ctx_fvars; eassumption.
          - tauto. }
        apply (proj2 (R_atom_agree U rho' rho rhob Hpt (sigma y))).
        apply Henv. exact Hlook. }
      pose proof (H0 X HXL rho' rhob sigma Hsig Henv') as Hres.
      change (R (open_ty T (Ty_FVar X)) rho' rhob (sksubst sigma (sk (open_tm_ty_rec 0 (Ty_FVar X) t)))) in Hres.
      rewrite (sk_open_tm_ty t 0 (Ty_FVar X)) in Hres.
      apply (proj1 (R_open_ty T 0 (Ty_FVar X) rho' rhob b (lc_ty_fvar 0 X))) in Hres.
      assert (HenvEq : forall i t0,
          upd_b 0 (R_cand (Ty_FVar X) rho' rhob) rhob i t0 <->
          upd_b 0 C rhob i t0).
      { intros i t0. destruct i as [|j]; simpl; [ | apply iff_refl ].
        change (R (Ty_FVar X) rho' rhob t0 <-> C t0).
        simpl. unfold rho', eupd. rewrite Nat.eqb_refl. tauto. }
      apply (proj1 (R_env_agree T rho' rho' _ _ (fun Y t0 => iff_refl (rho' Y t0)) HenvEq b)) in Hres.
      assert (Hag : forall i, i < ty_bound T -> forall t0,
          upd_b 0 C rhob i t0 <-> bcons C rhob i t0).
      { intros i Hi t0. assert (i = 0) by lia. subst i. simpl. split; auto. }
      apply (proj1 (R_rhob_agree T rho' (upd_b 0 C rhob) (bcons C rhob) Hag b)) in Hres.
      assert (HagAtom : forall Y, ty_free Y T -> forall t0, rho' Y t0 <-> rho Y t0).
      { intros Y Hf t0. unfold rho', eupd. destruct (Nat.eqb X Y) eqn:E.
        - apply Nat.eqb_eq in E. subst Y. exfalso. exact (HXfreeT Hf).
        - tauto. }
      exact (proj1 (R_atom_agree T rho' rho (bcons C rhob) HagAtom b) Hres). }
    pose proof (proj1 (R_is_cand T rho (bcons (rhob 0) rhob)) b (Hall (rhob 0))) as Hlcb.
    assert (Hlctabs : lc_sk (sk_tabs b)) by (apply lc_sk_tabs; exact Hlcb).
    split.
    + exact Hlctabs.
    + split.
      * apply SN_sk_value. apply v_sk_tabs. exact Hlctabs.
      * intros C. exact (R_tapp_tabs T rho (bcons C rhob) b (lc_sk_tabs 0 b Hlcb) (Hall C)).
  - (* T_TApp *) simpl.
    pose proof (IHHty rho rhob sigma Hsig Henv) as H1.
    destruct H1 as [Hlc [Hsn Hf]].
    pose proof (Hf (R_cand U rho rhob)) as Hb.
    pose proof (has_type_lc_ty Delta Gamma t (Ty_All T) Hty) as HlcAll.
    inversion HlcAll; subst.
    pose proof (wf_ty_lc Delta U H) as HlcU.
    assert (Hbound : ty_bound T <= 1) by (apply lc_ty_bound; exact H2).
    assert (Hag : forall i, i < ty_bound T -> forall t0,
        upd_b 0 (R_cand U rho rhob) rhob i t0 <-> bcons (R_cand U rho rhob) rhob i t0).
    { intros i Hi t0. assert (i = 0) by lia. subst i. simpl. split; auto. }
    exact (proj2 (R_open_ty T 0 U rho rhob _ HlcU)
            (proj2 (R_rhob_agree T rho (upd_b 0 (R_cand U rho rhob) rhob)
                      (bcons (R_cand U rho rhob) rhob) Hag _) Hb)).
  - (* T_Zero *) simpl.
    split; [ constructor | apply SN_sk_stuck; intros t' Hs; inversion Hs ].
  - (* T_Succ *) simpl.
    pose proof (IHHty rho rhob sigma Hsig Henv) as Hn.
    destruct Hn as [Hlc Hsn].
    split; [ apply lc_sk_succ; exact Hlc | apply SN_sk_succ; exact Hsn ].
  - (* T_Rec *) simpl.
    pose proof (IHHty1 rho rhob sigma Hsig Henv) as Hn.
    pose proof (IHHty2 rho rhob sigma Hsig Henv) as Hb.
    pose proof (IHHty3 rho rhob sigma Hsig Henv) as Hs.
    destruct Hn as [Hlc Hsn].
    exact (natrec_R T rho rhob (sksubst sigma (sk n)) Hsn Hlc
             (sksubst sigma (sk b)) (sksubst sigma (sk s)) Hb Hs).
Qed.

(* The universal candidate: all locally closed strongly normalizing terms *)
Definition top_cand : cand.
Proof.
  refine (mk_cand (fun t => lc_sk t /\ SN_sk t) _ _ _ _).
  - intros t [H _]. exact H.
  - intros t [_ H]. exact H.
  - intros t t' [Hl Hs] Hstep. split.
    + apply lc_sk_step with (t := t); assumption.
    + apply SN_sk_step with (t := t); assumption.
  - intros t Hnv Hl Hs Hred. split; assumption.
Defined.

Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  intros t T Hty.
  pose (rho := fun _ : atom => top_cand).
  pose (rhob := fun _ : nat => top_cand).
  pose (sigma := fun x : atom => sk_fvar x).
  assert (Hsig : forall x, lc_sk (sigma x)).
  { intro x. apply lc_sk_fvar. }
  assert (Henv : forall x U, lookup_context x empty = Some U -> R U rho rhob (sigma x)).
  { intros x U Hlook. simpl in Hlook. discriminate Hlook. }
  pose proof (fundamental [] empty t T Hty rho rhob sigma Hsig Henv) as HR.
  assert (Hid : sksubst sigma (sk t) = sk t) by apply sksubst_id.
  rewrite Hid in HR.
  pose proof (proj1 (proj2 (R_is_cand T rho rhob)) (sk t) HR) as HSN.
  exact (SN_sk_to_SN (sk t) HSN t eq_refl).
Qed.

End SystemFNormalizationRecursionHardTask.
