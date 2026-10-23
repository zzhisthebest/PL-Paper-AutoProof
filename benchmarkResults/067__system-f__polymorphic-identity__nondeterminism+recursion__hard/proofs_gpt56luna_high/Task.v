(** System F parametricity benchmark, Hard variant.
    Features: nondeterminism-recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
From Stdlib Require Import FunctionalExtensionality.
From Stdlib Require Import PropExtensionality.
Import ListNotations.

Module SystemFParametricityNondeterminismRecursionHardTask.

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
  | tm_natrec : tm -> tm -> tm -> tm
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

Notation "'Nat'" := Ty_Nat (in custom systemf_ty at level 0) : systemf_scope.
Notation "'zero'" := tm_zero (in custom systemf_tm at level 0) : systemf_scope.
Notation "'succ' t" := (tm_succ t) (in custom systemf_tm at level 9, t custom systemf_tm at level 0) : systemf_scope.
Notation "'rec' n b s" := (tm_natrec n b s)
  (in custom systemf_tm at level 9, n custom systemf_tm at level 0, b custom systemf_tm at level 0, s custom systemf_tm at level 0) : systemf_scope.
Notation "'choice' t1 'or' t2" := (tm_choice t1 t2)
  (in custom systemf_tm at level 200, t1 custom systemf_tm, t2 custom systemf_tm at level 200) : systemf_scope.

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
  | tm_choice t1 t2 => tm_choice (open_tm_rec k u t1) (open_tm_rec k u t2)
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
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (tm_subst x s t1)
  | tm_natrec n b f => tm_natrec (tm_subst x s n) (tm_subst x s b) (tm_subst x s f)
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
      lc_tm_at K k n -> lc_tm_at K k b -> lc_tm_at K k s -> lc_tm_at K k (tm_natrec n b s)
  | lc_tm_choice : forall K k t1 t2,
      lc_tm_at K k t1 -> lc_tm_at K k t2 -> lc_tm_at K k (tm_choice t1 t2).

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
  | ST_ChoiceLeft : forall t1 t2,
      locally_closed_tm t1 ->
      locally_closed_tm t2 ->
      tm_choice t1 t2 --> t1
  | ST_ChoiceRight : forall t1 t2,
      locally_closed_tm t1 ->
      locally_closed_tm t2 ->
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
      has_type Delta Gamma (tm_natrec n b s) T
  | T_Choice : forall Delta Gamma t1 t2 T,
      has_type Delta Gamma t1 T -> has_type Delta Gamma t2 T ->
      has_type Delta Gamma (tm_choice t1 t2) T.

Inductive multi : tm -> tm -> Prop :=
  | multi_refl : forall x, multi x x
  | multi_step : forall x y z, x --> y -> multi y z -> multi x z.
Notation "t '-->*' u" := (multi t u) (at level 40).


Hint Constructors lc_ty_at lc_tm_at value : core.

(* The relation used below is deliberately a relation on values.  The
   existential wrapper is important here: choice only promises one good
   branch, rather than that all branches have the same result. *)
Definition vrel := tm -> tm -> Prop.

Definition good_vrel (R : vrel) : Prop :=
  forall x y, R x y -> value x /\ value y.

Definition evrel (R : vrel) (t1 t2 : tm) : Prop :=
  exists v1 v2, multi t1 v1 /\ multi t2 v2 /\ R v1 v2.

Fixpoint lookup_vrel (X : atom) (E : list (atom * vrel)) : vrel :=
  match E with
  | [] => fun _ _ => False
  | (Y,R) :: E' => if Nat.eqb X Y then R else lookup_vrel X E'
  end.

Fixpoint nth_vrel (n : nat) (E : list vrel) : vrel :=
  match n, E with
  | O, R :: _ => R
  | S n', _ :: E' => nth_vrel n' E'
  | _, _ => fun _ _ => False
  end.

Fixpoint vrel_at (B : list vrel) (E : list (atom * vrel))
    (T : ty) : vrel :=
  match T with
  | Ty_BVar n => nth_vrel n B
  | Ty_FVar X => lookup_vrel X E
  | Ty_Arrow A C =>
      fun f g =>
        (exists T1 b1, f = tm_abs T1 b1 /\
         exists T2 b2, g = tm_abs T2 b2 /\
         locally_closed_tm f /\ locally_closed_tm g /\
         forall x y, vrel_at B E A x y ->
           evrel (vrel_at B E C) (tm_app f x) (tm_app g y))
  | Ty_All C =>
      fun f g =>
        (exists b1, f = tm_tabs b1 /\
         exists b2, g = tm_tabs b2 /\
         locally_closed_tm f /\ locally_closed_tm g /\
         forall U1 U2 R,
           locally_closed_ty U1 -> locally_closed_ty U2 ->
           good_vrel R ->
           evrel (vrel_at (R :: B) E C)
             (tm_tapp f U1) (tm_tapp g U2))
  | Ty_Nat =>
      fun n1 n2 => exists n, n1 = numeral n /\ n2 = numeral n
  end.

Lemma multi_trans : forall a b c, multi a b -> multi b c -> multi a c.
Proof.
  induction 1; eauto using multi.
Qed.

Lemma multi_one : forall t u, t --> u -> multi t u.
Proof. intros; eauto using multi. Qed.

Lemma multi_app1 : forall t t' u, locally_closed_tm u ->
  multi t t' -> multi (tm_app t u) (tm_app t' u).
Proof.
  intros t t' u Hlc H; induction H; eauto using multi, ST_App1.
Qed.

Lemma multi_app2 : forall v t t', value v ->
  multi t t' -> multi (tm_app v t) (tm_app v t').
Proof.
  intros v t t' Hv H; induction H; eauto using multi, ST_App2.
Qed.

Lemma multi_tapp : forall t t' U, locally_closed_ty U ->
  multi t t' -> multi (tm_tapp t U) (tm_tapp t' U).
Proof.
  intros t t' U Hlc H; induction H; eauto using multi, ST_TApp.
Qed.

Lemma multi_succ : forall t t', multi t t' ->
  multi (tm_succ t) (tm_succ t').
Proof.
  intros; induction H; eauto using multi, ST_Succ.
Qed.

Lemma numeric_lc : forall n, numeric_value n -> locally_closed_tm n.
Proof.
  induction 1.
  - constructor.
  - unfold locally_closed_tm in *. econstructor; eauto.
Qed.

Lemma value_lc : forall t, value t -> locally_closed_tm t.
Proof. intros t H; inversion H; eauto using numeric_lc. Qed.

Lemma numeric_value_numeral : forall n, numeric_value (numeral n).
Proof. induction n; simpl; eauto using numeric_value. Qed.

Fixpoint lookup_tm_subst (x : atom) (S : list (atom * tm)) : tm :=
  match S with
  | [] => tm_fvar x
  | (y,u) :: S' => if Nat.eqb x y then u else lookup_tm_subst x S'
  end.

Fixpoint lookup_ty_subst (x : atom) (S : list (atom * ty)) : ty :=
  match S with
  | [] => Ty_FVar x
  | (y,U) :: S' => if Nat.eqb x y then U else lookup_ty_subst x S'
  end.

Fixpoint ty_subst_env (S : list (atom * ty)) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => lookup_ty_subst X S
  | Ty_Arrow A B => Ty_Arrow (ty_subst_env S A) (ty_subst_env S B)
  | Ty_All A => Ty_All (ty_subst_env S A)
  | Ty_Nat => Ty_Nat
  end.

Fixpoint tm_subst_env (ST : list (atom * ty)) (S : list (atom * tm)) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => lookup_tm_subst x S
  | tm_abs T t1 => tm_abs (ty_subst_env ST T) (tm_subst_env ST S t1)
  | tm_app t1 t2 => tm_app (tm_subst_env ST S t1) (tm_subst_env ST S t2)
  | tm_tabs t1 => tm_tabs (tm_subst_env ST S t1)
  | tm_tapp t1 T => tm_tapp (tm_subst_env ST S t1) (ty_subst_env ST T)
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (tm_subst_env ST S t1)
  | tm_natrec n b s => tm_natrec (tm_subst_env ST S n)
      (tm_subst_env ST S b) (tm_subst_env ST S s)
  | tm_choice t1 t2 => tm_choice (tm_subst_env ST S t1) (tm_subst_env ST S t2)
  end.

Fixpoint ty_atoms (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow A B => ty_atoms A ++ ty_atoms B
  | Ty_All A => ty_atoms A
  | Ty_Nat => []
  end.

Fixpoint tm_atoms (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs T t1 => ty_atoms T ++ tm_atoms t1
  | tm_app t1 t2 => tm_atoms t1 ++ tm_atoms t2
  | tm_tabs t1 => tm_atoms t1
  | tm_tapp t1 T => tm_atoms t1 ++ ty_atoms T
  | tm_zero => []
  | tm_succ t1 => tm_atoms t1
  | tm_natrec n b s => tm_atoms n ++ tm_atoms b ++ tm_atoms s
  | tm_choice t1 t2 => tm_atoms t1 ++ tm_atoms t2
  end.

Fixpoint list_max (xs : list atom) : atom :=
  match xs with
  | [] => 0
  | x :: xs' => Nat.max x (list_max xs')
  end.

Definition fresh_atom (xs : list atom) : atom := S (list_max xs).

Lemma in_list_max : forall x xs, In x xs -> x <= list_max xs.
Proof.
  intros x xs. induction xs as [|y ys IH].
  - intros H. contradiction.
  - intros H. simpl in H. destruct H as [H|H].
    + subst x. simpl. apply Nat.le_max_l.
    + simpl. eapply Nat.le_trans; [apply IH; exact H|apply Nat.le_max_r].
Qed.

Lemma fresh_atom_notin : forall xs, ~ In (fresh_atom xs) xs.
Proof.
  intros xs H. unfold fresh_atom in H.
  pose proof (in_list_max (S (list_max xs)) xs H) as Hle.
  lia.
Qed.

Lemma lookup_tm_subst_none : forall x S,
  ~ In x (map fst S) -> lookup_tm_subst x S = tm_fvar x.
Proof.
  intros x S. induction S as [|[y u] S IH]; intros H.
  - reflexivity.
  - simpl.
    destruct (Nat.eqb x y) eqn:E.
    + exfalso. apply H. simpl. left. apply Nat.eqb_eq in E. symmetry. exact E.
    + simpl. apply IH. intro Hin. apply H. simpl. right. exact Hin.
Qed.

Lemma lookup_ty_subst_none : forall x S,
  ~ In x (map fst S) -> lookup_ty_subst x S = Ty_FVar x.
Proof.
  intros x S. induction S as [|[y u] S IH]; intros H.
  - reflexivity.
  - simpl.
    destruct (Nat.eqb x y) eqn:E.
    + exfalso. apply H. simpl. left. apply Nat.eqb_eq in E. symmetry. exact E.
    + simpl. apply IH. intro Hin. apply H. simpl. right. exact Hin.
Qed.

Lemma open_ty_rec_lc_at : forall d T, lc_ty_at d T ->
  forall k U, open_ty_rec (k + d) U T = T.
Proof.
  induction 1; intros; simpl.
  - destruct (Nat.eqb (k0 + k) i) eqn:E; [exfalso; apply Nat.eqb_eq in E; lia|reflexivity].
  - reflexivity.
  - rewrite IHlc_ty_at1, IHlc_ty_at2; reflexivity.
  - f_equal. replace (S (k0 + k)) with (k0 + S k) by lia.
    apply IHlc_ty_at.
  - reflexivity.
Qed.

Lemma ty_subst_open : forall S k U T,
  (forall X, locally_closed_ty (lookup_ty_subst X S)) ->
  ty_subst_env S (open_ty_rec k U T) =
  open_ty_rec k (ty_subst_env S U) (ty_subst_env S T).
Proof.
  intros S k U T H. revert k U.
  induction T as [i|X|A IHA B IHB|A IHA|]; intros k U; simpl.
  - destruct (Nat.eqb k i); reflexivity.
  - symmetry. replace k with (k + 0) by lia.
    apply open_ty_rec_lc_at with (d := 0) (T := lookup_ty_subst X S).
    exact (H X).
  - rewrite (IHA k U), (IHB k U); reflexivity.
  - Show.
    rewrite (IHA (Datatypes.S k) U); reflexivity.
  - reflexivity.
Qed.

Lemma open_tm_rec_lc_at : forall K d t, lc_tm_at K d t ->
  forall k u, open_tm_rec (k + d) u t = t.
Proof.
  induction 1; intros k0 u; simpl.
  - destruct (Nat.eqb (k0 + k) i) eqn:E;
      [exfalso; apply Nat.eqb_eq in E; lia|reflexivity].
  - reflexivity.
  - f_equal. replace (Datatypes.S (k0 + k)) with (k0 + Datatypes.S k) by lia.
    apply IHlc_tm_at.
  - f_equal; [apply IHlc_tm_at1|apply IHlc_tm_at2].
  - f_equal; apply IHlc_tm_at.
  - f_equal; apply IHlc_tm_at.
  - reflexivity.
  - f_equal; apply IHlc_tm_at.
  - f_equal; [apply IHlc_tm_at1|apply IHlc_tm_at2|apply IHlc_tm_at3].
  - f_equal; [apply IHlc_tm_at1|apply IHlc_tm_at2].
Qed.

Lemma tm_ty_subst_open : forall S k U t,
  (forall X, locally_closed_ty (lookup_ty_subst X S)) ->
  tm_subst_env S [] (open_tm_ty_rec k U t) =
  open_tm_ty_rec k (ty_subst_env S U) (tm_subst_env S [] t).
Proof.
  intros S k U t H. revert k U.
  induction t as [i|x|T t IH|t1 IH1 t2 IH2|t IH|t IH T| |t IH|
    n IHn b IHb s IHs|t1 IH1 t2 IH2]; intros k U; simpl.
  - reflexivity. - reflexivity.
  - f_equal. + apply ty_subst_open; exact H. + apply IH; exact H.
  - f_equal; [apply IH1; exact H|apply IH2; exact H].
  - f_equal; apply (IH (Datatypes.S k) U); exact H.
  - f_equal. + apply IH; exact H. + apply ty_subst_open; exact H.
  - reflexivity.
  - f_equal; apply IH; exact H.
  - f_equal; [apply IHn; exact H|apply IHb; exact H|apply IHs; exact H].
  - f_equal; [apply IH1; exact H|apply IH2; exact H].
Qed.

Lemma tm_subst_open : forall ST S k u t,
  (forall x, locally_closed_tm (lookup_tm_subst x S)) ->
  tm_subst_env ST S (open_tm_rec k u t) =
  open_tm_rec k (tm_subst_env ST S u) (tm_subst_env ST S t).
Proof.
  intros ST S k u t H. revert k u.
  induction t as [i|x|T t IH|t1 IH1 t2 IH2|t IH|t IH T| |t IH|
    n IHn b IHb s IHs|t1 IH1 t2 IH2]; intros k u; simpl.
  - destruct (Nat.eqb k i); reflexivity.
  - unfold locally_closed_tm in H. replace k with (k + 0) by lia.
    rewrite (open_tm_rec_lc_at 0 0
      (lookup_tm_subst x S) (H x) k (tm_subst_env ST S u)); reflexivity.
  - rewrite (IH (Datatypes.S k) u). reflexivity.
  - f_equal; [apply IH1; exact H|apply IH2; exact H].
  - f_equal; apply IH; exact H.
  - f_equal; apply IH; exact H.
  - reflexivity.
  - f_equal; apply IH; exact H.
  - f_equal; [apply IHn; exact H|apply IHb; exact H|apply IHs; exact H].
  - f_equal; [apply IH1; exact H|apply IH2; exact H].
Qed.

Lemma tm_subst_env_ext : forall ST S x a t,
  ~ In x (tm_atoms t) ->
  tm_subst_env ST ((x,a) :: S) t = tm_subst_env ST S t.
Proof.
  induction t as [i|y|T t IH|t1 IH1 t2 IH2|t IH|t IH T| |t IH|
    n IHn b IHb s IHs|t1 IH1 t2 IH2]; intros H; simpl in *.
  - reflexivity.
  - unfold lookup_tm_subst. simpl.
    destruct (Nat.eqb y x) eqn:E.
    + exfalso. apply H. simpl. left. apply Nat.eqb_eq in E. exact E.
    + reflexivity.
  - assert (Ht : ~ In x (tm_atoms t)).
    { intro K. apply H. rewrite in_app_iff. right. exact K. }
    rewrite (IH Ht). reflexivity.
  - assert (H1 : ~ In x (tm_atoms t1)).
    { intro K. apply H. rewrite in_app_iff. left. exact K. }
    assert (H2 : ~ In x (tm_atoms t2)).
    { intro K. apply H. rewrite in_app_iff. right. exact K. }
    rewrite (IH1 H1), (IH2 H2); reflexivity.
  - assert (Ht : ~ In x (tm_atoms t)).
    { exact H. }
    rewrite (IH Ht); reflexivity.
  - assert (Ht : ~ In x (tm_atoms t)).
    { intro K. apply H. rewrite in_app_iff. left. exact K. }
    rewrite (IH Ht); reflexivity.
  - reflexivity.
  - assert (Ht : ~ In x (tm_atoms t)).
    { exact H. }
    rewrite (IH Ht); reflexivity.
  - assert (Hn : ~ In x (tm_atoms n)).
    { intro K. apply H. rewrite in_app_iff. left. exact K. }
    assert (Hb : ~ In x (tm_atoms b)).
    { intro K. apply H. rewrite in_app_iff. right. rewrite in_app_iff. left. exact K. }
    assert (Hs : ~ In x (tm_atoms s)).
    { intro K. apply H. rewrite in_app_iff. right. rewrite in_app_iff. right. exact K. }
    rewrite (IHn Hn), (IHb Hb), (IHs Hs); reflexivity.
  - assert (H1 : ~ In x (tm_atoms t1)).
    { intro K. apply H. rewrite in_app_iff. left. exact K. }
    assert (H2 : ~ In x (tm_atoms t2)).
    { intro K. apply H. rewrite in_app_iff. right. exact K. }
    rewrite (IH1 H1), (IH2 H2); reflexivity.
Qed.

Lemma lc_ty_open_inv : forall k T U,
  lc_ty_at k (open_ty_rec k U T) -> lc_ty_at (Datatypes.S k) T.
Proof.
  intros k T U H. revert k U H.
  induction T as [i|X|A IHA B IHB|A IHA|]; intros k U H; simpl in H.
  - destruct (Nat.eqb k i) eqn:E.
    + apply lc_ty_bvar. apply Nat.eqb_eq in E. lia.
    + inversion H. apply lc_ty_bvar; lia.
  - constructor.
  - inversion H; constructor; eauto.
  - inversion H; constructor.
    apply IHA with (k := Datatypes.S k) (U := U); eauto.
  - constructor.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T H; induction H.
  - constructor.
  - constructor; assumption.
  - unfold locally_closed_ty. apply lc_ty_all.
    set (X := fresh_atom (L ++ Delta ++ ty_atoms T)).
    assert (HX : ~ In X L).
    { unfold X. intro HX'. apply (fresh_atom_notin
        (L ++ Delta ++ ty_atoms T)).
      apply in_or_app. left. exact HX'. }
    specialize (H0 X HX).
    apply lc_ty_open_inv with (k := 0)
      (U := Ty_FVar X).
    exact H0.
  - constructor.
Qed.

Lemma lc_tm_ty_open_inv : forall K k t U,
  lc_tm_at K k (open_tm_ty_rec K U t) -> lc_tm_at (Datatypes.S K) k t.
Proof.
  intros K k t U H. revert K k U H.
  induction t as [i|x|T t IH|t1 IH1 t2 IH2|t IH|t IH T| |t IH|
    n IHn b IHb s IHs|t1 IH1 t2 IH2]; intros K k U H; simpl in H.
  - inversion H; constructor; assumption.
  - constructor.
  - inversion H; constructor.
    + apply lc_ty_open_inv with (k := K) (U := U); eauto.
    + apply IH with (K := K) (k := Datatypes.S k) (U := U); eauto.
  - inversion H; constructor; eauto.
  - inversion H; constructor.
    apply IH with (K := Datatypes.S K) (k := k) (U := U); eauto.
  - inversion H; constructor.
    + apply IH with (K := K) (k := k) (U := U); eauto.
    + apply lc_ty_open_inv with (k := K) (U := U); eauto.
  - constructor.
  - inversion H; constructor; eauto.
  - inversion H; constructor; eauto.
  - inversion H; constructor; eauto.
Qed.

Lemma lc_tm_open_inv : forall K k t u,
  lc_tm_at K k (open_tm_rec k u t) -> lc_tm_at K (Datatypes.S k) t.
Proof.
  intros K k t u H. revert K k u H.
  induction t as [i|x|T t IH|t1 IH1 t2 IH2|t IH|t IH T| |t IH|
    n IHn b IHb s IHs|t1 IH1 t2 IH2]; intros K k u H; simpl in H.
  - destruct (Nat.eqb k i) eqn:E.
    + apply lc_tm_bvar; apply Nat.eqb_eq in E; lia.
    + inversion H; apply lc_tm_bvar; lia.
  - constructor.
  - inversion H; constructor; eauto.
  - inversion H; constructor; eauto.
  - inversion H; constructor.
    apply IH with (K := Datatypes.S K) (k := k) (u := u); eauto.
  - inversion H; constructor.
    + apply IH with (K := K) (k := k) (u := u); eauto.
    + eauto.
  - constructor.
  - inversion H; constructor; eauto.
  - inversion H; constructor; eauto.
  - inversion H; constructor; eauto.
Qed.

Lemma has_type_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T H; induction H.
  - constructor.
  - unfold locally_closed_tm. apply lc_tm_abs.
    + eapply wf_ty_lc. eauto.
    + set (x := fresh_atom (L ++ tm_atoms t2)).
      assert (HX : ~ In x L).
      { unfold x. intro Hx. apply (fresh_atom_notin (L ++ tm_atoms t2)).
        apply in_or_app. left. exact Hx. }
      specialize (H0 x HX).
      apply lc_tm_open_inv with (K := 0) (k := 0) (u := tm_fvar x).
      apply IHH0.
  - constructor; eauto using has_type_lc.
  - unfold locally_closed_tm. apply lc_tm_tabs.
    set (X := fresh_atom (L ++ ty_atoms T)).
    assert (HX : ~ In X L).
    { unfold X. intro HX'. apply (fresh_atom_notin (L ++ ty_atoms T)).
      apply in_or_app. left. exact HX'. }
    specialize (H0 X HX).
    apply lc_tm_ty_open_inv with (K := 0) (k := 0)
      (U := Ty_FVar X). apply IHH0.
  - constructor; eauto using has_type_lc, wf_ty_lc.
  - constructor; eauto using has_type_lc.
  - constructor.
  - constructor; eauto using has_type_lc.
  - constructor; eauto using has_type_lc.
  - constructor; eauto using has_type_lc.
Qed.

Fixpoint insert_vrel (k : nat) (R : vrel) (B : list vrel) : list vrel :=
  match k, B with
  | O, _ => R :: B
  | Datatypes.S k', b :: B' => b :: insert_vrel k' R B'
  | Datatypes.S k', [] => (fun _ _ => False) :: insert_vrel k' R []
  end.

Lemma nth_nil : forall i, nth_vrel i [] = (fun _ _ => False).
Proof. intros []; reflexivity. Qed.

Lemma nth_insert_lt : forall k R B i, i < k ->
  nth_vrel i (insert_vrel k R B) = nth_vrel i B.
Proof.
  induction k as [|k IH]; intros R B i H.
  - exfalso; lia.
  - destruct B as [|b B].
    + destruct i; simpl.
      * reflexivity.
      * assert (P := IH R (@nil vrel) i ltac:(lia)).
        rewrite nth_nil in P. exact P.
    + destruct i; simpl.
      * reflexivity.
      * apply IH. lia.
Qed.

Lemma nth_insert_eq : forall k R B,
  nth_vrel k (insert_vrel k R B) = R.
Proof.
  induction k as [|k IH]; intros R B; simpl.
  - reflexivity.
  - destruct B as [|b B]; simpl.
    + apply IH.
    + apply IH.
Qed.

Lemma insert_succ : forall k R B Q,
  insert_vrel (Datatypes.S k) R (Q :: B) = Q :: insert_vrel k R B.
Proof. reflexivity. Qed.

Lemma lookup_vrel_cons_neq : forall X Y R E,
  X <> Y -> lookup_vrel X ((Y,R)::E) = lookup_vrel X E.
Proof.
  intros; simpl. destruct (Nat.eqb X Y) eqn:E0; auto.
  exfalso; apply H; apply Nat.eqb_eq; exact E0.
Qed.

Lemma vrel_open : forall k T B E X R,
  lc_ty_at (Datatypes.S k) T ->
  ~ In X (ty_atoms T) ->
  ~ In X (map fst E) ->
  vrel_at B ((X,R)::E) (open_ty_rec k (Ty_FVar X) T) =
  vrel_at (insert_vrel k R B) E T.
Proof.
  intros k T B E X R Hlc Hfresh Henv.
  revert k B E X R Hlc Hfresh Henv.
  induction T as [i|Y|A IHA C IHC|C IHC|];
    intros k B E X R Hlc Hfresh Henv; simpl in *.
  - inversion Hlc.
    destruct (Nat.eqb k i) eqn:Eki.
    + apply Nat.eqb_eq in Eki. rewrite <- Eki.
      assert (Ex : Nat.eqb X X = true) by (apply Nat.eqb_eq; reflexivity).
      change (lookup_vrel X ((X,R)::E) =
        nth_vrel k (insert_vrel k R B)).
      unfold lookup_vrel. rewrite Ex. simpl. symmetry. apply nth_insert_eq.
    + assert (Hil : i < k \/ k <= i) by lia.
      destruct Hil as [Hi|Hi].
      * rewrite nth_insert_lt by exact Hi. reflexivity.
      * assert (Eeq : i = k) by lia.
        exfalso. apply Nat.eqb_neq in Eki. apply Eki. symmetry. exact Eeq.
  - assert (Hne : X <> Y).
    { intro Heq. subst Y. apply Hfresh. simpl. left. reflexivity. }
    destruct (Nat.eqb Y X) eqn:EYX.
    + exfalso. apply Hne. apply Nat.eqb_eq in EYX. symmetry. exact EYX.
    + reflexivity.
  - inversion Hlc.
    assert (HA : lc_ty_at (Datatypes.S k) A) by eauto.
    assert (HC : lc_ty_at (Datatypes.S k) C) by eauto.
    assert (HAX : ~ In X (ty_atoms A)).
    { intro h. apply Hfresh. rewrite in_app_iff. left. exact h. }
    assert (HCX : ~ In X (ty_atoms C)).
    { intro h. apply Hfresh. rewrite in_app_iff. right. exact h. }
    apply functional_extensionality; intro f.
    apply functional_extensionality; intro g.
    simpl. rewrite (IHA k B E X R HA HAX Henv).
    rewrite (IHC k B E X R HC HCX Henv).
    reflexivity.
  - inversion Hlc.
    assert (HC : lc_ty_at (Datatypes.S (Datatypes.S k)) C) by eauto.
    apply functional_extensionality; intro f.
    apply functional_extensionality; intro g.
    simpl. apply propositional_extensionality. split; intro Hrel.
    + destruct Hrel as [b1 [Hb1 [b2 [Hb2 [Hf [Hg Hall]]]]]].
      assert (Hbody : forall U1 U2 Q,
        locally_closed_ty U1 -> locally_closed_ty U2 -> good_vrel Q ->
        evrel (vrel_at (Q :: insert_vrel k R B) E C)
          (tm_tapp f U1) (tm_tapp g U2)).
      { intros U1 U2 Q HU1 HU2 HQ. specialize (Hall U1 U2 Q HU1 HU2 HQ).
        rewrite (IHC (Datatypes.S k) (Q :: B) E X R HC Hfresh Henv) in Hall.
        rewrite insert_succ in Hall. exact Hall. }
      exists b1.
      split; [exact Hb1|exists b2; repeat split; first [assumption | exact Hbody]].
    + destruct Hrel as [b1 [Hb1 [b2 [Hb2 [Hf [Hg Hall]]]]]].
      assert (Hbody : forall U1 U2 Q,
        locally_closed_ty U1 -> locally_closed_ty U2 -> good_vrel Q ->
        evrel (vrel_at (Q :: B) ((X,R)::E)
          (open_ty_rec (Datatypes.S k) (Ty_FVar X) C))
          (tm_tapp f U1) (tm_tapp g U2)).
      { intros U1 U2 Q HU1 HU2 HQ. specialize (Hall U1 U2 Q HU1 HU2 HQ).
        rewrite <- insert_succ in Hall.
        rewrite <- (IHC (Datatypes.S k) (Q :: B) E X R HC Hfresh Henv) in Hall.
        exact Hall. }
      exists b1.
      split; [exact Hb1|exists b2; repeat split; first [assumption | exact Hbody]].
  - reflexivity.
Qed.

Theorem polymorphic_identity_theorem_for_free : forall t,
  has_type [] empty t
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) ->
  forall U v,
    wf_ty [] U ->
    value v ->
    has_type [] empty v U ->
    tm_app (tm_tapp t U) v -->* v.
Proof.
  (* Complete the proof of the free theorem. *)
Qed.

End SystemFParametricityNondeterminismRecursionHardTask.
